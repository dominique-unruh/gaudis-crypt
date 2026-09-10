import GaudisCrypt.Syntax.ProgramSyntax
import GaudisCrypt.Language.Modules

/-!
# `flattenProcedureCalls` — flattening concretely-spelled-out `call`s (PLAN ONLY, no code yet)

("Flattening", not "inlining": *inlining* is reserved for the transformation that additionally
looks definitions up.  Here the callee is already spelled out in the term.)

This file is (for now) only a design plan for a meta-level pipeline that takes an elaborated
**`StmtWithHoles h L`** term and rewrites calls whose callee is *concretely spelled out* into the
callee's body, lifting the callee's parameters and local variables into the statement's
local-variable list (so the result is a `StmtWithHoles h L'` at a *widened* `L'`).  Working at
statement level keeps it generic; `ProcedureWithHoles` is a thin wrapper on top (§8).  Example,
written at the `proc` level where it is readable:

```
proc (…) -> T {
  var x y : Nat;
  x <- 1;
  y <- call (proc (z) -> U { var w : Nat; w <- 2*§z; return §w * §w; }) (§x + §x);
  …
}
```
becomes
```
proc (…) -> T {
  var z w x y : Nat;    -- the callee's variables are *prepended* (see §3)
  x <- 1;
  w <- default;         -- callee locals are re-initialised (see §6)
  z <- §x + §x;         -- argument binding
  w <- 2*§z;            -- callee body, retargeted to the new slots
  y <- §w * §w;         -- return value stored into the caller's l-value
  …
}
```

Main intended use: cleaning up a `ProcedureWithHoles` after its holes have been instantiated
(`ProcedureWithHoles.instantiate` turns every `.hole` into a `.call'` of the — then concrete —
procedure), so that the result is one flat program again.

## Decisions taken

* **Everything goes through lenses.**  Nothing is taken apart that does not have to be: whole
  subprograms are wrapped in `StmtWithHoles.applyLens trafo` and whole expressions in
  `trafo.chainGetter`, which is *always* well-typed and correct.  Consequence: no Expr surgery,
  no type substitution, no case analysis on statements that do not contain the call.
* **Cleaning rewrites with a closed set of lemmas only** — never `simp` with the default set, and
  with `zeta := false` so that `let`s survive.  Nothing may fire that was not put there on
  purpose for one of the three normalisation jobs of §6.2.
* **Flattening and cleaning are separate passes** (§6): the flattener emits deliberately ugly terms,
  a normalisation pass pushes the wrappers inwards, and a third pass re-associates `seq`.  The
  flattener is the only one that can fail; the other two never do.
* **Core types unchanged**: `ProcedureScope`, `typeListToTuple` and `localTypes` stay as they
  are.  The tuple encoding's irregularity (the last element is unwrapped) is absorbed in the base
  cases of §4's lens definitions, behind a five-lemma interface; no other code case-splits on it.
* **Callees**: no `whnf`, no unfolding of constants.  Only the callee's *locals list* and its
  *signature* have to be literal (§2); its body and return value need not be.
* **Locals**: callee locals are re-initialised with an explicit `w <- default;` at the call site
  (soundness, §6.1).
* **Layout**: the callee's variables are **prepended**, as one block, in front of the statement's
  own locals (§3) — this is what makes the widening lens of §4 a plain `osnd^|B|` and the callee
  embedding a plain prefix lens, with no offsets.
* **Fixed point**: `flattenProcedureCalls` repeats until no flattenable call is left, so calls
  that arrive *inside* a flattened body get flattened too.  This terminates: each round removes
  exactly one `call` node and introduces none.
* **Error**: `flattenCall` throws if the requested call does not exist or is not flattenable;
  `flattenProcedureCalls` throws if the first round already finds nothing.

## 0. Where this sits

**Everything lives in this file**: the Lean-side layer (§4's lenses, §5's `applyLens`, the
normalisation lemmas and the soundness theorems of §9) as well as the meta code.  Proper
*inlining* — the variant that looks definitions up — will be added here later, on top of the same
layer.

It sits in `Logic/` and imports `Syntax/ProgramSyntax.lean`, because the cleaning pass has to
produce terms in exactly the shape the `proc` macro produces — `liftLens` l-values,
`Getter.mk (fun st => …)` expressions, a `let`-telescope of `Lens.intoParams` /
`Lens.intoLocalVars` — or the delaborators there will refuse to print the result in surface
syntax.  That shape is the de-facto interface of this file.

Several of the Lean-side facts are not about flattening at all and should be *considered* for a
better home once they exist; mark each with a `-- TODO(move)` comment rather than moving it
speculatively.  Candidates: `Lens.prodMap`, `Lens.constUnit`, `Lens.chainGetter`,
`Lens.chainSetter` and the `Lens.ext`-style laws about them → `Language/Lens.lean`;
`SubProbability.mapState` and `ProgramDenotation.EquivInLens` with its congruence lemmas →
`Language/Semantics.lean` (or wherever `ProgramDenotation` grows next);
`StmtWithHoles.applyLens` and `programDenotation_applyLens` → `Language/Programs.lean`.

Out of scope here: a *tactic* that rewrites a goal mentioning `procedureDenotation ⟨…⟩`.  That
needs the procedure-level corollary of §9 proved first; the pipeline stops at the `MetaM` API
plus the test commands of §10.

## 1. Shape of the input (what `proc` elaborates to)

The input is the **body** field below — a `StmtWithHoles hCtx L₁` whose leading `let`s bind the
variable lenses.  Its scope type is required to be `L₁ = ProcedureScope P Ls` (that is where new
variables can be added); everything else about it is generic.  A `proc` term elaborates to

```
@ProcedureWithHoles.mk spec hCtx sig
  Ls                                        -- `[⟨T, inferInstance⟩, …] : List (Σ t, Inhabited t)`
  (let p₁ : Lens A₁ (ProcedureState L₁) := Lens.intoParams   ‹chain›; …   -- parameters
   let v₁ : Lens B₁ (ProcedureState L₁) := Lens.intoLocalVars ‹chain›; …  -- local variables
   let h₁ : HoleIndex hCtx sig₁ := HoleIndex.zero; …                      -- holes
   ‹statements›)
  (let p₁ …; let v₁ …; ‹spine let/haves›; Getter.mk (fun st => …))        -- return value
```

with `L₁ = ProcedureScope P Ls` and `‹chain› = Lens.id.ofst.osnd…` (`mkChain` / `navSteps` in
`ProgramSyntax.lean`): slot `k` of `n` is `Lens.id`, then `.ofst` unless `k = n-1`, then `k` ×
`.osnd`.  Statements are `StmtWithHoles.{skip,assign,sample,call',hole,seq,ifThenElse,while}`.
Expressions are `Getter.mk (fun st => … eval x …)` (the `letI : CurrentState _ := ⟨st⟩` is inlined
by elaboration, so each read is `@eval L₁ _ _ inst ⟨…⟩ x`).  L-values are `liftLens x` or
`Setter.throwaway`.

## 2. Which calls are flattenable

Calls are numbered in a pre-order walk of the statement tree (into `seq`, `ifThenElse`, `while`,
and through `let`/`have` statement binders).  Both call forms count, and neither is reduced into
the other:

* `StmtWithHoles.call' x ls b r args` — the constructor, with the callee's three fields spelled
  out separately.  This is what `StmtWithHoles.instantiate` re-emits for a call that was already
  a `call'`;
* `StmtWithHoles.call x p args` — the `@[match_pattern]` wrapper, which is what the `call p (…)`
  surface syntax elaborates to and what `StmtWithHoles.instantiate` builds from a `hole`.  Its
  callee `p` supplies the three fields; usable when `p` is a literal `ProcedureWithHoles.mk`
  (equivalently an anonymous-constructor `⟨locals, body, ret⟩`).

Such a call is **flattenable** iff

* its `sig`'s parameter-type list is a literal list, and every parameter type has an `Inhabited`
  instance (`synthInstance`) — a parameter becomes a local, and the locals list stores
  `⟨T, Inhabited T⟩`;
* its locals list `ls` is a literal `List.cons`/`List.nil` of `Sigma.mk`s.

**The body `b` and the return value `r` need not be literal**: they are used only as arguments to
`applyLens` / getter composition (§5).  A non-literal body simply means the result keeps an
`applyLens` around it — correct, just less pretty.  This is exactly what the generic transport
lemma of §9 buys.

Not flattenable, hence never touched: uninstantiated `StmtWithHoles.hole`s, callees whose locals
list or parameter list is not literal, and callees with a non-`Inhabited` parameter type.

Note for the intended use: right after `ProcedureWithHoles.instantiate`, a former hole reads
`StmtWithHoles.call x (inst.lookup n) args`, whose callee is a `lookup` application, not a
literal — `simp only [HoleSigs.Instantiation.lookup_zero_single, lookup_zero_cons, lookup_succ]`
(all three are `@[simp]` already) exposes the procedure first.

## 3. The new local-variable list

One call is flattened at a time, so the new block is exactly that callee's variables,

```
B = (its parameter types) ++ (its locals)
```

prepended in one piece: the new locals list is `B ++ Ls`.  The statement's own locals keep their
relative order and are shifted by `|B|` (slot `k` ↦ slot `k + |B|`); the callee's variables are
slots `0 … |B|-1`, its parameters first.  Because the block always sits at the front, there are
no offsets anywhere: §4's lenses are the simplest instances of their definitions.

The new list is *returned* (as an `Expr`); at statement level there is no field to store it in,
it is only the index of the result's type,
`StmtWithHoles hCtx (ProcedureScope P (B ++ Ls))`.

Cosmetic consequence: the printed `var` line lists the callee's variables first,
`var z w x y : …;`.

### Names

Printed names come from the `let` binder names of the telescope, so collisions matter for
round-trip printing (a shadowed `§w` would re-parse to the wrong lens).  Collect the names
already in use (the statement's params, locals, hole names); for each callee binder name `w` that
clashes, use `w0`, `w1`, … — the first free one.  Binder names carrying macro scopes are
normalized to a plain name first.  A callee whose body is *not* a literal telescope has no binder
names to read: generate `v0, v1, …` from the parameter/local types instead.

Accepted limitation: names are checked against the statement's own params, locals and holes only.
A *global* variable called `w` that is in scope at the use site would be shadowed in the printed
program (the term itself is unaffected — the shadowing only bites if someone re-parses the
output).  Enumerating globals is not possible in general; if it ever matters, the entry point can
take an extra list of names to avoid.

## 4. The two lenses (Lean-side, this file; see §0 on what may later move elsewhere)

```
L₁ := ProcedureScope P Ls           -- old scope        σ₁ := ProcedureState L₁
L₂ := ProcedureScope P (B ++ Ls)    -- widened scope    σ₂ := ProcedureState L₂
L_c := ProcedureScope P_c Ls_c      -- the callee's scope
```

* **`trafo : Lens σ₁ σ₂`** — widening.  Also the export of the pipeline: composing an outside
  term (precondition, invariant, `wp` goal) with `trafo` and normalizing rewrites it from the old
  scope to the new one.
* **`emb : Lens (ProcedureState L_c) σ₂`** — the callee's scope sitting in the block at the front.

**`ProcedureScope`, `typeListToTuple` and `localTypes` stay exactly as they are.**  The
irregularity of the tuple encoding — `typeListToTuple` unwraps the last element, so
`typeListToTuple (x :: rest) = x × typeListToTuple rest` only when `rest ≠ []` — is absorbed
*inside* the definitions below, in their base cases.  The rest of this file, and the meta code,
never case-split on it.

### What the rest of the world sees

The meta code never names a `widen`/`embedCallee` constant: neither could be *stated* generically,
because `ProcedureScope P (B ++ Ls)`'s variable tuple is `typeListToTuple (localTypes (B ++ Ls))`,
which for variable lists does not reduce to anything the recursions below produce (that is the
unwrapped-last-element problem again).  At *concrete* lists it does, by `rfl`, so the meta code
composes the two layers directly:

```lean
trafo := ProcedureState.mapScope (ProcedureScope.mapVars (tupleSuffix ‹localTypes B› _))
emb   := ProcedureState.mapScope (ProcedureScope.embedInLocalVars
           ((tupleBlock … ).chain (tupleSplit ‹P_c› ‹localTypes Ls_c› _)))
```

and the *interface* is five lemmas, stated at exactly that composed shape:

```lean
(mapScope (mapVars f)).chain (Lens.intoParams x)         = Lens.intoParams x          -- get_set
(mapScope (mapVars f)).chain (Lens.intoLocalVars x)      = Lens.intoLocalVars (f.chain x)  -- rfl
(mapScope (embedInLocalVars f)).chain (Lens.intoParams x)
    = Lens.intoLocalVars (f.chain (Lens.fst.chain x))                                  -- rfl
(mapScope (embedInLocalVars f)).chain (Lens.intoLocalVars x)
    = Lens.intoLocalVars (f.chain (Lens.snd.chain x))                                  -- rfl
(mapScope g).chain ProcedureState.globalL                = ProcedureState.globalL      -- get_set
```

What is left after those is a `chain` of tuple-level lenses, which the *algebraic* lemmas
(`Lens.id_chain`, `Lens.chain_id`, `Lens.osnd_chain`, `Lens.ofst_chain`,
`Lens.prodMap_chain_ofst`, `Lens.prodMap_chain_osnd`) collapse into a plain
`Lens.id.ofst.osnd…` chain — the very term `proc` would have produced, so the result prints as
`§w` again.  Those six lemmas are where the two irregular cases live: the shift of a variable that
was last in the callee and no longer is (`prodMap_chain_ofst`), and the identity steps.

A test should pin the outcome against `mkChain (navSteps k n)` for a few concrete shapes, since
the two are written independently.

### How they are built (nothing outside §4 depends on this)

Layered "map one component" combinators, each lawful from its argument's laws, field-wise:

```lean
/-- Transform the second component of a product, keeping the first. -/
def Lens.prodMap {a b c : Type} (f : Lens a b) : Lens (c × a) (c × b) where
  get t   := (t.1, f.get t.2)
  set v t := (v.1, f.set v.2 t.2)

/-- The variables `B` in front of a tail tuple `T`.  Recursing on `B` alone, with the tail as a
*parameter*, is what keeps every step reducible: `typeListToTuple (B ++ C)` for a variable `B`
does not reduce, `tupleApp B T` always does.  At concrete lists the two agree by `rfl`. -/
@[reducible] def tupleApp : List Type → Type → Type
  | [],     T => T
  | b :: B, T => b × tupleApp B T

/-- The tail `T` inside `tupleApp B T` — `trafo`'s tuple layer, `osnd` iterated `|B|` times. -/
def tupleSuffix : (B : List Type) → (T : Type) → Lens T (tupleApp B T)

/-- The block `B`, as its own tuple, inside `tupleApp B T`.  Its two base cases (`[]` via the
existing `Lens.punit`, and the singleton via `Lens.id.ofst`) are where the unwrapped-last-element
encoding is absorbed; the recursive case matches two constructors deep, which is what lets
`typeListToTuple` reduce there. -/
def tupleBlock : (B : List Type) → (T : Type) → Lens (typeListToTuple B) (tupleApp B T)

/-- A callee's `(parameters, locals)` pair inside the new variable tuple — `emb`'s tuple layer. -/
def tupleSplit : (A C : List Type) → (T : Type) →
    Lens (typeListToTuple A × typeListToTuple C) (tupleApp A (tupleApp C T))

/-- On the scope, parameters untouched (for `widen`). -/
def ProcedureScope.mapVars {P : List Type} {Ls₁ Ls₂ : List (Σ t : Type, Inhabited t)}
    (f : Lens (typeListToTuple (localTypes Ls₁)) (typeListToTuple (localTypes Ls₂))) :
    Lens (ProcedureScope P Ls₁) (ProcedureScope P Ls₂) where
  get s   := ⟨s.params, f.get s.localVars⟩
  set v s := ⟨v.params, f.set v.localVars s.localVars⟩

/-- On the scope, a whole foreign scope placed inside the local variables (for `embedCallee`);
the target's own parameters are untouched. -/
def ProcedureScope.embedInLocalVars {P P_c Ls Ls_c}
    (f : Lens (typeListToTuple P_c × typeListToTuple (localTypes Ls_c))
              (typeListToTuple (localTypes Ls))) :
    Lens (ProcedureScope P_c Ls_c) (ProcedureScope P Ls) where
  get s   := ⟨(f.get s.localVars).1, (f.get s.localVars).2⟩
  set v s := ⟨s.params, f.set (v.params, v.localVars) s.localVars⟩

/-- On the full state; the global half is untouched. -/
def ProcedureState.mapScope {L₁ L₂ : Type} (g : Lens L₁ L₂) :
    Lens (ProcedureState L₁) (ProcedureState L₂) where
  get t   := ⟨t.global, g.get t.locals⟩
  set v t := ⟨v.global, g.set v.locals t.locals⟩
```

so, with `T := typeListToTuple (localTypes Ls)` and `localTypes B = P_c ++ localTypes Ls_c` (which
holds by `rfl` at concrete lists, since `B` is built as the callee's parameters followed by its
locals):

```lean
trafo := ProcedureState.mapScope (ProcedureScope.mapVars (tupleSuffix (localTypes B) T))
emb   := ProcedureState.mapScope (ProcedureScope.embedInLocalVars
           (tupleSplit P_c (localTypes Ls_c) T))
```

The `intoLocalVars` lemmas above hold definitionally (`osnd`'s `set` overwrites the suffix, so no
read-back occurs); the `intoParams` and `globalL` ones are one `Lens.ext` each, proved once —
`mapScope`/`mapVars` write the untouched half back with the value they just read.

## 5. `applyLens` (Lean-side)

Nothing like this exists yet (`Lens.chain` is there; `Getter`/`Setter` composition is not).

```lean
def Lens.chainGetter {a s t} (l : Lens s t) (g : Getter a s) : Getter a t :=
  ⟨fun τ => g.get (l.get τ)⟩

def Lens.chainSetter {a s t} (l : Lens s t) (x : Setter a s) : Setter a t where
  set v τ  := l.set (x.set v (l.get τ)) τ
  set_set  := by …   -- `l.set_get`, `x.set_set`, `l.set_set`

/-- Re-target a statement along a lens between its states.  The `call'` case does *not* recurse
into the callee: its body/locals/return live at the callee's own scope, which `l` does not
mention. -/
def StmtWithHoles.applyLens {h L₁ L₂} (l : Lens (ProcedureState L₁) (ProcedureState L₂)) :
    StmtWithHoles h L₁ → StmtWithHoles h L₂
  | .skip             => .skip
  | .sample x e       => .sample (l.chainSetter x) (l.chainGetter e)
  | .call' x ls b r p => .call' (l.chainSetter x) ls b r (l.chainGetter p)
  | .hole n x p       => .hole n (l.chainSetter x) (l.chainGetter p)
  | .seq s₁ s₂        => .seq (s₁.applyLens l) (s₂.applyLens l)
  | .ifThenElse c t e => .ifThenElse (l.chainGetter c) (t.applyLens l) (e.applyLens l)
  | .while c b        => .while (l.chainGetter c) (b.applyLens l)
```

## 6. The pipeline

Five functions.  Only the first can fail.

```lean
structure FlattenStep where
  stmt      : Expr   -- at the widened scope
  newLocals : Expr   -- `B ++ Ls`
  trafo     : Expr   -- §4
  proof     : Expr   -- `‹input›.EquivInLens stmt trafo`   (§9); always built, never optional

/-- 6.1 — flatten call number `n`, uncleaned.  Throws if there is no such call, or it is not
flattenable per §2. -/
def flattenCall (n : Nat) (stmt : Expr) : MetaM FlattenStep

/-- 6.2 — push `applyLens` / `chain*` inwards as far as the terms allow.  Never fails; the proof
is a plain equality of statements, so this really is a `Simp.Result`. -/
def cleanStmt (stmt : Expr) : MetaM Simp.Result

/-- 6.3 — re-associate `seq` to the right.  Never fails; `Equiv` is `EquivInLens … Lens.id`. -/
def flattenSeq (stmt : Expr) : MetaM (Expr × Expr)   -- proof : `‹input›.Equiv result`

/-- 6.4 — 6.1 followed by 6.2 and 6.3, proofs composed. -/
def flattenCallCleaned (n : Nat) (stmt : Expr) : MetaM FlattenStep

/-- 6.5 — repeat 6.4 until no flattenable call is left. -/
def flattenProcedureCalls (stmt : Expr) : MetaM FlatteningResult
```

Two more, in §11 — a callee named through modules is not spelled out at the call site, so §2
refuses it until it has been evaluated:

```lean
/-- 11 — evaluate a term built from modules to the procedure it denotes. -/
def unfoldProcedure (e : Expr) : MetaM Simp.Result

/-- 11 — do that to the callee of call site `n`. -/
def inlineProcedureRaw (n : Nat) (stmt : Expr) : MetaM Simp.Result

/-- 11 — and then flatten that call site (6.4). -/
def inlineProcedure (n : Nat) (stmt : Expr) : MetaM FlattenStep

/-- 11 — the same on a procedure rather than a statement, through the §8 wrapper. -/
def inlineInProcedure (n : Nat) (p : Expr) : MetaM (Expr × Expr)
```

### 6.1 `flattenCall` — the only interesting one, and deliberately dumb

Recursion down to call `n`; **every subprogram that does not contain the call is replaced
wholesale** by `applyLens trafo sub`, and every expression on the path (an `if`/`while` guard) by
`trafo.chainGetter e`.  No statement off the path is inspected — an `x <- e` is never even looked
at — so there are no case distinctions beyond the four structural ones:

```
target call        ↦ ‹the expansion below›
seq a b            ↦ seq (rec a) (applyLens trafo b)     -- target in `a`
                   ↦ seq (applyLens trafo a) (rec b)     -- target in `b`
ifThenElse c t e   ↦ ifThenElse (trafo.chainGetter c) (rec t) (applyLens trafo e)   -- and mirrored
while c b          ↦ while (trafo.chainGetter c) (rec b)
let x : T := v; s  ↦ let x : T := v; rec s               -- binder kept verbatim
```

The last case is the `let`/`have`/`letI`/`haveI` statement form, which is a Lean `let` in the
term rather than a `StmtWithHoles` constructor.  The recursion goes under it and **the bound
value is not interpreted**: binder name, type and value are kept exactly as they are, still typed
at the *old* scope.  That is consistent, because everything the recursion emits either lives at
the old scope (the `applyLens trafo sub` subterms, where `x` is directly usable) or is built from
old-scope pieces by composition (`trafo.chainSetter x`, `trafo.chainGetter e`) — so a user who
hid a variable behind `let x' := x` just gets `trafo.chainSetter x'`, with no attempt to see
through the binder.  One cosmetic consequence: such a `let` prints with its old-scope type
ascription inside a statement that is otherwise at the new scope.

Flattening a call *inside* a `while` body is sound precisely because of the default-initialisation
below,
which re-runs on every iteration.

The expansion of `x <- call ‹proc (z₁ … zₙ) { var w₁ …; S; return e }› (args);` is four pieces,
all at the new scope, all built naively — no simplification, that is §6.2's job:

1. `wᵢ <- ‹default›;` per callee local, from the new slot lens and the `Inhabited` instance in the
   callee's `locals` sigma.  Needed because the callee's locals are `default`-initialised on
   *every* call, whereas a flattened-in local is initialised once, at procedure entry;
2. `zᵢ <- ‹πᵢ ∘ trafo.chainGetter args›;` per parameter — the projection composed on the outside,
   not pushed into the argument expression.  Sound in this order because the `zᵢ` are fresh, so no
   assignment can disturb a later `args` read;
3. `S.applyLens emb` — the callee's body, wholesale, whatever shape it has;
4. `x <- emb.chainGetter e;` with l-value `trafo.chainSetter x`, dropped when `x` is
   `Setter.throwaway`.

### 6.2 `cleanStmt` — normalisation, never fails

**Not** a `simp` call with the default simp set.  A recursion over the statement structure that
rewrites with an *explicit, closed* list of lemmas at the positions where they are meant to fire,
using `Simp` only as the rewriting engine with that list, `zeta := false` (so statement `let`s
survive untouched), and every other automatic behaviour off.  Unrestricted simping would unfold
binders, `liftLens`, or lens structures at will and undo exactly the shape the delaborators need.

The lemmas, in three groups, all plain equalities of terms:

1. **Through the constructors** — the defining equations of `applyLens`, `rfl`.  Plus
   `applyLens l (.assign x e) = .assign (l.chainSetter x) (l.chainGetter e)` (`assign` is a `def`
   over `sample`).  Two nested wrappers collapse:
   `(s.applyLens l).applyLens m = s.applyLens (m.chain l)`.
2. **Into l-values** — `l.chainSetter (Lens.toSetter x) = Lens.toSetter (l.chain x)` (`rfl`), then
   §4's chain lemmas; `l.chainSetter Setter.throwaway = Setter.throwaway` (needs `get_set`), so a
   void call stays void; and, since `liftLens` of a *global* lens is
   `(ProcedureState.globalL.chain x).toSetter`, the global-preservation lemma sends it back to
   `liftLens x`.
3. **Into expressions** — the group that keeps the output printable.  A composed `GaudiExpr`
   getter beta-reduces to `Getter.mk (fun τ => body[st := l.get τ])`, and the reads inside `body`
   are `Evaluatable.eval`.  With `Evaluatable.eval (l.get τ) x = Evaluatable.eval τ (l.chain x)`
   (`rfl`, both sides are `x.get (l.get τ)`) for a full-state variable, and global-preservation
   for a global one, every read becomes a read of the *new* variable and `l.get τ` disappears — so
   the result prints as `§x` again.  Projections `πᵢ ∘ getter` are pushed inside here too, and
   taken structurally when the body is a literal `Prod.mk` (which is what `mkArgTuple` builds), so
   `z <- §x + §x;` comes out rather than `z <- (§x + §x).1;`.

Whatever does not match — an opaque getter, a non-literal callee body — keeps its wrapper.
Correctness is unaffected (§9); only prettiness suffers.  Worth having standalone: it is useful
after any transformation that leaves `applyLens` behind.

*As built*, the traversal is `simp`'s own: one `simp only` over the whole statement with
`Flatten.cleanLemmas` as the entire theorem set, `Flatten.cleanUnfold` (just `Lens.chainGetter`,
which has to go for the `eval` lemmas to see the state it composes with) as the only unfolding,
and **every** switch that could touch a `let` turned off — `zeta` and `zetaDelta` (substituting a
binder), `zetaUnused` (dropping a binder the statement happens not to mention — still a variable
of the scope), `zetaHave` (the `proc` macro's binders are `have`s) and `letToHave` (which would
rewrite the very telescope the delaborators read).  Also `weaken`, which the expansion of §6.1
leaves around its two hole-free pieces, is pushed inwards by the same lemma set.

What this *cannot* do is rewrite under a `let`-bound variable name: `x` is opaque, so
`trafo.chain x` is stuck.  That is what §7 is for.

### 6.3 `flattenSeq`

`flattenCall` splices a four-statement block into one position, so the spine comes out as
`a; (b; c); d`.  Re-associating is *not* a syntactic equality (`seq` is a constructor), it is
`bind`-associativity at the denotation level — hence the denotational-equivalence proof, at
`Lens.id`.

It also drops `skip`s (`skip; s ≈ s` and `s; skip ≈ s`), which the expansion produces whenever a
callee has no locals or no parameters, and which is the same kind of denotational step.  It does
*not* touch `if`s (no collapsing of `if c { s } else { s }`) or anything else — this pass is only
about the shape of the sequence.  Also useful standalone.

### 6.4 / 6.5 — composition

Composing needs one lemma,
`EquivInLens a b l → EquivInLens b c m → EquivInLens a c (m.chain l)`, of which `Equiv` (6.3) is
the `m := Lens.id` case; cleaning contributes plain `=`, which rewrites in by `▸`.

`flattenProcedureCalls` (6.5) then loops: find the first flattenable call, run 6.4, repeat on the
result.  The
composite lens is the chain of the per-round ones, `trafoₖ.chain (… (trafo₁))`; a normalisation
lemma collapsing two prepends into one (`Scope.widen B₂` after `Scope.widen B₁` equals
`Scope.widen (B₂ ++ B₁)`) would keep that a single lens, and is worth having but is not
needed for correctness.

Termination: each round replaces one `call` node by the callee's body, whose own calls were
already inside that subtree, so the total number of `call` nodes strictly decreases.

## 7. Reassembling

At statement level the result is the rebuilt telescope over the new statements:

```
‹let-telescope: params, then all of B ++ Ls, then holes› ‹new statements›
```

with the `B` lets first inside the locals group (they are slots `0 … |B|-1`), the old locals
after them, and the binder names as fixed in §3.

A variable's *name* lives in a `let` binder, its *identity* in that binder's value (a slot chain
`Lens.id.ofst.osnd^k`, exactly what `mkChain (navSteps k n)` builds in `ProgramSyntax.lean`).
§6.2 cannot see through the name, so cleaning is sandwiched between the two halves of §7:

* `exposeStmt` walks the statement, **zeta-reduces every `let` whose value is a variable** —
  the enclosing telescope *and* the callee's, which arrives inline in the spliced-in body —
  and records `(scope, is-a-parameter, slot) ↦ name` as it goes.  A `let` binding anything else
  (a hole index, a user's own abbreviation) is kept as a binder, and references through it keep
  their `applyLens` wrapper: that is the degradation the "descend into `let`s but do not
  interpret the bound value" decision buys.
* `retelescope` builds the new telescope from the recorded names and `kabstract`s the new slot
  chains out of the statement *and the proof*, so both come back with binders in place.

Naming: the enclosing statement's own variables claim their names first, so a collision renames
the **callee's** variable (`w`, `w0`, `w1`, …) — the caller's names are the ones anything outside
the statement may still refer to.  A slot no telescope named gets `pₖ`/`vₖ`.

## 8. The `ProcedureWithHoles` wrapper

`flattenProcedure` does only bookkeeping: run the pipeline on `body`, put `B ++ Ls` into the
`locals` field, and replace `return_val` by `trafo.chainGetter return_val` (normalized by §6.2),
rebuilding its telescope the same way.  `delabProc` peels exactly `#params` `Lens.intoParams`
lets, then `#locals` `Lens.intoLocalVars` lets, then the holes, in both fields, and requires the
two name lists to agree — so the return value is re-bound with *the telescope the body got*
(peeled straight off the flattened body), not with one built independently.

It is stated for **hole-free** procedures, because that is where the soundness statement lives:
`procedureDenotation_congr` turns §6.5's `EquivInLens` into
`procedureDenotation new = procedureDenotation old`, which is what a *caller* of the procedure can
use.  A `ProcedureWithHoles` can still be flattened at statement level (§6.5 quantifies over the
instantiation); only the procedure-level equation is missing for it.

## 9. The result and its soundness

```lean
structure FlatteningResult where
  stmt      : Expr   -- the flattened statement: `StmtWithHoles hCtx (ProcedureScope P (B ++ Ls))`
  newLocals : Expr   -- the new locals list `B ++ Ls`, i.e. the type index of `stmt`
  trafo     : Expr   -- §4, composed over all rounds
  proof     : Expr   -- `‹input stmt›.EquivInLens stmt trafo`
  count     : Nat    -- how many calls were flattened; nonzero (else we threw)
```

This is not a `Simp.Result`: the rewrite preserves the *denotation*, not the term.  (The
individual cleaning pass, 6.2, *is* one.)

Deliberately *not* here: per-call bookkeeping and a list of calls left alone with a reason.  Both
are re-derivable from `stmt`/`newLocals`, and if they are ever wanted they should come back as
**one** array over a sum type — flattened and skipped calls interleave in the statement, and two
separate arrays lose that order.

### The relation

wp-free (`SubProbability` is a monad, so lifting a state map to a distribution is `<$>`):

```lean
/-- Push a state map through a denotation's result: `(u, τ) ↦ (u, f τ)`. -/
@[reducible] noncomputable def SubProbability.mapState {α s t : Type} (f : t → s)
    (μ : SubProbability (α × t)) : SubProbability (α × s) :=
  (fun p => (p.1, f p.2)) <$> μ

/-- `b`, on the wide state `t`, is denotationally equivalent to `a`, on the narrow state `s`,
    in the lens `l : Lens s t`. -/
def ProgramDenotation.EquivInLens {s t α : Type}
    (a : ProgramDenotation s α) (b : ProgramDenotation t α) (l : Lens s t) : Prop :=
  ∀ (sa : s) (sb : t), sa = l.get sb → (b sb).mapState l.get = a sa

/-- Statement level.  `programDenotation` needs a hole-free statement and the rewrite leaves hole
    indices untouched, so the instantiation is quantified — the same one on both sides. -/
def StmtWithHoles.EquivInLens {hCtx L₁ L₂} (a : StmtWithHoles hCtx L₁) (b : StmtWithHoles hCtx L₂)
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) : Prop :=
  ∀ inst : hCtx.Instantiation,
    (programDenotation (a.instantiate inst)).EquivInLens
      (programDenotation (b.instantiate inst)) l

abbrev StmtWithHoles.Equiv {hCtx L} (a b : StmtWithHoles hCtx L) : Prop :=
  a.EquivInLens b Lens.id
```

Nothing is assumed about the fresh block's initial value (it is quantified over `sb`), which is
sound precisely because of the `w <- default;` / `z <- args;` prefix of §6.1.  The premise
`sa = l.get sb` is logically redundant but is the shape one wants for `apply`/`rw`.

### Why the pass split modularizes the proof

Each pass proves its own thing, and they never mix:

* **6.1** — the denotational content, on the deliberately ugly term.  Two ingredients:

  * the generic transport lemma
    ```lean
    theorem programDenotation_applyLens (l) (s) (inst) :
        programDenotation ((s.applyLens l).instantiate inst)
          = ProgramDenotation.zoom l (programDenotation (s.instantiate inst))
    ```
    (`applyLens` commutes with `instantiate` by induction; the equation is an induction over the
    statement, using `l.set_get` for a `seq` and `l.set_set` for the write-back, with `while` the
    one nontrivial case — `while_loop` is an ω-CPO fixpoint, so it needs `mapState` ω-continuity,
    and `OmegaCompletePartialOrder (SubProbability a)` and `SubProbability.bind_mono` are already
    in `SubProbability.lean`).  Its corollary `s.EquivInLens (s.applyLens l) l` holds for
    *arbitrary* `s` — this is the "`applyLens l s` is always the right replacement for `s`" fact,
    and it is what lets §2 drop the literal requirement on the callee's body, and what lets 6.1
    replace whole subprograms without looking at them;
  * one **call-flattening lemma**: `call x p args` at the old scope is `EquivInLens`, along
    `trafo`, to the
    four-part expansion.  Its hypotheses are the freshness facts relating `emb` and `trafo`, both
    `rfl` at concrete lists: both preserve `global`, and
    `trafo.get (emb.set v τ) = ProcedureState.globalL.set v.global (trafo.get τ)` ("writing the
    callee's block is invisible through `trafo`, except for the global part").

  `EquivInLens l` is a congruence for `seq` (monad-law algebra on `map`/`bind`, no integrals),
  `ifThenElse` (pointwise) and `while` (the fixpoint argument again), so the proof is assembled
  structurally along the path to the call.

* **6.2** — plain `=` between statements; transports into the above by `rw`.  A term that fails to
  normalize costs prettiness, never correctness.
* **6.3** — `bind`-associativity, i.e. `Equiv`; composed by the transitivity lemma.

Bridges out, when a `wp` goal is what one actually has:
`b.wp (fun p => F (p.1, l.get p.2)) σ = a.wp F (l.get σ)` (one `congrArg ….expected` plus
`expected`-of-`map`), and from there `EquivModuloLens ‹block› b (ProgramDenotation.zoom l a)` in
the existing calculus of `Logic/EquivModuloLens.lean`.

### Procedure level (the §8 wrapper)

```lean
procedureDenotation ⟨B ++ Ls, new, trafo.chainGetter retval⟩ args
  = procedureDenotation ⟨Ls, old, retval⟩ args
```

from `EquivInLens` plus three cheap side facts:
`trafo.get ⟨st, localVariableInit (B ++ Ls) args⟩ = ⟨st, localVariableInit Ls args⟩` (`rfl` at
concrete lists — the fresh block gets defaults, the parameters are untouched),
`(trafo.chainGetter retval).get τ = retval.get (trafo.get τ)` (`rfl`), and
`(trafo.get τ).global = τ.global` (`rfl`).

## 10. Testing

`InlineTest.lean` (sibling, imported from `GaudisCrypt.lean` like the other `*Test.lean` files),
with **one command per pass** so failures localize.  Every command `Meta.check`s both the produced
term and the produced proof, and checks the proof's type against the expected statement — that,
not the printed output, is the real regression guard.

* `#flattenCall n` — the **uncleaned** output of 6.1, printed with `set_option pp.gaudisCrypt
  false` (an uncleaned term is full of `applyLens` and `chain*` and does not fit the surface
  syntax anyway).  This is the layer to test most heavily: its output is completely determined by
  the input's *shape*, with no simp set in the loop, so an expected-output test
  (`/-- info: … -/ #guard_msgs in`) is stable and a failure points at one recursion step.  The
  four structural cases, the four pieces of the expansion, and the block/lens arguments are all
  visible there.
* `#clean` — 6.2 applied to a term produced by `#flattenCall`, so cleaning is tested against a
  fixed, hand-checkable input rather than against whatever the flattener happens to emit.  Expected
  output is in surface syntax; add a `#roundtrip` (from `ProgramSyntaxTest.lean`) on the result,
  since printing back to `proc … { … }` is exactly what cleaning is for.
* `#flattenSeq` — 6.3 alone, on a hand-written `a; (b; c); d`.
* `#flatten` — the whole pipeline (6.5), before/after programs in surface syntax.

Below that, plain Lean tests for §4/§5, which need no meta code at all: the six interface lemmas
at a few concrete list shapes (`rfl`), `slot Ts ⟨k, _⟩ = mkChain (navSteps k n)` for several
shapes (the two are written independently, and everything printable depends on their agreement),
and `Scope.widen`/`Scope.embedCallee` instantiated at the degenerate shapes — no locals, one
local, callee with one variable — which is where §4's base cases live.

Cases to cover across the levels: several calls in one body; nested calls (the fixed point of
6.5); a call inside `if` / `while`; a name collision (`w`, `w0`); a callee with zero parameters
and zero locals; a statement with no locals of its own; a callee with several parameters (tuple
splitting); a callee whose body is an opaque constant (flattened, with `applyLens` surviving in
the output — worth an expected-output test at the `#clean` level too, to pin *how* it survives);
a `hole` and a non-literal-locals callee left alone; the "nothing to flatten" error.

## Implementation status

Done (this file, below the plan):

* §4's lens layer — `Lens.prodMap`, `tupleApp`/`tupleSuffix`/`tupleBlock`/`tupleSplit`,
  `ProcedureScope.mapVars`/`embedInLocalVars`, `ProcedureState.mapScope`, the algebraic `chain`
  lemmas and the five-lemma interface;
* §5's `Lens.chainGetter`/`chainSetter`, `StmtWithHoles.applyLens` and
  `StmtWithHoles.applyLens_instantiate`;
* §9's relations (`SubProbability.mapState`, `ProgramDenotation.EquivInLens`,
  `StmtWithHoles.EquivInLens`/`Equiv`) and the transport theorem: `zoom` against every primitive
  (`zoom_chain`/`zoom_get`/`zoom_set`/`zoom_lift`/`zoom_bot`/`zoom_ωScottContinuous`/`zoom_while`,
  the loop case by the Kleene/ωSup argument), then `programDenotation_applyLens` and its
  corollary `StmtWithHoles.equivInLens_applyLens` — "`applyLens l s` is always the right
  replacement for `s`", for an arbitrary `s`.

* the congruences: `EquivInLens.{pure,bot,get,set,lift,bind,ωSup,while_loop,refl,trans}` at
  denotation level and `StmtWithHoles.EquivInLens.{seq,ifThenElse,while,trans}` /
  `StmtWithHoles.Equiv.refl` at statement level;
* **`equivInLens_flattenCall`** — the one step with real content: a call is equivalent, along
  `trafo`, to prelude + `applyLens emb` of the callee's body + the return store, given that both
  lenses preserve globals and that writing the callee's slice is invisible through `trafo` except
  for the global part;
* the applied forms the meta code needs to instantiate it —
  `procedureDenotation_apply`, `programDenotation_call'_apply`, `flattenedCall_apply`,
  `programDenotation_assign_apply` — and `flattenSeq`'s equations
  (`StmtWithHoles.Equiv.{seq_assoc, skip_seq, seq_skip}`).

* **§6.1 `flattenCall`** and its helpers (`unfoldStmt`, `listLitElems`, `countCallSites`,
  `callData?`,
  `planCall`, `rebuildPath`), plus the `#flattenCall` command and a first end-to-end case in
  `InlineTest.lean`.  Three things the implementation settled:
  - statement positions are seen through with `whnf` at **`zeta := false`** (`unfoldStmt`), so
    `someProc.body` and `StmtWithHoles.call` are unfolded while the `let` telescope that carries
    the variable *names* survives; list literals are read at **reducible** transparency, which is
    exactly what makes §2's "literal callee" rule bite (a callee named by a `def` stays stuck);
  - the call site is planned **where it is found**, inside whatever `let` binders enclose it —
    the call mentions their variables — and the lenses flow back *up* the recursion, since they
    are only known once the callee has been seen;
  - the three freshness side conditions really are `rfl` at concrete variable lists: `mkRflProof`
    discharges them and `Meta.check` accepts the assembled proof.

* **§6.2 `cleanStmt`** (`cleanLemmas`, `cleanUnfold`, `cleanContext`), **§7** (`exposeStmt` /
  `exposeTerm` / `retelescope`, with `peelLets`/`rebindLets` and the slot-chain pair
  `mkSlotLens`/`slotOfLens?`), **§6.3 `flattenSeq`** (with `concatSeq`), and the compositions
  **§6.4 `flattenCallCleaned`** / **§6.5 `flattenProcedureCalls`**;
* **§8 `flattenProcedure`** and the procedure-level theorem `procedureDenotation_congr`;
* **§10**: `InlineTest.lean` has `#flattenCall`, `#flattenCallCleaned`, `#flattenSeq`, `#flatten`
  and `#flattenProc`, each `Meta.check`ing both the term and the proof, over the case list below
  — several calls with a name collision, nested calls (two rounds), calls inside `if` and
  `while`, several parameters, a zero-parameter/zero-local callee, and the two error cases
  (`#guard_msgs`-pinned);
* **§11** — `unfoldProcedure`, which evaluates a term built from modules to the procedure it
  denotes, the two functions that put it to work on a statement (`inlineProcedureRaw` and
  `inlineProcedure`), and `inlineInProcedure`, which does that to a procedure through the §8
  wrapper (now `inProcedure`, shared with `flattenProcedure`).  See the section itself, below §8,
  for what it steps with and why it is all head-position; `InlineTest.lean` has `#unfoldProc`,
  `#inlineRaw`, `#inline` and `#inlineProc`.

Four things that stage settled:

  - cleaning cannot rewrite under a `let`-bound variable name, which is what forced §7 into the
    shape it has: zeta the variable telescopes (remembering names), clean, rebuild.  `kabstract`
    is what puts the binders back, on the statement *and* the proof at once;
  - `simp` has five separate ways to disturb a `let` — `zeta`, `zetaDelta`, `zetaUnused`,
    `zetaHave` and `letToHave` — and all five have to be off.  `zetaUnused` in particular
    silently drops a variable the statement does not happen to mention; so does `mkLetFVars`
    unless it is passed `usedLetOnly := false`, which is why `rebuildPath` passes it;
  - `whnf` at a statement position steps *through* `assign` (a `def` over `sample`), which costs
    the surface form; `openStmt` stops at a known statement head and `foldAssign` folds the
    desugaring back when it cannot;
  - the composite lens of a multi-round §6.5 is a `Lens.chain` of the rounds' lenses, so
    `Lens.chain_assoc` has to be in the cleaning set — otherwise the *return value* (the one
    place that sees the composite rather than a single round's lens) does not normalize.

Not done:

* a rewriting tactic (deliberately out of scope, §0);
* the §8 wrapper for procedures that still have holes (see §8);
* the plain, meta-free tests of §4/§5 that §10 asks for below the pass-level ones;
* inlining a callee named by a plain *definition* rather than by a module expression.  §11 does
  reach that case — a constant at a procedure position is unfolded — but only a module term gets
  the head-position evaluation that makes the result predictable.
-/

namespace GaudisCrypt

/-! ## Lens helpers

TODO(move): everything in this section is about `Lens` alone and would fit
`Language/Lens.lean` once it has proved its worth here. -/

/-- Transform the second component of a product, keeping the first. -/
def Lens.prodMap {a b c : Type} (f : Lens a b) : Lens (c × a) (c × b) where
  get t := (t.1, f.get t.2)
  set v t := (v.1, f.set v.2 t.2)
  set_get s x := by simp [f.set_get]
  set_set s x y := by simp [f.set_set]
  get_set s := by simp [f.get_set]

/-- Compose a getter with a lens between its containers. -/
def Lens.chainGetter {a s t : Type} (l : Lens s t) (g : Getter a s) : Getter a t where
  get τ := g.get (l.get τ)

/-- Compose a setter with a lens between its containers. -/
def Lens.chainSetter {a s t : Type} (l : Lens s t) (x : Setter a s) : Setter a t where
  set v τ := l.set (x.set v (l.get τ)) τ
  set_set σ u v := by simp [l.set_get, x.set_set, l.set_set]

@[simp] theorem Lens.id_chain {a m : Type} (y : Lens a m) : Lens.chain Lens.id y = y := rfl

@[simp] theorem Lens.chain_id {a m : Type} (x : Lens a m) : Lens.chain x Lens.id = x := rfl

/-- Chaining is associative. -/
theorem Lens.chain_assoc {a b c d : Type} (x : Lens c d) (y : Lens b c) (z : Lens a b) :
    (x.chain y).chain z = x.chain (y.chain z) := rfl

/-- Navigating into the second component and then further is one `osnd`. -/
@[simp] theorem Lens.osnd_chain {a b m m' : Type} (f : Lens b m) (y : Lens a b) :
    (Lens.osnd (m' := m') f).chain y = Lens.osnd (f.chain y) := rfl

/-- Navigating into the first component and then further is one `ofst`. -/
@[simp] theorem Lens.ofst_chain {a b m m' : Type} (f : Lens b m) (y : Lens a b) :
    (Lens.ofst (m' := m') f).chain y = Lens.ofst (f.chain y) := rfl

/-- `prodMap` leaves the first component alone, so navigating there ignores it. -/
@[simp] theorem Lens.prodMap_chain_ofst {a b c d : Type} (f : Lens a b) (y : Lens d c) :
    (Lens.prodMap (c := c) f).chain (Lens.ofst y) = Lens.ofst y := by
  refine Lens.ext _ _ fun v s => ?_
  change (y.set v s.1, f.set (f.get s.2) s.2) = (y.set v s.1, s.2)
  rw [f.get_set]

/-- `prodMap` acts on the second component, where it composes. -/
@[simp] theorem Lens.prodMap_chain_osnd {a b c d : Type} (f : Lens a b) (y : Lens d a) :
    (Lens.prodMap (c := c) f).chain (Lens.osnd y) = Lens.osnd (f.chain y) := rfl

/-! ## Variable tuples

`typeListToTuple` leaves the *last* element unwrapped (`[T] ↦ T`), so
`typeListToTuple (x :: xs) = x × typeListToTuple xs` holds only when `xs ≠ []` — and for a
variable `xs` the match is stuck.  `tupleApp B T` — "the variables `B`, with `T` in tail
position" — recurses on `B` alone and therefore always reduces; it is the shape every lens below
is stated in.  At concrete lists `tupleApp B (typeListToTuple C)` and `typeListToTuple (B ++ C)`
are definitionally equal (for `C ≠ []`), which is all the meta code needs. -/

/-- The variables `B` in front of a tail tuple `T`: `tupleApp [b₀, b₁] T = b₀ × (b₁ × T)`. -/
@[reducible] def tupleApp : List Type → Type → Type
  | [],     T => T
  | b :: B, T => b × tupleApp B T

/-- The tail `T` inside `tupleApp B T` — `osnd` iterated `|B|` times. -/
def tupleSuffix : (B : List Type) → (T : Type) → Lens T (tupleApp B T)
  | [],     _ => Lens.id
  | _ :: B, T => (tupleSuffix B T).osnd

/-- The block `B`, as its own tuple, inside `tupleApp B T`.  The two base cases are where the
unwrapped-last-element encoding is absorbed. -/
def tupleBlock : (B : List Type) → (T : Type) → Lens (typeListToTuple B) (tupleApp B T)
  | [],          _ => Lens.punit
  | [_],         _ => Lens.id.ofst
  | _ :: b :: B, T => (tupleBlock (b :: B) T).prodMap

/-- A callee's `(parameters, locals)` pair inside the new variable tuple: `A` are its parameter
types, `C` its local types, `T` the tail (the enclosing statement's own variables). -/
def tupleSplit : (A C : List Type) → (T : Type) →
    Lens (typeListToTuple A × typeListToTuple C) (tupleApp A (tupleApp C T))
  | [],          C, T =>
      { get t := ((), (tupleBlock C T).get t)
        set v t := (tupleBlock C T).set v.2 t
        set_get s x := by simp [(tupleBlock C T).set_get]
        set_set s x y := by simp [(tupleBlock C T).set_set]
        get_set s := by simp [(tupleBlock C T).get_set] }
  | [_],         C, T => (tupleBlock C T).prodMap
  | _ :: b :: A, C, T =>
      let rec' := tupleSplit (b :: A) C T
      { get t := ((t.1, (rec'.get t.2).1), (rec'.get t.2).2)
        set v t := (v.1.1, rec'.set (v.1.2, v.2) t.2)
        set_get s x := by simp [rec'.set_get]
        set_set s x y := by simp [rec'.set_set]
        get_set s := by simp [rec'.get_set] }

/-! ## Scope and state layers

Widening a scope and embedding a callee's scope both only touch the *local variables* of a
`ProcedureScope`, and never the `global` half of a `ProcedureState`; both layers are therefore
"map one component" and lawful from their argument's laws, field-wise. -/

variable [ProgramSpec]

/-- Transform the local variables of a scope, keeping the parameters. -/
def ProcedureScope.mapVars {P : List Type} {Ls₁ Ls₂ : List (Σ t : Type, Inhabited t)}
    (f : Lens (typeListToTuple (localTypes Ls₁)) (typeListToTuple (localTypes Ls₂))) :
    Lens (ProcedureScope P Ls₁) (ProcedureScope P Ls₂) where
  get s := ⟨s.params, f.get s.localVars⟩
  set v s := ⟨v.params, f.set v.localVars s.localVars⟩
  set_get s x := by simp [f.set_get]
  set_set s x y := by simp [f.set_set]
  get_set s := by simp [f.get_set]

/-- Place a whole foreign scope (a callee's parameters *and* locals) inside the local variables
of another one; the host's own parameters are untouched. -/
def ProcedureScope.embedInLocalVars {P P_c : List Type}
    {Ls Ls_c : List (Σ t : Type, Inhabited t)}
    (f : Lens (typeListToTuple P_c × typeListToTuple (localTypes Ls_c))
              (typeListToTuple (localTypes Ls))) :
    Lens (ProcedureScope P_c Ls_c) (ProcedureScope P Ls) where
  get s := ⟨(f.get s.localVars).1, (f.get s.localVars).2⟩
  set v s := ⟨s.params, f.set (v.params, v.localVars) s.localVars⟩
  set_get s x := by simp [f.set_get]
  set_set s x y := by simp [f.set_set]
  get_set s := by simp [f.get_set]

/-- Transform the scope of a `ProcedureState`, keeping the global state. -/
def ProcedureState.mapScope {L₁ L₂ : Type} (g : Lens L₁ L₂) :
    Lens (ProcedureState L₁) (ProcedureState L₂) where
  get t := ⟨t.global, g.get t.locals⟩
  set v t := ⟨v.global, g.set v.locals t.locals⟩
  set_get s x := by simp [g.set_get]
  set_set s x y := by simp [g.set_set]
  get_set s := by simp [g.get_set]

/-! ### The interface: what a variable lens becomes under the two transformations

These six are the whole contract of the sections above.  The meta code composes
`ProcedureState.mapScope (ProcedureScope.mapVars …)` (widening) or
`ProcedureState.mapScope (ProcedureScope.embedInLocalVars …)` (callee embedding) and then
rewrites with these; nothing outside case-splits on how the tuple lenses are built. -/

section Interface
variable {L₁ L₂ : Type} {P P_c : List Type} {Ls Ls₁ Ls₂ Ls_c : List (Σ t : Type, Inhabited t)}

/-- Widening leaves the parameters where they are. -/
@[simp] theorem mapVars_chain_intoParams
    (f : Lens (typeListToTuple (localTypes Ls₁)) (typeListToTuple (localTypes Ls₂)))
    {A : Type} (x : Lens A (typeListToTuple P)) :
    (ProcedureState.mapScope (ProcedureScope.mapVars (P := P) f)).chain (Lens.intoParams x)
      = Lens.intoParams x := by
  refine Lens.ext _ _ fun v s => ?_
  change (⟨s.global, ⟨x.set v s.locals.params, f.set (f.get s.locals.localVars)
    s.locals.localVars⟩⟩ : ProcedureState (ProcedureScope P Ls₂))
      = ⟨s.global, ⟨x.set v s.locals.params, s.locals.localVars⟩⟩
  rw [f.get_set]

/-- Widening shifts a local variable by whatever `f` does to the variable tuple. -/
@[simp] theorem mapVars_chain_intoLocalVars
    (f : Lens (typeListToTuple (localTypes Ls₁)) (typeListToTuple (localTypes Ls₂)))
    {A : Type} (x : Lens A (typeListToTuple (localTypes Ls₁))) :
    (ProcedureState.mapScope (ProcedureScope.mapVars (P := P) f)).chain (Lens.intoLocalVars x)
      = Lens.intoLocalVars (f.chain x) := rfl

/-- A callee's parameter becomes a local variable of the host. -/
@[simp] theorem embedInLocalVars_chain_intoParams
    (f : Lens (typeListToTuple P_c × typeListToTuple (localTypes Ls_c))
              (typeListToTuple (localTypes Ls)))
    {A : Type} (x : Lens A (typeListToTuple P_c)) :
    (ProcedureState.mapScope
        (ProcedureScope.embedInLocalVars (P := P) (Ls := Ls) f)).chain (Lens.intoParams x)
      = Lens.intoLocalVars (f.chain (Lens.fst.chain x)) := rfl

/-- So does a callee's local variable. -/
@[simp] theorem embedInLocalVars_chain_intoLocalVars
    (f : Lens (typeListToTuple P_c × typeListToTuple (localTypes Ls_c))
              (typeListToTuple (localTypes Ls)))
    {A : Type} (x : Lens A (typeListToTuple (localTypes Ls_c))) :
    (ProcedureState.mapScope
        (ProcedureScope.embedInLocalVars (P := P) (Ls := Ls) f)).chain (Lens.intoLocalVars x)
      = Lens.intoLocalVars (f.chain (Lens.snd.chain x)) := rfl

/-- Neither transformation touches the global state. -/
@[simp] theorem mapScope_chain_globalL (g : Lens L₁ L₂) :
    (ProcedureState.mapScope g).chain ProcedureState.globalL = ProcedureState.globalL := by
  refine Lens.ext _ _ fun v s => ?_
  change (⟨v, g.set (g.get s.locals) s.locals⟩ : ProcedureState L₂) = ⟨v, s.locals⟩
  rw [g.get_set]

end Interface

/-! ## Re-targeting a statement along a lens

TODO(move): `StmtWithHoles.applyLens` is about statements in general, not about flattening;
`Language/Programs.lean` would be its home. -/

/-- Re-target a statement along a lens between its states.  The `call'` case does *not* recurse
into the callee: its locals, body and return value live at the callee's own scope, which `l` does
not mention. -/
def StmtWithHoles.applyLens {h : HoleSigs} {L₁ L₂ : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) :
    StmtWithHoles h L₁ → StmtWithHoles h L₂
  | .skip             => .skip
  | .sample x e       => .sample (l.chainSetter x) (l.chainGetter e)
  | .call' x ls b r p => .call' (l.chainSetter x) ls b r (l.chainGetter p)
  | .hole n x p       => .hole n (l.chainSetter x) (l.chainGetter p)
  | .seq s₁ s₂        => .seq (s₁.applyLens l) (s₂.applyLens l)
  | .ifThenElse c t e => .ifThenElse (l.chainGetter c) (t.applyLens l) (e.applyLens l)
  | .while c b        => .while (l.chainGetter c) (b.applyLens l)

/-- `applyLens` commutes with hole instantiation: it never touches a hole's index, and the
`hole ↦ call` step only re-tags the same setter and getter. -/
theorem StmtWithHoles.applyLens_instantiate {h : HoleSigs} {L₁ L₂ : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) (inst : h.Instantiation) :
    ∀ s : StmtWithHoles h L₁,
      (s.applyLens l).instantiate inst = (s.instantiate inst).applyLens l
  | .skip             => rfl
  | .sample _ _       => rfl
  | .call' _ _ _ _ _  => rfl
  | .hole _ _ _       => rfl
  | .seq s₁ s₂        => by
      simp only [StmtWithHoles.applyLens, StmtWithHoles.instantiate,
        applyLens_instantiate l inst s₁, applyLens_instantiate l inst s₂]
  | .ifThenElse _ t e => by
      simp only [StmtWithHoles.applyLens, StmtWithHoles.instantiate,
        applyLens_instantiate l inst t, applyLens_instantiate l inst e]
  | .while _ b        => by
      simp only [StmtWithHoles.applyLens, StmtWithHoles.instantiate,
        applyLens_instantiate l inst b]

/-! ## Denotational equivalence along a lens

TODO(move): `SubProbability.mapState` and `ProgramDenotation.EquivInLens` are general facts about
denotations; `Language/Semantics.lean` (or wherever `ProgramDenotation` grows next) is their
home. -/

/-- Push a state map through a denotation's result: `(u, τ) ↦ (u, f τ)`. -/
noncomputable def SubProbability.mapState {α s t : Type} (f : t → s)
    (μ : SubProbability (α × t)) : SubProbability (α × s) :=
  (fun p => (p.1, f p.2)) <$> μ

/-- `b`, running on the wide state `t`, is denotationally equivalent to `a`, running on the
narrow state `s`, in the lens `l : Lens s t`: from any wide state, running `b` and projecting the
result with `l.get` gives the same subdistribution as running `a` from the projected state.

Nothing is assumed about the part of the wide state that `l` does not see — in particular the
freshly added variables of a flattened call, which the flattened code initialises before it reads
them. -/
def ProgramDenotation.EquivInLens {s t α : Type} (a : ProgramDenotation s α)
    (b : ProgramDenotation t α) (l : Lens s t) : Prop :=
  ∀ (sa : s) (sb : t), sa = l.get sb → (b sb).mapState l.get = a sa

/-- The statement-level relation.  `programDenotation` needs a hole-free statement and the
rewrites here leave hole indices untouched, so the instantiation is quantified — the same one on
both sides. -/
def StmtWithHoles.EquivInLens {hCtx : HoleSigs} {L₁ L₂ : Type}
    (a : StmtWithHoles hCtx L₁) (b : StmtWithHoles hCtx L₂)
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) : Prop :=
  ∀ inst : hCtx.Instantiation,
    (programDenotation (a.instantiate inst)).EquivInLens
      (programDenotation (b.instantiate inst)) l

/-- Denotational equivalence at the *same* scope — what `flattenSeq` returns. -/
abbrev StmtWithHoles.Equiv {hCtx : HoleSigs} {L : Type} (a b : StmtWithHoles hCtx L) : Prop :=
  a.EquivInLens b Lens.id

/-! ## `zoom` against the primitives

TODO(move): these belong next to `ProgramDenotation.zoom_pure`/`zoom_bind` in
`Language/Semantics.lean`. -/

omit [ProgramSpec] in
/-- `ProgramDenotation.get` applied at a state — the `Getter` version of
`ProgramDenotation.get_apply` (which is stated for a `Lens`). -/
theorem ProgramDenotation.get_apply' {s a : Type} (g : Getter a s) (st : s) :
    ProgramDenotation.get g st = pure (g.get st, st) := by
  change (pure (st, st) : SubProbability (s × s)) >>= (fun as => pure (g.get as.1, as.2)) = _
  rw [SubProbability.pure_bind]

omit [ProgramSpec] in
/-- `ProgramDenotation.set` applied at a state — the `Setter` version of
`ProgramDenotation.set_apply` (which is stated for a `Lens`). -/
theorem ProgramDenotation.set_apply' {s a : Type} (x : Setter a s) (v : a) (st : s) :
    ProgramDenotation.set x v st = pure ((), x.set v st) := by
  change (pure (st, st) : SubProbability (s × s)) >>= (fun as => pure ((), x.set v as.1)) = _
  rw [SubProbability.pure_bind]

omit [ProgramSpec] in
/-- Zooming twice is zooming along the chained lens. -/
theorem ProgramDenotation.zoom_chain {s t u a : Type} (x : Lens t u) (y : Lens s t)
    (p : ProgramDenotation s a) :
    ProgramDenotation.zoom (x.chain y) p
      = ProgramDenotation.zoom x (ProgramDenotation.zoom y p) := by
  funext uv
  change (p (y.get (x.get uv)) >>= fun as => pure (as.1, x.set (y.set as.2 (x.get uv)) uv))
       = ((p (y.get (x.get uv)) >>= fun as => pure (as.1, y.set as.2 (x.get uv)))
            >>= fun bs => pure (bs.1, x.set bs.2 uv))
  rw [SubProbability.bind_assoc]
  congr 1; funext as
  rw [SubProbability.pure_bind]

omit [ProgramSpec] in
/-- Reading through a zoomed lens is reading through the composed getter. -/
theorem ProgramDenotation.zoom_get {s t a : Type} (l : Lens s t) (g : Getter a s) :
    ProgramDenotation.zoom l (ProgramDenotation.get g)
      = ProgramDenotation.get (l.chainGetter g) := by
  funext tv
  change ProgramDenotation.get g (l.get tv) >>= (fun as => pure (as.1, l.set as.2 tv))
    = ProgramDenotation.get (l.chainGetter g) tv
  rw [ProgramDenotation.get_apply', ProgramDenotation.get_apply', SubProbability.pure_bind]
  simp only [l.get_set]
  rfl

omit [ProgramSpec] in
/-- Writing through a zoomed lens is writing through the composed setter. -/
theorem ProgramDenotation.zoom_set {s t a : Type} (l : Lens s t) (x : Setter a s) (v : a) :
    ProgramDenotation.zoom l (ProgramDenotation.set x v)
      = ProgramDenotation.set (l.chainSetter x) v := by
  funext tv
  change ProgramDenotation.set x v (l.get tv) >>= (fun as => pure (as.1, l.set as.2 tv))
    = ProgramDenotation.set (l.chainSetter x) v tv
  rw [ProgramDenotation.set_apply', ProgramDenotation.set_apply', SubProbability.pure_bind]
  rfl

omit [ProgramSpec] in
/-- A state-blind draw is unaffected by zooming. -/
theorem ProgramDenotation.zoom_lift {s t a : Type} (l : Lens s t) (μ : SubProbability a) :
    ProgramDenotation.zoom l (μ.toProgramDenotation : ProgramDenotation s a)
      = (μ.toProgramDenotation : ProgramDenotation t a) := by
  funext tv
  change (μ >>= fun v => pure (v, l.get tv)) >>= (fun as => pure (as.1, l.set as.2 tv))
    = μ >>= fun v => pure (v, tv)
  rw [SubProbability.bind_assoc]
  congr 1; funext v
  rw [SubProbability.pure_bind]
  simp only [l.get_set]

omit [ProgramSpec] in
/-- Zooming the everywhere-diverging program diverges. -/
theorem ProgramDenotation.zoom_bot {s t a : Type} (l : Lens s t) :
    ProgramDenotation.zoom l (⊥ : ProgramDenotation s a) = ⊥ := by
  funext tv
  apply Subtype.ext
  exact MeasureTheory.Measure.bind_zero_left _

omit [ProgramSpec] in
/-- `zoom` is ω-continuous in its program argument — what the loop case needs. -/
theorem ProgramDenotation.zoom_ωScottContinuous {s t a : Type} (l : Lens s t) :
    OmegaCompletePartialOrder.ωScottContinuous
      (fun (m : ProgramDenotation s a) => ProgramDenotation.zoom l m) := by
  refine OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup ⟨?mono, ?sup⟩
  case mono =>
    intro m₁ m₂ h τ
    exact SubProbability.bind_mono (fun m : ProgramDenotation s a => m (l.get τ))
      (fun _ (p : a × s) => (pure (p.1, l.set p.2 τ) : SubProbability (a × t)))
      (fun _ _ hh => Pi.le_def.mp hh (l.get τ)) (fun _ _ _ => le_rfl) h
  case sup =>
    intro ch
    funext τ
    refine (SubProbability.bind_ωScottContinuous (fun m : ProgramDenotation s a => m (l.get τ))
      (fun _ (p : a × s) => (pure (p.1, l.set p.2 τ) : SubProbability (a × t))) ?_ ?_).map_ωSup ch
    · exact OmegaCompletePartialOrder.ωScottContinuous.const
    · exact OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup
        ⟨fun _ _ hh => Pi.le_def.mp hh (l.get τ), fun _ => rfl⟩

omit [ProgramSpec] in
/-- **`zoom` commutes with `while_loop`** (Kleene/ωSup argument): running the whole loop in the
sublens and writing back once is the same as writing back after every iteration. -/
theorem ProgramDenotation.zoom_while {s t : Type} (l : Lens s t)
    (cond : ProgramDenotation s Bool) (body : ProgramDenotation s Unit) :
    ProgramDenotation.zoom l (while_loop cond body)
      = while_loop (ProgramDenotation.zoom l cond) (ProgramDenotation.zoom l body) := by
  let F := while_iteration cond body
  let G := while_iteration (ProgramDenotation.zoom l cond) (ProgramDenotation.zoom l body)
  have key : ∀ n : ℕ,
      ProgramDenotation.zoom l ((F^[n] (⊥ : Unit → ProgramDenotation s Unit)) ())
        = (G^[n] (⊥ : Unit → ProgramDenotation t Unit)) () := by
    intro n
    induction n with
    | zero => exact ProgramDenotation.zoom_bot l
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change ProgramDenotation.zoom l (cond >>= fun b =>
          if b = true then body >>= fun _ => (F^[n] ⊥) ()
          else (pure () : ProgramDenotation s Unit))
        = (ProgramDenotation.zoom l cond) >>= fun b =>
          if b = true then (ProgramDenotation.zoom l body) >>= fun _ => (G^[n] ⊥) ()
          else (pure () : ProgramDenotation t Unit)
      rw [ProgramDenotation.zoom_bind]
      congr 1; funext b
      by_cases h : b = true
      · simp only [h, if_true]
        rw [ProgramDenotation.zoom_bind]
        congr 1; funext _
        exact ih
      · simp only [h, Bool.false_eq_true, if_false]
        exact ProgramDenotation.zoom_pure l ()
  change ProgramDenotation.zoom l (F.lfp ()) = G.lfp ()
  let chainF : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation s Unit) :=
    ⟨fun n => F^[n] ⊥, Monotone.monotone_iterate_of_le_map F.monotone (OrderBot.bot_le _)⟩
  let chainG : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation t Unit) :=
    ⟨fun n => G^[n] ⊥, Monotone.monotone_iterate_of_le_map G.monotone (OrderBot.bot_le _)⟩
  have hF_at : F.lfp () = OmegaCompletePartialOrder.ωSup
      (chainF.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := rfl
  have hG_at : G.lfp () = OmegaCompletePartialOrder.ωSup
      (chainG.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := rfl
  rw [hF_at, hG_at, (ProgramDenotation.zoom_ωScottContinuous l).map_ωSup]
  congr 1
  ext n
  exact key n

/-! ## The transport theorem

`applyLens l s` runs `s` in the sublens `l` — which is exactly `zoom l`.  The only assumption is
that `l` leaves the global state alone, which is what a `call` needs (the callee runs on the
global state, and must see the same one before and after re-targeting).

This holds for an *arbitrary* statement `s`, which is why the flattener may wrap whole
subprograms in `applyLens` without looking at them. -/

theorem programDenotation_applyLens {L₁ L₂ : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂))
    (hglob : l.chain ProcedureState.globalL = ProcedureState.globalL) :
    ∀ s : Stmt L₁,
      programDenotation (s.applyLens l) = ProgramDenotation.zoom l (programDenotation s)
  | .skip => by
      simp only [StmtWithHoles.applyLens, programDenotation, ProgramDenotation.skip]
      exact (ProgramDenotation.zoom_pure l ()).symm
  | .sample x e => by
      simp only [StmtWithHoles.applyLens, programDenotation]
      rw [ProgramDenotation.zoom_bind, ProgramDenotation.zoom_get]
      congr 1; funext μ
      rw [ProgramDenotation.zoom_bind, ProgramDenotation.zoom_lift]
      congr 1; funext v
      rw [ProgramDenotation.zoom_set]
  | .call' x ls b r p => by
      simp only [StmtWithHoles.applyLens, programDenotation]
      rw [ProgramDenotation.zoom_bind, ProgramDenotation.zoom_get]
      congr 1; funext args
      rw [ProgramDenotation.zoom_bind, ← ProgramDenotation.zoom_chain, hglob]
      congr 1; funext ret
      rw [ProgramDenotation.zoom_set]
  | .seq s₁ s₂ => by
      simp only [StmtWithHoles.applyLens, programDenotation,
        programDenotation_applyLens l hglob s₁, programDenotation_applyLens l hglob s₂]
      rw [ProgramDenotation.zoom_bind]
  | .ifThenElse c s₁ s₂ => by
      simp only [StmtWithHoles.applyLens, programDenotation,
        programDenotation_applyLens l hglob s₁, programDenotation_applyLens l hglob s₂]
      rw [ProgramDenotation.zoom_bind, ProgramDenotation.zoom_get]
      congr 1; funext bv
      cases bv <;> simp
  | .while c s => by
      simp only [StmtWithHoles.applyLens, programDenotation,
        programDenotation_applyLens l hglob s]
      rw [ProgramDenotation.zoom_while, ProgramDenotation.zoom_get]
  termination_by s => s.depth
  decreasing_by all_goals simp only [StmtWithHoles.depth]; omega

omit [ProgramSpec] in
/-- Zooming is always a correct replacement: projecting the result of the zoomed program back
gives the original program's result. -/
theorem ProgramDenotation.equivInLens_zoom {s t α : Type} (l : Lens s t)
    (p : ProgramDenotation s α) : p.EquivInLens (ProgramDenotation.zoom l p) l := by
  rintro sa sb rfl
  change ((ProgramDenotation.zoom l p sb) >>= fun q => pure (q.1, l.get q.2)) = p (l.get sb)
  change ((p (l.get sb) >>= fun as => pure (as.1, l.set as.2 sb))
            >>= fun q => pure (q.1, l.get q.2)) = p (l.get sb)
  have key : (fun as : α × s => (pure (as.1, l.set as.2 sb) : SubProbability (α × t))
                 >>= fun q => pure (q.1, l.get q.2))
           = (pure : α × s → SubProbability (α × s)) := by
    funext as
    rw [SubProbability.pure_bind]
    simp only [l.set_get]
  rw [SubProbability.bind_assoc, key]
  exact SubProbability.bind_pure _

/-- **`applyLens` is always the right replacement**: whatever the statement, re-targeting it
along a globals-preserving lens is denotationally equivalent in that lens. -/
theorem StmtWithHoles.equivInLens_applyLens {hCtx : HoleSigs} {L₁ L₂ : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂))
    (hglob : l.chain ProcedureState.globalL = ProcedureState.globalL)
    (s : StmtWithHoles hCtx L₁) : s.EquivInLens (s.applyLens l) l := by
  intro inst
  rw [StmtWithHoles.applyLens_instantiate, programDenotation_applyLens l hglob]
  exact ProgramDenotation.equivInLens_zoom l _

/-! ## `EquivInLens` is a congruence

What the flattener needs along the path down to the call it is rewriting. -/

omit [ProgramSpec] in
/-- `mapState` spelled out as a `bind`, for rewriting. -/
theorem SubProbability.mapState_eq {α s t : Type} (f : t → s)
    (μ : SubProbability (α × t)) : μ.mapState f = μ >>= fun q => pure (q.1, f q.2) := rfl

omit [ProgramSpec] in
/-- `pure` is equivalent to itself. -/
theorem ProgramDenotation.EquivInLens.pure {s t α : Type} {l : Lens s t} (a : α) :
    (Pure.pure a : ProgramDenotation s α).EquivInLens (Pure.pure a) l := by
  rintro sa sb rfl
  change ((Pure.pure (a, sb) : SubProbability (α × t))
      >>= fun q => (Pure.pure (q.1, l.get q.2) : SubProbability (α × s))) = _
  rw [SubProbability.pure_bind]
  rfl

omit [ProgramSpec] in
/-- Diverging is equivalent to diverging. -/
theorem ProgramDenotation.EquivInLens.bot {s t α : Type} {l : Lens s t} :
    (⊥ : ProgramDenotation s α).EquivInLens ⊥ l := by
  rintro sa sb rfl
  apply Subtype.ext
  exact MeasureTheory.Measure.bind_zero_left _

omit [ProgramSpec] in
/-- Reading through the composed getter is equivalent to reading through the original one. -/
theorem ProgramDenotation.EquivInLens.get {s t α : Type} (l : Lens s t) (g : Getter α s) :
    (ProgramDenotation.get g).EquivInLens (ProgramDenotation.get (l.chainGetter g)) l := by
  rintro sa sb rfl
  change (ProgramDenotation.get (l.chainGetter g) sb
      >>= fun q => (Pure.pure (q.1, l.get q.2) : SubProbability (α × s)))
    = ProgramDenotation.get g (l.get sb)
  rw [ProgramDenotation.get_apply', ProgramDenotation.get_apply', SubProbability.pure_bind]
  rfl

omit [ProgramSpec] in
/-- Writing through the composed setter is equivalent to writing through the original one. -/
theorem ProgramDenotation.EquivInLens.set {s t α : Type} (l : Lens s t) (x : Setter α s) (v : α) :
    (ProgramDenotation.set x v).EquivInLens (ProgramDenotation.set (l.chainSetter x) v) l := by
  rintro sa sb rfl
  change (ProgramDenotation.set (l.chainSetter x) v sb
      >>= fun q => (Pure.pure (q.1, l.get q.2) : SubProbability (Unit × s)))
    = ProgramDenotation.set x v (l.get sb)
  rw [ProgramDenotation.set_apply', ProgramDenotation.set_apply', SubProbability.pure_bind]
  simp only [Lens.chainSetter, l.set_get]

omit [ProgramSpec] in
/-- A state-blind draw is equivalent to itself. -/
theorem ProgramDenotation.EquivInLens.lift {s t α : Type} (l : Lens s t) (μ : SubProbability α) :
    (μ.toProgramDenotation : ProgramDenotation s α).EquivInLens
      (μ.toProgramDenotation : ProgramDenotation t α) l := by
  rintro sa sb rfl
  change ((μ >>= fun v => (Pure.pure (v, sb) : SubProbability (α × t)))
      >>= fun q => (Pure.pure (q.1, l.get q.2) : SubProbability (α × s)))
    = μ >>= fun v => Pure.pure (v, l.get sb)
  rw [SubProbability.bind_assoc]
  congr 1; funext v
  rw [SubProbability.pure_bind]

omit [ProgramSpec] in
/-- **Bind congruence** — the `seq` case, and the heart of the path congruences.  Note the
continuation hypothesis is over *wide* states, which is exactly what `EquivInLens` provides. -/
theorem ProgramDenotation.EquivInLens.bind {s t α β : Type} {l : Lens s t}
    {p : ProgramDenotation s α} {q : ProgramDenotation t α}
    {p' : α → ProgramDenotation s β} {q' : α → ProgramDenotation t β}
    (h : p.EquivInLens q l) (h' : ∀ a, (p' a).EquivInLens (q' a) l) :
    (p >>= p').EquivInLens (q >>= q') l := by
  rintro sa sb rfl
  have hfun : (fun r : α × t =>
        (q' r.1 r.2 >>= fun z => (Pure.pure (z.1, l.get z.2) : SubProbability (β × s))))
      = (fun r : α × t => p' r.1 (l.get r.2)) := funext fun r => h' r.1 _ r.2 rfl
  change ((q sb >>= fun r => q' r.1 r.2)
      >>= fun z => (Pure.pure (z.1, l.get z.2) : SubProbability (β × s)))
    = p (l.get sb) >>= fun r => p' r.1 r.2
  rw [SubProbability.bind_assoc, hfun, ← h _ sb rfl]
  change _ = ((q sb >>= fun z => (Pure.pure (z.1, l.get z.2) : SubProbability (α × s)))
      >>= fun r => p' r.1 r.2)
  rw [SubProbability.bind_assoc]
  congr 1; funext r
  rw [SubProbability.pure_bind]

omit [ProgramSpec] in
/-- Projecting twice is projecting along the composite. -/
theorem SubProbability.mapState_mapState {α s t u : Type} (f : u → t) (g : t → s)
    (μ : SubProbability (α × u)) : (μ.mapState f).mapState g = μ.mapState (fun x => g (f x)) := by
  change ((μ >>= fun q => Pure.pure (q.1, f q.2)) >>= fun q => Pure.pure (q.1, g q.2))
    = μ >>= fun q => Pure.pure (q.1, g (f q.2))
  rw [SubProbability.bind_assoc]
  congr 1; funext q
  rw [SubProbability.pure_bind]

omit [ProgramSpec] in
/-- Equivalences compose: through `l`, then through `m`, is through `m.chain l`. -/
theorem ProgramDenotation.EquivInLens.trans {s t u α : Type} {l : Lens s t} {m : Lens t u}
    {p : ProgramDenotation s α} {q : ProgramDenotation t α} {r : ProgramDenotation u α}
    (h : p.EquivInLens q l) (h' : q.EquivInLens r m) : p.EquivInLens r (m.chain l) := by
  rintro sa su rfl
  change ((r su).mapState (fun x => l.get (m.get x))) = p (l.get (m.get su))
  rw [← SubProbability.mapState_mapState, h' _ su rfl, h _ (m.get su) rfl]

omit [ProgramSpec] in
/-- `mapState` is ω-continuous — what the loop congruence needs. -/
theorem SubProbability.mapState_ωScottContinuous {α s t : Type} (f : t → s) :
    OmegaCompletePartialOrder.ωScottContinuous
      (fun μ : SubProbability (α × t) => μ.mapState f) := by
  refine OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup ⟨?mono, ?sup⟩
  case mono =>
    intro μ₁ μ₂ h
    exact SubProbability.bind_mono (fun μ : SubProbability (α × t) => μ)
      (fun _ q => (Pure.pure (q.1, f q.2) : SubProbability (α × s)))
      (fun _ _ hh => hh) (fun _ _ _ => le_rfl) h
  case sup =>
    intro ch
    exact (SubProbability.bind_ωScottContinuous (fun μ : SubProbability (α × t) => μ)
      (fun _ q => (Pure.pure (q.1, f q.2) : SubProbability (α × s)))
      OmegaCompletePartialOrder.ωScottContinuous.const
      OmegaCompletePartialOrder.ωScottContinuous.id).map_ωSup ch

omit [ProgramSpec] in
/-- Equivalence passes to ω-suprema of chains — the limit step of the loop congruence. -/
theorem ProgramDenotation.EquivInLens.ωSup {s t α : Type} {l : Lens s t}
    (chP : OmegaCompletePartialOrder.Chain (ProgramDenotation s α))
    (chQ : OmegaCompletePartialOrder.Chain (ProgramDenotation t α))
    (h : ∀ n, (chP n).EquivInLens (chQ n) l) :
    (OmegaCompletePartialOrder.ωSup chP).EquivInLens (OmegaCompletePartialOrder.ωSup chQ) l := by
  rintro sa sb rfl
  have hQ : (OmegaCompletePartialOrder.ωSup chQ) sb = OmegaCompletePartialOrder.ωSup
      (chQ.map ⟨fun m => m sb, fun _ _ hh => Pi.le_def.mp hh sb⟩) := rfl
  have hP : (OmegaCompletePartialOrder.ωSup chP) (l.get sb) = OmegaCompletePartialOrder.ωSup
      (chP.map ⟨fun m => m (l.get sb), fun _ _ hh => Pi.le_def.mp hh (l.get sb)⟩) := rfl
  rw [hQ, hP, (SubProbability.mapState_ωScottContinuous (α := α) l.get).map_ωSup]
  congr 1
  ext n
  exact h n _ sb rfl

omit [ProgramSpec] in
/-- **Loop congruence** (Kleene/ωSup argument again): equivalent conditions and equivalent bodies
give equivalent loops. -/
theorem ProgramDenotation.EquivInLens.while_loop {s t : Type} {l : Lens s t}
    {cond : ProgramDenotation s Bool} {cond' : ProgramDenotation t Bool}
    {body : ProgramDenotation s Unit} {body' : ProgramDenotation t Unit}
    (hc : cond.EquivInLens cond' l) (hb : body.EquivInLens body' l) :
    (while_loop cond body).EquivInLens (while_loop cond' body') l := by
  let F := while_iteration cond body
  let G := while_iteration cond' body'
  have key : ∀ n : ℕ, ((F^[n] (⊥ : Unit → ProgramDenotation s Unit)) ()).EquivInLens
      ((G^[n] (⊥ : Unit → ProgramDenotation t Unit)) ()) l := by
    intro n
    induction n with
    | zero => exact ProgramDenotation.EquivInLens.bot
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change (cond >>= fun b => if b = true then body >>= fun _ => (F^[n] ⊥) ()
                else (Pure.pure () : ProgramDenotation s Unit)).EquivInLens
             (cond' >>= fun b => if b = true then body' >>= fun _ => (G^[n] ⊥) ()
                else (Pure.pure () : ProgramDenotation t Unit)) l
      refine ProgramDenotation.EquivInLens.bind hc fun b => ?_
      by_cases h : b = true
      · simp only [h, if_true]
        exact ProgramDenotation.EquivInLens.bind hb fun _ => ih
      · simp only [h, Bool.false_eq_true, if_false]
        exact ProgramDenotation.EquivInLens.pure ()
  let chainF : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation s Unit) :=
    ⟨fun n => F^[n] ⊥, Monotone.monotone_iterate_of_le_map F.monotone (OrderBot.bot_le _)⟩
  let chainG : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation t Unit) :=
    ⟨fun n => G^[n] ⊥, Monotone.monotone_iterate_of_le_map G.monotone (OrderBot.bot_le _)⟩
  have hF_at : F.lfp () = OmegaCompletePartialOrder.ωSup
      (chainF.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := rfl
  have hG_at : G.lfp () = OmegaCompletePartialOrder.ωSup
      (chainG.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := rfl
  change (F.lfp ()).EquivInLens (G.lfp ()) l
  rw [hF_at, hG_at]
  exact ProgramDenotation.EquivInLens.ωSup _ _ key

omit [ProgramSpec] in
/-- Every program is equivalent to itself, in the identity lens. -/
theorem ProgramDenotation.EquivInLens.refl {s α : Type} (p : ProgramDenotation s α) :
    p.EquivInLens p Lens.id := by
  rintro sa sb rfl
  exact SubProbability.bind_pure _

/-! ### The same, at statement level -/

/-- Sequencing. -/
theorem StmtWithHoles.EquivInLens.seq {hCtx : HoleSigs} {L₁ L₂ : Type}
    {l : Lens (ProcedureState L₁) (ProcedureState L₂)}
    {a b : StmtWithHoles hCtx L₁} {a' b' : StmtWithHoles hCtx L₂}
    (ha : a.EquivInLens a' l) (hb : b.EquivInLens b' l) :
    (a.seq b).EquivInLens (a'.seq b') l := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation]
  exact ProgramDenotation.EquivInLens.bind (ha inst) fun _ => hb inst

/-- Branching; the condition is re-targeted by composing it with the lens. -/
theorem StmtWithHoles.EquivInLens.ifThenElse {hCtx : HoleSigs} {L₁ L₂ : Type}
    {l : Lens (ProcedureState L₁) (ProcedureState L₂)}
    (c : Getter Bool (ProcedureState L₁))
    {a b : StmtWithHoles hCtx L₁} {a' b' : StmtWithHoles hCtx L₂}
    (ha : a.EquivInLens a' l) (hb : b.EquivInLens b' l) :
    (StmtWithHoles.ifThenElse c a b).EquivInLens
      (StmtWithHoles.ifThenElse (l.chainGetter c) a' b') l := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation]
  refine ProgramDenotation.EquivInLens.bind (ProgramDenotation.EquivInLens.get l c) fun bv => ?_
  cases bv
  · simpa using hb inst
  · simpa using ha inst

/-- Looping; the condition is re-targeted by composing it with the lens. -/
theorem StmtWithHoles.EquivInLens.while {hCtx : HoleSigs} {L₁ L₂ : Type}
    {l : Lens (ProcedureState L₁) (ProcedureState L₂)}
    (c : Getter Bool (ProcedureState L₁))
    {b : StmtWithHoles hCtx L₁} {b' : StmtWithHoles hCtx L₂}
    (hb : b.EquivInLens b' l) :
    (StmtWithHoles.while c b).EquivInLens (StmtWithHoles.while (l.chainGetter c) b') l := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation]
  exact ProgramDenotation.EquivInLens.while_loop (ProgramDenotation.EquivInLens.get l c) (hb inst)

/-- Statement equivalences compose — how the flattener's three passes are stitched together. -/
theorem StmtWithHoles.EquivInLens.trans {hCtx : HoleSigs} {L₁ L₂ L₃ : Type}
    {l : Lens (ProcedureState L₁) (ProcedureState L₂)}
    {m : Lens (ProcedureState L₂) (ProcedureState L₃)}
    {a : StmtWithHoles hCtx L₁} {b : StmtWithHoles hCtx L₂} {c : StmtWithHoles hCtx L₃}
    (h : a.EquivInLens b l) (h' : b.EquivInLens c m) : a.EquivInLens c (m.chain l) :=
  fun inst => (h inst).trans (h' inst)

/-- Reflexivity of the same-scope relation. -/
theorem StmtWithHoles.Equiv.refl {hCtx : HoleSigs} {L : Type} (a : StmtWithHoles hCtx L) :
    a.Equiv a := fun _ => ProgramDenotation.EquivInLens.refl _

/-! ## Flattening one call

The one step with real content.  Everything else above is congruence and transport. -/

omit [ProgramSpec] in
/-- `>>=` of denotations, applied at a state. -/
theorem ProgramDenotation.bind_apply {s α β : Type} (m : ProgramDenotation s α)
    (k : α → ProgramDenotation s β) (st : s) :
    (m >>= k) st = m st >>= fun p => k p.1 p.2 := rfl

/-- A procedure, run at a global state: initialise its scope, run its body, read its return
value off the final scope. -/
theorem procedureDenotation_apply {sig : ProcedureSignature} (p : Procedure sig)
    (argv : sig.ParamType) (st : State) :
    procedureDenotation p argv st
      = programDenotation p.body ⟨st, sig.localVariableInit p.locals argv⟩
          >>= fun z => Pure.pure (p.return_val.get z.2, z.2.global) := by
  simp only [procedureDenotation]

/-- A `call` statement, run at a state: initialise the callee's scope with the arguments, run its
body, then store its return value. -/
theorem programDenotation_call'_apply {L : Type} {sig : ProcedureSignature}
    {ls : List (Σ t : Type, Inhabited t)}
    (x : Setter sig.ret (ProcedureState L)) (b : Stmt (sig.ProcedureScope ls))
    (r : Getter sig.ret (ProcedureState (sig.ProcedureScope ls)))
    (args : Getter sig.ParamType (ProcedureState L)) (s : ProcedureState L) :
    programDenotation (StmtWithHoles.call' (h := .empty) x ls b r args) s
      = programDenotation b ⟨s.global, sig.localVariableInit ls (args.get s)⟩
          >>= fun z => Pure.pure ((), x.set (r.get z.2)
                (ProcedureState.globalL.set z.2.global s)) := by
  simp only [programDenotation]
  rw [ProgramDenotation.bind_apply, ProgramDenotation.get_apply', SubProbability.pure_bind,
    ProgramDenotation.bind_apply]
  change (procedureDenotation ⟨ls, b, r⟩ (args.get s) s.global
      >>= fun w => Pure.pure (w.1, ProcedureState.globalL.set w.2 s))
      >>= (fun q => ProgramDenotation.set x q.1 q.2) = _
  rw [procedureDenotation_apply, SubProbability.bind_assoc, SubProbability.bind_assoc]
  congr 1; funext z
  rw [SubProbability.pure_bind, SubProbability.pure_bind, ProgramDenotation.set_apply']

/-- The four-part expansion of a call, run at a state: after the prelude `f`, the callee's body
runs in `emb`, and its return value is stored through the caller's setter. -/
theorem flattenedCall_apply {L₁ L₂ : Type} {sig : ProcedureSignature}
    {ls : List (Σ t : Type, Inhabited t)}
    (trafo : Lens (ProcedureState L₁) (ProcedureState L₂))
    (emb : Lens (ProcedureState (sig.ProcedureScope ls)) (ProcedureState L₂))
    (heg : emb.chain ProcedureState.globalL = ProcedureState.globalL)
    (x : Setter sig.ret (ProcedureState L₁)) (b : Stmt (sig.ProcedureScope ls))
    (r : Getter sig.ret (ProcedureState (sig.ProcedureScope ls)))
    (f : ProcedureState L₂ → ProcedureState L₂) (τ : ProcedureState L₂) :
    ((fun σ => Pure.pure ((), f σ)) >>= fun _ =>
        programDenotation (b.applyLens emb) >>= fun _ =>
          ProgramDenotation.get (emb.chainGetter r) >>= fun v =>
            ProgramDenotation.set (trafo.chainSetter x) v) τ
      = programDenotation b (emb.get (f τ)) >>= fun w =>
          Pure.pure ((), trafo.set (x.set (r.get w.2) (trafo.get (emb.set w.2 (f τ))))
            (emb.set w.2 (f τ))) := by
  rw [ProgramDenotation.bind_apply, SubProbability.pure_bind, ProgramDenotation.bind_apply,
    programDenotation_applyLens emb heg b]
  change (programDenotation b (emb.get (f τ)) >>= fun w => Pure.pure (w.1, emb.set w.2 (f τ)))
      >>= _ = _
  rw [SubProbability.bind_assoc]
  congr 1; funext w
  rw [SubProbability.pure_bind, ProgramDenotation.bind_apply, ProgramDenotation.get_apply',
    SubProbability.pure_bind, ProgramDenotation.set_apply']
  simp only [Lens.chainGetter, Lens.chainSetter, emb.set_get]

/-- **Flattening a call is sound.**  A `call` is denotationally equivalent, along `trafo`, to

* a *prelude* `f` that puts the arguments and the callee's default-initialised locals into the
  callee's slice of the widened state (`hpre_get`) without disturbing anything visible through
  `trafo` (`hpre_vis`);
* the callee's body, re-targeted with `applyLens emb`;
* a store of the callee's return value through the caller's setter.

The two lenses must preserve the global state (`htg`, `heg`), and writing the callee's slice must
be invisible through `trafo` except for the global part (`hdisj`) — that is the freshness of the
newly added variables. -/
theorem equivInLens_flattenCall {L₁ L₂ : Type} {sig : ProcedureSignature}
    {ls : List (Σ t : Type, Inhabited t)}
    (trafo : Lens (ProcedureState L₁) (ProcedureState L₂))
    (emb : Lens (ProcedureState (sig.ProcedureScope ls)) (ProcedureState L₂))
    (htg : trafo.chain ProcedureState.globalL = ProcedureState.globalL)
    (heg : emb.chain ProcedureState.globalL = ProcedureState.globalL)
    (hdisj : ∀ v τ, trafo.get (emb.set v τ)
      = ProcedureState.globalL.set v.global (trafo.get τ))
    (x : Setter sig.ret (ProcedureState L₁)) (args : Getter sig.ParamType (ProcedureState L₁))
    (b : Stmt (sig.ProcedureScope ls))
    (r : Getter sig.ret (ProcedureState (sig.ProcedureScope ls)))
    (f : ProcedureState L₂ → ProcedureState L₂)
    (hpre_get : ∀ τ, emb.get (f τ)
      = ⟨τ.global, sig.localVariableInit ls (args.get (trafo.get τ))⟩)
    (hpre_vis : ∀ τ, trafo.get (f τ) = trafo.get τ) :
    (programDenotation (StmtWithHoles.call' (h := .empty) x ls b r args)).EquivInLens
      ((fun σ => Pure.pure ((), f σ)) >>= fun _ =>
        programDenotation (b.applyLens emb) >>= fun _ =>
          ProgramDenotation.get (emb.chainGetter r) >>= fun v =>
            ProgramDenotation.set (trafo.chainSetter x) v) trafo := by
  rintro sa τ rfl
  have hglob : (trafo.get τ).global = τ.global :=
    congrArg (fun L : Lens State (ProcedureState L₂) => L.get τ) htg
  rw [programDenotation_call'_apply, SubProbability.mapState_eq,
    flattenedCall_apply trafo emb heg x b r f τ, SubProbability.bind_assoc, hpre_get, hglob]
  congr 1; funext w
  rw [SubProbability.pure_bind, trafo.set_get, hdisj, hpre_vis]

/-- An assignment, run at a state: a deterministic write.  This is what lets the meta code
instantiate the prelude `f` of `equivInLens_flattenCall` with the statements it emits. -/
theorem programDenotation_assign_apply {L a : Type} (y : Setter a (ProcedureState L))
    (e : Getter a (ProcedureState L)) (τ : ProcedureState L) :
    programDenotation (StmtWithHoles.assign (h := .empty) y e) τ
      = Pure.pure ((), y.set (e.get τ) τ) := by
  simp only [StmtWithHoles.assign, programDenotation]
  rw [ProgramDenotation.bind_apply, ProgramDenotation.get_apply', SubProbability.pure_bind,
    ProgramDenotation.bind_apply]
  change ((Pure.pure (e.get τ) : SubProbability a) >>= fun v => Pure.pure (v, τ))
      >>= (fun p => ProgramDenotation.set y p.1 p.2) = _
  rw [SubProbability.pure_bind, SubProbability.pure_bind, ProgramDenotation.set_apply']

/-! ### What `flattenSeq` rewrites with -/

/-- Sequencing is associative, denotationally. -/
theorem StmtWithHoles.Equiv.seq_assoc {hCtx : HoleSigs} {L : Type}
    (a b c : StmtWithHoles hCtx L) : ((a.seq b).seq c).Equiv (a.seq (b.seq c)) := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation]
  rw [ProgramDenotation.bind_assoc]
  exact ProgramDenotation.EquivInLens.refl _

/-- A leading `skip` can be dropped. -/
theorem StmtWithHoles.Equiv.skip_seq {hCtx : HoleSigs} {L : Type} (a : StmtWithHoles hCtx L) :
    ((StmtWithHoles.skip).seq a).Equiv a := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation, ProgramDenotation.skip]
  rw [ProgramDenotation.pure_bind]
  exact ProgramDenotation.EquivInLens.refl _

/-- A trailing `skip` can be dropped. -/
theorem StmtWithHoles.Equiv.seq_skip {hCtx : HoleSigs} {L : Type} (a : StmtWithHoles hCtx L) :
    (a.seq (StmtWithHoles.skip)).Equiv a := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation, ProgramDenotation.skip]
  rw [ProgramDenotation.bind_pure]
  exact ProgramDenotation.EquivInLens.refl _

/-! ### Placing a hole-free statement into a hole context

A flattened callee body is hole-free, but the statement it is spliced into need not be. -/

/-- Re-type a hole-free statement in any hole context.  (`hole` cannot occur: `HoleIndex .empty`
is uninhabited.) -/
def StmtWithHoles.weaken {h : HoleSigs} {l : Type} : Stmt l → StmtWithHoles h l
  | .skip             => .skip
  | .sample x e       => .sample x e
  | .call' x ls b r p => .call' x ls b r p
  | .seq s₁ s₂        => .seq (weaken s₁) (weaken s₂)
  | .ifThenElse c t e => .ifThenElse c (weaken t) (weaken e)
  | .while c b        => .while c (weaken b)
  termination_by s => s.depth
  decreasing_by all_goals simp only [StmtWithHoles.depth]; omega

/-- Weakening is undone by instantiation: a hole-free statement has nothing to fill in. -/
theorem StmtWithHoles.weaken_instantiate {h : HoleSigs} {l : Type} (inst : h.Instantiation) :
    ∀ s : Stmt l, (StmtWithHoles.weaken (h := h) s).instantiate inst = s
  | .skip             => by simp only [StmtWithHoles.weaken, StmtWithHoles.instantiate]
  | .sample _ _       => by simp only [StmtWithHoles.weaken, StmtWithHoles.instantiate]
  | .call' _ _ _ _ _  => by simp only [StmtWithHoles.weaken, StmtWithHoles.instantiate]
  | .seq s₁ s₂        => by
      simp only [StmtWithHoles.weaken, StmtWithHoles.instantiate,
        weaken_instantiate inst s₁, weaken_instantiate inst s₂]
  | .ifThenElse _ t e => by
      simp only [StmtWithHoles.weaken, StmtWithHoles.instantiate,
        weaken_instantiate inst t, weaken_instantiate inst e]
  | .while _ b        => by
      simp only [StmtWithHoles.weaken, StmtWithHoles.instantiate, weaken_instantiate inst b]
  termination_by s => s.depth
  decreasing_by all_goals simp only [StmtWithHoles.depth]; omega

/-- Sequencing is `bind`. -/
theorem programDenotation_seq {L : Type} (a b : Stmt L) :
    programDenotation (a.seq b) = programDenotation a >>= fun _ => programDenotation b := by
  simp only [programDenotation]

/-- An assignment is a read followed by a write. -/
theorem programDenotation_assign {L a : Type} (y : Setter a (ProcedureState L))
    (e : Getter a (ProcedureState L)) :
    programDenotation (StmtWithHoles.assign (h := .empty) y e)
      = ProgramDenotation.get e >>= fun v => ProgramDenotation.set y v := by
  funext τ
  rw [programDenotation_assign_apply, ProgramDenotation.bind_apply,
    ProgramDenotation.get_apply', SubProbability.pure_bind, ProgramDenotation.set_apply']

/-- **The statement-level call-flattening lemma** — what the meta code instantiates.  The prelude
is an arbitrary deterministic statement (`hpre`); in practice it is the assignment that fills the
callee's slice, whose denotation is given by `programDenotation_assign_apply`. -/
theorem StmtWithHoles.equivInLens_flattenCall {hCtx : HoleSigs} {L₁ L₂ : Type}
    {sig : ProcedureSignature} {ls : List (Σ t : Type, Inhabited t)}
    (trafo : Lens (ProcedureState L₁) (ProcedureState L₂))
    (emb : Lens (ProcedureState (sig.ProcedureScope ls)) (ProcedureState L₂))
    (htg : trafo.chain ProcedureState.globalL = ProcedureState.globalL)
    (heg : emb.chain ProcedureState.globalL = ProcedureState.globalL)
    (hdisj : ∀ v τ, trafo.get (emb.set v τ)
      = ProcedureState.globalL.set v.global (trafo.get τ))
    (x : Setter sig.ret (ProcedureState L₁)) (args : Getter sig.ParamType (ProcedureState L₁))
    (b : Stmt (sig.ProcedureScope ls))
    (r : Getter sig.ret (ProcedureState (sig.ProcedureScope ls)))
    (pre : Stmt L₂) (f : ProcedureState L₂ → ProcedureState L₂)
    (hpre : ∀ τ, programDenotation pre τ = Pure.pure ((), f τ))
    (hpre_get : ∀ τ, emb.get (f τ)
      = ⟨τ.global, sig.localVariableInit ls (args.get (trafo.get τ))⟩)
    (hpre_vis : ∀ τ, trafo.get (f τ) = trafo.get τ) :
    (StmtWithHoles.call' (h := hCtx) x ls b r args).EquivInLens
      ((StmtWithHoles.weaken pre).seq ((StmtWithHoles.weaken (b.applyLens emb)).seq
        (StmtWithHoles.assign (trafo.chainSetter x) (emb.chainGetter r)))) trafo := by
  intro inst
  have hpre' : programDenotation pre = fun σ => Pure.pure ((), f σ) := funext hpre
  simp only [StmtWithHoles.instantiate, StmtWithHoles.weaken_instantiate, StmtWithHoles.assign]
  rw [programDenotation_seq, programDenotation_seq, ← StmtWithHoles.assign,
    programDenotation_assign, hpre']
  exact _root_.GaudisCrypt.equivInLens_flattenCall
    trafo emb htg heg hdisj x args b r f hpre_get hpre_vis

/-! ### Deterministic preludes

`equivInLens_flattenCall` takes the prelude as *one* statement with a state map `f`.  The meta
code emits it as a sequence of assignments, one per callee variable, so these two lemmas are how
that sequence is folded into an `f`. -/

/-- `skip` is the identity state map. -/
theorem programDenotation_skip_apply {L : Type} (τ : ProcedureState L) :
    programDenotation (StmtWithHoles.skip (h := .empty)) τ = Pure.pure ((), τ) := by
  simp only [programDenotation, ProgramDenotation.skip]
  rfl

/-- Two deterministic statements in sequence: their state maps compose. -/
theorem programDenotation_seq_apply_det {L : Type} {a b : Stmt L}
    {fa fb : ProcedureState L → ProcedureState L}
    (ha : ∀ τ, programDenotation a τ = Pure.pure ((), fa τ))
    (hb : ∀ τ, programDenotation b τ = Pure.pure ((), fb τ)) :
    ∀ τ, programDenotation (a.seq b) τ = Pure.pure ((), fb (fa τ)) := by
  intro τ
  rw [programDenotation_seq, ProgramDenotation.bind_apply, ha, SubProbability.pure_bind, hb]

/-! ### What `flattenSeq` needs at the identity lens

`Equiv` is `EquivInLens … Lens.id`, so the congruences above already apply; these three only
specialise them, so that the re-associated statement keeps its condition verbatim rather than
picking up a `Lens.id.chainGetter`. -/

/-- Branching, at the identity lens. -/
theorem StmtWithHoles.Equiv.ifThenElse {hCtx : HoleSigs} {L : Type}
    (c : Getter Bool (ProcedureState L)) {a b a' b' : StmtWithHoles hCtx L}
    (ha : a.Equiv a') (hb : b.Equiv b') :
    (StmtWithHoles.ifThenElse c a b).Equiv (StmtWithHoles.ifThenElse c a' b') :=
  StmtWithHoles.EquivInLens.ifThenElse c ha hb

/-- Looping, at the identity lens. -/
theorem StmtWithHoles.Equiv.while {hCtx : HoleSigs} {L : Type}
    (c : Getter Bool (ProcedureState L)) {b b' : StmtWithHoles hCtx L} (hb : b.Equiv b') :
    (StmtWithHoles.while c b).Equiv (StmtWithHoles.while c b') :=
  StmtWithHoles.EquivInLens.while c hb

/-- Transitivity, at the identity lens (`Lens.id.chain Lens.id` is `Lens.id`). -/
theorem StmtWithHoles.Equiv.trans {hCtx : HoleSigs} {L : Type} {a b c : StmtWithHoles hCtx L}
    (h : a.Equiv b) (h' : b.Equiv c) : a.Equiv c :=
  StmtWithHoles.EquivInLens.trans h h'

/-! ### §8 — the procedure level

What the `ProcedureWithHoles` wrapper needs: an `EquivInLens` between the bodies plus three facts
about `trafo` that are `rfl` at concrete variable lists — the fresh block gets defaults at
procedure entry, the return value is read through the lens, and the global state is untouched. -/

/-- **The procedure-level statement**: widening a procedure's locals does not change what it
computes.  This is what turns §6.5's `EquivInLens` into a fact about `procedureDenotation`, and
therefore into something usable where a procedure is *called*. -/
theorem procedureDenotation_congr {sig : ProcedureSignature}
    {ls ls' : List (Σ t : Type, Inhabited t)}
    (trafo : Lens (ProcedureState (sig.ProcedureScope ls))
                  (ProcedureState (sig.ProcedureScope ls')))
    (b : Stmt (sig.ProcedureScope ls)) (b' : Stmt (sig.ProcedureScope ls'))
    (r : Getter sig.ret (ProcedureState (sig.ProcedureScope ls)))
    (r' : Getter sig.ret (ProcedureState (sig.ProcedureScope ls')))
    (hb : b.EquivInLens b' trafo)
    (hinit : ∀ (st : State) (argv : sig.ParamType),
      trafo.get ⟨st, sig.localVariableInit ls' argv⟩
        = (⟨st, sig.localVariableInit ls argv⟩ : ProcedureState (sig.ProcedureScope ls)))
    (hret : ∀ τ, r'.get τ = r.get (trafo.get τ))
    (hglob : ∀ τ, (trafo.get τ).global = τ.global) :
    procedureDenotation (⟨ls', b', r'⟩ : Procedure sig)
      = procedureDenotation (⟨ls, b, r⟩ : Procedure sig) := by
  funext argv st
  rw [procedureDenotation_apply, procedureDenotation_apply]
  have h := hb ⟨⟩ (trafo.get ⟨st, sig.localVariableInit ls' argv⟩)
    ⟨st, sig.localVariableInit ls' argv⟩ rfl
  rw [StmtWithHoles.instantiate_empty, StmtWithHoles.instantiate_empty, hinit] at h
  rw [← h, SubProbability.mapState_eq, SubProbability.bind_assoc]
  congr 1; funext p
  rw [SubProbability.pure_bind, hret, hglob]

/-! ## §6.2 — the lemmas `cleanStmt` rewrites with

The closed set.  `Flatten.cleanLemmas` lists exactly these names and nothing else; the cleaning
pass runs `simp only` with that list and no default simp set, no simprocs and `zeta := false`, so
statement `let`s (the variable names) and everything the delaborators depend on survive.

Three groups, as in the plan: through the statement wrappers (`applyLens`, `weaken`), into
l-values, and into expressions.  Everything that does not match keeps its wrapper — that costs
prettiness, never correctness (§9). -/

section Clean

/-! ### Group 0: lens algebra

`Lens.fst`/`Lens.snd` are rewritten to their `ofst`/`osnd` spellings so that a single set of
navigation lemmas applies; this is also the spelling `mkChain` (the `proc` macro) produces, and
therefore the one the delaborators read back. -/

omit [ProgramSpec] in
@[simp] theorem Lens.fst_eq_ofst_id {a b : Type} :
    (Lens.fst : Lens a (a × b)) = Lens.ofst Lens.id := rfl

omit [ProgramSpec] in
@[simp] theorem Lens.snd_eq_osnd_id {a b : Type} :
    (Lens.snd : Lens b (a × b)) = Lens.osnd Lens.id := rfl

omit [ProgramSpec] in
@[simp] theorem Lens.get_id {a : Type} (s : a) : (Lens.id : Lens a a).get s = s := rfl

omit [ProgramSpec] in
@[simp] theorem Lens.get_ofst {a m m' : Type} (y : Lens a m) (s : m × m') :
    (Lens.ofst (m' := m') y).get s = y.get s.1 := rfl

omit [ProgramSpec] in
@[simp] theorem Lens.get_osnd {a m m' : Type} (y : Lens a m) (s : m' × m) :
    (Lens.osnd (m' := m') y).get s = y.get s.2 := rfl

/-! ### Group 0': the tuple lenses of §4

The meta code never inspects these; cleaning turns a composite of them at a *concrete* variable
list into the plain `Lens.id.ofst.osnd^k` chain that a variable is written as. -/

omit [ProgramSpec] in
@[simp] theorem tupleSuffix_nil (T : Type) : tupleSuffix [] T = Lens.id := rfl

omit [ProgramSpec] in
@[simp] theorem tupleSuffix_cons (b : Type) (B : List Type) (T : Type) :
    tupleSuffix (b :: B) T = (tupleSuffix B T).osnd := rfl

omit [ProgramSpec] in
@[simp] theorem tupleBlock_nil (T : Type) : tupleBlock [] T = Lens.punit := rfl

omit [ProgramSpec] in
@[simp] theorem tupleBlock_single (b T : Type) : tupleBlock [b] T = Lens.id.ofst := rfl

omit [ProgramSpec] in
@[simp] theorem tupleBlock_cons_cons (a b : Type) (B : List Type) (T : Type) :
    tupleBlock (a :: b :: B) T = (tupleBlock (b :: B) T).prodMap := rfl

omit [ProgramSpec] in
@[simp] theorem tupleSplit_single (a : Type) (C : List Type) (T : Type) :
    tupleSplit [a] C T = (tupleBlock C T).prodMap := rfl

omit [ProgramSpec] in
/-- With no parameters, the callee's block is its locals alone. -/
@[simp] theorem tupleSplit_nil_chain_osnd {D : Type} (C : List Type) (T : Type)
    (y : Lens D (typeListToTuple C)) :
    (tupleSplit [] C T).chain (Lens.osnd y) = (tupleBlock C T).chain y := rfl

omit [ProgramSpec] in
/-- The first parameter of a ≥ 2-parameter callee sits at the head of the block. -/
@[simp] theorem tupleSplit_cons_cons_chain_ofst_ofst {D a b : Type} {A C : List Type} {T : Type}
    (y : Lens D a) :
    (tupleSplit (a :: b :: A) C T).chain (Lens.ofst (Lens.ofst y)) = Lens.ofst y := by
  refine Lens.ext _ _ fun v s => ?_
  change (y.set v s.1, (tupleSplit (b :: A) C T).set
      (((tupleSplit (b :: A) C T).get s.2).1, ((tupleSplit (b :: A) C T).get s.2).2) s.2)
    = (y.set v s.1, s.2)
  rw [show (((tupleSplit (b :: A) C T).get s.2).1, ((tupleSplit (b :: A) C T).get s.2).2)
      = (tupleSplit (b :: A) C T).get s.2 from rfl, (tupleSplit (b :: A) C T).get_set]

omit [ProgramSpec] in
/-- A later parameter of a ≥ 2-parameter callee sits one step further in. -/
@[simp] theorem tupleSplit_cons_cons_chain_ofst_osnd {D a b : Type} {A C : List Type} {T : Type}
    (y : Lens D (typeListToTuple (b :: A))) :
    (tupleSplit (a :: b :: A) C T).chain (Lens.ofst (Lens.osnd y))
      = Lens.osnd ((tupleSplit (b :: A) C T).chain (Lens.ofst y)) := rfl

omit [ProgramSpec] in
/-- The callee's locals sit behind all of its parameters. -/
@[simp] theorem tupleSplit_cons_cons_chain_osnd {D a b : Type} {A C : List Type} {T : Type}
    (y : Lens D (typeListToTuple C)) :
    (tupleSplit (a :: b :: A) C T).chain (Lens.osnd y)
      = Lens.osnd ((tupleSplit (b :: A) C T).chain (Lens.osnd y)) := rfl

/-! ### Group 1: through the statement wrappers -/

@[simp] theorem StmtWithHoles.applyLens_skip {h : HoleSigs} {L₁ L₂ : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) :
    (StmtWithHoles.skip (h := h)).applyLens l = StmtWithHoles.skip := rfl

@[simp] theorem StmtWithHoles.applyLens_sample {h : HoleSigs} {L₁ L₂ A : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) (x : Setter A (ProcedureState L₁))
    (e : Getter (SubProbability A) (ProcedureState L₁)) :
    (StmtWithHoles.sample (h := h) x e).applyLens l
      = StmtWithHoles.sample (l.chainSetter x) (l.chainGetter e) := rfl

@[simp] theorem StmtWithHoles.applyLens_assign {h : HoleSigs} {L₁ L₂ A : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) (x : Setter A (ProcedureState L₁))
    (e : Getter A (ProcedureState L₁)) :
    (StmtWithHoles.assign (h := h) x e).applyLens l
      = StmtWithHoles.assign (l.chainSetter x) (l.chainGetter e) := rfl

@[simp] theorem StmtWithHoles.applyLens_call' {h : HoleSigs} {L₁ L₂ : Type}
    {sig : ProcedureSignature} (l : Lens (ProcedureState L₁) (ProcedureState L₂))
    (x : Setter sig.ret (ProcedureState L₁)) (ls : List (Σ t : Type, Inhabited t))
    (b : Stmt (sig.ProcedureScope ls))
    (r : Getter sig.ret (ProcedureState (sig.ProcedureScope ls)))
    (p : Getter sig.ParamType (ProcedureState L₁)) :
    (StmtWithHoles.call' (h := h) x ls b r p).applyLens l
      = StmtWithHoles.call' (l.chainSetter x) ls b r (l.chainGetter p) := rfl

@[simp] theorem StmtWithHoles.applyLens_hole {h : HoleSigs} {L₁ L₂ : Type}
    {sig : ProcedureSignature} (l : Lens (ProcedureState L₁) (ProcedureState L₂))
    (n : HoleIndex h sig) (x : Setter sig.ret (ProcedureState L₁))
    (p : Getter sig.ParamType (ProcedureState L₁)) :
    (StmtWithHoles.hole n x p).applyLens l
      = StmtWithHoles.hole n (l.chainSetter x) (l.chainGetter p) := rfl

@[simp] theorem StmtWithHoles.applyLens_seq {h : HoleSigs} {L₁ L₂ : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) (s₁ s₂ : StmtWithHoles h L₁) :
    (s₁.seq s₂).applyLens l = (s₁.applyLens l).seq (s₂.applyLens l) := rfl

@[simp] theorem StmtWithHoles.applyLens_ifThenElse {h : HoleSigs} {L₁ L₂ : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) (c : Getter Bool (ProcedureState L₁))
    (t e : StmtWithHoles h L₁) :
    (StmtWithHoles.ifThenElse c t e).applyLens l
      = StmtWithHoles.ifThenElse (l.chainGetter c) (t.applyLens l) (e.applyLens l) := rfl

@[simp] theorem StmtWithHoles.applyLens_while {h : HoleSigs} {L₁ L₂ : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) (c : Getter Bool (ProcedureState L₁))
    (b : StmtWithHoles h L₁) :
    (StmtWithHoles.while c b).applyLens l
      = StmtWithHoles.while (l.chainGetter c) (b.applyLens l) := rfl

/-- Two nested re-targetings collapse into one — what a second flattening round leaves behind. -/
@[simp] theorem StmtWithHoles.applyLens_applyLens {h : HoleSigs} {L₁ L₂ L₃ : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂))
    (m : Lens (ProcedureState L₂) (ProcedureState L₃)) :
    ∀ s : StmtWithHoles h L₁, (s.applyLens l).applyLens m = s.applyLens (m.chain l)
  | .skip             => rfl
  | .sample _ _       => rfl
  | .call' _ _ _ _ _  => rfl
  | .hole _ _ _       => rfl
  | .seq s₁ s₂        => by
      simp only [StmtWithHoles.applyLens, applyLens_applyLens l m s₁, applyLens_applyLens l m s₂]
  | .ifThenElse _ t e => by
      simp only [StmtWithHoles.applyLens, applyLens_applyLens l m t, applyLens_applyLens l m e]
      rfl
  | .while _ b        => by
      simp only [StmtWithHoles.applyLens, applyLens_applyLens l m b]
      rfl

@[simp] theorem StmtWithHoles.weaken_skip {h : HoleSigs} {L : Type} :
    StmtWithHoles.weaken (h := h) (StmtWithHoles.skip (l := L)) = StmtWithHoles.skip := by
  simp only [StmtWithHoles.weaken]

@[simp] theorem StmtWithHoles.weaken_sample {h : HoleSigs} {L A : Type}
    (x : Setter A (ProcedureState L)) (e : Getter (SubProbability A) (ProcedureState L)) :
    StmtWithHoles.weaken (h := h) (StmtWithHoles.sample x e) = StmtWithHoles.sample x e := by
  simp only [StmtWithHoles.weaken]

@[simp] theorem StmtWithHoles.weaken_assign {h : HoleSigs} {L A : Type}
    (x : Setter A (ProcedureState L)) (e : Getter A (ProcedureState L)) :
    StmtWithHoles.weaken (h := h) (StmtWithHoles.assign x e) = StmtWithHoles.assign x e := by
  simp only [StmtWithHoles.assign, StmtWithHoles.weaken]

@[simp] theorem StmtWithHoles.weaken_call' {h : HoleSigs} {L : Type} {sig : ProcedureSignature}
    (x : Setter sig.ret (ProcedureState L)) (ls : List (Σ t : Type, Inhabited t))
    (b : Stmt (sig.ProcedureScope ls))
    (r : Getter sig.ret (ProcedureState (sig.ProcedureScope ls)))
    (p : Getter sig.ParamType (ProcedureState L)) :
    StmtWithHoles.weaken (h := h) (StmtWithHoles.call' x ls b r p)
      = StmtWithHoles.call' x ls b r p := by
  simp only [StmtWithHoles.weaken]

@[simp] theorem StmtWithHoles.weaken_seq {h : HoleSigs} {L : Type} (s₁ s₂ : Stmt L) :
    StmtWithHoles.weaken (h := h) (s₁.seq s₂)
      = (StmtWithHoles.weaken s₁).seq (StmtWithHoles.weaken s₂) := by
  simp only [StmtWithHoles.weaken]

@[simp] theorem StmtWithHoles.weaken_ifThenElse {h : HoleSigs} {L : Type}
    (c : Getter Bool (ProcedureState L)) (t e : Stmt L) :
    StmtWithHoles.weaken (h := h) (StmtWithHoles.ifThenElse c t e)
      = StmtWithHoles.ifThenElse c (StmtWithHoles.weaken t) (StmtWithHoles.weaken e) := by
  simp only [StmtWithHoles.weaken]

@[simp] theorem StmtWithHoles.weaken_while {h : HoleSigs} {L : Type}
    (c : Getter Bool (ProcedureState L)) (b : Stmt L) :
    StmtWithHoles.weaken (h := h) (StmtWithHoles.while c b)
      = StmtWithHoles.while c (StmtWithHoles.weaken b) := by
  simp only [StmtWithHoles.weaken]

/-- Weakening and re-targeting commute, so the two wrappers can be pushed inwards together. -/
@[simp] theorem StmtWithHoles.weaken_applyLens {h : HoleSigs} {L₁ L₂ : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) :
    ∀ s : Stmt L₁, StmtWithHoles.weaken (h := h) (s.applyLens l)
      = (StmtWithHoles.weaken (h := h) s).applyLens l
  | .skip             => by simp only [StmtWithHoles.applyLens, StmtWithHoles.weaken]
  | .sample _ _       => by simp only [StmtWithHoles.applyLens, StmtWithHoles.weaken]
  | .call' _ _ _ _ _  => by simp only [StmtWithHoles.applyLens, StmtWithHoles.weaken]
  | .seq s₁ s₂        => by
      simp only [StmtWithHoles.applyLens, StmtWithHoles.weaken,
        weaken_applyLens l s₁, weaken_applyLens l s₂]
  | .ifThenElse _ t e => by
      simp only [StmtWithHoles.applyLens, StmtWithHoles.weaken,
        weaken_applyLens l t, weaken_applyLens l e]
  | .while _ b        => by
      simp only [StmtWithHoles.applyLens, StmtWithHoles.weaken, weaken_applyLens l b]
  termination_by s => s.depth
  decreasing_by all_goals simp only [StmtWithHoles.depth]; omega

/-! ### Group 2: into l-values -/

/-- A variable used as an l-value travels along the lens. -/
@[simp] theorem Lens.chainSetter_liftLens {L₁ L₂ A : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) (x : Lens A (ProcedureState L₁)) :
    l.chainSetter (liftLens x) = liftLens (l.chain x) := rfl

/-- A *global* l-value is unaffected: neither of §4's lenses touches the global state. -/
@[simp] theorem Lens.chainSetter_liftLens_global {L₁ L₂ A : Type} (m : Lens L₁ L₂)
    (g : Lens A State) :
    (ProcedureState.mapScope m).chainSetter (liftLens (S := L₁) g) = liftLens (S := L₂) g := by
  ext v τ
  change (⟨g.set v τ.global, m.set (m.get τ.locals) τ.locals⟩ : ProcedureState L₂)
      = ⟨g.set v τ.global, τ.locals⟩
  rw [m.get_set]

/-- A discarded result stays discarded, so a void call does not acquire an l-value. -/
@[simp] theorem Lens.chainSetter_throwaway {A s t : Type} (l : Lens s t) :
    l.chainSetter (Setter.throwaway (a := A)) = Setter.throwaway := by
  ext v τ; exact l.get_set τ

omit [ProgramSpec] in
/-- A lens used as an l-value composes as a lens. -/
@[simp] theorem Lens.chainSetter_toSetter {a s t : Type} (l : Lens s t) (x : Lens a s) :
    l.chainSetter (Lens.toSetter x) = Lens.toSetter (l.chain x) := rfl

omit [ProgramSpec] in
@[simp] theorem Lens.chainSetter_chainSetter {a s t u : Type} (m : Lens t u) (l : Lens s t)
    (x : Setter a s) : m.chainSetter (l.chainSetter x) = (m.chain l).chainSetter x := rfl

omit [ProgramSpec] in
@[simp] theorem Lens.chainGetter_chainGetter {a s t u : Type} (m : Lens t u) (l : Lens s t)
    (g : Getter a s) : m.chainGetter (l.chainGetter g) = (m.chain l).chainGetter g := rfl

/-! ### Group 3: into expressions

A `GaudiExpr` getter is `Getter.mk (fun st => body)` with every variable read spelled
`Evaluatable.eval st x` (that is what `§x` elaborates to).  Composing it with a lens beta-reduces
to the same body at `l.get st`, and these four lemmas move the lens from the *state* to the
*variable* — after which group 0 normalizes the variable and the read prints as `§x` again. -/

@[simp] theorem eval_chain_lens {L₁ L₂ A : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) (τ : ProcedureState L₂)
    (x : Lens A (ProcedureState L₁)) :
    (eval (S := L₁) (cs := ⟨l.get τ⟩) x : A) = eval (S := L₂) (cs := ⟨τ⟩) (l.chain x) := rfl

@[simp] theorem eval_chain_getter {L₁ L₂ A : Type}
    (l : Lens (ProcedureState L₁) (ProcedureState L₂)) (τ : ProcedureState L₂)
    (x : Getter A (ProcedureState L₁)) :
    (eval (S := L₁) (cs := ⟨l.get τ⟩) x : A) = eval (S := L₂) (cs := ⟨τ⟩) (l.chainGetter x) := rfl

@[simp] theorem eval_mapScope_global_lens {L₁ L₂ A : Type} (m : Lens L₁ L₂)
    (τ : ProcedureState L₂) (g : Lens A State) :
    (eval (S := L₁) (cs := ⟨(ProcedureState.mapScope m).get τ⟩) g : A)
      = eval (S := L₂) (cs := ⟨τ⟩) g := rfl

@[simp] theorem eval_mapScope_global_getter {L₁ L₂ A : Type} (m : Lens L₁ L₂)
    (τ : ProcedureState L₂) (g : Getter A State) :
    (eval (S := L₁) (cs := ⟨(ProcedureState.mapScope m).get τ⟩) g : A)
      = eval (S := L₂) (cs := ⟨τ⟩) g := rfl

end Clean

/-! # The meta code (§6) -/

namespace Flatten

open Lean Meta

/-- `Lean.Expr`, under a name that `GaudisCrypt.Expr` (the program-expression abbreviation) does
not shadow. -/
abbrev Expr := Lean.Expr

/-- What one flattening step produces: the rewritten statement, the new locals list, the widening
lens, and a proof of `‹input›.EquivInLens stmt trafo`. -/
structure FlattenStep where
  /-- The rewritten statement, at the widened scope. -/
  stmt : Expr
  /-- The new locals list (the type index of `stmt`). -/
  newLocals : Expr
  /-- The widening lens. -/
  trafo : Expr
  /-- A proof of `‹input›.EquivInLens stmt trafo`. -/
  proof : Expr
  /-- The `ProgramSpec` instance the statement is over. -/
  inst : Expr
  /-- The hole context. -/
  hCtx : Expr
  /-- The parameter list, which flattening never changes. -/
  params : Expr
  /-- The locals list the statement had *before* this step — the scope whose variable names have
  priority when a callee's name collides with one of them (§3). -/
  oldLocals : Expr
  /-- Where each variable of the new scope came from — its source scope's two index lists,
  whether it was a parameter there, and its slot.  Parameters first, then locals; §7 uses this to
  recover the variable names from the telescopes it took apart. -/
  origin : Array (Expr × Expr × Bool × Nat)

/-- Expose the statement hiding behind projections and definitions (`someProc.body`), *without*
zeta-reducing its `let` telescope — those binders are the variable names, and the cleaning pass
and the delaborators both need them. -/
def unfoldStmt (e : Expr) : MetaM Expr :=
  withConfig (fun c => { c with zeta := false, zetaDelta := false }) (whnf e)

/-- The elements of a literal `List` expression.  Reducible transparency only: a callee named by
a definition stays stuck here, which is what makes §2's "literal callees only" rule bite. -/
partial def listLitElems (e : Expr) : MetaM (List Expr) := do
  match (← whnfR e).getAppFnArgs with
  | (``List.nil, _)             => return []
  | (``List.cons, #[_, hd, tl]) => return hd :: (← listLitElems tl)
  | _ => throwError "expected a literal list, got{indentExpr e}"

/-- Is this application a **call site** — one of the two call forms, or a hole?

A hole is a call whose callee is not known yet, so it is one of the things a user counts when
numbering the call sites of a statement, even though neither flattening nor inlining can do
anything with it.  Numbering it along with the rest is what keeps the call-site numbers of a
statement independent of which sites happen to be flattenable. -/
def isCallSite (e : Expr) : Bool :=
  e.isAppOf ``StmtWithHoles.call' || e.isAppOf ``StmtWithHoles.call
    || e.isAppOf ``StmtWithHoles.hole

/-- How many call sites the statement contains, in the pre-order they are numbered by.  A callee's
own body is *not* searched: its calls belong to a later round. -/
partial def countCallSites (e₀ : Expr) : MetaM Nat := do
  let e ← unfoldStmt e₀
  if isCallSite e then return 1
  match e with
  | .letE _ _ _ body _ => countCallSites body
  | _ =>
    let args := e.getAppArgs
    match e.getAppFn.constName? with
    | some ``StmtWithHoles.seq =>
        return (← countCallSites args[3]!) + (← countCallSites args[4]!)
    | some ``StmtWithHoles.ifThenElse =>
        return (← countCallSites args[4]!) + (← countCallSites args[5]!)
    | some ``StmtWithHoles.while => countCallSites args[4]!
    | _ => return 0

/-- The pieces of a call: its signature, result l-value, callee locals/body/return value, and
argument expression.  Both call forms are accepted; a `call` needs a literal callee. -/
structure CallData where
  /-- The callee's signature. -/
  sig : Expr
  /-- Where the result is stored. -/
  lvalue : Expr
  /-- The callee's local-variable list. -/
  locals : Expr
  /-- The callee's body. -/
  body : Expr
  /-- The callee's return value. -/
  retVal : Expr
  /-- The argument expression. -/
  args : Expr

/-- Read a call's pieces off the application. -/
def callData? (e : Expr) : MetaM (Option CallData) := do
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``StmtWithHoles.call' =>
      -- `[inst] {l h sig} x locals body ret params`
      return some { sig := args[3]!, lvalue := args[4]!, locals := args[5]!, body := args[6]!,
                    retVal := args[7]!, args := args[8]! }
  | some ``StmtWithHoles.call =>
      -- `[inst] {l h sig} x proc params`
      let p ← whnf args[5]!
      let pargs := p.getAppArgs
      unless p.isAppOf ``ProcedureWithHoles.mk && pargs.size == 6 do
        return none
      return some { sig := args[3]!, lvalue := args[4]!, locals := pargs[3]!, body := pargs[4]!,
                    retVal := pargs[5]!, args := args[6]! }
  | _ => return none

/-- The call site at the given pre-order index, if there is one. -/
partial def findCallSite? (idx : Nat) (e₀ : Expr) : MetaM (Option Expr) := do
  let e ← unfoldStmt e₀
  if isCallSite e then return if idx == 0 then some e else none
  match e with
  | .letE _ _ _ body _ => findCallSite? idx body
  | _ =>
    let args := e.getAppArgs
    let two (a b : Expr) : MetaM (Option Expr) := do
      let na ← countCallSites a
      if idx < na then findCallSite? idx a else findCallSite? (idx - na) b
    match e.getAppFn.constName? with
    | some ``StmtWithHoles.seq => two args[3]! args[4]!
    | some ``StmtWithHoles.ifThenElse => two args[4]! args[5]!
    | some ``StmtWithHoles.while => findCallSite? idx args[4]!
    | _ => return none

/-- A proof of an (iterated ∀ over an) equation, by `rfl`.  All the freshness side conditions of
`StmtWithHoles.equivInLens_flattenCall` are of this shape: at concrete variable lists both sides
compute to the same term. -/
def mkRflProof (ty : Expr) : MetaM Expr :=
  forallTelescope ty fun xs body => do
    let some (_, lhs, _) := body.eq?
      | throwError "expected an equation, got{indentExpr body}"
    mkLambdaFVars xs (← mkEqRefl lhs)

/-- Apply `f` to a `rfl` proof of whatever its next argument's type demands. -/
def appRfl (f : Expr) : MetaM Expr := do
  let ty ← whnf (← inferType f)
  let .forallE _ dom _ _ := ty | throwError "expected a function type, got{indentExpr ty}"
  return mkApp f (← mkRflProof dom)

/-- `(t : Type) × Inhabited t`, the entry type of a locals list, and `fun t => Inhabited t`. -/
def sigmaInhabited : MetaM (Expr × Expr) := do
  let fam := Lean.Expr.lam `t (mkSort Level.one)
    (mkApp (mkConst ``Inhabited [Level.one]) (.bvar 0)) .default
  return (← mkAppOptM ``Sigma #[none, some fam], fam)

/-- Annotate whatever goes wrong inside `k` with the step that was being built. -/
def inStep {α : Type} (what : String) (k : MetaM α) : MetaM α :=
  try k catch e => throwError "while building {what}: {e.toMessageData}"

/-! ## Variable slots

A program variable is `Lens.intoParams`/`Lens.intoLocalVars` of a *slot chain* — `Lens.id`
followed by `.ofst`/`.osnd` steps, exactly what `mkChain (navSteps k n)` in `ProgramSyntax.lean`
builds and what the delaborators read back.  Everything below builds and reads that shape; the
two directions are inverse, which is what makes the re-telescoping of §7 a syntactic operation. -/

/-- `typeListToTuple`, computed: the last element stays unwrapped. -/
def mkTupleTy : List Expr → MetaM Expr
  | []      => return mkConst ``Unit
  | [t]     => return t
  | t :: ts => do mkAppM ``Prod #[t, ← mkTupleTy ts]

/-- The lens onto slot `k` of a right-nested tuple of `tys` — `Lens.id.ofst.osnd^k`, or
`Lens.id.osnd^k` for the (unwrapped) last slot. -/
def mkSlotLens (tys : List Expr) (k : Nat) : MetaM Expr := do
  let n := tys.length
  unless k < n do throwError "slot {k} out of range for a {n}-tuple"
  let tk := tys[k]!
  let mut acc ← mkAppOptM ``Lens.id #[some tk]
  if k + 1 != n then
    acc ← mkAppOptM ``Lens.ofst #[some tk, some tk, some (← mkTupleTy (tys.drop (k + 1))), some acc]
  for i in [0:k] do
    let j := k - 1 - i
    acc ← mkAppOptM ``Lens.osnd
      #[some tk, some (← mkTupleTy (tys.drop (j + 1))), some tys[j]!, some acc]
  return acc

/-- The inverse of `mkSlotLens`: which slot of an `n`-tuple this chain navigates to. -/
partial def slotOfLens? (slot : Expr) (n : Nat) : Option Nat :=
  go slot 0
where
  /-- Peel `.osnd` steps, then expect either `.ofst Lens.id` or (in the last slot) `Lens.id`. -/
  go (e : Expr) (k : Nat) : Option Nat :=
    if e.isAppOfArity ``Lens.osnd 4 then go e.appArg! (k + 1)
    else if k + 1 == n then (if e.isAppOfArity ``Lens.id 1 then some k else none)
    else if e.isAppOfArity ``Lens.ofst 4 && e.appArg!.isAppOfArity ``Lens.id 1 then some k
    else none

/-- A program variable's lens, split into "is it a parameter", its content type, the scope's two
index lists, and the slot chain. -/
def varLens? (e : Expr) : Option (Bool × Expr × Expr × Expr × Expr) :=
  let a := e.getAppArgs
  if e.isAppOfArity ``Lens.intoParams 5 then some (true, a[1]!, a[2]!, a[3]!, a[4]!)
  else if e.isAppOfArity ``Lens.intoLocalVars 5 then some (false, a[1]!, a[2]!, a[3]!, a[4]!)
  else none

/-- Which variable of which scope a `let`'s value is, if it is one at all: the scope's parameter
and locals lists, whether it is a parameter, and its slot. -/
def varLetInfo? (val : Expr) : MetaM (Option (Expr × Expr × Bool × Nat)) := do
  let some (isParam, _, ptys, locs, slot) := varLens? val | return none
  let n? ← try
      pure (some (← listLitElems (if isParam then ptys else locs)).length)
    catch _ => pure none
  let some n := n? | return none
  return (slotOfLens? slot n).map fun k => (ptys, locs, isParam, k)

/-- What a scope's variables are called, keyed by the scope (its two index lists) and the slot.
Collected while §7 zeta-reduces the `let` telescopes; consumed when it rebuilds them. -/
abbrev VarTable := Array (Expr × Expr × Bool × Nat × Name)

/-- Look up the name a scope gave slot `k`. -/
def VarTable.find? (t : VarTable) (ptys locs : Expr) (isParam : Bool) (k : Nat) :
    MetaM (Option Name) := do
  for (p, l, ip, j, n) in t do
    if ip == isParam && j == k then
      if (← isDefEq p ptys) && (← isDefEq l locs) then return some n
  return none

/-- The replacement for one call, with its proof: everything of §4–§6 at a single call site. -/
structure CallPlan where
  /-- The new locals list `B ++ Ls`. -/
  newLocals : Expr
  /-- The widening lens. -/
  trafo : Expr
  /-- `trafo.chain globalL = globalL`. -/
  htg : Expr
  /-- The statement replacing the call. -/
  stmt : Expr
  /-- `(call …).EquivInLens stmt trafo`. -/
  proof : Expr
  /-- See `FlattenStep.origin`. -/
  origin : Array (Expr × Expr × Bool × Nat)

/-- Build the lenses, the four-part expansion and its correctness proof for one call site. -/
def planCall (inst hCtx P Ls : Expr) (cd : CallData) : MetaM CallPlan := do
  -- the callee's signature must expose a literal parameter list
  let sigW ← whnf cd.sig
  unless sigW.isAppOfArity ``ProcedureSignature.mk 2 do
    throwError "callee's signature is not literal:{indentExpr cd.sig}"
  let sigParams := sigW.getAppArgs[0]!
  let paramTys ← listLitElems sigParams
  -- a call built by `StmtWithHoles.call` carries the callee's fields as projections
  let calleeLocalsE ← whnfR cd.locals
  let calleeLocals ← try listLitElems calleeLocalsE catch _ =>
    throwError "the call is not flattenable: its callee is not spelled out at the call site\
      {indentExpr calleeLocalsE}"
  let ownLocals ← listLitElems Ls
  let (sigmaTy, fam) ← sigmaInhabited
  -- the callee's parameters become locals, so they need `Inhabited`
  let paramEntries ← paramTys.mapM fun t => do
    let .some i ← trySynthInstance (mkApp (mkConst ``Inhabited [Level.one]) t)
      | throwError "callee parameter type has no `Inhabited` instance:{indentExpr t}"
    mkAppOptM ``Sigma.mk #[none, some fam, some t, some i]
  let calleeLocalEntries ← calleeLocals.mapM fun e => do
    let w ← whnf e
    unless w.isAppOfArity ``Sigma.mk 4 do
      throwError "callee's locals list is not literal:{indentExpr cd.locals}"
    pure (w.getAppArgs[2]!, w.getAppArgs[3]!)
  let calleeLocalTys := calleeLocalEntries.map (·.1)
  let blockEntries := paramEntries ++ calleeLocals
  let blockTys := paramTys ++ calleeLocalTys
  let newLocals ← mkListLit sigmaTy (blockEntries ++ ownLocals)
  let blockTysE ← mkListLit (mkSort Level.one) blockTys
  let calleeLocalTysE ← mkListLit (mkSort Level.one) calleeLocalTys
  -- the tail tuple: the variables the statement already had
  let tailTuple ← mkAppM ``typeListToTuple #[← mkAppM ``localTypes #[Ls]]
  let scopeNew ← mkAppM ``ProcedureScope #[P, newLocals]
  -- `trafo` and `emb`
  let mapVars ← inStep "the widening lens" <| mkAppOptM ``ProcedureScope.mapVars
    #[some P, some Ls, some newLocals, some (← mkAppM ``tupleSuffix #[blockTysE, tailTuple])]
  let trafo ← mkAppM ``ProcedureState.mapScope #[mapVars]
  let embScope ← inStep "the callee embedding" <| mkAppOptM ``ProcedureScope.embedInLocalVars
    #[some P, some sigParams, some newLocals, some calleeLocalsE,
      some (← mkAppM ``tupleSplit #[sigParams, calleeLocalTysE, tailTuple])]
  let emb ← mkAppM ``ProcedureState.mapScope #[embScope]
  let htg ← mkAppM ``mapScope_chain_globalL #[mapVars]
  let heg ← mkAppM ``mapScope_chain_globalL #[embScope]
  -- the prelude (§6.1, pieces 1 and 2): one assignment per callee variable — its locals to their
  -- `Inhabited` default (they are re-initialised on *every* call, which is what makes flattening
  -- inside a loop sound), then its parameters to the argument's components.  Written through
  -- `emb`, so §6.2 turns each l-value into the new local it became.
  let stateNew ← mkAppM ``ProcedureState #[scopeNew]
  let scopeCallee ← mkAppM ``ProcedureScope #[sigParams, calleeLocalsE]
  let stateCallee ← mkAppM ``ProcedureState #[scopeCallee]
  -- the callee's own variable `v`, as an l-value at the callee's scope
  let calleeLValue (t v : Expr) : MetaM Expr :=
    mkAppOptM ``liftLens #[some inst, some scopeCallee, some t, some stateCallee, none, some v]
  let argsWide ← inStep "the argument expression" <| mkAppM ``Lens.chainGetter #[trafo, cd.args]
  let mut steps : Array (Expr × Expr) := #[]
  for j in [0:calleeLocalEntries.length] do
    let (t, ti) := calleeLocalEntries[j]!
    let slot ← mkSlotLens calleeLocalTys j
    let v ← mkAppOptM ``Lens.intoLocalVars
      #[some inst, some t, some sigParams, some calleeLocalsE, some slot]
    let setter ← inStep "a callee local's l-value" <|
      mkAppM ``Lens.chainSetter #[emb, ← calleeLValue t v]
    let dflt ← mkAppOptM ``default #[some t, some ti]
    let getter ← withLocalDeclD `tau stateNew fun τ => do
      mkAppM ``Getter.mk #[← mkLambdaFVars #[τ] dflt]
    steps := steps.push (setter, getter)
  for k in [0:paramTys.length] do
    let t := paramTys[k]!
    let slot ← mkSlotLens paramTys k
    let v ← mkAppOptM ``Lens.intoParams
      #[some inst, some t, some sigParams, some calleeLocalsE, some slot]
    let setter ← inStep "a callee parameter's l-value" <|
      mkAppM ``Lens.chainSetter #[emb, ← calleeLValue t v]
    let getter ← inStep "a callee parameter's value" <|
      withLocalDeclD `tau stateNew fun τ => do
        let whole ← mkAppM ``Getter.get #[argsWide, τ]
        let proj ← mkAppM ``Getter.get #[← mkAppM ``Lens.toGetter #[slot], whole]
        mkAppM ``Getter.mk #[← mkLambdaFVars #[τ] proj]
    steps := steps.push (setter, getter)
  -- fold the assignments into one statement, one state map and one `hpre`
  let idFun ← withLocalDeclD `tau stateNew fun τ => mkLambdaFVars #[τ] τ
  let skipStmt ← mkAppOptM ``StmtWithHoles.skip
    #[some inst, some (mkConst ``HoleSigs.empty), some scopeNew]
  let mut pre := skipStmt
  let mut f := idFun
  let mut hpre ← mkAppOptM ``programDenotation_skip_apply #[some inst, some scopeNew]
  for (setter, getter) in steps.reverse do
    let a ← mkAppOptM ``StmtWithHoles.assign
      #[none, none, some (mkConst ``HoleSigs.empty), none, some setter, some getter]
    let fa ← withLocalDeclD `tau stateNew fun τ => do
      mkLambdaFVars #[τ] (← mkAppM ``Setter.set #[setter, ← mkAppM ``Getter.get #[getter, τ], τ])
    let ha ← mkAppM ``programDenotation_assign_apply #[setter, getter]
    if pre == skipStmt then
      pre := a; f := fa; hpre := ha
    else
      hpre ← mkAppM ``programDenotation_seq_apply_det #[ha, hpre]
      pre ← mkAppM ``StmtWithHoles.seq #[a, pre]
      let f₀ := f
      f ← withLocalDeclD `tau stateNew fun τ =>
        mkLambdaFVars #[τ] (mkApp f₀ (mkApp fa τ).headBeta).headBeta
  -- the four-part expansion
  let preW ← mkAppOptM ``StmtWithHoles.weaken #[some inst, some hCtx, none, some pre]
  let bodyW ← mkAppOptM ``StmtWithHoles.weaken
    #[some inst, some hCtx, none, some (← mkAppM ``StmtWithHoles.applyLens #[emb, cd.body])]
  let retAssign ← mkAppOptM ``StmtWithHoles.assign
    #[none, none, some hCtx, none,
      some (← mkAppM ``Lens.chainSetter #[trafo, cd.lvalue]),
      some (← mkAppM ``Lens.chainGetter #[emb, cd.retVal])]
  let stmt ← mkAppM ``StmtWithHoles.seq
    #[preW, ← mkAppM ``StmtWithHoles.seq #[bodyW, retAssign]]
  -- the proof, with the three freshness conditions by `rfl`
  let proof ← mkAppOptM ``StmtWithHoles.equivInLens_flattenCall
    #[some inst, some hCtx, none, none, some sigW, some calleeLocalsE,
      some trafo, some emb, some htg, some heg]
  let proof ← appRfl proof                                        -- hdisj
  let proof := mkAppN proof #[cd.lvalue, cd.args, cd.body, cd.retVal, pre, f, hpre]
  let proof ← appRfl proof                                        -- hpre_get
  let proof ← appRfl proof                                        -- hpre_vis
  -- §7 bookkeeping: the new scope's parameters are the old ones, and its locals are the callee's
  -- parameters, then the callee's locals, then the statement's own locals (§3)
  let ownParams ← listLitElems P
  let origin : Array (Expr × Expr × Bool × Nat) :=
    (Array.range ownParams.length).map (fun k => (P, Ls, true, k))
      ++ (Array.range paramTys.length).map (fun k => (sigParams, calleeLocalsE, true, k))
      ++ (Array.range calleeLocalTys.length).map (fun j => (sigParams, calleeLocalsE, false, j))
      ++ (Array.range ownLocals.length).map (fun j => (P, Ls, false, j))
  return { newLocals, trafo, htg, stmt, proof, origin }

/-- What the traversal returns: the rewritten statement, its proof, and the plan the call site
produced (the lenses are only known once the call has been reached). -/
structure PathResult where
  /-- The rewritten statement. -/
  stmt : Expr
  /-- Its correctness proof. -/
  proof : Expr
  /-- The plan built at the call site. -/
  plan : CallPlan

/-- Rebuild the statement along the path to call `idx`, planning the call where it is found —
inside whatever `let` binders enclose it, since the call mentions their variables.  Everything off
the path is re-targeted wholesale with `applyLens`, without being inspected. -/
partial def rebuildPath (inst hCtx P Ls : Expr) (idx : Nat) (stmt₀ : Expr) : MetaM PathResult := do
  let stmt ← unfoldStmt stmt₀
  if stmt.isAppOf ``StmtWithHoles.hole then
    throwError "this call site is a hole: it has no callee to flatten"
  if isCallSite stmt then
    let some cd ← callData? stmt
      | throwError "the call is not flattenable: its callee is not spelled out"
    let plan ← planCall inst hCtx P Ls cd
    return { stmt := plan.stmt, proof := plan.proof, plan }
  match stmt with
  | .letE n ty val body _ =>
      withLetDecl n ty val fun fv => do
        let res ← rebuildPath inst hCtx P Ls idx (body.instantiate1 fv)
        -- `usedLetOnly := false`: a variable the statement happens not to mention is still part
        -- of the scope, and §7 needs its *name*
        return { res with stmt := ← mkLetFVars #[fv] res.stmt (usedLetOnly := false),
                          proof := ← mkLetFVars #[fv] res.proof (usedLetOnly := false) }
  | _ =>
    let args := stmt.getAppArgs
    -- a subprogram that does not contain the call, re-targeted and justified in one step
    let off (plan : CallPlan) (s : Expr) : MetaM (Expr × Expr) := do
      return (← mkAppM ``StmtWithHoles.applyLens #[plan.trafo, s],
              ← mkAppM ``StmtWithHoles.equivInLens_applyLens #[plan.trafo, plan.htg, s])
    match stmt.getAppFn.constName? with
    | some ``StmtWithHoles.seq =>
        let a := args[3]!
        let b := args[4]!
        let na ← countCallSites a
        let (res, a', pa, b', pb) ←
          if idx < na then do
            let res ← rebuildPath inst hCtx P Ls idx a
            let (b', pb) ← off res.plan b
            pure (res, res.stmt, res.proof, b', pb)
          else do
            let res ← rebuildPath inst hCtx P Ls (idx - na) b
            let (a', pa) ← off res.plan a
            pure (res, a', pa, res.stmt, res.proof)
        return { res with
          stmt := ← mkAppM ``StmtWithHoles.seq #[a', b'],
          proof := ← mkAppM ``StmtWithHoles.EquivInLens.seq #[pa, pb] }
    | some ``StmtWithHoles.ifThenElse =>
        let c := args[3]!
        let t := args[4]!
        let e := args[5]!
        let nt ← countCallSites t
        let (res, t', pt, e', pe) ←
          if idx < nt then do
            let res ← rebuildPath inst hCtx P Ls idx t
            let (e', pe) ← off res.plan e
            pure (res, res.stmt, res.proof, e', pe)
          else do
            let res ← rebuildPath inst hCtx P Ls (idx - nt) e
            let (t', pt) ← off res.plan t
            pure (res, t', pt, res.stmt, res.proof)
        return { res with
          stmt := ← mkAppM ``StmtWithHoles.ifThenElse
            #[← mkAppM ``Lens.chainGetter #[res.plan.trafo, c], t', e'],
          proof := ← mkAppM ``StmtWithHoles.EquivInLens.ifThenElse #[c, pt, pe] }
    | some ``StmtWithHoles.while =>
        let c := args[3]!
        let b := args[4]!
        let res ← rebuildPath inst hCtx P Ls idx b
        return { res with
          stmt := ← mkAppM ``StmtWithHoles.while
            #[← mkAppM ``Lens.chainGetter #[res.plan.trafo, c], res.stmt],
          proof := ← mkAppM ``StmtWithHoles.EquivInLens.while #[c, res.proof] }
    | _ => throwError "no call here:{indentExpr stmt}"

/-- **§6.1** — flatten call number `n` (pre-order), leaving the result deliberately uncleaned. -/
def flattenCall (n : Nat) (stmt : Expr) : MetaM FlattenStep := do
  let ty ← whnf (← inferType stmt)
  unless ty.isAppOfArity ``StmtWithHoles 3 do
    throwError "not a `StmtWithHoles`:{indentExpr ty}"
  let tyArgs := ty.getAppArgs
  let inst := tyArgs[0]!
  let hCtx := tyArgs[1]!
  let scope ← whnf tyArgs[2]!
  unless scope.isAppOfArity ``ProcedureScope 2 do
    throwError "the statement's scope is not a `ProcedureScope`:{indentExpr tyArgs[2]!}"
  -- the enclosing statement's own parameter and locals lists have to be literal; unlike a
  -- callee, they may be reached through definitions (`someProc.locals`), so reduce them
  let P ← whnf scope.getAppArgs[0]!
  let Ls ← whnf scope.getAppArgs[1]!
  let total ← countCallSites stmt
  if n ≥ total then
    throwError "there is no call site number {n}: the statement has {total}"
  let res ← rebuildPath inst hCtx P Ls n stmt
  return { stmt := res.stmt, newLocals := res.plan.newLocals, trafo := res.plan.trafo,
           proof := res.proof, inst, hCtx, params := P, oldLocals := Ls,
           origin := res.plan.origin }

/-! ## §6.2 — `cleanStmt`

`simp only` with `cleanLemmas` and **nothing else**: no default simp set, no simprocs, and
`zeta := false` / `zetaDelta := false`, so the `let`s that carry variable names survive.  The only
declaration unfolded is `Lens.chainGetter`, which has to go away for the `eval` lemmas of group 3
to see the state they are composed with. -/

/-- The closed lemma list of §6.2.  Nothing outside this list ever rewrites the statement. -/
def cleanLemmas : List Name :=
  -- group 0: lens algebra and the slot chains a variable is written as
  [``Lens.fst_eq_ofst_id, ``Lens.snd_eq_osnd_id,
   ``Lens.get_id, ``Lens.get_ofst, ``Lens.get_osnd,
   ``Lens.id_chain, ``Lens.chain_id, ``Lens.chain_assoc,
   ``Lens.osnd_chain, ``Lens.ofst_chain,
   ``Lens.prodMap_chain_ofst, ``Lens.prodMap_chain_osnd,
  -- group 0': §4's tuple lenses
   ``tupleSuffix_nil, ``tupleSuffix_cons,
   ``tupleBlock_nil, ``tupleBlock_single, ``tupleBlock_cons_cons,
   ``tupleSplit_single, ``tupleSplit_nil_chain_osnd,
   ``tupleSplit_cons_cons_chain_ofst_ofst, ``tupleSplit_cons_cons_chain_ofst_osnd,
   ``tupleSplit_cons_cons_chain_osnd,
  -- §4's interface: what a variable lens becomes under the two transformations
   ``mapVars_chain_intoParams, ``mapVars_chain_intoLocalVars,
   ``embedInLocalVars_chain_intoParams, ``embedInLocalVars_chain_intoLocalVars,
   ``mapScope_chain_globalL,
  -- group 1: through the statement wrappers
   ``StmtWithHoles.applyLens_skip, ``StmtWithHoles.applyLens_sample,
   ``StmtWithHoles.applyLens_assign, ``StmtWithHoles.applyLens_call',
   ``StmtWithHoles.applyLens_hole, ``StmtWithHoles.applyLens_seq,
   ``StmtWithHoles.applyLens_ifThenElse, ``StmtWithHoles.applyLens_while,
   ``StmtWithHoles.applyLens_applyLens,
   ``StmtWithHoles.weaken_skip, ``StmtWithHoles.weaken_sample, ``StmtWithHoles.weaken_assign,
   ``StmtWithHoles.weaken_call', ``StmtWithHoles.weaken_seq,
   ``StmtWithHoles.weaken_ifThenElse, ``StmtWithHoles.weaken_while,
   ``StmtWithHoles.weaken_applyLens,
  -- group 2: into l-values
   ``Lens.chainSetter_liftLens, ``Lens.chainSetter_liftLens_global,
   ``Lens.chainSetter_throwaway, ``Lens.chainSetter_toSetter,
   ``Lens.chainSetter_chainSetter, ``Lens.chainGetter_chainGetter,
  -- group 3: into expressions
   ``eval_chain_lens, ``eval_chain_getter,
   ``eval_mapScope_global_lens, ``eval_mapScope_global_getter]

/-- The one definition §6.2 unfolds. -/
def cleanUnfold : List Name := [``Lens.chainGetter]

/-- The simp context of §6.2: `cleanLemmas`, `cleanUnfold`, and nothing else. -/
def cleanContext : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for n in cleanLemmas do thms ← thms.addConst n
  for n in cleanUnfold do thms ← thms.addDeclToUnfold n
  -- every way `simp` could touch a `let` is switched off: `zeta`/`zetaDelta` (substituting),
  -- `zetaUnused` (dropping an unused binder — a variable a statement happens not to mention is
  -- still part of the scope), `zetaHave` (the `proc` macro's binders are `have`s) and
  -- `letToHave` (which would rewrite the telescope the delaborators read)
  Simp.mkContext
    (config := { zeta := false, zetaDelta := false, zetaUnused := false, zetaHave := false,
                 letToHave := false, decide := false, arith := false, failIfUnchanged := false })
    (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)

/-- **§6.2** — push `applyLens` / `weaken` / `chain*` inwards as far as the terms allow.  Never
fails; whatever does not match keeps its wrapper, which costs prettiness, never correctness. -/
def cleanStmt (stmt : Expr) : MetaM Simp.Result := do
  let (r, _) ← simp stmt (← cleanContext)
  return r

/-! ## §7 — taking the `let` telescope apart and putting it back

A variable's *name* lives in a `let` binder, its *identity* in the binder's value (a slot chain).
Cleaning cannot rewrite under an opaque `let`-bound name, so the telescope is zeta-reduced first
(`exposeStmt`, which records the names) and rebuilt afterwards at the new scope (`retelescope`,
which puts them back).  A `let` binding anything that is *not* a variable — a hole index, a user's
own abbreviation — is left alone, and references through it keep their `applyLens` wrapper: this
is the one place where the output is deliberately less pretty than it could be. -/

/-- The statement heads a traversal stops at. -/
def stmtHeads : Array Name :=
  #[``StmtWithHoles.skip, ``StmtWithHoles.sample, ``StmtWithHoles.call', ``StmtWithHoles.hole,
    ``StmtWithHoles.seq, ``StmtWithHoles.ifThenElse, ``StmtWithHoles.while,
    ``StmtWithHoles.assign, ``StmtWithHoles.applyLens, ``StmtWithHoles.weaken]

/-- Head reduction that keeps `let`s: beta, iota and projections only. -/
def whnfNoZeta (e : Expr) : MetaM Expr :=
  withConfig (fun c => { c with zeta := false, zetaDelta := false }) (whnfCore e)

/-- Expose a getter/setter position: the same, but also through structure *projection functions*
— a callee's `return_val` is one, and its telescope hides behind it.  Nothing else is unfolded,
so an l-value stays spelled `liftLens x`. -/
partial def openTerm (e : Expr) : MetaM Expr := do
  let e' ← whnfNoZeta e
  if e'.isLet then return e'
  let some n := e'.getAppFn.constName? | return e'
  unless (← getProjectionFnInfo? n).isSome do return e'
  match ← unfoldDefinition? e' with
  | some e'' => openTerm e''
  | none     => return e'

/-- Recognise the unfolding of `assign` and fold it back.  `assign x e` is a `def` over `sample`,
so a `whnf` at a statement position can step through it; this restores the surface form. -/
def foldAssign (e : Expr) : MetaM Expr := do
  unless e.isAppOfArity ``StmtWithHoles.sample 6 do return e
  let args := e.getAppArgs
  let g ← whnfNoZeta args[5]!
  unless g.isAppOfArity ``Getter.mk 3 do return e
  let some (_, body) ← pure (← lambdaBoundedTelescope g.getAppArgs[2]! 1 fun xs b =>
      pure (some (xs, b))) | return e
  unless body.isAppOfArity ``Pure.pure 4 do return e
  let inner := body.appArg!
  let ge ← lambdaBoundedTelescope g.getAppArgs[2]! 1 fun xs _ =>
    mkLambdaFVars xs (inner.instantiateRev xs) >>= fun f => mkAppM ``Getter.mk #[f]
  mkAppOptM ``StmtWithHoles.assign
    #[some args[3]!, some args[1]!, some args[2]!, some args[0]!, some args[4]!, some ge]

/-- Expose a statement position: reduce until a statement head (or a `let`) is visible, without
zeta-reducing and without paying the `assign` unfolding.

`heads` is which heads count as "a statement is visible".  The inliner passes `stmtHeads` plus
`StmtWithHoles.call`, whose callee is one sub-term: `whnf` steps through `call` to the `call'` it
is defined as, which spreads the callee over three arguments. -/
partial def openStmt (e : Expr) (heads : Array Name := stmtHeads) : MetaM Expr := do
  let e' ← whnfNoZeta e
  if e'.isLet then return e'
  if let some n := e'.getAppFn.constName? then
    if heads.contains n then return e'
  let e'' ← foldAssign (← unfoldStmt e')
  if e'' == e' then return e' else openStmt e'' heads

mutual

/-- §7, first half, at a statement position. -/
partial def exposeStmt (ref : IO.Ref VarTable) (e₀ : Expr) : MetaM Expr := do
  let e ← openStmt e₀
  match e with
  | .letE n ty val body _ =>
      match ← varLetInfo? val with
      | some (p, l, isP, k) =>
          ref.modify (·.push (p, l, isP, k, n))
          exposeStmt ref (body.instantiate1 val)
      | none => withLetDecl n ty val fun fv => do
          mkLetFVars #[fv] (← exposeStmt ref (body.instantiate1 fv)) (usedLetOnly := false)
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    -- rebuild in place: the implicit arguments are already right, only the sub-terms change
    let two (i j : Nat) (fi fj : Expr → MetaM Expr) : MetaM Expr := do
      let a ← fi args[i]!
      let b ← fj args[j]!
      return mkAppN fn ((args.set! i a).set! j b)
    match fn.constName? with
    | some ``StmtWithHoles.seq => two 3 4 (exposeStmt ref) (exposeStmt ref)
    | some ``StmtWithHoles.ifThenElse => do
        let c ← exposeTerm ref args[3]!
        let t ← exposeStmt ref args[4]!
        let f ← exposeStmt ref args[5]!
        return mkAppN fn (((args.set! 3 c).set! 4 t).set! 5 f)
    | some ``StmtWithHoles.while => two 3 4 (exposeTerm ref) (exposeStmt ref)
    | some ``StmtWithHoles.sample => two 4 5 (exposeTerm ref) (exposeTerm ref)
    | some ``StmtWithHoles.assign => two 4 5 (exposeTerm ref) (exposeTerm ref)
    | some ``StmtWithHoles.call' => two 4 8 (exposeTerm ref) (exposeTerm ref)
    | some ``StmtWithHoles.hole => two 5 6 (exposeTerm ref) (exposeTerm ref)
    | some ``StmtWithHoles.applyLens => do
        return mkAppN fn (args.set! 5 (← exposeStmt ref args[5]!))
    | some ``StmtWithHoles.weaken => do
        return mkAppN fn (args.set! 3 (← exposeStmt ref args[3]!))
    | _ => return e

/-- §7, first half, at a getter/setter position — a callee's `return_val` hides its telescope
behind a structure projection, which is what has to be seen through here. -/
partial def exposeTerm (ref : IO.Ref VarTable) (e₀ : Expr) : MetaM Expr := do
  if e₀.isAppOfArity ``Lens.chainGetter 5 || e₀.isAppOfArity ``Lens.chainSetter 5 then
    let args := e₀.getAppArgs
    return mkAppN e₀.getAppFn (args.set! 4 (← exposeTerm ref args[4]!))
  match ← openTerm e₀ with
  | .letE n ty val body _ =>
      match ← varLetInfo? val with
      | some (p, l, isP, k) =>
          ref.modify (·.push (p, l, isP, k, n))
          exposeTerm ref (body.instantiate1 val)
      | none => withLetDecl n ty val fun fv => do
          mkLetFVars #[fv] (← exposeTerm ref (body.instantiate1 fv)) (usedLetOnly := false)
  | e => return e

end

/-- Zeta-reduce the variable `let`s of a proof term, so that it matches a statement `exposeStmt`
has opened up.  (Both are zeta, hence definitional; the proof's type follows along.) -/
partial def zetaVarLets (e : Expr) : MetaM Expr := do
  match e with
  | .letE n ty val body _ =>
      if (← varLetInfo? val).isSome then zetaVarLets (body.instantiate1 val)
      else withLetDecl n ty val fun fv => do
        mkLetFVars #[fv] (← zetaVarLets (body.instantiate1 fv)) (usedLetOnly := false)
  | _ => return e

/-- Peel a `let` telescope, returning its binders (name, type, value) and the term underneath. -/
partial def peelLets (e : Expr) (acc : Array (Name × Expr × Expr) := #[]) :
    MetaM (Array (Name × Expr × Expr) × Expr) := do
  match e with
  | .letE n ty val body _ => peelLets (body.instantiate1 val) (acc.push (n, ty, val))
  | _ => return (acc, e)

/-- Put a `let` telescope in front of each of `targets`, abstracting the occurrences of every
binder's value with `kabstract` (so up to defeq, not just syntactically). -/
partial def rebindLets (binders : Array (Name × Expr × Expr)) (targets : Array Expr) :
    MetaM (Array Expr) :=
  go 0 targets
where
  /-- Bind `binders[i:]`, innermost first. -/
  go (i : Nat) (es : Array Expr) : MetaM (Array Expr) := do
    if h : i < binders.size then
      let (nm, ty, val) := binders[i]
      withLetDecl nm ty val fun fv => do
        let es ← es.mapM fun e => return (← kabstract e val).instantiate1 fv
        let es ← go (i + 1) es
        es.mapM fun e => mkLetFVars #[fv] e (usedLetOnly := false)
    else return es

/-- Pick a name for a variable: the one its old telescope gave it, `vₖ` if it had none, and with
`0`, `1`, … appended if that name is already taken (§3). -/
def freshVarName (used : Array Name) (given : Option Name) (fallback : Name) : Name :=
  let base := given.getD fallback
  if !used.contains base then base else
    Id.run do
      let mut i := 0
      while used.contains (base.appendAfter (toString i)) do i := i + 1
      return base.appendAfter (toString i)

/-- **§7** — rebuild the `let` telescope at the new scope, and re-abstract the proof with it.

The enclosing statement's own variables claim their names first, so that a collision renames the
*callee's* variable (`w`, `w0`, …) and leaves the caller's alone — the caller's names are the ones
anything outside the statement may still refer to. -/
def retelescope (inst P oldLocals newLocals : Expr) (vars : VarTable)
    (origin : Array (Expr × Expr × Bool × Nat)) (stmt proof : Expr) : MetaM (Expr × Expr) := do
  let paramTys ← listLitElems P
  let localEntries ← listLitElems newLocals
  let localTys ← localEntries.mapM fun e => do
    let w ← whnf e
    unless w.isAppOfArity ``Sigma.mk 4 do throwError "locals list is not literal:{indentExpr e}"
    pure w.getAppArgs[2]!
  let np := paramTys.length
  unless origin.size == np + localTys.length do
    throwError "§7: {origin.size} origins for {np} parameters and {localTys.length} locals"
  let scopeNew ← mkAppM ``ProcedureScope #[P, newLocals]
  let stateNew ← mkAppM ``ProcedureState #[scopeNew]
  -- pass 1: the enclosing scope's own variables keep their names unconditionally
  let isOwn (p l : Expr) : MetaM Bool := do
    pure ((← isDefEq p P) && (← isDefEq l oldLocals))
  let mut names : Array (Option Name) := .replicate origin.size none
  let mut used : Array Name := #[]
  for i in [0:origin.size] do
    let (p, l, isP, k) := origin[i]!
    if ← isOwn p l then
      if let some n ← vars.find? p l isP k then
        names := names.set! i (some n)
        used := used.push n
  -- pass 2: everything else, renamed on collision
  for i in [0:origin.size] do
    if names[i]!.isNone then
      let (p, l, isP, k) := origin[i]!
      let fallback := (if i < np then `p else `v).appendIndexAfter i
      let n := freshVarName used (← vars.find? p l isP k) fallback
      names := names.set! i (some n)
      used := used.push n
  -- name, content type, value
  let mut binders : Array (Name × Expr × Expr) := #[]
  for i in [0:origin.size] do
    let isParamSlot := i < np
    let a := if isParamSlot then paramTys[i]! else localTys[i - np]!
    let name := names[i]!.getD (Name.appendIndexAfter `v i)
    let slot ← if isParamSlot then mkSlotLens paramTys i else mkSlotLens localTys (i - np)
    let val ←
      if isParamSlot then
        mkAppOptM ``Lens.intoParams #[some inst, some a, some P, some newLocals, some slot]
      else
        mkAppOptM ``Lens.intoLocalVars #[some inst, some a, some P, some newLocals, some slot]
    binders := binders.push (name, a, val)
  let typed ← binders.mapM fun (nm, a, val) => do
    pure (nm, ← mkAppM ``Lens #[a, stateNew], val)
  let #[stmt', proof'] ← rebindLets typed #[stmt, proof] | throwError "§7: lost a term"
  return (stmt', proof')

/-! ## §6.3 — `flattenSeq` -/

/-- Is this `skip`? -/
def isSkip (e : Expr) : Bool := e.isAppOf ``StmtWithHoles.skip

/-- `a.Equiv a`. -/
def mkEquivRefl (s : Expr) : MetaM Expr := mkAppM ``StmtWithHoles.Equiv.refl #[s]

/-- Concatenate two already right-nested sequences, dropping `skip`s: returns the result together
with a proof of `(a.seq b).Equiv result`. -/
partial def concatSeq (a b : Expr) : MetaM (Expr × Expr) := do
  if isSkip a then return (b, ← mkAppM ``StmtWithHoles.Equiv.skip_seq #[b])
  if isSkip b then return (a, ← mkAppM ``StmtWithHoles.Equiv.seq_skip #[a])
  if a.isAppOfArity ``StmtWithHoles.seq 5 then
    let x := a.getAppArgs[3]!
    let y := a.getAppArgs[4]!
    let (r, p) ← concatSeq y b
    let p₁ ← mkAppM ``StmtWithHoles.Equiv.seq_assoc #[x, y, b]
    let p₂ ← mkAppM ``StmtWithHoles.EquivInLens.seq #[← mkEquivRefl x, p]
    return (← mkAppM ``StmtWithHoles.seq #[x, r],
            ← mkAppM ``StmtWithHoles.Equiv.trans #[p₁, p₂])
  let s ← mkAppM ``StmtWithHoles.seq #[a, b]
  return (s, ← mkEquivRefl s)

/-- **§6.3** — re-associate `seq` to the right and drop `skip`s, returning the result and a proof
of `‹input›.Equiv result`.  Never fails; `if`s are not otherwise touched. -/
partial def flattenSeq (s₀ : Expr) : MetaM (Expr × Expr) := do
  let s ← openStmt s₀
  match s with
  | .letE n ty val body _ =>
      withLetDecl n ty val fun fv => do
        let (r, p) ← flattenSeq (body.instantiate1 fv)
        return (← mkLetFVars #[fv] r (usedLetOnly := false),
                ← mkLetFVars #[fv] p (usedLetOnly := false))
  | _ =>
    let args := s.getAppArgs
    match s.getAppFn.constName? with
    | some ``StmtWithHoles.seq =>
        let (a, pa) ← flattenSeq args[3]!
        let (b, pb) ← flattenSeq args[4]!
        let (r, p) ← concatSeq a b
        let pseq ← mkAppM ``StmtWithHoles.EquivInLens.seq #[pa, pb]
        return (r, ← mkAppM ``StmtWithHoles.Equiv.trans #[pseq, p])
    | some ``StmtWithHoles.ifThenElse =>
        let (t, pt) ← flattenSeq args[4]!
        let (e, pe) ← flattenSeq args[5]!
        return (← mkAppM ``StmtWithHoles.ifThenElse #[args[3]!, t, e],
                ← mkAppM ``StmtWithHoles.Equiv.ifThenElse #[args[3]!, pt, pe])
    | some ``StmtWithHoles.while =>
        let (b, pb) ← flattenSeq args[4]!
        return (← mkAppM ``StmtWithHoles.while #[args[3]!, b],
                ← mkAppM ``StmtWithHoles.Equiv.while #[args[3]!, pb])
    | _ => return (s, ← mkEquivRefl s)

/-! ## §6.4 / §6.5 — composition and the fixed point -/

/-- **§6.4** — §6.1, then §6.2, then §6.3, with the proofs composed and the telescope of §7 put
back.  The only step that can fail is §6.1. -/
def flattenCallCleaned (n : Nat) (stmt : Expr) : MetaM FlattenStep := do
  let step ← flattenCall n stmt
  -- §7 (take apart) and §6.2
  let ref ← IO.mkRef (#[] : VarTable)
  let exposed ← exposeStmt ref step.stmt
  let vars ← ref.get
  let r ← inStep "the cleaning pass (§6.2)" <| cleanStmt exposed
  let proofZ ← zetaVarLets step.proof
  -- transport the proof of §6.1 along the cleaning equation
  let scopeNew ← mkAppM ``ProcedureScope #[step.params, step.newLocals]
  let L₁ := (← whnf (← inferType stmt)).getAppArgs[2]!
  let motive ← withLocalDeclD `s (← mkAppM ``StmtWithHoles #[step.hCtx, scopeNew]) fun s => do
    mkLambdaFVars #[s] (← mkAppOptM ``StmtWithHoles.EquivInLens
      #[some step.inst, some step.hCtx, some L₁, some scopeNew, some stmt, some s,
        some step.trafo])
  let proofC ← match r.proof? with
    | some h => mkEqNDRec motive proofZ h
    | none   => pure proofZ
  -- §6.3
  let (final, pSeq) ← inStep "the sequence pass (§6.3)" <| flattenSeq r.expr
  let proofF ← mkAppM ``StmtWithHoles.EquivInLens.trans #[proofC, pSeq]
  -- the composite lens is `Lens.id.chain trafo`, which *is* `trafo`
  let proofF ← mkExpectedTypeHint proofF (← mkAppOptM ``StmtWithHoles.EquivInLens
    #[some step.inst, some step.hCtx, some L₁, some scopeNew, some stmt, some final,
      some step.trafo])
  -- §7 (put back)
  let (stmt', proof') ← inStep "the re-telescoping (§7)" <|
    retelescope step.inst step.params step.oldLocals step.newLocals vars step.origin final proofF
  return { step with stmt := stmt', proof := proof' }

/-- The result of the whole pass (§9). -/
structure FlatteningResult extends FlattenStep where
  /-- How many calls were flattened; nonzero, or we threw. -/
  count : Nat

/-- Flatten the first call that *can* be flattened, or report that there is none. -/
def flattenSomeCall (stmt : Expr) : MetaM (Option FlattenStep × MessageData) := do
  let total ← countCallSites stmt
  let mut why : MessageData := m!"the statement contains no call"
  for i in [0:total] do
    try
      return (some (← flattenCallCleaned i stmt), m!"")
    catch e =>
      why := e.toMessageData
  return (none, why)

/-- **§6.5** — flatten calls until none is left.  Throws if there was nothing to flatten at all;
each round removes one `call` node, so the loop terminates. -/
def flattenProcedureCalls (stmt : Expr) : MetaM FlatteningResult := do
  let (first?, why) ← flattenSomeCall stmt
  let some first := first?
    | throwError "nothing to flatten: {why}"
  let mut acc := first
  let mut count := 1
  repeat
    let (next?, _) ← flattenSomeCall acc.stmt
    let some next := next? | break
    let proof ← mkAppM ``StmtWithHoles.EquivInLens.trans #[acc.proof, next.proof]
    let trafo ← mkAppM ``Lens.chain #[next.trafo, acc.trafo]
    acc := { next with proof, trafo }
    count := count + 1
  return { acc with count }

/-! ## §8 — the procedure wrapper

Bookkeeping only: run §6.5 on the body, put the new locals into the `locals` field, re-target
`return_val` along the composite lens, and re-bind it with *the same* telescope the body got —
`delabProc` peels both fields in step and requires the two name lists to agree. -/

/-- **§8** — run a pass on the body of a hole-free procedure and put the procedure back together:
the new locals into the `locals` field, the `return_val` re-targeted along the pass's lens, and
`procedureDenotation_congr` for the proof.  Whatever else the pass reports (`α`) is passed on.

Every user of §8 goes through this — §6.5 below, and §11's `inlineInProcedure`. -/
def inProcedure {α : Type} (p : Expr) (pass : Expr → MetaM (FlattenStep × α)) :
    MetaM (Expr × Expr × α) := do
  let ty ← whnf (← inferType p)
  unless ty.isAppOfArity ``ProcedureWithHoles 3 do
    throwError "not a procedure:{indentExpr ty}"
  let inst := ty.getAppArgs[0]!
  let hCtx ← whnf ty.getAppArgs[1]!
  unless hCtx.isAppOf ``HoleSigs.empty do
    throwError "§8 is stated for hole-free procedures; this one still has holes:{indentExpr hCtx}"
  let sig := ty.getAppArgs[2]!
  let pW ← whnf p
  unless pW.isAppOfArity ``ProcedureWithHoles.mk 6 do
    throwError "the procedure is not spelled out:{indentExpr p}"
  let locals := pW.getAppArgs[3]!
  let body := pW.getAppArgs[4]!
  let retVal := pW.getAppArgs[5]!
  let (res, a) ← pass body
  -- the return value travels along the composite lens, is cleaned, and is re-bound with the
  -- body's telescope so that the two `proc` fields agree on the variable names
  let ref ← IO.mkRef (#[] : VarTable)
  let retWide ← mkAppM ``Lens.chainGetter #[res.trafo, retVal]
  let retClean := (← cleanStmt (← exposeTerm ref retWide)).expr
  let (binders, _) ← peelLets res.stmt
  let #[retVal'] ← rebindLets binders #[retClean] | throwError "§8: lost the return value"
  let proc' ← mkAppOptM ``ProcedureWithHoles.mk
    #[some inst, some hCtx, some sig, some res.newLocals, some res.stmt, some retVal']
  let proof ← mkAppOptM ``procedureDenotation_congr
    #[some inst, some sig, some locals, some res.newLocals, some res.trafo,
      some body, some res.stmt, some retVal, some retVal', some res.proof]
  let proof ← inStep "the entry-state condition" <| appRfl proof   -- hinit
  let proof ← inStep "the return-value condition" <| appRfl proof  -- hret
  let proof ← inStep "the global-state condition" <| appRfl proof  -- hglob
  return (proc', proof, a)

/-- **§8** — flatten the calls of a hole-free procedure.  Returns the new procedure, a proof that
it has the same `procedureDenotation`, and the number of calls flattened. -/
def flattenProcedure (p : Expr) : MetaM (Expr × Expr × Nat) :=
  inProcedure p fun body => do
    let res ← flattenProcedureCalls body
    return (res.toFlattenStep, res.count)

/-! ## §11 — unfolding a module expression to a procedure

A call site may name its callee through *modules*: `call (Module.Proc.procedure (T.f (Module.app
M A))) …`.  §6 cannot flatten that — §2 wants the callee spelled out at the call site — so this
section provides the step before it: evaluate such a term to the procedure it denotes.

### What it evaluates, and how far

The term is built from `Module.app`, the constants the `module` and `moduletype` commands emit,
`Module.pair`/`Module.fst`/`Module.snd`, `Module.proc` and `Module.Proc.procedure`.  Two shapes
matter (`ModuleSyntax.lean` documents what each command declares):

* `T.f stuff` for a `moduletype` accessor `T.f` — the argument is evaluated **only as far as the
  accessor needs**: to a record, i.e. a `T.mk` or a `Module.pair`, and no further.  What comes
  out is the field, which is then evaluated in turn;
* `M.f stuff` for a `module`-declared procedure `M.f`, which for a module with no module
  parameters is a straight substitution of the definition.

The steps are the generated lemmas, each applied **at the head of the term and nowhere else**:
`M.apply_simp` (applying a module to its parameters, giving the record of its procedures),
`T.f.mk_simp` (reading a field off that record), `Module.fst_pair`/`snd_pair` (the same for the
anonymous record a `module` without a module type builds), `M.f.apply_simp` (applying a procedure
of a module to the parameters it uses, giving `Module.proc (M.f.procedure.instantiate ‹callees›)`)
and finally `M.f.procedure.apply_simp` (the body as written, with the hole calls turned back into
calls of those callees).  Nothing is rewritten *inside* the body: the callees it calls are left
exactly as the module wrote them.

Everything is head-position, so there is no simp set here and no risk of a lemma firing somewhere
unintended; what the pass cannot step is an error, not a silent stop.  In particular, a module
that is not concrete — `T.f (Module.app M A)` for a `M` that is a variable or an axiom — has no
body to find, and `unfoldProcedure` fails.

### And back into a statement

`inlineProcedureRaw n` rewrites call site `n` of a statement with `unfoldProcedure`, so that its
callee becomes literal; `inlineProcedure n` does that and then flattens the site with
`flattenCallCleaned n` — which is what "inlining" means here.  Call sites are numbered by
`countCallSites`, which counts `call`, `call'` *and* `hole` nodes: all three are calls as far as
someone reading the statement is concerned, and numbering them together makes the numbers
independent of which sites happen to be flattenable.  A hole has no callee, so both functions
fail on one. -/

/-- One rewrite with a named equation, at the head of `e` and nowhere else: instantiate the
lemma's binders with metavariables, unify its left-hand side with `e`, and hand back the
instantiated right-hand side together with the instantiated lemma as its proof.

`none` if the lemma does not exist (the callers name lemmas that a `module`/`moduletype`
declaration *may* have emitted), if it does not match, or if matching leaves anything open —
whatever comes back is a closed term. -/
def rewriteHead? (lem : Name) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  unless (← getEnv).contains lem do return none
  -- the whole attempt is speculative: a failed match must not leave assignments behind, and the
  -- results are checked to be metavariable-free before the state is dropped
  withoutModifyingState do
    let c ← mkConstWithFreshMVarLevels lem
    let (mvars, bis, body) ← forallMetaTelescope (← inferType c)
    let some (_, lhs, _) := body.eq? | return none
    unless ← isDefEq lhs e do return none
    -- an instance argument the unification did not pin down (there is none in practice: every
    -- generated lemma mentions its `ProgramSpec` in its statement)
    for (m, bi) in mvars.zip bis do
      if bi.isInstImplicit && !(← m.mvarId!.isAssigned) then
        let .some inst ← trySynthInstance (← inferType m) | return none
        unless ← isDefEq m inst do return none
    let proof ← instantiateMVars (mkAppN c mvars)
    let rhs ← instantiateMVars (← inferType proof)
    let some (_, _, rhs) := rhs.eq? | return none
    if proof.hasExprMVar || proof.hasLevelMVar || rhs.hasExprMVar || rhs.hasLevelMVar then
      return none
    return some (rhs, proof)

/-- Replace argument `i` of an application. -/
def setArg (e : Expr) (i : Nat) (x : Expr) : Expr :=
  mkAppN e.getAppFn (e.getAppArgs.set! i x)

/-- `congrArg` at argument `i` of an application: from `h : ‹arg i› = x` to `e = e[arg i := x]`. -/
def congrArgAt (e : Expr) (i : Nat) (h : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  withLocalDeclD `x (← inferType args[i]!) fun x => do
    mkCongrArg (← mkLambdaFVars #[x] (setArg e i x)) h

/-- Lift a rewrite of argument `i` to the whole application. -/
def liftResultAt (e : Expr) (i : Nat) (r : Simp.Result) : MetaM Simp.Result := do
  match r.proof? with
  | none   => return { expr := setArg e i r.expr }
  | some h => return { expr := setArg e i r.expr, proof? := some (← congrArgAt e i h) }

/-- Peel the `let` telescope off a procedure and look at what is underneath. -/
partial def procCore (e : Expr) : MetaM Expr := do
  match ← whnfNoZeta e with
  | .letE _ _ v b _ => procCore (b.instantiate1 v)
  | e' => return e'

/-- Is this a procedure written out — a `ProcedureWithHoles.mk`, possibly under the `let`
telescope that carries its variable names? -/
def isProcLiteral (e : Expr) : MetaM Bool :=
  return (← procCore e).isAppOfArity ``ProcedureWithHoles.mk 6

/-- `‹literal tuple›.lookup ‹literal index›`, computed.  This is what the three
`HoleSigs.Instantiation.lookup_*` lemmas say, and each of them is `rfl`, so the result is
*definitionally* the term it replaces — no proof is needed for the step, only a re-typing of the
proof that mentions it. -/
partial def lookupComponent? (e : Expr) : Option Expr := do
  guard (e.isAppOf ``HoleSigs.Instantiation.lookup)
  let args := e.getAppArgs
  guard (args.size ≥ 2)
  go args[args.size - 2]! args[args.size - 1]!
where
  /-- Walk the index, taking the tuple apart as it goes.  A one-hole instantiation is its
  procedure rather than a pair, which is the `tuple` that is not a `Prod.mk`. -/
  go (tuple idx : Expr) : Option Expr :=
    if idx.isAppOf ``HoleIndex.succ then
      if tuple.isAppOfArity ``Prod.mk 4 then go tuple.appArg! idx.appArg! else none
    else if idx.isAppOf ``HoleIndex.zero then
      some (if tuple.isAppOfArity ``Prod.mk 4 then tuple.getAppArgs[2]! else tuple)
    else none

/-- Compute away every `lookup` of a literal instantiation. -/
def reduceLookups (e : Expr) : Expr :=
  e.replace lookupComponent?

/-- Reduce a projection function applied to a record — the shape a `mk_simp` leaves behind
(`T.Structure.f {f := …, …}`).  Anything else is returned unchanged. -/
def reduceStructProj (e : Expr) : MetaM Expr := do
  let some n := e.getAppFn.constName? | return e
  let some _ ← getProjectionFnInfo? n | return e
  let some e' ← unfoldDefinition? e | return e
  let e'' ← whnfNoZeta e'
  -- only accept it if the projection really went away
  if e''.isProj || e''.getAppFn.constName? == some n then return e else return e''

/-- Spell a procedure out: `M.f.procedure.instantiate ‹callees›` becomes the body as it was
written — with each hole call turned back into a call of the callee it was made from — by the
`M.f.procedure.apply_simp` lemma the `module` command emits; a procedure named by a constant is
unfolded, its definition *being* the body.  Fails when no body can be reached. -/
partial def spellOutProcedure (e : Expr) (fuel : Nat := 32) : MetaM Simp.Result := do
  if ← isProcLiteral e then return { expr := e }
  if fuel == 0 then throwError "gave up looking for a procedure body in{indentExpr e}"
  if e.isAppOf ``ProcedureWithHoles.instantiate then
    let args := e.getAppArgs
    let p := args[args.size - 2]!
    let some c := p.getAppFn.constName?
      | throwError "no procedure body: the instantiated procedure is not a constant{indentExpr p}"
    let some (rhs, h) ← rewriteHead? (c ++ `apply_simp) e
      | throwError "no procedure body: `{c ++ `apply_simp}` does not apply to{indentExpr e}"
    -- the lemma's right-hand side calls `holeArgs.lookup ‹index›`; at a literal instantiation
    -- those are the callees themselves, definitionally
    let rhs' := reduceLookups rhs
    let h ← if rhs' == rhs then pure h else mkExpectedTypeHint h (← mkEq e rhs')
    let r ← spellOutProcedure rhs' (fuel - 1)
    ({ expr := rhs', proof? := some h } : Simp.Result).mkEqTrans r
  else if let some v ← unfoldDefinition? e then
    -- `v` is `e` by definition, so the step needs no proof of its own
    ({ expr := v } : Simp.Result).mkEqTrans (← spellOutProcedure v (fuel - 1))
  else
    throwError "no concrete procedure body:{indentExpr e}"

/-- The function argument of a `Module.app` — the last argument is what it is applied *to*. -/
def moduleAppFn? (e : Expr) : Option Nat :=
  if e.isAppOf ``Module.app && e.getAppNumArgs ≥ 2 then some (e.getAppNumArgs - 2) else none

/-- The head of a `Module.app` spine: `Module.app (… (Module.app h x₁) …) xₖ` ↦ `h`. -/
partial def moduleAppHead (e : Expr) : Expr :=
  match moduleAppFn? e with
  | some i => moduleAppHead e.getAppArgs[i]!
  | none   => e

/-- The lemma that reads a projection off a `Module.pair` — the anonymous record a `module`
without a module type builds. -/
def pairLemma? : Name → Option Name
  | ``Module.fst  => some ``Module.fst_pair
  | ``Module.snd  => some ``Module.snd_pair
  | ``Module.fst' => some ``Module.fst_pair'
  | ``Module.snd' => some ``Module.snd_pair'
  | _ => none

/-- Is this constant an accessor of a `moduletype` declaration?  It is exactly when the command
emitted the `mk_simp` lemma that reads the field back off a built module. -/
def isAccessor (c : Name) : MetaM Bool :=
  return (← getEnv).contains (c ++ `mk_simp)

/-- One step of head evaluation of a module expression: applying a module or one of its procedures
to its parameters, reading a field off a record, or — when none of those applies yet — the same
one step in the position that has to be evaluated first (the function of a `Module.app`, the
module a projection is taken of). -/
partial def moduleStep? (e : Expr) : MetaM (Option Simp.Result) := do
  let some c := e.getAppFn.constName? | return none
  let args := e.getAppArgs
  -- (1) applying a `module`-declared module, or one of its procedures, to its parameters
  if let some hc := (moduleAppHead e).getAppFn.constName? then
    if let some (rhs, h) ← rewriteHead? (hc ++ `apply_simp) e then
      return some { expr := rhs, proof? := some h }
  -- (2) a `moduletype` accessor of a module built by `mk`
  if let some (rhs, h) ← rewriteHead? (c ++ `mk_simp) e then
    return some { expr := ← reduceStructProj rhs, proof? := some h }
  -- (3) a projection out of a `Module.pair`
  if let some lem := pairLemma? c then
    if let some (rhs, h) ← rewriteHead? lem e then
      return some { expr := rhs, proof? := some h }
  -- (4) not yet: evaluate the position that has to come first, one step
  let i? : Option Nat ←
    match moduleAppFn? e with                                      -- its function
    | some i => pure (some i)
    | none =>
      if (pairLemma? c).isSome || (← isAccessor c) then pure (some (args.size - 1))
      else pure none
  let some i := i? | return none
  let some r ← moduleStep? args[i]! | return none
  return some (← liftResultAt e i r)

/-- Evaluate a module expression until its head is `Module.proc`, then spell that procedure out.
Fails as soon as no step applies — which is exactly the case where the term has no concrete
procedure body. -/
partial def unfoldModuleExpr (e : Expr) (fuel : Nat := 64) : MetaM Simp.Result := do
  if e.isAppOf ``Module.proc then
    let i := e.getAppNumArgs - 1
    return ← liftResultAt e i (← spellOutProcedure e.appArg!)
  if fuel == 0 then throwError "gave up unfolding{indentExpr e}"
  let some step ← moduleStep? e
    | throwError "no concrete procedure body: nothing to unfold at the head of{indentExpr e}"
  step.mkEqTrans (← unfoldModuleExpr step.expr (fuel - 1))

/-- **§11** — unfold a term built from modules that evaluates to a procedure, and hand back the
result with a proof that it equals the term.

Accepts both levels: a module term of type `Module.Proc sig`, whose result is
`Module.proc ‹procedure›`, and a procedure term — `Module.Proc.procedure ‹module›`, the shape a
call site carries — whose result is the procedure itself.  Fails if no concrete body can be
found.

This is the pass itself; `unfoldProcedure` wraps it. -/
def unfoldProcedureCore (e : Expr) : MetaM Simp.Result := do
  let ty ← whnf (← inferType e)
  if ty.isAppOfArity ``ProcedureWithHoles 3 then
    unless e.isAppOf ``Module.Proc.procedure do
      -- a procedure named some other way: nothing module-ish to evaluate, only a body to reach
      return ← spellOutProcedure e
    let i := e.getAppNumArgs - 1
    let r₁ ← liftResultAt e i (← unfoldModuleExpr e.appArg!)
    let some (rhs, h) ← rewriteHead? ``Module.procedure_proc' r₁.expr
      | throwError "unexpected: the module did not unfold to a `Module.proc`{indentExpr r₁.expr}"
    let r ← r₁.mkEqTrans { expr := rhs, proof? := some h }
    r.mkEqTrans (← spellOutProcedure rhs)
  else if ty.isAppOf ``GaudisCrypt.Module then
    unfoldModuleExpr e
  else
    throwError "not a module or a procedure:{indentExpr (← inferType e)}"

/-- **§11** — `unfoldProcedureCore`, with the proof re-typed to say what it proves.

A step that unfolds a *definition* carries no proof of its own — `none` is `rfl` — so what the
composed proof states can end at a term that is only definitionally the result.  Both are
correct; this is the one a caller (and a `#check`) would rather read. -/
def unfoldProcedure (e : Expr) : MetaM Simp.Result := do
  let r ← unfoldProcedureCore e
  let some h := r.proof? | return r
  return { r with proof? := some (← mkExpectedTypeHint h (← mkEq e r.expr)) }

/-- Rewrite call site `idx` of a statement by unfolding its callee, and prove that the result
*equals* the statement.  The traversal is the one that numbers the call sites, with the single
difference that it stops at a `StmtWithHoles.call`: `whnf` would step through it to the `call'` it
is defined as, which spreads the callee over three arguments instead of one. -/
partial def rewriteCalleeAt (idx : Nat) (e₀ : Expr) : MetaM Simp.Result := do
  let e ← openStmt e₀ (stmtHeads.push ``StmtWithHoles.call)
  if isCallSite e then
    unless idx == 0 do throwError "there is no call site number {idx} here:{indentExpr e}"
    match e.getAppFn.constName? with
    | some ``StmtWithHoles.call =>
        let i := e.getAppNumArgs - 2
        liftResultAt e i (← unfoldProcedure e.getAppArgs[i]!)
    | some ``StmtWithHoles.call' =>
        throwError "this call site has no callee to unfold: its callee is already spelled out"
    | _ => throwError "this call site is a hole: it has no callee to unfold"
  else match e with
  | .letE n ty val body _ =>
      withLetDecl n ty val fun fv => do
        let r ← rewriteCalleeAt idx (body.instantiate1 fv)
        let expr ← mkLetFVars #[fv] r.expr (usedLetOnly := false)
        match r.proof? with
        | none => return { expr }
        | some h =>
            -- `let x := v; (a = b)` and `(let x := v; a) = (let x := v; b)` differ by zeta
            let h ← mkLetFVars #[fv] h (usedLetOnly := false)
            return { expr, proof? := some (← mkExpectedTypeHint h (← mkEq e expr)) }
  | _ =>
    let args := e.getAppArgs
    let one (i : Nat) : MetaM Simp.Result := do
      liftResultAt e i (← rewriteCalleeAt idx args[i]!)
    let two (i j : Nat) : MetaM Simp.Result := do
      let ni ← countCallSites args[i]!
      if idx < ni then one i
      else liftResultAt e j (← rewriteCalleeAt (idx - ni) args[j]!)
    match e.getAppFn.constName? with
    | some ``StmtWithHoles.seq => two 3 4
    | some ``StmtWithHoles.ifThenElse => two 4 5
    | some ``StmtWithHoles.while => one 4
    | _ => throwError "no call site here:{indentExpr e}"

/-- **§11** — unfold the callee of call site `n`, leaving the call itself alone.  The proof is an
equation: the statement is rewritten, not re-targeted. -/
def inlineProcedureRaw (n : Nat) (stmt : Expr) : MetaM Simp.Result := do
  let total ← countCallSites stmt
  if n ≥ total then
    throwError "there is no call site number {n}: the statement has {total}"
  let r ← rewriteCalleeAt n stmt
  let some h := r.proof? | return r
  return { r with proof? := some (← mkExpectedTypeHint h (← mkEq stmt r.expr)) }

/-- **§11** — inline call site `n`: unfold its callee (`inlineProcedureRaw`), then flatten the
call (`flattenCallCleaned`).  The two proofs compose: the first is an equation, which transports
the second's `EquivInLens` back to the statement it started from. -/
def inlineProcedure (n : Nat) (stmt : Expr) : MetaM FlattenStep := do
  let r ← inlineProcedureRaw n stmt
  let step ← flattenCallCleaned n r.expr
  let some h := r.proof? | return step
  let scopeNew ← mkAppM ``ProcedureScope #[step.params, step.newLocals]
  let L₁ := (← whnf (← inferType stmt)).getAppArgs[2]!
  let motive ← withLocalDeclD `s (← mkAppM ``StmtWithHoles #[step.hCtx, L₁]) fun s => do
    mkLambdaFVars #[s] (← mkAppOptM ``StmtWithHoles.EquivInLens
      #[some step.inst, some step.hCtx, some L₁, some scopeNew, some s, some step.stmt,
        some step.trafo])
  return { step with proof := ← mkEqNDRec motive step.proof (← mkEqSymm h) }

/-- **§11** — `inlineProcedure` at the procedure level: inline call site `n` of the body of a
hole-free procedure that is spelled out, and hand back the new procedure together with a proof
that it has the same `procedureDenotation` (§8).

`proc (…) { xxx; call bla; yyy }` becomes `proc (…) { xxx; ‹the body of bla›; yyy }`, with the
callee's locals added to the procedure's own (renamed where they collide) and its result stored
where the call stored it. -/
def inlineInProcedure (n : Nat) (p : Expr) : MetaM (Expr × Expr) := do
  let (p', proof, _) ← inProcedure p fun body => return (← inlineProcedure n body, ())
  return (p', proof)

end Flatten

end GaudisCrypt
