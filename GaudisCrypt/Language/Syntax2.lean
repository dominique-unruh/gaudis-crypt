import GaudisCrypt.Language.Programs
import GaudisCrypt.Language.Modules

open GaudisCrypt

/-!
# Concrete syntax for programs, procedures, and module types

Surface syntax for the imperative probabilistic language (`StmtWithHoles` /
`ProcedureWithHoles` from `GaudisCrypt`).  The user-facing notations are
summarised below; see `syntax-ideas.md` for design notes.

## Expressions — `GaudiExpr[ e ]`

Wraps a Lean expression `e` as a program expression.  Inside, the `$` sigil reads program
variables:
* `$x`   — the value of program variable / lens `x`;
* `$(e)` — the value of an arbitrary lens-valued term `e`.

e.g. `GaudiExpr[ $a + $b * 2 ]`.  Every expression position in a statement is already an
`GaudiExpr`, so `$` may be used directly there.

## Statements / programs — `GaudiProg[ … ]`

A `;`-terminated sequence of statements.  The statement forms are:
* `skip;`
* `x <- e;`                       — assignment;
* `a, b <- e;`  /  `(a, b) <- e;` — tuple assignment (the parentheses are optional);
* `x <$ e;`                       — sample `x` from distribution `e`;
* `x <- call p (e₁, …, eₙ);`      — call procedure `p`, storing the result in `x`;
* `call p (e₁, …, eₙ);`           — call `p`, discarding the result;
* `if (e) { … } else { … }`       — the `else` branch is optional;
* `while (e) { … }`
* `{ … }`                         — a nested block.

The argument list `( … )` of a `call` is always required (write `()` for no arguments).

Example (`a b c : Lens Nat State`, `inc : Procedure …`):
```
GaudiProg[
  a <- $a + 1;
  b, c <- ($a, $a * 2);
  if ($a == 0) { a <- 1; } else { skip; }
  while ($b == 0) { b <- $b + 1; }
  a <- call inc ($a);
]
```

## Procedures — `proc (…) [uses (…)] [: R] { … }`

A procedure *term*:
```
proc (x : T, y : U) uses (A : (Nat) → Bool, B : (Bool) → Nat) : R {
  var u : V, w : W;     -- zero or more `var …;` lines of local variables
  <statements>
  return e
}
```
* parameters `(x : T, …)` (possibly none);
* an optional `uses (…)` clause declaring *holes* (abstract sub-procedures), each written
  `name : (T₁, …, Tₙ) → R`.  Inside the body a hole is invoked with the ordinary
  `call A (…)` syntax — `A` resolves to a hole when it is one of the declared names, and to
  a concrete procedure otherwise;
* an optional return type `: R` (inferred from `return e` when omitted);
* local variables via one or more `var name : T, …;` lines;
* a body of statements ending in `return e`.

## Procedure types and signatures

* `proctype (T, U, …) -> W`                    — the type of a closed procedure;
* `proctype (T, …) -> W uses ((T₁,…) → R, …)`   — the type of a procedure with holes;
* `procsig (T, U, …) -> W`                      — the bare `ProcedureSignature`.

`->` is used (rather than `:`) so these nest inside type ascriptions without extra
parentheses; they also pretty-print back into this form.

e.g. `proctype (Nat, Bool) -> Nat`, `proctype (Nat) -> Nat uses ((Nat) → Bool, (Bool) → Nat)`,
`procsig (Nat, Bool) -> Nat`.  Note `Procedure (procsig (Nat) -> Nat) = proctype (Nat) -> Nat`.

## Module types — `moduletype Name { … }`

A top-level command declaring a record-like module type, e.g.:
```
moduletype TwoProcs {
  proc enc (Nat, Nat) -> Bool;
  module aux : ModuleTypeRep.arr (ModuleTypeRep.proc (procsig (Nat) -> Nat)) ModuleTypeRep.unit;
}
```
where each field's type is a `ModuleTypeRep`.  A field may also be written `proc fᵢ (A₁, …) -> R;` as
shorthand for `module fᵢ : ModuleTypeRep.proc (procsig (A₁, …) -> R);`.  It generates `Name`
(the corresponding `Module`), a record `Name.Structure` with fields `fᵢ : Module Tᵢ`,
accessors `Name.fᵢ`, a constructor `Name.mk`, a destructor `Name.structure`, and round-trip
`@[simp]` lemmas relating them.
-/

namespace GaudisCrypt

open Lean

variable [ProgramSpec]

/-! ## Ambient current state + variable evaluation

An expression of value type `T` living in a statement with local-state `S` is a
`Getter T (State × S)`.  Inside the body we make the current state available via the
typeclass `CurrentState S`, so a program variable `x` (a lens/getter) can be read as
a plain value with `eval x`.  `eval` accepts both global variables (into `State`)
and full-current-state variables (into `State × S`); dispatch is on the concrete
type of the argument (see `Evaluatable`). -/

/-- The ambient current state `State × S`.  The local-state type `S` is an
`outParam`: `[CurrentState S]` resolves by reading off the ambient state's type, so
`S` need not be known up front — this is what lets a *global* variable, whose type
says nothing about `S`, still be evaluated. -/
class CurrentState (S : outParam Type) where
  state : ProcedureState S

/-- Anything that can be read to a value `T` in the ambient `CurrentState S`:
program variables (lenses/getters into `State`, or into the full `ProcedureState S`), and
anything users later add instances for.  Dispatch is on the concrete type `X` of
the argument, so resolution is never stuck on a metavariable. -/
class Evaluatable (S : Type) (X : Type) (T : outParam Type) where
  eval : ProcedureState S → X → T

/-- User-facing variable read, with `S` implicit (inferred from the variable's
container in the full case, from the ambient `CurrentState` in the global case).
Pass `(S := …)` to force a particular state. -/
def eval {S X T} [Evaluatable S X T] [cs : CurrentState S] (x : X) : T :=
  Evaluatable.eval cs.state x

/-- The four container shapes, dispatched directly on the argument type.  (No
`Lens → Getter` forwarder: it would overlap these, so we spell out all four.) -/
instance : Evaluatable S (Getter T State) T where
  eval cs x := x.get cs.global
instance : Evaluatable S (Getter T (ProcedureState S)) T where
  eval cs x := x.get cs
-- TODO: Needed? (We have Lens->Setter coercion)
instance : Evaluatable S (Lens T State) T where
  eval cs x := x.get cs.global
-- TODO: Needed? (We have Lens->Setter coercion)
instance : Evaluatable S (Lens T (ProcedureState S)) T where
  eval cs x := x.get cs

/-! ## Reduction lemmas (so denotations compute)

`simp` reduces all four cases (global/full × getter/lens) to a plain `.get` read.
Making `S` a real parameter (rather than a `cs.L` projection) is what lets the
full-state lemmas match under `simp`. -/

@[simp] theorem eval_getter_global [cs : CurrentState S] (x : Getter T State) :
    eval x = x.get cs.state.global := rfl

@[simp] theorem eval_getter_full [cs : CurrentState S] (x : Getter T (ProcedureState S)) :
    eval x = x.get cs.state := rfl

@[simp] theorem eval_lens_global [cs : CurrentState S] (x : Lens T State) :
    eval x = x.get cs.state.global := rfl

@[simp] theorem eval_lens_full [cs : CurrentState S] (x : Lens T (ProcedureState S)) :
    eval x = x.get cs.state := rfl

/-! ## Sigil syntax for expressions

The `$` sigil is parsed by Lean as a (pseudo) antiquotation node; we intercept
those nodes inside the `GaudiExpr[ ]` macro and rewrite `$e` to `eval e`.

`$x`             ↦ `eval x`     (variable reference)
`$(e)`           ↦ `eval e`     (arbitrary lens-valued term as a variable)
`GaudiExpr[ e ]` wraps an expression body `e` into a `Getter _ (State × S)`, making
the ambient `CurrentState` available inside `e`. -/

/-- Replace every `$e` (antiquotation) leaf in `stx` by `eval e`. -/
private def fixExpr (stx : Syntax) : MacroM Syntax :=
  stx.replaceM fun s => do
    if s.isAntiquot then
      let inner : Term := ⟨s.getAntiquotTerm⟩
      some <$> `(eval $inner)
    else
      pure none

scoped macro:max "GaudiExpr[" e:term "]" : term => do
  let e' : Term := ⟨← fixExpr e⟩
  `(Getter.mk (fun st => letI : CurrentState _ := ⟨st⟩; $e'))

end GaudisCrypt

/-! ## Experiments for expressions -/

namespace GaudisCrypt.Test

open GaudisCrypt

variable [ProgramSpec]

-- set_option trace.Meta.synthInstance true

axiom a : Lens Nat State
axiom b : Lens Nat State

-- a global variable, full state has trivial locals
#check (GaudiExpr[ $a + 1 ] : Getter Nat (ProcedureState Unit))
#check (GaudiExpr[ $a + $b ] : Getter Nat (ProcedureState Unit))

-- a full-current-state lens (e.g. a local variable already lifted)
axiom loc : Lens Nat (ProcedureState Unit)
#check (GaudiExpr[ $a + $loc ] : Getter Nat (ProcedureState Unit))
noncomputable def test := (GaudiExpr[ $a + $loc ] : Getter Nat (ProcedureState Unit))
#print test

-- $(...) for a compound lens term
#check (GaudiExpr[ $(a) + 1 ] : Getter Nat (ProcedureState Unit))

-- reduction: expressions compute through to plain lens reads
example (st : ProcedureState Unit) :
    (GaudiExpr[ $a + 1 ] : Getter Nat (ProcedureState Unit)).get st = a.get st.global + 1 := by
  simp

example (st : ProcedureState Unit) :
    (GaudiExpr[ $a + $loc ] : Getter Nat (ProcedureState Unit)).get st
      = a.get st.global + loc.get st := by
  simp

end GaudisCrypt.Test

/-! ## Syntax for programs (`StmtWithHoles`)

Statement syntax over `StmtWithHoles h l`.  Each expression position (assignment
RHS, sampling distribution, `if`/`while` condition) is wrapped with `GaudiExpr[ ]`
so the `$x` sigil works.  An l-value (assignment/sample LHS) is a *lens*, lifted
into the current full state `State × l` by `liftLens` — so a global `Lens a State`
may be written bare and is lifted with `.ofst`.

Surface forms (`gaudi_stmt`):

    skip;
    x <- e;                       -- assignment
    a, b <- e;   (a,b) <- e;      -- tuple l-value (parens optional), via `Lens.pair`
    x <$ e;                       -- sampling (e : a distribution expression)
    x <- call p (e₁, …, eₙ);      -- procedure call, result stored in `x`
    call p (e₁, …, eₙ);           -- procedure call, result discarded (Lens.throwaway)
    if (e) { … } else { … }       -- the `else` branch is optional
    while (e) { … }
    { … }                         -- a block (sequence)

The call argument list `( … )` is always required (even `()`); the arguments form a
tuple matching the callee's `ParamType`.  (`hole` is still deferred.) -/

namespace GaudisCrypt

variable [ProgramSpec]

/-- Lift a program variable used as an l-value into a lens on the full current state
`State × S`.  Dispatch is on the lens's *container* `M`: a global lens (`M = State`)
is lifted with `.ofst`, a full-state lens (`M = State × S`) is kept as-is.  The
content type `A` is deliberately *not* a class parameter — resolution then only needs
`M` (always concrete from the argument), and the result's content unifies with the
expected type as an ordinary, postponable constraint.  (That is what lets a `call`
result l-value resolve even before the callee's `sig` is known.) -/
class LiftLens (S : Type) (M : Type) where
  lift {A : Type} : Lens A M → Setter A (ProcedureState S)

instance {S : Type} : LiftLens S State where
  lift x := (ProcedureState.globalL.chain x).toSetter
instance {S : Type} : LiftLens S (ProcedureState S) where lift x := x.toSetter

/-- User-facing l-value lift; `S`, the container `M`, and the content `A` are inferred.
The result is a `Setter` (l-values only ever `set`). -/
def liftLens {S A M} [LiftLens S M] (x : Lens A M) : Setter A (ProcedureState S) :=
  LiftLens.lift x

/-- The raw (un-lifted) lens for an l-value: a tuple `(x, y, …)` becomes a nested
`Lens.pair`; a single term is itself.  Pairing needs the components to be disjoint
lenses in the same container — the `disjoint` instance is resolved at the concrete
lenses, so `(a, b)` requires `disjoint a b`. -/
scoped syntax "[lvalRaw| " term "]" : term
macro_rules
  | `([lvalRaw| ($x:term, $y:term)]) => `(Lens.pair [lvalRaw| $x] [lvalRaw| $y])
  | `([lvalRaw| $x:term]) => `($x)

/-- Raw nested `Lens.pair` of a comma-list of l-value components (each component
may itself be a paren-tuple, handled by `[lvalRaw|]`). -/
scoped syntax "[lvalRawList| " term,+ "]" : term
macro_rules
  | `([lvalRawList| $x:term]) => `([lvalRaw| $x])
  | `([lvalRawList| $x:term, $xs:term,*]) => `(Lens.pair [lvalRaw| $x] [lvalRawList| $xs,*])

/-- An l-value lifted into the current full state `State × S`.  Accepts a single
lens, a parenthesised tuple `(a, b)`, or a bare comma-list `a, b` (top-level
parens optional) — all interpreted via `Lens.pair`. -/
scoped syntax "[lval| " term,+ "]" : term
macro_rules
  | `([lval| $xs:term,*]) => `(liftLens [lvalRawList| $xs,*])

/-- A single `_` l-value discards the value written to it (`Setter.throwaway`).  Declared
after the general rule so it takes priority. -/
macro_rules
  | `([lval| _]) => `(Setter.throwaway)

/- ### Concrete syntax -/

declare_syntax_cat gaudi_stmt

syntax "skip" ";" : gaudi_stmt
syntax term:max,+ " <- " term ";" : gaudi_stmt
syntax term:max,+ " <$ " term ";" : gaudi_stmt
syntax (name := callStore) term:max,+ " <- " "call" term:max "(" term,* ")" ";" : gaudi_stmt
syntax (name := callVoid)  "call" term:max "(" term,* ")" ";" : gaudi_stmt
-- internal: generated by `proc` from `call <holeName>` (users never write `holecall`)
syntax (name := holecallStore) term:max,+ " <- " "holecall" term:max "(" term,* ")" ";" : gaudi_stmt
syntax (name := holecallVoid)  "holecall" term:max "(" term,* ")" ";" : gaudi_stmt
syntax "if" "(" term ")" "{" gaudi_stmt* "}" "else" "{" gaudi_stmt* "}" : gaudi_stmt
syntax "if" "(" term ")" "{" gaudi_stmt* "}" : gaudi_stmt
syntax "while" "(" term ")" "{" gaudi_stmt* "}" : gaudi_stmt
syntax "{" gaudi_stmt* "}" : gaudi_stmt

/-- Translate one statement to a `StmtWithHoles` term. -/
scoped syntax "[gstmt| " gaudi_stmt "]" : term
/-- Translate a statement sequence (fold with `seq`; empty ↦ `skip`). -/
scoped syntax "[gseq| " gaudi_stmt* "]" : term
/-- Top-level program bracket. -/
scoped syntax "GaudiProg[" gaudi_stmt* "]" : term

macro_rules
  | `([gseq| ]) => `(StmtWithHoles.skip)
  | `([gseq| $s:gaudi_stmt]) => `([gstmt| $s])
  | `([gseq| $s:gaudi_stmt $ss:gaudi_stmt*]) =>
      `(StmtWithHoles.seq [gstmt| $s] [gseq| $ss*])

macro_rules
  | `([gstmt| skip;]) => `(StmtWithHoles.skip)
  | `([gstmt| $xs:term,* <- $e:term;]) =>
      `(StmtWithHoles.assign [lval| $xs,*] (GaudiExpr[ $e ]))
  | `([gstmt| $xs:term,* <$ $e:term;]) =>
      `(StmtWithHoles.sample [lval| $xs,*] (GaudiExpr[ $e ]))
  | `([gstmt| if ($c:term) { $t:gaudi_stmt* } else { $e:gaudi_stmt* }]) =>
      `(StmtWithHoles.ifThenElse (GaudiExpr[ $c ]) [gseq| $t*] [gseq| $e*])
  | `([gstmt| if ($c:term) { $t:gaudi_stmt* }]) =>
      `(StmtWithHoles.ifThenElse (GaudiExpr[ $c ]) [gseq| $t*] StmtWithHoles.skip)
  | `([gstmt| while ($c:term) { $body:gaudi_stmt* }]) =>
      `(StmtWithHoles.while (GaudiExpr[ $c ]) [gseq| $body*])
  | `([gstmt| { $ss:gaudi_stmt* }]) => `([gseq| $ss*])

open Lean in
/-- Build the (right-nested) argument tuple from a comma-list of arg expressions:
`[]` ↦ `()`, `[e]` ↦ `e`, `e :: es` ↦ `(e, <es>)` — matching `paramListToTuple`. -/
private def mkArgTuple (args : List Term) : MacroM Term := do
  match args with
  | []      => `(())
  | [e]     => pure e
  | e :: es => do `(($e, $(← mkArgTuple es)))

-- `call` (procedure) and `holecall` (hole) statements.  `holecall` is *internal*: the
-- `proc` macro rewrites `call <holeName>` to it; users only ever write `call`.  In both
-- cases the callee is listed first so its `sig` is unified before the result l-value/args.
open Lean in
macro_rules
  | `([gstmt| $xs:term,* <- call $p:term ( $args:term,* );]) => do
      `(StmtWithHoles.call [lval| $xs,*] $p (GaudiExpr[ $(← mkArgTuple args.getElems.toList) ]))
  | `([gstmt| call $p:term ( $args:term,* );]) => do
      `(StmtWithHoles.call Setter.throwaway $p (GaudiExpr[ $(← mkArgTuple args.getElems.toList) ]))
  | `([gstmt| $xs:term,* <- holecall $n:term ( $args:term,* );]) => do
      `(StmtWithHoles.hole $n [lval| $xs,*] (GaudiExpr[ $(← mkArgTuple args.getElems.toList) ]))
  | `([gstmt| holecall $n:term ( $args:term,* );]) => do
      `(StmtWithHoles.hole $n Setter.throwaway (GaudiExpr[ $(← mkArgTuple args.getElems.toList) ]))

macro_rules
  | `(GaudiProg[ $ss:gaudi_stmt* ]) => `([gseq| $ss*])

/- ### Procedures

`proc (x : T, …) [: R] { var u : U, …; <stmts> ; return e }` builds a
`ProcedureWithHoles .empty sig`.  Each param/local name is `let`-bound — the user's
identifier spliced in, so hygiene lines up — to its projection lens into the full
state `State × l`, written as a plain `Lens.id.ofst.osnd…` chain.  The body's `$x`
and `x <- …` then resolve via the ordinary expression machinery.  `: R` is optional;
without it the return type is inferred from `return e`. -/

open Lean in section

declare_syntax_cat proc_binder
syntax ident " : " term : proc_binder

/-- `Lens.id` followed by a chain of `.ofst` (`true`) / `.osnd` (`false`). -/
private def mkChain (steps : List Bool) : MacroM Term := do
  let mut acc ← `(Lens.id)
  for s in steps do
    acc ← if s then `($(acc).ofst) else `($(acc).osnd)
  pure acc

/-- Steps to reach slot `k` of a right-nested `n`-tuple (the last element is
un-wrapped, so it needs no final `.ofst`). -/
private def navSteps (k n : Nat) : List Bool :=
  if k + 1 == n then List.replicate k false else true :: List.replicate k false

private def parseBinder : TSyntax `proc_binder → MacroM (Ident × Term)
  | `(proc_binder| $id:ident : $ty:term) => pure (id, ty)
  | _ => Macro.throwUnsupported

/-- A hole declaration `A : (T₁, …, Tₙ) → R` (an abstract procedure with no locals). -/
declare_syntax_cat hole_binder
syntax ident " : " "(" term,* ")" " → " term : hole_binder

private def parseHoleBinder : TSyntax `hole_binder → MacroM (Ident × List Term × Term)
  | `(hole_binder| $id:ident : ( $ps:term,* ) → $ret:term) => pure (id, ps.getElems.toList, ret)
  | _ => Macro.throwUnsupported

/-- Rewrite `call A (…)` → `holecall A (…)` for every callee `A` whose name is a hole
(recursing into `if`/`while`/block bodies); everything else is left untouched. -/
partial def rewriteHoles (holeNames : List Name) (s : TSyntax `gaudi_stmt) :
    MacroM (TSyntax `gaudi_stmt) := do
  let k := s.raw.getKind
  -- `call`/`holecall` statements carry a sepBy arg-list inside parens, which category
  -- quotations cannot match, so we dispatch on the production kind at the `Syntax` level.
  if k == ``callStore || k == ``callVoid then
    -- callee position: `callStore` is `xs,* "<-" "call" callee …`; `callVoid` is `"call" callee …`.
    let calleeIdx := if k == ``callStore then 3 else 1
    let args := s.raw.getArgs
    let callee := args[calleeIdx]!
    if callee.isIdent && holeNames.contains callee.getId then
      -- swap kind to the `holecall*` production and the `"call"` atom → `"holecall"`.
      let newKind := if k == ``callStore then ``holecallStore else ``holecallVoid
      let newArgs := args.map fun a =>
        match a with
        | .atom info "call" => .atom info "holecall"
        | _ => a
      return ⟨(s.raw.setArgs newArgs).setKind newKind⟩
    else
      return s
  match s with
  | `(gaudi_stmt| if ($c:term) { $t:gaudi_stmt* } else { $e:gaudi_stmt* }) => do
      `(gaudi_stmt| if ($c) { $(← t.mapM (rewriteHoles holeNames))* }
                          else { $(← e.mapM (rewriteHoles holeNames))* })
  | `(gaudi_stmt| if ($c:term) { $t:gaudi_stmt* }) => do
      `(gaudi_stmt| if ($c) { $(← t.mapM (rewriteHoles holeNames))* })
  | `(gaudi_stmt| while ($c:term) { $b:gaudi_stmt* }) => do
      `(gaudi_stmt| while ($c) { $(← b.mapM (rewriteHoles holeNames))* })
  | `(gaudi_stmt| { $ss:gaudi_stmt* }) => do
      `(gaudi_stmt| { $(← ss.mapM (rewriteHoles holeNames))* })
  | _ => pure s

syntax "proc" "(" proc_binder,* ")" ("uses" "(" hole_binder,* ")")? (" : " term:max)? "{"
         ("var" proc_binder,* ";")*
         gaudi_stmt*
         "return" term (";")?
       "}" : term

macro_rules
  | `(proc ( $params:proc_binder,* ) $[uses ( $holes:hole_binder,* )]? $[: $retTy:term]? {
        $[var $locals:proc_binder,* ;]*
        $stmts:gaudi_stmt*
        return $ret:term $[;]?
      }) => do
    let paramBs := (← params.getElems.toList.mapM parseBinder).toArray
    -- multiple `var …;` lines are concatenated into a single local-variable list
    let localBs := (← (locals.toList.flatMap (·.getElems.toList)).mapM parseBinder).toArray
    let holeBs := (← match holes with
      | some hs => hs.getElems.toList.mapM parseHoleBinder
      | none    => pure []).toArray
    let np := paramBs.size
    let nl := localBs.size
    -- the signature and local-variable list; the local-state `L` is the
    -- `LocalVariableState` *structure* (params tuple + vars tuple).
    let paramTys := paramBs.map (·.2)
    let localSigmas ← localBs.mapM fun (_, ty) => `(⟨$ty, inferInstance⟩)
    let retTyTerm ← match retTy with | some r => pure r | none => `(_)
    let sigTerm ← `(({ params := [$paramTys,*], ret := $retTyTerm } : ProcedureSignature))
    let localsTerm ← `([$localSigmas,*])
    -- `L` is the local-state structure, indexed by param *types* (no `ret`), so it is
    -- fully determined even when the return type is omitted.
    let L ← `(LocalVariableState [$paramTys,*] $localsTerm)
    -- one `let` per name, binding it to its lens into `ProcedureState L`.  A variable
    -- lens navigates `ProcedureState L` → (`localL`) `L` → (`paramsL`/`varsL`) the
    -- params/vars tuple → (`mkChain`/`navSteps`) the individual slot.
    let mut binds : Array (Ident × Term × Term) := #[]
    for k in [0:np] do
      let (id, ty) := paramBs[k]!
      let slot ← mkChain (navSteps k np)
      let chain ← `(Lens.intoParams $slot)
      binds := binds.push (id, ← `(Lens $ty (ProcedureState $L)), chain)
    for j in [0:nl] do
      let (id, ty) := localBs[j]!
      let slot ← mkChain (navSteps j nl)
      let chain ← `(Lens.intoVars $slot)
      binds := binds.push (id, ← `(Lens $ty (ProcedureState $L)), chain)
    -- holes: a `ProcedureSignature` (no locals) each, folded into a `HoleSigs` context,
    -- and one `let` per name binding it to its `HoleIndex` (last-declared = `.zero`).
    let nh := holeBs.size
    let holeSigTerms ← holeBs.mapM fun (_, ps, ret) =>
      `(({ params := [$(ps.toArray),*], ret := $ret } : ProcedureSignature))
    let mut hCtx ← `(HoleSigs.empty)
    for sigT in holeSigTerms do hCtx ← `(($hCtx).append $sigT)
    let mut holeBinds : Array (Ident × Term × Term) := #[]
    for k in [0:nh] do
      let (id, _, _) := holeBs[k]!
      let mut idx ← `(HoleIndex.zero)
      for _ in [0 : nh - 1 - k] do idx ← `(HoleIndex.succ $idx)
      holeBinds := holeBinds.push (id, ← `(HoleIndex $hCtx $(holeSigTerms[k]!)), idx)
    let wrap (bs : Array (Ident × Term × Term)) (inner : Term) : MacroM Term :=
      bs.foldrM (fun (id, ty, val) acc => `(let $id : $ty := $val; $acc)) inner
    -- annotate with the explicit local-state `L` (so expressions see `S = L`) and hole
    -- context `hCtx`; the `L = sig.LocalVariableState` check happens in ordinary elaboration.
    -- rewrite `call A (…)` → `holecall A (…)` for every callee `A` that is a declared hole
    let holeNames := holeBs.toList.map (·.1.getId)
    let stmts' ← stmts.mapM (rewriteHoles holeNames)
    let body ← wrap (binds ++ holeBinds) (← `((GaudiProg[ $stmts'* ] : StmtWithHoles $hCtx $L)))
    let retval ← wrap binds (← `((GaudiExpr[ $ret ] : Getter _ (ProcedureState $L))))
    `((⟨$localsTerm, $body, $retval⟩ : ProcedureWithHoles $hCtx $sigTerm))

end

/-! ### Procedure *type* syntax

`proctype (T, U, V) -> W` is the type `Procedure { params := [T, U, V], ret := W }`, and
`proctype (…) -> W uses ((A₁,…) → R₁, …)` is the corresponding `ProcedureWithHoles`, whose
hole context is built from the listed (nameless) procedure signatures.  (Uses `->` rather
than `:` so it needs no extra parentheses inside a type ascription.) -/

/-- A nameless hole signature `(T₁, …, Tₙ) → R` inside a `proctype … uses (…)` clause. -/
declare_syntax_cat hole_sig
syntax "(" term,* ")" " → " term : hole_sig

syntax "proctype " "(" term,* ")" (" → " <|> " -> ") term (" uses " "(" hole_sig,* ")")? : term

open Lean in
macro_rules
  -- unicode `→` spelling delegates to the `->` arm below (distinguished by the arrow atom)
  | `(proctype ( $params:term,* ) → $ret:term $[uses ( $holes:hole_sig,* )]?) =>
      `(proctype ( $params,* ) -> $ret $[uses ( $holes,* )]?)
  | `(proctype ( $params:term,* ) -> $ret:term $[uses ( $holes:hole_sig,* )]?) => do
      let sigTerm ← `(ProcedureSignature.mk [$params,*] $ret)
      match holes with
      | none    => `(Procedure $sigTerm)
      | some hs =>
        let mut hCtx ← `(HoleSigs.empty)
        for h in hs.getElems do
          match h with
          | `(hole_sig| ( $ps:term,* ) → $r:term) =>
              hCtx ← `(($hCtx).append (ProcedureSignature.mk [$ps,*] $r))
          | _ => Macro.throwUnsupported
        `(ProcedureWithHoles $hCtx $sigTerm)

/-! `proctype` unexpanders.  A signature already prints as `procsig (…) -> …` (the
`ProcedureSignature.mk` unexpander), so we just rewrite `Procedure (procsig …)` and
`ProcedureWithHoles … (procsig …)` to `proctype …`.  Parameter lists are read off the raw
`procsig` node (a category quotation can't match the sepBy inside the parens). -/

open Lean PrettyPrinter in
/-- If `s` is a `procsig ( … ) -> …` node, return its parameter list and return type. -/
private def procsigParts? (s : Syntax) : Option (Syntax.TSepArray `term "," × TSyntax `term) :=
  let a := s.getArgs
  if a.size == 6 && a[0]!.getAtomVal == "procsig" then some (⟨a[2]!.getArgs⟩, ⟨a[5]!⟩) else none

open Lean PrettyPrinter in
@[app_unexpander Procedure]
def unexpandProcedure : Unexpander
  | `($_ $sig) => do
      let some (ps, r) := procsigParts? sig.raw | throw ()
      `(proctype ( $ps,* ) → $r)
  | _ => throw ()

open Lean PrettyPrinter in
/-- Collect every `procsig ( … ) -> …` node in `s`, left to right.  (Matching field
notation on `HoleSigs.append` in a quotation is brittle, so we just gather the leaves.)
A hole context `HoleSigs.empty.append s₁ … .append sₙ` has the hole signatures as its
only `procsig` nodes, in declaration order. -/
private partial def collectProcsigParts (s : Syntax) :
    Array (Syntax.TSepArray `term "," × TSyntax `term) :=
  match procsigParts? s with
  | some pr => #[pr]
  | none    => s.getArgs.foldl (fun acc a => acc ++ collectProcsigParts a) #[]

open Lean PrettyPrinter in
@[app_unexpander ProcedureWithHoles]
def unexpandProcedureWithHoles : Unexpander
  | `($_ $holes $sig) => do
      let some (ps, r) := procsigParts? sig.raw | throw ()
      let holeParts := collectProcsigParts holes.raw
      if holeParts.isEmpty then `(proctype ( $ps,* ) -> $r)
      else
        let holeSyns ← holeParts.mapM fun (hps, hr) => `(hole_sig| ( $hps,* ) → $hr)
        `(proctype ( $ps,* ) → $r uses ( $holeSyns,* ))
  | _ => throw ()

/-! ### Procedure *signature* syntax

`procsig (T, U, V) -> W` is the bare `ProcedureSignature.mk [T, U, V] W` (the same surface
form as `proctype`, minus the holes — a signature has none).  By construction
`Procedure (procsig …) = proctype …`.  The unexpander is on `ProcedureSignature.mk`, so any
signature with a literal parameter list prints back as `procsig (…) -> …`. -/

syntax "procsig " "(" term,* ")" (" → " <|> " -> ") term : term

macro_rules
  | `(procsig ( $params:term,* ) → $ret:term) => `(procsig ( $params,* ) -> $ret)
  | `(procsig ( $params:term,* ) -> $ret:term) => `(ProcedureSignature.mk [$params,*] $ret)

open Lean PrettyPrinter in
@[app_unexpander ProcedureSignature.mk]
def unexpandProcSig : Unexpander
  | `($_ [$ps,*] $r) => `(procsig ( $ps,* ) → $r)
  | _ => throw ()

/-! ### Module type of a procedure — `procmod (…) -> R`

`procmod (T, …) -> R` is `ModuleTypeRep.proc (procsig (T,…) -> R)`: the same surface as `proctype`,
but producing a `ModuleTypeRep` rather than the `Procedure` type.  The return type is parsed at
precedence `36`, above the usual infix operators, so a trailing one groups as
`(procmod (…) -> R) ⊙ …` rather than folding into `R`.  A product/function *return* type therefore
needs parentheses: `procmod (…) -> (A × B)`.  (No `uses` clause: for a procedure-with-holes module
type write `ModuleTypeRep.arr` explicitly.) -/

syntax "procmod " "(" term,* ")" (" → " <|> " -> ") term:36 : term

macro_rules
  | `(procmod ( $params:term,* ) → $ret:term) => `(procmod ( $params,* ) -> $ret)
  | `(procmod ( $params:term,* ) -> $ret:term) =>
      `(_root_.GaudisCrypt.ModuleTypeRep.proc (procsig ( $params,* ) -> $ret))

open Lean PrettyPrinter in
@[app_unexpander _root_.GaudisCrypt.ModuleTypeRep.proc]
def unexpandProcMod : Unexpander
  | `($_ $sig) => do
      let some (ps, r) := procsigParts? sig.raw | throw ()
      `(procmod ( $ps,* ) → $r)
  | _ => throw ()

end GaudisCrypt

/-! ## Experiments for programs -/

namespace GaudisCrypt.ProgTest

open GaudisCrypt

variable [ProgramSpec]

axiom a : Lens Nat State
axiom b : Lens Nat State
axiom c : Lens Bool State
axiom d : Lens Nat State

-- `Lens.pair` needs disjointness of the paired lenses (resolved at the concrete lenses).
-- For nested tuples `(a, b), d` the `disjoint3'` instance derives `disjoint (a.pair b) d`
-- from the pairwise ones.
axiom a_b_disjoint : disjoint a b
axiom a_d_disjoint : disjoint a d
axiom b_d_disjoint : disjoint b d
attribute [instance] a_b_disjoint a_d_disjoint b_d_disjoint

noncomputable def prog_assign : Stmt Unit := GaudiProg[
  a <- $a + 1;
  b <- $a + $b;
]

noncomputable def prog_if : Stmt Unit := GaudiProg[
  if ($a == $b) {
    a <- 0;
  } else {
    a <- $b;
  }
]

noncomputable def prog_while : Stmt Unit := GaudiProg[
  while ($a == 0) {
    a <- $a + 1;
  }
]

noncomputable def prog_sample : Stmt Unit := GaudiProg[
  c <$ GaudisCrypt.SubProbability.uniform;
]

noncomputable def split : Stmt Unit := GaudiProg[
  (a,b) <- (1,2);
]

noncomputable def split2 : Stmt Unit := GaudiProg[
  a,b <- (1,2);
]

noncomputable def split3 : Stmt Unit := GaudiProg[
  (a,b),d <- ((1,3),2);
]


#check @prog_assign
#print prog_if

/- ### Procedures -/

-- one param, no locals, return type inferred
noncomputable def proc_inc := proc (x : Nat) {
  return $x + 1
}
#check @proc_inc

-- params + a local + body + explicit return type
noncomputable def proc_sum := proc (x : Nat, y : Nat) : Nat {
  var u : Nat;
  u <- $x + $y;
  return $u
}
#print proc_sum

-- no params, a local, control flow, writes to a global
noncomputable def proc_loop := proc () {
  var i : Nat;
  i <- 0;
  while ($i == 0) {
    i <- $i + 1;
    a <- $a + $i;
  }
  return $i
}
#check @proc_loop

/- ### Procedure calls -/

-- store the result of a one-argument call
noncomputable def prog_call : Stmt Unit := GaudiProg[
  a <- call proc_inc ($a);
]
#print prog_call

-- a two-argument call (the argument tuple matches the callee's `ParamType`)
noncomputable def prog_call2 : Stmt Unit := GaudiProg[
  a <- call proc_sum ($a, $b);
]

-- discard the result (uses `Lens.throwaway`); `()` still required
noncomputable def prog_call_void : Stmt Unit := GaudiProg[
  call proc_inc ($a);
]
#check @prog_call_void

/- ### Holes (adversary placeholders) -/

-- A `uses` clause declares holes; `call A (…)` on a hole name becomes `StmtWithHoles.hole`.
noncomputable def proc_with_hole := proc (x : Nat) uses (A : (Nat) → Nat) : Nat {
  var y : Nat;
  y <- call A ($x);          -- hole call (A is a HoleIndex)
  return $y
}
#print proc_with_hole

-- two holes + a concrete procedure call, mixed in one body
noncomputable def proc_two_holes := proc (x : Nat) uses (A : (Nat) → Bool, B : (Bool) → Nat) {
  var u : Bool;
  var v : Nat;
  u <- call A ($x);          -- hole A
  v <- call B ($u);          -- hole B
  v <- call proc_inc ($v);   -- concrete procedure (still `call`)
  call A ($v);               -- discarded hole result
  return $v
}
#check @proc_two_holes
#print proc_two_holes

/- ### Procedure *type* syntax -/

-- `proctype (…) -> W` is `Procedure { params := […], ret := W }`
example : (proctype (Nat, Bool) -> Nat) = Procedure { params := [Nat, Bool], ret := Nat } := rfl
#check (proc_inc : proctype (Nat) -> Nat)
#check (proc_sum : proctype (Nat, Nat) -> Nat)

-- `proctype (…) -> W uses (…)` is the corresponding `ProcedureWithHoles`
#check (proc_two_holes : proctype (Nat) -> Nat uses ((Nat) → Bool, (Bool) → Nat))
#check (proc_with_hole : proctype (Nat) -> Nat uses ((Nat) → Nat))

-- the types also print back as `proctype …` (unexpanders)
#check proctype (Nat) -> Nat
#check proctype (Nat, Bool) -> Nat uses ((Nat) → Bool, (Bool) → Nat)

-- `procsig (…) -> W` is the bare signature; `Procedure (procsig …) = proctype …`
example : (procsig (Nat, Bool) -> Nat) = ({ params := [Nat, Bool], ret := Nat } : ProcedureSignature) :=
  rfl
example : Procedure (procsig (Nat) -> Nat) = proctype (Nat) -> Nat := rfl
#check procsig (Nat, Bool) -> Nat
#check ProcedureSignature.mk [String,String] Nat
#check Procedure (ProcedureSignature.mk [String,String] Nat)
#check ProcedureWithHoles (.append .empty (procsig () -> Unit)) (ProcedureSignature.mk [String,String] Nat)
-- TODO: Can we make test cases that trigger if the terms above don't print the way we want?

-- both arrow spellings accepted: `->` and `→`
example : (procsig (Nat) → Bool) = (procsig (Nat) -> Bool) := rfl
example : (proctype (Nat) → Bool) = (proctype (Nat) -> Bool) := rfl
#check (proc_two_holes : proctype (Nat) → Nat uses ((Nat) → Bool, (Bool) → Nat))

end GaudisCrypt.ProgTest


open GaudisCrypt

/-! ## Concrete syntax for module types

`M →ₘ N` is `Module.Arr M N` and `M ×ₘ N` is `Module.Prod M N`: the arrow and the product on the
*types* of modules (`Module T`, a name declared by `moduletype`, …), each side classified by an
`IsModule` instance.  Precedences mirror `→`/`×`: `×ₘ` (35) binds tighter than `→ₘ` (25), both
right-associative.  Both are `scoped` to `GaudisCrypt`, so `open`ing that namespace activates them.

`ModuleTypeRep` itself has no infix notation; its constructors are written `.arr`/`.prod`/`.unit`
by dot notation (and `.proc` also as `procmod (…) -> R`). -/
namespace GaudisCrypt
scoped infixr:35 " ×ₘ " => _root_.GaudisCrypt.Module.Prod
scoped infixr:25 " →ₘ " => _root_.GaudisCrypt.Module.Arr
end GaudisCrypt

/-- A field `f : Module T` of a `moduletype` declaration. -/
/- A field of a `moduletype` declaration: either `module f : T;` (explicit module type)
or the shorthand `proc f (T₁, …) -> R;` (a procedure field). -/
declare_syntax_cat moduletypeField
syntax "module " ident " : " term ";" : moduletypeField
syntax "proc " ident " (" term,* ")" (" → " <|> " -> ") term ";" : moduletypeField

/-- `moduletype Name { module f₁ : T₁; … ; module fₙ : Tₙ }` declares a record-like module
type, where each `Tᵢ` is a `ModuleTypeRep`.  A field may also be written
`proc fᵢ (A₁, …) -> R;`, shorthand for `module fᵢ : ModuleTypeRep.proc (procsig (A₁, …) -> R);`.
It expands to: `Name := Module (ModuleTypeRep.prod T₁ (… Tₙ))` (right-nested product of the
field types), a record `Name.Structure` with fields `fᵢ : Module Tᵢ`, accessors `Name.fᵢ`
(via `Module.fst'`/`Module.snd'`), a constructor `Name.mk`, a destructor `Name.structure`, and
the two round-trip `@[simp]` lemmas `Name.mk_destruct` / `Name.destruct_mk`. -/
syntax "moduletype " ident "{" moduletypeField* "}" : command

open Lean Elab Command in
elab_rules : command
  | `(moduletype $nm:ident { $fields:moduletypeField* }) => do
      let n := fields.size
      if n == 0 then throwError "moduletype needs at least one field"
      -- per field: the field name and its `ModuleTypeRep`
      let fns ← fields.mapM fun f => match f with
        | `(moduletypeField| module $fn:ident : $_ ;)         => pure fn
        | `(moduletypeField| proc $fn:ident ( $_,* ) -> $_ ;) => pure fn
        | `(moduletypeField| proc $fn:ident ( $_,* ) → $_ ;)  => pure fn
        | _ => throwUnsupportedSyntax
      let Ts ← fields.mapM fun f => match f with
        | `(moduletypeField| module $_ : $T:term ;) => pure T
        | `(moduletypeField| proc $_ ( $ps,* ) -> $ret:term ;)
        | `(moduletypeField| proc $_ ( $ps,* ) → $ret:term ;) =>
            `(_root_.GaudisCrypt.ModuleTypeRep.proc (ProcedureSignature.mk [$ps,*] $ret))
        | _ => throwUnsupportedSyntax
      -- the field/accessor types are `Module Tᵢ`
      let fts ← Ts.mapM fun T => `(_root_.GaudisCrypt.Module $T)
      -- right-nested product of the underlying types
      let prodT ← Ts.pop.foldrM
        (fun T acc => `(_root_.GaudisCrypt.ModuleTypeRep.prod $T $acc)) Ts.back!
      -- generated names
      let nb := nm.getId
      let structId := mkIdent (nb.str "Structure")
      let ctorId   := mkIdent ((nb.str "Structure").str "mk")
      let mkId     := mkIdent (nb.str "mk")
      let structFn := mkIdent (nb.str "structure")
      let moduleTypeId := mkIdent (nb.str "typeRep")
      let accIds   := fns.map fun f => mkIdent (nb ++ f.getId)
      let projId : Nat → Ident := fun i => mkIdent ((nb.str "Structure") ++ fns[i]!.getId)
      let mId := mkIdent `m
      let sId := mkIdent `s
      -- (1) `X.typeRep` names the underlying `ModuleTypeRep`; `X := Module X.typeRep`.  `X` is a
      -- plain (non-reducible) def, so the `IsModule (Module t)` instance does not apply to it and
      -- it gets its own — without which `X` could not appear in a `Module.Arr`/`Module.Prod`.
      elabCommand (← `(def $moduleTypeId : _root_.GaudisCrypt.ModuleTypeRep := $prodT))
      elabCommand (← `(def $nm := _root_.GaudisCrypt.Module $moduleTypeId))
      elabCommand (← `(instance : _root_.GaudisCrypt.IsModule $nm where
        moduleTypeRep := $moduleTypeId))
      -- (2) the record structure
      elabCommand (← `(structure $structId where $[$fns:ident : $fts:term]*))
      -- (3) accessors: field `i` is `fst (snd^i m)`, or `snd^(n-1) m` for the last
      for i in [0:n] do
        let accId := accIds[i]!
        let ft := fts[i]!
        let mut e : Term := mId
        for _ in [0:i] do e ← `(_root_.GaudisCrypt.Module.snd' $e)
        if i + 1 < n then e ← `(_root_.GaudisCrypt.Module.fst' $e)
        elabCommand (← `(noncomputable def $accId ($mId : $nm) : $ft := $e))
      -- (4) constructor: right-nested `Module.pair`
      let mut mkBody : Term ← `($(projId (n-1)) $sId)
      for i in [0:n-1] do
        let j := n - 2 - i
        let pj := projId j
        mkBody ← `(_root_.GaudisCrypt.Module.pair' ($pj $sId) $mkBody)
      elabCommand (← `(@[reducible] noncomputable def $mkId ($sId : $structId) : $nm := $mkBody))
      -- (5) destructor
      let args ← (Array.range n).mapM fun i => do
        let accId : Ident := accIds[i]!
        `($accId $mId)
      elabCommand (← `(noncomputable def $structFn ($mId : $nm) : $structId := $ctorId $args*))
      -- (6) / (7) round-trip lemmas
      let baseLemmas : Array Ident := #[mkId, structFn] ++ accIds
      elabCommand (← `(@[simp] theorem $(mkIdent (nb.str "mk_destruct")) ($sId : $structId) :
          $structFn ($mkId $sId) = $sId := by simp [$[$baseLemmas:ident],*]))
      let dmLemmas : Array Ident := baseLemmas.push (mkIdent `Module.pair_fst_snd')
      elabCommand (← `(@[simp] theorem $(mkIdent (nb.str "destruct_mk")) ($mId : $nm) :
          $mkId ($structFn $mId) = $mId := by simp [$[$dmLemmas:ident],*]))

/-! ## Module definitions — `module X (…) : T { proc f (…) : R { … }; … }`

```
module X (A : Module.Arr TestModule (Module (procmod () → Unit)), B : TestModule) : M2 {
  proc g () : Unit {
    _ <- call (Module.app A myMod) ();
    _ <- call (myMod.main) ("hello", 5);
    return ();
  };
  proc h () : Unit { return (); };
}
```
declares a module `X` with module *parameters* `A`, `B` (the parameter list is optional) whose
fields are the procedures `g`, `h`.  Procedure bodies use the ordinary statement syntax, except
that the callee of a `call` is a *module* (`Module.Proc sig`) rather than a bare `Procedure sig`.

Elaboration is in two passes.  First the whole body of each procedure is type-checked *as
written* — with the module parameters in the local context and every callee in place (each callee
that mentions a parameter ascribed to `Module (.proc ?sig)`).  Only then, from the signatures that
this typing assigns to those `?sig`, is each procedure emitted as a constant
`X.<f>.procedure : ProcedureWithHoles …`, in which
* a `call` whose callee mentions a module parameter has become a **hole** (the callee, having
  done its job for typing, is dropped).  Two calls with the same callee syntax share one hole;
* every other callee is a closed module expression, converted with `Module.procedure`.

Each procedure also gets a *module* `X.<f>`.  When it uses no module parameter that is simply
`Module.proc X.<f>.procedure`.  Otherwise it is curried over the parameters it does use, in
declaration order — `X.<f> : Module.Arr T₁ (… (Module.Arr Tₖ (Module.Proc sig)))` — as
`Module.procWithHoles X.<f>.procedure` applied to the tuple of its callees, under `k` `.abs`
binders.  The callees are *read back* from their elaborated form for this: each is either closed
(then it is used as it stands) or built from the parameters with `Module.app`/`fst`/`snd`/`pair`,
possibly after unfolding — a callee that is anything else has no `ModuleExpression` counterpart
and is rejected.

Finally `X` itself is the record of those procedures (a right-nested `.pair`, as `moduletype`
nests its fields), abstracted over *all* the parameters — used or not — which it takes as one
right-nested tuple: `X : Module.Arr (Module.Prod T₁ (… Tₙ)) M`, where `M` is the module type
written after the `:`, or `Module.Prod (Module.Proc sig₁) (… (Module.Proc sigₙ))` — the anonymous
record of the procedures' own types — when there is none.  With an empty parameter list that tuple
is `Module.Unit`; with no parameter list at all `X` is not a function but an `M`.

A declaration *with* a parameter list also gets the `@[simp]` lemma `X.apply_simp` for applying
`X`: `Module.app X (Module.pair A (… Z)) = M.mk { f₁ := Module.app X.f₁ A, … }`, i.e. the record of
the procedures, each applied to the parameters it uses (`Module.pair` in place of `M.mk` when `M`
is not a `moduletype` name).  So the two ways of instantiating a module — applying the record `X`
or applying the individual `X.f` — agree, by `simp`. -/

/-- One procedure of a `module` declaration: `proc f (x : T, …) : R { … };`.  Same shape as
the `proc` *term* syntax (which it expands to), plus a name and a trailing `;`. -/
declare_syntax_cat gaudi_module_proc

-- the type ascriptions are parsed at `term:max` (as in the `proc` term syntax): a lower
-- precedence would let the type swallow the `{ … }` block that follows it as a structure instance
syntax "proc " ident "(" proc_binder,* ")" (" : " term:max)? "{"
         ("var" proc_binder,* ";")*
         gaudi_stmt*
         "return" term (";")?
       "}" (";")? : gaudi_module_proc

syntax "module " ident ("(" proc_binder,* ")")? (" : " term:max)? "{"
         gaudi_module_proc*
       "}" : command

/-- Proves `Module.app X t = <record of the procedures of X, applied to their parameters>` for the
module `X` of a `module X (…) { … }` declaration and a *variable* parameter tuple `t` — the generic
form of the `X.apply_simp` lemma the command emits (`ModuleDecl.elabApplySimp`).  `X` must be given
as its name, which the script unfolds.

Both sides are `.reduce`s of concrete expressions, so this is a normalisation proof — but a
directed one, not a search:
* the left-hand side is normalised on its own (`conv_lhs`).  Unfolding `X` exposes the β-redex
  `.app (.abs body) t`; `reduce_app_left`/`_right` strip the inner `.reduce`s that `toModule` left
  behind, `reduce_beta` fires the redex, and the substitution then computes — through the
  procedures' own expressions, which are closed (`Module.substituteSimultaneously_expression`).
  What is left is `reduce` of the record `.pair f₁ (… fₙ)` of the applied procedures;
* the right-hand side is *not* unfolded, so its fields are still modules.
  `Module.reduce_pair_expression` peels the record one field at a time against them, and each
  field's obligation `reduce fᵢ = (…).expression` is then closed by the same stripping lemmas —
  no normal-form search and no termination side conditions anywhere. -/
syntax "module_apply " ident : tactic

macro_rules
  | `(tactic| module_apply $x:ident) =>
    `(tactic|
        (apply GaudisCrypt.Module.ext
         conv_lhs =>
           simp only [$x:ident, GaudisCrypt.Module.app, GaudisCrypt.Module.app',
             GaudisCrypt.Module.moduleTypeRep, GaudisCrypt.ModuleExpression.toModule,
             GaudisCrypt.ModuleExpression.reduce_app_left,
             GaudisCrypt.ModuleExpression.reduce_app_right,
             GaudisCrypt.ModuleExpression.reduce_fst_inner,
             GaudisCrypt.ModuleExpression.reduce_snd_inner,
             GaudisCrypt.ModuleExpression.reduce_beta, GaudisCrypt.ModuleExpression.substitute,
             GaudisCrypt.ModuleExpression.substituteSimultaneously,
             GaudisCrypt.ModuleExpression.variableSubstitution,
             GaudisCrypt.ModuleExpression.liftSubst,
             GaudisCrypt.Module.substituteSimultaneously_expression]
         repeat' refine GaudisCrypt.Module.reduce_pair_expression _ _ ?_ ?_
         all_goals
           simp only [GaudisCrypt.Module.app, GaudisCrypt.Module.app', GaudisCrypt.Module.fst,
             GaudisCrypt.Module.fst', GaudisCrypt.Module.snd, GaudisCrypt.Module.snd',
             GaudisCrypt.Module.pair, GaudisCrypt.Module.pair',
             GaudisCrypt.Module.moduleTypeRep, GaudisCrypt.ModuleExpression.toModule,
             GaudisCrypt.ModuleExpression.reduce_app_left,
             GaudisCrypt.ModuleExpression.reduce_app_right,
             GaudisCrypt.ModuleExpression.reduce_fst_inner,
             GaudisCrypt.ModuleExpression.reduce_snd_inner,
             GaudisCrypt.Module.reduce_expression]))

namespace GaudisCrypt.ModuleDecl

open Lean Elab Command Meta Term

/-- The name of the `i`-th generated hole (both the `uses` binder and its call sites). -/
def holeIdent (i : Nat) : Ident := mkIdent (Name.mkSimple s!"_hole{i}")

/-- `holeIdent` in callee position. -/
def holeCallee (i : Nat) : Term := holeIdent i

/-- Does `s` mention one of the identifiers `names` (the module's parameters)?  A parameter also
counts as mentioned when it heads a field access (`B.main` is one identifier, not two). -/
partial def mentions (names : List Name) (s : Syntax) : Bool :=
  if s.isIdent then names.any fun n => n == s.getId || n.isPrefixOf s.getId
  else s.getArgs.any (mentions names)

/-- Syntactic equality ignoring source positions — two calls of the same module argument
should share a single hole. -/
partial def sameSyntax : Syntax → Syntax → Bool
  | .missing, .missing => true
  | .atom _ v, .atom _ v' => v == v'
  | .ident _ _ v _, .ident _ _ v' _ => v == v'
  | .node _ k as, .node _ k' as' =>
      k == k' && as.size == as'.size && (as.zip as').all fun (a, b) => sameSyntax a b
  | _, _ => false

/-- Rewrite the `call`s of a module body (recursing through the whole statement tree).  A callee
that mentions a module parameter is replaced by `mkCallee i` for its (deduplicated) hole number
`i`, and the state accumulates those callees in hole order.  Any other callee is a `Module.Proc`,
so `Module.procedure` extracts the procedure the `call` statement expects.

Two runs with the same `params` produce the same hole numbering, which is what lets the
type-checking pass and the final pass agree on it. -/
partial def rewriteCalls (params : List Name) (mkCallee : Nat → Term) (s : Syntax) :
    StateM (Array Term) Syntax := do
  let k := s.getKind
  if k == ``GaudisCrypt.callStore || k == ``GaudisCrypt.callVoid then
    let i := if k == ``GaudisCrypt.callStore then 3 else 1
    let callee : Term := ⟨s.getArg i⟩
    if mentions params callee.raw then
      let holes ← get
      let idx := (holes.findIdx? fun c => sameSyntax c.raw callee.raw).getD holes.size
      if idx == holes.size then set (holes.push callee)
      return s.setArg i (mkCallee idx)
    else
      return s.setArg i (Syntax.mkCApp ``GaudisCrypt.Module.procedure #[callee])
  else match s with
    | .node info k args => return .node info k (← args.mapM (rewriteCalls params mkCallee))
    | _ => return s

/-- The named metavariable `?_holeSigᵢ` standing for the signature of the `i`-th hole: it is
solved by elaborating the body with the real callees in place, and read back afterwards. -/
def sigHole (i : Nat) : Term :=
  ⟨mkNode ``Lean.Parser.Term.syntheticHole #[mkAtom "?", mkIdent (sigName i)]⟩
  where sigName (i : Nat) : Name := Name.mkSimple s!"_holeSig{i}"

/-- Bring the module parameters into the local context (with their declared types) so that a
callee mentioning them can be elaborated.  The continuation gets their free variables, in
declaration order. -/
def withParams {α} : List (Ident × Term) → (Array Lean.Expr → TermElabM α) → TermElabM α
  | [], k => k #[]
  | (id, ty) :: rest, k => do
      let tyE ← Term.elabType ty
      Term.synthesizeSyntheticMVarsNoPostponing
      withLocalDeclD id.getId (← instantiateMVars tyE) fun x =>
        withParams rest fun xs => k (#[x] ++ xs)

/-- Read a `List` literal off an `Expr`. -/
partial def listLit? (e : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then
    return some []
  else if e.isAppOfArity ``List.cons 3 then
    let args := e.getAppArgs
    match ← listLit? args[2]! with
    | some rest => return some (args[1]! :: rest)
    | none => return none
  else
    return none

/-- How many errors a message log holds (used to tell whether the type-checking pass failed). -/
def errorCount (msgs : MessageLog) : Nat :=
  msgs.toList.countP (·.severity == MessageSeverity.error)

/-- Split a solved `?_holeSigᵢ` into the syntax of its parameter types and its return type (for
the `uses` clause of the generated `proc`). -/
def sigSyntax (callee : Term) (sigMVar : Lean.Expr) : TermElabM (Array Term × Term) := do
  let sig ← whnf (← instantiateMVars sigMVar)
  let fail {α} : TermElabM α :=
    throwErrorAt callee
      "module: the signature of this call must elaborate to a literal `procsig (…) -> …`, \
       but it is{indentExpr sig}"
  unless sig.isAppOfArity ``GaudisCrypt.ProcedureSignature.mk 2 do fail
  let args := sig.getAppArgs
  let some ps ← listLit? args[0]! | fail
  let psStx ← ps.toArray.mapM fun p => PrettyPrinter.delab p
  return (psStx, ← PrettyPrinter.delab args[1]!)

/-- The name of the placeholder standing for the module parameter declared at position `i`
inside a callee's `ModuleExpression`. -/
def paramName (i : Nat) : Name := Name.mkSimple s!"_param{i}"

/-- The placeholder for the `i`-th module parameter.  A callee is read back with these in place of
the parameters, because the two consumers need different things there: `X.<f>` substitutes a de
Bruijn `.var` (it is curried over the parameters it uses), `X` a projection of its single argument
tuple. -/
def paramPlaceholder (i : Nat) : Term := mkIdent (paramName i)

/-- Replace the parameter placeholders of `s`: the one for position `i` by `subst[i]`. -/
partial def substParams (subst : Array Term) (s : Syntax) : Syntax :=
  if s.isIdent then
    match (Array.range subst.size).find? fun i => s.getId == paramName i with
    | some i => subst[i]!
    | none => s
  else match s with
    | .node info k args => .node info k (args.map (substParams subst))
    | _ => s

/-- Translate a module-valued term into `ModuleExpression` *syntax*, with the module parameters
(given as `params`, each with the position at which it was declared) becoming `paramPlaceholder`s.

A subterm mentioning no parameter is closed, so it is emitted as `Module.expression ‹subterm›`.
Otherwise the head has to be one of the module operations handled below; anything else is
unfolded and retried, and if that gets stuck the term is rejected.  (Rejecting is the only
option: a Lean function `T → Module _` cannot in general be reflected into a `.abs`.) -/
partial def toModuleExpr (params : List (FVarId × Nat)) (e : Lean.Expr) : TermElabM Term := do
  let e ← instantiateMVars e
  let isParam := fun id => (params.find? (·.1 == id)).isSome
  unless e.hasAnyFVar isParam do
    -- `.expression` as an explicit application: field notation would look the field up under the
    -- head of the type, which for a module type synonym (`TestModule`, `Module.Arr …`) is not
    -- `Module`
    return Syntax.mkCApp ``GaudisCrypt.Module.expression #[← PrettyPrinter.delab e]
  if let .fvar id := e then
    if let some (_, i) := params.find? (·.1 == id) then
      return paramPlaceholder i
  let args := e.getAppArgs
  let n := args.size
  -- the arguments of interest are the last ones (`Module.app` & co. carry leading implicit and
  -- instance arguments), so we count from the end
  let un (ctor : Name) : TermElabM Term := do
    return Syntax.mkCApp ctor #[← toModuleExpr params args[n-1]!]
  let bin (ctor : Name) : TermElabM Term := do
    return Syntax.mkCApp ctor #[← toModuleExpr params args[n-2]!, ← toModuleExpr params args[n-1]!]
  if let .const c _ := e.getAppFn then
    if n ≥ 2 && (c == ``GaudisCrypt.Module.app || c == ``GaudisCrypt.Module.app') then
      return ← bin ``GaudisCrypt.ModuleExpression.app
    if n ≥ 2 && (c == ``GaudisCrypt.Module.pair || c == ``GaudisCrypt.Module.pair') then
      return ← bin ``GaudisCrypt.ModuleExpression.pair
    if n ≥ 1 && (c == ``GaudisCrypt.Module.fst || c == ``GaudisCrypt.Module.fst') then
      return ← un ``GaudisCrypt.ModuleExpression.fst
    if n ≥ 1 && (c == ``GaudisCrypt.Module.snd || c == ``GaudisCrypt.Module.snd') then
      return ← un ``GaudisCrypt.ModuleExpression.snd
    -- `cast`/`cast'` only move between `Module T` and a type synonym for it
    if n ≥ 1 && (c == ``GaudisCrypt.Module.cast || c == ``GaudisCrypt.Module.cast') then
      return ← toModuleExpr params args[n-1]!
  let e' ← whnfCore e
  if e' != e then return ← toModuleExpr params e'
  match ← unfoldDefinition? e with
  | some e' => toModuleExpr params e'
  | none =>
      throwError "module: cannot read{indentExpr e}\nas a module expression built from the \
        module parameters — its head is none of `Module.app`, `Module.fst`, `Module.snd`, \
        `Module.pair` and it cannot be unfolded any further"

/-- The signature of an already-declared procedure, as syntax (`procsig (…) -> …`).  Used for the
type of the generated module, where `ProcedureWithHoles.signature p` would work too but would show
up unevaluated in every hover. -/
def procSig (procId : Ident) : TermElabM Term := do
  let e ← Term.elabTerm (← `(GaudisCrypt.ProcedureWithHoles.signature $procId)) none
  Term.synthesizeSyntheticMVarsNoPostponing
  PrettyPrinter.delab (← whnf (← instantiateMVars e))

/-- Type-check a procedure body with the module parameters in the local context and the *real*
callees in place (each hole callee ascribed to `Module (.proc ?_holeSigᵢ)`), and return, for each
hole, the signature that this elaboration assigns to its `?_holeSigᵢ` together with the callee
read back as a `ModuleExpression` over the parameters (which appear in it as `paramPlaceholder`s).

Holes are made only afterwards, from these signatures — so a call is typed exactly as written
before it loses its callee. -/
def checkBody (paramBs : List (Ident × Term)) (callees : Array Term)
    (body : Term) : TermElabM (Array (Array Term × Term) × Array Term) :=
  withParams paramBs fun fvars => do
    -- create the `?_holeSigᵢ` up front: `elabSyntheticHole` reuses a metavariable of that name
    let mvars ← (Array.range callees.size).mapM fun i =>
      mkFreshExprMVar (Lean.mkConst ``GaudisCrypt.ProcedureSignature)
        (userName := sigHole.sigName i)
    discard <| Term.elabTerm body none
    Term.synthesizeSyntheticMVarsNoPostponing
    let sigs ← (callees.zip mvars).mapM fun (c, mv) => sigSyntax c mv
    let params : List (FVarId × Nat) :=
      (fvars.toList.zipIdx).map fun (x, i) => (x.fvarId!, i)
    -- re-elaborate each callee on its own (same ascription as in the body, whose elaboration has
    -- by now solved `?_holeSigᵢ`) to get hold of its `Expr`
    let exprs ← callees.mapIdxM fun i c => do
      let stx ← `(($c : GaudisCrypt.Module (GaudisCrypt.ModuleTypeRep.proc $(sigHole i))))
      toModuleExpr params (← instantiateMVars (← Term.elabTerm stx none))
    return (sigs, exprs)

/-- A link that inserts `suggestion` over `range` and then moves the cursor to `newSelection`.
Same idea as `Lean.Meta.Hint.textInsertionWidget` — whose link text is fixed to `[apply]` and
which leaves the cursor where it was — and as ProofWidgets' `MakeEditLink`, which needs the
document's URI up front; here it is read from the infoview's position context instead. -/
@[widget_module]
def insertLinkWidget : Widget.Module where
  javascript := "
import * as React from 'react';
import { EditorContext, EnvPosContext } from '@leanprover/infoview';

const e = React.createElement;
export default function ({ range, suggestion, newSelection, hoverText, linkText }) {
  const pos = React.useContext(EnvPosContext)
  const ec = React.useContext(EditorContext)
  async function onClick() {
    await ec.api.applyEdit({ changes: { [pos.uri]: [{ range, newText: suggestion }] } })
    if (newSelection) await ec.revealLocation({ uri: pos.uri, range: newSelection })
  }
  return e('span', {
      onClick,
      title: hoverText,
      className: 'link pointer dim font-code',
      style: { color: 'var(--vscode-textLink-foreground)' }
    },
    linkText)
}"

/-- The width of `s` in UTF-16 code units — what LSP positions count in. -/
private def utf16Width (s : String) : Nat := s.foldl (fun w c => w + c.utf16Size.toNat) 0

/-- Report the declarations a `module` command generated, as
```
Defined:
  X.g.procedure — body of proc g
```
where each *name* is a link that inserts `#check <name>` right after the command and puts the
cursor at the end of the inserted line (the same edit is also offered as a code action).
`declared` pairs each name with a short description of what it is. -/
def logDeclared (ref : Syntax) (declared : Array (Name × String)) : CommandElabM Unit := do
  if declared.isEmpty then return
  -- the edit's range is empty and sits at the command's tail, so applying it *inserts* the
  -- `#check` on the following line rather than overwriting anything
  let some tailPos := ref.getTailPos? | return
  let range : Lean.Syntax.Range := ⟨tailPos, tailPos⟩
  let lspRange := (← getFileMap).utf8RangeToLspRange range
  let mut msg : MessageData := "Defined:"
  for (n, descr) in declared do
    let line := s!"#check {n}"
    let newText := "\n" ++ line
    let title := s!"Insert `{line}`"
    -- end of the inserted line: one line below the command, past the text just written
    let caret : Lsp.Position := ⟨lspRange.start.line + 1, utf16Width line⟩
    -- the code-action (lightbulb) counterpart of the link
    pushInfoLeaf <| .ofCustomInfo {
      stx := Syntax.ofRange (ref.getRange?.getD range)
      value := Dynamic.mk ({ edit := { range := lspRange, newText := newText }
                             codeActionTitle := title
                             suggestion := { suggestion := newText } } :
                           Lean.Meta.Tactic.TryThis.TryThisInfo) }
    let link : MessageData := .ofWidget
      { id := ``insertLinkWidget
        javascriptHash := insertLinkWidget.javascriptHash
        props := return json%
          { range: $(lspRange),
            suggestion: $(newText),
            newSelection: $(({ start := caret, «end» := caret } : Lsp.Range)),
            hoverText: $(title),
            linkText: $(n.toString) } }
      n.toString
    msg := msg ++ m!"\n• {link} — {descr}"
  msg := msg ++ "\n\n(Click to insert `#check symbolname`.)"
  logInfoAt ref msg

/-- What `elabProcedure` leaves for `elabProcModule` to work with. -/
structure ProcResult where
  /-- The procedure's name as written in the declaration. -/
  fn : Ident
  /-- The constant just declared: `X.<f>.procedure`. -/
  declId : Ident
  /-- The positions (in the module's parameter list) of the parameters this procedure uses,
  in declaration order. -/
  usedPos : Array Nat
  /-- Its hole callees as `ModuleExpression`s over the module parameters (which appear in them as
  `paramPlaceholder`s), in hole order. -/
  calleeExprs : Array Term

/-- Declare `X.<f>.procedure` for one `proc f (…) : R { … }` of a `module X (…)` declaration.
Returns `none` if the body does not type-check (the errors have then been reported already). -/
def elabProcedure (nm : Ident) (paramBs : Array (Ident × Term))
    (p : TSyntax `gaudi_module_proc) : CommandElabM (Option ProcResult) := do
  let `(gaudi_module_proc| proc $fn:ident ( $ps:proc_binder,* ) $[: $rty:term]? {
          $[var $locals:proc_binder,* ;]*
          $stmts:gaudi_stmt*
          return $rv:term $[;]?
        } $[;]?) := p | throwUnsupportedSyntax
  -- (`uses` is a keyword, hence the name `hbs?`)
  let mkProc (body : Array (TSyntax `gaudi_stmt))
      (hbs? : Option (Array (TSyntax `hole_binder))) : CommandElabM Term :=
    match hbs? with
    | none | some #[] =>
        `(proc ( $ps,* ) $[: $rty]? { $[var $locals,* ;]* $body* return $rv })
    | some hbs =>
        `(proc ( $ps,* ) uses ( $hbs,* ) $[: $rty]? { $[var $locals,* ;]* $body* return $rv })
  let paramNames := paramBs.toList.map (·.1.getId)
  -- the final (hole) form of the body, and with it the callees in hole order
  let (holeStmts, callees) :=
    (stmts.mapM fun s => rewriteCalls paramNames holeCallee s.raw).run #[]
  -- pass 1: the body with its callees intact, elaborated with the module parameters in the
  -- local context — this is where the whole body (holes included) is type-checked, and what
  -- determines the hole signatures
  let checked ← callees.mapIdxM fun i c =>
    `(GaudisCrypt.Module.procedure
        ($c : GaudisCrypt.Module (GaudisCrypt.ModuleTypeRep.proc $(sigHole i))))
  let (checkStmts, _) :=
    (stmts.mapM fun s => rewriteCalls paramNames (checked[·]!) s.raw).run #[]
  let checkTerm ← mkProc (checkStmts.map (⟨·⟩)) none
  -- the parameters this procedure uses
  let usedPos := (Array.range paramBs.size).filter fun i =>
    callees.any fun c => mentions [paramBs[i]!.1.getId] c.raw
  let errsBefore := errorCount (← get).messages
  let (holeSigs, calleeExprs) ←
    runTermElabM fun _ => checkBody paramBs.toList callees checkTerm
  -- a body that does not type-check has already been reported against its real callees;
  -- elaborating the hole version too would only duplicate the errors
  if errorCount (← get).messages > errsBefore then return none
  -- pass 2: now that they are typed, the parameter calls become holes
  let holeBinders ← holeSigs.mapIdxM fun i (hps, hret) =>
    `(hole_binder| $(holeIdent i):ident : ( $hps,* ) → $hret)
  let procTerm ← mkProc (holeStmts.map (⟨·⟩)) (some holeBinders)
  let declId := mkIdent (nm.getId ++ fn.getId ++ `procedure)
  elabCommand (← `(command| noncomputable def $declId:ident := $procTerm))
  return some { fn, declId, usedPos, calleeExprs }

/-- The `ModuleExpression` of the procedure `r`, with `subst[i]` put for the module parameter
declared at position `i`: either the closed `Module.proc X.<f>.procedure`, or
`Module.procWithHoles X.<f>.procedure` applied to the tuple of its callees.  That tuple is
right-nested and *reversed*, matching `HoleSigs.toModuleTypeRepTuple` (the last-declared hole is
the outermost `.fst`). -/
def procApplied (r : ProcResult) (subst : Array Term) : CommandElabM Term := do
  if r.calleeExprs.isEmpty then
    `(GaudisCrypt.Module.expression (GaudisCrypt.Module.proc $(r.declId)))
  else
    let mut tuple ← `(GaudisCrypt.ModuleExpression.unit)
    for c in r.calleeExprs do
      tuple ← `(GaudisCrypt.ModuleExpression.pair $(⟨substParams subst c⟩) $tuple)
    `(GaudisCrypt.ModuleExpression.app
        (GaudisCrypt.Module.expression (GaudisCrypt.Module.procWithHoles $(r.declId))) $tuple)

/-- The constant `X.<f>` that `elabProcModule` declares for the procedure `r` of `module X`. -/
def procModId (nm : Ident) (r : ProcResult) : Ident := mkIdent (nm.getId ++ r.fn.getId)

/-- Declare the module `X.<f>` of a procedure already declared by `elabProcedure`: either
`Module.proc X.<f>.procedure` (no module parameter used), or `procApplied` abstracted over the
parameters it does use, of type `Module.Arr T₁ (… (Module.Arr Tₖ (Module.Proc sig)))`.  Returns
the constant it declared. -/
def elabProcModule (nm : Ident) (paramBs : Array (Ident × Term)) (r : ProcResult) :
    CommandElabM Ident := do
  let modId := procModId nm r
  if r.calleeExprs.isEmpty then
    elabCommand (← `(command| noncomputable def $modId:ident :=
      GaudisCrypt.Module.proc $(r.declId)))
  else
    let mut ty ← `(GaudisCrypt.Module.Proc $(← runTermElabM fun _ => procSig r.declId))
    for i in r.usedPos.reverse do ty ← `(GaudisCrypt.Module.Arr $(paramBs[i]!.2) $ty)
    -- the `j`-th used parameter is `.var (k-1-j)`: the first one is the outermost binder.  A
    -- parameter outside `usedPos` does not occur, so what it maps to is immaterial.
    let subst := (Array.range paramBs.size).map fun i =>
      match r.usedPos.findIdx? (· == i) with
      | some j => Syntax.mkCApp ``GaudisCrypt.ModuleExpression.var
                    #[Syntax.mkNatLit (r.usedPos.size - 1 - j)]
      | none => paramPlaceholder i
    let mut body ← procApplied r subst
    for _ in r.usedPos do body ← `(GaudisCrypt.ModuleExpression.abs $body)
    elabCommand (← `(command| noncomputable def $modId:ident : $ty :=
      GaudisCrypt.ModuleExpression.toModule (m := $body)))
  return modId

/-- `f x₁ (f x₂ (… xₙ))` — every tuple built here is right-nested, and a one-element one is just
its element (as in `moduletype`, whose product of `n` field types has `n-1` `.prod`s).  `xs` must
not be empty. -/
def rightNest (f : Term → Term → CommandElabM Term) (xs : Array Term) : CommandElabM Term := do
  let mut acc := xs[xs.size - 1]!
  for j in [0 : xs.size - 1] do acc ← f xs[xs.size - 2 - j]! acc
  return acc

/-- If the declared module type is a name introduced by `moduletype` whose fields are exactly the
procedures declared here (same names, order immaterial), its constructor `N.mk`; `none` otherwise.
`N.mk` takes the record `N.Structure`, so the module can then be written
`N.mk { f₁ := …, fₙ := … }` rather than as a nest of `Module.pair`s. -/
def moduletypeMk? (mt? : Option Term) (fns : Array Name) : CommandElabM (Option Ident) := do
  let some mt := mt? | return none
  let `($id:ident) := mt | return none
  let some n ← (try pure (some (← resolveGlobalConstNoOverload id)) catch _ => pure none)
    | return none
  let env ← getEnv
  let structName := n.str "Structure"
  unless env.contains (n.str "mk") && isStructure env structName do return none
  let fields := getStructureFields env structName
  unless fields.size == fns.size && fns.all fields.contains do return none
  return some (mkIdent (n.str "mk"))

/-- The record whose field `i` is `fields[i]`: `N.mk { f₁ := …, fₙ := … }` when `mkId?` is the
constructor of a `moduletype` with exactly these fields (see `moduletypeMk?`), and the right-nested
`Module.pair` of them — which is the same record, only anonymous — otherwise. -/
def mkRecord (mkId? : Option Ident) (procs : Array ProcResult) (fields : Array Term) :
    CommandElabM Term := do
  match mkId? with
  | some mkId =>
      let fs ← procs.mapIdxM fun i r =>
        `(Lean.Parser.Term.structInstField| $(r.fn):ident := $(fields[i]!))
      `($mkId { $fs:structInstField,* })
  | none => rightNest (fun a b => `(GaudisCrypt.Module.pair $a $b)) fields

/-- Declare `X.apply_simp`, the `@[simp]` lemma that applies `X` to its parameters:
```
theorem X.apply_simp (A : T₁) … (Z : Tₙ) :
    Module.app X (Module.pair A (… Z)) = N.mk { f₁ := Module.app X.f₁ A, … }
```
— the record of the procedures, each applied to the parameters *it* uses (`Module.pair` in place of
`N.mk` when the module type is not a `moduletype` name, as in `mkRecord`).  For an empty parameter
list the tuple is the only argument `X` can take, a variable of `Module.Unit`.

Proved from the generic form (`X` applied to a *variable* tuple `t`, whose fields therefore get
`Module.fst`/`Module.snd` chains) by the `module_apply` tactic; rewriting with that form leaves the
projections of the concrete tuple, which `Module.fst_pair`/`Module.snd_pair` collapse. -/
def elabApplySimp (nm : Ident) (paramBs : Array (Ident × Term)) (paramProd : Term)
    (mkId? : Option Ident) (procs : Array ProcResult) : CommandElabM Ident := do
  let n := paramBs.size
  let tId := mkIdent `t
  -- the parameter at position `i`, projected out of the argument tuple `t`
  let proj ← (Array.range n).mapM fun i => do
    let mut e : Term := tId
    for _ in [0 : i] do e ← `(GaudisCrypt.Module.snd $e)
    if i + 1 < n then e ← `(GaudisCrypt.Module.fst $e)
    pure e
  -- the record of the procedures, each applied to the arguments at its `usedPos`
  let recordOf (args : Array Term) : CommandElabM Term := do
    mkRecord mkId? procs (← procs.mapM fun r => do
      let mut e : Term := procModId nm r
      for i in r.usedPos do e ← `(GaudisCrypt.Module.app $e $(args[i]!))
      pure e)
  let paramTerms : Array Term := paramBs.map fun b => b.1
  let rhs ← recordOf paramTerms
  let rhsGeneric ← recordOf proj
  let argTuple : Term ←
    if n == 0 then pure (tId : Term)
    else rightNest (fun a b => `(GaudisCrypt.Module.pair $a $b)) paramTerms
  -- the statement, as a `(x : T) → …` chain (there is no binder syntax to splice into a `theorem`)
  let mut stmt ← `(GaudisCrypt.Module.app $nm $argTuple = $rhs)
  if n == 0 then
    stmt ← `(($tId : GaudisCrypt.Module.Unit) → $stmt)
  else
    for i in [0 : n] do
      let (x, ty) := paramBs[n - 1 - i]!
      stmt ← `(($x : $ty) → $stmt)
  let ids := if n == 0 then #[tId] else paramBs.map (·.1)
  let thmId := mkIdent (nm.getId ++ `apply_simp)
  elabCommand (← `(command| @[simp] theorem $thmId:ident : $stmt := by
    intro $ids*
    have generic : ∀ ($tId : $paramProd),
        GaudisCrypt.Module.app $nm $tId = $rhsGeneric := fun $tId => by module_apply $nm
    rw [generic]
    all_goals simp))
  return thmId

/-- Declare the module `X` itself: the record of its procedures (a right-nested `.pair`, as
`moduletype` nests its fields) — each of them the constant `X.<f>` declared by `elabProcModule`,
applied to the parameters that `f` uses — abstracted over *all* the parameters at once, used or
not, which it takes as one right-nested tuple.  So `X : Module.Arr (Module.Prod T₁ (… Tₙ)) M`, with
`M` the declared module type, degenerating to `Module.Arr Module.Unit M` for an empty parameter list
and to plain `M` when the declaration has no parameter list at all.

A declaration without a module type gets the record of the procedures' own types for `M`, i.e.
`Module.Prod (Module.Proc sig₁) (… (Module.Proc sigₙ))` — which is what a `moduletype` of these
procedures unfolds to anyway, only anonymous.

With no parameter list there is no `.abs`, and no procedure can call a parameter either, so the
whole thing stays at the `Module` level: `X` is then `Module.pair X.f₁ (… X.fₙ)`, with no detour
through `ModuleExpression` and `toModule` — and when the declared module type is a `moduletype`
name `N` with exactly these fields, the named form `N.mk { f₁ := X.f₁, … }` instead.

With a parameter list `X` also gets the `@[simp]` lemma `X.apply_simp` for applying it to one (see
`elabApplySimp`).

Declares nothing (and returns `#[]`) if the declaration has no procedures.  The result lists what
was declared, for `logDeclared`. -/
def elabModule (nm : Ident) (params? : Option (Array (Ident × Term))) (mt? : Option Term)
    (procs : Array ProcResult) : CommandElabM (Array (Name × String)) := do
  if procs.isEmpty then return #[]
  let paramBs := params?.getD #[]
  let n := paramBs.size
  let prod := fun (a b : Term) => `(GaudisCrypt.Module.Prod $a $b)
  let mkId? ← moduletypeMk? mt? (procs.map (·.fn.getId))
  let mt ← match mt? with
    | some mt => pure mt
    | none => rightNest prod (← procs.mapM fun r => do
        `(GaudisCrypt.Module.Proc $(← runTermElabM fun _ => procSig r.declId)))
  let paramProd ←
    if n == 0 then `(GaudisCrypt.Module.Unit) else rightNest prod (paramBs.map (·.2))
  let ty ← match params? with
    | none => pure mt
    | some _ => `(GaudisCrypt.Module.Arr $paramProd $mt)
  if params?.isNone then
    let body ← mkRecord mkId? procs (procs.map fun r => procModId nm r)
    elabCommand (← `(command| noncomputable def $nm:ident : $ty := $body))
    return #[(nm.getId, "the module itself")]
  -- the parameter at position `i` is the `i`-th component of the argument tuple `.var 0`
  let subst ← (Array.range n).mapM fun i => do
    let mut e ← `(GaudisCrypt.ModuleExpression.var 0)
    for _ in [0 : i] do e ← `(GaudisCrypt.ModuleExpression.snd $e)
    if i + 1 < n then e ← `(GaudisCrypt.ModuleExpression.fst $e)
    pure e
  -- each field is the already-declared `X.<f>`, applied to the parameters that `f` uses (in
  -- declaration order, the order `elabProcModule` abstracted them in)
  let fields ← procs.mapM fun r => do
    let mut e ← `(GaudisCrypt.Module.expression $(procModId nm r))
    for i in r.usedPos do e ← `(GaudisCrypt.ModuleExpression.app $e $(subst[i]!))
    pure e
  let mut body ← rightNest (fun a b => `(GaudisCrypt.ModuleExpression.pair $a $b)) fields
  if params?.isSome then body ← `(GaudisCrypt.ModuleExpression.abs $body)
  elabCommand (← `(command| noncomputable def $nm:ident : $ty :=
    GaudisCrypt.ModuleExpression.toModule (m := $body)))
  let thmId ← elabApplySimp nm paramBs paramProd mkId? procs
  return #[(nm.getId, "the module itself"), (thmId.getId, "applying it to its parameters")]

end GaudisCrypt.ModuleDecl

open Lean Elab Command GaudisCrypt.ModuleDecl in
elab_rules : command
  | `(module $nm:ident $[( $params:proc_binder,* )]? $[: $mt:term]? {
        $procs:gaudi_module_proc*
      }) => do
    let paramBs? ← params.mapM fun ps => ps.getElems.mapM fun b => match b with
      | `(proc_binder| $id:ident : $ty:term) => pure (id, ty)
      | _ => throwUnsupportedSyntax
    let paramBs := paramBs?.getD #[]
    let mut declared : Array (Name × String) := #[]
    let mut results : Array ProcResult := #[]
    for p in procs do
      let some r ← elabProcedure nm paramBs p | continue
      results := results.push r
      -- the short names: the `#check`s are inserted right after the command, in the same namespace
      declared := declared.push (r.declId.getId, s!"body of proc {r.fn.getId}")
      let modId ← elabProcModule nm paramBs r
      let used := ", ".intercalate (r.usedPos.toList.map (paramBs[·]!.1.getId.toString))
      declared := declared.push (modId.getId,
        if r.usedPos.isEmpty then s!"proc {r.fn.getId} as a module"
        else s!"proc {r.fn.getId} as a module, in {used}")
    -- `X` itself — only when every procedure made it (a missing field would not type-check)
    if results.size == procs.size then
      declared := declared ++ (← elabModule nm paramBs? mt results)
    logDeclared (← getRef) declared

namespace Experiment
variable [ProgramSpec]

/-

Define a toplevel command `moduletype` that would transform something like the following
to the sequence of commands given below between START and END. Of course, this should not be restricted to allowing only two fields (main, aux)
but an arbitrary number.


moduletype TestModuleTypeRep {
  main : Module (ModuleTypeRep.proc (procsig (String,Nat) -> Bool));
  module aux : Module (ModuleTypeRep.proc (procsig (Nat) -> String)) (ModuleTypeRep.unit));
}

-/

moduletype TestModule {
  -- module main : ModuleTypeRep.proc (procsig (String, Nat) -> Bool);
  proc main (String, Nat) -> Bool;
  module aux : .arr (procmod (Nat) -> String) .unit;
}
#check TestModule.mk

/- ### `ModuleTypeRep` concrete syntax (`procmod`/`.proc`, `.arr`, `.prod`, `.unit`)

`ModuleTypeRep`'s constructors are written by dot notation wherever the expected type says so;
`procmod (…) -> R` abbreviates `.proc (procsig (…) -> R)`.  The infix `→ₘ`/`×ₘ` are *not* these:
they are `Module.Arr`/`Module.Prod`, on module **types** (see below). -/

-- `procmod (…) -> R` = `ModuleTypeRep.proc (procsig (…) -> R)`
example : (procmod (Nat) -> String : ModuleTypeRep) = ModuleTypeRep.proc (procsig (Nat) -> String) := rfl

-- `procmod` composes under `.arr` (its return type binds tighter than any trailing operator)
example : (.arr (procmod (Nat) -> String) .unit : ModuleTypeRep)
    = ModuleTypeRep.arr (ModuleTypeRep.proc (procsig (Nat) -> String)) ModuleTypeRep.unit := rfl

example : (.arr (.proc (procsig (Nat) -> String)) .unit : ModuleTypeRep)
    = ModuleTypeRep.arr (ModuleTypeRep.proc (procsig (Nat) -> String)) ModuleTypeRep.unit := rfl

example : (.prod (procmod () -> Bool) .unit : ModuleTypeRep)
    = ModuleTypeRep.prod (ModuleTypeRep.proc (procsig () -> Bool)) ModuleTypeRep.unit := rfl

-- `procmod` and the `moduletype` proc-field accept the `→` arrow spelling too
example : (procmod (Nat) → String : ModuleTypeRep) = procmod (Nat) -> String := rfl

moduletype UnicodeArrowField {
  proc f (Nat) → Bool;
  module g : .arr (procmod (Bool) → Nat) .unit;
}

-- prints back in the concrete form (`.proc …` and `procmod …` both print as `procmod …`)
#check (.arr (procmod (Nat) -> String) .unit : ModuleTypeRep)
#check (.arr (.proc (procsig (Nat) -> String)) .unit : ModuleTypeRep)
#check (.arr (.prod .unit .unit) .unit : ModuleTypeRep)

/- ### Module-type concrete syntax (`→ₘ` = `Module.Arr`, `×ₘ` = `Module.Prod`) -/

example : (TestModule →ₘ TestModule ×ₘ TestModule) = Module.Arr TestModule
    (Module.Prod TestModule TestModule) := rfl

-- `×ₘ` binds tighter than `→ₘ`, and `→ₘ` is right-associative
example : (TestModule ×ₘ TestModule →ₘ TestModule →ₘ TestModule)
    = Module.Arr (Module.Prod TestModule TestModule) (Module.Arr TestModule TestModule) := rfl

axiom testMain : Module (procmod (String, Nat) -> Bool)
axiom testAux : Module (.arr (procmod (Nat) -> String) .unit)

noncomputable
def myMod := TestModule.mk {main := testMain, aux := testAux}

theorem test : myMod.main = testMain := by
  simp [TestModule.main, myMod]

moduletype M2 {
  proc g() -> Unit;
  proc h() -> Unit;
}


/- ### `module` declarations -/

module X (A : Module.Arr TestModule (Module (procmod () → Unit)), B : TestModule) : M2 {
  proc g() : Unit {
    _ <- call (Module.app A myMod) ();
    _ <- call (Module.app A myMod) ();   -- same callee ⇒ same hole
    -- the `(5 : Nat)` ascription is needed because `paramListToTuple` is not reducible, so the
    -- expected type of the literal is stuck (see the TODO at the end of the file)
    _ <- call (myMod.main)  ("hello", (5 : Nat));
    return ();
  };
  proc h() : Unit {
    return ();
  };
}

-- `g` calls the parameter `A` (⇒ one hole) and the closed module `myMod.main` (⇒ a plain call)
#check (X.g.procedure : proctype () -> Unit uses (() → Unit))
#check (X.h.procedure : proctype () -> Unit)
#print X.g.procedure
#print X
#print X.g

-- `g` uses `A` but not `B`, so `X.g` abstracts over `A` alone; `h` uses no parameter at all
#check (X.g : Module.Arr (Module.Arr TestModule (Module (procmod () → Unit)))
                (Module.Proc (procsig () -> Unit)))
#check (X.h : Module.Proc (procsig () -> Unit))
#print X.g
#print X

-- two parameters, two holes; `B.main` reaches the parameter through a `moduletype` accessor
module Y (A : Module.Arr TestModule (Module (procmod () → Unit)), B : TestModule) : M2 {
  proc g() : Unit {
    _ <- call (B.main) ("hi", (3 : Nat));
    _ <- call (Module.app A myMod) ();
    return ();
  };
  proc h() : Unit { return (); };
}
#check (Y.g.procedure : proctype () -> Unit uses ((String, Nat) → Bool, () → Unit))
#check (Y.g : Module.Arr (Module.Arr TestModule (Module (procmod () → Unit)))
                (Module.Arr TestModule (Module.Proc (procsig () -> Unit))))
-- and it applies to modules of those types, in that order
#check fun (a : Module.Arr TestModule (Module (procmod () → Unit))) (b : TestModule) =>
  (Module.app (Module.app Y.g a) b : Module.Proc (procsig () -> Unit))

-- `X` itself takes *all* the parameters — `B` too, which only `Y` uses — as one tuple
#check (X : Module.Arr (Module.Prod (Module.Arr TestModule (Module (procmod () → Unit))) TestModule)
             M2)
#check (Y : Module.Arr (Module.Prod (Module.Arr TestModule (Module (procmod () → Unit))) TestModule)
             M2)
#print X
-- it applies to a tuple of them, and the fields are then projected out with the `M2` accessors
#check fun (a : Module.Arr TestModule (Module (procmod () → Unit))) (b : TestModule) =>
  (M2.g (Module.app X (Module.pair a b)) : Module (procmod () -> Unit))

-- `X.apply_simp` does that application: each field gets the parameters *it* uses (`g` gets `A`
-- alone, `h` none), so a projection out of an applied module reduces to an applied procedure
#print X.apply_simp
#print Y.apply_simp
example (a : Module.Arr TestModule (Module (procmod () → Unit))) (b : TestModule) :
    M2.g (Module.app X (Module.pair a b))
      = (Module.app X.g a : Module (procmod () -> Unit)) := by simp [M2.g, M2.mk]
example (a : Module.Arr TestModule (Module (procmod () → Unit))) (b : TestModule) :
    M2.h (Module.app X (Module.pair a b)) = (X.h : Module (procmod () -> Unit)) := by
  simp [M2.h, M2.mk]

-- TODO: Something like that should be autogenerated by moduletype command!
lemma M2.mk_g : M2.g (M2.mk s) = s.g := by simp [M2.mk, M2.g]
example (a : Module.Arr TestModule (Module (procmod () → Unit))) (b : TestModule) :
    M2.g (Module.app Y (Module.pair a b))
      = (Module.app (Module.app Y.g a) b : Module (procmod () -> Unit)) := by
      simp only [Y.apply_simp, M2.mk_g]


def M3 := M2

-- the parameter list is optional; without it `X` is the module type itself …
module NoParams : M2 {
  proc g() : Unit { return (); };
  proc h() : Unit { return (); };
}
#check (NoParams.g.procedure : proctype () -> Unit)
#check (NoParams.g : Module.Proc (procsig () -> Unit))
#check (NoParams : M2)
-- (no `NoParams.apply_simp`: with no parameter list there is nothing to apply `NoParams` to)
#check X.apply_simp

-- … whereas an empty one still makes it a function, of the empty tuple
module EmptyParams () : M2 {
  proc g() : Unit { return (); };
  proc h() : Unit { return (); };
}
#check EmptyParams.apply_simp
#check (EmptyParams : Module.Arr Module.Unit M2)

-- the module type is optional too; without it `X` gets the anonymous record of its procedures
module NoType (A : Module.Arr TestModule (Module (procmod () → Unit))) {
  proc g() : Unit {
    _ <- call (Module.app A myMod) ();
    return ();
  };
  proc h() : Bool { return true; };
}
#check (NoType : Module.Arr (Module.Arr TestModule (Module (procmod () → Unit)))
                   (Module.Prod (Module.Proc (procsig () -> Unit))
                                (Module.Proc (procsig () -> Bool))))
-- and `apply_simp` then builds that record with `Module.pair`, there being no `N.mk` to build it
#print NoType.apply_simp
example (a : Module.Arr TestModule (Module (procmod () → Unit))) :
    Module.fst (Module.app NoType a) = (Module.app NoType.g a : Module.Proc (procsig () -> Unit)) :=
  by simp

-- three parameters, so the generic form of `apply_simp` reaches them through the deeper
-- projections `fst (snd t)` and `snd (snd t)` — and `g` takes two of them, in declaration order
module Deep (A : Module.Arr TestModule (Module (procmod () → Unit)), B : TestModule,
             C : Module.Arr TestModule (Module (procmod () → Unit))) : M2 {
  proc g() : Unit {
    _ <- call (Module.app C myMod) ();
    _ <- call (Module.app A myMod) ();
    return ();
  };
  proc h() : Unit {
    _ <- call (B.main) ("hi", (3 : Nat));
    return ();
  };
}
#check (Deep.apply_simp :
  ∀ (A : Module.Arr TestModule (Module (procmod () → Unit))) (B : TestModule)
    (C : Module.Arr TestModule (Module (procmod () → Unit))),
  Module.app Deep (Module.pair A (Module.pair B C))
    = M2.mk { g := Module.app (Module.app Deep.g A) C, h := Module.app Deep.h B })

module NoTypeNoParams {
  proc g() : Unit { return (); };
}
-- a one-procedure record is that procedure (`moduletype` nests its fields the same way)
#check (NoTypeNoParams : Module.Proc (procsig () -> Unit))


end Experiment



-- TODO: When this works, make sure closed procedures have Stmt and Procedure in their types, not StmtWithHoles .empty, ProcedureWithHoles .empty
-- TODO: Make all things not only parseable, but also printable
-- TODO: Allow $-syntax in the lvalues. For individual names it's redundant, but one can use $(...) to construct setters explicitly
-- TODO: Allow _ inside a *tuple* lvalue too (a bare `_` already becomes Setter.throwaway)
-- TODO: `paramListToTuple` is not reducible, so a numeral argument of a `call` has a stuck
--   expected type (`OfNat (paramListToTuple [Nat]) 5`) and needs an ascription.
-- TODO: `X.apply_simp` relates `X` and the `X.f`, but nothing yet relates `X.f` and
--   `X.f.procedure` (`Module.procedure (Module.app X.f A) = X.f.procedure` with the holes filled
--   by `A`'s procedures).
-- TODO: Syntax for writing explicit modules (needed? or def + .mk is sufficient?)
-- Concrete syntax for module types: `procmod (…) -> R` (proc), `.proc`/`.arr`/`.prod`/`.unit` via
--   dot notation for `ModuleTypeRep`, and `→ₘ`/`×ₘ` (`Module.Arr`/`Module.Prod`) on module types.
--   See the `ModuleTypeRep concrete syntax` block above.
