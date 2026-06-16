import GaudisCrypt.Language.Programs

/-!
Concrete syntax for programs and procedures — take 2.

This file currently implements ONLY the expression layer (sigil `$`), standalone,
without any program/procedure syntax yet. See `syntax-ideas.md` for the design.
-/

namespace GaudisCrypt.Language.Syntax

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Programs
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
  state : State × S

/-- Anything that can be read to a value `T` in the ambient `CurrentState S`:
program variables (lenses/getters into `State`, or into the full `State × S`), and
anything users later add instances for.  Dispatch is on the concrete type `X` of
the argument, so resolution is never stuck on a metavariable. -/
class Evaluatable (S : Type) (X : Type) (T : outParam Type) where
  eval : (State × S) → X → T

/-- User-facing variable read, with `S` implicit (inferred from the variable's
container in the full case, from the ambient `CurrentState` in the global case).
Pass `(S := …)` to force a particular state. -/
def eval {S X T} [Evaluatable S X T] [cs : CurrentState S] (x : X) : T :=
  Evaluatable.eval cs.state x

/-- The four container shapes, dispatched directly on the argument type.  (No
`Lens → Getter` forwarder: it would overlap these, so we spell out all four.) -/
instance : Evaluatable S (Getter T State) T where
  eval cs x := x.get cs.1
instance : Evaluatable S (Getter T (State × S)) T where
  eval cs x := x.get cs
-- TODO: Needed? (We have Lens->Setter coercion)
instance : Evaluatable S (Lens T State) T where
  eval cs x := x.get cs.1
-- TODO: Needed? (We have Lens->Setter coercion)
instance : Evaluatable S (Lens T (State × S)) T where
  eval cs x := x.get cs

/-! ## Reduction lemmas (so denotations compute)

`simp` reduces all four cases (global/full × getter/lens) to a plain `.get` read.
Making `S` a real parameter (rather than a `cs.L` projection) is what lets the
full-state lemmas match under `simp`. -/

@[simp] theorem eval_getter_global [cs : CurrentState S] (x : Getter T State) :
    eval x = x.get cs.state.1 := rfl

@[simp] theorem eval_getter_full [cs : CurrentState S] (x : Getter T (State × S)) :
    eval x = x.get cs.state := rfl

@[simp] theorem eval_lens_global [cs : CurrentState S] (x : Lens T State) :
    eval x = x.get cs.state.1 := rfl

@[simp] theorem eval_lens_full [cs : CurrentState S] (x : Lens T (State × S)) :
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

end GaudisCrypt.Language.Syntax

/-! ## Experiments for expressions -/

namespace GaudisCrypt.Language.Syntax.Test

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Programs
open GaudisCrypt.Language.Syntax

variable [ProgramSpec]

-- set_option trace.Meta.synthInstance true

axiom a : Lens Nat State
axiom b : Lens Nat State

-- a global variable, full state has trivial locals
#check (GaudiExpr[ $a + 1 ] : Getter Nat (State × Unit))
#check (GaudiExpr[ $a + $b ] : Getter Nat (State × Unit))

-- a full-current-state lens (e.g. a local variable already lifted)
axiom loc : Lens Nat (State × Unit)
#check (GaudiExpr[ $a + $loc ] : Getter Nat (State × Unit))
noncomputable def test := (GaudiExpr[ $a + $loc ] : Getter Nat (State × Unit))
#print test

-- $(...) for a compound lens term
#check (GaudiExpr[ $(a) + 1 ] : Getter Nat (State × Unit))

-- reduction: expressions compute through to plain lens reads
example (st : State × Unit) :
    (GaudiExpr[ $a + 1 ] : Getter Nat (State × Unit)).get st = a.get st.1 + 1 := by
  simp

example (st : State × Unit) :
    (GaudiExpr[ $a + $loc ] : Getter Nat (State × Unit)).get st = a.get st.1 + loc.get st := by
  simp

end GaudisCrypt.Language.Syntax.Test

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

namespace GaudisCrypt.Language.Syntax

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Programs

variable [ProgramSpec]

/-- Lift a program variable used as an l-value into a lens on the full current state
`State × S`.  Dispatch is on the lens's *container* `M`: a global lens (`M = State`)
is lifted with `.ofst`, a full-state lens (`M = State × S`) is kept as-is.  The
content type `A` is deliberately *not* a class parameter — resolution then only needs
`M` (always concrete from the argument), and the result's content unifies with the
expected type as an ordinary, postponable constraint.  (That is what lets a `call`
result l-value resolve even before the callee's `sig` is known.) -/
class LiftLens (S : Type) (M : Type) where
  lift {A : Type} : Lens A M → Setter A (State × S)

instance {S : Type} : LiftLens S State where lift x := x.ofst.toSetter
instance {S : Type} : LiftLens S (State × S) where lift x := x.toSetter

/-- User-facing l-value lift; `S`, the container `M`, and the content `A` are inferred.
The result is a `Setter` (l-values only ever `set`). -/
def liftLens {S A M} [LiftLens S M] (x : Lens A M) : Setter A (State × S) :=
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

/-- Right-nested product (the `paramListToTuple` shape): `[] ↦ Unit`, `[T] ↦ T`. -/
private def mkProdType : List Term → MacroM Term
  | []      => `(Unit)
  | [t]     => pure t
  | t :: ts => do `($t × $(← mkProdType ts))

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
    let paramProd ← mkProdType (paramBs.toList.map (·.2))
    let localProd ← mkProdType (localBs.toList.map (·.2))
    let L ← `($paramProd × $localProd)
    -- the signature
    let paramTys := paramBs.map (·.2)
    let localSigmas ← localBs.mapM fun (_, ty) => `(⟨$ty, inferInstance⟩)
    let retTyTerm ← match retTy with | some r => pure r | none => `(_)
    -- one `let` per name, binding it to its lens into `State × L`
    let mut binds : Array (Ident × Term × Term) := #[]
    for k in [0:np] do
      let (id, ty) := paramBs[k]!
      let chain ← mkChain (navSteps k np ++ [true, false])   -- param: into paramTuple (fst of l)
      binds := binds.push (id, ← `(Lens $ty (State × $L)), chain)
    for j in [0:nl] do
      let (id, ty) := localBs[j]!
      let chain ← mkChain (navSteps j nl ++ [false, false])  -- local: into localTuple (snd of l)
      binds := binds.push (id, ← `(Lens $ty (State × $L)), chain)
    -- holes: a `ProcedureSignature` (no locals) each, folded into a `HoleSigs` context,
    -- and one `let` per name binding it to its `HoleIndex` (last-declared = `.zero`).
    let nh := holeBs.size
    let holeSigTerms ← holeBs.mapM fun (_, ps, ret) =>
      `(({ params := [$(ps.toArray),*], locals := [], ret := $ret } : ProcedureSignature))
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
    let retval ← wrap binds (← `((GaudiExpr[ $ret ] : Getter _ (State × $L))))
    `((⟨$body, $retval⟩ : ProcedureWithHoles $hCtx
        { params := [$paramTys,*], locals := [$localSigmas,*], ret := $retTyTerm }))

end

end GaudisCrypt.Language.Syntax

/-! ## Experiments for programs -/

namespace GaudisCrypt.Language.Syntax.ProgTest

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Programs
open GaudisCrypt.Language.Syntax

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
  c <$ SubProbability.uniform;
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

end GaudisCrypt.Language.Syntax.ProgTest

-- TODO: Try: let combined local/global state be a new structure `ProcedureState [ProgramSpec] localState` (with two fields)
--       Allow only getters/setters on this state in the syntax.
--       Introduce coercions to lift Getters/Setters/Lenses on State to `ProcedureState`.
--       This might avoid the whole mess with the Evaluation/LiftLens instances
-- TODO: When this works, make sure closed procedures have Stmt and Procedure in their types, not StmtWithHoles .empty, ProcedureWithHoles .empty
-- TODO: Create a nice syntax for a `Procedure[WithHoles] {...sig...}` types
-- TODO: Make all things not only parseable, but also printable
-- TODO: Allow $-syntax in the lvalues. For individual names it's redundant, but one can use $(...) to construct setters explicitly
-- TODO: Allow _ in lvalues (translated to Setter.throwaway)
