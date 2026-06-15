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
instance : Evaluatable S (Lens T State) T where
  eval cs x := x.get cs.1
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
    if (e) { … } else { … }       -- the `else` branch is optional
    while (e) { … }
    { … }                         -- a block (sequence)

(`call`/`hole` are deferred to the procedure layer.) -/

namespace GaudisCrypt.Language.Syntax

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Programs

variable [ProgramSpec]

/-- Lift a program variable used as an l-value into a lens on the full current
state `State × S`: a global `Lens A State` via `.ofst`, a full lens unchanged. -/
class LiftLens (S : Type) (X : Type) (A : outParam Type) where
  liftLens : X → Lens A (State × S)

instance : LiftLens S (Lens A State) A where
  liftLens x := x.ofst
instance : LiftLens S (Lens A (State × S)) A where
  liftLens x := x

/-- User-facing l-value lift, with `S` implicit (inferred from the expected
full-state lens type). -/
def liftLens {S X A} [LiftLens S X A] (x : X) : Lens A (State × S) :=
  LiftLens.liftLens (S := S) x

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

syntax "proc" "(" proc_binder,* ")" (" : " term:max)? "{"
         ("var" proc_binder,* ";")?
         gaudi_stmt*
         "return" term (";")?
       "}" : term

macro_rules
  | `(proc ( $params:proc_binder,* ) $[: $retTy:term]? {
        $[var $locals:proc_binder,* ;]?
        $stmts:gaudi_stmt*
        return $ret:term $[;]?
      }) => do
    let paramBs := (← params.getElems.toList.mapM parseBinder).toArray
    let localBs := (← match locals with
      | some ls => ls.getElems.toList.mapM parseBinder
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
    let wrap (inner : Term) : MacroM Term :=
      binds.foldrM (fun (id, ty, val) acc => `(let $id : $ty := $val; $acc)) inner
    -- annotate with the explicit local-state `L` so expressions see `S = L` directly
    -- (the `L = sig.LocalVariableState` check then happens in ordinary elaboration).
    let body ← wrap (← `((GaudiProg[ $stmts* ] : StmtWithHoles .empty $L)))
    let retval ← wrap (← `((GaudiExpr[ $ret ] : Getter _ (State × $L))))
    `((⟨$body, $retval⟩ : ProcedureWithHoles .empty
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

end GaudisCrypt.Language.Syntax.ProgTest

/-! ## Procedure layer (WIP)

Projecting a procedure's params/locals out of their tuple.  A `TuplePath` names a slot
in an arbitrarily nested tuple of binary products (`here`/`left`/`right`); the
`ProjAt` typeclass decomposes the (concrete) tuple type structurally, so
`Lens.nTh path` **deduces both the tuple type `M` and the component type `A` from the
expected output type** — the caller (the `proc` macro) supplies only the path.
Because the path is fully general, the macro can express the *entire*
`Lens T (State × l)` projection as a single path — the `State × l` split, the
`paramTuple × localTuple` split, and the slot within — with no separate `.ofst`/
`.osnd` lifting.  Encoding the path as an inductive, rather than `Nat` arithmetic in
instance indices, keeps typeclass resolution robust. -/

namespace GaudisCrypt.Language.Lens

/-- A navigation path into an arbitrarily nested tuple of binary products.
`here` stops at the current node; `left`/`right` descend into the first/second
component of `A × B` and continue.  The right-nested `paramListToTuple` shape is the
special case: element `k` of `[T₀,…]` is `right^k` then `left here` (or just `here`
for the last, un-wrapped element). -/
inductive TuplePath where
  | here                        -- stop: the current type is the target
  | left  : TuplePath → TuplePath   -- descend into the first component of `A × B`
  | right : TuplePath → TuplePath   -- descend into the second component of `A × B`

/-- `ProjAt p M A`: following path `p` into tuple type `M` lands on component `A`,
with projection lens `proj`.  `M` is an input (taken from the expected type), `A` is
deduced (`outParam`). -/
class ProjAt (p : TuplePath) (M : Type) (A : outParam Type) where
  proj : Lens A M

instance {M : Type} : ProjAt .here M M := ⟨Lens.id⟩
instance {p : TuplePath} {A B Tgt : Type} [g : ProjAt p A Tgt] :
    ProjAt (.left p) (A × B) Tgt := ⟨g.proj.ofst⟩
instance {p : TuplePath} {A B Tgt : Type} [g : ProjAt p B Tgt] :
    ProjAt (.right p) (A × B) Tgt := ⟨g.proj.osnd⟩

set_option linter.dupNamespace false in
/-- The lens projecting the slot named by `p` out of a (possibly nested) tuple.  The
tuple type `M` and component type `A` are deduced from the expected output type, so
the `proc` macro only supplies the path. -/
def Lens.nTh (p : TuplePath) {M A : Type} [g : ProjAt p M A] : Lens A M := g.proj

end GaudisCrypt.Language.Lens

/-! ### `Lens.nTh` examples -/

namespace GaudisCrypt.Language.Syntax.TuplePathTest

open GaudisCrypt.Language.Lens

-- Right-nested tuple `Nat × Bool × Nat` (the `paramListToTuple` shape):
#check (Lens.nTh (.left .here)           : Lens Nat  (Nat × Bool × Nat))   -- first
#check (Lens.nTh (.right (.left .here))  : Lens Bool (Nat × Bool × Nat))   -- middle
#check (Lens.nTh (.right (.right .here)) : Lens Nat  (Nat × Bool × Nat))   -- last (un-wrapped)
#check (Lens.nTh .here                   : Lens Nat  Nat)                  -- singleton

-- Arbitrarily nested tuple `(Nat × Bool) × (String × Nat)`:
#check (Lens.nTh (.left .here)            : Lens (Nat × Bool) ((Nat × Bool) × (String × Nat)))
#check (Lens.nTh (.left (.right .here))   : Lens Bool         ((Nat × Bool) × (String × Nat)))
#check (Lens.nTh (.right (.left .here))   : Lens String       ((Nat × Bool) × (String × Nat)))
#check (Lens.nTh (.right (.right .here))  : Lens Nat          ((Nat × Bool) × (String × Nat)))

end GaudisCrypt.Language.Syntax.TuplePathTest
