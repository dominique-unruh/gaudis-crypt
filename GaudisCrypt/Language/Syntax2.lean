import GaudisCrypt.Language.Programs
import GaudisCrypt.Language.Modules

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

syntax "proctype " "(" term,* ")" " -> " term (" uses " "(" hole_sig,* ")")? : term

open Lean in
macro_rules
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
      `(proctype ( $ps,* ) -> $r)
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
        `(proctype ( $ps,* ) -> $r uses ( $holeSyns,* ))
  | _ => throw ()

/-! ### Procedure *signature* syntax

`procsig (T, U, V) -> W` is the bare `ProcedureSignature.mk [T, U, V] W` (the same surface
form as `proctype`, minus the holes — a signature has none).  By construction
`Procedure (procsig …) = proctype …`.  The unexpander is on `ProcedureSignature.mk`, so any
signature with a literal parameter list prints back as `procsig (…) -> …`. -/

syntax "procsig " "(" term,* ")" " -> " term : term

macro_rules
  | `(procsig ( $params:term,* ) -> $ret:term) => `(ProcedureSignature.mk [$params,*] $ret)

open Lean PrettyPrinter in
@[app_unexpander ProcedureSignature.mk]
def unexpandProcSig : Unexpander
  | `($_ [$ps,*] $r) => `(procsig ( $ps,* ) -> $r)
  | _ => throw ()

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
  c <$ GaudisCrypt.Language.Semantics.SubProbability.uniform;
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


end GaudisCrypt.Language.Syntax.ProgTest

-- TODO: When this works, make sure closed procedures have Stmt and Procedure in their types, not StmtWithHoles .empty, ProcedureWithHoles .empty
-- TODO: Make all things not only parseable, but also printable
-- TODO: Allow $-syntax in the lvalues. For individual names it's redundant, but one can use $(...) to construct setters explicitly
-- TODO: Allow _ in lvalues (translated to Setter.throwaway)


/-


-/


open GaudisCrypt.Language.Programs
open GaudisCrypt.Language.Modules

/-- A field `f : Module T` of a `moduletype` declaration. -/
syntax moduletypeField := "module " ident " : " term ";"

/-- `moduletype Name { module f₁ : T₁; … ; module fₙ : Tₙ }` declares a record-like module
type, where each `Tᵢ` is a `ModuleType`.  It expands to: `Name := Module (ModuleType.prod T₁
(… Tₙ))` (right-nested product of the field types), a record `Name.Structure` with fields
`fᵢ : Module Tᵢ`, accessors `Name.fᵢ` (via `Module.fst`/`Module.snd`), a constructor
`Name.mk`, a destructor `Name.structure`, and the two round-trip `@[simp]` lemmas
`Name.mk_destruct` / `Name.destruct_mk`. -/
syntax "moduletype " ident "{" moduletypeField* "}" : command

open Lean Elab Command in
elab_rules : command
  | `(moduletype $nm:ident { $fields:moduletypeField* }) => do
      let n := fields.size
      if n == 0 then throwError "moduletype needs at least one field"
      -- per field: the field name and its `ModuleType`
      let fns ← fields.mapM fun f => match f with
        | `(moduletypeField| module $fn:ident : $_ ;) => pure fn
        | _ => throwUnsupportedSyntax
      let Ts ← fields.mapM fun f => match f with
        | `(moduletypeField| module $_ : $T:term ;) => pure T
        | _ => throwUnsupportedSyntax
      -- the field/accessor types are `Module Tᵢ`
      let fts ← Ts.mapM fun T => `(Module $T)
      -- right-nested product of the underlying types
      let prodT ← Ts.pop.foldrM (fun T acc => `(ModuleType.prod $T $acc)) Ts.back!
      -- generated names
      let nb := nm.getId
      let structId := mkIdent (nb.str "Structure")
      let ctorId   := mkIdent ((nb.str "Structure").str "mk")
      let mkId     := mkIdent (nb.str "mk")
      let structFn := mkIdent (nb.str "structure")
      let accIds   := fns.map fun f => mkIdent (nb ++ f.getId)
      let projId : Nat → Ident := fun i => mkIdent ((nb.str "Structure") ++ fns[i]!.getId)
      let mId := mkIdent `m
      let sId := mkIdent `s
      -- (1) the module type
      elabCommand (← `(def $nm := Module $prodT))
      -- (2) the record structure
      elabCommand (← `(structure $structId where $[$fns:ident : $fts:term]*))
      -- (3) accessors: field `i` is `fst (snd^i m)`, or `snd^(n-1) m` for the last
      for i in [0:n] do
        let accId := accIds[i]!
        let ft := fts[i]!
        let mut e : Term := mId
        for _ in [0:i] do e ← `(Module.snd $e)
        if i + 1 < n then e ← `(Module.fst $e)
        elabCommand (← `(def $accId ($mId : $nm) : $ft := $e))
      -- (4) constructor: right-nested `Module.pair`
      let mut mkBody : Term ← `($(projId (n-1)) $sId)
      for i in [0:n-1] do
        let j := n - 2 - i
        let pj := projId j
        mkBody ← `(Module.pair ($pj $sId) $mkBody)
      elabCommand (← `(@[reducible] def $mkId ($sId : $structId) : $nm := $mkBody))
      -- (5) destructor
      let args ← (Array.range n).mapM fun i => do
        let accId : Ident := accIds[i]!
        `($accId $mId)
      elabCommand (← `(def $structFn ($mId : $nm) : $structId := $ctorId $args*))
      -- (6) / (7) round-trip lemmas
      let baseLemmas : Array Ident := #[mkId, structFn] ++ accIds
      elabCommand (← `(@[simp] theorem $(mkIdent (nb.str "mk_destruct")) ($sId : $structId) :
          $structFn ($mkId $sId) = $sId := by simp [$[$baseLemmas:ident],*]))
      let dmLemmas : Array Ident := baseLemmas.push (mkIdent `Module.pair_fst_snd)
      elabCommand (← `(@[simp] theorem $(mkIdent (nb.str "destruct_mk")) ($mId : $nm) :
          $mkId ($structFn $mId) = $mId := by simp [$[$dmLemmas:ident],*]))

namespace Experiment
variable [ProgramSpec]

/-

Define a toplevel command `moduletype` that would transform something like the following
to the sequence of commands given below between START and END. Of course, this should not be restricted to allowing only two fields (main, aux)
but an arbitrary number.


moduletype TestModuleType {
  main : Module (ModuleType.proc (procsig (String,Nat) -> Bool));
  module aux : Module (ModuleType.proc (procsig (Nat) -> String)) (ModuleType.unit));
}

-/

moduletype TestModuleType {
  module main : ModuleType.proc (procsig (String, Nat) -> Bool);
  module aux : ModuleType.arr (ModuleType.proc (procsig (Nat) -> String)) ModuleType.unit;
}



axiom testMain : Module (ModuleType.proc (procsig (String,Nat) -> Bool))
axiom testAux : Module (ModuleType.arr (ModuleType.proc (procsig (Nat) -> String)) (ModuleType.unit))

noncomputable
def myMod := TestModuleType.mk {main := testMain, aux := testAux}

theorem test : myMod.main = testMain := by
  simp [TestModuleType.main, myMod]

end Experiment
