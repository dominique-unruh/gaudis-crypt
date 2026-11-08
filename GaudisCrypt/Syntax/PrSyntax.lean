import GaudisCrypt.Syntax.PHoareSyntax
import GaudisCrypt.Syntax.ModuleApplicationSyntax

/-!
# Concrete syntax for probabilities

EasyCrypt's `Pr[ M.f(a₁, …, aₙ) @ &m : E ]`:

    Pr[ M (a₁, …, aₙ) @ &m : E ]

is the probability that the procedure `M`, run on the arguments `a₁, …, aₙ` from the globals
`m : VariableAssignment`, ends with a result and globals satisfying the event `E` — the real
number `(Procedure.Pr p (a₁, …, aₙ) m E : ℝ)` (`Logic/PHoare.lean`).  As in EC it is a real, so
that differences and absolute values of probabilities are what they look like.

* The subject `M` is what the procedure judgments take (`hoare[ M : … ]`, `phoare[ M : … ]`): a
  procedure, or a procedure module (a `module`'s `X.f`, `Module.app X A`, …), at `term:max`.
* The arguments are Lean terms, as many as the procedure has parameters (none: `M ()`).  A
  single term for a procedure with several parameters is the whole argument tuple.
* The memory `m` follows `&` (EC's memory names), at `term:max`.
* The event `E` is read like the postcondition of `phoare[ M : … ]`: `§res` is the result, `§x`
  a global, `§allGlobals` the whole global state.  A `Bool` event is coerced, so EC's `: res` is
  `: §res`.

It prints back in the same form (`#roundtrip`, `PrSyntaxTest.lean`).
-/

namespace GaudisCrypt

open Lean

syntax ppGroup("Pr[ " term:max " (" term,* ")" " @ " "&" term:max " : " term " ]") : term

open Elab Term Meta in
elab_rules : term <= expectedType?
  | `(Pr[ $M:term ( $args,* ) @ & $mem:term : $ev:term ]) => do
    let (_, procTerm, sig) ← procedureOf M
    -- the signature known before the arguments are read (`()` against `ParamType ?sig` would
    -- be stuck)
    synthesizeSyntheticMVarsNoPostponing
    let sig ← instantiateMVars sig
    let params ← whnf (mkApp (mkConst ``ProcedureSignature.params) sig)
    let some tys ← ModuleDecl.listLit? params
      | throwErrorAt M m!"the parameter list of this procedure's signature is not a list \
          literal:{indentExpr params}"
    let n := tys.length
    let as := args.getElems
    -- one term for several parameters is the argument tuple itself
    unless as.size == n || (as.size == 1 && n ≥ 2) do
      throwErrorAt M "this procedure takes {n} argument(s), but {as.size} are given"
    let argsT : Term ← match as.size with
      | 0 => `(())
      | 1 => pure as[0]!
      | _ => `(($(as[0]!), $(as.extract 1 as.size),*))
    let paramTy ← exprToSyntax (← whnf (mkApp (mkConst ``ProcedureSignature.ParamType) sig))
    let retTy ← exprToSyntax (← whnf (mkApp (mkConst ``ProcedureSignature.ret) sig))
    -- the event in the shape of `phoare[ M : … ]`'s postcondition (`res` bound, read at
    -- `⟨σ, init⟩`), which is what lets it print back
    let resId := mkIdent `res
    let stId := mkIdent `σ
    let evT ← `(fun ($resId : $retTy) ($stId : VariableAssignment) =>
      let $resId := (Getter.mk fun _ => $resId : Getter _ ProgramState)
      (GaudiExpr[ $ev ] : Getter Prop ProgramState).get
        (⟨$stId, VariableAssignment.init⟩ : ProgramState))
    elabTerm (← `(NNReal.toReal (Procedure.Pr (sig := $(← exprToSyntax sig)) $procTerm
      ($argsT : $paramTy) $mem $evT))) expectedType?

/-! ## Printing -/

section Printing
open PrettyPrinter Delaborator SubExpr Meta

/-- The `n` components of an argument tuple built by `Prod.mk` (right-nested, as
`typeListToTuple`), delaborated; `none` if it is not built that way. -/
private partial def delabTupleArgs : Nat → DelabM (Option (Array Term))
  | 0 => return some #[]
  | 1 => return some #[← delab]
  | n + 1 => do
    unless (← getExpr).isAppOfArity ``Prod.mk 4 do return none
    let hd ← withNaryArg 2 delab
    let some tl ← withNaryArg 3 (delabTupleArgs n) | return none
    return some (#[hd] ++ tl)

/-- Print `NNReal.toReal (Procedure.Pr p a m E)` as `Pr[ M (a₁, …, aₙ) @ &m : E ]`, when `E` has
the shape the elaborator builds. -/
@[delab app.NNReal.toReal]
private def delabPr : Delab := do
  guardSurfaceSyntax
  let e ← getExpr
  guard (e.getAppNumArgs == 1)
  let pr := e.appArg!
  guard (pr.isAppOfArity ``Procedure.Pr 5)
  let some 1 := packedCondLets? (pr.getArg! 4) | failure
  let sig := pr.getArg! 0
  let some tys ← ModuleDecl.listLit? (← whnf (mkApp (mkConst ``ProcedureSignature.params) sig))
    | failure
  withNaryArg 0 do
    let (names, ev) ← withNaryArg 4 (delabProcCond 1)
    guard (names == #[`res])
    let callee ← withNaryArg 1 do
      if (procModule? (← getExpr)).isSome then withNaryArg 1 delab else delab
    -- a tuple that is not a literal prints as one term, which the elaborator also reads
    let args ← withNaryArg 2 do
      match ← delabTupleArgs tys.length with
      | some as => pure as
      | none => pure #[← delab]
    let mem ← parenBound (← withNaryArg 3 delab)
    `(Pr[ $callee:term ( $args,* ) @ & $mem : $ev ])

end Printing

end GaudisCrypt
