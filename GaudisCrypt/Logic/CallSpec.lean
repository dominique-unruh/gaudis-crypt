import GaudisCrypt.Logic.FelTactic
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Syntax.PHoareSyntax

/-!
# EasyCrypt's inline specifications: `call (: P ==> Q)`, `byphoare (: P ==> _)`

EC states the judgment about a callee, or the one a probability is read from, where it is used:

    phoare_call (: P ==> Q)          -- EC's `call (: P ==> Q)` in a `phoare`
    phoare_call (: P ==> Q) ≤ r      -- … with the callee's own bound
    hoare_call (: P ==> Q)           -- EC's `call (: P ==> Q)` in a `hoare`
    byphoare (: P ==> _)             -- EC's `byphoare (: P ==> _)`

`P` and `Q` are written as in `phoare[ M : P ==> Q ]` (`Syntax/PHoareSyntax.lean`): `P` reads
the callee's parameters and the globals, `Q` its result `res` and the globals.  The judgment
about the callee becomes the **first** goal, tagged `spec` (EC's order); the code before the call
is the second.  In a `phoare` the callee's relation is the goal's, and its bound the goal's, which
must then not depend on the state, or the one written after the parenthesis.

`hoare_call (: inv)` (`Logic/FelTactic.lean`, an invariant of an abstract module's oracles) is
the form without `==>`.
-/

namespace GaudisCrypt.CallSpec

open Lean Meta Elab Tactic

/-- The procedure argument `p` of the call rule `rule`, once its conclusion is unified with `ty`
(a judgment about a statement ending in a call).  The state is left as it was. -/
def calleeOf (rule : Name) (ty : Lean.Expr) : MetaM Lean.Expr := withoutModifyingState do
  let c ← mkConstWithFreshMVarLevels rule
  let cTy ← inferType c
  let names := cTy.getForallBinderNames
  let some i := names.findIdx? (· == `p) | throwError "`{rule}` has no argument `p`"
  let (ms, _, concl) ← forallMetaTelescope cTy
  unless ← isDefEq concl ty do
    throwError "the last statement is not a call:{indentExpr ty}"
  let p ← instantiateMVars ms[i]!
  if p.hasExprMVar then throwError "cannot read the callee off{indentExpr ty}"
  return p

/-- The term `stx` (a judgment, `phoare[ M : P ==> Q ] ρ r` or `hoare[ M : P ==> Q ]`)
elaborated, its errors thrown (not logged and replaced by `sorry`). -/
def elabSpec (stx : Term) : TacticM Lean.Expr := do
  let e ← Term.withoutErrToSorry do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    pure e
  instantiateMVars e

/-- A fresh goal of type `ty` with the tag `tag`. -/
def specGoal (ty : Lean.Expr) (tag : Name) : MetaM Lean.Expr :=
  mkFreshExprSyntheticOpaqueMVar ty tag

end CallSpec

open Lean Meta Elab Tactic CallSpec PHoareWp HoareWp

/-- **EC's `call (: P ==> Q)`** in a `phoare` judgment, see the module docstring. -/
syntax "phoare_call" " (" ": " term " ==> " term ")" (phoare_rel term:max)? : tactic

elab_rules : tactic
  | `(tactic| phoare_call (: $P ==> $Q) $[$rel? $r?]?) => withMainContext do
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    let #[_, _, _, ρ, bound] ← phoareParts ty | unreachable!
    let rule := if ρ.isAppOf ``Eq then ``phoareStmt_call_eq
      else if ρ.isAppOf ``GE.ge then ``phoareStmt_call_ge else ``phoareStmt_call_le
    -- the callee, read off the split goal (`phoareCallStep` splits it itself)
    let p ← withoutModifyingState do
      calleeOf rule (← instantiateMVars (← (← phoareSplit 1 g).getType))
    let pT ← Term.exprToSyntax p
    let spec ← match rel?, r? with
      | some rel, some r => elabSpec (← `(phoare[ $pT : $P ==> $Q ] $rel $r))
      | _, _ => do
        -- the goal's relation and its bound, which must not read the state
        let bound ← whnfR bound
        let .lam _ _ c _ := bound
          | throwError "phoare_call: the goal's bound is not a function of the state:\
              {indentExpr bound}"
        if c.hasLooseBVars then
          throwError "phoare_call: the goal's bound{indentExpr bound}\nreads the state; give \
            the callee's: `phoare_call (: P ==> Q) ≤ r`"
        let rel ← if ρ.isAppOf ``Eq then `(phoare_rel| =)
          else if ρ.isAppOf ``GE.ge then `(phoare_rel| ≥) else `(phoare_rel| ≤)
        elabSpec (← `(phoare[ $pT : $P ==> $Q ] $rel ($(← Term.exprToSyntax c))))
    let h ← specGoal spec `spec
    let g' ← phoareCallStep h g
    replaceMainGoal [h.mvarId!, g']

/-- **EC's `call (: P ==> Q)`** in a Hoare triple, see the module docstring. -/
syntax "hoare_call" " (" ": " term " ==> " term ")" : tactic

elab_rules : tactic
  | `(tactic| hoare_call (: $P ==> $Q)) => withMainContext do
    let g ← getMainGoal
    let p ← withoutModifyingState do
      let g ← HoareSplit.hoareSplit 1 g
      let gq :: _ ← g.apply (← mkConstWithFreshMVarLevels ``hoare_seq)
        | throwError "hoare_call: `hoare_seq` does not apply"
      calleeOf ``hoare_call_wp (← instantiateMVars (← gq.getType))
    let spec ← elabSpec (← `(hoare[ $(← Term.exprToSyntax p) : $P ==> $Q ]))
    let h ← specGoal spec `spec
    let gs ← hoareCallStep h g
    replaceMainGoal (h.mvarId! :: gs)

/-- **EC's `byphoare (: P ==> _)`**: `byphoare` (`Logic/PrTactics.lean`) with the precondition
`P` of the judgment, written as in `phoare[ M : P ==> Q ]`, instead of `arg = a ∧ glob = m`; the
side condition `P` at the run's arguments and memory is tried as `byphoare`'s are.  `P` may be
`_` (EC's `byphoare (: _ ==> _)`): `True`. -/
syntax "byphoare" " (" ": " term " ==> " "_" ")" : tactic

elab_rules : tactic
  | `(tactic| byphoare (: $P ==> _)) => withMainContext do
    let (rel, l, r) ← PrTactics.goalRel
    let (rule, Pr, x) ← match rel, PrTactics.prParts? l, PrTactics.prParts? r with
      | ``Eq, some Pr, _ => pure (``Procedure.toReal_Pr_eq_of_phoareProc, Pr, r)
      | ``LE.le, some Pr, _ => pure (``Procedure.toReal_Pr_le_of_phoareProc, Pr, r)
      | ``LE.le, none, some Pr => pure (``Procedure.le_toReal_Pr_of_phoareProc, Pr, l)
      | ``GE.ge, some Pr, _ => pure (``Procedure.le_toReal_Pr_of_phoareProc, Pr, r)
      | _, _, _ => throwError "byphoare: expected `Pr[ … ] ≤ x`, `= x` or `≥ x`"
    if rel == ``GE.ge then evalTactic (← `(tactic| show _ ≤ _))
    -- EC's `byphoare (: _ ==> _)`: no precondition
    let P ← if P.raw.isOfKind ``Lean.Parser.Term.hole then `(True) else pure P
    let spec ← elabSpec (← `(phoare[ $(← Term.exprToSyntax Pr[1]!) : $P ==> True ] = 0))
    let preT ← Term.exprToSyntax (spec.getArg! 1)
    let sigT ← Term.exprToSyntax Pr[0]!
    let xT ← Term.exprToSyntax x
    let ruleId := mkIdent rule
    if rule != ``Procedure.le_toReal_Pr_of_phoareProc then evalTactic (← `(tactic|
        refine $ruleId (sig := $sigT) (A := $preT) (r := fun _ _ => ENNReal.ofReal $xT)
          ?judgment ?hA ?hr ?hx))
    else evalTactic (← `(tactic|
        refine $ruleId (sig := $sigT) (A := $preT) (r := fun _ _ => ENNReal.ofReal $xT)
          ?judgment ?hA ?hr))
    let gs ← getGoals
    -- the quotation's tags are hygienic: compared, and left, without their macro scopes
    for g in gs do g.setTag (← g.getTag).eraseMacroScopes
    let judgment ← gs.filterM fun g => return (← g.getTag) == `judgment
    let left ← PrTactics.closeSide (gs.filter (!judgment.contains ·))
    -- the judgment restated as `phoare[ M : P ==> E ] ≤ x` writes it, the event `E` read back
    -- off the probability (`Syntax/PrSyntax.lean`), so that it prints so
    let relT ← if rel == ``Eq then `(phoare_rel| =)
      else if rule == ``Procedure.le_toReal_Pr_of_phoareProc then `(phoare_rel| ≥)
      else `(phoare_rel| ≤)
    let judgment ← judgment.mapM fun j => j.withContext do
      try
        -- `Pr[ M (a₁, …) @ &m : E ]`: `E` is its tenth part
        let stx ← PrettyPrinter.delab (mkApp (mkConst ``NNReal.toReal)
          (mkAppN (← mkConstWithFreshMVarLevels ``Procedure.Pr) Pr))
        unless stx.raw.getNumArgs == 11 && stx.raw[0].isToken "Pr[ " do return j
        let E : Term := ⟨stx.raw[9]⟩
        let T ← elabSpec (← `(phoare[ $(← Term.exprToSyntax Pr[1]!) : $P ==> $E ]
          $relT (ENNReal.ofReal $xT)))
        if ← isDefEq T (← j.getType) then j.replaceTargetDefEq T else return j
      catch _ => return j
    setGoals (judgment ++ left)

end GaudisCrypt
