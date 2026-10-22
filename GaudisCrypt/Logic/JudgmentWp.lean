import GaudisCrypt.Logic.HoareSplit

/-!
# Backwards wp steps, for every registered judgment

`Judgment.wpStep k` processes the last `k` statements of a judgment's statement one at a time,
from the end:

* deterministic code (`Judgment.detOf?`: assignments, resets, `skip`, sequences and conditionals
  of those) by the judgment's `detLemma` — the postcondition after the state update, the same
  shape in every judgment;
* a sampling by the judgment's `sampleLemma`, a call by its `callLemma` — where judgments
  genuinely differ;

simplifying the postcondition after each step with the judgment's `postSimp`.  `hoare_wp`,
`phoare_wp` and the dispatching `stmt_wp` are this one step.
-/

namespace GaudisCrypt.Judgment

open Lean Meta Elab Tactic

/-- Apply the rule `lem` to the goal `g` (of type `ty`): its conclusion unified with the goal, the
argument of type `Stmt.Det …` (if any) set to `det?`, and the judgment about the remaining
statement — the last argument — returned as the new goal. -/
def applyRule (lem : Name) (g : MVarId) (ty : Lean.Expr) (det? : Option Lean.Expr) :
    MetaM MVarId := do
  let c ← mkConstWithFreshMVarLevels lem
  let (ms, _, concl) ← forallMetaTelescope (← inferType c)
  if let some pf := det? then
    let some hd ← ms.findM? fun m => return (← instantiateMVars (← inferType m)).isAppOf ``Stmt.Det
      | throwError "`{lem}` has no `Stmt.Det` argument"
    unless ← isDefEq hd pf do throwError "`{lem}`: the determinism proof does not fit"
  unless ← isDefEq concl ty do
    throwError "`{lem}` does not apply to{indentExpr ty}"
  let some hJ := ms.back? | throwError "`{lem}` has no arguments"
  let g' ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (← inferType hJ)) (← g.getTag)
  unless ← isDefEq hJ g' do throwError "`{lem}`: cannot set the new judgment"
  g.assign (← instantiateMVars (mkAppN c ms))
  return g'.mvarId!

/-- Simplify argument `i` of the goal with `simpWithNames decls procs`. -/
def simpArg (g : MVarId) (i : Nat) (decls procs : List Name) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let (f, args) := (ty.getAppFn, ty.getAppArgs)
  let some B := args[i]? | throwError "simpArg: no argument {i} in{indentExpr ty}"
  let r ← simpWithNames decls procs B
  let target := mkAppN f (args.set! i r.expr)
  let some h := r.proof? | return ← g.replaceTargetDefEq target
  let motive ← withLocalDeclD `x (← inferType B) fun x =>
    mkLambdaFVars #[x] (mkAppN f (args.set! i x))
  g.replaceTargetEq target (← mkCongrArg motive h)

/-- One backwards step over the last statement of the goal's judgment. -/
def wpOne (g : MVarId) : MetaM MVarId := g.withContext do
  let g ← HoareSplit.hoareSplit 1 g
  let (d, ty) ← descOf g
  let st := stripLets (ty.getArg! d.stmtArg)
  unless st.isAppOf ``StmtWithHoles.seq do
    throwError "wp: the statement is not a sequence:{indentExpr st}"
  let last := stripLets (st.getArg! 2)
  let g ← if let some (_, pf) ← detOf? last then
      let some lem := d.detLemma | throwError "wp: `{d.head}` has no rule for deterministic code"
      applyRule lem g ty (some pf)
    else if last.isAppOf ``StmtWithHoles.sample then
      let some lem := d.sampleLemma | throwError "wp: `{d.head}` has no rule for sampling"
      applyRule lem g ty none
    else if last.isAppOf ``StmtWithHoles.call || last.isAppOf ``StmtWithHoles.call' then
      let some lem := d.callLemma
        | throwError "wp: `{d.head}` has no rule for a call without a specification — use the \
            judgment's call tactic (`hoare_call h`, …)"
      applyRule lem g ty none
    else
      throwError "wp: no wp rule for the statement (a loop needs an invariant):{indentExpr last}"
  simpArg g d.postArg d.postSimp d.postSimprocs

/-- `k` backwards steps (`wpOne`), the last statement first. -/
def wpStep (k : Nat) (g : MVarId) : MetaM MVarId := do
  let mut g := g
  for _ in [0:k] do g ← wpOne g
  return g

/-- `stmt_wp k`: the last `k` statements of any registered judgment's statement, by wp
(`Judgment.wpStep`). -/
elab "stmt_wp " k:num : tactic =>
  liftMetaTactic1 fun g => some <$> wpStep k.getNat g

end GaudisCrypt.Judgment
