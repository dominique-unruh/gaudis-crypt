import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ReadNorm

/-!
# EC's `auto` on the strict `skip`

    ec_auto     -- EC's `auto` on a Hoare triple, a `phoare` judgment or a relational judgment

`wp` over the code from the end (on a relational judgment also `rnd` on the samplings, as
`equiv_auto`); when the code is used up, `ec_skip` (`Logic/ReadNorm.lean`): the implication in
read normal form, every read a value, **an error if a state survives**; then what EC's `auto`
closes by itself.  When the code is not used up (a call, a loop), the judgment is left there, as
`hoare_auto`/`phoare_auto`/`equiv_auto` leave it.

The difference to those three: one normalizer on every path, and no goal silently left about the
states.  They are unchanged; proofs move to `ec_auto` one file at a time
(`notes/SHA3/TacticReview.md`, step 3).
-/

namespace GaudisCrypt.ECAutoStrict

open Lean Meta Elab Tactic

/-- Is the code of the judgment `g` used up (`skip`, on both sides of a relational one)? -/
def codeIsSkip (g : MVarId) : MetaM Bool := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let isSkip (st : Lean.Expr) : MetaM Bool := do return (← ECSim.lastKind st) == .skip
  if ty.isAppOfArity ``prhlStmt 4 then
    return (← isSkip (ty.getArg! 1)) && (← isSkip (ty.getArg! 2))
  if ty.isAppOf ``hoareStmt || ty.isAppOf ``phoareStmt then
    let (d, ty') ← Judgment.descOf g none
    return ← isSkip (ty'.getArg! d.stmtArg)
  return false

end GaudisCrypt.ECAutoStrict

open Lean Meta Elab Tactic GaudisCrypt ECAuto ECAutoStrict in
/-- **EC's `auto`, strict**: see the module docstring. -/
elab "ec_auto" : tactic => do
  -- a side goal `∀ σ₁, hoare[ … ]` (EC's `forall &1`, from a one-sided rule): the memory first
  evalTactic (← `(tactic| intros))
  let ty := (← instantiateMVars (← (← getMainGoal).getType)).cleanupAnnotations
  if ty.isAppOf ``prhlStmt then
    evalTactic (← `(tactic| (
      (try stmt_wp)
      (repeat (first
        | (equiv_rnd; try stmt_wp)
        | (equiv_rnd{1}; try stmt_wp)
        | (equiv_rnd{2}; try stmt_wp))))))
  else if ty.isAppOf ``hoareStmt || ty.isAppOf ``phoareStmt then
    liftMetaTactic1 fun g => do return some (← splitPairReads (← wpAll g))
  else throwError "ec_auto: not a Hoare, phoare or relational judgment about statements:\
    {indentExpr ty}"
  -- the code used up: the strict `skip`
  if ← codeIsSkip (← getMainGoal) then
    liftMetaTactic1 fun g => some <$> ReadNorm.ecSkip g
    -- what EC's `auto` closes by itself (closed, or left as `ec_skip` left it)
    evalTactic (← `(tactic| try (intros; first
      | rfl
      | trivial
      | exact le_rfl
      | (simp_all; done)
      | ((try simp only [decide_eq_true_eq, decide_eq_false_iff_not] at *)
         casesm* _ ∧ _; (try subst_vars); glob_reads; first | assumption | (simp_all; done)))))

open Lean Meta Elab Tactic in
/-- **`ec_intro`**: introduce the values a strict `skip` generalized (the goal's leading binders
that are not hypotheses) under their own names (`x`, `x₁`, `rnCount`, …), so that the proof refers
to them by name.  The hypotheses stay in the goal (`intro h`, `rintro ⟨h₁, h₂⟩`). -/
elab "ec_intro" : tactic => liftMetaTactic1 fun g => g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let n ← forallTelescope ty fun xs _ => do
    let mut n := 0
    for x in xs do
      if ← isProp (← inferType x) then break
      n := n + 1
    return n
  let (_, g) ← g.introNP n
  return some g
