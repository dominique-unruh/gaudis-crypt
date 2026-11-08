import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECCallUpto
import GaudisCrypt.Logic.RenameReads

/-!
# A closer for what EC leaves to `auto => /#`

    auto_close

EC closes the logical goals its program tactics leave with `smt` (`/#`, `smt(…)`).  We have no
SMT solver (by decision), but those goals come in a few shapes, and `auto_close` takes them
apart the way one does by hand:

* introduce everything, take the hypotheses apart (`∧`, `∃`, `∨`), substitute the equations of
  variables (the states of EC's `sp`: `σ = x.set v τ`);
* simplify the reads through writes everywhere, the hypotheses included (`simp_reads_all`; through
  the inliner's renamings, `rename_reads`), and the
  `glob` of a region past writes outside it (`glob_simp`, EC's implicit `={glob D}`);
* the tests back to propositions (`decide … = true`), indicators of events (`indicatorE P = 1`);
* split the goal (`∧`, `if`), and close each part by `rfl`, an assumption (either way round),
  `trivial`, `omega` (EC's `/#` on counters), or `simp_all`.

It closes the goal or fails, leaving it untouched.  It does not know the lemmas EC's `smt(l)`
is given: state those first (`have := l …`).
-/

namespace GaudisCrypt

open Lean Meta Elab Tactic

/-- `simp_reads` on the goal and every hypothesis (a hypothesis simplified to `False` closes the
goal). -/
elab "simp_reads_all" : tactic => withMainContext do
  let g ← getMainGoal
  let mut g := g
  let mut progress := false
  let hyps := (← g.getDecl).lctx.foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d.fvarId
  for h in hyps do
    let ty ← g.withContext do instantiateMVars (← h.getType)
    unless ← g.withContext (isProp ty) do continue
    let r ← g.withContext do Judgment.simpWithNames PRHLWp.relSimpDecls [] ty
    if r.expr == ty then continue
    progress := true
    match ← applySimpResultToLocalDecl g h r false with
    | none => replaceMainGoal []; return
    | some (_, g') => g := g'
  let ty ← g.withContext do instantiateMVars (← g.getType)
  let r ← g.withContext do Judgment.simpWithNames PRHLWp.relSimpDecls [] ty
  if r.expr != ty then
    progress := true
    g ← applySimpResultToTarget g ty r
  unless progress do throwError "simp_reads_all: no progress"
  replaceMainGoal [g]

/-- **What EC leaves to `auto => /#`**: see the module docstring. -/
syntax "auto_close" : tactic

macro_rules
  | `(tactic| auto_close) => `(tactic| focus (
      -- the `let`s of the conditions first (introduced, they would hide the reads)
      try simp only [] at *
      all_goals intros
      all_goals try casesm* _ ∧ _, ∃ _, _, _ ∨ _
      all_goals try subst_vars
      all_goals try rename_reads
      all_goals try simp only [Setter.throwaway_set] at *
      all_goals try simp_reads_all
      all_goals try glob_simp
      all_goals try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true',
        Bool.not_eq_eq_eq_not, Bool.not_true, not_lt, not_le, and_true, true_and,
        indicatorE_eq_one_iff, if_true, if_false] at *
      -- what the simplification took apart
      all_goals try casesm* _ ∧ _, ∃ _, _, _ ∨ _
      all_goals try subst_vars
      all_goals first
        | done
        | trivial
        | rfl
        | assumption
        | (apply Eq.symm; assumption)
        | omega
        | (apply And.intro <;> auto_close)
        | (split_ifs <;> auto_close)
        | (intro _; auto_close)
        | (simp_all; done)
        | fail "auto_close: a goal is left (state the lemmas EC's `smt` is given, or close it \
            by hand)"
      done))

end GaudisCrypt
