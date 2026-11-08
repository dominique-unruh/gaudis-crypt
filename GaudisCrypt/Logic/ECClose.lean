import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECCallUpto
import GaudisCrypt.Logic.RenameReads
import GaudisCrypt.Lib.EC.List

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

/-- The steps `auto_close` and `auto_progress` share: introduce, take the hypotheses apart,
substitute, simplify the reads and the tests (see the module docstring). -/
macro "auto_prep" : tactic => `(tactic| (
  -- the `let`s of the conditions first (introduced, they would hide the reads)
  try simp only [] at *
  all_goals intros
  all_goals try casesm* _ ∧ _, ∃ _, _, _ ∨ _
  all_goals try subst_vars
  all_goals try rename_reads
  all_goals try simp only [Setter.throwaway_set] at *
  all_goals try simp_reads_all
  all_goals try glob_simp
  -- … and in the hypotheses
  all_goals try simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at *
  all_goals try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true',
    Bool.not_eq_eq_eq_not, Bool.not_true, not_lt, not_le, and_true, true_and,
    indicatorE_eq_one_iff, if_true, if_false] at *
  -- what the simplification took apart
  all_goals try casesm* _ ∧ _, ∃ _, _, _ ∨ _
  all_goals try subst_vars))

/-- **What EC leaves to `auto => /#`**: see the module docstring. -/
syntax "auto_close" : tactic

macro_rules
  | `(tactic| auto_close) => `(tactic| focus (
      auto_prep
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

/-- **EC's `progress`** (`auto => />; progress`): `auto_close`'s steps, the goals it cannot close
left (split as far as it goes), for the lemmas EC's `smt` calls are given. -/
syntax "auto_progress" : tactic

macro_rules
  | `(tactic| auto_progress) => `(tactic| focus (
      auto_prep
      all_goals first
        | done
        | trivial
        | rfl
        | assumption
        | (apply Eq.symm; assumption)
        | omega
        | (apply And.intro <;> auto_progress)
        | (split_ifs <;> auto_progress)
        | (intro _; auto_progress)
        | (simp_all; done)
        | skip))

end GaudisCrypt

namespace GaudisCrypt

open Lean Meta Elab Tactic in
/-- `generalize_reads_all`: every read of a variable in a state (`x.get σ`, `X.get σ.globals`,
`σ` a local) a fresh variable, in the goal and the hypotheses: EC's view of a memory as its
variables' values. -/
elab "generalize_reads_all" : tactic => withMainContext do
  let g ← getMainGoal
  -- the propositions among the hypotheses go into the goal, and come back after
  let hyps ← (← getLCtx).foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    if ← isProp d.type then return acc.push d.fvarId else return acc
  let (_, g) ← g.revert hyps (preserveOrder := true)
  let g ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let reads ← IO.mkRef (#[] : Array Lean.Expr)
    Meta.forEachExpr t fun e => do
      unless e.isAppOfArity ``Getter.get 4 && !e.hasLooseBVars do return
      let st := e.appArg!
      let ok := st.isFVar || (st.isAppOfArity ``ProgramState.globals 1 && st.appArg!.isFVar)
      if ok && !(← reads.get).contains e then reads.modify (·.push e)
    let rs ← reads.get
    if rs.isEmpty then return g
    let args := rs.map fun r => ({ expr := r, xName? := some `v } : GeneralizeArg)
    let (_, g) ← g.generalize args
    return g
  let (_, g) ← g.intros
  replaceMainGoal [g]

/-- **EC's `smt(l₁, …)`**: `auto_close`'s preprocessing, the reads of the states as variables
(`generalize_reads_all`), their equations substituted, then `grind` with the lemmas `lᵢ`. -/
syntax "smt_close" (" [" Lean.Parser.Tactic.grindParam,* "]")? : tactic

macro_rules
  | `(tactic| smt_close) => `(tactic| smt_close [])
  | `(tactic| smt_close [$ls,*]) => `(tactic| focus (
      auto_prep
      all_goals try generalize_reads_all
      all_goals try subst_vars
      all_goals grind [GaudisCrypt.EC.oget_some, $ls,*]))

end GaudisCrypt
