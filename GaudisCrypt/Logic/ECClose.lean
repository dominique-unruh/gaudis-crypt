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

/-- `e` is a name (a variable with an accessible name) or a tuple of names. -/
partial def namedTuple (lctx : LocalContext) (e : Lean.Expr) : Bool :=
  let anon (n : Name) := n.hasMacroScopes || n.isInaccessibleUserName
  if e.isFVar then !anon (lctx.get! e.fvarId!).userName
  else if e.isAppOfArity ``Prod.mk 4 then namedTuple lctx (e.getArg! 2) && namedTuple lctx (e.getArg! 3)
  else false

/-- EC's `<<-` on reads: an equation between a read of the state (`FRO.m.get σ.globals`) and a
named variable (EC's `elim* => hs0`) rewrites the read into the name everywhere, so the closer
works with the names (`subst_vars` would eliminate the name instead). -/
elab "subst_reads" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut rules : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  let anon (n : Name) := n.hasMacroScopes || n.isInaccessibleUserName
  for d in lctx do
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    let isRead (e : Lean.Expr) := !e.isFVar && (e.find? fun t => t.isAppOf ``Getter.get ||
      t.isAppOf ``ProgramState.globals).isSome
    -- a name (EC's `elim*` name, `<<-`), or a tuple of names (`(x1, x2)`, EC's `->>`)
    let named (e : Lean.Expr) : Bool := namedTuple lctx e
    let h ← Term.exprToSyntax d.toExpr
    if isRead a && named b then rules := rules.push (← `(Lean.Parser.Tactic.simpLemma| $h:term))
    else if isRead b && named a then
      rules := rules.push (← `(Lean.Parser.Tactic.simpLemma| ← $h:term))
  if rules.isEmpty then return
  evalTactic (← `(tactic| simp only [$rules,*] at *))

/-- The state a read is of: `σ` for `G.get σ` and `G.get σ.globals`. -/
def readState? (e : Lean.Expr) : Option (Lean.Expr × FVarId) :=
  if e.isAppOfArity ``Getter.get 4 then
    let s := e.getArg! 3
    let s := if s.isAppOfArity ``ProgramState.globals 1 then s.appArg! else s
    if s.isFVar then some (e.getArg! 2, s.fvarId!) else none
  else none

/-- EC's memories as one: an equation between reads of the same variable in two states (the frame
`X.get τ = X.get σ` that `conseq` and `call` leave for what the code does not modify, or `={x}`)
rewrites the read of the later state (in the context) into the earlier one's, everywhere.  One
direction for every pair of states, so the rewriting cannot loop. -/
elab "subst_frames" : tactic => withMainContext do
  let g ← getMainGoal
  let lctx ← getLCtx
  let mut thms : SimpTheorems := {}
  let mut rules : Array FVarId := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    let some (Ga, sa) := readState? a | continue
    let some (Gb, sb) := readState? b | continue
    unless sa != sb && Ga == Gb do continue
    let (ia, ib) := ((lctx.get! sa).index, (lctx.get! sb).index)
    thms ← thms.add (.fvar d.fvarId) #[] d.toExpr (inv := ia < ib)
    rules := rules.push d.fvarId
  if rules.isEmpty then return
  -- every hypothesis but the rules themselves, and the goal
  let others := lctx.foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail || rules.contains d.fvarId then acc else acc.push d.fvarId
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simpGoal g ctx (fvarIdsToSimp := others)
  match r with
  | none => replaceMainGoal []
  | some (_, g') => replaceMainGoal [g']

/-- EC's `progress` on implications: a hypothesis `p → q` whose premise `p` is another hypothesis
(up to reducible unfolding) becomes `q`; repeated while one applies. -/
elab "mp_hyps" : tactic => withMainContext do
  let mut g ← getMainGoal
  for _ in [0:32] do
    let lctx ← g.withContext getLCtx
    let mut step : Option (FVarId × Lean.Expr × Lean.Expr) := none
    for d in lctx do
      if d.isImplementationDetail then continue
      let t ← g.withContext (instantiateMVars d.type)
      let .forallE _ p q _ := t | continue
      if q.hasLooseBVars then continue
      unless ← g.withContext (Meta.isProp p) do continue
      for e in lctx do
        if e.isImplementationDetail || e.fvarId == d.fvarId then continue
        if ← g.withContext (withReducible (isDefEq e.type p)) then
          step := some (d.fvarId, mkApp d.toExpr e.toExpr, q); break
      if step.isSome then break
    let some (h, pf, q) := step | break
    let g1 ← g.assert (← g.withContext (pure (lctx.get! h).userName)) q pf
    let (_, g2) ← g1.intro1P
    g ← g2.clear h
  replaceMainGoal [g]

/-- EC's `<<*`: an equation between a named variable (EC's `elim* => hs`) and an anonymous one
(a read generalized by the closer) eliminates the anonymous one, so the names stay. -/
elab "subst_named" : tactic => withMainContext do
  let mut g ← getMainGoal
  for _ in [0:64] do
    let lctx ← g.withContext getLCtx
    let mut found : Option FVarId := none
    for d in lctx do
      if d.isImplementationDetail then continue
      let some (_, a, b) := (← g.withContext (instantiateMVars d.type)).eq? | continue
      unless a.isFVar && b.isFVar do continue
      let anon (n : Name) := n.hasMacroScopes || n.isInaccessibleUserName
      let (da, db) := (lctx.get! a.fvarId!, lctx.get! b.fvarId!)
      if anon da.userName && !anon db.userName then
        found := some a.fvarId!; break
      if anon db.userName && !anon da.userName then
        found := some b.fvarId!; break
    let some x := found | break
    g ← g.withContext (substVar g x)
  replaceMainGoal [g]

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
  all_goals try norm_decide
  all_goals try glob_tuples
  all_goals try casesm* _ ∧ _
  all_goals try mp_hyps
  all_goals try casesm* _ ∧ _
  all_goals try subst_named
  all_goals try subst_reads
  all_goals try subst_vars
  all_goals try glob_reads
  all_goals try subst_frames
  all_goals try rename_reads
  all_goals try simp only [Setter.throwaway_set] at *
  all_goals try simp_reads_all
  all_goals try glob_simp
  -- … and in the hypotheses
  all_goals try simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at *
  all_goals try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true',
    Bool.not_eq_eq_eq_not, Bool.not_true, not_lt, not_le, and_true, true_and,
    indicatorE_eq_one_iff, if_true, if_false, Prod.mk.injEq, ite_self] at *
  -- what the simplification took apart
  all_goals try casesm* _ ∧ _, ∃ _, _, _ ∨ _
  all_goals try mp_hyps
  all_goals try casesm* _ ∧ _
  all_goals try subst_frames
  all_goals try subst_named
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
  -- the hypotheses back under their names (EC's `elim*` names, `inv0`, …)
  let (_, g) ← g.introNP hyps.size
  replaceMainGoal [g]

/-- **EC's `smt(l₁, …)`**: `auto_close`'s preprocessing, the reads of the states as variables
(`generalize_reads_all`), their equations substituted, then `grind` with the lemmas `lᵢ`. -/
syntax "smt_close" (" [" Lean.Parser.Tactic.grindParam,* "]")? : tactic

macro_rules
  | `(tactic| smt_close) => `(tactic| smt_close [])
  | `(tactic| smt_close [$ls,*]) => `(tactic| focus (
      auto_prep
      all_goals try generalize_reads_all
      all_goals try subst_named
      all_goals try subst_vars
      all_goals grind [GaudisCrypt.EC.oget_some, $ls,*]))

end GaudisCrypt
