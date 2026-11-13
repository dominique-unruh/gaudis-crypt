import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECAutoStrict

/-!
# The closer on goals about values: `ec_prep`, `ec_progress`, `ec_close`

    ec_values     -- a goal `∀ σ, …` about program states: every read a value, or an error
    ec_prep       -- introduce, take the hypotheses apart, substitute, simplify the tests
    ec_progress   -- EC's `progress`: `ec_prep`, split the goal, close what closes
    ec_close      -- EC's `auto => /#`: the same, an error if a goal is left

The closer works in two phases.

**First the states go** (`ec_values`): a goal `∀ σ, P` or `∀ σ₁ σ₂, P` about program states (the
side goal of a rule: the guards of an `if`, a `conseq`) is brought to the read normal form and
every read is generalized to a value, as `ec_skip` does (`Logic/ReadNorm.lean`); **a state that
survives is an error** naming the place.  A goal that is not of that shape (after `ec_auto` or
`ec_skip` it is already about values) is left as it is.  The same is done at states bound further
in (EC's final memories, `P → ∀ τ₁ τ₂, frames → Q`, of a `while` or `conseq`), when the
introduction reaches them.  A memory that is in the context (EC's `&m`; the other side's memory
in the side goal of a one-sided `rcond`) is not bound by the goal: its reads, in the goal and the
hypotheses, are made values after the introduction (`generalize_reads_all`), without the check
that it does not survive.

**Then logic**, on a goal about values.  What `auto_prep` (`Logic/ECClose.lean`) does about
states (reads through writes, frames, `glob`, renamings) has nothing to do there, and what is
left of it is logic.  `ec_prep` is that part alone, in `auto_prep`'s order:

* introduce everything: a value under the name of its binder (`x`, `RO_m`, `x₁`: the names the
  strict `skip` gave, usable in the proof), a hypothesis without a name;
* take the hypotheses apart (`∧`, `∃`, `∨`), use an implication whose premise is a hypothesis
  (`mp_hyps`), substitute the equations of variables (a named one stays, `subst_named`), a tuple
  of variables by components (`(p, n) = e` as `p = e.1`, `n = e.2`, `split_pair_eqs`: what EC's
  `sp` leaves for `(p, n) <- e`; `auto_prep` does not have this step);
* the tests back to propositions (`decide … = true`), indicators of events, pair equations;
* take apart and substitute what that made.

No step of the second phase looks at a state.

The old tactics (`auto_prep`, `auto_progress`, `auto_close`) are unchanged
(`notes/SHA3/TacticReview.md`, step 3).
-/

namespace GaudisCrypt.ECProgress

open Lean Meta

/-- Introduce every leading binder of the goal (as it is spelled: no unfolding): one that is not
a hypothesis under its own name, a hypothesis without a name.  At a binder that is a program state
(the final memories under the hypotheses of a `while` or `conseq` goal, `P → ∀ τ₁ τ₂, …`) the
rest of the goal is first brought to values, as at the top (`ReadNorm.generalizeStrict`: an error
if such a state survives). -/
partial def introAll (tac : String) (g : MVarId) : MetaM MVarId := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  match ty with
  | .forallE _ dom _ _ =>
      if dom.isConstOf ``ProgramState then
        introAll tac (← ReadNorm.generalizeStrict tac g)
      else if ← isProp dom then introAll tac (← g.intro1).2
      else introAll tac (← g.intro1P).2
  | .letE .. => introAll tac (← g.intro1P).2
  | _ => return g

/-- The first phase: a goal `∀ σ, P` or `∀ σ₁ σ₂, P` about program states in read normal form,
every read a value (`ReadNorm.generalizeStrict`: an error if a state survives); any other goal
as it is. -/
def valuesFirst (tac : String) (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  match ty with
  | .forallE _ dom _ _ =>
      if dom.isConstOf ``ProgramState then ReadNorm.generalizeStrict tac g else return g
  | _ => return g

/-- `e` is a variable or a tuple of variables. -/
partial def varTuple (e : Lean.Expr) : Bool :=
  e.isFVar || (e.isAppOfArity ``Prod.mk 4 && varTuple (e.getArg! 2) && varTuple (e.getArg! 3))

/-- One hypothesis `(x, y) = e` or `e = (x, y)` — a tuple of variables and a term that is not
written as a pair — replaced by the two component equations, `x = e.1` and `y = e.2`.  `none` if
there is no such hypothesis. -/
def splitPairEq (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    let isPair (e : Lean.Expr) : Bool := e.isAppOfArity ``Prod.mk 4
    let (l₁, r₁, l₂, r₂) ←
      if isPair a && varTuple a && !isPair b then
        pure (a.getArg! 2, ← mkAppM ``Prod.fst #[b], a.getArg! 3, ← mkAppM ``Prod.snd #[b])
      else if isPair b && varTuple b && !isPair a then
        pure (← mkAppM ``Prod.fst #[a], b.getArg! 2, ← mkAppM ``Prod.snd #[a], b.getArg! 3)
      else continue
    let T ← whnf (← inferType a)
    let lvls := T.getAppFn.constLevels!
    let proj (c : Name) : Lean.Expr := mkAppN (mkConst c lvls) #[T.getArg! 0, T.getArg! 1]
    let g ← g.assert d.userName (← mkEq l₂ r₂) (← mkCongrArg (proj ``Prod.snd) d.toExpr)
    let g ← g.assert d.userName (← mkEq l₁ r₁) (← mkCongrArg (proj ``Prod.fst) d.toExpr)
    let (_, g) ← g.introNP 2
    return some (← g.clear d.fvarId)
  return none

end GaudisCrypt.ECProgress

open Lean Elab Tactic in
/-- EC's `sp` over `(x, y) <- e` leaves `(x, y) = e`: every such hypothesis (a tuple of variables
equal to a term not written as a pair) becomes the component equations `x = e.1`, `y = e.2`,
which the substitution then uses. -/
elab "split_pair_eqs" : tactic => do
  let mut g ← getMainGoal
  for _ in [0:64] do
    let some g' ← GaudisCrypt.ECProgress.splitPairEq g | break
    g := g'
  replaceMainGoal [g]

open Lean Elab Tactic in
/-- **The closer's first phase**: a goal about one or two program states, `∀ σ, P`, in read normal
form with every read a value; an error if a state survives.  Any other goal is left as it is. -/
elab "ec_values" : tactic =>
  liftMetaTactic1 fun g => some <$> GaudisCrypt.ECProgress.valuesFirst "ec_values" g

open Lean Elab Tactic in
/-- Introduce every leading binder: a value under its own name, a hypothesis without a name
(`ec_intro` stops at the first hypothesis; this goes on).  A program state among the binders is
not introduced: its reads are generalized to values first (an error if it survives). -/
elab "ec_intros" : tactic =>
  liftMetaTactic1 fun g => some <$> GaudisCrypt.ECProgress.introAll "ec_intros" g

/-- **The preparation of a goal about values**: see the module docstring. -/
macro "ec_prep" : tactic => `(tactic| (
  ec_values
  ec_intros
  -- a memory of the context (the other side's, in the side goal of a one-sided rule): its reads
  -- values too
  all_goals try generalize_reads_all
  all_goals try casesm* _ ∧ _, ∃ _, _, _ ∨ _
  all_goals try mp_hyps
  all_goals try casesm* _ ∧ _
  all_goals try split_pair_eqs
  all_goals try subst_named
  all_goals try subst_vars
  all_goals try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true',
    Bool.not_eq_eq_eq_not, Bool.not_true, not_lt, not_le, and_true, true_and,
    GaudisCrypt.indicatorE_eq_one_iff, if_true, if_false, Prod.mk.injEq, ite_self] at *
  -- what the simplification took apart
  all_goals try casesm* _ ∧ _, ∃ _, _, _ ∨ _
  all_goals try mp_hyps
  all_goals try casesm* _ ∧ _
  all_goals try subst_named
  all_goals try subst_vars))

/-- **EC's `progress`** on a goal about values: `ec_prep`, the goal split (`∧`, `if`), each part
closed by `rfl`, an assumption (either way round), `trivial`, `omega` or `simp_all`; the parts it
cannot close are left. -/
syntax "ec_progress" : tactic

macro_rules
  | `(tactic| ec_progress) => `(tactic| focus (
      ec_prep
      all_goals first
        | done
        | trivial
        | rfl
        | assumption
        | (apply Eq.symm; assumption)
        | omega
        | (apply And.intro <;> ec_progress)
        | (split_ifs <;> ec_progress)
        | (intro _; ec_progress)
        | simp_all_done_safe
        | skip))

/-- **EC's `auto => /#`** on a goal about values: `ec_progress`, an error if a goal is left
(then nothing is changed). -/
macro "ec_close" : tactic => `(tactic| focus (
  ec_progress
  first
    | done
    | fail "ec_close: a goal is left (state the lemmas EC's `smt` is given, or close it by hand)"))
