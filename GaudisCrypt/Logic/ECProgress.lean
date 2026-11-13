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
`ec_skip` it is already about values) is left as it is.

**Then logic**, on a goal about values.  What `auto_prep` (`Logic/ECClose.lean`) does about
states (reads through writes, frames, `glob`, renamings) has nothing to do there, and what is
left of it is logic.  `ec_prep` is that part alone, in `auto_prep`'s order:

* introduce everything: a value under the name of its binder (`x`, `RO_m`, `x₁`: the names the
  strict `skip` gave, usable in the proof), a hypothesis without a name;
* take the hypotheses apart (`∧`, `∃`, `∨`), use an implication whose premise is a hypothesis
  (`mp_hyps`), substitute the equations of variables (a named one stays, `subst_named`);
* the tests back to propositions (`decide … = true`), indicators of events, pair equations;
* take apart and substitute what that made.

No step of the second phase looks at a state: a hypothesis that mentions one (a memory of the
context) is left as it is.

The old tactics (`auto_prep`, `auto_progress`, `auto_close`) are unchanged
(`notes/SHA3/TacticReview.md`, step 3).
-/

namespace GaudisCrypt.ECProgress

open Lean Meta

/-- Introduce every leading binder of the goal (as it is spelled: no unfolding): one that is not
a hypothesis under its own name, a hypothesis without a name. -/
partial def introAll (g : MVarId) : MetaM MVarId := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  match ty with
  | .forallE _ dom _ _ =>
      if ← isProp dom then introAll (← g.intro1).2 else introAll (← g.intro1P).2
  | .letE .. => introAll (← g.intro1P).2
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

end GaudisCrypt.ECProgress

open Lean Elab Tactic in
/-- **The closer's first phase**: a goal about one or two program states, `∀ σ, P`, in read normal
form with every read a value; an error if a state survives.  Any other goal is left as it is. -/
elab "ec_values" : tactic =>
  liftMetaTactic1 fun g => some <$> GaudisCrypt.ECProgress.valuesFirst "ec_values" g

open Lean Elab Tactic in
/-- Introduce every leading binder: a value under its own name, a hypothesis without a name
(`ec_intro` stops at the first hypothesis; this goes on). -/
elab "ec_intros" : tactic => liftMetaTactic1 fun g => some <$> GaudisCrypt.ECProgress.introAll g

/-- **The preparation of a goal about values**: see the module docstring. -/
macro "ec_prep" : tactic => `(tactic| (
  ec_values
  ec_intros
  all_goals try casesm* _ ∧ _, ∃ _, _, _ ∨ _
  all_goals try mp_hyps
  all_goals try casesm* _ ∧ _
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
