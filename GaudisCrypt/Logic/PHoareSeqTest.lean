import GaudisCrypt.Logic.PHoareSeq
import GaudisCrypt.Syntax.PHoareSyntax

/-! # Tests for `phoare_seq` -/

namespace GaudisCrypt.PHoareSeqTest

open GaudisCrypt

global_var x : Bool
global_var y : Bool

-- two coins: both heads with probability at most `1/2 · 1/2`, split at the first flip over the
-- event "the first is heads" (the bounds `1` on events are closed by `phoare_seq` itself)
example : phoare[ True ==> §x = true ∧ §y = true ] ≤ ((1 / 2) * (1 / 2)) {
  x <$ SubProbability.uniform;
  y <$ SubProbability.uniform;
} := by
  phoare_seq 1 : (§x = true) (1 / 2) (1 / 2) 1 0 True
  case invariant =>
    hoare_wp 1
    hoare_skip
    intros; trivial
  case first_E =>
    phoare_wp 1
    phoare_skip
    intros
    simp
  case second_E =>
    phoare_wp 1
    phoare_skip
    intros
    simp_all
  case second_notE =>
    phoare_wp 1
    phoare_skip
    intros
    simp_all
  case bound =>
    intros
    simp

-- EC's `seq 1 : true` on a lossless goal: the two flips, one at a time
/--
trace: case first
⊢ phoare[ True ==> 1 ] = 1 {
      x <$ SubProbability.uniform;
}

case second
⊢ phoare[ True ==> 1 ] = 1 {
      y <$ SubProbability.uniform;
}
---
warning: The following tactic starts with 2 goals and ends with 2 goals, 2 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : phoare[ True ==> 1 ] = 1 {
  x <$ SubProbability.uniform;
  y <$ SubProbability.uniform;
} := by
  phoare_seq_lossless 1 : (True)
  trace_state
  case first =>
    phoare_wp 1
    phoare_skip
    intros
    simp [ENNReal.inv_two_add_inv_two]
  case second =>
    phoare_wp 1
    phoare_skip
    intros
    simp [ENNReal.inv_two_add_inv_two]

end GaudisCrypt.PHoareSeqTest
