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

end GaudisCrypt.PHoareSeqTest
