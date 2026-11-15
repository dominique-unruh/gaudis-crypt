import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Lib.EC.IsUniform
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.PRHL2
import GaudisCrypt.Logic.ECHints

/-!
# EasyCrypt's `FixedBiased` (`theories/distributions/DBool.ec`)

The biased coin of a fixed bias: the theory's `op p : {real | 0%r < p < 1%r} as in01_p` is the
class `Params`, `dbiased` the distribution that gives `true` with probability `p`.  A clone
gives the bias (`clone import GaudisCrypt.EC.FixedBiased as Biased with op p <- p`).  Names
are EasyCrypt's.
-/

namespace GaudisCrypt.EC.FixedBiased

/-- The theory's parameter: a bias strictly between `0` and `1`. -/
class Params where
  /-- `op p : real`. -/
  p : ℝ
  /-- `axiom in01_p : 0%r < p < 1%r`. -/
  in01_p : 0 < p ∧ p < 1

export Params (p in01_p)

variable [Params]

theorem ge0_p : 0 ≤ (p : ℝ) := in01_p.1.le

theorem ge0_1p : 0 ≤ 1 - (p : ℝ) := by linarith [(in01_p (self := ‹_›)).2]

/-- `op dbiased`: `true` with probability `p`, `false` with probability `1 - p`. -/
noncomputable def dbiased : SubProbability Bool :=
  toSubProbability (PMF.ofFintype (fun b => ENNReal.ofReal (if b then p else 1 - p)) (by
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [← ENNReal.ofReal_add ge0_p ge0_1p]; simp))

/-- The mass of a point. -/
theorem dbiased_apply (b : Bool) :
    dbiased.1 {b} = ENNReal.ofReal (if b then p else 1 - p) := by
  letI : MeasurableSpace Bool := ⊤
  change (PMF.ofFintype _ _).toMeasure {b} = _
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton b), PMF.ofFintype_apply]

/-- `lemma dbiased1E`. -/
theorem dbiased1E (b : Bool) : mu1 dbiased b = if b then p else 1 - p := by
  rw [mu1, dbiased_apply, ENNReal.toReal_ofReal]
  split_ifs
  · exact ge0_p
  · exact ge0_1p

/-- The expected value under the biased coin. -/
theorem dbiased_expected (f : Bool → ENNReal) :
    dbiased.expected f = f true * ENNReal.ofReal p + f false * ENNReal.ofReal (1 - p) := by
  rw [SubProbability.expected_eq_tsum, tsum_fintype, Fintype.sum_bool, dbiased_apply,
    dbiased_apply]
  simp

/-- `lemma dbiasedE`. -/
theorem dbiasedE (E : Bool → Prop) [DecidablePred E] :
    mu dbiased E = (if E true then p else 0) + (if E false then 1 - p else 0) := by
  have hi : ∀ b, indicatorE (E b) ≠ ⊤ := fun b => by
    simp only [indicatorE]; split_ifs <;> simp
  rw [mu, dbiased_expected,
    ENNReal.toReal_add (ENNReal.mul_ne_top (hi _) ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top (hi _) ENNReal.ofReal_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ge0_p,
    ENNReal.toReal_ofReal ge0_1p]
  by_cases h1 : E true <;> by_cases h2 : E false <;> simp [indicatorE, h1, h2]

/-- `lemma supp_dbiased`. -/
theorem supp_dbiased (x : Bool) : x ∈ dbiased.support :=
  SubProbability.mem_support_of_ne_zero (by
    rw [dbiased_apply]
    cases x <;> simp [(in01_p (self := ‹_›)).1, (in01_p (self := ‹_›)).2])

/-- `lemma dbiased_ll`. -/
theorem dbiased_ll : is_lossless dbiased := by
  rw [is_lossless_iff_expected, dbiased_expected, one_mul, one_mul,
    ← ENNReal.ofReal_add ge0_p ge0_1p]
  simp

attribute [ec_random] dbiased_ll

end GaudisCrypt.EC.FixedBiased
