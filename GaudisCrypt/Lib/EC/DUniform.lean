import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.PRHL2

/-!
# EasyCrypt's `duniform` (`theories/distributions/Distr.ec`, theory `MUniform`)

`duniform s`: the uniform distribution on the elements of the list `s` (the empty
sub-distribution for the empty list), with EC's `duniform1E` and `duniformE`; and the list
operations they are stated with, `undup` and `count`.  Names are EasyCrypt's.
-/

namespace GaudisCrypt.EC

variable {α : Type} [DecidableEq α]

/-- `op undup`: the list without its duplicates. -/
def undup (s : List α) : List α := s.dedup

/-- `op count`: the number of elements of `s` that satisfy `p`. -/
def count (p : α → Prop) [DecidablePred p] (s : List α) : ℤ := s.countP fun x => decide (p x)

/-- `op duniform (s : 'a list)`: the uniform distribution on the elements of `s`. -/
noncomputable def duniform (s : List α) : SubProbability α :=
  if h : s.toFinset.Nonempty then SubProbability.uniformOfFinset s.toFinset h else ⊥

/-- The mass of a point under `duniform s`. -/
theorem duniform_apply (s : List α) (x : α) :
    (duniform s).1 {x} = if x ∈ s then (s.toFinset.card : ENNReal)⁻¹ else 0 := by
  unfold duniform
  split_ifs with h hx hx
  · letI : MeasurableSpace α := ⊤
    change (PMF.uniformOfFinset s.toFinset h).toMeasure {x} = _
    rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x),
      PMF.uniformOfFinset_apply_of_mem h (List.mem_toFinset.mpr hx)]
  · letI : MeasurableSpace α := ⊤
    change (PMF.uniformOfFinset s.toFinset h).toMeasure {x} = _
    rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x),
      PMF.uniformOfFinset_apply_of_notMem h (fun h' => hx (List.mem_toFinset.mp h'))]
  · exact absurd ⟨x, List.mem_toFinset.mpr hx⟩ h
  · rfl

/-- The expected value under `duniform s`: the average over the elements of `s`. -/
theorem duniform_expected (s : List α) (f : α → ENNReal) :
    (duniform s).expected f = ∑ x ∈ s.toFinset, f x / s.toFinset.card := by
  rw [SubProbability.expected_eq_tsum, tsum_eq_sum (s := s.toFinset)]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [duniform_apply, if_pos (List.mem_toFinset.mp hx), div_eq_mul_inv]
  · intro x hx
    rw [duniform_apply, if_neg (fun h => hx (List.mem_toFinset.mpr h)), mul_zero]

/-- `lemma duniform1E`. -/
theorem duniform1E (s : List α) (x : α) :
    mu1 (duniform s) x = if x ∈ s then 1 / (size (undup s) : ℝ) else 0 := by
  rw [mu1, duniform_apply]
  split_ifs
  · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div, size, undup, List.card_toFinset]
    norm_cast
  · rfl

/-- `lemma duniformE`. -/
theorem duniformE (s : List α) (E : α → Prop) [DecidablePred E] :
    mu (duniform s) E = (count E (undup s) : ℝ) / (size (undup s) : ℝ) := by
  have hc : (s.toFinset.filter E).card = (s.dedup.filter fun x => decide (E x)).length := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_dedup s).filter _)]
    congr 1; ext x; simp
  have hsum : ∑ x ∈ s.toFinset, indicatorE (E x) / (s.toFinset.card : ENNReal) =
      ((s.toFinset.filter E).card : ENNReal) * (s.toFinset.card : ENNReal)⁻¹ := by
    have hi : ∀ x, indicatorE (E x) = if E x then 1 else 0 := fun x => by
      by_cases h : E x <;> simp [indicatorE, h]
    simp only [div_eq_mul_inv, hi]
    rw [← Finset.sum_mul, Finset.sum_boole]
  rw [mu, duniform_expected, hsum, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, hc, count, undup, size, List.countP_eq_length_filter,
    List.card_toFinset, div_eq_mul_inv]
  norm_cast

end GaudisCrypt.EC
