import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Logic.PRHL.Prhl
import GaudisCrypt.Logic.PRHL2

/-!
# EasyCrypt's excepted distributions (`theories/distributions/Dexcepted.ec`)

`d \ P` is `dexcepted d P` (`Distr.lean`).  Only what ported developments use is here: its
expectation, losslessness, and the two-step sampling identity of the theory `TwoStepSampling`
(stated on distributions; EasyCrypt's module `S` and its procedures `direct`/`indirect` are
replaced by the distributions they sample).
-/

namespace GaudisCrypt.EC

variable {α : Type}

open Classical in
/-- The expectation under `d \ P`: the restriction of `d` to `¬ P`, normalized. -/
theorem dexcepted_expected (d : SubProbability α) (P : α → Prop) (hd : is_lossless d)
    (hex : ∃ a, ¬ P a ∧ d.1 {a} ≠ 0) (F : α → ENNReal) :
    (dexcepted d P).expected F =
      (∑' a, if P a then 0 else d.1 {a} * F a) * (∑' a, if P a then 0 else d.1 {a})⁻¹ := by
  obtain ⟨a₀, ha₀, hd₀⟩ := hex
  have h : ∃ hd : is_lossless d, ∃ a ∈ {a | ¬ P a}, d.toPMF hd a ≠ 0 := ⟨hd, a₀, ha₀, hd₀⟩
  rw [dexcepted, dif_pos h, SubProbability.expected_eq_tsum]
  letI : MeasurableSpace α := ⊤
  have hpt : ∀ a, (toSubProbability ((d.toPMF h.1).filter {a | ¬ P a} h.2)).1 {a} =
      ((d.toPMF h.1).filter {a | ¬ P a} h.2) a := fun a =>
    PMF.toMeasure_apply_singleton _ a (MeasurableSet.singleton a)
  simp only [hpt, PMF.filter_apply, Set.indicator, Set.mem_setOf_eq]
  have ht : ∀ a, (d.toPMF h.1) a = d.1 {a} := fun _ => rfl
  simp only [ht, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun a => ?_
  split_ifs <;> simp [mul_comm, mul_assoc]
open Classical in
/-- `lemma dexcepted_ll`: `d \ P` is lossless when `d` is and some `¬ P` outcome has positive
probability (EC's `mu d P < mu d predT`). -/
theorem dexcepted_ll (d : SubProbability α) (P : α → Prop) (hd : is_lossless d)
    (hex : ∃ a, ¬ P a ∧ d.1 {a} ≠ 0) : is_lossless (dexcepted d P) := by
  rw [is_lossless_iff_expected, dexcepted_expected d P hd hex]
  obtain ⟨a₀, ha₀, hd₀⟩ := hex
  simp only [mul_one]
  have hS0 : (∑' a, if P a then 0 else d.1 {a}) ≠ 0 := fun h0 => hd₀ (by
    simpa [ha₀] using ENNReal.tsum_eq_zero.mp h0 a₀)
  have hStop : (∑' a, if P a then 0 else d.1 {a}) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.tsum_le_tsum fun a => ?_).trans
      (d.toPMF hd).tsum_coe.le)
    change _ ≤ d.1 {a}
    split_ifs <;> simp
  exact ENNReal.mul_inv_cancel hS0 hStop

open Classical in
/-- EC's `TwoStepSampling.ll_direct_indirect_eq` (for `dt _ = d`), as an equality of
distributions: sampling `d`, and resampling from `d \ P` if the draw is in `P`, is sampling
`d \ P` (`d` lossless). -/
theorem dexcepted_indirect (d : SubProbability α) (P : α → Prop) (hd : is_lossless d) :
    (d >>= fun r => if P r then dexcepted d P else pure r) = dexcepted d P := by
  refine SubProbability.ext_of_expected fun F => ?_
  rw [SubProbability.expected_bind]
  by_cases hex : ∃ a, ¬ P a ∧ d.1 {a} ≠ 0
  · rw [dexcepted_expected d P hd hex, SubProbability.expected_eq_tsum]
    set S := ∑' a, if P a then 0 else d.1 {a}
    set T := ∑' a, if P a then 0 else d.1 {a} * F a
    set E := T * S⁻¹
    set U := ∑' a, if P a then d.1 {a} else 0
    obtain ⟨a₀, ha₀, hd₀⟩ := hex
    have hsplit : (∑' a, (if P a then dexcepted d P else pure a).expected F * d.1 {a}) =
        U * E + T := by
      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
      refine tsum_congr fun a => ?_
      split_ifs with hp
      · simp only [add_zero]
        rw [dexcepted_expected d P hd ⟨a₀, ha₀, hd₀⟩, mul_comm]
      · simp [expected_pure, mul_comm]
    have hUS : U + S = 1 := by
      rw [← ENNReal.tsum_add]
      have h1 := (d.toPMF hd).tsum_coe
      refine (tsum_congr fun a => ?_).trans h1
      change _ = d.1 {a}
      split_ifs <;> simp
    have hS0 : S ≠ 0 := fun h0 => hd₀ (by
      have := ENNReal.tsum_eq_zero.mp h0 a₀
      simpa [ha₀] using this)
    have hStop : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hUS ▸ le_add_self)
    have hT : T = S * E := by
      simp only [E]
      rw [mul_comm T, ← mul_assoc, ENNReal.mul_inv_cancel hS0 hStop, one_mul]
    rw [hsplit, hT, ← add_mul, hUS, one_mul]
  · have hb : dexcepted d P = ⊥ := by
      rw [dexcepted, dif_neg]
      rintro ⟨_, a, ha, hne⟩
      exact hex ⟨a, ha, hne⟩
    rw [hb, SubProbability.expected_bot, SubProbability.expected_eq_tsum]
    refine ENNReal.tsum_eq_zero.mpr fun a => ?_
    split_ifs with hp
    · simp [SubProbability.expected_bot]
    · have : d.1 {a} = 0 := by by_contra h; exact hex ⟨a, hp, h⟩
      simp [this]

end GaudisCrypt.EC
