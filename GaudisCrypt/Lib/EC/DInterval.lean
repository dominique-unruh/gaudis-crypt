import GaudisCrypt.Lib.EC.DUniform
import GaudisCrypt.Lib.EC.ListRange
import GaudisCrypt.Lib.EC.IsUniform
import GaudisCrypt.Lib.EC.Dexcepted

/-!
# EasyCrypt's `DInterval` (`theories/distributions/DInterval.ec`)

`dinter i j` (EC's `[i..j]`): the uniform distribution on the integers from `i` to `j`.  Only
what ported developments use is here.  Names are EasyCrypt's.
-/

namespace GaudisCrypt.EC

/-- The elements of `range m n` are distinct. -/
theorem range_nodup (m n : ℤ) : (range m n).Nodup := by
  unfold range iota_
  exact (List.nodup_range).map fun a b h => by simpa using h

/-- `lemma size_range`. -/
theorem size_range (m n : ℤ) : size (range m n) = max 0 (n - m) := by
  simp only [size, range, iota_, List.length_map, List.length_range]
  omega

/-- `undup (range m n) = range m n`. -/
theorem undup_range (m n : ℤ) : undup (range m n) = range m n :=
  (range_nodup m n).dedup

/-- `duniform s` is lossless for a list with an element. -/
theorem duniform_ll {α : Type} [DecidableEq α] (s : List α) (hs : s ≠ []) :
    is_lossless (duniform s) := by
  rw [is_lossless_iff_expected, duniform_expected]
  have hne : s.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil s hs
    exact ⟨x, List.mem_toFinset.mpr hx⟩
  rw [Finset.sum_const, nsmul_eq_mul, one_div]
  exact ENNReal.mul_inv_cancel (by simpa using hne.card_pos.ne') (ENNReal.natCast_ne_top _)

/-- `op dinter (i j : int) = duniform (range i (j + 1))`: EC's `[i..j]`. -/
noncomputable def dinter (i j : ℤ) : SubProbability ℤ := duniform (range i (j + 1))

/-- `lemma dinter1E`. -/
theorem dinter1E (i j x : ℤ) :
    mu1 (dinter i j) x = if i ≤ x ∧ x ≤ j then 1 / ((j - i + 1 : ℤ) : ℝ) else 0 := by
  rw [dinter, duniform1E, undup_range, size_range]
  have hx : x ∈ range i (j + 1) ↔ i ≤ x ∧ x ≤ j := by rw [mem_range]; omega
  by_cases h : i ≤ x ∧ x ≤ j
  · rw [if_pos (hx.mpr h), if_pos h, max_eq_right (by omega)]
    congr 2; ring
  · rw [if_neg (fun h' => h (hx.mp h')), if_neg h]

/-- `lemma supp_dinter`. -/
theorem supp_dinter (i j x : ℤ) : x ∈ (dinter i j).support ↔ i ≤ x ∧ x ≤ j := by
  have hx : x ∈ range i (j + 1) ↔ i ≤ x ∧ x ≤ j := by rw [mem_range]; omega
  rw [← hx, SubProbability.mem_support_iff]
  change ((dinter i j).1 {x}).toNNReal ≠ 0 ↔ _
  rw [dinter, duniform_apply]
  split_ifs with h
  · refine ⟨fun _ => h, fun _ => ?_⟩
    have hc : (range i (j + 1)).toFinset.card ≠ 0 :=
      (Finset.card_pos.mpr ⟨x, List.mem_toFinset.mpr h⟩).ne'
    simp [hc]
  · simp [h]

/-- `lemma dinter_ll`. -/
theorem dinter_ll (i j : ℤ) (h : i ≤ j) : is_lossless (dinter i j) :=
  duniform_ll _ fun h0 => by
    have : i ∈ range i (j + 1) := (mem_range _ _ _).mpr ⟨le_rfl, by omega⟩
    rw [h0] at this; exact absurd this (List.not_mem_nil)

/-- `lemma dinter_uni`. -/
theorem dinter_uni (i j : ℤ) : is_uniform (dinter i j) := by
  intro x y hx hy
  have hx' := (supp_dinter i j x).mp hx
  have hy' := (supp_dinter i j y).mp hy
  rw [dinter, duniform_apply, duniform_apply, if_pos ((mem_range _ _ _).mpr ⟨hx'.1, by omega⟩),
    if_pos ((mem_range _ _ _).mpr ⟨hy'.1, by omega⟩)]

/-- Sub-distributions with the same point masses are equal. -/
theorem _root_.GaudisCrypt.SubProbability.ext_singleton {α : Type} {μ ν : SubProbability α}
    (h : ∀ x, μ.1 {x} = ν.1 {x}) : μ = ν :=
  Subtype.ext (discreteMeasure.ext μ.2.2 ν.2.2 h)

/-- `lemma dexcepted1E`, as a point mass: the mass of `x` under `d \ P` is `0` on `P`, else
that under `d` divided by the mass `d` gives to `¬ P`. -/
theorem dexcepted_apply {α : Type} (d : SubProbability α) (P : α → Prop) [DecidablePred P]
    (hd : is_lossless d) (hex : ∃ a, ¬ P a ∧ d.1 {a} ≠ 0) (x : α) :
    (dexcepted d P).1 {x} =
      (if P x then 0 else d.1 {x}) * (∑' a, if P a then 0 else d.1 {a})⁻¹ := by
  rw [mu1_eq_expected, dexcepted_expected d P hd hex]
  congr 1
  · rw [tsum_eq_single x]
    · by_cases hP : P x <;> simp [hP]
    · intro a ha
      by_cases hP : P a <;> simp [hP, ha]
  · congr 1
    exact tsum_congr fun a => by by_cases hP : P a <;> simp [hP]

/-- The mass of a point of the interval under `dinter i j`. -/
theorem dinter_apply (i j x : ℤ) :
    (dinter i j).1 {x} =
      if i ≤ x ∧ x ≤ j then ((range i (j + 1)).toFinset.card : ENNReal)⁻¹ else 0 := by
  have hx : x ∈ range i (j + 1) ↔ i ≤ x ∧ x ≤ j := by rw [mem_range]; omega
  rw [dinter, duniform_apply]
  by_cases h : i ≤ x ∧ x ≤ j
  · rw [if_pos (hx.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hx.mp h')), if_neg h]

/-- The uniform distribution on an interval, conditioned on a sub-interval, is the uniform
distribution on the sub-interval (what EC computes with `dexcepted1E`, `weight_dinter`,
`dinter1E`, `dinterE` in `Dice4_6.ec`'s `D4_Sample`). -/
theorem dinter_dexcepted (i j i' j' : ℤ) (h : i ≤ i' ∧ i' ≤ j' ∧ j' ≤ j) :
    dexcepted (dinter i j) (fun v => ¬ (i' ≤ v ∧ v ≤ j')) = dinter i' j' := by
  obtain ⟨h1, h2, h3⟩ := h
  set N : ENNReal := ((range i (j + 1)).toFinset.card : ENNReal) with hN
  set n' : ENNReal := ((range i' (j' + 1)).toFinset.card : ENNReal) with hn'
  have hN0 : N ≠ 0 := by
    have : i ∈ (range i (j + 1)).toFinset :=
      List.mem_toFinset.mpr ((mem_range _ _ _).mpr ⟨le_rfl, by omega⟩)
    simpa [hN] using (Finset.card_pos.mpr ⟨i, this⟩).ne'
  have hn0 : n' ≠ 0 := by
    have : i' ∈ (range i' (j' + 1)).toFinset :=
      List.mem_toFinset.mpr ((mem_range _ _ _).mpr ⟨le_rfl, by omega⟩)
    simpa [hn'] using (Finset.card_pos.mpr ⟨i', this⟩).ne'
  have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have hnt : n' ≠ ⊤ := ENNReal.natCast_ne_top _
  have hd : ∀ a, i' ≤ a ∧ a ≤ j' → (dinter i j).1 {a} = N⁻¹ := fun a ha => by
    rw [dinter_apply, if_pos ⟨by omega, by omega⟩]
  have hex : ∃ a, ¬ ¬ (i' ≤ a ∧ a ≤ j') ∧ (dinter i j).1 {a} ≠ 0 :=
    ⟨i', not_not.mpr ⟨le_rfl, h2⟩, by rw [hd i' ⟨le_rfl, h2⟩]; simpa using hNt⟩
  have hS : (∑' a, if ¬ (i' ≤ a ∧ a ≤ j') then 0 else (dinter i j).1 {a}) = n' * N⁻¹ := by
    rw [tsum_eq_sum (s := (range i' (j' + 1)).toFinset)]
    · rw [Finset.sum_congr rfl (g := fun _ => N⁻¹), Finset.sum_const, nsmul_eq_mul]
      intro a ha
      have ha' : i' ≤ a ∧ a ≤ j' := by
        have := (mem_range _ _ _).mp (List.mem_toFinset.mp ha); omega
      rw [if_neg (not_not.mpr ha'), hd a ha']
    · intro a ha
      rw [if_pos fun h' => ha (List.mem_toFinset.mpr ((mem_range _ _ _).mpr ⟨h'.1, by omega⟩))]
  refine SubProbability.ext_singleton fun x => ?_
  rw [dexcepted_apply _ _ (dinter_ll i j (by omega)) hex, hS, dinter_apply i' j' x]
  by_cases hx : i' ≤ x ∧ x ≤ j'
  · rw [if_neg (not_not.mpr hx), if_pos hx, hd x hx,
      ENNReal.mul_inv (Or.inl hn0) (Or.inl hnt), inv_inv, mul_comm n'⁻¹, ← mul_assoc,
      ENNReal.inv_mul_cancel hN0 hNt, one_mul]
  · rw [if_pos hx, if_neg hx, zero_mul]

end GaudisCrypt.EC
