import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.PHoareWp

/-!
# Rejection sampling

Sample uniformly until the predicate `P` holds: the result is uniform on `{x | P x}`.

    x <$ uniform;  while (¬ P x) { x <$ uniform };  return x
-/

namespace GaudisCrypt.Examples.RejectionSampling

open GaudisCrypt

/-- A finite space with a predicate that some point satisfies. -/
structure Domain where
  X : Type
  [fintype : Fintype X]
  [inhabited : Inhabited X]
  P : X → Bool

@[reducible] instance (D : Domain) : Fintype D.X := D.fintype
@[reducible] instance (D : Domain) : Inhabited D.X := D.inhabited
@[reducible] noncomputable instance (D : Domain) : DecidableEq D.X := Classical.decEq _

variable (D : Domain)

/-- The number of points satisfying `P`. -/
def Domain.good : ℕ := (Finset.univ.filter fun x => D.P x = true).card

moduletype SamplerT {
  proc sample () -> D.X;
}

module Sampler : (SamplerT D) {
  proc sample () : D.X {
    var x : D.X;
    x <$ SubProbability.uniform;
    while (!D.P $x) {
      x <$ SubProbability.uniform;
    }
    return $x
  };
}

theorem good_ne_zero (t : D.X) (ht : D.P t = true) : (D.good : ENNReal) ≠ 0 := by
  simpa [Domain.good, Finset.card_eq_zero, Finset.filter_eq_empty_iff] using ⟨t, ht⟩

/-- One uniform draw, scored `indicatorE (x = t)` on good points and `1 / |good|` on bad ones,
    averages to `1 / |good|`: the invariant of the loop is a fixed point. -/
theorem avg_eq (t : D.X) (ht : D.P t = true) :
    ∑ x : D.X, (if D.P x = true then indicatorE (x = t) else 1 / (D.good : ENNReal))
        / Fintype.card D.X = 1 / D.good := by
  classical
  have hK0 := good_ne_zero D t ht
  have hN0 : (Fintype.card D.X : ENNReal) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hKN : D.good ≤ Fintype.card D.X := Finset.card_filter_le _ _
  have hbad : (Finset.univ.filter fun x => ¬ D.P x = true).card = Fintype.card D.X - D.good := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset D.X)) (fun x => D.P x = true)
    simp only [Finset.card_univ] at this
    unfold Domain.good
    omega
  have hgood : ∑ x ∈ Finset.univ.filter (fun x => D.P x = true), indicatorE (x = t) = 1 := by
    simp only [indicatorE]
    rw [Finset.sum_ite_eq']
    simp [ht]
  simp_rw [ENNReal.div_eq_inv_mul, mul_one]
  rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const, hbad, nsmul_eq_mul, hgood]
  -- `N⁻¹ * (1 + (N - K) * K⁻¹) = K⁻¹`, with `1 = K * K⁻¹`
  rw [← ENNReal.mul_inv_cancel hK0 (ENNReal.natCast_ne_top _), ← add_mul, ← Nat.cast_add,
    Nat.add_sub_cancel' hKN, ← mul_assoc, ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top _),
    one_mul]

/-- A uniform draw is good with probability `|good| / |X|`. -/
theorem good_prob :
    ∑ x : D.X, indicatorE (D.P x = true) / Fintype.card D.X
      = (D.good : ENNReal) / Fintype.card D.X := by
  classical
  simp_rw [ENNReal.div_eq_inv_mul]
  rw [← Finset.mul_sum]
  congr 1
  simp only [indicatorE]
  -- `Finset.sum_boole`, up to the (classical) decidability instance
  convert Finset.sum_boole (s := (Finset.univ : Finset D.X)) (p := fun x => D.P x = true)
    (R := ENNReal)
  rfl

/-- Each good point is hit with probability at most `1 / |good|`. -/
theorem sample_le (t : D.X) (ht : D.P t = true) :
    phoare[ (Sampler.sample D) : True ==> §res = t ] ≤ (1 / (D.good : ENNReal)) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_le (if D.P §x = true then indicatorE (§x = t) else 1 / (D.good : ENNReal))
  case body =>
    phoare_wp 1
    phoare_skip
    intro x hx
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hx
    rw [avg_eq D t ht]
    simp [hx]
  case exit =>
    intro x hx
    simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at hx
    simp [hx]
  phoare_wp 2
  phoare_skip
  exact fun _ => (avg_eq D t ht).le

/-- Each good point is hit with probability at least `1 / |good|`: the same invariant, plus
    termination (each draw is good with probability `|good| / |X|`). -/
theorem sample_ge (t : D.X) (ht : D.P t = true) :
    phoare[ (Sampler.sample D) : True ==> §res = t ] ≥ (1 / (D.good : ENNReal)) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_ge (if D.P §x = true then indicatorE (§x = t) else 1 / (D.good : ENNReal))
    using (D.good : ENNReal) / Fintype.card D.X
  case body =>
    phoare_wp 1
    phoare_skip
    intro x hx
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hx
    rw [avg_eq D t ht]
    simp [hx]
  case exit =>
    intro x hx
    simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at hx
    simp [hx]
  case lossless =>
    phoare_wp 1
    phoare_skip
    exact fun _ _ => ENNReal.sum_div_card 1
  case progress =>
    phoare_wp 1
    phoare_skip
    intro _ _
    simp only [Bool.not_eq_eq_eq_not, Bool.not_false]
    exact (good_prob D).ge
  case I_le_one =>
    intro x
    split_ifs
    · exact indicatorE_le_one _
    · exact ENNReal.div_le_of_le_mul (by
        rw [one_mul]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast good_ne_zero D t ht))
  case ε_ne_zero =>
    exact (ENNReal.div_pos (good_ne_zero D t ht) (ENNReal.natCast_ne_top _)).ne'
  case ε_le_one =>
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast Finset.card_filter_le _ _)
  phoare_wp 2
  phoare_skip
  exact fun _ => (avg_eq D t ht).ge

/-- **Rejection sampling is uniform on the good points.** -/
theorem sample_uniform (t : D.X) (ht : D.P t = true) :
    phoare[ (Sampler.sample D) : True ==> §res = t ] = (1 / (D.good : ENNReal)) :=
  phoareProc_eq_of_le_ge (sample_le D t ht) (sample_ge D t ht)

/-- A bad point is never returned: the invariant `0`, since the loop only exits on a good point. -/
theorem sample_good : phoare[ (Sampler.sample D) : True ==> D.P §res = false ] = 0 := by
  refine phoareProc_eq_of_le_ge ?_ fun _ _ _ => bot_le
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_le 0
  case body =>
    phoare_wp 1
    phoare_skip
    simp
  case exit =>
    intro x hx
    simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at hx
    simp [hx]
  phoare_wp 2
  phoare_skip
  simp

end GaudisCrypt.Examples.RejectionSampling
