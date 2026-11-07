import GaudisCrypt.Lib.EC.FMap
import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Logic.PHoare
import GaudisCrypt.Logic.PRHL2

/-!
# EasyCrypt's bounds on `mu` (`theories/distributions/Distr.ec`), on expectations

Our `phoare` bounds are expectations `d.expected f` of `ENNReal`-valued functions; EC's `mu d p`
is the expectation of an indicator.  The facts its proofs use:

| EasyCrypt | here |
|---|---|
| `mu_le` | `mu_le` (expectations), `indicatorE_le_of_imp` (indicators) |
| `mu_mem_le_mu1` (a uniform `d`) | `FMap.mu_rng_le`, at the values of a map |
-/

namespace GaudisCrypt

/-- EC's `mu_le` on expectations: a pointwise smaller function has a smaller expectation. -/
theorem EC.mu_le {γ : Type*} {μ : SubProbability γ} {f g : γ → ENNReal}
    (h : ∀ a, f a ≤ g a) : μ.expected f ≤ μ.expected g := by
  rw [SubProbability.expected_eq_tsum, SubProbability.expected_eq_tsum]
  exact ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

/-- `mu_le` on indicators: an implication of events. -/
theorem indicatorE_le_of_imp {P Q : Prop} (h : P → Q) : indicatorE P ≤ indicatorE Q := by
  by_cases hP : P
  · simp [indicatorE, hP, h hP]
  · simp [indicatorE, hP]

namespace EC.FMap

open Classical in
/-- `mu_mem_le_mu1` at the values of a map: a sample of a uniform `d` is a value of `m` with
probability at most `card (fdom m) * mu1 d default`. -/
theorem mu_rng_le {α β : Type} [DecidableEq α] [Inhabited β] {d : SubProbability β}
    (hfu : is_funiform d) (m : FMap α β) :
    d.expected (fun a => indicatorE (∃ k, dom m k ∧ get m k = some a)) ≤
      (fdom m).card * d.1 {default} := by
  let S : Finset β := (fdom m).image fun k => (get m k).getD default
  have hS : ∀ a, (∃ k, dom m k ∧ get m k = some a) → a ∈ S := by
    rintro a ⟨k, hk, hget⟩
    exact Finset.mem_image.mpr ⟨k, hk, by simp [hget]⟩
  rw [SubProbability.expected_eq_tsum]
  calc ∑' a, indicatorE (∃ k, dom m k ∧ get m k = some a) * d.1 {a}
      ≤ ∑' a, if a ∈ S then d.1 {a} else 0 := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases h : ∃ k, dom m k ∧ get m k = some a
        · simp [indicatorE, h, hS a h]
        · simp [indicatorE, h]
    _ = ∑ a ∈ S, d.1 {a} := by
        rw [tsum_eq_sum (s := S) (fun a ha => by simp [ha])]
        exact Finset.sum_congr rfl fun a ha => by simp [ha]
    _ = S.card * d.1 {default} := by
        rw [Finset.sum_congr rfl fun a _ => hfu a default, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (fdom m).card * d.1 {default} := by
        gcongr
        exact_mod_cast Finset.card_image_le

end EC.FMap

end GaudisCrypt
