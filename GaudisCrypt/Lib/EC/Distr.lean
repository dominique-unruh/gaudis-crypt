import GaudisCrypt.Language.SubProbability
import GaudisCrypt.Language.Semantics
import GaudisCrypt.WeakestPreconditions

/-!
# EasyCrypt's distributions (`theories/distributions/`)

EasyCrypt's `'a distr` is a sub-probability, here `SubProbability`.  Only what ported developments
use is here.  Names are EasyCrypt's.

| EasyCrypt | here |
|---|---|
| `d1 \`*\` d2` (`DProd`) | `dprod d1 d2` |
| `d \ P` (`Dexcepted`) | `dexcepted d P` |
| `{0,1}`, `dbool` (`DBool`) | `dbool` |
| `is_lossless d`, `is_full d`, `is_funiform d` | the same |
-/

namespace GaudisCrypt.EC

variable {α β : Type}

/-- `d1 \`*\` d2`: the product distribution, sampling both independently. -/
noncomputable def dprod (d1 : SubProbability α) (d2 : SubProbability β) : SubProbability (α × β) :=
  d1 >>= fun a => d2 >>= fun b => pure (a, b)

/-- EC's `mu1 d x`: the probability of `x` under `d`, a real. -/
noncomputable def mu1 (d : SubProbability α) (x : α) : ℝ := (d.1 {x}).toReal

/-- EC's `mu_bounded`, as finiteness: a point has finite mass. -/
theorem mu_ne_top (d : SubProbability α) (x : α) : d.1 {x} ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    ((MeasureTheory.measure_mono (Set.subset_univ _)).trans d.2.1)

/-- `is_lossless d`: `d` has total mass `1`. -/
def is_lossless (d : SubProbability α) : Prop := d.1 Set.univ = 1

/-- Losslessness as an expectation: the expected value of `1` is `1`. -/
theorem is_lossless_iff_expected (d : SubProbability α) :
    is_lossless d ↔ d.expected (fun _ => 1) = 1 := by
  unfold is_lossless SubProbability.expected
  rw [MeasureTheory.lintegral_one]

/-- `lemma dprod_ll`: the product of lossless distributions is lossless. -/
theorem dprod_ll {d1 : SubProbability α} {d2 : SubProbability β} (h1 : is_lossless d1)
    (h2 : is_lossless d2) : is_lossless (dprod d1 d2) := by
  rw [is_lossless_iff_expected] at h1 h2 ⊢
  simp only [dprod, SubProbability.expected_bind, expected_pure, h2, h1]

/-- `lemma duniform_ll` for a finite nonempty type: the uniform distribution is lossless. -/
theorem uniform_ll [Fintype α] [Nonempty α] :
    is_lossless (SubProbability.uniform : SubProbability α) := by
  letI : MeasurableSpace α := ⊤
  change (PMF.uniformOfFintype α).toMeasure Set.univ = 1
  haveI := @PMF.toMeasure.isProbabilityMeasure α ⊤ (PMF.uniformOfFintype α)
  exact MeasureTheory.IsProbabilityMeasure.measure_univ

/-- `is_full d`: every value is in the support of `d`. -/
def is_full (d : SubProbability α) : Prop := ∀ x, 0 < d.1 {x}

/-- `is_funiform d`: all values have the same probability. -/
def is_funiform (d : SubProbability α) : Prop := ∀ x y, d.1 {x} = d.1 {y}

/-- `lemma duniform_funi` for a finite nonempty type: the uniform distribution is uniform. -/
theorem uniform_funi [Fintype α] [Nonempty α] :
    is_funiform (SubProbability.uniform : SubProbability α) := by
  intro x y
  letI : MeasurableSpace α := ⊤
  change (PMF.uniformOfFintype α).toMeasure {x} = (PMF.uniformOfFintype α).toMeasure {y}
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x),
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton y)]
  simp

/-- `lemma duniform_fu` for a finite nonempty type: every value has positive probability. -/
theorem uniform_fu [Fintype α] [Nonempty α] :
    is_full (SubProbability.uniform : SubProbability α) := by
  intro x
  letI : MeasurableSpace α := ⊤
  change 0 < (PMF.uniformOfFintype α).toMeasure {x}
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x)]
  simp

/-- `lemma eq_distr` (one direction): distributions with the same point masses are equal. -/
theorem eq_distr {μ ν : SubProbability α} (h : ∀ x, μ.1 {x} = ν.1 {x}) : μ = ν :=
  Subtype.ext (discreteMeasure.ext μ.2.2 ν.2.2 h)

open Classical in
/-- `mu1 d v` as the expectation of the indicator of `v` (EC's `mu1` is `mu d (pred1 v)`). -/
theorem mu1_eq_expected (d : SubProbability α) (v : α) :
    d.1 {v} = d.expected (fun a => if a = v then 1 else 0) := by
  letI : MeasurableSpace α := ⊤
  change _ = ∫⁻ a, (if a = v then 1 else 0) ∂d.1
  rw [lintegral_eq_tsum_smul d.2.2, tsum_eq_single v (fun a ha => by simp [ha])]
  simp

/-- `lemma dprod1E`: the point masses of the product distribution are products. -/
theorem dprod1E (d1 : SubProbability α) (d2 : SubProbability β) (x : α) (y : β) :
    (dprod d1 d2).1 {(x, y)} = d1.1 {x} * d2.1 {y} := by
  classical
  rw [mu1_eq_expected, mu1_eq_expected d1, mu1_eq_expected d2]
  simp only [dprod, SubProbability.expected_bind, expected_pure, Prod.mk.injEq, ite_and]
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  have h : ∀ a, d2.expected (fun b => if a = x then (if b = y then (1 : ENNReal) else 0) else 0) =
      (if a = x then 1 else 0) * d2.expected (fun b => if b = y then 1 else 0) := fun a => by
    by_cases ha : a = x <;> simp [ha, SubProbability.expected]
  simp only [h]
  exact MeasureTheory.lintegral_mul_const _ (measurable_from_top (f := fun a : α =>
    if a = x then (1 : ENNReal) else 0))

/-- `supp_dprod`, as fullness: a product of full distributions is full. -/
theorem dprod_fu {d1 : SubProbability α} {d2 : SubProbability β} (h1 : is_full d1)
    (h2 : is_full d2) : is_full (dprod d1 d2) := by
  rintro ⟨x, y⟩
  rw [dprod1E]
  exact ENNReal.mul_pos (h1 x).ne' (h2 y).ne'

open Classical in
/-- `d \ P`: `d` conditioned on not satisfying `P`.  EasyCrypt normalizes the restriction of `d` to
`¬ P`.  Here that is done for lossless `d` with a `¬ P` outcome of positive probability; otherwise
the result is the null distribution, as in EasyCrypt when no such outcome exists. -/
noncomputable def dexcepted (d : SubProbability α) (P : α → Prop) : SubProbability α :=
  if h : ∃ hd : is_lossless d, ∃ a ∈ {a | ¬ P a}, d.toPMF hd a ≠ 0 then
    toSubProbability ((d.toPMF h.1).filter {a | ¬ P a} h.2)
  else ⊥

/-- `dbool` (`{0,1}`): a fair coin. -/
noncomputable def dbool : SubProbability Bool := SubProbability.uniform

/-- `lemma dbool_ll : is_lossless dbool`. -/
theorem dbool_ll : is_lossless dbool := uniform_ll

/-- `lemma dbool1E`: each boolean has probability `1/2`. -/
theorem dbool1E (b : Bool) : dbool.1 {b} = 2⁻¹ := by
  letI : MeasurableSpace Bool := ⊤
  change (PMF.uniformOfFintype Bool).toMeasure {b} = _
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton b)]
  simp

end GaudisCrypt.EC
