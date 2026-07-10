import GaudisCrypt.Language.Footprint

/-!
# Observational indistinguishability does not determine the touched getter

The converse of `Footprint.indistinguishable_of_touched_getter_eq` is **false**: two states can be
indistinguishable through a footprint (no test of the footprint separates them by acceptance
probability) while their `touched_getter` values differ.

The counterexample lives on `Bool`.  Take the *asymmetric lazy flip*

  `qKer false = ½·δ_false + ½·δ_true`,   `qKer true = ¼·δ_false + ¾·δ_true`

and the footprint `qCentralizer := (Footprint.from {qKer})ᶜ` — everything commuting with `qKer`.
Viewing kernels on `Bool` as substochastic 2×2 matrices, `qKer` is stochastic with distinct
eigenvalues, so its commutant is the *abelian* algebra `{α·I + β·qKer}`:

* every member has both row sums equal to `α + β`, so **every test mass is state-independent**
  and `false`/`true` are indistinguishable (`qCentralizer_indistinguishable`) — formally, any `h`
  commuting with `qKer` satisfies `m_f = ½·m_f + ½·m_t` at `false`, forcing `m_f = m_t`;
* its only *deterministic* member is `id` (`eq_id_of_comm`: the swap would need `½ = ¼`, the
  constants would need `½ ∈ {0, 1}`), so the `qCentralizerᶜ`-orbits are trivial and the touched
  getter **separates** `false` from `true` (`touched_getter_separates`).

This is the same self-commutant abelian pathology behind `LeastLens` and the `HasReset`
side-conditions — indeed `qCentralizer` has no reset anywhere (`qCentralizer_not_hasReset`), i.e.
it is not a genuine memory region.  For lens footprints the two notions agree.
-/

namespace GaudisCrypt.CounterExamples

open GaudisCrypt
open scoped ENNReal

/-- Fair coin on `Bool`. -/
noncomputable def flipPMF : PMF Bool :=
  PMF.ofFintype (fun _ => 2⁻¹) (by
    rw [Fintype.sum_bool, ENNReal.inv_two_add_inv_two])

/-- Biased coin: `false ↦ ¼`, `true ↦ ¾`. -/
noncomputable def biasPMF : PMF Bool :=
  PMF.ofFintype (fun b => cond b (3 * 4⁻¹) 4⁻¹) (by
    rw [Fintype.sum_bool]
    show (3 : ENNReal) * 4⁻¹ + 4⁻¹ = 1
    rw [← one_mul (4⁻¹ : ENNReal), ← mul_assoc, mul_one, ← add_mul]
    norm_num
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

/-- The asymmetric lazy flip: fair from `false`, biased from `true`.  A stochastic kernel with
    distinct "rows", whose commutant is abelian. -/
noncomputable def qKer : Bool → SubProbability Bool
  | false => toSubProbability flipPMF
  | true => toSubProbability biasPMF

/-- The pathological footprint: everything commuting with `qKer`. -/
noncomputable def qCentralizer : Footprint Bool := (Footprint.from {qKer})ᶜ

/-! ### Point evaluations of `qKer` -/

lemma qKer_false_apply (b : Bool) : (qKer false).1 {b} = 2⁻¹ := by
  letI : MeasurableSpace Bool := ⊤
  show (@PMF.toMeasure _ ⊤ flipPMF) {b} = 2⁻¹
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  simp [flipPMF]

lemma qKer_true_apply_false : (qKer true).1 {false} = 4⁻¹ := by
  letI : MeasurableSpace Bool := ⊤
  show (@PMF.toMeasure _ ⊤ biasPMF) {false} = 4⁻¹
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  simp [biasPMF]

lemma qKer_univ (σ : Bool) : (qKer σ).1 Set.univ = 1 := by
  cases σ
  · haveI := @PMF.toMeasure.isProbabilityMeasure _ ⊤ flipPMF
    show (@PMF.toMeasure _ ⊤ flipPMF) Set.univ = 1
    exact MeasureTheory.measure_univ
  · haveI := @PMF.toMeasure.isProbabilityMeasure _ ⊤ biasPMF
    show (@PMF.toMeasure _ ⊤ biasPMF) Set.univ = 1
    exact MeasureTheory.measure_univ

/-! ### Generic evaluation helpers -/

private lemma bind_apply' (μ : SubProbability Bool) (k : Bool → SubProbability Bool)
    (s : Set Bool) : (μ >>= k).1 s = ∫⁻ x, (k x).1 s ∂μ.1 := by
  letI : MeasurableSpace Bool := ⊤
  change (MeasureTheory.Measure.bind μ.1 fun x => (k x).1) s = _
  exact MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
    measurable_from_top.aemeasurable

/-- Integrating against `qKer false` is the fair two-point average. -/
private lemma lintegral_qKer_false (g : Bool → ENNReal) :
    ∫⁻ x, g x ∂(qKer false).1 = 2⁻¹ * g false + 2⁻¹ * g true := by
  rw [lintegral_eq_tsum_smul (qKer false).2.2 g, tsum_bool, qKer_false_apply, qKer_false_apply]

private lemma diracKer_apply₁ (f : Function.End Bool) (x : Bool) (h : f x = false) :
    (diracKer f x).1 {false} = 1 := by
  letI : MeasurableSpace Bool := ⊤
  show (@MeasureTheory.Measure.dirac Bool ⊤ (f x)) {false} = 1
  rw [h]
  exact MeasureTheory.Measure.dirac_apply_of_mem rfl

private lemma diracKer_apply₀ (f : Function.End Bool) (x : Bool) (h : f x = true) :
    (diracKer f x).1 {false} = 0 := by
  letI : MeasurableSpace Bool := ⊤
  show (@MeasureTheory.Measure.dirac Bool ⊤ (f x)) {false} = 0
  rw [h, MeasureTheory.Measure.dirac_apply' _ MeasurableSet.of_discrete]
  simp

/-! ### Theorem A: no test separates `false` from `true` -/

/-- Any kernel commuting with `qKer` has state-independent total weight — evaluating the
    commutation equation at `false` gives `m_f = ½·m_f + ½·m_t`, hence `m_f = m_t`.  So the two
    states of `Bool` are **indistinguishable** through `qCentralizer`. -/
theorem qCentralizer_indistinguishable : qCentralizer.indistinguishable false true := by
  intro h hh
  -- `h` commutes with `qKer`
  have hq_mem : qKer ∈ (Footprint.from {qKer}).updates := by
    rw [Footprint.from_updates]
    exact Set.subset_centralizer_centralizer (Set.mem_singleton _)
  have hh' : h ∈ (Submonoid.centralizer (Footprint.from {qKer}).updates).carrier := hh
  have hcomm : qKer * h = h * qKer := Submonoid.mem_centralizer_iff.mp hh' qKer hq_mem
  have hc : h false >>= qKer = qKer false >>= h := congrFun hcomm false
  -- total weights of the two sides
  have e1 : (h false >>= qKer).1 Set.univ = (h false).1 Set.univ := by
    rw [bind_apply']
    simp only [qKer_univ, MeasureTheory.lintegral_one]
  have e2 : (qKer false >>= h).1 Set.univ
      = 2⁻¹ * (h false).1 Set.univ + 2⁻¹ * (h true).1 Set.univ := by
    rw [bind_apply', lintegral_qKer_false]
  -- `m_f = ½·m_f + ½·m_t`
  have hmf : (h false).1 Set.univ
      = 2⁻¹ * (h false).1 Set.univ + 2⁻¹ * (h true).1 Set.univ :=
    calc (h false).1 Set.univ = (h false >>= qKer).1 Set.univ := e1.symm
      _ = (qKer false >>= h).1 Set.univ := by rw [hc]
      _ = _ := e2
  -- cancel to `m_t = m_f`
  have hfin : (h false).1 Set.univ ≠ ⊤ := by
    have hle : (h false).1 Set.univ ≤ 1 := (h false).2.1
    exact (hle.trans_lt ENNReal.one_lt_top).ne
  have hAfin : 2⁻¹ * (h false).1 Set.univ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero) hfin
  have hhalves : 2⁻¹ * (h false).1 Set.univ + 2⁻¹ * (h false).1 Set.univ
      = (h false).1 Set.univ := by
    rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
  have hboth : 2⁻¹ * (h false).1 Set.univ + 2⁻¹ * (h true).1 Set.univ
      = 2⁻¹ * (h false).1 Set.univ + 2⁻¹ * (h false).1 Set.univ := hmf.symm.trans hhalves.symm
  have hhalf : 2⁻¹ * (h true).1 Set.univ = 2⁻¹ * (h false).1 Set.univ :=
    calc 2⁻¹ * (h true).1 Set.univ
        = 2⁻¹ * (h false).1 Set.univ + 2⁻¹ * (h true).1 Set.univ
          - 2⁻¹ * (h false).1 Set.univ := (ENNReal.add_sub_cancel_left hAfin).symm
      _ = 2⁻¹ * (h false).1 Set.univ + 2⁻¹ * (h false).1 Set.univ
          - 2⁻¹ * (h false).1 Set.univ := by rw [hboth]
      _ = 2⁻¹ * (h false).1 Set.univ := ENNReal.add_sub_cancel_left hAfin
  have key : (h false).1 Set.univ = (h true).1 Set.univ := by
    have h2 := congrArg (fun z => (2 : ENNReal) * z) hhalf
    simp only [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
      one_mul] at h2
    exact h2.symm
  exact congrArg ENNReal.toNNReal key

/-! ### Theorem B: the touched getter separates `false` from `true` -/

/-- A **deterministic** kernel commuting with `qKer` is the identity: evaluating
    `qKer (f false) = map f (qKer false)` at the point `false` rules out the swap (`¼ ≠ ½`) and
    both constants (`½ ∉ {0, 1}` resp. `¼ ∉ {0, ½}`). -/
theorem eq_id_of_comm (f : Function.End Bool)
    (hcomm : qKer * diracKer f = diracKer f * qKer) : f = id := by
  have hc : qKer (f false) = qKer false >>= diracKer f := by
    have hc0 := congrFun hcomm false
    change diracKer f false >>= qKer = qKer false >>= diracKer f at hc0
    rwa [show diracKer f false = (pure (f false) : SubProbability Bool) from rfl,
      SubProbability.pure_bind] at hc0
  have hev : (qKer (f false)).1 {false}
      = 2⁻¹ * (diracKer f false).1 {false} + 2⁻¹ * (diracKer f true).1 {false} := by
    rw [hc, bind_apply', lintegral_qKer_false]
  have hcases : f false = false ∧ f true = true := by
    cases hff : f false <;> cases hft : f true
    · -- constant-to-`false`: `½ = 1`
      rw [hff, diracKer_apply₁ f false hff, diracKer_apply₁ f true hft,
        qKer_false_apply, mul_one, ENNReal.inv_two_add_inv_two] at hev
      exact absurd (ENNReal.inv_eq_one.mp hev) (by norm_num)
    · exact ⟨rfl, rfl⟩
    · -- the swap: `¼ = ½`
      rw [hff, diracKer_apply₀ f false hff, diracKer_apply₁ f true hft,
        qKer_true_apply_false, mul_zero, mul_one, zero_add] at hev
      have h42 : (4 : ENNReal) = 2 := inv_inj.mp hev
      norm_num at h42
    · -- constant-to-`true`: `¼ = 0`
      rw [hff, diracKer_apply₀ f false hff, diracKer_apply₀ f true hft,
        qKer_true_apply_false, mul_zero, add_zero] at hev
      exact absurd (ENNReal.inv_eq_zero.mp hev) (by simp)
  funext b
  cases b
  · exact hcases.1
  · exact hcases.2

private lemma comm_of_mem_updates (f : Function.End Bool)
    (hf : diracKer f ∈ (Footprint.from {qKer}).updates) :
    qKer * diracKer f = diracKer f * qKer := by
  rw [Footprint.from_updates] at hf
  exact Set.mem_centralizer_iff.mp hf qKer
    (fun m hm => by rw [Set.mem_singleton_iff.mp hm])

private lemma eqvGen_collapse {r : Bool → Bool → Prop} (hr : ∀ s s', r s s' → s = s')
    {a b : Bool} (h : Relation.EqvGen r a b) : a = b := by
  induction h with
  | rel s s' hstep => exact hr s s' hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The `qCentralizerᶜ`-orbits are trivial (its only deterministic member is `id`), so the
    **touched getter separates** `false` from `true`. -/
theorem touched_getter_separates :
    qCentralizer.touched_getter.get false ≠ qCentralizer.touched_getter.get true := by
  intro hg
  have horb : Relation.EqvGen (fun s s' => ∃ f : Function.End Bool,
      diracKer f ∈ qCentralizerᶜ.updates ∧ f s = s') false true := Quotient.exact hg
  refine Bool.noConfusion (eqvGen_collapse ?_ horb)
  rintro s s' ⟨f, hf, rfl⟩
  have hf0 : diracKer f ∈ ((Footprint.from {qKer})ᶜᶜ).updates := hf
  have hf1 : diracKer f ∈ (Footprint.from {qKer}).updates :=
    congrArg Footprint.updates (Footprint.compl_compl (Footprint.from {qKer})) ▸ hf0
  rw [eq_id_of_comm f (comm_of_mem_updates f hf1)]
  rfl

/-! ### The separation, and the tie-in with `HasReset` -/

/-- **The two notions genuinely differ**: indistinguishability through a footprint does *not*
    imply equal `touched_getter` — the converse of
    `Footprint.indistinguishable_of_touched_getter_eq` is false. -/
theorem exists_indistinguishable_touched_getter_ne :
    ∃ (T : Footprint Bool) (σ σ' : Bool),
      T.indistinguishable σ σ' ∧ T.touched_getter.get σ ≠ T.touched_getter.get σ' :=
  ⟨qCentralizer, false, true, qCentralizer_indistinguishable, touched_getter_separates⟩

/-- The pathological footprint is not a genuine memory region: it has **no reset** at any state
    (its only deterministic update is `id`, which cannot overwrite the — injective — touched
    content).  The same abelian-bicommutant family that breaks `HasReset` breaks the
    tests-determine-glob converse. -/
theorem qCentralizer_not_hasReset (σ : Bool) : ¬ qCentralizer.HasReset σ := by
  rintro ⟨f, hf, -, hall⟩
  have hq_mem : qKer ∈ (Footprint.from {qKer}).updates := by
    rw [Footprint.from_updates]
    exact Set.subset_centralizer_centralizer (Set.mem_singleton _)
  have hf' : diracKer f ∈ (Submonoid.centralizer (Footprint.from {qKer}).updates).carrier := hf
  have hcomm : qKer * diracKer f = diracKer f * qKer :=
    Submonoid.mem_centralizer_iff.mp hf' qKer hq_mem
  rw [eq_id_of_comm f hcomm] at hall
  exact touched_getter_separates ((hall false).trans (hall true).symm)

end GaudisCrypt.CounterExamples
