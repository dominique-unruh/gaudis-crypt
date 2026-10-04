/-
Measure-free types (Fremlin, *Measure Theory* vol. 4, 438A).
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.SetTheory.Cardinal.Aleph

namespace GaudisCrypt

open MeasureTheory Cardinal

universe u v

/-- A type `α` is *measure-free* (Fremlin 438A: "measure-free" / "of measure zero", there stated
for cardinals) if every probability measure on `α` defined on all subsets of `α` (i.e., w.r.t. the
discrete σ-algebra `⊤`) gives positive mass to some singleton. -/
class MeasureFree (α : Type*) : Prop where
  exists_pos_singleton : ∀ (μ : @Measure α ⊤) [@IsProbabilityMeasure α ⊤ μ], ∃ x, 0 < μ {x}

/-- Every countable type is measure-free. -/
instance MeasureFree.of_countable {α : Type*} [Countable α] : MeasureFree α :=
  ⟨fun μ _ => by
    by_contra! h
    have h0 : μ (⋃ x, ({x} : Set α)) = 0 :=
      measure_iUnion_null fun x => nonpos_iff_eq_zero.mp (h x)
    rw [Set.iUnion_of_singleton, measure_univ] at h0
    exact one_ne_zero h0⟩

/-- On a measure-free type, every nonzero s-finite measure on the discrete σ-algebra gives positive
mass to some singleton. -/
theorem MeasureFree.exists_pos_singleton_of_ne_zero {α : Type*} [MeasureFree α]
    (μ : @Measure α ⊤) [@SFinite α ⊤ μ] (h : μ ≠ 0) : ∃ x, 0 < μ {x} := by
  letI : MeasurableSpace α := ⊤
  obtain ⟨n, hn⟩ : ∃ n, sfiniteSeq μ n ≠ 0 := by
    by_contra! H
    exact h (by rw [← sum_sfiniteSeq μ, funext H, Measure.sum_zero])
  haveI : NeZero (sfiniteSeq μ n) := ⟨hn⟩
  obtain ⟨x, hx⟩ := exists_pos_singleton ((sfiniteSeq μ n Set.univ)⁻¹ • sfiniteSeq μ n)
  refine ⟨x, (pos_iff_ne_zero.2 fun h0 => ?_).trans_le (Measure.le_iff'.1 (sfiniteSeq_le μ n) _)⟩
  simp [h0] at hx

/-- On a measure-free type, an s-finite measure on the discrete σ-algebra that vanishes on all
singletons is zero. -/
theorem MeasureFree.eq_zero_of_forall_singleton {α : Type*} [MeasureFree α]
    (μ : @Measure α ⊤) [@SFinite α ⊤ μ] (h : ∀ x, μ {x} = 0) : μ = 0 := by
  by_contra h0
  obtain ⟨x, hx⟩ := exists_pos_singleton_of_ne_zero μ h0
  exact hx.ne' (h x)

/-- On a measure-free type, every s-finite measure on the discrete σ-algebra is discrete: the
measure of a set is the sum of the masses of its points. -/
theorem MeasureFree.measure_eq_tsum_singleton {α : Type*} [MeasureFree α]
    (μ : @Measure α ⊤) [@SFinite α ⊤ μ] (A : Set α) : μ A = ∑' x : A, μ {(x : α)} := by
  letI : MeasurableSpace α := ⊤
  -- the atoms
  set S := {x | 0 < μ {x}}
  have hS : S.Countable := Measure.countable_meas_pos_of_disjoint_iUnion
    (fun _ => MeasurableSpace.measurableSet_top) fun _ _ h => Set.disjoint_singleton.2 h
  -- the rest vanishes
  have hrest : μ.restrict Sᶜ = 0 := eq_zero_of_forall_singleton _ fun x => by
    rw [Measure.restrict_apply MeasurableSpace.measurableSet_top]
    by_cases hx : x ∈ S
    · rw [Set.singleton_inter_eq_empty.2 (not_not_intro hx), measure_empty]
    · exact measure_mono_null Set.inter_subset_left (nonpos_iff_eq_zero.1 (not_lt.1 hx))
  refine le_antisymm ?_ ?_
  · have hdiff : μ (A \ S) = 0 := by
      rw [Set.sdiff_eq, ← Measure.restrict_apply MeasurableSpace.measurableSet_top, hrest]
      rfl
    calc μ A ≤ μ (A ∩ S) + μ (A \ S) := measure_le_inter_add_sdiff μ A S
      _ = ∑' x : ↥(A ∩ S), μ {(x : α)} := by
        rw [hdiff, add_zero]
        exact (tsum_measure_preimage_singleton (hS.mono Set.inter_subset_right) (f := id)
          fun _ _ => MeasurableSpace.measurableSet_top).symm
      _ ≤ ∑' x : A, μ {(x : α)} :=
        ENNReal.tsum_mono_subtype (fun x => μ {x}) Set.inter_subset_left
  · calc ∑' x : A, μ {(x : α)} ≤ μ (⋃ x : A, {(x : α)}) := tsum_meas_le_meas_iUnion_of_disjoint μ
          (fun _ => MeasurableSpace.measurableSet_top)
          fun _ _ h => Set.disjoint_singleton.2 (Subtype.coe_injective.ne h)
      _ = μ A := by rw [Set.iUnion_of_singleton_coe]

/-- Measure-freeness passes to types that inject into a measure-free type. -/
theorem MeasureFree.of_injective {α β : Type*} [MeasureFree α] {f : β → α}
    (hf : Function.Injective f) : MeasureFree β :=
  ⟨fun μ _ => by
    letI : MeasurableSpace α := ⊤
    letI : MeasurableSpace β := ⊤
    have hm : Measurable f := measurable_from_top
    haveI := Measure.isProbabilityMeasure_map (μ := μ) hm.aemeasurable
    obtain ⟨x, hx⟩ := exists_pos_singleton (μ.map f)
    rw [Measure.map_apply hm MeasurableSpace.measurableSet_top] at hx
    rcases ((Set.subsingleton_singleton (a := x)).preimage hf).eq_empty_or_singleton with
      h | ⟨y, h⟩
    · simp [h] at hx
    · exact ⟨y, h ▸ hx⟩⟩

/-- Measure-freeness is invariant under equivalence. -/
theorem MeasureFree.of_equiv {α β : Type*} [MeasureFree β] (e : α ≃ β) : MeasureFree α :=
  of_injective e.injective

instance MeasureFree.subtype {α : Type*} [MeasureFree α] (p : α → Prop) : MeasureFree (Subtype p) :=
  of_injective Subtype.val_injective

instance MeasureFree.ulift {α : Type*} [MeasureFree α] : MeasureFree (ULift α) :=
  of_equiv Equiv.ulift

/-- A sum of measure-free types indexed by a measure-free type is measure-free. -/
instance MeasureFree.sigma {ι : Type*} {α : ι → Type*} [MeasureFree ι] [∀ i, MeasureFree (α i)] :
    MeasureFree (Σ i, α i) :=
  ⟨fun μ _ => by
    letI : MeasurableSpace (Σ i, α i) := ⊤
    letI : MeasurableSpace ι := ⊤
    letI (i : ι) : MeasurableSpace (α i) := ⊤
    have hm : Measurable (Sigma.fst : (Σ i, α i) → ι) := measurable_from_top
    haveI := Measure.isProbabilityMeasure_map (μ := μ) hm.aemeasurable
    obtain ⟨i, hi⟩ := exists_pos_singleton (μ.map Sigma.fst)
    rw [Measure.map_apply hm MeasurableSpace.measurableSet_top] at hi
    -- the fibre over `i`
    have hemb : MeasurableEmbedding (Sigma.mk i : α i → Σ i, α i) :=
      ⟨sigma_mk_injective, measurable_from_top, fun _ _ => MeasurableSpace.measurableSet_top⟩
    haveI : IsFiniteMeasure (μ.comap (Sigma.mk i)) :=
      ⟨by rw [hemb.comap_apply]; exact measure_lt_top _ _⟩
    have hne : μ.comap (Sigma.mk i) ≠ 0 := fun h0 => by
      have := hemb.comap_apply μ Set.univ
      rw [h0, Measure.coe_zero, Pi.zero_apply] at this
      refine hi.ne' (measure_mono_null (fun p (hp : p.1 = i) => ?_) this.symm)
      obtain ⟨j, y⟩ := p
      subst hp
      exact ⟨y, trivial, rfl⟩
    obtain ⟨y, hy⟩ := exists_pos_singleton_of_ne_zero _ hne
    rw [hemb.comap_apply, Set.image_singleton] at hy
    exact ⟨_, hy⟩⟩

instance MeasureFree.prod {α β : Type*} [MeasureFree α] [MeasureFree β] : MeasureFree (α × β) :=
  of_equiv (Equiv.sigmaEquivProd α β).symm

instance MeasureFree.sum {α : Type u} {β : Type v} [MeasureFree α] [MeasureFree β] :
    MeasureFree (α ⊕ β) :=
  have : ∀ b : Bool, MeasureFree (bif b then ULift.{u} β else ULift.{v} α) := by
    rintro (_ | _) <;> exact MeasureFree.ulift
  of_equiv ((Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm).trans
    (Equiv.sumEquivSigmaBool (ULift.{v} α) (ULift.{u} β)))

instance MeasureFree.option {α : Type*} [MeasureFree α] : MeasureFree (Option α) :=
  of_equiv (Equiv.optionEquivSumPUnit.{0} α)

/-- Ulam's matrix argument. Let `r` be a relation on `α` such that every `r`-initial segment
`{x | r x y}` is countable and every `{y | ¬ r x y}` is countable. Then no probability measure on
the discrete σ-algebra vanishes on all singletons. -/
private theorem ulam_matrix {α : Type*} (r : α → α → Prop)
    (hlt : ∀ y, {x | r x y}.Countable) (hnlt : ∀ x, {y | ¬ r x y}.Countable)
    (μ : @Measure α ⊤) [@IsProbabilityMeasure α ⊤ μ] (hsing : ∀ x, μ {x} = 0) : False := by
  letI : MeasurableSpace α := ⊤
  -- countable sets are null
  have hnull : ∀ s : Set α, s.Countable → μ s = 0 := fun s hs => by
    simpa using (measure_biUnion_null_iff (μ := μ) hs (s := fun x => {x})).2 fun x _ => hsing x
  -- `α` is uncountable
  have hunc : ¬ (Set.univ : Set α).Countable := fun hc => by
    simpa using hnull _ hc
  -- injections of the initial segments into `ℕ`
  have hinj : ∀ y, ∃ g : {x | r x y} → ℕ, Function.Injective g := fun y =>
    have := (hlt y).to_subtype
    Countable.exists_injective_nat _
  choose g hg using hinj
  -- the Ulam matrix
  let A : ℕ → α → Set α := fun n x => {y | ∃ h : r x y, g y ⟨x, h⟩ = n}
  have hdisj : ∀ n, Pairwise (Function.onFun Disjoint (A n)) := fun n x x' hne => by
    refine Set.disjoint_left.2 fun y ⟨h, hy⟩ ⟨h', hy'⟩ => hne ?_
    exact congrArg Subtype.val (hg y (hy.trans hy'.symm))
  -- every column has a row of positive measure
  have hpos : ∀ x, ∃ n, 0 < μ (A n x) := fun x => by
    by_contra! H
    have h0 : μ (⋃ n, A n x) = 0 := measure_iUnion_null fun n => nonpos_iff_eq_zero.mp (H n)
    have hU : (⋃ n, A n x) ∪ {y | ¬ r x y} = Set.univ := Set.eq_univ_of_forall fun y =>
      (em (r x y)).elim (fun hy => Or.inl (Set.mem_iUnion.2 ⟨_, hy, rfl⟩)) Or.inr
    have := measure_union_null h0 (hnull _ (hnlt x))
    rw [hU, measure_univ] at this
    exact one_ne_zero this
  choose N hN using hpos
  -- pigeonhole: some row contains uncountably many positive entries
  obtain ⟨k, hk⟩ : ∃ k, ¬ {x | N x = k}.Countable := by
    by_contra! H
    exact hunc ((Set.countable_iUnion H).mono fun x _ => Set.mem_iUnion.2 ⟨N x, rfl⟩)
  exact hk ((Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
    (fun _ => MeasurableSpace.measurableSet_top) (hdisj k)).mono fun x (hx : N x = k) => hx ▸ hN x)

/-- Every type of cardinality at most `ℵ₁` is measure-free (Ulam; Fremlin 438C). -/
theorem MeasureFree.of_le_aleph_one {α : Type*} (h : #α ≤ ℵ₁) : MeasureFree α := by
  obtain ⟨r, _, hr⟩ := Cardinal.exists_ord_eq α
  have hlt : ∀ y, {x | r x y}.Countable := fun y => by
    rw [← Cardinal.le_aleph0_iff_set_countable, ← Order.lt_succ_iff, Cardinal.succ_aleph0]
    exact (Cardinal.card_typein_lt (r := r) y hr).trans_le h
  refine ⟨fun μ _ => ?_⟩
  by_contra! H
  refine ulam_matrix r hlt (fun x => ((hlt x).insert x).mono fun y hy => ?_) μ
    fun x => nonpos_iff_eq_zero.mp (H x)
  exact ((trichotomous_of r x y).resolve_left hy).imp Eq.symm id

end GaudisCrypt
