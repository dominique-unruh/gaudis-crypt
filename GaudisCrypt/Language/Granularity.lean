import GaudisCrypt.Language.Programs
-- TODO: layering debt (re-introduced deliberately). `corner_crux` and its supporting reduce/extend
-- lemmas (`Lens.reduceFootprint_compl_footprint`, `reduce_updates_eq`, `liftFootprint_reduce_eq`,
-- `corner_crux_aux`) are general `Footprint` facts that depend on `Lens.reduceFootprint` (in
-- `GaudisCrypt.FV`, a range-framework file). Importing FV from `Language/` inverts the documented
-- layering. Once these lemmas (and the `Lens.reduceFootprint` machinery they need) are relocated to
-- `Language/Footprint.lean`, drop this import.
import GaudisCrypt.FV

namespace GaudisCrypt

class GranularProgramSpec extends ProgramSpec where
  grains : Set (Footprint State)
  from_lenses : ∀ f ∈ grains, f.FromLens
  disjoint : ∀ f ∈ grains, ∀ g ∈ grains, f ≠ g → f ≤ gᶜ
  nonempty_grains : ∀ f ∈ grains, f ≠ ⊥

def GranularFootprint [spec : GranularProgramSpec] := Finset spec.grains

def GranularFootprint.grains [spec : GranularProgramSpec] (F : GranularFootprint) :
  Set (Footprint State) :=
    Subtype.val '' (↑(show Finset spec.grains from F) : Set spec.grains)

def GranularFootprint.grainsFinset [spec : GranularProgramSpec] (F : GranularFootprint) :
    Finset (Footprint State) :=
  Finset.map ⟨Subtype.val, Subtype.val_injective⟩ F

theorem GranularFootprint.grains_finite [spec : GranularProgramSpec] (F : GranularFootprint) :
    (F.grains).Finite :=
  (F.finite_toSet).image _

theorem GranularFootprint.grains_subset [spec : GranularProgramSpec] (F : GranularFootprint) :
    F.grains ⊆ spec.grains := by
  simp [GranularFootprint.grains]

def GranularFootprint.footprint [spec : GranularProgramSpec]
    (F : GranularFootprint) : Footprint spec.state :=
  sSup F.grains

def Footprint.IsGranular [spec : GranularProgramSpec] (f : Footprint spec.state) :=
  ∃ (F : GranularFootprint), f = GranularFootprint.footprint F

def Footprint.IsSubGranular [spec : GranularProgramSpec] (f : Footprint spec.state) :=
  ∃ (F : GranularFootprint), f ≤ GranularFootprint.footprint F

instance [spec : GranularProgramSpec] : PartialOrder GranularFootprint where
  le f g := f.grains ⊆ g.grains
  le_refl _ := le_refl _
  le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂
  le_antisymm f g h₁ h₂ := by
    have hg : f.grains = g.grains := Set.Subset.antisymm h₁ h₂
    exact Finset.coe_injective (Set.image_injective.2 Subtype.val_injective hg)
  lt f g := f.grains ⊆ g.grains ∧ ¬ g.grains ⊆ f.grains
  lt_iff_le_not_ge _ _ := Iff.rfl

instance [spec : GranularProgramSpec] : OrderBot GranularFootprint where
  bot := Finset.empty
  bot_le f := by
    change GranularFootprint.grains Finset.empty ⊆ GranularFootprint.grains f
    exact Set.image_mono (Finset.coe_subset.mpr (Finset.empty_subset f))

def GranularFootprint.toFinset [spec : GranularProgramSpec] (F : GranularFootprint) :
    Finset spec.grains := F

theorem GranularFootprint.le_iff_subset [spec : GranularProgramSpec] {f g : GranularFootprint} :
    f ≤ g ↔ (show Finset spec.grains from f) ⊆ (show Finset spec.grains from g) :=
  ⟨fun h => Finset.coe_subset.mp ((Set.image_subset_image_iff Subtype.val_injective).mp h),
   fun h => Set.image_mono (Finset.coe_subset.mpr h)⟩

open Classical in
noncomputable instance [spec : GranularProgramSpec] : Lattice GranularFootprint where
  sup f g := (f.toFinset ∪ g.toFinset : Finset spec.grains)
  inf f g := (f.toFinset ∩ g.toFinset : Finset spec.grains)
  le_sup_left _ _ := GranularFootprint.le_iff_subset.mpr Finset.subset_union_left
  le_sup_right _ _ := GranularFootprint.le_iff_subset.mpr Finset.subset_union_right
  sup_le _ _ _ h₁ h₂ :=
    GranularFootprint.le_iff_subset.mpr
      (Finset.union_subset (GranularFootprint.le_iff_subset.mp h₁)
        (GranularFootprint.le_iff_subset.mp h₂))
  inf_le_left _ _ := GranularFootprint.le_iff_subset.mpr Finset.inter_subset_left
  inf_le_right _ _ := GranularFootprint.le_iff_subset.mpr Finset.inter_subset_right
  le_inf _ _ _ h₁ h₂ :=
    GranularFootprint.le_iff_subset.mpr
      (Finset.subset_inter (GranularFootprint.le_iff_subset.mp h₁)
        (GranularFootprint.le_iff_subset.mp h₂))

theorem GranularFootprint.toFinset_injective [spec : GranularProgramSpec] :
    Function.Injective (GranularFootprint.toFinset (spec := spec)) := fun _ _ h => h

open Classical in
noncomputable instance [spec : GranularProgramSpec] : SDiff GranularFootprint where
  sdiff f g := (f.toFinset \ g.toFinset : Finset spec.grains)

open Classical in
/-- `GranularFootprint` is a **generalized Boolean algebra** (a distributive lattice with `⊥` and a
    relative complement `\`), inherited from `Finset spec.grains` via the identity injection
    `toFinset`.  There is no `⊤`/`ᶜ` in general: complementing a finite grain family need not stay
    finite when the granularity is infinite, so this does not extend to a `BooleanAlgebra`. -/
noncomputable instance [spec : GranularProgramSpec] :
    GeneralizedBooleanAlgebra GranularFootprint :=
  GranularFootprint.toFinset_injective.generalizedBooleanAlgebra GranularFootprint.toFinset
    GranularFootprint.le_iff_subset.symm
    (fun {x y} => by
      rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
      exact and_congr GranularFootprint.le_iff_subset.symm
        (not_congr GranularFootprint.le_iff_subset.symm))
    (fun _ _ => rfl) (fun _ _ => rfl) rfl (fun _ _ => rfl)

open Classical in
/-- Infimum of a family of grain-sets: the intersection (grains common to every member).  Only
    meaningful when the family is nonempty; empty family reduces to `⊥` (junk, unconstrained by the
    conditional axioms). -/
noncomputable instance [spec : GranularProgramSpec] : InfSet GranularFootprint where
  sInf S := if hS : S.Nonempty then
      (hS.choose.toFinset.filter fun g => ∀ F ∈ S, g ∈ F.toFinset)
    else ⊥

open Classical in
/-- Supremum of a family of grain-sets: the union (grains touched by some member), which stays
    finite exactly when the family is bounded above.  Unbounded families reduce to `⊥` (junk); the
    empty family also gives `⊥`, so `sSup ∅ = ⊥`. -/
noncomputable instance [spec : GranularProgramSpec] : SupSet GranularFootprint where
  sSup S := if hS : BddAbove S then
      (hS.choose.toFinset.filter fun g => ∃ F ∈ S, g ∈ F.toFinset)
    else ⊥

open Classical in
/-- `GranularFootprint` is a **conditionally complete lattice**: any *nonempty* family of grain-sets
    that is bounded below has a greatest lower bound (its intersection), and any nonempty family
    bounded above has a least upper bound (its union — finite because contained in the bound).  It
    is not a `CompleteLattice`: there is no `⊤` when the granularity is infinite.  Combined with the
    existing `OrderBot`, `sSup ∅ = ⊥` holds by construction. -/
noncomputable instance [spec : GranularProgramSpec] :
    ConditionallyCompleteLattice GranularFootprint :=
  { (inferInstance : Lattice GranularFootprint),
    (inferInstance : SupSet GranularFootprint),
    (inferInstance : InfSet GranularFootprint) with
    isLUB_csSup := by
      intro S hne hbdd
      have hsSup : sSup S
          = hbdd.choose.toFinset.filter (fun g => ∃ F ∈ S, g ∈ F.toFinset) := dif_pos hbdd
      refine ⟨fun F hF => ?_, fun U hU => ?_⟩
      · rw [hsSup, GranularFootprint.le_iff_subset]
        intro g hg
        rw [Finset.mem_filter]
        exact ⟨(GranularFootprint.le_iff_subset.mp (hbdd.choose_spec hF)) hg, F, hF, hg⟩
      · rw [hsSup, GranularFootprint.le_iff_subset]
        intro g hg
        rw [Finset.mem_filter] at hg
        obtain ⟨_, F, hF, hgF⟩ := hg
        exact (GranularFootprint.le_iff_subset.mp (hU hF)) hgF
    isGLB_csInf := by
      intro S hne _hbdd
      have hsInf : sInf S
          = hne.choose.toFinset.filter (fun g => ∀ F ∈ S, g ∈ F.toFinset) := dif_pos hne
      refine ⟨fun F hF => ?_, fun L hL => ?_⟩
      · rw [hsInf, GranularFootprint.le_iff_subset]
        intro g hg
        rw [Finset.mem_filter] at hg
        exact hg.2 F hF
      · rw [hsInf, GranularFootprint.le_iff_subset]
        intro g hg
        rw [Finset.mem_filter]
        exact ⟨(GranularFootprint.le_iff_subset.mp (hL hne.choose_spec)) hg,
          fun F hF => (GranularFootprint.le_iff_subset.mp (hL hF)) hg⟩ }

theorem GranularFootprint.footprint_mono [spec : GranularProgramSpec] {F G : GranularFootprint}
    (h : F ≤ G) : F.footprint ≤ G.footprint :=
  sSup_le_sSup h

private theorem IsSubGranular.granularCover_finite
    [spec : GranularProgramSpec] {footprint : Footprint State} (h : footprint.IsSubGranular) :
       Finite { f : spec.grains | ¬ footprint ≤ f.valᶜ } := by
    obtain ⟨F, hF⟩ := h
    refine Set.Finite.of_finite_image ?_ Subtype.val_injective.injOn
    refine Set.Finite.subset (GranularFootprint.grains_finite F) ?_
    rintro g ⟨⟨g, hg⟩, hf_touch, rfl⟩
    by_contra hf_not
    apply hf_touch
    refine le_trans hF (sSup_le fun g' hg' => ?_)
    exact spec.disjoint g' (GranularFootprint.grains_subset F hg') g hg
      (fun e => hf_not (e ▸ hg'))


open Classical in
/-- A **minimal granular cover** of a sub-granular footprint: the sub-family of the grains of
    exactly the atoms `footprint` genuinely touches.  It is the least granular footprint containing
    `footprint` — that every touched atom is needed is immediate, and that these atoms already cover
    `footprint` is the product-corner structure theorem (`corner_crux`), applied in
    `Footprint.IsSubGranular.le_granular`. -/
noncomputable def Footprint.IsSubGranular.granularCover [spec : GranularProgramSpec]
    {footprint : Footprint State} (h : footprint.IsSubGranular) : GranularFootprint :=
  haveI := IsSubGranular.granularCover_finite h
  { f : spec.grains | ¬ footprint ≤ f.valᶜ }.toFinite.toFinset


/-- A granular footprint is a join of finitely many pairwise-disjoint lens footprints, hence
    itself lens-derived. -/
theorem GranularFootprint.footprint_fromLens [spec : GranularProgramSpec]
    (F : GranularFootprint) : F.footprint.FromLens := by
  classical
  change (sSup (Subtype.val '' (↑F.toFinset : Set spec.grains)) : Footprint State).FromLens
  induction F.toFinset using Finset.induction_on with
  | empty => simpa using Footprint.fromLens_bot
  | @insert p F hp ih =>
      rw [Finset.coe_insert, Set.image_insert_eq, sSup_insert]
      refine Footprint.FromLens.sup (spec.from_lenses p.val p.property) ih ?_
      have hsup : (sSup (Subtype.val '' (↑F : Set spec.grains)) : Footprint State)
          ≤ (p.val)ᶜ := by
        refine sSup_le ?_
        rintro q ⟨⟨q, hq⟩, hqF, rfl⟩
        refine spec.disjoint q hq p.val p.property (fun e => hp ?_)
        exact (Subtype.ext e : (⟨q, hq⟩ : spec.grains) = p) ▸ hqF
      calc (p.val : Footprint State) = (p.val)ᶜᶜ := (Footprint.compl_compl _).symm
        _ ≤ _ := Footprint.compl_le_compl hsup

theorem IsGranularFootprint.fromLens [spec : GranularProgramSpec] {f : Footprint State}
    (h : f.IsGranular) : f.FromLens := by
  obtain ⟨F, rfl⟩ := h
  exact F.footprint_fromLens

noncomputable def IsGranularFootprint.lens [spec : GranularProgramSpec] {f : Footprint State}
    (h : f.IsGranular) : Lens (Quotient fᶜ.orbit_setoid) State :=
  (IsGranularFootprint.fromLens h).lens

open Classical in
theorem isSubGranularFootprint_closed_sup [spec : GranularProgramSpec] {f g : Footprint State}
    (hf : f.IsSubGranular) (hg : g.IsSubGranular) :
    (f ⊔ g).IsSubGranular :=
  ⟨hf.choose ⊔ hg.choose,
    sup_le (hf.choose_spec.trans (GranularFootprint.footprint_mono le_sup_left))
      (hg.choose_spec.trans (GranularFootprint.footprint_mono le_sup_right))⟩

/-- The minimal granular cover's footprint is the join of exactly the grains that `f` touches. -/
-- TODO Rename → .granularCover_footprint_eq_sSup
theorem Footprint.IsSubGranular.granular_footprint [spec : GranularProgramSpec]
    (f : Footprint State) (h : f.IsSubGranular) :
    h.granularCover.footprint
      = sSup { g ∈ spec.grains | ¬ f ≤ gᶜ } := by
  unfold GranularFootprint.footprint Footprint.IsSubGranular.granularCover
  congr 1
  unfold GranularFootprint.grains
  ext g
  simp [and_comm]



theorem lens_pair_isSubGranular [GranularProgramSpec] {lens1 : Lens a State} {lens2 : Lens b State}
  [disjoint lens1 lens2] (h1 : lens1.footprint.IsSubGranular) (h2 : lens2.footprint.IsSubGranular) :
  (lens1.pair lens2).footprint.IsSubGranular :=
  pair_footprint lens1 lens2 ▸ isSubGranularFootprint_closed_sup h1 h2

-- TODO rename → Granularity.lens_pair_isSubGranular_sup
-- TODO make lens1, lens2 implicit args
theorem Lens.pair_granular_sup [GranularProgramSpec] (lens1 : Lens a State) (lens2 : Lens b State)
  [disjoint lens1 lens2] (h1 : lens1.footprint.IsSubGranular) (h2 : lens2.footprint.IsSubGranular) :
  (lens_pair_isSubGranular h1 h2).granularCover.footprint
   = h1.granularCover.footprint ⊔ h2.granularCover.footprint := by
  have hset : { g ∈ GranularProgramSpec.grains | ¬ (lens1.pair lens2).footprint ≤ gᶜ }
      = { g ∈ GranularProgramSpec.grains | ¬ lens1.footprint ≤ gᶜ }
        ∪ { g ∈ GranularProgramSpec.grains | ¬ lens2.footprint ≤ gᶜ } := by
    ext g
    simp only [pair_footprint, Set.mem_setOf_eq, Set.mem_union, sup_le_iff, not_and_or]
    tauto
  rw [Footprint.IsSubGranular.granular_footprint, Footprint.IsSubGranular.granular_footprint,
    Footprint.IsSubGranular.granular_footprint, hset, sSup_union]
  rfl


-- TODO: DOMINIQUE CHECK FROM HERE

/-! ### Corner order-iso and `corner_crux`

`corner_crux` (the product-corner structure theorem) is proved by reducing through the complement
lens `L := l.compl` of the splitter `B = l.footprint`: `Bᶜ = L.footprint`, and footprints below the
corner `L.footprint` are recovered by `L.liftFootprint ∘ Lens.reduceFootprint L` (the corner order-iso).  All
helpers are general `Footprint` facts, stated for an arbitrary state type (TODO check name /
relocate to `Language/Footprint.lean` with the `Lens.reduceFootprint` machinery). -/

-- TODO check name / relocate to `Language/Footprint.lean`.
/-- **Reducing the complement corner kills it.**  `Lens.reduceFootprint L` sends `(L.footprint)ᶜ` to `⊥`:
    every `L`-lift already lies in `L.footprint`, which commutes with all of `(L.footprint)ᶜ`, so
    the reduce-generator condition holds vacuously for every base kernel. -/
@[simp]
theorem Lens.reduceFootprint_compl_footprint {d s : Type} (L : Lens d s) :
    Lens.reduceFootprint L ((L.footprint)ᶜ) = ⊥ := by
  rw [Lens.reduceFootprint_alt_def]
  have hset : { f : d → SubProbability d | ∀ g ∈ ((L.footprint)ᶜ).updates,
      (L.liftSubProbability f : s → SubProbability s) * g
        = g * L.liftSubProbability f } = Set.univ := by
    ext f; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; intro g hg
    have hlift := Mlocalized_in_footprint L f
    rw [Footprint.updates_eq_centralizer_compl (L.footprint)ᶜ, Footprint.compl_compl] at hg
    exact (Submonoid.mem_centralizer_iff.mp hg) _ hlift
  rw [hset]; apply footprint_eq_of_updates
  rw [Footprint.from_updates, Set.centralizer_centralizer_centralizer]
  change Set.centralizer Set.univ = (Footprint.from ∅).updates
  rw [Footprint.from_updates, Set.centralizer_empty, Set.top_eq_univ]

private theorem compl_updates {m : Type} (R : Footprint m) :
    (Rᶜ).updates = Set.centralizer R.updates := by
  rw [Footprint.updates_eq_centralizer_compl (Rᶜ), Footprint.compl_compl]; rfl

-- TODO check name / relocate to `Language/Footprint.lean`.
/-- **`Lens.reduceFootprint` in commutant form.**  `(Lens.reduceFootprint L R).updates` is the centralizer of the base
    kernels whose `L`-lift lands in `Rᶜ` (folding `Lens.reduceFootprint_alt_def` through `Footprint.from`). -/
theorem reduce_updates_eq {d s : Type} (L : Lens d s) (R : Footprint s) :
    (Lens.reduceFootprint L R).updates
      = Set.centralizer { f : d → SubProbability d |
          (L.liftSubProbability f : s → SubProbability s) ∈ (Rᶜ).updates } := by
  rw [Lens.reduceFootprint_alt_def, Footprint.from_updates, Set.centralizer_centralizer_centralizer]
  congr 1; ext f
  simp only [Set.mem_setOf_eq, compl_updates, Set.mem_centralizer_iff]
  constructor <;> intro h g hg <;> exact (h g hg).symm

-- TODO check name / relocate to `Language/Footprint.lean`.
/-- **Corner order-iso.**  On `[⊥, L.footprint]`, `L.liftFootprint ∘ Lens.reduceFootprint L` is the identity:
    a footprint below the corner is exactly the lift of its reduction.

    `≥` (easy): each `u ∈ S.updates` is an `L`-lift (extraction), commuting with the reduce
    generators via `updateK` injectivity.  `≤` (hard): the pure-commutant obstruction (the center)
    is dissolved by the key set identity
    `{f | L.lift f ∈ Sᶜ} = centralizer {f | L.lift f ∈ S}` — whose `⊇` direction extracts each
    `k ∈ S.updates` as an `L`-lift (using `S ≤ L.footprint`) — giving
    `Lens.reduceFootprint L S ≤ (Lens.reduceFootprint L Sᶜ)ᶜ`, after which `liftSubProbability_comm_of_mem_reduce_compl`
    forces every lifted reduce-generator to commute with `Sᶜ`, i.e. to lie in `S`. -/
theorem liftFootprint_reduce_eq {d s : Type} (L : Lens d s) (S : Footprint s)
    (hS : S ≤ L.footprint) : L.liftFootprint (Lens.reduceFootprint L S) = S := by
  rcases isEmpty_or_nonempty s with hE | hNe
  · exact Footprint.empty_trivial (by rwa [not_nonempty_iff]) _ _
  · haveI := hNe
    have hextract : ∀ k ∈ L.footprint.updates, ∃ p, L.liftSubProbability p = k := by
      intro k hk
      have : k ∈ L.liftSubProbability '' (⊤ : Footprint d).updates := by
        rw [← fvP_extend_updates L ⊤, Lens.liftFootprint_top]; exact hk
      obtain ⟨p, -, hp⟩ := this; exact ⟨p, hp⟩
    refine le_antisymm ?_ ?_
    · -- `≤`: `L.liftFootprint (Lens.reduceFootprint L S) ≤ S`
      have hScomm' : (Sᶜ).updates = Set.centralizer S.updates := compl_updates S
      have hkey : { f : d → SubProbability d |
            (L.liftSubProbability f : s → SubProbability s) ∈ (Sᶜ).updates }
          = Set.centralizer { f : d → SubProbability d |
            (L.liftSubProbability f : s → SubProbability s) ∈ S.updates } := by
        ext f
        simp only [Set.mem_setOf_eq, Set.mem_centralizer_iff]
        constructor
        · intro hf h hh
          have hcomm : L.liftSubProbability h * L.liftSubProbability f
              = L.liftSubProbability f * L.liftSubProbability h := by
            rw [hScomm'] at hf; exact (Set.mem_centralizer_iff.mp hf) _ hh
          rw [← updateK_mul, ← updateK_mul] at hcomm; exact updateK_injective L hcomm
        · intro hf
          rw [hScomm', Set.mem_centralizer_iff]; intro k hk
          obtain ⟨p, rfl⟩ := hextract k (hS hk)
          have hpf : p * f = f * p := hf p hk
          rw [← updateK_mul, ← updateK_mul, hpf]
      have hH : Lens.reduceFootprint L S ≤ (Lens.reduceFootprint L Sᶜ)ᶜ := by
        intro p hp
        rw [reduce_updates_eq L S, hkey] at hp
        rw [compl_updates (Lens.reduceFootprint L Sᶜ), reduce_updates_eq L Sᶜ, Footprint.compl_compl S]
        exact hp
      intro u hu
      rw [fvP_extend_updates L (Lens.reduceFootprint L S)] at hu
      obtain ⟨f, hf, rfl⟩ := hu
      have hfc : f ∈ ((Lens.reduceFootprint L Sᶜ)ᶜ).updates := hH hf
      rw [show S.updates = Set.centralizer (Sᶜ).updates by
          rw [Footprint.updates_eq_centralizer_compl S]; rfl, Set.mem_centralizer_iff]
      intro w hw
      exact (liftSubProbability_comm_of_mem_reduce_compl hfc hw).symm
    · -- `≥`: `S ≤ L.liftFootprint (Lens.reduceFootprint L S)`
      intro u hu
      obtain ⟨u₀, hu₀⟩ := hextract u (hS hu)
      rw [fvP_extend_updates L (Lens.reduceFootprint L S)]
      refine ⟨u₀, ?_, hu₀⟩
      rw [Lens.reduceFootprint_alt_def, Footprint.from_updates]
      apply Set.subset_centralizer_centralizer
      rw [Set.mem_centralizer_iff]; intro f hf
      simp only [Set.mem_setOf_eq] at hf
      have hcomm : L.liftSubProbability f * u = u * L.liftSubProbability f := hf u hu
      rw [← hu₀, ← updateK_mul, ← updateK_mul] at hcomm
      exact updateK_injective L hcomm

-- TODO check name / relocate to `Language/Footprint.lean`.
/-- **Product-corner structure theorem, corner form.**  Reducing through `L`:
    `x ≤ A ⊔ (L.footprint)ᶜ`
    gives `Lens.reduceFootprint L x ≤ Lens.reduceFootprint L A` (the complement corner reduces to `⊥`), and the corner
    order-iso lifts that back to `x ≤ A`. -/
theorem corner_crux_aux {d s : Type} (L : Lens d s) {x A : Footprint s}
    (hAL : A ≤ L.footprint) (hxL : x ≤ L.footprint)
    (hx_sup : x ≤ A ⊔ (L.footprint)ᶜ) : x ≤ A := by
  have hred : Lens.reduceFootprint L x ≤ Lens.reduceFootprint L A := by
    have h1 := Lens.reduceFootprint_mono L hx_sup
    rw [Lens.reduceFootprint_sup, Lens.reduceFootprint_compl_footprint] at h1
    simpa using h1
  calc x = L.liftFootprint (Lens.reduceFootprint L x) := (liftFootprint_reduce_eq L x hxL).symm
    _ ≤ L.liftFootprint (Lens.reduceFootprint L A) := Lens.liftFootprint_mono L hred
    _ = A := liftFootprint_reduce_eq L A hAL

/-- **Product-corner structure theorem.**  For a lens-derived splitter `B`, an algebra `x` below
    `A ⊔ B` and orthogonal to `B` already lies below `A`.  Reduces to `corner_crux_aux` through the
    complement lens of `B` (`Bᶜ = l.compl.footprint`). -/
theorem corner_crux {s : Type} {x A B : Footprint s}
    (hB : B.FromLens) (hAB : A ≤ Bᶜ) (hx_sup : x ≤ A ⊔ B) (hx_perp : x ≤ Bᶜ) : x ≤ A := by
  obtain ⟨l, hl⟩ := hB
  have hBc : Bᶜ = (l.compl).footprint := (congrArg (·ᶜ) hl).trans (Lens.compl_footprint l)
  have hBB : ((l.compl).footprint)ᶜ = B := by
    rw [← Lens.compl_footprint l, Footprint.compl_compl]; exact hl.symm
  refine corner_crux_aux l.compl (hBc ▸ hAB) (hBc ▸ hx_perp) ?_
  rw [hBB]; exact hx_sup

open Classical in
/-- The minimal granular cover contains what it covers.

    The whole difficulty is isolated in `corner_crux` (the product-corner theorem): after
    rewriting with `granular_footprint`, the witnessing grain family splits into the touched grains
    `Tf` (which lie in the cover) and the untouched grains `U` (with `footprint ≤ gᶜ`).  The join
    `sSup U` is lens-derived and orthogonal to `sSup Tf`, and `footprint` is `≤ sSup Tf ⊔ sSup U`
    and `≤ (sSup U)ᶜ`, so `corner_crux` gives `footprint ≤ sSup Tf ≤ sSup (touched grains)`. -/
theorem Footprint.IsSubGranular.le_granular [spec : GranularProgramSpec]
    (footprint : Footprint State) (h : footprint.IsSubGranular) :
    footprint ≤ h.granularCover.footprint := by
  rw [Footprint.IsSubGranular.granular_footprint]
  obtain ⟨F, hF⟩ := h
  set T : Set (Footprint State) := { g ∈ spec.grains | ¬ footprint ≤ gᶜ } with hT
  set U : Set (Footprint State) := { g ∈ F.grains | footprint ≤ gᶜ } with hU
  set Tf : Set (Footprint State) := { g ∈ F.grains | ¬ footprint ≤ gᶜ } with hTf
  have hTf_T : Tf ⊆ T := fun g ⟨hgF, hgt⟩ => ⟨GranularFootprint.grains_subset F hgF, hgt⟩
  have hsplit : F.grains = Tf ∪ U := by
    ext g; by_cases hc : footprint ≤ gᶜ <;> simp [hTf, hU, hc]
  have hgrain_disj : ∀ g ∈ F.grains, ∀ g' ∈ F.grains, g ≠ g' → g ≤ g'ᶜ := fun g hg g' hg' hne =>
    spec.disjoint g (GranularFootprint.grains_subset F hg)
      g' (GranularFootprint.grains_subset F hg') hne
  have hAB : sSup Tf ≤ (sSup U)ᶜ := by
    rw [Footprint.le_compl_comm]
    refine sSup_le fun g hg => (Footprint.le_compl_comm _ _).mpr (sSup_le fun g' hg' => ?_)
    simp only [hTf, hU, Set.mem_setOf_eq] at hg hg'
    exact hgrain_disj g' hg'.1 g hg.1 (fun e => hg'.2 (e ▸ hg.2))
  have hFf : F.footprint = sSup Tf ⊔ sSup U := by
    rw [GranularFootprint.footprint, hsplit]; exact sSup_union
  have hx_sup : footprint ≤ sSup Tf ⊔ sSup U := hFf ▸ hF
  have hx_perp : footprint ≤ (sSup U)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr
      (sSup_le fun g hg => (Footprint.le_compl_comm _ _).mp ?_)
    simp only [hU, Set.mem_setOf_eq] at hg; exact hg.2
  have hUB : (sSup U).FromLens := by
    set Ufin : GranularFootprint :=
      (F.toFinset).filter (fun g => footprint ≤ (g.val : Footprint State)ᶜ) with hUfin
    have hUgrains : U = Ufin.grains := by
      ext g
      simp only [hU, GranularFootprint.grains, hUfin, GranularFootprint.toFinset,
        Finset.coe_filter, Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe]
      constructor
      · rintro ⟨⟨⟨g', hg'⟩, hmemF, rfl⟩, hle⟩
        exact ⟨⟨g', hg'⟩, ⟨hmemF, hle⟩, rfl⟩
      · rintro ⟨⟨g', hg'⟩, ⟨hmemF, hle⟩, rfl⟩
        exact ⟨⟨⟨g', hg'⟩, hmemF, rfl⟩, hle⟩
    rw [hUgrains]; exact GranularFootprint.footprint_fromLens Ufin
  exact le_trans (corner_crux hUB hAB hx_sup hx_perp) (sSup_le_sSup hTf_T)

end GaudisCrypt
