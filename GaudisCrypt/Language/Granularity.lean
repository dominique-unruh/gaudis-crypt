import GaudisCrypt.Language.Programs
-- TODO: layering debt (re-introduced deliberately). `corner_crux` and its supporting
-- reduce/extend lemmas (`fvP_reduce_compl_footprint`, `le_liftFootprint_reduce`,
-- `liftFootprint_reduce_le`, `corner_crux_aux`) are general `Footprint` facts that depend on
-- `fvP_reduce` (in `GaudisCrypt.FV`, a range-framework file). Importing FV from `Language/` inverts
-- the documented layering. Once these lemmas (and the `fvP_reduce` machinery they need) are
-- relocated to `Language/Footprint.lean`, drop this import.
import GaudisCrypt.FV

namespace GaudisCrypt

class GranularProgramSpec extends ProgramSpec where
  granularity : Set (Footprint State)
  from_lenses : ∀ f ∈ granularity, f.FromLens
  disjoint : ∀ f ∈ granularity, ∀ g ∈ granularity, f ≠ g → f ≤ gᶜ

def GranularFootprint [spec : GranularProgramSpec] := Finset spec.granularity

def GranularFootprint.grains [spec : GranularProgramSpec] (F : GranularFootprint) :
  Set (Footprint State) :=
    Subtype.val '' (↑(show Finset spec.granularity from F) : Set spec.granularity)

def GranularFootprint.grainsFinset [spec : GranularProgramSpec] (F : GranularFootprint) :
    Finset (Footprint State) :=
  Finset.map ⟨Subtype.val, Subtype.val_injective⟩ F

theorem GranularFootprint.grains_finite [spec : GranularProgramSpec] (F : GranularFootprint) :
    (F.grains).Finite :=
  (F.finite_toSet).image _

theorem GranularFootprint.grains_subset [spec : GranularProgramSpec] (F : GranularFootprint) :
    F.grains ⊆ spec.granularity := by
  simp [GranularFootprint.grains]

def GranularFootprint.footprint [spec : GranularProgramSpec]
    (F : GranularFootprint) : Footprint spec.state :=
  sSup F.grains

def Footprint.IsGranular [spec : GranularProgramSpec] (f : Footprint spec.state) :=
  ∃ (F : GranularFootprint), f = GranularFootprint.footprint F

def Footprint.IsSubGranular [spec : GranularProgramSpec] (f : Footprint spec.state) :=
  ∃ (F : GranularFootprint), f ≤ GranularFootprint.footprint F

/-- **Atomicity of the granularity**: a granularity element below the join of a finite
    granularity family is one of the members or trivial.  If `p ∉ F` it is disjoint from every
    member, hence below `(sSup ↑F)ᶜ ≤ pᶜ` — and a lens footprint inside its own commutant is `⊥`
    (`Lens.footprint_eq_bot_of_le_compl`). -/
theorem GranularProgramSpec.mem_or_eq_bot_of_le_sSup [spec : GranularProgramSpec]
    {p : Footprint State} (hp : p ∈ spec.granularity)
    {F : Finset (Footprint State)} (hF : ∀ q ∈ F, q ∈ spec.granularity)
    (hle : p ≤ sSup ↑F) : p ∈ F ∨ p = ⊥ := by
  by_cases hmem : p ∈ F
  · exact Or.inl hmem
  · refine Or.inr ?_
    have hsup : (sSup ↑F : Footprint State) ≤ pᶜ := by
      refine sSup_le fun q hq => ?_
      have hqF : q ∈ F := hq
      have hne : p ≠ q := fun h => hmem (h ▸ hqF)
      calc q = qᶜᶜ := (Footprint.compl_compl q).symm
        _ ≤ pᶜ := Footprint.compl_le_compl (spec.disjoint p hp q (hF q hqF) hne)
    obtain ⟨l, hl⟩ := spec.from_lenses p hp
    rw [hl]
    exact l.footprint_eq_bot_of_le_compl (hl ▸ hle.trans hsup)

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
    Finset spec.granularity := F

theorem GranularFootprint.le_iff_subset [spec : GranularProgramSpec] {f g : GranularFootprint} :
    f ≤ g ↔ (show Finset spec.granularity from f) ⊆ (show Finset spec.granularity from g) :=
  ⟨fun h => Finset.coe_subset.mp ((Set.image_subset_image_iff Subtype.val_injective).mp h),
   fun h => Set.image_mono (Finset.coe_subset.mpr h)⟩

open Classical in
noncomputable instance [spec : GranularProgramSpec] : Lattice GranularFootprint where
  sup f g := (f.toFinset ∪ g.toFinset : Finset spec.granularity)
  inf f g := (f.toFinset ∩ g.toFinset : Finset spec.granularity)
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

theorem GranularFootprint.footprint_mono [spec : GranularProgramSpec] {F G : GranularFootprint}
    (h : F ≤ G) : F.footprint ≤ G.footprint :=
  sSup_le_sSup h


open Classical in
/-- A **minimal granular cover** of a sub-granular footprint: the sub-family of the granularity of
    exactly the atoms `footprint` genuinely touches.  It is the least granular footprint containing
    `footprint` — that every touched atom is needed is immediate, and that these atoms already cover
    `footprint` is the product-corner structure theorem (`corner_crux`), applied in
    `Footprint.IsSubGranular.le_granular`. -/
noncomputable def Footprint.IsSubGranular.granular [spec : GranularProgramSpec]
    {footprint : Footprint State} (h : footprint.IsSubGranular) : GranularFootprint :=
  let grains := { f ∈ spec.granularity | ¬ footprint ≤ fᶜ }
  have finite : grains.Finite := by
    obtain ⟨F, hF⟩ := h
    apply Set.Finite.subset (GranularFootprint.grains_finite F)
    intro f hf
    have hf' : f ∈ spec.granularity ∧ ¬ footprint ≤ fᶜ := hf
    obtain ⟨hf_gran, hf_touch⟩ := hf'
    by_contra hf_not
    apply hf_touch
    refine le_trans hF (sSup_le fun g hg => ?_)
    have hg_gran : g ∈ spec.granularity := GranularFootprint.grains_subset F hg
    have hne : g ≠ f := fun e => hf_not (e ▸ hg)
    exact spec.disjoint g hg_gran f hf_gran hne
  (finite.toFinset).subtype (· ∈ spec.granularity)


-- `Footprint.IsSubGranular.le_granular` is proved at the end of this file: its proof depends on
-- `granular_footprint` and `GranularFootprint.footprint_fromLens`, both defined below.

-- TODO: Used only once. Inline
private theorem sSup_grains_fromLens [spec : GranularProgramSpec]
    (F : Finset spec.granularity) :
    (sSup (Subtype.val '' (↑F : Set spec.granularity)) : Footprint State).FromLens := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using Footprint.fromLens_bot
  | @insert p F hp ih =>
      rw [Finset.coe_insert, Set.image_insert_eq, sSup_insert]
      refine Footprint.FromLens.sup (spec.from_lenses p.val p.property) ih ?_
      have hsup : (sSup (Subtype.val '' (↑F : Set spec.granularity)) : Footprint State)
          ≤ (p.val)ᶜ := by
        refine sSup_le ?_
        rintro q ⟨⟨q, hq⟩, hqF, rfl⟩
        refine spec.disjoint q hq p.val p.property (fun e => hp ?_)
        exact (Subtype.ext e : (⟨q, hq⟩ : spec.granularity) = p) ▸ hqF
      calc (p.val : Footprint State) = (p.val)ᶜᶜ := (Footprint.compl_compl _).symm
        _ ≤ _ := Footprint.compl_le_compl hsup

/-- A granular footprint is a join of finitely many pairwise-disjoint lens footprints, hence
    itself lens-derived. -/
theorem GranularFootprint.footprint_fromLens [spec : GranularProgramSpec]
    (F : GranularFootprint) : F.footprint.FromLens :=
  sSup_grains_fromLens F

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
theorem _root_.GaudisCrypt.Footprint.IsSubGranular.granular_footprint [spec : GranularProgramSpec]
    (f : Footprint State) (h : f.IsSubGranular) :
    h.granular.footprint
      = sSup { g ∈ spec.granularity | ¬ f ≤ gᶜ } := by
  unfold GranularFootprint.footprint Footprint.IsSubGranular.granular
  congr 1
  unfold GranularFootprint.grains
  ext g
  simp [Finset.mem_subtype, Set.Finite.mem_toFinset, and_comm]

theorem Lens.pair_isSubGranular [GranularProgramSpec] {lens1 : Lens a State} {lens2 : Lens b State}
  [disjoint lens1 lens2] (h1 : lens1.footprint.IsSubGranular) (h2 : lens2.footprint.IsSubGranular) :
  (lens1.pair lens2).footprint.IsSubGranular :=
  pair_footprint lens1 lens2 ▸ isSubGranularFootprint_closed_sup h1 h2

theorem Lens.pair_granular_sup [GranularProgramSpec] (lens1 : Lens a State) (lens2 : Lens b State)
  [disjoint lens1 lens2] (h1 : lens1.footprint.IsSubGranular) (h2 : lens2.footprint.IsSubGranular) :
  (Lens.pair_isSubGranular h1 h2).granular.footprint
   = h1.granular.footprint ⊔ h2.granular.footprint := by
  have hset : { g ∈ GranularProgramSpec.granularity | ¬ (lens1.pair lens2).footprint ≤ gᶜ }
      = { g ∈ GranularProgramSpec.granularity | ¬ lens1.footprint ≤ gᶜ }
        ∪ { g ∈ GranularProgramSpec.granularity | ¬ lens2.footprint ≤ gᶜ } := by
    ext g
    simp only [pair_footprint, Set.mem_setOf_eq, Set.mem_union, sup_le_iff, not_and_or]
    tauto
  rw [Footprint.IsSubGranular.granular_footprint, Footprint.IsSubGranular.granular_footprint,
    Footprint.IsSubGranular.granular_footprint, hset, sSup_union]
  rfl

-- (`le_compl_comm` removed: use `Footprint.le_compl_comm` from `GaudisCrypt.FV`, now imported.)

/-! ### Corner order-iso and `corner_crux`

`corner_crux` (the product-corner structure theorem) is proved by reducing through the complement
lens `L := l.compl` of the splitter `B = l.footprint`: `Bᶜ = L.footprint`, and footprints below the
corner `L.footprint` are recovered by `L.liftFootprint ∘ fvP_reduce L` (the corner order-iso).  All
three helpers are general `Footprint` facts (TODO check name / relocate to `Language/Footprint.lean`
with the `fvP_reduce` machinery). -/

-- TODO check name / relocate to `Language/Footprint.lean`.
/-- **Reducing the complement corner kills it.**  `fvP_reduce L` sends `(L.footprint)ᶜ` to `⊥`:
    every `L`-lift already lies in `L.footprint`, which commutes with all of `(L.footprint)ᶜ`, so
    the reduce-generator condition holds vacuously for every base kernel. -/
@[simp]
theorem fvP_reduce_compl_footprint {d : Type} [ProgramSpec] (L : Lens d State) :
    fvP_reduce L ((L.footprint)ᶜ) = ⊥ := by
  rw [fvP_reduce_alt_def]
  have hset : { f : d → SubProbability d | ∀ g ∈ ((L.footprint)ᶜ).updates,
      (L.liftSubProbability f : State → SubProbability State) * g
        = g * L.liftSubProbability f } = Set.univ := by
    ext f; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; intro g hg
    have hlift := Mlocalized_in_footprint L f
    rw [Footprint.updates_eq_centralizer_compl (L.footprint)ᶜ, Footprint.compl_compl] at hg
    exact (Submonoid.mem_centralizer_iff.mp hg) _ hlift
  rw [hset]; apply footprint_eq_of_updates
  rw [Footprint.from_updates, Set.centralizer_centralizer_centralizer]
  change Set.centralizer Set.univ = (Footprint.from ∅).updates
  rw [Footprint.from_updates, Set.centralizer_empty, Set.top_eq_univ]

-- TODO check name / relocate to `Language/Footprint.lean`.
/-- **Corner order-iso, easy inclusion.**  A footprint below the corner `L.footprint` is recovered
    by `L.liftFootprint ∘ fvP_reduce L`: each `u ∈ S.updates` is an `L`-lift
    `L.liftSubProbability u₀` (extraction), and `u₀` commutes with the reduce generators because
    `updateK` is an injective
    monoid hom. -/
theorem le_liftFootprint_reduce {d : Type} [ProgramSpec] (L : Lens d State) (S : Footprint State)
    (hS : S ≤ L.footprint) : S ≤ L.liftFootprint (fvP_reduce L S) := by
  rcases isEmpty_or_nonempty State with hE | hNe
  · exact le_of_eq (Footprint.empty_trivial (by rwa [not_nonempty_iff]) _ _)
  · haveI := hNe
    intro u hu
    have huimg : u ∈ L.liftSubProbability '' (⊤ : Footprint d).updates := by
      rw [← fvP_extend_updates L ⊤, Lens.liftFootprint_top]; exact hS hu
    obtain ⟨u₀, -, hu₀⟩ := huimg
    rw [fvP_extend_updates L (fvP_reduce L S)]
    refine ⟨u₀, ?_, hu₀⟩
    rw [fvP_reduce_alt_def, Footprint.from_updates]
    apply Set.subset_centralizer_centralizer
    rw [Set.mem_centralizer_iff]; intro f hf
    simp only [Set.mem_setOf_eq] at hf
    have hcomm : L.liftSubProbability f * u = u * L.liftSubProbability f := hf u hu
    rw [← hu₀, ← updateK_mul, ← updateK_mul] at hcomm
    exact updateK_injective L hcomm

private theorem compl_updates {m : Type} (R : Footprint m) :
    (Rᶜ).updates = Set.centralizer R.updates := by
  rw [Footprint.updates_eq_centralizer_compl (Rᶜ), Footprint.compl_compl]; rfl

-- TODO check name / relocate to `Language/Footprint.lean`.
/-- **`fvP_reduce` in commutant form.**  `(fvP_reduce L R).updates` is the centralizer of the base
    kernels whose `L`-lift lands in `Rᶜ` (folding `fvP_reduce_alt_def` through `Footprint.from`). -/
theorem reduce_updates_eq {d : Type} [ProgramSpec] (L : Lens d State) (R : Footprint State) :
    (fvP_reduce L R).updates
      = Set.centralizer { f : d → SubProbability d |
          (L.liftSubProbability f : State → SubProbability State) ∈ (Rᶜ).updates } := by
  rw [fvP_reduce_alt_def, Footprint.from_updates, Set.centralizer_centralizer_centralizer]
  congr 1; ext f
  simp only [Set.mem_setOf_eq, compl_updates, Set.mem_centralizer_iff]
  constructor <;> intro h g hg <;> exact (h g hg).symm

-- TODO check name / relocate to `Language/Footprint.lean`.
/-- **Corner order-iso, hard inclusion.**  `L.liftFootprint ∘ fvP_reduce L` retracts onto
    `[⊥, L.footprint]`.  The pure-commutant obstruction (the center) is resolved by the key set
    identity `{f | L.lift f ∈ Sᶜ} = centralizer {f | L.lift f ∈ S}` — whose `⊇` direction extracts
    each `k ∈ S.updates` as an `L`-lift (using `S ≤ L.footprint`) — giving
    `fvP_reduce L S ≤ (fvP_reduce L Sᶜ)ᶜ`, after which `liftSubProbability_comm_of_mem_reduce_compl`
    forces every lifted reduce-generator to commute with `Sᶜ`, i.e. to lie in `S`. -/
theorem liftFootprint_reduce_le {d : Type} [ProgramSpec] (L : Lens d State) (S : Footprint State)
    (hS : S ≤ L.footprint) : L.liftFootprint (fvP_reduce L S) ≤ S := by
  rcases isEmpty_or_nonempty State with hE | hNe
  · exact le_of_eq (Footprint.empty_trivial (by rwa [not_nonempty_iff]) _ _)
  · haveI := hNe
    have hextract : ∀ k ∈ L.footprint.updates, ∃ p, L.liftSubProbability p = k := by
      intro k hk
      have : k ∈ L.liftSubProbability '' (⊤ : Footprint d).updates := by
        rw [← fvP_extend_updates L ⊤, Lens.liftFootprint_top]; exact hk
      obtain ⟨p, -, hp⟩ := this; exact ⟨p, hp⟩
    have hScomm' : (Sᶜ).updates = Set.centralizer S.updates := compl_updates S
    have hkey : { f : d → SubProbability d |
          (L.liftSubProbability f : State → SubProbability State) ∈ (Sᶜ).updates }
        = Set.centralizer { f : d → SubProbability d |
          (L.liftSubProbability f : State → SubProbability State) ∈ S.updates } := by
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
    have hH : fvP_reduce L S ≤ (fvP_reduce L Sᶜ)ᶜ := by
      intro p hp
      rw [reduce_updates_eq L S, hkey] at hp
      rw [compl_updates (fvP_reduce L Sᶜ), reduce_updates_eq L Sᶜ, Footprint.compl_compl S]
      exact hp
    intro u hu
    rw [fvP_extend_updates L (fvP_reduce L S)] at hu
    obtain ⟨f, hf, rfl⟩ := hu
    have hfc : f ∈ ((fvP_reduce L Sᶜ)ᶜ).updates := hH hf
    rw [show S.updates = Set.centralizer (Sᶜ).updates by
        rw [Footprint.updates_eq_centralizer_compl S]; rfl, Set.mem_centralizer_iff]
    intro w hw
    exact (liftSubProbability_comm_of_mem_reduce_compl hfc hw).symm

-- TODO check name / relocate to `Language/Footprint.lean`.
/-- **Product-corner structure theorem, corner form.**  Reducing through `L`:
    `x ≤ A ⊔ (L.footprint)ᶜ`
    gives `fvP_reduce L x ≤ fvP_reduce L A` (the complement corner reduces to `⊥`), and the corner
    order-iso lifts that back to `x ≤ A`. -/
theorem corner_crux_aux {d : Type} [ProgramSpec] (L : Lens d State) {x A : Footprint State}
    (hAL : A ≤ L.footprint) (hxL : x ≤ L.footprint)
    (hx_sup : x ≤ A ⊔ (L.footprint)ᶜ) : x ≤ A := by
  have hred : fvP_reduce L x ≤ fvP_reduce L A := by
    have h1 := fvP_reduce_mono L hx_sup
    rw [fvP_reduce_sup, fvP_reduce_compl_footprint] at h1
    simpa using h1
  calc x ≤ L.liftFootprint (fvP_reduce L x) := le_liftFootprint_reduce L x hxL
    _ ≤ L.liftFootprint (fvP_reduce L A) := Lens.liftFootprint_mono L hred
    _ ≤ A := liftFootprint_reduce_le L A hAL

/-- **Product-corner structure theorem.**  For a lens-derived splitter `B`, an algebra `x` below
    `A ⊔ B` and orthogonal to `B` already lies below `A`.  Reduces to `corner_crux_aux` through the
    complement lens of `B` (`Bᶜ = l.compl.footprint`). -/
theorem corner_crux [ProgramSpec] {x A B : Footprint State}
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
    footprint ≤ h.granular.footprint := by
  rw [Footprint.IsSubGranular.granular_footprint]
  obtain ⟨F, hF⟩ := h
  set T : Set (Footprint State) := { g ∈ spec.granularity | ¬ footprint ≤ gᶜ } with hT
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
