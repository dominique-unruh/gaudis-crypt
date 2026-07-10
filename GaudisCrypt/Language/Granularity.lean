import GaudisCrypt.Language.Programs
-- TODO: layering debt. `pair_footprint` and its ~18-declaration closure (`liftFootprint_sup`,
-- `chain_footprint`, the `updateK`/bicommutant scaffolding) are Footprint-level results that
-- currently live in `GaudisCrypt.FV`, a range-framework file. Importing FV from `Language/`
-- inverts the documented Language → range-framework layering. Fix by splitting the
-- Footprint-level half of `FV.lean` into `Language/Footprint.lean`, then drop this import.
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

def _root_.GaudisCrypt.Footprint.IsGranular [spec : GranularProgramSpec] (f : Footprint spec.state) :=
  ∃ (F : GranularFootprint), f = GranularFootprint.footprint F

def _root_.GaudisCrypt.Footprint.IsSubGranular [spec : GranularProgramSpec] (f : Footprint spec.state) :=
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
/-- A **minimal granular cover** of a sub-granular footprint: a minimal sub-family of the
    witnessing granularity family that still covers `footprint`.  (This is the least granular
    footprint containing `footprint` *modulo* the open corner-projection/tensor question: every
    granular cover contains all atoms that `footprint` genuinely touches, but showing those atoms
    alone already cover `footprint` needs the product-corner structure theorem.  Minimality —
    no strict sub-family of the returned one covers — holds by construction;
    see `IsSubGranularFootprint.le_granular`.) -/
noncomputable def _root_.GaudisCrypt.Footprint.IsSubGranular.granular [spec : GranularProgramSpec]
    (footprint : Footprint State) (h : footprint.IsSubGranular) : GranularFootprint :=
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


open Classical in
/-- The minimal granular cover contains what it covers. -/
theorem _root_.GaudisCrypt.Footprint.IsSubGranular.le_granular [spec : GranularProgramSpec]
    (footprint : Footprint State) (h : footprint.IsSubGranular) :
    footprint ≤ (Footprint.IsSubGranular.granular footprint h).footprint :=
  /- (Finset.mem_filter.mp
    ((h.choose.powerset.filter
        fun G : Finset (Footprint State) => footprint ≤ sSup ↑G).exists_minimal
      ⟨h.choose, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset_self _, h.choose_spec.2⟩⟩).choose_spec.1).2 -/
  sorry

-- TODO: the next four declarations are general `Lens`/`Footprint` facts, not granularity facts.
-- `Lens.punit` belongs in `Language/Lens.lean`; `Footprint.fromLens_bot` and
-- `Lens.disjoint_of_footprint_le_compl` belong in `Language/Footprint.lean` (next to its converse
-- `Lens.footprint_le_compl_of_disjoint`). `Footprint.FromLens.sup` can only join them there once
-- `pair_footprint` moves out of `FV.lean` — see the layering TODO at the top of this file.

/-- The trivial lens onto `PUnit`: reads nothing, writes nothing. -/
-- TODO: Generalize: works with any singleton type
-- TODO: Rename → Lens.empty
def Lens.punit {s : Type} : Lens PUnit s where
  get _ := PUnit.unit
  set _ σ := σ
  set_set _ _ _ := rfl
  set_get _ _ := rfl
  get_set _ := rfl

/-- The empty footprint comes from the trivial lens. -/
theorem _root_.GaudisCrypt.Footprint.fromLens_bot {s : Type} : (⊥ : Footprint s).FromLens := by
  have h : (Lens.punit : Lens PUnit s).footprint = ⊥ := Lens.footprint_eq_bot_of_subsingleton _
  rw [← h]
  exact Lens.footprint_fromLens _

/-- **Converse of `Lens.footprint_le_compl_of_disjoint`**: lenses whose footprints lie in each
    other's commutant have commuting setters.  Both constant writes are Dirac kernels in their
    lens's footprint, so the commutant hypothesis makes them commute as kernels; evaluating at a
    state and stripping `pure` yields the plain set-commutation law. -/
theorem Lens.disjoint_of_footprint_le_compl {a b s : Type} (x : Lens a s) (y : Lens b s)
    (h : x.footprint ≤ (y.footprint)ᶜ) : disjoint x y := by
  refine ⟨fun st v w => ?_⟩
  have hx := x.diracKer_liftFunction_mem_footprint (Function.const _ v)
  have hy := y.diracKer_liftFunction_mem_footprint (Function.const _ w)
  have hcomm := Submonoid.mem_centralizer_iff.mp (h hx)
    (diracKer (y.liftFunction (Function.const _ w))) hy
  rw [diracKer_mul, diracKer_mul] at hcomm
  exact (SubProbability.pure_injective (congrFun hcomm st)).symm

/-- **Lens-derived footprints are closed under disjoint joins**: pair the two lenses (the
    disjointness instance comes from `Lens.disjoint_of_footprint_le_compl`) and read off
    `pair_footprint`. -/
theorem _root_.GaudisCrypt.Footprint.FromLens.sup {s : Type} {f g : Footprint s}
    (hf : f.FromLens) (hg : g.FromLens) (hd : f ≤ gᶜ) : (f ⊔ g).FromLens := by
  obtain ⟨l1, hl1⟩ := hf
  obtain ⟨l2, hl2⟩ := hg
  haveI : disjoint l1 l2 :=
    Lens.disjoint_of_footprint_le_compl l1 l2 (by rw [← hl1, ← hl2]; exact hd)
  rw [hl1, hl2, ← pair_footprint l1 l2]
  exact Lens.footprint_fromLens _

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
    (Footprint.IsSubGranular.granular f h).footprint
      = sSup { g ∈ spec.granularity | ¬ f ≤ gᶜ } := by
  unfold GranularFootprint.footprint Footprint.IsSubGranular.granular
  congr 1
  unfold GranularFootprint.grains
  ext g
  simp [Finset.mem_subtype, Set.Finite.mem_toFinset, and_comm]

theorem Lens.pair_isSubGranular [GranularProgramSpec] {lens1 : Lens a State} {lens2 : Lens b State} [disjoint lens1 lens2]
  (h1 : lens1.footprint.IsSubGranular) (h2 : lens2.footprint.IsSubGranular) :
  (lens1.pair lens2).footprint.IsSubGranular :=
  pair_footprint lens1 lens2 ▸ isSubGranularFootprint_closed_sup h1 h2

theorem Lens.pair_granular_sup [GranularProgramSpec] (lens1 : Lens a State) (lens2 : Lens b State) [disjoint lens1 lens2]
  (h1 : lens1.footprint.IsSubGranular) (h2 : lens2.footprint.IsSubGranular) :
  (Lens.pair_isSubGranular h1 h2).granular.footprint = h1.granular.footprint ⊔ h2.granular.footprint := by
  have hset : { g ∈ GranularProgramSpec.granularity | ¬ (lens1.pair lens2).footprint ≤ gᶜ }
      = { g ∈ GranularProgramSpec.granularity | ¬ lens1.footprint ≤ gᶜ }
        ∪ { g ∈ GranularProgramSpec.granularity | ¬ lens2.footprint ≤ gᶜ } := by
    ext g
    simp only [pair_footprint, Set.mem_setOf_eq, Set.mem_union, sup_le_iff, not_and_or]
    tauto
  rw [Footprint.IsSubGranular.granular_footprint, Footprint.IsSubGranular.granular_footprint,
    Footprint.IsSubGranular.granular_footprint, hset, sSup_union]
  rfl


end GaudisCrypt
