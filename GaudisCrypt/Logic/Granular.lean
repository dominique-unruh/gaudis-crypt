import GaudisCrypt.Logic.AbstractCall
import GaudisCrypt.Language.Granularity

/-!
# Granular regions: EasyCrypt's `glob M` as a lens region

EasyCrypt's memory is a set of whole variables, and `glob M` is the set of variables `M` touches.
Here the grains of the variable granularity (`variableGranularity`) are the variables' slots, and
the granular cover of a module's footprint (`Footprint.IsSubGranular.granularCover`) is its
`glob`: the slots it touches, whole.  A cover is a lens region
(`GranularFootprint.footprint_fromLens`),
so a run that stays out of it leaves its content unchanged
(`ProgramDenotation.preserves_touched_of_fromLens`) — which footprint-disjointness alone does not
give (`CounterExamples/FramingNeedsReset.lean`).  An EasyCrypt-like module has one
(`Footprint.FinitelySupported.isSubGranular`), and a restriction against a variable carries over
to the cover (`Footprint.IsSubGranular.granularCover_le_compl`).  Evaluation:
`notes/SHA3/GlobGranularity.md`.
-/

namespace GaudisCrypt

/-- A run confined to `R` keeps the content of a lens-derived region `Q` outside `R`. -/
theorem ProgramDenotation.preserves_touched_of_fromLens {a : Type}
    {p : ProgramDenotation VariableAssignment a} {R Q : Footprint VariableAssignment}
    (hp : p.inFootprint R) (hQ : Q.FromLens) (hQR : Q ≤ Rᶜ) (σ : VariableAssignment) :
    (p σ).satisfies (fun xs => Q.touched_getter.get xs.2 = Q.touched_getter.get σ) := by
  obtain ⟨l, hl⟩ := hQ
  exact Lib.RO.Instantiate.inFootprint_preserves_touched hp hQR
    (hl ▸ Lens.footprint_hasReset l σ)

/-- A sub-granular footprint outside a grain has its whole granular cover outside it. -/
theorem Footprint.IsSubGranular.granularCover_le_compl [spec : GranularProgramSpec]
    {F G : Footprint VariableAssignment} (hF : F.IsSubGranular) (hG : G ∈ spec.grains)
    (hFG : F ≤ Gᶜ) : hF.granularCover.footprint ≤ Gᶜ := by
  rw [Footprint.IsSubGranular.granularCover_footprint_eq_sSup]
  refine sSup_le fun g ⟨hg, hgF⟩ => ?_
  by_cases h : g = G
  · subst h; exact absurd hFG hgF
  · exact spec.disjoint g hg G hG h

/-- EasyCrypt's memory: the grains are the slots of the variables (of nontrivial types). -/
@[reducible] noncomputable def variableGranularity : GranularProgramSpec where
  grains := {F | ∃ v : VariableName, F = (varLens v).footprint ∧ F ≠ ⊥}
  from_lenses := by
    rintro F ⟨v, rfl, -⟩
    exact Lens.footprint_fromLens _
  disjoint := by
    rintro F ⟨v, rfl, -⟩ G ⟨w, rfl, -⟩ hne
    have hvw : v ≠ w := fun h => hne (h ▸ rfl)
    haveI := varLens_disjoint hvw
    exact Lens.footprint_le_compl_of_disjoint (varLens v) (varLens w)
  nonempty_grains := by
    rintro F ⟨v, rfl, h⟩
    exact h

open Classical in
/-- Finitely many variables cover a sub-granular footprint. -/
theorem Footprint.FinitelySupported.isSubGranular {F : Footprint VariableAssignment}
    (hF : F.FinitelySupported) : @Footprint.IsSubGranular variableGranularity F := by
  letI := variableGranularity
  obtain ⟨vs, hvs⟩ := hF
  let G : GranularFootprint := (vs.filterMap fun v =>
      if h : (GaudisCrypt.varLens v).footprint ≠ ⊥ then
        some (⟨(GaudisCrypt.varLens v).footprint, v, rfl, h⟩ : GranularProgramSpec.grains)
      else none).toFinset
  refine ⟨G, hvs.trans (iSup₂_le fun v hv => ?_)⟩
  by_cases h : (GaudisCrypt.varLens v).footprint = ⊥
  · rw [h]; exact bot_le
  · refine le_sSup ⟨⟨(GaudisCrypt.varLens v).footprint, v, rfl, h⟩, ?_, rfl⟩
    simp only [G, Finset.mem_coe, List.mem_toFinset, List.mem_filterMap]
    exact ⟨v, hv, by simp [h]⟩

end GaudisCrypt
