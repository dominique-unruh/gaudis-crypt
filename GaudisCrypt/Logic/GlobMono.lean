import GaudisCrypt.Logic.FootprintSolver

/-!
# `glob` is monotone

EasyCrypt's `glob` (`Footprint.glob`, the slots of the variables a footprint touches) grows with
the footprint: a variable touched by `F ≤ F'` is touched by `F'`.  A region `G` within `glob GF`
then stays within `glob (GF ⊔ X)`, which is how a region hypothesis (exception E14 in
`notes/SHA3/Exceptions.md`) is extended by further variables.  A `global_var` is finitely
supported, and outside `glob F` when outside `F` (for `F` finitely supported).
-/

namespace GaudisCrypt

/-- A footprint below a sub-granular one is sub-granular. -/
theorem Footprint.IsSubGranular.mono [spec : GranularProgramSpec]
    {F F' : Footprint VariableAssignment} (h : F ≤ F') (hF' : F'.IsSubGranular) :
    F.IsSubGranular :=
  ⟨hF'.choose, h.trans hF'.choose_spec⟩

/-- **`glob` is monotone.** -/
theorem Footprint.glob_mono {F F' : Footprint VariableAssignment} (h : F ≤ F') :
    F.glob ≤ F'.glob := by
  letI := variableGranularity
  unfold Footprint.glob
  split
  · next hF =>
    split
    · next hF' =>
      rw [Footprint.IsSubGranular.granularCover_footprint_eq_sSup _ hF,
        Footprint.IsSubGranular.granularCover_footprint_eq_sSup _ hF']
      exact sSup_le_sSup fun g ⟨hg, hgF⟩ => ⟨hg, fun h' => hgF (h.trans h')⟩
    · exact le_top
  · next hF =>
    split
    · next hF' => exact absurd (hF'.mono h) hF
    · exact le_rfl

/-- A `global_var` is finitely supported (it is a single variable's slot). -/
theorem Footprint.FinitelySupported.globalVar {T : Type} (x : Lens T VariableAssignment)
    {v : VariableName} [h : Lens.IsGlobalVar x v] : x.footprint.FinitelySupported := by
  obtain ⟨hT, hx⟩ := h
  cases v
  subst hT
  cases eq_of_heq hx
  exact Footprint.FinitelySupported.varLens _

/-- A `global_var` outside a finitely supported `F` is outside `glob F`
(`Footprint.varLens_le_compl_glob` for a `global_var`). -/
theorem Footprint.globalVar_le_compl_glob {F : Footprint VariableAssignment}
    (hF : F.FinitelySupported) {T : Type} (x : Lens T VariableAssignment) {v : VariableName}
    [h : Lens.IsGlobalVar x v] (hx : F ≤ x.footprintᶜ) : x.footprint ≤ F.globᶜ := by
  obtain ⟨hT, hxv⟩ := h
  cases v
  subst hT
  cases eq_of_heq hxv
  exact Footprint.varLens_le_compl_glob hF _ hx

end GaudisCrypt
