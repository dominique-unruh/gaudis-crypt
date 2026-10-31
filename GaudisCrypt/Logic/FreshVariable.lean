import GaudisCrypt.Language.Footprint
import GaudisCrypt.Language.Variables

/-!
# Fresh variables

EasyCrypt gives a `local module` or a `local clone` declared in a section new global variables,
disjoint from those of every module the section declares.  Here such variables are lens
parameters of the local declarations, with freshness hypotheses (exception E6 of the SHA-3 port),
and a non-local result instantiates them with lenses that are actually fresh.

Fresh lenses need not exist for an arbitrary footprint: a statement's getters are arbitrary
functions of the state, so a module may read, say, every `ℤ`-typed slot, and then no `ℤ`-typed
variable is fresh for it.  EasyCrypt's modules have finitely many global variables.  This file
states that as `Footprint.FinitelySupported`: the footprint lies within the slots of finitely many
variable names.  Under it, `Footprint.exists_fresh` gives a fresh variable of any nonempty type,
itself finitely supported, so that several fresh variables can be chosen one after the other.
-/

namespace GaudisCrypt

/-- The footprint lies within the slots of the finitely many variables `vs`. -/
def Footprint.FinitelySupported (F : Footprint VariableAssignment) : Prop :=
  ∃ vs : List VariableName, F ≤ ⨆ v ∈ vs, (varLens v).footprint

theorem Footprint.FinitelySupported.mono {F G : Footprint VariableAssignment} (h : F ≤ G)
    (hG : G.FinitelySupported) : F.FinitelySupported := by
  obtain ⟨vs, hvs⟩ := hG
  exact ⟨vs, h.trans hvs⟩

theorem Footprint.FinitelySupported.bot : (⊥ : Footprint VariableAssignment).FinitelySupported :=
  ⟨[], bot_le⟩

theorem Footprint.FinitelySupported.sup {F G : Footprint VariableAssignment}
    (hF : F.FinitelySupported) (hG : G.FinitelySupported) : (F ⊔ G).FinitelySupported := by
  obtain ⟨vs, hvs⟩ := hF
  obtain ⟨ws, hws⟩ := hG
  refine ⟨vs ++ ws, sup_le (hvs.trans ?_) (hws.trans ?_)⟩ <;>
  · refine iSup₂_le fun v hv => ?_
    exact le_iSup₂_of_le (f := fun v (_ : v ∈ vs ++ ws) => (varLens v).footprint) v
      (by simp [hv]) le_rfl

/-- The slot of a single variable is finitely supported. -/
theorem Footprint.FinitelySupported.varLens (v : VariableName) :
    (GaudisCrypt.varLens v).footprint.FinitelySupported :=
  ⟨[v], le_iSup₂_of_le (f := fun w (_ : w ∈ [v]) => (GaudisCrypt.varLens w).footprint) v
    (by simp) le_rfl⟩

/-- A name longer than every name in `vs`, so different from all of them. -/
private def freshName (vs : List VariableName) : String :=
  String.ofList (List.replicate ((vs.map fun v => v.name.length).sum + 1) 'x')

private theorem freshName_ne (vs : List VariableName) (v : VariableName) (hv : v ∈ vs) :
    freshName vs ≠ v.name := by
  intro h
  have hlen : (freshName vs).length = (vs.map fun v => v.name.length).sum + 1 := by
    simp [freshName, String.length]
  have hle : v.name.length ≤ (vs.map fun v => v.name.length).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨v, hv, rfl⟩)
  rw [h] at hlen
  omega

/-- **Fresh variables.**  For a finitely supported footprint `F` and a nonempty type `T`, some
variable of type `T` lies outside `F`; its slot is itself finitely supported. -/
theorem Footprint.exists_fresh (T : Type) [Nonempty T] {F : Footprint VariableAssignment}
    (hF : F.FinitelySupported) :
    ∃ L : Lens T VariableAssignment, L.footprint ≤ Fᶜ ∧ L.footprint.FinitelySupported := by
  obtain ⟨vs, hvs⟩ := hF
  let w : VariableName :=
    { name := freshName vs, type := T, key := VariableName.encode (freshName vs),
      keyCorrect := rfl }
  refine ⟨varLens w, ?_, Footprint.FinitelySupported.varLens w⟩
  refine le_trans ?_ (Footprint.compl_antimono hvs)
  rw [Footprint.le_compl_comm]
  refine iSup₂_le fun v hv => ?_
  have hne : v ≠ w := fun h => freshName_ne vs v hv (by rw [h])
  haveI := varLens_disjoint hne
  exact Lens.footprint_le_compl_of_disjoint (varLens v) (varLens w)

end GaudisCrypt
