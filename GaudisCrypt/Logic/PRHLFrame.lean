import GaudisCrypt.Logic.HoareFrame
import GaudisCrypt.Logic.AbstractCallUpto
import GaudisCrypt.Logic.EqualOutside

/-!
# Framing a procedure judgment by footprints

EasyCrypt's `call` keeps everything the two callees do not touch (its module restrictions frame
the rest of the memory).  `prhlProc_frame_lens` is that for procedures confined to footprints: a
relation between a lens outside the left callee's footprint and one outside the right callee's is
added to both conditions (`hoareProc_frame` on each side).  `prhlProc_frame_equal_outside` is
its instance at the complement of a lens `L`: callees that only touch `L` keep the states equal
outside `L` (`Lens.equal_outside`), the frame of `prhlProc_abstract_call_equal_outside_module`'s
oracle premise.
-/

namespace GaudisCrypt

variable {sig₁ sig₂ : ProcedureSignature} {p₁ : Procedure sig₁} {p₂ : Procedure sig₂}
  {A : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop}
  {B : sig₁.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop}

open GaudisCrypt.Lib.RO.Instantiate in
/-- **The frame rule for footprints**: a relation `R` between `X₁` (untouched by `p₁`) and `X₂`
(untouched by `p₂`) is kept. -/
theorem prhlProc_frame_lens {α β : Type*} (X₁ : Lens α VariableAssignment)
    (X₂ : Lens β VariableAssignment)
    (h₁ : ∀ a, (procedureDenotation p₁ a).inFootprint (X₁.footprint)ᶜ)
    (h₂ : ∀ a, (procedureDenotation p₂ a).inFootprint (X₂.footprint)ᶜ) (R : α → β → Prop)
    (h : prhlProc A p₁ p₂ B) :
    prhlProc (fun a₁ g₁ a₂ g₂ => A a₁ g₁ a₂ g₂ ∧ R (X₁.get g₁) (X₂.get g₂)) p₁ p₂
      (fun r₁ g₁ r₂ g₂ => B r₁ g₁ r₂ g₂ ∧ R (X₁.get g₁) (X₂.get g₂)) := by
  intro a₁ a₂ g₁ g₂ ⟨hA, hR⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := h a₁ a₂ g₁ g₂ hA
  have hμ₁ : μ.satisfies (fun w => X₁.get w.1.2 = X₁.get g₁) :=
    coupling_satisfies_fst (by
      rw [hm1]
      exact (hoareProc_frame p₁ X₁ h₁ (· = X₁.get g₁)).satisfies (a := a₁) (g := g₁) rfl)
  have hμ₂ : μ.satisfies (fun w => X₂.get w.2.2 = X₂.get g₂) :=
    coupling_satisfies_snd (by
      rw [hm2]
      exact (hoareProc_frame p₂ X₂ h₂ (· = X₂.get g₂)).satisfies (a := a₂) (g := g₂) rfl)
  refine ⟨μ, hm1, hm2, fun w hw => ⟨hsat w hw, ?_⟩⟩
  rw [hμ₁ w hw, hμ₂ w hw]
  exact hR

/-- **Callees confined to `L` keep the states equal outside `L`** (`prhlProc_frame_lens` at the
complement of `L`). -/
theorem prhlProc_frame_equal_outside {Ω : Type} (L : Lens Ω VariableAssignment)
    (h₁ : ∀ a, (procedureDenotation p₁ a).inFootprint L.footprint)
    (h₂ : ∀ a, (procedureDenotation p₂ a).inFootprint L.footprint)
    (h : prhlProc A p₁ p₂ B) :
    prhlProc (fun a₁ g₁ a₂ g₂ => A a₁ g₁ a₂ g₂ ∧ L.equal_outside g₁ g₂) p₁ p₂
      (fun r₁ g₁ r₂ g₂ => B r₁ g₁ r₂ g₂ ∧ L.equal_outside g₁ g₂) := by
  have hc : (L.compl.footprint)ᶜ = L.footprint := by rw [← Lens.compl_footprint, Footprint.compl_compl]
  have h' := prhlProc_frame_lens L.compl L.compl (fun a => by rw [hc]; exact h₁ a)
    (fun a => by rw [hc]; exact h₂ a) Eq h
  refine prhlProc_conseq h' (fun a₁ g₁ a₂ g₂ ⟨hA, he⟩ => ⟨hA, ?_⟩)
    (fun r₁ g₁ r₂ g₂ ⟨hB, he⟩ => ⟨hB, ?_⟩)
  · exact (Lens.equal_outside_iff_compl L g₁ g₂).mp he
  · exact (Lens.equal_outside_iff_compl L g₁ g₂).mpr he

/-- `prhlProc_frame_equal_outside` for modules' procedures, by their footprints. -/
theorem prhlProc_frame_equal_outside_module {Ω : Type} (L : Lens Ω VariableAssignment)
    (M₁ : Module.Proc sig₁) (M₂ : Module.Proc sig₂)
    (h₁ : FVP.fvP M₁ ≤ L.footprint) (h₂ : FVP.fvP M₂ ≤ L.footprint)
    (h : prhlProc A M₁.procedure M₂.procedure B) :
    prhlProc (fun a₁ g₁ a₂ g₂ => A a₁ g₁ a₂ g₂ ∧ L.equal_outside g₁ g₂) M₁.procedure M₂.procedure
      (fun r₁ g₁ r₂ g₂ => B r₁ g₁ r₂ g₂ ∧ L.equal_outside g₁ g₂) :=
  prhlProc_frame_equal_outside L
    (fun a => ProgramDenotation.inFootprint_mono (Module.Proc.inFootprint_fvP _ a) h₁)
    (fun a => ProgramDenotation.inFootprint_mono (Module.Proc.inFootprint_fvP _ a) h₂) h

end GaudisCrypt
