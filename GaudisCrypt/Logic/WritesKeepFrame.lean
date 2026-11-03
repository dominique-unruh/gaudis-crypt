import GaudisCrypt.Logic.SyntacticFrame

/-!
# Framing a procedure judgment by what both procedures keep

`prhlProc_globInvF_of_writesKeep` frames `glob D`. This is the same argument for any getter. If
neither procedure writes what `K₁`, `K₂` read, then a relation between those values survives the
two runs. EasyCrypt's `sim` and `call` frame such equalities implicitly. With it, a judgment proven
on a small part of the state, such as `prhlProc_refl_of_within`, extends to an invariant on the
rest.
-/

namespace GaudisCrypt

open GaudisCrypt.Lib.RO.Instantiate in
/-- **The syntactic frame for procedure judgments**: a relation `R` between `K₁` on the left and
`K₂` on the right, which the two bodies keep (`WritesKeep`), is added to both conditions. -/
theorem prhlProc_frame_of_writesKeep {α : Type} {sig : ProcedureSignature}
    {o₁ o₂ : Procedure sig}
    {A : sig.ParamType → VariableAssignment → sig.ParamType → VariableAssignment → Prop}
    {B : sig.ret → VariableAssignment → sig.ret → VariableAssignment → Prop}
    (K₁ K₂ : VariableAssignment → α) (R : α → α → Prop)
    (h₁ : StmtWithHoles.WritesKeep K₁ o₁.body) (h₂ : StmtWithHoles.WritesKeep K₂ o₂.body)
    (h : prhlProc A o₁ o₂ B) :
    prhlProc (fun a₁ g₁ a₂ g₂ => A a₁ g₁ a₂ g₂ ∧ R (K₁ g₁) (K₂ g₂)) o₁ o₂
      (fun r₁ g₁ r₂ g₂ => B r₁ g₁ r₂ g₂ ∧ R (K₁ g₁) (K₂ g₂)) := by
  intro a₁ a₂ g₁ g₂ ⟨hA, hR⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := h a₁ a₂ g₁ g₂ hA
  have hμ₁ : μ.satisfies (fun w => K₁ w.1.2 = K₁ g₁) :=
    coupling_satisfies_fst (by rw [hm1]; exact Procedure.satisfies_of_writesKeep _ o₁ h₁ a₁ g₁)
  have hμ₂ : μ.satisfies (fun w => K₂ w.2.2 = K₂ g₂) :=
    coupling_satisfies_snd (by rw [hm2]; exact Procedure.satisfies_of_writesKeep _ o₂ h₂ a₂ g₂)
  refine ⟨μ, hm1, hm2, fun w hw => ⟨hsat w hw, ?_⟩⟩
  rw [hμ₁ w hw, hμ₂ w hw]
  exact hR

end GaudisCrypt
