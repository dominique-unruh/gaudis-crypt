import GaudisCrypt.Logic.AbstractCall

/-!
# States equal except on a lens

`Lens.equal_outside L g₁ g₂` (`Language/Lens.lean`): `g₂` is `g₁` with `L` overwritten.  The
relation EasyCrypt's `sim` keeps when the two programs differ only in variables the rest of the code
does not read (a local module's variable written on one side only, or written on both sides at
different times).  `prhlProc_self_equal_outside` is the call rule for it: a procedure that does not
touch `L`, on both sides.
-/

namespace GaudisCrypt

variable {Ω : Type} (L : Lens Ω VariableAssignment)

/-- `L.equal_outside g₁ g₂` (the states agree except on `L`) is agreement of the complement lens. -/
theorem Lens.equal_outside_iff_compl (g₁ g₂ : VariableAssignment) :
    L.equal_outside g₁ g₂ ↔ L.compl.get g₁ = L.compl.get g₂ :=
  ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

/-- **EasyCrypt's `sim` across a call, the states equal except on `L`**: a procedure that does not
touch `L`, called on both sides with equal arguments, keeps the states equal outside `L` and any
relation `I` of the two contents of `L` (`prhlProc_abstract_callF` without holes). -/
theorem prhlProc_self_equal_outside {sig : ProcedureSignature} (p : Procedure sig)
    (hp : FVP.fvP_proc p ≤ (L.footprint)ᶜ) (I : Ω → Ω → Prop) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂)) p p
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂)) := by
  have h := prhlProc_abstract_callF L (holes := .empty) PUnit.unit PUnit.unit p L.compl.footprint
    (by rw [← Lens.compl_footprint]; exact hp) (by rw [Lens.compl_footprint]) I
    (fun n => nomatch n) (fun n => nomatch n)
  simp only [ProcedureWithHoles.instantiate_empty] at h
  have e : ∀ g₁ g₂, globInvF L L.compl.footprint I g₁ g₂ ↔
      L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂) := fun g₁ g₂ => by
    rw [globInvF, Lens.footprint_touched_getter_eq_iff, Lens.equal_outside_iff_compl]
  refine prhlProc_conseq h (fun a₁ g₁ a₂ g₂ ⟨ha, hg⟩ => ⟨ha, (e g₁ g₂).mpr hg⟩)
    (fun r₁ g₁ r₂ g₂ ⟨hr, hg⟩ => ⟨hr, (e g₁ g₂).mp hg⟩)

/-- `prhlProc_self_equal_outside` for a module's procedure, bounded by the module's footprint. -/
theorem prhlProc_self_equal_outside_module {sig : ProcedureSignature} (M : Module.Proc sig)
    (hM : FVP.fvP M ≤ (L.footprint)ᶜ) (I : Ω → Ω → Prop) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))
      M.procedure M.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂)) := by
  refine prhlProc_self_equal_outside L M.procedure ?_ I
  have h : FVP.fvP M = FVP.fvP_proc M.procedure := by
    conv_lhs => rw [Module.Proc.eq_proc_procedure M]
    exact FVP.fvP_module_proc _
  rwa [← h]

variable {L}

/-- The same write of a lens disjoint from `L` keeps the states equal outside `L`. -/
theorem Lens.equal_outside.set_disjoint {β : Type} {X : Lens β VariableAssignment}
    [hd : Lens.Disjoint X L] {g₁ g₂ : VariableAssignment} (h : L.equal_outside g₁ g₂) (v : β) :
    L.equal_outside (X.set v g₁) (X.set v g₂) := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨x, (hd.commute g₁ v x).symm⟩

/-- States equal outside `L` agree on every lens disjoint from `L`. -/
theorem Lens.equal_outside.get_disjoint {β : Type} {X : Lens β VariableAssignment}
    [hd : Lens.Disjoint X L] {g₁ g₂ : VariableAssignment} (h : L.equal_outside g₁ g₂) :
    X.get g₁ = X.get g₂ := by
  obtain ⟨x, rfl⟩ := h
  exact (@Lens.get_of_disjoint_set _ _ _ X L hd.symm x g₁).symm

/-- A write of `L` on one side keeps the states equal outside `L`. -/
theorem Lens.equal_outside.set_right {g₁ g₂ : VariableAssignment} (h : L.equal_outside g₁ g₂)
    (v : Ω) : L.equal_outside g₁ (L.set v g₂) := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨v, by rw [L.set_set]⟩

/-- Every state is equal to itself outside `L`. -/
theorem Lens.equal_outside.refl (g : VariableAssignment) : L.equal_outside g g :=
  ⟨L.get g, L.get_set g⟩

/-- A write of `L` on the left keeps the states equal outside `L`. -/
theorem Lens.equal_outside.set_left {g₁ g₂ : VariableAssignment} (h : L.equal_outside g₁ g₂)
    (v : Ω) : L.equal_outside (L.set v g₁) g₂ := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨x, by rw [L.set_set]⟩

end GaudisCrypt
