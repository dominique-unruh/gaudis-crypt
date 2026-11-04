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

/-- **EasyCrypt's `call (: inv)` for an abstract module, the states equal except on `L`**: `D`
outside `L`, applied to two oracles that keep the states equal outside `L` and the relation `I` of
the two contents of `L`, keeps them too (`prhlProc_abstract_callF` at the complement of `L`).  With
`I` equality, the states are equal (`Lens.equal_outside_and_get_eq_iff`): EC's `sim` across a
call of an adversary whose oracles differ in code but not in behaviour. -/
theorem prhlProc_abstract_call_equal_outside_module {T : Type 1} [IsModule T]
    {sig : ProcedureSignature} {holes : HoleSigs} (D : Module.Arr T (Module.Proc sig))
    (ext : T → holes.Instantiation) (hD : Module.Representable D ext)
    (hdisj : FVP.fvP D ≤ (L.footprint)ᶜ) (I : Ω → Ω → Prop)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (O₁ O₂ : T)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))
        ((ext O₁).lookup n) ((ext O₂).lookup n)
        (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))
      (Module.app D O₁).procedure (Module.app D O₂).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂)) := by
  have e : ∀ g₁ g₂, globInvF L L.compl.footprint I g₁ g₂ ↔
      L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂) := fun g₁ g₂ => by
    rw [globInvF, Lens.footprint_touched_getter_eq_iff, Lens.equal_outside_iff_compl]
  obtain ⟨p, hden, hle⟩ := hD
  have h := prhlProc_abstract_callF L (ext O₁) (ext O₂) p L.compl.footprint
    (by rw [← Lens.compl_footprint]; exact hle.trans hdisj) (by rw [Lens.compl_footprint]) I hc
    (fun n => prhlProc_conseq (horacle n)
      (fun a₁ g₁ a₂ g₂ ⟨ha, hg⟩ => ⟨ha, (e g₁ g₂).mp hg⟩)
      (fun r₁ g₁ r₂ g₂ ⟨hr, hg⟩ => ⟨hr, (e g₁ g₂).mpr hg⟩))
  have h' : prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))
      (p.instantiate (ext O₁)) (p.instantiate (ext O₂))
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂)) :=
    prhlProc_conseq h (fun a₁ g₁ a₂ g₂ ⟨ha, hg⟩ => ⟨ha, (e g₁ g₂).mpr hg⟩)
    (fun r₁ g₁ r₂ g₂ ⟨hr, hg⟩ => ⟨hr, (e g₁ g₂).mp hg⟩)
  intro a₁ a₂
  rw [hden O₁ a₁, hden O₂ a₂]
  exact h' a₁ a₂

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

/-- `equal_outside` is symmetric. -/
theorem Lens.equal_outside.symm {g₁ g₂ : VariableAssignment} (h : L.equal_outside g₁ g₂) :
    L.equal_outside g₂ g₁ :=
  (L.equal_outside_setoid).iseqv.symm h

/-- `equal_outside` is transitive. -/
theorem Lens.equal_outside.trans {g₁ g₂ g₃ : VariableAssignment} (h : L.equal_outside g₁ g₂)
    (h' : L.equal_outside g₂ g₃) : L.equal_outside g₁ g₃ :=
  (L.equal_outside_setoid).iseqv.trans h h'

variable (L) in
/-- A write of `L` keeps a state equal to itself outside `L`. -/
theorem Lens.equal_outside_set_self (g : VariableAssignment) (v : Ω) :
    L.equal_outside g (L.set v g) := ⟨v, rfl⟩

/-- States equal outside `A` are equal outside `Lens.pair A B`. -/
theorem Lens.equal_outside.pair_left {α β : Type} {A : Lens α VariableAssignment}
    {B : Lens β VariableAssignment} [Lens.Disjoint A B] {g g' : VariableAssignment}
    (h : A.equal_outside g g') : (Lens.pair A B).equal_outside g g' := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨(x, B.get g), by simp only [Lens.pair, B.get_set]⟩

/-- States equal outside `B` are equal outside `Lens.pair A B`. -/
theorem Lens.equal_outside.pair_right {α β : Type} {A : Lens α VariableAssignment}
    {B : Lens β VariableAssignment} [hd : Lens.Disjoint A B] {g g' : VariableAssignment}
    (h : B.equal_outside g g') : (Lens.pair A B).equal_outside g g' := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨(A.get g, x), ?_⟩
  show A.set (A.get g) (B.set x g) = B.set x g
  have : A.get (B.set x g) = A.get g := @Lens.get_of_disjoint_set _ _ _ A B hd.symm x g
  conv_lhs => rw [← this]
  exact A.get_set _

/-- States equal outside `L` and on `L` are equal. -/
theorem Lens.equal_outside_and_get_eq_iff {g₁ g₂ : VariableAssignment} :
    L.equal_outside g₁ g₂ ∧ L.get g₁ = L.get g₂ ↔ g₁ = g₂ := by
  refine ⟨fun ⟨⟨x, hx⟩, hg⟩ => ?_, fun h => h ▸ ⟨Lens.equal_outside.refl g₁, rfl⟩⟩
  subst hx
  rw [L.set_get] at hg
  rw [← hg, L.get_set]

end GaudisCrypt
