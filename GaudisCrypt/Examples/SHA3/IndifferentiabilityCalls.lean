import GaudisCrypt.Examples.SHA3.Indifferentiability
import GaudisCrypt.Logic.AbstractCall

/-!
# Abstract calls of a simulator

EasyCrypt's `call (_ : inv)` on a simulator's procedure `S(F).init`, `S(F).f`, `S(F).fi` (in
`proc (inv)` of an outer abstract call): from `SIMULATOR.RepresentedBy`, each is a procedure with
the hole `F.f` (none for `init`), and the abstract call rule applies at a region `F ⊇ glob S`
(`prhlProc_abstract_callF`).  Used for the nested calls `Dist(…, S(F))` of the indifferentiability
proofs.
-/

namespace GaudisCrypt.SHA3.Indifferentiability
open GaudisCrypt
variable (p f_in f_out : Type) {Ω : Type} (L : Lens Ω VariableAssignment)

/-- The abstract call rule for a simulator's `init` (no oracle). -/
theorem SIMULATOR.call_init (S : SIMULATOR p f_in f_out)
    (hS : SIMULATOR.Representable p f_in f_out S)
    (F : Footprint VariableAssignment) (hSF : FVP.fvP S ≤ F) (hFL : F ≤ (L.footprint)ᶜ)
    (I : Ω → Ω → Prop) (F₁ F₂ : DFUNCTIONALITY p f_in f_out) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L F I g₁ g₂)
      (PRIMITIVE.init p f_in f_out (Module.app S F₁)).procedure
      (PRIMITIVE.init p f_in f_out (Module.app S F₂)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L F I g₁ g₂) := by
  obtain ⟨pinit, pf, pfi, hrep⟩ := hS
  intro a₁ a₂
  rw [hrep.init F₁ a₁, hrep.init F₂ a₂]
  exact prhlProc_abstract_callF (holes := .empty) L PUnit.unit PUnit.unit pinit F
    ((le_sup_left.trans (le_sup_left.trans hrep.fvP_le)).trans hSF) hFL I
    (fun n => nomatch n) (fun n => nomatch n) a₁ a₂

/-- A simulator's `init` does not depend on the functionality it is given: equal arguments and
globals give equal results and globals. -/
theorem SIMULATOR.init_eq (S : SIMULATOR p f_in f_out)
    (hS : SIMULATOR.Representable p f_in f_out S) (F₁ F₂ : DFUNCTIONALITY p f_in f_out) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (PRIMITIVE.init p f_in f_out (Module.app S F₁)).procedure
      (PRIMITIVE.init p f_in f_out (Module.app S F₂)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  obtain ⟨pinit, pf, pfi, hrep⟩ := hS
  intro a₁ a₂
  rw [hrep.init F₁ a₁, hrep.init F₂ a₂]
  exact prhlProc_refl _ a₁ a₂

/-- The abstract call rule for a simulator's `f`, whose oracle is the functionality's `f`. -/
theorem SIMULATOR.call_f (S : SIMULATOR p f_in f_out)
    (hS : SIMULATOR.Representable p f_in f_out S)
    (F : Footprint VariableAssignment) (hSF : FVP.fvP S ≤ F) (hFL : F ≤ (L.footprint)ᶜ)
    (I : Ω → Ω → Prop) [Countable f_in] (F₁ F₂ : DFUNCTIONALITY p f_in f_out)
    (horacle : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L F I g₁ g₂)
      (DFUNCTIONALITY.f p f_in f_out F₁).procedure (DFUNCTIONALITY.f p f_in f_out F₂).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L F I g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L F I g₁ g₂)
      (PRIMITIVE.f p f_in f_out (Module.app S F₁)).procedure
      (PRIMITIVE.f p f_in f_out (Module.app S F₂)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L F I g₁ g₂) := by
  obtain ⟨pinit, pf, pfi, hrep⟩ := hS
  intro a₁ a₂
  rw [hrep.f F₁ a₁, hrep.f F₂ a₂]
  exact prhlProc_abstract_callF L (simExt p f_in f_out F₁) (simExt p f_in f_out F₂) pf F
    ((le_sup_right.trans (le_sup_left.trans hrep.fvP_le)).trans hSF) hFL I
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable f_in)
      | succ n => nomatch n)
    (fun n => by cases n with
      | zero => exact horacle
      | succ n => nomatch n) a₁ a₂

/-- The abstract call rule for a simulator's `fi`. -/
theorem SIMULATOR.call_fi (S : SIMULATOR p f_in f_out)
    (hS : SIMULATOR.Representable p f_in f_out S)
    (F : Footprint VariableAssignment) (hSF : FVP.fvP S ≤ F) (hFL : F ≤ (L.footprint)ᶜ)
    (I : Ω → Ω → Prop) [Countable f_in] (F₁ F₂ : DFUNCTIONALITY p f_in f_out)
    (horacle : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L F I g₁ g₂)
      (DFUNCTIONALITY.f p f_in f_out F₁).procedure (DFUNCTIONALITY.f p f_in f_out F₂).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L F I g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L F I g₁ g₂)
      (PRIMITIVE.fi p f_in f_out (Module.app S F₁)).procedure
      (PRIMITIVE.fi p f_in f_out (Module.app S F₂)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L F I g₁ g₂) := by
  obtain ⟨pinit, pf, pfi, hrep⟩ := hS
  intro a₁ a₂
  rw [hrep.fi F₁ a₁, hrep.fi F₂ a₂]
  exact prhlProc_abstract_callF L (simExt p f_in f_out F₁) (simExt p f_in f_out F₂) pfi F
    (le_sup_right.trans hrep.fvP_le |>.trans hSF) hFL I
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable f_in)
      | succ n => nomatch n)
    (fun n => by cases n with
      | zero => exact horacle
      | succ n => nomatch n) a₁ a₂

end GaudisCrypt.SHA3.Indifferentiability
