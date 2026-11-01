import GaudisCrypt.Logic.EagerProc
import GaudisCrypt.Logic.AbstractCall

/-!
# The eager abstract-call rule for modules (EasyCrypt's `eager proc` on `D(O)`)

`eager_call` (`Logic/EagerProc.lean`) is EasyCrypt's `eager proc` for a procedure with holes: it
needs the procedure's own steps to swap with the block (`SwapLoc`) and each hole call to be eager.
Here the first condition comes from footprints, as EasyCrypt's comes from its syntactic check
that the block and the adversary share no variables.

* `swapLoc_of_confinedP`: steps confined to a region `R` swap with a block confined to a region
  outside `R` (`transferBy_refl_of_inFootprint_compl`, step by step).
* `inFootprint_zoom_globalL`: a block on the globals confined to a lens `X` is, zoomed to
  procedure states, confined to `globalL.chain X`.
* `eager_call_module`: **EasyCrypt's `eager proc` for a module** `D : Module.Arr T (procmod …)`
  that is representable over `ext` and disjoint from `X`, for a block `S` confined to `X`: each
  oracle procedure of `ext O₁` eager against that of `ext O₂` makes `D(O₁)` eager against `D(O₂)`.
  At equality invariants; EasyCrypt's invariant `I` is added by a self-coupling
  (`ProgramDenotation.eagerR_of_self_right`).
-/

namespace GaudisCrypt

open GaudisCrypt.Lib.RO.Instantiate

/-- **Confined steps swap with a block outside their region**: `ConfinedP` gives `SwapLoc`. -/
theorem swapLoc_of_confinedP {holes : HoleSigs} {F R : Footprint ProgramState}
    {SL : ProgramDenotation ProgramState Unit} (hSL : SL.inFootprint F) (hR : R ≤ Fᶜ) :
    ∀ (A : StmtWithHoles holes), ConfinedP R A → SwapLoc SL A
  | .skip, _ => trivial
  | .sample _ _, h =>
      ProgramDenotation.transferBy_refl_of_inFootprint_compl hSL
        (ProgramDenotation.inFootprint_mono h hR)
  | .call' _ _ _ _ _ _ _, h =>
      ProgramDenotation.transferBy_refl_of_inFootprint_compl hSL
        (ProgramDenotation.inFootprint_mono h hR)
  | .hole _ _ _, h =>
      ⟨ProgramDenotation.transferBy_refl_of_inFootprint_compl hSL
          (ProgramDenotation.inFootprint_mono h.1 hR),
        fun ret => ProgramDenotation.transferBy_refl_of_inFootprint_compl hSL
          (ProgramDenotation.inFootprint_mono (h.2 ret) hR)⟩
  | .seq s1 s2, h => ⟨swapLoc_of_confinedP hSL hR s1 h.1, swapLoc_of_confinedP hSL hR s2 h.2⟩
  | .ifThenElse _ t e, h =>
      ⟨ProgramDenotation.transferBy_refl_of_inFootprint_compl hSL
          (ProgramDenotation.inFootprint_mono h.1 hR),
        swapLoc_of_confinedP hSL hR t h.2.1, swapLoc_of_confinedP hSL hR e h.2.2⟩
  | .«while» _ t, h =>
      ⟨ProgramDenotation.transferBy_refl_of_inFootprint_compl hSL
          (ProgramDenotation.inFootprint_mono h.1 hR),
        swapLoc_of_confinedP hSL hR t h.2⟩

/-- A block on the globals confined to `X`, zoomed to procedure states. -/
theorem inFootprint_zoom_globalL {Ω : Type} {X : Lens Ω VariableAssignment}
    {S : ProgramDenotation VariableAssignment Unit} (hS : S.inFootprint X.footprint) :
    (ProgramDenotation.zoom ProgramState.globalL S).inFootprint
      (ProgramState.globalL.chain X).footprint := by
  refine ProgramDenotation.inFootprint_of_footprint_le ?_
  refine le_trans (lift_footprint_le ProgramState.globalL S) ?_
  rw [Lens.footprint_chain]
  exact Lens.liftFootprint_mono _ (ProgramDenotation.footprint_le_of_inFootprint hS)

/-- **EasyCrypt's `eager proc` for an abstract module** (equality invariants): a block `S`
confined to `X`, and a representable module `D` disjoint from `X`, whose oracle procedures are
eager (`ext O₁` against `ext O₂`), make `D(O₁)` eager against `D(O₂)`. -/
theorem eager_call_module {Ω : Type} (X : Lens Ω VariableAssignment) {T : Type 1} [IsModule T]
    {sig : ProcedureSignature} {holes : HoleSigs} (D : Module.Arr T (Module.Proc sig))
    (ext : T → holes.Instantiation) (hD : Module.Representable D ext)
    (hdisj : FVP.fvP D ≤ (X.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (S : ProgramDenotation VariableAssignment Unit) (hS : S.inFootprint X.footprint)
    (O₁ O₂ : T)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (a : sig'.ParamType),
      ProgramDenotation.eagerR S S (fun σ₁ σ₂ => σ₁ = σ₂)
        (procedureDenotation ((ext O₁).lookup n) a) (procedureDenotation ((ext O₂).lookup n) a)
        (fun u v => u = v))
    (a : sig.ParamType) :
    ProgramDenotation.eagerR S S (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (Module.app D O₁).procedure a)
      (procedureDenotation (Module.app D O₂).procedure a)
      (fun u v => u = v) := by
  obtain ⟨p, hp⟩ := hD
  rw [hp.denote O₁ a, hp.denote O₂ a]
  have hC : fvP_proc p ≤ ((ProgramState.globalL.chain X).footprint)ᶜ :=
    fvP_proc_le_chain_compl X p (hp.fvP_le.trans hdisj)
  have hSL := inFootprint_zoom_globalL hS
  exact eager_call (ext O₁) (ext O₂) p a S
    (swapLoc_of_confinedP hSL hC p.body
      (confinedP_of_fv (fvP_proc p) hc p.body (fvP_stmt_body_le_fvP_proc p)))
    (ProgramDenotation.transferBy_refl_of_inFootprint_compl hSL
      (ProgramDenotation.inFootprint_mono
        (get_confinedP_of_fv _ (get_return_val_le_fvP_proc p)) hC))
    (fun n x q hq hx => eagerR_call S _ _ x q (horacle n) hq hx)

end GaudisCrypt
