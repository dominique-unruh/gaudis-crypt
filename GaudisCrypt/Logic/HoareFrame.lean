import GaudisCrypt.Logic.Hoare
import GaudisCrypt.ProbProgramRange

/-!
# Framing a call by a footprint

EC's module restrictions (`A <: Adv {-Counter}`) say that an abstract procedure does not touch
some global state.  Here that is a footprint hypothesis,
`(procedureDenotation p args).inFootprint (L.footprint)ᶜ`, and the rules below turn it into Hoare
reasoning: a call to such a procedure leaves `L` as it was.
-/

namespace GaudisCrypt

/-- A procedure confined to the complement of `L`'s footprint keeps every property of `L`. -/
theorem hoareProc_frame {sig} (p : Procedure sig) {γ : Type*} (L : Lens γ VariableAssignment)
    (hp : ∀ args, (procedureDenotation p args).inFootprint (L.footprint)ᶜ) (P : γ → Prop) :
    hoareProc (fun _ σ => P (L.get σ)) p (fun _ σ => P (L.get σ)) := by
  classical
  refine hoareProc_of_wp fun args σ hP => ?_
  refine ProgramDenotation.wp_zero_of_lens_preserves_footprint (hp args) (v := L.get σ)
    (fun r hr => ?_) rfl
  exact Set.indicator_of_notMem (by simpa [hr] using hP) _

/-- The wp rule for a call to a procedure that does not touch `L`: `B` must hold after writing
    any result and any globals that agree with the old ones on `L`.  Use it with `hoare_call`:
    `hoare_call (hoare_call_frame L hp)`. -/
theorem hoare_call_frame {sig} {x : Setter sig.ret ProgramState} {p : Procedure sig}
    {args : Getter sig.ParamType ProgramState} {γ : Type*} (L : Lens γ VariableAssignment)
    (hp : ∀ a, (procedureDenotation p a).inFootprint (L.footprint)ᶜ) {B : ProgramState → Prop} :
    hoareStmt
      (fun σ => ∀ r g, L.get g = L.get σ.globals → B (x.set r (ProgramState.globalL.set g σ)))
      (Stmt.call x p args) B := fun σ hA =>
  hoare_call_wp x p args (hoareProc_frame p L hp (· = L.get σ.globals)) B σ
    ⟨rfl, fun r g h => hA r g h⟩

end GaudisCrypt
