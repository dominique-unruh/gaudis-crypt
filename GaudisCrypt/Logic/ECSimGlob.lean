import GaudisCrypt.Logic.ECCallOneSided
import GaudisCrypt.Logic.ECCallAbstract

/-!
# EasyCrypt's `sim` with `glob` equalities: the call rule

EC's `sim` works with a set of equal variables and `glob`s: a call of the same procedure `M` on
both sides keeps `glob M` equal (it is in the set), and the other variables of the set, which `M`
does not touch, unchanged.  `prhlStmt_seq_call_glob` is that step for a region `R` kept equal
(`M` inside it: `prhlProc_glob_module`) and a frame `Fr` of `M` on each side (what `M` keeps:
`Module.Proc.frame_lens`, `frame_glob`).  `sim` (`Logic/ECSim.lean`) uses it at a call when the
judgment's precondition keeps a region `R` equal containing the callee.
-/

namespace GaudisCrypt

open GaudisCrypt.Lib.RO.Instantiate

variable {A B : ProgramState → ProgramState → Prop} {s₁ s₂ : Stmt}

/-- **A call of the same procedure, a region kept equal** (EC's `sim` through a call): equal
arguments and states equal on `R` (the callee inside `R`) before; after, equal results, states
equal on `R`, and each side's globals in the frame `Fr` of its own before the call. -/
theorem prhlStmt_seq_call_glob (R : Footprint VariableAssignment) {sig : ProcedureSignature}
    {M : Module.Proc sig} (hM : FVP.fvP M ≤ R)
    {Fr : VariableAssignment → VariableAssignment → Prop} (hFr : M.Frame Fr)
    {x₁ x₂ : Setter sig.ret ProgramState} {e₁ e₂ : Getter sig.ParamType ProgramState}
    (hpre : prhlStmt A s₁ s₂ fun σ₁ σ₂ => e₁.get σ₁ = e₂.get σ₂ ∧
      R.touched_getter.get σ₁.globals = R.touched_getter.get σ₂.globals ∧
      ∀ r g₁ g₂, R.touched_getter.get g₁ = R.touched_getter.get g₂ →
        Fr σ₁.globals g₁ → Fr σ₂.globals g₂ →
        B (x₁.set r (ProgramState.globalL.set g₁ σ₁)) (x₂.set r (ProgramState.globalL.set g₂ σ₂))) :
    prhlStmt A (.seq s₁ (Stmt.call x₁ M.procedure e₁)) (.seq s₂ (Stmt.call x₂ M.procedure e₂))
      B := by
  refine prhlStmt_seq (B := fun σ₁ σ₂ => _) ?_ hpre
  intro σ₁ σ₂ ⟨he, hR, hB⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := prhlProc_glob_module M hM (e₁.get σ₁) (e₂.get σ₂) σ₁.globals
    σ₂.globals ⟨he, hR⟩
  have hμ₁ : μ.satisfies (fun w => Fr σ₁.globals w.1.2) :=
    coupling_satisfies_fst (by rw [hm1]; exact hFr _ _)
  have hμ₂ : μ.satisfies (fun w => Fr σ₂.globals w.2.2) :=
    coupling_satisfies_snd (by rw [hm2]; exact hFr _ _)
  refine ⟨μ >>= fun w => pure (((), x₁.set w.1.1 (ProgramState.globalL.set w.1.2 σ₁)),
    ((), x₂.set w.2.1 (ProgramState.globalL.set w.2.2 σ₂))), ?_, ?_, ?_⟩
  · refine SubProbability.marginal_fst_eq fun F => ?_
    rw [SubProbability.expected_map, SubProbability.expected_fst_of_marginal hm1
      (fun r => F ((), x₁.set r.1 (ProgramState.globalL.set r.2 σ₁))),
      programDenotation_call_apply, SubProbability.expected_hbind]
    simp only [expected_pure]
  · refine SubProbability.marginal_snd_eq fun F => ?_
    rw [SubProbability.expected_map, SubProbability.expected_snd_of_marginal hm2
      (fun r => F ((), x₂.set r.1 (ProgramState.globalL.set r.2 σ₂))),
      programDenotation_call_apply, SubProbability.expected_hbind]
    simp only [expected_pure]
  · refine SubProbability.satisfies_bind _ fun w hw => SubProbability.satisfies_pure _ _ ?_
    obtain ⟨hr, hRw⟩ := hsat w hw
    simp only
    rw [← hr]
    exact hB w.1.1 w.1.2 w.2.2 hRw (hμ₁ w hw) (hμ₂ w hw)

end GaudisCrypt
