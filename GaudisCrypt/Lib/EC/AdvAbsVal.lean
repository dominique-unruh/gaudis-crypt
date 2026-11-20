import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECCallEquiv
import GaudisCrypt.Logic.ECInline
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.PrTactics

/-!
# Absolute values of advantages (EasyCrypt `theories/crypto/AdvAbsVal.ec`)

EC's module type `Adv` (one procedure `main : unit -> bool`) is a procedure module,
`procmod () → Bool`; `Neg_main(A)` negates its answer.  `Neg_A_Pr_minus` is how EC turns a bound
on `Pr[A.main() : res]` into one on `Pr[A.main() : !res]` for a lossless `A`, and `abs_val` how
a bound on the signed advantage gives one on its absolute value.  EC's `Pr[mu_not]` is
`Pr_mu_not`.
-/

namespace GaudisCrypt.EC.AdvAbsVal

open GaudisCrypt

/-- EC's `module type Adv = { proc main () : bool }`: one procedure, a procedure module. -/
abbrev Adv := procmod () → Bool

-- EC's `module Neg_main (A:Adv) = { proc main () : bool = { var b : bool; b <@ A.main ();
-- return !b; } }`
module Neg_main using (A : Adv) {
  proc main () : Bool {
    var b : Bool;
    b <- call A ();
    return !$b
  };
}

/-- EC's `Pr[mu_not]`: the probability of `!E` is that of `true` minus that of `E`. -/
theorem Pr_mu_not {sig : ProcedureSignature} (p : Procedure sig) (args : sig.ParamType)
    (σ : VariableAssignment) (E : sig.ret → VariableAssignment → Prop) :
    ((p.Pr args σ (fun r g => ¬ E r g) : NNReal) : ℝ) =
      ((p.Pr args σ (fun _ _ => True) : NNReal) : ℝ) - ((p.Pr args σ E : NNReal) : ℝ) := by
  have h1 : (p.Pr args σ (fun r g => ¬ E r g) : ENNReal) + p.Pr args σ E =
      p.Pr args σ (fun _ _ => True) := by
    rw [Procedure.Pr_eq_ewp, Procedure.Pr_eq_ewp, Procedure.Pr_eq_ewp, ← Procedure.ewp_add]
    congr 1; funext v g
    by_cases h : E v g <;> simp [indicatorE, h]
  have h2 := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top] at h2
  simp only [ENNReal.coe_toReal] at h2
  linarith

section

declare module A <: Adv

/-- EC's `equiv Neg_A (A<:Adv) : Neg_main(A).main ~ A.main : ={glob A} ==> res{1} = !res{2}`. -/
theorem Neg_A : equiv[ Neg_main(A).main ~ A : ={glob A} ==> §res{1} = !§res{2} ] := by
  -- EC: proc *; inline{1} Neg_main(A).main.
  equiv_proc_to_stmt; stmt_inline{1} 0
  -- EC: by wp; call (: true).
  stmt_wp
  equiv_call (_ : True)
  ec_auto

/-- EC's `lemma Neg_A_Pr (A<:Adv) &m:
Pr[Neg_main(A).main() @ &m : res] = Pr[A.main() @ &m : !res]`. -/
theorem Neg_A_Pr (m : VariableAssignment) :
    Pr[ Neg_main(A).main () @ &m : §res ] = Pr[ A () @ &m : ¬ §res ] := by
  -- EC: by byequiv (Neg_A A).
  byequiv (Neg_A A)

/-- EC's `lemma Neg_A_Pr_minus (A<:Adv) &m: islossless A.main =>
Pr[Neg_main(A).main() @ &m : res] = 1%r - Pr[A.main() @ &m : res]`. -/
theorem Neg_A_Pr_minus (m : VariableAssignment) (Hl : islossless A) :
    Pr[ Neg_main(A).main () @ &m : §res ] = 1 - Pr[ A () @ &m : §res ] := by
  -- EC: move=> Hl; rewrite (Neg_A_Pr A &m); rewrite Pr[mu_not]; congr => //.
  rw [Neg_A_Pr A m, Pr_mu_not]; congr 1
  -- EC: by byphoare Hl.
  byphoare (Hl)

end

/-- EC's `lemma abs_val (P:real -> bool):
(forall &m (A <: Adv), P (Pr[A.main() @ &m : res] - 1%r/2%r)) =>
forall &m (A <: Adv), islossless A.main => P (`|Pr[A.main() @ &m : res] - 1%r/2%r|)`. -/
theorem abs_val (P : ℝ → Prop)
    (HP : ∀ (m : VariableAssignment) (A : Adv) [Module.Declared A ⊥],
      P (Pr[ A () @ &m : §res ] - 1 / 2))
    (m : VariableAssignment) (A : Adv) [Module.Declared A ⊥] (Hl : islossless A) :
    P (|Pr[ A () @ &m : §res ] - 1 / 2|) := by
  -- EC: move=> HP &m A Hl.
  -- EC: case (Pr[A.main() @ &m : res] <= 1%r / 2%r)=> Hle.
  by_cases Hle : Pr[ A () @ &m : §res ] ≤ 1 / 2
  -- EC: + by move: (HP &m (Neg_main(A))); rewrite (Neg_A_Pr_minus A &m) //#.
  · have h := @HP m (Module.app Neg_main A) ⟨by fp_finite, by fp_disjoint⟩
    rw [Neg_A_Pr_minus A m Hl] at h
    rw [abs_of_nonpos (by linarith)]; convert h using 1; ring
  -- EC: by move: (HP &m A)=> /#.
  · have h := HP m A
    rwa [abs_of_nonneg (by linarith)]

end GaudisCrypt.EC.AdvAbsVal
