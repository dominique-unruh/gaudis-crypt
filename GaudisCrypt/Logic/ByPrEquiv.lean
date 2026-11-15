import GaudisCrypt.Logic.ByPr
import GaudisCrypt.Logic.PRHL2
import GaudisCrypt.Logic.PRHLStmt

/-!
# EasyCrypt's `bypr`, on `equiv` judgments

EC's `bypr (res{1}) (res{2})` proves that two procedures return the same result,

    equiv[ p₁ ~ p₂ : P ==> ={res} ]

from the equality of the probabilities of each result,

    ∀ a₁ &1 a₂ &2 v, P → Pr[ p₁ (a₁) @ &1 : res = v ] = Pr[ p₂ (a₂) @ &2 : res = v ]

(`prhlProc_res_of_Pr_eq`).  The coupling is not built by hand: two programs whose results have
the same distribution are related by the wp-lifting for the relation "the same result"
(`ProgramDenotation.rel_fst_of_wp_eq`), and the wp-lifting gives a coupling (discrete Strassen:
`ProgramDenotation.relE.to_prhl2`).
-/

namespace GaudisCrypt

universe u v

open Classical in
/-- The expected value of a function of the result: the sum, over the results, of its value
times the probability of the result. -/
theorem SubProbability.expected_fst_eq_tsum {α : Type v} {S : Type (max u v)}
    (μ : SubProbability (α × S)) (k : α → ENNReal) :
    μ.expected (fun x => k x.1) = ∑' a, k a * μ.expected (fun x => indicatorE (x.1 = a)) := by
  have hE : ∀ a, μ.expected (fun x => indicatorE (x.1 = a)) = ∑' s, μ.1 {(a, s)} := by
    intro a
    rw [SubProbability.expected_eq_tsum, ENNReal.tsum_prod', tsum_eq_single a]
    · exact tsum_congr fun s => by rw [indicatorE_of rfl, one_mul]
    · intro a' ha'
      simp [indicatorE_of_not ha']
  rw [SubProbability.expected_eq_tsum, ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  rw [hE]; exact ENNReal.tsum_mul_left (a := k a) (f := fun s => μ.1 {(a, s)})

/-- Programs whose results have the same distribution are related, in the wp-lifting, by "the
same result". -/
theorem ProgramDenotation.rel_fst_of_wp_eq {s₁ s₂ : Type (max u v)} {α : Type v}
    {A : s₁ → s₂ → Prop} {c : ProgramDenotation s₁ α} {d : ProgramDenotation s₂ α}
    (h : ∀ σ₁ σ₂, A σ₁ σ₂ → ∀ a, (c σ₁).expected (fun x => indicatorE (x.1 = a)) =
      (d σ₂).expected (fun y => indicatorE (y.1 = a))) :
    c.rel d A (fun x y => x.1 = y.1) := by
  intro F G hFG σ₁ σ₂ hA
  -- the best bound on `G` that depends on the result only
  let k : α → ENNReal := fun a => ⨅ y : {y : α × s₂ // y.1 = a}, G y.1
  have h1 : ∀ x, F x ≤ k x.1 := fun x => le_iInf fun y => hFG x y.1 y.2.symm
  have h2 : ∀ y, k y.1 ≤ G y := fun y => iInf_le_of_le ⟨y, rfl⟩ le_rfl
  calc c.wp F σ₁ ≤ c.wp (fun x => k x.1) σ₁ := ProgramDenotation.wp_le_wp_of_le _ _ _ h1 σ₁
    _ = d.wp (fun y => k y.1) σ₂ := by
        change (c σ₁).expected (fun x => k x.1) = (d σ₂).expected (fun y => k y.1)
        rw [SubProbability.expected_fst_eq_tsum, SubProbability.expected_fst_eq_tsum]
        exact tsum_congr fun a => by rw [h σ₁ σ₂ hA a]
    _ ≤ d.wp G σ₂ := ProgramDenotation.wp_le_wp_of_le _ _ _ h2 σ₂

/-- Programs whose results have the same distribution can be coupled on "the same result". -/
theorem ProgramDenotation.prhl2_fst_of_wp_eq {s₁ s₂ : Type (max u v)} {α : Type v}
    {A : s₁ → s₂ → Prop} {c : ProgramDenotation s₁ α} {d : ProgramDenotation s₂ α}
    (h : ∀ σ₁ σ₂, A σ₁ σ₂ → ∀ a, (c σ₁).expected (fun x => indicatorE (x.1 = a)) =
      (d σ₂).expected (fun y => indicatorE (y.1 = a))) :
    ProgramDenotation.prhl2 A c d (fun x y => x.1 = y.1) := by
  refine ProgramDenotation.relE.to_prhl2 ⟨ProgramDenotation.rel_fst_of_wp_eq h, ?_⟩
  have := ProgramDenotation.rel_fst_of_wp_eq (A := fun σ₂ σ₁ => A σ₁ σ₂) (c := d) (d := c)
    fun σ₂ σ₁ hA a => (h σ₁ σ₂ hA a).symm
  exact fun F G hFG => this F G fun y x hxy => hFG y x hxy.symm

/-- **EC's `bypr (res{1}) (res{2})`**: two procedures with the same result type return the same
result (under a coupling) when each result has the same probability on the two sides. -/
theorem prhlProc_res_of_Pr_eq {ps₁ ps₂ : List Type} {α : Type}
    {A : (ProcedureSignature.mk ps₁ α).ParamType → VariableAssignment →
      (ProcedureSignature.mk ps₂ α).ParamType → VariableAssignment → Prop}
    {p₁ : Procedure ⟨ps₁, α⟩} {p₂ : Procedure ⟨ps₂, α⟩}
    (h : ∀ a₁ σ₁ a₂ σ₂ (v : α), A a₁ σ₁ a₂ σ₂ →
      (p₁.Pr a₁ σ₁ (fun r _ => r = v) : ℝ) = p₂.Pr a₂ σ₂ (fun r _ => r = v)) :
    prhlProc A p₁ p₂ (fun r₁ _ r₂ _ => r₁ = r₂) := by
  intro a₁ a₂
  refine ProgramDenotation.prhl2_fst_of_wp_eq fun σ₁ σ₂ hA v => ?_
  have e := congrArg (fun x : NNReal => (x : ENNReal)) (NNReal.coe_injective (h a₁ σ₁ a₂ σ₂ v hA))
  simp only [Procedure.Pr_eq_ewp] at e
  exact e

open Lean Elab Tactic in
/-- **EC's `bypr (res{1}) (res{2})`** on `equiv[ p₁ ~ p₂ : P ==> ={res} ]`: the goal becomes
`∀ a₁ &1 a₂ &2 v, P → Pr[ p₁ (a₁) @ &1 : res = v ] = Pr[ p₂ (a₂) @ &2 : res = v ]` (EC's goal
after `bypr … => &1 &2 v`: the arguments, the memories and the value are introduced by
`intro`). -/
elab "bypr" " (" &"res" Judgment.judgmentSide ")" " (" &"res" Judgment.judgmentSide ")" : tactic =>
    withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOf ``prhlProc do
    throwError "bypr: not a judgment `equiv[ p₁ ~ p₂ : P ==> Q ]` about two procedures"
  try evalTactic (← `(tactic| refine prhlProc_res_of_Pr_eq ?_))
  catch _ => throwError "bypr: the postcondition is not `=\{res}` (two procedures with one \
    result type){indentExpr ty}"

end GaudisCrypt
