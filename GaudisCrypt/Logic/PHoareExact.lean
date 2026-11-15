import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.PHoareSeq
import GaudisCrypt.Logic.ECConseq

/-!
# pHL on exact bounds: `seq`, `case`, `conseq`

The rules EasyCrypt's scripts use on `phoare[ c : P ==> Q ] = r` when `r` is not `1`
(`PIR.ec`'s `Pr_PIR_s`, `vonNeumann.eca`):

* `seq n : E p₁ p₂ p₃ p₄ I` (`phoareStmt_seq_eq`): `c₁` reaches `E` with probability exactly
  `p₁` and `¬E` with `p₃`; from `E` (and the invariant `I`) `c₂` reaches the postcondition with
  exactly `p₂`, from `¬E` with `p₄`; and `p₁ p₂ + p₃ p₄ = r`.  A bound `_` leaves its goal out:
  EC allows it where the other bound of the branch is `0`.
* `case E` (`phoareStmt_case`).
* `conseq (: _ ==> _ : = e)`: another bound, equal under the precondition
  (`phoareStmt_conseq_bound`).
* `conseq (: P ==> _)`: a weaker precondition (`phoareStmt_conseq_pre`).
* `conseq (: _ ==> Q₁) (: _ ==> Q₂)`: the event `Q₁` in pHL and `Q₂` in Hoare logic, where
  under `Q₂` the two events `Q₁` and `Q` agree (`phoareStmt_conseq_hoare`).
* `conseq H` for a judgment `H` about the same statement (`phoareStmt_conseq_of`).

The tactics are in `Logic/PHoareExactTactics.lean`.
-/

namespace GaudisCrypt

/-- Under a Hoare triple of `s` from `σ`, expectations that agree on its postcondition have the
same expected value. -/
theorem Stmt.ewp_congr_of_hoare {s : Stmt} {B : ProgramState → Prop} {σ : ProgramState}
    (h : hoareStmt (fun τ => τ = σ) s B) {F G : ProgramState → ENNReal}
    (hFG : ∀ τ, B τ → F τ = G τ) : s.ewp F σ = s.ewp G σ :=
  le_antisymm (Stmt.ewp_mono_of_hoare h fun τ hτ => (hFG τ hτ).le)
    (Stmt.ewp_mono_of_hoare h fun τ hτ => (hFG τ hτ).ge)

/-- The expected value of `0` is `0`. -/
theorem Stmt.ewp_zero (s : Stmt) (σ : ProgramState) : s.ewp (fun _ => 0) σ = 0 :=
  le_antisymm (Stmt.ewp_const_le s 0 σ) bot_le

/-- The contribution of one branch of pHL's `seq`: the runs of `s₁` that end in `E`, then
`s₂` to `Q`, have probability `p * q`. -/
def PHoareSeqBranch (A : ProgramState → Prop) (s₁ s₂ : Stmt) (E : ProgramState → Prop)
    (Q : ProgramState → ENNReal) (p q : ENNReal) : Prop :=
  ∀ σ, A σ → s₁.ewp (fun τ => indicatorE (E τ) * s₂.ewp Q τ) σ = p * q

/-- **pHL's `seq` with five bounds**, for an exact bound, from its two branches. -/
theorem phoareStmt_seq_eq {A : ProgramState → Prop} {s₁ s₂ : Stmt} (E I : ProgramState → Prop)
    {Q : ProgramState → ENNReal} (p₁ p₂ p₃ p₄ : ℝ) {r : ProgramState → ENNReal}
    (h0 : 0 ≤ p₁ ∧ 0 ≤ p₂ ∧ 0 ≤ p₃ ∧ 0 ≤ p₄)
    (hI : hoareStmt A s₁ I)
    (hE : PHoareSeqBranch A s₁ s₂ (fun τ => E τ ∧ I τ) Q (ENNReal.ofReal p₁) (ENNReal.ofReal p₂))
    (hN : PHoareSeqBranch A s₁ s₂ (fun τ => ¬ E τ ∧ I τ) Q (ENNReal.ofReal p₃)
      (ENNReal.ofReal p₄))
    (hr : ∀ σ, A σ → r σ = ENNReal.ofReal (p₁ * p₂ + p₃ * p₄)) :
    phoareStmt A (.seq s₁ s₂) Q Eq r := by
  classical
  intro σ hA
  obtain ⟨h1, h2, h3, h4⟩ := h0
  rw [Stmt.ewp_seq, hr σ hA, ENNReal.ofReal_add (mul_nonneg h1 h2) (mul_nonneg h3 h4),
    ENNReal.ofReal_mul h1, ENNReal.ofReal_mul h3, ← hE σ hA, ← hN σ hA, ← Stmt.ewp_add]
  have hσ : hoareStmt (fun τ => τ = σ) s₁ I := hoare_pre hI fun τ hτ => hτ ▸ hA
  refine Stmt.ewp_congr_of_hoare hσ fun τ hIτ => ?_
  by_cases hEτ : E τ
  · rw [indicatorE_of ⟨hEτ, hIτ⟩, indicatorE_of_not (fun h => h.1 hEτ)]; simp
  · rw [indicatorE_of_not (fun h => hEτ h.1), indicatorE_of ⟨hEτ, hIτ⟩]; simp

/-- A branch of `seq` from its two judgments. -/
theorem PHoareSeqBranch.both {A : ProgramState → Prop} {s₁ s₂ : Stmt}
    {E I : ProgramState → Prop} {Q : ProgramState → ENNReal} {p q : ENNReal}
    (hI : hoareStmt A s₁ I)
    (h₁ : phoareStmt A s₁ (fun τ => indicatorE (E τ)) Eq (fun _ => p))
    (h₂ : phoareStmt (fun τ => E τ ∧ I τ) s₂ Q Eq (fun _ => q)) :
    PHoareSeqBranch A s₁ s₂ (fun τ => E τ ∧ I τ) Q p q := by
  classical
  intro σ hA
  have hσ : hoareStmt (fun τ => τ = σ) s₁ I := hoare_pre hI fun τ hτ => hτ ▸ hA
  have e₁ : s₁.ewp (fun τ => indicatorE (E τ)) σ = p := h₁ σ hA
  rw [mul_comm p q, ← e₁, ← Stmt.ewp_const_mul]
  refine Stmt.ewp_congr_of_hoare hσ fun τ hIτ => ?_
  by_cases hEτ : E τ
  · rw [indicatorE_of ⟨hEτ, hIτ⟩, indicatorE_of hEτ, h₂ τ ⟨hEτ, hIτ⟩, one_mul, mul_one]
  · rw [indicatorE_of_not (fun h => hEτ h.1), indicatorE_of_not hEτ, zero_mul, mul_zero]

/-- A branch of `seq` whose second bound is `0`: the first is not needed (EC's `_`). -/
theorem PHoareSeqBranch.second_zero {A : ProgramState → Prop} {s₁ s₂ : Stmt}
    {E : ProgramState → Prop} {Q : ProgramState → ENNReal} (p : ENNReal)
    (h₂ : phoareStmt E s₂ Q Eq (fun _ => 0)) :
    PHoareSeqBranch A s₁ s₂ E Q p (ENNReal.ofReal 0) := by
  classical
  intro σ _
  have : (fun τ => indicatorE (E τ) * s₂.ewp Q τ) = fun _ => 0 := by
    funext τ
    by_cases hEτ : E τ
    · rw [h₂ τ hEτ, mul_zero]
    · rw [indicatorE_of_not hEτ, zero_mul]
  rw [this, Stmt.ewp_zero, ENNReal.ofReal_zero, mul_zero]

/-- A branch of `seq` whose first bound is `0`, for a postcondition at most `1` (an event): the
second is not needed (EC's `_`). -/
theorem PHoareSeqBranch.first_zero {A : ProgramState → Prop} {s₁ s₂ : Stmt}
    {E I : ProgramState → Prop} {Q : ProgramState → ENNReal} (q : ENNReal)
    (hQ : ∀ τ, Q τ ≤ 1)
    (h₁ : phoareStmt A s₁ (fun τ => indicatorE (E τ)) Eq (fun _ => 0)) :
    PHoareSeqBranch A s₁ s₂ (fun τ => E τ ∧ I τ) Q (ENNReal.ofReal 0) q := by
  classical
  intro σ hA
  rw [ENNReal.ofReal_zero, zero_mul]
  refine le_antisymm ?_ bot_le
  have e₁ : s₁.ewp (fun τ => indicatorE (E τ)) σ = 0 := h₁ σ hA
  rw [← e₁]
  refine Stmt.ewp_mono s₁ (fun τ => ?_) σ
  by_cases hEτ : E τ
  · rw [indicatorE_of hEτ]
    exact (mul_le_of_le_one_left bot_le (indicatorE_le_one _)).trans
      ((Stmt.ewp_mono s₂ hQ τ).trans (Stmt.ewp_const_le s₂ 1 τ))
  · rw [indicatorE_of_not (fun h => hEτ h.1), zero_mul]; exact bot_le

/-- **pHL's `case E`**. -/
theorem phoareStmt_case {A : ProgramState → Prop} {s : Stmt} {Q : ProgramState → ENNReal}
    {ρ : ENNReal → ENNReal → Prop} {r : ProgramState → ENNReal} (E : ProgramState → Prop)
    (h₁ : phoareStmt (fun σ => A σ ∧ E σ) s Q ρ r)
    (h₂ : phoareStmt (fun σ => A σ ∧ ¬ E σ) s Q ρ r) : phoareStmt A s Q ρ r := by
  classical
  intro σ hA
  by_cases hE : E σ
  · exact h₁ σ ⟨hA, hE⟩
  · exact h₂ σ ⟨hA, hE⟩

/-- **pHL's `conseq (: _ ==> _ : = e)`**: another bound, equal to the judgment's under the
precondition. -/
theorem phoareStmt_conseq_bound {A : ProgramState → Prop} {s : Stmt}
    {Q : ProgramState → ENNReal} {ρ : ENNReal → ENNReal → Prop} {r : ProgramState → ENNReal}
    (r' : ProgramState → ENNReal) (hr : ∀ σ, A σ → r σ = r' σ)
    (h : phoareStmt A s Q ρ r') : phoareStmt A s Q ρ r :=
  fun σ hA => hr σ hA ▸ h σ hA

/-- **pHL's `conseq (: P ==> _)`**: a weaker precondition. -/
theorem phoareStmt_conseq_pre {A : ProgramState → Prop} {s : Stmt}
    {Q : ProgramState → ENNReal} {ρ : ENNReal → ENNReal → Prop} {r : ProgramState → ENNReal}
    (A' : ProgramState → Prop) (hA : ∀ σ, A σ → A' σ)
    (h : phoareStmt A' s Q ρ r) : phoareStmt A s Q ρ r :=
  fun σ hσ => h σ (hA σ hσ)

/-- **pHL's `conseq (: _ ==> Q₁) (: _ ==> Q₂)`** on an exact bound: the event `Q₁` with the
bound, and `Q₂` in Hoare logic, under which `Q₁` and the judgment's event agree. -/
theorem phoareStmt_conseq_hoare {A : ProgramState → Prop} {s : Stmt}
    {Q : ProgramState → Prop} {r : ProgramState → ENNReal} (Q₁ Q₂ : ProgramState → Prop)
    (hpost : ∀ τ, Q₂ τ → (Q₁ τ ↔ Q τ))
    (hh : hoareStmt A s Q₂)
    (hp : phoareStmt A s (fun τ => indicatorE (Q₁ τ)) Eq r) :
    phoareStmt A s (fun τ => indicatorE (Q τ)) Eq r := by
  intro σ hA
  rw [← hp σ hA]
  have hσ : hoareStmt (fun τ => τ = σ) s Q₂ := hoare_pre hh fun τ hτ => hτ ▸ hA
  exact Stmt.ewp_congr_of_hoare hσ fun τ h2 => by rw [propext (hpost τ h2)]

/-- **pHL's `conseq H`**: from a judgment `H` about the same statement and postcondition, with
a weaker precondition and a bound equal under the goal's precondition. -/
theorem phoareStmt_conseq_of {A A' : ProgramState → Prop} {s : Stmt}
    {Q : ProgramState → ENNReal} {ρ : ENNReal → ENNReal → Prop} {r r' : ProgramState → ENNReal}
    (H : phoareStmt A' s Q ρ r') (hA : ∀ σ, A σ → A' σ) (hr : ∀ σ, A σ → r σ = r' σ) :
    phoareStmt A s Q ρ r :=
  fun σ hσ => hr σ hσ ▸ H σ (hA σ hσ)

end GaudisCrypt
