import GaudisCrypt.Logic.PHoareWp
import GaudisCrypt.Lib.EC.Mu

/-!
# EasyCrypt's `while I V` on a `phoare … = 1` judgment

    phoare_while I V        -- EC's `while I V`: the loop runs out with probability 1

On a goal `phoare[ … ==> E ] = 1 { s; while c body }` (EC proves a loop lossless, or that it ends
in `E`, with an invariant `I` and a variant `V`): the body, from `I`, the test and `V = k`, ends
in `I` with `V < k` with probability `1` (`body`, for every `k`); the code before the loop ends in
`I` with probability `1`.  The side conditions — `E` holds on leaving the loop from `I`
(`exit`), the expectation is at most `1` (`bound`) — are closed when `simp` can.

EC's `while (true) (size p - i)`: `I` is `True`, the variant `size p - i` (here a natural number,
`(size p - i).toNat`).
-/

namespace GaudisCrypt

/-- An expectation of a function at most `1` is at most `1`. -/
theorem SubProbability.expected_le_one {γ : Type _} (μ : SubProbability γ) {f : γ → ENNReal}
    (h : ∀ a, f a ≤ 1) : μ.expected f ≤ 1 := by
  refine (EC.mu_le h).trans ?_
  unfold SubProbability.expected
  rw [MeasureTheory.lintegral_one]
  exact μ.2.1

/-- `e ≤ 1` for an expectation built from indicators, products, conditionals and `expected` (what
the side condition `bound` of `phoare_while` is about). -/
macro "le_one" : tactic => `(tactic| repeat' (first
  | exact le_rfl
  | exact zero_le_one
  | exact indicatorE_le_one _
  | refine SubProbability.expected_le_one _ (fun _ => ?_)
  | refine mul_le_one' ?_ ?_
  | split_ifs))

/-- **A loop with a variant runs out**: from `I`, if every round from `I` and the test ends in
`I` with a smaller variant with probability `1`, the loop's expectation of `g` (at most `1`, and
`1` on leaving the loop from `I`) is `1`. -/
theorem Stmt.ewp_while_eq_one_of_phoare {c : Getter Bool ProgramState} {body : Stmt}
    (I : ProgramState → Prop) (V : ProgramState → ℕ) {g : ProgramState → ENNReal}
    (hbody : ∀ k σ, I σ → c.get σ = true → V σ = k →
      body.ewp (fun τ => indicatorE (I τ ∧ V τ < k)) σ = 1)
    (hexit : ∀ σ, I σ → c.get σ = false → g σ = 1) (hg : ∀ σ, g σ ≤ 1) (σ : ProgramState)
    (hI : I σ) : Stmt.ewp (StmtWithHoles.while c body) g σ = 1 := by
  have hW : ∀ τ, Stmt.ewp (StmtWithHoles.while c body) g τ ≤ 1 := fun τ =>
    (Stmt.ewp_mono _ hg τ).trans (Stmt.ewp_const_le _ 1 τ)
  induction hn : V σ using Nat.strong_induction_on generalizing σ with
  | _ n ih =>
  rw [Stmt.ewp_while_unfold]
  cases hc : c.get σ
  · simpa using hexit σ hI hc
  · simp only [if_true]
    refine le_antisymm ((Stmt.ewp_mono _ hW σ).trans (Stmt.ewp_const_le _ 1 σ)) ?_
    rw [← hbody n σ hI hc hn]
    refine Stmt.ewp_mono _ (fun τ => ?_) σ
    by_cases h : I τ ∧ V τ < n
    · rw [indicatorE_of h, ih (V τ) h.2 τ h.1 rfl]
    · rw [indicatorE_of_not h]; exact bot_le

/-- **EC's `while I V`** on a trailing loop, for `phoare[ … ] = 1`: the body (for every `k`, from
`I`, the test and `V = k`, to `I` and `V < k`), the code before the loop (to `I`), both with
probability `1`. -/
theorem phoareStmt_while_eq_one {A : ProgramState → Prop} {pre body : Stmt}
    {c : Getter Bool ProgramState} {g : ProgramState → ENNReal} (I : ProgramState → Prop)
    (V : ProgramState → ℕ)
    (hbody : ∀ k, phoareStmt (fun σ => I σ ∧ c.get σ = true ∧ V σ = k) body
      (fun τ => indicatorE (I τ ∧ V τ < k)) Eq (fun _ => 1))
    (hexit : ∀ σ, I σ → c.get σ = false → g σ = 1) (hg : ∀ σ, g σ ≤ 1)
    (hpre : phoareStmt A pre (fun σ => indicatorE (I σ)) Eq (fun _ => 1)) :
    phoareStmt A (.seq pre (.while c body)) g Eq (fun _ => 1) := by
  rw [phoareStmt_seq_iff]
  intro σ hA
  have hW : ∀ τ, Stmt.ewp (StmtWithHoles.while c body) g τ ≤ 1 := fun τ =>
    (Stmt.ewp_mono _ hg τ).trans (Stmt.ewp_const_le _ 1 τ)
  refine le_antisymm ((Stmt.ewp_mono _ hW σ).trans (Stmt.ewp_const_le _ 1 σ)) ?_
  rw [← hpre σ hA]
  refine Stmt.ewp_mono _ (fun τ => ?_) σ
  by_cases h : I τ
  · rw [indicatorE_of h, Stmt.ewp_while_eq_one_of_phoare I V
      (fun k σ hI hc hk => hbody k σ ⟨hI, hc, hk⟩) hexit hg τ h]
  · rw [indicatorE_of_not h]; exact bot_le

namespace PHoareWp

open Lean Meta Elab Tactic

/-- EC's `while I V` on `phoareStmt A {…; while c body} g = 1` (`phoareStmt_while_eq_one`): goals
`body`, then the code before the loop; `exit` and `bound` when `simp` does not close them. -/
def phoareWhileEqOneStep (I V : Lean.Expr) (g : MVarId) : TacticM (List MVarId) :=
    g.withContext do
  let g ← phoareSplit 1 g
  let rule ← mkConstWithFreshMVarLevels ``phoareStmt_while_eq_one
  let (ms, _, ty) ← forallMetaTelescope (← inferType rule)
  -- `{A pre body c g} (I) (V) (hbody) (hexit) (hg) (hpre)`
  unless ← isDefEq ms[5]! I do
    throwError "phoare_while: the invariant is not a condition on the program state"
  unless ← isDefEq ms[6]! V do
    throwError "phoare_while: the variant is not a natural number on the program state"
  unless ← isDefEq ty (← g.getType) do
    throwError "phoare_while: the goal is not `phoare[ … ] = 1` about a trailing loop:\
      {indentExpr (← g.getType)}"
  g.assign (mkAppN rule ms)
  let tagged (i : Nat) (tag : Name) : MetaM MVarId := do
    let m := ms[i]!.mvarId!
    m.setTag tag
    return m
  let gBody ← tagged 7 `body
  let gPre ← tagged 10 (← g.getTag)
  -- the side conditions, when `simp` closes them
  let mut side : List MVarId := []
  for (i, tag, tac) in [(8, `exit, ← `(tactic| (intros; simp_all; done))),
      (9, `bound, ← `(tactic| (intros; le_one; done)))] do
    let m ← tagged i tag
    let s ← saveState
    let rest ← try evalTacticAt tac m catch _ => do s.restore; pure [m]
    side := side ++ rest
  return [gBody, gPre] ++ side

end PHoareWp

open Lean Elab Tactic PHoareWp in
/-- **EC's `while I V`** on `phoare[ … ] = 1` (see the module docstring): `I` a condition, `V` a
natural number, written like the judgment's conditions. -/
elab "phoare_while " I:term:max ppSpace V:term:max : tactic => withMainContext do
  let Ie ← elabGoalFunction I (mkSort 0)
  let Ve ← elabGoalFunction V (mkConst ``Nat)
  let gs ← phoareWhileEqOneStep Ie Ve (← getMainGoal)
  replaceMainGoal gs

end GaudisCrypt
