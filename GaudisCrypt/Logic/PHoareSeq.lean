import GaudisCrypt.Logic.PHoareWp

/-!
# pHL's `seq` with five bounds (EasyCrypt's `seq n : E p₁ p₂ p₃ p₄ I`)

For an upper bound on `c₁; c₂`, EC's

    seq n : E p₁ p₂ p₃ p₄ I

splits at the `n`-th statement over the intermediate event `E`: `c₁` reaches `E` with probability
at most `p₁` and `¬E` with at most `p₃`; from `E` (and the invariant `I`, which `c₁` establishes)
`c₂` reaches the postcondition with at most `p₂`, from `¬E` with at most `p₄`; and
`p₁ p₂ + p₃ p₄ ≤ r`.

`phoareStmt_seq_le` is the rule; `phoare_seq n : E p₁ p₂ p₃ p₄ I` applies it, splitting after the
first `n` statements (EC's count), with `E` and `I` written like the judgment's conditions (`§x`).
The goals, in EC's order: `I` (a Hoare triple about `c₁`), `c₁`'s bounds for `E`, `c₂`'s from
`E ∧ I`, `c₁`'s for `¬E`, `c₂`'s from `¬E ∧ I`, the arithmetic.  A bound `1` on an event
(EC's `1%r`) is closed on the spot.
-/

namespace GaudisCrypt

/-- **pHL's `seq` with five bounds**, for an upper bound. -/
theorem phoareStmt_seq_le {A : ProgramState → Prop} {s₁ s₂ : Stmt} (E I : ProgramState → Prop)
    {Q : ProgramState → ENNReal} (p₁ p₂ p₃ p₄ : ENNReal) {r : ProgramState → ENNReal}
    (hI : hoareStmt A s₁ I)
    (h₁ : phoareStmt A s₁ (fun τ => indicatorE (E τ)) (@LE.le ENNReal _) (fun _ => p₁))
    (h₂ : phoareStmt (fun τ => E τ ∧ I τ) s₂ Q (@LE.le ENNReal _) (fun _ => p₂))
    (h₃ : phoareStmt A s₁ (fun τ => indicatorE (¬ E τ)) (@LE.le ENNReal _) (fun _ => p₃))
    (h₄ : phoareStmt (fun τ => ¬ E τ ∧ I τ) s₂ Q (@LE.le ENNReal _) (fun _ => p₄))
    (hr : ∀ σ, A σ → p₁ * p₂ + p₃ * p₄ ≤ r σ) :
    phoareStmt A (.seq s₁ s₂) Q (@LE.le ENNReal _) r := by
  classical
  intro σ hA
  rw [Stmt.ewp_seq]
  have hσ : hoareStmt (fun τ => τ = σ) s₁ I := hoare_pre hI fun τ hτ => hτ ▸ hA
  refine (Stmt.ewp_mono_of_hoare hσ
    (G := fun τ => p₂ * indicatorE (E τ) + p₄ * indicatorE (¬ E τ)) fun τ hIτ => ?_).trans ?_
  · by_cases hE : E τ
    · simpa [hE] using h₂ τ ⟨hE, hIτ⟩
    · simpa [hE] using h₄ τ ⟨hE, hIτ⟩
  · rw [Stmt.ewp_add, Stmt.ewp_const_mul, Stmt.ewp_const_mul]
    refine le_trans ?_ (hr σ hA)
    rw [mul_comm p₁, mul_comm p₃]
    exact add_le_add (mul_le_mul_left' (h₁ σ hA) _) (mul_le_mul_left' (h₃ σ hA) _)

/-- An event has probability at most `1` (EC's bound `1%r`). -/
theorem phoareStmt_indicator_le_one (A : ProgramState → Prop) (s : Stmt) (E : ProgramState → Prop) :
    phoareStmt A s (fun τ => indicatorE (E τ)) (@LE.le ENNReal _) (fun _ => 1) := by
  classical
  intro σ _
  refine (Stmt.ewp_mono s (G := fun _ => 1) (fun τ => ?_) σ).trans (Stmt.ewp_const_le s 1 σ)
  by_cases h : E τ <;> simp [h]

namespace PHoareSeq

open Lean Meta Elab Tactic

/-- Split `x₁; …; xₙ` after its first `m` statements (EC's count): `HoareSplit.splitSeq` with the
last `n - m` in the second block, under the `let`s of the local variables. -/
partial def splitLeading (m : Nat) (s₀ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let s ← TacticMisc.openStmt s₀
  if let .letE n ty val body _ := s then
    return ← withLetDecl n ty val fun fv => do
      let (r, p) ← splitLeading m (body.instantiate1 fv)
      return (← mkLetFVars #[fv] r (usedLetOnly := false),
              ← mkLetFVars #[fv] p (usedLetOnly := false))
  let n ← HoareSplit.seqLength s
  unless m ≤ n do throwError "phoare_seq: the statement has only {n} statements, not {m}"
  HoareSplit.splitSeq (n - m) s

end PHoareSeq

open Lean Meta Elab Tactic PHoareSeq PHoareWp in
/-- **EC's `seq n : E p₁ p₂ p₃ p₄ I`** for an upper bound (see the module docstring). -/
elab "phoare_seq " n:num " : " E:term:max p₁:term:max p₂:term:max p₃:term:max p₄:term:max
    I:term:max : tactic => do
  liftMetaTactic1 fun g => some <$> Judgment.onStmt (splitLeading n.getNat) g
  let Ee ← elabGoalFunction E (mkSort levelZero)
  let Ie ← elabGoalFunction I (mkSort levelZero)
  let ps ← withMainContext <| [p₁, p₂, p₃, p₄].mapM fun p => do
    -- EC's `_`: a bound left open, `1` (its goal, an event's probability, closed below)
    let p ← if p.raw.isOfKind ``Lean.Parser.Term.hole then `((1 : ENNReal)) else pure p
    let e ← Term.elabTermEnsuringType p (mkConst ``ENNReal)
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let ruleArgs := #[Ee, Ie] ++ ps.toArray
  let g ← getMainGoal
  let gs ← g.withContext do
    let c ← mkConstWithFreshMVarLevels ``phoareStmt_seq_le
    let (ms, _, ty) ← forallMetaTelescope (← inferType c)
    -- `{A s₁ s₂} (E I) {Q} (p₁ p₂ p₃ p₄) {r} (hI h₁ h₂ h₃ h₄ hr)`
    for (i, v) in [(3, ruleArgs[0]!), (4, ruleArgs[1]!), (6, ruleArgs[2]!), (7, ruleArgs[3]!),
        (8, ruleArgs[4]!), (9, ruleArgs[5]!)] do
      unless ← isDefEq ms[i]! v do throwError "phoare_seq: argument {i} does not fit"
    unless ← isDefEq ty (← g.getType) do
      throwError "phoare_seq: the goal is not an upper bound on a sequence{indentExpr (← g.getType)}"
    g.assign (mkAppN c ms)
    let names := #[`invariant, `first_E, `second_E, `first_notE, `second_notE, `bound]
    let mut out := []
    for k in [0:6] do
      let m := ms[11 + k]!.mvarId!
      m.setTag names[k]!
      let m ← m.withContext do
        m.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← m.getType)))
      -- a bound `1` on an event: closed here
      let closed ← try
          let ty ← instantiateMVars (← m.getType)
          if ty.isAppOfArity ``phoareStmt 5 then
            (·.isEmpty) <$> m.apply (← mkConstWithFreshMVarLevels ``phoareStmt_indicator_le_one)
          else pure false
        catch _ => pure false
      unless closed do out := out ++ [m]
    return out
  replaceMainGoal gs

end GaudisCrypt
