import GaudisCrypt.Logic.HoareWp
import GaudisCrypt.Logic.PHoare

/-!
# Backwards reasoning for probabilistic Hoare judgments

The tactics of `Logic/HoareWp.lean` and `Logic/Inline.lean`, for `phoareStmt`:

* `phoare_inline n` — inline call site `n` (the inliner of `hoare_inline`);
* `phoare_split k` — regroup the statement, the last `k` statements in a block of their own;
* `phoare_wp k` — replace the expectation by the exact expectation of the last `k` statements
  (`phoareStmt_seq_iff`).  Exact for every statement but a loop: an abstract call stays a
  symbolic `Procedure.ewp` term;
* `phoare_skip` — at `skip`, the inequality or equation itself, reads generalized.
-/

namespace GaudisCrypt

/-! ## Judgments about equivalent statements -/

theorem SubProbability.expected_mapState {α : Type v} {s t : Type u} (f : t → s)
    (μ : SubProbability (α × t)) (F : α × s → ENNReal) :
    (μ.mapState f).expected F = μ.expected fun p => F (p.1, f p.2) := by
  change (μ >>= fun p => pure (p.1, f p.2)).expected F = _
  rw [SubProbability.expected_bind]
  simp only [expected_pure]

/-- **A judgment about an equivalent statement**: along `s.EquivInLens s' l`, the judgment about
`s` is the one about `s'` with the conditions, the expectation and the bound read through `l`. -/
theorem phoareStmt_iff_of_equivInLens {A : ProgramState → Prop} {s s' : Stmt}
    {g : ProgramState → ENNReal} {ρ : ENNReal → ENNReal → Prop} {r : ProgramState → ENNReal}
    {l : Lens ProgramState ProgramState} (h : s.EquivInLens s' l) :
    phoareStmt A s g ρ r ↔
      phoareStmt (fun τ => A (l.get τ)) s' (fun τ => g (l.get τ)) ρ (fun τ => r (l.get τ)) := by
  have h' : ∀ τ, s.ewp g (l.get τ) = s'.ewp (fun τ => g (l.get τ)) τ := fun τ => by
    have := h ⟨⟩ (l.get τ) τ rfl
    rw [StmtWithHoles.instantiate_empty, StmtWithHoles.instantiate_empty] at this
    simp only [Stmt.ewp, ProgramDenotation.wp, ← this, SubProbability.expected_mapState]
  constructor
  · intro hs τ hA
    rw [← h' τ]
    exact hs _ hA
  · intro hs σ hA
    have hτ : l.get (l.set σ σ) = σ := l.set_get σ σ
    have := hs (l.set σ σ) (show A (l.get (l.set σ σ)) by rw [hτ]; exact hA)
    rw [← h'] at this
    simpa only [hτ] using this

/-- `phoareStmt_iff_of_equivInLens`, backwards, with the conditions given up to an equation:
what `phoare_inline` applies. -/
theorem phoareStmt_of_equivInLens {A A' : ProgramState → Prop} {s s' : Stmt}
    {g g' r r' : ProgramState → ENNReal} {ρ : ENNReal → ENNReal → Prop}
    {l : Lens ProgramState ProgramState} (h : s.EquivInLens s' l)
    (hA : (fun τ => A (l.get τ)) = A') (hg : (fun τ => g (l.get τ)) = g')
    (hr : (fun τ => r (l.get τ)) = r') (h' : phoareStmt A' s' g' ρ r') :
    phoareStmt A s g ρ r := by
  subst hA hg hr
  exact (phoareStmt_iff_of_equivInLens h).mpr h'

/-- A judgment about an equivalent statement, without renaming. -/
theorem phoareStmt_of_equiv {A : ProgramState → Prop} {s s' : Stmt}
    {g r : ProgramState → ENNReal} {ρ : ENNReal → ENNReal → Prop} (h : s.Equiv s')
    (h' : phoareStmt A s' g ρ r) : phoareStmt A s g ρ r :=
  (phoareStmt_iff_of_equivInLens h).mpr h'

/-- `Stmt.ewp_call`, at the spelling the statements carry. -/
theorem StmtWithHoles.ewp_call {sig} (x : Setter sig.ret ProgramState) (p : Procedure sig)
    (args : Getter sig.ParamType ProgramState) (g : ProgramState → ENNReal) :
    Stmt.ewp (StmtWithHoles.call x p args) g
      = fun σ => p.ewp (args.get σ) (fun v gl => g (x.set v (ProgramState.globalL.set gl σ)))
          σ.globals :=
  Stmt.ewp_call x p args g

namespace PHoareWp

open Lean Meta Elab Tactic TacticMisc

/-- Apply the right-to-left direction of the equivalence `lem`, its arguments by unification. -/
def applyIffMpr (lem : Name) (g : MVarId) : MetaM (List MVarId) := do
  let c ← mkConstWithFreshMVarLevels lem
  let (ms, _, ty) ← forallMetaTelescope (← inferType c)
  let some (a, b) := ty.iff? | throwError "applyIffMpr: `{lem}` is not an equivalence"
  -- not `MVarId.apply`: it would unfold the judgment (a `∀`) and guess the arity wrong
  unless ← isDefEq a (← g.getType) do
    throwError "applyIffMpr: `{lem}` does not apply to{indentExpr (← g.getType)}"
  let g' ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars b) (← g.getTag)
  g.assign (mkApp4 (mkConst ``Iff.mpr) a b (mkAppN c ms) g')
  return [g'.mvarId!]

/-- The parts of a goal `phoareStmt A s g ρ r`. -/
def phoareParts (ty : Lean.Expr) : MetaM (Array Lean.Expr) := do
  unless ty.isAppOfArity ``phoareStmt 5 do
    throwError "expected a goal `phoareStmt A s g ρ r`, got{indentExpr ty}"
  return ty.getAppArgs

/-- On a goal `phoareStmt A s g ρ r`: rewrite the statement with `f` (a statement and a proof of
`s.Equiv s'`), and continue with the judgment about the new statement (`hoareOnStmt`). -/
def phoareOnStmt (f : Lean.Expr → MetaM (Lean.Expr × Lean.Expr)) (g : MVarId) : MetaM MVarId :=
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let #[A, s, e, ρ, r] ← phoareParts ty | unreachable!
    let (s', p) ← f s
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``phoareStmt #[A, s', e, ρ, r])
      (← g.getTag)
    g.assign (← mkAppOptM ``phoareStmt_of_equiv
      #[some A, some s, some s', some e, some r, some ρ, some p, some g'])
    return g'.mvarId!

/-- `phoare_split k`: regroup the statement as `{x₁; …; xₙ₋ₖ}; {xₙ₋ₖ₊₁; …; xₙ}`. -/
def phoareSplit (k : Nat) (g : MVarId) : MetaM MVarId :=
  phoareOnStmt (HoareSplit.splitSeq k) g

elab "phoare_split " k:num : tactic =>
  liftMetaTactic1 fun g => some <$> phoareSplit k.getNat g

/-- On a goal `phoareStmt A s g ρ r`: inline call site `n` of `s` and continue with the judgment
about the result, its conditions read through the renaming and cleaned (`hoareInline`). -/
def phoareInline (n : Nat) (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let #[A, s, e, ρ, r] ← phoareParts ty | unreachable!
  let step ← Flatten.inlineProcedure n s (Flatten.namesIn r (Flatten.namesIn e
    (Flatten.namesIn A)))
  let (A', hA) ← Flatten.cleanCondition A step.trafo
  let (e', he) ← Flatten.cleanCondition e step.trafo
  let (r', hr) ← Flatten.cleanCondition r step.trafo
  let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``phoareStmt #[A', step.stmt, e', ρ, r'])
    (← g.getTag)
  g.assign (← mkAppOptM ``phoareStmt_of_equivInLens
    #[some A, some A', some s, some step.stmt, some e, some e', some r, some r', some ρ,
      some step.trafo, some step.proof, some hA, some he, some hr, some g'])
  return g'.mvarId!

elab "phoare_inline " n:num : tactic =>
  liftMetaTactic1 fun g => some <$> phoareInline n.getNat g

/-- The simp set computing an expectation: the exact expectations of the statements, the reads of
`simpReads`, and the uniform distribution's average. -/
def ewpDecls : List Name :=
  [``Stmt.ewp_seq, ``Stmt.ewp_skip, ``Stmt.ewp_assign, ``Stmt.ewp_sample,
   ``Stmt.ewp_ifThenElse, ``StmtWithHoles.ewp_call, ``Stmt.ewp_call,
   ``uniform_expected, ``Fintype.sum_bool, ``Fintype.card_bool, ``Nat.cast_ofNat,
   ``Bool.true_eq_false, ``Bool.false_eq_true, ``if_true, ``if_false,
   ``Bool.true_beq, ``Bool.false_beq, ``Bool.not_eq_true',
   -- events, and the arithmetic they leave
   ``indicatorE_true, ``indicatorE_false, ``ENNReal.zero_div, ``zero_add, ``add_zero, ``mul_one,
   ``one_mul, ``mul_zero, ``zero_mul] ++ HoareWp.simpReadsDecls

/-- One backwards step on a goal `phoareStmt A {x₁; …; xₙ} g ρ r`: split off the last `k`
statements (`phoareSplit`), and continue with the judgment about `x₁; …; xₙ₋ₖ`, the expectation
replaced by the exact expectation of the last `k` statements (`phoareStmt_seq_iff`), computed and
simplified (`ewpDecls`). -/
def phoareWpStep (k : Nat) (g : MVarId) : MetaM MVarId := do
  let g ← phoareSplit k g
  let gs ← applyIffMpr ``phoareStmt_seq_iff g
  let [g] := gs | throwError "phoare_wp: `phoareStmt_seq_iff` left {gs.length} goals"
  HoareWp.simpGoalArg ewpDecls g 2

elab "phoare_wp " k:num : tactic =>
  liftMetaTactic1 fun g => some <$> phoareWpStep k.getNat g

/-- The end of a backwards proof, on a goal `phoareStmt A skip g ρ r`: the relation itself,
`∀ σ, A σ → ρ (g σ) (r σ)` (`phoareStmt_skip_iff`), β-reduced, with the reads of the state
generalized to plain values (`generalizeReads`). -/
def phoareSkip (g : MVarId) : MetaM MVarId := do
  let gs ← applyIffMpr ``phoareStmt_skip_iff g
  let [g] := gs | throwError "phoare_skip: `phoareStmt_skip_iff` left {gs.length} goals"
  let g ← g.withContext do g.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars
    (← g.getType)))
  try generalizeReads g catch _ => pure g

elab "phoare_skip" : tactic =>
  liftMetaTactic1 fun g => some <$> phoareSkip g

end PHoareWp

end GaudisCrypt
