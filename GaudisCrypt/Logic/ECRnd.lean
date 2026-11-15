import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Lib.EC.BitWordRing

/-!
# EC's `rnd f g`

    rnd f g.

on `c₁; x <$ d₁ ~ c₂; y <$ d₂ : P ==> Q` couples the two samplings along the bijection `f`
with inverse `g`, and leaves EC's three conditions in the postcondition of the code before:

    (forall rR, rR \in d₂ => rR = f (g rR)) /\
    (forall rR, rR \in d₂ => mu1 d₂ rR = mu1 d₁ (g rR)) /\
    (forall rL, rL \in d₁ => f rL \in d₂ /\ rL = g (f rL) /\ Q[x := rL, y := f rL])

`equiv_rnd f` (`Logic/PRHLWp.lean`) asks instead that `f` push `d₁` to `d₂`, an equation of
distributions that is found for a few shapes of `f` on the uniform distribution; with the
inverse, the conditions are EC's equations.
-/

namespace GaudisCrypt

open Classical in
/-- A bijection between the supports that keeps the point masses pushes `d₁` to `d₂` (EC's
conditions of `rnd f g`). -/
theorem SubProbability.bind_pure_eq_of_inv {α β : Type} (d₁ : SubProbability α)
    (d₂ : SubProbability β) (f : α → β) (g : β → α)
    (h1 : ∀ b ∈ d₂.support, b = f (g b))
    (h2 : ∀ b ∈ d₂.support, EC.mu1 d₂ b = EC.mu1 d₁ (g b))
    (h3 : ∀ a ∈ d₁.support, f a ∈ d₂.support ∧ a = g (f a)) :
    (d₁ >>= fun a => (pure (f a) : SubProbability β)) = d₂ := by
  refine EC.eq_distr fun b => ?_
  rw [EC.mu1_eq_expected, SubProbability.expected_bind]
  simp only [expected_pure]
  by_cases hb : b ∈ d₂.support
  · have e : d₁.expected (fun a => if f a = b then (1 : ENNReal) else 0) =
        d₁.expected (fun a => if a = g b then 1 else 0) :=
      SubProbability.expected_congr_satisfies (P := (· ∈ d₁.support))
        (fun a ha => SubProbability.mem_support_of_ne_zero ha) (fun a ha => by
          by_cases hfa : f a = b
          · have hab : a = g b := by rw [← hfa]; exact (h3 a ha).2
            rw [if_pos hfa, if_pos hab]
          · have hab : a ≠ g b := fun h => hfa (by rw [h]; exact (h1 b hb).symm)
            rw [if_neg hfa, if_neg hab])
    rw [e, ← EC.mu1_eq_expected]
    have h := h2 b hb
    unfold EC.mu1 at h
    exact ((ENNReal.toReal_eq_toReal_iff' (EC.mu_ne_top _ _) (EC.mu_ne_top _ _)).mp h).symm
  · have h0 : d₂.1 {b} = 0 := by
      by_contra h
      exact hb (SubProbability.mem_support_of_ne_zero h)
    rw [h0]
    exact SubProbability.expected_eq_zero_of_support fun a ha => by
      have hfa : f a ≠ b := fun h => hb (h ▸ (h3 a ha).1)
      rw [if_neg hfa]

/-- The uniform distribution gives all values the same probability: EC's condition
`mu1 d₂ rR = mu1 d₁ (g rR)` of `rnd f g` for two uniform samplings. -/
@[simp] theorem EC.mu1_uniform_eq {α : Type} [Fintype α] [Nonempty α] (x y : α) :
    (EC.mu1 (SubProbability.uniform : SubProbability α) x = EC.mu1 SubProbability.uniform y)
      = True :=
  eq_true (by unfold EC.mu1; rw [EC.uniform_funi x y])

/-- The same for `{0,1}`. -/
@[simp] theorem EC.mu1_dbool_eq (x y : Bool) : (EC.mu1 EC.dbool x = EC.mu1 EC.dbool y) = True :=
  EC.mu1_uniform_eq x y

/-- `{0,1}` charges both values (EC's `dbool_fu`), for the conditions of `rnd` on a coin. -/
@[simp] theorem EC.dbool_support : EC.dbool.support = Set.univ :=
  SubProbability.uniform_support

section Sample

variable {A B : ProgramState → ProgramState → Prop} {s₁ s₂ : Stmt}

/-- **EC's `rnd f g`**: the two samplings coupled along `f` with inverse `g`; EC's three
conditions (see the module docstring). -/
theorem prhlStmt_seq_sample_inv {α β : Type} {x₁ : Setter α ProgramState}
    {x₂ : Setter β ProgramState} {e₁ : Getter (SubProbability α) ProgramState}
    {e₂ : Getter (SubProbability β) ProgramState}
    (f : ProgramState → ProgramState → α → β) (g : ProgramState → ProgramState → β → α)
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ =>
      (∀ b ∈ (e₂.get σ₂).support, b = f σ₁ σ₂ (g σ₁ σ₂ b)) ∧
      (∀ b ∈ (e₂.get σ₂).support,
        EC.mu1 (e₂.get σ₂) b = EC.mu1 (e₁.get σ₁) (g σ₁ σ₂ b)) ∧
      ∀ a ∈ (e₁.get σ₁).support, f σ₁ σ₂ a ∈ (e₂.get σ₂).support ∧
        a = g σ₁ σ₂ (f σ₁ σ₂ a) ∧ B (x₁.set a σ₁) (x₂.set (f σ₁ σ₂ a) σ₂)) :
    prhlStmt A (.seq s₁ (.sample x₁ e₁)) (.seq s₂ (.sample x₂ e₂)) B :=
  prhlStmt_seq_sample f (prhlStmt_post h fun σ₁ σ₂ ⟨h1, h2, h3⟩ =>
    ⟨SubProbability.bind_pure_eq_of_inv _ _ _ _ h1 h2
        (fun a ha => ⟨(h3 a ha).1, (h3 a ha).2.1⟩),
      fun a ha => (h3 a ha).2.2⟩)

end Sample

open Lean Meta Elab Tactic PRHLWp TacticMisc in
/-- **EC's `rnd f g`**: the last statements of both sides are samplings `x₁ <$ d₁`, `x₂ <$ d₂`,
coupled along `f` with inverse `g` (`prhlStmt_seq_sample_inv`): the postcondition before them is
EC's three conditions.  `f`, `g` are relational terms (`§x{1}`, `§x{2}`). -/
elab "equiv_rnd" ppSpace f:term:max ppSpace g:term:max : tactic => withMainContext do
  let gl ← getMainGoal
  let _ ← prhlGoal gl "equiv_rnd"
  let gl ← HoareSplit.hoareSplit 1 gl
  gl.withContext do
    let ty ← prhlGoal gl "equiv_rnd"
    for i in [1, 2] do
      let st := stripLets (ty.getArg! i)
      unless st.isAppOf ``StmtWithHoles.seq &&
          (stripLets (st.getArg! 2)).isAppOf ``StmtWithHoles.sample do
        throwError "equiv_rnd: the last statement of side {i} is not a sampling (deterministic \
          code first: `stmt_wp`):{indentExpr (stripLets (st.getArg! 2))}"
    let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_sample_inv
    let (ms, _, concl) ← forallMetaTelescope (← inferType c)
    unless ← isDefEq concl ty do
      throwError "equiv_rnd: the last statements are not two samplings:{indentExpr ty}"
    for (m, t) in [(ms[ms.size - 3]!, f), (ms[ms.size - 2]!, g)] do
      let mTy ← instantiateMVars (← inferType m)
      let .forallE _ _ (.forallE _ _ T _) _ := mTy
        | throwError "equiv_rnd: unexpected coupling type{indentExpr mTy}"
      let e ← elabRelTerm ty t T
      unless ← isDefEq m e do
        throwError "equiv_rnd: the function{indentExpr e}\ndoes not have type{indentExpr mTy}"
    let hJ := ms.back!
    let g' ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (← inferType hJ)) (← gl.getTag)
    unless ← isDefEq hJ g' do throwError "equiv_rnd: cannot set the new judgment"
    gl.assign (← instantiateMVars (mkAppN c ms))
    -- the conditions as EC's `rnd` leaves them: for two uniform samplings the masses are equal
    -- and every value is in the support
    let g' ← Judgment.simpArg g'.mvarId! 3 (relSimpDecls ++ [``EC.mu1_uniform_eq,
      ``EC.mu1_dbool_eq, ``EC.dbool_support, ``SubProbability.uniform_support,
      ``EC.BitWord.mu1_dunifin_eq, ``EC.BitWord.dunifin_support, ``Set.mem_univ,
      ``forall_const, ``true_and, ``and_true, ``implies_true]) []
    replaceMainGoal [g']

end GaudisCrypt
