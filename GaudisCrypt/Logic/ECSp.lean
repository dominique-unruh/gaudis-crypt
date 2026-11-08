import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.PHoareWp

/-!
# EasyCrypt's `sp`: deterministic code at the start, into the precondition

    stmt_sp          -- EC's `sp`: on every side, as long as the first statement is deterministic
    stmt_sp{i}       -- EC's `sp` on side `i` of a relational judgment
    stmt_sp n        -- EC's `sp n` (`stmt_sp{i} n`): `n` statements (on each side)

EC's `sp` moves the precondition forward over the assignments at the start of the code: `P`
becomes `exists x₀, P[x₀/x] /\ x = e[x₀/x]`.  Here, for a deterministic statement `d` running as
the update `upd` (`Stmt.Det d upd`, assignments and the resets inlining leaves among them), the
precondition `A` becomes `fun σ => ∃ τ, A τ ∧ σ = upd τ` (`hoareStmt_sp`, `phoareStmt_sp`,
`prhlStmt_sp_left`/`_right`).  A `phoare` bound is a function of the state: `sp` needs it unchanged
by `upd` (a constant bound, as EC's usually are; left as a goal otherwise).
-/

namespace GaudisCrypt

variable {d s s₁ s₂ : Stmt} {upd : ProgramState → ProgramState}

/-- A deterministic statement, then `s`: `s` from the updated state. -/
theorem programDenotation_seq_det (hd : Stmt.Det d upd) (s : Stmt) (σ : ProgramState) :
    programDenotation (.seq d s) σ = programDenotation s (upd σ) := by
  rw [programDenotation_seq, ProgramDenotation.bind_apply, hd.denotation, SubProbability.pure_bind]

/-- **EC's `sp`** on a Hoare triple: the first statement, deterministic, into the precondition. -/
theorem hoareStmt_sp {A B : ProgramState → Prop} (hd : Stmt.Det d upd)
    (h : hoareStmt (fun σ => ∃ τ, A τ ∧ σ = upd τ) s B) : hoareStmt A (.seq d s) B := by
  intro σ hA
  rw [programDenotation_seq_det hd]
  exact h (upd σ) ⟨σ, hA, rfl⟩

/-- **EC's `sp`** on a `phoare` judgment, its bound unchanged by the update. -/
theorem phoareStmt_sp {A : ProgramState → Prop} {g : ProgramState → ENNReal}
    {ρ : ENNReal → ENNReal → Prop} {r : ProgramState → ENNReal} (hd : Stmt.Det d upd)
    (hr : ∀ τ, A τ → r (upd τ) = r τ)
    (h : phoareStmt (fun σ => ∃ τ, A τ ∧ σ = upd τ) s g ρ r) : phoareStmt A (.seq d s) g ρ r := by
  intro σ hA
  have e : Stmt.ewp (StmtWithHoles.seq d s) g σ = s.ewp g (upd σ) := by
    simp only [Stmt.ewp, ProgramDenotation.wp]
    rw [programDenotation_seq_det hd]
  rw [e, ← hr σ hA]
  exact h (upd σ) ⟨σ, hA, rfl⟩

/-- **EC's `sp{1}`**: the left side's first statement, deterministic, into the precondition. -/
theorem prhlStmt_sp_left {A B : ProgramState → ProgramState → Prop} (hd : Stmt.Det d upd)
    (h : prhlStmt (fun σ₁ σ₂ => ∃ τ, A τ σ₂ ∧ σ₁ = upd τ) s₁ s₂ B) :
    prhlStmt A (.seq d s₁) s₂ B := by
  intro σ₁ σ₂ hA
  rw [programDenotation_seq_det hd]
  exact h (upd σ₁) σ₂ ⟨σ₁, hA, rfl⟩

/-- **EC's `sp{2}`**: the mirror of `prhlStmt_sp_left`. -/
theorem prhlStmt_sp_right {A B : ProgramState → ProgramState → Prop} (hd : Stmt.Det d upd)
    (h : prhlStmt (fun σ₁ σ₂ => ∃ τ, A σ₁ τ ∧ σ₂ = upd τ) s₁ s₂ B) :
    prhlStmt A s₁ (.seq d s₂) B := by
  intro σ₁ σ₂ hA
  rw [programDenotation_seq_det hd]
  exact h σ₁ (upd σ₂) ⟨σ₂, hA, rfl⟩

/-- `hoareStmt_sp`, the precondition kept on the new state when the update cannot change it (an
assignment to a variable it does not read): EC's `P /\ x = e` where `P` does not mention `x`. -/
theorem hoareStmt_sp_keep {A B : ProgramState → Prop} (hd : Stmt.Det d upd)
    (hA : ∀ τ, A τ → A (upd τ))
    (h : hoareStmt (fun σ => A σ ∧ ∃ τ, A τ ∧ σ = upd τ) s B) : hoareStmt A (.seq d s) B :=
  hoareStmt_sp hd (hoare_pre h fun _ ⟨τ, hτ, e⟩ => ⟨e ▸ hA τ hτ, τ, hτ, e⟩)

/-- `phoareStmt_sp`, the precondition kept on the new state (as `hoareStmt_sp_keep`). -/
theorem phoareStmt_sp_keep {A : ProgramState → Prop} {g : ProgramState → ENNReal}
    {ρ : ENNReal → ENNReal → Prop} {r : ProgramState → ENNReal} (hd : Stmt.Det d upd)
    (hr : ∀ τ, A τ → r (upd τ) = r τ) (hA : ∀ τ, A τ → A (upd τ))
    (h : phoareStmt (fun σ => A σ ∧ ∃ τ, A τ ∧ σ = upd τ) s g ρ r) :
    phoareStmt A (.seq d s) g ρ r :=
  phoareStmt_sp hd hr (phoareStmt_pre h fun _ ⟨τ, hτ, e⟩ => ⟨e ▸ hA τ hτ, τ, hτ, e⟩)

/-- `prhlStmt_sp_left`, the precondition kept on the new state (as `hoareStmt_sp_keep`). -/
theorem prhlStmt_sp_left_keep {A B : ProgramState → ProgramState → Prop} (hd : Stmt.Det d upd)
    (hA : ∀ τ σ₂, A τ σ₂ → A (upd τ) σ₂)
    (h : prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ ∃ τ, A τ σ₂ ∧ σ₁ = upd τ) s₁ s₂ B) :
    prhlStmt A (.seq d s₁) s₂ B :=
  prhlStmt_sp_left hd (prhlStmt_conseq h (fun _ σ₂ ⟨τ, hτ, e⟩ => ⟨e ▸ hA τ σ₂ hτ, τ, hτ, e⟩)
    fun _ _ h => h)

/-- `prhlStmt_sp_right`, the precondition kept on the new state. -/
theorem prhlStmt_sp_right_keep {A B : ProgramState → ProgramState → Prop} (hd : Stmt.Det d upd)
    (hA : ∀ σ₁ τ, A σ₁ τ → A σ₁ (upd τ))
    (h : prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ ∃ τ, A σ₁ τ ∧ σ₂ = upd τ) s₁ s₂ B) :
    prhlStmt A s₁ (.seq d s₂) B :=
  prhlStmt_sp_right hd (prhlStmt_conseq h (fun σ₁ _ ⟨τ, hτ, e⟩ => ⟨e ▸ hA σ₁ τ hτ, τ, hτ, e⟩)
    fun _ _ h => h)

/-! ### EC's `P /\ x = e`: an assignment as a read

For an assignment `x <- e` (the update `upd τ = x.set (e τ) τ`) that changes neither `P` nor `e`,
the precondition after it is `P ∧ x = e`, a fact about reads (EC's), rather than the equation of
states `σ = upd τ`: reads go through the later steps (the inliner's renamings among them). -/

/-- `hoareStmt_sp` for an assignment: `A ∧ x = e`. -/
theorem hoareStmt_sp_read {α : Type} {A B : ProgramState → Prop} (X : Lens α ProgramState)
    (E : ProgramState → α) (hd : Stmt.Det d upd) (hupd : ∀ τ, upd τ = X.set (E τ) τ)
    (hA : ∀ τ, A τ → A (upd τ)) (hE : ∀ τ, E (upd τ) = E τ)
    (h : hoareStmt (fun σ => A σ ∧ X.get σ = E σ) s B) : hoareStmt A (.seq d s) B :=
  hoareStmt_sp hd (hoare_pre h fun _ ⟨τ, hτ, e⟩ => by
    subst e; exact ⟨hA τ hτ, by rw [hE, hupd, X.set_get]⟩)

/-- `phoareStmt_sp` for an assignment: `A ∧ x = e`. -/
theorem phoareStmt_sp_read {α : Type} {A : ProgramState → Prop} {g : ProgramState → ENNReal}
    {ρ : ENNReal → ENNReal → Prop} {r : ProgramState → ENNReal} (X : Lens α ProgramState)
    (E : ProgramState → α) (hd : Stmt.Det d upd) (hupd : ∀ τ, upd τ = X.set (E τ) τ)
    (hr : ∀ τ, A τ → r (upd τ) = r τ) (hA : ∀ τ, A τ → A (upd τ)) (hE : ∀ τ, E (upd τ) = E τ)
    (h : phoareStmt (fun σ => A σ ∧ X.get σ = E σ) s g ρ r) : phoareStmt A (.seq d s) g ρ r :=
  phoareStmt_sp hd hr (phoareStmt_pre h fun _ ⟨τ, hτ, e⟩ => by
    subst e; exact ⟨hA τ hτ, by rw [hE, hupd, X.set_get]⟩)

/-- `prhlStmt_sp_left` for an assignment: `A ∧ x{1} = e{1}`. -/
theorem prhlStmt_sp_left_read {α : Type} {A B : ProgramState → ProgramState → Prop}
    (X : Lens α ProgramState) (E : ProgramState → α) (hd : Stmt.Det d upd)
    (hupd : ∀ τ, upd τ = X.set (E τ) τ) (hA : ∀ τ σ₂, A τ σ₂ → A (upd τ) σ₂)
    (hE : ∀ τ, E (upd τ) = E τ)
    (h : prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ X.get σ₁ = E σ₁) s₁ s₂ B) :
    prhlStmt A (.seq d s₁) s₂ B :=
  prhlStmt_sp_left hd (prhlStmt_conseq h (fun _ σ₂ ⟨τ, hτ, e⟩ => by
    subst e; exact ⟨hA τ σ₂ hτ, by rw [hE, hupd, X.set_get]⟩) fun _ _ h => h)

/-- `prhlStmt_sp_right` for an assignment: `A ∧ x{2} = e{2}`. -/
theorem prhlStmt_sp_right_read {α : Type} {A B : ProgramState → ProgramState → Prop}
    (X : Lens α ProgramState) (E : ProgramState → α) (hd : Stmt.Det d upd)
    (hupd : ∀ τ, upd τ = X.set (E τ) τ) (hA : ∀ σ₁ τ, A σ₁ τ → A σ₁ (upd τ))
    (hE : ∀ τ, E (upd τ) = E τ)
    (h : prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ X.get σ₂ = E σ₂) s₁ s₂ B) :
    prhlStmt A s₁ (.seq d s₂) B :=
  prhlStmt_sp_right hd (prhlStmt_conseq h (fun σ₁ _ ⟨τ, hτ, e⟩ => by
    subst e; exact ⟨hA σ₁ τ hτ, by rw [hE, hupd, X.set_get]⟩) fun _ _ h => h)

namespace ECSp

open Lean Meta Elab Tactic PRHLWp

/-- The lens an assignment's setter writes through (`Lens.toSetter X`, `liftLens X`), if any. -/
def lensOfSetter? (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let x ← instantiateMVars x
  if x.isAppOfArity ``Lens.toSetter 3 then return some x.appArg!
  if x.isAppOfArity `GaudisCrypt.liftLens 4 then
    let X := x.appArg!
    let .app (.app (.const ``Lens _) _) M ← whnfR (← inferType X) | return none
    if ← isDefEq M (mkConst ``ProgramState) then return some X
    if ← isDefEq M (mkConst ``VariableAssignment) then
      return some (← mkAppM ``Lens.intoGlobal #[X])
  return none

/-- The statement of side `side?` of the goal (the only one of a Hoare or `phoare` judgment). -/
def stmtOf (g : MVarId) (side? : Option Nat) : MetaM Lean.Expr := do
  let (d, ty) ← Judgment.descOf g side?
  return ty.getArg! d.stmtArg

/-- One step of `sp` on side `side?`: the first statement, if deterministic, into the
precondition; `none` if it is not. -/
def spOne (g : MVarId) (side? : Option Nat) : MetaM (Option (List MVarId)) := g.withContext do
  let st ← TacticMisc.openStmt (← stmtOf g side?)
  -- a single statement: `s; skip`, for the rule
  let first := if st.isAppOfArity ``StmtWithHoles.seq 3 then st.getArg! 1 else st
  let some (_, hd) ← detOf? first | return none
  let g ← if st.isAppOfArity ``StmtWithHoles.seq 3 then pure g
    else HoareSplit.hoareSplit 0 g side?
  let ty ← instantiateMVars (← g.getType)
  let (lem, keep) ← if ty.isAppOf ``hoareStmt then pure (``hoareStmt_sp, ``hoareStmt_sp_keep)
    else if ty.isAppOf ``phoareStmt then pure (``phoareStmt_sp, ``phoareStmt_sp_keep)
    else if ty.isAppOf ``prhlStmt then
      pure (if side? == some 2 then (``prhlStmt_sp_right, ``prhlStmt_sp_right_keep)
        else (``prhlStmt_sp_left, ``prhlStmt_sp_left_keep))
    else throwError "sp: not a statement judgment:{indentExpr ty}"
  -- EC's `P /\ x = e` for an assignment `x <- e` that changes neither `P` nor `e`
  let read? ← do
    let f := stripLets first
    if !f.isAppOf ``StmtWithHoles.assign then pure none else
    let some X ← lensOfSetter? (f.getArg! (f.getAppNumArgs - 2)) | pure none
    let E ← mkAppM ``Getter.get #[f.appArg!]
    let rlem := if ty.isAppOf ``hoareStmt then ``hoareStmt_sp_read
      else if ty.isAppOf ``phoareStmt then ``phoareStmt_sp_read
      else if side? == some 2 then ``prhlStmt_sp_right_read else ``prhlStmt_sp_left_read
    let s ← saveState
    try
      let gs ← applyLemma rlem g #[(`hd, hd), (`X, X), (`E, E)]
      let mut rest := #[]
      for h in gs do
        let tag ← h.getTag
        let t ← instantiateMVars (← h.getType)
        if t.isAppOf ``prhlStmt || t.isAppOf ``hoareStmt || t.isAppOf ``phoareStmt then
          rest := rest.push h; continue
        if tag == `hupd then
          let (_, h') ← h.intros
          h'.refl; continue
        if tag == `hA || tag == `hE then
          let [] ← Term.TermElabM.run' (Tactic.run h (do
              evalTactic (← `(tactic| first
                | (intros; rfl)
                | (intros; simp_reads; done)
                | (intros; simp_reads; first | assumption | exact id)
                | (simp_reads; intros; assumption)))))
            | throwError "not kept"
          continue
        rest := rest.push h
      pure (some rest.toList)
    catch _ => s.restore; pure none
  -- EC's `P /\ x = e` when the update cannot change `P` (its reads simplified, `P` again)
  let trivialPre ← do
    let A := ty.getArg! 0
    forallTelescope (← inferType A) fun xs _ => isDefEq (mkAppN A xs) (mkConst ``True)
  let kept? ← if read?.isSome then pure read? else if trivialPre then pure none else do
    let s ← saveState
    try
      let gs ← applyLemma keep g #[(`hd, hd)]
      -- `hA` (the invariance) is the open argument before the judgment
      let some hA := gs[gs.size - 2]? | throwError "sp: unexpected arguments"
      let [] ← Term.TermElabM.run' (Tactic.run hA (do
          evalTactic (← `(tactic| first
            | (intros; simp_reads; first | assumption | exact id)
            | (simp_reads; intros; assumption)))))
        | throwError "not invariant"
      pure (some (gs.toList.filter (· != hA)))
    catch _ => s.restore; pure none
  let gs ← match kept? with
    | some gs => pure gs
    | none => pure (← applyLemma lem g #[(`hd, hd)]).toList
  -- the bound's invariance (`phoare`): by `rfl` for a bound that does not read the state
  let mut out := []
  for h in gs do
    let t ← instantiateMVars (← h.getType)
    if t.isForall && !(t.getForallBody.isAppOf ``phoareStmt) then
      let s ← saveState
      try
        let (_, h') ← h.intros
        h'.refl
        continue
      catch _ => s.restore
    out := out ++ [h]
  return some out

/-- `sp` on side `side?`, `n?` statements (all deterministic ones at the start for `none`). -/
partial def spSide (g : MVarId) (side? : Option Nat) (n? : Option Nat) :
    MetaM (List MVarId) := do
  if n? == some 0 then return [g]
  let some gs ← spOne g side? | do
    if n?.isSome then throwError "sp: the first statement is not deterministic"
    return [g]
  -- the judgment goes on, the side conditions after it
  let (js, rest) ← gs.partitionM fun h => do
    let t ← instantiateMVars (← h.getType)
    return t.isAppOf ``prhlStmt || t.isAppOf ``hoareStmt || t.isAppOf ``phoareStmt
  let some j := js.head? | return gs
  return (← spSide j side? (n?.map (· - 1))) ++ rest

end ECSp

open Lean Elab Tactic ECSp in
/-- **EC's `sp`**: see the module docstring. -/
elab "stmt_sp" s:(Judgment.judgmentSide)? n:(ppSpace num)? : tactic => do
  let g ← getMainGoal
  let n? := n.map (·.getNat)
  let ty ← instantiateMVars (← g.getType)
  let gs ← match Judgment.sideOf? s with
    | some i => spSide g (some i) n?
    | none =>
      if ty.isAppOf ``prhlStmt then do
        let gs ← spSide g (some 1) n?
        match gs with
        | j :: rest => pure ((← spSide j (some 2) n?) ++ rest)
        | [] => pure []
      else spSide g none n?
  replaceMainGoal gs

open Lean Meta Elab Tactic ECSp Judgment in
/-- **EC's `sp n m`** on a relational judgment, with EC's code positions (`Judgment.ecGap`): the
statements before the gap `n` of the left side and before the gap `m` of the right forward (`0`:
none; `-k`: up to and with the `k`-th statement from the end). -/
elab "stmt_sp" ppSpace n:ecPos ppSpace m:ecPos : tactic => do
  let g ← getMainGoal
  let count (g : MVarId) (side : Nat) (pos : Int) : MetaM Nat := g.withContext do
    let (d, ty) ← descOf g (some side)
    let len ← HoareSplit.seqLength (stripLets (ty.getArg! d.stmtArg))
    ecGap pos len
  let k₁ ← count g 1 (ecPosOf n)
  let gs ← spSide g (some 1) (some k₁)
  match gs with
  | j :: rest =>
    let k₂ ← count j 2 (ecPosOf m)
    replaceMainGoal ((← spSide j (some 2) (some k₂)) ++ rest)
  | [] => replaceMainGoal []

end GaudisCrypt
