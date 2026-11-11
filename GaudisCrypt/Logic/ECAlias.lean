import GaudisCrypt.Logic.StmtSwap
import GaudisCrypt.Logic.ECLoop
import GaudisCrypt.Logic.HoareSplit
import GaudisCrypt.Logic.PRHLWp

/-!
# EasyCrypt's `alias`

    stmt_alias{i} n x = e      -- EC's `alias{i} n x = e`

Before EC's statement `n` of side `i` (from 1, the resets inlining leaves not counted), the
assignment `x <- e` to a fresh local `x`: it records `e` there, for the conditions after.  The
judgment about the code with the assignment gives the one without
(`prhlStmt_alias_left`/`_right`): the code does not touch `x` (it commutes with every write to
`x`, shown as for `stmt_swap`), and the postcondition does not read `x` on that side (a goal
when `simp` cannot show it).  `x`'s type is `e`'s.
-/

namespace GaudisCrypt

/-- Running `s₁; x <- e; s₂` and putting `x` back to its value at the start is running
`s₁; s₂`, when neither touches `x`. -/
theorem Stmt.ewp_alias {α : Type} (x : Lens α ProgramState) (e : Getter α ProgramState)
    {s₁ s₂ : Stmt} (h₁ : ∀ v, s₁.CommutesWith (x.set v)) (h₂ : ∀ v, s₂.CommutesWith (x.set v))
    (g : ProgramState → ENNReal) (σ : ProgramState) :
    Stmt.ewp (.seq s₁ (.seq (.assign (x : Setter α ProgramState) e) s₂))
        (fun τ => g (x.set (x.get σ) τ)) σ =
      Stmt.ewp (.seq s₁ s₂) g σ := by
  simp only [Stmt.ewp_seq, Stmt.ewp_assign]
  have hin : ∀ τ, s₂.ewp (fun ρ => g (x.set (x.get σ) ρ))
      ((x : Setter α ProgramState).set (e.get τ) τ) = s₂.ewp g (x.set (x.get σ) τ) := by
    intro τ
    rw [h₂ (e.get τ), h₂ (x.get σ) g τ]
    congr 1
    funext ρ
    rw [x.set_set]
  simp only [hin]
  rw [← h₁ (x.get σ) (s₂.ewp g) σ, x.get_set]

/-- A statement's run is determined by its expectations, here put through a state map. -/
theorem programDenotation_alias {α : Type} (x : Lens α ProgramState) (e : Getter α ProgramState)
    {s₁ s₂ : Stmt} (h₁ : ∀ v, s₁.CommutesWith (x.set v)) (h₂ : ∀ v, s₂.CommutesWith (x.set v))
    (σ : ProgramState) (F : Unit × ProgramState → ENNReal) :
    (programDenotation (.seq s₁ (.seq (.assign (x : Setter α ProgramState) e) s₂)) σ).expected
        (fun r => F (r.1, x.set (x.get σ) r.2)) =
      (programDenotation (.seq s₁ s₂) σ).expected F := by
  have := Stmt.ewp_alias x e h₁ h₂ (fun τ => F ((), τ)) σ
  simp only [Stmt.ewp, ProgramDenotation.wp] at this
  exact this

variable {A B : ProgramState → ProgramState → Prop}

/-- **EC's `alias{1}`**: the judgment about `s₁; s₂` from the one about `s₁; x <- e; s₂`, when
neither part touches `x` and the postcondition does not read `x` on the left. -/
theorem prhlStmt_alias_left {α : Type} (x : Lens α ProgramState) (e : Getter α ProgramState)
    {s₁ s₂ c : Stmt} (h₁ : ∀ v, s₁.CommutesWith (x.set v)) (h₂ : ∀ v, s₂.CommutesWith (x.set v))
    (hB : ∀ v τ₁ τ₂, B τ₁ τ₂ → B (x.set v τ₁) τ₂)
    (h : prhlStmt A (.seq s₁ (.seq (.assign (x : Setter α ProgramState) e) s₂)) c B) :
    prhlStmt A (.seq s₁ s₂) c B := by
  intro σ₁ σ₂ hA
  obtain ⟨μ, m1, m2, sat⟩ := h σ₁ σ₂ hA
  refine ⟨μ >>= fun w => pure ((w.1.1, x.set (x.get σ₁) w.1.2), w.2), ?_, ?_, ?_⟩
  · refine SubProbability.marginal_fst_eq fun F => ?_
    rw [SubProbability.expected_bind]
    simp only [expected_pure]
    rw [SubProbability.expected_fst_of_marginal m1 (fun r => F (r.1, x.set (x.get σ₁) r.2)),
      programDenotation_alias x e h₁ h₂]
  · refine SubProbability.marginal_snd_eq fun F => ?_
    rw [SubProbability.expected_bind]
    simp only [expected_pure]
    exact SubProbability.expected_snd_of_marginal m2 F
  · exact SubProbability.satisfies_bind _ fun w hw =>
      SubProbability.satisfies_pure _ _ (hB _ _ _ (sat w hw))

/-- **EC's `alias{2}`**: `prhlStmt_alias_left` on the right. -/
theorem prhlStmt_alias_right {α : Type} (x : Lens α ProgramState) (e : Getter α ProgramState)
    {s₁ s₂ c : Stmt} (h₁ : ∀ v, s₁.CommutesWith (x.set v)) (h₂ : ∀ v, s₂.CommutesWith (x.set v))
    (hB : ∀ v τ₁ τ₂, B τ₁ τ₂ → B τ₁ (x.set v τ₂))
    (h : prhlStmt A c (.seq s₁ (.seq (.assign (x : Setter α ProgramState) e) s₂)) B) :
    prhlStmt A c (.seq s₁ s₂) B :=
  prhlStmt_of_symm (prhlStmt_alias_left (B := fun σ₂ σ₁ => B σ₁ σ₂) x e h₁ h₂
    (fun v τ₂ τ₁ hb => hB v τ₁ τ₂ hb) h.symm)

/-- **EC's `alias{i} n x = e`**: see the module docstring. -/
syntax (name := stmtAlias) "stmt_alias" Judgment.judgmentSide ppSpace num ppSpace ident " = "
  term : tactic

open Lean Meta Elab Tactic PRHLWp StmtSwap in
elab_rules (kind := stmtAlias) : tactic
  | `(tactic| stmt_alias $s $n:num $x:ident = $e) => withMainContext do
    let side := (Judgment.sideOf? (some s)).getD 1
    let g ← getMainGoal
    let ty ← prhlGoal g "stmt_alias"
    let st := ty.getArg! side
    -- our position of EC's statement `n` (the resets before it come after the alias)
    let rs ← TacticMisc.spineResets st
    let gs := TacticMisc.ecGroups rs
    let n := n.getNat
    unless 1 ≤ n && n ≤ gs.size + 1 do
      throwError "stmt_alias: no position {n} (the code has {gs.size} statements)"
    let p := (gs.extract 0 (n - 1)).foldl (· + ·) 0
    -- `e` over side `side`'s variables, and the fresh local `x` of its type
    let vars := (← ProgramSyntax.frameVars #[st] #[]).filter (·.nameable)
    let mut t ← `((GaudiExpr[ $e ] : Getter _ ProgramState))
    for v in vars.reverse do
      let some slot := v.slots[0]? | continue
      t ← `(letI $(mkIdent (.mkSimple v.name)) := $(← Term.exprToSyntax slot); $t)
    let eE ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let eE ← instantiateMVars eE
    let α := (← whnfR (← inferType eE)).getArg! 0
    let (_, lty, lval) ← liftMacroM (ProgramSyntax.varBinding x (← Term.exprToSyntax α))
    let xE ← Term.elabTermEnsuringType lval (← Term.elabType lty)
    Term.synthesizeSyntheticMVarsNoPostponing
    let xE ← instantiateMVars xE
    -- the code cut where the assignment goes, and the rule
    let g ← Judgment.onStmt (HoareSplit.splitSeq (rs.length - p)) g (some side)
    setGoals [g]
    let lem := mkIdent (if side == 1 then ``prhlStmt_alias_left else ``prhlStmt_alias_right)
    evalTactic (← `(tactic| refine $lem $(← Term.exprToSyntax xE) $(← Term.exprToSyntax eE)
      ?h₁ ?h₂ ?hB ?h))
    let mut rest : Array MVarId := #[]
    for g in ← getGoals do
      let tag := (← g.getTag).eraseMacroScopes
      if tag == `h₁ || tag == `h₂ then
        -- the code does not touch `x`: it commutes with the writes to it
        let pf ← g.withContext do
          forallTelescope (← instantiateMVars (← g.getType)) fun vs body => do
            let pf ← try commutesOf (body.getArg! 0) (body.getArg! 1) (some xE)
              catch err => throwError "stmt_alias: `{x.getId}` is not fresh: \
                {err.toMessageData}"
            mkLambdaFVars vs pf
        g.assign pf
      else if tag == `hB then
        -- the postcondition does not read `x` on that side
        let s ← saveState
        try
          let [] ← evalTacticAt (← `(tactic| first
              | (intros; simp_reads; assumption)
              | (simp_reads; intros; assumption))) g
            | throwError "no"
        catch _ => s.restore; rest := rest.push g
      else rest := rest.push g
    -- the judgment first, then what is left of the side condition
    let isH (g : MVarId) : TacticM Bool := return (← g.getTag).eraseMacroScopes == `h
    -- at the start: the empty code before the assignment dropped (`skip; s` is `s`)
    if p == 0 then
      rest ← rest.mapM fun g => do
        unless ← isH g do return g
        let g' ← Judgment.onStmt (fun s => do
          let s ← TacticMisc.openStmt s
          unless s.isAppOfArity ``StmtWithHoles.seq 3 do throwError "no"
          return (s.getArg! 2, ← mkAppM ``StmtWithHoles.Equiv.skip_seq #[s.getArg! 2])) g
          (some side)
        g'.setTag `h
        return g'
    setGoals ((← rest.filterM isH).toList ++ (← rest.filterM fun g => return !(← isH g)).toList)

end GaudisCrypt
