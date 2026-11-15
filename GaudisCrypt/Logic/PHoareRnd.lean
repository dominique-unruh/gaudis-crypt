import GaudisCrypt.Logic.PHoareSeq
import GaudisCrypt.Logic.PRHLStmt
import GaudisCrypt.Logic.ECWhile
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.CallSpec
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Lib.EC.Logic

/-!
# pHL on an exact bound: EC's `rnd E`, `conseq`, `islossless`

EC proves `phoare[ c; x <$ d : P ==> Q ] = r` by

    rnd E.                      (* c : P ==> mu d E = r /\ forall v, v \in d => (E v <=> Q v) *)
    conseq (: _ ==> true).      (* the condition holds in every state *)
    islossless.                 (* c is lossless *)

The judgments of `Logic/PHoare.lean` are about expectations, and their rules for a sampling
(`phoare_auto`, `rnd_pred1`) work on the expectation it leaves, for upper bounds.  Here are EC's
three steps for an exact bound, on the judgment itself.
-/

namespace GaudisCrypt

open Classical in
/-- An expectation that is `r` on an event of probability `1` (and at most `1` elsewhere) has
expected value `r`. -/
theorem Stmt.ewp_eq_of_certain (s : Stmt) {Ψ : ProgramState → Prop} {h : ProgramState → ENNReal}
    {r : ENNReal} {σ : ProgramState} (hΨ : s.ewp (fun τ => indicatorE (Ψ τ)) σ = 1)
    (hle : ∀ τ, h τ ≤ 1) (hr : ∀ τ, Ψ τ → h τ = r) : s.ewp h σ = r := by
  have hnot : s.ewp (fun τ => indicatorE (¬ Ψ τ)) σ = 0 := by
    have hsum : s.ewp (fun τ => indicatorE (Ψ τ) + indicatorE (¬ Ψ τ)) σ ≤ 1 := by
      refine (Stmt.ewp_mono s (G := fun _ => 1) (fun τ => ?_) σ).trans (Stmt.ewp_const_le s 1 σ)
      by_cases hτ : Ψ τ <;> simp [hτ]
    rw [Stmt.ewp_add, hΨ] at hsum
    exact le_antisymm ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp (by simpa using hsum))
      bot_le
  refine le_antisymm ?_ ?_
  · calc s.ewp h σ ≤ s.ewp (fun τ => r * indicatorE (Ψ τ) + indicatorE (¬ Ψ τ)) σ := by
          refine Stmt.ewp_mono s (fun τ => ?_) σ
          by_cases hτ : Ψ τ
          · simp [hτ, hr τ hτ]
          · simpa [hτ] using hle τ
      _ = r := by rw [Stmt.ewp_add, Stmt.ewp_const_mul, hΨ, hnot, mul_one, add_zero]
  · calc r = s.ewp (fun τ => r * indicatorE (Ψ τ)) σ := by rw [Stmt.ewp_const_mul, hΨ, mul_one]
      _ ≤ s.ewp h σ := by
          refine Stmt.ewp_mono s (fun τ => ?_) σ
          by_cases hτ : Ψ τ
          · simp [hτ, hr τ hτ]
          · simp [hτ]

/-- **EC's pHL `rnd E`** on an exact bound: the code before the sampling reaches, with
probability `1`, a state in which `E` has probability `r` under the distribution and, on its
support, `E` is the postcondition. -/
theorem phoareStmt_rnd_eq {A : ProgramState → Prop} {c : Stmt} {α : Type}
    {x : Setter α ProgramState} {e : Getter (SubProbability α) ProgramState}
    (E : ProgramState → α → Prop) {Q : ProgramState → Prop} {r : ENNReal}
    (h : phoareStmt A c (fun τ => indicatorE
        (((e.get τ).expected fun v => indicatorE (E τ v)) = r ∧
          ∀ v ∈ (e.get τ).support, (E τ v ↔ Q (x.set v τ)))) Eq (fun _τ => 1)) :
    phoareStmt A (.seq c (.sample x e)) (fun τ => indicatorE (Q τ)) Eq (fun _τ => r) := by
  intro σ hA
  rw [Stmt.ewp_seq, Stmt.ewp_sample]
  refine Stmt.ewp_eq_of_certain c (h σ hA) (fun τ => ?_) (fun τ ⟨hr, hE⟩ => ?_)
  · refine SubProbability.expected_le_one _ (fun a => ?_)
    unfold indicatorE; split_ifs <;> simp
  · rw [← hr]
    refine SubProbability.expected_congr_satisfies (P := (· ∈ (e.get τ).support))
      (fun v hv => SubProbability.mem_support_of_ne_zero hv) (fun v hv => ?_)
    by_cases hQ : Q (x.set v τ)
    · rw [indicatorE_of hQ, indicatorE_of ((hE v hv).mpr hQ)]
    · rw [indicatorE_of_not hQ, indicatorE_of_not (fun h => hQ ((hE v hv).mp h))]

/-- **EC's `conseq (: _ ==> Q')`** on `phoare[ … ] = 1`: a weaker condition that is still reached
with probability `1`. -/
theorem phoareStmt_conseq_eq_one {A : ProgramState → Prop} {c : Stmt}
    {Q : ProgramState → Prop} (Q' : ProgramState → Prop)
    (hQ : ∀ τ, Q' τ → Q τ)
    (h : phoareStmt A c (fun τ => indicatorE (Q' τ)) Eq (fun _τ => 1)) :
    phoareStmt A c (fun τ => indicatorE (Q τ)) Eq (fun _τ => 1) := by
  classical
  intro σ hA
  refine le_antisymm (phoareStmt_indicator_le_one A c Q σ hA) ?_
  refine (h σ hA).ge.trans (Stmt.ewp_mono c (fun τ => ?_) σ)
  by_cases hτ : Q' τ
  · rw [indicatorE_of hτ, indicatorE_of (hQ τ hτ)]
  · rw [indicatorE_of_not hτ]; exact bot_le

/-- EC's `mu d E`: the probability of the event `E` under `d`, a real. -/
noncomputable def EC.mu {α : Type} (d : SubProbability α) (E : α → Prop) : ℝ :=
  (d.expected fun v => indicatorE (E v)).toReal

/-- EC's `mu1 d c` is `mu d (pred1 c)`. -/
theorem EC.mu_pred1 {α : Type} (d : SubProbability α) (c : α) :
    EC.mu d (EC.pred1 c) = EC.mu1 d c := by
  classical
  unfold EC.mu EC.mu1 EC.pred1 indicatorE
  rw [EC.mu1_eq_expected]

/-- EC's `dbool1E`, over the reals: `mu1 {0,1} b = 1%r / 2%r`. -/
theorem EC.dbool1E_mu1 (b : Bool) : EC.mu1 EC.dbool b = 1 / 2 := by
  rw [EC.mu1, EC.dbool1E]; simp

/-- `phoareStmt_rnd_eq` for a real bound (`Pr[ … ] = r`): the event's probability as EC's
`mu d E`. -/
theorem phoareStmt_rnd_eq_ofReal {A : ProgramState → Prop} {c : Stmt} {α : Type}
    {x : Setter α ProgramState} {e : Getter (SubProbability α) ProgramState}
    (E : ProgramState → α → Prop) {Q : ProgramState → Prop} {r : ℝ}
    (h : phoareStmt A c (fun τ => indicatorE
        (EC.mu (e.get τ) (E τ) = r ∧
          ∀ v ∈ (e.get τ).support, (E τ v ↔ Q (x.set v τ)))) Eq (fun _τ => 1)) :
    phoareStmt A (.seq c (.sample x e)) (fun τ => indicatorE (Q τ)) Eq
      (fun _τ => ENNReal.ofReal r) := by
  refine phoareStmt_rnd_eq E (phoareStmt_conseq_eq_one _ (fun τ ⟨hr, hE⟩ => ⟨?_, hE⟩) h)
  have hfin : ((e.get τ).expected fun v => indicatorE (E τ v)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (SubProbability.expected_le_one _ (fun a => by
      unfold indicatorE; split_ifs <;> simp))
  rw [← hr, EC.mu, ENNReal.ofReal_toReal hfin]

open Lean Meta Elab Tactic PHoareSeq PHoareWp in
/-- **EC's pHL `rnd E`** on an exact bound, `phoare[ c; x <$ d : P ==> Q ] = r`: the goal becomes
`phoare[ c : P ==> mu d E = r ∧ ∀ v ∈ d, (E v ↔ Q v) ] = 1` (`phoareStmt_rnd_eq`).  `E` is a
predicate on the sampled value and may read the program's variables (`pred1 §b'`). -/
elab "phoare_rnd " E:term:max : tactic => do
  liftMetaTactic1 fun g => some <$> Judgment.onStmt (HoareSplit.splitSeq 1) g
  let g ← getMainGoal
  let gs ← g.withContext do
    -- a real bound (`ENNReal.ofReal r`, as `byphoare` leaves it): EC's `mu d E = r`
    let fits (lem : Name) : TacticM (Option (Lean.Expr × Array Lean.Expr × List Name)) := do
      let s ← saveState
      let c ← mkConstWithFreshMVarLevels lem
      let (ms, _, ty) ← forallMetaTelescope (← inferType c)
      if ← isDefEq ty (← g.getType) then
        return some (c, ms, (← inferType c).getForallBinderNames)
      s.restore
      return none
    let some (c, ms, names) ← (do
        match ← fits ``phoareStmt_rnd_eq_ofReal with
        | some r => pure (some r)
        | none => fits ``phoareStmt_rnd_eq)
      | throwError "phoare_rnd: not `phoare[ c; x <$ d : P ==> Q ] = r` with `Q` an event and \
          `r` a constant{indentExpr (← g.getType)}"
    let idx (n : Name) : TacticM Nat := do
      let some i := names.findIdx? (· == n) | throwError "phoare_rnd: no argument `{n}`"
      return i
    let α ← instantiateMVars ms[← idx `α]!
    let Ee ← elabGoalFunction E (← mkArrow α (mkSort Level.zero))
    unless ← isDefEq ms[← idx `E]! Ee do throwError "phoare_rnd: the event does not fit"
    g.assign (mkAppN c ms)
    let m := ms[← idx `h]!.mvarId!
    m.setTag `judgment
    let ty ← Core.betaReduce (← instantiateMVars (← m.getType))
    let m ← m.replaceTargetDefEq ty
    -- the condition as the notation shows it (the reads through the sampling's write), under
    -- the indicator: it stays one event
    let g := ty.getArg! 2
    let .lam n d b bi := g | return [m]
    unless b.isAppOfArity ``indicatorE 1 do return [m]
    let inner := Lean.Expr.lam n d (b.getArg! 0) bi
    -- (the bound is kept as it is written: abstracted while the rest is simplified)
    let rE ← instantiateMVars ms[← idx `r]!
    let innerAbs ← kabstract inner rE
    let (e', h?) ← withLocalDeclD `r (← inferType rE) fun fv => do
      let r ← simpExprWith ewpDecls (innerAbs.instantiate1 fv)
      return (← mkLambdaFVars #[fv] r.expr, ← r.proof?.mapM (mkLambdaFVars #[fv] ·))
    let r : Simp.Result := { expr := (mkApp e' rE).headBeta, proof? := h?.map (mkApp · rE) }
    let args := ty.getAppArgs
    let mk (P : Lean.Expr) : MetaM Lean.Expr :=
      withLocalDeclD `τ d fun τ =>
        mkLambdaFVars #[τ] (mkApp (mkConst ``indicatorE) (mkApp P τ).headBeta)
    let target := mkAppN ty.getAppFn (args.set! 2 (← mk r.expr))
    let some h := r.proof? | return [← m.replaceTargetDefEq target]
    let motive ← withLocalDeclD `P (← inferType inner) fun P => do
      mkLambdaFVars #[P] (mkAppN ty.getAppFn (args.set! 2 (← mk P)))
    return [← m.replaceTargetEq target (← mkCongrArg motive h)]
  replaceMainGoal gs

open Lean Meta Elab Tactic PHoareWp GaudisCrypt.ECConseq in
/-- **EC's `conseq (: _ ==> Q)`** on `phoare[ c : P ==> Q₀ ] = 1`: goals `post` (`Q` implies
`Q₀`), then the judgment with `Q` (`phoareStmt_conseq_eq_one`). -/
elab "phoare_conseq" " (" ": " P:term " ==> " Q:term ")" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOf ``phoareStmt && isHole P && !isHole Q do throwUnsupportedSyntax
  unless (ty.getArg! 3).isAppOf ``Eq do throwUnsupportedSyntax
  let Qs ← Term.exprToSyntax (← elabGoalFunction Q (mkSort Level.zero))
  refineTagged (← `(phoareStmt_conseq_eq_one $Qs ?post ?judgment)) [`post, `judgment]
  let gs ← (← getGoals).mapM fun g => do
    match ← g.getTag with
    -- the implication, over values (the reads generalized)
    | `post => cleanSideGoal g
    -- the judgment, its event `True` the expectation `1`
    | `judgment => simpPost g
    | _ => pure g
  setGoals gs

/-- The uniform distribution on a finite nonempty type is lossless, as the sum `phoare_auto`
leaves at a sampling from it. -/
theorem ENNReal.sum_one_div_card_eq_one (α : Type) [Fintype α] [Nonempty α] :
    (∑ _x : α, (1 : ENNReal) / (Fintype.card α : ENNReal)) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
  exact ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _)

namespace PHoareRnd

open Lean Meta Elab Tactic

/-- The procedure the last statement of `s` calls, if it is a call. -/
partial def lastCallee? (s₀ : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let s ← TacticMisc.openStmt s₀
  if let .letE n ty val body _ := s then
    return ← withLetDecl n ty val fun fv => do
      let r ← lastCallee? (body.instantiate1 fv)
      return r.map (·.replaceFVar fv val)
  if s.isAppOfArity ``StmtWithHoles.seq 3 then return ← lastCallee? (s.getArg! 2)
  if s.isAppOf ``StmtWithHoles.call then
    for a in s.getAppArgs do
      if (← whnfR (← inferType a)).isAppOf ``Procedure then return some a
  return none

/-- The number of statements of `s` (under the `let`s of its local variables). -/
partial def stmtLength (s₀ : Lean.Expr) : MetaM Nat := do
  let s ← TacticMisc.openStmt s₀
  if let .letE n ty val body _ := s then
    return ← withLetDecl n ty val fun fv => stmtLength (body.instantiate1 fv)
  HoareSplit.seqLength s

/-- EC's `islossless` on `phoare[ c : P ==> 1 ] = 1`: the code statement by statement from the
end (`phoare_seq_lossless … : True`), an assignment or a sampling by `phoare_auto`, a call by a
new goal `islossless p` (`phoare_call`).  The calls' goals, the last call first. -/
partial def islosslessLoop (fuel : Nat) (acc : Array MVarId) : TacticM (Array MVarId) := do
  if fuel == 0 then throwError "islossless: gave up"
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOf ``phoareStmt do
    throwError "islossless: not a `phoare` judgment{indentExpr ty}"
  let n ← g.withContext (stmtLength (ty.getArg! 1))
  if n ≤ 1 then
    match ← g.withContext (lastCallee? (ty.getArg! 1)) with
    | some p =>
      let hp ← g.withContext do
        mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Procedure.IsLossless #[p]) `lossless
      evalTactic (← `(tactic| (phoare_call $(← Term.exprToSyntax hp); try (phoare_auto; done))))
      unless (← getGoals).isEmpty do
        throwError "islossless: the call's goal is left{indentExpr ty}"
      return acc.push hp.mvarId!
    | none =>
      -- an assignment, or a sampling from a lossless distribution (the uniform one: its mass,
      -- a sum of `1 / card`)
      evalTactic (← `(tactic| first
        | (phoare_auto; done)
        | (phoare_auto; intros; exact ENNReal.sum_one_div_card_eq_one _)
        | (phoare_auto; intros
           exact (EC.is_lossless_iff_expected _).mp
             (by first | exact EC.dbool_ll | exact EC.uniform_ll | assumption))
        | fail "islossless: cannot show that a sampling is lossless (a hypothesis \
            `is_lossless d` in the context is used)"))
      return acc
  else
    evalTactic (← `(tactic| phoare_seq_lossless $(Syntax.mkNumLit (toString (n - 1))) : (True)))
    let [g₁, g₂] ← getGoals | throwError "islossless: `seq` left other goals than two"
    setGoals [g₂]
    let acc ← islosslessLoop (fuel - 1) acc
    setGoals [g₁]
    islosslessLoop (fuel - 1) acc

end PHoareRnd

open Lean Meta Elab Tactic in
/-- **EC's `islossless`**: a statement without loops is lossless when its samplings and the
procedures it calls are.  On `phoare[ c : P ==> true ] = 1` (and on `islossless M.f`): one goal
`islossless p` per call, the last call first (EC's order). -/
elab "islossless" : tactic => do
  let g ← getMainGoal
  if (← instantiateMVars (← g.getType)).cleanupAnnotations.isAppOf ``Procedure.IsLossless then
    evalTactic (← `(tactic| phoare_proc))
  let rest := (← getGoals).drop 1
  setGoals [← getMainGoal]
  let calls ← PHoareRnd.islosslessLoop 64 #[]
  setGoals (calls.toList ++ rest)

end GaudisCrypt
