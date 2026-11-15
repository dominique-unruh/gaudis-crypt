import GaudisCrypt.Logic.PHoareSeq
import GaudisCrypt.Logic.PRHLStmt
import GaudisCrypt.Logic.ECWhile
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.CallSpec
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECHints
import GaudisCrypt.Lib.EC.BitWord
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

/-! ## Events reached with probability `1`

`phoare[ c : P ==> Q ] = 1` with `Q` an event: EC's rules keep it an event (a lossless call
leaves `∀ result, Q`, a sampling `is_lossless d ∧ ∀ v ∈ d, Q`), where the rules on expectations
(`Logic/PHoareWp.lean`) would leave a product of indicators, a sum, or a callee's expectation. -/

theorem indicatorE_mul_fold (P Q : Prop) : indicatorE P * indicatorE Q = indicatorE (P ∧ Q) :=
  (indicatorE_and P Q).symm

theorem indicatorE_ite_fold (c : Prop) [Decidable c] (P Q : Prop) :
    (if c then indicatorE P else indicatorE Q) = indicatorE (if c then P else Q) := by
  split_ifs <;> rfl

/-- **EC's `call H`** with `H : islossless f`, on `phoare[ c; x <@ f(a) : P ==> Q ] = 1`: the
code before the call reaches, with probability `1`, a state from which `Q` holds whatever the
call returns (and whatever globals it leaves). -/
theorem phoareStmt_call_lossless_eq_one {sig} {A : ProgramState → Prop} {pre : Stmt}
    {x : Setter sig.ret ProgramState} {p : Procedure sig} {a : Getter sig.ParamType ProgramState}
    {Q : ProgramState → Prop} (hp : p.IsLossless)
    (h : phoareStmt A pre (fun σ => indicatorE
      (∀ v gl, Q (x.set v (ProgramState.globalL.set gl σ)))) Eq (fun _τ => 1)) :
    phoareStmt A (.seq pre (Stmt.call x p a)) (fun τ => indicatorE (Q τ)) Eq (fun _τ => 1) := by
  intro σ hA
  rw [Stmt.ewp_seq]
  refine Stmt.ewp_eq_of_certain pre (h σ hA) (fun τ => ?_) (fun τ hτ => ?_)
  · simp only [Stmt.ewp_call]
    exact (Procedure.ewp_mono _ _ (fun _ _ => indicatorE_le_one _) _).trans
      (Procedure.ewp_const_le _ _ 1 _)
  · simp only [Stmt.ewp_call]
    have h1 : (fun v gl => indicatorE (Q (x.set v (ProgramState.globalL.set gl τ)))) =
        fun _ _ => (1 : ENNReal) := by
      funext v gl; exact indicatorE_of (hτ v gl)
    rw [h1]; exact hp _ _

/-- **EC's pHL `rnd`** (`rnd predT`) on `phoare[ c; x <$ d : P ==> Q ] = 1`: the distribution is
lossless and `Q` holds on its support. -/
theorem phoareStmt_rnd_lossless_eq_one {A : ProgramState → Prop} {c : Stmt} {α : Type}
    {x : Setter α ProgramState} {e : Getter (SubProbability α) ProgramState}
    {Q : ProgramState → Prop}
    (h : phoareStmt A c (fun τ => indicatorE
        (EC.is_lossless (e.get τ) ∧ ∀ v ∈ (e.get τ).support, Q (x.set v τ))) Eq (fun _τ => 1)) :
    phoareStmt A (.seq c (.sample x e)) (fun τ => indicatorE (Q τ)) Eq (fun _τ => 1) := by
  refine phoareStmt_rnd_eq (fun _ _ => True) (phoareStmt_conseq_eq_one _
    (fun τ ⟨hl, hQ⟩ => ⟨?_, fun v hv => ⟨fun _ => hQ v hv, fun _ => trivial⟩⟩) h)
  simpa using (EC.is_lossless_iff_expected _).mp hl

/-- The end of a proof of `phoare[ skip : P ==> Q ] = 1`: `P` implies `Q`. -/
theorem phoareStmt_skip_event {A Q : ProgramState → Prop} (h : ∀ σ, A σ → Q σ) :
    phoareStmt A .skip (fun τ => indicatorE (Q τ)) Eq (fun _τ => 1) :=
  phoareStmt_skip_iff.mpr fun σ hA => indicatorE_of (h σ hA)

namespace PHoareRnd

open Lean Meta Elab Tactic PHoareSeq PHoareWp

/-- The expectation of the `phoare` judgment `g` as one event, `fun τ => indicatorE (Q τ)`
(the rules on expectations split a conjunction into a product, a conditional into two
indicators); with `one`, the expectation `1` is the event `True`.  `none` if it is not an
event. -/
def foldEvent (g : MVarId) (one := false) : MetaM (Option MVarId) := do
  let s ← saveState
  let r ← go
  if r.isNone then s.restore
  return r
where
  go : MetaM (Option MVarId) := g.withContext do
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOfArity ``phoareStmt 5 do return none
    let g ← try Judgment.simpArg g 2 [``indicatorE_mul_fold, ``indicatorE_ite_fold] []
      catch _ => pure g
    let ty ← instantiateMVars (← g.getType)
    let .lam n d b bi := ty.getArg! 2 | return none
    if b.isAppOfArity ``indicatorE 1 then return some g
    unless one do return none
    -- `1`: the event `True`
    unless b.isAppOfArity ``OfNat.ofNat 3 && b.getArg! 1 == mkRawNatLit 1 do return none
    let args := ty.getAppArgs
    let post := Lean.Expr.lam n d (mkApp (mkConst ``indicatorE) (mkConst ``True)) bi
    let target := mkAppN ty.getAppFn (args.set! 2 post)
    let pf ← mkFreshExprMVar (← mkEq target ty)
    let (r, _) ← simpGoal pf.mvarId! (← Simp.mkContext
      (simpTheorems := #[← ({} : SimpTheorems).addConst ``indicatorE_true]))
    if r.isSome then return none
    return some (← g.replaceTargetEq target (← mkEqSymm pf))

/-- Is the judgment `g` an exact one with the bound `1` (`ENNReal.ofReal 1`, as `byphoare`
leaves it, is rewritten to `1`)?  `none`, the state restored, if not. -/
def boundOne (g : MVarId) : MetaM (Option MVarId) := do
  let s ← saveState
  let r ← go
  if r.isNone then s.restore
  return r
where
  go : MetaM (Option MVarId) := g.withContext do
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOfArity ``phoareStmt 5 && (ty.getArg! 3).isAppOf ``Eq do return none
    let g ← try Judgment.simpArg g 4 [``ENNReal.ofReal_one] [] catch _ => pure g
    let ty ← instantiateMVars (← g.getType)
    let .lam _ _ b _ := ty.getArg! 4 | return none
    unless b.isAppOfArity ``OfNat.ofNat 3 && b.getArg! 1 == mkRawNatLit 1 do return none
    return some g

/-- The event of the judgment `m` (`fun τ => indicatorE (P τ)`) simplified under the indicator
(`ewpDecls`: the reads through the last statement's write), so that it stays one event; `keep`,
if given, is abstracted meanwhile (a bound, kept as it is written). -/
def simpEvent (m : MVarId) (keep : Option Lean.Expr := none) : MetaM MVarId := m.withContext do
  let ty ← Core.betaReduce (← instantiateMVars (← m.getType))
  let m ← m.replaceTargetDefEq ty
  let g := ty.getArg! 2
  let .lam n d b bi := g | return m
  unless b.isAppOfArity ``indicatorE 1 do return m
  let inner := Lean.Expr.lam n d (b.getArg! 0) bi
  let r : Simp.Result ← match keep with
    | some rE => do
      let innerAbs ← kabstract inner rE
      let (e', h?) ← withLocalDeclD `r (← inferType rE) fun fv => do
        let r ← simpExprWith ewpDecls (innerAbs.instantiate1 fv)
        return (← mkLambdaFVars #[fv] r.expr, ← r.proof?.mapM (mkLambdaFVars #[fv] ·))
      pure { expr := (mkApp e' rE).headBeta, proof? := h?.map (mkApp · rE) }
    | none => simpExprWith ewpDecls inner
  let args := ty.getAppArgs
  let mk (P : Lean.Expr) : MetaM Lean.Expr :=
    withLocalDeclD `τ d fun τ =>
      mkLambdaFVars #[τ] (mkApp (mkConst ``indicatorE) (mkApp P τ).headBeta)
  let target := mkAppN ty.getAppFn (args.set! 2 (← mk r.expr))
  let some h := r.proof? | return ← m.replaceTargetDefEq target
  let motive ← withLocalDeclD `P (← inferType inner) fun P => do
    mkLambdaFVars #[P] (mkAppN ty.getAppFn (args.set! 2 (← mk P)))
  m.replaceTargetEq target (← mkCongrArg motive h)

/-- A rule about `c; s` (its hypothesis `h` the judgment about `c`) matched with a goal: the
goal split before its last statement, the rule applied to metavariables, and those by name. -/
structure EventRule where
  goal : MVarId
  proof : Lean.Expr
  arg : Name → MetaM Lean.Expr

/-- Match the rule `lem` with the goal `g`, split before its last statement.  Nothing is
assigned yet but the split (`EventRule.close`); `none`, the state restored, if the rule does not
fit. -/
def openEventRule (lem : Name) (g : MVarId) : MetaM (Option EventRule) := do
  let s ← saveState
  let g ← Judgment.onStmt (HoareSplit.splitSeq 1) g
  let r ← g.withContext do
    let c ← mkConstWithFreshMVarLevels lem
    let (ms, _, ty) ← forallMetaTelescope (← inferType c)
    let names := (← inferType c).getForallBinderNames
    let arg (n : Name) : MetaM Lean.Expr := do
      let some i := names.findIdx? (· == n) | throwError "no argument `{n}` in `{lem}`"
      return ms[i]!
    unless ← isDefEq ty (← g.getType) do return none
    return some { goal := g, proof := mkAppN c ms, arg := arg : EventRule }
  if r.isNone then s.restore
  return r

/-- Apply the matched rule: the new goal is its hypothesis `h`, tagged `judgment`. -/
def EventRule.close (r : EventRule) : MetaM MVarId := do
  r.goal.assign r.proof
  let m := (← r.arg `h).mvarId!
  m.setTag `judgment
  return m

/-- EC's `call H`, `H : islossless f`, on an event reached with probability `1`
(`phoareStmt_call_lossless_eq_one`). -/
def eventCall (h : Lean.Expr) (g : MVarId) : MetaM (Option MVarId) := do
  let some g ← foldEvent g | return none
  let s ← saveState
  let some r ← openEventRule ``phoareStmt_call_lossless_eq_one g | return none
  unless ← isDefEq (← r.arg `hp) h do
    s.restore; return none
  return some (← simpEvent (← r.close))

/-- EC's pHL `rnd` on an event reached with probability `1`
(`phoareStmt_rnd_lossless_eq_one`). -/
def eventRnd (g : MVarId) : MetaM (Option MVarId) := do
  let some g ← foldEvent g (one := true) | return none
  let some r ← openEventRule ``phoareStmt_rnd_lossless_eq_one g | return none
  return some (← simpEvent (← r.close))

/-- EC's `auto` on `phoare[ c : P ==> Q ] = 1`, `Q` an event: backwards over the code to the
last call (an assignment or a conditional by `wp`, a sampling by `rnd`), the judgment an event
throughout; `skip` when the code is used up.  `false` if the goal is not such a judgment. -/
def eventAuto : TacticM Bool := do
  let some g ← boundOne (← getMainGoal) | return false
  let some g ← foldEvent g | return false
  replaceMainGoal [g]
  for _ in [0:1000] do
    let g ← getMainGoal
    let some g ← foldEvent g (one := true) | break
    replaceMainGoal [g]
    let ty ← instantiateMVars (← g.getType)
    match ← ECSim.lastKind (ty.getArg! 1) with
    | .skip | .call | .loop => break
    | .sample =>
      let some g ← eventRnd g | break
      replaceMainGoal [g]
    | _ =>
      let s ← saveState
      try replaceMainGoal [← Judgment.wpOne g none]
      catch _ => s.restore; break
  let g ← getMainGoal
  let some g ← foldEvent g (one := true) | return true
  let ty ← instantiateMVars (← g.getType)
  unless (← ECSim.lastKind (ty.getArg! 1)) == .skip do
    replaceMainGoal [g]
    return true
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``phoareStmt_skip_event)
  let [g] := gs | throwError "phoare_auto: `phoareStmt_skip_event` left {gs.length} goals"
  let g ← g.withContext do
    g.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← g.getType)))
  replaceMainGoal [← TacticMisc.generalizeReadsOr "phoare_auto" g]
  return true

end PHoareRnd

open Lean Meta Elab Tactic PHoareSeq PHoareWp in
/-- **EC's pHL `rnd E`** on an exact bound, `phoare[ c; x <$ d : P ==> Q ] = r`: the goal becomes
`phoare[ c : P ==> mu d E = r ∧ ∀ v ∈ d, (E v ↔ Q v) ] = 1` (`phoareStmt_rnd_eq`).  `E` is a
predicate on the sampled value and may read the program's variables (`pred1 §b'`).

**EC's `rnd`** (no event: `rnd predT`), on `phoare[ c; x <$ d : P ==> Q ] = 1`: the goal becomes
`phoare[ c : P ==> is_lossless d ∧ ∀ v ∈ d, Q v ] = 1` (`phoareStmt_rnd_lossless_eq_one`). -/
syntax (name := phoareRndTac) "phoare_rnd" (ppSpace colGt term:max)? : tactic

open Lean Meta Elab Tactic PHoareSeq PHoareWp in
elab_rules : tactic
  | `(tactic| phoare_rnd) => do
    let g ← getMainGoal
    let some g ← PHoareRnd.boundOne g
      | throwError "phoare_rnd: not `phoare[ c; x <$ d : P ==> Q ] = 1`{indentExpr (← g.getType)}"
    let some g ← PHoareRnd.eventRnd g
      | throwError "phoare_rnd: not `phoare[ c; x <$ d : P ==> Q ] = 1` with `Q` an event\
          {indentExpr (← g.getType)}"
    replaceMainGoal [g]
  | `(tactic| phoare_rnd $E:term) => do
    let g₀ ← getMainGoal
    let g := (← PHoareRnd.foldEvent g₀).getD g₀
    let some r ← (do
        match ← PHoareRnd.openEventRule ``phoareStmt_rnd_eq_ofReal g with
        | some r => pure (some r)
        | none => PHoareRnd.openEventRule ``phoareStmt_rnd_eq g)
      | throwError "phoare_rnd: not `phoare[ c; x <$ d : P ==> Q ] = r` with `Q` an event and \
          `r` a constant{indentExpr (← g₀.getType)}"
    -- the event is read against the goal with its sampling
    replaceMainGoal [r.goal]
    let Ee ← r.goal.withContext do
      let α ← instantiateMVars (← r.arg `α)
      elabGoalFunction E (← mkArrow α (mkSort Level.zero))
    unless ← isDefEq (← r.arg `E) Ee do throwError "phoare_rnd: the event does not fit"
    let m ← r.close
    -- the condition as the notation shows it (the reads through the sampling's write), under
    -- the indicator: it stays one event (the bound is kept as it is written)
    let m ← PHoareRnd.simpEvent m (some (← instantiateMVars (← r.arg `r)))
    replaceMainGoal [m]

open Lean Meta Elab Tactic PHoareWp in
/-- **EC's `call H`** with `H : islossless f` on `phoare[ c; x <@ f(a) : P ==> Q ] = 1`, `Q` an
event: the goal becomes `phoare[ c : P ==> ∀ result, Q ] = 1`
(`phoareStmt_call_lossless_eq_one`).  Other goals and judgments go to `phoare_call` of
`Logic/PHoareWp.lean`. -/
elab_rules : tactic
  | `(tactic| phoare_call $h:term) => withMainContext do
    let s ← saveState
    let g ← getMainGoal
    let some g ← PHoareRnd.boundOne g | throwUnsupportedSyntax
    let he ← try elabTerm h none catch _ => (do s.restore; throwUnsupportedSyntax)
    let hty ← whnfR (← instantiateMVars (← inferType he))
    unless hty.isAppOf ``Procedure.IsLossless && !he.hasExprMVar do
      s.restore; throwUnsupportedSyntax
    let some g ← PHoareRnd.eventCall he g | (do s.restore; throwUnsupportedSyntax)
    replaceMainGoal [g]

open Lean Meta Elab Tactic in
/-- **EC's `auto`** on `phoare[ c : P ==> Q ] = 1`, `Q` an event (`PHoareRnd.eventAuto`): the
goal `P → Q'`, `Q'` with a conjunct `is_lossless d` and a quantifier over the support for each
sampling.  Other judgments go to `phoare_auto` of `Logic/ECAuto.lean`. -/
elab_rules : tactic
  | `(tactic| phoare_auto) => do
    let s ← saveState
    unless ← PHoareRnd.eventAuto do
      s.restore; throwUnsupportedSyntax
    -- what EC's `auto` closes by itself
    evalTactic (← `(tactic| try (intros; trivial)))

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

-- EC's hints `random` of its libraries: the coin, the uniform distribution, the words
attribute [ec_random] EC.dbool_ll EC.uniform_ll EC.BitWord.dunifin_ll

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
      -- an assignment, or a sampling from a lossless distribution: the uniform one (its mass,
      -- a sum of `1 / card`), one with a hint `ec_random` (EC's `random`), or a hypothesis
      let hints ← (← labelled `ec_random).mapM fun l =>
        `(Lean.Parser.Tactic.tacticSeq| exact (EC.is_lossless_iff_expected _).mp $(mkIdent l))
      evalTactic (← `(tactic| first
        | (phoare_auto; done)
        | (phoare_auto; intros; exact ENNReal.sum_one_div_card_eq_one _)
        | (phoare_auto; intros
           first
             | exact (EC.is_lossless_iff_expected _).mp (by assumption)
             $[| $hints]*)
        | fail "islossless: cannot show that a sampling is lossless (EC's hint `random`: tag \
            the lemma `is_lossless d` with `ec_random`)"))
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
procedures it calls are.  On `phoare[ c : P ==> true ] = 1` (and on `islossless M.f`): a call of
a concrete procedure is opened in turn; one goal `islossless p` per call of an abstract one, the
last call first (EC's order). -/
syntax (name := islosslessTac) "islossless" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic | `(tactic| islossless) => do
  let g ← getMainGoal
  if (← instantiateMVars (← g.getType)).cleanupAnnotations.isAppOf ``Procedure.IsLossless then
    evalTactic (← `(tactic| phoare_proc))
  let rest := (← getGoals).drop 1
  setGoals [← getMainGoal]
  let calls ← PHoareRnd.islosslessLoop 64 #[]
  -- a concrete callee is lossless by its own code (EC goes into it); an abstract one stays
  let mut out : Array MVarId := #[]
  for c in calls do
    let s ← saveState
    try
      setGoals [c]
      evalTactic (← `(tactic| islossless))
      out := out ++ (← getGoals).toArray
    catch _ =>
      s.restore
      out := out.push c
  setGoals (out.toList ++ rest)

end GaudisCrypt
