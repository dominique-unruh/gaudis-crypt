import GaudisCrypt.Logic.SyntacticFrame
import GaudisCrypt.Logic.PHoare

/-!
# The syntactic frame for expectations: concrete supermartingales

EasyCrypt's `fel` bounds a bad event through the oracles: each call increases the potential (the
bad event plus what remains to be paid) by at most nothing in expectation.  For a concrete oracle
that changes the potential's state only through a few sampling procedures (`Gcol.sample_c`), the
step lemma of those procedures is all that matters: every other write keeps the state.

`StmtWithHoles.ExpDecr G φ s` says that of `s`: each write keeps `G` of the globals, and each call
either is to a procedure that does not increase `φ ∘ G` in expectation or has a body of which
`ExpDecr` holds again.  `Stmt.ewp_le_of_expDecr` concludes that `s` does not increase `φ ∘ G`
(loops with `φ ∘ G` as the invariant).  The tactic `exp_decr` reduces an `ExpDecr` goal to the
single writes as `writes_keep` does, closing a call by a step lemma from the context when one
applies.
-/

namespace GaudisCrypt

/-- Each write of the statement keeps `G` of the globals, and each call either is to a procedure
that does not increase `φ ∘ G` in expectation or satisfies `ExpDecr` itself. -/
def StmtWithHoles.ExpDecr {β : Type*} (G : VariableAssignment → β) (φ : β → ENNReal)
    {h : HoleSigs} : StmtWithHoles h → Prop
  | .skip => True
  | .sample x _ => ∀ v σ, G (x.set v σ).globals = G σ.globals
  | .call' (sig := sig) x ns hl hn body r _ => (∀ v σ, G (x.set v σ).globals = G σ.globals) ∧
      ((∀ a g, Procedure.ewp (⟨ns, hl, hn, body, r⟩ : Procedure sig) a
          (fun _ g' => φ (G g')) g ≤ φ (G g)) ∨ body.ExpDecr G φ)
  | .hole _ _ _ => False
  | .seq s t => s.ExpDecr G φ ∧ t.ExpDecr G φ
  | .ifThenElse _ t e => t.ExpDecr G φ ∧ e.ExpDecr G φ
  | .while _ t => t.ExpDecr G φ

/-- A procedure's expectation, as its body's from the initial locals. -/
theorem Procedure.ewp_eq_body {sig} (p : Procedure sig) (a : sig.ParamType)
    (F : VariableAssignment → ENNReal) (g : VariableAssignment) :
    p.ewp a (fun _ g' => F g') g =
      Stmt.ewp p.body (fun τ => F τ.globals) ⟨g, p.initLocals a⟩ := by
  simp only [Procedure.ewp, Stmt.ewp, ProgramDenotation.wp, procedureDenotation,
    SubProbability.expected_hbind, expected_pure]

/-- **The syntactic frame for expectations**: a statement satisfying `ExpDecr G φ` does not increase
the expectation of `φ ∘ G`. -/
theorem Stmt.ewp_le_of_expDecr {β : Type*} (G : VariableAssignment → β) (φ : β → ENNReal) :
    ∀ s : Stmt, StmtWithHoles.ExpDecr G φ s →
      ∀ σ, s.ewp (fun τ => φ (G τ.globals)) σ ≤ φ (G σ.globals)
  | .skip, _, σ => by
      show Stmt.ewp StmtWithHoles.skip _ σ ≤ _
      rw [Stmt.ewp_skip]
  | .sample x e, hs, σ => by
      have hs' : ∀ v σ, G (x.set v σ).globals = G σ.globals := hs
      have : Stmt.ewp (StmtWithHoles.sample x e) (fun τ => φ (G τ.globals)) σ =
          Stmt.ewp (StmtWithHoles.sample x e) (fun _ => φ (G σ.globals)) σ := by
        rw [Stmt.ewp_sample, Stmt.ewp_sample]
        simp only [hs']
      rw [this]
      exact Stmt.ewp_const_le _ _ _
  | .call' (sig := sig) x ns hl hn body r p, hs, σ => by
      obtain ⟨hx, hc⟩ := (show _ ∧ _ from hs)
      show Stmt.ewp (Stmt.call x (⟨ns, hl, hn, body, r⟩ : Procedure sig) p) _ σ ≤ _
      rw [Stmt.ewp_call]
      have hfun : (fun (v : sig.ret) (gl : VariableAssignment) =>
          φ (G (x.set v (ProgramState.globalL.set gl σ)).globals)) = fun _ gl => φ (G gl) := by
        funext v gl
        rw [hx v]
        rfl
      simp only [hfun]
      rcases hc with hq | hb
      · exact hq _ _
      · rw [Procedure.ewp_eq_body]
        exact Stmt.ewp_le_of_expDecr G φ body hb _
  | .hole n _ _, hs, _ => nomatch n
  | .seq s t, hst, σ => by
      obtain ⟨hs, ht⟩ := (show _ ∧ _ from hst)
      show Stmt.ewp (StmtWithHoles.seq s t) _ σ ≤ _
      rw [Stmt.ewp_seq]
      exact (Stmt.ewp_mono s (fun τ => Stmt.ewp_le_of_expDecr G φ t ht τ) σ).trans
        (Stmt.ewp_le_of_expDecr G φ s hs σ)
  | .ifThenElse c t e, hte, σ => by
      obtain ⟨ht, he⟩ := (show _ ∧ _ from hte)
      show Stmt.ewp (StmtWithHoles.ifThenElse c t e) _ σ ≤ _
      rw [Stmt.ewp_ifThenElse]
      dsimp only
      split
      · exact Stmt.ewp_le_of_expDecr G φ t ht σ
      · exact Stmt.ewp_le_of_expDecr G φ e he σ
  | .while c t, ht, σ =>
      Stmt.ewp_while_le _ _ (fun τ _ => Stmt.ewp_le_of_expDecr G φ t ht τ) (fun _ _ => le_rfl) σ
termination_by s => s.depth
decreasing_by all_goals simp [StmtWithHoles.depth]; try omega

/-- `Stmt.ewp_le_of_expDecr` for a procedure. -/
theorem Procedure.ewp_le_of_expDecr {sig} {β : Type*} (G : VariableAssignment → β)
    (φ : β → ENNReal) (p : Procedure sig) (hp : StmtWithHoles.ExpDecr G φ p.body)
    (a : sig.ParamType) (g : VariableAssignment) :
    p.ewp a (fun _ g' => φ (G g')) g ≤ φ (G g) := by
  rw [Procedure.ewp_eq_body]
  exact Stmt.ewp_le_of_expDecr G φ p.body hp _

open Lean Meta Elab Tactic in
/-- Split a goal `StmtWithHoles.ExpDecr G φ s` down to its single writes, as `stmtPredSplit` does
for `WritesKeep`; at a call, first try to close the step-lemma alternative by a hypothesis. -/
partial def expDecrSplit (g : MVarId) (fuel : Nat := 256) : TacticM (List MVarId) := do
  if fuel == 0 then return [g]
  let ty ← whnf (← instantiateMVars (← g.getType))
  if ty.isAppOfArity ``And 2 then
    let gs ← g.apply (mkConst ``And.intro [])
    return (← gs.mapM (expDecrSplit · (fuel - 1))).flatten
  else if ty.isAppOfArity ``Or 2 then
    let s ← saveState
    try
      let [g'] ← g.apply (mkConst ``Or.inl []) | throwError "Or.inl"
      -- the callee is spelled out field by field (`⟨p.parameterNames, …, p.body, p.return_val⟩`):
      -- fold it back to `p` (eta), then look for a step lemma about `p` at reducible transparency
      -- (comparing different module procedures by unfolding them is expensive)
      let ty ← instantiateMVars (← g'.getType)
      let ty' := ty.replace fun e =>
        if e.isAppOfArity ``ProcedureWithHoles.mk 7 then
          match e.getArg! 5 with
          | .app (.app (.app (.const ``ProcedureWithHoles.body _) _) _) p => some p
          | .proj _ 3 p => some p
          | _ => none
        else none
      let g' ← g'.replaceTargetDefEq ty'
      withReducible g'.assumption
      return []
    catch _ =>
      s.restore
      let [g'] ← g.apply (mkConst ``Or.inr []) | throwError "Or.inr"
      expDecrSplit g' (fuel - 1)
  else if ty.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return []
  else if ty.isAppOf ``StmtWithHoles.ExpDecr then
    let some p := ty.find? (·.isAppOf ``Module.Proc.procedure)
      | throwError "stuck at{indentExpr ty}"
    let r ← Flatten.unfoldProcedure p
    let g ← g.replaceTargetDefEq ty
    let g ← match r.proof? with
      | none => g.replaceTargetDefEq (ty.replace fun e => if e == p then some r.expr else none)
      | some h => do
        let res ← g.rewrite ty h
        g.replaceTargetEq res.eNew res.eqProof
    expDecrSplit g (fuel - 1)
  else
    return [← g.replaceTargetDefEq ty]

open Lean Elab Tactic in
/-- Close `∀ v σ, L.get ((x.set v σ).globals) = L.get σ.globals` (a write to a global lens `X`) by
`touched_set_of_le_compl` with a hypothesis `X.footprint ≤ (L.footprint)ᶜ` from the context, trying
the hypotheses one by one (the written lens is only known once the term is elaborated). -/
elab "exp_decr_write" : tactic => do
  evalTactic (← `(tactic| intro v σ))
  evalTactic (← `(tactic| refine (Lens.footprint_touched_getter_eq_iff _ _ _).mp ?_))
  let g ← getMainGoal
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let s ← saveState
    try
      evalTactic (← `(tactic| exact touched_set_of_le_compl $(mkIdent d.userName) v σ.globals))
      return
    catch _ => s.restore
  throwError "exp_decr_write: no footprint hypothesis applies"

open Lean Elab Tactic in
/-- `exp_decr`: on a goal `StmtWithHoles.ExpDecr G φ s`, the conditions on the single writes of
`s`, callees included; a call is closed by a step lemma in the context when one matches.  Writes to
local variables are closed by `rfl`, writes to a global lens `X` (for `G = L.get`) by
`touched_set_of_le_compl` with a hypothesis `X.footprint ≤ (L.footprint)ᶜ` from the context
(`exp_decr_write`). -/
elab "exp_decr" : tactic => do
  let gs ← expDecrSplit (← getMainGoal)
  replaceMainGoal gs
  evalTactic (← `(tactic| all_goals first
    | exact fun _ _ => rfl
    | exp_decr_write
    | skip))

end GaudisCrypt
