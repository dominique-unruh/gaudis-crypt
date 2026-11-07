import GaudisCrypt.Logic.CallSpec
import GaudisCrypt.Logic.ECCallOneSided
import GaudisCrypt.Lib.EC.Mu

/-!
# EasyCrypt's `call (: P ==> Q)` in a `phoare`, with a frame

    phoare_call (: P ==> Q) / x₁, …, glob A

EC's `call (: P ==> Q)` keeps, past the call, what the callee does not touch (EC's `glob`):
the game's event after the call need only follow from `Q` for globals that agree with the ones
before on that.  Here that is a frame (`Module.Proc.Frame`, `Logic/ECCallOneSided.lean`): lenses
outside the callee (`Preimage2.hash` past `FEL(A, F).main`), the `glob` of declared modules.
Upper bounds (`phoareStmt_call_le_frame`).
-/

namespace GaudisCrypt

open Classical in
/-- **EC's `call (: P ==> Q)`** in an upper bound, with a frame `Fr` the callee keeps: the event
after the call bounded by the callee's for the globals in the frame of the ones before. -/
theorem phoareStmt_call_le_frame {sig} {A : ProgramState → Prop} {pre : Stmt}
    {x : Setter sig.ret ProgramState} {M : Module.Proc sig} {a : Getter sig.ParamType ProgramState}
    {g r : ProgramState → ENNReal} {P : sig.ParamType → VariableAssignment → Prop}
    {G : sig.ret → VariableAssignment → ENNReal} {R : sig.ParamType → VariableAssignment → ENNReal}
    {Fr : VariableAssignment → VariableAssignment → Prop} (hFr : M.Frame Fr)
    (h : phoareProc P M.procedure G LE.le R)
    (h' : phoareStmt A pre (fun σ =>
      if P (a.get σ) σ.globals ∧
          ∀ v gl, Fr σ.globals gl → g (x.set v (ProgramState.globalL.set gl σ)) ≤ G v gl
        then R (a.get σ) σ.globals else ⊤) LE.le r) :
    phoareStmt A (.seq pre (Stmt.call x M.procedure a)) g LE.le r := by
  rw [phoareStmt_seq_iff]
  refine phoareStmt_le_of_le h' fun σ => ?_
  rw [Stmt.ewp_call]
  split_ifs with hC
  · refine le_trans ?_ (h _ _ hC.1)
    simp only [Procedure.ewp, ProgramDenotation.wp]
    rw [SubProbability.expected_congr_satisfies (hFr (a.get σ) σ.globals)
      (G := fun u => if Fr σ.globals u.2 then g (x.set u.1 (ProgramState.globalL.set u.2 σ))
        else G u.1 u.2) fun u hu => by simp [hu]]
    refine EC.mu_le fun u => ?_
    show (if _ then _ else _) ≤ _
    split_ifs with hf
    · exact hC.2 _ _ hf
    · exact le_rfl
  · exact le_top

/-- **EC's `call H` (`H : islossless M`) in a `phoare … = 1`**, with a frame `Fr` the callee
keeps: the event `B` after the call holds with probability `1` when, before it, `B` holds after
the call for every result and every globals in the frame of the current ones. -/
theorem phoareStmt_call_lossless_frame {sig} {A : ProgramState → Prop} {pre : Stmt}
    {x : Setter sig.ret ProgramState} {M : Module.Proc sig} {a : Getter sig.ParamType ProgramState}
    {B : ProgramState → Prop} {Fr : VariableAssignment → VariableAssignment → Prop}
    (hFr : M.Frame Fr) (hll : M.procedure.IsLossless)
    (h' : phoareStmt A pre (fun σ => indicatorE (∀ v gl, Fr σ.globals gl →
        B (x.set v (ProgramState.globalL.set gl σ)))) Eq (fun _ => 1)) :
    phoareStmt A (.seq pre (Stmt.call x M.procedure a)) (fun σ => indicatorE (B σ)) Eq
      (fun _ => 1) := by
  rw [phoareStmt_seq_iff]
  intro σ hA
  have hC : ∀ τ, (Stmt.call x M.procedure a).ewp (fun σ => indicatorE (B σ)) τ ≤ 1 := fun τ =>
    (Stmt.ewp_mono _ (fun _ => indicatorE_le_one _) τ).trans (Stmt.ewp_const_le _ 1 τ)
  refine le_antisymm ((Stmt.ewp_mono _ hC σ).trans (Stmt.ewp_const_le _ 1 σ)) ?_
  rw [← h' σ hA]
  refine Stmt.ewp_mono _ (fun τ => ?_) σ
  by_cases h : ∀ v gl, Fr τ.globals gl → B (x.set v (ProgramState.globalL.set gl τ))
  · rw [indicatorE_of h, Stmt.ewp_call]
    have e := hll (a.get τ) τ.globals
    simp only [Procedure.ewp, ProgramDenotation.wp] at e ⊢
    rw [SubProbability.expected_congr_satisfies (hFr (a.get τ) τ.globals)
      (G := fun _ => 1) fun u hu => indicatorE_of (h _ _ hu), e]
  · rw [indicatorE_of_not h]; exact bot_le

end GaudisCrypt

open Lean Meta Elab Tactic GaudisCrypt CallSpec PHoareWp ECCallOneSided in
/-- **EC's `call (: P ==> Q)`** in an upper bound, past what the callee does not touch: the
frame `x₁, …, glob A` (see the module docstring).  Goals: the callee's judgment (`spec`), then
the code before the call. -/
elab "phoare_call" " (" ": " P:term " ==> " Q:term ")" " / " xs:term,+ : tactic =>
    withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let #[_, _, _, ρ, bound] ← phoareParts ty | unreachable!
  unless ρ.isAppOf ``LE.le do throwError "phoare_call / frame: an upper bound"
  let p ← withoutModifyingState do
    calleeOf ``phoareStmt_call_le (← instantiateMVars (← (← phoareSplit 1 g).getType))
  let pT ← Term.exprToSyntax p
  let bound ← whnfR bound
  let .lam _ _ c _ := bound
    | throwError "phoare_call: the goal's bound is not a function of the state"
  if c.hasLooseBVars then throwError "phoare_call: the goal's bound reads the state"
  let spec ← elabSpec (← `(phoare[ $pT : $P ==> $Q ] ≤ ($(← Term.exprToSyntax c))))
  let h ← specGoal spec `spec
  let h' ← normalizeSpec h
  let g ← phoareSplit 1 g
  let g' ← g.withContext do
    let fr ← frameTerm xs.getElems
    let gs ← Tactic.run g (evalTactic (← `(tactic|
      refine phoareStmt_call_le_frame $fr $(← Term.exprToSyntax h') ?_)))
    let [g'] := gs | throwError "phoare_call / frame: the rule left {gs.length} goals"
    pure g'
  g'.setTag (← g.getTag)
  replaceMainGoal [h.mvarId!, ← simpPost g']

open Lean Meta Elab Tactic GaudisCrypt PHoareWp ECCallOneSided in
/-- **EC's `call H`** (`H : islossless M`) in a `phoare … = 1`, past what the callee does not
touch: the frame `x₁, …, glob A` (`phoareStmt_call_lossless_frame`).  Goal: the code before the
call, the event for every result and globals in the frame. -/
elab "phoare_call " h:term:max " / " xs:term,+ : tactic => withMainContext do
  let g ← phoareSplit 1 (← getMainGoal)
  let g' ← g.withContext do
    let fr ← frameTerm xs.getElems
    let gs ← Tactic.run g (evalTactic (← `(tactic|
      refine phoareStmt_call_lossless_frame $fr $h ?_)))
    let [g'] := gs | throwError "phoare_call / frame: the rule left {gs.length} goals"
    pure g'
  g'.setTag (← g.getTag)
  replaceMainGoal [← simpPost g']
