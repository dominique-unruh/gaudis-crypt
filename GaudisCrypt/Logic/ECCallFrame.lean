import GaudisCrypt.Logic.CallSpec
import GaudisCrypt.Logic.ECCallOneSided
import GaudisCrypt.Lib.EC.Mu

/-!
# EasyCrypt's `call (: P ==> Q)` in a `phoare`, with a frame

    phoare_call (: P ==> Q) / x₁, …, glob A
    hoare_call (: P ==> Q) / x₁, …, glob A

EC's `call (: P ==> Q)` keeps, past the call, what the callee does not touch (EC's `glob`):
the game's event after the call need only follow from `Q` for globals that agree with the ones
before on that.  Here that is a frame (`Module.Proc.Frame`, `Logic/ECCallOneSided.lean`): lenses
outside the callee (`Preimage2.hash` past `FEL(A, F).main`), the `glob` of declared modules.
Upper bounds (`phoareStmt_call_le_frame`).

In a Hoare triple (`hoare_call_wp_frame`) the same frame serves EC's
`rcondt{i} n; first by auto; inline*; auto; conseq (: _ ==> true); auto`: the condition after a
call that does not write what it reads is `hoare_call (: True ==> True) / x; ec_auto`.
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

/-- A triple about a module's procedure also says what the procedure keeps (a frame `Fr` of the
module), for the globals `g₀` it starts from. -/
theorem hoareProc_and_frame {sig} {M : Module.Proc sig}
    {P : sig.ParamType → VariableAssignment → Prop} {Q : sig.ret → VariableAssignment → Prop}
    {Fr : VariableAssignment → VariableAssignment → Prop} (hFr : M.Frame Fr)
    (hp : hoareProc P M.procedure Q) (g₀ : VariableAssignment) :
    hoareProc (fun a g => P a g ∧ g = g₀) M.procedure (fun r g' => Q r g' ∧ Fr g₀ g') := by
  rw [hoareProc_iff_wp] at hp ⊢
  rintro a g ⟨hP, rfl⟩
  have h := hp a g hP
  simp only [ProgramDenotation.wp] at h ⊢
  refine (SubProbability.expected_congr_satisfies (hFr a g) fun x hx => ?_).trans h
  by_cases hQ : Q x.1 x.2 <;> simp [Set.indicator, hQ, hx]

/-- **EC's `call (: P ==> Q)` in a Hoare triple, with EC's frame**: the postcondition after the
call for every result and every globals that `Q` allows *and that are in the frame `Fr` of the
current ones* (what the callee does not write keeps its value). -/
theorem hoare_call_wp_frame {sig} (x : Setter sig.ret ProgramState)
    (M : Module.Proc sig) (args : Getter sig.ParamType ProgramState)
    {P : sig.ParamType → VariableAssignment → Prop} {Q : sig.ret → VariableAssignment → Prop}
    {Fr : VariableAssignment → VariableAssignment → Prop} (hFr : M.Frame Fr)
    (hp : hoareProc P M.procedure Q) (B : ProgramState → Prop) :
    hoareStmt
      (fun σ => P (args.get σ) σ.globals ∧
        ∀ r g, Fr σ.globals g → Q r g → B (x.set r (ProgramState.globalL.set g σ)))
      (Stmt.call x M.procedure args) B := by
  rintro σ ⟨hP, hQ⟩
  exact hoare_call_wp x M.procedure args (hoareProc_and_frame hFr hp σ.globals) B σ
    ⟨⟨hP, rfl⟩, fun r g ⟨hq, hf⟩ => hQ r g hf hq⟩

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

open Lean Meta Elab Tactic GaudisCrypt CallSpec HoareWp ECCallOneSided in
/-- **EC's `call (: P ==> Q)`** in a Hoare triple, past what the callee does not touch: the frame
`x₁, …, glob A` (as `phoare_call (: P ==> Q) / …`).  Goals: the callee's triple (`spec`; the
trivial one, `True ==> True`, is closed), then the code before the call.  EC's
`rcondt{i} n; first by auto; inline*; auto; conseq (: _ ==> true); auto` on a call that does not
write what the condition reads is `hoare_call (: True ==> True) / x; ec_auto`. -/
elab "hoare_call" " (" ": " P:term " ==> " Q:term ")" " / " xs:term,+ : tactic => withMainContext do
  let g ← getMainGoal
  let p ← withoutModifyingState do
    let g ← HoareSplit.hoareSplit 1 g
    let gq :: _ ← g.apply (← mkConstWithFreshMVarLevels ``hoare_seq)
      | throwError "hoare_call: `hoare_seq` does not apply"
    calleeOf ``hoare_call_wp (← instantiateMVars (← gq.getType))
  let spec ← elabSpec (← `(hoare[ $(← Term.exprToSyntax p) : $P ==> $Q ]))
  let h ← specGoal spec `spec
  let g ← HoareSplit.hoareSplit 1 g
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``hoare_seq)
  let gq :: gp :: _ := gs | throwError "hoare_call: `hoare_seq` left {gs.length} goals"
  let rest ← gq.withContext do
    let fr ← frameTerm xs.getElems
    Tactic.run gq (evalTactic (← `(tactic|
      exact hoare_call_wp_frame _ _ _ $fr $(← Term.exprToSyntax h) _)))
  unless rest.isEmpty do throwError "hoare_call / frame: the rule left {rest.length} goals"
  gp.setTag (← g.getTag)
  -- the trivial triple
  let specs ← try
      let [] ← h.mvarId!.apply (← mkConstWithFreshMVarLevels ``hoareProc_true) | failure
      pure []
    catch _ => pure [h.mvarId!]
  replaceMainGoal (specs ++ [← simpReads gp])
