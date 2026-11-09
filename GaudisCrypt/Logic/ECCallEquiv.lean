import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECCallOneSided

/-!
# EasyCrypt's relational `call (: P ==> Q)` and `exfalso`

    equiv_call (_ : P ==> Q)    -- EC's `call (: P ==> Q)`: the callees' judgment, a new goal
    equiv_exfalso               -- EC's `exfalso`: the precondition is contradictory

EC's `call (: P ==> Q)` on the last statements `x₁ <@ M₁(e₁)` and `x₂ <@ M₂(e₂)` of the two
sides asks for the judgment `equiv[ M₁ ~ M₂ : P ==> Q ]` (first goal), and before the calls for
`P` at the arguments and, for every results and globals `Q` relates, the postcondition — where
what the callees do not touch keeps its value (EC's memories past a call).  That frame is found
as EC finds it: the variables and `glob` regions the postcondition reads that a callee stays out
of (`fp_disjoint`, `Module.Proc.frame_lens`, `Module.Proc.frame_glob`); the rule is
`prhlStmt_seq_call_frame`.
-/

namespace GaudisCrypt

open GaudisCrypt.Lib.RO.Instantiate

/-- **EC's `call (: P ==> Q)`**, with each callee's frame: the callees' runs coupled by `h`; the
postcondition for every results and globals `h` relates that are in each side's frame of its
globals before the call. -/
theorem prhlStmt_seq_call_frame {sig₁ sig₂ : ProcedureSignature} {M₁ : Module.Proc sig₁}
    {M₂ : Module.Proc sig₂}
    {P : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop}
    {Q : sig₁.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop}
    (h : prhlProc P M₁.procedure M₂.procedure Q)
    {Fr₁ Fr₂ : VariableAssignment → VariableAssignment → Prop} (hFr₁ : M₁.Frame Fr₁)
    (hFr₂ : M₂.Frame Fr₂) {x₁ : Setter sig₁.ret ProgramState}
    {e₁ : Getter sig₁.ParamType ProgramState} {x₂ : Setter sig₂.ret ProgramState}
    {e₂ : Getter sig₂.ParamType ProgramState} {A B : ProgramState → ProgramState → Prop}
    {s₁ s₂ : Stmt}
    (hpre : prhlStmt A s₁ s₂ fun σ₁ σ₂ => P (e₁.get σ₁) σ₁.globals (e₂.get σ₂) σ₂.globals ∧
      ∀ r₁ g₁ r₂ g₂, Q r₁ g₁ r₂ g₂ → Fr₁ σ₁.globals g₁ → Fr₂ σ₂.globals g₂ →
        B (x₁.set r₁ (ProgramState.globalL.set g₁ σ₁))
          (x₂.set r₂ (ProgramState.globalL.set g₂ σ₂))) :
    prhlStmt A (.seq s₁ (Stmt.call x₁ M₁.procedure e₁)) (.seq s₂ (Stmt.call x₂ M₂.procedure e₂))
      B := by
  refine prhlStmt_seq (B := fun σ₁ σ₂ => _) ?_ hpre
  intro σ₁ σ₂ ⟨hA, hB⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := h (e₁.get σ₁) (e₂.get σ₂) σ₁.globals σ₂.globals hA
  have hμ₁ : μ.satisfies (fun w => Fr₁ σ₁.globals w.1.2) :=
    coupling_satisfies_fst (by rw [hm1]; exact hFr₁ _ _)
  have hμ₂ : μ.satisfies (fun w => Fr₂ σ₂.globals w.2.2) :=
    coupling_satisfies_snd (by rw [hm2]; exact hFr₂ _ _)
  refine ⟨μ >>= fun w => pure (((), x₁.set w.1.1 (ProgramState.globalL.set w.1.2 σ₁)),
    ((), x₂.set w.2.1 (ProgramState.globalL.set w.2.2 σ₂))), ?_, ?_, ?_⟩
  · refine SubProbability.marginal_fst_eq fun F => ?_
    rw [SubProbability.expected_map, SubProbability.expected_fst_of_marginal hm1
      (fun r => F ((), x₁.set r.1 (ProgramState.globalL.set r.2 σ₁))),
      programDenotation_call_apply, SubProbability.expected_hbind]
    simp only [expected_pure]
  · refine SubProbability.marginal_snd_eq fun F => ?_
    rw [SubProbability.expected_map, SubProbability.expected_snd_of_marginal hm2
      (fun r => F ((), x₂.set r.1 (ProgramState.globalL.set r.2 σ₂))),
      programDenotation_call_apply, SubProbability.expected_hbind]
    simp only [expected_pure]
  · exact SubProbability.satisfies_bind _ fun w hw => SubProbability.satisfies_pure _ _
      (hB _ _ _ _ (hsat w hw) (hμ₁ w hw) (hμ₂ w hw))

/-- **EC's `exfalso`** on a procedure judgment: a contradictory precondition. -/
theorem prhlProc_exfalso {sig₁ sig₂ : ProcedureSignature} {p₁ : Procedure sig₁}
    {p₂ : Procedure sig₂}
    {A : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop}
    {B : sig₁.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop}
    (h : ∀ a₁ g₁ a₂ g₂, A a₁ g₁ a₂ g₂ → False) : prhlProc A p₁ p₂ B :=
  fun a₁ a₂ g₁ g₂ hA => (h a₁ g₁ a₂ g₂ hA).elim

/-- **EC's `exfalso`** on a statement judgment: a contradictory precondition. -/
theorem prhlStmt_exfalso {A B : ProgramState → ProgramState → Prop} {c₁ c₂ : Stmt}
    (h : ∀ σ₁ σ₂, A σ₁ σ₂ → False) : prhlStmt A c₁ c₂ B :=
  fun σ₁ σ₂ hA => (h σ₁ σ₂ hA).elim

namespace ECCallEquiv

open Lean Meta Elab Tactic

/-- The module `M` of the last statement `x <- call M.procedure (e)` of `s`. -/
def lastCallee (s : Lean.Expr) : MetaM Lean.Expr := do
  let st ← TacticMisc.openStmt s
  let last ← if st.isAppOfArity ``StmtWithHoles.seq 3 then TacticMisc.openStmt (st.getArg! 2)
    else pure st
  unless last.isAppOf ``Stmt.call || last.isAppOf ``StmtWithHoles.call do
    throwError "equiv_call: the last statement is not a call{indentExpr last}"
  let p := last.getArg! (last.getAppNumArgs - 2)
  unless p.isAppOf ``Module.Proc.procedure do
    throwError "equiv_call: the callee is not a module's procedure{indentExpr p}"
  return p.appArg!

/-- `t` elaborates, with no error and no `sorry`; the state is restored if not. -/
def elabClean (t : Term) : TermElabM (Option Lean.Expr) := do
  let s ← saveState
  let log ← Core.getMessageLog
  try
    let e ← Term.withoutErrToSorry do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    if e.hasSorry || e.hasMVar || (← Core.getMessageLog).hasErrors then
      s.restore; Core.setMessageLog log; return none
    Core.setMessageLog log
    return some e
  catch _ => s.restore; Core.setMessageLog log; return none

/-- The frame of the callee `M` for the global variables `xs` and the regions `Rs` a condition
reads: those `M` stays out of (EC's call keeps them), combined with `Module.Proc.frame_and`. -/
def frameFor (M : Lean.Expr) (xs Rs : Array Lean.Expr) : TermElabM Lean.Expr := do
  let MS ← Term.exprToSyntax M
  let mut parts : Array Lean.Expr := #[]
  for x in xs do
    let XS ← Term.exprToSyntax x
    if let some e ← elabClean (← `(Module.Proc.frame_lens (M := $MS) $XS (by fp_disjoint))) then
      parts := parts.push e
  for R in Rs do
    let RS ← Term.exprToSyntax R
    if let some e ← elabClean
        (← `(Module.Proc.frame_glob (M := $MS) $RS (by fp_finite) (by fp_disjoint))) then
      parts := parts.push e
    else if let some X ← TacticMisc.regionLens? R then
      let XS ← Term.exprToSyntax X
      if let some e ← elabClean (← `(Module.Proc.frame_region (M := $MS) $XS (R := $RS)
          (by first | rfl | simp only [Footprint.lens_pair]) (by fp_disjoint))) then
        parts := parts.push e
  match parts.back? with
  | none => mkAppM ``Module.Proc.frame_true #[M]
  | some last => parts.pop.foldrM (fun p acc => mkAppM ``Module.Proc.frame_and #[p, acc]) last

end ECCallEquiv

end GaudisCrypt

/-- **EC's `call (: P ==> Q)`**: see the module docstring.  Goals: the callees' judgment
(`callee`), then the code before the calls. -/
syntax (name := equivCallSpec) "equiv_call" " (" "_" " : " term " ==> " term ")" : tactic

open Lean Meta Elab Tactic GaudisCrypt PRHLWp ECCallEquiv in
elab_rules : tactic
  | `(tactic| equiv_call (_ : $P ==> $Q)) => withMainContext do
    let g ← getMainGoal
    let _ ← prhlGoal g "equiv_call"
    let g ← HoareSplit.hoareSplit 1 g
    let (hJ, gPre) ← g.withContext do
      let ty ← prhlGoal g "equiv_call"
      let M₁ ← lastCallee (ty.getArg! 1)
      let M₂ ← lastCallee (ty.getArg! 2)
      -- the callees' judgment, its conditions as `equiv[ M₁ ~ M₂ : P ==> Q ]` reads them
      let j ← Term.elabTerm (← `(equiv[ $(← Term.exprToSyntax M₁) ~ $(← Term.exprToSyntax M₂) :
        $P ==> $Q ])) none
      Term.synthesizeSyntheticMVarsNoPostponing
      let j ← instantiateMVars j
      let hJ ← mkFreshExprSyntheticOpaqueMVar j `callee
      -- the frames: what the postcondition reads that each callee stays out of
      let B := ty.getArg! 3
      let (_, gls) ← ECSim.varsOf #[B]
      let Rs ← ECConseqFrame.regionsOf #[B]
      let fr₁ ← frameFor M₁ gls Rs
      let fr₂ ← frameFor M₂ gls Rs
      let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_call_frame
      let (ms, _, concl) ← forallMetaTelescope (← inferType c)
      let names := (← inferType c).getForallBinderNames
      let idx (n : Name) : TacticM Nat := do
        let some i := names.findIdx? (· == n) | throwError "equiv_call: no argument `{n}`"
        return i
      unless ← isDefEq ms[← idx `M₁]! M₁ do throwError "equiv_call: M₁"
      unless ← isDefEq ms[← idx `M₂]! M₂ do throwError "equiv_call: M₂"
      unless ← isDefEq ms[← idx `h]! hJ do
        throwError "equiv_call: the judgment does not fit the callees{indentExpr j}"
      unless ← isDefEq ms[← idx `hFr₁]! fr₁ do throwError "equiv_call: the left frame"
      unless ← isDefEq ms[← idx `hFr₂]! fr₂ do throwError "equiv_call: the right frame"
      unless ← isDefEq concl ty do
        throwError "equiv_call: the call rule does not fit the last statements{indentExpr ty}"
      g.assign (← instantiateMVars (mkAppN c ms))
      let gPre := ms[← idx `hpre]!.mvarId!
      gPre.setKind .syntheticOpaque
      gPre.setTag (← g.getTag)
      pure (hJ.mvarId!, gPre)
    replaceMainGoal [hJ, ← Judgment.simpArg gPre 3 relSimpDecls []]

open Lean Meta Elab Tactic GaudisCrypt in
/-- **EC's `exfalso`** on a relational judgment: the goal is that the precondition is
contradictory, `∀ …, pre → False`. -/
elab "equiv_exfalso" : tactic => withMainContext do
  -- (through a `match` an `intro ⟨a, b⟩` leaves)
  let ty ← whnfR (← instantiateMVars (← getMainTarget))
  if ty.isAppOf ``prhlProc then
    evalTactic (← `(tactic| refine prhlProc_exfalso ?_))
  else if ty.isAppOf ``prhlStmt then
    evalTactic (← `(tactic| refine prhlStmt_exfalso ?_))
  else throwError "equiv_exfalso: not a relational judgment"
  evalTactic (← `(tactic| beta_reduce))
