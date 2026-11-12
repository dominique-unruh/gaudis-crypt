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
  -- only this elaboration's messages: errors logged earlier in the file are not this term's
  Core.resetMessageLog
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

open Lean Meta Elab Tactic GaudisCrypt PRHLWp ECCallEquiv in
/-- **EC's `call H`** with `H` a judgment about the two last callees (modules' procedures), with
EC's frame: what each callee does not write keeps its value (as for `equiv_call (_ : P ==> Q)`).
Goal: the code before the calls.  Other uses of `equiv_call H` are left to `Logic/PRHLWp.lean`. -/
elab_rules (kind := GaudisCrypt.PRHLWp.tacticEquiv_call___) : tactic
  | `(tactic| equiv_call $h:term) => withMainContext do
    -- (`equiv_call (_ : …)`: the call forms with an invariant or a specification)
    if let `(term| (_ : $_)) := h then throwUnsupportedSyntax
    let s ← saveState
    let g ← getMainGoal
    let _ ← prhlGoal g "equiv_call"
    let g ← HoareSplit.hoareSplit 1 g
    -- `(goal, none)`: done; `(none, none)`: another use of the syntax (`Logic/PRHLWp.lean`);
    -- `(none, some e)`: the framed rule fails on these callees
    let res ← g.withContext do
      try
        let ty ← prhlGoal g "equiv_call"
        let M₁ ← lastCallee (ty.getArg! 1)
        let M₂ ← lastCallee (ty.getArg! 2)
        -- a functor applied to an abstract module (a parameter of a module type): the frameless
        -- rule (`Logic/PRHLWp.lean`)
        let isApp (M : Lean.Expr) := (M.find? (·.isAppOfArity ``Module.app 6)).isSome
        let abstractIn (M : Lean.Expr) : MetaM Bool := do
          for fv in (Lean.collectFVars {} M).fvarIds do
            if (← whnf (← fv.getType)).isAppOf ``GaudisCrypt.Module then return true
          return false
        if (isApp M₁ && (← abstractIn M₁)) || (isApp M₂ && (← abstractIn M₂)) then
          return (none, none)
        let hJ ← Term.elabTerm h none
        Term.synthesizeSyntheticMVarsNoPostponing
        let hJ ← instantiateMVars hJ
        unless (← whnfR (← inferType hJ)).isAppOf ``prhlProc do return (none, none)
        let B := ty.getArg! 3
        let (_, gls) ← ECSim.varsOf #[B]
        let Rs ← ECConseqFrame.regionsOf #[B]
        let fr₁ ← frameFor M₁ gls Rs
        let fr₂ ← frameFor M₂ gls Rs
        let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_call_frame
        let (ms, _, concl) ← forallMetaTelescope (← inferType c)
        let names := (← inferType c).getForallBinderNames
        let idx (n : Name) : MetaM Nat := do
          let some i := names.findIdx? (· == n) | throwError "equiv_call: no argument `{n}`"
          return i
        unless ← isDefEq ms[← idx `M₁]! M₁ do return (none, none)
        unless ← isDefEq ms[← idx `M₂]! M₂ do return (none, none)
        unless ← isDefEq ms[← idx `h]! hJ do return (none, none)
        unless ← isDefEq ms[← idx `hFr₁]! fr₁ do throwError "the left callee's frame does not fit"
        unless ← isDefEq ms[← idx `hFr₂]! fr₂ do throwError "the right callee's frame does not fit"
        unless ← isDefEq concl ty do
          throwError "the framed call rule does not fit the last statements{indentExpr ty}"
        g.assign (← instantiateMVars (mkAppN c ms))
        let gPre := ms[← idx `hpre]!.mvarId!
        gPre.setKind .syntheticOpaque
        gPre.setTag (← g.getTag)
        return (some gPre, none)
      catch e => return (none, some e)
    match res with
    | (some gPre, _) => replaceMainGoal [← Judgment.simpArg gPre 3 relSimpDecls []]
    | (none, none) => s.restore; throwUnsupportedSyntax
    | (none, some e) =>
      -- the weaker rule, said aloud (`ECReport.fallback`)
      s.restore
      ECReport.fallback "equiv_call" m!"the rule with EC's frame does not apply to these \
        callees; using the rule without a frame (`equiv_call_frameless`: what the callees do \
        not write is not kept)" (some e)
      PRHLWp.equivCallFrameless (some h)

open Lean Meta Elab Tactic GaudisCrypt PRHLWp ECCallEquiv in
/-- **EC's `call (_: ={x₁, …, glob M})` on a concrete callee**, with EC's frame: the callee keeps
`={x₁, …}` (`prhlProc_glob_module`, its footprint inside them), and what it does not write keeps
its value (as for `equiv_call (_ : P ==> Q)`).  Goal: the code before the calls.  Two different
concrete callees: `equiv_call (_ : ={arg, x₁, …} ==> ={res, x₁, …})` (their judgment a goal, as
EC's).  An abstract callee (`D(O)`) is left to the rule of `Logic/ECCallAbstract.lean`. -/
elab_rules (kind := GaudisCrypt.equivCallConcrete) : tactic
  | `(tactic| equiv_call_concrete (_ : ={ $xs:term,* })) => withMainContext do
    let s ← saveState
    let g ← getMainGoal
    let _ ← prhlGoal g "equiv_call"
    let g ← HoareSplit.hoareSplit 1 g
    let concrete ← g.withContext do
      let ty ← prhlGoal g "equiv_call"
      try
        let M₁ ← lastCallee (ty.getArg! 1)
        let M₂ ← lastCallee (ty.getArg! 2)
        let isApp (M : Lean.Expr) := (M.find? (·.isAppOfArity ``Module.app 6)).isSome
        -- an application of a declared (abstract) module: `Logic/ECCallAbstract.lean`'s rule
        let isAbstract (M : Lean.Expr) := (M.find? fun e =>
          e.isAppOfArity ``Module.app 6 && (e.getArg! 4).getAppFn.isFVar).isSome
        if isAbstract M₁ || isAbstract M₂ then return none
        -- two different concrete callees: EC's `={arg, x…} ==> ={res, x…}`, their judgment a goal
        unless ← withReducible (isDefEq M₁ M₂) do return some (ty, M₁, M₂, true)
        -- (an applied functor too: `fp_le` bounds its footprint, `@[fp_bound]`; if it cannot,
        -- the rule fails and the caller falls back to the frameless one)
        let _ := isApp
        return some (ty, M₁, M₂, false)
      catch _ => return none
    let some (ty, M₁, M₂, different) := concrete | do s.restore; throwUnsupportedSyntax
    if different then
      s.restore
      -- (`arg`, `res` unhygienic: the names the conditions give a procedure's argument and result)
      let argI := mkIdent `arg
      let resI := mkIdent `res
      evalTactic (← `(tactic| equiv_call (_ : ={$argI, $xs,*} ==> ={$resI, $xs,*})))
      return
    let Rs ← xs.getElems.mapM fun (t : Term) => match t with
      | `(glob $a) => `(glob_region $a)
      | _ => `(Lens.footprint $t)
    let some last := Rs.back? | throwError "equiv_call: `=\{glob M, x₁, …}`"
    let R ← Rs.pop.foldrM (fun x acc => `($x ⊔ $acc)) last
    let (fr₁, fr₂) ← g.withContext do
      let B := ty.getArg! 3
      let (_, gls) ← ECSim.varsOf #[B]
      let Rs' ← ECConseqFrame.regionsOf #[B]
      pure (← Term.exprToSyntax (← frameFor M₁ gls Rs'),
        ← Term.exprToSyntax (← frameFor M₂ gls Rs'))
    setGoals [g]
    -- (`withoutRecover`: a failing `by fp_le` is an exception here, not an error logged next to
    -- a goal with a `sorry` inside)
    let [gp] ← withoutRecover <| g.withContext <| evalTacticAt (← `(tactic| refine
        prhlStmt_seq_call_frame (prhlProc_glob_module _ (R := $R) (by fp_le)) $fr₁ $fr₂ ?_)) g
      | throwError "equiv_call: the call rule left more than the code before the calls"
    replaceMainGoal [← Judgment.simpArg gp 3 relSimpDecls []]

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
