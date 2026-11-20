import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECCallFrameRel
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
        let names := (← inferType c).getForallBinderNames
        let idx (n : Name) : MetaM Nat := do
          let some i := names.findIdx? (· == n) | throwError "equiv_call: no argument `{n}`"
          return i
        -- the judgment as written; if it does not fit the callees, with its aliases rewritten to
        -- their callees (the program calls the callee: after `inline*`, say)
        let attempt (hJ : Lean.Expr) : MetaM (Option (Array Lean.Expr × Lean.Expr)) := do
          let s ← saveState
          let (ms, _, concl) ← forallMetaTelescope (← inferType c)
          if (← isDefEq ms[← idx `M₁]! M₁) && (← isDefEq ms[← idx `M₂]! M₂) &&
              (← isDefEq ms[← idx `h]! hJ) then
            return some (ms, concl)
          s.restore
          return none
        let r? ← match ← attempt hJ with
          | some r => pure (some r)
          | none => do
            let hJ' ← unfoldAliasesIn hJ
            if hJ' == hJ then pure none else attempt hJ'
        let some (ms, concl) := r? | return (none, none)
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
