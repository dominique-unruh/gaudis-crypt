import GaudisCrypt.Logic.ECCallUpto
import GaudisCrypt.Logic.ECCallEquiv
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECAutoStrict

/-!
# EasyCrypt's `proc (I)` on an abstract procedure, and `conseq H` with EC's frame

    equiv_proc (I)           -- EC's `proc (I)` on `equiv[ A(O₁).f ~ A(O₂).f : P ==> Q ]`
    equiv_call (_ : I)       -- EC's `call (_ : I)` on a procedure with a rule (`@[proc_inv]`)
    equiv_conseq_frame H     -- EC's `conseq H` on a procedure judgment, with EC's frame
    equiv_call (H)           -- EC's `call H`, also where the calls spell the callees differently

## `equiv_proc (I)`

On a judgment about the same abstract procedure with two oracles, EC's `proc (I)` keeps the
invariant `I` across it if the oracles do.  `I` is written as for `equiv_call (_ : I)`
(`Logic/ECCallUpto.lean`): `={glob M, x, …} ∧ J` or a relation `J` between the two memories.

The abstract procedure is either
* `D(O₁).f ~ D(O₂).f` with `D` declared (`declare module`): the rule of `equiv_call (_ : I)`;
* a procedure that a rule tagged `@[proc_inv]` is about: a procedure of a declared functor with
  several procedures (a simulator `S(F).f`), whose oracle lists `declare module` does not state.
  A rule has the form

      … → prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L F I g₁ g₂) p₁ p₂
            (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L F I g₁ g₂)

  with arguments named `L`, `F`, `I`; its premises are closed from the context (a hypothesis
  about the module, `assumption`), by the footprint tactics, or are the oracles' judgments.

Goals: the oracles' judgments, EC's `={arg} ∧ I ==> ={res} ∧ I` when the oracles' writes keep the
region (`glob` of the modules, read off the goal's precondition), else with the region in them;
then `pre`, EC's two implications (the goal's precondition gives the invariant, the invariant the
postcondition), as one statement about no code, unless `ec_auto` closes it.

The same rules serve EC's `call (_ : I)` on such a procedure as the last statement:
`equiv_call (_ : ={glob M, …} ∧ I)` (goals: the oracles' judgments, then the code before).

## `equiv_conseq_frame H`

`equiv_conseq H` (`Logic/ECConseq.lean`) asks `H`'s postcondition to imply the goal's.  EC's
`conseq H` also knows what the procedures do not write: a variable or a `glob` the goal's
postcondition reads and a procedure stays out of keeps its value.  Goals `pre` (the goal's
precondition implies `H`'s) and `post`: for arguments and globals that satisfy the goal's
precondition, results and final globals that satisfy `H`'s postcondition and are in each side's
frame satisfy the goal's; an implication that simplification closes is closed.  The procedures
of the goal are read off their module views first
(`module_norm`), and a procedure named differently from `H`'s is recognised by its body.  The
rule is `prhlProc_conseq_frame`.
-/

/-- `@[proc_inv]`: a rule of `equiv_proc (I)` for an abstract procedure (see
`Logic/ECProcInv.lean`). -/
register_label_attr proc_inv

namespace GaudisCrypt

open GaudisCrypt.Lib.RO.Instantiate in
/-- **EC's `conseq H`** on a procedure judgment, with each procedure's frame: the postcondition
for the results and final globals `h` relates that are in each side's frame of the initial
globals, under the precondition. -/
theorem prhlProc_conseq_frame {sig₁ sig₂ : ProcedureSignature} {M₁ : Module.Proc sig₁}
    {M₂ : Module.Proc sig₂}
    {A A' : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop}
    {B B' : sig₁.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop}
    {Fr₁ Fr₂ : VariableAssignment → VariableAssignment → Prop}
    (h : prhlProc A' M₁.procedure M₂.procedure B') (hFr₁ : M₁.Frame Fr₁) (hFr₂ : M₂.Frame Fr₂)
    (hA : ∀ a₁ g₁ a₂ g₂, A a₁ g₁ a₂ g₂ → A' a₁ g₁ a₂ g₂)
    (hB : ∀ a₁ g₁ a₂ g₂, A a₁ g₁ a₂ g₂ → ∀ r₁ τ₁ r₂ τ₂, B' r₁ τ₁ r₂ τ₂ →
      Fr₁ g₁ τ₁ → Fr₂ g₂ τ₂ → B r₁ τ₁ r₂ τ₂) :
    prhlProc A M₁.procedure M₂.procedure B := by
  intro a₁ a₂ g₁ g₂ hAg
  obtain ⟨μ, m1, m2, sat⟩ := h a₁ a₂ g₁ g₂ (hA _ _ _ _ hAg)
  have h1 : μ.satisfies fun w => Fr₁ g₁ w.1.2 :=
    coupling_satisfies_fst (by rw [m1]; exact hFr₁ _ _)
  have h2 : μ.satisfies fun w => Fr₂ g₂ w.2.2 :=
    coupling_satisfies_snd (by rw [m2]; exact hFr₂ _ _)
  exact ⟨μ, m1, m2, fun x hx => hB _ _ _ _ hAg _ _ _ _ (sat x hx) (h1 x hx) (h2 x hx)⟩

namespace ECProcInv

open Lean Meta Elab Tactic

/-- The global variables (lenses into the globals, the components of a `Lens.pair`) and the
regions (`F` of `F.touched_getter`) that the condition `e` of a procedure judgment reads. -/
def readsOf (e : Lean.Expr) : MetaM (Array Lean.Expr × Array Lean.Expr) := do
  let e ← instantiateMVars e
  let lenses ← IO.mkRef (#[] : Array Lean.Expr)
  let regions ← IO.mkRef (#[] : Array Lean.Expr)
  Meta.forEachExpr e fun t => do
    if t.hasLooseBVars || !(t.isApp || t.isConst || t.isFVar) then return
    if t.isAppOfArity ``Footprint.touched_getter 2 then
      unless (← regions.get).contains t.appArg! do regions.modify (·.push t.appArg!)
    else if !t.isAppOf ``Lens.pair then
      let some ty ← observing? (do whnfR (← inferType t)) | return
      if ty.isAppOfArity ``Lens 2 && (ty.getArg! 1).isConstOf ``VariableAssignment then
        unless (← lenses.get).contains t do lenses.modify (·.push t)
  return (← lenses.get, ← regions.get)

/-- The procedure `i` (argument `3` or `4`) of the goal `prhlProc A p₁ p₂ B` as `q`: the same
term, or a procedure with the same body (the two unfolded, `Flatten.unfoldProcedure`: a module
behind a record of another port, an alias). -/
def alignProc (g : MVarId) (i : Nat) (q : Lean.Expr) : MetaM MVarId := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let p := ty.getArg! i
  if ← withReducible (isDefEq p q) then return g
  let eq? ← observing? do
    let r₁ ← Flatten.unfoldProcedure p
    let r₂ ← Flatten.unfoldProcedure q
    unless ← isDefEq r₁.expr r₂.expr do throwError "bodies"
    mkEqTrans (← r₁.getProof) (← mkEqSymm (← r₂.getProof))
  let some eq := eq? | do
    unless ← isDefEq p q do
      throwError "equiv_conseq_frame: the judgment is about{indentExpr q}\nand the goal about\
        {indentExpr p}"
    return g
  let args := ty.getAppArgs
  let motive ← withLocalDeclD `q (← inferType p) fun x =>
    mkLambdaFVars #[x] (mkAppN ty.getAppFn (args.set! i x))
  let g' ← mkFreshExprSyntheticOpaqueMVar (mkAppN ty.getAppFn (args.set! i q)) (← g.getTag)
  g.assign (← mkEqMPR (← mkCongrArg motive eq) g')
  return g'.mvarId!

/-- `k`'s result, built with the finite support of the regions `Rs` in context (`fp_finite`; a
region without it is left out): `fp_disjoint` takes a variable outside a region's `glob` from the
region's finite support, which it looks for among the hypotheses. -/
def withFiniteRegions (Rs : Array Lean.Expr) (k : TermElabM Lean.Expr) : TermElabM Lean.Expr :=
  let rec go (i : Nat) (hs pfs : Array Lean.Expr) : TermElabM Lean.Expr := do
    if h : i < Rs.size then
      let T ← mkAppM ``Footprint.FinitelySupported #[Rs[i]]
      match ← ECCallEquiv.elabClean (← `((by fp_finite : $(← Term.exprToSyntax T)))) with
      | none => go (i + 1) hs pfs
      | some pf => withLocalDeclD `hfin T fun x => go (i + 1) (hs.push x) (pfs.push pf)
    else
      return (← instantiateMVars (← k)).replaceFVars hs pfs
  go 0 #[] #[]

/-- An implication between conditions of procedure judgments, readable: the conditions' local
definitions (`have params := …`) replaced by their values and the reads simplified. -/
def tidy (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let ty' ← Meta.transform ty (pre := fun e => do
    if let .letE _ _ v b _ := e then return .visit (b.instantiate1 v)
    return .continue)
  let ty' ← Core.betaReduce ty'
  let g ← g.replaceTargetDefEq ty'
  let r ← Judgment.simpWithNames PRHLWp.relSimpDecls [] ty'
  if r.expr.isTrue then
    g.assign (← mkOfEqTrue (← r.getProof))
    return g
  applySimpResultToTarget g ty' r

/-- Close `g` by `tac` if that closes it (EC's tactics close the goals that are trivial); `none`
then, else the goal as it was. -/
def tryClose (g : MVarId) (tac : TSyntax `tactic) : TacticM (Option MVarId) := do
  if ← g.isAssigned then return none
  let s ← saveState
  try
    let [] ← withoutRecover <| evalTacticAt tac g | throwError "left"
    return none
  catch _ =>
    s.restore
    return some g

/-- Close an implication between conditions of procedure judgments by simplification, with what
EC takes for granted about `glob`s: states that agree on a region agree on a region inside it
(`={glob A, glob B}` gives `={glob B}`).  `none` if closed, else the goal as it was. -/
def closeImp (g : MVarId) : TacticM (Option MVarId) := do
  if ← g.isAssigned then return none
  let s ← saveState
  try
    let [g'] ← withoutRecover <| evalTacticAt (← `(tactic| (intros; try cases_type* And))) g
      | return none
    let Rs ← ECConseqFrame.regionsOf #[← g'.getType]
    let mut g' := g'
    for d in ← g'.withContext getLCtx do
      if d.isImplementationDetail then continue
      let some (_, lhs, rhs) := (← instantiateMVars d.type).eq? | continue
      unless lhs.isAppOfArity ``Getter.get 4 && rhs.isAppOfArity ``Getter.get 4 do continue
      let tg := lhs.getArg! 2
      unless tg.isAppOfArity ``Footprint.touched_getter 2 && rhs.getArg! 2 == tg do continue
      for R in Rs do
        if R == tg.appArg! then continue
        let s' ← saveState
        try
          let gNew ← g'.withContext do
            let le ← mkAppM ``LE.le #[R, tg.appArg!]
            let hle ← mkFreshExprSyntheticOpaqueMVar le
            let [] ← withoutRecover <| evalTacticAt (← `(tactic| fp_sub)) hle.mvarId!
              | throwError "left"
            let pf ← mkAppM ``Footprint.touched_getter_eq_of_le #[hle, d.toExpr]
            let (_, gNew) ← (← g'.assert `hglob (← inferType pf) pf).intro1P
            pure gNew
          g' := gNew
        catch _ => s'.restore
    -- the region facts are in; a declared module's restrictions are of no use to `simp_all`
    let [] ← withoutRecover <| evalTacticAt (← `(tactic| (clear_decl_hyps; simp_all; done))) g'
      | throwError "left"
    return none
  catch _ =>
    s.restore
    return some g

/-- The index of the argument `n` of a lemma with binder names `names`. -/
def argIdx (tac : String) (names : Array Name) (n : Name) : MetaM Nat := do
  let some i := names.findIdx? (· == n) | throwError "{tac}: no argument `{n}`"
  return i

/-- The goals `StmtWithHoles.WritesKeep F.touched_getter.get o.body` of an oracle procedure:
split down to its writes, a write to a local or to a global variable outside `F`
(`fp_disjoint`) closed.  Fails if a write is left (an abstract oracle, a write into `F`). -/
def closeWritesKeep (w : MVarId) (F : Lean.Expr) : TacticM Unit := do
  let saved ← getGoals
  w.withContext do
    setGoals [w]
    liftMetaTactic (writesKeepSplit ·)
    evalTactic (← `(tactic| all_goals try exact fun _ _ => rfl))
    let FS ← Term.exprToSyntax F
    for leaf in ← getGoals do
      if ← leaf.isAssigned then continue
      let lty ← instantiateMVars (← leaf.getType)
      let some lift := lty.find? (·.isAppOfArity ``liftLens 4)
        | throwError "equiv_proc: a write that is not of a variable"
      let XS ← Term.exprToSyntax lift.appArg!
      let [] ← leaf.withContext <| withoutRecover <| evalTacticAt (← `(tactic|
          exact fun v σ => touched_set_of_le_compl
            (show Lens.footprint $XS ≤ ($FS)ᶜ by fp_disjoint) v σ.globals)) leaf
        | throwError "equiv_proc: a write into the region"
  setGoals saved

/-- An oracle's goal `prhlProc (… ∧ globInvF L F I …) o₁ o₂ (… ∧ globInvF L F I …)` as EC's
`={arg} ∧ I ==> ={res} ∧ I`, the region `F` kept by the oracles' writes
(`prhlProc_globInvF_of_writesKeep`); if they do not keep it syntactically (an abstract oracle),
the goal with the region. -/
def oracleGoal (o : MVarId) (F : Lean.Expr) : TacticM MVarId := do
  let s ← saveState
  let tidy (o : MVarId) (lemmas : TSyntax `tactic) : TacticM MVarId := do
    let o' ← (do
      let [o'] ← evalTacticAt lemmas o | pure o
      pure o') <|> pure o
    o'.setTag `oracle
    return o'
  try
    let gs ← evalTacticAt (← `(tactic| refine prhlProc_globInvF_of_writesKeep _ ?w₁ ?w₂ ?o)) o
    let mut o' := o
    for g in gs do
      if (← g.getTag).eraseMacroScopes == `o then o' := g
      else closeWritesKeep g F
    tidy o' (← `(tactic| dsimp only [Lens.pair]))
  catch _ =>
    s.restore
    tidy o (← `(tactic| dsimp only [globInvF, Lens.pair]))

end ECProcInv

open Lean Meta Elab Tactic GaudisCrypt PRHLWp ECCallUpto ECCallEquiv ECProcInv in
/-- `equiv_proc (I)` by a rule tagged `@[proc_inv]`, on the judgment about the two call
statements (see the module docstring). -/
def ECProcInv.byRule (I : Term) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty0 ← prhlGoal g "equiv_proc"
  let (I', globs) ← splitGlobs I
  let IF ← elabRelCond ty0 I'
  let (L, _, preds) ← onGlobals #[IF]
  let g ← HoareSplit.hoareSplit 1 g
  setGoals [g]
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let p₁ ← mkAppM ``Module.Proc.procedure #[← lastCallee (ty.getArg! 1)]
    let p₂ ← mkAppM ``Module.Proc.procedure #[← lastCallee (ty.getArg! 2)]
    -- the region kept equal: the `glob`s of the goal's precondition, and those `I` names
    let mut Rs ← ECConseqFrame.regionsOf #[ty.getArg! 0]
    for t in globs do
      let R ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      let R ← instantiateMVars R
      unless Rs.contains R do Rs := Rs.push R
    let F? ← match Rs.back? with
      | none => pure none
      | some last => do
        let ss ← Rs.pop.mapM fun R => (Term.exprToSyntax R : TermElabM Term)
        let FS ← ss.foldrM (fun x acc => `($x ⊔ $acc)) (← Term.exprToSyntax last)
        let F ← Term.elabTerm FS none
        Term.synthesizeSyntheticMVarsNoPostponing
        pure (some (← instantiateMVars F))
    let mut errs : Array MessageData := #[]
    for lem in ← labelled `proc_inv do
      let s ← saveState
      try
        let c ← mkConstWithFreshMVarLevels lem
        let cty ← inferType c
        let (ms, bis, concl) ← forallMetaTelescope cty
        let names := cty.getForallBinderNames.toArray
        unless concl.isAppOfArity ``prhlProc 6 do throwError "not a rule about procedures"
        unless ← isDefEq ms[← argIdx "equiv_proc" names `L]! L do throwError "the view `L`"
        unless ← isDefEq ms[← argIdx "equiv_proc" names `I]! preds[0]! do
          throwError "the invariant `I`"
        let iF ← argIdx "equiv_proc" names `F
        if let some F := F? then
          unless ← isDefEq ms[iF]! F do throwError "the region `F`"
        unless ← isDefEq (concl.getArg! 3) p₁ do throwError "not about the left procedure"
        unless ← isDefEq (concl.getArg! 4) p₂ do throwError "not about the right procedure"
        for m in ms, bi in bis do
          if bi.isInstImplicit && !(← m.mvarId!.isAssigned) then
            m.mvarId!.assign (← synthInstance (← instantiateMVars (← inferType m)))
        -- the premises: the oracles' judgments, the others closed
        let mut oracles : Array MVarId := #[]
        for m in ms do
          let m' ← instantiateMVars m
          unless m'.isMVar do continue
          let mty ← instantiateMVars (← inferType m')
          unless ← isProp mty do continue
          if (← whnfR mty).isAppOfArity ``prhlProc 6 then
            m'.mvarId!.setKind .syntheticOpaque
            oracles := oracles.push m'.mvarId!
          else
            let [] ← evalTacticAt (← `(tactic| first
                | exact le_rfl
                | assumption
                | fp_le
                | ((try simp only [Footprint.lens_pair]); (repeat' apply sup_le);
                    all_goals fp_disjoint))) m'.mvarId!
              | throwError "a premise is left"
        let rule ← instantiateMVars (mkAppN c ms)
        if rule.hasExprMVar && !(← oracles.allM fun o => return !(← o.isAssigned)) then
          throwError "an argument is not determined"
        let F ← instantiateMVars ms[iF]!
        let cs ← mkConstWithFreshMVarLevels ``prhlStmt_seq_call
        let csty ← inferType cs
        let (ms2, _, concl2) ← forallMetaTelescope csty
        let names2 := csty.getForallBinderNames.toArray
        unless ← isDefEq ms2[← argIdx "equiv_proc" names2 `h]! rule do
          throwError "the rule does not fit the call rule"
        unless ← isDefEq concl2 ty do throwError "the rule does not fit the calls"
        g.assign (← instantiateMVars (mkAppN cs ms2))
        let gPre := ms2[← argIdx "equiv_proc" names2 `hpre]!.mvarId!
        gPre.setKind .syntheticOpaque
        let gPre ← (do
          let [p'] ← evalTacticAt (← `(tactic| dsimp only [globInvF, Lens.pair])) gPre | pure gPre
          pure p') <|> pure gPre
        gPre.setTag `pre
        let oracleGs ← oracles.mapM (oracleGoal · F)
        setGoals (oracleGs.toList ++ [gPre])
        return
      catch e =>
        s.restore
        errs := errs.push m!"{lem}: {e.toMessageData}"
    throwError "equiv_proc: no rule (`@[proc_inv]`) for the procedures{indentExpr p₁}\nand\
      {indentExpr p₂}{MessageData.joinSep (errs.toList.map fun e => m!"\n{e}") ""}"

/-- **EC's `proc (I)`** on an abstract procedure: see the module docstring.  Goals: the oracles'
judgments, then `pre`. -/
syntax (name := equivProcInv) "equiv_proc" colGt " (" term ")" : tactic

open Lean Meta Elab Tactic GaudisCrypt PRHLWp ECCallEquiv in
elab_rules (kind := equivProcInv) : tactic
  | `(tactic| equiv_proc ($I)) => do
    liftMetaTactic1 fun g => some <$> (ECProc.accessorNorm g >>= equivProcToStmt)
    let declared ← withMainContext do
      let ty ← prhlGoal (← getMainGoal) "equiv_proc"
      let M ← lastCallee (ty.getArg! 1)
      return M.isAppOfArity ``GaudisCrypt.Module.app 6 && (M.getArg! 4).isFVar
    if declared then equivCallInvAndCore I else ECProcInv.byRule I
    -- EC's two implications (`pre`): closed if `auto` closes them
    let gs ← getGoals
    let mut out : Array MVarId := #[]
    for g in gs do
      if (← g.getTag) == `pre then
        if let some g' ← ECProcInv.tryClose g (← `(tactic| (ec_auto; done))) then out := out.push g'
      else out := out.push g
    setGoals out.toList

open Lean Meta Elab Tactic GaudisCrypt PRHLWp ECCallEquiv in
/-- Do the two sides end with calls of procedures that a rule tagged `@[proc_inv]` is about
(and that are not a declared module applied to its oracles, which `equiv_call` has rules for)? -/
def ECProcInv.lastCallsHaveRule : TacticM Bool := withMainContext do
  let s ← saveState
  try
    let g ← getMainGoal
    let _ ← prhlGoal g "equiv_call"
    let g ← HoareSplit.hoareSplit 1 g
    g.withContext do
      let ty ← instantiateMVars (← g.getType)
      let M₁ ← lastCallee (ty.getArg! 1)
      let M₂ ← lastCallee (ty.getArg! 2)
      if M₁.isAppOfArity ``GaudisCrypt.Module.app 6 && (M₁.getArg! 4).isFVar then return false
      let p₁ ← mkAppM ``Module.Proc.procedure #[M₁]
      let p₂ ← mkAppM ``Module.Proc.procedure #[M₂]
      for lem in ← labelled `proc_inv do
        let c ← mkConstWithFreshMVarLevels lem
        let (_, _, concl) ← forallMetaTelescope (← inferType c)
        if concl.isAppOfArity ``prhlProc 6 then
          if (← isDefEq (concl.getArg! 3) p₁) && (← isDefEq (concl.getArg! 4) p₂) then
            return true
      return false
  catch _ => return false
  finally s.restore

/-- **EC's `call (_ : ={glob M, …} ∧ I)`** on the last statements, calls of a procedure with a
rule tagged `@[proc_inv]` (a simulator's `S(F).init`, `S(F).f`): as `equiv_proc (I)`.  Goals: the
oracles' judgments, then the code before the calls.  Any other callee is left to the forms of
`Logic/ECCallUpto.lean`. -/
elab_rules (kind := equivCallInvAnd) : tactic
  | `(tactic| equiv_call (_ : ={ $xs,* } ∧ $rest)) => do
    unless ← ECProcInv.lastCallsHaveRule do Lean.Elab.throwUnsupportedSyntax
    ECProcInv.byRule (← `(={ $xs,* } ∧ $rest))

/-- **EC's `call (_ : I)`** on the last statements, calls of a procedure with a rule tagged
`@[proc_inv]`: as `equiv_proc (I)`.  Any other callee is left to the other forms. -/
elab_rules (kind := GaudisCrypt.PRHLWp.tacticEquiv_call___) : tactic
  | `(tactic| equiv_call $h:term) => do
    let `(term| (_ : $I)) := h | Lean.Elab.throwUnsupportedSyntax
    unless ← ECProcInv.lastCallsHaveRule do Lean.Elab.throwUnsupportedSyntax
    ECProcInv.byRule I

open Lean Meta Elab Tactic GaudisCrypt PRHLWp ECCallEquiv ECProcInv in
/-- **EC's `call H`** where the calls spell the callees differently from `H` (a procedure behind
a record, `(RF.mk { get := M.get }).get`; a view that a functor has unfolded): `H` is taken to
the callees as the calls spell them, the two having the same body (`ECProcInv.alignProc`), and
the call is by that judgment (the rules of `Logic/ECCallEquiv.lean`, `Logic/PRHLWp.lean`).  Where
`H` is about the callees as spelled, or is written with holes that the callees fill
(`equiv_call (L _ _)`), those rules apply directly. -/
elab_rules (kind := GaudisCrypt.PRHLWp.tacticEquiv_call___) : tactic
  | `(tactic| equiv_call $h:term) => withMainContext do
    if let `(term| (_ : $_)) := h then throwUnsupportedSyntax
    let s ← saveState
    let g ← getMainGoal
    let _ ← prhlGoal g "equiv_call"
    let g' ← HoareSplit.hoareSplit 1 g
    let hJ? : Option Lean.Expr ← g'.withContext <|
      tryCatchRuntimeEx (m := TacticM) (do
        let ty ← prhlGoal g' "equiv_call"
        let M₁ ← lastCallee (ty.getArg! 1)
        let M₂ ← lastCallee (ty.getArg! 2)
        let hJ ← Term.elabTerm h none
        Term.synthesizeSyntheticMVarsNoPostponing
        let hJ ← instantiateMVars hJ
        -- holes for the callees to fill: the other rules' business
        if hJ.hasExprMVar then return none
        let hty := (← instantiateMVars (← inferType hJ)).cleanupAnnotations
        unless hty.isAppOfArity ``prhlProc 6 do return none
        let p₁ := hty.getArg! 3
        let p₂ := hty.getArg! 4
        let q₁ ← mkAppM ``Module.Proc.procedure #[M₁]
        let q₂ ← mkAppM ``Module.Proc.procedure #[M₂]
        if (← withReducible (isDefEq p₁ q₁)) && (← withReducible (isDefEq p₂ q₂)) then
          return none
        let args := hty.getAppArgs
        let m ← mkFreshExprSyntheticOpaqueMVar
          (mkAppN hty.getAppFn ((args.set! 3 q₁).set! 4 q₂))
        let g₁ ← alignProc m.mvarId! 3 p₁
        let g₂ ← alignProc g₁ 4 p₂
        g₂.assign hJ
        return some (← instantiateMVars m))
        (fun _ => pure none)
    s.restore
    let some hJ := hJ? | throwUnsupportedSyntax
    evalTactic (← `(tactic| equiv_call $(← Term.exprToSyntax hJ)))

open Lean Meta Elab Tactic GaudisCrypt ECCallEquiv ECProcInv in
/-- **EC's `conseq H`** on a procedure judgment, with EC's frame: see the module docstring.
Goals `pre`, `post`. -/
elab "equiv_conseq_frame " H:term:max : tactic => do
  liftMetaTactic1 fun g => some <$> ECProc.accessorNorm g
  withMainContext do
    let g ← getMainGoal
    let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
    unless ty.isAppOfArity ``prhlProc 6 do
      throwError "equiv_conseq_frame: not a judgment about procedures{indentExpr ty}"
    let hJ ← Term.elabTerm H none
    Term.synthesizeSyntheticMVarsNoPostponing
    let hJ ← instantiateMVars hJ
    -- a lemma with arguments left out (the section's modules): found by matching the goal
    let (hargs, hbis, hty) ← forallMetaTelescope (← instantiateMVars (← inferType hJ))
    let hJ := mkAppN hJ hargs
    let hty ← whnfR hty
    unless hty.isAppOfArity ``prhlProc 6 do
      throwError "equiv_conseq_frame: not a judgment about procedures{indentExpr hty}"
    let modOf (p : Lean.Expr) : MetaM Lean.Expr := do
      unless p.isAppOf ``Module.Proc.procedure do
        throwError "equiv_conseq_frame: not a module's procedure{indentExpr p}"
      return p.appArg!
    let M₁ ← modOf (hty.getArg! 3)
    let M₂ ← modOf (hty.getArg! 4)
    let g ← alignProc g 3 (hty.getArg! 3)
    let g ← alignProc g 4 (hty.getArg! 4)
    let undetermined : TacticM Unit := do
      throwError "equiv_conseq_frame: arguments of the judgment are not determined by the goal's \
        procedures (give them){indentExpr (← instantiateMVars hJ)}"
    for a in hargs, bi in hbis do
      if bi.isInstImplicit && !(← a.mvarId!.isAssigned) then
        let ity ← instantiateMVars (← inferType a)
        if ity.hasExprMVar then undetermined
        a.mvarId!.assign (← synthInstance ity)
    let hJ ← instantiateMVars hJ
    if hJ.hasExprMVar then undetermined
    let M₁ ← instantiateMVars M₁
    let M₂ ← instantiateMVars M₂
    g.withContext do
      let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
      -- the frames: what the goal's postcondition reads that each procedure stays out of
      let (gls, Rs) ← readsOf (ty.getArg! 5)
      let fr₁ ← withFiniteRegions Rs (frameFor M₁ gls Rs)
      let fr₂ ← withFiniteRegions Rs (frameFor M₂ gls Rs)
      let c ← mkConstWithFreshMVarLevels ``prhlProc_conseq_frame
      let cty ← inferType c
      let (ms, _, concl) ← forallMetaTelescope cty
      let names := cty.getForallBinderNames.toArray
      let idx := argIdx "equiv_conseq_frame" names
      unless ← isDefEq ms[← idx `h]! hJ do
        throwError "equiv_conseq_frame: the judgment does not fit the rule"
      unless ← isDefEq ms[← idx `hFr₁]! fr₁ do
        throwError "equiv_conseq_frame: the left procedure's frame does not fit"
      unless ← isDefEq ms[← idx `hFr₂]! fr₂ do
        throwError "equiv_conseq_frame: the right procedure's frame does not fit"
      unless ← isDefEq concl ty do
        throwError "equiv_conseq_frame: the judgment{indentExpr hty}\ndoes not fit the goal\
          {indentExpr ty}"
      g.assign (← instantiateMVars (mkAppN c ms))
      -- the implications, closed if simplification closes them (EC's `conseq H` leaves the
      -- ones that are not trivial)
      let goalOf (n tag : Name) : TacticM (Option MVarId) := do
        let m := ms[← idx n]!.mvarId!
        m.setKind .syntheticOpaque
        let m ← tidy m
        m.setTag tag
        closeImp m
      let pre ← goalOf `hA `pre
      let post ← goalOf `hB `post
      replaceMainGoal ([pre, post].filterMap id)

end GaudisCrypt
