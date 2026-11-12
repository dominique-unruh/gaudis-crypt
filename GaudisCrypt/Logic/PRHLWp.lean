import GaudisCrypt.Logic.HoareWp
import GaudisCrypt.Syntax.PRHLSyntax
import GaudisCrypt.Logic.StmtSwap
import GaudisCrypt.Logic.LoopTransform

/-!
# Tactics for relational judgments (pRHL)

`prhlStmt` registers one descriptor per side with the judgment registry (`Logic/Judgment.lean`),
so the generic statement steps work on it, on both sides or on one (`{1}`, `{2}`):

* `stmt_inline n`, `stmt_inline{i} n` — inline call site `n` (EC's `inline`);
* `stmt_split k`, `stmt_split{i} k` — regroup the last `k` statements;
* `stmt_wp`, `stmt_wp k`, `stmt_wp{i} k` — wp over deterministic code (EC's `wp`); over a
  sampling on one side, `rnd{i}` (the distribution must be lossless).

And the relational steps proper:

* `equiv_proc_to_stmt` — from `equiv[ M₁ ~ M₂ : P ==> Q ]` to the judgment about the two call
  statements (inlined by `stmt_inline 0`; EC's `proc`, to the bodies, is `equiv_proc`,
  `Logic/ECProc.lean`);
* `equiv_rnd`, `equiv_rnd f` — the two last statements are samplings, coupled along `f`
  (default: the identity) (EC's `rnd`);
* `equiv_rnd_run k` — a sampling on the left against the last `k` statements on the right, which
  sample the same;
* `equiv_while_raw I` — synchronized loops with the invariant `I` (four goals; EC's `while I` is `equiv_while`, `Logic/ECWhileRel.lean`);
* `equiv_call h` — the last statements are calls, related by the procedure judgment `h` (EC's
  `call`; `prhlProc_glob hA` for an abstract procedure, EC's `call (_ : ={glob A})`);
  `equiv_call` alone for calls of the same procedure from equal arguments and globals;
* `equiv_seq_last k₁ k₂ : M` — cut after all but the last `k₁` / `k₂` statements (EC's `seq`
  counts from the start: `equiv_seq`, `Logic/ECSeq.lean`);
* `equiv_case P` — case analysis on a relation of the initial states (EC's `case`);
* `equiv_if`, `equiv_if{i}` — conditionals on both sides, or on one (EC's `if`, `if{i}`);
* `equiv_sym` — swap the sides;
* `equiv_rcondf{i}` — a trailing loop on side `i` whose guard is false (EC's `rcondf{i}`);
* `equiv_skip` — at `skip ~ skip`, the implication, with the reads of both states generalized
  (`x₁`, `x₂`; EC's `skip`).

Relations written in tactics (`I`, `M`, `P`, the coupling `f`) are relational conditions as in
`equiv[ … ]`: `§x{1}`, `§x{2}`, `={x}`, over the program variables of the goal.
-/

namespace GaudisCrypt

namespace PRHLWp

/-- The simp set for relational conditions: the reads through writes of `simpReads`, and the
trivial coupling conditions `equiv_rnd` leaves (the identity and negation push a uniform
distribution to itself, and its support is everything). -/
def relSimpDecls : List Lean.Name :=
  HoareWp.simpReadsDecls ++ [``SubProbability.bind_pure_id, ``SubProbability.uniform_bind_not,
    ``SubProbability.uniform_bind_add_left, ``SubProbability.uniform_bind_add_right,
    ``SubProbability.uniform_bind_sub_right,
    ``SubProbability.uniform_expected_one,
    ``SubProbability.uniform_bind_xor,
    ``eq_self_iff_true, ``SubProbability.uniform_support, ``Set.mem_univ]

end PRHLWp

run_meta registerJudgment {
  head := ``prhlStmt
  side := 1
  stmtArg := 1
  postArg := 3
  equivLemma := ``prhlStmt_of_equiv_left
  transportLemma := ``prhlStmt_of_equivInLens_left
  detLemma := some ``prhlStmt_seq_det_left
  sampleLemma := some ``prhlStmt_seq_sample_left
  -- the inliner's cleaning does not push `.globals` through its renaming lenses
  condSimp := PRHLWp.relSimpDecls
  postSimp := PRHLWp.relSimpDecls }

run_meta registerJudgment {
  head := ``prhlStmt
  side := 2
  stmtArg := 2
  postArg := 3
  equivLemma := ``prhlStmt_of_equiv_right
  transportLemma := ``prhlStmt_of_equivInLens_right
  detLemma := some ``prhlStmt_seq_det_right
  sampleLemma := some ``prhlStmt_seq_sample_right
  condSimp := PRHLWp.relSimpDecls
  postSimp := PRHLWp.relSimpDecls }

namespace PRHLWp

open Lean Meta Elab Tactic TacticMisc

/-- The names of the binders of `ty`'s leading `∀`s. -/
partial def binderNames : Lean.Expr → Array Name
  | .forallE n _ b _ => #[n] ++ binderNames b
  | _ => #[]

/-- Apply the lemma `lem` to `g` by unifying its conclusion with the goal (no unfolding of the
judgment, which `MVarId.apply` would do to count arguments): `pre` sets the lemma's arguments by
binder name first.  The arguments left open are returned, in order. -/
def applyLemma (lem : Name) (g : MVarId) (pre : Array (Name × Lean.Expr) := #[]) :
    MetaM (Array MVarId) := g.withContext do
  let c ← mkConstWithFreshMVarLevels lem
  let cTy ← inferType c
  let names := binderNames cTy
  let (ms, _, concl) ← forallMetaTelescope cTy
  for (n, e) in pre do
    let some i := names.findIdx? (·.eraseMacroScopes == n)
      | throwError "`{lem}` has no argument `{n}`"
    unless ← isDefEq ms[i]! e do
      throwError "`{lem}`: the argument `{n}` does not fit:{indentExpr e}"
  unless ← isDefEq concl (← g.getType) do
    throwError "`{lem}` does not apply to{indentExpr (← g.getType)}"
  g.assign (← instantiateMVars (mkAppN c ms))
  let mut open_ := #[]
  for m in ms do
    let m := m.mvarId!
    unless ← m.isAssigned do
      m.setKind .syntheticOpaque
      open_ := open_.push m
  return open_

/-! ## Generalizing the reads of two states -/

/-- Does `σ.globals` occur in `e` other than as the state of a read `x.get σ.globals`? -/
partial def bareGlobals (σ : FVarId) (e : Lean.Expr) : Bool :=
  if e.isAppOfArity ``Getter.get 4 && isStateOf σ e.appArg! then bareGlobals σ (e.getArg! 2)
  else if e.isAppOfArity ``ProgramState.globals 1 && e.appArg!.isFVarOf σ then true
  else match e with
    | .proj ``ProgramState 0 b => b.isFVarOf σ || bareGlobals σ b
    | .app f a => bareGlobals σ f || bareGlobals σ a
    | .lam _ t b _ | .forallE _ t b _ => bareGlobals σ t || bareGlobals σ b
    | .letE _ t v b _ => bareGlobals σ t || bareGlobals σ v || bareGlobals σ b
    | .mdata _ b => bareGlobals σ b
    | _ => false

/-- Does the state `σ` occur in `e` only as read (`collectReadsOf`) or as its globals? -/
def onlyRead (σ : FVarId) (e : Lean.Expr) : Bool :=
  let reads := collectReadsOf σ e
  let stripped := e.replace fun x =>
    if reads.contains x || (x.isAppOfArity ``ProgramState.globals 1 && x.appArg!.isFVarOf σ) then
      some (mkConst ``True)
    else none
  !stripped.containsFVar σ

/-- On a goal `∀ σ₁ σ₂ : ProgramState, P σ₁ σ₂`: `generalizeReads` for both states — every read
of `σ₁` becomes a value `x₁`, every read of `σ₂` a value `x₂` (named after the variable), and the
states are dropped if nothing else mentions them; a state that occurs other than read is left
alone (`onlyRead`), its reads with it.  Where the globals themselves occur
(`§allGlobals`, the globals a call leaves), they become a value `globals₁`/`globals₂` first, and the reads of
global variables stay reads of it (`x.get globals₁`), so nothing is lost.  Atomic, as
`generalizeReads`. -/
def generalizeReadsRel (g : MVarId) (normDec : Bool := false) : MetaM MVarId :=
    commitIfNoEx <| g.withContext do
  let (fvs, g) ← g.introN 2
  let #[σ₁, σ₂] := fvs | throwError "generalizeReadsRel: expected two states"
  let (gvs, g) ← g.withContext do
    let ty ← instantiateMVars (← g.getType)
    -- `§allGlobals` is the globals themselves (`allGlobals_get`, by `rfl`): spelled as such, it
    -- makes the reads of global variables stay reads of the generalized globals, instead of
    -- becoming values unrelated to them
    let ty ← Meta.transform (← unfoldReads σ₂ (← unfoldReads σ₁ ty normDec) normDec)
      (post := fun e => do
      if e.isAppOfArity ``Getter.get 4 && (e.getArg! 2).isConstOf ``allGlobals
          && e.appArg!.isFVar then
        return .done (mkApp (mkConst ``ProgramState.globals) e.appArg!)
      return .continue)
    let g ← g.change ty
    -- (EC's `auto`, `equiv_skip_ec`: the `decide` instances first, so that no read is left)
    let g ← if normDec then (try TacticMisc.normDecideGoal g catch _ => pure g) else pure g
    let g ← try TacticMisc.globTuples g catch _ => pure g
    let body ← instantiateMVars (← g.getType)
    let mut args : Array GeneralizeArg := #[]
    for (σ, n) in [(σ₁, "globals₁"), (σ₂, "globals₂")] do
      if bareGlobals σ body && onlyRead σ body then
        args := args.push { expr := mkApp (mkConst ``ProgramState.globals) (mkFVar σ),
                            xName? := some (Name.mkSimple n) }
    if args.isEmpty then pure (#[], g) else g.generalize args
  g.withContext do
    let body ← instantiateMVars (← g.getType)
    let mut used := binderNamesIn body
    for d in ← getLCtx do
      used := used.push d.userName.eraseMacroScopes.toString
    let mut reads : Array Lean.Expr := #[]
    let mut args : Array GeneralizeArg := #[]
    for (σ, sfx) in [(σ₁, "₁"), (σ₂, "₂")] do
      -- a state that occurs other than read (in a statement's run, say) stays: generalizing its
      -- reads would cut them off from it
      unless onlyRead σ body do continue
      for r in collectReadsOf σ body do
        if ← reads.anyM fun r' => withReducible (isDefEq r r') then continue
        reads := reads.push r
        let n := freshIn used ((← readBaseName (r.getArg! 2)) ++ sfx)
        used := used.push n
        args := args.push { expr := r, xName? := some (Name.mkSimple n) }
    let (xs, g₀) ← if args.isEmpty then pure (#[], g) else g.generalize args
    let mut gc := g₀
    let mut keep := #[]
    for σ in [σ₂, σ₁] do
      try gc ← gc.clear σ catch _ => keep := keep.push σ
    let (_, gr) ← gc.revert (keep.reverse ++ gvs ++ xs) (preserveOrder := true)
    return gr

/-! ## Relational conditions in tactics -/

/-- Elaborate the relational term `t` (`§x{1}`, `§x{2}`, `={x}` over the program variables of the
goal `goalTy`) at type `T`, as a function `ProgramState → ProgramState → T`. -/
def elabRelTerm (goalTy : Lean.Expr) (t : Term) (T : Lean.Expr) : TacticM Lean.Expr := do
  let vars := (← ProgramSyntax.frameVars goalTy.getAppArgs #[]).filter (·.nameable)
  let σ₁ ← `(σ₁)
  let σ₂ ← `(σ₂)
  let states (k : Nat) : Option Term :=
    if k == 1 then some σ₁ else if k == 2 then some σ₂ else none
  let t' : Term := ⟨← liftMacroM (RelSyntax.expand states (fun _ _ => none) t)⟩
  let Tstx ← Term.exprToSyntax T
  let mut stx ← `(fun ($σ₁ : ProgramState) ($σ₂ : ProgramState) => ($t' : $Tstx))
  for v in vars.reverse do
    let some slot := v.slots[0]? | continue
    stx ← `(letI $(mkIdent (.mkSimple v.name)) := $(← Term.exprToSyntax slot); $stx)
  let ps := mkConst ``ProgramState
  let e ← elabTermEnsuringType stx (← mkArrow ps (← mkArrow ps T))
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- A relational condition (`Prop`-valued). -/
def elabRelCond (goalTy : Lean.Expr) (t : Term) : TacticM Lean.Expr :=
  elabRelTerm goalTy t (mkSort 0)

/-- `generalizeReadsRel`, for the tactic `tac`: if it fails, the goal stays about the two states,
and `tac` says so (`ECReport.fallback`). -/
def generalizeReadsRelOr (tac : String) (g : MVarId) (normDec : Bool := false) : MetaM MVarId := do
  try generalizeReadsRel g normDec
  catch e =>
    ECReport.fallback tac m!"the reads are not generalized: the goal stays about the states" (some e)
    pure g

/-- The goal's type, checked to be a `prhlStmt` judgment. -/
def prhlGoal (g : MVarId) (tac : String) : MetaM Lean.Expr := do
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  unless ty.isAppOfArity ``prhlStmt 4 do
    throwError "{tac}: expected a relational judgment `prhlStmt A c₁ c₂ B`, got{indentExpr ty}"
  return ty

/-! ## From procedures to statements -/

/-- On a goal `prhlProc A p₁ p₂ B`: the judgment about the two call statements
`res <- call pᵢ (x₁, …, xₙ)`, one local variable per parameter (`prhlProc_of_prhlStmt`), the
conditions with the reads simplified. -/
def equivProcToStmt (g : MVarId) : MetaM MVarId := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  unless ty.isAppOfArity ``prhlProc 6 do
    throwError "equiv_proc_to_stmt: expected a procedure judgment `prhlProc A p₁ p₂ B`, got\
      {indentExpr ty}"
  let #[sig₁, sig₂, A, p₁, p₂, B] := ty.getAppArgs | unreachable!
  let va := mkConst ``VariableAssignment
  let ps := mkConst ``ProgramState
  -- the slots of one side: the result, the parameters, the call statement
  let side (sig p : Lean.Expr) :
      MetaM (Lean.Expr × Lean.Expr × Lean.Expr × List Lean.Expr × Lean.Expr) := do
    let some tys ← ModuleDecl.listLit? (← whnf (mkApp (mkConst ``ProcedureSignature.params) sig))
      | throwError "the parameter list of{indentExpr sig}\nis not a list literal"
    let ret ← sigRetType sig
    let names ← procParamNames p tys.length
    let resName := Id.run do
      let mut r := "res"
      while names.contains r do r := r ++ "'"
      return r
    let (resVA, resPS) ← mkVarSlots resName ret
    let slots ← (names.toList.zip tys).mapM fun (n, T) => mkVarSlots n T
    let argsVA ← mkTupleLens va (slots.map (·.1))
    let argSlots := slots.map (·.2)
    let argsGetter ← match argSlots with
      | [l] => mkAppM ``Lens.toGetter #[l]
      | _ => withLocalDeclD `st ps fun st => do
          mkAppM ``Getter.mk #[← mkLambdaFVars #[st] (← mkTupleRead st argSlots)]
    let body ← mkAppOptM ``Stmt.call #[some sig, some (← mkAppM ``Lens.toSetter #[resPS]),
      some p, some argsGetter]
    return (resVA, resPS, argsVA, argSlots, body)
  let (resVA₁, resPS₁, argsVA₁, argSlots₁, body₁) ← side sig₁ p₁
  let (resVA₂, resPS₂, argsVA₂, argSlots₂, body₂) ← side sig₂ p₂
  let cond (C : Lean.Expr) (val₁ val₂ : Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr :=
    withLocalDeclD `σ₁ ps fun σ₁ => withLocalDeclD `σ₂ ps fun σ₂ => do
      let c := C.beta #[← val₁ σ₁, ← mkAppM ``ProgramState.globals #[σ₁], ← val₂ σ₂,
        ← mkAppM ``ProgramState.globals #[σ₂]]
      mkLambdaFVars #[σ₁, σ₂] (← reduceArgProjections (← zetaReduce c))
  let pre ← cond A (mkTupleRead · argSlots₁) (mkTupleRead · argSlots₂)
  let post ← cond B (mkLensGet resPS₁ ·) (mkLensGet resPS₂ ·)
  let target ← mkAppM ``prhlStmt #[pre, body₁, body₂, post]
  let lem ← mkAppOptM ``prhlProc_of_prhlStmt #[some sig₁, some sig₂, some A, some p₁, some p₂,
    some B, some resVA₁, some argsVA₁, some resVA₂, some argsVA₂]
  let .forallE _ hyp _ _ ← whnfR (← inferType lem)
    | throwError "equiv_proc_to_stmt: unexpected type of `prhlProc_of_prhlStmt`"
  unless ← isDefEq hyp target do
    throwError "equiv_proc_to_stmt: the statement built is not the lemma's"
  let g' ← mkFreshExprSyntheticOpaqueMVar target (← g.getTag)
  g.assign (mkApp lem g')
  let g ← Judgment.simpArg g'.mvarId! 0 relSimpDecls []
  Judgment.simpArg g 3 relSimpDecls []

/-- `equiv_proc_to_stmt`: from `equiv[ M₁ ~ M₂ : P ==> Q ]` to the judgment about the call
statements `res <- call Mᵢ (x₁, …, xₙ)` (`equivProcToStmt`); inline them with `stmt_inline 0`.
EC's `proc`, to the bodies, is `equiv_proc` (`Logic/ECProc.lean`). -/
elab "equiv_proc_to_stmt" : tactic => liftMetaTactic1 fun g => some <$> equivProcToStmt g

/-! ## Relational steps -/

/-- `skip ~ skip`: the implication, reads generalized (`generalizeReadsRel`). -/
def equivSkip (g : MVarId) (normDec : Bool := false) : MetaM MVarId := do
  let _ ← prhlGoal g "equiv_skip"
  let gs ← applyLemma ``prhlStmt_skip g
  let #[g] := gs | throwError "equiv_skip: `prhlStmt_skip` left {gs.size} goals"
  generalizeReadsRelOr "equiv_skip" g normDec

/-- `equiv_skip`: at `skip ~ skip` (what `stmt_wp` leaves when the code is all deterministic),
the implication from the precondition to the postcondition, the reads of the two states as
plain values `x₁`, `x₂`. -/
elab "equiv_skip" : tactic => liftMetaTactic1 fun g => some <$> equivSkip g

/-- `equiv_skip`, the `decide` instances normalized first (`TacticMisc.normDecide`), so that every
read is generalized (EC's `auto` uses it). -/
elab "equiv_skip_ec" : tactic => liftMetaTactic1 fun g => some <$> equivSkip g (normDec := true)

/-- **EC's `rnd{i}`**: the last statement of side `i` is a sampling `x <$ d`, which goes by
itself (`prhlStmt_seq_sample_left`/`_right`): the postcondition before it asks `d` lossless and
the postcondition for every value in its support. -/
syntax (priority := high) "equiv_rnd" Judgment.judgmentSide : tactic

elab_rules : tactic
  | `(tactic| equiv_rnd $s:judgmentSide) => withMainContext do
    let some i := Judgment.sideOf? (some s) | throwError "equiv_rnd: no side"
    let g ← getMainGoal
    let _ ← prhlGoal g "equiv_rnd"
    let g ← HoareSplit.hoareSplit 1 g (some i)
    let st ← g.withContext do
      let (d, ty) ← Judgment.descOf g (some i)
      pure (stripLets (ty.getArg! d.stmtArg))
    unless st.isAppOf ``StmtWithHoles.seq &&
        (stripLets (st.getArg! 2)).isAppOf ``StmtWithHoles.sample do
      throwError "equiv_rnd: the last statement of side {i} is not a sampling"
    replaceMainGoal [← Judgment.wpOne g (some i)]

/-- `equiv_rnd f`: the last statements of both sides are samplings `x₁ <$ d₁`, `x₂ <$ d₂`,
coupled along `f` (`prhlStmt_seq_sample`): the postcondition before them asks that `f` push `d₁`
to `d₂`, and the postcondition for every `a` in the support of `d₁` paired with `f a`.  `f` is a
relational term (it may read both states, `§x{1}`, `§x{2}`); without it, the identity. -/
elab "equiv_rnd" f?:(ppSpace colGt term:max)? : tactic => withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_rnd"
  let g ← HoareSplit.hoareSplit 1 g
  g.withContext do
    let ty ← prhlGoal g "equiv_rnd"
    -- an assignment is a sampling from a point mass, and would unify: insist on samplings
    for i in [1, 2] do
      let st := stripLets (ty.getArg! i)
      unless st.isAppOf ``StmtWithHoles.seq &&
          (stripLets (st.getArg! 2)).isAppOf ``StmtWithHoles.sample do
        throwError "equiv_rnd: the last statement of side {i} is not a sampling (deterministic \
          code first: `stmt_wp`):{indentExpr (stripLets (st.getArg! 2))}"
    let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_sample
    let (ms, _, concl) ← forallMetaTelescope (← inferType c)
    unless ← isDefEq concl ty do
      throwError "equiv_rnd: the last statements are not two samplings:{indentExpr ty}"
    let fm := ms[ms.size - 2]!
    let fTy ← instantiateMVars (← inferType fm)
    let f ← match f? with
      | some f => do
          let .forallE _ _ (.forallE _ _ T _) _ := fTy
            | throwError "equiv_rnd: unexpected coupling type{indentExpr fTy}"
          elabRelTerm ty f T
      | none => do
          let ps := mkConst ``ProgramState
          withLocalDeclD `σ₁ ps fun σ₁ => withLocalDeclD `σ₂ ps fun σ₂ => do
            let .forallE _ _ (.forallE _ _ (.forallE _ α _ _) _) _ := fTy
              | throwError "equiv_rnd: unexpected coupling type{indentExpr fTy}"
            let fid ← withLocalDeclD `a α fun a => mkLambdaFVars #[a] a
            mkLambdaFVars #[σ₁, σ₂] fid
    unless ← isDefEq fm f do
      throwError "equiv_rnd: the coupling{indentExpr f}\ndoes not have type{indentExpr fTy}"
    let hJ := ms.back!
    let g' ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (← inferType hJ)) (← g.getTag)
    unless ← isDefEq hJ g' do throwError "equiv_rnd: cannot set the new judgment"
    g.assign (← instantiateMVars (mkAppN c ms))
    let g' ← Judgment.simpArg g'.mvarId! 3 relSimpDecls []
    replaceMainGoal [g']

/-- `equiv_rnd_run k`: the last statement of the left side is a sampling `x₁ <$ d`, and the last
`k` statements of the right side sample from `d` into the same variable
(`prhlStmt_seq_sample_run_right`).  The
postcondition before them asks for that run, as an equation of the right side's run with the
sampling, and the postcondition for every draw. -/
elab "equiv_rnd_run" k:num : tactic => withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_rnd_run"
  let g ← HoareSplit.hoareSplit 1 g (side? := some 1)
  let g ← HoareSplit.hoareSplit k.getNat g (side? := some 2)
  g.withContext do
    let ty ← prhlGoal g "equiv_rnd_run"
    let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_sample_run_right
    let (ms, _, concl) ← forallMetaTelescope (← inferType c)
    unless ← isDefEq concl ty do
      throwError "equiv_rnd_run: the last statement of the left side is not a sampling of the \
        right side's type:{indentExpr ty}"
    -- the variable the right side samples into: by default the left side's
    let setters ← ms.filterM fun m => do
      return (← instantiateMVars (← inferType m)).isAppOf ``Setter
    if h : setters.size = 2 then
      let x₂ := setters[1]
      unless (← instantiateMVars x₂).isMVar == false do
        discard <| isDefEq x₂ (← instantiateMVars setters[0])
    let hJ := ms.back!
    let g' ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (← inferType hJ)) (← g.getTag)
    unless ← isDefEq hJ g' do throwError "equiv_rnd_run: cannot set the new judgment"
    g.assign (← instantiateMVars (mkAppN c ms))
    let g' ← Judgment.simpArg g'.mvarId! 3 relSimpDecls []
    replaceMainGoal [g']

/-- `equiv_while_raw I` (the older form of EC's `while I`, which is `equiv_while`,
`Logic/ECWhileRel.lean`): the last statements of both sides are loops, synchronized by the invariant
`I` (`prhlStmt_seq_while`).  Goals: `body` (the bodies keep `I`, from `I` and the guard), `guard`
(under `I` the guards agree), `exit` (`I` and a false guard give the postcondition), then the
code before the loops, with postcondition `I`. -/
elab "equiv_while_raw " I:term : tactic => withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_while_raw"
  let g ← HoareSplit.hoareSplit 1 g
  g.withContext do
    let ty ← prhlGoal g "equiv_while_raw"
    let Ie ← elabRelCond ty I
    let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_while
    let (ms, _, concl) ← forallMetaTelescope (← inferType c)
    -- `I` is the first implicit argument
    unless ← isDefEq ms[0]! Ie do
      throwError "equiv_while: not a relational condition:{indentExpr (← inferType Ie)}"
    unless ← isDefEq concl ty do
      throwError "equiv_while: the last statements are not two loops:{indentExpr ty}"
    g.assign (← instantiateMVars (mkAppN c ms))
    let n := ms.size
    let gGuard := ms[n - 4]!.mvarId!
    let gBody := ms[n - 3]!.mvarId!
    let gExit := ms[n - 2]!.mvarId!
    let gPre := ms[n - 1]!.mvarId!
    for (m, tag) in [(gGuard, `guard), (gBody, `body), (gExit, `exit)] do
      m.setKind .syntheticOpaque
      m.setTag tag
    gPre.setKind .syntheticOpaque
    let gBody ← Judgment.simpArg gBody 0 relSimpDecls []
    let gGuard ← generalizeReadsRelOr "equiv_while_raw" gGuard
    let gExit ← generalizeReadsRelOr "equiv_while_raw" gExit
    replaceMainGoal [gBody, gGuard, gExit, gPre]

/-- `equiv_while_noframe{i} I V` (the older form of EC's `while{i} I V`, which is
`equiv_while{i}`, `Logic/ECWhileRel.lean`): the last statement of side `i` is a loop, run on that
side only, with
the invariant `I` and the variant `V : ℕ` (both relational, EC's `while{i} I V`;
`prhlStmt_seq_while_left`/`_right`).  Goals: `lossless` (the body terminates under `I` and the
guard), `variant` (the body keeps `I` and decreases `V`, a Hoare triple for each state of the
other side and each value of `V`), `exit` (`I` and a false guard give the postcondition), then
the code before the loop, with postcondition `I`. -/
elab "equiv_while_noframe" s:Judgment.judgmentSide ppSpace I:term:max ppSpace V:term:max : tactic =>
    withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_while"
  let side := (Judgment.sideOf? (some s)).getD 1
  let g ← HoareSplit.hoareSplit 1 g (some side)
  g.withContext do
    let ty ← prhlGoal g "equiv_while"
    let Ie ← elabRelCond ty I
    let Ve ← elabRelTerm ty V (mkConst ``Nat)
    let lem := if side == 1 then ``prhlStmt_seq_while_left else ``prhlStmt_seq_while_right
    let gs ← try applyLemma lem g #[(`I, Ie), (`V, Ve)]
      catch _ => throwError "equiv_while: the last statement of side {side} is not a loop"
    let #[gll, gvar, gExit, gPre] := gs
      | throwError "equiv_while: `{lem}` left {gs.size} goals"
    for (m, tag) in [(gll, `lossless), (gvar, `variant), (gExit, `exit)] do
      m.setTag tag
    let gExit ← generalizeReadsRelOr "equiv_while_noframe" gExit
    replaceMainGoal [gll, gvar, gExit, gPre]

/-- `equiv_seq_last k₁ k₂ : M`: cut both statements, the last `k₁` (left) and `k₂` (right)
statements after the cut, with the relation `M` in between (`prhlStmt_seq`).  Goals: the code
before the cut (to `M`), then the code after it (from `M`). -/
elab "equiv_seq_last " k₁:num ppSpace k₂:num " : " M:term : tactic => withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_seq_last"
  let g ← HoareSplit.hoareSplit k₁.getNat g (some 1)
  let g ← HoareSplit.hoareSplit k₂.getNat g (some 2)
  g.withContext do
    let ty ← prhlGoal g "equiv_seq_last"
    let Me ← elabRelCond ty M
    -- `prhlStmt_seq`'s implicit arguments: `A B C c₁ c₂ d₁ d₂`
    let gs ← applyLemma ``prhlStmt_seq g #[(`B, Me)]
    let #[g₂, g₁] := gs | throwError "equiv_seq_last: `prhlStmt_seq` left {gs.size} goals"
    replaceMainGoal [g₁, g₂]

/-- The call rule without a frame (`prhlStmt_seq_call`, `prhlStmt_seq_call_refl`): what
`equiv_call h` and `equiv_call` do when no framed rule applies (`Logic/ECCallEquiv.lean`), and
`equiv_call_frameless` by name. -/
def equivCallFrameless (h? : Option Term) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_call"
  let g ← HoareSplit.hoareSplit 1 g
  g.withContext do
    let ty ← prhlGoal g "equiv_call"
    let mut extra : List MVarId := []
    let gPre ← match h? with
      | none => do
          let st ← saveState
          let gs ← try applyLemma ``prhlStmt_seq_call_refl g
            catch _ =>
              -- calls of procedures spelled differently: their equality is left as a goal
              st.restore
              try applyLemma ``prhlStmt_seq_call_eq g
              catch _ => throwError "equiv_call: the last statements are not calls of \
                procedures of the same signature (give a procedure judgment: `equiv_call h`):\
                {indentExpr ty}"
          match gs with
          | #[gPre] => pure gPre
          | #[hp, gPre] => do
              hp.setTag `callee
              extra := [hp]
              pure gPre
          | _ => throwError "equiv_call: the call rule left {gs.size} goals"
      | some h => do
          let hE ← elabTerm h none
          Term.synthesizeSyntheticMVarsNoPostponing
          let hE ← instantiateMVars hE
          let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_call
          let (ms, _, concl) ← forallMetaTelescope (← inferType c)
          let isJ (m : Lean.Expr) : TacticM Bool := do
            return (← instantiateMVars (← inferType m)).isAppOf ``prhlProc
          let some hm ← ms.findM? isJ
            | throwError "equiv_call: `prhlStmt_seq_call` has no procedure-judgment argument"
          unless ← isDefEq hm hE do
            throwError "equiv_call: not a procedure judgment:{indentExpr (← inferType hE)}"
          unless ← isDefEq concl ty do
            throwError "equiv_call: the judgment{indentExpr (← inferType hE)}\ndoes not fit the \
              last statements{indentExpr ty}"
          g.assign (← instantiateMVars (mkAppN c ms))
          let gPre := ms.back!.mvarId!
          gPre.setKind .syntheticOpaque
          pure gPre
    replaceMainGoal ((← Judgment.simpArg gPre 3 relSimpDecls []) :: extra)

/-- `equiv_call h`: the last statements of both sides are calls `x₁ <- call p₁ (e₁)`,
`x₂ <- call p₂ (e₂)`, and `h` a procedure judgment `equiv[ p₁ ~ p₂ : P ==> Q ]` about the callees
(`prhlStmt_seq_call`; for an abstract procedure, `prhlProc_glob hA`: EC's
`call (_ : ={glob A})`).  The postcondition before the calls: `P` at the arguments and globals,
and the postcondition after them for all results and globals `Q` relates.

`equiv_call` alone: both calls are of the same procedure (EC's `call (_ : true)` on the same
code, `prhlStmt_seq_call_refl`): the postcondition before them asks for equal arguments and equal
globals, and the postcondition after them for every result and globals, the same on both
sides. -/
elab "equiv_call" h?:(ppSpace colGt term)? : tactic => do
  -- `equiv_call (_ : …)` is one of the call forms with an invariant or a specification
  -- (`Logic/ECCallAbstract.lean`, …), parsed here too (a hole with a type ascription): left to them
  if let some h := h? then
    if let `(term| (_ : $_)) := h then throwUnsupportedSyntax
  equivCallFrameless h?

/-- `equiv_call_frameless h` / `equiv_call_frameless`: the call rule without a frame, by name
(what `equiv_call h` falls back to, with a warning, when the framed rule does not apply). -/
elab "equiv_call_frameless" h?:(ppSpace colGt term)? : tactic => equivCallFrameless h?

/-- `equiv_call_frame X`: `equiv_call` (same procedure on both sides) where the postcondition may
also assume that the variable `X` kept its value through the call
(`prhlStmt_seq_call_refl_frame`).  `X` must lie outside the callee's footprint: the module's own
(`Module.Proc.inFootprint_fvP`, or a hypothesis), the disjointness shown by `fp_disjoint` from the
restriction hypotheses in context.  EC proves such a step with `swap` or `sim`, from its memory
restrictions. -/
elab "equiv_call_frame " X:term : tactic => withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_call_frame"
  let g ← HoareSplit.hoareSplit 1 g
  g.withContext do
    let Xe ← elabTerm X none
    Term.synthesizeSyntheticMVarsNoPostponing
    let gs ← applyLemma ``prhlStmt_seq_call_refl_frame g #[(`X, ← instantiateMVars Xe)]
    let mut gPre? : Option MVarId := none
    for m in gs do
      if ← m.isAssigned then continue
      let t ← instantiateMVars (← m.getType)
      if t.isForall && (← forallTelescope t fun _ b =>
          pure (b.isAppOf ``ProgramDenotation.inFootprint)) then
        -- `applyLemma` made the footprint `?R` synthetic-opaque; the callee's footprint fixes it
        let pf ← withAssignableSyntheticOpaque (StmtSwap.calleeFootprint t)
        unless ← withAssignableSyntheticOpaque (isDefEq (mkMVar m) pf) do
          throwError "equiv_call_frame: cannot use the callee's footprint"
      else if t.isAppOfArity ``LE.le 4 then
        try FootprintSolver.solve m
        catch err => throwError "equiv_call_frame: cannot show that{indentExpr Xe}\nlies \
          outside the callee's footprint: {err.toMessageData}"
      else if (← isProp t) then gPre? := some m
    let some gPre := gPre? | throwError "equiv_call_frame: no precondition goal"
    replaceMainGoal [← Judgment.simpArg gPre 3 relSimpDecls []]

/-- `simp_reads`: simplify the goal with the read-through-write lemmas the judgment tactics use
(`relSimpDecls`: a variable read after writes to other variables, resets, the globals written by a
call), for goals left after unfolding expectations or judgments by hand. -/
elab "simp_reads" : tactic => liftMetaTactic1 fun g => do
  let ty ← instantiateMVars (← g.getType)
  let r ← Judgment.simpWithNames relSimpDecls [] ty
  applySimpResultToTarget g ty r

/-- `phoare_ewp`: on a goal `phoareStmt A s g ρ r` about loop-free code, introduce the state and the
precondition and spell the expectation `s.ewp g σ` out (`Stmt.ewp_seq`, `_ifThenElse`, `_assign`,
`_sample`, `_skip`): samplings become `expected`, conditionals `if`s (also those with a sampling
inside, which `phoare_wp` does not take), calls stay the callee's expectation.  Then
`simp_reads`, and the tests back to propositions.  What is left is about the initial state only. -/
macro "phoare_ewp" : tactic => `(tactic| (
  intro σ _
  try simp only [Stmt.ewp_seq, Stmt.ewp_ifThenElse, Stmt.ewp_assign, Stmt.ewp_sample,
    Stmt.ewp_skip]
  simp_reads
  try simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]))

/-- `if c t e; s` (through the `let`s of the locals) as `if c (t; s) (e; s)`, and the
equivalence (`Stmt.Equiv.seq_ite`); fails on anything else. -/
partial def distribIf (s₀ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let s ← TacticMisc.openStmt s₀
  if let .letE n ty val body _ := s then
    return ← withLetDecl n ty val fun fv => do
      let (r, pr) ← distribIf (body.instantiate1 fv)
      return (← mkLetFVars #[fv] r (usedLetOnly := false),
              ← mkLetFVars #[fv] pr (usedLetOnly := false))
  unless s.isAppOfArity ``StmtWithHoles.seq 3 do throwError "not a sequence"
  let a ← TacticMisc.openStmt (s.getArg! 1)
  unless a.isAppOfArity ``StmtWithHoles.ifThenElse 4 do throwError "not a conditional first"
  let (c, t, e, rest) := (a.getArg! 1, a.getArg! 2, a.getArg! 3, s.getArg! 2)
  let r ← mkAppM ``StmtWithHoles.ifThenElse
      #[c, ← mkAppM ``StmtWithHoles.seq #[t, rest], ← mkAppM ``StmtWithHoles.seq #[e, rest]]
  -- each branch one sequence (`flattenSeq`), as EC's `if` leaves it
  let (r', p') ← TacticMisc.flattenSeq r
  return (r', ← mkAppM ``StmtWithHoles.Equiv.trans
    #[← mkAppM ``Stmt.Equiv.seq_ite #[c, t, e, rest], p'])

/-- `equiv_if`: both statements are conditionals (`prhlStmt_if`): goals `then`, `else` (with the
test true, resp. false, on both sides) and `guard` (the tests agree under the precondition).
`equiv_if{i}`: side `i`'s statement is a conditional (`prhlStmt_if_left`/`_right`, EC's
`if{i}`): goals `then`, `else`, each against the other side.  To reach a conditional inside a
sequence, cut first (`equiv_seq`, `equiv_seq_last`). -/
elab "equiv_if" s:(Judgment.judgmentSide)? : tactic => withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_if"
  -- EC's `if` on the first statement of a sequence: the rest into both branches
  -- (`Stmt.Equiv.seq_ite`)
  let sides := match Judgment.sideOf? s with
    | some i => [i]
    | none => [1, 2]
  let mut g := g
  for i in sides do
    g ← (Judgment.onStmt distribIf g (some i) : MetaM MVarId) <|> (pure g : MetaM MVarId)
  let (lem, tags) := match Judgment.sideOf? s with
    | some 1 => (``prhlStmt_if_left, [`then, `else])
    | some 2 => (``prhlStmt_if_right, [`then, `else])
    | _ => (``prhlStmt_if, [`guard, `then, `else])
  let gs ← applyLemma lem g
  unless gs.size == tags.length do
    throwError "equiv_if: the statements are not conditionals (`{lem}` left {gs.size} goals)"
  let mut out := #[]
  for (m, tag) in gs.toList.zip tags do
    m.setTag tag
    if tag == `guard then
      out := out.push (← generalizeReadsRelOr "equiv_if" m)
    else
      let m' ← Judgment.simpArg m 0 relSimpDecls []
      m'.setTag tag
      out := out.push m'
  -- the branches first, as written
  let ordered := if out.size == 3 then #[out[1]!, out[2]!, out[0]!] else out
  replaceMainGoal ordered.toList

/-- `equiv_rcondf{i}`: the last statement of side `i` is a loop that does not run — its guard
is false where it starts (EC's `rcondf{i}`, for a trailing loop;
`prhlStmt_seq_while_false_left`/`_right`).  The postcondition before it adds the false guard. -/
elab "equiv_rcondf" s:Judgment.judgmentSide : tactic => withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_rcondf"
  let side := (Judgment.sideOf? (some s)).getD 1
  let g ← HoareSplit.hoareSplit 1 g (some side)
  let lem := if side == 1 then ``prhlStmt_seq_while_false_left
    else ``prhlStmt_seq_while_false_right
  let gs ← try applyLemma lem g
    catch _ => throwError "equiv_rcondf: the last statement of side {side} is not a loop"
  let #[g'] := gs | throwError "equiv_rcondf: `{lem}` left {gs.size} goals"
  replaceMainGoal [← Judgment.simpArg g' 3 relSimpDecls []]

/-- `equiv_sym`: swap the two sides (`prhlStmt.symm`, on a procedure judgment `prhlProc.symm`;
EC's `symmetry`). -/
elab "equiv_sym" : tactic => withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  if ty.isAppOfArity ``prhlProc 6 then
    let gs ← applyLemma ``prhlProc_of_symm g
    let #[g'] := gs | throwError "equiv_sym: `prhlProc_of_symm` left {gs.size} goals"
    let g' ← Judgment.simpArg g' 2 [] []
    replaceMainGoal [← Judgment.simpArg g' 5 [] []]
    return
  let _ ← prhlGoal g "equiv_sym"
  let gs ← applyLemma ``prhlStmt_of_symm g
  let #[g'] := gs | throwError "equiv_sym: `prhlStmt_of_symm` left {gs.size} goals"
  let g' ← Judgment.simpArg g' 0 [] []
  replaceMainGoal [← Judgment.simpArg g' 3 [] []]

/-- `equiv_case P`: case analysis on the relation `P` of the initial states
(`prhlStmt_case`): goals with `A ∧ P` and with `A ∧ ¬P` as preconditions. -/
elab "equiv_case " P:term : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← prhlGoal g "equiv_case"
  let Pe ← elabRelCond ty P
  let gs ← applyLemma ``prhlStmt_case g #[(`P, Pe)]
  replaceMainGoal gs.toList

/-- `equiv_sim`: EC's `sim` on straight-line code.  Backwards over both statements, as long as one
of these applies: `stmt_wp` (trailing deterministic code, both sides), `equiv_call` (calls of the
same procedure, or of procedures spelled differently, their equality tried by `rfl` and left as
a `callee` goal otherwise).  When both statements are used up, `equiv_skip`, and the implication
it leaves closed by `simp_all` if it can.  It stops at anything else (a conditional, a loop, a
sampling, calls of different procedures), leaving that goal: cut there with `equiv_seq … : M`. -/
macro "equiv_sim" : tactic => `(tactic| (
  repeat (first
    | fail_if_no_progress stmt_wp
    | (equiv_call; try (case callee => rfl)))
  try (equiv_skip; try (first
    | focus (intros; subst_vars; simp [Setter.throwaway, ProgramState.globalL]; done)
    | focus (intros; simp_all; done)
    | focus (intros; simp_all [Setter.throwaway, ProgramState.globalL]; done)))))

end PRHLWp

end GaudisCrypt
