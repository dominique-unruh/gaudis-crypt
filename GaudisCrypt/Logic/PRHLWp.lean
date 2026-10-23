import GaudisCrypt.Logic.HoareWp
import GaudisCrypt.Syntax.PRHLSyntax
import GaudisCrypt.Logic.StmtSwap

/-!
# Tactics for relational judgments (pRHL)

`prhlStmt` registers one descriptor per side with the judgment registry (`Logic/Judgment.lean`),
so the generic statement steps work on it, on both sides or on one (`{1}`, `{2}`):

* `stmt_inline n`, `stmt_inline{i} n` — inline call site `n` (EC's `inline`);
* `stmt_split k`, `stmt_split{i} k` — regroup the last `k` statements;
* `stmt_wp`, `stmt_wp k`, `stmt_wp{i} k` — wp over deterministic code (EC's `wp`); over a
  sampling on one side, `rnd{i}` (the distribution must be lossless).

And the relational steps proper:

* `equiv_proc` — from `equiv[ M₁ ~ M₂ : P ==> Q ]` to the judgment about the two call statements
  (EC's `proc`, with the calls then inlined by `stmt_inline 0`);
* `equiv_rnd`, `equiv_rnd f` — the two last statements are samplings, coupled along `f`
  (default: the identity) (EC's `rnd`);
* `equiv_while I` — synchronized loops with the invariant `I` (EC's `while I`);
* `equiv_call h` — the last statements are calls, related by the procedure judgment `h` (EC's
  `call`; `prhlProc_glob hA` for an abstract procedure, EC's `call (_ : ={glob A})`);
  `equiv_call` alone for calls of the same procedure from equal arguments and globals;
* `equiv_seq k₁ k₂ : M` — cut after all but the last `k₁` / `k₂` statements (EC's `seq`);
* `equiv_case P` — case analysis on a relation of the initial states (EC's `case`);
* `equiv_if`, `equiv_if{i}` — conditionals on both sides, or on one (EC's `if`, `if{i}`);
* `equiv_sym` — swap the sides;
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

/-- On a goal `∀ σ₁ σ₂ : ProgramState, P σ₁ σ₂`: `generalizeReads` for both states — every read
of `σ₁` becomes a value `x₁`, every read of `σ₂` a value `x₂` (named after the variable), and the
states are dropped if nothing else mentions them.  Where the globals themselves occur (`§allGlobals`,
the globals a call leaves), they become a value `globals₁`/`globals₂` first, and the reads of
global variables stay reads of it (`x.get globals₁`), so nothing is lost. -/
def generalizeReadsRel (g : MVarId) : MetaM MVarId := g.withContext do
  let (fvs, g) ← g.introN 2
  let #[σ₁, σ₂] := fvs | throwError "generalizeReadsRel: expected two states"
  let (gvs, g) ← g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let g ← g.change (← unfoldReads σ₂ (← unfoldReads σ₁ ty))
    let body ← instantiateMVars (← g.getType)
    let mut args : Array GeneralizeArg := #[]
    for (σ, n) in [(σ₁, "globals₁"), (σ₂, "globals₂")] do
      if bareGlobals σ body then
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
  let vars := (← ProgramSyntax.frameVars goalTy.getAppArgs #[]).filter (·.printable)
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

/-- The goal's type, checked to be a `prhlStmt` judgment. -/
def prhlGoal (g : MVarId) (tac : String) : MetaM Lean.Expr := do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``prhlStmt 4 do
    throwError "{tac}: expected a relational judgment `prhlStmt A c₁ c₂ B`, got{indentExpr ty}"
  return ty

/-! ## From procedures to statements -/

/-- On a goal `prhlProc A p₁ p₂ B`: the judgment about the two call statements
`res <- call pᵢ (x₁, …, xₙ)`, one local variable per parameter (`prhlProc_of_prhlStmt`), the
conditions with the reads simplified. -/
def equivProcToStmt (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``prhlProc 6 do
    throwError "equiv_proc: expected a procedure judgment `prhlProc A p₁ p₂ B`, got{indentExpr ty}"
  let #[sig₁, sig₂, A, p₁, p₂, B] := ty.getAppArgs | unreachable!
  let va := mkConst ``VariableAssignment
  let ps := mkConst ``ProgramState
  -- the slots of one side: the result, the parameters, the call statement
  let side (sig p : Lean.Expr) :
      MetaM (Lean.Expr × Lean.Expr × Lean.Expr × List Lean.Expr × Lean.Expr) := do
    let some tys ← ModuleDecl.listLit? (← whnf (mkApp (mkConst ``ProcedureSignature.params) sig))
      | throwError "the parameter list of{indentExpr sig}\nis not a list literal"
    let ret ← whnf (mkApp (mkConst ``ProcedureSignature.ret) sig)
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
    | throwError "equiv_proc: unexpected type of `prhlProc_of_prhlStmt`"
  unless ← isDefEq hyp target do
    throwError "equiv_proc: the statement built is not the lemma's"
  let g' ← mkFreshExprSyntheticOpaqueMVar target (← g.getTag)
  g.assign (mkApp lem g')
  let g ← Judgment.simpArg g'.mvarId! 0 relSimpDecls []
  Judgment.simpArg g 3 relSimpDecls []

/-- `equiv_proc`: from `equiv[ M₁ ~ M₂ : P ==> Q ]` to the judgment about the call statements
`res <- call Mᵢ (x₁, …, xₙ)` (`equivProcToStmt`); inline them with `stmt_inline 0`. -/
elab "equiv_proc" : tactic => liftMetaTactic1 fun g => some <$> equivProcToStmt g

/-! ## Relational steps -/

/-- `skip ~ skip`: the implication, reads generalized (`generalizeReadsRel`). -/
def equivSkip (g : MVarId) : MetaM MVarId := do
  let _ ← prhlGoal g "equiv_skip"
  let gs ← applyLemma ``prhlStmt_skip g
  let #[g] := gs | throwError "equiv_skip: `prhlStmt_skip` left {gs.size} goals"
  try generalizeReadsRel g catch _ => pure g

/-- `equiv_skip`: at `skip ~ skip` (what `stmt_wp` leaves when the code is all deterministic),
the implication from the precondition to the postcondition, the reads of the two states as
plain values `x₁`, `x₂`. -/
elab "equiv_skip" : tactic => liftMetaTactic1 fun g => some <$> equivSkip g

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

/-- `equiv_while I`: the last statements of both sides are loops, synchronized by the invariant
`I` (`prhlStmt_seq_while`).  Goals: `body` (the bodies keep `I`, from `I` and the guard), `guard`
(under `I` the guards agree), `exit` (`I` and a false guard give the postcondition), then the
code before the loops, with postcondition `I`. -/
elab "equiv_while " I:term : tactic => withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_while"
  let g ← HoareSplit.hoareSplit 1 g
  g.withContext do
    let ty ← prhlGoal g "equiv_while"
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
    let gGuard ← try generalizeReadsRel gGuard catch _ => pure gGuard
    let gExit ← try generalizeReadsRel gExit catch _ => pure gExit
    replaceMainGoal [gBody, gGuard, gExit, gPre]

/-- `equiv_seq k₁ k₂ : M`: cut both statements, the last `k₁` (left) and `k₂` (right)
statements after the cut, with the relation `M` in between (`prhlStmt_seq`).  Goals: the code
before the cut (to `M`), then the code after it (from `M`). -/
elab "equiv_seq " k₁:num ppSpace k₂:num " : " M:term : tactic => withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_seq"
  let g ← HoareSplit.hoareSplit k₁.getNat g (some 1)
  let g ← HoareSplit.hoareSplit k₂.getNat g (some 2)
  g.withContext do
    let ty ← prhlGoal g "equiv_seq"
    let Me ← elabRelCond ty M
    -- `prhlStmt_seq`'s implicit arguments: `A B C c₁ c₂ d₁ d₂`
    let gs ← applyLemma ``prhlStmt_seq g #[(`B, Me)]
    let #[g₂, g₁] := gs | throwError "equiv_seq: `prhlStmt_seq` left {gs.size} goals"
    replaceMainGoal [g₁, g₂]

/-- `equiv_call h`: the last statements of both sides are calls `x₁ <- call p₁ (e₁)`,
`x₂ <- call p₂ (e₂)`, and `h` a procedure judgment `equiv[ p₁ ~ p₂ : P ==> Q ]` about the callees
(`prhlStmt_seq_call`; for an abstract procedure, `prhlProc_glob hA`: EC's
`call (_ : ={glob A})`).  The postcondition before the calls: `P` at the arguments and globals,
and the postcondition after them for all results and globals `Q` relates.

`equiv_call` alone: both calls are of the same procedure (EC's `call (_ : true)` on the same
code, `prhlStmt_seq_call_refl`): the postcondition before them asks for equal arguments and equal
globals, and the postcondition after them for every result and globals, the same on both
sides. -/
elab "equiv_call" h?:(ppSpace colGt term)? : tactic => withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_call"
  let g ← HoareSplit.hoareSplit 1 g
  g.withContext do
    let ty ← prhlGoal g "equiv_call"
    let gPre ← match h? with
      | none => do
          let gs ← try applyLemma ``prhlStmt_seq_call_refl g
            catch _ => throwError "equiv_call: the last statements are not calls of the same \
              procedure (give a procedure judgment: `equiv_call h`):{indentExpr ty}"
          let #[gPre] := gs
            | throwError "equiv_call: `prhlStmt_seq_call_refl` left {gs.size} goals"
          pure gPre
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
    replaceMainGoal [← Judgment.simpArg gPre 3 relSimpDecls []]

/-- `equiv_if`: both statements are conditionals (`prhlStmt_if`): goals `then`, `else` (with the
test true, resp. false, on both sides) and `guard` (the tests agree under the precondition).
`equiv_if{i}`: side `i`'s statement is a conditional (`prhlStmt_if_left`/`_right`, EC's
`if{i}`): goals `then`, `else`, each against the other side.  To reach a conditional inside a
sequence, cut first (`equiv_seq`). -/
elab "equiv_if" s:(Judgment.judgmentSide)? : tactic => withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_if"
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
      out := out.push (← try generalizeReadsRel m catch _ => pure m)
    else
      let m' ← Judgment.simpArg m 0 relSimpDecls []
      m'.setTag tag
      out := out.push m'
  -- the branches first, as written
  let ordered := if out.size == 3 then #[out[1]!, out[2]!, out[0]!] else out
  replaceMainGoal ordered.toList

/-- `equiv_sym`: swap the two sides (`prhlStmt.symm`). -/
elab "equiv_sym" : tactic => withMainContext do
  let g ← getMainGoal
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

end PRHLWp

end GaudisCrypt
