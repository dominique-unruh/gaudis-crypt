import GaudisCrypt.Logic.StmtEquiv

/-!
# Judgments about statements, generically

Many proof steps change only the *statement* of a judgment — regrouping a sequence, inlining a
call — and prove the old statement equivalent to the new one, possibly along a renaming lens
(`StmtWithHoles.Equiv`, `StmtWithHoles.EquivInLens`).  What differs between `hoareStmt`,
`phoareStmt` (and later the two sides of a relational judgment) is only how the judgment is
transported along that equivalence.  A `JudgmentDesc` records exactly that, and the steps are
implemented once, for every registered judgment:

* `Judgment.onStmt` — rewrite the statement with a `Stmt.Equiv` proof (`hoare_split`, …);
* `Judgment.inline` (`Logic/Inline.lean`) — rewrite along `EquivInLens`, reading the conditions
  through the renaming.

A judgment registers itself (`registerJudgment`) in a file that imports this one — the registry
is an environment extension, which exists only downstream of its declaring file; Hoare triples
register in `Logic/TacticMisc.lean`.  The generic steps find the descriptor from the goal's head
constant.
-/

namespace GaudisCrypt

open Lean Meta

/-- How a judgment about one statement is transported along an equivalence of statements. -/
structure JudgmentDesc where
  /-- The head constant of the judgment (`hoareStmt`). -/
  head : Name
  /-- The position of the statement among the head's arguments. -/
  stmtArg : Nat
  /-- `J … s' … → J … s …` from `s.Equiv s'`, conditions unchanged (`hoareStmt_of_equiv`).  Its
  arguments are found by unification: one of type `_.Equiv _` (or `EquivInLens`), and the
  judgment about `s'` last. -/
  equivLemma : Name
  /-- `J … s' … → J … s …` from `s.EquivInLens s' l`, with one equation
  `(fun τ => C (l.get τ)) = C'` per condition `C` (`hoareStmt_of_equivInLens`).  Arguments found
  as for `equivLemma`; each equation by its type. -/
  transportLemma : Name
  /-- Simp lemmas (theorems rewritten with, definitions unfolded) run on a condition after the
  inliner's own cleaning, e.g. to put an expectation in the form the judgment's tactics expect. -/
  condSimp : List Name := []
  /-- Simprocs run along with `condSimp`. -/
  condSimprocs : List Name := []
  deriving Inhabited

/-- The registered judgments, by head constant. -/
initialize judgmentExt :
    SimplePersistentEnvExtension JudgmentDesc (NameMap JudgmentDesc) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m d => m.insert d.head d
    addImportedFn := fun ess => ess.foldl (fun m es => es.foldl (fun m d => m.insert d.head d) m) {}
  }

/-- Register a judgment (in the file that proves its transport lemmas). -/
def registerJudgment (d : JudgmentDesc) : CoreM Unit :=
  modifyEnv (judgmentExt.addEntry · d)

/-- The descriptor of a goal's judgment, if its head is registered. -/
def judgmentOf? (ty : Lean.Expr) : CoreM (Option JudgmentDesc) := do
  let some c := ty.getAppFn.constName? | return none
  return (judgmentExt.getState (← getEnv)).find? c

namespace Judgment

/-- The descriptor of the goal `g`'s judgment, or an error naming the registered ones. -/
def descOf (g : MVarId) : MetaM (JudgmentDesc × Lean.Expr) := do
  let ty ← instantiateMVars (← g.getType)
  let some d ← judgmentOf? ty
    | let known := (judgmentExt.getState (← getEnv)).toList.map (·.1)
      throwError "not a goal about a statement judgment (registered: {known}):{indentExpr ty}"
  unless ty.getAppNumArgs > d.stmtArg do
    throwError "the judgment `{d.head}` is not fully applied:{indentExpr ty}"
  return (d, ty)

/-- Simplify `e` with `simp only` over the declarations `decls` (theorems rewritten with,
definitions unfolded) and the simprocs `procs` along with the default ones. -/
def simpWithNames (decls procs : List Name) (e : Lean.Expr) : MetaM Simp.Result := do
  let mut thms : SimpTheorems := {}
  for n in decls do
    if (← getConstInfo n) matches .thmInfo _ then thms ← thms.addConst n
    else thms ← thms.addDeclToUnfold n
  let mut sp ← Simp.getSimprocs
  for n in procs do sp ← sp.add n (post := true)
  let ctx ← Simp.mkContext (config := { decide := true }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← simp e ctx #[sp]).1

/-- Is `t` (up to instantiation) the type of a statement equivalence? -/
def isEquivType (t : Lean.Expr) : MetaM Bool := do
  let t ← whnfR (← instantiateMVars t)
  return t.isAppOf ``StmtWithHoles.EquivInLens || t.isAppOf ``StmtWithHoles.Equiv

/-- Apply the transport lemma `lem` of `d` to the goal `g` (of type `ty`) with the equivalence
proof `p`: unify the lemma's conclusion with the goal, the equivalence argument with `p`, and run
`solveEq` on each remaining equation argument; the judgment about the new statement is returned
as the new goal. -/
def applyTransport (d : JudgmentDesc) (lem : Name) (g : MVarId) (ty p : Lean.Expr)
    (solveEq : Lean.Expr → MetaM Simp.Result) : MetaM MVarId := do
  let c ← mkConstWithFreshMVarLevels lem
  let (ms, _, concl) ← forallMetaTelescope (← inferType c)
  unless ← isDefEq concl ty do
    throwError "`{lem}` does not apply to{indentExpr ty}"
  let some he ← ms.findM? fun m => do isEquivType (← inferType m)
    | throwError "`{lem}` has no statement-equivalence argument"
  unless ← isDefEq he p do
    throwError "`{lem}`: the equivalence{indentExpr (← inferType p)}\ndoes not fit"
  let some hJ := ms.back? | throwError "`{lem}` has no arguments"
  unless (← instantiateMVars (← inferType hJ)).isAppOf d.head do
    throwError "`{lem}`: its last argument is not a `{d.head}` judgment"
  -- the equations, one per condition: `(fun τ => C (l.get τ)) = ?C'`
  for m in ms do
    if ← m.mvarId!.isAssigned then continue
    let t ← instantiateMVars (← inferType m)
    let some (_, lhs, rhs) := t.eq? | continue
    let r ← solveEq lhs
    unless ← isDefEq rhs r.expr do
      throwError "`{lem}`: cannot set the condition{indentExpr rhs}"
    m.mvarId!.assign (← r.getProof)
  let g' ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (← inferType hJ)) (← g.getTag)
  unless ← isDefEq hJ g' do throwError "`{lem}`: cannot set the new judgment"
  g.assign (← instantiateMVars (mkAppN c ms))
  return g'.mvarId!

/-- On a goal about a registered judgment: rewrite its statement with `f`, which returns the new
statement `s'` and a proof of `s.Equiv s'` (as `flattenSeq` and `HoareSplit.splitSeq` do), and
continue with the judgment about `s'`, conditions unchanged. -/
def onStmt (f : Lean.Expr → MetaM (Lean.Expr × Lean.Expr)) (g : MVarId) : MetaM MVarId :=
  g.withContext do
    let (d, ty) ← descOf g
    let (_, p) ← f (ty.getArg! d.stmtArg)
    applyTransport d d.equivLemma g ty p fun e => return { expr := e }

end Judgment

end GaudisCrypt
