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
  /-- The position of the postcondition (the condition wp steps rewrite) among the head's
  arguments. -/
  postArg : Nat := 2
  /-- `J A s (fun σ => B (upd σ)) … → J A (s; d) B …` from `d.Det upd` (`Stmt.Det`): the wp rule
  for deterministic code, the same in every judgment.  Arguments by unification, the `Det` proof
  by its type, the judgment about `s` last. -/
  detLemma : Option Name := none
  /-- The judgment's rule for a trailing sampling `x <$ e`: `J A s ‹post'› … → J A (s; x <$ e) B …`.
  Judgment-specific (`∀ a ∈ support` for Hoare triples, an average for `phoare`). -/
  sampleLemma : Option Name := none
  /-- The judgment's rule for a trailing call without a specification, if it has one (`phoare`:
  the callee's expectation, symbolically). -/
  callLemma : Option Name := none
  /-- Simp lemmas (theorems rewritten with, definitions unfolded) and simprocs for the
  postcondition after each wp step: reads through writes, and whatever the judgment's
  conditions need. -/
  postSimp : List Name := []
  postSimprocs : List Name := []
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

/-! ## Deterministic statements

A statement is deterministic if it maps the state by a function `upd` and always terminates:
then its weakest precondition, for a postcondition of *any* kind, is the postcondition after
`upd`.  `Stmt.Det d upd` says this of the wp, which is all the rules use. -/

/-- `d` runs as the state update `upd`: its wp of any postcondition is that postcondition after
`upd`. -/
def Stmt.Det (d : Stmt) (upd : ProgramState → ProgramState) : Prop :=
  ∀ (f : Unit × ProgramState → ENNReal) (σ : ProgramState),
    (programDenotation d).wp f σ = f ((), upd σ)

theorem Stmt.Det.skip : Stmt.Det (StmtWithHoles.skip) id := fun f σ => by
  simp only [programDenotation, ProgramDenotation.skip, wp_pure, id]

theorem Stmt.Det.assign {α} (x : Setter α ProgramState) (e : Getter α ProgramState) :
    Stmt.Det (StmtWithHoles.assign x e) (fun σ => x.set (e.get σ) σ) := fun f σ => by
  simp only [StmtWithHoles.assign, programDenotation, wp_bind, wp_get_g, wp_lift, wp_set_g,
    AsGetter.toG, AsSetter.toS, id_eq, expected_pure]

theorem Stmt.Det.seq {p q : Stmt} {up uq : ProgramState → ProgramState} (hp : Stmt.Det p up)
    (hq : Stmt.Det q uq) : Stmt.Det (StmtWithHoles.seq p q) (fun σ => uq (up σ)) := fun f σ => by
  simp only [programDenotation, wp_bind]
  rw [hp]
  exact hq f (up σ)

theorem Stmt.Det.ite {c : Getter Bool ProgramState} {p q : Stmt}
    {up uq : ProgramState → ProgramState} (hp : Stmt.Det p up) (hq : Stmt.Det q uq) :
    Stmt.Det (StmtWithHoles.ifThenElse c p q) (fun σ => if c.get σ then up σ else uq σ) :=
  fun f σ => by
    simp only [programDenotation, wp_bind, wp_get_g, AsGetter.toG, id_eq, wp_ite]
    cases c.get σ
    · exact hq f σ
    · exact hp f σ

/-- A read of a conditional state is the conditional of the reads — what a deterministic `if`
leaves in a postcondition (`Stmt.Det.ite` updates the state conditionally). -/
theorem Getter.get_ite {α m : Type*} (g : Getter α m) (c : Prop) [Decidable c] (a b : m) :
    g.get (if c then a else b) = if c then g.get a else g.get b :=
  apply_ite _ _ _ _

theorem ProgramState.globals_ite (c : Prop) [Decidable c] (a b : ProgramState) :
    (if c then a else b).globals = if c then a.globals else b.globals :=
  apply_ite _ _ _ _

/-- A statement with the `let`s on its spine substituted and metadata dropped. -/
partial def stripLets : Lean.Expr → Lean.Expr
  | .letE _ _ v b _ => stripLets (b.instantiate1 v)
  | .mdata _ b => stripLets b
  | e => e

/-- The state update of a deterministic statement, and the proof of `Stmt.Det`, built from its
syntax: assignments (resets included), `skip`, sequences and conditionals of those.  `none` for
anything else (sampling, calls, loops).  `let`s on the statement are zeta-reduced. -/
partial def detOf? (s : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let s := stripLets (← instantiateMVars s)
  match s.getAppFn.constName? with
  | some ``StmtWithHoles.skip =>
      let pf ← mkConstWithFreshMVarLevels ``Stmt.Det.skip
      return some (← mkAppOptM ``id #[mkConst ``ProgramState], pf)
  | some ``StmtWithHoles.assign =>
      let (x, e) := (s.getArg! 2, s.getArg! 3)
      let pf ← mkAppM ``Stmt.Det.assign #[x, e]
      let ty ← inferType pf
      return some (ty.appArg!, pf)
  | some ``StmtWithHoles.seq =>
      let some (_, hp) ← detOf? (s.getArg! 1) | return none
      let some (_, hq) ← detOf? (s.getArg! 2) | return none
      let pf ← mkAppM ``Stmt.Det.seq #[hp, hq]
      return some ((← inferType pf).appArg!, pf)
  | some ``StmtWithHoles.ifThenElse =>
      let some (_, hp) ← detOf? (s.getArg! 2) | return none
      let some (_, hq) ← detOf? (s.getArg! 3) | return none
      let pf ← mkAppOptM ``Stmt.Det.ite #[some (s.getArg! 1), none, none, none, none, some hp,
        some hq]
      return some ((← inferType pf).appArg!, pf)
  | _ => return none

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
