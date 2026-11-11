import GaudisCrypt.Logic.Fel
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.PHoareSeq

/-!
# EasyCrypt's `fel`, as a tactic

    fel cntr step q bad [pre] inv

on a goal `phoare[ P ==> bad ] ≤ r { s₀; x <- call D(O) (…); }` — `D` a declared module, the call
last (a `wp` first for what follows it) — applies `phoareStmt_fel`, EC's `fel`.  The arguments are
EC's: the counter `cntr` (an `ℤ` read off the state, `§Bounder.bounder`), the bound `step i` for a
call at counter `i`, the number of calls `q`, the event `bad`, the oracle's precondition `pre`
(the calls that may set `bad`), the invariant `inv` — the state-dependent ones written as the
judgment's conditions (`§x`).  What EC needs no words for is done here: the state view the
conditions read (the `global_var`s they mention, paired into one lens `L`), the representation of
`D` and its oracles' signatures (from `declare module` and the oracles' module type `T.ext`), the
disjointness of `D` and `L` (`fp_disjoint`), the result variable `x` outside `L`.

Goals left, in EC's order: `sum` (`∑_{i ∈ [0, q)} step i ≤ r`), `init` (`s₀` establishes `inv`,
`¬ bad`, `cntr = 0`), and per oracle the premises of `FelOracle`: `lt`, `step`, `incr`, `same`,
`keep`.  One oracle for now (EC's `[O₁: pre₁, …]` with several is not needed by the SHA-3 port).
-/

namespace GaudisCrypt.FelTactic

open Lean Meta Elab Tactic

/-- `t` is the read `X.get g` of the lens `X` (`Getter.get (Lens.toGetter X) g`) at `g`: `X`. -/
def readOf? (g t : Lean.Expr) : Option Lean.Expr := do
  guard (t.isAppOfArity ``GaudisCrypt.Getter.get 4 && t.appArg! == g)
  let self := t.getArg! 2
  guard (self.isAppOfArity ``GaudisCrypt.Lens.toGetter 3)
  return self.appArg!

/-- The fields of the structure `n`, if it is one. -/
def getStructureFields? (env : Environment) (n : Name) : Option (Array Name) :=
  if isStructure env n then some (getStructureFields env n) else none

/-- The globals `X` read as `X.get τ.globals` in `e`, in order of first occurrence. -/
def globalReads (τ : Lean.Expr) (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let acc ← IO.mkRef (#[] : Array Lean.Expr)
  let globals := mkApp (mkConst ``GaudisCrypt.ProgramState.globals) τ
  forEachExpr e fun t => do
    if let some X := readOf? globals t then
      unless (← acc.get).contains X do acc.modify (·.push X)
  acc.get

/-- The state function `f : ProgramState → α`, its reads simplified (`X.get τ.globals`), as a
body in the fresh variable `τ`. -/
def readBody (f : Lean.Expr) (τ : Lean.Expr) : MetaM Lean.Expr := do
  let b ← Core.betaReduce (mkApp f τ)
  let r ← Judgment.simpWithNames HoareWp.simpReadsDecls [] b
  instantiateMVars r.expr

/-- The `i`-th of `k` components of `s : X₁ × (X₂ × … Xₖ)`. -/
def proj (s : Lean.Expr) : Nat → Nat → MetaM Lean.Expr
  | _, 1 => pure s
  | 0, _ => mkAppM ``Prod.fst #[s]
  | i + 1, k + 1 => do proj (← mkAppM ``Prod.snd #[s]) i k
  | _, _ => pure s

/-- `body` with each read `Xᵢ.get τ.globals` replaced by the `i`-th component of `s`; fails if `τ`
is still used (a read of a local, or of something not a global). -/
def abstractReads (τ : Lean.Expr) (Xs : Array Lean.Expr) (s : Lean.Expr) (body : Lean.Expr) :
    MetaM Lean.Expr := do
  let globals := mkApp (mkConst ``GaudisCrypt.ProgramState.globals) τ
  let projs ← (Array.range Xs.size).mapM fun i => proj s i Xs.size
  let body' := body.replace fun t => do
    let X ← readOf? globals t
    (Xs.findIdx? (· == X)).map (projs[·]!)
  if body'.containsFVar τ.fvarId! then
    throwError "fel: the condition reads the state other than through global variables:\
      {indentExpr body}"
  return body'

/-- The view of the state functions `fs` (each `ProgramState → _`): the globals they read, paired
into one lens `L` (`Lens.pair`, disjointness by instance search), and each function as a function
of `L`'s value (`f τ` is `f' (L.get τ.globals)` by definition). -/
def inferView (fs : List Lean.Expr) : MetaM (Lean.Expr × Array Lean.Expr) := do
  withLocalDeclD `τ (mkConst ``GaudisCrypt.ProgramState) fun τ => do
    let bodies ← fs.mapM (readBody · τ)
    let mut Xs : Array Lean.Expr := #[]
    for b in bodies do
      for X in ← globalReads τ b do
        unless Xs.contains X do Xs := Xs.push X
    if Xs.isEmpty then throwError "the conditions read no global variable"
    let some last := Xs.back? | unreachable!
    -- `Lens.pair x y [x.Disjoint y]`: the disjointness by instance search
    let L ← (Xs.pop).foldrM (fun X acc => do
      let c ← mkConstWithFreshMVarLevels ``GaudisCrypt.Lens.pair
      let (ms, bis, _) ← forallMetaTelescope (← inferType c)
      let some ix := (List.range ms.size).reverse.find? (bis[·]! == .default)
        | throwError "unexpected `Lens.pair`"
      unless ← isDefEq ms[ix - 1]! X <&&> isDefEq ms[ix]! acc do
        throwError "cannot pair the views{indentExpr X}\nand{indentExpr acc}"
      for m in ms, bi in bis do
        if bi.isInstImplicit && !(← m.mvarId!.isAssigned) then
          m.mvarId!.assign (← synthInstance (← inferType m))
      instantiateMVars (mkAppN c ms)) last
    let LT ← whnfR (← inferType L)
    unless LT.isAppOfArity ``GaudisCrypt.Lens 2 do
      throwError "the view is not a lens:{indentExpr LT}"
    let Ω := LT.getArg! 0
    let fs' ← bodies.toArray.mapM fun b =>
      withLocalDeclD `s Ω fun s => do mkLambdaFVars #[s] (← abstractReads τ Xs s b)
    return (L, fs')

/-- Discharge the side conditions of an abstract call common to `fel` and `hoare_call (: inv)`:
the footprints, the countability of the oracles' arguments, the result outside the view. -/
def closeTagged (tag : Name) (tac : TSyntax `tactic) : TacticM Unit := do
  let gs ← getGoals
  let some g ← gs.findM? (fun g => return (← g.getTag) == tag) | return
  let s ← saveState
  try
    let rest ← evalTacticAt tac g
    unless rest.isEmpty do throwError "not closed"
    setGoals (gs.filter (· != g))
  catch _ => s.restore

/-- The goal tags without macro scopes (the holes of a quotation are hygienic), as `case` names. -/
def untagGoals : TacticM Unit := do
  for g in ← getGoals do g.setTag (← g.getTag).eraseMacroScopes

/-- The last call of an applied module in the goal's statement: `D` and the oracles `O`, the
oracles' module type's `T.ext`. -/
def abstractCall (ty : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Name) := do
  let some callee := ty.find? (·.isAppOfArity ``GaudisCrypt.Module.app 6)
    | throwError "no call of an applied module in{indentExpr ty}"
  let O := callee.getArg! 5
  let T ← whnfR (← inferType O)
  let some C := T.getAppFn.constName?
    | throwError "the oracles' type is not a module type:{indentExpr T}"
  let extC := C ++ `ext
  unless (← getEnv).contains extC do
    throwError "no `{extC}` (the oracles' procedures, `T.ext`) for the module type `{C}`"
  return (mkAppN (← mkConstWithFreshMVarLevels extC) T.getAppArgs, callee.getArg! 4, C)

end FelTactic

open Lean Meta Elab Tactic FelTactic PHoareWp in
/-- **EC's `fel cntr step q bad [pre] inv`** (see the module docstring). -/
elab "fel " cntr:term:max step:term:max q:term:max bad:term:max " [" pres:term,* "] "
    inv:term:max : tactic => do
  -- the statement as `s₀; x <- call D(O) (…)`
  liftMetaTactic1 fun g => some <$> Judgment.onStmt (HoareSplit.splitSeq 1) g
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some callee := ty.find? (·.isAppOfArity ``GaudisCrypt.Module.app 6)
    | throwError "fel: no call of an applied module in{indentExpr ty}"
  let O := callee.getArg! 5
  let T ← whnfR (← inferType O)
  let some C := T.getAppFn.constName?
    | throwError "fel: the oracles' type is not a module type:{indentExpr T}"
  let extC := C ++ `ext
  unless (← getEnv).contains extC do
    throwError "fel: no `{extC}` (the oracles' procedures, `T.ext`) for the module type `{C}`"
  let ext := mkAppN (← mkConstWithFreshMVarLevels extC) T.getAppArgs
  -- the conditions, as functions of the state
  let pres := pres.getElems
  unless pres.size == 1 do
    throwError "fel: one oracle precondition expected (several oracles are not supported yet)"
  let cntrF ← elabGoalFunction cntr (mkConst ``Int)
  let badF ← elabGoalFunction bad (mkSort Level.zero)
  let invF ← elabGoalFunction inv (mkSort Level.zero)
  let preF ← elabGoalFunction pres[0]! (mkSort Level.zero)
  let (stepE, qE) ← withMainContext do
    let s ← Term.elabTermEnsuringType step (← mkArrow (mkConst ``Int) (mkConst ``ENNReal))
    let q ← Term.elabTermEnsuringType q (mkConst ``Int)
    Term.synthesizeSyntheticMVarsNoPostponing
    return (← instantiateMVars s, ← instantiateMVars q)
  -- the view: the globals the conditions read, paired
  let (L, fs) ← g.withContext (inferView [cntrF, badF, invF, preF])
  let (cntr', bad', inv', pre') := (fs[0]!, fs[1]!, fs[2]!, fs[3]!)
  -- the rule, its side conditions discharged, EC's goals left
  let stx ← `(tactic| refine phoareStmt_fel (L := $(← Term.exprToSyntax L))
      (cntr := $(← Term.exprToSyntax cntr')) (step := $(← Term.exprToSyntax stepE))
      (q := $(← Term.exprToSyntax qE)) (bad := $(← Term.exprToSyntax bad'))
      (inv := $(← Term.exprToSyntax inv')) _ $(← Term.exprToSyntax ext)
      (Module.Declared.ecModule _ $(← Term.exprToSyntax ext)).representable ?hdisj ?hc _
      (fun _ => $(← Term.exprToSyntax pre')) ?horacle ?hx ?init ?sum)
  evalTactic stx
  -- the holes of the quotation are hygienic: their tags without macro scopes, as `case` names
  let untag : TacticM Unit := do
    for g in ← getGoals do g.setTag (← g.getTag).eraseMacroScopes
  untag
  -- the goal tagged `tag` (`?tag` in the rule's application, or a field of `FelOracle.mk`)
  let findTagged (gs : List MVarId) (tag : Name) : MetaM (Option MVarId) :=
    gs.findM? fun g => return (← g.getTag) == tag
  let close (tag : Name) (tac : TSyntax `tactic) : TacticM Unit := do
    let gs ← getGoals
    let some g ← findTagged gs tag | return
    let s ← saveState
    try
      let rest ← evalTacticAt tac g
      unless rest.isEmpty do throwError "not closed"
      setGoals (gs.filter (· != g))
    catch e =>
      s.restore
      let _ := e
  close `hdisj (← `(tactic| ((try simp only [Footprint.lens_pair]); fp_disjoint)))
  close `hc (← `(tactic| (apply HoleIndex.forall_single; first
    | infer_instance
    | (dsimp only [ProcedureSignature.ParamType, typeListToTuple]; infer_instance))))
  close `hx (← `(tactic| (intro _ _; rfl)))
  -- the oracle: its premises as goals
  let gs ← getGoals
  if let some go ← findTagged gs `horacle then
    let [go] ← evalTacticAt (← `(tactic| apply HoleIndex.forall_single)) go
      | throwError "fel: one oracle expected"
    -- the oracle's procedure out of `T.ext` and the record (`T.f.mk_simp`)
    let env ← getEnv
    let mkSimps : Array Ident := match getStructureFields? env (C ++ `Structure) with
      | some fs => fs.filterMap fun f =>
          let n := C ++ f ++ `mk_simp
          if env.contains n then some (mkIdent n) else none
      | none => #[]
    let [go] ← evalTacticAt (← `(tactic|
        simp only [$(mkIdent extC):ident, HoleSigs.Instantiation.lookup_zero_single,
          $[$mkSimps:ident],*])) go
      | throwError "fel: the oracle's procedure"
    let rest ← evalTacticAt (← `(tactic| refine FelOracle.mk ?lt ?step ?incr ?same ?keep)) go
    setGoals (gs.filter (· != go) ++ rest)
    untag
  close `lt (← `(tactic| (intros; first | assumption | omega)))
  -- EC's order: the sum, the initialization, the oracle's premises
  let gs ← getGoals
  let order := [`sum, `init, `lt, `step, `incr, `same, `keep]
  let named ← order.filterMapM fun n => findTagged gs n
  setGoals (named ++ gs.filter (fun g => !named.contains g))

open Lean Meta Elab Tactic FelTactic in
/-- **EC's `call (: inv)` on an abstract module**, in a Hoare triple about a statement ending in
`x <- call D(O) (…)` (`D` a declared module): the oracles keep `inv` (goal `oracle`, a triple
about the oracle's procedure), and before the call `inv` holds and every result and globals
keeping it give the postcondition (goal `pre`), in EC's order: `oracle`, then `pre`.  `inv` is written like the triple's conditions;
the state view, the representation, the footprints and the countability are as for `fel`. -/
elab "hoare_call" " (" ": " I:term ")" : tactic => do
  liftMetaTactic1 fun g => some <$> Judgment.onStmt (HoareSplit.splitSeq 1) g
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``GaudisCrypt.hoareStmt 3 do
    throwError "hoare_call (: inv): expected a goal `hoareStmt A s B`, got{indentExpr ty}"
  let (ext, _, C) ← abstractCall ty
  -- `inv` as a function of the state, as `hoare_while` reads its invariant
  let IF ← g.withContext do
    let vars := (← ProgramSyntax.frameVars #[ty.getArg! 0, ty.getArg! 1, ty.getArg! 2] #[]).filter
      (·.nameable)
    let mut stx ← `((GaudiExpr[ $I ] : Getter Prop ProgramState).get)
    for v in vars.reverse do
      let some slot := v.slots[0]? | continue
      stx ← `(letI $(mkIdent (.mkSimple v.name)) := $(← Term.exprToSyntax slot); $stx)
    let e ← Term.elabTermEnsuringType stx (← mkArrow (mkConst ``GaudisCrypt.ProgramState)
      (mkSort Level.zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let (L, fs) ← g.withContext (inferView [IF])
  evalTactic (← `(tactic| refine hoareStmt_call_inv (L := $(← Term.exprToSyntax L)) _
      $(← Term.exprToSyntax ext)
      (Module.Declared.ecModule _ $(← Term.exprToSyntax ext)).representable ?hdisj ?hc _
      $(← Term.exprToSyntax fs[0]!) ?oracle ?pre))
  untagGoals
  closeTagged `hdisj (← `(tactic| ((try simp only [Footprint.lens_pair]); fp_disjoint)))
  closeTagged `hc (← `(tactic| (apply HoleIndex.forall_single; first
    | infer_instance
    | (dsimp only [ProcedureSignature.ParamType, typeListToTuple]; infer_instance))))
  -- the oracle's triple, its procedure out of `T.ext` and the record (`T.f.mk_simp`)
  let gs ← getGoals
  if let some go ← gs.findM? (fun g => return (← g.getTag) == `oracle) then
    let [go'] ← evalTacticAt (← `(tactic| apply HoleIndex.forall_single)) go
      | throwError "hoare_call (: inv): one oracle expected"
    let env ← getEnv
    let mkSimps : Array Ident := match getStructureFields? env (C ++ `Structure) with
      | some fs => fs.filterMap fun f =>
          let n := C ++ f ++ `mk_simp
          if env.contains n then some (mkIdent n) else none
      | none => #[]
    let extC := C ++ `ext
    let rest ← evalTacticAt (← `(tactic|
        simp only [$(mkIdent extC):ident, HoleSigs.Instantiation.lookup_zero_single,
          $[$mkSimps:ident],*])) go'
    setGoals (gs.filter (· != go) ++ rest)
    for r in rest do r.setTag `oracle
  untagGoals
  -- EC's order: the oracle, then the code before the call
  let gs ← getGoals
  let named ← [`oracle, `pre].filterMapM fun n => gs.findM? fun g => return (← g.getTag) == n
  setGoals (named ++ gs.filter (fun g => !named.contains g))

end GaudisCrypt
