import GaudisCrypt.Logic.ConcreteFootprint
import GaudisCrypt.Logic.DeclareModule

/-!
# Footprints of concrete modules, read off their code

EasyCrypt reads a concrete module's globals off its code: no lemma states what `Bounder` or
`D1(A)` touches.  Here the same, for the footprint solver:

* `fp_disjoint` (this file's elaborator, extending `Logic/FootprintSolver.lean`'s): a concrete
  `module` `M` with no `@[fp_bound]` bound is bounded by the globals its code mentions
  (`DeclareModule.globalVarsOf`, through the modules and definitions it uses) and the abstract
  modules among its Lean arguments, `FVP.fvP M ≤ FVP.fvP A ⊔ (Lens.pair x₁ (… xₙ)).footprint`,
  proven by `fp_module`;
* `fp_finite`: `F.FinitelySupported` for a join of module footprints and variables, the modules
  declared (`Module.Declared`, `Module.ECModule`) or concrete (bounded as above);
* `ec_module`: `Module.ECModule D ext` for a concrete `D` over a first-order module type, its
  representability `Module.representable_of_firstOrder`, its finite support `fp_finite`.
-/

namespace GaudisCrypt.ModuleFootprint

open Lean Meta Elab Tactic

/-- `c` is a `module` (its definition mentions procedures `c.f`, `isModuleProc`). -/
def isModule (env : Environment) (c : Name) : Bool := Id.run do
  let some ci := env.find? c | return false
  let some v := ci.value? | return false
  return v.getUsedConstants.any fun d => d.getPrefix == c && isModuleProc env d

/-- A bound `FVP.fvP M ≤ B` for the concrete module `M` (a `module` applied to its Lean
arguments): `B` the footprint of its abstract module argument (at most one) and of the globals of
its code, proven by `fp_module`. -/
def concreteBound (M : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let M ← instantiateMVars M
  let env ← getEnv
  -- `Module.proc p` unfolded (`⟨(ModuleExpression.proc p).reduce, …⟩`, what a solver leaves
  -- after unfolding definitions): folded back, by definition
  let M ← do
    if M.isAppOfArity ``Module.mk 4 then
      let e := M.getArg! 1
      if e.isAppOfArity ``ModuleExpression.reduce 1 && e.appArg!.isAppOf ``ModuleExpression.proc then
        if let some M' ← observing? (mkAppM ``Module.proc #[e.appArg!.appArg!]) then
          pure M' else pure M
      else pure M
    else pure M
  -- a `module`'s procedure as a procedure module, `Module.proc (X.f.procedure args)` (what a
  -- call inside inlined code names): read off `X.f.procedure`'s code, at `args`
  let (hd, hdArgs) ← do
    if M.isAppOf ``Module.proc then
      let P := M.appArg!
      let some c := P.getAppFn.constName? | return none
      unless c.getString! == "procedure" && env.contains c.getPrefix do return none
      pure (P.getAppFn, P.getAppArgs)
    else pure (M.getAppFn, M.getAppArgs)
  let some c := hd.constName? | return none
  -- an alias of a clone stands for the theory's module; a `module`'s procedure (`X.f`, ordinary
  -- or an alias) is bounded as a module is
  let b := cloneBase env c
  unless M.isAppOf ``Module.proc || isModule env b || isModuleProc env b do
    return none
  -- the abstract modules among the explicit arguments
  let binfos ← forallTelescope (← getConstInfo c).type fun xs _ =>
    xs.mapM fun x => x.fvarId!.getBinderInfo
  let mut mods : Array Lean.Expr := #[]
  -- the global variables passed as lens arguments (`RO.asRO … RO.m`): the module's code writes
  -- its parameter, which is them
  let mut argLenses : Array Lean.Expr := #[]
  for a in hdArgs, bi in binfos do
    if bi.isExplicit then
      if let some fa ← observing? (mkAppM ``FVP.fvP #[a]) then mods := mods.push fa
      else if let some d := a.getAppFn.constName? then
        if DeclareModule.isGlobalVar env d then argLenses := argLenses.push a
  if mods.size > 1 then return none
  let vars := DeclareModule.globalVarsOf env #[c]
  Term.TermElabM.run' do
    -- the variables, their implicit arguments (the theory's types) by unification and instances
    let lenses ← vars.mapM fun v => do
      let e ← Term.elabTerm (mkCIdent v) none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let lenses := lenses ++ argLenses.filter fun a => !lenses.contains a
    let lensT ← match lenses.back? with
      | none => pure none
      | some last => do
        let mut acc ← Term.exprToSyntax last
        for l in (lenses.pop).reverse do
          acc ← `(Lens.pair $(← Term.exprToSyntax l) $acc)
        pure (some acc)
    let L? ← lensT.mapM fun t => do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let varsB ← L?.mapM fun L => mkAppM ``Lens.footprint #[L]
    let B ← match mods[0]?, varsB with
      | some m, some v => mkAppM ``Max.max #[m, v]
      | some m, none => pure m
      | none, some v => pure v
      | none, none => do
        -- a module with no globals at all (`RF(R)`, its procedures `R`'s): `⊥`, elaborated (the
        -- universe levels of `Footprint VariableAssignment` are not `0`)
        let e ← Term.elabTerm (← `((⊥ : Footprint VariableAssignment))) none
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e
    let goal ← mkAppM ``LE.le #[← mkAppM ``FVP.fvP #[M], B]
    let mv ← mkFreshExprSyntheticOpaqueMVar goal
    let tac ← match lensT with
      | some t => `(tactic| fp_module $t)
      | none => `(tactic| fp_module)
    -- without error recovery: a goal `fp_module` cannot close is a failure here, not a `sorry`
    -- in a bound that is then cached (and an error logged in the caller's proof); `SimLast(S)`,
    -- its argument's variables met in its code, was one
    let log ← Core.getMessageLog
    Core.resetMessageLog
    try
      let gs ← try Term.withoutErrToSorry <| Tactic.run mv.mvarId! (withoutRecover (evalTactic tac))
        catch _ => return none
      unless gs.isEmpty do return none
      if (← Core.getMessageLog).hasErrors then return none
      let pf ← instantiateMVars mv
      if pf.hasSorry then return none
      return some pf
    finally
      Core.setMessageLog log

/-- A cached bound: the module, the proof (if any), and the proof's free variables and constants
(collected once: the proof is a large shared term, and walking it on each use, as
`Expr.hasAnyFVar` does, without sharing, took 0.7 s per lookup under `Gext.M.f`). -/
structure BoundEntry where
  M : Lean.Expr
  pf : Option Lean.Expr
  fvars : Array FVarId
  consts : Array Name

/-- The bounds found so far (`concreteBound` is slow: `fp_module` over the module's code), shared
by the tactic runs of a file: an entry is used only where all its free variables are in scope. -/
initialize boundCache : IO.Ref (Array BoundEntry) ← IO.mkRef #[]

/-- `concreteBound`, each module bounded once (`boundCache`). -/
def cachedBound : FootprintSolver.BoundHook := fun M => do
  let M ← instantiateMVars M
  let lctx ← getLCtx
  let env ← getEnv
  -- its free variables in context, its constants in the environment (not those of a state since
  -- rolled back), no metavariables
  let inScope (e : Lean.Expr) : Bool :=
    !e.hasAnyFVar (fun f => (lctx.find? f).isNone) && !e.hasMVar &&
      e.getUsedConstants.all env.contains
  if inScope M then
    if let some en := (← boundCache.get).find? fun en =>
        en.M == M && en.fvars.all lctx.contains && en.consts.all env.contains then
      return en.pf
  let pf ← concreteBound M
  if inScope M then
    -- a proof with metavariables is not kept (as before: `inScope` failed on it)
    unless pf.any (·.hasMVar) do
      let fvars := match pf with
        | some p => (collectFVars {} p).fvarIds
        | none => #[]
      let consts := match pf with
        | some p => p.getUsedConstants
        | none => #[]
      boundCache.modify (·.push { M, pf, fvars, consts })
  return pf

/-- The footprints read off the code, for every caller of the solver. -/
initialize FootprintSolver.defaultBoundHook.set cachedBound

/-- A proof of `F.FinitelySupported`: a join of variables (`global_var`s, `module_var`s, pairs of
them) and module footprints, each module declared (`Module.Declared`, `Module.ECModule` in
context), built by the module combinators, or concrete (`hook`). -/
partial def finite (hook : FootprintSolver.BoundHook) (F : Lean.Expr) (fuel : Nat := 64) :
    MetaM Lean.Expr := do
  if fuel == 0 then throwError "fp_finite: gave up on{indentExpr F}"
  let F ← instantiateMVars F
  let viaBound (pf : Lean.Expr) : MetaM Lean.Expr := do
    let_expr LE.le _ _ _ B := ← inferType pf | throwError "fp_finite: not a bound"
    mkAppM ``Footprint.FinitelySupported.mono #[pf, ← finite hook B (fuel - 1)]
  if let some (a, b) := FootprintSolver.sup? F then
    return ← mkAppM ``Footprint.FinitelySupported.sup
      #[← finite hook a (fuel - 1), ← finite hook b (fuel - 1)]
  if F.isAppOf ``Bot.bot then return mkConst ``Footprint.FinitelySupported.bot
  if F.isAppOf ``Lens.footprint then
    let x := F.appArg!
    if x.isAppOf ``Lens.pair then
      -- the pair's own disjointness instance (`mkAppM` leaves a trailing instance argument)
      let pf ← mkAppM ``le_of_eq #[← mkAppOptM ``Footprint.lens_pair
        #[none, none, none, x.getArg! 3, x.getArg! 4, x.getArg! 5]]
      return ← viaBound pf
    -- `{v} [Lens.IsGlobalVar x v]` after `x`: the instance (its `outParam` `v`) by search
    return ← mkAppOptM ``Lens.IsGlobalVar.footprint_finitelySupported #[none, x, none, none]
  if let some pf ← observing? (FootprintSolver.finitelySupported F) then return pf
  let_expr FVP.fvP _ _ M := F | throwError "fp_finite: cannot show finite support of{indentExpr F}"
  -- a module with an `@[fp_bound]` bound (as `fp_disjoint`: matched at reducible transparency)
  for lem in ← labelled `fp_bound do
    let s ← saveState
    try
      let c ← mkConstWithFreshMVarLevels lem
      let (args, binfos, bty) ← forallMetaTelescope (← inferType c)
      let_expr LE.le _ _ L _ := bty | failure
      unless ← withReducible (isDefEq L F) do failure
      for a in args, bi in binfos do
        if bi.isInstImplicit && !(← a.mvarId!.isAssigned) then
          a.mvarId!.assign (← synthInstance (← inferType a))
      return ← viaBound (← instantiateMVars (mkAppN c args))
    catch _ => s.restore
  let M ← whnfCore M
  if M.isAppOfArity ``Module.app 6 then
    return ← viaBound (← mkAppM ``FVP.fvP_app #[M.getArg! 4, M.getArg! 5])
  if M.isAppOfArity ``Module.pair 6 then
    return ← viaBound (← mkAppM ``le_of_eq #[← mkAppM ``FVP.fvP_pair #[M.getArg! 4, M.getArg! 5]])
  -- the combinators a module type's constructor and accessors unfold to (as `fp_disjoint`)
  if M.isAppOfArity ``Module.pair' 4 then
    return ← viaBound
      (← mkAppM ``le_of_eq #[← mkAppM ``FVP.fvP_pair' #[M.getArg! 2, M.getArg! 3]])
  for (c, n, lem) in [(``Module.fst, 5, ``FVP.fvP_fst), (``Module.snd, 5, ``FVP.fvP_snd),
      (``Module.fst', 3, ``FVP.fvP_fst'), (``Module.snd', 3, ``FVP.fvP_snd')] do
    if M.isAppOfArity c n then
      return ← viaBound (← mkAppM lem #[M.getArg! (n - 1)])
  -- a typed module without parameters (a `Module.pair` of its procedures): its procedures first
  if let some M' ← unfoldDefinition? M then
    if M'.isAppOf ``Module.pair then
      let pf ← finite hook (← mkAppM ``FVP.fvP #[M']) (fuel - 1)
      return ← mkExpectedTypeHint pf (← mkAppM ``Footprint.FinitelySupported #[F])
  if let some pf ← hook M then return ← viaBound pf
  let some M' ← unfoldDefinition? M
    | throwError "fp_finite: no finite support for{indentExpr F}"
  let pf ← finite hook (← mkAppM ``FVP.fvP #[M']) (fuel - 1)
  mkExpectedTypeHint pf (← mkAppM ``Footprint.FinitelySupported #[F])

end ModuleFootprint

open Lean Meta Elab Tactic ModuleFootprint in
/-- `fp_disjoint`, with the footprints of concrete modules read off their code (see the module
docstring). -/
elab_rules : tactic
  | `(tactic| fp_disjoint) => liftMetaFinishingTactic fun g => do
    -- against nothing (`F ≤ ⊥ᶜ`, a module declared without restriction, EC's `A <: Adv`):
    -- always, by `⊥ ≤ Fᶜ`; read off the goal's syntax, so the other goals pay nothing
    let ty ← instantiateMVars (← g.getType)
    if let some (_, _, F, rhs) := ty.app4? ``LE.le then
      if let some (_, _, S) := rhs.app3? ``Compl.compl then
        if S.isAppOf ``Bot.bot then
          g.assign (← mkAppM ``Iff.mpr #[← mkAppM ``Footprint.le_compl_comm #[F, S],
            ← mkAppOptM ``bot_le #[none, none, none, ← mkAppM ``Compl.compl #[F]]])
          return
    FootprintSolver.solve g cachedBound

open Lean Elab Tactic ModuleFootprint in
/-- `fp_finite`: close `F.FinitelySupported` (see the module docstring). -/
elab "fp_finite" : tactic => liftMetaFinishingTactic fun g => g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``Footprint.FinitelySupported 1 do
    throwError "fp_finite: expected `F.FinitelySupported`, got{indentExpr ty}"
  g.assign (← finite cachedBound ty.appArg!)

/-- `ec_module`: close `Module.ECModule D ext` for a module `D` over a first-order module type
whose `ext` is the canonical one (see the module docstring). -/
macro "ec_module" : tactic => `(tactic|
  exact ⟨Module.representable_of_firstOrder (by module_first_order)
    (fun n => (by holes_nonempty : HoleSigs.AllNonempty _).index n) _ (fun _ => rfl) _,
    by fp_finite⟩)

end GaudisCrypt
