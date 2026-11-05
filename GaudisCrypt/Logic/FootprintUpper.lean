import GaudisCrypt.Logic.FootprintSolver
import GaudisCrypt.Logic.ConcreteFootprint

/-!
# Upper bounds of footprints

`fp_disjoint` proves restrictions `FVP.fvP M ≤ Aᶜ`.  `fp_le` proves upper bounds `FVP.fvP M ≤ U`,
`U` a join of variables and module footprints (EasyCrypt's "the module only touches these
variables", read off the code): the same descent through the module combinators (`fvP_app`,
`fvP_pair`, `fvP_fst`, …, unfolding definitions) down to concrete modules with an `@[fp_bound]`
bound, or modules with a bound hypothesis `FVP.fvP N ≤ B` in context, and `B`'s joinands found among
`U`'s (`FootprintSolver.solveLeSup`).  A use: the frame rule `prhlProc_frame_equal_outside`, whose
callees must stay within a lens.
-/

namespace GaudisCrypt

namespace FootprintUpper

open Lean Meta FootprintSolver

/-- Close `X ≤ U`, `X` a join of module footprints and variables (see the module doc). -/
partial def solve (g : MVarId) (fuel : Nat := 64) : MetaM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let_expr LE.le _ _ X U := ty | throwError "fp_le: not an inequality:{indentExpr ty}"
  if let some _ := sup? X then
    let [g₁, g₂] ← FootprintSolver.applyConst g ``sup_le | throwError "fp_le: `sup_le` failed"
    solve g₁ fuel
    solve g₂ fuel
    return
  -- `X` among `U`'s joinands (or `⊥`)
  if ← attempt (solveLeSup g) then return
  if fuel == 0 then throwError "fp_le: gave up on{indentExpr X}"
  -- `X ≤ B` by `pf`, then `B ≤ U`
  let viaBound (pf : Lean.Expr) : MetaM Unit := do
    let_expr LE.le _ _ _ B := ← inferType pf | throwError "fp_le: not a bound:{indentExpr pf}"
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[B, U])
    g.assign (← mkAppM ``le_trans #[pf, g'])
    solve g'.mvarId! (fuel - 1)
  -- a bound hypothesis `X ≤ B` (not a restriction `X ≤ Sᶜ`)
  for h in ← getLCtx do
    if h.isImplementationDetail then continue
    let hty ← instantiateMVars h.type
    let_expr LE.le _ _ F B := hty | continue
    if (compl? B).isSome then continue
    if ← attempt (do
        unless ← withReducible (isDefEq F X) do failure
        viaBound h.toExpr) then return
  -- a concrete module with an `@[fp_bound]` bound
  for lem in ← labelled `fp_bound do
    if ← attempt (do
        let c ← mkConstWithFreshMVarLevels lem
        let (args, binfos, bty) ← forallMetaTelescope (← inferType c)
        let_expr LE.le _ _ L _ := bty | failure
        unless ← withReducible (isDefEq L X) do failure
        for a in args, bi in binfos do
          if bi.isInstImplicit && !(← a.mvarId!.isAssigned) then
            a.mvarId!.assign (← synthInstance (← inferType a))
        viaBound (← instantiateMVars (mkAppN c args))) then return
  let_expr FVP.fvP _ _ M := X | throwError "fp_le: cannot bound{indentExpr X}"
  let M ← whnfCore (← instantiateMVars M)
  if M.isAppOfArity ``Module.app 6 then
    return ← viaBound (← mkAppM ``FVP.fvP_app #[M.getArg! 4, M.getArg! 5])
  if M.isAppOfArity ``Module.pair 6 then
    return ← viaBound (← mkAppM ``le_of_eq #[← mkAppM ``FVP.fvP_pair #[M.getArg! 4, M.getArg! 5]])
  if M.isAppOfArity ``Module.pair' 4 then
    return ← viaBound
      (← mkAppM ``le_of_eq #[← mkAppM ``FVP.fvP_pair' #[M.getArg! 2, M.getArg! 3]])
  for (c, n, lem) in [(``Module.fst, 5, ``FVP.fvP_fst), (``Module.snd, 5, ``FVP.fvP_snd),
      (``Module.fst', 3, ``FVP.fvP_fst'), (``Module.snd', 3, ``FVP.fvP_snd')] do
    if M.isAppOfArity c n then
      return ← viaBound (← mkAppM lem #[M.getArg! (n - 1)])
  -- a definition (a module type's accessor or constructor, a named module): unfold it
  let some M' ← unfoldDefinition? M | throwError "fp_le: no bound for{indentExpr X}"
  let g' ← g.replaceTargetDefEq (← mkAppM ``LE.le #[← mkAppM ``FVP.fvP #[M'], U])
  solve g' (fuel - 1)

end FootprintUpper

open Lean Elab Tactic in
/-- `fp_le`: close `FVP.fvP M ≤ U` (a join of variables and module footprints), bounding
`FVP.fvP M` through the module combinators by `@[fp_bound]` lemmas and bound hypotheses
`FVP.fvP N ≤ B` in context, each `B`'s joinands among `U`'s. -/
elab "fp_le" : tactic => liftMetaFinishingTactic FootprintUpper.solve

/-- `Module.comp f g` touches what `f` and `g` touch (EasyCrypt's alias `F(X) = f(g(X))`). -/
@[fp_bound] theorem FVP.fvP_comp_le {A B C : Type 1} [IsModule A] [IsModule B] [IsModule C]
    (f : Module.Arr B C) (g : Module.Arr A B) :
    FVP.fvP (Module.comp f g) ≤ FVP.fvP f ⊔ FVP.fvP g := by
  unfold Module.comp
  fp_module

end GaudisCrypt
