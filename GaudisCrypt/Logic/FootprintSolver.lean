import GaudisCrypt.Logic.Granular

/-!
# Footprint disjointness from module restrictions

EasyCrypt checks `{-M}`-style side conditions itself: a variable lies outside a module's globals
when the module is built from modules whose restrictions exclude it.  Here such a side condition
is a goal `A ≤ (FVP.fvP M)ᶜ` (equivalently `FVP.fvP M ≤ Aᶜ`), and `fp_disjoint` proves it the same
way: it bounds `FVP.fvP M` through the module combinators (`fvP_app`, `fvP_pair`, `fvP_fst`, …,
unfolding definitions such as a module type's accessors and constructors) down to modules with a
restriction hypothesis `FVP.fvP N ≤ Sᶜ` in the context, and finds `A` among the joinands of `S`
(a joinand `glob X`, EasyCrypt's restriction against an abstract module, covers `A ≤ X`).
-/

namespace GaudisCrypt

theorem FVP.fvP_fst' {T U : ModuleTypeRep} (m : Module (.prod T U)) :
    FVP.fvP (Module.fst' m) ≤ FVP.fvP m := FVP.fvP_fst (A := Module T) (B := Module U) m

theorem FVP.fvP_snd' {T U : ModuleTypeRep} (m : Module (.prod T U)) :
    FVP.fvP (Module.snd' m) ≤ FVP.fvP m := FVP.fvP_snd (A := Module T) (B := Module U) m

theorem FVP.fvP_pair' {T U : ModuleTypeRep} (m1 : Module T) (m2 : Module U) :
    FVP.fvP (Module.pair' m1 m2) = FVP.fvP m1 ⊔ FVP.fvP m2 :=
  FVP.fvP_pair (A := Module T) (B := Module U) m1 m2

/-- The form `fp_disjoint` reduces its goal to. -/
theorem Footprint.le_compl_of_fvP {A F : Footprint VariableAssignment} (h : F ≤ Aᶜ) : A ≤ Fᶜ :=
  (Footprint.le_compl_comm A F).mpr h

/-- A restriction hypothesis `F ≤ Sᶜ`, with `A ≤ S`, gives `F ≤ Aᶜ`. -/
theorem Footprint.le_compl_of_le_compl {A S F : Footprint VariableAssignment} (h : F ≤ Sᶜ)
    (hA : A ≤ S) : F ≤ Aᶜ :=
  le_trans h (Footprint.compl_antimono hA)

namespace FootprintSolver

open Lean Meta

/-- `a ⊔ b`, as its two sides. -/
def sup? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``Max.max 4 then some (e.getArg! 2, e.getArg! 3) else none

/-- `Sᶜ`, as `S`. -/
def compl? (e : Lean.Expr) : Option Lean.Expr :=
  if e.isAppOfArity ``Compl.compl 3 then some (e.getArg! 2) else none

/-- Run `k`; on failure restore the state and return `false`. -/
def attempt (k : MetaM Unit) : MetaM Bool := do
  let st ← saveState
  try k; return true catch _ => st.restore; return false

/-- Apply the lemma `lem`, its premises to be the new goals (in order). -/
def applyConst (g : MVarId) (lem : Name) : MetaM (List MVarId) := do
  g.apply (← mkConstWithFreshMVarLevels lem) { allowSynthFailures := true }

/-- Close `A ≤ S` with `A` a joinand of `S` (up to reducible defeq, unfolding definitions in `S`
that are not joins), or `A` itself a join of such, or `⊥`. -/
partial def solveLeSup (g : MVarId) (fuel : Nat := 8) : MetaM Unit := do
  let ty ← instantiateMVars (← g.getType)
  let_expr LE.le _ _ A S := ty | throwError "fp_disjoint: not an inequality:{indentExpr ty}"
  if let some _ := sup? A then
    let [g₁, g₂] ← applyConst g ``sup_le | throwError "fp_disjoint: `sup_le` failed"
    solveLeSup g₁ fuel
    solveLeSup g₂ fuel
    return
  if A.isAppOf ``Bot.bot then
    let [] ← applyConst g ``bot_le | throwError "fp_disjoint: `bot_le` left goals"
    return
  if ← withReducible (isDefEq A S) then
    g.assign (← mkAppM ``le_refl #[A])
    return
  if let some _ := sup? S then
    if ← attempt (do
        let [g'] ← applyConst g ``le_sup_of_le_left | failure
        solveLeSup g' fuel) then return
    if ← attempt (do
        let [g'] ← applyConst g ``le_sup_of_le_right | failure
        solveLeSup g' fuel) then return
    throwError "fp_disjoint: {A} is not among{indentExpr S}"
  -- EC's `glob X` (the variables `X` touches): what is below `X` is below it
  if S.isAppOfArity ``Footprint.glob 1 then
    let [g'] ← applyConst g ``Footprint.le_glob_of_le
      | throwError "fp_disjoint: `le_glob_of_le` failed"
    return ← solveLeSup g' fuel
  -- a named footprint (`C.footprint`, an abbreviation of a restriction): unfold it
  if fuel > 0 then
    if let some S' ← unfoldDefinition? S then
      let g' ← g.replaceTargetDefEq (← mkAppM ``LE.le #[A, S'])
      return ← solveLeSup g' (fuel - 1)
  throwError "fp_disjoint: cannot show{indentExpr ty}"

/-- Close `F ≤ Aᶜ` from a hypothesis `h : F ≤ Sᶜ` with `A ≤ S`. -/
def tryHyp (g : MVarId) (h : LocalDecl) : MetaM Bool := do
  if h.isImplementationDetail then return false
  let hty ← instantiateMVars h.type
  let_expr LE.le _ _ F' S' := hty | return false
  let some S := compl? S' | return false
  attempt do
    let ty ← instantiateMVars (← g.getType)
    let_expr LE.le _ _ F T := ty | failure
    let some A := compl? T | failure
    unless ← isDefEq F F' do failure
    let hA ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[A, S])
    g.assign (← mkAppOptM ``Footprint.le_compl_of_le_compl
      #[some A, some S, some F, some h.toExpr, some hA])
    solveLeSup hA.mvarId!

/-- Close `X ≤ Aᶜ`, `X` a join of module footprints `FVP.fvP M`: each `M` has a restriction
hypothesis, or is bounded through the module combinators by modules that do. -/
partial def solveFvP (g : MVarId) (fuel : Nat := 64) : MetaM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let_expr LE.le _ _ X _ := ty | throwError "fp_disjoint: not an inequality:{indentExpr ty}"
  if let some _ := sup? X then
    let [g₁, g₂] ← applyConst g ``sup_le | throwError "fp_disjoint: `sup_le` failed"
    solveFvP g₁ fuel
    solveFvP g₂ fuel
    return
  if X.isAppOf ``Bot.bot then
    let [] ← applyConst g ``bot_le | throwError "fp_disjoint: `bot_le` left goals"
    return
  for h in ← getLCtx do
    if ← tryHyp g h then return
  let_expr FVP.fvP _ _ M := X
    | throwError "fp_disjoint: no restriction hypothesis for{indentExpr X}"
  if fuel == 0 then throwError "fp_disjoint: gave up on{indentExpr M}"
  let M ← whnfCore (← instantiateMVars M)
  -- `fvP (f a …) ≤ B` by the combinator's lemma, then `B ≤ Aᶜ`
  let viaBound (pf : Lean.Expr) : MetaM Unit := do
    let_expr LE.le _ _ _ B := ← inferType pf | throwError "fp_disjoint: not a bound:{indentExpr pf}"
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[B, ty.getArg! 3])
    g.assign (← mkAppM ``le_trans #[pf, g'])
    solveFvP g'.mvarId! (fuel - 1)
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
  let some M' ← unfoldDefinition? M
    | throwError "fp_disjoint: no restriction hypothesis for{indentExpr X}"
  let g' ← g.replaceTargetDefEq (← mkAppM ``LE.le #[← mkAppM ``FVP.fvP #[M'], ty.getArg! 3])
  solveFvP g' (fuel - 1)

/-- Prove `A ≤ (FVP.fvP M)ᶜ` (or `A ≤ Fᶜ` for a join `F` of module footprints), or
`FVP.fvP M ≤ Aᶜ`, from the restriction hypotheses in context. -/
def solve (g : MVarId) : MetaM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let_expr LE.le _ _ L R := ty | throwError "fp_disjoint: not an inequality:{indentExpr ty}"
  let some F := compl? R | throwError "fp_disjoint: not of the form `A ≤ Fᶜ`:{indentExpr ty}"
  -- `A ≤ Fᶜ` with `F` the modules' side: turn it around
  let modulesSide (e : Lean.Expr) : Bool := e.find? (·.isAppOf ``FVP.fvP) |>.isSome
  if modulesSide F && !modulesSide L then
    let [g'] ← applyConst g ``Footprint.le_compl_of_fvP
      | throwError "fp_disjoint: `le_compl_of_fvP` failed"
    solveFvP g'
  else
    solveFvP g

end FootprintSolver

open Lean Elab Tactic in
/-- `fp_disjoint`: close `A ≤ (FVP.fvP M)ᶜ` or `FVP.fvP M ≤ Aᶜ` (EasyCrypt's check of a memory
restriction), bounding `FVP.fvP M` through the module combinators by modules with a restriction
hypothesis `FVP.fvP N ≤ Sᶜ` in context, `A` (or each joinand of it) among the joinands of `S`. -/
elab "fp_disjoint" : tactic => liftMetaFinishingTactic FootprintSolver.solve

end GaudisCrypt
