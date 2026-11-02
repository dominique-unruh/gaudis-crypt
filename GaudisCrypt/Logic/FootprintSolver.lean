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

A concrete module has no restriction hypothesis: its globals are read off its code.  A lemma
`FVP.fvP M ≤ B` tagged `@[fp_bound]` (proven by `fp_module`) bounds it; `B` is then a join of
variables.  A variable `v` is outside `glob D` when it is outside `D` and `D` is finitely supported
(EasyCrypt's `glob D` is a set of variables): `Footprint.varLens_le_compl_glob`, with the finite
support from a hypothesis `Module.ECModule D _` (or `(FVP.fvP D).FinitelySupported`).  A
restriction between abstract modules is symmetric (`Footprint.le_compl_glob_symm`): `M` is outside
`glob D` when `D` is outside `glob M`.
-/

/-- `@[fp_bound]`: a bound `FVP.fvP M ≤ B` on a concrete module that `fp_disjoint` uses. -/
register_label_attr fp_bound

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

/-- A variable outside a finitely supported `F` is outside `F.glob` (EasyCrypt: `glob D` is the
set of `D`'s variables). -/
theorem Footprint.varLens_le_compl_glob {F : Footprint VariableAssignment}
    (hF : F.FinitelySupported) (v : VariableName) (h : F ≤ (GaudisCrypt.varLens v).footprintᶜ) :
    (GaudisCrypt.varLens v).footprint ≤ F.globᶜ :=
  (Footprint.le_compl_comm _ _).mp (hF.glob_le_compl_varLens v h)

/-- **Fresh variables outside a `glob`**: `Footprint.exists_fresh` for `F ⊔ G`, the fresh variable
also outside `glob F` (it is a single variable outside `F`). -/
theorem Footprint.exists_fresh_glob (T : Type) [Nonempty T] {F G : Footprint VariableAssignment}
    (hF : F.FinitelySupported) (hG : G.FinitelySupported) :
    ∃ L : Lens T VariableAssignment, L.footprint ≤ F.globᶜ ∧ L.footprint ≤ (F ⊔ G)ᶜ ∧
      L.footprint.FinitelySupported := by
  obtain ⟨vs, hvs⟩ := hF.sup hG
  let w : VariableName :=
    { name := freshName vs, type := T, key := VariableName.encode (freshName vs),
      keyCorrect := rfl }
  have hw : (GaudisCrypt.varLens w).footprint ≤ (F ⊔ G)ᶜ := by
    refine le_trans ?_ (Footprint.compl_antimono hvs)
    rw [Footprint.le_compl_comm]
    refine iSup₂_le fun v hv => ?_
    have hne : v ≠ w := fun h => freshName_ne vs v hv (by rw [h])
    haveI := varLens_disjoint hne
    exact Lens.footprint_le_compl_of_disjoint (GaudisCrypt.varLens v) (GaudisCrypt.varLens w)
  exact ⟨GaudisCrypt.varLens w, Footprint.varLens_le_compl_glob hF w
    ((Footprint.le_compl_comm _ _).mp (hw.trans (Footprint.compl_antimono le_sup_left))), hw,
    Footprint.FinitelySupported.varLens w⟩

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
  -- the `glob` of the same module, its type spelled differently (a module reached through
  -- projections has its type unfolded): the kernel checks the instances agree (unifying at
  -- default transparency here can be slow)
  let globModule? (e : Lean.Expr) : Option Lean.Expr := do
    guard (e.isAppOfArity ``Footprint.glob 1)
    let f := e.getArg! 0
    guard (f.isAppOfArity ``FVP.fvP 3)
    return f.getArg! 2
  let sameModule ← match globModule? A, globModule? S with
    | some M₁, some M₂ => withReducible (isDefEq M₁ M₂)
    | _, _ => pure false
  if sameModule then
    g.assign (← mkAppOptM ``le_refl #[none, none, A])
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

/-- A proof of `F.FinitelySupported`, from a hypothesis `Module.ECModule D _` (`F = FVP.fvP D`)
or `F.FinitelySupported`. -/
def finitelySupported (F : Lean.Expr) : MetaM Lean.Expr := do
  let goal ← mkAppM ``Footprint.FinitelySupported #[F]
  for h in ← getLCtx do
    if h.isImplementationDetail then continue
    let hty ← instantiateMVars h.type
    let cand? : Option Lean.Expr ←
      if hty.isAppOf ``Module.ECModule then
        pure (some (← mkAppM ``Module.ECModule.finitelySupported #[h.toExpr]))
      else if hty.isAppOf ``Footprint.FinitelySupported then pure (some h.toExpr)
      else pure none
    if let some cand := cand? then
      if ← isDefEq (← inferType cand) goal then return cand
  throwError "fp_disjoint: no finite support (`Module.ECModule`) for{indentExpr F}"

/-- Close `X ≤ Aᶜ`, `X` a join of module footprints `FVP.fvP M` and variables: each `M` has a
restriction hypothesis, an `@[fp_bound]`, or is bounded through the module combinators by modules
that do; each variable is outside `A`'s modules (outside `glob D` by `D`'s finite support). -/
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
  if fuel == 0 then throwError "fp_disjoint: gave up on{indentExpr X}"
  let some T := compl? (ty.getArg! 3)
    | throwError "fp_disjoint: not of the form `X ≤ Aᶜ`:{indentExpr ty}"
  -- `glob F ≤ Tᶜ`: turn it around, to the variables of `T` against `glob F`
  if X.isAppOfArity ``Footprint.glob 1 then
    let [g'] ← applyConst g ``Footprint.le_compl_of_fvP
      | throwError "fp_disjoint: `le_compl_of_fvP` failed"
    return ← solveFvP g' (fuel - 1)
  -- variables `X` (no module): against `glob F` or a module's footprint
  unless X.find? (·.isAppOf ``FVP.fvP) |>.isSome do
    if T.isAppOfArity ``Footprint.glob 1 then
      -- a variable `v` outside `glob F`: `F` finitely supported, and `v` outside `F`
      if X.isAppOf ``Lens.footprint then
        let F := T.getArg! 0
        let v ← mkFreshExprMVar (mkConst ``VariableName)
        unless ← isDefEq X (← mkAppM ``Lens.footprint #[← mkAppM ``GaudisCrypt.varLens #[v]]) do
          -- a lens parameter (not a single variable): a hypothesis `glob F ≤ Sᶜ`, `X` in `S`
          -- (the restriction against `glob F` stated for it), turned around
          let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[T, ← mkAppM ``Compl.compl #[X]])
          g.assign (← mkAppM ``Iff.mpr #[← mkAppM ``Footprint.le_compl_comm #[X, T], g'])
          for h in ← getLCtx do
            if ← tryHyp g'.mvarId! h then return
          throwError "fp_disjoint: not a variable, and no restriction of {T} against it:{indentExpr X}"
        let hF ← finitelySupported F
        let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[F, ← mkAppM ``Compl.compl #[X]])
        g.assign (← mkAppOptM ``Footprint.varLens_le_compl_glob
          #[some F, some hF, some (← instantiateMVars v), some g'])
        return ← solveFvP g'.mvarId! (fuel - 1)
    else if T.find? (·.isAppOf ``FVP.fvP) |>.isSome then
      -- `X ≤ (fvP M)ᶜ`: turn it around
      let [g'] ← applyConst g ``Footprint.le_compl_of_fvP
        | throwError "fp_disjoint: `le_compl_of_fvP` failed"
      return ← solveFvP g' (fuel - 1)
    else if X.isAppOf ``Lens.footprint && (sup? T).isSome then
      -- a variable against a join: turn it around and split the join
      let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[T, ← mkAppM ``Compl.compl #[X]])
      g.assign (← mkAppM ``Iff.mpr #[← mkAppM ``Footprint.le_compl_comm #[X, T], g'])
      return ← solveFvP g'.mvarId! (fuel - 1)
    else if X.isAppOf ``Lens.footprint && T.isAppOf ``Lens.footprint then
      -- two variables: disjoint lenses (`global_var`s by instance search)
      if ← attempt (do
          g.assign (← mkAppOptM ``Lens.footprint_le_compl_of_disjoint
            #[none, none, none, X.appArg!, T.appArg!, none])) then return
      throwError "fp_disjoint: no `Lens.Disjoint` for{indentExpr ty}"
    -- a named footprint (`C.footprint`): unfold it
    if !X.isAppOf ``Lens.footprint then
      if let some X' ← unfoldDefinition? X then
        let g' ← g.replaceTargetDefEq (← mkAppM ``LE.le #[X', ty.getArg! 3])
        return ← solveFvP g' (fuel - 1)
    -- a variable against a region `T` with a restriction hypothesis `T ≤ Sᶜ`, `X` in `S`:
    -- turned around
    if X.isAppOf ``Lens.footprint then
      if ← attempt (do
          let g' ← mkFreshExprSyntheticOpaqueMVar
            (← mkAppM ``LE.le #[T, ← mkAppM ``Compl.compl #[X]])
          g.assign (← mkAppM ``Iff.mpr #[← mkAppM ``Footprint.le_compl_comm #[X, T], g'])
          let mut ok := false
          for h in ← getLCtx do
            if !ok then ok ← tryHyp g'.mvarId! h
          unless ok do failure) then return
    throwError "fp_disjoint: cannot show{indentExpr ty}"
  -- `X ≤ B` by `pf`, then `B ≤ Aᶜ`
  let viaBound (pf : Lean.Expr) : MetaM Unit := do
    let_expr LE.le _ _ _ B := ← inferType pf | throwError "fp_disjoint: not a bound:{indentExpr pf}"
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[B, ty.getArg! 3])
    g.assign (← mkAppM ``le_trans #[pf, g'])
    solveFvP g'.mvarId! (fuel - 1)
  -- a concrete module with an `@[fp_bound]` bound
  for lem in ← labelled `fp_bound do
    if ← attempt (do
        let c ← mkConstWithFreshMVarLevels lem
        let (args, binfos, bty) ← forallMetaTelescope (← inferType c)
        let_expr LE.le _ _ L _ := bty | failure
        -- reducible only: a bound is for the module it names, and unfolding other modules to
        -- compare is slow
        unless ← withReducible (isDefEq L X) do failure
        -- the lemma's instance arguments (`[Lens.Disjoint …]`) by instance search
        for a in args, bi in binfos do
          if bi.isInstImplicit && !(← a.mvarId!.isAssigned) then
            a.mvarId!.assign (← synthInstance (← inferType a))
        viaBound (← instantiateMVars (mkAppN c args))) then return
  let_expr FVP.fvP _ _ M := X
    | throwError "fp_disjoint: no restriction hypothesis for{indentExpr X}"
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
  let some M' ← unfoldDefinition? M
    | -- an abstract module against `glob F`: the restriction the other way round
      -- (`Footprint.le_compl_glob_symm`, `F` finitely supported)
      if T.isAppOfArity ``Footprint.glob 1 then
        if ← attempt (do
            let F := T.getArg! 0
            let hF ← finitelySupported F
            let g' ← mkFreshExprSyntheticOpaqueMVar
              (← mkAppM ``LE.le #[F, ← mkAppM ``Compl.compl #[← mkAppM ``Footprint.glob #[X]]])
            g.assign (← mkAppM ``Footprint.le_compl_glob_symm #[hF, g'])
            solveFvP g'.mvarId! (fuel - 1)) then return
      throwError "fp_disjoint: no restriction hypothesis for{indentExpr X}"
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
