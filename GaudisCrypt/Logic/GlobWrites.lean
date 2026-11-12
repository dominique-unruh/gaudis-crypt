import GaudisCrypt.Logic.ConcreteFootprint
import GaudisCrypt.Logic.FootprintUpper

/-!
# Lower bounds of footprints: a module's writes

`fp_le` bounds `FVP.fvP M` from above.  EC's `={glob M}` of a concrete module `M` is the equality
of `M`'s variables; ours is the equality on `FVP.fvP M`'s touched getter (`glob M` is the region
`M` may touch), and to get a variable's equality back, the variable must lie *inside* that
region: a lower bound.

A region containing every constant write of a lens `x` (`Footprint.HasWrites`) contains `x`'s
tests (`Footprint.HasWrites.testKer_mem`, the argument of `Lens.testKer_mem_footprint`), and the
tests read `x`: equal on the region, so equal on `x`
(`Lens.get_eq_of_touched_getter_eq_of_hasWrites`).  A procedure whose code assigns the global `x`
somewhere (its callees included) has all of `x`'s constant writes in its footprint: an
assignment's footprint is that of the writes of every value (`FVP.fvpInductiveFunctionGS.setter`).

    fp_writes   -- `(FVP.fvP M).HasWrites x`, `M` a concrete module assigning `x` somewhere

`fp_writes` goes down `M`'s module type to its procedures (`Module.fst'`/`Module.snd'`, each a
lower bound of `M`'s footprint), unfolds each as the inliner does (`Flatten.unfoldProcedure`) and
looks for an assignment of `x` in its code (callees' bodies included).  EC reads a concrete
module's globals off its code; this is that reading, for the variables the module writes.
-/

namespace GaudisCrypt

/-- `R` contains every constant write of `X`. -/
def Footprint.HasWrites {a m : Type*} (R : Footprint m) (X : Lens a m) : Prop :=
  ∀ c : a, (fun σ => (pure (X.set c σ) : SubProbability m)) ∈ R.updates

theorem Footprint.HasWrites.mono {a m : Type*} {R S : Footprint m} {X : Lens a m} (h : R ≤ S)
    (hR : R.HasWrites X) : S.HasWrites X := fun c => h (hR c)

/-- **A region with `X`'s constant writes contains `X`'s tests** (as `Lens.testKer_mem_footprint`:
a kernel commuting with the writes keeps `X`'s content, so the test passes it or kills it). -/
theorem Footprint.HasWrites.testKer_mem {a m : Type*} {R : Footprint m} {X : Lens a m}
    (hR : R.HasWrites X) (x₀ : a) : X.testKer x₀ ∈ R.updates := by
  classical
  rw [← R.double_commutant]
  refine Set.mem_centralizer_iff.mpr (fun k hk => ?_)
  have hwrite : ∀ (c : a) (σ : m),
      (k σ >>= fun τ => (pure (X.set c τ) : SubProbability m)) = k (X.set c σ) := by
    intro c σ
    have hcomm := Set.mem_centralizer_iff.mp hk _ (hR c)
    calc (k σ >>= fun τ => (pure (X.set c τ) : SubProbability m))
        = ((fun σ => (pure (X.set c σ) : SubProbability m)) * k) σ := rfl
      _ = (k * fun σ => (pure (X.set c σ) : SubProbability m)) σ := congrFun hcomm σ
      _ = k (X.set c σ) := by
          show (pure (X.set c σ) : SubProbability m) >>= k = k (X.set c σ)
          rw [SubProbability.pure_bind]
  funext σ
  show X.testKer x₀ σ >>= k = k σ >>= X.testKer x₀
  by_cases h : X.get σ = x₀
  · have hset : X.set x₀ σ = σ := by rw [← h]; exact X.get_set σ
    have hR' : k σ >>= X.testKer x₀ = k σ :=
      calc k σ >>= X.testKer x₀
          = (k σ >>= fun τ => (pure (X.set x₀ τ) : SubProbability m)) >>= X.testKer x₀ := by
            rw [hwrite x₀ σ, hset]
        _ = k σ >>= fun τ => X.testKer x₀ (X.set x₀ τ) := by
            rw [SubProbability.bind_assoc]; simp only [SubProbability.pure_bind]
        _ = k σ >>= fun τ => (pure (X.set x₀ τ) : SubProbability m) := by
            refine congrArg (fun f => k σ >>= f) (funext fun τ => ?_)
            show (if X.get (X.set x₀ τ) = x₀ then (pure (X.set x₀ τ) : SubProbability m) else ⊥)
                = (pure (X.set x₀ τ) : SubProbability m)
            rw [X.set_get, if_pos rfl]
        _ = k (X.set x₀ σ) := hwrite x₀ σ
        _ = k σ := by rw [hset]
    rw [show X.testKer x₀ σ = pure σ from if_pos h, SubProbability.pure_bind, hR']
  · have hset : X.set (X.get σ) σ = σ := X.get_set σ
    have hR' : k σ >>= X.testKer x₀ = (⊥ : SubProbability m) :=
      calc k σ >>= X.testKer x₀
          = (k σ >>= fun τ => (pure (X.set (X.get σ) τ) : SubProbability m)) >>= X.testKer x₀ := by
            rw [hwrite (X.get σ) σ, hset]
        _ = k σ >>= fun τ => X.testKer x₀ (X.set (X.get σ) τ) := by
            rw [SubProbability.bind_assoc]; simp only [SubProbability.pure_bind]
        _ = k σ >>= fun _ => (⊥ : SubProbability m) := by
            refine congrArg (fun f => k σ >>= f) (funext fun τ => ?_)
            show (if X.get (X.set (X.get σ) τ) = x₀
                then (pure (X.set (X.get σ) τ) : SubProbability m) else ⊥) = ⊥
            rw [X.set_get, if_neg h]
        _ = ⊥ := SubProbability.bind_bot _
    rw [show X.testKer x₀ σ = ⊥ from if_neg h, SubProbability.bot_bind, hR']

/-- **EC's `={glob M}` gives `={x}`** for a variable `x` whose writes lie in the region. -/
theorem Lens.get_eq_of_touched_getter_eq_of_hasWrites {β m : Type*} (x : Lens β m)
    {R : Footprint m} (hx : R.HasWrites x) {σ σ' : m}
    (h : R.touched_getter.get σ = R.touched_getter.get σ') : x.get σ = x.get σ' :=
  Footprint.get_eq_of_indistinguishable_of_testKer_mem hx.testKer_mem
    (Footprint.indistinguishable_of_touched_getter_eq h)

/-- The writes of a pair of variables: one's after the other's. -/
theorem Footprint.HasWrites.pair {a b m : Type*} {R : Footprint m} {x : Lens a m} {y : Lens b m}
    [Lens.Disjoint x y] (hx : R.HasWrites x) (hy : R.HasWrites y) :
    R.HasWrites (Lens.pair x y) := by
  rintro ⟨u, v⟩
  have h := R.comp (hx u) (hy v)
  convert h using 1
  funext σ
  change (pure (x.set u (y.set v σ)) : SubProbability m) =
    (pure (y.set v σ) : SubProbability m) >>= fun τ => (pure (x.set u τ) : SubProbability m)
  rw [SubProbability.pure_bind]

/-- **EC's `glob M` of a concrete module is its variables `X`**: a region between `X`'s writes and
`X`'s footprint is equal exactly where `X` is. -/
theorem touched_getter_eq_iff_of_writes {β m : Type*} {X : Lens β m} {R : Footprint m}
    (hle : R ≤ X.footprint) (hw : R.HasWrites X) (a b : m) :
    (R.touched_getter.get a = R.touched_getter.get b) = (X.get a = X.get b) :=
  propext ⟨X.get_eq_of_touched_getter_eq_of_hasWrites hw, fun h =>
    Footprint.touched_getter_eq_of_le hle ((Lens.footprint_touched_getter_eq_iff X a b).mpr h)⟩

/-! ## The writes of code -/

namespace GlobWrites

local notation "st" => FVP.fvpInductiveFunctionGS.stmt

/-- An assignment's footprint has the writes of its variable. -/
theorem setter {α : Type} (x : Setter α ProgramState) (Y : Lens α ProgramState)
    (hx : ∀ v σ, x.set v σ = Y.set v σ) :
    (ProgramDenotation.footprint' (ProgramDenotation.set x)).HasWrites Y := by
  classical
  intro c
  refine (le_iSup (fun v => (ProgramDenotation.set x v).footprint) c) ?_
  rw [ProgramDenotation.footprint, Footprint.from_updates]
  refine Set.subset_centralizer_centralizer ⟨(), ?_⟩
  funext σ
  simp only [ProgramDenotation.set, SubProbability.pure_bind, if_pos]
  exact congrArg pure (hx c σ)

/-- The globals' share of a statement has the writes of a global it assigns. -/
theorem reduce_globalL {a : Type} {T : Footprint ProgramState} {X : Lens a VariableAssignment}
    (h : T.HasWrites X.intoGlobal) :
    (Lens.reduceFootprint ProgramState.globalL T).HasWrites X := by
  intro c
  obtain ⟨ps₀⟩ : Nonempty ProgramState := inferInstance
  refine (Footprint.from_le_iff _ _).mp le_rfl
    ⟨((fun σ => pure (X.intoGlobal.set c σ)), fun _ => pure (ProgramState.globalL.compl.get ps₀),
      fun _ => pure ()), ⟨h c, Set.mem_univ _, Set.mem_univ _⟩, ?_⟩
  funext m
  simp only [Lens.reduceSubProbability, SubProbability.pure_hbind]
  show (pure (ProgramState.globalL.get (ProgramState.globalL.set
      (X.set c (ProgramState.globalL.get (ProgramState.globalL.splitSpace.invFun
        (m, ProgramState.globalL.compl.get ps₀))))
      (ProgramState.globalL.splitSpace.invFun (m, ProgramState.globalL.compl.get ps₀)))) :
        SubProbability VariableAssignment) = pure (X.set c m)
  rw [Lens.splitSpace_invFun_get, ProgramState.globalL.set_get]

/-- A callee's globals' share, back in the caller's state, has the writes of a global the callee
assigns. -/
theorem transfer {a : Type} {T : Footprint ProgramState} {X : Lens a VariableAssignment}
    (h : T.HasWrites X.intoGlobal) :
    (FVP.fvpInductiveFunctionGS.transfer T).HasWrites X.intoGlobal := by
  intro c
  have hr := reduce_globalL h c
  refine (Footprint.from_le_iff _ _).mp le_rfl ⟨_, hr, ?_⟩
  funext σ
  simp only [Lens.liftSubProbability, SubProbability.pure_hbind]
  rfl

theorem sample {h : HoleSigs} {α : Type} (x : Setter α ProgramState)
    (e : Getter (SubProbability α) ProgramState) {β : Type} {Y : Lens β ProgramState}
    (hx : (ProgramDenotation.footprint' (ProgramDenotation.set x)).HasWrites Y) :
    (st (StmtWithHoles.sample (h := h) x e)).HasWrites Y :=
  hx.mono le_sup_left

theorem call_set {h : HoleSigs} {sig : ProcedureSignature} (x : Setter sig.ret ProgramState)
    (ns : List String) (hl : ns.length = sig.params.length) (hn : ns.Nodup)
    (b : StmtWithHoles .empty) (r : Getter sig.ret ProgramState)
    (p : Getter sig.ParamType ProgramState) {β : Type} {Y : Lens β ProgramState}
    (hx : (ProgramDenotation.footprint' (ProgramDenotation.set x)).HasWrites Y) :
    (st (StmtWithHoles.call' (h := h) x ns hl hn b r p)).HasWrites Y :=
  hx.mono le_sup_left

theorem call_body {h : HoleSigs} {sig : ProcedureSignature} (x : Setter sig.ret ProgramState)
    (ns : List String) (hl : ns.length = sig.params.length) (hn : ns.Nodup)
    (b : StmtWithHoles .empty) (r : Getter sig.ret ProgramState)
    (p : Getter sig.ParamType ProgramState) {β : Type} {X : Lens β VariableAssignment}
    (hb : (st b).HasWrites X.intoGlobal) :
    (st (StmtWithHoles.call' (h := h) x ns hl hn b r p)).HasWrites X.intoGlobal :=
  (transfer hb).mono (le_sup_left.trans le_sup_right)

theorem hole {h : HoleSigs} {sig : ProcedureSignature} (n : HoleIndex h sig)
    (x : Setter sig.ret ProgramState) (p : Getter sig.ParamType ProgramState) {β : Type}
    {Y : Lens β ProgramState}
    (hx : (ProgramDenotation.footprint' (ProgramDenotation.set x)).HasWrites Y) :
    (st (StmtWithHoles.hole n x p)).HasWrites Y :=
  hx.mono le_sup_left

theorem seq_left {h : HoleSigs} (s t : StmtWithHoles h) {β : Type} {Y : Lens β ProgramState}
    (hs : (st s).HasWrites Y) : (st (StmtWithHoles.seq s t)).HasWrites Y :=
  hs.mono le_sup_left

theorem seq_right {h : HoleSigs} (s t : StmtWithHoles h) {β : Type} {Y : Lens β ProgramState}
    (ht : (st t).HasWrites Y) : (st (StmtWithHoles.seq s t)).HasWrites Y :=
  ht.mono le_sup_right

theorem ite_left {h : HoleSigs} (c : Getter Bool ProgramState) (s t : StmtWithHoles h) {β : Type}
    {Y : Lens β ProgramState} (hs : (st s).HasWrites Y) :
    (st (StmtWithHoles.ifThenElse c s t)).HasWrites Y :=
  hs.mono (le_sup_left.trans le_sup_right)

theorem ite_right {h : HoleSigs} (c : Getter Bool ProgramState) (s t : StmtWithHoles h)
    {β : Type} {Y : Lens β ProgramState} (ht : (st t).HasWrites Y) :
    (st (StmtWithHoles.ifThenElse c s t)).HasWrites Y :=
  ht.mono (le_sup_right.trans le_sup_right)

theorem while_body {h : HoleSigs} (c : Getter Bool ProgramState) (s : StmtWithHoles h) {β : Type}
    {Y : Lens β ProgramState} (hs : (st s).HasWrites Y) :
    (st (StmtWithHoles.while c s)).HasWrites Y :=
  hs.mono le_sup_right

/-- A procedure's footprint has the writes of a global its body assigns. -/
theorem procBody {holes : HoleSigs} {sig : ProcedureSignature} (p : ProcedureWithHoles holes sig)
    {a : Type} {X : Lens a VariableAssignment} (h : (st p.body).HasWrites X.intoGlobal) :
    (FVP.fvP_proc p).HasWrites X :=
  (reduce_globalL h).mono le_sup_left

/-- A procedure module's footprint is its procedure's. -/
theorem module_proc {sig : ProcedureSignature} (M : Module (.proc sig)) {a : Type}
    {X : Lens a VariableAssignment}
    (h : (FVP.fvP_proc (Module.Proc.procedure (sig := sig) M)).HasWrites X) :
    (FVP.fvP (M : Module.Proc sig)).HasWrites X := by
  have e := FVP.fvP_module_proc (Module.Proc.procedure (sig := sig) M)
  rw [← Module.Proc.eq_proc_procedure] at e
  exact e ▸ h

theorem module_fst {T U : ModuleTypeRep} (M : Module (.prod T U)) {a : Type}
    {X : Lens a VariableAssignment} (h : (FVP.fvP (Module.fst' M)).HasWrites X) :
    (FVP.fvP M).HasWrites X :=
  h.mono (FVP.fvP_fst' M)

theorem module_snd {T U : ModuleTypeRep} (M : Module (.prod T U)) {a : Type}
    {X : Lens a VariableAssignment} (h : (FVP.fvP (Module.snd' M)).HasWrites X) :
    (FVP.fvP M).HasWrites X :=
  h.mono (FVP.fvP_snd' M)

open Lean Meta

/-- Apply `lem` to `g`, the new goals (the hypotheses left open). -/
def applyConst (g : MVarId) (lem : Name) : MetaM (List MVarId) := do
  g.apply (← mkConstWithFreshMVarLevels lem)

/-- Run `k`, restoring the state if it fails. -/
def attempt (k : MetaM Unit) : MetaM Bool := do
  let s ← saveState
  try k; return true
  catch _ => s.restore; return false

/-- Rewrite the procedure `p` (a `Module.Proc.procedure M` in `g`'s goal) to its code, as the
inliner does. -/
def unfoldProcIn (g : MVarId) (p : Lean.Expr) : MetaM MVarId := do
  let r ← try Flatten.unfoldProcedure p catch _ => Flatten.unfoldProcedure p (views := true)
  let ty ← instantiateMVars (← g.getType)
  match r.proof? with
  | none => g.replaceTargetDefEq (ty.replace fun e => if e == p then some r.expr else none)
  | some h => do
    let res ← g.rewrite ty h
    g.replaceTargetEq res.eNew res.eqProof

/-- Close `(st s).HasWrites Y` (`Y` a global's lens in the program state) by an assignment of `Y`
in `s`, callees' bodies included. -/
partial def goStmt (g : MVarId) (fuel : Nat := 256) : MetaM Unit := g.withContext do
  if fuel == 0 then throwError "fp_writes: gave up"
  let ty ← instantiateMVars (← g.getType)
  let_expr Footprint.HasWrites _ _ R Y := ty | throwError "fp_writes: not a `HasWrites`"
  unless R.isAppOf ``InductiveFunctionGettersSetters.stmt do
    throwError "fp_writes: not a statement's footprint{indentExpr R}"
  let s := R.appArg!
  let s' ← whnf s
  let ctor? := match s'.getAppFn with
    | .const n _ => if n.getPrefix == ``StmtWithHoles then some n else none
    | _ => none
  let some ctor := ctor? | do
    -- a callee's body read off a module's procedure: its code
    let some p := s'.find? (·.isAppOf ``Module.Proc.procedure)
      | throwError "fp_writes: no code in{indentExpr s'}"
    let g ← g.replaceTargetDefEq (ty.replace fun e => if e == s then some s' else none)
    goStmt (← unfoldProcIn g p) (fuel - 1)
  let g ← g.replaceTargetDefEq (mkApp4 ty.getAppFn
    (ty.getArg! 0) (ty.getArg! 1) (mkApp R.appFn! s') Y)
  -- an assignment of `Y`: `liftLens X` (the assignment syntax's), `X` the variable (reducibly:
  -- comparing other variables' lenses unfolds them deeply)
  let leaf (lem : Name) (x : Lean.Expr) : MetaM Unit := do
    unless x.isAppOf ``liftLens do throwError "fp_writes: not a variable's assignment"
    let_expr Lens.intoGlobal _ X := Y | throwError "fp_writes: not a global"
    unless ← withReducible (isDefEq x.appArg! X) do throwError "fp_writes: another variable"
    let [hx] ← applyConst g lem | throwError "fp_writes: {lem}"
    let [hx'] ← applyConst hx ``setter | throwError "fp_writes: setter"
    let (_, hx'') ← hx'.intros
    hx''.refl
  let sub (lem : Name) : MetaM Unit := do
    let [g'] ← applyConst g lem | throwError "fp_writes: {lem}"
    goStmt g' (fuel - 1)
  let tries : List (MetaM Unit) := match ctor with
    | ``StmtWithHoles.sample => [leaf ``sample (s'.getArg! 2)]
    | ``StmtWithHoles.call' => [leaf ``call_set (s'.getArg! 2), sub ``call_body]
    | ``StmtWithHoles.hole => [leaf ``hole (s'.getArg! 3)]
    | ``StmtWithHoles.seq => [sub ``seq_left, sub ``seq_right]
    | ``StmtWithHoles.ifThenElse => [sub ``ite_left, sub ``ite_right]
    | ``StmtWithHoles.while => [sub ``while_body]
    | _ => []
  for t in tries do
    if ← attempt t then return
  throwError "fp_writes: no write in{indentExpr s'}"

/-- Close `(FVP.fvP M).HasWrites X` by an assignment of `X` in one of `M`'s procedures. -/
partial def goModule (g : MVarId) (fuel : Nat := 64) : MetaM Unit := g.withContext do
  if fuel == 0 then throwError "fp_writes: gave up"
  let ty ← instantiateMVars (← g.getType)
  let_expr Footprint.HasWrites _ _ R _ := ty | throwError "fp_writes: not a `HasWrites`"
  -- a procedure's code
  if R.isAppOf ``FVP.fvP_proc then
    let [g'] ← applyConst g ``procBody | throwError "fp_writes: proc"
    let g' ← g'.withContext do
      let ty' ← instantiateMVars (← g'.getType)
      let some p := ty'.find? (·.isAppOf ``Module.Proc.procedure) | pure g'
      unfoldProcIn g' p
    return ← goStmt g'
  let_expr FVP.fvP _ _ M := R | throwError "fp_writes: not a module's footprint{indentExpr R}"
  -- the module type, down to `Module (.proc sig)` or `Module (.prod T U)`
  let T ← whnf (← inferType M)
  unless T.isAppOfArity ``Module 1 do throwError "fp_writes: not a module{indentExpr T}"
  let rep ← whnf T.appArg!
  if rep.isAppOfArity ``ModuleTypeRep.proc 1 then
    let [g'] ← applyConst g ``module_proc | throwError "fp_writes: module_proc"
    return ← goModule g' (fuel - 1)
  if rep.isAppOfArity ``ModuleTypeRep.prod 2 then
    for lem in [``module_fst, ``module_snd] do
      if ← attempt (do
          let [g'] ← applyConst g lem | throwError "fp_writes: {lem}"
          goModule g' (fuel - 1)) then return
    throwError "fp_writes: no write in{indentExpr M}"
  throwError "fp_writes: a module of type{indentExpr rep}"

/-- The procedures of a module (`Module.Proc` leaves of its module type, by `Module.fst'` and
`Module.snd'`). -/
partial def procsOf (M : Lean.Expr) (fuel : Nat := 32) : MetaM (Array Lean.Expr) := do
  if fuel == 0 then throwError "fp_writes: gave up"
  let T ← whnf (← inferType M)
  unless T.isAppOfArity ``Module 1 do throwError "fp_writes: not a module{indentExpr T}"
  let rep ← whnf T.appArg!
  if rep.isAppOfArity ``ModuleTypeRep.proc 1 then
    return #[mkApp2 (mkConst ``Module.Proc.procedure) rep.appArg! M]
  if rep.isAppOfArity ``ModuleTypeRep.prod 2 then
    let (A, B) := (rep.getArg! 0, rep.getArg! 1)
    return (← procsOf (mkApp3 (mkConst ``Module.fst') A B M) (fuel - 1)) ++
      (← procsOf (mkApp3 (mkConst ``Module.snd') A B M) (fuel - 1))
  throwError "fp_writes: a module of type{indentExpr rep}"

/-- The globals the statement `s` assigns (`liftLens X`, `X` a lens into the globals), callees'
bodies included, added to `acc`. -/
partial def writesOfStmt (s : Lean.Expr) (acc : IO.Ref (Array Lean.Expr)) (fuel : Nat := 256) :
    MetaM Unit := do
  if fuel == 0 then throwError "fp_writes: gave up"
  let s' ← whnf s
  let add (x : Lean.Expr) : MetaM Unit := do
    unless x.isAppOf ``liftLens && (x.getArg! 1).isConstOf ``VariableAssignment do return
    let X := x.appArg!
    if X.hasLooseBVars then return
    unless ← (← acc.get).anyM fun Y => withReducible (isDefEq X Y) do acc.modify (·.push X)
  match s'.getAppFn with
  | .const ``StmtWithHoles.sample _ => add (s'.getArg! 2)
  | .const ``StmtWithHoles.call' _ =>
    add (s'.getArg! 2)
    writesOfStmt (s'.getArg! 6) acc (fuel - 1)
  | .const ``StmtWithHoles.hole _ => add (s'.getArg! 3)
  | .const ``StmtWithHoles.seq _ =>
    writesOfStmt (s'.getArg! 1) acc (fuel - 1)
    writesOfStmt (s'.getArg! 2) acc (fuel - 1)
  | .const ``StmtWithHoles.ifThenElse _ =>
    writesOfStmt (s'.getArg! 2) acc (fuel - 1)
    writesOfStmt (s'.getArg! 3) acc (fuel - 1)
  | .const ``StmtWithHoles.while _ => writesOfStmt (s'.getArg! 2) acc (fuel - 1)
  | .const ``StmtWithHoles.skip _ => pure ()
  | _ =>
    -- a callee's body read off a module's procedure: its code
    let some p := s'.find? (·.isAppOf ``Module.Proc.procedure)
      | throwError "fp_writes: no code in{indentExpr s'}"
    let r ← try Flatten.unfoldProcedure p catch _ => Flatten.unfoldProcedure p (views := true)
    writesOfStmt (s'.replace fun e => if e == p then some r.expr else none) acc (fuel - 1)

/-- The globals the module `M`'s code assigns. -/
def writesOf (M : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let acc ← IO.mkRef #[]
  for p in ← procsOf M do
    let r ← try Flatten.unfoldProcedure p catch _ => Flatten.unfoldProcedure p (views := true)
    writesOfStmt (← mkAppM ``ProcedureWithHoles.body #[r.expr]) acc
  acc.get

/-- `R.HasWrites X` for `X` a `Lens.pair` of variables a concrete module (`R = FVP.fvP M`)
writes. -/
partial def hasWritesPair (R X : Lean.Expr) : MetaM Lean.Expr := do
  if X.isAppOfArity ``Lens.pair 6 then
    let hx ← hasWritesPair R (X.getArg! 3)
    let hy ← hasWritesPair R (X.getArg! 4)
    return ← mkAppOptM ``Footprint.HasWrites.pair
      #[none, none, none, R, X.getArg! 3, X.getArg! 4, X.getArg! 5, hx, hy]
  let h ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Footprint.HasWrites #[R, X])
  goModule h.mvarId!
  instantiateMVars h

/-- The regions already read (`globRegion`'s results). -/
initialize globRegionCache : IO.Ref (Array (Lean.Expr × Option Lean.Expr)) ← IO.mkRef #[]

/-- **EC's `glob M` of a concrete module, off its code**: for `R = FVP.fvP M`, the variables `X`
`M` writes, if `M` touches nothing else (`fp_le`): the proof of
`∀ a b, (R.touched_getter.get a = R.touched_getter.get b) = (X.get a = X.get b)`. -/
def globRegion (R : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let_expr FVP.fvP _ _ M := R | return none
  if let some (_, r) := (← globRegionCache.get).find? (·.1 == R) then return r
  let s ← saveState
  let r ← try
      let xs ← writesOf M
      if xs.isEmpty then failure
      let mut U ← mkAppM ``Lens.footprint #[xs.back!]
      for x in xs.pop.reverse do
        U ← mkAppM ``Max.max #[← mkAppM ``Lens.footprint #[x], U]
      let some X ← TacticMisc.regionLens? U | failure
      -- `X.footprint = U`
      let lhs ← mkAppM ``Lens.footprint #[X]
      let t ← ({} : SimpTheorems).addConst ``Footprint.lens_pair
      let ctx ← Simp.mkContext (simpTheorems := #[t]) (congrTheorems := ← getSimpCongrTheorems)
      let (rU, _) ← simp lhs ctx
      unless ← isDefEq rU.expr U do failure
      let hU ← rU.getProof
      -- `R ≤ X.footprint`: `M` touches nothing else (its bounds, `fp_le`, or its code,
      -- `fp_module X`)
      let hle ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[R, U])
      let hle ← try
          FootprintUpper.solve hle.mvarId!
          mkAppM ``le_of_le_of_eq #[← instantiateMVars hle, ← mkEqSymm hU]
        catch _ =>
          let hle ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[R, lhs])
          -- (its inner `by within_lens` logs its failures: none may be left)
          let log ← Core.getMessageLog
          Core.resetMessageLog
          let gs ← try Elab.Term.TermElabM.run' <| Elab.Term.withoutErrToSorry do
              let XS ← Elab.Term.exprToSyntax X
              Elab.Tactic.run hle.mvarId! (Elab.Tactic.evalTactic (← `(tactic| fp_module $XS)))
            catch _ => pure [hle.mvarId!]
          let failed := (← Core.getMessageLog).hasErrors
          Core.setMessageLog log
          let pf ← instantiateMVars hle
          unless gs.isEmpty && !failed && !pf.hasSorry && !pf.hasMVar do failure
          pure pf
      let hw ← hasWritesPair R X
      pure (some (← instantiateMVars (← mkAppM ``touched_getter_eq_iff_of_writes #[hle, hw])))
    catch _ => s.restore; pure none
  globRegionCache.modify (·.push (R, r))
  return r

initialize TacticMisc.globRegionHook.set globRegion

end GlobWrites

open Lean Elab Tactic in
/-- `fp_writes`: close `(FVP.fvP M).HasWrites x` for a concrete module `M` whose code assigns the
global `x` somewhere (one of its procedures, a callee's body included). -/
elab "fp_writes" : tactic => liftMetaFinishingTactic GlobWrites.goModule

end GaudisCrypt
