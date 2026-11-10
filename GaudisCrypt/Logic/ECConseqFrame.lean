import GaudisCrypt.Logic.StmtSwap
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.HoareFrame
import GaudisCrypt.Logic.FrameTactics

/-!
# EasyCrypt's `conseq` keeps what the code does not modify

EC's `conseq (_: P' ==> Q')` on `c₁ ~ c₂ : P ==> Q` asks `P => P'` and
`forall &1 &2, P => forall (modified variables), Q' => Q`: the variables the code does not write
keep their values from the precondition.  Here that is a frame on each side
(`prhlStmt_conseq_frame`): the variables `Q` reads whose writes the code commutes with
(`Stmt.CommutesWith`, shown as for `stmt_swap`; such code keeps them, `Stmt.satisfies_keep`)
keep their values from the start, and the side goal is
`∀ σ₁ σ₂, P σ₁ σ₂ → ∀ τ₁ τ₂, (frames) → Q' τ₁ τ₂ → Q τ₁ τ₂`.  `equiv_conseq (: P ==> Q)` on
statements is this rule (`Logic/ECConseq.lean`).
-/

namespace GaudisCrypt

open GaudisCrypt.Lib.RO.Instantiate

open Classical in
/-- **A statement that commutes with every write to `x` keeps `x`**. -/
theorem Stmt.satisfies_keep {α : Type} (x : Lens α ProgramState) {s : Stmt}
    (h : ∀ v, s.CommutesWith (x.set v)) (σ : ProgramState) :
    (programDenotation s σ).satisfies fun r => x.get r.2 = x.get σ := by
  have hk : hoareStmt (fun τ => τ = σ) s (fun τ => x.get τ = x.get σ) := by
    rw [hoareStmt_iff_wp]
    intro τ hτ
    rw [hτ]
    have key : s.ewp (fun ρ => if x.get ρ = x.get σ then 0 else 1) σ = 0 := by
      have hc := h (x.get σ) (fun ρ => if x.get ρ = x.get σ then 0 else 1) σ
      rw [x.get_set] at hc
      rw [hc]
      simp only [x.set_get, if_true]
      exact le_antisymm (Stmt.ewp_const_le s 0 σ) bot_le
    rw [← key]
    simp only [Stmt.ewp]
    congr 1
    funext r
    by_cases hr : x.get r.2 = x.get σ <;> simp [Set.indicator, hr]
  exact hk.satisfies rfl

/-- `s` keeps `x`: every run ends with `x` as it started. -/
def Stmt.Keeps {α : Type} (x : Lens α ProgramState) (s : Stmt) : Prop :=
  ∀ c, hoareStmt (fun τ => x.get τ = c) s (fun τ => x.get τ = c)

namespace Stmt.Keeps

variable {α : Type} {x : Lens α ProgramState}

theorem satisfies {s : Stmt} (h : Stmt.Keeps x s) (σ : ProgramState) :
    (programDenotation s σ).satisfies fun r => x.get r.2 = x.get σ :=
  (h (x.get σ)).satisfies rfl

theorem «skip» : Stmt.Keeps x StmtWithHoles.skip := fun _ => hoare_skip_of_imp fun _ h => h

theorem seq {p q : Stmt} (hp : Stmt.Keeps x p) (hq : Stmt.Keeps x q) :
    Stmt.Keeps x (.seq p q) := fun c => hoare_seq (hq c) (hp c)

theorem ite {b : Getter Bool ProgramState} {p q : Stmt} (hp : Stmt.Keeps x p)
    (hq : Stmt.Keeps x q) : Stmt.Keeps x (.ifThenElse b p q) := fun c =>
  hoare_pre (hoare_if_wp (hp c) (hq c)) fun _ h => ⟨fun _ => h, fun _ => h⟩

theorem «while» {b : Getter Bool ProgramState} {body : Stmt} (h : Stmt.Keeps x body) :
    Stmt.Keeps x (.while b body) := fun c =>
  hoare_while _ (hoare_pre (h c) fun _ h => h.1) fun _ h _ => h

theorem assign {β : Type} {y : Setter β ProgramState} {e : Getter β ProgramState}
    (hy : ∀ v σ, x.get (y.set v σ) = x.get σ) : Stmt.Keeps x (.assign y e) := fun _ =>
  hoare_pre (hoare_assign_wp y e _) fun σ h => (hy _ σ).trans h

theorem sample {β : Type} {y : Setter β ProgramState} {e : Getter (SubProbability β) ProgramState}
    (hy : ∀ v σ, x.get (y.set v σ) = x.get σ) : Stmt.Keeps x (.sample y e) := fun _ =>
  hoare_pre (hoare_sample_wp y _) fun σ h a _ => (hy a σ).trans h

/-- A call keeps what neither its result nor the globals it leaves hold (a local other than the
result). -/
theorem «call» {sig : ProcedureSignature} {y : Setter sig.ret ProgramState} {p : Procedure sig}
    {args : Getter sig.ParamType ProgramState}
    (hy : ∀ r g σ, x.get (y.set r (ProgramState.globalL.set g σ)) = x.get σ) :
    Stmt.Keeps x (Stmt.call y p args) := fun _ =>
  hoare_pre (hoare_call_wp y p args (hoareProc_const p True) _) fun σ h =>
    ⟨trivial, fun r g _ => (hy r g σ).trans h⟩

/-- A call keeps a global `L` outside the callee's footprint. -/
theorem call_frame {sig : ProcedureSignature} {y : Setter sig.ret ProgramState}
    {p : Procedure sig} {args : Getter sig.ParamType ProgramState} {γ : Type}
    (L : Lens γ VariableAssignment)
    (hp : ∀ a, (procedureDenotation p a).inFootprint (L.footprint)ᶜ)
    (hy : ∀ r g σ, L.get g = L.get σ.globals →
      x.get (y.set r (ProgramState.globalL.set g σ)) = x.get σ) :
    Stmt.Keeps x (Stmt.call y p args) := fun _ =>
  hoare_pre (hoare_call_frame L hp) fun σ h r g hg => (hy r g σ hg).trans h

/-- A call keeps a global `L` outside the callee's footprint, its result written elsewhere. -/
theorem call_global {sig : ProcedureSignature} {y : Setter sig.ret ProgramState}
    {p : Procedure sig} {args : Getter sig.ParamType ProgramState} {γ : Type}
    (L : Lens γ VariableAssignment)
    (hp : ∀ a, (procedureDenotation p a).inFootprint (L.footprint)ᶜ)
    (hy : ∀ r σ, L.get (y.set r σ).globals = L.get σ.globals) :
    Stmt.Keeps L.intoGlobal (Stmt.call y p args) :=
  call_frame L hp fun r g σ hg => by
    rw [Lens.intoGlobal_get_eq, Lens.intoGlobal_get_eq, hy]
    exact hg

end Stmt.Keeps

/-- `s` keeps the region `F` of the globals (EC's `glob A`, `F = fvP A`): every run ends with
the same `F.touched_getter` of the globals as it started. -/
def Stmt.KeepsRegion (F : Footprint VariableAssignment) (s : Stmt) : Prop :=
  ∀ c, hoareStmt (fun τ => F.touched_getter.get τ.globals = c) s
    (fun τ => F.touched_getter.get τ.globals = c)

namespace Stmt.KeepsRegion

variable {F : Footprint VariableAssignment}

theorem satisfies {s : Stmt} (h : Stmt.KeepsRegion F s) (σ : ProgramState) :
    (programDenotation s σ).satisfies fun r =>
      F.touched_getter.get r.2.globals = F.touched_getter.get σ.globals :=
  (h (F.touched_getter.get σ.globals)).satisfies rfl

theorem «skip» : Stmt.KeepsRegion F StmtWithHoles.skip := fun _ => hoare_skip_of_imp fun _ h => h

theorem seq {p q : Stmt} (hp : Stmt.KeepsRegion F p) (hq : Stmt.KeepsRegion F q) :
    Stmt.KeepsRegion F (.seq p q) := fun c => hoare_seq (hq c) (hp c)

theorem ite {b : Getter Bool ProgramState} {p q : Stmt} (hp : Stmt.KeepsRegion F p)
    (hq : Stmt.KeepsRegion F q) : Stmt.KeepsRegion F (.ifThenElse b p q) := fun c =>
  hoare_pre (hoare_if_wp (hp c) (hq c)) fun _ h => ⟨fun _ => h, fun _ => h⟩

theorem «while» {b : Getter Bool ProgramState} {body : Stmt} (h : Stmt.KeepsRegion F body) :
    Stmt.KeepsRegion F (.while b body) := fun c =>
  hoare_while _ (hoare_pre (h c) fun _ h => h.1) fun _ h _ => h

theorem assign {β : Type} {y : Setter β ProgramState} {e : Getter β ProgramState}
    (hy : ∀ v σ, F.touched_getter.get (y.set v σ).globals = F.touched_getter.get σ.globals) :
    Stmt.KeepsRegion F (.assign y e) := fun _ =>
  hoare_pre (hoare_assign_wp y e _) fun σ h => (hy _ σ).trans h

theorem sample {β : Type} {y : Setter β ProgramState} {e : Getter (SubProbability β) ProgramState}
    (hy : ∀ v σ, F.touched_getter.get (y.set v σ).globals = F.touched_getter.get σ.globals) :
    Stmt.KeepsRegion F (.sample y e) := fun _ =>
  hoare_pre (hoare_sample_wp y _) fun σ h a _ => (hy a σ).trans h

end Stmt.KeepsRegion

theorem SubProbability.satisfies_and' {γ : Type*} {μ : SubProbability γ} {P Q : γ → Prop}
    (hP : μ.satisfies P) (hQ : μ.satisfies Q) : μ.satisfies fun x => P x ∧ Q x :=
  fun x hx => ⟨hP x hx, hQ x hx⟩

theorem SubProbability.satisfies_true' {γ : Type*} (μ : SubProbability γ) :
    μ.satisfies fun _ => True :=
  fun _ _ => trivial

/-- **EC's `conseq`, with frames**: `F₁`, `F₂` relate each side's state at the start to its
state at the end (what its code keeps). -/
theorem prhlStmt_conseq_frame {A A' B B' : ProgramState → ProgramState → Prop} {c₁ c₂ : Stmt}
    (F₁ F₂ : ProgramState → ProgramState → Prop)
    (hF₁ : ∀ σ, (programDenotation c₁ σ).satisfies fun r => F₁ σ r.2)
    (hF₂ : ∀ σ, (programDenotation c₂ σ).satisfies fun r => F₂ σ r.2)
    (h : prhlStmt A' c₁ c₂ B') (hA : ∀ σ₁ σ₂, A σ₁ σ₂ → A' σ₁ σ₂)
    (hB : ∀ σ₁ σ₂, A σ₁ σ₂ → ∀ τ₁ τ₂, F₁ σ₁ τ₁ → F₂ σ₂ τ₂ → B' τ₁ τ₂ → B τ₁ τ₂) :
    prhlStmt A c₁ c₂ B := by
  intro σ₁ σ₂ hAσ
  obtain ⟨μ, m1, m2, sat⟩ := h σ₁ σ₂ (hA _ _ hAσ)
  have h1 : μ.satisfies fun w => F₁ σ₁ w.1.2 :=
    coupling_satisfies_fst (B := fun r : Unit × ProgramState => F₁ σ₁ r.2) (by rw [m1]; exact hF₁ σ₁)
  have h2 : μ.satisfies fun w => F₂ σ₂ w.2.2 :=
    coupling_satisfies_snd (B := fun r : Unit × ProgramState => F₂ σ₂ r.2) (by rw [m2]; exact hF₂ σ₂)
  exact ⟨μ, m1, m2, fun w hw => hB σ₁ σ₂ hAσ _ _ (h1 w hw) (h2 w hw) (sat w hw)⟩

namespace ECConseqFrame

open Lean Meta Elab Tactic

/-- A proof of `Stmt.Keeps x s`, by the statement's syntax: writes to other variables (the side
equations by `StmtSwap.discharge`), calls keeping the caller's other locals, or a global outside
the callee's footprint (`fp_disjoint`). -/
partial def keepsOf (s x : Lean.Expr) : MetaM Lean.Expr := do
  let s ← TacticMisc.openStmt (← instantiateMVars s)
  let goal ← mkAppM ``Stmt.Keeps #[x, s]
  let byRule (lem : Name) (extra : Array (Name × Lean.Expr) := #[]) : MetaM Lean.Expr := do
    let c ← mkConstWithFreshMVarLevels lem
    let cTy ← inferType c
    let names := cTy.getForallBinderNames
    let (ms, _, concl) ← forallMetaTelescope cTy
    for (n, v) in extra do
      let some i := names.findIdx? (· == n) | throwError "keeps: no `{n}` in `{lem}`"
      unless ← isDefEq ms[i]! v do throwError "keeps: `{n}`"
    unless ← isDefEq concl goal do throwError "keeps: `{lem}` does not apply"
    for m in ms do
      if ← m.mvarId!.isAssigned then continue
      let t ← instantiateMVars (← inferType m)
      unless ← isProp t do continue
      let pf ← if t.isAppOf ``Stmt.Keeps then keepsOf t.appArg! x
        else if (← forallTelescope t fun _ b =>
            pure (b.isAppOf ``ProgramDenotation.inFootprint)) then do
          -- `∀ a, inFootprint (L.footprint)ᶜ` from the callee's `fvP` and `fp_disjoint`
          forallTelescope t fun as b => do
            let_expr ProgramDenotation.inFootprint _ _ den R := b
              | throwError "keeps: footprint"
            let p ← whnfR (den.getArg! 1)
            unless p.isAppOfArity ``Module.Proc.procedure 2 do throwError "keeps: callee"
            let hM ← mkAppM ``Module.Proc.inFootprint_fvP #[p.getArg! 1, as[0]!]
            let le ← mkFreshExprMVar
              (← mkAppM ``LE.le #[← mkAppM ``FVP.fvP #[p.getArg! 1], R])
            FootprintSolver.solve le.mvarId!
            mkLambdaFVars as (← mkAppM ``ProgramDenotation.inFootprint_mono #[hM, le])
        else StmtSwap.discharge t none
      unless ← isDefEq m pf do throwError "keeps: cannot use the proof of{indentExpr t}"
    instantiateMVars (mkAppN c ms)
  match s.getAppFn.constName? with
  | some ``StmtWithHoles.skip => byRule ``Stmt.Keeps.«skip»
  | some ``StmtWithHoles.seq => byRule ``Stmt.Keeps.seq
  | some ``StmtWithHoles.ifThenElse => byRule ``Stmt.Keeps.ite
  | some ``StmtWithHoles.while => byRule ``Stmt.Keeps.«while»
  | some ``StmtWithHoles.assign => byRule ``Stmt.Keeps.assign
  | some ``StmtWithHoles.sample => byRule ``Stmt.Keeps.sample
  | some ``StmtWithHoles.call | some ``Stmt.call | some ``StmtWithHoles.call' =>
    try byRule ``Stmt.Keeps.«call»
    catch _ =>
      -- a global `L.intoGlobal`, outside the callee
      unless x.isAppOfArity ``Lens.intoGlobal 2 do throwError "keeps: the call"
      byRule ``Stmt.Keeps.call_global #[(`L, x.appArg!)]
  | _ => throwError "keeps: no rule for{indentExpr s}"

/-- A write keeps the region: `∀ v σ, F.touched_getter.get (y.set v σ).globals = …` — a local
(the globals unchanged) or a global outside `F` (`touched_set_of_le_compl`, `fp_disjoint`). -/
def dischargeRegionWrite (ty : Lean.Expr) : MetaM Lean.Expr := do
  let m ← mkFreshExprMVar ty
  let log ← Core.getMessageLog
  try
    let gs ← Elab.Term.TermElabM.run' <| Elab.Term.withoutErrToSorry <|
      Elab.Tactic.run m.mvarId! do
        Elab.Tactic.evalTactic (← `(tactic| (
          intro v σ
          simp only [liftLens, LiftLens.lift, Lens.pair, localVarLens, globals_intoLocal_set,
            globals_intoGlobal_set, globals_resetSetter_set, globals_globalL_set,
            Setter.throwaway_set]
          repeat (rw [GaudisCrypt.touched_set_of_le_compl ?_]; rotate_left; fp_disjoint)
          done)))
    unless gs.isEmpty do throwError "keeps region: a write"
    if (← Core.getMessageLog).hasErrors then throwError "keeps region: a write"
    let pf ← instantiateMVars m
    if pf.hasSyntheticSorry || pf.hasSorry then throwError "keeps region: a write"
    return pf
  finally
    Core.setMessageLog log

/-- A proof of `Stmt.KeepsRegion F s`, by the statement's syntax (no calls). -/
partial def keepsRegionOf (s F : Lean.Expr) : MetaM Lean.Expr := do
  let s ← TacticMisc.openStmt (← instantiateMVars s)
  let goal ← mkAppM ``Stmt.KeepsRegion #[F, s]
  let byRule (lem : Name) : MetaM Lean.Expr := do
    let c ← mkConstWithFreshMVarLevels lem
    let (ms, _, concl) ← forallMetaTelescope (← inferType c)
    unless ← isDefEq concl goal do throwError "keeps region: `{lem}` does not apply"
    for m in ms do
      if ← m.mvarId!.isAssigned then continue
      let t ← instantiateMVars (← inferType m)
      unless ← isProp t do continue
      let pf ← if t.isAppOf ``Stmt.KeepsRegion then keepsRegionOf t.appArg! F
        else dischargeRegionWrite t
      unless ← isDefEq m pf do throwError "keeps region: cannot use the proof of{indentExpr t}"
    instantiateMVars (mkAppN c ms)
  match s.getAppFn.constName? with
  | some ``StmtWithHoles.skip => byRule ``Stmt.KeepsRegion.«skip»
  | some ``StmtWithHoles.seq => byRule ``Stmt.KeepsRegion.seq
  | some ``StmtWithHoles.ifThenElse => byRule ``Stmt.KeepsRegion.ite
  | some ``StmtWithHoles.while => byRule ``Stmt.KeepsRegion.«while»
  | some ``StmtWithHoles.assign => byRule ``Stmt.KeepsRegion.assign
  | some ``StmtWithHoles.sample => byRule ``Stmt.KeepsRegion.sample
  | _ => throwError "keeps region: no rule for{indentExpr s}"

/-- The regions `F` whose `F.touched_getter` the conditions `es` read (EC's `glob A`). -/
def regionsOf (es : Array Lean.Expr) : MetaM (Array Lean.Expr) := do
  let out ← IO.mkRef (#[] : Array Lean.Expr)
  for e in es do
    Meta.forEachExpr (← instantiateMVars e) fun t => do
      if t.isAppOfArity ``Footprint.touched_getter 2 && !t.hasLooseBVars then
        let F := t.appArg!
        unless (← out.get).contains F do out.modify (·.push F)
  out.get

/-- The frame of the statement `s` for the variables `xs` (lenses of the program state): those
it keeps (`keepsOf`), as `fun σ τ => x.get τ = x.get σ ∧ …`, and the proof of
`∀ σ, (programDenotation s σ).satisfies fun r => F σ r.2`. -/
def frameOf (s : Lean.Expr) (xs : Array Lean.Expr) (regions : Array Lean.Expr := #[]) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let ps := mkConst ``ProgramState
  -- the `let`s of the locals by their values (the same statement, by `zeta`)
  let s ← Meta.transform (← instantiateMVars s) (pre := fun e => do
    if let .letE _ _ v b _ := e then return .visit (b.instantiate1 v)
    return .continue)
  let mut kept : Array (Lean.Expr × Lean.Expr) := #[]
  for x in xs do
    let s' ← saveState
    try
      let pf ← keepsOf s x
      unless (← isTypeCorrect pf) do throwError "frame"
      kept := kept.push (x, pf)
    catch _ => s'.restore
  let mut keptR : Array (Lean.Expr × Lean.Expr) := #[]
  for F in regions do
    let s' ← saveState
    try
      let pf ← keepsRegionOf s F
      unless (← isTypeCorrect pf) do throwError "frame"
      keptR := keptR.push (F, pf)
    catch _ => s'.restore
  withLocalDeclD `σ ps fun σ => withLocalDeclD `τ ps fun τ => do
    -- a global as the conditions read it, `X.get σ.globals` (`X.intoGlobal.get σ`, by `rfl`)
    let get (x st : Lean.Expr) : MetaM Lean.Expr := do
      if x.isAppOfArity ``Lens.intoGlobal 2 then
        return ← mkAppM ``Getter.get #[← mkAppM ``Lens.toGetter #[x.appArg!],
          ← mkAppM ``ProgramState.globals #[st]]
      mkAppM ``Getter.get #[← mkAppM ``Lens.toGetter #[x], st]
    let getR (F st : Lean.Expr) : MetaM Lean.Expr := do
      mkAppM ``Getter.get #[← mkAppM ``Footprint.touched_getter #[F],
        ← mkAppM ``ProgramState.globals #[st]]
    let mut body := mkConst ``True
    for (F, _) in keptR.reverse do
      body ← mkAppM ``And #[← mkEq (← getR F τ) (← getR F σ), body]
    for (x, _) in kept.reverse do
      body ← mkAppM ``And #[← mkEq (← get x τ) (← get x σ), body]
    let F ← mkLambdaFVars #[σ, τ] body
    let μ ← mkAppM ``programDenotation #[s, σ]
    let mut pf ← mkAppM ``SubProbability.satisfies_true' #[μ]
    for (_, hk) in keptR.reverse do
      pf ← mkAppM ``SubProbability.satisfies_and'
        #[← mkAppM ``Stmt.KeepsRegion.satisfies #[hk, σ], pf]
    for (_, hk) in kept.reverse do
      pf ← mkAppM ``SubProbability.satisfies_and' #[← mkAppM ``Stmt.Keeps.satisfies #[hk, σ], pf]
    return (F, ← mkLambdaFVars #[σ] pf)

end ECConseqFrame

end GaudisCrypt
