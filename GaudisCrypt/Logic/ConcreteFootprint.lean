import GaudisCrypt.Logic.Representation
import GaudisCrypt.Logic.SyntacticFrame
import GaudisCrypt.Logic.PRHLWp

/-!
# The footprint of concrete code that only uses locals

`FVP.fvP` of a module is a syntactic over-approximation of what it touches.  For a concrete
procedure whose reads and writes are all on local variables (`StmtWithHoles.LocalsOnly`), it is
`⊥` (`FVP.fvP_proc_le_of_localsOnly`): such reads and writes are zooms along `localL`, which is
disjoint from the globals.  `locals_only` proves `LocalsOnly` for a module's procedure,
unfolding it as the inliner does and closing the reads and writes of local variables by `rfl`.
What it cannot close is a read or write of a global.

This is what makes a concrete wrapper of abstract modules (`RODist(D)`, …) finitely supported
when the abstract modules are.

More generally, a procedure whose reads and writes touch the globals only through a lens `X`
(`StmtWithHoles.Within X`) touches only `X` (`FVP.fvP_proc_le_of_within`): such reads and writes
are zooms along the pair of the locals and `X` (`ProgramState.withinL X`).  `within_lens` proves
`Within X` as `locals_only` proves `LocalsOnly`.  This is how a concrete oracle (PROM's
`RRO.resample`) is confined to its module variable.
-/

namespace GaudisCrypt

/-- A read that does not depend on the globals. -/
def Getter.LocalsOnly {α : Type} (e : Getter α ProgramState) : Prop :=
  ∀ g σ, e.get (ProgramState.globalL.set g σ) = e.get σ

/-- A write that keeps the globals and commutes with writing them. -/
def Setter.LocalsOnly {α : Type} (x : Setter α ProgramState) : Prop :=
  ∀ v g σ, x.set v (ProgramState.globalL.set g σ) = ProgramState.globalL.set g (x.set v σ) ∧
    (x.set v σ).globals = σ.globals

theorem Getter.LocalsOnly.footprint_le {α : Type} {e : Getter α ProgramState}
    (he : e.LocalsOnly) :
    (ProgramDenotation.get e).footprint ≤ (ProgramState.globalL.footprint)ᶜ := by
  have hz : ProgramDenotation.get e = ProgramDenotation.get
      (⟨fun σ => (⟨fun m => e.get ⟨VariableAssignment.init, m⟩⟩ :
        Getter α VariableAssignment).get σ.locals⟩ : Getter α ProgramState) := by
    funext σ
    rw [ProgramDenotation.get_apply', ProgramDenotation.get_apply']
    congr 2
    exact he σ.globals ⟨VariableAssignment.init, σ.locals⟩
  rw [hz]
  exact footprint_get_locals_le _

theorem Setter.LocalsOnly.footprint'_le {α : Type} {x : Setter α ProgramState}
    (hx : x.LocalsOnly) :
    ProgramDenotation.footprint' (ProgramDenotation.set x) ≤
      (ProgramState.globalL.footprint)ᶜ := by
  refine footprint'_set_le_of_locals x
    (fun v m => (x.set v ⟨VariableAssignment.init, m⟩).locals) fun v σ => ?_
  obtain ⟨h1, h2⟩ := hx v σ.globals ⟨VariableAssignment.init, σ.locals⟩
  have hσ : ProgramState.globalL.set σ.globals ⟨VariableAssignment.init, σ.locals⟩ = σ := rfl
  rw [hσ] at h1
  rw [h1]
  change (⟨σ.globals, _⟩ : ProgramState) = ⟨σ.globals, _⟩
  rfl

/-- Every read and write of the statement, its callees' included, is on the locals alone. -/
def StmtWithHoles.LocalsOnly {h : HoleSigs} : StmtWithHoles h → Prop
  | .skip => True
  | .sample x e => x.LocalsOnly ∧ e.LocalsOnly
  | .call' x _ _ _ b r p => x.LocalsOnly ∧ b.LocalsOnly ∧ r.LocalsOnly ∧ p.LocalsOnly
  | .hole _ x p => x.LocalsOnly ∧ p.LocalsOnly
  | .seq s t => s.LocalsOnly ∧ t.LocalsOnly
  | .ifThenElse c t e => c.LocalsOnly ∧ t.LocalsOnly ∧ e.LocalsOnly
  | .while c t => c.LocalsOnly ∧ t.LocalsOnly

local notation "rg" => Lens.reduceFootprint ProgramState.globalL

/-- **A statement on the locals alone has no globals' share.** -/
theorem StmtWithHoles.LocalsOnly.reduce_le {h : HoleSigs} (R : Footprint VariableAssignment) :
    ∀ s : StmtWithHoles h, s.LocalsOnly → rg (FVP.fvpInductiveFunctionGS.stmt s) ≤ R
  | .skip, _ => by
      simp only [InductiveFunctionGettersSetters.stmt, fvpGS_nothing]
      exact reduce_globalL_le_of_le_compl bot_le R
  | .sample x e, hs => by
      obtain ⟨hx, he⟩ := (show _ ∧ _ from hs)
      simp only [InductiveFunctionGettersSetters.stmt, fvpGS_join, fvpGS_getter, fvpGS_setter,
        Lens.reduceFootprint_sup]
      exact sup_le (reduce_globalL_le_of_le_compl hx.footprint'_le R)
        (reduce_globalL_le_of_le_compl he.footprint_le R)
  | .call' x ns hl hn b r p, hs => by
      obtain ⟨hx, hb, hr, hp⟩ := (show _ ∧ _ ∧ _ ∧ _ from hs)
      simp only [InductiveFunctionGettersSetters.stmt, InductiveFunctionGettersSetters.transfer,
        fvpGS_join, fvpGS_getter, fvpGS_setter, fvpGS_reduce, Lens.reduceFootprint_sup]
      refine sup_le (reduce_globalL_le_of_le_compl hx.footprint'_le R) (sup_le ?_ (sup_le ?_
        (reduce_globalL_le_of_le_compl hp.footprint_le R)))
      · exact (FVP.Lens.reduceFootprint_extend_le _ _).trans
          (StmtWithHoles.LocalsOnly.reduce_le R b hb)
      · exact (FVP.Lens.reduceFootprint_extend_le _ _).trans
          (reduce_globalL_le_of_le_compl hr.footprint_le R)
  | .hole n x p, hs => by
      obtain ⟨hx, hp⟩ := (show _ ∧ _ from hs)
      simp only [InductiveFunctionGettersSetters.stmt, fvpGS_join, fvpGS_getter, fvpGS_setter,
        Lens.reduceFootprint_sup]
      exact sup_le (reduce_globalL_le_of_le_compl hx.footprint'_le R)
        (reduce_globalL_le_of_le_compl hp.footprint_le R)
  | .seq s t, hs => by
      obtain ⟨h1, h2⟩ := (show _ ∧ _ from hs)
      simp only [InductiveFunctionGettersSetters.stmt, fvpGS_join, Lens.reduceFootprint_sup]
      exact sup_le (StmtWithHoles.LocalsOnly.reduce_le R s h1)
        (StmtWithHoles.LocalsOnly.reduce_le R t h2)
  | .ifThenElse c t e, hs => by
      obtain ⟨hc, h1, h2⟩ := (show _ ∧ _ ∧ _ from hs)
      simp only [InductiveFunctionGettersSetters.stmt, fvpGS_join, fvpGS_getter,
        Lens.reduceFootprint_sup]
      exact sup_le (reduce_globalL_le_of_le_compl hc.footprint_le R)
        (sup_le (StmtWithHoles.LocalsOnly.reduce_le R t h1)
          (StmtWithHoles.LocalsOnly.reduce_le R e h2))
  | .while c t, hs => by
      obtain ⟨hc, h1⟩ := (show _ ∧ _ from hs)
      simp only [InductiveFunctionGettersSetters.stmt, fvpGS_join, fvpGS_getter,
        Lens.reduceFootprint_sup]
      exact sup_le (reduce_globalL_le_of_le_compl hc.footprint_le R)
        (StmtWithHoles.LocalsOnly.reduce_le R t h1)
termination_by s => s.depth
decreasing_by all_goals simp [StmtWithHoles.depth]; try omega

/-- **A procedure on the locals alone touches no globals.** -/
theorem FVP.fvP_proc_le_of_localsOnly {h : HoleSigs} {sig : ProcedureSignature}
    (p : ProcedureWithHoles h sig) (hb : p.body.LocalsOnly) (hr : p.return_val.LocalsOnly)
    (R : Footprint VariableAssignment) : FVP.fvP_proc p ≤ R := by
  simp only [FVP.fvP_proc, InductiveFunctionGettersSetters.proc, fvpGS_reduce, fvpGS_getter]
  exact sup_le (StmtWithHoles.LocalsOnly.reduce_le R _ hb)
    (reduce_globalL_le_of_le_compl hr.footprint_le R)

/-! ## `fvP` of module expressions, by the expression -/

local notation "E" => FVP.fvpInductiveFunctionGS.evalMexpr

@[simp] theorem evalMexpr_app (a b : ModuleExpression) : E (.app a b) = E a ⊔ E b := rfl
@[simp] theorem evalMexpr_abs (b : ModuleExpression) : E (.abs b) = E b := rfl
@[simp] theorem evalMexpr_pair (a b : ModuleExpression) : E (.pair a b) = E a ⊔ E b := rfl
@[simp] theorem evalMexpr_var (n : Nat) : E (.var n) = ⊥ := rfl
@[simp] theorem evalMexpr_unit : E .unit = ⊥ := rfl
@[simp] theorem evalMexpr_fst (e : ModuleExpression) : E (.fst e) = E e := rfl
@[simp] theorem evalMexpr_snd (e : ModuleExpression) : E (.snd e) = E e := rfl
@[simp] theorem evalMexpr_proc {sig} (p : Procedure sig) : E (.proc p) = FVP.fvP_proc p := rfl
@[simp] theorem evalMexpr_procHoles {holes sig} (ne : holes.NonEmpty)
    (p : ProcedureWithHoles holes sig) : E (.procHoles ne p) = FVP.fvP_proc p := rfl

theorem evalMexpr_toModule_le {T : ModuleTypeRep} (m : ModuleExpression) (h : m.HasType [] T) :
    E (m.toModule h).expression ≤ E m := FVP.fvPMexpr_upper_bound h

theorem evalMexpr_procWithHoles_le {holes : HoleSigs} {sig : ProcedureSignature}
    (p : ProcedureWithHoles holes sig) : E (Module.procWithHoles p).expression ≤ FVP.fvP_proc p := by
  cases holes with
  | empty =>
      simp only [Module.procWithHoles, Module.const, Module.proc]
      refine (evalMexpr_toModule_le _ _).trans ?_
      simp only [evalMexpr_abs]
      refine (evalMexpr_toModule_le _ _).trans ?_
      simp
  | cons s h =>
      simp only [Module.procWithHoles]
      exact (evalMexpr_toModule_le _ _).trans le_rfl

open Lean Elab Tactic in
/-- `locals_only`: on a goal `StmtWithHoles.LocalsOnly s` (or `Getter.LocalsOnly`,
`Setter.LocalsOnly`), the conditions on the single reads and writes of `s`, callees included;
those on local variables are closed by `rfl`. -/
elab "locals_only" : tactic => do
  liftMetaTactic (stmtPredSplit ``StmtWithHoles.LocalsOnly ·)
  evalTactic (← `(tactic| all_goals first
    | exact fun _ _ => rfl
    | exact fun _ _ _ => ⟨rfl, rfl⟩
    | skip))

section Within

variable {Ω : Type} (X : Lens Ω VariableAssignment)

instance ProgramState.disjoint_localL_chain :
    Lens.Disjoint ProgramState.localL (ProgramState.globalL.chain X) := ⟨fun _ _ _ => rfl⟩

/-- The locals and `X`'s part of the globals, as one lens. -/
abbrev ProgramState.withinL : Lens (VariableAssignment × Ω) ProgramState :=
  Lens.pair ProgramState.localL (ProgramState.globalL.chain X)

/-- A read that depends on the globals only through `X`. -/
def Getter.Within {α : Type} (e : Getter α ProgramState) : Prop :=
  ∀ g σ, X.get g = X.get σ.globals → e.get ⟨g, σ.locals⟩ = e.get σ

/-- A write that changes the globals only through `X`, as a function of the locals and `X`. -/
def Setter.Within {α : Type} (x : Setter α ProgramState) : Prop :=
  ∀ v g σ, X.get g = X.get σ.globals →
    x.set v ⟨g, σ.locals⟩ = ⟨X.set (X.get (x.set v σ).globals) g, (x.set v σ).locals⟩

theorem reduce_globalL_withinL_le :
    Lens.reduceFootprint ProgramState.globalL (ProgramState.withinL X).footprint ≤ X.footprint := by
  rw [Footprint.lens_pair, Lens.reduceFootprint_sup]
  exact sup_le (reduce_globalL_le_of_le_compl
      (Lens.footprint_le_compl_of_disjoint ProgramState.localL ProgramState.globalL) _)
    (by rw [Lens.footprint_chain]; exact (FVP.Lens.reduceFootprint_extend _ _).le)

theorem footprint_zoom_withinL_le {α : Type} (q : ProgramDenotation (VariableAssignment × Ω) α) :
    (ProgramDenotation.zoom (ProgramState.withinL X) q).footprint ≤
      (ProgramState.withinL X).footprint := by
  have hz : ProgramDenotation.zoom (ProgramState.withinL X) q =
      (ProgramState.withinL X).lift q := by
    funext σ
    simp only [ProgramDenotation.zoom, Lens.lift]
    rw [SubProbability.hbind_eq_bind]
  rw [hz]
  exact ProgramDenotation.footprint_le_of_inFootprint (Lib.RO.Instantiate.lift_inFootprint_self _ _)

variable {X}

theorem Getter.Within.reduce_le {α : Type} {e : Getter α ProgramState} (he : e.Within X) :
    Lens.reduceFootprint ProgramState.globalL (ProgramDenotation.get e).footprint ≤
      X.footprint := by
  have hz : e = (ProgramState.withinL X).chainGetter
      ⟨fun p => e.get ⟨X.set p.2 VariableAssignment.init, p.1⟩⟩ := by
    cases e with
    | mk f =>
      congr 1; funext σ
      exact (he (X.set (X.get σ.globals) VariableAssignment.init) σ (X.set_get _ _)).symm
  rw [hz, ← ProgramDenotation.zoom_get]
  exact (Lens.reduceFootprint_mono _ (footprint_zoom_withinL_le X _)).trans
    (reduce_globalL_withinL_le X)

theorem Setter.Within.reduce_le {α : Type} {x : Setter α ProgramState} (hx : x.Within X) :
    Lens.reduceFootprint ProgramState.globalL
      (ProgramDenotation.footprint' (ProgramDenotation.set x)) ≤ X.footprint := by
  refine (Lens.reduceFootprint_mono _ (iSup_le fun v => ?_)).trans (reduce_globalL_withinL_le X)
  have hz : ProgramDenotation.set x v = ProgramDenotation.zoom (ProgramState.withinL X)
      (fun p => pure ((), ((x.set v ⟨X.set p.2 VariableAssignment.init, p.1⟩).locals,
        X.get (x.set v ⟨X.set p.2 VariableAssignment.init, p.1⟩).globals))) := by
    funext σ
    rw [ProgramDenotation.set_apply']
    simp only [ProgramDenotation.zoom, SubProbability.pure_hbind]
    have h1 := hx v (X.set (X.get σ.globals) VariableAssignment.init) σ (X.set_get _ _)
    have h2 := hx v σ.globals σ rfl
    congr 2
    change x.set v σ = ⟨X.set (X.get (x.set v ⟨X.set (X.get σ.globals) VariableAssignment.init,
      σ.locals⟩).globals) σ.globals, (x.set v ⟨X.set (X.get σ.globals) VariableAssignment.init,
      σ.locals⟩).locals⟩
    rw [h1]
    dsimp only
    rw [X.set_get]
    exact h2
  rw [hz]
  exact footprint_zoom_withinL_le X _

/-- A write of the locals alone is within any `X`. -/
theorem Setter.within_of_locals {α : Type} {x : Setter α ProgramState}
    (hl : ∀ v g σ, x.set v ⟨g, σ.locals⟩ = ⟨g, (x.set v σ).locals⟩)
    (hg : ∀ v σ, (x.set v σ).globals = σ.globals) : x.Within X := by
  intro v g σ h
  rw [hl, hg, ← h, X.get_set]

/-- A write of `X` itself is within `X`. -/
theorem Setter.within_self {x : Setter Ω ProgramState}
    (hx : ∀ v σ, x.set v σ = ⟨X.set v σ.globals, σ.locals⟩) : x.Within X := by
  intro v g σ _
  rw [hx, hx, X.set_get]

/-- Every read and write of the statement, its callees' included, touches the globals only
through `X`. -/
def StmtWithHoles.Within (X : Lens Ω VariableAssignment) {h : HoleSigs} :
    StmtWithHoles h → Prop
  | .skip => True
  | .sample x e => x.Within X ∧ e.Within X
  | .call' x _ _ _ b r p => x.Within X ∧ b.Within X ∧ r.Within X ∧ p.Within X
  | .hole _ x p => x.Within X ∧ p.Within X
  | .seq s t => s.Within X ∧ t.Within X
  | .ifThenElse c t e => c.Within X ∧ t.Within X ∧ e.Within X
  | .while c t => c.Within X ∧ t.Within X

/-- **A statement within `X` has its globals' share in `X`.** -/
theorem StmtWithHoles.Within.reduce_le {h : HoleSigs} :
    ∀ s : StmtWithHoles h, s.Within X → rg (FVP.fvpInductiveFunctionGS.stmt s) ≤ X.footprint
  | .skip, _ => by
      simp only [InductiveFunctionGettersSetters.stmt, fvpGS_nothing]
      exact reduce_globalL_le_of_le_compl bot_le _
  | .sample x e, hs => by
      obtain ⟨hx, he⟩ := (show _ ∧ _ from hs)
      simp only [InductiveFunctionGettersSetters.stmt, fvpGS_join, fvpGS_getter, fvpGS_setter,
        Lens.reduceFootprint_sup]
      exact sup_le hx.reduce_le he.reduce_le
  | .call' x ns hl hn b r p, hs => by
      obtain ⟨hx, hb, hr, hp⟩ := (show _ ∧ _ ∧ _ ∧ _ from hs)
      simp only [InductiveFunctionGettersSetters.stmt, InductiveFunctionGettersSetters.transfer,
        fvpGS_join, fvpGS_getter, fvpGS_setter, fvpGS_reduce, Lens.reduceFootprint_sup]
      refine sup_le hx.reduce_le (sup_le ?_ (sup_le ?_ hp.reduce_le))
      · exact (FVP.Lens.reduceFootprint_extend_le _ _).trans
          (StmtWithHoles.Within.reduce_le b hb)
      · exact (FVP.Lens.reduceFootprint_extend_le _ _).trans hr.reduce_le
  | .hole n x p, hs => by
      obtain ⟨hx, hp⟩ := (show _ ∧ _ from hs)
      simp only [InductiveFunctionGettersSetters.stmt, fvpGS_join, fvpGS_getter, fvpGS_setter,
        Lens.reduceFootprint_sup]
      exact sup_le hx.reduce_le hp.reduce_le
  | .seq s t, hs => by
      obtain ⟨h1, h2⟩ := (show _ ∧ _ from hs)
      simp only [InductiveFunctionGettersSetters.stmt, fvpGS_join, Lens.reduceFootprint_sup]
      exact sup_le (StmtWithHoles.Within.reduce_le s h1) (StmtWithHoles.Within.reduce_le t h2)
  | .ifThenElse c t e, hs => by
      obtain ⟨hc, h1, h2⟩ := (show _ ∧ _ ∧ _ from hs)
      simp only [InductiveFunctionGettersSetters.stmt, fvpGS_join, fvpGS_getter,
        Lens.reduceFootprint_sup]
      exact sup_le hc.reduce_le
        (sup_le (StmtWithHoles.Within.reduce_le t h1) (StmtWithHoles.Within.reduce_le e h2))
  | .while c t, hs => by
      obtain ⟨hc, h1⟩ := (show _ ∧ _ from hs)
      simp only [InductiveFunctionGettersSetters.stmt, fvpGS_join, fvpGS_getter,
        Lens.reduceFootprint_sup]
      exact sup_le hc.reduce_le (StmtWithHoles.Within.reduce_le t h1)
termination_by s => s.depth
decreasing_by all_goals simp [StmtWithHoles.depth]; try omega

/-- **A procedure within `X` touches only `X`.** -/
theorem FVP.fvP_proc_le_of_within {h : HoleSigs} {sig : ProcedureSignature}
    (p : ProcedureWithHoles h sig) (hb : p.body.Within X) (hr : p.return_val.Within X) :
    FVP.fvP_proc p ≤ X.footprint := by
  simp only [FVP.fvP_proc, InductiveFunctionGettersSetters.proc, fvpGS_reduce, fvpGS_getter]
  exact sup_le (StmtWithHoles.Within.reduce_le _ hb) hr.reduce_le

/-- A procedure within `X` runs confined to `X`. -/
theorem procedureDenotation_inFootprint_of_within {sig : ProcedureSignature} (p : Procedure sig)
    (hb : p.body.Within X) (hr : p.return_val.Within X) (a : sig.ParamType) :
    (procedureDenotation p a).inFootprint X.footprint :=
  ProgramDenotation.inFootprint_mono
    (Lib.RO.Instantiate.procedureDenotation_inFootprint_fvP_proc p a)
    (FVP.fvP_proc_le_of_within p hb hr)

end Within

open Lean Meta in
/-- Unfold every module procedure (`Module.Proc.procedure M`) in the goal, as the inliner does. -/
partial def unfoldModuleProcs (g : MVarId) (fuel : Nat := 64) : MetaM MVarId := do
  if fuel == 0 then return g
  let ty ← instantiateMVars (← g.getType)
  let some p := ty.find? (·.isAppOf ``Module.Proc.procedure) | return g
  let r ← Flatten.unfoldProcedure p
  let g ← match r.proof? with
    | none => g.replaceTargetDefEq (ty.replace fun e => if e == p then some r.expr else none)
    | some h => do
      let res ← g.rewrite ty h
      g.replaceTargetEq res.eNew res.eqProof
  unfoldModuleProcs g (fuel - 1)

open Lean Elab Tactic in
/-- `within_lens`: on a goal `StmtWithHoles.Within X s` (or `Getter.Within`, `Setter.Within`), the
conditions on the single reads and writes of `s`, callees included.  Reads and writes of local
variables, writes of `X` and reads of expressions in `X` and the locals are closed. -/
elab "within_lens" : tactic => do
  liftMetaTactic (stmtPredSplit ``StmtWithHoles.Within ·)
  -- a return value: unfold the procedure it is read off, if any
  evalTactic (← `(tactic| all_goals run_tac liftMetaTactic1 fun g => some <$> unfoldModuleProcs g))
  evalTactic (← `(tactic| all_goals first
    | exact fun _ _ _ => rfl
    | exact Setter.within_of_locals (fun _ _ _ => rfl) (fun _ _ => rfl)
    | exact Setter.within_self (fun _ _ => rfl)
    | exact fun _ _ h => by simp_reads; simp only [h]; try rfl
    | skip))

end GaudisCrypt
