import GaudisCrypt.Logic.Representation
import GaudisCrypt.Logic.SyntacticFrame

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

end GaudisCrypt
