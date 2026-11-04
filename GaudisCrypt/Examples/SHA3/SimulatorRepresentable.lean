import GaudisCrypt.Examples.SHA3.Indifferentiability
import GaudisCrypt.Logic.Representation
import GaudisCrypt.Logic.ConcreteFootprint

/-!
# Simulators are representable

A `SIMULATOR` is a functor from `DFUNCTIONALITY` (one procedure) to `PRIMITIVE` (three).  Each of
the result's procedures `f`, `fi`, as a functor of the oracle, is a first-order functor module
(`SIMULATOR.fF`, `SIMULATOR.fiF`: the simulator followed by a projection), and so is represented
(`Module.exists_representation_of_firstOrder`).  `SIMULATOR.RepresentedBy` also asks `init` to be
a fixed procedure, independent of the oracle (EasyCrypt's `init` calls nothing): that is the one
hypothesis of `SIMULATOR.representable_of_init`.  Removes exception E2 for a concrete simulator.
-/

namespace GaudisCrypt.SHA3.Indifferentiability

open GaudisCrypt

variable (p f_in f_out : Type)

/-- A `PRIMITIVE` built as a pair: its `init` is the first component. -/
theorem PRIMITIVE.init_pair {p f_in f_out : Type} (a : Module.Proc (procsig () -> Unit))
    (b : Module.Prod (Module.Proc (procsig (p) -> p)) (Module.Proc (procsig (p) -> p))) :
    PRIMITIVE.init p f_in f_out (Module.pair a b) = a :=
  Module.fst_pair a b

/-- The simulator's `init`, as a functor of the oracle. -/
noncomputable def SIMULATOR.initF (S : SIMULATOR p f_in f_out) :
    GaudisCrypt.Module (.arr (DFUNCTIONALITY.typeRep p f_in f_out) (.proc (procsig () -> Unit))) :=
  (ModuleExpression.abs (.fst (.app S.expression (.var 0)))).toModule
    (.abs (.fst (.app (Module.typed_weaken S _) (.var 0 (by simp)))))

/-- Applying `SIMULATOR.initF` is taking the `init` of the simulator's result. -/
theorem SIMULATOR.initF_app (S : SIMULATOR p f_in f_out) (F : DFUNCTIONALITY p f_in f_out) :
    Module.app' (SIMULATOR.initF p f_in f_out S) F =
      PRIMITIVE.init p f_in f_out (Module.app S F) := by
  apply Module.ext
  show (ModuleExpression.app (ModuleExpression.abs _).reduce F.expression).reduce =
    (ModuleExpression.fst (Module.app S F).expression).reduce
  rw [ModuleExpression.reduce_app_left, ModuleExpression.reduce_beta]
  show (ModuleExpression.fst (ModuleExpression.app
      (S.expression.substituteSimultaneously _) F.expression)).reduce = _
  rw [Module.substituteSimultaneously_expression]
  refine ModuleExpression.reduce_fst_cong _ _ ?_
  exact (ModuleExpression.reduce_idempotent _).symm

/-- The simulator's `f`, as a functor of the oracle. -/
noncomputable def SIMULATOR.fF (S : SIMULATOR p f_in f_out) :
    GaudisCrypt.Module (.arr (DFUNCTIONALITY.typeRep p f_in f_out) (.proc (procsig (p) -> p))) :=
  (ModuleExpression.abs (.fst (.snd (.app S.expression (.var 0))))).toModule
    (.abs (.fst (.snd (.app (Module.typed_weaken S _) (.var 0 (by simp))))))

/-- The simulator's `fi`, as a functor of the oracle. -/
noncomputable def SIMULATOR.fiF (S : SIMULATOR p f_in f_out) :
    GaudisCrypt.Module (.arr (DFUNCTIONALITY.typeRep p f_in f_out) (.proc (procsig (p) -> p))) :=
  (ModuleExpression.abs (.snd (.snd (.app S.expression (.var 0))))).toModule
    (.abs (.snd (.snd (.app (Module.typed_weaken S _) (.var 0 (by simp))))))

/-- Applying `SIMULATOR.fF` is taking the `f` of the simulator's result. -/
theorem SIMULATOR.fF_app (S : SIMULATOR p f_in f_out) (F : DFUNCTIONALITY p f_in f_out) :
    Module.app' (SIMULATOR.fF p f_in f_out S) F = PRIMITIVE.f p f_in f_out (Module.app S F) := by
  apply Module.ext
  show (ModuleExpression.app (ModuleExpression.abs _).reduce F.expression).reduce =
    (ModuleExpression.fst (ModuleExpression.snd (Module.app S F).expression).reduce).reduce
  rw [ModuleExpression.reduce_app_left, ModuleExpression.reduce_beta,
    ModuleExpression.reduce_fst_inner]
  show (ModuleExpression.fst (ModuleExpression.snd (ModuleExpression.app
      (S.expression.substituteSimultaneously _) F.expression))).reduce = _
  rw [Module.substituteSimultaneously_expression]
  refine ModuleExpression.reduce_fst_cong _ _ (ModuleExpression.reduce_snd_cong _ _ ?_)
  exact (ModuleExpression.reduce_idempotent _).symm

/-- Applying `SIMULATOR.fiF` is taking the `fi` of the simulator's result. -/
theorem SIMULATOR.fiF_app (S : SIMULATOR p f_in f_out) (F : DFUNCTIONALITY p f_in f_out) :
    Module.app' (SIMULATOR.fiF p f_in f_out S) F = PRIMITIVE.fi p f_in f_out (Module.app S F) := by
  apply Module.ext
  show (ModuleExpression.app (ModuleExpression.abs _).reduce F.expression).reduce =
    (ModuleExpression.snd (ModuleExpression.snd (Module.app S F).expression).reduce).reduce
  rw [ModuleExpression.reduce_app_left, ModuleExpression.reduce_beta,
    ModuleExpression.reduce_snd_inner]
  show (ModuleExpression.snd (ModuleExpression.snd (ModuleExpression.app
      (S.expression.substituteSimultaneously _) F.expression))).reduce = _
  rw [Module.substituteSimultaneously_expression]
  refine ModuleExpression.reduce_snd_cong _ _ (ModuleExpression.reduce_snd_cong _ _ ?_)
  exact (ModuleExpression.reduce_idempotent _).symm

/-- A procedure `f_in -> f_out` that touches no global (an oracle for `init`'s hole). -/
noncomputable def constProc [Nonempty f_in] [Nonempty f_out] : Procedure (procsig (f_in) -> f_out) :=
  proc (_x : f_in) : f_out { return (Classical.ofNonempty : f_out) }

/-- **A simulator whose `init` does not depend on the oracle is representable**
(`SIMULATOR.Representable`, exception E2 as a theorem): its procedures by
`Module.exists_representation_of_firstOrder`, `init`'s hole filled with `constProc`. -/
theorem SIMULATOR.representable_of_init [Nonempty f_in] [Nonempty f_out]
    (S : SIMULATOR p f_in f_out)
    (hinit : ∀ F F', (PRIMITIVE.init p f_in f_out (Module.app S F)).procedure =
      (PRIMITIVE.init p f_in f_out (Module.app S F')).procedure) :
    SIMULATOR.Representable p f_in f_out S := by
  have hT : (DFUNCTIONALITY.typeRep p f_in f_out).FirstOrder := by
    simp [DFUNCTIONALITY.typeRep, ModuleTypeRep.FirstOrder]
  have hne : ∀ {sig' : ProcedureSignature},
      HoleIndex ((DFUNCTIONALITY.typeRep p f_in f_out).holesApp .empty) sig' →
        (∀ U ∈ sig'.params, Nonempty U) ∧ Nonempty sig'.ret := fun n => by
    cases n with
    | zero => exact ⟨fun U hU => by simp at hU; subst hU; infer_instance, inferInstance⟩
    | succ n => nomatch n
  obtain ⟨pi, hpi, hdi⟩ :=
    Module.exists_representation_of_firstOrder hT hne (SIMULATOR.initF _ _ _ S)
  obtain ⟨pf, hpf, hdf⟩ := Module.exists_representation_of_firstOrder hT hne (SIMULATOR.fF _ _ _ S)
  obtain ⟨pfi, hpfi, hdfi⟩ :=
    Module.exists_representation_of_firstOrder hT hne (SIMULATOR.fiF _ _ _ S)
  -- `init`'s hole gets `constProc`
  let q : ∀ {sig : ProcedureSignature},
      HoleIndex ((DFUNCTIONALITY.typeRep p f_in f_out).holesApp .empty) sig →
        ProcedureWithHoles .empty sig :=
    HoleIndex.consFun (F := ProcedureWithHoles .empty)
      (ProcedureWithHoles.ofProc (constProc f_in f_out))
      (fun {_} (n : HoleIndex .empty _) => nomatch n)
  let F₀ : DFUNCTIONALITY p f_in f_out := Module.proc (constProc f_in f_out)
  refine ⟨pi.substHoles q, pf, pfi, ⟨fun F a => ?_, fun F a => ?_, fun F a => ?_, ?_⟩⟩
  · rw [hinit F F₀, ← SIMULATOR.initF_app, hdi F₀,
      ← pi.procedureDenotation_substHoles q _ PUnit.unit (fun n => by
        cases n with
        | zero =>
          refine (Module.procedure_proc' _).trans ?_
          exact (ProcedureWithHoles.ofProc_instantiate _ _).symm
        | succ n => nomatch n)]
  · rw [← SIMULATOR.fF_app]
    exact congrFun (hdf F) a
  · rw [← SIMULATOR.fiF_app]
    exact congrFun (hdfi F) a
  · refine sup_le (sup_le ((FVP.fvP_proc_substHoles_le pi q ⊥ fun n => ?_).trans
      (sup_le (hpi.trans ?_) bot_le)) (hpf.trans ?_)) (hpfi.trans ?_)
    · cases n with
      | zero =>
        show FVP.fvP_proc (ProcedureWithHoles.ofProc (constProc f_in f_out)) ≤ ⊥
        rw [FVP.fvP_proc_ofProc]
        exact FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _
      | succ n => nomatch n
    all_goals
      refine (FVP.fvPMexpr_upper_bound _).trans (le_of_eq ?_)
      exact sup_bot_eq _

end GaudisCrypt.SHA3.Indifferentiability
