-- CHAOS FILE

import GaudisCrypt.Language.Modules.InductiveFunctions

open GaudisCrypt.Language.Modules
open GaudisCrypt.Language.Modules.InductiveFunctions
open GaudisCrypt.Language.Programs

namespace FV

variable [ProgramSpec]

opaque FV : Type
-- Placeholder
axiom fv_proc {sig holes} (proc : ProcedureWithHoles holes sig) : FV
instance lattice_fv : CompleteLattice FV := sorry
axiom fv_zero : FV
axiom fv_join : FV → FV → FV



axiom fv_proc_instantiate {sig holes} (proc : ProcedureWithHoles holes sig) (args) :
  fv_proc (proc.instantiate args) ≤
    (fv_proc proc) ⊔ (Finset.univ.sup (fun i : HoleIndex holes sig => fv_proc (args i)))

noncomputable
def fvInductiveFunction : InductiveFunction FV where
  nothing := fv_zero
  proc (p : ProcedureWithHoles _ _) := fv_proc p
  join := fv_join

noncomputable
def fv' {ctx t} (m : ModuleExpression ctx t) : FV := fvInductiveFunction.evalMexpr m

noncomputable
def fv (m : Module t) : FV := fvInductiveFunction.eval m

scoped instance : Reducible fvInductiveFunction where
  comm := sorry
  assoc := sorry
  join_idem := sorry
  join_mono_left := sorry
  join_mono_right := sorry
  le_join_left := sorry
  le_join_right := sorry
  delta_bound := sorry

theorem fv_app (a : Module (.arr A B)) (b : Module A) :
    fv (.app a b) ≤ fv_join (fv a) (fv b) :=
    InductiveFunction.app _ _ _

theorem fv_pair (a : Module A) (b : Module B) :
    fv (.pair a b) = fv_join (fv a) (fv b) :=
    InductiveFunction.pair _ _ _

theorem fv_fst (a : Module (.prod A B)) :
    fv (.fst a) ≤ fv a :=
    InductiveFunction.fst _ _

theorem fv_snd (a : Module (.prod A B)) :
    fv (.snd a) ≤ fv a :=
    InductiveFunction.snd _ _

@[simp]
theorem fv_unit (a : Module .unit) : fv a = fv_zero :=
 InductiveFunction.unit _ _

end FV
