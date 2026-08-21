import GaudisCrypt.Language.Modules

/-! # Tests for `Modules` -/

namespace GaudisCrypt

variable [ProgramSpec]

/- # Demo -/



section Demo

axiom sig : ProcedureSignature
def TestModule := Module (ModuleTypeRep.prod (ModuleTypeRep.proc sig) (ModuleTypeRep.proc sig))

noncomputable
def TestModule.main (m : TestModule) : Module (ModuleTypeRep.proc sig) := m.fst'
noncomputable
def TestModule.aux (m : TestModule) : Module (ModuleTypeRep.proc sig) := m.snd'

structure TestModuleStruct where
  main : Module (ModuleTypeRep.proc sig)
  aux : Module (ModuleTypeRep.proc sig)

noncomputable
def TestModuleStruct.destruct (str : TestModuleStruct) : TestModule :=
  str.main.pair' str.aux

noncomputable
def TestModule.mk (str : TestModuleStruct) : TestModule := str.main.pair' str.aux

axiom testMain : Module (ModuleTypeRep.proc sig)
axiom testAux : Module (ModuleTypeRep.proc sig)

noncomputable
def myMod := TestModule.mk {main := testMain, aux := testAux}

theorem test : myMod.main = testMain := by
  simp [TestModule.main, myMod, TestModule.mk]


end Demo


end GaudisCrypt
