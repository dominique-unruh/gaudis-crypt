import GaudisCrypt.Logic.ECTransProc
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.Distr

/-!
# Golden tests of `transitivity` on procedures (`Logic/ECTransProc.lean`)

EC's `transitivity N.f (P₁ ==> Q₁) (P₂ ==> Q₂)` (see `Logic/ECAutoTest.lean` for the format;
`scripts/update_golden.py` refreshes the expected text).
-/

namespace GaudisCrypt.ECTransProcTest

open GaudisCrypt GaudisCrypt.EC

module A {
  proc f () : Bool {
    var b : Bool;
    b <$ dbool;
    return $b
  };
}

module B {
  proc f (x : Bool) : Bool {
    var b : Bool;
    b <$ dbool;
    return $b && $x
  };
}

-- the side conditions are closed (a precondition `true`, equalities that compose): the two
-- judgments through the middle procedure
/--
trace: case h₁
⊢ equiv[ A.f ~ A.f : True ==> ={res} ]

case h₂
⊢ equiv[ A.f ~ A.f : True ==> ={res} ]
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 2 goals and ends with 2 goals, 2 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : equiv[ A.f ~ A.f : True ==> ={res} ] := by
  equiv_trans (A.f) (True ==> ={res}) (True ==> ={res})
  trace_state
  all_goals sorry

-- a middle procedure with a parameter and a precondition on it: `hP` asks for its argument
-- and memory
/--
trace: case hP
⊢ ∀ (a₁ : (procsig () → Bool).ParamType) (g₁ : VariableAssignment) (a₂ : (procsig () → Bool).ParamType)
    (g₂ : VariableAssignment),
    (let params_1 := GaudiExpr[ a₁ ];
      let params_2 := GaudiExpr[ a₂ ];
      True) →
      ∃ a g,
        (let params_1 := GaudiExpr[ a₁ ];
          let params_2 := GaudiExpr[ a ];
          let x_2 := GaudiExpr[ Lens.id.get a ];
          §x_2 = true) ∧
          let params_1 := GaudiExpr[ a ];
          let x_1 := GaudiExpr[ Lens.id.get a ];
          let params_2 := GaudiExpr[ a₂ ];
          §x_1 = true

case h₁
⊢ equiv[ A.f ~ B.f (x) : §x{2} = true ==> ={res} ]

case h₂
⊢ equiv[ B.f (x) ~ A.f : §x{1} = true ==> ={res} ]
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 3 goals and ends with 3 goals, 3 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : equiv[ A.f ~ A.f : True ==> ={res} ] := by
  equiv_trans (B.f) (§x{2} = true ==> ={res}) (§x{1} = true ==> ={res})
  trace_state
  all_goals sorry

end GaudisCrypt.ECTransProcTest
