import GaudisCrypt.Logic.PHoareExactTactics
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Syntax.Syntax

/-!
# Golden tests of pHL on exact bounds (`Logic/PHoareExactTactics.lean`)

EC's `seq n : E p₁ p₂ p₃ p₄ I` with its `_`, `case`, and the forms of `conseq` on
`phoare[ c : P ==> Q ] = r` (see `Logic/ECAutoTest.lean` for the format;
`scripts/update_golden.py` refreshes the expected text).
-/

namespace GaudisCrypt.PHoareExactTest

open GaudisCrypt GaudisCrypt.EC

module Two {
  proc run () : Bool {
    var a : Bool, b : Bool;
    a <$ dbool;
    b <$ dbool;
    return $a && $b
  };
}

-- EC's `seq 1 : a (1/2) (1/2) _ 0 true`: the invariant, the first sampling reaches `a` with
-- probability `1/2`, from `a` the rest reaches the event with `1/2`, from `¬a` with `0` (the
-- probability of `¬a` is not asked), and the reals' equation
/--
trace: case invariant
⊢ hoare[ True ==> True ] {
      var a : Bool;
      a <$ dbool;
}

case first_E
⊢ phoare[ True ==> §a = true ] = (ENNReal.ofReal (1 / 2)) {
      var a : Bool;
      a <$ dbool;
}

case second_E
⊢ phoare[ §a = true ∧ True ==> (§a && §b) = true ] = (ENNReal.ofReal (1 / 2)) {
      var a : Bool, b : Bool;
      b <$ dbool;
}

case second_notE
⊢ phoare[ ¬§a = true ∧ True ==> (§a && §b) = true ] = 0 {
      var a : Bool, b : Bool;
      b <$ dbool;
}

case bound
⊢ 1 / 4 = 1 / 2 * (1 / 2)
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 5 goals and ends with 5 goals, 5 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : phoare[ Two.run : True ==> §res ] = (ENNReal.ofReal (1 / 4)) := by
  phoare_proc
  phoare_seq 1 : (§a) (1 / 2) (1 / 2) _ 0 (True)
  trace_state
  all_goals sorry

-- EC's `case (a)`
/--
trace: case pos
⊢ phoare[ (§a = true ∨ ¬§a = true) ∧ §a = true ==> §b = true ] = (ENNReal.ofReal (1 / 2)) {
      var a : Bool, b : Bool;
      b <$ dbool;
}

case neg
⊢ phoare[ (§a = true ∨ ¬§a = true) ∧ ¬§a = true ==> §b = true ] = (ENNReal.ofReal (1 / 2)) {
      var a : Bool, b : Bool;
      b <$ dbool;
}
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 2 goals and ends with 2 goals, 2 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : phoare[ §a ∨ ¬ §a ==> §b ] = (ENNReal.ofReal (1 / 2)) {
      var a : Bool, b : Bool;
      b <$ dbool;
    } := by
  phoare_case (§a)
  trace_state
  all_goals sorry

-- EC's `conseq (: _ ==> _ : = e)`: the bounds' equation over the reals, then the judgment
/--
trace: case bound
⊢ ∀ (a : Bool), a = true ∨ ¬a = true → 1 / 2 = if a = true then 1 / 2 else 2⁻¹

case judgment
⊢ phoare[ §a = true ∨ ¬§a = true ==> §b = true ] = (ENNReal.ofReal (if §a = true then 1 / 2 else 2⁻¹)) {
      var a : Bool, b : Bool;
      b <$ dbool;
}
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 2 goals and ends with 2 goals, 2 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : phoare[ §a ∨ ¬ §a ==> §b ] = (ENNReal.ofReal (1 / 2)) {
      var a : Bool, b : Bool;
      b <$ dbool;
    } := by
  phoare_conseq (: _ ==> _ : = (if §a then 1 / 2 else 2⁻¹))
  trace_state
  all_goals sorry

-- EC's `conseq (: P ==> _)` and `conseq (: _ ==> Q₁) (: _ ==> Q₂)`
/--
trace: case pre
⊢ ∀ (a1 : Bool), a1 = true → True ∨ a1 = true

case judgment
⊢ phoare[ True ∨ §a = true ==> §b = true ∧ §a = true ] = (ENNReal.ofReal (1 / 2)) {
      var a : Bool, b : Bool;
      b <$ dbool;
}
---
trace: case post
⊢ ∀ (a1 b : Bool), a1 = true → (b = true ↔ b = true ∧ a1 = true)

case hoare
⊢ hoare[ True ∨ §a = true ==> §a = true ] {
      var a : Bool, b : Bool;
      b <$ dbool;
}

case judgment
⊢ phoare[ True ∨ §a = true ==> §b = true ] = (ENNReal.ofReal (1 / 2)) {
      var a : Bool, b : Bool;
      b <$ dbool;
}
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 2 goals and ends with 2 goals, 2 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
---
warning: The following tactic starts with 3 goals and ends with 3 goals, 3 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : phoare[ §a ==> §b ∧ §a ] = (ENNReal.ofReal (1 / 2)) {
      var a : Bool, b : Bool;
      b <$ dbool;
    } := by
  phoare_conseq (: True ∨ §a ==> _)
  trace_state
  · exact fun _ _ => Or.inl trivial
  phoare_conseq (: _ ==> §b) (: _ ==> §a)
  trace_state
  all_goals sorry

-- EC's `conseq H`
/--
trace: case bound
w : Stmt
H :
  phoare[ True ==> §b = true ] = (ENNReal.ofReal (1 / 2)) {
      var b : Bool;
      stmt w;
}
⊢ ∀ (b : Bool), b = true → 2⁻¹ = 1 / 2
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (w : Stmt)
    (H : phoare[ True ==> §b ] = (ENNReal.ofReal (1 / 2)) { var b : Bool; stmt w; }) :
    phoare[ §b ==> §b ] = (ENNReal.ofReal (2⁻¹)) { var b : Bool; stmt w; } := by
  phoare_conseq H
  trace_state
  all_goals sorry

end GaudisCrypt.PHoareExactTest
