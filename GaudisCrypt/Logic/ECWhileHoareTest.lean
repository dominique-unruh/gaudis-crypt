import GaudisCrypt.Logic.ECWhileHoare
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Syntax.Syntax

/-! Tests of EC's `while I` on a Hoare triple (`hoare_while`, `Logic/ECWhileHoare.lean`). -/

namespace GaudisCrypt.ECWhileHoareTest

open GaudisCrypt

-- EC's two goals: `body`, then `hpre` (the code before, with the exit condition under the frame
-- of what the loop keeps: `n`).  (As shown: under `∀ τ`, the reads of the invariant and of the
-- guard are of `τ`, the state on exit, though they print as `§i`, `§n`.)
/--
trace: case body
P Q : ℤ → Prop
⊢ hoare[ (§i ≤ §n ∨ §n < 0) ∧ decide (§i < §n) = true ==> §i ≤ §n ∨ §n < 0 ] {
      var i : ℤ, n : ℤ;
      i <- §i + 1;
}

case hpre
P Q : ℤ → Prop
⊢ hoare[ P §n ==>
      let σ := CurrentState.state;
      (§i ≤ §n ∨ §n < 0) ∧
        ∀ (τ : ProgramState),
          n.get τ = n.get σ ∧ True → §i ≤ §n ∨ §n < 0 → decide (§i < §n) = false → Q (Evaluatable.eval τ i) ]
      {
      var n : ℤ, i : ℤ;
      i <- 0;
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
example (P Q : ℤ → Prop) : hoare[ P §n ==> Q §i ] {
      var i : ℤ, n : ℤ;
      i <- 0;
      while (decide ($i < $n)) { i <- $i + 1; }
    } := by
  hoare_while (§i ≤ §n ∨ §n < 0)
  trace_state
  all_goals sorry

/-- What the precondition says of `n`, which the loop does not modify, is there on exit: the
invariant does not carry it. -/
example (k : ℤ) : hoare[ §n = k ∧ 0 ≤ k ==> §i = k ] {
      var i : ℤ, n : ℤ;
      i <- 0;
      while (decide ($i < $n)) { i <- $i + 1; }
    } := by
  hoare_while (§i ≤ §n)
  · hoare_auto
  hoare_auto
  smt_close

/-- The loop is the whole code. -/
example (k : ℤ) : hoare[ §n = k ∧ §i ≤ §n ==> §i = k ] {
      var i : ℤ, n : ℤ;
      while (decide ($i < $n)) { i <- $i + 1; }
    } := by
  hoare_while (§i ≤ §n)
  · hoare_auto
  hoare_auto
  smt_close

end GaudisCrypt.ECWhileHoareTest
