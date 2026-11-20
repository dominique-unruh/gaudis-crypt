import GaudisCrypt.Logic.ECLoop
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Syntax.Syntax

/-! Tests of `stmt_splitwhile` and `stmt_unroll` (`Logic/ECLoop.lean`). -/

namespace GaudisCrypt.ECLoopTest

open GaudisCrypt

/-- EC's `splitwhile{i} 2 : i < 3` on both sides: the loops in two, the same code again
(`sim`). -/
example : equiv[ ={i} ==> ={i} ] {
      var i : ℕ;
      i <- 0;
      while (decide (§i < 5)) { i <- §i + 1; }
    } ~ {
      var i : ℕ;
      i <- 0;
      while (decide (§i < 5)) { i <- §i + 1; }
    } := by
  stmt_splitwhile{1} 2 : §i < 3
  stmt_splitwhile{2} 2 : §i < 3
  sim

-- `splitwhile` on a loop that is not last: the two loops are two statements, the code after
-- them at EC's positions (statement 3 is the second loop's, 4 the assignment)
/--
trace: Q : ℕ → ℕ → Prop
⊢ hoare[ True ==> Q §i §j ] {
      var i : ℕ, j : ℕ;
      i <- 0;
      while (decide (§i < 5) && decide (§i < 3)) {
        i <- §i + 1;
      }
      while (decide (§i < 5)) {
        i <- §i + 1;
      }
      j <- §i;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (Q : ℕ → ℕ → Prop) : hoare[ True ==> Q §i §j ] {
      var i : ℕ, j : ℕ;
      i <- 0;
      while (decide (§i < 5)) { i <- §i + 1; }
      j <- §i;
    } := by
  stmt_splitwhile 2 : §i < 3
  trace_state
  sorry

/-- EC's `unroll{i} 2` on both sides: one round as a conditional, the same code again (`sim`
through the conditional and the loop in it). -/
example : equiv[ ={i} ==> ={i} ] {
      var i : ℕ;
      i <- 0;
      while (decide (§i < 5)) { i <- §i + 1; }
    } ~ {
      var i : ℕ;
      i <- 0;
      while (decide (§i < 5)) { i <- §i + 1; }
    } := by
  stmt_unroll{1} 2
  stmt_unroll{2} 2
  sim

/-- EC's `sim` through two loops: the equality set (`={j}` after them, and the loops' `i`, `j`)
as the invariant. -/
example : equiv[ ={i, j} ==> ={j} ] {
      var i : ℕ, j : ℕ;
      while (decide (§i < 5)) { i <- §i + 1; j <- §j + §i; }
    } ~ {
      var i : ℕ, j : ℕ;
      while (decide (§i < 5)) { i <- §i + 1; j <- §j + §i; }
    } := by
  sim

/-- EC's `sim` through two loops whose variables are named differently on the two sides (an
inlined callee's locals, `i0` against `i`): the variables at corresponding positions of the two
loops are paired, EC's equality set of pairs (`i0{1} = i{2}`). -/
example : equiv[ ={n} ==> ={s} ] {
      var i0 : ℕ, s : ℕ, n : ℕ;
      i0 <- 0;
      s <- 0;
      while (decide (§i0 < §n)) { s <- §s + §i0; i0 <- §i0 + 1; }
    } ~ {
      var i : ℕ, s : ℕ, n : ℕ;
      i <- 0;
      s <- 0;
      while (decide (§i < §n)) { s <- §s + §i; i <- §i + 1; }
    } := by
  sim

end GaudisCrypt.ECLoopTest
