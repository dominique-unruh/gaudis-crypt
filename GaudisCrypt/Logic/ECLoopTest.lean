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
  equiv_while (={i})
  all_goals try (equiv_while (={i}))
  all_goals first | sim | auto_close

/-- EC's `unroll{i} 2` on both sides: one round as a conditional, the same code again. -/
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
  stmt_sp; equiv_if
  all_goals try (equiv_while (={i}))
  all_goals try sim
  all_goals auto_close

end GaudisCrypt.ECLoopTest
