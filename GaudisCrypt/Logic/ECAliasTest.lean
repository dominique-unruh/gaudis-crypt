import GaudisCrypt.Logic.ECAlias
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Syntax.Syntax

/-! Tests of `stmt_alias` (`Logic/ECAlias.lean`). -/

namespace GaudisCrypt.ECAliasTest

open GaudisCrypt

/-- EC's `alias{1} 2 x0 = x`: the value of `x` before the update, for the postcondition of the
code after it. -/
example : equiv[ ={x} ==> §x{1} = §x{2} + 1 ] {
      var x : ℕ;
      x <- §x + 1;
    } ~ {
      var x : ℕ;
      x <- §x;
    } := by
  stmt_alias{1} 1 x0 = §x
  equiv_auto

/-- At the end, and on the right. -/
example : equiv[ ={x} ==> ={x} ] {
      var x : ℕ;
      x <- §x + 1;
    } ~ {
      var x : ℕ;
      x <- §x + 1;
    } := by
  stmt_alias{2} 2 y = §x
  equiv_auto

/-- Before a loop (the loop does not touch the alias: `Stmt.CommutesWith.while`). -/
example : equiv[ ={i} ==> ={i} ] {
      var i : ℕ;
      while (decide (§i < 5)) { i <- §i + 1; }
    } ~ {
      var i : ℕ;
      while (decide (§i < 5)) { i <- §i + 1; }
    } := by
  stmt_alias{1} 1 i0 = §i
  stmt_sp{1} 1
  sim

end GaudisCrypt.ECAliasTest
