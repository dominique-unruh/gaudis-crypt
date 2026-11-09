import GaudisCrypt.Logic.ECWhileRel
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Syntax.Syntax

/-! Tests of EC's two-sided `while I` (`Logic/ECWhileRel.lean`). -/

namespace GaudisCrypt.ECWhileRelTest

open GaudisCrypt

/-- The postcondition reads `k`, which the loops do not modify and the invariant does not
mention: EC's frame keeps it from before the loops. -/
example : equiv[ ={n, k} ==> ={i, k} ] {
      var i : ℕ, n : ℕ, k : ℕ;
      i <- 0;
      while (decide (§i < §n)) {
        i <- §i + 1;
      }
    } ~ {
      var i : ℕ, n : ℕ, k : ℕ;
      i <- 0;
      while (decide (§i < §n)) {
        i <- §i + 1;
      }
    } := by
  equiv_while (={i, n})
  · equiv_auto
  · equiv_auto

end GaudisCrypt.ECWhileRelTest
