import GaudisCrypt.Logic.ECWhileRel
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.ECProgress
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

/-- EC's one-sided `while{2} I V`: `z` is read only by the invariant, and the exit needs it as it
was before the loop (`z = x`): EC's frame keeps what the loop does not write, the invariant's
variables among them. -/
example : equiv[ ={x} ==> §w{2} = §x{1} ] {
      var x : ℕ;
      skip;
    } ~ {
      var x : ℕ, z : ℕ, i : ℕ, w : ℕ;
      z <- §x;
      i <- 0;
      w <- §z;
      while (decide (§i < 3)) {
        w <- §z;
        i <- §i + 1;
      }
    } := by
  equiv_while{2} (§w{2} = §z{2} ∧ §i{2} ≤ 3) (3 - §i{2})
  · while_ll_phoare
    intro σ₁
    ec_auto
  · intro σ₁ k
    hoare_auto
    ec_close
  · equiv_auto

end GaudisCrypt.ECWhileRelTest
