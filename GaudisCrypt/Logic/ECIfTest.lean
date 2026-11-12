import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Syntax.Syntax

/-! Tests of `stmt_if` (`Logic/ECIf.lean`). -/

namespace GaudisCrypt.ECIfTest

open GaudisCrypt

/-- EC's `if` on a first statement followed by more code; each branch by wp. -/
example : hoare[ True ==> §y = 1 ] {
      var b : Bool, y : ℕ;
      if ($b) {
        y <- 0;
      } else {
        y <- 2;
      }
      y <- 1;
    } := by
  stmt_if
  · hoare_wp 2
    hoare_skip
    simp
  · hoare_wp 2
    hoare_skip
    simp

/-- EC's `if` on both sides, the tests equal by the precondition; the branches by `sim`. -/
example : equiv[ ={b} ==> ={y} ] {
      var b : Bool, y : ℕ;
      if ($b) {
        y <- 0;
      } else {
        y <- 2;
      }
      y <- §y + 1;
    } ~ {
      var b : Bool, y : ℕ;
      if ($b) {
        y <- 0;
      } else {
        y <- 2;
      }
      y <- §y + 1;
    } := by
  stmt_if
  · intros; simp_all
  · sim
  · sim

/-- EC's `rcondt 2`: the test holds after `b <- true`; the conditional is its `then` branch. -/
example : hoare[ True ==> §y = 0 ] {
      var b : Bool, y : ℕ;
      b <- true;
      if ($b) {
        y <- 0;
      } else {
        y <- 2;
      }
    } := by
  stmt_rcondt 2
  · hoare_wp 1
    hoare_skip
    simp
  · hoare_wp 3
    hoare_skip
    simp

/-- EC's `rcondf{1} 1` on one side: the precondition makes the test false. -/
example : equiv[ §b{1} = false ==> ={y} ] {
      var b : Bool, y : ℕ;
      if ($b) {
        y <- 0;
      } else {
        y <- 2;
      }
    } ~ {
      var y : ℕ;
      y <- 2;
    } := by
  stmt_rcondf{1} 1
  · intro _
    apply hoare_skip_of_imp
    simp_all
  · sim

/-- EC's `rcondt{1} 2` on a loop: its body comes before it; then `rcondf{1} 4` on the loop
again, which is no longer entered: it is gone. -/
example : equiv[ True ==> ={y} ] {
      var i : ℕ, y : ℕ;
      i <- 0;
      while (decide ($i < 1)) {
        i <- $i + 1;
      }
      y <- 2;
    } ~ {
      var y : ℕ;
      y <- 2;
    } := by
  stmt_rcondt{1} 2
  · intro _
    hoare_wp 1
    hoare_skip
    simp
  stmt_rcondf{1} 3
  · intro _
    hoare_wp 2
    hoare_skip
    simp
  sim

end GaudisCrypt.ECIfTest
