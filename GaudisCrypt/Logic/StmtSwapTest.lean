import GaudisCrypt.Logic.StmtSwap
import GaudisCrypt.Syntax.Syntax

/-! Tests of `stmt_swap` and `stmt_split_pair` (`Logic/StmtSwap.lean`). -/

namespace GaudisCrypt.StmtSwapTest

open GaudisCrypt

/-- A sampling moves past a reset of other names, then the reset and the sampling swap back. -/
example (F : Type) [Inhabited F] [Fintype F] :
    hoare[ True ==> True ] {
      var y : F;
      y <$ SubProbability.uniform;
      reset_vars {"z"};
    } := by
  stmt_swap 0 1
  stmt_swap 1 -1
  hoare_wp 2
  hoare_skip
  simp

/-- A tuple assignment split, and an assignment moved past a sampling it does not read. -/
example : hoare[ True ==> §x = 1 ∧ §y = 2 ] {
      var x : ℕ, y : ℕ, b : Bool;
      x, y <- (1, 2);
      b <$ SubProbability.uniform;
    } := by
  stmt_split_pair 0
  stmt_swap 1 1
  hoare_wp 3
  hoare_skip
  simp

end GaudisCrypt.StmtSwapTest
