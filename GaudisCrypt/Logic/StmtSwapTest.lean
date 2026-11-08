import GaudisCrypt.Logic.StmtSwap
import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.ECSim

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

global_var swapTestCount : ℕ

moduletype Init {
  proc init () -> Unit;
}

/-- EasyCrypt's `swap` past an abstract call: an assignment to a global variable moves past a call
to a module `M` declared `{-swapTestCount}`, also through a functor `G` applied to it; the
disjointness comes from the restriction hypotheses (`fp_disjoint`). -/
example (M : Init) (G : Init →ₘ Init) (hM : FVP.fvP M ≤ (swapTestCount.footprint)ᶜ)
    (hG : FVP.fvP G ≤ (swapTestCount.footprint)ᶜ) :
    hoare[ True ==> True ] {
      swapTestCount <- 0;
      call (Init.init M).procedure ();
      call (Init.init (Module.app G M)).procedure ();
    } := by
  stmt_swap 0 2
  stmt_swap 2 -1
  intro _ _
  simp only [not_true_eq_false]
  exact SubProbability.ofEvent_eq_zero_of_subset (F := ∅) (fun _ h => h)
    (by simp [SubProbability.ofEvent])

/-- EC's `swap k` and `swap -k`: the first statement two later, then the last one back one; on
both sides of a relational judgment. -/
example : equiv[ True ==> ={x, y} ] {
      var x : ℕ, y : ℕ, b : Bool;
      x <- 1;
      b <$ SubProbability.uniform;
      y <- 2;
    } ~ {
      var x : ℕ, y : ℕ, b : Bool;
      x <- 1;
      b <$ SubProbability.uniform;
      y <- 2;
    } := by
  stmt_swap 2
  stmt_swap{1} -1
  stmt_swap{1} -1
  stmt_swap{2} -2
  sim

end GaudisCrypt.StmtSwapTest
