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
  stmt_swap_raw 1 1
  stmt_swap_raw 2 -1
  hoare_wp 2
  hoare_skip
  simp

/-- `stmt_swap n k` counts EC's statements: the reset inlining leaves is not one, and moves with
the statement after it (`z <- 1` is EC's statement 1, the sampling statement 2). -/
example (F : Type) [Inhabited F] [Fintype F] :
    hoare[ True ==> §z = 1 ] {
      var y : F, z : ℕ;
      reset_vars {"w"};
      z <- 1;
      y <$ SubProbability.uniform;
    } := by
  stmt_swap 2 -1
  hoare_wp 3
  hoare_skip
  simp

/-- A clone's op given as a function (`op dout _ <- d`, an abbreviation): the sampling
`b <$ dout §x` does not read `x`, and moves past `x`'s assignment. -/
noncomputable abbrev dconst : ℕ → SubProbability Bool := fun _ => SubProbability.uniform

example : hoare[ True ==> §x = 1 ] {
      var x : ℕ, b : Bool;
      x <- 1;
      b <$ dconst §x;
    } := by
  stmt_swap 2 -1
  hoare_wp 2
  hoare_skip
  simp

/-- EC's `swap -k` past a statement preceded by a reset (inlining's) of the moved sampling's
variable: the reset goes first, the sampling after it (EC has no reset). -/
example : hoare[ True ==> §x = 1 ] {
      var x : ℕ, b : Bool;
      reset_vars {"x", "b"};
      x <- 1;
      b <$ dconst §x;
    } := by
  stmt_swap -1
  hoare_wp 3
  hoare_skip
  simp

/-- A tuple assignment split, and an assignment moved past a sampling it does not read. -/
example : hoare[ True ==> §x = 1 ∧ §y = 2 ] {
      var x : ℕ, y : ℕ, b : Bool;
      x, y <- (1, 2);
      b <$ SubProbability.uniform;
    } := by
  stmt_split_pair 0
  stmt_swap_raw 2 1
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
  stmt_swap_raw 1 2
  stmt_swap_raw 3 -1
  intro _ _
  simp only [not_true_eq_false]
  exact SubProbability.ofEvent_eq_zero_of_subset (F := ∅) (fun _ h => h)
    (by simp [SubProbability.ofEvent])

global_var swapTestFlag : Bool

/-- EC's `swap` of an abstract call past a deterministic `if` whose branch writes two globals
outside the callee (`Stmt.CommutesWith.call_ite`, `comp`): the condition reads a global the call
keeps; then back. -/
example (M : Init) (hM : FVP.fvP M ≤ (swapTestCount.footprint)ᶜ)
    (hM' : FVP.fvP M ≤ (swapTestFlag.footprint)ᶜ) :
    hoare[ True ==> True ] {
      call (Init.init M).procedure ();
      if (decide (§swapTestCount = 0)) {
        swapTestCount <- 1;
        swapTestFlag <- true;
      }
    } := by
  stmt_swap 1 1
  stmt_swap 2 -1
  intro _ _
  simp only [not_true_eq_false]
  exact SubProbability.ofEvent_eq_zero_of_subset (F := ∅) (fun _ h => h)
    (by simp [SubProbability.ofEvent])

/-- EC's `swap` of a call with a result past an assignment to a local reading a global the callee
keeps (`Stmt.CommutesWith.call_frame`; the local's write moved outward past the result's). -/
example (M : Init) (hM : FVP.fvP M ≤ (swapTestCount.footprint)ᶜ) :
    hoare[ True ==> True ] {
      var n : ℕ, r : Unit;
      r <- call (Init.init M).procedure ();
      n <- §swapTestCount + 1;
    } := by
  stmt_swap 1 1
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

/-- A deterministic `if` (a reset in its branch) moves before a conditional tuple assignment: the
writes of disjoint locals in normal form (`lensWriteNorm`) in each case of the conditions. -/
example : hoare[ True ==> True ] {
      var p : ℕ, v : ℕ, h : ℕ, b : Bool, c : Bool;
      if (§b) { p, v <- (1, 2); }
      if (§c) { reset_vars {"w"}; h <- 3; }
    } := by
  stmt_swap 2 -1
  intro _ _
  simp only [not_true_eq_false]
  exact SubProbability.ofEvent_eq_zero_of_subset (F := ∅) (fun _ h => h)
    (by simp [SubProbability.ofEvent])

/-- The same past a tuple assignment outside a conditional. -/
example : hoare[ True ==> True ] {
      var p : ℕ, v : ℕ, h : ℕ, c : Bool;
      p, v <- (1, 2);
      if (§c) { reset_vars {"w"}; h <- 3; }
    } := by
  stmt_swap 2 -1
  intro _ _
  simp only [not_true_eq_false]
  exact SubProbability.ofEvent_eq_zero_of_subset (F := ∅) (fun _ h => h)
    (by simp [SubProbability.ofEvent])

/-- Both conditionals with resets, the right one's prefix: the same variable reaches the side goal
both as `localVarLens n T` and unfolded (`(varLens ⟨n, T, …⟩).intoLocal`), which `lensWriteNorm`
takes for one lens (`ECSim.lensKey`). -/
example : hoare[ True ==> True ] {
      var p : ℕ, v : ℕ, x2 : ℕ, b : Bool, c : Bool, x1 : ℕ, y0 : ℕ;
      if (§b) { p, v <- (1, 2); reset_vars {"x2"} ∪ stringsStartingWith "@." \ {"@.x"};
        x2 <- §p + §v; }
      if (§c) { reset_vars {"x1", "y0"} ∪ stringsStartingWith "@@@." \ {"@@@.x", "@@@.y"};
        x1, y0 <- (§swapTestCount, 1); }
    } := by
  stmt_swap 2 -1
  intro _ _
  simp only [not_true_eq_false]
  exact SubProbability.ofEvent_eq_zero_of_subset (F := ∅) (fun _ h => h)
    (by simp [SubProbability.ofEvent])

/-- A reset of locals (in a conditional that samples, so it moves on its own) past a conditional
writing globals (`resetSetter_set_intoGlobal`). -/
example : hoare[ True ==> True ] {
      var x2 : ℕ, b : Bool, c : Bool, x1 : ℕ;
      if (§b) { reset_vars {"x2"} ∪ stringsStartingWith "@." \ {"@.x"}; x2 <- 3;
        b <$ SubProbability.uniform; } else { b <$ SubProbability.uniform; }
      if (!§c) { reset_vars {"x1"}; x1 <- §swapTestCount;
        swapTestCount <- §swapTestCount + §x1; }
    } := by
  stmt_swap 2 -1
  intro _ _
  simp only [not_true_eq_false]
  exact SubProbability.ofEvent_eq_zero_of_subset (F := ∅) (fun _ h => h)
    (by simp [SubProbability.ofEvent])

end GaudisCrypt.StmtSwapTest
