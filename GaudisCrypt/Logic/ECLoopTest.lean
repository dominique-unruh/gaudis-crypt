import GaudisCrypt.Logic.ECLoop
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Logic.ECWhileRel
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

module SimAdd {
  proc add (a : ℕ, b : ℕ) : ℕ {
    var c : ℕ;
    c <- $a + $b;
    return $c
  };
}

module SimSum {
  proc run (n : ℕ) : ℕ {
    var i : ℕ, s : ℕ;
    i <- 0;
    s <- 0;
    while (decide (§i < §n)) { s <- call SimAdd.add ($s, $i); i <- §i + 1; }
    return $s
  };
}

/-- The same through `inline*`: a callee with a loop whose body calls another procedure, inlined
under callers with different locals (on the left its `i` becomes `i0`, and the inner call's
temporaries are named differently on the two sides, in the frame resets of the bodies). -/
example : equiv[ ={n} ==> ={r} ] {
      var i : ℕ, c : ℕ, n : ℕ, r : ℕ;
      i <- 7;
      c <- 1;
      r <- call SimSum.run.procedure ($n);
    } ~ {
      var n : ℕ, r : ℕ;
      r <- call SimSum.run.procedure ($n);
    } := by
  stmt_inline*
  sim

/-- The pairs where a name means different variables on the two sides (`n0` the left's bound, the
right's temporary), after a tuple assignment and inside `if (true)` (what an inlined `IRO.f`
leaves); the temporaries the bodies write before reading them are not paired. -/
example : equiv[ ={q, k} ==> ={bs} ] {
      var q : List ℕ, k : ℕ, xn : List ℕ × ℕ, x2 : List ℕ, n0 : ℕ, i : ℕ, bs : List ℕ,
        x3 : List ℕ, n1 : ℕ;
      xn <- (§q, §k);
      x2, n0 <- §xn;
      i <- 0;
      bs <- [];
      if (true) {
        while (decide (§i < §n0)) {
          x3, n1 <- (§x2, §i);
          bs <- §bs ++ [§n1];
          i <- §i + 1;
        }
      }
    } ~ {
      var q : List ℕ, k : ℕ, xn : List ℕ × ℕ, x0 : List ℕ, n : ℕ, i : ℕ, bs : List ℕ,
        x1 : List ℕ, n0 : ℕ;
      xn <- (§q, §k);
      x0, n <- §xn;
      i <- 0;
      bs <- [];
      if (true) {
        while (decide (§i < §n)) {
          x1, n0 <- (§x0, §i);
          bs <- §bs ++ [§n0];
          i <- §i + 1;
        }
      }
    } := by
  sim

/-- `sim` in the goal's context: a relation that mentions a local the proof introduced (`c`, as
`intro F _` introduces a module) through a conditional on both sides. -/
example : ∀ c : ℕ, equiv[ ={b} ∧ §n{1} = c ==> ={s} ] {
      var b : Bool, n : ℕ, s : Bool;
      if (§b) { s <$ SubProbability.uniform; } else { s <- true; }
    } ~ {
      var b : Bool, n : ℕ, s : Bool;
      if (§b) { s <$ SubProbability.uniform; } else { s <- true; }
    } := by
  intro c
  sim

/-- The same with a sampling after the loops: the relation after them reads `∀ a ∈ d.support, …`;
the invariant is EC's equality set, the equalities that relation contains, not the relation. -/
example : equiv[ ={q, k} ==> ={bs, y} ] {
      var q : List ℕ, k : ℕ, xn : List ℕ × ℕ, x2 : List ℕ, n0 : ℕ, i : ℕ, bs : List ℕ,
        x3 : List ℕ, n1 : ℕ, y : Bool;
      xn <- (§q, §k);
      x2, n0 <- §xn;
      i <- 0;
      bs <- [];
      if (true) {
        while (decide (§i < §n0)) {
          x3, n1 <- (§x2, §i);
          bs <- §bs ++ [§n1];
          i <- §i + 1;
        }
      }
      y <$ SubProbability.uniform;
    } ~ {
      var q : List ℕ, k : ℕ, xn : List ℕ × ℕ, x0 : List ℕ, n : ℕ, i : ℕ, bs : List ℕ,
        x1 : List ℕ, n0 : ℕ, y : Bool;
      xn <- (§q, §k);
      x0, n <- §xn;
      i <- 0;
      bs <- [];
      if (true) {
        while (decide (§i < §n)) {
          x1, n0 <- (§x0, §i);
          bs <- §bs ++ [§n0];
          i <- §i + 1;
        }
      }
      y <$ SubProbability.uniform;
    } := by
  sim

-- EC's `sim` through two loops whose relation after them reads variables the loops keep,
-- differently named on the two sides (`x{1}` against `y{2}`, inside `f`): the equality set of
-- what the loops write as the invariant, EC's frame on exit (the framed loop rule of
-- `Logic/ECWhileRel.lean`, `ECSim.simWhileHook`)
example (f : List ℕ → ℕ → ℕ) : equiv[ ={i, s} ∧ §x{1} = §y{2} ==> f §s{1} §x{1} = f §s{2} §y{2} ] {
      var i : ℕ, s : List ℕ, x : ℕ;
      while (decide (§i < 5)) { s <- §i :: §s; i <- §i + 1; }
    } ~ {
      var i : ℕ, s : List ℕ, y : ℕ;
      while (decide (§i < 5)) { s <- §i :: §s; i <- §i + 1; }
    } := by
  sim

end GaudisCrypt.ECLoopTest
