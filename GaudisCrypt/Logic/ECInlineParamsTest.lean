import GaudisCrypt.Logic.ECInlineParams
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Syntax.Syntax

/-!
# Golden tests of `stmt_split_params`

The code EC's `inline` leaves: one assignment per parameter of an inlined call, the result's
tuple assignment as it is (see `Logic/ECAutoTest.lean` for the format; `scripts/update_golden.py`
refreshes the expected text).
-/

namespace GaudisCrypt.ECInlineParamsTest

open GaudisCrypt

module M {
  proc add (x : ℕ, y : ℕ, z : ℕ) : (ℕ × ℕ) {
    var s : ℕ;
    s <- $x + $y;
    return ($s, $s + $z)
  };
  proc main (a : ℕ) : ℕ {
    var u : ℕ, v : ℕ;
    u, v <- call M.add ($a, $a + 1, 2);
    return $u + $v
  };
}

-- three parameters: three assignments; the result's pair stays one statement
/--
trace: ⊢ equiv[ §a{1} = §a{2} ==> §u{1} + §v{1} = §u{2} + §v{2} ] {
      var a : ℕ, x : ℕ, y : ℕ, z : ℕ, s : ℕ, u : ℕ, v : ℕ;
      reset_vars {"x", "y", "z", "s"} ∪ stringsStartingWith "@." \ {"@.x", "@.y", "@.z", "@.s"};
      x <- §a;
      y <- §a + 1;
      z <- 2;
      s <- §x + §y;
      u, v <- (§s, §s + §z);
} ~ {
      var a : ℕ, x : ℕ, y : ℕ, z : ℕ, s : ℕ, u : ℕ, v : ℕ;
      reset_vars {"x", "y", "z", "s"} ∪ stringsStartingWith "@." \ {"@.x", "@.y", "@.z", "@.s"};
      x <- §a;
      y <- §a + 1;
      z <- 2;
      s <- §x + §y;
      u, v <- (§s, §s + §z);
}
-/
#guard_msgs in
example : equiv[ M.main ~ M.main : ={a} ==> ={res} ] := by
  equiv_proc; stmt_inline*
  stmt_split_params
  trace_state
  sim

-- one side only
/--
trace: ⊢ equiv[ §a{1} = §a{2} ==> §u{1} + §v{1} = §u{2} + §v{2} ] {
      var a : ℕ, x : ℕ, y : ℕ, z : ℕ, s : ℕ, u : ℕ, v : ℕ;
      reset_vars {"x", "y", "z", "s"} ∪ stringsStartingWith "@." \ {"@.x", "@.y", "@.z", "@.s"};
      x <- §a;
      y <- §a + 1;
      z <- 2;
      s <- §x + §y;
      u, v <- (§s, §s + §z);
} ~ {
      var a : ℕ, x : ℕ, y : ℕ, z : ℕ, s : ℕ, u : ℕ, v : ℕ;
      reset_vars {"x", "y", "z", "s"} ∪ stringsStartingWith "@." \ {"@.x", "@.y", "@.z", "@.s"};
      x, y, z <- (§a, §a + 1, 2);
      s <- §x + §y;
      u, v <- (§s, §s + §z);
}
-/
#guard_msgs in
example : equiv[ M.main ~ M.main : ={a} ==> ={res} ] := by
  equiv_proc; stmt_inline*
  stmt_split_params{1}
  trace_state
  sim

end GaudisCrypt.ECInlineParamsTest
