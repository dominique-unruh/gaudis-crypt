import GaudisCrypt.Logic.GlobWrites
import GaudisCrypt.Logic.ECCallUpto
import GaudisCrypt.Syntax.Syntax

/-! Tests of `fp_writes` (`Logic/GlobWrites.lean`), and of `glob_simp`'s guard
(`Logic/ECCallUpto.lean`). -/

namespace GaudisCrypt.GlobWritesTest

open GaudisCrypt

global_var gwCount : ℕ
global_var gwMap : ℕ → Bool
global_var gwRead : ℕ

moduletype Two {
  proc init () -> Unit;
  proc f (x : ℕ) -> Bool;
}

module Fill {
  proc fill (x : ℕ) : Bool {
    var r : Bool;
    r <$ SubProbability.uniform;
    gwMap <- Function.update $gwMap $x $r;
    return $r
  };
}

-- `init` writes `gwCount`; `f` writes `gwMap` through its callee `fill` only, and reads
-- `gwRead`.
module M : Two {
  proc init () : Unit {
    gwCount <- 0;
    return ()
  };
  proc f (x : ℕ) : Bool {
    var y : Bool;
    if ($x < $gwRead) {
      y <- call Fill.fill ($x);
    }
    return $y
  };
}

/-- A direct write in one procedure. -/
example : (FVP.fvP M).HasWrites gwCount := by fp_writes

/-- A write in a callee's body. -/
example : (FVP.fvP M).HasWrites gwMap := by fp_writes

/-- A variable only read is not written. -/
example : True := by
  fail_if_success have : (FVP.fvP M).HasWrites gwRead := by fp_writes
  trivial

/-- EC's `={glob M}` gives back `={gwCount}`. -/
example (σ σ' : VariableAssignment)
    (h : (FVP.fvP M).touched_getter.get σ = (FVP.fvP M).touched_getter.get σ') :
    gwCount.get σ = gwCount.get σ' :=
  gwCount.get_eq_of_touched_getter_eq_of_hasWrites (by fp_writes) h

-- `M2` touches only what it writes: `gwCount` and, through `fill`, `gwMap`.
module M2 : Two {
  proc init () : Unit {
    gwCount <- 0;
    return ()
  };
  proc f (x : ℕ) : Bool {
    var y : Bool;
    y <- call Fill.fill ($x);
    return $y
  };
}

/-- EC's `={glob M2}` is `={gwCount, gwMap}`, both ways. -/
example (σ σ' : VariableAssignment) :
    ((FVP.fvP M2).touched_getter.get σ = (FVP.fvP M2).touched_getter.get σ') ↔
      (gwCount.get σ = gwCount.get σ' ∧ gwMap.get σ = gwMap.get σ') := by
  glob_tuples
  exact Iff.rfl

/-- `M` also reads `gwRead`: its region is not its writes', left as it is. -/
example (σ σ' : VariableAssignment)
    (h : (FVP.fvP M).touched_getter.get σ = (FVP.fvP M).touched_getter.get σ') :
    (FVP.fvP M).touched_getter.get σ = (FVP.fvP M).touched_getter.get σ' := by
  glob_tuples
  exact h

/-! ### `glob_simp` and its guard `glob_set_present` -/

global_var gwOther : ℕ

-- a write outside `glob M` removed (the guard only checks: no change to the goal)
set_option linter.unusedTactic false in
#guard_msgs in
example (v : ℕ) (g : VariableAssignment) :
    (FVP.fvP M).touched_getter.get (gwOther.set v g) = (FVP.fvP M).touched_getter.get g := by
  glob_set_present
  glob_simp

-- no write under a getter: the guard fails
#guard_msgs in
example (g : VariableAssignment) :
    (FVP.fvP M).touched_getter.get g = (FVP.fvP M).touched_getter.get g := by
  fail_if_success glob_set_present
  rfl

/-! ### A bound `fp_module` cannot prove is no bound

`Wrap(M)`, a functor applied to a concrete module, is bounded by `FVP.fvP M`; `fp_module`, meeting
`M`'s variables in the code, cannot show it.  The footprint read off the code is then none (not a
`sorry`, cached, with an error logged in the caller's proof), and `fp_disjoint` fails. -/

set_option linter.gaudisCrypt.using false in
module Wrap (P : Two) {
  proc g (x : ℕ) : Bool {
    var r : Bool;
    r <- call P.f ($x);
    return $r
  };
}

#guard_msgs in
example : True := by
  fail_if_success have : FVP.fvP (Wrap M) ≤ (gwOther.footprint)ᶜ := by fp_disjoint
  trivial

/-! ### A module of procedure aliases

`proc f = c;` makes `f` the procedure `c`: `Al`'s procedures are `M.init` and `Fill.fill`, with no
`.procedure` of their own.  The footprint is read off them all the same. -/

module Al : Two {
  proc init = M.init;
  proc f = Fill.fill;
}

/-- A write in an aliased procedure. -/
example : (FVP.fvP Al).HasWrites gwCount := by fp_writes

/-- The bound read off the code, through the aliases. -/
example : FVP.fvP Al ≤ (gwOther.footprint)ᶜ := by fp_disjoint

/-! A concrete module met twice inside another (`M` in both aliases of `AlM`): `fp_module` bounds
it by its own bound (read off its code once, cached) instead of reading its code at each
occurrence. -/

module AlM : Two {
  proc init = M.init;
  proc f = M.f;
}

example : FVP.fvP AlM ≤ (gwOther.footprint)ᶜ := by fp_disjoint
example : (FVP.fvP AlM).HasWrites gwCount := by fp_writes

end GaudisCrypt.GlobWritesTest
