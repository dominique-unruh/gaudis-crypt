import GaudisCrypt.Logic.GlobWrites
import GaudisCrypt.Syntax.Syntax

/-! Tests of `fp_writes` (`Logic/GlobWrites.lean`). -/

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

end GaudisCrypt.GlobWritesTest
