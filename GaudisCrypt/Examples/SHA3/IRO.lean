import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Lib.EC.FMap
import GaudisCrypt.Lib.EC.FSet

/-!
# The infinite random oracle (EasyCrypt `proof/IRO.eca`)

It maps values of type `from` to infinite sequences of values of type `to`, each sampled
uniformly and independently; it is lazy.  Inputs not satisfying the validity predicate are mapped
to the empty list.

The abstract theory's types `to`, `from` and operators `valid`, `dto` are section variables, so a
`clone` is an application.  `to` and `from` are keywords, hence `«to»` and `«from»`.  EasyCrypt's
module type `IRO` and module `IRO` share a name; here the module type is `IRO_T` (exception E3 of
the port).
-/

namespace GaudisCrypt.SHA3.IRO

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet

variable («to» «from» : Type) [DecidableEq «from»] [Inhabited «to»] [Inhabited «from»]

-- EC's `module type IRO` (renamed: exception E3)
moduletype IRO_T {
  proc init () -> Unit;
  -- `f x`, returning the first `n` elements of the result
  proc f (x : «from», n : ℤ) -> (List «to»);
}

def prefix_closed (m : FMap («from» × ℤ) «to») : Prop :=
  ∀ x n, FMap.dom m (x, n) → ∀ i, 0 ≤ i ∧ i < n → FMap.dom m (x, i)

def prefix_closed' (m : FMap («from» × ℤ) «to») : Prop :=
  ∀ x n i, FMap.dom m (x, n) → 0 ≤ i ∧ i < n → FMap.dom m (x, i)

theorem prefix_closed_equiv (m : FMap («from» × ℤ) «to») :
    prefix_closed «to» «from» m ↔ prefix_closed' «to» «from» m := by
  sorry

section
variable {«to» «from»}
/-- EC's `IRO.mp`. -/
global_var IRO.mp : FMap («from» × ℤ) «to»
/-- EC's `IRO'.mp`. -/
global_var IRO'.mp : FMap («from» × ℤ) «to»
/-- EC's `IRO'.visible`. -/
global_var IRO'.visible : FSet («from» × ℤ)
end

variable (valid : «from» → Bool) (dto : SubProbability «to»)

-- The official version (EC: `module IRO : IRO`; it has more procedures than `IRO_T`, so no type
-- annotation here: see `notes/SHA3/README.md`, "Modules").
module IRO {
  proc init () : Unit {
    IRO.mp <- (FMap.empty : FMap («from» × ℤ) «to»);
    return ()
  };
  proc fill_in (x : «from», n : ℤ) : «to» {
    var r : «to»;
    if (!(decide (FMap.dom ($IRO.mp : FMap («from» × ℤ) «to») ($x, $n)))) {
      r <$ dto;
      IRO.mp <- FMap.set $IRO.mp ($x, $n) $r;
    }
    return oget (FMap.get $IRO.mp ($x, $n))
  };
  proc f (x : «from», n : ℤ) : (List «to») {
    var b : «to», bs : List «to», i : ℤ;
    i <- 0;
    bs <- [];
    if (valid $x) {
      while ($i < $n) {
        b <- call (IRO.fill_in «to» «from» valid dto) ($x, $i);
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
    }
    return $bs
  };
}

-- The version for the `AbsorbToBlocks.ec` attempt (EC: `module IRO' : IRO`).
module IRO' {
  proc resample_invisible () : Unit {
    var work : FSet («from» × ℤ), x : «from» × ℤ, r : «to»;
    work <- FMap.fdom ($IRO'.mp : FMap («from» × ℤ) «to») \ $IRO'.visible;
    while ($work != fset0) {
      x <- pick $work;
      r <$ dto;
      IRO'.mp <- FMap.set $IRO'.mp $x $r;
      work <- $work \ fset1 $x;
    }
    return ()
  };
  proc init () : Unit {
    IRO'.mp <- (FMap.empty : FMap («from» × ℤ) «to»);
    IRO'.visible <- (fset0 : FSet («from» × ℤ));
    return ()
  };
  proc fill_in (x : «from», n : ℤ) : «to» {
    var r : «to»;
    if (!(decide (FMap.dom ($IRO'.mp : FMap («from» × ℤ) «to») ($x, $n)))) {
      r <$ dto;
      IRO'.mp <- FMap.set $IRO'.mp ($x, $n) $r;
    }
    return oget (FMap.get $IRO'.mp ($x, $n))
  };
  proc f (x : «from», n : ℤ) : (List «to») {
    var b : «to», bs : List «to», i : ℤ;
    i <- 0;
    bs <- [];
    if (valid $x) {
      IRO'.visible <- $IRO'.visible ∪ fset1 ($x, $n);
      while ($i < $n) {
        b <- call (IRO'.fill_in «to» «from» valid dto) ($x, $i);
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
    }
    return $bs
  };
  proc f_lazy (x : «from», i : ℤ) : «to» {
    var b : «to»;
    b <- default;
    if (valid $x && decide (0 ≤ $i)) {
      IRO'.visible <- $IRO'.visible ∪ fset1 ($x, $i);
      b <- call (IRO'.fill_in «to» «from» valid dto) ($x, $i);
    }
    return $b
  };
}

end GaudisCrypt.SHA3.IRO
