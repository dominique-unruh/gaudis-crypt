import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.ModuleVar
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Lib.EC.FMap
import GaudisCrypt.Lib.EC.FSet

/-!
# The infinite random oracle (EasyCrypt `proof/IRO.eca`) — EC-fidelity port

It maps values of type `from` to infinite sequences of values of type `to`, each sampled
uniformly and independently; it is lazy.  Inputs not satisfying the validity predicate are mapped
to the empty list.

Translation (as the pilot `SecureRO`'s):
* the theory's operators are the class `Params to from`, whose types are `outParam`s (a clone is
  an instance), so `valid`, `dto` are written without types, as in EC;
* the module variables `IRO.mp`, `IRO'.mp`, `IRO'.visible` are `module_var`s;
* EC's module type `IRO` and module `IRO` share a name: the module type is `IRO_T` (exception E3);
* `f`'s parameters `(x, n)` are one pair, the type a functionality's `f` has where `IRO` is one
  (`BlockSponge`'s `f_in <- block list * int`), which EC identifies with two parameters;
* `module IRO : IRO`'s annotation is left out: `IRO` has more procedures (`fill_in`) than `IRO_T`.
-/

-- EasyCrypt names a module after its theory (`IRO.IRO`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.Pilot.IRO

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet

/-- EC's `type to, from.`, `op valid`, `op dto`.  The types are `outParam`s: a clone of the
theory is an instance. -/
class Params («to» «from» : outParam Type) where
  valid : «from» → Bool
  dto : SubProbability «to»

export Params (valid dto)

variable {«to» «from» : Type} [DecidableEq «from»] [Inhabited «to»] [Inhabited «from»]

moduletype IRO_T {
  proc init () -> Unit;
  -- `f x`, returning the first `n` elements of the result
  proc f (xn : «from» × ℤ) -> (List «to»);
}

def prefix_closed (m : FMap («from» × ℤ) «to») : Prop :=
  ∀ x n, FMap.dom m (x, n) → ∀ i, 0 ≤ i ∧ i < n → FMap.dom m (x, i)

def prefix_closed' (m : FMap («from» × ℤ) «to») : Prop :=
  ∀ x n i, FMap.dom m (x, n) → 0 ≤ i ∧ i < n → FMap.dom m (x, i)

omit [DecidableEq «from»] [Inhabited «to»] [Inhabited «from»] in
/-- EC's `prefix_closed_equiv m` (`smt()`). -/
theorem prefix_closed_equiv (m : FMap («from» × ℤ) «to») : prefix_closed m ↔ prefix_closed' m := by
  unfold prefix_closed prefix_closed'; grind

variable [Params «to» «from»]

/-! ### The official version -/

module_var IRO.mp : FMap («from» × ℤ) «to»

module IRO {
  proc init () : Unit {
    IRO.mp <- FMap.empty;
    return ()
  };
  proc fill_in (x : «from», n : ℤ) : «to» {
    var r : «to»;
    if (!(decide (FMap.dom $IRO.mp ($x, $n)))) {
      r <$ dto;
      IRO.mp <- FMap.set $IRO.mp ($x, $n) $r;
    }
    return oget (FMap.get $IRO.mp ($x, $n))
  };
  proc f (xn : «from» × ℤ) : (List «to») {
    var x : «from», n : ℤ, b : «to», bs : List «to», i : ℤ;
    x, n <- $xn;
    i <- 0;
    bs <- [];
    if (valid $x) {
      while ($i < $n) {
        b <- call IRO.fill_in ($x, $i);
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
    }
    return $bs
  };
}

/-! ### The version for the `AbsorbToBlocks.ec` attempt -/

module_var IRO'.mp : FMap («from» × ℤ) «to»

module_var IRO'.visible : FSet («from» × ℤ)

module IRO' {
  proc resample_invisible () : Unit {
    var work : FSet («from» × ℤ), x : «from» × ℤ, r : «to»;
    work <- FMap.fdom $IRO'.mp \ $IRO'.visible;
    while ($work != fset0) {
      x <- pick $work;
      r <$ dto;
      IRO'.mp <- FMap.set $IRO'.mp $x $r;
      work <- $work \ fset1 $x;
    }
    return ()
  };
  proc init () : Unit {
    IRO'.mp <- FMap.empty;
    IRO'.visible <- fset0;
    return ()
  };
  proc fill_in (x : «from», n : ℤ) : «to» {
    var r : «to»;
    if (!(decide (FMap.dom $IRO'.mp ($x, $n)))) {
      r <$ dto;
      IRO'.mp <- FMap.set $IRO'.mp ($x, $n) $r;
    }
    return oget (FMap.get $IRO'.mp ($x, $n))
  };
  proc f (xn : «from» × ℤ) : (List «to») {
    var x : «from», n : ℤ, b : «to», bs : List «to», i : ℤ;
    x, n <- $xn;
    i <- 0;
    bs <- [];
    if (valid $x) {
      IRO'.visible <- $IRO'.visible ∪ fset1 ($x, $n);
      while ($i < $n) {
        b <- call IRO'.fill_in ($x, $i);
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
      b <- call IRO'.fill_in ($x, $i);
    }
    return $b
  };
}

end GaudisCrypt.SHA3.Pilot.IRO
