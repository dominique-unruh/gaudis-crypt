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
the port).  The module variables (`IRO.mp` …) are parameters: a clone declares its own.
-/

-- EasyCrypt names a module after its theory (`RP.RP`, `IRO.IRO`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.IRO

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet

variable («to» «from» : Type) [DecidableEq «from»] [Inhabited «to»] [Inhabited «from»]

-- EC's `module type IRO` (renamed: exception E3)
moduletype IRO_T {
  proc init () -> Unit;
  -- `f x`, returning the first `n` elements of the result (EC's parameters `(x, n)` as one pair,
  -- the type `FUNCTIONALITY.f` has where the oracle is a functionality)
  proc f (xn : «from» × ℤ) -> (List «to»);
}

def prefix_closed (m : FMap («from» × ℤ) «to») : Prop :=
  ∀ x n, FMap.dom m (x, n) → ∀ i, 0 ≤ i ∧ i < n → FMap.dom m (x, i)

def prefix_closed' (m : FMap («from» × ℤ) «to») : Prop :=
  ∀ x n i, FMap.dom m (x, n) → 0 ≤ i ∧ i < n → FMap.dom m (x, i)

omit [DecidableEq «from»] [Inhabited «to»] [Inhabited «from»] in
theorem prefix_closed_equiv (m : FMap («from» × ℤ) «to») :
    prefix_closed «to» «from» m ↔ prefix_closed' «to» «from» m :=
  ⟨fun h x n i hd hi => h x n hd i hi, fun h x n hd i hi => h x n i hd hi⟩

variable (valid : «from» → Bool) (dto : SubProbability «to»)

section IRO
/-! `IRO`'s module variable `mp` is a parameter: a clone declares its own (`BIRO.IRO.mp`) and
passes it. -/
variable (mp : Lens (FMap («from» × ℤ) «to») VariableAssignment)

-- The official version (EC: `module IRO : IRO`; it has more procedures than `IRO_T`, so no type
-- annotation here: see `notes/SHA3/README.md`, "Modules").
module IRO {
  proc init () : Unit {
    mp <- (FMap.empty : FMap («from» × ℤ) «to»);
    return ()
  };
  proc fill_in (x : «from», n : ℤ) : «to» {
    var r : «to»;
    if (!(decide (FMap.dom ($mp : FMap («from» × ℤ) «to») ($x, $n)))) {
      r <$ dto;
      mp <- FMap.set $mp ($x, $n) $r;
    }
    return oget (FMap.get $mp ($x, $n))
  };
  proc f (xn : «from» × ℤ) : (List «to») {
    var x : «from», n : ℤ, b : «to», bs : List «to», i : ℤ;
    x, n <- $xn;
    i <- 0;
    bs <- [];
    if (valid $x) {
      while ($i < $n) {
        b <- call (IRO.fill_in «to» «from» valid dto mp) ($x, $i);
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
    }
    return $bs
  };
}

end IRO

section IRO'
/-! `IRO'`'s module variables `mp`, `visible` are parameters (see `IRO`). -/
variable (mp : Lens (FMap («from» × ℤ) «to») VariableAssignment)
  (visible : Lens (FSet («from» × ℤ)) VariableAssignment)

-- The version for the `AbsorbToBlocks.ec` attempt (EC: `module IRO' : IRO`).
module IRO' {
  proc resample_invisible () : Unit {
    var work : FSet («from» × ℤ), x : «from» × ℤ, r : «to»;
    work <- FMap.fdom ($mp : FMap («from» × ℤ) «to») \ $visible;
    while ($work != fset0) {
      x <- pick $work;
      r <$ dto;
      mp <- FMap.set $mp $x $r;
      work <- $work \ fset1 $x;
    }
    return ()
  };
  proc init () : Unit {
    mp <- (FMap.empty : FMap («from» × ℤ) «to»);
    visible <- (fset0 : FSet («from» × ℤ));
    return ()
  };
  proc fill_in (x : «from», n : ℤ) : «to» {
    var r : «to»;
    if (!(decide (FMap.dom ($mp : FMap («from» × ℤ) «to») ($x, $n)))) {
      r <$ dto;
      mp <- FMap.set $mp ($x, $n) $r;
    }
    return oget (FMap.get $mp ($x, $n))
  };
  proc f (xn : «from» × ℤ) : (List «to») {
    var x : «from», n : ℤ, b : «to», bs : List «to», i : ℤ;
    x, n <- $xn;
    i <- 0;
    bs <- [];
    if (valid $x) {
      visible <- $visible ∪ fset1 ($x, $n);
      while ($i < $n) {
        b <- call (IRO'.fill_in «to» «from» valid dto mp visible) ($x, $i);
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
      visible <- $visible ∪ fset1 ($x, $i);
      b <- call (IRO'.fill_in «to» «from» valid dto mp visible) ($x, $i);
    }
    return $b
  };
}

end IRO'

end GaudisCrypt.SHA3.IRO
