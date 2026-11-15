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

end GaudisCrypt.SHA3.IRO
