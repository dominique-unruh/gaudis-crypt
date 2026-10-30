import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Lib.EC.FMap
import GaudisCrypt.Lib.EC.Distr

/-!
# EasyCrypt's pseudo-random permutations (`theories/crypto/PRP.eca`)

The abstract type `D` and the operator `dD` are Lean parameters, so EasyCrypt's
`clone PRP with type D <- …` and `clone RP with op dD <- …` are applications.  The sub-theories
`StrongPRP` and `RP` are namespaces.  Only what ported developments use is here (`WeakPRP` is not).
-/

namespace GaudisCrypt.EC.PRP

open GaudisCrypt GaudisCrypt.EC

variable (D : Type) [DecidableEq D] [Inhabited D]

namespace StrongPRP

-- EC's `StrongPRP.PRP`
moduletype PRP {
  proc init () -> Unit;
  proc f (x : D) -> D;
  proc fi (x : D) -> D;
}

-- EC's `StrongPRP.SPRP_Oracles`
moduletype SPRP_Oracles {
  proc f (x : D) -> D;
  proc fi (x : D) -> D;
}

/-- EC's `StrongPRP.Distinguisher (P : SPRP_Oracles)`. -/
abbrev Distinguisher := SPRP_Oracles D →ₘ procmod () → Bool

end StrongPRP

namespace RP

section
variable {D}
/-- EC's `RP.m`. -/
global_var m : FMap D D
/-- EC's `RP.mi`. -/
global_var mi : FMap D D
end

variable (dD : SubProbability D)

-- EC's `RP.RP`
module RP : (StrongPRP.PRP D) {
  proc init () : Unit {
    m <- (FMap.empty : FMap D D);
    mi <- (FMap.empty : FMap D D);
    return ()
  };
  proc f (x : D) : D {
    var y : D;
    if (!(decide (FMap.dom $m $x))) {
      y <$ dexcepted dD (FMap.rng $m);
      m <- FMap.set $m $x $y;
      mi <- FMap.set $mi $y $x;
    }
    return oget (FMap.get $m $x)
  };
  proc fi (y : D) : D {
    var x : D;
    if (!(decide (FMap.dom $mi $y))) {
      x <$ dexcepted dD (FMap.rng $mi);
      mi <- FMap.set $mi $y $x;
      m <- FMap.set $m $x $y;
    }
    return oget (FMap.get $mi $y)
  };
}

end RP

end GaudisCrypt.EC.PRP
