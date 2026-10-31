import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Lib.EC.FMap
import GaudisCrypt.Lib.EC.Distr

/-!
# EasyCrypt's pseudo-random permutations (`theories/crypto/PRP.eca`)

The abstract type `D` and the operator `dD` are Lean parameters, so EasyCrypt's
`clone PRP with type D <- …` and `clone RP with op dD <- …` are applications.  So are the module
variables (`RP.m`, `RP.mi`): a clone declares its own `global_var`s and passes them.  The sub-theories
`StrongPRP` and `RP` are namespaces.  Only what ported developments use is here (`WeakPRP` is not).
-/

-- EasyCrypt names a module after its theory (`RP.RP`, `IRO.IRO`); kept (exception E1)
set_option linter.dupNamespace false

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

module IND using (P : PRP D, Dist : Distinguisher D) {
  proc main () : Bool {
    var b : Bool;
    _ <- call P.init ();
    b <- call (Module.app Dist (SPRP_Oracles.mk D { f := PRP.f D P, fi := PRP.fi D P })) ();
    return $b
  };
}

end StrongPRP

namespace RP

/-! The module variables `RP.m`, `RP.mi` are parameters: each clone declares its own (EasyCrypt's
`clone RP as Perm` has `Perm.m`, `Perm.mi`), so two clones never share them. -/

variable (dD : SubProbability D) (m mi : Lens (FMap D D) VariableAssignment)

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
