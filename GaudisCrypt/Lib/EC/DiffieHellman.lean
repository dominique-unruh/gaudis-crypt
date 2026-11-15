import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.Group

/-!
# Diffie–Hellman assumptions (EasyCrypt `theories/crypto/DiffieHellman.ec`)

The theories `DDH` and `CDH` over a cyclic group of prime order (`Lib/EC/Group.lean`: EC's
`clone CyclicGroup as G`, `clone G.PowZMod as GP`, `clone GP.FDistr as FD` at the head of the
file).  `List_CDH` and `Set_CDH` with their reductions are not ported yet.
-/

-- EasyCrypt names the game after its theory (`CDH.CDH`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.EC.DiffieHellman

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.CyclicGroup

variable {group exp : Type} [CommGroup group] [Field exp] [Fintype exp]
  [CyclicGroup.Params group exp]

/-! ## Decisional Diffie–Hellman -/

namespace DDH

moduletype Adversary {
  proc guess (gx : group, gy : group, gz : group) -> Bool;
}

module DDH0 using (A : Adversary) {
  proc main () : Bool {
    var b : Bool, x : exp, y : exp;
    x <$ dt;
    y <$ dt;
    b <- call A.guess (g ^ $x, g ^ $y, g ^ ($x * $y));
    return $b
  };
}

module DDH1 using (A : Adversary) {
  proc main () : Bool {
    var b : Bool, x : exp, y : exp, z : exp;
    x <$ dt;
    y <$ dt;
    z <$ dt;
    b <- call A.guess (g ^ $x, g ^ $y, g ^ $z);
    return $b
  };
}

end DDH

/-! ## Computational Diffie–Hellman -/

namespace CDH

moduletype Adversary {
  proc solve (gx : group, gy : group) -> group;
}

open Classical in
module CDH using (A : Adversary) {
  proc main () : Bool {
    var x : exp, y : exp, r : group;
    x <$ dt;
    y <$ dt;
    r <- call A.solve (g ^ $x, g ^ $y);
    return decide ($r = g ^ ($x * $y))
  };
}

end CDH

end GaudisCrypt.EC.DiffieHellman
