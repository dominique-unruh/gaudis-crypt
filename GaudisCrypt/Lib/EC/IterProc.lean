import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.List

/-!
# EasyCrypt's iteration of a procedure over a list (`theories/looping/IterProc.eca`)

The abstract type `t` is a section variable, so a `clone` is an application.  Only what ported
developments use is here.
-/

namespace GaudisCrypt.EC.IterProc

open GaudisCrypt GaudisCrypt.EC

variable (t : Type) [Inhabited t]

moduletype Orcl {
  proc f (x : t) -> Unit;
}

module Iter using (O : Orcl t) {
  proc iter (l : List t) : Unit {
    while (!(List.isEmpty $l)) {
      _ <- call O.f (head (default : t) $l);
      l <- drop 1 $l;
    }
    return ()
  };
}

end GaudisCrypt.EC.IterProc
