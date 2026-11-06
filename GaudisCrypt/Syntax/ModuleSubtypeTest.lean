import GaudisCrypt.Syntax.ModuleSubtype
import GaudisCrypt.Syntax.PrSyntax
-- for `#roundtrip`
import GaudisCrypt.Syntax.ProgramSyntaxTest

/-! # Tests for `module_subtype` -/

namespace GaudisCrypt.ModuleSubtypeTest

open GaudisCrypt

moduletype Coin {
  proc flip () -> Bool;
  proc neg (n : Int) -> Int;
}

moduletype Flip {
  proc flip () -> Bool;
}

module_subtype Coin <: Flip

module FairCoin : Coin {
  proc flip () : Bool {
    var b : Bool;
    b <$ SubProbability.uniform;
    return $b
  };
  proc neg (n : Int) : Int {
    return - $n
  };
}

module UseFlip using (F : Flip) {
  proc main () : Bool {
    var b : Bool;
    b <- call F.flip ();
    return $b
  };
}

-- a `Coin` where a `Flip` is expected; the coercion is the record of `Coin`'s `flip`
example : UseFlip(FairCoin).main =
    Module.app UseFlip (Flip.mk { flip := Coin.flip FairCoin }) := rfl
#roundtrip UseFlip(FairCoin).main

-- in a module body
module Twice using (C : Coin) {
  proc main () : Bool {
    var b : Bool;
    b <- call UseFlip(C).main ();
    return $b
  };
}

#roundtrip Twice(FairCoin).main

end GaudisCrypt.ModuleSubtypeTest
