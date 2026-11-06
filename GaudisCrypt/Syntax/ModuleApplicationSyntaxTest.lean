import GaudisCrypt.Syntax.PrSyntax
-- for `#roundtrip`
import GaudisCrypt.Syntax.ProgramSyntaxTest

/-! # Tests for `ModuleApplicationSyntax` -/

set_option linter.style.longLine false

namespace GaudisCrypt.ModuleApplicationSyntaxTest

open GaudisCrypt

moduletype Coin {
  proc flip () -> Bool;
  proc neg (n : Int) -> Int;
}

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

-- a functor with a declared type: `.f` is the accessor
module Swap using (C : Coin) : Coin {
  proc flip () : Bool {
    var b : Bool;
    b <- call C.flip ();
    return !$b
  };
  proc neg (n : Int) : Int {
    var r : Int;
    r <- call C.neg ($n);
    return $r
  };
}

-- a single-procedure functor of two arguments: `.main` names its procedure
module Both using (C : Coin, D : Coin) {
  proc main () : Bool {
    var b1 : Bool, b2 : Bool;
    b1 <- call C.flip ();
    b2 <- call D.flip ();
    return $b1 && $b2
  };
}

example : Swap(FairCoin).flip = Coin.flip (Module.app Swap FairCoin) := rfl
example : Both(FairCoin, Swap(FairCoin)).main =
    Module.app Both (Module.pair FairCoin (Module.app Swap FairCoin)) := rfl
-- an argument that is a Lean term
example : Both((Coin.mk { flip := FairCoin.flip, neg := FairCoin.neg }), FairCoin).main =
    Module.app Both (Module.pair (Coin.mk { flip := FairCoin.flip, neg := FairCoin.neg })
      FairCoin) := rfl

#roundtrip Swap(FairCoin).flip
#roundtrip Swap(Swap(FairCoin)).neg
#roundtrip Both(FairCoin, Swap(FairCoin)).main
#roundtrip Both((Coin.mk { flip := FairCoin.flip, neg := FairCoin.neg }), FairCoin).main

-- in the judgments
variable (m : VariableAssignment)
#roundtrip Pr[ Both(FairCoin, Swap(FairCoin)).main () @ &m : §res ]
#roundtrip Pr[ Swap(FairCoin).neg (3) @ &m : §res = -3 ]
#roundtrip hoare[ Swap(FairCoin).neg : §n = 3 ==> §res = -3 ]
-- field notation after a path
example : Swap(FairCoin).neg.procedure = (Coin.neg (Module.app Swap FairCoin)).procedure := rfl
#roundtrip (Swap(FairCoin).neg).procedure
#roundtrip phoare[ Both(FairCoin, FairCoin).main : True ==> §res ] = (1 / 4)

-- EC's `M.f(x)`, without the space, is still the procedure's arguments
noncomputable example : ℝ := Pr[ FairCoin.neg(3) @ &m : §res = -3 ]

/-- error: the module `GaudisCrypt.ModuleApplicationSyntaxTest.Both` has no procedure `run` (its procedure: [main]) -/
#guard_msgs in
noncomputable example := Both(FairCoin, FairCoin).run

end GaudisCrypt.ModuleApplicationSyntaxTest
