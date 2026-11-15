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

-- the parameter names of a single-procedure module's procedure, through `Module.app`
module One using (C : Coin) {
  proc main (k : Int) : Int {
    var r : Int;
    r <- call C.neg ($k);
    return $r
  };
}

#roundtrip hoare[ One(FairCoin).main : §k = 1 ==> §res = -1 ]

-- EC's subtyping by a coercion: the record it builds prints as the module
moduletype Flip {
  proc flip () -> Bool;
}

noncomputable instance : Coe Coin Flip := ⟨fun C => Flip.mk { flip := Coin.flip C }⟩

module UseFlip using (F : Flip) {
  proc main () : Bool {
    var b : Bool;
    b <- call F.flip ();
    return $b
  };
}

#roundtrip UseFlip(FairCoin).main
#roundtrip UseFlip(Swap(FairCoin)).main

-- EC's `module M : T` with a procedure `T` does not list: `M` is `T`'s record, `M.extra` a
-- procedure of its own
module Loaded : Coin {
  proc flip () : Bool {
    return true
  };
  proc neg (k : Int) : Int {
    return -$k
  };
  proc extra (k : Int) : Int {
    return $k + 1
  };
}

noncomputable example : Coin := Loaded
#check (Loaded.extra : procmod (Int) → Int)

-- a module without a module type and with several parameters: the path takes them all, each
-- procedure the ones it uses; a sibling procedure is called by its path
module Two using (C : Coin, F : Flip) {
  proc first () : Bool {
    var b : Bool;
    b <- call F.flip ();
    return $b
  };
  proc second (k : Int) : Int {
    var r : Int;
    r <- call C.neg ($k);
    return $r
  };
  proc both (k : Int) : Int {
    var b : Bool, r : Int;
    b <- call Two(C, F).first ();
    r <- call Two(C, F).second ($k);
    return $r
  };
}

noncomputable example : procmod () → Bool := Two(FairCoin, ((FairCoin : Flip))).first
noncomputable example : procmod (Int) → Int := Two(FairCoin, ((FairCoin : Flip))).second
noncomputable example : procmod (Int) → Int := Two(FairCoin, ((FairCoin : Flip))).both

end GaudisCrypt.ModuleApplicationSyntaxTest
