import GaudisCrypt.Logic.PHoareWp
import GaudisCrypt.Syntax.PHoareSyntax

/-! # Tests for the `phoare` tactics -/

namespace GaudisCrypt.PHoareWpTest

open GaudisCrypt

moduletype Coin {
  proc flip () -> Bool;
}

module FairCoin : Coin {
  proc flip () : Bool {
    var b : Bool;
    b <$ SubProbability.uniform;
    return $b
  };
}

theorem flip_half : phoare[ FairCoin.flip : True ==> §res = true ] = (1 / 2) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 3
  phoare_skip
  simp

/- ### Calls with a specification -/

module Relay using (C : Coin) {
  proc run () : Bool {
    var b : Bool;
    b <- call C.flip ();
    return $b
  };
}

-- modular: `FairCoin.flip` is not inlined, its judgment is used
example : phoare[ (Module.app Relay FairCoin) : True ==> §res = true ] = (1 / 2) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_call flip_half
  phoare_wp 1
  phoare_skip
  simp

-- an abstract coin, known only by an upper bound
example (C : Coin) (hC : phoare[ C.flip : True ==> §res = true ] ≤ (1 / 3)) :
    phoare[ (Module.app Relay C) : True ==> §res = true ] ≤ (1 / 3) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_call hC
  phoare_wp 1
  phoare_skip
  simp

module TwoFlips using (C : Coin) {
  proc both () : Bool {
    var a : Bool, b : Bool;
    a <- call C.flip ();
    b <- call C.flip ();
    return $a && $b
  };
}

-- the continuation of the second call still depends on `a`: the judgment as a rewrite rule
example : phoare[ (Module.app TwoFlips FairCoin) : True ==> §res = true ] = (1 / 4) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 4
  phoare_skip
  phoare_simp [flip_half]
  intro _
  norm_num [← ENNReal.mul_inv]

end GaudisCrypt.PHoareWpTest
