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

example : phoare[ FairCoin.flip : True ==> §res = true ] = (1 / 2) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 3
  phoare_skip
  simp

end GaudisCrypt.PHoareWpTest
