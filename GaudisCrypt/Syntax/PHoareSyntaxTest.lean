import GaudisCrypt.Syntax.PHoareSyntax
-- for `#roundtrip`
import GaudisCrypt.Syntax.ProgramSyntaxTest

/-! # Tests for `PHoareSyntax` -/

set_option linter.style.longLine false

namespace GaudisCrypt.PHoareSyntaxTest

open GaudisCrypt

axiom x : Lens Int VariableAssignment

/- ### Statement judgments -/

-- an event postcondition (a `Prop`): the judgment is about its indicator
example : Prop := phoare[ True ==> §u = 2 ] = 1 {
  var u : Int;
  u <- 2;
}

-- an expectation postcondition (an `ENNReal`), and a bound that needs parentheses
example : Prop := phoare[ True ==> (1 / 2 : ENNReal) ] ≤ (1 / 2) { skip; }

-- the three relations, and a global in the conditions
example : Prop := phoare[ §x = 1 ==> §x = 2 ] >= 1 { x <- §x + 1; }
example : Prop := phoare[ §x = 1 ==> §x = 2 ] <= 1 { x <- §x + 1; }

#roundtrip phoare[ True ==> §u = 2 ] = 1 { var u : Int; u <- 2; }
#roundtrip phoare[ §x = 1 ==> §x = 2 ] ≥ 1 { x <- §x + 1; }
#roundtrip phoare[ True ==> (1 / 2 : ENNReal) ] ≤ (1 / 2) { skip; }

/- ### Procedure judgments -/

moduletype Coin {
  proc flip () -> Bool;
  proc pick (a : Int, b : Int) -> Int;
}

module FairCoin : Coin {
  proc flip () : Bool {
    var b : Bool;
    b <$ SubProbability.uniform;
    return $b
  };
  proc pick (a : Int, b : Int) : Int {
    var c : Bool;
    c <$ SubProbability.uniform;
    return if $c then $a else $b
  };
}

example : Prop := phoare[ FairCoin.flip : True ==> §res = true ] = (1 / 2)
example : Prop := phoare[ FairCoin.pick : §a ≠ §b ==> §res = §x ] ≤ (1 / 2)
-- the bound may mention the parameters and the globals (the postcondition only `res` and the
-- globals, as in EC)
example : Prop := phoare[ FairCoin.pick : True ==> §res = 0 ] ≥ (if §a = 0 ∧ §b = 0 then 1 else 0)
#roundtrip phoare[ FairCoin.pick : True ==> §res = 0 ] ≥ (if §a = 0 ∧ §b = 0 then 1 else 0)

#roundtrip phoare[ FairCoin.flip : True ==> §res = true ] = (1 / 2)
#roundtrip phoare[ FairCoin.pick : §a ≠ §b ==> §res = §x ] ≤ (1 / 2)

end GaudisCrypt.PHoareSyntaxTest
