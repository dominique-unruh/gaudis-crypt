import GaudisCrypt.Syntax.PrSyntax
-- for `#roundtrip`
import GaudisCrypt.Syntax.ProgramSyntaxTest

/-! # Tests for `PrSyntax` -/

set_option linter.style.longLine false

namespace GaudisCrypt.PrSyntaxTest

open GaudisCrypt

axiom x : Lens Int VariableAssignment

moduletype Coin {
  proc flip () -> Bool;
  proc pick (a : Int, b : Int) -> Int;
  proc neg (n : Int) -> Int;
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
  proc neg (n : Int) : Int {
    x <- - $n;
    return - $n
  };
}

variable (m : VariableAssignment)

-- no arguments; a `Bool` event (EC's `: res`)
noncomputable example : ℝ := Pr[ FairCoin.flip () @ &m : §res ]
-- one argument, several arguments, a global in the event
noncomputable example : ℝ := Pr[ FairCoin.neg (3) @ &m : §res = -3 ∧ §x = -3 ]
noncomputable example : ℝ := Pr[ FairCoin.pick (1, 2) @ &m : §res = 1 ]
-- the argument tuple as one term
noncomputable example (ab : Int × Int) : ℝ := Pr[ FairCoin.pick (ab) @ &m : §res = 1 ]
-- EC's arithmetic on probabilities: they are reals
example : Prop := |Pr[ FairCoin.flip () @ &m : §res ] - Pr[ FairCoin.flip () @ &m : ¬ §res ]| ≤ 1
-- a memory that is not an atom
noncomputable example (f : VariableAssignment → VariableAssignment) : ℝ := Pr[ FairCoin.flip () @ &(f m) : §res ]

-- it is `Procedure.Pr`, coerced
example : Pr[ FairCoin.pick (1, 2) @ &m : §res = 1 ] =
    (Procedure.Pr (Module.Proc.procedure FairCoin.pick) (1, 2) m (fun r _ => r = 1) : ℝ) := rfl

#roundtrip Pr[ FairCoin.flip () @ &m : §res ]
#roundtrip Pr[ FairCoin.neg (3) @ &m : §res = -3 ∧ §x = -3 ]
#roundtrip Pr[ FairCoin.pick (1, 2) @ &m : §res = 1 ]
#roundtrip fun (ab : Int × Int) => Pr[ FairCoin.pick (ab) @ &m : §res = 1 ]
#roundtrip fun (f : VariableAssignment → VariableAssignment) => Pr[ FairCoin.flip () @ &(f m) : §res ]
#roundtrip |Pr[ FairCoin.flip () @ &m : §res ] - Pr[ FairCoin.flip () @ &m : ¬ §res ]| ≤ 1

-- a module application as the subject
module Twice using (C : Coin) {
  proc main () : Bool {
    var b1 : Bool, b2 : Bool;
    b1 <- call C.flip ();
    b2 <- call C.flip ();
    return $b1 && $b2
  };
}

#roundtrip Pr[ Twice(FairCoin).main () @ &m : §res ]

end GaudisCrypt.PrSyntaxTest
