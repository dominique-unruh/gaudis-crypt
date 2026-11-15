import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.Distr

/-!
# Commitment schemes (EasyCrypt `theories/crypto/Commitment.ec`)

EC's theory `CommitmentProtocol`: the module type of a commitment scheme and the experiments for
correctness, hiding and binding.  The theory's types are `outParam`s of the (field-less) class
`Params`: a clone is `clone import GaudisCrypt.EC.CommitmentProtocol as CM with type value <- …`.
-/

namespace GaudisCrypt.EC.CommitmentProtocol

open GaudisCrypt GaudisCrypt.EC

/-- EC's `type value, message, commitment, openingkey.` -/
class Params (value message commitment openingkey : outParam Type) : Prop

variable {value message commitment openingkey : Type} [Inhabited value] [Inhabited message]
  [Inhabited commitment] [Inhabited openingkey] [DecidableEq message]
  [Params value message commitment openingkey]

moduletype CommitmentScheme {
  proc gen () -> value;
  proc commit (x : value, m : message) -> (commitment × openingkey);
  proc verify (x : value, m : message, c : commitment, d : openingkey) -> Bool;
}

module Correctness using (S : CommitmentScheme) {
  proc main (m : message) : Bool {
    var x : value, c : commitment, d : openingkey, b : Bool;
    x <- call S.gen ();
    c, d <- call S.commit ($x, $m);
    b <- call S.verify ($x, $m, $c, $d);
    return $b
  };
}

moduletype Unhider {
  proc choose (x : value) -> (message × message);
  proc guess (c : commitment) -> Bool;
}

module HidingExperiment using (S : CommitmentScheme, U : Unhider) {
  proc main () : Bool {
    var b : Bool, b' : Bool, m0 : message, m1 : message, x : value, c : commitment,
      d : openingkey;
    x <- call S.gen ();
    m0, m1 <- call U.choose ($x);
    b <$ dbool;
    c, d <- call S.commit ($x, if $b then $m1 else $m0);
    b' <- call U.guess ($c);
    return decide ($b = $b')
  };
}

moduletype Binder {
  proc bind (x : value) -> (commitment × message × openingkey × message × openingkey);
}

module BindingExperiment using (S : CommitmentScheme, B : Binder) {
  proc main () : Bool {
    var x : value, c : commitment, m : message, m' : message, d : openingkey, d' : openingkey,
      v : Bool, v' : Bool;
    x <- call S.gen ();
    c, m, d, m', d' <- call B.bind ($x);
    v <- call S.verify ($x, $m, $c, $d);
    v' <- call S.verify ($x, $m', $c, $d');
    return $v && $v' && decide ($m ≠ $m')
  };
}

end GaudisCrypt.EC.CommitmentProtocol
