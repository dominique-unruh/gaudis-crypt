import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Lib.EC.List

/-!
# Sigma protocols (EasyCrypt `theories/crypto/SigmaProtocol.ec`)

EC's theory `SigmaProtocol`: the module types of a scheme and of its algorithms (extractor and
simulator), and the experiments for completeness, special soundness and special honest-verifier
zero knowledge.

The theory's types are `outParam`s of the class `Params`, its operators `de` and `R` the fields:
a clone is `clone import GaudisCrypt.EC.SigmaProtocol as SP with type statement <- …, op R <- …,
op de <- …`.  EC's `op slen`, `op wlen` with their axioms `slen_pos`, `wlen_pos` are used by no
declaration of the theory and are left out (EC's clones leave them abstract).  `R x w` is a
proposition; where a program stores it (`r <- R x w`) it is decided classically, as EC's logic
is.  EC's variable `to` is a Lean keyword, hence `«to»`.

Gap: `SimulateHonestVerifier.main` calls the module's own procedures (`b' <@ gameIdeal()`); there
is no syntax for that in a module with parameters, and the calls are written with the procedure
modules applied to the parameters they use.
-/

namespace GaudisCrypt.EC.SigmaProtocol

open GaudisCrypt GaudisCrypt.EC

/-- EC's `type statement, witness, message, secret, challenge, response`, `op de` and `op R`. -/
class Params (statement witness message secret challenge response : outParam Type) where
  de : SubProbability challenge
  R : statement → witness → Prop

export Params (de R)

variable {statement witness message secret challenge response : Type}
  [Inhabited statement] [Inhabited witness] [Inhabited message] [Inhabited secret]
  [Inhabited challenge] [Inhabited response] [DecidableEq challenge]
  [Params statement witness message secret challenge response]

/-- EC's `type transcript = message * challenge * response`. -/
abbrev transcript [Params statement witness message secret challenge response] : Type :=
  message × challenge × response

moduletype SigmaScheme {
  proc gen () -> (statement × witness);
  proc commit (x : statement, w : witness) -> (message × secret);
  proc test (x : statement, m : message) -> challenge;
  proc respond (sw : statement × witness, ms : message × secret, e : challenge) -> response;
  proc verify (x : statement, m : message, e : challenge, z : response) -> Bool;
}

moduletype SigmaAlgorithms {
  proc soundness (x : statement, m : message, e : challenge, z : response, e' : challenge,
    z' : response) -> (Option witness);
  proc simulate (x : statement, e : challenge) -> (message × challenge × response);
}

module Completeness using (S : SigmaScheme) {
  proc main (x : statement, w : witness) : Bool {
    var e : challenge, m : message, s : secret, z : response, b : Bool;
    m, s <- call S.commit ($x, $w);
    e <- call S.test ($x, $m);
    z <- call S.respond (($x, $w), ($m, $s), $e);
    b <- call S.verify ($x, $m, $e, $z);
    return $b
  };
}

module Run using (S : SigmaScheme) {
  proc main () : (statement × message × challenge × response) {
    var x : statement, w : witness, m : message, s : secret, e : challenge, z : response;
    x, w <- call S.gen ();
    m, s <- call S.commit ($x, $w);
    e <- call S.test ($x, $m);
    z <- call S.respond (($x, $w), ($m, $s), $e);
    return ($x, $m, $e, $z)
  };
}

open Classical in
module SpecialSoundnessExperiment using (S : SigmaScheme, A : SigmaAlgorithms) {
  proc main (x : statement, m : message, e : challenge, z : response, e' : challenge,
      z' : response) : (Option witness) {
    var s : Option witness, sto : Option witness, w : witness, r : Bool, v : Bool, v' : Bool;
    sto <- call A.soundness ($x, $m, $e, $z, $e', $z');
    if (decide ($e ≠ $e' ∧ $sto ≠ none)) {
      w <- oget $sto;
      r <- decide (R $x $w);
      v <- call S.verify ($x, $m, $e, $z);
      v' <- call S.verify ($x, $m, $e', $z');
      if ($r && $v && $v') {
        s <- some $w;
      } else {
        s <- none;
      }
    } else {
      s <- none;
    }
    return $s
  };
}

module SpecialHVZKExperiment using (S : SigmaScheme, A : SigmaAlgorithms) {
  proc main (x : statement, e : challenge) : (Option (message × challenge × response)) {
    var m : message, z : response, v : Bool, «to» : Option (message × challenge × response);
    m, e, z <- call A.simulate ($x, $e);
    v <- call S.verify ($x, $m, $e, $z);
    if ($v) {
      «to» <- some ($m, $e, $z);
    } else {
      «to» <- none;
    }
    return $«to»
  };
}

moduletype SigmaTraceDistinguisher {
  proc distinguish (x : statement, t : transcript) -> Bool;
}

module SimulateHonestVerifier using (S : SigmaScheme, A : SigmaAlgorithms,
    D : SigmaTraceDistinguisher) {
  proc gameIdeal () : Bool {
    var b : Bool, e : challenge, i : ℤ, m : message, s : secret, t : transcript,
      «to» : Option transcript, x : statement, w : witness;
    x, w <- call S.gen ();
    m, s <- call S.commit ($x, $w);
    e <$ de;
    «to» <- call SpecialHVZKExperiment(S, A).main ($x, $e);
    i <- 0;
    while (decide ($«to» = none)) {
      «to» <- call SpecialHVZKExperiment(S, A).main ($x, $e);
      i <- $i + 1;
    }
    t <- oget $«to»;
    b <- call D.distinguish ($x, $t);
    return $b
  };
  proc gameReal () : Bool {
    var b : Bool, t : transcript, m : message, e : challenge, z : response, x : statement;
    x, m, e, z <- call Run(S).main ();
    t <- ($m, $e, $z);
    b <- call D.distinguish ($x, $t);
    return $b
  };
  -- EC's `b' <@ gameIdeal()`, `b' <@ gameReal()`: the module's own procedures, here as the
  -- procedure modules applied to the parameters they use (GAP: no syntax for a sibling's call)
  proc main () : Bool {
    var b : Bool, b' : Bool;
    b <$ dbool;
    if ($b) {
      b' <- call (Module.app (Module.app (Module.app SimulateHonestVerifier.gameIdeal S) A) D) ();
    } else {
      b' <- call (Module.app (Module.app SimulateHonestVerifier.gameReal S) D) ();
    }
    return decide ($b' = $b)
  };
}

end GaudisCrypt.EC.SigmaProtocol
