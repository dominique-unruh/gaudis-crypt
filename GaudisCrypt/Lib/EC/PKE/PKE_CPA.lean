import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.Distr

/-!
# IND-CPA security of a public-key encryption scheme
(EasyCrypt `theories/crypto/pke/PKE_CPA.eca`)

The theory's types `pkey`, `skey`, `ptxt`, `ctxt` are `outParam`s of the (field-less) class
`Params`: a clone is `clone import GaudisCrypt.EC.PKE_CPA as PKE with type pkey <- …`.
-/

namespace GaudisCrypt.EC.PKE_CPA

open GaudisCrypt GaudisCrypt.EC

/-- EC's `type pkey, skey, ptxt, ctxt.` -/
class Params (pkey skey ptxt ctxt : outParam Type) : Prop

variable {pkey skey ptxt ctxt : Type} [Inhabited pkey] [Inhabited skey] [Inhabited ptxt]
  [Inhabited ctxt] [Params pkey skey ptxt ctxt]

moduletype Scheme {
  proc kg () -> (pkey × skey);
  proc enc (pk : pkey, m : ptxt) -> ctxt;
}

moduletype Adversary {
  proc choose (pk : pkey) -> (ptxt × ptxt);
  proc guess (c : ctxt) -> Bool;
}

module CPA using (S : Scheme, A : Adversary) {
  proc main () : Bool {
    var pk : pkey, sk : skey, m0 : ptxt, m1 : ptxt, c : ctxt, b : Bool, b' : Bool;
    pk, sk <- call S.kg ();
    m0, m1 <- call A.choose ($pk);
    b <$ dbool;
    c <- call S.enc ($pk, if $b then $m1 else $m0);
    b' <- call A.guess ($c);
    return decide ($b' = $b)
  };
}

end GaudisCrypt.EC.PKE_CPA
