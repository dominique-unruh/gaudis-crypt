import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.PRHLStmt
import GaudisCrypt.Lib.EC.Distr

/-!
# EasyCrypt's product distributions (`theories/distributions/DProd.ec`), `ProdSampling`

The abstract theory `ProdSampling`'s types `t1`, `t2` are section variables, so a `clone` is an
application.  Only what ported developments use is here.
-/

namespace GaudisCrypt.EC.DProd.ProdSampling

open GaudisCrypt GaudisCrypt.EC

variable (t1 t2 : Type) [Inhabited t1] [Inhabited t2]

module S {
  proc sample (d1 : SubProbability t1, d2 : SubProbability t2) : (t1 × t2) {
    var r : t1 × t2;
    r <$ dprod $d1 $d2;
    return $r
  };
  proc sample2 (d1 : SubProbability t1, d2 : SubProbability t2) : (t1 × t2) {
    var r1 : t1, r2 : t2;
    r1 <$ $d1;
    r2 <$ $d2;
    return ($r1, $r2)
  };
}

/-- `equiv sample_sample2 : S.sample ~ S.sample2 : ={d1, d2} ==> ={res}`. -/
theorem sample_sample2 :
    prhlProc (fun a₁ _ a₂ _ => a₁ = a₂) (S.sample t1 t2).procedure (S.sample2 t1 t2).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  sorry

end GaudisCrypt.EC.DProd.ProdSampling
