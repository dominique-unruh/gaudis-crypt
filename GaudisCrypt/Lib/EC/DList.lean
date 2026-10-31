import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Lib.EC.Distr

/-!
# EasyCrypt's list distributions (`theories/distributions/DList.ec`)

`dlist d n` samples `n` values from `d`, independently.  The abstract theory `Program`'s type `t`
and operator `d` are section variables, so a `clone` is an application.  Only what ported
developments use is here.
-/

namespace GaudisCrypt.EC

variable {α : Type}

/-- `dlist d n`: a list of `n` independent samples of `d` (the empty list for `n ≤ 0`). -/
noncomputable def dlist (d : SubProbability α) (n : ℤ) : SubProbability (List α) :=
  go n.toNat
where
  /-- `dlist d n` for `n : ℕ`. -/
  go : ℕ → SubProbability (List α)
    | 0 => pure []
    | k + 1 => d >>= fun a => go k >>= fun l => pure (a :: l)

namespace DList.Program

open GaudisCrypt

variable (t : Type) [Inhabited t] (d : SubProbability t)

module LoopSnoc {
  proc sample (n : ℤ) : (List t) {
    var i : ℤ, r : t, l : List t;
    i <- 0;
    l <- [];
    while ($i < $n) {
      r <$ d;
      l <- $l ++ [$r];
      i <- $i + 1;
    }
    return $l
  };
}

end DList.Program

end GaudisCrypt.EC
