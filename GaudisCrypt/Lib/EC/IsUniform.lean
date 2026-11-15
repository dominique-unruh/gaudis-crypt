import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Logic.PRHLStmt

/-!
# EasyCrypt's `is_uniform` (`theories/distributions/Distr.ec`)

Uniformity on the support, next to `Lib/EC/Distr.lean`'s `is_funiform` (uniformity on the whole
type).  Names are EasyCrypt's.
-/

namespace GaudisCrypt.EC

/-- `is_uniform d`: all values in the support of `d` have the same probability. -/
def is_uniform {α : Type} (d : SubProbability α) : Prop :=
  ∀ x y, x ∈ d.support → y ∈ d.support → d.1 {x} = d.1 {y}

/-- `lemma is_full_funiform`: a full and uniform distribution is uniform on its type. -/
theorem is_full_funiform {α : Type} {d : SubProbability α} (hfu : is_full d)
    (huni : is_uniform d) : is_funiform d := fun x y =>
  huni x y (SubProbability.mem_support_of_ne_zero (hfu x).ne')
    (SubProbability.mem_support_of_ne_zero (hfu y).ne')

/-- A full distribution has every value in its support (EC's `is_fullP`). -/
theorem is_full.mem_support {α : Type} {d : SubProbability α} (h : is_full d) (x : α) :
    x ∈ d.support := SubProbability.mem_support_of_ne_zero (h x).ne'

/-- `lemma funi_uni`: uniform on the type, uniform on the support. -/
theorem funi_uni {α : Type} {d : SubProbability α} (h : is_funiform d) : is_uniform d :=
  fun x y _ _ => h x y

end GaudisCrypt.EC
