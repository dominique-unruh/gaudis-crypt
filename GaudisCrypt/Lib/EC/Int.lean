import Mathlib.Data.Int.Init
import Mathlib.Logic.Function.Iterate

/-!
# EasyCrypt's integers (`theories/datatypes/Int.ec`)

Only what ported developments use is here.  Names are EasyCrypt's.
-/

namespace GaudisCrypt.EC

/-- `iter n f x`: `f` applied `n` times to `x` (no times for `n ≤ 0`). -/
def iter {α : Type*} (n : ℤ) (f : α → α) (x : α) : α := f^[n.toNat] x

end GaudisCrypt.EC
