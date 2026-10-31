import Mathlib.Data.List.Basic
import Mathlib.Data.Int.Init
import Mathlib.Algebra.Order.Ring.Int

/-!
# EasyCrypt's list library, on `int` (`theories/datatypes/List.ec`)

EasyCrypt's list operations take and return `int`s (`size`, `nth`, `take`, `drop`, `nseq`,
`index`, `find`, `mkseq`).  To keep EasyCrypt statements as they are, they are mirrored here on `ℤ`,
with EasyCrypt's behaviour on negative arguments: a negative count is `0`.  The operations that
EasyCrypt shares with Lean (`map`, `rev`, `flatten`, `++`, `∈`) are Lean's.

Only what ported developments use is here.  Names are EasyCrypt's.
-/

namespace GaudisCrypt.EC

variable {α β : Type*}

/-- `size s`, as an `int`. -/
def size (s : List α) : ℤ := s.length

/-- `nseq n x`: `n` copies of `x` (none for `n ≤ 0`). -/
def nseq (n : ℤ) (x : α) : List α := List.replicate n.toNat x

/-- `take n s`: the first `n` elements (none for `n ≤ 0`). -/
def take (n : ℤ) (s : List α) : List α := List.take n.toNat s

/-- `drop n s`: all but the first `n` elements (all for `n ≤ 0`). -/
def drop (n : ℤ) (s : List α) : List α := List.drop n.toNat s

/-- `nth x0 s n`: the `n`-th element, `x0` out of range. -/
def nth (x0 : α) (s : List α) (n : ℤ) : α := if 0 ≤ n then s.getD n.toNat x0 else x0

/-- `head x0 s`. -/
def head (x0 : α) (s : List α) : α := s.headD x0

/-- `behead s`: `s` without its head. -/
def behead (s : List α) : List α := s.tail

/-- `last x0 s`: the last element, `x0` for the empty list. -/
def last (x0 : α) (s : List α) : α := s.getLastD x0

/-- `rcons s x`: `s` with `x` appended. -/
def rcons (s : List α) (x : α) : List α := s ++ [x]

/-- `index x s`: the position of the first `x` in `s`, `size s` if there is none. -/
def index [BEq α] (x : α) (s : List α) : ℤ := s.idxOf x

/-- `find p s`: the position of the first element satisfying `p`, `size s` if there is none. -/
def find (p : α → Bool) (s : List α) : ℤ := s.findIdx p

/-- `iota_ i n`: `[i; i + 1; …; i + n - 1]`. -/
def iota_ (i n : ℤ) : List ℤ := (List.range n.toNat).map fun k => i + k

/-- `mkseq f n`: `[f 0; …; f (n - 1)]`. -/
def mkseq (f : ℤ → α) (n : ℤ) : List α := (iota_ 0 n).map f

/-- `range m n`: the integers from `m` (included) to `n` (excluded). -/
def range (m n : ℤ) : List ℤ := iota_ m (n - m)

/-! ## Function properties (`theories/core` and `theories/prelude`) -/

/-- `cancel f g`: `g` is a left inverse of `f`. -/
def cancel (f : α → β) (g : β → α) : Prop := ∀ x, g (f x) = x

/-- `pcancel f g`: `g` is a partial left inverse of `f`. -/
def pcancel (f : α → β) (g : β → Option α) : Prop := ∀ x, g (f x) = some x

/-- `ocancel g f`: `f` undoes `g` wherever `g` succeeds. -/
def ocancel (g : β → Option α) (f : α → β) : Prop :=
  ∀ x, match g x with | none => True | some y => f y = x

/-- `oget`: the content of an option, `default` for `none`. -/
def oget [Inhabited α] (o : Option α) : α := o.getD default

end GaudisCrypt.EC
