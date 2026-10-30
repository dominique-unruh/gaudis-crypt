import Mathlib.Data.Finset.Basic

/-!
# EasyCrypt's finite sets (`theories/datatypes/FSet.ec`)

`'a fset` is Mathlib's `Finset`.  Only what ported developments use is here.  Names are
EasyCrypt's; the operators `` `|` `` and `` `\` `` are Lean's `∪` and `\`.
-/

namespace GaudisCrypt.EC

/-- `'a fset`. -/
abbrev FSet (α : Type*) := Finset α

namespace FSet

variable {α : Type*}

/-- `fset0`: the empty set. -/
def fset0 : FSet α := ∅

/-- `fset1 x`: the singleton. -/
def fset1 (x : α) : FSet α := {x}

/-- `elems s`: the elements of `s`, as a list (in some order). -/
noncomputable def elems (s : FSet α) : List α := s.toList

open Classical in
/-- `pick s`: some element of `s` (EasyCrypt leaves which one unspecified), `witness` for the
empty set. -/
noncomputable def pick [Inhabited α] (s : FSet α) : α :=
  if h : s.Nonempty then h.choose else default

end FSet

end GaudisCrypt.EC
