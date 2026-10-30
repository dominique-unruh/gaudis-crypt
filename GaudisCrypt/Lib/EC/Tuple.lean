import GaudisCrypt.Lib.EC.List

/-!
# EasyCrypt's words over a finite alphabet (`theories/datatypes/Tuple.eca`)

The alphabet's enumeration (`Support.enum` of the `FinType` clone) is an explicit argument.  Only
what ported developments use is here.
-/

namespace GaudisCrypt.EC.Tuple

variable {α : Type*}

namespace WordN

def cross1 (x : α) (s : List (List α)) : List (List α) := s.map fun w => x :: w

def cross (s : List α) (a : List (List α)) : List (List α) := (s.map fun x => cross1 x a).flatten

end WordN

/-- `wordn n`: all words of length `n` over the alphabet `enum`. -/
def wordn (enum : List α) (n : ℤ) : List (List α) :=
  (iota_ 0 n).foldl (fun s _ => WordN.cross enum s) [[]]

end GaudisCrypt.EC.Tuple
