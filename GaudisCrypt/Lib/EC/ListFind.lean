import GaudisCrypt.Lib.EC.List

/-!
# EasyCrypt's `find` and `nth` (`theories/datatypes/List.ec`): `nth_find`

Names are EasyCrypt's.
-/

namespace GaudisCrypt.EC

variable {α : Type}

/-- `lemma nth_find z p s : has p s => p (nth z s (find p s))`. -/
theorem nth_find (z : α) (p : α → Bool) (s : List α) (h : ∃ x ∈ s, p x = true) :
    p (nth z s (find p s)) = true := by
  have hlt : s.findIdx p < s.length := List.findIdx_lt_length_of_exists h
  have hnn : (0 : ℤ) ≤ (s.findIdx p : ℤ) := Int.natCast_nonneg _
  unfold nth find
  rw [if_pos hnn, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  exact List.findIdx_getElem

end GaudisCrypt.EC
