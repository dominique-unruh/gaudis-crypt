import GaudisCrypt.Lib.EC.FSet
import GaudisCrypt.Lib.EC.List

/-!
# EasyCrypt's `FSet`: `oflist` and membership (`theories/datatypes/FSet.ec`)

Next to `Lib/EC/FSet.lean`: the finite set of a list, EC's names for membership in a union, an
intersection, a singleton and the empty set, and `mem_iota` of `List.ec`.  EC's `` s `|` t ``
and `` s `&` t `` are `s ∪ t` and `s ∩ t`.  Names are EasyCrypt's.
-/

namespace GaudisCrypt.EC

/-- `lemma mem_iota`: `x \in iota_ m n <=> m <= x < m + n`. -/
theorem mem_iota (m n x : ℤ) : x ∈ iota_ m n ↔ m ≤ x ∧ x < m + n := by
  simp only [iota_, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨(x - m).toNat, by omega, by omega⟩

namespace FSet

variable {α : Type}

/-- `lemma in_fset0`. -/
@[simp] theorem in_fset0 (x : α) : x ∈ (fset0 : FSet α) ↔ False := by simp [fset0]

/-- `lemma in_fset1`. -/
@[simp] theorem in_fset1 (z x : α) : x ∈ fset1 z ↔ x = z := by simp [fset1]

/-- `lemma fsetP`: extensionality. -/
theorem fsetP (s1 s2 : FSet α) : s1 = s2 ↔ ∀ x, x ∈ s1 ↔ x ∈ s2 := Finset.ext_iff

variable [DecidableEq α]

/-- `op oflist`: the finite set of the elements of a list. -/
def oflist (s : List α) : FSet α := s.toFinset

/-- `lemma mem_oflist`. -/
@[simp] theorem mem_oflist (s : List α) (x : α) : x ∈ oflist s ↔ x ∈ s := List.mem_toFinset

/-- `lemma in_fsetU`. -/
theorem in_fsetU (s1 s2 : FSet α) (x : α) : x ∈ s1 ∪ s2 ↔ x ∈ s1 ∨ x ∈ s2 := Finset.mem_union

/-- `lemma in_fsetI`. -/
theorem in_fsetI (s1 s2 : FSet α) (x : α) : x ∈ s1 ∩ s2 ↔ x ∈ s1 ∧ x ∈ s2 := Finset.mem_inter

/-- `lemma set0E : fset0 = oflist []`. -/
theorem set0E : (fset0 : FSet α) = oflist [] := rfl

/-- `lemma oflist_cons`. -/
theorem oflist_cons (x : α) (s : List α) : oflist (x :: s) = fset1 x ∪ oflist s := by
  ext y; simp [oflist, fset1]

/-- `lemma fset0U`. -/
@[simp] theorem fset0U (s : FSet α) : fset0 ∪ s = s := by simp [fset0]

end FSet

end GaudisCrypt.EC
