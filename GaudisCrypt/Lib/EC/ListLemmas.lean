import GaudisCrypt.Lib.EC.List

/-!
# More of EasyCrypt's list library (`theories/datatypes/List.ec`)

The lemmas on `take`, `nth`, `size`, `nseq`, `last` that ported proofs cite in their `smt(…)` and
`rewrite`s, under EasyCrypt's names and with its statements (on `int`, see `Lib/EC/List.lean`).
Kept apart from `List.lean` only so that adding one does not rebuild everything over it.
-/

namespace GaudisCrypt.EC

variable {α : Type*}

/-- `lemma take0`. -/
theorem take0 (s : List α) : take 0 s = [] := by simp [take]

/-- `lemma take_le0`. -/
theorem take_le0 (n : ℤ) (s : List α) (h : n ≤ 0) : take n s = [] := by
  simp [take, Int.toNat_of_nonpos h]

/-- `lemma take_oversize`. -/
theorem take_oversize (n : ℤ) (s : List α) (h : size s ≤ n) : take n s = s :=
  List.take_of_length_le (by simp only [size] at h; omega)

/-- `lemma size_take`. -/
theorem size_take (n : ℤ) (s : List α) (h : 0 ≤ n) :
    size (take n s) = if n < size s then n else size s := by
  simp only [size, take, List.length_take]
  split_ifs <;> omega

/-- `lemma nth_take`. -/
theorem nth_take (x0 : α) (n : ℤ) (s : List α) (i : ℤ) (_h0 : 0 ≤ n) (h : i < n) :
    nth x0 (take n s) i = nth x0 s i := by
  unfold nth take
  split_ifs with hi
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
    rw [if_pos (by omega)]
  · rfl

/-- `lemma size_cat`. -/
theorem size_cat (s₁ s₂ : List α) : size (s₁ ++ s₂) = size s₁ + size s₂ := by simp [size]

/-- `lemma size_nseq`. -/
theorem size_nseq (n : ℤ) (x : α) : size (nseq n x) = max 0 n := by
  simp only [size, nseq, List.length_replicate]
  omega

/-- `lemma size_rcons`. -/
theorem size_rcons (s : List α) (x : α) : size (rcons s x) = size s + 1 := by
  simp [size, rcons]

/-- `lemma nth_nseq`. -/
theorem nth_nseq (x0 : α) (m : ℤ) (x : α) (n : ℤ) (h : 0 ≤ n ∧ n < m) :
    nth x0 (nseq m x) n = x := by
  unfold nth nseq
  rw [if_pos h.1, List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (by omega)]
  rfl

/-- `lemma cats0`. -/
theorem cats0 (s : List α) : s ++ [] = s := List.append_nil s

/-- `lemma nseq0`. -/
theorem nseq0 (x : α) : nseq 0 x = [] := rfl

/-- `lemma take_cat`. -/
theorem take_cat (n : ℤ) (s₁ s₂ : List α) :
    take n (s₁ ++ s₂) = if n < size s₁ then take n s₁ else s₁ ++ take (n - size s₁) s₂ := by
  unfold take size
  split_ifs with h
  · rw [List.take_append_of_le_length (by omega)]
  · rw [List.take_append, List.take_of_length_le (by omega),
      show (n - (s₁.length : ℤ)).toNat = n.toNat - s₁.length by omega]

/-- `lemma last_rcons`. -/
theorem last_rcons (x0 : α) (s : List α) (x : α) : last x0 (rcons s x) = x := by
  simp [last, rcons]

/-- `lemma nth_last`. -/
theorem nth_last (x0 : α) (s : List α) : nth x0 s (size s - 1) = last x0 s := by
  unfold nth last size
  rcases List.eq_nil_or_concat s with rfl | ⟨l, a, rfl⟩
  · simp
  · rw [if_pos (by simp), List.getD_eq_getElem?_getD]
    simp

/-- `lemma last_cat`. -/
theorem last_cat (x0 : α) (s₁ s₂ : List α) : last x0 (s₁ ++ s₂) = last (last x0 s₁) s₂ := by
  unfold last
  rcases List.eq_nil_or_concat s₂ with rfl | ⟨l, a, rfl⟩
  · simp
  · simp [← List.append_assoc]

/-- `lemma last_nseq`. -/
theorem last_nseq (x0 : α) (n : ℤ) (x : α) (h : 0 < n) : last x0 (nseq n x) = x := by
  unfold last nseq
  obtain ⟨k, hk⟩ : ∃ k, n.toNat = k + 1 := ⟨n.toNat - 1, by omega⟩
  rw [hk, List.replicate_succ']
  simp

end GaudisCrypt.EC
