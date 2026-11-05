import GaudisCrypt.Lib.EC.List

/-!
# `range` lemmas of EasyCrypt's `List.ec`

`range m n` (`GaudisCrypt.EC.range`) grows by one at the right (`rangeSr`), is empty when
`n <= m` (`range_geq`), and its members are the integers in `[m, n)` (`mem_range`).  Kept apart
from `List.lean` so that its many importers need not be rebuilt.
-/

namespace GaudisCrypt.EC

/-- `lemma range_geq (m n : int) : n <= m => range m n = []`. -/
theorem range_geq (m n : ℤ) (h : n ≤ m) : range m n = [] := by
  unfold range iota_
  rw [show (n - m).toNat = 0 by omega]
  rfl

/-- `lemma rangeSr (m n : int) : m <= n => range m (n + 1) = rcons (range m n) n`. -/
theorem rangeSr (m n : ℤ) (h : m ≤ n) : range m (n + 1) = rcons (range m n) n := by
  unfold range iota_ rcons
  rw [show (n + 1 - m).toNat = (n - m).toNat + 1 by omega, List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil, List.append_cancel_left_eq, List.cons.injEq, and_true]
  omega

/-- `lemma mem_range (m n i : int) : (i \in range m n) <=> (m <= i < n)`. -/
theorem mem_range (m n i : ℤ) : i ∈ range m n ↔ m ≤ i ∧ i < n := by
  unfold range iota_
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨(i - m).toNat, by omega, by omega⟩

end GaudisCrypt.EC
