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
def iota_ (i n : ℤ) : List ℤ := (List.range n.toNat).map fun k : ℕ => i + (k : ℤ)

/-- `mkseq f n`: `[f 0; …; f (n - 1)]`. -/
def mkseq (f : ℤ → α) (n : ℤ) : List α := (iota_ 0 n).map f

/-- `range m n`: the integers from `m` (included) to `n` (excluded). -/
def range (m n : ℤ) : List ℤ := iota_ m (n - m)

/-- `lemma mkseq0`. -/
theorem mkseq0 (f : ℤ → α) : mkseq f 0 = [] := rfl

/-- `lemma mkseqSr`: `mkseq f (n + 1) = f 0 :: mkseq (f \o (+) 1) n`, for `0 ≤ n`. -/
theorem mkseqSr (f : ℤ → α) (n : ℤ) (hn : 0 ≤ n) :
    mkseq f (n + 1) = f 0 :: mkseq (fun i => f (1 + i)) n := by
  unfold mkseq iota_
  rw [show (n + 1).toNat = n.toNat + 1 by omega, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  refine congrArg₂ _ (by simp) (List.map_congr_left fun k _ => ?_)
  simp only [Function.comp_apply]
  congr 1
  omega

/-- `lemma eq_in_mkseq`: `mkseq` reads its function only on `0 ≤ i < n`. -/
theorem eq_in_mkseq {f g : ℤ → α} {n : ℤ} (h : ∀ i, 0 ≤ i → i < n → f i = g i) :
    mkseq f n = mkseq g n := by
  unfold mkseq iota_
  simp only [List.map_map]
  exact List.map_congr_left fun k hk => by
    simp only [List.mem_range] at hk
    simp only [Function.comp_apply]
    exact h _ (by omega) (by omega)

/-- `lemma size_mkseq`: `size (mkseq f n) = max 0 n`. -/
theorem size_mkseq (f : ℤ → α) (n : ℤ) : size (mkseq f n) = max 0 n := by
  simp only [size, mkseq, iota_, List.length_map, List.length_range]
  omega

/-- `lemma mkseqP`-style membership: an element of `mkseq f n` is `f i` for some `0 ≤ i < n`. -/
theorem mem_mkseq {f : ℤ → α} {n : ℤ} {x : α} :
    x ∈ mkseq f n ↔ ∃ i, 0 ≤ i ∧ i < n ∧ f i = x := by
  simp only [mkseq, iota_, List.map_map, List.mem_map, List.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, by omega, by omega, by simp⟩
  · rintro ⟨i, h0, hi, rfl⟩; exact ⟨i.toNat, by omega, by simp [Int.toNat_of_nonneg h0]⟩

/-- `lemma take_size`: `take (size s) s = s`. -/
theorem take_size (s : List α) : take (size s) s = s := by
  simp [take, size]

/-- `lemma cat_take_drop`: `take n s ++ drop n s = s`. -/
theorem cat_take_drop (n : ℤ) (s : List α) : take n s ++ drop n s = s := by
  simp [take, drop]

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

/-- `lemma nth_rcons`. -/
theorem nth_rcons (x0 : α) (s : List α) (z : α) (i : ℤ) :
    nth x0 (rcons s z) i = if i < size s then nth x0 s i else if i = size s then z else x0 := by
  unfold nth rcons size
  by_cases h0 : 0 ≤ i
  · simp only [h0, if_true, List.getD_eq_getElem?_getD]
    split_ifs with h1 h2
    · rw [List.getElem?_append_left (by omega)]
    · rw [List.getElem?_append_right (by omega), show i.toNat - s.length = 0 by omega]
      simp
    · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)]
      rfl
  · simp only [h0, if_false]
    split_ifs <;> first | rfl | omega

/-- `lemma nth_cat`. -/
theorem nth_cat (x0 : α) (s₁ s₂ : List α) (n : ℤ) :
    nth x0 (s₁ ++ s₂) n = if n < size s₁ then nth x0 s₁ n else nth x0 s₂ (n - size s₁) := by
  unfold nth size
  by_cases h0 : 0 ≤ n
  · simp only [h0, if_true, List.getD_eq_getElem?_getD]
    split_ifs with h1 h2
    · rw [List.getElem?_append_left (by omega)]
    · rw [List.getElem?_append_right (by omega), show (n - s₁.length).toNat = n.toNat - s₁.length
        by omega]
    · omega
  · simp only [h0, if_false]
    split_ifs with h1 h2 <;> first | rfl | omega

/-- `lemma set_nth_default`: in range, the default does not matter. -/
theorem set_nth_default (x1 x2 : α) (s : List α) (n : ℤ) (h : 0 ≤ n ∧ n < size s) :
    nth x1 s n = nth x2 s n := by
  unfold nth size at *
  simp only [h.1, if_true, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

/-- `lemma take_nth`. -/
theorem take_nth (x0 : α) (n : ℤ) (s : List α) (h : 0 ≤ n ∧ n < size s) :
    take (n + 1) s = rcons (take n s) (nth x0 s n) := by
  unfold take rcons nth size at *
  simp only [h.1, if_true, List.getD_eq_getElem?_getD]
  rw [show (n + 1).toNat = n.toNat + 1 by omega, List.take_add_one,
    List.getElem?_eq_getElem (by omega)]
  rfl
end GaudisCrypt.EC
