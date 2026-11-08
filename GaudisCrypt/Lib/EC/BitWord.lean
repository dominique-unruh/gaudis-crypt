import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Language.SubProbability
import GaudisCrypt.Lib.EC.Distr
import Mathlib.Data.Fintype.Vector

/-!
# EasyCrypt's fixed-length bit words (`theories/datatypes/BitWord.eca`) and bit chunking
(`theories/datatypes/BitEncoding.ec`, `BitChunking`)

`BitWord` is an abstract theory over a length `n : int` with `0 < n`.  A clone fixes `n` and
renames `word`, typically to `block` or `capacity`.  Here the theory is the structure `word n`,
and a clone is a namespace of abbreviations under the new names; see
`GaudisCrypt/Examples/SHA3/Common.lean`.
-/

namespace GaudisCrypt.EC

/-- `word`: bit strings of length `n`. -/
abbrev BitWord.word (n : ℤ) := List.Vector Bool n.toNat

namespace BitWord

variable {n : ℤ}

/-- `ofword w`: the bits of `w`. -/
def ofword (w : word n) : List Bool := w.toList

/-- `mkword s`: the word whose `i`-th bit is `nth false s i`.  `s` is cut or padded with `false` to
length `n`. -/
def mkword (s : List Bool) : word n := List.Vector.ofFn fun i => s.getD i false

/-- `zerow`: the all-`false` word. -/
def zerow : word n := List.Vector.replicate _ false

/-- `w₁ +^ w₂`: bitwise exclusive or. -/
def xorw (w₁ w₂ : word n) : word n := List.Vector.map₂ xor w₁ w₂

instance : Inhabited (word n) := ⟨zerow⟩

/-- `lemma mkwordK : cancel ofword mkword`. -/
theorem mkwordK (w : word n) : mkword (ofword w) = w := by
  apply List.Vector.ext
  intro i
  have hi : (i : ℕ) < (List.Vector.toList w).length := by
    rw [List.Vector.toList_length]; exact i.isLt
  rw [mkword, List.Vector.get_ofFn]
  simp only [ofword, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.Vector.get_eq_get_toList]
  rfl

/-- `lemma ofwordK s : size s = n => ofword (mkword s) = s`. -/
theorem ofwordK (s : List Bool) (h : size s = n) : ofword (mkword s : word n) = s := by
  have hl : s.length = n.toNat := by simp only [size] at h; omega
  apply List.ext_getElem (by simp [ofword, hl])
  intro i h1 h2
  simp [ofword, mkword, List.getD_eq_getElem?_getD, h2]

/-- `lemma size_word w : size (ofword w) = n` (`0 ≤ n`, EC's `gt0_n`). -/
theorem size_word (hn : 0 ≤ n) (w : word n) : size (ofword w) = n := by
  simp [size, ofword, Int.toNat_of_nonneg hn]

/-- `DWord.dunifin`: the uniform distribution on words. -/
noncomputable def dunifin : SubProbability (word n) := SubProbability.uniform

/-- `DWord.dunifin_ll`. -/
theorem dunifin_ll : is_lossless (dunifin : SubProbability (word n)) := uniform_ll

/-- `DWord.dunifin_fu`. -/
theorem dunifin_fu : is_full (dunifin : SubProbability (word n)) := uniform_fu

/-- `DWord.dunifin_funi`. -/
theorem dunifin_funi : is_funiform (dunifin : SubProbability (word n)) := uniform_funi

end BitWord

/-- `w₁ +^ w₂`. -/
infixl:65 " +^ " => BitWord.xorw

/-- `BitChunking.chunk r bs`: `bs` cut into pieces of length `r`; an incomplete last piece is
dropped. -/
def BitChunking.chunk {α : Type*} (r : ℤ) (bs : List α) : List (List α) :=
  mkseq (fun i => take r (drop (r * i) bs)) (size bs / r)

end GaudisCrypt.EC
