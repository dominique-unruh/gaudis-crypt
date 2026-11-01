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

/-- `DWord.dunifin`: the uniform distribution on words. -/
noncomputable def dunifin : SubProbability (word n) := SubProbability.uniform

/-- `DWord.dunifin_ll`. -/
theorem dunifin_ll : is_lossless (dunifin : SubProbability (word n)) := uniform_ll

end BitWord

/-- `w₁ +^ w₂`. -/
infixl:65 " +^ " => BitWord.xorw

/-- `BitChunking.chunk r bs`: `bs` cut into pieces of length `r`; an incomplete last piece is
dropped. -/
def BitChunking.chunk {α : Type*} (r : ℤ) (bs : List α) : List (List α) :=
  mkseq (fun i => take r (drop (r * i) bs)) (size bs / r)

end GaudisCrypt.EC
