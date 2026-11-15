import GaudisCrypt.Lib.EC.BitWord

/-!
# Bit words: the algebra of `+^` (EasyCrypt `theories/datatypes/BitWord.eca`)

The lemmas `xorw0`, `xorwA`, `xorwC`, `xorwK` of EC's `BitWord`, what its `algebra` uses on
words (EC: `clone import Ring.BoolRing as WRing`), and the uniform distribution's facts that the
conditions of `rnd` ask for.  Names are EasyCrypt's.
-/

namespace GaudisCrypt.EC.BitWord

variable {n : ℤ}

/-- `lemma xorwE w1 w2 i: (w1 +^ w2).[i] = w1.[i] ^^ w2.[i]`. -/
theorem xorwE (w₁ w₂ : word n) (i : Fin n.toNat) :
    (w₁ +^ w₂).get i = xor (w₁.get i) (w₂.get i) := by
  simp [xorw]

/-- `lemma xorw0: right_id zerow (+^)`. -/
@[simp] theorem xorw0 (w : word n) : w +^ zerow = w := by
  apply List.Vector.ext; intro i; simp [xorwE, zerow]

/-- `lemma xorwA: associative (+^)`. -/
theorem xorwA (w₁ w₂ w₃ : word n) : w₁ +^ (w₂ +^ w₃) = w₁ +^ w₂ +^ w₃ := by
  apply List.Vector.ext; intro i; simp [xorwE]

/-- `lemma xorwC: commutative (+^)`. -/
theorem xorwC (w₁ w₂ : word n) : w₁ +^ w₂ = w₂ +^ w₁ := by
  apply List.Vector.ext; intro i; simp [xorwE, Bool.xor_comm]

/-- `lemma xorwK: forall x, x +^ x = zerow`. -/
@[simp] theorem xorwK (w : word n) : w +^ w = zerow := by
  apply List.Vector.ext; intro i; simp [xorwE, zerow]

/-- `zerow` is a left identity (EC: `xorwC`, `xorw0`). -/
@[simp] theorem xor0w (w : word n) : zerow +^ w = w := by rw [xorwC, xorw0]

/-- Adding the same word twice cancels (EC's `algebra`). -/
@[simp] theorem xorwKr (w m : word n) : w +^ m +^ m = w := by
  rw [← xorwA, xorwK, xorw0]

/-- `dunifin` charges every word (EC's `dunifin_fu`), for the conditions of `rnd`. -/
@[simp] theorem dunifin_support : (dunifin : SubProbability (word n)).support = Set.univ :=
  SubProbability.uniform_support

/-- All words have the same probability (EC's `dunifin_funi`), as EC's `rnd` asks. -/
@[simp] theorem mu1_dunifin_eq (x y : word n) :
    (mu1 (dunifin : SubProbability (word n)) x = mu1 dunifin y) = True :=
  eq_true (by unfold mu1; rw [dunifin_funi x y])

end GaudisCrypt.EC.BitWord
