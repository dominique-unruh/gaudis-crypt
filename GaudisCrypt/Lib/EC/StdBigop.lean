import GaudisCrypt.Lib.EC.Distr

/-!
# EasyCrypt's big operators on bounds (`theories/algebra/StdBigop`)

The facts EC's `smt()` uses on the bounds of `fel` and `seq`: a sum over EC's `range 0 n` (here
`Finset.Ico (0 : ℤ) n`) of a constant, the same sum over `ℕ`, and a real bound `n%r * mu1 d v`
as an `ENNReal` (`ENNReal.ofReal`).  None needs `0 ≤ n`: for a negative `n` both sides vanish.
-/

namespace GaudisCrypt.EC

variable {α : Type}

/-- `big predT (fun _ => c) (range 0 n) = n * c`. -/
theorem sum_Ico_const (n : ℤ) (c : ENNReal) :
    ∑ _i ∈ Finset.Ico (0 : ℤ) n, c = (n.toNat : ENNReal) * c := by
  simp [Finset.sum_const, Int.card_Ico, nsmul_eq_mul]

/-- A sum over EC's `range 0 n` of a function of `i`, as a sum over `ℕ`. -/
theorem sum_Ico_toNat (n : ℕ) (f : ℕ → ENNReal) :
    ∑ i ∈ Finset.Ico (0 : ℤ) n, f i.toNat = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, Nat.cast_succ,
      ← Finset.insert_Ico_right_eq_Ico_add_one (Int.natCast_nonneg k),
      Finset.sum_insert (by simp), add_comm, Int.toNat_natCast]

/-- `n%r * mu1 d v`, the real bound, as an `ENNReal`: `n` times the mass of `v`. -/
theorem ofReal_intCast_mul_mu1 (d : SubProbability α) (v : α) (n : ℤ) :
    ENNReal.ofReal ((n : ℝ) * mu1 d v) = (n.toNat : ENNReal) * d.1 {v} := by
  rcases le_or_gt 0 n with hn | hn
  · rw [ENNReal.ofReal_mul (by exact_mod_cast hn), mu1, ENNReal.ofReal_toReal (mu_ne_top d v)]
    congr 1
    rw [show (n : ℝ) = ((n.toNat : ℕ) : ℝ) by exact_mod_cast (Int.toNat_of_nonneg hn).symm,
      ENNReal.ofReal_natCast]
  · have : (n : ℝ) * mu1 d v ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hn.le) ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_of_nonpos this, Int.toNat_of_nonpos hn.le]
    simp

end GaudisCrypt.EC
