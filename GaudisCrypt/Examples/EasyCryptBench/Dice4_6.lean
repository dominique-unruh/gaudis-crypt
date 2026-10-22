import GaudisCrypt.Examples.EasyCryptBench.WhileSampling

/-!
# A d4 from a d6 (EasyCrypt `examples/Dice4_6.ec`)

Roll a six-sided die until it shows 1–4.  EasyCrypt:

```
module D6 = {
  proc sample () : int = {
    var r <- 5;
    while (5 <= r) r <$ [1..6];
    return r;
  }
}.

lemma prD6 : forall k &m, Pr[D6.sample() @ &m : res = k] =
      if 1 <= k <= 4 then 1%r/4%r else 0%r.
proof.
move=> k &m.
rewrite -(: Pr[D4.sample() @ &m: res = k] = Pr[D6.sample() @ &m: res = k]).
+ by byequiv (D4_D6 (fun x=> x) (fun x=> x) _ _).
exact/(@prD4 k &m).
qed.
```

— via `D4_D6`, an `equiv` against a direct d4 (`r <$ [1..4]`), proved by `transitivity` through
the abstract `WhileSamplingFixedTest` clone (`D4_Sample`, `D6_Sample`, `sampleE_sampleWi`), about
40 lines with interval arithmetic by `iotaS`.

Here: an instance of `WhileSampling` (`t = ℤ`, `d` uniform on `[1..6]`, test `5 ≤ r`).  The
loop is closed by the general fixed-point fact `draw_inv`, and what is left is the concrete
conditional probability `μ(r = k ∧ r < 5) / μ(r < 5)`.
-/

namespace GaudisCrypt.Examples.EasyCryptBench.Dice4_6

open GaudisCrypt GaudisCrypt.Examples.EasyCryptBench.WhileSampling

/-- EC's `[1..6]`. -/
noncomputable def d6 : SubProbability ℤ :=
  SubProbability.uniformOfFinset (Finset.Icc 1 6) ⟨1, by simp⟩

/-- The d6 with the test `5 ≤ r`, as a `WhileSampling` setup. -/
noncomputable def Dice : Setup where
  t := ℤ
  d := d6
  X r := decide (5 ≤ r)

moduletype DieT {
  proc sample () -> ℤ;
}

module D6 : DieT {
  proc sample () : ℤ {
    var r : ℤ;
    r <- 5;
    while (5 <= $r) {
      r <$ d6;
    }
    return $r
  };
}

theorem dice_lossless : Lossless Dice := by
  change d6.expected (fun _ => 1) = 1
  rw [d6, uniformOfFinset_expected, Finset.sum_const, nsmul_eq_mul]
  exact ENNReal.mul_div_cancel' (by simp) (by simp)

/-- `μ(E)` under the d6, as a sum over its six faces. -/
theorem dice_mass (E : ℤ → Prop) :
    mass Dice E = ∑ x ∈ Finset.Icc (1 : ℤ) 6, indicatorE (E x) / 6 := by
  change d6.expected _ = _
  rw [d6, uniformOfFinset_expected]
  simp

set_option linter.flexible false in
/-- `μ(r < 5) = 4/6`: faces 1–4. -/
theorem dice_mass_low :
    ∑ x ∈ Finset.Icc (1 : ℤ) 6, indicatorE (Dice.X x = false) / 6 = 4 / 6 := by
  rw [show Finset.Icc (1 : ℤ) 6 = {1, 2, 3, 4, 5, 6} by decide]
  simp [Dice, indicatorE]
  rw [div_eq_mul_inv]
  ring

set_option linter.flexible false in
/-- The conditional probability `μ(r = k ∧ r < 5) / μ(r < 5)`: `1/4` on `1..4`. -/
theorem dice_cond (k : ℤ) : condProb Dice (· = k) = if 1 ≤ k ∧ k ≤ 4 then 1 / 4 else 0 := by
  rw [condProb, dice_mass, dice_mass]
  -- the numerator: only the face `k` counts, and only if it is below 5
  have hnum : ∑ x ∈ Finset.Icc (1 : ℤ) 6, indicatorE (x = k ∧ Dice.X x = false) / 6
      = if 1 ≤ k ∧ k ≤ 4 then 1 / 6 else 0 := by
    have hpt : ∀ x : ℤ, indicatorE (x = k ∧ Dice.X x = false) / 6
        = if x = k then indicatorE (Dice.X k = false) / 6 else 0 := fun x => by
      by_cases h : x = k
      · subst h; simp
      · simp [h, indicatorE]
    simp only [hpt, Finset.sum_ite_eq', Finset.mem_Icc]
    by_cases h1 : 1 ≤ k ∧ k ≤ 4
    · have h2 : (1 ≤ k ∧ k ≤ 6) := ⟨h1.1, by omega⟩
      have h3 : Dice.X k = false := by simp [Dice]; omega
      simp [h1, h2, h3]
    · by_cases h2 : 1 ≤ k ∧ k ≤ 6
      · have h3 : Dice.X k = true := by simp [Dice]; omega
        have h4 : ¬ k ≤ 4 := by omega
        simp [h2, h3, h4]
      · simp [h1, h2]
  change (∑ x ∈ Finset.Icc (1 : ℤ) 6, indicatorE (x = k ∧ Dice.X x = false) / 6)
    / (∑ x ∈ Finset.Icc (1 : ℤ) 6, indicatorE (Dice.X x = false) / 6) = _
  rw [hnum, dice_mass_low]
  split_ifs <;> simp [ENNReal.div_eq_inv_mul]
  -- `(6⁻¹ · 4)⁻¹ · 6⁻¹ = 4⁻¹`
  rw [ENNReal.mul_inv (by simp) (by simp), inv_inv, mul_comm (6 : ENNReal), mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

theorem d6_le (k : ℤ) :
    phoare[ D6.sample : True ==> §res = k ] ≤ (condProb Dice (· = k)) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_le (if decide (5 ≤ §r) = true then condProb Dice (· = k) else indicatorE (§r = k))
  case body =>
    phoare_wp 1
    phoare_skip
    intro r hr
    simp only [hr, if_true]
    exact (draw_inv Dice dice_lossless (· = k)).le
  case exit =>
    intro r hr
    simp [hr]
  phoare_wp 2
  phoare_skip
  simp

theorem d6_ge (k : ℤ) :
    phoare[ D6.sample : True ==> §res = k ] ≥ (condProb Dice (· = k)) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_ge (if decide (5 ≤ §r) = true then condProb Dice (· = k) else indicatorE (§r = k))
    using mass Dice (fun a => Dice.X a = false)
  case body =>
    phoare_wp 1
    phoare_skip
    intro r hr
    simp only [hr, if_true]
    exact (draw_inv Dice dice_lossless (· = k)).ge
  case exit =>
    intro r hr
    simp [hr]
  case lossless =>
    phoare_wp 1
    phoare_skip
    exact fun _ _ => dice_lossless
  case progress =>
    phoare_wp 1
    phoare_skip
    exact fun _ _ => le_rfl
  case I_le_one =>
    intro r
    split_ifs
    · exact condProb_le_one Dice _
    · exact indicatorE_le_one _
  case ε_ne_zero =>
    rw [dice_mass, dice_mass_low]
    simp
  case ε_le_one => exact mass_le_one Dice dice_lossless _
  phoare_wp 2
  phoare_skip
  simp

/-- **EC's `prD6`**: the d6-with-rerolls is a fair d4. -/
theorem prD6 (k : ℤ) (σ : VariableAssignment) :
    ((Module.Proc.procedure D6.sample).Pr () σ (fun r _ => r = k) : ENNReal)
      = if 1 ≤ k ∧ k ≤ 4 then 1 / 4 else 0 := by
  rw [← dice_cond]
  exact Procedure.Pr_of_phoareProc (phoareProc_eq_of_le_ge (d6_le k) (d6_ge k))
    (args := ()) (σ := σ) trivial

end GaudisCrypt.Examples.EasyCryptBench.Dice4_6
