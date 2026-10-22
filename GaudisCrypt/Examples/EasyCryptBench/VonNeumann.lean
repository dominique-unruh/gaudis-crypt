import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.PHoareWp

/-!
# Von Neumann's trick (EasyCrypt `examples/vonNeumann.eca`)

A fair coin from a biased coin of unknown bias `p`: flip twice until the flips differ, and return
the first.  EasyCrypt's `Simulate_is_Fair` (abridged):

```
module Simulate = {
  proc sample(): bool = {
    var b, b';
    b  <- true;
    b' <- true;
    while (b = b') {
      b  <$ dbiased;
      b' <$ dbiased;
    }
    return b;
  }
}.

lemma Simulate_is_Fair (x:bool) &m:
  Pr[Simulate.sample() @ &m: res = x] = Pr[Fair.sample() @ &m: res = x].
proof.
  (* … via SamplePair, then: *)
byphoare (_: true ==> res = x)=> //; proc; sp.
conseq (: _: =(if b = b' then mu dvn (pred1 x \o fst) else b2r (b = x)))=> //.
conseq (: true ==> _).
while true (b2i (b = b')) 1 (2%r * p * (1%r - p))=> />.
+ by move=> /#.
+ move=> ih.
  seq 1: (b = x) (mu1 dbiased x) (mu1 dbiased (!x) + mu1 dbiased x * mu dvn (pred1 x \o fst))
                 (mu1 dbiased (!x)) (mu1 dbiased (!x) * mu dvn (pred1 x \o fst))=> //.
  + by rnd (pred1 x); auto=> />; rewrite dbiased.
  + seq 1: (b' = !x) (mu1 dbiased (!x)) 1%r (mu1 dbiased x) (mu dvn (pred1 x \o fst)) (b = x)=> //.
    + by auto.
    + by rnd (pred1 (!x)); auto.
    + by conseq ih=> />; rewrite -negbDR.
    + by rnd (pred1 x); auto=> /#.
    by conseq ih=> /> &0 /negbDR /=.
  + by rnd (pred1 (!x)); auto=> /#.
  + seq 1: (b' = x) _ 0%r (mu1 dbiased (!x)) (mu dvn (pred1 x \o fst)) (b <> x)=> //.
    + by auto.
    + by conseq ih=> /> &0 ->.
    + by rnd (pred1 (!x)); auto=> /#.
    by conseq ih=> /> &0 /negbDR -> /negbDR ->.
  move=> {ih} _ -> /=; rewrite !vnE /svn /(\o)/ pred1 /= /b2i /=.
  by move: x=> [] /=; rewrite !dbiased1E /#.
+ by auto=> />; rewrite dbiased_ll.
split => //= [|z]; first by smt w=(in01_p).
conseq (_: true ==> b <> b'); first by move=> /#.
seq 1: b p (1%r - p) (1%r - p) p=> //.
+ by rnd; skip=> />; rewrite dbiasedE.
+ by rnd; skip=> />; rewrite dbiasedE.
+ by rnd; skip=> />; rewrite dbiasedE.
+ by rnd; skip=> /> &hr _; rewrite dbiasedE.
smt(in01_p).
qed.
```

Here: one invariant, `if b = b' then 1/2 else indicatorE (b = x)`, which one round leaves
unchanged — `p²/2 + p(1−p)·[true = x] + (1−p)p·[false = x] + (1−p)²/2 = 1/2` — so it bounds the
loop from above (`phoare_while_le`) and, with termination (`ε = 2p(1−p)`, the chance a round's
flips differ), from below (`phoare_while_ge`).
-/

namespace GaudisCrypt.Examples.EasyCryptBench.VonNeumann

open GaudisCrypt

/-- A coin of bias `p ∈ (0, 1)`. -/
structure Bias where
  p : NNReal
  pos : 0 < p
  lt_one : p < 1

theorem Bias.le_one (B : Bias) : B.p ≤ 1 := B.lt_one.le

theorem add_compl_one (p : NNReal) (hp : p ≤ 1) :
    (p : ENNReal) + ((1 - p : NNReal) : ENNReal) = 1 := by
  rw [← ENNReal.coe_add, add_tsub_cancel_of_le hp, ENNReal.coe_one]

/-- EC's `dbiased`: `true` with probability `p`. -/
noncomputable def biased (p : NNReal) (hp : p ≤ 1) : SubProbability Bool :=
  toSubProbability
    (PMF.ofFintype (fun b => if b then (p : ENNReal) else ((1 - p : NNReal) : ENNReal))
      (by simpa [Fintype.sum_bool] using add_compl_one p hp))

theorem biased_expected (p : NNReal) (hp : p ≤ 1) (f : Bool → ENNReal) :
    (biased p hp).expected f = p * f true + ((1 - p : NNReal) : ENNReal) * f false := by
  letI : MeasurableSpace Bool := ⊤
  change ∫⁻ x, f x ∂(PMF.ofFintype _ _).toMeasure = _
  rw [MeasureTheory.lintegral_fintype]
  simp [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.ofFintype_apply,
    mul_comm]

/-- `p²/2 + pq + q²/2 = (p + q)²/2 = 1/2` when `p + q = 1`: one round of the trick, from a state
    where the two flips agreed, keeps the invariant at `1/2`. -/
theorem half_square (a q : ENNReal) (h : a + q = 1) :
    a * (a * (1 / 2) + q) + q * (q * (1 / 2)) = 1 / 2 := by
  calc _ = a * (a * (1 / 2) + q * (1 / 2 + 1 / 2)) + q * (q * (1 / 2)) := by
        rw [ENNReal.add_halves, mul_one]
    _ = (a + q) * (a + q) * (1 / 2) := by ring
    _ = 1 / 2 := by rw [h, one_mul, one_mul]

theorem Bias.add_compl (B : Bias) : (B.p : ENNReal) + ((1 - B.p : NNReal) : ENNReal) = 1 :=
  add_compl_one B.p B.le_one

variable (B : Bias)

/-- **One round keeps the invariant**: from a state where the flips agreed, two fresh flips and
    the invariant `if b = b' then 1/2 else [b = x]` average to `1/2` again. -/
theorem round_eq (x : Bool) :
    ((biased B.p B.le_one).expected fun a => (biased B.p B.le_one).expected fun a' =>
      if a = a' then (1 / 2 : ENNReal) else indicatorE (a = x)) = 1 / 2 := by
  simp only [biased_expected]
  have hpq := B.add_compl
  -- evaluate the coin outcomes and the indicators, then it is `half_square`
  cases x <;> simp only [if_true, Bool.true_eq_false, Bool.false_eq_true, ite_false,
    indicatorE_true, indicatorE_false, mul_one, mul_zero, add_zero, zero_add]
  · calc _ = ((1 - B.p : NNReal) : ENNReal) * (((1 - B.p : NNReal) : ENNReal) * (1 / 2) + B.p)
          + B.p * (B.p * (1 / 2)) := by ring
      _ = 1 / 2 := half_square _ _ ((add_comm _ _).trans hpq)
  · exact half_square _ _ hpq

moduletype SimulateT {
  proc sample () -> Bool;
}

module Simulate : SimulateT {
  proc sample () : Bool {
    var b : Bool, b' : Bool;
    b <- true;
    b' <- true;
    while ($b == $b') {
      b <$ biased B.p B.le_one;
      b' <$ biased B.p B.le_one;
    }
    return $b
  };
}

theorem simulate_le (x : Bool) :
    phoare[ (Simulate.sample B) : True ==> §res = x ] ≤ (1 / 2) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_le (if §b = §b' then (1 / 2 : ENNReal) else indicatorE (§b = x))
  case body =>
    phoare_wp 2
    phoare_skip
    intro b b' hbb
    simp only [beq_iff_eq] at hbb
    rw [if_pos hbb, round_eq]
  case exit =>
    intro b b' h
    simp_all
  phoare_wp 3
  phoare_skip
  simp

theorem simulate_ge (x : Bool) :
    phoare[ (Simulate.sample B) : True ==> §res = x ] ≥ (1 / 2) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_ge (if §b = §b' then (1 / 2 : ENNReal) else indicatorE (§b = x))
    using 2 * B.p * ((1 - B.p : NNReal) : ENNReal)
  case body =>
    phoare_wp 2
    phoare_skip
    intro b b' hbb
    simp only [beq_iff_eq] at hbb
    rw [if_pos hbb, round_eq]
  case exit =>
    intro b b' h
    simp_all
  case lossless =>
    phoare_wp 2
    phoare_skip
    intro _ _ _
    simp only [biased_expected, mul_one, B.add_compl]
  case progress =>
    -- the two flips differ with probability `pq + qp = 2pq`
    phoare_wp 2
    phoare_skip
    intro _ _ _
    simp only [biased_expected]
    simp only [beq_self_eq_true, Bool.true_eq_false, indicatorE_false, Bool.beq_eq_decide_eq,
      decide_eq_false_iff_not, Bool.false_eq_true, not_false_eq_true, indicatorE_true, mul_zero,
      mul_one, zero_add, add_zero]
    exact le_of_eq (by ring)
  case ε_ne_zero =>
    have hq : (0 : NNReal) < 1 - B.p := tsub_pos_of_lt B.lt_one
    exact mul_ne_zero (mul_ne_zero two_ne_zero (ENNReal.coe_ne_zero.mpr B.pos.ne'))
      (ENNReal.coe_ne_zero.mpr hq.ne')
  case ε_le_one =>
    -- `2pq ≤ p² + 2pq + q² = (p + q)² = 1`
    calc 2 * (B.p : ENNReal) * ((1 - B.p : NNReal) : ENNReal)
        ≤ B.p * B.p + (2 * B.p * ((1 - B.p : NNReal) : ENNReal)
            + ((1 - B.p : NNReal) : ENNReal) * ((1 - B.p : NNReal) : ENNReal)) :=
          le_add_left le_self_add
      _ = (B.p + ((1 - B.p : NNReal) : ENNReal)) * (B.p + ((1 - B.p : NNReal) : ENNReal)) := by
          ring
      _ = 1 := by rw [B.add_compl, one_mul]
  phoare_wp 3
  phoare_skip
  simp

/-- The simulated coin is fair. -/
theorem simulate_half (x : Bool) :
    phoare[ (Simulate.sample B) : True ==> §res = x ] = (1 / 2) :=
  phoareProc_eq_of_le_ge (simulate_le B x) (simulate_ge B x)

-- EC's `Fair`: a fair coin, directly
module Fair : SimulateT {
  proc sample () : Bool {
    var b : Bool;
    b <$ SubProbability.uniform;
    return $b
  };
}

theorem fair_half (x : Bool) : phoare[ Fair.sample : True ==> §res = x ] = (1 / 2) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 3
  phoare_skip
  cases x <;> simp

/-- EC's `Simulate_is_Fair`: the two samplers give every outcome the same probability (both
    `1/2`, by `byphoare` on `simulate_half` and `fair_half`). -/
theorem simulate_is_fair (x : Bool) (σ : VariableAssignment) :
    (Simulate.sample B).procedure.Pr () σ (fun r _ => r = x)
      = (Module.Proc.procedure Fair.sample).Pr () σ (fun r _ => r = x) := by
  have h₁ := Procedure.Pr_of_phoareProc (simulate_half B x) (args := ()) (σ := σ) trivial
  have h₂ := Procedure.Pr_of_phoareProc (fair_half x) (args := ()) (σ := σ) trivial
  exact ENNReal.coe_inj.mp (h₁.trans h₂.symm)

end GaudisCrypt.Examples.EasyCryptBench.VonNeumann
