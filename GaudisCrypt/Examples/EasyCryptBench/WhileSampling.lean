import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.PHoareWp
import GaudisCrypt.Logic.PRHL.Coupling

/-!
# Rejection sampling for any distribution (EasyCrypt `theories/distributions/Dexcepted.ec`)

`WhileSampling`: draw from `d` until the test `X` fails; the result is distributed as `d`
conditioned on `¬X` — EC's `d \ X`, with `mu (d \ X) P = mu d (P ∧ ¬X) / mu d ¬X` (`dexceptedE`,
for lossless `d`).  EasyCrypt:

```
module SampleW = {
  proc sample(i : input, test) = {
    var r;
    r <$ dt i;
    r <@ SampleWi.sample(i, r, test);      (* while (test i r) { r <$ dt i; } *)
    return r;
  }
}.

lemma pr_sampleW &m x X P :
  is_lossless (dt x) =>
  Pr[SampleW.sample(x, X) @ &m : P res] = mu (dt x \ X x) P.
proof.
  (* ~45 lines: a case split on whether the loop can terminate, `phoare split` ("TRANSITIVITY
     FOR PHOARE!!"), two nested `seq`s with five probabilities each, `rcondf`, a `call` to
     `pr_sampleWi` — itself ~35 lines: the variant rule `while (…) (if test x r then 1 else 0)
     1 (mu (dt x) (predC (X x)))` and a second case split *)
qed.
```

Here: the invariant `if X r then c else [P r]` with `c = μ(P ∧ ¬X) / μ(¬X)` is a fixed point of
one draw (`draw_inv`: `μ(X)·c + μ(P ∧ ¬X) = c`, since `c·μ(¬X) = μ(P ∧ ¬X)`), so it bounds the
loop from above (`phoare_while_le`) and, with termination (each round exits with probability
`μ(¬X)`), from below (`phoare_while_ge`).  The degenerate case `μ(¬X) = 0` — the loop never
terminates — needs no split: then `c = 0/0 = 0` and the upper bound alone is the answer.
-/

namespace GaudisCrypt.Examples.EasyCryptBench.WhileSampling

open GaudisCrypt

/-- The sample space, the distribution `d` and the test `X` (EC's `dt i` and `test i`, at a fixed
    input `i`). -/
structure Setup where
  t : Type
  [inhabited : Inhabited t]
  d : SubProbability t
  X : t → Bool

@[reducible] instance (S : Setup) : Inhabited S.t := S.inhabited

variable (S : Setup)

/-- EC's `mu d E`: the probability of an event under `d`. -/
noncomputable def mass (E : S.t → Prop) : ENNReal := S.d.expected fun a => indicatorE (E a)

/-- The target probability `μ(P ∧ ¬X) / μ(¬X)` — EC's `mu (d \ X) P`. -/
noncomputable def condProb (P : S.t → Prop) : ENNReal :=
  mass S (fun a => P a ∧ S.X a = false) / mass S (fun a => S.X a = false)

theorem expected_const_mul' {α : Type*} (μ : SubProbability α) (c : ENNReal) (f : α → ENNReal) :
    μ.expected (fun a => c * f a) = c * μ.expected f := by
  letI : MeasurableSpace α := ⊤
  exact MeasureTheory.lintegral_const_mul c measurable_from_top

/-- `d` is lossless: a draw always succeeds (EC's `is_lossless (dt x)`). -/
def Lossless : Prop := S.d.expected (fun _ => 1) = 1

/-- `μ(X) + μ(¬X) = 1` for a lossless `d`. -/
theorem mass_add_compl (hll : Lossless S) :
    mass S (fun a => S.X a = true) + mass S (fun a => S.X a = false) = 1 := by
  rw [mass, mass, ← SubProbability.expected_add, ← hll]
  exact SubProbability.expected_congr _ fun a => by cases S.X a <;> simp

theorem mass_le_one (hll : Lossless S) (E : S.t → Prop) : mass S E ≤ 1 := by
  rw [← hll]
  exact SubProbability.expected_mono_pt _ fun a => indicatorE_le_one _

theorem condProb_le_one (P : S.t → Prop) : condProb S P ≤ 1 := by
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact SubProbability.expected_mono_pt _ fun a => by
    by_cases h : S.X a = false <;> by_cases hp : P a <;> simp [indicatorE, h, hp]

/-- If the loop can never exit (`μ(¬X) = 0`), the target is `0`: `μ(P ∧ ¬X) = 0` too, and
    `0 / 0 = 0` in `ENNReal`. -/
theorem mass_and_eq_zero (P : S.t → Prop) (h0 : mass S (fun a => S.X a = false) = 0) :
    mass S (fun a => P a ∧ S.X a = false) = 0 := by
  refine le_antisymm (h0 ▸ SubProbability.expected_mono_pt _ fun a => ?_) bot_le
  by_cases h : S.X a = false <;> by_cases hp : P a <;> simp [indicatorE, h, hp]

theorem condProb_eq_zero (P : S.t → Prop) (h0 : mass S (fun a => S.X a = false) = 0) :
    condProb S P = 0 := by
  simp [condProb, mass_and_eq_zero S P h0, h0]

/-- **One draw keeps the invariant**: `if X r then c else [P r]` averages to `c` again. -/
theorem draw_inv (hll : Lossless S) (P : S.t → Prop) :
    S.d.expected (fun r => if S.X r = true then condProb S P else indicatorE (P r)) = condProb S P := by
  -- the draw splits into `μ(X) · c + μ(P ∧ ¬X)`
  have hsplit : S.d.expected (fun r => if S.X r = true then condProb S P else indicatorE (P r))
      = condProb S P * mass S (fun a => S.X a = true) + mass S (fun a => P a ∧ S.X a = false) := by
    rw [mass, mass, ← expected_const_mul', ← SubProbability.expected_add]
    exact SubProbability.expected_congr _ fun a => by
      cases h : S.X a <;> by_cases hp : P a <;> simp [indicatorE, hp]
  rw [hsplit]
  -- and `c · μ(¬X) = μ(P ∧ ¬X)`, so it is `c · (μ(X) + μ(¬X)) = c`
  by_cases h0 : mass S (fun a => S.X a = false) = 0
  · simp [condProb_eq_zero S P h0, mass_and_eq_zero S P h0]
  · have htop : mass S (fun a => S.X a = false) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (mass_le_one S hll _)
    have hc : condProb S P * mass S (fun a => S.X a = false) = mass S (fun a => P a ∧ S.X a = false) :=
      ENNReal.div_mul_cancel h0 htop
    rw [← hc, ← mul_add, mass_add_compl S hll, mul_one]

moduletype SamplerT {
  proc sample () -> S.t;
}

module SampleW : (SamplerT S) {
  proc sample () : S.t {
    var r : S.t;
    r <$ S.d;
    while (S.X $r) {
      r <$ S.d;
    }
    return $r
  };
}

theorem sampleW_le (hll : Lossless S) (P : S.t → Prop) :
    phoare[ (SampleW.sample S) : True ==> P §res ] ≤ (condProb S P) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_le (if S.X §r = true then condProb S P else indicatorE (P §r))
  case body =>
    phoare_wp 1
    phoare_skip
    intro r hr
    rw [draw_inv S hll P]
    simp [hr]
  case exit =>
    intro r hr
    simp [hr]
  phoare_wp 2
  phoare_skip
  exact fun _ => (draw_inv S hll P).le

theorem sampleW_ge (hll : Lossless S) (P : S.t → Prop) :
    phoare[ (SampleW.sample S) : True ==> P §res ] ≥ (condProb S P) := by
  -- if the loop can never exit, the target is `0`
  by_cases h0 : mass S (fun a => S.X a = false) = 0
  · intro _ _ _
    simp [condProb_eq_zero S P h0]
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_ge (if S.X §r = true then condProb S P else indicatorE (P §r))
    using mass S (fun a => S.X a = false)
  case body =>
    phoare_wp 1
    phoare_skip
    intro r hr
    rw [draw_inv S hll P]
    simp [hr]
  case exit =>
    intro r hr
    simp [hr]
  case lossless =>
    phoare_wp 1
    phoare_skip
    exact fun _ _ => hll
  case progress =>
    -- each round exits with probability `μ(¬X)`
    phoare_wp 1
    phoare_skip
    exact fun _ _ => le_rfl
  case I_le_one =>
    intro r
    split_ifs
    · exact condProb_le_one S P
    · exact indicatorE_le_one _
  case ε_ne_zero => exact h0
  case ε_le_one => exact mass_le_one S hll _
  phoare_wp 2
  phoare_skip
  exact fun _ => (draw_inv S hll P).ge

/-- **EC's `pr_sampleW`**, as a judgment: the loop samples from `d` conditioned on `¬X`. -/
theorem sampleW_eq (hll : Lossless S) (P : S.t → Prop) :
    phoare[ (SampleW.sample S) : True ==> P §res ] = (condProb S P) :=
  phoareProc_eq_of_le_ge (sampleW_le S hll P) (sampleW_ge S hll P)

/-- **EC's `pr_sampleW`**, as EC states it: `Pr[SampleW.sample() @ &m : P res] = mu (d \ X) P`. -/
theorem pr_sampleW (hll : Lossless S) (P : S.t → Prop) (σ : VariableAssignment) :
    ((Module.Proc.procedure (SampleW.sample S)).Pr () σ (fun r _ => P r) : ENNReal) = condProb S P :=
  Procedure.Pr_of_phoareProc (sampleW_eq S hll P) (args := ()) (σ := σ) trivial

end GaudisCrypt.Examples.EasyCryptBench.WhileSampling
