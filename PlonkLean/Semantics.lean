/-

Put here:

- General monad stuff
- ...


-/

import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Uniform


/-!
# Discrete subprobability monad
-/

def SubProbability (a : Type) := {mu: @MeasureTheory.Measure a ⊤ // mu ⊤ <= 1}

noncomputable
instance : Monad SubProbability where
  pure a :=
    ⟨@MeasureTheory.Measure.dirac _ ⊤ a, by simp⟩
  bind x f :=
    let ⟨mu, h⟩ := x
    ⟨MeasureTheory.Measure.bind mu (fun a => (f a).1), by
        simp only [Set.top_eq_univ]
        rw [MeasureTheory.Measure.bind_apply MeasurableSet.univ measurable_from_top.aemeasurable]
        calc ∫⁻ a, (f a).1 ⊤ ∂mu
            ≤ ∫⁻ _, 1 ∂mu := MeasureTheory.lintegral_mono (fun a => (f a).2)
          _ = mu ⊤ := MeasureTheory.lintegral_one
          _ ≤ 1 := h⟩

noncomputable
def toSubProbability (p : PMF α) : SubProbability α :=
  ⟨@PMF.toMeasure _ ⊤ p, by
    haveI := @PMF.toMeasure.isProbabilityMeasure _ ⊤ p
    exact le_of_eq MeasureTheory.IsProbabilityMeasure.measure_univ⟩
