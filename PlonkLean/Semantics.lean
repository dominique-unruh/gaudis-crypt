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

noncomputable
def SubProbability.uniform [h : Fintype α] [h : Nonempty α] : SubProbability α :=
  toSubProbability (PMF.uniformOfFintype α)

def SubProbability.ofEvent (μ : SubProbability a) e := μ.1 e

instance : FunLike (SubProbability a) a ENNReal where
  coe μ x := μ.ofEvent {x}
  coe_injective' μ ν h := sorry

/-!

# Stateful programs

-/

@[reducible]
def Program (state : Type) := StateT state SubProbability

noncomputable
def SubProbability.toProgram (p: SubProbability a) : Program s a := StateT.lift p

noncomputable
def PMF.toProgram {st α} (p : PMF α) : Program st α := StateT.lift (toSubProbability p)

noncomputable
def Program.uniform [h : Fintype α] [h : Nonempty α] : Program s α :=
  SubProbability.uniform.toProgram

def Program.finalProb (prog : Program s a) (st : s) (X : Set a) : NNReal :=
  ((prog st).ofEvent (X ×ˢ ⊤)).toNNReal

def Program.finalProb1 (prog : Program s a) (st : s) (x : a) : NNReal :=
  prog.finalProb st {x}
