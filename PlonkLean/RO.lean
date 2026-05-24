import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Order.FixedPoints
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.OmegaCompletePartialOrder

import PlonkLean.Misc
import PlonkLean.Semantics
import PlonkLean.WeakestPreconditions
import PlonkLean.Lens
import PlonkLean.Unsorted

------ Oracles

opaque input : Type
opaque output : Type
instance : Countable state := sorry
instance : Inhabited input := sorry
instance : Fintype input := sorry
instance : Inhabited output := sorry
instance : Fintype output := sorry


axiom random_oracle_state : Variable (input -> Option output)

instance [Fintype a] [Fintype b] : Fintype (a → b) := sorry
instance : DecidableEq input := sorry

/- samples from the entire `input -> output` function space -/
noncomputable def random_oracle_init := do
  let (h : input -> output) <- Program.uniform
  Program.set random_oracle_state (fun x => some (h x))

/- initializes the state with `none` for all inputs -/
noncomputable def lazy_init : Program state Unit := Program.set random_oracle_state (fun _ => none)

/- fills all the holes with output of a uniformly sampled function -/
noncomputable def convert : Program state Unit := do
  let h <- Program.get random_oracle_state
  let (y : input -> output) <- Program.uniform
  Program.set random_oracle_state (fun x => some ((h x).getD (y x)))

noncomputable def lazy_init_convert : Program state Unit := do
  lazy_init
  convert


private theorem program_ext {s a : Type} (p q : Program s a)
    (h : ∀ f, p.wp f = q.wp f) : p = q := by
  funext st
  apply Subtype.ext
  letI : MeasurableSpace (a × s) := ⊤
  apply MeasureTheory.Measure.ext
  intro A hA
  have hf := congrFun (h (A.indicator 1)) st
  simp only [Program.wp, SubProbability.expected] at hf
  rwa [MeasureTheory.lintegral_indicator_one hA,
       MeasureTheory.lintegral_indicator_one hA] at hf

theorem claim_1 :
   lazy_init_convert = random_oracle_init := by
   apply program_ext
   intro f
   simp [lazy_init_convert, lazy_init, convert, random_oracle_init,
         wp_bind, wp_set, wp_get, wp_uniform,
         random_oracle_state.set_get, random_oracle_state.set_set,
         Option.getD_none]
