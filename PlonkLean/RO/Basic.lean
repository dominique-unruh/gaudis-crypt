import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Order.FixedPoints
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.OmegaCompletePartialOrder

import PlonkLean.Misc
import PlonkLean.Language.Semantics
import PlonkLean.WeakestPreconditions
import PlonkLean.Language.Lens
import PlonkLean.LensRange
import PlonkLean.ProgramRange
import PlonkLean.Unsorted

/-!
# Random oracle primitives

The basic actors of the random oracle framework: the RO state lens, the
two query primitives (`lazy_query` and `random_oracle_query`), and their
respective initialisation routines (`lazy_init` and `random_oracle_init`).

`convert` and everything related to converting one to the other lives in
`PlonkLean.RO.Transfer`. The scratch state variables used by the
adversary-driven oracle loops live in `PlonkLean.RO.OracleLoop`.
-/

opaque input : Type
opaque output : Type
instance : Countable state := sorry
instance : Inhabited input := sorry
instance : Fintype input := sorry
instance : Inhabited output := sorry
instance : Fintype output := sorry
noncomputable instance : DecidableEq output := Classical.decEq output

axiom random_oracle_state : Variable (input -> Option output)

instance [Fintype a] [Fintype b] : Fintype (a → b) := sorry
instance : DecidableEq input := sorry

/-- Sample the entire `input → output` function space uniformly and store it
    in the random oracle (as the eager initialisation). -/
noncomputable def random_oracle_init := do
  let (h : input -> output) <- Program.uniform
  Program.set random_oracle_state (fun x => some (h x))

/-- Initialise the random oracle with no cached entries (lazy initialisation). -/
noncomputable def lazy_init : Program state Unit :=
  Program.set random_oracle_state (fun _ => none)

/-- Lazy random-oracle query: return the cached output if present, otherwise
    sample uniformly and cache. -/
noncomputable def lazy_query (inp : input) : Program state output := do
  let h <- Program.get random_oracle_state
  let cached := h inp
  match cached with
  | some x => return x
  | none =>
    let value <- Program.uniform
    Program.set random_oracle_state (fun x => if x=inp then some value else h x)
    return value

/-- Eager random-oracle query: read the (pre-sampled) value at `inp`. -/
noncomputable def random_oracle_query (inp : input) : Program state output := do
  let h <- Program.get random_oracle_state
  return (h inp).getD default

/-- `lazy_query` only reads and writes `random_oracle_state`. -/
theorem lazy_query_inRange_ro (inp : input) :
    (lazy_query inp).inRange random_oracle_state.range := by
  refine Program.inRange_bind (Program.inRange_get _) ?_
  intro h
  cases h inp with
  | some x => exact Program.inRange_pure _ _
  | none =>
    refine Program.inRange_bind ?_ ?_
    · exact Program.inRange_mono Program.inRange_uniform bot_le
    · intro value
      refine Program.inRange_bind (Program.inRange_set _ _) ?_
      intro _
      exact Program.inRange_pure _ _
