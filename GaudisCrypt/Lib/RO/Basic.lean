import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Order.FixedPoints
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.OmegaCompletePartialOrder

import GaudisCrypt.Misc
import GaudisCrypt.Language.Semantics
import GaudisCrypt.WeakestPreconditions
import GaudisCrypt.Language.Lens
import GaudisCrypt.Language.Footprint
import GaudisCrypt.ProbProgramRange

open GaudisCrypt
open GaudisCrypt

/-- The ambient state of the development. (Moved here from the former scratch
    `Unsorted.lean` so that the crypto layer doesn't depend on that file.) -/
structure state where
  x : Nat
  y : Nat
  z : String

/-- A `Variable` is a lens into the ambient `state`. -/
abbrev Variable a := Lens a state

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

-- Removed this because there's Pi.instFintype, which just needs an extra DecidableEq
-- instance [Fintype a] [Fintype b] : Fintype (a → b) := sorry
instance : DecidableEq input := sorry

/-- Sample the entire `input → output` function space uniformly and store it
    in the random oracle (as the eager initialisation). -/
noncomputable def random_oracle_init := do
  let (h : input -> output) <- ProgramDenotation.uniform
  ProgramDenotation.set random_oracle_state (fun x => some (h x))

/-- Initialise the random oracle with no cached entries (lazy initialisation). -/
noncomputable def lazy_init : ProgramDenotation state Unit :=
  ProgramDenotation.set random_oracle_state (fun _ => none)

/-- Lazy random-oracle query: return the cached output if present, otherwise
    sample uniformly and cache. -/
noncomputable def lazy_query (inp : input) : ProgramDenotation state output := do
  let h <- ProgramDenotation.get random_oracle_state
  let cached := h inp
  match cached with
  | some x => return x
  | none =>
    let value <- ProgramDenotation.uniform
    ProgramDenotation.set random_oracle_state (fun x => if x=inp then some value else h x)
    return value

/-- Eager random-oracle query: read the (pre-sampled) value at `inp`. -/
noncomputable def random_oracle_query (inp : input) : ProgramDenotation state output := do
  let h <- ProgramDenotation.get random_oracle_state
  return (h inp).getD default


/-- `lazy_query`'s **probabilistic** footprint lies in `random_oracle_state.footprint` — the prob
    analogue of `lazy_query_inRange_ro`, for the countability-free transfer migration. -/
theorem lazy_query_inFootprint_ro (inp : input) :
    (lazy_query inp).inFootprint random_oracle_state.footprint := by
  refine ProgramDenotation.inFootprint_bind (ProgramDenotation.inFootprint_get _) ?_
  intro h
  cases h inp with
  | some x => exact ProgramDenotation.inFootprint_pure _ _
  | none =>
    refine ProgramDenotation.inFootprint_bind ?_ ?_
    · exact ProgramDenotation.inFootprint_mono ProgramDenotation.inFootprint_uniform bot_le
    · intro value
      refine ProgramDenotation.inFootprint_bind (ProgramDenotation.inFootprint_set _ _) ?_
      intro _
      exact ProgramDenotation.inFootprint_pure _ _
