import GaudisCrypt.Language.SubProbability
import GaudisCrypt.Language.Semantics

/-!
# EasyCrypt's distributions (`theories/distributions/`)

EasyCrypt's `'a distr` is a sub-probability, here `SubProbability`.  Only what ported developments
use is here.  Names are EasyCrypt's.

| EasyCrypt | here |
|---|---|
| `d1 \`*\` d2` (`DProd`) | `dprod d1 d2` |
| `d \ P` (`Dexcepted`) | `dexcepted d P` |
| `{0,1}`, `dbool` (`DBool`) | `dbool` |
| `is_lossless d`, `is_full d`, `is_funiform d` | the same |
-/

namespace GaudisCrypt.EC

variable {α β : Type}

/-- `d1 \`*\` d2`: the product distribution, sampling both independently. -/
noncomputable def dprod (d1 : SubProbability α) (d2 : SubProbability β) : SubProbability (α × β) :=
  d1 >>= fun a => d2 >>= fun b => pure (a, b)

/-- `is_lossless d`: `d` has total mass `1`. -/
def is_lossless (d : SubProbability α) : Prop := d.1 Set.univ = 1

/-- `is_full d`: every value is in the support of `d`. -/
def is_full (d : SubProbability α) : Prop := ∀ x, 0 < d.1 {x}

/-- `is_funiform d`: all values have the same probability. -/
def is_funiform (d : SubProbability α) : Prop := ∀ x y, d.1 {x} = d.1 {y}

open Classical in
/-- `d \ P`: `d` conditioned on not satisfying `P`.  EasyCrypt normalizes the restriction of `d` to
`¬ P`.  Here that is done for lossless `d` with a `¬ P` outcome of positive probability; otherwise
the result is the null distribution, as in EasyCrypt when no such outcome exists. -/
noncomputable def dexcepted (d : SubProbability α) (P : α → Prop) : SubProbability α :=
  if h : ∃ hd : is_lossless d, ∃ a ∈ {a | ¬ P a}, d.toPMF hd a ≠ 0 then
    toSubProbability ((d.toPMF h.1).filter {a | ¬ P a} h.2)
  else ⊥

/-- `dbool` (`{0,1}`): a fair coin. -/
noncomputable def dbool : SubProbability Bool := SubProbability.uniform

/-- `lemma dbool_ll : is_lossless dbool`. -/
theorem dbool_ll : is_lossless dbool := by
  letI : MeasurableSpace Bool := ⊤
  change (PMF.uniformOfFintype Bool).toMeasure Set.univ = 1
  haveI := @PMF.toMeasure.isProbabilityMeasure Bool ⊤ (PMF.uniformOfFintype Bool)
  exact MeasureTheory.IsProbabilityMeasure.measure_univ

end GaudisCrypt.EC
