import GaudisCrypt.Lib.EC.Distr

/-!
# The support of an excepted distribution

`d \ P` puts no mass on `P`: a value in its support is not in `P` (one direction of EasyCrypt's
`supp_dexcepted`).  Kept apart from `Dexcepted.lean` so that the developments that use it do not
depend on that file's imports.
-/

namespace GaudisCrypt.EC

/-- `supp_dexcepted`, the direction `x \in d \ P => !P x`. -/
theorem not_of_mem_support_dexcepted {α : Type} {d : SubProbability α} {P : α → Prop} {a : α}
    (h : a ∈ (dexcepted d P).support) : ¬ P a := by
  intro hp
  rw [SubProbability.mem_support_iff] at h
  apply h
  unfold dexcepted
  split_ifs with hh
  · letI : MeasurableSpace α := ⊤
    change (toSubProbability _).ofEvent {a} = 0
    simp [SubProbability.ofEvent, toSubProbability,
      PMF.toMeasure_apply_singleton _ a (MeasurableSet.singleton a), PMF.filter_apply,
      Set.indicator, hp]
  · rfl

end GaudisCrypt.EC
