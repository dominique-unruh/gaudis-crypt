import GaudisCrypt.CounterExamples.IndistinguishableVsGlob
import GaudisCrypt.Logic.PRHL.Prhl

/-!
# Footprint-disjointness does not frame a run

A run confined to a footprint `R` need not leave the content (`touched_getter`) of a region
`F ≤ Rᶜ` unchanged: with `qKer`'s lazy flip (`IndistinguishableVsGlob`), the program `qProg`
lies in `R = Footprint.from {qKer}` and moves `false` to `true` with probability `½`, which
`F = qCentralizer = Rᶜ` separates.  `F` has no reset (`qCentralizer_not_hasReset`); for regions
with a reset (lens regions) the frame holds (`Lib.RO.Instantiate.inFootprint_preserves_touched`).

This is why a one-sided run of an abstract procedure (EC's `call{1}`) can be framed against a
lens region, or a granular cover (`Logic/Granular.lean`), but not against an arbitrary
`FVP.fvP A` from footprint-disjointness alone (`notes/SHA3/GlobGranularity.md`).
-/

namespace GaudisCrypt.CounterExamples
open GaudisCrypt

/-- The lazy flip as a program. -/
noncomputable def qProg : ProgramDenotation Bool Unit := fun σ => qKer σ >>= fun s => pure ((), s)

theorem qProg_inFootprint : qProg.inFootprint (Footprint.from {qKer}) := by
  intro f hf
  have hq : qKer ∈ (Footprint.from {qKer}).updates := by
    rw [Footprint.from_updates]
    exact Set.subset_centralizer_centralizer (Set.mem_singleton _)
  have hcomm : qKer * f = f * qKer :=
    Submonoid.mem_centralizer_iff.mp hf qKer hq
  funext st
  have h := congrFun hcomm st
  change f st >>= qKer = qKer st >>= f at h
  simp only [qProg, Prod.mk.eta, SubProbability.bind_pure, SubProbability.bind_assoc,
    SubProbability.pure_bind]
  rw [← SubProbability.bind_assoc, h, SubProbability.bind_assoc]

theorem qProg_false_true : (qProg false).1 {((), true)} = 2⁻¹ := by
  letI : MeasurableSpace (Unit × Bool) := ⊤
  letI : MeasurableSpace Bool := ⊤
  change (MeasureTheory.Measure.bind (qKer false).1
    fun x => (pure ((), x) : SubProbability (Unit × Bool)).1) {((), true)} = _
  rw [MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
    measurable_from_top.aemeasurable, lintegral_eq_tsum_smul (qKer false).2.2, tsum_bool,
    qKer_false_apply, qKer_false_apply]
  have hd : ∀ x y : Unit × Bool, (pure x : SubProbability (Unit × Bool)).1 {y} =
      if x = y then 1 else 0 := by
    intro x y
    change (MeasureTheory.Measure.dirac x) {y} = _
    rw [MeasureTheory.Measure.dirac_apply' _ MeasurableSet.of_discrete]
    by_cases h : x = y <;> simp [h, Set.indicator]
  rw [hd, hd]
  simp

/-- **Footprint-disjointness does not frame**: a program confined to `R` can change the content
of a region `F ≤ Rᶜ` (here `F = Rᶜ`), when `F` has no reset. -/
theorem framing_fails :
    ∃ (p : ProgramDenotation Bool Unit) (R F : Footprint Bool), p.inFootprint R ∧ F ≤ Rᶜ ∧
      ¬ (p false).satisfies (fun xs => F.touched_getter.get xs.2 = F.touched_getter.get false) :=
  ⟨qProg, Footprint.from {qKer}, qCentralizer, qProg_inFootprint, le_rfl, fun h =>
    touched_getter_separates (h ((), true) (by rw [qProg_false_true]; norm_num)).symm⟩

end GaudisCrypt.CounterExamples
