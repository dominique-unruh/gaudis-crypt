import GaudisCrypt.Examples.SHA3.SmartCounter.Handle
import GaudisCrypt.Logic.ExpectationFrame

/-!
# The collision event of `G1` (EasyCrypt `proof/smart_counter/Gcol.eca`)

`Pr_G1col` bounds the probability of `G1.bcol` by `max_size · (2 max_size / 2^c)`, through the
game `Gcol` that counts the capacity samples (the `fel` argument of `Pr_col`).

Translation notes (see `notes/SHA3/README.md`):
* `clone export Handle as Handle0` clones a theory without parameters: it is `Handle`, opened.
* The local module `Gcol` calls `sample_c` from its inner modules `M`, `S`: these are the modules
  `Gcol.sample_c`, `Gcol.M`, `Gcol.S`, and `Gcol D` the game (with `D` a Lean parameter).
* The local module `Gcol`'s variable `count` is the lens parameter `Gcol_count` of the local
  declarations (`Gcol.sample_c`, `Gcol.M`, `Gcol.S`, `Gcol`, `Pr_col`, `G1_col`), fresh by
  hypothesis; `Pr_G1col` does not mention it (exception E6).
* EasyCrypt's `2^c` (an `int` power, `c > 0`) is `2 ^ c.toNat`; `card` (an `int`) is the
  cardinality cast to `ℤ`.
-/

-- EasyCrypt names the local module after the file (`Gcol.Gcol`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.Gcol

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.ConcreteF
open GaudisCrypt.SHA3.Handle

export GaudisCrypt.SHA3.SLCommon (state PRIMITIVE)

variable [SLCommon.Params]

theorem c_gt0r : (0 : ℝ) < ((2 ^ c.toNat : ℤ) : ℝ) := by
  positivity

theorem c_ge0r : (0 : ℝ) ≤ ((2 ^ c.toNat : ℤ) : ℝ) := by
  positivity

/-- `mu1 cdistr x = 1 / 2^c`. -/
theorem cdistr1E (x : capacity) : cdistr.1 {x} = 1 / (2 ^ c.toNat : ENNReal) := by
  letI : MeasurableSpace capacity := ⊤
  change (PMF.uniformOfFintype capacity).toMeasure {x} = _
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x)]
  simp [capacity, BitWord.word, card_vector]

/-! ## The section `PROOF` -/

omit [SLCommon.Params] in
theorem card_rng_set {α β : Type} [DecidableEq α] [DecidableEq β] (m : FMap α β) (x : α) (y : β) :
    ((FMap.frng (FMap.set m x y)).card : ℤ) ≤ (FMap.frng m).card + 1 := by
  have hsub : FMap.frng (FMap.set m x y) ⊆ insert y (FMap.frng m) := by
    intro b hb
    rw [FMap.mem_frng, FMap.rngE] at hb
    obtain ⟨a, ha⟩ := hb
    rw [FMap.get_setE] at ha
    split_ifs at ha with hax
    · simp at ha; simp [ha]
    · exact Finset.mem_insert_of_mem ((FMap.mem_frng _ _).mpr ⟨a, ha⟩)
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

theorem hinv_image (handles : handles) (c : capacity) :
    hinv handles c ≠ none → c ∈ Finset.image Prod.fst (FMap.frng handles) := by
  intro hn
  have hP := hinvP handles c
  rw [if_neg hn] at hP
  obtain ⟨f, hf⟩ := hP
  exact Finset.mem_image.mpr ⟨(c, f), (FMap.mem_frng _ _).mpr ⟨_, hf⟩, rfl⟩

/-- EC's `Mu_mem.mu_mem` for `cdistr`: a set of capacities has probability `card S / 2^c`. -/
theorem cdistr_expected_mem (S : Finset capacity) :
    cdistr.expected (fun a => if a ∈ S then (1 : ENNReal) else 0) =
      (S.card : ENNReal) * (1 / (2 ^ c.toNat : ENNReal)) := by
  rw [SubProbability.expected_eq_tsum]
  calc ∑' a, (if a ∈ S then (1 : ENNReal) else 0) * cdistr.1 {a}
      = ∑' a, if a ∈ S then cdistr.1 {a} else 0 := tsum_congr fun a => by split_ifs <;> simp
    _ = ∑ a ∈ S, cdistr.1 {a} := by
        rw [tsum_eq_sum (s := S) (fun a ha => by simp [ha])]
        exact Finset.sum_congr rfl fun a ha => by simp [ha]
    _ = _ := by rw [Finset.sum_congr rfl fun a _ => cdistr1E a, Finset.sum_const, nsmul_eq_mul]

/-! ## The invariant of `G1_col` and the oracles' steps -/

/-- A variable's footprint below a join of footprints it is a joinand of (`C.footprint`
unfolded). -/
macro "gcol_fp" : tactic => `(tactic| ((try unfold C.footprint); fp_mem))

end GaudisCrypt.SHA3.Gcol
