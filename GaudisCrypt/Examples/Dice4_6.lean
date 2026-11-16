import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Syntax.Clone
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECRnd
import GaudisCrypt.Logic.ECWhileRel
import GaudisCrypt.Logic.ECTransProc
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.PHoareExactTactics
import GaudisCrypt.Lib.EC.Logic
import GaudisCrypt.Lib.EC.DInterval
import GaudisCrypt.Lib.EC.WhileSamplingFixedTest

/-!
# A four-sided die from a six-sided one (EasyCrypt `examples/Dice4_6.ec`)

Roll a six-sided die until it shows 1–4 (`D6`): each of 1–4 has probability `1/4` (`prD6`), as
for a four-sided die (`D4`, `prD4`).  The two are related (`D4_D6`) through EC's theory of
rejection sampling, cloned as `D4_6`: `D4` samples the restricted distribution (`D4_Sample`),
`D6` is the rejection loop (`D6_Sample`), and the theory relates the two
(`D4_6.sampleE_sampleWi`, `Lib/EC/WhileSamplingFixedTest.lean`).

EC's file, declaration by declaration.  All of EC's lemmas are proven.

Translation:
* `[1..6]` is `dinter 1 6` (`Lib/EC/DInterval.lean`); `var r <- 5` is the declaration and the
  assignment; `while (5 <= r) r <$ [1..6]` has its body in braces.
* `clone WhileSamplingFixedTest as D4_6 with …`: the clone; the theory's `dt`, `test` at the
  clone are written `WhileSamplingFixedTest.dt`, `WhileSamplingFixedTest.test`.

Gap list (what keeps the file from reading as EC's):
* GAP 1 (`D4_Sample`): EC's `rnd` asks that the two distributions give each value the same
  mass, which the script computes (`dexcepted1E`, `weight_dinter`, `dinter1E`, `dinterE`,
  `iotaS`, …); `equiv_rnd` asks that they are equal, which is the library's
  `dinter_dexcepted` (an interval conditioned on a sub-interval).
* GAP 2 (`D4_D6`): EC's `proc *` and `rewrite equiv[{1} 1 L args]` (the call on the left
  replaced along an equivalence, three times, then `sim`) are two `transitivity` steps on the
  procedures (`equiv_trans (N.f) (P₁ ==> Q₁) (P₂ ==> Q₂)`): through `D4_6.SampleE.sample`
  (`D4_Sample`) and `D4_6.SampleWi.sample` (`D4_6.sampleE_sampleWi`, then `D6_Sample`
  reversed).  The argument `((), 5 :@ r)` and the side condition `dinter_ll` of EC's second
  rewrite are the `hP` goal of the second step.
* GAP 3: `rnd f finv; auto=> />` is `equiv_rnd f finv; equiv_skip` (`equiv_auto` loops on
  `b = f (finv b)`); EC's `rewrite supp_dinter /#` on the conditions (and `apply: dinter_uni`)
  are `smt_close [supp_dinter]`, `smt_close [supp_dinter, dinter1E]`.
* GAP 4: `byphoare (: True ==> _)` for `byphoare=> //`; `rnd` on an exact bound is
  `phoare_rnd (pred1 k)`.
-/

set_option ec.strict true
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace GaudisCrypt.Examples.Dice4_6

open GaudisCrypt GaudisCrypt.EC

-- EC: clone WhileSamplingFixedTest as D4_6 with
--       type t             <- int,
--       type input         <- unit,
--       op   dt   (i:unit) <- [1..6],
--       op   test (i:unit) <- fun r=> !1 <= r <= 4
--     proof *.
clone GaudisCrypt.EC.WhileSamplingFixedTest as D4_6 with
  type t <- ℤ, type input <- Unit,
  op dt <- fun _ => dinter 1 6,
  op test <- fun _ r => decide (¬ (1 ≤ r ∧ r ≤ 4))

module D4 {
  proc sample () : ℤ {
    var r : ℤ;
    r <$ dinter 1 4;
    return $r
  };
}

theorem prD4 (k : ℤ) (m : VariableAssignment) :
    Pr[ D4.sample () @ &m : §res = k ] = if 1 ≤ k ∧ k ≤ 4 then 1 / 4 else 0 := by
  -- EC: move=> k &m; byphoare=> //.
  --     by proc; rnd; auto=> />; rewrite dinter1E.
  byphoare (: True ==> _)
  phoare_proc; phoare_rnd (pred1 k); phoare_auto
  refine ⟨?_, fun _ _ => Iff.rfl⟩
  rw [mu_pred1, dinter1E]; norm_num

module D6 {
  proc sample () : ℤ {
    var r : ℤ;
    r <- 5;
    while (decide (5 ≤ $r)) {
      r <$ dinter 1 6;
    }
    return $r
  };
}

theorem D4_Sample : equiv[ D4.sample ~ D4_6.SampleE.sample : True ==> ={res} ] := by
  -- EC: proc; rnd; auto=> />; split=> [r|_ r].
  equiv_proc; equiv_rnd; equiv_auto
  -- EC: + rewrite supp_dexcepted supp_dinter=> /= - [] _ r_bounds.
  --       rewrite dexcepted1E /= r_bounds /=.
  --       rewrite weight_dinter /= !dinter1E dinterE size_filter.
  --       rewrite /range /= (@iotaS 1 5) //= (@iotaS 2 4) //= (@iotaS 3 3) //=.
  --       rewrite (@iotaS 4 2) //= (@iotaS 5 1) //= (@iotaS 6 0) //= (@iota0 7 0) //=.
  --       by rewrite /b2i /max /#.
  --     by rewrite supp_dinter supp_dexcepted supp_dinter /= /#.
  intro _ _
  change dinter 1 4 = dexcepted (dinter 1 6) (fun v => decide (¬ (1 ≤ v ∧ v ≤ 4)) = true)
  simp only [decide_eq_true_eq]
  exact (dinter_dexcepted 1 6 1 4 (by norm_num)).symm

theorem D6_Sample : equiv[ D6.sample ~ D4_6.SampleWi.sample : §r{2} = 5 ==> ={res} ] := by
  -- EC: proc=> /=; while (={r}).
  equiv_proc
  equiv_while (={r})
  · -- EC: + by rnd; auto=> /> &2 _ + r; rewrite supp_dinter /#.
    equiv_rnd; equiv_auto
    smt_close [supp_dinter]
  -- EC: by auto.
  equiv_auto
  smt_close

theorem D4_D6 (f finv : ℤ → ℤ) :
    (∀ i, 1 ≤ i ∧ i ≤ 4 ↔ 1 ≤ f i ∧ f i ≤ 4) →
    (∀ i, 1 ≤ i ∧ i ≤ 4 → f (finv i) = i ∧ finv (f i) = i) →
    equiv[ D4.sample ~ D6.sample : True ==> §res{1} = finv §res{2} ] := by
  -- EC: move=> Hbound Hbij.
  intro Hbound Hbij
  -- EC: transitivity D4.sample (true ==> res{1} = finv res{2})
  --                            (true ==> ={res})=> //.
  equiv_trans (D4.sample) (True ==> §res{1} = finv §res{2}) (True ==> ={res})
  · -- EC: + proc; rnd f finv; auto=> />; split=> [r|_].
    equiv_proc; equiv_rnd f finv; equiv_skip
    -- EC:   + by rewrite supp_dinter /#.
    --       split=> [r|_ r].
    --       + rewrite supp_dinter=> - /= r_bounds.
    --         by apply: dinter_uni; rewrite supp_dinter /#.
    --       by rewrite !supp_dinter /#.
    smt_close [supp_dinter, dinter1E]
  -- EC: proc *.
  --     rewrite equiv[{1} 1 D4_Sample].
  --     rewrite equiv[{1} 1 D4_6.sampleE_sampleWi ((), 5 :@ r)].
  --     + by auto; rewrite dinter_ll.
  --     rewrite equiv[{1} 1 -D6_Sample ( :@ r)]; sim.
  equiv_trans (D4_6.SampleE.sample) (True ==> ={res}) (True ==> ={res})
  · exact D4_Sample
  equiv_trans (D4_6.SampleWi.sample)
    (={i} ∧ is_lossless (WhileSamplingFixedTest.dt §i{1}) ∧
      WhileSamplingFixedTest.test §i{2} §r{2} ==> ={res})
    (§r{1} = 5 ==> ={res})
  · exact fun _ g _ _ _ => ⟨((), 5), g, ⟨rfl, dinter_ll 1 6 (by norm_num), rfl⟩, rfl⟩
  · exact D4_6.sampleE_sampleWi
  · equiv_sym
    exact prhlProc_conseq D6_Sample (fun _ _ _ _ h => h) (fun _ _ _ _ h => h.symm)

theorem prD6 (k : ℤ) (m : VariableAssignment) :
    Pr[ D6.sample () @ &m : §res = k ] = if 1 ≤ k ∧ k ≤ 4 then 1 / 4 else 0 := by
  -- EC: move=> k &m.
  --     rewrite -(: Pr[D4.sample() @ &m: res = k] = Pr[D6.sample() @ &m: res = k]).
  --     + by byequiv (D4_D6 (fun x=> x) (fun x=> x) _ _).
  --     exact/(@prD4 k &m).
  have h : Pr[ D4.sample () @ &m : §res = k ] = Pr[ D6.sample () @ &m : §res = k ] := by
    byequiv (D4_D6 (fun x => x) (fun x => x) (fun _ => Iff.rfl) fun _ _ => ⟨rfl, rfl⟩)
  rw [← h]
  exact prD4 k m

end GaudisCrypt.Examples.Dice4_6
