import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECLoop
import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Logic.ECWhile
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.PHoareWhileRev
import GaudisCrypt.Logic.PHoareExactTactics
import GaudisCrypt.Logic.ByPrEquiv
import GaudisCrypt.Lib.EC.Logic
import GaudisCrypt.Lib.EC.Dexcepted

/-!
# EasyCrypt's `WhileSamplingFixedTest` (`theories/distributions/Dexcepted.ec`)

Sampling from `dt i \ test i` (the distribution `dt i` conditioned on failing `test i`) and
rejection sampling: `SampleE` samples the conditioned distribution, `SampleWi` resamples from
`dt i` while the test holds.  The theory's types and operators (`type input, t`,
`op dt : input -> t distr`, `op test : input -> t -> bool`) are the class `Params`.

Only what ported developments use is here: the modules `SampleE`, `SampleWi`, and the lemmas
`pr_sampleE`, `pr_sampleWi`, `sampleE_sampleWi`.  The proofs are not EasyCrypt's (which go
through its theories `TwoStepSampling` and `WhileSampling`): `pr_sampleWi` is the loop rule
`while I V k ε` with the two-step identity `dexcepted_indirect` for the body.  Names are
EasyCrypt's.
-/

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace GaudisCrypt

/-- A sampling followed by a statement `w`, from a judgment about `w` whose bound is a
function of the state: the bound is its expected value over the sampling. -/
theorem phoareStmt_sample_seq {α : Type} {A I : ProgramState → Prop}
    {x : Setter α ProgramState} {e : Getter (SubProbability α) ProgramState} {w : Stmt}
    {Q r r' : ProgramState → ENNReal}
    (ih : phoareStmt I w Q Eq r')
    (hI : ∀ σ, A σ → ∀ a, I (x.set a σ))
    (hr : ∀ σ, A σ → (e.get σ).expected (fun a => r' (x.set a σ)) = r σ) :
    phoareStmt A (.seq (.sample x e) w) Q Eq r := by
  intro σ hA
  rw [Stmt.ewp_seq, Stmt.ewp_sample, ← hr σ hA]
  exact SubProbability.expected_congr _ fun a => ih _ (hI σ hA a)

namespace EC

variable {α : Type}

/-- An event that never holds has probability `0`. -/
theorem mu_eq_zero_of_forall_not (d : SubProbability α) (E : α → Prop) (h : ∀ v, ¬ E v) :
    mu d E = 0 := by
  unfold mu
  rw [show (fun v => indicatorE (E v)) = fun _ => 0 from funext fun v => indicatorE_of_not (h v),
    SubProbability.expected_zero]
  rfl

/-- An event of probability `0` holds nowhere on the support. -/
theorem not_of_mem_support_of_mu_eq_zero (d : SubProbability α) (E : α → Prop)
    (h : mu d E = 0) : ∀ v, d.1 {v} ≠ 0 → ¬ E v := by
  intro v hv hE
  have h1 : d.expected (fun v => indicatorE (E v)) ≤ 1 := by
    letI : MeasurableSpace α := ⊤
    refine le_trans (MeasureTheory.lintegral_mono fun v => indicatorE_le_one (E v)) ?_
    rw [MeasureTheory.lintegral_one]; exact d.2.1
  have h0 : d.expected (fun v => indicatorE (E v)) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp h with h0 | htop
    · exact h0
    · exact absurd (htop ▸ h1) (by simp)
  rw [SubProbability.expected_eq_tsum] at h0
  have := ENNReal.tsum_eq_zero.mp h0 v
  rw [indicatorE_of hE, one_mul] at this
  exact hv this

/-- `d \ P` is the null distribution when `d` gives no mass outside `P`. -/
theorem dexcepted_eq_bot (d : SubProbability α) (P : α → Prop) (h : ∀ a, ¬ P a → d.1 {a} = 0) :
    dexcepted d P = ⊥ := by
  rw [dexcepted, dif_neg]
  rintro ⟨_, a, ha, hne⟩
  exact hne (h a ha)

open Classical in
/-- One round of rejection sampling: the expected value, over a draw from `d`, of "the
probability of `P` under `d \ X` if the draw is in `X`, else whether the draw is in `P`", is
the probability of `P` under `d \ X` (EC's `TwoStepSampling`, `dexcepted_indirect`). -/
theorem dexcepted_expected_step (d : SubProbability α) (X P : α → Prop) (hd : is_lossless d) :
    d.expected (fun a => ENNReal.ofReal
      (if X a then mu (dexcepted d X) P else if P a then 1 else 0)) =
      ENNReal.ofReal (mu (dexcepted d X) P) := by
  have key := congrArg (fun μ => μ.expected (fun v => indicatorE (P v)))
    (dexcepted_indirect d X hd)
  simp only [SubProbability.expected_bind] at key
  have hM : ENNReal.ofReal (mu (dexcepted d X) P) =
      (dexcepted d X).expected (fun v => indicatorE (P v)) := by
    refine ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top ?_)
    letI : MeasurableSpace α := ⊤
    refine le_trans (MeasureTheory.lintegral_mono fun v => indicatorE_le_one (P v)) ?_
    rw [MeasureTheory.lintegral_one]; exact (dexcepted d X).2.1
  rw [hM, ← key]
  refine SubProbability.expected_congr _ fun a => ?_
  by_cases hX : X a
  · rw [if_pos hX, if_pos hX, hM]
  · rw [if_neg hX, if_neg hX, expected_pure]
    by_cases hP : P a <;> simp [hP, indicatorE]

end EC

end GaudisCrypt

namespace GaudisCrypt.EC.WhileSamplingFixedTest

open GaudisCrypt GaudisCrypt.EC

/-- The theory's parameters. -/
class Params (input t : outParam Type) where
  /-- `op dt : input -> t distr`. -/
  dt : input → SubProbability t
  /-- `op test : input -> t -> bool`. -/
  test : input → t → Bool

export Params (dt test)

variable {input t : Type} [Inhabited input] [Inhabited t] [Params input t]

module SampleE {
  proc init () : Unit {
    return ()
  };
  proc sample (i : input) : t {
    var r : t;
    r <$ dexcepted (dt $i) (fun v => test $i v);
    return $r
  };
}

module SampleWi {
  proc init () : Unit {
    return ()
  };
  proc sample (i : input, r : t) : t {
    while (test $i $r) {
      r <$ dt $i;
    }
    return $r
  };
}

/-- `lemma pr_sampleE`. -/
theorem pr_sampleE (m : VariableAssignment) (x : input) (P : t → Prop) :
    Pr[ SampleE.sample (x) @ &m : P §res ] = mu (dexcepted (dt x) (fun v => test x v)) P := by
  byphoare (: §i = x ==> _)
  case hx => exact ge0_mu _ _
  phoare_proc; phoare_rnd P; phoare_auto
  rintro i rfl; rfl

/-- When `dt x` gives no mass to the values that fail the test, its support passes it. -/
theorem test_of_mem_support (x : input)
    (h : ¬ 0 < mu (dt x) (fun v => test x v = false)) (v : t) (hv : v ∈ (dt x).support) :
    test x v = true := by
  have := not_of_mem_support_of_mu_eq_zero (dt x) _
    (le_antisymm (not_lt.mp h) (ge0_mu _ _)) v fun h0 =>
      (SubProbability.mem_support_iff _ _).mp hv (by simp [SubProbability.ofEvent, h0])
  simpa using this

open Classical in
/-- `lemma pr_sampleWi`. -/
theorem pr_sampleWi (m : VariableAssignment) (x : input) (y : t) (P : t → Prop)
    (dt_ll : is_lossless (dt x)) :
    Pr[ SampleWi.sample (x, y) @ &m : P §res ] =
      if test x y then mu (dexcepted (dt x) (fun v => test x v)) P
      else if P y then 1 else 0 := by
  by_cases hy : test x y = true
  swap
  · -- the loop is not entered
    rw [if_neg hy]
    byphoare (: §i = x ∧ §r = y ==> _)
    phoare_proc
    stmt_rcondf 1
    · hoare_auto
    phoare_auto
    rintro i r ⟨rfl, rfl⟩
    by_cases hp : P r <;> simp [hp, indicatorE]
  rw [if_pos hy]
  byphoare (: §i = x ∧ §r = y ==> _)
  case hx => exact ge0_mu _ _
  phoare_proc
  by_cases hP : ∃ v, P v
  swap
  · -- an event that never holds
    phoare_conseq (: _ ==> _ : = 0)
    · intros; exact mu_eq_zero_of_forall_not _ _ fun v hv => hP ⟨v, hv⟩
    phoare_hoare
    exact hoare_post (hoareStmt_true _ _) fun σ _ h => hP ⟨_, h⟩
  by_cases hε : 0 < mu (dt x) (fun v => test x v = false)
  swap
  · -- `dt x` gives no mass outside the test: the loop does not end
    phoare_conseq (: _ ==> _ : = 0)
    · intros
      rw [dexcepted_eq_bot _ _ fun a ha => by_contra fun h =>
        ha (test_of_mem_support x hε a (SubProbability.mem_support_of_ne_zero h))]
      unfold mu; rw [SubProbability.expected_bot]; rfl
    phoare_hoare
    hoare_conseq (: _ ==> False)
    · exact fun _ _ _ _ h => h.elim
    hoare_while_raw (§i = x ∧ test §i §r)
    · hoare_auto
      rintro i r ⟨⟨rfl, -⟩, -⟩ v hv
      exact ⟨rfl, test_of_mem_support _ hε v hv⟩
    · rintro i r ⟨-, h⟩ h'
      exact Bool.noConfusion (h.symm.trans h')
    hoare_auto
  phoare_conseq (: _ ==> _ : = (if test x §r then mu (dexcepted (dt x) (fun v => test x v)) P
    else if P §r then 1 else 0))
  · rintro i r ⟨rfl, rfl⟩; rw [if_pos hy]
  phoare_conseq (: §i = x ==> _)
  · exact fun _ _ h => h.1
  phoare_while (§i = x) (if test §i §r then 1 else 0) 1 (mu (dt x) (fun v => test x v = false))
  · rintro i r rfl h
    rw [if_neg (by simp [h])]
    by_cases hp : P r <;> simp [hp, indicatorE]
  · rintro i r rfl
    by_cases h : test i r = true <;> simp [h]
  · intro w ih
    refine phoareStmt_sample_seq ih ?_ ?_
    · intro σ h a
      simp_reads
      exact h.1
    · intro σ h
      simp_reads
      have h1 : (localVarLens "i" input).get σ = x := h.1
      have h2 : test x ((localVarLens "r" t).get σ) = true := h1 ▸ h.2
      rw [h1, if_pos h2]
      convert dexcepted_expected_step (dt x) (fun v => test x v = true) P dt_ll
  · phoare_auto
    rintro i r ⟨rfl, -⟩; exact ⟨dt_ll, fun _ _ => rfl⟩
  · intro z
    phoare_rnd (fun v => test x v = false); phoare_auto
    rintro i r ⟨rfl, h, rfl⟩
    refine ⟨le_rfl, fun v _ hv => ?_⟩
    rw [if_pos h, if_neg (by simp [hv])]; norm_num
  · rintro i r rfl
    rw [ENNReal.ofReal_le_one]
    split_ifs <;> first | exact le1_mu _ _ | norm_num
  · obtain ⟨v, hv⟩ := hP
    exact ⟨(localVarLens "r" t).set v ⟨VariableAssignment.init, VariableAssignment.init⟩,
      indicatorE_of (by rw [Lens.set_get]; exact hv)⟩

/-- `equiv sampleE_sampleWi`: sampling `dt i \ test i`, and resampling from `dt i` while the
test holds (from a value that satisfies it), return the same result. -/
theorem sampleE_sampleWi :
    equiv[ SampleE.sample ~ SampleWi.sample :
      ={i} ∧ is_lossless (dt §i{1}) ∧ test §i{2} §r{2} ==> ={res} ] := by
  -- EC: bypr (res{1}) (res{2}) => /> &m1 &m2 a dt_ll Htr.
  --     by rewrite (@pr_sampleE &m1 i{m2} (pred1 a)) (@pr_sampleWi &m2 i{m2} r{m2} (pred1 a))
  --        // Htr.
  bypr (res{1}) (res{2})
  intro (a1 : input) m1 (a2 : input × t) m2 v h
  obtain ⟨x, y⟩ := a2
  have h' : a1 = x ∧ is_lossless (dt a1) ∧ test x y = true := h
  obtain ⟨rfl, dt_ll, Htr⟩ := h'
  refine ((pr_sampleE m1 a1 (fun r => r = v)).trans ?_).trans
    (pr_sampleWi m2 a1 y (fun r => r = v) dt_ll).symm
  rw [if_pos Htr]

end GaudisCrypt.EC.WhileSamplingFixedTest
