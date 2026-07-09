import GaudisCrypt.Lib.RO.CollisionResistance
import GaudisCrypt.Logic.PRHL.Coupling
import GaudisCrypt.Logic.PRHL.UpToBad
import GaudisCrypt.Logic.PRHL.Loops

open GaudisCrypt
open GaudisCrypt.Language.Semantics

/-!
# PRP/PRF switching lemma — oracles and the shared bad flag (Phase 1)

Infrastructure for the information-theoretic switching lemma
`|Pr[A^RF] − Pr[A^RP]| ≤ q(q−1)/2N`, set up for the up-to-bad (Fundamental
Lemma) argument in the relational calculus.

The two oracles are *identical until bad*: both draw the **same** underlying
uniform value `y` on a cache miss and set the shared flag `prp_bad` to `true`
iff `y` already occurs in the oracle's image (a collision). On no collision
both behave identically (cache `y`); on a collision `RF` keeps `y` (with
replacement) while `RP` resamples a fresh value from the unused outputs
(without replacement). Because the flag is set from the same draw against the
same image, it agrees on both sides — exactly what `relE.up_to_bad` needs.

* `prp_bad : Variable Bool` — the shared "a collision has occurred" flag.
* `colliding_outputs h inp` — outputs already used by inputs other than `inp`
  (the values a fresh draw at `inp` would collide with). Equal to
  `inducing_set inp σ` when `h = random_oracle_state.get σ`.
* `lazy_query_rf` / `lazy_query_rp` — the RF and RP oracles.
* `lazy_query_rf_inRange` / `lazy_query_rp_inRange` — both touch only
  `random_oracle_state` and `prp_bad`.

This is **Phase 1** of the plan; the per-query coupling (Phase 2) and the
Fundamental-Lemma assembly (Phases 3–4) build on these definitions.
-/

/-- Shared "a collision has occurred" flag for the switching coupling. Set to
    `true` the first time a freshly drawn output already appears in the image;
    both `lazy_query_rf` and `lazy_query_rp` maintain it identically. -/
axiom prp_bad : Variable Bool

axiom disjoint_prp_bad_ro : disjoint prp_bad random_oracle_state
axiom disjoint_prp_bad_oracle_input : disjoint prp_bad oracle_input
axiom disjoint_prp_bad_oracle_output : disjoint prp_bad oracle_output

attribute [instance] disjoint_prp_bad_ro
                     disjoint_prp_bad_oracle_input
                     disjoint_prp_bad_oracle_output

/-- Symmetric instances. -/
instance : disjoint random_oracle_state prp_bad := disjoint_prp_bad_ro.symm
instance : disjoint oracle_input prp_bad := disjoint_prp_bad_oracle_input.symm
instance : disjoint oracle_output prp_bad := disjoint_prp_bad_oracle_output.symm

/-- The symmetric forms of the OracleLoop RO-disjointness axioms, needed to
    frame the RO read/write inside the oracles against the scratch lenses. -/
instance : disjoint random_oracle_state oracle_input := disjoint_oracle_input_ro.symm
instance : disjoint random_oracle_state oracle_output := disjoint_oracle_output_ro.symm

/-- Outputs already assigned to some input *other than* `inp` — i.e. the values
    a fresh draw at `inp` would collide with, and (when `inp` is uncached) the
    set `RP` must avoid to stay injective. Definitionally equal to
    `inducing_set inp σ` when `h = random_oracle_state.get σ`. -/
noncomputable def colliding_outputs (h : input → Option output) (inp : input) :
    Finset output :=
  ((Finset.univ.erase inp).filter (fun x' => (h x').isSome)).image
    (fun x' => (h x').getD default)

/-- **RF oracle (instrumented).** Acts exactly like `lazy_query` on the RO
    state, additionally setting `prp_bad := true` when the freshly drawn value
    already occurs in the image (the draw creates a collision). Written with
    explicit `>>=` to avoid the do-notation join-point macro on the `if`. -/
noncomputable def lazy_query_rf (inp : input) : ProgramDenotation state output :=
  ProgramDenotation.get random_oracle_state >>= fun h =>
    match h inp with
    | some x => (pure x : ProgramDenotation state output)
    | none =>
      ProgramDenotation.uniform >>= fun y =>
        (if y ∈ colliding_outputs h inp then ProgramDenotation.set prp_bad true
         else (pure () : ProgramDenotation state Unit)) >>= fun _ =>
          ProgramDenotation.set random_oracle_state (fun x => if x = inp then some y else h x)
            >>= fun _ => (pure y : ProgramDenotation state output)

/-- **RP oracle (instrumented, resample-on-collision).** Draws the *same* `y`
    and sets `prp_bad` on a collision exactly as `lazy_query_rf`. On a collision
    it resamples uniformly from the unused outputs (`univ \ colliding_outputs`),
    keeping the oracle injective; if the outputs are exhausted it falls through
    (the flag is already set, so the returned value is immaterial). -/
noncomputable def lazy_query_rp (inp : input) : ProgramDenotation state output :=
  ProgramDenotation.get random_oracle_state >>= fun h =>
    match h inp with
    | some x => (pure x : ProgramDenotation state output)
    | none =>
      ProgramDenotation.uniform >>= fun y =>
        if y ∈ colliding_outputs h inp then
          ProgramDenotation.set prp_bad true >>= fun _ =>
            (if hne : (Finset.univ \ colliding_outputs h inp).Nonempty then
               ProgramDenotation.uniformOfFinset (Finset.univ \ colliding_outputs h inp) hne
             else (pure y : ProgramDenotation state output)) >>= fun y' =>
              ProgramDenotation.set random_oracle_state (fun x => if x = inp then some y' else h x)
                >>= fun _ => (pure y' : ProgramDenotation state output)
        else
          ProgramDenotation.set random_oracle_state (fun x => if x = inp then some y else h x)
            >>= fun _ => (pure y : ProgramDenotation state output)

/-! ### Closed-form weakest preconditions (Phase 2a)

The per-query coupling marginals are computed against these closed forms. -/

/-- The sub-distribution `lazy_query_rp` resamples from on a collision: uniform
    over the unused outputs, or a point mass on `y` if all outputs are used. -/
noncomputable def rp_resample_sub (h : input → Option output) (inp : input)
    (y : output) : SubProbability output :=
  if hne : (Finset.univ \ colliding_outputs h inp).Nonempty then
    SubProbability.uniformOfFinset (Finset.univ \ colliding_outputs h inp) hne
  else (pure y : SubProbability output)

/-- `lazy_query_rf` on a cache hit returns the cached value, no state change. -/
lemma lazy_query_rf_wp_hit {inp : input} {σ : state} {x : output}
    (hc : random_oracle_state.get σ inp = some x) (F : output × state → ENNReal) :
    (lazy_query_rf inp).wp F σ = F (x, σ) := by
  simp only [lazy_query_rf, wp_bind, wp_get, hc, wp_pure]

/-- `lazy_query_rp` on a cache hit returns the cached value, no state change. -/
lemma lazy_query_rp_wp_hit {inp : input} {σ : state} {x : output}
    (hc : random_oracle_state.get σ inp = some x) (G : output × state → ENNReal) :
    (lazy_query_rp inp).wp G σ = G (x, σ) := by
  simp only [lazy_query_rp, wp_bind, wp_get, hc, wp_pure]

/-- `lazy_query_rf` on a cache miss: uniform over the drawn value `y`, setting
    the flag and caching `y` on a collision (with replacement). -/
lemma lazy_query_rf_wp_miss {inp : input} {σ : state}
    (hc : random_oracle_state.get σ inp = none) (F : output × state → ENNReal) :
    (lazy_query_rf inp).wp F σ
      = ∑ y : output, F (y,
          if y ∈ colliding_outputs (random_oracle_state.get σ) inp
          then random_oracle_state.set
                 (fun k => if k = inp then some y else random_oracle_state.get σ k)
                 (prp_bad.set true σ)
          else random_oracle_state.set
                 (fun k => if k = inp then some y else random_oracle_state.get σ k) σ)
        / Fintype.card output := by
  simp only [lazy_query_rf, wp_bind, wp_get, hc, wp_uniform]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  by_cases hb : y ∈ colliding_outputs (random_oracle_state.get σ) inp
  · simp only [if_pos hb, wp_set, wp_pure]
  · simp only [if_neg hb, wp_set, wp_pure]

/-- `lazy_query_rp` on a cache miss: uniform over the drawn value `y`; on a
    collision it sets the flag and resamples a fresh value (without
    replacement) via `rp_resample_sub`, otherwise caches `y`. -/
lemma lazy_query_rp_wp_miss {inp : input} {σ : state}
    (hc : random_oracle_state.get σ inp = none) (G : output × state → ENNReal) :
    (lazy_query_rp inp).wp G σ
      = ∑ y : output,
          (if y ∈ colliding_outputs (random_oracle_state.get σ) inp
           then (rp_resample_sub (random_oracle_state.get σ) inp y).expected
                  (fun y' => G (y', random_oracle_state.set
                    (fun k => if k = inp then some y' else random_oracle_state.get σ k)
                    (prp_bad.set true σ)))
           else G (y, random_oracle_state.set
                    (fun k => if k = inp then some y else random_oracle_state.get σ k) σ))
        / Fintype.card output := by
  simp only [lazy_query_rp, wp_bind, wp_get, hc, wp_uniform]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  by_cases hb : y ∈ colliding_outputs (random_oracle_state.get σ) inp
  · simp only [if_pos hb, wp_bind, wp_set]
    unfold rp_resample_sub
    by_cases hne : (Finset.univ \ colliding_outputs (random_oracle_state.get σ) inp).Nonempty
    · simp only [dif_pos hne, ProgramDenotation.uniformOfFinset, wp_lift, wp_pure]
    · simp only [dif_neg hne, wp_pure, expected_pure]
  · simp only [if_neg hb, wp_bind, wp_set, wp_pure]

/-- `lazy_query_rf` touches only `random_oracle_state` and `prp_bad`: it lives in
    the complement of any lens disjoint from both. -/
lemma lazy_query_rf_inRange {α : Type} (L : Variable α)
    [disjoint random_oracle_state L] [disjoint prp_bad L] (inp : input) :
    (lazy_query_rf inp).inRange L.compl.range := by
  unfold lazy_query_rf
  refine ProgramDenotation.inRange_bind
    (ProgramDenotation.get_inRange_compl_of_disjoint random_oracle_state L) (fun h => ?_)
  cases h inp with
  | some x => exact ProgramDenotation.inRange_pure _ _
  | none =>
    refine ProgramDenotation.inRange_bind
      (ProgramDenotation.inRange_mono ProgramDenotation.inRange_uniform bot_le) (fun y => ?_)
    refine ProgramDenotation.inRange_bind ?_ (fun _ => ?_)
    · by_cases hy : y ∈ colliding_outputs h inp
      · simp only [if_pos hy]
        exact ProgramDenotation.set_inRange_compl_of_disjoint prp_bad L true
      · simp only [if_neg hy]
        exact ProgramDenotation.inRange_pure _ _
    · exact ProgramDenotation.inRange_bind
        (ProgramDenotation.set_inRange_compl_of_disjoint random_oracle_state L _)
        (fun _ => ProgramDenotation.inRange_pure _ _)

/-- `lazy_query_rp` touches only `random_oracle_state` and `prp_bad`. -/
lemma lazy_query_rp_inRange {α : Type} (L : Variable α)
    [disjoint random_oracle_state L] [disjoint prp_bad L] (inp : input) :
    (lazy_query_rp inp).inRange L.compl.range := by
  unfold lazy_query_rp
  refine ProgramDenotation.inRange_bind
    (ProgramDenotation.get_inRange_compl_of_disjoint random_oracle_state L) (fun h => ?_)
  cases h inp with
  | some x => exact ProgramDenotation.inRange_pure _ _
  | none =>
    refine ProgramDenotation.inRange_bind
      (ProgramDenotation.inRange_mono ProgramDenotation.inRange_uniform bot_le) (fun y => ?_)
    by_cases hy : y ∈ colliding_outputs h inp
    · simp only [if_pos hy]
      refine ProgramDenotation.inRange_bind
        (ProgramDenotation.set_inRange_compl_of_disjoint prp_bad L true) (fun _ => ?_)
      refine ProgramDenotation.inRange_bind ?_ (fun y' => ?_)
      · by_cases hne : (Finset.univ \ colliding_outputs h inp).Nonempty
        · simp only [dif_pos hne]
          exact ProgramDenotation.inRange_mono (ProgramDenotation.inRange_uniformOfFinset _ hne)
              bot_le
        · simp only [dif_neg hne]
          exact ProgramDenotation.inRange_pure _ _
      · exact ProgramDenotation.inRange_bind
          (ProgramDenotation.set_inRange_compl_of_disjoint random_oracle_state L _)
          (fun _ => ProgramDenotation.inRange_pure _ _)
    · simp only [if_neg hy]
      exact ProgramDenotation.inRange_bind
        (ProgramDenotation.set_inRange_compl_of_disjoint random_oracle_state L _)
        (fun _ => ProgramDenotation.inRange_pure _ _)

/-! ### The per-query coupling (Phase 2b) -/

/-- The resample sub-distribution has mass one, so integrating a constant
    against it returns the constant. -/
lemma rp_resample_sub_expected_const (h : input → Option output) (inp : input)
    (y : output) (c : ENNReal) :
    (rp_resample_sub h inp y).expected (fun _ => c) = c := by
  unfold rp_resample_sub
  by_cases hne : (Finset.univ \ colliding_outputs h inp).Nonempty
  · simp only [dif_pos hne]
    rw [uniformOfFinset_expected, Finset.sum_const, nsmul_eq_mul,
        ENNReal.mul_div_cancel
          (by exact_mod_cast (Finset.card_pos.mpr hne).ne' :
              ((Finset.univ \ colliding_outputs h inp).card : ENNReal) ≠ 0)
          (ENNReal.natCast_ne_top _)]
  · simp only [dif_neg hne, expected_pure]

/-- **Per-query coupling** (the heart of the switching argument). From equal
    states with the flag clear, `lazy_query_rf` and `lazy_query_rp` are coupled
    so that the flag always agrees, and on no-collision runs the full
    output-and-state result agrees. The collision branch is coupled by the
    independent product (both flags are then `true`, so the post is satisfied
    regardless). -/
lemma lazy_query_switch_step (inp : input) :
    (lazy_query_rf inp).relE (lazy_query_rp inp)
      (fun σ₁ σ₂ => σ₁ = σ₂ ∧ prp_bad.get σ₁ = false)
      (fun u v => prp_bad.get u.2 = prp_bad.get v.2
        ∧ (prp_bad.get u.2 = false → u = v)) := by
  refine ProgramDenotation.relE.of_coupling ?_
  rintro σ₁ σ₂ ⟨rfl, hflag⟩
  cases hc : random_oracle_state.get σ₁ inp with
  | some x =>
    exact ProgramDenotation.Coupling.of_pure (x, σ₁) (x, σ₁)
      (fun F => lazy_query_rf_wp_hit hc F)
      (fun G => lazy_query_rp_wp_hit hc G)
      ⟨rfl, fun _ => rfl⟩
  | none =>
    have hb_rf : ∀ y : output, prp_bad.get (random_oracle_state.set
        (fun k => if k = inp then some y else random_oracle_state.get σ₁ k)
        (prp_bad.set true σ₁)) = true := fun y => by
      rw [prp_bad.get_of_disjoint_set random_oracle_state, prp_bad.set_get]
    refine
      { w := (SubProbability.uniform : SubProbability output) >>= fun y =>
          if y ∈ colliding_outputs (random_oracle_state.get σ₁) inp then
            rp_resample_sub (random_oracle_state.get σ₁) inp y >>= fun y' =>
              (pure
                ((y, random_oracle_state.set
                      (fun k => if k = inp then some y else random_oracle_state.get σ₁ k)
                      (prp_bad.set true σ₁)),
                 (y', random_oracle_state.set
                      (fun k => if k = inp then some y' else random_oracle_state.get σ₁ k)
                      (prp_bad.set true σ₁)))
                : SubProbability ((output × state) × (output × state)))
          else
            (pure
              ((y, random_oracle_state.set
                    (fun k => if k = inp then some y else random_oracle_state.get σ₁ k) σ₁),
               (y, random_oracle_state.set
                    (fun k => if k = inp then some y else random_oracle_state.get σ₁ k) σ₁))
              : SubProbability ((output × state) × (output × state)))
        marg₁ := ?_, marg₂ := ?_, supp := ?_ }
    · intro F
      rw [SubProbability.expected_bind, uniform_expected, lazy_query_rf_wp_miss hc]
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      by_cases hbb : y ∈ colliding_outputs (random_oracle_state.get σ₁) inp
      · simp only [if_pos hbb, SubProbability.expected_bind, expected_pure]
        exact rp_resample_sub_expected_const _ _ _ _
      · simp only [if_neg hbb, expected_pure]
    · intro G
      rw [SubProbability.expected_bind, uniform_expected, lazy_query_rp_wp_miss hc]
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      by_cases hbb : y ∈ colliding_outputs (random_oracle_state.get σ₁) inp
      · simp only [if_pos hbb, SubProbability.expected_bind, expected_pure]
      · simp only [if_neg hbb, expected_pure]
    · intro f hf
      rw [SubProbability.expected_bind]
      refine Eq.trans
        (SubProbability.expected_congr _ (g := fun _ : output => (0 : ENNReal)) (fun y => ?_))
        (SubProbability.expected_zero _)
      by_cases hbb : y ∈ colliding_outputs (random_oracle_state.get σ₁) inp
      · simp only [if_pos hbb]
        rw [SubProbability.expected_bind]
        refine Eq.trans
          (SubProbability.expected_congr _ (g := fun _ : output => (0 : ENNReal)) (fun y' => ?_))
          (SubProbability.expected_zero _)
        rw [expected_pure]
        apply hf
        exact ⟨by rw [hb_rf y, hb_rf y'],
          fun hcontra => by rw [hb_rf y] at hcontra; exact absurd hcontra (by decide)⟩
      · simp only [if_neg hbb, expected_pure]
        exact hf _ ⟨rfl, fun _ => rfl⟩

/-! ### Unary facts: mass one and flag preservation (Phase 3a)

These feed the *flag-set* mode of the loop body, where the two games have
already diverged and are coupled only through `rel.of_unary`: each side
independently keeps `prp_bad = true` (with full mass). -/

/-- Setting `random_oracle_state` doesn't change the flag. -/
lemma prp_bad_get_ro_set (g : input → Option output) (σ : state) :
    prp_bad.get (random_oracle_state.set g σ) = prp_bad.get σ :=
  prp_bad.get_of_disjoint_set random_oracle_state g σ

/-- After setting the flag then the RO, the flag is `true`. -/
lemma prp_bad_get_ro_set_true (g : input → Option output) (σ : state) :
    prp_bad.get (random_oracle_state.set g (prp_bad.set true σ)) = true := by
  rw [prp_bad_get_ro_set, prp_bad.set_get]

/-- `lazy_query_rf` is lossless. -/
lemma lazy_query_rf_mass_one (inp : input) (σ : state) :
    (lazy_query_rf inp).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  cases hc : random_oracle_state.get σ inp with
  | some x => rw [lazy_query_rf_wp_hit hc]
  | none => rw [lazy_query_rf_wp_miss hc]; exact sum_const_div_card 1

/-- `lazy_query_rp` is lossless. -/
lemma lazy_query_rp_mass_one (inp : input) (σ : state) :
    (lazy_query_rp inp).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  cases hc : random_oracle_state.get σ inp with
  | some x => rw [lazy_query_rp_wp_hit hc]
  | none =>
    rw [lazy_query_rp_wp_miss hc]
    refine Eq.trans (Finset.sum_congr rfl (fun y _ => ?_)) (sum_const_div_card 1)
    by_cases hb : y ∈ colliding_outputs (random_oracle_state.get σ) inp
    · rw [if_pos hb, rp_resample_sub_expected_const]
    · rw [if_neg hb]

/-- `lazy_query_rf` keeps `prp_bad = true`. -/
lemma lazy_query_rf_keeps_flag {inp : input} {σ : state} (h : prp_bad.get σ = true) :
    (lazy_query_rf inp).wp
      (fun u => if prp_bad.get u.2 = true then (0 : ENNReal) else 1) σ = 0 := by
  cases hc : random_oracle_state.get σ inp with
  | some x => rw [lazy_query_rf_wp_hit hc]; simp only [h, if_true]
  | none =>
    rw [lazy_query_rf_wp_miss hc]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [if_pos ?_, ENNReal.zero_div]
    by_cases hb : y ∈ colliding_outputs (random_oracle_state.get σ) inp
    · rw [if_pos hb, prp_bad_get_ro_set_true]
    · rw [if_neg hb, prp_bad_get_ro_set, h]

/-- `lazy_query_rp` keeps `prp_bad = true` (with full mass). -/
lemma lazy_query_rp_keeps_flag {inp : input} {σ : state} (h : prp_bad.get σ = true) :
    (lazy_query_rp inp).wp
      (fun u => if prp_bad.get u.2 = true then (1 : ENNReal) else 0) σ = 1 := by
  cases hc : random_oracle_state.get σ inp with
  | some x => rw [lazy_query_rp_wp_hit hc]; simp only [h, if_true]
  | none =>
    rw [lazy_query_rp_wp_miss hc]
    refine Eq.trans (Finset.sum_congr rfl (fun y _ => ?_)) (sum_const_div_card 1)
    by_cases hb : y ∈ colliding_outputs (random_oracle_state.get σ) inp
    · rw [if_pos hb]
      congr 1
      refine Eq.trans
        (SubProbability.expected_congr _ (g := fun _ => (1 : ENNReal)) (fun y' => ?_)) ?_
      · rw [if_pos (prp_bad_get_ro_set_true _ _)]
      · exact rp_resample_sub_expected_const _ _ _ _
    · rw [if_neg hb, if_pos (by rw [prp_bad_get_ro_set]; exact h)]

/-! ### Two-mode relational lifting (Phase 3b) -/

/-- A program that doesn't touch `prp_bad` almost surely keeps it `true`. -/
lemma wp_keeps_flag_zero {α : Type} {prog : ProgramDenotation state α}
    (hpres : prog.inRange prp_bad.compl.range) {σ : state} (h : prp_bad.get σ = true) :
    prog.wp (fun u => if prp_bad.get u.2 = true then (0 : ENNReal) else 1) σ = 0 := by
  have hle := ProgramDenotation.wp_le_of_factors prp_bad hpres
    (P := fun σ' => if prp_bad.get σ' = true then (0 : ENNReal) else 1)
    (fun _ _ hss => by simp only [hss]) σ
  rw [if_pos h] at hle
  exact le_zero_iff.mp hle

/-- From losslessness and a.s.-flag-preservation, the full-mass flag form. -/
lemma flag_one_of_zero {α : Type} {prog : ProgramDenotation state α} {σ : state}
    (hmass : prog.wp (fun _ => (1 : ENNReal)) σ = 1)
    (hzero : prog.wp (fun u => if prp_bad.get u.2 = true then (0 : ENNReal) else 1) σ = 0) :
    prog.wp (fun u => if prp_bad.get u.2 = true then (1 : ENNReal) else 0) σ = 1 := by
  have hadd := ProgramDenotation.wp_add prog
    (fun u => if prp_bad.get u.2 = true then (1 : ENNReal) else 0)
    (fun u => if prp_bad.get u.2 = true then (0 : ENNReal) else 1) σ
  rw [show (fun u : α × state => (if prp_bad.get u.2 = true then (1 : ENNReal) else 0)
        + (if prp_bad.get u.2 = true then (0 : ENNReal) else 1)) = fun _ => 1 from by
      funext u; by_cases hb : prp_bad.get u.2 = true <;> simp [hb]] at hadd
  rw [hmass, hzero, add_zero] at hadd
  exact hadd.symm

/-- **Two-mode relational lifting.** For two programs over `state` related by a
    precondition that (a) forces flag agreement and (b) when the flag is clear
    forces synchronization (`h_sync_*`), the judgment lifts to the conditional
    invariant. The flag-clear mode is given directly; the flag-set mode uses
    `rel.of_unary` (each side independently keeps `prp_bad` set). -/
lemma two_mode_relE {α : Type} {p q : ProgramDenotation state α}
    {Pre : state → state → Prop} {Post : α × state → α × state → Prop}
    (h_flageq : ∀ σ₁ σ₂, Pre σ₁ σ₂ → prp_bad.get σ₁ = prp_bad.get σ₂)
    (h_sync_fwd : p.rel q (fun σ₁ σ₂ => Pre σ₁ σ₂ ∧ prp_bad.get σ₁ = false) Post)
    (h_sync_bwd : q.rel p (fun σ₂ σ₁ => Pre σ₁ σ₂ ∧ prp_bad.get σ₁ = false)
        (fun v u => Post u v))
    (h_p0 : ∀ σ, prp_bad.get σ = true →
        p.wp (fun u => if prp_bad.get u.2 = true then (0 : ENNReal) else 1) σ = 0)
    (h_p1 : ∀ σ, prp_bad.get σ = true →
        p.wp (fun u => if prp_bad.get u.2 = true then (1 : ENNReal) else 0) σ = 1)
    (h_q0 : ∀ σ, prp_bad.get σ = true →
        q.wp (fun u => if prp_bad.get u.2 = true then (0 : ENNReal) else 1) σ = 0)
    (h_q1 : ∀ σ, prp_bad.get σ = true →
        q.wp (fun u => if prp_bad.get u.2 = true then (1 : ENNReal) else 0) σ = 1)
    (h_post_true : ∀ u v, prp_bad.get u.2 = true → prp_bad.get v.2 = true → Post u v) :
    p.relE q Pre Post := by
  have hbool : ∀ b : Bool, ¬ (b = false) → b = true := by decide
  constructor
  · intro F G hFG σ₁ σ₂ hpre
    by_cases hf : prp_bad.get σ₁ = false
    · exact h_sync_fwd F G hFG σ₁ σ₂ ⟨hpre, hf⟩
    · have hf1 : prp_bad.get σ₁ = true := hbool _ hf
      have hf2 : prp_bad.get σ₂ = true := (h_flageq σ₁ σ₂ hpre) ▸ hf1
      have hun : p.rel q (fun a b => prp_bad.get a = true ∧ prp_bad.get b = true)
          (fun u v => prp_bad.get u.2 = true ∧ prp_bad.get v.2 = true) :=
        ProgramDenotation.rel.of_unary (fun a _ hab => h_p0 a hab.1) (fun _ b hab => h_q1 b hab.2)
      exact hun.wp_le (fun u v huv => hFG u v (h_post_true u v huv.1 huv.2)) ⟨hf1, hf2⟩
  · intro F G hFG σ₂ σ₁ hpre
    by_cases hf : prp_bad.get σ₁ = false
    · exact h_sync_bwd F G hFG σ₂ σ₁ ⟨hpre, hf⟩
    · have hf1 : prp_bad.get σ₁ = true := hbool _ hf
      have hf2 : prp_bad.get σ₂ = true := (h_flageq σ₁ σ₂ hpre) ▸ hf1
      have hun : q.rel p (fun b a => prp_bad.get b = true ∧ prp_bad.get a = true)
          (fun v u => prp_bad.get v.2 = true ∧ prp_bad.get u.2 = true) :=
        ProgramDenotation.rel.of_unary (fun b _ hab => h_q0 b hab.1) (fun _ a hab => h_p1 a hab.2)
      exact hun.wp_le (fun v u hvu => hFG v u (h_post_true u v hvu.2 hvu.1)) ⟨hf2, hf1⟩

/-- `lazy_query_rp` a.s. keeps `prp_bad = true`. -/
lemma lazy_query_rp_keeps_flag_zero {inp : input} {σ : state} (h : prp_bad.get σ = true) :
    (lazy_query_rp inp).wp
      (fun u => if prp_bad.get u.2 = true then (0 : ENNReal) else 1) σ = 0 := by
  cases hc : random_oracle_state.get σ inp with
  | some x => rw [lazy_query_rp_wp_hit hc]; simp only [h, if_true]
  | none =>
    rw [lazy_query_rp_wp_miss hc]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [ENNReal.div_eq_zero_iff]
    refine Or.inl ?_
    by_cases hb : y ∈ colliding_outputs (random_oracle_state.get σ) inp
    · rw [if_pos hb]
      refine Eq.trans
        (SubProbability.expected_congr _ (g := fun _ : output => (0 : ENNReal)) (fun y' => ?_)) ?_
      · rw [if_pos (prp_bad_get_ro_set_true _ _)]
      · exact SubProbability.expected_zero _
    · rw [if_neg hb, if_pos (by rw [prp_bad_get_ro_set]; exact h)]

/-- `lazy_query_rf` keeps `prp_bad = true` with full mass. -/
lemma lazy_query_rf_keeps_flag_one {inp : input} {σ : state} (h : prp_bad.get σ = true) :
    (lazy_query_rf inp).wp
      (fun u => if prp_bad.get u.2 = true then (1 : ENNReal) else 0) σ = 1 :=
  flag_one_of_zero (lazy_query_rf_mass_one inp σ) (lazy_query_rf_keeps_flag h)

/-! ### The loop body preserves the conditional invariant (Phase 3b) -/

/-- **The switching loop body relates RF to RP at the conditional invariant.**
    `oracle_step A` with the RF oracle relates to the same with the RP oracle:
    the flag always agrees, and as long as it is clear the states stay equal.
    Requires `A` to leave `prp_bad` untouched and to be lossless. -/
lemma oracle_step_switch_relE (A : ProgramDenotation state Unit)
    (hA_pres : A.inRange prp_bad.compl.range)
    (hA_mass : ∀ σ, A.wp (fun _ => (1 : ENNReal)) σ = 1) :
    (oracle_step A lazy_query_rf).relE (oracle_step A lazy_query_rp)
      (fun σ₁ σ₂ => prp_bad.get σ₁ = prp_bad.get σ₂ ∧ (prp_bad.get σ₁ = false → σ₁ = σ₂))
      (fun u v => prp_bad.get u.2 = prp_bad.get v.2 ∧ (prp_bad.get u.2 = false → u.2 = v.2)) := by
  have hget_pres : (ProgramDenotation.get oracle_input).inRange prp_bad.compl.range :=
    ProgramDenotation.get_inRange_compl_of_disjoint oracle_input prp_bad
  have hset_pres : ∀ y, (ProgramDenotation.set oracle_output y).inRange prp_bad.compl.range :=
    fun y => ProgramDenotation.set_inRange_compl_of_disjoint oracle_output prp_bad y
  have hget_mass : ∀ σ, (ProgramDenotation.get oracle_input).wp (fun _ => (1 : ENNReal)) σ = 1 :=
    fun σ => by simp [wp_get]
  have hset_mass : ∀ y σ, (ProgramDenotation.set oracle_output y).wp (fun _ => (1 : ENNReal)) σ =
      1 :=
    fun y σ => by simp [wp_set]
  have hptrue : ∀ {α : Type} (u v : α × state), prp_bad.get u.2 = true → prp_bad.get v.2 = true →
      prp_bad.get u.2 = prp_bad.get v.2 ∧ (prp_bad.get u.2 = false → u = v) :=
    fun u v hu hv => ⟨hu.trans hv.symm, fun hf => absurd (hu.symm.trans hf) (by decide)⟩
  -- A component
  have hA : A.relE A
      (fun σ₁ σ₂ => prp_bad.get σ₁ = prp_bad.get σ₂ ∧ (prp_bad.get σ₁ = false → σ₁ = σ₂))
      (fun u v => prp_bad.get u.2 = prp_bad.get v.2 ∧ (prp_bad.get u.2 = false → u.2 = v.2)) := by
    refine two_mode_relE (fun _ _ hpre => hpre.1) ?_ ?_
      (fun σ h => wp_keeps_flag_zero hA_pres h)
      (fun σ h => flag_one_of_zero (hA_mass σ) (wp_keeps_flag_zero hA_pres h))
      (fun σ h => wp_keeps_flag_zero hA_pres h)
      (fun σ h => flag_one_of_zero (hA_mass σ) (wp_keeps_flag_zero hA_pres h))
      (fun u v hu hv => ⟨hu.trans hv.symm, fun hf => absurd (hu.symm.trans hf) (by decide)⟩)
    · intro F G hFG σ₁ σ₂ hp
      obtain ⟨hpre, hf⟩ := hp
      have heq : σ₁ = σ₂ := hpre.2 hf
      subst heq
      exact ProgramDenotation.wp_le_wp_of_le A F G (fun x => hFG x x ⟨rfl, fun _ => rfl⟩) σ₁
    · intro F G hFG σ₂ σ₁ hp
      obtain ⟨hpre, hf⟩ := hp
      have heq : σ₁ = σ₂ := hpre.2 hf
      subst heq
      exact ProgramDenotation.wp_le_wp_of_le A F G (fun x => hFG x x ⟨rfl, fun _ => rfl⟩) σ₁
  -- get oracle_input component
  have hGet : (ProgramDenotation.get oracle_input).relE (ProgramDenotation.get oracle_input)
      (fun σ₁ σ₂ => prp_bad.get σ₁ = prp_bad.get σ₂ ∧ (prp_bad.get σ₁ = false → σ₁ = σ₂))
      (fun u v => prp_bad.get u.2 = prp_bad.get v.2 ∧ (prp_bad.get u.2 = false → u = v)) := by
    refine two_mode_relE (fun _ _ hpre => hpre.1) ?_ ?_
      (fun σ h => wp_keeps_flag_zero hget_pres h)
      (fun σ h => flag_one_of_zero (hget_mass σ) (wp_keeps_flag_zero hget_pres h))
      (fun σ h => wp_keeps_flag_zero hget_pres h)
      (fun σ h => flag_one_of_zero (hget_mass σ) (wp_keeps_flag_zero hget_pres h))
      (fun u v hu hv => hptrue u v hu hv)
    · intro F G hFG σ₁ σ₂ hp
      obtain ⟨hpre, hf⟩ := hp
      have heq : σ₁ = σ₂ := hpre.2 hf
      subst heq
      exact ProgramDenotation.wp_le_wp_of_le _ F G (fun x => hFG x x ⟨rfl, fun _ => rfl⟩) σ₁
    · intro F G hFG σ₂ σ₁ hp
      obtain ⟨hpre, hf⟩ := hp
      have heq : σ₁ = σ₂ := hpre.2 hf
      subst heq
      exact ProgramDenotation.wp_le_wp_of_le _ F G (fun x => hFG x x ⟨rfl, fun _ => rfl⟩) σ₁
  -- oracle component (rf inp₁ vs rp inp₂)
  have hOracle : ∀ inp₁ inp₂, (lazy_query_rf inp₁).relE (lazy_query_rp inp₂)
      (fun τ₁ τ₂ => prp_bad.get τ₁ = prp_bad.get τ₂
        ∧ (prp_bad.get τ₁ = false → (inp₁, τ₁) = (inp₂, τ₂)))
      (fun u v => prp_bad.get u.2 = prp_bad.get v.2 ∧ (prp_bad.get u.2 = false → u = v)) := by
    intro inp₁ inp₂
    refine two_mode_relE (fun _ _ hpre => hpre.1) ?_ ?_
      (fun σ h => lazy_query_rf_keeps_flag h)
      (fun σ h => lazy_query_rf_keeps_flag_one h)
      (fun σ h => lazy_query_rp_keeps_flag_zero h)
      (fun σ h => lazy_query_rp_keeps_flag h)
      (fun u v hu hv => hptrue u v hu hv)
    · intro F G hFG σ₁ σ₂ hp
      obtain ⟨hpre, hf⟩ := hp
      obtain ⟨hinp, hst⟩ := Prod.mk.inj (hpre.2 hf)
      subst hinp; subst hst
      exact (lazy_query_switch_step inp₁).1 F G hFG σ₁ σ₁ ⟨rfl, hf⟩
    · intro F G hFG σ₂ σ₁ hp
      obtain ⟨hpre, hf⟩ := hp
      obtain ⟨hinp, hst⟩ := Prod.mk.inj (hpre.2 hf)
      subst hinp; subst hst
      exact (lazy_query_switch_step inp₁).2 F G hFG σ₁ σ₁ ⟨rfl, hf⟩
  -- set oracle_output component
  have hSet : ∀ y₁ y₂, (ProgramDenotation.set oracle_output y₁).relE (ProgramDenotation.set
      oracle_output y₂)
      (fun τ₁ τ₂ => prp_bad.get τ₁ = prp_bad.get τ₂
        ∧ (prp_bad.get τ₁ = false → (y₁, τ₁) = (y₂, τ₂)))
      (fun u v => prp_bad.get u.2 = prp_bad.get v.2 ∧ (prp_bad.get u.2 = false → u.2 = v.2)) := by
    intro y₁ y₂
    refine two_mode_relE (fun _ _ hpre => hpre.1) ?_ ?_
      (fun σ h => wp_keeps_flag_zero (hset_pres y₁) h)
      (fun σ h => flag_one_of_zero (hset_mass y₁ σ) (wp_keeps_flag_zero (hset_pres y₁) h))
      (fun σ h => wp_keeps_flag_zero (hset_pres y₂) h)
      (fun σ h => flag_one_of_zero (hset_mass y₂ σ) (wp_keeps_flag_zero (hset_pres y₂) h))
      (fun u v hu hv => ⟨hu.trans hv.symm, fun hf => absurd (hu.symm.trans hf) (by decide)⟩)
    · intro F G hFG σ₁ σ₂ hp
      obtain ⟨hpre, hf⟩ := hp
      obtain ⟨hy, hst⟩ := Prod.mk.inj (hpre.2 hf)
      subst hy; subst hst
      exact ProgramDenotation.wp_le_wp_of_le _ F G (fun x => hFG x x ⟨rfl, fun _ => rfl⟩) σ₁
    · intro F G hFG σ₂ σ₁ hp
      obtain ⟨hpre, hf⟩ := hp
      obtain ⟨hy, hst⟩ := Prod.mk.inj (hpre.2 hf)
      subst hy; subst hst
      exact ProgramDenotation.wp_le_wp_of_le _ F G (fun x => hFG x x ⟨rfl, fun _ => rfl⟩) σ₁
  -- assemble the body via relE.bind
  unfold oracle_step
  refine ProgramDenotation.relE.bind hA (fun _ _ => ?_)
  refine ProgramDenotation.relE.bind hGet (fun inp₁ inp₂ => ?_)
  exact ProgramDenotation.relE.bind (hOracle inp₁ inp₂) (fun y₁ y₂ => hSet y₁ y₂)

/-! ### Loop lifting and the Fundamental Lemma (Phase 3c) -/

/-- The whole `q`-round game relates RF to RP at the conditional invariant. -/
lemma loop_switch_relE (A : ProgramDenotation state Unit)
    (hA_pres : A.inRange prp_bad.compl.range)
    (hA_mass : ∀ σ, A.wp (fun _ => (1 : ENNReal)) σ = 1) (q : ℕ) :
    (loop_n q (oracle_step A lazy_query_rf)).relE (loop_n q (oracle_step A lazy_query_rp))
      (fun σ₁ σ₂ => prp_bad.get σ₁ = prp_bad.get σ₂ ∧ (prp_bad.get σ₁ = false → σ₁ = σ₂))
      (fun u v => prp_bad.get u.2 = prp_bad.get v.2 ∧ (prp_bad.get u.2 = false → u.2 = v.2)) :=
  ProgramDenotation.relE.loop_n (oracle_step_switch_relE A hA_pres hA_mass) q

/-- **Switching inequality (Fundamental Lemma).** For any state-functional `G`,
    the RF game's expectation is at most the RP game's plus the probability that
    RF triggered a collision (`prp_bad`). Starting from a common state. -/
lemma switch_up_to_bad (A : ProgramDenotation state Unit)
    (hA_pres : A.inRange prp_bad.compl.range)
    (hA_mass : ∀ σ, A.wp (fun _ => (1 : ENNReal)) σ = 1)
    (q : ℕ) (G : state → ENNReal) (σ : state) :
    (loop_n q (oracle_step A lazy_query_rf)).wp (fun u => G u.2) σ
    ≤ (loop_n q (oracle_step A lazy_query_rp)).wp (fun u => G u.2) σ
      + (loop_n q (oracle_step A lazy_query_rf)).wp
          (fun u => if prp_bad.get u.2 = true then G u.2 else 0) σ := by
  classical
  have hEq := (loop_switch_relE A hA_pres hA_mass q).conseq
    (Pre' := (Eq : state → state → Prop))
    (fun σ₁ σ₂ h => ⟨congrArg _ h, fun _ => h⟩) (fun _ _ h => h)
  exact ProgramDenotation.relE.up_to_bad (bad := fun σ => prp_bad.get σ = true) (fun u => G u.2) hEq
    (fun x y hxy => by rw [hxy.1])
    (fun x y hxy hb => by
      rw [Bool.not_eq_true] at hb
      rw [hxy.2 hb])
    σ

/-! ### Bounding the bad event (Phase 4) -/

/-- Caching a fresh input grows the RO size by exactly one (independent of any
    disjoint scratch state in the base). -/
lemma RO_size_set_upd_fresh {x : input} {σ : state}
    (hc : random_oracle_state.get σ x = none) (y : output) (τ : state) :
    RO_size (random_oracle_state.set
      (fun k => if k = x then some y else random_oracle_state.get σ k) τ)
      = RO_size σ + 1 := by
  classical
  unfold RO_size
  rw [random_oracle_state.set_get]
  have hfilter : Finset.filter
        (fun k => ((fun k' => if k' = x then some y else random_oracle_state.get σ k') k).isSome)
        Finset.univ
      = insert x (Finset.filter (fun k => (random_oracle_state.get σ k).isSome) Finset.univ) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hk : k = x
    · subst hk; simp
    · simp [hk]
  rw [hfilter, Finset.card_insert_of_notMem (by simp [Finset.mem_filter, hc])]

/-- One RF query grows the expected RO size by at most one. -/
lemma lazy_query_rf_RO_size_step (x : input) (σ : state) :
    (lazy_query_rf x).wp (fun u => (RO_size u.2 : ENNReal)) σ ≤ (RO_size σ : ENNReal) + 1 := by
  cases hc : random_oracle_state.get σ x with
  | some v => rw [lazy_query_rf_wp_hit hc]; exact le_self_add
  | none =>
    rw [lazy_query_rf_wp_miss hc]
    refine le_of_eq (Eq.trans (Finset.sum_congr rfl (fun y _ => ?_))
      (sum_const_div_card ((RO_size σ : ENNReal) + 1)))
    congr 1
    by_cases hb : y ∈ colliding_outputs (random_oracle_state.get σ) x
    · rw [if_pos hb, RO_size_set_upd_fresh hc y]; push_cast; ring
    · rw [if_neg hb, RO_size_set_upd_fresh hc y]; push_cast; ring

/-- One RF query bumps the bad-flag indicator by at most `RO_size σ / N`: the
    flag flips only when the fresh draw lands in the (≤ `RO_size`)-element
    collision set. -/
lemma lazy_query_rf_bad_step (x : input) (σ : state) :
    (lazy_query_rf x).wp (fun u => if prp_bad.get u.2 = true then (1 : ENNReal) else 0) σ
    ≤ (if prp_bad.get σ = true then (1 : ENNReal) else 0)
      + (RO_size σ : ENNReal) / Fintype.card output := by
  cases hc : random_oracle_state.get σ x with
  | some v => rw [lazy_query_rf_wp_hit hc]; exact le_self_add
  | none =>
    rw [lazy_query_rf_wp_miss hc]
    refine le_trans (Finset.sum_le_sum (g := fun y : output =>
        ((if prp_bad.get σ = true then (1 : ENNReal) else 0)
          + (if y ∈ colliding_outputs (random_oracle_state.get σ) x then (1 : ENNReal) else 0))
          / Fintype.card output) (fun y _ => ?_)) ?_
    · -- pointwise: bad_ind(rf-state y) ≤ bad_ind σ + (y ∈ colliding ? 1 : 0)
      apply ENNReal.div_le_div_right
      by_cases hb : y ∈ colliding_outputs (random_oracle_state.get σ) x
      · rw [if_pos hb, prp_bad_get_ro_set_true, if_pos hb, if_pos rfl]
        exact le_add_self
      · rw [if_neg hb, prp_bad_get_ro_set, if_neg hb, add_zero]
    · -- ∑ (bad_ind σ + ind_y)/N = bad_ind σ + |colliding|/N ≤ bad_ind σ + RO_size σ/N
      rw [show (fun y : output => ((if prp_bad.get σ = true then (1 : ENNReal) else 0)
              + (if y ∈ colliding_outputs (random_oracle_state.get σ) x then (1 : ENNReal) else 0))
              / Fintype.card output)
            = (fun y => (if prp_bad.get σ = true then (1 : ENNReal) else 0) / Fintype.card output
              + (if y ∈ colliding_outputs (random_oracle_state.get σ) x then (1 : ENNReal) else 0)
                / Fintype.card output) from by funext y; rw [ENNReal.add_div]]
      rw [Finset.sum_add_distrib, sum_const_div_card]
      gcongr
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      gcongr
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact_mod_cast inducing_set_card_le_RO_size x σ

/-- Generic `oracle_step` potential bump, parameterized by the oracle (the
    `lazy_query`-specific `oracle_step_wp_indicator_bump` adapted). -/
lemma oracle_step_bump_gen {A : ProgramDenotation state Unit} (oracle : input → ProgramDenotation
    state output)
    {f : state → ENNReal} (c : state → ENNReal)
    (h_adv_f : ∀ σ, A.wp (fun yσ : Unit × state => f yσ.2) σ ≤ f σ)
    (h_adv_c : ∀ σ, A.wp (fun yσ : Unit × state => c yσ.2) σ ≤ c σ)
    (h_set_oo : ∀ y σ, f (oracle_output.set y σ) = f σ)
    (h_oracle : ∀ x σ, (oracle x).wp (fun yσ : output × state => f yσ.2) σ ≤ f σ + c σ)
    (σ : state) :
    (oracle_step A oracle).wp (fun yσ : Unit × state => f yσ.2) σ ≤ f σ + c σ := by
  show (A >>= fun _ =>
        ProgramDenotation.get oracle_input >>= fun inp =>
          oracle inp >>= fun y => ProgramDenotation.set oracle_output y).wp _ σ ≤ _
  rw [wp_bind]
  have h_inner : ∀ σ_a : state,
      (ProgramDenotation.get oracle_input >>= fun inp =>
        oracle inp >>= fun y => ProgramDenotation.set oracle_output y).wp
          (fun yσ : Unit × state => f yσ.2) σ_a ≤ f σ_a + c σ_a := by
    intro σ_a
    simp only [wp_bind, wp_get]
    rw [show (fun yσ : output × state =>
              (ProgramDenotation.set oracle_output yσ.1).wp (fun yσ' : Unit × state => f yσ'.2)
                  yσ.2)
            = (fun yσ : output × state => f yσ.2) from by
      funext yσ; rw [wp_set]; exact h_set_oo yσ.1 yσ.2]
    exact h_oracle (oracle_input.get σ_a) σ_a
  calc A.wp _ σ
      ≤ A.wp (fun yσ : Unit × state => f yσ.2 + c yσ.2) σ := by
        apply ProgramDenotation.wp_le_wp_of_le; intro yσ; exact h_inner yσ.2
    _ = A.wp (fun yσ : Unit × state => f yσ.2) σ + A.wp (fun yσ : Unit × state => c yσ.2) σ := by
        rw [ProgramDenotation.wp_add]
    _ ≤ f σ + c σ := add_le_add (h_adv_f σ) (h_adv_c σ)

/-- One loop body bumps `RO_size` by at most one. -/
lemma oracle_step_rf_size_bump {A : ProgramDenotation state Unit}
    (hA_ro : A.inRange random_oracle_state.compl.range)
    (hA_mass : ∀ σ, A.wp (fun _ => (1 : ENNReal)) σ = 1) (σ : state) :
    (oracle_step A lazy_query_rf).wp (fun u => (RO_size u.2 : ENNReal)) σ
    ≤ (RO_size σ : ENNReal) + 1 := by
  have h := oracle_step_bump_gen lazy_query_rf (fun _ => 1)
    (fun σ' => ProgramDenotation.wp_le_of_factors random_oracle_state hA_ro
      (fun _ _ hss => congrArg _ (RO_size_of_get_eq hss)) σ')
    (fun σ' => le_of_eq (hA_mass σ'))
    (fun y σ' => by rw [RO_size_set_disjoint oracle_output y σ'])
    lazy_query_rf_RO_size_step σ
  simpa using h

/-- One loop body bumps the bad-flag indicator by at most `RO_size σ / N`. -/
lemma oracle_step_rf_bad_bump {A : ProgramDenotation state Unit}
    (hA_ro : A.inRange random_oracle_state.compl.range)
    (hA_pres : A.inRange prp_bad.compl.range) (σ : state) :
    (oracle_step A lazy_query_rf).wp
      (fun u => if prp_bad.get u.2 = true then (1 : ENNReal) else 0) σ
    ≤ (if prp_bad.get σ = true then (1 : ENNReal) else 0)
      + (RO_size σ : ENNReal) / Fintype.card output :=
  oracle_step_bump_gen lazy_query_rf (fun σ' => (RO_size σ' : ENNReal) / Fintype.card output)
    (fun σ' => ProgramDenotation.wp_le_of_factors prp_bad hA_pres
      (P := fun s => if prp_bad.get s = true then (1 : ENNReal) else 0)
      (fun _ _ hss => by simp only [hss]) σ')
    (fun σ' => ProgramDenotation.wp_le_of_factors random_oracle_state hA_ro
      (P := fun s => (RO_size s : ENNReal) / Fintype.card output)
      (fun _ _ hss => by simp only [RO_size_of_get_eq hss]) σ')
    (fun y σ' => by simp only [prp_bad.get_of_disjoint_set oracle_output])
    lazy_query_rf_bad_step σ

/-! ### The switching lemma (Phase 4) -/

/-- **Bad-event bound.** Starting from a clean state (flag clear, empty oracle),
    the probability that `q` RF rounds set `prp_bad` is at most `q(q−1)/2N`. The
    bad flag is itself a collision potential, so this is `loop_n_birthday_bound`
    applied directly. -/
lemma loop_rf_bad_bound {A : ProgramDenotation state Unit}
    (hA_ro : A.inRange random_oracle_state.compl.range)
    (hA_pres : A.inRange prp_bad.compl.range)
    (hA_mass : ∀ σ, A.wp (fun _ => (1 : ENNReal)) σ = 1)
    (q : ℕ) (σ : state) (h_flag : prp_bad.get σ = false) (h_size0 : RO_size σ = 0) :
    (loop_n q (oracle_step A lazy_query_rf)).wp
      (fun u => if prp_bad.get u.2 = true then (1 : ENNReal) else 0) σ
    ≤ ((q : ENNReal) * ((q : ENNReal) - 1)) / (2 * Fintype.card output) := by
  have hb := loop_n_birthday_bound (oracle_step A lazy_query_rf)
    (fun σ' => if prp_bad.get σ' = true then (1 : ENNReal) else 0) RO_size (Fintype.card output)
    (by exact_mod_cast Fintype.card_pos.ne') (ENNReal.natCast_ne_top _)
    (oracle_step_rf_bad_bump hA_ro hA_pres) (oracle_step_rf_size_bump hA_ro hA_mass) q σ
  refine le_trans hb ?_
  simp [h_flag, h_size0]

/-- **PRP/PRF switching lemma.** For a distinguisher `A` (touching neither the
    oracle table nor the internal flag, and lossless) outputting a `[0,1]`-valued
    functional `G`, the RF and RP games differ by at most `q(q−1)/2N`:

    `Pr[A^RF : G] ≤ Pr[A^RP : G] + q(q−1)/2N`.

    Combines the Fundamental Lemma (`switch_up_to_bad`) with the birthday bound
    on the bad event (`loop_rf_bad_bound`). -/
theorem switching_lemma {A : ProgramDenotation state Unit}
    (hA_ro : A.inRange random_oracle_state.compl.range)
    (hA_pres : A.inRange prp_bad.compl.range)
    (hA_mass : ∀ σ, A.wp (fun _ => (1 : ENNReal)) σ = 1)
    (q : ℕ) (G : state → ENNReal) (hG : ∀ σ, G σ ≤ 1)
    (σ : state) (h_flag : prp_bad.get σ = false) (h_size0 : RO_size σ = 0) :
    (loop_n q (oracle_step A lazy_query_rf)).wp (fun u => G u.2) σ
    ≤ (loop_n q (oracle_step A lazy_query_rp)).wp (fun u => G u.2) σ
      + ((q : ENNReal) * ((q : ENNReal) - 1)) / (2 * Fintype.card output) := by
  refine le_trans (switch_up_to_bad A hA_pres hA_mass q G σ) ?_
  gcongr
  refine le_trans (ProgramDenotation.wp_le_wp_of_le _ _ _ ?_ σ)
    (loop_rf_bad_bound hA_ro hA_pres hA_mass q σ h_flag h_size0)
  intro u
  by_cases hb : prp_bad.get u.2 = true
  · simp only [if_pos hb]; exact hG _
  · simp only [if_neg hb, le_refl]
