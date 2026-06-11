import PlonkLean.RO.OneWayness_GameHop.Definitions
import PlonkLean.RO.OneWayness_GameHop.GuessExperiment
import PlonkLean.RO.OneWayness_GameHop.UpToBad

/-!
# OneWayness GameHop: Game 1 reduction

This module reduces Game 1's bad event (`chal_x_queried_gh = true`) to the
abstract `guess_experiment` framework, ultimately bounding it by `(q+1)/|input|`.

## Game 1 variants

* `body_game_1`, `final_game_1` — direct query / response handlers.
* `body_recording_game_1`, `final_recording_game_1` — recording variants that
  append each query to `queries_input`.
## Correspondence (relational)

`game_1_correspondence` couples the match-tracking run to the recording
run with one pRHL invariant (see `InvG1` below); the former Game 1'
explicit-match variants and their bridge lemmas are gone.


* `game_1_correspondence` — Game 1's per-σ', t inequality (LHS ≤ RHS in
  schema form), proven by chaining: bridges → `schema_inner_equation` for
  Game 1' → reverse bridges.
* `ow_game_1_tracked_bad_le_guess_input_bound` — full bound:
  `Pr[Game 1 bad] ≤ (q+1)/|input|`.

## Flag-elision (lazy ↔ tracked)

`ow_game_1_wp_eq_ow_game_1_tracked_wp_of_flag_ignoring` — at flag-ignoring
posts, Game 1's lazy oracle and tracked oracle are wp-equivalent. Bridges
the OW theorem's "lazy" Game 1 to our "tracked" Game 1.
-/

section Game1

variable (ow_adv : Program state Unit)

/-- Body of `guess_experiment_game_1`: adv query + lazy_query_tracked
    (which internally flips chal_x_queried_gh when inp = chal_x). Doesn't
    use the bound target `x`. -/
private noncomputable def body_game_1 (_x : input) : Program state Unit := do
  ow_adv
  let inp ← Program.get oracle_input
  let y ← lazy_query_tracked inp
  Program.set oracle_output y

/-- Final of `guess_experiment_game_1`: oracle on response. Doesn't use
    the bound target. -/
private noncomputable def final_game_1 (_x : input) : Program state Unit := do
  let resp ← Program.get ow_response
  let y ← lazy_query_tracked resp
  Program.set oracle_output y

private noncomputable def guess_experiment_game_1 (q : ℕ) : Program state Bool :=
  guess_experiment lazy_init Program.uniform ow_challenge_x chal_x_queried_gh
    (body_game_1 ow_adv) (final_game_1) q


/-- Helper: the chal_y block + trailing `pure (decide (y_check = y))` (which
    uses the outer-bound y) absorbs into NEW_POST for chal_xqg-reading posts.
    Used for G2 bad-event reduction. -/
private lemma chal_y_block_pure_decide_eliminate
    (k : Program state output)
    (h_k : k.inRange ow_challenge_y.compl.range)
    (σ : state) :
    ((Program.uniform : Program state output) >>= fun y =>
      Program.set ow_challenge_y y >>= fun _ =>
      k >>= fun y_check => pure (decide (y_check = y))).wp
      (fun bσ : Bool × state => if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
    = k.wp (fun aσ : output × state =>
        if chal_x_queried_gh.get aσ.2 = true then (1 : ENNReal) else 0) σ := by
  rw [wp_bind, wp_uniform]
  -- For each y, the inner reduces to k.wp NEW_POST σ.
  have h_inner : ∀ y, (Program.set ow_challenge_y y >>= fun _ =>
      k >>= fun y_check => pure (decide (y_check = y))).wp
      (fun bσ : Bool × state => if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
      = k.wp (fun aσ : output × state =>
        if chal_x_queried_gh.get aσ.2 = true then (1 : ENNReal) else 0) σ := by
    intro y
    rw [wp_bind, wp_set, wp_bind]
    -- Goal: k.wp (fun aσ => (pure (decide aσ.1 = y)).wp F_chal_xqg aσ.2) (chal_y.set y σ)
    --       = k.wp NEW_POST σ.
    -- Simplify the post via wp_pure: F_chal_xqg ignores Bool.
    have h_post_eq :
        (fun aσ : output × state =>
          (Pure.pure (decide (aσ.1 = y)) : Program state Bool).wp
            (fun bσ : Bool × state =>
              if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) aσ.2)
        = fun aσ : output × state =>
          if chal_x_queried_gh.get aσ.2 = true then (1 : ENNReal) else 0 := by
      funext aσ
      rw [wp_pure]
    rw [h_post_eq]
    -- Goal: k.wp NEW_POST (chal_y.set y σ) = k.wp NEW_POST σ.
    have h_F : IgnoresLens ow_challenge_y
        (fun aσ' : output × state =>
          if chal_x_queried_gh.get aσ'.2 = true then (1 : ENNReal) else 0) := by
      intro aσ v
      simp only [Lens.get_of_disjoint_set chal_x_queried_gh ow_challenge_y v aσ.2]
    have h_k_wp_inv : IgnoresLens ow_challenge_y
        (fun aσ : Unit × state => k.wp
          (fun aσ' : output × state =>
            if chal_x_queried_gh.get aσ'.2 = true then (1 : ENNReal) else 0) aσ.2) :=
      IgnoresLens.comp_inRange (L := ow_challenge_y) h_F (fun _ : Unit => k)
        (fun _ => h_k)
    exact h_k_wp_inv ((), σ) y
  simp_rw [h_inner]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  exact ENNReal.div_mul_cancel
    (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

/-- **Game 2 bad-event ↔ guess_experiment_game_1 matched-event bridge.**

    `ow_game_2_tracked`'s bad event (`chal_x_queried_gh = true` at the end)
    is exactly `guess_experiment_game_1`'s matched event. Both run the same
    `lazy_query_tracked`-based loop; the prefixes and trailing operations
    differ only by chal_x_qg-invisible steps (sampling chal_y, setting
    oracle_output) that the bad-event post doesn't observe. -/
private lemma ow_game_2_tracked_bad_eq_guess_experiment_game_1
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (q : ℕ) (σ : state) :
    (ow_game_2_tracked ow_adv q).wp
        (fun bσ : Bool × state =>
          if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
    = (guess_experiment_game_1 ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  -- Common "tail" k = loop_n; get resp; lqt resp.
  set k : Program state output :=
    loop_n q (oracle_step ow_adv lazy_query_tracked) >>= fun _ =>
      Program.get ow_response >>= fun resp =>
      lazy_query_tracked resp with k_def
  -- NEW_POST: chal_xqg-reading, output-ignoring post.
  set NEW_POST : output × state → ENNReal :=
    fun aσ => if chal_x_queried_gh.get aσ.2 = true then 1 else 0
      with NEW_POST_def
  -- (b) RHS trailing absorption — generic helper inlined.
  -- For any p : Program state output:
  --   (p >>= fun y => set oo y >>= fun _ => get chal_xqg).wp F_matched σ
  --   = p.wp NEW_POST σ
  -- The absorption uses oo ⊥ chal_xqg.
  have h_trailing_absorb : ∀ (p : Program state output) (σ' : state),
      (p >>= fun y =>
          Program.set oracle_output y >>= fun _ =>
          Program.get chal_x_queried_gh).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
      = p.wp NEW_POST σ' := by
    intro p σ'
    rw [wp_bind]
    congr 1
    funext aσ
    obtain ⟨a, s'⟩ := aσ
    dsimp only
    rw [wp_bind, wp_set, wp_get]
    simp only [NEW_POST_def]
    have h_get : chal_x_queried_gh.get (oracle_output.set a s')
                = chal_x_queried_gh.get s' :=
      Lens.get_of_disjoint_set chal_x_queried_gh oracle_output a s'
    rw [h_get]
  -- View GE1 as `(prefix >>= k) >>= trailing` and apply h_trailing_absorb.
  -- For this we need GE1 = (prefix >>= k) >>= trailing as Programs. This holds
  -- up to bind_assoc rewriting.
  -- View GE1 as `(prefix >>= k) >>= trailing` via Program equality (bind_assoc).
  have h_GE1_eq : guess_experiment_game_1 ow_adv q
      = (lazy_init >>= fun _ =>
         (Program.uniform : Program state input) >>= fun x =>
         Program.set ow_challenge_x x >>= fun _ =>
         Program.set chal_x_queried_gh false >>= fun _ => k) >>=
        (fun y => Program.set oracle_output y >>= fun _ =>
                  Program.get chal_x_queried_gh) := by
    unfold guess_experiment_game_1 guess_experiment body_game_1 final_game_1
    simp only [k_def, oracle_step, Program.bind_assoc]
  have h_RHS : (guess_experiment_game_1 ow_adv q).wp
      (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
      = (lazy_init >>= fun _ =>
         (Program.uniform : Program state input) >>= fun x =>
         Program.set ow_challenge_x x >>= fun _ =>
         Program.set chal_x_queried_gh false >>= fun _ => k).wp NEW_POST σ := by
    rw [h_GE1_eq]
    exact h_trailing_absorb _ σ
  rw [h_RHS]
  -- k is chal_y-disjoint (composed from loop_n_inRange + lqt_inRange_chal_y).
  have h_k_chal_y : k.inRange ow_challenge_y.compl.range := by
    rw [k_def]
    refine Program.inRange_bind ?_ (fun _ => ?_)
    · exact loop_n_inRange _ (oracle_step_lazy_query_tracked_inRange_ow_challenge_y
        ow_adv h_ow_adv_chal_y) q
    refine Program.inRange_bind
      (Program.get_inRange_compl_of_disjoint ow_response ow_challenge_y) (fun _ => ?_)
    exact lazy_query_tracked_inRange_ow_challenge_y _
  -- (a) LHS: trailing pure-decide absorbed + chal_y block eliminated.
  have h_OG2_eq : ow_game_2_tracked ow_adv q
      = (lazy_init >>= fun _ =>
         Program.set chal_x_queried_gh false >>= fun _ =>
         (Program.uniform : Program state input) >>= fun x =>
         Program.set ow_challenge_x x) >>= fun _ =>
        ((Program.uniform : Program state output) >>= fun y =>
         Program.set ow_challenge_y y >>= fun _ =>
         k >>= fun y_check => pure (decide (y_check = y))) := by
    unfold ow_game_2_tracked
    rw [oracle_loop_n_eq_loop_n]
    simp only [k_def, Program.bind_assoc]
  have h_LHS : (ow_game_2_tracked ow_adv q).wp
      (fun bσ : Bool × state =>
        if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
      = ((lazy_init >>= fun _ =>
          Program.set chal_x_queried_gh false >>= fun _ =>
          (Program.uniform : Program state input) >>= fun x =>
          Program.set ow_challenge_x x) >>= fun _ => k).wp NEW_POST σ := by
    rw [h_OG2_eq]
    rw [wp_bind]
    conv_rhs => rw [wp_bind]
    congr 1
    funext aσ
    exact chal_y_block_pure_decide_eliminate k h_k_chal_y aσ.2
  rw [h_LHS]
  -- (c) Two prefixes equal up to `set chal_xqg false` commutation.
  have h_prefix_eq :
      ((lazy_init >>= fun _ =>
        Program.set chal_x_queried_gh false >>= fun _ =>
        (Program.uniform : Program state input) >>= fun x =>
        Program.set ow_challenge_x x) >>= (fun _ => k))
      = ((lazy_init >>= fun _ =>
          (Program.uniform : Program state input) >>= fun x =>
          Program.set ow_challenge_x x >>= fun _ =>
          Program.set chal_x_queried_gh false) >>= (fun _ => k)) := by
    simp only [Program.bind_assoc]
    congr 1
    funext _
    rw [Program.bind_uniform_comm
      (Program.set chal_x_queried_gh false) (fun x =>
        (Program.set ow_challenge_x x : Program state Unit) >>= fun _ => k)]
    congr 1
    funext x
    apply Program.ext_of_wp
    intro F
    funext σ_pre
    simp only [wp_bind, wp_set]
    congr 1
    exact ((inferInstance : disjoint chal_x_queried_gh ow_challenge_x).commute
      σ_pre false x).symm
  rw [h_prefix_eq]
  -- Final cleanup: both sides are now structurally equal modulo bind_assoc.
  simp only [Program.bind_assoc]


/-- `lazy_query_tracked` is queries_input-disjoint. -/
private lemma lazy_query_tracked_inRange_queries_input (inp : input) :
    (lazy_query_tracked inp).inRange queries_input.compl.range := by
  unfold lazy_query_tracked
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state queries_input)
  refine Program.inRange_bind ?_ (fun cx => ?_)
  · exact Program.get_inRange_compl_of_disjoint ow_challenge_x queries_input
  refine Program.inRange_bind ?_ (fun _ => Program.inRange_pure _ _)
  by_cases h : inp = cx
  · simp only [if_pos h]
    exact Program.set_inRange_compl_of_disjoint chal_x_queried_gh queries_input true
  · simp only [if_neg h]
    exact Program.inRange_pure _ _



/-- Body recording for Game 1 bad: same shape as guess_experiment_game_1.body
    but appends `inp` (adv's query) to qs. -/
private noncomputable def body_recording_game_1 (adv : Program state Unit) :
    Program state Unit := do
  adv
  let inp ← Program.get oracle_input
  let y ← lazy_query_tracked inp
  Program.set oracle_output y
  let qs ← Program.get queries_input
  Program.set queries_input (qs ++ [inp])

/-- Final recording for Game 1 bad: the last query attempt records `resp`. -/
private noncomputable def final_recording_game_1 : Program state Unit := do
  let resp ← Program.get ow_response
  let y ← lazy_query_tracked resp
  Program.set oracle_output y
  let qs ← Program.get queries_input
  Program.set queries_input (qs ++ [resp])

/-- body_recording_game_1 bumps queries_input.length by at most 1 per iteration. -/
private lemma body_recording_game_1_qs_length_bump
    (adv : Program state Unit)
    (h_adv : adv.inRange queries_input.compl.range)
    (σ : state) :
    (body_recording_game_1 adv).wp
      (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal)) σ
    ≤ ((queries_input.get σ).length : ENNReal) + 1 := by
  unfold body_recording_game_1
  rw [wp_bind]
  have h_rest_bound : ∀ σ',
      (Program.get oracle_input >>= fun inp =>
        lazy_query_tracked inp >>= fun y =>
        Program.set oracle_output y >>= fun _ =>
        Program.get queries_input >>= fun qs =>
        Program.set queries_input (qs ++ [inp])).wp
        (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal)) σ'
      ≤ ((queries_input.get σ').length : ENNReal) + 1 := by
    intro σ'
    rw [wp_bind, wp_get]
    dsimp only
    rw [wp_bind]
    have h_inner_eq : ∀ (y : output) (σ_lqt : state),
        (Program.set oracle_output y >>= fun _ =>
          Program.get queries_input >>= fun qs =>
          Program.set queries_input (qs ++ [oracle_input.get σ'])).wp
          (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal)) σ_lqt
        = ((queries_input.get σ_lqt).length : ENNReal) + 1 := by
      intro y σ_lqt
      simp only [wp_bind, wp_set, wp_get]
      simp only [Lens.get_of_disjoint_set queries_input oracle_output, Lens.set_get,
        List.length_append, List.length_singleton]
      push_cast
      ring
    refine le_trans (Program.wp_le_wp_of_le _ _
        (fun yσ : output × state => ((queries_input.get yσ.2).length : ENNReal) + 1)
        ?_ σ') ?_
    · intro yσ
      exact le_of_eq (h_inner_eq yσ.1 yσ.2)
    rw [Program.wp_add (lazy_query_tracked _)
        (fun yσ : output × state => ((queries_input.get yσ.2).length : ENNReal))
        (fun _ : output × state => (1 : ENNReal))]
    refine add_le_add ?_ ?_
    · exact Program.wp_qs_length_preserved_of_inRange queries_input
        (lazy_query_tracked _) (lazy_query_tracked_inRange_queries_input _) _
    · exact Program.wp_const_le _ _ _
  refine le_trans (Program.wp_le_wp_of_le _ _
      (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal) + 1)
      ?_ σ) ?_
  · intro aσ
    exact h_rest_bound aσ.2
  rw [Program.wp_add adv
      (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal))
      (fun _ : Unit × state => (1 : ENNReal))]
  refine add_le_add ?_ ?_
  · exact Program.wp_qs_length_preserved_of_inRange queries_input adv h_adv σ
  · exact Program.wp_const_le _ _ _

/-- final_recording_game_1 bumps queries_input.length by at most 1. -/
private lemma final_recording_game_1_qs_length_bump (σ : state) :
    final_recording_game_1.wp
      (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal)) σ
    ≤ ((queries_input.get σ).length : ENNReal) + 1 := by
  unfold final_recording_game_1
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_bind]
  have h_inner_eq : ∀ (y : output) (σ_lqt : state),
      (Program.set oracle_output y >>= fun _ =>
        Program.get queries_input >>= fun qs =>
        Program.set queries_input (qs ++ [ow_response.get σ])).wp
        (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal)) σ_lqt
      = ((queries_input.get σ_lqt).length : ENNReal) + 1 := by
    intro y σ_lqt
    simp only [wp_bind, wp_set, wp_get]
    simp only [Lens.get_of_disjoint_set queries_input oracle_output, Lens.set_get,
      List.length_append, List.length_singleton]
    push_cast
    ring
  refine le_trans (Program.wp_le_wp_of_le _ _
      (fun yσ : output × state => ((queries_input.get yσ.2).length : ENNReal) + 1)
      ?_ σ) ?_
  · intro yσ
    exact le_of_eq (h_inner_eq yσ.1 yσ.2)
  rw [Program.wp_add (lazy_query_tracked _)
      (fun yσ : output × state => ((queries_input.get yσ.2).length : ENNReal))
      (fun _ : output × state => (1 : ENNReal))]
  refine add_le_add ?_ ?_
  · exact Program.wp_qs_length_preserved_of_inRange queries_input
      (lazy_query_tracked _) (lazy_query_tracked_inRange_queries_input _) _
  · exact Program.wp_const_le _ _ _

/-! ### The relational correspondence

The match-tracking run (left: `body_game_1`, whose `lazy_query_tracked`
flips `chal_x_queried_gh` when the query equals `chal_x = t`) is coupled
to the recording run (right: `body_recording_game_1`, which appends each
query to `queries_input`) by the invariant `InvG1` below: the recording
state is the tracking state with the three bookkeeping lenses
overwritten; the left flag mirrors membership of the target in the
recorded list; the left challenge is pinned to the target. The right
flag value `m` is existential — the right run's `lazy_query_tracked`
junk-flips it against `tv = chal_x.get σ'`, and the ending overwrites it
anyway.

This one invariant replaces the entire former Game 1' apparatus (the
explicit-match variants, eight bridge lemmas, the queries-input
invisibility block, and two `maxHeartbeats` game-level conversions — see
git history). -/

/-- The Game-1 coupling invariant. -/
private abbrev InvG1 (t tv : input) (σ₁ σ₂ : state) : Prop :=
  ∃ (l : List input) (m : Bool),
    σ₂ = queries_input.set l (chal_x_queried_gh.set m (ow_challenge_x.set tv σ₁))
    ∧ chal_x_queried_gh.get σ₁ = decide (t ∈ l)
    ∧ ow_challenge_x.get σ₁ = t

/-- Reading any lens disjoint from the three bookkeeping lenses through
    the overwrite is invisible. -/
private lemma get_ovw {γ : Type} (L : Lens γ state)
    [disjoint queries_input L] [disjoint chal_x_queried_gh L]
    [disjoint ow_challenge_x L]
    (tv : input) (l : List input) (m : Bool) (σ : state) :
    L.get (queries_input.set l (chal_x_queried_gh.set m
      (ow_challenge_x.set tv σ))) = L.get σ := by
  rw [Lens.get_of_disjoint_set L queries_input,
      Lens.get_of_disjoint_set L chal_x_queried_gh,
      Lens.get_of_disjoint_set L ow_challenge_x]

/-- The right run reads `tv` as its challenge. -/
private lemma cx_ovw (tv : input) (l : List input) (m : Bool) (σ : state) :
    ow_challenge_x.get (queries_input.set l (chal_x_queried_gh.set m
      (ow_challenge_x.set tv σ))) = tv := by
  rw [Lens.get_of_disjoint_set ow_challenge_x queries_input,
      Lens.get_of_disjoint_set ow_challenge_x chal_x_queried_gh,
      ow_challenge_x.set_get]

/-- A fresh RO write commutes with the three-lens overwrite. -/
private lemma RO_write_ovw (tv inp : input) (l : List input) (m : Bool)
    (σ₁ : state) (w : output) :
    random_oracle_state.set (fun k => if k = inp then some w
      else random_oracle_state.get (queries_input.set l (chal_x_queried_gh.set m
        (ow_challenge_x.set tv σ₁))) k)
      (queries_input.set l (chal_x_queried_gh.set m (ow_challenge_x.set tv σ₁)))
    = queries_input.set l (chal_x_queried_gh.set m (ow_challenge_x.set tv
        (random_oracle_state.set (fun k => if k = inp then some w
          else random_oracle_state.get σ₁ k) σ₁))) := by
  rw [get_ovw random_oracle_state,
      (inferInstance : disjoint random_oracle_state queries_input).commute,
      (inferInstance : disjoint random_oracle_state chal_x_queried_gh).commute,
      (inferInstance : disjoint random_oracle_state ow_challenge_x).commute]

/-- Fold an `if` of applications into an application of an `if`. -/
private lemma ite_app (F : output × state → ENNReal) (v : output)
    (c : Prop) [Decidable c] (a b : state) :
    (if c then F (v, a) else F (v, b)) = F (v, if c then a else b) :=
  (apply_ite (fun s : state => F (v, s)) c a b).symm

/-- Post-state algebra shared by the hit and miss branches of the
    per-query coupling: the (asymmetric) conditional flag writes preserve
    the overwrite shape, updating the left flag to `old || (inp = t)`. -/
private lemma lqt_post_alg (t tv inp : input) (l : List input) (m : Bool)
    {τ₁ τ₂ : state}
    (hτ : τ₂ = queries_input.set l (chal_x_queried_gh.set m
      (ow_challenge_x.set tv τ₁)))
    (hf : chal_x_queried_gh.get τ₁ = decide (t ∈ l))
    (hcx : ow_challenge_x.get τ₁ = t) :
    (∃ m', (if inp = tv then chal_x_queried_gh.set true τ₂ else τ₂)
        = queries_input.set l (chal_x_queried_gh.set m'
            (ow_challenge_x.set tv
              (if inp = t then chal_x_queried_gh.set true τ₁ else τ₁))))
    ∧ chal_x_queried_gh.get
        (if inp = t then chal_x_queried_gh.set true τ₁ else τ₁)
        = (decide (t ∈ l) || decide (inp = t))
    ∧ ow_challenge_x.get
        (if inp = t then chal_x_queried_gh.set true τ₁ else τ₁) = t := by
  haveI hxq : disjoint ow_challenge_x chal_x_queried_gh :=
    disjoint_chal_x_queried_gh_ow_challenge_x.symm
  subst hτ
  refine ⟨⟨if inp = tv then true else m, ?_⟩, ?_, ?_⟩
  · by_cases hiv : inp = tv
    · by_cases hit : inp = t
      · simp only [if_pos hiv, if_pos hit]
        rw [(inferInstance : disjoint chal_x_queried_gh queries_input).commute,
            chal_x_queried_gh.set_set, hxq.commute, chal_x_queried_gh.set_set]
      · simp only [if_pos hiv, if_neg hit]
        rw [(inferInstance : disjoint chal_x_queried_gh queries_input).commute,
            chal_x_queried_gh.set_set]
    · by_cases hit : inp = t
      · simp only [if_neg hiv, if_pos hit]
        rw [hxq.commute, chal_x_queried_gh.set_set]
      · simp only [if_neg hiv, if_neg hit]
  · by_cases hit : inp = t
    · rw [if_pos hit, chal_x_queried_gh.set_get, decide_eq_true hit, Bool.or_true]
    · rw [if_neg hit, hf, decide_eq_false hit, Bool.or_false]
  · by_cases hit : inp = t
    · rw [if_pos hit, Lens.get_of_disjoint_set ow_challenge_x chal_x_queried_gh]
      exact hcx
    · rw [if_neg hit]
      exact hcx

/-- **Per-query coupling**: `lazy_query_tracked inp` on the tracking side
    relates to `lazy_query_tracked inp` on the recording side across the
    overwrite — same answer, flag updated to `old || (inp = t)` on the
    left, junk flag absorbed on the right. -/
private lemma lqt_pair_relE (t tv inp : input) (l : List input) (m : Bool) :
    (lazy_query_tracked inp).relE (lazy_query_tracked inp)
      (fun σ₁ σ₂ =>
        σ₂ = queries_input.set l (chal_x_queried_gh.set m
          (ow_challenge_x.set tv σ₁))
        ∧ chal_x_queried_gh.get σ₁ = decide (t ∈ l)
        ∧ ow_challenge_x.get σ₁ = t)
      (fun u v => u.1 = v.1
        ∧ (∃ m', v.2 = queries_input.set l (chal_x_queried_gh.set m'
            (ow_challenge_x.set tv u.2)))
        ∧ chal_x_queried_gh.get u.2 = (decide (t ∈ l) || decide (inp = t))
        ∧ ow_challenge_x.get u.2 = t) := by
  refine Program.relE.of_coupling ?_
  rintro σ₁ σ₂ ⟨rfl, hf₁, hcx₁⟩
  have hcx₂ := cx_ovw tv l m σ₁
  have hRO := get_ovw random_oracle_state tv l m σ₁
  cases hr : random_oracle_state.get σ₁ inp with
  | some v =>
    have hL : ∀ F : output × state → ENNReal,
        (lazy_query_tracked inp).wp F σ₁
        = F (v, if inp = t then chal_x_queried_gh.set true σ₁ else σ₁) := by
      intro F
      rw [wp_lqt, wp_lq_hit inp hr]
      dsimp only
      rw [hcx₁, ite_app F v]
    have hR : ∀ G : output × state → ENNReal,
        (lazy_query_tracked inp).wp G
          (queries_input.set l (chal_x_queried_gh.set m
            (ow_challenge_x.set tv σ₁)))
        = G (v, if inp = tv
            then chal_x_queried_gh.set true (queries_input.set l
              (chal_x_queried_gh.set m (ow_challenge_x.set tv σ₁)))
            else queries_input.set l (chal_x_queried_gh.set m
              (ow_challenge_x.set tv σ₁))) := by
      intro G
      rw [wp_lqt, wp_lq_hit inp (by rw [hRO]; exact hr)]
      dsimp only
      rw [hcx₂, ite_app G v]
    exact Program.Coupling.of_pure _ _ hL hR
      ⟨rfl, lqt_post_alg t tv inp l m rfl hf₁ hcx₁⟩
  | none =>
    have hL : ∀ F : output × state → ENNReal,
        (lazy_query_tracked inp).wp F σ₁
        = ∑ w : output, F (w, if inp = t
            then chal_x_queried_gh.set true (random_oracle_state.set
              (fun k => if k = inp then some w
                        else random_oracle_state.get σ₁ k) σ₁)
            else random_oracle_state.set
              (fun k => if k = inp then some w
                        else random_oracle_state.get σ₁ k) σ₁)
          / Fintype.card output := by
      intro F
      rw [wp_lqt, wp_lq_miss inp hr]
      refine Finset.sum_congr rfl fun w _ => ?_
      congr 1
      rw [show ow_challenge_x.get (random_oracle_state.set
            (fun k => if k = inp then some w
                      else random_oracle_state.get σ₁ k) σ₁) = t from by
          rw [Lens.get_of_disjoint_set ow_challenge_x random_oracle_state]
          exact hcx₁,
        ite_app F w]
    have hR : ∀ G : output × state → ENNReal,
        (lazy_query_tracked inp).wp G
          (queries_input.set l (chal_x_queried_gh.set m
            (ow_challenge_x.set tv σ₁)))
        = ∑ w : output, G (w, if inp = tv
            then chal_x_queried_gh.set true (random_oracle_state.set
              (fun k => if k = inp then some w
                        else random_oracle_state.get (queries_input.set l
                          (chal_x_queried_gh.set m (ow_challenge_x.set tv σ₁))) k)
              (queries_input.set l (chal_x_queried_gh.set m
                (ow_challenge_x.set tv σ₁))))
            else random_oracle_state.set
              (fun k => if k = inp then some w
                        else random_oracle_state.get (queries_input.set l
                          (chal_x_queried_gh.set m (ow_challenge_x.set tv σ₁))) k)
              (queries_input.set l (chal_x_queried_gh.set m
                (ow_challenge_x.set tv σ₁))))
          / Fintype.card output := by
      intro G
      rw [wp_lqt, wp_lq_miss inp (by rw [hRO]; exact hr)]
      refine Finset.sum_congr rfl fun w _ => ?_
      congr 1
      rw [show ow_challenge_x.get (random_oracle_state.set
            (fun k => if k = inp then some w
                      else random_oracle_state.get (queries_input.set l
                        (chal_x_queried_gh.set m (ow_challenge_x.set tv σ₁))) k)
            (queries_input.set l (chal_x_queried_gh.set m
              (ow_challenge_x.set tv σ₁)))) = tv from by
          rw [Lens.get_of_disjoint_set ow_challenge_x random_oracle_state]
          exact hcx₂,
        ite_app G w]
    refine Program.Coupling.of_uniform _ _ hL hR (fun w => ?_)
    refine ⟨rfl, ?_⟩
    refine lqt_post_alg t tv inp l m (RO_write_ovw tv inp l m σ₁ w) ?_ ?_
    · rw [Lens.get_of_disjoint_set chal_x_queried_gh random_oracle_state]
      exact hf₁
    · rw [Lens.get_of_disjoint_set ow_challenge_x random_oracle_state]
      exact hcx₁

/-- The adversary relates to itself across the overwrite, remembering the
    two pinned left-side values (`q_shift`-style triple shift + frames). -/
private lemma adv_shift_rel
    (h_cx : ow_adv.inRange ow_challenge_x.compl.range)
    (h_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_qi : ow_adv.inRange queries_input.compl.range)
    (t tv : input) (l : List input) (m : Bool) :
    ow_adv.rel ow_adv
      (fun σ₁ σ₂ => σ₂ = queries_input.set l (chal_x_queried_gh.set m
          (ow_challenge_x.set tv σ₁))
        ∧ chal_x_queried_gh.get σ₁ = decide (t ∈ l)
        ∧ ow_challenge_x.get σ₁ = t)
      (fun u v => v.2 = queries_input.set l (chal_x_queried_gh.set m
          (ow_challenge_x.set tv u.2))
        ∧ chal_x_queried_gh.get u.2 = decide (t ∈ l)
        ∧ ow_challenge_x.get u.2 = t) := by
  have hshift : ow_adv.relE ow_adv
      (fun σ₁ σ₂ => σ₂ = queries_input.set l (chal_x_queried_gh.set m
        (ow_challenge_x.set tv σ₁)))
      (fun u v => v.1 = u.1 ∧ v.2 = queries_input.set l
        (chal_x_queried_gh.set m (ow_challenge_x.set tv u.2))) := by
    refine ((Program.relE.self_lens_set ow_challenge_x h_cx tv).trans
      ((Program.relE.self_lens_set chal_x_queried_gh h_flag m).trans
        (Program.relE.self_lens_set queries_input h_qi l))).conseq ?_ ?_
    · rintro σ₁ σ₂ rfl
      exact ⟨_, rfl, _, rfl, rfl⟩
    · rintro x z ⟨y, ⟨ha1, ha2⟩, y', ⟨hb1, hb2⟩, hc1, hc2⟩
      exact ⟨hc1.trans (hb1.trans ha1), by rw [hc2, hb2, ha2]⟩
  have h2 := Program.relE.frame ow_challenge_x ow_challenge_x h_cx h_cx
    (Program.relE.frame chal_x_queried_gh chal_x_queried_gh h_flag h_flag
      hshift (decide (t ∈ l)) m)
    t tv
  refine h2.1.conseq ?_ ?_
  · rintro σ₁ σ₂ ⟨rfl, hf, hcx⟩
    refine ⟨⟨rfl, hf, ?_⟩, hcx, cx_ovw tv l m σ₁⟩
    rw [Lens.get_of_disjoint_set chal_x_queried_gh queries_input,
        chal_x_queried_gh.set_get]
  · rintro u v ⟨⟨⟨_, hst⟩, hfU, _⟩, hcxU, _⟩
    exact ⟨hst, hfU, hcxU⟩

/-- The recording suffix: left `set oracle_output` vs right
    `set oracle_output; append the query` — extends the recorded list. -/
private lemma record_step_rel (t tv inp : input) (l : List input) (y : output) :
    (Program.set oracle_output y).rel
      (Program.set oracle_output y >>= fun _ =>
        Program.get queries_input >>= fun qs =>
        Program.set queries_input (qs ++ [inp]))
      (fun τ₁ τ₂ =>
        (∃ m', τ₂ = queries_input.set l (chal_x_queried_gh.set m'
          (ow_challenge_x.set tv τ₁)))
        ∧ chal_x_queried_gh.get τ₁ = (decide (t ∈ l) || decide (inp = t))
        ∧ ow_challenge_x.get τ₁ = t)
      (fun u v => InvG1 t tv u.2 v.2) := by
  intro F G hFG τ₁ τ₂ hpre
  obtain ⟨⟨m', rfl⟩, hf, hcx⟩ := hpre
  rw [wp_set]
  rw [wp_bind, wp_set]
  dsimp only
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_set]
  refine hFG _ _ ⟨l ++ [inp], m', ?_, ?_, ?_⟩
  · rw [Lens.get_of_disjoint_set queries_input oracle_output,
        Lens.set_get queries_input,
        (inferInstance : disjoint oracle_output queries_input).commute,
        queries_input.set_set,
        (inferInstance : disjoint oracle_output chal_x_queried_gh).commute,
        (inferInstance : disjoint oracle_output ow_challenge_x).commute]
  · rw [Lens.get_of_disjoint_set chal_x_queried_gh oracle_output, hf,
        decide_eq_decide.mpr (show (t ∈ l ++ [inp]) ↔ (t ∈ l ∨ inp = t) from by
          rw [List.mem_append, List.mem_singleton]
          exact or_congr_right eq_comm),
        Bool.decide_or]
  · rw [Lens.get_of_disjoint_set ow_challenge_x oracle_output]
    exact hcx

/-- The ending: reading the tracking flag (left) returns the same boolean
    as the deferred membership test (right). -/
private lemma ending_g1_rel (t tv : input) :
    (Program.get chal_x_queried_gh).rel
      (Program.get queries_input >>= fun qs =>
        Program.set chal_x_queried_gh (decide (t ∈ qs)) >>= fun _ =>
        Program.get chal_x_queried_gh)
      (InvG1 t tv) (fun u v => u.1 = v.1) := by
  intro F G hFG σ₁ σ₂ hpre
  obtain ⟨l, m, rfl, hf, hcx⟩ := hpre
  rw [wp_get]
  simp only [wp_bind, wp_get, wp_set, Lens.set_get]
  refine hFG _ _ ?_
  change chal_x_queried_gh.get σ₁ = decide (t ∈ l)
  exact hf

/-- **Loop-body judgment**: one tracking step vs one recording step. -/
private lemma body_game_1_rel
    (h_cx : ow_adv.inRange ow_challenge_x.compl.range)
    (h_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_qi : ow_adv.inRange queries_input.compl.range)
    (t tv : input) :
    (body_game_1 ow_adv t).rel (body_recording_game_1 ow_adv)
      (InvG1 t tv) (fun u v => InvG1 t tv u.2 v.2) := by
  haveI : disjoint ow_challenge_x oracle_input :=
    disjoint_oracle_input_ow_challenge_x.symm
  change (ow_adv >>= fun _ =>
    Program.get oracle_input >>= fun inp =>
    lazy_query_tracked inp >>= fun y =>
    Program.set oracle_output y).rel
    (ow_adv >>= fun _ =>
    Program.get oracle_input >>= fun inp =>
    lazy_query_tracked inp >>= fun y =>
    Program.set oracle_output y >>= fun _ =>
    Program.get queries_input >>= fun qs =>
    Program.set queries_input (qs ++ [inp])) _ _
  apply Program.rel.exists_pre
  intro l
  apply Program.rel.exists_pre
  intro m
  refine Program.rel.bind
    (Mid := fun u v : Unit × state =>
      v.2 = queries_input.set l (chal_x_queried_gh.set m
        (ow_challenge_x.set tv u.2))
      ∧ chal_x_queried_gh.get u.2 = decide (t ∈ l)
      ∧ ow_challenge_x.get u.2 = t)
    (adv_shift_rel ow_adv h_cx h_flag h_qi t tv l m) (fun _ _ => ?_)
  refine Program.rel.bind
    (Mid := fun u v : input × state => u.1 = v.1
      ∧ v.2 = queries_input.set l (chal_x_queried_gh.set m
        (ow_challenge_x.set tv u.2))
      ∧ chal_x_queried_gh.get u.2 = decide (t ∈ l)
      ∧ ow_challenge_x.get u.2 = t)
    (Program.rel.get_get ?_) (fun inp₁ inp₂ => ?_)
  · rintro σ₁ σ₂ ⟨rfl, hf, hcx⟩
    exact ⟨(get_ovw oracle_input tv l m σ₁).symm, rfl, hf, hcx⟩
  · refine Program.rel.bind
      (Mid := fun u v : output × state => u.1 = v.1
        ∧ (∃ m', v.2 = queries_input.set l (chal_x_queried_gh.set m'
            (ow_challenge_x.set tv u.2)))
        ∧ chal_x_queried_gh.get u.2 = (decide (t ∈ l) || decide (inp₂ = t))
        ∧ ow_challenge_x.get u.2 = t)
      ?_ (fun y₁ y₂ => ?_)
    · intro F G hFG τ₁ τ₂ hpre
      obtain ⟨hval, hτ, hf, hcx⟩ := hpre
      have hval' : inp₁ = inp₂ := hval
      rw [hval']
      exact (lqt_pair_relE t tv inp₂ l m).1 F G hFG τ₁ τ₂ ⟨hτ, hf, hcx⟩
    · intro F G hFG τ₁ τ₂ hpre
      obtain ⟨hval, hm', hf, hcx⟩ := hpre
      have hval' : y₁ = y₂ := hval
      subst hval'
      exact record_step_rel t tv inp₂ l y₁ F G hFG τ₁ τ₂ ⟨hm', hf, hcx⟩

/-- **Final-step judgment**: the verification query vs its recording. -/
private lemma final_game_1_rel (t tv : input) :
    (final_game_1 t).rel final_recording_game_1
      (InvG1 t tv) (fun u v => InvG1 t tv u.2 v.2) := by
  haveI : disjoint ow_challenge_x ow_response :=
    disjoint_ow_response_ow_challenge_x.symm
  change (Program.get ow_response >>= fun resp =>
    lazy_query_tracked resp >>= fun y =>
    Program.set oracle_output y).rel
    (Program.get ow_response >>= fun resp =>
    lazy_query_tracked resp >>= fun y =>
    Program.set oracle_output y >>= fun _ =>
    Program.get queries_input >>= fun qs =>
    Program.set queries_input (qs ++ [resp])) _ _
  apply Program.rel.exists_pre
  intro l
  apply Program.rel.exists_pre
  intro m
  refine Program.rel.bind
    (Mid := fun u v : input × state => u.1 = v.1
      ∧ v.2 = queries_input.set l (chal_x_queried_gh.set m
        (ow_challenge_x.set tv u.2))
      ∧ chal_x_queried_gh.get u.2 = decide (t ∈ l)
      ∧ ow_challenge_x.get u.2 = t)
    (Program.rel.get_get ?_) (fun r₁ r₂ => ?_)
  · rintro σ₁ σ₂ ⟨rfl, hf, hcx⟩
    exact ⟨(get_ovw ow_response tv l m σ₁).symm, rfl, hf, hcx⟩
  · refine Program.rel.bind
      (Mid := fun u v : output × state => u.1 = v.1
        ∧ (∃ m', v.2 = queries_input.set l (chal_x_queried_gh.set m'
            (ow_challenge_x.set tv u.2)))
        ∧ chal_x_queried_gh.get u.2 = (decide (t ∈ l) || decide (r₂ = t))
        ∧ ow_challenge_x.get u.2 = t)
      ?_ (fun y₁ y₂ => ?_)
    · intro F G hFG τ₁ τ₂ hpre
      obtain ⟨hval, hτ, hf, hcx⟩ := hpre
      have hval' : r₁ = r₂ := hval
      rw [hval']
      exact (lqt_pair_relE t tv r₂ l m).1 F G hFG τ₁ τ₂ ⟨hτ, hf, hcx⟩
    · intro F G hFG τ₁ τ₂ hpre
      obtain ⟨hval, hm', hf, hcx⟩ := hpre
      have hval' : y₁ = y₂ := hval
      subst hval'
      exact record_step_rel t tv r₂ l y₁ F G hFG τ₁ τ₂ ⟨hm', hf, hcx⟩

/-- **Game 1 correspondence**, relationally: the tracking flag fires iff
    the target lands in the recorded query list. One synchronized
    invariant (`InvG1`) through the loop, the final query, and the ending. -/
private theorem game_1_correspondence (ow_adv : Program state Unit)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_qg : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (q : ℕ)
    (σ' : state) (t : input) :
    (Program.set ow_challenge_x t >>= fun _ : Unit =>
     Program.set chal_x_queried_gh false >>= fun _ : Unit =>
     loop_n q (body_game_1 ow_adv t) >>= fun _ : Unit =>
     final_game_1 t >>= fun _ : Unit =>
     Program.get chal_x_queried_gh).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
     ≤
    (Program.set queries_input [] >>= fun _ : Unit =>
     loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
     final_recording_game_1 >>= fun _ : Unit =>
     Program.get queries_input >>= fun qs =>
     Program.set chal_x_queried_gh (decide (t ∈ qs)) >>= fun _ : Unit =>
     Program.get chal_x_queried_gh).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ' := by
  haveI hxq : disjoint ow_challenge_x chal_x_queried_gh :=
    disjoint_chal_x_queried_gh_ow_challenge_x.symm
  have hTail : (loop_n q (body_game_1 ow_adv t) >>= fun _ : Unit =>
      final_game_1 t >>= fun _ : Unit =>
      Program.get chal_x_queried_gh).rel
    (loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
      final_recording_game_1 >>= fun _ : Unit =>
      Program.get queries_input >>= fun qs =>
      Program.set chal_x_queried_gh (decide (t ∈ qs)) >>= fun _ : Unit =>
      Program.get chal_x_queried_gh)
    (InvG1 t (ow_challenge_x.get σ')) (fun u v => u.1 = v.1) :=
    Program.rel.bind
      (Mid := fun u v : Unit × state => InvG1 t (ow_challenge_x.get σ') u.2 v.2)
      (Program.rel.loop_n
        (body_game_1_rel ow_adv h_ow_adv_chal_x h_ow_adv_chal_x_qg h_ow_adv_qi
          t (ow_challenge_x.get σ')) q)
      (fun _ _ => Program.rel.bind
        (Mid := fun u v : Unit × state =>
          InvG1 t (ow_challenge_x.get σ') u.2 v.2)
        (final_game_1_rel t (ow_challenge_x.get σ'))
        (fun _ _ => ending_g1_rel t (ow_challenge_x.get σ')))
  rw [Program.wp_set_seq, Program.wp_set_seq, Program.wp_set_seq]
  refine hTail.wp_le ?_ ?_
  · intro u v h
    rw [h]
  · refine ⟨[], chal_x_queried_gh.get σ', ?_, ?_, ?_⟩
    · rw [hxq.commute, chal_x_queried_gh.set_set, ow_challenge_x.set_set,
          ow_challenge_x.get_set, chal_x_queried_gh.get_set]
    · rw [chal_x_queried_gh.set_get]
      simp
    · rw [Lens.get_of_disjoint_set ow_challenge_x chal_x_queried_gh,
          ow_challenge_x.set_get]


/-- **Reduction: bad-in-Game-1 ≤ Guess(input, q+1)**.

    Routes via `guess_experiment_game_1` → `interim` → `collector` → bound. -/
theorem ow_game_1_tracked_bad_le_guess_input_bound
    (h_ow_adv_RO : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_ow_adv_queries : ow_adv.inRange queries_input.compl.range)
    (h_ow_adv_mass_one : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1)
    (q : ℕ) (σ : state) :
    (ow_game_1_tracked ow_adv q).wp
        (fun bσ : Bool × state =>
          if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
    ≤ ((q + 1) : ENNReal) / Fintype.card input := by
  rw [ow_game_1_tracked_bad_eq_ow_game_2_tracked_bad ow_adv h_ow_adv_RO
      h_ow_adv_chal_x h_ow_adv_chal_x_queried_gh h_ow_adv_mass_one q σ]
  rw [ow_game_2_tracked_bad_eq_guess_experiment_game_1 ow_adv
      h_ow_adv_chal_y q σ]
  refine le_trans (guess_experiment_le_interim_assumption _ _ _ queries_input _ _
      (body_recording_game_1 ow_adv) final_recording_game_1 _
      (game_1_correspondence ow_adv h_ow_adv_chal_x h_ow_adv_chal_x_queried_gh
        h_ow_adv_queries q) _) ?_
  apply guess_experiment_interim_wp_bound
  -- h_qs_length_le for Game 1.
  intro σ'
  have h_post_eq : (fun aσ : Unit × state =>
        ((queries_input.get aσ.2).length : ENNReal) / Fintype.card input)
      = fun aσ : Unit × state => (Fintype.card input : ENNReal)⁻¹ *
            ((queries_input.get aσ.2).length : ENNReal) := by
    funext aσ
    rw [div_eq_mul_inv, mul_comm]
  rw [h_post_eq, Program.wp_const_mul]
  rw [show ((q + 1 : ℕ) : ENNReal) / Fintype.card input
        = (Fintype.card input : ENNReal)⁻¹ * ((q + 1 : ℕ) : ENNReal) from by
      rw [div_eq_mul_inv, mul_comm]]
  refine mul_le_mul' (le_refl _) ?_
  rw [wp_bind]
  refine le_trans (Program.wp_le_wp_of_le _ _
      (fun _ : Unit × state => ((q + 1 : ℕ) : ENNReal)) ?_ σ') ?_
  · intro aσ_lazy
    rw [wp_bind, wp_set]
    set σ_init := queries_input.set [] aσ_lazy.2 with σ_init_def
    have h_qs_init : (queries_input.get σ_init).length = 0 := by
      simp [σ_init_def, Lens.set_get]
    rw [wp_bind]
    refine le_trans (Program.wp_le_wp_of_le _ _
        (fun aσ : Unit × state =>
          ((queries_input.get aσ.2).length : ENNReal) + 1) ?_ σ_init) ?_
    · intro aσ_loop
      exact final_recording_game_1_qs_length_bump _
    rw [Program.wp_add (loop_n q (body_recording_game_1 ow_adv))
        (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal))
        (fun _ : Unit × state => (1 : ENNReal))]
    refine le_trans (add_le_add (loop_n_wp_linear_bound (body_recording_game_1 ow_adv)
        (fun σ => ((queries_input.get σ).length : ENNReal)) 1
        (fun σ_body => body_recording_game_1_qs_length_bump ow_adv h_ow_adv_queries σ_body)
        q σ_init) (Program.wp_const_le _ _ _)) ?_
    rw [h_qs_init]
    push_cast
    ring_nf
    rfl
  · exact Program.wp_const_le _ _ _

/-! ## Flag-elision bridge: untracked Game 1 ↔ tracked Game 1

For postconditions that don't read `chal_x_queried_gh`, the tracked and
untracked variants of Game 1 agree at the wp level. -/

private lemma lazy_query_equiv_lazy_query_tracked (inp : input) :
    Program.EquivModuloLens chal_x_queried_gh (lazy_query inp) (lazy_query_tracked inp) := by
  intro F h_F σ
  -- Apply lazy_query_tracked_eq_lazy_query_wp with k := pure.
  have h_eq := lazy_query_tracked_eq_lazy_query_wp
    (k := fun y => (pure y : Program state output))
    (fun y => Program.inRange_pure _ _) F h_F inp σ
  -- h_eq : (lazy_query_tracked inp >>= pure).wp F σ = (lazy_query inp >>= pure).wp F σ.
  simp only [Program.bind_pure] at h_eq
  exact h_eq.symm

/-- `oracle_step ow_adv lazy_query` is equivalent (modulo `chal_x_queried_gh`)
    to `oracle_step ow_adv lazy_query_tracked` — same body, with the inner
    `lazy_query` replaced by the tracked variant. -/
private lemma oracle_step_equiv_lazy_query_lazy_query_tracked :
    Program.EquivModuloLens chal_x_queried_gh
      (oracle_step ow_adv lazy_query)
      (oracle_step ow_adv lazy_query_tracked) := by
  dsimp only [oracle_step]
  -- The continuation `fun _ => get input >>= lazy_query inp >>= set oo` is
  -- flag-disjoint (LHS uses lazy_query, which is flag-disjoint).
  have h_inner_lq_inRange : ∀ _ : Unit, (do
      let inp ← Program.get oracle_input
      let y ← lazy_query inp
      Program.set oracle_output y : Program state Unit).inRange
        chal_x_queried_gh.compl.range := by
    intro _
    refine Program.inRange_bind
      (Program.get_inRange_compl_of_disjoint oracle_input chal_x_queried_gh)
      (fun inp => ?_)
    refine Program.inRange_bind ?_ (fun y =>
      Program.set_inRange_compl_of_disjoint oracle_output chal_x_queried_gh y)
    exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)
  refine Program.EquivModuloLens.bind (Program.EquivModuloLens.refl ow_adv)
    (fun _ => ?_) h_inner_lq_inRange
  -- Inner: get input >>= ... [lq vs lqt] >>= set oo.
  have h_lq_set_oo_inRange : ∀ inp : input, (do
      let y ← lazy_query inp
      Program.set oracle_output y : Program state Unit).inRange
        chal_x_queried_gh.compl.range := by
    intro inp
    refine Program.inRange_bind ?_ (fun y =>
      Program.set_inRange_compl_of_disjoint oracle_output chal_x_queried_gh y)
    exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)
  refine Program.EquivModuloLens.bind
    (Program.EquivModuloLens.refl (Program.get oracle_input))
    (fun inp => ?_) h_lq_set_oo_inRange
  -- After get input: lazy_query[_t] inp >>= set oo y.
  refine Program.EquivModuloLens.bind
    (lazy_query_equiv_lazy_query_tracked inp)
    (fun _ => Program.EquivModuloLens.refl _)
    (fun y => Program.set_inRange_compl_of_disjoint oracle_output chal_x_queried_gh y)

/-- `oracle_step ow_adv lazy_query` is flag-disjoint. Used by the calculus
    chains in flag elision. -/
private lemma oracle_step_lazy_query_inRange_chal_x_queried_gh
    (h_ow_adv_flag : ow_adv.inRange chal_x_queried_gh.compl.range) :
    (oracle_step ow_adv lazy_query).inRange chal_x_queried_gh.compl.range := by
  dsimp only [oracle_step]
  refine Program.inRange_bind h_ow_adv_flag (fun _ => ?_)
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint oracle_input chal_x_queried_gh)
    (fun inp => ?_)
  refine Program.inRange_bind ?_ (fun y =>
    Program.set_inRange_compl_of_disjoint oracle_output chal_x_queried_gh y)
  exact Program.inRange_mono (lazy_query_inRange_ro inp)
    (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)

/-- Loop-level: `oracle_loop_n adv q lazy_query ≈_L oracle_loop_n adv q lazy_query_tracked`. -/
private lemma oracle_loop_n_equiv_lazy_query_lazy_query_tracked
    (h_ow_adv_flag : ow_adv.inRange chal_x_queried_gh.compl.range) (q : ℕ) :
    Program.EquivModuloLens chal_x_queried_gh
      (oracle_loop_n ow_adv q lazy_query)
      (oracle_loop_n ow_adv q lazy_query_tracked) := by
  -- Convert both to loop_n form via oracle_loop_n_eq_loop_n, then loop_n_congr.
  rw [oracle_loop_n_eq_loop_n, oracle_loop_n_eq_loop_n]
  exact loop_n_congr
    (oracle_step_lazy_query_inRange_chal_x_queried_gh ow_adv h_ow_adv_flag)
    (oracle_step_equiv_lazy_query_lazy_query_tracked ow_adv) q

/-- The "tail after lazy_init" of `ow_game_1` is flag-disjoint. -/
private lemma ow_game_1_tail_inRange_chal_x_queried_gh
    (h_ow_adv_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (q : ℕ) : (do
      let x ← Program.uniform
      Program.set ow_challenge_x x
      let y ← Program.uniform
      Program.set random_oracle_state (fun k => if k = x then some y else none)
      Program.set ow_challenge_y y
      oracle_loop_n ow_adv q lazy_query
      let resp ← Program.get ow_response
      let y_check ← lazy_query resp
      pure (decide (y_check = y)) : Program state Bool).inRange
        chal_x_queried_gh.compl.range := by
  refine Program.inRange_bind (Program.inRange_mono Program.inRange_uniform bot_le) (fun x => ?_)
  refine Program.inRange_bind
    (Program.set_inRange_compl_of_disjoint ow_challenge_x chal_x_queried_gh x) (fun _ => ?_)
  refine Program.inRange_bind (Program.inRange_mono Program.inRange_uniform bot_le) (fun y => ?_)
  refine Program.inRange_bind ?_ (fun _ => ?_)
  · -- set random_oracle_state ... in flag.compl.range
    exact Program.set_inRange_compl_of_disjoint random_oracle_state chal_x_queried_gh _
  refine Program.inRange_bind
    (Program.set_inRange_compl_of_disjoint ow_challenge_y chal_x_queried_gh y) (fun _ => ?_)
  refine Program.inRange_bind ?_ (fun _ => ?_)
  · -- oracle_loop_n adv q lazy_query in flag.compl.range
    exact oracle_loop_n_inRange_compl chal_x_queried_gh h_ow_adv_flag q
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint ow_response chal_x_queried_gh) (fun resp => ?_)
  refine Program.inRange_bind ?_ (fun y_check => Program.inRange_pure _ _)
  -- lazy_query resp in flag.compl.range
  exact Program.inRange_mono (lazy_query_inRange_ro resp)
    (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)

/-- Post-loop tail (get response + final lazy_query + pure check) is
    equivalent under flag-ignoring posts when we replace `lazy_query` with
    `lazy_query_tracked`. Uses `bind_eq_p` because the prefix `get ow_response`
    is identical on both sides. -/
private lemma ow_game_1_post_loop_equiv (y : output) :
    Program.EquivModuloLens chal_x_queried_gh
      (do
        let resp ← Program.get ow_response
        let y_check ← lazy_query resp
        pure (decide (y_check = y)) : Program state Bool)
      (do
        let resp ← Program.get ow_response
        let y_check ← lazy_query_tracked resp
        pure (decide (y_check = y)) : Program state Bool) := by
  apply Program.EquivModuloLens.bind_eq_p
  intro resp
  -- Inner: lazy_query resp >>= pure ≈ lazy_query_tracked resp >>= pure.
  -- Here prefixes differ (lq vs lqt), so use `bind`. The continuation is
  -- `pure (decide ...)`, whose inRange is `inRange_pure`.
  refine Program.EquivModuloLens.bind
    (lazy_query_equiv_lazy_query_tracked resp)
    (fun _ => Program.EquivModuloLens.refl _)
    (fun _ => Program.inRange_pure _ _)

/-- Post-loop tail (get response + final lazy_query + pure check) is
    flag-disjoint. -/
private lemma ow_game_1_post_loop_inRange (y : output) :
    (do
      let resp ← Program.get ow_response
      let y_check ← lazy_query resp
      pure (decide (y_check = y)) : Program state Bool).inRange
        chal_x_queried_gh.compl.range := by
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint ow_response chal_x_queried_gh)
    (fun resp => ?_)
  refine Program.inRange_bind ?_ (fun _ => Program.inRange_pure _ _)
  exact Program.inRange_mono (lazy_query_inRange_ro resp)
    (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)

/-- Loop + post-loop tail equivalence — the `oracle_loop_n` call composed
    with the `get ow_response; lazy_query resp; pure (decide ...)` tail. -/
private lemma ow_game_1_loop_tail_equiv
    (h_ow_adv_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (q : ℕ) (y : output) :
    Program.EquivModuloLens chal_x_queried_gh
      (do
        oracle_loop_n ow_adv q lazy_query
        let resp ← Program.get ow_response
        let y_check ← lazy_query resp
        pure (decide (y_check = y)) : Program state Bool)
      (do
        oracle_loop_n ow_adv q lazy_query_tracked
        let resp ← Program.get ow_response
        let y_check ← lazy_query_tracked resp
        pure (decide (y_check = y)) : Program state Bool) := by
  -- Prefixes differ (loop with lq vs lqt). Use `bind`.
  refine Program.EquivModuloLens.bind
    (oracle_loop_n_equiv_lazy_query_lazy_query_tracked ow_adv h_ow_adv_flag q)
    (fun _ => ow_game_1_post_loop_equiv y)
    (fun _ => ow_game_1_post_loop_inRange y)

/-- The full tail of `ow_game_1` (after `lazy_init`) is equivalent (modulo
    `chal_x_queried_gh`) to the full tail of `ow_game_1_tracked` (after
    `lazy_init` and `set chal_x_queried_gh false`).

    The 5-layer prefix (uniform / set chal_x / uniform / set ro / set chal_y)
    is *identical* on both sides, so we use `bind_eq_p` repeatedly — no
    inRange proofs needed for the prefix. -/
private lemma ow_game_1_full_tail_equiv_lazy_query_tracked
    (h_ow_adv_flag : ow_adv.inRange chal_x_queried_gh.compl.range) (q : ℕ) :
    Program.EquivModuloLens chal_x_queried_gh
      (do
        let x ← Program.uniform
        Program.set ow_challenge_x x
        let y ← Program.uniform
        Program.set random_oracle_state (fun k => if k = x then some y else none)
        Program.set ow_challenge_y y
        oracle_loop_n ow_adv q lazy_query
        let resp ← Program.get ow_response
        let y_check ← lazy_query resp
        pure (decide (y_check = y)) : Program state Bool)
      (do
        let x ← Program.uniform
        Program.set ow_challenge_x x
        let y ← Program.uniform
        Program.set random_oracle_state (fun k => if k = x then some y else none)
        Program.set ow_challenge_y y
        oracle_loop_n ow_adv q lazy_query_tracked
        let resp ← Program.get ow_response
        let y_check ← lazy_query_tracked resp
        pure (decide (y_check = y)) : Program state Bool) := by
  apply Program.EquivModuloLens.bind_eq_p; intro x
  apply Program.EquivModuloLens.bind_eq_p; intro _
  apply Program.EquivModuloLens.bind_eq_p; intro y
  apply Program.EquivModuloLens.bind_eq_p; intro _
  apply Program.EquivModuloLens.bind_eq_p; intro _
  exact ow_game_1_loop_tail_equiv ow_adv h_ow_adv_flag q y

/-- **Flag elision at the game level**: `ow_game_1` and `ow_game_1_tracked`
    have equal wp's for flag-ignoring postconditions.

    Proof via the `EquivModuloLens` calculus: bind congruence chains compose
    `oracle_loop_n_equiv` (loop-level), `lazy_query_equiv_lazy_query_tracked`
    (final query), and `set_equiv_pure` (initial set chal_x_queried_gh false). -/
theorem ow_game_1_wp_eq_ow_game_1_tracked_wp_of_flag_ignoring
    (h_ow_adv_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (q : ℕ) (F : Bool × state → ENNReal)
    (h_F : IgnoresLens chal_x_queried_gh F)
    (σ : state) :
    (ow_game_1 ow_adv q).wp F σ = (ow_game_1_tracked ow_adv q).wp F σ := by
  suffices h_equiv : Program.EquivModuloLens chal_x_queried_gh
      (ow_game_1 ow_adv q) (ow_game_1_tracked ow_adv q) by
    exact h_equiv F h_F σ
  dsimp only [ow_game_1, ow_game_1_tracked]
  -- Outer `lazy_init` prefix is identical on both sides; use `bind_eq_p`.
  apply Program.EquivModuloLens.bind_eq_p
  intro _
  -- Goal: REST_lq ≈_L (set chal_x_queried_gh false >>= REST_lqt).
  -- Step 1: REST_lq ≈_L set L false >>= REST_lq (dead set insertion via
  --   bind_eq_k with `pure_equiv_set`, then rewriting `pure () >>= _` via
  --   `Program.pure_bind`).
  -- Step 2: set L false >>= REST_lq ≈_L set L false >>= REST_lqt (replace
  --   lq with lqt under same prefix; uses bind_eq_p with full-tail equiv).
  have h_dead_set := Program.EquivModuloLens.bind_eq_k
    (Program.EquivModuloLens.pure_equiv_set (L := chal_x_queried_gh) false)
    (fun _ : Unit => ow_game_1_tail_inRange_chal_x_queried_gh ow_adv h_ow_adv_flag q)
  -- h_dead_set : (pure () >>= fun _ => REST_lq) ≈_L (set L false >>= fun _ => REST_lq)
  rw [Program.pure_bind] at h_dead_set
  -- h_dead_set : REST_lq ≈_L (set L false >>= fun _ => REST_lq)
  exact h_dead_set.trans (Program.EquivModuloLens.bind_eq_p
    (fun _ => ow_game_1_full_tail_equiv_lazy_query_tracked ow_adv h_ow_adv_flag q))


end Game1
