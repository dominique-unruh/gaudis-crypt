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
* `body_game_1'`, `final_game_1'` — *Game 1' variants* with the chal_x check
  EXPLICIT (`if a = t then set chal_x_qg true`) instead of buried inside
  `lazy_query_tracked`. This form fits the schema's `q >>= match_check`
  decomposition with `q_body_game_1' := adv; get inp; lazy_query inp; set output y; pure inp`.
* `body_recording_game_1'`, `final_recording_game_1'` — the recording cousins.
* `guess_experiment_game_1'` — Game 1' as a `guess_experiment` instance.

## Bridges (Game 1 ↔ Game 1')

At chal_x_queried_gh-respecting posts (or under the invariant `ow_challenge_x = t`),
`lazy_query_tracked` and `lazy_query + explicit if-set` are wp-equivalent:

* `lazy_query_tracked_bind_wp_eq_lazy_query_bind` — generic helper.
* `body_recording_game_1_wp_eq_body_recording_game_1'` — body recording.
* `final_recording_game_1_wp_eq_final_recording_game_1'` — final recording.
* `body_game_1_wp_eq_body_game_1'_at_chal_x_eq` — body (under chal_x = t).
* `final_game_1_wp_eq_final_game_1'_at_chal_x_eq` — final (under chal_x = t).
* `loop_final_body_game_1_wp_eq` — loop-level bridge by induction on q.
* `guess_experiment_game_1_wp_eq_game_1'` — game-level bridge.

## Correspondence + bound

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
    -- Goal: k.wp (fun aσ => (pure (decide aσ.1 = y)).wp F_chal_xqg aσ.2) (chal_y.set y σ) = k.wp NEW_POST σ.
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



/-- Helper: `get qi >>= fun qs => set qi (qs ++ [v])` has the same wp as
    `pure ()` at queries_input-ignoring posts. -/
private lemma wp_qi_get_set_invisible
    (val : input)
    (F : Unit × state → ENNReal)
    (h_F : IgnoresLens queries_input F)
    (σ : state) :
    (Program.get queries_input >>= fun qs : List input =>
       Program.set queries_input (qs ++ [val])).wp F σ
    = F ((), σ) := by
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_set]
  exact h_F ((), σ) _

/-- Helper: a trailing `get qi >>= set qi (qs ++ [v])` is invisible to wp at
    queries_input-ignoring posts. (Specialized to Program state Unit.) -/
private lemma wp_qi_trailing_invisible
    (p : Program state Unit) (val : input)
    (F : Unit × state → ENNReal)
    (h_F : IgnoresLens queries_input F)
    (σ : state) :
    (p >>= fun _ : Unit =>
       Program.get queries_input >>= fun qs : List input =>
       Program.set queries_input (qs ++ [val])).wp F σ
    = p.wp F σ := by
  rw [wp_bind]
  congr 1
  funext aσ
  obtain ⟨a, s'⟩ := aσ
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_set]
  exact h_F (a, s') _

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

/-! ### Game 1 schema: explicit-match form via game-hop

Game 1's `body_game_1` hides the match-check inside `lazy_query_tracked`
(which flips `chal_x_queried_gh` when `inp = chal_x`). The schema framework
requires the match-check to be explicit. We define `body_game_1'` using
`lazy_query` (untracked) plus an explicit `if inp = x` check, and show via
a game-hop that the wp's agree.

`q_body_game_1'` and `q_final_game_1'` are the schema's shared query
subprograms. -/

/-- The "query" subprogram for the explicit-match form of Game 1's body. -/
private noncomputable def q_body_game_1' (ow_adv : Program state Unit) : Program state input := do
  ow_adv
  let inp ← Program.get oracle_input
  let y ← lazy_query inp
  Program.set oracle_output y
  pure inp

/-- The "query" subprogram for the explicit-match form of Game 1's final. -/
private noncomputable def q_final_game_1' : Program state input := do
  let resp ← Program.get ow_response
  let y ← lazy_query resp
  Program.set oracle_output y
  pure resp

/-- Explicit-match body for Game 1 (post game-hop). Uses untracked
    `lazy_query` and explicit `if inp = x then set chal_x_qg true`. -/
private noncomputable def body_game_1' (ow_adv : Program state Unit) (x : input) :
    Program state Unit :=
  q_body_game_1' ow_adv >>= fun a : input =>
    if a = x then Program.set chal_x_queried_gh true else (pure () : Program state Unit)

/-- Explicit-match final for Game 1 (post game-hop). -/
private noncomputable def final_game_1' (x : input) : Program state Unit :=
  q_final_game_1' >>= fun a : input =>
    if a = x then Program.set chal_x_queried_gh true else (pure () : Program state Unit)

/-- Recording-style body for Game 1, using untracked `lazy_query`. This is
    wp-equivalent to `body_recording_game_1` at chal_x_qg-ignoring posts
    (since lazy_query_tracked's chal_x_qg flip is invisible). -/
private noncomputable def body_recording_game_1' (ow_adv : Program state Unit) :
    Program state Unit :=
  q_body_game_1' ow_adv >>= fun a : input =>
    Program.get queries_input >>= fun qs : List input =>
    Program.set queries_input (qs ++ [a])

/-- Recording-style final for Game 1, using untracked `lazy_query`. -/
private noncomputable def final_recording_game_1' : Program state Unit :=
  q_final_game_1' >>= fun a : input =>
    Program.get queries_input >>= fun qs : List input =>
    Program.set queries_input (qs ++ [a])

/-- Game 1', the schema-friendly variant. Same as Game 1 but with the
    explicit-match body/final. -/
private noncomputable def guess_experiment_game_1' (ow_adv : Program state Unit) (q : ℕ) :
    Program state Bool :=
  guess_experiment lazy_init Program.uniform ow_challenge_x chal_x_queried_gh
    (body_game_1' ow_adv) final_game_1' q

/-! ### Disjointness for q_body_game_1' and q_final_game_1' -/

/-- `q_body_game_1' ow_adv` is chal_x_queried_gh-disjoint. -/
private lemma q_body_game_1'_inRange_chal_x_queried_gh
    (ow_adv : Program state Unit)
    (h_ow_adv : ow_adv.inRange chal_x_queried_gh.compl.range) :
    (q_body_game_1' ow_adv).inRange chal_x_queried_gh.compl.range := by
  unfold q_body_game_1'
  refine Program.inRange_bind h_ow_adv (fun _ => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun inp => ?_)
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `q_body_game_1' ow_adv` is queries_input-disjoint. -/
private lemma q_body_game_1'_inRange_queries_input
    (ow_adv : Program state Unit)
    (h_ow_adv : ow_adv.inRange queries_input.compl.range) :
    (q_body_game_1' ow_adv).inRange queries_input.compl.range := by
  unfold q_body_game_1'
  refine Program.inRange_bind h_ow_adv (fun _ => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun inp => ?_)
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state queries_input)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `q_body_game_1' ow_adv` is ow_challenge_x-disjoint. -/
private lemma q_body_game_1'_inRange_ow_challenge_x
    (ow_adv : Program state Unit)
    (h_ow_adv : ow_adv.inRange ow_challenge_x.compl.range) :
    (q_body_game_1' ow_adv).inRange ow_challenge_x.compl.range := by
  unfold q_body_game_1'
  refine Program.inRange_bind h_ow_adv (fun _ => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun inp => ?_)
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_x)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `q_final_game_1'` is chal_x_queried_gh-disjoint. -/
private lemma q_final_game_1'_inRange_chal_x_queried_gh :
    q_final_game_1'.inRange chal_x_queried_gh.compl.range := by
  unfold q_final_game_1'
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun resp => ?_)
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro resp)
      (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `q_final_game_1'` is queries_input-disjoint. -/
private lemma q_final_game_1'_inRange_queries_input :
    q_final_game_1'.inRange queries_input.compl.range := by
  unfold q_final_game_1'
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun resp => ?_)
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro resp)
      (Lens.range_le_compl_of_disjoint random_oracle_state queries_input)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `q_final_game_1'` is ow_challenge_x-disjoint. -/
private lemma q_final_game_1'_inRange_ow_challenge_x :
    q_final_game_1'.inRange ow_challenge_x.compl.range := by
  unfold q_final_game_1'
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun resp => ?_)
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro resp)
      (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_x)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `body_recording_game_1' ow_adv` is in `chal_x_queried_gh.compl.range`.
    Used to lift the body-recording bridge to the loop level. -/
private lemma body_recording_game_1'_inRange_chal_x_queried_gh
    (ow_adv : Program state Unit)
    (h_ow_adv_chal_x_qg : ow_adv.inRange chal_x_queried_gh.compl.range) :
    (body_recording_game_1' ow_adv).inRange chal_x_queried_gh.compl.range := by
  unfold body_recording_game_1'
  refine Program.inRange_bind
    (q_body_game_1'_inRange_chal_x_queried_gh ow_adv h_ow_adv_chal_x_qg) (fun a => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun qs => ?_)
  exact Program.set_inRange_compl_of_disjoint _ _ _

/-- `final_recording_game_1'` is in `chal_x_queried_gh.compl.range`.
    Used to lift the final-recording bridge to the loop level. -/
private lemma final_recording_game_1'_inRange_chal_x_queried_gh :
    final_recording_game_1'.inRange chal_x_queried_gh.compl.range := by
  unfold final_recording_game_1'
  refine Program.inRange_bind q_final_game_1'_inRange_chal_x_queried_gh (fun a => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun qs => ?_)
  exact Program.set_inRange_compl_of_disjoint _ _ _

/-- **Generic wp-bridge for `lazy_query_tracked` vs `lazy_query`**: at any
    chal_x_queried_gh-ignoring post `F` with a chal_x_queried_gh-disjoint
    continuation `K`, the two are wp-equivalent. The chal_x_qg flip inside
    `lazy_query_tracked` is invisible at chal_x_qg-ignoring F. -/
private lemma lazy_query_tracked_bind_wp_eq_lazy_query_bind
    (inp : input) {β : Type} (K : output → Program state β)
    (h_K : ∀ y, (K y).inRange chal_x_queried_gh.compl.range)
    (F : β × state → ENNReal) (h_F : IgnoresLens chal_x_queried_gh F)
    (σ : state) :
    (lazy_query_tracked inp >>= K).wp F σ = (lazy_query inp >>= K).wp F σ := by
  unfold lazy_query_tracked
  simp only [Program.bind_assoc, Program.pure_bind]
  rw [wp_bind]
  conv_rhs => rw [wp_bind]
  congr 1
  funext aσ_lq
  obtain ⟨y, σ_lq⟩ := aσ_lq
  dsimp only
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_bind]
  by_cases h : inp = ow_challenge_x.get σ_lq
  · rw [if_pos h, wp_set]
    dsimp only
    have hf : (fun s' : state => chal_x_queried_gh.set true s') ∈
        ((chal_x_queried_gh.compl.range : LensRange state)ᶜ).updates := by
      rw [show ((chal_x_queried_gh.compl.range : LensRange state)ᶜ) = chal_x_queried_gh.range from by
        rw [LensRange.complement_range, LensRange.compl_compl]]
      exact ⟨Function.const _ true, Set.mem_univ _, rfl⟩
    show (K y).wp F ((fun s' => chal_x_queried_gh.set true s') σ_lq) = (K y).wp F σ_lq
    rw [Program.wp_shift_input (h_K y) hf]
    congr 1
    funext xs
    exact h_F xs true
  · rw [if_neg h, wp_pure]

/-- **Body-recording bridge**: at chal_x_queried_gh-ignoring posts,
    `body_recording_game_1` (with lazy_query_tracked) and
    `body_recording_game_1'` (with lazy_query) have the same wp. The
    chal_x_qg flip in lazy_query_tracked is invisible at chal_x_qg-ignoring
    posts. -/
private lemma body_recording_game_1_wp_eq_body_recording_game_1'
    (ow_adv : Program state Unit)
    (F : Unit × state → ENNReal)
    (h_F : IgnoresLens chal_x_queried_gh F)
    (σ : state) :
    (body_recording_game_1 ow_adv).wp F σ
    = (body_recording_game_1' ow_adv).wp F σ := by
  -- Normalize body_recording_game_1' via bind_assoc + pure_bind so the
  -- structures match except for `lazy_query` vs `lazy_query_tracked`.
  unfold body_recording_game_1 body_recording_game_1' q_body_game_1'
  simp only [Program.bind_assoc, Program.pure_bind]
  -- Both sides: ow_adv; get inp; lazy_query[_tracked] inp; set output y; record qs.
  rw [wp_bind]
  conv_rhs => rw [wp_bind]
  congr 1
  funext aσ_adv
  obtain ⟨_, σ_adv⟩ := aσ_adv
  dsimp only
  rw [wp_bind, wp_get]
  conv_rhs => rw [wp_bind, wp_get]
  dsimp only
  -- Goal: (lazy_query_tracked (oracle_input.get σ_adv) >>= K).wp F σ_adv =
  --       (lazy_query (oracle_input.get σ_adv) >>= K).wp F σ_adv
  -- where K = fun y => set output y >>= fun _ => get qs >>= fun qs' => set qs (qs' ++ [inp]).
  apply lazy_query_tracked_bind_wp_eq_lazy_query_bind _ _ _ _ h_F
  intro y
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun qs => ?_)
  exact Program.set_inRange_compl_of_disjoint _ _ _

/-- **Final-recording bridge**: same as body-recording bridge for final. -/
private lemma final_recording_game_1_wp_eq_final_recording_game_1'
    (F : Unit × state → ENNReal)
    (h_F : IgnoresLens chal_x_queried_gh F)
    (σ : state) :
    final_recording_game_1.wp F σ = final_recording_game_1'.wp F σ := by
  unfold final_recording_game_1 final_recording_game_1' q_final_game_1'
  simp only [Program.bind_assoc, Program.pure_bind]
  rw [wp_bind, wp_get]
  conv_rhs => rw [wp_bind, wp_get]
  dsimp only
  apply lazy_query_tracked_bind_wp_eq_lazy_query_bind _ _ _ _ h_F
  intro y
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun qs => ?_)
  exact Program.set_inRange_compl_of_disjoint _ _ _

/-- Helper: body of `body_game_1 ow_adv _` and `body_game_1' ow_adv t` have the
    same wp at any post, when starting from state σ with `ow_challenge_x.get σ = t`.

    The two bodies differ in HOW they compare adv's query `inp` against the bound
    target `t`: body_game_1 reads chal_x from state (via lazy_query_tracked's
    `get chal_x` inside); body_game_1' uses the bound `t` directly. When state
    has chal_x = t, both ways agree. The chal_x_qg-write and set-output also
    appear in opposite orders; they commute by disjointness. -/
private lemma body_game_1_wp_eq_body_game_1'_at_chal_x_eq
    (ow_adv : Program state Unit)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (t : input) (F : Unit × state → ENNReal) (σ : state)
    (h_cx : ow_challenge_x.get σ = t) :
    (body_game_1 ow_adv t).wp F σ = (body_game_1' ow_adv t).wp F σ := by
  unfold body_game_1 body_game_1' q_body_game_1' lazy_query_tracked
  simp only [Program.bind_assoc, Program.pure_bind]
  -- Step 1: peel ow_adv, strengthening with chal_x preservation.
  rw [wp_bind, Program.wp_strengthen_lens_preserved ow_challenge_x h_ow_adv_chal_x]
  conv_rhs => rw [wp_bind, Program.wp_strengthen_lens_preserved ow_challenge_x h_ow_adv_chal_x]
  congr 1
  funext aσ_adv
  obtain ⟨_, σ_adv⟩ := aσ_adv
  dsimp only
  by_cases h1 : ow_challenge_x.get σ_adv = ow_challenge_x.get σ
  · simp only [if_pos h1]
    rw [h_cx] at h1
    -- Step 2: peel get inp.
    rw [wp_bind, wp_get]
    conv_rhs => rw [wp_bind, wp_get]
    dsimp only
    -- Step 3: peel lazy_query, strengthening with chal_x preservation.
    have h_lq_chal_x : (lazy_query (oracle_input.get σ_adv)).inRange
        ow_challenge_x.compl.range :=
      Program.inRange_mono (lazy_query_inRange_ro _)
        (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_x)
    rw [wp_bind, Program.wp_strengthen_lens_preserved ow_challenge_x h_lq_chal_x]
    conv_rhs => rw [wp_bind, Program.wp_strengthen_lens_preserved ow_challenge_x h_lq_chal_x]
    congr 1
    funext aσ_lq
    obtain ⟨y, σ_lq⟩ := aσ_lq
    dsimp only
    by_cases h2 : ow_challenge_x.get σ_lq = ow_challenge_x.get σ_adv
    · simp only [if_pos h2]
      rw [h1] at h2
      -- Step 4: LHS = (get chal_x; (if inp = cx then ...); set output y).wp F σ_lq.
      --         RHS = (set output y; (if inp = t then ...)).wp F σ_lq.
      rw [wp_bind, wp_get]
      dsimp only
      rw [h2]
      rw [wp_bind]
      conv_rhs => rw [wp_bind, wp_set]
      dsimp only
      by_cases h : oracle_input.get σ_adv = t
      · simp only [if_pos h]
        rw [wp_set]
        dsimp only
        simp only [wp_set]
        congr 2
        exact (inferInstance : disjoint oracle_output chal_x_queried_gh).commute σ_lq y true
      · simp only [if_neg h]
        simp only [wp_pure, wp_set]
    · simp only [if_neg h2]
  · simp only [if_neg h1]

/-- Final-game-1 equivalent of the body bridge: `final_game_1` and `final_game_1' t`
    have the same wp when starting from a state with `ow_challenge_x.get σ = t`. -/
private lemma final_game_1_wp_eq_final_game_1'_at_chal_x_eq
    (t : input) (F : Unit × state → ENNReal) (σ : state)
    (h_cx : ow_challenge_x.get σ = t) :
    (final_game_1 t).wp F σ = (final_game_1' t).wp F σ := by
  unfold final_game_1 final_game_1' q_final_game_1' lazy_query_tracked
  simp only [Program.bind_assoc, Program.pure_bind]
  -- Step 1: peel get ow_response.
  rw [wp_bind, wp_get]
  conv_rhs => rw [wp_bind, wp_get]
  dsimp only
  -- Step 2: peel lazy_query, strengthening with chal_x preservation.
  have h_lq_chal_x : (lazy_query (ow_response.get σ)).inRange
      ow_challenge_x.compl.range :=
    Program.inRange_mono (lazy_query_inRange_ro _)
      (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_x)
  rw [wp_bind, Program.wp_strengthen_lens_preserved ow_challenge_x h_lq_chal_x]
  conv_rhs => rw [wp_bind, Program.wp_strengthen_lens_preserved ow_challenge_x h_lq_chal_x]
  congr 1
  funext aσ_lq
  obtain ⟨y, σ_lq⟩ := aσ_lq
  dsimp only
  by_cases h1 : ow_challenge_x.get σ_lq = ow_challenge_x.get σ
  · simp only [if_pos h1]
    rw [h_cx] at h1
    rw [wp_bind, wp_get]
    dsimp only
    rw [h1]
    rw [wp_bind]
    conv_rhs => rw [wp_bind, wp_set]
    dsimp only
    by_cases h : ow_response.get σ = t
    · simp only [if_pos h]
      rw [wp_set]
      dsimp only
      simp only [wp_set]
      congr 2
      exact (inferInstance : disjoint oracle_output chal_x_queried_gh).commute σ_lq y true
    · simp only [if_neg h]
      simp only [wp_pure, wp_set]
  · simp only [if_neg h1]

/-- `body_game_1' ow_adv t` is in `ow_challenge_x.compl.range`: every sub-program
    is chal_x-disjoint (adv via hypothesis, get/set oracle_input/output via
    disjointness, lazy_query via RO ⊥ chal_x, the if-set on chal_x_qg via
    chal_x_qg ⊥ chal_x). -/
private lemma body_game_1'_inRange_chal_x
    (ow_adv : Program state Unit)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (t : input) :
    (body_game_1' ow_adv t).inRange ow_challenge_x.compl.range := by
  unfold body_game_1' q_body_game_1'
  refine Program.inRange_bind ?_ (fun a => ?_)
  · refine Program.inRange_bind h_ow_adv_chal_x (fun _ => ?_)
    refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun inp => ?_)
    refine Program.inRange_bind ?_ (fun y => ?_)
    · exact Program.inRange_mono (lazy_query_inRange_ro inp)
        (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_x)
    refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
    exact Program.inRange_pure _ _
  · by_cases hh : a = t
    · simp only [if_pos hh]
      exact Program.set_inRange_compl_of_disjoint _ _ _
    · simp only [if_neg hh]
      exact Program.inRange_pure _ _

/-- `final_game_1' t` is in `ow_challenge_x.compl.range`. -/
private lemma final_game_1'_inRange_chal_x (t : input) :
    (final_game_1' t).inRange ow_challenge_x.compl.range := by
  unfold final_game_1' q_final_game_1'
  refine Program.inRange_bind ?_ (fun a => ?_)
  · refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun resp => ?_)
    refine Program.inRange_bind ?_ (fun y => ?_)
    · exact Program.inRange_mono (lazy_query_inRange_ro resp)
        (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_x)
    refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
    exact Program.inRange_pure _ _
  · by_cases hh : a = t
    · simp only [if_pos hh]
      exact Program.set_inRange_compl_of_disjoint _ _ _
    · simp only [if_neg hh]
      exact Program.inRange_pure _ _

/-- Loop+final bridge for Game 1: under the invariant `ow_challenge_x.get σ = t`,
    the loop-and-final wp's of Game 1 and Game 1' agree at any post `F`. Proven
    by induction on `q` with the chal_x-invariant threaded through each iter
    via `body_game_1_preserves_chal_x`. -/
private lemma loop_final_body_game_1_wp_eq
    (ow_adv : Program state Unit)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (t : input) (q : ℕ) :
    ∀ (F : Unit × state → ENNReal) (σ : state), ow_challenge_x.get σ = t →
      (loop_n q (body_game_1 ow_adv t) >>= fun _ => final_game_1 t).wp F σ
    = (loop_n q (body_game_1' ow_adv t) >>= fun _ => final_game_1' t).wp F σ := by
  induction q with
  | zero =>
    intro F σ h_cx
    show ((pure () : Program state Unit) >>= fun _ => final_game_1 t).wp F σ = _
    rw [Program.pure_bind]
    conv_rhs => rw [show (loop_n 0 (body_game_1' ow_adv t) >>= fun _ => final_game_1' t) =
                       final_game_1' t from by
                  show (pure () >>= fun _ => final_game_1' t) = _
                  rw [Program.pure_bind]]
    exact final_game_1_wp_eq_final_game_1'_at_chal_x_eq t F σ h_cx
  | succ n ih =>
    intro F σ h_cx
    -- LHS: loop_n (n+1) body_game_1 >>= final_game_1 = body >>= loop_n n body >>= final.
    -- Apply wp_bind directly (loop_n (n+1) body = body >>= fun _ => loop_n n body by rfl,
    -- and the outer >>= is body >>= (loop_n n body >>= final)).
    rw [show (loop_n (n+1) (body_game_1 ow_adv t) >>= fun _ => final_game_1 t) =
           body_game_1 ow_adv t >>= fun _ =>
             loop_n n (body_game_1 ow_adv t) >>= fun _ => final_game_1 t from by
         show (body_game_1 ow_adv t >>= fun _ => loop_n n (body_game_1 ow_adv t)) >>= _ = _
         rw [Program.bind_assoc]]
    conv_rhs => rw [show (loop_n (n+1) (body_game_1' ow_adv t) >>= fun _ => final_game_1' t) =
           body_game_1' ow_adv t >>= fun _ =>
             loop_n n (body_game_1' ow_adv t) >>= fun _ => final_game_1' t from by
         show (body_game_1' ow_adv t >>= fun _ => loop_n n (body_game_1' ow_adv t)) >>= _ = _
         rw [Program.bind_assoc]]
    rw [wp_bind]
    conv_rhs => rw [wp_bind]
    -- Step 1: convert LHS's body_game_1 → body_game_1' via body bridge.
    rw [body_game_1_wp_eq_body_game_1'_at_chal_x_eq ow_adv h_ow_adv_chal_x t _ σ h_cx]
    -- Step 2: strengthen with chal_x preservation on both sides (body_game_1' is chal_x-disjoint).
    rw [Program.wp_strengthen_lens_preserved ow_challenge_x
        (body_game_1'_inRange_chal_x ow_adv h_ow_adv_chal_x t)]
    conv_rhs => rw [Program.wp_strengthen_lens_preserved ow_challenge_x
        (body_game_1'_inRange_chal_x ow_adv h_ow_adv_chal_x t)]
    -- Step 3: equate posts; in the chal_x-preserved branch, apply IH.
    congr 1
    funext aσ_body
    obtain ⟨_, σ_body⟩ := aσ_body
    dsimp only
    by_cases h_inv : ow_challenge_x.get σ_body = ow_challenge_x.get σ
    · simp only [if_pos h_inv]
      rw [h_cx] at h_inv
      exact ih F σ_body h_inv
    · simp only [if_neg h_inv]

set_option maxHeartbeats 4000000 in
/-- Generic prefix-peel helper for `guess_experiment`: peels env, uniform t,
    set tvar t, set mvar false, and the trailing get mvar, reducing the wp
    to a wp at the inner state involving only (loop_n q (body t) >>= final t).

    Used to bridge guess_experiment_game_1 and guess_experiment_game_1' at the
    canonical inner form, where loop_final_body_game_1_wp_eq applies. -/
private lemma guess_experiment_wp_inner_eq
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (env : Program state Unit) (tvar : Lens T state) (mvar : Lens Bool state)
    (body body' : T → Program state Unit)
    (final final' : T → Program state Unit) (q : ℕ)
    (h_inner : ∀ (σ_inner : state) (t : T),
       tvar.get σ_inner = t →
       (loop_n q (body t) >>= fun _ => final t).wp
         (fun aσ : Unit × state => if mvar.get aσ.2 then (1 : ENNReal) else 0) σ_inner
       = (loop_n q (body' t) >>= fun _ => final' t).wp
         (fun aσ : Unit × state => if mvar.get aσ.2 then (1 : ENNReal) else 0) σ_inner)
    [disjoint mvar tvar] (σ : state) :
    (guess_experiment env Program.uniform tvar mvar body final q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    = (guess_experiment env Program.uniform tvar mvar body' final' q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  haveI : disjoint tvar mvar := disjoint.symm inferInstance
  -- Show the inner post equality.
  have h_inner_post : ∀ (σ_env : state) (t : T),
      (Program.set tvar t >>= fun _ =>
       Program.set mvar false >>= fun _ =>
       loop_n q (body t) >>= fun _ =>
       final t >>= fun _ =>
       Program.get mvar).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ_env
      = (Program.set tvar t >>= fun _ =>
         Program.set mvar false >>= fun _ =>
         loop_n q (body' t) >>= fun _ =>
         final' t >>= fun _ =>
         Program.get mvar).wp
          (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ_env := by
    intro σ_env t
    rw [wp_bind, wp_set]
    conv_rhs => rw [wp_bind, wp_set]
    dsimp only
    rw [wp_bind, wp_set]
    conv_rhs => rw [wp_bind, wp_set]
    dsimp only
    set σ_inner : state := mvar.set false (tvar.set t σ_env) with σ_inner_def
    have h_tvar_get : tvar.get σ_inner = t := by
      show tvar.get (mvar.set false (tvar.set t σ_env)) = t
      rw [Lens.get_of_disjoint_set tvar mvar]
      exact tvar.set_get σ_env t
    -- Reassociate via bind_assoc: `loop >>= (\_. final >>= (\_. get))` =
    -- `(loop >>= (\_. final)) >>= (\_. get)`.
    rw [← Program.bind_assoc]
    conv_rhs => rw [← Program.bind_assoc]
    -- Now: ((loop >>= final) >>= get mvar).wp F σ_inner. Apply wp_bind to peel get mvar.
    rw [wp_bind]
    conv_rhs => rw [wp_bind]
    have h_post :
        (fun aσ : Unit × state =>
          (Program.get mvar).wp (fun bσ : Bool × state =>
            if bσ.1 then (1 : ENNReal) else 0) aσ.2)
        = (fun aσ : Unit × state => if mvar.get aσ.2 then (1 : ENNReal) else 0) := by
      funext aσ; rw [wp_get]
    rw [h_post]
    exact h_inner σ_inner t h_tvar_get
  -- Now apply at the guess_experiment level.
  unfold guess_experiment
  conv_lhs => rw [wp_bind]
  conv_rhs => rw [wp_bind]
  congr 1
  funext aσ_env
  obtain ⟨_, σ_env⟩ := aσ_env
  dsimp only
  conv_lhs => rw [wp_bind, wp_uniform]
  conv_rhs => rw [wp_bind, wp_uniform]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  exact h_inner_post σ_env t

set_option maxHeartbeats 800000 in
/-- **Game-hop bridge**: at the chal_x_queried_gh-firing post,
    `guess_experiment_game_1` and `guess_experiment_game_1'` have the same wp.

    Inside the loop, `lazy_query_tracked inp` (which reads chal_x from state and
    fires `set chal_x_queried_gh true` iff `inp = chal_x`) is wp-equivalent to
    `lazy_query inp; if inp = t then set chal_x_queried_gh true` provided
    `chal_x.get state = t`. The schema's prefix sets `chal_x ← t`, so this
    invariant is established before the loop and preserved by every iter
    (no body modifies chal_x). -/
private lemma guess_experiment_game_1_wp_eq_game_1'
    (ow_adv : Program state Unit)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (q : ℕ) (σ : state) :
    (guess_experiment_game_1 ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    = (guess_experiment_game_1' ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  unfold guess_experiment_game_1 guess_experiment_game_1'
  refine guess_experiment_wp_inner_eq lazy_init ow_challenge_x chal_x_queried_gh
    (body_game_1 ow_adv) (body_game_1' ow_adv) final_game_1 final_game_1' q ?_ σ
  intro σ_inner t h_tvar
  exact loop_final_body_game_1_wp_eq ow_adv h_ow_adv_chal_x t q _ σ_inner h_tvar

/-- Helper: body_game_1 ow_adv and body_recording_game_1 ow_adv have the same
    wp at queries_input-ignoring posts. body_recording adds only a trailing
    qi append, which is wp-invisible to qi-ignoring F. -/
private lemma body_game_1_wp_eq_body_recording_game_1
    (ow_adv : Program state Unit) (t : input)
    (F : Unit × state → ENNReal)
    (h_F : IgnoresLens queries_input F)
    (σ : state) :
    (body_game_1 ow_adv t).wp F σ = (body_recording_game_1 ow_adv).wp F σ := by
  unfold body_game_1 body_recording_game_1
  conv_lhs => rw [wp_bind]
  conv_rhs => rw [wp_bind]
  congr 1
  funext aσ_ow
  obtain ⟨_, σ_1⟩ := aσ_ow
  dsimp only
  conv_lhs => rw [wp_bind, wp_get]
  conv_rhs => rw [wp_bind, wp_get]
  dsimp only
  conv_lhs => rw [wp_bind]
  conv_rhs => rw [wp_bind]
  congr 1
  funext aσ_lq
  obtain ⟨y, σ_2⟩ := aσ_lq
  dsimp only
  conv_lhs => rw [wp_set]
  conv_rhs => rw [wp_bind, wp_set]
  dsimp only
  rw [wp_qi_get_set_invisible _ F h_F _]

/-- body_game_1 is queries_input-disjoint when ow_adv is. -/
private lemma body_game_1_inRange_qi
    (ow_adv : Program state Unit)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (t : input) :
    (body_game_1 ow_adv t).inRange queries_input.compl.range := by
  unfold body_game_1
  refine Program.inRange_bind h_ow_adv_qi (fun _ => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun inp => ?_)
  refine Program.inRange_bind (lazy_query_tracked_inRange_queries_input _) (fun y => ?_)
  exact Program.set_inRange_compl_of_disjoint _ _ _

/-- final_game_1 is queries_input-disjoint. -/
private lemma final_game_1_inRange_qi (t : input) :
    (final_game_1 t).inRange queries_input.compl.range := by
  unfold final_game_1
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun resp => ?_)
  refine Program.inRange_bind (lazy_query_tracked_inRange_queries_input _) (fun y => ?_)
  exact Program.set_inRange_compl_of_disjoint _ _ _

/-- A queries_input-disjoint program's wp at qi-ignoring F is invariant under
    setting queries_input on the input. -/
private lemma wp_qi_input_invariant_of_inRange_qi
    {α : Type} (p : Program state α)
    (h_p_qi : p.inRange queries_input.compl.range)
    (F : α × state → ENNReal) (h_F : IgnoresLens queries_input F)
    (σ : state) (v : List input) :
    p.wp F (queries_input.set v σ) = p.wp F σ := by
  have h_f_updates : (queries_input.update (Function.const _ v))
      ∈ ((queries_input.compl.range : LensRange state)ᶜ).updates := by
    rw [show ((queries_input.compl.range : LensRange state)ᶜ) = queries_input.range from by
        rw [LensRange.complement_range, LensRange.compl_compl]]
    exact ⟨Function.const _ v, Set.mem_univ _, rfl⟩
  have h_set_eq : queries_input.update (Function.const _ v) σ = queries_input.set v σ := by
    show queries_input.set ((Function.const _ v) (queries_input.get σ)) σ = queries_input.set v σ
    rfl
  rw [← h_set_eq]
  rw [Program.wp_shift_input h_p_qi h_f_updates]
  congr 1
  funext xs
  show F (xs.1, queries_input.update (Function.const _ v) xs.2) = F xs
  show F (xs.1, queries_input.set v xs.2) = F xs
  exact h_F xs v

/-- Body equivalence packaged as EquivModuloLens. -/
private lemma body_game_1_equiv_body_recording_game_1
    (ow_adv : Program state Unit) (t : input) :
    Program.EquivModuloLens queries_input
      (body_game_1 ow_adv t) (body_recording_game_1 ow_adv) :=
  fun F h_F σ => body_game_1_wp_eq_body_recording_game_1 ow_adv t F h_F σ

/-- Loop equivalence at the wp level — via the codebase's existing
    `loop_n_congr` lemma. -/
private lemma loop_n_body_game_1_wp_eq_loop_n_body_recording_game_1
    (ow_adv : Program state Unit) (t : input)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (n : ℕ) (F : Unit × state → ENNReal) (h_F : IgnoresLens queries_input F)
    (σ : state) :
    (loop_n n (body_game_1 ow_adv t)).wp F σ
    = (loop_n n (body_recording_game_1 ow_adv)).wp F σ :=
  loop_n_congr (body_game_1_inRange_qi ow_adv h_ow_adv_qi t)
    (body_game_1_equiv_body_recording_game_1 ow_adv t) n F h_F σ

/-- Helper: final_game_1 t and final_recording_game_1 have the same wp at
    queries_input-ignoring posts. -/
private lemma final_game_1_wp_eq_final_recording_game_1
    (t : input)
    (F : Unit × state → ENNReal)
    (h_F : IgnoresLens queries_input F)
    (σ : state) :
    (final_game_1 t).wp F σ = final_recording_game_1.wp F σ := by
  unfold final_game_1 final_recording_game_1
  conv_lhs => rw [wp_bind, wp_get]
  conv_rhs => rw [wp_bind, wp_get]
  dsimp only
  conv_lhs => rw [wp_bind]
  conv_rhs => rw [wp_bind]
  congr 1
  funext aσ_lq
  obtain ⟨y, σ_2⟩ := aσ_lq
  dsimp only
  conv_lhs => rw [wp_set]
  conv_rhs => rw [wp_bind, wp_set]
  dsimp only
  rw [wp_qi_get_set_invisible _ F h_F _]

/-- body_recording_game_1's wp at qi-ignoring posts is invariant under
    setting queries_input on the input. Proven by routing through body_game_1
    (which is qi-disjoint). -/
private lemma body_recording_game_1_wp_qi_input_invariant
    (ow_adv : Program state Unit) (t : input)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (F : Unit × state → ENNReal) (h_F : IgnoresLens queries_input F)
    (σ : state) (v : List input) :
    (body_recording_game_1 ow_adv).wp F (queries_input.set v σ)
    = (body_recording_game_1 ow_adv).wp F σ := by
  rw [← body_game_1_wp_eq_body_recording_game_1 ow_adv t F h_F
        (queries_input.set v σ)]
  rw [wp_qi_input_invariant_of_inRange_qi _
        (body_game_1_inRange_qi ow_adv h_ow_adv_qi t) F h_F σ v]
  rw [body_game_1_wp_eq_body_recording_game_1 ow_adv t F h_F σ]

/-- loop_n body_recording's wp at qi-ignoring posts is qi-input-invariant.
    Same routing trick: factor through loop_n body_game_1 (which is qi-disjoint). -/
private lemma loop_n_body_recording_game_1_wp_qi_input_invariant
    (ow_adv : Program state Unit) (t : input)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (n : ℕ) (F : Unit × state → ENNReal) (h_F : IgnoresLens queries_input F)
    (σ : state) (v : List input) :
    (loop_n n (body_recording_game_1 ow_adv)).wp F (queries_input.set v σ)
    = (loop_n n (body_recording_game_1 ow_adv)).wp F σ := by
  rw [← loop_n_body_game_1_wp_eq_loop_n_body_recording_game_1 ow_adv t h_ow_adv_qi n F h_F
        (queries_input.set v σ)]
  rw [wp_qi_input_invariant_of_inRange_qi _
        (loop_n_inRange _ (body_game_1_inRange_qi ow_adv h_ow_adv_qi t) n) F h_F σ v]
  rw [loop_n_body_game_1_wp_eq_loop_n_body_recording_game_1 ow_adv t h_ow_adv_qi n F h_F σ]

/-- final_recording_game_1's wp at qi-ignoring posts is qi-input-invariant. -/
private lemma final_recording_game_1_wp_qi_input_invariant
    (t : input)
    (F : Unit × state → ENNReal) (h_F : IgnoresLens queries_input F)
    (σ : state) (v : List input) :
    final_recording_game_1.wp F (queries_input.set v σ)
    = final_recording_game_1.wp F σ := by
  rw [← final_game_1_wp_eq_final_recording_game_1 t F h_F (queries_input.set v σ)]
  rw [wp_qi_input_invariant_of_inRange_qi _ (final_game_1_inRange_qi t) F h_F σ v]
  rw [final_game_1_wp_eq_final_recording_game_1 t F h_F σ]

/-- Bridge: LHS with body_game_1 = LHS with body_recording_game_1, for the
    full game_1 LHS (loop + final + get chal_x_qg). Uses the loop and final
    equivalences with the qi-ignoring chal_x_qg post. -/
private lemma loop_final_get_game_1_wp_eq_recording
    (ow_adv : Program state Unit)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (t : input) (q : ℕ) (σ : state) :
    (loop_n q (body_game_1 ow_adv t) >>= fun _ : Unit =>
     final_game_1 t >>= fun _ : Unit =>
     Program.get chal_x_queried_gh).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    = (loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
       final_recording_game_1 >>= fun _ : Unit =>
       Program.get chal_x_queried_gh).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  -- Post `if bσ.1 then 1 else 0` after `get chal_x_qg` reduces to
  -- `fun aσ : Unit × state => if chal_x_qg.get aσ.2 then 1 else 0` = F_chal_xqg.
  set F_chal_xqg : Unit × state → ENNReal :=
    fun aσ => if chal_x_queried_gh.get aσ.2 = true then (1 : ENNReal) else 0
    with hF_chal_xqg
  have h_F_chal_xqg_qi : IgnoresLens queries_input F_chal_xqg := by
    intro aσ v
    show (if chal_x_queried_gh.get (queries_input.set v aσ.2) = true then _ else _)
       = (if chal_x_queried_gh.get aσ.2 = true then _ else _)
    rw [Lens.get_of_disjoint_set chal_x_queried_gh queries_input]
  -- Step 1: peel the get chal_x_qg. After this, the post becomes F_chal_xqg.
  have h_get_collapse : ∀ (k : Program state Unit) (σ_k : state),
      (k >>= fun _ : Unit => Program.get chal_x_queried_gh).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ_k
      = k.wp F_chal_xqg σ_k := by
    intro k σ_k
    rw [wp_bind]
    congr 1
    funext aσ
    rw [wp_get]
  -- Apply h_get_collapse on both sides (LHS and RHS of the goal).
  -- After: (loop_n q body_game_1 >>= fun _ => final_game_1).wp F_chal_xqg σ
  --      = (loop_n q body_recording >>= fun _ => final_recording).wp F_chal_xqg σ
  rw [show (loop_n q (body_game_1 ow_adv t) >>= fun _ : Unit =>
          final_game_1 t >>= fun _ : Unit =>
          Program.get chal_x_queried_gh)
       = ((loop_n q (body_game_1 ow_adv t) >>= fun _ : Unit => final_game_1 t)
          >>= fun _ : Unit => Program.get chal_x_queried_gh)
       from by simp [Program.bind_assoc]]
  rw [show (loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
          final_recording_game_1 >>= fun _ : Unit =>
          Program.get chal_x_queried_gh)
       = ((loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit => final_recording_game_1)
          >>= fun _ : Unit => Program.get chal_x_queried_gh)
       from by simp [Program.bind_assoc]]
  rw [h_get_collapse, h_get_collapse]
  -- Step 2: peel final via wp_bind, then use final_game_1 ↔ final_recording equivalence.
  rw [wp_bind, wp_bind]
  -- Inner post: fun aσ : Unit × state => final_X.wp F_chal_xqg aσ.2 (X varies).
  -- This inner post is qi-ignoring (final_X is qi-disjoint + F_chal_xqg qi-ignoring).
  have h_final_post_qi : IgnoresLens queries_input
      (fun aσ : Unit × state => (final_game_1 t).wp F_chal_xqg aσ.2) := by
    intro aσ v
    exact wp_qi_input_invariant_of_inRange_qi _ (final_game_1_inRange_qi t)
      F_chal_xqg h_F_chal_xqg_qi _ v
  -- Use loop equivalence on the loop's wp.
  rw [loop_n_body_game_1_wp_eq_loop_n_body_recording_game_1 ow_adv t h_ow_adv_qi q _
      h_final_post_qi σ]
  -- Now: (loop_n q body_recording).wp (fun aσ => (final_game_1 t).wp F_chal_xqg aσ.2) σ
  --    = (loop_n q body_recording).wp (fun aσ => final_recording.wp F_chal_xqg aσ.2) σ
  congr 1
  funext aσ
  exact final_game_1_wp_eq_final_recording_game_1 t F_chal_xqg h_F_chal_xqg_qi aσ.2

/-- The full "loop + final + get chal_x_qg" chain (with recording bodies) is
    qi-input-invariant. -/
private lemma loop_final_get_recording_wp_qi_input_invariant
    (ow_adv : Program state Unit) (t : input)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (q : ℕ) (σ : state) (v : List input) :
    (loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
     final_recording_game_1 >>= fun _ : Unit =>
     Program.get chal_x_queried_gh).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0)
       (queries_input.set v σ)
    = (loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
       final_recording_game_1 >>= fun _ : Unit =>
       Program.get chal_x_queried_gh).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  rw [← loop_final_get_game_1_wp_eq_recording ow_adv h_ow_adv_qi t q (queries_input.set v σ)]
  rw [← loop_final_get_game_1_wp_eq_recording ow_adv h_ow_adv_qi t q σ]
  have h_chain_qi : (loop_n q (body_game_1 ow_adv t) >>= fun _ : Unit =>
                       final_game_1 t >>= fun _ : Unit =>
                       Program.get chal_x_queried_gh).inRange
                      queries_input.compl.range := by
    refine Program.inRange_bind
      (loop_n_inRange _ (body_game_1_inRange_qi ow_adv h_ow_adv_qi t) q) (fun _ => ?_)
    refine Program.inRange_bind (final_game_1_inRange_qi t) (fun _ => ?_)
    exact Program.get_inRange_compl_of_disjoint _ _
  have h_F_qi : IgnoresLens queries_input
      (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) := by
    intro bσ v'
    rfl
  exact wp_qi_input_invariant_of_inRange_qi _ h_chain_qi _ h_F_qi σ v

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

/-- **Game 1 correspondence**.

    `body_game_1 ow_adv`'s match-fire on `chal_x_queried_gh` (via
    `lazy_query_tracked` flipping the flag when `inp = chal_x = t`) corresponds
    to `t ∈ queries_input` after `body_recording_game_1 ow_adv` (which appends
    each `inp` to the list). Both events are "some lazy_query_tracked saw
    `inp = t`".

    Proof structure: route through Game 1':
    1. Convert LHS body_game_1 → body_game_1' via `loop_final_body_game_1_wp_eq`
       (the game-hop bridge, requires chal_x.get σ_inner = t which is established
       by the prefix `set ow_challenge_x t`).
    2. Apply `schema_inner_equation` for Game 1' (uses q_body_game_1' and
       q_final_game_1' which are chal_x_qg, qi, and ow_challenge_x disjoint).
    3. Convert RHS body_recording_game_1' → body_recording_game_1 via
       `body_recording_game_1_wp_eq_body_recording_game_1'` and its loop+final
       lifting (the chal_x_qg flip in lazy_query_tracked is invisible at
       chal_x_qg-ignoring posts; the trailing `get qi; set chal_x_qg (decide);
       get chal_x_qg` produces a qi-only post which IS chal_x_qg-ignoring). -/
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
  refine le_of_eq ?_
  -- We will route LHS_game1 = LHS_game1' = RHS_game1' = RHS_game1.
  -- Step 1: LHS_game1 = LHS_game1' via game-hop bridge.
  have h_LHS_eq :
      (Program.set ow_challenge_x t >>= fun _ : Unit =>
       Program.set chal_x_queried_gh false >>= fun _ : Unit =>
       loop_n q (body_game_1 ow_adv t) >>= fun _ : Unit =>
       final_game_1 t >>= fun _ : Unit =>
       Program.get chal_x_queried_gh).wp
         (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
      =
      (Program.set ow_challenge_x t >>= fun _ : Unit =>
       Program.set chal_x_queried_gh false >>= fun _ : Unit =>
       loop_n q (body_game_1' ow_adv t) >>= fun _ : Unit =>
       final_game_1' t >>= fun _ : Unit =>
       Program.get chal_x_queried_gh).wp
         (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ' := by
    rw [wp_bind, wp_set, wp_bind, wp_set]
    conv_rhs => rw [wp_bind, wp_set, wp_bind, wp_set]
    dsimp only
    set σ_inner : state := chal_x_queried_gh.set false (ow_challenge_x.set t σ')
    have h_chal_x_inner : ow_challenge_x.get σ_inner = t := by
      show ow_challenge_x.get (chal_x_queried_gh.set false (ow_challenge_x.set t σ')) = t
      rw [Lens.get_of_disjoint_set ow_challenge_x chal_x_queried_gh]
      exact ow_challenge_x.set_get σ' t
    -- Re-associate so `(loop body >>= final) >>= get chal_x_qg` is exposed for loop_final bridge.
    rw [← Program.bind_assoc]
    conv_rhs => rw [← Program.bind_assoc]
    rw [wp_bind]
    conv_rhs => rw [wp_bind]
    have h_post :
        (fun aσ : Unit × state =>
          (Program.get chal_x_queried_gh).wp
            (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) aσ.2)
        = (fun aσ : Unit × state =>
            if chal_x_queried_gh.get aσ.2 then (1 : ENNReal) else 0) := by
      funext aσ; rw [wp_get]
    rw [h_post]
    exact loop_final_body_game_1_wp_eq ow_adv h_ow_adv_chal_x t q _ σ_inner h_chal_x_inner
  rw [h_LHS_eq]
  -- Step 2: LHS_game1' = RHS_game1' via schema_inner_equation for Game 1'.
  -- LHS_game1' has the form `set tvar t; set mvar false; loop q_body >>= match_check; q_final >>= match_check; get mvar`.
  -- We need to substitute body_game_1' = q_body_game_1' >>= match_check, etc., via unfold.
  haveI : disjoint ow_challenge_x chal_x_queried_gh := disjoint.symm inferInstance
  haveI : disjoint ow_challenge_x queries_input := disjoint.symm inferInstance
  show (Program.set ow_challenge_x t >>= fun _ : Unit =>
        Program.set chal_x_queried_gh false >>= fun _ : Unit =>
        loop_n q (body_game_1' ow_adv t) >>= fun _ : Unit =>
        final_game_1' t >>= fun _ : Unit =>
        Program.get chal_x_queried_gh).wp _ σ' = _
  unfold body_game_1' final_game_1'
  rw [show (Program.set queries_input [] >>= fun _ : Unit =>
            loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
            final_recording_game_1 >>= fun _ : Unit =>
            Program.get queries_input >>= fun qs =>
            Program.set chal_x_queried_gh (decide (t ∈ qs)) >>= fun _ : Unit =>
            Program.get chal_x_queried_gh).wp
              (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
        = (Program.set queries_input [] >>= fun _ : Unit =>
            loop_n q (q_body_game_1' ow_adv >>= fun a : input =>
              Program.get queries_input >>= fun qs : List input =>
              Program.set queries_input (qs ++ [a])) >>= fun _ : Unit =>
            (q_final_game_1' >>= fun a : input =>
              Program.get queries_input >>= fun qs : List input =>
              Program.set queries_input (qs ++ [a])) >>= fun _ : Unit =>
            Program.get queries_input >>= fun qs =>
            Program.set chal_x_queried_gh (decide (t ∈ qs)) >>= fun _ : Unit =>
            Program.get chal_x_queried_gh).wp
              (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ' from ?_]
  · exact schema_inner_equation ow_challenge_x chal_x_queried_gh queries_input
      (q_body_game_1' ow_adv) q_final_game_1'
      (q_body_game_1'_inRange_chal_x_queried_gh ow_adv h_ow_adv_chal_x_qg)
      (q_body_game_1'_inRange_queries_input ow_adv h_ow_adv_qi)
      (q_body_game_1'_inRange_ow_challenge_x ow_adv h_ow_adv_chal_x)
      q_final_game_1'_inRange_chal_x_queried_gh
      q_final_game_1'_inRange_queries_input
      q_final_game_1'_inRange_ow_challenge_x
      q σ' t
  · -- Step 3: RHS_game1' = RHS_game1 via recording bridges (chal_x_qg-ignoring inner post).
    rw [wp_bind, wp_set]
    conv_rhs => rw [wp_bind, wp_set]
    dsimp only
    set σ_rhs_inner : state := queries_input.set [] σ' with σ_rhs_inner_def
    -- Helper: trailing reduction (the get qi; set chal_x_qg; get chal_x_qg is qi-dependent only).
    have h_reduce : ∀ (X : Program state Unit) (s : state),
        (X >>= fun _ : Unit =>
          Program.get queries_input >>= fun qs : List input =>
          Program.set chal_x_queried_gh (decide (t ∈ qs)) >>= fun _ : Unit =>
          Program.get chal_x_queried_gh).wp
          (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) s
        = X.wp (fun aσ : Unit × state =>
            if decide (t ∈ queries_input.get aσ.2) then (1 : ENNReal) else 0) s := by
      intro X s
      rw [wp_bind]
      congr 1
      funext aσ_X
      rw [wp_bind, wp_get]
      dsimp only
      rw [wp_bind, wp_set, wp_get]
      dsimp only
      rw [Lens.set_get chal_x_queried_gh]
    -- The goal LHS has body_recording_game_1, RHS has body_recording_game_1' (unfolded).
    -- Reassociate so loop+final is the prefix on both sides.
    rw [show (loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
              final_recording_game_1 >>= fun _ : Unit =>
              Program.get queries_input >>= fun qs : List input =>
              Program.set chal_x_queried_gh (decide (t ∈ qs)) >>= fun _ : Unit =>
              Program.get chal_x_queried_gh) =
            ((loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit => final_recording_game_1)
              >>= fun _ : Unit =>
              Program.get queries_input >>= fun qs : List input =>
              Program.set chal_x_queried_gh (decide (t ∈ qs)) >>= fun _ : Unit =>
              Program.get chal_x_queried_gh) from
      (Program.bind_assoc _ _ _).symm]
    -- RHS uses UNFOLDED forms: q_body_game_1' ow_adv >>= fun a => get qi >>= ... etc.
    conv_rhs => rw [show (loop_n q (q_body_game_1' ow_adv >>= fun a : input =>
              Program.get queries_input >>= fun qs : List input =>
              Program.set queries_input (qs ++ [a])) >>= fun _ : Unit =>
              (q_final_game_1' >>= fun a : input =>
                Program.get queries_input >>= fun qs : List input =>
                Program.set queries_input (qs ++ [a])) >>= fun _ : Unit =>
              Program.get queries_input >>= fun qs : List input =>
              Program.set chal_x_queried_gh (decide (t ∈ qs)) >>= fun _ : Unit =>
              Program.get chal_x_queried_gh) =
            ((loop_n q (q_body_game_1' ow_adv >>= fun a : input =>
                Program.get queries_input >>= fun qs : List input =>
                Program.set queries_input (qs ++ [a])) >>= fun _ : Unit =>
              q_final_game_1' >>= fun a : input =>
                Program.get queries_input >>= fun qs : List input =>
                Program.set queries_input (qs ++ [a])) >>= fun _ : Unit =>
              Program.get queries_input >>= fun qs : List input =>
              Program.set chal_x_queried_gh (decide (t ∈ qs)) >>= fun _ : Unit =>
              Program.get chal_x_queried_gh) from
      (Program.bind_assoc _ _ _).symm]
    -- Now apply h_reduce on both sides.
    rw [h_reduce (loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
        final_recording_game_1)]
    conv_rhs => rw [h_reduce (loop_n q (q_body_game_1' ow_adv >>= fun a : input =>
                Program.get queries_input >>= fun qs : List input =>
                Program.set queries_input (qs ++ [a])) >>= fun _ : Unit =>
              q_final_game_1' >>= fun a : input =>
                Program.get queries_input >>= fun qs : List input =>
                Program.set queries_input (qs ++ [a]))]
    -- Now both sides: (loop body_X >>= final_X).wp F_qi σ_rhs_inner where F_qi is qi-only (chal_x_qg-ignoring).
    have h_F_qi : IgnoresLens chal_x_queried_gh
        (fun aσ : Unit × state =>
          if decide (t ∈ queries_input.get aσ.2) then (1 : ENNReal) else 0) := by
      intro aσ v
      show (if decide (t ∈ queries_input.get (chal_x_queried_gh.set v aσ.2)) then _ else _)
         = if decide (t ∈ queries_input.get aσ.2) then _ else _
      rw [Lens.get_of_disjoint_set queries_input chal_x_queried_gh]
    -- Apply EquivModuloLens chain. Goal: (loop body_rec).wp F_qi σ = (loop body_rec').wp F_qi σ.
    -- We need EquivModuloLens with LHS reference (body_rec'), since loop_n_congr requires the
    -- reference body to be chal_x_qg-disjoint (body_rec is NOT).
    have h_body_equiv : Program.EquivModuloLens chal_x_queried_gh
        (body_recording_game_1' ow_adv) (body_recording_game_1 ow_adv) :=
      Program.EquivModuloLens.symm
        (body_recording_game_1_wp_eq_body_recording_game_1' ow_adv)
    have h_loop_equiv : Program.EquivModuloLens chal_x_queried_gh
        (loop_n q (body_recording_game_1' ow_adv))
        (loop_n q (body_recording_game_1 ow_adv)) :=
      loop_n_congr
        (body_recording_game_1'_inRange_chal_x_queried_gh ow_adv h_ow_adv_chal_x_qg)
        h_body_equiv q
    have h_final_equiv : Program.EquivModuloLens chal_x_queried_gh
        final_recording_game_1' final_recording_game_1 :=
      Program.EquivModuloLens.symm
        (final_recording_game_1_wp_eq_final_recording_game_1')
    have h_loop_final_equiv : Program.EquivModuloLens chal_x_queried_gh
        (loop_n q (body_recording_game_1' ow_adv) >>= fun _ : Unit => final_recording_game_1')
        (loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit => final_recording_game_1) :=
      Program.EquivModuloLens.bind h_loop_equiv (fun _ => h_final_equiv)
        (fun _ => final_recording_game_1'_inRange_chal_x_queried_gh)
    -- Goal direction: (loop body_rec >>= final_rec).wp F_qi σ = (loop body_rec' >>= final_rec').wp F_qi σ.
    -- h_loop_final_equiv has direction body_rec' → body_rec. Symm gives body_rec → body_rec'.
    exact (h_loop_final_equiv.symm) _ h_F_qi σ_rhs_inner

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
private lemma ow_game_1_full_tail_equiv_lq_lqt
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
    (h_F : IgnoresChalXQueriedGh F)
    (σ : state) :
    (ow_game_1 ow_adv q).wp F σ = (ow_game_1_tracked ow_adv q).wp F σ := by
  have h_F' : IgnoresLens chal_x_queried_gh F := fun aσ v => h_F aσ v
  suffices h_equiv : Program.EquivModuloLens chal_x_queried_gh
      (ow_game_1 ow_adv q) (ow_game_1_tracked ow_adv q) by
    exact h_equiv F h_F' σ
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
    (fun _ => ow_game_1_full_tail_equiv_lq_lqt ow_adv h_ow_adv_flag q))


end Game1
