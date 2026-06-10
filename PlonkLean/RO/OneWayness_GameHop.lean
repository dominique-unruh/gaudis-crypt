import PlonkLean.RO
import PlonkLean.RO.OneWayness
import PlonkLean.EquivModuloLens
import PlonkLean.RO.OneWayness_GameHop.Definitions
import PlonkLean.RO.OneWayness_GameHop.GuessExperiment
import PlonkLean.RO.OneWayness_GameHop.UpToBad
import PlonkLean.RO.OneWayness_GameHop.Game1
import PlonkLean.RO.OneWayness_GameHop.Game2

/-!
# Game-hopping proof of one-wayness

An alternative proof of the OW lazy bound
`P[ow_experiment wins] ≤ 2(q+1)/|output|` via three games and one
up-to-bad analysis, with both probability bounds reduced to a single
unifying "guessing game" lemma.

See `notes/RO/OW_GameHop_Plan.md` for the full plan.

`guess_experiment_le_interim_assumption` is a proper theorem parameterized by
a `h_correspondence` hypothesis (the body↔body_recording correspondence). The
hypothesis is discharged at each call site by per-game correspondence lemmas
(`game_1_correspondence`, `game_2_correspondence`), which are currently
declared as `axiom`s — they're concrete, TRUE statements about specific
programs, with deferred proof effort. Proving them requires inducting on the
loop with the invariant `matched_var = decide (t ∈ queries_list_var)`
maintained by the body_recording. The existing proof in
`PlonkLean/RO/OneWayness.lean` remains intact.
-/

/-! ## The final game-hop bound

Combining the proved infrastructure:
* `ow_game_0_eq_ow_game_1` — Hop 0 → 1 (program equality).
* `ow_game_1_wp_eq_ow_game_1_tracked_wp_of_flag_ignoring` — tracking is
  invisible for flag-ignoring posts.
* `ow_game_1_tracked_le_ow_game_2_tracked_plus_bad` — Hop 1 → 2 via
  `Program.up_to_bad`.
* `ow_game_2_tracked_wins_le_guess_output_bound` — Game 2 win bound.
* `ow_game_1_tracked_bad_le_guess_input_bound` — bad event bound.
* `card_input_ge_output` — |input| ≥ |output|.

Yields `P[ow_experiment wins] ≤ 2(q+1)/|output|`. -/

section GameHopParam_Final

variable (ow_adv : Program state Unit)

/-- **The OW lazy bound via the game-hop chain**.
    Matches the existing `ow_lazy_bound` (in `QueryHit.lean`), proved via
    the game-hopping + up-to-bad chain instead of the
    useful_preimage/deferred-sampling machinery. -/
theorem ow_lazy_bound_via_gamehop
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_ow_adv_matched_chal_y : ow_adv.inRange matched_chal_y.compl.range)
    (h_ow_adv_queries_output : ow_adv.inRange queries_output.compl.range)
    (h_ow_adv_queries_input : ow_adv.inRange queries_input.compl.range)
    (h_ow_adv_mass_one : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1)
    (h_ow_adv_chal_x_blind : ∀ (F : Unit × state → ENNReal) (σ : state) (v : input),
      ow_adv.wp F (ow_challenge_x.set v σ) = ow_adv.wp F σ)
    (h_ow_adv_chal_y_blind : ∀ (F : Unit × state → ENNReal) (σ : state) (v : output),
      ow_adv.wp F (ow_challenge_y.set v σ) = ow_adv.wp F σ)
    (q : ℕ) (σ : state) :
    (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ (2 * (q + 1) : ENNReal) / Fintype.card output := by
  -- Win indicator is flag-ignoring (depends only on `bσ.1`) and RO-invariant.
  set Win : Bool × state → ENNReal := fun bσ => if bσ.1 then (1 : ENNReal) else 0 with Win_def
  have h_Win_flag : IgnoresChalXQueriedGh Win := by
    intro aσ b
    simp [Win_def]
  have h_Win_RO_inv : ∀ (bσ : Bool × state) (y : output),
      Win (bσ.1, insert_at_chal_x y bσ.2) = Win bσ := by
    intro bσ y
    simp [Win_def]
  -- Bridge: ow_experiment.wp Win = ow_game_0.wp Win = ow_game_1.wp Win = ow_game_1_tracked.wp Win.
  show (ow_experiment ow_adv q lazy_init lazy_query).wp Win σ
       ≤ (2 * (q + 1) : ENNReal) / Fintype.card output
  rw [show (ow_experiment ow_adv q lazy_init lazy_query) = ow_game_0 ow_adv q from rfl]
  rw [ow_game_0_eq_ow_game_1 ow_adv q]
  rw [ow_game_1_wp_eq_ow_game_1_tracked_wp_of_flag_ignoring ow_adv
      h_ow_adv_chal_x_queried_gh q Win h_Win_flag σ]
  -- Apply up_to_bad: ow_game_1_tracked.wp Win ≤ ow_game_2_tracked.wp Win + bad-wp.
  calc (ow_game_1_tracked ow_adv q).wp Win σ
      ≤ (ow_game_2_tracked ow_adv q).wp Win σ
        + (ow_game_1_tracked ow_adv q).wp
            (fun bσ : Bool × state =>
              if chal_x_queried_gh.get bσ.2 = true then Win bσ else 0) σ := by
        exact ow_game_1_tracked_le_ow_game_2_tracked_plus_bad ow_adv
          h_ow_adv h_ow_adv_chal_x h_ow_adv_chal_x_queried_gh q Win h_Win_RO_inv σ
    _ ≤ ((q + 1) : ENNReal) / Fintype.card output
        + ((q + 1) : ENNReal) / Fintype.card input := by
        gcongr
        · exact ow_game_2_tracked_wins_le_guess_output_bound ow_adv
            h_ow_adv_matched_chal_y h_ow_adv_queries_output h_ow_adv_chal_y q σ
        · -- The "bad ∩ Win" wp is ≤ "bad" wp (since Win ≤ 1).
          calc (ow_game_1_tracked ow_adv q).wp
                  (fun bσ : Bool × state =>
                    if chal_x_queried_gh.get bσ.2 = true then Win bσ else 0) σ
              ≤ (ow_game_1_tracked ow_adv q).wp
                  (fun bσ : Bool × state =>
                    if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ := by
                apply Program.wp_le_wp_of_le
                intro bσ
                by_cases h : chal_x_queried_gh.get bσ.2 = true
                · simp only [if_pos h, Win_def]
                  split_ifs <;> simp
                · simp [h]
            _ ≤ ((q + 1) : ENNReal) / Fintype.card input := by
                exact ow_game_1_tracked_bad_le_guess_input_bound ow_adv
                  h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x
                  h_ow_adv_chal_x_queried_gh h_ow_adv_queries_input
                  h_ow_adv_mass_one h_ow_adv_chal_x_blind q σ
    _ ≤ ((q + 1) : ENNReal) / Fintype.card output
        + ((q + 1) : ENNReal) / Fintype.card output := by
        gcongr
        exact_mod_cast card_input_ge_output
    _ = (2 * (q + 1) : ENNReal) / Fintype.card output := by
        rw [← ENNReal.add_div]; ring_nf

end GameHopParam_Final
