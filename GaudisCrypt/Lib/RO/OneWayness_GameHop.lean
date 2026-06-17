import GaudisCrypt.Lib.RO
import GaudisCrypt.Lib.RO.OneWayness
import GaudisCrypt.EquivModuloLens
import GaudisCrypt.Lib.RO.OneWayness_GameHop.Definitions
import GaudisCrypt.Lib.RO.OneWayness_GameHop.GuessExperiment
import GaudisCrypt.Lib.RO.OneWayness_GameHop.UpToBad
import GaudisCrypt.Lib.RO.OneWayness_GameHop.Game1
import GaudisCrypt.Lib.RO.OneWayness_GameHop.Game2

open GaudisCrypt.Language.Semantics

/-!
# One-wayness via game hopping

A proof from first principles that for any adversary against a random oracle
making at most `q` queries:

```
  P[OW experiment wins]  ≤  2 (q + 1) / |output|
```

## Proof structure

```
                                       ow_game_0_eq_ow_game_1
  ow_experiment  ==  ow_game_0  ==========================>  ow_game_1
                                  (program equality)              ║
                                                                  ║ flag-elision
                                                                  ║ (tracking
                                                                  ║  invisible
                                                                  ║  at flag-
                                                                  ║  ignoring
                                                                  ║  posts)
                                                                  ║
                                                                  ▼
                                                          ow_game_1_tracked
                                                                  ║
                                                                  ║ up-to-bad
                                                                  ║ (Game 1 ─ Game 2
                                                                  ║   identical
                                                                  ║   until adv
                                                                  ║   queries
                                                                  ║   chal_x)
                                                                  ▼
                                                          ow_game_2_tracked
                                                          + bad event
                                            ┌───────────────┴──────────┐
                                            ▼                          ▼
                                     win event in G2              bad event
                                            │                          │
                                            │ Game 2 → guess-          │ Game 1 → guess-
                                            │ experiment_game_2        │ experiment_game_1
                                            │ (matched_chal_y)         │ (chal_x_queried_gh)
                                            ▼                          ▼
                                  ≤ (q+1)/|output|              ≤ (q+1)/|input|
                                                                       │
                                                                       │ |input| ≥ |output|
                                                                       ▼
                                                                ≤ (q+1)/|output|
                                            └──────────────┬───────────┘
                                                           ▼
                                                ≤ 2(q+1)/|output|
```

## Module layout

* `Definitions` — the three games (`ow_game_0`, `ow_game_1`, `ow_game_2`),
  their tracked variants, the tracking flag `chal_x_queried_gh`, the
  matched flag `matched_chal_y`, the query-recording lists
  `queries_input`/`queries_output`, all disjointness axioms.
* `GuessExperiment` — the abstract guessing-game framework
  (`guess_experiment`, `guess_experiment_interim`, `schema_inner_equation`,
  `guess_experiment_le_interim_via_schema`, `guess_experiment_interim_wp_bound`).
  Reduces both Game 2 wins and Game 1 bad to a single bound `≤ (q+1)/|T|`.
* `UpToBad` — the identical-until-bad analysis bridging Game 1 to Game 2.
  Contains RO-invariance machinery, mass-conservation lemmas, and the
  `up_to_bad`-style decomposition.
* `Game1` — Game 1 specifics: bridges Game 1 to Game 1' (a schema-friendly
  variant with explicit `if inp = t then set chal_x_queried_gh true`),
  `game_1_correspondence`, and the bad-event bound.
* `Game2` — Game 2 specifics: schema decomposition (`q_body_game_2`,
  `q_final_game_2`), win-event bound.

## The master theorem

`ow_lazy_bound_via_gamehop` (this file) chains everything together. -/

section GameHopParam_Final

variable (ow_adv : Program state Unit)

/-- **The OW lazy bound via the game-hop chain**.
    Matches the existing `ow_lazy_bound` (in `QueryHit.lean`), proved via
    the game-hopping + up-to-bad chain. -/
theorem ow_lazy_bound_via_gamehop
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_ow_adv_matched_chal_y : ow_adv.inRange matched_chal_y.compl.range)
    (h_ow_adv_queries_output : ow_adv.inRange queries_output.compl.range)
    (h_ow_adv_queries_input : ow_adv.inRange queries_input.compl.range)
    (h_ow_adv_mass_one : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1)
    (q : ℕ) (σ : state) :
    (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ (2 * (q + 1) : ENNReal) / Fintype.card output := by
  -- Win indicator is flag-ignoring (depends only on `bσ.1`) and RO-invariant.
  set Win : Bool × state → ENNReal := fun bσ => if bσ.1 then (1 : ENNReal) else 0 with Win_def
  have h_Win_flag : IgnoresLens chal_x_queried_gh Win := by
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
          h_ow_adv h_ow_adv_chal_x h_ow_adv_chal_x_queried_gh
          h_ow_adv_mass_one q Win h_Win_RO_inv σ
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
                  h_ow_adv_mass_one q σ
    _ ≤ ((q + 1) : ENNReal) / Fintype.card output
        + ((q + 1) : ENNReal) / Fintype.card output := by
        gcongr
        exact_mod_cast card_input_ge_output
    _ = (2 * (q + 1) : ENNReal) / Fintype.card output := by
        rw [← ENNReal.add_div]; ring_nf

end GameHopParam_Final
