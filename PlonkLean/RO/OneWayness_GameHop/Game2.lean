import PlonkLean.RO.OneWayness_GameHop.Definitions
import PlonkLean.RO.OneWayness_GameHop.GuessExperiment
import PlonkLean.RO.OneWayness_GameHop.UpToBad

/-!
# OneWayness GameHop: Game 2 reduction

This module reduces Game 2's win event to the abstract `guess_experiment`
framework, ultimately bounding it by `(q+1)/|output|`.

## Game 2 components

* `body_game_2`, `final_game_2` — direct query / response handlers (with
  explicit `if y_val = y then set matched_chal_y true`).
* `env_game_2` — the prefix that samples `y` and tracks the matched flag.
* `body_recording_game_2`, `final_recording_game_2` — recording variants
  that append each response to `queries_output`.
* `q_body_game_2`, `q_final_game_2` — shared query subprograms;
  `body_game_2 = q_body_game_2 >>= match_check_y` and
  `body_recording_game_2 = q_body_game_2 >>= record_to_qs`. This decomposition
  fits the schema directly (no bridges needed).
* `guess_experiment_game_2` — Game 2 as a `guess_experiment` instance.

## Bridges and bound

* `ow_game_2_tracked_wins_le_guess_experiment_game_2_matched` — Game 2's
  win event ≤ guess_experiment_game_2 matched event.
* `ow_game_2_tracked_bad_eq_guess_experiment_game_1` — Game 2's BAD event
  equals guess_experiment_game_1's matched event (used in `UpToBad`).
* `ow_game_2_tracked_wins_le_guess_output_bound` — full bound:
  `Pr[Game 2 wins] ≤ (q+1)/|output|`, by chaining the above into
  `guess_experiment_le_interim_via_schema` and `guess_experiment_interim_wp_bound`.

## Length-bound helpers

`Program.wp_qs_length_preserved_of_inRange`, `loop_n_wp_linear_bound`,
`body_recording_game_2_qs_length_bump`, etc. — used to discharge
`h_qs_length_le` (the `|queries| ≤ q+1` hypothesis of
`guess_experiment_interim_wp_bound`).
-/
