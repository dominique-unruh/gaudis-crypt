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
