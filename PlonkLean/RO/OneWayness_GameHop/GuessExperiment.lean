import PlonkLean.RO.OneWayness_GameHop.Definitions

/-!
# OneWayness GameHop: Guess Experiment Framework

This module provides the **abstract guessing-game machinery** that abstracts
both the win and bad events in the OW chain. Used by both Game 1's bad-event
reduction and Game 2's win-event reduction.

## Core combinators

* `loop_n n body` — iterate `body` exactly `n` times.
* `guess_experiment env sample tvar mvar body final n` — the abstract guessing
  experiment. Adversary makes `n` queries, then a `final` query; we count
  whether the matched flag fires.
* `guess_experiment_interim` — the same experiment but with a recording list
  collecting all adv queries (sampling happens FIRST).
* `guess_experiment_collector` — equivalent recording form with sampling
  commuted past the recording loop.

## Bounds

* `guess_experiment_collector_wp_bound : (collector).wp post σ ≤ (n+1)/|T|`
  — the heart of the bound, via `uniform_wp_mem_le`.
* `guess_experiment_interim_eq_collector` — interim = collector by
  `Program.bind_uniform_comm` applied 3 times.
* `guess_experiment_interim_wp_bound` — composed bound: interim ≤ (n+1)/|T|.

## Schema (per-game correspondence)

* `guess_experiment_le_interim_assumption` — given a per-σ', t correspondence
  (`h_correspondence`), bounds guess_experiment by guess_experiment_interim.
* `schema_inner_equation` — the per-σ', t equation, proven structurally for any
  body decomposed as `q >>= match_check` and `body_recording` as `q >>= record`.
* `guess_experiment_le_interim_via_schema` — combines the above two: applies
  to any game whose body fits the schema's `q >>= ...` form.

Game 2's body fits directly. Game 1's needs the bridges in `Game1.lean` to
convert to Game 1' form.
-/
