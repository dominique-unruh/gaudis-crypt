import PlonkLean.RO.OneWayness_GameHop.Definitions
import PlonkLean.RO.OneWayness_GameHop.GuessExperiment

/-!
# OneWayness GameHop: Up-to-Bad Hop (Game 1 → Game 2)

This module contains the **up-to-bad machinery** that bounds the difference
between `ow_game_1_tracked` and `ow_game_2_tracked` by the bad event (the
adversary queried `chal_x`).

The two games differ only in whether the random oracle is *pre-programmed* at
`chal_x` (Game 1 does, Game 2 doesn't). Identical-until-bad means their win
events differ only when adv queries `chal_x` — i.e., when `chal_x_queried_gh`
fires.

## Core lemmas

* `lazy_query_tracked_eq_lazy_query_wp` — at chal_x_qg-ignoring posts,
  `lazy_query_tracked` and `lazy_query` have the same wp.
* `RO_setentry_neq_commutes_lazy_query` — and friends — RO invariance
  under chal_x-update at non-match positions.
* `Program.wp_zero_of_flag_true_in_range` — and friends — at posts that
  vanish when the flag is true, wp is 0 if the flag is already set.
* `ow_game_1_tracked_eq_ow_game_2_tracked_until_bad` — the identical-until-bad
  equality (at flag-non-firing posts).
* `ow_game_1_tracked_bad_eq_ow_game_2_tracked_bad` — bad events agree (via
  mass conservation).
* `ow_game_1_tracked_le_ow_game_2_tracked_plus_bad` — the main hop bound:
  `Pr[Game 1 wins] ≤ Pr[Game 2 wins] + Pr[bad]`.

## Mass conservation infrastructure

A family of `*_mass_one` lemmas (`lazy_query_mass_one`,
`lazy_query_tracked_mass_one`, `oracle_step_lqt_mass_eq_adv_mass`,
`loop_n_mass_one`, etc.) plus `Program.mass_bind` for composing them.
-/
