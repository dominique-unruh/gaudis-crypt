import PlonkLean.RO
import PlonkLean.RO.OneWayness
import PlonkLean.EquivModuloLens

/-!
# OneWayness GameHop: Definitions

This module collects the *game definitions* used in the game-hopping proof of
one-wayness for a random-oracle adversary:

* `ow_game_0` — the original OW experiment (eager RO).
* `ow_game_1` — equivalent to Game 0 but with `y` sampled and pre-programmed
  explicitly. Connected to Game 0 by `ow_game_0_eq_ow_game_1` (Hop 0→1).
* `ow_game_1_tracked`, `ow_game_2_tracked` — versions of Game 1 and Game 2
  using `lazy_query_tracked` instead of `lazy_query` so the
  `chal_x_queried_gh` flag tracks whether `chal_x` was ever queried.

Plus the **tracking flags** and **collector variables** with their
disjointness axioms / instances:

* `chal_x_queried_gh : Variable Bool` — tracks whether the adv queried `chal_x`.
* `matched_chal_y    : Variable Bool` — tracks whether `chal_y` was returned.
* `queries_input     : Variable (List input)`  — adversary's query list.
* `queries_output    : Variable (List output)` — RO's response list.

This module also defines `lazy_query_tracked` (the flag-flipping variant of
`lazy_query`) which is shared by Game 1 and Game 2.
-/
