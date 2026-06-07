import PlonkLean.RO.Basic
import PlonkLean.RO.Wrapper
import PlonkLean.RO.Transfer
import PlonkLean.RO.OracleLoop

/-!
# Random oracle framework

This file is a barrel re-exporting the framework. The actual definitions
and lemmas live in `PlonkLean/RO/`:

* `PlonkLean.RO.Basic` — RO axioms and primitives (`lazy_query`,
  `random_oracle_query`, `lazy_init`, `random_oracle_init`, `convert`),
  the `oracle_input`/`oracle_output`/`adversary_result`/`want_more`
  scratch variables, and `lazy_init_convert_eq_random_oracle_init` / `lazy_query_convert_eq_convert_random_oracle_query` / `lazy_query_conv_eq_conv_random_oracle`.

* `PlonkLean.RO.Wrapper` — adversary-parameterised wrapper layer:
  `oracle_loop` (while-loop with `want_more`), `adv_conv_eq_conv_adv` (`convert`
  commutes with adversaries), `oracle_loop_lazy_convert_eq_random_oracle_loop` (Kleene-style transfer of
  `oracle_loop`), and `oracle_loop_wp_lazy_eq_random_oracle` / `oracle_loop_marginal_lazy_eq_random_oracle` / `oracle_loop_marginal_lazy_eq_random_oracle_compl` /
  `oracle_loop_marginal_lazy_eq_random_oracle_glob`.

* `PlonkLean.RO.Transfer` — generic lazy/eager transfer relation
  `Program.transfer`, its closure lemmas, the bridge to wp/marginal
  statements, and convenience shortcuts (`transfer_set/get_of_disjoint_ro`,
  `transfer_uniform`, `convert_bind_random_oracle_init_bind`).

* `PlonkLean.RO.OracleLoop` — generic adversary + oracle loop primitives
  (`oracle_step`, `oracle_loop_n`), their transfer/`inRange` lemmas,
  the `lazy_query` + `set oracle_output` key-reasoning lemmas, and the
  generic indicator-step lemmas (`lazy_query_wp_step`,
  `oracle_step_wp_indicator_bump`, `oracle_loop_n_wp_linear_bound`).
-/
