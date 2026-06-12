import GaudisCrypt.RO.Basic
import GaudisCrypt.RO.Transfer
import GaudisCrypt.RO.OracleLoop
import GaudisCrypt.RO.ROEquiv

/-!
# Random oracle framework

This file is a barrel re-exporting the framework. The actual definitions
and lemmas live in `PlonkLean/RO/`:

* `PlonkLean.RO.Basic` — RO primitives only: `random_oracle_state` axiom,
  `lazy_init` / `random_oracle_init`, `lazy_query` / `random_oracle_query`,
  and `lazy_query_inRange_ro`. No bridging between lazy and eager.

* `PlonkLean.RO.Transfer` — the lazy/eager bridge: `convert` itself,
  convert algebra (`convert_wp_eq`, `convert_mass`, `convert_wp_const`,
  `convert_commutes_set/get`, `convert_random_oracle_init`,
  `convert_bind_random_oracle_init_bind`), the foundational lazy/eager
  equations (`lazy_init_convert_eq_random_oracle_init`,
  `lazy_query_convert_eq_convert_random_oracle_query`,
  `lazy_query_conv_eq_conv_random_oracle`, `if_factor_convert`), the
  `Program.transfer` relation with its closure laws (including
  `Program.transfer_while_loop`), and the wp/marginal bridges
  (`Program.transfer_wp_value`, `_marginal`, and the RO-invariant
  enrichments).

* `PlonkLean.RO.OracleLoop` — scratch state for adversary-driven loops
  (`want_more`, `oracle_input`, `oracle_output`, `adversary_result`,
  `skip`, disjointness instances), the `lazy_query + set oracle_output`
  key-reasoning lemmas (`query_set_convert_eq`,
  `lazy_query_then_set_oracle_output_inRange_compl`,
  `lazy_query_set_oracle_output_preserves_RO_at_other_key`,
  `RO_setentry_neq_commutes_lazy_query_set_oracle_output`), the three
  oracle loop variants (`oracle_step`, `oracle_loop_n`, `oracle_loop`),
  and their transfer/`inRange`/indicator-step lemmas.

* `PlonkLean.RO.ROEquiv` — the lazy = eager equivalence for `oracle_loop`:
  `adv_conv_eq_conv_adv` (`convert` commutes with RO-disjoint adversaries),
  `Program.transfer_oracle_loop` (full transfer of the while-loop game,
  built via the framework's `transfer_while_loop` closure law),
  `oracle_loop_lazy_convert_eq_random_oracle_loop` (the foundational
  equation), and the corollary family `oracle_loop_wp_lazy_eq_random_oracle`
  / `oracle_loop_marginal_lazy_eq_random_oracle` / `..._compl` / `..._glob`.
-/
