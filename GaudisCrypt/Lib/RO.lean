import GaudisCrypt.Lib.RO.Basic
import GaudisCrypt.Lib.RO.TransferConvert
import GaudisCrypt.Lib.RO.OracleLoop
import GaudisCrypt.Lib.RO.ROEquiv

open GaudisCrypt
open GaudisCrypt

/-!
# Random oracle framework

This file is a barrel re-exporting the framework. The actual definitions
and lemmas live in `PlonkLean/RO/`:

* `PlonkLean.RO.Basic` — RO primitives only: `random_oracle_state` axiom,
  `lazy_init` / `random_oracle_init`, `lazy_query` / `random_oracle_query`,
  and `lazy_query_inFootprint_ro`. No bridging between lazy and eager. (The legacy
  `inRange` duals live in `PlonkLean.RO.LegacyRange`, kept only for `QueryHit`.)

* `PlonkLean.RO.TransferConvert` — the lazy/eager bridge: `convert` itself,
  convert algebra (`convert_wp_eq`, `convert_mass`,
  `convert_commutes_set/get`, `convert_random_oracle_init`,
  `convert_bind_random_oracle_init_bind`), the foundational lazy/eager
  equations (`lazy_init_convert_eq_random_oracle_init`,
  `lazy_query_convert_eq_convert_random_oracle_query`, `if_factor_convert`),
  the `ProgramDenotation.transfer` relation (= `transferBy convert`, closure
  laws inherited from `GaudisCrypt.Logic.TransferBy`), and the wp/marginal
  bridges (`ProgramDenotation.transfer_value_marginal` and the RO-invariant
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
  `ProgramDenotation.transfer_oracle_loop` (full transfer of the while-loop game,
  built via the framework's `transfer_while_loop` closure law),
  `oracle_loop_lazy_convert_eq_random_oracle_loop` (the foundational
  equation), and the corollary family `oracle_loop_wp_lazy_eq_random_oracle`
  / `oracle_loop_marginal_lazy_eq_random_oracle` / `..._compl` / `..._glob`.
-/
