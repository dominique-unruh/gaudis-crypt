import Mathlib.Tactic.Basic

/-!
# EC's lossless distributions, as a simp set

    @[ec_lossless] theorem bdistr_expected_one : bdistr.expected (fun _ => 1) = 1

EasyCrypt's `auto` takes a sampling `x <$ d` of a lossless distribution (`is_lossless d`,
`dunifin_ll`, …) as one that happens: what `rnd` leaves of it, the mass `mu d predT`, is `1`.
Ours is the expectation `d.expected (fun _ => 1)`; the facts `d.expected (fun _ => 1) = 1` of the
distributions a development uses are tagged `@[ec_lossless]`, and the `auto` tactics
(`equiv_auto`, `phoare_auto`, the strict `ec_auto`) and the closers' `ec_prep` simplify with them.
-/

/-- EC's lossless distributions: `d.expected (fun _ => 1) = 1`, used by the `auto` tactics. -/
register_simp_attr ec_lossless
