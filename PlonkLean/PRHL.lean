import PlonkLean.PRHL.Core
import PlonkLean.PRHL.Lenses
import PlonkLean.PRHL.Loops
import PlonkLean.PRHL.UpToBad
import PlonkLean.PRHL.Coupling

/-!
# pRHL: a probabilistic relational Hoare logic for `Program`

A relational layer over the unary wp calculus, in the EasyCrypt/CertiCrypt
tradition but with a wp-based (coupling-free) semantics:

```
Program.rel  p q Pre Post  :=
  ∀ F G, (∀ x y, Post x y → F x ≤ G y) →
    ∀ σ₁ σ₂, Pre σ₁ σ₂ → p.wp F σ₁ ≤ q.wp G σ₂
Program.relE p q Pre Post  :=  rel in both directions
```

All rules are derived as lemmas from the unary wp lemma base (CertiCrypt's
"semantic setting" methodology): if the rule set is insufficient, fall back
to `wp` reasoning or `Program.ext_of_wp`.

## Module layout

* `Core` — the judgments, Pr-bridges (`rel.wp_le`, `relE.wp_eq`), structural
  rules (`conseq`, `refl`, `trans`, `bind`, `prefix_left/right`,
  `ite_sync`), assignment rules (`set_set`, `get_get`, one-sided variants),
  sampling rules (`uniform_bij`, `sample_left/right`).
* `Lenses` — footprint-aware rules: `self_shift` (relational
  `wp_shift_input`), `frame` (relational `wp_strengthen_lens_preserved`),
  and the two-way bridge with the `EquivModuloLens` calculus.
* `Loops` — synchronized invariant rule for `loop_n`.
* `UpToBad` — the Fundamental Lemma (`relE.up_to_bad`, `relE.bad_eq`) and
  the rectangular rule `rel.of_unary` (for phases where the two sides
  genuinely diverge).

## Roadmap

1. ✅ Core judgment + rule set (this library).
2. ✅ Validation client 1: `schema_inner_equation` re-proved relationally in
   `Clients/SchemaInnerEquation.lean` — 280 lines (incl. docs) vs the
   ~980-line unary block, no `maxHeartbeats` bump (original: 1600000), and
   strictly more general (generic state type, no `Fintype`/`Nonempty` on
   `T`, 2 of 3 disjointness assumptions). Drop-in compatibility certified
   in `Clients/SchemaInnerEquationCheck.lean`.
3. ✅ Validation client 2: the UpToBad core re-derived in
   `Clients/UpToBadPRHL.lean` — one judgment (`ow_game_tracked_relE`, the
   textbook coupling invariant `InvUB`) yields all three theorems
   (`until_bad`, `bad_eq`, the hop bound) as corollaries. Honest verdict:
   ~line parity with the unary original (832 vs 891) — `relE` pays a
   two-direction mirror tax and the rectangular phase keeps the unary
   flag/mass side conditions — but the architecture is one invariant + 3
   corollaries instead of ~15 interdependent inductions, `bad_eq` comes
   free (unary: 138-line mass/cancellation chain), and the judgment is
   post-generic. Extra hypothesis: adversary mass-1 (see module docstring).
4. ✅ Migration: `schema_inner_equation`'s proof is now the relational
   client; its 280-line unary proof, `maxHeartbeats 1600000`, and ~700-line
   private support block are deleted (GuessExperiment.lean: 1407 → 483).
5. Parallel track: `glob`/`Program.range` synthesis automation to discharge
   `inRange` side conditions (gates roughly a third of the compression).
6. ✅ Symmetric-`relE` principle: `Coupling.lean` — an explicit coupling
   witness yields both `relE` directions at once (`relE.of_coupling`, with
   `Coupling.of_pure`/`of_uniform` builders). Couplings are used at leaves
   only; composition stays with the wp-lifting rules. `lqt_relE` in the
   up-to-bad client now does its case analysis once.
7. Remaining tactic-layer candidates: do-notation-aware `rel_step`,
   synchronized `while_loop` rule (Kleene argument).

## Known landmines (do not "fix")

* No conjunction rule for posts (see `Core` header).
* `rel.sample_right` works because `uniform` has mass 1; a general
  sample-introduction rule for sub-mass-1 distributions is unsound.
-/
