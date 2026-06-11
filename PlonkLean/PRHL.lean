import PlonkLean.PRHL.Core
import PlonkLean.PRHL.Lenses
import PlonkLean.PRHL.Loops
import PlonkLean.PRHL.UpToBad

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
2. Validation client 1: re-prove `schema_inner_equation`
   (GuessExperiment.lean) as one `relE.loop_n` invariant
   (`matched₁ = (t ∈ qs₂)`). Target: ≤150 lines vs the current ~950-line
   unary block.
3. Validation client 2: re-derive the UpToBad.lean core (Game 1 ~ Game 2
   identical-until-bad) via `relE.up_to_bad`. Target: ≤250 lines vs ~810.
4. Parallel track: `glob`/`Program.range` synthesis automation to discharge
   `inRange` side conditions (gates roughly a third of the compression).
5. On demand only: synchronized `while_loop` rule (Kleene argument),
   do-notation-aware `rel_step` tactic.

## Known landmines (do not "fix")

* No conjunction rule for posts (see `Core` header).
* `rel.sample_right` works because `uniform` has mass 1; a general
  sample-introduction rule for sub-mass-1 distributions is unsound.
-/
