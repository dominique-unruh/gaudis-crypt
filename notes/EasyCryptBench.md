# EasyCrypt `phoare` test bench

Small, self-contained `phoare` proofs from the EasyCrypt distribution, to replicate with our
`phoare` tactics (`Logic/PHoare.lean`, `Logic/PHoareWp.lean`) and compare.  Sources:
`~/.opam/ec/.opam-switch/sources/easycrypt` (EasyCrypt r2026.06, opam switch `ec`).

Replications go to `GaudisCrypt/Examples/EasyCryptBench/`, one file per EC source; each file's
header quotes the EC proof for side-by-side comparison.

| # | EC source | Statement | What it exercises | Status |
|---|---|---|---|---|
| 1 | `examples/vonNeumann.eca` — `Simulate_is_Fair` | fair coin from a biased coin of unknown bias `p`: `while (b = b') { b <$ dbiased; b' <$ dbiased }; return b` has `Pr[res = x] = 1/2` | loop lower bound + termination; EC needs the variant rule `while true (b2i (b = b')) 1 (2p(1−p))` and nested five-probability `seq`s; here one fixed-point invariant `if b = b' then 1/2 else [b = x]`, `ε = 2p(1−p)` | **done** — `Examples/EasyCryptBench/VonNeumann.lean` |
| 2 | `examples/Dice4_6.ec` — `prD6` | a d4 from a d6: `while (5 <= r) r <$ [1..6]` has `Pr[res = k] = 1/4` | rejection sampling on an integer interval; EC goes through `byequiv` and `WhileSamplingFixedTest`, here directly | |
| 3 | `theories/modules/PlugAndPray.eca` — `PBound` | abstract game, then a uniform guess: `(1/|I|) · Pr[G : φ] = Pr[Guess(G) : φ ∧ i = ψ]` | abstract call + linearity; EC: `seq` with probabilities, `call`, nested `byequiv` ("FIXME: more verbose than it should be") | **done** — `Examples/EasyCryptBench/PlugAndPray.lean` |
| 4 | `theories/encryption/Means.ec` — `prCond`, `Mean` | abstract worker on a sampled input: `Pr[ev] = Σ_v μ(v) · Pr[A.work(v) : ev v]` | exactly the symbolic exact wp of `phoare_wp` | **done** — `Examples/EasyCryptBench/Means.lean` |
| 5 | `theories/distributions/Dexcepted.ec` — `WhileSampling` | rejection sampling with an arbitrary distribution and test = the `dexcepted` distribution | generalizes `Examples/RejectionSampling.lean` beyond uniform | |

Deferred: `examples/PIR.ec` (two-server private information retrieval) — **postponed until we
have pRHL syntax and tactics**: its privacy proofs `PIR_secure1/2` are `equiv` judgments
(couplings, flipping the coin where the indices differ).  Its `phoare` parts also need a
**variant rule** for counted loops (`while (j < N)` exits with probability 0 except in the last
round, so `Stmt.ewp_while_one`'s `ε > 0` does not apply; EC uses `while I (N − j)`): correctness
(`PIR_correct`, `Pr[res = a i] = 1`) and the explicit distribution `Pr_PIR_s`
(`Pr[set s = x] = 2^-N`, an expectation invariant `if s = x ∩ [0, j) then 2^-(N−j) else 0`).
Model `s`, `s'` as `Finset ℕ` to avoid EC's list↔fset bookkeeping.  Not candidates: the large
crypto developments (`cramer_shoup`, `ChaChaPoly`, KEM theories) — too much library.

Note: no `Language/` change is needed for non-uniform distributions — `x <$ d` samples from any
`d : SubProbability α`, and `toSubProbability : PMF α → SubProbability α` exists (e.g. a biased
coin is `toSubProbability (PMF.ofFintype …)`; `PMF.bernoulli` is deprecated).

## Log

* 2026-10-22 — **von Neumann done** (`simulate_is_fair`, standard axioms).  The biased coin is a
  local definition (`toSubProbability (PMF.ofFintype …)`) with an expectation lemma; no language
  change.  Proof structure: `simulate_le` (`phoare_while_le`) and `simulate_ge`
  (`phoare_while_ge … using 2p(1−p)`) with the *same* invariant, both bodies closed by one
  lemma `round_eq` (one round keeps the invariant: `p²/2 + pq + q²/2 = (p+q)²/2 = 1/2`); then
  `byphoare` against `Fair`.  The probabilistic structure is ~25 tactic lines plus ~20 lines
  of `ENNReal` arithmetic (`round_eq`, `ε ≤ 1`), against EC's ~35 dense lines (variant rule,
  three nested `seq`s with five probabilities each, `smt`).  Friction: `ENNReal` arithmetic
  wants controlled `simp only` (a plain `simp` rewrites `1/2` to `2⁻¹` and rescales);
  `PMF.bernoulli` is deprecated, `PMF.ofFintype` used instead.
* 2026-10-22 — **Plug-and-pray done** (`pbound`, EC's statement).  EC's `glob G` is the final
  globals (our posts read them); the index list is a finite type.  The bound
  `(1/|I|) · Pr[G.main(x) : φ]` depends on the initial state, which our judgment allows directly
  (`phoareProc … Eq (fun x σ => G.ewp x [φ] σ / |I|)`), so no `seq`/`call`/`bypr`/`byequiv`:
  inline, `phoare_wp 5`, `phoare_skip`, then a 6-line pointwise fact (the uniform guess hits `ψ`
  with probability `1/|I|`) and one `rw` (linearity).  Tactic gap found and fixed:
  `phoare_inline` now also simplifies the conditions and the bound with the expectation simp set
  — the inliner's own cleaning did not push `.globals` through its renaming lenses, so a bound
  reading the initial globals was left behind `((rename …).chain trafo).get σ`.
* 2026-10-22 — **Means done** (`prCond`, `mean`, EC's statements, for an arbitrary input
  distribution `d` on a finite type).  `Mean` is literally what `phoare_wp` computes: after
  `phoare_skip` the goal is `d.expected (fun a => A.work.ewp a …) = Σ_x μ{x} · …`, closed by
  `SubProbability.expected_eq_sum` (new, `Logic/PHoare.lean`) — one line, against EC's `byequiv`
  (`introOrs`) and an induction over the support with `prCond` and `Pr[mu_disjoint]`.
  `prCond` adds `Finset.sum_eq_single` (linearity had already pulled `[v = a]` out of the
  worker's expectation).
* 2026-10-22 — **`§allGlobals`**: the whole global state as a value in conditions and bounds
  (EC's `glob A`, and `&m` in a bound), so `pbound_phoare`, `mean_phoare` and `prCond_phoare`
  are now stated in the `phoare[ … ]` syntax rather than as raw `phoareProc` terms.  Needed
  `Evaluatable`'s value type to be universe-polymorphic (`VariableAssignment : Type 1`; one-line
  change in `Syntax/ExpressionSyntax.lean`), the getter `allGlobals`, and `allGlobals_get` in
  `simpReads`.  The EC-style `Pr` corollaries now go through `exact` (the notation's elaborated
  conditions are the plain ones up to unfolding).
