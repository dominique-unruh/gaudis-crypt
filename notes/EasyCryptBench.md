# EasyCrypt `phoare` test bench

Small, self-contained `phoare` proofs from the EasyCrypt distribution, to replicate with our
`phoare` tactics (`Logic/PHoare.lean`, `Logic/PHoareWp.lean`) and compare.  Sources:
`~/.opam/ec/.opam-switch/sources/easycrypt` (EasyCrypt r2026.06, opam switch `ec`).

Replications go to `GaudisCrypt/Examples/EasyCryptBench/`, one file per EC source; each file's
header quotes the EC proof for side-by-side comparison.

| # | EC source | Statement | What it exercises | Status |
|---|---|---|---|---|
| 1 | `examples/vonNeumann.eca` — `Simulate_is_Fair` | fair coin from a biased coin of unknown bias `p`: `while (b = b') { b <$ dbiased; b' <$ dbiased }; return b` has `Pr[res = x] = 1/2` | loop lower bound + termination; EC needs the variant rule `while true (b2i (b = b')) 1 (2p(1−p))` and nested five-probability `seq`s; here one fixed-point invariant `if b = b' then 1/2 else [b = x]`, `ε = 2p(1−p)` | **done** — `Examples/EasyCryptBench/VonNeumann.lean` |
| 2 | `examples/Dice4_6.ec` — `prD6` | a d4 from a d6: `while (5 <= r) r <$ [1..6]` has `Pr[res = k] = 1/4` | rejection sampling on an integer interval; EC goes through `byequiv` and `WhileSamplingFixedTest`, here directly | **done** — `Examples/EasyCryptBench/Dice4_6.lean` |
| 3 | `theories/modules/PlugAndPray.eca` — `PBound` | abstract game, then a uniform guess: `(1/|I|) · Pr[G : φ] = Pr[Guess(G) : φ ∧ i = ψ]` | abstract call + linearity; EC: `seq` with probabilities, `call`, nested `byequiv` ("FIXME: more verbose than it should be") | **done** — `Examples/EasyCryptBench/PlugAndPray.lean` |
| 4 | `theories/encryption/Means.ec` — `prCond`, `Mean` | abstract worker on a sampled input: `Pr[ev] = Σ_v μ(v) · Pr[A.work(v) : ev v]` | exactly the symbolic exact wp of `phoare_wp` | **done** — `Examples/EasyCryptBench/Means.lean` |
| 5 | `theories/distributions/Dexcepted.ec` — `WhileSampling` | rejection sampling with an arbitrary distribution and test = the `dexcepted` distribution | generalizes `Examples/RejectionSampling.lean` beyond uniform | **done** — `Examples/EasyCryptBench/WhileSampling.lean` |

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

## Round 2: `equiv` + `phoare` candidates (2026-10-24)

Small EC examples (`~/.opam/ec/.opam-switch/sources/easycrypt/examples`) mixing `equiv` and
`phoare`, with what each needs beyond what we have:

1. **`Pedersen.ec`** (175 lines) — we have correctness and hiding (`Examples/Pedersen/`), but our
   `phi_hi` goes through the old `prhl2` layer and depends on a `sorry` (`hidingGame_self_glob`,
   the `={glob U}` adversary rule at the denotation level).  With `equiv[ ]` the precondition
   `={allGlobals}` and `prhlProc_refl` for the adversary calls suffice for the `Pr` equality at
   one memory — no footprint needed.  Also `pedersen_computational_binding` (an `equiv` reduction
   to discrete log: `call (_ : true)`, then algebra) and `std_red_dl_bridge` (`if{2}`, `seq`).
2. **`elgamal.ec`** (134) — IND-CPA from DDH: `cpa_ddh0` (`equiv`, `swap`, `call (_:true)`),
   `ddh1_gb` (`rnd` along `z ↦ z + log m_b`, state-dependent), `Gb_half` (`byphoare`,
   `rnd (pred1 b')`, lossless adversary), `conclusion`.  Needs **`swap`** (a sampling moved across
   an adversary call) — a statement rewrite, so it would be judgment-generic (`stmt_swap`).
3. **`hashed_elgamal_std.ec`** (199) — the same shape with entropy smoothing; after ElGamal.
4. **`SchnorrPK.ec`** (173) — completeness (`phoare = 1`), special soundness (`phoare = 1`,
   deterministic), SHVZK (`equiv`, `rnd` along `z ↦ z - w·e`, `swap`s, `rcondf`).  Needs the
   `SigmaProtocol` games and `swap`.
5. **`RWhileSampling.ec`** (75) — `equiv[ sample ~ idle ]` for a rejection loop: a loop on **one
   side only** (`while{1}`), terminating by the `phoare` loop rule.  Needs a one-sided loop rule.
6. **`global-hybrid/GlobalHybridExamp1.ec`** (207) — hybrid argument with up-to-bad `byequiv`
   (`: bad`), `phoare` with `seq` probabilities, `while true (m - i)`.  Needs the up-to-bad
   `byequiv` form and the hybrid lemma.
7. `async-while.ec` (73, EC's `async while`), `Upto.ec` (145, `fel` + up-to-bad call rule):
   specialised rules, later.

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
* 2026-10-23 — **WhileSampling done** (`pr_sampleW`: `Pr[SampleW : P res] = μ(P ∧ ¬X)/μ(¬X)`,
  EC's `mu (d \ X) P`, for any lossless `d` on any type).  One general fact, `draw_inv` (one draw
  keeps `if X r then c else [P r]`, `c = μ(P ∧ ¬X)/μ(¬X)`), closes both loop bounds; the
  degenerate `μ(¬X) = 0` (the loop never exits) needs no split in the upper bound (`c = 0/0 = 0`)
  and a one-line one in the lower bound.  EC: ~80 lines across `pr_sampleW` and `pr_sampleWi`
  (variant rule, `phoare split`, nested `seq`s, two case splits).
* 2026-10-23 — **Dice4_6 done** (`prD6`, EC's statement), as an *instance* of `WhileSampling`
  (`t = ℤ`, `d` uniform on `[1..6]`, test `5 ≤ r`): the loop is `draw_inv` at the instance; the
  rest is the concrete `μ(r = k ∧ r < 5)/μ(r < 5) = (1/6)/(4/6) = 1/4`.  EC instead goes through
  an `equiv` with a direct d4 and the `WhileSamplingFixedTest` clone.  Library fix on the way:
  `uniformOfFinset_expected` (`WeakestPreconditions.lean`) required `[Fintype a]` of the whole
  ambient type — sampling from a finite subset of `ℤ` was impossible to reason about; now proved
  via `lintegral_eq_tsum_smul` with no finiteness assumption (the now-unused instances dropped
  from `wp_uniformOfFinset`, `uniformOfFinset_mass_one` and the Attic's
  `inRange_uniformOfFinset`).
* 2026-10-23 — **PIR privacy done** (`secure1`, `secure2`, `security_s`, `security_s'` in
  `Examples/EasyCryptBench/PIR.lean`, standard axioms), with the new pRHL layer (branch
  `prhl-syntax`).  `secure1` is EC's script step for step: `equiv_proc; stmt_inline 0` ×3
  (`proc; inline *`), `stmt_wp`, `equiv_while ={j, s}`, body `stmt_wp; equiv_rnd; equiv_skip`
  and a 2-line `simp`.  `secure2` couples the coins with one *state-dependent* function,
  `fun b => if (§j{1} == §i0{1}) = (§j{2} == §i0{2}) then b else !b`, where EC does a `case`
  and two `rnd`s.  The `byequiv` corollaries are one term each (`Procedure.Pr_eq_of_prhlProc`).
  The database is any additive group (EC: words with xor); `s`, `s'` are `List ℕ` as in EC.
  Later the same night: **`PIR_correct`** (`correct`/`pir_correct`, `Pr[res = a i] = 1`) with a
  new loop rule for lower bounds with a *variant* (`phoare_while_ge I variant N - §j`;
  `Stmt.ewp_while_ge_variant`, well-founded induction on the variant, no losslessness or exit
  probability needed) and EC's invariant as an indicator — the database needs characteristic 2
  (`char_two`); and **`PIR_s_uniform`** (`s_uniform`, relational, the xor coupling
  `b ^^ (decide (j ∈ x₁) ^^ decide (j ∈ x₂))`, queries as `Finset`s via `List.toFinset`, one step
  lemma `toFinset_step`); `PIR_s'_uniform` (`s'_uniform`, the same coupling — the second query
  takes `j` iff `b ^^ (j == i)`, and both runs have the same `i`); **`Pr_PIR_s`** (`pr_s`,
  `Pr_PIR_s`: `Pr[set s = x] = if x ⊆ [0, N) then 2^-N else 0`) with one exact per-round equation
  (`core_step`: the chance from round `j` is the average of the two chances from `j + 1`) serving
  both `phoare_while_le` and `phoare_while_ge … variant N - §j` (the invariants differ only off
  the reachable states), against EC's ~50 lines of `seq` with five probabilities, `conseq` and
  `smt`; and `PIR_secuity_s_bypr` (`security_s_bypr`); the mirrors `Pr_PIR_s'`,
  `PIR_secuity_s'_bypr` (at the index the two coin values swap roles: `add_comm`).  **Every
  lemma of `PIR.ec` is now replicated**, standard axioms.
* 2026-10-24 — **Pedersen with `equiv[ ]`** (round 2, candidate 1): every lemma of EC's
  `Pedersen.ec` now has a standard-axioms proof.  `Examples/Pedersen/HidingPRHL.lean`:
  `phi_hi_prhl` (EC's `phi_hi` script: inline, `equiv_call prhlProc_refl _` for the adversary,
  `equiv_rnd (fun d => d + §x0{1} * §m{1})`, algebra — 20 lines, against ~300 for the earlier
  `prhl2` route), `phi_hi'`, `pedersen_perfect_hiding'` (the existing `pedersen_perfect_hiding`
  depends on the `sorry` in `hidingGame_self_glob`).  `Examples/Pedersen/Binding.lean`: EC's
  `DLogAttacker`, `DLogExperiment`, `DLogStdExperiment`, `StdRedAdversary`; `binding_prhl` /
  `pedersen_computational_binding` (an inverse on exponents and injective `g^·` as hypotheses —
  `PedersenGroup` has neither), `std_red_prhl` / `std_red_dl_bridge` (`equiv_seq 0 1`, then
  `equiv_if{2}` with a one-sided sampling — EC's `seq 2 3; if{2}`), and
  `pedersen_std_computational_binding`.  Tool fix on the way: `equiv_rnd` refused nothing, and
  an assignment (a point-mass sampling) unified with it; it now insists on samplings.
* 2026-10-24 — **ElGamal done** (round 2, candidate 2; `Examples/EasyCryptBench/ElGamal.lean`,
  standard axioms): `cpa_ddh0`, `ddh1_gb`, `gb_half`, `conclusion`
  (`|Pr[CPA] − 1/2| = |Pr[DDH0] − Pr[DDH1]|` over the reals, any lossless adversary).  New,
  judgment-generic: **`stmt_swap{i} n k`** (EC's `swap`; `Logic/StmtSwap.lean`) — adjacent
  swaps justified by `Stmt.swap_det` (a deterministic statement and one commuting with its
  update) or `Stmt.swap_sample` (a sampling from a constant distribution and one commuting with
  writes to its variable, by Fubini); commutation `Stmt.CommutesWith` built syntax-directed
  (assignments, samplings, calls, `if`, sequences), side conditions — state equations — by
  `simp` with the read-through-write set plus `Lens.set_outward X` (writes to the moved
  variable pushed outward) and `resetSetter_set_varLens`.  **`stmt_split_pair{i} n`** splits a
  tuple assignment (the inliner assigns a call's parameters as one tuple; EC inlines one
  assignment per parameter, which its `swap`s rely on).  The ElGamal scripts are EC's, swap for
  swap (in `cpa_ddh0` the right side moves instead of the left).  `gb_half` needs no
  `rnd (pred1 b')`.  Pitfalls met: a lemma about `(varLens v).intoLocal` does not fire on a
  `VariableName.mk …` literal (implicit `v.type` not unifiable before `v`) — state it with the
  constructor's fields; l-values are `liftLens X`, not `Lens.toSetter X`.
* 2026-10-24 — **Hashed ElGamal done** (round 2, candidate 3;
  `Examples/EasyCryptBench/HashedElGamal.lean`, standard axioms): `cpa_ddh0`, `ddh1_es1`,
  `es0_gb` (coupling `w ↦ w + m_b`), `gb_half`, `conclusion` (`≤` DDH + ES advantages).  No new
  machinery: each relational proof went through on the first attempt once the swaps were
  planned.  The one new obstacle: the inliner's `reset_vars` of a callee's locals blocks moving
  a sampling of a same-named variable past it (EC's inliner has no resets) — moved out of the
  way first (`stmt_swap{1} 4 -3` in `ddh1_es1`).  Statement positions are still counted by hand.
