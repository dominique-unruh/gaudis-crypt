# A game-hopping proof of one-wayness, formalized in Lean

This report documents a fully verified, axiom-free Lean proof of the
random-oracle one-wayness bound

$$
\Pr[\textsf{OW}_q^{A} = 1] \;\le\; \frac{2(q+1)}{|\textsf{output}|}
$$

via three game hops and an "up-to-bad" analysis, with both intermediate
probability bounds reduced to a single abstract "guessing game" lemma.

The proof lives in `PlonkLean/RO/OneWayness_GameHop/` (split across 5
modules + a root file containing the master theorem) and is independent
of the older `useful_preimage`/`QueryHit` proof of the same fact.

The report has three parts:

1. **High-level intuition** — what we're proving and why it's true.
2. **The cryptographic proof** — game hops, written for a reader
   comfortable with reduction-style cryptographic proofs.
3. **The formal proof** — how the cryptographic argument was rendered
   in Lean: the framework, the module structure, the key abstractions,
   and the design choices.

---

## Part 1: High-level intuition

### What is one-wayness in the random oracle model?

A *random oracle* is an idealized hash function: a freshly sampled
uniformly random function `H : input → output`, exposed only via a
black-box query interface. An adversary `A` is a probabilistic program
that interacts with the oracle by making at most `q` queries.

The *one-wayness experiment* sets a challenge:

1. Sample a uniformly random `x ← input` and define `y := H(x)`.
2. Reveal `y` (but not `x`) to `A`.
3. `A` runs for at most `q` oracle queries and outputs a guess `resp`.
4. `A` wins iff `H(resp) = y`.

The theorem says: no matter how clever `A` is, its winning probability
is at most `2(q+1)/|output|`.

### Why is this true, informally?

`A` wins iff one of two things happens:

- **Lucky guess.** `A` outputs some `resp` with `H(resp) = y` *without
  ever having queried* `H(resp)`. Since `H(resp)` is uniformly random
  over `output` and `A` has no information about it, this happens with
  probability at most `1/|output|`.
- **Detected query.** `A` actually queries `H` at the right preimage at
  some point during execution. Each of the `q` queries hits the target
  with probability at most `1/|input|` (since `x` was sampled
  uniformly), and there are also the verification queries on `resp`,
  so the total is at most `(q+1)/|input|`.

Adding the two events:

$$
\Pr[A \text{ wins}] \;\le\; \frac{1}{|\textsf{output}|} + \frac{q+1}{|\textsf{input}|}.
$$

Assuming `|input| ≥ |output|` (necessary for the hash function to be
plausibly one-way at all), this is at most `2(q+1)/|output|`.

### Why is the formal version non-trivial?

The informal argument elides several things a proof assistant must make
precise:

- **What does "queried the right preimage" *mean* as a statement about
  the distribution induced by `A`?** The experiment doesn't naturally
  carry that information; we have to instrument the oracle.
- **Why is `A`'s response independent of the challenge when it
  didn't query?** `A`'s response is a function of its execution trace,
  and the trace *might* depend on `x` through subtle channels (e.g.,
  the ordering of responses to other queries). We have to argue that
  the trace cannot depend on `H(x)` unless `A` actually asked.
- **How do we formalize "averaging over a uniform sample" at the right
  point in the program?** The challenge is sampled, used to set up the
  oracle, and only later does the adversary interact with it.
- **What's the right semantic framework?** We use a
  weakest-precondition (wp) calculus over a probabilistic programming
  language with state. Every step in the proof manipulates expressions
  of the form `program.wp post state` and we need a calculus rich
  enough to handle them.

The formal proof's job is to make every one of these precise and
mechanically check that the argument goes through.

---

## Part 2: The cryptographic proof (game-hopping)

### The three games

We organize the proof around three programs (`Game 0`, `Game 1`,
`Game 2`), each of type "probability distribution over Bool" (Boolean
= adversary wins).

**Game 0 — the original experiment.** Lazy oracle, programmed
on-demand:

```
lazy_init                            -- empty oracle cache
x ← Uniform(input)
chal_x ← x
y_chal ← lazy_query x                -- this lazily samples y and stores (x ↦ y)
for q rounds: adv interacts via the oracle
resp ← read adv's final response
y_check ← lazy_query resp
return y_check = y_chal
```

**Game 1 — explicit `y` sampling.** Unfold the `lazy_query x` step
into "sample `y`; write `(x ↦ y)` into the cache; return `y`". Same
program, just regrouped:

```
lazy_init
x ← Uniform(input);  chal_x ← x
y ← Uniform(output);  set RO[x] := y;  y_chal ← y    -- ← was inside lazy_query
loop / response / check (unchanged)
```

This is a pure program equality — no probabilistic content.

**Game 2 — decouple `chal_x` from `RO`.** Same as Game 1 but *don't*
pre-program the cache at `x`:

```
lazy_init
x ← Uniform(input);  chal_x ← x
y ← Uniform(output);  y_chal ← y                     -- ← skipped the set RO[x] := y
loop / response / check (unchanged)
```

In Game 2, the adversary's `lazy_query` calls now sample fresh `y`
values whenever they hit `x` — they don't see `y_chal`. So the
adversary's distribution over `resp` is *completely independent* of
`y_chal`. This is the point of Game 2.

### The chain of bounds

**Hop 0 → 1: program equality.** `Game 0 = Game 1` as programs (not
just in distribution). The lazy-query unfolding is a definitional
rewrite. No probability lost.

**Hop 1 → 2: up-to-bad.** Games 1 and 2 are *identical until the
adversary queries `chal_x`*. Formally: as long as `chal_x` is never
queried during the loop, the adversary's view in both games is
distributed identically, because the only difference between them
(the pre-programming of `RO[x]`) is invisible. We obtain

$$
\Pr[\text{Game 1 wins}] \;\le\; \Pr[\text{Game 2 wins}] + \Pr[\text{adv queries } \mathit{chal\_x} \text{ in Game 1}].
$$

To make "adversary queries `chal_x`" a measurable event in our setting
we add a *tracking flag* `chal_x_queried_gh : Bool` to the state and
replace every `lazy_query inp` with `lazy_query_tracked inp`, which
behaves the same except that it additionally sets the flag to `true`
whenever `inp = chal_x`. (Game 1 and Game 2 with `lazy_query_tracked`
are wp-equivalent to themselves with plain `lazy_query` on any post
that doesn't read the flag.)

**Bounding Game 2 wins.** In Game 2, `y_chal` is a uniformly random
`output` value that nothing in the program depends on except the final
equality check `y_check = y_chal`. The adversary effectively has to
"guess" `y_chal`. We show this is at most `(q+1)/|output|` —
intuitively, `A` has `q` chances during the loop and one chance at the
final response, and each chance is independent of `y_chal`.

**Bounding the bad event.** In Game 1 (or equivalently, in the tracked
version of the experiment), the adversary "queries `chal_x`" iff at
some point during its `q` loop iterations or its final response check,
some `inp` equals the uniformly-random `chal_x`. The adversary has at
most `q+1` such inputs to compare against a uniform target — so the
bad event happens with probability at most `(q+1)/|input|`.

**Putting it together.** Using `|input| ≥ |output|`:

$$
\Pr[\text{Game 0 wins}] \;=\; \Pr[\text{Game 1 wins}]
\;\le\; \frac{q+1}{|\textsf{output}|} + \frac{q+1}{|\textsf{input}|}
\;\le\; \frac{2(q+1)}{|\textsf{output}|}.
$$

### The unifying observation

Both the "Game 2 wins" bound and the "bad event" bound have the same
shape: "an adversary makes `q+1` attempts to guess a uniformly random
target." We capture this with a single abstract game,
`guess_experiment`, parameterized over

- the target type `T` (= `output` for win, `input` for bad);
- the matching predicate;
- the per-iteration body and the final-step body.

A single lemma `(guess_experiment …).wp F ≤ (q+1)/|T|` then discharges
both intermediate bounds.

---

## Part 3: The formal proof

This part describes how the cryptographic argument is rendered in
Lean. It assumes familiarity with Lean 4 and basic type theory but
not with the specific formalism.

### Framework

The proof is written against a custom probabilistic programming
framework (also part of this repository, in `PlonkLean/Language/`):

- **`Program s α`** is the type of probabilistic programs with state
  type `s` returning values of type `α`. Concretely:
  `Program s α = StateT s SubProbability` where `SubProbability α` is
  the type of sub-probability distributions on `α`.
- **`Program.wp p F σ`** is the weakest precondition operator: given
  a post-condition `F : α × s → ENNReal` and an input state `σ : s`,
  it returns the expected value of `F` under the distribution produced
  by `p` from `σ`. Probabilities are recovered by taking `F` to be an
  indicator function.
- **Lenses** (`Lens γ s`) decompose the state. Each "variable" in the
  program (`chal_x`, `chal_x_queried_gh`, `queries_input`, etc.) is a
  lens. Two lenses can be `disjoint`, expressing that they pick out
  independent parts of the state.
- **`Program.inRange p R`** says that `p`'s reads and writes are
  confined to the lens-range `R`. We use this to express things like
  "`adv` doesn't touch the matched flag" or "`lazy_query` only touches
  the random-oracle state".
- **`Program.EquivModuloLens L p q`** is a derived relation: `p` and
  `q` have equal `wp` on any post that doesn't depend on lens `L`.
  This is the workhorse for tracking-flag elision: extra
  `set flag ...` operations are *invisible* at flag-ignoring posts.

### Module structure

After the refactor, the proof is organized into 6 files:

```
PlonkLean/RO/
  OneWayness_GameHop.lean              (160 lines, the master theorem)
  OneWayness_GameHop/
    Definitions.lean                   (399 lines)
    GuessExperiment.lean              (1494 lines)
    UpToBad.lean                       (947 lines)
    Game1.lean                        (1764 lines)
    Game2.lean                         (721 lines)
```

Plus two small generic additions to shared infrastructure
(`ProgramRange.lean`, `EquivModuloLens.lean`).

- **`Definitions.lean`** — the three games (`ow_game_0`, `ow_game_1`,
  `ow_game_2`), their tracked variants, the flag axioms
  (`chal_x_queried_gh`, `matched_chal_y`, `queries_input`,
  `queries_output`), all disjointness instances. Also `lazy_query_tracked`
  (which is shared by Game 1 and Game 2).
- **`GuessExperiment.lean`** — the abstract `guess_experiment`, its
  interim and collector forms, the *schema framework* for reducing
  per-game wins/bad events to the guess bound, and the bound
  `(q+1)/|T|`.
- **`UpToBad.lean`** — the identical-until-bad machinery: RO-invariance
  lemmas, mass-conservation infrastructure, the
  `ow_game_1_tracked_le_ow_game_2_tracked_plus_bad` theorem.
- **`Game1.lean`** — Game 1' definitions, the four wp-equivalence
  *bridges* connecting Game 1's `lazy_query_tracked`-based body to a
  schema-friendly variant, `game_1_correspondence`, and the
  `(q+1)/|input|` bad-event bound.
- **`Game2.lean`** — Game 2's schema decomposition and the
  `(q+1)/|output|` win bound.
- **Root** — chains everything together into `ow_lazy_bound_via_gamehop`.

The dependency topology is acyclic:

```
Definitions ← {GuessExperiment, UpToBad, Game1, Game2}
GuessExperiment ← {UpToBad, Game1, Game2}
UpToBad ← {Game1}
{Game1, Game2} ← Root
```

### Key abstractions

#### The guess-experiment framework

The most interesting piece of infrastructure is `guess_experiment`
itself, which abstracts both intermediate bounds. Its signature:

```lean
guess_experiment
  (env          : Program state Unit)
  (sample_target: Program state T)
  (target_var   : Lens T state)
  (matched_var  : Lens Bool state)
  (body         : T → Program state Unit)
  (final        : T → Program state Unit)
  (n            : ℕ)
  : Program state Bool
```

It runs `env`, samples a target `t`, stores it in `target_var`,
initializes `matched_var := false`, runs `body t` for `n` rounds, runs
`final t`, and returns the value of `matched_var`. Both the Game 2
win-event reduction and the Game 1 bad-event reduction *are*
instances of `guess_experiment` (with `target_var =
ow_challenge_y`/`ow_challenge_x` and `matched_var =
matched_chal_y`/`chal_x_queried_gh`).

The single bound

```lean
theorem guess_experiment_interim_wp_bound :
    (guess_experiment_interim …).wp F σ  ≤  (n + 1) / |T|
```

is then enough to bound both events. The "interim" variant moves
target sampling to the *end* and replaces the matched-flag tracking
with a *recording list* (a list of all values the adversary's queries
were compared against). Sampling at the end and asking "is the
random target in this fixed-length list?" is a 1-line probability
argument: `n+1` elements in the list, target uniformly in `T`,
membership probability at most `(n+1)/|T|`.

#### The schema

The bridge from the actual game (with the matched flag) to the
interim form (with the recording list) is the *schema*. Its key
ingredient is `schema_inner_equation`: a single per-σ', t equation
that says:

> Provided the `body` and `body_recording` of the actual and
> recording games both decompose as `q_body >>= ...` for some shared
> "query" subprogram `q_body`, with the actual game ending in a
> match-check `if a = t then set matched true` and the recording game
> ending in `append a to queries_list`, the two games produce the
> same `wp` (when run from a freshly-initialized state).

The proof is a chain of `EquivModuloLens` reductions threading the
invariant `matched_var = decide (t ∈ queries_list_var)` through the
loop. Specifically:

1. **`body_match ≈_qs body_aug`** — augmenting the actual body with a
   redundant record-append doesn't change `wp` at posts that ignore
   the queries list.
2. **`body_aug` agrees with itself under the matched-vs-decide
   invariant** — at invariant-preserving states, the two posts
   `F(matched_var)` and `F(decide (t ∈ qs))` are equal.
3. **`body_aug ≈_matched body_rec`** — removing the match-check from
   the augmented body doesn't change `wp` at posts that ignore the
   matched flag.

Combine the three steps and you get
`body_match.wp F_matched = body_rec.wp F_decide` at an aligned
starting state. The schema theorem
`guess_experiment_le_interim_via_schema` plumbs this through the
loop and the final iteration.

Game 2 fits the schema directly: `body_game_2 = q_body_game_2 >>=
match_check`. Game 1's body, on the other hand, uses
`lazy_query_tracked` which buries the match-check inside (it flips
the flag whenever `inp = chal_x`, where `chal_x` is read from
state). To get Game 1 into the schema's pattern we introduce
**Game 1'** — a "schema-friendly" variant with an *explicit*
match-check — and prove four wp-equivalence bridges between Game 1
and Game 1':

- `lazy_query_tracked_bind_wp_eq_lazy_query_bind` — the chal_x_qg
  flip in `lazy_query_tracked` is invisible at flag-ignoring posts.
- `body_recording_game_1_wp_eq_body_recording_game_1'` and the
  analogous final bridge — recording bodies agree at flag-ignoring
  posts.
- `body_game_1_wp_eq_body_game_1'_at_chal_x_eq` and the analogous
  final bridge — actual bodies agree at any post when the state
  has `chal_x = t` (the bound target).
- `loop_final_body_game_1_wp_eq` lifts the body bridge through the
  loop (`loop_n q`) under the chal_x-preservation invariant.
- `guess_experiment_game_1_wp_eq_game_1'` lifts to the full game by
  peeling the common prefix and applying the loop bridge.

`game_1_correspondence` chains these bridges with the schema:
Game 1 → Game 1' (via bridges) → schema → recording form
(Game 1' recording) → Game 1 recording (via the recording bridges in
the reverse direction).

#### Up-to-bad

The Hop 1 → 2 analysis is in `UpToBad.lean`. The key ingredients:

- **RO-invariance for `lazy_query_tracked`**: for any post `F` that
  vanishes when the bad flag is set AND is itself
  `RO[chal_x]`-invariant, `lazy_query_tracked.wp F` is
  `RO[chal_x]`-invariant. Either the lookup hits `chal_x` (flag becomes
  `true`, `F` returns 0), or it doesn't (the lookup is at a position
  where the RO update is invisible). This is the per-step heart of
  the up-to-bad argument; extending it through `oracle_step` and
  `oracle_loop_n` is by induction.
- **Mass conservation**: a family of `_mass_one` lemmas saying that
  every step of `Game 1`/`Game 2` preserves total mass (probability
  sum = 1). Used to derive `Pr[bad in Game 1] = Pr[bad in Game 2]`,
  the linchpin of the up-to-bad cancellation.
- **The final theorem**: `ow_game_1_tracked_le_ow_game_2_tracked_plus_bad`
  states `wp(Game 1, F) ≤ wp(Game 2, F) + wp(Game 1, F restricted to
  bad)` for any `RO[chal_x]`-invariant post `F` (which the win post
  satisfies vacuously).

#### Master theorem

`ow_lazy_bound_via_gamehop` (in the root file) chains:

```
ow_experiment = ow_game_0          (program equality, by reflexivity)
              = ow_game_1          (Hop 0 → 1, by ow_game_0_eq_ow_game_1)
              ≈ ow_game_1_tracked  (flag elision at flag-ignoring posts)
              ≤ ow_game_2_tracked + bad      (up-to-bad)
              ≤ (q+1)/|output| + (q+1)/|input|   (the two intermediate bounds)
              ≤ 2(q+1)/|output|     (|input| ≥ |output|)
```

The Lean proof is a short `calc` block — about 50 lines — once all
the intermediate theorems are in place.

### Design choices and lessons

Some choices that turned out to matter:

**`EquivModuloLens` as a first-class relation.** Many of the proof's
"obvious" facts — "the tracking flag is invisible if the post
doesn't read it", "adding a redundant record-append is a no-op" —
are most naturally expressed as wp equivalences modulo a particular
lens. We packaged this as a relation `EquivModuloLens L p q` with
closure rules (`refl`, `symm`, `trans`, `bind`, `bind_eq_p`,
`bind_eq_k`) and an instance combinator `loop_n_then_congr` (lift
body and final equivalences through a loop). Once the calculus was
in place, most "moral" arguments became 5–10 line proofs.

**Splitting `body_match` into `body_match` and `body_aug`.** The
schema's invariant `matched = decide (t ∈ qs)` requires both flags
*and* the queries list to be in scope. We introduce an intermediate
"augmented" body that does both the match-check *and* the
record-append, and show it's `wp`-equivalent to each of the two pure
forms at the appropriate `IgnoresLens` post. This is what lets the
invariant tracking go through cleanly.

**`schema_inner_equation` as an extracted lemma.** Originally the
schema's correspondence proof was inlined inside
`guess_experiment_le_interim_via_schema`. When we needed the same
correspondence proof for Game 1 (after the bridges convert Game 1
to Game 1'), we extracted the inner equation as a standalone lemma
parameterized over the `q_body`/`q_final` decomposition. Now both
the Game 2 path (direct schema application) and the Game 1 path
(bridges → schema_inner_equation → reverse bridges) share the same
core argument.

**The `wp_strengthen_lens_preserved` building block.** Many proofs
needed the pattern "this program preserves lens `L`, so I can
strengthen the post with an `if L.get = L.get σ then F else 0`
check and the wp doesn't change." We named this and use it 15+
times across the proof. It's the most-used non-trivial wp lemma.

**Beware do-notation desugaring.** Lean 4's do-notation desugars
through the monad instance, which in our case goes
`Program s = StateT s SubProbability`. Some `wp` tactics that work
on direct `>>=` chains struggle to unify against the desugared form,
producing wnh timeouts in the kernel. The workaround is either to
extract `unfold X` of the do-block as a separate lemma or to keep
the underlying programs *named* (so the kernel can rewrite at the
name level rather than chasing through the desugared bind chain).

**`private` qualifier discipline.** Of the ~163 declarations across
the 5 modules, about 132 are `private` — they're internal helpers
that exist only to support a handful of public theorems. This keeps
the public API small: ~31 declarations across 5 modules, dominated
by game definitions, the master theorems, and the schema
infrastructure.

### What was hard

- **Closing the schema's inner assembly.** The chain of EquivModuloLens
  steps + state alignment + invariant lemmas is a 7-step argument;
  getting the right form on each step (in particular, peeling the
  trailing `get matched_var` into a `matched`-reading post, and
  aligning the LHS/RHS to a common `σ_aligned` state) took several
  iterations. The final proof is ~150 lines but heavily uses
  pre-existing helpers; without them the assembly would be unwieldy.
- **The game-level Game 1 bridge.** `guess_experiment_game_1_wp_eq_game_1'`
  required threading the `chal_x = t` invariant through the loop body
  via `wp_strengthen_lens_preserved`. The bridge proof is recursive
  on `q` and required the right form of the body-level bridge to
  combine cleanly with `loop_n_congr`.
- **Whnf timeouts on deep do-blocks.** Several `wp`-manipulation
  tactics that should have "just worked" hit Lean kernel timeouts
  during definitional checking. The fix in each case was either
  to extract a small helper or to pre-name a subprogram so the
  kernel could rewrite at a name rather than chase a deeply nested
  bind expression.
- **State-conditional equivalences.** `body_game_1` (which reads
  `chal_x` from state) and `body_game_1'` (which uses the bound
  target `t` directly) are equivalent only at states where
  `chal_x.get σ = t`. This isn't an `EquivModuloLens` statement
  (which is state-unconditional); we had to use
  `wp_strengthen_lens_preserved` to add the
  `chal_x = t` check to the post, then use it inside the proof.

### Process

The proof was developed and refactored over several sessions:

1. **Architecture (planned in `OW_GameHop_Plan.md`).** Three games,
   one up-to-bad analysis, both intermediate bounds via a unifying
   guessing-game framework.
2. **Closing sorries.** Started with 4 sorries (the schema's inner
   assembly + three Game 1 game-hop bridges); each was closed
   one by one. The final sorry (the game-level Game 1 bridge) was
   the hardest and required the state-conditional analysis described
   above.
3. **Module split.** A single 5349-line file was split into 5
   modules (plus a slim root) following the natural sections.
4. **Hygiene pass.** 132 helpers marked `private`, 4 unused
   hypotheses removed, 50+ lines of stale comments stripped.
5. **Pattern extraction.** Two reusable combinators
   (`Program.wp_zero_of_lens_preserves`, `loop_n_then_congr`) moved
   into shared infrastructure, available to future cryptographic
   proofs in this codebase.
6. **Naming pass.** 14 renames in public API to use full lens names
   (e.g., `_lqt_` → `_lazy_query_tracked_`).

The final state: 5485 lines across 6 files, 0 sorries, 0 axioms
specific to the proof (only the underlying RO model has the
expected axioms for the variable types and disjointness), clean
build.

---

## What this proof gives us

- **A second, independent verification** of the OW lazy bound. The
  existing proof in `OneWayness.lean` uses different machinery
  (`useful_preimage` lemmas, deferred-sampling techniques in
  `QueryHit.lean`). Two independent proofs of the same theorem in
  the same Lean codebase make a strong correctness statement.
- **A reusable game-hopping framework.** `guess_experiment`,
  `schema_inner_equation`, and `guess_experiment_le_interim_via_schema`
  are generic in their target type and matching predicate. Any future
  cryptographic proof in this codebase that needs a "guessing-game"
  reduction can use them.
- **A reusable up-to-bad pattern.** The combination of
  `EquivModuloLens` + `Program.wp_zero_of_lens_preserves` + mass
  conservation generalizes to any "identical-until-bad" analysis.
- **A demonstration that formal cryptographic proofs can be
  legible.** The 6-module structure, the ASCII flow diagram in the
  root file, and the private/public API split mean a cryptographer
  can read the proof's outline without diving into any `wp`
  manipulation. (And if they do dive in, the helpers and naming
  conventions should keep things tractable.)
