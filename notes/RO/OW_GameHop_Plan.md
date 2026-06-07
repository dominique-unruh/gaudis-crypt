# Game-hopping proof of OW: plan

An alternative proof of `ow_lazy_bound : P[ow_experiment wins] ≤ 2(q+1)/|output|`
via game hops and up-to-bad analysis, with both probability bounds reduced
to a single unifying "guessing game" lemma.

This is a parallel proof to the existing `useful_preimage` proof in
`PlonkLean/RO/OneWayness.lean` (Layers A_OW / C_OW / D_OW) and the
deferred-sampling machinery in `PlonkLean/RO/QueryHit.lean`. We keep the
old proof for now; the new one is in `PlonkLean/RO/OneWayness_GameHop.lean`
and is meant as a clarity demonstration.

---

## The games

Three programs, each `Program state Bool`. All run with `lazy_init` and
`lazy_query`.

### Game 0 — the original OW experiment

```
lazy_init
x ← Uniform input
chal_x ← x
chal_y ← lazy_query x          -- samples y, inserts (x ↦ y) into RO
loop q times:
  adv
  inp ← Program.get oracle_input
  y' ← lazy_query inp
  Program.set oracle_output y'
resp ← Program.get ow_response
y_check ← lazy_query resp
return (decide (y_check = chal_y))
```

This is the existing `ow_experiment ow_adv q lazy_init lazy_query` from
`PlonkLean/RO/OneWayness.lean`.

### Game 1 — explicit y sampling

The `lazy_query x` step, applied to an empty cache at `x`, *definitionally*
unfolds to "sample y uniform, write (x ↦ y) into RO, return y". Make those
two operations explicit and write them out separately:

```
lazy_init
x ← Uniform input
chal_x ← x
y ← Uniform output                                      -- ← was inside lazy_query
RO ← random_oracle_state.set
       (fun k => if k = x then some y
                 else random_oracle_state.get _ k)      -- ← was inside lazy_query
chal_y ← y
loop q times: …
resp ← Program.get ow_response
y_check ← lazy_query resp
return (decide (y_check = chal_y))
```

### Game 2 — drop the (x ↦ y) insertion (the "up-to-bad" game)

Remove the RO insertion from Game 1. The adversary now sees a `chal_y` that
is uniformly random but not reflected in the random oracle.

```
lazy_init
x ← Uniform input
chal_x ← x
y ← Uniform output
chal_y ← y
                                                        -- ← no insertion
loop q times: …
resp ← Program.get ow_response
y_check ← lazy_query resp
return (decide (y_check = chal_y))
```

---

## The hops

### Hop 0 → 1: program equality

`Game 0 = Game 1` as `Program state Bool`.

Justification: definitional unfolding of `lazy_query x` on an RO state where
`x` is not cached (which holds after `lazy_init`). Pure refactoring; no
probabilistic content.

### Hop 1 → 2: up-to-bad

Define **`bad_queried_x : state → Prop`** as "the adversary's loop body (or
the final `lazy_query resp`) ever called `lazy_query` at input `chal_x`."
Tracked by a flag variable along the lines of `QueryHit.lean`'s
`chal_x_queried`.

Games 1 and 2 are *identical until bad*: the only place they can differ is a
`lazy_query inp` with `inp = chal_x`, where Game 1's RO has `chal_x ↦ chal_y`
cached (returning `chal_y`) but Game 2's does not (sampling fresh).

**Conclusion (up-to-bad lemma):**

```
P[Game 1 wins] ≤ P[Game 2 wins] + P[bad in Game 1].
```

---

## Bounds via the unifying guessing game

Both `P[Game 2 wins]` and `P[bad in Game 1]` reduce to the same combinatorial
game: an adversary with q+1 attempts tries to hit a uniformly random target
that's independent of its view.

### The guessing game

```
guess_experiment (T : Type) [Fintype T] [Nonempty T] (n : ℕ)
    (env : Program state Unit)        -- non-target setup (e.g. RO init,
                                        --  sampling of irrelevant variables)
    (target_var : Lens T state)       -- where the target is stored
    (adv_step : Program state T)      -- one "guess", may have side effects
    : Program state Bool := do
  env
  t ← Uniform T
  Program.set target_var t
  Program.set matched false           -- matched flag, disjoint from target_var
  loop n times:
    g ← adv_step
    if g = (Program.get target_var) then
      Program.set matched true
  Program.get matched
```

Hypotheses:

* `adv_step` is in `target_var.compl.range` (adversary's guess never reads
  the target — i.e., the guess is independent of `t`).
* `env` is in `target_var.compl.range` (setup never reads the target — needed
  so target sampling and env can be hoisted in either order).

**Conclusion (guessing-game lemma):**

```
(guess_experiment T n env target_var adv_step).wp
    (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0)
    σ₀
  ≤ n / |T|
```

The proof is the standard "Layer A + loop accumulation" pattern: each guess
matches with prob ≤ 1/|T|; q+1 guesses give ≤ (q+1)/|T| by union (or
equivalently by `oracle_loop_n_wp_linear_bound` over the matched-flag
indicator).

### Reducing Game 2 wins to Guess(output, q+1)

* `T := output`
* `target_var := chal_y` (or the new flag-bearing version of it)
* `env` = the prefix `lazy_init >>= sample x >>= set chal_x` (no RO write
  involving y; just RO init + sampling x and storing it).
* `adv_step` per iteration produces a `T`-value: from
  `adv >>= get oracle_input >>= lazy_query >>= set oracle_output`, the
  emitted value is the result of `lazy_query`. After q loop iterations there
  is one final `lazy_query resp` (the "verification query"); that's
  the (q+1)st guess.

The match check (`y_check = chal_y`) is exactly the guess-matching condition:
the y-value sampled by `lazy_query` lands on `chal_y`.

Caveat: in Game 2, "guesses" must be IDENTIFIED with the lazy_query outputs;
the OW win condition needs to be shown equivalent to "some guess matched."
This requires:

* A *cached match* in a loop iteration: any previous `lazy_query inp` that
  returned `chal_y` can be replayed by the adversary as the final `resp`,
  and the cached value will equal `chal_y`. So "some loop-step output =
  chal_y" implies "final y_check = chal_y" (the adversary can win).
* A *final fresh match*: the (q+1)st guess is the final `lazy_query resp`,
  which is a fresh sample if `resp` was not previously queried.

Combined: `P[Game 2 wins] = P[some guess matched]`. Bounded by Guess(output, q+1).

### Reducing bad-in-Game-1 to Guess(input, q+1)

* `T := input`
* `target_var := chal_x`
* `env` = the prefix `lazy_init >>= sample y >>= set chal_y` (chal_y is set
  from y, not from RO; chal_x is *not* sampled yet, so adv's view is
  independent of chal_x by being independent of x).
* `adv_step` per iteration produces a `T = input` value: from
  `adv >>= get oracle_input`, the `inp` value the adversary chose.

The bad event is "some iteration's `inp = chal_x`" — i.e., a guess matched.

This requires sampling `chal_x` AFTER the adversary runs the experiment, or
equivalently, since `chal_x`'s value doesn't affect the experiment (in
Game 2) the order is interchangeable. Formally: `chal_x` is sampled
uniformly and independent of the experiment's other randomness, and the
adversary's view is independent of `chal_x`.

Once that's set up: `P[bad in Game 1] = P[some guess matched]`. Bounded by
Guess(input, q+1).

---

## The full chain

```
P[Game 0 wins]
  = P[Game 1 wins]                              -- Hop 0 → 1: program eq
  ≤ P[Game 2 wins] + P[bad in Game 1]           -- Hop 1 → 2: up-to-bad
  ≤ Guess(output, q+1) bound                    -- reduction
    + Guess(input, q+1) bound                   -- reduction
  ≤ (q+1)/|output| + (q+1)/|input|              -- guessing lemma × 2
  ≤ 2(q+1)/|output|                             -- card_input_ge_output
```

---

## Proof obligations (Lean lemmas to build)

In `PlonkLean/RO/OneWayness_GameHop.lean`:

1. **`ow_game_0`**, **`ow_game_1`**, **`ow_game_2`** — the three game
   definitions. Game 0 may simply alias `ow_experiment`.

2. **`ow_game_0_eq_ow_game_1`** — program equality (Hop 0 → 1). Proof by
   `Program.ext_of_wp` + unfolding `lazy_query` on the empty-RO branch.

3. **`Program.up_to_bad`** — generic up-to-bad lemma at the wp level:
   given a "bad" predicate and equality of wp's restricted to non-bad
   outputs, derive a wp inequality with a `+ P[bad]` term. (Framework-level;
   could live in `RO/Transfer.lean` or in `ProgramRange.lean`.)

4. **`ow_game_1_le_game_2_plus_bad`** — applying `Program.up_to_bad` to
   Game 1 vs Game 2, using a `chal_x_queried` style tracking variable to
   define `bad_queried_x`.

5. **`guess_experiment`** def + **`guess_experiment_wp_bound`** — the
   unifying guessing game and its `n/|T|` bound. (Framework-level; could
   live in `RO/OracleLoop.lean` alongside `oracle_loop_n_wp_linear_bound`.)

6. **`ow_game_2_wins_le_guess_output`** — reduction of Game 2 win event to
   Guess(output, q+1).

7. **`ow_bad_le_guess_input`** — reduction of bad-in-Game-1 to
   Guess(input, q+1).

8. **`ow_lazy_bound_via_gamehop`** — combine the chain to get the
   `2(q+1)/|output|` bound.

---

## Notes on infrastructure we may want to add

* **An up-to-bad framework**. Possibly more than one lemma — closure under
  bind ("if hops compose, so does the bad-event tracking"), an
  identical-until-bad SubProb-marginal version, a wp-level inequality
  version, etc. We'll start with the minimal wp-level statement needed
  for OW.

* **A "matched-flag tracking" combinator** for the guessing game. A
  variant of `Program.wp_get_then_conditional_set_disjoint_no_op` that
  toggles the matched flag in a counting-style argument.

* **A "guess produces a uniform value independent of target" lemma**.
  Captures what makes `lazy_query` work as a guess for Game 2: a fresh
  sample is uniform; a cached sample was previously a fresh sample. May
  bottom out at `lazy_query_wp_step` with `bad x y σ = if y = target then
  1 else 0`.

---

## What this gives us

Compared to the existing `useful_preimage` + `QueryHit` proof (~3000 + a
few hundred lines):

* No `useful_preimage` indicator — its role is taken by Game 2's straight
  win event, which is independent of `chal_y` *by construction*.
* No `chal_x_queried` tracking via Layer A_OW / C_OW / D_OW — its role is
  taken by the up-to-bad analysis.
* No deferred-sampling machinery — the conditional independence becomes
  manifest in Game 2 (y was never written to RO, so y is independent of
  everything).
* The two probability bounds factor through one shared lemma
  (`guess_experiment_wp_bound`), instead of being two ad-hoc Layer A
  arguments.

Estimated size of the new proof: roughly 300–500 lines, vs. ~3000 lines
for the QueryHit-based version. The shared `guess_experiment` infrastructure
is reusable for other crypto proofs (signature unforgeability, hash
preimage, etc.).
