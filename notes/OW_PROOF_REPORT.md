# Closing the OW (One-Wayness) Reduction Without Axioms

## What we're proving

The **one-wayness** of a hash function `H` modeled as a random oracle:
given a hash value `y = H(x)` for a uniformly random input `x`, no
efficient adversary can recover `x` (or any other preimage of `y`)
with high probability.

Concretely, the theorem says: for an adversary that makes at most `q`
oracle queries during its computation and outputs some candidate
preimage `resp`, the probability that `H(resp) = y` is bounded by:

$$\Pr[H(\text{resp}) = y] \leq \frac{q + 1}{|\text{input}|}$$

where `|input|` is the size of the input space. This is the standard
tight bound for one-wayness in the random oracle model: the only ways
to find a preimage are either to query the oracle on the actual `x`
(probability `q/|input|` over `q` random guesses) or to guess `x`
without querying (probability `1/|input|`).

In Lean, this is `ow_experiment_resp_eq_chal_x_bound` in
`OneWayness.lean`. After this session, both `OneWayness.lean` and
`QueryHit.lean` are **sorry-free**.

## What makes this proof non-trivial

If you've seen cryptography handouts before, the bound `(q+1)/|input|`
looks like a one-line argument: "adv either queries the challenge or
doesn't; either way it's bounded." But making this rigorous in a proof
assistant requires being explicit about several things that the handout
elides:

1. **What does "queried the challenge" even mean** as a statement about
   probability distributions? The experiment doesn't naturally carry
   that information.
2. **Why is adv's response independent of the challenge** when adv
   didn't query it? Adv's response is some function of its execution
   trace, and the trace might *almost* depend on the challenge — we
   need to argue that the dependency only kicks in when adv queries.
3. **How do we formalize "averaging over a uniform sample"** at the
   right point in the program? The challenge is sampled, used to set
   up the oracle, and only later does the adversary interact.
4. **What's the right framework**? We use a weakest-precondition (wp)
   calculus over a probabilistic programming language. Every step in
   the proof manipulates `program.wp post state` terms, and we need
   the right lemmas to push things around.

The result of the session is a clean factorization where each of these
concerns is handled by a focused lemma, and the final theorem composes
them.

## The setup: probabilistic programs and wp

The codebase models the experiment as a probabilistic program in a
small DSL with `Program.get`, `Program.set`, `Program.uniform`, `pure`,
and `>>=`. Each program induces a sub-probability distribution on
output values × output states.

The **weakest-precondition** `p.wp F σ` is the expected value of `F`
applied to the (output value, output state) pair, when `p` runs
starting at state `σ`. So `experiment.wp [adversary wins] σ₀` is the
probability of the winning event.

Lenses (`ow_challenge_x`, `chal_x_queried`, `random_oracle_state`, …)
identify specific pieces of the state. Disjoint lenses can be set and
read independently; `wp_set_disjoint_no_op` says that setting a
disjoint lens is invisible to a program/post that doesn't touch it.

The two key structural lemmas about wp:

- **`wp_shift_input`**: if a program `p` doesn't interact with lens
  `L`, then shifting `L` in the input is equivalent to shifting it in
  the output post. (Formally: `p.wp F (L.set v σ) = p.wp (F ∘ shift) σ`.)
- **`wp_strengthen_lens_preserved`**: same hypothesis, says `p` preserves
  `L`'s value, so we can restrict the post to the L-preserved support
  for free.

Almost every nontrivial step in the proof is one of these two lemmas
applied at a carefully chosen position.

## The two-layer decomposition

The winning event `[resp = chal_x ∧ is_preimage(resp)]` splits based
on whether adv queried the challenge during its computation:

```
[adv wins] ≤ [adv queried chal_x] + [adv didn't query chal_x ∧ resp = chal_x]
```

This is a pointwise inequality on indicator functions, and taking
expectations gives:

$$\Pr[\text{adv wins}] \;\leq\; \underbrace{\Pr[\text{queried}]}_{\text{Layer C}_\text{obs}} \;+\; \underbrace{\Pr[\neg\text{queried} \wedge \text{resp} = \text{chal\_x}]}_{\text{Conditional independence}}$$

The proof strategy is to bound each of these separately:

- **Layer C_obs** ≤ `q / |input|`: the adversary has `q` chances to
  pick the challenge as an oracle query, each of which has probability
  `1/|input|` of being correct (since chal_x is uniform).
- **Conditional independence** ≤ `1 / |input|`: when adv doesn't query
  the challenge, its response is independent of the challenge's value,
  so a uniform challenge matches the response with probability
  `1/|input|`.

Adding these gives `(q+1)/|input|`.

## The tracking variable trick

The native experiment doesn't carry an explicit "did adv query the
challenge" flag — it's a property of the run, not the state. To talk
about it in the wp framework, we *instrument* the experiment.

We introduce `chal_x_queried : Variable Bool` — a piece of state that
adv can neither read nor write (enforced by disjointness assumptions).
The experiment initializes it to `false` and the (modified) loop body
sets it to `true` whenever `oracle_input = ow_challenge_x` at the
beginning of an iteration:

```
ow_loop_body_tracked = do
  ow_adv  -- adv writes oracle_input
  let inp ← Program.get oracle_input
  let cx  ← Program.get ow_challenge_x
  if inp = cx then Program.set chal_x_queried true
  let y ← lazy_query inp
  Program.set oracle_output y
```

Critically, the tracking is done by *the experiment*, not by adv —
this lets us inspect adv's queries without changing adv. The tracked
and untracked experiments have the same probability for any
chal_x_queried-independent event (`ow_experiment_eq_tracked_lazy`),
so all bounds we prove transfer back.

With this in place, "adv queried chal_x" is just `chal_x_queried.get`
at the end of the experiment — a concrete state predicate.

## Layer C_obs: bounding the query probability

The intuition: across `q` iterations, adv proposes `q` query inputs.
Since adv doesn't see `chal_x`, its choices are independent of it.
For a uniform `chal_x` sampled from `|input|` possibilities, each
query has a `1/|input|` chance of matching. Union bound gives
`q/|input|`.

In the wp framework, this becomes the **strengthened sum lemma**:

```
ow_loop_tracked_chal_x_queried_sum_le:
  ∀ q σ, σ.cxq = false →
    ∑ x : input, loop_q.wp [chal_x_queried] (chal_x.set x σ) ≤ q.
```

Read: across all possible challenge values `x`, the total probability
that the loop ends with `chal_x_queried = true` (when started in a
state where chal_x = x) is at most `q`.

The proof is by induction on `q`. Each iteration of the loop contributes
at most `1` to the sum: in any particular iteration, adv picks some
input `inp`, and exactly one challenge value (`x = inp`) causes the
flag to flip. The remaining `|input|-1` values pass through unchanged
and contribute via the inductive hypothesis to subsequent iterations.

The technical machinery — `wp_shift_input` to commute `chal_x.set x`
past adv, `wp_finset_sum` to pull the sum inside adv's wp,
`wp_strengthen_lens_preserved` to keep track of which states preserve
relevant invariants — is what makes the "intuitively each step
contributes 1" rigorous.

Composing the sum lemma with the rest of the experiment (the uniform
sampling of `chal_x`, the pre-loop oracle query, the post-loop check)
yields `ow_experiment_tracked_chal_x_queried_bound`:
`P[chal_x_queried] ≤ q/|input|`.

## Conditional independence: the deeper layer

This is where most of the session's effort went. The bound is:

```
P[¬chal_x_queried ∧ resp = chal_x] ≤ 1/|input|.
```

**The intuition**: condition on the event "adv didn't query the
challenge." In this case, adv's entire view (its random tape plus the
oracle responses it received) is independent of `chal_x` — adv literally
never interacted with information about `chal_x`. So adv's response
`resp`, computed from its view, is also independent of `chal_x`. The
challenge is uniformly distributed over `|input|`, so the probability
that any particular value (in this case, `resp`) equals the challenge
is exactly `1/|input|`.

**Why is this harder than it sounds?** In the wp framework, we can't
just "condition on an event" the way a probabilist would on paper.
Conditioning would require splitting the measure into two pieces and
manipulating each. Instead, we need to express the bound *directly*
as a wp manipulation. The key insight is that the bound follows from
a *symmetric* sum lemma:

```
ow_loop_tracked_indep_sum_le_strong:
  ∀ q σ, ∑ x, loop_q.wp [resp = x ∧ ¬cxq] (chal_x.set x σ) ≤ [¬cxq.get σ].
```

This says: across all possible challenge values, the total probability
of "resp happens to equal this particular challenge AND we didn't get
flagged" is at most 1 (when starting in a non-flagged state).

Why this bound? Look at the inner predicate. For any fixed adversary
outcome (where adv produced some specific `resp_value` and didn't get
flagged), the indicator `[resp = x ∧ ¬cxq]` is `1` for exactly *one*
challenge value (namely `x = resp_value`) and `0` for all others. So
summing over `x` gives at most `1` for any outcome, regardless of `q`.

This is the conceptual core of conditional independence, but expressed
without explicit conditioning.

### Why "strengthened" by `[¬cxq.get σ]`?

The naive statement would just bound by `1`. The strengthening
(`[¬cxq.get σ]`, which equals `1` when cxq is false and `0` when true)
is needed for the **inductive proof** to go through.

In the inductive step, consider the case where adv's current iteration
queries the challenge (the "hit" case). The body sets `cxq = true`,
and the remaining `q` iterations run from a state with `cxq` already
flipped. We need to argue that this contributes `0` to the sum (because
the `¬cxq` indicator at the end is `0`). The strengthened IH at the
`cxq = true` state says `∑ x ≤ [¬cxq] = [¬true] = 0`, forcing every
term in the sum to be `0` by positivity. In particular, the term where
`x` equals the (preserved) `chal_x.get` value is `0`, which is the
term we need for the hit case.

Without this strengthening, the inductive argument would need a separate
"loop preserves cxq=true" lemma. With the strengthening, it falls out
of the IH for free. This is a small example of a recurring theme in
formalization: a slightly stronger statement is often easier to prove
by induction than the obvious weaker one.

## The composition challenge: bridging F_bool to F'_x

With the sum lemma in hand, we'd like to apply it directly to the
experiment. The experiment's post is:

```
F_bool(b, σ) = [resp.get σ = ow_challenge_x.get σ ∧ ¬chal_x_queried.get σ]
```

Note that this reads `ow_challenge_x.get σ` from the final state —
the challenge value is read dynamically.

The sum lemma, on the other hand, uses a per-x post:

```
F'_x(_, σ) = [resp.get σ = x ∧ ¬chal_x_queried.get σ]
```

where `x` is a *fixed* value (the summation variable).

These are equal *if* we know that `chal_x.get σ = x` at the end state.
And indeed, in the experiment, after `uniform x; set chal_x x`, the
challenge is set to `x` and *no subsequent step writes it*. So at any
final state, `chal_x.get` equals the sampled `x`.

But — and this is the technical heart of the session — proving "no
subsequent step writes chal_x" is more subtle than it sounds in our
wp framework.

### Why `wp_strengthen_lens_preserved` doesn't apply directly

The `wp_strengthen_lens_preserved` lemma says: if a program is in
`L.compl.range` (i.e., doesn't *interact* with `L`), then its wp
preserves `L`'s value, and we can strengthen any post with the
"L-preserved" condition for free.

The tracked loop body, however, *reads* `chal_x` via
`Program.get ow_challenge_x` to test `inp = cx`. Reading puts the
program outside `chal_x.compl.range` in the framework's accounting.
The framework treats reads symmetrically with writes for this lens-range
machinery — both are "interactions" that prevent us from shifting
the lens.

This is a real constraint, not just bookkeeping: a program that reads
chal_x might branch differently depending on its value, so we can't
freely shift chal_x without changing the program's behavior.

But what we want isn't "shift chal_x without changing behavior" —
we want to argue that chal_x's *value at the output* equals its
value at the input. The body reads chal_x but never writes it, so
this is true. We just need a custom proof.

### Recovering chal_x preservation

The body decomposes as:

```
body = ow_adv  >>=
       get oracle_input  >>=        -- captures inp
       get ow_challenge_x >>=       -- captures cx (THIS reads chal_x)
       (if inp = cx then set chal_x_queried true else pure ()) >>=
       lazy_query inp >>=
       set oracle_output
```

The key observation: after the two gets, `inp` and `cx` are bound
*values* in scope. The remaining program `(if inp = cx then …;
lazy_query inp; set oracle_output)` doesn't *read* chal_x anymore —
it uses the captured `cx` value. So that remaining program IS in
`chal_x.compl.range`.

Combined with the fact that adv is in `chal_x.compl.range`
(it can't read chal_x by assumption), we get a two-step argument:

1. `wp_strengthen` on `adv` enforces chal_x preservation through adv.
2. After the `get`s capture `inp` and `cx` as values, `wp_strengthen`
   on the inner program enforces chal_x preservation through the rest.

This gives `ow_loop_body_tracked_preserves_chal_x_wp`. By induction
on `q`, this lifts to `ow_loop_tracked_preserves_chal_x_wp`: the
whole tracked loop preserves chal_x's value.

This was the conceptual breakthrough for closing the proof. Once
chal_x preservation is established, F_bool and F'_x agree on the
loop's support, and the equivalence we need follows.

## How the pieces fit together

Here's the conditional independence bound, end-to-end, as a sequence
of equalities and bounds:

```
experiment.wp F_bool σ₀

    -- Unfold: init + set cxq false + uniform x.
    -- After lazy_init: state has all-none RO. After set cxq false: σ_a.
  = (1/|input|) · ∑ x, (set chal_x x; ⟨rest⟩).wp F_bool σ_a
```

Here `⟨rest⟩ = lazy_query x; set chal_y y; loop_q; post_loop; pure`.
The `(1/|input|)` factor and the sum come from `Program.uniform`'s
wp definition.

```
    -- Post_loop preserves resp, chal_x, cxq (only modifies RO).
    -- post_loop_preserves_indep_wp bounds (post_loop).wp F_bool by
    -- the input state's indicator.
  ≤ (1/|input|) · ∑ x, (set chal_x x; lazy_query x; set chal_y y; loop).wp F_unit σ_a
```

`F_unit` is the same indicator as `F_bool` but on `Unit × state`
(the loop's output type) — they evaluate to the same thing on state.

```
    -- After set chal_x x: state has chal_x = x. chal_x preservation
    -- through the rest (loop reads chal_x but doesn't write) means
    -- the final chal_x is still x. So F_unit (which reads chal_x.get
    -- dynamically) agrees with F'_x (which uses fixed x) on the support.
  = (1/|input|) · ∑ x, (lazy_query x; set chal_y y; loop).wp F'_x (chal_x.set x σ_a)
```

```
    -- F'_x freshness: averaging over the uniform RO sample y_lq from
    -- lazy_query x is invariant — the post doesn't depend on RO[x]
    -- on the ¬cxq support, and adv's behavior conditional on ¬cxq is
    -- independent of RO[x]. Also drops the chal_y set (disjoint).
  = (1/|input|) · ∑ x, loop.wp F'_x (chal_x.set x σ_a)
```

```
    -- Strengthened sum lemma at σ_a (cxq = false): the sum is ≤ 1.
  ≤ (1/|input|) · 1 = 1/|input|.
```

## Why each technical piece exists

In the proof above, several non-obvious technical lemmas appear. Here's
why each is needed:

**`ow_loop_tracked_indep_sum_le_strong`** (the strengthened sum
lemma): the core "at most one x matches resp" argument. The
strengthening `[¬cxq.get σ]` makes the inductive step's hit-case
trivial (gives 0 instead of needing a separate argument).

**`ow_loop_tracked_indep_RO_invariance_avg`** (averaged invariance):
to drop the pre-loop `lazy_query x` (which inserts a uniform value
into `RO[x]`), we need to know that averaging over that value doesn't
change the loop's wp at F'_x. The conceptual statement is "if adv
doesn't query x, it doesn't see RO[x], so it doesn't matter what's
there."

**`ow_loop_tracked_lazy_query_freshness_indep`**: composes the
averaged invariance with the chal_y set step (also dropped via
disjointness) to give the precise lemma we use to drop the prefix
from the experiment.

**`post_loop_preserves_indep_wp`**: bounds the post-loop tail by the
input-state indicator. The post-loop only modifies RO, so resp,
chal_x, and cxq are all preserved — the indicator can't increase.

**`ow_loop_tracked_preserves_chal_x_wp`** (and its body version): the
chal_x preservation bridge described above. Without this, F_bool and
F'_x are different posts and we can't connect the experiment to the
sum lemma.

## The conceptual arc

Reading the proof linearly, the key conceptual moments are:

1. **Recognize the right decomposition.** The naive proof attempt
   says "either adv queries or doesn't" but doesn't say how to
   formalize that in wp. The tracking variable makes the case split
   into a concrete state predicate.

2. **Find the right inductive invariant.** For Layer C_obs, the
   sum lemma `∑ x ≤ q` is the right statement — it's structurally
   compatible with the loop's body+rest decomposition. For conditional
   independence, the analogous `∑ x ≤ 1` lemma works, but only if
   strengthened by `[¬cxq]` to make the hit case fall out trivially.

3. **Identify the freshness and averaging arguments.** To bridge
   from the experiment to the sum lemma, we need to absorb the
   pre-loop oracle interactions. These are the averaged invariance
   and freshness lemmas — both are essentially "an unobservable
   uniform sample averages out."

4. **Handle chal_x preservation.** The loop reads chal_x, so it's not
   in `chal_x.compl.range`. But it doesn't *write* chal_x, so its
   value is preserved at the output. This required a custom proof
   exploiting the body's structure (gets capture values, leaving a
   write-only remainder).

5. **Compose carefully.** The final composition has half a dozen
   lemmas applied at the right spots. Each step is conceptually
   small but technically delicate (wp_bind unfoldings produce match
   forms; rewrites need to target the right side; etc.).

## A brief comparison: Layer C_obs vs. conditional independence

Both layers use the same "strengthened sum lemma over uniform x"
pattern. The structural difference is in the hit-case bound:

- **C_obs**: when adv queries chal_x, `chal_x_queried` flips to true
  for the rest of the run. The hit-case contribution is `1` per
  iteration. Total bound: `q`.
- **Indep**: when adv queries chal_x, `chal_x_queried` flips to true,
  making `[¬cxq]` false for all states reachable from there. The
  hit-case contribution is `0` for any subsequent iteration. Total
  bound: `1`.

This is the same mathematical phenomenon — conditioning on `¬cxq`
zeros out the queried branch — but expressed in the additive language
of wp.

## Files and lemmas

The proof lives in two files:

- **`PlonkLean/QueryHit.lean`** (~3000 lines): all the wp machinery
  for the OW analysis, organized roughly as:
  1. Tracked loop definitions and equivalence with untracked.
  2. inRange lemmas for various lens ranges.
  3. The strengthened sum lemmas (C_obs and indep).
  4. The averaged invariance lemmas (cxq and indep).
  5. The freshness lemmas (cxq and indep).
  6. The chal_x preservation lemmas.
  7. The two layer bounds and final composition.

- **`PlonkLean/OneWayness.lean`**: defines the OW experiment and
  composes the two layer bounds to give the final theorem.

Both files are now **sorry-free**. The proof depends only on the
underlying framework axioms (lens definitions, disjointness of
distinct named variables, basic measure-theoretic facts about
ENNReal sums), which are design choices rather than holes.

## Dependency tree of the conditional independence proof

```
ow_experiment_tracked_indep_bound                    -- THE BOUND
├── post_loop_preserves_indep_wp                     -- drop post-loop
├── ow_loop_tracked_preserves_chal_x_wp              -- bridge F_bool ↔ F'_x
│   └── ow_loop_body_tracked_preserves_chal_x_wp     -- body preserves
│       └── body_inner_inRange_chal_x_compl          -- inner (post-gets) in compl
├── ow_loop_tracked_lazy_query_freshness_indep       -- drop pre-loop steps
│   └── ow_loop_tracked_indep_RO_invariance_avg      -- averaged RO invariance
│       └── ow_loop_tracked_indep_sum_le_strong      -- HIT-case = 0 via strengthened IH
│           └── RO_setentry_neq_commutes_lazy_query_set_oracle_output
└── ow_loop_tracked_indep_sum_le_strong              -- the outer sum bound
```
