# IND-security of the hashed one-time pad — a report

*A game-hopping proof in the relational (pRHL) calculus, `GaudisCrypt/Lib/Enc/HashedOTP.lean`.*

---

## 1. What is proved, and why it is true

### The scheme

Fix a random oracle `H : input → output` and give `output` a commutative
group structure `+` (think bitwise XOR). The **hashed one-time pad**
encrypts a message `m : output` under a key `k : input` as

```
Enc(k, m) = H(k) + m.
```

This is the textbook "use a random oracle as a key-derivation function,
then one-time-pad the message" construction.

### The security claim (left-or-right indistinguishability)

An adversary `A` may query the oracle up to `q` times. We sample a secret
key `k`, hand `A` the ciphertext `c = H(k) + m_b` for one of two messages,
and `A` outputs a guess bit. The scheme is secure if `A` cannot tell the
`m₀`-world from the `m₁`-world. Formally (`enc_ind_secure`):

```
Pr[A guesses true | c = H(k)+m₀]  ≤  Pr[A guesses true | c = H(k)+m₁]  +  (q+1)/|input|.
```

By symmetry in `m₀, m₁` this is the two-sided bound
`|Pr₀ − Pr₁| ≤ (q+1)/|input|`.

### The intuition

`H(k)` is a uniformly random group element, and the **only** way `A` can
learn anything about it is to query the oracle at the key `k` itself.

* **If `A` never queries `k`:** then `H(k)` is, from `A`'s point of view, a
  fresh uniform pad, completely independent of everything `A` sees. So
  `c = H(k) + m_b` is a uniformly random group element *regardless of `b`*.
  The two worlds are then **identically distributed** — `A`'s guess cannot
  depend on `b`, and the two probabilities are exactly equal.

* **If `A` does query `k`:** all bets are off (it could read `H(k)`,
  recover `m_b`, and win). But `A` is just throwing `q` darts at a uniformly
  random target `k ∈ input`, and `c` leaks nothing about `k`, so its darts
  are independent of `k`: `Pr[A queries k] ≤ q/|input| ≤ (q+1)/|input|`.

The advantage is bounded by the probability of that second, "bad", event.
This is the classic **identical-until-bad** argument, with the bad event
being *"the adversary queried the key"*.

---

## 2. The proof as a sequence of games

The formal proof is a chain of game hops. Two ingredients recur and are
worth naming up front, because they are *reused verbatim* from the
one-wayness (OW) development in `GaudisCrypt/Lib/RO/OneWayness_GameHop/`:

* **the tracked oracle** `lazy_query_tracked`, a lazy random-oracle query
  that additionally flips a ghost flag `chal_x_queried_gh` whenever it is
  asked at the value stored in the register `ow_challenge_x`;
* **the up-to-bad invariant** `InvUB x y σ₁ σ₂` — "the flags of `σ₁,σ₂`
  agree, and on good runs `σ₁` equals `σ₂` with `RO[x]` overwritten to `y`".

We deliberately **store the key in `ow_challenge_x`** and use
`chal_x_queried_gh` as the "queried the key" flag, so the entire OW
up-to-bad machinery applies with no change.

The chain (each arrow is one or more lemmas in the file):

```
                        enc_game m_b
                            │  (1) preprogramming mini-hop
                            ▼
                        enc_game_pre m_b
            ┌───────────────┴───────────────┐
   (2a) OTP coupling + up-to-bad      (2b) bad-event bound
            │                                │  (3) drop preprogramming
            ▼                                ▼
   Pr₀ ≤ Pr₁ + Pr[bad]              enc_game_nopre  (lazy RO at the key)
                                             │  (4) reindex mask, defer key
                                             ▼
                                     guess_experiment (env_c …)
                                             │  (5) reuse OW's schema bound
                                             ▼
                                       ≤ (q+1)/|input|
```

### Hop (1): preprogramming — `enc_game_wp_eq_pre`

`enc_game` computes `H(k)` with a real `lazy_query`. On the freshly
initialised (empty) oracle, a lazy query at `k` is *definitionally* "sample
`hk ← uniform`, store `RO[k] := hk`, return `hk`". `enc_game_pre` makes
that explicit. The two have equal weakest-preconditions
(`enc_game_wp_eq_pre`), exposing the uniform sample `hk` that the coupling
in hop (2a) acts on. (The bridge lemma `lazy_query_on_totally_empty_RO`
doing this lives in the OW `Definitions`.)

### Hop (2a): the one-time-pad coupling — `enc_guess_le`

This is the heart of the proof and the place the **relational calculus**
earns its keep. We relate the `m₀`-game and the `m₁`-game directly,
*coupling their random choices*:

* the **key** `k` is coupled by the identity (both runs use the same `k`);
* the **mask** `hk` is coupled by the bijection `hk ↦ hk + (m₀ − m₁)`.

Under this coupling the *published ciphertexts coincide*:

```
   (m₀-run)  hk + m₀     =     (hk + m₀ − m₁) + m₁   (m₁-run),
```

so after publishing `c` the two runs differ **only** at the oracle entry
`RO[k]` — which is exactly `InvUB k hk`. The shared adversary loop then
preserves `InvUB` by the OW body coupling `body_relE`, and the guesses
agree as long as the flag never fires. Feeding this into the relational
up-to-bad rule (`relE.up_to_bad`) yields

```
Pr[m₀ : guess] ≤ Pr[m₁ : guess] + Pr[m₀ : adversary queried the key].
```

### Hop (2b)–(5): the bad-event bound — `enc_bad_bound`

We must show `Pr[adversary queries the key] ≤ (q+1)/|input|`. The
adversary's queries depend on `c`, which is correlated with nothing about
`k` — so this is a "uniform target hit by `q` independent darts" bound. We
discharge it by routing into the OW **guess-experiment** framework, in
three steps:

* **(3) drop the preprogramming** (`enc_pre_bad_eq_nopre`). Whether or not
  `RO[k]` was preprogrammed only matters once the adversary actually
  queries `k` — but that *is* the bad event. So the games are
  identical-until-bad, and their bad-event probabilities are *equal*
  (relational `relE.bad_eq`, again via `InvUB`). This replaces a 138-line
  mass-conservation argument in the original unary OW development.

* **(4) reindex and defer** (`enc_nopre_bad_le_gexp`). Reindex the mask
  `hk ↦ c = hk + m`: now `c` is a fresh uniform ciphertext, and `m`
  *disappears from the game entirely*. Commute `c`'s sampling before the
  key's. The result is literally a `guess_experiment` whose target is the
  uniform key, whose body is the OW loop body, and whose environment
  `env_c` just publishes a uniform ciphertext.

* **(5) reuse the OW bound** (`gexp_env_c_bound`). The guess-experiment
  framework already proves `≤ (n+1)/|target|` for any environment, via
  `game_1_correspondence` (which turned out to be *environment-generic*) and
  a generic deferred-sampling bound. We instantiate it.

Composing (2a) and (2b) gives `enc_ind_secure`.

---

## 3. The formalization substrate

### The probabilistic language

Programs are `Program s α := StateT s SubProbability`, where
`SubProbability` is the discrete sub-probability (Giry) monad. Semantics is
given by a weakest-precondition transformer
`Program.wp : (α × s → ENNReal) → s → ENNReal`, i.e. `wp p F σ` is the
expected value of the post `F` over `p`'s run from `σ`. A probability is a
`wp` of an indicator: `Pr[p : E] = p.wp (indicator E)`.

State is accessed through **lenses** (`Variable γ = Lens γ state`) with a
`disjoint` relation; disjointness gives the commutation facts that drive
all the bookkeeping. Here the relevant registers are `random_oracle_state`,
`ow_challenge_x` (the key), `chal_x_queried_gh` (the bad flag), and two new
ones for this file: `chal_c` (the published ciphertext) and `guess_var`
(the adversary's output bit).

### The relational calculus (pRHL)

The proof is written in the project's relational layer (`GaudisCrypt/Logic/PRHL/`).
Its judgments are

```
Program.rel  p q Pre Post  :=  ∀ F G, (∀ x y, Post x y → F x ≤ G y) →
                                  ∀ σ₁ σ₂, Pre σ₁ σ₂ → p.wp F σ₁ ≤ q.wp G σ₂
Program.relE p q Pre Post  :=  rel p q … ∧ rel q p …      (both directions)
```

This is a *coupling-free, wp-based* relational Hoare logic: a judgment is
defined by its elimination form, so the probability bridges (`relE.wp_eq`,
`relE.bad_eq`, `relE.up_to_bad`) are immediate and every proof rule is a
small consequence of the unary `wp` lemmas. The rules used here:

| rule | role in this proof |
|---|---|
| `relE.bind` | sequence two related fragments (the workhorse) |
| `relE.loop_n` | relate `n` synchronized loop iterations |
| `relE.uniform_bij` | couple two uniform samples along a bijection — the OTP step |
| `relE.get_get`, `set_set`, `self_lens_set` | atomic state ops |
| `relE.up_to_bad` | the Fundamental Lemma: `Pr[p:G] ≤ Pr[q:G] + Pr[p: bad∧G]` |
| `relE.bad_eq` | equal bad-event probabilities from a flag-agreeing post |

### What was inherited from one-wayness

The single biggest structural decision is that EncRO **reuses the OW
up-to-bad core verbatim** by aliasing registers. Concretely it imports and
applies, unchanged:

* `lazy_query_tracked`, `insRO`, `InvUB`, `invUB_of_good`, `get_insRO`;
* `body_relE` — the per-loop-iteration coupling preserving `InvUB`;
* the `guess_experiment` framework, `body_game_1`/`final_game_1`,
  `game_1_correspondence`, and the generic interim bound.

The only genuinely new probabilistic content in the whole file is the OTP
bijection coupling; everything else is plumbing or reuse.

---

## 4. Formalization structure (the lemma DAG)

The file is ~690 lines in five sections. Reading top to bottom:

**Setup.** `outputCommGroup` (the group on `output`, axiomatized like the
type's other instances), the registers `chal_c`/`guess_var`, their
disjointness axioms, and the two games `enc_game` / `enc_game_pre`.

**§ EncStage1 — the coupling (indistinguishability up to bad).**

```
enc_tail_relE        loop+read-guess preserves InvUB → encPost   (uses body_relE)
       └── enc_otp_tail_relE   the OTP coupling on the (uniform hk; …) tail
                  └── enc_game_pre_relE   peel the shared prefix → game-level relE
```
`enc_game_wp_eq_pre` (§ EncMiniHop) then transports to `enc_game`, and
`enc_guess_le_pre` / `enc_guess_le` (§ EncIndist) apply `relE.up_to_bad`.

**§ EncBad — the bad-event bound.**

```
enc_pre_bad_eq_nopre   drop RO[k] preprogramming        (relE.bad_eq, via enc_bad_invUB)
gexp_env_c_bound       guess-experiment ≤ (q+1)/|input| (reuse game_1_correspondence)
   helpers:  final_game_1_mono   the extra final query only sets the flag
             enc_tail_mono       dropping the final query lowers the bad prob
             enc_state_comm      the ciphertext register commutes
             sum_sum_div         pull both averaging factors out of a double sum
enc_nopre_bad_le_gexp  reindex + sum_comm + termwise   (the connector)
       └── enc_bad_bound   mini-hop ▸ (3) ▸ (4) ▸ (5)
```

**§ EncMain — the headline.** `enc_ind_secure = enc_guess_le ▸ enc_bad_bound`.

Hypotheses threaded throughout: the adversary `enc_adv` is confined away
from each bookkeeping register (`inRange …compl.range` for RO, the flag,
the key, the query-list) and is **lossless** (`wp 1 = 1`). The losslessness
is the one assumption beyond what the unary OW bad-bound needed; it is
demanded by the rectangular/up-to-bad phase and is assumed by the master
theorems anyway.

---

## 5. Selected technical details

### The OTP coupling, in code

The mask coupling is one application of `relE.uniform_bij` with
`Equiv.addRight (m₀ − m₁)`; the proof obligation is that the published
ciphertexts coincide, closed by `abel`:

```
hk₁ = hk₀ + (m₀ − m₁)   ⟹   hk₁ + m₁ = hk₀ + m₀.
```
After the two `set RO` / `set chal_c` writes, the relating states satisfy
`σ₁ = insRO k hk₀ σ₂` (they differ only at `RO[k]`), i.e. `InvUB k hk₀`
holds — established by `enc_bad_invUB` / the inline state algebra and fed to
`body_relE`.

### Identical-until-bad as an equality

`enc_pre_bad_eq_nopre` shows the preprogrammed and lazy games have *equal*
bad probabilities. The relational statement is a `relE` whose post says
"flags agree, and on good runs the guesses agree"; `relE.bad_eq` extracts
exactly the bad-event equality from the flag-agreement conjunct. This is
where the relational layer pays off most sharply: the original unary OW
proof needed a 138-line mass-conservation + `ENNReal`-cancellation argument
for the analogous step.

### Why the bad event reduces cleanly

The reindex `hk ↦ c = hk + m` is the formal embodiment of "`c` is a fresh
uniform pad independent of `k`": once reindexed, the message `m` does not
appear anywhere in the game, so the bad probability is *the same for every
`m`*, and the game is a plain `guess_experiment` against a uniform key.

### `ENNReal` pitfalls worth recording

* `Finset.sum_div` requires a `DivisionRing`; `ENNReal` is not one. The
  helper `sum_sum_div` instead pulls averaging factors out via
  `div_eq_mul_inv` + `Finset.sum_mul`, leaving the factor as
  `Nβ⁻¹ * Nα⁻¹` and *avoiding* the conditional product-inverse law
  `(Nα*Nβ)⁻¹ = Nα⁻¹*Nβ⁻¹` (which carries `≠0 / ≠⊤` side conditions in
  `ENNReal`).
* `oracle_loop_n_eq_loop_n` cannot be `rw`-ritten under a `∑` binder; the
  conversion is done inside the per-term `Finset.sum_le_sum`.
* The two sample orders (`k`-then-`hk` vs `c`-then-`k`) are reconciled by
  `Equiv.sum_comp (Equiv.addRight m)` (the reindex) followed by
  `Finset.sum_comm` (Fubini) — both at the `ENNReal`-sum level, where they
  are unconditional.

---

## 6. What this validates

EncRO is the first *new* theorem proved natively in the relational
calculus (everything before it was a migration of an existing unary proof).
The takeaway: a fresh cryptographic result was closed end-to-end with
essentially no new probabilistic infrastructure — the up-to-bad core, the
`InvUB` invariant, the `guess_experiment` framework, and
`game_1_correspondence` all transferred unchanged, and the only bespoke
content was a single bijection coupling plus mechanical sum bookkeeping.
That is the evidence that the calculus accelerates new work, not just
refactors.

## 7. Assumptions and scope

* `output` carries a `AddCommGroup` (axiomatized, like the opaque type's
  existing `Fintype`/`Inhabited` instances). Any concrete instantiation
  (e.g. `ZMod 2^n`) discharges it.
* The adversary is **lossless** and **confined** to non-bookkeeping
  registers (standard for game-based proofs; the confinement is what
  EasyCrypt gets for free from its module system).
* The bound is `(q+1)/|input|`, matching the OW bad-event bound (the
  challenger's own key computation is untracked, so only the adversary's
  `q` loop queries — plus the framework's `+1` slack — count).
* The whole file is `sorry`-free; the only `sorry`s in its dependency
  cone are the framework-level opaque-type instances in `GaudisCrypt/Lib/RO/Basic.lean`
  (`Countable state`, `Fintype output`, …), shared by every proof in the
  project.
