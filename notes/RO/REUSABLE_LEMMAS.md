# Reusable lemmas in the framework

This document catalogues the framework-level lemmas extracted from the OW /
CR / QueryHit proofs and intended for reuse by future random-oracle-style
cryptographic proofs in this codebase.

The lemmas live in:

- `PlonkLean/ProgramRange.lean` — generic `wp` and `inRange` building
  blocks (no random-oracle content).
- `PlonkLean/RO/` — random-oracle-specific framework, split into:
  - `PlonkLean/RO/Basic.lean` — RO axioms, primitives (`lazy_query`,
    `random_oracle_query`, `lazy_init`, `random_oracle_init`, `convert`),
    state-variable axioms (`oracle_input`, `oracle_output`, `want_more`,
    `adversary_result`), and `lazy_init_convert_eq_random_oracle_init` / `lazy_query_conv_eq_conv_random_oracle` / `lazy_query_convert_eq_convert_random_oracle_query`.
  - `PlonkLean/RO/Transfer.lean` — generic `Program.transfer` framework,
    closure laws (including `transfer_while_loop`), convert absorption,
    and transfer shortcuts.
  - `PlonkLean/RO/OracleLoop.lean` — oracle loop primitives
    (`oracle_step`, `oracle_loop_n`, `oracle_loop`) and the
    indicator-step lemmas.
  - `PlonkLean/RO/ROEquiv.lean` — lazy = eager equivalence for the
    unbounded `oracle_loop` (`adv_conv_eq_conv_adv`,
    `Program.transfer_oracle_loop`,
    `oracle_loop_lazy_convert_eq_random_oracle_loop`,
    `oracle_loop_wp_lazy_eq_random_oracle`, marginal/compl/glob variants).

`PlonkLean/RO.lean` is a barrel that re-exports all four; importing it
gives access to everything.

Each entry below gives the lemma name, location, signature, and a one-line
summary of the pattern it captures. References to existing call sites
appear where useful — see those for concrete examples of how to apply the
lemma.

---

## 1. Generic oracle-loop primitives

The shared "adversary + oracle call" loop shape used by every game in this
codebase. Game files alias these (`cr_loop_body := oracle_step cr_adv`,
`ow_loop := oracle_loop_n ow_adv`, etc.).

### `oracle_step`

`PlonkLean/RO/OracleLoop.lean:161`

```lean
noncomputable def oracle_step (adv : Program state Unit)
    (oracle : input → Program state output) : Program state Unit := do
  adv
  Program.set oracle_output (← oracle (← Program.get oracle_input))
```

One round of an "adversary writes `oracle_input`, then we query the
oracle, store the result in `oracle_output`" loop body. Parameterised
over the oracle so it can be instantiated to `lazy_query` or
`random_oracle_query`.

### `oracle_loop_n`

`PlonkLean/RO/OracleLoop.lean:167`

```lean
noncomputable def oracle_loop_n (adv : Program state Unit) :
    ℕ → (input → Program state output) → Program state Unit
  | 0,     _      => pure ()
  | n + 1, oracle => do
      oracle_step adv oracle
      oracle_loop_n adv n oracle
```

Run `oracle_step adv` for `q` rounds.

### `Program.transfer_oracle_step`

`PlonkLean/RO/OracleLoop.lean:176`

```lean
lemma Program.transfer_oracle_step
    {adv : Program state Unit}
    (h_adv : adv.inRange random_oracle_state.compl.range) :
    Program.transfer (oracle_step adv lazy_query)
                     (oracle_step adv random_oracle_query)
```

Lazy/eager transfer of one body iteration. Reduces game-specific
`transfer_*_loop_body` lemmas to one-liners.

### `Program.transfer_oracle_loop_n`

`PlonkLean/RO/OracleLoop.lean:195`

```lean
lemma Program.transfer_oracle_loop_n
    {adv : Program state Unit}
    (h_adv : adv.inRange random_oracle_state.compl.range) (q : ℕ) :
    Program.transfer (oracle_loop_n adv q lazy_query)
                     (oracle_loop_n adv q random_oracle_query)
```

Same, lifted to `q` iterations. Reduces game-specific `transfer_*_loop`.

### `oracle_step_inRange_compl`

`PlonkLean/RO/OracleLoop.lean:213`

```lean
lemma oracle_step_inRange_compl {γ : Type} (L : Lens γ state)
    [disjoint random_oracle_state L]
    [disjoint oracle_input L]
    [disjoint oracle_output L]
    {adv : Program state Unit}
    (h_adv : adv.inRange L.compl.range) :
    (oracle_step adv lazy_query).inRange L.compl.range
```

The body preserves any lens `L` that's disjoint from the loop's scratch
variables, given the adversary preserves it.

### `oracle_loop_n_inRange_compl`

`PlonkLean/RO/OracleLoop.lean:232`

```lean
lemma oracle_loop_n_inRange_compl {γ : Type} (L : Lens γ state)
    [disjoint random_oracle_state L]
    [disjoint oracle_input L]
    [disjoint oracle_output L]
    {adv : Program state Unit}
    (h_adv : adv.inRange L.compl.range) (q : ℕ) :
    (oracle_loop_n adv q lazy_query).inRange L.compl.range
```

Same, lifted to the loop.

---

## 2. Loop accumulation and per-query indicator bumps

### `oracle_loop_n_wp_linear_bound`

`PlonkLean/RO/OracleLoop.lean:253`

```lean
lemma oracle_loop_n_wp_linear_bound
    {adv : Program state Unit}
    {f : state → ENNReal} {c : ENNReal}
    (h_body : ∀ σ, (oracle_step adv lazy_query).wp
                     (fun yσ : Unit × state => f yσ.2) σ ≤ f σ + c)
    (q : ℕ) (σ : state) :
    (oracle_loop_n adv q lazy_query).wp
        (fun yσ : Unit × state => f yσ.2) σ ≤ f σ + (q : ENNReal) * c
```

**Linear loop accumulation.** If one body iteration bumps the wp of `f`
by at most constant `c`, then `q` iterations bump it by at most `q*c`.
Captures the standard induction-on-`q` skeleton used for both
query-budget bounds (CR `RO_size` with `c = 1`) and probability bounds
(OW `useful_preimage` with `c = 1/|output|`).

### `lazy_query_wp_step`

`PlonkLean/RO/OracleLoop.lean:301`

```lean
lemma lazy_query_wp_step
    (f : state → ENNReal) (bad : input → output → state → ENNReal)
    (h_bound : ∀ x σ y, random_oracle_state.get σ x = none →
        f (random_oracle_state.set
              (fun x' => if x' = x then some y else random_oracle_state.get σ x') σ)
        ≤ f σ + bad x y σ)
    (x : input) (σ : state) :
    (lazy_query x).wp (fun yσ : output × state => f yσ.2) σ
    ≤ f σ + (∑ y : output, bad x y σ) / Fintype.card output
```

**Per-query indicator bump (generic).** If on every cache-miss the new
fresh sample `y` at `x` bumps `f` by at most `bad x y σ`, then one
`lazy_query x` bumps the wp of `f` by at most the integrated badness
`(∑ y, bad x y σ) / |output|`. Cache-hit case is automatic. Captures
`lazy_query_collision_step` (CR, `bad = inducing_set`),
`lazy_query_RO_size_step` (CR, `bad = 1`), and
`lazy_query_useful_preimage_step` (OW, `bad = challenge match`).

### `oracle_step_wp_indicator_bump`

`PlonkLean/RO/OracleLoop.lean:348`

```lean
lemma oracle_step_wp_indicator_bump
    {adv : Program state Unit}
    {f : state → ENNReal} (c : state → ENNReal)
    (h_adv_preserves_f : ∀ σ, adv.wp (fun yσ : Unit × state => f yσ.2) σ ≤ f σ)
    (h_adv_preserves_c : ∀ σ, adv.wp (fun yσ : Unit × state => c yσ.2) σ ≤ c σ)
    (h_set_oo : ∀ y σ, f (oracle_output.set y σ) = f σ)
    (h_lazy_query : ∀ x σ,
        (lazy_query x).wp (fun yσ : output × state => f yσ.2) σ ≤ f σ + c σ)
    (σ : state) :
    (oracle_step adv lazy_query).wp (fun yσ : Unit × state => f yσ.2) σ
    ≤ f σ + c σ
```

**Per-body-step indicator bump (generic).** One `oracle_step` bumps `f`
by at most `c σ`, given: adv preserves `f`, adv preserves `c`, writes
to `oracle_output` leave `f` unchanged, and one `lazy_query` bumps `f`
by at most `c σ`. The "Layer A + adv-preservation" pattern.

### `oracle_step_wp_indicator_bump_const`

`PlonkLean/RO/OracleLoop.lean:388`

```lean
lemma oracle_step_wp_indicator_bump_const
    {adv : Program state Unit}
    {f : state → ENNReal} (c : ENNReal)
    (h_adv_preserves : ∀ σ, adv.wp (fun yσ : Unit × state => f yσ.2) σ ≤ f σ)
    (h_set_oo : ∀ y σ, f (oracle_output.set y σ) = f σ)
    (h_lazy_query : ∀ x σ,
        (lazy_query x).wp (fun yσ : output × state => f yσ.2) σ ≤ f σ + c)
    (σ : state) :
    (oracle_step adv lazy_query).wp (fun yσ : Unit × state => f yσ.2) σ
    ≤ f σ + c
```

Constant-`c` specialisation of the previous lemma. The adversary
trivially preserves a constant via `Program.wp_const_le`.

---

## 3. lazy_query + RO key reasoning

### `lazy_query_then_set_oracle_output_inRange_compl`

`PlonkLean/RO/Transfer.lean:246`

```lean
lemma lazy_query_then_set_oracle_output_inRange_compl
    {γ : Type} (L : Lens γ state)
    [disjoint random_oracle_state L] [disjoint oracle_output L]
    (inp : input) :
    (lazy_query inp >>= fun y => Program.set oracle_output y).inRange
        L.compl.range
```

The compound "query + cache the result in `oracle_output`" stays in
`L.compl.range` for any `L` disjoint from `random_oracle_state` and
`oracle_output`.

### `lazy_query_set_oracle_output_preserves_RO_at_other_key`

`PlonkLean/RO/OracleLoop.lean:20`

```lean
lemma lazy_query_set_oracle_output_preserves_RO_at_other_key
    (inp k : input) (h_neq : inp ≠ k) (σ : state) (F : Unit × state → ENNReal) :
    (lazy_query inp >>= fun y_lq => Program.set oracle_output y_lq).wp F σ
    = (lazy_query inp >>= fun y_lq => Program.set oracle_output y_lq).wp
        (fun aσ_lq =>
          if random_oracle_state.get aσ_lq.2 k = random_oracle_state.get σ k
          then F aσ_lq else 0) σ
```

A query at `inp ≠ k` doesn't change `RO[k]`. Wp-level statement that
strengthens any post `F` with a "RO at k unchanged" check at no cost.

### `RO_setentry_neq_commutes_lazy_query_set_oracle_output`

`PlonkLean/RO/OracleLoop.lean:53`

```lean
lemma RO_setentry_neq_commutes_lazy_query_set_oracle_output
    (inp x : input) (h_neq : inp ≠ x) (y : output) (σ : state)
    (F : Unit × state → ENNReal) : ...
```

Writes to `RO[x]` commute past a `lazy_query inp >>= set oracle_output`
when `inp ≠ x`. Mechanical core of "deferred sampling" / averaged
invariance arguments for indistinct-key reasoning.

---

## 4. wp building blocks

### `Program.wp_finset_sum`

`PlonkLean/WeakestPreconditions.lean:226`

```lean
theorem Program.wp_finset_sum {s α β : Type} [Fintype β]
    (p : Program s α) (F : β → α × s → ENNReal) (σ : s) :
    p.wp (fun aσ => ∑ b : β, F b aσ) σ = ∑ b : β, p.wp (F b) σ
```

Linearity of `wp` over a finite sum of postconditions. Appears in any
argument that bounds an event by summing over a finite set of values
(challenge values, adversary outcomes, etc.).

### `Program.wp_value_eq_marginal_expected`

`PlonkLean/ProgramRange.lean:272`

```lean
lemma Program.wp_value_eq_marginal_expected {s α : Type}
    (p : Program s α) (G : α → ENNReal) (σ : s) :
    p.wp (fun aσ : α × s => G aσ.1) σ
      = (p σ >>= fun aσ : α × s => (pure aσ.1 : SubProbability α)).expected G
```

`wp` of a value-only post equals the expected value of `G` under the
value-marginal distribution.

### `Program.wp_eq_of_marginal_eq`

`PlonkLean/ProgramRange.lean:288`

```lean
lemma Program.wp_eq_of_marginal_eq {s α : Type}
    {p q : Program s α}
    (h_marg : ∀ σ, (p σ >>= fun aσ => (pure aσ.1 : SubProbability α))
                 = (q σ >>= fun aσ => (pure aσ.1 : SubProbability α)))
    (G : α → ENNReal) (σ : s) :
    p.wp (fun aσ => G aσ.1) σ = q.wp (fun aσ => G aσ.1) σ
```

**SubProb-marginal equality lifts to wp-equality for value-only posts.**
Bridges a SubProb-level transfer theorem (e.g. `cr_transfer`,
`ow_transfer`) to a wp-level statement. Reduces `cr_transfer_wp_of_bit`,
`ow_transfer_wp_of_bit` to one-liners.

### `Program.bind_uniform_comm`

`PlonkLean/ProgramRange.lean:914`

```lean
theorem Program.bind_uniform_comm {s α β a : Type} [Fintype α] [Nonempty α]
    (p : Program s β) (k : α → Program s a) :
    (p >>= fun _ => (Program.uniform : Program s α) >>= k)
    = (Program.uniform >>= fun y => p >>= fun _ => k y)
```

**`Program.uniform` commutes with any program** — `uniform` is
state-preserving and produces an independent sample, so it can be
hoisted out of a preceding bind. The result of the preceding program is
discarded.

### `Program.wp_shift_input`

`PlonkLean/ProgramRange.lean:299`

```lean
lemma Program.wp_shift_input {s a : Type} {p : Program s a} {R : LensRange s}
    (hp : p.inRange R) {f : s → s} (hf : f ∈ Rᶜ.updates)
    (F : a × s → ENNReal) (σ : s) :
    p.wp F (f σ) = p.wp (fun (xs : a × s) => F (xs.1, f xs.2)) σ
```

Shifting the input state by `f ∈ Rᶜ.updates` is equivalent to
post-composing `f` on the state coordinate of the postcondition.
Foundational tool used by `wp_strengthen_lens_preserved` and
`wp_set_disjoint_no_op`.

### `Program.wp_strengthen_lens_preserved`

`PlonkLean/ProgramRange.lean:318`

```lean
lemma Program.wp_strengthen_lens_preserved {s α γ : Type} [DecidableEq γ]
    (L : Lens γ s) {p : Program s α} (h_inRange : p.inRange L.compl.range)
    (F : α × s → ENNReal) (σ : s) :
    p.wp F σ
      = p.wp (fun aσ' : α × s => if L.get aσ'.2 = L.get σ then F aσ' else 0) σ
```

If `p` only modifies the complement of `L`, the post can be strengthened
with a `L`-preserved check at no cost.

### `Program.wp_set_disjoint_no_op`

`PlonkLean/ProgramRange.lean:349`

```lean
lemma Program.wp_set_disjoint_no_op {s γ : Type} [DecidableEq γ] {L : Lens γ s}
    {α : Type} {rest : Program s α} (h_rest : rest.inRange L.compl.range)
    (v : γ) (F : α × s → ENNReal)
    (h_F : ∀ aσ : α × s, F (aσ.1, L.set v aσ.2) = F aσ)
    (σ : s) :
    (Program.set L v >>= fun _ => rest).wp F σ = rest.wp F σ
```

**Dead write.** Prepending `Program.set L v` to a program in
`L.compl.range` is a no-op for any post that ignores `L`. Useful for
removing bookkeeping writes that downstream code doesn't read.

---

## 5. Conditional set / tracking variable patterns

### `Program.wp_conditional_set_disjoint_no_op`

`PlonkLean/ProgramRange.lean:375`

```lean
lemma Program.wp_conditional_set_disjoint_no_op {s γ : Type} [DecidableEq γ]
    {L : Lens γ s} {α : Type} (cond : Prop) [Decidable cond] (v : γ)
    {rest : Program s α} (h_rest : rest.inRange L.compl.range)
    (F : α × s → ENNReal)
    (h_F : ∀ aσ : α × s, F (aσ.1, L.set v aσ.2) = F aσ)
    (σ : s) :
    ((if cond then Program.set L v else pure ()) >>= fun _ => rest).wp F σ
    = rest.wp F σ
```

**Conditional dead write.** Wp-level core of the tracking-variable
pattern. Any time you conditionally write a flag, the rest of the
program doesn't see it, so the write is invisible to a post that
doesn't read it either.

### `Program.wp_get_then_conditional_set_disjoint_no_op`

`PlonkLean/ProgramRange.lean:393`

```lean
lemma Program.wp_get_then_conditional_set_disjoint_no_op
    {s γ δ : Type} [DecidableEq γ] {L_get : Lens δ s} {L_set : Lens γ s}
    {α : Type} (pred : δ → Prop) [DecidablePred pred] (v : γ)
    {rest : Program s α} (h_rest : rest.inRange L_set.compl.range)
    (F : α × s → ENNReal)
    (h_F : ∀ aσ : α × s, F (aσ.1, L_set.set v aσ.2) = F aσ)
    (σ : s) :
    (Program.get L_get >>= fun cx =>
        (if pred cx then Program.set L_set v else pure ())
          >>= fun _ => rest).wp F σ
    = rest.wp F σ
```

"Branch on the secret/challenge, optionally update a tracking flag,
continue." Exact shape of the tracking-variable bind block in
`QueryHit.lean`.

---

## 6. Multi-lens preservation

### `Program.wp_le_of_factors`

`PlonkLean/ProgramRange.lean:411`

```lean
lemma Program.wp_le_of_factors {s α γ : Type} (L : Lens γ s)
    {prog : Program s α} (h_inRange : prog.inRange L.compl.range)
    {P : s → ENNReal}
    (h_factors : ∀ σ σ', L.get σ' = L.get σ → P σ' = P σ)
    (σ : s) :
    prog.wp (fun xs : α × s => P xs.2) σ ≤ P σ
```

If `prog` modifies only the complement of `L` and `P` factors through
`L.get`, then `prog.wp(P ∘ snd) σ ≤ P σ`. Single-lens version.

### `Program.wp_le_of_factors_two` / `Program.wp_le_of_factors_three`

`PlonkLean/ProgramRange.lean:441` / `:466`

Multi-lens versions: `P` factors through `(L₁.get, L₂.get)` (resp.
through three lenses) and `prog` preserves each, so
`prog.wp(P ∘ snd) σ ≤ P σ`. Used by `ow_adv_wp_useful_preimage` (3
lenses). Reusable for any indicator with multi-lens factoring.

---

## 7. inRange shortcuts

### `Program.set_inRange_compl_of_disjoint`

`PlonkLean/ProgramRange.lean:208`

```lean
lemma Program.set_inRange_compl_of_disjoint
    {s α β : Type} (v : Lens α s) (L : Lens β s) [disjoint v L] (x : α) :
    (Program.set v x).inRange L.compl.range
```

One-liner replacement for
`inRange_mono (inRange_set _ _) (Lens.range_le_compl_of_disjoint v L)`.

### `Program.get_inRange_compl_of_disjoint`

`PlonkLean/ProgramRange.lean:217`

```lean
lemma Program.get_inRange_compl_of_disjoint
    {s α β : Type} (v : Lens α s) (L : Lens β s) [disjoint v L] :
    (Program.get v).inRange L.compl.range
```

Same, for `Program.get`.

---

## 8. Transfer shortcuts

These shortcut the common "this primitive trivially transfers to
itself" cases in `transfer_*_experiment` chains.

### `Program.transfer_set_of_disjoint_ro`

`PlonkLean/RO/Transfer.lean:110`

```lean
lemma Program.transfer_set_of_disjoint_ro {α : Type}
    (v : Lens α state) [disjoint v random_oracle_state] (x : α) :
    Program.transfer (Program.set v x) (Program.set v x)
```

### `Program.transfer_get_of_disjoint_ro`

`PlonkLean/RO/Transfer.lean:116`

```lean
lemma Program.transfer_get_of_disjoint_ro {α : Type} [Countable α]
    (v : Lens α state) [disjoint v random_oracle_state] :
    Program.transfer (Program.get v) (Program.get v)
```

### `Program.transfer_uniform`

`PlonkLean/RO/Transfer.lean:122`

```lean
lemma Program.transfer_uniform {α : Type} [Countable α] [Fintype α] [Nonempty α] :
    Program.transfer (Program.uniform : Program state α) Program.uniform
```

---

## 9. Convert absorption

### `convert_random_oracle_init`

`PlonkLean/RO/Transfer.lean:23`

```lean
lemma convert_random_oracle_init :
    (convert >>= fun _ => random_oracle_init) = random_oracle_init
```

A fresh uniform sample overwrites any prior RO content — so `convert`
followed immediately by `random_oracle_init` is just
`random_oracle_init`.

### `convert_bind_random_oracle_init_bind`

`PlonkLean/RO/Transfer.lean:48`

```lean
lemma convert_bind_random_oracle_init_bind {α : Type} (rest : Program state α) :
    (convert >>= fun _ : Unit =>
      random_oracle_init >>= fun _ : Unit => rest)
    = random_oracle_init >>= fun _ : Unit => rest
```

Absorb preceding `convert` past any program that *starts* with
`random_oracle_init`. Reduces `convert_*_experiment_eager` lemmas to
one-liners.

---

## 10. Transfer framework (background)

These are the existing framework primitives; the new pieces above build
on them.

- `Program.transfer` (`RO/Transfer.lean:62`): the relation
  `(p >>= a => convert >>= pure a) = (convert >>= q)`.
- `Program.transfer_refl_of_inRange_compl` (`RO/Transfer.lean:67`):
  RO-disjoint programs transfer to themselves.
- `Program.transfer_of_inRange_disjoint` (`RO/Transfer.lean:99`):
  programs in `v.range` (for `v` disjoint from `random_oracle_state`)
  transfer to themselves.
- `Program.transfer_bind` (`RO/Transfer.lean:128`): bind closure.
- `Program.transfer_pure` (`RO/Transfer.lean:150`): pure transfers to pure.
- `Program.transfer_lazy_init` (`RO/Transfer.lean:157`): `lazy_init` ↦
  `random_oracle_init`.
- `Program.transfer_lazy_query` (`RO/Transfer.lean:172`): `lazy_query x` ↦
  `random_oracle_query x`.
- `Program.transfer_wp_value` (`RO/Transfer.lean:187`): transfer at the wp
  level, for value-only posts (`G : α → ENNReal`).
- `Program.transfer_value_marginal` (`RO/Transfer.lean:218`): SubProb-level
  marginal statement of transfer.

---

## Patterns *not* extracted as code

A few patterns are worth knowing but don't generalise cleanly into a
single reusable lemma. They appear in similar form in any wp-based
cryptographic argument:

- **Tracking variable pattern.** When a property of an adversary's
  execution can't be naturally expressed as a state predicate (e.g.,
  "did adv query this particular value at some point"), introduce an
  auxiliary state variable disjoint from everything else, modify the
  experiment to write to it from the appropriate vantage point, and
  prove an equivalence with the original experiment for posts that
  ignore the tracking variable. See `QueryHit.lean` for the OW example.

- **Strengthened sum lemma over a uniform challenge.** For bounds of
  the form "for uniform `x ∈ X`, adv's advantage is at most `b`," the
  wp-level statement is `∑ x, loop_q.wp F_x (chal.set x σ) ≤ k`. The
  inductive proof uses `wp_shift_input`, `wp_finset_sum`,
  `wp_strengthen_lens_preserved`, and case-splits on whether the
  current iteration "hits" the relevant condition.

- **Averaged invariance + freshness pair.** For arguments where a
  uniform oracle response is sampled and then averaged over, factor
  the proof as: (1) an *averaged invariance* lemma showing that the
  loop's wp is invariant under averaging over the relevant uniform
  value, and (2) a *freshness* lemma using (1) plus disjointness to
  absorb the pre-loop sampling step into the loop. Each game needs its
  own pair, but the proof technique transfers (induction on `q` with
  HIT/MISS case-split using
  `RO_setentry_neq_commutes_lazy_query_set_oracle_output`).

- **Chal_x preservation through a read-but-not-write loop.** When a
  loop body reads but doesn't write a lens, decompose the body so that
  reads get captured into local bindings, leaving a write-only remainder
  that *is* in `L.compl.range`. Then `wp_strengthen` applies in two
  pieces. See `ow_loop_tracked_preserves_chal_x_wp` for the OW example.

---

## Quick reference: what to grab when proving X

| Problem | Use |
|---|---|
| "this program preserves lens L" (set/get) | `Program.set_inRange_compl_of_disjoint`, `Program.get_inRange_compl_of_disjoint` |
| "this loop preserves lens L" | `oracle_loop_n_inRange_compl L` |
| "this loop transfers lazy ↔ eager" | `Program.transfer_oracle_loop_n` |
| "each query bumps RO_size / collision / preimage by ≤ c" | `lazy_query_wp_step` |
| "each body iteration bumps my indicator by ≤ c" | `oracle_step_wp_indicator_bump` (state-dep), `_const` (constant) |
| "q iterations bump my indicator by ≤ q·c" | `oracle_loop_n_wp_linear_bound` |
| "this indicator factors through 2 / 3 lenses" | `Program.wp_le_of_factors_two/_three` |
| "this conditional set is a no-op for posts that ignore the flag" | `Program.wp_conditional_set_disjoint_no_op` |
| "marginal equality at SubProb gives wp equality" | `Program.wp_eq_of_marginal_eq` |
| "absorb `convert` into an eager experiment" | `convert_bind_random_oracle_init_bind` |
| "set/get of an RO-disjoint variable transfers to itself" | `Program.transfer_set_of_disjoint_ro`, `Program.transfer_get_of_disjoint_ro` |
| "uniform transfers to itself" | `Program.transfer_uniform` |
