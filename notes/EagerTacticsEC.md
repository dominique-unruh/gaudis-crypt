# EasyCrypt's eager tactics: empirically observed conditions vs. our eager calculus

*2026-07-05. Ground truth captured from a live EasyCrypt r2026.06 (git g761aaf2), installed
locally for this purpose. Experiment scripts and full goal transcripts:
`~/easycrypt-eager-experiments/` (prelude + E1–E8, one `.log` per experiment).
EC sources incl. `theories/crypto/PROM.ec`: `~/.opam/ec/.opam-switch/sources/easycrypt/`.*

Our side of the comparison: `GaudisCrypt/Logic/EagerRhl.lean` (judgment + seq/while/conseq/
invariant rules), `GaudisCrypt/Logic/EagerProc.lean` (abstract-proc rule `eager_call`, call-site
rule `eagerR_call`), `GaudisCrypt/Lib/RO/FullEager.lean` (the PROM-mirror proof).

## How the data was obtained

```bash
export PATH=~/.local/bin:$PATH LD_LIBRARY_PATH=$HOME/.local/lib
eval $(opam env --switch=ec)
easycrypt cli          # sentence-per-line REPL; prints goal state after each step
```

with `pragma Goals:printall.` so every subgoal is displayed. Shared experiment prelude:

```
module V  = { var m : bool  var w : int }.                     (* globals *)
module Sw = { proc s() = { var c; c <$ dbool; V.m <- c; } }.   (* the sliding block S *)
module P1 = { proc f(z : int) : int = { V.w <- V.w + z; V.w <- V.w * 2; return V.w; } }.
module P2 = P1 (copy).
module type Or_t = { proc get(x : int) : bool }.
module Or : Or_t = { proc get(x : int) : bool = { return V.m; } }.
module type Dist(O : Or_t) = { proc run(z : int) : bool }.
```

The eager judgment is two-block: `eager [S1, c ~ c', S2 : P ==> Q]` meaning
`{P} S1; c ~ c'; S2 {Q}` — left runs the block *first*, right runs it *last*.
Our `eagerR S₁ S₂ P p q Q` is the same shape (p = eager side).

## Per-tactic observed subgoals

### `eager seq n1 n2 : s : R`  →  4 subgoals  (E1)

Split positions `n1`/`n2`, an *explicit middle block* `s`, middle relation `R`
(confirming that the load-bearing generality of our `eagerR_seq` — the free middle
block — is EC's design too). On
`eager [Sw.s();, P1.f ~ P2.f, Sw.s(); : ={V.m,V.w,arg} ==> ={res,V.m,V.w}]`
after `eager proc`, `eager seq 1 1 : Sw.s(); : (={V.m, V.w, z})` yields:

1. `eager [S1, c1 ~ d1, s : P ==> R]` — first halves, middle block as exit;
2. `eager [s, c2 ~ d2, S2 : R ==> Q]` — second halves, middle block as entry;
3. self-equivalence of the **bare first piece** (programs in sync), with an
   exists-strengthened pre:
   ```
   pre  = (={V.m,V.w,z}) /\ exists m, V.m{m} = V.m{2} /\ V.w{m} = V.w{2} /\ z{m} = z{2}
   (1)  V.w <- V.w + z
   post = ={V.m,V.w,z}                                   (i.e. R)
   ```
4. self-equivalence of the bare second piece: `pre = R`, `post = Q`(projected).

So: **2 eager goals + 2 framing self-equivalences** — the exact decomposition of our
`eagerR_seq_inv`, with one granularity difference: EC frames the *pieces alone*; we frame
the *composites* (piece + block). Same mathematical content (the eager halves already tie
pieces to blocks); no change needed.

### `eager if`  →  4 subgoals  (E2)

1. guard agreement: `pre ⇒ e₁ = e₂`;
2. **one-sided Hoare** guard stability under the sliding prefix, fresh `b : bool`:
   `hoare [ prefix {&1} : pre ∧ e = b ==> e = b ]`;
3. then-case: sync'd equiv with `pre ∧ e = true`;
4. else-case: sync'd equiv with `pre ∧ e = false`.

We have not built `eagerR_if` yet; this is its blueprint. The notable condition is (2):
guard-value stability is *one-sided Hoare*, not relational.

### `eager while I`  →  6 subgoals  (E3)

Guard agreement; body-with-block goal (pre `I ∧ e`); the same one-sided guard-stability
Hoare; two framing self-equivalences (one with the `exists m` strengthening); exit case
(pre `I ∧ ¬e`). Matches our `eagerR_while_inv` (6-premise form).

### `eager proc` (concrete)  →  1 subgoal  (E4)

Both bodies inlined into the two-block *statement* judgment: `S1` prepended on the left,
`S2` appended on the right, `result <- ret-expr` made explicit. This is exactly our
`procWrap` unfolding (`procWrap_block_in/out`).

### `eager proc I` (abstract adversary)  →  6 subgoals  (E5) — **the glob rule**

On `eager [Sw.s();, D(Or).run ~ D(Or).run, Sw.s(); : ={glob D, V.m, arg} ==> ={res, glob D, V.m}]`
with `declare module D <: Dist {-V}`, the tactic `eager proc (={V.m})` yields, verbatim:

```
Goal 1:  forall &1 &2,  PRE  =>  arg{1} = arg{2} /\ (glob D){1} = (glob D){2} /\ I
Goal 2:  forall &1 &2,  res{1} = res{2} /\ (glob D){1} = (glob D){2} /\ I  =>  POST
Goal 3:  equiv (sync): pre = I;  (1) Sw.s();  post = I          (* block preserves I  *)
Goal 4:  eager[ Sw.s();, Or.get ~ Or.get, Sw.s(); :
                arg{1} = arg{2} /\ I ==> res{1} = res{2} /\ I ]  (* per oracle          *)
Goal 5:  equiv: pre = I /\ arg= /\ I;  Or.get ~ Or.get;  post = res= /\ I   (* left copy  *)
Goal 6:  equiv: pre = arg= /\ I;       Or.get ~ Or.get;  post = res= /\ I   (* right copy *)
```

(with `I = V.m{1} = V.m{2}`). Three glob facts, confirmed by targeted probes:

- **`={glob D}` never appears in the per-oracle goals.** It is threaded structurally by
  the rule — justified by module typing (D writes only its own globals and calls the
  oracles). Semantically this is precisely our footprint-disjointness hypothesis `hdisj`
  plus the `fvP` machinery.
- **The precondition must imply `={glob D}`** (E5b): stating the lemma with pre `={V.m, arg}`
  still produces the same 6 goals, but Goal 1 becomes
  `={V.m,arg} => arg= ∧ ={glob D} ∧ I` — unprovable. The rule hard-codes `={glob D}` in
  the entry/exit consequence goals; weakening the *post* is fine.
- **The invariant may not mention `glob D`** (E5c): `eager proc (={V.m, glob D})` is
  rejected outright — `The module D can write D (add restriction D to D, or D to D)`.
  So EC's `I` is oracle/block-state-only; adversary glob equality is *never* carried
  through `I`.

Our `eager_D_glob` (`={glob A} ==> ={res, glob A}` with an oracle-state invariant) is a
precise match for PROM's `eager_D`
(`eager proc (={FRO.m}) => //; try by sim` in `theories/crypto/PROM.ec:695`).

### `eager call lem`  →  1 subgoal  (E6)

On the equiv goal `Sw.s(); b <@ D(Or).run(z) ~ b <@ D(Or).run(z); Sw.s()`,
`eager call E5` leaves exactly one goal: a sync'd *empty-program* consequence
(current pre ⇒ the lemma's pre), argument/result equalities handled by unification
against the call instruction. Two further forms exist:

- inline cut `eager call (: P ==> Q)` (E7) → 2 goals: the cut eager judgment itself +
  the same consequence goal (used in `SDist.ec:542`);
- bare invariant `eager call (: I)` (used in `examples/PRG.ec:343`).

### Non-members  (E8)

`eager rnd` and `eager swap` are parse errors. The family is exactly
**{judgment, seq, if, while, proc, proc I, call}**; ordinary pRHL tactics apply inside
eager goals (PROM's per-oracle proofs use `rnd`, `swap`, `transitivity`, `iter` freely).

## Mapping to our Lean rules

| EasyCrypt | Ours | Status |
|---|---|---|
| `eager [S1, c ~ c', S2 : P ==> Q]` | `ProgramDenotation.eagerR S₁ S₂ P p q Q` | match (two-block) |
| `eager seq` (2 eager + 2 piece self-equivs) | `eagerR_seq` (Eq) / `eagerR_seq_inv` | match; we frame composites, EC frames pieces |
| `eager if` (guard-eq + 1-sided Hoare stability + 2 branches) | — | **missing**; blueprint above |
| `eager while I` (6 goals) | `eagerR_while` (Eq) / `eagerR_while_inv` | match |
| `eager proc` (concrete) | `procWrap` unfolding (`EagerProc.lean`) | match |
| `eager proc I` (abstract; glob discipline above) | `eager_call` (+`eager_call_inv`); headline shape `eager_D_glob` | match; EC's module typing = our `hdisj`/footprint |
| `eager call` (1 consequence goal) | `eagerR_call` (+`eagerR_call_inv`) | match **except** our `hp`/`hx` side conditions — see below |

**The one real divergence.** Our `eagerR_call` demands swap-stability of the call-site
argument read and result write against the block
(`hp : transferBy (zoom globalL S) (get p) (get p)`, `hx : ∀ ret, transferBy … (set x ret) …`).
EC has *no* such side conditions — in EC, arguments/results are **local** variables and
blocks can only touch **globals**, so the commutation is free by construction. Our `hp`/`hx`
are the shallow-embedding rendering of that locals/globals separation. Refinement: a derived
rule for setters/getters built via `intoParams`/`intoVars` (which factor through
`ProcedureState.localL`, disjoint from `globalL`) that discharges `hp`/`hx` once and for
all, restoring EC's zero-side-condition call sites.

## Action items

1. Derived `eagerR_call` variant for local-lens argument/result plumbing
   (auto-discharged `hp`/`hx`).
2. `eagerR_if`, following E2's 4-goal shape — in particular the one-sided
   guard-stability condition (needs a one-sided Hoare/wp judgment or the `prhl2`
   diagonal to express `{P ∧ e=b} S {e=b}`).
