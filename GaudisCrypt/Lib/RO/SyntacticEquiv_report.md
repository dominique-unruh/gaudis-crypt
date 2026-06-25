# Lazy = Eager Random Oracle for *Syntactic* Adversaries — a walkthrough

**File:** `GaudisCrypt/Lib/RO/SyntacticEquiv.lean`
**Goal:** subtask 3 of `CLAUDE.md` — for an *arbitrary* adversary `A` written in
the imperative probabilistic syntax (`StmtWithHoles`), prove that running `A`
against a **lazy** random oracle is equivalent to running it against an
**eager** one. Two flavours of equivalence:

1. `Program.transfer_instantiate` — a *transfer* (equational) statement.
2. `prhl_instantiate` — a *relational/coupling* statement (invariant preservation).

Both are **proved, with no `sorry` of our own** (only the pre-existing RO
scaffolding placeholders in `Basic.lean` remain).

---

## 1. The setup, intuitively

A **random oracle** is a random function `input → output` the adversary queries.
Two standard ways to implement it:

* **Lazy** (`lazy_query`): begin with an *empty* table. On a query, if the input
  is already cached, return the cached value; otherwise sample a fresh random
  output, **store it**, and return it. (Sampling happens *on demand*.)
* **Eager** (`random_oracle_query`): at the very start, sample the *entire*
  function `input → output` and store it. On a query, just *read* the table.
  (All sampling happens *up front*.)

To any adversary these look the same — the output distribution is identical.
We want to prove that for *any* `A`, by induction on the structure of `A`.

### Why we cannot prove `A[lazy] = A[eager]` literally

These two programs are **not equal as programs**. They sample at *different
times* (lazy on-demand, eager up-front), so their *intermediate states* differ.
Any literal equality of the syntax trees, or of step-by-step behaviour, is false.
We need a coarser, semantic notion of "same".

---

## 2. The bridge: `convert`

The repository already provides the crucial gadget. `convert` (in `Transfer.lean`)
takes a *lazy* state (a partial table, some entries undefined) and **fills in all
the missing entries with fresh uniform samples**, turning a lazy state into an
eager-looking one.

The atomic fact (already proven: `lazy_query_convert_eq_convert_random_oracle_query`):

```
lazy_query x ; convert   =   convert ; random_oracle_query x
```

> *Query lazily and then fill in the rest of the table* = *fill in the whole
> table first and then read.* Both end with a fully-sampled table and the same
> answer distribution.

This single equation is the seed. Everything in Theorem 1 is about lifting it
from one query to a whole adversary.

---

## 3. Theorem 1 — `convert` slides across the whole adversary

**Statement (transfer form).** For a local adversary `A`,

```
A[lazy] ; convert   =   convert ; A[eager]
```

**The picture.** Think of `convert` as a token sitting at the *right end* of the
program. The theorem says the token can **slide all the way to the left**, and as
it passes each *lazy* query it rewrites it into an *eager* query. By the time it
reaches the start, every query has flipped from lazy to eager.

### 3.1 A generic sliding calculus (`transferBy`)

We abstract "`c` slides across, value preserved" into a relation parameterised by
*any* program `c`:

```
transferBy c p q   :=   (p >>= fun a => c >>= fun _ => pure a)  =  (c >>= fun _ => q)
```

(`Program.transfer` is exactly `transferBy convert`.) We then prove, **once and
generically**:

* `transferBy_pure`, `transferBy_bind` — the token slides across `pure` and
  through `;` (so sequencing is compositional);
* `zoom_pure`, `zoom_bind` — `Program.zoom` (running a program on a *sub-window*
  of the state) is a **monad morphism**;
* `transferBy_zoom` — therefore *any* sliding fact lifts through `zoom`. This is
  what carries the per-query fact (which lives on the global RO state) up to the
  full procedure state.

All of this is fully axiom-clean.

### 3.2 The structural induction (`body_transfer_gen`)

We induct on the seven `StmtWithHoles` constructors. Each case is one move:

| construct | how the token slides |
|---|---|
| `skip` / `pure` | trivially (`transferBy_pure`) |
| `s₁ ; s₂` | slide across `s₂`, then across `s₁` (`transferBy_bind`) |
| `if c then t else e` | slide past the guard, then into the taken branch |
| `while c do t` | the hard case — see §3.4 |
| adversary's own `sample`/assignment | `convert` *commutes* with it (it touches only the RO table, which these ops do not) |
| the **oracle hole** | the seed fires: `lazy_query ↦ eager_query` |

The oracle is modelled as a **hole** in the syntax; filling it (`instantiate`)
plugs in a procedure. The induction is parametric in the hole, so the
"lazy ↦ eager" step is supplied as a hypothesis and the structural plumbing is
uniform.

### 3.3 The honest locality `Loc` (and why `fv` was unusable)

Every structural case needs *"the adversary's own operation does not touch the RO
table"* — otherwise the token cannot pass it. The repo expresses this with a
free-variable footprint `fv_proc A`, but:

* its leaf definitions (`fv_getter`, `fv_setter`, …) are `sorry`; and
* a *computed* footprint of an **arbitrary getter/setter is genuinely
  undefinable** — getters are opaque Lean functions, not syntactic variables.

So we replaced `fv_proc A ≤ …ᶜ` with an **honest, semantic** predicate `Loc A`:
*each of `A`'s own operations commutes with `convert`* (i.e. transfers to itself,
`Stable`). This is exactly what the induction consumes, and it is *true precisely
when* the op doesn't interfere with the RO table.

> This locality is **necessary, not laziness**: an adversary that overwrites the
> RO table directly genuinely breaks the equivalence (fill-then-overwrite ≠
> overwrite-then-fill). `Loc` is the correct statement of "black-box oracle
> access: the adversary touches the table only through the oracle."

### 3.4 The hard case: `while` (a Kleene fixed point)

A loop is the *least fixed point* of its body — equivalently the supremum of its
finite unrollings `⊥, body;⊥, body;body;⊥, …`. To slide `convert` through it:

1. couple every finite unrolling of the lazy loop with the *same* unrolling of an
   intermediate transformer `Ψ` whose "exit" branch is `convert`
   (`whileBy_kleene_lazy`);
2. do the mirror for the eager side (`whileBy_kleene_eager`);
3. take the supremum: both sides agree at every stage, hence at the limit, using
   ω-Scott-continuity of `· ; convert` and `convert ; ·`.

The repo had this for `convert` specifically. We **ported it to be generic**
(`transferBy_while_loop`: any state, any token `c`), so the only RO-specific
ingredient — *the loop guard commutes with the token* — became a clean
hypothesis, discharged at the RO level by `Loc`'s `Stable` condition. The generic
lemma is **fully axiom-clean**; `transferL_while_loop` just instantiates it.

### 3.5 From query *semantics* back to the *syntax* (the bridges)

The theorem is phrased via the syntax's `Procedure.instantiate`, which needs the
oracle to be an actual **syntactic procedure** — `RO_lazy`/`RO_eager`. We encode
the queries with the available statements (`sample` + assignment) and prove the
**bridges** `procedureDenotation RO_lazy_proc = lazy_query` (and eager). The lazy
bridge needs a cached/fresh **case split** and a `funext` argument: in the cached
branch the procedure *re-writes the same value* into the table, which is a no-op
(`set (get s) s = s`).

> *Aside:* a cleaner design would interpret the hole with a *semantic* oracle
> directly (no syntactic procedure, no bridges), but that requires extending the
> denotation layer (Dominique's active file). The bridges are the price of using
> the existing `instantiate` pipeline — and they are now proven.

### 3.6 The procedure wrapper

`A` is a *procedure*: running it means *initialise locals → run the body →
extract `(return value, global state)`*. The body-level transfer lifts to the
procedure level through `transfer_wrapper`, which pushes `convert` through the
init/extract. The one extra requirement: the **return value must not depend on
the RO table** (so that reading it commutes with `convert`).

---

## 4. Theorem 2 — a coupling that preserves an invariant

**Statement (relational `prhl` form).** Given a state relation `P` such that the
oracle preserves it (`h`) and `A`'s own operations preserve it, then

```
prhl P  A[eager]  A[lazy]  (liftPost P)
```

**The picture.** A *coupling* runs the two programs **in lockstep** as one joint
distribution whose marginals are the two programs and whose support lies in
`P`-related pairs. Theorem 2 says: if every step keeps the two runs `P`-related,
the whole adversary does. (This is the form used for game hops / `EncRO`-style
arguments.)

The architecture is the **mirror image of Theorem 1**, in the coupling world:

| Theorem 1 (transfer / equation) | Theorem 2 (coupling / `prhl2`) |
|---|---|
| `Stable` (commutes with `convert`) | `GetOK`/`LocP` (preserves the invariant relationally) |
| `body_transfer_gen` | `body_prhl2_gen` (7 cases via `bind`/`cond`/`while_loop`/`pure_pure`) |
| `transferBy_zoom` | `prhl2_zoom` (lift a coupling through `zoom`) |
| `transferL_while_loop` (Kleene) | `prhl2.while_loop` (synchronized-loop coupling) |
| RO hole via `transfer_lazy_query` | RO hole via `ro_hhole_prhl` (couples `eager_query` vs `lazy_query`, from `h`) |
| `transfer_wrapper` | `prhl_wrapper` |

Two things to note about the coupling cases:

* **`if`** uses a *synchronized* conditional rule: both runs take the **same
  branch** because the guard, evaluated on `P`-related states, returns **equal
  booleans** (that's what `GetOK` guarantees).
* **`while`** uses a *synchronized* loop rule: both loops run the **same number
  of iterations**, the body preserving the invariant each time.

The lifted relation `liftRel P` says "`P` on the global RO states **and identical
locals**" — because the adversary's local computation is byte-for-byte the same on
the eager and lazy sides; only the oracle differs.

---

## 5. The map: lemma → idea

```
transferBy / transferBy_bind / transferBy_zoom   the generic sliding calculus      §3.1
body_transfer_gen                                structural induction (7 cases)    §3.2
Loc / Stable                                     honest locality                   §3.3
transferBy_while_loop / transferL_while_loop     the Kleene while argument         §3.4
RO_lazy/RO_eager + procDenotation_RO_*           syntactic oracle + bridges        §3.5
transfer_wrapper                                 procedure init/extract            §3.6
Program.transfer_instantiate                     ════ THEOREM 1 ════

liftRel / liftRelPost / GetOK / LocP             lifted invariant + locality       §4
body_prhl2_gen                                   structural coupling induction     §4
prhl2_zoom                                       coupling lift through zoom        §4
ro_hhole_prhl                                    RO hole coupling                  §4
prhl_wrapper                                     procedure wrapper (→ prhl)        §4
prhl_instantiate                                 ════ THEOREM 2 ════
```

---

## 6. What is and isn't trusted

* **Proved with no new `sorry`.** Every lemma above elaborates. The
  *state-generic* lemmas (`transferBy_while_loop`, `transferBy_zoom`,
  `prhl2_zoom`, …) depend only on `[propext, Classical.choice, Quot.sound]`.
* **Pre-existing scaffolding.** The RO model in `Basic.lean` leaves placeholder
  `sorry`s for the opaque types' instances (`Inhabited output`, `Fintype input`,
  `Countable state`, …). The final theorems inherit those via `#print axioms`,
  but **we introduced none of them**.
* **The one genuine hypothesis** (beyond the oracle fact) is **locality**: `A`
  touches the RO table *only through the oracle hole*. This is the faithful model
  of black-box oracle access, and — as noted — it is logically necessary.

---

## 7. One-paragraph summary

We proved that an arbitrary syntactic adversary cannot distinguish a lazy random
oracle from an eager one, in two equivalent forms. The engine is a single fact —
*"query lazily then fill the table = fill the table then read"* — lifted across
an arbitrary program by induction. We built a small generic calculus so the
lift is compositional, ported the loop (Kleene) argument to be oracle-agnostic,
replaced the unfinished syntactic free-variable analysis with an honest *semantic*
locality condition, and wrapped the result through the procedure-call boundary.
The relational version is the same skeleton expressed with couplings instead of
equations.
