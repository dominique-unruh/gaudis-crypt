# A guided tour of the framework

A report for Denis to prepare to explain the work to the team.

This document explains the conceptual building blocks we've put in place — **lenses**, **lens-ranges**, **orbits**, **orbit collapses**, the **`inRange` predicate**, **`glob`**, and the **headline commutation theorem** — and how they combine to give the cryptographic indistinguishability result (`claim_5`).

The audience is someone who knows Lean and basic probabilistic programming but is not an expert in measure theory.

---

## 1. The problem we're solving

The cryptographic setting is the standard "lazy vs eager random oracle" indistinguishability:

- **Eager world**: at the start, sample a random function `h : input → output` and store it. Every oracle query just reads `h`.
- **Lazy world**: at the start, the oracle table is empty (`fun _ => none`). Each query: if cached, return the cached value; otherwise sample a fresh output and cache it.

These two implementations produce the *same observable distribution* for any adversary. We want to prove this in Lean.

The "axiom-heavy" way to do this would be: write a couple of axioms saying "the adversary doesn't touch the oracle's internal state", then bash through. The framework we built lets us **replace those axioms with a single structural statement**: the adversary's range is disjoint from the oracle's range. The commutativity equations the axioms used to assert now become *theorems*.

The framework is general — it's not specific to oracles. It's a toolkit for reasoning about *which parts of state a probabilistic program touches*.

---

## 2. Programs and state

A program in our framework has type

```lean
Program s a := StateT s SubProbability a
```

Unfolding: `Program s a = s → SubProbability (a × s)`. Read it as: "given a starting state `s`, produce a (sub-)distribution over `(return value, final state)`".

A `SubProbability` is a probability measure whose total mass is `≤ 1` — basically a probability measure that can "lose mass" (modelling computations that might silently fail). All operations (`pure`, `bind`, `set`, `get`, `uniform`) live in this monad.

We don't need to know any measure theory beyond two facts:
- A `SubProbability` is something you can *integrate against*: given a function `F : a → ENNReal`, you get an expected value `∫⁻ x, F x ∂μ.1` (this is `μ.expected F`).
- For a `pure` (= "Dirac at `x`"), the integral is just `F x`.

The semantic primitives we use are:
- `Program.uniform : Program s a` — sample uniformly from a finite type, don't touch state.
- `Program.set v x : Program s Unit` — write `x` into the lens `v` of state.
- `Program.get v : Program s a` — read from lens `v`, don't change state.
- `pure x` / `bind` — monadic plumbing.

---

## 3. Lenses

### 3.1 What's a lens
z
A `Lens a m` is a focused "window" onto a piece of memory:

```lean
structure Lens (a m : Type) where
  get : m → a
  set : a → m → m
  set_get : ∀ s x, get (set x s) = x
  set_set : ∀ s x y, set y (set x s) = set y s
  get_set : ∀ s, set (get s) s = s
```

The three laws are the obvious ones — "what you put in is what you get out", "the last write wins", "writing what's already there is a no-op".

### 3.2 Intuition

Think of `m = state` (a big record) and `a = ℕ` (one field). The lens `X : Lens ℕ state` is just "the field named X". `X.get s` reads the field; `X.set v s` is `{ s with X := v }`.

But the lens abstraction is more general — `a` doesn't have to be a literal field. `a` could be a *function* of several fields (e.g., `x + y` taken jointly), and `set` can do nontrivial bookkeeping. The laws make sure the abstraction stays sensible.

### 3.3 Disjointness of lenses

Two lenses `X, Y : Lens ?₁ s` and `Lens ?₂ s` are **disjoint** when their `set`s commute:

```lean
class disjoint (x : Lens a m) (y : Lens b m) where
  commute : ∀ s v w, x.set v (y.set w s) = y.set w (x.set v s)
```

Intuitively: `X` and `Y` are different fields. Writing one doesn't disturb the other.

---

## 4. Updates and `Lens.range`

### 4.1 Updates are functions `m → m`

Given a lens `l : Lens a m`, every function `f : a → a` becomes a state-update `l.update f : m → m`:

```lean
def Lens.update (lens : Lens a m) (f : a → a) : m → m :=
  fun s => lens.set (f (lens.get s)) s
```

"Read the lens, transform the value, write it back." This is the *only* way a lens can change memory.

### 4.2 `Lens.range`: the set of updates a lens can do

```lean
def Lens.range (lens : Lens a m) : LensRange m where
  updates := Set.image lens.update ⊤   -- = {lens.update f | f : a → a}
  …
```

This is **the set of all possible memory transformations achievable via this lens**. For `X : Lens ℕ state`, `X.range.updates` is exactly the set `{ (s ↦ {s with X := f s.X}) | f : ℕ → ℕ }`.

So a "lens-range" can be read as: "**which part of memory** can be affected, expressed as a set of functions `m → m`".

---

## 5. `LensRange`: a region of memory

A `LensRange m` abstracts the notion of "a region of memory" *without* tying it to a specific Lens:

```lean
structure LensRange (m : Type) where
  updates : Set (m → m)
  id ∈ updates                  -- can do nothing
  closed under composition       -- can chain updates
  double_commutant : (Submonoid.centralizer (Submonoid.centralizer updates).carrier).carrier
                   = updates
```

The first two conditions just say `updates` is a *submonoid* of the function monoid `(m → m, ∘, id)`.

The third — the **bicommutant condition** — is the interesting one. Let me explain.

### 5.1 The bicommutant condition

The **commutant** of a set `S ⊆ (m → m)` is

$$S' := \{ f : m → m \mid \forall g \in S,\ f \circ g = g \circ f \}$$

— everything that commutes with everything in `S`. The **bicommutant** is `S'' := (S')'`. You always have `S ⊆ S''`.

A LensRange is required to satisfy `updates'' = updates` — its updates equal their own bicommutant. We call such a set *bicommutant-closed*.

**Why this condition?** Bicommutant closure is the algebraic shadow of "these updates all operate on the same region of memory". It's the same trick that defines a *von Neumann algebra* in operator theory. Without it, the abstraction would admit pathological subsets that don't correspond to any sensible "region".

**Concrete example**: for `m = ℕ × ℕ` (two fields X, Y), three example LensRanges are
- `R_X.updates = { s ↦ (h s.1, s.2) | h : ℕ → ℕ }` (everything that only touches X)
- `R_Y.updates = { s ↦ (s.1, h s.2) | h : ℕ → ℕ }` (everything that only touches Y)
- `R_{XY}.updates = { s ↦ (f s, g s) | f, g : ℕ × ℕ → ℕ }` (joint updates of X and Y)

All three are bicommutant-closed. `R_X ⊑ R_{XY}`, `R_Y ⊑ R_{XY}`.

### 5.2 The lattice structure

`LensRange m` is a *complete lattice* under set inclusion of `updates`:
- `⊥` is the trivial range `{id}` (nothing).
- `⊤` is the full function monoid (everything).
- `⊔` (join) of two ranges is the bicommutant closure of their union.
- `⊓` (meet) is intersection.

This complete-lattice structure is **important** because we'll define `Program.range p` as an `sInf` (greatest-lower-bound).

### 5.3 Complement: `Rᶜ`

For `R : LensRange m`, its complement `Rᶜ` is the commutant `R'`:

```lean
Rᶜ.updates = (Submonoid.centralizer R.updates).carrier
```

This is again a LensRange (the commutant is always bicommutant-closed). Intuitively: `Rᶜ` is "everything that ignores what `R` is doing" — updates orthogonal to `R`.

**The "disjoint" check.** Two ranges `R, R'` are *disjoint* (in our sense — every R-update commutes with every R'-update) iff `R ≤ R'ᶜ` (equivalently `R' ≤ Rᶜ`).

---

## 6. Lenses give rise to LensRanges; not every LensRange comes from a lens

`Lens.range : Lens a m → LensRange m` is the obvious map. But it's not surjective — there are perfectly good `LensRange m`s that aren't of the form `l.range` for any lens.

We have an explicit counterexample in `Lens.lean` (the `no_least_lens` theorem): two specific lenses on `bit × bit × bit` whose **least upper bound** doesn't exist in the lens lattice. The two lenses' ranges *do* have a join in `LensRange`, but it's not lens-derived.

This is why we work with `LensRange` rather than `Lens` directly — the lattice is *closed* under joins and meets.

---

## 7. Orbits

### 7.1 The orbit of a state under a range

Given `R : LensRange m` and a state `σ : m`, the **`R`-orbit of `σ`** is

$$\text{R-orbit}(\sigma) := \{ u\,\sigma \mid u \in R.\text{updates} \}$$

— all states reachable from `σ` by applying some update in `R`. Since `id ∈ R`, we have `σ ∈ R-orbit(σ)`.

**Examples** (with `m = ℕ × ℕ`):
- `R_X-orbit((3, 7)) = { (n, 7) | n : ℕ }` — vary X, fix Y.
- `R_Y-orbit((3, 7)) = { (3, n) | n : ℕ }` — vary Y, fix X.
- `R_{XY}-orbit((3, 7)) = ℕ × ℕ` — everything.

**Conceptually**: the orbit is "everything I can transform σ into using only operations in `R`". It captures the **forward action** of `R` on the state.

### 7.2 The orbit equivalence

Two states are *R-orbit-equivalent* iff one is in the other's orbit (equivalence closure):

```lean
def LensRange.orbit_setoid (R : LensRange m) : Setoid m where
  r := Relation.EqvGen (fun s s' => ∃ f ∈ R.updates, f s = s')
  ...
```

The quotient `m / R.orbit_setoid` is "states modulo what `R` can do" — i.e., "the part of state that `R` can't modify".

For Lens-derived `R = l.range`, this quotient is `Quotient l.equal_outside_setoid` — the complement of `l`'s field.

---

## 8. `Program.inRange p R`: "`p` lives in `R`"

The central predicate of the framework:

```lean
def Program.inRange (p : Program s a) (R : LensRange s) : Prop :=
  ∀ f ∈ Rᶜ.updates,
    (liftF f >>= fun _ => p) = (p >>= fun x => liftF f >>= fun _ => pure x)
```

Where `liftF f` is the lift of a deterministic state update `f : s → s` to a `Program s Unit`.

**The intuition is non-obvious; here's the unpacking.**

### 8.1 Why "commutes with the complement"?

`p.inRange R` says: `p` *commutes* with every "deterministic update from outside `R`". Imagine `p` as a black box that touches state in some way. If you can switch the order between `p` and any `f ∈ Rᶜ` (= any update orthogonal to `R`), then `p` doesn't touch anything *outside* `R`. Hence `p`'s "region of activity" is inside `R`.

By the bicommutant closure of `R`, "commutes with everything in `Rᶜ`" is exactly "lives in `R = (Rᶜ)'`" — the algebraic statement of "actions are in `R`".

### 8.2 What `inRange` tells us, concretely

For `p.inRange R` with `R` lens-derived:
- `p` only reads and writes within `R`'s slot.
- `p`'s output state is in `R-orbit(σ)` for any input state `σ` (the **orbit fact**).
- `p` commutes with anything that *only* touches state outside `R`.

For the canonical example, `p := Program.set X 5`:
- We can prove `p.inRange X.range` (literally as `Program.inRange_set` in `ProgramRange.lean`).
- Reading from any disjoint lens `Y` *before* or *after* `p` gives the same result (because `p` doesn't touch `Y`).

### 8.3 Why the equation has that funny shape

The two sides of `inRange` need to have the same return type. Naively writing `(liftF f >>= fun _ => p) = (p >>= fun _ => liftF f)` would type-fail: the LHS returns `p`'s value (type `a`), but the RHS returns Unit. The "save the output and restore it" pattern on the RHS is just type bookkeeping.

### 8.4 Structural lemmas

- **`inRange_pure x R`**: `pure x` lives in *any* range (it touches no state).
- **`inRange_bind`**: if `p.inRange R` and `∀ x, (f x).inRange R`, then `(p >>= f).inRange R`. (Composition preserves the region.)
- **`inRange_mono`**: if `p.inRange R` and `R ≤ R'`, then `p.inRange R'`. (Bigger range still contains.)
- **Primitives** (`inRange_set`, `inRange_get`, `inRange_uniform`): `set v x` and `get v` live in `v.range`; `uniform` lives in `⊥` (touches no state).

These together give a **compositional algorithm** to compute the range of any program built from primitives: each piece has a known range, and `inRange_bind` joins them.

---

## 9. `Program.range p`: the smallest range containing `p`

```lean
noncomputable def Program.range (p : Program s a) : LensRange s :=
  sInf { R | p.inRange R }
```

The **smallest LensRange** in which `p` lives, taken as the meet (in the lattice) of all valid `R`s.

**Caveat**: `p.inRange p.range` is *not* automatic from this definition — the meet of an upward-closed set isn't guaranteed to be in the set. So this is the *abstract* "natural range", but in practice we either supply `inRange` evidence with respect to a specific `R` (often Lens-derived), or we work with the lens-derived wrapper.

---

## 10. `glob`: the global variables of a program

```lean
noncomputable def Program.glob (A : Program s a) :
    Getter (Quotient (A.range)ᶜ.orbit_setoid) s :=
  A.range.touched_getter
```

A **Getter** is a read-only lens: just `{ get : m → a }`, no setter.

`glob A` is the read-only projection of state onto "the part `A` touches". Concretely:
- `A.range` is the region `A` operates in.
- `(A.range)ᶜ` is its commutant — everything outside the region.
- `(A.range)ᶜ.orbit_setoid` partitions state by "what's invariant under everything outside the region".
- The quotient by this equivalence picks out "the part inside the region" — exactly `glob A`.

For `A = Program.set X 5`: `A.range = X.range`, complement is "everything except X", complement's orbit is "states agreeing on everything except X", quotient is "the X-value". So `glob A : Getter ℕ state` just reads `X`.

This matches the EC notion of `glob A`: "the variables A touches".

### 10.1 A worked example

Let's make this concrete with a small state and three programs. Take

```lean
structure state where
  x : ℕ        -- field 1
  y : ℕ        -- field 2

def X : Lens ℕ state := { get := (·.x), set := fun v s => { s with x := v }, … }
def Y : Lens ℕ state := { get := (·.y), set := fun v s => { s with y := v }, … }
-- with instance disjoint X Y
```

Now consider three programs, in **decreasing order of how cleanly the framework's "natural" range matches our intuition**:

#### Program A₃: sample uniformly, ignore the result (cleanest case)

```lean
def A₃ : Program state Bool := Program.uniform
```

- **Action of `A₃` at `(x, y)`**: returns a uniformly random `Bool` and leaves state untouched.
- **`A₃.range`**: by `inRange_uniform`, `A₃.inRange ⊥`. The smallest valid range is `⊥ = {id}` (uniform doesn't change state and its output doesn't depend on state).
- **`(A₃.range)ᶜ = ⊥ᶜ = ⊤`** (everything commutes with `id`).
- **`⊤.orbit_setoid`** identifies all states with all states (take `f = const σ'`; it's in `⊤`, and `f σ = σ'`). Quotient = a singleton.
- **`glob A₃ : Getter (Quotient = singleton ≅ Unit) state`** — reads nothing.

✓ "Uniform sampling has no global variables." Clean and right.

#### Program A₂: read X, increment X

```lean
def A₂ : Program state Unit := do
  let v ← Program.get X
  Program.set X (v + 1)
```

- **Action of `A₂` at `(x, y)`**: produces `((), (x+1, y))`. Deterministically increments X.
- **`A₂.range`**: the smallest range here is `X.range`. Why? Because `inRange A₂ R` requires `Rᶜ`-updates to (a) preserve the value `A₂` reads (= `X.get s`) and (b) commute with `A₂`'s write. Both force `Rᶜ ⊆ X.compl.range = X.rangeᶜ`, i.e. `R ⊇ X.range`. So `A₂.range = X.range`.
- **`(A₂.range)ᶜ = X.rangeᶜ = X.compl.range`** — "updates not touching X".
- **`X.compl.range.orbit_setoid`** identifies `(x₁, y₁) ~ (x₂, y₂)` iff `y₁ = y₂` (only Y-updates relate them). Quotient ≅ `ℕ` (the X-value).
- **`glob A₂ : Getter (Quotient ≅ ℕ) state`** projects to the X-field.

✓ "A program that reads-and-writes X has glob = X-value." Matches intuition.

The key here is that `A₂`'s `range` is `X.range` *because A₂ can take X to any value via `v + 1` over varying inputs* — the entire `X.range` of updates is needed to express A₂'s dependence on X.

#### Program A₁: write the *specific* value 5 to X (subtle case)

```lean
def A₁ : Program state Unit := Program.set X 5
```

This looks innocent, but the actual `A₁.range` is **strictly smaller than `X.range`**, and the corresponding `glob A₁` is **not** `Getter ℕ state`. Here's the analysis:

- **Action of `A₁` at `(x, y)`**: produces `((), (5, y))`. Deterministically *forces* X to 5, regardless of input.
- **`A₁.range`**: by `inRange_set`, `A₁.inRange X.range` holds — so `A₁.range ≤ X.range`. But the smallest valid range is the *bicommutant of the single action* `X.update (const 5)`. Computing it: this turns out to be
  $$A_1.\text{range} = \{ X.\text{update}\, h \mid h(5) = 5 \}.$$
  Only X-updates that fix the value `5`. This is **strictly smaller** than `X.range`, because A₁ never actually distinguishes X-values *other than 5* — anything that "agrees with setting X to 5" is observationally indistinguishable from A₁ as far as A₁'s commutation behaviour is concerned.
- **`(A₁.range)ᶜ`** is correspondingly *bigger* than `X.rangeᶜ`. It includes updates that *change* X, as long as they preserve the value `5` (e.g., a function that maps X = 3 to X = 7 but fixes X = 5).
- **The orbit equivalence** under `(A₁.range)ᶜ` identifies any two states with X ≠ 5 (since `(A₁.range)ᶜ` lets us swap X-values freely as long as we fix `5`), and keeps `X = 5` states separate. So the quotient has effectively **two equivalence classes**: "X = 5" and "X ≠ 5".
- **`glob A₁ : Getter (Quotient ≅ Bool) state`** — projects to the single bit "is X = 5?".

That is, `A₁`'s `glob` does **not** read the whole X-value — it reads only "is X equal to 5?", because that's the only observable distinction A₁ makes among states.

#### Summary

| Program | What it does | `range` | `glob` reads |
|---|---|---|---|
| `Program.uniform` | samples, no state change | `⊥` (= `{id}`) | nothing (`≅ Unit`) |
| `Program.get X >>= fun v => Program.set X (v+1)` | reads then writes X | `X.range` | the X-value (`≅ ℕ`) |
| `Program.set X 5` | writes the specific value 5 to X | `{X.update h | h(5)=5}` ⊊ `X.range` | the bit "X = 5?" (`≅ Bool`) |

### 10.2 What the example teaches

The key conceptual point is:

> **`Program.range` is the smallest LensRange that captures the program's *observable behavior under commutation*, not necessarily the smallest LensRange "containing the variables it touches" in any naive sense.**

For a program that uses X in a "full" way (reads or writes arbitrary X-values), `range` matches `X.range` and `glob` projects to the full X-value. For a program that uses X "narrowly" (e.g., always writes the *same* fixed value), `range` is finer than `X.range` and `glob` reflects only the specific aspect of X that the program distinguishes.

This is sharper than EC's notion of `glob A` (which typically tracks *which variables* `A` reads/writes). Our `glob` tracks *which aspects of which variables* — a finer-grained semantics. For most practical programs the two coincide; the difference shows up for programs that fix a constant value (as `A₁` does).

In practice, when reasoning about `claim_3` and `claim_5`, this subtlety doesn't matter because we always use `inRange p R` against a chosen `R` (typically lens-derived), never `Program.range p` directly. The `Program.range` definition is mostly there for theoretical completeness.

---

## 11. `HasOrbitCollapse`: the technical assumption that makes the headline proof go through

```lean
def LensRange.HasOrbitCollapse (R : LensRange m) (σ : m) : Prop :=
  ∃ f ∈ Rᶜ.updates, f σ = σ ∧ ∀ s, ∃ u ∈ R.updates, u σ = f s
```

This one takes some unpacking. Let me build up the intuition with pictures and concrete examples.

### 11.1 The picture

Imagine the state space `m` partitioned into `R`-orbits — equivalence classes under "can be transformed into one another by an update in `R`". Pick a state `σ`; the `R`-orbit of `σ` is the equivalence class containing `σ`.

```
  m
  ┌────────────────────────────────────┐
  │  R-orbit of σ                       │
  │  ┌──────────────┐                   │
  │  │    σ • • • • │                   │
  │  │     • • • • •│  ← states reachable from σ via R
  │  │  • • • • •   │
  │  └──────────────┘                   │
  │                                      │
  │   • • •            ← other orbits   │
  │      • • •                          │
  │                                      │
  │  • •                                 │
  │                                      │
  └────────────────────────────────────┘
```

`HasOrbitCollapse R σ` says: **there's a single function `f : m → m` in `Rᶜ`** that

1. **fixes `σ`** — leaves σ where it is, and
2. **takes every state to *some* point in the orbit of `σ`** — collapses the entire space *into* the orbit.

So `f` is a "projection onto the orbit" that doesn't move σ. Picture:

```
  ┌────────────────────────────────────┐
  │  ┌──────────────┐                   │
  │  │    σ • • • • │     ▲             │
  │  │     • • • • •│ ← all the         │
  │  │  • • • • •   │     arrows        │
  │  └─────▲────────┘     from f        │
  │   •────┘        ▲                   │
  │       •─────────┘                   │
  │                                      │
  │  •────────────────►(somewhere in    │
  │                     the orbit)       │
  └────────────────────────────────────┘
```

The crucial thing is that `f` lives in `Rᶜ` — it commutes with everything in `R`. So applying `f` is "*from outside* `R`", yet it ends up inside `R`'s orbit. That combination is what makes it useful.

### 11.2 Concrete construction: lens-derived case

For `R = l.range` where `l : Lens a m` is a lens, we can write down the collapse function explicitly. Let `[σ] := l.compl.get σ` (= the "everything except `l`" part of σ).

The function is

```lean
f := l.compl.update (Function.const _ [σ])
```

i.e., "force every state's *complement* to match σ's complement, leaving the lens-content alone".

Let's verify the three properties:

1. **`f ∈ Rᶜ.updates`**. By the `complement_range` theorem, `Rᶜ = l.compl.range`. Our `f` is `l.compl.update _`, so it's in `l.compl.range.updates`. ✓

2. **`f σ = σ`**. We have `f σ = l.compl.set [σ] σ`. By the lens law `set (get x) x = x` (here applied to `l.compl`), this equals `σ`. ✓

3. **`f s ∈ R-orbit(σ)`** for all `s`. Compute:
   - `f s` has *lens-content* `l.get s` (because `l.compl.set` doesn't touch lens-content).
   - `f s` has *complement* `[σ]` (we forced it).

   So `f s` agrees with σ on the complement. Hence `f s ∈ l-orbit(σ)`. ✓

**Concrete instance** (`m = ℕ × ℕ`, `l = X`):
- `R-orbit(σ) = { (x, σ.y) | x : ℕ }` (all states with σ's Y-value).
- `f := Y.update (const σ.y)` ("force Y to σ.y").
- `f σ = (σ.x, σ.y) = σ`. ✓
- For any `s = (x, y)`: `f s = (x, σ.y) ∈ R-orbit(σ)`. ✓

That's it — the lens-derived case is mechanical: the lens decomposition `m ≃ (lens-content) × (complement)` lets us collapse the complement to σ's, leaving lens-content arbitrary, ending up in σ's orbit.

This is exactly what `Lens.range_hasOrbitCollapse` proves in the codebase.

### 11.3 Where it can fail

The condition isn't automatic. Here's a setting where it **fails**.

Take `m = ℝ × ℝ` and `R := {translations along the diagonal}`, i.e.
$$R.\text{updates} = \{ (x, y) \mapsto (x + a, y + a) \mid a \in \mathbb{R} \}.$$

This is an *abelian* monoid (additive).

- `R-orbit(σ) = the diagonal line through σ` — a one-dimensional subspace.
- `Rᶜ` (the commutant) is the set of all functions that commute with every diagonal translation. Computing: any `f` that satisfies `f((x,y) + (a,a)) = f(x,y) + (a,a)` — i.e., diagonal-translation-equivariant maps.
- For HasOrbitCollapse: we need `f ∈ Rᶜ` with `f σ = σ` and `f s` on the diagonal through σ.

After computing (set `b(x-y)` as a function of the off-diagonal coordinate), one finds that the constraints — translation-equivariance, fixing σ, and mapping to the diagonal — together force `b(x - y) = b(x - y) + a` for every `a`, which is contradictory. **No such `f` exists.** HasOrbitCollapse fails.

The deeper reason: for abelian `R`, you have `R ⊆ Rᶜ`, so the "outside-`R`" updates `Rᶜ` are *the same kind of thing* as `R` itself, just larger. The constraint "fix σ AND be in `Rᶜ`" forces the function into a stabiliser, which is too small to do real work.

For lens-derived `R`, `Rᶜ` consists of "updates on the orthogonal slot" — *qualitatively different* from `R`'s "updates on the lens slot". That qualitative difference is what allows a non-trivial `f` to exist.

### 11.4 Why we need it in the proof

`commute_of_disjoint` reduces, after some setup, to needing: **for each outcome `(x, s_p)` of `p σ`, there's a `u ∈ R.updates` with `u σ = s_p`** — i.e., `p`'s output states lie in `R-orbit(σ)` (this is the "orbit fact").

The proof of the orbit fact is exactly where `HasOrbitCollapse` is used:

> For any potential "bad" state `s' ∉ R-orbit(σ)`: take the collapse function `f`. Since `f σ = σ` and `f` maps every state into `R-orbit(σ)`, the function `f` doesn't reach `s'` (any preimage of `s'` would have to be in `f`'s image, which lies in `R-orbit(σ)` — but `s' ∉ R-orbit(σ)`).
>
> By `inRange p R` and the `(p σ).1 = (p (f σ)).1.map (id × f)` identity, the measure of `(x, s')` in `(p σ).1` equals the measure of `f`'s preimage, which is empty. So `(p σ).1 {(x, s')} = 0`.

Without `f`, this argument has no traction — we can't "test" whether a state is outside the orbit by applying some function from outside `R`.

### 11.5 What this means in practice

- **Lens-derived ranges**: HasOrbitCollapse is automatic (via `Lens.range_hasOrbitCollapse`). The wrapper `commute_of_disjoint_lens` discharges the hypothesis silently.

- **Non-lens-derived ranges** (e.g., joins, intersections, abelian regions): HasOrbitCollapse may or may not hold. If it does, the user must provide the collapse function as data; if it doesn't, `commute_of_disjoint` simply *can't be applied to this `R`*, and the proof needs a different tactic.

- **In our cryptographic use case**: every range we care about (`random_oracle_state.compl.range`, `random_oracle_state.range`) is lens-derived. So we never have to think about HasOrbitCollapse — it's discharged for free.

The technical assumption is the price of working in a fully general LensRange framework. If we restricted to lens-derived ranges by construction, we wouldn't need it. We pay for the generality with this hypothesis.

---

## 12. The headline: `commute_of_disjoint`

```lean
theorem Program.commute_of_disjoint
    {s a b : Type} [Countable a] [Countable b] [Countable s]
    {p : Program s a} {q : Program s b} {R R' : LensRange s}
    (hp : p.inRange R) (hq : q.inRange R') (hdisj : R ≤ R'ᶜ)
    (hp_coll : ∀ σ, R.HasOrbitCollapse σ)
    (hq_coll : ∀ σ, R'.HasOrbitCollapse σ) :
    (p >>= fun x => q >>= fun y => pure (x, y))
  = (q >>= fun y => p >>= fun x => pure (x, y))
```

**Reading**: if `p` lives in `R`, `q` lives in `R'`, and `R, R'` are disjoint (every R-update commutes with every R'-update), then `p` and `q` commute as programs.

### 12.1 Why this needs measure theory

For deterministic programs this is a one-line algebraic argument: `p`'s state-update `u_p ∈ R` commutes with `q`'s update `v_q ∈ R'`. Done.

For *probabilistic* programs it's more subtle: each run of `p` picks a different `u_p` (depending on its random coins), and we have to swap two integrations against `(p σ).1` and `(q σ).1`. This is genuine Fubini-style measure theory.

### 12.2 The proof, in five steps (sketched gently)

After applying `program_ext` (it suffices to show all `wp`s match) and stripping the binds, we need

$$\int_{(x, s_p) \sim p\sigma} \int_{(y, s_{pq}) \sim q s_p} F((x,y), s_{pq}) = \int_{(y, s_q) \sim q\sigma} \int_{(x, s_{qp}) \sim p s_q} F((x,y), s_{qp})$$

**Step (a)**: use the orbit fact (from `hp_coll`) to pick, for each `p`-outcome `(x, s_p)`, a witness `u_p ∈ R.updates` with `u_p σ = s_p` (via `Classical.choice`). Then `q s_p = (q σ).map (id × u_p)` (by `inRange_subprob`), so the inner integral becomes `∫ F((x,y), u_p s') d(q σ)`.

**Step (b)**: now both integrals are over the *independent* measures `(p σ)` and `(q σ)`. Apply `lintegral_lintegral_swap` (Fubini).

**Step (c)**: use disjoint-commutativity `u_p ∘ v_q = v_q ∘ u_p` (from `hdisj`) to rewrite `u_p s' = v_q s_p` for `q`-outcomes `(y, s')` in q-orbit.

**Step (d)**: use `inRange_subprob` *for p* (with `v_q` now playing the role of the shift) to convert `∫ ... d(p σ)` to `∫ ... d(p s_q)`.

**Step (e)**: reassemble — the result is the RHS form.

The Countable hypotheses are needed for the Fubini side condition: in general, the product of two top-σ-algebras isn't the top σ-algebra, but for countable types it is, and every function is automatically measurable.

### 12.3 The `commute_of_disjoint_lens` wrapper

For Lens-derived ranges, the `HasOrbitCollapse` hypotheses are automatic. The wrapper

```lean
theorem Program.commute_of_disjoint_lens
    {l : Lens c s} {l' : Lens d s}
    (hp : p.inRange l.range) (hq : q.inRange l'.range)
    (hdisj : l.range ≤ (l'.range)ᶜ) :
    ...
```

drops them entirely. This is the version `claim_3` actually uses.

---

## 13. The cryptographic application

This is the payoff. Let me walk through the chain.

### 13.1 The cast

```lean
axiom random_oracle_state : Variable (input → Option output)  -- the oracle's cache
axiom adv : Program state Unit                                  -- the adversary
axiom adv_inRange_compl_ro :                                    -- the only structural axiom
    adv.inRange random_oracle_state.compl.range
```

The single axiom says: **`adv`'s range is contained in `random_oracle_state.compl.range`**, i.e., the adversary touches only stuff outside the oracle's cache. This replaces the previous *two* axioms that asserted specific commutativity equations.

### 13.2 `convert` (the bridge)

```lean
def convert : Program state Unit := do
  let h ← Program.get random_oracle_state
  let y ← Program.uniform
  Program.set random_oracle_state (fun x => some ((h x).getD (y x)))
```

`convert` "fills in the holes" of the lazy table with uniformly random values. It only touches `random_oracle_state`.

We prove (no axiom!) `convert.inRange random_oracle_state.range` mechanically via `inRange_bind`, `inRange_get`, `inRange_uniform`, `inRange_set`.

### 13.3 `claim_3`: `adv; convert = convert; adv`

Apply `commute_of_disjoint_lens` with:
- `l = random_oracle_state.compl` (witnesses adv's range)
- `l' = random_oracle_state` (witnesses convert's range)
- `hdisj`: `l.range ≤ l'.rangeᶜ`. By `LensRange.complement_range`, `l.range = l'.rangeᶜ`, so this is just `le_of_eq`.

Result: `adv; convert = convert; adv`. The previous two axioms are now provable.

### 13.4 `claim_4`: lazy + convert = eager

```lean
theorem claim_4 :
    (oracle_loop lazy_init lazy_query >>= fun b => convert >>= fun _ => pure b)
  = oracle_loop random_oracle_init random_oracle_query
```

A `while`-loop induction (Kleene fixed-point + ω-continuity) using `claim_1` (lazy_init + convert = eager_init), `claim_2` (lazy_query + convert ≡ convert + eager_query), and `claim_3` (adv + convert = convert + adv) as the per-iteration step.

### 13.5 `claim_5` (wp-level)

```lean
theorem claim_5 (F : Bool × state → ENNReal)
    (hF_inv : ∀ b σ x, F (b, random_oracle_state.set x σ) = F (b, σ)) :
    (oracle_loop lazy_init lazy_query).wp F
  = (oracle_loop random_oracle_init random_oracle_query).wp F
```

**For any postcondition `F` that doesn't depend on the oracle's cache, lazy and eager loops have the same `wp`.**

Proof: `wp F` of `claim_4`'s LHS unfolds via `wp_bind` to `lazy.wp (λ(b,σ). (convert >>= pure b).wp F σ)`. The inner `(convert >>= pure b).wp F σ` simplifies to `F(b, σ)` when `F` is RO-invariant (because `convert` is a probability measure that only changes RO). Hence `lazy.wp F = eager.wp F`.

### 13.6 `claim_5_subprob` (SubProbability-level)

```lean
theorem claim_5_subprob {β : Type} (h : state → β)
    (h_inv : ∀ σ x, h (random_oracle_state.set x σ) = h σ)
    (σ₀ : state) :
    (oracle_loop lazy_init lazy_query σ₀ >>=
        fun bσ => pure (bσ.1, h bσ.2))
    =
    (oracle_loop random_oracle_init random_oracle_query σ₀ >>=
        fun bσ => pure (bσ.1, h bσ.2))
```

The distributional version: project the final state through any RO-invariant `h`, and the resulting joint distribution of `(boolean output, h state)` is the same in lazy and eager worlds.

The proof reduces to `claim_5` by integrating the indicator function of each measurable set — a clean wrapper.

---

## 14. The big picture

```
┌──────────────┐         ┌──────────────┐
│   Lens a m   │ ── give rise to ──▶ │ LensRange m  │
└──────────────┘                     └──────────────┘
                                           │
                                           │ defines
                                           ▼
        ┌────────────────────────────────────────────┐
        │  inRange p R  ─── "p touches only R"        │
        │  range p      ─── smallest R containing p   │
        │  glob p       ─── what's visible to p       │
        └────────────────────────────────────────────┘
                                           │
                                           │ enables
                                           ▼
        ┌────────────────────────────────────────────┐
        │  commute_of_disjoint:                       │
        │    p.inRange R, q.inRange R', R ⫫ R'        │
        │  ⟹  p;q = q;p (as programs)                │
        └────────────────────────────────────────────┘
                                           │
                                           │ applied to (adv, convert)
                                           ▼
        ┌────────────────────────────────────────────┐
        │  claim_3 : adv;convert = convert;adv        │
        │  (replaces two ad-hoc commutativity axioms) │
        └────────────────────────────────────────────┘
                                           │
                                           │ combined with claims 1, 2
                                           ▼
        ┌────────────────────────────────────────────┐
        │  claim_4 : lazy;convert = eager             │
        └────────────────────────────────────────────┘
                                           │
                                           │ + convert is RO-only
                                           ▼
        ┌────────────────────────────────────────────┐
        │  claim_5 : for RO-invariant F,              │
        │            lazy.wp F = eager.wp F            │
        │                                              │
        │  claim_5_subprob : distributions of          │
        │    (boolean output, h state) agree, for     │
        │    any RO-invariant h.                       │
        └────────────────────────────────────────────┘
```

---

## 15. Things to flag when explaining to the team

1. **The framework is independent of the cryptographic application.** It's a general theory of "what parts of state does a program touch" for any state-and-distribution setting.

2. **The single structural axiom** (`adv_inRange_compl_ro`) is much more honest than the two behavioral axioms it replaced. We assert "adv touches only non-RO state" once and derive every commutativity equation as a theorem.

3. **The `Countable` hypotheses on `commute_of_disjoint`** are a Lean-formal artifact (the product of top σ-algebras isn't top in general, but is for countable spaces). They're not a real mathematical assumption — the math holds without them, but the Lean proof needs them for the Fubini side condition. Our `state` is already countable in the codebase, so this is never a practical limitation.

4. **`HasOrbitCollapse`** is a technical condition needed for the proof, automatically satisfied for Lens-derived ranges. The user-facing `commute_of_disjoint_lens` wrapper hides it entirely.

5. **The lens witnesses `l, l'`** in the wrapper are *collapse certificates*, not arbitrary upper bounds. `p.range` itself (the sInf-defined range) isn't guaranteed to be lens-derived, so we ask the user to *supply* a lens-derived upper bound.

6. **What we don't have proved** (and could be future work):
   - `Program.inRange_self : p.inRange p.range` — currently `range` is defined but not known to be a valid range. In practice, callers supply specific `R` with `inRange p R`.
   - A typeclass-based version of `HasOrbitCollapse` to eliminate `l` from the signature entirely.
   - Generalization beyond `[Countable]` (would need real Lean measure-theoretic work for non-product σ-algebras).

7. **The proof of `commute_of_disjoint`** uses, in order: `program_ext` (wp ext), `inRange_subprob` (SubProb form of inRange), `Classical.choice` (to extract `u_p`), `lintegral_lintegral_swap` (Fubini), disjoint commutativity, `inRange_subprob` (again, for p), reassembly. Roughly 150 lines of careful measure-theoretic bookkeeping.

---

## 16. Useful entry points in the code

- `PlonkLean/Lens.lean` — definition of `Lens`, `disjoint`, `Lens.compl` (complement lens via equivalence quotient).
- `PlonkLean/LensRange.lean` — `LensRange`, `Lens.range`, lattice/Compl instances, `orbit_setoid`, `global_getter`, `touched_getter`.
- `PlonkLean/ProgramRange.lean` — `Program.inRange`, `Program.range`, `Program.glob`, the structural lemmas (`inRange_bind`, `inRange_pure`, `inRange_mono`), the primitive lemmas (`inRange_set`, `inRange_get`, `inRange_uniform`), orbit-collapse machinery (`HasOrbitCollapse`, `Lens.range_hasOrbitCollapse`), the headline `commute_of_disjoint` and its lens wrapper, and the SubProb/wp characterizations.
- `PlonkLean/RO.lean` — the cryptographic application: `convert`, `claim_1`/`2`/`3`/`4`/`5` (and the SubProb variant).
- `PlonkLean/Semantics.lean` — `Program`, `SubProbability`, monad laws.
- `PlonkLean/WeakestPreconditions.lean` — `wp`, `wp_bind`, `wp_set`, `wp_get`, `wp_uniform`.

---

*End of report.*
