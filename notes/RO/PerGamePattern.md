# Per-game pattern for new cryptographic games

This document describes the recommended pattern for adding a new
cryptographic game to plonk-lean, given the current state of the framework.

## Background

The framework is laid out in two tiers:

- **Framework-level state and variables** (in `RO.lean`): `state`,
  `random_oracle_state`, `want_more`, `oracle_input`, `oracle_output`,
  `adversary_result`. These are declared as `axiom`s and shared across all
  games. They support `oracle_loop`, the `adv_conv_eq_conv_adv` /
  `oracle_loop_*_lazy_eq_random_oracle` lemmas, `Program.transfer`,
  and the transfer framework.

- **Game-level state, variables, and adversary** (in `CollisionResistance.lean`):
  things like `claim_x`, `claim_x'`, and `cr_adv`. These are NOT axiomatic —
  they're *section parameters* via `variable` declarations. This means CR's
  theorems take the adversary (and its RO-disjointness) as parameters, so they
  apply to *any* RO-disjoint adversary.

Why this split? The framework axioms encode "every game shares the same
random-oracle setup, with the same scratch variables." Refactoring them out
would buy little (since the framework setup is genuinely shared) at high cost
(framework defs/proofs touch them pervasively, and Lean doesn't auto-apply
section variables to function references). The medium refactor in
[the parameterize-over-adv commit](../README.md) parameterizes the *game-level*
adversary, which is where new wrappers actually need flexibility.

## Adding a new game — the pattern

Suppose we're adding a new game `MyGame` with:

- An adversary `myAdv : Program state Unit` that may write some game-specific
  state variables and read/write `oracle_input`/`oracle_output`/`want_more`.
- Game-specific Variables, e.g., `myVar1 : Variable Foo`, `myVar2 : Variable Bar`.

### Step 1. Declare game-specific Variables (still axiomatic)

```lean
import PlonkLean.CollisionResistance  -- or just RO.lean if not building on CR

axiom myVar1 : Variable Foo
axiom myVar2 : Variable Bar

axiom disjoint_myVar1_ro : disjoint myVar1 random_oracle_state
axiom disjoint_myVar2_ro : disjoint myVar2 random_oracle_state

attribute [instance] disjoint_myVar1_ro disjoint_myVar2_ro
```

Yes, these are axiomatic. Until the state-polymorphism refactor (deferred —
see below), this is how new variables are added. Disjointness with each
framework variable that you actually use must be axiomatized.

### Step 2. Parameterize the adversary

```lean
section MyGameSection

variable (myAdv : Program state Unit)
variable (h_myAdv : myAdv.inRange random_oracle_state.compl.range)
```

The adversary and its RO-disjointness are section *parameters*, not axioms.
Theorems in the section that mention `myAdv` auto-bind it; theorems that need
`h_myAdv` for their proofs add `include h_myAdv in` before the theorem signature.

### Step 3. Define the game and prove things

```lean
noncomputable def myExperiment (init : ...) (oracle : ...) : Program state Bool := do
  init
  -- the game's structure, using myAdv, framework variables, oracle, etc.
  ...

include h_myAdv in
theorem myExperiment_bound (...) : ...
  -- proof, using lemmas about myAdv via h_myAdv where needed
```

Closure under bind (from `Program.transfer_bind`) plus the framework's
`Program.transfer_lazy_init` / `Program.transfer_lazy_query` base cases give
you `cr_transfer`-style lazy/eager bridges for free as long as you can decompose
your experiment into RO-disjoint pieces and lazy_query calls.

### Step 4. Close the section

```lean
end MyGameSection
```

The exported theorems now have `myAdv` (and `h_myAdv` where needed) as
parameters. Future code can instantiate them with any adversary.

## What this pattern gives you

- **Adversary polymorphism**: theorems work for any RO-disjoint adversary.
- **Wrapper-friendly**: a wrapper around `myAdv` is just another instance of
  `myAdv'` you can pass to the same theorems. No cheat axioms required.
- **Composable**: the transfer framework (`Program.transfer`) is closed under
  bind, so structural composition of RO-disjoint pieces + queries gives
  lazy/eager equivalence automatically.

## What this pattern doesn't give you

- **Game isolation**: `myVar1`, `myVar2` axioms are visible globally. A second
  game that doesn't care about MyGame still sees these names in its namespace.
  This is the remaining "state pollution" pain — see below.

## Deferred: state polymorphism

A larger refactor (deferred) would make `state` itself a type parameter,
moving framework variables (`random_oracle_state`, etc.) and game variables
(`myVar1`, etc.) into a per-game record or typeclass. This would eliminate
all axioms in favor of per-game instances.

The reason it's deferred: the framework defs (`lazy_init`, `convert`,
`lazy_query`, `oracle_loop`, etc.) reference framework variables ~200 times
in `RO.lean` alone, and Lean does not auto-apply section variables to
function references. So every use becomes `lazy_init V` (where V is the
bundle), inflating the proof code substantially. Until we have ≥2 distinct
games that motivate the shape of the polymorphism (e.g., different state
representations or different framework-variable sets), the cost outweighs
the benefit.

When that motivation arrives, the leading candidate designs are documented
in the chat history of the 2026-06-03 session (see project memory). Briefly:

- **Bundle structure (option 3)**: one `ROVars state` structure, pass V
  explicitly. Cleanest at the type level; most verbose at call sites.
- **Typeclass (option 4)**: one `ROFramework state` typeclass; Lean's
  instance-resolution auto-fills. Cleanest at call sites; tripped over
  elaboration corner cases in the prototype.
- **Concretize the framework state (option 1)**: state becomes a record;
  framework variables are real lenses (no axioms, no parameters). Loses
  per-game state separation but no axioms.

## Reference

`PlonkLean/RO/CollisionResistance.lean` is the canonical worked example. Read
its outline (the `section CRParam` block; `cr_adv` and `h_cr_adv` parameters;
`include h_cr_adv in` annotations) for the template.
