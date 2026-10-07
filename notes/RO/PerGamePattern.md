# Per-game pattern for new cryptographic games

This document describes the recommended pattern for adding a new
cryptographic game to plonk-lean, given the current state of the framework.

## Background

The framework is laid out in two tiers:

- **Framework-level state and variables** (`Lib/RO/Basic.lean`,
  `Lib/RO/OracleLoop.lean`): `state` (= `VariableAssignment`, the globals),
  `random_oracle_state`, `want_more`, `oracle_input`, `oracle_output`,
  `adversary_result`. These are global variables declared with `global_var`
  (see Step 1) and shared across all games. They support `oracle_loop`, the
  `adv_conv_eq_conv_adv` / `oracle_loop_*_lazy_eq_random_oracle` lemmas,
  `Program.transfer`, and the transfer framework.

- **Game-level variables** (e.g. `claim_x`, `claim_x'` in
  `CollisionResistance.lean`): also `global_var`s.

- **Adversaries** (e.g. `cr_adv`): *section parameters* via `variable`
  declarations. This means CR's theorems take the adversary (and its
  RO-disjointness) as parameters, so they apply to *any* RO-disjoint
  adversary.

Why this split? The framework variables encode "every game shares the same
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

### Step 1. Declare game-specific variables

```lean
import GaudisCrypt.Lib.RO.CollisionResistance  -- or just Lib.RO.Basic if not building on CR

global_var myVar1 : Foo
global_var myVar2 : Bar
```

`global_var x : T` (in `Language/Variables.lean`) defines
`x : Lens T VariableAssignment` as the slot of the variable `⟨"N.x", T⟩` in the
globals, `N.x` being the full name of the declaration (`T` must be
`Nonempty`). No axioms: any two `global_var`s are disjoint by instance search,
in both directions (`Lens.IsGlobalVar.instDisjoint`), and so are their
`intoGlobal` lifts. A named disjointness fact, where a proof wants to cite one,
is `theorem disjoint_myVar1_ro : Lens.Disjoint myVar1 random_oracle_state :=
inferInstance`.

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

- **Game isolation**: `myVar1`, `myVar2` are declarations visible globally. A
  second game that doesn't care about MyGame still sees these names in its
  namespace (they cannot clash with its own variables' slots, though: slots
  are named by full declaration names). See below.

## Deferred: state polymorphism

A larger refactor (deferred) would make `state` itself a type parameter,
moving framework variables (`random_oracle_state`, etc.) and game variables
(`myVar1`, etc.) into a per-game record or typeclass. (This was originally
also meant to eliminate the variable axioms; `global_var` has done that.)

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
  framework variables are concrete lenses (no axioms, no parameters). Loses
  per-game state separation but no axioms. (The `global_var` scheme is a
  variant of this, with `VariableAssignment` as the record.)

## Reference

`GaudisCrypt/Lib/RO/CollisionResistance.lean` is the canonical worked example. Read
its outline (the `section CRParam` block; `cr_adv` and `h_cr_adv` parameters;
`include h_cr_adv in` annotations) for the template.
