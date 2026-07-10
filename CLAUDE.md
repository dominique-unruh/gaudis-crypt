# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

Last systematic update of this file: 2026-06-30

## What this is

Gaudí's Crypt is a Lean 4 framework for **cryptographic proofs** (probabilistic
relational reasoning, random-oracle indistinguishability, game hopping). It is
research-stage and lightly documented. The project is named after the *crypt* of
Gaudí's Church of Colònia Güell with its *lean*ing pillars.

Lean toolchain: `leanprover/lean4:v4.30.0` (see `lean-toolchain`). Depends on
mathlib `v4.30.0`, `doc-gen4`, and `Metatheory-Unruh`
(github.com/dominique-unruh/Lean-Metatheory).

## Build / develop

- `lake build` — build everything (or `make build`).
- `lake build GaudisCrypt.Logic.PRHL.Core` — build a single module. Use the
  dotted module path matching the file path under the repo root. Prefer this
  for fast iteration over a full `lake build`.
- `make update` — one-stop refresh after changing `lean-toolchain` or the
  `[[require]]` deps in `lakefile.toml`: installs the toolchain, runs
  `lake update`, fetches the mathlib cache (`lake exe cache get`), then builds.
  Run this (or at least `lake exe cache get`) before a first build so mathlib
  comes from cache instead of compiling from source.
- `lake clean` / `make clean`.

There is no test suite and no separate lint step — correctness *is* the build
(a green `lake build` means all proofs check). `lakefile.toml` enables mathlib's
standard linter set via `weak.linter.mathlibStandardSet`.

### Lean LSP tooling (MCP)

The `lean-lsp` MCP server is available and is the right way to interact with
proofs: `lean_goal` (proof state at a position), `lean_diagnostic_messages`
(errors/warnings for a file), `lean_hover_info`, `lean_multi_attempt` (try
tactics without editing), and the search tools (`lean_local_search` first, then
`lean_leansearch`/`lean_loogle`/`lean_state_search`). The MCP does **not** edit
files — use Edit/Write for that. `lean_build` restarts the LSP and is slow; only
use it after adding imports.

## Architecture

The dependency flow is **Language → (range framework) → Logic / Lib**.
`GaudisCrypt.lean` is the barrel importing every module.

### `GaudisCrypt/Language/` — the programming language

- `SubProbability.lean` / `Semantics.lean` — `SubProbability` (a measure of
  total mass ≤ 1, modelling possibly-failing computation) and the core program
  type `Program s a := StateT s SubProbability a`, i.e. `s → SubProbability (a × s)`.
  Monad primitives: `pure`, `bind`, `Program.uniform` (sample a finite type,
  no state change), `Program.get`/`Program.set` (read/write a lens).
- `Lens.lean` — `Lens a m` (get/set with the three lens laws), `Getter` (read-only
  lens), lens `disjoint` (sets commute), and `Lens.compl` (complement lens).
- `Programs.lean`, `Syntax2.lean`, `Modules.lean` — program/procedure syntax,
  procedures with holes, and module expressions.

### The range framework (state-footprint analysis)

This is the conceptual core. `notes/REPORT.md` is a long, excellent guided tour —
**read it before working in this area.** Key types and definitions:

- `LensRange m` — a "region of memory" as a *bicommutant-closed* submonoid of
  `m → m` (the von-Neumann-algebra trick). Forms a complete lattice; complement
  `Rᶜ` is the commutant. Lenses give rise to lens-ranges, but not every range is
  lens-derived (that's why we work with `LensRange`, not `Lens`, for joins/meets).
- `Program.inRange p R` — "`p` only touches `R`", defined as `p` commuting with
  every deterministic update in `Rᶜ`. Compositional: `inRange_bind`,
  `inRange_pure`, `inRange_mono`, plus primitives `inRange_set/get/uniform`.
- `Program.range p := sInf { R | p.inRange R }`, and `Program.glob` (a `Getter`
  onto the part of state a program touches — finer than EasyCrypt's `glob`).
- Headline theorem `Program.commute_of_disjoint` (+ the `_lens` wrapper that
  discharges the `HasOrbitCollapse` hypotheses automatically for lens-derived
  ranges): disjoint footprints ⟹ programs commute.

Note `Language/Footprint`/`ProbProgramRange`/`ProgramRange`/`DetermFootprint`/`FV`/
`WeakestPreconditions` make up this framework. `WeakestPreconditions.lean` provides `wp`, `wp_bind`, `wp_set`, etc.

### `GaudisCrypt/Logic/PRHL/` — probabilistic relational Hoare logic

`Core.lean` (judgments), `Coupling.lean`, `Lenses.lean`, `Loops.lean`,
`Prhl.lean`, `Tactics.lean`, `UpToBad.lean`. This is the relational reasoning
layer used to relate two games. `PRHL2*.lean` are a newer/alternate iteration.
Two further relational calculi live directly in `Logic/`:
`EquivModuloLens.lean` (wp-equality on posts that ignore a lens) and
`TransferBy.lean` (the generic "sliding coupling" `transferBy`, instantiated
by the RO library).

### `GaudisCrypt/Lib/RO/` — random-oracle library (main application)

Lazy-vs-eager random-oracle indistinguishability and downstream games. The
framework lets the adversary's *only* assumption be a single structural fact —
its footprint is disjoint from the oracle's state — from which the commutativity
"axioms" become theorems. `Basic.lean` has the RO primitives (`lazy_query`,
`random_oracle_query`, `convert`, …); `ROEquiv.lean`/`TransferConvert.lean`/
`OracleLoop.lean` build the lazy = eager equivalence (on the generic `transferBy`
calculus in `Logic/TransferBy.lean`); `OneWayness*`,
`CollisionResistance`, `Switching`, `QueryHit` are concrete games.
`Lib/Enc/HashedOTP.lean` is an encryption example.

### `GaudisCrypt/CounterExamples/`

Standalone theorems showing framework limits (e.g. `LeastLens` — two lenses
whose least upper bound doesn't exist as a lens). Not used elsewhere.

## Conventions and gotchas

- **The `notes/` directory uses the old project name** (`PlonkLean/...` paths,
  the `.idea` module is `plonk-lean`). The code now lives under `GaudisCrypt/`.
  When following a note, translate `PlonkLean/X.lean` → `GaudisCrypt/X.lean`.
- **`RENAME.md`** tracks in-progress renamings (e.g. `Program` → `Denotation`).
  Check it before introducing names in the
  range framework so you match the intended direction.
- **Per-game pattern**: `notes/RO/PerGamePattern.md` documents how to add a new
  cryptographic game. Framework-level state/variables (`random_oracle_state`,
  etc.) are shared `axiom`s; game-level adversaries and variables are
  `variable` section parameters so theorems apply to *any* RO-disjoint adversary.
  New game variables are still declared axiomatically with axiomatized
  disjointness, marked `attribute [instance]`.
- `Test.lean` / `Test2.lean` are untracked scratch files, not part of the build.

### Name spaces, file names, naming convention

(Note: we currently don't follow this convention, but will transition to it.
New content should use it.)

* Files are named after the topic they introduce, singular preferred. (E.g., `Lens.lean`.)
* All our files use namespace `GaudisCrypt`.
  (Except for the files under `CounterExamples` and `Attic` which can deviate from that.)
* All types (such as `Lens`, `Procedure`) are defined directly inside `GaudisCrypt`.
* Theorems, definitions, etc. that relate to an existing type `T` in some way are in the subnamespace `GaudisCrypt.T`. (E.g., `Lens.compl` for lens complements or `Lens.master_theorem` for some master theorem about lenses.)
* Theorems/definitions that are not prefixed by a type (e.g., because they don't really "belong" to a given type) are named with project-wide unambiguity in mind. (Exception: private theorems/definitions.)
* Names follow the Mathlib-style (e.g., concerning capitalization etc.).
* Directory `GaudisCrypt/Attic/` is for content that is obsolete but kept anyway.
  Only files from `Attic/` or from `CounterExamples/` may import files from `Attic/`
* Directory `GaudisCrypt/CounterExamples/` is for counterexamples that are not needed for the main
  development. Only files from `CounterExamples/` may import files from `CounterExamples/`


## Docs / GitHub Pages

`scripts/build-gh-pages.py` (`make publish-docs`) builds the Jekyll site under
`docs/website/` plus doc-gen4 API docs and publishes to the `gh-pages` branch.
Slow. See `docs/gh-pages.md`. The `DocEntrypoint` lean_lib in `lakefile.toml`
exists only for this script.
