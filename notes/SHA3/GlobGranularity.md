# Evaluation: EasyCrypt's `glob M` through granularity

Date: 2026-11-01. Branch: `sha3`. This came up while proving `GIdeal_Collision_RO`, the second
game hop of `IndifRO_is_secure.coll_resistant_if_indifferentiable`.

## The question

EasyCrypt's `call{1} (S_ll RO _)` runs the abstract `S(RO).init` on the left only. The relation
after it, EasyCrypt's `={glob A, Bounder.bounder, Counter.c}`, must survive that run. The
statement says `S <: SIMULATOR {-Bounder, -A}`, which the port translates as
`FVP.fvP S ≤ (… ⊔ FVP.fvP A)ᶜ`.

We need a frame lemma: a run confined to `fvP S` leaves A's content
(`(fvP A).touched_getter`) unchanged.

- The framework proves this frame only for regions with a reset
  (`Lib.RO.Instantiate.inFootprint_preserves_touched`, hypothesis `Footprint.HasReset`).
- Lens regions have a reset (`Lens.footprint_hasReset`).
- `fvP A` is not known to have one.

Can we assume a granular state instead, as suggested?

## Verdict

Yes, with one convention change.

- Granularity gives `glob A` as a lens region: the granular cover of `fvP A`, which is the set of
  variable slots A touches, whole. Lens regions frame.
- The restriction between two abstract modules has to be stated against that cover: `fvP S ≤ (glob A)ᶜ`.
  This is exactly EasyCrypt's `{-A}`, which means "no common variable".
- Today's `fvP S ≤ (fvP A)ᶜ` is weaker than EasyCrypt's, and no frame lemma follows from it alone.

## 1. Footprint-disjointness does not frame (proven)

`CounterExamples/FramingNeedsReset.lean`, `framing_fails` (standard axioms):

- The program `qProg`, built on the lazy flip `qKer`, lies in `R = Footprint.from {qKer}`.
- `F = qCentralizer = Rᶜ` satisfies `F ≤ Rᶜ`.
- Yet `qProg` moves `false` to `true` with probability ½, and `F`'s `touched_getter` separates the two.

So "`p` confined to `R`, `F ≤ Rᶜ` ⇒ `p` keeps `F`" is false for general footprints. `F` here has
no reset (`qCentralizer_not_hasReset`).

**Does this happen for `FVP.fvP` of real code?** It is open.

- The example lifts into the slot of a `Bool` variable, where it is sub-granular.
- A statement can sample from a state-dependent distribution: `v <$ (if $v then bias else fair)` *is* `qKer`.
- Whether `fvP` (a join of getter and setter footprints, reduced and extended) can ever be such a
  region would need a characterization of all footprints FV produces.

That is research, and it may fail. So option (a), "prove the frame for `fvP`-disjoint
sub-granular modules", is not a plan we can schedule.

**Even with granularity, `fvP`-disjointness is too weak.** Take a variable `v : Bool × Bool`.
`A` may use only `v.1` and `S` only `v.2`. Their footprints are disjoint, but both touch the grain
`v`, so `S` can change `glob A` (the cover contains all of `v`). This case is not formalized: it
needs two disjoint sub-lenses of one slot. It is the reason the restriction must be stated at
grain level.

## 2. What granularity gives (proven)

All four results below are in `Logic/Granular.lean`, standard axioms only:

| Lemma | Statement |
|---|---|
| `variableGranularity` | A `GranularProgramSpec` whose grains are the slots of the variables of nontrivial types. It is a definition, with no new hypothesis. |
| `Footprint.FinitelySupported.isSubGranular` | `Module.ECModule`'s finite support (E2/E6) makes the footprint sub-granular. So every EasyCrypt-like module already has a cover, `glob`, and `ECModule` does not change. |
| `ProgramDenotation.preserves_touched_of_fromLens` | A run confined to `R` keeps the content of any lens-derived `Q ≤ Rᶜ`. A cover is lens-derived (`GranularFootprint.footprint_fromLens`, in the framework). |
| `Footprint.IsSubGranular.granularCover_le_compl` | `fvP A ≤ Gᶜ` for a grain `G` (a whole variable) gives `glob A ≤ Gᶜ`. So restrictions against *concrete* variables (`{-Bounder}`, `{-RO}`, …) carry over to covers with no change. |

## 3. The convention it needs

- **`glob`.** Define `Footprint.glob F` as the granular cover of `F` (under `variableGranularity`)
  when `F` is sub-granular. Otherwise it is `⊤`, which is conservative: `X ≤ ⊤ᶜ` forces `X = ⊥`.
- **Restriction between two abstract modules.** EasyCrypt's `X <: T {-Y}`, for an abstract `Y`,
  becomes `FVP.fvP X ≤ (Footprint.glob (FVP.fvP Y))ᶜ`.
  - It says "X touches no variable Y touches". That is symmetric and equals EasyCrypt's
    variable-level disjointness.
  - It implies the current form, since `fvP Y ≤ glob Y`. So every proof done so far
    (`Collision_FM_GReal`, the swaps) still goes through, and `fp_disjoint` needs only the lemma
    `fvP Y ≤ glob Y`.
- **Restrictions against concrete variables** are unchanged.

**Scope.** 52 hypotheses in the port relate two abstract modules; the per-file counts are below.
Only 3 need the stronger form today: the `∃ S {-A}` premises of the three lemmas of
`IndifRO_is_secure`.

- `IndifRO_is_secure`: 13
- `SLCommon`: 10
- `Gcol`: 6
- `Gconcl_list`: 6
- `Gext`: 4
- `Handle`: 4
- `ConcreteF`: 3
- `SHA3Indiff`: 2
- `Gconcl`: 2
- `SHA3_OIndiff`: 1
- `Sponge`: 1

The other one-sided calls in SHA-3 don't need it:

- SLCommon's three `call{2}`s come after a bad event. They only frame `C.c`, a lens region.
- Gconcl's `call{1}` is the concrete `RRO.resample`. It only frames concrete variables.

**Dischargeability.** The premises are discharged where SHA3Security provides `Simulator`.

- They need `fvP Simulator ≤ (glob A)ᶜ` from A's concrete restriction `{-Simulator, …}`.
- That follows from `granularCover_le_compl` once `fvP Simulator` is bounded by its variables.
- The current `fvP`-level form needs that same bound. It is the pending item "show `ECModule` for a
  concrete module". So the stronger form costs nothing extra at instantiation.

## 4. Two prerequisites of the second hop that granularity does not touch

Both are recorded here because they surfaced in the same analysis.

- **Countable oracle arguments.** The abstract-call rule needs countable oracle argument types
  (`Tooling.md`). In `IndifRO_is_secure` that is `f_in`, a type variable with no `Countable`. It
  needs `[Countable f_in]`. The SHA-3 instance (`List Bool`) satisfies it. This is a new
  exception-level assumption: EasyCrypt types are not required to be countable.
- **One oracle state lens.** The oracle state `(Bounder.bounder, Counter.c, RO.m)` must be a single
  lens (`Lens.pair`) for the abstract-call rule. The generic theory's variables are lens
  parameters (E4), with no disjointness. That needs `Lens.Disjoint` hypotheses among them, which
  EasyCrypt has for free: distinct variables. A clone instantiating them with `global_var`s
  discharges them by instance search.

## 5. Alternatives considered

| Option | Why it falls short |
|---|---|
| **Frame lemma for `fvP`-disjoint sub-granular modules** | Not provable from what we have (section 1). It is false for general footprints and open for FV-derived ones. |
| **`ECModule` requires `fvP` to be *granular* (exact union of slots)** | Not dischargeable. A module reading only `v.1` has a footprint strictly inside `v`'s slot. |
| **Restate everything with variable lists** (EasyCrypt literally: an abstract module carries its variables) | Equivalent in strength to the proposal, but it changes every abstract-module hypothesis, the abstract-call rule's interface, and E2. Granularity reaches the same lens regions through the existing `fvP`. |
| **Leave the 3 lemmas `sorry`** | Possible, but `coll_resistant_if_indifferentiable` and its two siblings are on the path of the headline `SHA3Security` results. |

## 6. Recommendation

1. Adopt `glob` through `variableGranularity`, and translate a restriction between abstract
   modules as `FVP.fvP X ≤ (Footprint.glob (FVP.fvP Y))ᶜ`. Record it as an exception (E2 refined).
2. Apply it uniformly to all 52 hypotheses, not just the 3 that need it now.
   - The change is mechanical, and one rule is easier to audit than a mixed convention.
   - Any later frame argument (a one-sided call, an up-to-bad oracle against an abstract module's
     state) then finds the hypothesis it needs.
   - The minimal variant (3 hypotheses) is a valid fallback if fewer statement changes are preferred.
3. Add `[Countable f_in]` and the `Lens.Disjoint` hypotheses for the generic theory's variables
   where the abstract-call rule is used. Record them too.
4. Then prove `GIdeal_Collision_RO`:
   - frame `S(RO).init` against `glob A` and the lens regions `bounder`, `c`;
   - after that, weaken to `fvP A` (`Footprint.touched_getter_eq_of_le`);
   - then use the existing abstract-call rule, with oracle state `(bounder, c, m)`.

**Risks.**

- `glob` depends on the choice of granularity. `variableGranularity` is the canonical one, and
  nothing else in the framework instantiates `GranularProgramSpec`.
- The proposal does not settle option (a). It sidesteps it, as EasyCrypt does, by restricting at
  variable level.
