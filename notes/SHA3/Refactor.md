# Refactor plan: EasyCrypt → Gaudí, one to one

Agreed 2026-11-06, after the SHA-3 port was completed (no `sorry`).

## Goal

The project's point is that EasyCrypt formalizations can be transpiled to Gaudí in a very
close, almost one-to-one way.  Proofs may differ in detail, but each EC lemma should have:

* a Lean statement that reads like the EC statement (`equiv[ … ]`, `hoare[ … ]`, `phoare[ … ]`,
  `Pr[ … ]`, `islossless`), with no hypotheses EC does not have;
* a proof that is a pRHL / Hoare / pHL tactic script, without term-mode rule applications,
  denotational reasoning or footprint bookkeeping, and without auxiliary lemmas for steps EC
  does inline (oracle steps of `call (: inv)`, frames, restrictions).

## Measuring it (phase 0)

`scripts/ec_fidelity.py` reads `Mapping.md` and the Lean files and reports per file (the
classification is syntactic, a trend indicator).  `--list raw|term|den|fp|overhead|aux` lists
the lemmas in a category.

Baseline (2026-11-06, commit after cdb44ca):

| | count |
|---|---:|
| EC lemmas / equivs | 421 |
| of which judgments (equiv/hoare/phoare/Pr/islossless) | 153 |
| judgment statements in surface syntax | 0 |
| judgment proofs that are clean tactic scripts | 33 (+15 reuses of an identical proof) |
| proofs with term-mode rule applications | 64 |
| proofs with denotational reasoning | 21 |
| proofs with footprint bookkeeping | 74 |
| statements with hypotheses EC lacks | 103 |
| EC rows marked `exc` | 43 |
| auxiliary theorems (no EC row) | 778 |

Other indicators: 118 `set_option maxHeartbeats`; `fp_disjoint` 319×, `fp_module` 128×.

EC tactic usage in the SHA-3 sources (prioritizes phase 3): `auto` 1976, `smt` 1376, `sp` 1037,
`if` 889, `inline` 862, `proc` 783, `case` 534, `call` 321, `rcondt` 287, `sim` 274, `while` 267,
`conseq` 252, `wp` 231, `rcondf` 182, `seq` 121, `byequiv` 101, `rnd` 77, `swap` 63,
`splitwhile` 35, `transitivity` 33, `alias` 25, `bypr` 10, `byphoare` 10, `fel` 8,
`symmetry` 6.  Missing in Gaudí today: `auto`, `sp`, `conseq`, `rcondt`, `splitwhile`,
`transitivity`, `alias`, `bypr`, `byphoare`, `fel`, `symmetry`, `unroll`.  Different
conventions: `inline` by call-site index (EC: by name), `equiv_seq` counts trailing statements
(EC: leading), `call` neither frames unwritten variables nor discharges footprints.

## Phases

1. **Statement layer** (`Syntax/`): `Pr[ G.main() @ m : res ]`; `equiv[ M.f ~ N.g : P ==> Q ]`
   over module applications (`A(B).f`), `={glob A}`, `res`; `hoare[ M.f : P ==> Q ]`,
   `phoare[ M.f : P ==> Q ] = r`, `islossless M.f` over procedures; delaborators so goals print
   the EC way.
2. **Module declarations**: `declare module D <: T {-M₁, -M₂}`, `declare axiom D_ll : …`,
   `local module` variables — section variables plus one bundled hypothesis, hiding
   E2/E6/E7/E13 behind one mechanism and removing the `unfold …; obtain …; have h : … ≤ …ᶜ`
   preambles.
3. **Tactics with EC behaviour**, on the judgment registry, by EC usage: `auto`/`sp`,
   `inline M.f` by name, `call (: inv)` (abstract and concrete), `rcondt`/`rcondf`, `sim`,
   `conseq`, `seq n m : P` (leading count), then the rest.  The make-or-break part: `call`/`sim`
   discharge footprint side conditions and frame unwritten variables themselves.
4. **Rewrite the proofs** file by file, leaves up: oracle-step lemmas fold back into `call`
   bullets; denotational proofs are replaced by small library rules (retiring E9, E10, E12 via
   `bypr`).
5. **Retire the remaining exceptions**: E2 (representability of every module, by induction over
   normal forms), E14 (a `glob` lower bound for wrapper modules), E11, E8.  Some may touch
   `Language/` (Dominique).
6. **Framework hygiene**: consolidate `Logic/` (≈50 files: `PRHL`/`PRHL2`/`PRHLStmt`/`PRHLWp`,
   `AbstractCall*`, `EqualOutside`, `EagerRhl`, `TransferBy`, …) into one EC-shaped logic layer,
   legacy to `Attic/` after checking dependents; heartbeats and build time.
7. **(Optional) transpiler**: `.ec` → Lean skeletons (definitions, modules, statements), checked
   by regenerating the SHA-3 skeleton and diffing against the hand port.

Order: a vertical pilot first — one short file with equivs, `Pr` statements and abstract calls
(`SecureRO.eca` or `SHA3_OIndiff.ec`) pushed to near one-to-one form, building only the syntax
and tactics it needs; measure; then widen.

## Open decisions

1. Tactic names: EC names verbatim (scoped, e.g. inside an EC tactic block) or the
   `equiv_*`/`hoare_*` family with EC behaviour.
2. `Language/` is off-limits: coordinate E2 (option B) / E14 changes with Dominique, or work
   around them.
3. Branch: refactor on `sha3`, or a new branch off it (old proofs kept until replaced).
4. Transpiler: a deliverable, or is "close enough to transpile by hand" the bar.
5. Auxiliary lemmas: zero as the goal, or fine when separated and judgment-tactic only.
