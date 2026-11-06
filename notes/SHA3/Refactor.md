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

## Decisions (Denis, 2026-11-06)

1. **Tactic names**: keep the prefixed families (`equiv_*`, `hoare_*`, `phoare_*`, `stmt_*`), but
   reuse one machinery behind them so the number of tactics does not grow as
   steps × judgments (`phoare_wp`/`hoare_wp`/`equiv_wp` = one step, the judgment registry).  EC
   behaviour is reasonable to match, but not a goal in itself: where EC does something
   unreasonable or we can do better, deviate (and document it).
2. **Branch**: `ec-fidelity`, off `sha3`; old proofs are kept until each file is replaced.
3. **Pilot**: `SecureRO.eca`.

Still open: coordination with Dominique on `Language/` changes (E2 option B, E14); whether a
mechanical transpiler is a deliverable; the target for auxiliary lemmas.

## Pilot: `SecureRO.eca`

EC's three proofs share one shape: `byequiv; proc; inline*; sim` to a variant game, then
`byphoare (: arg = h ==> _)`, pHL's five-bound `seq 1 : E p₁ p₂ p₃ p₄ I`, a Hoare
`call (: inv)` on the adversary, `call (: true ==> E); bypr; fel 1 cntr f bound E [O: pre] inv`,
and the last query by `rnd (pred1 h)`, `hoare`, `rcondt`/`rcondf`, `swap`, `case`.

Today's Lean: the modules take eight explicit parameters (types, ops, three lens variables);
`fel` is a hand-made supermartingale per game (`preimagePotential` + step + tail lemmas, reused
by `SecureORO`); the `seq`/`byphoare` steps are `ewp` rewriting; 52 auxiliary theorems.

Missing pieces, in order:

1. **Statements**: `Pr[ M(A, F).main(x) @ m : E ]`; module-application subjects
   (`Preimage(A, RO).main`, via the module command's callee parser) in `equiv[ ]`, `hoare[ ]`,
   `phoare[ ]`, `Pr[ ]`.
2. **Theory parameters bundled** (as in `Gconcl_list`/`SHA3Security`): a `Params` class (types'
   ops and axioms) and a class of the theory's module variables (lenses + disjointness), so
   modules are applied to their module arguments only.
3. **`declare module A <: AdvPreimage {-RO, -Preimage}`**: variable + one bundled hypothesis.
4. **Rules + tactics**: `byequiv`, `byphoare`, `bypr`; pHL's five-bound `seq`; `fel` as a
   library rule with EC's premises (derived once from `Module.ewp_app_le`), retiring the three
   per-game potentials; `rcondt`/`rcondf`, `case`, `rnd (pred1 _)` shared by hoare/phoare.
5. **Rewrite** `SecureRO` (then `SecureORO`, its twin) and measure.

### Status

* **Step 1 done (2026-11-06).** Checked first: no `Pr[ ]` and no EC module paths existed; the rule
  lemmas did (`Procedure.Pr_of_phoareProc` = `byphoare`, `Procedure.Pr_eq_of_prhlProc`/`_le_`/
  `_abs_sub_le_…_upto` = `byequiv`), so only syntax was added:
  * `Syntax/PrSyntax.lean`: `Pr[ M (a₁, …, aₙ) @ &m : E ]`, a real (`NNReal.toReal` of
    `Procedure.Pr`, EC's `Pr` is real); `M` and `E` read as in `phoare[ M : … ]` (`§res`, `§x`);
    prints back.
  * `Syntax/ModuleApplicationSyntax.lean`: `M(A, B(C)).f` = the accessor `T.f` of
    `Module.app M (Module.pair A (Module.app B C))` (or `M.f` for a single-procedure module),
    accepted wherever a term is (so in all judgment subjects); prints back.  `atomic`, so EC's
    `M.f(x)` in `Pr[ ]` still reads as the procedure and its arguments.
  * Heads must be names: needs step 2 for the SHA-3 modules (they take Lean parameters today).
* **Step 2, `Preimage` slice done (2026-11-06)**: `Examples/SHA3/Pilot/SecureRO.lean` (parallel to the
  old file, whose generic `FMap`/potential lemmas it reuses), no `sorry`, axioms clean.
  * Theory ops + axioms: `class Params (from to : outParam Type)` — the outParams let `bound`,
    `sampleto` … resolve with no types written (EC's clone semantics: the instance is the clone).
  * Module variables: `global_var`s (`Counter.c`, `Bounder.bounder`), disjoint by instance search:
    every `Lens.Disjoint` hypothesis and `have := (…).symm` line is gone.  `RO.m`, whose type
    mentions only the types, is a `global_var` written out with the `[Params]` binder (so `RO.m`
    alone fixes its types); `global_var` (in `Language/`) could take instance binders — to raise
    with Dominique.
  * Types explicit for `moduletype`s, then `variable {from to}`: modules are names.
  * EC's module-type subtyping (`A(Bounder(F))`: an `RF` where an `Oracle` is expected; `RO` where
    an `RF` is) is a `Coe` instance whose body is a `fun` building the record — the coercion then
    unfolds to the record the `module` command reads callees back from.  For that, a path's
    arguments are elaborated without expected type, `(aᵢ :)`, and coerced.
  * Statement: `Pr[ Preimage(A, RO).main (h) @ &m : §res ] ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto h`
    (EC: `Pr [ Preimage(A,RO).main(h) @ &m : res ] <= (bound + 1)%r * mu1 sampleto h`); `mu1`
    added to `Lib/EC/Distr.lean`.  Left: the `declare module` hypotheses (`ECModule`, footprint),
    step 3.
  * Printing gap: a coerced argument prints as its record (`RF.mk { init := …, get := … }`), not
    as `RO`.  A delaborator recognising "record of one module's own fields" would print it back.
  * **Step 3 done**: `Logic/DeclareModule.lean`, `declare module A <: AdvPreimage «from» «to»
    {-RO, -Preimage}` = `variable (A : …) [Module.Declared A S]`, `S` computed: the
    `global_var`s the code of each `-X` mentions (EC's `glob` of a concrete module), `glob X` for
    a declared `X`.  `Module.Declared` (finite support + restriction, `S` an `outParam`) is an
    instance-implicit section variable, so it is part of exactly the lemmas mentioning `A` (EC's
    generalization at the section's end); `fp_disjoint` reads it.  Representability (E2) is no
    longer assumed: `Module.Declared.ecModule A Oracle.ext` proves `Module.ECModule` from
    `Module.representable_of_firstOrder`, side conditions by auto-params.  The statement now has
    EC's hypotheses only.
  * **Step 4 started**: `Logic/PrTactics.lean`, `byequiv` and `byphoare` on `Pr[ ]` goals (real
    probabilities: small `toReal` bridges over `Procedure.Pr_eq_of_prhlProc`/`_le_`/
    `Pr_of_phoareProc`).  Without a term they leave the judgment with EC's defaults (`={arg,
    glob}` / `arg = a ∧ glob = m`, events related, bound `ENNReal.ofReal x`); with a term the side
    conditions, tried by `rfl`/`trivial`/`simp_all`/`positivity`.  The pilot's main theorem is
    now `calc … := by byequiv (Preimage_Preimage2 A); _ ≤ … := by byphoare (Preimage2_le A); <EC's
    arithmetic>` (EC: `have->: … by byequiv; …; byphoare …`).
  * All the section's statements are in surface syntax (`phoare[ … ]`, `equiv[ … : ={hash,
    allGlobals} ==> ={res} ]`, `Pr[ ]`): no raw `phoareProc`/`prhlProc`.  Deviation: parameter
    names are written at the triple (`Preimage.FEL(A, RO).main (hash)`), since `knownParamNames?`
    (`Syntax/HoareSyntax.lean`) does not look through `Module.app X …` to `X`'s procedure — to
    fix with the next batch of `Syntax/` changes (each costs a full rebuild).
  * Proofs of `Preimage2_le`/`FEL_preimagePotential` are still the old ones (term-mode `fel` via `Module.ewp_app_le`, `show`, `ewp`
    arithmetic): steps 3–4.
