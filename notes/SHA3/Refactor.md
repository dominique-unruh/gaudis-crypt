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
  * **`fel` (step 4, part 2)**: `Logic/Fel.lean` — `Module.fel`, EC's `fel` once for all games,
    derived from `Module.ewp_app_le` on one potential (`felPotential`); the per-oracle premises
    are the structure `FelOracle` (`lt`, `step` a pHL judgment, `incr`/`same`/`keep` Hoare
    triples), proven with the judgment tactics.  Deviation: `bad` must persist (`keep`).  The
    pilot's `fel` is `FEL_rng` (EC's statement) with `Bounder_RO_get_fel` (EC's oracle bullets);
    `preimagePotential` and its step/tail lemmas are gone from the pilot.
  * **Hoare wp through conditionals with samplings/calls**: `hoare_seq_if` registered as hoare's
    `ifLemma` (`Logic/PHoareWp.lean`): a branch's outcomes off `B` have probability `0`, computed
    by the `Stmt.ewp` lemmas and turned back into a condition (`expected_eq_zero_iff`) — the
    phoare machinery reused, one implementation.
  * **pHL's five-bound `seq` (step 4, part 3)**: `Logic/PHoareSeq.lean`, rule `phoareStmt_seq_le`
    and tactic `phoare_seq n : E p₁ p₂ p₃ p₄ I` (EC's leading count, `E`/`I` in `§` syntax, goals in
    EC's order, bounds `1` closed on the spot).  The pilot's `Preimage2_le` is now EC's
    `byphoare(: arg = h ==> _); proc; seq 1 : (rng RO.m h) … (hash = h)` with bullets
    `invariant` (`hoare_call`), `first_E` (`phoare_call (FEL_rng A h)`), `second_notE` (the last
    query, EC's `rnd (pred1 h)`); `preimage_tail_le` gone.  Deviation: our `seq` counts the two
    statements `proc` adds for the argument (`seq 3`) — a `phoare_proc` like `equiv_proc_to_stmt` would
    remove that.
  * Still old-style: `Preimage_Preimage2` (by-index inlining, manual `equiv_seq`); auxiliary
    lemmas (`FEL_rng`, `Bounder_RO_get_fel`, `Preimage2_le`, `Preimage_Preimage2`) are EC's inline
    `have`/bullets — fold them in once `fel` is a tactic. (term-mode `fel` via `Module.ewp_app_le`, `show`, `ewp`
    arithmetic): steps 3–4.

### Pilot complete (2026-11-06)

`SecureRO.eca` in EC's shape: `Examples/SHA3/Pilot/SecureRO.lean` (theory, `Preimage`),
`…/SecureRO_SecondPreimage.lean`, `…/SecureRO_Collision.lean` (one file in EC; split for build
time).  All three headline theorems proven, axioms `propext`, `Classical.choice`, `Quot.sound`:

    Pr[ Preimage(A, RO).main (h) @ &m : §res ] ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto h
    Pr[ SecondPreimage(A, RO).main (mess1) @ &m : §res ] ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto default
    Pr[ Collision(A, RO).main () @ &m : §res ] ≤ ((bound * (bound - 1) + 2 : ℤ) : ℝ) / 2 * mu1 sampleto default

with EC's hypotheses only (`declare module A <: … {-…}`, `[Countable «from»]`; `[Countable «to»]`
for `RO_LRO_D`).  Each headline proof is EC's: a `calc` of `byequiv` steps (EC's `have->`), then
`byphoare` with the arithmetic.  All judgment statements are in surface syntax.  EC's `fel` is
`Module.fel` with the oracles' premises proven by `hoare_wp`/`phoare_wp` (`FelOracle`), EC's
five-bound `seq` is `phoare_seq`, EC's Hoare `call (: inv)` on the adversary is
`Module.hoare_app_inv`.  The three per-game potentials of the old file are not used; E2, E6 are
retired for this file, E8 is reduced to the `Countable` side conditions.

Measured (`scripts/ec_fidelity.py`, EC's three lemmas; aux = Lean theorems with no EC row):

| | surface statements | clean proofs | term / den / fp | extra hyps | exc | aux |
|---|---:|---:|---:|---:|---:|---:|
| old `SecureRO.lean` | 0 / 3 | 0 / 3 | 0 / 3 / 2 | 3 | 3 | 52 |
| pilot (3 files) | 3 / 3 | 3 / 3 | 0 / 0 / 0 | 0 | 0 | 24 |

The 24 auxiliary theorems are EC's inline `have`s and bullets as lemmas (the equivalences, the
`fel` premises and `fel`/`seq` statements, footprint bounds of concrete modules), plus two
`FMap` facts EC leaves to `smt`.

Machinery added on the way (all generic): `Syntax/PrSyntax.lean`, `Syntax/ModuleApplicationSyntax.lean`
(paths `M(A, B).f`, coercions as EC's subtyping, printed back), `Logic/DeclareModule.lean`,
`Logic/PrTactics.lean` (`byequiv`, `byphoare`), `Logic/Fel.lean` (`Module.fel`,
`Module.hoare_app_inv`), `Logic/PHoareSeq.lean` (`phoare_seq`), `hoare_seq_if` (Hoare wp through
conditionals with samplings), parameter names found through `Module.app` for triples, a precise
name-clash rule for printing local variables, `mu1`/`mu_ne_top` (`Lib/EC/Distr.lean`).

Still different from EC (each small, listed for the next files):
* `proc` adds the statements that copy the arguments: our `seq` counts them (`seq 3` for EC's
  `seq 1`); a `phoare_proc` like `equiv_proc_to_stmt` would remove that.
* Auxiliary lemmas where EC has inline `have`s/bullets (the equivalences, the `fel` premises as a
  `FelOracle` lemma, the `fel`/`seq` lemmas): folding them needs `fel` as a tactic.
* `Preimage_Preimage2` and the other equivalences are by-index inlining and `equiv_seq` splits,
  not EC's `inline*; sim`.
* The local modules' variables and `RO.m`/`FRO.m` are written out (`global_var` does not take
  the theory's instance); the adversary is restricted against the local modules explicitly
  (EC: fresh); `bad` must persist in `fel`.
* Named variables make disjointness slower: two raised heartbeat/recursion limits in
  `SecondPreimage`.

Next: switch `SecureORO`, `IndifRO_is_secure`, `SHA3Security` to the pilot and retire the old
`SecureRO.lean`; then the next file.

## Phase 2: remove the boilerplate EC does not have (agreed 2026-11-06)

The pilot is 1452 lines for EC's 525.  The gap, by pattern (counts in the three pilot files):
types `«from» «to»` 121; `*_proc_to_stmt` + `*_inline k` 69; `Lens.pair` state views 40;
expectation lemmas after wp 38; `split_ifs`/`simp_all`/`omega` 50; footprint tactics 21;
abstract-call side conditions 23; hand-written module variables and coercions 12;
`(self := inferInstance)`/`set_option` 19.

**A. Declarations**
1. Theory types implicit for module types too (declared after `variable {from to} [Params]`, the
   instance's `outParam`s fixing them): `RF`, `Oracle.mk`, `RF.get F` without types.
2. Our own `module_var x : T` command (what `RO.m`, `FRO.m`, `SecondPreimage2.m2`, `D1.m1` are by
   hand today); `global_var` stays as it is.
3. `module_subtype RF <: Oracle`: the coercion from the field names.
4. `T.holes`/`T.ext` generated, recorded by `declare module`: no `Module.Declared.ecModule …` in
   proofs.
5. The theory's axioms usable by name (no `(self := inferInstance)`).

**B. Tactics** (one implementation per step, all judgments)
6. `proc` to the body with the parameters as locals (no argument copies: EC's `seq` counts);
   `inline*`, `inline M.f` by name.
7. `fel cntr step q bad [O: pre] inv` and `call (: inv)` on abstract calls: EC's arguments in `§`
   syntax, the state view inferred from the variables, side conditions from `declare module`, EC's
   per-oracle premises as bullets.
8. Statement-level `rnd (pred1 v)`, `rcondt`/`rcondf`, `case P`, `hoare`, leading-count `seq`
   everywhere; what is left is logic, closed by `simp_all`/`omega` (no `smt`-like tactic).
9. A simp set for EC's real-valued bounds.

**C. Structure**
10. EC's inline `have`s and bullets back inline; generic `FMap` facts to `Lib/EC/FMap.lean` under
    EC's names; target: no auxiliary lemmas beyond EC's.
11. One pilot file; the slow disjointness of long variable names.
12. `scripts/ec_fidelity.py`: Lean/EC line ratio per proof, boilerplate counts.

Validation after each phase: `SecureORO` (SecureRO's twin) with the new machinery; then switch
`SecureORO`, `IndifRO_is_secure`, `SHA3Security` to the pilot and retire the old file.

Decisions (Denis): no `smt`-like tactic; `global_var` unchanged, our own commands where needed.

### Phase 2 progress

* **A done** (A4 folded into B7): implicit theory types (`RF`, `Oracle`, `declare module A <:
  AdvPreimage`), `module_var` (`Syntax/ModuleVar.lean`), `module_subtype`
  (`Syntax/ModuleSubtype.lean`), axioms by name.
* **B7 done**: `fel cntr step q bad [pre] inv` (`Logic/FelTactic.lean`, rule `phoareStmt_fel`):
  the state view inferred from the globals the conditions read, `D`, its oracles' `T.ext`,
  representability, countability, footprints and the result variable discharged; EC's goals left
  in EC's order (`sum`, `init`, the oracle's `step`, `incr`, `same`, `keep`).  The pilot's three
  `fel` lemmas are EC's script with bullets; the three oracle-premise lemmas
  (`Bounder_RO_get_fel*`) and all `Module.fel`/`Lens.pair`/`Oracle.ext` plumbing in them are gone.
  One oracle only for now.
* **B7, Hoare side**: `hoare_call (: inv)` (EC's `call (: inv)` on an abstract module, rule
  `hoareStmt_call_inv`), same view inference and side conditions; goals `oracle` and `pre`.
  `FEL_dom`'s hand-built `Module.hoare_app_inv` and the lemma `Bounder_RO_get_dom` are gone.
* Pilot: 1339 lines (from 1452), auxiliary theorems 20 (from 24).
* **C10, the `have`s and bullets inline**: EC's inline specifications as tactics
  (`Logic/CallSpec.lean`): `phoare_call (: P ==> Q)` (EC's `call (: P ==> Q)` in a `phoare`; the
  callee's relation and bound the goal's, or written after), `hoare_call (: P ==> Q)`,
  `byphoare (: P ==> _)` (the judgment restated as `phoare[ M : P ==> E ] ≤ x`, `E` read back off
  the `Pr[ ]`).  The judgment about the callee is the first goal, as in EC.  With them, and with
  `byequiv`'s default judgment as a goal, each headline is **one proof as EC's**: the `have->:`
  are `calc` steps (`rw` fails on `Pr[ ]`: not type-correct at instance transparency), the `fel`s
  are under the `call`s, the arithmetic of EC's last `smt()` is the `bound` goal of `phoare_seq`.
  Gone: `FEL_rng`, `Preimage2_le`, `Preimage_Preimage2`, `FEL2_rng`, `FEL_dom`,
  `SecondPreimage2_le`, `SecondPreimage_SecondPreimage2`, `SecondPreimage3_RO_LRO`, `FEL_coll`,
  `Collision2_le`, `Collision_Collision2`, and the dead `RO.LRO_asRF`, `fvP_LRO_init/get`.
  Kept: `SecondPreimage2_SecondPreimage3` (EC's third and fifth `have`, one lemma for `LRO` and
  `RO`; EC repeats a one-line `sim`, ours is 100 lines), the footprint bounds `fvP_*` of concrete
  modules (`@[fp_bound]`, the solver's), `sum_Ico_int_toNat`.  Fixes on the way: `procedureOf`
  instantiates an already elaborated procedure (`exprToSyntax`), `byphoare`/`byequiv` find their
  goals by tag (hygienic tags, `eraseMacroScopes`), `byphoare` passes the signature.  The two
  folded headlines with `fel` need `maxHeartbeats 1000000` (one declaration).
* **SecondPreimage's modules in EC's shape**: `Bounder(F).init`, `A(Bounder(F)).guess`,
  `F.sample`, `FEL(A, F).main`, `D1(A, F).distinguish` instead of hand-built `RF.mk {…}`,
  `Oracle.mk {…}`, `Module.app (M) (Module.pair A F)`.  EC's module type `RO` is `RO_T` (the
  theory's types fixed by `Params`).  A path's first arguments fill the head's explicit Lean
  parameters (`Syntax/ModuleApplicationSyntax.lean`): `D1(A, F)` is `Module.app (D1 A) F`, `D1 A`
  being EC's partial application `D1(A)` (an `RO_Distinguisher`), and prints back so.  Accessors
  as field notation in proofs (`F.init = RO.LRO.init`, `FVP.fvP RO.sample`).
* **Footprints of concrete modules read off their code** (`Logic/ModuleFootprint.lean`), as EC
  does: `fp_disjoint` bounds a concrete `module` with no `@[fp_bound]` by the globals its code
  mentions (`DeclareModule.globalVarsOf`) and its abstract module argument, proven by
  `fp_module` (a hook in `FootprintSolver`, which also splits pair lenses itself now);
  `fp_finite` (finite support) and `ec_module` (`Module.ECModule` of a concrete module over a
  first-order type) on the same bounds.  The bounds are cached per file.  SecondPreimage's
  `RO_LRO_D` step is EC's one `call`, `equiv_call (RO_LRO_D … (D1 A) (by ec_module)
  (by fp_disjoint))`; `fvP_D1`, `fvP_Bounder`, `fvP_RO_sample`, `fvP_LRO_sample` and the
  hand-built `ECModule`/finite-support proof are gone; `SecondPreimage2_SecondPreimage3` takes
  its disjointness as an auto-parameter.  Cost: disjointness of two named globals is 250–400 ms
  of instance search (`NatNe` on the names' encodings, `Language/Variables.lean`), so bounding
  `D1(A)` is the expensive part; the headline needs `maxHeartbeats 2000000` (the old file spent
  2M on `fvP_D1` alone).  Single-threaded CPU time of the file 71 s (from 87 s).
* Collision's modules in EC's shape too (`Bounder(F).init`, `A(Bounder(F)).guess`,
  `FEL(A, F).main`, `F : RO_T`): no hand-built module record left in the pilot.
* **B6, EC's `proc`** (`Logic/ECProc.lean`): `phoare_proc`, `hoare_proc`, `equiv_proc` turn a
  procedure judgment into the judgment about the body (bodies), the parameters local variables
  under their own names, the postcondition read at the return value: no call, no argument
  copies, no frame reset, so EC's counts are ours (`seq 1`).  The rules
  (`phoareProc_of_body_anyLocals`, `hoareProc_of_body_anyLocals`, `prhlProc_of_body_anyLocals`)
  prove the body's judgment from every state whose parameter variables hold the arguments, as
  EC's `proc` does.  The old step to the call statement is `*_proc_to_stmt`; `equiv_proc` was
  that step and is renamed `equiv_proc_to_stmt` everywhere (321 uses).  The pilot's `phoare`
  and `hoare` proofs use `*_proc`; the return-copy `wp 1` steps and the copy-skipping `wp 2`s are
  gone.
* **EC's `inline*` and `sim`** (`Logic/ECSim.lean`): `stmt_inline*` (`phoare_inline*`,
  `hoare_inline*`) inlines every call that can be (not an abstract procedure's).  `sim` goes
  backwards over two statements with a relation (not EC's sets of equal variables): wp over the
  deterministic code of either side (copies, dead writes, frame resets vanish), samplings coupled
  by the identity, calls of the same procedure, conditionals on both sides (equal guards, the
  branches' relations found by `sim` on the branches, `prhlStmt_seq_if_bwd`); the final
  implication by `simp_all` with `lensWriteNorm` (a simproc putting chains of global writes in
  normal form: `set_set`, disjoint writes sorted by `Lens.Disjoint.commute`).  The pilot's
  equivalences are EC's: `byequiv; equiv_proc; stmt_inline*; sim` for `Preimage ~ Preimage2`,
  `Collision ~ Collision2`, `SecondPreimage ~ SecondPreimage2` (25, 17, 45 lines before), and
  the `RO_LRO_D` step `byequiv; equiv_proc; equiv_call (RO_LRO_D … (D1 A) …); stmt_inline*; sim`.
  Left: `SecondPreimage2_SecondPreimage3`, where the states differ in variables the adversary
  does not touch (EC's `sim` with `={glob A}`): a call rule equal outside a lens.
* **EC's `auto` and `rnd` steps** (`Logic/ECAuto.lean`, B8): `phoare_auto`/`hoare_auto` (wp
  back to the last call, then `skip`, the reads as plain variables); on the expectations a
  sampling leaves, `rnd_pred1 v` (EC's `rnd (pred1 v)`), `rnd_bound` (EC's `rnd` with a lossless
  distribution), `rnd_null` (EC's `hoare`), each leaving the pointwise goal.  The pilot's
  bullets use them and `*_inline*`: no `expected_mono'`/`expected_point'`/
  `SubProbability.expected_eq_zero_of_support` chains, no `phoare_wp 20`.  Measured: the
  preimage and collision headlines `clean`, second preimage `fp` (the `RO_LRO_D` call's
  `by fp_disjoint`), no `den`.
* Pilot: 1061 lines (from 1215).
* **B9, the bounds' arithmetic** (`Lib/EC/StdBigop.lean`): `sum_Ico_const`, `sum_Ico_toNat`,
  `ofReal_intCast_mul_mu1` (no `0 ≤ n` needed), EC's `StdBigop` facts its `smt()` uses: the
  preimage and second-preimage `bound` goals are 4 lines (from 15).  `hoare_auto`/`phoare_auto`
  split the reads of `fel`'s pair views before `skip`, so the oracle bullets lose their
  `simp only [Lens.pair, eval_lens_global] at …`.  Collision's `sum_Ico_int_toNat` is the
  library's `sum_Ico_toNat`.
* Pilot: 1029 lines (from 1061), auxiliary theorems 1 (`SecondPreimage2_SecondPreimage3`).
* The clone's `RO_LRO_D` in `Pilot/SecureRO.lean` (EC's `clone import PROM.FullRO as RO` makes
  it): its statement `type_of%` `PROM`'s at the clone's arguments, its side conditions
  auto-parameters (`ec_module`, `fp_disjoint`); SecondPreimage's step is EC's
  `equiv_call (RO_LRO_D (D1 A))`.  Measured: all three headlines `clean` (no term, den, fp).
* **C11, one file** as EC's: `Pilot/SecureRO.lean` holds the three sections (1007 lines, EC 525);
  `ec_fidelity.py` counts per Lean file (the sections of one EC file mapped to one Lean file).
  Measured: 3/3 statements in surface syntax, 3/3 proofs clean, no extra hypotheses, 2 auxiliary
  theorems (the clone's `RO_LRO_D`, and `SecondPreimage2_SecondPreimage3`, which waits for a
  `sim` with EC's `={glob A}` frame).
* **`sim` with a frame**, `sim / x₁, …, xₙ` (EC's `sim` with `={glob A}`): the states equal except
  on the listed globals; a call of the same module that does not touch them by
  `prhlStmt_seq_call_outside` (after the call, the same globals on both sides but each side's own
  frame), its disjointness by `fp_disjoint`; the closer reads `equal_outside` as an equation of
  chains of writes (`Lens.equal_outside_iff_set`, `lensWriteNorm`), with `split_ifs` for the same
  conditional writes on both sides.  `fp_disjoint`'s concrete-module bounds also take the globals
  passed as lens arguments (`RO.asRO … RO.m`).  SecondPreimage's third and fifth `have`s are EC's
  `byequiv; proc; inline*; sim / SecondPreimage2.m2, D1.m1`; `SecondPreimage2_SecondPreimage3`
  (100 lines) is gone.  The headline needs `maxHeartbeats 4000000` (one declaration, two framed
  `sim`s of about 20 s each).
* Pilot: 896 lines (EC 525), one auxiliary theorem (the clone's `RO_LRO_D`, EC's `clone`), all
  headlines clean, standard axioms only.
* Pilot: 1215 lines (from 1311), auxiliary theorems 2 (from 6): `SecondPreimage2_SecondPreimage3`
  and `sum_Ico_int_toNat`.
* Pilot: 1311 lines (from 1339), auxiliary theorems 6 (from 20).  The script now flags the three
  headlines `den` (no longer `clean`): the expectation steps of EC's `rnd (pred1 v)` and `hoare`
  bullets (`expected_mono'`, `SubProbability.expected_eq_zero_of_support`) were in the auxiliary
  lemmas and are now in the proofs; B8 is what removes them.

## Phase 3: migrating the codebase (agreed 2026-11-06)

**Strategy.** A file is switched only by its fidelity port: the port lives in `Pilot/` next to
the old file, the dependents move to it one by one, and the old file is retired when its last
dependent is ported.  Bottom-up along the SHA-3 import graph; the cross-cutting issues first
(clones, module-variable freshness, disjointness cost); each file gated by `ec_fidelity.py`.

### Cross-cutting

* **Clones** (`Syntax/Clone.lean`, `Syntax/CloneRegistry.lean`): `clone [import] T as C with type
  a <- τ, op o <- e` then `proof * by tac`; a theory is a namespace with `class T.Params`.  The
  clone is the instance `C.params` plus reducible aliases `C.x`; the registry lets `globalVarsOf`,
  `fp_disjoint` and the frames (`sim /`, `equiv_call (_ : ={…})`) read clone names.
* **Disjointness cost**: `global_var`/`module_var` emit their key equation as a theorem
  (`variable_name_key_theorem`, no section variables).  Three disjointness queries went from about
  2.2 s to 156 ms, kernel 0.8 s to 0.6 ms; pilot budgets went down (SecureRO's second preimage
  4M to 1M).  The one change in `Language/` (`Variables.lean`), to review.
* **`Module.Declared A S`** without `outParam`, weakened by `Footprint.JoinLe` (an adversary
  declared against more is one against less).

### EC's tactics added (all judgments where EC has them)

`sp`, `if`, `rcondt`/`rcondf` (`Logic/ECSp.lean`, `Logic/ECIf.lean`); `hoare`, `conseq`,
`exists*` (`Logic/ECConseq.lean`); `seq`'s `_` bound; one-sided `call` with a frame
(`equiv_call{i} H / x, glob A`, `Logic/ECCallOneSided.lean`); `call (_ : ={glob A, …})` on an
abstract module (`Logic/ECCallAbstract.lean`); framed `call (: P ==> Q)` in `phoare`
(`Logic/ECCallFrame.lean`); `hoare_call (: inv)` with EC's goal order (oracle first); `sim n₁ n₂`;
the block `swap{i} [a..b] k` with EC's positions; `byequiv` for different argument types.

### Ported

* `Pilot/IndifRO_is_secure.lean` (2026-11-06): 3/3 statements in surface syntax, 3/3 proofs
  clean, no auxiliary theorems.
* `Pilot/SecureORO.lean` (2026-11-07): all three lemmas, EC's proof steps (the `have->:` chain,
  `byphoare`, `seq 1`, `call (: inv)`, `fel`), 3/3 and 3/3 clean, one auxiliary theorem (the
  clone's `RO_LRO_D`).  Deviation: second preimage's `fel` takes `bad` without its
  `mess1 \in RO.m` (it is in the invariant; our `fel` wants the event to be `bad`).  EC's last
  goals' `rcondt`/`swap`/`case` are the conditionals split by `split_ifs`: the tactics exist,
  but after `phoare_auto` the goal is already the split.  Budgets: second preimage 2M (five
  `sim`s; the framed third one alone needs 200k–600k, 1.6 s), collision 1M.

* The leaves (2026-11-07): `Pilot/Indifferentiability.lean` (with `IndifRO_is_secure`),
  `Pilot/OptionIndifferentiability.lean`, `Pilot/SecureHash.lean`, `Pilot/IRO.lean` —
  declarations only (and `IRO`'s `prefix_closed_equiv`, EC's `smt()` a `grind`).  `SecureHash`'s
  three games take a 400k budget: the `module` command's generated `apply_simp` proof normalises
  the adversary's callee `A(FBounder(F(P)), PBounder(P))`, whose `module_subtype` coercions
  duplicate their arguments (~160k of the ~240k; `F(P).init` alone ~37k) — a cost in
  `Syntax/ModuleSyntax.lean` (`procApply`) to raise with Dominique.  `Common.lean` is not
  re-ported: no judgments, its theory already the class `Params`; its hand-built clones of
  `BitWord`/`PRP`/`RP` wait for `Lib/EC`'s theories to follow the `Params` convention (and for
  `clone`'s `rename`).

* The `CF_G1` experiment (2026-11-07, `Pilot/Handle.lean`, over the old declarations): EC's
  game-level equivalence through the up-to-bad call over three oracles, EC's proof step by step
  (about 100 lines; the old proof about 210 plus its auxiliary lemmas; budget 1M against 4M).  New:
  `equiv_call (_ : bad, I, J)` (`Logic/ECCallUpto.lean`: the invariants' variables collected, the
  goals in EC's order, `D_ll`'s goal closed by `exact D_ll`), `glob M` in conditions
  (`Logic/ECGlob.lean`), `equiv_conseq` on procedures and `equiv_conseq H`, `phoare_while I V`
  for `= 1` (`Logic/ECWhile.lean`), `sp` keeping a precondition the statement cannot change (EC's
  `P /\ x = e`), `glob_simp` (EC's implicit `={glob D}` across writes), `phoare_auto` closing the
  trivial goals; `inline*` through typed modules without parameters; the footprint solver using a
  typed module's procedure bounds (54 s → 0.3 s).  What was left are EC's closers (`smt`, `/#`):
  here `simp`, `split_ifs`, `omega`, and the old port's `INV_CF_G1_init` for EC's 18 `smt` calls.

* The second experiment (2026-11-07, `Pilot/Sponge.lean`, over the old declarations):
  `Sponge_Raise_BlockSponge_f`, a procedure equivalence with two two-sided loops, EC's proof step
  by step (about 45 lines against about 110 plus a helper; default budget).  New: EC's
  `equiv_seq n m : P` (positions from the start, resets not counted; the old cut, counted from
  the end, is `equiv_seq_last`, 444 uses renamed), `stmt_inline (M.f)` (EC's inline by name),
  `equiv_auto`, `equiv_call (_ : ={glob P})` on a concrete callee (`prhlProc_glob_module`),
  `hoare_auto` introducing the memory of a one-sided side goal, and stronger closers for
  `hoare_auto`/`equiv_auto` (reads simplified, the generalized variables substituted) — which
  also closed by themselves several goals the pilots `SecureRO`/`SecureORO` closed by hand (those
  lines removed).  Not gaps after all: two-sided `while I` and `case` existed (`equiv_while`,
  `equiv_case`).  What was left are EC's rewriting/`smt` steps (`simp_all` with the `blocks2bits`
  lemmas) and declaration artifacts of the old port.

* Deferred (agreed 2026-11-07): the path elaborator (`Syntax/ModuleApplicationSyntax.lean`) finds
  `.f` by the module type's head constant, so over the old port's module types (abbreviations of
  `Indifferentiability.X` with explicit type parameters) `Sponge(Perm).f` fails; `Pilot/Sponge.lean`
  works around it (`Module.app Sponge.f …`, the old views as coercions).  Fix later: see through
  such abbreviations; the pilot-style declarations do not need it.

### What retiring the old files waits for

The old `SecureRO.lean` is imported by the old `SecureORO.lean` and `IndifRO_is_secure.lean`;
those by `SHA3OSecurity.lean` (7791 lines) and `SHA3Security.lean` (2603 lines), which use the
old files' lens parameters (`RO_m`, `Bounder_bounder`, …) about 120 times each.  Retiring the
three old files is porting those two.
