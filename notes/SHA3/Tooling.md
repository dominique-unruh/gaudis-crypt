# SHA-3 port: logic and tactic extensions

A log of what was added to, or changed in, the logic and tactics for the port, and why.  The
newest entries are at the bottom.

## 2026-10-31: the abstract call rule (EasyCrypt's `call (: inv)` for an adversary with oracles)

**Files**: `GaudisCrypt/Logic/AbstractCall.lean` (the rule) and
`GaudisCrypt/Logic/AbstractCallTest.lean` (a toy).

**What EasyCrypt does.** `call (: inv)` on an abstract `D` whose oracles differ between the two
sides produces two kinds of premise:
* per oracle `o`: `equiv[ O₁.o ~ O₂.o : ={arg} ∧ inv ==> ={res} ∧ inv ]`;
* the call itself: precondition `={arg} ∧ ={glob D} ∧ inv`, postcondition
  `={res} ∧ ={glob D} ∧ inv`.

`inv` may not mention `glob D`, and globals outside `glob D` and `inv` are unconstrained.

**What we have now:**

| Lean | Role |
|---|---|
| `globInv L A I` | the invariant: `={glob A} ∧ I (L.get g₁) (L.get g₂)`.  `L` is a lens onto the oracles' state and `I` a relation on its content (EasyCrypt's `inv`). |
| `prhlProc_abstract_call` | the rule.  Its hypotheses are: `A` disjoint from `L` (`FVP.fvP_proc A ≤ L.footprintᶜ`, EasyCrypt's `{-O}`); the hole parameter types are countable; per oracle, `prhlProc (={arg} ∧ globInv) o₁ o₂ (={res} ∧ globInv)`. |
| `prhl2_instantiate_globInv` | the same rule on denotations |
| `prhlProc_globInv_of_confined` | removes `={glob A}` from an oracle premise when the oracle is confined to `L`, leaving EasyCrypt's premise |
| `glob_set_of_le_compl` | `glob A (X.set v g) = glob A g` for a lens `X` that `A` cannot see.  An oracle premise keeping `={glob A}` is then proven with the ordinary `equiv` tactics (see the toy). |
| `footprintCompat_globInv` | the adversary side: `A`'s own steps preserve `globInv` |
| `hhole_of_prhl2` | the oracle side: per-oracle specifications give the per-call coupling |

**How it is proven.** The rule is the oracle-agnostic machinery of
`Lib/RO/ROCouplingEquiv.lean` (`instantiate_of_fvP_gen`), fed with two new ingredients:
* `footprintCompat_globInv` generalizes `footprintCompat_PGlob` (`Lib/RO/GlobTransfer.lean`) from
  "equal random-oracle tables" to any `I` on a lens region disjoint from `A`;
* `hhole_of_prhl2` generalizes `ro_hhole_prhl` from the random oracle to any pair of
  instantiations.

`HasReset` is never needed for `glob A`: `={glob A}` is carried by the orbit self-coupling, and
`I` by the per-run preservation of the `L`-content (`L` is a lens, so it is resettable).

**Changes to existing files** (`Lib/RO/GlobTransfer.lean`):
* `liftedGlobSteps`, `lifted_step_mem_fvP_proc_compl`, `lifted_orbit_of_global` and
  `glob_locals_of_lifted_orbit` are generalized from the random oracle's holes (`roHoles`) to any
  hole signature.  Their proofs never used `roHoles`, and the callers are unchanged.
* `coupling_satisfies_fst` and `coupling_satisfies_snd` are no longer `private`.

**The toy** (`AbstractCallTest.lean`): an abstract adversary with one oracle, run against a
counter that adds 1 and one that adds 2, keeps `count₂ = 2 · count₁`, `={glob A}` and `={res}`
(`adversary_count`).  The oracle premise (`count_query`) is `equiv_proc_to_stmt; stmt_inline 0; stmt_wp;
equiv_skip`, then `glob_set_of_le_compl` and `omega`.

**Limitations and open points:**
* The adversary is a procedure with holes, not an arbitrary module of functor type (see
  `Exceptions.md`, E2).  A representation lemma would close the gap: every
  `D : Module.Arr T (procmod …)` applied to oracles has the same denotation as some procedure with
  holes instantiated with them.  It belongs in `Language/` (module metatheory).
* `I` reads a single lens `L`.  Several oracle variables go through a pair lens of disjoint
  lenses.
* No unary (`hoare`/`phoare`) version and no up-to-bad version (`call (: bad, inv, inv')`) yet.
* No tactic wrapper.  At a call site, `equiv_call (prhlProc_abstract_call …)` should do; to be
  confirmed on the first SHA-3 use.
* No automation for footprint bounds of concrete procedures (`(procedureDenotation o a).inFootprint
  L.footprint`, needed by `prhlProc_globInv_of_confined`).  The toy avoids it by proving the oracle
  premise with `={glob A}` included.

## 2026-10-31: the abstract call rule for modules; `={glob}` over any region

**File**: `GaudisCrypt/Logic/AbstractCall.lean`, restructured.

**`={glob}` over any region.** The invariant is now `globInvF L F I`: agreement on a region `F`
plus `I` on the `L`-content.  `F` is any region that contains the adversary's footprint and is
disjoint from `L`.  The rule in this generality is `prhlProc_abstract_callF`.
* `globInv L A I` is `globInvF L (FVP.fvP_proc A) I`, and `prhlProc_abstract_call` is unchanged.
* The orbit argument needed no change: steps outside `F` are steps outside `A`'s footprint.  The
  local copies are `liftedStepsOutside`, `lifted_orbit_outside` and
  `touched_locals_of_lifted_orbit`.
* The oracle-side lemmas are generalized to `F` as well: `touched_set_of_le_compl`,
  `touched_eq_of_inFootprint` and `prhlProc_globInvF_of_confined`.

**Modules.** These match EasyCrypt's `declare module D <: T {-O}` (exception E2):

| Lean | What it is |
|---|---|
| `Module.RepresentedBy D ext p` | for every `O`, `D` applied to `O` has the denotation of `p.instantiate (ext O)`, and `FVP.fvP_proc p ≤ FVP.fvP D`.  `ext : T → holes.Instantiation` lists the oracle procedures `D` may call (EasyCrypt's `OI.allowed`). |
| `Module.Representable D ext` | `∃ p, Module.RepresentedBy D ext p` |
| `prhlProc_abstract_call_module` | the rule for `(Module.app D O₁).procedure` and `(Module.app D O₂).procedure`, with `={glob D}` as agreement on `FVP.fvP D`.  Hypotheses: `Module.Representable D ext`, `FVP.fvP D ≤ L.footprintᶜ`, and the per-oracle premises on `ext O₁` and `ext O₂`. |

**Tests** (`AbstractCallTest.lean`):
* `module_adversary_count`: the counter toy with `D : Module.Arr Oracle (procmod () → Bool)`.
* `Guess`, written with the `module` command: the denotation half of `Module.RepresentedBy`
  holds by `simp [Guess.apply_simp, Guess.main.apply_simp]`.

**Closed 2026-10-31: `Module.Representable` is not vacuous.** The footprint half no longer
needs module-expression normalization:
* `FVP.fvP_stmt_le_instantiate` and `FVP.fvP_proc_le_instantiate`: footprints only grow when holes
  are filled.  A hole contributes the result write and the argument read; the call replacing it
  contributes those and more.
* `FVP.fvP_module_proc`: `fvP (Module.proc q) = fvP_proc q`.
* `Lens.reduceFootprint_bot`: `reduceFootprint L ⊥ = ⊥`.  It follows from monotonicity and
  `reduce (extend r) ≤ r`.
* `Module.representedBy_of_app_eq`: a functor module `D` with `Module.app D O = Module.proc
  (p.instantiate (ext O))` for all `O` is represented by `p`, given one oracle module `O₀` with
  `fvP O₀ = ⊥`.  The bound is
  `fvP_proc p ≤ fvP_proc (p.instantiate (ext O₀)) = fvP (D O₀) ≤ fvP D ⊔ fvP O₀ = fvP D`.

For a `module`-command functor, the equation is its `apply_simp` lemmas
(`simp [D.apply_simp, D.f.apply_simp]`).  `O₀` can be any module of constant procedures:
`fvP O₀ = ⊥` because a constant getter denotes `pure`, whose footprint is `⊥`.

Test: `guess_representable` in `AbstractCallTest.lean`, with `O₀ = Zero` (`fvP_Zero`).  It uses
only the standard axioms.

## 2026-10-31: three fixes in `Language/` and `Syntax/`, found porting the first files

* **`global_var` with abstract types** (`Language/Variables.lean`).  The macro's
  `Lens.IsGlobalVar` instance named the bare constant, so a variable whose type mentions an
  implicit section variable (`variable {D}`, then `global_var m : FMap D D`) failed.  The
  instance now ascribes the type, `($x : Lens $T VariableAssignment)`, which lets the implicit
  arguments be inferred.  This is needed for the module variables of abstract theories
  (`PRP.RP.m`, `IRO.mp`).
* **The `module` command with three or more module parameters** (`Syntax/ModuleSyntax.lean`,
  `moduleCallee`).  This is the failure first met in Schnorr.  A call target built from several
  parameters keeps the outer parameters' substitutions around the inner ones.  An example is
  `D(F, P)` in `Indif`, with `D` applied to views of `F` and `P`.  The callee simp set now
  evaluates substitutions on variables (`rename`, `substituteSimultaneously`, `liftSubst`,
  `variableSubstitution`) and lets them pass through closed expressions.
* **The tactic `module_reduce_congr`** (`Syntax/ModuleSyntax.lean`), with the lemmas
  `ModuleExpression.reduce_app_congr`, `reduce_pair_congr`, `reduce_fst_congr` and
  `reduce_snd_congr` (`Language/ModuleExpression.lean`).  It proves `X.reduce = Y.reduce` for
  expressions that differ only by `reduce`s at inner positions, below the reach of the
  stripping lemmas.  `moduleCallee` runs it last.

All existing modules still build: the full build is green.  Schnorr's `SHVIdeal` could now take
the scheme and the simulator as module parameters again, as in EasyCrypt; this has not been
tried.

## 2026-10-31: more EasyCrypt library theories (`GaudisCrypt/Lib/EC/`), for `SLCommon`

* `PROM.lean` contains `FullRO`:
  * the `flag` type (`Known`/`Unknown`) and `is_`;
  * the module types `RO_T`, `ROmap`, `FRO_T` (E3), `RO_Distinguisher` and `FRO_Distinguisher`;
  * `MainD`;
  * the oracles `RO` (with `RO.asRO`), `LRO`, `FRO` and `FullEager.RRO`;
  * `FullEager.RO_LRO_D`, stated, with a representability hypothesis on `D`.

  `Lib/RO/FullEager.lean` has a native lazy = eager proof in a different setting (the `prhl2`
  layer).  Bridging it to `RO_LRO_D` is left for when a SHA-3 proof needs it.
* `IterProc.lean` contains `Iter`, for `RRO.resample`.
* `Tuple.lean` contains `wordn`, for `SLCommon.bl_enum`.
* `DProd.lean` contains `ProdSampling.S` and `sample_sample2` (stated), for `SLCommon.Sample2`.
* `FMap` gains `restr` and `find`; `FSet` gains `elems`.
* `Strong_RP_RF.lean` contains `ARP`, `DBounder` (with `DBounder.FBounder`), the `PRPi` clone, and
  `Conclusion` (stated).  `PRP.lean` gains `StrongPRP.IND`.  `FMap.rng` gets a classical
  `Decidable` instance.
* `PROM.lean` gains `FullEager.Eager` (`main1`, `main2`) and `Eager_1_2` (stated), for `Gext`.

## 2026-10-31: `Module.comp` (`Language/Modules.lean`), for `BlockSponge.Sim`

`Module.comp f g : Module.Arr A C`, for `f : Module.Arr B C` and `g : Module.Arr A B`, is the
module `λ X. f (g X)`, typed with the `HasType` constructors in the same way as `Module.const`.
It translates EasyCrypt's functor aliases with composite bodies,
`module Sim (F) = Gconcl.S(Last(F))`.

## 2026-10-31: module variables of generic theories are parameters (E4 resolved)

The generic modules in `Lib/EC/` (`PRP.RP`, `Strong_RP_RF.ARP`/`DBounder`, `PROM.FullRO`'s
`RO`/`LRO`/`FRO`/`RRO`/`Eager`) and `IRO.lean` no longer declare `global_var`s.  They take their
module variables as lens parameters; a module body uses a parameter lens like a variable
(`m <- …`, `$m`).  Each clone declares its own variables and passes them.  The `global_var` macro
fix for implicit types (2026-10-31) is still in place, but nothing in the port uses it any more.

## 2026-10-31: for `Sponge`

* **`PROM.FullRO`'s distinguishers may call every oracle procedure.**  `RO_LRO_D` and `Eager_1_2`
  had a representability hypothesis whose holes were `G.get` alone, a narrower statement than
  EasyCrypt's (whose `RO_Distinguisher` is unrestricted).  The holes are now all of `RO`'s
  (`RO_holes`, `RO_ext`: `init`, `get`, `set`, `rem`, `sample`) and all of `FRO`'s (`FRO_holes`,
  `FRO_ext`).
* **`Indifferentiability.SIMULATOR.Representable`** (with `simHoles`, `simExt` and
  `SIMULATOR.RepresentedBy`): EasyCrypt's call restrictions on an abstract simulator (`f`, `fi`
  may call `F.f`; `init` nothing), procedure by procedure, since `Module.Representable` covers only
  functors returning one procedure (E2).  First needed for `Sponge`'s `declare module BlockSim`.
* **`Lib/EC/DList.lean`**: `dlist`, and the abstract theory `Program`'s `LoopSnoc`.
  **`Lib/EC/Int.lean`**: `iter`.
* `Common` gains a `Decidable` instance for `valid_toplevel`; `BlockSponge.BIRO` gains the
  abbreviations `IRO.init`, `IRO.fill_in`, `IRO.f`.
* **Writing `prhlProc` between procedures of different signatures.**  The pre-condition is
  elaborated before the procedures, so `a₁ = a₂` between `(xs, i)` and the pair `x` (or projections
  `a₁.2.1`) fails on the unknown signature.  Such statements give the signatures:
  `prhlProc (sig₁ := procsig (List block, ℤ) -> Bool) (sig₂ := procsig (List block × ℤ) -> Bool) …`.
* **`module` and section variables.**  A `module` takes a whole `variable` binder group when it
  mentions one of its names: `variable (a b : Lens …)` gives a module using `b` both lens
  parameters.  Declare lens variables one binder each.

## 2026-10-31: for `SHA3_OIndiff`

* `OptionIndifferentiability` gains `distHoles`, `distExt`: the oracle procedures an
  `ODISTINGUISHER` may call, as in `Indifferentiability` (E2).
* `SHA3Indiff.DistRestrictions.footprint` names what `SHA3Indiff`'s restriction excludes, so that
  `SHA3_OIndiff.ODistRestrictions` (the same list, plus `Counter` and `OSimulator`) reuses it.

## 2026-10-31: `module` with callees `A(G(F(P.mk …)), …)` (`Syntax/ModuleSyntax.lean`), for `SecureHash`

`SecureHash`'s games call their adversary as `A(FBounder(F(P)), PBounder(P))`: a module parameter
(`A`) applied to a closed functor (`FBounder`) around another applied parameter (`F`), whose
argument is a record built in place (`ODPRIMITIVE.mk … P`).  The `module` command's typing proof
failed there, in two places:
* `moduleCallee` did not unfold the `Module` combinators (`Module.app`, `Module.pair'` …) inside a
  callee's arguments, so `(Module.app F (X.mk …)).expression` stayed folded.  `X.mk` is reducible,
  a nest of `Module.pair'`s, so unfolding the combinators covers it.  `moduleCallee`'s simp set now
  includes `moduleCombinators`.
* `module_reduce_congr` stripped a doubled `reduce` (`(e.reduce).reduce`) only when that closed the
  goal.  It now also strips it and goes on descending.

Both were reproduced on toy modules first, with three module parameters `A`, `F`, `P` and closed
functors `G`, `H` around them (`A(G(F(P.mk …)), H(P))`).  The full build is green.

## 2026-10-31: `SHA3OSecurity`

* The `module` command's typing proof of `SORO_P1`/`SORO_P2`/`SORO_Coll` (an adversary applied to
  `DFSetSize(OFC(ExtendOutputSize(F)))` and `OPC(OSimulator(ExtendOutputSize(F)))`) takes about
  20 s, past the default heartbeat limit; those three modules raise it to 10M.  Bisected on scratch
  copies: either oracle alone checks in a few seconds; together they are slow but terminate.
* The file's three sections repeat the same local declarations; the Lean file was generated from
  one template per section (with the section-specific games, adversaries and bounds) and its long
  lines reflowed, so the sections stay in step.

## 2026-11-01: fresh variables (`Logic/FreshVariable.lean`)

* `Footprint.FinitelySupported F`: `F` lies within the slots of finitely many variables (with
  `mono`, `bot`, `sup`, and `varLens` for a single slot).
* `Footprint.exists_fresh T hF`: a lens of type `T` whose footprint lies in `Fᶜ`, itself finitely
  supported.  Proven, standard axioms only.  It is what the non-local results of E6 use to
  instantiate the local declarations' lens parameters.


## 2026-11-01: the inliner rewrites under a classically decided `decide`

A condition decided classically (`open Classical in … decide ($hash1 = $hash2 ∧ …)` on a type
without `DecidableEq`, as in `SecureRO.Collision`) kept the inliner's wrappers on its reads: after
inlining, `b <- decide (§hash1 = …)` still read the callee's names, while every other occurrence
was renamed (to `hash10`, … because the stale names counted as taken).  Sound, but unusable.

The cause: `simp`'s congruence for `decide p` re-synthesizes `Decidable p'` for the rewritten
proposition, and when it cannot (no `Classical` instance in scope) it leaves `p` alone.  A
congruence lemma casting the instance (`h ▸ hp`) fixed the reads but kept the old reads inside the
instance (phantom variables, false read dependencies for `stmt_swap`).

Fix (`Logic/Inline.lean`): the simproc `Flatten.reduceDecide` in the cleaning pass rewrites `p` to
`p'`, then synthesizes `Decidable p'` if possible and takes `Classical.propDecidable p'` otherwise
(`Flatten.decide_congr_inst`: `decide` of equal propositions agrees whatever the instances).
Reproduced on a toy module first; the full build is green.

## 2026-11-01: swapping a global update past an abstract call (pilot 1, in progress)

EC's `swap{1} [1..2] 2` in `coll_resistant_if_indifferentiable` moves `Bounder.bounder <- 0;
Counter.init()` past `P.init(); C(P).init()`, justified by `C`, `P` being `{-Bounder}`.
`stmt_swap`'s call rule (`Stmt.CommutesWith.«call»`) only commutes a call with updates of the
caller's locals.  New, proven:

* `Stmt.CommutesWith.call_footprint` (`Logic/StmtSwap.lean`): a call to `p`, which lies in the
  footprint `R` on every argument, commutes with an update applying `f` to the globals when
  `pure ∘ f ∈ Rᶜ` — from `ProgramDenotation.wp_of_inFootprint_det`, which is the definition of
  `inFootprint` at the kernel `pure ∘ f`.
* `Module.Proc.inFootprint_fvP` (`Logic/AbstractCall.lean`): a module's procedure lies in the
  module's footprint `FVP.fvP M` (with `Module.Proc.eq_proc_procedure`).

Wired into `stmt_swap` (same day):

* `Stmt.CommutesWith.call_assign_global X e`: `call_footprint` for the update of `X <- e`, `X` a
  global variable with `X.footprint ≤ Rᶜ`.  When `stmt_swap`'s plain call rule fails and the other
  statement is an assignment to a global, it tries this rule: the callee's footprint from
  `Module.Proc.inFootprint_fvP` (or a hypothesis `∀ a, (procedureDenotation p a).inFootprint R`),
  the disjointness by the new solver, the rest by `simp` as before.
* `fp_disjoint` (`Logic/FootprintSolver.lean`): closes `A ≤ (FVP.fvP M)ᶜ` / `FVP.fvP M ≤ Aᶜ` — EC's
  memory-restriction check.  It bounds `FVP.fvP M` through `Module.app`/`pair`/`fst`/`snd` (and
  the primed forms, `FVP.fvP_fst'` etc., new), unfolding module-type accessors and constructors,
  down to modules with a restriction hypothesis `FVP.fvP N ≤ Sᶜ`, and finds `A` among the
  joinands of `S` (unfolding named footprints such as `C.footprint`).
* Test: `StmtSwapTest.lean` (a global assignment past `M.init` and `G(M).init`, and back).
* In pilot 1, `stmt_swap{1} 4 3; stmt_swap{1} 2 4` is EC's `swap{1} [1..2] 2`, with no side goals.

Also, the inliner (`Flatten.moduleStep?`, step 6) now unfolds a definition whose value applies a
`module`-declared module: a single-procedure module (`SecureRO.Counter c := Counter.init c`, which
it could not inline before) and a game defined as an application (`GReal`, which needed a manual
`unfold`).

## 2026-11-01: pilot 1, first game hop proven (`Collision_FM_GReal`)

EC's `byequiv; proc; inline*; wp; sim. swap{1} [1..2] 2; sim.` is, in Lean, inlining, two
`stmt_swap`s, then by hand what `sim` does: `equiv_seq` after the adversary call, `equiv_call`
backwards through the prefix, `equiv_if` twice with `equiv_call`/`stmt_wp`/`equiv_skip` in the
branches (~40 tactic lines).  Tooling fixed or added on the way:

* `equiv_call` (no argument) on calls of procedures spelled differently: rule
  `prhlStmt_seq_call_eq` (`Logic/PRHLStmt.lean`), their equality left as a goal tagged `callee`.
  Here the adversary's oracles `Bounder(FM(C,P))` and `Bounder(FInit(DColl…))`: closed by `simp only`
  with the modules' `apply_simp`/`mk_simp` lemmas and `rfl` (`FM.get.procedure` and
  `FInit.get.procedure` are the same body).
* `generalizeReadsRel` (behind `equiv_skip`, the `guard` goal of `equiv_if`): `§allGlobals` is now
  read as the globals themselves, so the reads of global variables stay reads of the generalized
  globals.  Before, `§SRO_Counter_c{1}` and `§allGlobals{1}` became unrelated values and the
  guard goal was false.
* `reduceDecide` (moved from the inliner to `Logic/Judgment.lean`) is now in every tactic's
  `simpWithNames`: without it no read under a classically decided `decide` was simplified
  (`b <- decide (§hash1 = §hash2 ∧ …)` on `f_out` without `DecidableEq`), and `equiv_skip` lost
  the link between the reads and the states.

The second hop, `GIdeal_Collision_RO`, needs EC's `call{1} (S_ll RO _)`: a one-sided call of an
abstract procedure from its losslessness.  A `sim` tactic would replace the hand-written part.

## 2026-11-01: `equiv_sim` (light `sim`), and a framing gap

* `equiv_sim` (`Logic/PRHLWp.lean`, a macro): EC's `sim` on straight-line code — backwards by
  `stmt_wp` and `equiv_call` (a differently spelled callee tried by `rfl`, else left as a `callee`
  goal), then `equiv_skip` and the remaining implication closed by `subst`+`simp` or `simp_all` if
  possible.  It stops at a conditional, loop or sampling; there the relation is given by hand
  (`equiv_seq … : M`, then `equiv_if`).  A full `sim` would compute those relations (EC's backward
  equality sets: reads of the guard and of the branches' needed variables); not built yet.
  `Collision_FM_GReal` went from ~40 to ~20 lines of relational steps with it.
* Gap, for `GIdeal_Collision_RO` (EC's `call{1} (S_ll RO _)`, 7 one-sided calls in all of SHA-3):
  after a one-sided run of the abstract `S(RO).init`, the relation `={glob A, bounder, c}` must still
  hold.  The framework can frame a run only against a *lens* region
  (`inFootprint_preserves_touched` needs `Footprint.HasReset`, proven for lens footprints only;
  `CounterExamples/IndistinguishableVsGlob.lean` shows the subtlety), while `glob A` is
  `FVP.fvP A`, an arbitrary footprint.  Options: (a) a framing lemma for `FinitelySupported` module
  footprints; (b) EC's semantics literally — an abstract module's globals as a list of variables
  (E2/E6) and `{-M}` between abstract modules as disjoint variable lists, so every region is a
  lens; (c) leave these 7 for later.

## 2026-11-01: pilot 1, second game hop proven (`GIdeal_Collision_RO`)

EC's `call{1} (S_ll RO _)` and the adversary call against an oracle that differs on the two sides.
After E7 (`glob`), the proof is:
* the adversary call by `prhlProc_abstract_call_module`, invariant `globInvF` over the oracle state
  `(bounder, (c, m))` (E8), the oracle premise `Bounder_FInit_get_equiv` (both oracles inlined, the
  sampling by `equiv_rnd`, `={glob A}` through the writes by `touched_set_of_le_compl`);
* the one-sided `S(RO).init` by `prhlStmt_seq_left` and, new in `Logic/PRHLStmt.lean`,
  `Stmt.call_wp_one` (a lossless callee terminates) and `Stmt.call_satisfies` (outcomes of a
  call); the frame by `ProgramDenotation.preserves_touched_of_glob` through `S`'s representation
  (`SIMULATOR.RepresentedBy.init`); `RO.get`'s losslessness (`RO_f_lossless`) by `phoare_*`;
* the oracle calls after the adversary by `RO_get_FInit_equiv` (globals are no longer equal on the
  two sides, so `equiv_call` needs a judgment, not reflexivity).

Fixes on the way:
* `equiv_proc_to_stmt`, `Judgment.descsOf`, `prhlGoal` read the goal through `cleanupAnnotations`: after a
  `have` the goal carries an annotation, and the tactics did not recognize the judgment.
* `generalizeReadsRel` (behind `equiv_skip`, the `guard` goals) leaves a state alone when it
  occurs other than read (`onlyRead`), for example in the run of a call: it used to generalize the
  state's globals into a fresh value and keep the state, losing the link between the two.
  `equiv_sim`'s closing step gained a `simp_all` that unfolds `Setter.throwaway`/`globalL` for the
  goals this leaves.

## 2026-11-01: `equiv_call_frame X` (calls with a frame), preimage lemmas

EC's `swap{2} [1..2] 4` in `preimage_resistant_if_indifferentiable` moves `P.init(); C(P).init()`
past the read of `DPre.h` (a global read into a local), justified by `{-DPre}`.  `stmt_swap`
handles writes to globals past calls, not reads; mirrored, the relation `hash{1} = DPre.h{2}` must
survive the two calls on both sides, which reflexive coupling does not give (any globals are
allowed after it).  New (`Logic/Granular.lean`):
* `prhlStmt_seq_call_refl_frame`: calls of the same procedure on both sides, the postcondition
  needed only for globals that keep the value of a variable `X` outside the callee's footprint
  (`Procedure.satisfies_frame`, `SubProbability.satisfies_fst_of_marginal`);
* `equiv_call_frame X` (`Logic/PRHLWp.lean`): the tactic, the callee's footprint and
  `X ≤ footprintᶜ` discharged as for `stmt_swap` (`calleeFootprint`, `fp_disjoint`).

With it, `Preimage_FM_GReal`, `GIdeal_Preimage_RO`, `SecondPreimage_FM_GReal`,
`GIdeal_SecondPreimage_RO` follow the collision proofs; `IndifRO_is_secure.lean` has no `sorry`
left (its three theorems rest on `SecureRO`'s three bounds).

## 2026-11-01: the abstract call rule for expectations (`Logic/ExpectationCall.lean`)

EC's `fel` (failure event lemma, 8 uses in SHA-3) bounds the probability of a bad event over an
abstract adversary's oracle calls.  Its semantic core, proven here:
* `Module.ewp_app_le` / `ProcedureWithHoles.ewp_instantiate_le`: an adversary that cannot touch
  the oracle's state lens `L`, its oracles not increasing the expectation of a potential `φ ∘ L`,
  does not increase it either (a supermartingale).  Induction over the adversary's statement
  (`ConfinedP` from its footprint): hole-free code keeps `L` (lens frame), oracle calls are the
  hypothesis, sequences compose by `Stmt.ewp_mono`, loops by `Stmt.ewp_while_le`.
* A `fel` is then a choice of `φ`: the indicator of the bad event plus the bound still to pay for
  the remaining oracle calls; `Pr[bad] ≤ φ(state before the adversary)`.

## 2026-11-01: `RO_is_collision_resistant` proven (EC's `fel`), the collision chain closed

The proof follows EC's: `Collision ≡ Collision2` (`Collision_Collision2`, `inline*; sim`), then
`byphoare; seq 1` as an expectation bound (`Collision2_le`): the tail after the adversary is at most
`[collision RO.m] + μ` (`collision_tail_le`, EC's four `case`s) and the adversary part is EC's
`fel`, here `FEL_potential`: the potential `collisionPotential` (the collision indicator, plus the
bound still to pay for the remaining queries while `|dom RO.m| ≤ bounder`, `⊤` otherwise) is a
supermartingale under the oracle (`Bounder_RO_get_potential`, from `collisionPotential_step`) and
`Module.ewp_app_le` carries it over the abstract adversary.  The arithmetic
`∑_{i<bound} i · μ + μ = (bound (bound-1) + 2) / 2 · μ` closes it.  `coll_resistant_if_indifferentiable`
is now proven with standard axioms only.

New on the way: `simp_reads` (the judgments' read-through-write simp set, for hand-unfolded
expectations); `phoare_proc_to_stmt` sees through goal annotations.  Expectations of conditionals
with a sampling inside (no `phoare_if` yet) are unfolded with `Stmt.ewp_*` and `simp_reads`.

## 2026-11-01: `phoare_ewp`

`phoare_ewp` (`Logic/PRHLWp.lean`, a macro): on a `phoareStmt` goal about loop-free code, introduce
the state and spell the expectation out with the `Stmt.ewp_*` equations (samplings become
`expected`, conditionals `if`s, also those with a sampling inside, which `phoare_wp` refuses),
then `simp_reads`.  Replaces the hand-written sequence in `SecureRO` (`Bounder_RO_get_potential`,
`Collision2_le`); test in `PRHLWpTest.lean` (`CondFlip`).

## 2026-11-01: one-sided loops (EC's `while{i} I V`), pilot 2's `HIRO` lemmas

* `prhlStmt_seq_while_right`/`_left` (`Logic/PRHLStmt.lean`): a loop on one side only, with an
  invariant `I` and a variant `V : ℕ`, both relations (they may mention the other side's state,
  which the loop does not change).  Premises: the body is lossless under `I` and the guard, it keeps
  `I` and decreases `V` (a Hoare triple for each state of the other side and each value of `V`),
  and `I` with a false guard gives the postcondition.  On the way: `Stmt.ewp_while_eq_one` (a
  terminating, lossless-bodied loop is lossless) and `hoareStmt.satisfies`.
* `equiv_while{i} I V` (`Logic/PRHLWp.lean`): the rule as a tactic; goals `lossless`, `variant`,
  `exit`, then the code before the loop with postcondition `I`.
* Difference to EC: EC's `while{i}` folds the part of the relation the loop does not touch into the
  precondition of the preceding code (`while{2} (true) …` in `HybridIROLazy_HIRO_LRO_f`); here the
  invariant carries it.  Likewise the synchronized `equiv_while` does not frame, so the invariants
  of `HIRO_RO_HybridIROEager_f` list `bs` resp. `m`, which EC's leave out.
* `HybridIROLazy_HIRO_LRO_f`, `HIRO_RO_HybridIROEager_f` and the two `init` lemmas are proven with
  them, EC's tactic scripts step for step.

## 2026-11-01: the syntactic frame (`Logic/SyntacticFrame.lean`), Sponge's `Exper` lemmas

EC's `call (_ : inv)` against an abstract `D` keeps `={glob D}` across the oracles because they
write none of `D`'s variables, which EC checks syntactically.  The framework's oracle premise
(`prhlProc_globInvF_of_confined`) needs a footprint fact `inFootprint L.footprint` instead, and a
concrete procedure does not come with one (bounding `FVP.fvP` of concrete code is still open).

* `StmtWithHoles.WritesKeep G s`: every write of `s`, its callees' bodies included, keeps `G` of the
  globals.  `hoareStmt_of_writesKeep`, `hoareProc_of_writesKeep`,
  `Procedure.satisfies_of_writesKeep`: then `s` keeps `G` (induction over the statement; the loop
  case is `hoare_while`).
* `prhlProc_globInvF_of_writesKeep`: the oracle premise from the oracles' own relation
  `={arg} ∧ inv ==> ={res} ∧ inv` and `WritesKeep F.touched_getter.get` of both oracles.
* `writes_keep`: reduces a `WritesKeep` goal to the single writes, unfolding module procedures as the
  inliner does (`Flatten.unfoldProcedure`).  It closes writes to locals by `rfl` and writes to a
  global lens `X` by `touched_set_of_le_compl` with a hypothesis `X.footprint ≤ Fᶜ` from the context.
* `Exper_HybridIROLazy_LRO`, `Exper_RO_HybridIROEager` are proven with it, as EC's `byequiv; proc;
  inline*; wp; call (_ : mp{1} = m{2}); conseq …_f; auto`.  The two oracle states are one lens
  (`Lens.pair`, E8) with the invariant `a.1 = b.2`.

## 2026-11-01: representing functor modules (`Logic/Representation.lean`), towards removing E2

Every module is code: a closed normal module expression.  `Module.exists_representation` extracts
the procedure with holes from that normal form, for a functor over a first-order oracle (a tuple of
procedures, `H.toModuleTypeRepTuple`), over the full list of the oracle's procedures, with at most
the `fvP` of the normal form.  Standard axioms only.  Pieces:

* `StmtWithHoles.substHoles` / `ProcedureWithHoles.substHoles`: substitute procedures with holes for
  holes (each hole call flattened, as the inliner does, along `Flatten.trafo`/`emb`; the outer
  parameters renamed by `escape`).  Sound: `procedureDenotation_substHoles`.  Footprint:
  `FVP.fvP_proc_substHoles_le` — the renamings are invisible to `fvP`
  (`Footprint.GlobalsCommute.zoom`: a kernel on the globals commutes with `zoom l p` once it commutes
  with `p`, for `l` keeping the globals; proved through `Lens.reduceFootprint_alt_def`).
* `ModuleExpression.FONormal`, `foNormal_of_hasType`, `Module.expression_shape`: the normal forms over
  first-order parameters.
* `FOProj.reduce_substitute` (oracle components on a literal oracle), `ProcedureWithHoles.ofHole`
  (the wrapper calling one hole; **needs nonempty parameter and result types**: they live in local
  slots), `ofProc`, `HoleSigs.Instantiation.ofFun`, `procedureDenotation_instantiate_congr`.
* `FONormal.extract`: the induction; `Module.exists_representation`: its module form.

**Done the same day** (2d95fe5, then PROM): `Module.exists_representation_of_firstOrder` /
`Module.representable_of_firstOrder` for module types (any tree of products; `T.holesApp`,
`T.extOf`, `ModuleExpression.rebuild`), and `PROM.FullRO.RO_Distinguisher.representable`,
`FRO_Distinguisher.representable`.  The paragraph below is the plan as it stood before.

Open before it applies to SHA-3: a `moduletype`'s representation is a right-nested product *without*
the trailing `unit` (fields may be nested module types), so an adapter from arbitrary first-order
product trees to the tuple form is needed (rebuild the value from the tuple's projections: no
footprint), and a lemma that a module type's `ext` (e.g. `PROM.FullRO.RO_ext`) lists the leaves of
`O.expression`.  Then `Module.Representable (RODist D) ERO.RO_ext` follows, and with it E2 is gone for
every full-list `ext`.  Restricted lists (`HYBRID_IRO_DIST.ext`, EC's `OI.allowed`) keep `hD`.

## 2026-11-01: `fvP` of concrete code (`Logic/ConcreteFootprint.lean`); `RODist.ecModule`

* `StmtWithHoles.LocalsOnly` (reads independent of the globals, writes commuting with global writes),
  `FVP.fvP_proc_le_of_localsOnly`: a concrete procedure on locals alone has no footprint.
  `locals_only` proves `LocalsOnly` for a module's procedure (unfolding as `writes_keep` does; both
  now run on `stmtPredSplit`), closing local reads and writes by `rfl`.
* `evalMexpr_*` simp lemmas, `evalMexpr_toModule_le`, `evalMexpr_procWithHoles_le`: bound `fvP` of a
  module by walking its expression, down to the abstract modules it applies and the concrete
  procedures (closed by `locals_only`).
* Sponge: `fvP_HIRO : fvP HIRO = ⊥`, `fvP_RODist_le : fvP (RODist D) ≤ fvP D`, and
  `RODist.ecModule : ECModule (RODist D) ERO.RO_ext` from `D`'s — EC's "by construction", now a
  theorem (with `RO_Distinguisher.representable`).

## 2026-11-01: `IterProc` lemmas (`Lib/EC/IterProc.lean`)

* `programDenotation_while_unfold` (`Logic/PRHLStmt.lean`): a loop's fixed-point equation on
  denotations.
* `iter_loop`: a loop calling `f` on the head of a list slot and dropping it computes `iterDen f`
  of the list (stated for any guard/argument/update satisfying the obvious equations, so it
  instantiates by `rfl`); `Iter.iter_denotation`: `Iter(O).iter l` is `iterDen (O.f) l`.
* `iter_ll`, `iter_inv` (as EC), `iter_cat`, `iter_perm`, `iter1_perm` (denotational, E9), via
  `iterDen_append`, `iterDen_perm` (induction on `List.Perm`).

## 2026-11-01: PROM's `RO_FRO_D` and `LRO_RRO_D` (`Lib/EC/PROM.lean`, `Lib/EC/FMap.lean`)

* `FMap`: `restr` and `map` are now built by `ofOpt s h` (the map binding each `x ∈ s` with
  `h x = some y` to `y`), whose lookup is `get_ofOpt`.  EasyCrypt's lemmas follow from it under
  their names: `domE`, `fmap_eqP`, `emptyE`, `mem_empty`, `get_setE`, `get_set_sameE`,
  `get_set_neqE`, `get_set_id`, `mem_set`, `remE`, `rem_id`, `mapE`, `mem_map`, `map_set`,
  `map_comp`, `map_id`, `map_empty`, `map_rem`, `restrP`, `dom_restr`, `restr_set`,
  `restr_set_eq`, `restr0`, `restr_rem`; and `noflags`.
* `PROM`: `FRO.asRO` and `FullEager.RRO.asRO`, the `RO_T` views of `FRO` and `RRO` (EasyCrypt's
  subtyping `FRO <: RO`).  `RO_FRO_init` … `RO_FRO_sample`, `RO_FRO_D`; `LRO_RRO_init` …
  `LRO_RRO_sample`, `LRO_RRO_D`.  `FullEager` is now laid out as in EasyCrypt: `RRO`, then
  `EagerCore` (`Eager`, `Eager_1_2`, the `LRO_RRO_*`), then `RO_LRO_D`.
* Recipe for EasyCrypt's `proc (inv) => //; conseq O_init; …` over a module type's full oracle
  list: `prhlProc_abstract_call_module` with `RO_Distinguisher.representable`; each oracle premise
  by `prhlProc_conseq (prhlProc_globInvF_of_writesKeep _ ?_ ?_ ?_)`, then per hole
  `simp only [ext, view, T.f.mk_simp, lookup_*]` and `first | writes_keep; done | exact …`.
  The outer `prhlProc_conseq` absorbs what `simp` does to `r₁ = r₂` at `Unit` (it becomes `True`).
  `writes_keep` never fails (it leaves what it cannot split), so it must not run on the main goal
  unguarded.

## 2026-11-01: PROM's `eager_D` (`Logic/EagerAbstract.lean`, `Logic/ConcreteFootprint.lean`)

* `StmtWithHoles.Within X` (with `Getter.Within`, `Setter.Within`): every read and write touches
  the globals only through the lens `X`.  `FVP.fvP_proc_le_of_within`: such a procedure has
  `fvP ≤ X.footprint`.  Reads and writes are zooms along `ProgramState.withinL X` (the locals and
  `X`).  Tactic `within_lens` (on `stmtPredSplit`, like `locals_only`): closes local reads and
  writes, writes of `X` (`Setter.within_self`), and reads of expressions in `X` and the locals
  (`simp_reads; simp only [h]`).  Used for `RRO.resample_fvP`.
* Inliner (`Logic/Inline.lean`, `moduleStep?`, new step (8)): the accessor of a one-procedure
  `moduletype` (`Orcl.f O := O`) applied to a `Module.proc` that is not a `T.mk` is unfolded by
  definition.  Needed to unfold `Iter(RRO.I)` (`RRO.I` is a `module` without a module type).
* `Logic/EagerAbstract.lean`: `swapLoc_of_confinedP` (`ConfinedP R` gives `SwapLoc SL` when `SL`
  is confined outside `R`), `inFootprint_zoom_globalL`, and `eager_call_module` — EasyCrypt's
  `eager proc` for a representable module disjoint from the block's lens, at equality invariants.
* `PROM`: `Countable flag`; `RRO.resampleDen`, `RRO.resample_fvP`, `RRO.resample_inFootprint`;
  `RRO_resample_ll` and `eager_init` … `eager_allKnown` stated (sorry, step 4); `eager_D` proven
  from them (E10).

## 2026-11-01: from relational statements to `eagerR` (`Logic/EagerBridge.lean`); PROM step 4

* `ProgramDenotation.preserves_compl_of_inFootprint` (a run confined to `X` keeps `X.compl`),
  `Lens.eq_of_get_compl_get`, and **`ProgramDenotation.eagerR_of_prhl2_lens`** (the frame: a
  coupling of `S; p` and `q; S` with equal results and equal `X` is the full equality-invariant
  eager judgment, when all three are confined to `X`).
* `eagerLeftStmt R p a y` / `eagerRightStmt R q a y` (`_ <- R(); y <- p(a)` and
  `y <- q(a); _ <- R()`, with `StmtWithHoles.call` so that the inliner sees the call sites), their
  denotations (`eagerLeftStmt_denotation`, `eagerRightStmt_denotation`), and
  **`eagerR_of_prhlStmt`**: a `prhlStmt` between them from `={X}` to `={y} ∧ ={X}` is the eager
  judgment.  EasyCrypt's `eager proc` on concrete procedures is `eagerR_of_prhlStmt` then
  `unfold eagerLeftStmt eagerRightStmt; repeat stmt_inline{i} 0`, after which EasyCrypt's proof
  runs with the `equiv_*` tactics (`equiv_rcondf`, `equiv_while`, …).
* `programDenotation_hcall_apply` (`programDenotation_call_apply` for `StmtWithHoles.call`).
* `procedureDenotation_inFootprint_of_within`; `within_lens` now also unfolds the module
  procedures in a `Getter.Within` goal on a return value (`unfoldModuleProcs`).
* FMap: `get_set_id`, `fdom0`, `mem_fdom`, `in_dom_with_set`.
* One-sided lossless call (EC's `call{1} p_ll`): after `stmt_wp`, with a lone call left on one side,
  `unfold prhlStmt`, rewrite `programDenotation skip` to `pure ()`, then
  `ProgramDenotation.prhl2.kill_left'` with `Stmt.call_wp_one` and `Stmt.call_satisfies`.
* PROM: `RRO_I_f_ll`, `RRO_resample_ll`, `eager_init`, `eager_queried`, `eager_allKnown` proven
  (EasyCrypt's proofs step for step).
* (later) `prhlStmt_seq_congr_left` / `prhlStmt_seq_congr_right_snd` (replace a statement by one with
  the same runs, conditionally on the precondition: EC's `transitivity{i}` against a program proven
  equivalent denotationally), `prhlStmt_fix_left` (EC's `exists* e{1}; elim*`).
* FMap: `set_setE`, `fdom_set`, `eq_except` (with `eq_except_set`, `_setl`, `_setr`, `_remr`,
  `_refl`), `rem_eq_of_eq_except`, `in_dom_with_congr`.
* PROM: `RRO.I_f_denotation`, `RRO.I_f_procedure`, `iter_perm2` (denotational, E9),
  `RRO.resample_denotation`, `RRO.resample_call_eq`, `RRO.resample_call_split` (EC's
  `transitivity{1} { Iter(RRO.I).iter_1s(x, …) }` via `iter1_perm RRO.I iter_perm2`), `I_f_eqex`,
  and `eager_rem` (EC's proof: case split, `iter_1s`, `seq 3 1`, `exists*`, `iter_inv`).
* `prhlStmt_seq_congr_right_snd_on` (replace the second statement on the right, given a Hoare
  postcondition of the first: EC's `transitivity{2}` after `rcondt{2}`).
* `stmt_swap` (`Logic/StmtSwap.lean`): a sampling now also swaps with a call whose write-back leaves
  the distribution unchanged (`Stmt.swap_sample_call`; `c <$ dout x` past a call that writes no
  local), which EC's `swap{1} -1` in `eager_sample` needs.
* PROM: `eager_set`, `eager_sample` (EC's proofs, including the `swap` and the `seq 1 7` coupling of
  the left `c` with the one `RRO.I.f` samples).
* `prhlStmt_fix_right` (EC's `exists* e{2}; elim*`). PROM: `I_f_neq`, `I_f_set`, `eager_get` (EC's
  three cases: `Known` by `rnd{1}` + `iter_inv`/`I_f_neq`; `Unknown` by `transitivity{1}` through
  `iter_1s`, `seq 5 3`, `iter_inv`/`I_f_eqex`; unbound by `swap{1} -1`, `seq 1 1`,
  `iter_inv`/`I_f_set`).  With it all seven eager oracle lemmas are proven, and so is `eager_D`.

## 2026-11-01: PROM complete (`Eager_1_2`, `RO_LRO_D`); Sponge's lazy/eager chain closed

* `Logic/EagerBridge.lean`: `prhl2_refl_of_inFootprint`, `prhlProc_refl_of_inFootprint`,
  `prhlProc_refl_of_within` (EC's `sim` on code within a lens: from `={arg, X}` to `={res, X}`,
  through the commutation with the update that replaces the outside of `X`);
  `ProgramDenotation.prhl2_lossless_left` (a lossless run against a value, any result types).
* FMap: `restr_map_tag`, `restr_map_tag_ne`, `noflags_map_tag` (EC's `map_comp`/`map_id`/`restrP`
  at `map (fun _ c => (c, f))`).
* PROM: `RRO.resample_keeps` (resample keeps every region outside `FRO.m`), `eager_D_RO` (EC's
  `eager_D` at an `RO_Distinguisher`, EC's subtyping), `Eager.main1_denotation`,
  `Eager.main2_denotation`, `FRO_init_denotation`, `FRO_init_resample`, `Eager.main2_eq_main1`,
  `Eager.main1_self` (with a local `oracle_sim` macro), `Eager_1_2`, `RO_LRO_D` (EC's two
  `transitivity`s by `prhl2.trans`, the middle state with `FRO.m := map (·, Known) RO.m`).
  `PROM.lean` has no `sorry`.
* Sponge: `LRO_RO`, `HybridIROExper_Lazy_Eager'`, `HybridIROExper_Lazy_Eager` proven outright.

## 2026-11-01: `Common.ec` complete

* `Lib/EC/List.lean`: `mkseq0`, `mkseqSr`, `eq_in_mkseq`, `size_mkseq`, `mem_mkseq`; `iota_`
  restated with an explicit `ℕ → ℤ` cast (the implicit list coercion elaborated as a monadic bind).
* `Lib/EC/Distr.lean`: `is_lossless_iff_expected`, `dprod_ll`, `uniform_ll`.
  `Lib/EC/BitWord.lean`: `mkwordK`, `ofwordK`, `size_word`, `dunifin_ll`.
* `Common.lean`: all 62 lemmas proven (tactic proofs).  Helpers that are not EasyCrypt lemmas, each
  documented as such: `needed_blocks_eq`, `split_first_true`, `pad_of_unpad_some` (`unpad` accepts
  exactly paddings: `padK`/`unpadK`/`unpadP` follow), `chunk_cons'`/`chunk_lt'` (chunking peels one
  block), `findIdx_replicate_append`.  `valid_block_structP` is argued with
  `List.append_eq_append_iff` (where the padding falls relative to the last block) rather than
  EC's index arithmetic.

## 2026-11-01: `SLCommon.ec` — prefix, permutation, path and handle lemmas; lossless wrappers

* `Lib/EC/List.lean`: `take_size`, `cat_take_drop`.  `Lib/EC/FMap.lean`: `rngE`, `findP` (EC's
  `findP` with bindings `get m x = some y` for `x \in m` and `oget m.[x]`).
* `SLCommon.lean`: all lemmas but `DRestr_ll`, `swap_restr`, `Pr_restr` proven (tactic proofs).
  Helpers that are not EasyCrypt lemmas, each documented as such: `prefix_take_min`
  (`prefix (take i l1) l2 = min (prefix l1 l2) (max i 0)`, from which `prefix_geq`,
  `prefix_take_prefix`, `prefix_leq_prefix_cat`, `prefix_take_(leq|geq)_prefix`, `all_take_in`,
  `prefix_lt_size` follow without EC's inductions), `max_prefix_congr` (for `get_max_prefix_take`),
  `mem_elems_fdom` (EC's `memE` + `mem_fdom`).  `prefix_leq_prefix_cat_size` is argued from
  `prefix_cat1` at the maximal element instead of EC's induction over `ll`.
* Inliner (`Logic/Inline.lean`): a `moduletype` accessor applied to the `Module.pair` a typed
  `module` builds (`DPRIMITIVE.f (DPRestr(P))`) is unfolded to its projection, which is then read
  off the pair (`Module.fst'_pair`, `Module.snd'_pair` and their `Module.Proc`/`Module.Prod`
  spellings, matched at default transparency).
* pHL wp (`Logic/Judgment.lean`, `JudgmentWp.lean`, `PHoareWp.lean`): a judgment may register an
  `ifLemma` for a trailing conditional with calls or samplings in its branches; pHL's is
  `phoareStmt_seq_if` (the branches' expectations by cases), so `phoare_wp` goes through EC's
  `if` in lossless proofs.  `rp_ll`, `rpi_ll`, `rf_ll`: `phoare_proc_to_stmt; phoare_inline 0;
  phoare_wp 5; phoare_simp [hll]; phoare_skip`.
* Bug fixes: `generalizeReads`/`generalizeReadsRel` are atomic (`commitIfNoEx`) — a failure after
  a partial assignment used to make `phoare_skip` (and the other callers' `try … catch`) drop the
  goal, leaving a metavariable in the proof term; `hoare_/phoare_/equiv_proc_to_stmt` take the
  result variable's type as the signature spells it (`sigRetType`), not `whnf`-unfolded (`block`
  became a bare subtype without its `Nonempty` instance).

## 2026-11-01: `SLCommon.ec` — `DRestr_ll`, `swap_restr`; footprints of concrete modules

* `fp_module X` (`Logic/ConcreteFootprint.lean`): proves `FVP.fvP M ≤ B` for a concrete module
  (a `module`, or a functor of modules; the parameters contribute nothing) by its expression down
  to its procedures, each `within_lens` of `X`, with `X.footprint ≤ B`.  `fp_module` alone: locals
  only.  EasyCrypt reads a concrete module's globals off its code; `fvP_DFRestr`, `fvP_DPRestr`
  (`≤ C.footprint`) are such bounds, not EasyCrypt lemmas.
* `within_lens` closes writes of a component of a pair `X` (`Setter.within_of_global`) and reads
  of its components (`X = Lens.pair C.c C.queries` for `C`'s two variables).
* `fp_disjoint` (`Logic/FootprintSolver.lean`):
  * `@[fp_bound]` lemmas `FVP.fvP M ≤ B` bound concrete modules (tried before the combinators);
  * a variable outside a finitely supported `D` is outside `glob D`
    (`Footprint.varLens_le_compl_glob`; the finite support from a `Module.ECModule D _`
    hypothesis), so `C`'s variables are outside `glob D` given `{-C}`;
  * two variables are disjoint by their `Lens.Disjoint` instance (`global_var`s);
  * goals `glob F ≤ Tᶜ` and `v ≤ (fvP M)ᶜ` are turned around.
* `DRestr_ll`: EC's `{-DRestr(D)}` on `F`, `P` is stated as `glob DRestr(D)` spelled out,
  `C.footprint ⊔ glob D` (README: `{-M}` for a concrete module lists its variables, callees'
  included), and `D` carries `Module.ECModule` (E2; its finite support gives `glob D ≤ C.footprintᶜ`).
  Proof as EC's: `D_ll (DFRestr F) (DPRestr P)` with `rp_ll`, `rpi_ll`, `rf_ll` (side conditions
  by `fp_disjoint`), then `inline *; auto` as `phoare_inline; phoare_wp; phoare_simp [hll]`.
* `swap_restr`: `Indifferentiability.DFUNCTIONALITY.mk_f`, `DPRIMITIVE.mk_f_fi` (a record of a
  module's procedures is the module; not EC lemmas) let `simp` rewrite `FRestr(F).f` to
  `DFRestr(F).f` in the callee.  EC's `swap{1}[1..2] 3; sim` becomes three `stmt_swap{1}` and
  `equiv_sim`; the left-only `Redo.prefixes <- …` (which EC's `sim` ignores, tracking only
  `={glob D, glob F, glob P, glob C}`) is swapped to the end, past the calls that cannot see it,
  since `equiv_sim`'s calls need equal globals.
* `Pr_restr` remains `stated`: it needs EasyCrypt's up-to-bad abstract call
  `call (_: max_size < C.c, ={glob P, glob CO, glob C})` (also used by `Handle.eca`).

## 2026-11-01: the up-to-bad abstract call rule (`Logic/AbstractCallUpto.lean`, `Logic/PRHL2Upto.lean`)

* `prhlProc_abstract_call_upto` (procedure with holes) and `prhlProc_abstract_call_upto_module`:
  EasyCrypt's `call (: bad, invP, invQ)` on an abstract procedure (`equivF_abs_upto`).  `bad`,
  `invP`, `invQ` read the oracle lens `L`; `={glob}` is agreement on a region `F ⊇ fvP D`, outside
  `L`.  Pre and post `badInv ∨ (={arg/res} ∧ syncInv)` are EasyCrypt's
  `if bad{2} then invQ else ={…} /\ ={glob A} /\ invP`.  Premises: the adversary lossless with each
  instantiation (E11), the per-oracle equivalence up to `bad` (`prhlProc`), and the per-oracle
  preservation of `invQ` (left, once `bad{2}`) and `bad ∧ invQ` (right) as `hoareProc`.
* Proof: `prhl2_body_upto`, an induction over the adversary's code with invariant `uptoInv`.  Before
  `bad`: as the plain rule (synchronized, `LocP`).  After: `ProgramDenotation.prhl2.product` of the
  two remainders, each side keeping a unary invariant (`satisfies_inv_of_confined`, the diagonal
  self-coupling of `body_prhl2_gen`).  The induction carries `ProgramDenotation.LosslessAt` of the
  current statement at both states; `LosslessAt.of_bind` passes it to almost every intermediate
  state.  Loops: `ProgramDenotation.prhl2.while_upto` — the synchronized while rule that switches
  to a given coupling of the remaining loops when an exit condition holds at the start of an
  iteration (its coupling is the least fixed point of the extended transformer; the marginals are
  sandwiched between the loop's Kleene iterates and the loop, in expectation).

## 2026-11-01: `SLCommon.ec` complete — `Pr_restr`

* `Pr_restr` is EC's proof: `byequiv` (`Procedure.Pr_le_of_prhlProc`), `symmetry` (`equiv_sym`),
  `inline *`, the up-to-bad `call` (`equiv_call` with `prhlProc_abstract_call_upto_module`), and
  `auto; call(_:true); …` (`stmt_swap{2}` of `C.init`'s writes past `P.init(); CO(P).init()`, then
  `equiv_sim`).  EC's `={glob P, glob CO, glob C}` before the bad event is taken as equality of the
  global states (`F = L.compl.footprint`, `invP` equality on `C`'s lens: `syncInv_compl_eq_iff`,
  `prhlProc_upto_of_eq`), so the oracle subgoals call `P.f`, `CO(P).f` on equal states.
* EC's nine `call` subgoals: `apply D_ll` (both oracle sets, with `rp_ll`, `rpi_ll`, `rf_ll` and
  the new `pc_f_ll`, `pc_fi_ll`, `fc_ll`); the three equivalences `Pr_restr_F_upto`,
  `Pr_restr_f_upto`, `Pr_restr_fi_upto` (EC's `if{1}` as `equiv_if{1}`; its `call{2} f_ll` as a
  one-sided lossless call, `prhlStmt_seq_right` with `hoare_call_frame` for `C.c`); `invQ` trivial
  (`hoareProc_true`); the counting oracles keep `bad` (`FC_f_bad`, `PC_f_bad`, `PC_fi_bad`, with
  `hoare_call_frame`; `FC`'s conditional by `hoare_seq`/`hoare_if_wp`, Hoare having no `ifLemma`).
* `Indifferentiability.lean`: `FUNCTIONALITY.view_f`, `PRIMITIVE.view_f`, `PRIMITIVE.view_fi`
  (a view's procedures are the module's; not EC lemmas, EC's subtyping).  Not `@[simp]`.
* `fp_disjoint`: a restriction between abstract modules is symmetric
  (`Footprint.le_compl_glob_symm`, `Logic/Granular.lean`: `F ≤ (glob G)ᶜ` with `F` finitely
  supported gives `G ≤ (glob F)ᶜ` — EC's `{-D}` means "no common variable"); used at an abstract
  leaf against a `glob`.  A module reached through projections has its type unfolded: two `glob`s
  of the same module term are closed by `le_refl`, the kernel checking the instances (unifying at
  default transparency there made `IndifRO_is_secure` time out).

## 2026-11-01: `RO_is_preimage_resistant` proven (EC's `fel`, as for collision)

Same scheme as `RO_is_collision_resistant`: `Preimage ≡ Preimage2` (`Preimage_Preimage2`, EC's
`inline*; sim`; `Preimage`'s own `Counter.init` is dead since `Bounder.init` runs it again, so the
initialization is a one-sided `stmt_wp` + lens commutation instead of `sim`), then `Preimage2_le`:
the tail is at most `[rng RO.m h] + μ1 sampleto h` (`preimage_tail_le`), the adversary part is
EC's `fel` with the potential `preimagePotential` (`[rng RO.m h]`, else `(bound - bounder) · μ`;
EC's invariant on `|dom RO.m|` is not needed here) via `Module.ewp_app_le`.  The shared expectation
lemmas (`expected_mono'`, `expected_const_le'`, `get_set_self`, …) moved to a section
`FELHelpers` before both.  `preimage_resistant_if_indifferentiable` is now proven with standard
axioms only.

The bound is stated per argument (`phoareProc (fun _ _ => True) … (fun h _ => … μ1 sampleto h)`):
a precondition `fun a _ => a = h` does not elaborate before the procedure fixes the signature.

## 2026-11-01: `RO_is_second_preimage_resistant` proven; equal-outside framing, solver fixes

EC's chain of five `have->`, each a Lean lemma in the namespace `SecondPreimage`:
`RO.LRO_asRF_eq` (at the type `RF`, `RO` and `LRO` are one module), `SecondPreimage_SecondPreimage2`
(at `LRO`; EC's `sim` with `m2{1} = SecondPreimage2.m2{2}`: the queries after the adversary are
inlined and coupled by `equiv_rnd`), `SecondPreimage2_SecondPreimage3` (one lemma for EC's third and
fifth step, `F` = `LRO` and `RO`), `SecondPreimage3_RO_LRO` (EC's `call (RO_LRO_D (D1(A)))`), then
`SecondPreimage2_le` (EC's `byphoare; seq 1; fel 2` with the potential `secondPreimagePotential`,
`FEL_potential` over the eager `F.sample(m1)` and the adversary, and `secondPreimage_tail_le`).
The final theorem picks `SecondPreimage2.m2`, `D1.m1` fresh (E6).  `D1` and `SecondPreimage3`
take `A` as a Lean parameter (as `IndifRO_is_secure`'s `D2Pre`), so that `D1 A` is an
`RO_Distinguisher`; `D1 A` is EasyCrypt-like by `RO_Distinguisher.ecModule` and `fvP_D1`.

New tooling:
* `Logic/EqualOutside.lean`: `prhlProc_self_equal_outside(_module)`, EC's `sim` across a call when
  the states are equal except on a lens `L` the callee does not touch (`Lens.equal_outside`, from
  `prhlProc_abstract_callF` with no holes), and the algebra of `equal_outside` (`set_disjoint`,
  `get_disjoint`, `set_left`/`set_right`, `refl`).  Used where one side writes `SecondPreimage2.m2`,
  `D1.m1` and the other does not (EC's `wp 8 -2; sim`).  The relation is best stated with the lens
  generalized (`generalize Lens.pair … = L`): the judgment simp would unfold `Lens.pair`.
* `fp_disjoint`: a variable against a join of variables (`X ≤ (Y ⊔ Z)ᶜ`, turned around and split);
  `@[fp_bound]` lemmas with instance arguments get them by instance search; `@[fp_bound]` lemmas
  match at reducible transparency only (default transparency made `IndifRO_is_secure` time out
  once `SecureRO` had bounds on `Bounder`, `LRO`).
* `within_lens`: return values read off a `module`-generated procedure definition are unfolded
  (`unfoldReturnVals`, for PROM's `RO`); component writes of nested pair lenses
  (`Lens.set_get_of_disjoint_set`); reads under a `decide` whose instance is stated in another form
  (`decide_eq_decide`, then `Iff.rfl`).
* `fp_module`: an abstract module inside the concrete one (a Lean parameter) is bounded by its own
  `FVP.fvP`, and the bound may be `F ⊔ X.footprint`.
* `fp_bound`s in `SecureRO`: `fvP_LRO_init`, `fvP_LRO_get`, `fvP_RO_sample`, `fvP_LRO_sample`,
  `fvP_Bounder`.

## 2026-11-02: `SecureORO.eca` complete

The three lemmas follow `SecureRO`'s proofs step for step; the potentials and tail lemmas
(`SecureRO.preimagePotential`, `secondPreimagePotential`, `collisionPotential`, their `_step`s and
`*_tail_le`s) are reused, `SecureORO` importing `SecureRO` for them (EC's `SecureORO.eca` is a
separate copy).  `SecureORO` has no `Counter`: the potentials' middle (counter) component is `0`
and the step lemmas are applied with the counter guard `True`.  The option answers of `Bounder`
(`None` once the bound is spent) are normalized by `simp only [Option.some.injEq,
exists_eq_left, and_false, exists_false]` before the `SecureRO` tail lemma applies.

* `RO_is_preimage_resistant`: EC's `Preimage2` keeps the hash in a module variable
  `Preimage2.hash` (`Preimage2_hash`, fresh: E6).  `Preimage_Preimage2` frames it
  (`prhlProc_self_equal_outside_module` at `L = Preimage2.hash`, with `I` fixing its value, after
  `prhlStmt_fix_right` — EC's `exists*`/`elim*`); the potential reads the hash off the state
  (lens `Bounder.bounder × Preimage2.hash × RO.m`), so `Module.ewp_app_le` carries it over the
  adversary unchanged.
* `RO_is_second_preimage_resistant`: EC's five `have->` as in `SecureRO`, but its first step
  `SecondPreimage(A, RF(RO)) ~ SecondPreimage(A, RF(LRO))` cannot be an equation of modules:
  `RF(RO)` and `RF(LRO)` are module applications whose `get`s agree only after reduction.  New rule
  `prhlProc_abstract_call_equal_outside_module` (`Logic/EqualOutside.lean`): an abstract module
  applied to two oracles that keep `L.equal_outside ∧ I` keeps it too; with `I` equality
  (`Lens.equal_outside_and_get_eq_iff`) this is EC's `sim` across an adversary whose oracles differ
  in code.  `SecondPreimage2_SecondPreimage3` is general over `F : RO` with `F.init = LRO.init`
  (both `init`s are inlined) and `fvP F ≤ RO.m` (`F.sample`, `Bounder(RF(F)).get` and the adversary
  are framed).
* `RO_is_collision_resistant`: no new tooling.
* `@[fp_bound]`s: `fvP_Bounder`, `fvP_RF` (`⊥`: `fp_module` without a lens), `fvP_RO`, `fvP_LRO`.
* `§x` for a local variable whose name a bound variable of the program shadows (`y` in
  `∃ y, some y = §hash1 …`): the program prints it, and it is written, as
  `§(localVarLens "y" (Option «to»))`.

## 2026-11-02: library lemmas — `DProd.sample_sample2`, `dprod1E`, `duniform_funi`

* `Lib/EC/Distr.lean`: `uniform_funi` (EC's `duniform_funi`, for a finite type), `mu1_eq_expected`,
  `dprod1E`; `Lib/EC/BitWord.lean`: `DWord.dunifin_funi`.  Used by `ConcreteF`'s
  `realize uD_uf_fu`.
* `Lib/EC/DProd.lean`: `sample_sample2` proven.  EC proves it by `bypr` (equal probability of each
  result), which Gaudí has no rule for; here a coupling rule `prhlStmt_seq_sample_dprod`
  (`x <$ d1 \`*\` d2` against `x₁ <$ d1; x₂ <$ d2`, by the identity) and its tactic
  `equiv_rnd_dprod` (splits the last statement on the left, the last two on the right — statements
  are right-nested).  `DProd` now imports `Logic/PRHLWp`.

## 2026-11-02: `Strong_RP_RF` complete (the PRP/PRF switching lemma)

EC's three sections, statement for statement (Mapping, "Library: `Strong_RP_RF.eca`"):
* `PRPi_PRPi'_Indirect`: `eq_Direct_Indirect` from `dexcepted_indirect` (`Lib/EC/Dexcepted.lean`:
  EC's `TwoStepSampling` as an equality of distributions, `dexcepted_expected`, `dexcepted_ll`);
  EC's `transitivity PRPi'(Direct).f` is `prhlProc.trans`; the abstract call is
  `prhlProc_abstract_call_equal_outside_module` with `I` equality.
* `Upto`: `PRPi'_Indirect_eq` by the equal-outside call at `PRP_indirect_bad.bad`;
  `pr_PRPi'_Indirect_ARP` by `prhlProc_abstract_call_upto_module` at the lens of all six oracle
  variables (both sides), `F = fvP D`, with the oracle premises by the new
  `prhlProc_upto_of_writesKeep` (`Logic/SyntacticFrame.lean`) and EC's `byequiv: bad` as the new
  `Procedure.Pr_abs_sub_le_of_prhlProc_upto` (`Logic/PRHLStmt.lean`, with `prhlProc.symm` and the
  union bound `Procedure.Pr_or_le`).  The lemma is proven for a region `G ⊇ fvP D` (`D_ll` over
  oracles outside `G`), EC's statement being `G = glob D`: `PartialConclusion` applies it to
  `DBounder(D)` at `glob D ⊔ DBounder.c` (a composed module's `glob` is not its parts').
* `CollisionProbability`: EC's `fel 2` as a potential over the distinguisher
  (`Module.ewp_app_le`, as in `SecureRO`); the potential is `⊤` off EC's invariant
  `|dom ARP.m|, |dom ARP.mi| <= c`, so EC's local module `FEL` and the two `have`s that switch to it
  are not needed (a proof-level deviation; statements unchanged).
* `Conclusion` picks `PRP_indirect_bad.bad` fresh outside `glob D` (`Footprint.exists_fresh_glob`,
  `Logic/FootprintSolver.lean`; `freshName` made public).

New tooling:
* `prhlStmt_seq_sample_run_right` and the tactic `equiv_rnd_run k`: a sampling on the left against
  `k` statements on the right whose run is the same sampling (the obligation is an equation of
  runs).
* `fp_disjoint`: a lens parameter against `glob F` or any region `T`, from a hypothesis `T ≤ Sᶜ`
  with the parameter in `S` (turned around).
* `Lib/EC/FMap.lean`: `mem_frng`, `leq_card_rng_dom`, `endo_dom_rng`.
* `Distinguisher.representable`/`ecModule` for `PRP.StrongPRP.Distinguisher` (E2 as a theorem).
* Gotchas: `hoare_proc_to_stmt`/`phoare_proc_to_stmt` before any `have` (the judgment annotation);
  `simp` under `localVarLens` reads can fail on an ill-typed-at-instances term: `generalize` the
  reads first; rewriting under `decide`: `simp only [decide_eq_true_eq] at h` first; a read
  `§X` of a predicate variable in a guard is the same on both sides once the argument is
  rewritten (`Iff.of_eq (congrFun h _)`).

## 2026-11-02: `Sponge.ec` complete

Every statement of `Sponge.ec` proven; `conclusion` depends on `propext`, `Classical.choice`,
`Quot.sound` only.  The ideal side is EC's chain `Ideal_IRO_Experiment_HybridLazy`,
`Experiment_Hybrid_Lazy_Eager` (through `HybridIROExper_Lazy_Eager` on `HybridIRODist`),
`Experiment_HybridEager_Ideal_BlockIRO`; `IdealIndif_IRO_BlockIRO` picks `HIRO`'s two variables
fresh (`Footprint.exists_fresh`, E6).  The notes below ("Sponge, ideal side") have the recipes.

### Sponge (`HybridIRO`, loops)

* Inlining: `repeat stmt_inline{i} 0` inlines a call and the calls of its body (fill-in calls
  inside the loops), so both sides become plain loops.
* `equiv_seq k₁ k₂` with `0`: `equiv_seq 1 0` cuts before a trailing conditional on the left
  with nothing after the cut on the right (EC's `seq 1 0`); `equiv_seq 0 1` puts a whole side
  before the cut (a left loop coupled with a prefix of the right, then a right-only loop).
* EC's `exists* i'` (a ghost for an initial value): not needed when some variable keeps it
  (`next_block_split`: `i' = m - r`, `m` never written).
* `equiv_while{2} I V`, `variant` goal: `hoare_wp k` then `hoare_skip` generalizes the moving
  side; the other side's reads then show as `§x` (`eval`), and
  `simp only [eval_lens_full, eval_lens_global] at *` turns them into `.get σ₁` reads (so `omega`
  sees one atom per variable).  `lossless` on deterministic code: `simp [Stmt.ewp_seq,
  Stmt.ewp_assign]`.
* A branch whose precondition is contradictory: `prhlStmt_conseq prhlStmt_false`.
* `Lib/EC/List.lean`: `nth_rcons`.
* `Lib/EC/DList.lean`: `dlist0`, `dlist_succ`, `dlist_supp`, and EC's `Program` theory results
  for `LoopSnoc`: `LoopSnoc.sample_ewp` (exact expectation, by `phoare_while_le` and
  `phoare_while_ge … variant`, glued by `phoareProc_eq_of_le_ge`), `sample_denotation`,
  `pr_sample` (EC's `Sample_LoopSnoc_eq` + `pr_Sample`).  `Lib/EC/Distr.lean`: `eq_distr`.
* `prhlStmt_seq_sample_run_map_right` (`Logic/PRHLStmt.lean`): a sampling against code whose run
  samples `μ`, the left distribution being `μ`'s image by `f` (used for `bypr`, exception E12).
* Exact loop expectations: `phoare_while_le I` and `phoare_while_ge I variant V` with the same `I`.
  In `I`, read the globals as `CurrentState.state.globals`, not `§allGlobals`: `phoare_skip`
  generalizes `§allGlobals` apart from the `σ.globals` of the postcondition.
* Relation variables named `x` or `l` do not elaborate as `§x{1}` (an identifier clash in the
  elaborator); write `§(localVarLens "x" T){1}`.
* A call's run: `refine (programDenotation_call_apply _ _ _ σ).trans ?_` (`rw` fails on the
  instance-transparency check of variable names).
* `Lib/EC/List.lean`: `nth_cat`, `set_nth_default`, `take_nth`.
* A procedure judgment stated with `M.p.procedure` (the body's definition) does not fit a call of
  `M.p` (`Module.Proc.procedure M.p`) in `equiv_call`: restate it with `(M.p).procedure`
  (`by simpa using h`).
* Ghost variables (EC's `exists*`): read them from the other side when it keeps them, or fold the
  use of the ghost into the invariant (a universally quantified statement about the current
  state).
* `Logic/LoopTransform.lean` (new): EC's `splitwhile` (`Stmt.Equiv.splitwhile`, needs a variant
  for the first loop: proven on expectations, `ewp_while_le` above and `ewp_while_ge_variant`
  below) and `unroll` (`Stmt.Equiv.unroll`), applied in judgments by
  `prhlStmt_(seq_)splitwhile_left/right` and `prhlStmt_(seq_)unroll_left/right`; the split guard
  is `c.andB e` (`unfold Getter.andB` before `equiv_while`, so the guard goal sees both tests).
  `prhlStmt.trans` is EC's `transitivity{i} { code }` (middle programs as `equiv[ … ] { … } ~
  { … }` statements of `have`s; a variable with two types on the two sides is written
  `(localVarLens "bs" T)` in the code, and the relations of the outer leg as lambdas).
  `prhlStmt_of_forall_nat` + `induction` is EC's induction on the rounds left
  (`HybridIROEagerTrans_BlockSpongeTrans_loop`: per step, `splitwhile` the bit loop at the next
  block, `unroll` the block loop, the block by `next_block` through calls).
* Reads of a measure written with `localVarLens` and the elaborator's `Lens.intoLocal (varLens …)`
  are different atoms for `omega`: `dsimp only [localVarLens] at h` first.
* Exit conditions of `prhlStmt.trans` chains show middle-state reads as `§x` (`eval`):
  `simp only [eval_lens_full, eval_lens_global, eval_getter_full, eval_getter_global,
  allGlobals_get] at *` before rewriting.

### Sponge, ideal side (nested abstract calls)

* `Logic/ModuleComp.lean`: `Module.app_comp` (`Module.comp f g` applied is `f (g x)`), for
  `RaiseSim S = S(LowerFun(·))`.  State the equation for the exact terms of the goal
  (`Module.app (RaiseSim S) X = …`) and `rw` with it.
* `prhlProc_abstract_call_moduleF` (`Logic/AbstractCall.lean`): the abstract call rule at a region
  `F ⊇ glob D`, so that the invariant `globInvF L F I` is the same for `Dist` and for the simulator
  it calls; `Examples/SHA3/IndifferentiabilityCalls.lean`: `SIMULATOR.call_init/f/fi` (from
  `SIMULATOR.RepresentedBy`) and `SIMULATOR.init_eq`.  EC's `call (_ : ={glob Dist, glob S} /\
  inv)` with `proc (inv)` twice is `F := fvP Dist ⊔ fvP S`, the concrete oracles framed by
  `prhlProc_globInvF_of_writesKeep` + `writes_keep` (the facts `X.footprint ≤ Fᶜ` in context).
* The oracle procedures appear as `(FUNCTIONALITY.f (Module.app M X)).procedure`; the lemmas are
  about `(Module.app M.f X).procedure`.  Bridge by an equation: `simp only [M.apply_simp,
  M.f.apply_simp]; unfold FUNCTIONALITY.f; erw [Module.snd'_pair_proc]` (for a one-procedure
  `DFUNCTIONALITY`, `unfold DFUNCTIONALITY.f; rfl`), then `rw` and `exact` the lemma.
* **A distinguisher restricted to some of its oracle's procedures** (EC's `{HI.f}` in a module
  type): `HybridIRO.HYBRID_IRO_DIST.representable_of_f` gets `Module.Representable D ext` over
  `HI.f` alone from a congruence (`HI.f = HI'.f → D HI = D HI'`, proven by `apply_simp` on the
  concrete `D`).  Recipe: the general representation over all procedures
  (`Module.representable_of_firstOrder`), its other holes substituted
  (`ProcedureWithHoles.substHoles`) by a do-nothing procedure (`ofProc noInit`) and the kept hole
  by its wrapper (`ofHole`); the denotation through `procedureDenotation_substHoles`,
  `procedureDenotation_instantiate_congr` and `procedureDenotation_ofHole`, at the oracle
  `HYBRID_IRO.mk {init := proc noInit, f := HI.f}`; the footprint through
  `FVP.fvP_proc_substHoles_le` at `⊥`.  `HybridIRODist.ecModule` adds the finite support
  (`fvP_HybridIRODist_le`, in the style of `fvP_RODist_le`).
* EC's `exists* n{1}; elim*=> n'` before `call (lemma n' …)`: `prhlStmt_fix_left`/`_right`, then
  `equiv_call (lemma n' …)` (the callee rewritten first to the lemma's procedure form).
* A lemma whose EC statement carries `={glob S}` (`RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f`)
  but is used under a larger `glob` region: prove it without the `glob` (`…_inv`) and frame in
  either region with `prhlProc_globInvF_of_writesKeep`.

## 2026-11-02: `Gcol.Pr_col` (EC's `fel` over concrete oracles) — `Logic/ExpectationFrame.lean`

EC's `fel` with oracles that are large concrete procedures (`DRestr(D)` over `Gcol.M`, `Gcol.S`)
which change the potential's state only through one sampling procedure (`Gcol.sample_c`):
* `StmtWithHoles.ExpDecr G φ s`: every write keeps `G` of the globals, every call is either to a
  procedure that does not increase `φ ∘ G` in expectation or satisfies `ExpDecr` itself;
  `Stmt.ewp_le_of_expDecr`/`Procedure.ewp_le_of_expDecr`: then `s` does not increase `φ ∘ G`
  (loops take `φ ∘ G` as invariant).
* Tactic `exp_decr` (as `writes_keep`): splits the goal down to single writes, closes a call by a
  step lemma `∀ a g, p.ewp a (fun _ g' => φ (G g')) g ≤ φ (G g)` in the context (matched at reducible
  transparency after folding the callee's field-by-field spelling back to `p`), local writes by
  `rfl`, global writes by `touched_set_of_le_compl` with a footprint fact from the context
  (`exp_decr_write` tries the hypotheses one by one).
* Recipe (`Gcol_potential`): the step lemma by `phoare_proc_to_stmt; repeat phoare_inline 0;
  phoare_ewp` + a pure step inequality; the main game by `phoare_inline`, `Stmt.ewp_seq/assign`,
  `simp_reads`, `erw [Stmt.ewp_call]`, then `Module.ewp_app_le` with each oracle by
  `Procedure.ewp_le_of_expDecr _ _ _ (by exp_decr)`.  A typed module defined with a parameter
  (`Gcol.S c := Module.pair …`) must be unfolded (`unfold Gcol.S`) before `exp_decr` so the
  inliner sees the pair.
* Gotcha: inside a tactic, `exact f (by assumption) …` may commit `assumption` before unification
  pins the type; use `refine f ?_ …; assumption` or try hypotheses one by one.

## 2026-11-02: `Gcol.G1_col` — `Gcol.eca` complete

EC's `call (_: ={…} /\ (G1.bcol{1} => G1.bcol{2}) /\ card … /\ Gcol.count <= C.c <= max_size)`
over `DRestr(D)`'s three oracles, ported oracle by oracle:
* Inner steps (`S_f_col`, `S_fi_col`, `M_f_col`): `G1.S.f ~ Gcol.S.f` etc. with the `C.c` budget
  explicit in pre/post (`card ≤ 2·C.c + 1 → card ≤ 2·C.c + 3` for the primitive; the functionality
  with the charge `qcost p g = size p - prefix p (get_max_prefix p (elems (fdom C.queries)))` and
  `equiv_while` with the counter in the invariant).  Wrappers (`DPRestr_f_col`, `DPRestr_fi_col`,
  `DFRestr_f_col`): `stmt_inline{i} 0` **once** (call sites are numbered in pre-order, so
  `repeat stmt_inline 0` also inlines the oracle inside the wrapper), `equiv_if`, `equiv_call` of
  the inner step.
* Top level: `prhlProc_abstract_call_moduleF` with `L` a nested `Lens.pair` of the twelve
  variables and `I` written on the tuple's projections in `colInv`'s order, so that
  `I (L.get g₁) (L.get g₂)` is `colInv g₁ g₂` by `Iff.rfl`: the oracle obligations are then
  `prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep') (DFRestr_f_col …)`.
* EC's `rcondt{2}` on `sample_c`'s guard: cut so that the left sampling faces the right's guard
  alone (`equiv_seq 1 1`), `equiv_if{2}`; the else branch is `prhlStmt_pre prhlStmt_false`.
* EC's `swap{1}[1..2]3` in `S.f` (samplings before the `FRO.m` update on the left, after it on the
  right): `stmt_swap` cannot move a deterministic `if` past an `if` containing samplings (its
  `discharge` does not push reads through the `ite` the update unfolds to; adding `apply_ite`
  there is the follow-up).  Done instead by running the right's deterministic prefix against
  `skip` (`equiv_seq 7 4`, the left side whole), with the relation stated on the left globals
  after the update (`rngUpd x g`; simp lemmas `rngUpd_get`, `rngUpd_set` for the other
  variables).
* `writes_keep` closes a global write by `by assumption`, which can pick a footprint fact about a
  different lens and fail (an expensive defeq aborts the search): local `writes_keep'` in
  `Gcol.lean` takes the hypothesis about the written lens itself, found syntactically
  (follow-up: fold into `writes_keep` and `exp_decr_write`, `Logic/SyntacticFrame.lean`,
  `Logic/ExpectationFrame.lean`).
* Bulk closing pattern for the generalized goals: destructure the ten equalities `e1 … e10` of
  `colEq`, rewrite the left reads (`col_rw`), `split_ifs` (one case per test, both sides now
  agree), then `col_eq` (`colEq` unfolded, `simp_reads`, the equalities).  `equiv_rnd`/`col_rw`
  turn trivial conjuncts into `True`: close them by `trivial`, not `rfl`.
* `maxHeartbeats` counts the whole declaration: the inlined oracles need 1–4M.
* `fp_mem` (local): `X ≤ A₁ ⊔ … ⊔ Aₙ` by backtracking over nested joins (`C.footprint` unfolded).

## 2026-11-03: `Gext.Pr_ext`, `RROset_inv_lt`, `Real_G2`

* `Pr_ext` is `Gcol.Pr_col`'s recipe (`Gext_potential`, potential `gcolPotential` reused on
  `(G1.bext, ReSample.count)`), with a call *after* the adversary (`Gext.resample`, an
  `Iter(ReSample).iter`): after `simp only [Stmt.ewp_seq]`, bound the continuation first,
  `refine le_trans (Stmt.ewp_mono _ (fun τ => Stmt.ewp_le_of_expDecr G φ _ ?_ _) _) ?_` with
  `exp_decr`, then the adversary's call by `Module.ewp_app_le`.
* `exp_decr` matches a step lemma against the callee **as spelled at the call site**: inside a
  functor the hole is instantiated as `(IterProc.Orcl.f t (IterProc.Orcl.mk t {f := p})).procedure`,
  not `p.procedure`, and the reducible-transparency `assumption` misses it; `exp_decr` then descends
  into the body and leaves the potential's own writes open.  Restate the step lemma in that
  spelling (`:= hsf`, a defeq coercion).  Debugging: `logInfo` inside the `try` of a tactic is
  discarded by `restoreState`; print with `IO.eprintln`.  (Follow-up: try `assumption` at default
  transparency after the reducible one fails, in `expDecrSplit`.)
* The final reads of the initial state through fifteen writes: `simp only [Lens.pair, …]` times
  out at `whnf`; `change gcolPotential (G1.bext.get _, ReSample_count.get _) ≤ _; simp_reads`
  works (2M heartbeats for the declaration).
* `Real_G2` needs `Eager_1_2` for `G2(DRestr(D))` and the events `G1.bext`, `inv_ext …`: the
  `prhlProc` relates only `glob D`, and a variable's equality would need a *lower* bound on
  `FVP.fvP (G2 (DRestr D))`.  `Eager.main2_eq_main1` (denotational equality) transports every event
  instead (`unfold Procedure.Pr; rw [Eager.main2_eq_main1 …]`).  Its side conditions: `fvP_G2` by
  `fp_module` with a ten-variable `Lens.pair` (slow: about 90 s, `maxHeartbeats 8000000`),
  `ECModule` from `FRO_Distinguisher.representable` and finite support.
* `fp_sub` (local, `Gext.lean`): `A₁ ⊔ … ⊔ Aₙ ≤ B` by `fp_mem` on each joinand, splitting the left
  join only when the whole is not itself a joinand (so `C.footprint` stays atomic).

## 2026-11-03: `Gext.EG2_Gext`, `Gext.G1_G2` — `Gext.eca` complete

Both follow `G1_col` (oracle steps, `DRestr` wrappers, `prhlProc_abstract_call_moduleF` with a
nested `Lens.pair` and `I` on its projections so that `I (L.get g₁) (L.get g₂) ↔ inv g₁ g₂` is
`Iff.rfl`).  New points:
* `equiv_seq k₁ k₂` counts the statements **after** the cut.
* Code after the adversary's call (`EG2_Gext`'s resample loops): `prhlStmt_seq_call` needs the call
  last, so cut after it first (`equiv_seq 6 5 : extInv …`), then cut before it into `globInvF`, and
  run the loops with `equiv_while` from the cut's relation.
* Asymmetric branches (`G2.S.f` samples `y2` in both branches of the `paths` test, `Gext.S.f` after
  it): `equiv_if{1}`, then `equiv_seq 1 1` and `equiv_if{2}` inside each case; the mismatched cases
  by `prhlStmt_pre prhlStmt_false` (`rw` of the guard fails on the dependent `Decidable` instance:
  `simp only [e, hx] at h1` and `of_decide_eq_true`/`of_decide_eq_false` instead).
* EC's `rnd{2}` (a discarded sample, `FRO.get` on a bound handle): `stmt_wp{2} 1`, which leaves the
  losslessness `d.expected (fun _ => 1) = 1` (`cdistr_expected_one`).
* `FRO.m` is an abbreviation of `ROhandle.FRO.m`, and the programs mix the two spellings.  `simp`
  sees through it, but `omega` (two atoms), `split_ifs` (two conditions, inconsistent cases) and
  `writes_keep'` (syntactic lookup) do not: `simp only [FRO.m] at h ⊢` before them, or state the
  footprint fact in both spellings (`hfro'`).
* When a sampling's distribution reads the state, the generalized goal stays half in `σ`-form:
  `rintro` with `rfl` patterns for the read equalities, then `by_cases` on the guard and
  `simp only [h, h1, …]` with the fact for both states (not `split_ifs` after `col_rw`, which may
  leave the two sides' guards syntactically different).
* `handle` is `abbrev handle := ℤ`, but `omega` needs binders typed `ℤ` (`∀ h : ℤ, …`).
* A local list of the inlined `Iter` has type `List (procsig (handle) → Unit).ParamType`: `headD`,
  `drop` lemmas do not fire; `change` to `List handle` terms first.
* `colEq` is a `def`: the anonymous constructor does not build it from `e1 … e10`; pass `hE`.
* `G1_G2`'s `inv_ext1` reasoning is factored into `bext_pre` (`G1`'s early update of `G1.bext`),
  `inv_ext1_of_weak` (a new `Known` handle) and `inv_ext1_hit` (`G2`'s `FRO.get` of the witness
  handle fires `bad_ext`/`y2 = x.2`), with freshness `∀ h ∈ FRO.m, h < G1.chandle`
  (`get_set_fresh`, `fresh_set`).

## 2026-11-03: `Gconcl.G2_G3`, `G3_G4`, `G4_Ideal`, `Real_Ideal` — `Gconcl.ec` complete

Same outline as `Gext.G1_G2` (oracle steps for `DFRestr`/`DPRestr`, then
`prhlProc_abstract_call_moduleF` with a nested `Lens.pair` and `I` on its projections).  New points:
* **No `rcondt` for a conditional in the middle of a statement.**  `G2_G3`'s `S.f`: on the guard
  `(x.1, hx2) \in G1.mh /\ t`, `G2` resamples `y2` inside `RRO.get` after its bookkeeping, `G3`
  samples it before; the coupling partner of `G3`'s `y2` depends on the guard.  Recipe:
  `equiv_case P` on the initial states (`P` the guard computed from them, `sfGuard`), then in each
  case cut (`equiv_seq k₁ k₂`) so that the conditional is a whole side, `equiv_if{1}`, and the
  impossible branch by `prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => …) (fun _ _ h => h)`.  Put
  the two samples to be coupled in the same block: the right's `y2` is moved past the bookkeeping
  with `stmt_swap{2} n k` in the guard-true case only.
* **`stmt_swap` does not commute two `reset_vars`** (inlined frames): moving `G2`'s bookkeeping
  (`allKnown`, `set`, `queried`, inlined) past the `paths` test (which inlines `RO.get`) fails.  A
  sample or an assignment past resets works (`resetSetter_set_localVarLens`).
* `equiv_if{i}` and `equiv_if{2}` inside handle asymmetric branches: a sample in both branches on
  one side (`G2.S.f`'s `y2`) against a sample after the conditional on the other side.
* EC's `call{1} RRO_resample_ll` (a trailing lossless call whose effects the post ignores):
  `stmt_split{1} 1` (so the call is the second block: `prhlStmt_seq_left` matches `.seq s d`, and
  the statement is right-nested), `apply prhlStmt_seq_left`, and at the end
  `⟨Stmt.call_wp_one (RRO_resample_ll …) _ _ _, Stmt.call_satisfies fun r _ => ?_⟩`; the result
  setter is `Setter.throwaway` (`simp only [Setter.throwaway]; simp_reads`).
* wp of a conditional leaves `(if c then X else X)` for every variable it does not write:
  `simp only [ite_self]` after substituting the equalities (`rintro … ⟨rfl, …⟩`).
* `rintro` patterns on a hypothesis in `σ`-form (`§x{1} = §x{2}` not generalized) may try to `cases`
  the equation and fail ("dependent elimination failed"): use projections (`h.1.2.2…`).
* Guard goals are value-generalized (binders for the reads), not `σ`-form: `rintro g₁ g₂ x … ⟨rfl, …⟩`.
* A conjunct reduced to `True` by the wp (`x1 = x1`) needs `trivial`, not `rfl`; count the
  conjuncts by `refine ⟨…, ?_⟩; trace_state` when a tuple does not fit.
* `col_close` (`intros; simp only [colEq] at *; try simp_reads; simp_all`) closes the synchronized
  steps of `DFRestr_f_G23` (a macro, so the unused-`simp_reads` linter is quiet).
* A `procmod () → Bool` is not an `RO_Distinguisher` (`procmod (Unit) → Bool`): `G3`, `G4` take
  `(_u : Unit)` as `G2` does, so that `RO_LRO_D` applies; their `ECModule` is
  `RO_Distinguisher.ecModule` with finite support from `fvP_G3`/`fvP_G4` (`fp_module`).
* Heartbeats are counted per declaration: a chain of `simp_all` closers can time out a lemma whose
  steps are each fast.
* Long lines: count characters, not bytes (`awk length` counts bytes under a C locale).

## 2026-11-03: `Gconcl_list.Ideal_equiv_valid`, `ideal_equiv2`, `Ideal_equiv3`

* **One EC module type, two Lean instances.** `SLCommon`'s and `BlockSponge`'s `DPRIMITIVE` are
  both `Indifferentiability.DPRIMITIVE state _ _` at different (unused) `f_in`/`f_out`; they are
  defeq only by unfolding the module type, so a module declared with one and applied to the other
  type-checks but does not inline (`A.apply_simp` does not match: "no concrete procedure body").
  Fix: declare the parameter at the type it is applied to and repackage with `mk` where it is passed
  on (`A`'s `P`).  `S2 = Module.comp Gconcl.S Last` has the same mismatch (`PRIMITIVE`).
* **Layered oracle steps.** For `D(FC(DSqueeze(F)), PC(S(F)))`: prove the inner step (`F.f`) once,
  then lift it through each wrapper with `equiv_call`, inlining one layer at a time
  (`stmt_inline{i} 0` once); state the wrapper lemmas generically over the inner step (`FC_f_sInv`,
  `S_f_sInv`) and over an invariant `sInv K₁ K₂ R` (equalities on `S`, `C`, and a relation between
  two lenses' values, disjointness instances as arguments: `simp_reads` frames them).
* **Unification through `mk` layers is slow**: `exact (PC_f_sInv S_f_sInv)` against a goal with
  `DPRIMITIVE.f (DPRIMITIVE.mk {f := …})` timed out at 4M heartbeats.  State the wrapper lemma over a
  `mk`-built argument (`{X₁ X₂ Y₁ Y₂}`, `DPRIMITIVE.mk {f := X₁, fi := Y₁}`) and
  `simp only [DPRIMITIVE.f.mk_simp, DPRIMITIVE.fi.mk_simp]` the goal (and, inside the lemma, the
  inlined call) first.  Implicit lens/relation arguments not fixed by a hypothesis (`S_fi_sInv`)
  must be given by name.
* A local `let L := …` shadows a module `L` (`unfold L` fails): name the lens `Lg`.
* After `simp`/wp, substituted equalities may have become `True`: close tuples with
  `and_intros <;> first | trivial | rfl | …` (and prune never-executed alternatives: the linter
  flags them).
* Redirect `lake env lean` output to an absolute scratch path (`cd` moves the shell).
* Open framework points (not yet needed by a finished proof): a lower bound `fvP D ≤ fvP (A D)` and
  `glob` monotonicity (for `A_lossless`/`concl`: EC's `{-A(D)}` is `glob (A D)`); and bridging an
  E5 wrapper module to the call it wraps (for `RO_LRO_D` on `D2`, `D3`, `D5`, `D6` in
  `equiv_ideal`: `prhlProc_refl` + `prhlProc.trans` after inlining the wrapper).

## 2026-11-03: `Gconcl_list.equiv_L4_ideal`

* **Same proof shape as `Ideal_equiv3`.** The invariant `L4Inv` relates lenses that exist on one
  side only (`F.RO.m`, `F2.RO.m` on the left; `BIRO.IRO.mp`, `BIRO2.IRO.mp` on the right).
  `globInvF` takes one lens `Lg` for both sides, so `Lg` pairs all four, and `I` reads each side's
  half.
* **The `S(Last(F))` wrapper** (`S2`, E5): inline the wrapper's call once on each side, then
  `equiv_call (S_f_sInvD Last_f_L4)`. `S_f_sInvD` is `S_f_sInv` for `S` applied to a
  `DFUNCTIONALITY`. `Last_f_L4` needs `simp only [FUNCTIONALITY.view_f]` and `stmt_wp` (for the
  trailing `res <- last b0 z`) before `equiv_call`.
* **Two branches with loops on each side** (`DSqueeze2_Valid_f`). Cut before the validity tests and
  run `equiv_if` on both sides.
  * The right side's inner `if` (`BIRO.valid x1` / `true`) is `equiv_if{2}`; close its else with
    `prhlStmt_conseq prhlStmt_false`.
  * The invalid branch's left middle loop does not run, because `i = 0 = nn - n`: use
    `equiv_rcondf{1}`.
  * Each remaining pair of loops is one `equiv_while`. Its body is a cut, then `equiv_if{2}` on the
    right's `¬dom`, with `lemma5` / `lemma5bis` as the step.
  * The invalid branch carries `parse (format pp n) = (pp, n)` and `i ≤ n` in the loop invariant.
    That gives `parse (format pp (i+1)) = (pp, i+1)` through `parse_twice`.
* **Closing tuples after `simp only [ite_self]`.** `simp only` also rewrites `a = a` to `True`, so a
  `⟨rfl, …⟩` tuple fails. Instead use `refine ⟨?_, …, hI, ?_⟩ <;> trivial`; it keeps the
  `INV_L4_ideal` conjunct whole, which `and_intros` would split.
* **Heartbeats.** `DSqueeze2_Valid_f` needs 1.6M; the main proof needs 4M, as `Ideal_equiv3` does.

## 2026-11-03: `Gconcl_list.A_lossless`, `Neg_D_lossless`, `Ideal_lossless`

* **Statement fixes.** EC's section `Real_Ideal_Abs` declares the axiom `D_lossless`.
  `Neg_D_lossless`, `Real_lossless` and `Ideal_lossless` use it, so they take it as a hypothesis,
  as `concl` already did. Otherwise they are false for a non-terminating `D`.
* **`{-A(D)}`.** EC's `{-A(D)}` excludes `glob A(D)`, which is `C.c` plus `glob D`. It is stated as
  `(C.c.footprint ⊔ (fvP D).glob)ᶜ`, following `SLCommon.DRestr_ll`. Likewise `{-Neg_D(D)}` is
  `((fvP D).glob)ᶜ`. That closes the open point "a lower bound `fvP D ≤ fvP (A D)`" from the
  previous entry: no monotonicity is needed.
* **Loops under a conditional, for lower bounds.** `phoare_wp` stops at an `if` whose branch
  contains a loop. The new `Logic/PHoareLossless.lean` adds two rules:
  * `phoareStmt_if_ge`: one lower bound per branch.
  * `phoareStmt_seq_ge_one`: `p; q` with `q` lossless from everywhere.

  The losslessness recipe (`IRO_f_ll`, `DSqueeze_f_ll`):
  1. Switch to a lower bound with `phoareProc_eq_of_le_ge (… Procedure.ewp_const_le …)`.
  2. `phoare_wp 1`, `phoare_split 1`, `refine phoareStmt_seq_ge_one ?_ ?_`, then
     `refine phoareStmt_if_ge ?_ ?_`.
  3. For the loop: `phoare_while_ge 1 variant (§n - §i).toNat`.
  4. `decreases` is a Hoare triple. `hoare_wp` has no rule for an `if` containing a sampling or a
     call, so build that step by hand:
     `hoare_split 1; refine hoare_seq (hoare_if_wp (hoare_call_wp _ _ _ (hoareProc_true _) _)
     (hoare_skip_wp _)) ?_`. Use `hoare_seq (hoare_assign_wp …) (hoare_sample_wp …)` for a
     sampling instead.
* **`phoare_simp [h]` needs the callee's expectation to be literally `1`.** `S.f` calls `F.f` with
  the continuation `cdistr.expected 1`, so the rewrite fails. Instead run `phoare_skip`, `split`,
  then `convert hF _ _ trivial using 2` and `funext`.
* **`fp_disjoint` for composite oracles.**
  * Unfold the restriction definition first (`unfold DRestrictions_Real_Ideal at h`).
    `fp_disjoint` does not unfold hypotheses: it silently skips them.
  * Give each concrete module an `@[fp_bound]`. A bound must be a join of variable footprints,
    not a `Lens.pair` footprint (`simpa only [Footprint.lens_pair]`).
  * A functor's bound may mention its module parameter, e.g. `fvP (SimLast S) ≤ fvP S ⊔ …`. One
    `fp_module` over all of `SimLast Gconcl.S` timed out.
  * The new bounds for BlockSponge's `FC`, `PC` and `IRO` live in `Gconcl_list`. Their natural
    home is `BlockSponge.lean`/`IRO.lean`, left alone to avoid rebuilding the chain.
* **`Real_lossless` stays open.** It needs EC's `call (: invm Perm.m Perm.mi)`: a losslessness
  abstract call under an invariant, which the framework lacks. `D_lossless` gives losslessness only
  for unconditionally lossless oracles, and `Perm.f`'s `dexcepted` sampling is lossless only under
  `invm`.

## 2026-11-03: `Gconcl_list.Simplify_Simulator.equal2`

* **`Logic/WritesKeepFrame.lean`: `prhlProc_frame_of_writesKeep`.** This is the syntactic frame
  for any getter. A relation `R (K₁ g₁) (K₂ g₂)` between values that neither procedure writes
  (`WritesKeep`) is added to both conditions. `prhlProc_refl_of_within`, which compares one
  procedure on both sides on its own lens, plus this frame gives EC's `sim` for an oracle that is
  the same on both sides (`FC_IRO_e2`). Its `WritesKeep` side goals for a `Lens.pair` getter are
  closed by `writes_keep <;> (intro v σ; simp only [Lens.pair]; simp_reads; try trivial)`.
* **Reuse `sInv`'s wrapper lemmas by putting the invariant in `sInv`'s shape.** `e2Inv` is
  `sInv K₁ K₂ Eq`: `K₁` pairs `Simulator`'s maps with `unvalid_map`, `K₂` pairs them with
  `IRO2.RO.m`. `PC_f_sInv`/`PC_fi_sInv` then lift the simulator steps. The abstract call's `Lg`
  includes `Gconcl.S`'s variables, which neither side writes. `I` is written so that
  `I (Lg.get g₁) (Lg.get g₂) ↔ e2Inv g₁ g₂` is `Iff.rfl`.
* **A local lens parameter (E6) needs its disjointness instances in both directions**, for
  `Lens.pair` and for `simp_reads`. Get them from the freshness hypothesis with
  `Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)`, using
  `(Footprint.le_compl_comm _ _).mp` for the reverse direction. The section's instance variables
  then need `omit … in` per lemma, and `set_option … in` must come before `omit … in`.
* **`fp_disjoint` failed on a whole join `X₁ ⊔ … ⊔ X₁₀ ≤ (fvP D)ᶜ` but succeeds per variable.**
  Split it with `sup_le` and run `fp_disjoint` on each piece.
* **Macro hygiene.** A `local macro` whose quotation names a definition must come after that
  definition. Otherwise the name stays unresolved and `simp only [e2Inv]` silently does nothing
  under `try`.
* **A loop on one side that does nothing** (`Simu`'s `LRO.sample` loop) is handled by
  `equiv_while{2} I (§k{2} - §i{2}).toNat`. In the `variant` case, `hoare_skip` generalized the
  globals inconsistently, so use `refine hoare_skip_of_imp fun σ h => ?_` and
  `Int.toNat_lt_toNat`. `omega` did not see through the `toNat` atoms there.
* **`LRO.get` samples unconditionally.** Against `if ¬dom {r <$ d; set}`:
  * `equiv_if{1}` on the left's test.
  * Then branch: `equiv_rnd` on the two samples.
  * Else branch: `stmt_wp{2} 1` on the right's discarded sample (`bdistr_expected_one`).

## 2026-11-03: `Gconcl_list.Simplify_Simulator.equal1`

* **`cInv K₁ K₂ R`**: equal `C.c` plus a relation `R` between a lens on each side. Unlike `sInv`,
  it has no `={glob S}` part, so the left and right maps may live in different variables (`S.m` vs
  `Simulator.m`). `PC_f_cInv`/`PC_fi_cInv` are `PC_f_sInv`/`PC_fi_sInv` for it.
* **Coupling two loops that fill the same entries in different ways** (`BIRO2.IRO.f`'s `fill_in`
  loop against `Simu`'s `RO.sample` loop) needs no `splitwhile`. The two loops run in lockstep
  under the invariant `0 < i → last b0 bs = oget m[(q, i-1)] ∧ (q, i-1) ∈ m`, so `RO.get(q, k-1)`
  afterwards finds its entry and drops its sample (`stmt_wp{2} 1`). Each step is a cut, then
  `equiv_if{1}` on the left's `¬dom`:
  * Then branch: `equiv_rnd` with the right's unconditional sample.
  * Else branch: `stmt_wp{2} 1`.
* **`equiv_seq 0 k`** (an empty side after the cut) works. Use it to put one side's trailing
  statements after a loop pair.
* **`parse (format (parse x).1 (parse x).2)`**: rewrite with `formatK`; `parse_gt0` gives
  `0 < k`, which rules out `Simu`'s `k ≤ 0` branch (closed with `prhlStmt_conseq prhlStmt_false`).

## 2026-11-03: `Gconcl_list.Simplify_simulator`

* **A functor over the random oracle for `RO_LRO_D`.** `L` must be a module over its oracle,
  `Module.app (L D) RO`, not a Lean function of it.
  * Its `distinguish` calls `Indif` applied to the game's modules (E5).
  * The functor it passes the oracle to, `Simu`, takes it as a second `using` parameter:
    `using (FRO, F)`, applied as `Module.app Simu (Module.pair FRO F)`. A Lean parameter cannot
    be instantiated by a module variable.
  * `equal1`/`equal2` (statements and proofs) were unaffected beyond the renaming, because
    inlining yields the same code.
* **Fresh `RO.m`/`FRO.m` for a local clone (E6).** Use the recipe of
  `Sponge.HybridIROExper_Lazy_Eager'`:
  1. Get the two lenses from `Footprint.exists_fresh`, the second fresh from the first.
  2. Get `Lens.Disjoint` from `Lens.disjoint_of_footprint_le_compl`.
  3. Get `ECModule (L D)` from `RO_Distinguisher.ecModule` and the `fvP_L` bound (`fp_module`
     with `D` in the bound).
  4. Prove the inclusion of the bound's variables in the restriction with `fp_sub`.

## 2026-11-03: `Gconcl_list.equiv_ideal`

* **`RO_LRO_D` inside a game, for a distinguisher that the game builds from its oracle.** Steps:
  1. Define the distinguisher as a module over the random oracle (`D2`, using `(F : F.RO_T)`).
     Its `distinguish` calls an `abbrev` `D2o D F`, the inner `D(…)` call written exactly as
     inlining the game leaves it, after `simp only [DPRIMITIVE.f.mk_simp, …, FUNCTIONALITY.view,
     Valid2, FUNCTIONALITY.f.mk_simp]`. The `abbrev` matters: with an opaque `def` the module
     command cannot prove its `apply_simp` equation. `view`s of terms that depend on the parameter
     must be written out as `DFUNCTIONALITY.mk {f := …}` for the same reason.
  2. Bridges `D2o D F ~ D2(D)(F)`: `equiv_proc_to_stmt` keeps the abstract `D2o` as a call statement, so
     use `stmt_inline` on the wrapper side only, then `equiv_call (prhlProc_refl _)`.
  3. `prhlProc.trans` bridge, `RO_LRO_D`, bridge, then `prhlProc_conseq` down to `g₁ = g₂ ⟹ r₁ = r₂`.
  4. In the game, inline everything, `simp only` the call into `D2o` form, `stmt_wp`, then
     `equiv_call` with that judgment.
* **Keep the wrapped body small.** The module command's elaboration grows quickly with the body
  (`D5o`, with five copies of `DSqueeze2`, took about 5 min, and its footprint bound timed out at
  4M heartbeats). A wrapper around the whole game (`L4F`: `Indif` applied to `L4`'s modules) is
  small, and its bridges need no inlining of `L4`.

## 2026-11-03: `Gconcl_list.squeeze_squeezeless`

* **`P` (= `Perm`, a `StrongPRP.PRP`) as a `PRIMITIVE` does not unfold.** `stmt_inline` and
  `writes_keep` stop at `PRIMITIVE.f … P` ("no concrete procedure body"). Bridges proven by
  `unfold P Perm PRP.RP.RP; simp [PRIMITIVE.f, PRP.StrongPRP.PRP.mk]`: `P_f`, `P_fi`, `P_init`
  (to `RP.f`, …) and `P_view`/`P_view'` (`PRIMITIVE.view P` as `DPRIMITIVE.mk {f := RP.f, …}`).
  * `rw [P_f]` works on a `prhlProc` goal *before* `equiv_proc_to_stmt`.
  * A `simp only [P_init, …]` must come *after* the inlining that exposes the call.
  * For `writes_keep` through a module that calls `P` deeper down (`DSqueeze(SqueezelessSponge(view
    P))`), `rw [P_view']` first: the view is visible in the goal, its callees' bodies are not.
* **Sampling from `dexcepted`.** `equiv_rnd` leaves `∀ a ∈ (dexcepted d P).support, …`. The fact
  `¬ P a` is `not_of_mem_support_dexcepted` (new `Lib/EC/DexceptedSupport.lean`; not in
  `Dexcepted.lean`, whose dependents are a long rebuild).
* **Specifications with logical variables.** For a `call` whose specification mentions values of
  the state (EC: `exists* p{1}, i{1}; elim*`), use `prhlStmt_fix_left f (fun q => ?_)` (in
  `PRHLStmt`), then `equiv_call (lemma q.1 q.2)`. Example: `SS_f_extend bl j` (the squeezing calls
  of `DSqueeze`).
* **`splitwhile` guards.** After `prhlStmt_splitwhile_left e V hvar`, `unfold Getter.andB` before
  `equiv_seq`/`equiv_while{1}`. Otherwise the `exit` goal has the split guard generalized to an
  opaque `Bool`. The `hvar` goal itself takes `simp only [Getter.andB_get, Bool.and_eq_true,
  decide_eq_true_eq]`.
* **`§x` reads in one-sided loop goals.** `equiv_while{1}`'s `lossless`/`variant` hypotheses read
  `§x` (`eval`): `simp only [eval_lens_full, eval_lens_global] at h` turns them into `.get σ` before
  `omega`/`rw`. Before `omega` on `toNat` of reads, `generalize` the reads.
* **Avoiding EC's outer `splitwhile`.** EC splits the squeezing loop to treat its last round apart.
  Instead, a lockstep `equiv_while` whose invariant has the fact about the next prefix under the
  guard (`i < n → prefixes[format p (i + 1)] = …`) needs no split.
* **Index of `stmt_inline`.** `stmt_inline{i} k` counts *call sites*, not statements.

## 2026-11-04: `Gconcl_list.equiv_sponge`

* **Same code on both sides, one side counting.** The left runs `SqueezelessSponge(SLCommon.PC(P))`,
  the right `SqueezelessSponge(P)`, so the loops run in lockstep (no `splitwhile`). Only the counter
  needs a bound. `SS_gen bl s k`: with `take s bl` known, `SLCommon.C.c` grows by at most
  `size bl - s`. The invariant bound is `k + max 0 (i - s)`, and an uncached prefix forces `s ≤ i`
  through `all_prefixes`. One lemma covers absorbing (`s = 0`) and each squeezing call
  (`s = size (format p j)`, so at most `+1`).
* **Counters as Lean parameters.** `DSqueeze_count bl nb k` and `SS_gen` take the bound `k` as a
  parameter. The call sites fix the state's values with `prhlStmt_fix_left`, and `FC_count` fixes
  `(bl, nb, C.c)` before `FC`'s increment.
* **`writes_keep` through `SLCommon.PC(Perm)`.** `rw [Perm_mk]` (`Perm` as `PRIMITIVE.mk {RP.init,
  RP.f, RP.fi}`, by `rfl`) first, as `rw [P_view']` for `view P`.
* **Inlining the game's inits.** `PC(Perm).init` exposes `Perm.init` only after one inlining pass:
  `repeat stmt_inline; simp only [P_init']; repeat stmt_inline`.
* **`rintro … rfl` between two variables** (`p₁ = bl` with `bl` a theorem argument) may eliminate
  the argument. Name the equation and `subst p₁` instead.

## 2026-11-04: `Gconcl_list.equiv_L3_L4`

* **`stmt_inline{i} k` reaches call sites inside loop bodies** (`k` counts call sites). After
  `repeat stmt_inline{1} 0` a loop body is call-free, so the `lossless`/`variant` goals of a
  one-sided `equiv_while{i}` are about samplings and assignments only. `lossless`: `simp [Stmt.ewp_seq,
  Stmt.ewp_assign, Stmt.ewp_sample, Stmt.ewp_ifThenElse]`, then `simp only [Stmt.ewp_skip, ite_self]`
  and the distribution's mass (`bdistr_expected_one`).
* **A discarded `RO.get` of a known entry.** `stmt_wp` folds `get`'s `if`, then `stmt_wp{i} 1` drops the
  draw (with `bdistr_expected_one`).
* **Keep the other side's statements when cutting.** A leading `stmt_wp` folds the other side's
  deterministic suffix (an `if` after a sampling) into the postcondition. Cut around the statements
  instead (`equiv_seq 2 3`, …).
* **`RO_T.get F.RO.asRO` against `RO.get`.** Inlining `sample` exposes `FullRO.RO.get …`, while the
  game's calls read `RO_T.get … F.RO.asRO`. The bridges `F_RO_get_eq` and `F_RO_sample_eq` (`simp`)
  convert between them. `rw` them at the `prhlProc` goal before `equiv_proc_to_stmt`, where the other side's
  module terms are folded.
* **Two spellings of a local read.** `omega` treats `(localVarLens "i" ℤ).get σ` from the program and
  from a `§i` in an invariant as different atoms, because their `autoParam` proofs differ. Restate
  the hypotheses with `have h' : … := by simpa using h` and the goal with `show …`, in one spelling.
* **`rintro` patterns.** An `rfl` against `x = k` with `k` a theorem argument can eliminate `k`; name
  the equation and `subst x`. Count `⟨` for left-nested `((A ∧ B) ∧ C) ∧ D` preconditions: one per
  level.
* **Inside an anonymous constructor**, `fun j h1 h2 => by tac; exact h` swallows the following
  components. Parenthesize it.

## 2026-11-04: `Handle.eq_fi`, `eq_f`, `CF_G1`, `Real_G1`

* **Big oracle steps under `INV_CF_G1`.** Inline both oracles, `stmt_wp` the deterministic tail,
  split the heads with `equiv_if{1}` / `equiv_if{2}` (the impossible combination by `incl`
  through `prhlStmt_pre prhlStmt_false`), couple the samplings with `equiv_rnd`, and close the
  pure goal by cases (EC's `case @[ambient]`: `getflag hs xc` none / Known / Unknown). `simp only`
  with the case facts resolves the `if`s; `simp_reads` the reads. The invariant step of each case is
  a pure lemma (`fi_none_inv`, `f_known_inv`, `f_path_inv`, …), mostly wrapping `lemma1`/`lemma2`/
  `lemma3`.
* **wp blow-up.** Three deterministic `if`s after the samplings make an 8-way post; the inlined
  `RO.get`'s `if` would double it again and `equiv_skip` times out. Cut just before that `if`
  (`equiv_seq 1 3`) with a relation carrying its guard's value (`¬ dom RO x1`, from
  `f_path_ro_none`), and resolve it with `equiv_if{2}` and `prhlStmt_false`.
* **`oget` of a known lookup.** Do not `simp only [oget]`: it unfolds every `oget` and hides the
  rewrite targets. State `have h' : oget (FMap.get m k) = v := by rw [h]; rfl` and `simp only [h']`.
* **Up-to-bad abstract call with a non-equality invariant** (`CF_G1`). `prhlProc_abstract_call_upto_module`
  over a lens `cfL` of every game variable; the invariant `cfI`, `cfBad`, `cfQ` on the tuple
  projections in the order `INV_CF_G1` reads them, so `cfI (cfL.get g₁) (cfL.get g₂) ↔ …` is
  `Iff.rfl`. Oracle premises: `prhlProc_upto_of_writesKeep _ (by writes_keep') (by writes_keep')
  (prhlProc_conseq (eq_f …) …)`, after `unfold PF G1.S` (`writes_keep'` needs concrete bodies).
* **`fp_disjoint` and concrete modules.** It unfolds `PF`, `G1.M`, `G1.S` to their procedures
  (`PF.init`, `G1.M.f`, …), so the `@[fp_bound]` lemmas are per procedure. For `G1.M`, `G1.S` it
  still failed; prove `FVP.fvP (Module.app DFRestr G1.M) ≤ Gᶜ` by hand with `FVP.fvP_app`,
  `fvP_DFRestr`, `fvP_G1M` and `_hGd` turned around (`Footprint.le_compl_comm`).
* **`PF` folded back.** Inlining `CF`'s inits needs `unfold PF`, which also rewrites the
  distinguisher's oracles; `rw [PF_eta, view_PF_eq]` restores `PRIMITIVE.view PF`.
* **Shared tactics moved to `Logic/FrameTactics.lean`:** `fp_mem`, `fp_sub` (from `Gcol`/`Gext`),
  `writes_keep'`, and `hoareProc_const`, `hoare_if_inv`, `hoare_seq_inv`. `repeat' tac; tac'`
  parses `tac'` into the `repeat'`: parenthesize.

## 2026-11-04: `Handle.PFf_Cf`

* **EC's `splitwhile` on both sides** at `i < qpre p Q` (`prhlStmt_splitwhile_left/right`, then
  `unfold Getter.andB` and `equiv_seq 1 1` between the halves). The variant obligation is a Hoare
  triple over the body; it does not write `i` or `p`, so thread `J := (size p - (i+1)).toNat < k`
  through every `if` with `hoare_if_inv` / `hoare_seq_inv` (`hoare_wp` refuses an `if` with
  samplings).
* **Invariants as pure predicates on values.** `PJ1` (first loop), `PJ2L` (left facts, whatever the
  bad event) and `PJ2` (before the bad event) take the variables' values; the relational invariants
  are a few equalities plus `PJ1 §FRO.m{2} … §h{2}`. Every loop step is a pure lemma (`PJ1_step`,
  `PJ2_known`, `PJ2_fresh`, …), proved separately from the programs.
* **EC's `alias{1} 1 prefixes = Redo.prefixes`**: `prhlStmt_fix_left (fun σ => Redo.prefixes.get
  σ.globals)` before the loops. The old `(sa, sc)` of a step, overwritten before the `PF.f` call, is
  fixed the same way, then `equiv_seq 1 1` cuts before the `if`s.
* **Bad case inside a loop body**: `equiv_case (§G1.bcol{2} = true ∨ §G1.bext{2} = true)`. Before the
  bad event the guards of the two sides agree (`lemma5'`); after it, the four branch combinations
  with one-sided samplings (`stmt_wp{i} 1` and losslessness). The right's counter guard is always
  true (counter bound in the invariant), so its `else` is impossible in both cases.
* **Coupling across reordered samplings**: the left draws `y1` then `y2`, the right `sc` then the
  oracle's `r`; `stmt_swap{1} 0 1` swaps the left draws so that `equiv_rnd` pairs `y1↔r`, `y2↔sc`.
* **Goal shapes after `simp_reads`**: some conjuncts become `True` (`p = p`) and stay; add `true_and`
  (and `ite_self`) before `refine ⟨…⟩`.


## 2026-11-04: `ConcreteF.DoubleBounding`, `GReal_GReal'`, `Real_Concrete`

* **`DoubleBounding`, `GReal_GReal'`: the equal-outside abstract call** over a lens of the
  variables that differ (`dbL`, `grL`), with a pure invariant on their values (`dbI`, `grI`). An
  oracle that writes a variable inside the lens is inlined, the inner call taken by
  `prhlProc_self_equal_outside_module`, and the writes by the lens's `equal_outside` write lemmas.
* **`stmt_inline{i} k` counts calls only** (not `reset_vars`, assignments, `var`). When one side
  has an extra call (`CF`'s `FUNCTIONALITY.init`), `equiv_sim` lines up the wrong calls: inline the
  extra one first.
* **Module-view bridges by `rfl`**: `PRIMITIVE.view Perm = SPRP_Oracles.mk {f := PRP.f (PRPi…), …}`,
  the same for `PF`, `DPRIMITIVE.mk {f := PRIMITIVE.f PF, …}`; `Perm_init_eq` and `PF_init_eq` by
  `simp`. `Perm.f` is lossless after `rw [← PRIMITIVE.view_f, view_Perm_eq, dprim_f_mk]` (then
  `phoare_ewp` and `excepted_lossless`).
* **`fp_disjoint` limits met here.**
  - An `@[fp_bound]` lemma does not fire under `glob` or for a functor parameter (`CO`) whose module
    type is spelled differently. Instead, prove the side condition by hand with
    `Footprint.le_compl_glob_symm`, `Footprint.globalVar_le_compl_glob` and the bound (`fvP_Perm_sup`).
  - `DFUNCTIONALITY.mk {f := …}` unfolds into its expression form. Use `FUNCTIONALITY.view X` (equal
    by `rfl`, `view_SS_eq`) and `rf_ll'` (no `{-C}`).
  - A variable against a named footprint on the right (`≤ C.footprintᶜ`) needs `unfold C.footprint`.
  - An abstract region against a join (`G ≤ (… ⊔ …)ᶜ`): `Footprint.le_compl_comm` and `sup_le`, by
    hand.
* **Fresh lenses outside `G`**: `Footprint.exists_fresh_glob T hGF hR` with `G ≤ GF.glob` gives
  `L ≤ GF.globᶜ`, hence `G ≤ Lᶜ`. A `Lens.Disjoint` instance with a `global_var` comes from
  `Lens.disjoint_of_footprint_le_compl … (by fp_disjoint)`; add the `.symm` too (instance search
  needs both orders).
* **The `Pr` chain** in ℝ: `rw` the NNReal equalities under the casts, `exact_mod_cast` for `≤`,
  `abs_sub_le_iff.mp` for `Conclusion`, then `linarith`.

## 2026-11-04: `SHA3Indiff`

* **Two wrappers counting in different variables** (`drestr_commute`: `Cntr.c` vs `BlockSponge.C.c`):
  the equal-outside abstract call over `Lens.pair Cntr.c C.c` with `I := Cntr.c{1} = C.c{2}`, proven
  once for any `F`, `P` (`dc_dist`) and instantiated for the real and ideal games.
* **Two simulators with different variables** (`replace_simulator`): equal outside the six
  variables (`sL`), with the cross equalities `sI`.  Writes inside `sL` on one side by
  `Lens.equal_outside_set_self`/`pair_left`/`pair_right` and `.symm`/`.trans`
  (`Logic/EqualOutside.lean`); the same write outside `sL` on both sides by `set_disjoint`.  Inner
  calls of `F`, `IRO2` by `prhlProc_self_equal_outside_module`.
* **`Module.comp`** (`RaiseSim`) does not inline: state `X.f (Module.app (RaiseSim S) F) =
  X.f (Module.app S (Module.app LowerFun F))` as a lemma (`rw [RaiseSim, Module.app_comp]; rfl`) and
  `rw` with it — rewriting the goal directly with `Module.app_comp` leaves a term `stmt_inline`
  cannot unfold.
* **Program variables in `equiv[…]` relations**: `§y{2}` resolves only if the *left* program
  declares `y` too; otherwise write `§(localVarLens "y" T){2}`.  An inlined parameter (`a` of a
  module procedure) may not be in the `var` list at all: also `localVarLens`.
* **`fp_disjoint`**: bound lemmas for bit-level `IRO.init`/`IRO.f` (`Bool` output), `FC`, `PC`,
  `RaiseFun`, `BlockSponge.Sponge`; an instance `Lens.Disjoint X sL` is not found once the goal
  shows `sL` unfolded: pass it with `@Lens.equal_outside.set_disjoint _ sL _ X inferInstance …`.
* **Simulators are representable** (`Examples/SHA3/SimulatorRepresentable.lean`): `f`, `fi`,
  `init` as functors `.abs (proj (.app S.expression (.var 0)))`, represented by
  `Module.exists_representation_of_firstOrder`; `init`'s hole filled with a global-free procedure,
  given `init` independent of the oracle (for `SimLast(Gconcl.S)` by `simp only [*.apply_simp,
  PRIMITIVE.init_pair]`).

## 2026-11-05: `SHA3Security`

* **EC's `transitivity{1} { c } (E ==> F) (P ==> Q)`** with a reflexive `E`: `prhlStmt.trans_left`
  (`Logic/PRHLTransitivity.lean`); the middle program written out in `equiv[ … ] {…} ~ {…}`, the
  second leg left as the goal with postcondition `∀ τ₁, F τ₁ τ₂ → Q τ₁ τ₃`.  A sampling against a
  call of `LoopSnoc.sample`: `prhlStmt_seq_sample_run_map_right` with `LoopSnoc.sample_denotation`
  (`equiv_ro_iro`, after `BlockGen_direct_BlockGenCall`).
* **The frame of a `call`** (`Logic/PRHLFrame.lean`): `prhlProc_frame_lens X₁ X₂ h₁ h₂ R h` adds a
  relation of lenses outside the callees' footprints; `prhlProc_frame_equal_outside(_module) L`
  adds `L.equal_outside` for callees confined to `L`.  So a local equivalence about part of the
  state (`equiv_sponge_perm`, `equiv_ro_iro`) serves as the oracle premise of
  `prhlProc_abstract_call_equal_outside_module`.
* **`fp_le`** (`Logic/FootprintUpper.lean`): `FVP.fvP M ≤ X₁ ⊔ … ⊔ Xₙ` through the module
  combinators, by `@[fp_bound]` lemmas (leaves by `fp_module`) and bound hypotheses; with
  `FVP.fvP_comp_le` for `Module.comp`.  `fp_module` on a big composite module times out: bound the
  pieces and compose with `fp_le`.
* **Equal-outside over a `def` lens**: make the lens (`realL`, `idealL`) a `def` (judgment simp
  unfolds `Lens.pair`), with a `@[simp]` `get` lemma, a `footprint` lemma, `X.set v g = L.set w g`
  lemmas for its components, and `instance : Lens.Disjoint Y L := by unfold L; infer_instance`.
* **Rewriting a callee whose module types are spelled differently** (`CONSTRUCTION` at the clone's
  types vs `Sponge`'s, defeq): `rw` fails, `erw` succeeds; a bridge lemma about
  `@Module.app (T := …)` with the goal's spelling makes plain `rw` work.  `fp_disjoint`'s
  `@[fp_bound]` matching is reducible: state the bound at the goal's spelling (`fvP_Perm'`,
  `fvP_CSetSize_Sponge'`), or give a restriction hypothesis.
* **Parse trap**: a bare `fp_module` ending a proof takes a following `set_option … in` (or
  `open … in`) line as its optional term argument.  Put such declarations after one that does not
  end with `fp_module`.
* **`fp_disjoint` against `glob (fvP M)` of a concrete module** (`DistRestrictions` has
  `glob (SimLast(Gconcl.S))`): it may panic.  Turn it around by hand:
  `(Footprint.le_compl_comm _ _).mp (Footprint.le_compl_glob_symm hMfs (by fp_disjoint))`.
* **Losslessness with an abstract adversary** (`Dist_lossless_at` of `DSetSize(D(A))`): the
  oracle's `get` lossless by `phoare_wp`/`phoare_simp [fll]`; `A_ll` for `A`'s; then the game:
  `phoare_inline` (twice, for the `if`'s call), `phoare_wp n`, `phoare_simp [fll]`, `phoare_skip`,
  `simp only [ite_self, fll']` and `exact hAll _ _ trivial` (`phoare_simp` does not take `ite_self`).

## 2026-11-05: `SHA3_OIndiff`

* **Counts.** `equiv_seq n₁ n₂ : M` counts the statements of the *second* (trailing) block on each
  side.  `stmt_inline{i} k` counts *call sites*, not statements (`k = 0` is the first call,
  wherever it is, also inside a branch).
* **EC's `rcondt{2}`/`rcondf{2}` on an inner conditional**: cut so that the conditional is the
  whole right statement (`equiv_seq 1 1`, the left call kept for the second block), then
  `equiv_if{2}`; the infeasible branch by
  `refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)` and the guard
  (`simp only [decide_eq_false_iff_not] at hg`).
* **A counter value through a call** (EC's `exists* c; elim*`): `prhlStmt_fix_left (fun σ => …)`
  fixes it as `q`; then the callee's judgment at a relation `J` of the counters' contents built
  from `q`.
* **Reusable oracle steps over an equal-outside lens**: state the callee step for *every*
  relation `J` of the lens' contents (`SomeEquiv`, `∀ J, prhlProc (… ∧ L.equal_outside ∧ J …)`),
  so the wrappers (`opc_f`, `ofc_f`) instantiate it at the counter values they fix.  A callee
  outside the lens is `prhlProc_self_equal_outside_module L _ hfp J`; a procedure on the right
  with no body (`Perm.f`) stays an opaque call after `equiv_proc_to_stmt`.
* **Same write on both sides of a variable outside `L`**: `he.set_disjoint v`, reads by
  `he.get_disjoint` (`instance : Lens.Disjoint X L := by unfold L; infer_instance`).  The
  judgment simp already turns `J (L.get (X.set v g))` into `J (L.get g)`.
* **`fp_disjoint` for `X ≤ (glob (fvP M))ᶜ` joinands**: prove the `glob` joinand once
  (`Footprint.globalVar_le_compl_glob hMfs x (by fp_disjoint)`) and match it with
  `first | with_reducible exact hg | fp_disjoint`; trying `le_compl_glob_symm` on every joinand
  times out (`whnf` of the unification).
* **`lean_multi_attempt`**: multi-line snippets get mangled; join tactics with `;` in parentheses.

## 2026-11-05: `SHA3OSecurity` (started)

* **A dlist sampling against a loop** (EC's `transitivity{1} { z <@ LoopSnoc.sample(n); }`):
  `prhlStmt_dlist_left` / `prhlStmt_seq_dlist_left` (`Lib/EC/DListCall.lean`, EC's
  `Sample_LoopSnoc_eq` at the statement level) replace the sampling by the call; then
  `stmt_inline` and a lockstep `equiv_while`.  The one semantic fact is in the library rule.
* **Lenses with an abstract local variable** (`Log.m`, a lens parameter, E6): `Lens.pair` needs
  `Lens.Disjoint` instances, from `LocalFresh` by `Lens.disjoint_of_footprint_le_compl` (`haveI`);
  make the pair a `def` taking the instances.  Writes of a pair component keep a state equal
  outside the pair: `(Lens.equal_outside_set_self _ g v).pair_left` / `.pair_right`, chained with
  `.trans`/`.symm`.  `simp_reads` can hang on a goal with a write of the abstract lens: close
  such goals with `change` and the lens laws (`set_get`, `Lens.get_of_disjoint_set`).
* **`fp_module (Lens.pair Log_m G)`** for a module writing an abstract lens and globals: give the
  lemma both-direction `Lens.Disjoint` instances between `Log_m` and each global of `G`, or the
  lens-law goals stay open.
* **`prhlStmt_seq_call`** needs the call *last*: cut after it (`equiv_seq 1 1`) when more follows.
* **Module-type spellings** (`OPRIMITIVE state (List Bool) f_out` vs `… (List Bool × ℤ) (List
  Bool)`, defeq): restate rewrite lemmas at the other spelling (`PSome_init'`), `erw` for
  `ODPRIMITIVE.f.mk_simp` across spellings, and state oracle lemmas with the simplified right side.
* **`Footprint.FinitelySupported.mono h (hG.sup ?_)`** inside a `refine` leaves `?_` an unresolved
  metavariable: prove the finite support in a separate `have` with its type.

## 2026-11-05: `SHA3OSecurity`, section `Preimage` complete

* **Generic congruences for the ideal game** (top of `SHA3OSecurity.lean`, reusable by the other
  sections): `osim_congr_f` (`OSimulator(F₁).f ~ OSimulator(F₂).f` from `F₁.f ~ F₂.f`, over
  `ODFUNCTIONALITY`s, a relation `I` before and a weaker `J` after: the simulator calls `F.f` at
  most once), `osim_congr_fi`, `opc_congr_f/fi` (counter outside the lens), `ideal_game_congr`
  (`OIndif(F₁, OSimulator(F₁), D) ~ OIndif(F₂, OSimulator(F₂), D)`, `D` one abstract call).
  When the counter is *inside* the lens (`fL`), write the `OPC` step by hand (`fin_pf/pfi`).
* **Lifting a local equiv to an equal-outside invariant**: `prhlProc_frame_equal_outside_module`
  (callees within the lens; bounds by `fp_module L` or `fp_le`) and `prhlProc_frame_lens`
  (a relation of variables the callees do not touch), then `prhlProc_conseq`
  (`eager_f_lazy`, `eq_extend_lift`, `eq_IRO_RFWhile_frame`).
* **Two lenses, one relation**: `L := Lens.pair X₁ X₂` with `I v₁ v₂ := v₁.1 = v₂.2` relates
  `X₁{1}` to `X₂{2}` (`eagerL`, `xL`, `fL`); component writes keep the states equal outside `L`
  (`(Lens.equal_outside_set_self _ g v).pair_left`, `.pair_right` nested for deeper components).
* **Different init orders in the two prefixes**: chain `equal_outside` steps (component writes,
  `.set_disjoint` for equal writes outside the lens) and commute the writes of disjoint lenses:
  `have d : Lens.Disjoint X Y := inferInstance; rw [d.commute]` (`(inferInstanceAs …).commute`
  does not elaborate).  Align the samplings first with `stmt_swap{i} n k`.
* **One-sided lossless code** (the right runs, the left does not, the post is about the left):
  `prhlStmt_conseq` to a left-only post, `equiv_if{2}`, `equiv_while{2} I V` (cases `lossless`:
  `simp only [Stmt.ewp_seq, Stmt.ewp_assign, Stmt.ewp_sample]; exact (is_lossless_iff_expected
  _).mp dbool_ll`; `variant`: `hoare_wp; hoare_skip`; `exit`).
* **A call wrapper against its callee** (`Dist(F).distinguish` vs the game it calls):
  `equiv_proc_to_stmt; stmt_inline{1} 0; stmt_wp; simp only [view]; equiv_call (prhlProc_refl _)`.
* **Probability chains**: `.trans`/`.symm` of `Procedure.Pr_eq_of_prhlProc (a₁ := ()) (a₂ := ())`;
  a real-valued `≤` by `exact_mod_cast Procedure.Pr_le_of_prhlProc`.
* **Pitfalls**: a precondition on an argument's projection (`a₁.2`) came out as `sorry` (inline
  the caller instead; the cause: unknown signatures, see 2026-11-06); `simp_reads` unfolds an abbreviated pair lens into a
  structure, on which `Lens.Disjoint` instance search fails (state helpers on the named lens:
  `hLog : (fL _).equal_outside g₁ g₂ → Log_m.get g₁ = Log_m.get g₂`); `omega` needs `dsimp only`
  on tuple projections and treats syntactically different `increase_counter` terms as distinct
  atoms (derive the bound with `(lt_increase_counter _ _ _).trans_le hg`); `-` is not a `fun`
  pattern (use `_`); a lemma whose only use of a section variable is a hypothesis drags it into
  every user (`eq_IRO_RFWhile` lost its unused `LocalFresh`).
* **Section instances**: `variable [Lens.Disjoint …]` in a section; the closing lemma derives
  them from `LocalFresh` with one helper `hD Y X hY hX : Lens.Disjoint Y X ∧ Lens.Disjoint X Y`.

## 2026-11-06: `SHA3OSecurity`, section `SecondPreimage` complete

* **Duplicated local modules**: EC's sections repeat `RFList`, `RFWhile`, `ExtendOutputSize`,
  `ExtendSample`, `Fill_In`; the Lean copies are definitionally equal (`rfl`), so the repeated
  local equivs are `exact Preimage.…` (also for `Collision`).  Shared proofs with a parameter for
  what differs: `Preimage.eager_ideal_of` (any distinguisher `D` and `RO_Distinguisher` with a
  `Dist_game`), `soro_spre_game` (`soro_pre_game` for `SORO.SecondPreimage`).
* **`a₂` in a precondition elaborates to `sorry`** when the judgment's signatures are not yet known
  (`prhlProc` takes them from the procedures, after the precondition): give
  `(sig₁ := procsig () -> Bool) (sig₂ := procsig (List Bool) -> Bool)`.  This, not `equiv_proc_to_stmt`,
  is the cause of the earlier `a₁.2` pitfall.
* **EC's `call` frames what the callee does not write; ours does not.**  A variable read after a
  call (`Dist_of_P2Adv.m`) needs `prhlProc_frame_lens X X h₁ h₂ R spec`, `h` from a footprint bound
  (`ProgramDenotation.inFootprint_mono (Module.Proc.inFootprint_fvP _ a) hb`).  For an abstract
  call `Module.app A O`: `(FVP.fvP_app _ _).trans (sup_le hA hO)`, with `hO` a separate lemma
  about the oracles (`fp_module` inside a big proof exhausts its heartbeats; on a big
  `Module.pair` it may give up: `rw [FVP.fvP_pair]` and bound the halves).  Leave the frame's
  footprint obligations as named holes (`?hfr₁`, not `?h₁`: `equiv_seq` uses that tag) closed after
  the abstract call, or the oracle metavariable gets an abbreviation whose type parameters differ
  and `Module.snd_pair` stops matching.
* **EC's `exists* e{1}; elim* => v`** is `prhlStmt_fix_left (fun σ => …) fun v => ?_`; EC's `case`
  is `equiv_case P`.  A trailing call coupled only by losslessness (`ll_get`): one-sided
  `equiv_seq 1 0 / 0 1`, `equiv_if{i}`, `equiv_while{i} I V`; a variant through an `if` with a
  sampling: `hoare_split 1; refine hoare_seq (hoare_if_wp (hoare_seq (hoare_assign_wp _ _ _)
  (hoare_sample_wp _ _)) (hoare_skip_wp _)) ?_`.
* **Reads through a call's frame** (`(Setter.throwaway.set r (ProgramState.globalL.set g τ))`):
  `.globals` is `g` by `rfl`; a local read through `resetSetter`: `show` it on the reset alone,
  `erw [intoLocal_varLens_get_resetSetter]; rw [if_neg (by simp [stringsStartingWith])]`.  Better:
  split the argument copy off with `equiv_seq` first, so `equiv_skip` generalizes it.
* **Running a game from a modified state** (EC's `TOTO` wrapper setting a local variable):
  `Pr_eq_of_prhlProc (prhlProc_self_equal_outside_module X G hG (fun _ _ => True))` between `m`
  and `X.set v m`, `G` not touching `X`.
* **A section closed too late** (missing `end FinSim`) shows only as errors at the namespace's
  `end`; the declarations in between silently gain the section's instance arguments.

## 2026-11-06: `Gconcl_list.Real_lossless` (the last `sorry`)

* **No lossless abstract call under an invariant is needed.**  EC's `call (: invm Perm.m Perm.mi)`
  only provides `useful` (losslessness of `dexcepted dstate (rng Perm.m)` for a fresh key).  A
  finite map missing a key misses a value, so `Perm.f`/`Perm.fi` are lossless in every state
  (`ConcreteF.Perm_f_ll`, reused by defeq as `Gconcl_list.P_f_ll`), and `D_ll` applies directly,
  as in `Ideal_lossless`.  `Sponge_f_ll`: two counted loops (`phoare_split 1;
  refine phoareStmt_seq_ge_one`, then `phoare_while_ge 1 variant …` per loop).
* **Inlining the real game stops at `P.init`** (`P = Perm`, an `RP` read as a `PRIMITIVE`):
  `simp only [P_init]` first, then `repeat phoare_inline 0`.
* **`fp_module` takes an optional term**: a following `open X in` (term-level `open … in`) is
  parsed as its argument.  Put a declaration without `open … in` after a lemma ending in
  `fp_module`.
