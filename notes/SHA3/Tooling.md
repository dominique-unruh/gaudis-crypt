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
(`adversary_count`).  The oracle premise (`count_query`) is `equiv_proc; stmt_inline 0; stmt_wp;
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
* `equiv_proc`, `Judgment.descsOf`, `prhlGoal` read the goal through `cleanupAnnotations`: after a
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
