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
