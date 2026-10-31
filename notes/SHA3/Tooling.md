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
