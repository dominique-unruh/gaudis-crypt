# SHA-3 port: deviations from the EasyCrypt structure

Each deviation from the mapping rules in `README.md`, with its reason.  Identifiers: `E<n>`.

## E1: EasyCrypt names are kept verbatim (project convention)

**Rule broken.** The project convention (CLAUDE.md, "Name spaces, file names, naming
convention") asks for Mathlib-style names.

**What we do instead.** The port keeps EasyCrypt's names exactly, including their
capitalization and underscores: `Sponge_coll_resistant`, `eager_invar`, `Gconcl_list`, ….
The Lean file names follow the EasyCrypt file names in the same way.

**Why.** The mapping must be mechanical: from an EasyCrypt name you find the Lean declaration
by `grep`, and the reverse.  It also keeps `Mapping.md` checkable.

## E2: abstract modules carry a representability hypothesis (temporary)

**Rule broken.** EasyCrypt's `declare module D <: DISTINGUISHER {-O}` is mapped to a module
variable plus a footprint hypothesis, as the conventions say:

```
variable (D : Module.Arr (oracle module type) (procmod …)) (hdisj : FVP.fvP D ≤ (L.footprint)ᶜ)
```

There is one extra hypothesis, `hD : Module.Representable D ext`: applied to any oracles `O`, `D`
has the same denotation as some procedure with holes filled with `ext O`, and touches nothing more
than `D` (`Logic/AbstractCall.lean`).  `ext` lists the oracle procedures `D` may call.

**EasyCrypt counterpart.** None is needed: `hD` holds in EasyCrypt by construction.
* An EasyCrypt module is program code.  Its module type lists the oracle procedures each
  procedure may call (`{ P.f }`, or all procedures of the parameters when there is no list).
* Applying a functor binds those calls to the given modules.  So "`D` applied to oracles is code
  with its oracle calls filled in" holds by definition.
* EasyCrypt's abstract call rule (`proc inv`, kernel function `equivF_abs_spec` in
  `src/phl/ecPhlFun.ml`) is a trusted kernel rule over that code.  It produces one premise per
  allowed oracle (`OI.allowed`), and it rejects an `inv` that depends on `glob D`
  (`PV.check_depend`).

**Why we need it.** Gaudí's module language is a small λ-calculus (functors, pairs, projections,
nested applications), so the representation must be proven.  Gaudí proves the abstract call rule
as a theorem, by induction over the adversary's code, so it needs that code
(`prhlProc_abstract_call_module`).

**How to remove it.** Either:
* prove that every module of a functor type is representable; or
* prove the abstract call rule by induction over the normal form of a module expression.  This
  route avoids flattening nested applications into one procedure with holes, which a call's
  closed callee body does not allow.

`hD` then disappears from every statement mechanically.

**Status (2026-11-01): the first route is done for full oracle lists.**
`Module.representable_of_firstOrder` (`Logic/Representation.lean`) proves `Module.Representable D
ext` for every functor module `D` over a first-order module type (a tree of products of
procedures, as `moduletype` builds them) whose `ext` is the full list of the type's procedures,
provided those procedures' parameter and result types are nonempty (they live in local slots of
the extracted code).  The representation is extracted from `D`'s own normal form; nested
applications are flattened by `ProcedureWithHoles.substHoles`, with the inliner's term-level
lemmas.  Instances: `PROM.FullRO.RO_Distinguisher.representable`,
`FRO_Distinguisher.representable` (so `RO_Distinguisher.ecModule` needs only finite support).
Where `ext` is a restricted list (EasyCrypt's `{HI.f}`, `OI.allowed`, e.g. `HYBRID_IRO_DIST.ext`),
`hD` stays: our module types do not restrict which oracle procedures a functor calls.

**The hypothesis is not vacuous.** Every functor module written with the `module` command satisfies
it, by `Module.representedBy_of_app_eq` (`notes/SHA3/Tooling.md`, test `guess_representable`).  So
a theorem assuming `hD` applies to every distinguisher one can actually write.  What is not yet
proven is that the hypothesis holds for every module of the type: that is the representation
lemma.

**Constructions are not covered yet.** The representation is defined for a functor returning one
procedure (a distinguisher).  A construction `CO : CONSTRUCTION` returns a functionality with
several procedures, so `SLCommon.Pr_restr` has no `hD` for it.  This will be extended when a
proof needs the abstract call rule on a construction.

**Affects** every `declare module` whose module type takes oracles: the distinguishers and
adversaries of `Indifferentiability`, `SecureRO`, `SecureORO`, `SecureHash`, `SHA3Security` and
`SHA3OSecurity`.

**Bundled with finite support (2026-11-01).** Statements carry `Module.ECModule D ext`, which is
`Module.Representable D ext` together with `(FVP.fvP D).FinitelySupported` (E6): EasyCrypt's modules
are both representable and have finitely many global variables.

## E3: a module type that shares its name with a module gets the suffix `_T`

**Rule broken.** EC names are kept verbatim (E1).

**What we do instead.** EasyCrypt keeps module types and modules in separate namespaces:
`IRO.eca` has both `module type IRO` and `module IRO`, and `SecureORO.eca` has both
`module type RF` and `module RF`.  In Lean they would clash, so the module type is named
`IRO_T` (`RF_T`).

**Affects** `IRO.eca` and `SecureORO.eca`.  These are the only two clashes in the development,
found from the inventory.

## E4 (resolved 2026-10-31): clones of a theory at the same types shared module variables

This exception no longer applies.  Generic modules declared their variables once
(`global_var PRP.RP.m : FMap D D`), so two clones at the same types shared them, where EasyCrypt
gives each clone its own copy.  `Gconcl_list` needs two random oracles at the same types in one
game (`F` and its clone `F2`, both `block list -> block`), so the sharing would have changed the
game.

**Now**: generic modules take their variables as lens parameters (`PRP.RP.RP D dD m mi`,
`PROM.FullRO.RO … m`, `IRO.IRO … mp`, `Strong_RP_RF.ARP … coll m mi`).  Each clone declares its
own `global_var`s under EasyCrypt's names (`Perm.m`, `F.RO.m`, `F2.RO.m`, `ROhandle.FRO.m`,
`Switching.PRPi.m`, `BIRO.IRO.mp` …) and passes them, as EasyCrypt's clone semantics demands.

## E5: procedure aliases inside a functor are wrapped in a call

**Rule broken.** EasyCrypt's `proc f = M.g` makes `f` the very procedure `M.g`.  Elsewhere the port
keeps that: modules with aliases are Lean functions assembling the aliased procedures with `T.mk`
(`PRestr`, `FRestr`, `Squeeze`, `IF'`).

**What we do instead.** A few modules alias a procedure of a functor applied to their own module
parameters and are used as functors themselves: `Gconcl_list.SimLast(S)(F)`
(`proc f = S(Last(Valid(F))).f`) is a `SIMULATOR`, and `Gconcl_list.DValid(D)(F)(P)`
(`= D(FValid(F), P)`) is a `DISTINGUISHER`.  A Lean function cannot be a functor module, and the
`module` command cannot alias.  So their procedures call the aliased one:
`proc f (x) { y <- call (S(Last(Valid(F)))).f (x); return y }`.  The denotation is the same; the
code has one more call.

`Sponge.LowerDist(D, F) = D(RaiseFun(F))` is a whole-module alias of the same kind: `D` applied to
only one of its two oracles, used as `LowerDist(Dist) : BlockSponge.DISTINGUISHER`.  Its
`distinguish` calls `D(RaiseFun(F), P).distinguish`.  `SHA3_OIndiff.FSome(F)` (`proc init = F.init`) is used as a functor
by `CSome`, so its `init` calls `F.init`.  So do `SecureORO.RF(R)` (`proc init = R.init`,
`proc sample = R.sample`) and `SecureORO.Bounder(F)` (`proc sample = F.sample`).  In `IndifRO_is_secure`:
`FInit`, `GetF`, `SInit`, `FM` and `DColl`.  In `SHA3Security`: `CSetSize`, `FSetSize`, `DSetSize`.  In `SHA3OSecurity`: `FSetSize`, and the
sections' `FInit`, `PInit`, `OF`, `ExtendOutput`, `ExtendSample`, `Fill_In`, `Dist`.

**How to remove it.** Combinators building a functor from its fields, so that the alias is the
same procedure.  For a whole-module alias with a composite body, `Module.comp` already exists
(`BlockSponge.Sim`, `Gconcl_list.S2`).

## E6: variables of local clones and local modules are lens parameters, fresh by hypothesis

**Rule broken.** A Lean statement has the EasyCrypt statement's hypotheses, no more.

**Why.** EasyCrypt gives a `local clone` (or a `local module`) declared in a section new variables,
disjoint from those of every module the section declares (`declare module D`).  The section's
lemmas may rely on that, and the non-local results do not mention the local variables at all.  A
fixed `global_var` cannot express this freshness: nothing stops an arbitrary `D` from touching it.
A local lemma would then need a hypothesis `D` disjoint from it, and the non-local result, which
is proven from the local lemmas, could not discharge that hypothesis.

**What we do instead.** The variables of a local clone are lens parameters of the local declarations
that mention them, with hypotheses that they are fresh for the section's modules:
* in `Sponge`'s `HybridIRO` section, `ERO`'s `ERO_RO_m`, `ERO_FRO_m` (hypotheses `_hDd`, `_hERO`);
* in `Sponge`'s last section, `HIRO`'s `HIRO_Lazy_mp`, `HIRO_Eager_mp` (`HIRO_fresh`, which also
  asks them finitely supported, as `HybridIROExper_Lazy_Eager` needs; `IdealIndif_IRO_BlockIRO`
  chooses them with `Footprint.exists_fresh`).
* in `SecureRO`, `SecureORO` and `SHA3OSecurity`, the variables of the sections' local modules
  (`SecondPreimage2.m2`, `D1.m1`, `Log.m`, `RFList.m`, `Dist_of_P2Adv.m` …; `LocalFresh` in
  `SHA3OSecurity`).

The non-local results (`HybridIROExper_Lazy_Eager'`, `IdealIndif_IRO_BlockIRO`, `conclu`,
`conclusion`) have exactly EasyCrypt's hypotheses.  Their proofs need a **fresh-variable lemma**.

**The fresh-variable lemma needs finite support (2026-11-01).**  It is false for an arbitrary module,
representable or not: a statement's getters are arbitrary functions of the state, so a module may
read every `ℤ`-typed slot, and then no `ℤ` variable is fresh for it.  EasyCrypt's modules have
finitely many global variables.  `Logic/FreshVariable.lean` states that as
`Footprint.FinitelySupported` (the footprint lies within the slots of finitely many variable names)
and proves `Footprint.exists_fresh`: under it, there is a fresh variable of any nonempty type, itself
finitely supported, so several can be chosen in turn.  The non-local results therefore need finite
support of their abstract modules.  It is bundled with representability (E2): every abstract module
of a ported statement carries `Module.ECModule D ext := Module.Representable D ext ∧
(FVP.fvP D).FinitelySupported` ("`D` is an EasyCrypt-like module"; `SIMULATOR.ECModule` for a
simulator), decided 2026-11-01.

**Module variables of the generic theory, too (2026-11-01).** A fresh variable must avoid the
section's own module variables as well, and those are lens parameters (E4).  So a non-local result
that picks fresh local variables also takes finite support of the lens parameters it must avoid.
First case: `Sponge`'s `HybridIROExper_Lazy_Eager'` and `HybridIROExper_Lazy_Eager` take
`HybridIROLazy_mp.footprint.FinitelySupported` and `HybridIROEager_mp.footprint.FinitelySupported`.
A clone instantiating them with `global_var`s discharges them by
`Footprint.FinitelySupported.varLens`.

**Applied everywhere (audit 2026-11-01).** Every `local clone` and every `local module` with
variables in the development:
* `ConcreteF`: the clone `Switching` (`PRPi_m`, `PRPi_mi`, `ARP_coll`, `ARP_m`, `ARP_mi`,
  `DBounder_FBounder_c`; `DoubleBounding`);
* `Gcol`: `Gcol.count` (`Gcol_count`; `Pr_col`, `G1_col`);
* `Gext`: `ReSample.count` (`ReSample_count`; `Pr_ext`, `EG2_Gext`, and `RROset_inv_lt` with only
  `GcolFresh ReSample_count`, outside `G1` and `C`: it does not call `D`); `Real_G2` picks it with
  `Footprint.exists_fresh`;
* `Gconcl_list`: the clone `IRO2` (`IRO2_RO_m`; `equal1`, `equal2`);
* `Sponge`, `SecureRO`, `SecureORO`, `SHA3OSecurity`: as listed above.
  `SecureRO.RO_is_second_preimage_resistant` (proven 2026-11-01) picks `SecondPreimage2.m2` and
  `D1.m1` fresh, so it takes finite support of `Bounder.bounder`, `Counter.c`, `RO.m`, `FRO.m`
  (the clone's variables, lens parameters); `IndifRO_is_secure`'s
  `second_preimage_resistant_if_indifferentiable` passes the same four on for `SRO`.
  `SecureORO.RO_is_preimage_resistant` (proven 2026-11-02) picks `Preimage2.hash` fresh and takes
  finite support of `Bounder.bounder`, `RO.m`; `SecureORO.RO_is_second_preimage_resistant` picks
  `SecondPreimage2.m2`, `D1.m1` fresh and takes finite support of `Bounder.bounder`, `RO.m`,
  `FRO.m`.

The other local clones have no module variables (`ConcreteF`'s `ProdSampling`), or clone a theory
whose own local modules do not survive the clone.  `Gconcl`'s `local clone import Gext as Gext0` is
the exception: its (non-local) module variables are fixed `global_var`s (E13).


## E7: a restriction against a module is stated against its `glob` (variable level)

**Rule changed** (2026-11-01, Denis's decision; evaluation in `GlobGranularity.md`).  EasyCrypt's
`X <: T {-M}` for a module `M`, and a restriction like it in a lemma's or an axiom's premise
(`forall (F <: FUNCTIONALITY {-A})`), is

```
FVP.fvP X ≤ ((FVP.fvP M).glob ⊔ …)ᶜ
```

and no longer `FVP.fvP X ≤ (FVP.fvP M ⊔ …)ᶜ`.  `Footprint.glob` (`Logic/Granular.lean`) is
EasyCrypt's `glob M`: the slots of the variables `M`'s footprint touches, whole (its granular
cover under `variableGranularity`, whose grains are the variables).  Restrictions against
variables (`{-Bounder}` as `Bounder.bounder.footprint ⊔ Counter.c.footprint`, `{-C}` as
`C.footprint`) are unchanged: they are variables already.

**EasyCrypt counterpart.** Exactly `{-M}`: EasyCrypt's memory is a set of variables, and `{-M}`
excludes every variable of `glob M`.  The previous translation was weaker: two modules can have
disjoint footprints and still touch the same variable (one `v.1`, the other `v.2`).

**Why.** A one-sided run of an abstract procedure (EC's `call{1}`, as in `IndifRO_is_secure`'s
`GIdeal_Collision_RO`) must leave `={glob A}` intact, and the framework can frame a run only
against a region with a reset (`CounterExamples/FramingNeedsReset.lean` shows that
footprint-disjointness alone does not frame).  A `glob` is a lens region, so it frames
(`ProgramDenotation.preserves_touched_of_glob`).

**Consequences.**
* All 53 such hypotheses (52 in the SHA-3 files, 1 in `Lib/EC/Strong_RP_RF`) and the named
  restriction footprints (`SHA3Indiff.DistRestrictions.footprint`) were converted.
* A hypothesis about an abstract module's `glob` is a premise about whole variables, so a lemma
  with it in a hypothesis position asks more, and one with it in a premise (`D_ll`, `∃ S`) gives
  more: both as in EasyCrypt.
* `glob M ≥ fvP M` (`Footprint.le_glob`), so the old form follows; `fp_disjoint` uses it.  For a
  concrete module, `glob` is bounded by its variables (`FinitelySupported.glob_le_compl_varLens`).
* An abstract module against the module variables of a *generic* theory (lens parameters, E4/E6)
  is stated the other way round, as `(FVP.fvP X).glob ≤ (vars)ᶜ` (2026-11-02, `Strong_RP_RF`'s
  `Conclusion`, `PartialConclusion`, `pr_PRPi'_Indirect_ARP`): a lens parameter need not be a
  single variable, and `glob X` is outside it only if said so.  For `global_var` instances it
  follows from `FVP.fvP X ≤ (vars)ᶜ` and `X`'s finite support, which `fp_disjoint` does
  (`varLens_le_compl_glob`); `fp_disjoint` uses a hypothesis `glob X ≤ Sᶜ` for a lens parameter in
  `S` (and any `T ≤ Sᶜ` for a region `T`).

## E8: the abstract call rule's side conditions in a generic theory

**Rule added** (2026-11-01).  Where a lemma of a generic theory calls an abstract adversary with
the abstract call rule (`prhlProc_abstract_call_module`), it has two more hypotheses:
* `[Countable T]` for the type `T` of the oracle's arguments (the rule's `hc`): the coupling of
  the adversary's runs is glued along the oracle calls, which needs countably many call points;
* `[Lens.Disjoint X Y]` for the theory's module variables that make up the oracle state (E4: they
  are lens parameters), which the invariant reads as one lens (`Lens.pair`).

First used in `IndifRO_is_secure` (`GIdeal_Collision_RO`, and the three
`*_resistant_if_indifferentiable`): `[Countable f_in]` and the three disjointness instances of
`SRO_Bounder_bounder`, `SRO_Counter_c`, `SRO_RO_m`; the preimage lemmas also
`[Lens.Disjoint SRO_RO_m DPre_h]` (resp. `D2Pre_m2`), since `DPre.h` is read right after
`RO.init` writes `RO.m`.  `SecureRO.RO_is_collision_resistant` and `RO_is_preimage_resistant`
(EC's `fel` over the adversary) take `[Countable «from»]` and the disjointness of
`Bounder_bounder`, `Counter_c`, `RO_m`.  `RO_is_second_preimage_resistant` also uses `FullEager.RO_LRO_D`
(below): `[Countable «to»]`, `[Lens.Disjoint RO_m FRO_m]`, and `Bounder_bounder`, `Counter_c`
disjoint from `FRO_m` (`D1(A)` touches them and must stay outside `RO.m`, `FRO.m`); so does
`second_preimage_resistant_if_indifferentiable` for `SRO`.
`SecureORO`'s three lemmas (proven 2026-11-02) likewise take `[Countable «from»]` and
`[Lens.Disjoint Bounder_bounder RO_m]` (no `Counter` there); `RO_is_second_preimage_resistant` also
`[Countable «to»]`, `[Lens.Disjoint RO_m FRO_m]`, `[Lens.Disjoint Bounder_bounder FRO_m]`
(`RO_LRO_D (D1(A))`).
`Sponge`'s `Exper_HybridIROLazy_LRO` (resp. `Exper_RO_HybridIROEager`) takes
`[Lens.Disjoint HybridIROLazy_mp ERO_RO_m]` (resp. `[Lens.Disjoint ERO_RO_m HybridIROEager_mp]`):
the invariant `HybridIROLazy.mp{1} = ERO.RO.m{2}` relates two oracle states, read as one lens.  The
argument type `block list * int` is countable outright (`block` is finite).
`PROM.FullRO.RO_FRO_D`, `FullEager.LRO_RRO_D` and `FullEager.RO_LRO_D` take
`[Countable in_t] [Countable out_t]` (the arguments of `get` and `set`) and
`[Lens.Disjoint RO_m FRO_m]`; `FullEager.eager_D` and `Eager_1_2` take the countability.  So
`Sponge.HybridIRO.LRO_RO` takes `[Lens.Disjoint ERO_RO_m ERO_FRO_m]`, which
`HybridIROExper_Lazy_Eager'` discharges by choosing `ERO_FRO_m` fresh for `ERO_RO_m` as well.
`Lib/EC/Strong_RP_RF` (2026-11-02): the abstract calls of `D` (`pr_PRPi_PRPi'_Indirect`,
`PRPi'_Indirect_eq`, `pr_PRPi'_Indirect_ARP`, `pr_PRFi_collision`) take `[Countable D]` and the
disjointness of the module variables they read as one lens: `PRPi.m`, `PRPi.mi`,
`PRP_indirect_bad.bad`, `ARP.m`, `ARP.mi`, `ARP.coll`, `DBounder.FBounder.c` (all pairs, as
instances); `Conclusion` and `PartialConclusion` the same for the theory's variables, plus their
finite support (E6, to choose `PRP_indirect_bad.bad` fresh).

**EasyCrypt counterpart.** None needed.  EasyCrypt's distributions are discrete, which the rule's
countability stands in for, and distinct module variables are distinct memory locations.  A clone
that instantiates the lens parameters with `global_var`s discharges the disjointness by instance
search; the SHA-3 instance of `f_in` is `List Bool`, countable.

## E9: IterProc's permutation lemmas are denotational equalities

**Rule broken.** A Lean statement is EasyCrypt's statement.

**What EasyCrypt states.** `iter_cat`, `iter_perm`, `iter1_perm` (theory `IterProc`) are `equiv`s
between iterations over related lists, with `={glob O}` before and after, under `iter2_eq`
(`equiv[Iter(O).iter_12 ~ Iter(O).iter_21 : ={glob O, t1, t2} ==> ={glob O}]`).

**What we state.** Equalities of denotations (`Lib/EC/IterProc.lean`): e.g. `iter_perm` says
`procedureDenotation (Iter(O).iter) l₁ = procedureDenotation (Iter(O).iter) l₂` for `l₁ ~ l₂`, if two
calls of `O.f` commute denotationally.  EC's `Iter(O).iters` and `Iter(O).iter_1s` are spelled as the
composite denotations they stand for.  `iter_ll` and `iter_inv` are as in EasyCrypt.

**Why.** `={glob O}` for an arbitrary `O` needs a frame for `O`'s footprint (E7), while the
denotational form holds for every `O` with no hypothesis on it, is strictly stronger (it gives
EC's `equiv` under any relation), and is used by rewriting the iteration inside a judgment, where
EC uses `call (iter1_perm …)` or `transitivity`.  The proofs go through one characterization,
`Iter.iter_denotation` (the iteration is the calls of `O.f` in order).

## E10: PROM's eager lemmas are stated at equality invariants

**Rule broken.** A Lean statement is EasyCrypt's statement.

**What EasyCrypt states.** `eager_init` … `eager_allKnown` and `eager_D` (`PROM.FullEager`) are
`eager` judgments with partial-equality invariants, e.g.
`eager [RRO.resample();, FRO.get ~ RRO.get, RRO.resample(); : ={x, FRO.m} ==> ={res, FRO.m}]` and
`eager [RRO.resample();, D(FRO).distinguish ~ D(RRO).distinguish, RRO.resample(); :
={glob D, FRO.m, arg} ==> ={FRO.m, glob D} /\ ={res}]`.

**What we state.** The same judgments (`ProgramDenotation.eagerR`, with the block
`RRO.resampleDen`) at equality of the whole global state before and after, for equal arguments.
For the oracle procedures, which touch only `FRO.m`, this says the same as EasyCrypt's.

**Why.** The eager calculus composes equality-invariant judgments (`eagerR_seq`, `eager_call`,
`eager_call_module`): EasyCrypt's `eager proc` rule is `eager_call_module`, which needs no `={…}`
of the adversary since its steps swap with the block by footprint disjointness.  EasyCrypt's form
with an invariant follows by a self-coupling of one composite
(`ProgramDenotation.eagerR_of_self_right`), where a use needs it.

## E11: the up-to-bad abstract call rule asks the adversary lossless with both oracles

**Rule broken.** A Gaudí rule has EasyCrypt's premises.

**What EasyCrypt asks.** `call (: bad, invP, invQ)` on an abstract procedure (`equivF_abs_upto`,
`src/phl/ecPhlFun.ml`) asks: `A` lossless whenever its oracles are (`islossless`, from `D_ll`);
per oracle, the equivalence up to `bad`; the left oracle lossless and keeping `invQ` once `bad{2}`
holds (`phoare … = 1`); the right one lossless and keeping `bad /\ invQ`.

**What we ask.** `prhlProc_abstract_call_upto(_module)` (`Logic/AbstractCallUpto.lean`) asks `A`
lossless with each of the two given oracle instantiations, and the per-oracle `invQ`/`bad`
preservation as Hoare triples (`hoareProc`, no losslessness).  A caller derives the first from
`D_ll` with the two oracle modules, which needs them lossless everywhere, not only after `bad`.

**Why.** The coupling after `bad` is independent, so both remaining runs must be lossless.  The
Gaudí proof gets that from the losslessness of the whole run (`LosslessAt.of_bind`: almost every
intermediate state then has a lossless remainder).  EasyCrypt's weaker premise needs an argument
over every oracle behaviour (`A` lossless for *all* lossless oracles, applied to oracles that
replay the run's history), which the Gaudí rule does not formalize.  The oracles of the SHA-3 uses
(`SLCommon.Pr_restr`, `Handle.eca`) are lossless everywhere, so nothing is lost there.

## E12: `bypr` is replaced by equivalences through an auxiliary module

**EasyCrypt.** `BlockGen_loop_direct` (`Sponge.ec`) is proven by `bypr res{1} res{2}`: two
procedures with no shared state are equivalent on `={res}` when every `Pr[_ : res = w]` agrees.

**Gaudí.** There is no `bypr` rule (it needs a coupling built from equal result marginals, i.e.
conditional distributions of the globals).  The statement is unchanged; the proof composes two
equivalences through an auxiliary module `BlockGenCall` (`BlockGen.loop` with its loop the call
`Prog.LoopSnoc.sample(r)`, not in EasyCrypt): EC's own `byequiv` step (the loops in lockstep), and
a sampling against the call (`prhlStmt_seq_sample_run_map_right`), from the same facts EC uses as
probabilities (`LoopSnoc.sample_denotation`: the loop samples `dlist {0,1} r`; `bdistr_dlist`:
its image by `mkblock` is `bdistr`).

The same pattern for EC's `transitivity{2}` through code blocks in
`HybridIROEagerTrans_BlockSpongeTrans_next_block` (`{ w <@ BlockGen.loop(); }`, then
`{ w <@ BlockGen.direct(); }`): auxiliary modules `NextBlockSplitLoop`/`NextBlockSplitDirect`
(`next_block_split` with its loop of bits replaced by those calls), each step an equivalence of
procedures, composed by `prhlProc.trans`.  EC's ghosts (`exists* i{1}, bs{1}`) are read from the
other side, which keeps them; EC's `exists* HybridIROEager.mp{1}` (the map before the writes) is
folded into the invariant as the statement it is used for (`∀ mq, eager_eq_except … → … →
eager_invar … mq`).

## E13: `Gconcl`'s `Gext0` variables are fresh for `D` by hypothesis (`Gext0Fresh`)

**Rule broken.** A Lean statement has the EasyCrypt statement's hypotheses, no more (as E6).

**Why.** `Gconcl.ec` declares `D <: DISTINGUISHER {-C, -Perm, -F.RO, -F.FRO, -S, -Redo}` and then
`local clone import Gext as Gext0`.  The clone copies `Gext` and, through its `clone export`s,
`Gcol`, `Handle`, `ConcreteF` and `ROhandle`, so `G1`, `PF`, `ROhandle.FRO`, `ROhandle.RO` are new
modules that `D` cannot touch.  The local games `G3`, `G4` and `Gext`'s `Real_G2` rely on it: their
oracles read and write `G1.m`, `G1.mh`, `FRO.m` … around `D`'s call.  In Lean those theories were
ported as plain theories: their module variables are fixed `global_var`s (`G1.m`, `PF.m`,
`ROhandle.FRO.m` …), not lens parameters, so the E6 remedy (lens parameters, chosen fresh with
`Footprint.exists_fresh` in the non-local result) is not available without making `Handle`,
`Gcol`, `Gext` and `ConcreteF` generic over their variables.

**What we do instead.** `Gconcl.Gext0Fresh D` (`D` outside `PF.m`, `PF.mi`, `G1.m`, `G1.mi`, `G1.mh`,
`G1.mhi`, `G1.chandle`, `G1.paths`, `G1.bext`, `G1.bcol`, `FRO.m`, `ROhandle.RO.m`) is a hypothesis of
the local lemmas `G2_G3`, `G3_G4`, `G4_Ideal` (as E6 allows) and of the non-local `Real_Ideal`.  With
`DRestrictions D` it gives `Real_G2`'s restriction.

**Consequences.** `Gconcl_list` uses `Real_Ideal` (for `A(D)`), so its results need `Gext0Fresh`
for the distinguisher it builds, and so on up to `SHA3Indiff`'s final theorem: the adversary must not
touch these proof-internal variables.  To be propagated when those proofs are done.

**How to remove it.** Make the variables of `Handle`, `Gcol`, `Gext` (and `ConcreteF`'s `PF`) lens
parameters, as `Sponge`'s `HybridIRO` section does (E6), and pick them fresh in `Real_Ideal` with
`Footprint.exists_fresh` (under finite support of `D`, which `Module.ECModule` provides).
