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
* in `Sponge`'s last section, `HIRO`'s `HIRO_Lazy_mp`, `HIRO_Eager_mp` (`HIRO_fresh`).
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
* `Gext`: `ReSample.count` (`ReSample_count`; `RROset_inv_lt`, `Pr_ext`, `EG2_Gext`);
* `Gconcl_list`: the clone `IRO2` (`IRO2_RO_m`; `equal1`, `equal2`);
* `Sponge`, `SecureRO`, `SecureORO`, `SHA3OSecurity`: as listed above.

The other local clones have no module variables (`ConcreteF`'s `ProdSampling`), or clone a theory
whose own local modules do not survive the clone (`Gconcl`'s `Gext0`).


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
`RO.init` writes `RO.m`.  `SecureRO.RO_is_collision_resistant` (EC's `fel` over the adversary)
takes `[Countable «from»]` and the disjointness of `Bounder_bounder`, `Counter_c`, `RO_m`.
`Sponge`'s `Exper_HybridIROLazy_LRO` (resp. `Exper_RO_HybridIROEager`) takes
`[Lens.Disjoint HybridIROLazy_mp ERO_RO_m]` (resp. `[Lens.Disjoint ERO_RO_m HybridIROEager_mp]`):
the invariant `HybridIROLazy.mp{1} = ERO.RO.m{2}` relates two oracle states, read as one lens.  The
argument type `block list * int` is countable outright (`block` is finite).
`PROM.FullRO.RO_FRO_D` and `FullEager.LRO_RRO_D` take `[Countable in_t] [Countable out_t]` (the
arguments of `get` and `set`) and `[Lens.Disjoint RO_m FRO_m]`.

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
