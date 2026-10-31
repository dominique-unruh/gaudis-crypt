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

`hD` then disappears from every statement mechanically.  Neither route is done.

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
by `CSome`, so its `init` calls `F.init`.

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

The non-local results (`HybridIROExper_Lazy_Eager'`, `IdealIndif_IRO_BlockIRO`, `conclu`,
`conclusion`) have exactly EasyCrypt's hypotheses.  Their proofs need a **fresh-variable lemma**:
for a representable `D` (E2), whose code is finite, there is a lens of any type disjoint from
`FVP.fvP D` and from given finitely many variables.  Not yet proven; it is the same kind of fact as
the representation lemma of E2.

**Not yet applied to earlier files.** The skeletons of `ConcreteF` (`Switching`, a local clone of
`Strong_RP_RF`), `Gconcl_list` (`IRO2`, a local clone of `PROM.FullRO`) and other files with local
modules that have variables still use `global_var`s for them.  Their local lemmas either lack the
freshness hypothesis or carry it into non-local statements.  They must be brought to this
convention before their proofs: audit every `local clone` and `local module` with variables.

