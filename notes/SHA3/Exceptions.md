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
