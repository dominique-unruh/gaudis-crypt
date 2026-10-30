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

## E2: abstract adversaries are procedures with holes, not arbitrary functor modules (temporary)

**Rule broken.** EasyCrypt's `declare module D <: DISTINGUISHER` quantifies over every module of
the (functor) module type.  The Gaudí counterpart would be a variable
`D : Module.Arr (oracle types) (procmod …)`.

**What we do instead.** The port quantifies over a procedure with holes,
`D : ProcedureWithHoles holes sig`, one hole per oracle procedure the distinguisher may call.  It
enters games as the module `Module.procWithHoles D`.

**Why.** The abstract call rule (`Logic/AbstractCall.lean`, see `Tooling.md`) is proven by
induction over the adversary's code, so it needs that code.  For a module variable, the missing
step is a representation lemma: every functor module applied to oracles has the same denotation
as some procedure with holes instantiated with them.  It is module metatheory (`Language/`).

**How to remove it.** Prove the representation lemma; the statements then switch to module
variables.

**Affects** every `declare module` whose module type takes oracles: the distinguishers and
adversaries of `Indifferentiability`, `SecureRO`, `SecureORO`, `SecureHash`, `SHA3Security` and
`SHA3OSecurity`.
