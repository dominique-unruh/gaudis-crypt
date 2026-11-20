# What `clone` needs to change

Design note, 2026-11-20.  For Denis and Dominique.  Problem statement and a proposal; nothing is
built yet.

## Summary

Two limits of `clone` (`GaudisCrypt/Syntax/Clone.lean`) block what is left of the SHA-3 port's
alignment with EasyCrypt:

1. **Two clones of one theory at different types cannot be used in one file**: whatever finds
   the theory's instance by search finds the latest clone's.
2. **Two clones of one theory share its module variables**, where EasyCrypt gives each clone
   its own.

Both come from one design choice: use sites find a clone's operators and variables through the
theory's instance (`[T.Params …]`), by instance search.  The proposal keeps that choice inside
the theory and removes it outside: **the clone generates, at its own instance, everything a use
site needs**, and a theory's module variables take their slot name from the instance.
No change to how a theory is written, and none in `Language/`.

## How `clone` works today

A theory `T` is a namespace whose declarations take the theory's types as implicit section
variables and its operators and axioms as one instance `[T.Params τ₁ … τₙ]`.  The types are
`outParam`s, so that inside the theory a declaration used alone (`RO.m`, `§RO.m`) gets its types
from the instance.  `clone T as C with type a <- τ, op o <- e` makes:

* the instance `C.params : T.Params τ…`;
* for every definition and theorem `T.x` an alias `C.x`, `T.x` at the clone's types and
  instance.  Inductive types and structures are skipped: an alias of a structure would lose its
  constructor notation.

A module variable of a theory (`module_var RO.m : FMap «from» «to»`, `Syntax/ModuleVar.lean`) is
the slot `⟨"T.RO.m", FMap «from» «to»⟩`.  Its name is a literal fixed when `T` is elaborated.

## Problem 1: instance search across clones

Lean erases `outParam`s before instance search.  A search for `T.Params ?a ?b` therefore returns
the most recent instance, whatever the types the use site needs.  Where two clones of `T` at
different types are in scope, every step that searches fails at the earlier clone's types:

* **Record notation for a module type's constructor.**  `T.FUNCTIONALITY.mk { f := … }` searches
  for the instance.  The clone has no `C.FUNCTIONALITY.mk`, because structures are skipped.
* **The subtyping coercions.**  `module_subtype OPRIMITIVE <: ODPRIMITIVE`, stated in the
  theory, is a `Coe` instance over `[T.Params …]`.
* **A theory lemma used without its clone's alias.**

Where it bites:

* `Gconcl_list` has SLCommon's and BlockSponge's clones of `Indifferentiability`.  EasyCrypt has
  the same two clones there.
* `SHA3OSecurity` would have two clones of `OptionIndifferentiability`: SHA3_OIndiff's
  `OIndif` at `state, List Bool × ℤ, List Bool`, and `SH.OIndif` through the `SecureHash` clone,
  at `state, List Bool, f_out`.

Tried on 2026-11-18 (branch `wip/module-types-as-clones`, `cb41dd7`, does not build): SLCommon
through Gconcl and BlockSponge build; Gconcl_list and Sponge fail.

* `semiOutParam`: the theory's own definitions get stuck.
* A universal instance for a field-less `Params`: Lean refuses instances with open out-params.

What it blocks: the first port's `Indifferentiability` and `OptionIndifferentiability` (their
module types with explicit type parameters, the `view`s, `GReal`, `GIdeal`) stay.  So do the
abbreviation blocks that stand for EasyCrypt's `clone … with type p <- …` in SLCommon,
BlockSponge, Sponge, SHA3Security, SHA3_OIndiff and SHA3OSecurity.  Because a clone's
projections do not reduce on the first port's records, these remain too:

* the bridge lemmas `ODPRIMITIVE_f_mk`, `ODPRIMITIVE_fi_mk`, `OPRIMITIVE_coe_eq`, `OSponge_app`,
  `PSome_Perm_init`, `CSetSize_Sponge_Perm_*`, `SimSetSize_init_eq`;
* SHA3OSecurity's GAP 3 (`simp only [ODPRIMITIVE_f_mk]` before `proc`) and GAP 6.

## Problem 2: module variables per clone

`module_var` names the slot after the theory, so `C₁.RO.m` and `C₂.RO.m` are the same slot when
`C₁` and `C₂` clone `T` at the same types.  EasyCrypt gives each clone its own variable.

Where it bites:

* Gconcl_list clones `IRO` as `BIRO` (with `valid_block`) and `BIRO2` (with `predT`) at the
  same types, and uses both in one game.
* The same holds for `F` and `F2`, two clones of `PROM.FullRO`.

So these clones still use the first port's `IRO`, a module whose map is a lens parameter.  Each
clone declares its own `global_var` and passes it in.  The port's own `IRO`, with `module_var`s,
has no user.

The same mechanism makes a second limit of `clone`: two clones of one theory at the same types
with different operators are not supported (EasyCrypt's `SRO` and a second `SRO'`).  The use
site's search cannot tell them apart.

## Proposal

### Change 1: the clone makes what use sites search for

Inside the theory nothing changes: there the only instance is the section variable, and the
search is right.  Outside, `clone` generates at `C.params` what a use site would otherwise look
up by search:

1. **Constructors.**  For every module type `T.X` of the theory, an alias `C.X.mk` (`T.X.mk` at
   the clone's types and `C.params`).  It is a definition, so record notation works on its
   argument (`C.FUNCTIONALITY.mk { f := … }`), with no search.
2. **Subtyping.**  For every `module_subtype S <: U` of the theory, the clone's instance
   `Coe C.S C.U` (the same function, at `C.params`), at a higher priority than the theory's.
   `module_subtype` records its pairs per theory (a registry like `Syntax/CloneRegistry.lean`,
   which records the clones themselves) so that the clone can repeat them.  Search for a coercion then unifies with the
   clone's concrete instance and finds the clone's own coercion.
3. **Theory lemmas.**  Used through the clone's aliases only.  This is already the rule.  A
   linter could flag `T.x` used at a clone's types.

This is all inside `Syntax/Clone.lean` and `Syntax/ModuleSubtype.lean`.  It also fixes the case
of two clones at the same types with different operators: nothing at a use site looks the clone
up by its types any more.

### Change 2: module variables named after the clone

`T.Params` gets one more field, the clone's name: `cloneName : String`.  The clone sets it to
`"C"`.  `module_var RO.m` names its slot `cloneName ++ ".RO.m"` instead of the literal
`"T.RO.m"`, so the variable is per clone:

* **Inside the theory**, nothing changes: `RO.m` is still `RO.m` at the section's instance.  The
  theory's proofs, which speak about `RO.m` through hypotheses (`declare module` restrictions,
  `glob`), are generic in the name.
* **At the clone**, the name is a literal again (`"C.RO.m"`).  The clone generates for each
  module variable the key theorem (`C.RO.m.key_eq`) and the `Lens.IsGlobalVar` instance that
  `module_var` makes today.  Disjointness from other globals and from the other clone's
  variables is then found by instance search on the literal keys, as for any `global_var`.

This touches `Syntax/ModuleVar.lean` and `Syntax/Clone.lean`.  It uses `Language`'s
`VariableName.mk` with a computed name inside the theory, so it is a question for Dominique
whether that is acceptable there: the key proof is generic, `k = encode n`, and becomes a literal
at the clone.

### What the two changes unlock in SHA-3

* **Change 1:** the six abbreviation blocks become one `clone … with type p <- …` line each.
  The first port's `Indifferentiability` and `OptionIndifferentiability` (about 130 lines) go,
  with the `view`s, the bridge lemmas listed above, GAP 3 and GAP 6.
* **Change 2:** `BIRO`, `BIRO2` and Sponge's `BIRO` become clones of the port's `IRO`, and so do
  `F`, `F2` of `PROM.FullRO`.  The first port's `IRO` (its lens parameter `mp`) goes.

Both together are most of what the first-port sections still hold besides EasyCrypt's own
lemmas.

## Plan

1. **Golden test (`Syntax/CloneTest.lean`):** a theory with two module types, a
   `module_subtype` and a `module_var`, cloned twice in one file at different types, and twice
   at the same types with different operators.  Check record notation, the coercions, aliased
   lemmas, and that the two clones' variables are disjoint.
2. **Change 1,** then the first real case: SHA3_OIndiff's `OIndif` as a clone, next to
   SHA3OSecurity's `SH`.
3. **Change 2,** then `BIRO` and `BIRO2`.
4. One full build per step.  Then the other abbreviation blocks, file by file.

## Questions for Dominique

* Is a clone-level `Coe` instance at a higher priority than the theory's the right way to give
  subtyping per clone, or should `module_subtype` stop being an instance in theories?
* Change 2: a slot name computed from the theory's instance (literal only at the clone).  Is
  that acceptable for `VariableName`, or should the clone instead re-declare the variables and
  substitute them in its aliases?  The second avoids the computed name but needs every theory
  declaration to take its module variables as parameters.
