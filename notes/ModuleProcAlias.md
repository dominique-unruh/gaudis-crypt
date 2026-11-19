# Procedure aliases in `module` (`proc f = c;`)

Design note, 2026-11-19.  For Denis and Dominique (the `module` command's author).

## What EasyCrypt has

```
module Valid2 (F : RO) = {
  proc init = F.init
  proc f (x) = { … }
}
module D2 (D : DISTINGUISHER) (F : RO) = {
  proc distinguish = D(FC(DSqueeze(Valid2(F))), PC(S(Valid2(F)))).distinguish
}
```

`proc f = c` makes `f` *the very procedure* `c`, not a procedure that calls it.  The
`module` command could not say this, so the port wrapped every alias in a call
(`proc f (x) { r <- call c (x); return r }`, exception E5 in `notes/SHA3/Exceptions.md`), or
built the module as a Lean definition with `T.mk` (`Valid2`, `IF'`, `PRestr`, …).  The wrappers
are an extra call in every proof that meets them (inline, then `sim`); the Lean definitions are not
modules, so `equiv_call`, `fp_module` and the `apply_simp` machinery don't see through them, and
proofs about them carry bridges.

## Syntax

One more form of procedure inside `module`, next to `proc f (…) : R { … };`:

```lean
module Valid2 using (F : RO_T) : RO_T {
  proc init = F.init;
  proc f (x : List block) : block { … };
}
module D2 (D : DISTINGUISHER) using (F : RO_T) {
  proc distinguish = D(FC(DSqueeze(Valid2(F))), PC(S(Valid2(F)))).distinguish;
}
```

The callee `c` is any procedure-valued module term over the module parameters, the same terms a
`call` accepts as callee.  The trailing `;` is required (a term cannot end where the next `proc`
begins otherwise).

## What it generates

For `proc f = c` with `c` mentioning the parameters `A₁ … Aₖ` (declaration order):

* `X.f : A₁'s type →ₘ … →ₘ procmod (…) → R`, the module expression of `c` abstracted over
  `A₁ … Aₖ` (`toModule (.abs … (.abs ⟦c⟧))`, the same reading of a callee that holes already
  use).  With `k = 0`, `X.f := c` itself.
* `@[simp] X.f.apply_simp : Module.app (… (Module.app X.f A₁) …) Aₖ = c`, so after `simp` the
  alias **is** `c`: no `X.f.procedure`, no instantiation, no extra call.
* `@[gaudiModuleAlias]` on `X.f`: it marks `X.f` as a procedure of a `module`. The tools that
  recognised one by its `X.f.procedure` (the footprint solver, `M(A).f` paths, parameter-name
  lookup for notation) ask `isModuleProc` instead.
* `@[gaudiProcParamNames]` on `X.f`, copied from `c`'s head when it records them (an accessor
  `F.init`, say).

`X` itself, `X.apply_simp` and the record built with `T.mk` are unchanged: an alias is one more
field, so a module may mix aliases and ordinary procedures.

## What it is not

* Not a whole-module alias (`module S2 (F) = S(Last(F))`): that is `Module.comp`, or a Lean
  definition applying modules, as before.
* No new proof rule: the alias's `apply_simp` is proved by the same normalisation as an ordinary
  procedure's (unfold, `reduce_simp`, compare callees with `moduleCallee`).

## Limits

* A callee going through a Lean *definition* that builds a module (rather than a `module`), such as
  the first port's `Valid2 := FUNCTIONALITY.mk { init := F.init, f := Module.app Valid2.f_ F }`,
  is read through the definition when `X.f` is built, while the lemma's right-hand side names the
  definition.  The two are equal but not by the comparison `moduleCallee` does.  Holes already
  have this limit.  The command then fails with a message that says to declare the definition
  as a `module` (golden test `ThroughDef` in `ModuleSyntaxTest.lean`).  The fix is to make such
  definitions modules (with aliases, now possible) rather than to teach the proof to unfold.
  A definition that only rearranges the parameter's own fields goes through.

## `equiv_call` with a judgment about an alias

EC's `call (RO_LRO_D (D2(D)))` names the alias, while the program (after `inline*`) calls the
callee.  `equiv_call h` now rewrites the aliases in `h`'s type first (`PRHLWp.unfoldAliasesIn`:
the aliases' `X.f.apply_simp`, and for a module made of aliases only its `X.apply_simp` and the
accessors' `mk_simp`).  Golden test in `Logic/ECCallsTest.lean` (`Fw`, `FwT`).

## Checked on the real case (scratch, not committed)

In `Gconcl_list`: `module V2 using (F) { proc init = F.init; }` gives
`Module.app V2.init F = FullRO.RO_T.init … F`.  EC's `D2(D)(F)` with
`proc distinguish = D(FC(DSqueeze(Valid2(F))), PC(S(Valid2(F)))).distinguish;` (plus
`module_subtype SLCommon.PRIMITIVE <: DPRIMITIVE`) elaborates and states its lemma as EC's path.
The proof stops at the first port's `Valid2`, the limit above.

## Use

Removes exception E5 once the wrappers are converted (`SimLast`, `DValid`, `L`, `D2`, `D3`,
`FSome`, `RF`, `Bounder`, the SHA-3 sections' `FInit`/`PInit`/…).  It is also the first step of
porting `Gconcl_list`'s lazy/eager block in EasyCrypt's form, which then needs the first port's
`Valid2`/`IF'`/`L`/`L2`/`L4` as modules and PROM's `RO_Distinguisher` over any procedure signature.
