# Hoare tactics: issues found on `HidingExperiment` (2026-10-21)

All five are addressed on branch `hoare-call-rule`; each section ends with what was done.

Found while driving `HidingExperiment(Pedersen, U).main` with the new `hoare[…]` tactics
(`hoare_proc_to_stmt`, `hoare_inline`, `hoare_wp`, `hoare_skip`).  Test case:
`GaudisCrypt/Examples/Pedersen/HidingHoare.lean` (`hiding_diverges_of_guess_diverges`).

Context: `hoareStmt`/`hoareProc` is partial correctness ("¬B has mass 0"), so it cannot state
hiding itself (`Pr = 1/2`); the experiment proves a smaller triple that still needs Pedersen's
algebra (`commit_shift`).

## 1. No rule for a call to an abstract procedure

`hoareWpFull` has rules for assignment, sampling, resets, `skip` and sequencing only, so
`hoare_wp` stops at the adversary calls `U.choose`/`U.guess`.  Needed: EC's
`call (_ : P ==> Q)` — given `hoareProc P p Q`, the precondition of `x <- call p (args)` w.r.t.
`B` is `P args ∧ ∀ r g, Q r g → B[x := r, globals := g]`.  Also the trivial triple
`hoareProc (fun _ _ => True) p (fun _ _ => True)`, for calls whose spec does not matter.

**Done.** `hoare_call_wp` and `hoareProc_true` in `Logic/Hoare.lean`; the tactic `hoare_call h`
(`hoareCallStep`) in `Logic/HoareWp.lean` closes a trailing call with the triple `h` and
simplifies the new postcondition like `hoare_wp`.  Bare `hoare_call` uses `hoareProc_true`.

## 2. `simpReads` does not read a local through a write to the globals

A call writes the globals (`ProgramState.globalL.set g σ`), and a later read of a local, e.g.
`(localVarLens "x" G).get (ProgramState.globalL.set g …)`, stays stuck: `Lens.get_of_disjoint_set`
needs `Lens.Disjoint ProgramState.globalL x.intoLocal`, and there is no such instance (only
`globalL`/`localL` and `intoLocal`/`intoGlobal`).

**Done.** Instances `Lens.disjoint_globalL_intoLocal`/`Lens.disjoint_intoLocal_globalL` in
`Language/Variables.lean`.

## 3. Clutter left in conditions

`simpReads` leaves `Lens.id.get e` (single-argument getters) and `∀ r g, True` (from the trivial
part of a call's precondition) in place.

**Done.** `simpReadsDecls` gains `Lens.id_get`/`Lens.ofst_get`/`Lens.osnd_get` (new, in
`Language/Lens.lean`) and `implies_true`, `true_implies`, `and_true`, `true_and`.

## 4. Variables printed as raw lenses after a call

After `hoare_call`, a variable still used by the program (here `x`) dropped out of the `var`
list and printed as `(localVarLens "x" group.G)`.

**Cause.** The postcondition still held `eval (Getter.mk fun x => (localVarLens "c" _).get x)`
(the call's argument getter, read at the current state); the binder `x` there made
`nameClashes` refuse to print the program variable `x` under its name.
**Done.** `simpReadsDecls` gains `eval_getter_full`, which reduces that read away.

## 5. An `abbrev` around a module blocks `hoare_inline`

`hoare[ (hidingGame group U) : … ]` with `hidingGame` an `abbrev` for the module fails with
"no concrete procedure body: nothing to unfold at the head of hidingGame group U";
`moduleStep?` never unfolds a definition unless its value is a `T.mk` record.

**Done.** `moduleStep?` (`Logic/Inline.lean`) gets a step (6): a reducible head constant is
unfolded.  Module combinators are not reducible, so they are unaffected.

(Not a bug, but easy to trip over: a module with two `using` parameters takes a *pair*,
`Module.app (HidingExperiment types) (Module.pair S U)`, not two curried applications.)

## 6. No rules for `if`, `while`, or framing an abstract call (second round)

Found while proving `game_query_count` (`GaudisCrypt/Examples/QueryCounting.lean`): an abstract
adversary and a counting oracle in a `q`-round loop, with the EC-style claim
`hoare[ Game(A, O).main : q = n ==> count = n ]` for any `A` that does not touch `count`.

**Done.**
* `hoare_if_wp`, `hoare_while` (invariant rule, from `wp_while_invariant`) in `Logic/Hoare.lean`;
  `hoare_wp` now goes through conditionals (`hoareWpClose`, `Logic/TacticMisc.lean`).
* Tactic `hoare_while I` (`Logic/HoareWp.lean`): `I` is written like a triple's condition, `§x`
  for the program's variables; goals `body`, `exit` (reads generalized), then the code before.
* `Logic/HoareFrame.lean`: `hoareProc_frame` and `hoare_call_frame` — EC's `A <: Adv {-L}` as a
  footprint hypothesis `inFootprint (L.footprint)ᶜ`, via
  `ProgramDenotation.wp_zero_of_lens_preserves_footprint`.  `hoare_call` now also takes such a
  statement-level rule: `hoare_call (hoare_call_frame count hA)`.

## 7. Global reads in conditions got stuck (second round)

A global read in a condition is `eval g` with the state in `eval`'s *instance* argument `cs`,
where `simp` does not rewrite; after an inline and a few wp steps it sat under the renaming
lenses and a chain of writes, and `generalizeReads` then cut it off from the invariant's reads
(the `exit` goal became unprovable as stated).

**Done.**  `simpReads` takes global reads out of `eval` (`eval_lens_global`,
`eval_getter_global`) and pushes `.globals` through writes (`globals_intoLocal_set`,
`globals_intoGlobal_set`, `globals_resetSetter_set`, `globals_globalL_set`, `globals_chain_get`,
`globals_trafo_get`/`_emb_get`/`_rename_get`).  The inliner's cleaning pass reads a global at a
state seen through a composite lens (`eval_chain_state_global_lens`/`_getter`).

Remaining rough edges: procedure triples bind parameters in the precondition only (as in EC), so
a postcondition about an argument needs a logical variable (`$q = n ==> $count = n`); a
`while` test prints as `decide (§i < §q)`.
