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
