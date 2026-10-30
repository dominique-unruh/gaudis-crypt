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
