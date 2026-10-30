# Porting the EasyCrypt SHA-3 development

Source: <https://gitlab.com/easycrypt/sha3> at `4315ef7` (2026-05-07). It accompanies "Machine-Checked
Proofs for Cryptographic Standards: Indifferentiability of Sponge and Secure High-Assurance
Implementations of SHA-3" (CCS 2019).

**Scope**: the EasyCrypt security proofs only, that is `proof/` and `proof/smart_counter/`
(21 files, ~17k lines, 428 lemmas/equivs).  The following are out of scope:

* `proof/impl/`: the Jasmin implementations and their correctness and constant-time proofs;
* `utils/DomainSeparation.eca`: nothing requires it, and the repository's own test configuration
  does not check it.

**The rule**: the port preserves the structure of the EasyCrypt development.  Every EasyCrypt
statement has a Gaudí counterpart that can be found mechanically, and every unavoidable
deviation is recorded in `Exceptions.md`.

Files in this directory:

* `Mapping.md`: one row per EasyCrypt declaration, giving its Lean name and status.  It is
  generated, and the statuses are maintained by hand.
* `Dependencies.md`: the files in dependency order, and the EasyCrypt library theories they use.
* `Exceptions.md`: the deviations, each with its reason.
* `Tooling.md`: the logic and tactic extensions made for the port.

## Conventions

* **Files.** One Lean file per EasyCrypt file, with the same base name:
  * `proof/X.ec` and `proof/X.eca` go to `GaudisCrypt/Examples/SHA3/X.lean`;
  * `proof/smart_counter/X.ec*` goes to `GaudisCrypt/Examples/SHA3/SmartCounter/X.lean`.

  Declarations keep the EasyCrypt file order.
* **Names.** Every EasyCrypt `lemma`, `equiv`, `module`, `module type`, `op`, `pred`, `type` and
  `axiom` keeps its EasyCrypt name verbatim.  It lives in namespace `GaudisCrypt.SHA3.<File>`,
  plus `.<Theory>` when it is inside an EasyCrypt `theory`.  This deviates from the
  project's naming convention (exception E1).
* **Statements.** These must map exactly:
  * the same games, written with the same procedures, statements and order;
  * the same hypotheses (EasyCrypt `declare axiom`s become hypotheses);
  * the same bound.

  An `equiv` becomes a theorem stated as `equiv[ … ]`, an `hoare` becomes `hoare[ … ]`, a
  `phoare` becomes `phoare[ … ]`, and a `Pr[…]` lemma becomes a statement about
  `Procedure.Pr`.
* **Proofs.** The structure should match as far as possible: the same `seq` cut points and
  intermediate relations, the same `while` and `call` invariants, and the same `swap`s,
  `rnd` bijections and case splits.  The tactic sequence may differ.  The `smt`, `auto` and
  `algebra` leaves are free: we prove them in Lean however we like.
* **Theories.**
  * An abstract theory (`.eca`) becomes a Lean `section` whose `variable`s are the theory's
    abstract `type`s, `op`s and `axiom`s.
  * `clone T as U with …` becomes the instantiation of those variables, under the name `U`.
* **Sections.**
  * `declare module A <: T {-M₁, …}` becomes a `variable (A : …)`.  The memory restriction
    `{-M₁, …}` becomes a footprint-disjointness hypothesis.
  * `declare axiom` becomes a hypothesis `variable`.
  * `local` declarations stay ordinary declarations, keeping their EasyCrypt names.

## Plan

0. **Inventory**: `Mapping.md` and `Dependencies.md`.  Done 2026-10-30.
   * **Ground truth.** EasyCrypt r2026.09-1-g311ba5d (opam switch `ec`, with Alt-Ergo 2.6.3, CVC4
     1.8 and Z3 4.12.6) checks 20 of the 21 files (`easycrypt runtest config/tests.config sponge`,
     about 1.5 minutes with 4 jobs).  `smart_counter/ConcreteF.eca` stops at line 418 with an
     EasyCrypt anomaly (`InvalidGoalShape`) inside a `sim`.  The authors left a FIXME there about
     an ill-formed term.
1. **Logic prerequisites.**  Each is tested on a toy before SHA-3 uses it.
   * **Distinguishers with oracle access**: EasyCrypt's `module type DISTINGUISHER (F : …, P : …)`
     and `Indif(F, P, D)`.  Module parameters of functor type already exist
     (`A : Module.Arr T (procmod …)`, `ModuleSyntaxTest.lean`), and so does a functor of three
     module parameters (`Deep` there).  Not yet tried:
     * a parameter applied to other parameters (`D(F, P)` inside `Indif`);
     * the Schnorr failure: three module parameters of module types that take a Lean parameter
       (`SigmaScheme P`), where the `module` command's well-typedness proof does not close.
   * **Abstract call rule**: EasyCrypt's `call (: inv)` for an abstract adversary run against two
     different oracle sets.  **Done 2026-10-31** (`Logic/AbstractCall.lean`, see `Tooling.md`),
     for adversaries given as procedures with holes (exception E2).  Still missing: the unary
     (`hoare`) version, the up-to-bad version, and the representation lemma that would remove E2.
   * **Up-to-bad**: `call (: bad, inv, inv')`, `byequiv : bad`, and `fel` (EasyCrypt's failure
     event lemma; used 8 times, in `Gcol` and `Gext` via `FelTactic`).
   * **Smaller tactics**:
     * `rcondt` and a general `rcondf`, for a loop or `if` at any position (531 uses);
     * `sim`, which relates two copies of the same code (308 uses);
     * `conseq` forms;
     * `transitivity`, `islossless`, `exlim`.
2. **Skeleton**: every definition ported and every lemma stated with `sorry`, in dependency
   order, so that the headline statements exist early.
3. **Proofs**, from the leaves up: first the short reductions in `SHA3Security` and
   `IndifRO_is_secure`, then `Sponge` and `BlockSponge`, and the `smart_counter` chain last
   (`Handle.eca` is the largest single piece).

### EasyCrypt library theories needed

Lean counterparts are needed for these EasyCrypt library theories:

| Theory | Size | What the development uses from it |
|---|---|---|
| `PROM.FullRO` | 1045 lines | `RO`, `FRO`, `LRO`, `FullEager.RO_LRO_D`, `eager_*` (cloned 7 times) |
| `Strong_RP_RF` | 576 lines | the PRP/PRF switching lemma (`ConcreteF`) |
| `PRP` | 729 lines | |
| `FelTactic` | | `fel` |
| `Mu_mem` | | |
| `Dexcepted` | | |
| `DList`, `DProd`, `DBool` | | distributions |
| `BitWord`, `BitEncoding` | | blocks, capacities, bit lists (`Common`) |
| `FMap`, `FSet`, `SmtMap` | | finite maps and finite sets |
| `AdvAbsVal` | | |

`Lib/RO/FullEager.lean` already has a PROM-style lazy = eager proof.  It is built on the
`prhl2` and footprint layer, not on statements and modules.
