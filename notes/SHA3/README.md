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

### Conventions found while porting (2026-10-31)

* **EasyCrypt standard library.** Counterparts live in `GaudisCrypt/Lib/EC/`, one file per
  EasyCrypt theory (`List`, `BitWord` with `BitChunking`, `FMap`, `FSet`, `Distr`, `PRP`).  They
  keep EasyCrypt's names and include only what the port uses.
  * `int` is `ℤ`.  The `int`-valued list operations (`size`, `nth`, `take`, `drop`, `nseq`, `index`,
    `find`, `mkseq`) are mirrored on `ℤ`, with EasyCrypt's behaviour on negative arguments.
  * `%/`, `%%` and `%|` are `/`, `%` and `∣`.  EasyCrypt's division is Euclidean, like Lean's on `ℤ`.
  * `fmap` is `Finmap`, with `FMap.get`/`set`/`dom`/`rng` for `m.[x]`, `m.[x <- y]`, `x \in m`,
    `rng m`.  `fset` is `Finset`.  `distr` is `SubProbability`.
* **Abstract constants.** An abstract `op` with an axiom, at file level, becomes a field of a
  parameter class: `op r : { int | 2 <= r } as ge2_r` is `Common.Params`.  An abstract theory's
  types and operators (`.eca`) are section variables instead, and a `clone` is an application.
* **Clones with renaming.** `clone BitWord as Block … rename "word" as "block"` becomes a namespace
  `Block` of abbreviations under the new names, exported where EasyCrypt exports.
* **Module types with parameters.** `module type X (P : T) = { … }` is the functor type
  `T →ₘ X'`.  The per-procedure call restrictions `{ P.f }` are expressed by the `ext` of a
  `Module.Representable` hypothesis (E2), where a theorem needs them.
* **Subtyping.** EasyCrypt passes a module where a smaller module type is expected (a
  `PRIMITIVE` as a `DPRIMITIVE`).  Here the smaller view is built explicitly
  (`PRIMITIVE.view`, or `DPRIMITIVE.mk … { f := …, fi := … }` inside a call).
* **Modules with more procedures than their type.** EasyCrypt allows this (`module IRO : IRO`
  with an extra `fill_in`); `module X : T` does not.  Such modules are declared without the type,
  and a `T`-view is built where one is needed.
* **Module aliases.** `module GReal(C, P) = Indif(C(P), P)` is a definition applying `Indif`.
* **Module variables.** `var m` of module `M` is `global_var M.m`.  In a generic theory
  (`.eca`) the module's variables are lens parameters of the module (`PRP.RP.RP D dD m mi`), and
  each clone declares its own `global_var`s under EasyCrypt's names (`Perm.m`, `F.RO.m`) and passes
  them.  This is EasyCrypt's semantics, in which a clone copies the module variables.  Reads whose
  type is not determined by the context are annotated (`($G1.mh : hsmap)`).
* **Calls between procedures of the same module** are `call (M.g <Lean parameters>)`.
* **Keywords.** `to`, `from` and `prefix` are keywords, so they are written `«to»`, `«from»` and
  `«prefix»`.
* **Procedure aliases.** `proc f = M.g` (`LRO`, `RRO`, `PRestr`, `FRestr`) is the same
  procedure: the module is a Lean function or definition that assembles its procedures with
  `T.mk`, taking the aliased ones from `M`.
* **Partially applied functors.** EasyCrypt applies `DRestr(D : DISTINGUISHER, F, P)` to `D`
  alone, and the result is a `DISTINGUISHER`.  Here `D` is a Lean parameter of the module, so
  `DRestr D` has that type.
* **Module restrictions** `{-C, -Redo}` on a lemma's module quantifier or `declare module` are
  footprint hypotheses, against `C.footprint` (or `X.footprint`, `FVP.fvP M`).
* **`declare axiom`s** are hypotheses with the axiom's name.
* **Name scoping.** Where EasyCrypt's last import shadows an earlier name (`SLCommon`'s
  `PRIMITIVE` over `Common`'s, both via clones), a file states the winner with
  `export GaudisCrypt.SHA3.SLCommon (state PRIMITIVE)`.  `state` also needs it, against the RO
  library's root-level `state`.
* **Inner modules** that do not depend on the functor's parameters (`G1(D).M`, `G1(D).S`) are
  modules of their own (`G1.M`, `G1.S`).
* **Clones of a theory without parameters** (`clone export ConcreteF as ConcreteF1`) are the
  theory itself, opened.
* **Repeated sub-expressions** of EasyCrypt statements, such as the instance of `INV_CF_G1`
  between `CF` and `G1`, may be named once (`INV_CF_G1_12`, `eq_glob_C` in `Handle`).  Such a
  definition is an abbreviation, documented as not being an EasyCrypt declaration.
* **Tuple parameters.** A procedure whose EasyCrypt parameters `(bl, nb)` are the module type's
  single parameter of a product type takes that pair and names its components
  (`bl, nb <- $x`).
* **Functor aliases.** `module Sim (F) = Gconcl.S(Last(F))` is the composite
  `Module.comp Gconcl.S Last`.
* **Abstract operators over earlier parameters.** An abstract `op` whose axioms mention
  definitions depending on earlier parameters is a class over those parameters:
  `class Params` (`parse`, `formatK` …) in `BlockSponge`, used with `[SLCommon.Params]`.
* **Section-local name clashes.** EasyCrypt reuses a local name in different sections of a file
  (`invmC` in `Real` and `Real_Ideal_Abs`, `L` in `Ideal` and `Simplify_Simulator`).  The locals of
  the later section go into a Lean namespace named after it (`Real_Ideal_Abs.invmC`).
* **Two-parameter procedures used as a functionality.** `IRO.f(x, n)` is used as the
  functionality `f : block list * int -> …`; here it takes the pair (`IRO.f (xn)`), and
  `BlockSponge.BIRO.IRO.asF` is its view as a `FUNCTIONALITY`.
* **Ground truth for names.** For a non-local declaration, `print M.X.` in `easycrypt cli`
  (`-I proof -I proof/smart_counter`, after `require M.`) shows it with every name fully
  resolved.  This settled `C.init` in `Gconcl_list`, where both `SLCommon.C` and
  `BlockSponge.C` are in scope; it is `BlockSponge.C`.
* **Views inside module bodies** are written out (`DFUNCTIONALITY.mk … { f := … }`): the `module`
  command's proofs cannot see through a helper such as `FUNCTIONALITY.view`.
* **Local clones and local modules with variables.** Their variables are lens parameters of the
  local declarations that mention them, with freshness hypotheses (`Sponge.HIRO_fresh`); the
  non-local results do not mention them (exception E6).  `local clone HybridIRO as HIRO` is the
  theory at the lenses `HIRO_Lazy_mp`, `HIRO_Eager_mp`.
* **Abstract simulators** (`declare module BlockSim <: SIMULATOR`) carry
  `Indifferentiability.SIMULATOR.Representable` (E2), as distinguishers carry
  `Module.Representable`.
* **Equivalences between procedures of different signatures** give them:
  `prhlProc (sig₁ := …) (sig₂ := …)`.  Arguments are tuples: `a₁.2.1` is the second parameter.
* **`proc f()` used where `proc f(_ : unit)` is expected** (a `RO_Distinguisher`) takes a `Unit`
  parameter.
* **Axioms of an abstract theory** whose operators are section variables (`SecureHash`): a
  structure `Axioms` of them, a hypothesis where needed and supplied by a clone's `realize`s.
* **EasyCrypt formulas in program expressions** (`exists y, …` in a game's result) are decided
  classically (`open Classical in` before the `module`).
* **A Lean parameter cannot receive a module parameter** inside a `module` body: the command
  cannot read the callee `D1(A)(F)` back when `A` is a module parameter of the caller.  Such a
  functor (`SecureRO.SecondPreimage.D1`) takes both as module parameters, as in EasyCrypt; a proof
  needing the partial application `D1(A)` builds it.
* **`{-M}` for a module `M` without variables of its own** (`-Preimage` in `SecureRO`) excludes
  the variables `M`'s code touches.
* **Abstract theories cloned with `include`** (`clone include Indifferentiability with …` in
  `SLCommon`) are abbreviations of the instantiated declarations in the including file.

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
     both for procedures with holes and for modules.  The module form carries a representability
     hypothesis (exception E2).  Still missing: the unary (`hoare`) version, the up-to-bad version,
     and the representation lemma that would remove E2.
   * **Up-to-bad**: `call (: bad, inv, inv')`, `byequiv : bad`, and `fel` (EasyCrypt's failure
     event lemma; used 8 times, in `Gcol` and `Gext` via `FelTactic`).
   * **Smaller tactics**:
     * `rcondt` and a general `rcondf`, for a loop or `if` at any position (531 uses);
     * `sim`, which relates two copies of the same code (308 uses);
     * `conseq` forms;
     * `transitivity`, `islossless`, `exlim`.
2. **Skeleton**: every definition ported and every lemma stated with `sorry`, in dependency
   order, so that the headline statements exist early.  In progress: `Common`,
   `Indifferentiability`, `OptionIndifferentiability`, `IRO`, `SLCommon`, `ConcreteF`,
   `Handle`, `Gcol`, `Gext`, `Gconcl`, `BlockSponge`, `Gconcl_list`, `Sponge`, `SHA3Indiff`, `SHA3_OIndiff`, `SecureHash`, `SecureRO` and `SecureORO` are done
   (2026-10-31).
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
