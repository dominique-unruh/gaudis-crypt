---
name: ec-transfer
description: Transferring EasyCrypt (.ec/.eca) developments to GaudísCrypt (Lean 4) one to one — declarations, statements and proof scripts in EC's shape. Use when porting an EC file or lemma, rewriting an old port in EC-fidelity form, or deciding how to express an EC construct/tactic in Gaudí.
---

# Transferring EasyCrypt proofs to Gaudí

Distilled from the EC-fidelity pilots in this directory (2026-11-06 … 11-09): `SecureRO`,
`SecureORO`, `IndifRO_is_secure`, `Indifferentiability`, `OptionIndifferentiability`,
`SecureHash`, `IRO`, `SLCommon`, `Sponge`, `ConcreteF`, `Handle`.  The design log, with the
reasons behind every rule here, is `notes/SHA3/Refactor.md`; the known structural deviations are
`notes/SHA3/Exceptions.md` (E1–E14).

## 0. The contract

Each EC lemma gets

* a Lean **statement that reads like EC's** (`equiv[ … ]`, `hoare[ … ]`, `phoare[ … ] = r`,
  `Pr[ … ]`, `islossless`), with **no hypotheses EC does not have**;
* a **proof that is EC's script, step for step**: same tactics (under prefixed names), same
  arguments, same positions, same conditions, same lemma names in the closers;
* **no auxiliary lemmas** for steps EC does inline (oracle steps, frames, restrictions,
  footprints).  EC's inline `have`s stay inline.

**The golden rule (Denis, 2026-11-08):** if the Lean proof needs glue EC does not have — `haveI`
instances, footprint proofs, `@lemma` with explicit instances, `rw [show X = Y from rfl]`,
`unfold …; module_norm; rfl`, `Eq.trans_le (b := …)` — **stop and fix the cause** (declarations,
instance search, the solver, the tactic) in `Logic/`, `Lib/` or `Syntax/`.  Don't push through
with glue.  After each EC step compare line counts; extra lines mean an infrastructure gap.

EC behaviour is a reasonable target but not a goal in itself: where EC is unreasonable, or we can
do better, deviate — and **document the deviation in the theorem's docstring**.

## 1. Workflow per file

1. **Read EC's file.**  The sources are not in the repo: clone `formosa-crypto/sha3` (directory
   `proof/`, `proof/smart_counter/`) into the session scratchpad — earlier sessions' copies are
   gone.  Note its clones, module variables, `declare module`s, `local` modules, `declare
   axiom`s, and which E-exceptions (`notes/SHA3/Exceptions.md`) it will hit.
2. **Port bottom-up** along the import graph.  (History of the SHA-3 files: they were first
   ported in an older style; the fidelity port of each lived in `Examples/SHA3/Pilot/` next to
   the old file, and dependents moved to it one by one.  On 2026-11-15 the first port's proofs
   were removed and the pilots promoted to `Examples/SHA3/`.  What a file still uses of the first
   port — modules, definitions, plain lemmas — is its section `FirstPort`; "the first port's" /
   "the old port's" in a comment refers to it.  A new port has no such section.)
3. **File setup**: `<EcName>.lean` in the development's directory (SHA-3: `Examples/SHA3/`,
   `SmartCounter/` for `proof/smart_counter/`), `namespace GaudisCrypt.SHA3.Pilot.<EcName>` (the
   SHA-3 namespaces kept their `Pilot` in the promotion), module
   docstring with a "Translation" list (see `SecureRO.lean`).  **Imports**: every EC tactic
   lives in its own module and there is no barrel for them — a missing import shows up as a
   *parse error* at the tactic.  Copy the import block of the closest pilot and add as needed:
   `Logic.ECProc` (`*_proc`), `ECSim` (`inline*`, `sim`), `ECAuto` (`*_auto`, `rnd_*`),
   `ECClose` (`auto_close`, `smt_close`, `auto_progress`), `ECSp`, `ECIf`, `ECSeq`, `ECInline`,
   `ECConseq`, `ECCallEquiv`/`ECCallAbstract`/`ECCallUpto`/`ECCallOneSided`/`ECCallFrame`/
   `CallSpec`, `ECWhile`, `ECLoop`, `ECTrans`, `ECAlias`, `ECGoals`, `StmtSwap`, `FelTactic`,
   `PHoareSeq`, `PrTactics`, `DeclareModule`, `ECModuleBinders`, `ModuleFootprint`;
   `Syntax.PrSyntax`, `Syntax.Clone`, `Syntax.ModuleVar`, `Syntax.ModuleSubtype`.  Add the file to
   `GaudisCrypt.lean` once it builds; add a section to `notes/SHA3/Mapping.md` (EC lemma → Lean
   name rows, as for the other pilots).
4. **Declarations first** (§2), then statements (§3) — compile them with `sorry` proofs.
5. **Proofs**: transcribe EC's script line by line (§4), closers last (§5).  **Each logical
   block starts with EC's own lines as a comment** (Denis, 2026-11-09), verbatim:
   `-- EC: proc; sp; inline*; sp.` then the Lean steps; a long EC block as several `-- EC:` lines.
   A reader checks the port block by block against EC this way.
6. **Each gap** (a step with no Lean counterpart, or one that needs glue): **don't stop the proof
   for it** (Denis, 2026-11-09).  Write that step by hand (or `sorry` it), mark it `-- GAP: <what
   is missing>`, add it to the gap list of the port (file header), and go on.  Fix the gaps in a
   **batch** — once, generically, in `Logic/`/`Lib/`/`Syntax/`, with a test next to it
   (`XTest.lean`) — then remove the hand-written workarounds: the final proof has no glue.  Only a
   trivial gap is fixed on the spot.  Batches show which gaps recur and which matter.
   Before adding anything, check it does not exist (`grep -rn 'elab "…' GaudisCrypt/Logic`;
   names with trailing spaces are easy to miss).
   **Ground truth from EC itself (Denis's method):** to design a tactic that must match EC — its
   goals, their order, their exact conditions, what counts as a statement — write a tiny EC file
   with *opaque* types and ops (`type t. op b1 : t -> bool. op I : t -> t -> bool.` …), modules
   over them, and run the tactic in `easycrypt cli` with `pragma Goals:printall.`.  Nothing can be
   simplified away, so EC prints every side condition in full.  Setup: memory
   `easycrypt_local_install.md` (opam switch `ec`); probes and logs in
   `~/easycrypt-transfer-probes/` (eager ones in `~/easycrypt-eager-experiments/`).
   Findings so far (`while_if.ec`): `var h, i, c <- x` is **three** statements; two-sided `if`
   leaves (1) the ambient `∀ &1 &2, P ⇒ (b1{1} ⇔ b2{2})`, (2) `P ∧ b1{1}` and (3) `P ∧ ¬b1{1}`
   with the programs in sync; two-sided `while I` leaves (1) the body `I ∧ b1{1} ∧ b2{2} ==> I ∧
   (b1{1} ⇔ b2{2})`, (2) the code before with post `(I ∧ (b1 ⇔ b2)) ∧ ∀ x_L x_R, ¬b1 x_L ⇒ ¬b2
   x_R ⇒ I x_L x_R ⇒ Q x_L x_R` (quantified over the loop's *modified variables*).
7. **Measure**: `scripts/ec_fidelity.py` (surface statements, clean proofs, term/den/fp, extra
   hypotheses, aux).  Update `notes/SHA3/Refactor.md` (Ported / Measurement) and
   `notes/SHA3/Mapping.md`.
8. **Build/check**: `LEAN_NUM_THREADS=4 nice -n 10 lake build <Module>` (use fewer threads if the
   box is busy — it is shared); never two lake builds at once.  After *any* change to closers or
   `generalizeReads`, also recheck the pilots outside the barrel (`SmartCounter/ConcreteF.lean` ~150 s,
   `IRO.lean`; `lake env lean …`) and do a full build — closer changes break old
   hand-written proofs (`rintro` patterns) far away.
9. Commit locally at milestones (`Co-Authored-By` line); the user pushes.

## 2. Declarations

| EC | Gaudí | Notes |
|---|---|---|
| `type from, to.` + `op`s + `axiom`s of a theory | `class Params («from» «to» : outParam Type)` with the ops and axioms as fields; `export Params (…)` | outParams: the one instance in scope (= EC's clone) fixes the types, so ops and module types are written without types. Then `variable {«from» «to» : Type} [Params «from» «to»]`. |
| `clone [import] T as C with type a <- τ, op o <- e` | `clone [import] GaudisCrypt.….T as C with type a <- τ, op o <- e` (`Syntax/Clone.lean`; the theory **fully qualified**), `proof * by tac` on its own line | Theory = namespace with `class T.Params`. Clone = instance `C.params` + reducible aliases `C.x`. Limits: no per-axiom `realize x by t` / `proof x by t` (only `proof *`); no clone `rename`; two clones of one theory at the same types share module variables, and same-type clones with different ops are unsupported (`Clone.lean` docstring). Clones of theories still in old (lens-parameter) style — `Lib/EC`'s `BitWord`/`PRP`/`RP`/`Strong_RP_RF`, `Common` (not re-ported) — are a `namespace C` with `global_var`s for its module variables, `abbrev`s applying the library modules at them, and its `realize`d axioms as theorems (`ConcreteF`'s `Switching`, `SLCommon`'s `F`). |
| `rename [module] "A" as "B"` | `noncomputable abbrev B := @C.A` | |
| `op f (x : t) = e` / `pred P (x : t) = e` | `def` (or `abbrev` when closers must see through it) / `def … : Prop` | EC's provers see through `op` bodies, ours don't: an opaque `def` must be passed to `smt_close`/`simp`. |
| `inductive P = \| C of …` (e.g. `INV_CF_G1`) | `inductive P … : Prop` (or `structure` for one constructor) | Fields by `.1`/`obtain ⟨…⟩`, as the old port's `INV_CF_G1`. |
| `module M = { var x : t … }` | `global_var M.x : t` before `module M { … }` | Disjoint from every other variable by instance search. |
| module variable whose type mentions only theory types | `module_var M.x : T` (`Syntax/ModuleVar.lean`) | It takes the theory's instance; `global_var` (in `Language/`, off-limits) does not. |
| `module type T = { proc f(x : a) : b … }` | `moduletype T { proc f (x : a) -> b; … }` | A module type named like a module: suffix `_T` (E3). |
| `module type A (F : Oracle) = { proc guess … }` | `abbrev A := Oracle →ₘ procmod (a) → b` | |
| `module type Adv (O : POracle) = { proc a1 … proc a2 … }` (several procedures, with an oracle) | `moduletype AdvProcs { proc a1 …; proc a2 …; }` + `abbrev Adv := POracle →ₘ AdvProcs` | Calls are `A(O).a1`, `A(O).a2`.  All call rules take them (2026-11-15, `br93.ec`): `equiv_call (_ : ={glob A, x, …})`, `(_ : ={…} ∧ I)`, `(_ : bad, I)`, pHL's `phoare_call`; see section 4. |
| `local module G1 = M(A) with { var r … proc main [ … ] }` (module update) | the module written out: `module_var G1.r : T`, `module G1 using (A : Adv) { proc main … }` | No module-update syntax.  `A` is a parameter, the lemmas say `G1(A).main`. |
| `module M (A : T, F : U) : V = { … }` | `module M using (A : T, F : U) : V { … }` | Procedures: `proc f (x : a) : b { var y : c; …; return e };` Reads are `$x`, writes `x <- e`, samplings `x <$ d`, calls `x <- call F.f ($a)`; booleans of props via `decide`; `open Classical in` before the module if needed. |
| EC's `witness` | `default` | |
| subtyping `RO <: RF` (passing an `RF` where an `Oracle` is expected) | `module_subtype RF <: Oracle` | Same-field module types: identity coercion. Module-type abbreviations are seen through. |
| `module CF(D) = Indif(SqueezelessSponge(PF), PF, D)` (alias) | `noncomputable abbrev CF (D : T) := Module.app Indif (Module.pair …)` | Prefer an alias over a `def` (a `def` needs `unfold` in proofs). |
| `section S. declare module A <: T {-M₁, -M₂}.` | `section S` … `declare module A <: T {-M₁, -M₂}` … `end S` (`Logic/DeclareModule.lean`; needs the enclosing `section`, as do `declare axiom`s) | Variable + instance-implicit `[Module.Declared A S]`; `S` read off the `global_var`s of `M₁`'s code / `glob` of declared modules. Representability is derived. |
| `declare axiom D_ll : …` | `variable (D_ll : ∀ (F <: T {-D}), …, islossless D(F, P).distinguish)` + `include D_ll in` on the lemmas using it | `∀ (F <: T {-X}), P` and `∃ (S <: T {-X}), P` are `Logic/ECModuleBinders.lean`. |
| `declare module D` whose lemma is later applied to a module built from a declared one (`Real_Ideal (A(D))`), with `declare axiom D_ll` over `{-D}` | `declare module D <: T {-M₁, -M₂} with glob R` and `{-R}` for `{-D}` in `D_ll` | E14. EC's `glob A(D)` is `glob D` and `A`'s variables by definition; ours is known from above only, so `{-A(D)}` does not give `{-D}`. `R` is a region above `D`'s footprint, restricted like `D`. Proofs do not change. At the application the region is written out: an instance `Module.ECGlob (A D) (R ⊔ C.c.footprint)` next to `A` (from `fvP_A`), and `@Real_Ideal _ (A D) ⟨by fp_finite, by fp_disjoint⟩ _ _ ⟨‹Footprint.Restricted R _›.finite.sup (by fp_finite), by fp_disjoint⟩ A_lossless m` (`Gconcl_list.concl`). A section whose lemmas receive such a `D_ll` needs the form too (the whole chain below the application). |
| `local module L (A : T) = { … }` | an ordinary `module` (or `module_var`s + `module`) inside `namespace Section` *before* the section's `declare module` | Its freshness for the declared adversary goes in the adversary's restriction list (EC: implicit) — e.g. `{-RO, -Preimage, -Preimage.Preimage2}`. |
| `local` (clones, lemmas) | nothing — names stay visible | |
| `lemma l &m (h : to) : Pr[ … ]` | `theorem l (m : VariableAssignment) (h : «to») : Pr[ … ]` | `&m` is an explicit memory argument. |
| `equiv l : M.f ~ N.g : P ==> Q` | `theorem l : equiv[ M.f ~ N.g : P ==> Q ]` | |
| EC lemma names | **verbatim** (E1), incl. `lemma1'`, `Real_GReal'` | A theorem of the current namespace shadows an opened one of the same name: to reach the opened one, qualify it (in `Pilot.Handle`, `SHA3.Handle.eq_fi` is the *old* port's lemma, the bare `eq_fi` the pilot's). |
| `state` (clashes with a root `state`) | `abbrev state := GaudisCrypt.SHA3.SLCommon.state` | |
| `open … hiding X` | same | Needed when EC's names clash with ours (`PRIMITIVE`). |

**Clone-level lemmas** (`RO_LRO_D` of a cloned `PROM.FullRO`): a theorem whose statement is
`type_of% (Lib.lemma … clone args …)`, its side conditions auto-params
(`(hD : … := by ec_module) (hdisj : … := by fp_disjoint)`), so the use is EC's `call (RO_LRO_D D)`.

**Concrete modules' footprints** are read off their code (`Logic/ModuleFootprint.lean`); add an
`@[fp_bound]` lemma (proved `by fp_module m`) only for library modules whose procedures the solver
cannot see through (PROM's `RO.init/get/set/rem` were missing; symptom: `fp_disjoint` fails on a
call to them).

## 3. Statements (surface syntax)

* Paths: `M(A, B(C)).f` is a term (`Syntax/ModuleApplicationSyntax.lean`); a head's explicit Lean
  parameters are filled first, so `D1(A, F)` = `Module.app (D1 A) F` (EC's partial application).
  A module without a module type (EC's `module Eager(D) = { proc main1 …; proc main2 … }`):
  `Eager(G2(DRestr(D))).main1` is the procedure module `Eager.main1 (G2 (DRestr D))`; its
  parameter names are found through abbreviations (a pilot's `abbrev Eager.main1 := PROM.…`).
  Mathlib's token `C(` breaks `C(P)`: write `«C»(P)`.
* Variables: EC's `x{1}` is `§x{1}`; module variables `§G1.bcol{2}`; `={x, y}`, `={res}`,
  `={arg}`, `={glob A}`, `={glob A, glob B}` (one region, the join — don't split it).
* `glob C` of a **concrete** module = its variables (`C.c`, `C.queries`); of a declared/abstract
  module its footprint.  Closers read `={glob C}` as variable equalities.
* `Pr[ M(A, F).main (x) @ &m : §res ∧ §C.c ≤ max_size ]` is a real number (EC's `Pr` is real);
  bounds are written over ℝ with casts: `((bound + 1 : ℤ) : ℝ) * mu1 sampleto h`.
* EC's `x \in m` (maps) is `FMap.dom m x`; `m.[x]` is `FMap.get m x` (or `m.get x`); `rng`,
  `fdom` are in `Lib/EC/FMap.lean`, `oget` in `Lib/EC/List.lean`, under EC's names.
* Boolean variables as propositions, as in EC: `(§G1.bcol{1} → §G1.bcol{2})` for EC's
  `G1.bcol{1} => G1.bcol{2}` (a read is elaborated without the expected type, then coerced: the
  term is `§G1.bcol{1} = true → …`, what goals and closers show).
* Parameter names in `hoare[ ]`/`phoare[ ]` are the procedure's; `arg` maps to `params`.
* `islossless M.f`.

## 4. Proof steps: EC tactic → Gaudí tactic

Prefixes: `equiv_*` (pRHL), `hoare_*`, `phoare_*`, `stmt_*` (any judgment).  Side `{i}` as in EC.

**Positions are EC's** in every position-taking EC form: inlining leaves `reset_vars` statements
(the callee's locals) that EC does not have; they are not counted and move with the statement
after them (`TacticMisc.ecGroups`, `ecGapIn`).  So EC's numbers are copied as they are:
`stmt_rcondt/f`, `equiv_seq`, `stmt_swap{i} n k`, `stmt_swap{i} [a..b] k`, `stmt_swap{i} k`,
`stmt_wp n m`, `stmt_sp n m`, `stmt_alias`, `stmt_splitwhile` (since 2026-11-09 for
`swap n k`/`wp n m`/`sp n m`).  `stmt_swap_raw{i} n k` is the older form in *our* positions
(resets counted), kept for the old ports only; `stmt_wp k` / `stmt_inline n` (one number) are
ours too.

**Goal order is EC's for `if`** (two-sided `stmt_if`: `guard, then, else`; EC's `if; 1,3: auto`
is `stmt_if; on_goals 1, 3 => equiv_auto`) and for `while` (`equiv_while`, two goals) — but see
the `while` row.

### Program logic

| EC | Gaudí |
|---|---|
| `byequiv` / `byequiv (_ : P ==> Q)` / `byequiv (H)` | `byequiv` / `byequiv (_ : P ==> Q)` / `byequiv (H)` |
| `byphoare (: P ==> _)` / `byphoare (H)` | `byphoare (: P ==> _)` / `byphoare (H)`.  Where `P` names a parameter of a game whose parameter names are not known (a clone's game, a module with a Lean parameter): `byphoare (?j : phoare[ M.main (m) : §m = a ==> §res ] ≤ (ENNReal.ofReal x))`, the judgment written out with its bound (§7) |
| `have ->: Pr[…] = Pr[…] by …` (rewrite chain) | `calc` steps, or `have e : … := by …` then `simp only [e]` (`rw` on `Pr[ ]` goals often fails its instances-transparency check) |
| `proc` | `equiv_proc` / `hoare_proc` / `phoare_proc` (to the body, params as locals; EC's counts) |
| `inline*` | `stmt_inline*` (`hoare_inline*`, `phoare_inline*`) |
| `inline*` of calls with several parameters, before a position (`swap n k`, `seq n m`) | `stmt_inline*` then `stmt_split_params` (`Logic/ECInlineParams.lean`, 2026-11-15): our inliner writes the parameters as one tuple assignment, EC as one assignment each; the tactic splits them (the tuple assignments after a `reset_vars`), so EC's positions and its swaps between two parameters apply.  A gap of the inliner: the line goes when `inline` does it |
| `inline{i} M.f` / `inline M₁ M₂` / `inline{i}*` | `stmt_inline{i} (M.f)` / `stmt_inline (M₁) (M₂)` / `stmt_inline*{i}` (parens needed: `stmt_inline n` inlines call site `n`) |
| `sp` / `sp n m` | `stmt_sp` / `stmt_sp n m` (EC positions) |
| `wp` / `wp n m` | `stmt_wp` / `stmt_wp n m` (EC positions; `-k` from the end). One-number `stmt_wp k` is *ours*: the last `k` statements |
| `auto` | `equiv_auto` / `hoare_auto` / `phoare_auto` |
| `auto`, `skip` (new proofs) | `ec_auto`, `ec_skip`: the same on every judgment, every read a value or an error; then `ec_intro` puts the values in the context under their names (`RO_m`, `bounder`, `x`), and the hand step names values, never `X.get σ.globals` |
| `skip` | `equiv_skip` / `hoare_skip` / `phoare_skip`; if a read under `decide` or an inlined call's renamed state blocks the closer, `equiv_skip_ec` (what `equiv_auto` uses) |
| `if` / `if{i}` | `stmt_if` (goals EC's: `guard, then, else`; each branch with the code after it, flattened: EC's positions inside a branch) / `stmt_if{i}` |
| `rcondt{i} n` / `rcondf{i} n` | `stmt_rcondt{i} n` / `stmt_rcondf{i} n`, EC's positions; side goal first: `· hoare_auto; …` |
| `seq n m : P` (pRHL) | `equiv_seq n m : (P)` (leading counts, resets not counted). The old from-the-end cut is `equiv_seq_last` |
| pHL `seq n : E p₁ p₂ p₃ p₄ I` (upper bound) | `phoare_seq n : (E) p₁ p₂ p₃ p₄ (I)`; goals tagged `invariant, first_E, second_E, first_notE, second_notE, bound` (bounds `1` closed on the spot), `_` bound allowed. `≤` goals only |
| pHL `seq n : P` on a lossless goal (`islossless`, `phoare[ … ==> 1 ] = 1`) | `phoare_seq_lossless n : (P)` (`Logic/PHoareSeq.lean`); goals `first` (the first `n` statements reach `P` with probability 1; for `seq n : true`, lossless), `second` |
| Hoare `seq n : P` (one condition) | **missing** as an EC-form tactic (Gconcl_list); `stmt_split k` cuts counting from the end |
| `swap{i} n k` / `swap{i} [a..b] k` / `swap k` | `stmt_swap{i} n k` (EC positions) / `stmt_swap{i} [a..b] k` / `stmt_swap{i}? [-]k`.  A call moves past assignments, samplings, and deterministic `if`s/sequences of writes to globals outside the callee whose conditions read what the call keeps (`callDet`, Gcol's `swap{1}[1..2]3`).  Not yet: past an assignment whose value reads a global the callee only *reads* (Gcol GAP 4: inline the call first).  **When the moved block and what it moves past both read a variable** (footprints not disjoint), do EC's later `inline *` first (`stmt_inline{i} k`, last call first) so that one side is deterministic code, then `stmt_swap` at EC's positions *after* the inlining (a `reset_vars` counts with the statement after it); EC's later `seq`s then count the inlined statements (Gconcl `G2_G3` `S.f`) |
| `call (: inv)` (abstract adversary, Hoare) | `hoare_call (: inv)`; goals oracle(s) first, then pre |
| `call (_ : ={glob A, x…})` (abstract) | `equiv_call (_ : ={glob A, x, …})` |
| `call (_ : ={…} /\ I)` | `equiv_call (_ : ={…} ∧ I)`; the oracles' goals are EC's `={arg} ∧ I ==> ={res} ∧ I` (`={glob D}` framed by their writes), so EC's intermediate conditions need no `glob D`.  With another `glob X` named (or an oracle the frame cannot open, a view), the oracles keep the region `glob D ⊔ glob X` themselves |
| `call (_ : bad, I, J)` (up to bad) | `equiv_call (_ : bad, I, J)`; EC's goal order; `D_ll`'s goal: `exact D_ll` (E11: right oracles' `islossless` is one more goal each) |
| `call (_ : …)` on `A(O).a2`, `A` declared at a type with **several procedures and an oracle** | the same `equiv_call (_ : ={glob A, x, …})` / `(_ : ={…} ∧ I)` / `(_ : bad, I)` (2026-11-15).  Differences from the single-procedure case, both EC's: the code before gets EC's **frame** (a global the postcondition reads and neither `A` nor the oracle writes keeps its value: `∀ r g, … → G.z.get g₁ = §G.z{1} → …`), and up-to-bad's precondition is EC's `bad ∨ (={args, glob A} ∧ I ∧ ¬bad)`.  Every global of the section's modules that must survive the call has to be in `A`'s restriction (`{-LRO, -Log, -Game1, …}`) |
| `call (: P ==> Q)` (concrete callees, pRHL) | `equiv_call (_ : P ==> Q)`; callee's judgment first, then pre; the frame of unwritten variables is found |
| `call (_ : ={glob P})` / `call (_: ={x})` (concrete callee) | `equiv_call (_ : ={glob P})` / `equiv_call (_ : ={x})`, with EC's frame (what the callee does not write keeps its value); the callee's judgment (EC's `1: by sim`) is closed by its footprint |
| `call (_ : true)` on the adversary (a declared module) | `equiv_call (_ : True)` (2026-11-15): `equiv_call (_ : ={glob A})` for the module `A` the two calls are of; with oracles' variables to keep, `equiv_call (_ : ={glob A, x, …})` as before |
| `call H` | `equiv_call (H)` (also where the calls spell the callees differently from `H`: behind a record `(RF.mk { get := M.get }).get`, a view unfolded — `H` is taken to them by their bodies, `Logic/ECProcInv.lean`); `phoare_call H` (`?_` holes = EC's `call` subgoals); `hoare_call H` |
| `call{i} H` | `equiv_call{i} H / x, glob A` (frame listed) |
| `call (: P ==> Q)` in `phoare` / `hoare` | `phoare_call (: P ==> Q)` / `hoare_call (: P ==> Q)`; with EC's frame (what the callee does not write): `phoare_call (: P ==> Q) / x, …`, `hoare_call (: P ==> Q) / x, …` (the trivial triple `True ==> True` closed), `phoare_call H / x, …` for lossless + frame |
| `sim` / `sim n m` / `sim (_ : I)` / `sim` with `={glob A}` | `sim` / `sim n₁ n₂` / `sim (_ : I)` / `sim / x₁, …, xₙ` (equal except the listed globals).  Calls of different concrete procedures (EC's `sim` goes into them): where plain `sim` makes no progress it inlines the callees, runs again and closes the rest by `auto_close` — so EC's `by sim` stays `sim` (Gconcl `G4_Ideal`).  A partial `sim` is never changed that way.  Two loops: the invariant is the relation after them plus EC's equality set (computed backwards through the bodies, `ECSim.eqBack`: locals written before read are not in it); when that relation reads what the loops change, the equality set alone (Gconcl `G2_G3` `M.f`).  Why `sim` stops: `set_option debug.sim true in sim` (loops, calls, unfinished branches) |
| `rnd` / `rnd{i}` / `rnd f` | `equiv_rnd` / `equiv_rnd{i}` / `equiv_rnd f` (product samplings: `equiv_rnd_dprod`) |
| `rnd f g` | `equiv_rnd f g` (`Logic/ECRnd.lean`, 2026-11-15): EC's three conditions in the postcondition before the samplings (`rR = f (g rR)`, `mu1 d₂ rR = mu1 d₁ (g rR)`, `rL = g (f rL)` with `f rL \in d₂` and the postcondition); `f`, `g` may read both memories (`§k{1}`).  For two samplings from the uniform distribution (or `dbool`) the masses and the supports are discharged, and EC's `auto; progress` after it is `equiv_auto; auto_progress` (it closes ring identities itself).  `equiv_rnd f` (one function) stays for involutions and for the cases with a known push-forward (`SHA3OSecurity` `rw_ideal`: `equiv_rnd (fun l => oget (of_list l))` with `dlist_dout`) |
| pHL `rnd (pred1 v)` / `rnd` (lossless) | `rnd_pred1 v` / `rnd_bound` (on the expectation `phoare_auto` leaves at a sampling) |
| pHL `rnd E` on an **exact** bound (`phoare[ c; x <$ d : P ==> Q ] = r`) | `phoare_rnd E` (`Logic/PHoareRnd.lean`, 2026-11-15): the goal becomes EC's `phoare[ c : P ==> mu d E = r ∧ ∀ v ∈ d, (E v ↔ Q v) ] = 1`; `E` may read variables (`phoare_rnd (pred1 §b')`).  `mu`, `mu_pred1`, `dbool1E_mu1`, `pred1E` for the closer |
| pHL `call H` (`H : islossless f`), `rnd`, `auto` on `phoare[ c : P ==> Q ] = 1`, `Q` an event | `phoare_call H` / `phoare_rnd` / `phoare_auto` with `Logic/PHoareRnd.lean` imported (2026-11-15): the judgment stays an event, as in EC — a call leaves `∀ result, Q`, a sampling `is_lossless d ∧ ∀ v ∈ d, Q`, `auto` ends with `P → Q'` (`Pedersen.ec`'s `rnd (pred1 b'); call ug_ll; wp; rnd; call uc_ll; auto => />` is the same line; EC's `rewrite dt_ll … dbool1E` after it is `smt_close [dt_ll, mu_pred1, dbool1E_mu1, pred1E]`).  Without the import, and on an expectation that is not an event (`1` after `conseq (: _ ==> true)`), the rules on expectations apply as before |
| `conseq (: _ ==> Q)` on `phoare[ … ] = 1` | `phoare_conseq (: _ ==> Q)` (same file): goals `post` (over values), then the judgment; `Q = True` gives `phoare[ … ==> 1 ] = 1` |
| `conseq (: _ ==> true) (: _ ==> Q)` on `phoare[ … : P ==> Q ] = 1` (the event by Hoare logic, then losslessness) | `phoare_conseq (: _ ==> True) (: _ ==> _)` (2026-11-15): goals `hoare` (`hoare[ P ==> Q ]`), then `lossless` (`phoare[ P ==> 1 ] = 1`).  On the statement: after `byphoare`, `phoare_proc` first (EC's `proc` in each branch is then dropped) |
| pHL `call (_ : true)` on the adversary with `declare axiom A_ll (O <: POracle {-A}) : islossless O.o => islossless A(O).a`: EC's goals `exact A_ll` and the oracle's losslessness | `phoare_call (@A_ll _ ?_ ?_)` (the oracle and its restriction are found from the call; the restriction is closed), then `· islossless` for the oracle (EC's `proc; call (LRO_o_ll _); auto; apply dptxt_ll`), with the samplings' `is_lossless` lemmas tagged `[ec_random]` |
| `islossless` (the tactic) | `islossless`: on `phoare[ c : P ==> 1 ] = 1` or `islossless M.f`, code without loops; assignments and samplings from `dbool`, the uniform distribution or a distribution with `is_lossless d` in the context are closed, each call leaves `islossless p`, the last call first — EC's `islossless; [apply Ag_ll \| apply Ac_ll]` is `islossless <;> [exact Ag_ll; exact Ac_ll]` |
| `hint exact random : dhkey_ll.` | `attribute [ec_random] dhkey_ll` (`Logic/ECHints.lean`): the lemmas `is_lossless d` that `islossless` closes a sampling with (EC's hint database `random`); the library's `dbool_ll`, `uniform_ll`, `BitWord.dunifin_ll` are tagged |
| `rnd f` (pRHL, `f` an involution) | `equiv_rnd f f`: EC's `rnd f` is `rnd f f` (`hashed_elgamal_std.ec`'s `rnd (fun w, w +^ m)`; the xor identities by `Lib/EC/BitWordRing.lean`'s simp lemmas) |
| `hoare` | as a *tactic turning a `phoare … = 0`/`≤ 0` goal into a Hoare triple*: `phoare_hoare`; at a *sampling* inside a pHL proof (the event has probability 0): `rnd_null` |
| `conseq (: P ==> Q)` / `conseq (_ : _ ==> Q)` | `equiv_conseq (: P ==> Q)` / `equiv_conseq (: _ ==> Q)`; also `hoare_conseq (: P ==> Q)`, `phoare_conseq (: P ==> Q)` (upper bounds). EC's frame of what the code keeps is kept: the `post` goal is `P σ → (frame) → Q' τ → Q τ`, for `equiv_conseq` and (since 2026-11-16) `hoare_conseq` — EC's `conseq (_: _ ==> Q') => //; move=> &m -> …` needs no copy of the precondition's facts in `Q'` |
| `conseq (_ : P ==> Q) _ (_ : P₂ ==> Q₂)` | `equiv_conseq (: P ==> Q) _ (: P₂ ==> Q₂)` (`Logic/ECConseqHoare.lean`): the right program's own Hoare triple, its conditions written with the tag (`size §bs{2} = §n{2} - 1`); goals `pre`, `post`, `hoare`, `judgment` |
| `conseq H` | `equiv_conseq H` (pRHL only); on procedures, when `post` needs the precondition (EC keeps it): `equiv_conseq_pre H` (`Logic/ECConseqHoare.lean`); when the goal keeps variables or a `glob` that `H` does not mention (EC's frame), or the goal names the procedures through module views: `equiv_conseq_frame H` (`Logic/ECProcInv.lean`), which also closes the implications that are trivial (`by conseq H`) |
| `exists* e₁{1}, e₂{2}; elim* => a b` | `equiv_exists* §e₁{1}, §e₂{2}` then `intro a b` (also on procedure judgments, `§x{2}` the parameter); `stmt_exists* e` |
| `elim * => a b` (after `sp`) | `equiv_elim* => a b` / `hoare_elim* => a`: EC's names, the left side's existentials first |
| `case (P)` (pRHL) | `equiv_case (P)` |
| `case @[ambient]: {-1}(e) (eq_refl e) => [h₁ \| x h₂]` | `rcases h : e with _ \| x` (or `by_cases h : P`) |
| `exfalso` | `equiv_exfalso` |
| `while I` (two-sided) | `equiv_while (I)` (`Logic/ECWhileRel.lean`): EC's two goals, `body` (`I ∧ b₁ ∧ b₂ ==> I ∧ b₁ = b₂`) and `hpre` (EC's `(I ∧ b₁ = b₂) ∧ ∀ τ₁ τ₂, (frames: what the loops keep) → I → ¬b₁ → ¬b₂ → Q`). EC's `while I; last first; + auto; progress.` and its bullets transcribe as `equiv_while (I)` then `case hpre => equiv_auto; auto_progress` with one bullet per EC bullet (PFf_Cf's first loop: EC's seven).  The exit goal's frames are equations between the two final states' reads (`x τ₂ = x τ₁`, and the invariant's `x τ₁ = x τ₂`): `subst_frames` keeps one of each pair, so `progress`/`smt_close` close frame equalities as EC does.  The older four-goal form without frame is `equiv_while_raw` |
| `while{i} I V` | `equiv_while{i} (I) (V)`; goals `lossless`, `variant`, then the code before (EC's: `I` and, over the loop's final states under EC's frame, `I ∧ ¬guard ⇒ post`; old form with an `exit` goal and no frame: `equiv_while_noframe{i}`). EC's body goal (`auto; sp; rcondt 1; …`) on `lossless`: `while_ll_phoare`, then the `phoare` tactics |
| pHL `while I V` (`= 1`) | `phoare_while I V` (then `intro k` in the body goal) |
| pHL `while I V k ε` (the loop alone; probabilistic termination) | `phoare_while I V k ε` (`Logic/PHoareWhileRev.lean`, 2026-11-15): `V` an integer, `k` an integer, `ε` a real.  EC's goals in its order — `pre_inv`, `pre_bound`, `term` (`I → V ≤ k ∧ (V ≤ 0 → ¬guard)`), `body` (`∀ w, phoare[ w : P ==> Q ] = r → phoare[ c; w : P ∧ guard ==> Q ] = r`: EC's abstract statement, `intro w ih`), `inv`, `rate` (`0 < ε`), `variant` (`∀ z, phoare[ c : I ∧ guard ∧ V = z ==> V < z ] ≥ ε`) — those that are not judgments closed when trivial (EC's `=> //`); beyond EC's, `sat` (some state satisfies the postcondition; closed for `true`): our `w` is a quantified statement, and without `sat` the `body` goal could hold vacuously.  EC's `seq 1: true=> //` on the body goal is `phoare_seq_lossless 1 : (True)` with `exact ih` for the second part |
| pHL `seq n : E p₁ p₂ p₃ p₄ I` on an **exact** bound | `phoare_seq n : (E) p₁ p₂ p₃ p₄ (I)` with `Logic/PHoareExactTactics.lean` imported (2026-11-15): the bounds are reals, `_` as in EC (a bound left open where the other bound of its branch is `0`; its goal is not asked).  EC's goals in its order: `invariant`, `first_E`, `second_E`, `first_notE`, `second_notE`, `bound` (the reals' equation `r = p₁ p₂ + p₃ p₄`).  It counts the statements of a block (the loop body before `stmt w` in the body goal of `while I V k ε`).  `I` may be left out (EC's default `true`).  On a lower bound `≥ r`: the same goals with `≥`, `_` a bound `0` (its goal not asked), `bound` is `r ≤ p₁ p₂ + p₃ p₄`; `nonneg` (`0 ≤ pᵢ`) is left when `positivity` does not find it.  On an upper bound: the rule of `Logic/PHoareSeq.lean`, as before |
| pHL `case (E)` | `phoare_case (E)`: goals `pos`, `neg` |
| `bypr (res{1}) (res{2})` on `equiv[ f ~ g : P ==> ={res} ]` | `bypr (res{1}) (res{2})` (`Logic/ByPrEquiv.lean`, 2026-11-15): the goal becomes `∀ a₁ &1 a₂ &2 v, P → Pr[ f (a₁) @ &1 : res = v ] = Pr[ g (a₂) @ &2 : res = v ]` (EC's `=> &1 &2 v` is `intro a1 m1 a2 m2 v _`; then `cases a1; cases a2` for procedures without parameters).  The coupling comes from the wp-lifting (discrete Strassen), not from a hand-built one.  Shown raw (not as `Pr[ ]`) while the arguments are variables |
| pHL `conseq (_ : _ ==> _ : = e)` (another bound) | `phoare_conseq (: _ ==> _ : = e)`, `e` a real: goals `bound` (the two bounds are equal under the precondition, over the reals), then the judgment; the bounds `0`, `1` are then `0`, `1` (`phoare_hoare` and the event rules apply) |
| pHL `conseq (: P ==> _)` on an exact bound | `phoare_conseq (: P ==> _)`: `pre`, then the judgment |
| pHL `conseq (_ : _ ==> Q₁) (_ : _ ==> Q₂)` on an exact bound | `phoare_conseq (: _ ==> Q₁) (: _ ==> Q₂)`: goals `post` (under `Q₂`, `Q₁` iff the event), `hoare` (for `Q₂`), then the judgment for `Q₁` — EC's order |
| pHL `conseq H` (`H` the hypothesis of `while I V k ε`'s body goal) | `phoare_conseq H`: goals `pre`, `bound`, each closed when trivial |
| `hoare` on `phoare[ … ] = 0` | `phoare_hoare` |
| pHL `conseq (: P ==> Q)` on a lower bound `≥ r` | `phoare_conseq (: P ==> Q)` (`Logic/PHoareRnd.lean`): goals `pre` (closed when trivial), `post` (from the old precondition, `Q` implies the old event: EC's goal, over the values before and after), then the judgment |
| pHL `rnd` / `rnd E` on a lower bound `≥ r` | `phoare_rnd` (the postcondition is the event) / `phoare_rnd E`: the goal becomes `phoare[ c : P ==> r ≤ mu d E ∧ ∀ v ∈ d, (E v → Q v) ] = 1`; then `phoare_auto` |
| Hoare `while I` | `hoare_while (I)` (`Logic/ECWhileHoare.lean`, 2026-11-16): EC's two goals, `body` (`I ∧ b ==> I`) and `hpre` (the code before establishes `I ∧ ∀ τ, (frame: what the loop keeps) → I τ → ¬b τ → Q τ`), so what the precondition says of variables the loop does not modify is there on exit and stays out of `I`.  `while I; auto; smt(…)` is `hoare_while (I) <;> hoare_auto <;> smt_close […]`.  The older form — three goals `body`, `exit`, the code before with postcondition `I`, no frame — is `hoare_while_raw I` (the first SHA-3 port's proofs use it) |
| `splitwhile{i} n : e` / `unroll{i} n` | `stmt_splitwhile{i} n : e` / `stmt_unroll{i} n` |
| `alias{i} n x = e` | `stmt_alias{i} n x = e` |
| `transitivity{i} { code } (P₁ ==> Q₁) (P₂ ==> Q₂)` | `equiv_trans{i} { code } (P₁ ==> Q₁) (P₂ ==> Q₂)` |
| `transitivity N.f (P₁ ==> Q₁) (P₂ ==> Q₂)` (procedure) | `equiv_trans (N.f) (P₁ ==> Q₁) (P₂ ==> Q₂)` (`Logic/ECTransProc.lean`, 2026-11-15): goals `hP` (the middle procedure's argument and memory: `exact fun _ g _ _ _ => ⟨args, g, …⟩`), `hQ`, then the two judgments; `hP` for preconditions `true` and `hQ` for equalities that compose are closed.  (Sponge's two uses are still the rule `prhlProc_trans_ec`.)  A judgment whose condition reads a parameter is shown as the plain `prhlProc` term (display) |
| `proc *; rewrite equiv[{1} 1 L args]` (a call replaced along an equivalence) | no tactic: `equiv_trans (N.f) …` on the procedures, one step per rewrite, `exact L` for its judgment (`Examples/Dice4_6.lean` `D4_D6`); for `rewrite equiv[… -L]`: `equiv_sym; exact prhlProc_conseq L (fun _ _ _ _ h => h) (fun _ _ _ _ h => h.symm)` |
| `proc (I)` on an abstract procedure | `equiv_proc (I)` (`Logic/ECProcInv.lean`): `D(O₁).f ~ D(O₂).f` with `D` declared, or a procedure with a rule tagged `@[proc_inv]` (a simulator's `S(F).f`: `attribute [local proc_inv] SIMULATOR.call_f SIMULATOR.call_fi`, and the simulator's oracle lists as a section hypothesis). Goals: the oracles' judgments in EC's form `={arg} ∧ I ==> ={res} ∧ I` (then `exact H`, EC's `apply H`), then `pre` if `ec_auto` does not close it. EC's `call (_ : P ==> Q). proc (I)` on the last statement is `equiv_call (_ : ={glob M} ∧ I)` directly |
| `symmetry` | `equiv_sym` |
| `fel n cntr step q bad [O.f : pre] inv` | `fel §cntr (fun i => step) q (bad) [pre] (inv)` — EC's `n` dropped: the call must be the **last** statement (`stmt_wp` first). Goals EC's order (`sum`, `init`, oracle `step`, `incr`, `same`, `keep`). Deviations: `bad` must persist; **one oracle only** — Gext's `fel 8 … [ReSample.f : …; ReSample.f1 : …]` needs the multi-oracle extension .  **A procedure the oracles call** (`fel … [Gcol.sample_c : pre]`): `fel §cntr (fun _ => step) q (bad) [Gcol.sample_c : pre] (inv)?` (`Logic/FelInner.lean`; `inv` may be left out): `stmt_wp` itself, the event may be EC's `bad ∧ cntr ≤ q`, `pre` may read anything, the oracles' code checked syntactically (`exp_decr`), `lt` closed; goals `sum`, `init`, then per procedure `step`, `incr`, `same`, `keep`. Over the procedure's body: `byphoare (: True ==> _)`, `phoare_proc`, `phoare_inline*` first (Gcol's `Pr_col`).  Code *after* the adversary's call (Gext's resampling) is checked like the oracles, so it must stay calls of the named procedures: inline only the wrapper (`phoare_inline 1` for `DRestr(D)`'s call, Gext's `Pr_ext`); several procedures `[ReSample.f : …, ReSample.f1 : …]` (EC's `;` is `,`) |
| `bypr` (pHL, `phoare[ p : P ==> E ] ≤ r`) | `bypr` (`Logic/ByPr.lean`): the goal becomes `∀ a σ, P → Pr[ p (a) @ &σ : E ] ≤ x` (`=`, `≥`), the bound a real (`ENNReal.ofReal x`); EC's `bypr=> &m [#] -> h` is `intro a m' ⟨ha, h⟩` then `have ha' : a = mess := ha; subst ha'`.  `bypr e₁ e₂` (pRHL) is not a tactic (E12; before `fel` it collapses to `phoare_proc`) |

### Goal management

| EC | Gaudí |
|---|---|
| `t; 1,3: t'`, `2..-2: t'`, `-1: t'` | `on_goals 1, 3 => t'`, … — it acts on **all current goals**, not only `t`'s subgoals as in EC: use it inside a focused bullet (`· t; on_goals 1, 3 => t'`). Remember `equiv_while`'s four goals |
| `last first` / `first last` | `rotate_right` (`swap` when there are exactly two goals) / `rotate_left` |
| `n: t` (one goal) | Batteries' `on_goal n => t` |
| `t; t'` (on all subgoals) | `t <;> t'` |
| `t; [t₁ \| t₂]` (67 uses) | `t <;> [t₁; t₂]` (Batteries) or bullets; EC's `t₀; t; 1,3: t'` over branches as `t₀ <;> (t <;> [t'; …])` — `on_goals` positions shift when branches leave different numbers of goals |
| `+ …` / `- …` bullets | `·` |
| `=> //` | usually nothing (the tactics close trivial goals); else `<;> try trivial` |
| `progress` (286 uses) | `auto_progress` (`Logic/ECClose.lean`), leaves goals split and simplified |
| `auto => /#`, `progress` (new proofs) | `ec_close`, `ec_progress` (`Logic/ECProgress.lean`): the states first (every read a value, or an error), then logic; `ec_prep` before a hand step |

## 5. Closers (EC's `smt`, `/#`, `move=>`, `progress`)

Closers are the bulk of the remaining manual work.  Order of attack:

1. **`auto_close`** — our `auto => /#`: intro, take hypotheses apart, substitute, reads through
   writes, `glob_simp`, split, `omega`/`simp_all`.  Closes or fails (never half-way).
2. **`smt_close [l₁, …]`** — EC's `smt(l₁, …)` (grind-based, reads generalized).  Try it **at
   most once** with EC's hint lemmas; if it fails — *any* failure, internal `grind` errors
   included — **write the closer by hand right away**.  Never investigate why `grind` fails, and
   don't list grind failures as infrastructure gaps (Denis, 2026-11-08 and 2026-11-09: time spent
   on grind/smt is wasted).  EC's provers see through definitions; ours don't: pass definitions to unfold
   (`prefix_inv`, `all_prefixes`) as hints.  When `grind` fails, `smt_close` retries once with
   the hint lemmas' instances at the goal's terms as hypotheses (`ec_instances`: `size_ge0` at
   `size p`), so EC's `smt(List.size_ge0 …)` needs no `exact size_ge0 _` first.
   Since 2026-11-16 the closer also does what EC's provers do in these cases (so EC's line
   transcribes; the two steps above come first, a goal they closed is closed as before):
   * a **predicate of the file being checked** (`def P … : Prop`, EC's `pred`) is unfolded
     without being named (`sxor2`, `is_restr`); a predicate of a library still has to be named;
   * **linear arithmetic over the reals** (`linarith`; `grind` does not do it);
   * **a chain of lemmas** (`smt(pr_Game0_Game1 pr_Game1_Game2 … pr_Game2_OW)`): the lemmas
     are instantiated at the terms of the goal and of the instances, their hypotheses and
     instances taken from the context (`A_a1_ll`, `A_a2_ll` of the section);
   * **a hint that is a fact**: a lemma applied to its arguments (`smt_close [l A m]`), or the
     name of a lemma with no argument but instances (`dbool_ll`, `dbiased_ll`, a theory's axiom
     `in01_p`, `N_pos`), becomes a hypothesis.  (`grind [l]` on such a name fails with "unknown
     free variable" when its instance comes from a clone.)
   EC's `rewrite l; smt(…)` before a closer: put `l` in the hints (`rewrite oflist_cons;
   smt (is_restrS is_restr_addS)` is `smt_close [oflist_cons, is_restrS, is_restr_addS]`).
   A pHL bound that is `0` needs `ENNReal.ofReal_zero` as a hint.  A hint list with a name that
   does not exist fails like any other failure: check the names first.
3. **By hand**, with **EC's lemmas** (`lemma1'`, `huniq_hinvK_h`, `m_p_of_INV` …):
   `auto_prep` then `rw`/`simp`/`refine lemma … ?_ ?_`.  For a lemma over plain values:
   `generalize_reads_all; subst_vars; apply lemma <;> assumption`.  A conditional postcondition
   (`if bad then … else …`, what EC's `progress` splits): `auto_prep; split_ifs`, then one bullet
   per EC bullet.

What `auto_prep` does (so you know what is left to write): intro, split conjunctions,
`norm_decide` (`decide` instances), `glob_tuples` (`={glob C}` of a concrete module as its
variables' equalities, in goal and hypotheses, also over written states), **`mp_hyps`** (EC's
`progress` on implications: `h : p → q` with `p` a hypothesis becomes `q`), `subst_named` (`<<*`),
`subst_reads` (`<<-`/`->>`), `subst_vars`, `glob_reads`, reads through writes, `glob_simp`, and
**`subst_frames`** (EC's memories as one: the frames `X.get τ = X.get σ` that `conseq`/`call`
leave for unmodified variables, and `={x}` equations, rewrite the later state's reads into the
earlier one's — after it, unmodified variables are read in one state, as in EC's goal).
4. If EC's inline closer is very long (100+ ssreflect lines) and the old port proved the same
   fact as a lemma, reusing it is acceptable — **as a documented deviation** (`eq_f`'s path case
   = `f_path_inv`).

**Auxiliary lemmas, the one exception to "no aux lemmas":** a small lemma *over plain values*
(no programs, no states) that stands for what EC's `smt` finds by itself — ConcreteF's `db_*`,
`rc_*` — is allowed, named after the EC lemma it comes from, in the game file if specific,
in `Lib/EC/` under EC's name if generic.  Never an aux lemma for a program step.

**Hand closers in practice** (from `PFf_Cf`):
* After `auto_prep` the variables and hypotheses are anonymous: name them with `rename_i` (print
  the context once to get the order), then apply EC's lemma explicitly.
* An EC invariant in conjunction form and an old-port lemma stated over a packaged predicate
  (`PJ2 …`): build the predicate from the named hypotheses (`⟨hI, hmp, ⟨f, hh⟩, …⟩`), apply the
  lemma, take its result apart, `refine` the goal.  Name long terms with `set x := … with hx`
  when a lemma argument is not determined by unification.
* EC's pair `((oget m.[x]).1, (oget m.[x]).2)` vs `oget m.[x]`: `simp only [Prod.mk.eta]`;
  `x ∈ m → m.[x] = Some (oget m.[x])` is EC's `FMap.get_some`.
* One EC closer repeated over many leaves (`smt(get_setE mem_set DBlock.dunifin_ll …)`): one
  file-local `macro` with a docstring naming EC's call, used at each leaf.
* EC's `smt(lemma)` where the lemma is an inequality (`prefix_sizel`, `card_rng_set`): `grind`'s
  default pattern is the normalized inequality, which never matches — give the lemma a
  `grind_pattern` on the term EC's `smt` would trigger on (`grind_pattern card_rng_set =>
  FMap.frng (FMap.set m x y)`), next to the lemma; then `smt_close [lemma]` works.
* A procedure called as a module (`call Gcol.sample_c.procedure`, inside an inlined oracle) is
  `Module.proc p` to the footprint solver, which reads only named `module`s off their code: give
  it an `@[fp_bound]` (`FVP.fvP (Module.proc M.f.procedure) ≤ … := by fp_module (Lens.pair …)`).
* Our abstract `call (_ : ={…} ∧ I)` keeps `={glob D}` in the oracles' judgments (EC's do not
  mention it): EC's intermediate `seq` conditions inside an oracle need `glob D` added (gap).
* `simp_all` can cycle on hypotheses that are equations between reads (EC's frames) and hit the
  recursion limit — a *runtime* exception that `try`/`first` do not catch: `auto_progress` uses
  `simp_all_done_safe` (runtime-safe); in hand closers avoid bare `simp_all` on such contexts.
* Do not add rules to `auto_prep`'s simp set that change the *shape* of hypotheses (decoding
  boolean guards broke ConcreteF's `apply db_* <;> assumption`): decode locally
  (`simp only [Bool.and_eq_true, decide_eq_true_eq] at *`) where a closer needs it.

Mappings for ssreflect idioms:

* `move=> &1 &2 [#] !<<- ->> h` → the closers do it (`subst_named` = `<<*`, `subst_reads` =
  `<<-`/`->>` for `read = name` or `read = (name, name)`); positional `move=> … ya ? yc ?` →
  `rename_i ya _ yc _` (a deviation; names are positional in EC's sense).
* `have /lemma [] h1 h2 := inv0` → `obtain ⟨h1, h2⟩ := lemma … inv0`.
* `case: e => [|x]` / `elim` → `rcases e with _ | x` / `induction`; views `apply/l`, `move/l` →
  `apply l.mpr` / `have := l.mp h`; `rewrite /f` → `unfold f`/`simp only [f]`; `rewrite -l` →
  `rw [← l]`; `@/f` → `simp only [f]`; `split` → `constructor`/`refine ⟨?_, ?_⟩`;
  `exists x` → `refine ⟨x, ?_⟩`; `pose x := e` → `set x := e`; `congr` → `congr 1`;
  `do !t` → `repeat t`; `ring` → `ring`; `smt ml=0 w=…` → as `smt`.
* `rewrite domE Pmi_xaxc` → `simp [FMap.domE, Pmi_xaxc]`; `smt(domE)` → `smt_close [FMap.domE]`.
* Plain lemmas over an invariant (Handle's `lemma1`–`lemma3`, ported 2026-11-20):
  `have /hs_of_INV [] … := HINV` → `obtain ⟨…⟩ := hs_of_INV _ … _ HINV` (one `_` per argument, as
  EC's own `m_p_of_INV _ _ … inv0`); `by case: HINV` (a component of the invariant) →
  `cases HINV; assumption`, also inside a term (`(by cases HINV; assumption)`); `split` on the
  invariant → `constructor`, one bullet per EC bullet, in EC's order.
* `[#] <<*>` on `some (a, b) = some (c, d)` → `obtain ⟨rfl, rfl⟩ := by simpa using h`.  A `rfl`
  pattern eliminates the *right-hand* variable when both sides are variables: on
  `(xa', hx') = (xa, hx)` it removes `xa`, `hx` and the later steps no longer find them.  Where
  EC keeps the left names: `obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst xa' hx'` (`subst x` removes
  `x`).
* `omega` does not see through `abbrev handle := ℤ` ("No usable constraints"): use `linarith`,
  and `ne_of_lt`/`.ne` for `≠`.  In `rw [FMap.get_set_neqE _ _ _ _ (by tac)]` the keys are still
  metavariables when `tac` runs: name them, `FMap.get_set_neqE _ x y _ (by tac)`.
* EC's `proc *` is `equiv_proc_to_stmt`.  EC's `have->: Pr[…] = Pr[…]` is `have h : … := by …`
  then `rw [h]` (`rw [show … by …]` sees the `Pr[ … ]` before it is elaborated).
* A lemma over EC's `A <: Adv` (no restriction) applied to a concrete game: the game's
  `Module.Declared _ ⊥` is `⟨by fp_finite, by fp_disjoint⟩`; `fp_finite` needs an `@[fp_bound]` for
  a module family with a Lean parameter inside the game (`DRestr D`: `fp_module C.c`, the
  variables it adds as the tactic's argument).
* `byphoare Hl` with `Hl : islossless p` (EC's `phoare[ p : true ==> true ] = 1%r`) closes
  `Pr[ p (a) @ &m : true ] = 1`.
* EC's `smt` sees through the section's `op`s (`(<=)` on maps in Gconcl_list) and `oget`;
  `grind` does not: give `smt_close` the definition (`smt_close [FMap.domE, «<=»]`) and, for
  `oget m.[x]` with `x \in m`, EC's `FMap.get_some`.
* `rewrite xorwA xorwK xorwC xorw0` → the same `rw`, with EC's names from `Lib/EC/BitWordRing`
  (import it, `open GaudisCrypt.EC.BitWord (xorwA xorwK xorwC xorw0)`).
* `smt (@Block.DBlock …)` for losslessness → the `@[simp]` facts `bdistr_expected_one` etc.
  (state them once per file/library, `is_lossless_iff_expected`).
* EC's `smt()` on real arithmetic → `smt_close` (linear, since 2026-11-16), else
  `linarith`/`positivity`; bounds: `Lib/EC/StdBigop.lean`
  (`sum_Ico_const`, `sum_Ico_toNat`, `ofReal_intCast_mul_mu1`).
* `sp` gives EC's read form `P ∧ x = e`, and past the resets inlining leaves it keeps `P` and
  forgets the reset (EC has no such statement).  Over `x <- e` with `e` reading `x` it gives EC's
  `∃ v, P[x:=v] ∧ x = e[x:=v]` (`X.set v σ` inside reads); `equiv_elim*` names `v` as EC's
  `elim *`, and `auto_prep` turns the rest into plain values.  Hand closers written against the
  older `∃ τ, … σ = X.set … τ` form name hypotheses positionally (`rename_i`): recompute them
  from `trace_state`.  If a precondition shows `∃ τ, … σ = …set… τ`
  instead, `sp` could not show `P` unchanged by some statement: that is an infrastructure gap
  (seen: `decide` instances, `True` side goals), not something to work around in the proof.
* `hoare_auto`/`hoare_skip` lose the link when the precondition still mentions the state outside
  reads (`∃ τ, … σ = x.set … τ`): use `intros; apply hoare_skip_of_imp; auto_prep;
  generalize_reads_all; subst_vars; omega`.

## 6. Performance

* `maxHeartbeats` is **per declaration**: `set_option maxHeartbeats N in` + a `--` comment on why
  (EC's long lemmas need 1M–8M).  An `inline*`/`simp` "nested timeout" means the budget is gone.
  Heartbeat timeouts are not caught by `try`/`first`.
* `sim` propagates relations backwards and blows up through nested `if`s.  **Where `sim` is slow,
  replace it with explicit `stmt_wp`/`equiv_call`/`stmt_sp`/`stmt_if`** (Denis, 2026-11-07),
  noting the deviation; don't raise budgets for it.
* `equiv_auto` with a big invariant (`INV_CF_G1`) through inlined code is the most expensive
  step: weaken the postcondition first (`equiv_conseq (: _ ==> §G1.bext{2})`) when the branch
  only needs the bad flag.
* Drop EC's **no-op** `wp`/`sp` (one with a loop on one side timed out at 4M).
* Disjointness of two named globals costs ~150–400 ms of instance search; big restriction lists
  and many module variables add up.  `module_subtype` coercions are duplicated by the `module`
  command's generated proof (`procApply`): callees like `A(FBounder(F(P)), PBounder(P))` need
  ~400k (SecureHash).
* Many variable pairs in restrictions (`{-PRPi, -ARP, -DBounder}`): `set_option
  synthInstance.maxSize 1024 in`.
* Probing a large goal: `trace_state` + `lake env lean file | grep` (the LSP may choke);
  `#count_heartbeats` misses async elaboration (`set_option Elab.async false in`);
  `lean_profile_proof` fails on same-file modules — use `set_option profiler true in`.
* **Declare local tactic macros (and any `syntax`/`notation`) before a file's heavy proofs**, not
  at their first use: a syntax declaration waits for every proof before it to finish (its parser
  is run at once), so one in the middle of a file splits it into stretches elaborated one after
  the other (`Gconcl_list`'s six macros, 2026-11-19).  `module`, `def`, `instance`, `global_var`
  do not wait.  Hygienic macros resolve names where they are declared: after what they name.
* Measuring: `-Dprofiler=true -Dprofiler.threshold=1000` (per kind), `-Dtrace.profiler=true
  -Dtrace.profiler.threshold=500` (per declaration and tactic, wall time),
  `trace.profiler.useHeartbeats` (work rather than waiting); a slow step with no slow child: time
  its parts in a scratch file importing the built module (`run_tac` with `IO.monoMsNow`).
* Long proofs: `sorry` the later bullets while working on early ones; files outside the barrel
  are checked with `lake env lean`.  For one bullet of a long proof, work in an uncommitted
  scratch copy of the file with every other bullet `sorry`'d (`GcolScratch.lean`: 7 s per
  check against 2.5 min for `G1_col` whole), then paste the bullet back.

## 7. Known limitations and standing deviations

Document each in the docstring when it applies.

* **Inliner renaming**: an inlined callee's locals that clash with names in the conditions are
  renamed (`p`, `sa` → `p0`, `sa0` on side 2): EC's `={sa, p}` becomes `§sa{1} = §sa0{2} ∧ …`.
* **`rename_i`** for EC's positional intro names; `rcases h : e` for `case @[ambient]`.
* **E11**: the EC-form up-to-bad call `equiv_call (_ : bad, I, J)` wants the right oracles
  lossless everywhere (one more `islossless` goal each, CF_G1).  (`Exceptions.md` E11 describes
  the older `prhlProc_abstract_call_upto` rule, whose oracle premises are Hoare triples.)
* **E13, E14** will recur in Gconcl, Gconcl_list, SHA3Indiff, SHA3(O)Security: variables of
  local games fresh for `D` by hypothesis (`Gext0Fresh`), `D_ll` over a region rather than
  `glob D`.  Read them before porting those files.  E13 is `declare module`'s restriction list
  (the local games' modules named in it).  E14 is `declare module … with glob R` (§2): it stays
  an exception, in two lines per section.
* **Clone ops given as functions** (`op dout _ <- bdistr`) stay applied in our code
  (`r <$ F.dout x`), but `stmt_swap` sees such a distribution as constant (equal up to reducible
  unfolding), so EC's swaps go through.  Moving a statement to an earlier position past
  inlining's resets takes the resets along (they go first; EC has none), so a sampling of a
  callee's local can move past that callee's reset.
* **EC's `auto` couples the last samplings of both sides, and only same-type ones** — ours falls
  back to a one-sided `rnd` when the last samplings differ in type, so where EC's `auto` stops
  before a `swap` (types differ), write that `auto` as `stmt_wp`, then EC's `swap`, then
  `equiv_auto`.  For the same reason EC's `auto;rnd{1};auto` is one `equiv_auto` here (Gconcl
  `G2_G3` `S.f`: `wp;rnd;auto;rnd{1};auto` → `stmt_wp; equiv_rnd; equiv_auto`).
* **`fel`**: the oracle form takes one oracle (Gext needs two); `bad` must persist (`keep` goal);
  the call last.  The inner-procedure form (`[M : pre]`) takes any number of procedures, the
  oracles of a product module type, and EC's event `bad ∧ cntr ≤ q`.
* **`rw`** fails on goals with terms well-typed only by unfolding module types (`PRIMITIVE.f Perm`
  at a PRP type): use `simp only`.  Module types are not reducibly equal (making `moduletype`'s
  types `@[reducible]` is proposed, not done); instances like `Module.GlobBound` must be stated at
  the module type the lemmas ask for.
* **`@D_ll _ ?_ _ ?_`**: restriction holes of declared axioms are spelled out in `phoare_call`.
* **Regions**: `={glob A, glob B}` is one region (no join lemma — never split it); EC's
  `call (: true)` on init code is `equiv_call (_ : ={glob D, glob P})`.
* **`seq`/`proc` counts** match EC only with the EC tactics (`*_proc`, `equiv_seq`); the
  `*_proc_to_stmt` and `equiv_seq_last` forms are older and count differently.
* **Missing** (counts over the files still to port): Hoare `seq n : P`; `rnd f g` (~14);
  procedure-level `transitivity` (2) and `proc (I)` on abstract procedures (4); clone `realize` /
  `proof x by` (~20) and `rename` (6); multi-oracle `fel` (Gext); two-judgment
  `conseq (: _ ==> true) (: _ ==> Q)`; `sim` over abstract calls with differing oracles (use
  `equiv_call` with the invariant); `bypr` (2; E12).  Not used there at all: `ecall`, `eager`,
  `fission`/`fusion`, `cfold`, `kill`, `outline`, `exlim`, `byupto`, `rewrite equiv`.
* **Old-port declarations**: lemmas ported in EC form *over the old declarations* (Handle's
  `eq_f`) carry artifacts (`unfold CF`, `module_subtype SLCommon.PRIMITIVE <: DPRIMITIVE`, old
  invariant forms); they vanish when the declarations are re-ported.
* Closer scoping: `equiv_auto` uses `equiv_skip_ec` (decide-instance normalization, renamed-state
  fold); plain `equiv_skip` keeps the old behaviour that old hand-written proofs rely on.  Use the
  EC tactics in new proofs.

* **After `inline*`, the callee's parameter assignment comes first** (`x0 <- x`), where EC's
  inlined code starts with the callee's first statement: before EC's `if`, a `stmt_sp`.
* **A lemma `∀ (F <: T {-X}), …` at a concrete module** (EC's `equiv_sim_f IRO`): the
  declaration by hand, `@lemma _ _ _ M ⟨by fp_finite, by fp_disjoint⟩` (the leading `_`s are the
  section's instance parameters).  Its `={glob F}` is then `M`'s footprint region, read as EC
  does, `={M's variables}`, when `M` is a module of procedures touching only the globals its code
  writes (`Logic/GlobWrites.lean`: `fp_writes` finds an assignment, `globTuples` rewrites
  `={glob M}` both ways; SHA3Indiff GAP 3).  Not yet for a functor (`G2(DRestr(D))` before its
  oracle is applied: Gext GAP 8), nor for a variable `M` only reads.
* **Inlined callees' locals are renamed per side** (`x3, n0` against `x0, n`), as in EC: `sim`
  pairs the locals at corresponding positions of two loops (EC's equality set of pairs), so EC's
  `sim` stays `sim` (since 2026-11-21).  What it leaves is EC's: the precondition's implication
  (`ec_close`, or `smt_close [lemmas]` for EC's `sim; smt(lemmas)`).  It still stops where the
  relation after the loops relates differently named variables through terms (`f x0{1} =
  f x1{2}`): there `equiv_while` with EC's equality set (SHA3_OIndiff GAP 2).
* **A probe that leaves a goal behind** (`sim` then `trace_state`, nothing closing the rest)
  fails as "don't know how to synthesize placeholder for argument `h`" at the tactic that
  created the goal (`equiv_conseq`, the rule's argument), not at the probe.
* **`byequiv`'s precondition through `sp`**: the two memories' equation with the initializations
  written over them; `glob D`'s equality by hand, `congrArg` of `glob D`'s getter then
  `simp (disch := fp_disjoint) only [touched_set_of_le_compl]` (SHA3Indiff GAP 4).

* **`rcondt{i} n` / `rcondf{i} n` on a `while`** (Gconcl_list `ideal_equiv`): as EC, the loop
  unrolled first — `rcondt` leaves the body before the loop (EC's later positions count the body's
  statements), `rcondf` removes the loop.  `splitwhile` then `rcondt` on the second loop and
  `rcondf` on the spliced `if`, then on the loop again, is EC's usual last-round peel.
* **`hoare_while I` (and `hoare_while_raw I`) needs the loop last**: EC's `while` side goals after `rcondt` on a loop end
  with the spliced round's head (`i <- i + 1; …`): `stmt_wp` first (deviation).
* **`call (: ={glob IF, glob S, glob A} ∧ …)` with concrete modules**: `equiv_call` reads each
  `glob M` of a module of procedures as its written variables (`Logic/GlobWrites.lean`), exactly
  EC's goals.
* **EC's `smt` selects lemmas itself** (`domE`, `mem_set`, `get_setE`, the definition of an `op`
  such as Gconcl_list's `<=`): `smt_close` takes them in its list (a definition by name unfolds).
* **Tuple equations from `sp`** (`(bl, nb) = x`, or a chain `(p, n) = x0`, `x0 = (bl, nb)`):
  `auto_close` does not use them (GAP 1 of Gconcl_list): `intro σ₁ σ₂ h; simp_reads_all;
  smt_close []`.  (A rule for them in `subst_reads` was tried on 2026-11-12 and taken out: it
  broke `smt_close` steps in `SHA3Indiff.lean` and shifted `SmartCounter/Handle.lean`'s `rename_i` names.)
* **`hoare_auto` after `sp`**: its `skip` simplifies the reads through writes before it
  generalizes the reads (2026-11-12); the goals it leaves have no `True ∧` and no state binder
  when nothing reads the state.
* **Every pilot file is in the barrel** (`GaudisCrypt.lean`), also unfinished ones: a file outside
  it is not checked by the full build (`SHA3Indiff.lean` broke unnoticed that way).

* **A warning `tac: … (ECReport.fallback)` is a gap, not noise** (2026-11-13): the tactic could
  not do the step as specified and continued another way (`the reads are not generalized`: the
  goal stays about the states; `using the rule without a frame`; `sim: no equality set for the
  call`).  `set_option ec.strict true in` makes it an error; `set_option trace.ec.frame true in`
  lists what a frame keeps and drops.  The frameless call rule by name: `equiv_call_frameless`.
* **Golden tests** (`Logic/ECAutoTest.lean`, `ECCloseTest.lean`, `ECRulesTest.lean`,
  `ECCallsTest.lean`): a tactic change that changes an output fails there first;
  `scripts/update_golden.py FILE` refreshes the expected text — its diff is the record of the
  behaviour change.  A tactic change comes with a golden test of the new behaviour.

* **`call (_ : I)` on an abstract module, `I` without a `={…}` part** is `equiv_call (_ : I)`
  (2026-11-13; before, only `={…}` and `={…} ∧ I` were taken): `glob D` is kept without being
  named, the oracle goals are `={arg} ∧ I ==> ={res} ∧ I`.  Writing `={glob D} ∧ I` instead
  gives the form in which the oracles must keep `glob D` themselves — not EC's.
* **A statement over the first port's modules** names the parameters at the triple
  (`equiv[ M(P).f (x) ~ N(P).f (x) : ={glob P, x} ==> … ]`); an abstract `P` that is called
  needs a declaration even with no restriction: `∀ (P <: DPRIMITIVE {})`.
* **A module with more procedures than its module type** (`HybridIROLazy : HYBRID_IRO` with
  `fill_in`): declare the type's procedures as the module type's accessors of the module
  (`abbrev HybridIROLazy.f := HYBRID_IRO.f HybridIROLazy`), not as the module's own procedure.
  A call of an oracle `HI.f` names it in that form, so EC's `inline HybridIROLazy.f` and
  `conseq L` after an abstract call fit as written; `equiv_proc` opens it.  After `equiv_conseq L`
  come its two implications when the conditions are not literally `L`'s (`Sponge.lean`,
  `conseq_side`).
* **`phoare … = 1` with code behind a loop** (EC: `…; auto; while (true) (n - i); auto`).
  `phoare_auto` passes the trailing assignments and samplings; a sampling leaves
  `d.expected fun _ => 1` as the postcondition, and `phoare_while` wants `1`:
  `phoare_auto; simp only [cdistr_expected_one]; phoare_while True ((§n - §i).toNat)`
  (`Gconcl_list.Ideal_lossless`).  The body's variant step is one lemma (`variant_decr`).
* **Splicing a finished lemma into a file**: put it before the next declaration's
  `set_option`/comment/docstring header, not after the last blank line before `theorem` — a
  docstring may contain a blank line, and block comments nest, so a block pasted inside one
  disappears without an error.
* **`transitivity N (P₁ ==> Q₁) (P₂ ==> Q₂)` on procedures** (`Sponge.lean`,
  `HybridIROEagerTrans_BlockSpongeTrans_next_block`): no tactic yet, the rule is
  `prhlProc_trans_ec` (`Logic/ECTrans.lean`).  State the judgment EC proves in place as its own
  lemma, then `refine prhlProc_trans_ec ?_ ?_ h₁ h₂`.  The two side goals are over the parameter
  tuples: `rintro ⟨xs, i, m, bs⟩ g₁ ⟨x, i', bs'⟩ g₂ ⟨…⟩`, restate each hypothesis in reduced form
  (`replace hi : i = i2 * r := hi`), give EC's `exists` witness as the tuple and the globals.
* **A first-port fact about a `module`-declared procedure** is stated with `X.f.procedure`; the
  judgment syntax `equiv[ X.f ~ … ]` reads `Module.Proc.procedure X.f`, and `exact` does not see
  through it.  Restate once:
  `rw [← show Module.Proc.procedure X.f = X.f.procedure from Module.procedure_proc _] at h`.
* **`call L` where `L` is `true ==> ={res}`** in code that still has other state:
  `equiv_call (_ : True ==> ={res})`; goals `callee` (`exact L`), then the code before.
* **`while{i} I V` whose invariant reads an unmodified variable the postcondition does not**:
  the exit goal frames only the postcondition's reads, so the variable's final value is not
  tied to the initial one.  Add the missing fact to the preceding `conseq`'s postcondition
  (marked as a gap) rather than changing the invariant: with an invariant that reads the other
  memory the strict `auto` on the loop body runs out of recursion depth (`stmt_wp; hoare_skip`).
* **`elim n'` on a procedure judgment** (`move: ge0_n'; elim n'=> [| n' ge0_n' IH]` after
  `proc`): `equiv_proc` first, then `induction n', ge0_n' using Int.leInduction with | base => …
  | succ n' ge0_n' IH => …`.  `IH` is about the two bodies, so EC's `conseq IH=> //` is
  `equiv_conseq IH` with `ec_close` on its two implications
  (`Sponge.lean`, `HybridIROEagerTrans_BlockSpongeTrans_loop`).
* **The middle memory of `transitivity{i}`** (EC: `progress; exists M.mp{1} n' xs{2}=> //`):
  when it is one side's memory, `exact ⟨σ₁, …⟩`; when a variable differs,
  `refine ⟨(localVarLens "n" ℤ).set n' σ₁, ?_⟩; simp_reads; exact ⟨…⟩`.
* **`call (_ : ={M.x})` on a concrete procedure** uses the rule with EC's frame, which needs the
  callee's footprint: state it once, `@[fp_bound] theorem fvP_M_f : FVP.fvP M.f ≤ M.x.footprint
  := by fp_module M.x`.  The callee's own goal is then closed by the tactic.  `call (_ : true)`
  in a Hoare goal (`rcondf` side goal): `hoare_call (: True ==> True)`, goals `spec`
  (`hoare_proc; ec_auto`) and the code before.
* **`(bs, i) <@ M.f(…)` in `transitivity` code**: `bs, i <- call (M.f).procedure (…);`.
* **A leaf where the strict `auto`/`equiv_skip` fail with "maximum recursion depth"** on a
  `skip ~ skip` goal (seen with `bs{1} = take n1 bs{2}` next to `={bs}`): don't raise limits;
  `refine prhlStmt_skip ?_`, `rintro σ₁ σ₂ ⟨…⟩` and build the conjunction with lemmas that work
  up to `rfl` (`hin.ge`, `congrArg₂ take hsz hbs`, …), since the conditions are not in read
  normal form there.
* **`wp; rnd; auto; progress` where the strict `auto` fails with "maximum recursion depth"**
  (two-sided loop body whose invariant has quantified conjuncts over a map that the body sets;
  `SHA3Security.lean`, `equiv_ro_iro`): `equiv_rnd; equiv_skip; ec_progress` gives EC's
  bullets (the trivial ones closed).  The one-sided side goal of `rcondt{2} 1; 1:auto; progress`
  there: `intro σ₁; hoare_skip; rintro … ⟨…⟩` and EC's argument by hand.
* **Bullets after `ec_progress` have anonymous hypotheses**: cite them by statement
  (`‹same_ro m₁ mp›`, `‹∀ l j, mp.dom (l, j) → mp₂.dom (l, j)› _ _ ‹_›`).  A witness left as `_`
  in an anonymous constructor is not found by `‹0 ≤ _›` (the goal still has the metavariable):
  `refine ⟨_, ?_, ?_, h⟩ <;> assumption`, the component that fixes it given as a term.
* **`rw [lemma …]` whose instance is stated on a class field** (`Params.spec_dout r` is about
  `Params.to_list`, the goal about the operator `to_list`): the pattern is not found; state the
  fact first at the operators (`have ht : take size_out (to_list r) = to_list r :=
  take_oversize _ _ (le_of_eq (Params.spec_dout r))`) and rewrite with `ht`.
* **`Sample.sample` / `LoopSnoc.sample` of EC's theory `Program`**: not modules here.  A
  `transitivity` through them is one `equiv_trans{1}` through the first port's
  `Prog.LoopSnoc.sample` call, first leg `Pilot.SHA3Security.Preimage.dout_LoopSnoc` (E12).
* **A theory's lemma applied to concrete modules** (`SHA3Security.ec`:
  `rewrite (preimage_resistant_if_indifferentiable A A_ll (CSetSize(Sponge)) Perm &m ha init_ha)`,
  `exists (SimSetSize(Simulator))`): give each concrete module its globals once, at the module
  type the lemma asks for — `@[fp_bound] theorem fvP_M : @FVP.fvP T _ M ≤ x.footprint ⊔ …` and
  `instance : @Module.GlobBound T _ M (x.footprint ⊔ …) := ⟨fvP_M, by fp_finite⟩` (a bound `⊥` for
  a module without globals).  Then the restrictions are found by instance search:
  `refine S.lemma A (CSetSize Sponge) Perm m ha init_ha ?_` and
  `refine ⟨SimSetSize Simulator, inferInstance, ?_, ?_⟩`.  (`synthInstance.maxHeartbeats 400000`,
  `synthInstance.maxSize 1024` on the lemma.)
* **A clone's game over modules of another module type** (`Indiff0.GReal(CSetSize(Sponge), Perm,
  D)`, the modules declared at the sponge's types): the game applies them at the clone's types,
  where `inline` and call lemmas stated at the sponge's types do not see them.  State once that
  the two are equal, by `rfl` (`theorem M_init (C : Indiff0.CONSTRUCTION) (P : Indiff0.PRIMITIVE)
  (hC : C = CSetSize Sponge) (hP : P = Perm) : «C»(P).init = CSetSize(Sponge, Perm).init := by
  subst hC hP; rfl`), and rewrite right after `proc`: `erw [M_init _ _ rfl rfl, M_f _ _ rfl rfl]`.
* **`byequiv` where the proof needs a fact about `&m`** (EC's inferred precondition knows the
  memory): `byequiv (_ : §allGlobals{1} = §allGlobals{2} ∧ §DPre.h{1} = ha ==> ={res})`; the
  side goals are closed from the hypotheses.
* **EC's list of procedures to `inline` in front of an adversary's call** (paths over the first
  port's views do not elaborate): `repeat stmt_inline{1} 0; repeat stmt_inline{2} 0`, which
  inline call site by call site and stop at the abstract call; then EC's `sp`, `wp`.
* **`exists* x{1}; elim* => m c1 c2 b1 b2` after `sp`** (EC names `sp`'s old values): name what
  the next step needs, `equiv_exists* §x{1}, §Cntr.c{2}; intro m c1`.
* **`conseq (: _ ==> Q)` in front of an abstract call** does not keep a global that the callee
  does not write (EC's does, from the restriction): carry the fact through the call's invariant.
* **`rcondt{i} n; first by auto; inline*; auto; conseq (: _ ==> true); auto`** where statement
  `n - 1` is a call that does not write what the condition reads (the game's counter past
  `F.get(m1)`): `stmt_rcondt{i} n` then, for the side goal,
  `intro σ; hoare_call (: True ==> True) / SRO.Counter.c; ec_auto` (`Logic/ECCallFrame.lean`:
  the Hoare call with EC's frame; the trivial triple about the callee is closed).  Where the
  condition is about the other side's copy of the counter, two more lines relate the two.
* **A branch that both sides leave with the same constant** (`b <- false` after a call, EC:
  `auto; inline*; auto; sp; conseq (: _ ==> true); auto. if{2}; sp; auto; sim.
  while{1} (I) (v). …`): after `stmt_wp` the postcondition is `True`; `stmt_inline*; stmt_sp`,
  `equiv_conseq (: _ ==> True)`, `stmt_if{2}`; where both sides run the same loops, EC's `sim`
  is `equiv_while` on each loop with the equalities; where one side runs alone,
  `equiv_while{1} (I) (v)` with its three goals (`while_ll_phoare` for the body's losslessness,
  the body's triple `intro σ₂ k; hoare_auto; ec_progress`, the code before).  The variant is
  stated with the loop's own bound (`§n{1}`), not a value known from before the loop (GAP 4).
* **A section that repeats another's script** (`Collision` after `SecondPreimage`): derive it
  from the finished one by renaming, compile, and fix what the games' differences change (the
  pre goals; `seq` counts where a pair assignment is two EC statements and one here).
* **`islossless` of a game with the adversary's call in the middle** (EC: `seq 1 : true; auto.
  + call (A_ll (O) _); auto. …`): `phoare_proc; phoare_inline*; stmt_sp; stmt_wp;
  phoare_seq_lossless 1 : (True)`, then `phoare_call (@A_ll _ ?_ ?_)` (goals: the code before,
  the oracle's `islossless`; the restriction hole is closed) and the rest (`stmt_if; …`).
* **`inline M.f; sim` when `M.f` has a loop**: `sim` does not pass the copies of the
  parameters; `stmt_inline{i} (M.f); stmt_sp; stmt_wp; equiv_while (…)` with the equalities
  between the caller's variables and the copies (`§xs{1} = §xs0{2} ∧ …`).
* **Guards after `splitwhile`**: the equality of the two loops' guards that `while` asks is a
  small arithmetic fact about `decide`s; state it once as a private lemma
  (`splitwhile_guard_left`, `_right`, `_le` in `Sponge.lean`) and close the leaf with it.
* **An abstract simulator** (`declare module S <: SIMULATOR {…}`, a functor with several
  procedures; `Sponge.lean`, final section).  EC's module type lists each procedure's
  oracles; state them once as a section hypothesis (`variable (S_rep :
  SIMULATOR.Representable … S)`, `include S_rep in` on the lemmas that use it).  Then:
  `call (_ : true)` on `S(F).init` is `equiv_call` of a small lemma from `SIMULATOR.call_init`
  (`BlockSim_init_call`), followed by `simp only [Setter.throwaway_set]; ec_auto;
  simp (disch := fp_disjoint) only [touched_set_of_le_compl]; ec_close`; `proc (I)` on `S(F).f`
  is `equiv_proc (I)`; `RaiseSim(S, F)` is `S(LowerFun(F))` after
  `simp only [RaiseSim, Module.app_comp]`.
  `call (_ : I)` on `S(F).init` as the last statement is `equiv_call (_ : ={glob M, …} ∧ I)`
  with `SIMULATOR.call_init` tagged `@[proc_inv]`.  **No `swap` past `S(F).init`**: its footprint
  as code is not known (only its behaviour); leave the statements where they are, `stmt_wp`
  the assignment after the call on the other side, and put what the swap would give into the
  call's invariant (`§mp{2} = FMap.empty`).
* **`sim` on `D(F, S(G)) ~ D(F, S(G))` with a `glob` region and a variable in the
  precondition** fails ("no equality set"): `stmt_wp; equiv_call (_ : ={glob S} ∧ §x{1} =
  §x{2})`, then `equiv_proc (§x{1} = §x{2}); equiv_proc; sim` for the simulator's oracles, and
  for a concrete oracle `have H : equiv[ F.f (x) ~ F.f (x) : ={x, X} ==> ={res, X} ] := by
  equiv_proc; sim` then `equiv_conseq_frame H`.
* **`inline*; sim n m; sp` at the start of a game** (`SHA3_OIndiff`): EC's positions do not
  count our inliner's `reset_vars` statements.  Use `stmt_inline*; stmt_wp` (the assignments
  after the distinguisher's call), leave the initializations before the call, and close the
  last goal with `ec_auto; simp (disch := fp_disjoint) only [touched_set_of_le_compl]; ec_close`.
  `sim` in front of a conditional (EC: `sim; if; …`) is `sim 1 1` (the code after it).
* **Probing a long script cheaply**: write every leaf as
  `first | (ec_close; done) | (trace "name"; sorry)` (or with `ec_auto`, `ec_auto; ec_close`),
  compile once, read which names were printed, then replace each `first` by the alternative
  that worked.  Never `simp_all` on a goal after `sp`: it can eat the whole budget.  An operator
  that EC's `auto` unfolds (`increase_counter`) is unfolded once after `inline*`
  (`simp only [increase_counter]`); the closers do not unfold definitions.
* **`equiv_call (_ : ={glob M} ∧ I)` must not be parenthesized**: `(_ : (={glob M} ∧ I))` is
  read as an invariant without a `glob` part and fails ("the conditions read … which is not a
  global variable").
* **No frame where one is expected** (`call H`, `conseq H`: the goal after it asks `={glob M}`
  or a variable for arbitrary final globals): the footprint of a concrete callee is not known.
  Since 2026-11-17 `fp_le` reads a `module`'s or a `module`'s procedure's footprint off its code
  (`ModuleFootprint.cachedBound`, as `fp_disjoint` did), so a named concrete callee needs nothing
  stated.  State it (`@[fp_bound] theorem fvP_X_f : FVP.fvP X.f ≤ X.mp.footprint := by fp_module
  X.mp`) only where that fails (a module with more than one abstract argument, a callee spelled
  through a record): for the procedure and for the modules it is applied to
  (`fvP_RaiseFun : … ≤ ⊥`), outside any `include R`.  A frame that now applies where none did
  changes the goal after `call`: the hand-written intro patterns after it may need adjusting.
  Since 2026-11-18 `stmt_swap` (`swap`) reads them off the code too, including a callee named
  as inlined code names it (`Module.proc M.f.procedure`); it is the only `fp_disjoint` caller
  that does so by default (doing it for every caller made Gext time out: the solver then tries
  the code of every module it meets before the stated bounds).  A stated bound that only
  `swap` needed can go; one that a slow file needs for speed (Gext's procedure group) stays.
* **Side goals over parameter tuples and results** (`prhlProc_trans_ec`, `equiv_conseq_pre`,
  `equiv_conseq H` on procedures): the variables have the signature's types
  (`typeListToTuple [ℤ]`, `(procsig …).ret`) and the conditions are unreduced reads, so `omega`
  and `rw` do not see them.  Introduce at the plain types
  (`intro (n1 : ℤ) (xs' : List block)`, `rintro ⟨xs, (n : ℤ)⟩ g₁ … (r₁ : List Bool)`), restate
  each hypothesis (`replace hn : n = n' * r := hn`) and `change` the goal.  A middle memory that
  mixes the two sides' globals: `M.x.set (M.x.get g₂) g₁`, with `Lens.set_get` and
  `Lens.get_of_disjoint_set`.
* **`omega` after a loop fails with two atoms that print the same** (the guard's read of a
  local and the invariant's): combine the two hypotheses by a lemma instead
  (`le_antisymm t2 hg`), which works up to `rfl`.
* **A name that is not a variable of the side** (`SHA3OSecurity` `eq_eager_ideal2`): the
  tactics resolve `§x{i}` from the statement and the conditions; a callee's local whose name is
  also a variable of the other side or of the precondition at another type (`x1`{1}, `x0`{2}
  after `inline*; sp`), and a variable the statement no longer mentions (`k` after `wp`, in
  `splitwhile{1} 1 : i < k`), give "Unknown identifier".  Write them with their lenses:
  `§(localVarLens "x0" (List Bool)){2}`, `§(localVarLens "k" ℤ)`.
* **An adversary of one clone given a module of another's module type** (EC's module types are
  structural; `SH.AdvPreimage` given the sponge's primitive by the first port's `ODRestr`):
  `equiv_proc` on the oracle says "no concrete procedure body: nothing to unfold at the head of
  `ODPRIMITIVE.f (… .mk …)`".  State the projection once at the clone's name, by the clone's
  own `mk_simp` (`theorem ODPRIMITIVE_f_mk (f fi) : SH.OIndif.ODPRIMITIVE.f (….mk … {f, fi}) = f
  := SH.OIndif.ODPRIMITIVE.f.mk_simp {f, fi}`; `rfl` does not prove it, the two `Structure`s
  differ), and use it by `simp only [ODPRIMITIVE_f_mk]` in front of `equiv_proc`.  `rw`/`erw`
  do not find it: the clone's name is a reducible alias of the theory's constant, which `simp`
  unfolds and `rw`'s matching does not.
* **EC's chains `inline{1} 1; inline{2} 1; sp` down to an adversary's call**:
  `repeat stmt_inline{1} 0; repeat stmt_inline{2} 0; stmt_sp` (each stops at the abstract call);
  one `stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp` per EC line where swaps come in between.
  `stmt_swap [a..b] k` on a relational goal takes a side (`stmt_swap{1} [1..2] 3;
  stmt_swap{2} [1..2] 3` for EC's two-sided `swap[1..2] 3`); `stmt_swap k` does not.
* **EC's `call (RO_LRO_D D _)`** for a clone of `FullRO`: state the clone's `RO_LRO_D` once,
  its side conditions as auto-params (`hD := by ec_module`, `hdisj := by fp_disjoint`), as in
  `SecureRO.lean` and `SHA3OSecurity`'s `Eager.RO_LRO_D`; then
  `equiv_call (Eager.RO_LRO_D (Dist A))`, with `Dist A` taking `RO_Distinguisher`'s `unit`.
* **`equiv_call (_ : ={x₁, …})` on a declared adversary** gives EC's oracle judgments,
  `={arg, x₁, …} ==> ={res, x₁, …}`, without `={glob A}` (since 2026-11-21; before, the
  postconditions read `glob A` over written memories and `stmt_inline` did not end: invariants
  were split in two parts, `SHA3OSecurity` GAP 5).  Write EC's set as it is.  With another
  declared module's `glob` in the set, the oracles keep that region, `glob A` with it.
* **A call keeps the other variables only if the callee's footprint is known at the call's
  spelling**: after `equiv_call H` the goals `X.get g₁ = X.get g₂` for arbitrary final `g₁`,
  `g₂` mean the frame was empty.  State `@[fp_bound] theorem … : FVP.fvP (SORO.RF_T.get
  RFList) ≤ RFList.m.footprint := by fp_module RFList.m` for the callee as the call prints it,
  and for the modules a framed `hoare_call` goes through (`fvP_SORO_Bounder`, `fvP_RFWhile`);
  "fp_disjoint: no restriction hypothesis for FVP.fvP {…}" names the module that lacks one.
* **EC's `have ->: Pr[…] = Pr[…]`**: `have h : … := by …` then `rw [h]; clear h`.  Left in
  context, the equation costs every later `simp_all` a pass through its two games.
* **`byequiv` on `Pr[…] ≤ Pr[…]`**: the events' implication (`hE`) is closed by `byequiv`
  itself, as EC's `=> //` (2026-11-15; before, `case hE => exact fun _ _ _ _ h => h`).
* **Probing leaves under a stubbed context**: a lemma made of several `have`s is compiled one
  part at a time with the others' proofs replaced by `sorry` (saved to files and put back by
  script); heartbeat budgets are per declaration, so the assembled lemma needs the sum.
* **A game of a clone applied to modules of another module type** (`SH.Preimage(A, OSponge,
  PSome(Perm))`; EC's module types are structural): `inline` stops at the clone's projections
  and coercions.  Put the game at the modules' own types right after `proc`, by lemmas that
  hold by `rfl`: the coercion (`OPRIMITIVE_coe_eq`, by `simp only`), the composed functor
  (`OSponge_app`, by `erw`), a procedure (`PSome_Perm_init`, by `rw` after the `inline` that
  exposes it).  Three things to know: (1) state the left-hand side with the *theory's* constant
  (`@SecureHash.OIndif.OPRIMITIVE.init … SH.params P`), not the clone's alias — `rw` keys on the
  head and does not unfold the alias, `simp` does; (2) where the argument in the goal is not
  syntactically the module (`Module.app PBounder (PSome Perm)` before `inline`), give the
  lemma a variable and an equation, `(P) (hP : P = PSome Perm)`, and use it as `rw [L _ rfl]`;
  (3) `set_option pp.explicit true in trace_state` shows which of the two it is.
* **`inline*` opens callees whose locals the two sides then name differently, or at two
  spellings of a type** (`state` / `block × capacity`): the closers do not identify them and
  `sim` does not relate the loops.  Inline selectively instead (`stmt_inline{i} k`, the `k`-th
  call site, repeated: each `inline` renumbers them), so that both sides keep the same call in
  the loop bodies; then EC's `sim` applies, after `equiv_conseq (: _ ==> ={…})` to the
  equalities.  Where `sim` still does not end, `equiv_while (={…})` and
  `equiv_call (_ : ={glob P})` on the calls.
* **A theory's lemma applied to a module built from the section's adversary** (`SORO
  .RO_is_preimage_resistant (SORO_P1 A)`): state the built module's footprint
  (`@[fp_bound] theorem fvP_SORO_P1 … ≤ FVP.fvP A ⊔ (X.footprint ⊔ …)` by `fp_module` on the
  pair lens and `Footprint.lens_pair`), give the lemma's restriction as
  `have hP : Module.Declared (SORO_P1 A) S := ⟨by fp_finite, by fp_disjoint⟩`, and add the
  lemma's fresh-in-EC variables (`-SORO.Preimage.Preimage2`) to the adversary's declaration.
* **`conseq (: _ ==> Q)` in front of the adversary's call drops the variables the adversary
  does not write** (EC's keeps them; `SHA3OSecurity` GAP 8): a fact about such a variable
  (`§Dist_of_P2Adv.m{1} = mess`) goes into the call's invariant, and into the `seq`
  invariants inside the oracles.
* **`byequiv` with a fact about `&m`, one game taking a parameter**: the judgment written out,
  `byequiv (?last : equiv[ G₁.main () ~ G₂.main (m1) : §allGlobals{1} = §allGlobals{2} ∧
  §X{1} = mess ∧ §m1{2} = mess ==> (§res{1} → §res{2}) ])` (`↔` for `=`, which leaves the
  judgment only), then `case last => …` (the events' condition `hE` is closed by `byequiv`).  A fresh goal name: `?judgment`
  clashes with the earlier `byequiv`s of the proof.
* **Parameter names of a clone's game, or of a module with a Lean parameter, are not known**
  (`SH.SecondPreimage(A, …).main`, `TOTO(A).main`; "no parameter names are known for this
  procedure"): `byequiv (_ : P ==> Q)`, `byphoare (: P ==> _)` and `phoare_call (: P ==> Q)`
  cannot read `§m1` in `P`.  Write the judgment, `phoare[ M.main (m1) : … ==> … ] ≤
  (ENNReal.ofReal x)`, as the term of `byphoare (?j : …)`, `phoare_call (?spec : …)`
  (`SHA3OSecurity` GAP 9).  The written judgment also has `≤` in the form `phoare_call`
  reads: plain `byphoare`'s judgment has it as `fun x1 x2 ↦ x1 ≤ x2`, on which `phoare_call`
  fails ("the goal's relation is not `=`, `≤` or `≥`") unless a `phoare_seq` came between.
* **`byphoare`'s side goal `hx : 0 ≤ x`** (the bound is a real; EC does not ask): by hand
  where `positivity` does not see it (`(n ^ 2 - n : ℤ)` cast: `Int.le_self_sq`).
* **Two queries after the adversary's call** (EC opens both and cases on the first one's
  counter test): one after the other with `equiv_seq 1 1 : (…)`, each by EC's steps for one
  query.
* **A one-sided loop** (`while{2}` in EC): `equiv_while{2} (I) (variant)`; its goals are the
  loop's losslessness (`while_ll_phoare; intro σ₁; ec_auto; ec_progress`, then the samplings'
  `…_ll`), the body's Hoare triple (`intro σ₁ k; hoare_auto`), and the precondition.
* **A wrapped oracle in a statement** (`Bounder(RFWhile).get`): `simp only
  [SORO.Bounder.apply_simp, SORO.RF_T.get.mk_simp]` before `equiv_proc`.
* **`sim` where one side writes a variable the other does not** (`TOTO.main` sets
  `Dist_of_P2Adv.m`, then calls the game): `sim / Dist_of_P2Adv.m` (EC's `sim` with
  `={glob A}`), after inlining the wrapper's call only.  It may leave the last implication
  (reads through the calls' writes, states equal outside the variable): `intro σ₁ σ₂ h;
  simp only [Lens.equal_outside_iff_set] at *; simp_all [Lens.set_get,
  Lens.get_of_disjoint_set, ECSim.lensWriteNorm, Setter.throwaway, globals_globalL_set]`
  (`SHA3OSecurity` GAP 10).  A plain `sim` does not read equalities off an event's `↔`.
* **`sp` over a write to a global, then a call's precondition about that global** (pHL): `sp`
  states the fact as `§X.intoGlobal = …`, which the closers do not identify with `§X` (two
  values after `auto`, the goal then false).  Leave the assignment to the `auto` after the
  call (`SHA3OSecurity` GAP 11).
* **A local module that only wraps a game applied to the section's adversary** (`TOTO`):
  the adversary as a Lean parameter, `module TOTO (A : …) { … }` (with `using (A : …)` the
  `module` command's `apply_simp` proof is left unsolved on the clone's game).
* **`Countable` side conditions** of the theory lemmas (`RO_is_second_preimage_resistant`):
  an instance, `Countable f_out` from `to_list_inj`.
* **An inlined game's locals are renamed where the other side has variables of those
  names** (`Collision`: `m1`, `m2`, `hash1`, `hash2` of `Dist_of_CollAdv` against the game's
  own; they become `m10`, `m20`, `hash10`, `hash20` on the inlined side).  EC's `={m1, m2}`
  written as is then relates a variable the side does not have: nothing fails at the `seq`,
  the leaves do (a counter test about an unrelated value, `inv` goals with no hypothesis).
  Write `§m10{1} = §m1{2} ∧ §m20{1} = §m2{2}`; `trace_state` after the inlining shows the
  names.
* **A section that repeats another one** (`Collision` after `SecondPreimage`: EC's text
  differs in a few lines): diff the two EC sections lemma by lemma, generate the Lean text
  from the finished section's by the same edits (a script with exact, asserted
  replacements), and compile lemma by lemma with the others stubbed.  Five of six lemmas
  compiled on the first run.
* **The scratch file imports the pilot file**: it must not declare again what the pilot
  already has (after a splice: the section's header and the new lemma only), and it sees the
  pilot's *last built* `.olean` — lemmas spliced since then are stubbed in the scratch.
* **The scratch checker under `timeout`**: when the limit kills it, the filtered log is the
  *previous* run's (the raw log is empty).  Check the raw log's size before reading results;
  run long compiles in the background.

* **A game's oracles are written as EC's path, never as records** (2026-11-15):
  `b <- call D(FC(F), PC(P)).distinguish ();` with `module_subtype FUNCTIONALITY <:
  DFUNCTIONALITY` (and `PRIMITIVE <: DPRIMITIVE`) declared once next to the module types — also
  over module types that are abbreviations with explicit type parameters.  The coercion is the
  record a hand-written view builds, so turning `Module.app D (Module.pair (T.mk … { f := … })
  …)` into the path changes no term.  A concrete module of another module type with more
  procedures (`Perm`, a `PRP`, where a `DPRIMITIVE` is expected) gets its own
  `module_subtype (PRP …) <: DPRIMITIVE`: the record then holds `Perm`'s own procedures and
  `proc; sim` opens them (a view through an intermediate type, `PRIMITIVE.view`, does not).
* **A module of one clone's module type handed to an adversary of another clone** (EC: one
  module type; `LowerDist(D, F, P) = D(RaiseFun(F), P)`): pass it as it is.  Its procedure in an
  oracle goal is then an accessor of one clone on a module of the other, which `equiv_proc`
  opens (since 2026-11-17: `proc` and `inline` retry through the views where the plain pass
  finds no body; `module_norm` first is no longer needed).  `inline*` then also inlines what is
  behind a view (`Perm.f` behind `PRIMITIVE.view`), as EC's `inline*` does: where a proof keeps
  such a call to `call` a losslessness lemma on it, inline one call site (`phoare_inline 0`).
* **Both namespaces in one file**: in `namespace GaudisCrypt.SHA3.Pilot.Z`, `Y.name` is
  `GaudisCrypt.SHA3.Pilot.Y.name` when that exists, whatever is opened; the first port's is
  `SHA3.Y.name`.  A `simp only [Y.T.f.mk_simp]` that silently becomes the other clone's lemma
  shows up as "no concrete procedure body" at the next `proc`.
* **A theory's module variables kept in one namespace, used from another**:
  `export A.B (X.m Y.m)` inside `namespace C` makes `C.X.m` the same variable, so restriction
  lists written `-C.X.m` in other files keep reading.

* **A hygienic binder does not hide a program variable** (2026-11-15): `fun _ => r` in a
  rule's statement has the binder `x✝`, which no longer stops the printer from showing a
  program variable `x` by name (`binderClashes` compares the names as they print).

* **`swap` across the start of an inlined body** (2026-11-15): `inline` leaves a `reset_vars`
  of the callee's locals in front of the body, which EC's count attaches to the statement after
  it.  Moving a statement *earlier* past it works (`stmt_swap n -k`: the resets in the region
  jumped over go to its front first — `SchnorrPK.ec`'s `swap{1} 15 -7`, `swap 8 -7`).  Moving
  the body's first statement *later* (`hashed_elgamal_std.ec`'s `swap{1} 1 1`) takes its reset
  along, which does not commute with the next statement (it resets that statement's variable):
  `stmt_swap` fails.  Move the statement alone with our position, `stmt_swap_raw{i} 2 k`.  To
  do: a statement moved later leaves its reset where it is.
* **`call H; auto` in pHL on a lossless suffix** (EC's `call Ag_ll; auto. by call Ac_ll;
  auto=> />; rewrite dhkey_ll dt_ll dbits_ll`, after `conseq (: _ ==> true)`): the judgment is
  `phoare[ … ==> 1 ] = 1`, on which `phoare_call H; phoare_auto` computes through the code before
  the call and leaves an expectation of the earlier call; write `islossless` for the whole
  lossless part.  (On an *event*, EC's `call H; wp; rnd; call H'; auto` is ours: the table's
  row on `phoare[ c : P ==> Q ] = 1`.)

* **A path into a module without a module type that has several module parameters**
  (`SimulateHonestVerifier(S, A, D).gameIdeal`, EC's `theories/crypto/SigmaProtocol.ec`): the
  path takes all the module's parameters, as in EC; the procedure module itself is applied to
  those it uses (read off `M.apply_simp`).  A call of the module's own procedure inside its
  declaration (`b' <@ gameIdeal()`) is written with the path too, the arguments the module's
  parameters by name: `b' <- call SimulateHonestVerifier(S, A, D).gameIdeal ();`.
* **`byphoare (_: P ==> _)`, `hoare[ M.main : … ]` on a clone's game with parameters**
  (`Completeness(SchnorrPK).main (h, w')`): the parameters' names are those of the theory's
  module (2026-11-15): `byphoare (: §x = h ∧ §w = w' ==> _)`, `hoare[ Correctness(Pedersen).main
  : True ==> §res ]`.
* **A theory's operator in a development that clones it** (`R` of `SigmaProtocol`): the clone
  does not alias the class's fields; `open GaudisCrypt.EC.SigmaProtocol (R)` and `R h w` is the
  clone's (`R_DL h w` by definition).
* **A variable with one type on the left and another on the right** (after `inline*`: `x` the
  key, a group element, of `Correctness`'s inlined `gen`, and `x` the secret exponent of the
  other game; `Pedersen.ec`): two variables of one name.  `§x{i}` is side `i`'s, in every
  tactic's condition (`PRHLWp.elabRelTerm`), in a written `equiv[ … ] { var x : group; … } ~
  { var x : exp; … }` and in the goals as shown (`ProgramSyntax.frameVarsSided`).
* **Relational goals as shown (2026-11-16)**: `§x{1} = §x{2}` prints as `={x}`, a conjunction
  of them as `={x, y}` (what the parser reads it as: the printed goal can be pasted back);
  the whole global state is `={allGlobals}` (what `byequiv` states where EC shows `={glob A}`);
  `(FVP.fvP A).touched_getter` read on a side is `glob A`.  A judgment about two procedures
  that do not take the same parameters prints as `equiv[ M.f (x) ~ N.g (y, z) : … ]` also when
  a condition reads a parameter.  Still raw: the goal between `byequiv` and `proc` (a
  `prhlProc` with conditions on the tuples), `bypr`'s goal; under the `∀ τ` of a `while`'s
  second goal the reads of the exit state print as `§x`, like those of the current state.
* **`(a, b) <- (e₁, e₂)` under `sp`** leaves `(§a, §b) = (e₁, e₂)`: the closers take it apart
  (`Prod.mk.injEq`), so EC's tuple assignment is written as it is (PIR's
  `(s, s') <- ([], [])`).
* **`inline{i} M(A).f` by name where the game calls `f` through its module type** (the
  experiment's `A.guess` at `A := StdRedAdversary(L)`): `stmt_inline{i} (M(A).f)` finds the
  call (the callees are compared as the module steps evaluate them).
* **A lemma over a module and a memory** (`(U <: Unhider) &m`): one binder per quantifier,
  `∀ (U <: Unhider), ∀ m : VariableAssignment, islossless U.choose → …`; `intro U m uc_ll ug_ll`.
  `islossless` leaves the calls' goals (it closes the samplings by hint): with the hypotheses
  in the context, `islossless <;> assumption`.
* **EC's intro pattern after `auto => />`** (`=> /> x _ [c m d m' d'] /= comm comm' m_neq_m'`):
  `equiv_auto; auto_progress`, then `rename_i` for the hypotheses and `obtain ⟨c, μ, d, μ', d'⟩`
  for a call's tuple result (`simp only at … ⊢` reduces the projections).  `auto_progress` also
  leaves the cases EC's `/>` closes (a conditional's other branch): close them after.
* **`pow_bij`** (`g ^ a = g ^ b ↔ a = b`): `congrArg loge h` and `loggK`.
* **`module M : T` with more procedures than `T`** (`ElGamal : Scheme` with `dec`): as in EC;
  the module is the record of `T`'s procedures, `M.dec` a procedure of its own (2026-11-15).
  (For a procedure that must be *called through the type* by other modules, see "A module with
  more procedures than its module type" above.)
* **EC's abstract statement** (the `w` of pHL `while I V k ε`'s body goal): a variable
  `w : Stmt`, written and printed `stmt w;` inside a program.
* **`auto` on a lossless goal** (`phoare[ c : P ==> true ] = 1`, EC's `by auto=> />; exact/sample_ll`):
  with `Logic/PHoareRnd.lean` imported `phoare_auto` leaves `is_lossless d` for a sampling (the
  event rules; before, the expectation `d.expected fun _ => 1 = 1`): `phoare_auto; exact
  sample_ll`.
* **`={glob M}` for a concrete module `M`** in an invariant (`call (: ={glob Log, glob LRO})`):
  list the variables, and say `glob A`: `equiv_call (_ : ={glob A, Log.qs, LRO.m})`.  The
  oracle's judgment (EC's `1: by sim`) is `equiv_proc; stmt_inline*; equiv_auto; auto_progress`
  when `sim` finds no equality set (a cloned theory's oracle).
* **EC's local modules and the adversary's restriction**: EC keeps a `local module` declared
  after `declare module A` apart from `A`; here its variables go into the restriction
  (`declare module A <: Adv {-LRO, -Log, -Game1, -Game2, -OWr}`), else the call rules lose them
  (symptom: after `equiv_call`, a hypothesis about `Game2.r` is missing).
* **`swap` of a sampling into a global past a call of the adversary** (`swap{1} 6 -2`):
  `stmt_swap{1} 6 -2`; the oracle modules the adversary is applied to need their footprint as an
  `@[fp_bound]` lemma (`theorem fvP_Log : FVP.fvP Log ≤ Log.qs.footprint := by fp_module Log.qs`;
  symptom: "no restriction hypothesis for FVP.fvP …").
* **A lemma over `∀ (I <: Inverter {-OWr})` applied to a built module** (`rewrite (OW_OWr &m
  (I(A)))`): `I(A)` as a term is `Module.app I A`, and its restriction is an instance stated by
  hand: `haveI : Module.Declared (Module.app I A) OWr.x.footprint := ⟨by fp_finite, by
  fp_disjoint⟩`, then `rw [OW_OWr m (Module.app I A)]`.
* **Closing several goals by alternatives**: `all_goals solve | simp_all | grind`, not `first`
  (`first` takes a `simp_all` that made progress without closing the goal).
* **`smt_close` with lemmas applied to section hypotheses** (`smt_close [pr_Game0_Game1 A A_ll
  m, …]`) failed with "unknown free variable" (2026-11-15); closed 2026-11-16: EC's line as it
  is, `smt_close [pr_Game0_Game1, pr_Game1_Game2, pr_bad_Game1_Game2, pr_Game2, pr_Game2_OW]`
  (the facts form works too).
* **An abstract theory instantiated in the same file** (`br93.ec`: `abstract theory BR93 … end
  BR93.`, then `local clone import BR93 as Instance with …` and the theorem for the instance):
  the theory is a namespace with its class, the instance part a sibling namespace with its own
  class for the file's remaining operators (`op k`, `op l`, `dkeys`, `f`, …), and
  `clone import GaudisCrypt.Examples.BR93 as Instance with … proof * by first | …`.  Cloning a
  theory that itself contains clones works (`Instance.H.Lazy.LRO`, `Instance.OW_rand.OW`).
  The clone goes before the section (its variables are named in `A`'s restriction).  A
  declaration of the current namespace shadows the clone's (`I` is the instance's inverter,
  `Instance.I` the theory's; EC's `Self.I` and `I`).
* **A second clone of a theory at the same types and operators** (`clone import ROM as H` in
  the instance, and the one inside `BR93`): one module, one variable; EC's
  `H.Lazy.LRO.m{1} = LRO.m{2}` is `={LRO.m}` (in an invariant `={glob A, LRO.m}`).
* **A module variable whose type depends on an operator** (`var qs : rand list`, `rand` the
  words of length `l`): `module_var I.qs : List rand` (fixed 2026-11-15; before, a type
  mismatch between the definition's type and its body).  The type abbreviations
  (`abbrev rand : Type := BitWord.word l`) need no annotations at their uses.
* **A nested module** (`module QRO = { … }` inside `module I`): a module next to it, named
  `I.QRO`, with the outer module's parameters it uses (`A(I.QRO(H)).a1`).  **A procedure
  alias** (`proc a1 = A(H).a1`): `proc a1 = A(H).a1;` inside the `module` (since 2026-11-19,
  `notes/ModuleProcAlias.md`).  `X.a1.apply_simp` rewrites the alias to its callee, so EC's
  script sees the callee as EC's does, with no `inline`.  Older ports wrap it in a procedure with
  the one call (E5).  **EC's `call (F.FullEager.RO_LRO_D (D2(D)) _)` with `D2` such an alias**
  (`Gconcl_list.equiv_ideal`): `D2` a `module` with `proc distinguish = D(…).distinguish;`, the
  clone-level `F.FullEager.RO_LRO_D` stated once with `ec_module`/`fp_disjoint` defaults (as
  `SecureRO`'s), and EC's script as it stands: `byequiv; equiv_proc; stmt_inline*; stmt_sp;
  stmt_wp; equiv_call (F.FullEager.RO_LRO_D (D2 D)); ec_auto`.  `equiv_call` rewrites the alias to
  its callee; `ec_auto` sees the two memories equal after the same initializations.  A *call* of
  an alias is a call of the aliased procedure: `stmt_inline*` rewrites it so (and inlines further
  where that one has a body), and `equiv_proc` on an alias opens the aliased procedure, as EC's
  `proc` and `inline*` do.  Converting a wrapper to an alias removes the wrapper's inlining level:
  a script written for the wrapper loses an `inline` and its inlined locals' names shift (EC's
  names come back: `x{1}` for the port's `x0{1}`).  Rename by the program, not by guess:
  `trace_state` after the inlining shows each side's `var` list, and an inlined callee's locals are
  the ones its `reset_vars {…}` resets.  A loop invariant must name the *caller's* variable; one
  that names the callee's copy (reset and reassigned at the top of the body) fails in the closers
  with "a state is still used after the reads are generalized" (`Gconcl_list.equal1`,
  `SHA3Security.equiv_ro_iro`).
* **A wrapper around a declared adversary, passed to a lemma of another section** (`apply
  (Reduction (A_CPA(A)) _ _ &m)`): `module A_CPA (A : Adv) using (H : POracle) : AdvProcs`
  (`A` a Lean parameter: `A_CPA A` is EC's `A_CPA(A)`), `theorem fvP_A_CPA : FVP.fvP (A_CPA A)
  ≤ FVP.fvP A := by (fp_module)`, the instance `Module.ECGlob (A_CPA A) R` from it, and the
  lemma's section in the form `declare module A … with glob R` (E14).  The application:
  `refine @Instance.Reduction _ … (A_CPA A) ⟨by fp_finite, by fp_disjoint⟩ _ _
  (Footprint.Restricted.glob_declared A) ?_ ?_ m`; the losslessness goals are then about
  oracles outside `glob A`, EC's hypotheses.
* **`fp_module` as the last tactic before `set_option … in`**: write `(fp_module)` — its
  optional argument otherwise takes the next command as a term.
* **A tactic with a shorter and a longer form** (`equiv_rnd f` / `equiv_rnd f g`,
  `phoare_while I V` / `phoare_while I V k ε`): the extra arguments are on the same line or
  indented further (fixed 2026-11-15 with `colGt`; before, the short form took the next line's
  tactic as an argument: "Unknown identifier `trace_state`").
* **`conseq` and `while` in Hoare logic do not carry the precondition's facts about unmodified
  variables** (EC's `move=> &m ->` in the `post` goal): put the fact in the new postcondition
  and in the invariant (`PIR_correct`: `sxor2 §PIR.s §PIR.s' §i ∧ §i = i0`).  Open gap.
* **`big predT F s`** over a clone of EC's `Bigop`: `Lib/EC/Bigop.lean` (`big`, `big_nil`,
  `big_cons`, `big_consT`, `big_cat`); `predT` is in `Lib/EC/Logic.lean`.  A hypothesis in read
  form (`h : §PIR.s = s1 ++ s2`) does not rewrite a goal in lens form (`PIR.s.get σ.globals`):
  `have h' : PIR.s.get σ.globals = _ := h`.
* **A probability computed in pHL** (`PIR.ec`'s `Pr_PIR_s`: `case`, `conseq … : = e`, `sp`,
  the two-judgment `conseq`, `while I V k ε`, `seq … _ 0%r 0%r _`, `exists*`, `conseq H`):
  `Examples/PIR.lean` is the reference.  Start with `byphoare (: True ==> _)` where EC writes
  `byphoare=> //` (the default precondition `arg = a ∧ glob = m` makes `sp` state the memory).
  EC's `case: (P)` on a pure fact is `by_cases`.  `exists * x, y; elim * => x0 y0` is
  `stmt_exists * §x; intro x0; stmt_exists * §y; intro y0`.  Our `while I V k ε` asks two
  goals more (`bound_le_one`, `sat`); for `sat` give a state: `⟨(localVarLens "j" ℤ).set 0
  ⟨X.set v VariableAssignment.init, VariableAssignment.init⟩, indicatorE_of ?_⟩`, with the
  globals of a local write by `rfl` and `Lens.set_get`.
* **`sp` over `(x, y) <- (e₁, e₂)`** leaves a condition on the pair `§(x.pair y)`, which the
  conditions on `§x` do not see (pHL; open gap): write two assignments.
* **A `Decidable` instance for a predicate of the theory** (`instance : Decidable (is_restr s
  n)`, needed for `if is_restr x N then …`) lets `auto` decide closed instances of it: goals
  after `auto` may have fewer conjuncts than before the instance was added.
* **Two tactics of one syntax do not fall back to each other** (infrastructure): a second
  `elab "t" …` with the syntax of an earlier one is tried alone, and its
  `throwUnsupportedSyntax` is the error "Unexpected syntax".  One tactic, several rules: the
  first file names it (`elab (name := phoareConseq) "phoare_conseq" …`), later files add
  `elab_rules (kind := phoareConseq) : tactic | `(tactic| phoare_conseq (: $P ==> $Q)) => …`;
  a rule declines with `throwUnsupportedSyntax`, and the rules are tried newest first
  (`phoare_conseq (: P ==> Q)`: `ECConseq` ≤, `PHoareRnd` `= 1` and `≥`, `PHoareExactTactics`
  `=`; `phoare_seq`: `PHoareSeq` ≤, `PHoareExactTactics` `=` and `≥`).  Test each rule with
  the newest file imported (`Logic/PHoareExactTest.lean`, the last three tests).
* **Distributions of EC's library**: `duniform s` with `duniform1E`, `duniformE`, `undup`,
  `count` (`Lib/EC/DUniform.lean`); the biased coin `dbiased` of `FixedBiased` with
  `dbiased1E`, `dbiasedE`, `dbiased_ll` (`Lib/EC/DBoolBiased.lean`, a theory to clone);
  `ge0_mu`, `le1_mu` (`Logic/PHoareExact.lean`).  A new finite distribution: a `PMF`
  (`PMF.ofFintype`, `PMF.uniformOfFinset`) through `toSubProbability`; its point masses by
  `PMF.toMeasure_apply_singleton`, its expectation by `SubProbability.expected_eq_tsum`.
* **A lemma named like a module** (`equiv SamplePair` next to `module SamplePair`): another
  name for the lemma (`SamplePair_Fair`).
* **`rnd` (identity) between two different distributions** (`r <$ [1..4]` ~ `r <$ [1..6] \ X`):
  `equiv_rnd` asks `d₁ = d₂` (EC: the masses pointwise on the support): a library equality
  (`dinter_dexcepted`), by `SubProbability.ext_singleton` and the point masses
  (`dexcepted_apply`, `dinter_apply`).  `equiv_auto` after `equiv_rnd f g` loops when a
  condition is `b = f (g b)` (simp takes it as a rewrite rule): `equiv_skip` and the
  conditions by hand.
* **Rejection sampling** (EC's `WhileSamplingFixedTest`): `Lib/EC/WhileSamplingFixedTest.lean`
  (`SampleE`, `SampleWi`, `pr_sampleE`, `pr_sampleWi`, `sampleE_sampleWi`); `dinter` is
  `Lib/EC/DInterval.lean`.
* **A file that is its own theory** (`WhileSampling.ec`: `type t. op sample … axiom …`): a class
  `Params (t : outParam Type)` with the operators and axioms as fields, `export Params (…)`,
  `variable {t : Type} [Params t]`.  `predC test` takes a `Bool` test (`Lib/EC/Logic.lean`).

* **EC's `bypr res{1} res{2}=> // &1 &2 w` (2026-11-18, `Sponge.BlockGen_loop_direct`)**:
  `bypr (res{1}) (res{2})`, `intro a1 m1 a2 m2 w _`; EC's `have -> : Pr[…] = …` by
  `byphoare (: True ==> _)` / `byequiv` as written; then `cases a1; cases a2` and
  `refine (?_ : _ = (x : ℝ)).trans h.symm` to chain the `Pr`s.  A value named like a local of
  the procedure (EC's `w` and `BlockGen.direct`'s local `w`) is read as the local inside a
  tactic's argument (`phoare_rnd (pred1 w)`): give it another name (`w0`).
* **Several clones of one theory in a file (2026-11-18)**: a theory's types are `outParam`s of
  its `Params`, so instance search finds the latest clone's instance whatever the types.  Reach
  the theory's definitions and lemmas through each clone's aliases (`C.FUNCTIONALITY.mk`,
  `C.SIMULATOR.call_init`), never the theory's names, where two clones of it are in scope; record
  notation for `mk` and the subtyping coercions still search, and fail at the other clone's
  types (`Syntax/Clone.lean`; why the first port's module types are not clones yet:
  `notes/SHA3/TacticReview.md`, "Status 2026-11-18").

* **A first-port lemma re-proved in EC's script (2026-11-18, `Gconcl_list.lemma1`–`lemma5bis`)**:
  where the first port re-proves a library fact inline (`FMap.joinE`, `FMap.mem_join` for EC's
  `m1 + m2`), move it to `Lib/EC` under EC's name first, then the script is EC's line by line:
  `intro` the names of EC's `move=>`, `obtain` for `have[]…:=INV0`, `constructor` for `split`,
  `smt_close [EC's hints]` for each `smt`.  Give `smt_close` the operators EC's provers see
  through (`valid` for `valid p = true` against `valid_block p`); `rw` cannot rewrite a `dom`
  under an `if` (its `Decidable` instance): `simp only [FMap.mem_set]`.

## 8. Infrastructure pitfalls (when fixing a gap)

* Off-limits: `GaudisCrypt/Language/` (Dominique), `OneWayness.lean`, `QueryHit.lean`.  A change in
  `Syntax/` rebuilds nearly everything (~25 min): batch them.
* New generic lemmas go to `Logic/` or `Lib/` (`Lib/EC/` under EC's names), never in a game file.
* `mkAppM` leaves trailing instance-implicit arguments unapplied (`Lens.pair`'s `Disjoint`):
  `synthInstance` them.
* `✝` names: test `.hasMacroScopes`, not `isInaccessibleUserName`; goal tags from `?h` in
  quotations carry macro scopes (`eraseMacroScopes`).
* `evalTactic` errors inside saved/restored regions are *logged*, not thrown (silent `sorry`):
  restore the `MessageLog` and throw.  `logInfo` inside `saveState`/`restore` is lost.
* `elabTermWithHoles` makes holes `syntheticOpaque`; `applyLemma` too for implicit mvars.
* `simp [Lens.Disjoint.commute]` loops — use `lensWriteNorm`.  `Setter.throwaway_set` in
  `simpReadsDecls` broke PROM.  `lensWriteNorm` together with `Lens.set_outward` loops too
  (`stmt_swap`'s discharger keeps them in separate passes).
* A local variable reaches side goals in two spellings, `localVarLens n T` and, once a rule has
  unfolded that `abbrev`, `(varLens ⟨n, T, …⟩).intoLocal` (its type argument then `⟨n, T, …⟩.type`).
  Anything that compares lenses syntactically must normalize first (`ECSim.lensKey`: every
  subterm `whnfR`, proofs erased); `lensWriteNorm` failed to sort such chains before.
* `stmt_swap`'s side goals: when one fails, reproduce the two statements in a scratch `hoare`
  example (`stmt_swap 2 -1`), then prove the printed residual by hand; the missing simp rule shows
  at once (a reset past a global write needed `resetSetter_set_intoGlobal`).  Debug output
  inside the discharger's `saveState`/`restore` is lost: print with `IO.eprintln`.
* `simp_reads` rewrites under `decide` but leaves the instance: `normDecide` re-synthesizes it.
* Two `elab_rules` for one syntax kind in different files compete by import order (the later
  tried first): `equiv_call (_ : ={…})` had a framed concrete-callee rule in `ECCallEquiv` and a
  frameless one in `ECCallAbstract`, and which one ran depended on the file.  Give one rule the
  syntax and let it hand over to a separate syntax (`equiv_call_concrete`) declared low enough
  to be seen by both.
* Building terms with `arg`/`res` in a syntax quotation makes them hygienic (`arg✝`): no longer
  the condition keywords.  `mkIdent `arg`.
* `moduleStep?` (inlining, `proc`, frames) unfolds views only with `views := true`
  (`accessorNorm`); turned on everywhere it can loop/crash (stack overflow, exit 139); the frame
  splitter uses it only where the plain unfolding is stuck.  `Module.comp` (EC's aliases,
  `RaiseSim`) is steps (11), (12).  A `module`'s `apply_simp` at default transparency (a view
  whose module type's parameters are spelled differently, `RaiseSim(S)`) only with
  `set_option inline.defEqApply true`: always on, it inlined further than the first port's
  `SHA3Security` proofs expect (their `rw`s found nothing).
* Rebuild the module you changed *and* the modules your test file reaches it through:
  `lake env lean` loads stale `.olean`s silently (a fix that "does nothing").
* Names in tactic conditions come from `ProgramSyntax.frameVars`: `.nameable` for elaborating
  (the condition is wrapped in `letI x := slot`), `.printable` for printing (also no binder `x`
  anywhere in the goal).  A new tactic that elaborates a condition filters by `.nameable`; using
  `.printable` hid procedure parameters and locals whenever some `fun x`/proof `h` was in the goal.
* A namespace-local theorem shadows an opened one of the same name; two *opened* namespaces
  with the same name give "Ambiguous term" — when moving a helper (e.g. into `TacticMisc`), don't
  leave an alias behind in the old namespace, qualify the users.
* Tactics that loop over "the next deterministic statement" must stop at `skip` (`sp` over `skip`
  leaves `skip`: it looped until the heartbeats ran out — a `whnf` timeout far from the cause).
* `rfl` at default transparency on reads of local variables unfolds the variable names'
  encodings: use `with_reducible rfl` in tactic alternatives.
* `simp only [h, …] at *` with hypotheses as rules also rewrites the rules themselves (they become
  `True`); to rewrite with hypotheses everywhere else, use `simpGoal` with `fvarIdsToSimp`
  excluding them (`subst_frames`).
* Changing a tactic's semantics (positions, goal order): grep every use first; old ports rely on
  the old behaviour — keep it under a new name (`stmt_swap_raw`) and rename the old uses
  mechanically, rather than recomputing their arguments.
* Elaborators must run `withMainContext`; module steps inside simp callbacks at default
  transparency.
* Multi-line tactic quotations inside `( … )` fail to parse: bind sub-tactics with `let`.  The
  same in proofs: `on_goals 2 => (t₁; t₂⏎ t₃)` does not parse — put the block on its own lines
  under `on_goals 2 =>`.
* **Frames and clone aliases**: the variables a condition reads are collected by `ECSim.varsOf`
  (frames of `sim`, `conseq`, `while`, `call (: P ==> Q)`).  A clone's alias of a global
  (`FRO.m := ROhandle.FRO.m`, a reducible `abbrev`) was missed, so `FRO.m` had no frame and the
  goal was unprovable; `varsOf` now takes reducible aliases of globals too.  When a goal after a
  framed rule lacks an equation EC has, check the variable is seen by `varsOf`.
* **`glob D` through an `if`**: `glob_simp` first pushes the view into conditional states
  (`touched_getter_get_ite`; `RO.get`'s `if (x ∉ m) m.[x] <- r`), then removes the writes.
* **Frames between two final states** (`while`'s exit, `x τ₂ = x τ₁` beside the invariant's
  `x τ₁ = x τ₂`): `subst_frames` keeps one equation of each pair — two made `simp_all` loop.
  A frame whose right side is not a read (`G1.bcol.get g₁ = (… || …)` after a call) is left as a
  hypothesis: `rw [‹G1.bcol.get g₁ = _›]` in a hand closer.
* **EC's `seq n m : R; last by t`**: our `equiv_seq` leaves the first part, then the rest —
  `on_goals 2 => t` is EC's `last`.
* A `smt_close` attempt that failed on a goal that was *wrong* (missing frame, an infrastructure
  bug) may be retried once the goal is fixed — the one-attempt rule is per goal.
* **Ambiguous tactic syntax**: `equiv_call (_ : ={x})` also parses as `equiv_call H` with `H` the
  term `(_ : ={x})` (a `choice` node, which moves to the next reading only on
  `throwUnsupportedSyntax`).  The invariant reading comes first; the `equiv_call H` rules now also
  refuse a hole with a type ascription.  A new `elab_rules` for an existing kind must throw
  `unsupportedSyntax` (not an error) for what it does not handle, and check the forms another
  syntax shares.  To see which elaborator runs: `tacticElabAttribute.getEntries env kind` on each
  alternative, results collected and logged *after* the state restore.
* **Earlier errors and frames**: the frame builders (`ECCallEquiv.elabClean`,
  `ECConseqFrame`'s proofs, `module_subtype`) used to reject a frame whenever the file's message
  log had *any* error, so one failing bullet above made every later call lose its frames (goals
  without `G1.bcol.get g₁ = …`).  Fixed (the log reset around each check); when a frame is
  missing, still fix the errors above it first.
* **Two different concrete callees**: `equiv_call (_ : ={x})` is EC's
  `={arg, x} ==> ={res, x}`, the callees' judgment left as the first goal (EC's `call` subgoal).
* **`sim` over a call**: with no equality set given, ours now keeps EC's — the variables read
  after the call that the callee touches (`F.RO.m` for `RO.get`), needing their `fp_bound`s
  (`fp_le` on the callee).  A `sim` goal asking `globals₁ = globals₂` means no bound was found.
  Calls of *different* concrete procedures and two loops after `inline*`: `sim` handles them
  (Gconcl GAP 1, 5).
* **One-sided `while{i}`**: `equiv_while{1} (I) (V)` (both in parentheses), with EC's frame of
  what the loop keeps, so EC's `I` as is (`true`).  Its goals: `lossless`
  (`while_ll_phoare; intro σ₂; phoare_auto`), `variant` (`intro σ₂ k; hoare_auto`), the code
  before (EC's second goal; its exit part over the loop's final state `τ`).
* **EC's `case (P{1}); [rcondt{1} n;2:rcondt{2} n | rcondf{1} n;2:rcondf{2} n]`**:
  `equiv_case (P)` then per branch `stmt_rcondt{1} n` / `stmt_rcondt{2} n`, each side goal by
  `hoare_auto` (EC's `move=>?;conseq (_:true);auto`).
* **One declaration per EC variable.**  A `global_var` is identified by its full name: two files
  that each declare `C.c` have two variables, and lemmas about one say nothing about the other.
  Before declaring a variable, module or module type, check whether a file the pilot builds on
  already declares it, and use (open) that one.
* **Local modules of other files** (EC's `local module`, `local clone`): fresh for `D` in EC; when
  a section uses a lemma whose `declare module D` names them, its own `declare module D` names
  them too (`-Pilot.Gcol.Gcol.sample_c`, `-Pilot.ConcreteF.Switching.DBounder`, …).  Large
  restrictions need `set_option synthInstance.maxHeartbeats 400000` (`Module.Declared.weaken`).
* **EC's `byequiv … => //#` up to bad**: `Pr[ p₁ : E₁ ] ≤ Pr[ p₂ : E₂ ] + Pr[ p₂ : bad ]` is
  `byequiv H` directly (the side goal `E₁ → E₂ ∨ bad` from `H`'s post).
* **`glob` of a concrete functor application** (`G2(DRestr(D))`) in a lemma's side conditions:
  register the old port's footprint bound (`attribute [fp_bound] fvP_G2`) so `ec_module` and
  `fp_disjoint` see through it.  Its `={glob …}` does not give its variables' equalities (an
  upper bound only): Gext's GAP 8.
* **Globals in `sp`'s existential form**: the rule states `X.intoGlobal.get σ = …` and
  `… (X.intoGlobal.set v σ).globals …`; `stmt_sp` now rewrites them to `§x` reads.  Unnormalized,
  frames (`ECSim.varsOf`) and closers did not see the variable: a framed call lost its frame
  equations, a closer lost `C.c{1} = v + 1`.
* **`conseq` and `glob A` across calls**: EC's `conseq` keeps `glob D` over code that calls
  concrete procedures outside `D`; ours does too (`Stmt.KeepsRegion.call`, `fp_finite` and
  `fp_disjoint` side goals).  A post goal `touched_getter τ₁ = touched_getter τ₂` left after a
  `conseq` means the frame lost a region: check `keepsRegionOf` has a rule for each statement.
* **`inline *` after `if`**: EC's `if=>//; inline *` inlines in *every* branch; ours is
  `stmt_if; · auto_close; all_goals stmt_inline*`.
* **`‹_›` and implicit shapes**: `lt_irrefl _ (‹∀ h0, _ → _› _ hd)` lets the pattern's `_` unify
  with the wrong body; name the hypothesis first (`have hf := ‹∀ h0, … → h0 < _›`).  Likewise
  `(h.trans (by omega))` runs `omega` before unification: `refine h.trans ?_; omega`.
* **EC's type abbreviations** (`state`): write the module code with the library's own name
  (`SLCommon.state`).  A local `abbrev state` types the procedures' variables twice
  (`localVarLens "x0" state` vs `localVarLens "x0" SLCommon.state`); reads at one type are not
  rewritten by equations at the other, and closers fail.
* `sorry` after a tactic that closed all goals is **not** reported; a `trace_state` printing
  nothing there means the goal was already closed.

* **Strict `auto`/`skip` (2026-11-12)**: `ec_auto`/`ec_skip` (`Logic/ECAutoStrict.lean`,
  `Logic/ReadNorm.lean`) normalize the goal to the read normal form and generalize every read;
  a state that survives is an error naming the place, not a goal about `σ`.  Migrating a proof
  from `hoare_auto`/`phoare_auto`/`phoare_skip`: `rintro σ ⟨…⟩` becomes `ec_intro; rintro ⟨…⟩`,
  reads of `σ` in the hand step become the value names.  A hypothesis that is now an equation
  between values (`hash = h`) is taken with `rintro rfl`: an anonymous-constructor pattern on it
  substitutes and binds nothing.  A gap in the normal form is fixed in `ReadNorm.normalize`, with
  a golden test in `Logic/ReadNormTest.lean`, not at the call site.

* **Strict mode (2026-11-13)**: every pilot with proofs starts with `set_option ec.strict true`.
  A tactic fallback (reads not generalized, a weaker call rule, `sim` asking all globals equal)
  is then an error at the tactic, not a warning.  Where a fallback is a known gap, switch it off
  for that one tactic, `set_option ec.strict false in equiv_call (_ : ={glob Perm})`, so the gap
  is visible in the source.  A new pilot file gets the option from the start.

* **The closer in new proofs (2026-11-14)**: `ec_close` (EC's `auto => /#`), `ec_progress`
  (EC's `progress`), `ec_prep` (the preparation alone, before a hand step) — `Logic/ECProgress.lean`.
  Two phases.  First the states go: a goal `∀ σ, P` / `∀ σ₁ σ₂, P` (a rule's side goal) gets every
  read generalized to a value, an error if a state survives (`ec_values`); a goal after
  `ec_auto`/`ec_skip` is already about values.  Then logic only, `auto_prep`'s steps without the
  ones about states.  The values are in the context **under their names** (`x`, `x₁`, `RO_m`), so a
  hand step refers to them by name; the hypotheses have no names: take them by type (`‹_ ≤ _›`),
  or name them before the closer (`ec_auto; ec_intro; rintro ⟨h₁, h₂⟩`), not by `rename_i`.
  The old `auto_close`/`auto_progress`/`auto_prep` stay for the proofs written on them.
* **Names of the values (2026-11-14)**: a generalized read is named after its variable (`x`; `x₁`,
  `x₂` by side).  Where that name is taken — in the context, or by another read — a module's
  variable takes the module's name with it: `RO_m`, `RO_m₁` (before: a number, `m1`).  A local
  variable keeps its name (numbered only if that is taken too).

* **Writing a proof on the strict tactics (2026-11-14, `SmartCounter/Gconcl_list.lean` from
  `Ideal_equiv_valid` on)**:
  - EC's `auto` on a judgment is `ec_auto`; where EC's `auto` closes the goal and `ec_auto` leaves
    an implication, `ec_auto; ec_close`.  While developing write `ec_auto <;> ec_close` and remove
    what the linter reports as never executed.
  - EC's `call (: I)` on two *different* concrete procedures (`S(IF').f ~ S(Valid2).f`):
    `equiv_call (_ : ={arg, x…} ∧ I ==> ={res, x…} ∧ I)` with the invariant's variables, then
    `equiv_proc` (EC's form opens the callees).  On a declared callee with only `glob`s,
    `equiv_call (_ : ={glob S, glob C, glob F.RO.asRO})` gives EC's goals.
  - After `ec_progress` the values have their names and the hypotheses none: a hand step takes a
    hypothesis by type, `‹inv_L_L3 _ _ _›`, `‹valid _ = true›`, `‹¬ FMap.dom m₁ _›` (name the
    value in the pattern when two hypotheses have the same shape).
  - Nested final memories (`∀ τ₁ τ₂` of `while`/`conseq`) become values too; their names are
    qualified further (`SLCommon_F_RO_m₁` next to `F_RO_m₁`).
  - The side goal of a one-sided `rcond` has the other side's memory in the context: the closer
    makes its reads values too (`ec_auto; ec_prep`, then the hand step).
  - A fact EC's `smt` uses everywhere (`parse_valid` for our `valid`): one `have` at the top of
    the proof; the closers then find it.
  - Probing: one lemma in an uncommitted scratch file next to the pilot, compiled alone with the
    lakefile's options (seconds, not the file's minutes), `trace_state` at the open leaves.

  - A long proof: keep the finished branches in a saved copy and `sorry` them in the scratch
    file (`· sorry -- TRIMn`), splice them back at the end; each check then compiles only the
    branch in work.
  - An EC module alias (`module P = Perm`) is written as what it stands for: EC unfolds it, and
    a Lean `abbrev` of another module type is not opened by `inline*`.
  - A fact EC proves inline several times (in both branches of a test, at each `rcond`): a plain
    lemma before the theorem, stated on values, EC's lines kept as comments at each use.
  - A hypothesis with binders is not found by `‹∀ l, P l → _›`: state it in full,
    `have h : ∀ l, … := by assumption`.  A side condition `(by omega)` of a lemma inside `rw [..]`
    runs before the lemma's arguments are known: write the arguments.
  - A shared preamble for all the leaves (`all_goals have …`) ends with its `simp only … at *`:
    the goals it closes (`x = x`) then need no bullet.
  - Two states equal by components after `sp` (GAP 8): `have hx : x₁ = x₂ := Prod.ext (by simp
    only [*]) (by simp only [*])`, before any `subst` that makes the two sets of hypotheses
    indistinguishable.

## 9. Checklist before calling a lemma done

- [ ] Statement in surface syntax, EC's hypotheses only, EC's name; docstring quotes EC's
      statement and lists deviations.
- [ ] Proof: every EC step has a Lean step with the same arguments/positions; no glue (§0).
- [ ] Closers: `auto_close` / `smt_close [EC's lemmas]` / short hand proofs with EC's lemmas.
- [ ] No aux lemma beyond EC's (inline `have`s inline), except plain-value facts standing for
      EC's `smt` (§5).
- [ ] EC's goal selectors renumbered where our goal order differs (`equiv_while`); no
      `stmt_swap_raw` / one-number `stmt_wp k` where EC writes positions (§4).
- [ ] Budget set per declaration with a reason; `sorry`-free; `lean_verify` shows standard axioms.
- [ ] `lake build` of the module green; full build + `SmartCounter/ConcreteF.lean` if infrastructure
      changed.
- [ ] `notes/SHA3/Refactor.md` (and `Mapping.md`) updated; `ec_fidelity.py` run.

## 10. Reference ports (read these first)

`SecureRO`, `SecureORO`, `IndifRO_is_secure`, `SLCommon`, `ConcreteF` are on EC-form
declarations.  **`Handle.lean` and `Sponge.lean` are over the old port's declarations** and carry
its artifacts (`unfold CF`, abbreviation module types, `Module.app Sponge.f …`, CF_G1's `rintro`
glue around the *old* `eq_f`/`eq_fi`): copy their proof steps, not their declarations.

* Statements + `Pr` + `fel` + `phoare_seq`: `SecureRO.lean` (`RO_is_preimage_resistant`).
* Abstract calls, clones, `sim /`: `SecureORO.lean`, `IndifRO_is_secure.lean`.
* `declare axiom`, up-to-bad call, `equiv_sym`: `SLCommon.lean` (`Pr_restr`, `swap_restr`).
* Two-sided loops, `inline` by name, `equiv_seq`: `Sponge.lean`.
* Loops, `splitwhile`/`alias`/`conseq` frames, `sim (_ : I)`, `phoare_while`: `ConcreteF.lean`
  (`DoubleBounding`, `Real_GReal'`, `Real_Concrete`).
* An adversary with several procedures and an oracle, a cloned random oracle, up-to-bad with
  the oracle's log, pHL on an event, `swap` past the adversary: `Examples/BR93.lean`
  (`br93.ec`); goals of the call rules in `Logic/ECCallMultiProcTest.lean`.  The same file:
  a theory and its instance (`clone` of a theory with clones, a wrapper adversary, the
  theory's theorem applied to it).
* `bypr` on `equiv`, nested pHL `seq` with all four bounds, `seq` on a lower bound, a cloned
  distribution theory: `Examples/VonNeumann.lean` (`vonNeumann.eca`).
* pHL on exact bounds (a probability computed step by step), loops in pRHL with a coupling
  (`rnd (fun b => …)`), finite sets: `Examples/PIR.lean` (`PIR.ec`); goals of the rules in
  `Logic/PHoareExactTest.lean`.
* Large invariant proofs with `exists*`, ambient cases, `rcondt`/`rcondf`, `swap` past calls:
  `Handle.lean` (`eq_fi`, `eq_f`, `CF_G1`) — compare with `Handle.eca`: `eq_fi` from line 1349,
  `eq_f` 1488–1813, `CF_G1` 2595.
