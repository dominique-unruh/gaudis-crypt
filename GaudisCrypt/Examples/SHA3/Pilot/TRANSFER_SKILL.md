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
   **Order** (`Refactor.md`, "What retiring the old files waits for"): bottom-up; the two tops
   `SHA3OSecurity` (7.8k lines) and `SHA3Security` use the old files' lens parameters ~120× each.
2. **Port bottom-up** along the import graph.  A file is switched *by its fidelity port*: the
   port lives in `Pilot/` next to the old file; dependents move to it one by one; the old file is
   retired when its last dependent is ported.  Never mechanically rewire old dependents.
3. **File setup**: `Pilot/<EcName>.lean`, `namespace GaudisCrypt.SHA3.Pilot.<EcName>`, module
   docstring with a "Translation" list (see `Pilot/SecureRO.lean`).  **Imports**: every EC tactic
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
   `generalizeReads`, also recheck the pilots outside the barrel (`Pilot/ConcreteF.lean` ~150 s,
   `Pilot/IRO.lean`; `lake env lean …`) and do a full build — closer changes break old
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
| `module M (A : T, F : U) : V = { … }` | `module M using (A : T, F : U) : V { … }` | Procedures: `proc f (x : a) : b { var y : c; …; return e };` Reads are `$x`, writes `x <- e`, samplings `x <$ d`, calls `x <- call F.f ($a)`; booleans of props via `decide`; `open Classical in` before the module if needed. |
| EC's `witness` | `default` | |
| subtyping `RO <: RF` (passing an `RF` where an `Oracle` is expected) | `module_subtype RF <: Oracle` | Same-field module types: identity coercion. Module-type abbreviations are seen through. |
| `module CF(D) = Indif(SqueezelessSponge(PF), PF, D)` (alias) | `noncomputable abbrev CF (D : T) := Module.app Indif (Module.pair …)` | Prefer an alias over a `def` (a `def` needs `unfold` in proofs). |
| `section S. declare module A <: T {-M₁, -M₂}.` | `section S` … `declare module A <: T {-M₁, -M₂}` … `end S` (`Logic/DeclareModule.lean`; needs the enclosing `section`, as do `declare axiom`s) | Variable + instance-implicit `[Module.Declared A S]`; `S` read off the `global_var`s of `M₁`'s code / `glob` of declared modules. Representability is derived. |
| `declare axiom D_ll : …` | `variable (D_ll : ∀ (F <: T {-D}), …, islossless D(F, P).distinguish)` + `include D_ll in` on the lemmas using it | `∀ (F <: T {-X}), P` and `∃ (S <: T {-X}), P` are `Logic/ECModuleBinders.lean`. |
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
| `byphoare (: P ==> _)` / `byphoare (H)` | `byphoare (: P ==> _)` / `byphoare (H)` |
| `have ->: Pr[…] = Pr[…] by …` (rewrite chain) | `calc` steps, or `have e : … := by …` then `simp only [e]` (`rw` on `Pr[ ]` goals often fails its instances-transparency check) |
| `proc` | `equiv_proc` / `hoare_proc` / `phoare_proc` (to the body, params as locals; EC's counts) |
| `inline*` | `stmt_inline*` (`hoare_inline*`, `phoare_inline*`) |
| `inline{i} M.f` / `inline M₁ M₂` / `inline{i}*` | `stmt_inline{i} (M.f)` / `stmt_inline (M₁) (M₂)` / `stmt_inline*{i}` (parens needed: `stmt_inline n` inlines call site `n`) |
| `sp` / `sp n m` | `stmt_sp` / `stmt_sp n m` (EC positions) |
| `wp` / `wp n m` | `stmt_wp` / `stmt_wp n m` (EC positions; `-k` from the end). One-number `stmt_wp k` is *ours*: the last `k` statements |
| `auto` | `equiv_auto` / `hoare_auto` / `phoare_auto` |
| `auto`, `skip` (new proofs) | `ec_auto`, `ec_skip`: the same on every judgment, every read a value or an error; then `ec_intro` puts the values in the context under their names (`m1`, `bounder`, `x`), and the hand step names values, never `X.get σ.globals` |
| `skip` | `equiv_skip` / `hoare_skip` / `phoare_skip`; if a read under `decide` or an inlined call's renamed state blocks the closer, `equiv_skip_ec` (what `equiv_auto` uses) |
| `if` / `if{i}` | `stmt_if` (goals EC's: `guard, then, else`; each branch with the code after it, flattened: EC's positions inside a branch) / `stmt_if{i}` |
| `rcondt{i} n` / `rcondf{i} n` | `stmt_rcondt{i} n` / `stmt_rcondf{i} n`, EC's positions; side goal first: `· hoare_auto; …` |
| `seq n m : P` (pRHL) | `equiv_seq n m : (P)` (leading counts, resets not counted). The old from-the-end cut is `equiv_seq_last` |
| pHL `seq n : E p₁ p₂ p₃ p₄ I` (upper bound) | `phoare_seq n : (E) p₁ p₂ p₃ p₄ (I)`; goals tagged `invariant, first_E, second_E, first_notE, second_notE, bound` (bounds `1` closed on the spot), `_` bound allowed. `≤` goals only |
| Hoare/pHL `seq n : P` (one condition) | **missing** as an EC-form tactic (8 uses: SHA3Security, Gconcl_list); `stmt_split k` cuts counting from the end |
| `swap{i} n k` / `swap{i} [a..b] k` / `swap k` | `stmt_swap{i} n k` (EC positions) / `stmt_swap{i} [a..b] k` / `stmt_swap{i}? [-]k`.  A call moves past assignments, samplings, and deterministic `if`s/sequences of writes to globals outside the callee whose conditions read what the call keeps (`callDet`, Gcol's `swap{1}[1..2]3`).  Not yet: past an assignment whose value reads a global the callee only *reads* (Gcol GAP 4: inline the call first).  **When the moved block and what it moves past both read a variable** (footprints not disjoint), do EC's later `inline *` first (`stmt_inline{i} k`, last call first) so that one side is deterministic code, then `stmt_swap` at EC's positions *after* the inlining (a `reset_vars` counts with the statement after it); EC's later `seq`s then count the inlined statements (Gconcl `G2_G3` `S.f`) |
| `call (: inv)` (abstract adversary, Hoare) | `hoare_call (: inv)`; goals oracle(s) first, then pre |
| `call (_ : ={glob A, x…})` (abstract) | `equiv_call (_ : ={glob A, x, …})` |
| `call (_ : ={…} /\ I)` | `equiv_call (_ : ={…} ∧ I)`; the oracles' goals are EC's `={arg} ∧ I ==> ={res} ∧ I` (`={glob D}` framed by their writes), so EC's intermediate conditions need no `glob D`.  With another `glob X` named (or an oracle the frame cannot open, a view), the oracles keep the region `glob D ⊔ glob X` themselves |
| `call (_ : bad, I, J)` (up to bad) | `equiv_call (_ : bad, I, J)`; EC's goal order; `D_ll`'s goal: `exact D_ll` (E11: right oracles' `islossless` is one more goal each) |
| `call (: P ==> Q)` (concrete callees, pRHL) | `equiv_call (_ : P ==> Q)`; callee's judgment first, then pre; the frame of unwritten variables is found |
| `call (_ : ={glob P})` / `call (_: ={x})` (concrete callee) | `equiv_call (_ : ={glob P})` / `equiv_call (_ : ={x})`, with EC's frame (what the callee does not write keeps its value); the callee's judgment (EC's `1: by sim`) is closed by its footprint |
| `call H` | `equiv_call (H)`; `phoare_call H` (`?_` holes = EC's `call` subgoals); `hoare_call H` |
| `call{i} H` | `equiv_call{i} H / x, glob A` (frame listed) |
| `call (: P ==> Q)` in `phoare` / `hoare` | `phoare_call (: P ==> Q)` / `hoare_call (: P ==> Q)`; `phoare_call H / x, …` for lossless + frame |
| `sim` / `sim n m` / `sim (_ : I)` / `sim` with `={glob A}` | `sim` / `sim n₁ n₂` / `sim (_ : I)` / `sim / x₁, …, xₙ` (equal except the listed globals).  Calls of different concrete procedures (EC's `sim` goes into them): where plain `sim` makes no progress it inlines the callees, runs again and closes the rest by `auto_close` — so EC's `by sim` stays `sim` (Gconcl `G4_Ideal`).  A partial `sim` is never changed that way.  Two loops: the invariant is the relation after them plus EC's equality set (computed backwards through the bodies, `ECSim.eqBack`: locals written before read are not in it); when that relation reads what the loops change, the equality set alone (Gconcl `G2_G3` `M.f`).  Why `sim` stops: `set_option debug.sim true in sim` (loops, calls, unfinished branches) |
| `rnd` / `rnd{i}` / `rnd f` | `equiv_rnd` / `equiv_rnd{i}` / `equiv_rnd f` (product samplings: `equiv_rnd_dprod`) |
| `rnd f g` | **missing** (~14 uses, Sponge, SHA3OSecurity): `equiv_rnd f` has other side goals |
| pHL `rnd (pred1 v)` / `rnd` (lossless) | `rnd_pred1 v` / `rnd_bound` (on the expectation `phoare_auto` leaves at a sampling) |
| `hoare` | as a *tactic turning a `phoare … = 0`/`≤ 0` goal into a Hoare triple*: `phoare_hoare`; at a *sampling* inside a pHL proof (the event has probability 0): `rnd_null` |
| `conseq (: P ==> Q)` / `conseq (_ : _ ==> Q)` | `equiv_conseq (: P ==> Q)` / `equiv_conseq (: _ ==> Q)`; also `hoare_conseq (: P ==> Q)`, `phoare_conseq (: P ==> Q)` (upper bounds). EC's frame of what the code keeps is kept |
| `conseq H` | `equiv_conseq H` (pRHL only) |
| `exists* e₁{1}, e₂{2}; elim* => a b` | `equiv_exists* §e₁{1}, §e₂{2}` then `intro a b` (also on procedure judgments, `§x{2}` the parameter); `stmt_exists* e` |
| `elim * => a b` (after `sp`) | `equiv_elim* => a b` / `hoare_elim* => a`: EC's names, the left side's existentials first |
| `case (P)` (pRHL) | `equiv_case (P)` |
| `case @[ambient]: {-1}(e) (eq_refl e) => [h₁ \| x h₂]` | `rcases h : e with _ \| x` (or `by_cases h : P`) |
| `exfalso` | `equiv_exfalso` |
| `while I` (two-sided) | `equiv_while (I)` (`Logic/ECWhileRel.lean`): EC's two goals, `body` (`I ∧ b₁ ∧ b₂ ==> I ∧ b₁ = b₂`) and `hpre` (EC's `(I ∧ b₁ = b₂) ∧ ∀ τ₁ τ₂, (frames: what the loops keep) → I → ¬b₁ → ¬b₂ → Q`). EC's `while I; last first; + auto; progress.` and its bullets transcribe as `equiv_while (I)` then `case hpre => equiv_auto; auto_progress` with one bullet per EC bullet (PFf_Cf's first loop: EC's seven).  The exit goal's frames are equations between the two final states' reads (`x τ₂ = x τ₁`, and the invariant's `x τ₁ = x τ₂`): `subst_frames` keeps one of each pair, so `progress`/`smt_close` close frame equalities as EC does.  The older four-goal form without frame is `equiv_while_raw` |
| `while{i} I V` | `equiv_while{i} (I) (V)`; goals `lossless`, `variant`, then the code before (EC's: `I` and, over the loop's final states under EC's frame, `I ∧ ¬guard ⇒ post`; old form with an `exit` goal and no frame: `equiv_while_noframe{i}`). EC's body goal (`auto; sp; rcondt 1; …`) on `lossless`: `while_ll_phoare`, then the `phoare` tactics |
| pHL `while I V` (`= 1`) | `phoare_while I V` (then `intro k` in the body goal) |
| Hoare `while I` | `hoare_while I` |
| `splitwhile{i} n : e` / `unroll{i} n` | `stmt_splitwhile{i} n : e` / `stmt_unroll{i} n` |
| `alias{i} n x = e` | `stmt_alias{i} n x = e` |
| `transitivity{i} { code } (P₁ ==> Q₁) (P₂ ==> Q₂)` | `equiv_trans{i} { code } (P₁ ==> Q₁) (P₂ ==> Q₂)` |
| `transitivity N.f (P₁ ==> Q₁) (P₂ ==> Q₂)` (procedure) | **no tactic** (2 uses, Sponge); the rule `prhlProc_trans_ec` (`Logic/ECTrans.lean`) |
| `proc (I)` on an abstract procedure | **no tactic** (4 uses, Sponge); use `equiv_call (_ : ={…} ∧ I)` one level up, or the `AbstractCall` lemmas |
| `symmetry` | `equiv_sym` |
| `fel n cntr step q bad [O.f : pre] inv` | `fel §cntr (fun i => step) q (bad) [pre] (inv)` — EC's `n` dropped: the call must be the **last** statement (`stmt_wp` first). Goals EC's order (`sum`, `init`, oracle `step`, `incr`, `same`, `keep`). Deviations: `bad` must persist; **one oracle only** — Gext's `fel 8 … [ReSample.f : …; ReSample.f1 : …]` needs the multi-oracle extension .  **A procedure the oracles call** (`fel … [Gcol.sample_c : pre]`): `fel §cntr (fun _ => step) q (bad) [Gcol.sample_c : pre] (inv)?` (`Logic/FelInner.lean`; `inv` may be left out): `stmt_wp` itself, the event may be EC's `bad ∧ cntr ≤ q`, `pre` may read anything, the oracles' code checked syntactically (`exp_decr`), `lt` closed; goals `sum`, `init`, then per procedure `step`, `incr`, `same`, `keep`. Over the procedure's body: `byphoare (: True ==> _)`, `phoare_proc`, `phoare_inline*` first (Gcol's `Pr_col`).  Code *after* the adversary's call (Gext's resampling) is checked like the oracles, so it must stay calls of the named procedures: inline only the wrapper (`phoare_inline 1` for `DRestr(D)`'s call, Gext's `Pr_ext`); several procedures `[ReSample.f : …, ReSample.f1 : …]` (EC's `;` is `,`) |
| `bypr` | not a tactic (E12; before `fel`, collapses to `phoare_proc`) |

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
* `smt (@Block.DBlock …)` for losslessness → the `@[simp]` facts `bdistr_expected_one` etc.
  (state them once per file/library, `is_lossless_iff_expected`).
* EC's `smt()` on real arithmetic → `linarith`/`positivity`; bounds: `Lib/EC/StdBigop.lean`
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
* Long proofs: `sorry` the later bullets while working on early ones; files outside the barrel
  are checked with `lake env lean`.  For one bullet of a long proof, work in an uncommitted
  scratch copy of the file with every other bullet `sorry`'d (`Pilot/GcolScratch.lean`: 7 s per
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
  `glob D`.  Read them before porting those files; retire them if `declare module` /
  `Module.ECGlob` now cover the case.
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
* **Missing** (counts over the files still to port): Hoare/pHL `seq n : P` (8); `rnd f g` (~14);
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
* **Inlined callees' locals are renamed per side** (`x3, n0` against `x0, n`): `sim` relates
  loops by name, so it stops at loops of such callees; `equiv_while (§x3{1} = §(localVarLens "x0"
  T){2} ∧ …)` with the bodies by `sim` (SHA3Indiff GAP 2).
* **`byequiv`'s precondition through `sp`**: the two memories' equation with the initializations
  written over them; `glob D`'s equality by hand, `congrArg` of `glob D`'s getter then
  `simp (disch := fp_disjoint) only [touched_set_of_le_compl]` (SHA3Indiff GAP 4).

* **`rcondt{i} n` / `rcondf{i} n` on a `while`** (Gconcl_list `ideal_equiv`): as EC, the loop
  unrolled first — `rcondt` leaves the body before the loop (EC's later positions count the body's
  statements), `rcondf` removes the loop.  `splitwhile` then `rcondt` on the second loop and
  `rcondf` on the spliced `if`, then on the loop again, is EC's usual last-round peel.
* **`hoare_while I` needs the loop last**: EC's `while` side goals after `rcondt` on a loop end
  with the spliced round's head (`i <- i + 1; …`): `stmt_wp` first (deviation).
* **`call (: ={glob IF, glob S, glob A} ∧ …)` with concrete modules**: `equiv_call` reads each
  `glob M` of a module of procedures as its written variables (`Logic/GlobWrites.lean`), exactly
  EC's goals.
* **EC's `smt` selects lemmas itself** (`domE`, `mem_set`, `get_setE`, the definition of an `op`
  such as Gconcl_list's `<=`): `smt_close` takes them in its list (a definition by name unfolds).
* **Tuple equations from `sp`** (`(bl, nb) = x`, or a chain `(p, n) = x0`, `x0 = (bl, nb)`):
  `auto_close` does not use them (GAP 1 of Gconcl_list): `intro σ₁ σ₂ h; simp_reads_all;
  smt_close []`.  (A rule for them in `subst_reads` was tried on 2026-11-12 and taken out: it
  broke `smt_close` steps in `Pilot/SHA3Indiff` and shifted `Pilot/Handle`'s `rename_i` names.)
* **`hoare_auto` after `sp`**: its `skip` simplifies the reads through writes before it
  generalizes the reads (2026-11-12); the goals it leaves have no `True ∧` and no state binder
  when nothing reads the state.
* **Every pilot file is in the barrel** (`GaudisCrypt.lean`), also unfinished ones: a file outside
  it is not checked by the full build (`Pilot/SHA3Indiff` broke unnoticed that way).

* **A warning `tac: … (ECReport.fallback)` is a gap, not noise** (2026-11-13): the tactic could
  not do the step as specified and continued another way (`the reads are not generalized`: the
  goal stays about the states; `using the rule without a frame`; `sim: no equality set for the
  call`).  `set_option ec.strict true in` makes it an error; `set_option trace.ec.frame true in`
  lists what a frame keeps and drops.  The frameless call rule by name: `equiv_call_frameless`.
* **Golden tests** (`Logic/ECAutoTest.lean`, `ECCloseTest.lean`, `ECRulesTest.lean`,
  `ECCallsTest.lean`): a tactic change that changes an output fails there first;
  `scripts/update_golden.py FILE` refreshes the expected text — its diff is the record of the
  behaviour change.  A tactic change comes with a golden test of the new behaviour.

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
- [ ] `lake build` of the module green; full build + `Pilot/ConcreteF.lean` if infrastructure
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
* Large invariant proofs with `exists*`, ambient cases, `rcondt`/`rcondf`, `swap` past calls:
  `Handle.lean` (`eq_fi`, `eq_f`, `CF_G1`) — compare with `Handle.eca`: `eq_fi` from line 1349,
  `eq_f` 1488–1813, `CF_G1` 2595.
