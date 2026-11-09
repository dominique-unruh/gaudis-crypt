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

1. **Read EC's file** (sources: `scratchpad/ext/sha3/proof/…` in the session scratchpad; clone
   `formosa-crypto/sha3` again if gone).  Note its clones, module variables, `declare module`s,
   `local` modules, `declare axiom`s.
2. **Port bottom-up** along the import graph.  A file is switched *by its fidelity port*: the
   port lives in `Pilot/` next to the old file; dependents move to it one by one; the old file is
   retired when its last dependent is ported.  Never mechanically rewire old dependents.
3. **Declarations first** (§2), then statements (§3) — compile them with `sorry` proofs.
4. **Proofs**: transcribe EC's script line by line (§4), closers last (§5).
5. **Each gap** (a step with no Lean counterpart, or one that needs glue): fix it once,
   generically, in `Logic/`/`Lib/`/`Syntax/`, add a test next to it (`XTest.lean`), then continue.
   Before adding anything, check it does not exist (`grep -rn 'elab "…' GaudisCrypt/Logic`;
   names with trailing spaces are easy to miss).
6. **Measure**: `scripts/ec_fidelity.py` (surface statements, clean proofs, term/den/fp, extra
   hypotheses, aux).  Update `notes/SHA3/Refactor.md` (Ported / Measurement) and
   `notes/SHA3/Mapping.md`.
7. **Build/check**: `LEAN_NUM_THREADS=4 nice -n 10 lake build <Module>`; never two lake builds at
   once.  After *any* change to closers or `generalizeReads`, also recheck
   `Pilot/ConcreteF.lean` (not in the barrel, ~150 s: `lake env lean …`) and do a full build —
   closer changes break old hand-written proofs (`rintro` patterns) far away.
8. Commit locally at milestones (`Co-Authored-By` line); the user pushes.

## 2. Declarations

| EC | Gaudí | Notes |
|---|---|---|
| `type from, to.` + `op`s + `axiom`s of a theory | `class Params («from» «to» : outParam Type)` with the ops and axioms as fields; `export Params (…)` | outParams: the one instance in scope (= EC's clone) fixes the types, so ops and module types are written without types. Then `variable {«from» «to» : Type} [Params «from» «to»]`. |
| `clone [import] T as C with type a <- τ, op o <- e` | `clone [import] T as C with type a <- τ, op o <- e` (`Syntax/Clone.lean`), `proof * by tac` on its own line | Theory = namespace with `class T.Params`. Clone = instance `C.params` + reducible aliases `C.x`. Clones of theories still in old (lens-parameter) style: a `namespace C` with `global_var`s for its module variables and `abbrev`s applying the library modules at them (`ConcreteF`'s `Switching`, `SLCommon`'s `F`). |
| `rename [module] "A" as "B"` | `noncomputable abbrev B := @C.A` | |
| `module M = { var x : t … }` | `global_var M.x : t` before `module M { … }` | Disjoint from every other variable by instance search. |
| module variable whose type mentions only theory types | `module_var M.x : T` (`Syntax/ModuleVar.lean`) | It takes the theory's instance; `global_var` (in `Language/`, off-limits) does not. |
| `module type T = { proc f(x : a) : b … }` | `moduletype T { proc f (x : a) -> b; … }` | A module type named like a module: suffix `_T` (E3). |
| `module type A (F : Oracle) = { proc guess … }` | `abbrev A := Oracle →ₘ procmod (a) → b` | |
| `module M (A : T, F : U) : V = { … }` | `module M using (A : T, F : U) : V { … }` | Procedures: `proc f (x : a) : b { var y : c; …; return e };` Reads are `$x`, writes `x <- e`, samplings `x <$ d`, calls `x <- call F.f ($a)`; booleans of props via `decide`; `open Classical in` before the module if needed. |
| EC's `witness` | `default` | |
| subtyping `RO <: RF` (passing an `RF` where an `Oracle` is expected) | `module_subtype RF <: Oracle` | Same-field module types: identity coercion. Module-type abbreviations are seen through. |
| `module CF(D) = Indif(SqueezelessSponge(PF), PF, D)` (alias) | `noncomputable abbrev CF (D : T) := Module.app Indif (Module.pair …)` | Prefer an alias over a `def` (a `def` needs `unfold` in proofs). |
| `section; declare module A <: T {-M₁, -M₂}.` | `declare module A <: T {-M₁, -M₂}` (`Logic/DeclareModule.lean`) | Variable + instance-implicit `[Module.Declared A S]`; `S` read off the `global_var`s of `M₁`'s code / `glob` of declared modules. Representability is derived. |
| `declare axiom D_ll : …` | `variable (D_ll : ∀ (F <: T {-D}), …, islossless D(F, P).distinguish)` + `include D_ll in` on the lemmas using it | `∀ (F <: T {-X}), P` and `∃ (S <: T {-X}), P` are `Logic/ECModuleBinders.lean`. |
| `local module L (A : T) = { … }` | an ordinary `module` (or `module_var`s + `module`) inside `namespace Section` *before* the section's `declare module` | Its freshness for the declared adversary goes in the adversary's restriction list (EC: implicit) — e.g. `{-RO, -Preimage, -Preimage.Preimage2}`. |
| `local` (clones, lemmas) | nothing — names stay visible | |
| `lemma l &m (h : to) : Pr[ … ]` | `theorem l (m : VariableAssignment) (h : «to») : Pr[ … ]` | `&m` is an explicit memory argument. |
| `equiv l : M.f ~ N.g : P ==> Q` | `theorem l : equiv[ M.f ~ N.g : P ==> Q ]` | |
| EC lemma names | **verbatim** (E1), incl. `lemma1'`, `Real_GReal'` | Collisions with an opened namespace: qualify (`SHA3.Handle.eq_fi`). |
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
  Mathlib's token `C(` breaks `C(P)`: write `«C»(P)`.
* Variables: EC's `x{1}` is `§x{1}`; module variables `§G1.bcol{2}`; `={x, y}`, `={res}`,
  `={arg}`, `={glob A}`, `={glob A, glob B}` (one region, the join — don't split it).
* `glob C` of a **concrete** module = its variables (`C.c`, `C.queries`); of a declared/abstract
  module its footprint.  Closers read `={glob C}` as variable equalities.
* `Pr[ M(A, F).main (x) @ &m : §res ∧ §C.c ≤ max_size ]` is a real number (EC's `Pr` is real);
  bounds are written over ℝ with casts: `((bound + 1 : ℤ) : ℝ) * mu1 sampleto h`.
* EC's `x \in m` (maps) is `FMap.dom m x`; `m.[x]` is `FMap.get m x` (or `m.get x`); `oget`,
  `rng`, `fdom` are in `Lib/EC/FMap.lean` under EC's names.
* Parameter names in `hoare[ ]`/`phoare[ ]` are the procedure's; `arg` maps to `params`.
* `islossless M.f`.

## 4. Proof steps: EC tactic → Gaudí tactic

Prefixes: `equiv_*` (pRHL), `hoare_*`, `phoare_*`, `stmt_*` (any judgment).  Side `{i}` as in EC.

### Program logic

| EC | Gaudí |
|---|---|
| `byequiv` / `byequiv (_ : P ==> Q)` / `byequiv (H)` | `byequiv` / `byequiv (_ : P ==> Q)` / `byequiv (H)` |
| `byphoare (: P ==> _)` / `byphoare (H)` | `byphoare (: P ==> _)` / `byphoare (H)` |
| `have ->: Pr[…] = Pr[…] by …` (rewrite chain) | `calc` steps, or `have e : … := by …` then `simp only [e]` (`rw` on `Pr[ ]` goals often fails its instances-transparency check) |
| `proc` | `equiv_proc` / `hoare_proc` / `phoare_proc` (to the body, params as locals; EC's counts) |
| `inline*` | `stmt_inline*` (`hoare_inline*`, `phoare_inline*`) |
| `inline M.f` / `inline M₁ M₂` | `stmt_inline (M.f)` / `stmt_inline (M₁) (M₂)` (no `{i}`; parens needed) |
| `sp` / `sp n m` | `stmt_sp` / `stmt_sp n m` |
| `wp` / `wp n m` | `stmt_wp` / `stmt_wp n m` (EC positions; `-k` from the end). One-number `stmt_wp k` is *ours*: the last `k` statements |
| `auto` | `equiv_auto` / `hoare_auto` / `phoare_auto` |
| `skip` | `equiv_skip` / `hoare_skip` / `phoare_skip` |
| `if` / `if{i}` | `stmt_if` / `stmt_if{i}` |
| `rcondt{i} n` / `rcondf{i} n` | `stmt_rcondt{i} n` / `stmt_rcondf{i} n`, EC's positions; side goal first: `· hoare_auto; …` |
| `seq n m : P` (pRHL) | `equiv_seq n m : (P)` (leading counts, resets not counted). The old from-the-end cut is `equiv_seq_last` |
| pHL `seq n : E p₁ p₂ p₃ p₄ I` | `phoare_seq n : (E) p₁ p₂ p₃ p₄ (I)`; goals tagged (`invariant`, `first_E`, `first_notE`, `second_notE`, `bound`…), `_` bound allowed |
| `swap{i} n k` / `swap{i} [a..b] k` / `swap k` | `stmt_swap{i} n k` (1-based) / `stmt_swap{i} [a..b] k` / `stmt_swap{i}? [-]k` |
| `call (: inv)` (abstract adversary, Hoare) | `hoare_call (: inv)`; goals oracle(s) first, then pre |
| `call (_ : ={glob A, x…})` (abstract) | `equiv_call (_ : ={glob A, x, …})` |
| `call (_ : ={…} /\ I)` | `equiv_call (_ : ={…} ∧ I)` |
| `call (_ : bad, I, J)` (up to bad) | `equiv_call (_ : bad, I, J)`; EC's goal order; `D_ll`'s goal: `exact D_ll` (E11: right oracles' `islossless` is one more goal each) |
| `call (: P ==> Q)` (concrete callees, pRHL) | `equiv_call (_ : P ==> Q)`; callee's judgment first, then pre; the frame of unwritten variables is found |
| `call (_ : ={glob P})` (concrete callee) | `equiv_call (_ : ={glob P})` |
| `call H` | `equiv_call (H)`; `phoare_call H` (`?_` holes = EC's `call` subgoals) |
| `call{i} H` | `equiv_call{i} H / x, glob A` (frame listed) |
| `call (: P ==> Q)` in `phoare` / `hoare` | `phoare_call (: P ==> Q)` / `hoare_call (: P ==> Q)`; `phoare_call H / x, …` for lossless + frame |
| `sim` / `sim n m` / `sim (_ : I)` / `sim` with `={glob A}` | `sim` / `sim n₁ n₂` / `sim (_ : I)` / `sim / x₁, …, xₙ` (equal except the listed globals) |
| `rnd` / `rnd{i}` / `rnd f` | `equiv_rnd` / `equiv_rnd{i}` / `equiv_rnd f` |
| pHL `rnd (pred1 v)` / `rnd` (lossless) / `hoare` | `rnd_pred1 v` / `rnd_bound` / `rnd_null` (after `phoare_auto`) |
| `hoare` (phoare → hoare for a 0 bound) | `phoare_hoare` |
| `conseq (: P ==> Q)` / `conseq (_ : _ ==> Q)` / `conseq H` | `equiv_conseq (: P ==> Q)` / `equiv_conseq (: _ ==> Q)` / `equiv_conseq H` (also `hoare_`, `phoare_`); EC's frame of what the code keeps is kept |
| `exists* e₁{1}, e₂{2}; elim* => a b` | `equiv_exists* §e₁{1}, §e₂{2}` then `intro a b` (also on procedure judgments, `§x{2}` the parameter); `stmt_exists* e` |
| `case (P)` (pRHL) | `equiv_case (P)` |
| `case @[ambient]: {-1}(e) (eq_refl e) => [h₁ \| x h₂]` | `rcases h : e with _ \| x` (or `by_cases h : P`) |
| `exfalso` | `equiv_exfalso` |
| `while I` (two-sided) | `equiv_while (I)`; goals tagged `body`, `guard`, `exit`, `hpre` |
| `while{i} I V` | `equiv_while{i} (I) (V)` |
| pHL `while I V` (`= 1`) | `phoare_while I V` (then `intro k` in the body goal); `while_ll_phoare` for EC's `sp; rcondt 1; auto` on a lossless side goal |
| `splitwhile{i} n : e` / `unroll{i} n` | `stmt_splitwhile{i} n : e` / `stmt_unroll{i} n` |
| `alias{i} n x = e` | `stmt_alias{i} n x = e` |
| `transitivity{i} { code } (P₁ ==> Q₁) (P₂ ==> Q₂)` | `equiv_trans{i} { code } (P₁ ==> Q₁) (P₂ ==> Q₂)` |
| `symmetry` | `equiv_sym` |
| `fel n cntr step q bad [O.f : pre] inv` | `fel §cntr (fun i => step) q (bad) [pre] (inv)`; goals EC's order (`sum`, `init`, oracle `step`, `incr`, `same`, `keep`). Deviation: `bad` must persist; one oracle only so far |

### Goal management

| EC | Gaudí |
|---|---|
| `1,3: t`, `2..-2: t`, `-1: t` | `on_goals 1, 3 => t`, `on_goals 2..-2 => t`, `on_goals -1 => t` |
| `last first` / `first last` | `swap` / `rotate_right` / `rotate_left` |
| `n: t` (one goal) | Batteries' `on_goal n => t` |
| `t; t'` (on all subgoals) | `t <;> t'` |
| `+ …` / `- …` bullets | `·` |
| `=> //` | usually nothing (the tactics close trivial goals); else `<;> try trivial` |

## 5. Closers (EC's `smt`, `/#`, `move=>`, `progress`)

Closers are the bulk of the remaining manual work.  Order of attack:

1. **`auto_close`** — our `auto => /#`: intro, take hypotheses apart, substitute, reads through
   writes, `glob_simp`, split, `omega`/`simp_all`.  Closes or fails (never half-way).
2. **`smt_close [l₁, …]`** — EC's `smt(l₁, …)` (grind-based, reads generalized).  Try it **once**
   with EC's hint lemmas; on failure **do not tune grind** — write the proof (policy, Denis
   2026-11-08).  EC's provers see through definitions; ours don't: pass definitions to unfold
   (`prefix_inv`, `all_prefixes`) as hints.
3. **By hand**, with **EC's lemmas** (`lemma1'`, `huniq_hinvK_h`, `m_p_of_INV` …):
   `auto_prep` (normalizes: `norm_decide`, `subst_named`, `subst_reads`, `subst_vars`,
   `glob_reads`, simp of reads) then `rw`/`simp`/`refine lemma … ?_ ?_`.  For a lemma over plain
   values: `generalize_reads_all; subst_vars; apply lemma <;> assumption`.
4. If EC's inline closer is very long (100+ ssreflect lines) and the old port proved the same
   fact as a lemma, reusing it is acceptable — **as a documented deviation** (`eq_f`'s path case
   = `f_path_inv`).

Mappings for ssreflect idioms:

* `move=> &1 &2 [#] !<<- ->> h` → the closers do it (`subst_named` = `<<*`, `subst_reads` =
  `<<-`/`->>` for `read = name` or `read = (name, name)`); positional `move=> … ya ? yc ?` →
  `rename_i ya _ yc _` (a deviation; names are positional in EC's sense).
* `have /lemma [] h1 h2 := inv0` → `obtain ⟨h1, h2⟩ := lemma … inv0`.
* `rewrite domE Pmi_xaxc` → `simp [FMap.domE, Pmi_xaxc]`; `smt(domE)` → `smt_close [FMap.domE]`.
* `smt (@Block.DBlock …)` for losslessness → the `@[simp]` facts `bdistr_expected_one` etc.
  (state them once per file/library, `is_lossless_iff_expected`).
* EC's `smt()` on real arithmetic → `linarith`/`positivity`; bounds: `Lib/EC/StdBigop.lean`
  (`sum_Ico_const`, `sum_Ico_toNat`, `ofReal_intCast_mul_mu1`).
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
* Many variable pairs in restrictions (`{-PRPi, -ARP, -DBounder}`): `set_option
  synthInstance.maxSize 1024 in`.
* Probing a large goal: `trace_state` + `lake env lean file | grep` (the LSP may choke);
  `#count_heartbeats` misses async elaboration (`set_option Elab.async false in`);
  `lean_profile_proof` fails on same-file modules — use `set_option profiler true in`.
* Long proofs: `sorry` the later bullets while working on early ones; files outside the barrel
  are checked with `lake env lean`.

## 7. Known limitations and standing deviations

Document each in the docstring when it applies.

* **Inliner renaming**: an inlined callee's locals that clash with names in the conditions are
  renamed (`p`, `sa` → `p0`, `sa0` on side 2): EC's `={sa, p}` becomes `§sa{1} = §sa0{2} ∧ …`.
* **`rename_i`** for EC's positional intro names; `rcases h : e` for `case @[ambient]`.
* **E11**: the up-to-bad call wants the right oracles lossless (one more goal each).
* **`fel`**: one oracle; `bad` must persist (`keep` goal); the event must be `bad` itself.
* **`rw`** fails on goals with terms well-typed only by unfolding module types (`PRIMITIVE.f Perm`
  at a PRP type): use `simp only`.  Module types are not reducibly equal (making `moduletype`'s
  types `@[reducible]` is proposed, not done); instances like `Module.GlobBound` must be stated at
  the module type the lemmas ask for.
* **`@D_ll _ ?_ _ ?_`**: restriction holes of declared axioms are spelled out in `phoare_call`.
* **Regions**: `={glob A, glob B}` is one region (no join lemma — never split it); EC's
  `call (: true)` on init code is `equiv_call (_ : ={glob D, glob P})`.
* **`seq`/`proc` counts** match EC only with the EC tactics (`*_proc`, `equiv_seq`); the
  `*_proc_to_stmt` and `equiv_seq_last` forms are older and count differently.
* **Missing**: two-judgment `conseq (: _ ==> true) (: _ ==> Q)`; `rnd f g` (ours: `equiv_rnd f`,
  other side goals); `sim` over abstract calls with differing oracles (use `equiv_call` with the
  invariant); `bypr` (E12; collapses to `phoare_proc` before `fel`); multi-oracle `fel`.
* **Old-port declarations**: lemmas ported in EC form *over the old declarations* (Handle's
  `eq_f`) carry artifacts (`unfold CF`, `module_subtype SLCommon.PRIMITIVE <: DPRIMITIVE`, old
  invariant forms); they vanish when the declarations are re-ported.
* Closer scoping: `equiv_auto` uses `equiv_skip_ec` (decide-instance normalization, renamed-state
  fold); plain `equiv_skip` keeps the old behaviour that old hand-written proofs rely on.  Use the
  EC tactics in new proofs.

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
  `simpReadsDecls` broke PROM.
* `simp_reads` rewrites under `decide` but leaves the instance: `normDecide` re-synthesizes it.
* A namespace-local theorem shadows an opened one of the same name.
* Elaborators must run `withMainContext`; module steps inside simp callbacks at default
  transparency.
* Multi-line tactic quotations inside `( … )` fail to parse: bind sub-tactics with `let`.

## 9. Checklist before calling a lemma done

- [ ] Statement in surface syntax, EC's hypotheses only, EC's name; docstring quotes EC's
      statement and lists deviations.
- [ ] Proof: every EC step has a Lean step with the same arguments/positions; no glue (§0).
- [ ] Closers: `auto_close` / `smt_close [EC's lemmas]` / short hand proofs with EC's lemmas.
- [ ] No aux lemma beyond EC's (inline `have`s inline).
- [ ] Budget set per declaration with a reason; `sorry`-free; `lean_verify` shows standard axioms.
- [ ] `lake build` of the module green; full build + `Pilot/ConcreteF.lean` if infrastructure
      changed.
- [ ] `notes/SHA3/Refactor.md` (and `Mapping.md`) updated; `ec_fidelity.py` run.

## 10. Reference ports (read these first)

* Statements + `Pr` + `fel` + `phoare_seq`: `SecureRO.lean` (`RO_is_preimage_resistant`).
* Abstract calls, clones, `sim /`: `SecureORO.lean`, `IndifRO_is_secure.lean`.
* `declare axiom`, up-to-bad call, `equiv_sym`: `SLCommon.lean` (`Pr_restr`, `swap_restr`).
* Two-sided loops, `inline` by name, `equiv_seq`: `Sponge.lean`.
* Loops, `splitwhile`/`alias`/`conseq` frames, `sim (_ : I)`, `phoare_while`: `ConcreteF.lean`
  (`DoubleBounding`, `Real_GReal'`, `Real_Concrete`).
* Large invariant proofs with `exists*`, ambient cases, `rcondt`/`rcondf`, `swap` past calls:
  `Handle.lean` (`eq_fi`, `eq_f`, `CF_G1`) — compare with `Handle.eca` lines 1349–1800.
