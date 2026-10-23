# Factoring the program-logic tactics: judgment × step

Goal (from the 2026-10 discussion): one implementation per *step* (split, inline, wp, skip, …)
and one *wrapper* per judgment (`hoareStmt`, `phoareStmt`, later the two sides of a relational
judgment), instead of one implementation per pair; plus tactics that dispatch on the goal.

## Analysis

1. **Statement rewriting** (split, inline, flatten, later swap) changes only the statement, with a
   proof of `s.Equiv s'` / `s.EquivInLens s' l`.  Judgment-agnostic; the per-judgment part is the
   transport lemma (and how the transported conditions are cleaned).  **Done in step 1.**
2. **wp** is substitution for deterministic code (assignment, reset, `if`, sequencing) in every
   judgment — one lemma per judgment `J A (s; x <- e) B ↔ J A s B[x := e]` over a shared core.
   Sampling, calls and loops are genuinely judgment-specific (`∀ a ∈ support` / an exact average /
   a coupling; spec forms; invariant forms), as in EasyCrypt (`wp` generic; `rnd`, `call`,
   `while` per judgment).
3. **skip**: shared core ("the precondition implies the postcondition's relation", reads
   generalized), thin per-judgment wrapper.
4. Possible later shortcut: `hoare[A ==> B]` is `phoare[A ==> ¬B] = 0` (`hoareStmt_iff_phoareStmt`),
   so Hoare could be a view on phoare (for sampling, `expected = 0` ⇔ zero on the support).

## Step 1 (branch `judgment-registry`)

* `Logic/Judgment.lean`: `JudgmentDesc` — head constant, statement position, `equivLemma`
  (`J … s' … → J … s …` from `s.Equiv s'`), `transportLemma` (from `s.EquivInLens s' l`, one
  equation `(fun τ => C (l.get τ)) = C'` per condition), and `condSimp`/`condSimprocs` for
  cleaning transported conditions.  A persistent environment extension (`judgmentExt`,
  `registerJudgment`); the transport lemmas are applied by unification, the equivalence and
  the equations found by their types, so the number and order of a judgment's conditions do not
  matter.  Generic `Judgment.onStmt`, `Judgment.applyTransport`.
  (An `initialize`d extension cannot be used in its own file: judgments register downstream.)
* Registrations: `hoareStmt` in `Logic/TacticMisc.lean`; `phoareStmt` in `Logic/PHoareWp.lean`
  (with `condSimp := ewpDecls`, `condSimprocs := [reduceProcedureConst]`).
* Generic steps: `HoareSplit.hoareSplit` (= split for any registered judgment),
  `Flatten.judgmentInline`; `hoareOnStmt`/`phoareOnStmt`, `phoareSplit`, `hoareInline`/
  `phoareInline` are now aliases.  Dispatching tactics `stmt_split k`, `stmt_inline n`
  (`split`/`skip` are Lean tactics, and an `inline` keyword would break `@[inline]`); the
  prefixed tactics stay.
* Regression test: every hoare/phoare proof in the repository, plus `stmt_*` tests on both
  judgments in `Logic/PHoareWpTest.lean`.

## Step 2 (wp)

* `Stmt.Det d upd` (`Logic/Judgment.lean`): `d` runs as the state update `upd` (its wp of any
  postcondition is that postcondition after `upd`), with rules for `skip`, assignment (resets
  included), sequence and `if`, and the syntax-directed builder `Judgment.detOf?`.
* Descriptor fields: `postArg`; `detLemma` (`J A s (B ∘ upd) → J A (s; d) B` — one per judgment,
  the shared core); `sampleLemma`, `callLemma` (judgment-specific: `∀ a ∈ support` /
  average / symbolic call; Hoare has no call rule without a spec); `postSimp`, `postSimprocs`.
* `Logic/JudgmentWp.lean`: the driver `Judgment.wpStep k` — one statement at a time from the
  end, classify (deterministic / sampling / call), apply the registered rule, simplify the
  postcondition.  `hoare_wp`, `phoare_wp` and the dispatching `stmt_wp` are all this driver.
  Rules: `hoare_seq_det`, `hoare_seq_sample` (`TacticMisc`), `phoareStmt_seq_det`,
  `phoareStmt_seq_sample`, `phoareStmt_seq_call` (`PHoareWp`).
* The Hoare-only wp machinery (`hoareWpClose`, `hoareWpFull`, ~70 lines) is gone.
* Behaviour change: a deterministic `if` now updates the state conditionally, so the condition
  stays inside values (`(if b then 1 else 0) ≤ 1`) where the old Hoare rule split the
  postcondition (`if b then 1 ≤ 1 else 0 ≤ 1`); `Getter.get_ite`/`ProgramState.globals_ite`
  push reads into the conditional state.  One test adjusted (`QueryCounting.lean`).  An `if`
  whose branches sample or call is not handled generically (neither old tactic needed it in any
  proof); a per-judgment `ifLemma` would be the place for it.

## Step 3 (pRHL; branch `prhl-syntax`, off `judgment-registry`)

* The judgment: `prhlStmt A c₁ c₂ B` / `prhlProc A p₁ p₂ B` (`Logic/PRHLStmt.lean`) — the coupling
  judgment `ProgramDenotation.prhl2` (`Logic/PRHL2.lean`) at the denotations, so every coupling
  rule there applies.  Statement-level rules: `prhlStmt_seq`, `_skip`, `_case`, `_conseq`/`_pre`/
  `_post`, `.symm`; one-sided tails `prhlStmt_seq_left/_right` (lossless where the precondition
  holds — `kill_left'`), with the instances `_seq_det_left/_right` (`Stmt.Det`) and
  `_seq_sample_left/_right` (EC's `rnd{i}`); `prhlStmt_seq_sample f` (EC's `rnd f`, `f` may read
  both states); `prhlStmt_while`/`_seq_while`, `prhlStmt_if`; transport along `EquivInLens` per
  side (`prhlStmt_of_equivInLens_left/_right`); calls `prhlStmt_seq_call` (by a procedure
  judgment) and `prhlProc_glob` (EC's `call (_ : ={glob A})`, from `prhl2_glob`); the bridges
  `prhlProc_of_prhlStmt` (EC's `proc`) and `Procedure.Pr_eq_of_prhlProc`/`_le_`/`ewp_eq_`
  (EC's `byequiv`).
* The registry: `JudgmentDesc.side` (0 for a unary judgment, 1/2 for the sides of a relational
  one; the extension maps a head to its descriptors).  `descsOf`/`descOf g side?`/`forSides`;
  `onStmt`, `judgmentInline`, `wpStep` take an optional side.  Tactic syntax `{1}`/`{2}`
  (`Judgment.judgmentSide`): `stmt_inline{i} n`, `stmt_split{i} k`, `stmt_wp{i} k`; without a
  side, both sides in turn.  New: `stmt_wp` without a count = all trailing deterministic code
  (`Judgment.wpDet`, EC's `wp`), for any judgment.
* Inlining one side no longer avoids the *other* side's local names (separate states), so both
  sides of `main ~ main` inline to the same names (`j`, `b`, …) and EC's `={j}` reads naturally.
* Relational steps (`Logic/PRHLWp.lean`): `equiv_proc`, `equiv_rnd [f]`, `equiv_while I`
  (goals `body`, `guard`, `exit`, then the prefix), `equiv_call h`, `equiv_seq k₁ k₂ : M`,
  `equiv_case P`, `equiv_skip` (reads of both states generalized as `x₁`, `x₂`).  Relations in
  tactics are written like the judgment's conditions.
* Syntax (`Syntax/PRHLSyntax.lean`): `equiv[ P ==> Q ] { … } ~ { … }`,
  `equiv[ M₁ (x) ~ M₂ (y) : P ==> Q ]`; sided reads `§x{1}`/`§x{2}` and `={x, y}`, expanded at
  elaboration to `eval` at `CurrentState.mk σᵢ` (so the unary read machinery — `simpReads`,
  `generalizeReads` — handles them unchanged).  The statement form prints back (round-trip
  tests); the procedure form does not print yet.  The barrel `Syntax/Syntax.lean` does *not*
  import it (it pulls in `PRHL2` and its heavy imports); `Logic/PRHLWp.lean` does.
* The simp set for relational conditions `PRHLWp.relSimpDecls` = `simpReadsDecls` plus the trivial
  coupling facts (`bind_pure_id`, `uniform_bind_not`, `uniform_support`).  `id_eq` was added to
  `simpReadsDecls` (an `if` without `else` updates by `id`).

Added later the same night: `equiv_if` (both sides; `equiv_if{i}` one side, EC's `if{i}`,
`prhlStmt_if_left/_right`), `equiv_sym`, `prhlProc_refl` (EC's `call (_ : true)` on the same code),
`prhlProc.trans` (game hopping), `prhlProc_conseq`; the procedure form prints
(`equiv[ M₁ (x) ~ M₂ (y) : P ==> Q ]`, round-trip tests); simp facts for couplings and one-sided
samplings (`uniform_bind_add_left`, `uniform_bind_xor`, `uniform_expected_one`).  pHoare: a loop
rule for lower bounds with a variant, `phoare_while_ge I variant V` (`Stmt.ewp_while_ge_variant`),
for counted loops.  Examples: all of EC's `PIR.ec`; `Examples/OTP.lean` (perfect secrecy against
any adversary: `equiv_call prhlProc_refl _` for the adversary, `equiv_rnd (fun k => §m{1} + k)`).

Known gaps: no one-sided call/`while` (EC's `call{1}`, `while{1}`); `equiv_if` only on whole
statements (cut with `equiv_seq` first); no `sp`/`conseq` tactics (the lemmas
`prhlStmt_pre`/`_post` work with `apply`/`refine`); no `byequiv` tactic (the lemmas
`Procedure.Pr_eq_of_prhlProc`/`_le_` are one term).  `variant` is now a keyword (from
`phoare_while_ge … variant …`), hence the goal tag `decreases`.

Added 2026-10-24: `stmt_swap{i} n k` and `stmt_split_pair{i} n` (`Logic/StmtSwap.lean`, EC's
`swap`); `equiv_call` without argument (same procedure on both sides, `prhlStmt_seq_call_refl`);
`equiv_skip` generalizes bare globals to `globals₁`/`globals₂`.

## Friction points (to decide later)

Met while replicating Pedersen, ElGamal and hashed ElGamal (2026-10-24); not yet acted on.

1. **Statement positions are counted by hand.**  `stmt_swap{2} 6 -4`, `stmt_split_pair{1} 5`,
   `stmt_inline{1} 3` count from 0 over the flattened sequence, `reset_vars` lines included;
   every index was worked out by reading the printed goal.  Error-prone, and it breaks when the
   inliner's output changes.  Options: name the statement by the variable it assigns or the
   callee it calls (`stmt_swap y after choose`), or at least number the statements in the goal
   display.
2. **The inliner's `reset_vars` block swaps.**  Inlining resets the callee's locals on entry;
   EC's inliner does not.  A sampling of a same-named variable cannot move past such a reset, so
   the reset has to be moved out of the way first (an extra swap EC does not need — hashed
   ElGamal's `ddh1_es1`).  Options: a step that drops a reset whose variables are all written
   before they are read, or an inliner that renames instead of resetting.
3. **Tuple assignments need a manual `stmt_split_pair`.**  The inliner assigns a call's
   parameters as one tuple; EC assigns them one by one, and its swaps rely on that.  Options:
   split automatically when `stmt_swap` needs to move one component, or have the inliner emit
   one assignment per parameter.
4. **The equal-globals hypothesis appears twice** after `equiv_skip`
   (`globals₁ = globals₂ → … globals₁ = globals₂ ∧ …`), costing a `refine ⟨h, …⟩` per proof.
   Removing it would mean substituting equalities generally, which reshapes other goals (PIR).
5. **The swap discharger falls back to the full `simp` set** when the targeted one leaves a
   goal: robust, but less predictable and possibly slow on large programs.  Its specific lemmas
   (`Lens.set_outward`, `resetSetter_set_varLens`) had to be stated for the exact spellings the
   inliner produces (`liftLens X`; `VariableName.mk` literals, where a lemma about
   `(varLens v).intoLocal` does not fire).
6. **Counted wp steps fall short at the end.**  `phoare_wp k` must count statements exactly;
   in `gb_half` a trailing reset was left, hence `phoare_wp 6` followed by `stmt_wp`.  The
   uncounted `stmt_wp` (deterministic code only) and the counted per-judgment steps could be
   made consistent (e.g. `phoare_wp` without a count = everything, samplings included).
7. **Inline call sites are numbered by hand** too (`stmt_inline{1} 3` …), same issue as 1.

## Next

* Possible later: Hoare as a view on phoare (`hoareStmt_iff_phoareStmt`).
