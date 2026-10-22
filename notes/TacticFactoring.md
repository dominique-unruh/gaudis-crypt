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

## Next

* Step 2: the deterministic part of wp on a shared core.
* Step 3: pRHL syntax; `prhl_left`/`prhl_right` as one descriptor per side (needs `stmtArg` to
  select the side's statement, and a transport lemma per side).
