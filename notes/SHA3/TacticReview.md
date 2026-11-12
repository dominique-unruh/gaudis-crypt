# Review of the EC-fidelity tactic layer (2026-11-12)

Scope: `GaudisCrypt/Logic/` as used by the pilots in `GaudisCrypt/Examples/SHA3/Pilot/`
(about 28k lines, 96 files, about 100 commits since 1 November).

Method: three independent reviewers read the code, the manual (`Pilot/TRANSFER_SKILL.md`), the
pilots and the git history, one area each, without being given any conclusions. Nothing was
built or run; claims are from reading, with inferences marked in the per-area notes below.
Section 5 is the first-hand list from the porting sessions, kept separate.

## 1. Verdict

The question was whether fixing one failing proof at a time converges. It does not, in three of
the four parts of the layer:

| Part | Converging? | Why |
|---|---|---|
| Statement rewriting (inline, swap, wp, splitwhile, unroll, the judgment registry) | Yes | One shared model, documented, the inliner has real output tests |
| Closers (`auto_close`, `smt_close`, `*_auto`, `sp`'s conditions) | No | No normal form for reads; a 29-step heuristic script whose output is consumed by position |
| Rules (`call`, `while`, `conseq`, `sim`, `rcond`) | No | Each rule has its own frame, dispatch and fallback; failures are silent |
| Modules, `glob`, frames | No | A concrete module has no record of its variables; each tactic re-derives them |

The semantic core underneath (footprints, the judgments, the rule lemmas) is not in question.

## 2. What all three reviews found independently

1. **Failure is silent.** A step that does not apply is skipped (`try`), or a weaker rule is used
   instead (`catch`), or a variable is dropped from a frame. The result is a sound goal that
   cannot be proved, discovered later in a closer. Examples: 12 `try generalizeReads … catch`
   sites; `equiv_call` falling from the framed rule to the frameless one on any exception;
   frame builders dropping a variable they cannot prove kept.
2. **Nothing pins behaviour.** Outside `InlineTest`, tests are small proofs that close; none
   fixes a tactic's goal count, order, tags or shape. The closers have no tests at all. The
   regression suite is the pilots, at minutes per file.
3. **One concept, several implementations.** Reads: about nine spellings and four notions of
   "the same read". Frames: four or five builders on three semantics. "The variables of M": six
   derivations. `equiv_call`: eight syntaxes in five files. Skip-and-generalize: five variants.
4. **Their first recommendation is the same: tests that pin output, before any redesign.**

## 3. Findings by area

### Closers and reads
- The same read can be `eval` with the state in an instance argument, `(Getter.mk …).get σ`,
  `x.get σ`, `X.get σ.globals`, `X.intoGlobal.get σ`, a read through a write or a renaming, or a
  generalized variable. Six partial normalizers exist; the target form is stated in one
  docstring and checked nowhere.
- `auto_prep` grew from about 10 to 29 `try` steps in five days, each added for one gap. About
  65 hand proofs consume its output by position (`rename_i` lists of up to 44 names) or by
  typed patterns.
- Results depend on whether a name is accessible, on context order, and on ambient hypotheses.

### Rules
- Frames are best-effort: the rule collects what the postcondition reads and tries to prove
  each variable kept. EasyCrypt keeps everything the code does not write.
- Positions: `ecGroups` is a sound model for resets but is re-derived in five places and not
  applied by `sim n m`, `stmt_sp n` or `stmt_wp k`.
- The inliner's output contract (callee locals named per side, parameter assignment, resets) is
  not specified, and downstream tactics compensate case by case.
- Old and new forms coexist (`equiv_if`/`stmt_if`, `equiv_while_raw`/`_noframe`), also inside
  the pilots.

### Modules, `glob`, frames
- `glob M` of a concrete module means different sets in conditions, in `{-M}`, in the abstract
  call with `bad`, in `fp_disjoint`'s hook and in `globTuples`' hook.
- `Logic/GlobWrites.lean` (lower bounds, added this week) exists only because `glob` of a
  concrete module is the footprint's getter and has to be turned back into variables. It does
  not cover functors (Gext GAP 8), variables only read, or modules that read more than they
  write.
- Hidden state: two process-global caches, one of which caches failures with no scope check; a
  hook installed only if a later file is imported; two elaborators for `fp_disjoint` chosen by
  import order. (Editor staleness from the caches is an inference, not tested.)

## 4. Recommended plan

Stop adding special cases. In this order:

**Phase 0: make changes visible (2–3 days, low risk).**
- Golden tests: one minimal goal per tactic and per gap already fixed, pinning goal count,
  order, tags and printed goal (`#guard_msgs`). About 30 for the closers, about 40 for the rules.
- Every pilot in the build, including unfinished ones (a second target next to the barrel), so
  no file is outside the check.
- Report instead of swallow: a frame that drops a variable the postcondition reads, and a rule
  that falls back to a weaker one, say so.

**Phase 1: reads and closers (about 1–2 weeks).**
- One normal form for reads, one normalizer, and a checker at the exit of every judgment
  tactic, so a violation fails where it is produced.
- A closer in two phases with a contract: (A) resolve frames and `glob`, generalize all reads,
  fail if a state survives, with deterministic accessible names; (B) pure closing.
  This replaces `auto_prep`'s script and the positional `rename_i` proofs.

**Phase 2: modules and frames (about 2 weeks, the largest change).**
- The `module` command records, per procedure, read variables, written variables and abstract
  callees, and proves the bound once.
- `glob` defined syntactically (the recorded variables, joined with the `glob`s of module
  arguments); the footprint only as its soundness proof. A declared module carries a region
  above its footprint. No lower bounds are then needed; `GlobWrites.lean` and Gext GAP 8 go away.
- One write-based frame function shared by `call`, `conseq`, `while`, `sim` and `swap`.

**Phase 3: rules (about 1 week).**
- One `equiv_call` front end that picks exactly one rule from a table; weaker rules only under
  explicit names. One statement-view API behind every position argument. Inliner output in
  EasyCrypt's shape (names chosen per side).

Decisions this needs:
- Phase 2 reverses the choice recorded in `notes/SHA3/GlobGranularity.md` §5 (2026-11-01) and
  touches `Syntax/ModuleSyntax.lean`; it needs Dominique's agreement.
- Whether the port pauses for Phases 0–1, or continues in parallel with manual proofs wherever
  a closer misses.

## 5. First-hand observations from the porting sessions (not independent)

- On 2026-11-12 three changes to shared closers each made one new proof pass and broke proofs
  in other pilots (`Gconcl`, `Handle`, `SecureRO`, `SecureORO`, `SHA3Indiff`); one of them (a
  tuple rule in `subst_reads`) was taken out again the same day.
- Commit `a2601fb` went in with `Pilot/SHA3Indiff.lean` broken: that file is outside the barrel,
  so the full build did not see it.
- The one change that was a real bug fix (`hoare_auto` generalizing reads before simplifying
  reads through writes) still changed goal shapes in two older pilots, because nothing pins
  what `hoare_auto` leaves.
- Where the closers miss, the manual proofs are short (a lemma application and `omega`), but
  they depend on hypothesis positions or on how a read is spelled.

## 6. Progress

### Step 1 done (2026-11-13): golden tests

66 tests in `Logic/ECAutoTest.lean`, `ECCloseTest.lean`, `ECRulesTest.lean`, `ECCallsTest.lean`,
all in the barrel; `scripts/update_golden.py` refreshes the expected text (it compiles under the
lakefile's `leanOptions`: a bare `lean` prints goals differently from the build).

### Step 2 done (2026-11-13): fallbacks report

`Logic/ECReport.lean`: `ECReport.fallback` (a warning; an error under `set_option ec.strict
true`) and the trace classes `ec.frame`, `ec.rule`, `ec.close`.  Converted: the un-generalized
reads (11 sites), the four rule fallbacks (`equiv_call H`, `equiv_call (_ : ={x})`,
`equiv_call (_ : … ∧ I)`, `sim`'s call), a nested failure that was logged next to a goal with a
`sorry` inside (now an exception), `rcond`'s unrolling (only on a loop); frames trace what they
keep and drop.  The frameless call rule has a name, `equiv_call_frameless`.

Measured on the full build (2841 jobs, green):

| Fallback | Fires | Where |
|---|---|---|
| Reads not generalized (the goal stays about states) | 81 | mostly `hoare_auto`, `phoare_skip`; 14 files |
| `sim`: no equality set for a call, all globals asked equal | 11 | `Pilot/IndifRO_is_secure` |
| `equiv_call (_ : ={x})`: frameless rule | 3 | `Pilot/Sponge` (2), `Pilot/ConcreteF` (1) |
| `equiv_call H`, `equiv_call (_ : … ∧ I)`: weaker rule | 0 | |

75 of the 95 are in pilot files.

All 81 un-generalized reads report the same failure (`generalize`: result not type correct).
Traced on one of them (`Pilot/SecureRO.lean:292`): a `decide (…)` whose `Decidable` instance
spells the read differently from the visible one; `norm_decide` first makes every read generalize
and the state disappear.  The relational `skip` (`equiv_skip_ec`) normalizes these instances
before generalizing; the Hoare and pHL paths do not.  The other 80 were not traced.

Not done from the inventory: the trace of `sp`'s choice of precondition form; letting errors
other than "no progress" through the best-effort simplifications (about 12 sites); keeping the
underlying error in reworded ones (about 8).

### Requirements for step 3 collected so far

1. The read normal form includes canonical `decide` instances, and it is applied on every path
   (Hoare, pHL, relational) before the reads are generalized: this alone accounts for the 81.
2. Changing that in place alters about 80 goals at once: the new closer goes in under a new name,
   pilots migrate file by file.
3. `sim`'s call case needs the write-based equality set (11 sites pass today only because their
   preconditions give all globals equal).

### Step 3, first two pieces (2026-11-12): the read normal form, `ec_skip`, `ec_auto`, `ec_intro`

`Logic/ReadNorm.lean` states the read normal form (atoms `x.get σ` / `X.get σ.globals`, no
expressions around reads, no reads through writes, canonical `decide` instances, regions of
variables read as variables) and has the one normalizer (`ReadNorm.normalize`: the existing four
steps, all of them, in one order), a checker (`ReadNorm.offenders`) and the strict skip:

    ec_skip     -- EC's `skip` on hoare / phoare / equiv; an error if a state survives

`Logic/ECAutoStrict.lean` builds EC's `auto` on it, for the three judgments:

    ec_auto     -- wp (and `rnd` on a relational judgment), then `ec_skip`, then the trivial closers
    ec_intro    -- the generalized values into the context under their own names

Old tactics (`hoare_auto`, `phoare_auto`, `equiv_auto`, the `*_skip` variants) are unchanged.
Golden tests: `Logic/ReadNormTest.lean`.

Trial migration, `Pilot/SecureRO.lean`: its 13 sites where `hoare_auto`/`phoare_auto` left the
goal about a state are now `ec_auto`.  All 13 generalize (no other cause than the `decide`
instances turned up in this file).  The hand steps after them changed from

    intro τ h;  … (RO.m.get τ.globals) … ((localVarLens "x" «from»).get τ) …

to

    ec_intro;  intro h;  … m1 … x …

i.e. they name values, not reads of a state.  The file has no fallback warning left.

Left in the pilot check after the trial (`lake build GaudisCrypt.PilotCheck`, green): 60
un-generalized reads, 48 of them in pilots (`SecureORO` 19, `Gext` 12, `Gcol` 7, `Handle` 6,
`ConcreteF` 4) and 12 in first-port files the pilots import.

Next: the `while` exit goals on the same normalizer; the remaining pilots file by file; then delete `auto_prep`'s script and the old skip variants when
their last user is gone.
