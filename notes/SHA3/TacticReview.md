# Review of the EC-fidelity tactic layer (2026-11-12)

Scope: `GaudisCrypt/Logic/` as used by the pilots (the EC-fidelity port of SHA-3, then in
`GaudisCrypt/Examples/SHA3/Pilot/`; promoted to `GaudisCrypt/Examples/SHA3/` on 2026-11-15, and
the file paths below are the promoted ones)
(about 28k lines, 96 files, about 100 commits since 1 November).

Method: three independent reviewers read the code, the manual (`Examples/SHA3/TRANSFER_SKILL.md`), the
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
  (2026-11-13: Dominique prefers not to take over EC's `glob`; a smaller form is on trial, see
  "Step 4, tried another way" in §6.)
- Whether the port pauses for Phases 0–1, or continues in parallel with manual proofs wherever
  a closer misses.

## 5. First-hand observations from the porting sessions (not independent)

- On 2026-11-12 three changes to shared closers each made one new proof pass and broke proofs
  in other pilots (`Gconcl`, `Handle`, `SecureRO`, `SecureORO`, `SHA3Indiff`); one of them (a
  tuple rule in `subst_reads`) was taken out again the same day.
- Commit `a2601fb` went in with `SHA3Indiff.lean` broken: that file is outside the barrel,
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
| `sim`: no equality set for a call, all globals asked equal | 11 | `IndifRO_is_secure.lean` |
| `equiv_call (_ : ={x})`: frameless rule | 3 | `Sponge.lean` (2), `SmartCounter/ConcreteF.lean` (1) |
| `equiv_call H`, `equiv_call (_ : … ∧ I)`: weaker rule | 0 | |

75 of the 95 are in pilot files.

All 81 un-generalized reads report the same failure (`generalize`: result not type correct).
Traced on one of them (`SecureRO.lean:292`): a `decide (…)` whose `Decidable` instance
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

Trial migration, `SecureRO.lean`: its 13 sites where `hoare_auto`/`phoare_auto` left the
goal about a state are now `ec_auto`.  All 13 generalize (no other cause than the `decide`
instances turned up in this file).  The hand steps after them changed from

    intro τ h;  … (RO.m.get τ.globals) … ((localVarLens "x" «from»).get τ) …

to

    ec_intro;  intro h;  … m1 … x …

i.e. they name values, not reads of a state.  The file has no fallback warning left.

Second file, `SecureORO.lean` (19 sites): 18 generalize as they are.  The 19th, the
`skip` after a `phoare_call`, showed a second cause: an `if … then … else` whose instance is not
synthesized (`instDecidableAnd` over a classical part) and still spells the read through the
state the call rule built.  `ReadNorm.normInst` now re-makes the instance of every `decide` and
`if` along the instance's own structure (golden test "The instance of an `if`").

Remaining pilots (`Gcol` 7, `Gext` 12, `Handle` 6, `ConcreteF` 3): 28 sites, all generalize
with the normalizer as it is; four hand steps are closed by `ec_auto` itself.

### Step 3, third piece (2026-11-13): strict mode in the pilots

`set_option ec.strict true` at the top of every pilot that uses the tactic layer (12 files).
It means two things:

* a fallback (`ECReport.fallback`) is an error, not a warning;
* a goal that an old rule or closer leaves about the states (`while`/`if` exits, side goals,
  `hoare_auto`, the `*_skip`s) and whose reads do not generalize gets its instances normalized
  (`TacticMisc.normInst`) and is tried again.  A goal whose reads generalize as they are is not
  touched (normalizing at every exit timed out in `SmartCounter/Gconcl.lean`).

Files without the option behave as before.  The option is switched off, in the source, at the
six places where a rule falls back today (`set_option ec.strict false in …`):

| Where | Fallback |
|---|---|
| `IndifRO_is_secure.lean` (3 `sim`s, 11 calls) | no equality set for a call, all globals asked equal |
| `Sponge.lean` (2), `SmartCounter/ConcreteF.lean` (1) | `equiv_call (_ : ={x})` on a concrete callee: frameless rule |

Pilot check green.  Un-generalized reads left: none in the pilots; 12 in first-port files the
pilots import (`SmartCounter/Gconcl_list` 7, `SmartCounter/SLCommon` 2, `SmartCounter/ConcreteF`
1, `Lib/EC/Strong_RP_RF` 2), which stay on the old behaviour.

Still to do in step 3: `auto_prep`'s script and the positional `rename_i` proofs (the closer in
two phases); deleting the old skip variants needs the first-port files above migrated or retired.

Seen while migrating, changed on 2026-11-14 (below):
- The generalized values were named after the variable's last name component, numbered on a
  clash: with a memory `m` in the context `RO.m` was `m1`, and the local `m1` then `m11`.
- `ec_skip` printed a place under a binder with a loose index (`#1`).

### Step 3, fourth piece (2026-11-14): names, and the closer on values

Decided with Denis on 2026-11-13: no bulk rewrite of the 69 `auto_prep` sites of the pilots
(11 of them followed by `rename_i`; the rest go on with `refine`/`exact`/`simp`).  They stay on
the old tactics and move only when edited.  New proofs use the strict tactics.

* **Names** (`TacticMisc.readValueNames`): the variable's name; where it is taken (context, or
  another read) a module's variable is named with its module, `RO_m`, `RO_m₁`.  A name no longer
  depends on a number for the usual clash (a memory `m`, two modules' `m`).  Golden tests in
  `Logic/ReadNormTest.lean` ("The names of the values").  `SecureRO.lean` and `SecureORO.lean`
  followed (`m1` → `RO_m`, `m11` → `m1`).
* **`ec_skip`'s message** names a place under a binder with the binder's variable.
* **The closer on values** (`Logic/ECProgress.lean`, tests `Logic/ECProgressTest.lean`):
  `ec_values` (a goal `∀ σ, P` about states: every read a value, an error if a state survives),
  `ec_prep` (`ec_values`, then the steps of `auto_prep` that are logic: introduce — values under
  their names — take apart, substitute, simplify the tests), `ec_progress`, `ec_close`.  No step
  after `ec_values` looks at a state.  This is the two-phase closer of the plan, under new names;
  `auto_prep`, `auto_progress`, `auto_close` are unchanged.

What stays open in step 3: deleting the old skip variants and `auto_prep` (their users are the
first-port files and the pilot proofs written before 2026-11-13).

### The port on the strict tactics (2026-11-14): `SmartCounter/Gconcl_list.lean`, section `Ideal`

Six lemmas of `Gconcl_list.ec` (lines 334–964: `Ideal_equiv_valid`, `ideal_equiv2`,
`Ideal_equiv3`, `equiv_L3_L4`, `equiv_L4_ideal`, `equiv_ideal`), about 440 lines of EC script,
written on the new tactics only.  The numbers, against the one lemma of the file written before
(`ideal_equiv`, on the old tactics):

| | `ideal_equiv` (old tactics) | the six new lemmas |
|---|---:|---:|
| `-- EC:` blocks | 39 | 203 |
| `equiv_auto` / `hoare_auto` | 55 | 0 |
| `ec_auto` | — | 210 |
| `auto_close` / `auto_progress` | 27 | 0 |
| `ec_close` / `ec_progress` | — | 112 |
| `auto_prep` + `rename_i` | 3 + 6 | 0 |
| `ec_prep` (before a hand step) | — | 37 |
| `smt_close` | 21 | 12 |
| tactic fallbacks (strict mode) | 0 | 0 |
| `sorry` | 0 | 0 |

What this shows:

* **No positional proof**: not one `rename_i`.  A hand step names values (`x₂`, `F_RO_m₂`) and
  takes hypotheses by type (`‹inv_L_L3 _ _ _›`).
* **Every position of EC's script is EC's** (`rcond`, `wp n m`, `rnd{1}`, `seq`, `splitwhile`,
  about 90 position-taking steps), after one fix (`stmt_splitwhile`, below).
* **Hand steps are EC's `smt` calls**: where EC writes `smt(lemma1 parse_valid …)` the port
  applies those lemmas by hand, a line or two each.  `smt_close` was tried once per kind of goal
  and kept where it worked (12); with `parseK`-like hints it fails on an unknown free variable
  (`ec_instances`, known).

Changes to shared tactics made on the way, each with a golden test and none to make one proof
pass that the tactic's specification did not already promise:

| Change | Why | Test |
|---|---|---|
| `equiv_call (_ : ={glob M₁, …})`, only `glob`s, declared callee | had no rule (an error) | `ECCallsTest` |
| `ec_prep`: `(x, y) = e` ↦ `x = e.1`, `y = e.2` | what EC's `sp` leaves for `(x, y) <- e` | `ECProgressTest` |
| closer: states bound further in become values | `while`/`conseq` final memories were introduced as states | `ECProgressTest` |
| closer: reads of a memory in the context become values | the other side's memory in a one-sided `rcond` side goal | `ECProgressTest` |
| value names: module further out on a clash | `F.RO.m` and `F2.RO.m` were `RO_m`, `RO_m1` | `ReadNormTest` |
| `stmt_splitwhile` re-associates | the two loops were one block: positions after it off by one | `ECLoopTest` |

Gaps found and not fixed (worked around in the proof, listed in the pilot's header as GAP 3–7):
`glob M` of a concrete module in a `while` invariant stays a region; `equiv_conseq`'s frame over
a procedure that writes nothing; EC's `call (: I)` on two different concrete procedures has no
one-condition form; the frame of a call is the module's, not the procedure's; `hoare_conseq` and
the Hoare `while` have no frame.  The last three are rule gaps of the kind of step 5.

**Section `Real` (2026-11-13).**  The port did not need new declarations to go on: what stopped
`equiv_sponge` was the first port's alias `P` (`abbrev P : BlockSponge.PRIMITIVE := Perm`), which
`inline*` does not open.  EC's `module P = Perm` is an alias EC itself unfolds, so the statement
is written with `Perm`, with one `module_subtype` for `SqueezelessSponge(Perm)`, and
`glob P` as `Perm.m, Perm.mi` (GAP 3, as for `IF`).  Step 4 (`glob`) would turn the two maps
back into `glob P`; nothing else of section `Real` waits for it.

`equiv_sponge` (EC lines 1100–1434, 335 lines) is done on the strict tactics: 45 `-- EC:` blocks,
28 `ec_auto`, 29 `ec_close`/`ec_progress`, 6 `ec_prep`, 3 `smt_close`, no `rename_i`, no fallback,
no `sorry`.  The leaves `ec_progress` leaves are closed by hand with EC's lemmas (`smt_close`
was tried on four: three closed, one failed and is by hand).  What is new in it:

* EC proves the same five facts on `Redo.prefixes.[take (i+1) p <- v]` in both branches of the
  permutation's test (by `smt` and by hand, about 50 lines), and the fact "this prefix of
  `format p (i+1)` is known" at each `rcond` of the two inner loops.  Here each is a lemma stated once before
  the theorem (`absorb_*`, `squeeze_known_*`), and the leaves are one `exact` each.  This is the
  one place where the Lean proof is not EC's line for line; EC's lines are kept as comments.
* `Lib/EC/ListLemmas.lean`: EC's `List` lemmas the script cites (`take0`, `take_le0`,
  `take_oversize`, `size_take`, `nth_take`, `size_cat`, `size_nseq`, `nth_nseq`, `take_cat`,
  `last_cat`, `last_nseq`, `nth_last`, …), with EC's names and statements.  They were missing, or
  in first-port files under other names (`size_take'`, `nth_take_of_lt`).
* Gaps (pilot header, GAP 8–10): two states known equal by components only after `sp` over a
  pair assignment; the guard of a split loop `(a && b) = true` left as it is by the closer (third
  lemma where this costs a `simp only … at *; omega`: a candidate for `ec_prep`'s set, with a
  golden test); no `seq` on a Hoare triple; `splitwhile`'s condition does not see a variable
  that is only in the conditions; a goal prints as the plain term right after `sp`.
* No shared tactic was changed for this lemma.

`squeeze_squeezeless` (EC lines 1493–1744) and `pr_real` complete section `Real`:
35 `-- EC:` blocks, 32 `ec_auto`, 24 `ec_close`/`ec_progress`, 7 `ec_prep`, no `smt_close`, no
`rename_i`, no fallback, no `sorry`.  The same pattern as `equiv_sponge`: five plain lemmas for
facts EC proves inline at each use (`INV_Real_known_step` stands for a seven-line script EC
repeats five times).  One new gap: `inline*` leaves `Sponge(Perm)`'s calls of the permutation
behind the first port's `PRIMITIVE.view` (`Flatten.moduleStep?` keeps a record of another module
type closed, for the first port's proofs), so the proof has one bridge line,
`simp only [P_view]`.  The fix is an opt-in option of `inline` for the pilots, with a golden
test; it touches `Logic/Inline.lean` (a rebuild of everything), so it waits for a batch with
GAP 9 (`ec_prep` on split-loop guards) and the Hoare `seq`.

**Sections `Real_Ideal`, `Real_Ideal_Abs` (2026-11-13): what waits, and for what.**
`A_lossless` and `Neg_D_lossless` are done (EC's scripts, `phoare` tactics).  The rest waited for
three things, none of them a proof step:

* `concl` applied `Gconcl.Real_Ideal` to `A(D)` and waited for step 4: **done**, see "Step 4,
  tried another way" below.  `neg_D_concl`, `Inefficient_Real_Ideal` and the final `Real_Ideal` now wait
  only for the two lemmas below (`concl (Neg_D(D))` is the same application, with the region
  `glob D`).
* `Real_lossless`: EC's `call (: invm Perm.m Perm.mi)` on the abstract `D` in a `phoare … = 1`
  goal.  `phoare_call` has the rule for lossless oracles only.  (The first port avoided the
  invariant: `Perm.f` is lossless unconditionally; that is not EC's script.)
* `Ideal_lossless`: loops followed by sampling code in `phoare … = 1`; EC's `auto` passes the
  code after the loop, our `phoare` tactics have no such step.  One of its three oracles is done
  in a draft (not in the file).

Independent of all three: section `Simplify_Simulator` (EC l. 2008–2195).  Its local clone
`IRO2` is declared in the pilots' style (`global_var`s, where the first port has a lens
parameter with eighteen disjointness hypotheses); `L` is an alias.  `equal2` is done (EC's 25
lines; three new gaps, 14–16: `glob D` past initializations after `skip`, EC's bare `conseq`,
`sim` over differently named locals).  `equal1` (75 lines) and `Simplify_simulator` are done
(2026-11-13).  `equal1` follows EC's script; the fact EC derives inline three times is one plain
lemma; EC's proof that the last query is already sampled (`splitwhile`, two `rcond`s and `seq` on
a Hoare triple) is a loop invariant here, since there is no `seq` on a Hoare triple (GAP 9).
`Simplify_simulator` is EC's two lines, with two bridges from the alias `L` to the first port's
module `L D`, which `RO_LRO_D` takes (E5).

**`Gconcl_list` complete (2026-11-13).**  The last five lemmas, none needing a new tactic:
* `Ideal_lossless`: GAP 13 was not a missing step.  EC's `auto` passes the sampling behind the
  loop; `phoare_auto` does too and leaves `cdistr.expected fun _ => 1` as the postcondition,
  which `simp only [cdistr_expected_one]` turns back into `1` before `phoare_while`.
* `Real_lossless`: hand-closed (GAP 12 stays).  EC keeps `invm Perm.m Perm.mi` through the call
  of `D`, because EC's permutation samples losslessly only under it; here `Perm.f`, `Perm.fi`
  are lossless in every state, so the call is EC's `call (: true)`.
* `neg_D_concl`: `concl` applied to `Neg_D(D)` with the region of `D` (the second use of the
  region form).  Since 2026-11-20 EC's script with `AdvAbsVal` (GAP 17 closed).
* `Inefficient_Real_Ideal`, `Real_Ideal`: EC's lines.
All of section `Real_Ideal_Abs` and the last section declare `D` with a region, since
`SHA3Indiff` applies `Real_Ideal` to `LowerDist(Dist)`.

**Step 4, tried another way (2026-11-13): no syntactic `glob`; a region where `glob F(A)` is
needed.**  Dominique's concern: EasyCrypt's `glob` system may be inconsistent, and taking it over closely
is dangerous; where `glob F(A)` is needed, write `glob F` and `glob A` explicitly.  A lemma about
a module variable `D` cannot have `glob D` rewritten at its use, so the lemma takes it as a
parameter: `declare module D <: T {-…} with glob R` declares a region `R` above `D`'s footprint,
restricted like `D`, and `D_ll` restricts its oracles against `R` (`{-R}`).  The application to
`A(D)` gives `R ⊔ C.c.footprint`.  Every region is checked against the footprint by a proof;
nothing is read off EasyCrypt's `glob`.  This is exception E14 in the pilots
(`notes/SHA3/Exceptions.md`).  If the trial is kept, Phase 2's "`glob` defined syntactically"
is dropped.

What it took:
* `Logic/FootprintSolver.lean`: the class `Footprint.Restricted R S`, read by `fp_disjoint` as a
  restriction hypothesis; one more rule (an abstract module against a region).
* `Logic/DeclareModule.lean`: the command, `{-R}` in restrictions, the weakening instances (as a
  declaration's), `Footprint.FinitelySupported.glob`.
* `Logic/ECCallUpto.lean`: the up-to-bad call states `D_ll` against the region of a module that
  has one (`Module.ECGlob`); for every other module the goal is as before.
* Golden tests in `Logic/ECCallsTest.lean`.
* The pilots: two lines in each of six sections (`SLCommon`, `ConcreteF`, `Handle`, `Gext`,
  `Gconcl`, `Gconcl_list`), one instance generalized (`D'(D)`), one added (`A(D)`), no proof
  changed.  `concl` is EC's five lines; the region is written at the one application.

Still to come with the same form: `SHA3Indiff`'s `security` (`Real_Ideal` of `Gconcl_list` at
`LowerDist(Dist)`), `SHA3Security` (three `SHA3Indiff (DSetSize(…(A)))`, one
`Sponge_coll_resistant`), `SHA3OSecurity` (three), `SHA3_OIndiff` (one).

**The batch of rule fixes this port has collected** (each small, each with a golden test; the
first needs a full rebuild, so they go together):
1. `inline`: an option to open a record of another module type (GAP 11).
2. `ec_prep`: the guards of split loops, `(a && b) = true/false`, and `decide p = !false`
   (GAP 9; met in three lemmas).
3. `equiv_conseq` without a specification, EC's `conseq=> />` (GAP 15).
4. `skip`: `glob D` past writes outside `D`, as `sp` does (GAP 14).
5. `seq` on a Hoare triple (GAP 9); `splitwhile` reading the conditions' variables (GAP 10).
6. `phoare_call` with an invariant on an abstract module (GAP 12; `Real_lossless` is
   hand-closed without it).  (GAP 13 needed no step: `phoare_auto` and one rewrite.)
7. `smt_close`'s unknown free variable in `ec_instances` (GAP 2).
8. `sim` over differently named locals (GAP 16); pair states equal by components (GAP 8).
   **First half done 2026-11-21**: `sim`'s third loop attempt pairs the locals at corresponding
   positions of the two loops (`loopInvPairs`, EC's equality set of pairs; an EC probe showed
   EC's inliner also renames per side and its `sim` relates them).  The invariant is an
   equality set (pairs, the same-name variables the loops need, the equalities of the relation
   after them), not that relation.  Closed: Gconcl_list GAP 16 (both sites), SHA3Indiff GAP 2,
   two of SHA3_OIndiff's three.  Open: a relation after the loops that relates differently
   named variables through terms (`f x0{1} = f x1{2}`, SHA3_OIndiff's third site), which EC's
   `sim` leaves as its goal.  Also fixed: the `sim` elab ran outside the goal's context
   (`withMainContext`), so a relation mentioning intro'd locals failed silently.
9. EC's theory `AdvAbsVal` (`Neg_main`, `Neg_A`, `Neg_A_Pr`, `Neg_A_Pr_minus`): a small library
   file; needs `proc *` and `Pr[mu_not]` (GAP 17).  **Done 2026-11-20** (`Lib/EC/AdvAbsVal.lean`;
   `proc *` is `equiv_proc_to_stmt`, `Pr[mu_not]` is `Pr_mu_not`; on the way: procedure modules
   typed by an abbreviation, `byphoare Hl` with `Hl : islossless p`, `fp_disjoint` against `⊥`).
10. From `Sponge.lean` (its GAP 2–5): EC's path for a callee inside a library procedure;
   reads through a discarded call result in the strict `auto`; the oracle goals of an abstract
   call in the module's own procedure names, and only for the procedures the module type's
   `{…}` allows; `equiv_conseq H` closing its implications.

11. From `Sponge.lean`, the second half of `HybridIRO` (its GAP 6–13): the strict `auto` on a
   one-sided loop body whose invariant reads the other memory, and on a `skip ~ skip` goal with
   `bs{1} = take n1 bs{2}` next to `={bs}` (both run out of recursion depth); the frame of a
   one-sided loop's exit goal covering what the invariant reads; `transitivity N (…) (…)` on
   procedures as a tactic (the rule is `prhlProc_trans_ec`); a first-port fact about
   `X.f.procedure` fitting `equiv[ X.f ~ … ]`; `={bs}` in a condition of `equiv_trans` when
   the goal's two sides have a `bs` of different types; `sim` through an inlined call that
   copies its parameters and has a loop; `omega` on a guard's read against the invariant's.

**Added without waiting for the batch** (new names in new files, no existing tactic touched):
`equiv_conseq (: P ==> Q) _ (: P₂ ==> Q₂)`, EC's `conseq (_ : P ==> Q) _ (_ : P₂ ==> Q₂)`
(`Logic/ECConseqHoare.lean`, rule `prhlStmt_and_hoare_right`, test
`Logic/ECConseqHoareTest.lean`); used once, in `HybridIROEager_f_BlockIRO_f`.  In the same
file, `equiv_conseq_pre H`: EC's `conseq H` on procedures with `post` under the precondition
(rule `prhlProc_conseq_pre`); used once, in `HybridIROEager_BlockIRO_f`.  In the batch,
`equiv_conseq H` itself should state `post` so, and the side goals over parameters and results
should come in read normal form at the plain types.

Also added (2026-11-14, `Logic/ECProcInv.lean`, test `Logic/ECProcInvTest.lean`):
`equiv_proc (I)`, EC's `proc (I)` on an abstract procedure (a declared functor with one
procedure by the rule of `equiv_call (_ : I)`; any other by a rule tagged `@[proc_inv]`), and
`equiv_conseq_frame H`, EC's `conseq H` on procedures with EC's frame (rule
`prhlProc_conseq_frame`), which reads the goal's procedures off their module views, recognises a
procedure named differently from `H`'s by its body, and closes the implications that
simplification closes (with `={glob A, glob B}` giving `={glob B}`).  In the batch:
`equiv_conseq H` should become this one; `fp_disjoint` should find the finite support of a join
of regions itself (the tactic hands it over, `withFiniteRegions`); a concrete procedure's
footprint should be read off its code also for the first port's lens-parameterised modules (now
`@[fp_bound]` lemmas by `fp_module`).

The same file gives EC's `call (_ : I)` on a procedure with a rule
(`equiv_call (_ : ={glob M, …} ∧ I)` on a simulator's `init`, by `SIMULATOR.call_init`).  Two
more items for the batch, from the last lemmas of `Sponge.ec`: `sim` should take an equality set
made of a `glob` region and variables (GAP 15 of `Sponge.lean`; it needs "equal on a
region and on a variable outside it" as "equal on their join"), and `swap` past a procedure
whose oracle list is a hypothesis about its behaviour needs a semantic check, not the footprint
of its code (GAP 14).

## The final section of `Sponge.ec` (EC l. 1913–2163): decisions (2026-11-14)

The three questions below were decided as follows.
1. and 2. **One hypothesis**: the section assumes `SIMULATOR.Representable BlockSim` (the first
   port's exception E2), which is EC's module type with its oracle lists: `init` calls nothing,
   `f` and `fi` call `F.f`.  The init equation alone was not enough: no abstract call rule
   applies to `BlockSim(F).f` without the representation, and `declare module` gives one only
   for a functor with one procedure.  The two sites then read as EC's with `equiv_proc (I)`;
   the first version, the first port's rules applied by hand (about 50 lines for EC's six), was
   dropped.  Still open for the framework: oracle lists in `moduletype`/`declare module`, or the
   representation derived from the module calculus (a projection functor composed with the
   simulator), either of which removes the hypothesis.
3. **Footprints**: `fp_module` proves them; the failure was an `omit [BlockSponge.Params]` (the
   first port's unfolding lemma takes the instance).  Stated as `@[fp_bound]` lemmas.

## The final section of `Sponge.ec` (EC l. 1913–2163): what was open

Done in `Sponge.lean`: the section's two declarations (`BlockSim … with glob R`, `Dist`
restricted against `R`) and `RealIndif_Sponge_BlockSponge` (EC l. 1953).  The ideal side is the
first place the pilots meet an **abstract simulator** (`BlockSim <: BlockSponge.SIMULATOR`, a
declared functor whose result is a record of three procedures), and three things are missing.
They are decisions about the framework, so nothing was built for them:

1. **`proc init() : unit { }`** — EC's module type says `BlockSim(F).init` calls no oracle, and
   `call (_ : true)` on it (EC l. 1983, 2034, 2049, 2110) uses that: the two sides give
   `BlockSim` different functionalities.  `declare module` has no per-procedure oracle
   restriction (for `HYBRID_IRO_DIST`'s `{HI.f}` the missing restriction only cost one more
   goal, GAP 4; here the extra goal is false).  The first port carried a hypothesis
   (`SIMULATOR.ECModule`, exception E2).  Options: a section hypothesis in the pilot
   (`∀ F F', BlockSim(F).init = BlockSim(F').init`, stated once, read as the module type's
   `{ }`), or oracle restrictions in `moduletype`/`declare module`.
2. **`proc (I)` on an abstract procedure under an abstract call** (EC l. 1990–1997,
   2117–2122): `Dist`'s oracle `P.f` is `BlockSim(F).f`, itself abstract with oracle `F.f`.
   `equiv_proc_to_stmt` turns the procedure judgment into one about the call, and
   `equiv_call (_ : I)` then applies in principle; it was not tried to the end, because with
   `={glob BlockSim}` named the oracles' goals keep the region `glob Dist ⊔ glob BlockSim`, and a
   proven lemma about concrete procedures (`LowerFun_IRO_HybridIROLazy_f`) then needs a frame
   step that the rule does not do through the first port's records (same reason as below).
3. **Footprints of the first port's lens-parameterised procedures** (`HybridIROEager.f`,
   `BlockSponge.BIRO.IRO.f`): `fp_module` proves the bound for `fill_in` but stops at a
   procedure that calls another one of these ("no concrete procedure body").  Without the
   bound, `call (HybridIROEager_f_BlockIRO_f n' xs2)` in
   `RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f` (EC l. 2070) has no frame for
   `={glob BlockSim}`.

Smaller findings from `RealIndif_Sponge_BlockSponge`:
* `equiv_call (_ : ={glob Perm})` on the abstract `Dist` falls through to the older rule's error
  (`the oracles' variables`); the glob-only rule of `Logic/ECCallUpto.lean` fails first and its
  error is not shown.  Written as an invariant, `equiv_call (_ : §Perm.m{1} = §Perm.m{2} ∧
  §Perm.mi{1} = §Perm.mi{2})`, the oracles' goals are EC's.
* A `seq` cut `={glob Dist, glob Perm}` generalizes the joint region to one value, unrelated to
  `Perm.m`, `Perm.mi`: written `={glob Dist, Perm.m, Perm.mi}`.
* `RaiseSim(S)` is `Module.comp S LowerFun`; a call of `RaiseSim(BlockSim, F).init` is seen as
  `BlockSim`'s after `simp only [RaiseSim, Module.app_comp]`.
* A declaration restricted against another module's region (`{-R}`) is an instance that mentions
  `R`: `include R`, or lemmas that do not mention the other module lose the instance.

## `SHA3Security.ec`, section `Preimage` (2026-11-14): findings and one batch of changes

Decisions taken alone while porting `Sponge_preimage_resistant` (EC l. 392–475).  The low-level
changes (1–3 and 8) were made in one batch, each with a golden test (`Syntax/CloneTest.lean`,
`Logic/ECProcInvTest.lean`, `Logic/PHoareSeqTest.lean`).

1. **`clone` copies the theory's `*.congr_simp` theorems** (`Syntax/Clone.lean`, `Clone.skip`):
   `S.DPre.h.congr_simp` is an alias whose statement is about the theory's `DPre.h`.  When simp
   wants the congruence lemma of the clone's constant it finds that name in the environment,
   without the entry of Lean's own table, and prints `PANIC at Lean.Meta.mkCongrSimpForConst?
   … unreachable code` (hundreds of lines with backtraces; the proofs still check).  Seen with
   `fp_module` through `DPre(A)` and in every `byequiv` of the section.  Fix: `skip` also skips
   `isReservedName env n` (Lean's auto-generated names: `congr_simp`, `eq_def`, `eq_unfold`, …),
   and each alias of a definition is registered for them (`enableRealizationsForConst`), so
   that `C.x.congr_simp` is Lean's own lemma about `C.x`, in the clone's file too.
2. **A module without globals** (`CSetSize(Sponge)`, bound `⊥`) has no `Footprint.Outside ⊥ S`
   instance, so `Module.Declared.ofGlobBound` does not apply: instance `Footprint.Outside.bot`
   in `Logic/DeclareModule.lean`.  With `Module.GlobBound`
   instances for `CSetSize Sponge`, `Perm`, `SimSetSize Simulator` *at the clone's module types*
   (`@Module.GlobBound Indiff0.PRIMITIVE _ Perm …`), EC's
   `rewrite (preimage_resistant_if_indifferentiable A A_ll (CSetSize(Sponge)) Perm &m ha init_ha)`
   is `refine S.preimage_resistant_if_indifferentiable A (CSetSize Sponge) Perm m ha init_ha ?_`
   and `exists (SimSetSize(Simulator))` is `refine ⟨SimSetSize Simulator, inferInstance, ?_, ?_⟩`:
   the restrictions are found by instance search, as EC checks them.
3. **`call H` where the calls spell the callees differently from `H`** (the game calls
   `(RF.mk { get := FInit(…).get }).get`, a functor has unfolded a view): `equiv_call (H)`
   compared the two up to definitional unfolding, which does not decide it for modules.  New
   fallback for `equiv_call (H)` only where the old rule fails: `H` is taken to the callees as
   the calls spell them by `ECProcInv.alignProc` (the same bodies), then the call is by that
   judgment (`Logic/ECProcInv.lean`).
4. **First-port modules under the clone's module types.**  `Indiff0.GReal(CSetSize(Sponge), Perm,
   D)` applies `CSetSize(Sponge)` at the clone's `DPRIMITIVE`; `inline` and the call lemmas
   (stated at the sponge's types) do not see through it.  Stated once as equations that hold by
   `rfl` (`CSetSize_Sponge_Perm_init`, `CSetSize_Sponge_Perm_f`, `SimSetSize_init_eq`) and
   rewritten right after `proc` (`erw`, one line; GAP 6 of the file).  The alternative, declaring
   the file's modules over the clone's types throughout, would re-open `equiv_sponge_perm`.
5. **`byequiv`'s inferred precondition** is `={glob}` when both runs start in the same memory; EC's
   also knows the memory (`DPre.h{1} = DPre.h{m} = ha`).  Written
   `byequiv (_ : §allGlobals{1} = §allGlobals{2} ∧ §DPre.h{1} = ha ==> ={res})`; a candidate
   change of the inferred form (always `g₁ = m ∧ g₂ = m`) is not made.
6. **EC's per-procedure `inline` lists** before an adversary's call: paths over the first port's
   views do not elaborate (GAP 3), so the calls before the adversary's are inlined by call site,
   `repeat stmt_inline{i} 0` (it stops at the abstract call).
7. **Cost: the closers' `simp_all` on a declared module's restrictions.**
   `Sponge_preimage_resistant` took 17 minutes to check.  The profiler (`set_option profiler
   true`) on its ideal half: 398 s in `simp` over 83 calls of 4–5 s each.  The cost does not
   depend on the goal: `equiv[ ={Cntr.c} ==> ={Cntr.c} ] { Cntr.c <- §Cntr.c + 1; } ~ { … }` by
   `ec_auto` takes 3.7 s inside the section that declares the adversary and no measurable time
   outside it.  The cause is the closing attempt of `auto` (`simp_all; done`): `simp_all`
   simplifies every hypothesis, and the adversary's restriction (`Module.Declared A S`, `S` a
   join of some sixty footprints; `Footprint.Restricted R S`) is one, which the default simp set
   can do nothing with but tries on every subterm.  Fix: `clear_decl_hyps` (`Logic/ECAuto.lean`)
   clears these hypotheses in front of `simp_all` in the closers of `equiv_auto`, `hoare_auto`,
   `ec_auto`, `auto_close`, `auto_progress` — only where the goal is then closed or the step
   undone, since the footprint tactics need them.  (`sim`'s closer is left alone: one of its
   alternatives discharges by `fp_disjoint`.)  Effect on the full build, seconds per file before
   and after: `SHA3Security.lean` 1026 → 74, `SHA3_OIndiff.lean` 1473 → 147,
   `SHA3Indiff.lean` 171 → 81, `SmartCounter/Gconcl_list.lean` 630 → 502, `SmartCounter/Gconcl.lean` 488 → 398,
   `SmartCounter/Gext.lean` 374 → 269, `SmartCounter/Gcol.lean` 205 → 150.
9. **The Hoare `call` had no frame** (the pHL and pRHL ones do).  EC's
   `rcondt{i} n; first by auto; inline*; auto; conseq (: _ ==> true); auto` asks, after a call
   to a procedure with loops, a condition on a counter the procedure does not write; with
   `hoare_call (: True ==> True)` the condition was asked of every final memory.  Added
   `hoare_call (: P ==> Q) / x₁, …, glob A` (`Logic/ECCallFrame.lean`, rules
   `hoareProc_and_frame`, `hoare_call_wp_frame`; golden test in `Logic/ECProcInvTest.lean`);
   eight uses in sections `SecondPreimage` and `Collision`.
8. **pHL `seq n : P` on a lossless goal** was missing (EC: `seq 1 : true; auto.` in each
   section's losslessness of `DSetSize(D(A))`): `phoare_seq_lossless n : (P)`
   (`Logic/PHoareSeq.lean`, rule `phoareStmt_seq_eq_one`).  A new name: `phoare_seq n : (P)`
   would be read as the start of the five-bound form.

## `SHA3OSecurity.ec`, section `Preimage` up to `rw_ideal_2` (2026-11-14): findings, no tactic change

Nothing was changed in the tactics for this stretch; these are the items for the next batch.

1. **`equiv_call (_ : ={x₁, …})` on a declared adversary puts `={glob A}` into the oracles'
   judgments** (`Logic/ECCallAbstract.lean`: "`glob A` … is always part of the invariant").
   EC's oracle judgments do not have it: the oracles cannot touch `glob A`.  With short oracle
   proofs (`sim`) it does not matter.  In `rw_ideal_2` the oracles' proofs are long: every
   `wp`/`sim n m` then carries `glob A` read over the written memory
   (`(FVP.fvP A).touched_getter.get (Counter.c.set … (Simulator.paths.set … allGlobals))`), the
   read is never simplified, and `stmt_inline` on such a goal ran out of 40M heartbeats (the
   `simp` after the unfolding goes through the postcondition).  Written instead in the general
   form, the same invariant in two parts, `(_ : ={x₁, …} ∧ ={y₁, …})`: EC's oracle judgments,
   and the whole first `have` in five minutes.  To do: either the `={…}` form gives EC's oracle
   judgments too (the abstract rule's invariant without the `glob A` part, which the rule
   already keeps by the adversary's restriction), or `wp` simplifies a `glob A` read over a
   write outside `A` (`touched_set_of_le_compl`, by `fp_disjoint`).
   **Done 2026-11-21** (the first): on a call `A(O₁) ~ A(O₂)` of a declared module, the `={…}`
   form goes to the general form's rule (`Logic/ECCallUpto.lean`, `equivCallInvAndCore`):
   EC's oracle judgments, `glob A` kept by the oracles' writes.  The old region rule stays for
   another declared module's `glob` in the set and as the fallback.  Full build unchanged in
   time; Gconcl's six `equiv_auto; auto_close` became EC's `auto`; `rw_ideal_2`'s invariants
   are EC's single sets again.
2. **Names across the two sides** (`eq_eager_ideal2`): `§x0{2}` is "Unknown identifier" when
   `x0` is also a variable of the other side, or of the precondition, at another type, and
   `splitwhile{1} 1 : i < k` cannot name `k` once no statement mentions it.  Written with the
   lenses.  To do: resolve `§x{i}` among side `i`'s variables first, and let conditions name
   every variable the precondition reads.
3. **Structural module types across clones** (`SH.AdvPreimage` given the sponge's primitive by
   the first port's `ODRestr`): `equiv_proc` does not see through the other module type's
   constructor.  One projection lemma per procedure, stated at the clone's name, and
   `simp only` in front of `proc`.  It goes away with the first port's `ODRestr` (the pilot's
   own would build the primitive at the clone's type), or with reducible module types.
4. **Speed.** `rw_ideal_2` takes about 18 minutes (measured: the first `have` 5, the last
   `byequiv` 3; the `eq_extend` hop is the rest, not measured by itself); in the last part `simp` is 96 s of 150 and instance search
   30 s.  `have h : Pr[…] = Pr[…]; rw [h]` leaves the equation among the hypotheses, where every
   closing `simp_all` goes through its two games: `clear h` after the `rw` (EC's `have ->:`
   consumes it) took 20% off the last part.  To do: profile the `eq_extend` hop; a `have ->`
   form (`ec_have_rw`?) that does not keep the equation.
5. **`rnd f g`** (next lemma, `rw_ideal`): `equiv_rnd f` asks the push-forward equation
   `d₁ >>= pure ∘ f = d₂`, which for `f = oget ∘ of_list` is the first port's `dlist_dout`; EC's
   three bijection conditions are not asked.  If that goes through, `rnd f g` stays
   `equiv_rnd f` with one lemma per pair of distributions.

6. **`rnd f g` did go through `equiv_rnd f`** (`rw_ideal`, three uses): the side goal is the
   push-forward equation, closed by the first port's `dlist_dout`.  No new tactic.
7. **`sim` on loops that call a concrete procedure** (`rw_real`): after `conseq (: _ ==>
   ={z0, n})` it closes two sponge loops with calls of `Poget(PSome(Perm)).f` (3 minutes); after
   `conseq (: _ ==> ={z0, n, glob Perm})`, on the same loops, it runs for minutes and fails
   without a message.  Worked around with the `while` rule and `call (_ : ={glob Perm})`.  To
   do: find what the kept `glob Perm` changes (`debug.sim`).
8. **`inline` and module types across clones, again** (`rw_real`): three `rfl` lemmas put
   `SH.Preimage(A, OSponge, PSome(Perm))` at the sponge's module types (the coercion of the
   primitive, `OSponge` applied, `PSome(Perm).init`).  The GAP 3 and GAP 6 workarounds of this file have
   the same root: module types of two theories that are equal by unfolding but not reducibly,
   and constructors/projections that are different constants.  A `clone` that makes the
   clone's module types reducible aliases of the first port's (or the first port's modules
   re-stated at the pilot's theories) removes all of them.
9. **`rcondt{2} 2` with `sp`'s chain of tuple equations** (`rw_ideal`): the side goal needs
   `x3 = oget (unpad_blocks (parse …).1)` from six equations of `sp`, which the closers do not
   chain (GAP 1 of `Gconcl_list`).  Avoided: `wp` through the right's deterministic
   conditional and the facts settled in the last goal, where the two sides are related.

## `SHA3OSecurity.ec`, section `SecondPreimage` (2026-11-14): one new tactic, findings

**New: `bypr`** (`Logic/ByPr.lean`, golden test `Logic/ByPrTest.lean`).  EC's `bypr` on a pHL
judgment about a procedure: `phoare[ p : P ==> E ] ≤ (ENNReal.ofReal x)` (`=`, `≥`) becomes
`∀ a σ, P → Pr[ p (a) @ &σ : E ] ≤ x` — the converse of `byphoare`, three rules
(`Procedure.phoareProc_le_of_toReal_Pr_le`, `…_ge_of_le_toReal_Pr`, `…_eq_of_toReal_Pr_eq`).
The event is rebuilt from the postcondition in the shape `Pr[ … ]` elaborates to, so the new
goal prints as a probability.  The precondition stays as the judgment has it (a `let` chain
over the arguments); `intro a m ⟨h₁, h₂⟩` destructs it.  Used once
(`Sponge_second_preimage_resistant`).  The pRHL form `bypr e₁ e₂` is still E12.

Items for the next batch (nothing else was changed):

1. **Parameter names of a procedure are not known through a clone's alias or a Lean
   parameter** (`paramNamesOf`, `Syntax/HoareSyntax.lean`): `SH.SecondPreimage(A, F, P).main`
   and `TOTO(A).main` give "no parameter names are known", so `byequiv (_ : P ==> Q)`,
   `byphoare (: P ==> _)`, `phoare_call (: P ==> Q)` cannot be used with `§m1` in `P`; the
   judgments are written out as terms, with their bound.  To do: `appliedModuleParamNames?`
   through `unfoldCloneAliases` and through an application to Lean arguments.
2. **`byphoare`'s judgment has its relation as a lambda** (`fun x1 x2 ↦ x1 ≤ x2`, from the
   rule's `(· ≤ ·)`), on which `phoareCallStep` fails ("the goal's relation is not …").  It
   went unnoticed because `phoare_seq` came between the two everywhere else.  To do: state the
   `byphoare` rules with `@LE.le ENNReal _` (as `phoare[ … ] ≤ r` elaborates), or eta-reduce
   in `phoareParts`.
3. **`sim / x` leaves the final implication** where the calls' results are discarded
   (`Setter.throwaway`) and the globals are read through `ProgramState.globalL.set`:
   `closeImp`'s `equal_outside` branch lacks `Setter.throwaway` and `globals_globalL_set`.
   One line by hand in the proof.  To do: add the two to that branch (golden test on a wrapper
   procedure that sets a variable and calls a game).
4. **`sp` over `X <- e` for a global `X` states `§X.intoGlobal = e`**; a later condition
   reading `§X` is generalized to a second value (`Dist_of_P2Adv_m`, `Dist_of_P2Adv_m1`), and
   the goal `auto` leaves is then false.  Avoided by leaving the assignment to `auto` (`wp`).
   To do: `sp`'s fact in the read normal form (`Lens.intoGlobal_get_eq`).
5. **`module … using (A : SH.AdvSecondPreimage)` calling the clone's game on `A`** fails in
   the `module` command's `apply_simp` proof (unsolved goal about
   `(SH.SecondPreimage.expression.app (A.expression.pair …)).reduce`); with `A` a Lean
   parameter it goes through.  To do: reproduce on a small clone.
6. **Speed**: `rw_ideal_2` 24 min, `rw_ideal` 12, `rw_real` 10, the final lemma 4 (its `sim /`
   2.5); the module takes about 55 minutes.

## `SHA3OSecurity.ec`, section `Collision` (2026-11-15): no tactic change

The section is `SecondPreimage`'s with the fixed message removed; its Lean text was generated
from that section's proofs.  One finding for the batch:

1. **Inlining renames a callee's locals against the *other* side's variables** (`m1` → `m10`
   on the left because the right game has an `m1`).  EC keeps the names (its memories are
   separate), so EC's `={m1, m2}` cannot be written as is, and `§m1{1}` for a variable the
   left side does not have is accepted silently (it reads an unrelated local).  To do: fresh
   names per side only; and an error (or a warning) when a relational condition reads a
   local that the side's statement does not declare.

## Aligning the first port's remainder (2026-11-15): what the declarations could not fix

After the promotion (`Refactor.md`, last sections) the first port's remaining declarations were
brought to the port's form where that is a matter of how they are written: games in EC's paths
with `module_subtype` in place of hand-built records, `global_var`s in place of lens parameters,
aliases in place of `def`s, duplicates of what the port has removed.  No shared tactic was
changed.  What is left of the misalignment comes from four limits of the infrastructure, each
with the glue it costs today:

1. **A procedure of a module of one clone's module type, read at another clone's** (EC: one
   module type).  `LowerDist(D, F, P)` hands `BlockSponge`'s primitive to the bit sponge's `D`;
   `Indifferentiability`'s `GReal` reads a `PRP` as a `PRIMITIVE` and that as a `DPRIMITIVE`.
   `*_proc` and `inline` do not open such a procedure (`Flatten.moduleStep?` switches the
   accessor only for `Module.app` arguments, or with `views := true`, which `module_norm` and
   `accessorNorm` use).  Glue: `module_norm` before `equiv_proc` at six goals (`Sponge`,
   `SHA3Indiff`); the `simp only [PRIMITIVE.view, Perm, PRP.RP.RP, …]` lists of GAP 1 in
   `SHA3Security`, `SHA3_OIndiff` and GAP 3 in `SHA3OSecurity`; `P_view` (GAP 11 of
   `Gconcl_list`).  It is also why the module types cannot yet become clones of the port's
   `Indifferentiability`: an accessor and a `mk` of two clones do not reduce
   (`T.f.mk_simp` is stated per instance).  To do: `*_proc` (and `inline`'s head step) retry
   after `ECProc.accessorNorm` when the head has no body; `views` was off by default because
   it changed goals of the first port's proofs, which are gone.  Golden test: an adversary of
   one clone given a module of another's type, `proc` on its oracle.
2. **EC's procedure aliases used as a module (exception E5)**: `call (RO_LRO_D (D2(D)) _)` on a
   goal whose call is the alias's target.  Our `D2 D` is a module with one procedure that calls
   the target, so the judgment is about another procedure than the goal's call.  Glue: the
   first port's `D2o`/`D2`/`D2o_D2`/`D2_D2o`/`L2_RO_LRO` and the three like it in
   `Gconcl_list` (about 400 lines, used once each in `equiv_ideal`, a declared deviation), and
   the port's own bridging equations `b1`, `b2` in `Simplify_simulator`.  To do: `equiv_call H`
   (and `byequiv H`) accept an `H` about a one-call wrapper of the goal's callee.
3. **`clone`**: two clones of one theory at the same types share its module variables, and
   with different operators they are not supported.  `IRO` is cloned as `BIRO` (`valid_block`)
   and `BIRO2` (`predT`) at the same types, so both still apply the first port's `IRO`, a module
   with a lens parameter, and the port's own `IRO` (with `module_var`s) has no user.  Same for
   `F`, `F2` (clones of `PROM.FullRO`, a library theory in the old style).  To do: per-clone
   module variables (the slot named after the clone), and the clone's operators selected by the
   clone, not by the types.
4. **`fp_le` has no bound for a `module`-declared procedure it is not told about**
   (`fp_le: no bound for FVP.fvP { expression := (ModuleExpression.proc X.f.procedure).reduce … }`).
   The frame rules of `call` on a concrete callee ask for one.  Glue: about 45 `@[fp_bound]`
   lemmas, each `by fp_module L` (tried without: `SLCommon`'s four were not needed; `Handle`'s
   and `Sponge`'s are).  To do: `fp_le` reads the procedure's code, as `fp_disjoint` does for a
   module (`Logic/ModuleFootprint.lean`).

Items 1 and 2 remove the most text; 1 also unblocks the clone-style module types.

### To do (saved 2026-11-15, not started): the plan for the four, in this order

Every change to a shared tactic invalidates the whole pilot check (about an hour): develop each
against its golden test and the fast files (`Sponge.lean` builds in a minute, `SHA3Indiff.lean`
in one and a half), then one full rebuild per item.

1. **Procedures across clones' module types** (item 1 above; the code is read, the fix small).
   `equiv_proc`, `hoare_proc`, `phoare_proc` are `ECProc.procStep` followed by
   `ECProc.accessorNorm`; `accessorNorm` (which `module_norm` is) already reads a procedure off
   a module of another module type (`Flatten.moduleStep?` with `views := true`).  Change: when
   `procStep` finds no body at the head, `accessorNorm` first and retry; the same retry in
   `inline`'s head step (`Flatten.unfoldProcedure`, as `GlobWrites` and `SyntacticFrame`
   already do with `catch _ => … (views := true)`).  Nothing that passes today changes: it acts
   only where `proc` fails.  Golden test: an adversary of one clone given a module of another
   clone's module type, `proc` on its oracle.  Then remove: the six `module_norm`s (`Sponge`,
   `SHA3Indiff`), the `simp only [PRIMITIVE.view, Perm, PRP.RP.RP, …]` lists (`SHA3Security`,
   `SHA3_OIndiff`, `SHA3OSecurity`), `P_view` (`Gconcl_list`).  Then the module types: the
   abbreviation blocks of `SLCommon`, `BlockSponge`, `Sponge`, `SHA3Security`, `SHA3_OIndiff`,
   `SHA3OSecurity` become `clone … Indifferentiability as … with type p <- …` (the alias
   modules written with `T.mk` take the clone's `mk`), and the first port's
   `Indifferentiability`/`OptionIndifferentiability` (`view`, `GReal`, `GIdeal`) go.
2. **`fp_le` on procedures** (item 4 above; mechanical).  `fp_disjoint` reads a concrete
   module's globals off its code (`ModuleFootprint.concreteBound`, cached); `fp_le`
   (`Logic/FootprintUpper.lean`) never asks it, and `concreteBound` knows whole modules only
   (`isModule`), not a procedure module such as `HybridIROEager.fill_in`.  Change:
   `concreteBound` for a `module`'s procedure (`X.f` with `X.f.procedure`), and `fp_le` falls
   back to the hook after the `@[fp_bound]` lemmas.  Then delete the stated footprint lemmas
   group by group, the build as judge; watch the timings (`concreteBound` runs `fp_module`).
3. **EC's aliases used as modules** (item 2 above; one probe, then a choice).
   Option A, the real fix: `module` accepts `proc f = M(args).g` with no body, the procedure
   being the target by definition (`apply_simp` gives it); exception E5 goes everywhere, not
   only in `Gconcl_list`.  Option B, the fallback: `equiv_call H` and `byequiv H` accept an `H`
   about a one-call wrapper of the goal's callee.  Probe first: whether a procedure taking `()`
   and one taking a `unit` argument have the same signature here (EC identifies them;
   `RO_Distinguisher`'s `distinguish` takes `d_in_t = unit`, and our wrappers are called with
   `(())`).  Then: `D2`, `D3`, `D5`, `D6` in `Gconcl_list` as EC's aliases, `equiv_ideal`'s
   four steps by `call (F.FullEager.RO_LRO_D (D2 D))` (the clone-level lemma stated once, as
   `SecureORO`'s), and the first port's `D2o`…`L4_F2_RO_LRO` deleted.
   *Status 2026-11-19:* option A done (`proc f = c;`, `notes/ModuleProcAlias.md`); the probe
   answered no (`procmod ()` ≠ `procmod (Unit)`), so PROM's `RO_LRO_D` takes any procedure
   signature; `equiv_call H` rewrites the aliases in `H`; `ec_auto` derives the memories'
   equality after the same initializations (`subst_states`).  `D2`, `D3` done (steps e3, e8 of
   `equiv_ideal` are EC's script; the first port's `D2o`…`L_RO_LRO`, `IF'`, `Valid2`, `L`, `L2`
   deleted).  `D5`, `D6` done the same day (with `S2(…)` for EC's `S(Last(…))`; the first port's
   `L4`, `L4F`, `L4G` and their bridges deleted): `equiv_ideal`'s four steps are EC's.  Cost:
   `Gconcl_list` 314 s → 406 s (the four `RO_LRO_D` side conditions, `ec_module`/`fp_disjoint`
   over `D2(D)` … `D6(D)`, run inside `equiv_ideal`, where the bridges' footprint lemmas ran in
   parallel).  `S2`, `DValid`, `SimLast` as aliases the next day (`cfe2989`;
   `equiv_L3_L4`, `equiv_L4_ideal` lost their extra inline after the simulator's call), with every
   other procedure alias of the port (SecureORO, SHA3_OIndiff, IndifRO_is_secure, SHA3Security,
   SHA3OSecurity): E5 is down to the whole-module aliases.
4. **`clone`'s module variables** (item 3 above; a design decision, the least certain).
   First a test (`Syntax/CloneTest.lean`): two clones of one theory at the same types with
   different operators, to see what breaks in fact (used through their namespaces they may
   mostly work).  Per-clone variables need the slot to depend on the clone; candidate: a tag
   carried by the theory's instance, which `module_var` puts in the slot's name.  It touches how
   variables are declared, next to `Language/`: to be agreed with Dominique before building.
   Then: `BIRO`, `BIRO2` (and `Sponge`'s `BIRO`) as clones of the port's `IRO`, and the first
   port's `IRO` (a lens parameter) goes.

### Status 2026-11-17

* **Item 1 (procedures across clones' module types): done.**  `Flatten.unfoldProcedure` retries
  through the views (`views := true`) where the plain pass finds no body, so `*_proc` and
  `inline` (and every other user of `unfoldProcedure`) open them.  Removed: the six
  `module_norm`s (`Sponge`, `SHA3Indiff`), the `simp only [PRIMITIVE.view, Perm, …]` lines
  (`SHA3Security`, `SHA3_OIndiff`), `P_view` (`Gconcl_list`).  Side effects, fixed: `inline*` now
  also inlines `Perm` behind the view (EC's `inline*` does too): `Real_lossless` keeps its
  deviation by `phoare_inline 0`; one inlined variable renamed in `Gconcl_list`.  Not yet done:
  the module types as clones (the first port's `Indifferentiability`/`OptionIndifferentiability`).
* **Item 4 (`fp_le` on procedures): done.**  `concreteBound` bounds a `module`'s procedure too, and
  `fp_le` asks `ModuleFootprint.cachedBound` (if the rest then goes through) before unfolding.
  Two `call H` side goals in `Sponge` changed shape (a frame where there was none): EC's
  `skip; progress; smt()` as `ec_progress` and one line.  Stated `@[fp_bound]` lemmas deleted
  (2026-11-18), the build as judge: 19 of the 45 that nothing names (Handle 5, Gext 5, Sponge 6,
  SHA3Indiff 2, SecureORO 1).  Still needed: those `stmt_swap` asks for (it reads footprints by
  `fp_disjoint` on the callee's procedure module, `Module.proc p`, not a named module: Gcol's
  `fvP_sample_c`, BR93's `fvP_Log`, Gext's procedure-module group and simulator accessors), and
  frames that are lost without them (Gconcl_list 3, SHA3Indiff `fvP_RaiseSim`, SHA3OSecurity 8).
  The rest (38) are named by `GlobBound` instances (restriction checks by instance search).
* **Item 3 (EC's aliases): parked** (Denis, 2026-11-17).  `proc f = M(O).g` is not accepted by
  `module`; for `RO_LRO_D`'s distinguisher also `procmod () → _` and `procmod (Unit) → _` are
  different signatures (EC identifies them), and a generic wrapper over a Lean function `X F` is
  refused by `module` (a call target must be a module expression).  The bridges stay; they can be
  shortened (path form, one shared bridge script, restriction proofs by the solvers).
* **Item 4 of the plan (per-clone variables): parked**, to agree with Dominique.


### Status 2026-11-18

* **`stmt_swap` reads footprints off the code** (`27e4ba6`): the solver's default bound hook
  (`FootprintSolver.defaultBoundHook`, set by `ModuleFootprint` to `cachedBound`) is passed by
  `stmt_swap` only (for every caller, Gext timed out).  Gcol's `fvP_sample_c` went; the other
  stated footprints stay (frames, speed).  76 stated before 2026-11-17, 56 now.
* **The first port's module types as clones (item 2 of the "what is left" plan): blocked by the
  clone design.**  Branch `wip/module-types-as-clones` (`cb41dd7`) switches `SLCommon`,
  `BlockSponge`, `Sponge`, the `Option` files to clones of the port's theories, deletes the first
  port's module types and views, and moves `SIMULATOR.call_*`, `representable_of_init` into the
  theory (so that clones alias them).  `SLCommon` … `Gconcl` and `BlockSponge` build; `Gconcl_list`
  and `Sponge` do not.  Cause: a theory's `Params` has its types as `outParam`s, which Lean erases
  before instance search, so the search answers with the latest clone's instance whatever the
  types; where two clones of one theory at different types meet (`SLCommon`'s and
  `BlockSponge`'s `Indifferentiability` in `Gconcl_list`, as in EC), record notation for `mk`, the
  subtyping coercions and unaliased theory lemmas fail at the other clone's types.  Tried:
  `semiOutParam` (the theory's own definitions get stuck), a universal instance for a field-less
  `Params` (Lean refuses instances with open out-params).  A fix changes how a theory receives
  its types (`Syntax/Clone.lean`): e.g. the types as ordinary parameters with the theory's
  declarations elaborated against its section variables, or the clone generating per-clone
  structures/coercions so that nothing at a use site searches for `Params`.  To agree with
  Dominique, like per-clone variables.
* **`BlockGen_loop_direct` in EC's script** (item 4 of the "what is left" plan): `bypr (res{1})
  (res{2})`, `byphoare`, `byequiv` with EC's `seq`/`while`, `PrLoopSnoc_sample`, `dlist1E`.  The
  first port's proof (`bdistr_dlist`, `BlockGenCall` and its two equivalences) and the GAP 9
  restatement go; EC's `DWord.dunifin1E` is `BitWord.dunifin1E` (`Lib/EC/BitWord.lean`, also
  used by `Gconcl_list`); exception E12 keeps only the `Sample`/`LoopSnoc` step.

### Build time (2026-11-19)

The full build took 95 min (4 threads), almost all of it the serial SHA-3 chain `ConcreteF` →
`Handle` → `Gcol` → `Gext` → `Gconcl` → `Gconcl_list` → `SHA3Indiff` → `SHA3_OIndiff` →
`SHA3OSecurity`.  Profiled (`-Dprofiler`, `trace.profiler`); kernel checking is about 1 min in
all.  The time is our tactics' failure paths:

* **`sim`'s closer** (`ECSim.closeImp`) tried up to eight `simp_all`s with the declared module's
  restrictions in context; under `SHA3OSecurity.ec`'s adversary (a restriction of ~40 modules) a
  `simp_all` on a trivial goal costs 7 s.  43 runs that closed nothing took ~170 CPU-min, the
  successful ones ~46.  Fixed: its `simp_all` attempts (and `ECProcInv`'s closer) go after
  `clear_decl_hyps`, as `auto`/`ec_close` already did (`clear_decl_hyps` moved to
  `DeclareModule.lean` so that `ECSim` can use it).  `SHA3OSecurity` 33.6 → 12.2 min, full build
  95 → 72 min.
* **`call`'s frame search** (`ECCallFrameRel.frameFor`) tries `fp_disjoint` for each global the
  condition reads; when the callee writes it, the solver fails after ~20 s.  `Gext` (21 min, one
  proof, `EG2_Gext`): 39 such failures, 12.7 min; `Handle`: ~17 CPU-min.  Cause, found by timing
  the solver's pieces: each lookup in the cache of bounds read off the code
  (`ModuleFootprint.cachedBound`) checked that the cached proof's free variables are in scope with
  `Expr.hasAnyFVar`, which walks the (large, shared) proof as a tree: 0.7 s per lookup under
  `Gext.M.f`, many lookups per `fp_disjoint`, failing or not.  Fixed: the free variables and
  constants are collected once, when the bound is cached.  `Gext` 1261 → 196 s, `Handle` 771 →
  271 s, `Gconcl` 401 → 215 s; full build 72 → 43 min.
* **`call`'s same-callee rule** (`PRHLWp.equivCallFrameless`, also inside `sim`) unified the two
  callees at default transparency with no limit: 185 s to find `OSimulator(…(RFList)).fi` and
  `OSimulator(…(RFWhile)).fi` different, in each section's `rw_ideal_2`.  Fixed: tried within
  `sim`'s callee budget (50M heartbeats); past it the callees' equality is the `callee` goal, as
  for callees that differ.  `SHA3OSecurity` 720 → 579 s; full build 43 → 40 min.
* **Syntax declarations mid-file are barriers**: a `macro`/`syntax`/`notation` (also `moduletype`,
  `clone`) waits for every proof before it (its parser is run at once); `module`, `def`,
  `instance`, `global_var`, `declare module` do not (measured with sleeping theorems).
  `Gconcl_list`'s six local tactic macros, declared at their first use, made it elaborate in
  stretches (181% CPU): declared after the namespace's header now, `Gconcl_list` 578 → 340 s;
  `Handle`'s `pf_bad_leaf` likewise, 268 → 179 s.  The proofs are unchanged (TRANSFER_SKILL §6).
* Parallelism: `SHA3OSecurity` is 2389 s of work on one thread (`lean -j1`), 570 s by default
  (~590% CPU: 4.2× faster, ~40% overhead).  `LEAN_NUM_THREADS` does not limit the elaboration
  inside a file (588% CPU with it set to 1); `lean -j N` does.  The file's time is now its longest
  proofs (`rw_ideal_2`, `eager_ideal` of the three sections).
* Not ours: in `SHA3OSecurity` the same work (heartbeats) of a step took 16 s alone and up to
  22 min of wall time inside the file (`call (Eager.RO_LRO_D (Dist A))` in sections
  `SecondPreimage` and `Collision`, not in `Preimage`): a stall of Lean's parallel elaboration.
  Not reproduced with a sleeping or one heavy concurrent proof, nor with sleeping theorems
  around it; still 420 s of `Collision.eager_ideal`'s 774 s after the fixes, so it now sets the
  file's time.  Hypothesis (unchecked): the step waits for a small task (a lemma the `module Dist`
  command generates?) queued behind the heavy proofs.  Parked.
* Second round (work counted in heartbeats, `trace.profiler.useHeartbeats`, so contention does
  not distort it; Gconcl_list, Gconcl, Gext, Handle: 66G heartbeats).  Failing attempts were
  ~21% of it: two `rw`s 9.8% (fixed below), closers' `simp_all` 6.4%, `equiv_call`'s frame
  search (`fp_disjoint` per variable) 4.6%.  The footprint solver (`fp_module`) is 11–14%,
  nearly all successful.
  * The `module` command's procedure lemma (`procApply`) retried `rw [← procedure_spec]` twice
    on the goal it had just rewritten, failing after searching the whole callee: ~1G heartbeats
    per generated lemma with a large callee (`Gconcl_list.D2`, `D3`).  Fixed (`f3e7055`).
  * `glob_simp`'s `repeat (rw [touched_set_of_le_compl ?_]; …)` ended in a `rw` whose open
    pattern was unified with every `get` of the goal: 1.3G heartbeats a call in
    `Handle.CF_G1`.  Fixed by a syntactic guard, `glob_set_present` (`c17eace`).
  * `concreteBound` cached a `sorry`'d bound when `fp_module` failed under error recovery
    (`SimLast(S)`: a functor applied to a concrete module).  Fixed (`fa57869`, a correctness
    fix of the tactic, time neutral).  Open: `fp_module` could bound such a module by its
    argument's footprint.
  * Closers' failing `simp_all`s cost 270–570M heartbeats, successful ones up to 380M: no budget
    separates them.  Left as is.
  * The SHA-3 imports are a single chain (each file uses the previous one), so the build time is
    the sum along it; no import to trim.
  Full build 40.4 → 33.2 min.
* Third round (2026-11-19, after `equiv_ideal`'s lazy/eager steps moved to EC's form): the four
  `RO_LRO_D` side conditions (`ec_module`/`fp_disjoint` over `D2(D)` … `D6(D)`) ran inside
  `equiv_ideal`, 5.5G heartbeats, `D5`/`D6` 2.2G each, spread over `fp_module` reading the same
  sub-modules' code (`DSqueeze2` twice in each, `FC`, `PC`, `S2`) again and again; Gconcl_list
  320 → 406 s.  `fp_module` now bounds a closed sub-module below the root by its own bound (the
  bound hook, cached per file: `FpModule.subBound`), unfolding only where that bound does not
  fit.  Gconcl_list 304 s; full build 33.2 min, as before the change.
