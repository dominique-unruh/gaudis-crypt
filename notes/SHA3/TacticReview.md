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
  (2026-11-13: Dominique prefers not to take over EC's `glob`; a smaller form is on trial, see
  "Step 4, tried another way" in §6.)
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

Second file, `Pilot/SecureORO.lean` (19 sites): 18 generalize as they are.  The 19th, the
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
  touched (normalizing at every exit timed out in `Pilot/Gconcl`).

Files without the option behave as before.  The option is switched off, in the source, at the
six places where a rule falls back today (`set_option ec.strict false in …`):

| Where | Fallback |
|---|---|
| `Pilot/IndifRO_is_secure` (3 `sim`s, 11 calls) | no equality set for a call, all globals asked equal |
| `Pilot/Sponge` (2), `Pilot/ConcreteF` (1) | `equiv_call (_ : ={x})` on a concrete callee: frameless rule |

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
  `Logic/ReadNormTest.lean` ("The names of the values").  `Pilot/SecureRO` and `Pilot/SecureORO`
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

### The port on the strict tactics (2026-11-14): `Pilot/Gconcl_list`, section `Ideal`

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
  region form).  EC's theory `AdvAbsVal` is not ported (GAP 17): its two steps are one equation
  here, from two lemmas of the first port.
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
9. EC's theory `AdvAbsVal` (`Neg_main`, `Neg_A`, `Neg_A_Pr`, `Neg_A_Pr_minus`): a small library
   file; needs `proc *` and `Pr[mu_not]` (GAP 17).
10. From `Pilot/Sponge` (its GAP 2–5): EC's path for a callee inside a library procedure;
   reads through a discarded call result in the strict `auto`; the oracle goals of an abstract
   call in the module's own procedure names, and only for the procedures the module type's
   `{…}` allows; `equiv_conseq H` closing its implications.

11. From `Pilot/Sponge`, the second half of `HybridIRO` (its GAP 6–13): the strict `auto` on a
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
made of a `glob` region and variables (GAP 15 of `Pilot/Sponge.lean`; it needs "equal on a
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

Done in `Pilot/Sponge.lean`: the section's two declarations (`BlockSim … with glob R`, `Dist`
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
   and after: `Pilot/SHA3Security` 1026 → 74, `Pilot/SHA3_OIndiff` 1473 → 147,
   `Pilot/SHA3Indiff` 171 → 81, `Pilot/Gconcl_list` 630 → 502, `Pilot/Gconcl` 488 → 398,
   `Pilot/Gext` 374 → 269, `Pilot/Gcol` 205 → 150.
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
