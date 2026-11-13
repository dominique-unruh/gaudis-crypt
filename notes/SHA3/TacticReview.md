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
`A_lossless` and `Neg_D_lossless` are done (EC's scripts, `phoare` tactics).  The rest waits for
three things, none of them a proof step:

* `concl` applies `Gconcl.Real_Ideal` to `A(D)`.  The pilots state `Real_Ideal` (and all it rests
  on, down to `ConcreteF`) for `declare module D`, with `D_ll` over oracles `{-D}`.  For the
  composed `A(D)`, EC's `{-A(D)}` is `glob D ∪ {C.c}`, read off the code; here `fvP (A D)` is
  only bounded above by that, so an oracle outside `glob (A D)` is not known to be outside
  `glob D`, and `A_lossless` cannot be given as the `D_ll` of `A(D)`.  The `ConcreteF` pilot met
  the same thing once (`Switching.Conclusion` over `Module.ECGlob`).  Doing it here means stating
  the chain `Real_Concrete` … `Real_Ideal` over `Module.ECGlob` instead of `declare module`, in
  five pilot files: this *is* step 4 (EC's syntactic `glob`), and is not started without a
  decision.  `neg_D_concl`, `Inefficient_Real_Ideal` and the final `Real_Ideal` follow `concl`
  (`concl (Neg_D(D))` is the same situation).
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
`sim` over differently named locals).  `equal1` (75 lines) is started: opening, the call and
its three easy goals, the simulator's `f` up to the split on `valid q`; its two branches (the
loop of `BIRO.IRO.f` and the eager oracle's loop against `BIRO2.IRO.f`) are left, with
`Simplify_simulator` (one `RO_LRO_D`).

**The batch of rule fixes this port has collected** (each small, each with a golden test; the
first needs a full rebuild, so they go together):
1. `inline`: an option to open a record of another module type (GAP 11).
2. `ec_prep`: the guards of split loops, `(a && b) = true/false`, and `decide p = !false`
   (GAP 9; met in three lemmas).
3. `equiv_conseq` without a specification, EC's `conseq=> />` (GAP 15).
4. `skip`: `glob D` past writes outside `D`, as `sp` does (GAP 14).
5. `seq` on a Hoare triple (GAP 9); `splitwhile` reading the conditions' variables (GAP 10).
6. `phoare_call` with an invariant on an abstract module (GAP 12); a `phoare` step for code
   after a loop (GAP 13).
7. `smt_close`'s unknown free variable in `ec_instances` (GAP 2).
8. `sim` over differently named locals (GAP 16); pair states equal by components (GAP 8).

