# Probabilistic Hoare logic (`phoare`): plan

Branch `phoare` (on top of `hoare-call-rule`).  Goal: EasyCrypt-style
`phoare[ M : P ==> Q ] = r` / `<= r` / `>= r` with tactics analogous to the `hoare` ones.

## Design: expectations underneath, EC's event syntax on top

```lean
/-- expected value of `g` after running `c` from `σ` -/
def Stmt.ewp (c : Stmt) (g : ProgramState → ENNReal) : ProgramState → ENNReal :=
  (programDenotation c).wp (fun r => g r.2)

/-- `ρ` is `(· ≤ ·)`, `(· ≥ ·)` or `(· = ·)` -/
def phoareStmt (A : ProgramState → Prop) (c : Stmt) (g : ProgramState → ENNReal)
    (ρ : ENNReal → ENNReal → Prop) (r : ProgramState → ENNReal) : Prop :=
  ∀ σ, A σ → ρ (c.ewp g σ) (r σ)
```

and `phoareProc` at procedure level.  EC's event `Q` is the indicator `if Q then 1 else 0`.

Why expectations: the sequencing law is exact, for all three relations,

    phoareStmt A (p; q) g ρ r ↔ phoareStmt A p (q.ewp g) ρ r

so `phoare_wp k` only *rewrites the postcondition* with the exact wp of the last `k`
statements — including through abstract calls, left symbolic as
`(procedureDenotation U.f a).wp (fun (v, g) => …) σ.globals`.  Facts about the adversary
(losslessness, its own specs) are used at the end, by linearity/monotonicity.  EC's
`seq n : R r1 … r5` and `swap`/`rnd (pred1 b')` become unnecessary in the common cases.

## Phases

0. **Judgment, syntax, bridges** (`Logic/PHoare.lean`): definitions; `phoare[ … ]` syntax and
   printing (after `hoare[ … ]`); move `Pr`, `IsLossless` from `Examples/Pedersen/Hiding.lean`;
   `byphoare` (`Pr M σ ⋈ r` from a `phoareProc`), `hoare ↔ phoare[¬Q] = 0`,
   `islossless ↔ phoare[True] = 1`; consequence rules.
1. **`phoare_wp k`, `phoare_skip`**: exact `ewp` lemmas (assign, sample, reset, `if`, symbolic
   call); reuse `hoareSplit`, the inliner, `generalizeReads`; generalize `simpReads` to any
   condition type/judgment head; an `ENNReal` arithmetic simp set (`∑ x, … / card`, Bool sums,
   `card ≠ 0`, `≠ ⊤`).
2. **Calls with specs**: `phoare_call h`, `h` a procedure judgment about the callee, for a
   trailing call.  The call's expectation is replaced by the spec's bound under the side
   condition `C σ` (the spec's precondition at the arguments, and the continuation related to the
   spec's postcondition): `if C σ then R else ⊤` for `≤`, `… else 0` for `≥`, `… else ‹the
   symbolic expectation›` for `=` (exact).  Losslessness is used through the expectation algebra
   (`IsLossless.ewp_const`).
3. **Loops**: `phoare_while_le I` with an expectation invariant (`wp_while_invariant`).  A
   potential such as `indicatorE bad + (q − i) · δ` gives the union bound over a `q`-round loop,
   which is EC's `fel` in the loop form our games use (`oracle_loop_n`); `loop_n_wp_linear_bound`
   and the Birthday lemmas are hand-proved instances.  Lower bounds for loops (termination, from
   `expected_while_lfp_iSup` in `Logic/PRHL2.lean`) wait until something needs them.
4. **`islossless` tactic.**

*Not planned for now*: EC's `fel` proper.  Its point is an abstract adversary `A^O` calling its
oracles itself, an unknown number of times — an induction over the oracle calls.  That needs a
call rule for abstract procedures with oracle holes, preserving an invariant/potential on the
oracle state (EC's `call (_ : inv)`, of which `fel` is the probabilistic version): a project of
its own, once adversaries calling oracle holes are in use.

## Milestones

1. Re-prove `hi_ll` and `fakecommit_half` (`Examples/Pedersen/Hiding.lean`) with the tactics
   (phases 0–2).
2. Abstract adversary hitting a fresh uniform secret within `q` rounds of an explicit loop:
   `phoare[ … : True ==> hit ] <= q / |X|` (phase 3, potential invariant).
3. Optionally, port one RO bound (QueryHit / CollisionResistance / Switching).

## Log

* 2026-10-22 — **Phase 0 done, phase 1 core done.**
  * `Logic/PHoare.lean`: `Stmt.ewp`, `Procedure.ewp`, `phoareStmt`, `phoareProc`; `indicatorE`
    (EC's `b2r`); `Procedure.Pr`, `Procedure.Pr_eq_ewp`, `Procedure.Pr_of_phoareProc` (`byphoare`);
    `Procedure.IsLossless`; `hoareStmt_iff_phoareStmt`, `hoareProc_iff_phoareProc`;
    `phoareStmt_seq_iff` (exact sequencing), consequence rules, `ewp` of every statement but
    `while`; `phoareProc_as_phoareStmt`.
  * `Syntax/PHoareSyntax.lean`: `phoare[ P ==> Q ] ⋈ r { … }` and `phoare[ M (x) : P ==> Q ] ⋈ r`,
    `⋈ ∈ {=, <=, >=, ≤, ≥}`, bound at `term:max`; a `Prop` postcondition is an event (tried
    first), an `ENNReal` one an expectation; printing round-trips (`PHoareSyntaxTest.lean`);
    `phoare_proc_to_stmt`.  The `HoareSyntax` helpers it reuses are no longer `private`.
  * `Logic/PHoareWp.lean`: `phoare_inline n`, `phoare_split k`, `phoare_wp k`, `phoare_skip`;
    `HoareWp.simpGoalArg` (generalized `simpReads`).
  * First proof: `phoare[ FairCoin.flip : True ==> §res = true ] = (1 / 2)` in 5 tactic lines
    (`Logic/PHoareWpTest.lean`).

* 2026-10-22 — **Milestone 1 done** (`Examples/Pedersen/HidingPHoare.lean`).
  * Expectation algebra in `Logic/PHoare.lean`: `Procedure.ewp_add`/`_const_mul`/`_finset_sum`/
    `_mono`, `Procedure.IsLossless.ewp_const`, `Procedure.ewp_const_le`, `indicatorE_add_not`,
    `ENNReal.sum_div_card`.
  * `fakecommit_half_phoare` (judgment) + `fakecommit_half'` (EC's statement, via `byphoare`):
    9 + 5 tactic lines, against ~70 in `Hiding.lean`.  No `swap`/`rnd (pred1 b')`: the exact
    expectation keeps both adversary calls symbolic, and one `simp only` (linearity, the
    partition of the coin, losslessness, averages) closes it.
  * `hi_ll_phoare`: 6 tactic lines, against ~45.

* 2026-10-22 — **Phase 2 (calls with specs) done.**  `fel` dropped from the plan (see above).
  * Rules `phoareStmt_call_le`/`_ge`/`_eq` (`Logic/PHoare.lean`): a trailing call closed by a
    judgment about the callee, under the side condition "precondition at the arguments, and the
    continuation related to the postcondition"; trivial bound (or, for `=`, the symbolic
    expectation) where it fails.  `phoareProc_le_of_eq`/`_ge_of_eq`; `phoareProc.ewp_eq`/
    `_le`/`_ge` (a judgment as a fact about the callee's expectation).
  * `phoare_call h` (`Logic/PHoareWp.lean`): picks the rule by the goal's relation (an exact `h`
    serves for all three), after normalizing `h`'s conditions with the goal's simp set — the side
    condition then usually simplifies away.
  * `phoare_simp [h₁, …]`: the simp set of `phoare_wp`, plus exact judgments as rewrite rules for
    their callees' expectations — for continuations that are not literally the spec's
    postcondition (`indicatorE a * indicatorE v` after two coin flips): linearity
    (`Procedure.ewp_const_mul`, `indicatorE_and`) exposes the spec's expectation.
  * Pitfall found: after inlining a functor, a callee is a `moduletype` accessor on a record,
    `(Coin.flip FairCoin).procedure`, which is *not* definitionally the constant
    `FairCoin.flip.procedure` (`Module.procedure_proc'` is propositional).  The simproc
    `reduceProcedureConst` (the inliner's module evaluation, run at default transparency) puts
    both the goal's and the spec's expectations in the constant form; `phoare_call` leaves the
    spec's procedure alone, so it still unifies with the call statement.
  * Tests (`Logic/PHoareWpTest.lean`): a relay game proved from `flip_half` without inlining the
    coin (`=`), the same with an abstract coin known by an upper bound (`≤`), and two flips
    `= 1/4` via `phoare_simp [flip_half]`.

* 2026-10-22 — **Phase 3 (loop upper bounds) done; milestone 2 done.**
  * `Stmt.ewp_while_le`, `phoareStmt_while_le` (`Logic/PHoare.lean`): an expectation invariant
    `I` that one iteration does not increase (where the test passes), above `g` where it fails.
    Qualitative invariants fold in as `if inv then … else ⊤`.
  * `phoare_while_le I` (`Logic/PHoareWp.lean`), `I` in program syntax; goals `body`
    (`phoare[ test ==> I ] ≤ I { body }`), `exit` (simplified, reads generalized), then the code
    before the loop with expectation `I`.
  * Union-bound helpers: `indicatorE_or_le`, `ENNReal.sum_indicatorE_eq_div_card`;
    `Bool.or_eq_true` in the simp set (`beq_iff_eq` is *not*: it pre-empts `Bool.true_beq` and
    turns `(true == v) = true` into `true = v`).
  * Milestone 2 (`Examples/GuessingGame.lean`, `game_hit_le`): an abstract guesser, `q` rounds,
    a fresh uniform secret after each guess: `phoare[ Game(A) (q) : q = n ==> hit ] ≤ n / |X|`,
    with the potential `indicatorE hit + (q − i) / |X|`.  Loop, exit and set-up goals are one
    line each; the per-round step is a ~15-line `calc` (pointwise bound, `ewp_const_le`, the
    union bound, arithmetic).
