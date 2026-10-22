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
2. **Calls with specs**: `phoare_call h` for `≤`/`≥` (monotonicity) and `=`; lossless rule
   (post constant in the call's result); frame variant via the footprint lemmas.
3. **Loops**: `phoare_while_le I` (expectation invariant, `wp_while_invariant`); lower bounds
   need termination — variant / bounded-counter rule from Kleene iterates
   (`expected_while_lfp_iSup`, `Logic/PRHL2.lean`); then EC's `fel`
   (`Pr[bad] ≤ ∑_{i<q} f i`), generalizing `loop_n_wp_linear_bound`.
4. **`islossless` tactic.**

## Milestones

1. Re-prove `hi_ll` and `fakecommit_half` (`Examples/Pedersen/Hiding.lean`) with the tactics
   (phases 0–2).
2. Abstract adversary hitting a fresh uniform secret within `q` queries:
   `phoare[ … : True ==> hit ] <= q / |X|` (phase 3, `fel`).
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
