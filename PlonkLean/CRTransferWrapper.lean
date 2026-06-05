import PlonkLean.CollisionResistance

/-!
# CR transfer via the wrapper approach (post-parameterization)

Sketch of the wrapper alternative to `Program.transfer`. With `oracle_loop`
and `claim_5_subprob` now parameterised over an arbitrary adversary, the
**cheat axiom** that the previous version of this file needed
(`adv_eq_cr_adv_wrapped`) is gone. The structural friction is genuinely
lower: instantiate `oracle_loop`'s adversary slot with `cr_adv_wrapped`,
and the existing claim-5 machinery applies.

What still remains:

* **State pollution.** The wrapper introduces two new state variables
  (`cr_counter`, `cr_first_y`) as encoding artifacts. They aren't part of
  the natural formulation of `cr_experiment`. Each new experiment built
  via this wrapper pattern would need its own counter/holder pair.

* **Init mismatch.** `cr_experiment q init oracle` runs just `init`, but
  the `oracle_loop` slot needs an init that also initializes `cr_counter`.
  Wrapping fixes this (`cr_init_wrapped`), but means we apply
  `claim_5_subprob` to `cr_init_wrapped q lazy_init` rather than the bare
  `lazy_init` it was originally stated for. The proof goes through — but
  only because `set cr_counter` is RO-invariant — which is a fact someone
  still has to prove.

* **The equivalence is heavy.** Proving `cr_experiment ≡ wrapped oracle_loop`
  still requires Kleene-style induction matching the wrapper's `q+3`
  iterations to `cr_experiment`'s structure (~150-250 lines).

So even after the medium refactor, the wrapper approach trades the
"closure under bind" of the transfer framework for "structural matching"
between two different program shapes. The transfer approach scales better
for new experiments; the wrapper approach is only competitive when the
target shape already matches `oracle_loop`.

This file is kept as a **template** for what the wrapper approach looks
like now. Both main theorems (`cr_experiment_eq_oracle_loop_marginal` and
`cr_transfer_via_wrapper`) are `sorry` — completing them is a non-trivial
exercise but is no longer obstructed.
-/

/-! ### New state variables and disjointness axioms (still required) -/

/-- Phase counter for the wrapper. -/
axiom cr_counter : Variable Nat
/-- Holds the first verification query's output across iterations. -/
axiom cr_first_y : Variable output

axiom disjoint_cr_counter_ro : disjoint cr_counter random_oracle_state
axiom disjoint_cr_first_y_ro : disjoint cr_first_y random_oracle_state

attribute [instance] disjoint_cr_counter_ro disjoint_cr_first_y_ro

section WrapperSection

/-! ### The wrapper adversary

Parameterised over the inner CR adversary `cr_adv`. The wrapper reads
`cr_counter` to decide what to do this iteration:

* `> 2`: a "loop round" — run the inner `cr_adv` (which writes
  `oracle_input` as usual), then decrement.
* `= 2`: prepare the first verification — write `claim_x` to `oracle_input`.
* `= 1`: capture the result of the first verification (`oracle_output` was
  set by the loop's call to `oracle`), then prepare the second verification.
* `= 0`: compute the result bit, write it to `adversary_result`, and set
  `want_more := false` to terminate the loop.

Unlike the pre-parameterization version, `cr_adv_wrapped` is now an
ordinary function returning a `Program`, not something that needs to be
identified with the (no-longer-existing) global `adv` axiom. -/
noncomputable def cr_adv_wrapped (cr_adv : Program state Unit) :
    Program state Unit := do
  let c ← Program.get cr_counter
  match c with
  | 0 => do
      let y ← Program.get cr_first_y
      let y' ← Program.get oracle_output
      let x ← Program.get claim_x
      let x' ← Program.get claim_x'
      Program.set adversary_result (decide (x ≠ x' ∧ y = y'))
      Program.set want_more false
  | 1 => do
      let y ← Program.get oracle_output
      Program.set cr_first_y y
      let x' ← Program.get claim_x'
      Program.set oracle_input x'
      Program.set cr_counter 0
  | 2 => do
      let x ← Program.get claim_x
      Program.set oracle_input x
      Program.set cr_counter 1
  | (c + 3) => do
      cr_adv
      Program.set cr_counter (c + 2)

variable (cr_adv : Program state Unit)
    (h_cr_adv : cr_adv.inRange random_oracle_state.compl.range)

include h_cr_adv in
/-- The wrapper adversary itself is RO-disjoint (assuming the inner one is).
    This is the hypothesis we'd need to feed to `oracle_loop`'s parameter slot. -/
private lemma cr_adv_wrapped_inRange :
    (cr_adv_wrapped cr_adv).inRange random_oracle_state.compl.range := by
  -- `cr_adv_wrapped` uses cr_adv (inRange RO.compl by hypothesis) plus
  -- reads/writes on cr_counter, cr_first_y, oracle_output, claim_x,
  -- claim_x', oracle_input, adversary_result, want_more — all disjoint from RO.
  -- Each branch of the match is a bind chain of RO-disjoint ops.
  --
  -- The proof would walk the four match branches, applying
  -- `Program.inRange_bind`, `Program.inRange_get`, `Program.inRange_set`,
  -- `Program.inRange_mono`, and the disjoint-to-compl helper.
  sorry

/-! ### Wrapped init

`cr_experiment` runs `init` alone, but the `oracle_loop` slot needs `init`
plus a counter initialization. -/
noncomputable def cr_init_wrapped (q : ℕ) (init : Program state Unit) :
    Program state Unit := do
  init
  Program.set cr_counter (q + 2)

/-! ### The equivalence (still heavy) -/

theorem cr_experiment_eq_oracle_loop_marginal
    (q : ℕ) (σ₀ : state)
    (init : Program state Unit) (oracle : input → Program state output) :
    (cr_experiment cr_adv q init oracle σ₀ >>=
        fun bσ : Bool × state => (pure bσ.1 : SubProbability Bool))
    =
    (oracle_loop (cr_adv_wrapped cr_adv) (cr_init_wrapped q init) oracle σ₀ >>=
        fun bσ : Bool × state => (pure bσ.1 : SubProbability Bool)) := by
  -- Proof outline (not implemented; ~150-250 lines):
  --
  -- * Unfold `cr_experiment` and `oracle_loop` to expose binds.
  -- * Do `q + 3` rounds of `wp_while_unfold` on the RHS to match the
  --   finite structure of the LHS.
  -- * At each round, the wrapper's match-on-counter and the experiment's
  --   corresponding action coincide. The `cr_first_y` write at counter 1
  --   threads the value y from the first verification query to counter 0
  --   where the decide is computed.
  -- * Project to Bool: state differences (cr_counter, cr_first_y, want_more,
  --   adversary_result) are discarded by the marginal projection.
  --
  -- This is genuinely the kind of proof that the `Program.transfer`
  -- framework avoids — there closure under bind handles structural
  -- matching automatically; here it's bespoke.
  sorry

include h_cr_adv in
theorem cr_transfer_via_wrapper (q : ℕ) (σ₀ : state) :
    (cr_experiment cr_adv q lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state => (pure bσ.1 : SubProbability Bool))
    =
    (cr_experiment cr_adv q random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state => (pure bσ.1 : SubProbability Bool)) := by
  rw [cr_experiment_eq_oracle_loop_marginal cr_adv,
      cr_experiment_eq_oracle_loop_marginal cr_adv]
  -- With parameterized `oracle_loop`, the cheat axiom is no longer needed:
  -- pass `cr_adv_wrapped cr_adv` and its inRange proof
  -- (`cr_adv_wrapped_inRange`) to the parameterized `claim_5_subprob`.
  --
  -- Remaining work:
  -- * Show `cr_init_wrapped q init` is RO-invariant in the sense
  --   `claim_5_subprob` needs (i.e. `set cr_counter` commutes with `convert`).
  --   This is provable from disjointness.
  -- * Apply `claim_5_subprob` with `h := fun _ => ()` (or similar trivial
  --   projection) to extract just the Bool marginal.
  sorry

end WrapperSection

/-! ## Tally — what changed after the medium refactor

What this file contains vs. the transfer file:

| Item | Transfer (proved) | Wrapper (still sorry'd) |
|---|---|---|
| New `Variable` axioms | 0 | 2 (`cr_counter`, `cr_first_y`) |
| New disjointness axioms | 0 | 2 |
| Cheat axioms | 0 | **0 (was 1 pre-refactor)** |
| Wrapper definition | n/a | concrete, ~25 lines |
| Equivalence proof | n/a | sorry (~150-250 lines estimated) |
| Application proof | ~3 lines | sorry, plus extra structural work |
| Reusable for new experiments | yes (closure lemmas) | no (each experiment needs its own wrapper) |

The cheat axiom was the most embarrassing cost of the wrapper approach,
and it's gone. The remaining costs (state pollution, init mismatch, heavy
equivalence proof) are inherent to wrapping `cr_experiment` into
`oracle_loop`'s shape rather than to the framework. -/
