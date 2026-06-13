import GaudisCrypt.Lib.RO
import GaudisCrypt.Lib.Birthday

/-!
# Collision resistance of the random oracle

A 101-crypto example exercising the framework. We define the standard
collision-resistance game (`cr_experiment`) parameterised by a query budget
`q`, an `init` step, and a `query` step. Two flavours are then obtained by
plugging in `lazy_*` or `random_oracle_*` (= eager) primitives.

The high-level claims are:

* `cr_transfer` — the collision probability is identical under lazy and
  eager random oracle (proved via `oracle_loop_wp_lazy_eq_random_oracle`).
* `cr_lazy_bound` — the lazy collision probability is bounded by the
  birthday bound `(q+2)(q+1) / (2 · |output|)` (the +2 accounts for the
  final two collision-check queries).
* `cr_eager_bound` — the same bound for eager, by `cr_transfer`.

All results below are fully proved (no `sorry`): the transfer via the
`Program.transfer` framework, and the birthday bound by a unary
wp-expectation induction.
-/

/-- The CR adversary's two collision claims, stored in state. -/
axiom claim_x : Variable input
axiom claim_x' : Variable input

/-- Disjointness: the claim variables don't alias the RO state. -/
axiom disjoint_claim_x_ro : disjoint claim_x random_oracle_state
axiom disjoint_claim_x'_ro : disjoint claim_x' random_oracle_state

attribute [instance] disjoint_claim_x_ro disjoint_claim_x'_ro

/-- Output equality needed for the collision check. We get it for free
    from classical logic (the rest of the file is noncomputable anyway). -/
noncomputable instance : DecidableEq output := Classical.decEq output

/-! ## CR experiment parameterised over an adversary

`cr_adv` is a *parameter* (via the `variable` declaration below), not an
axiom. Every `cr_experiment`-, `cr_lazy_bound`-, `cr_transfer`-style
definition and theorem in this section takes an arbitrary CR adversary
`cr_adv : Program state Unit` together with `h_cr_adv : cr_adv.inRange ...`.

The adversary may set `oracle_input` (queried each round), may set
`claim_x` and `claim_x'` (its candidate collision), and may *not* touch
`random_oracle_state` directly. -/

section CRParam

variable (cr_adv : Program state Unit)

/-- One round of the CR loop body: the adversary computes, then we run one
    query on whatever `cr_adv` placed in `oracle_input`. Thin alias for the
    generic `oracle_step` in `RO.lean`. -/
noncomputable def cr_loop_body (oracle : input → Program state output) :
    Program state Unit := oracle_step cr_adv oracle

/-- Run the adversary-and-query loop for `q` rounds. Thin alias for the
    generic `oracle_loop_n` in `RO.lean`. -/
noncomputable def cr_loop (q : ℕ) (oracle : input → Program state output) :
    Program state Unit := oracle_loop_n cr_adv q oracle

/-- **The CR experiment** parameterised by query budget `q`, init, and oracle.

    Run the adversary for `q` rounds, then read its claim `(x, x')`, query the
    oracle at both, and report whether `(x ≠ x') ∧ (y = y')`. -/
noncomputable def cr_experiment (q : ℕ)
    (init : Program state Unit)
    (oracle : input → Program state output) : Program state Bool := do
  init
  cr_loop cr_adv q oracle
  let x  ← Program.get claim_x
  let x' ← Program.get claim_x'
  let y  ← oracle x
  let y' ← oracle x'
  pure (decide (x ≠ x' ∧ y = y'))

/-! ## Phase 2 — Transfer (lazy = eager)

The output of `cr_experiment` is RO-invariant (it only depends on state
variables disjoint from `random_oracle_state`), so the dist of the result
bit agrees under lazy and eager RO. -/

variable (h_cr_adv : cr_adv.inRange random_oracle_state.compl.range)

/-! ### Building blocks for `cr_transfer` via the `Program.transfer` framework. -/

include h_cr_adv in
/-- `cr_adv` transfers to itself: it doesn't touch RO. -/
private lemma transfer_cr_adv : Program.transfer cr_adv cr_adv :=
  Program.transfer_refl_of_inRange_compl h_cr_adv

include h_cr_adv in
/-- One iteration of `cr_loop_body` transfers from lazy to eager. -/
private lemma transfer_cr_loop_body :
    Program.transfer (cr_loop_body cr_adv lazy_query)
                     (cr_loop_body cr_adv random_oracle_query) :=
  Program.transfer_oracle_step h_cr_adv

include h_cr_adv in
/-- `cr_loop q` transfers from lazy to eager. -/
private lemma transfer_cr_loop (q : ℕ) :
    Program.transfer (cr_loop cr_adv q lazy_query) (cr_loop cr_adv q random_oracle_query) :=
  Program.transfer_oracle_loop_n h_cr_adv q

include h_cr_adv in
/-- The full `cr_experiment q` transfers from lazy to eager. -/
private lemma transfer_cr_experiment (q : ℕ) :
    Program.transfer
      (cr_experiment cr_adv q lazy_init lazy_query)
      (cr_experiment cr_adv q random_oracle_init random_oracle_query) := by
  show Program.transfer
    (lazy_init >>= fun _ => cr_loop cr_adv q lazy_query >>= fun _ =>
      Program.get claim_x >>= fun x => Program.get claim_x' >>= fun x' =>
        lazy_query x >>= fun y => lazy_query x' >>= fun y' =>
          (pure (decide (x ≠ x' ∧ y = y')) : Program state Bool))
    (random_oracle_init >>= fun _ => cr_loop cr_adv q random_oracle_query >>= fun _ =>
      Program.get claim_x >>= fun x => Program.get claim_x' >>= fun x' =>
        random_oracle_query x >>= fun y => random_oracle_query x' >>= fun y' =>
          (pure (decide (x ≠ x' ∧ y = y')) : Program state Bool))
  apply Program.transfer_bind Program.transfer_lazy_init
  intro _
  apply Program.transfer_bind (transfer_cr_loop cr_adv h_cr_adv q)
  intro _
  apply Program.transfer_bind (Program.transfer_get_of_disjoint_ro claim_x)
  intro x
  apply Program.transfer_bind (Program.transfer_get_of_disjoint_ro claim_x')
  intro x'
  apply Program.transfer_bind (Program.transfer_lazy_query x)
  intro y
  apply Program.transfer_bind (Program.transfer_lazy_query x')
  intro y'
  exact Program.transfer_pure _

/-- `convert` is absorbed by the eager `cr_experiment` (it starts with
    `random_oracle_init`, which overwrites RO via a fresh uniform sample).
    Thin wrapper over the generic `convert_bind_random_oracle_init_bind`. -/
private lemma convert_cr_experiment_eager (q : ℕ) :
    (convert >>= fun _ =>
      cr_experiment cr_adv q random_oracle_init random_oracle_query)
    = cr_experiment cr_adv q random_oracle_init random_oracle_query :=
  convert_bind_random_oracle_init_bind _

include h_cr_adv in
/-- **Transfer theorem**: The marginal distribution of the result bit is
    identical under lazy and eager random oracle. -/
theorem cr_transfer (q : ℕ) (σ₀ : state) :
    (cr_experiment cr_adv q lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state => (pure bσ.1 : SubProbability Bool))
    =
    (cr_experiment cr_adv q random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state => (pure bσ.1 : SubProbability Bool)) :=
  Program.transfer_value_marginal (transfer_cr_experiment cr_adv h_cr_adv q)
    (convert_cr_experiment_eager cr_adv q) σ₀

/-! ## Phase 3 — Birthday bound on the lazy CR experiment

The proof is decomposed into helper lemmas and a top-level
composition. The composition `cr_lazy_bound` itself is
*proved* — no `sorry` — modulo the two helpers.

* `cr_true_implies_collision_wp` (bookkeeping): if the experiment's
  result bit is `true`, then the final state has a collision. This is
  a structural / support-analysis fact: `cr_experiment` writes
  `lazy_query x` and `lazy_query x'` into the RO table before
  returning `decide (x ≠ x' ∧ y = y')`, so a `true` return implies
  `RO[x] = RO[x'] = some y` with `x ≠ x'`.

* `cr_collision_birthday_bound` (the real probability work): the
  expected collision indicator is bounded by `(q+2)(q+1) / (2·N)`.
  This is the actual birthday argument — a union bound over pairs of
  distinct queried inputs, each pair colliding with probability ≤ 1/N
  because lazy_query yields uniform fresh samples.
-/

/-- A state has a "collision": two distinct inputs both have cached RO
    values, and those cached values are equal. -/
def has_collision (σ : state) : Prop :=
  ∃ x x' : input, x ≠ x' ∧
    ∃ y : output,
      random_oracle_state.get σ x = some y ∧
      random_oracle_state.get σ x' = some y

noncomputable instance : DecidablePred has_collision :=
  fun _ => Classical.propDecidable _

/-- 0/1-valued collision indicator on state. -/
noncomputable def collision_indicator (σ : state) : ENNReal :=
  if has_collision σ then 1 else 0

/-! ### Helper: `lazy_query` postcondition strengthening -/

/-- **`lazy_query` support strengthening**: if an invariant `I : output → state → Prop`
    holds at every state reachable from `lazy_query x σ` — namely, on the cached
    output (when the entry is cached) and on every fresh-sample post-state (when
    not cached) — then strengthening the postcondition with `if I then F else 0`
    leaves the `wp` value unchanged. -/
lemma lazy_query_wp_strengthen
    {x : input} {σ : state} {I : output → state → Prop}
    [DecidablePred (fun yσ : output × state => I yσ.1 yσ.2)]
    (h_cache : ∀ y_cache, random_oracle_state.get σ x = some y_cache → I y_cache σ)
    (h_fresh : ∀ value, random_oracle_state.get σ x = none → I value
      (random_oracle_state.set
        (fun x' => if x' = x then some value else random_oracle_state.get σ x') σ))
    (F : output × state → ENNReal) :
    (lazy_query x).wp F σ
      = (lazy_query x).wp
          (fun yσ : output × state => if I yσ.1 yσ.2 then F yσ else 0) σ := by
  simp only [lazy_query, wp_bind, wp_get]
  cases h_cache_state : random_oracle_state.get σ x with
  | some y_cache =>
    simp only [wp_pure]
    rw [if_pos (h_cache y_cache h_cache_state)]
  | none =>
    simp only [wp_bind, wp_uniform, wp_set, wp_pure]
    apply Finset.sum_congr rfl
    intro value _
    congr 1
    rw [if_pos (h_fresh value h_cache_state)]

/-- **`lazy_query` writes its output**: integrating any `F` against
    `lazy_query x σ` is the same as integrating `F` restricted to states
    where `RO[x] = some (returned y)`. -/
lemma lazy_query_wp_writes_output
    (x : input) (F : output × state → ENNReal) (σ : state) :
    (lazy_query x).wp F σ
      = (lazy_query x).wp
          (fun yσ : output × state =>
            if random_oracle_state.get yσ.2 x = some yσ.1 then F yσ else 0) σ := by
  apply lazy_query_wp_strengthen
    (I := fun y σ' => random_oracle_state.get σ' x = some y)
  · intro _ h; exact h
  · intro value _; show random_oracle_state.get _ x = some value
    rw [random_oracle_state.set_get]; exact if_pos rfl

/-- **`lazy_query` preserves disjoint state**: querying doesn't change
    the value of any variable disjoint from `random_oracle_state`. -/
lemma lazy_query_wp_preserves_disjoint {α : Type} [DecidableEq α]
    (v : Variable α) [disjoint v random_oracle_state]
    (x : input) (F : output × state → ENNReal) (σ : state) :
    (lazy_query x).wp F σ
      = (lazy_query x).wp
          (fun yσ : output × state =>
            if v.get yσ.2 = v.get σ then F yσ else 0) σ :=
  letI := (inferInstance : disjoint v random_oracle_state).symm
  lazy_query_wp_strengthen
    (I := fun _ σ' => v.get σ' = v.get σ)
    (fun _ _ => rfl)
    (fun _ _ => v.get_of_disjoint_set random_oracle_state _ σ)
    F

/-- **`lazy_query` preserves other RO entries**: querying `x` doesn't
    change `RO[x']` for `x' ≠ x`. -/
lemma lazy_query_wp_preserves_other_RO
    (x x' : input) (h_neq : x' ≠ x) (F : output × state → ENNReal) (σ : state) :
    (lazy_query x).wp F σ
      = (lazy_query x).wp
          (fun yσ : output × state =>
            if random_oracle_state.get yσ.2 x' = random_oracle_state.get σ x'
              then F yσ else 0) σ := by
  apply lazy_query_wp_strengthen
    (I := fun _ σ' => random_oracle_state.get σ' x' = random_oracle_state.get σ x')
  · intro _ _; rfl
  · intro _ _; show random_oracle_state.get _ x' = random_oracle_state.get σ x'
    rw [random_oracle_state.set_get, if_neg h_neq]

/-- **Bookkeeping helper**: at every state in the support of
    `cr_experiment cr_adv q lazy_init lazy_query`, if the result bit is `true`
    then the state has a collision. Stated at the `wp` level so it
    composes with the birthday bound below.

    **Proof plan** (~80-100 lines; helpers all in place):

    1. Goal after `simp only [cr_experiment, wp_bind, wp_get, wp_pure]`:
       wp-tower with both `lazy_query` calls visible. Call the inner state
       parameters `σ₂` (after `cr_loop`), `σ₅` (after first lazy_query),
       `σ₆` (after second).

    2. Apply `lazy_query_wp_writes_output` to the *first* lazy_query
       (returning `y` from `x_v = claim_x.get σ₂`). This strengthens the
       postcondition of `lazy_query x_v` with `RO[x_v] = some y` at `σ₅`.

    3. Apply `lazy_query_wp_writes_output` to the *second* lazy_query
       (`y' ← lazy_query x'_v`). Postcondition gains `RO[x'_v] = some y'`
       at `σ₆`.

    4. Apply `lazy_query_wp_preserves_other_RO` to the second lazy_query
       with `x = x'_v, x' = x_v` (under `x_v ≠ x'_v`): `RO[x_v]` preserved
       from `σ₅` to `σ₆`, so still `= some y` at `σ₆`.

    5. Apply `lazy_query_wp_preserves_disjoint` to both lazy_query calls
       for `claim_x` and `claim_x'`. These give us `claim_x.get σ₆ = x_v`
       and `claim_x'.get σ₆ = x'_v`.

    6. At the leaf, with all invariants strengthened into the post:
       result = `decide (x_v ≠ x'_v ∧ y = y') = true` ⟹
       `claim_x.get σ₆ = x_v ≠ x'_v = claim_x'.get σ₆`, and
       `RO[x_v] = some y = some y' = RO[x'_v]` at `σ₆`. So
       `has_collision σ₆` with witnesses `(x_v, x'_v, y)`.

    7. The strengthened post is pointwise ≤ `collision_indicator σ₆`;
       apply `MeasureTheory.lintegral_mono` propagated outward through
       each wp_bind layer. -/
lemma cr_true_implies_collision_wp (q : ℕ) (σ₀ : state) :
    (cr_experiment cr_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ₀
    ≤ (cr_experiment cr_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => collision_indicator bσ.2) σ₀ := by
  simp only [cr_experiment, wp_bind, wp_get, wp_pure]
  -- Propagate via wp_le_wp_of_le through init and cr_loop.
  apply Program.wp_le_wp_of_le
  rintro ⟨_, σ_1⟩
  apply Program.wp_le_wp_of_le
  rintro ⟨_, σ_2⟩
  -- Now at σ_2 level: goal is
  --   (lazy_query (claim_x.get σ_2)).wp (fun (y, σ_5) =>
  --     (lazy_query (claim_x'.get σ_2)).wp (fun (y', σ_6) =>
  --       if decide (claim_x.get σ_2 ≠ claim_x'.get σ_2 ∧ y = y') then 1 else 0) σ_5) σ_2
  --   ≤ same with collision_indicator σ_6.
  --
  -- Case-split on whether the claims are equal.
  by_cases h_eq : claim_x.get σ_2 = claim_x'.get σ_2
  · -- Equal: bool is forced to false, so LHS integrand is 0.
    -- The inner if condition `claim_x.get σ_2 ≠ claim_x'.get σ_2` is false.
    have h_inner_zero : ∀ (y : output) (σ_5 : state),
        (lazy_query (claim_x'.get σ_2)).wp
          (fun yσ : output × state =>
            if decide (claim_x.get σ_2 ≠ claim_x'.get σ_2 ∧ y = yσ.1) then (1 : ENNReal) else 0)
          σ_5 = 0 := by
      intro y σ_5
      have h_const_zero : (fun yσ : output × state =>
            if decide (claim_x.get σ_2 ≠ claim_x'.get σ_2 ∧ y = yσ.1) then (1 : ENNReal) else 0)
          = (fun _ : output × state => (0 : ENNReal)) := by
        funext yσ
        simp [h_eq]
      rw [h_const_zero]
      exact Program.wp_zero_post _ _
    have h_outer_zero :
        (lazy_query (claim_x.get σ_2)).wp (fun yσ : output × state =>
          (lazy_query (claim_x'.get σ_2)).wp
            (fun yσ' : output × state =>
              if decide (claim_x.get σ_2 ≠ claim_x'.get σ_2 ∧ yσ.1 = yσ'.1)
                then (1 : ENNReal) else 0) yσ.2) σ_2 = 0 := by
      have h_const_zero : (fun yσ : output × state =>
            (lazy_query (claim_x'.get σ_2)).wp
              (fun yσ' : output × state =>
                if decide (claim_x.get σ_2 ≠ claim_x'.get σ_2 ∧ yσ.1 = yσ'.1)
                  then (1 : ENNReal) else 0) yσ.2)
          = (fun _ : output × state => (0 : ENNReal)) := by
        funext yσ
        exact h_inner_zero yσ.1 yσ.2
      rw [h_const_zero]
      exact Program.wp_zero_post _ _
    rw [h_outer_zero]
    exact bot_le
  · -- Not equal case: x_v ≠ x'_v where x_v = claim_x.get σ_2, x'_v = claim_x'.get σ_2.
    -- Apply strengthening helpers to the OUTER lazy_query (for x_v).
    -- This wraps the postcondition in `if RO σ_5 x_v = some y then ... else 0` etc.
    -- Both LHS and RHS get the same strengthening (since rw matches both).
    rw [lazy_query_wp_writes_output (claim_x.get σ_2)]
    rw [lazy_query_wp_preserves_disjoint claim_x (claim_x.get σ_2)]
    rw [lazy_query_wp_preserves_disjoint claim_x' (claim_x.get σ_2)]
    -- Descend to σ_5 level.
    apply Program.wp_le_wp_of_le
    rintro ⟨y, σ_5⟩
    -- Goal: nested ifs over (y, σ_5) with INNER wp at the bottom.
    -- Split on each if.
    split_ifs with h_cx5 h_cx'5 h_RO5
    · -- All ifs true: claim_x.get σ_5 = claim_x.get σ_2, claim_x'.get σ_5 = claim_x'.get σ_2,
      -- RO σ_5 (claim_x.get σ_2) = some y.
      -- Now strengthen the INNER lazy_query (for x'_v).
      rw [lazy_query_wp_writes_output (claim_x'.get σ_2)]
      rw [lazy_query_wp_preserves_disjoint claim_x (claim_x'.get σ_2)]
      rw [lazy_query_wp_preserves_disjoint claim_x' (claim_x'.get σ_2)]
      rw [lazy_query_wp_preserves_other_RO (claim_x'.get σ_2) (claim_x.get σ_2) h_eq]
      -- Descend to σ_6 level.
      apply Program.wp_le_wp_of_le
      rintro ⟨y', σ_6⟩
      -- Goal: nested ifs with leaf `if decide(x_v ≠ x'_v ∧ y = y') then 1 else 0` vs `collision_indicator σ_6`.
      split_ifs with h_RO6_x h_cx'6 h_cx6 h_RO6_x' h_decide
      · -- All invariants AND decide true.
        -- h_RO6_x : RO σ_6 (claim_x.get σ_2) = RO σ_5 (claim_x.get σ_2)
        -- h_cx'6 : claim_x'.get σ_6 = claim_x'.get σ_5
        -- h_cx6  : claim_x.get σ_6 = claim_x.get σ_5
        -- h_RO6_x' : RO σ_6 (claim_x'.get σ_2) = some y'
        -- h_decide: decide (claim_x.get σ_2 ≠ claim_x'.get σ_2 ∧ y = y') = true
        have h_AND : claim_x.get σ_2 ≠ claim_x'.get σ_2 ∧ y = y' := of_decide_eq_true h_decide
        have h_has_collision : has_collision σ_6 := by
          refine ⟨claim_x.get σ_2, claim_x'.get σ_2, h_AND.1, y, ?_, ?_⟩
          · -- RO σ_6 (claim_x.get σ_2) = some y
            rw [h_RO6_x, h_RO5]
          · -- RO σ_6 (claim_x'.get σ_2) = some y
            rw [h_RO6_x', ← h_AND.2]
        simp [collision_indicator, h_has_collision]
      all_goals (first | exact bot_le | (simp [collision_indicator]; exact bot_le))
    all_goals exact bot_le

/-! ### Birthday-bound decomposition

The proof is decomposed into:

* `RO_size` — counts the cached entries of the random oracle.
* `lazy_query_collision_step` (Layer A) — each query bumps the collision
  probability by at most `RO_size σ / N`. Core probability content.
* `lazy_query_RO_size_step` (Layer B, *proved*) — each query's expected
  `RO_size` grows by at most 1. Combinatorial.
* `cr_loop_birthday_step` (Layer C) — combining A and B over `cr_loop k`:
  after `k` queries the collision bump is at most the triangular sum
  `k * (2 * RO_size σ + k - 1) / (2N)`.
* `cr_collision_birthday_bound` (Layer D, *proved* modulo A & C) — combines
  `cr_loop q` with the two final queries.
-/

/-- The number of cached entries in the random oracle state. -/
noncomputable def RO_size (σ : state) : ℕ :=
  (Finset.filter (fun x => (random_oracle_state.get σ x).isSome) Finset.univ).card

/-! ### Layer A and its sublemmas

`lazy_query_collision_step` (Layer A): each `lazy_query` bumps the collision
probability by at most `RO_size σ / N`. The fresh-sample case is a union bound:
each uniform sample collides with at most `RO_size σ` existing entries (each
with probability `1/N`). Decomposed into 5 helpers below. -/

/-- The Finset of output values that a fresh sample at `x` could collide with:
    values that already appear in the RO at some other input. -/
noncomputable def inducing_set (x : input) (σ : state) : Finset output :=
  ((Finset.univ.erase x).filter
    (fun x' => (random_oracle_state.get σ x').isSome)).image
    (fun x' => (random_oracle_state.get σ x').getD default)

/-- Membership characterization. -/
lemma mem_inducing_set_iff (x : input) (σ : state) (y : output) :
    y ∈ inducing_set x σ ↔
      ∃ x' : input, x' ≠ x ∧ random_oracle_state.get σ x' = some y := by
  unfold inducing_set
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x', hx'_mem, h_eq⟩
    rw [Finset.mem_filter, Finset.mem_erase] at hx'_mem
    obtain ⟨⟨hx'_ne_x, _⟩, h_isSome⟩ := hx'_mem
    refine ⟨x', hx'_ne_x, ?_⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h_isSome
    rw [hv] at h_eq
    simp at h_eq
    rw [hv, h_eq]
  · rintro ⟨x', hx'_ne_x, hRO⟩
    refine ⟨x', ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_erase]
      refine ⟨⟨hx'_ne_x, Finset.mem_univ _⟩, ?_⟩
      rw [hRO]; rfl
    · rw [hRO]; rfl

/-- The inducing set has at most `RO_size σ` elements. -/
lemma inducing_set_card_le_RO_size (x : input) (σ : state) :
    (inducing_set x σ).card ≤ RO_size σ := by
  unfold inducing_set
  apply le_trans Finset.card_image_le
  unfold RO_size
  apply Finset.card_le_card
  intro a ha
  rw [Finset.mem_filter] at ha
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, ha.2⟩

/-- Pointwise: after sampling `y`, the new collision indicator is bounded by
    the existing collision indicator plus 1 if `y` is in the inducing set. -/
private lemma pointwise_collision_bound (x : input) (σ : state)
    (h_fresh : random_oracle_state.get σ x = none) (y : output) :
    collision_indicator (random_oracle_state.set
      (fun x' => if x' = x then some y else random_oracle_state.get σ x') σ)
    ≤ collision_indicator σ +
        (if y ∈ inducing_set x σ then (1 : ENNReal) else 0) := by
  set σ_y := random_oracle_state.set
    (fun x' => if x' = x then some y else random_oracle_state.get σ x') σ with hσ_y_def
  unfold collision_indicator
  by_cases h_sy : has_collision σ_y
  · rw [if_pos h_sy]
    obtain ⟨a, a', hne, z, hza, hza'⟩ := h_sy
    rw [hσ_y_def, random_oracle_state.set_get] at hza hza'
    by_cases ha_x : a = x
    · rw [ha_x, if_pos rfl] at hza
      have hyz : y = z := Option.some.inj hza
      have ha'_x : a' ≠ x := by intro h; apply hne; rw [ha_x, h]
      rw [if_neg ha'_x] at hza'
      have hP_y : y ∈ inducing_set x σ := by
        rw [mem_inducing_set_iff]
        refine ⟨a', ha'_x, ?_⟩
        rw [hza', hyz]
      rw [if_pos hP_y]
      exact le_add_self
    · rw [if_neg ha_x] at hza
      by_cases ha'_x : a' = x
      · rw [ha'_x, if_pos rfl] at hza'
        have hyz : y = z := Option.some.inj hza'
        have hP_y : y ∈ inducing_set x σ := by
          rw [mem_inducing_set_iff]
          refine ⟨a, ha_x, ?_⟩
          rw [hza, hyz]
        rw [if_pos hP_y]
        exact le_add_self
      · rw [if_neg ha'_x] at hza'
        have h_collision_σ : has_collision σ := ⟨a, a', hne, z, hza, hza'⟩
        rw [if_pos h_collision_σ]
        exact le_self_add
  · rw [if_neg h_sy]
    exact bot_le

lemma lazy_query_collision_step (x : input) (σ : state) :
    (lazy_query x).wp (fun yσ : output × state => collision_indicator yσ.2) σ
    ≤ collision_indicator σ + (RO_size σ : ENNReal) / Fintype.card output := by
  have h_step := lazy_query_wp_step collision_indicator
    (fun x' y σ' => if y ∈ inducing_set x' σ' then (1 : ENNReal) else 0)
    (fun x' σ' y h_cache => pointwise_collision_bound x' σ' h_cache y) x σ
  apply le_trans h_step
  gcongr
  rw [sum_indicator_eq_card_ENNReal _]
  exact_mod_cast inducing_set_card_le_RO_size x σ

/-- **Layer B**: the expected `RO_size` after one `lazy_query` is at most
    one more than before. (Tight: in the cached branch, equal; in the fresh
    branch, exactly `+1`.) Reduced to the generic `lazy_query_wp_step` with
    pointwise bad-event `1`. -/
lemma lazy_query_RO_size_step (x : input) (σ : state) :
    (lazy_query x).wp (fun yσ : output × state => (RO_size yσ.2 : ENNReal)) σ
    ≤ (RO_size σ + 1 : ENNReal) := by
  -- Pointwise: at every cache-miss with new sample y, RO_size grows by exactly 1.
  have h_pointwise : ∀ x' σ' y, random_oracle_state.get σ' x' = none →
      ((RO_size (random_oracle_state.set
          (fun x'' => if x'' = x' then some y else random_oracle_state.get σ' x'') σ')
        : ENNReal)) ≤ (RO_size σ' : ENNReal) + 1 := by
    intro x' σ' y h_cache
    -- RO_size of the extended state is RO_size σ' + 1.
    have h_size_eq : RO_size (random_oracle_state.set
          (fun x'' => if x'' = x' then some y else random_oracle_state.get σ' x'') σ')
        = RO_size σ' + 1 := by
      unfold RO_size
      have h_filter_eq : Finset.filter
          (fun x'' => (random_oracle_state.get (random_oracle_state.set
            (fun x''' => if x''' = x' then some y else random_oracle_state.get σ' x''') σ') x'').isSome)
          Finset.univ
        = insert x' (Finset.filter
            (fun x'' => (random_oracle_state.get σ' x'').isSome) Finset.univ) := by
        ext x''
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                   random_oracle_state.set_get]
        by_cases hxx : x'' = x'
        · subst hxx; simp
        · simp [hxx]
      rw [h_filter_eq, Finset.card_insert_of_notMem]
      intro h_mem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, h_cache,
                 Option.isSome_none, Bool.false_eq_true] at h_mem
    rw [h_size_eq]; push_cast; rfl
  have h_step := lazy_query_wp_step (fun s => (RO_size s : ENNReal))
    (fun _ _ _ => (1 : ENNReal)) h_pointwise x σ
  apply le_trans h_step
  gcongr
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ENNReal.div_self _ (ENNReal.natCast_ne_top _)]
  exact_mod_cast Fintype.card_pos.ne'

-- `cr_loop_birthday_step` (Layer C) is defined below the helpers that follow.

/-- `RO_size` factors through the RO content: equal RO maps give equal sizes. -/
lemma RO_size_of_get_eq {σ σ' : state}
    (h : random_oracle_state.get σ' = random_oracle_state.get σ) :
    RO_size σ' = RO_size σ := by
  unfold RO_size
  congr 1
  ext x
  rw [h]

include h_cr_adv in
/-- `cr_adv` doesn't touch the RO, so its expected `RO_size` is preserved. -/
lemma cr_adv_wp_RO_size (σ : state) :
    cr_adv.wp (fun yσ : Unit × state => (RO_size yσ.2 : ENNReal)) σ
    ≤ (RO_size σ : ENNReal) :=
  Program.wp_le_of_factors (P := fun σ => (RO_size σ : ENNReal))
    random_oracle_state h_cr_adv
    (fun _ _ h => congrArg _ (RO_size_of_get_eq h)) σ

/-- Setting a variable disjoint from `random_oracle_state` doesn't change `RO_size`. -/
lemma RO_size_set_disjoint {α : Type} (v : Variable α) [disjoint v random_oracle_state]
    (x : α) (σ : state) : RO_size (v.set x σ) = RO_size σ :=
  RO_size_of_get_eq (random_oracle_state.get_of_disjoint_set v x σ)

include h_cr_adv in
/-- One iteration of `cr_loop_body` bumps `RO_size` by at most 1 in expectation.
    Reduced to the generic `oracle_step_wp_indicator_bump_const`. -/
lemma cr_loop_body_wp_RO_size (σ : state) :
    (cr_loop_body cr_adv lazy_query).wp
        (fun yσ : Unit × state => (RO_size yσ.2 : ENNReal)) σ
    ≤ (RO_size σ + 1 : ENNReal) :=
  oracle_step_wp_indicator_bump_const (1 : ENNReal)
    (cr_adv_wp_RO_size cr_adv h_cr_adv)
    (fun y σ' => by show (RO_size (oracle_output.set y σ') : ENNReal) = _;
                    rw [RO_size_set_disjoint])
    lazy_query_RO_size_step σ

include h_cr_adv in
/-- **Layer B-iterated**: expected `RO_size` after `cr_loop k` grows by at most
    `k`. Needed by Layer D to bound the size at intermediate points. Reduced
    to the generic `oracle_loop_n_wp_linear_bound` with `c = 1`. -/
lemma cr_loop_RO_size_step (k : ℕ) (σ : state) :
    (cr_loop cr_adv k lazy_query).wp
        (fun yσ : Unit × state => (RO_size yσ.2 : ENNReal)) σ
    ≤ (RO_size σ + k : ENNReal) := by
  have h := oracle_loop_n_wp_linear_bound
    (f := fun s => (RO_size s : ENNReal)) (c := 1)
    (fun σ' => cr_loop_body_wp_RO_size cr_adv h_cr_adv σ') k σ
  simpa [mul_one] using h

/-! ### Collision-side helpers (mirror of the RO_size helpers above) -/

/-- `collision_indicator` factors through the RO content. -/
lemma collision_indicator_of_get_eq {σ σ' : state}
    (h : random_oracle_state.get σ' = random_oracle_state.get σ) :
    collision_indicator σ' = collision_indicator σ := by
  unfold collision_indicator
  congr 1
  apply propext
  unfold has_collision
  constructor
  · rintro ⟨x, x', hne, y, hy, hy'⟩
    exact ⟨x, x', hne, y, h ▸ hy, h ▸ hy'⟩
  · rintro ⟨x, x', hne, y, hy, hy'⟩
    exact ⟨x, x', hne, y, h ▸ hy, h ▸ hy'⟩

include h_cr_adv in
/-- `cr_adv` doesn't touch the RO, so the collision indicator is preserved
    in expectation. -/
lemma cr_adv_wp_collision (σ : state) :
    cr_adv.wp (fun yσ : Unit × state => collision_indicator yσ.2) σ
    ≤ collision_indicator σ :=
  Program.wp_le_of_factors (P := collision_indicator)
    random_oracle_state h_cr_adv
    (fun _ _ h => collision_indicator_of_get_eq h) σ

/-- Setting a variable disjoint from `random_oracle_state` doesn't change
    `collision_indicator`. -/
lemma collision_indicator_set_disjoint {α : Type} (v : Variable α)
    [disjoint v random_oracle_state] (x : α) (σ : state) :
    collision_indicator (v.set x σ) = collision_indicator σ :=
  collision_indicator_of_get_eq (random_oracle_state.get_of_disjoint_set v x σ)

include h_cr_adv in
/-- One iteration of `cr_loop_body` bumps the collision indicator by at most
    `RO_size σ / N` (in expectation). Reduced to the generic
    `oracle_step_wp_indicator_bump`. -/
lemma cr_loop_body_wp_collision (σ : state) :
    (cr_loop_body cr_adv lazy_query).wp
        (fun yσ : Unit × state => collision_indicator yσ.2) σ
    ≤ collision_indicator σ + (RO_size σ : ENNReal) / Fintype.card output :=
  oracle_step_wp_indicator_bump
    (c := fun σ' => (RO_size σ' : ENNReal) / Fintype.card output)
    (cr_adv_wp_collision cr_adv h_cr_adv)
    (fun σ' => by
      -- adv.wp (RO_size σ'.2 / N) σ' ≤ RO_size σ' / N
      calc cr_adv.wp (fun yσ : Unit × state =>
              (RO_size yσ.2 : ENNReal) / Fintype.card output) σ'
          = (1 / Fintype.card output : ENNReal) *
              cr_adv.wp (fun yσ : Unit × state => (RO_size yσ.2 : ENNReal)) σ' := by
            rw [show (fun yσ : Unit × state =>
                    (RO_size yσ.2 : ENNReal) / Fintype.card output)
                  = (fun yσ : Unit × state =>
                      (1 / Fintype.card output : ENNReal) * (RO_size yσ.2 : ENNReal))
                from by funext yσ; rw [one_div, ← ENNReal.div_eq_inv_mul]]
            rw [Program.wp_const_mul]
        _ ≤ (1 / Fintype.card output : ENNReal) * (RO_size σ' : ENNReal) := by
            gcongr; exact cr_adv_wp_RO_size cr_adv h_cr_adv σ'
        _ = (RO_size σ' : ENNReal) / Fintype.card output := by
            rw [one_div, ← ENNReal.div_eq_inv_mul])
    (fun y σ' => collision_indicator_set_disjoint oracle_output y σ')
    lazy_query_collision_step σ

include h_cr_adv in
/-- **Layer C**: the cumulative collision bound after `cr_loop k` queries.
    Triangular sum of Layer A across the loop.

    Proof plan (induction on k):
    * Base k=0: cr_loop 0 = pure, no bump.
    * Step k+1: cr_loop_body bumps collision by ≤ RO_size σ / N (helper above).
      Then by IH at post-body state σ' (with RO_size σ' ≤ RO_size σ + 1 in
      expectation), the rest adds at most k(2*(RO_size σ + 1) + k - 1)/(2N)
      = k(2*RO_size σ + k + 1)/(2N). Combined: RO_size σ/N + k(2*RO_size σ + k + 1)/(2N)
      = (k+1)(2*RO_size σ + k)/(2N), matching the bound at level k+1. -/
lemma cr_loop_birthday_step (k : ℕ) (σ : state) :
    (cr_loop cr_adv k lazy_query).wp
        (fun yσ : Unit × state => collision_indicator yσ.2) σ
    ≤ collision_indicator σ
      + (k * (2 * RO_size σ + k - 1) : ENNReal) / (2 * Fintype.card output) := by
  rw [show (cr_loop cr_adv k lazy_query)
        = loop_n k (cr_loop_body cr_adv lazy_query) from
      oracle_loop_n_eq_loop_n cr_adv lazy_query k]
  exact loop_n_birthday_bound (cr_loop_body cr_adv lazy_query)
    collision_indicator RO_size (Fintype.card output)
    (by exact_mod_cast Fintype.card_pos.ne') (ENNReal.natCast_ne_top _)
    (cr_loop_body_wp_collision cr_adv h_cr_adv)
    (cr_loop_body_wp_RO_size cr_adv h_cr_adv) k σ

/-! ### `lazy_init` zeroing -/

/-- After `lazy_init`, the RO is empty: `RO_size = 0`. -/
lemma lazy_init_RO_size (σ₀ : state) :
    RO_size (random_oracle_state.set (fun _ => none) σ₀) = 0 := by
  unfold RO_size
  suffices h : Finset.filter
      (fun x => (random_oracle_state.get
        (random_oracle_state.set (fun _ : input => none) σ₀) x).isSome) Finset.univ = ∅ by
    rw [h]; rfl
  rw [Finset.filter_eq_empty_iff]
  intro x _
  rw [random_oracle_state.set_get]
  simp

/-- After `lazy_init`, no collision exists. -/
lemma lazy_init_collision_indicator (σ₀ : state) :
    collision_indicator (random_oracle_state.set (fun _ => none) σ₀) = 0 := by
  unfold collision_indicator
  rw [if_neg]
  intro ⟨x, x', _, y, hy, _⟩
  rw [random_oracle_state.set_get] at hy
  simp at hy

include h_cr_adv in
/-- **Layer D — `cr_collision_birthday_bound`**: composition of A, B, C.

    After `lazy_init`, `RO_size = 0`. After `cr_loop q`, by Layer C the bound is
    `q(q-1)/(2N)`. The two final queries add at most `(q + (q+1))/N` (via Layer
    A applied twice). Total: `(q+2)(q+1)/(2N)`. -/
lemma cr_collision_birthday_bound (q : ℕ) (σ₀ : state) :
    (cr_experiment cr_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => collision_indicator bσ.2) σ₀
    ≤ ((q + 2) * (q + 1) : ENNReal) / (2 * Fintype.card output) := by
  -- Set up notation
  set N : ENNReal := (Fintype.card output : ENNReal) with hN_def
  have hN_pos : N ≠ 0 := by rw [hN_def]; exact_mod_cast Fintype.card_pos.ne'
  have hN_top : N ≠ ⊤ := by rw [hN_def]; exact ENNReal.natCast_ne_top _
  -- Unfold cr_experiment to expose the structure
  simp only [cr_experiment, wp_bind, wp_get, wp_pure, lazy_init, wp_set,
             Program.set, wp_get_state, wp_set_state]
  -- After unfolding lazy_init: state becomes σ_1 = RO.set (fun _ => none) σ₀
  set σ_1 : state := random_oracle_state.set (fun _ : input => none) σ₀ with hσ_1
  -- σ_1 has RO_size 0 and collision_indicator 0
  have h_RO_size_σ_1 : RO_size σ_1 = 0 := lazy_init_RO_size σ₀
  have h_collision_σ_1 : collision_indicator σ_1 = 0 := lazy_init_collision_indicator σ₀
  -- Define abbreviations for the nested wp's
  -- Goal pattern: (cr_loop cr_adv q lazy_query).wp (fun (_, σ_2) =>
  --   (lazy_query x_v).wp (fun (_, σ_5) =>
  --     (lazy_query x'_v).wp (fun (_, σ_6) => collision_indicator σ_6) σ_5
  --   ) σ_2
  -- ) σ_1
  -- where x_v = claim_x.get σ_2 and x'_v = claim_x'.get σ_2.
  --
  -- Strategy:
  -- 1. Bound the innermost lazy_query x'_v: by Layer A, ≤ collision_indicator σ_5 + RO_size σ_5/N.
  -- 2. Bound the middle lazy_query x_v of the resulting sum:
  --    by linearity, splits into Layer A (collision) and Layer B (RO_size).
  --    Result: ≤ collision_indicator σ_2 + (2*RO_size σ_2 + 1)/N.
  -- 3. Bound (cr_loop q).wp of that sum: by linearity, Layer C, B-iterated.
  --    Result: ≤ collision_indicator σ_1 + q*(q-1)/(2N) + (2q+1)/N.
  -- 4. Substitute the σ_1 values (both 0) and arithmetic.

  -- Step 1: pointwise bound on innermost
  have step_inner : ∀ σ_2 σ_5 : state, (lazy_query (claim_x'.get σ_2)).wp
      (fun yσ : output × state => collision_indicator yσ.2) σ_5
      ≤ collision_indicator σ_5 + (RO_size σ_5 : ENNReal) / N := by
    intro σ_2 σ_5
    exact lazy_query_collision_step (claim_x'.get σ_2) σ_5
  -- Step 2: pointwise bound on middle
  have step_middle : ∀ σ_2 : state, (lazy_query (claim_x.get σ_2)).wp
      (fun yσ : output × state =>
        (lazy_query (claim_x'.get σ_2)).wp
          (fun yσ' : output × state => collision_indicator yσ'.2) yσ.2) σ_2
      ≤ collision_indicator σ_2 + (2 * RO_size σ_2 + 1 : ENNReal) / N := by
    intro σ_2
    calc (lazy_query (claim_x.get σ_2)).wp
            (fun yσ : output × state =>
              (lazy_query (claim_x'.get σ_2)).wp
                (fun yσ' : output × state => collision_indicator yσ'.2) yσ.2) σ_2
        ≤ (lazy_query (claim_x.get σ_2)).wp
            (fun yσ : output × state =>
              collision_indicator yσ.2 + (RO_size yσ.2 : ENNReal) / N) σ_2 := by
            apply MeasureTheory.lintegral_mono
            intro yσ
            exact step_inner σ_2 yσ.2
      _ = (lazy_query (claim_x.get σ_2)).wp
            (fun yσ : output × state => collision_indicator yσ.2) σ_2 +
          (lazy_query (claim_x.get σ_2)).wp
            (fun yσ : output × state => (RO_size yσ.2 : ENNReal) / N) σ_2 := by
            rw [Program.wp_add]
      _ ≤ (collision_indicator σ_2 + (RO_size σ_2 : ENNReal) / N) +
          (lazy_query (claim_x.get σ_2)).wp
            (fun yσ : output × state => (RO_size yσ.2 : ENNReal) / N) σ_2 := by
            gcongr
            exact lazy_query_collision_step (claim_x.get σ_2) σ_2
      _ = (collision_indicator σ_2 + (RO_size σ_2 : ENNReal) / N) +
          (1 / N) * (lazy_query (claim_x.get σ_2)).wp
            (fun yσ : output × state => (RO_size yσ.2 : ENNReal)) σ_2 := by
            rw [show (fun yσ : output × state => (RO_size yσ.2 : ENNReal) / N)
                  = (fun yσ : output × state => (1 / N) * (RO_size yσ.2 : ENNReal)) from by
                  funext yσ; rw [ENNReal.div_eq_inv_mul]; rw [one_div]]
            rw [Program.wp_const_mul]
      _ ≤ (collision_indicator σ_2 + (RO_size σ_2 : ENNReal) / N) +
          (1 / N) * (RO_size σ_2 + 1 : ENNReal) := by
            gcongr
            exact lazy_query_RO_size_step (claim_x.get σ_2) σ_2
      _ = collision_indicator σ_2 + (2 * RO_size σ_2 + 1 : ENNReal) / N := by
            rw [show (1 / N : ENNReal) * (RO_size σ_2 + 1 : ENNReal)
                  = (RO_size σ_2 + 1 : ENNReal) / N from by
                rw [one_div, ← ENNReal.div_eq_inv_mul]]
            rw [add_assoc, ENNReal.div_add_div_same]
            congr 2
            push_cast
            ring
  -- Step 3: bound cr_loop q's wp of (collision + (2*RO_size + 1)/N).
  -- Use Layer C, B-iterated, and constant integral.
  have step_outer : (cr_loop cr_adv q lazy_query).wp
      (fun yσ : Unit × state =>
        (lazy_query (claim_x.get yσ.2)).wp
          (fun yσ' : output × state =>
            (lazy_query (claim_x'.get yσ.2)).wp
              (fun yσ'' : output × state => collision_indicator yσ''.2) yσ'.2) yσ.2) σ_1
      ≤ collision_indicator σ_1 + (q * (2 * RO_size σ_1 + q - 1) : ENNReal) / (2 * N) +
        (2 * (RO_size σ_1 + q) + 1 : ENNReal) / N := by
    calc _ ≤ (cr_loop cr_adv q lazy_query).wp
              (fun yσ : Unit × state =>
                collision_indicator yσ.2 + (2 * RO_size yσ.2 + 1 : ENNReal) / N) σ_1 := by
              apply MeasureTheory.lintegral_mono
              intro yσ
              exact step_middle yσ.2
      _ = (cr_loop cr_adv q lazy_query).wp
            (fun yσ : Unit × state => collision_indicator yσ.2) σ_1 +
          (cr_loop cr_adv q lazy_query).wp
            (fun yσ : Unit × state => (2 * RO_size yσ.2 + 1 : ENNReal) / N) σ_1 := by
            rw [Program.wp_add]
      _ ≤ (collision_indicator σ_1 +
            (q * (2 * RO_size σ_1 + q - 1) : ENNReal) / (2 * N)) +
          (cr_loop cr_adv q lazy_query).wp
            (fun yσ : Unit × state => (2 * RO_size yσ.2 + 1 : ENNReal) / N) σ_1 := by
            gcongr
            exact cr_loop_birthday_step cr_adv h_cr_adv q σ_1
      _ ≤ (collision_indicator σ_1 +
            (q * (2 * RO_size σ_1 + q - 1) : ENNReal) / (2 * N)) +
          (2 * (RO_size σ_1 + q) + 1 : ENNReal) / N := by
            gcongr
            -- Bound the wp of (2*RO_size + 1)/N by (2*(RO_size+q) + 1)/N
            calc (cr_loop cr_adv q lazy_query).wp
                    (fun yσ : Unit × state => (2 * RO_size yσ.2 + 1 : ENNReal) / N) σ_1
                = (1 / N) * (cr_loop cr_adv q lazy_query).wp
                    (fun yσ : Unit × state => 2 * RO_size yσ.2 + 1) σ_1 := by
                  rw [show (fun yσ : Unit × state => (2 * RO_size yσ.2 + 1 : ENNReal) / N)
                       = (fun yσ : Unit × state => (1 / N) * (2 * RO_size yσ.2 + 1)) from by
                    funext yσ; rw [ENNReal.div_eq_inv_mul]; rw [one_div]]
                  rw [Program.wp_const_mul]
              _ = (1 / N) * ((cr_loop cr_adv q lazy_query).wp
                    (fun yσ : Unit × state => 2 * (RO_size yσ.2 : ENNReal)) σ_1 +
                  (cr_loop cr_adv q lazy_query).wp
                    (fun _ : Unit × state => 1) σ_1) := by
                  congr 1
                  rw [show (fun yσ : Unit × state => (2 * RO_size yσ.2 + 1 : ENNReal))
                       = (fun yσ : Unit × state => 2 * (RO_size yσ.2 : ENNReal) + 1) from rfl]
                  rw [Program.wp_add]
              _ ≤ (1 / N) * (2 * (RO_size σ_1 + q : ENNReal) + 1) := by
                  apply mul_le_mul_left'
                  apply add_le_add
                  · rw [show (fun yσ : Unit × state => 2 * (RO_size yσ.2 : ENNReal))
                         = (fun yσ : Unit × state => 2 * (RO_size yσ.2 : ENNReal)) from rfl]
                    rw [Program.wp_const_mul]
                    apply mul_le_mul_left'
                    exact cr_loop_RO_size_step cr_adv h_cr_adv q σ_1
                  · exact Program.wp_const_le (cr_loop cr_adv q lazy_query) 1 σ_1
              _ = (2 * (RO_size σ_1 + q) + 1 : ENNReal) / N := by
                  rw [one_div, ← ENNReal.div_eq_inv_mul]
  -- Step 4: substitute σ_1 values and finish arithmetic
  calc _ ≤ collision_indicator σ_1 + (q * (2 * RO_size σ_1 + q - 1) : ENNReal) / (2 * N) +
            (2 * (RO_size σ_1 + q) + 1 : ENNReal) / N := step_outer
    _ = 0 + (q * (q - 1) : ENNReal) / (2 * N) + (2 * q + 1 : ENNReal) / N := by
          rw [h_collision_σ_1, h_RO_size_σ_1]
          push_cast; ring_nf
    _ ≤ ((q + 2) * (q + 1) : ENNReal) / (2 * N) := by
          rw [zero_add]
          -- Convert (2q+1)/N to (2*(2q+1))/(2N).
          rw [show ((2 : ENNReal) * (q : ENNReal) + 1) / N
                = ((2 : ENNReal) * (2 * (q : ENNReal) + 1)) / (2 * N) from by
              rw [ENNReal.mul_div_mul_left _ _ (by norm_num : (2 : ENNReal) ≠ 0)
                    (by norm_num : (2 : ENNReal) ≠ ⊤)]]
          rw [ENNReal.div_add_div_same]
          gcongr
          -- Need: ↑q*(↑q - 1) + 2*(2*↑q + 1) ≤ (↑q + 2)*(↑q + 1)
          cases q with
          | zero => push_cast; simp
          | succ n =>
            rw [ENNReal.natCast_succ_sub_one]
            push_cast
            ring_nf
            rfl

include h_cr_adv in
/-- **Birthday bound** for the lazy CR experiment. Proved by composing
    the bookkeeping lemma with the probability bound. -/
theorem cr_lazy_bound (q : ℕ) (σ₀ : state) :
    ((cr_experiment cr_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0)) σ₀
    ≤ ((q + 2) * (q + 1) : ENNReal) / (2 * Fintype.card output) :=
  le_trans (cr_true_implies_collision_wp cr_adv q σ₀)
    (cr_collision_birthday_bound cr_adv h_cr_adv q σ₀)

include h_cr_adv in
/-- **Transfer of `cr_transfer` from the SubProb marginal level to the
    `wp` level**, for postconditions that depend only on the result bit
    `bσ.1`. This bridges Phase 2 and Phase 3 for `cr_eager_bound`. Thin
    wrapper over the generic `Program.wp_eq_of_marginal_eq`. -/
lemma cr_transfer_wp_of_bit (q : ℕ) (σ₀ : state) (G : Bool → ENNReal) :
    (cr_experiment cr_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => G bσ.1) σ₀
    = (cr_experiment cr_adv q random_oracle_init random_oracle_query).wp
        (fun bσ : Bool × state => G bσ.1) σ₀ :=
  Program.wp_eq_of_marginal_eq (cr_transfer cr_adv h_cr_adv q) G σ₀

include h_cr_adv in
/-- Birthday bound for the eager (true random oracle) game,
    obtained by transferring `cr_lazy_bound` via `cr_transfer`. -/
theorem cr_eager_bound (q : ℕ) (σ₀ : state) :
    ((cr_experiment cr_adv q random_oracle_init random_oracle_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0)) σ₀
    ≤ ((q + 2) * (q + 1) : ENNReal) / (2 * Fintype.card output) := by
  rw [← cr_transfer_wp_of_bit cr_adv h_cr_adv q σ₀
        (fun b => if b then (1 : ENNReal) else 0)]
  exact cr_lazy_bound cr_adv h_cr_adv q σ₀

end CRParam

/-- **Generic lazy-oracle collision bound.** For any adversary `A` that only
    touches the random-oracle state, after `lazy_init` and `q` query rounds
    (each round runs `A`, then answers one `lazy_query`), the probability
    that the oracle map contains a collision is at most `q(q−1)/2N`.

    This is the birthday framework `loop_n_birthday_bound` instantiated at the
    RO collision/size potentials, with `lazy_init` zeroing both. Unlike
    `cr_collision_birthday_bound` (which carries two extra challenge queries,
    giving `(q+2)(q+1)/2N`), this is the clean `q(q−1)/2N` for the bare
    `q`-round loop — the `Pr[bad]` input to the PRP/PRF switching lemma. -/
lemma loop_n_lazy_query_collision_bound (A : Program state Unit)
    (hA : A.inRange random_oracle_state.compl.range) (q : ℕ) (σ₀ : state) :
    (lazy_init >>= fun _ => loop_n q (oracle_step A lazy_query)).wp
        (fun yσ : Unit × state => collision_indicator yσ.2) σ₀
    ≤ ((q : ENNReal) * ((q : ENNReal) - 1)) / (2 * Fintype.card output) := by
  simp only [wp_bind, lazy_init, Program.set, wp_get_state, wp_set_state]
  have h := loop_n_birthday_bound (oracle_step A lazy_query)
    collision_indicator RO_size (Fintype.card output)
    (by exact_mod_cast Fintype.card_pos.ne') (ENNReal.natCast_ne_top _)
    (cr_loop_body_wp_collision A hA) (cr_loop_body_wp_RO_size A hA) q
    (random_oracle_state.set (fun _ : input => none) σ₀)
  refine le_trans h ?_
  rw [lazy_init_collision_indicator, lazy_init_RO_size]
  simp only [Nat.cast_zero, mul_zero, zero_add, le_refl]
