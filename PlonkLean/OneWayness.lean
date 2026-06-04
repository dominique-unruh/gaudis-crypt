import PlonkLean.RO
import PlonkLean.CollisionResistance

/-!
# One-wayness of the random oracle

A 101-crypto example mirroring `CollisionResistance.lean`. The OW game:

1. Sample challenge input `x ← uniform`.
2. Compute `y := oracle(x)` and publish `y` via `ow_challenge_y`.
3. Run the adversary `ow_adv` for `q` rounds with oracle access; the adversary
   writes its candidate preimage to `ow_response`.
4. Check whether `oracle(ow_response) = y`.

The high-level claims:

* `ow_transfer` — the win-bit distribution is identical under lazy and eager RO.
* `ow_lazy_bound` — the lazy win probability is at most `2(q + 1) / |output|`
  (the standard linear bound: `(q+1)/|output|` from a `useful_preimage` union
  bound over the `q` loop queries and 1 final query, plus `(q+1)/|input|` ≤
  `(q+1)/|output|` for the chance the adversary's response happens to equal
  the uniformly random `ow_challenge_x`).
* `ow_eager_bound` — the same bound, via `ow_transfer`.

The bound is **linear** in `q` (not quadratic like CR's birthday bound), because
each `lazy_query` has at most `1 / |output|` chance of producing the fixed
challenge value `y`.
-/

/-- The challenge value `y` published to the adversary (= `oracle(x)` for a
    random `x`). -/
axiom ow_challenge_y : Variable output

/-- The original challenge input `x` (kept in state for the bound analysis). -/
axiom ow_challenge_x : Variable input

/-- The adversary's response: its candidate preimage of the challenge. -/
axiom ow_response : Variable input

/-- Disjointness: game-specific variables don't alias the random oracle. -/
axiom disjoint_ow_challenge_y_ro : disjoint ow_challenge_y random_oracle_state
axiom disjoint_ow_challenge_x_ro : disjoint ow_challenge_x random_oracle_state
axiom disjoint_ow_response_ro : disjoint ow_response random_oracle_state

/-- Game-specific variables are disjoint from the loop's scratch variables.
    Needed so that `ow_loop_body`'s `Program.get oracle_input` /
    `Program.set oracle_output` / `random_oracle_state` operations preserve
    `ow_challenge_y` (and similarly for `ow_response`). -/
axiom disjoint_oracle_input_ow_challenge_y : disjoint oracle_input ow_challenge_y
axiom disjoint_oracle_output_ow_challenge_y : disjoint oracle_output ow_challenge_y
axiom disjoint_ro_ow_challenge_y : disjoint random_oracle_state ow_challenge_y
axiom disjoint_oracle_input_ow_challenge_x : disjoint oracle_input ow_challenge_x
axiom disjoint_oracle_output_ow_challenge_x : disjoint oracle_output ow_challenge_x
axiom disjoint_ro_ow_challenge_x : disjoint random_oracle_state ow_challenge_x
axiom disjoint_ow_challenge_y_ow_challenge_x : disjoint ow_challenge_y ow_challenge_x
axiom disjoint_oracle_input_ow_response : disjoint oracle_input ow_response
axiom disjoint_oracle_output_ow_response : disjoint oracle_output ow_response
axiom disjoint_ro_ow_response : disjoint random_oracle_state ow_response

attribute [instance] disjoint_ow_challenge_y_ro disjoint_ow_challenge_x_ro
                     disjoint_ow_response_ro
                     disjoint_oracle_input_ow_challenge_y
                     disjoint_oracle_output_ow_challenge_y
                     disjoint_ro_ow_challenge_y
                     disjoint_oracle_input_ow_challenge_x
                     disjoint_oracle_output_ow_challenge_x
                     disjoint_ro_ow_challenge_x
                     disjoint_ow_challenge_y_ow_challenge_x
                     disjoint_oracle_input_ow_response
                     disjoint_oracle_output_ow_response
                     disjoint_ro_ow_response

/-- DecidableEq on `output` (needed for the win-bit). Same trick as CR. -/
noncomputable instance : DecidableEq output := Classical.decEq output

/-! ## Game definition (parameterized over the adversary) -/

section OWParam

variable (ow_adv : Program state Unit)

/-- One round of the OW loop body: the adversary computes (and writes
    `oracle_input`), then we run one oracle query. Same shape as
    `cr_loop_body`. -/
noncomputable def ow_loop_body (oracle : input → Program state output) :
    Program state Unit := do
  ow_adv
  Program.set oracle_output (← oracle (← Program.get oracle_input))

/-- Run the adversary-and-query loop for `q` rounds. -/
noncomputable def ow_loop : ℕ → (input → Program state output) → Program state Unit
  | 0,     _      => pure ()
  | n + 1, oracle => do
      ow_loop_body ow_adv oracle
      ow_loop n oracle

/-- **The OW experiment** parameterised by query budget `q`, init, and oracle.

    Sample `x`, set `y := oracle(x)`, publish `y`, run adversary for `q` rounds,
    read the adversary's response, and check whether `oracle(response) = y`. -/
noncomputable def ow_experiment (q : ℕ)
    (init : Program state Unit)
    (oracle : input → Program state output) : Program state Bool := do
  init
  let x ← Program.uniform
  Program.set ow_challenge_x x
  let y ← oracle x
  Program.set ow_challenge_y y
  ow_loop ow_adv q oracle
  let resp ← Program.get ow_response
  let y_check ← oracle resp
  pure (decide (y_check = y))

/-! ## Phase 2 — Transfer (lazy = eager)

Mirrors `cr_transfer` from `CollisionResistance.lean`. -/

variable (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
variable (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
variable (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)

include h_ow_adv in
/-- `ow_adv` transfers to itself: it doesn't touch RO. -/
private lemma transfer_ow_adv : Program.transfer ow_adv ow_adv :=
  Program.transfer_refl_of_inRange_compl h_ow_adv

include h_ow_adv in
/-- One iteration of `ow_loop_body` transfers from lazy to eager. -/
private lemma transfer_ow_loop_body :
    Program.transfer (ow_loop_body ow_adv lazy_query)
                     (ow_loop_body ow_adv random_oracle_query) := by
  show Program.transfer
    (ow_adv >>= fun _ => Program.get oracle_input >>= fun inp =>
      lazy_query inp >>= fun y => Program.set oracle_output y)
    (ow_adv >>= fun _ => Program.get oracle_input >>= fun inp =>
      random_oracle_query inp >>= fun y => Program.set oracle_output y)
  apply Program.transfer_bind (transfer_ow_adv ow_adv h_ow_adv)
  intro _
  apply Program.transfer_bind
    (Program.transfer_of_inRange_disjoint _ oracle_input (Program.inRange_get _))
  intro inp
  apply Program.transfer_bind (Program.transfer_lazy_query inp)
  intro y
  exact Program.transfer_of_inRange_disjoint _ oracle_output (Program.inRange_set _ _)

include h_ow_adv in
/-- `ow_loop q` transfers from lazy to eager, by induction on `q`. -/
private lemma transfer_ow_loop (q : ℕ) :
    Program.transfer (ow_loop ow_adv q lazy_query) (ow_loop ow_adv q random_oracle_query) := by
  induction q with
  | zero => exact Program.transfer_pure ()
  | succ n ih =>
    show Program.transfer
      (ow_loop_body ow_adv lazy_query >>= fun _ => ow_loop ow_adv n lazy_query)
      (ow_loop_body ow_adv random_oracle_query >>=
        fun _ => ow_loop ow_adv n random_oracle_query)
    exact Program.transfer_bind (transfer_ow_loop_body ow_adv h_ow_adv) (fun _ => ih)

include h_ow_adv in
/-- The full `ow_experiment q` transfers from lazy to eager. -/
private lemma transfer_ow_experiment (q : ℕ) :
    Program.transfer
      (ow_experiment ow_adv q lazy_init lazy_query)
      (ow_experiment ow_adv q random_oracle_init random_oracle_query) := by
  show Program.transfer
    (lazy_init >>= fun _ =>
      Program.uniform >>= fun x =>
        Program.set ow_challenge_x x >>= fun _ =>
          lazy_query x >>= fun y =>
            Program.set ow_challenge_y y >>= fun _ =>
              ow_loop ow_adv q lazy_query >>= fun _ =>
                Program.get ow_response >>= fun resp =>
                  lazy_query resp >>= fun y_check =>
                    (pure (decide (y_check = y)) : Program state Bool))
    (random_oracle_init >>= fun _ =>
      Program.uniform >>= fun x =>
        Program.set ow_challenge_x x >>= fun _ =>
          random_oracle_query x >>= fun y =>
            Program.set ow_challenge_y y >>= fun _ =>
              ow_loop ow_adv q random_oracle_query >>= fun _ =>
                Program.get ow_response >>= fun resp =>
                  random_oracle_query resp >>= fun y_check =>
                    (pure (decide (y_check = y)) : Program state Bool))
  apply Program.transfer_bind Program.transfer_lazy_init
  intro _
  apply Program.transfer_bind
    (Program.transfer_refl_of_inRange_compl
      (Program.inRange_mono Program.inRange_uniform bot_le))
  intro x
  apply Program.transfer_bind
    (Program.transfer_of_inRange_disjoint _ ow_challenge_x (Program.inRange_set _ _))
  intro _
  apply Program.transfer_bind (Program.transfer_lazy_query x)
  intro y
  apply Program.transfer_bind
    (Program.transfer_of_inRange_disjoint _ ow_challenge_y (Program.inRange_set _ _))
  intro _
  apply Program.transfer_bind (transfer_ow_loop ow_adv h_ow_adv q)
  intro _
  apply Program.transfer_bind
    (Program.transfer_of_inRange_disjoint _ ow_response (Program.inRange_get _))
  intro resp
  apply Program.transfer_bind (Program.transfer_lazy_query resp)
  intro y_check
  exact Program.transfer_pure _

/-- `convert` is absorbed by the eager `ow_experiment` (it starts with
    `random_oracle_init`). -/
private lemma convert_ow_experiment_eager (q : ℕ) :
    (convert >>= fun _ =>
      ow_experiment ow_adv q random_oracle_init random_oracle_query)
    = ow_experiment ow_adv q random_oracle_init random_oracle_query := by
  set rest : Program state Bool :=
    Program.uniform >>= fun x =>
      Program.set ow_challenge_x x >>= fun _ =>
        random_oracle_query x >>= fun y =>
          Program.set ow_challenge_y y >>= fun _ =>
            ow_loop ow_adv q random_oracle_query >>= fun _ =>
              Program.get ow_response >>= fun resp =>
                random_oracle_query resp >>= fun y_check =>
                  (pure (decide (y_check = y)) : Program state Bool) with hrest
  show (convert >>= fun _ => random_oracle_init >>= fun _ => rest)
      = (random_oracle_init >>= fun _ => rest)
  rw [← Program.bind_assoc, convert_random_oracle_init]

include h_ow_adv in
/-- **Transfer theorem**: the marginal distribution of the win-bit is identical
    under lazy and eager random oracle. -/
theorem ow_transfer (q : ℕ) (σ₀ : state) :
    (ow_experiment ow_adv q lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state => (pure bσ.1 : SubProbability Bool))
    =
    (ow_experiment ow_adv q random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state => (pure bσ.1 : SubProbability Bool)) :=
  Program.transfer_value_marginal (transfer_ow_experiment ow_adv h_ow_adv q)
    (convert_ow_experiment_eager ow_adv q) σ₀

/-! ## Phase 3 — Bookkeeping: win implies preimage in RO

State predicate: at the end of the experiment, if `result = true`, then
`RO[ow_response] = some ow_challenge_y`. This is the OW analog of
`cr_true_implies_collision_wp`. -/

/-- The "is a preimage" state predicate: `RO σ (ow_response σ) = some (ow_challenge_y σ)`. -/
def is_preimage (σ : state) : Prop :=
  random_oracle_state.get σ (ow_response.get σ) = some (ow_challenge_y.get σ)

noncomputable instance : DecidablePred is_preimage :=
  fun _ => Classical.propDecidable _

/-- 0/1-valued indicator that `ow_response` is a preimage of `ow_challenge_y`
    in the random oracle. -/
noncomputable def preimage_indicator (σ : state) : ENNReal :=
  if is_preimage σ then 1 else 0

include h_ow_adv_chal_y in
/-- `ow_loop_body` preserves `ow_challenge_y`. -/
private lemma ow_loop_body_inRange_chal_y_compl :
    (ow_loop_body ow_adv lazy_query).inRange ow_challenge_y.compl.range := by
  show (ow_adv >>= fun _ =>
        Program.get oracle_input >>= fun inp =>
          lazy_query inp >>= fun y =>
            Program.set oracle_output y).inRange ow_challenge_y.compl.range
  refine Program.inRange_bind h_ow_adv_chal_y ?_
  intro _
  refine Program.inRange_bind
    (Program.inRange_mono (Program.inRange_get _)
      (Lens.range_le_compl_of_disjoint oracle_input ow_challenge_y)) ?_
  intro inp
  refine Program.inRange_bind ?_ ?_
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_y)
  · intro y
    exact Program.inRange_mono (Program.inRange_set _ _)
      (Lens.range_le_compl_of_disjoint oracle_output ow_challenge_y)

include h_ow_adv_chal_y in
/-- `ow_loop q` preserves `ow_challenge_y`. -/
private lemma ow_loop_inRange_chal_y_compl (q : ℕ) :
    (ow_loop ow_adv q lazy_query).inRange ow_challenge_y.compl.range := by
  induction q with
  | zero => exact Program.inRange_pure _ _
  | succ n ih =>
    show (ow_loop_body ow_adv lazy_query >>= fun _ =>
          ow_loop ow_adv n lazy_query).inRange _
    exact Program.inRange_bind
      (ow_loop_body_inRange_chal_y_compl ow_adv h_ow_adv_chal_y) (fun _ => ih)

include h_ow_adv_chal_y in
/-- **Bookkeeping**: if the experiment's result bit is `true`, then the final
    random oracle has `ow_response` as a preimage of `ow_challenge_y`. -/
lemma ow_true_implies_preimage_wp (q : ℕ) (σ₀ : state) :
    (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ₀
    ≤ (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => preimage_indicator bσ.2) σ₀ := by
  simp only [ow_experiment, wp_bind, wp_set, wp_get, wp_pure, lazy_init]
  -- After simp, lazy_init's `set RO` is inlined. First stochastic wp is uniform.
  -- Layers (stochastic): uniform, lazy_query x, ow_loop, lazy_query resp.
  apply Program.wp_le_wp_of_le; rintro ⟨x, σ_u⟩; dsimp only
  apply Program.wp_le_wp_of_le; rintro ⟨y, σ_l⟩; dsimp only
  -- Now ow_loop is at outermost wp. Its input state is `ow_challenge_y.set y σ_l`
  -- (since `Program.set ow_challenge_y y` was inlined via wp_set).
  rw [Program.wp_strengthen_lens_preserved ow_challenge_y
      (ow_loop_inRange_chal_y_compl ow_adv h_ow_adv_chal_y q)]
  apply Program.wp_le_wp_of_le; rintro ⟨_, σ_o⟩; dsimp only
  -- LHS has an outer-if wrap from `wp_strengthen_lens_preserved`; RHS does not.
  -- Split on that outer condition so both sides become bare `lazy_query.wp`s.
  split_ifs with h_chal_y_o
  · -- Strengthen the final `lazy_query (ow_response.get σ_o)`.
    rw [lazy_query_wp_writes_output (ow_response.get σ_o)]
    rw [lazy_query_wp_preserves_disjoint ow_response (ow_response.get σ_o)]
    rw [lazy_query_wp_preserves_disjoint ow_challenge_y (ow_response.get σ_o)]
    apply Program.wp_le_wp_of_le; rintro ⟨y_check, σ_f⟩; dsimp only
    -- Compare nested-if expressions pointwise.
    split_ifs with h_chal_y_f h_resp_f h_RO_f h_decide
    · -- All conditions hold.
      have h_chal_y_eq_y : ow_challenge_y.get σ_f = y := by
        rw [h_chal_y_f, h_chal_y_o, ow_challenge_y.set_get]
      have h_y_check_eq_y : y_check = y := of_decide_eq_true h_decide
      have h_is_preimage : is_preimage σ_f := by
        change random_oracle_state.get σ_f (ow_response.get σ_f) =
               some (ow_challenge_y.get σ_f)
        rw [h_resp_f, h_RO_f, h_chal_y_eq_y, h_y_check_eq_y]
      simp [preimage_indicator, h_is_preimage]
    all_goals exact zero_le _
  · exact zero_le _

/-! ## Phase 4 — Probability bound on preimage_indicator

The bookkeeping lemma reduces `P[win]` to `P[preimage_indicator at end]`,
which we now bound by `2(q + 1) / |output|` (the standard linear OW bound).
Decomposed into layers analogous to CR's Layer A–D, but with a *linear*
bound instead of quadratic (since each `lazy_query` has at most `1/|output|`
chance of producing the fixed challenge value, rather than `RO_size/|output|`).

**Layer A_OW** (per-query bound): each `lazy_query` bumps the expected
"useful preimage" indicator by at most `1/|output|`. The "useful preimage"
is a preimage of `ow_challenge_y` other than `ow_challenge_x` — i.e., a
preimage the adversary actually "found" rather than the trivially-cached
challenge entry.

**Layer C_OW** (loop accumulation): by induction on `q`, `ow_loop q` bumps
the useful_preimage indicator by ≤ `q / |output|`.

**Layer D_OW** (full composition): decompose `preimage ≤ useful_preimage +
[resp = ow_challenge_x ∧ preimage]`, where:
* `E[useful_preimage]` ≤ `(q+1)/|output|`: the loop contributes `q/|output|`
  (Layer C_OW); the final `lazy_query resp` contributes `1/|output|` (Layer
  A_OW); the initial `lazy_query x_orig` contributes 0 because `x_orig =
  ow_challenge_x` (tight self-step).
* `E[[resp = ow_challenge_x ∧ preimage]]` ≤ `(q+1)/|input|`: the standard
  "guessing the secret" bound — `ow_challenge_x` is uniform over `input`,
  and the adversary can identify it only by `lazy_query`ing it among `q+1`
  total queries.

Total: `2(q+1)/|output|`, using `|input| ≥ |output|`. -/

/-- Standard hash-function assumption: the input space is at least as large
    as the output space. -/
axiom card_input_ge_output : Fintype.card output ≤ Fintype.card input

/-! ### Definitions: `useful_preimage`

A *useful* preimage is a preimage of `ow_challenge_y` other than the trivially
cached `ow_challenge_x`. We track this separately because:

* `lazy_query x'` bumps `useful_preimage` by exactly `[x' ≠ ow_challenge_x ∧
  fresh-sample = ow_challenge_y]` (at most `1/|output|` in expectation).
* `useful_preimage` depends only on `random_oracle_state`, `ow_challenge_x`,
  `ow_challenge_y` — variables disjoint from the adversary's range — so the
  adversary cannot affect it directly. -/

private def useful_preimage (σ : state) : Prop :=
  ∃ x' : input, x' ≠ ow_challenge_x.get σ ∧
    random_oracle_state.get σ x' = some (ow_challenge_y.get σ)

private noncomputable instance (σ : state) : Decidable (useful_preimage σ) :=
  Classical.propDecidable _

private noncomputable def useful_preimage_indicator (σ : state) : ENNReal :=
  if useful_preimage σ then 1 else 0

/-- Structural decomposition: `preimage` implies either the response is the
    trivially cached challenge input, or there's a useful preimage. -/
private lemma preimage_le_useful_or_resp_eq_chal_x (σ : state) :
    preimage_indicator σ ≤ useful_preimage_indicator σ +
      (if ow_response.get σ = ow_challenge_x.get σ ∧ is_preimage σ
       then (1 : ENNReal) else 0) := by
  unfold preimage_indicator
  by_cases h_pre : is_preimage σ
  · rw [if_pos h_pre]
    by_cases h_eq : ow_response.get σ = ow_challenge_x.get σ
    · rw [if_pos ⟨h_eq, h_pre⟩]; exact le_add_self
    · have h_useful : useful_preimage σ := ⟨ow_response.get σ, h_eq, h_pre⟩
      unfold useful_preimage_indicator
      rw [if_pos h_useful]
      exact le_self_add
  · rw [if_neg h_pre]; exact zero_le _

/-! ### Layer A_OW: per-query bump for `useful_preimage_indicator` -/

/-- Pointwise bound: after a fresh sample `y` at `x`, the new useful_preimage
    indicator is at most the old one plus `[y = ow_challenge_y σ ∧ x ≠ ow_challenge_x σ]`. -/
private lemma pointwise_useful_preimage_bound (x : input) (σ : state)
    (h_fresh : random_oracle_state.get σ x = none) (y : output) :
    useful_preimage_indicator (random_oracle_state.set
      (fun x' => if x' = x then some y else random_oracle_state.get σ x') σ)
    ≤ useful_preimage_indicator σ +
      (if y = ow_challenge_y.get σ ∧ x ≠ ow_challenge_x.get σ
       then (1 : ENNReal) else 0) := by
  set σ_y := random_oracle_state.set
    (fun x' => if x' = x then some y else random_oracle_state.get σ x') σ with hσ_y_def
  have h_chal_x : ow_challenge_x.get σ_y = ow_challenge_x.get σ := by
    rw [hσ_y_def]; exact ow_challenge_x.get_of_disjoint_set random_oracle_state _ σ
  have h_chal_y : ow_challenge_y.get σ_y = ow_challenge_y.get σ := by
    rw [hσ_y_def]; exact ow_challenge_y.get_of_disjoint_set random_oracle_state _ σ
  unfold useful_preimage_indicator
  by_cases h_up_y : useful_preimage σ_y
  · rw [if_pos h_up_y]
    obtain ⟨x'', h_neq, h_RO⟩ := h_up_y
    rw [h_chal_x] at h_neq
    rw [h_chal_y] at h_RO
    rw [hσ_y_def, random_oracle_state.set_get] at h_RO
    by_cases h_x''_x : x'' = x
    · rw [if_pos h_x''_x] at h_RO
      have h_y_eq : y = ow_challenge_y.get σ := Option.some.inj h_RO
      have h_x_neq : x ≠ ow_challenge_x.get σ := by
        rw [← h_x''_x]; exact h_neq
      have h_yx : y = ow_challenge_y.get σ ∧ x ≠ ow_challenge_x.get σ := ⟨h_y_eq, h_x_neq⟩
      rw [if_pos h_yx]
      exact le_add_self
    · rw [if_neg h_x''_x] at h_RO
      have h_useful_σ : useful_preimage σ := ⟨x'', h_neq, h_RO⟩
      rw [if_pos h_useful_σ]
      exact le_self_add
  · rw [if_neg h_up_y]; exact zero_le _

/-- **Layer A_OW**: each `lazy_query` bumps the expected `useful_preimage_indicator`
    by at most `1/|output|`. The fresh-sample case puts probability `1/|output|`
    on the single "bad" value `ow_challenge_y σ`; if `x = ow_challenge_x σ` the
    bump is zero. -/
private lemma lazy_query_useful_preimage_step (x : input) (σ : state) :
    (lazy_query x).wp
        (fun yσ : output × state => useful_preimage_indicator yσ.2) σ
    ≤ useful_preimage_indicator σ + (1 : ENNReal) / Fintype.card output := by
  simp only [lazy_query, wp_bind, wp_get]
  cases h_cache : random_oracle_state.get σ x with
  | some y_cache =>
    simp only [wp_pure]
    exact le_self_add
  | none =>
    simp only [wp_bind, wp_uniform, wp_set, wp_pure]
    set N : ENNReal := (Fintype.card output : ENNReal) with hN_def
    have hN_pos : N ≠ 0 := by rw [hN_def]; exact_mod_cast Fintype.card_pos.ne'
    have hN_top : N ≠ ⊤ := by rw [hN_def]; exact ENNReal.natCast_ne_top _
    calc ∑ y : output, useful_preimage_indicator (random_oracle_state.set
            (fun x' => if x' = x then some y else random_oracle_state.get σ x') σ) / N
        = (∑ y : output, useful_preimage_indicator (random_oracle_state.set
            (fun x' => if x' = x then some y else random_oracle_state.get σ x') σ)) / N := by
          simp_rw [ENNReal.div_eq_inv_mul]
          rw [← Finset.mul_sum]
      _ ≤ (∑ y : output, (useful_preimage_indicator σ +
            (if y = ow_challenge_y.get σ ∧ x ≠ ow_challenge_x.get σ
             then (1 : ENNReal) else 0))) / N := by
          gcongr with y _
          exact pointwise_useful_preimage_bound x σ h_cache y
      _ = (N * useful_preimage_indicator σ +
            (if x ≠ ow_challenge_x.get σ then (1 : ENNReal) else 0)) / N := by
          have h_sum_eq : (∑ y : output, (useful_preimage_indicator σ +
                (if y = ow_challenge_y.get σ ∧ x ≠ ow_challenge_x.get σ
                 then (1 : ENNReal) else 0)))
              = N * useful_preimage_indicator σ +
                  (if x ≠ ow_challenge_x.get σ then (1 : ENNReal) else 0) := by
            rw [Finset.sum_add_distrib]
            congr 1
            · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN_def]
            · by_cases h_x_neq : x ≠ ow_challenge_x.get σ
              · rw [if_pos h_x_neq]
                have h_simp : ∀ y : output,
                    (if y = ow_challenge_y.get σ ∧ x ≠ ow_challenge_x.get σ
                     then (1 : ENNReal) else 0)
                    = (if y = ow_challenge_y.get σ then (1 : ENNReal) else 0) := by
                  intro y
                  by_cases h_y : y = ow_challenge_y.get σ
                  · rw [if_pos ⟨h_y, h_x_neq⟩, if_pos h_y]
                  · rw [if_neg (fun h => h_y h.1), if_neg h_y]
                simp_rw [h_simp]
                rw [Finset.sum_ite_eq' Finset.univ (ow_challenge_y.get σ) (fun _ => (1 : ENNReal))]
                rw [if_pos (Finset.mem_univ _)]
              · rw [if_neg h_x_neq]
                push_neg at h_x_neq
                apply Finset.sum_eq_zero
                intro y _
                rw [if_neg]
                intro ⟨_, h_contra⟩
                exact h_contra h_x_neq
          rw [h_sum_eq]
      _ ≤ (N * useful_preimage_indicator σ + 1) / N := by
          gcongr
          split_ifs <;> simp
      _ = useful_preimage_indicator σ + 1 / N := by
          rw [ENNReal.add_div]
          rw [mul_comm N (useful_preimage_indicator σ), mul_div_assoc,
              ENNReal.div_self hN_pos hN_top, mul_one]

/-! ### Layer C_OW: loop accumulation -/

/-- `useful_preimage_indicator` only depends on `random_oracle_state`,
    `ow_challenge_x`, `ow_challenge_y`. If all three lens values are preserved,
    the indicator is preserved. -/
private lemma useful_preimage_indicator_of_three_get_eq {σ σ' : state}
    (h_RO : random_oracle_state.get σ' = random_oracle_state.get σ)
    (h_x : ow_challenge_x.get σ' = ow_challenge_x.get σ)
    (h_y : ow_challenge_y.get σ' = ow_challenge_y.get σ) :
    useful_preimage_indicator σ' = useful_preimage_indicator σ := by
  have h_useful : useful_preimage σ' ↔ useful_preimage σ := by
    unfold useful_preimage
    constructor
    · rintro ⟨x', hne, hRO⟩
      refine ⟨x', ?_, ?_⟩
      · rw [← h_x]; exact hne
      · rw [← h_y, ← h_RO]; exact hRO
    · rintro ⟨x', hne, hRO⟩
      refine ⟨x', ?_, ?_⟩
      · rw [h_x]; exact hne
      · rw [h_y, h_RO]; exact hRO
  unfold useful_preimage_indicator
  by_cases h : useful_preimage σ
  · rw [if_pos (h_useful.mpr h), if_pos h]
  · rw [if_neg (h_useful.not.mpr h), if_neg h]

/-- Setting a variable disjoint from `random_oracle_state`, `ow_challenge_x`,
    and `ow_challenge_y` doesn't change `useful_preimage_indicator`. -/
private lemma useful_preimage_indicator_set_disjoint {α : Type} (v : Variable α)
    [disjoint v random_oracle_state] [disjoint v ow_challenge_x]
    [disjoint v ow_challenge_y] (a : α) (σ : state) :
    useful_preimage_indicator (v.set a σ) = useful_preimage_indicator σ :=
  useful_preimage_indicator_of_three_get_eq
    (random_oracle_state.get_of_disjoint_set v a σ)
    (ow_challenge_x.get_of_disjoint_set v a σ)
    (ow_challenge_y.get_of_disjoint_set v a σ)

include h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x in
/-- `ow_adv` preserves the `useful_preimage_indicator` (in expectation): it
    modifies only the complement of each of `random_oracle_state`,
    `ow_challenge_x`, `ow_challenge_y`. -/
private lemma ow_adv_wp_useful_preimage (σ : state) :
    ow_adv.wp (fun yσ : Unit × state => useful_preimage_indicator yσ.2) σ
    ≤ useful_preimage_indicator σ := by
  rw [Program.wp_strengthen_lens_preserved ow_challenge_y h_ow_adv_chal_y]
  rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_ow_adv_chal_x]
  rw [Program.wp_strengthen_lens_preserved random_oracle_state h_ow_adv]
  calc ow_adv.wp _ σ
      ≤ ow_adv.wp (fun _ : Unit × state => useful_preimage_indicator σ) σ := by
        apply Program.wp_le_wp_of_le
        rintro ⟨_, σ'⟩; dsimp only
        split_ifs with h_RO h_x h_y
        · exact le_of_eq (useful_preimage_indicator_of_three_get_eq h_RO h_x h_y)
        all_goals exact zero_le _
    _ ≤ useful_preimage_indicator σ := Program.wp_const_le ow_adv _ σ

include h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x in
/-- One iteration of `ow_loop_body` bumps the useful_preimage indicator by at
    most `1/|output|` (in expectation). -/
private lemma ow_loop_body_useful_preimage_step (σ : state) :
    (ow_loop_body ow_adv lazy_query).wp
        (fun yσ : Unit × state => useful_preimage_indicator yσ.2) σ
    ≤ useful_preimage_indicator σ + (1 : ENNReal) / Fintype.card output := by
  unfold ow_loop_body
  rw [wp_bind]
  have h_inner : ∀ σ_a : state,
      (Program.get oracle_input >>= fun inp =>
        lazy_query inp >>= fun y => Program.set oracle_output y).wp
          (fun yσ : Unit × state => useful_preimage_indicator yσ.2) σ_a
      ≤ useful_preimage_indicator σ_a + (1 : ENNReal) / Fintype.card output := by
    intro σ_a
    simp only [wp_bind, wp_get]
    rw [show (fun yσ : output × state =>
              (Program.set oracle_output yσ.1).wp
                (fun yσ' : Unit × state => useful_preimage_indicator yσ'.2) yσ.2)
            = (fun yσ : output × state => useful_preimage_indicator yσ.2) from by
      funext yσ
      rw [wp_set]
      exact useful_preimage_indicator_set_disjoint oracle_output yσ.1 yσ.2]
    exact lazy_query_useful_preimage_step (oracle_input.get σ_a) σ_a
  calc ow_adv.wp _ σ
      ≤ ow_adv.wp (fun yσ : Unit × state =>
            useful_preimage_indicator yσ.2 + (1 : ENNReal) / Fintype.card output) σ := by
        apply Program.wp_le_wp_of_le
        intro yσ
        exact h_inner yσ.2
    _ = ow_adv.wp (fun yσ : Unit × state => useful_preimage_indicator yσ.2) σ
        + ow_adv.wp (fun _ : Unit × state =>
            (1 : ENNReal) / Fintype.card output) σ := by
      rw [Program.wp_add]
    _ ≤ useful_preimage_indicator σ + (1 : ENNReal) / Fintype.card output := by
      gcongr
      · exact ow_adv_wp_useful_preimage ow_adv h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x σ
      · exact Program.wp_const_le ow_adv _ σ

include h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x in
/-- **Layer C_OW**: the cumulative useful_preimage bound after `ow_loop k`.
    Linear sum of Layer A_OW across the loop body. -/
private lemma ow_loop_useful_preimage_step (k : ℕ) (σ : state) :
    (ow_loop ow_adv k lazy_query).wp
        (fun yσ : Unit × state => useful_preimage_indicator yσ.2) σ
    ≤ useful_preimage_indicator σ + (k : ENNReal) / Fintype.card output := by
  induction k generalizing σ with
  | zero =>
    show (pure () : Program state Unit).wp _ σ ≤ _
    rw [wp_pure]; simp
  | succ k ih =>
    show (ow_loop_body ow_adv lazy_query >>= fun _ =>
          ow_loop ow_adv k lazy_query).wp _ σ ≤ _
    rw [wp_bind]
    set N : ENNReal := (Fintype.card output : ENNReal) with hN_def
    calc (ow_loop_body ow_adv lazy_query).wp (fun yσ : Unit × state =>
            (ow_loop ow_adv k lazy_query).wp
              (fun yσ' : Unit × state => useful_preimage_indicator yσ'.2) yσ.2) σ
        ≤ (ow_loop_body ow_adv lazy_query).wp (fun yσ : Unit × state =>
            useful_preimage_indicator yσ.2 + (k : ENNReal) / N) σ := by
          apply Program.wp_le_wp_of_le
          intro yσ
          exact ih yσ.2
      _ = (ow_loop_body ow_adv lazy_query).wp
            (fun yσ : Unit × state => useful_preimage_indicator yσ.2) σ +
          (ow_loop_body ow_adv lazy_query).wp
            (fun _ : Unit × state => (k : ENNReal) / N) σ := by
          rw [Program.wp_add]
      _ ≤ (useful_preimage_indicator σ + 1 / N) + (k : ENNReal) / N := by
          gcongr
          · exact ow_loop_body_useful_preimage_step ow_adv h_ow_adv
              h_ow_adv_chal_y h_ow_adv_chal_x σ
          · exact Program.wp_const_le _ _ _
      _ = useful_preimage_indicator σ + ((k + 1 : ℕ) : ENNReal) / N := by
          rw [add_assoc]
          congr 1
          push_cast
          rw [ENNReal.add_div, one_div, ENNReal.div_eq_inv_mul, add_comm]

/-! ### Layer D_OW: full bound -/

/-- Tight Layer A_OW for the special case `x = ow_challenge_x σ`: querying
    the challenge input itself cannot create a useful preimage (the only fresh
    entry has `x' = chal_x`, which fails the `x' ≠ chal_x` requirement). -/
private lemma lazy_query_useful_preimage_step_self (σ : state) :
    (lazy_query (ow_challenge_x.get σ)).wp
        (fun yσ : output × state => useful_preimage_indicator yσ.2) σ
    ≤ useful_preimage_indicator σ := by
  simp only [lazy_query, wp_bind, wp_get]
  cases h_cache : random_oracle_state.get σ (ow_challenge_x.get σ) with
  | some y_cache => simp only [wp_pure]; exact le_refl _
  | none =>
    simp only [wp_bind, wp_uniform, wp_set, wp_pure]
    set N : ENNReal := (Fintype.card output : ENNReal) with hN_def
    have hN_pos : N ≠ 0 := by rw [hN_def]; exact_mod_cast Fintype.card_pos.ne'
    have hN_top : N ≠ ⊤ := by rw [hN_def]; exact ENNReal.natCast_ne_top _
    -- Each summand is bounded by useful_preimage_indicator σ (zero bump,
    -- since the new RO entry has x'' = ow_challenge_x σ which fails ≠ chal_x).
    have h_each : ∀ y : output,
        useful_preimage_indicator (random_oracle_state.set
          (fun x' => if x' = ow_challenge_x.get σ then some y
                     else random_oracle_state.get σ x') σ)
        ≤ useful_preimage_indicator σ := by
      intro y
      have h_bound := pointwise_useful_preimage_bound
        (ow_challenge_x.get σ) σ h_cache y
      have h_zero : (if y = ow_challenge_y.get σ ∧
            ow_challenge_x.get σ ≠ ow_challenge_x.get σ
          then (1 : ENNReal) else 0) = 0 := by
        rw [if_neg]; rintro ⟨_, hne⟩; exact hne rfl
      rw [h_zero, add_zero] at h_bound
      exact h_bound
    calc ∑ y : output, useful_preimage_indicator (random_oracle_state.set
            (fun x' => if x' = ow_challenge_x.get σ then some y
                       else random_oracle_state.get σ x') σ) / N
        = (∑ y : output, useful_preimage_indicator (random_oracle_state.set
            (fun x' => if x' = ow_challenge_x.get σ then some y
                       else random_oracle_state.get σ x') σ)) / N := by
          simp_rw [ENNReal.div_eq_inv_mul]; rw [← Finset.mul_sum]
      _ ≤ (∑ _y : output, useful_preimage_indicator σ) / N := by
          gcongr with y _; exact h_each y
      _ = (N * useful_preimage_indicator σ) / N := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN_def]
      _ = useful_preimage_indicator σ := by
          rw [mul_comm, mul_div_assoc, ENNReal.div_self hN_pos hN_top, mul_one]

/-- At any state with `RO = fun _ => none` and `ow_challenge_y = y_chal`,
    after `random_oracle_state.set (extend x_orig → y_chal)`, the
    `useful_preimage_indicator` is `0`: the only `RO` entry is `x_orig`, which
    fails the `x' ≠ ow_challenge_x` requirement (since `ow_challenge_x = x_orig`). -/
private lemma useful_preimage_indicator_post_init_eq_zero
    (x_orig : input) (y_chal : output) (σ : state)
    (h_chal_x : ow_challenge_x.get σ = x_orig)
    (h_chal_y : ow_challenge_y.get σ = y_chal)
    (h_RO_x : random_oracle_state.get σ x_orig = none)
    (h_RO_other : ∀ x' ≠ x_orig, random_oracle_state.get σ x' = none) :
    useful_preimage_indicator (random_oracle_state.set
      (fun x' => if x' = x_orig then some y_chal else random_oracle_state.get σ x') σ)
    = 0 := by
  set σ' := random_oracle_state.set
    (fun x' => if x' = x_orig then some y_chal else random_oracle_state.get σ x') σ
  unfold useful_preimage_indicator
  rw [if_neg]
  rintro ⟨x', hne, hRO⟩
  have h_chal_x' : ow_challenge_x.get σ' = x_orig := by
    rw [show σ' = random_oracle_state.set _ σ from rfl]
    rw [ow_challenge_x.get_of_disjoint_set, h_chal_x]
  rw [h_chal_x'] at hne
  have h_RO' : random_oracle_state.get σ' x' = none := by
    rw [show σ' = random_oracle_state.set _ σ from rfl,
        random_oracle_state.set_get, if_neg hne]
    exact h_RO_other x' hne
  rw [h_RO'] at hRO
  simp at hRO

include h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x in
/-- Inner bound: starting from a state where `RO` is empty and `ow_challenge_x = x_orig`,
    the lazy_query (x_orig) + set ow_challenge_y + ow_loop + lazy_query (resp) chain
    accumulates useful_preimage to at most `(q+1)/|output|`. -/
private lemma ow_experiment_useful_preimage_inner (q : ℕ) (x_orig : input) (σ : state)
    (h_chal_x : ow_challenge_x.get σ = x_orig)
    (h_RO : ∀ x', random_oracle_state.get σ x' = none) :
    (lazy_query x_orig).wp (fun yσ : output × state =>
      (ow_loop ow_adv q lazy_query).wp (fun yσ' : Unit × state =>
        (lazy_query (ow_response.get yσ'.2)).wp (fun yσ'' : output × state =>
          useful_preimage_indicator yσ''.2) yσ'.2)
        (ow_challenge_y.set yσ.1 yσ.2)) σ
    ≤ ((q + 1) : ENNReal) / Fintype.card output := by
  set N : ENNReal := (Fintype.card output : ENNReal) with hN_def
  -- Step 1: bound the inner (post-set-chal_y) by useful + (q+1)/N using C_OW + A_OW.
  have h_inner : ∀ σ_4 : state, useful_preimage_indicator σ_4 = 0 →
      (ow_loop ow_adv q lazy_query).wp (fun yσ' : Unit × state =>
        (lazy_query (ow_response.get yσ'.2)).wp (fun yσ'' : output × state =>
          useful_preimage_indicator yσ''.2) yσ'.2) σ_4
      ≤ ((q + 1) : ENNReal) / N := by
    intro σ_4 h_zero
    calc (ow_loop ow_adv q lazy_query).wp (fun yσ' : Unit × state =>
            (lazy_query (ow_response.get yσ'.2)).wp (fun yσ'' : output × state =>
              useful_preimage_indicator yσ''.2) yσ'.2) σ_4
        ≤ (ow_loop ow_adv q lazy_query).wp (fun yσ' : Unit × state =>
            useful_preimage_indicator yσ'.2 + 1 / N) σ_4 := by
          apply Program.wp_le_wp_of_le
          intro yσ'
          exact lazy_query_useful_preimage_step _ yσ'.2
      _ = (ow_loop ow_adv q lazy_query).wp (fun yσ' : Unit × state =>
            useful_preimage_indicator yσ'.2) σ_4 +
          (ow_loop ow_adv q lazy_query).wp (fun _ : Unit × state => 1 / N) σ_4 := by
          rw [Program.wp_add]
      _ ≤ (useful_preimage_indicator σ_4 + (q : ENNReal) / N) + 1 / N := by
          gcongr
          · exact ow_loop_useful_preimage_step ow_adv h_ow_adv
              h_ow_adv_chal_y h_ow_adv_chal_x q σ_4
          · exact Program.wp_const_le _ _ _
      _ = ((q + 1) : ENNReal) / N := by
          rw [h_zero, zero_add, ← ENNReal.add_div]
  -- Step 2: peel the lazy_query x_orig. Since RO σ x_orig = none, only the
  -- fresh branch fires. Unfold the outer lazy_query only; keep the inner folded.
  show (do let cache ← Program.get random_oracle_state
           match cache x_orig with
           | some y => pure y
           | none => do
               let value ← Program.uniform
               Program.set random_oracle_state
                 (fun x' => if x' = x_orig then some value else cache x')
               pure value).wp _ σ ≤ _
  simp only [wp_bind, wp_get]
  have h_cache : random_oracle_state.get σ x_orig = none := h_RO x_orig
  rw [h_cache]
  simp only [wp_bind, wp_uniform, wp_set, wp_pure]
  -- Goal: ∑ y, INNER(y) / N ≤ (q+1)/N.
  have h_each : ∀ y : output, useful_preimage_indicator
      (ow_challenge_y.set y (random_oracle_state.set
        (fun x' => if x' = x_orig then some y else random_oracle_state.get σ x') σ)) = 0 := by
    intro y
    set σ_4 := ow_challenge_y.set y (random_oracle_state.set
      (fun x' => if x' = x_orig then some y else random_oracle_state.get σ x') σ)
    have h_chal_y_4 : ow_challenge_y.get σ_4 = y := ow_challenge_y.set_get _ _
    have h_chal_x_4 : ow_challenge_x.get σ_4 = x_orig := by
      show ow_challenge_x.get (ow_challenge_y.set y _) = x_orig
      rw [ow_challenge_x.get_of_disjoint_set ow_challenge_y,
          ow_challenge_x.get_of_disjoint_set random_oracle_state, h_chal_x]
    have h_RO_4 : ∀ x' ≠ x_orig, random_oracle_state.get σ_4 x' = none := by
      intro x' hne
      show random_oracle_state.get (ow_challenge_y.set _ _) x' = none
      rw [show random_oracle_state.get (ow_challenge_y.set y _) =
            random_oracle_state.get (random_oracle_state.set _ σ) from
          random_oracle_state.get_of_disjoint_set ow_challenge_y y _]
      rw [random_oracle_state.set_get, if_neg hne]
      exact h_RO x'
    unfold useful_preimage_indicator
    rw [if_neg]
    rintro ⟨x', hne, hRO⟩
    rw [h_chal_x_4] at hne
    rw [h_RO_4 x' hne] at hRO
    simp at hRO
  have hN_pos : N ≠ 0 := by rw [hN_def]; exact_mod_cast Fintype.card_pos.ne'
  have hN_top : N ≠ ⊤ := by rw [hN_def]; exact ENNReal.natCast_ne_top _
  have h_sum_le : ∀ (g : output → state),
      (∀ y, useful_preimage_indicator (g y) = 0) →
      (∑ y : output,
        (ow_loop ow_adv q lazy_query).wp (fun yσ' : Unit × state =>
          (lazy_query (ow_response.get yσ'.2)).wp (fun yσ'' : output × state =>
            useful_preimage_indicator yσ''.2) yσ'.2) (g y) / N)
      ≤ ((q + 1) : ENNReal) / N := by
    intro g hg
    calc (∑ y : output, _ / N)
        ≤ (∑ _y : output, ((q + 1) : ENNReal) / N / N) := by
          gcongr with y _
          exact h_inner (g y) (hg y)
      _ = ((q + 1) : ENNReal) / N := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN_def]
          rw [show N * (((q + 1) : ENNReal) / N / N)
                = (N * ((q + 1) / N)) / N from by rw [mul_div_assoc]]
          rw [ENNReal.mul_div_cancel hN_pos hN_top]
  exact h_sum_le _ h_each

include h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x in
/-- The expected `useful_preimage_indicator` at the end of the experiment is
    at most `(q+1)/|output|`: the initial `lazy_query` on `ow_challenge_x` adds
    nothing (handled by `lazy_query_useful_preimage_step_self`), the loop adds
    at most `q/|output|` (Layer C_OW), and the final `lazy_query` on the
    adversary's response adds at most `1/|output|` (Layer A_OW). -/
private lemma ow_experiment_useful_preimage_bound (q : ℕ) (σ₀ : state) :
    (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => useful_preimage_indicator bσ.2) σ₀
    ≤ ((q + 1) : ENNReal) / Fintype.card output := by
  simp only [ow_experiment, wp_bind, wp_set, wp_get, wp_pure, lazy_init, wp_uniform]
  -- After simp, goal is `∑ x_orig, INNER(x_orig) / |input| ≤ (q+1)/|output|`
  -- where INNER(x_orig) = (lazy_query x_orig).wp ... at state
  -- `ow_challenge_x.set x_orig (random_oracle_state.set (fun _ => none) σ₀)`.
  set σ_init : state := random_oracle_state.set (fun _ => none) σ₀ with hσ_init
  set Ninp : ENNReal := (Fintype.card input : ENNReal) with hNinp_def
  set N : ENNReal := (Fintype.card output : ENNReal) with hN_def
  have hNinp_pos : Ninp ≠ 0 := by rw [hNinp_def]; exact_mod_cast Fintype.card_pos.ne'
  have hNinp_top : Ninp ≠ ⊤ := by rw [hNinp_def]; exact ENNReal.natCast_ne_top _
  have h_each : ∀ x_orig : input,
      (lazy_query x_orig).wp (fun yσ : output × state =>
        (ow_loop ow_adv q lazy_query).wp (fun yσ' : Unit × state =>
          (lazy_query (ow_response.get yσ'.2)).wp (fun yσ'' : output × state =>
            useful_preimage_indicator yσ''.2) yσ'.2)
          (ow_challenge_y.set yσ.1 yσ.2)) (ow_challenge_x.set x_orig σ_init)
      ≤ ((q + 1) : ENNReal) / N := by
    intro x_orig
    apply ow_experiment_useful_preimage_inner ow_adv h_ow_adv
      h_ow_adv_chal_y h_ow_adv_chal_x q x_orig (ow_challenge_x.set x_orig σ_init)
      (ow_challenge_x.set_get _ _)
    intro x'
    rw [random_oracle_state.get_of_disjoint_set ow_challenge_x x_orig σ_init,
        hσ_init, random_oracle_state.set_get]
  -- Bound the sum by (q+1)/N.
  calc ∑ x_orig : input, _ / Ninp
      ≤ ∑ _x_orig : input, (((q + 1) : ENNReal) / N) / Ninp := by
        gcongr with x_orig _
        exact h_each x_orig
    _ = ((q + 1) : ENNReal) / N := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hNinp_def]
        exact ENNReal.mul_div_cancel hNinp_pos hNinp_top

include h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x in
/-- The expected `[resp = ow_challenge_x]` indicator is at most `(q+1)/|input|`:
    `ow_challenge_x` is uniform over `input`, and the adversary's `q+1` lazy
    queries (including the final one at `ow_response`) can each "hit"
    `ow_challenge_x` with probability at most `1/|input|`. The bound follows
    by a union bound over those queries plus the trivial "guess" probability. -/
private lemma ow_experiment_resp_eq_chal_x_bound (q : ℕ) (σ₀ : state) :
    (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state =>
          if ow_response.get bσ.2 = ow_challenge_x.get bσ.2 ∧ is_preimage bσ.2
          then (1 : ENNReal) else 0) σ₀
    ≤ ((q + 1) : ENNReal) / Fintype.card input := by
  sorry

include h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x in
/-- **Layer D_OW**: probability bound on `preimage_indicator` at the end of
    the experiment. Combines the two sub-bounds via the decomposition
    `preimage ≤ useful_preimage + [resp = ow_challenge_x ∧ preimage]`. The
    standard tight bound is `2(q+1)/|output|`. -/
private lemma ow_preimage_bound (q : ℕ) (σ₀ : state) :
    (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => preimage_indicator bσ.2) σ₀
    ≤ (2 * (q + 1) : ENNReal) / Fintype.card output := by
  set N : ENNReal := (Fintype.card output : ENNReal) with hN_def
  calc (ow_experiment ow_adv q lazy_init lazy_query).wp
          (fun bσ : Bool × state => preimage_indicator bσ.2) σ₀
      ≤ (ow_experiment ow_adv q lazy_init lazy_query).wp
          (fun bσ : Bool × state => useful_preimage_indicator bσ.2 +
            (if ow_response.get bσ.2 = ow_challenge_x.get bσ.2 ∧ is_preimage bσ.2
             then (1 : ENNReal) else 0)) σ₀ := by
        apply Program.wp_le_wp_of_le
        intro bσ
        exact preimage_le_useful_or_resp_eq_chal_x bσ.2
    _ = (ow_experiment ow_adv q lazy_init lazy_query).wp
          (fun bσ : Bool × state => useful_preimage_indicator bσ.2) σ₀ +
        (ow_experiment ow_adv q lazy_init lazy_query).wp
          (fun bσ : Bool × state =>
            if ow_response.get bσ.2 = ow_challenge_x.get bσ.2 ∧ is_preimage bσ.2
            then (1 : ENNReal) else 0) σ₀ := by
        rw [Program.wp_add]
    _ ≤ ((q + 1) : ENNReal) / N + ((q + 1) : ENNReal) / Fintype.card input := by
        gcongr
        · exact ow_experiment_useful_preimage_bound ow_adv h_ow_adv
            h_ow_adv_chal_y h_ow_adv_chal_x q σ₀
        · exact ow_experiment_resp_eq_chal_x_bound ow_adv h_ow_adv
            h_ow_adv_chal_y h_ow_adv_chal_x q σ₀
    _ ≤ ((q + 1) : ENNReal) / N + ((q + 1) : ENNReal) / N := by
        gcongr
        rw [hN_def]
        exact_mod_cast card_input_ge_output
    _ = (2 * (q + 1) : ENNReal) / N := by
        rw [← ENNReal.add_div]; ring_nf

include h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x in
/-- **Birthday-style bound** for the lazy one-wayness experiment.
    Composes the bookkeeping lemma (`ow_true_implies_preimage_wp`) with the
    probability bound (`ow_preimage_bound`). -/
theorem ow_lazy_bound (q : ℕ) (σ₀ : state) :
    ((ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0)) σ₀
    ≤ (2 * (q + 1) : ENNReal) / Fintype.card output :=
  le_trans (ow_true_implies_preimage_wp ow_adv h_ow_adv_chal_y q σ₀)
    (ow_preimage_bound ow_adv h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x q σ₀)

include h_ow_adv in
/-- **Transfer of `ow_transfer` from the SubProb marginal level to the
    `wp` level**, for postconditions that depend only on the result bit. -/
lemma ow_transfer_wp_of_bit (q : ℕ) (σ₀ : state) (G : Bool → ENNReal) :
    (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => G bσ.1) σ₀
    = (ow_experiment ow_adv q random_oracle_init random_oracle_query).wp
        (fun bσ : Bool × state => G bσ.1) σ₀ := by
  have h_wp_to_marg : ∀ (p : Program state Bool) (σ : state),
      p.wp (fun bσ : Bool × state => G bσ.1) σ
        = (p σ >>= fun bσ : Bool × state =>
            (pure bσ.1 : SubProbability Bool)).expected G := by
    intro p σ
    change (p σ).expected (fun bσ : Bool × state => G bσ.1)
         = (p σ >>= fun bσ : Bool × state =>
              (pure bσ.1 : SubProbability Bool)).expected G
    rw [SubProbability.expected_bind]
    congr 1
    funext bσ
    exact (expected_pure _).symm
  rw [h_wp_to_marg, h_wp_to_marg, ow_transfer ow_adv h_ow_adv]

include h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x in
/-- One-wayness bound for the eager (true random oracle) game, obtained by
    transferring `ow_lazy_bound` via `ow_transfer`. -/
theorem ow_eager_bound (q : ℕ) (σ₀ : state) :
    ((ow_experiment ow_adv q random_oracle_init random_oracle_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0)) σ₀
    ≤ (2 * (q + 1) : ENNReal) / Fintype.card output := by
  rw [← ow_transfer_wp_of_bit ow_adv h_ow_adv q σ₀
        (fun b => if b then (1 : ENNReal) else 0)]
  exact ow_lazy_bound ow_adv h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x q σ₀

end OWParam
