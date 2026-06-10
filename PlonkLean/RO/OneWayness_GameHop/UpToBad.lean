import PlonkLean.RO.OneWayness_GameHop.Definitions
import PlonkLean.RO.OneWayness_GameHop.GuessExperiment

/-!
# OneWayness GameHop: Up-to-Bad Hop (Game 1 → Game 2)

This module contains the **up-to-bad machinery** that bounds the difference
between `ow_game_1_tracked` and `ow_game_2_tracked` by the bad event (the
adversary queried `chal_x`).

The two games differ only in whether the random oracle is *pre-programmed* at
`chal_x` (Game 1 does, Game 2 doesn't). Identical-until-bad means their win
events differ only when adv queries `chal_x` — i.e., when `chal_x_queried_gh`
fires.

## Core lemmas

* `lazy_query_tracked_eq_lazy_query_wp` — at chal_x_qg-ignoring posts,
  `lazy_query_tracked` and `lazy_query` have the same wp.
* `RO_setentry_neq_commutes_lazy_query` — and friends — RO invariance
  under chal_x-update at non-match positions.
* `Program.wp_zero_of_flag_true_in_range` — and friends — at posts that
  vanish when the flag is true, wp is 0 if the flag is already set.
* `ow_game_1_tracked_eq_ow_game_2_tracked_until_bad` — the identical-until-bad
  equality (at flag-non-firing posts).
* `ow_game_1_tracked_bad_eq_ow_game_2_tracked_bad` — bad events agree (via
  mass conservation).
* `ow_game_1_tracked_le_ow_game_2_tracked_plus_bad` — the main hop bound:
  `Pr[Game 1 wins] ≤ Pr[Game 2 wins] + Pr[bad]`.

## Mass conservation infrastructure

A family of `*_mass_one` lemmas (`lazy_query_mass_one`,
`lazy_query_tracked_mass_one`, `oracle_step_lqt_mass_eq_adv_mass`,
`loop_n_mass_one`, etc.) plus `Program.mass_bind` for composing them.
-/

section UpToBad

variable (ow_adv : Program state Unit)

/-! ### Step 1: tracking is invisible to flag-ignoring posts

For any continuation that doesn't read `chal_x_queried_gh`, the extra
`set chal_x_queried_gh ...` calls in `lazy_query_tracked` are no-ops at
the wp level. -/

/-- `IgnoresChalXQueriedGh F` says `F` doesn't read `chal_x_queried_gh`:
    setting the flag to any value doesn't change `F`. -/
def IgnoresChalXQueriedGh {α : Type} (F : α × state → ENNReal) : Prop :=
  ∀ (aσ : α × state) (b : Bool),
    F (aσ.1, chal_x_queried_gh.set b aσ.2) = F aσ

/-- One `lazy_query_tracked` is wp-equivalent to one `lazy_query` for any
    flag-ignoring continuation whose post is also flag-ignoring. -/
lemma lazy_query_tracked_eq_lazy_query_wp
    {α : Type} (k : output → Program state α)
    (h_k_inRange : ∀ y, (k y).inRange chal_x_queried_gh.compl.range)
    (F : α × state → ENNReal) (h_F_inv : IgnoresChalXQueriedGh F)
    (inp : input) (σ : state) :
    (lazy_query_tracked inp >>= k).wp F σ
    = (lazy_query inp >>= k).wp F σ := by
  unfold lazy_query_tracked
  show
    ((lazy_query inp >>= fun y =>
      Program.get ow_challenge_x >>= fun cx =>
        (if inp = cx then Program.set chal_x_queried_gh true
         else (pure () : Program state Unit)) >>= fun _ =>
        (pure y : Program state output)) >>= k).wp F σ
    = (lazy_query inp >>= k).wp F σ
  -- Re-associate the binds so `k` is the innermost continuation.
  simp only [Program.bind_assoc, Program.pure_bind]
  show
    (lazy_query inp >>= fun y =>
      Program.get ow_challenge_x >>= fun cx =>
        (if inp = cx then Program.set chal_x_queried_gh true
         else (pure () : Program state Unit)) >>= fun _ =>
        k y).wp F σ
    = (lazy_query inp >>= k).wp F σ
  rw [wp_bind, wp_bind]
  congr 1
  funext yσ
  exact Program.wp_get_then_conditional_set_disjoint_no_op
    (L_get := ow_challenge_x) (L_set := chal_x_queried_gh)
    (fun cx : input => inp = cx) true (h_k_inRange yσ.1) F
    (fun aσ => h_F_inv aσ true) yσ.2

/-! ### Step 2: RO[chal_x]-invariance for `lazy_query_tracked`

The crux of Hop 1 → 2: for posts `F` that vanish whenever the bad flag is
set AND are themselves RO[chal_x]-invariant, the `lazy_query_tracked` wp
is RO[chal_x]-invariant. Reason:

* If `inp = chal_x`, the conditional set fires, the flag is `true` in any
  post-state, and `F` vanishes (so both wp's are 0).
* If `inp ≠ chal_x`, the `lazy_query` reads RO at `inp` only — and since
  σ and σ_inserted agree on RO[k] for all `k ≠ chal_x`, the behaviour is
  identical.
-/

/-- Shorthand: the state with RO[chal_x] forcibly set to `some y_chal`. -/
noncomputable def insert_at_chal_x (y_chal : output) (σ : state) : state :=
  random_oracle_state.set
    (fun k => if k = ow_challenge_x.get σ then some y_chal
              else random_oracle_state.get σ k) σ

/-- Decompose `lazy_query_tracked.wp` into a `lazy_query.wp` with the
    bad-flag branching folded into the post. -/
lemma lazy_query_tracked_wp_decompose
    (inp : input) (F : output × state → ENNReal) (σ : state) :
    (lazy_query_tracked inp).wp F σ
    = (lazy_query inp).wp
        (fun yσ' : output × state =>
          if inp = ow_challenge_x.get yσ'.2 then
            F (yσ'.1, chal_x_queried_gh.set true yσ'.2)
          else F yσ')
        σ := by
  unfold lazy_query_tracked
  simp only [wp_bind, wp_get, wp_pure]
  congr 1
  funext yσ
  by_cases h : inp = ow_challenge_x.get yσ.2
  · simp only [h, ↓reduceIte, wp_set, wp_pure]
  · simp only [h, ↓reduceIte, wp_pure]

lemma RO_setentry_neq_commutes_lazy_query
    (inp x : input) (h_neq : inp ≠ x) (y : output) (σ : state)
    (F : output × state → ENNReal) :
    (lazy_query inp).wp F
      (random_oracle_state.set (fun k => if k = x then some y
                                       else random_oracle_state.get σ k) σ)
    = (lazy_query inp).wp
      (fun aσ : output × state => F (aσ.1, random_oracle_state.set
                              (fun k => if k = x then some y
                                       else random_oracle_state.get aσ.2 k) aσ.2))
      σ := by
  set σ_xy : state := random_oracle_state.set
    (fun k => if k = x then some y else random_oracle_state.get σ k) σ with σ_xy_def
  have h_RO_xy_inp : random_oracle_state.get σ_xy inp = random_oracle_state.get σ inp := by
    show random_oracle_state.get (random_oracle_state.set _ σ) inp
        = random_oracle_state.get σ inp
    rw [random_oracle_state.set_get, if_neg h_neq]
  simp only [lazy_query, wp_bind, wp_get]
  rw [h_RO_xy_inp]
  cases h_eq : random_oracle_state.get σ inp with
  | some v =>
    simp only [wp_pure]
    -- LHS: F (v, σ_xy). RHS-inner at (v, σ): F (v, RO.set ... σ) = F (v, σ_xy).
    rfl
  | none =>
    simp only [wp_bind, wp_uniform, wp_set, wp_pure]
    -- Need summand-wise: F (v, σ_xy.RO.set (extend inp ↦ v))
    --                  = F (v, RO.set (extend x ↦ y) (σ.RO.set (extend inp ↦ v))).
    have h_setentry_commute : ∀ v : output,
        random_oracle_state.set
          (fun k => if k = inp then some v
                    else random_oracle_state.get (random_oracle_state.set
                          (fun k' => if k' = x then some y else random_oracle_state.get σ k') σ) k)
          (random_oracle_state.set
            (fun k' => if k' = x then some y else random_oracle_state.get σ k') σ)
        = random_oracle_state.set
          (fun k => if k = x then some y else random_oracle_state.get
              (random_oracle_state.set
                (fun k' => if k' = inp then some v else random_oracle_state.get σ k') σ) k)
          (random_oracle_state.set
            (fun k => if k = inp then some v else random_oracle_state.get σ k) σ) := by
      intro v
      rw [random_oracle_state.set_set, random_oracle_state.set_set]
      congr 1
      funext k
      simp only [random_oracle_state.set_get]
      by_cases hk_x : k = x
      · by_cases hk_inp : k = inp
        · exfalso; exact h_neq (hk_inp.symm.trans hk_x)
        · simp [if_pos hk_x, if_neg hk_inp]
      · by_cases hk_inp : k = inp
        · simp [if_neg hk_x, if_pos hk_inp]
        · simp [if_neg hk_x, if_neg hk_inp]
    congr 1
    funext v
    congr 1
    rw [σ_xy_def, h_setentry_commute v]

/-- Per-step invariance for `lazy_query` at inp ≠ `chal_x`. -/
lemma lazy_query_wp_invariant_under_RO_chal_x_set_at_neq
    (inp : input) (F : output × state → ENNReal)
    (h_F_RO_inv : ∀ (a : output) (σ' : state) (y : output),
       F (a, insert_at_chal_x y σ') = F (a, σ'))
    (σ : state) (y_chal : output)
    (h_neq : inp ≠ ow_challenge_x.get σ) :
    (lazy_query inp).wp F (insert_at_chal_x y_chal σ)
    = (lazy_query inp).wp F σ := by
  -- σ_ins = RO.set (extend (chal_x σ) ↦ y_chal) σ. Apply the commutativity.
  unfold insert_at_chal_x
  rw [RO_setentry_neq_commutes_lazy_query inp (ow_challenge_x.get σ) h_neq y_chal σ F]
  -- Now LHS post is `fun aσ => F (aσ.1, RO.set (extend (chal_x σ) ↦ y_chal) aσ.2)`.
  -- The `RO.set (extend (chal_x σ) ↦ y_chal) aσ.2` equals `insert_at_chal_x y_chal aσ.2`
  -- when chal_x aσ.2 = chal_x σ (which holds because lazy_query doesn't write chal_x).
  -- Strengthen both wp's via `wp_strengthen_lens_preserved` on `ow_challenge_x` to
  -- get the chal_x-preservation hypothesis, then apply h_F_RO_inv.
  have h_lq_chalx : (lazy_query inp).inRange ow_challenge_x.compl.range :=
    Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_x)
  conv_lhs => rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_lq_chalx]
  conv_rhs => rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_lq_chalx]
  congr 1
  funext aσ
  by_cases h_chal : ow_challenge_x.get aσ.2 = ow_challenge_x.get σ
  · simp only [if_pos h_chal]
    -- F (aσ.1, RO.set (extend (chal_x σ) ↦ y_chal) aσ.2) = F (aσ.1, aσ.2)
    -- Since chal_x aσ.2 = chal_x σ, the set function matches insert_at_chal_x at aσ.2.
    rw [← h_chal]
    -- Now: F (aσ.1, RO.set (extend (chal_x aσ.2) ↦ y_chal) aσ.2) = F (aσ.1, aσ.2)
    -- The RO.set ... aσ.2 is exactly `insert_at_chal_x y_chal aσ.2`.
    have : (fun k => if k = ow_challenge_x.get aσ.2 then some y_chal
                     else random_oracle_state.get aσ.2 k)
        = (fun k => if k = ow_challenge_x.get aσ.2 then some y_chal
                     else random_oracle_state.get aσ.2 k) := rfl
    show F (aσ.1, random_oracle_state.set _ aσ.2) = F aσ
    have h_eq : random_oracle_state.set
        (fun k => if k = ow_challenge_x.get aσ.2 then some y_chal
                  else random_oracle_state.get aσ.2 k) aσ.2
      = insert_at_chal_x y_chal aσ.2 := rfl
    rw [h_eq, h_F_RO_inv]
  · simp only [if_neg h_chal]

/-- Per-step invariance for `lazy_query_tracked`. -/
lemma lazy_query_tracked_wp_invariant_under_RO_chal_x_set
    (inp : input) (F : output × state → ENNReal)
    (h_F_bad_zero : ∀ aσ, chal_x_queried_gh.get aσ.2 = true → F aσ = 0)
    (h_F_RO_inv : ∀ (a : output) (σ' : state) (y : output),
       F (a, insert_at_chal_x y σ') = F (a, σ'))
    (σ : state) (y_chal : output) :
    (lazy_query_tracked inp).wp F (insert_at_chal_x y_chal σ)
    = (lazy_query_tracked inp).wp F σ := by
  rw [lazy_query_tracked_wp_decompose, lazy_query_tracked_wp_decompose]
  have h_lq_chalx : (lazy_query inp).inRange ow_challenge_x.compl.range :=
    Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_x)
  have h_chalx_σ_ins :
      ow_challenge_x.get (insert_at_chal_x y_chal σ) = ow_challenge_x.get σ := by
    unfold insert_at_chal_x
    rw [ow_challenge_x.get_of_disjoint_set]
  by_cases h : inp = ow_challenge_x.get σ
  · -- inp = chal_x σ. After chal_x-preserving strengthening, the if-positive branch is taken
    -- everywhere, giving F (·, flag.set true ·) = 0 by h_F_bad_zero. Both wp's are 0.
    have h_post_zero : ∀ (σ' : state),
        ow_challenge_x.get σ' = ow_challenge_x.get σ →
        (lazy_query inp).wp
          (fun yσ' : output × state =>
            if inp = ow_challenge_x.get yσ'.2 then
              F (yσ'.1, chal_x_queried_gh.set true yσ'.2)
            else F yσ') σ' = 0 := by
      intro σ' h_chalx
      rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_lq_chalx]
      rw [show (fun yσ' : output × state =>
                if ow_challenge_x.get yσ'.2 = ow_challenge_x.get σ' then
                  (if inp = ow_challenge_x.get yσ'.2 then
                    F (yσ'.1, chal_x_queried_gh.set true yσ'.2)
                   else F yσ')
                else 0)
              = (fun _ : output × state => (0 : ENNReal)) from by
        funext yσ'
        by_cases h_chal : ow_challenge_x.get yσ'.2 = ow_challenge_x.get σ'
        · simp only [if_pos h_chal]
          rw [h_chal, h_chalx, ← h]
          simp only [if_pos rfl]
          exact h_F_bad_zero _ (by rw [chal_x_queried_gh.set_get])
        · simp only [if_neg h_chal]]
      exact Program.wp_zero_post _ _
    rw [h_post_zero (insert_at_chal_x y_chal σ) h_chalx_σ_ins]
    rw [h_post_zero σ rfl]
  · -- inp ≠ chal_x σ. After chal_x-preserving strengthening, the if-positive branch is never
    -- taken on the support. So Cont = F on support. Apply at-neq for F.
    have h_reduce_to_F : ∀ (σ' : state),
        ow_challenge_x.get σ' = ow_challenge_x.get σ →
        (lazy_query inp).wp
          (fun yσ' : output × state =>
            if inp = ow_challenge_x.get yσ'.2 then
              F (yσ'.1, chal_x_queried_gh.set true yσ'.2)
            else F yσ') σ'
        = (lazy_query inp).wp F σ' := by
      intro σ' h_chalx
      rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_lq_chalx]
      conv_rhs => rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_lq_chalx]
      congr 1
      funext yσ'
      by_cases h_chal : ow_challenge_x.get yσ'.2 = ow_challenge_x.get σ'
      · simp only [if_pos h_chal]
        rw [h_chal, h_chalx]
        rw [if_neg h]
      · simp only [if_neg h_chal]
    rw [h_reduce_to_F (insert_at_chal_x y_chal σ) h_chalx_σ_ins]
    rw [h_reduce_to_F σ rfl]
    exact lazy_query_wp_invariant_under_RO_chal_x_set_at_neq inp F h_F_RO_inv σ y_chal h

lemma Program.wp_zero_of_flag_true_in_range
    {α : Type} {p : Program state α} (h_p : p.inRange chal_x_queried_gh.compl.range)
    {F : α × state → ENNReal}
    (h_F_bad_zero : ∀ aσ, chal_x_queried_gh.get aσ.2 = true → F aσ = 0)
    {σ : state} (h_σ : chal_x_queried_gh.get σ = true) :
    p.wp F σ = 0 := by
  rw [Program.wp_strengthen_lens_preserved chal_x_queried_gh h_p]
  rw [show (fun aσ : α × state =>
            if chal_x_queried_gh.get aσ.2 = chal_x_queried_gh.get σ then F aσ else 0)
          = (fun _ : α × state => (0 : ENNReal)) from by
    funext aσ
    by_cases h : chal_x_queried_gh.get aσ.2 = chal_x_queried_gh.get σ
    · simp only [if_pos h]
      apply h_F_bad_zero
      rw [h]; exact h_σ
    · simp only [if_neg h]]
  exact Program.wp_zero_post _ _

/-- **Flag-true-zero for `lazy_query_tracked`**: starting at flag-true, the wp on a
    bad-vanishing post is 0. `lazy_query_tracked` may set flag to true but never to
    false, so all post-states have flag = true. -/
lemma lazy_query_tracked_wp_at_flag_true
    (inp : input) (F : output × state → ENNReal)
    (h_F_bad_zero : ∀ aσ, chal_x_queried_gh.get aσ.2 = true → F aσ = 0)
    (σ : state) (h_flag : chal_x_queried_gh.get σ = true) :
    (lazy_query_tracked inp).wp F σ = 0 := by
  rw [lazy_query_tracked_wp_decompose]
  have h_lq_flag : (lazy_query inp).inRange chal_x_queried_gh.compl.range :=
    Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)
  refine Program.wp_zero_of_flag_true_in_range h_lq_flag ?_ h_flag
  intro yσ' h_yσ'_flag
  by_cases h : inp = ow_challenge_x.get yσ'.2
  · simp only [if_pos h]
    exact h_F_bad_zero _ (by rw [chal_x_queried_gh.set_get])
  · simp only [if_neg h]
    exact h_F_bad_zero yσ' h_yσ'_flag

/-- **Flag-true-zero for `oracle_step`**: same property as for `lazy_query_tracked`,
    extended to a single oracle step. The adversary is flag-disjoint, the
    `get oracle_input` is no-op, the `lazy_query_tracked` step uses its own
    flag-true-zero lemma, and the `set oracle_output` is flag-disjoint. -/
lemma oracle_step_wp_at_flag_true
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (F : Unit × state → ENNReal)
    (h_F_bad_zero : ∀ aσ, chal_x_queried_gh.get aσ.2 = true → F aσ = 0)
    (σ : state) (h_flag : chal_x_queried_gh.get σ = true) :
    (oracle_step ow_adv lazy_query_tracked).wp F σ = 0 := by
  -- oracle_step adv lazy_query_tracked = adv >>= fun _ =>
  --   Program.set oracle_output (← lazy_query_tracked (← Program.get oracle_input))
  show (do
          ow_adv
          let inp ← Program.get oracle_input
          let y ← lazy_query_tracked inp
          Program.set oracle_output y).wp F σ = 0
  simp only [wp_bind, wp_get]
  -- ow_adv.wp (fun aσ_adv => (lazy_query_tracked (oracle_input.get aσ_adv.2)).wp
  --                            (fun yσ_lq => (set oracle_output yσ_lq.1).wp F yσ_lq.2)
  --                          aσ_adv.2) σ = 0
  -- Apply Program.wp_zero_of_flag_true_in_range with ow_adv.
  refine Program.wp_zero_of_flag_true_in_range h_ow_adv_chal_x_queried_gh ?_ h_flag
  intro aσ_adv h_adv_flag
  -- Inner: (lazy_query_tracked (oracle_input.get aσ_adv.2)).wp Cont aσ_adv.2
  -- with Cont = fun yσ_lq => (set oo yσ_lq.1).wp F yσ_lq.2.
  -- Apply lazy_query_tracked_wp_at_flag_true.
  apply lazy_query_tracked_wp_at_flag_true
  · intro yσ_lq h_yσ_lq_flag
    -- (set oracle_output yσ_lq.1).wp F yσ_lq.2 = F ((), oo.set yσ_lq.1 yσ_lq.2).
    -- oo is disjoint from flag, so flag is preserved at true.
    simp only [wp_set]
    apply h_F_bad_zero
    show chal_x_queried_gh.get (oracle_output.set yσ_lq.1 yσ_lq.2) = true
    rw [chal_x_queried_gh.get_of_disjoint_set]
    exact h_yσ_lq_flag
  · exact h_adv_flag

/-- **Flag-true-zero for `oracle_loop_n`**: the loop preserves the flag-true-zero
    property. By induction on the iteration count. -/
lemma oracle_loop_n_lazy_query_tracked_wp_at_flag_true
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (q : ℕ) (F : Unit × state → ENNReal)
    (h_F_bad_zero : ∀ aσ, chal_x_queried_gh.get aσ.2 = true → F aσ = 0)
    (σ : state) (h_flag : chal_x_queried_gh.get σ = true) :
    (oracle_loop_n ow_adv q lazy_query_tracked).wp F σ = 0 := by
  induction q generalizing F σ with
  | zero =>
    simp only [oracle_loop_n, wp_pure]
    exact h_F_bad_zero ((), σ) h_flag
  | succ n IH =>
    show (oracle_step ow_adv lazy_query_tracked >>= fun _ =>
          oracle_loop_n ow_adv n lazy_query_tracked).wp F σ = 0
    rw [wp_bind]
    refine oracle_step_wp_at_flag_true ow_adv h_ow_adv_chal_x_queried_gh
      (fun aσ_step : Unit × state =>
        (oracle_loop_n ow_adv n lazy_query_tracked).wp F aσ_step.2)
      ?_ σ h_flag
    intro yσ' h_yσ'_flag
    exact IH F h_F_bad_zero yσ'.2 h_yσ'_flag

/-- **`oracle_step` preserves RO[chal_x]-invariance**: if the post `F`
    is bad-vanishing and RO[chal_x]-invariant, then the wp's at `σ` and
    `insert_at_chal_x y_chal σ` agree.

    Proof uses `wp_shift_input` via `h_ow_adv` (the adversary is RO-disjoint,
    so it commutes with RO writes), then chal_x-preservation strengthening,
    then the per-step lemma for `lazy_query_tracked`. -/
lemma oracle_step_lazy_query_tracked_wp_invariant_under_RO_chal_x_set
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (F : Unit × state → ENNReal)
    (h_F_bad_zero : ∀ aσ, chal_x_queried_gh.get aσ.2 = true → F aσ = 0)
    (h_F_RO_inv : ∀ (a : Unit) (σ' : state) (y : output),
       F (a, insert_at_chal_x y σ') = F (a, σ'))
    (σ : state) (y_chal : output) :
    (oracle_step ow_adv lazy_query_tracked).wp F (insert_at_chal_x y_chal σ)
    = (oracle_step ow_adv lazy_query_tracked).wp F σ := by
  set x_val := ow_challenge_x.get σ with x_val_def
  -- σ-independent shift function: f σ' = RO.set (extend x_val ↦ y_chal) σ'.
  set f : state → state := fun σ' =>
    random_oracle_state.set (fun k => if k = x_val then some y_chal
                                     else random_oracle_state.get σ' k) σ' with f_def
  have h_f_in_updates :
      f ∈ ((random_oracle_state.compl.range : LensRange state)ᶜ).updates := by
    rw [show ((random_oracle_state.compl.range : LensRange state)ᶜ) =
          random_oracle_state.range from by
      rw [LensRange.complement_range, LensRange.compl_compl]]
    exact ⟨fun h k => if k = x_val then some y_chal else h k, Set.mem_univ _, rfl⟩
  have h_f_at_σ : f σ = insert_at_chal_x y_chal σ := rfl
  show (do
          ow_adv
          let inp ← Program.get oracle_input
          let y ← lazy_query_tracked inp
          Program.set oracle_output y).wp F (insert_at_chal_x y_chal σ)
     = (do
          ow_adv
          let inp ← Program.get oracle_input
          let y ← lazy_query_tracked inp
          Program.set oracle_output y).wp F σ
  simp only [wp_bind, wp_get]
  rw [← h_f_at_σ]
  rw [Program.wp_shift_input h_ow_adv h_f_in_updates]
  -- Both sides: ow_adv.wp G' σ where G' aσ_adv = Inner f-shifted or unshifted.
  -- Strengthen by chal_x preservation, then on the support, f = insert_at_chal_x.
  rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_ow_adv_chal_x]
  conv_rhs => rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_ow_adv_chal_x]
  congr 1
  funext aσ_adv
  by_cases h_chal : ow_challenge_x.get aσ_adv.2 = ow_challenge_x.get σ
  · simp only [if_pos h_chal]
    have h_f_eq : f aσ_adv.2 = insert_at_chal_x y_chal aσ_adv.2 := by
      show random_oracle_state.set _ aσ_adv.2 = random_oracle_state.set _ aσ_adv.2
      congr 1
      funext k
      by_cases hk : k = x_val
      · have hk' : k = ow_challenge_x.get aσ_adv.2 := by rw [hk, x_val_def, ← h_chal]
        simp only [if_pos hk, if_pos hk']
      · have hk' : k ≠ ow_challenge_x.get aσ_adv.2 := by
          intro h_eq
          exact hk ((h_eq.trans h_chal).trans x_val_def.symm)
        simp only [if_neg hk, if_neg hk']
    rw [h_f_eq]
    haveI : disjoint random_oracle_state oracle_input := disjoint_oracle_input_ro.symm
    have h_oi_get : oracle_input.get (insert_at_chal_x y_chal aσ_adv.2)
                  = oracle_input.get aσ_adv.2 := by
      unfold insert_at_chal_x
      rw [oracle_input.get_of_disjoint_set]
    rw [h_oi_get]
    -- Apply lazy_query_tracked_wp_invariant_under_RO_chal_x_set with Cont as the F.
    have h_Cont_bad_zero : ∀ yσ_lq : output × state,
        chal_x_queried_gh.get yσ_lq.2 = true →
        (Program.set oracle_output yσ_lq.1).wp F yσ_lq.2 = 0 := by
      intro yσ_lq h_flag
      rw [wp_set]
      apply h_F_bad_zero
      show chal_x_queried_gh.get (oracle_output.set yσ_lq.1 yσ_lq.2) = true
      rw [chal_x_queried_gh.get_of_disjoint_set]
      exact h_flag
    have h_Cont_RO_inv : ∀ (a : output) (σ'' : state) (y : output),
        (Program.set oracle_output a).wp F (insert_at_chal_x y σ'')
        = (Program.set oracle_output a).wp F σ'' := by
      intro a σ'' y
      simp only [wp_set]
      have h_commute : oracle_output.set a (insert_at_chal_x y σ'')
                     = insert_at_chal_x y (oracle_output.set a σ'') := by
        unfold insert_at_chal_x
        rw [disjoint_oracle_output_ro.commute]
        congr 1
        funext k
        rw [ow_challenge_x.get_of_disjoint_set]
        by_cases hk : k = ow_challenge_x.get σ''
        · simp only [if_pos hk]
        · simp only [if_neg hk]
          rw [random_oracle_state.get_of_disjoint_set]
      rw [h_commute, h_F_RO_inv]
    exact lazy_query_tracked_wp_invariant_under_RO_chal_x_set
      (oracle_input.get aσ_adv.2)
      (fun yσ_lq => (Program.set oracle_output yσ_lq.1).wp F yσ_lq.2)
      h_Cont_bad_zero h_Cont_RO_inv aσ_adv.2 y_chal
  · simp only [if_neg h_chal]
/-- **Loop-level RO[chal_x]-invariance**: the q-iteration adversary loop
    preserves the RO[chal_x]-invariance + bad-vanishing post equality. By
    induction on `q`, using the per-step lemma at each oracle_step and
    the flag-true-zero lemma to show the inner wp is bad-vanishing. -/
lemma oracle_loop_n_lazy_query_tracked_wp_invariant_under_RO_chal_x_set
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (q : ℕ) (F : Unit × state → ENNReal)
    (h_F_bad_zero : ∀ aσ, chal_x_queried_gh.get aσ.2 = true → F aσ = 0)
    (h_F_RO_inv : ∀ (a : Unit) (σ' : state) (y : output),
       F (a, insert_at_chal_x y σ') = F (a, σ'))
    (σ : state) (y_chal : output) :
    (oracle_loop_n ow_adv q lazy_query_tracked).wp F (insert_at_chal_x y_chal σ)
    = (oracle_loop_n ow_adv q lazy_query_tracked).wp F σ := by
  induction q generalizing F σ y_chal with
  | zero =>
    simp only [oracle_loop_n, wp_pure]
    exact h_F_RO_inv () σ y_chal
  | succ n IH =>
    show (oracle_step ow_adv lazy_query_tracked >>= fun _ =>
          oracle_loop_n ow_adv n lazy_query_tracked).wp F (insert_at_chal_x y_chal σ)
       = (oracle_step ow_adv lazy_query_tracked >>= fun _ =>
          oracle_loop_n ow_adv n lazy_query_tracked).wp F σ
    simp only [wp_bind]
    refine oracle_step_lazy_query_tracked_wp_invariant_under_RO_chal_x_set
      ow_adv h_ow_adv h_ow_adv_chal_x
      (fun aσ_step : Unit × state =>
        (oracle_loop_n ow_adv n lazy_query_tracked).wp F aσ_step.2)
      ?_ ?_ σ y_chal
    · intro aσ_step h_flag
      exact oracle_loop_n_lazy_query_tracked_wp_at_flag_true ow_adv
        h_ow_adv_chal_x_queried_gh n F h_F_bad_zero aσ_step.2 h_flag
    · intro a σ' y
      exact IH F h_F_bad_zero h_F_RO_inv σ' y


theorem ow_game_1_tracked_eq_ow_game_2_tracked_until_bad
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (q : ℕ) (G : Bool × state → ENNReal)
    (h_G_RO_inv : ∀ (bσ : Bool × state) (y : output),
       G (bσ.1, insert_at_chal_x y bσ.2) = G bσ)
    (σ : state) :
    (ow_game_1_tracked ow_adv q).wp
      (fun bσ : Bool × state =>
        if chal_x_queried_gh.get bσ.2 = true then 0 else G bσ) σ
    = (ow_game_2_tracked ow_adv q).wp
      (fun bσ : Bool × state =>
        if chal_x_queried_gh.get bσ.2 = true then 0 else G bσ) σ := by
  set F : Bool × state → ENNReal :=
    fun bσ => if chal_x_queried_gh.get bσ.2 = true then 0 else G bσ with F_def
  have h_F_bad_zero : ∀ bσ : Bool × state,
      chal_x_queried_gh.get bσ.2 = true → F bσ = 0 := by
    intro bσ h_flag; simp [F_def, h_flag]
  have h_F_RO_inv : ∀ (b : Bool) (σ' : state) (y : output),
      F (b, insert_at_chal_x y σ') = F (b, σ') := by
    intro b σ' y
    simp only [F_def]
    have h_flag_inv : chal_x_queried_gh.get (insert_at_chal_x y σ')
                    = chal_x_queried_gh.get σ' := by
      unfold insert_at_chal_x
      rw [chal_x_queried_gh.get_of_disjoint_set]
    rw [h_flag_inv]
    by_cases h : chal_x_queried_gh.get σ' = true
    · simp [h]
    · simp [h]; exact h_G_RO_inv (b, σ') y
  -- Unfold games. Apply wp on lazy_init (= set RO none), flag init, sample x, set chal_x, sample y.
  -- Leave the divergent `set RO ...` and the tail (`set chal_y`, loop, etc.) as binds.
  unfold ow_game_1_tracked ow_game_2_tracked lazy_init
  simp only [wp_bind, wp_set, wp_uniform]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  -- σ_pre = chal_x.set x (flag.set false (RO.set (fun _ => none) σ)).
  set σ_pre := ow_challenge_x.set x
    (chal_x_queried_gh.set false (random_oracle_state.set (fun _ => none) σ))
    with σ_pre_def
  -- LHS: (set chal_y y >>= ...).wp F (chal_y-state with RO-inserted).
  -- After the simp, LHS has chal_y.set y (RO.set f σ_pre); RHS has chal_y.set y σ_pre.
  -- We need: chal_y.set y (RO.set f σ_pre) = chal_y.set y σ_pre re: the loop_n.wp output.
  -- Note: RO.set f σ_pre = insert_at_chal_x y σ_pre. Commute chal_y.set with RO.set:
  -- chal_y.set y (RO.set f σ_pre) = RO.set f (chal_y.set y σ_pre) = insert (chal_y.set y σ_pre).
  -- Then apply loop-level invariance with appropriate post.
  have h_chal_x_at_σ_pre : ow_challenge_x.get σ_pre = x := by
    show ow_challenge_x.get (ow_challenge_x.set x _) = x
    rw [ow_challenge_x.set_get]
  have h_RO_at_σ_pre : ∀ k, random_oracle_state.get σ_pre k = none := by
    intro k
    show random_oracle_state.get (ow_challenge_x.set x
      (chal_x_queried_gh.set false (random_oracle_state.set (fun _ => none) σ))) k = none
    rw [random_oracle_state.get_of_disjoint_set]
    rw [random_oracle_state.get_of_disjoint_set]
    rw [random_oracle_state.set_get]
  -- State equation: chal_y.set y (RO.set f σ_pre) = insert_at_chal_x y (chal_y.set y σ_pre).
  have h_state_eq :
      ow_challenge_y.set y (random_oracle_state.set (fun k => if k = x then some y else none) σ_pre)
      = insert_at_chal_x y (ow_challenge_y.set y σ_pre) := by
    haveI : disjoint ow_challenge_y random_oracle_state := disjoint_ow_challenge_y_ro
    rw [disjoint_ow_challenge_y_ro.commute]
    unfold insert_at_chal_x
    congr 1
    funext k
    haveI : disjoint ow_challenge_y ow_challenge_x := disjoint_ow_challenge_y_ow_challenge_x
    rw [ow_challenge_x.get_of_disjoint_set]
    rw [h_chal_x_at_σ_pre]
    by_cases hk : k = x
    · simp [hk]
    · simp only [if_neg hk]
      rw [random_oracle_state.get_of_disjoint_set]
      exact (h_RO_at_σ_pre k).symm
  rw [h_state_eq]
  -- Now: LHS = loop_n.wp (cont) (insert (chal_y.set y σ_pre)),
  --      RHS = loop_n.wp (cont) (chal_y.set y σ_pre).
  -- Apply loop-level RO[chal_x]-invariance.
  refine oracle_loop_n_lazy_query_tracked_wp_invariant_under_RO_chal_x_set
    ow_adv h_ow_adv h_ow_adv_chal_x h_ow_adv_chal_x_queried_gh q _ ?_ ?_
    (ow_challenge_y.set y σ_pre) y
  · -- post bad-vanishing at flag-true state.
    intro aσ_loop h_flag
    simp only [wp_bind, wp_get]
    haveI : disjoint chal_x_queried_gh ow_response := disjoint_chal_x_queried_gh_ow_response
    apply lazy_query_tracked_wp_at_flag_true _ _ _ aσ_loop.2 h_flag
    intro yσ_lq h_yσ_lq_flag
    simp only [wp_pure]
    exact h_F_bad_zero _ h_yσ_lq_flag
  · -- post RO[chal_x]-inv.
    intro a σ_inner y_inner
    simp only [wp_bind, wp_get]
    have h_resp_get : ow_response.get (insert_at_chal_x y_inner σ_inner)
                    = ow_response.get σ_inner := by
      unfold insert_at_chal_x
      rw [ow_response.get_of_disjoint_set]
    rw [h_resp_get]
    refine lazy_query_tracked_wp_invariant_under_RO_chal_x_set
      (ow_response.get σ_inner)
      (fun yσ_lq : output × state =>
        (pure (decide (yσ_lq.1 = y)) : Program state Bool).wp F yσ_lq.2)
      ?_ ?_ σ_inner y_inner
    · intro yσ_lq h_yσ_lq_flag
      simp only [wp_pure]
      exact h_F_bad_zero _ h_yσ_lq_flag
    · intro a' σ'' y''
      simp only [wp_pure]
      exact h_F_RO_inv _ σ'' y''

/-! ### Bad-event probability equality

The bad-event probability is the same in G1 and G2. Proof uses
identical-until-bad (for non-bad complement) + mass conservation
(both games have the same total mass) + linearity.

Mass conservation REQUIRES the adversary to be a probability program
(mass = 1 at every state). For sub-probability adversaries, post-bad
termination probabilities can differ between G1 and G2. -/

/-- Mass of `lazy_query` is 1 at any state — it always returns. -/
lemma lazy_query_mass_one (inp : input) (σ : state) :
    (lazy_query inp).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  unfold lazy_query
  rw [wp_bind, wp_get]
  rcases h : (random_oracle_state.get σ) inp with _ | y_cached
  · -- none: sample fresh, set, return.
    simp only [h]
    rw [wp_bind, wp_uniform]
    simp only [wp_bind, wp_set, wp_pure]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    exact ENNReal.div_mul_cancel
      (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
  · -- some: return cached value.
    simp only [h]
    rw [wp_pure]

/-- Mass of `lazy_query_tracked` is 1 at any state. -/
lemma lazy_query_tracked_mass_one (inp : input) (σ : state) :
    (lazy_query_tracked inp).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  have h_rest_mass : ∀ (y : output) (σ' : state),
      (Program.get ow_challenge_x >>= fun cx =>
        (if inp = cx then Program.set chal_x_queried_gh true
         else (pure () : Program state Unit)) >>= fun _ =>
        (pure y : Program state output)).wp (fun _ => (1 : ENNReal)) σ' = 1 := by
    intro y σ'
    rw [wp_bind, wp_get]
    dsimp only
    rw [wp_bind]
    by_cases h : inp = ow_challenge_x.get σ'
    · simp only [if_pos h, wp_set, wp_pure]
    · simp only [if_neg h, wp_pure]
  unfold lazy_query_tracked
  rw [wp_bind]
  have h_post_const : (fun aσ : output × state =>
      (Program.get ow_challenge_x >>= fun cx =>
        (if inp = cx then Program.set chal_x_queried_gh true
         else (pure () : Program state Unit)) >>= fun _ =>
        (pure aσ.1 : Program state output)).wp (fun _ => (1 : ENNReal)) aσ.2)
    = fun _ : output × state => (1 : ENNReal) := by
    funext aσ
    exact h_rest_mass aσ.1 aσ.2
  rw [h_post_const]
  exact lazy_query_mass_one inp σ

/-- Mass of `oracle_step adv lazy_query_tracked` equals mass of `adv`. -/
lemma oracle_step_lqt_mass_eq_adv_mass (σ : state) :
    (oracle_step ow_adv lazy_query_tracked).wp (fun _ => (1 : ENNReal)) σ
    = ow_adv.wp (fun _ => (1 : ENNReal)) σ := by
  unfold oracle_step
  rw [wp_bind]
  have h_post_const : (fun aσ : Unit × state =>
      (Program.get oracle_input >>= fun inp =>
        lazy_query_tracked inp >>= fun y =>
        Program.set oracle_output y).wp (fun _ => (1 : ENNReal)) aσ.2)
    = fun _ : Unit × state => (1 : ENNReal) := by
    funext aσ
    rw [wp_bind, wp_get]
    dsimp only
    rw [wp_bind]
    have h_post_lqt : (fun yσ : output × state =>
        (Program.set oracle_output yσ.1).wp (fun _ => (1 : ENNReal)) yσ.2)
      = fun _ : output × state => (1 : ENNReal) := by
      funext yσ
      rw [wp_set]
    rw [h_post_lqt]
    exact lazy_query_tracked_mass_one _ aσ.2
  rw [h_post_const]

/-- Mass of `loop_n n body` is `1` if body has mass 1 at every state. -/
lemma loop_n_mass_one
    (body : Program state Unit)
    (h_body : ∀ σ, body.wp (fun _ => (1 : ENNReal)) σ = 1)
    (n : ℕ) (σ : state) :
    (loop_n n body).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  induction n generalizing σ with
  | zero => rw [show loop_n 0 body = pure () from rfl, wp_pure]
  | succ n ih =>
    show (body >>= fun _ => loop_n n body).wp (fun _ => (1 : ENNReal)) σ = 1
    rw [wp_bind]
    have h_post : (fun aσ : Unit × state =>
        (loop_n n body).wp (fun _ => (1 : ENNReal)) aσ.2)
      = fun _ : Unit × state => (1 : ENNReal) := by
      funext aσ
      exact ih aσ.2
    rw [h_post]
    exact h_body σ

/-- Mass of `oracle_loop_n adv q lazy_query_tracked` is `1` if adv has mass 1. -/
lemma oracle_loop_n_lqt_mass_one
    (h_adv_mass : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1)
    (q : ℕ) (σ : state) :
    (oracle_loop_n ow_adv q lazy_query_tracked).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  rw [oracle_loop_n_eq_loop_n]
  apply loop_n_mass_one
  intro σ'
  rw [oracle_step_lqt_mass_eq_adv_mass]
  exact h_adv_mass σ'

/-- Mass-preservation under bind: if `p` and every `k a` have mass 1, then `p >>= k` has mass 1. -/
lemma Program.mass_bind {α β : Type}
    (p : Program state α) (k : α → Program state β)
    (hp : ∀ σ, p.wp (fun _ => (1 : ENNReal)) σ = 1)
    (hk : ∀ a σ, (k a).wp (fun _ => (1 : ENNReal)) σ = 1)
    (σ : state) :
    (p >>= k).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  rw [wp_bind]
  have h_post : (fun aσ : α × state => (k aσ.1).wp (fun _ => (1 : ENNReal)) aσ.2)
              = fun _ : α × state => (1 : ENNReal) := by
    funext aσ
    exact hk aσ.1 aσ.2
  rw [h_post]
  exact hp σ

/-- Mass of `Program.set` is always 1. -/
lemma Program.set_mass_one {α : Type} (L : Lens α state) (v : α) (σ : state) :
    (Program.set L v).wp (fun _ => (1 : ENNReal)) σ = 1 := by rw [wp_set]

/-- Mass of `Program.uniform` is always 1. -/
lemma Program.uniform_mass_one {α : Type} [Fintype α] [Nonempty α] (σ : state) :
    (Program.uniform : Program state α).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  rw [wp_uniform]
  show ∑ _i : α, (1 : ENNReal) / (Fintype.card α : ENNReal) = 1
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_div_assoc, mul_one,
      ENNReal.div_self
        (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0))
        (ENNReal.natCast_ne_top _)]

/-- **Bad-event invariance.** P[bad in G1] = P[bad in G2].

    Proven via identical-until-bad (for F_nonBad) + mass conservation
    + linearity + ENNReal cancellation. Mass conservation requires that
    `ow_adv` is a probability program (mass = 1 at every state), captured
    by `h_ow_adv_mass_one`. -/
lemma ow_game_1_tracked_bad_eq_ow_game_2_tracked_bad
    (h_ow_adv_RO : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_ow_adv_mass_one : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1)
    (q : ℕ) (σ : state) :
    (ow_game_1_tracked ow_adv q).wp
        (fun bσ : Bool × state =>
          if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
    = (ow_game_2_tracked ow_adv q).wp
        (fun bσ : Bool × state =>
          if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ := by
  set F_bad : Bool × state → ENNReal :=
    fun bσ => if chal_x_queried_gh.get bσ.2 = true then 1 else 0 with F_bad_def
  set F_nonBad : Bool × state → ENNReal :=
    fun bσ => if chal_x_queried_gh.get bσ.2 = true then 0 else 1 with F_nonBad_def
  -- Step 1: identical-until-bad with G = const 1 gives F_nonBad equality.
  have h_nonBad_eq : (ow_game_1_tracked ow_adv q).wp F_nonBad σ
                  = (ow_game_2_tracked ow_adv q).wp F_nonBad σ :=
    ow_game_1_tracked_eq_ow_game_2_tracked_until_bad ow_adv h_ow_adv_RO
      h_ow_adv_chal_x h_ow_adv_chal_x_queried_gh q (fun _ => 1) (fun _ _ => rfl) σ
  -- Step 2: linearity decomposition.
  have h_decompose : ∀ (p : Program state Bool),
      p.wp (fun _ => (1 : ENNReal)) σ = p.wp F_nonBad σ + p.wp F_bad σ := by
    intro p
    rw [← Program.wp_add]
    congr 1
    funext bσ
    simp only [F_nonBad_def, F_bad_def]
    by_cases h : chal_x_queried_gh.get bσ.2 = true
    · simp [h]
    · simp [h]
  -- Step 3: mass conservation. Each game has mass = 1, since all operations
  -- (lazy_init, set, uniform, get, lazy_query_tracked, oracle_loop_n, pure)
  -- have mass 1 individually, and adv has mass 1 by hypothesis.
  have h_tail_mass : ∀ (y_outer : output) (σ' : state),
      ((oracle_loop_n ow_adv q lazy_query_tracked) >>= fun _ =>
        Program.get ow_response >>= fun resp =>
        lazy_query_tracked resp >>= fun y_check =>
        (pure (decide (y_check = y_outer)) : Program state Bool)).wp
          (fun _ => (1 : ENNReal)) σ' = 1 := by
    intro y_outer σ'
    rw [wp_bind]
    have h_post : (fun aσ : Unit × state =>
        (Program.get ow_response >>= fun resp =>
          lazy_query_tracked resp >>= fun y_check =>
          (pure (decide (y_check = y_outer)) : Program state Bool)).wp
            (fun _ => (1 : ENNReal)) aσ.2)
      = fun _ : Unit × state => (1 : ENNReal) := by
      funext aσ
      rw [wp_bind, wp_get]
      dsimp only
      rw [wp_bind]
      have h_post2 : (fun yσ : output × state =>
          (Pure.pure (decide (yσ.1 = y_outer)) : Program state Bool).wp
            (fun _ => (1 : ENNReal)) yσ.2)
        = fun _ : output × state => (1 : ENNReal) := by
        funext yσ
        rw [wp_pure]
      rw [h_post2]
      exact lazy_query_tracked_mass_one _ aσ.2
    rw [h_post]
    exact oracle_loop_n_lqt_mass_one ow_adv h_ow_adv_mass_one q σ'
  -- Mass of G_i = 1. Each game = lazy_init; set chal_xqg false; uniform x;
  -- set chal_x x; uniform y; [set RO?;] set chal_y y; oracle_loop_n; get resp;
  -- lqt resp; pure decide. By wp_bind + wp_set (mass 1) + wp_uniform (sum
  -- collapse) + tail mass (h_tail_mass), each game has mass 1.
  --
  -- The unfolding via simp_only [wp_bind, wp_set, wp_uniform] should reduce
  -- to a double sum over (x, y) of `h_tail_mass`-applicable expressions.
  -- Then each sum collapses via Finset.sum_const + ENNReal arithmetic.
  -- (Detailed wp-chain assembly still needs care to avoid simp not matching.)
  -- Mass of G_i = 1 — by descent through wp_bind + wp_set/uniform on the prefix,
  -- reducing to h_tail_mass at the deepest level.
  have h_uniform_sum_collapse : ∀ {T : Type} [Fintype T] [Nonempty T] (c : ENNReal),
      (Finset.univ.sum (fun _ : T => c)) / (Fintype.card T : ENNReal) = c := by
    intros T _ _ c
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm,
        mul_div_assoc, ENNReal.div_self
          (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card T ≠ 0))
          (ENNReal.natCast_ne_top _), mul_one]
  -- Define the inner-mass-1 helper that handles set chal_y; tail.
  have h_after_set_chal_y_mass : ∀ (y : output) (σ' : state),
      (Program.set ow_challenge_y y >>= fun _ =>
        (oracle_loop_n ow_adv q lazy_query_tracked) >>= fun _ =>
        Program.get ow_response >>= fun resp =>
        lazy_query_tracked resp >>= fun y_check =>
        (pure (decide (y_check = y)) : Program state Bool)).wp
          (fun _ => (1 : ENNReal)) σ' = 1 := by
    intro y σ'
    rw [wp_bind, wp_set]
    exact h_tail_mass y _
  have h_g2_mass : (ow_game_2_tracked ow_adv q).wp (fun _ => (1 : ENNReal)) σ = 1 := by
    unfold ow_game_2_tracked lazy_init
    apply Program.mass_bind _ _ (fun σ' => Program.set_mass_one _ _ σ')
    intro _ _
    apply Program.mass_bind _ _ (fun σ' => Program.set_mass_one _ _ σ')
    intro _ _
    apply Program.mass_bind _ _ (fun σ' => Program.uniform_mass_one σ')
    intro x _
    apply Program.mass_bind _ _ (fun σ' => Program.set_mass_one _ _ σ')
    intro _ _
    apply Program.mass_bind _ _ (fun σ' => Program.uniform_mass_one σ')
    intro y _
    apply Program.mass_bind _ _ (fun σ' => Program.set_mass_one _ _ σ')
    intro _ σ_6
    exact h_tail_mass y σ_6
  have h_g1_mass : (ow_game_1_tracked ow_adv q).wp (fun _ => (1 : ENNReal)) σ = 1 := by
    unfold ow_game_1_tracked lazy_init
    apply Program.mass_bind _ _ (fun σ' => Program.set_mass_one _ _ σ')
    intro _ _
    apply Program.mass_bind _ _ (fun σ' => Program.set_mass_one _ _ σ')
    intro _ _
    apply Program.mass_bind _ _ (fun σ' => Program.uniform_mass_one σ')
    intro x _
    apply Program.mass_bind _ _ (fun σ' => Program.set_mass_one _ _ σ')
    intro _ _
    apply Program.mass_bind _ _ (fun σ' => Program.uniform_mass_one σ')
    intro y _
    -- G1 has extra `set random_oracle_state ...` step before set chal_y.
    apply Program.mass_bind _ _ (fun σ' => Program.set_mass_one _ _ σ')
    intro _ _
    apply Program.mass_bind _ _ (fun σ' => Program.set_mass_one _ _ σ')
    intro _ σ_7
    exact h_tail_mass y σ_7
  have h_mass_eq : (ow_game_1_tracked ow_adv q).wp (fun _ => 1) σ
                = (ow_game_2_tracked ow_adv q).wp (fun _ => 1) σ := by
    rw [h_g1_mass, h_g2_mass]
  -- Step 4: combine via cancellation.
  rw [h_decompose, h_decompose, h_nonBad_eq] at h_mass_eq
  have h_nb_finite : (ow_game_2_tracked ow_adv q).wp F_nonBad σ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := (1 : ENNReal)) ENNReal.one_ne_top ?_
    refine le_trans ?_ (Program.wp_const_le (ow_game_2_tracked ow_adv q) 1 σ)
    apply Program.wp_le_wp_of_le
    intro bσ
    simp only [F_nonBad_def]
    split_ifs <;> simp
  exact (IsAddRegular.of_ne_top h_nb_finite).1 h_mass_eq

/-! ### Up-to-bad inequality for tracked games

Applying `Program.up_to_bad` with `bad := chal_x_queried_gh.get · = true`
and the identical-until-bad hypothesis from above. -/

theorem ow_game_1_tracked_le_ow_game_2_tracked_plus_bad
    (h_ow_adv_RO : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (q : ℕ) (G : Bool × state → ENNReal)
    (h_G_RO_inv : ∀ (bσ : Bool × state) (y : output),
       G (bσ.1, insert_at_chal_x y bσ.2) = G bσ)
    (σ : state) :
    (ow_game_1_tracked ow_adv q).wp G σ
    ≤ (ow_game_2_tracked ow_adv q).wp G σ
      + (ow_game_1_tracked ow_adv q).wp
          (fun bσ : Bool × state =>
            if chal_x_queried_gh.get bσ.2 = true then G bσ else 0) σ :=
  Program.up_to_bad
    (bad := fun σ' => chal_x_queried_gh.get σ' = true)
    (G := G)
    (h_agree_on_good := fun σ' =>
      ow_game_1_tracked_eq_ow_game_2_tracked_until_bad ow_adv h_ow_adv_RO
        h_ow_adv_chal_x h_ow_adv_chal_x_queried_gh q G h_G_RO_inv σ')
    σ

end UpToBad
