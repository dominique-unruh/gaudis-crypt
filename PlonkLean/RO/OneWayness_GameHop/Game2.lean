import PlonkLean.RO.OneWayness_GameHop.Definitions
import PlonkLean.RO.OneWayness_GameHop.GuessExperiment
import PlonkLean.RO.OneWayness_GameHop.UpToBad

/-!
# OneWayness GameHop: Game 2 reduction

This module reduces Game 2's win event to the abstract `guess_experiment`
framework, ultimately bounding it by `(q+1)/|output|`.

## Game 2 components

* `body_game_2`, `final_game_2` — direct query / response handlers (with
  explicit `if y_val = y then set matched_chal_y true`).
* `env_game_2` — the prefix that samples `y` and tracks the matched flag.
* `body_recording_game_2`, `final_recording_game_2` — recording variants
  that append each response to `queries_output`.
* `q_body_game_2`, `q_final_game_2` — shared query subprograms;
  `body_game_2 = q_body_game_2 >>= match_check_y` and
  `body_recording_game_2 = q_body_game_2 >>= record_to_qs`. This decomposition
  fits the schema directly (no bridges needed).
* `guess_experiment_game_2` — Game 2 as a `guess_experiment` instance.

## Bridges and bound

* `ow_game_2_tracked_wins_le_guess_experiment_game_2_matched` — Game 2's
  win event ≤ guess_experiment_game_2 matched event.
* `ow_game_2_tracked_bad_eq_guess_experiment_game_1` — Game 2's BAD event
  equals guess_experiment_game_1's matched event (used in `UpToBad`).
* `ow_game_2_tracked_wins_le_guess_output_bound` — full bound:
  `Pr[Game 2 wins] ≤ (q+1)/|output|`, by chaining the above into
  `guess_experiment_le_interim_via_schema` and `guess_experiment_interim_wp_bound`.

## Length-bound helpers

`Program.wp_qs_length_preserved_of_inRange`, `loop_n_wp_linear_bound`,
`body_recording_game_2_qs_length_bump`, etc. — used to discharge
`h_qs_length_le` (the `|queries| ≤ q+1` hypothesis of
`guess_experiment_interim_wp_bound`).
-/

section Game2

variable (ow_adv : Program state Unit)

/-- Body of `guess_experiment_game_2`: adv query + explicit match check
    against the bound target `y`. -/
private noncomputable def body_game_2 (y : output) : Program state Unit := do
  ow_adv
  let inp ← Program.get oracle_input
  let y_val ← lazy_query_tracked inp
  Program.set oracle_output y_val
  if y_val = y then Program.set matched_chal_y true else pure ()

/-- Final of `guess_experiment_game_2`: oracle on response + explicit
    match check against the bound target `y`. -/
private noncomputable def final_game_2 (y : output) : Program state Unit := do
  let resp ← Program.get ow_response
  let y_val ← lazy_query_tracked resp
  if y_val = y then Program.set matched_chal_y true else pure ()

/-- Env of `guess_experiment_game_2`: lazy_init + reset chal_x_queried_gh +
    sample chal_x. -/
private noncomputable def env_game_2 : Program state Unit := do
  lazy_init
  Program.set chal_x_queried_gh false
  let x ← Program.uniform
  Program.set ow_challenge_x x

/-- **Game 2 as a `guess_experiment` instance.** The matched flag is
    `matched_chal_y`; the target is the uniformly-sampled `chal_y`. Body
    and final use the BOUND target `y` for explicit match-checks. -/
private noncomputable def guess_experiment_game_2 (q : ℕ) : Program state Bool :=
  guess_experiment env_game_2 Program.uniform ow_challenge_y matched_chal_y
    (body_game_2 ow_adv) (final_game_2) q

private lemma lazy_query_tracked_inRange_matched_chal_y (inp : input) :
    (lazy_query_tracked inp).inRange matched_chal_y.compl.range := by
  unfold lazy_query_tracked
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state matched_chal_y)
  refine Program.inRange_bind ?_ (fun cx => ?_)
  · exact Program.get_inRange_compl_of_disjoint ow_challenge_x matched_chal_y
  refine Program.inRange_bind ?_ (fun _ => Program.inRange_pure _ _)
  by_cases h : inp = cx
  · simp only [if_pos h]
    exact Program.set_inRange_compl_of_disjoint
      chal_x_queried_gh matched_chal_y true
  · simp only [if_neg h]
    exact Program.inRange_pure _ _

/-- `oracle_step adv lazy_query_tracked` is matched_chal_y-disjoint when
    `adv` is. -/
private lemma oracle_step_lazy_query_tracked_inRange_matched_chal_y
    (h_ow_adv_matched_chal_y : ow_adv.inRange matched_chal_y.compl.range) :
    (oracle_step ow_adv lazy_query_tracked).inRange matched_chal_y.compl.range := by
  unfold oracle_step
  refine Program.inRange_bind h_ow_adv_matched_chal_y (fun _ => ?_)
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint oracle_input matched_chal_y) (fun inp => ?_)
  refine Program.inRange_bind (lazy_query_tracked_inRange_matched_chal_y inp)
    (fun y => ?_)
  exact Program.set_inRange_compl_of_disjoint oracle_output matched_chal_y y

-- The chal_y inRange lemmas and loop_n_inRange were moved earlier in the file
-- to be available for the bridge proofs.

/-- **Cond_set invisibility for matched-ignoring posts.** A direct
    `if cond then set matched true else pure ()` is wp-invisible. -/
private lemma cond_set_matched_chal_y_wp_invisible
    (cond : Prop) [Decidable cond] (F : Unit × state → ENNReal)
    (h_F : ∀ aσ : Unit × state,
        F (aσ.1, matched_chal_y.set true aσ.2) = F aσ)
    (σ : state) :
    (if cond then Program.set matched_chal_y true
     else (pure () : Program state Unit)).wp F σ = F ((), σ) := by
  by_cases h : cond
  · rw [if_pos h, wp_set]
    exact h_F ((), σ)
  · rw [if_neg h, wp_pure]

/-- The loop body used by `guess_experiment_game_2`: oracle_step plus a
    bound-variable cond_set on the matched_chal_y flag. Defined as a
    separate program so the kernel sees a single named term rather than a
    deeply-nested lambda expression — keeps inductive proofs tractable. -/
private noncomputable def body_v2 (adv : Program state Unit) (y : output) :
    Program state Unit := do
  adv
  let inp ← Program.get oracle_input
  let y_val ← lazy_query_tracked inp
  Program.set oracle_output y_val
  if y_val = y then Program.set matched_chal_y true else pure ()

/-- **Body-level wp equality for the bound-variable cond_set pattern.**
    `body_v2 ow_adv y` has same wp as plain `oracle_step` for
    matched_chal_y-ignoring posts. -/
private lemma body_v2_wp_eq_oracle_step
    (y : output) (F : Unit × state → ENNReal)
    (h_F : ∀ aσ : Unit × state,
        F (aσ.1, matched_chal_y.set true aσ.2) = F aσ)
    (σ : state) :
    (body_v2 ow_adv y).wp F σ
    = (oracle_step ow_adv lazy_query_tracked).wp F σ := by
  unfold body_v2 oracle_step
  simp only [wp_bind, wp_get, wp_set,
    cond_set_matched_chal_y_wp_invisible _ F h_F]

/-- **Generic loop-level wp equality**: if two bodies have the same wp on
    any matched-ignoring post (provided some matched-disjoint reference
    body's wp is matched-set-invariant on input), then their loops have
    same wp. Abstracted to avoid kernel timeouts from heavy fixed bodies. -/
private lemma loop_n_wp_eq_of_body_eq
    {body_v body_ref : Program state Unit}
    (h_ref_inRange : body_ref.inRange matched_chal_y.compl.range)
    (h_body_eq : ∀ (F : Unit × state → ENNReal),
        (∀ aσ : Unit × state, F (aσ.1, matched_chal_y.set true aσ.2) = F aσ) →
        ∀ σ, body_v.wp F σ = body_ref.wp F σ)
    (n : ℕ)
    (F : Unit × state → ENNReal)
    (h_F : ∀ aσ : Unit × state,
        F (aσ.1, matched_chal_y.set true aσ.2) = F aσ)
    (σ : state) :
    (loop_n n body_v).wp F σ = (loop_n n body_ref).wp F σ := by
  have h_loop_inRange : ∀ k, (loop_n k body_ref).inRange matched_chal_y.compl.range :=
    fun k => loop_n_inRange body_ref h_ref_inRange k
  have h_loop_set_inv : ∀ k σ',
      (loop_n k body_ref).wp F (matched_chal_y.set true σ')
      = (loop_n k body_ref).wp F σ' := by
    intro k σ'
    have hf : (fun s : state => matched_chal_y.set true s) ∈
        ((matched_chal_y.compl.range : LensRange state)ᶜ).updates := by
      rw [show ((matched_chal_y.compl.range : LensRange state)ᶜ)
            = matched_chal_y.range from by
            rw [LensRange.complement_range, LensRange.compl_compl]]
      exact ⟨Function.const _ true, Set.mem_univ _, rfl⟩
    rw [Program.wp_shift_input (h_loop_inRange k) hf]
    congr 1
    funext xs
    exact h_F xs
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    show (body_v >>= fun _ => loop_n n body_v).wp F σ
       = (body_ref >>= fun _ => loop_n n body_ref).wp F σ
    rw [wp_bind]
    conv_rhs => rw [wp_bind]
    have h_post_eq :
        (fun ttσ : Unit × state => (loop_n n body_v).wp F ttσ.2)
        = (fun ttσ : Unit × state => (loop_n n body_ref).wp F ttσ.2) := by
      funext ttσ
      exact ih ttσ.2
    rw [h_post_eq]
    exact h_body_eq _ (fun aσ => h_loop_set_inv n aσ.2) σ

/-- Specialization: `loop_n n (body_v2 ow_adv y)` ≡ `loop_n n oracle_step` on
    matched-ignoring posts. -/
private lemma loop_n_body_v2_wp_eq
    (h_ow_adv_matched_chal_y : ow_adv.inRange matched_chal_y.compl.range)
    (n : ℕ) (y : output)
    (F : Unit × state → ENNReal)
    (h_F : ∀ aσ : Unit × state,
        F (aσ.1, matched_chal_y.set true aσ.2) = F aσ)
    (σ : state) :
    (loop_n n (body_v2 ow_adv y)).wp F σ
    = (loop_n n (oracle_step ow_adv lazy_query_tracked)).wp F σ :=
  loop_n_wp_eq_of_body_eq
    (oracle_step_lazy_query_tracked_inRange_matched_chal_y ow_adv h_ow_adv_matched_chal_y)
    (fun F' h_F' σ' => body_v2_wp_eq_oracle_step ow_adv y F' h_F' σ')
    n F h_F σ

/-- **General matched_chal_y-set invariance of wp.** For any program in
    matched_chal_y.compl.range and any matched-ignoring post, the wp value
    is invariant under matched_chal_y.set on the input state. -/
private lemma wp_matched_chal_y_set_inv {α : Type} {p : Program state α}
    (hp : p.inRange matched_chal_y.compl.range)
    (b : Bool) (F : α × state → ENNReal)
    (h_F : ∀ aσ : α × state, F (aσ.1, matched_chal_y.set b aσ.2) = F aσ)
    (σ : state) :
    p.wp F (matched_chal_y.set b σ) = p.wp F σ := by
  have hf : (fun s : state => matched_chal_y.set b s) ∈
      ((matched_chal_y.compl.range : LensRange state)ᶜ).updates := by
    rw [show ((matched_chal_y.compl.range : LensRange state)ᶜ)
          = matched_chal_y.range from by
          rw [LensRange.complement_range, LensRange.compl_compl]]
    exact ⟨Function.const _ b, Set.mem_univ _, rfl⟩
  rw [Program.wp_shift_input hp hf]
  congr 1
  funext xs
  exact h_F xs

/-- **Direct Game 2 bridge to the guess_experiment framework.**

    Routes around the SubProb-level marginal_eq wall by stating the bridge
    DIRECTLY between `ow_game_2_tracked.win` and `guess_experiment_game_2.matched`.

    Semantic argument: for any execution, if `ow_game_2_tracked` wins
    (final `y_check = y`), then the final match-check in `guess_experiment_game_2`
    fires, setting `matched_chal_y := true`. So
      `P[ow_game_2_tracked wins] ≤ P[guess_experiment_game_2 matched]`.

    Proof pattern attempted: extend the wp_bind_le pattern (from Step B) to
    handle DIFFERENT continuations of the same return type. Helper lemma
    `wp_bind_le_diff_k` lifts comparison through the shared env+sample+set
    prefix. After descending past the prefix, the comparison reduces to
    `(tracked_tail y).wp F_win σ ≤ (guess_tail y).wp F_matched σ`.

    The tail comparison: tracked_tail has `oracle_loop_n + ... + pure decide`,
    guess_tail has `set matched false + loop_n with cond_set + ... + cond_set +
    get matched`. Pointwise on each execution, the win event implies the
    matched event (final iteration's match-check fires when win holds).
    Lean elaboration of full `unfold` is heavy (whnf timeouts) — needs
    careful per-symbol unfolding. Sorry'd. -/
private lemma ow_game_2_tracked_wins_le_guess_experiment_game_2_matched
    (h_ow_adv_matched_chal_y : ow_adv.inRange matched_chal_y.compl.range)
    (q : ℕ) (σ : state) :
    (ow_game_2_tracked ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ (guess_experiment_game_2 ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  have wp_bind_le_diff_k : ∀ {α β : Type} (prog : Program state α)
      (k1 k2 : α → Program state β) (F G : Program.Post state β),
      (∀ aσ : α × state, (k1 aσ.1).wp F aσ.2 ≤ (k2 aσ.1).wp G aσ.2) →
      ∀ σ : state, (prog >>= k1).wp F σ ≤ (prog >>= k2).wp G σ := by
    intro α β prog k1 k2 F G h σ_pre
    rw [wp_bind, wp_bind]
    exact Program.wp_le_wp_of_le _ _ _ h _
  dsimp only [ow_game_2_tracked, guess_experiment_game_2, guess_experiment,
    env_game_2, body_game_2, final_game_2]
  -- Flatten do-notation on both sides so binds match structurally.
  simp only [Program.bind_assoc]
  -- Descend through the shared env+sample+set chal_y prefix.
  apply wp_bind_le_diff_k; rintro ⟨_, σ1⟩  -- lazy_init
  apply wp_bind_le_diff_k; rintro ⟨_, σ2⟩  -- set chal_x_queried_gh false
  apply wp_bind_le_diff_k; rintro ⟨_, σ3⟩  -- uniform x
  apply wp_bind_le_diff_k; rintro ⟨_, σ4⟩  -- set chal_x x
  apply wp_bind_le_diff_k; rintro ⟨y, σ5⟩  -- uniform y (captured)
  apply wp_bind_le_diff_k; rintro ⟨_, σ6⟩  -- set chal_y y
  -- Now y is captured. Peel `set matched_chal_y false` from RHS only.
  conv_rhs => rw [wp_bind, wp_set]
  dsimp only
  -- Convert LHS's oracle_loop_n to loop_n form to match RHS structure.
  rw [oracle_loop_n_eq_loop_n]
  -- LHS now has `loop_n q (oracle_step ...)`. Peel via wp_bind on both sides.
  rw [wp_bind]
  conv_rhs => rw [wp_bind]
  -- Step A: state alignment via matched-set-invariance of LHS's wp.
  have h_loop_oracle_step_inRange :
      (loop_n q (oracle_step ow_adv lazy_query_tracked)).inRange
        matched_chal_y.compl.range :=
    loop_n_inRange (oracle_step ow_adv lazy_query_tracked)
      (oracle_step_lazy_query_tracked_inRange_matched_chal_y ow_adv
        h_ow_adv_matched_chal_y) q
  have hf : (fun s : state => matched_chal_y.set false s) ∈
      ((matched_chal_y.compl.range : LensRange state)ᶜ).updates := by
    rw [show ((matched_chal_y.compl.range : LensRange state)ᶜ)
          = matched_chal_y.range from by
          rw [LensRange.complement_range, LensRange.compl_compl]]
    exact ⟨Function.const _ false, Set.mem_univ _, rfl⟩
  -- Step A: state alignment. LHS's post is matched-ignoring; LHS is
  -- matched-disjoint; so LHS.wp is invariant under matched.set on input.
  have h_rest_LHS_inRange :
      (do
        let resp ← Program.get ow_response
        let y_check ← lazy_query_tracked resp
        pure (decide (y_check = y)) : Program state Bool).inRange
          matched_chal_y.compl.range := by
    refine Program.inRange_bind
      (Program.get_inRange_compl_of_disjoint ow_response matched_chal_y)
      (fun resp => ?_)
    refine Program.inRange_bind (lazy_query_tracked_inRange_matched_chal_y resp)
      (fun y_check => ?_)
    exact Program.inRange_pure _ _
  -- The post fun ttσ => rest_LHS.wp F_win ttσ.2 is matched-ignoring.
  have h_post_LHS_inv : ∀ aσ : Unit × state,
      (do
        let resp ← Program.get ow_response
        let y_check ← lazy_query_tracked resp
        pure (decide (y_check = y)) : Program state Bool).wp
          (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0)
          (matched_chal_y.set false aσ.2)
      = (do
        let resp ← Program.get ow_response
        let y_check ← lazy_query_tracked resp
        pure (decide (y_check = y)) : Program state Bool).wp
          (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) aσ.2 := by
    intro aσ
    exact wp_matched_chal_y_set_inv h_rest_LHS_inRange false _ (fun _ => rfl) aσ.2
  -- Rewrite LHS from "at σ6" to "at matched.set false σ6".
  rw [show (loop_n q (oracle_step ow_adv lazy_query_tracked)).wp _ σ6 =
        (loop_n q (oracle_step ow_adv lazy_query_tracked)).wp _ (matched_chal_y.set false σ6)
        from (wp_matched_chal_y_set_inv h_loop_oracle_step_inRange false _
                (fun aσ => h_post_LHS_inv aσ) σ6).symm]
  -- Step B: body conversion. Convert LHS's oracle_step to body_v2 form.
  -- Need post matched-ignoring for `true` (loop_n_body_v2_wp_eq's h_F shape).
  have h_post_LHS_inv_true : ∀ aσ : Unit × state,
      (do
        let resp ← Program.get ow_response
        let y_check ← lazy_query_tracked resp
        pure (decide (y_check = y)) : Program state Bool).wp
          (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0)
          (matched_chal_y.set true aσ.2)
      = (do
        let resp ← Program.get ow_response
        let y_check ← lazy_query_tracked resp
        pure (decide (y_check = y)) : Program state Bool).wp
          (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) aσ.2 := by
    intro aσ
    exact wp_matched_chal_y_set_inv h_rest_LHS_inRange true _ (fun _ => rfl) aσ.2
  rw [show (loop_n q (oracle_step ow_adv lazy_query_tracked)).wp _
        (matched_chal_y.set false σ6) =
        (loop_n q (body_v2 ow_adv y)).wp _ (matched_chal_y.set false σ6)
        from (loop_n_body_v2_wp_eq ow_adv h_ow_adv_matched_chal_y q y _
                (fun aσ => h_post_LHS_inv_true aσ) (matched_chal_y.set false σ6)).symm]
  -- Step C: both sides now have `loop_n q (body_v2 ow_adv y)` form
  -- (modulo Lean's defeq of body_v2 named vs inline). Apply wp_le_wp_of_le.
  apply Program.wp_le_wp_of_le
  -- Step D: pointwise tail comparison.
  intro aσ
  -- Both tails start with get ow_response + lazy_query_tracked. Same prog,
  -- different continuations + posts. Use wp_bind_le_diff_k.
  apply wp_bind_le_diff_k; rintro ⟨resp, σ_a⟩
  apply wp_bind_le_diff_k; rintro ⟨y_check, σ_b⟩
  -- Now trailing comparison:
  -- LHS: pure (decide (y_check = y)).wp F_win σ_b.
  -- RHS: (if y_check = y then set matched true else pure ()) >>= get matched .wp F_matched σ_b.
  by_cases h : y_check = y
  · -- y_check = y case: LHS = 1, RHS = 1.
    simp only [wp_pure, if_pos h, wp_bind, wp_set, wp_get,
      matched_chal_y.set_get]
    simp [h]
  · -- y_check ≠ y case: LHS = 0, RHS ≥ 0.
    simp only [wp_pure, if_neg h, Program.pure_bind, wp_get]
    split_ifs with h1 h2 <;> simp_all

/-! ### Collector-based per-game instances and reductions

For each game, define `body_recording` and `final_recording` that record
guesses into the appropriate queries list, then assume the per-game
inequality `guess_experiment_game_X ≤ guess_experiment_interim_game_X`
and the length invariant. This closes the chain via:
  Game → guess_experiment → guess_experiment_interim → (n+1)/|T|. -/

/-- Body recording for Game 2 wins: same shape as guess_experiment_game_2.body
    but without the explicit match-check; instead appends `y_val` to qs. -/
private noncomputable def body_recording_game_2 (adv : Program state Unit) :
    Program state Unit := do
  adv
  let inp ← Program.get oracle_input
  let y_val ← lazy_query_tracked inp
  Program.set oracle_output y_val
  let qs ← Program.get queries_output
  Program.set queries_output (qs ++ [y_val])

/-- Final recording for Game 2 wins: the last query attempt records `y_val`. -/
private noncomputable def final_recording_game_2 : Program state Unit := do
  let resp ← Program.get ow_response
  let y_val ← lazy_query_tracked resp
  let qs ← Program.get queries_output
  Program.set queries_output (qs ++ [y_val])

/-! ### Game 2 schema: shared query subprograms for body and body_recording

For the schema-based correspondence, body_game_2 and body_recording_game_2
share a `q_body_game_2` subprogram that returns the `y_val` value. Similarly
for final. -/

/-- The "query" subprogram shared between body_game_2 and body_recording_game_2.
    Returns `y_val` (the lazy_query_tracked output for the adv's query). -/
private noncomputable def q_body_game_2 (ow_adv : Program state Unit) : Program state output := do
  ow_adv
  let inp ← Program.get oracle_input
  let y_val ← lazy_query_tracked inp
  Program.set oracle_output y_val
  pure y_val

/-- The "query" subprogram shared between final_game_2 and final_recording_game_2.
    Returns `y_val` for the response. -/
private noncomputable def q_final_game_2 : Program state output := do
  let resp ← Program.get ow_response
  let y_val ← lazy_query_tracked resp
  pure y_val

/-- Schema equation: body_game_2 follows the schema with q_body_game_2 + match_check. -/
private lemma body_game_2_eq_schema (ow_adv : Program state Unit) (y : output) :
    body_game_2 ow_adv y
    = q_body_game_2 ow_adv >>= fun y_val : output =>
        if y_val = y then Program.set matched_chal_y true
        else (pure () : Program state Unit) := by
  unfold body_game_2 q_body_game_2
  simp only [Program.bind_assoc, Program.pure_bind]

/-- Schema equation: body_recording_game_2 follows the schema with q_body_game_2 + record. -/
private lemma body_recording_game_2_eq_schema (ow_adv : Program state Unit) :
    body_recording_game_2 ow_adv
    = q_body_game_2 ow_adv >>= fun y_val : output =>
        Program.get queries_output >>= fun qs : List output =>
        Program.set queries_output (qs ++ [y_val]) := by
  unfold body_recording_game_2 q_body_game_2
  simp only [Program.bind_assoc, Program.pure_bind]

/-- Schema equation: final_game_2 follows the schema with q_final_game_2 + match_check. -/
private lemma final_game_2_eq_schema (y : output) :
    final_game_2 y
    = q_final_game_2 >>= fun y_val : output =>
        if y_val = y then Program.set matched_chal_y true
        else (pure () : Program state Unit) := by
  unfold final_game_2 q_final_game_2
  simp only [Program.bind_assoc, Program.pure_bind]

/-- Schema equation: final_recording_game_2 follows the schema with q_final_game_2 + record. -/
private lemma final_recording_game_2_eq_schema :
    final_recording_game_2
    = q_final_game_2 >>= fun y_val : output =>
        Program.get queries_output >>= fun qs : List output =>
        Program.set queries_output (qs ++ [y_val]) := by
  unfold final_recording_game_2 q_final_game_2
  simp only [Program.bind_assoc, Program.pure_bind]

/-- `lazy_query_tracked` is queries_output-disjoint. -/
private lemma lazy_query_tracked_inRange_queries_output (inp : input) :
    (lazy_query_tracked inp).inRange queries_output.compl.range := by
  unfold lazy_query_tracked
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state queries_output)
  refine Program.inRange_bind ?_ (fun cx => ?_)
  · exact Program.get_inRange_compl_of_disjoint ow_challenge_x queries_output
  refine Program.inRange_bind ?_ (fun _ => Program.inRange_pure _ _)
  by_cases h : inp = cx
  · simp only [if_pos h]
    exact Program.set_inRange_compl_of_disjoint chal_x_queried_gh queries_output true
  · simp only [if_neg h]
    exact Program.inRange_pure _ _



/-- `q_body_game_2 ow_adv` is matched_chal_y-disjoint when ow_adv is. -/
private lemma q_body_game_2_inRange_matched_chal_y
    (ow_adv : Program state Unit)
    (h_ow_adv : ow_adv.inRange matched_chal_y.compl.range) :
    (q_body_game_2 ow_adv).inRange matched_chal_y.compl.range := by
  unfold q_body_game_2
  refine Program.inRange_bind h_ow_adv (fun _ => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun inp => ?_)
  refine Program.inRange_bind (lazy_query_tracked_inRange_matched_chal_y _) (fun y => ?_)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `q_body_game_2 ow_adv` is queries_output-disjoint when ow_adv is. -/
private lemma q_body_game_2_inRange_queries_output
    (ow_adv : Program state Unit)
    (h_ow_adv : ow_adv.inRange queries_output.compl.range) :
    (q_body_game_2 ow_adv).inRange queries_output.compl.range := by
  unfold q_body_game_2
  refine Program.inRange_bind h_ow_adv (fun _ => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun inp => ?_)
  refine Program.inRange_bind (lazy_query_tracked_inRange_queries_output _) (fun y => ?_)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `q_body_game_2 ow_adv` is ow_challenge_y-disjoint when ow_adv is. -/
private lemma q_body_game_2_inRange_ow_challenge_y
    (ow_adv : Program state Unit)
    (h_ow_adv : ow_adv.inRange ow_challenge_y.compl.range) :
    (q_body_game_2 ow_adv).inRange ow_challenge_y.compl.range := by
  unfold q_body_game_2
  refine Program.inRange_bind h_ow_adv (fun _ => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun inp => ?_)
  refine Program.inRange_bind (lazy_query_tracked_inRange_ow_challenge_y _) (fun y => ?_)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `q_final_game_2` is matched_chal_y-disjoint. -/
private lemma q_final_game_2_inRange_matched_chal_y :
    q_final_game_2.inRange matched_chal_y.compl.range := by
  unfold q_final_game_2
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun resp => ?_)
  refine Program.inRange_bind (lazy_query_tracked_inRange_matched_chal_y _) (fun y => ?_)
  exact Program.inRange_pure _ _

/-- `q_final_game_2` is queries_output-disjoint. -/
private lemma q_final_game_2_inRange_queries_output :
    q_final_game_2.inRange queries_output.compl.range := by
  unfold q_final_game_2
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun resp => ?_)
  refine Program.inRange_bind (lazy_query_tracked_inRange_queries_output _) (fun y => ?_)
  exact Program.inRange_pure _ _

/-- `q_final_game_2` is ow_challenge_y-disjoint. -/
private lemma q_final_game_2_inRange_ow_challenge_y :
    q_final_game_2.inRange ow_challenge_y.compl.range := by
  unfold q_final_game_2
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun resp => ?_)
  refine Program.inRange_bind (lazy_query_tracked_inRange_ow_challenge_y _) (fun y => ?_)
  exact Program.inRange_pure _ _

/-- final_recording_game_2 bumps queries_output.length by at most 1. -/
private lemma final_recording_game_2_qs_length_bump (σ : state) :
    final_recording_game_2.wp
      (fun aσ : Unit × state => ((queries_output.get aσ.2).length : ENNReal)) σ
    ≤ ((queries_output.get σ).length : ENNReal) + 1 := by
  unfold final_recording_game_2
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_bind]
  have h_inner_eq : ∀ (y_val : output) (σ_lqt : state),
      (Program.get queries_output >>= fun qs =>
        Program.set queries_output (qs ++ [y_val])).wp
        (fun aσ : Unit × state => ((queries_output.get aσ.2).length : ENNReal)) σ_lqt
      = ((queries_output.get σ_lqt).length : ENNReal) + 1 := by
    intro y_val σ_lqt
    simp only [wp_bind, wp_set, wp_get]
    simp only [Lens.set_get, List.length_append, List.length_singleton]
    push_cast
    ring
  refine le_trans (Program.wp_le_wp_of_le _ _
      (fun yσ : output × state => ((queries_output.get yσ.2).length : ENNReal) + 1)
      ?_ σ) ?_
  · intro yσ
    exact le_of_eq (h_inner_eq yσ.1 yσ.2)
  rw [Program.wp_add (lazy_query_tracked _)
      (fun yσ : output × state => ((queries_output.get yσ.2).length : ENNReal))
      (fun _ : output × state => (1 : ENNReal))]
  refine add_le_add ?_ ?_
  · exact Program.wp_qs_length_preserved_of_inRange queries_output
      (lazy_query_tracked _) (lazy_query_tracked_inRange_queries_output _) _
  · exact Program.wp_const_le _ _ _

/-- body_recording_game_2 bumps queries_output.length by at most 1 per iteration. -/
private lemma body_recording_game_2_qs_length_bump
    (adv : Program state Unit)
    (h_adv : adv.inRange queries_output.compl.range)
    (σ : state) :
    (body_recording_game_2 adv).wp
      (fun aσ : Unit × state => ((queries_output.get aσ.2).length : ENNReal)) σ
    ≤ ((queries_output.get σ).length : ENNReal) + 1 := by
  unfold body_recording_game_2
  -- Compute the wp by descending step by step.
  -- The final `set queries_output (qs ++ [y_val])` increments length by 1.
  -- All prior steps (adv, get oi, lqt, set oo, get qs) are queries-disjoint
  -- so they preserve queries_output.length.
  rw [wp_bind]
  -- adv.wp (fun aσ => (rest).wp _ aσ.2) σ
  have h_rest_bound : ∀ σ',
      (Program.get oracle_input >>= fun inp =>
        lazy_query_tracked inp >>= fun y_val =>
        Program.set oracle_output y_val >>= fun _ =>
        Program.get queries_output >>= fun qs =>
        Program.set queries_output (qs ++ [y_val])).wp
        (fun aσ : Unit × state => ((queries_output.get aσ.2).length : ENNReal)) σ'
      ≤ ((queries_output.get σ').length : ENNReal) + 1 := by
    intro σ'
    rw [wp_bind, wp_get]
    dsimp only
    rw [wp_bind]
    -- lqt inp .wp (fun (y_val, σ_lqt) => (set oo; get qs; set qs).wp _ σ_lqt) σ'
    -- The inner: (set oo y_val; get qs; set qs (qs ++ [y_val])).wp (qs.length post) σ_lqt
    --   = qs.length σ_lqt + 1
    -- (assuming queries preserved through set oo).
    have h_inner_eq : ∀ (y_val : output) (σ_lqt : state),
        (Program.set oracle_output y_val >>= fun _ =>
          Program.get queries_output >>= fun qs =>
          Program.set queries_output (qs ++ [y_val])).wp
          (fun aσ : Unit × state => ((queries_output.get aσ.2).length : ENNReal)) σ_lqt
        = ((queries_output.get σ_lqt).length : ENNReal) + 1 := by
      intro y_val σ_lqt
      simp only [wp_bind, wp_set, wp_get]
      simp only [Lens.get_of_disjoint_set queries_output oracle_output, Lens.set_get,
        List.length_append, List.length_singleton]
      push_cast
      ring
    refine le_trans (Program.wp_le_wp_of_le _ _
        (fun yσ : output × state => ((queries_output.get yσ.2).length : ENNReal) + 1)
        ?_ σ') ?_
    · intro yσ
      exact le_of_eq (h_inner_eq yσ.1 yσ.2)
    rw [Program.wp_add (lazy_query_tracked _)
        (fun yσ : output × state => ((queries_output.get yσ.2).length : ENNReal))
        (fun _ : output × state => (1 : ENNReal))]
    refine add_le_add ?_ ?_
    · exact Program.wp_qs_length_preserved_of_inRange queries_output
        (lazy_query_tracked _) (lazy_query_tracked_inRange_queries_output _) _
    · exact Program.wp_const_le _ _ _
  -- Apply adv.wp ≤ ... via similar decomposition.
  refine le_trans (Program.wp_le_wp_of_le _ _
      (fun aσ : Unit × state => ((queries_output.get aσ.2).length : ENNReal) + 1)
      ?_ σ) ?_
  · intro aσ
    exact h_rest_bound aσ.2
  rw [Program.wp_add adv
      (fun aσ : Unit × state => ((queries_output.get aσ.2).length : ENNReal))
      (fun _ : Unit × state => (1 : ENNReal))]
  refine add_le_add ?_ ?_
  · exact Program.wp_qs_length_preserved_of_inRange queries_output adv h_adv σ
  · exact Program.wp_const_le _ _ _


/-- Game 2 wins bound: combines the direct bridge with the framework bound.
    Routes via `guess_experiment_game_2` → `interim` → `collector` → bound.
    Uses the schema-based correspondence (no per-game ad-hoc lemma needed). -/
theorem ow_game_2_tracked_wins_le_guess_output_bound
    (h_ow_adv_matched_chal_y : ow_adv.inRange matched_chal_y.compl.range)
    (h_ow_adv_queries : ow_adv.inRange queries_output.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (q : ℕ) (σ : state) :
    (ow_game_2_tracked ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ ((q + 1) : ENNReal) / Fintype.card output := by
  -- Step 1: Game 2 wins ≤ guess_experiment_game_2 matched (proved).
  refine le_trans (ow_game_2_tracked_wins_le_guess_experiment_game_2_matched ow_adv
      h_ow_adv_matched_chal_y q σ) ?_
  -- Step 2: guess_experiment_game_2 ≤ guess_experiment_interim_game_2 via schema.
  unfold guess_experiment_game_2
  refine le_trans (guess_experiment_le_interim_via_schema env_game_2
      ow_challenge_y matched_chal_y queries_output
      (q_body_game_2 ow_adv) q_final_game_2
      (q_body_game_2_inRange_matched_chal_y ow_adv h_ow_adv_matched_chal_y)
      (q_body_game_2_inRange_queries_output ow_adv h_ow_adv_queries)
      (q_body_game_2_inRange_ow_challenge_y ow_adv h_ow_adv_chal_y)
      q_final_game_2_inRange_matched_chal_y
      q_final_game_2_inRange_queries_output
      q_final_game_2_inRange_ow_challenge_y
      (body_game_2 ow_adv) final_game_2
      (body_recording_game_2 ow_adv) final_recording_game_2
      (body_game_2_eq_schema ow_adv) (body_recording_game_2_eq_schema ow_adv)
      final_game_2_eq_schema final_recording_game_2_eq_schema
      q σ) ?_
  -- Step 3: guess_experiment_interim_game_2 ≤ (q+1)/|output|. Generic.
  apply guess_experiment_interim_wp_bound
  -- h_qs_length_le for Game 2.
  intro σ'
  -- Strategy: prog.wp (qs.length / |T|) σ' = |T|⁻¹ * prog.wp qs.length σ'
  --        and prog.wp qs.length σ' ≤ q+1 (via lazy_init + set qs [] + loop bound + final bump).
  have h_post_eq : (fun aσ : Unit × state =>
        ((queries_output.get aσ.2).length : ENNReal) / Fintype.card output)
      = fun aσ : Unit × state => (Fintype.card output : ENNReal)⁻¹ *
            ((queries_output.get aσ.2).length : ENNReal) := by
    funext aσ
    rw [div_eq_mul_inv, mul_comm]
  rw [h_post_eq, Program.wp_const_mul]
  -- Goal: |output|⁻¹ * prog.wp (qs.length post) σ' ≤ (q+1) / |output|.
  rw [show ((q + 1 : ℕ) : ENNReal) / Fintype.card output
        = (Fintype.card output : ENNReal)⁻¹ * ((q + 1 : ℕ) : ENNReal) from by
      rw [div_eq_mul_inv, mul_comm]]
  refine mul_le_mul' (le_refl _) ?_
  -- Goal: prog.wp (qs.length post) σ' ≤ q+1.
  -- Step: lazy_init preserves queries.
  rw [wp_bind]
  refine le_trans (Program.wp_le_wp_of_le _ _
      (fun _ : Unit × state => ((q + 1 : ℕ) : ENNReal)) ?_ σ') ?_
  · intro aσ_lazy
    -- (set qs []; loop; final).wp (qs.length post) aσ_lazy.2 ≤ q+1
    rw [wp_bind, wp_set]
    -- After set qs []: state has qs = []. qs.length = 0.
    -- (loop; final).wp (qs.length post) (queries.set [] aσ_lazy.2)
    -- ≤ loop.wp (qs.length + 1) σ_init = qs.length σ_init + q + 1 = 0 + q + 1 = q+1.
    set σ_init := queries_output.set [] aσ_lazy.2 with σ_init_def
    have h_qs_init : (queries_output.get σ_init).length = 0 := by
      simp [σ_init_def, Lens.set_get]
    rw [wp_bind]
    refine le_trans (Program.wp_le_wp_of_le _ _
        (fun aσ : Unit × state =>
          ((queries_output.get aσ.2).length : ENNReal) + 1) ?_ σ_init) ?_
    · intro aσ_loop
      exact final_recording_game_2_qs_length_bump _
    rw [Program.wp_add (loop_n q (body_recording_game_2 ow_adv))
        (fun aσ : Unit × state => ((queries_output.get aσ.2).length : ENNReal))
        (fun _ : Unit × state => (1 : ENNReal))]
    refine le_trans (add_le_add (loop_n_wp_linear_bound (body_recording_game_2 ow_adv)
        (fun σ => ((queries_output.get σ).length : ENNReal)) 1
        (fun σ_body => body_recording_game_2_qs_length_bump ow_adv h_ow_adv_queries σ_body)
        q σ_init) (Program.wp_const_le _ _ _)) ?_
    rw [h_qs_init]
    push_cast
    ring_nf
    rfl
  · exact Program.wp_const_le _ _ _


end Game2
