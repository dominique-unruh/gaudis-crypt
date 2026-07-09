import GaudisCrypt.Lib.RO.OneWayness_GameHop.Definitions
import GaudisCrypt.Lib.RO.OneWayness_GameHop.GuessExperiment
import GaudisCrypt.Lib.RO.OneWayness_GameHop.UpToBad

open GaudisCrypt
open GaudisCrypt

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

`ProgramDenotation.wp_qs_length_preserved_of_inRange`, `loop_n_wp_linear_bound`,
`body_recording_game_2_qs_length_bump`, etc. — used to discharge
`h_qs_length_le` (the `|queries| ≤ q+1` hypothesis of
`guess_experiment_interim_wp_bound`).
-/

section Game2

variable (ow_adv : ProgramDenotation state Unit)

/-- Body of `guess_experiment_game_2`: adv query + explicit match check
    against the bound target `y`. -/
private noncomputable def body_game_2 (y : output) : ProgramDenotation state Unit := do
  ow_adv
  let inp ← ProgramDenotation.get oracle_input
  let y_val ← lazy_query_tracked inp
  ProgramDenotation.set oracle_output y_val
  if y_val = y then ProgramDenotation.set matched_chal_y true else pure ()

/-- Final of `guess_experiment_game_2`: oracle on response + explicit
    match check against the bound target `y`. -/
private noncomputable def final_game_2 (y : output) : ProgramDenotation state Unit := do
  let resp ← ProgramDenotation.get ow_response
  let y_val ← lazy_query_tracked resp
  if y_val = y then ProgramDenotation.set matched_chal_y true else pure ()

/-- Env of `guess_experiment_game_2`: lazy_init + reset chal_x_queried_gh +
    sample chal_x. -/
private noncomputable def env_game_2 : ProgramDenotation state Unit := do
  lazy_init
  ProgramDenotation.set chal_x_queried_gh false
  let x ← ProgramDenotation.uniform
  ProgramDenotation.set ow_challenge_x x

/-- **Game 2 as a `guess_experiment` instance.** The matched flag is
    `matched_chal_y`; the target is the uniformly-sampled `chal_y`. Body
    and final use the BOUND target `y` for explicit match-checks. -/
private noncomputable def guess_experiment_game_2 (q : ℕ) : ProgramDenotation state Bool :=
  guess_experiment env_game_2 ProgramDenotation.uniform ow_challenge_y matched_chal_y
    (body_game_2 ow_adv) (final_game_2) q

private lemma lazy_query_tracked_inRange_matched_chal_y (inp : input) :
    (lazy_query_tracked inp).inRange matched_chal_y.compl.range := by
  unfold lazy_query_tracked
  refine ProgramDenotation.inRange_bind ?_ (fun y => ?_)
  · exact ProgramDenotation.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state matched_chal_y)
  refine ProgramDenotation.inRange_bind ?_ (fun cx => ?_)
  · exact ProgramDenotation.get_inRange_compl_of_disjoint ow_challenge_x matched_chal_y
  refine ProgramDenotation.inRange_bind ?_ (fun _ => ProgramDenotation.inRange_pure _ _)
  by_cases h : inp = cx
  · simp only [if_pos h]
    exact ProgramDenotation.set_inRange_compl_of_disjoint
      chal_x_queried_gh matched_chal_y true
  · simp only [if_neg h]
    exact ProgramDenotation.inRange_pure _ _

/-- `oracle_step adv lazy_query_tracked` is matched_chal_y-disjoint when
    `adv` is. -/
private lemma oracle_step_lazy_query_tracked_inRange_matched_chal_y
    (h_ow_adv_matched_chal_y : ow_adv.inRange matched_chal_y.compl.range) :
    (oracle_step ow_adv lazy_query_tracked).inRange matched_chal_y.compl.range := by
  unfold oracle_step
  refine ProgramDenotation.inRange_bind h_ow_adv_matched_chal_y (fun _ => ?_)
  refine ProgramDenotation.inRange_bind
    (ProgramDenotation.get_inRange_compl_of_disjoint oracle_input matched_chal_y) (fun inp => ?_)
  refine ProgramDenotation.inRange_bind (lazy_query_tracked_inRange_matched_chal_y inp)
    (fun y => ?_)
  exact ProgramDenotation.set_inRange_compl_of_disjoint oracle_output matched_chal_y y

-- The chal_y inRange lemmas and loop_n_inRange were moved earlier in the file
-- to be available for the bridge proofs.

/-! ### The relational bridge: Game 2 wins ≤ guess-experiment matched

The two programs share their entire probabilistic structure (same prefix,
same adversary loop, same final query); the guess experiment additionally
maintains the write-only `matched_chal_y` flag. The coupling invariant is

```
InvM σ₁ σ₂ := ∃ b, σ₂ = matched_chal_y.set b σ₁
```

("the guess-experiment state is the game state with some matched-flag
value on top"), and the final post is `win → matched`: when the game's
verification succeeds (`y_check = y`), the experiment's final match-check
fires. One `rel` judgment (only the `≤` direction is needed) replaces the
former manual seq-descent and its `body_v2`/loop-conversion machinery. -/

/-- Any `matched_chal_y`-disjoint program relates to itself across a
    matched-flag write (same answer, flag carried along). -/
private lemma rel_across_matched {α : Type} {p : ProgramDenotation state α}
    (hp : p.inRange matched_chal_y.compl.range) :
    p.rel p (fun σ₁ σ₂ => ∃ b, σ₂ = matched_chal_y.set b σ₁)
      (fun u v => v.1 = u.1 ∧ ∃ b, v.2 = matched_chal_y.set b u.2) := by
  apply ProgramDenotation.rel.exists_pre
  intro b
  exact ((ProgramDenotation.relE.self_lens_set matched_chal_y hp b).1).conseq
    (fun _ _ h => h) (fun u v h => ⟨h.1, b, h.2⟩)

/-- Leaf: the games' `set oracle_output` vs the experiment's
    `set oracle_output; match-check` preserve the invariant. -/
private lemma set_oo_match_check_rel (y y_val : output) :
    (ProgramDenotation.set oracle_output y_val).rel
      (ProgramDenotation.set oracle_output y_val >>= fun _ =>
        if y_val = y then ProgramDenotation.set matched_chal_y true
        else (pure () : ProgramDenotation state Unit))
      (fun τ₁ τ₂ => ∃ b, τ₂ = matched_chal_y.set b τ₁)
      (fun u v => ∃ b, v.2 = matched_chal_y.set b u.2) := by
  intro F G hFG τ₁ τ₂ hpre
  obtain ⟨b, rfl⟩ := hpre
  rw [wp_set, wp_bind, wp_set]
  dsimp only
  by_cases h : y_val = y
  · rw [if_pos h, wp_set]
    refine hFG _ _ ⟨true, ?_⟩
    rw [disjoint_matched_chal_y_output.symm.commute, matched_chal_y.set_set]
  · rw [if_neg h, wp_pure]
    exact hFG _ _ ⟨b, by rw [disjoint_matched_chal_y_output.symm.commute]⟩

/-- Leaf: the game's verification verdict vs the experiment's final
    match-check + flag read — a win forces the matched flag. -/
private lemma verdict_rel (y y_check : output) :
    (pure (decide (y_check = y)) : ProgramDenotation state Bool).rel
      ((if y_check = y then ProgramDenotation.set matched_chal_y true
        else (pure () : ProgramDenotation state Unit)) >>= fun _ =>
        ProgramDenotation.get matched_chal_y)
      (fun τ₁ τ₂ => ∃ b, τ₂ = matched_chal_y.set b τ₁)
      (fun u v => u.1 = true → v.1 = true) := by
  intro F G hFG τ₁ τ₂ hpre
  obtain ⟨b, rfl⟩ := hpre
  rw [wp_pure]
  by_cases h : y_check = y
  · rw [if_pos h]
    simp only [wp_bind, wp_set, wp_get, Lens.set_get]
    exact hFG _ _ (fun _ => rfl)
  · rw [if_neg h, ProgramDenotation.pure_bind, wp_get]
    exact hFG _ _ (fun hu => absurd (of_decide_eq_true hu) h)

/-- **Loop-body judgment**: one adversary step of the tracked game vs one
    `body_game_2` step of the guess experiment. -/
private lemma body_game_2_rel
    (h_ow_adv_matched_chal_y : ow_adv.inRange matched_chal_y.compl.range)
    (y : output) :
    (oracle_step ow_adv lazy_query_tracked).rel (body_game_2 ow_adv y)
      (fun σ₁ σ₂ => ∃ b, σ₂ = matched_chal_y.set b σ₁)
      (fun u v => ∃ b, v.2 = matched_chal_y.set b u.2) := by
  change (ow_adv >>= fun _ =>
    ProgramDenotation.get oracle_input >>= fun inp =>
    lazy_query_tracked inp >>= fun y_val =>
    ProgramDenotation.set oracle_output y_val).rel
    (ow_adv >>= fun _ =>
    ProgramDenotation.get oracle_input >>= fun inp =>
    lazy_query_tracked inp >>= fun y_val =>
    ProgramDenotation.set oracle_output y_val >>= fun _ =>
    if y_val = y then ProgramDenotation.set matched_chal_y true
    else (pure () : ProgramDenotation state Unit)) _ _
  refine ProgramDenotation.rel.bind
    (Mid := fun u v : Unit × state => ∃ b, v.2 = matched_chal_y.set b u.2)
    ((rel_across_matched h_ow_adv_matched_chal_y).conseq
      (fun _ _ h => h) (fun _ _ h => h.2)) (fun _ _ => ?_)
  refine ProgramDenotation.rel.bind
    (Mid := fun u v : input × state =>
      u.1 = v.1 ∧ ∃ b, v.2 = matched_chal_y.set b u.2)
    (ProgramDenotation.rel.get_get ?_) (fun inp₁ inp₂ => ?_)
  · rintro σ₁ σ₂ ⟨b, rfl⟩
    exact ⟨(Lens.get_of_disjoint_set oracle_input matched_chal_y b σ₁).symm, b, rfl⟩
  · refine ProgramDenotation.rel.bind
      (Mid := fun u v : output × state =>
        u.1 = v.1 ∧ ∃ b, v.2 = matched_chal_y.set b u.2)
      ?_ (fun y₁ y₂ => ?_)
    · intro F G hFG τ₁ τ₂ hpre
      obtain ⟨hval, hb⟩ := hpre
      have hval' : inp₁ = inp₂ := hval
      subst hval'
      exact rel_across_matched (lazy_query_tracked_inRange_matched_chal_y inp₁)
        F G (fun u v h => hFG u v ⟨h.1.symm, h.2⟩) τ₁ τ₂ hb
    · intro F G hFG τ₁ τ₂ hpre
      obtain ⟨hval, hb⟩ := hpre
      have hval' : y₁ = y₂ := hval
      subst hval'
      exact set_oo_match_check_rel y y₁ F G hFG τ₁ τ₂ hb

/-- **Final-segment judgment**: the game's verification vs the
    experiment's final match-check + flag read. -/
private lemma final_game_2_rel (y : output) :
    (ProgramDenotation.get ow_response >>= fun resp =>
      lazy_query_tracked resp >>= fun y_check =>
      (pure (decide (y_check = y)) : ProgramDenotation state Bool)).rel
    (final_game_2 y >>= fun _ => ProgramDenotation.get matched_chal_y)
      (fun σ₁ σ₂ => ∃ b, σ₂ = matched_chal_y.set b σ₁)
      (fun u v => u.1 = true → v.1 = true) := by
  change (ProgramDenotation.get ow_response >>= fun resp =>
      lazy_query_tracked resp >>= fun y_check =>
      (pure (decide (y_check = y)) : ProgramDenotation state Bool)).rel
    ((ProgramDenotation.get ow_response >>= fun resp =>
      lazy_query_tracked resp >>= fun y_val =>
      if y_val = y then ProgramDenotation.set matched_chal_y true
      else (pure () : ProgramDenotation state Unit)) >>= fun _ =>
      ProgramDenotation.get matched_chal_y) _ _
  simp only [ProgramDenotation.bind_assoc]
  refine ProgramDenotation.rel.bind
    (Mid := fun u v : input × state =>
      u.1 = v.1 ∧ ∃ b, v.2 = matched_chal_y.set b u.2)
    (ProgramDenotation.rel.get_get ?_) (fun r₁ r₂ => ?_)
  · rintro σ₁' σ₂' ⟨b, rfl⟩
    exact ⟨(Lens.get_of_disjoint_set ow_response matched_chal_y b σ₁').symm, b, rfl⟩
  · refine ProgramDenotation.rel.bind
      (Mid := fun u v : output × state =>
        u.1 = v.1 ∧ ∃ b, v.2 = matched_chal_y.set b u.2)
      ?_ (fun y₁ y₂ => ?_)
    · intro F' G' hFG' τ₁ τ₂ hpre'
      obtain ⟨hval, hb⟩ := hpre'
      have hval' : r₁ = r₂ := hval
      subst hval'
      exact rel_across_matched (lazy_query_tracked_inRange_matched_chal_y r₁)
        F' G' (fun u v h => hFG' u v ⟨h.1.symm, h.2⟩) τ₁ τ₂ hb
    · intro F' G' hFG' τ₁ τ₂ hpre'
      obtain ⟨hval, hb⟩ := hpre'
      have hval' : y₁ = y₂ := hval
      subst hval'
      exact verdict_rel y y₁ F' G' hFG' τ₁ τ₂ hb

/-- **Game 2 bridge to the guess-experiment framework**, relationally:
    a win in the tracked game forces the matched flag in the experiment. -/
private lemma ow_game_2_tracked_wins_le_guess_experiment_game_2_matched
    (h_ow_adv_matched_chal_y : ow_adv.inRange matched_chal_y.compl.range)
    (q : ℕ) (σ : state) :
    (ow_game_2_tracked ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ (guess_experiment_game_2 ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  have hTail : ∀ y : output,
      (loop_n q (oracle_step ow_adv lazy_query_tracked) >>= fun _ : Unit =>
        ProgramDenotation.get ow_response >>= fun resp =>
        lazy_query_tracked resp >>= fun y_check =>
        (pure (decide (y_check = y)) : ProgramDenotation state Bool)).rel
      (loop_n q (body_game_2 ow_adv y) >>= fun _ : Unit =>
        final_game_2 y >>= fun _ => ProgramDenotation.get matched_chal_y)
      (fun σ₁ σ₂ => ∃ b, σ₂ = matched_chal_y.set b σ₁)
      (fun u v => u.1 = true → v.1 = true) :=
    fun y => ProgramDenotation.rel.bind
      (Mid := fun u v : Unit × state => ∃ b, v.2 = matched_chal_y.set b u.2)
      ((ProgramDenotation.rel.loop_n (Inv := fun σ₁ σ₂ => ∃ b, σ₂ = matched_chal_y.set b σ₁)
        (body_game_2_rel ow_adv h_ow_adv_matched_chal_y y) q).conseq
        (fun _ _ h => h) (fun _ _ h => h))
      (fun _ _ => final_game_2_rel y)
  refine ProgramDenotation.rel.wp_le (Post := fun u v : Bool × state => u.1 = true → v.1 = true)
    ?_ ?_ (rfl : σ = σ)
  · -- the game-level judgment, by peeling the shared prefix
    intro F G hFG σ' σ'' hpre
    cases hpre
    unfold ow_game_2_tracked guess_experiment_game_2 guess_experiment env_game_2
      lazy_init
    rw [oracle_loop_n_eq_loop_n]
    simp only [ProgramDenotation.bind_assoc]
    simp only [ProgramDenotation.wp_set_seq, ProgramDenotation.wp_uniform_seq]
    refine Finset.sum_le_sum fun x _ => ?_
    refine ENNReal.div_le_div_right ?_ _
    refine Finset.sum_le_sum fun y _ => ?_
    refine ENNReal.div_le_div_right ?_ _
    exact hTail y F G hFG _ _ ⟨false, rfl⟩
  · intro u v h
    by_cases hu : u.1 = true
    · rw [if_pos hu, if_pos (h hu)]
    · rw [if_neg hu]
      exact zero_le

/-! ### Collector-based per-game instances and reductions

For each game, define `body_recording` and `final_recording` that record
guesses into the appropriate queries list, then assume the per-game
inequality `guess_experiment_game_X ≤ guess_experiment_interim_game_X`
and the length invariant. This closes the chain via:
  Game → guess_experiment → guess_experiment_interim → (n+1)/|T|. -/

/-- Body recording for Game 2 wins: same shape as guess_experiment_game_2.body
    but without the explicit match-check; instead appends `y_val` to qs. -/
private noncomputable def body_recording_game_2 (adv : ProgramDenotation state Unit) :
    ProgramDenotation state Unit := do
  adv
  let inp ← ProgramDenotation.get oracle_input
  let y_val ← lazy_query_tracked inp
  ProgramDenotation.set oracle_output y_val
  let qs ← ProgramDenotation.get queries_output
  ProgramDenotation.set queries_output (qs ++ [y_val])

/-- Final recording for Game 2 wins: the last query attempt records `y_val`. -/
private noncomputable def final_recording_game_2 : ProgramDenotation state Unit := do
  let resp ← ProgramDenotation.get ow_response
  let y_val ← lazy_query_tracked resp
  let qs ← ProgramDenotation.get queries_output
  ProgramDenotation.set queries_output (qs ++ [y_val])

/-! ### Game 2 schema: shared query subprograms for body and body_recording

For the schema-based correspondence, body_game_2 and body_recording_game_2
share a `q_body_game_2` subprogram that returns the `y_val` value. Similarly
for final. -/

/-- The "query" subprogram shared between body_game_2 and body_recording_game_2.
    Returns `y_val` (the lazy_query_tracked output for the adv's query). -/
private noncomputable def q_body_game_2 (ow_adv : ProgramDenotation state Unit) : ProgramDenotation
    state output := do
  ow_adv
  let inp ← ProgramDenotation.get oracle_input
  let y_val ← lazy_query_tracked inp
  ProgramDenotation.set oracle_output y_val
  pure y_val

/-- The "query" subprogram shared between final_game_2 and final_recording_game_2.
    Returns `y_val` for the response. -/
private noncomputable def q_final_game_2 : ProgramDenotation state output := do
  let resp ← ProgramDenotation.get ow_response
  let y_val ← lazy_query_tracked resp
  pure y_val

/-- Schema equation: body_game_2 follows the schema with q_body_game_2 + match_check. -/
private lemma body_game_2_eq_schema (ow_adv : ProgramDenotation state Unit) (y : output) :
    body_game_2 ow_adv y
    = q_body_game_2 ow_adv >>= fun y_val : output =>
        if y_val = y then ProgramDenotation.set matched_chal_y true
        else (pure () : ProgramDenotation state Unit) := by
  unfold body_game_2 q_body_game_2
  simp only [ProgramDenotation.bind_assoc, ProgramDenotation.pure_bind]

/-- Schema equation: body_recording_game_2 follows the schema with q_body_game_2 + record. -/
private lemma body_recording_game_2_eq_schema (ow_adv : ProgramDenotation state Unit) :
    body_recording_game_2 ow_adv
    = q_body_game_2 ow_adv >>= fun y_val : output =>
        ProgramDenotation.get queries_output >>= fun qs : List output =>
        ProgramDenotation.set queries_output (qs ++ [y_val]) := by
  unfold body_recording_game_2 q_body_game_2
  simp only [ProgramDenotation.bind_assoc, ProgramDenotation.pure_bind]

/-- Schema equation: final_game_2 follows the schema with q_final_game_2 + match_check. -/
private lemma final_game_2_eq_schema (y : output) :
    final_game_2 y
    = q_final_game_2 >>= fun y_val : output =>
        if y_val = y then ProgramDenotation.set matched_chal_y true
        else (pure () : ProgramDenotation state Unit) := by
  unfold final_game_2 q_final_game_2
  simp only [ProgramDenotation.bind_assoc, ProgramDenotation.pure_bind]

/-- Schema equation: final_recording_game_2 follows the schema with q_final_game_2 + record. -/
private lemma final_recording_game_2_eq_schema :
    final_recording_game_2
    = q_final_game_2 >>= fun y_val : output =>
        ProgramDenotation.get queries_output >>= fun qs : List output =>
        ProgramDenotation.set queries_output (qs ++ [y_val]) := by
  unfold final_recording_game_2 q_final_game_2
  simp only [ProgramDenotation.bind_assoc, ProgramDenotation.pure_bind]

/-- `lazy_query_tracked` is queries_output-disjoint. -/
private lemma lazy_query_tracked_inRange_queries_output (inp : input) :
    (lazy_query_tracked inp).inRange queries_output.compl.range := by
  unfold lazy_query_tracked
  refine ProgramDenotation.inRange_bind ?_ (fun y => ?_)
  · exact ProgramDenotation.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state queries_output)
  refine ProgramDenotation.inRange_bind ?_ (fun cx => ?_)
  · exact ProgramDenotation.get_inRange_compl_of_disjoint ow_challenge_x queries_output
  refine ProgramDenotation.inRange_bind ?_ (fun _ => ProgramDenotation.inRange_pure _ _)
  by_cases h : inp = cx
  · simp only [if_pos h]
    exact ProgramDenotation.set_inRange_compl_of_disjoint chal_x_queried_gh queries_output true
  · simp only [if_neg h]
    exact ProgramDenotation.inRange_pure _ _



/-- `q_body_game_2 ow_adv` is matched_chal_y-disjoint when ow_adv is. -/
private lemma q_body_game_2_inRange_matched_chal_y
    (ow_adv : ProgramDenotation state Unit)
    (h_ow_adv : ow_adv.inRange matched_chal_y.compl.range) :
    (q_body_game_2 ow_adv).inRange matched_chal_y.compl.range := by
  unfold q_body_game_2
  refine ProgramDenotation.inRange_bind h_ow_adv (fun _ => ?_)
  refine ProgramDenotation.inRange_bind (ProgramDenotation.get_inRange_compl_of_disjoint _ _) (fun
      inp => ?_)
  refine ProgramDenotation.inRange_bind (lazy_query_tracked_inRange_matched_chal_y _) (fun y => ?_)
  refine ProgramDenotation.inRange_bind (ProgramDenotation.set_inRange_compl_of_disjoint _ _ _) (fun
      _ => ?_)
  exact ProgramDenotation.inRange_pure _ _

/-- `q_body_game_2 ow_adv` is queries_output-disjoint when ow_adv is. -/
private lemma q_body_game_2_inRange_queries_output
    (ow_adv : ProgramDenotation state Unit)
    (h_ow_adv : ow_adv.inRange queries_output.compl.range) :
    (q_body_game_2 ow_adv).inRange queries_output.compl.range := by
  unfold q_body_game_2
  refine ProgramDenotation.inRange_bind h_ow_adv (fun _ => ?_)
  refine ProgramDenotation.inRange_bind (ProgramDenotation.get_inRange_compl_of_disjoint _ _) (fun
      inp => ?_)
  refine ProgramDenotation.inRange_bind (lazy_query_tracked_inRange_queries_output _) (fun y => ?_)
  refine ProgramDenotation.inRange_bind (ProgramDenotation.set_inRange_compl_of_disjoint _ _ _) (fun
      _ => ?_)
  exact ProgramDenotation.inRange_pure _ _

/-- `q_body_game_2 ow_adv` is ow_challenge_y-disjoint when ow_adv is. -/
private lemma q_body_game_2_inRange_ow_challenge_y
    (ow_adv : ProgramDenotation state Unit)
    (h_ow_adv : ow_adv.inRange ow_challenge_y.compl.range) :
    (q_body_game_2 ow_adv).inRange ow_challenge_y.compl.range := by
  unfold q_body_game_2
  refine ProgramDenotation.inRange_bind h_ow_adv (fun _ => ?_)
  refine ProgramDenotation.inRange_bind (ProgramDenotation.get_inRange_compl_of_disjoint _ _) (fun
      inp => ?_)
  refine ProgramDenotation.inRange_bind (lazy_query_tracked_inRange_ow_challenge_y _) (fun y => ?_)
  refine ProgramDenotation.inRange_bind (ProgramDenotation.set_inRange_compl_of_disjoint _ _ _) (fun
      _ => ?_)
  exact ProgramDenotation.inRange_pure _ _

/-- `q_final_game_2` is matched_chal_y-disjoint. -/
private lemma q_final_game_2_inRange_matched_chal_y :
    q_final_game_2.inRange matched_chal_y.compl.range := by
  unfold q_final_game_2
  refine ProgramDenotation.inRange_bind (ProgramDenotation.get_inRange_compl_of_disjoint _ _) (fun
      resp => ?_)
  refine ProgramDenotation.inRange_bind (lazy_query_tracked_inRange_matched_chal_y _) (fun y => ?_)
  exact ProgramDenotation.inRange_pure _ _

/-- `q_final_game_2` is queries_output-disjoint. -/
private lemma q_final_game_2_inRange_queries_output :
    q_final_game_2.inRange queries_output.compl.range := by
  unfold q_final_game_2
  refine ProgramDenotation.inRange_bind (ProgramDenotation.get_inRange_compl_of_disjoint _ _) (fun
      resp => ?_)
  refine ProgramDenotation.inRange_bind (lazy_query_tracked_inRange_queries_output _) (fun y => ?_)
  exact ProgramDenotation.inRange_pure _ _

/-- `q_final_game_2` is ow_challenge_y-disjoint. -/
private lemma q_final_game_2_inRange_ow_challenge_y :
    q_final_game_2.inRange ow_challenge_y.compl.range := by
  unfold q_final_game_2
  refine ProgramDenotation.inRange_bind (ProgramDenotation.get_inRange_compl_of_disjoint _ _) (fun
      resp => ?_)
  refine ProgramDenotation.inRange_bind (lazy_query_tracked_inRange_ow_challenge_y _) (fun y => ?_)
  exact ProgramDenotation.inRange_pure _ _

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
      (ProgramDenotation.get queries_output >>= fun qs =>
        ProgramDenotation.set queries_output (qs ++ [y_val])).wp
        (fun aσ : Unit × state => ((queries_output.get aσ.2).length : ENNReal)) σ_lqt
      = ((queries_output.get σ_lqt).length : ENNReal) + 1 := by
    intro y_val σ_lqt
    simp only [wp_bind, wp_set, wp_get]
    simp only [Lens.set_get, List.length_append, List.length_singleton]
    push_cast
    ring
  refine le_trans (ProgramDenotation.wp_le_wp_of_le _ _
      (fun yσ : output × state => ((queries_output.get yσ.2).length : ENNReal) + 1)
      ?_ σ) ?_
  · intro yσ
    exact le_of_eq (h_inner_eq yσ.1 yσ.2)
  rw [ProgramDenotation.wp_add (lazy_query_tracked _)
      (fun yσ : output × state => ((queries_output.get yσ.2).length : ENNReal))
      (fun _ : output × state => (1 : ENNReal))]
  refine add_le_add ?_ ?_
  · exact ProgramDenotation.wp_qs_length_preserved_of_inRange queries_output
      (lazy_query_tracked _) (lazy_query_tracked_inRange_queries_output _) _
  · exact ProgramDenotation.wp_const_le _ _ _

/-- body_recording_game_2 bumps queries_output.length by at most 1 per iteration. -/
private lemma body_recording_game_2_qs_length_bump
    (adv : ProgramDenotation state Unit)
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
      (ProgramDenotation.get oracle_input >>= fun inp =>
        lazy_query_tracked inp >>= fun y_val =>
        ProgramDenotation.set oracle_output y_val >>= fun _ =>
        ProgramDenotation.get queries_output >>= fun qs =>
        ProgramDenotation.set queries_output (qs ++ [y_val])).wp
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
        (ProgramDenotation.set oracle_output y_val >>= fun _ =>
          ProgramDenotation.get queries_output >>= fun qs =>
          ProgramDenotation.set queries_output (qs ++ [y_val])).wp
          (fun aσ : Unit × state => ((queries_output.get aσ.2).length : ENNReal)) σ_lqt
        = ((queries_output.get σ_lqt).length : ENNReal) + 1 := by
      intro y_val σ_lqt
      simp only [wp_bind, wp_set, wp_get]
      simp only [Lens.get_of_disjoint_set queries_output oracle_output, Lens.set_get,
        List.length_append, List.length_singleton]
      push_cast
      ring
    refine le_trans (ProgramDenotation.wp_le_wp_of_le _ _
        (fun yσ : output × state => ((queries_output.get yσ.2).length : ENNReal) + 1)
        ?_ σ') ?_
    · intro yσ
      exact le_of_eq (h_inner_eq yσ.1 yσ.2)
    rw [ProgramDenotation.wp_add (lazy_query_tracked _)
        (fun yσ : output × state => ((queries_output.get yσ.2).length : ENNReal))
        (fun _ : output × state => (1 : ENNReal))]
    refine add_le_add ?_ ?_
    · exact ProgramDenotation.wp_qs_length_preserved_of_inRange queries_output
        (lazy_query_tracked _) (lazy_query_tracked_inRange_queries_output _) _
    · exact ProgramDenotation.wp_const_le _ _ _
  -- Apply adv.wp ≤ ... via similar decomposition.
  refine le_trans (ProgramDenotation.wp_le_wp_of_le _ _
      (fun aσ : Unit × state => ((queries_output.get aσ.2).length : ENNReal) + 1)
      ?_ σ) ?_
  · intro aσ
    exact h_rest_bound aσ.2
  rw [ProgramDenotation.wp_add adv
      (fun aσ : Unit × state => ((queries_output.get aσ.2).length : ENNReal))
      (fun _ : Unit × state => (1 : ENNReal))]
  refine add_le_add ?_ ?_
  · exact ProgramDenotation.wp_qs_length_preserved_of_inRange queries_output adv h_adv σ
  · exact ProgramDenotation.wp_const_le _ _ _


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
  rw [h_post_eq, ProgramDenotation.wp_const_mul]
  -- Goal: |output|⁻¹ * prog.wp (qs.length post) σ' ≤ (q+1) / |output|.
  rw [show ((q + 1 : ℕ) : ENNReal) / Fintype.card output
        = (Fintype.card output : ENNReal)⁻¹ * ((q + 1 : ℕ) : ENNReal) from by
      rw [div_eq_mul_inv, mul_comm]]
  refine mul_le_mul' (le_refl _) ?_
  -- Goal: prog.wp (qs.length post) σ' ≤ q+1.
  -- Step: lazy_init preserves queries.
  rw [wp_bind]
  refine le_trans (ProgramDenotation.wp_le_wp_of_le _ _
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
    refine le_trans (ProgramDenotation.wp_le_wp_of_le _ _
        (fun aσ : Unit × state =>
          ((queries_output.get aσ.2).length : ENNReal) + 1) ?_ σ_init) ?_
    · intro aσ_loop
      exact final_recording_game_2_qs_length_bump _
    rw [ProgramDenotation.wp_add (loop_n q (body_recording_game_2 ow_adv))
        (fun aσ : Unit × state => ((queries_output.get aσ.2).length : ENNReal))
        (fun _ : Unit × state => (1 : ENNReal))]
    refine le_trans (add_le_add (loop_n_wp_linear_bound (body_recording_game_2 ow_adv)
        (fun σ => ((queries_output.get σ).length : ENNReal)) 1
        (fun σ_body => body_recording_game_2_qs_length_bump ow_adv h_ow_adv_queries σ_body)
        q σ_init) (ProgramDenotation.wp_const_le _ _ _)) ?_
    rw [h_qs_init]
    push_cast
    ring_nf
    rfl
  · exact ProgramDenotation.wp_const_le _ _ _


end Game2
