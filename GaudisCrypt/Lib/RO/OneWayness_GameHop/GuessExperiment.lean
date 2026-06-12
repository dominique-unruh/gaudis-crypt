import GaudisCrypt.Lib.RO.OneWayness_GameHop.Definitions
import GaudisCrypt.Logic.PRHL.Clients.SchemaInnerEquation

/-!
# OneWayness GameHop: Guess Experiment Framework

This module provides the **abstract guessing-game machinery** that abstracts
both the win and bad events in the OW chain. Used by both Game 1's bad-event
reduction and Game 2's win-event reduction.

## Core combinators

* `loop_n n body` — iterate `body` exactly `n` times.
* `guess_experiment env sample tvar mvar body final n` — the abstract guessing
  experiment. Adversary makes `n` queries, then a `final` query; we count
  whether the matched flag fires.
* `guess_experiment_interim` — the same experiment but with a recording list
  collecting all adv queries (sampling happens FIRST).
* `guess_experiment_collector` — equivalent recording form with sampling
  commuted past the recording loop.

## Bounds

* `guess_experiment_collector_wp_bound : (collector).wp post σ ≤ (n+1)/|T|`
  — the heart of the bound, via `uniform_wp_mem_le`.
* `guess_experiment_interim_eq_collector` — interim = collector by
  `Program.bind_uniform_comm` applied 3 times.
* `guess_experiment_interim_wp_bound` — composed bound: interim ≤ (n+1)/|T|.

## Schema (per-game correspondence)

* `guess_experiment_le_interim_assumption` — given a per-σ', t correspondence
  (`h_correspondence`), bounds guess_experiment by guess_experiment_interim.
* `schema_inner_equation` — the per-σ', t equation, proven structurally for any
  body decomposed as `q >>= match_check` and `body_recording` as `q >>= record`.
* `guess_experiment_le_interim_via_schema` — combines the above two: applies
  to any game whose body fits the schema's `q >>= ...` form.

Game 2's body fits directly. Game 1's needs the bridges in `Game1.lean` to
convert to Game 1' form.
-/

section GuessExperiment

/-! ## Generic guessing-game combinators

The framework for cryptographic guess-game reductions. `loop_n` is a
plain bounded loop; `guess_experiment` is the unifying "n+1 attempts to
hit a uniform target" game. -/

-- `loop_n` is defined generically in PlonkLean.ProgramRange.

/-- A generic "guess the uniform target" experiment.

    The key generalization vs prior versions: the `body` and `final`
    iterations are parameterized by the target `t`. Each iteration can
    use the bound target directly in match-checks (no state extracts
    required). This unifies two shapes of match-check that arise in OW:
    * **Input-side match (Game 1 bad):** lazy_query_tracked already
      tracks input matches internally via `chal_x_queried_gh`; the body
      doesn't need an explicit match-check (it ignores its target param).
    * **Output-side match (Game 2 win-bound):** body explicitly does
      `if y_val = t then set matched_var true` using bound `y_val` and `t`.

    Returns the matched flag's final value (Bool). Cryptographic reductions
    relate ow_game_*'s win/bad events to the matched flag via specialized
    bridges. -/
noncomputable def guess_experiment {T s : Type}
    (env : Program s Unit)
    (sample_target : Program s T)
    (target_var : Lens T s)
    (matched_var : Lens Bool s)
    (body : T → Program s Unit)
    (final : T → Program s Unit)
    (n : ℕ) : Program s Bool := do
  env
  let t ← sample_target
  Program.set target_var t
  Program.set matched_var false
  loop_n n (body t)
  final t
  Program.get matched_var



-- `loop_n_inRange` is defined generically in PlonkLean.ProgramRange.
-- `loop_n_congr` and `loop_n_then_congr` are defined generically in PlonkLean.EquivModuloLens.

/-! ### Collector-game route to the bound.

ALTERNATIVE architectural approach: introduce a *collector* version of
`guess_experiment` that:
- Doesn't sample the target during the loop.
- Records each iteration's "comparison value" into a list.
- Samples target uniformly at the END, then checks if it lies in the
  recorded list.

The bound on the collector is then a one-line application of "uniform
sample ∈ finite list of length ≤ n+1 has probability ≤ (n+1)/|T|". The
deferred-sampling content becomes a single equivalence proof
`guess_experiment ≤ guess_experiment_collector`. -/

/-- Collector form of `guess_experiment`. Doesn't take a `target_var`
    parameter — target is sampled uniformly at the end and used only to
    compute the matched flag via `decide (t ∈ queries_list)`. `body` and
    `final` operate without knowledge of the target; they're responsible
    for appending their "comparison values" to `queries_list`. -/
private noncomputable def guess_experiment_collector
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (env : Program state Unit)
    (queries_list_var : Lens (List T) state)
    (matched_var : Lens Bool state)
    (body_recording : Program state Unit)
    (final_recording : Program state Unit)
    (n : ℕ) : Program state Bool := do
  env
  Program.set queries_list_var []
  loop_n n body_recording
  final_recording
  let t ← Program.uniform
  let qs ← Program.get queries_list_var
  Program.set matched_var (decide (t ∈ qs))
  Program.get matched_var

/-- **Interim form of `guess_experiment`**: same as the collector but with the
    target sampled FIRST (like `guess_experiment`) instead of last. -/
noncomputable def guess_experiment_interim
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (env : Program state Unit)
    (queries_list_var : Lens (List T) state)
    (matched_var : Lens Bool state)
    (body_recording : Program state Unit)
    (final_recording : Program state Unit)
    (n : ℕ) : Program state Bool := do
  env
  let t ← Program.uniform
  Program.set queries_list_var []
  loop_n n body_recording
  final_recording
  let qs ← Program.get queries_list_var
  Program.set matched_var (decide (t ∈ qs))
  Program.get matched_var

/-- **Interim = Collector** as programs, by commuting the `uniform` sampling
    past the `t`-independent prefix via `Program.bind_uniform_comm`. -/
private theorem guess_experiment_interim_eq_collector
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (env : Program state Unit)
    (queries_list_var : Lens (List T) state)
    (matched_var : Lens Bool state)
    (body_recording : Program state Unit)
    (final_recording : Program state Unit)
    (n : ℕ) :
    guess_experiment_interim env queries_list_var matched_var
        body_recording final_recording n
    = guess_experiment_collector env queries_list_var matched_var
        body_recording final_recording n := by
  unfold guess_experiment_interim guess_experiment_collector
  congr 1
  funext _
  -- uniform >>= fun t => set qs []; loop; final; ...t...
  -- = set qs []; uniform >>= fun t => loop; final; ...t...
  rw [← Program.bind_uniform_comm]
  congr 1
  funext _
  rw [← Program.bind_uniform_comm]
  congr 1
  funext _
  rw [← Program.bind_uniform_comm]

/-- Pointwise bound: `Program.uniform`'s wp on a list-membership indicator
    is at most `|list|/|T|`. The core trivial fact behind (B).

    Proof: wp_uniform gives ∑_t 1[t ∈ qs] / |T|; ∑_t 1[t ∈ qs] equals
    `(Finset.univ.filter (· ∈ qs)).card = qs.toFinset.card ≤ qs.length`. -/
private lemma uniform_wp_mem_le
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (qs : List T) (σ : state) :
    (Program.uniform : Program state T).wp
        (fun aσ : T × state => if aσ.1 ∈ qs then (1 : ENNReal) else 0) σ
    ≤ (qs.length : ENNReal) / Fintype.card T := by
  simp only [wp_uniform]
  have h_sum_le : ∑ t : T, (if t ∈ qs then (1 : ENNReal) else 0)
                ≤ (qs.length : ENNReal) := by
    calc ∑ t : T, (if t ∈ qs then (1 : ENNReal) else 0)
        = ∑ t ∈ Finset.univ.filter (fun t : T => t ∈ qs), (1 : ENNReal) := by
          rw [← Finset.sum_filter]
      _ = ((Finset.univ.filter (fun t : T => t ∈ qs)).card : ENNReal) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (qs.toFinset.card : ENNReal) := by
          apply Nat.cast_le.mpr
          apply Finset.card_le_card
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
          exact List.mem_toFinset.mpr ht
      _ ≤ (qs.length : ENNReal) := by exact_mod_cast List.toFinset_card_le qs
  calc ∑ t : T, (if t ∈ qs then (1 : ENNReal) else 0) / Fintype.card T
      = (∑ t : T, (if t ∈ qs then (1 : ENNReal) else 0)) * ((Fintype.card T : ENNReal))⁻¹ := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul]
    _ ≤ (qs.length : ENNReal) * ((Fintype.card T : ENNReal))⁻¹ := by
        gcongr
    _ = (qs.length : ENNReal) / Fintype.card T := by
        rw [← div_eq_mul_inv]

/-- **(B): Trivial bound on the collector.**

    After body+final, `queries_list` holds some list `qs` of length ≤ n+1
    (under the length hypothesis). Then `t ~ Uniform[T]` is sampled
    independently. So `P[t ∈ qs] = |qs|/|T| ≤ (n+1)/|T|`. -/
private theorem guess_experiment_collector_wp_bound
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (env : Program state Unit)
    (queries_list_var : Lens (List T) state)
    (matched_var : Lens Bool state)
    [disjoint queries_list_var matched_var]
    (body_recording : Program state Unit)
    (final_recording : Program state Unit)
    (n : ℕ)
    (_h_qs_length_le : ∀ σ : state,
      (env >>= fun _ : Unit =>
        Program.set queries_list_var [] >>= fun _ =>
        loop_n n body_recording >>= fun _ => final_recording).wp
          (fun aσ : Unit × state =>
            ((queries_list_var.get aσ.2).length : ENNReal) / Fintype.card T) σ
      ≤ ((n + 1 : ℕ) : ENNReal) / Fintype.card T)
    (σ : state) :
    (guess_experiment_collector env queries_list_var matched_var
        body_recording final_recording n).wp
      (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ ((n + 1) : ENNReal) / Fintype.card T := by
  dsimp only [guess_experiment_collector]
  have h_inner : ∀ σ' : state,
      ((Program.uniform : Program state T) >>= fun t =>
        Program.get queries_list_var >>= fun qs =>
        Program.set matched_var (decide (t ∈ qs)) >>= fun _ =>
        Program.get matched_var).wp
          (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
      ≤ ((queries_list_var.get σ').length : ENNReal) / Fintype.card T := by
    intro σ'
    rw [wp_bind]
    refine le_trans ?_ (uniform_wp_mem_le (queries_list_var.get σ') σ')
    rw [wp_uniform, wp_uniform]
    apply Finset.sum_le_sum
    intro t _
    simp only [wp_bind, wp_get, wp_set, Lens.set_get, decide_eq_true_eq]
    exact le_refl _
  rw [show ((n : ℕ) : ENNReal) + 1 = ((n + 1 : ℕ) : ENNReal) by push_cast; ring]
  refine le_trans ?_ (_h_qs_length_le σ)
  rw [show (env >>= fun _ : Unit =>
      Program.set queries_list_var [] >>= fun _ =>
      loop_n n body_recording >>= fun _ =>
      final_recording >>= fun _ =>
      Program.uniform >>= fun t =>
      Program.get queries_list_var >>= fun qs =>
      Program.set matched_var (decide (t ∈ qs)) >>= fun _ =>
      Program.get matched_var)
    = (env >>= fun _ : Unit =>
        Program.set queries_list_var [] >>= fun _ =>
        loop_n n body_recording >>= fun _ => final_recording) >>= fun _ =>
        Program.uniform >>= fun t =>
        Program.get queries_list_var >>= fun qs =>
        Program.set matched_var (decide (t ∈ qs)) >>= fun _ =>
        Program.get matched_var from by
      simp [Program.bind_assoc]]
  rw [wp_bind]
  apply Program.wp_le_wp_of_le
  intro aσ
  exact h_inner aσ.2

/-- **Generic bound: `guess_experiment.wp ≤ guess_experiment_interim.wp`** (with
    `sample_target = Program.uniform`).

    The cryptographic content is in `h_correspondence`: a per-state bound
    that the LHS's matched-fire after the loop+final is at most the RHS's
    `t ∈ qs` after recording+final_recording. This bound must be discharged
    at each instantiation — the proof here just peels the common `env` and
    `uniform t` prefix. -/
theorem guess_experiment_le_interim_assumption
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (env : Program state Unit)
    (target_var : Lens T state) (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    (body : T → Program state Unit) (final : T → Program state Unit)
    (body_recording : Program state Unit) (final_recording : Program state Unit)
    (n : ℕ)
    (h_correspondence : ∀ (σ' : state) (t : T),
      (Program.set target_var t >>= fun _ =>
       Program.set matched_var false >>= fun _ =>
       loop_n n (body t) >>= fun _ =>
       final t >>= fun _ =>
       Program.get matched_var).wp
         (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
       ≤
      (Program.set queries_list_var [] >>= fun _ =>
       loop_n n body_recording >>= fun _ =>
       final_recording >>= fun _ =>
       Program.get queries_list_var >>= fun qs =>
       Program.set matched_var (decide (t ∈ qs)) >>= fun _ =>
       Program.get matched_var).wp
         (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ')
    (σ : state) :
    (guess_experiment env Program.uniform target_var matched_var body final n).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ (guess_experiment_interim env queries_list_var matched_var
        body_recording final_recording n).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  -- Both unfold to env >>= fun _ => uniform >>= fun t => (tail t).
  unfold guess_experiment guess_experiment_interim
  conv_lhs => rw [wp_bind]
  conv_rhs => rw [wp_bind]
  apply Program.wp_le_wp_of_le
  intro aσ_env
  conv_lhs => rw [wp_bind, wp_uniform]
  conv_rhs => rw [wp_bind, wp_uniform]
  apply Finset.sum_le_sum
  intro t _
  gcongr
  exact h_correspondence aσ_env.2 t

/-- **Schema's inner per-σ', t equation**: the per-`σ', t` correspondence that
    `guess_experiment_le_interim_via_schema` uses to discharge the
    `h_correspondence` of `guess_experiment_le_interim_assumption`.

    Proved relationally: this is `PRHLSchema.schema_inner_equation_prhl`
    (`PlonkLean/PRHL/Clients/SchemaInnerEquation.lean`), one synchronized
    loop invariant `matched₁ = (t ∈ qs₂)` in the pRHL calculus. The former
    unary proof (~280 lines plus ~700 lines of private support lemmas,
    `maxHeartbeats 1600000`) was removed in favor of it.

    Reusable for other game-level proofs (e.g., `game_1_correspondence`) that
    need the inner equation directly without going through the full schema. -/
lemma schema_inner_equation
    {T : Type} [DecidableEq T]
    (target_var : Lens T state) (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint matched_var queries_list_var]
    [disjoint matched_var target_var]
    [disjoint queries_list_var target_var]
    (q_body q_final : Program state T)
    (h_q_body_matched : q_body.inRange matched_var.compl.range)
    (h_q_body_qs : q_body.inRange queries_list_var.compl.range)
    (h_q_body_target : q_body.inRange target_var.compl.range)
    (h_q_final_matched : q_final.inRange matched_var.compl.range)
    (h_q_final_qs : q_final.inRange queries_list_var.compl.range)
    (h_q_final_target : q_final.inRange target_var.compl.range)
    (n : ℕ) (σ' : state) (t : T) :
    (Program.set target_var t >>= fun _ : Unit =>
     Program.set matched_var false >>= fun _ : Unit =>
     loop_n n (q_body >>= fun a : T =>
        if a = t then Program.set matched_var true else (pure () : Program state Unit))
      >>= fun _ : Unit =>
     (q_final >>= fun a : T =>
        if a = t then Program.set matched_var true else (pure () : Program state Unit))
      >>= fun _ : Unit =>
     Program.get matched_var).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
    = (Program.set queries_list_var [] >>= fun _ : Unit =>
       loop_n n (q_body >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])) >>= fun _ : Unit =>
       (q_final >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])) >>= fun _ : Unit =>
       Program.get queries_list_var >>= fun qs =>
       Program.set matched_var (decide (t ∈ qs)) >>= fun _ : Unit =>
       Program.get matched_var).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ' :=
  PRHLSchema.schema_inner_equation_prhl target_var matched_var queries_list_var
    q_body q_final h_q_body_matched h_q_body_qs h_q_body_target
    h_q_final_matched h_q_final_qs h_q_final_target n σ' t

/-- **Schema-based correspondence**: when body and body_recording both
    decompose as `q >>= ...` for some shared "query" subprogram `q`, with
    body's tail being a match-check against `t` and body_recording's tail
    appending to `queries_list_var`, the per-state correspondence (the
    `h_correspondence` hypothesis of `guess_experiment_le_interim_assumption`)
    is provable structurally via `schema_inner_equation`.

    `q_body` and `q_final` are the shared subprograms for the loop and the
    final iteration respectively. They may differ (e.g., body does adv query
    via oracle_input, final does response check via ow_response). -/
theorem guess_experiment_le_interim_via_schema
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (env : Program state Unit)
    (target_var : Lens T state) (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint matched_var queries_list_var]
    [disjoint matched_var target_var]
    [disjoint queries_list_var target_var]
    (q_body q_final : Program state T)
    (h_q_body_matched : q_body.inRange matched_var.compl.range)
    (h_q_body_qs : q_body.inRange queries_list_var.compl.range)
    (h_q_body_target : q_body.inRange target_var.compl.range)
    (h_q_final_matched : q_final.inRange matched_var.compl.range)
    (h_q_final_qs : q_final.inRange queries_list_var.compl.range)
    (h_q_final_target : q_final.inRange target_var.compl.range)
    (body : T → Program state Unit) (final : T → Program state Unit)
    (body_recording : Program state Unit) (final_recording : Program state Unit)
    (h_body : ∀ t, body t = q_body >>= fun a : T =>
        if a = t then Program.set matched_var true else (pure () : Program state Unit))
    (h_body_recording : body_recording = q_body >>= fun a : T =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a]))
    (h_final : ∀ t, final t = q_final >>= fun a : T =>
        if a = t then Program.set matched_var true else (pure () : Program state Unit))
    (h_final_recording : final_recording = q_final >>= fun a : T =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a]))
    (n : ℕ)
    (σ : state) :
    (guess_experiment env Program.uniform target_var matched_var body final n).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ (guess_experiment_interim env queries_list_var matched_var
        body_recording final_recording n).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  refine guess_experiment_le_interim_assumption env target_var matched_var
    queries_list_var body final body_recording final_recording n ?_ σ
  intro σ' t
  rw [h_body t, h_final t, h_body_recording, h_final_recording]
  refine le_of_eq ?_
  exact schema_inner_equation target_var matched_var queries_list_var
    q_body q_final h_q_body_matched h_q_body_qs h_q_body_target
    h_q_final_matched h_q_final_qs h_q_final_target n σ' t

/-- **Interim wp bound**: by `interim = collector` + collector bound. Generic. -/
theorem guess_experiment_interim_wp_bound
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (env : Program state Unit)
    (queries_list_var : Lens (List T) state)
    (matched_var : Lens Bool state)
    [disjoint queries_list_var matched_var]
    (body_recording : Program state Unit)
    (final_recording : Program state Unit)
    (n : ℕ)
    (h_qs_length_le : ∀ σ : state,
      (env >>= fun _ : Unit =>
        Program.set queries_list_var [] >>= fun _ =>
        loop_n n body_recording >>= fun _ => final_recording).wp
          (fun aσ : Unit × state =>
            ((queries_list_var.get aσ.2).length : ENNReal) / Fintype.card T) σ
      ≤ ((n + 1 : ℕ) : ENNReal) / Fintype.card T)
    (σ : state) :
    (guess_experiment_interim env queries_list_var matched_var
        body_recording final_recording n).wp
      (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ ((n + 1) : ENNReal) / Fintype.card T := by
  rw [guess_experiment_interim_eq_collector]
  exact guess_experiment_collector_wp_bound env queries_list_var matched_var
    body_recording final_recording n h_qs_length_le σ

/-! ### Helpers for length-bound proofs -/

/-- For a program `p` that doesn't write to `qs_var`, the expected list
    length at output is bounded by the initial length (up to mass ≤ 1). -/
lemma Program.wp_qs_length_preserved_of_inRange
    {T : Type} [DecidableEq T]
    (qs_var : Lens (List T) state) {α : Type} (p : Program state α)
    (h_p : p.inRange qs_var.compl.range) (σ : state) :
    p.wp (fun aσ : α × state => ((qs_var.get aσ.2).length : ENNReal)) σ
    ≤ ((qs_var.get σ).length : ENNReal) := by
  rw [Program.wp_strengthen_lens_preserved qs_var h_p]
  refine le_trans (Program.wp_le_wp_of_le _ _
      (fun _ : α × state => ((qs_var.get σ).length : ENNReal)) ?_ σ) ?_
  · intro aσ
    by_cases h : qs_var.get aσ.2 = qs_var.get σ
    · simp [h]
    · simp [h]
  · exact Program.wp_const_le _ _ _

-- `loop_n_wp_linear_bound` is defined generically in PlonkLean.ProgramRange.

end GuessExperiment
