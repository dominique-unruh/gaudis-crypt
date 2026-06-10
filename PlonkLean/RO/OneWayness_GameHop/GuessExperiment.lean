import PlonkLean.RO.OneWayness_GameHop.Definitions

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

/-- Run `body` exactly `n` times. Generic bounded loop combinator. -/
noncomputable def loop_n {s : Type} (n : ℕ) (body : Program s Unit) : Program s Unit :=
  match n with
  | 0 => pure ()
  | n + 1 => body >>= fun _ => loop_n n body

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

lemma oracle_loop_n_eq_loop_n
    (adv : Program state Unit) (oracle : input → Program state output) (q : ℕ) :
    oracle_loop_n adv q oracle = loop_n q (oracle_step adv oracle) := by
  induction q with
  | zero => rfl
  | succ n ih =>
    show oracle_step adv oracle >>= (fun _ => oracle_loop_n adv n oracle)
       = oracle_step adv oracle >>= fun _ => loop_n n (oracle_step adv oracle)
    rw [ih]


lemma loop_n_inRange {R : LensRange state}
    (body : Program state Unit) (h_body : body.inRange R) (n : ℕ) :
    (loop_n n body).inRange R := by
  induction n with
  | zero => exact Program.inRange_pure _ _
  | succ n ih =>
    show (body >>= fun _ => loop_n n body).inRange R
    exact Program.inRange_bind h_body (fun _ => ih)

/-- **Loop congruence for the equiv-modulo-lens calculus**: if two bodies
    are `≈_L`-equivalent, so are their loops. Requires the reference body
    `body` to be `L`-disjoint so that `loop_n n body` is also `L`-disjoint
    (needed for the bind congruence in the inductive step). -/
lemma loop_n_congr {γ : Type} [DecidableEq γ] {L : Lens γ state}
    {body body' : Program state Unit}
    (h_body : body.inRange L.compl.range)
    (h_eq : Program.EquivModuloLens L body body')
    (n : ℕ) :
    Program.EquivModuloLens L (loop_n n body) (loop_n n body') := by
  induction n with
  | zero => exact Program.EquivModuloLens.refl _
  | succ n ih =>
    show Program.EquivModuloLens L (body >>= fun _ => loop_n n body)
                                   (body' >>= fun _ => loop_n n body')
    exact Program.EquivModuloLens.bind h_eq (fun _ => ih)
      (fun _ => loop_n_inRange body h_body n)

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

/-- A trailing `get qs >>= set qs (qs ++ [a])` is wp-invisible at
    queries_list-ignoring posts. Generic in `T` and `queries_list_var`. -/
private lemma wp_record_append_invisible
    {T : Type} (queries_list_var : Lens (List T) state) (val : T)
    (F : Unit × state → ENNReal)
    (h_F : IgnoresLens queries_list_var F)
    (σ : state) :
    (Program.get queries_list_var >>= fun qs : List T =>
       Program.set queries_list_var (qs ++ [val])).wp F σ
    = F ((), σ) := by
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_set]
  exact h_F ((), σ) _

/-- The match-check `if a = t then set matched true else pure ()` is
    wp-invisible at matched-ignoring posts. -/
private lemma wp_match_check_matched_invisible
    {T : Type} [DecidableEq T] (matched_var : Lens Bool state)
    (t a : T) (F : Unit × state → ENNReal)
    (h_F : IgnoresLens matched_var F)
    (σ : state) :
    (if a = t then Program.set matched_var true
     else (pure () : Program state Unit)).wp F σ
    = F ((), σ) := by
  by_cases h : a = t
  · simp only [if_pos h, wp_set]
    exact h_F ((), σ) _
  · simp only [if_neg h, wp_pure]

/-- The combined "match_check + record" trailing has a specific wp form:
    it sets matched to (old_matched ∨ (a = t)) and qs to (old_qs ++ [a]).
    For F that's "invariant-respecting" (returns same value on states
    satisfying the invariant), the wp from invariant-respecting input
    gives F applied at an invariant-respecting output state. -/
private lemma match_check_record_wp
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint matched_var queries_list_var]
    (t a : T)
    (F : Unit × state → ENNReal)
    (σ : state) :
    ((if a = t then Program.set matched_var true
      else (pure () : Program state Unit)) >>=
     fun _ : Unit =>
     Program.get queries_list_var >>= fun qs : List T =>
     Program.set queries_list_var (qs ++ [a])).wp F σ
    = F ((), queries_list_var.set
            (queries_list_var.get σ ++ [a])
            (if a = t then matched_var.set true σ else σ)) := by
  haveI : disjoint queries_list_var matched_var := disjoint.symm inferInstance
  by_cases ha : a = t
  · simp only [if_pos ha]
    rw [wp_bind, wp_set, wp_bind, wp_get]
    dsimp only
    rw [wp_set]
    congr 1
    rw [Lens.get_of_disjoint_set queries_list_var matched_var true σ]
  · simp only [if_neg ha]
    rw [wp_bind, wp_pure, wp_bind, wp_get]
    dsimp only
    rw [wp_set]

/-- After running `match_check t a; record a` from a state σ with the invariant
    `matched.get σ = decide (t ∈ qs.get σ)`, the resulting state also satisfies
    the invariant. -/
private lemma match_check_record_preserves_invariant
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint matched_var queries_list_var]
    (t a : T) (σ : state)
    (h_inv : matched_var.get σ = decide (t ∈ queries_list_var.get σ)) :
    matched_var.get
      (queries_list_var.set (queries_list_var.get σ ++ [a])
        (if a = t then matched_var.set true σ else σ))
    = decide (t ∈ queries_list_var.get
      (queries_list_var.set (queries_list_var.get σ ++ [a])
        (if a = t then matched_var.set true σ else σ))) := by
  haveI : disjoint queries_list_var matched_var := disjoint.symm inferInstance
  by_cases ha : a = t
  · simp only [if_pos ha]
    rw [Lens.get_of_disjoint_set matched_var queries_list_var]
    rw [Lens.set_get matched_var]
    rw [Lens.set_get queries_list_var]
    rw [ha]
    symm
    rw [decide_eq_true_iff]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · simp only [if_neg ha]
    rw [Lens.get_of_disjoint_set matched_var queries_list_var]
    rw [Lens.set_get queries_list_var]
    rw [h_inv]
    congr 1
    apply propext
    constructor
    · intro h
      exact List.mem_append_left _ h
    · intro h
      rcases List.mem_append.mp h with h1 | h1
      · exact h1
      · exact absurd (List.mem_singleton.mp h1).symm ha

/-- Generalized body_aug agreement lemma: if F1 and F2 agree on
    invariant-respecting states, then body_aug.wp F1 = body_aug.wp F2 at
    invariant-respecting input. -/
private lemma body_aug_wp_agree_on_invariant
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint matched_var queries_list_var]
    (q_body : Program state T)
    (h_q_body_matched : q_body.inRange matched_var.compl.range)
    (h_q_body_qs : q_body.inRange queries_list_var.compl.range)
    (t : T)
    (F1 F2 : Unit × state → ENNReal)
    (h_agree : ∀ aσ : Unit × state,
      matched_var.get aσ.2 = decide (t ∈ queries_list_var.get aσ.2) →
      F1 aσ = F2 aσ)
    (σ : state)
    (h_inv : matched_var.get σ = decide (t ∈ queries_list_var.get σ)) :
    (q_body >>= fun a : T =>
       (if a = t then Program.set matched_var true
        else (pure () : Program state Unit)) >>=
       fun _ : Unit =>
       Program.get queries_list_var >>= fun qs : List T =>
       Program.set queries_list_var (qs ++ [a])).wp F1 σ
    = (q_body >>= fun a : T =>
       (if a = t then Program.set matched_var true
        else (pure () : Program state Unit)) >>=
       fun _ : Unit =>
       Program.get queries_list_var >>= fun qs : List T =>
       Program.set queries_list_var (qs ++ [a])).wp F2 σ := by
  haveI : disjoint queries_list_var matched_var := disjoint.symm inferInstance
  rw [wp_bind]
  conv_rhs => rw [wp_bind]
  rw [Program.wp_strengthen_lens_preserved matched_var h_q_body_matched _ σ,
      Program.wp_strengthen_lens_preserved queries_list_var h_q_body_qs _ σ]
  conv_rhs =>
    rw [Program.wp_strengthen_lens_preserved matched_var h_q_body_matched _ σ,
        Program.wp_strengthen_lens_preserved queries_list_var h_q_body_qs _ σ]
  congr 1
  funext aσ_q
  obtain ⟨a, σ_q⟩ := aσ_q
  dsimp only
  by_cases hq : queries_list_var.get σ_q = queries_list_var.get σ
  · by_cases hm : matched_var.get σ_q = matched_var.get σ
    · simp only [hq, hm, if_true]
      have h_inv_σ_q : matched_var.get σ_q = decide (t ∈ queries_list_var.get σ_q) := by
        rw [hm, hq]; exact h_inv
      rw [match_check_record_wp matched_var queries_list_var t a _ σ_q]
      rw [match_check_record_wp matched_var queries_list_var t a _ σ_q]
      have h_inv_σ_new :=
        match_check_record_preserves_invariant matched_var queries_list_var t a σ_q h_inv_σ_q
      exact h_agree _ h_inv_σ_new
    · simp only [hm, if_false]
  · simp only [hq, if_false]

/-- Loop version of `body_aug_wp_agree_on_invariant`: the n-fold iteration
    of body_aug also has wp agreeing on invariant-respecting posts when
    starting from an invariant-respecting state. -/
private lemma loop_n_body_aug_wp_agree_on_invariant
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint matched_var queries_list_var]
    (q_body : Program state T)
    (h_q_body_matched : q_body.inRange matched_var.compl.range)
    (h_q_body_qs : q_body.inRange queries_list_var.compl.range)
    (t : T) (n : ℕ) :
    ∀ (F1 F2 : Unit × state → ENNReal),
      (∀ aσ : Unit × state,
        matched_var.get aσ.2 = decide (t ∈ queries_list_var.get aσ.2) →
        F1 aσ = F2 aσ) →
      ∀ (σ : state),
        matched_var.get σ = decide (t ∈ queries_list_var.get σ) →
        (loop_n n (q_body >>= fun a : T =>
           (if a = t then Program.set matched_var true
            else (pure () : Program state Unit)) >>=
           fun _ : Unit =>
           Program.get queries_list_var >>= fun qs : List T =>
           Program.set queries_list_var (qs ++ [a]))).wp F1 σ
        = (loop_n n (q_body >>= fun a : T =>
           (if a = t then Program.set matched_var true
            else (pure () : Program state Unit)) >>=
           fun _ : Unit =>
           Program.get queries_list_var >>= fun qs : List T =>
           Program.set queries_list_var (qs ++ [a]))).wp F2 σ := by
  induction n with
  | zero =>
    intro F1 F2 h_agree σ h_inv
    show (pure () : Program state Unit).wp F1 σ = (pure () : Program state Unit).wp F2 σ
    rw [wp_pure, wp_pure]
    exact h_agree _ h_inv
  | succ n ih =>
    intro F1 F2 h_agree σ h_inv
    -- Use body_aug_wp_agree_on_invariant for the outer body_aug, with the
    -- inner post being (loop_n n body_aug).wp F.
    -- For aσ with invariant: (loop_n n body_aug).wp F1 aσ.2 = (loop_n n body_aug).wp F2 aσ.2 by IH.
    have h_inner_agree : ∀ aσ : Unit × state,
        matched_var.get aσ.2 = decide (t ∈ queries_list_var.get aσ.2) →
        (loop_n n (q_body >>= fun a : T =>
           (if a = t then Program.set matched_var true
            else (pure () : Program state Unit)) >>=
           fun _ : Unit =>
           Program.get queries_list_var >>= fun qs : List T =>
           Program.set queries_list_var (qs ++ [a]))).wp F1 aσ.2
        = (loop_n n (q_body >>= fun a : T =>
           (if a = t then Program.set matched_var true
            else (pure () : Program state Unit)) >>=
           fun _ : Unit =>
           Program.get queries_list_var >>= fun qs : List T =>
           Program.set queries_list_var (qs ++ [a]))).wp F2 aσ.2 := by
      intro aσ' h_inv'
      exact ih F1 F2 h_agree aσ'.2 h_inv'
    -- The succ case: loop_n (n+1) body = body >>= loop_n n body.
    -- wp_bind gives body.wp (post involving loop_n n) σ.
    -- Apply body_aug_wp_agree_on_invariant.
    have h_LHS : (loop_n (n + 1) (q_body >>= fun a : T =>
           (if a = t then Program.set matched_var true
            else (pure () : Program state Unit)) >>=
           fun _ : Unit =>
           Program.get queries_list_var >>= fun qs : List T =>
           Program.set queries_list_var (qs ++ [a]))).wp F1 σ
        = (q_body >>= fun a : T =>
           (if a = t then Program.set matched_var true
            else (pure () : Program state Unit)) >>=
           fun _ : Unit =>
           Program.get queries_list_var >>= fun qs : List T =>
           Program.set queries_list_var (qs ++ [a])).wp
          (fun aσ : Unit × state =>
            (loop_n n (q_body >>= fun a : T =>
              (if a = t then Program.set matched_var true
               else (pure () : Program state Unit)) >>=
              fun _ : Unit =>
              Program.get queries_list_var >>= fun qs : List T =>
              Program.set queries_list_var (qs ++ [a]))).wp F1 aσ.2) σ := by
      show ((q_body >>= fun a : T =>
              (if a = t then Program.set matched_var true
               else (pure () : Program state Unit)) >>=
              fun _ : Unit =>
              Program.get queries_list_var >>= fun qs : List T =>
              Program.set queries_list_var (qs ++ [a])) >>= fun _ : Unit =>
            loop_n n _).wp F1 σ = _
      rw [wp_bind]
    have h_RHS : (loop_n (n + 1) (q_body >>= fun a : T =>
           (if a = t then Program.set matched_var true
            else (pure () : Program state Unit)) >>=
           fun _ : Unit =>
           Program.get queries_list_var >>= fun qs : List T =>
           Program.set queries_list_var (qs ++ [a]))).wp F2 σ
        = (q_body >>= fun a : T =>
           (if a = t then Program.set matched_var true
            else (pure () : Program state Unit)) >>=
           fun _ : Unit =>
           Program.get queries_list_var >>= fun qs : List T =>
           Program.set queries_list_var (qs ++ [a])).wp
          (fun aσ : Unit × state =>
            (loop_n n (q_body >>= fun a : T =>
              (if a = t then Program.set matched_var true
               else (pure () : Program state Unit)) >>=
              fun _ : Unit =>
              Program.get queries_list_var >>= fun qs : List T =>
              Program.set queries_list_var (qs ++ [a]))).wp F2 aσ.2) σ := by
      show ((q_body >>= fun a : T =>
              (if a = t then Program.set matched_var true
               else (pure () : Program state Unit)) >>=
              fun _ : Unit =>
              Program.get queries_list_var >>= fun qs : List T =>
              Program.set queries_list_var (qs ++ [a])) >>= fun _ : Unit =>
            loop_n n _).wp F2 σ = _
      rw [wp_bind]
    rw [h_LHS, h_RHS]
    exact body_aug_wp_agree_on_invariant matched_var queries_list_var
      q_body h_q_body_matched h_q_body_qs t _ _ h_inner_agree σ h_inv
private lemma body_aug_wp_invariant_step
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint matched_var queries_list_var]
    (q_body : Program state T)
    (h_q_body_matched : q_body.inRange matched_var.compl.range)
    (h_q_body_qs : q_body.inRange queries_list_var.compl.range)
    (t : T)
    (F1 : Bool → state → ENNReal)
    (σ : state)
    (h_inv : matched_var.get σ = decide (t ∈ queries_list_var.get σ)) :
    (q_body >>= fun a : T =>
       (if a = t then Program.set matched_var true
        else (pure () : Program state Unit)) >>=
       fun _ : Unit =>
       Program.get queries_list_var >>= fun qs : List T =>
       Program.set queries_list_var (qs ++ [a])).wp
       (fun aσ : Unit × state => F1 (matched_var.get aσ.2) aσ.2) σ
    = (q_body >>= fun a : T =>
       (if a = t then Program.set matched_var true
        else (pure () : Program state Unit)) >>=
       fun _ : Unit =>
       Program.get queries_list_var >>= fun qs : List T =>
       Program.set queries_list_var (qs ++ [a])).wp
       (fun aσ : Unit × state =>
         F1 (decide (t ∈ queries_list_var.get aσ.2)) aσ.2) σ := by
  haveI : disjoint queries_list_var matched_var := disjoint.symm inferInstance
  rw [wp_bind]
  conv_rhs => rw [wp_bind]
  rw [Program.wp_strengthen_lens_preserved matched_var h_q_body_matched _ σ,
      Program.wp_strengthen_lens_preserved queries_list_var h_q_body_qs _ σ]
  conv_rhs =>
    rw [Program.wp_strengthen_lens_preserved matched_var h_q_body_matched _ σ,
        Program.wp_strengthen_lens_preserved queries_list_var h_q_body_qs _ σ]
  congr 1
  funext aσ_q
  obtain ⟨a, σ_q⟩ := aσ_q
  dsimp only
  by_cases hq : queries_list_var.get σ_q = queries_list_var.get σ
  · by_cases hm : matched_var.get σ_q = matched_var.get σ
    · simp only [hq, hm, if_true]
      have h_inv_σ_q : matched_var.get σ_q = decide (t ∈ queries_list_var.get σ_q) := by
        rw [hm, hq]; exact h_inv
      rw [match_check_record_wp matched_var queries_list_var t a _ σ_q]
      rw [match_check_record_wp matched_var queries_list_var t a _ σ_q]
      have h_inv_σ_new :=
        match_check_record_preserves_invariant matched_var queries_list_var t a σ_q h_inv_σ_q
      rw [h_inv_σ_new]
    · simp only [hm, if_false]
  · simp only [hq, if_false]

/-- Augmentation invisibility: `body_match` and `body_aug` (= body_match + record)
    have the same wp at queries_list-ignoring posts. The trailing record is
    invisible. -/
private lemma body_match_eq_body_aug_qs_ignoring
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    (q : Program state T)
    (t : T)
    (F : Unit × state → ENNReal)
    (h_F_qs : IgnoresLens queries_list_var F)
    (σ : state) :
    (q >>= fun a : T =>
       if a = t then Program.set matched_var true
       else (pure () : Program state Unit)).wp F σ
    = (q >>= fun a : T =>
       (if a = t then Program.set matched_var true
        else (pure () : Program state Unit)) >>=
       fun _ : Unit =>
       Program.get queries_list_var >>= fun qs : List T =>
       Program.set queries_list_var (qs ++ [a])).wp F σ := by
  rw [wp_bind]
  conv_rhs => rw [wp_bind]
  congr 1
  funext aσ_q
  obtain ⟨a, σ_q⟩ := aσ_q
  dsimp only
  rw [wp_bind]
  congr 1
  funext aσ'
  exact (wp_record_append_invisible queries_list_var a F h_F_qs aσ'.2).symm

/-- Match-check elision: `body_aug` and `body_rec` (= body_aug without match_check)
    have the same wp at matched-ignoring posts. -/
private lemma body_aug_eq_body_rec_matched_ignoring
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint queries_list_var matched_var]
    (q : Program state T)
    (t : T)
    (F : Unit × state → ENNReal)
    (h_F_matched : IgnoresLens matched_var F)
    (σ : state) :
    (q >>= fun a : T =>
       (if a = t then Program.set matched_var true
        else (pure () : Program state Unit)) >>=
       fun _ : Unit =>
       Program.get queries_list_var >>= fun qs : List T =>
       Program.set queries_list_var (qs ++ [a])).wp F σ
    = (q >>= fun a : T =>
       Program.get queries_list_var >>= fun qs : List T =>
       Program.set queries_list_var (qs ++ [a])).wp F σ := by
  haveI : disjoint matched_var queries_list_var := disjoint.symm inferInstance
  rw [wp_bind]
  conv_rhs => rw [wp_bind]
  congr 1
  funext aσ_q
  obtain ⟨a, σ_q⟩ := aσ_q
  dsimp only
  rw [wp_bind]
  have h_inner_matched_ignoring : IgnoresLens matched_var
      (fun aσ' : Unit × state =>
        (Program.get queries_list_var >>= fun qs : List T =>
         Program.set queries_list_var (qs ++ [a])).wp F aσ'.2) := by
    intro aσ' v
    show (Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])).wp F (matched_var.set v aσ'.2)
        = (Program.get queries_list_var >>= fun qs : List T =>
           Program.set queries_list_var (qs ++ [a])).wp F aσ'.2
    have h_LHS_compute :
        (Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])).wp F (matched_var.set v aσ'.2)
        = F ((), queries_list_var.set (queries_list_var.get aσ'.2 ++ [a])
                  (matched_var.set v aσ'.2)) := by
      rw [wp_bind, wp_get]
      dsimp only
      rw [wp_set]
      rw [Lens.get_of_disjoint_set queries_list_var matched_var v aσ'.2]
    have h_RHS_compute :
        (Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])).wp F aσ'.2
        = F ((), queries_list_var.set (queries_list_var.get aσ'.2 ++ [a]) aσ'.2) := by
      rw [wp_bind, wp_get]
      dsimp only
      rw [wp_set]
    rw [h_LHS_compute, h_RHS_compute]
    have h_swap : queries_list_var.set
          (queries_list_var.get aσ'.2 ++ [a]) (matched_var.set v aσ'.2)
        = matched_var.set v
          (queries_list_var.set (queries_list_var.get aσ'.2 ++ [a]) aσ'.2) :=
      (inferInstance : disjoint queries_list_var matched_var).commute aσ'.2 _ v
    rw [h_swap]
    exact h_F_matched ((),
      queries_list_var.set (queries_list_var.get aσ'.2 ++ [a]) aσ'.2) v
  rw [wp_match_check_matched_invisible matched_var t a _ h_inner_matched_ignoring σ_q]

/-- The invariant lemma extended to include a final iteration: for σ_aligned
    with invariant, the wp of `loop_n n body_aug >>= final_aug` at posts
    agreeing on invariant-respecting states is independent of which post. -/
private lemma loop_final_body_aug_wp_agree_on_invariant
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint matched_var queries_list_var]
    (q_body q_final : Program state T)
    (h_q_body_matched : q_body.inRange matched_var.compl.range)
    (h_q_body_qs : q_body.inRange queries_list_var.compl.range)
    (h_q_final_matched : q_final.inRange matched_var.compl.range)
    (h_q_final_qs : q_final.inRange queries_list_var.compl.range)
    (t : T) (n : ℕ)
    (F1 F2 : Unit × state → ENNReal)
    (h_agree : ∀ aσ : Unit × state,
      matched_var.get aσ.2 = decide (t ∈ queries_list_var.get aσ.2) →
      F1 aσ = F2 aσ)
    (σ : state)
    (h_inv : matched_var.get σ = decide (t ∈ queries_list_var.get σ)) :
    (loop_n n (q_body >>= fun a : T =>
       (if a = t then Program.set matched_var true
        else (pure () : Program state Unit)) >>=
       fun _ : Unit =>
       Program.get queries_list_var >>= fun qs : List T =>
       Program.set queries_list_var (qs ++ [a])) >>= fun _ : Unit =>
     q_final >>= fun a : T =>
       (if a = t then Program.set matched_var true
        else (pure () : Program state Unit)) >>=
       fun _ : Unit =>
       Program.get queries_list_var >>= fun qs : List T =>
       Program.set queries_list_var (qs ++ [a])).wp F1 σ
    = (loop_n n (q_body >>= fun a : T =>
       (if a = t then Program.set matched_var true
        else (pure () : Program state Unit)) >>=
       fun _ : Unit =>
       Program.get queries_list_var >>= fun qs : List T =>
       Program.set queries_list_var (qs ++ [a])) >>= fun _ : Unit =>
     q_final >>= fun a : T =>
       (if a = t then Program.set matched_var true
        else (pure () : Program state Unit)) >>=
       fun _ : Unit =>
       Program.get queries_list_var >>= fun qs : List T =>
       Program.set queries_list_var (qs ++ [a])).wp F2 σ := by
  rw [wp_bind]
  conv_rhs => rw [wp_bind]
  apply loop_n_body_aug_wp_agree_on_invariant matched_var queries_list_var
    q_body h_q_body_matched h_q_body_qs t n
  · intro aσ' h_inv'
    exact body_aug_wp_agree_on_invariant matched_var queries_list_var
      q_final h_q_final_matched h_q_final_qs t F1 F2 h_agree aσ'.2 h_inv'
  · exact h_inv

/-- Body_match → body_aug as EquivModuloLens at queries_list_var. -/
private lemma body_match_equiv_body_aug
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    (q : Program state T) (t : T) :
    Program.EquivModuloLens queries_list_var
      (q >>= fun a : T =>
        if a = t then Program.set matched_var true
        else (pure () : Program state Unit))
      (q >>= fun a : T =>
        (if a = t then Program.set matched_var true
         else (pure () : Program state Unit)) >>=
        fun _ : Unit =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a])) :=
  fun F h_F σ =>
    body_match_eq_body_aug_qs_ignoring matched_var queries_list_var q t F h_F σ

/-- Body_aug → body_rec as EquivModuloLens at matched_var. -/
private lemma body_aug_equiv_body_rec
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint queries_list_var matched_var]
    (q : Program state T) (t : T) :
    Program.EquivModuloLens matched_var
      (q >>= fun a : T =>
        (if a = t then Program.set matched_var true
         else (pure () : Program state Unit)) >>=
        fun _ : Unit =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a]))
      (q >>= fun a : T =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a])) :=
  fun F h_F σ =>
    body_aug_eq_body_rec_matched_ignoring matched_var queries_list_var q t F h_F σ

/-- body_match (= q >>= match_check) is qs-disjoint when q is. -/
private lemma body_match_inRange_qs
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint matched_var queries_list_var]
    (q : Program state T)
    (h_q_qs : q.inRange queries_list_var.compl.range)
    (t : T) :
    (q >>= fun a : T =>
      if a = t then Program.set matched_var true
      else (pure () : Program state Unit)).inRange queries_list_var.compl.range := by
  refine Program.inRange_bind h_q_qs (fun a => ?_)
  by_cases ha : a = t
  · simp only [if_pos ha]
    exact Program.set_inRange_compl_of_disjoint _ _ _
  · simp only [if_neg ha]
    exact Program.inRange_pure _ _

/-- body_rec (= q >>= record) is matched-disjoint when q is and matched ⊥ qs. -/
private lemma body_rec_inRange_matched
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint queries_list_var matched_var]
    (q : Program state T)
    (h_q_matched : q.inRange matched_var.compl.range) :
    (q >>= fun a : T =>
      Program.get queries_list_var >>= fun qs : List T =>
      Program.set queries_list_var (qs ++ [a])).inRange matched_var.compl.range := by
  refine Program.inRange_bind h_q_matched (fun a => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun qs => ?_)
  exact Program.set_inRange_compl_of_disjoint _ _ _

/-- The loop+final body_match ≈ body_aug equivalence (modulo queries_list_var). -/
private lemma loop_final_body_match_equiv_body_aug
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint matched_var queries_list_var]
    (q_body q_final : Program state T)
    (h_q_body_qs : q_body.inRange queries_list_var.compl.range)
    (h_q_final_qs : q_final.inRange queries_list_var.compl.range)
    (t : T) (n : ℕ) :
    Program.EquivModuloLens queries_list_var
      (loop_n n (q_body >>= fun a : T =>
        if a = t then Program.set matched_var true
        else (pure () : Program state Unit)) >>= fun _ : Unit =>
       q_final >>= fun a : T =>
        if a = t then Program.set matched_var true
        else (pure () : Program state Unit))
      (loop_n n (q_body >>= fun a : T =>
        (if a = t then Program.set matched_var true
         else (pure () : Program state Unit)) >>=
        fun _ : Unit =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a])) >>= fun _ : Unit =>
       q_final >>= fun a : T =>
        (if a = t then Program.set matched_var true
         else (pure () : Program state Unit)) >>=
        fun _ : Unit =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a])) := by
  refine Program.EquivModuloLens.bind
    (loop_n_congr (body_match_inRange_qs matched_var queries_list_var q_body h_q_body_qs t)
      (body_match_equiv_body_aug matched_var queries_list_var q_body t) n)
    (fun _ => body_match_equiv_body_aug matched_var queries_list_var q_final t)
    (fun _ => body_match_inRange_qs matched_var queries_list_var q_final h_q_final_qs t)

/-- The loop+final body_aug ≈ body_rec equivalence (modulo matched_var). -/
private lemma loop_final_body_aug_equiv_body_rec
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint queries_list_var matched_var]
    (q_body q_final : Program state T)
    (h_q_body_matched : q_body.inRange matched_var.compl.range)
    (h_q_final_matched : q_final.inRange matched_var.compl.range)
    (t : T) (n : ℕ) :
    Program.EquivModuloLens matched_var
      (loop_n n (q_body >>= fun a : T =>
        (if a = t then Program.set matched_var true
         else (pure () : Program state Unit)) >>=
        fun _ : Unit =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a])) >>= fun _ : Unit =>
       q_final >>= fun a : T =>
        (if a = t then Program.set matched_var true
         else (pure () : Program state Unit)) >>=
        fun _ : Unit =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a]))
      (loop_n n (q_body >>= fun a : T =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a])) >>= fun _ : Unit =>
       q_final >>= fun a : T =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a])) := by
  -- loop_n_congr requires body to be matched-disjoint. body_aug ISN'T (writes matched).
  -- So use body_rec (matched-disjoint) as the in-range body, then symm.
  refine Program.EquivModuloLens.symm ?_
  refine Program.EquivModuloLens.bind
    (loop_n_congr (body_rec_inRange_matched matched_var queries_list_var q_body h_q_body_matched)
      (Program.EquivModuloLens.symm
        (body_aug_equiv_body_rec matched_var queries_list_var q_body t)) n)
    (fun _ => Program.EquivModuloLens.symm
      (body_aug_equiv_body_rec matched_var queries_list_var q_final t))
    (fun _ => body_rec_inRange_matched matched_var queries_list_var q_final h_q_final_matched)

/-- LHS prefix/trailing peel for the schema: peels `set target_var t`,
    `set matched_var false` from the prefix and `>>= get matched_var` from
    the trailing, leaving a canonical `(X >>= Y).wp F_matched σ_inner` form. -/
private lemma guess_experiment_LHS_reduce
    {T : Type}
    (target_var : Lens T state) (matched_var : Lens Bool state)
    (X Y : Program state Unit)
    (t : T) (σ' : state) :
    (Program.set target_var t >>= fun _ =>
     Program.set matched_var false >>= fun _ =>
     X >>= fun _ =>
     Y >>= fun _ =>
     Program.get matched_var).wp
     (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
   = (X >>= fun _ => Y).wp
     (fun aσ : Unit × state => if matched_var.get aσ.2 then (1 : ENNReal) else 0)
     (matched_var.set false (target_var.set t σ')) := by
  rw [wp_bind, wp_set]
  dsimp only
  rw [wp_bind, wp_set]
  dsimp only
  rw [wp_bind]
  conv_rhs => rw [wp_bind]
  congr 1
  funext aσ
  obtain ⟨_, σ_x⟩ := aσ
  dsimp only
  rw [wp_bind]
  congr 1
  funext aσ'
  obtain ⟨_, σ_y⟩ := aσ'
  dsimp only
  rw [wp_get]

/-- RHS prefix/trailing peel for the schema: peels `set queries_list_var []`
    from the prefix and `>>= get qs >>= set matched (decide t ∈ qs) >>= get matched`
    from the trailing, leaving a canonical `(X >>= Y).wp F_decide σ_inner` form. -/
private lemma guess_experiment_RHS_reduce
    {T : Type} [DecidableEq T]
    (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    (X Y : Program state Unit)
    (t : T) (σ' : state) :
    (Program.set queries_list_var [] >>= fun _ =>
     X >>= fun _ =>
     Y >>= fun _ =>
     Program.get queries_list_var >>= fun qs =>
     Program.set matched_var (decide (t ∈ qs)) >>= fun _ =>
     Program.get matched_var).wp
     (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
   = (X >>= fun _ => Y).wp
     (fun aσ : Unit × state =>
       if decide (t ∈ queries_list_var.get aσ.2) then (1 : ENNReal) else 0)
     (queries_list_var.set [] σ') := by
  rw [wp_bind, wp_set]
  dsimp only
  rw [wp_bind]
  conv_rhs => rw [wp_bind]
  congr 1
  funext aσ
  obtain ⟨_, σ_x⟩ := aσ
  dsimp only
  rw [wp_bind]
  congr 1
  funext aσ'
  obtain ⟨_, σ_y⟩ := aσ'
  dsimp only
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_bind, wp_set]
  dsimp only
  rw [wp_get]
  dsimp only
  rw [Lens.set_get matched_var]

set_option maxHeartbeats 1600000 in
/-- **Schema's inner per-σ' equation**: the per-`σ', t` correspondence that
    `guess_experiment_le_interim_via_schema` uses to discharge the
    `h_correspondence` of `guess_experiment_le_interim_assumption`.

    Reusable for other game-level proofs (e.g., `game_1_correspondence`) that
    need the inner equation directly without going through the full schema. -/
lemma schema_inner_equation
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
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
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ' := by
  haveI h_qs_matched : disjoint queries_list_var matched_var := disjoint.symm inferInstance
  haveI h_target_matched_sym : disjoint target_var matched_var := disjoint.symm inferInstance
  haveI h_target_qs_sym : disjoint target_var queries_list_var := disjoint.symm inferInstance
  -- IgnoresLens facts for F_matched and F_decide.
  have hF_matched_qs : IgnoresLens queries_list_var
      (fun aσ : Unit × state => if matched_var.get aσ.2 then (1 : ENNReal) else 0) := by
    intro aσ v
    show (if matched_var.get (queries_list_var.set v aσ.2) then (1 : ENNReal) else 0)
        = if matched_var.get aσ.2 then (1 : ENNReal) else 0
    rw [Lens.get_of_disjoint_set matched_var queries_list_var v aσ.2]
  have hF_decide_matched : IgnoresLens matched_var
      (fun aσ : Unit × state =>
        if decide (t ∈ queries_list_var.get aσ.2) then (1 : ENNReal) else 0) := by
    intro aσ v
    show (if decide (t ∈ queries_list_var.get (matched_var.set v aσ.2)) then (1 : ENNReal) else 0)
        = if decide (t ∈ queries_list_var.get aσ.2) then (1 : ENNReal) else 0
    rw [Lens.get_of_disjoint_set queries_list_var matched_var v aσ.2]
  have hF_decide_target : IgnoresLens target_var
      (fun aσ : Unit × state =>
        if decide (t ∈ queries_list_var.get aσ.2) then (1 : ENNReal) else 0) := by
    intro aσ v
    show (if decide (t ∈ queries_list_var.get (target_var.set v aσ.2)) then (1 : ENNReal) else 0)
        = if decide (t ∈ queries_list_var.get aσ.2) then (1 : ENNReal) else 0
    rw [Lens.get_of_disjoint_set queries_list_var target_var v aσ.2]
  -- Loop+final body_match is qs-disjoint.
  have h_loop_final_match_qs :
      (loop_n n (q_body >>= fun a : T =>
        if a = t then Program.set matched_var true else (pure () : Program state Unit)) >>= fun _ =>
       q_final >>= fun a : T =>
        if a = t then Program.set matched_var true else (pure () : Program state Unit)).inRange
      queries_list_var.compl.range :=
    Program.inRange_bind
      (loop_n_inRange _ (body_match_inRange_qs matched_var queries_list_var q_body h_q_body_qs t) n)
      (fun _ => body_match_inRange_qs matched_var queries_list_var q_final h_q_final_qs t)
  -- Loop+final body_rec is matched-disjoint.
  have h_loop_final_rec_matched :
      (loop_n n (q_body >>= fun a : T =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a])) >>= fun _ =>
       q_final >>= fun a : T =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a])).inRange
      matched_var.compl.range :=
    Program.inRange_bind
      (loop_n_inRange _
        (body_rec_inRange_matched matched_var queries_list_var q_body h_q_body_matched) n)
      (fun _ => body_rec_inRange_matched matched_var queries_list_var q_final h_q_final_matched)
  -- Loop+final body_rec is target-disjoint.
  have h_body_rec_target : ∀ q : Program state T, q.inRange target_var.compl.range →
      (q >>= fun a : T =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a])).inRange target_var.compl.range := by
    intro q h_q
    refine Program.inRange_bind h_q (fun a => ?_)
    refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun qs => ?_)
    exact Program.set_inRange_compl_of_disjoint _ _ _
  have h_loop_final_rec_target :
      (loop_n n (q_body >>= fun a : T =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a])) >>= fun _ =>
       q_final >>= fun a : T =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a])).inRange
      target_var.compl.range :=
    Program.inRange_bind
      (loop_n_inRange _ (h_body_rec_target q_body h_q_body_target) n)
      (fun _ => h_body_rec_target q_final h_q_final_target)
  -- State shorthands.
  set σ_LHS_inner : state := matched_var.set false (target_var.set t σ') with σ_LHS_inner_def
  set σ_RHS_inner : state := queries_list_var.set [] σ' with σ_RHS_inner_def
  set σ_aligned : state := queries_list_var.set [] σ_LHS_inner with σ_aligned_def
  -- Invariant holds at σ_aligned.
  have h_inv_aligned :
      matched_var.get σ_aligned = decide (t ∈ queries_list_var.get σ_aligned) := by
    show matched_var.get (queries_list_var.set [] σ_LHS_inner)
       = decide (t ∈ queries_list_var.get (queries_list_var.set [] σ_LHS_inner))
    rw [Lens.get_of_disjoint_set matched_var queries_list_var, Lens.set_get queries_list_var]
    show matched_var.get (matched_var.set false (target_var.set t σ')) = decide (t ∈ ([] : List T))
    rw [Lens.set_get matched_var]
    simp
  -- σ_aligned equals matched.set false (target.set t σ_RHS_inner) up to lens-commutations.
  have h_σ_aligned_eq :
      σ_aligned = matched_var.set false (target_var.set t σ_RHS_inner) := by
    show queries_list_var.set [] (matched_var.set false (target_var.set t σ'))
       = matched_var.set false (target_var.set t (queries_list_var.set [] σ'))
    rw [(inferInstance : disjoint queries_list_var matched_var).commute]
    rw [(inferInstance : disjoint queries_list_var target_var).commute]
  -- Reduce LHS to canonical form.
  have h_LHS_reduce :
      (Program.set target_var t >>= fun _ =>
       Program.set matched_var false >>= fun _ =>
       loop_n n (q_body >>= fun a : T =>
          if a = t then Program.set matched_var true else (pure () : Program state Unit))
        >>= fun _ =>
       (q_final >>= fun a : T =>
          if a = t then Program.set matched_var true else (pure () : Program state Unit))
        >>= fun _ =>
       Program.get matched_var).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
       =
      (loop_n n (q_body >>= fun a : T =>
          if a = t then Program.set matched_var true else (pure () : Program state Unit))
        >>= fun _ =>
       q_final >>= fun a : T =>
          if a = t then Program.set matched_var true else (pure () : Program state Unit)).wp
       (fun aσ : Unit × state => if matched_var.get aσ.2 then (1 : ENNReal) else 0)
       σ_LHS_inner := by
    exact guess_experiment_LHS_reduce target_var matched_var
      (loop_n n (q_body >>= fun a : T =>
        if a = t then Program.set matched_var true else (pure () : Program state Unit)))
      (q_final >>= fun a : T =>
        if a = t then Program.set matched_var true else (pure () : Program state Unit))
      t σ'
  -- Reduce RHS to canonical form.
  have h_RHS_reduce :
      (Program.set queries_list_var [] >>= fun _ =>
       loop_n n (q_body >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])) >>= fun _ =>
       (q_final >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])) >>= fun _ =>
       Program.get queries_list_var >>= fun qs =>
       Program.set matched_var (decide (t ∈ qs)) >>= fun _ =>
       Program.get matched_var).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
       =
      (loop_n n (q_body >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])) >>= fun _ =>
       q_final >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])).wp
       (fun aσ : Unit × state =>
         if decide (t ∈ queries_list_var.get aσ.2) then (1 : ENNReal) else 0)
       σ_RHS_inner := by
    exact guess_experiment_RHS_reduce matched_var queries_list_var
      (loop_n n (q_body >>= fun a : T =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a])))
      (q_final >>= fun a : T =>
        Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a]))
      t σ'
  rw [h_LHS_reduce, h_RHS_reduce]
  -- Now: (loop+final body_match).wp F_matched σ_LHS_inner = (loop+final body_rec).wp F_decide σ_RHS_inner.
  -- Step 1: shift LHS input qs to [].
  have h_LHS_shift :
      (loop_n n (q_body >>= fun a : T =>
          if a = t then Program.set matched_var true else (pure () : Program state Unit))
        >>= fun _ =>
       q_final >>= fun a : T =>
          if a = t then Program.set matched_var true else (pure () : Program state Unit)).wp
       (fun aσ : Unit × state => if matched_var.get aσ.2 then (1 : ENNReal) else 0)
       σ_LHS_inner
      =
      (loop_n n (q_body >>= fun a : T =>
          if a = t then Program.set matched_var true else (pure () : Program state Unit))
        >>= fun _ =>
       q_final >>= fun a : T =>
          if a = t then Program.set matched_var true else (pure () : Program state Unit)).wp
       (fun aσ : Unit × state => if matched_var.get aσ.2 then (1 : ENNReal) else 0)
       σ_aligned := by
    have hf_in : (fun s' : state => queries_list_var.set [] s') ∈
        ((queries_list_var.compl.range : LensRange state)ᶜ).updates := by
      rw [show ((queries_list_var.compl.range : LensRange state)ᶜ) = queries_list_var.range from by
        rw [LensRange.complement_range, LensRange.compl_compl]]
      exact ⟨Function.const _ [], Set.mem_univ _, rfl⟩
    show _ = (loop_n n _ >>= fun _ => _).wp _ ((fun s' => queries_list_var.set [] s') σ_LHS_inner)
    rw [Program.wp_shift_input h_loop_final_match_qs hf_in]
    congr 1
    funext xs
    exact (hF_matched_qs xs []).symm
  -- Step 2: shift RHS input matched/target.
  have h_RHS_shift :
      (loop_n n (q_body >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])) >>= fun _ =>
       q_final >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])).wp
       (fun aσ : Unit × state =>
         if decide (t ∈ queries_list_var.get aσ.2) then (1 : ENNReal) else 0)
       σ_aligned
      =
      (loop_n n (q_body >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])) >>= fun _ =>
       q_final >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])).wp
       (fun aσ : Unit × state =>
         if decide (t ∈ queries_list_var.get aσ.2) then (1 : ENNReal) else 0)
       σ_RHS_inner := by
    rw [h_σ_aligned_eq]
    -- Shift away matched.set false.
    have hf_matched : (fun s' : state => matched_var.set false s') ∈
        ((matched_var.compl.range : LensRange state)ᶜ).updates := by
      rw [show ((matched_var.compl.range : LensRange state)ᶜ) = matched_var.range from by
        rw [LensRange.complement_range, LensRange.compl_compl]]
      exact ⟨Function.const _ false, Set.mem_univ _, rfl⟩
    have hf_target : (fun s' : state => target_var.set t s') ∈
        ((target_var.compl.range : LensRange state)ᶜ).updates := by
      rw [show ((target_var.compl.range : LensRange state)ᶜ) = target_var.range from by
        rw [LensRange.complement_range, LensRange.compl_compl]]
      exact ⟨Function.const _ t, Set.mem_univ _, rfl⟩
    show (loop_n n _ >>= _).wp _
        ((fun s' => matched_var.set false s') (target_var.set t σ_RHS_inner)) = _
    rw [Program.wp_shift_input h_loop_final_rec_matched hf_matched]
    show (loop_n n _ >>= _).wp _ ((fun s' => target_var.set t s') σ_RHS_inner) = _
    rw [Program.wp_shift_input h_loop_final_rec_target hf_target]
    congr 1
    funext xs
    show (if decide (t ∈ queries_list_var.get (matched_var.set false (target_var.set t xs.2)))
          then (1 : ENNReal) else 0)
       = if decide (t ∈ queries_list_var.get xs.2) then (1 : ENNReal) else 0
    rw [Lens.get_of_disjoint_set queries_list_var matched_var,
        Lens.get_of_disjoint_set queries_list_var target_var]
  rw [h_LHS_shift, ← h_RHS_shift]
  -- Now both sides at σ_aligned. Apply the equivalence chain:
  --   body_match ≈_qs body_aug   (loop_final_body_match_equiv_body_aug)
  --   body_aug agrees w/ body_aug under invariant  (loop_final_body_aug_wp_agree_on_invariant)
  --   body_aug ≈_matched body_rec   (loop_final_body_aug_equiv_body_rec)
  -- Step 3a: match → aug at F_matched (qs-ignoring).
  rw [(loop_final_body_match_equiv_body_aug matched_var queries_list_var q_body q_final
        h_q_body_qs h_q_final_qs t n).wp_eq _ hF_matched_qs σ_aligned]
  -- Step 3b: aug at F_matched = aug at F_decide via invariant.
  rw [loop_final_body_aug_wp_agree_on_invariant matched_var queries_list_var
        q_body q_final h_q_body_matched h_q_body_qs h_q_final_matched h_q_final_qs
        t n _ _ ?_ σ_aligned h_inv_aligned]
  · -- Step 3c: aug → rec at F_decide (matched-ignoring).
    exact ((loop_final_body_aug_equiv_body_rec matched_var queries_list_var q_body q_final
        h_q_body_matched h_q_final_matched t n).wp_eq _ hF_decide_matched σ_aligned)
  -- Sub-goal: F_matched and F_decide agree on invariant-respecting states.
  · intro aσ h_inv
    show (if matched_var.get aσ.2 then (1 : ENNReal) else 0)
       = if decide (t ∈ queries_list_var.get aσ.2) then (1 : ENNReal) else 0
    rw [h_inv]

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

/-- Linear bump bound for `loop_n` with respect to a state-projected potential.
    If body bumps `f` by ≤ c per iter, then `loop_n n body` bumps by ≤ n*c. -/
lemma loop_n_wp_linear_bound
    (body : Program state Unit)
    (f : state → ENNReal) (c : ENNReal)
    (h_body : ∀ σ, body.wp (fun aσ : Unit × state => f aσ.2) σ ≤ f σ + c)
    (n : ℕ) (σ : state) :
    (loop_n n body).wp (fun aσ : Unit × state => f aσ.2) σ
    ≤ f σ + (n : ENNReal) * c := by
  induction n generalizing σ with
  | zero =>
    show (pure () : Program state Unit).wp _ σ ≤ _
    rw [wp_pure]; simp
  | succ n ih =>
    show (body >>= fun _ => loop_n n body).wp _ σ ≤ _
    rw [wp_bind]
    calc body.wp (fun yσ : Unit × state =>
            (loop_n n body).wp
              (fun yσ' : Unit × state => f yσ'.2) yσ.2) σ
        ≤ body.wp (fun yσ : Unit × state => f yσ.2 + (n : ENNReal) * c) σ := by
          apply Program.wp_le_wp_of_le
          intro yσ
          exact ih yσ.2
      _ = body.wp (fun yσ : Unit × state => f yσ.2) σ +
          body.wp (fun _ : Unit × state => (n : ENNReal) * c) σ := by
          rw [Program.wp_add]
      _ ≤ (f σ + c) + (n : ENNReal) * c := by
          gcongr
          · exact h_body σ
          · exact Program.wp_const_le _ _ _
      _ = f σ + ((n + 1 : ℕ) : ENNReal) * c := by
          push_cast; ring

end GuessExperiment
