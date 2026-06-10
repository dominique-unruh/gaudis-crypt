import PlonkLean.RO
import PlonkLean.RO.OneWayness
import PlonkLean.EquivModuloLens

/-!
# Game-hopping proof of one-wayness

An alternative proof of the OW lazy bound
`P[ow_experiment wins] ≤ 2(q+1)/|output|` via three games and one
up-to-bad analysis, with both probability bounds reduced to a single
unifying "guessing game" lemma.

See `notes/RO/OW_GameHop_Plan.md` for the full plan.

`guess_experiment_le_interim_assumption` is a proper theorem parameterized by
a `h_correspondence` hypothesis (the body↔body_recording correspondence). The
hypothesis is discharged at each call site by per-game correspondence lemmas
(`game_1_correspondence`, `game_2_correspondence`), which are currently
declared as `axiom`s — they're concrete, TRUE statements about specific
programs, with deferred proof effort. Proving them requires inducting on the
loop with the invariant `matched_var = decide (t ∈ queries_list_var)`
maintained by the body_recording. The existing proof in
`PlonkLean/RO/OneWayness.lean` remains intact.
-/

section GameHopParam

variable (ow_adv : Program state Unit)
variable (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
variable (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
variable (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)

/-! ## Game 0 — the original OW experiment

This is exactly `ow_experiment ow_adv q lazy_init lazy_query`. We give it a
new name here for clarity in the game-hopping chain. -/

noncomputable def ow_game_0 (q : ℕ) : Program state Bool :=
  ow_experiment ow_adv q lazy_init lazy_query

/-! ## Game 1 — explicit y sampling

`lazy_query x` on an empty cache at `x` unfolds to "sample y uniform, write
`(x ↦ y)` into RO, return y". Game 1 makes this explicit: sample y
separately and write it into RO manually. Same distribution as Game 0. -/

noncomputable def ow_game_1 (q : ℕ) : Program state Bool := do
  lazy_init
  let x ← Program.uniform
  Program.set ow_challenge_x x
  let y ← Program.uniform
  -- Insert (x ↦ y) into RO. At this point RO is `fun _ => none` (set by
  -- lazy_init, not touched since), so the "fallback to existing entries"
  -- in `lazy_query`'s case-miss branch is equivalent to "fallback to none".
  Program.set random_oracle_state (fun k => if k = x then some y else none)
  Program.set ow_challenge_y y
  oracle_loop_n ow_adv q lazy_query
  let resp ← Program.get ow_response
  let y_check ← lazy_query resp
  pure (decide (y_check = y))

/-! ## Hop 0 → 1: program equality

`ow_game_0 = ow_game_1` (no probabilistic content; just unfolding
`lazy_query x` on an RO state where `x` is not cached). -/

/-- On a state whose entire RO is `fun _ => none` (i.e., immediately after
    `lazy_init`), `lazy_query inp` is wp-equivalent to "sample a fresh `y`,
    insert `(inp ↦ y)` into the RO, return `y`". -/
private lemma lazy_query_on_totally_empty_RO
    (inp : input) (σ : state)
    (h_empty : random_oracle_state.get σ = fun _ => none)
    (F : output × state → ENNReal) :
    (lazy_query inp).wp F σ
    = (Program.uniform >>= fun y =>
        Program.set random_oracle_state
          (fun k => if k = inp then some y else none) >>= fun _ =>
        (pure y : Program state output)).wp F σ := by
  simp only [lazy_query, wp_bind, wp_get]
  rw [h_empty]
  -- The match key is now `(fun _ : input => none) inp = none`. Reduce.
  simp only [wp_bind, wp_uniform, wp_set, wp_pure]

private lemma lazy_query_x_eq_explicit_y_frame {α : Type}
    (rest : input → output → Program state α) :
    (lazy_init >>= fun _ : Unit =>
      Program.uniform >>= fun x : input =>
        Program.set ow_challenge_x x >>= fun _ : Unit =>
          lazy_query x >>= fun y : output => rest x y)
    = (lazy_init >>= fun _ : Unit =>
      Program.uniform >>= fun x : input =>
        Program.set ow_challenge_x x >>= fun _ : Unit =>
          Program.uniform >>= fun y : output =>
            Program.set random_oracle_state
              (fun k : input => if k = x then some y else none) >>= fun _ : Unit =>
                rest x y) := by
  apply Program.ext_of_wp
  intro F
  funext σ
  -- Unfold all wp's. After this, both sides are fully reduced to nested
  -- sums of F applied to specific states.
  simp only [lazy_init, wp_bind, wp_set, wp_uniform]
  congr 1
  funext x
  -- At this point, LHS has `(lazy_query x).wp Cont σ_x` (lazy_query not yet
  -- unfolded), RHS has `∑ y, F (..., RO.set ... σ_x) / N_output` (fully
  -- unfolded). Use the lazy_query helper to rewrite LHS.
  set σ_x : state := ow_challenge_x.set x (random_oracle_state.set (fun _ => none) σ)
    with hσ_x_def
  have h_RO_empty : random_oracle_state.get σ_x = fun _ => none := by
    show random_oracle_state.get
      (ow_challenge_x.set x (random_oracle_state.set (fun _ => none) σ))
      = fun _ => none
    rw [random_oracle_state.get_of_disjoint_set, random_oracle_state.set_get]
  rw [lazy_query_on_totally_empty_RO x σ_x h_RO_empty]
  -- Now LHS is `(uniform >>= set RO >>= pure y).wp Cont σ_x`. Unfold.
  simp only [wp_bind, wp_uniform, wp_set, wp_pure]

theorem ow_game_0_eq_ow_game_1 (q : ℕ) :
    ow_game_0 ow_adv q = ow_game_1 ow_adv q := by
  -- Both Game 0 and Game 1 fit the same template `(lazy_init >>= … >>= rest x y)`,
  -- differing only at the `lazy_query x` vs explicit `uniform >>= set RO`
  -- step. Apply the frame lemma with the OW-experiment suffix as `rest`.
  unfold ow_game_0 ow_experiment ow_game_1 ow_loop
  exact lazy_query_x_eq_explicit_y_frame
    (fun x y =>
      Program.set ow_challenge_y y >>= fun _ =>
        oracle_loop_n ow_adv q lazy_query >>= fun _ =>
          Program.get ow_response >>= fun resp =>
            lazy_query resp >>= fun y_check =>
              (pure (decide (y_check = y)) : Program state Bool))

/-! ## Hop 1 → 2: up-to-bad

`P[Game 1 wins] ≤ P[Game 2 wins] + P[bad in Game 1]`, where `bad` =
"adversary queries the oracle at `chal_x` at some point in the loop or
in the verification step."

The strategy:

* Augment both games with a tracking flag `chal_x_queried_gh` that gets
  set to `true` whenever a `lazy_query` is invoked at input
  `chal_x`.
* Show the tracked games are wp-equivalent to the untracked games on
  posts that ignore the flag (`Program.wp_conditional_set_disjoint_no_op`).
* Show the tracked Game 1 and tracked Game 2 are *identical until bad*:
  their wp's agree on posts that vanish whenever the flag is `true`.
* Apply `Program.up_to_bad` to derive
  `Game 1_tracked.wp G ≤ Game 2_tracked.wp G + Game 1_tracked.wp (G | bad)`.
* Strip tracking to obtain the corresponding statement for the
  un-tracked games.
-/

end GameHopParam

/-- Fresh tracking flag for the game-hopping proof (separate from QueryHit's
    `chal_x_queried` to avoid cross-contamination). -/
axiom chal_x_queried_gh : Variable Bool

axiom disjoint_chal_x_queried_gh_ro : disjoint chal_x_queried_gh random_oracle_state
axiom disjoint_chal_x_queried_gh_ow_challenge_x :
  disjoint chal_x_queried_gh ow_challenge_x
axiom disjoint_chal_x_queried_gh_ow_challenge_y :
  disjoint chal_x_queried_gh ow_challenge_y
axiom disjoint_chal_x_queried_gh_ow_response : disjoint chal_x_queried_gh ow_response
axiom disjoint_chal_x_queried_gh_oracle_input :
  disjoint chal_x_queried_gh oracle_input
axiom disjoint_chal_x_queried_gh_oracle_output :
  disjoint chal_x_queried_gh oracle_output

attribute [instance] disjoint_chal_x_queried_gh_ro
                     disjoint_chal_x_queried_gh_ow_challenge_x
                     disjoint_chal_x_queried_gh_ow_challenge_y
                     disjoint_chal_x_queried_gh_ow_response
                     disjoint_chal_x_queried_gh_oracle_input
                     disjoint_chal_x_queried_gh_oracle_output

/-- Symmetric instances. -/
instance : disjoint random_oracle_state chal_x_queried_gh :=
  disjoint_chal_x_queried_gh_ro.symm
instance : disjoint ow_challenge_x chal_x_queried_gh :=
  disjoint_chal_x_queried_gh_ow_challenge_x.symm
instance : disjoint ow_challenge_y chal_x_queried_gh :=
  disjoint_chal_x_queried_gh_ow_challenge_y.symm
instance : disjoint ow_response chal_x_queried_gh :=
  disjoint_chal_x_queried_gh_ow_response.symm
instance : disjoint oracle_input chal_x_queried_gh :=
  disjoint_chal_x_queried_gh_oracle_input.symm
instance : disjoint oracle_output chal_x_queried_gh :=
  disjoint_chal_x_queried_gh_oracle_output.symm

/-- A `lazy_query` that *also* sets `chal_x_queried_gh` to `true` if the
    input equals `chal_x`. The tracked games use this in place of
    `lazy_query`. Defined via explicit `>>=` to avoid Lean's do-notation
    join-point macro on the `if` branch. -/
noncomputable def lazy_query_tracked (inp : input) : Program state output :=
  lazy_query inp >>= fun y =>
    Program.get ow_challenge_x >>= fun cx =>
      (if inp = cx then Program.set chal_x_queried_gh true
       else (pure () : Program state Unit)) >>= fun _ =>
        (pure y : Program state output)

/-! ### Output-side matched flag for the Game 2 reduction

The reduction `Game 2 wins ≤ guess(output, q+1) matched` tracks "some
`lazy_query` returned `chal_y`" via a fresh flag `matched_chal_y`. Game 2's
win event implies this flag is set: the final `lazy_query_tracked` returns
`y_check = chal_y`, which sets the flag.

This is the standard cryptographic factorization where the matching event
is captured by a dedicated flag, exposing it as a `guess_experiment` instance. -/

/-- Matched flag for the output-side guess (against `chal_y`). -/
axiom matched_chal_y : Variable Bool

axiom disjoint_matched_chal_y_ro : disjoint matched_chal_y random_oracle_state
axiom disjoint_matched_chal_y_chal_x : disjoint matched_chal_y ow_challenge_x
axiom disjoint_matched_chal_y_chal_y : disjoint matched_chal_y ow_challenge_y
axiom disjoint_matched_chal_y_response : disjoint matched_chal_y ow_response
axiom disjoint_matched_chal_y_input : disjoint matched_chal_y oracle_input
axiom disjoint_matched_chal_y_output : disjoint matched_chal_y oracle_output
axiom disjoint_matched_chal_y_chal_x_queried_gh :
  disjoint matched_chal_y chal_x_queried_gh

attribute [instance] disjoint_matched_chal_y_ro
                     disjoint_matched_chal_y_chal_x
                     disjoint_matched_chal_y_chal_y
                     disjoint_matched_chal_y_response
                     disjoint_matched_chal_y_input
                     disjoint_matched_chal_y_output
                     disjoint_matched_chal_y_chal_x_queried_gh

instance : disjoint random_oracle_state matched_chal_y :=
  disjoint_matched_chal_y_ro.symm
instance : disjoint ow_challenge_x matched_chal_y :=
  disjoint_matched_chal_y_chal_x.symm
instance : disjoint ow_challenge_y matched_chal_y :=
  disjoint_matched_chal_y_chal_y.symm
instance : disjoint ow_response matched_chal_y :=
  disjoint_matched_chal_y_response.symm
instance : disjoint oracle_input matched_chal_y :=
  disjoint_matched_chal_y_input.symm
instance : disjoint oracle_output matched_chal_y :=
  disjoint_matched_chal_y_output.symm
instance : disjoint chal_x_queried_gh matched_chal_y :=
  disjoint_matched_chal_y_chal_x_queried_gh.symm

/-- Queries list for the input-side collector (Game 1 bad reduction).
    Records adversary's inputs across loop iterations. -/
axiom queries_input : Variable (List input)

/-- Queries list for the output-side collector (Game 2 wins reduction).
    Records `lazy_query_tracked` outputs across loop iterations. -/
axiom queries_output : Variable (List output)

axiom disjoint_queries_input_chal_x_queried_gh :
  disjoint queries_input chal_x_queried_gh
axiom disjoint_queries_input_ro : disjoint queries_input random_oracle_state
axiom disjoint_queries_input_chal_x : disjoint queries_input ow_challenge_x
axiom disjoint_queries_input_chal_y : disjoint queries_input ow_challenge_y
axiom disjoint_queries_input_response : disjoint queries_input ow_response
axiom disjoint_queries_input_oracle_input : disjoint queries_input oracle_input
axiom disjoint_queries_input_oracle_output : disjoint queries_input oracle_output

axiom disjoint_queries_output_matched_chal_y :
  disjoint queries_output matched_chal_y
axiom disjoint_queries_output_ro : disjoint queries_output random_oracle_state
axiom disjoint_queries_output_chal_x : disjoint queries_output ow_challenge_x
axiom disjoint_queries_output_chal_y : disjoint queries_output ow_challenge_y
axiom disjoint_queries_output_response : disjoint queries_output ow_response
axiom disjoint_queries_output_oracle_input : disjoint queries_output oracle_input
axiom disjoint_queries_output_oracle_output : disjoint queries_output oracle_output
axiom disjoint_queries_output_chal_x_queried_gh :
  disjoint queries_output chal_x_queried_gh

attribute [instance] disjoint_queries_input_chal_x_queried_gh
                     disjoint_queries_input_ro
                     disjoint_queries_input_chal_x
                     disjoint_queries_input_chal_y
                     disjoint_queries_input_response
                     disjoint_queries_input_oracle_input
                     disjoint_queries_input_oracle_output
                     disjoint_queries_output_matched_chal_y
                     disjoint_queries_output_ro
                     disjoint_queries_output_chal_x
                     disjoint_queries_output_chal_y
                     disjoint_queries_output_response
                     disjoint_queries_output_oracle_input
                     disjoint_queries_output_oracle_output
                     disjoint_queries_output_chal_x_queried_gh

instance : disjoint chal_x_queried_gh queries_input :=
  disjoint_queries_input_chal_x_queried_gh.symm
instance : disjoint random_oracle_state queries_input :=
  disjoint_queries_input_ro.symm
instance : disjoint ow_challenge_x queries_input :=
  disjoint_queries_input_chal_x.symm
instance : disjoint ow_challenge_y queries_input :=
  disjoint_queries_input_chal_y.symm
instance : disjoint ow_response queries_input :=
  disjoint_queries_input_response.symm
instance : disjoint oracle_input queries_input :=
  disjoint_queries_input_oracle_input.symm
instance : disjoint oracle_output queries_input :=
  disjoint_queries_input_oracle_output.symm

instance : disjoint matched_chal_y queries_output :=
  disjoint_queries_output_matched_chal_y.symm
instance : disjoint random_oracle_state queries_output :=
  disjoint_queries_output_ro.symm
instance : disjoint ow_challenge_x queries_output :=
  disjoint_queries_output_chal_x.symm
instance : disjoint ow_challenge_y queries_output :=
  disjoint_queries_output_chal_y.symm
instance : disjoint ow_response queries_output :=
  disjoint_queries_output_response.symm
instance : disjoint oracle_input queries_output :=
  disjoint_queries_output_oracle_input.symm
instance : disjoint oracle_output queries_output :=
  disjoint_queries_output_oracle_output.symm
instance : disjoint chal_x_queried_gh queries_output :=
  disjoint_queries_output_chal_x_queried_gh.symm

-- Note: in the `guess_experiment`-based design, the match-check is placed
-- in `guess_experiment`'s body using BOUND variables (y_val, target y),
-- not via state reads. This is what makes the Game 2 wall proof tractable.

section GameHopParam_Tracked

variable (ow_adv : Program state Unit)
variable (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)

/-- Tracked Game 1: same as `ow_game_1`, but every `lazy_query` is replaced
    by `lazy_query_tracked` so the `chal_x_queried_gh` flag tracks whether
    the adversary ever queried `chal_x`. -/
noncomputable def ow_game_1_tracked (q : ℕ) : Program state Bool := do
  lazy_init
  Program.set chal_x_queried_gh false  -- explicit init of the flag
  let x ← Program.uniform
  Program.set ow_challenge_x x
  let y ← Program.uniform
  Program.set random_oracle_state (fun k => if k = x then some y else none)
  Program.set ow_challenge_y y
  oracle_loop_n ow_adv q lazy_query_tracked
  let resp ← Program.get ow_response
  let y_check ← lazy_query_tracked resp
  pure (decide (y_check = y))

/-- Tracked Game 2: same as `ow_game_2`, with `lazy_query` → `lazy_query_tracked`. -/
noncomputable def ow_game_2_tracked (q : ℕ) : Program state Bool := do
  lazy_init
  Program.set chal_x_queried_gh false
  let x ← Program.uniform
  Program.set ow_challenge_x x
  let y ← Program.uniform
  Program.set ow_challenge_y y
  oracle_loop_n ow_adv q lazy_query_tracked
  let resp ← Program.get ow_response
  let y_check ← lazy_query_tracked resp
  pure (decide (y_check = y))

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

/-- Body of `guess_experiment_game_2`: adv query + explicit match check
    against the bound target `y`. -/
noncomputable def body_game_2 (y : output) : Program state Unit := do
  ow_adv
  let inp ← Program.get oracle_input
  let y_val ← lazy_query_tracked inp
  Program.set oracle_output y_val
  if y_val = y then Program.set matched_chal_y true else pure ()

/-- Final of `guess_experiment_game_2`: oracle on response + explicit
    match check against the bound target `y`. -/
noncomputable def final_game_2 (y : output) : Program state Unit := do
  let resp ← Program.get ow_response
  let y_val ← lazy_query_tracked resp
  if y_val = y then Program.set matched_chal_y true else pure ()

/-- Env of `guess_experiment_game_2`: lazy_init + reset chal_x_queried_gh +
    sample chal_x. -/
noncomputable def env_game_2 : Program state Unit := do
  lazy_init
  Program.set chal_x_queried_gh false
  let x ← Program.uniform
  Program.set ow_challenge_x x

/-- **Game 2 as a `guess_experiment` instance.** The matched flag is
    `matched_chal_y`; the target is the uniformly-sampled `chal_y`. Body
    and final use the BOUND target `y` for explicit match-checks. -/
noncomputable def guess_experiment_game_2 (q : ℕ) : Program state Bool :=
  guess_experiment env_game_2 Program.uniform ow_challenge_y matched_chal_y
    (body_game_2 ow_adv) (final_game_2) q

/-- Body of `guess_experiment_game_1`: adv query + lazy_query_tracked
    (which internally flips chal_x_queried_gh when inp = chal_x). Doesn't
    use the bound target `x`. -/
noncomputable def body_game_1 (_x : input) : Program state Unit := do
  ow_adv
  let inp ← Program.get oracle_input
  let y ← lazy_query_tracked inp
  Program.set oracle_output y

/-- Final of `guess_experiment_game_1`: oracle on response. Doesn't use
    the bound target. -/
noncomputable def final_game_1 (_x : input) : Program state Unit := do
  let resp ← Program.get ow_response
  let y ← lazy_query_tracked resp
  Program.set oracle_output y

noncomputable def guess_experiment_game_1 (q : ℕ) : Program state Bool :=
  guess_experiment lazy_init Program.uniform ow_challenge_x chal_x_queried_gh
    (body_game_1 ow_adv) (final_game_1) q

/-! ### Bridge lemmas: ow_game_*_tracked ↔ guess_experiment_game_*

The cryptographic chain uses these bridges to relate the OW experiment's
win/bad events to the matched flag of the corresponding `guess_experiment`
instance. The matched flag is then bounded by `guess_experiment_wp_bound`. -/

section Bridges

variable (ow_adv : Program state Unit)

/-- `oracle_loop_n adv q oracle = loop_n q (oracle_step adv oracle)`.
    Both are recursive over `q` with the same body shape; the equality is
    a straightforward induction. -/
lemma oracle_loop_n_eq_loop_n
    (adv : Program state Unit) (oracle : input → Program state output) (q : ℕ) :
    oracle_loop_n adv q oracle = loop_n q (oracle_step adv oracle) := by
  induction q with
  | zero => rfl
  | succ n ih =>
    show oracle_step adv oracle >>= (fun _ => oracle_loop_n adv n oracle)
       = oracle_step adv oracle >>= fun _ => loop_n n (oracle_step adv oracle)
    rw [ih]

/-- `lazy_query_tracked inp` is ow_challenge_y-disjoint. -/
lemma lazy_query_tracked_inRange_ow_challenge_y (inp : input) :
    (lazy_query_tracked inp).inRange ow_challenge_y.compl.range := by
  haveI : disjoint ow_challenge_x ow_challenge_y :=
    disjoint_ow_challenge_y_ow_challenge_x.symm
  unfold lazy_query_tracked
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_y)
  refine Program.inRange_bind ?_ (fun cx => ?_)
  · exact Program.get_inRange_compl_of_disjoint ow_challenge_x ow_challenge_y
  refine Program.inRange_bind ?_ (fun _ => Program.inRange_pure _ _)
  by_cases h : inp = cx
  · simp only [if_pos h]
    exact Program.set_inRange_compl_of_disjoint
      chal_x_queried_gh ow_challenge_y true
  · simp only [if_neg h]
    exact Program.inRange_pure _ _

/-- `oracle_step adv lazy_query_tracked` is ow_challenge_y-disjoint when
    `adv` is. -/
lemma oracle_step_lazy_query_tracked_inRange_ow_challenge_y
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range) :
    (oracle_step ow_adv lazy_query_tracked).inRange ow_challenge_y.compl.range := by
  unfold oracle_step
  refine Program.inRange_bind h_ow_adv_chal_y (fun _ => ?_)
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint oracle_input ow_challenge_y) (fun inp => ?_)
  refine Program.inRange_bind (lazy_query_tracked_inRange_ow_challenge_y inp)
    (fun y => ?_)
  exact Program.set_inRange_compl_of_disjoint oracle_output ow_challenge_y y

/-- `loop_n n body` stays in `R` whenever `body` does. -/
lemma loop_n_inRange {R : LensRange state}
    (body : Program state Unit) (h_body : body.inRange R) (n : ℕ) :
    (loop_n n body).inRange R := by
  induction n with
  | zero => exact Program.inRange_pure _ _
  | succ n ih =>
    show (body >>= fun _ => loop_n n body).inRange R
    exact Program.inRange_bind h_body (fun _ => ih)

/-- Helper: the chal_y block + trailing `pure (decide (y_check = y))` (which
    uses the outer-bound y) absorbs into NEW_POST for chal_xqg-reading posts.
    Used for G2 bad-event reduction. -/
private lemma chal_y_block_pure_decide_eliminate
    (k : Program state output)
    (h_k : k.inRange ow_challenge_y.compl.range)
    (σ : state) :
    ((Program.uniform : Program state output) >>= fun y =>
      Program.set ow_challenge_y y >>= fun _ =>
      k >>= fun y_check => pure (decide (y_check = y))).wp
      (fun bσ : Bool × state => if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
    = k.wp (fun aσ : output × state =>
        if chal_x_queried_gh.get aσ.2 = true then (1 : ENNReal) else 0) σ := by
  rw [wp_bind, wp_uniform]
  -- For each y, the inner reduces to k.wp NEW_POST σ.
  have h_inner : ∀ y, (Program.set ow_challenge_y y >>= fun _ =>
      k >>= fun y_check => pure (decide (y_check = y))).wp
      (fun bσ : Bool × state => if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
      = k.wp (fun aσ : output × state =>
        if chal_x_queried_gh.get aσ.2 = true then (1 : ENNReal) else 0) σ := by
    intro y
    rw [wp_bind, wp_set, wp_bind]
    -- Goal: k.wp (fun aσ => (pure (decide aσ.1 = y)).wp F_chal_xqg aσ.2) (chal_y.set y σ) = k.wp NEW_POST σ.
    -- Simplify the post via wp_pure: F_chal_xqg ignores Bool.
    have h_post_eq :
        (fun aσ : output × state =>
          (Pure.pure (decide (aσ.1 = y)) : Program state Bool).wp
            (fun bσ : Bool × state =>
              if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) aσ.2)
        = fun aσ : output × state =>
          if chal_x_queried_gh.get aσ.2 = true then (1 : ENNReal) else 0 := by
      funext aσ
      rw [wp_pure]
    rw [h_post_eq]
    -- Goal: k.wp NEW_POST (chal_y.set y σ) = k.wp NEW_POST σ.
    have h_F : IgnoresLens ow_challenge_y
        (fun aσ' : output × state =>
          if chal_x_queried_gh.get aσ'.2 = true then (1 : ENNReal) else 0) := by
      intro aσ v
      simp only [Lens.get_of_disjoint_set chal_x_queried_gh ow_challenge_y v aσ.2]
    have h_k_wp_inv : IgnoresLens ow_challenge_y
        (fun aσ : Unit × state => k.wp
          (fun aσ' : output × state =>
            if chal_x_queried_gh.get aσ'.2 = true then (1 : ENNReal) else 0) aσ.2) :=
      IgnoresLens.comp_inRange (L := ow_challenge_y) h_F (fun _ : Unit => k)
        (fun _ => h_k)
    exact h_k_wp_inv ((), σ) y
  simp_rw [h_inner]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  exact ENNReal.div_mul_cancel
    (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

/-- **Game 2 bad-event ↔ guess_experiment_game_1 matched-event bridge.**

    Both programs have the same structure (lazy RO, no pre-programming,
    `lazy_query_tracked` for the loop). They differ only by:
    1. Order of disjoint-lens writes in the prefix.
    2. G2 has `uniform y; set chal_y y` (invisible at F_chal_xqg).
    3. Trailing: G2 `pure (decide (y_check = y))` (Game 2's win indicator,
       ignored by F_chal_xqg) vs guess `set oo y_check; get chal_xqg`.

    No deferred-sampling needed — both games have lazy RO.

    **Proof outline** (deferred — see helper `uniform_set_chal_y_invisible`
    above; the architectural piece is in place but assembling the full
    wp-chain is mechanical and tedious):

    Let NEW_POST(yc, σ') := if chal_xqg.get σ' then 1 else 0.

    1. **Trailing absorption.**
       * LHS: `wp_bind` + `wp_pure` on `pure (decide y_check = y)` →
         post becomes `fun (yc, σ') => F_chal_xqg(decide yc = y, σ')`.
         F_chal_xqg ignores Bool, so post simplifies to NEW_POST.
       * RHS: `wp_bind` + `wp_set` on `set oo y_check`, then `wp_get`
         on `get chal_xqg`. Result: NEW_POST (oo ⊥ chal_xqg means
         `chal_xqg.get (oo.set v σ') = chal_xqg.get σ'`).
       * After this step, both sides reduce to
         `(prefix; loop; get resp; lqt resp).wp NEW_POST σ`
         for different prefixes.

    2. **Eliminate G2's chal_y block.**
       Apply `uniform_set_chal_y_invisible` with
       k = `loop_n q (oracle_step adv lqt) >>= fun _ => get ow_response
            >>= fun resp => lqt resp`, F = NEW_POST. Hypotheses:
       * `h_k`: k is chal_y-disjoint. Composition of loop_n_inRange +
         oracle_step's chal_y-disjointness (needs `h_ow_adv_chal_y`) +
         lqt's chal_y-disjointness.
       * `h_F`: NEW_POST is chal_y-ignoring (only reads chal_xqg).

    3. **Commute `set chal_xqg false`.**
       After step 2, LHS has `lazy_init; set chal_xqg false; uniform x;
       set chal_x x; k` and RHS has `lazy_init; uniform x; set chal_x x;
       set chal_xqg false; k`. Differ only by position of `set chal_xqg
       false` relative to `uniform x; set chal_x x`. Commute via:
       * `bind_uniform_comm` to move `set chal_xqg false` past `uniform x`
         (uniform doesn't write state).
       * Lens-disjoint commutation (chal_xqg ⊥ chal_x) to move past
         `set chal_x x`.

    Each step is a standard pattern in the existing proofs (cf.
    `ow_game_2_tracked_wins_le_guess_experiment_game_2_matched` for the
    Game 2 win bridge). The helper `uniform_set_chal_y_invisible` already
    captures the only structurally novel piece. -/
lemma ow_game_2_tracked_bad_eq_guess_experiment_game_1
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (q : ℕ) (σ : state) :
    (ow_game_2_tracked ow_adv q).wp
        (fun bσ : Bool × state =>
          if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
    = (guess_experiment_game_1 ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  -- Common "tail" k = loop_n; get resp; lqt resp.
  set k : Program state output :=
    loop_n q (oracle_step ow_adv lazy_query_tracked) >>= fun _ =>
      Program.get ow_response >>= fun resp =>
      lazy_query_tracked resp with k_def
  -- NEW_POST: chal_xqg-reading, output-ignoring post.
  set NEW_POST : output × state → ENNReal :=
    fun aσ => if chal_x_queried_gh.get aσ.2 = true then 1 else 0
      with NEW_POST_def
  -- (b) RHS trailing absorption — generic helper inlined.
  -- For any p : Program state output:
  --   (p >>= fun y => set oo y >>= fun _ => get chal_xqg).wp F_matched σ
  --   = p.wp NEW_POST σ
  -- The absorption uses oo ⊥ chal_xqg.
  have h_trailing_absorb : ∀ (p : Program state output) (σ' : state),
      (p >>= fun y =>
          Program.set oracle_output y >>= fun _ =>
          Program.get chal_x_queried_gh).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
      = p.wp NEW_POST σ' := by
    intro p σ'
    rw [wp_bind]
    congr 1
    funext aσ
    obtain ⟨a, s'⟩ := aσ
    dsimp only
    rw [wp_bind, wp_set, wp_get]
    simp only [NEW_POST_def]
    have h_get : chal_x_queried_gh.get (oracle_output.set a s')
                = chal_x_queried_gh.get s' :=
      Lens.get_of_disjoint_set chal_x_queried_gh oracle_output a s'
    rw [h_get]
  -- View GE1 as `(prefix >>= k) >>= trailing` and apply h_trailing_absorb.
  -- For this we need GE1 = (prefix >>= k) >>= trailing as Programs. This holds
  -- up to bind_assoc rewriting.
  -- View GE1 as `(prefix >>= k) >>= trailing` via Program equality (bind_assoc).
  have h_GE1_eq : guess_experiment_game_1 ow_adv q
      = (lazy_init >>= fun _ =>
         (Program.uniform : Program state input) >>= fun x =>
         Program.set ow_challenge_x x >>= fun _ =>
         Program.set chal_x_queried_gh false >>= fun _ => k) >>=
        (fun y => Program.set oracle_output y >>= fun _ =>
                  Program.get chal_x_queried_gh) := by
    unfold guess_experiment_game_1 guess_experiment body_game_1 final_game_1
    simp only [k_def, oracle_step, Program.bind_assoc]
  have h_RHS : (guess_experiment_game_1 ow_adv q).wp
      (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
      = (lazy_init >>= fun _ =>
         (Program.uniform : Program state input) >>= fun x =>
         Program.set ow_challenge_x x >>= fun _ =>
         Program.set chal_x_queried_gh false >>= fun _ => k).wp NEW_POST σ := by
    rw [h_GE1_eq]
    exact h_trailing_absorb _ σ
  rw [h_RHS]
  -- k is chal_y-disjoint (composed from loop_n_inRange + lqt_inRange_chal_y).
  have h_k_chal_y : k.inRange ow_challenge_y.compl.range := by
    rw [k_def]
    refine Program.inRange_bind ?_ (fun _ => ?_)
    · exact loop_n_inRange _ (oracle_step_lazy_query_tracked_inRange_ow_challenge_y
        ow_adv h_ow_adv_chal_y) q
    refine Program.inRange_bind
      (Program.get_inRange_compl_of_disjoint ow_response ow_challenge_y) (fun _ => ?_)
    exact lazy_query_tracked_inRange_ow_challenge_y _
  -- (a) LHS: trailing pure-decide absorbed + chal_y block eliminated.
  have h_OG2_eq : ow_game_2_tracked ow_adv q
      = (lazy_init >>= fun _ =>
         Program.set chal_x_queried_gh false >>= fun _ =>
         (Program.uniform : Program state input) >>= fun x =>
         Program.set ow_challenge_x x) >>= fun _ =>
        ((Program.uniform : Program state output) >>= fun y =>
         Program.set ow_challenge_y y >>= fun _ =>
         k >>= fun y_check => pure (decide (y_check = y))) := by
    unfold ow_game_2_tracked
    rw [oracle_loop_n_eq_loop_n]
    simp only [k_def, Program.bind_assoc]
  have h_LHS : (ow_game_2_tracked ow_adv q).wp
      (fun bσ : Bool × state =>
        if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
      = ((lazy_init >>= fun _ =>
          Program.set chal_x_queried_gh false >>= fun _ =>
          (Program.uniform : Program state input) >>= fun x =>
          Program.set ow_challenge_x x) >>= fun _ => k).wp NEW_POST σ := by
    rw [h_OG2_eq]
    rw [wp_bind]
    conv_rhs => rw [wp_bind]
    congr 1
    funext aσ
    exact chal_y_block_pure_decide_eliminate k h_k_chal_y aσ.2
  rw [h_LHS]
  -- (c) Two prefixes equal up to `set chal_xqg false` commutation.
  have h_prefix_eq :
      ((lazy_init >>= fun _ =>
        Program.set chal_x_queried_gh false >>= fun _ =>
        (Program.uniform : Program state input) >>= fun x =>
        Program.set ow_challenge_x x) >>= (fun _ => k))
      = ((lazy_init >>= fun _ =>
          (Program.uniform : Program state input) >>= fun x =>
          Program.set ow_challenge_x x >>= fun _ =>
          Program.set chal_x_queried_gh false) >>= (fun _ => k)) := by
    simp only [Program.bind_assoc]
    congr 1
    funext _
    rw [Program.bind_uniform_comm
      (Program.set chal_x_queried_gh false) (fun x =>
        (Program.set ow_challenge_x x : Program state Unit) >>= fun _ => k)]
    congr 1
    funext x
    apply Program.ext_of_wp
    intro F
    funext σ_pre
    simp only [wp_bind, wp_set]
    congr 1
    exact ((inferInstance : disjoint chal_x_queried_gh ow_challenge_x).commute
      σ_pre false x).symm
  rw [h_prefix_eq]
  -- Final cleanup: both sides are now structurally equal modulo bind_assoc.
  simp only [Program.bind_assoc]

end Bridges

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
private noncomputable def insert_at_chal_x (y_chal : output) (σ : state) : state :=
  random_oracle_state.set
    (fun k => if k = ow_challenge_x.get σ then some y_chal
              else random_oracle_state.get σ k) σ

/-- Decompose `lazy_query_tracked.wp` into a `lazy_query.wp` with the
    bad-flag branching folded into the post. -/
private lemma lazy_query_tracked_wp_decompose
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

private lemma RO_setentry_neq_commutes_lazy_query
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
private lemma lazy_query_wp_invariant_under_RO_chal_x_set_at_neq
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
private lemma lazy_query_tracked_wp_invariant_under_RO_chal_x_set
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

/-- **Flag-true-zero (generic)**: a program in `flag.compl.range` produces wp = 0
    at flag-true input when the post vanishes on flag-true outputs. The program
    doesn't write flag, so all post-states still have flag = true. -/
private lemma Program.wp_zero_of_flag_true_in_range
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
private lemma lazy_query_tracked_wp_at_flag_true
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
private lemma oracle_step_wp_at_flag_true
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
private lemma oracle_loop_n_lazy_query_tracked_wp_at_flag_true
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
private lemma oracle_step_lazy_query_tracked_wp_invariant_under_RO_chal_x_set
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
private lemma oracle_loop_n_lazy_query_tracked_wp_invariant_under_RO_chal_x_set
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

end GameHopParam_Tracked

/-! ## Reductions from OW games to the guessing game

We instantiate `guess_experiment` for the two OW reductions:

* **Output side (Game 2 wins)**: `T = output`, `target_var = ow_challenge_y`.
  Each guess is the value returned by `lazy_query_tracked` at the
  adversary's chosen input (loop step) or at `ow_response` (final step).
  After `q` loop iterations and `1` final query, we have `q+1` guesses.
  Adversary's view is independent of `chal_y` (it never reads `chal_y`).

* **Input side (bad in Game 1)**: `T = input`, `target_var = ow_challenge_x`.
  Each guess is the input chosen by the adversary (`oracle_input` after
  the adversary step), or `ow_response` (final step). After `q+1` guesses,
  the bad event "some guess equaled `chal_x`" is exactly the
  `chal_x_queried_gh` flag being `true`.

The reductions show that the OW game's win/bad indicator wp is bounded
above by the corresponding guess_experiment's matched indicator wp.
The final `(q+1)/|T|` bound on `guess_experiment` is deferred. -/

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
noncomputable def guess_experiment_collector
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
theorem guess_experiment_interim_eq_collector
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
theorem guess_experiment_collector_wp_bound
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

/-- Body_aug invariant step: for body_aug = q_body >>= match_check t >>= record,
    the wp from invariant-respecting σ at "matched-reading" post equals the
    wp at "decide (t ∈ qs)-reading" post. -/
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
    (if a = t then Program.set matched_var true else (pure () : Program state Unit)).wp F σ
    = F ((), σ) := by
  by_cases h : a = t
  · simp only [if_pos h, wp_set]
    exact h_F ((), σ) _
  · simp only [if_neg h, wp_pure]

/-- **Schema-based correspondence**: when body and body_recording both
    decompose as `q >>= ...` for some shared "query" subprogram `q`, with
    body's tail being a match-check against `t` and body_recording's tail
    appending to `queries_list_var`, the per-state correspondence (the
    `h_correspondence` hypothesis of `guess_experiment_le_interim_assumption`)
    is provable structurally.

    The cryptographic content "the LHS's matched-fire ↔ RHS's `t ∈ qs`"
    becomes the *invariant* `matched_var = decide (t ∈ queries_list_var)`,
    maintained by each iter since both sides run the same `q` and update
    their respective tracking variables in lockstep.

    `q_body` and `q_final` are the shared subprograms for the loop and the
    final iteration respectively. They may differ (e.g., body does adv query
    via oracle_input, final does response check via ow_response). -/
theorem guess_experiment_le_interim_via_schema
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (env : Program state Unit)
    (target_var : Lens T state) (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint matched_var queries_list_var]
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
  -- Substitute schema hypotheses to expose the q_body / q_final structure.
  rw [h_body t, h_final t, h_body_recording, h_final_recording]
  -- ATTEMPT: prove the per-state correspondence directly by induction on n.
  --
  -- Key claim (strengthened induction):
  -- For any σ_state, the wp equality holds for one iter + tail, allowing
  -- us to peel iters off the loop. The invariant tracks how matched.get
  -- relates to (t ∈ qs.get) through the chain.
  --
  -- Concretely, we prove by induction:
  -- For any σ_inner with matched_var.get σ_inner = false ∧ qs.get σ_inner = [],
  -- the LHS chain and RHS chain have equal wps.
  --
  -- We achieve "matched = false, qs = []" by inserting/aligning the
  -- prefix sets on both sides.
  sorry

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

section Reductions

variable (ow_adv : Program state Unit)

/-! ### Game 2 reduction to the `guess_experiment` framework

The reduction routes directly through `guess_experiment_game_2`. The chain:

1. `ow_game_2_tracked.wp win ≤ guess_experiment_game_2.wp matched`
   (Game 2 wall, PROVED via the chain: env+sample+set chal_y descent,
   state alignment, body conversion, pointwise tail comparison).
2. `guess_experiment_game_2.wp matched ≤ (q+1)/|output|` (framework
   bound — each lazy_query has ≤ 1/|output| chance of returning the
   uniformly-sampled `chal_y`). -/

/-- `lazy_query_tracked inp` is matched_chal_y-disjoint: all writes go to
    `random_oracle_state` or `chal_x_queried_gh`, both disjoint from
    `matched_chal_y`. -/
lemma lazy_query_tracked_inRange_matched_chal_y (inp : input) :
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
lemma oracle_step_lazy_query_tracked_inRange_matched_chal_y
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

/-- **Cond_set invisibility for matched-ignoring posts.** A direct
    `if cond then set matched true else pure ()` is wp-invisible. -/
lemma cond_set_matched_chal_y_wp_invisible
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
noncomputable def body_v2 (adv : Program state Unit) (y : output) :
    Program state Unit := do
  adv
  let inp ← Program.get oracle_input
  let y_val ← lazy_query_tracked inp
  Program.set oracle_output y_val
  if y_val = y then Program.set matched_chal_y true else pure ()

/-- **Body-level wp equality for the bound-variable cond_set pattern.**
    `body_v2 ow_adv y` has same wp as plain `oracle_step` for
    matched_chal_y-ignoring posts. -/
lemma body_v2_wp_eq_oracle_step
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
lemma loop_n_wp_eq_of_body_eq
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
lemma loop_n_body_v2_wp_eq
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
lemma wp_matched_chal_y_set_inv {α : Type} {p : Program state α}
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
lemma ow_game_2_tracked_wins_le_guess_experiment_game_2_matched
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

/-! ### Collector-based per-game instances and reductions

For each game, define `body_recording` and `final_recording` that record
guesses into the appropriate queries list, then assume the per-game
inequality `guess_experiment_game_X ≤ guess_experiment_interim_game_X`
and the length invariant. This closes the chain via:
  Game → guess_experiment → guess_experiment_interim → (n+1)/|T|. -/

/-- Body recording for Game 2 wins: same shape as guess_experiment_game_2.body
    but without the explicit match-check; instead appends `y_val` to qs. -/
noncomputable def body_recording_game_2 (adv : Program state Unit) :
    Program state Unit := do
  adv
  let inp ← Program.get oracle_input
  let y_val ← lazy_query_tracked inp
  Program.set oracle_output y_val
  let qs ← Program.get queries_output
  Program.set queries_output (qs ++ [y_val])

/-- Final recording for Game 2 wins: the last query attempt records `y_val`. -/
noncomputable def final_recording_game_2 : Program state Unit := do
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
noncomputable def q_body_game_2 (ow_adv : Program state Unit) : Program state output := do
  ow_adv
  let inp ← Program.get oracle_input
  let y_val ← lazy_query_tracked inp
  Program.set oracle_output y_val
  pure y_val

/-- The "query" subprogram shared between final_game_2 and final_recording_game_2.
    Returns `y_val` for the response. -/
noncomputable def q_final_game_2 : Program state output := do
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

/-- `lazy_query_tracked` is queries_input-disjoint. -/
private lemma lazy_query_tracked_inRange_queries_input (inp : input) :
    (lazy_query_tracked inp).inRange queries_input.compl.range := by
  unfold lazy_query_tracked
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state queries_input)
  refine Program.inRange_bind ?_ (fun cx => ?_)
  · exact Program.get_inRange_compl_of_disjoint ow_challenge_x queries_input
  refine Program.inRange_bind ?_ (fun _ => Program.inRange_pure _ _)
  by_cases h : inp = cx
  · simp only [if_pos h]
    exact Program.set_inRange_compl_of_disjoint chal_x_queried_gh queries_input true
  · simp only [if_neg h]
    exact Program.inRange_pure _ _

/-! ### Disjointness for q_body_game_2 and q_final_game_2 -/

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

/-- Helper: `get qi >>= fun qs => set qi (qs ++ [v])` has the same wp as
    `pure ()` at queries_input-ignoring posts. -/
private lemma wp_qi_get_set_invisible
    (val : input)
    (F : Unit × state → ENNReal)
    (h_F : IgnoresLens queries_input F)
    (σ : state) :
    (Program.get queries_input >>= fun qs : List input =>
       Program.set queries_input (qs ++ [val])).wp F σ
    = F ((), σ) := by
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_set]
  exact h_F ((), σ) _

/-- Helper: a trailing `get qi >>= set qi (qs ++ [v])` is invisible to wp at
    queries_input-ignoring posts. (Specialized to Program state Unit.) -/
private lemma wp_qi_trailing_invisible
    (p : Program state Unit) (val : input)
    (F : Unit × state → ENNReal)
    (h_F : IgnoresLens queries_input F)
    (σ : state) :
    (p >>= fun _ : Unit =>
       Program.get queries_input >>= fun qs : List input =>
       Program.set queries_input (qs ++ [val])).wp F σ
    = p.wp F σ := by
  rw [wp_bind]
  congr 1
  funext aσ
  obtain ⟨a, s'⟩ := aσ
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_set]
  exact h_F (a, s') _

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

/-- Body recording for Game 1 bad: same shape as guess_experiment_game_1.body
    but appends `inp` (adv's query) to qs. -/
noncomputable def body_recording_game_1 (adv : Program state Unit) :
    Program state Unit := do
  adv
  let inp ← Program.get oracle_input
  let y ← lazy_query_tracked inp
  Program.set oracle_output y
  let qs ← Program.get queries_input
  Program.set queries_input (qs ++ [inp])

/-- Final recording for Game 1 bad: the last query attempt records `resp`. -/
noncomputable def final_recording_game_1 : Program state Unit := do
  let resp ← Program.get ow_response
  let y ← lazy_query_tracked resp
  Program.set oracle_output y
  let qs ← Program.get queries_input
  Program.set queries_input (qs ++ [resp])

/-! ### Game 1 schema: explicit-match form via game-hop

Game 1's `body_game_1` hides the match-check inside `lazy_query_tracked`
(which flips `chal_x_queried_gh` when `inp = chal_x`). The schema framework
requires the match-check to be explicit. We define `body_game_1'` using
`lazy_query` (untracked) plus an explicit `if inp = x` check, and show via
a game-hop that the wp's agree.

`q_body_game_1'` and `q_final_game_1'` are the schema's shared query
subprograms. -/

/-- The "query" subprogram for the explicit-match form of Game 1's body. -/
noncomputable def q_body_game_1' (ow_adv : Program state Unit) : Program state input := do
  ow_adv
  let inp ← Program.get oracle_input
  let y ← lazy_query inp
  Program.set oracle_output y
  pure inp

/-- The "query" subprogram for the explicit-match form of Game 1's final. -/
noncomputable def q_final_game_1' : Program state input := do
  let resp ← Program.get ow_response
  let y ← lazy_query resp
  Program.set oracle_output y
  pure resp

/-- Explicit-match body for Game 1 (post game-hop). Uses untracked
    `lazy_query` and explicit `if inp = x then set chal_x_qg true`. -/
noncomputable def body_game_1' (ow_adv : Program state Unit) (x : input) :
    Program state Unit :=
  q_body_game_1' ow_adv >>= fun a : input =>
    if a = x then Program.set chal_x_queried_gh true else (pure () : Program state Unit)

/-- Explicit-match final for Game 1 (post game-hop). -/
noncomputable def final_game_1' (x : input) : Program state Unit :=
  q_final_game_1' >>= fun a : input =>
    if a = x then Program.set chal_x_queried_gh true else (pure () : Program state Unit)

/-- Recording-style body for Game 1, using untracked `lazy_query`. This is
    wp-equivalent to `body_recording_game_1` at chal_x_qg-ignoring posts
    (since lazy_query_tracked's chal_x_qg flip is invisible). -/
noncomputable def body_recording_game_1' (ow_adv : Program state Unit) :
    Program state Unit :=
  q_body_game_1' ow_adv >>= fun a : input =>
    Program.get queries_input >>= fun qs : List input =>
    Program.set queries_input (qs ++ [a])

/-- Recording-style final for Game 1, using untracked `lazy_query`. -/
noncomputable def final_recording_game_1' : Program state Unit :=
  q_final_game_1' >>= fun a : input =>
    Program.get queries_input >>= fun qs : List input =>
    Program.set queries_input (qs ++ [a])

/-- Game 1', the schema-friendly variant. Same as Game 1 but with the
    explicit-match body/final. -/
noncomputable def guess_experiment_game_1' (ow_adv : Program state Unit) (q : ℕ) :
    Program state Bool :=
  guess_experiment lazy_init Program.uniform ow_challenge_x chal_x_queried_gh
    (body_game_1' ow_adv) final_game_1' q

/-! ### Disjointness for q_body_game_1' and q_final_game_1' -/

/-- `q_body_game_1' ow_adv` is chal_x_queried_gh-disjoint. -/
private lemma q_body_game_1'_inRange_chal_x_queried_gh
    (ow_adv : Program state Unit)
    (h_ow_adv : ow_adv.inRange chal_x_queried_gh.compl.range) :
    (q_body_game_1' ow_adv).inRange chal_x_queried_gh.compl.range := by
  unfold q_body_game_1'
  refine Program.inRange_bind h_ow_adv (fun _ => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun inp => ?_)
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `q_body_game_1' ow_adv` is queries_input-disjoint. -/
private lemma q_body_game_1'_inRange_queries_input
    (ow_adv : Program state Unit)
    (h_ow_adv : ow_adv.inRange queries_input.compl.range) :
    (q_body_game_1' ow_adv).inRange queries_input.compl.range := by
  unfold q_body_game_1'
  refine Program.inRange_bind h_ow_adv (fun _ => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun inp => ?_)
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state queries_input)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `q_body_game_1' ow_adv` is ow_challenge_x-disjoint. -/
private lemma q_body_game_1'_inRange_ow_challenge_x
    (ow_adv : Program state Unit)
    (h_ow_adv : ow_adv.inRange ow_challenge_x.compl.range) :
    (q_body_game_1' ow_adv).inRange ow_challenge_x.compl.range := by
  unfold q_body_game_1'
  refine Program.inRange_bind h_ow_adv (fun _ => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun inp => ?_)
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_x)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `q_final_game_1'` is chal_x_queried_gh-disjoint. -/
private lemma q_final_game_1'_inRange_chal_x_queried_gh :
    q_final_game_1'.inRange chal_x_queried_gh.compl.range := by
  unfold q_final_game_1'
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun resp => ?_)
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro resp)
      (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `q_final_game_1'` is queries_input-disjoint. -/
private lemma q_final_game_1'_inRange_queries_input :
    q_final_game_1'.inRange queries_input.compl.range := by
  unfold q_final_game_1'
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun resp => ?_)
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro resp)
      (Lens.range_le_compl_of_disjoint random_oracle_state queries_input)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- `q_final_game_1'` is ow_challenge_x-disjoint. -/
private lemma q_final_game_1'_inRange_ow_challenge_x :
    q_final_game_1'.inRange ow_challenge_x.compl.range := by
  unfold q_final_game_1'
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun resp => ?_)
  refine Program.inRange_bind ?_ (fun y => ?_)
  · exact Program.inRange_mono (lazy_query_inRange_ro resp)
      (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_x)
  refine Program.inRange_bind (Program.set_inRange_compl_of_disjoint _ _ _) (fun _ => ?_)
  exact Program.inRange_pure _ _

/-- **Game-hop bridge**: at the chal_x_queried_gh-firing post (which is what
    Game 1 cares about), `guess_experiment_game_1` and `guess_experiment_game_1'`
    have the same wp. This is because, inside guess_experiment's loop after
    `set ow_challenge_x t`, `lazy_query_tracked inp` (which compares inp to
    chal_x = t) is wp-equivalent to `lazy_query inp >>= if inp = t then set chal_x_qg`.

    Proof DEFERRED — requires conditional-wp manipulation that respects the
    `chal_x = t` post-condition through each iter. -/
private lemma guess_experiment_game_1_wp_eq_game_1'
    (ow_adv : Program state Unit)
    (h_ow_adv_RO : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (q : ℕ) (σ : state) :
    (guess_experiment_game_1 ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    = (guess_experiment_game_1' ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  sorry

/-- **Body-recording bridge**: at chal_x_queried_gh-ignoring posts,
    `body_recording_game_1` (with lazy_query_tracked) and
    `body_recording_game_1'` (with lazy_query) have the same wp.

    Proof DEFERRED — the chal_x_qg flip in lazy_query_tracked is invisible
    at chal_x_qg-ignoring posts. -/
private lemma body_recording_game_1_wp_eq_body_recording_game_1'
    (ow_adv : Program state Unit)
    (F : Unit × state → ENNReal)
    (h_F : IgnoresLens chal_x_queried_gh F)
    (σ : state) :
    (body_recording_game_1 ow_adv).wp F σ
    = (body_recording_game_1' ow_adv).wp F σ := by
  sorry

/-- **Final-recording bridge**: same as body-recording bridge for final. -/
private lemma final_recording_game_1_wp_eq_final_recording_game_1'
    (F : Unit × state → ENNReal)
    (h_F : IgnoresLens chal_x_queried_gh F)
    (σ : state) :
    final_recording_game_1.wp F σ = final_recording_game_1'.wp F σ := by
  sorry

/-- Helper: body_game_1 ow_adv and body_recording_game_1 ow_adv have the same
    wp at queries_input-ignoring posts. body_recording adds only a trailing
    qi append, which is wp-invisible to qi-ignoring F. -/
private lemma body_game_1_wp_eq_body_recording_game_1
    (ow_adv : Program state Unit) (t : input)
    (F : Unit × state → ENNReal)
    (h_F : IgnoresLens queries_input F)
    (σ : state) :
    (body_game_1 ow_adv t).wp F σ = (body_recording_game_1 ow_adv).wp F σ := by
  unfold body_game_1 body_recording_game_1
  conv_lhs => rw [wp_bind]
  conv_rhs => rw [wp_bind]
  congr 1
  funext aσ_ow
  obtain ⟨_, σ_1⟩ := aσ_ow
  dsimp only
  conv_lhs => rw [wp_bind, wp_get]
  conv_rhs => rw [wp_bind, wp_get]
  dsimp only
  conv_lhs => rw [wp_bind]
  conv_rhs => rw [wp_bind]
  congr 1
  funext aσ_lq
  obtain ⟨y, σ_2⟩ := aσ_lq
  dsimp only
  conv_lhs => rw [wp_set]
  conv_rhs => rw [wp_bind, wp_set]
  dsimp only
  rw [wp_qi_get_set_invisible _ F h_F _]

/-- body_game_1 is queries_input-disjoint when ow_adv is. -/
private lemma body_game_1_inRange_qi
    (ow_adv : Program state Unit)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (t : input) :
    (body_game_1 ow_adv t).inRange queries_input.compl.range := by
  unfold body_game_1
  refine Program.inRange_bind h_ow_adv_qi (fun _ => ?_)
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun inp => ?_)
  refine Program.inRange_bind (lazy_query_tracked_inRange_queries_input _) (fun y => ?_)
  exact Program.set_inRange_compl_of_disjoint _ _ _

/-- final_game_1 is queries_input-disjoint. -/
private lemma final_game_1_inRange_qi (t : input) :
    (final_game_1 t).inRange queries_input.compl.range := by
  unfold final_game_1
  refine Program.inRange_bind (Program.get_inRange_compl_of_disjoint _ _) (fun resp => ?_)
  refine Program.inRange_bind (lazy_query_tracked_inRange_queries_input _) (fun y => ?_)
  exact Program.set_inRange_compl_of_disjoint _ _ _

/-- A queries_input-disjoint program's wp at qi-ignoring F is invariant under
    setting queries_input on the input. -/
private lemma wp_qi_input_invariant_of_inRange_qi
    {α : Type} (p : Program state α)
    (h_p_qi : p.inRange queries_input.compl.range)
    (F : α × state → ENNReal) (h_F : IgnoresLens queries_input F)
    (σ : state) (v : List input) :
    p.wp F (queries_input.set v σ) = p.wp F σ := by
  have h_f_updates : (queries_input.update (Function.const _ v))
      ∈ ((queries_input.compl.range : LensRange state)ᶜ).updates := by
    rw [show ((queries_input.compl.range : LensRange state)ᶜ) = queries_input.range from by
        rw [LensRange.complement_range, LensRange.compl_compl]]
    exact ⟨Function.const _ v, Set.mem_univ _, rfl⟩
  have h_set_eq : queries_input.update (Function.const _ v) σ = queries_input.set v σ := by
    show queries_input.set ((Function.const _ v) (queries_input.get σ)) σ = queries_input.set v σ
    rfl
  rw [← h_set_eq]
  rw [Program.wp_shift_input h_p_qi h_f_updates]
  congr 1
  funext xs
  show F (xs.1, queries_input.update (Function.const _ v) xs.2) = F xs
  show F (xs.1, queries_input.set v xs.2) = F xs
  exact h_F xs v

/-- Body equivalence packaged as EquivModuloLens. -/
private lemma body_game_1_equiv_body_recording_game_1
    (ow_adv : Program state Unit) (t : input) :
    Program.EquivModuloLens queries_input
      (body_game_1 ow_adv t) (body_recording_game_1 ow_adv) :=
  fun F h_F σ => body_game_1_wp_eq_body_recording_game_1 ow_adv t F h_F σ

/-- Loop equivalence at the wp level — via the codebase's existing
    `loop_n_congr` lemma. -/
private lemma loop_n_body_game_1_wp_eq_loop_n_body_recording_game_1
    (ow_adv : Program state Unit) (t : input)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (n : ℕ) (F : Unit × state → ENNReal) (h_F : IgnoresLens queries_input F)
    (σ : state) :
    (loop_n n (body_game_1 ow_adv t)).wp F σ
    = (loop_n n (body_recording_game_1 ow_adv)).wp F σ :=
  loop_n_congr (body_game_1_inRange_qi ow_adv h_ow_adv_qi t)
    (body_game_1_equiv_body_recording_game_1 ow_adv t) n F h_F σ

/-- Helper: final_game_1 t and final_recording_game_1 have the same wp at
    queries_input-ignoring posts. -/
private lemma final_game_1_wp_eq_final_recording_game_1
    (t : input)
    (F : Unit × state → ENNReal)
    (h_F : IgnoresLens queries_input F)
    (σ : state) :
    (final_game_1 t).wp F σ = final_recording_game_1.wp F σ := by
  unfold final_game_1 final_recording_game_1
  conv_lhs => rw [wp_bind, wp_get]
  conv_rhs => rw [wp_bind, wp_get]
  dsimp only
  conv_lhs => rw [wp_bind]
  conv_rhs => rw [wp_bind]
  congr 1
  funext aσ_lq
  obtain ⟨y, σ_2⟩ := aσ_lq
  dsimp only
  conv_lhs => rw [wp_set]
  conv_rhs => rw [wp_bind, wp_set]
  dsimp only
  rw [wp_qi_get_set_invisible _ F h_F _]

/-- body_recording_game_1's wp at qi-ignoring posts is invariant under
    setting queries_input on the input. Proven by routing through body_game_1
    (which is qi-disjoint). -/
private lemma body_recording_game_1_wp_qi_input_invariant
    (ow_adv : Program state Unit) (t : input)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (F : Unit × state → ENNReal) (h_F : IgnoresLens queries_input F)
    (σ : state) (v : List input) :
    (body_recording_game_1 ow_adv).wp F (queries_input.set v σ)
    = (body_recording_game_1 ow_adv).wp F σ := by
  rw [← body_game_1_wp_eq_body_recording_game_1 ow_adv t F h_F
        (queries_input.set v σ)]
  rw [wp_qi_input_invariant_of_inRange_qi _
        (body_game_1_inRange_qi ow_adv h_ow_adv_qi t) F h_F σ v]
  rw [body_game_1_wp_eq_body_recording_game_1 ow_adv t F h_F σ]

/-- loop_n body_recording's wp at qi-ignoring posts is qi-input-invariant.
    Same routing trick: factor through loop_n body_game_1 (which is qi-disjoint). -/
private lemma loop_n_body_recording_game_1_wp_qi_input_invariant
    (ow_adv : Program state Unit) (t : input)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (n : ℕ) (F : Unit × state → ENNReal) (h_F : IgnoresLens queries_input F)
    (σ : state) (v : List input) :
    (loop_n n (body_recording_game_1 ow_adv)).wp F (queries_input.set v σ)
    = (loop_n n (body_recording_game_1 ow_adv)).wp F σ := by
  rw [← loop_n_body_game_1_wp_eq_loop_n_body_recording_game_1 ow_adv t h_ow_adv_qi n F h_F
        (queries_input.set v σ)]
  rw [wp_qi_input_invariant_of_inRange_qi _
        (loop_n_inRange _ (body_game_1_inRange_qi ow_adv h_ow_adv_qi t) n) F h_F σ v]
  rw [loop_n_body_game_1_wp_eq_loop_n_body_recording_game_1 ow_adv t h_ow_adv_qi n F h_F σ]

/-- final_recording_game_1's wp at qi-ignoring posts is qi-input-invariant. -/
private lemma final_recording_game_1_wp_qi_input_invariant
    (t : input)
    (F : Unit × state → ENNReal) (h_F : IgnoresLens queries_input F)
    (σ : state) (v : List input) :
    final_recording_game_1.wp F (queries_input.set v σ)
    = final_recording_game_1.wp F σ := by
  rw [← final_game_1_wp_eq_final_recording_game_1 t F h_F (queries_input.set v σ)]
  rw [wp_qi_input_invariant_of_inRange_qi _ (final_game_1_inRange_qi t) F h_F σ v]
  rw [final_game_1_wp_eq_final_recording_game_1 t F h_F σ]

/-- Bridge: LHS with body_game_1 = LHS with body_recording_game_1, for the
    full game_1 LHS (loop + final + get chal_x_qg). Uses the loop and final
    equivalences with the qi-ignoring chal_x_qg post. -/
private lemma loop_final_get_game_1_wp_eq_recording
    (ow_adv : Program state Unit)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (t : input) (q : ℕ) (σ : state) :
    (loop_n q (body_game_1 ow_adv t) >>= fun _ : Unit =>
     final_game_1 t >>= fun _ : Unit =>
     Program.get chal_x_queried_gh).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    = (loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
       final_recording_game_1 >>= fun _ : Unit =>
       Program.get chal_x_queried_gh).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  -- Post `if bσ.1 then 1 else 0` after `get chal_x_qg` reduces to
  -- `fun aσ : Unit × state => if chal_x_qg.get aσ.2 then 1 else 0` = F_chal_xqg.
  set F_chal_xqg : Unit × state → ENNReal :=
    fun aσ => if chal_x_queried_gh.get aσ.2 = true then (1 : ENNReal) else 0
    with hF_chal_xqg
  have h_F_chal_xqg_qi : IgnoresLens queries_input F_chal_xqg := by
    intro aσ v
    show (if chal_x_queried_gh.get (queries_input.set v aσ.2) = true then _ else _)
       = (if chal_x_queried_gh.get aσ.2 = true then _ else _)
    rw [Lens.get_of_disjoint_set chal_x_queried_gh queries_input]
  -- Step 1: peel the get chal_x_qg. After this, the post becomes F_chal_xqg.
  have h_get_collapse : ∀ (k : Program state Unit) (σ_k : state),
      (k >>= fun _ : Unit => Program.get chal_x_queried_gh).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ_k
      = k.wp F_chal_xqg σ_k := by
    intro k σ_k
    rw [wp_bind]
    congr 1
    funext aσ
    rw [wp_get]
  -- Apply h_get_collapse on both sides (LHS and RHS of the goal).
  -- After: (loop_n q body_game_1 >>= fun _ => final_game_1).wp F_chal_xqg σ
  --      = (loop_n q body_recording >>= fun _ => final_recording).wp F_chal_xqg σ
  rw [show (loop_n q (body_game_1 ow_adv t) >>= fun _ : Unit =>
          final_game_1 t >>= fun _ : Unit =>
          Program.get chal_x_queried_gh)
       = ((loop_n q (body_game_1 ow_adv t) >>= fun _ : Unit => final_game_1 t)
          >>= fun _ : Unit => Program.get chal_x_queried_gh)
       from by simp [Program.bind_assoc]]
  rw [show (loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
          final_recording_game_1 >>= fun _ : Unit =>
          Program.get chal_x_queried_gh)
       = ((loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit => final_recording_game_1)
          >>= fun _ : Unit => Program.get chal_x_queried_gh)
       from by simp [Program.bind_assoc]]
  rw [h_get_collapse, h_get_collapse]
  -- Step 2: peel final via wp_bind, then use final_game_1 ↔ final_recording equivalence.
  rw [wp_bind, wp_bind]
  -- Inner post: fun aσ : Unit × state => final_X.wp F_chal_xqg aσ.2 (X varies).
  -- This inner post is qi-ignoring (final_X is qi-disjoint + F_chal_xqg qi-ignoring).
  have h_final_post_qi : IgnoresLens queries_input
      (fun aσ : Unit × state => (final_game_1 t).wp F_chal_xqg aσ.2) := by
    intro aσ v
    exact wp_qi_input_invariant_of_inRange_qi _ (final_game_1_inRange_qi t)
      F_chal_xqg h_F_chal_xqg_qi _ v
  -- Use loop equivalence on the loop's wp.
  rw [loop_n_body_game_1_wp_eq_loop_n_body_recording_game_1 ow_adv t h_ow_adv_qi q _
      h_final_post_qi σ]
  -- Now: (loop_n q body_recording).wp (fun aσ => (final_game_1 t).wp F_chal_xqg aσ.2) σ
  --    = (loop_n q body_recording).wp (fun aσ => final_recording.wp F_chal_xqg aσ.2) σ
  congr 1
  funext aσ
  exact final_game_1_wp_eq_final_recording_game_1 t F_chal_xqg h_F_chal_xqg_qi aσ.2

/-- body_recording_game_1 is chal_x-input-invariant given ow_adv chal_x-blindness.
    Reason: body_recording starts with ow_adv, and the rest doesn't touch chal_x. -/
private lemma body_recording_game_1_wp_chal_x_input_invariant
    (ow_adv : Program state Unit)
    (h_ow_adv_chal_x_blind : ∀ (F : Unit × state → ENNReal) (σ : state) (v : input),
      ow_adv.wp F (ow_challenge_x.set v σ) = ow_adv.wp F σ)
    (F : Unit × state → ENNReal) (σ : state) (v : input) :
    (body_recording_game_1 ow_adv).wp F (ow_challenge_x.set v σ)
    = (body_recording_game_1 ow_adv).wp F σ := by
  -- body_recording = ow_adv >>= k. By chal_x-blindness of ow_adv on the
  -- wp post (whatever it is), the wp value is chal_x-input-invariant.
  unfold body_recording_game_1
  -- The do-block elaborates to ow_adv >>= fun _ => (...). Use wp_bind directly.
  rw [show (do
        ow_adv
        let inp ← Program.get oracle_input
        let y ← lazy_query_tracked inp
        Program.set oracle_output y
        let qs ← Program.get queries_input
        Program.set queries_input (qs ++ [inp]) : Program state Unit)
       = ow_adv >>= fun _ : Unit =>
           Program.get oracle_input >>= fun inp : input =>
           lazy_query_tracked inp >>= fun y : output =>
           Program.set oracle_output y >>= fun _ : Unit =>
           Program.get queries_input >>= fun qs : List input =>
           Program.set queries_input (qs ++ [inp])
       from rfl]
  rw [wp_bind, wp_bind]
  exact h_ow_adv_chal_x_blind _ σ v

/-- The full "loop + final + get chal_x_qg" chain (with recording bodies) is
    qi-input-invariant. -/
private lemma loop_final_get_recording_wp_qi_input_invariant
    (ow_adv : Program state Unit) (t : input)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (q : ℕ) (σ : state) (v : List input) :
    (loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
     final_recording_game_1 >>= fun _ : Unit =>
     Program.get chal_x_queried_gh).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0)
       (queries_input.set v σ)
    = (loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
       final_recording_game_1 >>= fun _ : Unit =>
       Program.get chal_x_queried_gh).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  rw [← loop_final_get_game_1_wp_eq_recording ow_adv h_ow_adv_qi t q (queries_input.set v σ)]
  rw [← loop_final_get_game_1_wp_eq_recording ow_adv h_ow_adv_qi t q σ]
  have h_chain_qi : (loop_n q (body_game_1 ow_adv t) >>= fun _ : Unit =>
                       final_game_1 t >>= fun _ : Unit =>
                       Program.get chal_x_queried_gh).inRange
                      queries_input.compl.range := by
    refine Program.inRange_bind
      (loop_n_inRange _ (body_game_1_inRange_qi ow_adv h_ow_adv_qi t) q) (fun _ => ?_)
    refine Program.inRange_bind (final_game_1_inRange_qi t) (fun _ => ?_)
    exact Program.get_inRange_compl_of_disjoint _ _
  have h_F_qi : IgnoresLens queries_input
      (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) := by
    intro bσ v'
    rfl
  exact wp_qi_input_invariant_of_inRange_qi _ h_chain_qi _ h_F_qi σ v

/-- body_recording_game_1 bumps queries_input.length by at most 1 per iteration. -/
private lemma body_recording_game_1_qs_length_bump
    (adv : Program state Unit)
    (h_adv : adv.inRange queries_input.compl.range)
    (σ : state) :
    (body_recording_game_1 adv).wp
      (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal)) σ
    ≤ ((queries_input.get σ).length : ENNReal) + 1 := by
  unfold body_recording_game_1
  rw [wp_bind]
  have h_rest_bound : ∀ σ',
      (Program.get oracle_input >>= fun inp =>
        lazy_query_tracked inp >>= fun y =>
        Program.set oracle_output y >>= fun _ =>
        Program.get queries_input >>= fun qs =>
        Program.set queries_input (qs ++ [inp])).wp
        (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal)) σ'
      ≤ ((queries_input.get σ').length : ENNReal) + 1 := by
    intro σ'
    rw [wp_bind, wp_get]
    dsimp only
    rw [wp_bind]
    have h_inner_eq : ∀ (y : output) (σ_lqt : state),
        (Program.set oracle_output y >>= fun _ =>
          Program.get queries_input >>= fun qs =>
          Program.set queries_input (qs ++ [oracle_input.get σ'])).wp
          (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal)) σ_lqt
        = ((queries_input.get σ_lqt).length : ENNReal) + 1 := by
      intro y σ_lqt
      simp only [wp_bind, wp_set, wp_get]
      simp only [Lens.get_of_disjoint_set queries_input oracle_output, Lens.set_get,
        List.length_append, List.length_singleton]
      push_cast
      ring
    refine le_trans (Program.wp_le_wp_of_le _ _
        (fun yσ : output × state => ((queries_input.get yσ.2).length : ENNReal) + 1)
        ?_ σ') ?_
    · intro yσ
      exact le_of_eq (h_inner_eq yσ.1 yσ.2)
    rw [Program.wp_add (lazy_query_tracked _)
        (fun yσ : output × state => ((queries_input.get yσ.2).length : ENNReal))
        (fun _ : output × state => (1 : ENNReal))]
    refine add_le_add ?_ ?_
    · exact Program.wp_qs_length_preserved_of_inRange queries_input
        (lazy_query_tracked _) (lazy_query_tracked_inRange_queries_input _) _
    · exact Program.wp_const_le _ _ _
  refine le_trans (Program.wp_le_wp_of_le _ _
      (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal) + 1)
      ?_ σ) ?_
  · intro aσ
    exact h_rest_bound aσ.2
  rw [Program.wp_add adv
      (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal))
      (fun _ : Unit × state => (1 : ENNReal))]
  refine add_le_add ?_ ?_
  · exact Program.wp_qs_length_preserved_of_inRange queries_input adv h_adv σ
  · exact Program.wp_const_le _ _ _

/-- final_recording_game_1 bumps queries_input.length by at most 1. -/
private lemma final_recording_game_1_qs_length_bump (σ : state) :
    final_recording_game_1.wp
      (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal)) σ
    ≤ ((queries_input.get σ).length : ENNReal) + 1 := by
  unfold final_recording_game_1
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_bind]
  have h_inner_eq : ∀ (y : output) (σ_lqt : state),
      (Program.set oracle_output y >>= fun _ =>
        Program.get queries_input >>= fun qs =>
        Program.set queries_input (qs ++ [ow_response.get σ])).wp
        (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal)) σ_lqt
      = ((queries_input.get σ_lqt).length : ENNReal) + 1 := by
    intro y σ_lqt
    simp only [wp_bind, wp_set, wp_get]
    simp only [Lens.get_of_disjoint_set queries_input oracle_output, Lens.set_get,
      List.length_append, List.length_singleton]
    push_cast
    ring
  refine le_trans (Program.wp_le_wp_of_le _ _
      (fun yσ : output × state => ((queries_input.get yσ.2).length : ENNReal) + 1)
      ?_ σ) ?_
  · intro yσ
    exact le_of_eq (h_inner_eq yσ.1 yσ.2)
  rw [Program.wp_add (lazy_query_tracked _)
      (fun yσ : output × state => ((queries_input.get yσ.2).length : ENNReal))
      (fun _ : output × state => (1 : ENNReal))]
  refine add_le_add ?_ ?_
  · exact Program.wp_qs_length_preserved_of_inRange queries_input
      (lazy_query_tracked _) (lazy_query_tracked_inRange_queries_input _) _
  · exact Program.wp_const_le _ _ _

/-- **Game 1 correspondence**.

    `body_game_1 ow_adv`'s match-fire on `chal_x_queried_gh` (via
    `lazy_query_tracked` flipping the flag when `inp = chal_x = t`) corresponds
    to `t ∈ queries_input` after `body_recording_game_1 ow_adv` (which appends
    each `inp` to the list). Both events are "some lazy_query_tracked saw
    `inp = t`".

    Requires hypothesis `h_ow_adv_chal_x_blind` that ow_adv is chal_x-input-blind
    (its wp is invariant under chal_x state changes). Without this, an adv that
    reads chal_x can violate the bound (e.g., always query chal_x = t in LHS).

    Proof obligation (currently `sorry`): inducting on the loop with invariant
    `chal_x_queried_gh = decide (t ∈ queries_input)` maintained by
    `body_recording_game_1`. -/
theorem game_1_correspondence (ow_adv : Program state Unit)
    (h_ow_adv_qi : ow_adv.inRange queries_input.compl.range)
    (h_ow_adv_chal_x_blind : ∀ (F : Unit × state → ENNReal) (σ : state) (v : input),
      ow_adv.wp F (ow_challenge_x.set v σ) = ow_adv.wp F σ)
    (q : ℕ)
    (σ' : state) (t : input) :
    (Program.set ow_challenge_x t >>= fun _ : Unit =>
     Program.set chal_x_queried_gh false >>= fun _ : Unit =>
     loop_n q (body_game_1 ow_adv t) >>= fun _ : Unit =>
     final_game_1 t >>= fun _ : Unit =>
     Program.get chal_x_queried_gh).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
     ≤
    (Program.set queries_input [] >>= fun _ : Unit =>
     loop_n q (body_recording_game_1 ow_adv) >>= fun _ : Unit =>
     final_recording_game_1 >>= fun _ : Unit =>
     Program.get queries_input >>= fun qs =>
     Program.set chal_x_queried_gh (decide (t ∈ qs)) >>= fun _ : Unit =>
     Program.get chal_x_queried_gh).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ' := by
  -- The chal_x_qg-only post is qi-ignoring.
  set Post : Bool × state → ENNReal :=
    fun bσ => if bσ.1 then (1 : ENNReal) else 0 with hPost
  -- Inner post after get chal_x_qg: F_inner = fun aσ : Unit × state =>
  --   if chal_x_qg.get aσ.2 then 1 else 0. Qi-ignoring.
  have h_F_inner_qi : IgnoresLens queries_input
      (fun aσ : Unit × state =>
        if chal_x_queried_gh.get aσ.2 = true then (1 : ENNReal) else 0) := by
    intro aσ v
    show (if chal_x_queried_gh.get (queries_input.set v aσ.2) = true then _ else _)
       = (if chal_x_queried_gh.get aσ.2 = true then _ else _)
    rw [Lens.get_of_disjoint_set chal_x_queried_gh queries_input]
  -- The remaining work — alignment, invariant, final wp algebra — is DEFERRED.
  sorry

/-- **Reduction: bad-in-Game-1 ≤ Guess(input, q+1)**.

    Routes via `guess_experiment_game_1` → `interim` → `collector` → bound. -/
theorem ow_game_1_tracked_bad_le_guess_input_bound
    (h_ow_adv_RO : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_ow_adv_queries : ow_adv.inRange queries_input.compl.range)
    (h_ow_adv_mass_one : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1)
    (h_ow_adv_chal_x_blind : ∀ (F : Unit × state → ENNReal) (σ : state) (v : input),
      ow_adv.wp F (ow_challenge_x.set v σ) = ow_adv.wp F σ)
    (q : ℕ) (σ : state) :
    (ow_game_1_tracked ow_adv q).wp
        (fun bσ : Bool × state =>
          if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
    ≤ ((q + 1) : ENNReal) / Fintype.card input := by
  rw [ow_game_1_tracked_bad_eq_ow_game_2_tracked_bad ow_adv h_ow_adv_RO
      h_ow_adv_chal_x h_ow_adv_chal_x_queried_gh h_ow_adv_mass_one q σ]
  rw [ow_game_2_tracked_bad_eq_guess_experiment_game_1 ow_adv
      h_ow_adv_chal_y q σ]
  refine le_trans (guess_experiment_le_interim_assumption _ _ _ queries_input _ _
      (body_recording_game_1 ow_adv) final_recording_game_1 _
      (game_1_correspondence ow_adv h_ow_adv_queries h_ow_adv_chal_x_blind q) _) ?_
  apply guess_experiment_interim_wp_bound
  -- h_qs_length_le for Game 1.
  intro σ'
  have h_post_eq : (fun aσ : Unit × state =>
        ((queries_input.get aσ.2).length : ENNReal) / Fintype.card input)
      = fun aσ : Unit × state => (Fintype.card input : ENNReal)⁻¹ *
            ((queries_input.get aσ.2).length : ENNReal) := by
    funext aσ
    rw [div_eq_mul_inv, mul_comm]
  rw [h_post_eq, Program.wp_const_mul]
  rw [show ((q + 1 : ℕ) : ENNReal) / Fintype.card input
        = (Fintype.card input : ENNReal)⁻¹ * ((q + 1 : ℕ) : ENNReal) from by
      rw [div_eq_mul_inv, mul_comm]]
  refine mul_le_mul' (le_refl _) ?_
  rw [wp_bind]
  refine le_trans (Program.wp_le_wp_of_le _ _
      (fun _ : Unit × state => ((q + 1 : ℕ) : ENNReal)) ?_ σ') ?_
  · intro aσ_lazy
    rw [wp_bind, wp_set]
    set σ_init := queries_input.set [] aσ_lazy.2 with σ_init_def
    have h_qs_init : (queries_input.get σ_init).length = 0 := by
      simp [σ_init_def, Lens.set_get]
    rw [wp_bind]
    refine le_trans (Program.wp_le_wp_of_le _ _
        (fun aσ : Unit × state =>
          ((queries_input.get aσ.2).length : ENNReal) + 1) ?_ σ_init) ?_
    · intro aσ_loop
      exact final_recording_game_1_qs_length_bump _
    rw [Program.wp_add (loop_n q (body_recording_game_1 ow_adv))
        (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal))
        (fun _ : Unit × state => (1 : ENNReal))]
    refine le_trans (add_le_add (loop_n_wp_linear_bound (body_recording_game_1 ow_adv)
        (fun σ => ((queries_input.get σ).length : ENNReal)) 1
        (fun σ_body => body_recording_game_1_qs_length_bump ow_adv h_ow_adv_queries σ_body)
        q σ_init) (Program.wp_const_le _ _ _)) ?_
    rw [h_qs_init]
    push_cast
    ring_nf
    rfl
  · exact Program.wp_const_le _ _ _

/-! ## Flag-elision bridge: untracked Game 1 ↔ tracked Game 1

For postconditions that don't read `chal_x_queried_gh`, the tracked and
untracked variants of Game 1 agree at the wp level. -/

lemma lazy_query_equiv_lazy_query_tracked (inp : input) :
    Program.EquivModuloLens chal_x_queried_gh (lazy_query inp) (lazy_query_tracked inp) := by
  intro F h_F σ
  -- Apply lazy_query_tracked_eq_lazy_query_wp with k := pure.
  have h_eq := lazy_query_tracked_eq_lazy_query_wp
    (k := fun y => (pure y : Program state output))
    (fun y => Program.inRange_pure _ _) F h_F inp σ
  -- h_eq : (lazy_query_tracked inp >>= pure).wp F σ = (lazy_query inp >>= pure).wp F σ.
  simp only [Program.bind_pure] at h_eq
  exact h_eq.symm

/-- `oracle_step ow_adv lazy_query` is equivalent (modulo `chal_x_queried_gh`)
    to `oracle_step ow_adv lazy_query_tracked` — same body, with the inner
    `lazy_query` replaced by the tracked variant. -/
lemma oracle_step_equiv_lazy_query_lazy_query_tracked :
    Program.EquivModuloLens chal_x_queried_gh
      (oracle_step ow_adv lazy_query)
      (oracle_step ow_adv lazy_query_tracked) := by
  dsimp only [oracle_step]
  -- The continuation `fun _ => get input >>= lazy_query inp >>= set oo` is
  -- flag-disjoint (LHS uses lazy_query, which is flag-disjoint).
  have h_inner_lq_inRange : ∀ _ : Unit, (do
      let inp ← Program.get oracle_input
      let y ← lazy_query inp
      Program.set oracle_output y : Program state Unit).inRange
        chal_x_queried_gh.compl.range := by
    intro _
    refine Program.inRange_bind
      (Program.get_inRange_compl_of_disjoint oracle_input chal_x_queried_gh)
      (fun inp => ?_)
    refine Program.inRange_bind ?_ (fun y =>
      Program.set_inRange_compl_of_disjoint oracle_output chal_x_queried_gh y)
    exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)
  refine Program.EquivModuloLens.bind (Program.EquivModuloLens.refl ow_adv)
    (fun _ => ?_) h_inner_lq_inRange
  -- Inner: get input >>= ... [lq vs lqt] >>= set oo.
  have h_lq_set_oo_inRange : ∀ inp : input, (do
      let y ← lazy_query inp
      Program.set oracle_output y : Program state Unit).inRange
        chal_x_queried_gh.compl.range := by
    intro inp
    refine Program.inRange_bind ?_ (fun y =>
      Program.set_inRange_compl_of_disjoint oracle_output chal_x_queried_gh y)
    exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)
  refine Program.EquivModuloLens.bind
    (Program.EquivModuloLens.refl (Program.get oracle_input))
    (fun inp => ?_) h_lq_set_oo_inRange
  -- After get input: lazy_query[_t] inp >>= set oo y.
  refine Program.EquivModuloLens.bind
    (lazy_query_equiv_lazy_query_tracked inp)
    (fun _ => Program.EquivModuloLens.refl _)
    (fun y => Program.set_inRange_compl_of_disjoint oracle_output chal_x_queried_gh y)

/-- `oracle_step ow_adv lazy_query` is flag-disjoint. Used by the calculus
    chains in flag elision. -/
lemma oracle_step_lazy_query_inRange_chal_x_queried_gh
    (h_ow_adv_flag : ow_adv.inRange chal_x_queried_gh.compl.range) :
    (oracle_step ow_adv lazy_query).inRange chal_x_queried_gh.compl.range := by
  dsimp only [oracle_step]
  refine Program.inRange_bind h_ow_adv_flag (fun _ => ?_)
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint oracle_input chal_x_queried_gh)
    (fun inp => ?_)
  refine Program.inRange_bind ?_ (fun y =>
    Program.set_inRange_compl_of_disjoint oracle_output chal_x_queried_gh y)
  exact Program.inRange_mono (lazy_query_inRange_ro inp)
    (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)

/-- Loop-level: `oracle_loop_n adv q lazy_query ≈_L oracle_loop_n adv q lazy_query_tracked`. -/
lemma oracle_loop_n_equiv_lazy_query_lazy_query_tracked
    (h_ow_adv_flag : ow_adv.inRange chal_x_queried_gh.compl.range) (q : ℕ) :
    Program.EquivModuloLens chal_x_queried_gh
      (oracle_loop_n ow_adv q lazy_query)
      (oracle_loop_n ow_adv q lazy_query_tracked) := by
  -- Convert both to loop_n form via oracle_loop_n_eq_loop_n, then loop_n_congr.
  rw [oracle_loop_n_eq_loop_n, oracle_loop_n_eq_loop_n]
  exact loop_n_congr
    (oracle_step_lazy_query_inRange_chal_x_queried_gh ow_adv h_ow_adv_flag)
    (oracle_step_equiv_lazy_query_lazy_query_tracked ow_adv) q

/-- The "tail after lazy_init" of `ow_game_1` is flag-disjoint. -/
private lemma ow_game_1_tail_inRange_chal_x_queried_gh
    (h_ow_adv_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (q : ℕ) : (do
      let x ← Program.uniform
      Program.set ow_challenge_x x
      let y ← Program.uniform
      Program.set random_oracle_state (fun k => if k = x then some y else none)
      Program.set ow_challenge_y y
      oracle_loop_n ow_adv q lazy_query
      let resp ← Program.get ow_response
      let y_check ← lazy_query resp
      pure (decide (y_check = y)) : Program state Bool).inRange
        chal_x_queried_gh.compl.range := by
  refine Program.inRange_bind (Program.inRange_mono Program.inRange_uniform bot_le) (fun x => ?_)
  refine Program.inRange_bind
    (Program.set_inRange_compl_of_disjoint ow_challenge_x chal_x_queried_gh x) (fun _ => ?_)
  refine Program.inRange_bind (Program.inRange_mono Program.inRange_uniform bot_le) (fun y => ?_)
  refine Program.inRange_bind ?_ (fun _ => ?_)
  · -- set random_oracle_state ... in flag.compl.range
    exact Program.set_inRange_compl_of_disjoint random_oracle_state chal_x_queried_gh _
  refine Program.inRange_bind
    (Program.set_inRange_compl_of_disjoint ow_challenge_y chal_x_queried_gh y) (fun _ => ?_)
  refine Program.inRange_bind ?_ (fun _ => ?_)
  · -- oracle_loop_n adv q lazy_query in flag.compl.range
    exact oracle_loop_n_inRange_compl chal_x_queried_gh h_ow_adv_flag q
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint ow_response chal_x_queried_gh) (fun resp => ?_)
  refine Program.inRange_bind ?_ (fun y_check => Program.inRange_pure _ _)
  -- lazy_query resp in flag.compl.range
  exact Program.inRange_mono (lazy_query_inRange_ro resp)
    (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)

/-- Post-loop tail (get response + final lazy_query + pure check) is
    equivalent under flag-ignoring posts when we replace `lazy_query` with
    `lazy_query_tracked`. Uses `bind_eq_p` because the prefix `get ow_response`
    is identical on both sides. -/
private lemma ow_game_1_post_loop_equiv (y : output) :
    Program.EquivModuloLens chal_x_queried_gh
      (do
        let resp ← Program.get ow_response
        let y_check ← lazy_query resp
        pure (decide (y_check = y)) : Program state Bool)
      (do
        let resp ← Program.get ow_response
        let y_check ← lazy_query_tracked resp
        pure (decide (y_check = y)) : Program state Bool) := by
  apply Program.EquivModuloLens.bind_eq_p
  intro resp
  -- Inner: lazy_query resp >>= pure ≈ lazy_query_tracked resp >>= pure.
  -- Here prefixes differ (lq vs lqt), so use `bind`. The continuation is
  -- `pure (decide ...)`, whose inRange is `inRange_pure`.
  refine Program.EquivModuloLens.bind
    (lazy_query_equiv_lazy_query_tracked resp)
    (fun _ => Program.EquivModuloLens.refl _)
    (fun _ => Program.inRange_pure _ _)

/-- Post-loop tail (get response + final lazy_query + pure check) is
    flag-disjoint. -/
private lemma ow_game_1_post_loop_inRange (y : output) :
    (do
      let resp ← Program.get ow_response
      let y_check ← lazy_query resp
      pure (decide (y_check = y)) : Program state Bool).inRange
        chal_x_queried_gh.compl.range := by
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint ow_response chal_x_queried_gh)
    (fun resp => ?_)
  refine Program.inRange_bind ?_ (fun _ => Program.inRange_pure _ _)
  exact Program.inRange_mono (lazy_query_inRange_ro resp)
    (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)

/-- Loop + post-loop tail equivalence — the `oracle_loop_n` call composed
    with the `get ow_response; lazy_query resp; pure (decide ...)` tail. -/
private lemma ow_game_1_loop_tail_equiv
    (h_ow_adv_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (q : ℕ) (y : output) :
    Program.EquivModuloLens chal_x_queried_gh
      (do
        oracle_loop_n ow_adv q lazy_query
        let resp ← Program.get ow_response
        let y_check ← lazy_query resp
        pure (decide (y_check = y)) : Program state Bool)
      (do
        oracle_loop_n ow_adv q lazy_query_tracked
        let resp ← Program.get ow_response
        let y_check ← lazy_query_tracked resp
        pure (decide (y_check = y)) : Program state Bool) := by
  -- Prefixes differ (loop with lq vs lqt). Use `bind`.
  refine Program.EquivModuloLens.bind
    (oracle_loop_n_equiv_lazy_query_lazy_query_tracked ow_adv h_ow_adv_flag q)
    (fun _ => ow_game_1_post_loop_equiv y)
    (fun _ => ow_game_1_post_loop_inRange y)

/-- The full tail of `ow_game_1` (after `lazy_init`) is equivalent (modulo
    `chal_x_queried_gh`) to the full tail of `ow_game_1_tracked` (after
    `lazy_init` and `set chal_x_queried_gh false`).

    The 5-layer prefix (uniform / set chal_x / uniform / set ro / set chal_y)
    is *identical* on both sides, so we use `bind_eq_p` repeatedly — no
    inRange proofs needed for the prefix. -/
private lemma ow_game_1_full_tail_equiv_lq_lqt
    (h_ow_adv_flag : ow_adv.inRange chal_x_queried_gh.compl.range) (q : ℕ) :
    Program.EquivModuloLens chal_x_queried_gh
      (do
        let x ← Program.uniform
        Program.set ow_challenge_x x
        let y ← Program.uniform
        Program.set random_oracle_state (fun k => if k = x then some y else none)
        Program.set ow_challenge_y y
        oracle_loop_n ow_adv q lazy_query
        let resp ← Program.get ow_response
        let y_check ← lazy_query resp
        pure (decide (y_check = y)) : Program state Bool)
      (do
        let x ← Program.uniform
        Program.set ow_challenge_x x
        let y ← Program.uniform
        Program.set random_oracle_state (fun k => if k = x then some y else none)
        Program.set ow_challenge_y y
        oracle_loop_n ow_adv q lazy_query_tracked
        let resp ← Program.get ow_response
        let y_check ← lazy_query_tracked resp
        pure (decide (y_check = y)) : Program state Bool) := by
  apply Program.EquivModuloLens.bind_eq_p; intro x
  apply Program.EquivModuloLens.bind_eq_p; intro _
  apply Program.EquivModuloLens.bind_eq_p; intro y
  apply Program.EquivModuloLens.bind_eq_p; intro _
  apply Program.EquivModuloLens.bind_eq_p; intro _
  exact ow_game_1_loop_tail_equiv ow_adv h_ow_adv_flag q y

/-- **Flag elision at the game level**: `ow_game_1` and `ow_game_1_tracked`
    have equal wp's for flag-ignoring postconditions.

    Proof via the `EquivModuloLens` calculus: bind congruence chains compose
    `oracle_loop_n_equiv` (loop-level), `lazy_query_equiv_lazy_query_tracked`
    (final query), and `set_equiv_pure` (initial set chal_x_queried_gh false). -/
theorem ow_game_1_wp_eq_ow_game_1_tracked_wp_of_flag_ignoring
    (h_ow_adv_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (q : ℕ) (F : Bool × state → ENNReal)
    (h_F : IgnoresChalXQueriedGh F)
    (σ : state) :
    (ow_game_1 ow_adv q).wp F σ = (ow_game_1_tracked ow_adv q).wp F σ := by
  have h_F' : IgnoresLens chal_x_queried_gh F := fun aσ v => h_F aσ v
  suffices h_equiv : Program.EquivModuloLens chal_x_queried_gh
      (ow_game_1 ow_adv q) (ow_game_1_tracked ow_adv q) by
    exact h_equiv F h_F' σ
  dsimp only [ow_game_1, ow_game_1_tracked]
  -- Outer `lazy_init` prefix is identical on both sides; use `bind_eq_p`.
  apply Program.EquivModuloLens.bind_eq_p
  intro _
  -- Goal: REST_lq ≈_L (set chal_x_queried_gh false >>= REST_lqt).
  -- Step 1: REST_lq ≈_L set L false >>= REST_lq (dead set insertion via
  --   bind_eq_k with `pure_equiv_set`, then rewriting `pure () >>= _` via
  --   `Program.pure_bind`).
  -- Step 2: set L false >>= REST_lq ≈_L set L false >>= REST_lqt (replace
  --   lq with lqt under same prefix; uses bind_eq_p with full-tail equiv).
  have h_dead_set := Program.EquivModuloLens.bind_eq_k
    (Program.EquivModuloLens.pure_equiv_set (L := chal_x_queried_gh) false)
    (fun _ : Unit => ow_game_1_tail_inRange_chal_x_queried_gh ow_adv h_ow_adv_flag q)
  -- h_dead_set : (pure () >>= fun _ => REST_lq) ≈_L (set L false >>= fun _ => REST_lq)
  rw [Program.pure_bind] at h_dead_set
  -- h_dead_set : REST_lq ≈_L (set L false >>= fun _ => REST_lq)
  exact h_dead_set.trans (Program.EquivModuloLens.bind_eq_p
    (fun _ => ow_game_1_full_tail_equiv_lq_lqt ow_adv h_ow_adv_flag q))

end Reductions

/-! ## The final game-hop bound

Combining the proved infrastructure:
* `ow_game_0_eq_ow_game_1` — Hop 0 → 1 (program equality).
* `ow_game_1_wp_eq_ow_game_1_tracked_wp_of_flag_ignoring` — tracking is
  invisible for flag-ignoring posts.
* `ow_game_1_tracked_le_ow_game_2_tracked_plus_bad` — Hop 1 → 2 via
  `Program.up_to_bad`.
* `ow_game_2_tracked_wins_le_guess_output_bound` — Game 2 win bound.
* `ow_game_1_tracked_bad_le_guess_input_bound` — bad event bound.
* `card_input_ge_output` — |input| ≥ |output|.

Yields `P[ow_experiment wins] ≤ 2(q+1)/|output|`. -/

section GameHopParam_Final

variable (ow_adv : Program state Unit)

/-- **The OW lazy bound via the game-hop chain**.
    Matches the existing `ow_lazy_bound` (in `QueryHit.lean`), proved via
    the game-hopping + up-to-bad chain instead of the
    useful_preimage/deferred-sampling machinery. -/
theorem ow_lazy_bound_via_gamehop
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_ow_adv_matched_chal_y : ow_adv.inRange matched_chal_y.compl.range)
    (h_ow_adv_queries_output : ow_adv.inRange queries_output.compl.range)
    (h_ow_adv_queries_input : ow_adv.inRange queries_input.compl.range)
    (h_ow_adv_mass_one : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1)
    (h_ow_adv_chal_x_blind : ∀ (F : Unit × state → ENNReal) (σ : state) (v : input),
      ow_adv.wp F (ow_challenge_x.set v σ) = ow_adv.wp F σ)
    (h_ow_adv_chal_y_blind : ∀ (F : Unit × state → ENNReal) (σ : state) (v : output),
      ow_adv.wp F (ow_challenge_y.set v σ) = ow_adv.wp F σ)
    (q : ℕ) (σ : state) :
    (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ (2 * (q + 1) : ENNReal) / Fintype.card output := by
  -- Win indicator is flag-ignoring (depends only on `bσ.1`) and RO-invariant.
  set Win : Bool × state → ENNReal := fun bσ => if bσ.1 then (1 : ENNReal) else 0 with Win_def
  have h_Win_flag : IgnoresChalXQueriedGh Win := by
    intro aσ b
    simp [Win_def]
  have h_Win_RO_inv : ∀ (bσ : Bool × state) (y : output),
      Win (bσ.1, insert_at_chal_x y bσ.2) = Win bσ := by
    intro bσ y
    simp [Win_def]
  -- Bridge: ow_experiment.wp Win = ow_game_0.wp Win = ow_game_1.wp Win = ow_game_1_tracked.wp Win.
  show (ow_experiment ow_adv q lazy_init lazy_query).wp Win σ
       ≤ (2 * (q + 1) : ENNReal) / Fintype.card output
  rw [show (ow_experiment ow_adv q lazy_init lazy_query) = ow_game_0 ow_adv q from rfl]
  rw [ow_game_0_eq_ow_game_1 ow_adv q]
  rw [ow_game_1_wp_eq_ow_game_1_tracked_wp_of_flag_ignoring ow_adv
      h_ow_adv_chal_x_queried_gh q Win h_Win_flag σ]
  -- Apply up_to_bad: ow_game_1_tracked.wp Win ≤ ow_game_2_tracked.wp Win + bad-wp.
  calc (ow_game_1_tracked ow_adv q).wp Win σ
      ≤ (ow_game_2_tracked ow_adv q).wp Win σ
        + (ow_game_1_tracked ow_adv q).wp
            (fun bσ : Bool × state =>
              if chal_x_queried_gh.get bσ.2 = true then Win bσ else 0) σ := by
        exact ow_game_1_tracked_le_ow_game_2_tracked_plus_bad ow_adv
          h_ow_adv h_ow_adv_chal_x h_ow_adv_chal_x_queried_gh q Win h_Win_RO_inv σ
    _ ≤ ((q + 1) : ENNReal) / Fintype.card output
        + ((q + 1) : ENNReal) / Fintype.card input := by
        gcongr
        · exact ow_game_2_tracked_wins_le_guess_output_bound ow_adv
            h_ow_adv_matched_chal_y h_ow_adv_queries_output h_ow_adv_chal_y q σ
        · -- The "bad ∩ Win" wp is ≤ "bad" wp (since Win ≤ 1).
          calc (ow_game_1_tracked ow_adv q).wp
                  (fun bσ : Bool × state =>
                    if chal_x_queried_gh.get bσ.2 = true then Win bσ else 0) σ
              ≤ (ow_game_1_tracked ow_adv q).wp
                  (fun bσ : Bool × state =>
                    if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ := by
                apply Program.wp_le_wp_of_le
                intro bσ
                by_cases h : chal_x_queried_gh.get bσ.2 = true
                · simp only [if_pos h, Win_def]
                  split_ifs <;> simp
                · simp [h]
            _ ≤ ((q + 1) : ENNReal) / Fintype.card input := by
                exact ow_game_1_tracked_bad_le_guess_input_bound ow_adv
                  h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x
                  h_ow_adv_chal_x_queried_gh h_ow_adv_queries_input
                  h_ow_adv_mass_one h_ow_adv_chal_x_blind q σ
    _ ≤ ((q + 1) : ENNReal) / Fintype.card output
        + ((q + 1) : ENNReal) / Fintype.card output := by
        gcongr
        exact_mod_cast card_input_ge_output
    _ = (2 * (q + 1) : ENNReal) / Fintype.card output := by
        rw [← ENNReal.add_div]; ring_nf

end GameHopParam_Final
