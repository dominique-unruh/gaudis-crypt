import PlonkLean.RO
import PlonkLean.RO.OneWayness

/-!
# Game-hopping proof of one-wayness

An alternative proof of the OW lazy bound
`P[ow_experiment wins] ≤ 2(q+1)/|output|` via three games and one
up-to-bad analysis, with both probability bounds reduced to a single
unifying "guessing game" lemma.

See `notes/RO/OW_GameHop_Plan.md` for the full plan.

This file is being built incrementally. Stubs use `sorry`. The existing
proof in `PlonkLean/RO/OneWayness.lean` (Layer A_OW / C_OW / D_OW +
`PlonkLean/RO/QueryHit.lean`) remains intact.
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

/-! ## Game 2 — drop the (x ↦ y) insertion

Same as Game 1, but the `RO ← RO[x ↦ y]` step is removed. The adversary
sees a uniformly-random `chal_y` that is *not* reflected in the RO. This
is the "up-to-bad" game: identical to Game 1 unless the adversary queries
the oracle at `x`. -/

noncomputable def ow_game_2 (q : ℕ) : Program state Bool := do
  lazy_init
  let x ← Program.uniform
  Program.set ow_challenge_x x
  let y ← Program.uniform
  -- No RO insertion!
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

/-- Frame variant: at the point in a program where the RO is empty
    everywhere (the state immediately after `lazy_init`), one `lazy_query`
    can be swapped for an explicit `uniform >>= set RO` pair, with the
    continuation unchanged. -/
private lemma swap_lazy_query_after_empty_RO
    {α : Type} (k : output → Program state α) (σ : state)
    (h_empty : random_oracle_state.get σ = fun _ => none) (F : α × state → ENNReal)
    (inp : input) :
    (lazy_query inp >>= k).wp F σ
    = (Program.uniform >>= fun y =>
        Program.set random_oracle_state
          (fun k' => if k' = inp then some y else none) >>= fun _ =>
        k y).wp F σ := by
  rw [wp_bind, lazy_query_on_totally_empty_RO inp σ h_empty
      (fun yσ : output × state => (k yσ.1).wp F yσ.2)]
  -- Both sides are now `Program.uniform.wp (fun y => ... ) σ`. Reduce.
  simp only [wp_bind, wp_uniform, wp_set, wp_pure]

/-- The lazy_query swap, framed as a program equality (not wp). Both Game 0
    and Game 1 instantiate this with the OW-experiment suffix as `rest`. -/
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

-- Note: in the `guess_experiment`-based design, the match-check is placed
-- OUTSIDE the lazy_query, in `guess_experiment`'s body itself. So we
-- don't need a dedicated `lazy_query_with_match` — `ow_game_2_with_match`
-- uses `lazy_query_tracked` and adds the match-check via guess_experiment's
-- loop body / final body structure.

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

/-- **Intermediate game for the bridge proof.** Same body as `ow_game_2_tracked`
    but returns `(y_check, y, decide(y_check = y))` instead of just the Bool.
    The first two components match `ow_game_2_with_match`'s output structure,
    enabling the marginal-equality-based bridge. -/
noncomputable def ow_game_2_tracked_p (q : ℕ) : Program state (output × output × Bool) := do
  lazy_init
  Program.set chal_x_queried_gh false
  let x ← Program.uniform
  Program.set ow_challenge_x x
  let y ← Program.uniform
  Program.set ow_challenge_y y
  oracle_loop_n ow_adv q lazy_query_tracked
  let resp ← Program.get ow_response
  let y_check ← lazy_query_tracked resp
  pure (y_check, y, decide (y_check = y))

/-- **Step 2 of the bridge:** `ow_game_2_tracked.wp F_win σ` equals
    `ow_game_2_tracked_p.wp F_match σ` where F_match is the (output-only)
    comparison `bσ.1.1 = bσ.1.2.1`. Both programs have identical bodies;
    only the final `pure` differs, and the posts evaluate to the same value
    on the respective return values.

    Critically, this uses F_match (not F_proj) on the RHS — F_match compares
    `bσ.1.1 = bσ.1.2.1` directly (output-only), aligning with the bridge's
    target RHS post. The Bool component in ow_game_2_tracked_p's return is
    just `decide(y_check = y)`, so `bσ.1.1 = bσ.1.2.1` evaluates to the same
    as F_win's check `bσ.1 = true`. -/
private lemma ow_game_2_tracked_wp_eq_ow_game_2_tracked_p_wp
    (q : ℕ) (σ : state) :
    (ow_game_2_tracked ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    = (ow_game_2_tracked_p ow_adv q).wp
        (fun bσ : (output × output × Bool) × state =>
          if bσ.1.1 = bσ.1.2.1 then (1 : ENNReal) else 0) σ := by
  unfold ow_game_2_tracked ow_game_2_tracked_p
  simp only [wp_bind, wp_pure, decide_eq_true_eq]

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

/-- **Game 2 with matched tracking** — structurally close to `ow_game_2_tracked_p`.

    Same prefix and loop structure as `ow_game_2_tracked_p`, with the
    following ADDITIONS (each surgically inserted to track matched_chal_y):
    1. `set matched_chal_y false` after the env prefix.
    2. In-loop match-check: `if y_val = y then set matched_chal_y true`
       using the *bound* `y_val` and `y` (no state reads).
    3. Final match-check: `if y_check = y then set matched_chal_y true`.
    4. Trailing `get matched_chal_y` reading into `m`.
    5. Pure tuple uses `m` instead of `decide (y_check = y)`.

    Crucially, the match-checks use BOUND VARIABLES (not state reads),
    so they are `wp_conditional_set_disjoint_no_op`-style invisible for
    matched_chal_y-ignoring posts — making the bridge to `ow_game_2_tracked_p`
    tractable. -/
noncomputable def ow_game_2_with_match (q : ℕ) : Program state (output × output × Bool) := do
  lazy_init
  Program.set chal_x_queried_gh false
  let x ← Program.uniform
  Program.set ow_challenge_x x
  let y ← Program.uniform
  Program.set ow_challenge_y y
  Program.set matched_chal_y false
  loop_n q (do
    ow_adv
    let inp ← Program.get oracle_input
    let y_val ← lazy_query_tracked inp
    Program.set oracle_output y_val
    if y_val = y then Program.set matched_chal_y true else pure ())
  let resp ← Program.get ow_response
  let y_check ← lazy_query_tracked resp
  if y_check = y then Program.set matched_chal_y true else pure ()
  let m ← Program.get matched_chal_y
  pure (y_check, y, m)

/-- **Game 2 as a `guess_experiment` instance.** The matched flag is
    `matched_chal_y`; the target is the uniformly-sampled `chal_y`. Body
    and final use the BOUND target `y` for explicit match-checks
    (`if y_val = y then ...`), avoiding state reads. The result is just
    the matched Bool (no extra output tuple).

    Same structure as `ow_game_2_with_match` minus the trailing `pure
    (y_check, y, m)` reconstruction — that's added back via a bridge
    when needed. -/
noncomputable def guess_experiment_game_2 (q : ℕ) : Program state Bool :=
  guess_experiment
    (env := do
      lazy_init
      Program.set chal_x_queried_gh false
      let x ← Program.uniform
      Program.set ow_challenge_x x)
    (sample_target := Program.uniform)
    (target_var := ow_challenge_y)
    (matched_var := matched_chal_y)
    (body := fun y => do
      ow_adv
      let inp ← Program.get oracle_input
      let y_val ← lazy_query_tracked inp
      Program.set oracle_output y_val
      if y_val = y then Program.set matched_chal_y true else pure ())
    (final := fun y => do
      let resp ← Program.get ow_response
      let y_val ← lazy_query_tracked resp
      if y_val = y then Program.set matched_chal_y true else pure ())
    (n := q)

/-- **Game 1 as a `guess_experiment` instance.** The matched flag is
    `chal_x_queried_gh`; the target is the uniformly-sampled `chal_x`.
    Body and final use `lazy_query_tracked` which has the input-match
    tracking INTERNAL (it sets `chal_x_queried_gh` when `inp = chal_x`).
    The body therefore IGNORES its target parameter — the matching is
    handled inside `lazy_query_tracked`.

    Same structure as `ow_game_1_tracked` minus the RO pre-programming
    and the trailing win-pure — those add back via a bridge when needed
    (for the bad-event bound, the pre-programming doesn't affect the
    flag distribution and can be omitted). -/
noncomputable def guess_experiment_game_1 (q : ℕ) : Program state Bool :=
  guess_experiment
    (env := do
      lazy_init)
    (sample_target := Program.uniform)
    (target_var := ow_challenge_x)
    (matched_var := chal_x_queried_gh)
    (body := fun _x => do  -- Body ignores target; lazy_query_tracked checks internally.
      ow_adv
      let inp ← Program.get oracle_input
      let y ← lazy_query_tracked inp
      Program.set oracle_output y)
    (final := fun _x => do
      let resp ← Program.get ow_response
      let y ← lazy_query_tracked resp
      Program.set oracle_output y)
    (n := q)

/-! ### Bridge lemmas: ow_game_*_tracked ↔ guess_experiment_game_*

The cryptographic chain uses these bridges to relate the OW experiment's
win/bad events to the matched flag of the corresponding `guess_experiment`
instance. The matched flag is then bounded by `guess_experiment_wp_bound`. -/

section Bridges

variable (ow_adv : Program state Unit)

/-- **Game 2 bridge**: `ow_game_2_with_match`'s matched-indicator wp equals
    `guess_experiment_game_2`'s output Bool wp.

    Both programs run the identical matched_chal_y trajectory. They differ
    only at the final pure: `ow_game_2_with_match` reconstructs the tuple
    `(y_check, y, m)`, while `guess_experiment_game_2` just outputs `m`.
    The matched indicator on the tuple's `.1.2.2` projects to exactly `m`,
    matching the Bool output's `.1` projection.

    Provable by: (i) Program equality between `ow_game_2_with_match` and
    `guess_experiment_game_2 >>= (get oo >>= fun y_check => get chal_y >>=
    fun y => pure (y_check, y, m))`; (ii) wp simplification. Deferred. -/
lemma ow_game_2_with_match_matched_wp_eq_guess_experiment_game_2_wp
    (q : ℕ) (σ : state) :
    (ow_game_2_with_match ow_adv q).wp
        (fun bσ : (output × output × Bool) × state =>
          if bσ.1.2.2 then (1 : ENNReal) else 0) σ
    = (guess_experiment_game_2 ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  -- Both programs run the identical matched_chal_y trajectory; the difference
  -- is only at the final pure (tuple vs Bool). Deferred — full proof needs
  -- careful chained `congrArg`/`funext` through ~10 binds, ending in a
  -- case-split on `y_check = y` where both posts compute the same value.
  sorry

/-- **Game 1 bridge**: `ow_game_1_tracked`'s bad-indicator wp (reading
    `chal_x_queried_gh` from state at end) equals `guess_experiment_game_1`'s
    output Bool wp (returning matched flag at end).

    Conceptual equivalence: both programs track input matches via
    `chal_x_queried_gh` inside `lazy_query_tracked`; the bad event in
    `ow_game_1_tracked` is "some query input matched chal_x" =
    matched flag at end = `guess_experiment_game_1`'s output.

    Differences between the programs:
    1. `ow_game_1_tracked` pre-programs RO at `(chal_x, chal_y)`.
       `guess_experiment_game_1` does not.
    2. `ow_game_1_tracked` returns `decide (y_check = y)` (win flag),
       not the matched flag.
    3. `ow_game_1_tracked` samples chal_y and stores it in ow_challenge_y.

    For the bad indicator (state read on `chal_x_queried_gh`), differences
    1-3 don't affect the bad probability (they don't read or modify
    `chal_x_queried_gh`). Deferred. -/
lemma ow_game_1_tracked_bad_wp_eq_guess_experiment_game_1_wp
    (q : ℕ) (σ : state) :
    (ow_game_1_tracked ow_adv q).wp
        (fun bσ : Bool × state =>
          if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
    = (guess_experiment_game_1 ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ := by
  sorry

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

/-- **`lazy_query_tracked` writes its output**. After a tracked query at `x`,
    the RO contains `x ↦ some y_check`. Same property as
    `lazy_query_wp_writes_output` for the tracked variant; the flag-update
    step is RO-disjoint so the property propagates through. -/
private lemma lazy_query_tracked_wp_writes_output
    (x : input) (F : output × state → ENNReal) (σ : state) :
    (lazy_query_tracked x).wp F σ
    = (lazy_query_tracked x).wp
        (fun yσ : output × state =>
          if random_oracle_state.get yσ.2 x = some yσ.1 then F yσ else 0) σ := by
  rw [lazy_query_tracked_wp_decompose]
  conv_rhs => rw [lazy_query_tracked_wp_decompose]
  rw [lazy_query_wp_strengthen
    (I := fun y σ' => random_oracle_state.get σ' x = some y)
    (h_cache := fun _ h_cache => h_cache)
    (h_fresh := fun value _ => by
      show random_oracle_state.get _ x = some value
      rw [random_oracle_state.set_get]; exact if_pos rfl)]
  haveI : disjoint chal_x_queried_gh random_oracle_state := disjoint_chal_x_queried_gh_ro
  congr 1
  funext yσ'
  have h_flag_RO : random_oracle_state.get (chal_x_queried_gh.set true yσ'.2) x
                 = random_oracle_state.get yσ'.2 x := by
    rw [random_oracle_state.get_of_disjoint_set]
  by_cases h_RO : random_oracle_state.get yσ'.2 x = some yσ'.1
  · simp only [if_pos h_RO]
    by_cases h_chal_x : x = ow_challenge_x.get yσ'.2
    · simp only [if_pos h_chal_x]
      rw [h_flag_RO, if_pos h_RO]
    · simp only [if_neg h_chal_x, if_pos h_RO]
  · simp only [if_neg h_RO]
    by_cases h_chal_x : x = ow_challenge_x.get yσ'.2
    · simp only [if_pos h_chal_x]
      rw [h_flag_RO, if_neg h_RO]
    · simp only [if_neg h_chal_x, if_neg h_RO]

/-- The state `insert_at_chal_x y_chal σ` has the same `ow_challenge_x` as
    `σ` (the insertion only touches RO, which is disjoint from chal_x). -/
private lemma chal_x_get_insert_at_chal_x (σ : state) (y_chal : output) :
    ow_challenge_x.get (insert_at_chal_x y_chal σ) = ow_challenge_x.get σ := by
  unfold insert_at_chal_x
  exact ow_challenge_x.get_of_disjoint_set _ _ _

/-- The state `insert_at_chal_x y_chal σ` has the same `chal_x_queried_gh`
    as `σ`. -/
private lemma chal_x_queried_gh_get_insert_at_chal_x (σ : state) (y_chal : output) :
    chal_x_queried_gh.get (insert_at_chal_x y_chal σ) = chal_x_queried_gh.get σ := by
  unfold insert_at_chal_x
  exact chal_x_queried_gh.get_of_disjoint_set _ _ _

/-- `random_oracle_state.get` at `insert_at_chal_x` keys away from `chal_x σ`
    agrees with the original. -/
private lemma RO_get_insert_at_chal_x_of_neq (σ : state) (y_chal : output)
    (k : input) (h_neq : k ≠ ow_challenge_x.get σ) :
    random_oracle_state.get (insert_at_chal_x y_chal σ) k
    = random_oracle_state.get σ k := by
  unfold insert_at_chal_x
  rw [random_oracle_state.set_get]
  simp [h_neq]

/-- `random_oracle_state.get` at `insert_at_chal_x` evaluated at the chal_x key
    yields the inserted value. -/
private lemma RO_get_insert_at_chal_x_at_chal_x (σ : state) (y_chal : output) :
    random_oracle_state.get (insert_at_chal_x y_chal σ) (ow_challenge_x.get σ)
    = some y_chal := by
  unfold insert_at_chal_x
  rw [random_oracle_state.set_get]
  simp

/-- **Generic RO-set commutativity for `lazy_query`**: writes to `RO[x]`
    commute with `lazy_query inp` when `inp ≠ x`. The lazy_query at inp
    doesn't touch RO[x], so any pre-existing write to RO[x] passes through.
    Adapted from `RO_setentry_neq_commutes_lazy_query_set_oracle_output`,
    without the `set oracle_output` continuation. -/
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

/-- **Tail invariance under RO[chal_x] insertion**. The portion of both
    games starting from `set ow_challenge_y y` produces equal wp's at `σ`
    and `insert_at_chal_x y_chal σ`. Composes:
    `chal_y`-RO commutativity, the loop-level invariance, RO-disjointness
    of `ow_response`, the per-step invariance for `lazy_query_tracked`,
    and `F`'s RO-invariance for the final `pure`. -/
private lemma ow_tail_wp_invariant_under_RO_chal_x_set
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (q : ℕ) (y : output) (F : Bool × state → ENNReal)
    (h_F_bad_zero : ∀ bσ : Bool × state, chal_x_queried_gh.get bσ.2 = true → F bσ = 0)
    (h_F_RO_inv : ∀ (b : Bool) (σ' : state) (y' : output),
       F (b, insert_at_chal_x y' σ') = F (b, σ'))
    (σ : state) (y_chal : output) :
    (Program.set ow_challenge_y y >>= fun _ =>
      oracle_loop_n ow_adv q lazy_query_tracked >>= fun _ =>
      Program.get ow_response >>= fun resp =>
      lazy_query_tracked resp >>= fun y_check =>
      (pure (decide (y_check = y)) : Program state Bool)).wp F
        (insert_at_chal_x y_chal σ)
    = (Program.set ow_challenge_y y >>= fun _ =>
      oracle_loop_n ow_adv q lazy_query_tracked >>= fun _ =>
      Program.get ow_response >>= fun resp =>
      lazy_query_tracked resp >>= fun y_check =>
      (pure (decide (y_check = y)) : Program state Bool)).wp F σ := by
  -- Step 1: Unfold the outer bind on `set chal_y y` via wp_set.
  -- We get the remaining program's wp at `chal_y.set y (insert σ)` vs `chal_y.set y σ`.
  haveI : disjoint ow_challenge_y random_oracle_state := disjoint_ow_challenge_y_ro
  haveI : disjoint ow_challenge_y ow_challenge_x := disjoint_ow_challenge_y_ow_challenge_x
  simp only [wp_bind, wp_set]
  -- chal_y.set y (insert σ) = insert (chal_y.set y σ): commute set-set via disjointness.
  have h_chal_y_commute :
      ow_challenge_y.set y (insert_at_chal_x y_chal σ)
      = insert_at_chal_x y_chal (ow_challenge_y.set y σ) := by
    unfold insert_at_chal_x
    rw [(disjoint_ow_challenge_y_ro).commute]
    congr 1
    funext k
    rw [ow_challenge_x.get_of_disjoint_set]
    rw [random_oracle_state.get_of_disjoint_set]
  rw [h_chal_y_commute]
  -- Step 2: Apply loop-level RO[chal_x] invariance.
  refine oracle_loop_n_lazy_query_tracked_wp_invariant_under_RO_chal_x_set
    ow_adv h_ow_adv h_ow_adv_chal_x h_ow_adv_chal_x_queried_gh q _ ?_ ?_
    (ow_challenge_y.set y σ) y_chal
  · -- post bad-vanishing: starting at flag-true, the inner wp = 0.
    intro aσ_loop h_flag
    -- inner = (get resp >>= lq_t resp >>= pure decide).wp F aσ_loop.2 at flag-true state.
    -- get resp's result is independent of state; lq_t at flag-true with F bad-vanishing gives 0.
    simp only [wp_bind, wp_get]
    -- Now: (lq_t (resp.get aσ_loop.2)).wp (fun yσ_lq => (pure ...).wp F yσ_lq.2) aσ_loop.2 = 0.
    haveI : disjoint chal_x_queried_gh ow_response :=
      disjoint_chal_x_queried_gh_ow_response
    apply lazy_query_tracked_wp_at_flag_true _ _ _ aσ_loop.2 h_flag
    intro yσ_lq h_yσ_lq_flag
    rw [wp_pure]
    exact h_F_bad_zero _ h_yσ_lq_flag
  · -- post RO[chal_x]-inv.
    intro a σ_inner y_inner
    -- inner.wp F (insert σ_inner) = inner.wp F σ_inner.
    -- Unfold: get resp doesn't change state; resp.get (insert σ_inner) = resp.get σ_inner.
    -- Then lq_t's per-step invariance.
    simp only [wp_bind, wp_get]
    have h_resp_get : ow_response.get (insert_at_chal_x y_inner σ_inner)
                    = ow_response.get σ_inner := by
      unfold insert_at_chal_x
      rw [ow_response.get_of_disjoint_set]
    rw [h_resp_get]
    -- Now: (lq_t (resp.get σ_inner)).wp (fun yσ_lq => F (decide (yσ_lq.1=y), yσ_lq.2)) (insert σ_inner)
    --    = (lq_t (resp.get σ_inner)).wp (...) σ_inner
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

/-- **Identical-until-bad** at the game level. For posts that vanish on
    `chal_x_queried_gh = true` outcomes AND are RO[chal_x]-invariant, tracked
    Game 1 and tracked Game 2 produce equal wp's.

    The argument is structural: Games 1 and 2 share the prefix
    `lazy_init >>= set flag false >>= uniform x >>= set chal_x x >>= uniform y`;
    they differ only at the `set random_oracle_state (...)` step in Game 1.
    For the tail program (which is shared between Games 1 and 2 starting
    from RO-different states), the wp is RO[chal_x]-invariant on
    bad-vanishing-and-state-invariant posts. The chain of invariance
    lemmas concludes that Games 1 and 2 produce equal wp's. -/
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

/-- **TODO**. Bound on `guess_experiment`'s matched indicator: each iteration
    has ≤ 1/|T| chance of setting `matched_var := true` (because the target
    is uniformly sampled and revealed only via the lens read inside the body),
    so the union bound over `n+1` iterations gives `(n+1)/|T|`.

    Generic over the body's structure; the body MAY use the bound target `t`
    in match-checks (Game 2 style) or query an oracle that internally tracks
    matches against state-stored target (Game 1 style — `lazy_query_tracked`).
    Deferred. -/
theorem guess_experiment_wp_bound
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (env : Program state Unit) (sample_target : Program state T)
    (target_var : Lens T state) (matched_var : Lens Bool state)
    [disjoint target_var matched_var]
    (body : T → Program state Unit) (final : T → Program state Unit)
    (n : ℕ) (σ : state) :
    (guess_experiment env sample_target target_var matched_var body final n).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ ((n + 1) : ENNReal) / Fintype.card T := by
  sorry

section Reductions

variable (ow_adv : Program state Unit)

/-! ### Game 2 reduction to the matched-flag game (Option B)

The reduction factors through `ow_game_2_with_match`, an instrumented
version of `ow_game_2_tracked` that additionally sets `matched_chal_y` to
`true` whenever a `lazy_query` returns `chal_y`. The chain:

1. `ow_game_2_tracked.wp win = ow_game_2_with_match.wp win` (game
   equivalence — matched tracking is invisible to win-only posts).
2. `ow_game_2_with_match.wp win ≤ ow_game_2_with_match.wp matched`
   (structural — winning means the final lazy_query returned `chal_y`,
   which sets the matched flag).
3. `ow_game_2_with_match.wp matched ≤ (q+1)/|output|` (linear bound —
   each lazy_query has ≤ 1/|output| chance of returning `chal_y`).

Step 3 is the `guess_experiment_wp_bound` specialized to this game. -/

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

/-- **Match-check is wp-invisible** for matched_chal_y-ignoring posts and
    matched_chal_y-disjoint continuations. The match-check pattern is
    `get oo + get chal_y + (if g = t' then set matched true else pure ())`.
    For a continuation `rest` that doesn't touch `matched_chal_y` and a
    post `F` that doesn't depend on `matched_chal_y` content, this whole
    block is a no-op.

    Reusable building block for eliminating match-check operations in the
    Game 2 bridge marginal equality. -/
lemma match_check_invisible
    {α : Type} {rest : Program state α}
    (h_rest : rest.inRange matched_chal_y.compl.range)
    (F : α × state → ENNReal)
    (h_F : ∀ aσ : α × state,
        F (aσ.1, matched_chal_y.set true aσ.2) = F aσ)
    (σ : state) :
    ((Program.get oracle_output >>= fun g =>
        Program.get ow_challenge_y >>= fun t' =>
        (if g = t' then Program.set matched_chal_y true
         else (pure () : Program state Unit))) >>= fun _ => rest).wp F σ
    = rest.wp F σ := by
  -- Reassociate the outer bind so the conditional is bound directly to rest.
  simp only [Program.bind_assoc]
  -- Peel outer get oo.
  rw [wp_bind, wp_get]
  dsimp only
  -- Peel get chal_y.
  rw [wp_bind, wp_get]
  dsimp only
  exact Program.wp_conditional_set_disjoint_no_op
    (oracle_output.get σ = ow_challenge_y.get σ) true h_rest F h_F σ

/-- `loop_n n body` stays in `R` whenever `body` does. -/
lemma loop_n_inRange {R : LensRange state}
    (body : Program state Unit) (h_body : body.inRange R) (n : ℕ) :
    (loop_n n body).inRange R := by
  induction n with
  | zero => exact Program.inRange_pure _ _
  | succ n ih =>
    show (body >>= fun _ => loop_n n body).inRange R
    exact Program.inRange_bind h_body (fun _ => ih)

/-- **The match_check pattern inside a loop is wp-invisible** for posts that
    ignore `matched_chal_y`. Generalizes `match_check_invisible` over the
    `q`-iteration `loop_n` combinator.

    Proof: induction on `n`. Inductive step:
    * Unfold `loop_n` once on both sides.
    * Apply `wp_bind` to peel `body` on both sides.
    * Show post equality via `funext`: for each state σ', the inner
      `(mc >>= fun _ => loop_n n bm).wp F σ' = (loop_n n body).wp F σ'`.
    * Inside: use IH to replace `loop_n n bm` with `loop_n n body` (post-
      function equality via `funext`), then apply `match_check_invisible`
      with `rest := loop_n n body` (`matched_chal_y`-disjoint via
      `loop_n_inRange`).
    * Lift back via `congr_arg`. -/
lemma loop_n_match_check_invisible
    (n : ℕ) (body : Program state Unit)
    (h_body : body.inRange matched_chal_y.compl.range)
    (F : Unit × state → ENNReal)
    (h_F : ∀ aσ : Unit × state,
        F (aσ.1, matched_chal_y.set true aσ.2) = F aσ)
    (σ : state) :
    (loop_n n (body >>= fun _ =>
        (Program.get oracle_output >>= fun g =>
         Program.get ow_challenge_y >>= fun t' =>
         (if g = t' then Program.set matched_chal_y true
          else (pure () : Program state Unit))))).wp F σ
    = (loop_n n body).wp F σ := by
  -- Helper: wp of `loop_n n body` is matched_chal_y-set-invariant on input.
  have h_loop_body_inRange : ∀ k, (loop_n k body).inRange matched_chal_y.compl.range :=
    fun k => loop_n_inRange body h_body k
  have h_loop_set_inv : ∀ k σ',
      (loop_n k body).wp F (matched_chal_y.set true σ') = (loop_n k body).wp F σ' := by
    intro k σ'
    have hf : (fun s : state => matched_chal_y.set true s) ∈
        ((matched_chal_y.compl.range : LensRange state)ᶜ).updates := by
      rw [show ((matched_chal_y.compl.range : LensRange state)ᶜ)
            = matched_chal_y.range from by
            rw [LensRange.complement_range, LensRange.compl_compl]]
      exact ⟨Function.const _ true, Set.mem_univ _, rfl⟩
    rw [Program.wp_shift_input (h_loop_body_inRange k) hf]
    congr 1
    funext xs
    exact h_F xs
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    -- Unfold loop_n one step.
    show ((body >>= fun _ =>
            (Program.get oracle_output >>= fun g =>
             Program.get ow_challenge_y >>= fun t' =>
             (if g = t' then Program.set matched_chal_y true
              else (pure () : Program state Unit)))) >>= fun _ =>
            loop_n n (body >>= fun _ =>
              (Program.get oracle_output >>= fun g =>
               Program.get ow_challenge_y >>= fun t' =>
               (if g = t' then Program.set matched_chal_y true
                else (pure () : Program state Unit))))).wp F σ
       = (body >>= fun _ => loop_n n body).wp F σ
    -- Reassociate: body >>= (mc >>= loop_n n bm).
    rw [Program.bind_assoc, wp_bind]
    -- RHS: also peel body.
    conv_rhs => rw [wp_bind]
    -- Goal: body.wp (fun ttσ => (mc >>= fun _ => loop_n n bm).wp F ttσ.2) σ
    --     = body.wp (fun ttσ => (loop_n n body).wp F ttσ.2) σ
    -- Establish post equality.
    have h_post :
      (fun ttσ : Unit × state =>
          ((Program.get oracle_output >>= fun g =>
            Program.get ow_challenge_y >>= fun t' =>
            (if g = t' then Program.set matched_chal_y true
             else (pure () : Program state Unit))) >>= fun _ =>
              loop_n n (body >>= fun _ =>
                (Program.get oracle_output >>= fun g =>
                 Program.get ow_challenge_y >>= fun t' =>
                 (if g = t' then Program.set matched_chal_y true
                  else (pure () : Program state Unit))))).wp F ttσ.2)
        =
      (fun ttσ : Unit × state => (loop_n n body).wp F ttσ.2) := by
      funext ttσ
      -- Sub-step 1: replace loop_n n bm with loop_n n body via IH.
      have h_inner_eq : ∀ σ',
          (loop_n n (body >>= fun _ =>
            (Program.get oracle_output >>= fun g =>
             Program.get ow_challenge_y >>= fun t' =>
             (if g = t' then Program.set matched_chal_y true
              else (pure () : Program state Unit))))).wp F σ'
          = (loop_n n body).wp F σ' := fun σ' => ih σ'
      -- The whole expression is `(mc >>= fun _ => K) F ttσ.2` for the two
      -- different K's. Show wp-eq via post-function equality + congrArg.
      -- Reassociate and peel get oo + get chal_y via wp_bind + wp_get.
      simp only [Program.bind_assoc]
      rw [wp_bind, wp_get]
      dsimp only
      rw [wp_bind, wp_get]
      dsimp only
      -- Now goal: `(if g = t' then set matched true else pure ()) >>= loop_n n bm)`
      --   .wp F ttσ.2 = (loop_n n body).wp F ttσ.2.
      -- where g = oo.get ttσ.2, t' = chal_y.get ttσ.2.
      by_cases hgt : oracle_output.get ttσ.2 = ow_challenge_y.get ttσ.2
      · -- Positive: set matched true >>= loop_n n bm.
        simp only [if_pos hgt, wp_bind, wp_set]
        -- (loop_n n bm).wp F (matched_chal_y.set true ttσ.2) = (loop_n n body).wp F ttσ.2
        rw [h_inner_eq]
        -- (loop_n n body).wp F (matched_chal_y.set true ttσ.2) = (loop_n n body).wp F ttσ.2
        exact h_loop_set_inv n ttσ.2
      · -- Negative: pure () >>= loop_n n bm.
        simp only [if_neg hgt, Program.pure_bind]
        exact h_inner_eq _
    rw [h_post]

/-- **Loop-level wp equality**: the bare `oracle_loop_n` (used in
    `ow_game_2_tracked_p`) has the same wp as the `loop_n` with match-checks
    inside (used in `ow_game_2_with_match`'s `loop_body`), for any post that
    ignores `matched_chal_y`.

    Combines `oracle_loop_n_eq_loop_n` + `loop_n_match_check_invisible` +
    `oracle_step_lazy_query_tracked_inRange_matched_chal_y`. -/
lemma ow_game_2_loops_wp_eq
    (h_ow_adv_matched_chal_y : ow_adv.inRange matched_chal_y.compl.range)
    (F : Unit × state → ENNReal)
    (h_F : ∀ aσ : Unit × state,
        F (aσ.1, matched_chal_y.set true aσ.2) = F aσ)
    (q : ℕ) (σ : state) :
    (oracle_loop_n ow_adv q lazy_query_tracked).wp F σ
    = (loop_n q (oracle_step ow_adv lazy_query_tracked >>= fun _ =>
        (Program.get oracle_output >>= fun g =>
         Program.get ow_challenge_y >>= fun t' =>
         (if g = t' then Program.set matched_chal_y true
          else (pure () : Program state Unit))))).wp F σ := by
  rw [oracle_loop_n_eq_loop_n]
  exact (loop_n_match_check_invisible q (oracle_step ow_adv lazy_query_tracked)
    (oracle_step_lazy_query_tracked_inRange_matched_chal_y ow_adv
      h_ow_adv_matched_chal_y) F h_F σ).symm

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
  dsimp only [ow_game_2_tracked, guess_experiment_game_2, guess_experiment]
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
  sorry

/-- Game 2 wins bound: combines the direct bridge with the framework bound.
    Routes via `guess_experiment_game_2` — bypasses the old marginal_eq wall. -/
theorem ow_game_2_tracked_wins_le_guess_output_bound
    [Fintype output] [Nonempty output] [DecidableEq output]
    (q : ℕ) (σ : state) :
    (ow_game_2_tracked ow_adv q).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ ((q + 1) : ENNReal) / Fintype.card output :=
  le_trans
    (ow_game_2_tracked_wins_le_guess_experiment_game_2_matched ow_adv q σ)
    (by unfold guess_experiment_game_2
        exact guess_experiment_wp_bound _ _ ow_challenge_y matched_chal_y _ _ q σ)

/-- **Reduction: bad-in-Game-1 ≤ Guess(input, q+1)**.

    The bad event `chal_x_queried_gh = true` happens iff some
    `lazy_query_tracked` was called with input `= chal_x`. This matches
    `guess_experiment`'s structure with target = `chal_x`, guesses = the
    inputs chosen by the adversary (`oracle_input` after each adversary
    step) plus `ow_response` for the final query, env = `lazy_init >>=
    sample y >>= set chal_y`, n = q+1.

    The reduction is structurally tight: the `chal_x_queried_gh` flag in
    `ow_game_1_tracked` is exactly the "matched" flag of the
    guess_experiment. Combined with `guess_experiment_wp_bound`, this
    gives `≤ (q+1)/|input|`. -/
theorem ow_game_1_tracked_bad_le_guess_input_bound
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried_gh : ow_adv.inRange chal_x_queried_gh.compl.range)
    (q : ℕ) (σ : state) :
    (ow_game_1_tracked ow_adv q).wp
        (fun bσ : Bool × state =>
          if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
    ≤ ((q + 1) : ENNReal) / Fintype.card input := by
  sorry

/-! ## Flag-elision bridge: untracked Game 1 ↔ tracked Game 1

For postconditions that don't read `chal_x_queried_gh`, the tracked and
untracked variants of Game 1 agree at the wp level. -/

/-- **Flag elision at the game level**: `ow_game_1` and `ow_game_1_tracked`
    have equal wp's for flag-ignoring postconditions. Composes
    `lazy_query_tracked_eq_lazy_query_wp` over the q+1 lazy_query calls and
    handles the initial `set chal_x_queried_gh false`.

    The win indicator `fun bσ => if bσ.1 then 1 else 0` is trivially
    flag-ignoring (depends only on `bσ.1`). Proof deferred. -/
theorem ow_game_1_wp_eq_ow_game_1_tracked_wp_of_flag_ignoring
    (q : ℕ) (F : Bool × state → ENNReal)
    (h_F : IgnoresChalXQueriedGh F)
    (σ : state) :
    (ow_game_1 ow_adv q).wp F σ = (ow_game_1_tracked ow_adv q).wp F σ := by
  sorry

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
  rw [ow_game_1_wp_eq_ow_game_1_tracked_wp_of_flag_ignoring ow_adv q Win h_Win_flag σ]
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
        · exact ow_game_2_tracked_wins_le_guess_output_bound ow_adv q σ
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
                  h_ow_adv_chal_x_queried_gh q σ
    _ ≤ ((q + 1) : ENNReal) / Fintype.card output
        + ((q + 1) : ENNReal) / Fintype.card output := by
        gcongr
        exact_mod_cast card_input_ge_output
    _ = (2 * (q + 1) : ENNReal) / Fintype.card output := by
        rw [← ENNReal.add_div]; ring_nf

end GameHopParam_Final
