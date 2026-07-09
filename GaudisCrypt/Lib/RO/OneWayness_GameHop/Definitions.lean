import GaudisCrypt.Lib.RO
import GaudisCrypt.Lib.RO.OneWayness
import GaudisCrypt.Logic.EquivModuloLens

open GaudisCrypt
open GaudisCrypt

/-!
# OneWayness GameHop: Definitions

This module collects the *game definitions* used in the game-hopping proof of
one-wayness for a random-oracle adversary:

* `ow_game_0` — the original OW experiment (eager RO).
* `ow_game_1` — equivalent to Game 0 but with `y` sampled and pre-programmed
  explicitly. Connected to Game 0 by `ow_game_0_eq_ow_game_1` (Hop 0→1).
* `ow_game_1_tracked`, `ow_game_2_tracked` — versions of Game 1 and Game 2
  using `lazy_query_tracked` instead of `lazy_query` so the
  `chal_x_queried_gh` flag tracks whether `chal_x` was ever queried.

Plus the **tracking flags** and **collector variables** with their
disjointness axioms / instances:

* `chal_x_queried_gh : Variable Bool` — tracks whether the adv queried `chal_x`.
* `matched_chal_y    : Variable Bool` — tracks whether `chal_y` was returned.
* `queries_input     : Variable (List input)`  — adversary's query list.
* `queries_output    : Variable (List output)` — RO's response list.

This module also defines `lazy_query_tracked` (the flag-flipping variant of
`lazy_query`) which is shared by Game 1 and Game 2.
-/

section GameHopParam

variable (ow_adv : ProgramDenotation state Unit)
variable (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
variable (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
variable (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)

/-! ## Game 0 — the original OW experiment

This is exactly `ow_experiment ow_adv q lazy_init lazy_query`. We give it a
new name here for clarity in the game-hopping chain. -/

noncomputable def ow_game_0 (q : ℕ) : ProgramDenotation state Bool :=
  ow_experiment ow_adv q lazy_init lazy_query

/-! ## Game 1 — explicit y sampling

`lazy_query x` on an empty cache at `x` unfolds to "sample y uniform, write
`(x ↦ y)` into RO, return y". Game 1 makes this explicit: sample y
separately and write it into RO manually. Same distribution as Game 0. -/

noncomputable def ow_game_1 (q : ℕ) : ProgramDenotation state Bool := do
  lazy_init
  let x ← ProgramDenotation.uniform
  ProgramDenotation.set ow_challenge_x x
  let y ← ProgramDenotation.uniform
  -- Insert (x ↦ y) into RO. At this point RO is `fun _ => none` (set by
  -- lazy_init, not touched since), so the "fallback to existing entries"
  -- in `lazy_query`'s case-miss branch is equivalent to "fallback to none".
  ProgramDenotation.set random_oracle_state (fun k => if k = x then some y else none)
  ProgramDenotation.set ow_challenge_y y
  oracle_loop_n ow_adv q lazy_query
  let resp ← ProgramDenotation.get ow_response
  let y_check ← lazy_query resp
  pure (decide (y_check = y))

/-! ## Hop 0 → 1: program equality

`ow_game_0 = ow_game_1` (no probabilistic content; just unfolding
`lazy_query x` on an RO state where `x` is not cached). -/

/-- On a state whose entire RO is `fun _ => none` (i.e., immediately after
    `lazy_init`), `lazy_query inp` is wp-equivalent to "sample a fresh `y`,
    insert `(inp ↦ y)` into the RO, return `y`". -/
lemma lazy_query_on_totally_empty_RO
    (inp : input) (σ : state)
    (h_empty : random_oracle_state.get σ = fun _ => none)
    (F : output × state → ENNReal) :
    (lazy_query inp).wp F σ
    = (ProgramDenotation.uniform >>= fun y =>
        ProgramDenotation.set random_oracle_state
          (fun k => if k = inp then some y else none) >>= fun _ =>
        (pure y : ProgramDenotation state output)).wp F σ := by
  simp only [lazy_query, wp_bind, wp_get]
  rw [h_empty]
  -- The match key is now `(fun _ : input => none) inp = none`. Reduce.
  simp only [wp_bind, wp_uniform, wp_set, wp_pure]

private lemma lazy_query_x_eq_explicit_y_frame {α : Type}
    (rest : input → output → ProgramDenotation state α) :
    (lazy_init >>= fun _ : Unit =>
      ProgramDenotation.uniform >>= fun x : input =>
        ProgramDenotation.set ow_challenge_x x >>= fun _ : Unit =>
          lazy_query x >>= fun y : output => rest x y)
    = (lazy_init >>= fun _ : Unit =>
      ProgramDenotation.uniform >>= fun x : input =>
        ProgramDenotation.set ow_challenge_x x >>= fun _ : Unit =>
          ProgramDenotation.uniform >>= fun y : output =>
            ProgramDenotation.set random_oracle_state
              (fun k : input => if k = x then some y else none) >>= fun _ : Unit =>
                rest x y) := by
  apply ProgramDenotation.ext_of_wp
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
      ProgramDenotation.set ow_challenge_y y >>= fun _ =>
        oracle_loop_n ow_adv q lazy_query >>= fun _ =>
          ProgramDenotation.get ow_response >>= fun resp =>
            lazy_query resp >>= fun y_check =>
              (pure (decide (y_check = y)) : ProgramDenotation state Bool))

/-! ## Hop 1 → 2: up-to-bad

`P[Game 1 wins] ≤ P[Game 2 wins] + P[bad in Game 1]`, where `bad` =
"adversary queries the oracle at `chal_x` at some point in the loop or
in the verification step."

The strategy:

* Augment both games with a tracking flag `chal_x_queried_gh` that gets
  set to `true` whenever a `lazy_query` is invoked at input
  `chal_x`.
* Show the tracked games are wp-equivalent to the untracked games on
  posts that ignore the flag (`ProgramDenotation.wp_conditional_set_disjoint_no_op`).
* Show the tracked Game 1 and tracked Game 2 are *identical until bad*:
  their wp's agree on posts that vanish whenever the flag is `true`.
* Apply `ProgramDenotation.up_to_bad` to derive
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
noncomputable def lazy_query_tracked (inp : input) : ProgramDenotation state output :=
  lazy_query inp >>= fun y =>
    ProgramDenotation.get ow_challenge_x >>= fun cx =>
      (if inp = cx then ProgramDenotation.set chal_x_queried_gh true
       else (pure () : ProgramDenotation state Unit)) >>= fun _ =>
        (pure y : ProgramDenotation state output)

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

variable (ow_adv : ProgramDenotation state Unit)
variable (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)

/-- Tracked Game 1: same as `ow_game_1`, but every `lazy_query` is replaced
    by `lazy_query_tracked` so the `chal_x_queried_gh` flag tracks whether
    the adversary ever queried `chal_x`. -/
noncomputable def ow_game_1_tracked (q : ℕ) : ProgramDenotation state Bool := do
  lazy_init
  ProgramDenotation.set chal_x_queried_gh false  -- explicit init of the flag
  let x ← ProgramDenotation.uniform
  ProgramDenotation.set ow_challenge_x x
  let y ← ProgramDenotation.uniform
  ProgramDenotation.set random_oracle_state (fun k => if k = x then some y else none)
  ProgramDenotation.set ow_challenge_y y
  oracle_loop_n ow_adv q lazy_query_tracked
  let resp ← ProgramDenotation.get ow_response
  let y_check ← lazy_query_tracked resp
  pure (decide (y_check = y))

/-- Tracked Game 2: same as `ow_game_2`, with `lazy_query` → `lazy_query_tracked`. -/
noncomputable def ow_game_2_tracked (q : ℕ) : ProgramDenotation state Bool := do
  lazy_init
  ProgramDenotation.set chal_x_queried_gh false
  let x ← ProgramDenotation.uniform
  ProgramDenotation.set ow_challenge_x x
  let y ← ProgramDenotation.uniform
  ProgramDenotation.set ow_challenge_y y
  oracle_loop_n ow_adv q lazy_query_tracked
  let resp ← ProgramDenotation.get ow_response
  let y_check ← lazy_query_tracked resp
  pure (decide (y_check = y))


lemma lazy_query_tracked_inRange_ow_challenge_y (inp : input) :
    (lazy_query_tracked inp).inRange ow_challenge_y.compl.range := by
  haveI : disjoint ow_challenge_x ow_challenge_y :=
    disjoint_ow_challenge_y_ow_challenge_x.symm
  unfold lazy_query_tracked
  refine ProgramDenotation.inRange_bind ?_ (fun y => ?_)
  · exact ProgramDenotation.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_y)
  refine ProgramDenotation.inRange_bind ?_ (fun cx => ?_)
  · exact ProgramDenotation.get_inRange_compl_of_disjoint ow_challenge_x ow_challenge_y
  refine ProgramDenotation.inRange_bind ?_ (fun _ => ProgramDenotation.inRange_pure _ _)
  by_cases h : inp = cx
  · simp only [if_pos h]
    exact ProgramDenotation.set_inRange_compl_of_disjoint
      chal_x_queried_gh ow_challenge_y true
  · simp only [if_neg h]
    exact ProgramDenotation.inRange_pure _ _

/-- `oracle_step adv lazy_query_tracked` is ow_challenge_y-disjoint when
    `adv` is. -/
lemma oracle_step_lazy_query_tracked_inRange_ow_challenge_y
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range) :
    (oracle_step ow_adv lazy_query_tracked).inRange ow_challenge_y.compl.range := by
  unfold oracle_step
  refine ProgramDenotation.inRange_bind h_ow_adv_chal_y (fun _ => ?_)
  refine ProgramDenotation.inRange_bind
    (ProgramDenotation.get_inRange_compl_of_disjoint oracle_input ow_challenge_y) (fun inp => ?_)
  refine ProgramDenotation.inRange_bind (lazy_query_tracked_inRange_ow_challenge_y inp)
    (fun y => ?_)
  exact ProgramDenotation.set_inRange_compl_of_disjoint oracle_output ow_challenge_y y


end GameHopParam_Tracked
