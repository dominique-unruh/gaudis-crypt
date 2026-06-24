import GaudisCrypt.Lib.RO.OneWayness

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics

/-!
# Deferred-sampling infrastructure for one-wayness

This file provides the infrastructure to close the
`ow_experiment_resp_eq_chal_x_bound` lemma without axioms.

The standard cryptographic argument:
```
P[adv's output = chal_x in lazy game]
  ≤ P[adv ever queried chal_x]               (bad event)
    + P[adv's output = chal_x ∧ ¬queried]    (good event)
  ≤ q/|input|                                (Layer A_obs union bound)
    + 1/|input|                              (conditional independence on good event)
  = (q+1)/|input|
```

## Strategy

1. **Tracking variable** `chal_x_queried : Variable Bool` records whether
   any adversary lazy_query input has equalled `ow_challenge_x` so far.
   The *experiment* (not adv) maintains this — adv cannot read or write
   it directly.

2. **Tracked experiment** `ow_experiment_tracked` is the same as
   `ow_experiment` but with the tracking variable updated in each loop
   iteration. Observable behavior (the win bit, the preimage condition)
   is unchanged.

3. **Equivalence**: `ow_experiment.wp F σ = ow_experiment_tracked.wp F σ`
   for any `F` that doesn't read `chal_x_queried`.

4. **Layer A_obs**: per-iteration, `E[chal_x_queried becomes true] ≤ 1/|input|`
   (via `wp_shift_input` on `chal_x.compl.range`).

5. **Layer C_obs**: by induction, `E[chal_x_queried at end of ow_loop q]
   ≤ q/|input|`.

6. **Conditional independence**: on `¬chal_x_queried_at_end`, adv's view
   is independent of `chal_x`, so the final lazy_query's hit at chal_x
   has probability `1/|input|`.

7. **Composition**: bound `[resp = chal_x ∧ preimage]` by combining 5+6.
-/

/-- Tracking variable for whether the adversary has queried `ow_challenge_x`
    via `oracle_input` in any loop iteration so far.

    Initialized to `false` at the start of the tracked experiment, set to
    `true` by the *experiment* (not the adversary) whenever it observes
    `oracle_input.get = ow_challenge_x.get` at the moment of a lazy_query
    in `ow_loop_body`. -/
axiom chal_x_queried : Variable Bool

/-! ### Disjointness axioms for `chal_x_queried` -/

axiom disjoint_chal_x_queried_ro :
  disjoint chal_x_queried random_oracle_state
axiom disjoint_chal_x_queried_ow_challenge_x :
  disjoint chal_x_queried ow_challenge_x
axiom disjoint_chal_x_queried_ow_challenge_y :
  disjoint chal_x_queried ow_challenge_y
axiom disjoint_chal_x_queried_ow_response :
  disjoint chal_x_queried ow_response
axiom disjoint_chal_x_queried_oracle_input :
  disjoint chal_x_queried oracle_input
axiom disjoint_chal_x_queried_oracle_output :
  disjoint chal_x_queried oracle_output

attribute [instance] disjoint_chal_x_queried_ro
                     disjoint_chal_x_queried_ow_challenge_x
                     disjoint_chal_x_queried_ow_challenge_y
                     disjoint_chal_x_queried_ow_response
                     disjoint_chal_x_queried_oracle_input
                     disjoint_chal_x_queried_oracle_output

/-- Symmetric disjoint instances. -/
instance : disjoint random_oracle_state chal_x_queried :=
  disjoint_chal_x_queried_ro.symm
instance : disjoint ow_challenge_x chal_x_queried :=
  disjoint_chal_x_queried_ow_challenge_x.symm
instance : disjoint ow_challenge_y chal_x_queried :=
  disjoint_chal_x_queried_ow_challenge_y.symm
instance : disjoint ow_response chal_x_queried :=
  disjoint_chal_x_queried_ow_response.symm
instance : disjoint oracle_input chal_x_queried :=
  disjoint_chal_x_queried_oracle_input.symm
instance : disjoint oracle_output chal_x_queried :=
  disjoint_chal_x_queried_oracle_output.symm
instance : disjoint ow_challenge_x ow_response :=
  disjoint_ow_response_ow_challenge_x.symm
instance : disjoint ow_challenge_y ow_response :=
  disjoint_ow_response_ow_challenge_y.symm

section OWParam

variable (ow_adv : Program state Unit)
variable (h_ow_adv_chal_x_queried :
            ow_adv.inRange chal_x_queried.compl.range)

/-! ### Tracked loop body and experiment

The tracked version of `ow_loop_body` updates `chal_x_queried` whenever
the adversary's chosen `oracle_input` matches `ow_challenge_x`. This is
done by the experiment (it reads `ow_challenge_x`), not by adv.
-/

/-- One round of the tracked OW loop body. After adv sets `oracle_input`
    and the experiment computes the oracle response, we additionally check
    whether `oracle_input = ow_challenge_x` and update `chal_x_queried`. -/
noncomputable def ow_loop_body_tracked
    (oracle : input → Program state output) : Program state Unit :=
  ow_adv >>= fun _ =>
    Program.get oracle_input >>= fun inp =>
      Program.get ow_challenge_x >>= fun cx =>
        (if inp = cx then Program.set chal_x_queried true
         else (pure () : Program state Unit)) >>= fun _ =>
          oracle inp >>= fun y =>
            Program.set oracle_output y

/-- Run the tracked loop for `q` rounds. -/
noncomputable def ow_loop_tracked
    : ℕ → (input → Program state output) → Program state Unit
  | 0,     _      => pure ()
  | n + 1, oracle => do
      ow_loop_body_tracked ow_adv oracle
      ow_loop_tracked n oracle

/-- The tracked OW experiment: like `ow_experiment` but with `chal_x_queried`
    initialized to `false` at start and updated by `ow_loop_body_tracked`. -/
noncomputable def ow_experiment_tracked (q : ℕ)
    (init : Program state Unit)
    (oracle : input → Program state output) : Program state Bool := do
  init
  Program.set chal_x_queried false
  let x ← Program.uniform
  Program.set ow_challenge_x x
  let y ← oracle x
  Program.set ow_challenge_y y
  ow_loop_tracked ow_adv q oracle
  let resp ← Program.get ow_response
  let y_check ← oracle resp
  pure (decide (y_check = y))

/-! ### Equivalence with the original experiment

For post-conditions `F` that don't read `chal_x_queried`, the original
`ow_experiment` and `ow_experiment_tracked` have the same wp. The extra
`Program.set chal_x_queried _` steps in the tracked version only modify a
variable that's disjoint from everything `F` reads. -/

-- `Program.wp_set_disjoint_no_op` moved to ProgramRange.lean.

/-- A post-condition `F : Bool × state → ENNReal` "ignores `chal_x_queried`"
    iff its value doesn't depend on `chal_x_queried.get`. Formally:
    for any state, replacing `chal_x_queried`'s value doesn't change `F`. -/
def IgnoresChalXQueried (F : Bool × state → ENNReal) : Prop :=
  ∀ bσ b, F (bσ.1, chal_x_queried.set b bσ.2) = F bσ

/-- The "preimage win" post-condition (which is what we care about for OW)
    doesn't depend on `chal_x_queried`. -/
lemma preimage_win_ignores_chal_x_queried :
    IgnoresChalXQueried (fun bσ : Bool × state =>
      if ow_response.get bσ.2 = ow_challenge_x.get bσ.2 ∧ is_preimage bσ.2
      then (1 : ENNReal) else 0) := by
  intro bσ b
  dsimp only
  -- chal_x_queried is disjoint from ow_response, ow_challenge_x, RO, chal_y.
  -- So setting it doesn't change ow_response.get, ow_challenge_x.get, or is_preimage.
  rw [ow_response.get_of_disjoint_set chal_x_queried,
      ow_challenge_x.get_of_disjoint_set chal_x_queried]
  congr 1
  unfold is_preimage
  rw [random_oracle_state.get_of_disjoint_set chal_x_queried,
      ow_response.get_of_disjoint_set chal_x_queried,
      ow_challenge_y.get_of_disjoint_set chal_x_queried]

/-- The "lazy_query then set oracle_output" rest of `ow_loop_body` is in
    `chal_x_queried.compl.range`. Specialization of the generic
    `lazy_query_then_set_oracle_output_inRange_compl` in `RO.lean`. -/
lemma lazy_query_then_set_oracle_output_inRange_chal_x_queried_compl
    (inp : input) :
    (lazy_query inp >>= fun y => Program.set oracle_output y).inRange
        chal_x_queried.compl.range :=
  lazy_query_then_set_oracle_output_inRange_compl chal_x_queried inp

/-- Specialization for `ow_challenge_x`. -/
lemma lazy_query_then_set_oracle_output_inRange_ow_challenge_x_compl
    (inp : input) :
    (lazy_query inp >>= fun y => Program.set oracle_output y).inRange
        ow_challenge_x.compl.range :=
  lazy_query_then_set_oracle_output_inRange_compl ow_challenge_x inp

/-- The conditional `set chal_x_queried` step is a no-op for posts that
    ignore `chal_x_queried`, provided the rest is in `chal_x_queried.compl.range`.
    Thin wrapper over `Program.wp_conditional_set_disjoint_no_op`. -/
lemma conditional_set_chal_x_queried_no_op
    {α : Type} (cond : Prop) [Decidable cond]
    {rest : Program state α} (h_rest : rest.inRange chal_x_queried.compl.range)
    (F : α × state → ENNReal)
    (h_F : ∀ aσ : α × state, F (aσ.1, chal_x_queried.set true aσ.2) = F aσ)
    (σ : state) :
    ((if cond then Program.set chal_x_queried true else pure ()) >>= fun _ => rest).wp F σ
    = rest.wp F σ :=
  Program.wp_conditional_set_disjoint_no_op cond true h_rest F h_F σ

/-- A helper combining `get ow_challenge_x` with the conditional set. Thin
    wrapper over `Program.wp_get_then_conditional_set_disjoint_no_op`. -/
lemma get_chal_x_then_conditional_set_no_op
    {α : Type} (inp : input)
    {rest : Program state α} (h_rest : rest.inRange chal_x_queried.compl.range)
    (F : α × state → ENNReal)
    (h_F : ∀ aσ : α × state, F (aσ.1, chal_x_queried.set true aσ.2) = F aσ)
    (σ : state) :
    (Program.get ow_challenge_x >>= fun cx =>
        (if inp = cx then Program.set chal_x_queried true
         else (pure () : Program state Unit)) >>= fun _ => rest).wp F σ
    = rest.wp F σ :=
  Program.wp_get_then_conditional_set_disjoint_no_op
    (L_get := ow_challenge_x) (L_set := chal_x_queried)
    (fun cx => inp = cx) true h_rest F h_F σ

/-- The inner post equivalence — provable using
    `get_chal_x_then_conditional_set_no_op`. -/
private lemma ow_loop_body_inner_eq
    (G : Unit × state → ENNReal)
    (h_G : ∀ aσ : Unit × state, G (aσ.1, chal_x_queried.set true aσ.2) = G aσ)
    (σ_a : state) :
    (Program.get oracle_input >>= fun inp =>
      lazy_query inp >>= fun y => Program.set oracle_output y).wp G σ_a
    = (Program.get oracle_input >>= fun inp =>
      Program.get ow_challenge_x >>= fun cx =>
        (if inp = cx then Program.set chal_x_queried true
         else (pure () : Program state Unit)) >>= fun _ =>
          lazy_query inp >>= fun y => Program.set oracle_output y).wp G σ_a := by
  rw [wp_bind, wp_get, wp_bind, wp_get]
  set inp := oracle_input.get σ_a
  exact (get_chal_x_then_conditional_set_no_op inp
      (lazy_query_then_set_oracle_output_inRange_chal_x_queried_compl inp)
      G h_G σ_a).symm

/-- Per-iteration body equivalence: `ow_loop_body` and `ow_loop_body_tracked`
    produce the same wp for posts that ignore `chal_x_queried`. -/
lemma ow_loop_body_eq_tracked
    (G : Unit × state → ENNReal)
    (h_G : ∀ aσ : Unit × state, G (aσ.1, chal_x_queried.set true aσ.2) = G aσ)
    (σ : state) :
    (ow_loop_body ow_adv lazy_query).wp G σ
    = (ow_loop_body_tracked ow_adv lazy_query).wp G σ := by
  -- Step 1: unfold both bodies via rfl (defs are defeq).
  -- Step 2: apply wp_bind on both, then use inner equivalence.
  have h_lhs : (ow_loop_body ow_adv lazy_query).wp G σ
      = ow_adv.wp (fun xs : Unit × state =>
          (Program.get oracle_input >>= fun inp =>
            lazy_query inp >>= fun y =>
              Program.set oracle_output y).wp G xs.snd) σ := by
    show (ow_adv >>= fun _ : Unit =>
          Program.get oracle_input >>= fun inp =>
            lazy_query inp >>= fun y =>
              Program.set oracle_output y).wp G σ
       = ow_adv.wp _ σ
    rw [wp_bind]
  have h_rhs : (ow_loop_body_tracked ow_adv lazy_query).wp G σ
      = ow_adv.wp (fun xs : Unit × state =>
          (Program.get oracle_input >>= fun inp =>
            Program.get ow_challenge_x >>= fun cx =>
              (if inp = cx then Program.set chal_x_queried true
               else (pure () : Program state Unit)) >>= fun _ =>
                lazy_query inp >>= fun y =>
                  Program.set oracle_output y).wp G xs.snd) σ := by
    show (ow_adv >>= fun _ : Unit =>
          Program.get oracle_input >>= fun inp =>
            Program.get ow_challenge_x >>= fun cx =>
              (if inp = cx then Program.set chal_x_queried true
               else (pure () : Program state Unit)) >>= fun _ =>
                lazy_query inp >>= fun y =>
                  Program.set oracle_output y).wp G σ
       = ow_adv.wp _ σ
    rw [wp_bind]
  rw [h_lhs, h_rhs]
  apply congrArg (fun P => ow_adv.wp P σ)
  funext xs
  exact ow_loop_body_inner_eq G h_G xs.snd

/-! ### Loop and experiment equivalence

By induction on `q`, the loop equivalence lifts the body equivalence.
This requires `ow_adv.inRange chal_x_queried.compl.range` so that
`ow_loop` (untouched) is in `chal_x_queried.compl.range` and the
"G' ignores chal_x_queried" hypothesis carries through induction. -/

include h_ow_adv_chal_x_queried in
/-- `ow_loop_body` (the original, untracked) is in `chal_x_queried.compl.range`:
    it's built from operations that don't touch `chal_x_queried`. -/
private lemma ow_loop_body_inRange_chal_x_queried_compl :
    (ow_loop_body ow_adv lazy_query).inRange chal_x_queried.compl.range :=
  oracle_step_inRange_compl chal_x_queried h_ow_adv_chal_x_queried

include h_ow_adv_chal_x_queried in
/-- `ow_loop q` (the original, untracked) is in `chal_x_queried.compl.range`. -/
private lemma ow_loop_inRange_chal_x_queried_compl (q : ℕ) :
    (ow_loop ow_adv q lazy_query).inRange chal_x_queried.compl.range :=
  oracle_loop_n_inRange_compl chal_x_queried h_ow_adv_chal_x_queried q

/-- `ow_loop_body_tracked` is in `ow_challenge_y.compl.range`. -/
private lemma ow_loop_body_tracked_inRange_ow_challenge_y_compl
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range) :
    (ow_loop_body_tracked ow_adv lazy_query).inRange ow_challenge_y.compl.range := by
  refine Program.inRange_bind h_ow_adv_chal_y ?_
  intro _
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint oracle_input ow_challenge_y) ?_
  intro inp
  haveI _disj_cx_cy : disjoint ow_challenge_x ow_challenge_y :=
    disjoint_ow_challenge_y_ow_challenge_x.symm
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint ow_challenge_x ow_challenge_y) ?_
  intro cx
  refine Program.inRange_bind ?_ ?_
  · by_cases h : inp = cx
    · rw [if_pos h]
      exact Program.set_inRange_compl_of_disjoint chal_x_queried ow_challenge_y _
    · rw [if_neg h]
      exact Program.inRange_pure _ _
  · intro _
    exact lazy_query_then_set_oracle_output_inRange_compl ow_challenge_y inp

/-- `ow_loop_tracked q` is in `ow_challenge_y.compl.range`. -/
private lemma ow_loop_tracked_inRange_ow_challenge_y_compl
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (q : ℕ) :
    (ow_loop_tracked ow_adv q lazy_query).inRange ow_challenge_y.compl.range := by
  induction q with
  | zero => exact Program.inRange_pure _ _
  | succ n ih =>
    show (ow_loop_body_tracked ow_adv lazy_query >>= fun _ =>
          ow_loop_tracked ow_adv n lazy_query).inRange _
    exact Program.inRange_bind
      (ow_loop_body_tracked_inRange_ow_challenge_y_compl ow_adv h_ow_adv_chal_y)
      (fun _ => ih)

include h_ow_adv_chal_x_queried in
/-- The wp of `ow_loop q` at a `chal_x_queried = true` state equals the wp at
    the original state, for posts that ignore `chal_x_queried`. -/
private lemma ow_loop_wp_chal_x_queried_invariant (q : ℕ)
    (G : Unit × state → ENNReal)
    (h_G : ∀ aσ : Unit × state, G (aσ.1, chal_x_queried.set true aσ.2) = G aσ)
    (σ : state) :
    (ow_loop ow_adv q lazy_query).wp G (chal_x_queried.set true σ)
    = (ow_loop ow_adv q lazy_query).wp G σ := by
  set f : state → state := chal_x_queried.update (Function.const _ true) with hf_def
  have h_f_in_Rc : f ∈ ((chal_x_queried.compl.range : TotLensRange state)ᶜ).updates := by
    rw [show ((chal_x_queried.compl.range : TotLensRange state)ᶜ) = chal_x_queried.range from by
      rw [TotLensRange.complement_range, TotLensRange.compl_compl]]
    exact ⟨Function.const _ true, Set.mem_univ _, rfl⟩
  have h_f_eq : ∀ σ', f σ' = chal_x_queried.set true σ' := fun σ' => by
    show chal_x_queried.set ((Function.const _ true) (chal_x_queried.get σ')) σ'
      = chal_x_queried.set true σ'
    rw [Function.const_apply]
  rw [← h_f_eq σ]
  rw [Program.wp_shift_input
      (ow_loop_inRange_chal_x_queried_compl ow_adv h_ow_adv_chal_x_queried q)
      h_f_in_Rc]
  congr 1
  funext xs
  rw [h_f_eq xs.snd]
  exact h_G xs

include h_ow_adv_chal_x_queried in
/-- **Loop equivalence**: `ow_loop` and `ow_loop_tracked` produce the same wp
    for posts that ignore `chal_x_queried`. By induction on `q`. -/
lemma ow_loop_eq_tracked (q : ℕ)
    (G : Unit × state → ENNReal)
    (h_G : ∀ aσ : Unit × state, G (aσ.1, chal_x_queried.set true aσ.2) = G aσ)
    (σ : state) :
    (ow_loop ow_adv q lazy_query).wp G σ
    = (ow_loop_tracked ow_adv q lazy_query).wp G σ := by
  induction q generalizing σ with
  | zero =>
    -- Both ow_loop 0 = pure () and ow_loop_tracked 0 = pure ().
    rfl
  | succ n ih =>
    -- ow_loop (n+1) = ow_loop_body >>= ow_loop n.
    -- ow_loop_tracked (n+1) = ow_loop_body_tracked >>= ow_loop_tracked n.
    show (ow_loop_body ow_adv lazy_query >>= fun _ =>
          ow_loop ow_adv n lazy_query).wp G σ
       = (ow_loop_body_tracked ow_adv lazy_query >>= fun _ =>
          ow_loop_tracked ow_adv n lazy_query).wp G σ
    rw [wp_bind, wp_bind]
    -- Both sides: body[_tracked].wp (fun aσ => loop[_tracked] n .wp G aσ.2) σ.
    -- Set up the post G' for body equivalence.
    set G' : Unit × state → ENNReal :=
      fun aσ => (ow_loop ow_adv n lazy_query).wp G aσ.2
    -- G' ignores chal_x_queried by ow_loop_wp_chal_x_queried_invariant.
    have h_G' : ∀ aσ : Unit × state,
        G' (aσ.1, chal_x_queried.set true aσ.2) = G' aσ := by
      intro aσ
      show (ow_loop ow_adv n lazy_query).wp G (chal_x_queried.set true aσ.2)
         = (ow_loop ow_adv n lazy_query).wp G aσ.2
      exact ow_loop_wp_chal_x_queried_invariant
        ow_adv h_ow_adv_chal_x_queried n G h_G aσ.2
    -- Replace RHS's `ow_loop_tracked n` with `ow_loop n` (by IH).
    have h_rhs_inner : (fun aσ : Unit × state =>
        (ow_loop_tracked ow_adv n lazy_query).wp G aσ.2)
        = G' := by
      funext aσ
      show (ow_loop_tracked ow_adv n lazy_query).wp G aσ.2
         = (ow_loop ow_adv n lazy_query).wp G aσ.2
      exact (ih aσ.snd).symm
    rw [h_rhs_inner]
    -- Now both sides: body[_tracked].wp G' σ. Apply body equivalence.
    exact ow_loop_body_eq_tracked ow_adv G' h_G' σ

include h_ow_adv_chal_x_queried in
/-- The "rest of the experiment" minus the initial `init` step is in
    `chal_x_queried.compl.range`. -/
private lemma ow_experiment_rest_inRange_chal_x_queried_compl (q : ℕ)
    (oracle : input → Program state output)
    (h_oracle_inRange : ∀ x : input,
        (oracle x).inRange chal_x_queried.compl.range)
    (h_ow_loop_in_compl :
        (ow_loop ow_adv q oracle).inRange chal_x_queried.compl.range) :
    (Program.uniform >>= fun x : input =>
      Program.set ow_challenge_x x >>= fun _ =>
        oracle x >>= fun y =>
          Program.set ow_challenge_y y >>= fun _ =>
            ow_loop ow_adv q oracle >>= fun _ =>
              Program.get ow_response >>= fun resp =>
                oracle resp >>= fun y_check =>
                  (pure (decide (y_check = y)) : Program state Bool)).inRange
      chal_x_queried.compl.range := by
  refine Program.inRange_bind
    (Program.inRange_mono Program.inRange_uniform bot_le) ?_
  intro x
  refine Program.inRange_bind
    (Program.set_inRange_compl_of_disjoint ow_challenge_x chal_x_queried _) ?_
  intro _
  refine Program.inRange_bind (h_oracle_inRange x) ?_
  intro y
  refine Program.inRange_bind
    (Program.set_inRange_compl_of_disjoint ow_challenge_y chal_x_queried _) ?_
  intro _
  refine Program.inRange_bind h_ow_loop_in_compl ?_
  intro _
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint ow_response chal_x_queried) ?_
  intro resp
  refine Program.inRange_bind (h_oracle_inRange resp) ?_
  intro _
  exact Program.inRange_mono (Program.inRange_pure _ _) bot_le

/-- The post-loop tail `get resp >>= lazy_query resp >>= pure` is in
    `chal_x_queried.compl.range`. -/
private lemma post_loop_inRange_chal_x_queried_compl (y_chal : output) :
    (Program.get ow_response >>= fun resp =>
      lazy_query resp >>= fun y_check =>
        (pure (decide (y_check = y_chal)) : Program state Bool)).inRange
        chal_x_queried.compl.range := by
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint ow_response chal_x_queried) ?_
  intro resp
  refine Program.inRange_bind ?_ ?_
  · exact Program.inRange_mono (lazy_query_inRange_ro resp)
      (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried)
  · intro _
    exact Program.inRange_mono (Program.inRange_pure _ _) bot_le

include h_ow_adv_chal_x_queried in
/-- **REST equivalence**: the experiment "rest" with `ow_loop` vs `ow_loop_tracked`
    have the same wp for posts ignoring `chal_x_queried`. -/
private lemma ow_experiment_rest_eq_tracked (q : ℕ)
    (F : Bool × state → ENNReal) (h_F : IgnoresChalXQueried F) (σ_init : state) :
    (Program.uniform >>= fun x : input =>
      Program.set ow_challenge_x x >>= fun _ =>
        lazy_query x >>= fun y =>
          Program.set ow_challenge_y y >>= fun _ =>
            ow_loop ow_adv q lazy_query >>= fun _ =>
              Program.get ow_response >>= fun resp =>
                lazy_query resp >>= fun y_check =>
                  (pure (decide (y_check = y)) : Program state Bool)).wp F σ_init
    = (Program.uniform >>= fun x : input =>
      Program.set ow_challenge_x x >>= fun _ =>
        lazy_query x >>= fun y =>
          Program.set ow_challenge_y y >>= fun _ =>
            ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
              Program.get ow_response >>= fun resp =>
                lazy_query resp >>= fun y_check =>
                  (pure (decide (y_check = y)) : Program state Bool)).wp F σ_init := by
  -- Both sides differ only at ow_loop vs ow_loop_tracked.
  -- Peel off wp_bind on both sides, then use congrArg + funext to descend.
  rw [wp_bind]; conv_rhs => rw [wp_bind]
  apply congrArg (fun P => Program.uniform.wp P σ_init)
  funext xs_u
  -- xs_u : input × state. The inner is set chal_x xs_u.1 >>= ... .wp F xs_u.2.
  show (Program.set ow_challenge_x xs_u.1 >>= fun _ =>
        lazy_query xs_u.1 >>= fun y =>
          Program.set ow_challenge_y y >>= fun _ =>
            ow_loop ow_adv q lazy_query >>= fun _ =>
              Program.get ow_response >>= fun resp =>
                lazy_query resp >>= fun y_check =>
                  (pure (decide (y_check = y)) : Program state Bool)).wp F xs_u.2
      = (Program.set ow_challenge_x xs_u.1 >>= fun _ =>
          lazy_query xs_u.1 >>= fun y =>
            Program.set ow_challenge_y y >>= fun _ =>
              ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
                Program.get ow_response >>= fun resp =>
                  lazy_query resp >>= fun y_check =>
                    (pure (decide (y_check = y)) : Program state Bool)).wp F xs_u.2
  rw [wp_bind]; conv_rhs => rw [wp_bind]
  apply congrArg (fun P => (Program.set ow_challenge_x xs_u.1).wp P xs_u.2)
  funext xs_cx
  -- xs_cx : Unit × state.
  show (lazy_query xs_u.1 >>= fun y =>
          Program.set ow_challenge_y y >>= fun _ =>
            ow_loop ow_adv q lazy_query >>= fun _ =>
              Program.get ow_response >>= fun resp =>
                lazy_query resp >>= fun y_check =>
                  (pure (decide (y_check = y)) : Program state Bool)).wp F xs_cx.2
      = (lazy_query xs_u.1 >>= fun y =>
          Program.set ow_challenge_y y >>= fun _ =>
            ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
              Program.get ow_response >>= fun resp =>
                lazy_query resp >>= fun y_check =>
                  (pure (decide (y_check = y)) : Program state Bool)).wp F xs_cx.2
  rw [wp_bind]; conv_rhs => rw [wp_bind]
  apply congrArg (fun P => (lazy_query xs_u.1).wp P xs_cx.2)
  funext xs_lq
  -- xs_lq : output × state.
  show (Program.set ow_challenge_y xs_lq.1 >>= fun _ =>
          ow_loop ow_adv q lazy_query >>= fun _ =>
            Program.get ow_response >>= fun resp =>
              lazy_query resp >>= fun y_check =>
                (pure (decide (y_check = xs_lq.1)) : Program state Bool)).wp F xs_lq.2
      = (Program.set ow_challenge_y xs_lq.1 >>= fun _ =>
          ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
            Program.get ow_response >>= fun resp =>
              lazy_query resp >>= fun y_check =>
                (pure (decide (y_check = xs_lq.1)) : Program state Bool)).wp F xs_lq.2
  rw [wp_bind]; conv_rhs => rw [wp_bind]
  apply congrArg (fun P => (Program.set ow_challenge_y xs_lq.1).wp P xs_lq.2)
  funext xs_cy
  -- xs_cy : Unit × state.
  show (ow_loop ow_adv q lazy_query >>= fun _ =>
          Program.get ow_response >>= fun resp =>
            lazy_query resp >>= fun y_check =>
              (pure (decide (y_check = xs_lq.1)) : Program state Bool)).wp F xs_cy.2
      = (ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
          Program.get ow_response >>= fun resp =>
            lazy_query resp >>= fun y_check =>
              (pure (decide (y_check = xs_lq.1)) : Program state Bool)).wp F xs_cy.2
  rw [wp_bind]; conv_rhs => rw [wp_bind]
  -- Now: ow_loop.wp G' xs_cy.2 = ow_loop_tracked.wp G' xs_cy.2 where
  -- G' = fun aσ => post_loop.wp F aσ.2.
  set post_loop : Program state Bool :=
    Program.get ow_response >>= fun resp =>
      lazy_query resp >>= fun y_check =>
        (pure (decide (y_check = xs_lq.1)) : Program state Bool) with hpost_def
  set G' : Unit × state → ENNReal :=
    fun aσ => post_loop.wp F aσ.2 with hG'_def
  -- G' ignores chal_x_queried since post_loop is in chal_x_queried.compl.range
  -- and F ignores chal_x_queried.
  have h_G' : ∀ aσ : Unit × state,
      G' (aσ.1, chal_x_queried.set true aσ.2) = G' aσ := by
    intro aσ
    show post_loop.wp F (chal_x_queried.set true aσ.2) = post_loop.wp F aσ.2
    -- Apply wp_shift_input.
    set f : state → state := chal_x_queried.update (Function.const _ true) with hf_def
    have h_f_in_Rc : f ∈ ((chal_x_queried.compl.range : TotLensRange state)ᶜ).updates := by
      rw [show ((chal_x_queried.compl.range : TotLensRange state)ᶜ) = chal_x_queried.range from by
        rw [TotLensRange.complement_range, TotLensRange.compl_compl]]
      exact ⟨Function.const _ true, Set.mem_univ _, rfl⟩
    have h_f_eq : ∀ σ', f σ' = chal_x_queried.set true σ' := fun σ' => by
      show chal_x_queried.set ((Function.const _ true) (chal_x_queried.get σ')) σ'
        = chal_x_queried.set true σ'
      rw [Function.const_apply]
    rw [← h_f_eq aσ.2]
    rw [Program.wp_shift_input
        (post_loop_inRange_chal_x_queried_compl xs_lq.1) h_f_in_Rc]
    congr 1
    funext xs_b
    rw [h_f_eq xs_b.snd]
    exact h_F xs_b true
  exact ow_loop_eq_tracked ow_adv h_ow_adv_chal_x_queried q G' h_G' xs_cy.2

include h_ow_adv_chal_x_queried in
/-- **Experiment equivalence (for lazy oracle)**: `ow_experiment` with
    `lazy_query` and `ow_experiment_tracked` with `lazy_query` produce the same
    wp for posts ignoring `chal_x_queried`. -/
lemma ow_experiment_eq_tracked_lazy (q : ℕ)
    (init : Program state Unit)
    (h_init_inRange : init.inRange chal_x_queried.compl.range)
    (F : Bool × state → ENNReal) (h_F : IgnoresChalXQueried F) (σ : state) :
    (ow_experiment ow_adv q init lazy_query).wp F σ
    = (ow_experiment_tracked ow_adv q init lazy_query).wp F σ := by
  -- Factor out init via wp_bind on both sides.
  have h_lhs :
      (ow_experiment ow_adv q init lazy_query).wp F σ
      = init.wp (fun xs : Unit × state =>
          (Program.uniform >>= fun x : input =>
            Program.set ow_challenge_x x >>= fun _ =>
              lazy_query x >>= fun y =>
                Program.set ow_challenge_y y >>= fun _ =>
                  ow_loop ow_adv q lazy_query >>= fun _ =>
                    Program.get ow_response >>= fun resp =>
                      lazy_query resp >>= fun y_check =>
                        (pure (decide (y_check = y)) : Program state Bool)).wp F xs.snd) σ := by
    show (init >>= fun _ : Unit =>
          Program.uniform >>= fun x : input =>
            Program.set ow_challenge_x x >>= fun _ =>
              lazy_query x >>= fun y =>
                Program.set ow_challenge_y y >>= fun _ =>
                  ow_loop ow_adv q lazy_query >>= fun _ =>
                    Program.get ow_response >>= fun resp =>
                      lazy_query resp >>= fun y_check =>
                        (pure (decide (y_check = y)) : Program state Bool)).wp F σ
       = init.wp _ σ
    rw [wp_bind]
  have h_rhs :
      (ow_experiment_tracked ow_adv q init lazy_query).wp F σ
      = init.wp (fun xs : Unit × state =>
          (Program.set chal_x_queried false >>= fun _ =>
            Program.uniform >>= fun x : input =>
              Program.set ow_challenge_x x >>= fun _ =>
                lazy_query x >>= fun y =>
                  Program.set ow_challenge_y y >>= fun _ =>
                    ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
                      Program.get ow_response >>= fun resp =>
                        lazy_query resp >>= fun y_check =>
                          (pure (decide (y_check = y)) : Program state Bool)).wp F xs.snd) σ := by
    show (init >>= fun _ : Unit =>
          Program.set chal_x_queried false >>= fun _ =>
            Program.uniform >>= fun x : input =>
              Program.set ow_challenge_x x >>= fun _ =>
                lazy_query x >>= fun y =>
                  Program.set ow_challenge_y y >>= fun _ =>
                    ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
                      Program.get ow_response >>= fun resp =>
                        lazy_query resp >>= fun y_check =>
                          (pure (decide (y_check = y)) : Program state Bool)).wp F σ
       = init.wp _ σ
    rw [wp_bind]
  rw [h_lhs, h_rhs]
  apply congrArg (fun P => init.wp P σ)
  funext xs
  -- Inner equality: REST.wp F xs.snd = (set chal_x_queried false >>= REST_TRACKED).wp F xs.snd.
  set σ_a := xs.snd with hσ_a_def
  -- Step 1: (set chal_x_queried false >>= REST_TRACKED).wp F σ_a
  --       = REST_TRACKED.wp F (chal_x_queried.set false σ_a)   [wp_bind + wp_set]
  rw [show (Program.set chal_x_queried false >>= fun _ =>
            Program.uniform >>= fun x : input =>
              Program.set ow_challenge_x x >>= fun _ =>
                lazy_query x >>= fun y =>
                  Program.set ow_challenge_y y >>= fun _ =>
                    ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
                      Program.get ow_response >>= fun resp =>
                        lazy_query resp >>= fun y_check =>
                          (pure (decide (y_check = y)) : Program state Bool)).wp F σ_a
        = (Program.uniform >>= fun x : input =>
            Program.set ow_challenge_x x >>= fun _ =>
              lazy_query x >>= fun y =>
                Program.set ow_challenge_y y >>= fun _ =>
                  ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
                    Program.get ow_response >>= fun resp =>
                      lazy_query resp >>= fun y_check =>
                        (pure (decide (y_check = y)) : Program state Bool)).wp F
            (chal_x_queried.set false σ_a) from by
      rw [wp_bind, wp_set]]
  -- Step 2: REST_TRACKED.wp F (chal_x_queried.set false σ_a)
  --       = REST.wp F (chal_x_queried.set false σ_a)            [REST equivalence reversed]
  rw [← ow_experiment_rest_eq_tracked ow_adv h_ow_adv_chal_x_queried q F h_F
        (chal_x_queried.set false σ_a)]
  -- Step 3: REST.wp F (chal_x_queried.set false σ_a) = REST.wp F σ_a
  --   [wp_shift_input + h_F + REST.inRange chal_x_queried.compl.range]
  set f : state → state := chal_x_queried.update (Function.const _ false) with hf_def
  have h_f_in_Rc : f ∈ ((chal_x_queried.compl.range : TotLensRange state)ᶜ).updates := by
    rw [show ((chal_x_queried.compl.range : TotLensRange state)ᶜ) = chal_x_queried.range from by
      rw [TotLensRange.complement_range, TotLensRange.compl_compl]]
    exact ⟨Function.const _ false, Set.mem_univ _, rfl⟩
  have h_f_eq : ∀ σ', f σ' = chal_x_queried.set false σ' := fun σ' => by
    show chal_x_queried.set ((Function.const _ false) (chal_x_queried.get σ')) σ'
      = chal_x_queried.set false σ'
    rw [Function.const_apply]
  rw [← h_f_eq σ_a]
  rw [Program.wp_shift_input
      (ow_experiment_rest_inRange_chal_x_queried_compl ow_adv
        h_ow_adv_chal_x_queried q lazy_query
        (fun x => Program.inRange_mono (lazy_query_inRange_ro x)
          (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried))
        (ow_loop_inRange_chal_x_queried_compl ow_adv h_ow_adv_chal_x_queried q))
      h_f_in_Rc]
  congr 1
  funext xs_b
  rw [h_f_eq xs_b.snd]
  exact (h_F xs_b false).symm

/-! ### Layer A_obs: per-iteration query-hit bound

When entering a loop iteration with `chal_x_queried = false`, the probability
that the iteration sets `chal_x_queried = true` is at most `1/|input|`.

The key insight: with `chal_x_queried = false`, by the equivalence lemma
combined with `wp_shift_input`, the experiment's behavior up to this point
is independent of `chal_x`'s value. Marginalizing over the initial uniform
sample of `chal_x` gives `1/|input|`.
-/

/-- Mass bound for the tracked loop body. (Trivial; not the real Layer A_obs.) -/
private lemma ow_loop_body_tracked_mass_le_one
    (σ : state) :
    (ow_loop_body_tracked ow_adv lazy_query).wp
        (fun _ : Unit × state => (1 : ENNReal)) σ
    ≤ 1 :=
  Program.wp_const_le _ 1 σ

/-! ### Bound on `chal_x_queried_at_end` (Layer C_obs)

The "bad event" bound: across the `q` loop iterations, the probability that
some adversary `oracle_input` equals `ow_challenge_x` is at most `q/|input|`.

This is a union bound, valid because the adversary cannot read `ow_challenge_x`
and `ow_challenge_x` is uniformly sampled. -/

/-! ### Proof sketch (Layer C_obs)

The bound reduces (via `wp_uniform` at the experiment's outer `uniform x`) to
a strengthened sum inequality on the loop:

  **Sum lemma**: ∀ q : ℕ, ∀ σ with `chal_x_queried.get σ = false`,
    ∑ x : input, (ow_loop_tracked q lazy_query).wp
      [chal_x_queried.get bσ.2 = true] (ow_challenge_x.set x σ) ≤ q

Proof by induction on q.

* `q = 0`: `pure ()` preserves chal_x_queried = false; indicator = 0; sum = 0. ✓
* `q → q+1`:
  - Unfold `ow_loop_tracked (q+1) = body_tracked >>= ow_loop_tracked q`.
  - Use `wp_bind` to factor.
  - body_tracked = `ow_adv >>= post_adv` where `post_adv` does the conditional
    chal_x_queried update and the lazy_query.
  - Apply `wp_shift_input` on `ow_adv` (∈ `chal_x.compl.range`): commute the
    `chal_x.set x` past the adversary.
  - Apply `wp_finset_sum` to pull `∑ x` inside `ow_adv.wp`.
  - For each adversary outcome `aσ_adv` (with `inp = oracle_input.get aσ_adv.2`,
    note `inp` is independent of `x`):
    - For `x = inp` (one term): the conditional fires, setting
      chal_x_queried = true; the rest of body preserves it; loop_q preserves it.
      Contribution ≤ 1.
    - For `x ≠ inp` (other terms): conditional doesn't fire; the remaining
      `lazy_query inp >>= set oracle_output >>= loop_q` is independent of `x`
      via another `wp_shift_input` (this program is in `chal_x.compl.range`).
      Apply `wp_finset_sum` again, then IH gives sum ≤ q.
  - Total per outcome: ≤ 1 + q. Adversary mass ≤ 1 gives sum ≤ q+1.

This argument relies crucially on `h_ow_adv_chal_x`: the adversary cannot read
`ow_challenge_x`, so its choice of `inp` is independent of `chal_x`.
-/

include h_ow_adv_chal_x_queried in
/-- **Strengthened sum bound** for `ow_loop_tracked`: for any state with
    `chal_x_queried = false`, summing the loop's wp at `[chal_x_queried]`
    over `chal_x = x` gives at most `q`. This is the core of Layer C_obs.

    Proof by induction on `q`.

    * `q = 0`: `pure ()` preserves chal_x_queried; indicator = 0; sum = 0.
    * `q → q+1`: Apply `wp_shift_input` to commute `chal_x.set x` past
      `ow_adv` (which doesn't read chal_x). Use `wp_finset_sum` to pull the
      sum inside. For each adversary outcome with `inp`, split: `x = inp`
      contributes ≤ 1 (hit case); `x ≠ inp` contributes the miss-branch wp,
      which we shift again (lazy_query and set are also in chal_x.compl.range)
      and apply IH. Total per outcome ≤ 1 + q; adversary mass ≤ 1 gives q+1.
-/
private lemma ow_loop_tracked_chal_x_queried_sum_le
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range) :
    ∀ (q : ℕ) (σ : state), chal_x_queried.get σ = false →
    ∑ x : input, (ow_loop_tracked ow_adv q lazy_query).wp
        (fun aσ : Unit × state =>
          if chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)
        (ow_challenge_x.set x σ) ≤ (q : ENNReal) := by
  intro q
  induction q with
  | zero =>
    intro σ h_σ
    -- ow_loop_tracked 0 = pure (). wp evaluates the indicator at the state.
    show ∑ x : input, (Pure.pure () : Program state Unit).wp _ (ow_challenge_x.set x σ) ≤ _
    simp_rw [wp_pure]
    -- chal_x.set preserves chal_x_queried.get since chal_x and chal_x_queried are disjoint.
    have h_qf : ∀ x : input,
        chal_x_queried.get (ow_challenge_x.set x σ) = false := by
      intro x
      rw [chal_x_queried.get_of_disjoint_set]; exact h_σ
    have h_zero : ∀ x : input,
        (if chal_x_queried.get (ow_challenge_x.set x σ) then (1 : ENNReal) else 0) = 0 := by
      intro x; rw [h_qf x]; simp
    simp_rw [h_zero]
    simp
  | succ q ih =>
    intro σ h_σ
    -- Abbreviations.
    set F : Unit × state → ENNReal :=
      fun aσ : Unit × state => if chal_x_queried.get aσ.2 then (1 : ENNReal) else 0 with hF_def
    set G : Unit × state → ENNReal :=
      fun aσ_b : Unit × state => (ow_loop_tracked ow_adv q lazy_query).wp F aσ_b.2 with hG_def
    -- Step 1: Reduce loop (q+1) to body >>= loop_q via wp_bind.
    have h_step1 : ∀ x : input,
        (ow_loop_tracked ow_adv (q+1) lazy_query).wp F (ow_challenge_x.set x σ)
        = (ow_loop_body_tracked ow_adv lazy_query).wp G (ow_challenge_x.set x σ) := by
      intro x
      show (ow_loop_body_tracked ow_adv lazy_query >>= fun _ : Unit =>
              ow_loop_tracked ow_adv q lazy_query).wp F (ow_challenge_x.set x σ) = _
      rw [wp_bind]
    simp_rw [h_step1]
    -- Step 2: body = ow_adv >>= post_adv. Apply wp_bind.
    have h_step2 : ∀ x : input,
        (ow_loop_body_tracked ow_adv lazy_query).wp G (ow_challenge_x.set x σ)
        = ow_adv.wp (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp G aσ_adv.2)
            (ow_challenge_x.set x σ) := by
      intro x
      show (ow_adv >>= fun _ : Unit =>
              Program.get oracle_input >>= fun inp =>
                Program.get ow_challenge_x >>= fun cx =>
                  (if inp = cx then Program.set chal_x_queried true
                   else (pure () : Program state Unit)) >>= fun _ =>
                    lazy_query inp >>= fun y =>
                      Program.set oracle_output y).wp G (ow_challenge_x.set x σ) = _
      rw [wp_bind]
    simp_rw [h_step2]
    -- Step 3: Shift chal_x.set x past ow_adv using wp_shift_input.
    have h_shift_chal_x : ow_challenge_x.set ∈ Set.univ ∧
        ∀ x : input, ow_challenge_x.update (Function.const _ x) ∈
            ((ow_challenge_x.compl.range : TotLensRange state)ᶜ).updates := by
      refine ⟨Set.mem_univ _, ?_⟩
      intro x
      rw [show ((ow_challenge_x.compl.range : TotLensRange state)ᶜ) = ow_challenge_x.range from by
        rw [TotLensRange.complement_range, TotLensRange.compl_compl]]
      exact ⟨Function.const _ x, Set.mem_univ _, rfl⟩
    -- Rewrite ow_challenge_x.set x σ = (ow_challenge_x.update (const x)) σ.
    have h_set_as_update : ∀ x : input, ow_challenge_x.set x σ
        = (ow_challenge_x.update (Function.const _ x)) σ := by
      intro x
      show ow_challenge_x.set x σ
        = ow_challenge_x.set ((Function.const _ x) (ow_challenge_x.get σ)) σ
      rw [Function.const_apply]
    -- Step 4: Apply wp_shift_input on ow_adv.
    have h_shift : ∀ x : input,
        ow_adv.wp (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp G aσ_adv.2)
            (ow_challenge_x.set x σ)
        = ow_adv.wp (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp G (ow_challenge_x.set x aσ_adv.2))
            σ := by
      intro x
      rw [h_set_as_update x]
      exact Program.wp_shift_input h_ow_adv_chal_x (h_shift_chal_x.2 x) _ σ
    simp_rw [h_shift]
    -- Step 5: Pull sum inside ow_adv.wp using wp_finset_sum.
    rw [← Program.wp_finset_sum]
    -- Step 6: Bound the inner sum ≤ 1 + q, then ow_adv.wp ≤ 1 + q.
    have h_target : ((q + 1 : ℕ) : ENNReal) = 1 + (q : ENNReal) := by push_cast; ring
    rw [h_target]
    -- Apply wp_strengthen on ow_adv to add `chal_x_queried.get aσ_adv.2 = false`.
    rw [Program.wp_strengthen_lens_preserved chal_x_queried h_ow_adv_chal_x_queried _ σ]
    refine le_trans (Program.wp_le_wp_of_le ow_adv _ (fun _ => 1 + (q : ENNReal)) ?_ σ)
                    (Program.wp_const_le ow_adv _ σ)
    intro aσ_adv
    -- The post is `if cxq_aσ_adv = cxq_σ then ... else 0`. Case-split.
    by_cases h_cxq_adv : chal_x_queried.get aσ_adv.2 = chal_x_queried.get σ
    swap
    · simp only [if_neg h_cxq_adv]; exact bot_le
    simp only [if_pos h_cxq_adv]
    -- We now know cxq.get aσ_adv.2 = cxq.get σ = false.
    have h_aσ_adv_qf : chal_x_queried.get aσ_adv.2 = false := h_cxq_adv.trans h_σ
    -- Show: ∑ x : input, post_adv.wp G (ow_challenge_x.set x aσ_adv.2) ≤ 1 + q.
    set inp := oracle_input.get aσ_adv.2 with h_inp_def
    -- helpers for state operations on chal_x.set x aσ_adv.2.
    haveI _disj_cx_oi : disjoint ow_challenge_x oracle_input :=
      disjoint_oracle_input_ow_challenge_x.symm
    have h_inp_get : ∀ x : input,
        oracle_input.get (ow_challenge_x.set x aσ_adv.2) = inp := by
      intro x; rw [oracle_input.get_of_disjoint_set]
    have h_cx_get : ∀ x : input,
        ow_challenge_x.get (ow_challenge_x.set x aσ_adv.2) = x := fun x =>
      ow_challenge_x.set_get _ _
    -- (lazy_query inp >>= set oracle_output) is in ow_challenge_x.compl.range.
    have h_lqso_inRange_cx_compl :
        (lazy_query inp >>= fun y => Program.set oracle_output y).inRange
            ow_challenge_x.compl.range := by
      refine Program.inRange_bind ?_ ?_
      · exact Program.inRange_mono (lazy_query_inRange_ro inp)
          (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_x)
      · intro y
        exact Program.set_inRange_compl_of_disjoint oracle_output ow_challenge_x _
    -- (lazy_query inp >>= set oracle_output) is in chal_x_queried.compl.range.
    have h_lqso_inRange_cxq_compl :
        (lazy_query inp >>= fun y => Program.set oracle_output y).inRange
            chal_x_queried.compl.range :=
      lazy_query_then_set_oracle_output_inRange_chal_x_queried_compl inp
    -- G is bounded by 1 pointwise.
    have h_G_le_one : ∀ aσ_b : Unit × state, G aσ_b ≤ 1 := by
      intro aσ_b
      show (ow_loop_tracked ow_adv q lazy_query).wp F aσ_b.2 ≤ 1
      refine le_trans (Program.wp_le_wp_of_le _ F (fun _ => 1) ?_ aσ_b.2)
                      (Program.wp_const_le _ 1 aσ_b.2)
      intro aσ
      show (if chal_x_queried.get aσ.2 then (1 : ENNReal) else 0) ≤ 1
      split <;> [rfl; exact bot_le]
    -- Pointwise: post_adv.wp G (chal_x.set x aσ_adv.2) ≤
    --   (if x = inp then 1 else 0) + (lazy_query inp >>= set oracle_output).wp G (chal_x.set x aσ_adv.2)
    have h_pointwise : ∀ x : input,
        (Program.get oracle_input >>= fun inp' =>
          Program.get ow_challenge_x >>= fun cx =>
            (if inp' = cx then Program.set chal_x_queried true
             else (pure () : Program state Unit)) >>= fun _ =>
              lazy_query inp' >>= fun y =>
                Program.set oracle_output y).wp G (ow_challenge_x.set x aσ_adv.2)
        ≤ (if x = inp then (1 : ENNReal) else 0) +
            (lazy_query inp >>= fun y =>
              Program.set oracle_output y).wp G (ow_challenge_x.set x aσ_adv.2) := by
      intro x
      -- Unfold wp via get, ite, set/pure.
      simp only [wp_bind, wp_get]
      rw [h_inp_get x, h_cx_get x]
      by_cases h : inp = x
      · simp only [if_pos h]
        rw [wp_set]
        have h_xi : x = inp := h.symm
        rw [if_pos h_xi]
        refine le_add_right ?_
        -- Goal: (lazy_query inp).wp (fun x ↦ (set oracle_output x.1).wp G x.2)
        --         (chal_x_queried.set true (chal_x.set x aσ_adv.2)) ≤ 1
        refine le_trans (Program.wp_le_wp_of_le _ _ (fun _ => 1) ?_ _) ?_
        · intro xy
          refine le_trans (Program.wp_le_wp_of_le _ _ (fun _ => 1) ?_ _) ?_
          · intro xz; exact h_G_le_one xz
          · exact Program.wp_const_le _ 1 _
        · exact Program.wp_const_le _ 1 _
      · simp only [if_neg h]
        rw [wp_pure]
        have h_xi : x ≠ inp := fun he => h he.symm
        rw [if_neg h_xi, zero_add]
    -- Sum the pointwise bound.
    refine le_trans (Finset.sum_le_sum (fun x _ => h_pointwise x)) ?_
    rw [Finset.sum_add_distrib]
    -- Goal: ∑ x, (if x = inp then 1 else 0) + ∑ x, (lazy_query >>= ...).wp G (chal_x.set x aσ_adv.2) ≤ 1 + q
    rw [show ∑ x : input, (if x = inp then (1 : ENNReal) else 0) = 1 by
      rw [Finset.sum_ite_eq' Finset.univ inp (fun _ => (1 : ENNReal))]
      simp]
    -- Goal: 1 + ∑ x, (lazy_query inp >>= set oracle_output).wp G (chal_x.set x aσ_adv.2) ≤ 1 + q
    refine add_le_add (le_refl _) ?_
    -- Goal: ∑ x, (lazy_query inp >>= set oracle_output).wp G (chal_x.set x aσ_adv.2) ≤ q.
    -- Apply wp_shift_input on (lazy_query inp >>= set oracle_output) (in chal_x.compl.range).
    have h_shift_lqso : ∀ x : input,
        (lazy_query inp >>= fun y => Program.set oracle_output y).wp G
          (ow_challenge_x.set x aσ_adv.2)
        = (lazy_query inp >>= fun y => Program.set oracle_output y).wp
          (fun aσ_lq : Unit × state => G (aσ_lq.1, ow_challenge_x.set x aσ_lq.2))
          aσ_adv.2 := by
      intro x
      rw [show ow_challenge_x.set x aσ_adv.2
          = (ow_challenge_x.update (Function.const _ x)) aσ_adv.2 by
        show ow_challenge_x.set x aσ_adv.2
          = ow_challenge_x.set ((Function.const _ x) (ow_challenge_x.get aσ_adv.2)) aσ_adv.2
        rw [Function.const_apply]]
      exact Program.wp_shift_input h_lqso_inRange_cx_compl (h_shift_chal_x.2 x) _ _
    simp_rw [h_shift_lqso]
    -- Apply wp_finset_sum to pull sum inside.
    rw [← Program.wp_finset_sum]
    -- Apply wp_strengthen_lens_preserved on (lazy_query inp >>= set oracle_output)
    -- with L = chal_x_queried to add `cxq_aσ_lq = cxq_aσ_adv` to the post.
    rw [Program.wp_strengthen_lens_preserved chal_x_queried h_lqso_inRange_cxq_compl _ aσ_adv.2]
    refine le_trans
      (Program.wp_le_wp_of_le _ _ (fun _ => (q : ENNReal)) ?_ aσ_adv.2)
      (Program.wp_const_le _ _ _)
    intro aσ_lq
    -- The post is `if cxq_aσ_lq = cxq_aσ_adv then ∑ x ... else 0`.
    by_cases h_cxq_lq : chal_x_queried.get aσ_lq.2 = chal_x_queried.get aσ_adv.2
    swap
    · simp only [if_neg h_cxq_lq]; exact bot_le
    simp only [if_pos h_cxq_lq]
    -- Combine: cxq_aσ_lq = cxq_aσ_adv = false. Apply IH.
    have h_aσ_lq_qf : chal_x_queried.get aσ_lq.2 = false := h_cxq_lq.trans h_aσ_adv_qf
    exact ih aσ_lq.2 h_aσ_lq_qf

-- `lazy_query_set_oracle_output_preserves_RO_at_other_key` moved to RO.lean.
-- `RO_setentry_neq_commutes_lazy_query_set_oracle_output` moved to RO.lean.

/-- **Averaged RO invariance** for `ow_loop_tracked`'s `chal_x_queried`
    indicator: averaging over uniform `y` of the loop's wp at
    `RO_setentry chal_x y σ` equals the wp at `σ`.

    This is the deferred-sampling content needed for the experiment-level
    bound. Provable WITHOUT adv-termination assumption, by variable
    renaming in the `inp = x` case and IH application in the `inp ≠ x`
    case (using `RO_setentry_neq_commutes_lazy_query_set_oracle_output`). -/
private lemma ow_loop_tracked_chal_x_queried_RO_invariance_avg
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried' : ow_adv.inRange chal_x_queried.compl.range) :
    ∀ (q : ℕ) (σ : state),
    chal_x_queried.get σ = false →
    random_oracle_state.get σ (ow_challenge_x.get σ) = none →
    (1 : ENNReal) / Fintype.card output *
      ∑ y : output, (ow_loop_tracked ow_adv q lazy_query).wp
        (fun aσ : Unit × state =>
          if chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)
        (random_oracle_state.set
          (fun k => if k = ow_challenge_x.get σ then some y
                    else random_oracle_state.get σ k) σ)
    = (ow_loop_tracked ow_adv q lazy_query).wp
        (fun aσ : Unit × state =>
          if chal_x_queried.get aσ.2 then (1 : ENNReal) else 0) σ := by
  intro q
  induction q with
  | zero =>
    intro σ h_qf h_ro
    show (1 : ENNReal) / Fintype.card output *
        ∑ y : output, (Pure.pure () : Program state Unit).wp _ _
      = (Pure.pure () : Program state Unit).wp _ _
    simp_rw [wp_pure]
    -- RO_setentry preserves chal_x_queried.get (lens disjoint).
    have h_cxq_unchanged : ∀ y : output,
        chal_x_queried.get (random_oracle_state.set
          (fun k => if k = ow_challenge_x.get σ then some y
                    else random_oracle_state.get σ k) σ)
        = chal_x_queried.get σ := by
      intro y
      rw [chal_x_queried.get_of_disjoint_set]
    simp_rw [h_cxq_unchanged]
    rw [h_qf]
    simp
  | succ q ih =>
    intro σ h_qf h_ro
    set x := ow_challenge_x.get σ with x_def
    set F : Unit × state → ENNReal :=
      fun aσ : Unit × state => if chal_x_queried.get aσ.2 then (1 : ENNReal) else 0 with hF_def
    set G : Unit × state → ENNReal :=
      fun aσ_b : Unit × state => (ow_loop_tracked ow_adv q lazy_query).wp F aσ_b.2 with hG_def
    -- Reduce loop_{q+1} = body >>= loop_q on both sides.
    have h_unfold : ∀ σ' : state,
        (ow_loop_tracked ow_adv (q+1) lazy_query).wp F σ'
        = (ow_loop_body_tracked ow_adv lazy_query).wp G σ' := by
      intro σ'
      show (ow_loop_body_tracked ow_adv lazy_query >>= fun _ : Unit =>
              ow_loop_tracked ow_adv q lazy_query).wp F σ' = _
      rw [wp_bind]
    simp_rw [h_unfold]
    -- Now: (1/|output|) ∑ y body.wp G (RO_setentry x y σ) = body.wp G σ.
    -- body = adv >>= post_adv. Apply wp_bind.
    have h_body_unfold : ∀ σ' : state,
        (ow_loop_body_tracked ow_adv lazy_query).wp G σ'
        = ow_adv.wp (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp G aσ_adv.2) σ' := by
      intro σ'
      show (ow_adv >>= fun _ : Unit =>
              Program.get oracle_input >>= fun inp =>
                Program.get ow_challenge_x >>= fun cx =>
                  (if inp = cx then Program.set chal_x_queried true
                   else (pure () : Program state Unit)) >>= fun _ =>
                    lazy_query inp >>= fun y =>
                      Program.set oracle_output y).wp G σ' = _
      rw [wp_bind]
    simp_rw [h_body_unfold]
    -- Apply wp_shift_input on adv with shift = RO_setentry x y.
    have h_shift : ∀ y' : output,
        ow_adv.wp (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp G aσ_adv.2)
            (random_oracle_state.set
              (fun k => if k = x then some y'
                        else random_oracle_state.get σ k) σ)
        = ow_adv.wp (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp G
              (random_oracle_state.set
                (fun k => if k = x then some y'
                          else random_oracle_state.get aσ_adv.2 k) aσ_adv.2)) σ := by
      intro y'
      have h_shift_in : (fun σ' => random_oracle_state.set
          (fun k => if k = x then some y' else random_oracle_state.get σ' k) σ')
          ∈ ((random_oracle_state.compl.range : TotLensRange state)ᶜ).updates := by
        rw [show ((random_oracle_state.compl.range : TotLensRange state)ᶜ)
            = random_oracle_state.range from by
          rw [TotLensRange.complement_range, TotLensRange.compl_compl]]
        exact ⟨fun h => fun k => if k = x then some y' else h k, Set.mem_univ _, rfl⟩
      exact Program.wp_shift_input h_ow_adv h_shift_in _ σ
    simp_rw [h_shift]
    -- Pull sum and 1/|output| inside ow_adv.wp.
    rw [← Program.wp_finset_sum, ← Program.wp_const_mul]
    -- Apply wp_strengthen_lens_preserved 3x: RO, ow_challenge_x, chal_x_queried.
    rw [Program.wp_strengthen_lens_preserved random_oracle_state h_ow_adv _ σ,
        Program.wp_strengthen_lens_preserved random_oracle_state h_ow_adv
          (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
                Program.get ow_challenge_x >>= fun cx =>
                  (if inp = cx then Program.set chal_x_queried true
                   else (pure () : Program state Unit)) >>= fun _ =>
                    lazy_query inp >>= fun y_lq =>
                      Program.set oracle_output y_lq).wp G aσ_adv.2) σ]
    rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_ow_adv_chal_x _ σ,
        Program.wp_strengthen_lens_preserved ow_challenge_x h_ow_adv_chal_x
          (fun aσ_adv : Unit × state =>
            if random_oracle_state.get aσ_adv.2 = random_oracle_state.get σ then
              (Program.get oracle_input >>= fun inp =>
                  Program.get ow_challenge_x >>= fun cx =>
                    (if inp = cx then Program.set chal_x_queried true
                     else (pure () : Program state Unit)) >>= fun _ =>
                      lazy_query inp >>= fun y_lq =>
                        Program.set oracle_output y_lq).wp G aσ_adv.2
            else 0) σ]
    rw [Program.wp_strengthen_lens_preserved chal_x_queried h_ow_adv_chal_x_queried' _ σ,
        Program.wp_strengthen_lens_preserved chal_x_queried h_ow_adv_chal_x_queried'
          (fun aσ_adv : Unit × state =>
            if ow_challenge_x.get aσ_adv.2 = ow_challenge_x.get σ then
              if random_oracle_state.get aσ_adv.2 = random_oracle_state.get σ then
                (Program.get oracle_input >>= fun inp =>
                    Program.get ow_challenge_x >>= fun cx =>
                      (if inp = cx then Program.set chal_x_queried true
                       else (pure () : Program state Unit)) >>= fun _ =>
                        lazy_query inp >>= fun y_lq =>
                          Program.set oracle_output y_lq).wp G aσ_adv.2
              else 0
            else 0) σ]
    apply congrArg (fun P => ow_adv.wp P σ)
    funext aσ_adv
    by_cases h_cxq_pres : chal_x_queried.get aσ_adv.2 = chal_x_queried.get σ
    swap
    · simp only [if_neg h_cxq_pres]
    simp only [if_pos h_cxq_pres]
    by_cases h_cx_pres : ow_challenge_x.get aσ_adv.2 = ow_challenge_x.get σ
    swap
    · simp only [if_neg h_cx_pres]
    simp only [if_pos h_cx_pres]
    by_cases h_ro_pres : random_oracle_state.get aσ_adv.2 = random_oracle_state.get σ
    swap
    · simp only [if_neg h_ro_pres]
    simp only [if_pos h_ro_pres]
    have h_aσ_adv_chal_x : ow_challenge_x.get aσ_adv.2 = x := h_cx_pres
    have h_aσ_adv_ro_x : random_oracle_state.get aσ_adv.2 x = none := by
      rw [h_ro_pres]; exact h_ro
    have h_aσ_adv_cxq : chal_x_queried.get aσ_adv.2 = false := by
      rw [h_cxq_pres]; exact h_qf
    -- Goal: (1/|output|) ∑ y, post_adv.wp G (RO_setentry x y aσ_adv.2) = post_adv.wp G aσ_adv.2.
    -- Step 1: unfold post_adv via wp_bind + wp_get.
    simp only [wp_bind, wp_get]
    -- For RO_setentry x y aσ_adv.2: oracle_input.get and ow_challenge_x.get are same as on aσ_adv.2.
    haveI _disj_ro_oi : disjoint random_oracle_state oracle_input :=
      disjoint_oracle_input_ro.symm
    have h_oi_RO : ∀ y_arg : output,
        oracle_input.get (random_oracle_state.set
          (fun k => if k = x then some y_arg
                    else random_oracle_state.get aσ_adv.2 k) aσ_adv.2)
        = oracle_input.get aσ_adv.2 := by
      intro _; rw [oracle_input.get_of_disjoint_set]
    have h_cx_RO : ∀ y_arg : output,
        ow_challenge_x.get (random_oracle_state.set
          (fun k => if k = x then some y_arg
                    else random_oracle_state.get aσ_adv.2 k) aσ_adv.2)
        = ow_challenge_x.get aσ_adv.2 := by
      intro _; rw [ow_challenge_x.get_of_disjoint_set]
    simp_rw [h_oi_RO, h_cx_RO, h_aσ_adv_chal_x]
    -- Now both sides have `if oracle_input.get aσ_adv.2 = x then ... else ...`.
    set inp_a := oracle_input.get aσ_adv.2 with inp_a_def
    by_cases h_inp : inp_a = x
    · -- HIT case (inp_a = x): variable renaming.
      simp only [if_pos h_inp]
      -- Substitute inp_a = x throughout.
      rw [h_inp]
      -- LHS: (1/|output|) ∑ y, (set chal_x_queried true; lazy_query x; set oracle_output).wp G
      --        (RO_setentry x y aσ_adv.2)
      -- RHS: (set chal_x_queried true; lazy_query x; set oracle_output).wp G aσ_adv.2
      -- By wp_bind + wp_set on `set chal_x_queried true`:
      simp only [wp_bind, wp_set]
      -- Now both sides involve (lazy_query x; set oracle_output).wp G (chal_x_queried.set true ...).
      haveI _disj_cxq_ro : disjoint chal_x_queried random_oracle_state :=
        disjoint_chal_x_queried_ro
      -- LHS state at chal_x_queried.set true (RO_setentry x y aσ_adv.2)
      --      = RO_setentry x y (chal_x_queried.set true aσ_adv.2) (by disjoint commute).
      have h_commute_LHS : ∀ y_arg : output,
          chal_x_queried.set true
            (random_oracle_state.set
              (fun k => if k = x then some y_arg
                        else random_oracle_state.get aσ_adv.2 k) aσ_adv.2)
          = random_oracle_state.set
              (fun k => if k = x then some y_arg
                        else random_oracle_state.get (chal_x_queried.set true aσ_adv.2) k)
              (chal_x_queried.set true aσ_adv.2) := by
        intro y_arg
        rw [_disj_cxq_ro.commute]
        congr 1
        funext k
        rw [random_oracle_state.get_of_disjoint_set chal_x_queried true aσ_adv.2]
      simp_rw [h_commute_LHS]
      -- Now LHS = (1/|output|) ∑ y, (lazy_query x; set oracle_output).wp G (RO_setentry x y σ_arg)
      -- RHS = (lazy_query x; set oracle_output).wp G σ_arg
      -- where σ_arg = chal_x_queried.set true aσ_adv.2.
      -- σ_arg.RO[x] = aσ_adv.2.RO[x] = none.
      have h_σ_arg_ro : random_oracle_state.get (chal_x_queried.set true aσ_adv.2) x = none := by
        rw [random_oracle_state.get_of_disjoint_set chal_x_queried true aσ_adv.2]
        exact h_aσ_adv_ro_x
      -- Compute both sides via lazy_query's wp.
      -- For LHS state RO_setentry x y σ_arg: RO[x] = some y. lazy_query returns y.
      -- For RHS state σ_arg: RO[x] = none. lazy_query samples uniform.
      have h_LHS_get_x : ∀ y_arg : output,
          random_oracle_state.get
            (random_oracle_state.set
              (fun k => if k = x then some y_arg
                        else random_oracle_state.get (chal_x_queried.set true aσ_adv.2) k)
              (chal_x_queried.set true aσ_adv.2)) x
          = some y_arg := by
        intro y_arg
        rw [random_oracle_state.set_get]; simp
      simp only [lazy_query, wp_bind, wp_get, wp_uniform, wp_pure, wp_set]
      simp_rw [h_LHS_get_x, h_σ_arg_ro]
      -- LHS now has pure for each y. RHS has do-block (none branch).
      -- Apply more simp to unfold do-block.
      simp only [wp_bind, wp_uniform, wp_set, wp_pure]
      -- Both sides equal up to (1/c) * ∑ vs ∑ ../c distribution.
      rw [Finset.mul_sum]
      congr 1
      funext y_arg
      simp only [one_div, mul_one, ENNReal.div_eq_inv_mul]
    · -- MISS case (inp_a ≠ x): RO_setentry_commute + IH.
      simp only [if_neg h_inp]
      -- The goal already has (pure ()).wp form. Reduce via wp_pure.
      simp only [wp_pure]
      -- Now refold via ← wp_bind to get (lazy_query inp_a >>= set oracle_output).wp.
      simp_rw [← wp_bind]
      -- Apply RO_setentry_commute per y.
      have h_commute : ∀ y_arg : output,
          (lazy_query inp_a >>= fun y_lq => Program.set oracle_output y_lq).wp G
            (random_oracle_state.set
              (fun k => if k = x then some y_arg
                        else random_oracle_state.get aσ_adv.2 k) aσ_adv.2)
          = (lazy_query inp_a >>= fun y_lq => Program.set oracle_output y_lq).wp
              (fun aσ_lq => G (aσ_lq.1, random_oracle_state.set
                                      (fun k => if k = x then some y_arg
                                               else random_oracle_state.get aσ_lq.2 k) aσ_lq.2))
              aσ_adv.2 :=
        fun y_arg => RO_setentry_neq_commutes_lazy_query_set_oracle_output
          inp_a x h_inp y_arg aσ_adv.2 G
      simp_rw [h_commute]
      -- Pull (1/|output|) ∑ y inside the outer wp via wp_finset_sum + wp_const_mul.
      rw [← Program.wp_finset_sum, ← Program.wp_const_mul]
      -- Apply wp_strengthen 3x on both sides to enforce preconditions.
      have h_inRange_cxq : (lazy_query inp_a >>= fun y_lq =>
          Program.set oracle_output y_lq).inRange chal_x_queried.compl.range :=
        lazy_query_then_set_oracle_output_inRange_chal_x_queried_compl inp_a
      have h_inRange_cx : (lazy_query inp_a >>= fun y_lq =>
          Program.set oracle_output y_lq).inRange ow_challenge_x.compl.range :=
        lazy_query_then_set_oracle_output_inRange_ow_challenge_x_compl inp_a
      -- Strengthen LHS with three conditions stacked (use conv_lhs to disambiguate).
      conv_lhs =>
        rw [Program.wp_strengthen_lens_preserved chal_x_queried h_inRange_cxq _ aσ_adv.2,
            Program.wp_strengthen_lens_preserved ow_challenge_x h_inRange_cx _ aσ_adv.2,
            lazy_query_set_oracle_output_preserves_RO_at_other_key inp_a x h_inp aσ_adv.2 _]
      -- Strengthen RHS with same three conditions stacked.
      conv_rhs =>
        rw [Program.wp_strengthen_lens_preserved chal_x_queried h_inRange_cxq G aσ_adv.2,
            Program.wp_strengthen_lens_preserved ow_challenge_x h_inRange_cx _ aσ_adv.2,
            lazy_query_set_oracle_output_preserves_RO_at_other_key inp_a x h_inp aσ_adv.2 _]
      -- Now both sides have the same outer structure. Show post equality per aσ_lq.
      congr 1
      funext aσ_lq
      -- Per-aσ_lq: case on the 3 stacked if-conditions.
      by_cases h_ro_lq : random_oracle_state.get aσ_lq.2 x
          = random_oracle_state.get aσ_adv.2 x
      swap
      · simp only [if_neg h_ro_lq]
      simp only [if_pos h_ro_lq]
      by_cases h_cx_lq : ow_challenge_x.get aσ_lq.2 = ow_challenge_x.get aσ_adv.2
      swap
      · simp only [if_neg h_cx_lq]
      simp only [if_pos h_cx_lq]
      by_cases h_cxq_lq : chal_x_queried.get aσ_lq.2 = chal_x_queried.get aσ_adv.2
      swap
      · simp only [if_neg h_cxq_lq]
      simp only [if_pos h_cxq_lq]
      -- Now aσ_lq.2 satisfies: cxq = false, chal_x = x, RO[x] = none.
      have h_aσ_lq_cxq : chal_x_queried.get aσ_lq.2 = false :=
        h_cxq_lq.trans h_aσ_adv_cxq
      have h_aσ_lq_chal_x : ow_challenge_x.get aσ_lq.2 = x :=
        h_cx_lq.trans h_aσ_adv_chal_x
      have h_aσ_lq_ro_x : random_oracle_state.get aσ_lq.2 x = none :=
        h_ro_lq.trans h_aσ_adv_ro_x
      have h_aσ_lq_ro_chal_x : random_oracle_state.get aσ_lq.2
          (ow_challenge_x.get aσ_lq.2) = none := by
        rw [h_aσ_lq_chal_x]; exact h_aσ_lq_ro_x
      -- Apply IH at aσ_lq.2.
      have h_ih := ih aσ_lq.2 h_aσ_lq_cxq h_aσ_lq_ro_chal_x
      -- h_ih has chal_x.get aσ_lq.2; substitute to x.
      rw [h_aσ_lq_chal_x] at h_ih
      exact h_ih

/-- **Lazy-query freshness invariance** for the chal_x_queried indicator:
    pre-setting `RO[x] = y` (uniform y) is equivalent (averaged over y) to
    no pre-set entry, when the post is the chal_x_queried indicator.

    Intuition: the indicator only depends on WHETHER adv queried x, not on
    the response value. Adv's pre-x-query behavior is independent of RO[x].
    So the iter of first hit (if any) has the same distribution. -/
private lemma ow_loop_tracked_lazy_query_freshness
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried : ow_adv.inRange chal_x_queried.compl.range)
    (q : ℕ) (x : input) (σ : state)
    (h_σ_qf : chal_x_queried.get σ = false)
    (h_σ_ro : random_oracle_state.get σ x = none) :
    (lazy_query x >>= fun y => Program.set ow_challenge_y y >>= fun _ =>
        ow_loop_tracked ow_adv q lazy_query).wp
      (fun aσ : Unit × state =>
        if chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)
      (ow_challenge_x.set x σ)
    = (ow_loop_tracked ow_adv q lazy_query).wp
      (fun aσ : Unit × state =>
        if chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)
      (ow_challenge_x.set x σ) := by
  set σ_in := ow_challenge_x.set x σ with σ_in_def
  set F : Unit × state → ENNReal :=
    fun aσ : Unit × state => if chal_x_queried.get aσ.2 then (1 : ENNReal) else 0 with hF_def
  -- σ_in properties.
  have h_σ_in_cxq : chal_x_queried.get σ_in = false := by
    rw [σ_in_def, chal_x_queried.get_of_disjoint_set]; exact h_σ_qf
  have h_σ_in_chal_x : ow_challenge_x.get σ_in = x := ow_challenge_x.set_get σ x
  have h_σ_in_ro_x : random_oracle_state.get σ_in x = none := by
    rw [σ_in_def, random_oracle_state.get_of_disjoint_set]; exact h_σ_ro
  have h_σ_in_ro_chal_x : random_oracle_state.get σ_in (ow_challenge_x.get σ_in) = none := by
    rw [h_σ_in_chal_x]; exact h_σ_in_ro_x
  -- inRange for ow_loop_tracked w.r.t. ow_challenge_y.
  have h_loop_inRange_cy : (ow_loop_tracked ow_adv q lazy_query).inRange
      ow_challenge_y.compl.range :=
    ow_loop_tracked_inRange_ow_challenge_y_compl ow_adv h_ow_adv_chal_y q
  -- F doesn't read ow_challenge_y (only reads chal_x_queried; chal_x_queried ⟂ ow_challenge_y).
  have h_F_no_cy : ∀ v : output, ∀ aσ : Unit × state,
      F (aσ.1, ow_challenge_y.set v aσ.2) = F aσ := by
    intro v aσ
    simp only [hF_def]
    rw [chal_x_queried.get_of_disjoint_set]
  -- (set ow_challenge_y v; ow_loop_tracked).wp F σ' = ow_loop_tracked.wp F σ' for all σ', v.
  have h_drop_chal_y : ∀ (v : output) (σ' : state),
      (Program.set ow_challenge_y v >>= fun _ : Unit =>
          ow_loop_tracked ow_adv q lazy_query).wp F σ'
      = (ow_loop_tracked ow_adv q lazy_query).wp F σ' :=
    fun v σ' => Program.wp_set_disjoint_no_op h_loop_inRange_cy v F (h_F_no_cy v) σ'
  -- Apply wp_bind on outer and h_drop_chal_y inside.
  rw [wp_bind]
  simp_rw [h_drop_chal_y]
  -- Now: (lazy_query x).wp (fun aσ_lq => ow_loop_tracked.wp F aσ_lq.2) σ_in = ow_loop_tracked.wp F σ_in.
  -- Compute (lazy_query x).wp at σ_in where σ_in.RO[x] = none.
  have h_lq_compute : ∀ (Q : output × state → ENNReal),
      (lazy_query x).wp Q σ_in
      = ∑ v : output, Q (v, random_oracle_state.set
          (fun k => if k = x then some v else random_oracle_state.get σ_in k) σ_in)
            / Fintype.card output := by
    intro Q
    show (do let h <- Program.get random_oracle_state
             match h x with
             | some v => pure v
             | none => do let value <- Program.uniform
                          Program.set random_oracle_state
                            (fun k => if k=x then some value else h k)
                          pure value).wp Q σ_in = _
    simp only [wp_bind, wp_get]
    rw [h_σ_in_ro_x]
    simp only [wp_bind, wp_uniform, wp_set, wp_pure]
  rw [h_lq_compute]
  -- Goal: ∑ v, ow_loop_tracked.wp F (RO_setentry x v σ_in) / |output| = ow_loop_tracked.wp F σ_in.
  -- Apply averaged freshness at σ_in.
  have h_avg := ow_loop_tracked_chal_x_queried_RO_invariance_avg ow_adv h_ow_adv
    h_ow_adv_chal_y h_ow_adv_chal_x h_ow_adv_chal_x_queried q σ_in h_σ_in_cxq h_σ_in_ro_chal_x
  rw [h_σ_in_chal_x] at h_avg
  -- h_avg: (1/|output|) * ∑ y, ow_loop_tracked.wp F (RO_setentry x y σ_in) = ow_loop_tracked.wp F σ_in.
  -- Convert sum-divided-by-c form to const-mul-sum form.
  rw [show ∀ (g : output → ENNReal),
      (∑ v : output, g v / Fintype.card output)
      = 1 / Fintype.card output * ∑ v : output, g v from fun g => by
    rw [Finset.mul_sum]; congr 1; funext v; rw [ENNReal.div_eq_inv_mul, one_div]]
  exact h_avg

/-- Helper: `post_loop` (`get resp; lazy_query resp; pure (decide ...)`) preserves
    `chal_x_queried`. Hence its wp at the chal_x_queried indicator equals the
    indicator at the input state. -/
private lemma post_loop_preserves_chal_x_queried_wp
    (y_chal : output) (σ : state) :
    (Program.get ow_response >>= fun resp =>
      lazy_query resp >>= fun y_check =>
        (pure (decide (y_check = y_chal)) : Program state Bool)).wp
      (fun bσ : Bool × state => if chal_x_queried.get bσ.2 then (1 : ENNReal) else 0) σ
    ≤ (if chal_x_queried.get σ then (1 : ENNReal) else 0) := by
  -- post_loop is in chal_x_queried.compl.range. Bound the wp by mass · indicator.
  have h_inRange : (Program.get ow_response >>= fun resp =>
      lazy_query resp >>= fun y_check =>
        (pure (decide (y_check = y_chal)) : Program state Bool)).inRange
      chal_x_queried.compl.range := post_loop_inRange_chal_x_queried_compl y_chal
  -- Use wp_strengthen_lens_preserved with L = chal_x_queried.
  rw [Program.wp_strengthen_lens_preserved chal_x_queried h_inRange _ σ]
  -- Now post is `if cxq.get bσ.2 = cxq.get σ then F bσ else 0`.
  -- Bound by `if cxq.get σ then 1 else 0` (constant).
  refine le_trans (Program.wp_le_wp_of_le _ _ _ ?_ σ)
                  (Program.wp_const_le _ _ σ)
  intro bσ
  by_cases h : chal_x_queried.get bσ.2 = chal_x_queried.get σ
  · rw [if_pos h, h]
  · rw [if_neg h]; exact bot_le

/-- Helper: `post_loop` preserves the indep indicator `[resp = chal_x ∧ ¬cxq]`.
    Argument: after `get ow_response`, the remaining `lazy_query resp; pure decide`
    is in `random_oracle_state.range`, which is in the compl range of `ow_response`,
    `ow_challenge_x`, and `chal_x_queried` (all disjoint from RO). -/
private lemma post_loop_preserves_indep_wp
    (y_chal : output) (σ : state) :
    (Program.get ow_response >>= fun resp =>
      lazy_query resp >>= fun y_check =>
        (pure (decide (y_check = y_chal)) : Program state Bool)).wp
      (fun bσ : Bool × state =>
        if ow_response.get bσ.2 = ow_challenge_x.get bσ.2 ∧ ¬ chal_x_queried.get bσ.2
        then (1 : ENNReal) else 0) σ
    ≤ (if ow_response.get σ = ow_challenge_x.get σ ∧ ¬ chal_x_queried.get σ
       then (1 : ENNReal) else 0) := by
  rw [wp_bind, wp_get]
  simp only []  -- beta-reduce
  -- Goal: (lazy_query (ow_response.get σ) >>= pure decide).wp F_bool σ ≤ indicator(σ).
  set resp_val := ow_response.get σ with h_resp_val_def
  -- (lazy_query resp_val; pure decide).wp F_bool σ.
  rw [wp_bind]
  -- (lazy_query resp_val).wp (fun (y_check, σ') => (pure decide).wp F_bool σ') σ.
  -- lazy_query is in random_oracle_state.range. Apply wp_strengthen for resp, chal_x, cxq.
  have h_lq_inRange_resp : (lazy_query resp_val).inRange ow_response.compl.range :=
    Program.inRange_mono (lazy_query_inRange_ro _)
      (Lens.range_le_compl_of_disjoint random_oracle_state ow_response)
  have h_lq_inRange_cx : (lazy_query resp_val).inRange ow_challenge_x.compl.range :=
    Program.inRange_mono (lazy_query_inRange_ro _)
      (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_x)
  have h_lq_inRange_cxq : (lazy_query resp_val).inRange chal_x_queried.compl.range :=
    Program.inRange_mono (lazy_query_inRange_ro _)
      (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried)
  rw [Program.wp_strengthen_lens_preserved ow_response h_lq_inRange_resp _ σ,
      Program.wp_strengthen_lens_preserved ow_challenge_x h_lq_inRange_cx _ σ,
      Program.wp_strengthen_lens_preserved chal_x_queried h_lq_inRange_cxq _ σ]
  refine le_trans
    (Program.wp_le_wp_of_le _ _ (fun _ =>
      if ow_response.get σ = ow_challenge_x.get σ ∧ ¬ chal_x_queried.get σ
      then (1 : ENNReal) else 0) ?_ σ)
    (Program.wp_const_le _ _ σ)
  intro yσ
  by_cases h_cxq_pres : chal_x_queried.get yσ.2 = chal_x_queried.get σ
  swap
  · simp only [if_neg h_cxq_pres]; exact bot_le
  simp only [if_pos h_cxq_pres]
  by_cases h_cx_pres : ow_challenge_x.get yσ.2 = ow_challenge_x.get σ
  swap
  · simp only [if_neg h_cx_pres]; exact bot_le
  simp only [if_pos h_cx_pres]
  by_cases h_resp_pres : ow_response.get yσ.2 = ow_response.get σ
  swap
  · simp only [if_neg h_resp_pres]; exact bot_le
  simp only [if_pos h_resp_pres]
  -- (pure decide).wp F_bool yσ.2 ≤ if resp = chal_x ∧ ¬cxq at σ then 1 else 0.
  rw [wp_pure]
  simp only []  -- beta-reduce
  -- F_bool (decide ..., yσ.2) = if resp = chal_x ∧ ¬cxq at yσ.2 then 1 else 0.
  -- By preservation: = if resp = chal_x ∧ ¬cxq at σ then 1 else 0.
  rw [h_resp_pres, h_cx_pres, h_cxq_pres]

include h_ow_adv_chal_x_queried in
/-- **Layer C_obs**: the probability that `chal_x_queried` is set during the
    tracked experiment is at most `q/|input|`.

    Reduction: use lazy-query freshness invariance to drop the pre-loop's
    `lazy_query x` (which only affects RO[x] = chal_y), then apply the
    strengthened sum lemma. -/
lemma ow_experiment_tracked_chal_x_queried_bound
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (q : ℕ) (σ₀ : state) :
    (ow_experiment_tracked ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state =>
          if chal_x_queried.get bσ.2 then (1 : ENNReal) else 0) σ₀
    ≤ (q : ENNReal) / Fintype.card input := by
  set F : Unit × state → ENNReal :=
    fun aσ : Unit × state => if chal_x_queried.get aσ.2 then (1 : ENNReal) else 0 with hF_def
  -- σ_a = state after init + set cxq false. cxq = false, RO = all none.
  set σ_a : state := chal_x_queried.set false (random_oracle_state.set (fun _ => none) σ₀)
    with σ_a_def
  have h_σ_a_cxq : chal_x_queried.get σ_a = false := by
    rw [σ_a_def, chal_x_queried.set_get]
  have h_σ_a_ro : ∀ k : input, random_oracle_state.get σ_a k = none := by
    intro k
    rw [σ_a_def, random_oracle_state.get_of_disjoint_set, random_oracle_state.set_get]
  -- Helper: post_loop step bound for any y.
  have h_post_drop : ∀ (y : output) (σ' : state),
      (Program.set ow_challenge_y y >>= fun _ =>
          ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
          Program.get ow_response >>= fun resp =>
          lazy_query resp >>= fun y_check =>
          (pure (decide (y_check = y)) : Program state Bool)).wp
        (fun bσ : Bool × state =>
          if chal_x_queried.get bσ.2 then (1 : ENNReal) else 0) σ'
      ≤ (Program.set ow_challenge_y y >>= fun _ =>
          ow_loop_tracked ow_adv q lazy_query).wp F σ' := by
    intro y σ'
    conv_lhs =>
      rw [wp_bind, wp_set, wp_bind]
    conv_rhs =>
      rw [wp_bind, wp_set]
    refine Program.wp_le_wp_of_le _ _ _ ?_ _
    intro aσ_l
    exact post_loop_preserves_chal_x_queried_wp y aσ_l.2
  -- Per-x bound.
  have h_per_x : ∀ x : input,
      (Program.set ow_challenge_x x >>= fun _ =>
        lazy_query x >>= fun y => Program.set ow_challenge_y y >>= fun _ =>
        ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
        Program.get ow_response >>= fun resp =>
        lazy_query resp >>= fun y_check =>
        (pure (decide (y_check = y)) : Program state Bool)).wp
          (fun bσ : Bool × state =>
            if chal_x_queried.get bσ.2 then (1 : ENNReal) else 0) σ_a
      ≤ (ow_loop_tracked ow_adv q lazy_query).wp F (ow_challenge_x.set x σ_a) := by
    intro x
    rw [wp_bind, wp_set]
    -- Apply wp_bind on lazy_query x.
    rw [wp_bind]
    -- Apply wp_le_wp_of_le on lazy_query post via h_post_drop.
    refine le_trans (Program.wp_le_wp_of_le _ _
      (fun yσ_l : output × state =>
        (Program.set ow_challenge_y yσ_l.1 >>= fun _ =>
            ow_loop_tracked ow_adv q lazy_query).wp F yσ_l.2)
      (fun yσ_l => h_post_drop yσ_l.1 yσ_l.2) _) ?_
    -- Refold inner via ← wp_bind.
    rw [show (lazy_query x).wp
        (fun yσ_l : output × state =>
          (Program.set ow_challenge_y yσ_l.1 >>= fun _ =>
              ow_loop_tracked ow_adv q lazy_query).wp F yσ_l.2)
        (ow_challenge_x.set x σ_a)
        = (lazy_query x >>= fun y => Program.set ow_challenge_y y >>= fun _ =>
            ow_loop_tracked ow_adv q lazy_query).wp F (ow_challenge_x.set x σ_a)
        from by rw [wp_bind]]
    -- Apply freshness.
    rw [ow_loop_tracked_lazy_query_freshness ow_adv h_ow_adv h_ow_adv_chal_y
        h_ow_adv_chal_x h_ow_adv_chal_x_queried q x σ_a h_σ_a_cxq (h_σ_a_ro x)]
  -- Unfold experiment via wp_bind.
  show (lazy_init >>= fun _ => Program.set chal_x_queried false >>= fun _ =>
        Program.uniform >>= fun x => Program.set ow_challenge_x x >>= fun _ =>
        lazy_query x >>= fun y => Program.set ow_challenge_y y >>= fun _ =>
        ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
        Program.get ow_response >>= fun resp =>
        lazy_query resp >>= fun y_check =>
        (pure (decide (y_check = y)) : Program state Bool)).wp _ σ₀ ≤ _
  rw [wp_bind]
  unfold lazy_init
  rw [wp_set, wp_bind, wp_set]
  simp only []  -- beta-reduce
  -- Now: (do uniform; continuation).wp F_bool σ_a ≤ q / |input|.
  rw [wp_bind, wp_uniform]
  -- Goal: ∑ x, (continuation x).wp F_bool σ_a / |input| ≤ q / |input|.
  refine le_trans (Finset.sum_le_sum (fun x _ =>
    show (Program.set ow_challenge_x x >>= fun _ =>
            lazy_query x >>= fun y => Program.set ow_challenge_y y >>= fun _ =>
            ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
            Program.get ow_response >>= fun resp =>
            lazy_query resp >>= fun y_check =>
            (pure (decide (y_check = y)) : Program state Bool)).wp
            (fun bσ : Bool × state =>
              if chal_x_queried.get bσ.2 then (1 : ENNReal) else 0) σ_a
          / Fintype.card input
        ≤ (ow_loop_tracked ow_adv q lazy_query).wp F (ow_challenge_x.set x σ_a)
          / Fintype.card input
        from ENNReal.div_le_div_right (h_per_x x) _)) ?_
  rw [show ∑ i : input, (ow_loop_tracked ow_adv q lazy_query).wp F (ow_challenge_x.set i σ_a)
            / Fintype.card input
        = (∑ i : input, (ow_loop_tracked ow_adv q lazy_query).wp F
            (ow_challenge_x.set i σ_a)) / Fintype.card input from by
    simp only [ENNReal.div_eq_inv_mul, ← Finset.mul_sum]]
  exact ENNReal.div_le_div_right
    (ow_loop_tracked_chal_x_queried_sum_le ow_adv h_ow_adv_chal_x_queried h_ow_adv
      h_ow_adv_chal_y h_ow_adv_chal_x q σ_a h_σ_a_cxq) _

include h_ow_adv_chal_x_queried in
/-- **Strengthened sum bound** for conditional independence:
    `∑ x, loop_q.wp [resp=x ∧ ¬cxq] (chal_x.set x σ) ≤ [¬cxq.get σ]`.

    Stronger than `≤ 1`: yields 0 when σ.cxq=true. The strengthened IH at
    cxq=true forces each term to be 0 by positivity. -/
private lemma ow_loop_tracked_indep_sum_le_strong
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range) :
    ∀ (q : ℕ) (σ : state),
    ∑ x : input, (ow_loop_tracked ow_adv q lazy_query).wp
        (fun aσ : Unit × state =>
          if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
          then (1 : ENNReal) else 0)
        (ow_challenge_x.set x σ)
    ≤ (if chal_x_queried.get σ then (0 : ENNReal) else 1) := by
  intro q
  induction q with
  | zero =>
    intro σ
    show ∑ x : input, (Pure.pure () : Program state Unit).wp _ (ow_challenge_x.set x σ) ≤ _
    simp_rw [wp_pure]
    have h_resp : ∀ x : input,
        ow_response.get (ow_challenge_x.set x σ) = ow_response.get σ := by
      intro x; rw [ow_response.get_of_disjoint_set]
    have h_cxq : ∀ x : input,
        chal_x_queried.get (ow_challenge_x.set x σ) = chal_x_queried.get σ := by
      intro x; rw [chal_x_queried.get_of_disjoint_set]
    simp_rw [h_resp, h_cxq]
    by_cases h : chal_x_queried.get σ = true
    · have h_zero : ∀ x : input,
          (if ow_response.get σ = x ∧ ¬ chal_x_queried.get σ then (1 : ENNReal) else 0) = 0 := by
        intro x
        rw [if_neg]
        rintro ⟨_, h_neg⟩
        exact h_neg h
      simp_rw [h_zero, Finset.sum_const_zero]
      rw [if_pos h]
    · have h_simplify : ∀ x : input,
          (if ow_response.get σ = x ∧ ¬ chal_x_queried.get σ then (1 : ENNReal) else 0)
          = if ow_response.get σ = x then (1 : ENNReal) else 0 := by
        intro x
        by_cases h_resp_x : ow_response.get σ = x
        · rw [if_pos h_resp_x, if_pos]
          exact ⟨h_resp_x, h⟩
        · rw [if_neg h_resp_x, if_neg]
          exact fun ⟨h1, _⟩ => h_resp_x h1
      simp_rw [h_simplify]
      rw [if_neg h]
      rw [Finset.sum_ite_eq Finset.univ (ow_response.get σ) (fun _ => (1 : ENNReal))]
      simp
  | succ q ih =>
    intro σ
    -- Step 1: Reduce loop_(q+1) via wp_bind (per-x).
    have h_step1 : ∀ x : input,
        (ow_loop_tracked ow_adv (q+1) lazy_query).wp
            (fun aσ : Unit × state =>
              if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
              then (1 : ENNReal) else 0)
            (ow_challenge_x.set x σ)
        = (ow_loop_body_tracked ow_adv lazy_query).wp
            (fun aσ_b : Unit × state =>
              (ow_loop_tracked ow_adv q lazy_query).wp
                (fun aσ : Unit × state =>
                  if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
                  then (1 : ENNReal) else 0)
                aσ_b.2)
            (ow_challenge_x.set x σ) := by
      intro x
      show (ow_loop_body_tracked ow_adv lazy_query >>= fun _ : Unit =>
              ow_loop_tracked ow_adv q lazy_query).wp _ (ow_challenge_x.set x σ) = _
      rw [wp_bind]
    simp_rw [h_step1]
    -- Step 2: body = adv >>= post_adv. Apply wp_bind.
    have h_step2 : ∀ x : input,
        (ow_loop_body_tracked ow_adv lazy_query).wp
            (fun aσ_b : Unit × state =>
              (ow_loop_tracked ow_adv q lazy_query).wp
                (fun aσ : Unit × state =>
                  if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
                  then (1 : ENNReal) else 0)
                aσ_b.2)
            (ow_challenge_x.set x σ)
        = ow_adv.wp (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp
              (fun aσ_b : Unit × state =>
                (ow_loop_tracked ow_adv q lazy_query).wp
                  (fun aσ : Unit × state =>
                    if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
                    then (1 : ENNReal) else 0)
                  aσ_b.2) aσ_adv.2)
            (ow_challenge_x.set x σ) := by
      intro x
      show (ow_adv >>= fun _ : Unit =>
              Program.get oracle_input >>= fun inp =>
                Program.get ow_challenge_x >>= fun cx =>
                  (if inp = cx then Program.set chal_x_queried true
                   else (pure () : Program state Unit)) >>= fun _ =>
                    lazy_query inp >>= fun y =>
                      Program.set oracle_output y).wp _ (ow_challenge_x.set x σ) = _
      rw [wp_bind]
    simp_rw [h_step2]
    -- Step 3: Apply wp_shift_input on adv to move chal_x.set x past adv.
    have h_shift_chal_x : ow_challenge_x.set ∈ Set.univ ∧
        ∀ x : input, ow_challenge_x.update (Function.const _ x) ∈
            ((ow_challenge_x.compl.range : TotLensRange state)ᶜ).updates := by
      refine ⟨Set.mem_univ _, ?_⟩
      intro x
      rw [show ((ow_challenge_x.compl.range : TotLensRange state)ᶜ) = ow_challenge_x.range from by
        rw [TotLensRange.complement_range, TotLensRange.compl_compl]]
      exact ⟨Function.const _ x, Set.mem_univ _, rfl⟩
    have h_set_as_update : ∀ x : input, ow_challenge_x.set x σ
        = (ow_challenge_x.update (Function.const _ x)) σ := by
      intro x
      show ow_challenge_x.set x σ
        = ow_challenge_x.set ((Function.const _ x) (ow_challenge_x.get σ)) σ
      rw [Function.const_apply]
    have h_shift : ∀ x : input,
        ow_adv.wp (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp
              (fun aσ_b : Unit × state =>
                (ow_loop_tracked ow_adv q lazy_query).wp
                  (fun aσ : Unit × state =>
                    if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
                    then (1 : ENNReal) else 0)
                  aσ_b.2) aσ_adv.2)
            (ow_challenge_x.set x σ)
        = ow_adv.wp (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp
              (fun aσ_b : Unit × state =>
                (ow_loop_tracked ow_adv q lazy_query).wp
                  (fun aσ : Unit × state =>
                    if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
                    then (1 : ENNReal) else 0)
                  aσ_b.2) (ow_challenge_x.set x aσ_adv.2))
            σ := by
      intro x
      rw [h_set_as_update x]
      exact Program.wp_shift_input h_ow_adv_chal_x (h_shift_chal_x.2 x) _ σ
    simp_rw [h_shift]
    -- Step 4: Pull sum inside ow_adv.wp.
    rw [← Program.wp_finset_sum]
    -- Step 5: wp_strengthen on adv with chal_x_queried.compl.range.
    rw [Program.wp_strengthen_lens_preserved chal_x_queried h_ow_adv_chal_x_queried _ σ]
    refine le_trans (Program.wp_le_wp_of_le ow_adv _
      (fun _ => if chal_x_queried.get σ then (0 : ENNReal) else 1) ?_ σ)
      (Program.wp_const_le ow_adv _ σ)
    intro aσ_adv
    by_cases h_cxq_adv : chal_x_queried.get aσ_adv.2 = chal_x_queried.get σ
    swap
    · simp only [if_neg h_cxq_adv]; exact bot_le
    simp only [if_pos h_cxq_adv]
    -- Set inp = oracle_input.get aσ_adv.2.
    set inp := oracle_input.get aσ_adv.2 with h_inp_def
    haveI _disj_cx_oi : disjoint ow_challenge_x oracle_input :=
      disjoint_oracle_input_ow_challenge_x.symm
    have h_inp_get : ∀ x : input,
        oracle_input.get (ow_challenge_x.set x aσ_adv.2) = inp := by
      intro x; rw [oracle_input.get_of_disjoint_set]
    have h_cx_get : ∀ x : input,
        ow_challenge_x.get (ow_challenge_x.set x aσ_adv.2) = x := fun x =>
      ow_challenge_x.set_get _ _
    -- (lazy_query inp; set oo) in chal_x.compl.range and chal_x_queried.compl.range.
    have h_lqso_inRange_cx_compl :
        (lazy_query inp >>= fun y => Program.set oracle_output y).inRange
            ow_challenge_x.compl.range :=
      lazy_query_then_set_oracle_output_inRange_ow_challenge_x_compl inp
    have h_lqso_inRange_cxq_compl :
        (lazy_query inp >>= fun y => Program.set oracle_output y).inRange
            chal_x_queried.compl.range :=
      lazy_query_then_set_oracle_output_inRange_chal_x_queried_compl inp
    -- Pointwise bound: per x, post_adv.wp G_x ≤ (lazy_query inp; set oo).wp G_x.
    have h_pointwise : ∀ x : input,
        (Program.get oracle_input >>= fun inp' =>
          Program.get ow_challenge_x >>= fun cx =>
            (if inp' = cx then Program.set chal_x_queried true
             else (pure () : Program state Unit)) >>= fun _ =>
              lazy_query inp' >>= fun y =>
                Program.set oracle_output y).wp
          (fun aσ_b : Unit × state =>
            (ow_loop_tracked ow_adv q lazy_query).wp
              (fun aσ : Unit × state =>
                if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
                then (1 : ENNReal) else 0)
              aσ_b.2) (ow_challenge_x.set x aσ_adv.2)
        ≤ (lazy_query inp >>= fun y => Program.set oracle_output y).wp
          (fun aσ_b : Unit × state =>
            (ow_loop_tracked ow_adv q lazy_query).wp
              (fun aσ : Unit × state =>
                if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
                then (1 : ENNReal) else 0)
              aσ_b.2) (ow_challenge_x.set x aσ_adv.2) := by
      intro x
      simp only [wp_bind, wp_get]
      rw [h_inp_get x, h_cx_get x]
      by_cases h : inp = x
      · -- Hit: inp = x. set cxq true.
        simp only [if_pos h]
        rw [wp_set]
        simp only []  -- beta-reduce the `(fun st => ...) σ` form
        rw [← wp_bind]
        -- LHS = (lazy_query inp; set oo).wp G_x at (cxq.set true (chal_x.set x aσ_adv.2)).
        -- Show LHS ≤ 0 ≤ RHS via strengthened IH at the lazy_query/set oo output.
        refine le_trans ?_ (bot_le)
        -- Apply wp_strengthen for chal_x AND chal_x_queried.
        rw [Program.wp_strengthen_lens_preserved chal_x_queried h_lqso_inRange_cxq_compl _
              (chal_x_queried.set true (ow_challenge_x.set x aσ_adv.2))]
        rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_lqso_inRange_cx_compl _
              (chal_x_queried.set true (ow_challenge_x.set x aσ_adv.2))]
        refine le_trans (Program.wp_le_wp_of_le _ _ (fun _ => (0 : ENNReal)) ?_ _)
                        (Program.wp_const_le _ _ _)
        intro aσ_lqo
        by_cases h_cx_pres : ow_challenge_x.get aσ_lqo.2 = ow_challenge_x.get
            (chal_x_queried.set true (ow_challenge_x.set x aσ_adv.2))
        swap
        · simp only [if_neg h_cx_pres]; rfl
        simp only [if_pos h_cx_pres]
        by_cases h_cxq_pres : chal_x_queried.get aσ_lqo.2 = chal_x_queried.get
            (chal_x_queried.set true (ow_challenge_x.set x aσ_adv.2))
        swap
        · simp only [if_neg h_cxq_pres]; rfl
        simp only [if_pos h_cxq_pres]
        -- Now aσ_lqo has chal_x = x AND cxq = true.
        have h_aσ_lqo_chal_x : ow_challenge_x.get aσ_lqo.2 = x := by
          rw [h_cx_pres]
          rw [ow_challenge_x.get_of_disjoint_set]
          exact ow_challenge_x.set_get _ _
        have h_aσ_lqo_cxq : chal_x_queried.get aσ_lqo.2 = true := by
          rw [h_cxq_pres, chal_x_queried.set_get]
        -- Apply strengthened IH at aσ_lqo.2 with cxq=true.
        have h_ih_at_lqo := ih aσ_lqo.2
        rw [if_pos h_aσ_lqo_cxq] at h_ih_at_lqo
        -- h_ih_at_lqo: ∑ x', loop_q.wp F'_x' (chal_x.set x' aσ_lqo.2) ≤ 0.
        -- For x' = x = chal_x.get aσ_lqo.2: chal_x.set x aσ_lqo.2 = aσ_lqo.2.
        have h_set_eq : ow_challenge_x.set x aσ_lqo.2 = aσ_lqo.2 := by
          rw [← h_aσ_lqo_chal_x]; exact ow_challenge_x.get_set aσ_lqo.2
        have h_term_le_sum :
            (ow_loop_tracked ow_adv q lazy_query).wp
              (fun aσ : Unit × state =>
                if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)
              (ow_challenge_x.set x aσ_lqo.2)
            ≤ ∑ x' : input, (ow_loop_tracked ow_adv q lazy_query).wp
                (fun aσ : Unit × state =>
                  if ow_response.get aσ.2 = x' ∧ ¬ chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)
                (ow_challenge_x.set x' aσ_lqo.2) :=
          Finset.single_le_sum (f := fun x' => (ow_loop_tracked ow_adv q lazy_query).wp
              (fun aσ : Unit × state =>
                if ow_response.get aσ.2 = x' ∧ ¬ chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)
              (ow_challenge_x.set x' aσ_lqo.2)) (fun _ _ => bot_le) (Finset.mem_univ x)
        rw [h_set_eq] at h_term_le_sum
        exact le_trans h_term_le_sum h_ih_at_lqo
      · -- Miss: inp ≠ x. pure ().
        simp only [if_neg h]
        rw [wp_pure]
    -- After pointwise: ∑ x, post_adv.wp G_x ≤ ∑ x, (lazy_query inp; set oo).wp G_x ≤ [¬cxq.get σ].
    refine le_trans (Finset.sum_le_sum (fun x _ => h_pointwise x)) ?_
    -- Apply wp_shift_input on (lazy_query inp; set oo) for chal_x.
    have h_shift_lqso : ∀ x : input,
        (lazy_query inp >>= fun y => Program.set oracle_output y).wp
          (fun aσ_b : Unit × state =>
            (ow_loop_tracked ow_adv q lazy_query).wp
              (fun aσ : Unit × state =>
                if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
                then (1 : ENNReal) else 0)
              aσ_b.2) (ow_challenge_x.set x aσ_adv.2)
        = (lazy_query inp >>= fun y => Program.set oracle_output y).wp
          (fun aσ_lqo : Unit × state =>
            (ow_loop_tracked ow_adv q lazy_query).wp
              (fun aσ : Unit × state =>
                if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
                then (1 : ENNReal) else 0)
              (ow_challenge_x.set x aσ_lqo.2))
          aσ_adv.2 := by
      intro x
      rw [show ow_challenge_x.set x aσ_adv.2
          = (ow_challenge_x.update (Function.const _ x)) aσ_adv.2 by
        show ow_challenge_x.set x aσ_adv.2
          = ow_challenge_x.set ((Function.const _ x) (ow_challenge_x.get aσ_adv.2)) aσ_adv.2
        rw [Function.const_apply]]
      exact Program.wp_shift_input h_lqso_inRange_cx_compl (h_shift_chal_x.2 x) _ _
    simp_rw [h_shift_lqso]
    -- Apply wp_finset_sum.
    rw [← Program.wp_finset_sum]
    -- Apply wp_strengthen on (lazy_query inp; set oo) for chal_x_queried.
    rw [Program.wp_strengthen_lens_preserved chal_x_queried h_lqso_inRange_cxq_compl _ aσ_adv.2]
    refine le_trans
      (Program.wp_le_wp_of_le _ _ (fun _ => if chal_x_queried.get σ then (0 : ENNReal) else 1) ?_ aσ_adv.2)
      (Program.wp_const_le _ _ _)
    intro aσ_lqo
    by_cases h_cxq_lqo : chal_x_queried.get aσ_lqo.2 = chal_x_queried.get aσ_adv.2
    swap
    · simp only [if_neg h_cxq_lqo]; exact bot_le
    simp only [if_pos h_cxq_lqo]
    have h_aσ_lqo_cxq : chal_x_queried.get aσ_lqo.2 = chal_x_queried.get σ :=
      h_cxq_lqo.trans h_cxq_adv
    -- ∑ x, loop_q.wp F_x (chal_x.set x aσ_lqo.2) ≤ [¬cxq.get aσ_lqo.2] = [¬cxq.get σ].
    have h_ih_at_lqo := ih aσ_lqo.2
    rw [h_aσ_lqo_cxq] at h_ih_at_lqo
    exact h_ih_at_lqo

include h_ow_adv_chal_x_queried in
/-- **F'_x averaged RO invariance**: pre-setting `RO[chal_x.get σ] = y` (uniform y)
    is equivalent (averaged over y) to no pre-set entry, when the post is
    `[resp = chal_x.get σ ∧ ¬cxq]`.

    Mirrors `ow_loop_tracked_chal_x_queried_RO_invariance_avg` but with a
    different post. HIT case is simpler: cxq=true at end ⟹ post=0 on both
    sides via strengthened sum lemma. -/
private lemma ow_loop_tracked_indep_RO_invariance_avg
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried' : ow_adv.inRange chal_x_queried.compl.range) :
    ∀ (q : ℕ) (σ : state),
    chal_x_queried.get σ = false →
    random_oracle_state.get σ (ow_challenge_x.get σ) = none →
    (1 : ENNReal) / Fintype.card output *
      ∑ y : output, (ow_loop_tracked ow_adv q lazy_query).wp
        (fun aσ : Unit × state =>
          if ow_response.get aσ.2 = ow_challenge_x.get σ ∧ ¬ chal_x_queried.get aσ.2
          then (1 : ENNReal) else 0)
        (random_oracle_state.set
          (fun k => if k = ow_challenge_x.get σ then some y
                    else random_oracle_state.get σ k) σ)
    = (ow_loop_tracked ow_adv q lazy_query).wp
        (fun aσ : Unit × state =>
          if ow_response.get aσ.2 = ow_challenge_x.get σ ∧ ¬ chal_x_queried.get aσ.2
          then (1 : ENNReal) else 0) σ := by
  intro q
  induction q with
  | zero =>
    intro σ h_qf h_ro
    show (1 : ENNReal) / Fintype.card output *
        ∑ y : output, (Pure.pure () : Program state Unit).wp _ _
      = (Pure.pure () : Program state Unit).wp _ _
    simp_rw [wp_pure]
    -- RO_setentry preserves resp.get and cxq.get (RO ⟂ resp, RO ⟂ cxq).
    have h_resp_unchanged : ∀ y : output,
        ow_response.get (random_oracle_state.set
          (fun k => if k = ow_challenge_x.get σ then some y
                    else random_oracle_state.get σ k) σ)
        = ow_response.get σ := by
      intro y
      rw [ow_response.get_of_disjoint_set]
    have h_cxq_unchanged : ∀ y : output,
        chal_x_queried.get (random_oracle_state.set
          (fun k => if k = ow_challenge_x.get σ then some y
                    else random_oracle_state.get σ k) σ)
        = chal_x_queried.get σ := by
      intro y
      rw [chal_x_queried.get_of_disjoint_set]
    simp_rw [h_resp_unchanged, h_cxq_unchanged]
    -- ∑ over y of a constant.
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    -- Goal: (1/|output|) * (|output| * indicator) = indicator
    rw [← mul_assoc, mul_comm (1 / _) _, mul_one_div,
        ENNReal.div_self
          (by exact_mod_cast Fintype.card_pos.ne')
          (by simp [ENNReal.natCast_ne_top]), one_mul]
  | succ q ih =>
    intro σ h_qf h_ro
    set x := ow_challenge_x.get σ with x_def
    set F : Unit × state → ENNReal :=
      fun aσ : Unit × state =>
        if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
        then (1 : ENNReal) else 0 with hF_def
    set G : Unit × state → ENNReal :=
      fun aσ_b : Unit × state => (ow_loop_tracked ow_adv q lazy_query).wp F aσ_b.2 with hG_def
    -- Reduce loop_{q+1} = body >>= loop_q on both sides.
    have h_unfold : ∀ σ' : state,
        (ow_loop_tracked ow_adv (q+1) lazy_query).wp F σ'
        = (ow_loop_body_tracked ow_adv lazy_query).wp G σ' := by
      intro σ'
      show (ow_loop_body_tracked ow_adv lazy_query >>= fun _ : Unit =>
              ow_loop_tracked ow_adv q lazy_query).wp F σ' = _
      rw [wp_bind]
    simp_rw [h_unfold]
    -- body = adv >>= post_adv. Apply wp_bind.
    have h_body_unfold : ∀ σ' : state,
        (ow_loop_body_tracked ow_adv lazy_query).wp G σ'
        = ow_adv.wp (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp G aσ_adv.2) σ' := by
      intro σ'
      show (ow_adv >>= fun _ : Unit =>
              Program.get oracle_input >>= fun inp =>
                Program.get ow_challenge_x >>= fun cx =>
                  (if inp = cx then Program.set chal_x_queried true
                   else (pure () : Program state Unit)) >>= fun _ =>
                    lazy_query inp >>= fun y =>
                      Program.set oracle_output y).wp G σ' = _
      rw [wp_bind]
    simp_rw [h_body_unfold]
    -- Apply wp_shift_input on adv with shift = RO_setentry x y.
    have h_shift : ∀ y' : output,
        ow_adv.wp (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp G aσ_adv.2)
            (random_oracle_state.set
              (fun k => if k = x then some y'
                        else random_oracle_state.get σ k) σ)
        = ow_adv.wp (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp G
              (random_oracle_state.set
                (fun k => if k = x then some y'
                          else random_oracle_state.get aσ_adv.2 k) aσ_adv.2)) σ := by
      intro y'
      have h_shift_in : (fun σ' => random_oracle_state.set
          (fun k => if k = x then some y' else random_oracle_state.get σ' k) σ')
          ∈ ((random_oracle_state.compl.range : TotLensRange state)ᶜ).updates := by
        rw [show ((random_oracle_state.compl.range : TotLensRange state)ᶜ)
            = random_oracle_state.range from by
          rw [TotLensRange.complement_range, TotLensRange.compl_compl]]
        exact ⟨fun h => fun k => if k = x then some y' else h k, Set.mem_univ _, rfl⟩
      exact Program.wp_shift_input h_ow_adv h_shift_in _ σ
    simp_rw [h_shift]
    -- Pull sum and 1/|output| inside ow_adv.wp.
    rw [← Program.wp_finset_sum, ← Program.wp_const_mul]
    -- Apply wp_strengthen_lens_preserved 3x: RO, ow_challenge_x, chal_x_queried.
    rw [Program.wp_strengthen_lens_preserved random_oracle_state h_ow_adv _ σ,
        Program.wp_strengthen_lens_preserved random_oracle_state h_ow_adv
          (fun aσ_adv : Unit × state =>
            (Program.get oracle_input >>= fun inp =>
                Program.get ow_challenge_x >>= fun cx =>
                  (if inp = cx then Program.set chal_x_queried true
                   else (pure () : Program state Unit)) >>= fun _ =>
                    lazy_query inp >>= fun y_lq =>
                      Program.set oracle_output y_lq).wp G aσ_adv.2) σ]
    rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_ow_adv_chal_x _ σ,
        Program.wp_strengthen_lens_preserved ow_challenge_x h_ow_adv_chal_x
          (fun aσ_adv : Unit × state =>
            if random_oracle_state.get aσ_adv.2 = random_oracle_state.get σ then
              (Program.get oracle_input >>= fun inp =>
                  Program.get ow_challenge_x >>= fun cx =>
                    (if inp = cx then Program.set chal_x_queried true
                     else (pure () : Program state Unit)) >>= fun _ =>
                      lazy_query inp >>= fun y_lq =>
                        Program.set oracle_output y_lq).wp G aσ_adv.2
            else 0) σ]
    rw [Program.wp_strengthen_lens_preserved chal_x_queried h_ow_adv_chal_x_queried' _ σ,
        Program.wp_strengthen_lens_preserved chal_x_queried h_ow_adv_chal_x_queried'
          (fun aσ_adv : Unit × state =>
            if ow_challenge_x.get aσ_adv.2 = ow_challenge_x.get σ then
              if random_oracle_state.get aσ_adv.2 = random_oracle_state.get σ then
                (Program.get oracle_input >>= fun inp =>
                    Program.get ow_challenge_x >>= fun cx =>
                      (if inp = cx then Program.set chal_x_queried true
                       else (pure () : Program state Unit)) >>= fun _ =>
                        lazy_query inp >>= fun y_lq =>
                          Program.set oracle_output y_lq).wp G aσ_adv.2
              else 0
            else 0) σ]
    apply congrArg (fun P => ow_adv.wp P σ)
    funext aσ_adv
    by_cases h_cxq_pres : chal_x_queried.get aσ_adv.2 = chal_x_queried.get σ
    swap
    · simp only [if_neg h_cxq_pres]
    simp only [if_pos h_cxq_pres]
    by_cases h_cx_pres : ow_challenge_x.get aσ_adv.2 = ow_challenge_x.get σ
    swap
    · simp only [if_neg h_cx_pres]
    simp only [if_pos h_cx_pres]
    by_cases h_ro_pres : random_oracle_state.get aσ_adv.2 = random_oracle_state.get σ
    swap
    · simp only [if_neg h_ro_pres]
    simp only [if_pos h_ro_pres]
    have h_aσ_adv_chal_x : ow_challenge_x.get aσ_adv.2 = x := h_cx_pres
    have h_aσ_adv_ro_x : random_oracle_state.get aσ_adv.2 x = none := by
      rw [h_ro_pres]; exact h_ro
    have h_aσ_adv_cxq : chal_x_queried.get aσ_adv.2 = false := by
      rw [h_cxq_pres]; exact h_qf
    -- Goal: (1/|output|) ∑ y, post_adv.wp G (RO_setentry x y aσ_adv.2) = post_adv.wp G aσ_adv.2.
    -- Step 1: unfold post_adv via wp_bind + wp_get.
    simp only [wp_bind, wp_get]
    haveI _disj_ro_oi : disjoint random_oracle_state oracle_input :=
      disjoint_oracle_input_ro.symm
    have h_oi_RO : ∀ y_arg : output,
        oracle_input.get (random_oracle_state.set
          (fun k => if k = x then some y_arg
                    else random_oracle_state.get aσ_adv.2 k) aσ_adv.2)
        = oracle_input.get aσ_adv.2 := by
      intro _; rw [oracle_input.get_of_disjoint_set]
    have h_cx_RO : ∀ y_arg : output,
        ow_challenge_x.get (random_oracle_state.set
          (fun k => if k = x then some y_arg
                    else random_oracle_state.get aσ_adv.2 k) aσ_adv.2)
        = ow_challenge_x.get aσ_adv.2 := by
      intro _; rw [ow_challenge_x.get_of_disjoint_set]
    simp_rw [h_oi_RO, h_cx_RO, h_aσ_adv_chal_x]
    set inp_a := oracle_input.get aσ_adv.2 with inp_a_def
    by_cases h_inp : inp_a = x
    · -- HIT case (inp_a = x): both LHS and RHS = 0 via strengthened sum lemma at cxq=true.
      simp only [if_pos h_inp]
      rw [h_inp]
      simp only [wp_bind, wp_set]
      -- LHS state at chal_x_queried.set true (RO_setentry x y aσ_adv.2)
      --      = RO_setentry x y (chal_x_queried.set true aσ_adv.2) (by disjoint commute).
      haveI _disj_cxq_ro : disjoint chal_x_queried random_oracle_state :=
        disjoint_chal_x_queried_ro
      have h_commute_LHS : ∀ y_arg : output,
          chal_x_queried.set true
            (random_oracle_state.set
              (fun k => if k = x then some y_arg
                        else random_oracle_state.get aσ_adv.2 k) aσ_adv.2)
          = random_oracle_state.set
              (fun k => if k = x then some y_arg
                        else random_oracle_state.get (chal_x_queried.set true aσ_adv.2) k)
              (chal_x_queried.set true aσ_adv.2) := by
        intro y_arg
        rw [_disj_cxq_ro.commute]
        congr 1
        funext k
        rw [random_oracle_state.get_of_disjoint_set chal_x_queried true aσ_adv.2]
      simp_rw [h_commute_LHS]
      -- Helper: (lazy_query x; set oo).wp G at cxq=true, chal_x=x state = 0.
      -- Uses strengthened sum lemma.
      have h_lqso_inRange_cx_compl :
          (lazy_query x >>= fun y => Program.set oracle_output y).inRange
              ow_challenge_x.compl.range :=
        lazy_query_then_set_oracle_output_inRange_ow_challenge_x_compl x
      have h_lqso_inRange_cxq_compl :
          (lazy_query x >>= fun y => Program.set oracle_output y).inRange
              chal_x_queried.compl.range :=
        lazy_query_then_set_oracle_output_inRange_chal_x_queried_compl x
      -- Bridge: (lazy_query x; set oo).wp G σ = (lazy_query x).wp (fun aσ => G ((), oo.set ...)) σ.
      have h_bridge : ∀ σ_in : state,
          (lazy_query x >>= fun y_lq => Program.set oracle_output y_lq).wp G σ_in
          = (lazy_query x).wp
            (fun x_1 : output × state => G ((), oracle_output.set x_1.1 x_1.2)) σ_in := by
        intro σ_in
        rw [wp_bind]
        congr 1
        funext aσ_lq
        simp only [wp_set]
      have h_zero_at_cxq_true : ∀ σ_in : state,
          chal_x_queried.get σ_in = true →
          ow_challenge_x.get σ_in = x →
          (lazy_query x >>= fun y_lq => Program.set oracle_output y_lq).wp G σ_in = 0 := by
        intro σ_in h_cxq_in h_cx_in
        rw [Program.wp_strengthen_lens_preserved chal_x_queried h_lqso_inRange_cxq_compl _ σ_in]
        rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_lqso_inRange_cx_compl _ σ_in]
        refine le_antisymm ?_ (bot_le)
        refine le_trans
          (Program.wp_le_wp_of_le _ _ (fun _ => (0 : ENNReal)) ?_ σ_in)
          (Program.wp_const_le _ _ _)
        intro aσ_lqo
        by_cases h_cx_lq : ow_challenge_x.get aσ_lqo.2 = ow_challenge_x.get σ_in
        swap
        · simp only [if_neg h_cx_lq]; rfl
        simp only [if_pos h_cx_lq]
        by_cases h_cxq_lq : chal_x_queried.get aσ_lqo.2 = chal_x_queried.get σ_in
        swap
        · simp only [if_neg h_cxq_lq]; rfl
        simp only [if_pos h_cxq_lq]
        have h_aσ_lqo_chal_x : ow_challenge_x.get aσ_lqo.2 = x := h_cx_lq.trans h_cx_in
        have h_aσ_lqo_cxq : chal_x_queried.get aσ_lqo.2 = true := h_cxq_lq.trans h_cxq_in
        -- Apply strengthened sum lemma at aσ_lqo.2 (cxq=true).
        have h_sum := ow_loop_tracked_indep_sum_le_strong ow_adv h_ow_adv_chal_x_queried'
          h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x q aσ_lqo.2
        rw [if_pos h_aσ_lqo_cxq] at h_sum
        -- For x' = x = chal_x.get aσ_lqo.2: chal_x.set x aσ_lqo.2 = aσ_lqo.2.
        have h_set_eq : ow_challenge_x.set x aσ_lqo.2 = aσ_lqo.2 := by
          rw [← h_aσ_lqo_chal_x]; exact ow_challenge_x.get_set aσ_lqo.2
        -- G aσ_lqo = loop_q.wp F aσ_lqo.2 ≤ ∑ x', loop_q.wp F'_x' (chal_x.set x' aσ_lqo.2) ≤ 0.
        show (ow_loop_tracked ow_adv q lazy_query).wp F aσ_lqo.2 ≤ 0
        have h_term_le_sum :
            (ow_loop_tracked ow_adv q lazy_query).wp F (ow_challenge_x.set x aσ_lqo.2)
            ≤ ∑ x' : input, (ow_loop_tracked ow_adv q lazy_query).wp
              (fun aσ : Unit × state =>
                if ow_response.get aσ.2 = x' ∧ ¬ chal_x_queried.get aσ.2
                then (1 : ENNReal) else 0)
              (ow_challenge_x.set x' aσ_lqo.2) :=
          Finset.single_le_sum (f := fun x' => (ow_loop_tracked ow_adv q lazy_query).wp
              (fun aσ : Unit × state =>
                if ow_response.get aσ.2 = x' ∧ ¬ chal_x_queried.get aσ.2
                then (1 : ENNReal) else 0)
              (ow_challenge_x.set x' aσ_lqo.2)) (fun _ _ => bot_le) (Finset.mem_univ x)
        rw [h_set_eq] at h_term_le_sum
        exact le_trans h_term_le_sum h_sum
      -- Apply h_zero_at_cxq_true on both sides.
      have h_LHS_zero : ∀ y_arg : output,
          (lazy_query x >>= fun y_lq => Program.set oracle_output y_lq).wp G
            (random_oracle_state.set
              (fun k => if k = x then some y_arg
                        else random_oracle_state.get (chal_x_queried.set true aσ_adv.2) k)
              (chal_x_queried.set true aσ_adv.2)) = 0 := by
        intro y_arg
        apply h_zero_at_cxq_true
        · rw [chal_x_queried.get_of_disjoint_set, chal_x_queried.set_get]
        · rw [ow_challenge_x.get_of_disjoint_set, ow_challenge_x.get_of_disjoint_set]
          exact h_aσ_adv_chal_x
      have h_RHS_zero : (lazy_query x >>= fun y_lq => Program.set oracle_output y_lq).wp G
          (chal_x_queried.set true aσ_adv.2) = 0 := by
        apply h_zero_at_cxq_true
        · rw [chal_x_queried.set_get]
        · rw [ow_challenge_x.get_of_disjoint_set]
          exact h_aσ_adv_chal_x
      simp_rw [← h_bridge]
      rw [Finset.sum_eq_zero (fun y _ => h_LHS_zero y), mul_zero, h_RHS_zero]
    · -- MISS case (inp_a ≠ x): RO_setentry_commute + IH.
      simp only [if_neg h_inp]
      simp only [wp_pure]
      simp_rw [← wp_bind]
      have h_commute : ∀ y_arg : output,
          (lazy_query inp_a >>= fun y_lq => Program.set oracle_output y_lq).wp G
            (random_oracle_state.set
              (fun k => if k = x then some y_arg
                        else random_oracle_state.get aσ_adv.2 k) aσ_adv.2)
          = (lazy_query inp_a >>= fun y_lq => Program.set oracle_output y_lq).wp
              (fun aσ_lq => G (aσ_lq.1, random_oracle_state.set
                                      (fun k => if k = x then some y_arg
                                               else random_oracle_state.get aσ_lq.2 k) aσ_lq.2))
              aσ_adv.2 :=
        fun y_arg => RO_setentry_neq_commutes_lazy_query_set_oracle_output
          inp_a x h_inp y_arg aσ_adv.2 G
      simp_rw [h_commute]
      rw [← Program.wp_finset_sum, ← Program.wp_const_mul]
      have h_inRange_cxq : (lazy_query inp_a >>= fun y_lq =>
          Program.set oracle_output y_lq).inRange chal_x_queried.compl.range :=
        lazy_query_then_set_oracle_output_inRange_chal_x_queried_compl inp_a
      have h_inRange_cx : (lazy_query inp_a >>= fun y_lq =>
          Program.set oracle_output y_lq).inRange ow_challenge_x.compl.range :=
        lazy_query_then_set_oracle_output_inRange_ow_challenge_x_compl inp_a
      conv_lhs =>
        rw [Program.wp_strengthen_lens_preserved chal_x_queried h_inRange_cxq _ aσ_adv.2,
            Program.wp_strengthen_lens_preserved ow_challenge_x h_inRange_cx _ aσ_adv.2,
            lazy_query_set_oracle_output_preserves_RO_at_other_key inp_a x h_inp aσ_adv.2 _]
      conv_rhs =>
        rw [Program.wp_strengthen_lens_preserved chal_x_queried h_inRange_cxq G aσ_adv.2,
            Program.wp_strengthen_lens_preserved ow_challenge_x h_inRange_cx _ aσ_adv.2,
            lazy_query_set_oracle_output_preserves_RO_at_other_key inp_a x h_inp aσ_adv.2 _]
      congr 1
      funext aσ_lq
      by_cases h_ro_lq : random_oracle_state.get aσ_lq.2 x
          = random_oracle_state.get aσ_adv.2 x
      swap
      · simp only [if_neg h_ro_lq]
      simp only [if_pos h_ro_lq]
      by_cases h_cx_lq : ow_challenge_x.get aσ_lq.2 = ow_challenge_x.get aσ_adv.2
      swap
      · simp only [if_neg h_cx_lq]
      simp only [if_pos h_cx_lq]
      by_cases h_cxq_lq : chal_x_queried.get aσ_lq.2 = chal_x_queried.get aσ_adv.2
      swap
      · simp only [if_neg h_cxq_lq]
      simp only [if_pos h_cxq_lq]
      have h_aσ_lq_cxq : chal_x_queried.get aσ_lq.2 = false :=
        h_cxq_lq.trans h_aσ_adv_cxq
      have h_aσ_lq_chal_x : ow_challenge_x.get aσ_lq.2 = x :=
        h_cx_lq.trans h_aσ_adv_chal_x
      have h_aσ_lq_ro_x : random_oracle_state.get aσ_lq.2 x = none :=
        h_ro_lq.trans h_aσ_adv_ro_x
      have h_aσ_lq_ro_chal_x : random_oracle_state.get aσ_lq.2
          (ow_challenge_x.get aσ_lq.2) = none := by
        rw [h_aσ_lq_chal_x]; exact h_aσ_lq_ro_x
      have h_ih := ih aσ_lq.2 h_aσ_lq_cxq h_aσ_lq_ro_chal_x
      rw [h_aσ_lq_chal_x] at h_ih
      exact h_ih

/-- The inner part of body (after adv and the two gets) doesn't read chal_x —
    cx is captured as a value. Hence it's in chal_x.compl.range. -/
private lemma body_inner_inRange_chal_x_compl (inp cx : input) :
    ((if inp = cx then Program.set chal_x_queried true
      else (pure () : Program state Unit)) >>= fun _ =>
        lazy_query inp >>= fun y =>
          Program.set oracle_output y).inRange ow_challenge_x.compl.range := by
  refine Program.inRange_bind ?_ ?_
  · by_cases h : inp = cx
    · rw [if_pos h]
      exact Program.set_inRange_compl_of_disjoint chal_x_queried ow_challenge_x _
    · rw [if_neg h]
      exact Program.inRange_pure _ _
  · intro _
    exact lazy_query_then_set_oracle_output_inRange_ow_challenge_x_compl inp

/-- `ow_loop_body_tracked` preserves chal_x value: at any body output state,
    chal_x.get equals input's chal_x.get. -/
private lemma ow_loop_body_tracked_preserves_chal_x_wp
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (F : Unit × state → ENNReal) (σ : state) :
    (ow_loop_body_tracked ow_adv lazy_query).wp F σ
    = (ow_loop_body_tracked ow_adv lazy_query).wp
        (fun aσ : Unit × state =>
          if ow_challenge_x.get aσ.2 = ow_challenge_x.get σ then F aσ else 0) σ := by
  have h_lhs : (ow_loop_body_tracked ow_adv lazy_query).wp F σ
      = ow_adv.wp (fun aσ_adv : Unit × state =>
          (Program.get oracle_input >>= fun inp =>
            Program.get ow_challenge_x >>= fun cx =>
              (if inp = cx then Program.set chal_x_queried true
               else (pure () : Program state Unit)) >>= fun _ =>
                lazy_query inp >>= fun y =>
                  Program.set oracle_output y).wp F aσ_adv.2) σ := by
    show (ow_adv >>= fun _ : Unit =>
            Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp F σ = _
    rw [wp_bind]
  have h_rhs : (ow_loop_body_tracked ow_adv lazy_query).wp
        (fun aσ : Unit × state =>
          if ow_challenge_x.get aσ.2 = ow_challenge_x.get σ then F aσ else 0) σ
      = ow_adv.wp (fun aσ_adv : Unit × state =>
          (Program.get oracle_input >>= fun inp =>
            Program.get ow_challenge_x >>= fun cx =>
              (if inp = cx then Program.set chal_x_queried true
               else (pure () : Program state Unit)) >>= fun _ =>
                lazy_query inp >>= fun y =>
                  Program.set oracle_output y).wp
            (fun aσ : Unit × state =>
              if ow_challenge_x.get aσ.2 = ow_challenge_x.get σ then F aσ else 0)
            aσ_adv.2) σ := by
    show (ow_adv >>= fun _ : Unit =>
            Program.get oracle_input >>= fun inp =>
              Program.get ow_challenge_x >>= fun cx =>
                (if inp = cx then Program.set chal_x_queried true
                 else (pure () : Program state Unit)) >>= fun _ =>
                  lazy_query inp >>= fun y =>
                    Program.set oracle_output y).wp _ σ = _
    rw [wp_bind]
  rw [h_lhs, h_rhs]
  rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_ow_adv_chal_x _ σ,
      Program.wp_strengthen_lens_preserved ow_challenge_x h_ow_adv_chal_x
        (fun aσ_adv : Unit × state =>
          (Program.get oracle_input >>= fun inp =>
            Program.get ow_challenge_x >>= fun cx =>
              (if inp = cx then Program.set chal_x_queried true
               else (pure () : Program state Unit)) >>= fun _ =>
                lazy_query inp >>= fun y =>
                  Program.set oracle_output y).wp
            (fun aσ : Unit × state =>
              if ow_challenge_x.get aσ.2 = ow_challenge_x.get σ then F aσ else 0)
            aσ_adv.2) σ]
  congr 1
  funext aσ_adv
  by_cases h_cx_pres : ow_challenge_x.get aσ_adv.2 = ow_challenge_x.get σ
  swap
  · simp only [if_neg h_cx_pres]
  simp only [if_pos h_cx_pres]
  show (Program.get oracle_input >>= fun inp =>
            Program.get ow_challenge_x >>= fun cx =>
              (if inp = cx then Program.set chal_x_queried true
               else (pure () : Program state Unit)) >>= fun _ =>
                lazy_query inp >>= fun y =>
                  Program.set oracle_output y).wp F aσ_adv.2
      = (Program.get oracle_input >>= fun inp =>
            Program.get ow_challenge_x >>= fun cx =>
              (if inp = cx then Program.set chal_x_queried true
               else (pure () : Program state Unit)) >>= fun _ =>
                lazy_query inp >>= fun y =>
                  Program.set oracle_output y).wp
        (fun aσ : Unit × state =>
          if ow_challenge_x.get aσ.2 = ow_challenge_x.get σ then F aσ else 0)
        aσ_adv.2
  conv_lhs => rw [wp_bind, wp_get]
  conv_rhs => rw [wp_bind, wp_get]
  simp only []
  conv_lhs => rw [wp_bind, wp_get]
  conv_rhs => rw [wp_bind, wp_get]
  simp only []
  set inp := oracle_input.get aσ_adv.2
  set cx := ow_challenge_x.get aσ_adv.2
  have h_inner_inRange : ((if inp = cx then
      Program.set chal_x_queried true
      else (pure () : Program state Unit)) >>= fun _ =>
        lazy_query inp >>= fun y =>
          Program.set oracle_output y).inRange ow_challenge_x.compl.range :=
    body_inner_inRange_chal_x_compl inp cx
  rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_inner_inRange _ aσ_adv.2,
      Program.wp_strengthen_lens_preserved ow_challenge_x h_inner_inRange
        (fun aσ : Unit × state =>
          if ow_challenge_x.get aσ.2 = ow_challenge_x.get σ then F aσ else 0) aσ_adv.2]
  congr 1
  funext aσ_rest
  by_cases h_cx_rest : ow_challenge_x.get aσ_rest.2 = ow_challenge_x.get aσ_adv.2
  swap
  · simp only [if_neg h_cx_rest]
  simp only [if_pos h_cx_rest]
  simp [if_pos (h_cx_rest.trans h_cx_pres)]

/-- `ow_loop_tracked q` preserves chal_x value. By induction on q using the
    body preservation lemma. -/
private lemma ow_loop_tracked_preserves_chal_x_wp
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range) :
    ∀ (q : ℕ) (σ : state) (F : Unit × state → ENNReal),
    (ow_loop_tracked ow_adv q lazy_query).wp F σ
    = (ow_loop_tracked ow_adv q lazy_query).wp
        (fun aσ : Unit × state =>
          if ow_challenge_x.get aσ.2 = ow_challenge_x.get σ then F aσ else 0) σ := by
  intro q
  induction q with
  | zero =>
    intro σ F
    show (Pure.pure () : Program state Unit).wp F σ
        = (Pure.pure () : Program state Unit).wp _ σ
    rw [wp_pure, wp_pure]
    simp
  | succ q ih =>
    intro σ F
    -- loop_(q+1) = body; loop_q. Apply wp_bind.
    show (ow_loop_body_tracked ow_adv lazy_query >>= fun _ : Unit =>
            ow_loop_tracked ow_adv q lazy_query).wp F σ
        = (ow_loop_body_tracked ow_adv lazy_query >>= fun _ : Unit =>
            ow_loop_tracked ow_adv q lazy_query).wp _ σ
    rw [wp_bind, wp_bind]
    -- LHS = body.wp (fun aσ_b => loop_q.wp F aσ_b.2) σ.
    -- Apply body chal_x preservation: LHS = body.wp (if chal_x_pres aσ_b then ... else 0) σ.
    rw [ow_loop_body_tracked_preserves_chal_x_wp ow_adv h_ow_adv_chal_x _ σ]
    rw [ow_loop_body_tracked_preserves_chal_x_wp ow_adv h_ow_adv_chal_x
        (fun aσ : Unit × state =>
          (ow_loop_tracked ow_adv q lazy_query).wp
            (fun aσ' : Unit × state =>
              if ow_challenge_x.get aσ'.2 = ow_challenge_x.get σ then F aσ' else 0)
            aσ.2) σ]
    -- Both sides now have body.wp (if chal_x_pres then ... else 0) σ.
    -- Show per aσ_b with chal_x_pres: loop_q.wp F aσ_b.2 = loop_q.wp F_strong aσ_b.2.
    congr 1
    funext aσ_b
    by_cases h_cx_b : ow_challenge_x.get aσ_b.2 = ow_challenge_x.get σ
    swap
    · simp only [if_neg h_cx_b]
    simp only [if_pos h_cx_b]
    -- aσ_b.2 has chal_x.get = chal_x.get σ. Apply IH at aσ_b.2.
    have h_ih := ih aσ_b.2 F
    -- h_ih: loop_q.wp F aσ_b.2 = loop_q.wp (if chal_x.get = chal_x.get aσ_b.2 then F else 0) aσ_b.2.
    rw [h_ih, h_cx_b]

/-- F'_x freshness analog of `ow_loop_tracked_lazy_query_freshness` for the
    indep indicator. -/
private lemma ow_loop_tracked_lazy_query_freshness_indep
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (h_ow_adv_chal_x_queried : ow_adv.inRange chal_x_queried.compl.range)
    (q : ℕ) (x : input) (σ : state)
    (h_σ_qf : chal_x_queried.get σ = false)
    (h_σ_ro : random_oracle_state.get σ x = none) :
    (lazy_query x >>= fun y => Program.set ow_challenge_y y >>= fun _ =>
        ow_loop_tracked ow_adv q lazy_query).wp
      (fun aσ : Unit × state =>
        if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
        then (1 : ENNReal) else 0)
      (ow_challenge_x.set x σ)
    = (ow_loop_tracked ow_adv q lazy_query).wp
      (fun aσ : Unit × state =>
        if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
        then (1 : ENNReal) else 0)
      (ow_challenge_x.set x σ) := by
  set σ_in := ow_challenge_x.set x σ with σ_in_def
  set F : Unit × state → ENNReal :=
    fun aσ : Unit × state =>
      if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
      then (1 : ENNReal) else 0 with hF_def
  have h_σ_in_cxq : chal_x_queried.get σ_in = false := by
    rw [σ_in_def, chal_x_queried.get_of_disjoint_set]; exact h_σ_qf
  have h_σ_in_chal_x : ow_challenge_x.get σ_in = x := ow_challenge_x.set_get σ x
  have h_σ_in_ro_x : random_oracle_state.get σ_in x = none := by
    rw [σ_in_def, random_oracle_state.get_of_disjoint_set]; exact h_σ_ro
  have h_σ_in_ro_chal_x : random_oracle_state.get σ_in (ow_challenge_x.get σ_in) = none := by
    rw [h_σ_in_chal_x]; exact h_σ_in_ro_x
  have h_loop_inRange_cy : (ow_loop_tracked ow_adv q lazy_query).inRange
      ow_challenge_y.compl.range :=
    ow_loop_tracked_inRange_ow_challenge_y_compl ow_adv h_ow_adv_chal_y q
  -- F doesn't read ow_challenge_y (reads resp, cxq — both ⟂ chal_y).
  have h_F_no_cy : ∀ v : output, ∀ aσ : Unit × state,
      F (aσ.1, ow_challenge_y.set v aσ.2) = F aσ := by
    intro v aσ
    simp only [hF_def]
    rw [ow_response.get_of_disjoint_set, chal_x_queried.get_of_disjoint_set]
  have h_drop_chal_y : ∀ (v : output) (σ' : state),
      (Program.set ow_challenge_y v >>= fun _ : Unit =>
          ow_loop_tracked ow_adv q lazy_query).wp F σ'
      = (ow_loop_tracked ow_adv q lazy_query).wp F σ' :=
    fun v σ' => Program.wp_set_disjoint_no_op h_loop_inRange_cy v F (h_F_no_cy v) σ'
  rw [wp_bind]
  simp_rw [h_drop_chal_y]
  have h_lq_compute : ∀ (Q : output × state → ENNReal),
      (lazy_query x).wp Q σ_in
      = ∑ v : output, Q (v, random_oracle_state.set
          (fun k => if k = x then some v else random_oracle_state.get σ_in k) σ_in)
            / Fintype.card output := by
    intro Q
    show (do let h <- Program.get random_oracle_state
             match h x with
             | some v => pure v
             | none => do let value <- Program.uniform
                          Program.set random_oracle_state
                            (fun k => if k=x then some value else h k)
                          pure value).wp Q σ_in = _
    simp only [wp_bind, wp_get]
    rw [h_σ_in_ro_x]
    simp only [wp_bind, wp_uniform, wp_set, wp_pure]
  rw [h_lq_compute]
  -- Apply F'_x averaged invariance at σ_in.
  have h_avg := ow_loop_tracked_indep_RO_invariance_avg ow_adv h_ow_adv_chal_x_queried
    h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x h_ow_adv_chal_x_queried q σ_in
    h_σ_in_cxq h_σ_in_ro_chal_x
  rw [h_σ_in_chal_x] at h_avg
  -- Convert ∑ / c to (1/c) * ∑.
  rw [show ∀ (g : output → ENNReal),
      (∑ v : output, g v / Fintype.card output)
      = 1 / Fintype.card output * ∑ v : output, g v from fun g => by
    rw [Finset.mul_sum]; congr 1; funext v; rw [ENNReal.div_eq_inv_mul, one_div]]
  exact h_avg

include h_ow_adv_chal_x_queried in
/-- **Conditional independence**: on the event `¬chal_x_queried_at_end`,
    the adversary's response equals `ow_challenge_x` with probability
    at most `1/|input|`.

    Intuition: if `chal_x_queried_at_end` is false, the adversary never
    queried `ow_challenge_x` during the loop. Since the adversary cannot
    read `ow_challenge_x` directly, its view (and hence its response) is
    statistically independent of `ow_challenge_x`. Thus the probability
    the adversary's deterministic-from-view response coincides with the
    uniformly-sampled `ow_challenge_x` is `1/|input|`. -/
lemma ow_experiment_tracked_indep_bound
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (q : ℕ) (σ₀ : state) :
    (ow_experiment_tracked ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state =>
          if ow_response.get bσ.2 = ow_challenge_x.get bσ.2 ∧
             ¬ chal_x_queried.get bσ.2
          then (1 : ENNReal) else 0) σ₀
    ≤ (1 : ENNReal) / Fintype.card input := by
  set σ_a : state := chal_x_queried.set false (random_oracle_state.set (fun _ => none) σ₀)
    with σ_a_def
  have h_σ_a_cxq : chal_x_queried.get σ_a = false := by
    rw [σ_a_def, chal_x_queried.set_get]
  have h_σ_a_ro : ∀ k : input, random_oracle_state.get σ_a k = none := by
    intro k
    rw [σ_a_def, random_oracle_state.get_of_disjoint_set, random_oracle_state.set_get]
  set F_unit : Unit × state → ENNReal :=
    fun aσ : Unit × state =>
      if ow_response.get aσ.2 = ow_challenge_x.get aσ.2 ∧ ¬ chal_x_queried.get aσ.2
      then (1 : ENNReal) else 0 with hF_unit_def
  have h_post_drop : ∀ (y : output) (σ' : state),
      (Program.set ow_challenge_y y >>= fun _ =>
          ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
          Program.get ow_response >>= fun resp =>
          lazy_query resp >>= fun y_check =>
          (pure (decide (y_check = y)) : Program state Bool)).wp
        (fun bσ : Bool × state =>
          if ow_response.get bσ.2 = ow_challenge_x.get bσ.2 ∧ ¬ chal_x_queried.get bσ.2
          then (1 : ENNReal) else 0) σ'
      ≤ (Program.set ow_challenge_y y >>= fun _ =>
          ow_loop_tracked ow_adv q lazy_query).wp F_unit σ' := by
    intro y σ'
    conv_lhs => rw [wp_bind, wp_set, wp_bind]
    conv_rhs => rw [wp_bind, wp_set]
    refine Program.wp_le_wp_of_le _ _ _ ?_ _
    intro aσ_l
    exact post_loop_preserves_indep_wp y aσ_l.2
  -- For σ_l with chal_x.get σ_l = x, loop.wp F_unit σ_l = loop.wp F'_x σ_l.
  have h_loop_bridge : ∀ (x : input) (σ_l : state), ow_challenge_x.get σ_l = x →
      (ow_loop_tracked ow_adv q lazy_query).wp F_unit σ_l
      = (ow_loop_tracked ow_adv q lazy_query).wp
          (fun aσ : Unit × state =>
            if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
            then (1 : ENNReal) else 0) σ_l := by
    intro x σ_l h_σ_l_x
    rw [ow_loop_tracked_preserves_chal_x_wp ow_adv h_ow_adv_chal_x q σ_l F_unit,
        ow_loop_tracked_preserves_chal_x_wp ow_adv h_ow_adv_chal_x q σ_l
          (fun aσ : Unit × state =>
            if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)]
    congr 1
    funext aσ
    by_cases h : ow_challenge_x.get aσ.2 = ow_challenge_x.get σ_l
    swap
    · simp only [if_neg h]
    simp only [if_pos h]
    rw [hF_unit_def]
    simp only [h, h_σ_l_x]
  -- Per-x bound.
  have h_per_x : ∀ x : input,
      (Program.set ow_challenge_x x >>= fun _ =>
        lazy_query x >>= fun y => Program.set ow_challenge_y y >>= fun _ =>
        ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
        Program.get ow_response >>= fun resp =>
        lazy_query resp >>= fun y_check =>
        (pure (decide (y_check = y)) : Program state Bool)).wp
          (fun bσ : Bool × state =>
            if ow_response.get bσ.2 = ow_challenge_x.get bσ.2 ∧ ¬ chal_x_queried.get bσ.2
            then (1 : ENNReal) else 0) σ_a
      ≤ (ow_loop_tracked ow_adv q lazy_query).wp
          (fun aσ : Unit × state =>
            if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2
            then (1 : ENNReal) else 0)
          (ow_challenge_x.set x σ_a) := by
    intro x
    rw [wp_bind, wp_set, wp_bind]
    -- Apply h_post_drop inside.
    refine le_trans (Program.wp_le_wp_of_le _ _
      (fun yσ_l : output × state =>
        (Program.set ow_challenge_y yσ_l.1 >>= fun _ =>
            ow_loop_tracked ow_adv q lazy_query).wp F_unit yσ_l.2)
      (fun yσ_l => h_post_drop yσ_l.1 yσ_l.2) _) ?_
    -- Now bound (lazy_query x).wp (fun yσ => (chal_y; loop).wp F_unit yσ.2) σ' ≤ loop.wp F'_x σ'.
    -- Strategy: replace inner F_unit by F'_x using h_loop_bridge.
    -- For yσ in lazy_query x's support at chal_x.set x σ_a: chal_x.get yσ.2 = x.
    -- chal_x.get (chal_y.set yσ.1 yσ.2) = chal_x.get yσ.2 = x.
    -- So loop.wp F_unit (chal_y.set yσ.1 yσ.2) = loop.wp F'_x (chal_y.set yσ.1 yσ.2).
    have h_lq_inRange_cx : (lazy_query x).inRange ow_challenge_x.compl.range :=
      Program.inRange_mono (lazy_query_inRange_ro _)
        (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_x)
    -- Apply wp_strengthen on lazy_query x to enforce yσ.2 has chal_x.get = x.
    rw [Program.wp_strengthen_lens_preserved ow_challenge_x h_lq_inRange_cx _
        (ow_challenge_x.set x σ_a)]
    -- Inner: replace F_unit by F'_x using h_loop_bridge.
    have h_inner_eq : ∀ yσ : output × state,
        ow_challenge_x.get yσ.2 = ow_challenge_x.get (ow_challenge_x.set x σ_a) →
        (Program.set ow_challenge_y yσ.1 >>= fun _ =>
            ow_loop_tracked ow_adv q lazy_query).wp F_unit yσ.2
        = (Program.set ow_challenge_y yσ.1 >>= fun _ =>
            ow_loop_tracked ow_adv q lazy_query).wp
          (fun aσ : Unit × state =>
            if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)
          yσ.2 := by
      intro yσ h_cx_yσ
      have h_yσ_x : ow_challenge_x.get yσ.2 = x := by
        rw [h_cx_yσ, ow_challenge_x.set_get]
      rw [wp_bind, wp_set, wp_bind, wp_set]
      have h_chal_y_x : ow_challenge_x.get (ow_challenge_y.set yσ.1 yσ.2) = x := by
        rw [ow_challenge_x.get_of_disjoint_set]; exact h_yσ_x
      exact h_loop_bridge x _ h_chal_y_x
    -- Apply h_inner_eq via wp_le_wp_of_le.
    refine le_trans (Program.wp_le_wp_of_le _ _
      (fun yσ_l : output × state =>
        if ow_challenge_x.get yσ_l.2 = ow_challenge_x.get (ow_challenge_x.set x σ_a) then
          (Program.set ow_challenge_y yσ_l.1 >>= fun _ =>
              ow_loop_tracked ow_adv q lazy_query).wp
            (fun aσ : Unit × state =>
              if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)
            yσ_l.2
        else 0) ?_ _) ?_
    · intro yσ_l
      by_cases h_cx : ow_challenge_x.get yσ_l.2 = ow_challenge_x.get (ow_challenge_x.set x σ_a)
      swap
      · simp only [if_neg h_cx]; rfl
      simp only [if_pos h_cx]
      rw [h_inner_eq yσ_l h_cx]
    -- Now (lazy_query x).wp (if chal_x_pres then (chal_y; loop).wp F'_x yσ.2 else 0) σ'.
    -- Reverse wp_strengthen on lazy_query x.
    rw [← Program.wp_strengthen_lens_preserved ow_challenge_x h_lq_inRange_cx _
        (ow_challenge_x.set x σ_a)]
    -- Now (lazy_query x).wp (fun yσ => (chal_y; loop).wp F'_x yσ.2) σ' = (chain).wp F'_x σ' (by wp_bind).
    rw [show (lazy_query x).wp
        (fun yσ_l : output × state =>
          (Program.set ow_challenge_y yσ_l.1 >>= fun _ =>
              ow_loop_tracked ow_adv q lazy_query).wp
            (fun aσ : Unit × state =>
              if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)
            yσ_l.2)
        (ow_challenge_x.set x σ_a)
        = (lazy_query x >>= fun y => Program.set ow_challenge_y y >>= fun _ =>
            ow_loop_tracked ow_adv q lazy_query).wp
          (fun aσ : Unit × state =>
            if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)
          (ow_challenge_x.set x σ_a) from by rw [wp_bind]]
    -- Apply F'_x freshness.
    rw [ow_loop_tracked_lazy_query_freshness_indep ow_adv h_ow_adv h_ow_adv_chal_y
        h_ow_adv_chal_x h_ow_adv_chal_x_queried q x σ_a h_σ_a_cxq (h_σ_a_ro x)]
  -- Outer experiment unfold + sum lemma.
  show (lazy_init >>= fun _ => Program.set chal_x_queried false >>= fun _ =>
        Program.uniform >>= fun x => Program.set ow_challenge_x x >>= fun _ =>
        lazy_query x >>= fun y => Program.set ow_challenge_y y >>= fun _ =>
        ow_loop_tracked ow_adv q lazy_query >>= fun _ =>
        Program.get ow_response >>= fun resp =>
        lazy_query resp >>= fun y_check =>
        (pure (decide (y_check = y)) : Program state Bool)).wp _ σ₀ ≤ _
  rw [wp_bind]
  unfold lazy_init
  rw [wp_set, wp_bind, wp_set]
  simp only []
  rw [wp_bind, wp_uniform]
  refine le_trans (Finset.sum_le_sum (fun x _ =>
    ENNReal.div_le_div_right (h_per_x x) _)) ?_
  rw [show ∑ x : input,
        (ow_loop_tracked ow_adv q lazy_query).wp
          (fun aσ : Unit × state =>
            if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)
          (ow_challenge_x.set x σ_a) / Fintype.card input
        = (∑ x : input, (ow_loop_tracked ow_adv q lazy_query).wp
          (fun aσ : Unit × state =>
            if ow_response.get aσ.2 = x ∧ ¬ chal_x_queried.get aσ.2 then (1 : ENNReal) else 0)
          (ow_challenge_x.set x σ_a)) / Fintype.card input from by
    simp only [ENNReal.div_eq_inv_mul, ← Finset.mul_sum]]
  have h_sum_bound := ow_loop_tracked_indep_sum_le_strong ow_adv h_ow_adv_chal_x_queried
    h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x q σ_a
  rw [if_neg (by rw [h_σ_a_cxq]; exact Bool.false_ne_true)] at h_sum_bound
  exact ENNReal.div_le_div_right h_sum_bound _

/-! ### Composition: closing the OW bound

Using the two bounds above plus the experiment equivalence, we close the
original `ow_experiment_resp_eq_chal_x_bound` sorry in `OneWayness.lean`.
-/

/-- Indicator decomposition: `[resp = chal_x ∧ is_preimage]` is bounded by
    the sum of `[chal_x_queried]` and `[resp = chal_x ∧ ¬chal_x_queried]`. -/
private lemma resp_chal_x_preimage_decomp (σ : state) :
    (if ow_response.get σ = ow_challenge_x.get σ ∧ is_preimage σ
     then (1 : ENNReal) else 0)
    ≤ (if chal_x_queried.get σ then (1 : ENNReal) else 0)
      + (if ow_response.get σ = ow_challenge_x.get σ ∧
            ¬ chal_x_queried.get σ
         then (1 : ENNReal) else 0) := by
  by_cases h_queried : chal_x_queried.get σ
  · rw [if_pos h_queried]
    by_cases h : ow_response.get σ = ow_challenge_x.get σ ∧ is_preimage σ
    · rw [if_pos h]
      exact (le_add_right (le_refl (1 : ENNReal)))
    · rw [if_neg h]
      exact bot_le
  · rw [if_neg h_queried]
    by_cases h : ow_response.get σ = ow_challenge_x.get σ ∧ is_preimage σ
    · rw [if_pos h]
      have h2 : ow_response.get σ = ow_challenge_x.get σ ∧ ¬ chal_x_queried.get σ :=
        ⟨h.1, h_queried⟩
      rw [if_pos h2]; rw [zero_add]
    · rw [if_neg h]; exact bot_le

include h_ow_adv_chal_x_queried in
/-- **The OW bound, via the tracking variable approach**: in the *lazy*
    experiment, `E[resp = chal_x ∧ is_preimage] ≤ (q+1)/|input|`.

    Composes:
    1. `ow_experiment_eq_tracked_lazy` (switch to tracked variant).
    2. `resp_chal_x_preimage_decomp` (decompose indicator).
    3. `ow_experiment_tracked_chal_x_queried_bound` (Layer C_obs).
    4. `ow_experiment_tracked_indep_bound` (conditional independence). -/
theorem ow_experiment_resp_eq_chal_x_bound_via_tracked
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (q : ℕ) (σ₀ : state) :
    (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state =>
          if ow_response.get bσ.2 = ow_challenge_x.get bσ.2 ∧ is_preimage bσ.2
          then (1 : ENNReal) else 0) σ₀
    ≤ ((q + 1) : ENNReal) / Fintype.card input := by
  -- Step 1: lazy_init is in chal_x_queried.compl.range.
  have h_lazy_init_inRange :
      (lazy_init : Program state Unit).inRange chal_x_queried.compl.range :=
    Program.set_inRange_compl_of_disjoint random_oracle_state chal_x_queried _
  -- Step 2: switch to tracked variant via the equivalence.
  rw [ow_experiment_eq_tracked_lazy ow_adv h_ow_adv_chal_x_queried q lazy_init
      h_lazy_init_inRange _ (preimage_win_ignores_chal_x_queried) σ₀]
  -- Step 3: bound by the decomposition.
  calc (ow_experiment_tracked ow_adv q lazy_init lazy_query).wp
          (fun bσ : Bool × state =>
            if ow_response.get bσ.2 = ow_challenge_x.get bσ.2 ∧ is_preimage bσ.2
            then (1 : ENNReal) else 0) σ₀
      ≤ (ow_experiment_tracked ow_adv q lazy_init lazy_query).wp
          (fun bσ : Bool × state =>
            (if chal_x_queried.get bσ.2 then (1 : ENNReal) else 0)
            + (if ow_response.get bσ.2 = ow_challenge_x.get bσ.2 ∧
                  ¬ chal_x_queried.get bσ.2
               then (1 : ENNReal) else 0)) σ₀ := by
        apply Program.wp_le_wp_of_le
        intro bσ
        exact resp_chal_x_preimage_decomp bσ.2
    _ = (ow_experiment_tracked ow_adv q lazy_init lazy_query).wp
          (fun bσ : Bool × state =>
            if chal_x_queried.get bσ.2 then (1 : ENNReal) else 0) σ₀
        + (ow_experiment_tracked ow_adv q lazy_init lazy_query).wp
          (fun bσ : Bool × state =>
            if ow_response.get bσ.2 = ow_challenge_x.get bσ.2 ∧
               ¬ chal_x_queried.get bσ.2
            then (1 : ENNReal) else 0) σ₀ := by
        rw [Program.wp_add]
    _ ≤ (q : ENNReal) / Fintype.card input
        + (1 : ENNReal) / Fintype.card input := by
        gcongr
        · exact ow_experiment_tracked_chal_x_queried_bound ow_adv
            h_ow_adv_chal_x_queried h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x q σ₀
        · exact ow_experiment_tracked_indep_bound ow_adv
            h_ow_adv_chal_x_queried h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x q σ₀
    _ = ((q + 1) : ENNReal) / Fintype.card input := by
        rw [← ENNReal.add_div]

include h_ow_adv_chal_x_queried in
/-- **Layer D_OW (closed)**: probability bound on `preimage_indicator` at the
    end of the experiment. Closes the original `ow_preimage_bound` from
    `OneWayness.lean` without axioms (modulo two clean sub-bounds). -/
theorem ow_preimage_bound
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (q : ℕ) (σ₀ : state) :
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
        · exact ow_experiment_resp_eq_chal_x_bound_via_tracked ow_adv
            h_ow_adv_chal_x_queried h_ow_adv h_ow_adv_chal_y h_ow_adv_chal_x q σ₀
    _ ≤ ((q + 1) : ENNReal) / N + ((q + 1) : ENNReal) / N := by
        gcongr
        rw [hN_def]
        exact_mod_cast card_input_ge_output
    _ = (2 * (q + 1) : ENNReal) / N := by
        rw [← ENNReal.add_div]; ring_nf

include h_ow_adv_chal_x_queried in
/-- **Birthday-style bound** for the lazy one-wayness experiment, closed via
    the deferred-sampling tracking variable. -/
theorem ow_lazy_bound
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (q : ℕ) (σ₀ : state) :
    ((ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0)) σ₀
    ≤ (2 * (q + 1) : ENNReal) / Fintype.card output :=
  le_trans (ow_true_implies_preimage_wp ow_adv h_ow_adv_chal_y q σ₀)
    (ow_preimage_bound ow_adv h_ow_adv_chal_x_queried h_ow_adv
       h_ow_adv_chal_y h_ow_adv_chal_x q σ₀)

include h_ow_adv_chal_x_queried in
/-- **One-wayness bound for the eager (true random oracle) game**, obtained by
    transferring `ow_lazy_bound` via `ow_transfer`. Closed via the tracking
    variable. -/
theorem ow_eager_bound
    (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
    (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)
    (h_ow_adv_chal_x : ow_adv.inRange ow_challenge_x.compl.range)
    (q : ℕ) (σ₀ : state) :
    ((ow_experiment ow_adv q random_oracle_init random_oracle_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0)) σ₀
    ≤ (2 * (q + 1) : ENNReal) / Fintype.card output := by
  rw [← ow_transfer_wp_of_bit ow_adv h_ow_adv q σ₀
        (fun b => if b then (1 : ENNReal) else 0)]
  exact ow_lazy_bound ow_adv h_ow_adv_chal_x_queried h_ow_adv
    h_ow_adv_chal_y h_ow_adv_chal_x q σ₀

end OWParam
