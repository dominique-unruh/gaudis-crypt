import GaudisCrypt.Lib.RO.OneWayness_GameHop.Definitions
import GaudisCrypt.Lib.RO.OneWayness_GameHop.GuessExperiment
import GaudisCrypt.Logic.PRHL

open GaudisCrypt
open GaudisCrypt

/-!
# OneWayness GameHop: Up-to-Bad Hop (Game 1 → Game 2), relationally

This module bounds the difference between `ow_game_1_tracked` and
`ow_game_2_tracked` by the bad event (the adversary queried `chal_x`).
The two games differ only in whether the random oracle is *pre-programmed*
at `chal_x` (Game 1 does, Game 2 doesn't).

**One pRHL judgment delivers everything** (`ow_game_tracked_relE`):
`G1 ~ G2 : Eq ⇒ PostG` where `PostG` says the bad flags agree and, on good
runs, the results agree and the states differ only by the pre-programmed
RO entry. The coupling invariant carried through the adversary loop is

```
InvUB x y σ₁ σ₂ := flag σ₁ = flag σ₂
                 ∧ (flag σ₁ = false → chal_x σ₂ = x ∧ σ₁ = insRO x y σ₂)
```

The per-query coupling `lqt_relE` is proved by exhibiting one coupling per
cache branch (`relE.of_coupling`); the after-bad phase is the rectangular
rule `rel.of_unary`, whose side conditions are the flag-monotonicity and
mass-1 facts.

## Main results (all corollaries of the judgment)

* `ow_game_1_tracked_eq_ow_game_2_tracked_until_bad` — agree-until-bad
  (via `relE.wp_eq`).
* `ow_game_1_tracked_bad_eq_ow_game_2_tracked_bad` — bad events agree
  (via `relE.bad_eq`; the former unary proof needed a 138-line
  mass-conservation/cancellation chain).
* `ow_game_1_tracked_le_ow_game_2_tracked_plus_bad` — the hop bound
  (via `relE.up_to_bad`).

**Hypothesis note**: the single-judgment route needs the adversary's
mass-1 hypothesis for all three results (the rectangular phase needs the
right side to be lossless). The OW master theorem assumes it anyway.

The former ~790-line unary development (per-step RO-invariance machinery,
flag-true-zero family, mass block, hand-rolled identical-until-bad
induction) was replaced by this relational proof; see git history.
-/

section UpToBad

variable (ow_adv : ProgramDenotation state Unit)

/-! ### Tracking is invisible to flag-ignoring posts (kept: used by Game1) -/

/-- One `lazy_query_tracked` is wp-equivalent to one `lazy_query` for any
    flag-ignoring continuation whose post is also flag-ignoring. -/
lemma lazy_query_tracked_eq_lazy_query_wp
    {α : Type} (k : output → ProgramDenotation state α)
    (h_k_inRange : ∀ y, (k y).inRange chal_x_queried_gh.compl.range)
    (F : α × state → ENNReal) (h_F_inv : IgnoresLens chal_x_queried_gh F)
    (inp : input) (σ : state) :
    (lazy_query_tracked inp >>= k).wp F σ
    = (lazy_query inp >>= k).wp F σ := by
  unfold lazy_query_tracked
  show
    ((lazy_query inp >>= fun y =>
      ProgramDenotation.get ow_challenge_x >>= fun cx =>
        (if inp = cx then ProgramDenotation.set chal_x_queried_gh true
         else (pure () : ProgramDenotation state Unit)) >>= fun _ =>
        (pure y : ProgramDenotation state output)) >>= k).wp F σ
    = (lazy_query inp >>= k).wp F σ
  -- Re-associate the binds so `k` is the innermost continuation.
  simp only [ProgramDenotation.bind_assoc, ProgramDenotation.pure_bind]
  show
    (lazy_query inp >>= fun y =>
      ProgramDenotation.get ow_challenge_x >>= fun cx =>
        (if inp = cx then ProgramDenotation.set chal_x_queried_gh true
         else (pure () : ProgramDenotation state Unit)) >>= fun _ =>
        k y).wp F σ
    = (lazy_query inp >>= k).wp F σ
  rw [wp_bind, wp_bind]
  congr 1
  funext yσ
  exact ProgramDenotation.wp_get_then_conditional_set_disjoint_no_op
    (L_get := ow_challenge_x) (L_set := chal_x_queried_gh)
    (fun cx : input => inp = cx) true (h_k_inRange yσ.1) F
    (fun aσ => h_F_inv aσ true) yσ.2

/-! ### The RO[chal_x] insertion point

`insert_at_chal_x` is the state-indexed form of the pre-programming write
(position read from the state); the relational development below uses the
fixed-position form `insRO` and relates the two where needed. -/

/-- Shorthand: the state with RO[chal_x] forcibly set to `some y_chal`. -/
noncomputable def insert_at_chal_x (y_chal : output) (σ : state) : state :=
  random_oracle_state.set
    (fun k => if k = ow_challenge_x.get σ then some y_chal
              else random_oracle_state.get σ k) σ


/-! ## The shift function and the coupling invariant -/

/-- Overwrite the RO entry at the (fixed) position `x` with `some y`.
    This is `insert_at_chal_x` with the position decoupled from the state. -/
noncomputable def insRO (x : input) (y : output) (σ : state) : state :=
  random_oracle_state.set
    (fun k => if k = x then some y else random_oracle_state.get σ k) σ

/-- Reading any RO-disjoint lens through `insRO` is invisible. -/
lemma get_insRO {γ : Type} (L : Lens γ state)
    [disjoint random_oracle_state L] (x : input) (y : output) (σ : state) :
    L.get (insRO x y σ) = L.get σ := by
  unfold insRO
  rw [Lens.get_of_disjoint_set L random_oracle_state]

private lemma RO_get_insRO (x : input) (y : output) (σ : state) :
    random_oracle_state.get (insRO x y σ)
    = fun k => if k = x then some y else random_oracle_state.get σ k := by
  unfold insRO
  rw [random_oracle_state.set_get]

/-- `insRO x y` is an update inside the RO's footprint. -/
private lemma insRO_mem (x : input) (y : output) :
    insRO x y ∈ ((random_oracle_state.compl.range : DetermFootprint state)ᶜ).updates := by
  rw [show ((random_oracle_state.compl.range : DetermFootprint state)ᶜ)
        = random_oracle_state.range from by
    rw [DetermFootprint.complement_range, DetermFootprint.compl_compl]]
  exact ⟨fun h k => if k = x then some y else h k, Set.mem_univ _, rfl⟩

/-- **The coupling invariant** between the Game-1 run (left) and the
    Game-2 run (right): flags agree; on good runs the left state is the
    right state with `RO[x ↦ y]` overwritten and the right challenge is `x`. -/
def InvUB (x : input) (y : output) (σ₁ σ₂ : state) : Prop :=
  chal_x_queried_gh.get σ₁ = chal_x_queried_gh.get σ₂
  ∧ (chal_x_queried_gh.get σ₁ = false →
      ow_challenge_x.get σ₂ = x ∧ σ₁ = insRO x y σ₂)

/-- The good-phase form of the invariant. -/
private abbrev GoodPre (x : input) (y : output) (σ₁ σ₂ : state) : Prop :=
  chal_x_queried_gh.get σ₂ = false ∧ ow_challenge_x.get σ₂ = x
  ∧ σ₁ = insRO x y σ₂

lemma invUB_of_good {x : input} {y : output} {σ₁ σ₂ : state}
    (_hf : chal_x_queried_gh.get σ₂ = false) (hcx : ow_challenge_x.get σ₂ = x)
    (hσ : σ₁ = insRO x y σ₂) : InvUB x y σ₁ σ₂ := by
  subst hσ
  exact ⟨by rw [get_insRO], fun _ => ⟨hcx, rfl⟩⟩

lemma invUB_of_bad {x : input} {y : output} {σ₁ σ₂ : state}
    (h₁ : chal_x_queried_gh.get σ₁ = true) (h₂ : chal_x_queried_gh.get σ₂ = true) :
    InvUB x y σ₁ σ₂ :=
  ⟨h₁.trans h₂.symm, fun h => absurd (h₁.symm.trans h) (by simp)⟩

lemma invUB_cases {x : input} {y : output} {σ₁ σ₂ : state}
    (h : InvUB x y σ₁ σ₂) :
    GoodPre x y σ₁ σ₂
    ∨ (chal_x_queried_gh.get σ₁ = true ∧ chal_x_queried_gh.get σ₂ = true) := by
  obtain ⟨heq, himp⟩ := h
  cases hb : chal_x_queried_gh.get σ₁ with
  | false => exact Or.inl ⟨heq.symm.trans hb, (himp hb).1, (himp hb).2⟩
  | true => exact Or.inr ⟨rfl, heq.symm.trans hb⟩

/-- Bad-bad output pairs satisfy the lqt post. -/
private lemma lqtPost_of_bad {x : input} {y : output} {u v : output × state}
    (h₁ : chal_x_queried_gh.get u.2 = true) (h₂ : chal_x_queried_gh.get v.2 = true) :
    InvUB x y u.2 v.2 ∧ (chal_x_queried_gh.get u.2 = false → u.1 = v.1) :=
  ⟨invUB_of_bad h₁ h₂, fun h => absurd (h₁.symm.trans h) (by simp)⟩

/-! ## Closed wp forms (the `wp`-tactic analogue) -/

lemma wp_lq_hit (inp : input) {σ : state} {v : output}
    (h : random_oracle_state.get σ inp = some v) (F : output × state → ENNReal) :
    (lazy_query inp).wp F σ = F (v, σ) := by
  simp only [lazy_query, wp_bind, wp_get, h, wp_pure]

lemma wp_lq_miss (inp : input) {σ : state}
    (h : random_oracle_state.get σ inp = none) (F : output × state → ENNReal) :
    (lazy_query inp).wp F σ
    = ∑ v : output, F (v, random_oracle_state.set
        (fun k => if k = inp then some v
                  else random_oracle_state.get σ k) σ) / Fintype.card output := by
  simp only [lazy_query, wp_bind, wp_get, h, wp_uniform, wp_set, wp_pure]

/-- Decompose `lazy_query_tracked.wp` into a `lazy_query.wp` with the
    flag-branching folded into the post. -/
lemma wp_lqt (inp : input) (F : output × state → ENNReal) (σ : state) :
    (lazy_query_tracked inp).wp F σ
    = (lazy_query inp).wp
        (fun yσ : output × state =>
          if inp = ow_challenge_x.get yσ.2 then
            F (yσ.1, chal_x_queried_gh.set true yσ.2)
          else F yσ) σ := by
  unfold lazy_query_tracked
  simp only [wp_bind, wp_get, wp_pure]
  congr 1
  funext yσ
  by_cases h : inp = ow_challenge_x.get yσ.2
  · simp only [h, ↓reduceIte, wp_set]
  · simp only [h, ↓reduceIte, wp_pure]

lemma wp_set_seq_state {γ α : Type} (L : Lens γ state) (v : γ)
    (P : ProgramDenotation state α) (F : α × state → ENNReal) (σ : state) :
    (ProgramDenotation.set L v >>= fun _ : Unit => P).wp F σ = P.wp F (L.set v σ) := by
  rw [wp_bind, wp_set]

lemma wp_uniform_seq_state {α β : Type} [Fintype α] [Nonempty α]
    (k : α → ProgramDenotation state β) (F : β × state → ENNReal) (σ : state) :
    ((ProgramDenotation.uniform : ProgramDenotation state α) >>= k).wp F σ
    = ∑ v : α, (k v).wp F σ / Fintype.card α := by
  rw [wp_bind, wp_uniform]

/-! ## The per-query coupling (the heart of the hop)

`lazy_query_tracked inp` relates to itself across `insRO x y`:
* `inp ≠ x`: both sides read the same cache entry — hit-hit returns the
  same value, miss-miss couples the fresh sample identically and the new
  entry commutes with the `x`-overwrite. Good post, equal values.
* `inp = x`: the left side hits the pre-programmed entry while the right
  side does whatever its cache says — but *both* set the flag. Bad post.

Proved by exhibiting one coupling per branch (`relE.of_coupling`), so both
judgment directions come from a single case analysis. -/
private lemma lqt_relE (x : input) (y : output) (inp₁ inp₂ : input) :
    (lazy_query_tracked inp₁).relE (lazy_query_tracked inp₂)
      (fun σ₁ σ₂ => (inp₁ = inp₂ ∧ chal_x_queried_gh.get σ₂ = false
          ∧ ow_challenge_x.get σ₂ = x) ∧ σ₁ = insRO x y σ₂)
      (fun u v => InvUB x y u.2 v.2
        ∧ (chal_x_queried_gh.get u.2 = false → u.1 = v.1)) := by
  -- shared state algebra ---------------------------------------------------
  have hsetentry : ∀ (σ₂ : state) (v : output), inp₁ ≠ x →
      random_oracle_state.set
        (fun k => if k = inp₁ then some v
                  else random_oracle_state.get (insRO x y σ₂) k) (insRO x y σ₂)
      = insRO x y (random_oracle_state.set
          (fun k => if k = inp₁ then some v
                    else random_oracle_state.get σ₂ k) σ₂) := by
    intro σ₂ v hix
    unfold insRO
    simp only [random_oracle_state.set_get, random_oracle_state.set_set]
    congr 1
    funext k
    by_cases hk₁ : k = inp₁
    · subst hk₁; simp [hix]
    · by_cases hk₂ : k = x
      · subst hk₂; simp [hk₁]
      · simp [hk₁, hk₂]
  refine ProgramDenotation.relE.of_coupling ?_
  rintro σ₁ σ₂ ⟨⟨rfl, hf₂, hcx⟩, rfl⟩
  have hcx' : ow_challenge_x.get (insRO x y σ₂) = x := by
    rw [get_insRO]; exact hcx
  by_cases hix : inp₁ = x
  · -- bad transition: LHS hits the pre-programmed entry; both flags fire.
    have hhit : random_oracle_state.get (insRO x y σ₂) inp₁ = some y := by
      rw [RO_get_insRO]; simp [hix]
    have hL : ∀ F : output × state → ENNReal,
        (lazy_query_tracked inp₁).wp F (insRO x y σ₂)
        = F (y, chal_x_queried_gh.set true (insRO x y σ₂)) := by
      intro F
      rw [wp_lqt, wp_lq_hit inp₁ hhit]
      dsimp only
      rw [hcx', if_pos hix]
    cases hr : random_oracle_state.get σ₂ inp₁ with
    | some v =>
      have hR : ∀ G : output × state → ENNReal,
          (lazy_query_tracked inp₁).wp G σ₂
          = G (v, chal_x_queried_gh.set true σ₂) := by
        intro G
        rw [wp_lqt, wp_lq_hit inp₁ hr]
        dsimp only
        rw [hcx, if_pos hix]
      exact ProgramDenotation.Coupling.of_pure _ _ hL hR
        (lqtPost_of_bad (by rw [Lens.set_get]) (by rw [Lens.set_get]))
    | none =>
      have hR : ∀ G : output × state → ENNReal,
          (lazy_query_tracked inp₁).wp G σ₂
          = ∑ t : output, G (t, chal_x_queried_gh.set true
              (random_oracle_state.set
                (fun k => if k = inp₁ then some t
                          else random_oracle_state.get σ₂ k) σ₂))
            / Fintype.card output := by
        intro G
        rw [wp_lqt, wp_lq_miss inp₁ hr]
        refine Finset.sum_congr rfl fun t _ => ?_
        congr 1
        rw [if_pos (by
          rw [Lens.get_of_disjoint_set ow_challenge_x random_oracle_state, hcx]
          exact hix)]
      refine ProgramDenotation.Coupling.of_uniform
        (fun _ : output => (y, chal_x_queried_gh.set true (insRO x y σ₂)))
        (fun t : output => (t, chal_x_queried_gh.set true
          (random_oracle_state.set
            (fun k => if k = inp₁ then some t
                      else random_oracle_state.get σ₂ k) σ₂)))
        (fun F => by rw [hL]; exact (sum_const_div_card _).symm) hR
        (fun t => lqtPost_of_bad (by rw [Lens.set_get]) (by rw [Lens.set_get]))
  · -- good step: synchronized cache behaviour.
    have hread : random_oracle_state.get (insRO x y σ₂) inp₁
        = random_oracle_state.get σ₂ inp₁ := by
      rw [RO_get_insRO]; simp [hix]
    cases hr : random_oracle_state.get σ₂ inp₁ with
    | some v =>
      have hL : ∀ F : output × state → ENNReal,
          (lazy_query_tracked inp₁).wp F (insRO x y σ₂)
          = F (v, insRO x y σ₂) := by
        intro F
        rw [wp_lqt, wp_lq_hit inp₁ (hread.trans hr)]
        dsimp only
        rw [hcx', if_neg hix]
      have hR : ∀ G : output × state → ENNReal,
          (lazy_query_tracked inp₁).wp G σ₂ = G (v, σ₂) := by
        intro G
        rw [wp_lqt, wp_lq_hit inp₁ hr]
        dsimp only
        rw [hcx, if_neg hix]
      exact ProgramDenotation.Coupling.of_pure _ _ hL hR
        ⟨invUB_of_good hf₂ hcx rfl, fun _ => rfl⟩
    | none =>
      have hL : ∀ F : output × state → ENNReal,
          (lazy_query_tracked inp₁).wp F (insRO x y σ₂)
          = ∑ t : output, F (t, random_oracle_state.set
              (fun k => if k = inp₁ then some t
                        else random_oracle_state.get (insRO x y σ₂) k)
              (insRO x y σ₂)) / Fintype.card output := by
        intro F
        rw [wp_lqt, wp_lq_miss inp₁ (hread.trans hr)]
        refine Finset.sum_congr rfl fun t _ => ?_
        congr 1
        rw [if_neg (by
          rw [Lens.get_of_disjoint_set ow_challenge_x random_oracle_state, hcx']
          exact hix)]
      have hR : ∀ G : output × state → ENNReal,
          (lazy_query_tracked inp₁).wp G σ₂
          = ∑ t : output, G (t, random_oracle_state.set
              (fun k => if k = inp₁ then some t
                        else random_oracle_state.get σ₂ k) σ₂)
            / Fintype.card output := by
        intro G
        rw [wp_lqt, wp_lq_miss inp₁ hr]
        refine Finset.sum_congr rfl fun t _ => ?_
        congr 1
        rw [if_neg (by
          rw [Lens.get_of_disjoint_set ow_challenge_x random_oracle_state, hcx]
          exact hix)]
      refine ProgramDenotation.Coupling.of_uniform _ _ hL hR (fun t => ?_)
      have hf₂' : chal_x_queried_gh.get (random_oracle_state.set
          (fun k => if k = inp₁ then some t
                    else random_oracle_state.get σ₂ k) σ₂) = false := by
        rw [Lens.get_of_disjoint_set chal_x_queried_gh random_oracle_state]
        exact hf₂
      have hcx₂' : ow_challenge_x.get (random_oracle_state.set
          (fun k => if k = inp₁ then some t
                    else random_oracle_state.get σ₂ k) σ₂) = x := by
        rw [Lens.get_of_disjoint_set ow_challenge_x random_oracle_state]
        exact hcx
      exact ⟨invUB_of_good hf₂' hcx₂' (hsetentry σ₂ t hix), fun _ => rfl⟩

/-! ## Bad-phase unary side conditions (flag monotonicity and mass) -/

lemma lqt_flag_zero {inp : input} {F : output × state → ENNReal}
    (hF : ∀ u : output × state, chal_x_queried_gh.get u.2 = true → F u = 0)
    {σ : state} (h : chal_x_queried_gh.get σ = true) :
    (lazy_query_tracked inp).wp F σ = 0 := by
  rw [wp_lqt]
  have h_lq : (lazy_query inp).inRange chal_x_queried_gh.compl.range :=
    ProgramDenotation.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state chal_x_queried_gh)
  refine ProgramDenotation.wp_zero_of_lens_preserves h_lq ?_ h
  intro u hu
  by_cases hc : inp = ow_challenge_x.get u.2
  · rw [if_pos hc]
    exact hF _ (by rw [Lens.set_get])
  · rw [if_neg hc]
    exact hF u hu

lemma lazy_query_mass (inp : input) (σ : state) :
    (lazy_query inp).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  cases h : random_oracle_state.get σ inp with
  | some v => rw [wp_lq_hit inp h]
  | none =>
    rw [wp_lq_miss inp h]
    have := ProgramDenotation.uniform_mass_one (s := state) (α := output) σ
    rw [wp_uniform] at this
    exact this

lemma lqt_mass (inp : input) (σ : state) :
    (lazy_query_tracked inp).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  rw [wp_lqt]
  simp only [ite_self]
  exact lazy_query_mass inp σ

/-- Indicator complement trick: full mass + zero on the complement gives
    mass 1 on the event. -/
lemma wp_flag_one {α : Type} (p : ProgramDenotation state α) {σ : state}
    (hmass : p.wp (fun _ => (1 : ENNReal)) σ = 1)
    (hzero : p.wp (fun u : α × state =>
      if chal_x_queried_gh.get u.2 = true then 0 else 1) σ = 0) :
    p.wp (fun u : α × state =>
      if chal_x_queried_gh.get u.2 = true then 1 else 0) σ = 1 := by
  have h := ProgramDenotation.wp_add p
    (fun u : α × state => if chal_x_queried_gh.get u.2 = true then 1 else 0)
    (fun u : α × state => if chal_x_queried_gh.get u.2 = true then 0 else 1) σ
  rw [show (fun u : α × state =>
        (if chal_x_queried_gh.get u.2 = true then (1 : ENNReal) else 0)
        + (if chal_x_queried_gh.get u.2 = true then 0 else 1))
      = fun _ : α × state => (1 : ENNReal) from by
    funext u
    by_cases hb : chal_x_queried_gh.get u.2 = true <;> simp [hb]] at h
  rw [hmass, hzero, add_zero] at h
  exact h.symm

lemma body_flag_zero
    (h_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    {F : Unit × state → ENNReal}
    (hF : ∀ u : Unit × state, chal_x_queried_gh.get u.2 = true → F u = 0)
    {σ : state} (h : chal_x_queried_gh.get σ = true) :
    (oracle_step ow_adv lazy_query_tracked).wp F σ = 0 := by
  change (ow_adv >>= fun _ =>
    ProgramDenotation.get oracle_input >>= fun inp =>
    lazy_query_tracked inp >>= fun y' =>
    ProgramDenotation.set oracle_output y').wp F σ = 0
  simp only [wp_bind, wp_get]
  refine ProgramDenotation.wp_zero_of_lens_preserves h_flag ?_ h
  rintro ⟨u, s⟩ hu
  change (lazy_query_tracked (oracle_input.get s)).wp _ s = 0
  refine lqt_flag_zero ?_ hu
  rintro ⟨a, s'⟩ hw
  change (ProgramDenotation.set oracle_output a).wp F s' = 0
  rw [wp_set]
  refine hF _ ?_
  change chal_x_queried_gh.get (oracle_output.set a s') = true
  rw [Lens.get_of_disjoint_set chal_x_queried_gh oracle_output]
  exact hw

/-- Pointwise post congruence for `wp`. -/
lemma wp_post_congr {α : Type} (p : ProgramDenotation state α)
    {F G : α × state → ENNReal} (h : ∀ u, F u = G u) (σ : state) :
    p.wp F σ = p.wp G σ := by
  rw [funext h]

lemma body_mass
    (h_mass : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1) (σ : state) :
    (oracle_step ow_adv lazy_query_tracked).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  change (ow_adv >>= fun _ =>
    ProgramDenotation.get oracle_input >>= fun inp =>
    lazy_query_tracked inp >>= fun y' =>
    ProgramDenotation.set oracle_output y').wp (fun _ => (1 : ENNReal)) σ = 1
  rw [wp_bind]
  refine (wp_post_congr _ ?_ σ).trans (h_mass σ)
  rintro ⟨u, s⟩
  change (ProgramDenotation.get oracle_input >>= fun inp =>
    lazy_query_tracked inp >>= fun y' =>
    ProgramDenotation.set oracle_output y').wp (fun _ => (1 : ENNReal)) s = (1 : ENNReal)
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_bind]
  refine (wp_post_congr _ ?_ s).trans (lqt_mass _ s)
  rintro ⟨a, s'⟩
  change (ProgramDenotation.set oracle_output a).wp (fun _ => (1 : ENNReal)) s' = (1 : ENNReal)
  rw [wp_set]

/-- The verification segment shared by both games (parameterized by the
    challenge output `y_v` it compares against). -/
noncomputable def finalSeg (y_v : output) : ProgramDenotation state Bool :=
  ProgramDenotation.get ow_response >>= fun resp =>
  lazy_query_tracked resp >>= fun y_check =>
  pure (decide (y_check = y_v))

private lemma final_flag_zero (y_v : output) {F : Bool × state → ENNReal}
    (hF : ∀ u : Bool × state, chal_x_queried_gh.get u.2 = true → F u = 0)
    {σ : state} (h : chal_x_queried_gh.get σ = true) :
    (finalSeg y_v).wp F σ = 0 := by
  unfold finalSeg
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_bind]
  refine lqt_flag_zero ?_ h
  rintro ⟨a, s'⟩ hw
  change (pure (decide (a = y_v)) : ProgramDenotation state Bool).wp F s' = 0
  rw [wp_pure]
  exact hF _ hw

private lemma final_mass (y_v : output) (σ : state) :
    (finalSeg y_v).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  unfold finalSeg
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_bind]
  refine (wp_post_congr _ ?_ σ).trans (lqt_mass _ σ)
  rintro ⟨a, s'⟩
  change (pure (decide (a = y_v)) : ProgramDenotation state Bool).wp
      (fun _ => (1 : ENNReal)) s' = (1 : ENNReal)
  rw [wp_pure]

/-! ## The rectangular (after-bad) judgments -/

lemma body_bad_relE
    (h_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_mass : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1)
    (x : input) (y : output) :
    (oracle_step ow_adv lazy_query_tracked).relE
      (oracle_step ow_adv lazy_query_tracked)
      (fun σ₁ σ₂ => chal_x_queried_gh.get σ₁ = true
        ∧ chal_x_queried_gh.get σ₂ = true)
      (fun u v => InvUB x y u.2 v.2) := by
  have h0 : ∀ σ : state, chal_x_queried_gh.get σ = true →
      (oracle_step ow_adv lazy_query_tracked).wp
        (fun u : Unit × state =>
          if chal_x_queried_gh.get u.2 = true then 0 else 1) σ = 0 := by
    intro σ h
    refine body_flag_zero ow_adv h_flag ?_ h
    intro u hu
    rw [if_pos hu]
  have h1 : ∀ σ : state, chal_x_queried_gh.get σ = true →
      (oracle_step ow_adv lazy_query_tracked).wp
        (fun u : Unit × state =>
          if chal_x_queried_gh.get u.2 = true then 1 else 0) σ = 1 := by
    intro σ h
    exact wp_flag_one _ (body_mass ow_adv h_mass σ) (h0 σ h)
  constructor
  · refine (ProgramDenotation.rel.of_unary
      (P := fun u : Unit × state => chal_x_queried_gh.get u.2 = true)
      (Q := fun v : Unit × state => chal_x_queried_gh.get v.2 = true)
      (fun σ₁ σ₂ h => h0 σ₁ h.1) (fun σ₁ σ₂ h => h1 σ₂ h.2)).conseq
      (fun _ _ h => h) ?_
    intro u v h
    exact invUB_of_bad h.1 h.2
  · refine (ProgramDenotation.rel.of_unary
      (P := fun v : Unit × state => chal_x_queried_gh.get v.2 = true)
      (Q := fun u : Unit × state => chal_x_queried_gh.get u.2 = true)
      (fun σ₂ σ₁ h => h0 σ₂ h.2) (fun σ₂ σ₁ h => h1 σ₁ h.1)).conseq
      (fun _ _ h => h) ?_
    intro v u h
    exact invUB_of_bad h.2 h.1

private lemma final_bad_relE
    (y_v : output) :
    (finalSeg y_v).relE (finalSeg y_v)
      (fun σ₁ σ₂ => chal_x_queried_gh.get σ₁ = true
        ∧ chal_x_queried_gh.get σ₂ = true)
      (fun u v => chal_x_queried_gh.get u.2 = chal_x_queried_gh.get v.2
        ∧ (chal_x_queried_gh.get u.2 = false →
            u.1 = v.1 ∧ ∃ y', u.2 = insert_at_chal_x y' v.2)) := by
  have h0 : ∀ σ : state, chal_x_queried_gh.get σ = true →
      (finalSeg y_v).wp (fun u : Bool × state =>
        if chal_x_queried_gh.get u.2 = true then 0 else 1) σ = 0 := by
    intro σ h
    refine final_flag_zero y_v ?_ h
    intro u hu
    rw [if_pos hu]
  have h1 : ∀ σ : state, chal_x_queried_gh.get σ = true →
      (finalSeg y_v).wp (fun u : Bool × state =>
        if chal_x_queried_gh.get u.2 = true then 1 else 0) σ = 1 := by
    intro σ h
    exact wp_flag_one _ (final_mass y_v σ) (h0 σ h)
  constructor
  · refine (ProgramDenotation.rel.of_unary
      (P := fun u : Bool × state => chal_x_queried_gh.get u.2 = true)
      (Q := fun v : Bool × state => chal_x_queried_gh.get v.2 = true)
      (fun σ₁ σ₂ h => h0 σ₁ h.1) (fun σ₁ σ₂ h => h1 σ₂ h.2)).conseq
      (fun _ _ h => h) ?_
    intro u v h
    exact ⟨h.1.trans h.2.symm, fun hf => absurd (h.1.symm.trans hf) (by simp)⟩
  · refine (ProgramDenotation.rel.of_unary
      (P := fun v : Bool × state => chal_x_queried_gh.get v.2 = true)
      (Q := fun u : Bool × state => chal_x_queried_gh.get u.2 = true)
      (fun σ₂ σ₁ h => h0 σ₂ h.2) (fun σ₂ σ₁ h => h1 σ₁ h.1)).conseq
      (fun _ _ h => h) ?_
    intro v u h
    exact ⟨h.2.trans h.1.symm, fun hf => absurd (h.2.symm.trans hf) (by simp)⟩

/-! ## The good-phase judgments -/

lemma body_good_relE
    (h_RO : ow_adv.inRange random_oracle_state.compl.range)
    (h_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_cx : ow_adv.inRange ow_challenge_x.compl.range)
    (x : input) (y : output) :
    (oracle_step ow_adv lazy_query_tracked).relE
      (oracle_step ow_adv lazy_query_tracked)
      (GoodPre x y) (fun u v => InvUB x y u.2 v.2) := by
  haveI : disjoint random_oracle_state oracle_input := disjoint_oracle_input_ro.symm
  -- the adversary across the shift, framed by the flag and chal_x values
  have h_adv : ow_adv.relE ow_adv (GoodPre x y)
      (fun u v : Unit × state => GoodPre x y u.2 v.2) := by
    have h2 := ProgramDenotation.relE.frame ow_challenge_x ow_challenge_x h_cx h_cx
      (ProgramDenotation.relE.frame chal_x_queried_gh chal_x_queried_gh h_flag h_flag
        ((ProgramDenotation.relE.self_shift h_RO (insRO_mem x y)).symm) false false)
      x x
    refine h2.conseq ?_ ?_
    · rintro σ₁ σ₂ ⟨hf₂, hcx, rfl⟩
      exact ⟨⟨rfl, by rw [get_insRO]; exact hf₂, hf₂⟩,
        by rw [get_insRO]; exact hcx, hcx⟩
    · rintro u v ⟨⟨⟨_, hst⟩, _, hfV⟩, _, hcxV⟩
      exact ⟨hfV, hcxV, hst⟩
  change (ow_adv >>= fun _ =>
    ProgramDenotation.get oracle_input >>= fun inp =>
    lazy_query_tracked inp >>= fun y' =>
    ProgramDenotation.set oracle_output y').relE
    (ow_adv >>= fun _ =>
    ProgramDenotation.get oracle_input >>= fun inp =>
    lazy_query_tracked inp >>= fun y' =>
    ProgramDenotation.set oracle_output y')
    (GoodPre x y) (fun u v => InvUB x y u.2 v.2)
  refine ProgramDenotation.relE.bind (Mid := fun u v : Unit × state => GoodPre x y u.2 v.2)
    h_adv (fun _ _ => ?_)
  refine ProgramDenotation.relE.bind
    (Mid := fun u v : input × state => u.1 = v.1 ∧ GoodPre x y u.2 v.2)
    (ProgramDenotation.relE.get_get ?_) (fun inp₁ inp₂ => ?_)
  · rintro σ₁ σ₂ ⟨hf₂, hcx, rfl⟩
    exact ⟨by rw [get_insRO], hf₂, hcx, rfl⟩
  · refine ProgramDenotation.relE.bind
      (Mid := fun u v : output × state => InvUB x y u.2 v.2
        ∧ (chal_x_queried_gh.get u.2 = false → u.1 = v.1))
      ((lqt_relE x y inp₁ inp₂).conseq ?_ (fun _ _ h => h))
      (fun y₁ y₂ => ProgramDenotation.relE.set_set ?_)
    · rintro τ₁ τ₂ ⟨hval, hf₂, hcx, hst⟩
      exact ⟨⟨hval, hf₂, hcx⟩, hst⟩
    · rintro τ₁ τ₂ ⟨⟨hfeq, hgood⟩, hval⟩
      have hfeq' : chal_x_queried_gh.get τ₁ = chal_x_queried_gh.get τ₂ := hfeq
      refine ⟨?_, ?_⟩
      · change chal_x_queried_gh.get (oracle_output.set y₁ τ₁)
            = chal_x_queried_gh.get (oracle_output.set y₂ τ₂)
        rw [Lens.get_of_disjoint_set chal_x_queried_gh oracle_output,
            Lens.get_of_disjoint_set chal_x_queried_gh oracle_output]
        exact hfeq'
      · intro hf
        have hf0 : chal_x_queried_gh.get (oracle_output.set y₁ τ₁) = false := hf
        rw [Lens.get_of_disjoint_set chal_x_queried_gh oracle_output] at hf0
        obtain ⟨hcx0, hst0⟩ := hgood hf0
        have hcx' : ow_challenge_x.get τ₂ = x := hcx0
        have hst' : τ₁ = insRO x y τ₂ := hst0
        have hvv : y₁ = y₂ := hval hf0
        subst hvv
        refine ⟨?_, ?_⟩
        · change ow_challenge_x.get (oracle_output.set y₁ τ₂) = x
          rw [Lens.get_of_disjoint_set ow_challenge_x oracle_output]
          exact hcx'
        · change oracle_output.set y₁ τ₁ = insRO x y (oracle_output.set y₁ τ₂)
          rw [hst']
          unfold insRO
          rw [disjoint_oracle_output_ro.commute]
          congr 1
          funext k
          by_cases hk : k = x
          · simp [hk]
          · simp only [if_neg hk]
            rw [Lens.get_of_disjoint_set random_oracle_state oracle_output]

/-- The full loop-body judgment: `Inv` is preserved by one oracle step. -/
lemma body_relE
    (h_RO : ow_adv.inRange random_oracle_state.compl.range)
    (h_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_cx : ow_adv.inRange ow_challenge_x.compl.range)
    (h_mass : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1)
    (x : input) (y : output) :
    (oracle_step ow_adv lazy_query_tracked).relE
      (oracle_step ow_adv lazy_query_tracked)
      (InvUB x y) (fun u v => InvUB x y u.2 v.2) :=
  (ProgramDenotation.relE.or_pre (body_good_relE ow_adv h_RO h_flag h_cx x y)
    (body_bad_relE ow_adv h_flag h_mass x y)).conseq
    (fun _ _ h => invUB_cases h) (fun _ _ h => h)

/-- The good-phase verification-segment judgment. -/
private lemma final_good_relE (y_v : output) (x : input) (y : output) :
    (finalSeg y_v).relE (finalSeg y_v) (GoodPre x y)
      (fun u v => chal_x_queried_gh.get u.2 = chal_x_queried_gh.get v.2
        ∧ (chal_x_queried_gh.get u.2 = false →
            u.1 = v.1 ∧ ∃ y', u.2 = insert_at_chal_x y' v.2)) := by
  unfold finalSeg
  refine ProgramDenotation.relE.bind
    (Mid := fun u v : input × state => u.1 = v.1 ∧ GoodPre x y u.2 v.2)
    (ProgramDenotation.relE.get_get ?_) (fun r₁ r₂ => ?_)
  · rintro σ₁ σ₂ ⟨hf₂, hcx, rfl⟩
    exact ⟨by rw [get_insRO], hf₂, hcx, rfl⟩
  · refine ProgramDenotation.relE.bind
      (Mid := fun u v : output × state => InvUB x y u.2 v.2
        ∧ (chal_x_queried_gh.get u.2 = false → u.1 = v.1))
      ((lqt_relE x y r₁ r₂).conseq ?_ (fun _ _ h => h))
      (fun yc₁ yc₂ => ProgramDenotation.relE.pure_pure ?_)
    · rintro τ₁ τ₂ ⟨hval, hf₂, hcx, hst⟩
      exact ⟨⟨hval, hf₂, hcx⟩, hst⟩
    · rintro τ₁ τ₂ ⟨⟨hfeq, hgood⟩, hval⟩
      refine ⟨hfeq, ?_⟩
      intro hf
      obtain ⟨hcx, hst⟩ := hgood hf
      obtain rfl := hval hf
      refine ⟨rfl, y, ?_⟩
      rw [hst]
      unfold insRO insert_at_chal_x
      rw [hcx]

/-- The full verification-segment judgment. -/
private lemma final_relE (y_v : output) (x : input) (y : output) :
    (finalSeg y_v).relE (finalSeg y_v) (InvUB x y)
      (fun u v => chal_x_queried_gh.get u.2 = chal_x_queried_gh.get v.2
        ∧ (chal_x_queried_gh.get u.2 = false →
            u.1 = v.1 ∧ ∃ y', u.2 = insert_at_chal_x y' v.2)) :=
  (ProgramDenotation.relE.or_pre (final_good_relE y_v x y) (final_bad_relE y_v)).conseq
    (fun _ _ h => invUB_cases h) (fun _ _ h => h)

/-! ## The game-level judgment -/

/-- The invariant holds at the two post-prefix states. -/
private lemma init_inv (x : input) (y : output) (σ : state) :
    InvUB x y
      (ow_challenge_y.set y (random_oracle_state.set
        (fun k => if k = x then some y else none)
        (ow_challenge_x.set x (chal_x_queried_gh.set false
          (random_oracle_state.set (fun _ => none) σ)))))
      (ow_challenge_y.set y (ow_challenge_x.set x (chal_x_queried_gh.set false
        (random_oracle_state.set (fun _ => none) σ)))) := by
  have hRO : random_oracle_state.get
      (ow_challenge_y.set y (ow_challenge_x.set x (chal_x_queried_gh.set false
        (random_oracle_state.set (fun _ => none) σ))))
      = fun _ => none := by
    rw [Lens.get_of_disjoint_set random_oracle_state ow_challenge_y,
        Lens.get_of_disjoint_set random_oracle_state ow_challenge_x,
        Lens.get_of_disjoint_set random_oracle_state chal_x_queried_gh,
        random_oracle_state.set_get]
  refine invUB_of_good ?_ ?_ ?_
  · rw [Lens.get_of_disjoint_set chal_x_queried_gh ow_challenge_y,
        Lens.get_of_disjoint_set chal_x_queried_gh ow_challenge_x,
        Lens.set_get]
  · rw [Lens.get_of_disjoint_set ow_challenge_x ow_challenge_y,
        Lens.set_get]
  · unfold insRO
    rw [hRO, disjoint_ow_challenge_y_ro.commute]

/-- **The game-level judgment**: tracked Game 1 and tracked Game 2 are
    related at "flags agree, and on good runs the results agree and the
    states differ only by the pre-programmed RO entry". All three
    up-to-bad theorems are corollaries. -/
theorem ow_game_tracked_relE
    (h_RO : ow_adv.inRange random_oracle_state.compl.range)
    (h_cx : ow_adv.inRange ow_challenge_x.compl.range)
    (h_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_mass : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1)
    (q : ℕ) :
    (ow_game_1_tracked ow_adv q).relE (ow_game_2_tracked ow_adv q) Eq
      (fun u v => chal_x_queried_gh.get u.2 = chal_x_queried_gh.get v.2
        ∧ (chal_x_queried_gh.get u.2 = false →
            u.1 = v.1 ∧ ∃ y', u.2 = insert_at_chal_x y' v.2)) := by
  have hTail : ∀ (x : input) (y : output),
      (loop_n q (oracle_step ow_adv lazy_query_tracked) >>= fun _ : Unit =>
        finalSeg y).relE
      (loop_n q (oracle_step ow_adv lazy_query_tracked) >>= fun _ : Unit =>
        finalSeg y) (InvUB x y)
      (fun u v => chal_x_queried_gh.get u.2 = chal_x_queried_gh.get v.2
        ∧ (chal_x_queried_gh.get u.2 = false →
            u.1 = v.1 ∧ ∃ y', u.2 = insert_at_chal_x y' v.2)) :=
    fun x y => ProgramDenotation.relE.bind
      (Mid := fun u v : Unit × state => InvUB x y u.2 v.2)
      (ProgramDenotation.relE.loop_n (body_relE ow_adv h_RO h_flag h_cx h_mass x y) q)
      (fun _ _ => final_relE y x y)
  constructor
  · intro F G hFG σ σ' hpre
    cases hpre
    unfold ow_game_1_tracked ow_game_2_tracked lazy_init
    rw [oracle_loop_n_eq_loop_n]
    simp only [wp_set_seq_state, wp_uniform_seq_state]
    refine Finset.sum_le_sum fun x _ => ?_
    refine ENNReal.div_le_div_right ?_ _
    refine Finset.sum_le_sum fun y _ => ?_
    refine ENNReal.div_le_div_right ?_ _
    exact (hTail x y).1 F G hFG _ _ (init_inv x y σ)
  · intro F G hFG σ₂ σ₁ hpre
    cases hpre
    unfold ow_game_1_tracked ow_game_2_tracked lazy_init
    rw [oracle_loop_n_eq_loop_n]
    simp only [wp_set_seq_state, wp_uniform_seq_state]
    refine Finset.sum_le_sum fun x _ => ?_
    refine ENNReal.div_le_div_right ?_ _
    refine Finset.sum_le_sum fun y _ => ?_
    refine ENNReal.div_le_div_right ?_ _
    exact (hTail x y).2 F G hFG _ _ (init_inv x y σ₂)

/-! ## The three theorems of the unary development, as corollaries -/

/-- **Agree-until-bad** (the unary original is the ~110-line private
    `ow_game_1_tracked_eq_ow_game_2_tracked_until_bad` plus its ~390 lines
    of RO-invariance machinery; here it needs the extra mass hypothesis). -/
private theorem ow_game_1_tracked_eq_ow_game_2_tracked_until_bad
    (h_RO : ow_adv.inRange random_oracle_state.compl.range)
    (h_cx : ow_adv.inRange ow_challenge_x.compl.range)
    (h_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_mass : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1)
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
  refine (ow_game_tracked_relE ow_adv h_RO h_cx h_flag h_mass q).wp_eq ?_ rfl
  intro u v hpost
  obtain ⟨hfeq, hgood⟩ := hpost
  by_cases hb : chal_x_queried_gh.get u.2 = true
  · rw [if_pos hb, if_pos (hfeq.symm.trans hb)]
  · have hbf : chal_x_queried_gh.get u.2 = false := by
      revert hb; cases chal_x_queried_gh.get u.2 <;> simp
    obtain ⟨hval, y', hy'⟩ := hgood hbf
    rw [if_neg hb, if_neg (fun hv => hb (hfeq.trans hv))]
    calc G u = G (v.1, insert_at_chal_x y' v.2) := by
          rw [show u = (v.1, insert_at_chal_x y' v.2) from Prod.ext hval hy']
      _ = G v := h_G_RO_inv v y'

/-- **Bad-event probability equality** (the unary original needed a
    138-line mass-conservation + ENNReal-cancellation chain). -/
lemma ow_game_1_tracked_bad_eq_ow_game_2_tracked_bad
    (h_RO : ow_adv.inRange random_oracle_state.compl.range)
    (h_cx : ow_adv.inRange ow_challenge_x.compl.range)
    (h_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_mass : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1)
    (q : ℕ) (σ : state) :
    (ow_game_1_tracked ow_adv q).wp
        (fun bσ : Bool × state =>
          if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
    = (ow_game_2_tracked ow_adv q).wp
        (fun bσ : Bool × state =>
          if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ :=
  ProgramDenotation.relE.bad_eq (bad := fun σ' => chal_x_queried_gh.get σ' = true)
    (ow_game_tracked_relE ow_adv h_RO h_cx h_flag h_mass q)
    (fun _ _ h => by rw [h.1]) σ

/-- **The up-to-bad hop bound**:
    `Pr[G1 : G] ≤ Pr[G2 : G] + Pr[G1 : bad ∧ G]`. -/
theorem ow_game_1_tracked_le_ow_game_2_tracked_plus_bad
    (h_RO : ow_adv.inRange random_oracle_state.compl.range)
    (h_cx : ow_adv.inRange ow_challenge_x.compl.range)
    (h_flag : ow_adv.inRange chal_x_queried_gh.compl.range)
    (h_mass : ∀ σ, ow_adv.wp (fun _ => (1 : ENNReal)) σ = 1)
    (q : ℕ) (G : Bool × state → ENNReal)
    (h_G_RO_inv : ∀ (bσ : Bool × state) (y : output),
       G (bσ.1, insert_at_chal_x y bσ.2) = G bσ)
    (σ : state) :
    (ow_game_1_tracked ow_adv q).wp G σ
    ≤ (ow_game_2_tracked ow_adv q).wp G σ
      + (ow_game_1_tracked ow_adv q).wp
          (fun bσ : Bool × state =>
            if chal_x_queried_gh.get bσ.2 = true then G bσ else 0) σ := by
  refine ProgramDenotation.relE.up_to_bad (bad := fun σ' => chal_x_queried_gh.get σ' = true) G
    (ow_game_tracked_relE ow_adv h_RO h_cx h_flag h_mass q)
    (fun _ _ h => by rw [h.1]) ?_ σ
  intro u v hpost hb
  have hb' : ¬ chal_x_queried_gh.get u.2 = true := hb
  have hbf : chal_x_queried_gh.get u.2 = false := by
    revert hb'; cases chal_x_queried_gh.get u.2 <;> simp
  obtain ⟨hval, y', hy'⟩ := hpost.2 hbf
  calc G u = G (v.1, insert_at_chal_x y' v.2) := by
        rw [show u = (v.1, insert_at_chal_x y' v.2) from Prod.ext hval hy']
    _ = G v := h_G_RO_inv v y'

end UpToBad
