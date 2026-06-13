import GaudisCrypt.Lib.RO.CollisionResistance

/-!
# PRP/PRF switching lemma — oracles and the shared bad flag (Phase 1)

Infrastructure for the information-theoretic switching lemma
`|Pr[A^RF] − Pr[A^RP]| ≤ q(q−1)/2N`, set up for the up-to-bad (Fundamental
Lemma) argument in the relational calculus.

The two oracles are *identical until bad*: both draw the **same** underlying
uniform value `y` on a cache miss and set the shared flag `prp_bad` to `true`
iff `y` already occurs in the oracle's image (a collision). On no collision
both behave identically (cache `y`); on a collision `RF` keeps `y` (with
replacement) while `RP` resamples a fresh value from the unused outputs
(without replacement). Because the flag is set from the same draw against the
same image, it agrees on both sides — exactly what `relE.up_to_bad` needs.

* `prp_bad : Variable Bool` — the shared "a collision has occurred" flag.
* `colliding_outputs h inp` — outputs already used by inputs other than `inp`
  (the values a fresh draw at `inp` would collide with). Equal to
  `inducing_set inp σ` when `h = random_oracle_state.get σ`.
* `lazy_query_rf` / `lazy_query_rp` — the RF and RP oracles.
* `lazy_query_rf_inRange` / `lazy_query_rp_inRange` — both touch only
  `random_oracle_state` and `prp_bad`.

This is **Phase 1** of the plan; the per-query coupling (Phase 2) and the
Fundamental-Lemma assembly (Phases 3–4) build on these definitions.
-/

/-- Shared "a collision has occurred" flag for the switching coupling. Set to
    `true` the first time a freshly drawn output already appears in the image;
    both `lazy_query_rf` and `lazy_query_rp` maintain it identically. -/
axiom prp_bad : Variable Bool

axiom disjoint_prp_bad_ro : disjoint prp_bad random_oracle_state
axiom disjoint_prp_bad_oracle_input : disjoint prp_bad oracle_input
axiom disjoint_prp_bad_oracle_output : disjoint prp_bad oracle_output

attribute [instance] disjoint_prp_bad_ro
                     disjoint_prp_bad_oracle_input
                     disjoint_prp_bad_oracle_output

/-- Symmetric instances. -/
instance : disjoint random_oracle_state prp_bad := disjoint_prp_bad_ro.symm
instance : disjoint oracle_input prp_bad := disjoint_prp_bad_oracle_input.symm
instance : disjoint oracle_output prp_bad := disjoint_prp_bad_oracle_output.symm

/-- The symmetric forms of the OracleLoop RO-disjointness axioms, needed to
    frame the RO read/write inside the oracles against the scratch lenses. -/
instance : disjoint random_oracle_state oracle_input := disjoint_oracle_input_ro.symm
instance : disjoint random_oracle_state oracle_output := disjoint_oracle_output_ro.symm

/-- Outputs already assigned to some input *other than* `inp` — i.e. the values
    a fresh draw at `inp` would collide with, and (when `inp` is uncached) the
    set `RP` must avoid to stay injective. Definitionally equal to
    `inducing_set inp σ` when `h = random_oracle_state.get σ`. -/
noncomputable def colliding_outputs (h : input → Option output) (inp : input) :
    Finset output :=
  ((Finset.univ.erase inp).filter (fun x' => (h x').isSome)).image
    (fun x' => (h x').getD default)

/-- **RF oracle (instrumented).** Acts exactly like `lazy_query` on the RO
    state, additionally setting `prp_bad := true` when the freshly drawn value
    already occurs in the image (the draw creates a collision). Written with
    explicit `>>=` to avoid the do-notation join-point macro on the `if`. -/
noncomputable def lazy_query_rf (inp : input) : Program state output :=
  Program.get random_oracle_state >>= fun h =>
    match h inp with
    | some x => (pure x : Program state output)
    | none =>
      Program.uniform >>= fun y =>
        (if y ∈ colliding_outputs h inp then Program.set prp_bad true
         else (pure () : Program state Unit)) >>= fun _ =>
          Program.set random_oracle_state (fun x => if x = inp then some y else h x)
            >>= fun _ => (pure y : Program state output)

/-- **RP oracle (instrumented, resample-on-collision).** Draws the *same* `y`
    and sets `prp_bad` on a collision exactly as `lazy_query_rf`. On a collision
    it resamples uniformly from the unused outputs (`univ \ colliding_outputs`),
    keeping the oracle injective; if the outputs are exhausted it falls through
    (the flag is already set, so the returned value is immaterial). -/
noncomputable def lazy_query_rp (inp : input) : Program state output :=
  Program.get random_oracle_state >>= fun h =>
    match h inp with
    | some x => (pure x : Program state output)
    | none =>
      Program.uniform >>= fun y =>
        if y ∈ colliding_outputs h inp then
          Program.set prp_bad true >>= fun _ =>
            (if hne : (Finset.univ \ colliding_outputs h inp).Nonempty then
               Program.uniformOfFinset (Finset.univ \ colliding_outputs h inp) hne
             else (pure y : Program state output)) >>= fun y' =>
              Program.set random_oracle_state (fun x => if x = inp then some y' else h x)
                >>= fun _ => (pure y' : Program state output)
        else
          Program.set random_oracle_state (fun x => if x = inp then some y else h x)
            >>= fun _ => (pure y : Program state output)

/-- `lazy_query_rf` touches only `random_oracle_state` and `prp_bad`: it lives in
    the complement of any lens disjoint from both. -/
lemma lazy_query_rf_inRange {α : Type} (L : Variable α)
    [disjoint random_oracle_state L] [disjoint prp_bad L] (inp : input) :
    (lazy_query_rf inp).inRange L.compl.range := by
  unfold lazy_query_rf
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint random_oracle_state L) (fun h => ?_)
  cases h inp with
  | some x => exact Program.inRange_pure _ _
  | none =>
    refine Program.inRange_bind
      (Program.inRange_mono Program.inRange_uniform bot_le) (fun y => ?_)
    refine Program.inRange_bind ?_ (fun _ => ?_)
    · by_cases hy : y ∈ colliding_outputs h inp
      · simp only [if_pos hy]
        exact Program.set_inRange_compl_of_disjoint prp_bad L true
      · simp only [if_neg hy]
        exact Program.inRange_pure _ _
    · exact Program.inRange_bind
        (Program.set_inRange_compl_of_disjoint random_oracle_state L _)
        (fun _ => Program.inRange_pure _ _)

/-- `lazy_query_rp` touches only `random_oracle_state` and `prp_bad`. -/
lemma lazy_query_rp_inRange {α : Type} (L : Variable α)
    [disjoint random_oracle_state L] [disjoint prp_bad L] (inp : input) :
    (lazy_query_rp inp).inRange L.compl.range := by
  unfold lazy_query_rp
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint random_oracle_state L) (fun h => ?_)
  cases h inp with
  | some x => exact Program.inRange_pure _ _
  | none =>
    refine Program.inRange_bind
      (Program.inRange_mono Program.inRange_uniform bot_le) (fun y => ?_)
    by_cases hy : y ∈ colliding_outputs h inp
    · simp only [if_pos hy]
      refine Program.inRange_bind
        (Program.set_inRange_compl_of_disjoint prp_bad L true) (fun _ => ?_)
      refine Program.inRange_bind ?_ (fun y' => ?_)
      · by_cases hne : (Finset.univ \ colliding_outputs h inp).Nonempty
        · simp only [dif_pos hne]
          exact Program.inRange_mono (Program.inRange_uniformOfFinset _ hne) bot_le
        · simp only [dif_neg hne]
          exact Program.inRange_pure _ _
      · exact Program.inRange_bind
          (Program.set_inRange_compl_of_disjoint random_oracle_state L _)
          (fun _ => Program.inRange_pure _ _)
    · simp only [if_neg hy]
      exact Program.inRange_bind
        (Program.set_inRange_compl_of_disjoint random_oracle_state L _)
        (fun _ => Program.inRange_pure _ _)
