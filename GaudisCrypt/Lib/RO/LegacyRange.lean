import GaudisCrypt.ProgramRange
import GaudisCrypt.Lib.RO.ROEquiv

open GaudisCrypt
open GaudisCrypt

/-!
# Legacy `DetermFootprint`/`inRange` compatibility layer — **quarantined**

The RO framework proper (`Basic`/`TransferConvert`/`OracleLoop`/`ROEquiv`) is on the
probabilistic `Footprint`/`inFootprint` API.  This file collects the deterministic-range
(`DetermFootprint`, `ProgramRange.lean`) duals that `QueryHit.lean` still consumes, so that
the framework files no longer import the quarantined `ProgramRange`.  New code should use
the `inFootprint` analogues that live next to the original locations of these lemmas.
Delete this file once `QueryHit.lean` is migrated.
-/

/-- `lazy_query` only reads and writes `random_oracle_state`. -/
theorem lazy_query_inRange_ro (inp : input) :
    (lazy_query inp).inRange random_oracle_state.range := by
  refine ProgramDenotation.inRange_bind (ProgramDenotation.inRange_get _) ?_
  intro h
  cases h inp with
  | some x => exact ProgramDenotation.inRange_pure _ _
  | none =>
    refine ProgramDenotation.inRange_bind ?_ ?_
    · exact ProgramDenotation.inRange_mono ProgramDenotation.inRange_uniform bot_le
    · intro value
      refine ProgramDenotation.inRange_bind (ProgramDenotation.inRange_set _ _) ?_
      intro _
      exact ProgramDenotation.inRange_pure _ _

/-- `convert` only reads and writes `random_oracle_state` (modulo a uniform sample). -/
theorem convert_inRange_ro : convert.inRange random_oracle_state.range := by
  show ((ProgramDenotation.get random_oracle_state) >>= fun h =>
          (ProgramDenotation.uniform : ProgramDenotation state (input → output)) >>= fun y =>
            ProgramDenotation.set random_oracle_state (fun x => some ((h x).getD (y x)))).inRange _
  refine ProgramDenotation.inRange_bind (ProgramDenotation.inRange_get _) ?_
  intro _
  refine ProgramDenotation.inRange_bind ?_ ?_
  · exact ProgramDenotation.inRange_mono ProgramDenotation.inRange_uniform bot_le
  · intro _
    exact ProgramDenotation.inRange_set _ _

/-- `(lazy_query inp >>= set oracle_output)` is in `L.compl.range` for any
    lens `L` disjoint from both `random_oracle_state` and `oracle_output`.
    Useful for `wp_strengthen_lens_preserved` arguments downstream. -/
lemma lazy_query_then_set_oracle_output_inRange_compl
    {γ : Type} (L : Lens γ state)
    [disjoint random_oracle_state L]
    [disjoint oracle_output L]
    (inp : input) :
    (lazy_query inp >>= fun y => ProgramDenotation.set oracle_output y).inRange
        L.compl.range := by
  refine ProgramDenotation.inRange_bind ?_ ?_
  · exact ProgramDenotation.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state L)
  · intro y
    exact ProgramDenotation.set_inRange_compl_of_disjoint oracle_output L _

/-- Generic preservation: `oracle_step adv` stays in `L.compl.range` for any
    lens `L` disjoint from `random_oracle_state`, `oracle_input`, and
    `oracle_output`, provided the adversary stays in `L.compl.range`. -/
lemma oracle_step_inRange_compl {γ : Type} (L : Lens γ state)
    [disjoint random_oracle_state L]
    [disjoint oracle_input L]
    [disjoint oracle_output L]
    {adv : ProgramDenotation state Unit}
    (h_adv : adv.inRange L.compl.range) :
    (oracle_step adv lazy_query).inRange L.compl.range := by
  show (adv >>= fun _ =>
        ProgramDenotation.get oracle_input >>= fun inp =>
          lazy_query inp >>= fun y =>
            ProgramDenotation.set oracle_output y).inRange L.compl.range
  refine ProgramDenotation.inRange_bind h_adv ?_
  intro _
  refine ProgramDenotation.inRange_bind
    (ProgramDenotation.get_inRange_compl_of_disjoint oracle_input L) ?_
  intro inp
  exact lazy_query_then_set_oracle_output_inRange_compl L inp

/-- Generic preservation lifted to the loop, by induction on `q`. -/
lemma oracle_loop_n_inRange_compl {γ : Type} (L : Lens γ state)
    [disjoint random_oracle_state L]
    [disjoint oracle_input L]
    [disjoint oracle_output L]
    {adv : ProgramDenotation state Unit}
    (h_adv : adv.inRange L.compl.range)
    (q : ℕ) :
    (oracle_loop_n adv q lazy_query).inRange L.compl.range := by
  induction q with
  | zero => exact ProgramDenotation.inRange_pure _ _
  | succ n ih =>
    show (oracle_step adv lazy_query >>= fun _ =>
          oracle_loop_n adv n lazy_query).inRange _
    exact ProgramDenotation.inRange_bind (oracle_step_inRange_compl L h_adv) (fun _ => ih)

/-- **Form (b) — `ProgramDenotation.glob` projection** (legacy `DetermFootprint` endpoint).
    Needs both hypotheses: the footprint one drives the marginal equivalence, the legacy
    `inRange` one drives the `glob`-projection invariance (`glob` is built on
    `ProgramDenotation.range`).** The joint distribution of
    (adv's bit, what `adv` can see/modify) is identical under lazy and
    eager. Specialisation via `(ProgramDenotation.glob adv).get`. -/
theorem oracle_loop_marginal_lazy_eq_random_oracle_glob
    (adv : ProgramDenotation state Unit)
    (h_adv : adv.inFootprint (random_oracle_state.footprint)ᶜ)
    (h_adv_range : adv.inRange random_oracle_state.compl.range) (σ₀ : state) :
    (oracle_loop adv lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state =>
          (Pure.pure (bσ.1, (ProgramDenotation.glob adv).get bσ.2) :
            SubProbability (Bool × adv.Globals)))
    =
    (oracle_loop adv random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state =>
          (Pure.pure (bσ.1, (ProgramDenotation.glob adv).get bσ.2) :
            SubProbability (Bool × adv.Globals))) := by
  refine oracle_loop_marginal_lazy_eq_random_oracle adv h_adv
    (ProgramDenotation.glob adv).get ?_ σ₀
  intro σ x
  apply Quotient.sound
  change Relation.EqvGen
      (fun s s' : state => ∃ f ∈ ((adv.range)ᶜ : DetermFootprint state).updates, f s = s')
      (random_oracle_state.set x σ) σ
  apply Relation.EqvGen.symm
  apply Relation.EqvGen.rel
  refine ⟨random_oracle_state.set x, ?_, rfl⟩
  have h_in_ro : random_oracle_state.set x ∈ random_oracle_state.range.updates := by
    refine ⟨Function.const _ x, Set.mem_univ _, ?_⟩
    funext σ'
    simp [Lens.liftFunction]
  have hadv_le : adv.range ≤ random_oracle_state.compl.range :=
    sInf_le h_adv_range
  have h_le : random_oracle_state.range ≤ (adv.range)ᶜ := by
    have hflip : (random_oracle_state.compl.range)ᶜ ≤ (adv.range)ᶜ := by
      change (Submonoid.centralizer random_oracle_state.compl.range.updates).carrier
           ⊆ (Submonoid.centralizer adv.range.updates).carrier
      exact Submonoid.centralizer_le hadv_le
    rwa [DetermFootprint.complement_range, DetermFootprint.compl_compl] at hflip
  exact h_le h_in_ro
