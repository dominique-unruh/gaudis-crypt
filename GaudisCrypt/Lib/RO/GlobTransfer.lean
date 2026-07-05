import GaudisCrypt.Lib.RO.TransferInstantiate
import GaudisCrypt.Lib.RO.ROCouplingEquiv

/-!
# Consuming `={glob A}`: the whole-game coupling from glob-equal initial states

The produce side (`output_glob_transfer_games`, `TransferInstantiate.lean`) starts the
lazy and eager games from **equal** states.  This file relaxes the precondition to
EasyCrypt's `={glob A}` — the initial states need only agree on everything `A` may
touch.

Architecture (chained by `prhl2.trans`):

    G_lazy σ₁  ~[same-program glob rule]~  G_lazy σ₂  ~[produce side, σ₂ = σ₂]~  G_eager σ₂

* `PGlob A` — the invariant threaded through the body induction: `={glob A}` **plus
  equal oracle tables**.  Glob-equality alone is too weak (the per-query coupling
  needs equal tables); the tables conjunct is established by `lazy_init`
  (`lazy_init_coupling_glob`) rather than assumed of the initial states.

* `glob_self_coupling_lazy` — the same-program whole-game rule: from `={glob A}`,
  two runs of the **lazy** game couple with equal results and `={glob A}` finals.
  Assembled from the init coupling and the oracle-generic body machinery
  (`instantiate_of_fvP_gen` at `eagerInst := lazyInst := RO_lazy`, with the
  same-side hole wrapper `ro_hhole_prhl_lazy`).

* `output_glob_transfer_games_of_glob` — the endpoint: `={glob A}` precondition,
  `u.1 = v.1 ∧ ={glob A}` postcondition, lazy vs eager.

One obligation remains a **hypothesis**, to be discharged in a follow-up:

* `hcompat : FootprintCompat (PGlob A) (fvP_proc A)` — the *glob adversary rule*:
  every `A`-confined program self-couples from `PGlob`-related states.  Planned
  proof: per-`EqvGen`-orbit-step map-`f` couplings + `prhl2.trans`, with the tables
  conjunct re-attached from per-leg support facts (`inFootprint_preserves_touched`).

(The other obligation of the skeleton — the same-side per-query coupling — is
discharged: `lazy_query_self_coupling` couples cache hits on the shared cached
value and cache misses diagonally on one uniform sample; unlike the lazy-vs-eager
per-query coupling, the diagonal one is satisfiable and provable.)
-/

namespace GaudisCrypt.Lib.RO.Instantiate

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics
open GaudisCrypt.Language.Programs

/-- The consume-side invariant: agreement on everything `A` may touch (`={glob A}`)
    **plus equal oracle tables**.  The tables conjunct is what makes the per-query
    self-coupling satisfiable; it is established by the initialisation, not assumed
    of the initial states. -/
def PGlob {sig : ProcedureSignature} (A : ProcedureWithHoles roHoles sig) :
    state → state → Prop :=
  fun g₁ g₂ => (FVP.glob A).get g₁ = (FVP.glob A).get g₂
    ∧ random_oracle_state.get g₁ = random_oracle_state.get g₂

/-! ## The per-query self-coupling

`lazy_query` applied is a point mass on a cache hit and a uniform sample + table
write on a miss.  With **equal tables** the two sides take the same branch: a hit
returns the shared cached value; a miss couples the samples diagonally. -/

/-- `ProgramDenotation` bind, applied: the StateT plumbing, definitionally. -/
private lemma bind_apply {α β : Type} (p : ProgramDenotation state α)
    (k : α → ProgramDenotation state β) (σ : state) :
    (p >>= k) σ = p σ >>= fun a => k a.1 a.2 := rfl

/-- `ProgramDenotation.get random_oracle_state`, applied: a point mass on the table. -/
private lemma get_ro_apply (σ : state) :
    (ProgramDenotation.get random_oracle_state
        : ProgramDenotation state (input → Option output)) σ
      = (pure (random_oracle_state.get σ, σ)
          : SubProbability ((input → Option output) × state)) := by
  simp only [ProgramDenotation.get, bind, StateT.bind, StateT.get, pure, StateT.pure,
    AsGetter.toG]
  refine Subtype.ext ?_
  exact MeasureTheory.Measure.dirac_bind measurable_from_top (σ, σ)

/-- `ProgramDenotation.set random_oracle_state Z`, applied: the deterministic write. -/
private lemma set_ro_apply (Z : input → Option output) (σ : state) :
    (ProgramDenotation.set random_oracle_state Z : ProgramDenotation state Unit) σ
      = (pure ((), random_oracle_state.set Z σ) : SubProbability (Unit × state)) := by
  simp only [ProgramDenotation.set, bind, StateT.bind, StateT.get, StateT.set, pure,
    AsSetter.toS]
  refine Subtype.ext ?_
  exact MeasureTheory.Measure.dirac_bind measurable_from_top (σ, σ)

/-- `ProgramDenotation.uniform`, applied: sample, thread the state (definitional). -/
private lemma uniform_apply (σ : state) :
    (ProgramDenotation.uniform : ProgramDenotation state output) σ
      = (SubProbability.uniform : SubProbability output) >>= fun v =>
          (pure (v, σ) : SubProbability (output × state)) := rfl

/-- `lazy_query` applied on a cache **hit**: a point mass, state unchanged. -/
lemma lazy_query_apply_hit (inp : input) {σ : state} {x : output}
    (h : random_oracle_state.get σ inp = some x) :
    lazy_query inp σ = (pure (x, σ) : SubProbability (output × state)) := by
  unfold lazy_query
  rw [bind_apply, get_ro_apply, SubProbability.pure_bind]
  simp only [h]
  rfl

/-- `lazy_query` applied on a cache **miss**: sample uniformly, cache, return. -/
lemma lazy_query_apply_miss (inp : input) {σ : state}
    (h : random_oracle_state.get σ inp = none) :
    lazy_query inp σ
      = (SubProbability.uniform : SubProbability output) >>= fun v =>
          (pure (v, random_oracle_state.set
              (fun x => if x = inp then some v else random_oracle_state.get σ x) σ)
            : SubProbability (output × state)) := by
  unfold lazy_query
  rw [bind_apply, get_ro_apply, SubProbability.pure_bind]
  simp only [h]
  rw [bind_apply, uniform_apply, SubProbability.bind_assoc]
  congr 1; funext v
  rw [SubProbability.pure_bind, bind_apply, set_ro_apply, SubProbability.pure_bind]
  rfl

/-- **Same-side per-query coupling** (generic): for any invariant `P` that implies
    equal oracle tables and is preserved by equal RO writes, two `lazy_query`s
    couple with equal results and `P` preserved. -/
theorem lazy_query_self_coupling {P : state → state → Prop}
    (htab : ∀ σ₁ σ₂, P σ₁ σ₂ → random_oracle_state.get σ₁ = random_oracle_state.get σ₂)
    (hset : ∀ (Z : input → Option output) (σ₁ σ₂ : state), P σ₁ σ₂ →
        P (random_oracle_state.set Z σ₁) (random_oracle_state.set Z σ₂))
    (inp : input) :
    ProgramDenotation.prhl2 P (lazy_query inp) (lazy_query inp) (liftPost P) := by
  intro σ₁ σ₂ hP
  have htabs := htab σ₁ σ₂ hP
  cases hc : random_oracle_state.get σ₁ inp with
  | some x =>
      have hc₂ : random_oracle_state.get σ₂ inp = some x := by rw [← htabs]; exact hc
      refine ⟨pure ((x, σ₁), (x, σ₂)), ?_, ?_, ?_⟩
      · rw [SubProbability.pure_bind, lazy_query_apply_hit inp hc]
      · rw [SubProbability.pure_bind, lazy_query_apply_hit inp hc₂]
      · exact SubProbability.satisfies_pure _ _ ⟨rfl, hP⟩
  | none =>
      have hc₂ : random_oracle_state.get σ₂ inp = none := by rw [← htabs]; exact hc
      refine ⟨(SubProbability.uniform : SubProbability output) >>= fun v =>
          pure ((v, random_oracle_state.set
                  (fun x => if x = inp then some v else random_oracle_state.get σ₁ x) σ₁),
                (v, random_oracle_state.set
                  (fun x => if x = inp then some v else random_oracle_state.get σ₂ x) σ₂)),
          ?_, ?_, ?_⟩
      · rw [SubProbability.bind_assoc, lazy_query_apply_miss inp hc]
        congr 1; funext v
        rw [SubProbability.pure_bind]
      · rw [SubProbability.bind_assoc, lazy_query_apply_miss inp hc₂]
        congr 1; funext v
        rw [SubProbability.pure_bind]
      · refine SubProbability.satisfies_bind _ (fun v _ => ?_)
        refine SubProbability.satisfies_pure _ _ ⟨rfl, ?_⟩
        change P (random_oracle_state.set
            (fun x => if x = inp then some v else random_oracle_state.get σ₁ x) σ₁)
          (random_oracle_state.set
            (fun x => if x = inp then some v else random_oracle_state.get σ₂ x) σ₂)
        rw [show (fun x => if x = inp then some v else random_oracle_state.get σ₂ x)
              = (fun x => if x = inp then some v else random_oracle_state.get σ₁ x) from by
            rw [htabs]]
        exact hset _ σ₁ σ₂ hP

/-- The per-query obligation for `PGlob A`: lazy-vs-lazy queries self-couple —
    tables are equal by the invariant, glob-agreement survives the write
    (`glob_ro_set_invariant`), and the written tables coincide. -/
theorem lazy_query_self_coupling_PGlob {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) (inp : input) :
    ProgramDenotation.prhl2 (PGlob A) (lazy_query inp) (lazy_query inp)
      (liftPost (PGlob A)) :=
  lazy_query_self_coupling (fun _ _ h => h.2)
    (fun _ σ₁ σ₂ h =>
      ⟨by rw [glob_ro_set_invariant A hdisj, glob_ro_set_invariant A hdisj]; exact h.1,
       by rw [random_oracle_state.set_get, random_oracle_state.set_get]⟩)
    inp

/-- Same-side analogue of `ro_hhole_prhl`: the **lazy-vs-lazy** oracle hole preserves
    the invariant, given the per-query self-coupling `h`. -/
theorem ro_hhole_prhl_lazy {P : state → state → Prop} {l : Type}
    (h : ∀ inp : input, ProgramDenotation.prhl2 P (lazy_query inp) (lazy_query inp)
        (liftPost P))
    {sig : ProcedureSignature} (n : HoleIndex roHoles sig)
    (x : Setter sig.ret (ProcedureState l)) (p : Getter sig.ParamType (ProcedureState l))
    (hp : GetOK P p)
    (hx : ∀ ret, ProgramDenotation.prhl2 (liftRel P) (ProgramDenotation.set x ret)
        (ProgramDenotation.set x ret) (liftRelPost P)) :
    ProgramDenotation.prhl2 (liftRel P)
      (programDenotation (StmtWithHoles.call x (RO_lazy n) p))
      (programDenotation (StmtWithHoles.call x (RO_lazy n) p)) (liftRelPost P) := by
  cases n with
  | zero =>
      haveI : Countable roSig.ParamType := inferInstanceAs (Countable input)
      haveI : Countable roSig.ret := inferInstanceAs (Countable output)
      change ProgramDenotation.prhl2 (liftRel P)
          (programDenotation (StmtWithHoles.call x RO_lazy_proc p))
          (programDenotation (StmtWithHoles.call x RO_lazy_proc p)) (liftRelPost P)
      rw [denote_call]
      refine ProgramDenotation.prhl2.bind hp (fun args₁ args₂ => ?_)
      intro σ₁ σ₂ hpre
      obtain ⟨rfl, hrel⟩ := hpre
      refine (ProgramDenotation.prhl2.bind (M := liftRelPost P) ?_ (fun ret₁ ret₂ => ?_)) σ₁ σ₂ hrel
      · -- the zoomed query self-couples (via `prhl2_zoom`)
        rw [procDenotation_RO_lazy]
        exact ProgramDenotation.prhl2.conseq (prhl2_zoom l (h args₁))
          (fun _ _ h => h) (fun _ _ hB => ⟨hB.1.1, hB.1.2, hB.2⟩)
      · -- the write couples (equal results from the middle post)
        intro τ₁ τ₂ hpre2
        obtain ⟨rfl, hrel2⟩ := hpre2
        exact hx ret₁ τ₁ τ₂ hrel2
  | succ m => nomatch m

/-- `lazy_init` applied: the deterministic table reset, as a point mass. -/
lemma lazy_init_apply (σ : state) :
    lazy_init σ
      = (pure ((), random_oracle_state.set (fun _ => none) σ)
          : SubProbability (Unit × state)) :=
  set_ro_apply (fun _ => none) σ

/-- From `={glob A}` initial states, the two `lazy_init`s couple and **establish the
    full invariant**: glob-agreement survives the RO write (`glob_ro_set_invariant`),
    and both tables are reset to `fun _ => none`. -/
theorem lazy_init_coupling_glob {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) :
    ProgramDenotation.prhl2
      (fun σ₁ σ₂ : state => (FVP.glob A).get σ₁ = (FVP.glob A).get σ₂)
      lazy_init lazy_init
      (fun u v : Unit × state => PGlob A u.2 v.2) := by
  intro σ₁ σ₂ hσ
  refine ⟨pure (((), random_oracle_state.set (fun _ => none) σ₁),
           ((), random_oracle_state.set (fun _ => none) σ₂)), ?_, ?_, ?_⟩
  · rw [SubProbability.pure_bind, lazy_init_apply]
  · rw [SubProbability.pure_bind, lazy_init_apply]
  · refine SubProbability.satisfies_pure _ _ ?_
    change PGlob A (random_oracle_state.set (fun _ => none) σ₁)
        (random_oracle_state.set (fun _ => none) σ₂)
    exact ⟨by rw [glob_ro_set_invariant A hdisj, glob_ro_set_invariant A hdisj]; exact hσ,
           by rw [random_oracle_state.set_get, random_oracle_state.set_get]⟩

/-- **The same-program whole-game glob rule** (lazy side): from `={glob A}` initial
    states, two runs of the lazy game couple with equal results and `={glob A}` final
    states.  `lazy_init` establishes `PGlob A`; the body preserves it via the
    oracle-generic machinery at `eagerInst := lazyInst := RO_lazy`. -/
theorem glob_self_coupling_lazy {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ)
    (hcompat : FootprintCompat (PGlob A) (fvP_proc A)) :
    ProgramDenotation.prhl2
      (fun σ₁ σ₂ : state => (FVP.glob A).get σ₁ = (FVP.glob A).get σ₂)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (fun u v => u.1 = v.1 ∧ (FVP.glob A).get u.2 = (FVP.glob A).get v.2) := by
  have hbody : ProgramDenotation.prhl2 (PGlob A)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (procedureDenotation (A.instantiate RO_lazy) args) (liftPost (PGlob A)) :=
    instantiate_of_fvP_gen RO_lazy RO_lazy A args hcompat roHole_paramType_countable
      (fun n x p hp hx =>
        ro_hhole_prhl_lazy (lazy_query_self_coupling_PGlob A hdisj) n x p hp hx)
  exact ProgramDenotation.prhl2.conseq
    (ProgramDenotation.prhl2.bind (lazy_init_coupling_glob A hdisj) (fun _ _ => hbody))
    (fun _ _ h => h) (fun u v h => ⟨h.1, h.2.1⟩)

/-- **The endpoint — `={glob A}` consumed and produced.**  From initial states that
    agree on everything `A` may touch, the lazy and eager whole games couple with
    equal results and `={glob A}` final states.  Chains the same-program glob rule
    (`glob_self_coupling_lazy`, taking `σ₁` to `σ₂` on the lazy side) with the
    produce-side coupling (`output_glob_transfer_games`, lazy to eager at `σ₂`) by
    `prhl2.trans`. -/
theorem output_glob_transfer_games_of_glob {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ)
    (hcompat : FootprintCompat (PGlob A) (fvP_proc A)) :
    ProgramDenotation.prhl2
      (fun σ₁ σ₂ : state => (FVP.glob A).get σ₁ = (FVP.glob A).get σ₂)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (do random_oracle_init; procedureDenotation (A.instantiate RO_eager) args)
      (fun u v => u.1 = v.1 ∧ (FVP.glob A).get u.2 = (FVP.glob A).get v.2) := by
  have h12 := ProgramDenotation.prhl2.trans
    (glob_self_coupling_lazy A args hdisj hcompat)
    (output_glob_transfer_games A args hdisj)
  refine h12.conseq (fun σ₁ σ₃ h => ⟨σ₃, h, rfl⟩) ?_
  rintro u v ⟨w, hw1, hw2⟩
  exact ⟨hw1.1.trans hw2.1, hw1.2.trans hw2.2⟩

/-- `Win`-form of the endpoint: any event decided by `A`'s output transfers between
    the lazy and eager games from `={glob A}` initial states, with `={glob A}` final
    states. -/
theorem output_win_transfer_games_of_glob {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType) (Win : sig.ret → Prop)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ)
    (hcompat : FootprintCompat (PGlob A) (fvP_proc A)) :
    ProgramDenotation.prhl2
      (fun σ₁ σ₂ : state => (FVP.glob A).get σ₁ = (FVP.glob A).get σ₂)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (do random_oracle_init; procedureDenotation (A.instantiate RO_eager) args)
      (fun u v => (Win u.1 ↔ Win v.1) ∧ (FVP.glob A).get u.2 = (FVP.glob A).get v.2) :=
  (output_glob_transfer_games_of_glob A args hdisj hcompat).conseq
    (fun _ _ h => h) (fun _ _ h => ⟨by rw [h.1], h.2⟩)

end GaudisCrypt.Lib.RO.Instantiate
