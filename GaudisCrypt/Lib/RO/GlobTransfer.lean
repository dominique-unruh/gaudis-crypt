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

Both obligations of the original skeleton are discharged, so the endpoint needs
**only** the footprint disjointness `hdisj`:

* the same-side per-query coupling (`lazy_query_self_coupling`) — cache hits agree
  on the shared cached value, cache misses couple the samples diagonally; and

* the *glob adversary rule* (`footprintCompat_PGlob`) — every `A`-confined program
  self-couples from `PGlob`-related states, via per-orbit-step map-`f` couplings
  (`inFootprint_subprob`) chained by `prhl2.refl/symm/trans`
  (`prhl2_self_of_orbit`), the reduce/lift bridge
  (`lifted_step_mem_fvP_proc_compl`), and per-leg table preservation re-attached
  through the coupling marginals.
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

/-! ## The glob adversary rule: `FootprintCompat (PGlob A) (fvP_proc A)`

An `A`-confined program self-couples from `PGlob`-related states.  The glob-equality
precondition is an orbit fact — the two global states are joined by a zig-zag of
`(FVP.fvP_proc A)ᶜ`-updates (`Quotient.exact`).  Each such update, lifted through
`globalL` (fixing the locals), commutes with everything `A` may touch as a procedure
(`lifted_step_mem_fvP_proc_compl`, via the reduce/lift algebra), so a confined `p`
maps one leg onto the other pointwise (`inFootprint_subprob`), giving a per-step
coupling; `prhl2.refl/symm/trans` chain the zig-zag (`prhl2_self_of_orbit`).  The
final states remain in a lifted orbit — equal locals and `={glob A}` globals
(`glob_locals_of_lifted_orbit`) — while the tables conjunct is re-attached from the
per-leg supports (`inFootprint_preserves_touched` through the coupling marginals). -/

/-- A `satisfies` of the first marginal holds on the coupling's support. -/
private lemma coupling_satisfies_fst {γ δ : Type} {μ : SubProbability (γ × δ)}
    {B : γ → Prop}
    (h : (μ >>= fun x => (pure x.1 : SubProbability γ)).satisfies B) :
    μ.satisfies (fun x => B x.1) := by
  intro x hx
  apply h x.1
  rw [SubProbability.marginal_fst_singleton]
  have hle : μ.1 {(x.1, x.2)} ≤ ∑' b, μ.1 {(x.1, b)} := ENNReal.le_tsum x.2
  intro h0
  rw [h0] at hle
  exact hx (le_antisymm hle zero_le)

/-- A `satisfies` of the second marginal holds on the coupling's support. -/
private lemma coupling_satisfies_snd {γ δ : Type} {μ : SubProbability (γ × δ)}
    {B : δ → Prop}
    (h : (μ >>= fun x => (pure x.2 : SubProbability δ)).satisfies B) :
    μ.satisfies (fun x => B x.2) := by
  intro x hx
  apply h x.2
  rw [SubProbability.marginal_snd_singleton]
  have hle : μ.1 {(x.1, x.2)} ≤ ∑' a, μ.1 {(a, x.2)} := ENNReal.le_tsum x.1
  intro h0
  rw [h0] at hle
  exact hx (le_antisymm hle zero_le)

/-- **Self-coupling along an orbit of confined-complement updates.**  A program confined
    to `F` couples with itself across any zig-zag of updates from `U ⊆ Fᶜ`: each step is
    mapped through `p` pointwise (`inFootprint_subprob`), and `prhl2.refl/symm/trans`
    compose the zig-zag.  The coupled final states are again `U`-orbit-related. -/
theorem prhl2_self_of_orbit {s γ : Type} {F : Footprint s} {p : ProgramDenotation s γ}
    (hp : p.inFootprint F) (U : Set (Function.End s))
    (hU : ∀ f ∈ U, diracKer f ∈ (Fᶜ).updates) :
    ProgramDenotation.prhl2
      (Relation.EqvGen fun a b => ∃ f ∈ U, f a = b) p p
      (fun u v => u.1 = v.1 ∧ Relation.EqvGen (fun a b => ∃ f ∈ U, f a = b) u.2 v.2) := by
  intro σ₁ σ₂ horb
  suffices hJ : ProgramDenotation.prhl2 (fun x y => x = σ₁ ∧ y = σ₂) p p
      (fun u v => u.1 = v.1 ∧ Relation.EqvGen (fun a b => ∃ f ∈ U, f a = b) u.2 v.2) from
    hJ σ₁ σ₂ ⟨rfl, rfl⟩
  induction horb with
  | rel a b hab =>
      intro x y hxy
      rw [hxy.1, hxy.2]
      obtain ⟨f, hfU, hfab⟩ := hab
      refine ⟨p a >>= fun w => pure (w, (w.1, f w.2)), ?_, ?_, ?_⟩
      · rw [SubProbability.bind_assoc]
        have hinner : ∀ w : γ × s,
            ((pure (w, (w.1, f w.2)) : SubProbability ((γ × s) × (γ × s))) >>= fun z =>
              (pure z.1 : SubProbability (γ × s))) = pure w := by
          intro w; rw [SubProbability.pure_bind]
        simp only [hinner]
        exact SubProbability.bind_pure _
      · rw [SubProbability.bind_assoc]
        have hinner : ∀ w : γ × s,
            ((pure (w, (w.1, f w.2)) : SubProbability ((γ × s) × (γ × s))) >>= fun z =>
              (pure z.2 : SubProbability (γ × s))) = pure (w.1, f w.2) := by
          intro w; rw [SubProbability.pure_bind]
        simp only [hinner]
        rw [← hfab]
        exact (inFootprint_subprob hp (hU f hfU) a).symm
      · refine SubProbability.satisfies_bind _ (fun w _ => ?_)
        exact SubProbability.satisfies_pure _ _
          ⟨rfl, Relation.EqvGen.rel _ _ ⟨f, hfU, rfl⟩⟩
        -- (the recorded step is `f w.2 = f w.2`)
  | refl a =>
      intro x y hxy
      rw [hxy.1, hxy.2]
      refine ⟨p a >>= fun w => pure (w, w), ?_, ?_, ?_⟩
      · rw [SubProbability.bind_assoc]
        have hinner : ∀ w : γ × s,
            ((pure (w, w) : SubProbability ((γ × s) × (γ × s))) >>= fun z =>
              (pure z.1 : SubProbability (γ × s))) = pure w := by
          intro w; rw [SubProbability.pure_bind]
        simp only [hinner]
        exact SubProbability.bind_pure _
      · rw [SubProbability.bind_assoc]
        have hinner : ∀ w : γ × s,
            ((pure (w, w) : SubProbability ((γ × s) × (γ × s))) >>= fun z =>
              (pure z.2 : SubProbability (γ × s))) = pure w := by
          intro w; rw [SubProbability.pure_bind]
        simp only [hinner]
        exact SubProbability.bind_pure _
      · refine SubProbability.satisfies_bind _ (fun w _ => ?_)
        exact SubProbability.satisfies_pure _ _ ⟨rfl, Relation.EqvGen.refl _⟩
  | symm a b _ ih =>
      exact (ProgramDenotation.prhl2.symm ih).conseq
        (fun x y h => ⟨h.2, h.1⟩)
        (fun v u h => ⟨h.1.symm, Relation.EqvGen.symm _ _ h.2⟩)
  | trans a b c _ _ ih₁ ih₂ =>
      exact (ProgramDenotation.prhl2.trans ih₁ ih₂).conseq
        (fun x y h => ⟨b, ⟨h.1, rfl⟩, rfl, h.2⟩)
        (fun u v h => by
          obtain ⟨w, hw1, hw2⟩ := h
          exact ⟨hw1.1.trans hw2.1, Relation.EqvGen.trans _ _ _ hw1.2 hw2.2⟩)

/-- The update set driving the orbit coupling: global `(FVP.fvP_proc A)ᶜ`-updates lifted
    through `globalL` (fixing the locals). -/
def liftedGlobSteps {sig : ProcedureSignature} (A : ProcedureWithHoles roHoles sig)
    (l : Type) : Set (Function.End (ProcedureState l)) :=
  { fp | ∃ f : Function.End state,
      diracKer f ∈ ((FVP.fvP_proc A)ᶜ).updates ∧
      fp = (ProcedureState.globalL (l := l)).liftFunction f }

/-- **The bridge**: a global update commuting with everything `A` may touch globally
    (`(FVP.fvP_proc A)ᶜ`), lifted through `globalL`, commutes with everything `A` may
    touch as a procedure (`(fvP_proc A)ᶜ`).  Both `fvP_proc`s decompose (definitionally)
    into body ⊔ return, with the global one the `globalL`-reduction of the procedure one;
    per component the commutation transfers by `liftSubProbability_comm_of_mem_reduce_compl`. -/
theorem lifted_step_mem_fvP_proc_compl {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) {f : Function.End state}
    (hf : diracKer f ∈ ((FVP.fvP_proc A)ᶜ).updates) :
    diracKer ((ProcedureState.globalL
        (l := sig.LocalVariableState A.locals)).liftFunction f)
      ∈ ((fvP_proc A)ᶜ).updates := by
  have hdecompG : FVP.fvP_proc A
      = fvP_reduce ProcedureState.globalL (FVP.fvP_stmt A.body) ⊔
        fvP_reduce ProcedureState.globalL
          ((ProgramDenotation.get A.return_val).footprint) := rfl
  -- Per component: `X ≤ (from {lifted step})ᶜ` whenever `f` commutes with `X`'s reduction.
  have hsing : ∀ X : Footprint (ProcedureState (sig.LocalVariableState A.locals)),
      diracKer f ∈ ((fvP_reduce ProcedureState.globalL X)ᶜ).updates →
      X ≤ (Footprint.from
        {diracKer ((ProcedureState.globalL
          (l := sig.LocalVariableState A.locals)).liftFunction f)})ᶜ := by
    intro X hfX
    rw [← Footprint.le_compl_comm]
    refine (Footprint.from_le_iff _ _).mpr ?_
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    rw [← FVP.updateK_diracKer]
    change ProcedureState.globalL.liftSubProbability (diracKer f)
        ∈ Submonoid.centralizer X.updates
    rw [Submonoid.mem_centralizer_iff]
    intro k hk
    exact (liftSubProbability_comm_of_mem_reduce_compl hfX hk).symm
  -- Transport `hf` to the two components of the global decomposition.
  have hble : fvP_reduce ProcedureState.globalL (FVP.fvP_stmt A.body) ≤ FVP.fvP_proc A := by
    rw [hdecompG]; exact le_sup_left
  have hrle : fvP_reduce ProcedureState.globalL
      ((ProgramDenotation.get A.return_val).footprint) ≤ FVP.fvP_proc A := by
    rw [hdecompG]; exact le_sup_right
  have h1 := le_trans (fvP_stmt_le_FVP A.body)
    (hsing _ (Footprint.compl_le_compl hble hf))
  have h2 := hsing _ (Footprint.compl_le_compl hrle hf)
  -- Reassemble at the procedure level.
  have hsup : fvP_proc A ≤ (Footprint.from
      {diracKer ((ProcedureState.globalL
        (l := sig.LocalVariableState A.locals)).liftFunction f)})ᶜ := by
    exact sup_le h1 h2
  exact (Footprint.from_le_iff _ _).mp
    ((Footprint.le_compl_comm _ _).mpr hsup) (Set.mem_singleton _)

/-- **Pre-transport**: a global `(FVP.fvP_proc A)ᶜ`-orbit lifts to a `liftedGlobSteps`
    orbit of procedure states with any fixed locals. -/
lemma lifted_orbit_of_global {sig : ProcedureSignature} (A : ProcedureWithHoles roHoles sig)
    {l : Type} (loc : l) {g₁ g₂ : state}
    (h : Relation.EqvGen (fun a b : state => ∃ f : Function.End state,
        diracKer f ∈ ((FVP.fvP_proc A)ᶜ).updates ∧ f a = b) g₁ g₂) :
    Relation.EqvGen (fun a b => ∃ fp ∈ liftedGlobSteps A l, fp a = b)
      (⟨g₁, loc⟩ : ProcedureState l) ⟨g₂, loc⟩ := by
  induction h with
  | rel a b hab =>
      obtain ⟨f, hf, rfl⟩ := hab
      exact Relation.EqvGen.rel _ _
        ⟨(ProcedureState.globalL (l := l)).liftFunction f, ⟨f, hf, rfl⟩, rfl⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- **Post-transport**: `liftedGlobSteps`-orbit-related procedure states have equal locals
    and `={glob A}` globals (each step fixes the locals and is invisible to `glob A`). -/
lemma glob_locals_of_lifted_orbit {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) {l : Type} {x y : ProcedureState l}
    (h : Relation.EqvGen (fun a b => ∃ fp ∈ liftedGlobSteps A l, fp a = b) x y) :
    (FVP.glob A).get x.global = (FVP.glob A).get y.global ∧ x.locals = y.locals := by
  induction h with
  | rel a b hab =>
      obtain ⟨fp, ⟨f, hf, rfl⟩, rfl⟩ := hab
      exact ⟨(Footprint.touched_getter_get_eq_of_mem hf a.global).symm, rfl⟩
  | refl a => exact ⟨rfl, rfl⟩
  | symm a b _ ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | trans a b c _ _ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1, ih₁.2.trans ih₂.2⟩

/-- **The glob adversary rule**: every program confined to `fvP_proc A` self-couples
    from `PGlob A`-related states — the last obligation of the consume-side endpoint. -/
theorem footprintCompat_PGlob {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) :
    FootprintCompat (PGlob A) (fvP_proc A) := by
  intro γ p hp ps₁ ps₂ hpre
  obtain ⟨⟨hglob, htab⟩, hloc⟩ := hpre
  -- The lifted-orbit pre, from `={glob A}` + equal locals.
  have horbG : Relation.EqvGen (fun a b : state => ∃ f : Function.End state,
      diracKer f ∈ ((FVP.fvP_proc A)ᶜ).updates ∧ f a = b) ps₁.global ps₂.global :=
    Quotient.exact hglob
  have horb : Relation.EqvGen
      (fun a b => ∃ fp ∈ liftedGlobSteps A (sig.LocalVariableState A.locals), fp a = b)
      ps₁ ps₂ := by
    have h0 := lifted_orbit_of_global A ps₁.locals horbG
    have h1 : (⟨ps₂.global, ps₁.locals⟩
        : ProcedureState (sig.LocalVariableState A.locals)) = ps₂ := by
      rw [hloc]
    exact h1 ▸ h0
  -- The orbit coupling.
  have hU : ∀ fp ∈ liftedGlobSteps A (sig.LocalVariableState A.locals),
      diracKer fp ∈ ((fvP_proc A)ᶜ).updates := by
    rintro fp ⟨f, hf, rfl⟩
    exact lifted_step_mem_fvP_proc_compl A hf
  obtain ⟨μ, hm1, hm2, hsat⟩ := prhl2_self_of_orbit hp _ hU ps₁ ps₂ horb
  -- Per-leg table preservation, lifted onto the coupling's support.
  have hSle : (roLift (sig.LocalVariableState A.locals)).footprint ≤ (fvP_proc A)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (fvP_proc_le_roLift_compl A hdisj)
  have htabLeg : ∀ ps : ProcedureState (sig.LocalVariableState A.locals),
      (p ps).satisfies (fun xs =>
        random_oracle_state.get xs.2.global = random_oracle_state.get ps.global) := by
    intro ps xs hxs
    have h' := (Lens.footprint_touched_getter_eq_iff _ _ _).mp
      (inFootprint_preserves_touched hp hSle (Lens.footprint_hasReset _ ps) xs hxs)
    rwa [roLift_get_global, roLift_get_global] at h'
  have hμ₁ : μ.satisfies (fun w =>
      random_oracle_state.get w.1.2.global = random_oracle_state.get ps₁.global) :=
    coupling_satisfies_fst (by rw [hm1]; exact htabLeg ps₁)
  have hμ₂ : μ.satisfies (fun w =>
      random_oracle_state.get w.2.2.global = random_oracle_state.get ps₂.global) :=
    coupling_satisfies_snd (by rw [hm2]; exact htabLeg ps₂)
  refine ⟨μ, hm1, hm2, ?_⟩
  intro w hw
  obtain ⟨hres, horbw⟩ := hsat w hw
  have hgl := glob_locals_of_lifted_orbit A horbw
  refine ⟨hres, ⟨hgl.1, ?_⟩, hgl.2⟩
  rw [hμ₁ w hw, hμ₂ w hw]
  exact htab

/-- **The same-program whole-game glob rule** (lazy side): from `={glob A}` initial
    states, two runs of the lazy game couple with equal results and `={glob A}` final
    states.  `lazy_init` establishes `PGlob A`; the body preserves it via the
    oracle-generic machinery at `eagerInst := lazyInst := RO_lazy`. -/
theorem glob_self_coupling_lazy {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) :
    ProgramDenotation.prhl2
      (fun σ₁ σ₂ : state => (FVP.glob A).get σ₁ = (FVP.glob A).get σ₂)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (fun u v => u.1 = v.1 ∧ (FVP.glob A).get u.2 = (FVP.glob A).get v.2) := by
  have hbody : ProgramDenotation.prhl2 (PGlob A)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (procedureDenotation (A.instantiate RO_lazy) args) (liftPost (PGlob A)) :=
    instantiate_of_fvP_gen RO_lazy RO_lazy A args (footprintCompat_PGlob A hdisj)
      roHole_paramType_countable
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
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) :
    ProgramDenotation.prhl2
      (fun σ₁ σ₂ : state => (FVP.glob A).get σ₁ = (FVP.glob A).get σ₂)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (do random_oracle_init; procedureDenotation (A.instantiate RO_eager) args)
      (fun u v => u.1 = v.1 ∧ (FVP.glob A).get u.2 = (FVP.glob A).get v.2) := by
  have h12 := ProgramDenotation.prhl2.trans
    (glob_self_coupling_lazy A args hdisj)
    (output_glob_transfer_games A args hdisj)
  refine h12.conseq (fun σ₁ σ₃ h => ⟨σ₃, h, rfl⟩) ?_
  rintro u v ⟨w, hw1, hw2⟩
  exact ⟨hw1.1.trans hw2.1, hw1.2.trans hw2.2⟩

/-- `Win`-form of the endpoint: any event decided by `A`'s output transfers between
    the lazy and eager games from `={glob A}` initial states, with `={glob A}` final
    states. -/
theorem output_win_transfer_games_of_glob {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType) (Win : sig.ret → Prop)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) :
    ProgramDenotation.prhl2
      (fun σ₁ σ₂ : state => (FVP.glob A).get σ₁ = (FVP.glob A).get σ₂)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (do random_oracle_init; procedureDenotation (A.instantiate RO_eager) args)
      (fun u v => (Win u.1 ↔ Win v.1) ∧ (FVP.glob A).get u.2 = (FVP.glob A).get v.2) :=
  (output_glob_transfer_games_of_glob A args hdisj).conseq
    (fun _ _ h => h) (fun _ _ h => ⟨by rw [h.1], h.2⟩)

end GaudisCrypt.Lib.RO.Instantiate
