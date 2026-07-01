import GaudisCrypt.Lib.RO.InstantiateCommon
import GaudisCrypt.FV

/-!
# RO coupling equivalence (subtask-3, theorem 2)

Lazy ≈ eager random oracle as a **relational** statement (`ProgramDenotation.prhl2`, i.e. a
    coupling): for a
syntactic adversary `A`, instantiating `A` against the eager oracle and against the lazy oracle yields
couplable executions preserving any state invariant `P`. The companion `TransferInstantiate` proves
the *distributional* version (theorem 1) via transfer; this file is the coupling version.

The development has three layers:

* **Lifting** (`liftRel`/`liftRelPost`/`GetOK`/`LocP`): lift the state invariant `P` to
  procedure states (`P` on globals, equal locals) and state the per-statement honest-locality predicate.
* **The coupling** (`body_prhl2_gen` → `ro_hhole_prhl` → `prhl_wrapper`): the body
  induction in `prhl2`, the RO-hole coupling, and the procedure wrapper, assembled into the main theorem.
* **Confinement endpoints** (`FootprintCompat` → `confinedP_locP` → `prhl_instantiate_of_fvP`):
  discharge `LocP` from the adversary's footprint lying in a `FootprintCompat` region (lens-free).
  The EasyCrypt-style entry point is `prhl_instantiate_of_glob`, whose adversary hypothesis is just
  footprint disjointness from the oracle (`FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ`).
-/

namespace GaudisCrypt.Lib.RO.Instantiate

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics
open GaudisCrypt.Language.Programs
open Classical


/-- Lift a state relation `P` to a post-relation on `(result, state)` pairs:
    require equal results and `P` on the states. -/
def liftPost {α : Type} (P : state → state → Prop) : α × state → α × state → Prop :=
  fun u v => u.1 = v.1 ∧ P u.2 v.2


/-! ### Theorem 2 scaffolding: relational invariant preservation

Subtask-3 theorem 2 is the coupling/`prhl2` analogue of theorem 1.  We lift the
state invariant `P` to procedure states (`P` on globals, equal locals), give an
honest locality predicate `LocP` (each of the adversary's own operations
preserves the invariant relationally — its guards return equal booleans and its
updates preserve the relation), and prove the body induction `body_prhl2_gen`
in `prhl2` (the richer relational calculus). -/

/-- Lift `P` (on the global RO state) to a relation on procedure states:
    `P` on the globals, identical locals (the adversary's local computation is
    the same on the eager and lazy sides). -/
def liftRel {l : Type} (P : state → state → Prop) : ProcedureState l → ProcedureState l → Prop :=
  fun ps₁ ps₂ => P ps₁.global ps₂.global ∧ ps₁.locals = ps₂.locals


/-- Post-relation on `(result, procedure state)`: equal results, `liftRel P` on states. -/
def liftRelPost {l α : Type} (P : state → state → Prop) :
    α × ProcedureState l → α × ProcedureState l → Prop :=
  fun u v => u.1 = v.1 ∧ liftRel P u.2 v.2


/-- Read coupling: a getter returns equal values and preserves `liftRel P`.
    Used both for `Bool` guards (`if`/`while`) and the oracle's params getter. -/
def GetOK {γ l : Type} (P : state → state → Prop) (g : Getter γ (ProcedureState l)) : Prop :=
  ProgramDenotation.prhl2 (liftRel P) (ProgramDenotation.get g) (ProgramDenotation.get g)
      (liftRelPost P)


/-- Honest locality for theorem 2: every operation of `A` *outside the oracle*
    preserves the invariant relationally (self-couples under `liftRel P`).  The
    oracle hole is exempt (handled by the per-query hypothesis). -/
def LocP {holes : HoleSigs} {l : Type} (P : state → state → Prop) : StmtWithHoles holes l → Prop
  | .skip => True
  | .sample x e => ProgramDenotation.prhl2 (liftRel P) (programDenotation (StmtWithHoles.sample x e
      : Stmt l))
      (programDenotation (StmtWithHoles.sample x e : Stmt l)) (liftRelPost P)
  | .call' x ls b r p => ProgramDenotation.prhl2 (liftRel P)
      (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l))
      (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l)) (liftRelPost P)
  | .hole _ x p => GetOK P p ∧
      (∀ ret, ProgramDenotation.prhl2 (liftRel P) (ProgramDenotation.set x ret)
          (ProgramDenotation.set x ret) (liftRelPost P))
  | .seq s1 s2 => LocP P s1 ∧ LocP P s2
  | .ifThenElse c t e => GetOK P c ∧ LocP P t ∧ LocP P e
  | .while c t => GetOK P c ∧ LocP P t


/-- **Footprint-level compatibility with `liftRel P`** (lens-free).  A region `R` is `P`-compatible
    when *every* program confined to `R` self-couples under `liftRel P`.  This is exactly what
    `confinedP_locP` consumes — it never inspects a lens, only `inFootprint R`.  Discharged for the
    oracle-complement region by `footprintCompat_of_glob` (the glob/`HasReset` route). -/
def FootprintCompat {l : Type} (P : state → state → Prop)
    (R : Footprint (ProcedureState l)) : Prop :=
  ∀ {γ : Type} {p : ProgramDenotation (ProcedureState l) γ}, p.inFootprint R →
    ProgramDenotation.prhl2 (liftRel P) p p (liftRelPost P)


-- `P` — the state invariant relating eager/lazy global states — is fixed throughout.
variable {P : state → state → Prop}


/-! ## Layer 2 — the coupling -/

/-- **Body induction**: an arbitrary adversary body `A` preserves the lifted invariant relationally,
    given `LocP` and a per-hole coupling `hhole` (the oracle preserves the invariant).  Threads the
    `prhl2` composition rules (`bind`/`cond`/`while_loop`) over the statement structure. -/
theorem body_prhl2_gen :
    ∀ {holes : HoleSigs} {l : Type} (A : StmtWithHoles holes l)
      (eagerInst lazyInst : holes.Instantiation),
      LocP P A →
      (∀ {sig} (n : HoleIndex holes sig)
          (x : Setter sig.ret (ProcedureState l))
          (p : Getter sig.ParamType (ProcedureState l)),
          GetOK P p →
          (∀ ret, ProgramDenotation.prhl2 (liftRel P) (ProgramDenotation.set x ret)
              (ProgramDenotation.set x ret) (liftRelPost P)) →
          ProgramDenotation.prhl2 (liftRel P)
            (programDenotation (StmtWithHoles.call x (eagerInst n) p))
            (programDenotation (StmtWithHoles.call x (lazyInst n) p)) (liftRelPost P)) →
      ProgramDenotation.prhl2 (liftRel P)
        (programDenotation (A.instantiate eagerInst))
        (programDenotation (A.instantiate lazyInst)) (liftRelPost P) := by
  intro holes l A
  induction A with
  | skip =>
      intro eagerInst lazyInst _ _
      simp only [StmtWithHoles.instantiate, programDenotation, ProgramDenotation.skip]
      exact ProgramDenotation.prhl2.pure_pure (fun _ _ h => ⟨rfl, h⟩)
  | sample x e =>
      intro eagerInst lazyInst hloc _
      simp only [StmtWithHoles.instantiate]
      exact hloc
  | call' x ls b r p =>
      intro eagerInst lazyInst hloc _
      simp only [StmtWithHoles.instantiate]
      exact hloc
  | hole n x p =>
      intro eagerInst lazyInst hloc hhole
      simp only [StmtWithHoles.instantiate]
      exact hhole n x p hloc.1 hloc.2
  | seq s1 s2 ih1 ih2 =>
      intro eagerInst lazyInst hloc hhole
      simp only [StmtWithHoles.instantiate, programDenotation]
      refine ProgramDenotation.prhl2.bind (ih1 eagerInst lazyInst hloc.1 hhole) (fun _ _ => ?_)
      exact ProgramDenotation.prhl2.conseq (ih2 eagerInst lazyInst hloc.2 hhole)
        (fun _ _ hpre => hpre.2) (fun _ _ hB => hB)
  | ifThenElse c t e iht ihe =>
      intro eagerInst lazyInst hloc hhole
      simp only [StmtWithHoles.instantiate, programDenotation]
      exact ProgramDenotation.prhl2.cond hloc.1 (iht eagerInst lazyInst hloc.2.1 hhole)
        (ihe eagerInst lazyInst hloc.2.2 hhole)
  | «while» c t iht =>
      intro eagerInst lazyInst hloc hhole
      simp only [StmtWithHoles.instantiate, programDenotation]
      refine ProgramDenotation.prhl2.conseq
        (ProgramDenotation.prhl2.while_loop (PostC := fun _ => liftRel P) hloc.1 ?_)
        (fun _ _ h => h) (fun _ _ hB => ⟨rfl, hB⟩)
      exact ProgramDenotation.prhl2.conseq (iht eagerInst lazyInst hloc.2 hhole)
        (fun _ _ h => h) (fun _ _ hB => hB.2)


/-- **Coupling lift through `zoom globalL`** (the `prhl2` analogue of
    `transferBy_zoom`): a state-level coupling of `c`, `d` under `P` lifts to a
    `ProcedureState` coupling of their `zoom`s under `liftRel P`, threading the
    (equal) locals.  Used to lift the per-query hypothesis `h` to the oracle hole. -/
theorem prhl2_zoom (l : Type) {γ : Type}
    {c d : ProgramDenotation state γ} {B : γ × state → γ × state → Prop}
    (hcd : ProgramDenotation.prhl2 P c d B) :
    ProgramDenotation.prhl2 (liftRel (l := l) P)
      (ProgramDenotation.zoom (ProcedureState.globalL (l := l)) c)
      (ProgramDenotation.zoom (ProcedureState.globalL (l := l)) d)
      (fun u v => B (u.1, u.2.global) (v.1, v.2.global) ∧ u.2.locals = v.2.locals) := by
  intro ps₁ ps₂ hrel
  obtain ⟨μ, hm1, hm2, hsat⟩ := hcd ps₁.global ps₂.global hrel.1
  refine ⟨μ >>= fun w => pure ((w.1.1, (⟨w.1.2, ps₁.locals⟩ : ProcedureState l)),
                               (w.2.1, (⟨w.2.2, ps₂.locals⟩ : ProcedureState l))), ?_, ?_, ?_⟩
  · simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
    show (μ >>= fun w => pure (w.1.1, (⟨w.1.2, ps₁.locals⟩ : ProcedureState l)))
        = c ps₁.global >>= fun as => pure (as.1, (⟨as.2, ps₁.locals⟩ : ProcedureState l))
    rw [← hm1]
    simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
  · simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
    show (μ >>= fun w => pure (w.2.1, (⟨w.2.2, ps₂.locals⟩ : ProcedureState l)))
        = d ps₂.global >>= fun as => pure (as.1, (⟨as.2, ps₂.locals⟩ : ProcedureState l))
    rw [← hm2]
    simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
  · exact SubProbability.satisfies_bind _
      (fun w hw => SubProbability.satisfies_pure _ _ ⟨hsat w hw, hrel.2⟩)


/-- **RO hole coupling**: the eager/lazy oracle calls couple under `liftRel P`,
    given the surrounding read/write are `liftRel`-preserving.  The query couples
    via `prhl2_zoom` of the per-query hypothesis `h` (with the bridges identifying
    the procedures with the semantic queries).  This is `body_prhl2_gen`'s `hhole`
    for the RO instantiation. -/
theorem ro_hhole_prhl {l : Type}
    (h : ∀ inp : input, ProgramDenotation.prhl2 P (random_oracle_query inp) (lazy_query inp)
        (liftPost P))
    {sig : ProcedureSignature} (n : HoleIndex roHoles sig)
    (x : Setter sig.ret (ProcedureState l)) (p : Getter sig.ParamType (ProcedureState l))
    (hp : GetOK P p)
    (hx : ∀ ret, ProgramDenotation.prhl2 (liftRel P) (ProgramDenotation.set x ret)
        (ProgramDenotation.set x ret) (liftRelPost P)) :
    ProgramDenotation.prhl2 (liftRel P)
      (programDenotation (StmtWithHoles.call x (RO_eager n) p))
      (programDenotation (StmtWithHoles.call x (RO_lazy n) p)) (liftRelPost P) := by
  cases n with
  | zero =>
      haveI : Countable roSig.ParamType := inferInstanceAs (Countable input)
      haveI : Countable roSig.ret := inferInstanceAs (Countable output)
      show ProgramDenotation.prhl2 (liftRel P)
          (programDenotation (StmtWithHoles.call x RO_eager_proc p))
          (programDenotation (StmtWithHoles.call x RO_lazy_proc p)) (liftRelPost P)
      rw [denote_call, denote_call]
      refine ProgramDenotation.prhl2.bind hp (fun args₁ args₂ => ?_)
      intro σ₁ σ₂ hpre
      obtain ⟨rfl, hrel⟩ := hpre
      refine (ProgramDenotation.prhl2.bind (M := liftRelPost P) ?_ (fun ret₁ ret₂ => ?_)) σ₁ σ₂ hrel
      · -- the zoomed query couples (via `prhl2_zoom`); post normalized to `liftRelPost P`
        rw [procDenotation_RO_eager, procDenotation_RO_lazy]
        exact ProgramDenotation.prhl2.conseq (prhl2_zoom l (h args₁))
          (fun _ _ h => h) (fun _ _ hB => ⟨hB.1.1, hB.1.2, hB.2⟩)
      · -- the write couples (equal results from the middle post)
        intro τ₁ τ₂ hpre2
        obtain ⟨rfl, hrel2⟩ := hpre2
        exact hx ret₁ τ₁ τ₂ hrel2
  | succ m => nomatch m


/-- **Body-level theorem 2** — fully assembled: an arbitrary `Loc`al adversary
    body preserves the invariant relationally, with the RO oracle.  Combines
    `body_prhl2_gen` with the RO hole coupling `ro_hhole_prhl`. -/
theorem prhl_instantiate_body {l : Type}
    (h : ∀ inp : input, ProgramDenotation.prhl2 P (random_oracle_query inp) (lazy_query inp)
        (liftPost P))
    (A : StmtWithHoles roHoles l) (hloc : LocP P A) :
    ProgramDenotation.prhl2 (liftRel P)
      (programDenotation (A.instantiate RO_eager))
      (programDenotation (A.instantiate RO_lazy)) (liftRelPost P) :=
  body_prhl2_gen A RO_eager RO_lazy hloc (fun n x p hp hx => ro_hhole_prhl h n x p hp hx)


/-- **Procedure wrapper for `prhl2`** (isolated, analogue of `transfer_wrapper`):
    a body-level `prhl2` coupling lifts to a state-level `prhl2` coupling of the
    whole procedure, given the return value is determined by the invariant. -/
theorem prhl_wrapper {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hbody : ProgramDenotation.prhl2 (liftRel P)
      (programDenotation (A.body.instantiate RO_eager))
      (programDenotation (A.body.instantiate RO_lazy)) (liftRelPost P))
    (hret : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → A.return_val.get ps₁ = A.return_val.get ps₂) :
    ProgramDenotation.prhl2 P
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args) (liftPost P) := by
  intro st₁ st₂ hP
  obtain ⟨μ, hm1, hm2, hsat⟩ :=
    hbody ⟨st₁, sig.localVariableInit A.locals args⟩ ⟨st₂, sig.localVariableInit A.locals args⟩ ⟨hP, rfl⟩
  refine ⟨μ >>= fun w => pure ((A.return_val.get w.1.2, w.1.2.global),
                               (A.return_val.get w.2.2, w.2.2.global)), ?_, ?_, ?_⟩
  · simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
    rw [procedureDenotation_eq_procWrap]
    show (μ >>= fun w => pure (A.return_val.get w.1.2, w.1.2.global))
        = (programDenotation (A.body.instantiate RO_eager))
            ⟨st₁, sig.localVariableInit A.locals args⟩ >>= fun p => pure (A.return_val.get p.2, p.2.global)
    rw [← hm1]
    simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
  · simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
    rw [procedureDenotation_eq_procWrap]
    show (μ >>= fun w => pure (A.return_val.get w.2.2, w.2.2.global))
        = (programDenotation (A.body.instantiate RO_lazy))
            ⟨st₂, sig.localVariableInit A.locals args⟩ >>= fun p => pure (A.return_val.get p.2, p.2.global)
    rw [← hm2]
    simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
  · refine SubProbability.satisfies_bind _ (fun w hw => SubProbability.satisfies_pure _ _ ?_)
    have hlr := hsat w hw
    exact ⟨hret w.1.2 w.2.2 hlr.2, hlr.2.1⟩


/-! ## Layer 3 — confinement endpoints (discharge `LocP` from a footprint) -/



/-- **Adversary rule — single `Rᶜ`-step** (footprint `glob`).  A program confined to `R`, run from
    a state `σ` and its image `f σ` under one deterministic `Rᶜ`-update, self-couples: equal
    results, output states again one `Rᶜ`-step apart.  This is the base case of the `={glob A}`
    adversary rule for `glob A = R.touched_getter`.  The full rule is its `EqvGen` closure over the
    `Rᶜ`-orbit — which needs coupling **transitivity** (gluing along a common middle), open in this
    framework; it is gluing-free exactly when `Rᶜ`'s deterministic updates are invertible (e.g.
    lens-derived `R`, handled directly by `prhl2.adversary_inRange`). -/
theorem adversary_couple_step {s a : Type} {R : Footprint s} {p : ProgramDenotation s a}
    (hp : p.inFootprint R) {f : s → s} (hf : diracKer f ∈ Rᶜ.updates) (σ : s) :
    ∃ μ : SubProbability ((a × s) × (a × s)),
      (μ >>= fun x => (pure x.1 : SubProbability (a × s))) = p σ ∧
      (μ >>= fun x => (pure x.2 : SubProbability (a × s))) = p (f σ) ∧
      μ.satisfies (fun x => x.1.1 = x.2.1 ∧
        ∃ g : Function.End s, diracKer g ∈ Rᶜ.updates ∧ g x.1.2 = x.2.2) := by
  refine ⟨p σ >>= fun xs => pure ((xs.1, xs.2), (xs.1, f xs.2)), ?_, ?_, ?_⟩
  · rw [SubProbability.bind_assoc']
    simp only [SubProbability.pure_bind, Prod.mk.eta, SubProbability.bind_pure]
  · rw [SubProbability.bind_assoc']
    simp only [SubProbability.pure_bind]
    exact (inFootprint_subprob hp hf σ).symm
  · exact SubProbability.satisfies_bind _
      (fun xs _ => SubProbability.satisfies_pure _ _ ⟨rfl, f, hf, rfl⟩)


/-- **Adversary rule (full), footprint `glob`.**  A program confined to `R` self-couples under
    `={glob A}` (with `glob A = R.touched_getter`): from states agreeing on `glob A` it returns
    equal results and states that again agree on `glob A`.  The `EqvGen`-closure of
    `adversary_couple_step` — `refl`/`symm`/`trans` on `prhl2` (the `trans` = coupling gluing,
    `ProgramDenotation.prhl2.trans`, discrete disintegration). -/
theorem prhl2_glob {s a : Type} {R : Footprint s} {p : ProgramDenotation s a}
    (hp : p.inFootprint R) :
    ProgramDenotation.prhl2 (fun x y => R.touched_getter.get x = R.touched_getter.get y) p p
      (fun u v => u.1 = v.1 ∧ R.touched_getter.get u.2 = R.touched_getter.get v.2) := by
  -- The one-step `Rᶜ`-orbit relation and its equivalence closure.
  set r : s → s → Prop := fun t t' => ∃ f : Function.End s, diracKer f ∈ Rᶜ.updates ∧ f t = t'
    with hr
  set E : s → s → Prop := Relation.EqvGen r with hE
  -- `touched_getter`-equality is exactly the `EqvGen` relation `E` (via `Quotient.eq`).
  have hgetter : ∀ x y : s, R.touched_getter.get x = R.touched_getter.get y ↔ E x y := by
    intro x y
    change Quotient.mk Rᶜ.orbit_setoid x = Quotient.mk Rᶜ.orbit_setoid y ↔ E x y
    rw [Quotient.eq]
    rfl
  -- Point-precondition auxiliary, proved by induction on the `EqvGen` derivation.
  have aux : ∀ x y : s, E x y →
      ProgramDenotation.prhl2 (fun a b => a = x ∧ b = y) p p
        (fun u v => u.1 = v.1 ∧ E u.2 v.2) := by
    intro x y h
    induction h with
    | rel x y hxy =>
      obtain ⟨f, hf, hfxy⟩ := hxy
      intro σ₁ σ₂ hpre
      obtain ⟨e1, e2⟩ := hpre
      rw [e1, e2]
      obtain ⟨μ, hm1, hm2, hsat⟩ := adversary_couple_step hp hf x
      refine ⟨μ, hm1, ?_, ?_⟩
      · rw [hm2, hfxy]
      · intro w hw
        obtain ⟨heq, g, hg, hgw⟩ := hsat w hw
        exact ⟨heq, Relation.EqvGen.rel _ _ ⟨g, hg, hgw⟩⟩
    | refl x =>
      intro σ₁ σ₂ hpre
      obtain ⟨e1, e2⟩ := hpre
      rw [e1, e2]
      refine ⟨p x >>= fun w => pure (w, w), ?_, ?_, ?_⟩
      · rw [SubProbability.bind_assoc']
        simp only [SubProbability.pure_bind, SubProbability.bind_pure]
      · rw [SubProbability.bind_assoc']
        simp only [SubProbability.pure_bind, SubProbability.bind_pure]
      · exact SubProbability.satisfies_bind _
          (fun w _ => SubProbability.satisfies_pure _ _ ⟨rfl, Relation.EqvGen.refl _⟩)
    | symm x y _hxy ih =>
      refine (ih.symm).conseq (fun σ₁ σ₂ hpre => ⟨hpre.2, hpre.1⟩) ?_
      rintro u v ⟨heq, hEvu⟩
      exact ⟨heq.symm, Relation.EqvGen.symm _ _ hEvu⟩
    | trans x m y _hxm _hmy ihxm ihmy =>
      refine (ihxm.trans ihmy).conseq (fun σ₁ σ₂ hpre => ⟨m, ⟨hpre.1, rfl⟩, rfl, hpre.2⟩) ?_
      rintro u v ⟨w, ⟨heq₁, hE₁⟩, heq₂, hE₂⟩
      exact ⟨heq₁.trans heq₂, Relation.EqvGen.trans _ _ _ hE₁ hE₂⟩
  -- Assemble the main goal from the auxiliary and the getter/`EqvGen` bridge.
  intro x y hxy
  have hExy : E x y := (hgetter x y).mp hxy
  obtain ⟨μ, hm1, hm2, hsat⟩ := aux x y hExy x y ⟨rfl, rfl⟩
  refine ⟨μ, hm1, hm2, ?_⟩
  intro w hw
  obtain ⟨heq, hEw⟩ := hsat w hw
  exact ⟨heq, (hgetter _ _).mpr hEw⟩


/-- **Confinement preserves a disjoint footprint's content** (the lens-free frame linchpin).  A
    program confined to `R` leaves unchanged the content (`S.touched_getter`) of any *resettable*
    footprint `S` disjoint from `R` (`S ≤ Rᶜ`).  Idempotent-fixpoint argument (no orbit collapse):
    `S.HasReset`'s overwrite is an `Rᶜ`-update fixing `σ` that collapses `S.touched_getter` to `σ`'s
    value, so by `inFootprint_subprob` `p σ` is a fixpoint of pushing it.  For `S = roLift.footprint`
    (a lens), `Lens.footprint_hasReset` discharges `S.HasReset`, so the frame needs only footprint
    disjointness `S ≤ Rᶜ`. -/
theorem inFootprint_preserves_touched {s a : Type} {R S : Footprint s} {p : ProgramDenotation s a}
    (hp : p.inFootprint R) (hSc : S ≤ Rᶜ) {σ : s} (hS : S.HasReset σ) :
    (p σ).satisfies (fun xs => S.touched_getter.get xs.2 = S.touched_getter.get σ) := by
  obtain ⟨f, hgen, hfix, hcollapse⟩ := hS
  have hmem : diracKer f ∈ Rᶜ.updates := hSc hgen
  have hstep := inFootprint_subprob hp hmem σ
  rw [hfix] at hstep
  rw [hstep]
  exact SubProbability.satisfies_bind _
    (fun xs _ => SubProbability.satisfies_pure _ _ (hcollapse xs.2))

/-- **`FootprintCompat` is antitone**: a smaller footprint is still `P`-compatible.  Lets us prove
    compatibility once for a large "nice" region (e.g. `Oᶜ`, the oracle-complement) and transport it
    down to any confined adversary `fvP_proc A ≤ Oᶜ` (disjoint from the oracle). -/
theorem FootprintCompat.mono {l : Type} {R R' : Footprint (ProcedureState l)}
    (h : FootprintCompat P R) (hle : R' ≤ R) : FootprintCompat P R' :=
  fun hp => h (ProgramDenotation.inFootprint_mono hp hle)

/-- **Glob-based `FootprintCompat`** (lens-free, `Q`-free, disjointness form).  Reduce
    `FootprintCompat P R` to two intrinsic properties of `liftRel P` over the split into the touched
    content `R.touched_getter` and a *resettable* oracle region `O` disjoint from `R` (`O ≤ Rᶜ`,
    `O.HasReset`):
    * `hrefine` — `liftRel P` **refines `={glob A}`**: the touched content `R.touched_getter` is equal.
    * `hstable` — `liftRel P` is **frame-stable on the oracle**: it depends only on `O`'s content, so
      overwriting the touched content on both sides (keeping `O.touched_getter` fixed) preserves it.

    Each confined program self-couples via `prhl2_glob` (touched stays equal) and
    `inFootprint_preserves_touched` (the oracle content stays fixed, from `O.HasReset` + `O ≤ Rᶜ`),
    then `hstable` rebuilds `liftRel P`.  No `Lens`, no orbit collapse, no frame predicate. -/
theorem footprintCompat_of_glob {l : Type} {R O : Footprint (ProcedureState l)}
    (hOc : O ≤ Rᶜ) (hO : ∀ σ, O.HasReset σ)
    (hrefine : ∀ a b, liftRel P a b → R.touched_getter.get a = R.touched_getter.get b)
    (hstable : ∀ a b u v, liftRel P a b →
        R.touched_getter.get u = R.touched_getter.get v →
        O.touched_getter.get u = O.touched_getter.get a →
        O.touched_getter.get v = O.touched_getter.get b → liftRel P u v) :
    FootprintCompat P R := by
  intro γ' p hp x y hxy
  obtain ⟨μ, hm1, hm2, hsat⟩ := prhl2_glob hp x y (hrefine x y hxy)
  refine ⟨μ, hm1, hm2, ?_⟩
  -- Confinement preserves the oracle content on both marginals (`O ≤ Rᶜ`, `O.HasReset`).
  have hgx := inFootprint_preserves_touched hp hOc (hO x)
  have hgy := inFootprint_preserves_touched hp hOc (hO y)
  intro w hw
  obtain ⟨heq1, htw⟩ := hsat w hw
  refine ⟨heq1, ?_⟩
  -- `w.1` (resp. `w.2`) lies in `p x`'s (resp. `p y`'s) support: its marginal atom is positive.
  have hpx : (p x).1 {w.1} ≠ 0 := by
    rw [← hm1, SubProbability.marginal_fst_singleton μ w.1]
    exact fun h0 => hw ((ENNReal.tsum_eq_zero.mp h0) w.2)
  have hpy : (p y).1 {w.2} ≠ 0 := by
    rw [← hm2, SubProbability.marginal_snd_singleton μ w.2]
    exact fun h0 => hw ((ENNReal.tsum_eq_zero.mp h0) w.1)
  -- `hstable` rebuilds `liftRel P` on the outputs from touched-agreement + preserved oracle content.
  exact hstable x y w.1.2 w.2.2 hxy htw (hgx w.1 hpx) (hgy w.2 hpy)


/-- **`ConfinedP` discharges `LocP`** (theorem-2 locality) for any invariant `P` — the
    `Footprint` analogue of `confined_locP`. -/
theorem confinedP_locP {holes : HoleSigs} {l : Type}
    (R : Footprint (ProcedureState l))
    (hR : FootprintCompat P R)
    (hc : ∀ {sig : ProcedureSignature}, HoleIndex holes sig → Countable sig.ParamType) :
    ∀ (A : StmtWithHoles holes l), ConfinedP R A → LocP P A
  | .skip, _ => trivial
  | .sample _ _, h => hR h
  | .call' _ _ _ _ _, h => hR h
  | .hole n _ _, h =>
      haveI := hc n
      ⟨hR h.1, fun ret => hR (h.2 ret)⟩
  | .seq s1 s2, h =>
      ⟨confinedP_locP R hR hc s1 h.1, confinedP_locP R hR hc s2 h.2⟩
  | .ifThenElse _ t e, h =>
      ⟨hR h.1, confinedP_locP R hR hc t h.2.1, confinedP_locP R hR hc e h.2.2⟩
  | .«while» _ t, h =>
      ⟨hR h.1, confinedP_locP R hR hc t h.2⟩


/-- A getter confined to a `FootprintCompat` region reads **equal** values from `liftRel P`-related
    states — the return-value condition `prhl_wrapper` needs, now derived from the footprint bound
    rather than assumed.  A deterministic `get`/`get` self-coupling has both marginals point masses,
    so its (a.e.) post `x.1.1 = x.2.1` pins the two reads together.  Replaces the standalone
    `hret`. -/
theorem reads_equal_of_footprintCompat {l γ : Type} {R : Footprint (ProcedureState l)}
    (hR : FootprintCompat P R) {g : Getter γ (ProcedureState l)}
    (hg : (ProgramDenotation.get g).inFootprint R)
    {ps₁ ps₂ : ProcedureState l} (hpre : liftRel P ps₁ ps₂) :
    g.get ps₁ = g.get ps₂ := by
  obtain ⟨μ, hm1, hm2, hsat⟩ := hR hg ps₁ ps₂ hpre
  -- Push each marginal to its first *value* component; the two `get`/`get` marginals are point
  -- masses, so `pure (g.get ps₁) = pure (g.get ps₂)` follows from the a.e. post `x.1.1 = x.2.1`.
  have hget : ∀ ps, (ProgramDenotation.get g) ps = pure (g.get ps, ps) := by
    intro ps
    simp only [ProgramDenotation.get, StateT.get, AsGetter.toG, bind, StateT.bind, pure,
      StateT.pure, id_eq, MeasureTheory.Measure.dirac_bind measurable_from_top]
  have h1 : (μ >>= fun x => (pure x.1.1 : SubProbability γ)) = pure (g.get ps₁) := by
    have hrw : (μ >>= fun x => (pure x.1.1 : SubProbability γ))
        = (μ >>= fun x => (pure x.1 : SubProbability (γ × ProcedureState l)))
          >>= fun y => (pure y.1 : SubProbability γ) := by
      rw [SubProbability.bind_assoc]
      exact SubProbability.bind_congr_support _ (fun x _ => by rw [SubProbability.pure_bind])
    rw [hrw, hm1, hget, SubProbability.pure_bind]
  have h2 : (μ >>= fun x => (pure x.2.1 : SubProbability γ)) = pure (g.get ps₂) := by
    have hrw : (μ >>= fun x => (pure x.2.1 : SubProbability γ))
        = (μ >>= fun x => (pure x.2 : SubProbability (γ × ProcedureState l)))
          >>= fun y => (pure y.1 : SubProbability γ) := by
      rw [SubProbability.bind_assoc]
      exact SubProbability.bind_congr_support _ (fun x _ => by rw [SubProbability.pure_bind])
    rw [hrw, hm2, hget, SubProbability.pure_bind]
  have h12 : (μ >>= fun x => (pure x.1.1 : SubProbability γ))
      = (μ >>= fun x => (pure x.2.1 : SubProbability γ)) :=
    SubProbability.bind_congr_support _ (fun x hx => congrArg pure (hsat x hx).1)
  have hpe : (pure (g.get ps₁) : SubProbability γ) = pure (g.get ps₂) := by
    rw [← h1, ← h2, h12]
  -- `pure`-injectivity on `SubProbability γ`: evaluate the dirac measures at `{g.get ps₁}`.
  letI : MeasurableSpace γ := ⊤
  haveI : MeasurableSingletonClass γ := ⟨fun _ => trivial⟩
  have hdirac : (MeasureTheory.Measure.dirac (g.get ps₁)) {g.get ps₁}
      = (MeasureTheory.Measure.dirac (g.get ps₂)) {g.get ps₁} :=
    congrFun (congrArg DFunLike.coe (congrArg Subtype.val hpe)) {g.get ps₁}
  by_contra hne
  rw [MeasureTheory.Measure.dirac_apply' _ (MeasurableSet.singleton _),
    MeasureTheory.Measure.dirac_apply' _ (MeasurableSet.singleton _)] at hdirac
  rw [Set.indicator_of_mem (Set.mem_singleton _),
    Set.indicator_of_notMem (by simpa [Set.mem_singleton_iff] using fun h => hne h.symm)] at hdirac
  exact one_ne_zero hdirac


/-- **Theorem 2 — the entry point.**  Relational (coupling) lazy ≈ eager equivalence for an
    invariant `P`, for any adversary whose own footprint `fvP_proc A` (body + return) is
    `P`-compatible (`FootprintCompat P (fvP_proc A)`).  This is the weakest such hypothesis — only
    `A`'s actual footprint need be compatible, not a larger region — and it subsumes the explicit
    RO-disjointness premise (for the canonical RO-agreement `P`, `FootprintCompat P (fvP_proc A)`
    *is* "`A` is disjoint from the random oracle").  Lens-free, `R`-free; inlines the whole
    `fvP → ConfinedP → LocP → coupling → prhl2` chain. -/
theorem prhl_instantiate_of_fvP {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hcompat : FootprintCompat P (fvP_proc A))
    (h : ∀ inp : input,
        ProgramDenotation.prhl2 P (random_oracle_query inp) (lazy_query inp) (liftPost P)) :
    ProgramDenotation.prhl2 P
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (liftPost P) :=
  prhl_wrapper A args
    (prhl_instantiate_body h A.body
      (confinedP_locP (fvP_proc A) hcompat roHole_paramType_countable A.body
        (confinedP_of_fv (fvP_proc A) roHole_paramType_countable A.body
          (fvP_stmt_body_le_fvP_proc A))))
    (fun _ _ hpre => reads_equal_of_footprintCompat hcompat
      (ProgramDenotation.inFootprint_of_footprint_le (get_return_val_le_fvP_proc A)) hpre)


/-- **The oracle content of a procedure state is the oracle table of its global**: `roLift` reads
    through `globalL` into `random_oracle_state`. -/
theorem roLift_get_global {l : Type} (x : ProcedureState l) :
    (roLift l).get x = random_oracle_state.get x.global := rfl

/-- **The oracle-complement of a procedure state splits into locals + non-oracle global.**  Two
    states have equal outside-oracle content (`(roLift l).compl.get`) iff their locals agree and their
    globals agree away from the oracle (`random_oracle_state.compl.get`).  This is what lets the
    endpoint phrase its premises purely on the global invariant `P` (on `state`), with the locals
    handled structurally by the framework. -/
theorem roLift_compl_get_iff {l : Type} (x y : ProcedureState l) :
    (roLift l).compl.get x = (roLift l).compl.get y ↔
      (x.locals = y.locals ∧
        random_oracle_state.compl.get x.global = random_oracle_state.compl.get y.global) := by
  -- `compl.get` equality unfolds to `equal_outside` (`∃ t, lens.set t · = ·`) on both sides.
  have e1 : ((roLift l).compl.get x = (roLift l).compl.get y) ↔ (roLift l).equal_outside x y :=
    Quotient.eq''
  have e2 : (random_oracle_state.compl.get x.global = random_oracle_state.compl.get y.global) ↔
      random_oracle_state.equal_outside x.global y.global := Quotient.eq''
  rw [e1, e2]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨rfl, t, rfl⟩
  · rintro ⟨hloc, t, ht⟩
    refine ⟨t, ?_⟩
    obtain ⟨xg, xl⟩ := x
    obtain ⟨yg, yl⟩ := y
    show ProcedureState.mk (random_oracle_state.set t xg) xl = ProcedureState.mk yg yl
    rw [show random_oracle_state.set t xg = yg from ht, show xl = yl from hloc]

/-- **Complement is order-reversing on `Footprint`** (`le`/`compl` swap): `R ≤ Sᶜ ↔ S ≤ Rᶜ`.
    Both sides say every `R`-update commutes with every `S`-update, so the relation is symmetric in
    `R`, `S`.  Lets us flip a disjointness stated against the oracle into one stated against the
    adversary. -/
theorem Footprint.le_compl_comm {m : Type} (R S : Footprint m) : R ≤ Sᶜ ↔ S ≤ Rᶜ := by
  constructor <;>
  · intro h
    intro k hk
    show k ∈ Submonoid.centralizer _
    rw [Submonoid.mem_centralizer_iff]
    intro j hj
    exact ((Submonoid.mem_centralizer_iff.mp (h hj)) k hk).symm

/-- **A chained lens's footprint is the `liftFootprint` of the inner lens's footprint through the
    outer lens** (generator-level): `diracKer ((L.chain v).liftFunction g)` is exactly
    `L.liftSubProbability (diracKer (v.liftFunction g))`.  The chained overwrite is the inner
    overwrite performed on the `L`-content and written back. -/
theorem chain_liftFunction_diracKer {a b c : Type} (L : Lens b c) (v : Lens a b)
    (g : Function.End a) :
    diracKer ((L.chain v).liftFunction g) = L.liftSubProbability (diracKer (v.liftFunction g)) := by
  funext x
  show (pure ((L.chain v).liftFunction g x) : SubProbability c)
     = (diracKer (v.liftFunction g) (L.get x)) >>= fun a' => pure (L.set a' x)
  rw [show (diracKer (v.liftFunction g) (L.get x) : SubProbability b)
        = pure (v.liftFunction g (L.get x)) from rfl, SubProbability.pure_bind]
  rfl

/-- **The lift of a `v.footprint`-update commutes with every `R`-update**, when the
    `globalL`-reduction of `R` is disjoint from `v.footprint` — the update-level core of ingredient
    (B).  For `f ∈ v.footprint.updates` and `k ∈ R.updates`, the reduced generators
    `reduceSubProbability globalL (k, i, o)` lie in `(fvP_reduce globalL R).updates`, so `hred`
    makes them commute with `f`; the Fubini identities (`reduceBaseGen_mul_left`/`_right`) turn that
    into commutation of `globalL.liftSubProbability f` with `k` (via `reduceSubProbability_ext`). -/
theorem liftSubProbability_comm_of_reduce_disj {c : Type} {v : Lens (input → Option output) State}
    {R : Footprint (ProcedureState c)}
    (hred : fvP_reduce ProcedureState.globalL R ≤ (v.footprint)ᶜ)
    {f : State → SubProbability State} (hf : f ∈ v.footprint.updates)
    {k : ProcedureState c → SubProbability (ProcedureState c)} (hk : k ∈ R.updates) :
    ProcedureState.globalL.liftSubProbability f * k
      = k * ProcedureState.globalL.liftSubProbability f := by
  apply Lens.reduceSubProbability_ext ProcedureState.globalL
  intro i o
  -- Each reduced generator of `k` is a generator of `fvP_reduce globalL R`, hence (by `hred`)
  -- commutes with `f ∈ v.footprint.updates`.
  have hgen : Lens.reduceSubProbability ProcedureState.globalL (k, i, o)
      ∈ (fvP_reduce ProcedureState.globalL R).updates := by
    rw [fvP_reduce_eq_from, Footprint.from_updates]
    exact Set.subset_centralizer_centralizer
      ⟨(k, i, o), ⟨hk, Set.mem_univ _, Set.mem_univ _⟩, rfl⟩
  have hcomm : f * Lens.reduceSubProbability ProcedureState.globalL (k, i, o)
      = Lens.reduceSubProbability ProcedureState.globalL (k, i, o) * f :=
    (Submonoid.mem_centralizer_iff.mp (hred hgen)) f hf
  rw [reduceBaseGen_mul_left, reduceBaseGen_mul_right] at hcomm
  exact hcomm

/-- **A chained lens's footprint lies in `Rᶜ` whenever the inner footprint's `globalL`-reduction
    does** (specialized to `globalL`): from `fvP_reduce globalL R ≤ (v.footprint)ᶜ` conclude
    `R ≤ ((globalL.chain v).footprint)ᶜ`.  This is ingredient (B) of the FV bridge — the locals
    drop out because `globalL` is the reduction lens.  Route: flip the goal via `le_compl_comm` to
    `(globalL.chain v).footprint ≤ Rᶜ`, then show each generator
    `globalL.liftSubProbability (diracKer (v.liftFunction g))` commutes with every `k ∈ R.updates`
    via `liftSubProbability_comm_of_reduce_disj`. -/
theorem reduce_chain_le_compl {c : Type} {v : Lens (input → Option output) State}
    {R : Footprint (ProcedureState c)}
    (hred : fvP_reduce ProcedureState.globalL R ≤ (v.footprint)ᶜ) :
    R ≤ ((ProcedureState.globalL.chain v).footprint)ᶜ := by
  rw [Footprint.le_compl_comm]
  refine (Footprint.from_le_iff _ _).mpr ?_
  rintro _ ⟨g, rfl⟩
  -- Goal: diracKer ((globalL.chain v).liftFunction g) ∈ Rᶜ.updates = centralizer R.updates
  show diracKer ((ProcedureState.globalL.chain v).liftFunction g) ∈ Rᶜ.updates
  rw [chain_liftFunction_diracKer]
  show ProcedureState.globalL.liftSubProbability (diracKer (v.liftFunction g))
      ∈ Submonoid.centralizer R.updates
  rw [Submonoid.mem_centralizer_iff]
  intro k hk
  have hg_mem : diracKer (v.liftFunction g) ∈ v.footprint.updates :=
    (Footprint.from_le_iff (Set.range fun h : Function.End (input → Option output) =>
      diracKer (v.liftFunction h)) v.footprint).mp le_rfl ⟨g, rfl⟩
  exact (liftSubProbability_comm_of_reduce_disj hred hg_mem hk).symm

/-- **A sampled value's footprint is trivial** — `μ.toProgramDenotation` only draws its result, it
    touches no state, so it lies in `⊥` (mirrors `inFootprint_uniform` for an arbitrary `μ`). -/
theorem inFootprint_toProgramDenotation {s a : Type} (μ : SubProbability a) :
    (SubProbability.toProgramDenotation μ : ProgramDenotation s a).inFootprint ⊥ := by
  rw [inFootprint_iff_clean]
  intro f hf
  funext st
  show (f st >>= fun st' =>
          μ >>= fun v => (pure (v, st') : SubProbability (a × s)))
     = ((μ >>= fun v => (pure (v, st) : SubProbability (a × s)))
          >>= fun w : a × s => f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))
  rw [bind_swap (f st) μ (fun v st' => pure (v, st'))]
  rw [SubProbability.bind_assoc]
  congr 1; funext v
  rw [SubProbability.pure_bind]

/-! ### `while_loop` confinement (fixpoint) — needed for the `call'` body's self-soundness. -/

/-- `⊥` (the always-diverging program) lies in every footprint: it commutes with all kernels. -/
theorem inFootprint_bot {s a : Type} (R : Footprint s) :
    (⊥ : ProgramDenotation s a).inFootprint R := by
  rw [inFootprint_iff_clean]
  intro f hf
  funext st
  show (f st >>= fun _ => (⊥ : SubProbability (a × s)))
     = ((⊥ : SubProbability (a × s)) >>= fun w => f w.2 >>= fun st'' => pure (w.1, st''))
  rw [SubProbability.bot_bind, SubProbability.bind_bot]

open OmegaCompletePartialOrder in
/-- The "run outside kernel first" side of the `inFootprint` equation, as a map of the program `p`,
    is ω-Scott-continuous (rewritten as a `ProgramDenotation` bind so `bind_ωScottContinuous`
    applies). -/
theorem inFootprint_sideL_cont {s a : Type} (f : s → SubProbability s) :
    ωScottContinuous (fun p : ProgramDenotation s a => (fun st => f st >>= fun st' => p st')) := by
  set pf : ProgramDenotation s Unit :=
    (fun st => f st >>= fun st' => (pure ((), st') : SubProbability (Unit × s))) with hpf
  have hbind : ∀ p : ProgramDenotation s a,
      (fun st => f st >>= fun st' => p st') = pf >>= (fun _ => p) := by
    intro p; funext st
    show f st >>= (fun st' => p st')
       = (f st >>= fun st' => (pure ((), st') : SubProbability (Unit × s))) >>= (fun w => p w.2)
    rw [SubProbability.bind_assoc]; congr 1; funext st'; rw [SubProbability.pure_bind]
  rw [show (fun p : ProgramDenotation s a => (fun st => f st >>= fun st' => p st'))
      = (fun p : ProgramDenotation s a => pf >>= (fun _ => p)) from funext hbind]
  refine ProgramDenotation.bind_ωScottContinuous (fun _ => pf) (fun p _ => p) ?_
    ωScottContinuous.const
  exact ωScottContinuous.of_monotone_map_ωSup ⟨fun _ _ hle _ => hle, fun ch => by funext _; rfl⟩

open OmegaCompletePartialOrder in
/-- The "run outside kernel last" side of the `inFootprint` equation is ω-Scott-continuous. -/
theorem inFootprint_sideR_cont {s a : Type} (f : s → SubProbability s) :
    ωScottContinuous (fun p : ProgramDenotation s a =>
      (fun st => p st >>= fun w : a × s =>
        f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))) :=
  ProgramDenotation.bind_ωScottContinuous (fun p => p)
    (fun _ (w : a) (st' : s) => f st' >>= fun st'' => (pure (w, st'') : SubProbability (a × s)))
    ωScottContinuous.const ωScottContinuous.id

open OmegaCompletePartialOrder in
/-- **`inFootprint R` is closed under ω-suprema of chains.**  Both sides of the clean commutation
    equation are ω-Scott-continuous in the program, so if every chain element self-commutes, the
    supremum does too — the admissibility needed for the `while_loop` fixpoint. -/
theorem inFootprint_ωSup {s a : Type} (R : Footprint s)
    (c : Chain (ProgramDenotation s a)) (hc : ∀ n, (c n).inFootprint R) :
    (ωSup c).inFootprint R := by
  rw [inFootprint_iff_clean]
  intro f hf
  have hLeq := (inFootprint_sideL_cont (a := a) f).map_ωSup c
  have hReq := (inFootprint_sideR_cont (a := a) f).map_ωSup c
  show (fun st => f st >>= fun st' => (ωSup c) st') = _
  rw [hLeq, hReq]
  apply congrArg ωSup
  refine Chain.ext (funext fun n => ?_)
  show (fun st => f st >>= fun st' => (c n) st') = _
  exact (inFootprint_iff_clean.mp (hc n)) f hf

/-- One unrolling of the `while_iteration` operator preserves `inFootprint R` (given the guard and
    body do). -/
theorem while_iter_inFootprint {s : Type} (R : Footprint s)
    (cond : ProgramDenotation s Bool) (body : ProgramDenotation s Unit)
    (hcond : cond.inFootprint R) (hbody : body.inFootprint R)
    (g : Unit → ProgramDenotation s Unit) (hg : (g ()).inFootprint R) :
    ((while_iteration cond body) g ()).inFootprint R := by
  show ((do if ← cond then body; g () else return ()) : ProgramDenotation s Unit).inFootprint R
  apply ProgramDenotation.inFootprint_bind hcond
  intro bc
  cases bc with
  | true => exact ProgramDenotation.inFootprint_bind hbody (fun _ => hg)
  | false => exact ProgramDenotation.inFootprint_pure () R

open OmegaCompletePartialOrder in
/-- **`while_loop` confinement.**  A while loop whose guard and body are confined to `R` is itself
    confined to `R`.  The loop is the least fixpoint `⨆ₙ Fⁿ⊥` of `while_iteration`; each Kleene
    iterate is confined (`inFootprint_bot`/`while_iter_inFootprint`), and `inFootprint_ωSup` passes
    this to the supremum. -/
theorem while_loop_inFootprint {s : Type} (R : Footprint s)
    (cond : ProgramDenotation s Bool) (body : ProgramDenotation s Unit)
    (hcond : cond.inFootprint R) (hbody : body.inFootprint R) :
    (while_loop cond body).inFootprint R := by
  set F := while_iteration cond body with hF
  have hmono : Monotone (fun n => (⇑F)^[n] ⊥) := by
    apply monotone_nat_of_le_succ
    intro n
    induction n with
    | zero => simp only [Function.iterate_zero, id_eq, Function.iterate_one]; exact bot_le
    | succ m ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact F.monotone ih
  have hiter : ∀ n, ((⇑F)^[n] ⊥ ()).inFootprint R := by
    intro n
    induction n with
    | zero => exact inFootprint_bot R
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact while_iter_inFootprint R cond body hcond hbody _ ih
  show (F.lfp ()).inFootprint R
  rw [show F.lfp
      = ωSup (⟨fun n => (⇑F)^[n] ⊥, hmono⟩ : Chain (Unit → ProgramDenotation s Unit)) from rfl]
  show (ωSup (⟨fun n => (⇑F)^[n] ⊥ (), fun _ _ hmn => hmono hmn ()⟩ :
      Chain (ProgramDenotation s Unit))).inFootprint R
  exact inFootprint_ωSup R _ hiter

/-! ### Self-soundness and the `lift`/`procedureDenotation` footprint bounds for `call'`. -/

/-- **Self-soundness of the pipeline footprint**: the denotation of a statement is confined to its
    own semantic footprint `Instantiate.fvP_stmt s`.  Leaves are equalities; the compound nodes use
    `footprint_bind_le` + the recursive bound; `while` uses `while_loop_inFootprint`. -/
theorem programDenotation_footprint_le_fvP_stmt {l : Type} :
    ∀ (s : Stmt l), (programDenotation s).footprint ≤ fvP_stmt s
  | .skip => by
      rw [programDenotation.eq_1]
      show (ProgramDenotation.skip : ProgramDenotation (ProcedureState l) Unit).footprint
          ≤ fvP_stmt (StmtWithHoles.skip)
      rw [show fvP_stmt (StmtWithHoles.skip) = (⊥ : Footprint (ProcedureState l)) from rfl]
      apply ProgramDenotation.footprint_le_of_inFootprint
      rw [ProgramDenotation.skip]
      exact ProgramDenotation.inFootprint_pure () ⊥
  | .sample x e => by
      rw [show fvP_stmt (StmtWithHoles.sample x e)
          = (programDenotation (StmtWithHoles.sample x e : Stmt l)).footprint from rfl]
  | .call' x ls b r p => by
      rw [show fvP_stmt (StmtWithHoles.call' x ls b r p)
          = (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l)).footprint from rfl]
  | .seq s1 s2 => by
      rw [programDenotation.eq_3]
      rw [show fvP_stmt (StmtWithHoles.seq s1 s2) = fvP_stmt s1 ⊔ fvP_stmt s2 from rfl]
      refine le_trans (ProgramDenotation.footprint_bind_le _ _) (sup_le ?_ ?_)
      · exact le_trans (programDenotation_footprint_le_fvP_stmt s1) le_sup_left
      · exact iSup_le fun _ => le_trans (programDenotation_footprint_le_fvP_stmt s2) le_sup_right
  | .ifThenElse c t e => by
      rw [programDenotation.eq_4]
      rw [show fvP_stmt (StmtWithHoles.ifThenElse c t e)
          = (ProgramDenotation.get c).footprint ⊔ fvP_stmt t ⊔ fvP_stmt e from rfl]
      refine le_trans (ProgramDenotation.footprint_bind_le _ _) (sup_le ?_ ?_)
      · exact le_trans le_sup_left le_sup_left
      · refine iSup_le fun bcond => ?_
        cases bcond with
        | true =>
            exact le_trans (programDenotation_footprint_le_fvP_stmt t)
              (le_trans le_sup_right le_sup_left)
        | false =>
            exact le_trans (programDenotation_footprint_le_fvP_stmt e) le_sup_right
  | .while c t => by
      rw [programDenotation.eq_5]
      rw [show fvP_stmt (StmtWithHoles.while c t)
          = (ProgramDenotation.get c).footprint ⊔ fvP_stmt t from rfl]
      apply ProgramDenotation.footprint_le_of_inFootprint
      exact while_loop_inFootprint _ (ProgramDenotation.get c) (programDenotation t)
        (ProgramDenotation.inFootprint_of_footprint_le le_sup_left)
        (ProgramDenotation.inFootprint_of_footprint_le
          (le_trans (programDenotation_footprint_le_fvP_stmt t) le_sup_right))
  termination_by s => s.depth
  decreasing_by all_goals (simp only [StmtWithHoles.depth]; omega)

/-- **The footprint of a lens-lift is bounded by the `liftFootprint` of the inner footprint.**  Each
    return-value slice of `L.lift Q` is the `L`-lift of the corresponding slice of `Q`, so every
    generator of `(L.lift Q).footprint` is a generator of `liftFootprint L Q.footprint`. -/
theorem lift_footprint_le {c s a : Type} (L : Lens c s) (Q : ProgramDenotation c a) :
    (L.lift Q).footprint ≤ Lens.liftFootprint L (Q.footprint) := by
  refine (Footprint.from_le_iff _ _).mpr ?_
  rintro _ ⟨y, rfl⟩
  show (fun st => (L.lift Q) st >>= fun w : a × s => if w.1 = y then pure w.2 else ⊥)
      ∈ (Lens.liftFootprint L Q.footprint).updates
  have hgen : (fun st => (L.lift Q) st >>= fun w : a × s => if w.1 = y then pure w.2 else ⊥)
      = L.liftSubProbability
          (fun cc => Q cc >>= fun xc : a × c => if xc.1 = y then pure xc.2 else ⊥) := by
    funext σ
    show ((Q (L.get σ) >>= fun xc : a × c => (pure (xc.1, L.set xc.2 σ) : SubProbability (a × s)))
        >>= fun w : a × s => if w.1 = y then pure w.2 else ⊥)
      = (Q (L.get σ) >>= fun xc : a × c => if xc.1 = y then pure xc.2 else ⊥)
          >>= fun c' => pure (L.set c' σ)
    rw [SubProbability.bind_assoc, SubProbability.bind_assoc]
    congr 1; funext xc
    rw [SubProbability.pure_bind]
    by_cases h : xc.1 = y
    · rw [if_pos h, if_pos h, SubProbability.pure_bind]
    · rw [if_neg h, if_neg h, SubProbability.bot_bind]
  rw [hgen]
  unfold Lens.liftFootprint
  rw [Footprint.from_updates]
  refine Set.subset_centralizer_centralizer ⟨_, ?_, rfl⟩
  exact (Footprint.from_le_iff _ Q.footprint).mp le_rfl ⟨y, rfl⟩

open MeasureTheory in
/-- `globalL.liftSubProbability f` applied to a padded state applies `f` to the global. -/
private theorem globalL_liftSubProbability_pad {l : Type} (f : State → SubProbability State)
    (g : State) (loc : l) :
    (ProcedureState.globalL.liftSubProbability f) ⟨g, loc⟩
      = f g >>= fun a => pure (⟨a, loc⟩ : ProcedureState l) := by
  simp only [Lens.liftSubProbability]; rfl

/-- Reading the global out of `globalL.liftSubProbability f` recovers `f` on the global. -/
private theorem globalL_liftSubProbability_global {l : Type} (f : State → SubProbability State)
    (w2 : ProcedureState l) {ρ : Type} (x : ρ) :
    ((ProcedureState.globalL.liftSubProbability f) w2 >>= fun s'' => pure (x, s''.global))
      = f w2.global >>= fun a => pure (x, a) := by
  simp only [Lens.liftSubProbability]
  rw [SubProbability.bind_assoc]; congr 1; funext a; rw [SubProbability.pure_bind]; rfl

open MeasureTheory in
/-- **Core `call'` commutation.**  Given that the body `pb` and the return getter `r` both commute
    with `globalL.liftSubProbability f`, the reduced procedure denotation commutes with `f` — the
    heart of the `procedureDenotation` footprint bound. -/
theorem procDenot_core {sig : ProcedureSignature}
    (ls : List (Σ t : Type, Inhabited t))
    (r : Getter sig.ret (ProcedureState (sig.LocalVariableState ls)))
    (σ : State)
    (f : State → SubProbability State)
    (pb : ProgramDenotation (ProcedureState (sig.LocalVariableState ls)) Unit)
    (init : sig.LocalVariableState ls)
    (hbc : (fun st => (ProcedureState.globalL.liftSubProbability f) st >>= pb)
        = (fun st => pb st >>= fun w =>
            (ProcedureState.globalL.liftSubProbability f) w.2 >>= fun st'' =>
              (pure (w.1, st'') :
                SubProbability (Unit × ProcedureState (sig.LocalVariableState ls)))))
    (hrc : (fun st =>
        (ProcedureState.globalL.liftSubProbability f) st >>= (ProgramDenotation.get r))
        = (fun st => (ProgramDenotation.get r) st >>= fun w =>
            (ProcedureState.globalL.liftSubProbability f) w.2 >>= fun st'' =>
              (pure (w.1, st'') :
                SubProbability (sig.ret × ProcedureState (sig.LocalVariableState ls))))) :
    (f σ >>= fun σ' => pb ⟨σ', init⟩ >>= fun w =>
        (pure (r.get w.2, w.2.global) : SubProbability (sig.ret × State)))
      = (pb ⟨σ, init⟩ >>= fun w =>
          (pure (r.get w.2, w.2.global) : SubProbability (sig.ret × State)))
          >>= fun u => f u.2 >>= fun s'' => pure (u.1, s'') := by
  set F := ProcedureState.globalL.liftSubProbability f with hFdef
  have step1 : (f σ >>= fun σ' => pb ⟨σ', init⟩) = F ⟨σ, init⟩ >>= pb := by
    rw [hFdef, globalL_liftSubProbability_pad, SubProbability.bind_assoc]
    congr 1; funext a; rw [SubProbability.pure_bind]
  have hLHS : (f σ >>= fun σ' => pb ⟨σ', init⟩ >>= fun w =>
        (pure (r.get w.2, w.2.global) : SubProbability (sig.ret × State)))
      = (f σ >>= fun σ' => pb ⟨σ', init⟩) >>= fun w =>
          (pure (r.get w.2, w.2.global) : SubProbability (sig.ret × State)) := by
    rw [SubProbability.bind_assoc]
  rw [hLHS, step1]
  have hbcσ := congrFun hbc ⟨σ, init⟩
  rw [hbcσ, SubProbability.bind_assoc, SubProbability.bind_assoc]
  congr 1; funext w
  rw [SubProbability.pure_bind, SubProbability.bind_assoc]
  have hLcont : (F w.2 >>= fun s'' =>
        (pure (w.1, s'') : SubProbability (Unit × ProcedureState (sig.LocalVariableState ls)))
        >>= fun w' => pure (r.get w'.2, w'.2.global))
      = F w.2 >>= fun s'' => (pure (r.get s'', s''.global) : SubProbability (sig.ret × State)) := by
    congr 1; funext s''; rw [SubProbability.pure_bind]
  rw [hLcont]
  have hget : ∀ s' : ProcedureState (sig.LocalVariableState ls),
      (ProgramDenotation.get r) s' = pure (r.get s', s') := by
    intro s'
    simp only [ProgramDenotation.get, StateT.get, AsGetter.toG, bind, StateT.bind, pure,
      StateT.pure, id_eq, MeasureTheory.Measure.dirac_bind measurable_from_top]
  have hrcw0 := congrFun hrc w.2
  have hrcw : (F w.2 >>= fun s' =>
        (pure (r.get s', s') :
          SubProbability (sig.ret × ProcedureState (sig.LocalVariableState ls))))
      = F w.2 >>= fun s'' =>
          (pure (r.get w.2, s'') :
            SubProbability (sig.ret × ProcedureState (sig.LocalVariableState ls))) := by
    have hL : (F w.2 >>= fun s' =>
          (pure (r.get s', s') :
            SubProbability (sig.ret × ProcedureState (sig.LocalVariableState ls))))
        = F w.2 >>= ProgramDenotation.get r := by
      congr 1; funext s'; rw [hget s']
    have hR : ((ProgramDenotation.get r) w.2 >>= fun v => F v.2 >>= fun s'' =>
          (pure (v.1, s'') :
            SubProbability (sig.ret × ProcedureState (sig.LocalVariableState ls))))
        = F w.2 >>= fun s'' =>
            (pure (r.get w.2, s'') :
              SubProbability (sig.ret × ProcedureState (sig.LocalVariableState ls))) := by
      rw [hget w.2, SubProbability.pure_bind]
    rw [hL, hrcw0, hR]
  have hsplit : (F w.2 >>= fun s'' =>
        (pure (r.get s'', s''.global) : SubProbability (sig.ret × State)))
      = (F w.2 >>= fun s' =>
          (pure (r.get s', s') :
            SubProbability (sig.ret × ProcedureState (sig.LocalVariableState ls))))
          >>= fun u => pure (u.1, u.2.global) := by
    rw [SubProbability.bind_assoc]; congr 1; funext s''; rw [SubProbability.pure_bind]
  rw [hsplit, hrcw, SubProbability.bind_assoc]
  have hfin : (F w.2 >>= fun s'' =>
        (pure (r.get w.2, s'') :
          SubProbability (sig.ret × ProcedureState (sig.LocalVariableState ls)))
        >>= fun u => pure (u.1, u.2.global))
      = F w.2 >>= fun s'' => (pure (r.get w.2, s''.global) : SubProbability (sig.ret × State)) := by
    congr 1; funext s''; rw [SubProbability.pure_bind]
  rw [hfin, hFdef, globalL_liftSubProbability_global]

/-- **The reduced procedure denotation is confined to the `globalL`-reduction of its body+return
    footprint.**  Ingredient of the `call'` FV-soundness case: `f` outside `fvP_reduce globalL Y`
    lifts to `globalL.liftSubProbability f ∈ Yᶜ` (Fubini), so the body and return getter commute
    with it, and `procDenot_core` then commutes the whole procedure with `f`. -/
theorem procedureDenotation_inFootprint_reduce {sig : ProcedureSignature}
    (ls : List (Σ t : Type, Inhabited t))
    (b : StmtWithHoles HoleSigs.empty (sig.LocalVariableState ls))
    (r : Getter sig.ret (ProcedureState (sig.LocalVariableState ls)))
    (av : sig.ParamType)
    (Y : Footprint (ProcedureState (sig.LocalVariableState ls)))
    (hb : (programDenotation b).footprint ≤ Y)
    (hr : (ProgramDenotation.get r).footprint ≤ Y) :
    (procedureDenotation ⟨ls, b, r⟩ av).inFootprint (fvP_reduce ProcedureState.globalL Y) := by
  rw [inFootprint_iff_clean]
  intro f hf
  have hF : ProcedureState.globalL.liftSubProbability f ∈ Yᶜ.updates := by
    show ProcedureState.globalL.liftSubProbability f ∈ Submonoid.centralizer Y.updates
    rw [Submonoid.mem_centralizer_iff]
    intro k hk
    apply Lens.reduceSubProbability_ext ProcedureState.globalL
    intro i o
    have hgen : Lens.reduceSubProbability ProcedureState.globalL (k, i, o)
        ∈ (fvP_reduce ProcedureState.globalL Y).updates := by
      rw [fvP_reduce_eq_from, Footprint.from_updates]
      exact Set.subset_centralizer_centralizer
        ⟨(k, i, o), ⟨hk, Set.mem_univ _, Set.mem_univ _⟩, rfl⟩
    have hcomm : Lens.reduceSubProbability ProcedureState.globalL (k, i, o) * f
        = f * Lens.reduceSubProbability ProcedureState.globalL (k, i, o) :=
      (Submonoid.mem_centralizer_iff.mp hf) _ hgen
    rw [reduceBaseGen_mul_right, reduceBaseGen_mul_left] at hcomm
    exact hcomm
  have hbc := (inFootprint_iff_clean.mp (ProgramDenotation.inFootprint_of_footprint_le hb)) _ hF
  have hrc := (inFootprint_iff_clean.mp (ProgramDenotation.inFootprint_of_footprint_le hr)) _ hF
  funext σ
  rw [show procedureDenotation ⟨ls, b, r⟩ av
      = (fun st => programDenotation b ⟨st, sig.localVariableInit ls av⟩
          >>= fun w => pure (r.get w.2, w.2.global)) from ?_]
  · exact procDenot_core ls r σ f (programDenotation b) (sig.localVariableInit ls av) hbc hrc
  · funext st; rw [procedureDenotation]

/-- **The `call'` leaf's footprint is bounded by FV's syntactic footprint.**  The nested call
    denotation is `get p; zoom globalL (procedureDenotation …); set x`; each piece is bounded — the
    `zoom` via `lift_footprint_le` + `procedureDenotation_inFootprint_reduce` + self-soundness of
    the body — and the transferred sub-body/return footprints match FV's `transfer` summands.  Takes
    the body's FV soundness `hbody` as a hypothesis (from the recursive `fvP_stmt_le_FVP`). -/
theorem fvP_stmt_call_le {holes : HoleSigs} {l : Type} {sig : ProcedureSignature}
    (x : Setter sig.ret (ProcedureState l))
    (ls : List (Σ t : Type, Inhabited t))
    (b : StmtWithHoles HoleSigs.empty (sig.LocalVariableState ls))
    (r : Getter sig.ret (ProcedureState (sig.LocalVariableState ls)))
    (p : Getter sig.ParamType (ProcedureState l))
    (hbody : fvP_stmt b ≤ FVP.fvP_stmt b) :
    fvP_stmt (StmtWithHoles.call' (h := holes) x ls b r p)
      ≤ FVP.fvP_stmt (StmtWithHoles.call' (h := holes) x ls b r p) := by
  rw [show FVP.fvP_stmt (StmtWithHoles.call' (h := holes) x ls b r p) =
      ProgramDenotation.footprint' (ProgramDenotation.set x) ⊔
      (Lens.liftFootprint ProcedureState.globalL
          (fvP_reduce ProcedureState.globalL (FVP.fvP_stmt b)) ⊔
      (Lens.liftFootprint ProcedureState.globalL
          (fvP_reduce ProcedureState.globalL ((ProgramDenotation.get r).footprint)) ⊔
      (ProgramDenotation.get p).footprint)) from rfl]
  rw [show fvP_stmt (StmtWithHoles.call' (h := holes) x ls b r p)
      = (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l)).footprint from rfl]
  rw [programDenotation.eq_6]
  refine le_trans (ProgramDenotation.footprint_bind_le _ _) (sup_le ?_ ?_)
  · exact le_trans le_sup_right (le_trans le_sup_right le_sup_right)
  · refine iSup_le fun av => ?_
    refine le_trans (ProgramDenotation.footprint_bind_le _ _) (sup_le ?_ ?_)
    · show (ProcedureState.globalL.lift (procedureDenotation ⟨ls, b, r⟩ av)).footprint ≤ _
      refine le_trans (lift_footprint_le _ _) ?_
      set Y := (programDenotation b).footprint ⊔ (ProgramDenotation.get r).footprint with hY
      have hpr : (procedureDenotation ⟨ls, b, r⟩ av).footprint
          ≤ fvP_reduce ProcedureState.globalL Y :=
        ProgramDenotation.footprint_le_of_inFootprint
          (procedureDenotation_inFootprint_reduce ls b r av Y le_sup_left le_sup_right)
      refine le_trans (Lens.liftFootprint_mono _ hpr) ?_
      have hYle : Y ≤ FVP.fvP_stmt b ⊔ (ProgramDenotation.get r).footprint := by
        refine sup_le ?_ le_sup_right
        exact le_trans (le_trans (programDenotation_footprint_le_fvP_stmt b) hbody) le_sup_left
      refine le_trans (Lens.liftFootprint_mono _ (fvP_reduce_mono _ hYle)) ?_
      rw [fvP_reduce_sup, Lens.liftFootprint_sup]
      exact sup_le (le_trans le_sup_left le_sup_right)
        (le_trans (le_trans le_sup_left le_sup_right) le_sup_right)
    · exact iSup_le fun rv => by
        rw [ProgramDenotation.footprint']
        exact le_trans (le_iSup (fun z => (ProgramDenotation.set x z).footprint) rv) le_sup_left

/-- **The sample leaf's footprint is bounded by `setter x ⊔ getter e`** — the `sample` case of FV
    soundness, isolated (so unification never has to reduce `programDenotation` while matching the
    outer join).  The inner `sample`-body `μ.toProgramDenotation >>= set x` lands in `setter x` (its
    sampled part is `⊥`), and the leading `get e` in `getter e`. -/
theorem fvP_stmt_sample_le {holes : HoleSigs} {l a : Type} (x : Setter a (ProcedureState l))
    (e : Getter (SubProbability a) (ProcedureState l)) :
    fvP_stmt (StmtWithHoles.sample (h := holes) x e)
      ≤ FVP.fvP_stmt (StmtWithHoles.sample (h := holes) x e) := by
  rw [show FVP.fvP_stmt (StmtWithHoles.sample (h := holes) x e) =
      ProgramDenotation.footprint' (ProgramDenotation.set x) ⊔
        (ProgramDenotation.get e).footprint from rfl]
  rw [show fvP_stmt (StmtWithHoles.sample (h := holes) x e)
      = (programDenotation (StmtWithHoles.sample x e : Stmt l)).footprint from rfl]
  rw [programDenotation.eq_2]
  -- Inner bound: the sample-body lands in `footprint' (set x)`.
  have hinner : ∀ μ : SubProbability a,
      (μ.toProgramDenotation >>= fun v => ProgramDenotation.set x v).footprint
        ≤ ProgramDenotation.footprint' (ProgramDenotation.set x) := by
    intro μ
    refine le_trans (ProgramDenotation.footprint_bind_le _ _) (sup_le ?_ ?_)
    · exact le_trans (ProgramDenotation.footprint_le_of_inFootprint
        (inFootprint_toProgramDenotation μ)) bot_le
    · exact iSup_le fun v => le_iSup (fun ret => (ProgramDenotation.set x ret).footprint) v
  refine le_trans (ProgramDenotation.footprint_bind_le _ _) (sup_le ?_ ?_)
  · exact le_sup_right
  · exact le_trans (iSup_le hinner) le_sup_left

/-- **FV soundness (statement level)** — ingredient (A): the pipeline's *semantic* per-statement
    footprint `Instantiate.fvP_stmt s` is bounded by FV's *syntactic* one `FVP.fvP_stmt s`.  By
    structural recursion on `s`: leaves are bounded via `footprint_bind_le` (matching `setter`/
    `getter`), the `call'` leaf via `fvP_stmt_call_le` (fed the body's recursive bound), and the
    structural nodes by `⊔`-monotonicity + the recursive bound. -/
theorem fvP_stmt_le_FVP {holes : HoleSigs} {l : Type} :
    ∀ (s : StmtWithHoles holes l), fvP_stmt s ≤ FVP.fvP_stmt s
  | .skip => by
      show fvP_stmt (StmtWithHoles.skip) ≤ FVP.fvP_stmt (StmtWithHoles.skip)
      simp only [fvP_stmt]
      exact bot_le
  | .sample x e => fvP_stmt_sample_le x e
  | .call' x ls b r p => fvP_stmt_call_le x ls b r p (fvP_stmt_le_FVP b)
  | .hole n x p => by
      rw [show FVP.fvP_stmt (StmtWithHoles.hole n x p) =
          ProgramDenotation.footprint' (ProgramDenotation.set x) ⊔
            (ProgramDenotation.get p).footprint from rfl]
      rw [show fvP_stmt (StmtWithHoles.hole n x p) =
          (ProgramDenotation.get p).footprint ⊔
            (⨆ ret, (ProgramDenotation.set x ret).footprint) from rfl]
      rw [sup_comm, ProgramDenotation.footprint']
  | .seq s1 s2 => by
      rw [show FVP.fvP_stmt (StmtWithHoles.seq s1 s2) =
          FVP.fvP_stmt s1 ⊔ FVP.fvP_stmt s2 from rfl]
      rw [show fvP_stmt (StmtWithHoles.seq s1 s2) = fvP_stmt s1 ⊔ fvP_stmt s2 from rfl]
      exact sup_le_sup (fvP_stmt_le_FVP s1) (fvP_stmt_le_FVP s2)
  | .ifThenElse c t e => by
      rw [show FVP.fvP_stmt (StmtWithHoles.ifThenElse c t e) =
          (ProgramDenotation.get c).footprint ⊔ (FVP.fvP_stmt t ⊔ FVP.fvP_stmt e) from rfl]
      rw [show fvP_stmt (StmtWithHoles.ifThenElse c t e) =
          (ProgramDenotation.get c).footprint ⊔ fvP_stmt t ⊔ fvP_stmt e from rfl]
      rw [sup_assoc]
      exact sup_le_sup_left (sup_le_sup (fvP_stmt_le_FVP t) (fvP_stmt_le_FVP e)) _
  | .«while» c t => by
      rw [show FVP.fvP_stmt (StmtWithHoles.while c t) =
          (ProgramDenotation.get c).footprint ⊔ FVP.fvP_stmt t from rfl]
      rw [show fvP_stmt (StmtWithHoles.while c t) =
          (ProgramDenotation.get c).footprint ⊔ fvP_stmt t from rfl]
      exact sup_le_sup_left (fvP_stmt_le_FVP t) _
  termination_by s => s.depth
  decreasing_by all_goals (simp only [StmtWithHoles.depth]; omega)

/-- **Bridge: FV's (global, syntactic) `fvP_proc` disjointness ⟹ the pipeline's (procedure-state,
    semantic) disjointness.**  `FVP.fvP_proc A` (a `Footprint State`, the `globalL`-reduction of A's
    *syntactic* footprint) over-approximates the pipeline's *semantic* `fvP_proc A` after reduction, so
    a disjointness from `random_oracle_state` on the global state gives the disjointness from
    `roLift = globalL.chain random_oracle_state` the confinement needs.  Two ingredients:
    (1) **FV soundness** — the pipeline's semantic `fvP_stmt` is bounded by FV's syntactic one; and
    (2) the **`reduce`/`chain` transfer** through `globalL` (where the locals drop out — they are `⊥`
    to the oracle). -/
theorem fvP_proc_le_roLift_compl {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) :
    fvP_proc A ≤ ((roLift (sig.LocalVariableState A.locals)).footprint)ᶜ := by
  -- `FVP.fvP_proc A = fvP_reduce globalL (FVP.fvP_stmt body) ⊔ fvP_reduce globalL (get return)`.
  rw [show FVP.fvP_proc A =
      fvP_reduce ProcedureState.globalL (FVP.fvP_stmt A.body) ⊔
        fvP_reduce ProcedureState.globalL ((ProgramDenotation.get A.return_val).footprint)
      from rfl] at hdisj
  -- `roLift = globalL.chain random_oracle_state`; both summands go via `reduce_chain_le_compl`.
  show fvP_stmt A.body ⊔ (ProgramDenotation.get A.return_val).footprint
      ≤ ((ProcedureState.globalL.chain random_oracle_state).footprint)ᶜ
  refine sup_le ?_ ?_
  · -- body: `fvP_reduce (fvP_stmt) ≤ fvP_reduce (FVP.fvP_stmt) ≤ FVP.fvP_proc ≤ (ros)ᶜ`.
    refine reduce_chain_le_compl (le_trans (fvP_reduce_mono _ (fvP_stmt_le_FVP A.body)) ?_)
    exact le_trans le_sup_left hdisj
  · -- return: `fvP_reduce (get return) ≤ FVP.fvP_proc ≤ (ros)ᶜ`.
    exact reduce_chain_le_compl (le_trans le_sup_right hdisj)

/-- **Theorem 2 via `glob`** (the EasyCrypt-style endpoint, disjointness form, global invariant).
    Relational lazy ≈ eager for any adversary `A` whose footprint is **disjoint from the random
    oracle** (`hdisj : fvP_proc A ≤ (roLift _).footprintᶜ`), from two conditions on the **global**
    invariant `P` (on `state`) — no locals, phrased entirely via `random_oracle_state`:
    * `hrefine` — `P` forces agreement on the non-oracle globals (`random_oracle_state.compl`), and
    * `hstable` — `P` is determined by the **oracle table** (`random_oracle_state`): overwriting the
      non-oracle globals on both sides (keeping each side's table) preserves it.

    Locals never appear: `liftRel`'s `locals`-equality is carried structurally by `prhl2_glob` (A runs
    identically), which is also why locals *must not* enter a condition that has to survive descent
    into `call'` (a callee's locals differ).  Internally `footprintCompat_of_glob` runs at
    `R = (roLift _).footprintᶜ` (resettability discharged by `Lens.footprint_hasReset`); the global
    `P`-conditions are lifted to procedure states via `roLift_compl_get_iff`/`roLift_get_global` and
    `FootprintCompat.mono` transports the result down to `fvP_proc A` via `hdisj`. -/
theorem prhl_instantiate_of_glob {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ)
    (hrefine : ∀ g₁ g₂ : state, P g₁ g₂ →
        random_oracle_state.compl.get g₁ = random_oracle_state.compl.get g₂)
    (hstable : ∀ g₁ g₂ g₁' g₂' : state, P g₁ g₂ →
        random_oracle_state.compl.get g₁' = random_oracle_state.compl.get g₂' →
        random_oracle_state.get g₁' = random_oracle_state.get g₁ →
        random_oracle_state.get g₂' = random_oracle_state.get g₂ → P g₁' g₂')
    (h : ∀ inp : input,
        ProgramDenotation.prhl2 P (random_oracle_query inp) (lazy_query inp) (liftPost P)) :
    ProgramDenotation.prhl2 P
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (liftPost P) :=
  prhl_instantiate_of_fvP A args
    (FootprintCompat.mono
      (footprintCompat_of_glob
        (R := ((roLift (sig.LocalVariableState A.locals)).footprint)ᶜ)
        (O := (roLift (sig.LocalVariableState A.locals)).footprint)
        (le_of_eq (Footprint.compl_compl _).symm)
        (fun σ => Lens.footprint_hasReset _ σ)
        (fun a b hab =>
          (Lens.footprint_compl_touched_getter_eq_iff _ a b).mpr
            ((roLift_compl_get_iff a b).mpr ⟨hab.2, hrefine a.global b.global hab.1⟩))
        (fun a b u v hab htouch hgu hgv => by
          obtain ⟨hloc, hng⟩ := (roLift_compl_get_iff u v).mp
            ((Lens.footprint_compl_touched_getter_eq_iff _ u v).mp htouch)
          refine ⟨hstable a.global b.global u.global v.global hab.1 hng ?_ ?_, hloc⟩
          · rw [← roLift_get_global u, ← roLift_get_global a]
            exact (Lens.footprint_touched_getter_eq_iff _ u a).mp hgu
          · rw [← roLift_get_global v, ← roLift_get_global b]
            exact (Lens.footprint_touched_getter_eq_iff _ v b).mp hgv))
      (fvP_proc_le_roLift_compl A hdisj)) h

end GaudisCrypt.Lib.RO.Instantiate
