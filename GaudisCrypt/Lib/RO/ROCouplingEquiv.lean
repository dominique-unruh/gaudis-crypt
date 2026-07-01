import GaudisCrypt.Lib.RO.InstantiateCommon

/-!
# RO coupling equivalence (subtask-3, theorem 2)

Lazy ≈ eager random oracle as a **relational** statement (`ProgramDenotation.prhl`, i.e. a
    coupling): for a
syntactic adversary `A`, instantiating `A` against the eager oracle and against the lazy oracle yields
couplable executions preserving any state invariant `P`. The companion `TransferInstantiate` proves
the *distributional* version (theorem 1) via transfer; this file is the coupling version.

The development has three layers:

* **Lifting** (`liftRel`/`liftRelPost`/`GetOK`/`LocP`/`LiftCompat`): lift the state invariant `P` to
  procedure states (`P` on globals, equal locals) and state the per-statement honest-locality predicate.
* **The coupling** (`body_prhl2_gen` → `ro_hhole_prhl` → `prhl_wrapper`): the body
  induction in `prhl2`, the RO-hole coupling, and the procedure wrapper, assembled into the main theorem.
* **Confinement endpoints** (`FootprintCompat` / `footprintCompat_of_lens` → `confinedP_locP` →
  `prhl_instantiate_of_fvP`): discharge `LocP` from the adversary's footprint lying in a
  `FootprintCompat` region (lens-free; a `LiftCompat` lens gives one via `footprintCompat_of_lens`).
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

Subtask-3 theorem 2 is the coupling/`prhl` analogue of theorem 1.  We lift the
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


/-- **`L_adv` is a `liftRel P`-congruence**: it reads equal values from `liftRel P`-related states
    (`.1`) and its writes preserve `liftRel P` (`.2`). Exactly the compatibility that turns
    confinement-to-`L_adv` into the relational locality `LocP`. -/
def LiftCompat {l advSt : Type} (P : state → state → Prop)
    (L_adv : Lens advSt (ProcedureState l)) : Prop :=
  (∀ ps₁ ps₂, liftRel P ps₁ ps₂ → L_adv.get ps₁ = L_adv.get ps₂) ∧
  (∀ (c : advSt) ps₁ ps₂, liftRel P ps₁ ps₂ → liftRel P (L_adv.set c ps₁) (L_adv.set c ps₂))


/-- **Footprint-level compatibility with `liftRel P`** (lens-free).  A region `R` is `P`-compatible
    when *every* program confined to `R` self-couples under `liftRel P`.  This is exactly what
    `confinedP_locP` consumes — it never inspects a lens, only `inFootprint R`.  The lens route
    `LiftCompat` is one way to discharge it (`footprintCompat_of_lens`); other regions (e.g.
    joins of compatible footprints) can be supplied directly. -/
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
    (h : ∀ inp : input, ProgramDenotation.prhl P (random_oracle_query inp) (lazy_query inp)
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
        exact ProgramDenotation.prhl2.conseq (prhl2_zoom l ((h args₁).to_prhl2))
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
    (h : ∀ inp : input, ProgramDenotation.prhl P (random_oracle_query inp) (lazy_query inp)
        (liftPost P))
    (A : StmtWithHoles roHoles l) (hloc : LocP P A) :
    ProgramDenotation.prhl2 (liftRel P)
      (programDenotation (A.instantiate RO_eager))
      (programDenotation (A.instantiate RO_lazy)) (liftRelPost P) :=
  body_prhl2_gen A RO_eager RO_lazy hloc (fun n x p hp hx => ro_hhole_prhl h n x p hp hx)


/-- **Procedure wrapper for `prhl`** (isolated, analogue of `transfer_wrapper`):
    a body-level `prhl2` coupling lifts to a state-level `prhl` coupling of the
    whole procedure, given the return value is determined by the invariant. -/
theorem prhl_wrapper {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hbody : ProgramDenotation.prhl2 (liftRel P)
      (programDenotation (A.body.instantiate RO_eager))
      (programDenotation (A.body.instantiate RO_lazy)) (liftRelPost P))
    (hret : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → A.return_val.get ps₁ = A.return_val.get ps₂) :
    ProgramDenotation.prhl P
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args) (liftPost P) := by
  apply ProgramDenotation.prhl2.to_prhl
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

/-- A program confined to an adversary lens `L_adv` (with `LiftCompat P L_adv`) self-couples under
    `liftRel P` — the lift form (mirrors `ProgramDenotation.prhl2.adversary`, generalized from
        `L.get =` to an
    arbitrary `liftRel P`): `hcompat.1` gives the inner program equal inputs, `hcompat.2` propagates
    the relation through the write-back. -/
theorem prhl2_lift_lens {l γ advSt : Type}
    (L_adv : Lens advSt (ProcedureState l))
    (hcompat : LiftCompat P L_adv)
    (p' : ProgramDenotation advSt γ) :
    ProgramDenotation.prhl2 (liftRel P) (L_adv.lift p') (L_adv.lift p') (liftRelPost P) := by
  intro ps₁ ps₂ hpre
  refine ⟨p' (L_adv.get ps₁) >>= fun xc =>
      pure ((xc.1, L_adv.set xc.2 ps₁), (xc.1, L_adv.set xc.2 ps₂)), ?_, ?_, ?_⟩
  · rw [SubProbability.bind_assoc']; simp only [SubProbability.pure_bind]; rfl
  · rw [SubProbability.bind_assoc']; simp only [SubProbability.pure_bind]
    rw [show L_adv.get ps₁ = L_adv.get ps₂ from hcompat.1 ps₁ ps₂ hpre]; rfl
  · exact SubProbability.satisfies_bind _ (fun xc _ =>
      SubProbability.satisfies_pure _ _ ⟨rfl, hcompat.2 xc.2 ps₁ ps₂ hpre⟩)


/-- **Theorem-2 leaf discharge** (probabilistic). A program confined (in the `inFootprint` sense)
    to an adversary lens `L_adv` compatible with `liftRel P` self-couples. The `Footprint`
    analogue of `prhl2_of_inRange_lens` — factors through `factor_of_inFootprint` and the
    *range-independent* `prhl2_lift_lens` (reused verbatim). -/
theorem prhl2_of_inFootprint_lens {l γ advSt : Type} [Nonempty (ProcedureState l)]
    (L_adv : Lens advSt (ProcedureState l))
    (hcompat : LiftCompat P L_adv)
    {p : ProgramDenotation (ProcedureState l) γ} (hp : p.inFootprint L_adv.footprint) :
    ProgramDenotation.prhl2 (liftRel P) p p (liftRelPost P) := by
  rw [factor_of_inFootprint L_adv hp]
  exact prhl2_lift_lens L_adv hcompat (L_adv.factor p)


/-- **The lens route to `FootprintCompat`.**  A `LiftCompat` lens furnishes a `P`-compatible
    footprint (its own `footprint`): factor any confined program through the lens, then self-couple
    via `prhl2_of_inFootprint_lens`.  This is the *only* place the lens / `Nonempty` / factorization
    is needed — every downstream theorem takes a bare `FootprintCompat`. -/
theorem footprintCompat_of_lens {l advSt : Type} [Nonempty (ProcedureState l)]
    (L_adv : Lens advSt (ProcedureState l)) (hcompat : LiftCompat P L_adv) :
    FootprintCompat P L_adv.footprint :=
  fun hp => prhl2_of_inFootprint_lens L_adv hcompat hp


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


/-- **Confinement preserves a complement lens** (the frame linchpin).  A program confined to `R`
    leaves unchanged the content of any lens `u` disjoint from `R` (`u.footprint ≤ Rᶜ`): every
    output state agrees with the input on `u.get`.  Proved by an idempotent-fixpoint argument (no
    orbit collapse): `u.set (u.get σ)` is an `Rᶜ`-update fixing `σ`, so by `inFootprint_subprob`
    `p σ` is a fixpoint of pushing it, hence supported on `{s | u.get s = u.get σ}`. -/
theorem inFootprint_preserves_lens {s a γ : Type} {R : Footprint s} {p : ProgramDenotation s a}
    (hp : p.inFootprint R) (u : Lens γ s) (hu : u.footprint ≤ Rᶜ) (σ : s) :
    (p σ).satisfies (fun xs => u.get xs.2 = u.get σ) := by
  -- The localized update `f = u.set (u.get σ)` is a generator of `u.footprint`, hence an
  -- `Rᶜ`-update, and it fixes `σ` (lens law `get_set`).
  set f : Function.End s := u.liftFunction (fun _ => u.get σ) with hf_def
  have hgen : diracKer f ∈ u.footprint.updates :=
    (Footprint.from_le_iff (Set.range fun g : Function.End γ => diracKer (u.liftFunction g))
      u.footprint).mp le_rfl ⟨fun _ => u.get σ, rfl⟩
  have hmem : diracKer f ∈ Rᶜ.updates := hu hgen
  have hfix : f σ = σ := u.get_set σ
  -- Confinement makes `p σ` a fixpoint of pushing `f`.
  have hstep := inFootprint_subprob hp hmem σ
  rw [hfix] at hstep
  rw [hstep]
  -- Each pushed atom `u.set (u.get σ) xs.2` reads back `u.get σ` (lens law `set_get`).
  exact SubProbability.satisfies_bind _
    (fun xs _ => SubProbability.satisfies_pure _ _ (u.set_get xs.2 (u.get σ)))

/-- **Confinement preserves the complement content** (the lens-free frame linchpin).  When `R`
    collapses to `σ` (`HasOrbitCollapse`), a program confined to `R` leaves the whole `R`-complement
    content — the `R.global_getter` value — unchanged: every output lies in `σ`'s `R`-orbit.  The
    `Footprint`/`satisfies` analogue of `ProgramDenotation.inRange_orbit_of_collapse`: the collapse
    map `f ∈ Rᶜ` fixes `σ`, so `inFootprint_subprob` makes `p σ` a fixpoint of pushing `f`, and `f`
    lands every state in `σ`'s single-step `R`-orbit, killing the "not-reachable" outputs. -/
theorem inFootprint_preserves_global {s a : Type} {R : Footprint s} {p : ProgramDenotation s a}
    (hp : p.inFootprint R) {σ : s} (hcoll : R.HasOrbitCollapse σ) :
    (p σ).satisfies (fun xs => R.global_getter.get xs.2 = R.global_getter.get σ) := by
  obtain ⟨f, hf_in, hf_fix, hf_collapse⟩ := hcoll
  letI : MeasurableSpace (a × s) := ⊤
  -- Invariance: p σ = (p σ) >>= (fun (x, s') => pure (x, f s')).
  have h_inv : p σ
      = (p σ) >>= (fun (xs : a × s) => (pure (xs.1, f xs.2) : SubProbability (a × s))) := by
    have := inFootprint_subprob hp hf_in σ
    rwa [hf_fix] at this
  intro xs hxs
  -- Reduce the quotient equality to a single directed orbit step.
  change Quotient.mk R.orbit_setoid xs.2 = Quotient.mk R.orbit_setoid σ
  rw [Quotient.eq]
  suffices h : ∃ u : Function.End s, diracKer u ∈ R.updates ∧ u σ = xs.2 by
    obtain ⟨u, hu_in, hu_eq⟩ := h
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨u, hu_in, hu_eq⟩)
  by_contra hne
  simp only [not_exists, not_and] at hne
  -- `hne : ∀ u, diracKer u ∈ R.updates → u σ ≠ xs.2`; derive `(p σ).1 {xs} = 0`.
  apply hxs
  have hS_meas : MeasurableSet ({xs} : Set (a × s)) := trivial
  -- Rewrite (p σ).1 {xs} using invariance + map structure.
  have h_meas_eq : (p σ).1 {xs} = (p σ).1 {ws : a × s | (ws.1, f ws.2) ∈ ({xs} : Set (a × s))} := by
    conv_lhs => rw [h_inv]
    change (MeasureTheory.Measure.bind (p σ).1
              (fun ws => (pure (ws.1, f ws.2) : SubProbability (a × s)).1)) {xs}
         = (p σ).1 {ws : a × s | (ws.1, f ws.2) ∈ ({xs} : Set (a × s))}
    have hdirac : ∀ ws : a × s,
        ((pure (ws.1, f ws.2) : SubProbability (a × s)).1
          : MeasureTheory.Measure (a × s))
        = @MeasureTheory.Measure.dirac (a × s) ⊤ (ws.1, f ws.2) := fun _ => rfl
    simp_rw [hdirac]
    rw [MeasureTheory.Measure.bind_dirac_eq_map (p σ).1 measurable_from_top,
        MeasureTheory.Measure.map_apply measurable_from_top hS_meas]
    rfl
  -- The preimage is empty: `f` collapses every state into `R`-orbit(σ), which excludes `xs.2`.
  have h_empty : {ws : a × s | (ws.1, f ws.2) ∈ ({xs} : Set (a × s))} = (∅ : Set (a × s)) := by
    ext ⟨x, s'⟩
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
               Prod.ext_iff]
    rintro ⟨-, hfs⟩
    obtain ⟨u, hu_in, hu_eq⟩ := hf_collapse s'
    exact hne u hu_in (hu_eq.trans hfs)
  rw [h_meas_eq, h_empty]
  exact MeasureTheory.measure_empty

/-- **Glob-based `FootprintCompat`** (the endpoint, lens-free, `Q`-free).  Reduce `FootprintCompat P R`
    to two intrinsic properties of `liftRel P`, via the touched/untouched split (`R.touched_getter` /
    `R.global_getter`) plus orbit collapse of `R` (free for lens-derived `R`):
    * `hrefine` — `liftRel P` **refines `={glob A}`**: the touched content is pinned equal.
    * `hstable` — `liftRel P` is **frame-stable**: it depends only on the untouched content, so
      overwriting A's touched content identically on both sides (keeping the untouched content fixed)
      preserves it.

    Each confined program self-couples via `prhl2_glob` (touched stays equal) and
    `inFootprint_preserves_global` (untouched stays fixed), then `hstable` rebuilds `liftRel P`.  The
    EasyCrypt `={glob A}` route into theorem 2 — no `Lens`, and no auxiliary frame predicate. -/
theorem footprintCompat_of_glob {l : Type} {R : Footprint (ProcedureState l)}
    (hcoll : ∀ σ, R.HasOrbitCollapse σ)
    (hrefine : ∀ a b, liftRel P a b → R.touched_getter.get a = R.touched_getter.get b)
    (hstable : ∀ a b u v, liftRel P a b →
        R.touched_getter.get u = R.touched_getter.get v →
        R.global_getter.get u = R.global_getter.get a →
        R.global_getter.get v = R.global_getter.get b → liftRel P u v) :
    FootprintCompat P R := by
  intro γ' p hp x y hxy
  obtain ⟨μ, hm1, hm2, hsat⟩ := prhl2_glob hp x y (hrefine x y hxy)
  refine ⟨μ, hm1, hm2, ?_⟩
  -- Confinement preserves the untouched content on both marginals.
  have hgx := inFootprint_preserves_global hp (hcoll x)
  have hgy := inFootprint_preserves_global hp (hcoll y)
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
  -- `hstable` rebuilds `liftRel P` on the outputs from touched-agreement + preserved untouched.
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
    `fvP → ConfinedP → LocP → coupling → prhl` chain. -/
theorem prhl_instantiate_of_fvP {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hcompat : FootprintCompat P (fvP_proc A))
    (h : ∀ inp : input,
        ProgramDenotation.prhl P (random_oracle_query inp) (lazy_query inp) (liftPost P)) :
    ProgramDenotation.prhl P
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


/-- **Theorem 2 via `glob`** (the EasyCrypt-style endpoint, lens-free, `Q`-free).  Relational
    lazy ≈ eager for any adversary `A`, from two intrinsic properties of the invariant `liftRel P`
    over the touched/untouched split of `fvP_proc A`:
    * `hrefine` — `liftRel P` refines `={glob A}` (agreement on `A`'s touched content), and
    * `hstable` — `liftRel P` depends only on the untouched content (frame-stable: overwriting `A`'s
      touched content on both sides preserves it),
    plus orbit collapse of `fvP_proc A` (free for lens-derived footprints).  No `Lens`, no auxiliary
    frame predicate — the adversary assumption is exactly the glob split of the invariant. -/
theorem prhl_instantiate_of_glob {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hcoll : ∀ σ, (fvP_proc A).HasOrbitCollapse σ)
    (hrefine : ∀ a b, liftRel P a b →
        (fvP_proc A).touched_getter.get a = (fvP_proc A).touched_getter.get b)
    (hstable : ∀ a b u v, liftRel P a b →
        (fvP_proc A).touched_getter.get u = (fvP_proc A).touched_getter.get v →
        (fvP_proc A).global_getter.get u = (fvP_proc A).global_getter.get a →
        (fvP_proc A).global_getter.get v = (fvP_proc A).global_getter.get b → liftRel P u v)
    (h : ∀ inp : input,
        ProgramDenotation.prhl P (random_oracle_query inp) (lazy_query inp) (liftPost P)) :
    ProgramDenotation.prhl P
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (liftPost P) :=
  prhl_instantiate_of_fvP A args (footprintCompat_of_glob hcoll hrefine hstable) h

end GaudisCrypt.Lib.RO.Instantiate
