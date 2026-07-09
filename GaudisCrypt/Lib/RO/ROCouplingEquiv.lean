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

open GaudisCrypt
open GaudisCrypt
open GaudisCrypt
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


/-- **Oracle-agnostic procedure wrapper for `prhl2`** (the generalization of `prhl_wrapper`):
    a body-level `prhl2` coupling of `A`'s body under two *arbitrary* hole-instantiations
    `eagerInst`/`lazyInst` lifts to a state-level `prhl2` coupling of the whole procedure, given the
    return value is determined by the invariant.  The proof never inspects the instantiations (only
    uses them via `A.instantiate`/`procedureDenotation`), so `RO_eager`/`RO_lazy` were incidental. -/
theorem prhl_wrapper_gen {holes : HoleSigs} {sig : ProcedureSignature}
    (eagerInst lazyInst : holes.Instantiation)
    (A : ProcedureWithHoles holes sig) (args : sig.ParamType)
    (hbody : ProgramDenotation.prhl2 (liftRel P)
      (programDenotation (A.body.instantiate eagerInst))
      (programDenotation (A.body.instantiate lazyInst)) (liftRelPost P))
    (hret : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → A.return_val.get ps₁ = A.return_val.get ps₂) :
    ProgramDenotation.prhl2 P
      (procedureDenotation (A.instantiate eagerInst) args)
      (procedureDenotation (A.instantiate lazyInst) args) (liftPost P) := by
  intro st₁ st₂ hP
  obtain ⟨μ, hm1, hm2, hsat⟩ :=
    hbody ⟨st₁, sig.localVariableInit A.locals args⟩ ⟨st₂, sig.localVariableInit A.locals args⟩ ⟨hP, rfl⟩
  refine ⟨μ >>= fun w => pure ((A.return_val.get w.1.2, w.1.2.global),
                               (A.return_val.get w.2.2, w.2.2.global)), ?_, ?_, ?_⟩
  · simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
    rw [procedureDenotation_eq_procWrap_gen]
    show (μ >>= fun w => pure (A.return_val.get w.1.2, w.1.2.global))
        = (programDenotation (A.body.instantiate eagerInst))
            ⟨st₁, sig.localVariableInit A.locals args⟩ >>= fun p => pure (A.return_val.get p.2, p.2.global)
    rw [← hm1]
    simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
  · simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
    rw [procedureDenotation_eq_procWrap_gen]
    show (μ >>= fun w => pure (A.return_val.get w.2.2, w.2.2.global))
        = (programDenotation (A.body.instantiate lazyInst))
            ⟨st₂, sig.localVariableInit A.locals args⟩ >>= fun p => pure (A.return_val.get p.2, p.2.global)
    rw [← hm2]
    simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
  · refine SubProbability.satisfies_bind _ (fun w hw => SubProbability.satisfies_pure _ _ ?_)
    have hlr := hsat w hw
    exact ⟨hret w.1.2 w.2.2 hlr.2, hlr.2.1⟩

/-- **Procedure wrapper for `prhl2`** (isolated, analogue of `transfer_wrapper`):
    a body-level `prhl2` coupling lifts to a state-level `prhl2` coupling of the
    whole procedure, given the return value is determined by the invariant.  The RO instantiation of
    the oracle-agnostic `prhl_wrapper_gen`. -/
theorem prhl_wrapper {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hbody : ProgramDenotation.prhl2 (liftRel P)
      (programDenotation (A.body.instantiate RO_eager))
      (programDenotation (A.body.instantiate RO_lazy)) (liftRelPost P))
    (hret : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → A.return_val.get ps₁ = A.return_val.get ps₂) :
    ProgramDenotation.prhl2 P
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args) (liftPost P) :=
  prhl_wrapper_gen RO_eager RO_lazy A args hbody hret


/-! ## Layer 3 — confinement endpoints (discharge `LocP` from a footprint) -/


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


/-- **Oracle-agnostic footprint endpoint** (the generalization of `prhl_instantiate_of_fvP`).
    Relational (coupling) `A[eager] ≈ A[lazy]` for an invariant `P` under two *arbitrary*
    hole-instantiations `eagerInst`/`lazyInst`, given (1) `A`'s own footprint `fvP_proc A` is
    `P`-compatible (`FootprintCompat P (fvP_proc A)`) and (2) a per-hole coupling `hhole` (the oracle
    call preserves the invariant).  Nothing about the specific oracle enters: this inlines the
    `fvP → ConfinedP → LocP → coupling → prhl2` chain with `RO_eager`/`RO_lazy` replaced by the
    given instantiations and `ro_hhole_prhl` replaced by `hhole`. -/
theorem instantiate_of_fvP_gen {holes : HoleSigs} {sig : ProcedureSignature}
    (eagerInst lazyInst : holes.Instantiation)
    (A : ProcedureWithHoles holes sig) (args : sig.ParamType)
    (hcompat : FootprintCompat P (fvP_proc A))
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (hhole : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig')
        (x : Setter sig'.ret (ProcedureState (sig.LocalVariableState A.locals)))
        (p : Getter sig'.ParamType (ProcedureState (sig.LocalVariableState A.locals))),
        GetOK P p →
        (∀ ret, ProgramDenotation.prhl2 (liftRel P) (ProgramDenotation.set x ret)
            (ProgramDenotation.set x ret) (liftRelPost P)) →
        ProgramDenotation.prhl2 (liftRel P)
          (programDenotation (StmtWithHoles.call x (eagerInst n) p))
          (programDenotation (StmtWithHoles.call x (lazyInst n) p)) (liftRelPost P)) :
    ProgramDenotation.prhl2 P
      (procedureDenotation (A.instantiate eagerInst) args)
      (procedureDenotation (A.instantiate lazyInst) args)
      (liftPost P) :=
  prhl_wrapper_gen eagerInst lazyInst A args
    (body_prhl2_gen A.body eagerInst lazyInst
      (confinedP_locP (fvP_proc A) hcompat hc A.body
        (confinedP_of_fv (fvP_proc A) hc A.body
          (fvP_stmt_body_le_fvP_proc A)))
      (fun n x p hp hx => hhole n x p hp hx))
    (fun _ _ hpre => reads_equal_of_footprintCompat hcompat
      (ProgramDenotation.inFootprint_of_footprint_le (get_return_val_le_fvP_proc A)) hpre)

/-- **Oracle-agnostic glob endpoint** — the oracle-agnostic *core* of `prhl_instantiate_of_glob`.
    Relational (coupling) `A[eager] ≈ A[lazy]` for an invariant `P` under two *arbitrary*
    hole-instantiations `eagerInst`/`lazyInst`, from a **footprint-disjointness** hypothesis against an
    arbitrary *resettable* oracle region `O` (`hdisj : fvP_proc A ≤ Oᶜ`) plus the glob-split conditions
    (`hrefine`/`hstable`) on `liftRel P` over the split into the outside-`O` content (`Oᶜ.touched_getter`)
    and `O`'s content (`O.touched_getter`), a countability plumbing `hc`, and a per-hole coupling
    `hhole`.

    Instantiate with `(RO_eager, RO_lazy, roLift.footprint, ro_hhole_prhl h)` for the **random oracle**
    (this is exactly how `prhl_instantiate_of_glob` is derived).  A **random-permutation oracle** would
    be another instantiation: it supplies its own two hole-instantiations, its permutation-table region
    as `O`, and its collision-avoiding per-hole coupling as `hhole`.  The middle
    (`footprintCompat_of_glob` + `FootprintCompat.mono` + wrapper + body induction) is oracle-agnostic
    and lives here; the caller supplies only the oracle-specific ingredients. -/
theorem instantiate_of_glob_gen {holes : HoleSigs} {sig : ProcedureSignature}
    (eagerInst lazyInst : holes.Instantiation)
    (A : ProcedureWithHoles holes sig) (args : sig.ParamType)
    (O : Footprint (ProcedureState (sig.LocalVariableState A.locals)))
    (hO : ∀ σ, O.HasReset σ)
    (hdisj : fvP_proc A ≤ Oᶜ)
    (hrefine : ∀ a b, liftRel P a b → Oᶜ.touched_getter.get a = Oᶜ.touched_getter.get b)
    (hstable : ∀ a b u v, liftRel P a b →
        Oᶜ.touched_getter.get u = Oᶜ.touched_getter.get v →
        O.touched_getter.get u = O.touched_getter.get a →
        O.touched_getter.get v = O.touched_getter.get b → liftRel P u v)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (hhole : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig')
        (x : Setter sig'.ret (ProcedureState (sig.LocalVariableState A.locals)))
        (p : Getter sig'.ParamType (ProcedureState (sig.LocalVariableState A.locals))),
        GetOK P p →
        (∀ ret, ProgramDenotation.prhl2 (liftRel P) (ProgramDenotation.set x ret)
            (ProgramDenotation.set x ret) (liftRelPost P)) →
        ProgramDenotation.prhl2 (liftRel P)
          (programDenotation (StmtWithHoles.call x (eagerInst n) p))
          (programDenotation (StmtWithHoles.call x (lazyInst n) p)) (liftRelPost P)) :
    ProgramDenotation.prhl2 P
      (procedureDenotation (A.instantiate eagerInst) args)
      (procedureDenotation (A.instantiate lazyInst) args)
      (liftPost P) :=
  instantiate_of_fvP_gen eagerInst lazyInst A args
    (FootprintCompat.mono
      (footprintCompat_of_glob (R := Oᶜ) (O := O)
        (le_of_eq (Footprint.compl_compl _).symm) hO hrefine hstable)
      hdisj)
    hc hhole

/-- **Theorem 2 — the entry point.**  Relational (coupling) lazy ≈ eager equivalence for an
    invariant `P`, for any adversary whose own footprint `fvP_proc A` (body + return) is
    `P`-compatible (`FootprintCompat P (fvP_proc A)`).  This is the weakest such hypothesis — only
    `A`'s actual footprint need be compatible, not a larger region — and it subsumes the explicit
    RO-disjointness premise (for the canonical RO-agreement `P`, `FootprintCompat P (fvP_proc A)`
    *is* "`A` is disjoint from the random oracle").  Lens-free, `R`-free; the RO instantiation of the
    oracle-agnostic `instantiate_of_fvP_gen`. -/
theorem prhl_instantiate_of_fvP {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hcompat : FootprintCompat P (fvP_proc A))
    (h : ∀ inp : input,
        ProgramDenotation.prhl2 P (random_oracle_query inp) (lazy_query inp) (liftPost P)) :
    ProgramDenotation.prhl2 P
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (liftPost P) :=
  instantiate_of_fvP_gen RO_eager RO_lazy A args hcompat roHole_paramType_countable
    (fun n x p hp hx => ro_hhole_prhl h n x p hp hx)


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
  instantiate_of_glob_gen RO_eager RO_lazy A args
    (O := (roLift (sig.LocalVariableState A.locals)).footprint)
    (fun σ => Lens.footprint_hasReset _ σ)
    (fvP_proc_le_roLift_compl A hdisj)
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
        exact (Lens.footprint_touched_getter_eq_iff _ v b).mp hgv)
    roHole_paramType_countable
    (fun n x p hp hx => ro_hhole_prhl h n x p hp hx)

/-- **Output-decided game transfer for an abstract adversary** (the collision-resistance shape).  For
    *any* adversary `A` disjoint from the oracle and *any* predicate `Win` on its result, the eager
    and lazy instantiations couple so the win event coincides: `A` wins against the eager (real)
    oracle **iff** against the lazy one.  Immediate from `prhl_instantiate_of_glob`, which equates the
    two results (`u.1 = v.1`) — so *any* event decided by `A`'s output transfers, regardless of the
    full oracle table.  **Collision resistance** is the instance where `Win r` reads "`r` is a
    collision `A` produced" (e.g. two distinct queried inputs whose observed answers are equal). -/
theorem output_win_transfer {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType) (Win : sig.ret → Prop)
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
      (fun u v => Win u.1 ↔ Win v.1) :=
  (prhl_instantiate_of_glob A args hdisj hrefine hstable h).conseq (fun _ _ hp => hp)
    (fun _ _ hlift => by rw [hlift.1])

/- The read-only-tests sketch that lived here is formalized in `GaudisCrypt/Footprint.lean`:
`Footprint.testsOf`, `Footprint.indistinguishable` (with `indistinguishable_iff_testsOf`), and
the touched-getter soundness `Footprint.indistinguishable_of_touched_getter_eq`. -/

end GaudisCrypt.Lib.RO.Instantiate
