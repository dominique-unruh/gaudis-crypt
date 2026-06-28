import GaudisCrypt.Lib.RO.InstantiateCommon

/-!
# Prhl instantiate (theorem 2) — relational RO equivalence

Lazy/eager **relational** equivalence (`Program.prhl`, coupling) for a syntactic adversary: the
lifted invariant `liftRel`/`LocP`, the `prhl2` body induction, `prhl_instantiate`, and the
confinement end-points `prhl_instantiate_confinedP` / `prhl_instantiate_of_fvP`.
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
  Program.prhl2 (liftRel P) (Program.get g) (Program.get g) (liftRelPost P)


/-- Honest locality for theorem 2: every operation of `A` *outside the oracle*
    preserves the invariant relationally (self-couples under `liftRel P`).  The
    oracle hole is exempt (handled by the per-query hypothesis). -/
def LocP {holes : HoleSigs} {l : Type} (P : state → state → Prop) : StmtWithHoles holes l → Prop
  | .skip => True
  | .sample x e => Program.prhl2 (liftRel P) (programDenotation (StmtWithHoles.sample x e : Stmt l))
      (programDenotation (StmtWithHoles.sample x e : Stmt l)) (liftRelPost P)
  | .call' x ls b r p => Program.prhl2 (liftRel P)
      (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l))
      (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l)) (liftRelPost P)
  | .hole _ x p => GetOK P p ∧
      (∀ ret, Program.prhl2 (liftRel P) (Program.set x ret) (Program.set x ret) (liftRelPost P))
  | .seq s1 s2 => LocP P s1 ∧ LocP P s2
  | .ifThenElse c t e => GetOK P c ∧ LocP P t ∧ LocP P e
  | .while c t => GetOK P c ∧ LocP P t


/-- **Body induction**: an arbitrary adversary body `A` preserves the lifted
    invariant relationally, given `LocP` and a per-hole coupling `hhole` (the
    oracle preserves the invariant).  `[Countable l]` feeds the `prhl2`
    composition rules (`bind`/`cond`/`while_loop`). -/
theorem body_prhl2_gen {P : state → state → Prop} :
    ∀ {holes : HoleSigs} {l : Type} (A : StmtWithHoles holes l)
      (eagerInst lazyInst : holes.Instantiation),
      LocP P A →
      (∀ {sig} (n : HoleIndex holes sig)
          (x : Setter sig.ret (ProcedureState l))
          (p : Getter sig.ParamType (ProcedureState l)),
          GetOK P p →
          (∀ ret, Program.prhl2 (liftRel P) (Program.set x ret) (Program.set x ret) (liftRelPost P)) →
          Program.prhl2 (liftRel P)
            (programDenotation (StmtWithHoles.call x (eagerInst n) p))
            (programDenotation (StmtWithHoles.call x (lazyInst n) p)) (liftRelPost P)) →
      Program.prhl2 (liftRel P)
        (programDenotation (A.instantiate eagerInst))
        (programDenotation (A.instantiate lazyInst)) (liftRelPost P) := by
  intro holes l A
  induction A with
  | skip =>
      intro eagerInst lazyInst _ _
      simp only [StmtWithHoles.instantiate, programDenotation, Program.skip]
      exact Program.prhl2.pure_pure (fun _ _ h => ⟨rfl, h⟩)
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
      refine Program.prhl2.bind (ih1 eagerInst lazyInst hloc.1 hhole) (fun _ _ => ?_)
      exact Program.prhl2.conseq (ih2 eagerInst lazyInst hloc.2 hhole)
        (fun _ _ hpre => hpre.2) (fun _ _ hB => hB)
  | ifThenElse c t e iht ihe =>
      intro eagerInst lazyInst hloc hhole
      simp only [StmtWithHoles.instantiate, programDenotation]
      exact Program.prhl2.cond hloc.1 (iht eagerInst lazyInst hloc.2.1 hhole)
        (ihe eagerInst lazyInst hloc.2.2 hhole)
  | «while» c t iht =>
      intro eagerInst lazyInst hloc hhole
      simp only [StmtWithHoles.instantiate, programDenotation]
      refine Program.prhl2.conseq
        (Program.prhl2.while_loop (PostC := fun _ => liftRel P) hloc.1 ?_)
        (fun _ _ h => h) (fun _ _ hB => ⟨rfl, hB⟩)
      exact Program.prhl2.conseq (iht eagerInst lazyInst hloc.2 hhole)
        (fun _ _ h => h) (fun _ _ hB => hB.2)


/-- **Coupling lift through `zoom globalL`** (the `prhl2` analogue of
    `transferBy_zoom`): a state-level coupling of `c`, `d` under `P` lifts to a
    `ProcedureState` coupling of their `zoom`s under `liftRel P`, threading the
    (equal) locals.  Used to lift the per-query hypothesis `h` to the oracle hole. -/
theorem prhl2_zoom (l : Type) {γ : Type} {P : state → state → Prop}
    {c d : Program state γ} {B : γ × state → γ × state → Prop}
    (hcd : Program.prhl2 P c d B) :
    Program.prhl2 (liftRel (l := l) P)
      (Program.zoom (ProcedureState.globalL (l := l)) c)
      (Program.zoom (ProcedureState.globalL (l := l)) d)
      (fun u v => B (u.1, u.2.global) (v.1, v.2.global) ∧ u.2.locals = v.2.locals) := by
  intro ps₁ ps₂ hrel
  obtain ⟨μ, hm1, hm2, hsat⟩ := hcd ps₁.global ps₂.global hrel.1
  refine ⟨μ >>= fun w => pure ((w.1.1, (⟨w.1.2, ps₁.locals⟩ : ProcedureState l)),
                               (w.2.1, (⟨w.2.2, ps₂.locals⟩ : ProcedureState l))), ?_, ?_, ?_⟩
  · rw [SubProbability.bind_assoc']
    simp only [SubProbability.pure_bind]
    show (μ >>= fun w => pure (w.1.1, (⟨w.1.2, ps₁.locals⟩ : ProcedureState l)))
        = c ps₁.global >>= fun as => pure (as.1, (⟨as.2, ps₁.locals⟩ : ProcedureState l))
    rw [← hm1, SubProbability.bind_assoc']
    simp only [SubProbability.pure_bind]
  · rw [SubProbability.bind_assoc']
    simp only [SubProbability.pure_bind]
    show (μ >>= fun w => pure (w.2.1, (⟨w.2.2, ps₂.locals⟩ : ProcedureState l)))
        = d ps₂.global >>= fun as => pure (as.1, (⟨as.2, ps₂.locals⟩ : ProcedureState l))
    rw [← hm2, SubProbability.bind_assoc']
    simp only [SubProbability.pure_bind]
  · exact SubProbability.satisfies_bind _
      (fun w hw => SubProbability.satisfies_pure _ _ ⟨hsat w hw, hrel.2⟩)


/-- **RO hole coupling**: the eager/lazy oracle calls couple under `liftRel P`,
    given the surrounding read/write are `liftRel`-preserving.  The query couples
    via `prhl2_zoom` of the per-query hypothesis `h` (with the bridges identifying
    the procedures with the semantic queries).  This is `body_prhl2_gen`'s `hhole`
    for the RO instantiation. -/
theorem ro_hhole_prhl {l : Type} {P : state → state → Prop}
    (h : ∀ inp : input, Program.prhl P (random_oracle_query inp) (lazy_query inp) (liftPost P))
    {sig : ProcedureSignature} (n : HoleIndex roHoles sig)
    (x : Setter sig.ret (ProcedureState l)) (p : Getter sig.ParamType (ProcedureState l))
    (hp : GetOK P p)
    (hx : ∀ ret, Program.prhl2 (liftRel P) (Program.set x ret) (Program.set x ret) (liftRelPost P)) :
    Program.prhl2 (liftRel P)
      (programDenotation (StmtWithHoles.call x (RO_eager n) p))
      (programDenotation (StmtWithHoles.call x (RO_lazy n) p)) (liftRelPost P) := by
  cases n with
  | zero =>
      haveI : Countable roSig.ParamType := inferInstanceAs (Countable input)
      haveI : Countable roSig.ret := inferInstanceAs (Countable output)
      show Program.prhl2 (liftRel P)
          (programDenotation (StmtWithHoles.call x RO_eager_proc p))
          (programDenotation (StmtWithHoles.call x RO_lazy_proc p)) (liftRelPost P)
      rw [denote_call, denote_call]
      refine Program.prhl2.bind hp (fun args₁ args₂ => ?_)
      intro σ₁ σ₂ hpre
      obtain ⟨rfl, hrel⟩ := hpre
      refine (Program.prhl2.bind (M := liftRelPost P) ?_ (fun ret₁ ret₂ => ?_)) σ₁ σ₂ hrel
      · -- the zoomed query couples (via `prhl2_zoom`); post normalized to `liftRelPost P`
        rw [procDenotation_RO_eager, procDenotation_RO_lazy]
        exact Program.prhl2.conseq (prhl2_zoom l ((h args₁).to_prhl2))
          (fun _ _ h => h) (fun _ _ hB => ⟨hB.1.1, hB.1.2, hB.2⟩)
      · -- the write couples (equal results from the middle post)
        intro τ₁ τ₂ hpre2
        obtain ⟨rfl, hrel2⟩ := hpre2
        exact hx ret₁ τ₁ τ₂ hrel2
  | succ m => nomatch m


/-- **Body-level theorem 2** — fully assembled: an arbitrary `Loc`al adversary
    body preserves the invariant relationally, with the RO oracle.  Combines
    `body_prhl2_gen` with the RO hole coupling `ro_hhole_prhl`. -/
theorem prhl_instantiate_body {l : Type} {P : state → state → Prop}
    (h : ∀ inp : input, Program.prhl P (random_oracle_query inp) (lazy_query inp) (liftPost P))
    (A : StmtWithHoles roHoles l) (hloc : LocP P A) :
    Program.prhl2 (liftRel P)
      (programDenotation (A.instantiate RO_eager))
      (programDenotation (A.instantiate RO_lazy)) (liftRelPost P) :=
  body_prhl2_gen A RO_eager RO_lazy hloc (fun n x p hp hx => ro_hhole_prhl h n x p hp hx)


/-- **Procedure wrapper for `prhl`** (isolated, analogue of `transfer_wrapper`):
    a body-level `prhl2` coupling lifts to a state-level `prhl` coupling of the
    whole procedure, given the return value is determined by the invariant. -/
theorem prhl_wrapper {sig : ProcedureSignature} {P : state → state → Prop}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hbody : Program.prhl2 (liftRel P)
      (programDenotation (A.body.instantiate RO_eager))
      (programDenotation (A.body.instantiate RO_lazy)) (liftRelPost P))
    (hret : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → A.return_val.get ps₁ = A.return_val.get ps₂) :
    Program.prhl P
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args) (liftPost P) := by
  apply Program.prhl2.to_prhl
  intro st₁ st₂ hP
  obtain ⟨μ, hm1, hm2, hsat⟩ :=
    hbody ⟨st₁, sig.localVariableInit A.locals args⟩ ⟨st₂, sig.localVariableInit A.locals args⟩ ⟨hP, rfl⟩
  refine ⟨μ >>= fun w => pure ((A.return_val.get w.1.2, w.1.2.global),
                               (A.return_val.get w.2.2, w.2.2.global)), ?_, ?_, ?_⟩
  · rw [SubProbability.bind_assoc']
    simp only [SubProbability.pure_bind]
    rw [procedureDenotation_eq_procWrap]
    show (μ >>= fun w => pure (A.return_val.get w.1.2, w.1.2.global))
        = (programDenotation (A.body.instantiate RO_eager))
            ⟨st₁, sig.localVariableInit A.locals args⟩ >>= fun p => pure (A.return_val.get p.2, p.2.global)
    rw [← hm1, SubProbability.bind_assoc']
    simp only [SubProbability.pure_bind]
  · rw [SubProbability.bind_assoc']
    simp only [SubProbability.pure_bind]
    rw [procedureDenotation_eq_procWrap]
    show (μ >>= fun w => pure (A.return_val.get w.2.2, w.2.2.global))
        = (programDenotation (A.body.instantiate RO_lazy))
            ⟨st₂, sig.localVariableInit A.locals args⟩ >>= fun p => pure (A.return_val.get p.2, p.2.global)
    rw [← hm2, SubProbability.bind_assoc']
    simp only [SubProbability.pure_bind]
  · refine SubProbability.satisfies_bind _ (fun w hw => SubProbability.satisfies_pure _ _ ?_)
    have hlr := hsat w hw
    exact ⟨hret w.1.2 w.2.2 hlr.2, hlr.2.1⟩


/-- **`prhl_instantiate`** (subtask 3, theorem 2).

Given a state invariant `P` that (a) is preserved relationally by a single oracle
query (`h`), and (b) is preserved by `A`'s own operations (`hloc`, the honest
locality; `fv_proc` is unusable while its leaves are `sorry`) and its return read
(`hret`), the eager and lazy instantiations of `A` are related by `Program.prhl`
under `P`.  Reduces to `prhl_instantiate_body` via `prhl_wrapper`. -/
theorem prhl_instantiate {sig : ProcedureSignature} {P : state → state → Prop}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (h : ∀ inp : input,
        Program.prhl P (random_oracle_query inp) (lazy_query inp) (liftPost P))
    (hloc : LocP P A.body)
    (hret : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → A.return_val.get ps₁ = A.return_val.get ps₂) :
    Program.prhl P
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (liftPost P) :=
  prhl_wrapper A args (prhl_instantiate_body h A.body hloc) hret


/-- A program confined to an adversary lens `L_adv` self-couples under `liftRel P`
    — the lift form (mirrors `Program.prhl2.adversary`).  The two compatibility
    conditions are: `heq` — `liftRel P` forces equality on `L_adv` (so the inner
    program gets equal inputs); `hset` — writing the (equal) result back into
    `L_adv` preserves `liftRel P`. -/
theorem prhl2_lift_lens {l γ advSt : Type}
    {P : state → state → Prop} (L_adv : Lens advSt (ProcedureState l))
    (heq : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → L_adv.get ps₁ = L_adv.get ps₂)
    (hset : ∀ (c : advSt) ps₁ ps₂, liftRel P ps₁ ps₂ →
        liftRel P (L_adv.set c ps₁) (L_adv.set c ps₂))
    (p' : Program advSt γ) :
    Program.prhl2 (liftRel P) (L_adv.lift p') (L_adv.lift p') (liftRelPost P) := by
  intro ps₁ ps₂ hpre
  refine ⟨p' (L_adv.get ps₁) >>= fun xc =>
      pure ((xc.1, L_adv.set xc.2 ps₁), (xc.1, L_adv.set xc.2 ps₂)), ?_, ?_, ?_⟩
  · rw [SubProbability.bind_assoc']; simp only [SubProbability.pure_bind]; rfl
  · rw [SubProbability.bind_assoc']; simp only [SubProbability.pure_bind]
    rw [show L_adv.get ps₁ = L_adv.get ps₂ from heq ps₁ ps₂ hpre]; rfl
  · exact SubProbability.satisfies_bind _ (fun xc _ =>
      SubProbability.satisfies_pure _ _ ⟨rfl, hset xc.2 ps₁ ps₂ hpre⟩)


/-- **Theorem-2 leaf discharge** (probabilistic). A program confined (in the `inProbRange` sense)
    to an adversary lens `L_adv` compatible with `liftRel P` self-couples. The `ProbLensRange`
    analogue of `prhl2_of_inRange_lens` — factors through `factor_of_inProbRange` and the
    *range-independent* `prhl2_lift_lens` (reused verbatim). -/
theorem prhl2_of_inProbRange_lens {l γ advSt : Type} [Nonempty (ProcedureState l)]
    {P : state → state → Prop}
    (L_adv : Lens advSt (ProcedureState l))
    (heq : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → L_adv.get ps₁ = L_adv.get ps₂)
    (hset : ∀ (c : advSt) ps₁ ps₂, liftRel P ps₁ ps₂ →
        liftRel P (L_adv.set c ps₁) (L_adv.set c ps₂))
    {p : Program (ProcedureState l) γ} (hp : p.inProbRange L_adv.probRange) :
    Program.prhl2 (liftRel P) p p (liftRelPost P) := by
  rw [factor_of_inProbRange L_adv hp]
  exact prhl2_lift_lens L_adv heq hset (L_adv.factor p)


/-- **`ConfinedP` discharges `LocP`** (theorem-2 locality) for any invariant `P` — the
    `ProbLensRange` analogue of `confined_locP`. -/
theorem confinedP_locP {holes : HoleSigs} {l advSt : Type} [Nonempty (ProcedureState l)]
    {P : state → state → Prop}
    (L_adv : Lens advSt (ProcedureState l))
    (heq : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → L_adv.get ps₁ = L_adv.get ps₂)
    (hset : ∀ (c : advSt) ps₁ ps₂, liftRel P ps₁ ps₂ →
        liftRel P (L_adv.set c ps₁) (L_adv.set c ps₂))
    (hc : ∀ {sig : ProcedureSignature}, HoleIndex holes sig → Countable sig.ParamType) :
    ∀ (A : StmtWithHoles holes l), ConfinedP L_adv A → LocP P A
  | .skip, _ => trivial
  | .sample _ _, h => prhl2_of_inProbRange_lens L_adv heq hset h
  | .call' _ _ _ _ _, h => prhl2_of_inProbRange_lens L_adv heq hset h
  | .hole n _ _, h =>
      haveI := hc n
      ⟨prhl2_of_inProbRange_lens L_adv heq hset h.1,
        fun ret => prhl2_of_inProbRange_lens L_adv heq hset (h.2 ret)⟩
  | .seq s1 s2, h =>
      ⟨confinedP_locP L_adv heq hset hc s1 h.1, confinedP_locP L_adv heq hset hc s2 h.2⟩
  | .ifThenElse _ t e, h =>
      ⟨prhl2_of_inProbRange_lens L_adv heq hset h.1, confinedP_locP L_adv heq hset hc t h.2.1,
        confinedP_locP L_adv heq hset hc e h.2.2⟩
  | .«while» _ t, h =>
      ⟨prhl2_of_inProbRange_lens L_adv heq hset h.1, confinedP_locP L_adv heq hset hc t h.2⟩


/-- **Theorem 2, probabilistic confinement form (general adversary lens).**  The `ProbLensRange`
    rendering of `prhl_instantiate_confined`; reuses the existing `LocP`→`prhl_instantiate` chain
    via `confinedP_locP`. -/
theorem prhl_instantiate_confinedP {sig : ProcedureSignature} {advSt : Type}
    {P : state → state → Prop}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (L_adv : Lens advSt (ProcedureState (sig.LocalVariableState A.locals)))
    (heq : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → L_adv.get ps₁ = L_adv.get ps₂)
    (hset : ∀ (c : advSt) ps₁ ps₂, liftRel P ps₁ ps₂ →
        liftRel P (L_adv.set c ps₁) (L_adv.set c ps₂))
    [Nonempty (ProcedureState (sig.LocalVariableState A.locals))]
    (h : ∀ inp : input,
        Program.prhl P (random_oracle_query inp) (lazy_query inp) (liftPost P))
    (hconf : ConfinedP L_adv A.body)
    (hret : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → A.return_val.get ps₁ = A.return_val.get ps₂) :
    Program.prhl P
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (liftPost P) :=
  prhl_instantiate A args h
    (confinedP_locP L_adv heq hset roHole_paramType_countable A.body hconf) hret


/-- **Theorem 2, end-to-end from footprint disjointness.**  The relational (coupling) equivalence
    for an invariant `P`, from the body's footprint lying in a `liftRel P`-compatible region `L_adv`
    — the full `fvP → ConfinedP → LocP → prhl` chain in one step. -/
theorem prhl_instantiate_of_fvP {sig : ProcedureSignature} {advSt : Type}
    {P : state → state → Prop}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (L_adv : Lens advSt (ProcedureState (sig.LocalVariableState A.locals)))
    (heq : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → L_adv.get ps₁ = L_adv.get ps₂)
    (hset : ∀ (c : advSt) ps₁ ps₂, liftRel P ps₁ ps₂ →
        liftRel P (L_adv.set c ps₁) (L_adv.set c ps₂))
    [Nonempty (ProcedureState (sig.LocalVariableState A.locals))]
    (h : ∀ inp : input,
        Program.prhl P (random_oracle_query inp) (lazy_query inp) (liftPost P))
    (hbody : fvP_stmt A.body ≤ L_adv.probRange)
    (hret : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → A.return_val.get ps₁ = A.return_val.get ps₂) :
    Program.prhl P
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (liftPost P) :=
  prhl_instantiate_confinedP A args L_adv heq hset h
    (confinedP_of_fv L_adv roHole_paramType_countable A.body hbody) hret

end GaudisCrypt.Lib.RO.Instantiate
