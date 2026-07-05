import GaudisCrypt.Lib.RO.InstantiateCommon

/-!
# Transfer instantiate (theorem 1)

Lazy/eager **distribution** equivalence (`ProgramDenotation.transfer`) for a syntactic adversary:
    the
`transferBy` calculus, `Stable`/`Loc`, the body/wrapper lemmas, and the single confinement entry
point `ProgramDenotation.transfer_instantiate_of_fvP`.
-/

namespace GaudisCrypt.Lib.RO.Instantiate

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics
open GaudisCrypt.Language.Programs
open Classical


/-! ## The generic `transferBy` calculus

`ProgramDenotation.transfer` is `transferBy convert`.  We need the same relation
at the `ProcedureState` level (with `convertL`), so we use the generic calculus
`ProgramDenotation.transferBy` from `GaudisCrypt.Logic.TransferBy` — monad-law
combinators, the Kleene `while_loop` closure, and the `zoom` lifting lemma
(`convertL = zoom globalL convert`, and `zoom` is a monad morphism, so any
state-level transfer lifts to a zoomed `ProcedureState` one). -/

open GaudisCrypt.Language.Semantics.ProgramDenotation
  (transferBy transferBy_pure transferBy_bind transferBy_zoom)


/-! ## Honest locality + the body induction

`fv_proc` is `sorry` in `FV.lean`, and a *computed* footprint for an opaque
getter/setter is genuinely undefinable.  The honest, usable locality condition
is **semantic**: each of the adversary's own operations commutes with `convert`
(i.e. transfers to itself).  `Loc A` collects exactly these per-leaf facts.  The
oracle hole is exempt — it is handled by the `hhole` hypothesis (later
discharged by the per-query transfer lemma). -/

/-- `p` commutes with `convertL` ("transfers to itself"). -/
def Stable {l α : Type} (p : ProgramDenotation (ProcedureState l) α) : Prop :=
  transferBy convertL p p


/-- Locality: every operation of `A` *outside the oracle interface* is `Stable`.
    For a hole, this is the surrounding read (`get p`) and write (`set x`) — the
    oracle query itself is *not* required stable (it transfers, lazy↦eager). -/
def Loc {holes : HoleSigs} {l : Type} : StmtWithHoles holes l → Prop
  | .skip => True
  | .sample x e => Stable (programDenotation (StmtWithHoles.sample x e : Stmt l))
  | .call' x ls b r p => Stable (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l))
  | .hole _ x p => Stable (ProgramDenotation.get p) ∧ (∀ ret, Stable (ProgramDenotation.set x ret))
  | .seq s1 s2 => Loc s1 ∧ Loc s2
  | .ifThenElse c t e => Stable (ProgramDenotation.get c) ∧ Loc t ∧ Loc e
  | .while c t => Stable (ProgramDenotation.get c) ∧ Loc t

/-- **The former hard lemma** (now proved): `transferBy convertL` is closed under
    `while_loop`.  Instantiates the generic Kleene closure
    `ProgramDenotation.transferBy_while_loop` with `c := convertL`; the
    condition's self-transfer is literally `Stable c`. -/
theorem transferL_while_loop {l : Type} {c : ProgramDenotation (ProcedureState l) Bool}
    {body_lazy body_eager : ProgramDenotation (ProcedureState l) Unit}
    (hc : Stable c) (hbody : transferBy convertL body_lazy body_eager) :
    transferBy convertL (while_loop c body_lazy) (while_loop c body_eager) :=
  ProgramDenotation.transferBy_while_loop hc hbody


/-- **Body induction**: an arbitrary syntactic adversary `A` transfers from its
    lazy to its eager instantiation, given locality (`Loc`) of its own operations
    and a per-hole transfer hypothesis (`hhole`).  Generic over the holes so the
    induction goes through; specialized to the RO hole below. -/
theorem body_transfer_gen :
    ∀ {holes : HoleSigs} {l : Type} (A : StmtWithHoles holes l)
      (lazyInst eagerInst : holes.Instantiation),
      Loc A →
      (∀ {sig} (n : HoleIndex holes sig)
          (x : Setter sig.ret (ProcedureState l))
          (p : Getter sig.ParamType (ProcedureState l)),
          Stable (ProgramDenotation.get p) → (∀ ret, Stable (ProgramDenotation.set x ret)) →
          transferBy convertL (programDenotation (StmtWithHoles.call x (lazyInst n) p))
            (programDenotation (StmtWithHoles.call x (eagerInst n) p))) →
      transferBy convertL (programDenotation (A.instantiate lazyInst))
        (programDenotation (A.instantiate eagerInst)) := by
  intro holes l A
  induction A with
  | skip =>
      intro lazyInst eagerInst _ _
      simp only [StmtWithHoles.instantiate, programDenotation]
      exact transferBy_pure ()
  | sample x e =>
      intro lazyInst eagerInst hloc _
      simp only [StmtWithHoles.instantiate]
      exact hloc
  | call' x ls b r p =>
      intro lazyInst eagerInst hloc _
      simp only [StmtWithHoles.instantiate]
      exact hloc
  | hole n x p =>
      intro lazyInst eagerInst hloc hhole
      simp only [StmtWithHoles.instantiate]
      exact hhole n x p hloc.1 hloc.2
  | seq s1 s2 ih1 ih2 =>
      intro lazyInst eagerInst hloc hhole
      simp only [StmtWithHoles.instantiate, programDenotation]
      exact transferBy_bind (ih1 lazyInst eagerInst hloc.1 hhole)
        (fun _ => ih2 lazyInst eagerInst hloc.2 hhole)
  | ifThenElse c t e iht ihe =>
      intro lazyInst eagerInst hloc hhole
      simp only [StmtWithHoles.instantiate, programDenotation]
      refine transferBy_bind hloc.1 (fun b => ?_)
      by_cases hb : b = true
      · subst hb; simpa using iht lazyInst eagerInst hloc.2.1 hhole
      · simp only [Bool.not_eq_true] at hb; subst hb
        simpa using ihe lazyInst eagerInst hloc.2.2 hhole
  | «while» c t iht =>
      intro lazyInst eagerInst hloc hhole
      simp only [StmtWithHoles.instantiate, programDenotation]
      exact transferL_while_loop hloc.1 (iht lazyInst eagerInst hloc.2 hhole)


/-- **Discharge of the oracle hypothesis for RO**: the lazy and eager oracle
    calls transfer, given the surrounding read/write are stable.  This is the
    concrete `hhole` for `body_transfer_gen` with `RO_lazy`/`RO_eager`: the
    query itself transfers by `ProgramDenotation.transfer_lazy_query` (lifted via
    `transferBy_zoom`), and the bridges identify the procedures with the
    semantic queries. -/
theorem ro_hhole {l : Type} {sig : ProcedureSignature} (n : HoleIndex roHoles sig)
    (x : Setter sig.ret (ProcedureState l)) (p : Getter sig.ParamType (ProcedureState l))
    (hp : Stable (ProgramDenotation.get p)) (hx : ∀ ret, Stable (ProgramDenotation.set x ret)) :
    transferBy convertL (programDenotation (StmtWithHoles.call x (RO_lazy n) p))
      (programDenotation (StmtWithHoles.call x (RO_eager n) p)) := by
  cases n with
  | zero =>
      show transferBy convertL (programDenotation (StmtWithHoles.call x RO_lazy_proc p))
          (programDenotation (StmtWithHoles.call x RO_eager_proc p))
      rw [denote_call, denote_call]
      refine transferBy_bind hp (fun args => transferBy_bind ?_ (fun ret => hx ret))
      rw [procDenotation_RO_lazy, procDenotation_RO_eager]
      exact transferBy_zoom ProcedureState.globalL (ProgramDenotation.transfer_lazy_query args)
  | succ m => nomatch m


/-- **Body-level RO transfer** — fully assembled (only `transferL_while_loop`
    remains, via `body_transfer_gen`).  For any syntactic adversary body `A`
    that is `Loc`al (touches the RO table only through the oracle hole), the
    lazy and eager instantiations transfer at the `ProcedureState` level. -/
theorem transfer_instantiate_body {l : Type} (A : StmtWithHoles roHoles l) (hloc : Loc A) :
    transferBy convertL (programDenotation (A.instantiate RO_lazy))
      (programDenotation (A.instantiate RO_eager)) :=
  body_transfer_gen A RO_lazy RO_eager hloc (fun n x p hp hx => ro_hhole n x p hp hx)


/-- **`convertL` slides in**: `convert` before the wrapper = `convertL` before the
    body, inside the wrapper.  Structural (no return-value hypothesis). -/
theorem procWrap_convertL_in {sig : ProcedureSignature} {L : Type}
    (rv : Getter sig.ret (ProcedureState L)) (initL : L) (B : ProgramDenotation (ProcedureState L)
        Unit) :
    procWrap rv initL (convertL >>= fun _ => B) = (convert >>= fun _ => procWrap rv initL B) := by
  funext st
  simp only [procWrap, convertL, ProgramDenotation.zoom, bind, StateT.bind, pure, StateT.pure,
    ProcedureState.globalL]
  generalize convert st = U
  obtain ⟨mu, hmu⟩ := U
  simp only [MeasureTheory.Measure.bind_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, MeasureTheory.Measure.dirac_bind measurable_from_top]
  rfl


/-- `ProgramDenotation.get rv` reads `rv` and threads the state through unchanged. -/
theorem programGet_eq {sig : ProcedureSignature} {L : Type} (rv : Getter sig.ret (ProcedureState L)) :
    (ProgramDenotation.get rv : ProgramDenotation (ProcedureState L) sig.ret) = fun ps => pure
        (rv.get ps, ps) := by
  funext ps
  simp only [ProgramDenotation.get, StateT.get, AsGetter.toG, bind, StateT.bind, pure, StateT.pure,
    id_eq, SubProbability.pure_bind, MeasureTheory.Measure.dirac_bind measurable_from_top]


/-- From `hret`: reading `rv` commutes with `convertL` (clean `convertL`-form). -/
theorem rv_convertL_stable {sig : ProcedureSignature} {L : Type}
    (rv : Getter sig.ret (ProcedureState L)) (hret : Stable (ProgramDenotation.get rv)) (ps :
        ProcedureState L) :
    (convertL ps >>= fun q => pure (rv.get ps, q.2)) = (convertL ps >>= fun q => pure (rv.get q.2, q.2)) := by
  have h := congrFun hret ps
  simp only [Stable, transferBy, programGet_eq, bind, StateT.bind, pure, StateT.pure,
    SubProbability.pure_bind, MeasureTheory.Measure.dirac_bind measurable_from_top] at h
  exact h


/-- `key`: reading `rv` is invariant under `convert` changing the table (the global
    component of `rv_convertL_stable`). -/
theorem rv_convert_invariant {sig : ProcedureSignature} {L : Type}
    (rv : Getter sig.ret (ProcedureState L)) (hret : Stable (ProgramDenotation.get rv)) (ps :
        ProcedureState L) :
    (convert ps.global >>= fun w => pure (rv.get ps, w.2))
      = (convert ps.global >>= fun w => pure (rv.get ⟨w.2, ps.locals⟩, w.2)) := by
  have hc := rv_convertL_stable rv hret ps
  have hp := congrArg (fun (m : SubProbability (sig.ret × ProcedureState L)) =>
      m >>= fun p => (pure (p.1, p.2.global) : SubProbability (sig.ret × state))) hc
  simp only [convertL, ProgramDenotation.zoom, ProcedureState.globalL, bind, StateT.bind, pure,
      StateT.pure,
    SubProbability.bind_assoc', SubProbability.pure_bind] at hp ⊢
  generalize convert ps.global = U at hp ⊢
  obtain ⟨mu, hmu⟩ := U
  simp only [MeasureTheory.Measure.bind_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, MeasureTheory.Measure.dirac_bind measurable_from_top] at hp ⊢
  exact hp


set_option maxHeartbeats 1000000 in
/-- **`convert` slides out**: `convert` after the wrapper = `convertL` after the
    body, inside the wrapper.  Consumes `hret` (the return value is RO-disjoint,
    so reading it commutes with `convert` changing the table) via `rv_convert_invariant`. -/
theorem procWrap_convert_out {sig : ProcedureSignature} {L : Type}
    (rv : Getter sig.ret (ProcedureState L)) (initL : L) (B : ProgramDenotation (ProcedureState L)
        Unit)
    (hret : Stable (ProgramDenotation.get rv)) :
    (procWrap rv initL B >>= fun r => convert >>= fun _ => pure r)
      = procWrap rv initL (B >>= fun a => convertL >>= fun _ => pure a) := by
  funext st
  simp only [procWrap, convertL, ProgramDenotation.zoom, ProcedureState.globalL, bind, StateT.bind,
    pure, StateT.pure]
  generalize B ⟨st, initL⟩ = Bv
  obtain ⟨mb, hb⟩ := Bv
  simp only [MeasureTheory.Measure.bind_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, MeasureTheory.Measure.dirac_bind measurable_from_top]
  apply Subtype.ext
  show mb.bind _ = mb.bind _
  congr 1
  funext p
  have h := congrArg Subtype.val (rv_convert_invariant rv hret p.2)
  simp only [bind, StateT.bind, pure, StateT.pure] at h ⊢
  generalize convert p.2.global = U at h ⊢
  obtain ⟨mu, hmu⟩ := U
  simp only [MeasureTheory.Measure.bind_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, MeasureTheory.Measure.dirac_bind measurable_from_top] at h ⊢
  exact h


/-- **Procedure wrapper**: a body-level `transferBy convertL` lifts to a
    state-level `ProgramDenotation.transfer` of the whole procedure denotation, provided
    the return value is RO-disjoint.  Assembled from `procedureDenotation_eq_procWrap`,
    `procWrap_convert_out` (uses `hret`), `hbody`, and `procWrap_convertL_in`. -/
theorem transfer_wrapper {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hbody : transferBy convertL (programDenotation (A.body.instantiate RO_lazy))
              (programDenotation (A.body.instantiate RO_eager)))
    (hret : Stable (ProgramDenotation.get A.return_val)) :
    ProgramDenotation.transfer
      (procedureDenotation (A.instantiate RO_lazy) args)
      (procedureDenotation (A.instantiate RO_eager) args) := by
  rw [procedureDenotation_eq_procWrap A args RO_lazy, procedureDenotation_eq_procWrap A args RO_eager]
  show (procWrap A.return_val (sig.localVariableInit A.locals args)
          (programDenotation (A.body.instantiate RO_lazy)) >>= fun r => convert >>= fun _ => pure r)
      = (convert >>= fun _ => procWrap A.return_val (sig.localVariableInit A.locals args)
          (programDenotation (A.body.instantiate RO_eager)))
  rw [procWrap_convert_out _ _ _ hret,
      congrArg (procWrap A.return_val (sig.localVariableInit A.locals args)) hbody,
      procWrap_convertL_in]


/-- **`Stable` from probabilistic footprint disjointness.** A program confined (in the
    `inFootprint` sense) to the complement of the RO table commutes with `convertL`, i.e. is
    `Stable`. The `Footprint` analogue of `stable_of_inRange_compl`; the `ᶜ`-form makes the
    `commute_of_disjoint_footprint` disjointness hypothesis `le_refl`, so no `complement_range` analog
    is needed. -/
theorem stable_of_inFootprint_compl {l α : Type}
    {p : ProgramDenotation (ProcedureState l) α} (hp : p.inFootprint ((roLift l).footprint)ᶜ) :
        Stable p :=
  ProgramDenotation.transferBy_refl_of_inFootprint_compl convertL_inFootprint hp


/-- **`Stable` from confinement to a footprint disjoint from the RO** (probabilistic). The
    `Footprint` analogue of `stable_of_confined_lens`. No `complement_range` needed — the
    `ᶜ`-form bound `hdisj` feeds `inFootprint_mono` directly. -/
theorem stable_of_confinedP_footprint {l α : Type}
    (R : Footprint (ProcedureState l)) (hdisj : R ≤ ((roLift l).footprint)ᶜ)
    {p : ProgramDenotation (ProcedureState l) α} (hp : p.inFootprint R) : Stable p :=
  stable_of_inFootprint_compl (ProgramDenotation.inFootprint_mono hp hdisj)


/-- **`ConfinedP` discharges `Loc`** (theorem-1 locality), leaf by leaf — reusing the existing
    `Loc`→theorems chain. The `Footprint` analogue of `confined_loc`. -/
theorem confinedP_loc {holes : HoleSigs} {l : Type}
    (R : Footprint (ProcedureState l)) (hdisj : R ≤ ((roLift l).footprint)ᶜ)
    (hc : ∀ {sig : ProcedureSignature}, HoleIndex holes sig → Countable sig.ParamType) :
    ∀ (A : StmtWithHoles holes l), ConfinedP R A → Loc A
  | .skip, _ => trivial
  | .sample _ _, h => stable_of_confinedP_footprint R hdisj h
  | .call' _ _ _ _ _, h => stable_of_confinedP_footprint R hdisj h
  | .hole n _ _, h =>
      haveI := hc n
      ⟨stable_of_confinedP_footprint R hdisj h.1,
        fun ret => stable_of_confinedP_footprint R hdisj (h.2 ret)⟩
  | .seq s1 s2, h => ⟨confinedP_loc R hdisj hc s1 h.1, confinedP_loc R hdisj hc s2 h.2⟩
  | .ifThenElse _ t e, h =>
      ⟨stable_of_confinedP_footprint R hdisj h.1, confinedP_loc R hdisj hc t h.2.1,
        confinedP_loc R hdisj hc e h.2.2⟩
  | .«while» _ t, h =>
      ⟨stable_of_confinedP_footprint R hdisj h.1, confinedP_loc R hdisj hc t h.2⟩


/-- **Theorem 1, end-to-end from footprint disjointness.**  Lazy/eager indistinguishability for any
    adversary whose full footprint `fvP_proc A` (body + return) is **disjoint from the random-oracle
    state** — `fvP_proc A ≤ (roLift _).footprintᶜ` — derived from that single bound, with no
    per-leaf confinement to check by hand (lens-free, `R`-free).  Inlines the whole
    `fvP → ConfinedP → Loc → transfer` chain — the sole entry point. -/
theorem ProgramDenotation.transfer_instantiate_of_fvP {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hdisj : fvP_proc A ≤ ((roLift (sig.LocalVariableState A.locals)).footprint)ᶜ) :
    ProgramDenotation.transfer
      (procedureDenotation (A.instantiate RO_lazy) args)
      (procedureDenotation (A.instantiate RO_eager) args) :=
  transfer_wrapper A args
    (transfer_instantiate_body A.body
      (confinedP_loc (fvP_proc A) hdisj roHole_paramType_countable A.body
        (confinedP_of_fv (fvP_proc A) roHole_paramType_countable A.body
          (fvP_stmt_body_le_fvP_proc A))))
    (stable_of_confinedP_footprint (fvP_proc A) hdisj
      (get_confinedP_of_fv A.return_val (get_return_val_le_fvP_proc A)))

/-! ## Whole-game form: initialisations included, coupling output

The per-query eager/lazy coupling is pointwise **unsatisfiable** (a fixed eager table entry cannot
couple with a fresh lazy sample), so theorem 2's `h` cannot be discharged for the genuine RO pair.
The true lazy = eager statement lives at the *whole-game* level, where `random_oracle_init`
supplies the eager table's randomness — and that is exactly theorem 1.  The results below convert
theorem 1 into the coupling format (`prhl2` with a result-decided post), giving the `h`-free
end-to-end transfer. -/

/-- `convert` is lossless (measure form of `convert_mass`): from any state its run has total
    mass `1`. -/
lemma convert_lossless (σ : state) : (convert σ).1 Set.univ = 1 := by
  have h := convert_mass σ
  simp only [ProgramDenotation.wp, SubProbability.expected, MeasureTheory.lintegral_one] at h
  exact h

/-- **Theorem 1 at whole-game level**: with the initialisations *included*, the lazy game followed
    by a result-preserving `convert` **equals** the eager game.  Unlike the per-query coupling,
    this is unconditionally true from footprint disjointness — the eager table's randomness is
    supplied by `random_oracle_init = lazy_init; convert`. -/
theorem game_transfer_of_fvP {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hdisj : fvP_proc A ≤ ((roLift (sig.LocalVariableState A.locals)).footprint)ᶜ) :
    ((lazy_init >>= fun _ => procedureDenotation (A.instantiate RO_lazy) args) >>= fun a =>
        convert >>= fun _ => pure a)
      = random_oracle_init >>= fun _ => procedureDenotation (A.instantiate RO_eager) args := by
  have ht : (procedureDenotation (A.instantiate RO_lazy) args >>= fun a =>
        convert >>= fun _ => pure a)
      = (convert >>= fun _ => procedureDenotation (A.instantiate RO_eager) args) :=
    ProgramDenotation.transfer_instantiate_of_fvP A args hdisj
  have h1 : ((lazy_init >>= fun _ => procedureDenotation (A.instantiate RO_lazy) args) >>= fun a =>
        convert >>= fun _ => pure a)
      = lazy_init >>= fun _ => (procedureDenotation (A.instantiate RO_lazy) args >>= fun a =>
          convert >>= fun _ => pure a) :=
    ProgramDenotation.bind_assoc _ _ _
  have h2 : (lazy_init >>= fun _ => (procedureDenotation (A.instantiate RO_lazy) args >>= fun a =>
        convert >>= fun _ => pure a))
      = lazy_init >>= fun _ =>
          (convert >>= fun _ => procedureDenotation (A.instantiate RO_eager) args) :=
    congrArg (fun k => lazy_init >>= k) (funext fun _ => ht)
  have h3 : (lazy_init >>= fun _ =>
        (convert >>= fun _ => procedureDenotation (A.instantiate RO_eager) args))
      = (lazy_init >>= fun _ => convert) >>= fun _ =>
          procedureDenotation (A.instantiate RO_eager) args :=
    (ProgramDenotation.bind_assoc _ _ _).symm
  have h4 : ((lazy_init >>= fun _ => convert) >>= fun _ =>
        procedureDenotation (A.instantiate RO_eager) args)
      = random_oracle_init >>= fun _ =>
          procedureDenotation (A.instantiate RO_eager) args :=
    congrArg (fun m => m >>= fun _ =>
        procedureDenotation (A.instantiate RO_eager) args)
      (show (lazy_init >>= fun _ => convert) = random_oracle_init from
        lazy_init_convert_eq_random_oracle_init)
  exact h1.trans (h2.trans (h3.trans h4))

/-- Game-level output-decided transfer, *semantic* disjointness form — see
    `output_win_transfer_games` for the user-facing (syntactic-`FVP`) statement. -/
theorem output_win_transfer_games_of_fvP {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType) (Win : sig.ret → Prop)
    (hdisj : fvP_proc A ≤ ((roLift (sig.LocalVariableState A.locals)).footprint)ᶜ) :
    ProgramDenotation.prhl2 (fun σ₁ σ₂ : state => σ₁ = σ₂)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (do random_oracle_init; procedureDenotation (A.instantiate RO_eager) args)
      (fun u v => Win u.1 ↔ Win v.1) :=
  (ProgramDenotation.prhl2_of_lossless_tail convert_lossless
      (game_transfer_of_fvP A args hdisj)).conseq
    (fun _ _ h => h) (fun _ _ h => by rw [h])

/-- **Game-level output-decided transfer** — the `h`-free counterpart of `output_win_transfer`,
    for **any** adversary whose variables avoid the oracle (`FVP.fvP_proc A ≤ oracleᶜ`, the same
    EasyCrypt-style hypothesis as `prhl_instantiate_of_glob`) and **any** predicate `Win` on its
    result: the *whole games* (initialisation included) couple with `Win u.1 ↔ Win v.1`.
    **Collision resistance** is the instance where `Win r` reads "`r` is a collision `A`
    produced".  Everything is discharged by theorem 1 (`convert`-sliding), which owns the eager
    table's initialisation randomness — no per-query coupling hypothesis remains. -/
theorem output_win_transfer_games {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType) (Win : sig.ret → Prop)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) :
    ProgramDenotation.prhl2 (fun σ₁ σ₂ : state => σ₁ = σ₂)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (do random_oracle_init; procedureDenotation (A.instantiate RO_eager) args)
      (fun u v => Win u.1 ↔ Win v.1) :=
  output_win_transfer_games_of_fvP A args Win (fvP_proc_le_roLift_compl A hdisj)

end GaudisCrypt.Lib.RO.Instantiate
