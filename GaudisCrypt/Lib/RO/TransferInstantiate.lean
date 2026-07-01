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


/-! ## Generic `transferBy` calculus

`ProgramDenotation.transfer` is `transferBy convert`.  We need the same relation at the
`ProcedureState` level (with `convertL`), so we factor out a generic version
`transferBy c p q := (p >>= a => c >>= _ => pure a) = (c >>= _ => q)` over an
arbitrary "convert" program `c`, prove the monad-law combinators once, and a
`zoom` lifting lemma — `convertL = zoom globalL convert`, and `zoom` is a monad
morphism, so any state-level transfer lifts to a zoomed `ProcedureState` one. -/

/-- Generic transfer: `c` slides from after `p` to before `q`, preserving the value. -/
def transferBy {s α : Type} (c : ProgramDenotation s Unit) (p q : ProgramDenotation s α) : Prop :=
  (p >>= fun a => c >>= fun _ => pure a) = (c >>= fun _ => q)


/-- `pure` transfers to itself (generic). -/
theorem transferBy_pure {s α : Type} {c : ProgramDenotation s Unit} (a : α) :
    transferBy c (pure a) (pure a) := by
  show ((pure a : ProgramDenotation s α) >>= fun a' => c >>= fun _ => pure a') = (c >>= fun _ =>
      pure a)
  rw [ProgramDenotation.pure_bind]


/-- `transferBy` chains under `>>=` (generic; copy of `ProgramDenotation.transfer_bind`). -/
theorem transferBy_bind {s α β : Type} {c : ProgramDenotation s Unit}
    {p q : ProgramDenotation s α} {p' q' : α → ProgramDenotation s β}
    (h : transferBy c p q) (h' : ∀ a, transferBy c (p' a) (q' a)) :
    transferBy c (p >>= p') (q >>= q') := by
  show ((p >>= p') >>= fun b => c >>= fun _ => pure b) = (c >>= fun _ => q >>= q')
  rw [ProgramDenotation.bind_assoc]
  conv_lhs =>
    rhs; ext a
    rw [show (p' a >>= fun b => c >>= fun _ => (Pure.pure b : ProgramDenotation s β))
          = (c >>= fun _ => q' a) from h' a]
  conv_lhs =>
    rhs; ext a
    rw [show (c >>= fun _ => q' a)
          = (c >>= fun _ => (Pure.pure a : ProgramDenotation s α)) >>= q' from by
        rw [ProgramDenotation.bind_assoc]; congr 1; funext _; rw [ProgramDenotation.pure_bind]]
  rw [← ProgramDenotation.bind_assoc]
  rw [show (p >>= fun a => c >>= fun _ => (Pure.pure a : ProgramDenotation s α))
        = (c >>= fun _ => q) from h]
  rw [ProgramDenotation.bind_assoc]


/-- `zoom` lifts `transferBy`: a state-level transfer becomes a zoomed one. -/
theorem transferBy_zoom {s t α : Type} (lens : Lens s t)
    {c : ProgramDenotation s Unit} {p q : ProgramDenotation s α} (h : transferBy c p q) :
    transferBy (ProgramDenotation.zoom lens c) (ProgramDenotation.zoom lens p)
        (ProgramDenotation.zoom lens q) := by
  show (ProgramDenotation.zoom lens p >>= fun a => ProgramDenotation.zoom lens c >>= fun _ => pure
      a)
      = (ProgramDenotation.zoom lens c >>= fun _ => ProgramDenotation.zoom lens q)
  rw [show (fun a => ProgramDenotation.zoom lens c >>= fun _ => (pure a : ProgramDenotation t α))
        = (fun a => ProgramDenotation.zoom lens (c >>= fun _ => pure a)) from by
      funext a; rw [zoom_bind]; congr 1; funext _; rw [zoom_pure]]
  rw [← zoom_bind, ← zoom_bind]
  rw [show (p >>= fun a => c >>= fun _ => pure a) = (c >>= fun _ => q) from h]


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

/-! ### Generic Kleene closure of `transferBy` under `while_loop`

A state-and-`c`-generic port of `ProgramDenotation.transfer_while_loop`.  The only step
that was RO-specific there (the condition commuting with `convert`) is taken as
a hypothesis `h_cond_comm` here — at the `ProcedureState` level it is supplied
by `Stable cond`. -/

/-- Intermediate iteration: the lazy body, but with `c` in the else branch. -/
private noncomputable def whileBy_Ψ {s : Type} (c : ProgramDenotation s Unit)
    (cond : ProgramDenotation s Bool) (body_lazy : ProgramDenotation s Unit) :
    (Unit → ProgramDenotation s Unit) →𝒄 (Unit → ProgramDenotation s Unit) :=
  OmegaCompletePartialOrder.ContinuousHom.ofFun fun (fp : Unit → ProgramDenotation s Unit) => fun ()
      =>
    do if ← cond then body_lazy; fp () else c


/-- Lazy iterate composed with `c` equals the `Ψ`-iterate. -/
private lemma whileBy_kleene_lazy {s : Type} (c : ProgramDenotation s Unit)
    (cond : ProgramDenotation s Bool) (body_lazy : ProgramDenotation s Unit) :
    ∀ n : ℕ,
    (((while_iteration cond body_lazy)^[n] (⊥ : Unit → ProgramDenotation s Unit)) () >>= (fun _ =>
        c))
    = ((whileBy_Ψ c cond body_lazy)^[n] (⊥ : Unit → ProgramDenotation s Unit)) () := by
  intro n
  induction n with
  | zero =>
    change ((⊥ : ProgramDenotation s Unit) >>= fun _ => c) = (⊥ : ProgramDenotation s Unit)
    exact ProgramDenotation.bot_bind _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (((cond) >>= fun b =>
              if b = true then body_lazy >>= fun _ => ((while_iteration cond body_lazy)^[n] ⊥) ()
              else (pure () : ProgramDenotation s Unit)) >>= fun _ => c)
        = (cond) >>= fun b =>
              if b = true then body_lazy >>= fun _ => ((whileBy_Ψ c cond body_lazy)^[n] ⊥) ()
              else c
    rw [ProgramDenotation.bind_assoc]
    congr 1; funext b
    by_cases h : b = true
    · simp only [h, if_true]; rw [ProgramDenotation.bind_assoc]; congr 1; funext _; exact ih
    · simp only [h, if_false]; exact ProgramDenotation.pure_bind () _


/-- `c` prepended to the eager iterate equals the `Ψ`-iterate. -/
private lemma whileBy_kleene_eager {s : Type} (c : ProgramDenotation s Unit) {cond :
    ProgramDenotation s Bool}
    (h_cond_comm : ∀ {β : Type} (k : Bool → ProgramDenotation s β),
        (cond >>= fun b => c >>= fun _ => k b) = (c >>= fun _ => cond >>= k))
    {body_lazy body_eager : ProgramDenotation s Unit}
    (h_body : (body_lazy >>= fun _ : Unit => c) = (c >>= fun _ : Unit => body_eager)) :
    ∀ n : ℕ,
    c >>= (fun _ => ((while_iteration cond body_eager)^[n] (⊥ : Unit → ProgramDenotation s Unit))
        ())
    = ((whileBy_Ψ c cond body_lazy)^[n] (⊥ : Unit → ProgramDenotation s Unit)) () := by
  intro n
  induction n with
  | zero =>
    change (c >>= fun _ => (⊥ : ProgramDenotation s Unit)) = (⊥ : ProgramDenotation s Unit)
    exact ProgramDenotation.bind_bot _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (c >>= fun _ => (cond) >>= fun b =>
              if b = true then body_eager >>= fun _ => ((while_iteration cond body_eager)^[n] ⊥) ()
              else (pure () : ProgramDenotation s Unit))
        = (cond) >>= fun b =>
              if b = true then body_lazy >>= fun _ => ((whileBy_Ψ c cond body_lazy)^[n] ⊥) ()
              else c
    rw [show (c >>= fun _ => (cond) >>=
              fun b => if b = true then body_eager >>= fun _ =>
                  ((while_iteration cond body_eager)^[n] ⊥) () else (pure () : ProgramDenotation s
                      Unit))
            = ((cond) >>= fun b => c >>= fun _ =>
                if b = true then body_eager >>= fun _ =>
                  ((while_iteration cond body_eager)^[n] ⊥) () else (pure () : ProgramDenotation s
                      Unit)) from
        (h_cond_comm _).symm]
    congr 1; funext b
    by_cases h : b = true
    · simp only [h, if_true]
      rw [← ProgramDenotation.bind_assoc]
      rw [show (c >>= fun _ : Unit => body_eager) = (body_lazy >>= fun _ : Unit => c) from h_body.symm]
      rw [ProgramDenotation.bind_assoc]; congr 1; funext _; exact ih
    · simp only [h, if_false]; exact ProgramDenotation.bind_pure _


/-- **Generic `while_loop` closure for `transferBy`.** -/
theorem transferBy_while_loop {s : Type} (c : ProgramDenotation s Unit) {cond : ProgramDenotation s
    Bool}
    (h_cond_comm : ∀ {β : Type} (k : Bool → ProgramDenotation s β),
        (cond >>= fun b => c >>= fun _ => k b) = (c >>= fun _ => cond >>= k))
    {body_lazy body_eager : ProgramDenotation s Unit}
    (h_body : (body_lazy >>= fun _ : Unit => c) = (c >>= fun _ : Unit => body_eager)) :
    transferBy c (while_loop cond body_lazy) (while_loop cond body_eager) := by
  show (while_loop cond body_lazy >>= fun u : Unit => c >>= fun _ : Unit => (Pure.pure u :
      ProgramDenotation s Unit))
      = (c >>= fun _ : Unit => while_loop cond body_eager)
  rw [show (fun u : Unit => c >>= fun _ : Unit => (Pure.pure u : ProgramDenotation s Unit)) = (fun _
      : Unit => c) from by
        funext u
        rw [show (Pure.pure u : ProgramDenotation s Unit) = (Pure.pure () : ProgramDenotation s
            Unit) from rfl]
        exact ProgramDenotation.bind_pure _]
  let F_lazy := while_iteration cond body_lazy
  let F_eager := while_iteration cond body_eager
  have hL_chain : ∀ n, ((F_lazy^[n] ⊥ : Unit → ProgramDenotation s Unit) () >>= (fun _ => c))
                     = ((whileBy_Ψ c cond body_lazy)^[n] ⊥ : Unit → ProgramDenotation s Unit) () :=
    whileBy_kleene_lazy c cond body_lazy
  have hE_chain : ∀ n, c >>= (fun _ => (F_eager^[n] ⊥ : Unit → ProgramDenotation s Unit) ())
                     = ((whileBy_Ψ c cond body_lazy)^[n] ⊥ : Unit → ProgramDenotation s Unit) () :=
    whileBy_kleene_eager c h_cond_comm h_body
  have h_bind_c_cont : OmegaCompletePartialOrder.ωScottContinuous
      (fun (m : ProgramDenotation s Unit) => m >>= fun _ => c) := by fun_prop
  have h_c_bind_cont : OmegaCompletePartialOrder.ωScottContinuous
      (fun (m : ProgramDenotation s Unit) => c >>= fun _ => m) := by fun_prop
  change (F_lazy.lfp ()) >>= (fun _ => c) = c >>= (fun _ => F_eager.lfp ())
  let chain_lazy : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation s Unit) :=
    ⟨fun n => F_lazy^[n] ⊥, Monotone.monotone_iterate_of_le_map F_lazy.monotone (OrderBot.bot_le _)⟩
  let chain_eager : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation s Unit) :=
    ⟨fun n => F_eager^[n] ⊥, Monotone.monotone_iterate_of_le_map F_eager.monotone (OrderBot.bot_le _)⟩
  have hLfpL : F_lazy.lfp = OmegaCompletePartialOrder.ωSup chain_lazy := rfl
  have hLfpE : F_eager.lfp = OmegaCompletePartialOrder.ωSup chain_eager := rfl
  have hLfpL_at : F_lazy.lfp () = OmegaCompletePartialOrder.ωSup
                    (chain_lazy.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := by rw [hLfpL]; rfl
  have hLfpE_at : F_eager.lfp () = OmegaCompletePartialOrder.ωSup
                    (chain_eager.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := by rw [hLfpE]; rfl
  rw [hLfpL_at, hLfpE_at, h_bind_c_cont.map_ωSup, h_c_bind_cont.map_ωSup]
  congr 1
  ext n
  exact (hL_chain n).trans (hE_chain n).symm


/-- **The former hard lemma** (now proved): `transferBy convertL` is closed under
    `while_loop`.  Instantiates `transferBy_while_loop` with `c := convertL`; the
    condition-commutation comes from `Stable c` and the body bind-form from `hbody`. -/
theorem transferL_while_loop {l : Type} {c : ProgramDenotation (ProcedureState l) Bool}
    {body_lazy body_eager : ProgramDenotation (ProcedureState l) Unit}
    (hc : Stable c) (hbody : transferBy convertL body_lazy body_eager) :
    transferBy convertL (while_loop c body_lazy) (while_loop c body_eager) := by
  refine transferBy_while_loop convertL (cond := c) ?_ ?_
  · -- condition commutes with convertL, from `Stable c`
    intro β k
    have hc' : (c >>= fun a => convertL >>= fun _ => (pure a : ProgramDenotation (ProcedureState l)
        Bool))
             = (convertL >>= fun _ => c) := hc
    have h_pair : (c >>= fun b => convertL >>= fun _ => (pure (b, ()) : ProgramDenotation
        (ProcedureState l) (Bool × Unit)))
                = (convertL >>= fun _ => c >>= fun b => pure (b, ())) := by
      have := congrArg (fun m => m >>= fun b =>
        (pure (b, ()) : ProgramDenotation (ProcedureState l) (Bool × Unit))) hc'
      simpa only [ProgramDenotation.bind_assoc, ProgramDenotation.pure_bind] using this
    have hL : (c >>= fun b => convertL >>= fun _ => k b)
            = (c >>= fun b => convertL >>= fun _ =>
                (pure (b, ()) : ProgramDenotation (ProcedureState l) (Bool × Unit))) >>= fun bu => k
                    bu.1 := by
      simp_rw [ProgramDenotation.bind_assoc]; congr 1; funext b; congr 1; funext u; rw
          [ProgramDenotation.pure_bind]
    have hR : (convertL >>= fun _ => c >>= k)
            = (convertL >>= fun _ => c >>= fun b =>
                (pure (b, ()) : ProgramDenotation (ProcedureState l) (Bool × Unit))) >>= fun bu => k
                    bu.1 := by
      simp_rw [ProgramDenotation.bind_assoc]; congr 1; funext u; congr 1; funext b; rw
          [ProgramDenotation.pure_bind]
    rw [hL, hR, h_pair]
  · -- body bind-form, from `hbody`
    calc (body_lazy >>= fun _ : Unit => convertL)
        = (body_lazy >>= fun u : Unit =>
              convertL >>= fun _ : Unit => (Pure.pure u : ProgramDenotation (ProcedureState l)
                  Unit)) := by
          congr 1; funext u
          show convertL = convertL >>= fun _ : Unit => Pure.pure u
          rw [show (Pure.pure u : ProgramDenotation (ProcedureState l) Unit)
                = (Pure.pure () : ProgramDenotation (ProcedureState l) Unit) from rfl]
          exact (ProgramDenotation.bind_pure _).symm
      _ = (convertL >>= fun _ : Unit => body_eager) := hbody


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
        Stable p := by
  show (p >>= fun a => convertL >>= fun _ => pure a) = (convertL >>= fun _ => p)
  have h_commute : (p >>= fun a => convertL >>= fun b => pure (a, b))
                 = (convertL >>= fun b => p >>= fun a => pure (a, b)) :=
    ProgramDenotation.commute_of_disjoint_footprint hp convertL_inFootprint (le_refl _)
  have hL : (p >>= fun a => convertL >>= fun b => pure (a, b)) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : ProgramDenotation (ProcedureState l) α))
          = (p >>= fun a => convertL >>= fun _ => (Pure.pure a : ProgramDenotation (ProcedureState
              l) α)) := by
    rw [ProgramDenotation.bind_assoc]; congr 1; funext a
    rw [ProgramDenotation.bind_assoc]; congr 1; funext _
    rw [ProgramDenotation.pure_bind]
  have hR : (convertL >>= fun b => p >>= fun a => pure (a, b)) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : ProgramDenotation (ProcedureState l) α))
          = (convertL >>= fun _ => p) := by
    rw [ProgramDenotation.bind_assoc]
    congr 1; funext _
    rw [ProgramDenotation.bind_assoc]
    rw [show (fun a : α => pure (a, ()) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : ProgramDenotation (ProcedureState l) α)))
          = (fun a : α => (Pure.pure a : ProgramDenotation (ProcedureState l) α)) from by
        funext a; rw [ProgramDenotation.pure_bind]]
    exact ProgramDenotation.bind_pure _
  rw [← hL, h_commute, hR]


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

end GaudisCrypt.Lib.RO.Instantiate
