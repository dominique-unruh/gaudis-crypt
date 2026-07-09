import GaudisCrypt.Logic.EagerRhl
import GaudisCrypt.Language.Programs

/-!
# The eager abstract-call rule (EasyCrypt's `eager proc`/`eager call`)

The instantiation layer of the eager calculus: for a procedure-with-holes `A`
and two hole-instantiations, the whole procedure is eager for a block `S`
provided each hole is (`hhole`) and `A`'s own operations swap with the lifted
block (`SwapLoc`).  This is the calculus-level rule whose soundness is a
once-and-for-all induction over the adversary's syntax — the analogue of
EasyCrypt's trusted `eager proc` rule (justified by induction in the
metatheory); client derivations only ever *apply* it.

* `SwapLoc SL A` — locality: every operation of `A` outside the holes swaps
  with the lifted block `SL` (self-`transferBy`).  For `SL := convertL` this is
  definitionally the RO development's `Loc`, so the existing footprint
  discharge (`confinedP_loc`) applies unchanged.
* `eager_body` — the induction over `StmtWithHoles`, threading the `eagerR`
  rules (`eagerR_pure`/`eagerR_seq`/`eagerR_while`) over the statement
  structure.
* `procWrap_block_in` / `procWrap_block_out` — the block slides through the
  procedure wrapper (`zoom globalL S` inside ↔ `S` outside), generalizing the
  `convert`-specific wrapper lemmas.
* `eager_call` — the assembled rule at the level of `procedureDenotation`.
-/

namespace GaudisCrypt

open GaudisCrypt
open GaudisCrypt

variable [ProgramSpec]

/-! ## Locality -/

/-- **Swap-locality**: every operation of `A` *outside the holes* swaps with the
    block `SL` (self-`transferBy`).  For a hole, this is the surrounding read
    (`get p`) and write (`set x`) — the hole call itself is *not* required to
    swap (it is handled by the per-hole hypothesis). -/
def SwapLoc {holes : HoleSigs} {l : Type}
    (SL : ProgramDenotation (ProcedureState l) Unit) :
    StmtWithHoles holes l → Prop
  | .skip => True
  | .sample x e => ProgramDenotation.transferBy SL
      (programDenotation (StmtWithHoles.sample x e : Stmt l))
      (programDenotation (StmtWithHoles.sample x e : Stmt l))
  | .call' x ls b r p => ProgramDenotation.transferBy SL
      (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l))
      (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l))
  | .hole _ x p => ProgramDenotation.transferBy SL
        (ProgramDenotation.get p) (ProgramDenotation.get p)
      ∧ (∀ ret, ProgramDenotation.transferBy SL
          (ProgramDenotation.set x ret) (ProgramDenotation.set x ret))
  | .seq s1 s2 => SwapLoc SL s1 ∧ SwapLoc SL s2
  | .ifThenElse c t e => ProgramDenotation.transferBy SL
        (ProgramDenotation.get c) (ProgramDenotation.get c)
      ∧ SwapLoc SL t ∧ SwapLoc SL e
  | .while c t => ProgramDenotation.transferBy SL
        (ProgramDenotation.get c) (ProgramDenotation.get c)
      ∧ SwapLoc SL t

omit [ProgramSpec] in
/-- A self-`transferBy` fact is a (diagonal) self-eager judgment. -/
theorem eagerR_self_of_transferBy {s α : Type}
    {SL : ProgramDenotation s Unit} {p : ProgramDenotation s α}
    (h : ProgramDenotation.transferBy SL p p) :
    ProgramDenotation.eagerR SL SL (fun σ₁ σ₂ : s => σ₁ = σ₂) p p
      (fun u v : α × s => u = v) :=
  (ProgramDenotation.eagerR_eq_iff_transferBy SL p p).mpr h

/-! ## The body induction (EC's `eager proc`) -/

/-- **Eager body induction**: an arbitrary syntactic body `A` is eager for the
    block `SL` across two hole-instantiations, given swap-locality of its own
    operations and a per-hole eager hypothesis.  The `eagerR` rules are threaded
    over the statement structure. -/
theorem eager_body (S : ProgramDenotation State Unit) :
    ∀ {holes : HoleSigs} {l : Type}
      (A : StmtWithHoles holes l) (eagerInst lazyInst : holes.Instantiation),
      SwapLoc (ProgramDenotation.zoom ProcedureState.globalL S) A →
      (∀ {sig : ProcedureSignature} (n : HoleIndex holes sig)
          (x : Setter sig.ret (ProcedureState l))
          (p : Getter sig.ParamType (ProcedureState l)),
          ProgramDenotation.transferBy (ProgramDenotation.zoom ProcedureState.globalL S)
            (ProgramDenotation.get p) (ProgramDenotation.get p) →
          (∀ ret, ProgramDenotation.transferBy (ProgramDenotation.zoom ProcedureState.globalL S)
            (ProgramDenotation.set x ret) (ProgramDenotation.set x ret)) →
          ProgramDenotation.eagerR
            (ProgramDenotation.zoom ProcedureState.globalL S)
            (ProgramDenotation.zoom ProcedureState.globalL S)
            (fun σ₁ σ₂ : ProcedureState l => σ₁ = σ₂)
            (programDenotation (StmtWithHoles.call x (eagerInst n) p))
            (programDenotation (StmtWithHoles.call x (lazyInst n) p))
            (fun u v : Unit × ProcedureState l => u = v)) →
      ProgramDenotation.eagerR
        (ProgramDenotation.zoom ProcedureState.globalL S)
        (ProgramDenotation.zoom ProcedureState.globalL S)
        (fun σ₁ σ₂ : ProcedureState l => σ₁ = σ₂)
        (programDenotation (A.instantiate eagerInst))
        (programDenotation (A.instantiate lazyInst))
        (fun u v : Unit × ProcedureState l => u = v) := by
  intro holes l A
  induction A with
  | skip =>
      intro eagerInst lazyInst _ _
      simp only [StmtWithHoles.instantiate, programDenotation]
      exact ProgramDenotation.eagerR_pure (ProgramDenotation.zoom ProcedureState.globalL S) ()
  | sample x e =>
      intro eagerInst lazyInst hloc _
      simp only [StmtWithHoles.instantiate]
      exact eagerR_self_of_transferBy hloc
  | call' x ls b r p =>
      intro eagerInst lazyInst hloc _
      simp only [StmtWithHoles.instantiate]
      exact eagerR_self_of_transferBy hloc
  | hole n x p =>
      intro eagerInst lazyInst hloc hhole
      simp only [StmtWithHoles.instantiate]
      exact hhole n x p hloc.1 hloc.2
  | seq s1 s2 ih1 ih2 =>
      intro eagerInst lazyInst hloc hhole
      simp only [StmtWithHoles.instantiate, programDenotation]
      exact ProgramDenotation.eagerR_seq (ih1 eagerInst lazyInst hloc.1 hhole)
        (fun _ => ih2 eagerInst lazyInst hloc.2 hhole)
  | ifThenElse c t e iht ihe =>
      intro eagerInst lazyInst hloc hhole
      simp only [StmtWithHoles.instantiate, programDenotation]
      refine ProgramDenotation.eagerR_seq (eagerR_self_of_transferBy hloc.1) (fun b => ?_)
      by_cases hb : b = true
      · subst hb; simpa using iht eagerInst lazyInst hloc.2.1 hhole
      · simp only [Bool.not_eq_true] at hb; subst hb
        simpa using ihe eagerInst lazyInst hloc.2.2 hhole
  | «while» c t iht =>
      intro eagerInst lazyInst hloc hhole
      simp only [StmtWithHoles.instantiate, programDenotation]
      exact ProgramDenotation.eagerR_while (eagerR_self_of_transferBy hloc.1)
        (iht eagerInst lazyInst hloc.2 hhole)

/-! ## The block slides through the procedure wrapper -/

/-- **The lifted block slides in**: `S` before the wrapper = `zoom globalL S`
    before the body, inside the wrapper.  Structural. -/
theorem procWrap_block_in {sig : ProcedureSignature} {L : Type}
    (S : ProgramDenotation State Unit)
    (rv : Getter sig.ret (ProcedureState L)) (initL : L)
    (B : ProgramDenotation (ProcedureState L) Unit) :
    procWrap rv initL (ProgramDenotation.zoom ProcedureState.globalL S >>= fun _ => B)
      = (S >>= fun _ => procWrap rv initL B) := by
  funext st
  simp only [procWrap, ProgramDenotation.zoom, bind, StateT.bind, pure,
    ProcedureState.globalL]
  generalize S st = U
  obtain ⟨mu, hmu⟩ := U
  simp only [MeasureTheory.Measure.bind_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, MeasureTheory.Measure.dirac_bind measurable_from_top]
  rfl

/-- `ProgramDenotation.get rv` reads `rv` and threads the state through unchanged. -/
theorem programGet_eq' {sig : ProcedureSignature} {L : Type}
    (rv : Getter sig.ret (ProcedureState L)) :
    (ProgramDenotation.get rv : ProgramDenotation (ProcedureState L) sig.ret)
      = fun ps => pure (rv.get ps, ps) := by
  funext ps
  simp only [ProgramDenotation.get, StateT.get, AsGetter.toG, bind, StateT.bind, pure,
    StateT.pure, id_eq, MeasureTheory.Measure.dirac_bind measurable_from_top]

/-- From the return-value swap: reading `rv` commutes with the lifted block
    (clean form). -/
theorem rv_block_stable {sig : ProcedureSignature} {L : Type}
    (S : ProgramDenotation State Unit)
    (rv : Getter sig.ret (ProcedureState L))
    (hret : ProgramDenotation.transferBy
      (ProgramDenotation.zoom ProcedureState.globalL S)
      (ProgramDenotation.get rv) (ProgramDenotation.get rv))
    (ps : ProcedureState L) :
    ((ProgramDenotation.zoom ProcedureState.globalL S) ps >>= fun q => pure (rv.get ps, q.2))
      = ((ProgramDenotation.zoom ProcedureState.globalL S) ps >>= fun q =>
          pure (rv.get q.2, q.2)) := by
  have h := congrFun hret ps
  simp only [programGet_eq', bind, StateT.bind, pure, StateT.pure,
    MeasureTheory.Measure.dirac_bind measurable_from_top] at h
  exact h

/-- Reading `rv` is invariant under the block changing the global component. -/
theorem rv_block_invariant {sig : ProcedureSignature} {L : Type}
    (S : ProgramDenotation State Unit)
    (rv : Getter sig.ret (ProcedureState L))
    (hret : ProgramDenotation.transferBy
      (ProgramDenotation.zoom ProcedureState.globalL S)
      (ProgramDenotation.get rv) (ProgramDenotation.get rv))
    (ps : ProcedureState L) :
    (S ps.global >>= fun w => pure (rv.get ps, w.2))
      = (S ps.global >>= fun w => pure (rv.get ⟨w.2, ps.locals⟩, w.2)) := by
  have hc := rv_block_stable S rv hret ps
  have hp := congrArg (fun (m : SubProbability (sig.ret × ProcedureState L)) =>
      m >>= fun p => (pure (p.1, p.2.global) : SubProbability (sig.ret × State))) hc
  simp only [ProgramDenotation.zoom, ProcedureState.globalL, bind, pure] at hp ⊢
  generalize S ps.global = U at hp ⊢
  obtain ⟨mu, hmu⟩ := U
  simp only [MeasureTheory.Measure.bind_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, MeasureTheory.Measure.dirac_bind measurable_from_top]
    at hp ⊢
  exact hp

set_option maxHeartbeats 1000000 in
-- the final `exact h` closes a large deterministic measure-plumbing defeq; the default
-- budget is slightly too small for it (as for the `convert`-specific original)
/-- **The block slides out**: `S` after the wrapper = the lifted block after the
    body, inside the wrapper.  Consumes `hret` (the return value swaps with the
    block, so reading it commutes with the block changing the globals). -/
theorem procWrap_block_out {sig : ProcedureSignature} {L : Type}
    (S : ProgramDenotation State Unit)
    (rv : Getter sig.ret (ProcedureState L)) (initL : L)
    (B : ProgramDenotation (ProcedureState L) Unit)
    (hret : ProgramDenotation.transferBy
      (ProgramDenotation.zoom ProcedureState.globalL S)
      (ProgramDenotation.get rv) (ProgramDenotation.get rv)) :
    (procWrap rv initL B >>= fun r => S >>= fun _ => pure r)
      = procWrap rv initL (B >>= fun a =>
          ProgramDenotation.zoom ProcedureState.globalL S >>= fun _ => pure a) := by
  funext st
  simp only [procWrap, ProgramDenotation.zoom, ProcedureState.globalL, bind, StateT.bind,
    pure, StateT.pure]
  generalize B ⟨st, initL⟩ = Bv
  obtain ⟨mb, hb⟩ := Bv
  simp only [MeasureTheory.Measure.bind_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, MeasureTheory.Measure.dirac_bind measurable_from_top]
  apply Subtype.ext
  change mb.bind _ = mb.bind _
  congr 1
  funext p
  have h := congrArg Subtype.val (rv_block_invariant S rv hret p.2)
  simp only [bind, pure] at h ⊢
  generalize S p.2.global = U at h ⊢
  obtain ⟨mu, hmu⟩ := U
  simp only [MeasureTheory.Measure.bind_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, MeasureTheory.Measure.dirac_bind measurable_from_top]
    at h ⊢
  exact h

/-! ## The assembled rule -/

/-- **Procedure wrapper for the eager judgment**: a body-level eager judgment
    (block `zoom globalL S`) lifts to a state-level eager judgment (block `S`)
    of the whole procedure denotations, provided the return value swaps with
    the lifted block. -/
theorem eager_wrapper {holes : HoleSigs} {sig : ProcedureSignature}
    (eagerInst lazyInst : holes.Instantiation)
    (A : ProcedureWithHoles holes sig) (args : sig.ParamType)
    (S : ProgramDenotation State Unit)
    (hbody : ProgramDenotation.eagerR
      (ProgramDenotation.zoom ProcedureState.globalL S)
      (ProgramDenotation.zoom ProcedureState.globalL S)
      (fun σ₁ σ₂ => σ₁ = σ₂)
      (programDenotation (A.body.instantiate eagerInst))
      (programDenotation (A.body.instantiate lazyInst))
      (fun u v => u = v))
    (hret : ProgramDenotation.transferBy
      (ProgramDenotation.zoom ProcedureState.globalL S)
      (ProgramDenotation.get A.return_val) (ProgramDenotation.get A.return_val)) :
    ProgramDenotation.eagerR S S (fun σ₁ σ₂ : State => σ₁ = σ₂)
      (procedureDenotation (A.instantiate eagerInst) args)
      (procedureDenotation (A.instantiate lazyInst) args)
      (fun u v : sig.ret × State => u = v) := by
  refine ProgramDenotation.eagerR_of_eq ?_
  rw [procedureDenotation_eq_procWrap_gen A args eagerInst,
      procedureDenotation_eq_procWrap_gen A args lazyInst]
  calc (S >>= fun _ => procWrap A.return_val (sig.localVariableInit A.locals args)
          (programDenotation (A.body.instantiate eagerInst)))
      = procWrap A.return_val (sig.localVariableInit A.locals args)
          (ProgramDenotation.zoom ProcedureState.globalL S >>= fun _ =>
            programDenotation (A.body.instantiate eagerInst)) :=
        (procWrap_block_in S _ _ _).symm
    _ = procWrap A.return_val (sig.localVariableInit A.locals args)
          (programDenotation (A.body.instantiate lazyInst) >>= fun a =>
            ProgramDenotation.zoom ProcedureState.globalL S >>= fun _ => pure a) := by
        rw [ProgramDenotation.eagerR_to_eq hbody]
    _ = (procWrap A.return_val (sig.localVariableInit A.locals args)
          (programDenotation (A.body.instantiate lazyInst)) >>= fun r =>
            S >>= fun _ => pure r) :=
        (procWrap_block_out S _ _ _ hret).symm

/-- **EC's `eager call` on an abstract procedure** (equality invariants): the
    whole procedure is eager for `S` across two hole-instantiations, given
    swap-locality of its own operations, a swapping return read, and the
    per-hole eager hypothesis. -/
theorem eager_call {holes : HoleSigs} {sig : ProcedureSignature}
    (eagerInst lazyInst : holes.Instantiation)
    (A : ProcedureWithHoles holes sig) (args : sig.ParamType)
    (S : ProgramDenotation State Unit)
    (hloc : SwapLoc (ProgramDenotation.zoom ProcedureState.globalL S) A.body)
    (hret : ProgramDenotation.transferBy
      (ProgramDenotation.zoom ProcedureState.globalL S)
      (ProgramDenotation.get A.return_val) (ProgramDenotation.get A.return_val))
    (hhole : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig')
        (x : Setter sig'.ret (ProcedureState (sig.LocalVariableState A.locals)))
        (p : Getter sig'.ParamType (ProcedureState (sig.LocalVariableState A.locals))),
        ProgramDenotation.transferBy (ProgramDenotation.zoom ProcedureState.globalL S)
          (ProgramDenotation.get p) (ProgramDenotation.get p) →
        (∀ ret, ProgramDenotation.transferBy (ProgramDenotation.zoom ProcedureState.globalL S)
          (ProgramDenotation.set x ret) (ProgramDenotation.set x ret)) →
        ProgramDenotation.eagerR
          (ProgramDenotation.zoom ProcedureState.globalL S)
          (ProgramDenotation.zoom ProcedureState.globalL S)
          (fun σ₁ σ₂ => σ₁ = σ₂)
          (programDenotation (StmtWithHoles.call x (eagerInst n) p))
          (programDenotation (StmtWithHoles.call x (lazyInst n) p))
          (fun u v => u = v)) :
    ProgramDenotation.eagerR S S (fun σ₁ σ₂ : State => σ₁ = σ₂)
      (procedureDenotation (A.instantiate eagerInst) args)
      (procedureDenotation (A.instantiate lazyInst) args)
      (fun u v : sig.ret × State => u = v) :=
  eager_wrapper eagerInst lazyInst A args S
    (eager_body S A.body eagerInst lazyInst hloc
      (fun n x p hp hx => hhole n x p hp hx))
    hret

/-- The denotation of a (closed) call: read the arguments, run the procedure
    zoomed into the globals, write the result.  (Local copy of
    `Lib.RO.Instantiate.denote_call`, which this file cannot import.) -/
private theorem denote_call {l : Type} {sig : ProcedureSignature}
    (x : Setter sig.ret (ProcedureState l)) (proc : Procedure sig)
    (p : Getter sig.ParamType (ProcedureState l)) :
    programDenotation (StmtWithHoles.call x proc p)
      = (ProgramDenotation.get p >>= fun args =>
          ProgramDenotation.zoom ProcedureState.globalL (procedureDenotation proc args)
            >>= fun ret => ProgramDenotation.set x ret) := by
  simp only [StmtWithHoles.call, programDenotation]; rfl

/-- **EC's `eager call`**: a (closed) call site is eager, given a proven
    procedure-level eager specification and swap-stability of the surrounding
    argument read and result write. -/
theorem eagerR_call {l : Type} {sig : ProcedureSignature}
    (S : ProgramDenotation State Unit) (f f' : Procedure sig)
    (x : Setter sig.ret (ProcedureState l)) (p : Getter sig.ParamType (ProcedureState l))
    (hspec : ∀ args : sig.ParamType,
      ProgramDenotation.eagerR S S (fun σ₁ σ₂ : State => σ₁ = σ₂)
        (procedureDenotation f args) (procedureDenotation f' args)
        (fun u v : sig.ret × State => u = v))
    (hp : ProgramDenotation.transferBy (ProgramDenotation.zoom ProcedureState.globalL S)
      (ProgramDenotation.get p) (ProgramDenotation.get p))
    (hx : ∀ ret, ProgramDenotation.transferBy (ProgramDenotation.zoom ProcedureState.globalL S)
      (ProgramDenotation.set x ret) (ProgramDenotation.set x ret)) :
    ProgramDenotation.eagerR
      (ProgramDenotation.zoom ProcedureState.globalL S)
      (ProgramDenotation.zoom ProcedureState.globalL S)
      (fun σ₁ σ₂ : ProcedureState l => σ₁ = σ₂)
      (programDenotation (StmtWithHoles.call (h := .empty) x f p))
      (programDenotation (StmtWithHoles.call (h := .empty) x f' p))
      (fun u v : Unit × ProcedureState l => u = v) := by
  rw [denote_call, denote_call]
  refine ProgramDenotation.eagerR_seq (eagerR_self_of_transferBy hp) (fun args => ?_)
  refine ProgramDenotation.eagerR_seq ?_ (fun ret => eagerR_self_of_transferBy (hx ret))
  exact ProgramDenotation.eagerR_zoom ProcedureState.globalL (hspec args)

/-- **EC's `eager call` with an invariant**: the equality-level call rule
    strengthened by a framing self-coupling of the lazy call site. -/
theorem eagerR_call_inv {l : Type} {sig : ProcedureSignature}
    (S : ProgramDenotation State Unit) (f f' : Procedure sig)
    (x : Setter sig.ret (ProcedureState l)) (p : Getter sig.ParamType (ProcedureState l))
    {P : ProcedureState l → ProcedureState l → Prop}
    {Q : Unit × ProcedureState l → Unit × ProcedureState l → Prop}
    (hspec : ∀ args : sig.ParamType,
      ProgramDenotation.eagerR S S (fun σ₁ σ₂ : State => σ₁ = σ₂)
        (procedureDenotation f args) (procedureDenotation f' args)
        (fun u v : sig.ret × State => u = v))
    (hp : ProgramDenotation.transferBy (ProgramDenotation.zoom ProcedureState.globalL S)
      (ProgramDenotation.get p) (ProgramDenotation.get p))
    (hx : ∀ ret, ProgramDenotation.transferBy (ProgramDenotation.zoom ProcedureState.globalL S)
      (ProgramDenotation.set x ret) (ProgramDenotation.set x ret))
    (hself : ProgramDenotation.prhl2 P
      (programDenotation (StmtWithHoles.call (h := .empty) x f' p) >>= fun a =>
        ProgramDenotation.zoom ProcedureState.globalL S >>= fun _ => pure a)
      (programDenotation (StmtWithHoles.call (h := .empty) x f' p) >>= fun a =>
        ProgramDenotation.zoom ProcedureState.globalL S >>= fun _ => pure a) Q) :
    ProgramDenotation.eagerR
      (ProgramDenotation.zoom ProcedureState.globalL S)
      (ProgramDenotation.zoom ProcedureState.globalL S) P
      (programDenotation (StmtWithHoles.call (h := .empty) x f p))
      (programDenotation (StmtWithHoles.call (h := .empty) x f' p)) Q :=
  ProgramDenotation.eagerR_of_self_right (eagerR_call S f f' x p hspec hp hx) hself

/-- **EC's `eager proc I` on an abstract procedure**: the equality-level
    abstract-call rule strengthened to an invariant `P`, given a framing
    self-coupling of the lazy composite under `P` — the packaged form of EC's
    per-oracle `fl ~ fl` / `s ~ s : I ==> I` side conditions (which discharge it
    via the standard relational body machinery). -/
theorem eager_call_inv {holes : HoleSigs} {sig : ProcedureSignature}
    (eagerInst lazyInst : holes.Instantiation)
    (A : ProcedureWithHoles holes sig) (args : sig.ParamType)
    (S : ProgramDenotation State Unit)
    {P : State → State → Prop} {Q : sig.ret × State → sig.ret × State → Prop}
    (hloc : SwapLoc (ProgramDenotation.zoom ProcedureState.globalL S) A.body)
    (hret : ProgramDenotation.transferBy
      (ProgramDenotation.zoom ProcedureState.globalL S)
      (ProgramDenotation.get A.return_val) (ProgramDenotation.get A.return_val))
    (hhole : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig')
        (x : Setter sig'.ret (ProcedureState (sig.LocalVariableState A.locals)))
        (p : Getter sig'.ParamType (ProcedureState (sig.LocalVariableState A.locals))),
        ProgramDenotation.transferBy (ProgramDenotation.zoom ProcedureState.globalL S)
          (ProgramDenotation.get p) (ProgramDenotation.get p) →
        (∀ ret, ProgramDenotation.transferBy (ProgramDenotation.zoom ProcedureState.globalL S)
          (ProgramDenotation.set x ret) (ProgramDenotation.set x ret)) →
        ProgramDenotation.eagerR
          (ProgramDenotation.zoom ProcedureState.globalL S)
          (ProgramDenotation.zoom ProcedureState.globalL S)
          (fun σ₁ σ₂ => σ₁ = σ₂)
          (programDenotation (StmtWithHoles.call x (eagerInst n) p))
          (programDenotation (StmtWithHoles.call x (lazyInst n) p))
          (fun u v => u = v))
    (hself : ProgramDenotation.prhl2 P
      (procedureDenotation (A.instantiate lazyInst) args >>= fun a =>
        S >>= fun _ => pure a)
      (procedureDenotation (A.instantiate lazyInst) args >>= fun a =>
        S >>= fun _ => pure a) Q) :
    ProgramDenotation.eagerR S S P
      (procedureDenotation (A.instantiate eagerInst) args)
      (procedureDenotation (A.instantiate lazyInst) args) Q :=
  ProgramDenotation.eagerR_of_self_right
    (eager_call eagerInst lazyInst A args S hloc hret hhole) hself

end GaudisCrypt
