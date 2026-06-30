import GaudisCrypt.Language.Programs
import GaudisCrypt.Lib.RO.Transfer
import GaudisCrypt.Logic.PRHL.Prhl
import GaudisCrypt.Logic.PRHL2
import GaudisCrypt.Footprint

/-!
# Instantiate: shared base

RO procedure setup (`RO_lazy`/`RO_eager`, denotation bridges), the `zoom`/`transferBy`-agnostic
monad-morphism lemmas, and the Footprint confinement core (`ConfinedP`, `fvP_stmt`,
`confinedP_of_fv`, the `Lens.lift` framework, `convertL_inFootprint`). Shared by the transfer
(`TransferInstantiate`) and relational (`ROCouplingEquiv`) developments.
-/

namespace GaudisCrypt.Lib.RO.Instantiate

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics
open GaudisCrypt.Language.Programs
open Classical


/-- The ambient state of an RO adversary is the RO `state`. -/
instance roSpec : ProgramSpec := ⟨state⟩


/-- `State` (= `state`) is inhabited — needed for `Lens.lift_inRange_chain`'s
    `factor_of_inRange` padding. -/
instance : Nonempty State := ⟨⟨0, 0, ""⟩⟩


/-- The oracle's signature: a query takes an `input`, returns an `output`.
    `abbrev` so `roSig.ParamType` reduces to `input` (for `DecidableEq` synthesis). -/
abbrev roSig : ProcedureSignature := { params := [input], ret := output }


/-- One oracle hole. -/
abbrev roHoles : HoleSigs := HoleSigs.empty.append roSig


/-- `convert` lifted from the RO `State` to a procedure state. -/
noncomputable def convertL {l : Type} : ProgramDenotation (ProcedureState l) Unit :=
  ProgramDenotation.zoom ProcedureState.globalL convert


/-! ## RO table as a procedure-state lens

`roLift` is the RO table viewed inside a procedure state.  The confinement theorems below all hinge
on `convertL`'s probabilistic footprint `convertL.inFootprint (roLift l).footprint`
(`convertL_inFootprint`), obtained from `convert_inFootprint_ro` via the `Lens.lift` framework. -/

/-- The RO table as a lens into a procedure state. -/
noncomputable def roLift (l : Type) : Lens (input → Option output) (ProcedureState l) :=
  ProcedureState.globalL.chain random_oracle_state


/-- `ProcedureState l` is `Countable` when its locals are (the global RO `state`
    already is) — used to discharge the `[Countable]` on the instantiation theorems. -/
instance instCountableProcedureState {l : Type} [Countable l] : Countable (ProcedureState l) :=
  Countable.of_equiv (state × l)
    { toFun := fun p => ⟨p.1, p.2⟩, invFun := fun ps => (ps.global, ps.locals),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }


/-- The oracle procedure has one local variable, of type `output`, holding the
    result that `return_val` reads back. -/
def roLocals : List (Σ t : Type, Inhabited t) := [⟨output, inferInstance⟩]


/-- The procedure's local state. -/
abbrev roLocalState : Type := roSig.LocalVariableState roLocals


/-- Read the query input.  `paramListToTuple [input] = input`, so the lens into
    the parameter tuple is the identity, lifted into the procedure state. -/
def inpL : Lens input (ProcedureState roLocalState) := (Lens.id (m := input)).intoParams


/-- Read/write the result.  `paramListToTuple [output] = output`, so likewise. -/
def outL : Lens output (ProcedureState roLocalState) := (Lens.id (m := output)).intoVars


/-- Read/write the RO table living in the global state. -/
noncomputable def roG : Lens (input → Option output) (ProcedureState roLocalState) :=
  ProcedureState.globalL.chain random_oracle_state


/-- Lazy body: sample the result (cached → point mass, else uniform), then write
    the table entry. Two clean-lens statements; denotes to `lazy_query`. -/
noncomputable def RO_lazy_body : StmtWithHoles .empty roLocalState :=
  StmtWithHoles.seq
    (StmtWithHoles.sample outL
      ⟨fun ps => match (roG.get ps) (inpL.get ps) with
                 | some y => pure y
                 | none   => SubProbability.uniform⟩)
    (StmtWithHoles.assign roG
      ⟨fun ps => fun j => if j = inpL.get ps then some (outL.get ps) else (roG.get ps) j⟩)


/-- Eager body: read the (pre-sampled) table entry into the result. Denotes to
    `random_oracle_query`. -/
noncomputable def RO_eager_body : StmtWithHoles .empty roLocalState :=
  StmtWithHoles.assign outL
    ⟨fun ps => ((roG.get ps) (inpL.get ps)).getD default⟩


/-- The lazy oracle as a closed procedure. -/
noncomputable def RO_lazy_proc : Procedure roSig := ⟨roLocals, RO_lazy_body, outL.toGetter⟩


/-- The eager oracle as a closed procedure. -/
noncomputable def RO_eager_proc : Procedure roSig := ⟨roLocals, RO_eager_body, outL.toGetter⟩


/-- The lazy instantiation of the single oracle hole. -/
noncomputable def RO_lazy : roHoles.Instantiation
  | _, .zero => RO_lazy_proc


/-- The eager instantiation of the single oracle hole. -/
noncomputable def RO_eager : roHoles.Instantiation
  | _, .zero => RO_eager_proc


/-! ### `zoom` is a monad morphism, and lifts `transferBy` -/

theorem zoom_pure {s t a : Type} (lens : Lens s t) (x : a) :
    ProgramDenotation.zoom lens (pure x) = (pure x : ProgramDenotation t a) := by
  funext tv
  show ((pure x : ProgramDenotation s a) (lens.get tv)) >>= (fun as => pure (as.1, lens.set as.2
      tv))
       = (pure (x, tv) : SubProbability (a × t))
  show (pure (x, lens.get tv) : SubProbability (a × s)) >>= (fun as => pure (as.1, lens.set as.2 tv))
       = (pure (x, tv) : SubProbability (a × t))
  rw [SubProbability.pure_bind]
  simp only [lens.get_set]


theorem zoom_bind {s t a b : Type} (lens : Lens s t)
    (p : ProgramDenotation s a) (k : a → ProgramDenotation s b) :
    ProgramDenotation.zoom lens (p >>= k) = ProgramDenotation.zoom lens p >>= fun a =>
        ProgramDenotation.zoom lens (k a) := by
  funext tv
  show (((p (lens.get tv)) >>= fun as => k as.1 as.2) >>= fun bs => pure (bs.1, lens.set bs.2 tv))
       = ((p (lens.get tv)) >>= fun as => pure (as.1, lens.set as.2 tv))
          >>= fun cs => (k cs.1 (lens.get cs.2)) >>= fun bs => pure (bs.1, lens.set bs.2 cs.2)
  rw [SubProbability.bind_assoc', SubProbability.bind_assoc']
  congr 1; funext as
  rw [SubProbability.pure_bind]
  simp only [lens.set_get, lens.set_set]


/-! ### Denotation bridges: the procedures *are* `lazy_query`/`random_oracle_query`. -/

theorem procDenotation_RO_eager (args : roSig.ParamType) :
    procedureDenotation RO_eager_proc args = random_oracle_query args := by
  funext st
  simp only [procedureDenotation, RO_eager_proc, RO_eager_body, StmtWithHoles.assign,
    programDenotation, random_oracle_query, ProgramDenotation.get, ProgramDenotation.set,
    bind, StateT.bind, StateT.get, StateT.set, StateT.lift, pure, StateT.pure,
    SubProbability.toProgramDenotation, MeasureTheory.Measure.dirac_bind measurable_from_top]
  refine Subtype.ext ?_
  simp only [inpL, outL, roG, Lens.intoParams, Lens.intoVars, Lens.chain, Lens.id, Lens.fst,
    ProcedureState.globalL, ProcedureState.localL, LocalVariableState.paramsL,
    LocalVariableState.varsL, Lens.toGetter, Lens.toSetter, AsGetter.toG, AsSetter.toS,
    id_eq, MeasureTheory.Measure.dirac_bind measurable_from_top,
    ProcedureSignature.localVariableInit]
  rfl


theorem procDenotation_RO_lazy (args : roSig.ParamType) :
    procedureDenotation RO_lazy_proc args = lazy_query args := by
  funext st
  simp only [procedureDenotation, RO_lazy_proc, RO_lazy_body, StmtWithHoles.assign,
    programDenotation, lazy_query, ProgramDenotation.get, ProgramDenotation.set,
        ProgramDenotation.uniform,
    bind, StateT.bind, StateT.get, StateT.set, StateT.lift, pure, StateT.pure,
    SubProbability.toProgramDenotation, MeasureTheory.Measure.dirac_bind measurable_from_top]
  refine Subtype.ext ?_
  simp only [inpL, outL, roG, Lens.intoParams, Lens.intoVars, Lens.chain, Lens.id, Lens.fst,
    ProcedureState.globalL, ProcedureState.localL, LocalVariableState.paramsL,
    LocalVariableState.varsL, Lens.toGetter, Lens.toSetter, AsGetter.toG, AsSetter.toS,
    id_eq, ProcedureSignature.localVariableInit]
  cases hc : random_oracle_state.get st args with
  | some y =>
      simp only [hc, MeasureTheory.Measure.dirac_bind measurable_from_top]
      have hfun : (fun (j : input) => if j = args then some y else random_oracle_state.get st j)
                = random_oracle_state.get st := by
        funext j; by_cases hj : j = args
        · rw [if_pos hj, hj]; exact hc.symm
        · rw [if_neg hj]
      rw [hfun, random_oracle_state.get_set]; rfl
  | none =>
      simp only [hc, bind, StateT.bind, StateT.get, StateT.set, StateT.lift, pure, StateT.pure]
      generalize (SubProbability.uniform : SubProbability output) = U
      obtain ⟨mu, hmu⟩ := U
      simp only [MeasureTheory.Measure.bind_bind measurable_from_top.aemeasurable
        measurable_from_top.aemeasurable, MeasureTheory.Measure.dirac_bind measurable_from_top]
      rfl


/-- The denotation of a procedure call, with the called procedure kept intact
    (`programDenotation` reconstructs `⟨proc.locals, proc.body, proc.return_val⟩`,
    which is `proc` by structure-eta). -/
theorem denote_call {l : Type} {sig : ProcedureSignature}
    (x : Setter sig.ret (ProcedureState l)) (proc : Procedure sig)
    (p : Getter sig.ParamType (ProcedureState l)) :
    programDenotation (StmtWithHoles.call x proc p)
      = (ProgramDenotation.get p >>= fun args =>
          ProgramDenotation.zoom ProcedureState.globalL (procedureDenotation proc args)
            >>= fun ret => ProgramDenotation.set x ret) := by
  simp only [StmtWithHoles.call, programDenotation]; rfl


/-! ## The two subtask-3 theorems

Here `A : ProcedureWithHoles roHoles sig` is an adversary procedure carrying the
single oracle hole.  `A.instantiate RO_lazy` / `A.instantiate RO_eager` fill that
hole, and `procedureDenotation _ args : ProgramDenotation state sig.ret` runs the result on
the RO global `state`. -/

/-- The procedure denotation as an explicit wrapper: initialise locals, run the
    body, extract `(return_val, global)`. -/
noncomputable def procWrap {sig : ProcedureSignature} {L : Type}
    (rv : Getter sig.ret (ProcedureState L)) (initL : L)
    (B : ProgramDenotation (ProcedureState L) Unit) : ProgramDenotation state sig.ret :=
  fun st => B ⟨st, initL⟩ >>= fun p => pure (rv.get p.2, p.2.global)


/-- `procedureDenotation` of an instantiated procedure is `procWrap` of its body. -/
theorem procedureDenotation_eq_procWrap {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType) (inst : roHoles.Instantiation) :
    procedureDenotation (A.instantiate inst) args
      = procWrap A.return_val (sig.localVariableInit A.locals args)
          (programDenotation (A.body.instantiate inst)) := by
  funext st; simp only [procedureDenotation, ProcedureWithHoles.instantiate, procWrap]; rfl


/-! ## Faithful hypothesis: the adversary confined to its private local state

The honest "`fv(A)` disjoint from `oracle_state`" reading: the adversary's own
operations live in its **private local state** `ProcedureState.localL`, which is
disjoint from the oracle (the RO table sits in `global`).  The magic is that
`liftRel P` *pins the locals to equality* — so the same confinement assumption
discharges **both** `Loc` (theorem 1) and `LocP` (theorem 2), the latter with
**no `P`-specific side condition** (subtask 3's `h'` is subsumed). -/

/-- The locals and the global part of a `ProcedureState` are disjoint lenses. -/
instance instDisjointLocalGlobal {l : Type} :
    disjoint (ProcedureState.localL : Lens l (ProcedureState l)) ProcedureState.globalL :=
  ⟨fun _ _ _ => rfl⟩


instance instNonemptyProcedureState {l : Type} [Nonempty l] : Nonempty (ProcedureState l) :=
  ⟨⟨Classical.arbitrary State, Classical.arbitrary l⟩⟩


/-- The single `roHoles` hole has signature `roSig`, whose query type is
    `Countable`.  (`HoleIndex roHoles sig` forces `sig = roSig`.) -/
theorem roHole_paramType_countable {sig : ProcedureSignature}
    (n : HoleIndex roHoles sig) : Countable sig.ParamType := by
  cases n with
  | zero => exact inferInstanceAs (Countable input)
  | succ i => exact nomatch i


/-- **Self-range over `Footprint` (PROVEN).**  For any program with countable return,
    `p.inFootprint p.footprint`.  This is *exactly* the statement that is FALSE for `DetermFootprint`
    (witness: `range_get_fst_eq_bot`), whose failure forced `get_confined_of_fv`/`call'` to be
    `sorry`.  Every leaf bridge below is a corollary. -/
theorem inFootprint_selfRange {a s : Type} (p : ProgramDenotation s a) :
    p.inFootprint p.footprint :=
  ProgramDenotation.inFootprint_of_footprint_le (le_refl _)


/-- **The `get` bridge over `Footprint` — PROVEN (the litmus).**  The probabilistic counterpart
    of `get_confined_of_fv` (the open `sorry`): where the `DetermFootprint` bridge is self-range for a
    read (false), this is the litmus, which holds for any read with countable result. -/
theorem get_confinedP_of_fv {a l : Type} (c : Getter a (ProcedureState l))
    {R : Footprint (ProcedureState l)} (h : (ProgramDenotation.get c).footprint ≤ R) :
    (ProgramDenotation.get c).inFootprint R :=
  ProgramDenotation.inFootprint_of_footprint_le h


/-- **The setter bridge over `Footprint` — PROVEN (the litmus).**  In `confined_of_fv` the
    setter bridge had to be *assumed* (`hset`); here it is the litmus, for free. -/
theorem set_confinedP_of_fv {a l : Type} (y : Setter a (ProcedureState l)) (w : a)
    {R : Footprint (ProcedureState l)} (h : (ProgramDenotation.set y w).footprint ≤ R) :
    (ProgramDenotation.set y w).inFootprint R :=
  ProgramDenotation.inFootprint_of_footprint_le h


/-- **The probabilistic footprint of a statement.**  The `Footprint` analogue of `fv_stmt`,
    defined *directly* as the join of each leaf's own `footprint` — no `fv_reduce`/`fv_extend`
    machinery is needed, because self-range makes every program its own footprint.  In particular
    the nested `call'` leaf is just `(programDenotation (call' …)).footprint`. -/
noncomputable def fvP_stmt {holes : HoleSigs} {l : Type} :
    StmtWithHoles holes l → Footprint (ProcedureState l)
  | .skip => ⊥
  | .sample x e => (programDenotation (StmtWithHoles.sample x e : Stmt l)).footprint
  | .call' x ls b r p => (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l)).footprint
  | .hole _ x p => (ProgramDenotation.get p).footprint ⊔ (⨆ ret, (ProgramDenotation.set x
      ret).footprint)
  | .seq s1 s2 => fvP_stmt s1 ⊔ fvP_stmt s2
  | .ifThenElse c t e => (ProgramDenotation.get c).footprint ⊔ fvP_stmt t ⊔ fvP_stmt e
  | .while c t => (ProgramDenotation.get c).footprint ⊔ fvP_stmt t


/-- **Factorization**: a program confined to `L`'s probabilistic range comes from running some
    inner program on the `L`-content. The `inFootprint` analogue of `Lens.factor_of_inRange`. -/
theorem factor_of_inFootprint {c s a : Type} [Nonempty s] (L : Lens c s) {Adv : ProgramDenotation s
    a}
    (h : Adv.inFootprint L.footprint) : Adv = L.lift (L.factor Adv) := by
  funext σ
  set f : s → s := fun σ' => L.set (L.get σ') σ with hf_def
  have h_fσ_pad : f (L.set (L.get σ) (Classical.arbitrary s)) = σ := by
    show L.set (L.get (L.set (L.get σ) (Classical.arbitrary s))) σ = σ
    rw [L.set_get, L.get_set]
  have h_f_mem : diracKer f ∈ ((L.footprint)ᶜ).updates := by
    refine Submonoid.mem_centralizer_iff.mpr ?_
    intro k hk
    have hfgen : diracKer f ∈
        Submonoid.centralizer (Set.range fun g : Function.End c => diracKer (L.liftFunction g)) := by
      refine Submonoid.mem_centralizer_iff.mpr ?_
      rintro _ ⟨g, rfl⟩
      rw [diracKer_mul, diracKer_mul]; congr 1
      show L.liftFunction g ∘ f = f ∘ L.liftFunction g
      funext σ'
      show L.liftFunction g (f σ') = f (L.liftFunction g σ')
      simp only [Lens.liftFunction, hf_def, L.set_get, L.set_set]
    exact (Submonoid.mem_centralizer_iff.mp hk (diracKer f) hfgen).symm
  have h_iv : Adv σ
      = (Adv (L.set (L.get σ) (Classical.arbitrary s)))
          >>= (fun xs : a × s => (pure (xs.1, f xs.2) : SubProbability (a × s))) := by
    conv_lhs => rw [← h_fσ_pad]
    exact inFootprint_subprob h h_f_mem _
  change Adv σ
      = ((Adv (L.set (L.get σ) (Classical.arbitrary s)))
            >>= fun xσ' : a × s => (pure (xσ'.1, L.get xσ'.2) : SubProbability (a × c)))
          >>= fun xc : a × c => (pure (xc.1, L.set xc.2 σ) : SubProbability (a × s))
  rw [h_iv, SubProbability.bind_assoc']
  congr 1; funext xσ'
  rw [SubProbability.pure_bind]


-- `Mlocalized_in_footprint` (an `M`-localized kernel lies in `M.footprint`) was a general
-- `Footprint` fact, not RO-specific; it now lives in `GaudisCrypt.Footprint` and is
-- reused here (and by the `fvP` footprint layer).

/-- **A lift lives in its lens's probabilistic range** — the `inFootprint` analogue of
    `Lens.lift_inRange_self`. The `y`-generator of `(M.lift Q).footprint` is the `M`-localized
    kernel for `Q` conditioned on returning `y`, so `Mlocalized_in_footprint` applies. -/
theorem lift_inFootprint_self {c s a : Type}
    (M : Lens c s) (Q : ProgramDenotation c a) : (M.lift Q).inFootprint M.footprint := by
  refine ProgramDenotation.inFootprint_of_footprint_le ?_
  refine (Footprint.from_le_iff _ _).mpr ?_
  rintro k ⟨y, rfl⟩
  show (fun st => (M.lift Q) st >>= fun w : a × s => if w.1 = y then pure w.2 else ⊥)
       ∈ M.footprint.updates
  have heq : (fun st => (M.lift Q) st >>= fun w : a × s => if w.1 = y then pure w.2 else ⊥)
           = (fun st => (Q (M.get st) >>= fun xc : a × c => if xc.1 = y then pure xc.2 else ⊥)
               >>= fun mc' => (pure (M.set mc' st) : SubProbability s)) := by
    funext st
    show (Q (M.get st) >>= fun xc : a × c => (pure (xc.1, M.set xc.2 st) : SubProbability (a × s)))
          >>= (fun w : a × s => if w.1 = y then pure w.2 else ⊥)
       = (Q (M.get st) >>= fun xc : a × c => if xc.1 = y then pure xc.2 else ⊥)
          >>= fun mc' => (pure (M.set mc' st) : SubProbability s)
    rw [SubProbability.bind_assoc, SubProbability.bind_assoc]
    congr 1; funext xc
    rw [SubProbability.pure_bind]
    by_cases h : xc.1 = y
    · rw [if_pos h, if_pos h, SubProbability.pure_bind]
    · rw [if_neg h, if_neg h, SubProbability.bot_bind]
  rw [heq]
  exact Mlocalized_in_footprint M (fun mc => Q mc >>= fun xc => if xc.1 = y then pure xc.2 else ⊥)


/-- **Lift confines the footprint through the chained lens** — `inFootprint` analogue of
    `Lens.lift_inRange_chain`. Factor `P` as `v.lift (v.factor P)`, fold the double lift into a
    single `(L.chain v)`-lift (`lift_lift_chain`), and confine via `lift_inFootprint_self`. -/
theorem lift_inFootprint_chain {c s d a : Type} [Nonempty c]
    (L : Lens c s) (v : Lens d c) (P : ProgramDenotation c a) (hP : P.inFootprint v.footprint) :
    (L.lift P).inFootprint (L.chain v).footprint := by
  rw [factor_of_inFootprint v hP, Lens.lift_lift_chain]
  exact lift_inFootprint_self (L.chain v) (v.factor P)


/-- **`convertL` is confined to the (lifted) RO table, as a probabilistic range.** Via the lift
    framework (avoiding the `zoom`-rewrite's `state`/`State` `rw` obstacle): `convertL = globalL.lift
    convert`, and `convert.inFootprint random_oracle_state.footprint` (`convert_inFootprint_ro`). -/
theorem convertL_inFootprint {l : Type} :
    (convertL : ProgramDenotation (ProcedureState l) Unit).inFootprint (roLift l).footprint :=
  lift_inFootprint_chain ProcedureState.globalL random_oracle_state convert convert_inFootprint_ro


/-- **Probabilistic confinement predicate.** The `inFootprint`/`footprint` analogue of `Confined`:
    each leaf's footprint lies in the adversary region `L_adv`. Crucially the `get`-leaves are now
    soundly derivable from footprint disjointness (litmus), unlike `Confined` (`DetermFootprint`),
    where `get`'s `ProgramDenotation.range` collapses (the `get_confined_of_fv` sorry). -/
def ConfinedP {holes : HoleSigs} {l advSt : Type} (L_adv : Lens advSt (ProcedureState l)) :
    StmtWithHoles holes l → Prop
  | .skip => True
  | .sample x e =>
      (programDenotation (StmtWithHoles.sample x e : Stmt l)).inFootprint L_adv.footprint
  | .call' x ls b r p =>
      (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l)).inFootprint L_adv.footprint
  | .hole _ x p => (ProgramDenotation.get p).inFootprint L_adv.footprint ∧
      (∀ ret, (ProgramDenotation.set x ret).inFootprint L_adv.footprint)
  | .seq s1 s2 => ConfinedP L_adv s1 ∧ ConfinedP L_adv s2
  | .ifThenElse c t e =>
      (ProgramDenotation.get c).inFootprint L_adv.footprint ∧ ConfinedP L_adv t ∧ ConfinedP L_adv e
  | .while c t => (ProgramDenotation.get c).inFootprint L_adv.footprint ∧ ConfinedP L_adv t


/-- **`fvP`-disjointness ⟹ `ConfinedP` — COMPLETE, no `sorry`.**  The full structural reduction
    that `confined_of_fv` (`DetermFootprint`) could only achieve modulo the `get` `sorry`
    (`get_confined_of_fv`), the orthogonal `call'` `sorry`, and an *assumed* setter bridge
    (`hset`).  Over `Footprint` every leaf — get, set, sample, *and the nested `call'`* —
    discharges by the litmus (self-range, `inFootprint_selfRange`), so the reduction is total.
    Composing with `confinedP_loc`/`confinedP_locP` gives the two main theorems directly from a
    footprint-disjointness hypothesis. -/
theorem confinedP_of_fv {holes : HoleSigs} {l advSt : Type}
    (L_adv : Lens advSt (ProcedureState l))
    (hc : ∀ {sig : ProcedureSignature}, HoleIndex holes sig → Countable sig.ParamType) :
    ∀ (A : StmtWithHoles holes l), fvP_stmt A ≤ L_adv.footprint → ConfinedP L_adv A
  | .skip, _ => trivial
  | .sample x e, h => by
      show (programDenotation (StmtWithHoles.sample x e : Stmt l)).inFootprint L_adv.footprint
      exact ProgramDenotation.inFootprint_of_footprint_le h
  | .call' x ls b r p, h => by
      show (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l)).inFootprint L_adv.footprint
      exact ProgramDenotation.inFootprint_of_footprint_le h
  | .hole n x p, h =>
      haveI := hc n
      ⟨get_confinedP_of_fv p (le_sup_left.trans h),
        fun ret => set_confinedP_of_fv x ret
          ((le_iSup (fun ret => (ProgramDenotation.set x ret).footprint) ret).trans
              (le_sup_right.trans h))⟩
  | .seq s1 s2, h =>
      ⟨confinedP_of_fv L_adv hc s1 (le_sup_left.trans h),
        confinedP_of_fv L_adv hc s2 (le_sup_right.trans h)⟩
  | .ifThenElse c t e, h =>
      ⟨get_confinedP_of_fv c (le_sup_left.trans (le_sup_left.trans h)),
        confinedP_of_fv L_adv hc t (le_sup_right.trans (le_sup_left.trans h)),
        confinedP_of_fv L_adv hc e (le_sup_right.trans h)⟩
  | .«while» c t, h =>
      ⟨get_confinedP_of_fv c (le_sup_left.trans h),
        confinedP_of_fv L_adv hc t (le_sup_right.trans h)⟩

end GaudisCrypt.Lib.RO.Instantiate
