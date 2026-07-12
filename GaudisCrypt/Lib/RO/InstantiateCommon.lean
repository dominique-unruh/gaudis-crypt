import GaudisCrypt.Language.Programs
import GaudisCrypt.Lib.RO.TransferConvert
import GaudisCrypt.Logic.PRHL.Prhl
import GaudisCrypt.Logic.PRHL2
import GaudisCrypt.Language.Footprint
import GaudisCrypt.FV

/-!
# Instantiate: shared base

RO procedure setup (`RO_lazy`/`RO_eager`, denotation bridges), the `zoom`/`transferBy`-agnostic
monad-morphism lemmas, and the Footprint confinement core (`ConfinedP`, `fvP_stmt`,
`confinedP_of_fv`, the `Lens.lift` framework, `convertL_inFootprint`). Shared by the transfer
(`TransferInstantiate`) and relational (`ROCouplingEquiv`) developments.
-/

namespace GaudisCrypt.Lib.RO.Instantiate

open GaudisCrypt
open GaudisCrypt
open GaudisCrypt
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


/-! ### Denotation bridges: the procedures *are* `lazy_query`/`random_oracle_query`.

(`zoom` being a monad morphism — `ProgramDenotation.zoom_pure`/`zoom_bind` — now
lives in `GaudisCrypt`; the `transferBy` lift `transferBy_zoom`
in `GaudisCrypt.Logic.TransferBy`.) -/

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

/-- `procedureDenotation` of an instantiated procedure is `procWrap` of its body
    (`procWrap` now lives in `GaudisCrypt`). -/
theorem procedureDenotation_eq_procWrap {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType) (inst : roHoles.Instantiation) :
    procedureDenotation (A.instantiate inst) args
      = procWrap A.return_val (sig.localVariableInit A.locals args)
          (programDenotation (A.body.instantiate inst)) :=
  procedureDenotation_eq_procWrap_gen A args inst


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


/-- **The full probabilistic footprint of a procedure**: the body's footprint joined with the
    return getter's.  A single `fvP_proc A ≤ R` bound feeds *both* the body confinement and the
    return-value condition — replacing the separate `hbody`/`hret` hypotheses. -/
noncomputable def fvP_proc {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) :
    Footprint (ProcedureState (sig.LocalVariableState A.locals)) :=
  fvP_stmt A.body ⊔ (ProgramDenotation.get A.return_val).footprint

theorem fvP_stmt_body_le_fvP_proc {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) : fvP_stmt A.body ≤ fvP_proc A := le_sup_left

theorem get_return_val_le_fvP_proc {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) :
    (ProgramDenotation.get A.return_val).footprint ≤ fvP_proc A := le_sup_right

/-- **`glob A`** — the EasyCrypt-style global window of a procedure: the `touched_getter` of its
    footprint `fvP_proc A`.  `(glob A).get x = (glob A).get y` iff `x`, `y` agree on everything `A`
    owns (they differ only outside `fvP_proc A`) — i.e. `={glob A}`. -/
noncomputable def glob {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) :
    Getter (Quotient ((fvP_proc A)ᶜ).orbit_setoid)
      (ProcedureState (sig.LocalVariableState A.locals)) :=
  (fvP_proc A).touched_getter


-- `factor_of_inFootprint` (the `inFootprint` factorization through a lens window) was
-- generic, not RO-specific; it now lives in `GaudisCrypt.ProbProgramRange` and is
-- reused here and by the pRHL adversary rule.


-- `Mlocalized_in_footprint` (an `M`-localized kernel lies in `M.footprint`) was a general
-- `Footprint` fact, not RO-specific; it now lives in `GaudisCrypt.Language.Footprint` and is
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
def ConfinedP {holes : HoleSigs} {l : Type} (R : Footprint (ProcedureState l)) :
    StmtWithHoles holes l → Prop
  | .skip => True
  | .sample x e =>
      (programDenotation (StmtWithHoles.sample x e : Stmt l)).inFootprint R
  | .call' x ls b r p =>
      (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l)).inFootprint R
  | .hole _ x p => (ProgramDenotation.get p).inFootprint R ∧
      (∀ ret, (ProgramDenotation.set x ret).inFootprint R)
  | .seq s1 s2 => ConfinedP R s1 ∧ ConfinedP R s2
  | .ifThenElse c t e =>
      (ProgramDenotation.get c).inFootprint R ∧ ConfinedP R t ∧ ConfinedP R e
  | .while c t => (ProgramDenotation.get c).inFootprint R ∧ ConfinedP R t


/-- **`fvP`-disjointness ⟹ `ConfinedP` — COMPLETE, no `sorry`.**  The full structural reduction
    that `confined_of_fv` (`DetermFootprint`) could only achieve modulo the `get` `sorry`
    (`get_confined_of_fv`), the orthogonal `call'` `sorry`, and an *assumed* setter bridge
    (`hset`).  Over `Footprint` every leaf — get, set, sample, *and the nested `call'`* —
    discharges by the litmus (self-range, `inFootprint_selfRange`), so the reduction is total.
    Composing with `confinedP_loc`/`confinedP_locP` gives the two main theorems directly from a
    footprint-disjointness hypothesis. -/
theorem confinedP_of_fv {holes : HoleSigs} {l : Type}
    (R : Footprint (ProcedureState l))
    (hc : ∀ {sig : ProcedureSignature}, HoleIndex holes sig → Countable sig.ParamType) :
    ∀ (A : StmtWithHoles holes l), fvP_stmt A ≤ R → ConfinedP R A
  | .skip, _ => trivial
  | .sample x e, h => by
      show (programDenotation (StmtWithHoles.sample x e : Stmt l)).inFootprint R
      exact ProgramDenotation.inFootprint_of_footprint_le h
  | .call' x ls b r p, h => by
      show (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l)).inFootprint R
      exact ProgramDenotation.inFootprint_of_footprint_le h
  | .hole n x p, h =>
      haveI := hc n
      ⟨get_confinedP_of_fv p (le_sup_left.trans h),
        fun ret => set_confinedP_of_fv x ret
          ((le_iSup (fun ret => (ProgramDenotation.set x ret).footprint) ret).trans
              (le_sup_right.trans h))⟩
  | .seq s1 s2, h =>
      ⟨confinedP_of_fv R hc s1 (le_sup_left.trans h),
        confinedP_of_fv R hc s2 (le_sup_right.trans h)⟩
  | .ifThenElse c t e, h =>
      ⟨get_confinedP_of_fv c (le_sup_left.trans (le_sup_left.trans h)),
        confinedP_of_fv R hc t (le_sup_right.trans (le_sup_left.trans h)),
        confinedP_of_fv R hc e (le_sup_right.trans h)⟩
  | .«while» c t, h =>
      ⟨get_confinedP_of_fv c (le_sup_left.trans h),
        confinedP_of_fv R hc t (le_sup_right.trans h)⟩



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
    footprint.**  Ingredient of the `call'` FV-soundness case: `f` outside `Lens.reduceFootprint globalL Y`
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
    (procedureDenotation ⟨ls, b, r⟩ av).inFootprint (Lens.reduceFootprint ProcedureState.globalL Y) := by
  rw [inFootprint_iff_clean]
  intro f hf
  have hF : ProcedureState.globalL.liftSubProbability f ∈ Yᶜ.updates := by
    show ProcedureState.globalL.liftSubProbability f ∈ Submonoid.centralizer Y.updates
    rw [Submonoid.mem_centralizer_iff]
    intro k hk
    apply Lens.reduceSubProbability_ext ProcedureState.globalL
    intro i o
    have hgen : Lens.reduceSubProbability ProcedureState.globalL (k, i, o)
        ∈ (Lens.reduceFootprint ProcedureState.globalL Y).updates := by
      rw [Lens.reduceFootprint, Footprint.from_updates]
      exact Set.subset_centralizer_centralizer
        ⟨(k, i, o), ⟨hk, Set.mem_univ _, Set.mem_univ _⟩, rfl⟩
    have hcomm : Lens.reduceSubProbability ProcedureState.globalL (k, i, o) * f
        = f * Lens.reduceSubProbability ProcedureState.globalL (k, i, o) :=
      (Submonoid.mem_centralizer_iff.mp hf) _ hgen
    rw [Lens.reduceSubProbability_mul_right, Lens.reduceSubProbability_mul_left] at hcomm
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
          (Lens.reduceFootprint ProcedureState.globalL (FVP.fvP_stmt b)) ⊔
      (Lens.liftFootprint ProcedureState.globalL
          (Lens.reduceFootprint ProcedureState.globalL ((ProgramDenotation.get r).footprint)) ⊔
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
          ≤ Lens.reduceFootprint ProcedureState.globalL Y :=
        ProgramDenotation.footprint_le_of_inFootprint
          (procedureDenotation_inFootprint_reduce ls b r av Y le_sup_left le_sup_right)
      refine le_trans (Lens.liftFootprint_mono _ hpr) ?_
      have hYle : Y ≤ FVP.fvP_stmt b ⊔ (ProgramDenotation.get r).footprint := by
        refine sup_le ?_ le_sup_right
        exact le_trans (le_trans (programDenotation_footprint_le_fvP_stmt b) hbody) le_sup_left
      refine le_trans (Lens.liftFootprint_mono _ (Lens.reduceFootprint_mono _ hYle)) ?_
      rw [Lens.reduceFootprint_sup, Lens.liftFootprint_sup]
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
  -- `FVP.fvP_proc A = Lens.reduceFootprint globalL (FVP.fvP_stmt body) ⊔ Lens.reduceFootprint globalL (get return)`.
  rw [show FVP.fvP_proc A =
      Lens.reduceFootprint ProcedureState.globalL (FVP.fvP_stmt A.body) ⊔
        Lens.reduceFootprint ProcedureState.globalL ((ProgramDenotation.get A.return_val).footprint)
      from rfl] at hdisj
  -- `roLift = globalL.chain random_oracle_state`; both summands go via `reduce_chain_le_compl`.
  show fvP_stmt A.body ⊔ (ProgramDenotation.get A.return_val).footprint
      ≤ ((ProcedureState.globalL.chain random_oracle_state).footprint)ᶜ
  refine sup_le ?_ ?_
  · -- body: `Lens.reduceFootprint (fvP_stmt) ≤ Lens.reduceFootprint (FVP.fvP_stmt) ≤ FVP.fvP_proc ≤ (ros)ᶜ`.
    refine reduce_chain_le_compl (le_trans (Lens.reduceFootprint_mono _ (fvP_stmt_le_FVP A.body)) ?_)
    exact le_trans le_sup_left hdisj
  · -- return: `Lens.reduceFootprint (get return) ≤ FVP.fvP_proc ≤ (ros)ᶜ`.
    exact reduce_chain_le_compl (le_trans le_sup_right hdisj)

end GaudisCrypt.Lib.RO.Instantiate
