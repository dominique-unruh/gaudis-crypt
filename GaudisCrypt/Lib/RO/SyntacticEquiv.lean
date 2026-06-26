import GaudisCrypt.Language.Programs
import GaudisCrypt.Lib.RO.Transfer
import GaudisCrypt.FV
import GaudisCrypt.Logic.PRHL.Prhl
import GaudisCrypt.Logic.PRHL2
import GaudisCrypt.ProbLensRange

/-!
# Lazy/eager RO equivalence for *syntactic* adversaries

Goal (subtask 3): for any adversary `A` written in Dominique's `StmtWithHoles`
syntax, the lazy and eager instantiations of its oracle hole are related by
`Program.transfer` — `convert` slides across `A`, turning every lazy query into
an eager one. This generalizes `ROEquiv.lean` (which proves it for one fixed
loop adversary) to an arbitrary `A`, by structural induction.

## Architecture

* **Generic `transferBy` calculus** (`transferBy_pure`/`_bind`/`_zoom`,
  `zoom_pure`/`zoom_bind`): `Program.transfer = transferBy convert`; we factor
  out the relation over an arbitrary "convert" `c`, prove the monad-law
  combinators once, and a `zoom`-lifting lemma.  All **sorry-free**.
* **Body induction** (`body_transfer_gen`): every `StmtWithHoles` constructor
  reduces to the calculus + a per-hole hypothesis (`hhole`).  All seven cases
  **proven**; the only residual it touches is `transferL_while_loop`.
* **Honest locality** (`Loc`/`Stable`): since `fv_proc` is `sorry` in `FV.lean`
  (a computed footprint for an opaque getter is undefinable), the usable
  condition is *semantic*: each of the adversary's own operations commutes with
  `convert`.

## Status

`Program.transfer_instantiate` (subtask 3, theorem 1) is **fully assembled**:
it reduces (via `transfer_wrapper`) to `transfer_instantiate_body`, which is
proven by `body_transfer_gen` + `ro_hhole`.  The denotation bridges
(`procDenotation_RO_{eager,lazy}`), the hole discharge (`ro_hhole`), `denote_call`,
and the entire body induction are **proven** (sorry-free modulo the pre-existing
RO-scaffolding `sorry`s in `Basic.lean`: `Inhabited output`, `Fintype input`, …).

**`Program.transfer_instantiate` (subtask 3, theorem 1) is COMPLETE** — proven
sorry-free (modulo the pre-existing RO-scaffolding `sorry`s in `Basic.lean`:
`Inhabited output`, `Fintype input`, …).  All components are proven:
* the generic `transferBy` calculus + `zoom` morphism;
* the body induction `body_transfer_gen` (all 7 cases);
* the two denotation bridges and the hole discharge `ro_hhole`;
* the procedure wrapper `transfer_wrapper` (`procedureDenotation_eq_procWrap`,
  `procWrap_convertL_in`, `procWrap_convert_out` ← `rv_convert_invariant`);
* `transferL_while_loop`, via the state-generic `transferBy_while_loop` (a port
  of `Program.transfer_while_loop`'s Kleene fixed-point argument — itself fully
  sorry-free, the RO-specific condition-commutation being supplied by `Stable`).

**Subtask 3, theorem 2** (`prhl_instantiate`, relational/coupling form) is also
**COMPLETE**, parallel to theorem 1:
* the lifted relation `liftRel`/`liftRelPost` and honest locality `LocP`/`GetOK`;
* the inductive core `body_prhl2_gen` (all 7 cases in the `prhl2` calculus —
  `bind`/`cond`/`while_loop`/`pure_pure` + `conseq`);
* `prhl2_zoom` (coupling lift through `zoom globalL`, the analogue of
  `transferBy_zoom`) and the RO hole coupling `ro_hhole_prhl`;
* the procedure wrapper `prhl_wrapper` (built like `prhl2_zoom`, bridged to
  `prhl` via `prhl2.to_prhl`).

**Both subtask-3 theorems are proved, sorry-free** modulo the pre-existing
RO-scaffolding `sorry`s in `Basic.lean` (`Inhabited output`, `Fintype input`,
`Countable state`, …) — none introduced here.
-/

namespace GaudisCrypt.Lib.RO.SyntacticEquiv

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics
open GaudisCrypt.Language.Programs
open FV

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
noncomputable def convertL {l : Type} : Program (ProcedureState l) Unit :=
  Program.zoom ProcedureState.globalL convert

/-! ## Faithful `fv`-based locality (bridge to `Loc`)

To restate the theorems with the real `fv` (subtask 3's "fv(A) disjoint
oracle_state"), we derive the semantic locality `Loc` from `fv_stmt`-disjointness.
The crux is `convertL.inRange (roLift).range`, via the range-framework lemma
`lift_inRange_chain` (a program confined to `v` lifts to one confined to `L∘v`). -/

-- `Program.wp_lift`, `Lens.lift_lift_chain`, `Lens.lift_inRange_self` and the key
-- `Lens.lift_inRange_chain` (a program confined to `v` lifts to one confined to
-- `L∘v`) now live — proven, no `sorry` — in `ProgramRange.lean`.

/-- The RO table as a lens into a procedure state. -/
noncomputable def roLift (l : Type) : Lens (input → Option output) (ProcedureState l) :=
  ProcedureState.globalL.chain random_oracle_state

/-- `ProcedureState l` is `Countable` when its locals are (the global RO `state`
    already is) — needed for `commute_of_disjoint_lens` and the `prhl2` rules. -/
instance instCountableProcedureState {l : Type} [Countable l] : Countable (ProcedureState l) :=
  Countable.of_equiv (state × l)
    { toFun := fun p => ⟨p.1, p.2⟩, invFun := fun ps => (ps.global, ps.locals),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }

/-- `convertL` is confined to the (lifted) RO table — instance of
    `Lens.lift_inRange_chain` (ProgramRange.lean). -/
theorem convertL_inRange {l : Type} : convertL.inRange (roLift l).range :=
  Lens.lift_inRange_chain ProcedureState.globalL random_oracle_state convert convert_inRange_ro

/-! ## Concrete RO instantiations

We make the oracle hole concrete: `RO_lazy`/`RO_eager` are *actual* procedures
(over the RO `state`). Their bodies are the syntactic lazy/eager queries, and
the bridge lemmas record that they denote to the semantic `lazy_query` /
`random_oracle_query`. With these in hand we can state the two subtask-3
theorems directly in terms of `Procedure.instantiate` / `Program.transfer` /
`Program.prhl`. -/

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

/-- Lift a state relation `P` to a post-relation on `(result, state)` pairs:
    require equal results and `P` on the states. -/
def liftPost {α : Type} (P : state → state → Prop) : α × state → α × state → Prop :=
  fun u v => u.1 = v.1 ∧ P u.2 v.2

/-! ## Generic `transferBy` calculus

`Program.transfer` is `transferBy convert`.  We need the same relation at the
`ProcedureState` level (with `convertL`), so we factor out a generic version
`transferBy c p q := (p >>= a => c >>= _ => pure a) = (c >>= _ => q)` over an
arbitrary "convert" program `c`, prove the monad-law combinators once, and a
`zoom` lifting lemma — `convertL = zoom globalL convert`, and `zoom` is a monad
morphism, so any state-level transfer lifts to a zoomed `ProcedureState` one. -/

/-- Generic transfer: `c` slides from after `p` to before `q`, preserving the value. -/
def transferBy {s α : Type} (c : Program s Unit) (p q : Program s α) : Prop :=
  (p >>= fun a => c >>= fun _ => pure a) = (c >>= fun _ => q)

/-- `pure` transfers to itself (generic). -/
theorem transferBy_pure {s α : Type} {c : Program s Unit} (a : α) :
    transferBy c (pure a) (pure a) := by
  show ((pure a : Program s α) >>= fun a' => c >>= fun _ => pure a') = (c >>= fun _ => pure a)
  rw [Program.pure_bind]

/-- `transferBy` chains under `>>=` (generic; copy of `Program.transfer_bind`). -/
theorem transferBy_bind {s α β : Type} {c : Program s Unit}
    {p q : Program s α} {p' q' : α → Program s β}
    (h : transferBy c p q) (h' : ∀ a, transferBy c (p' a) (q' a)) :
    transferBy c (p >>= p') (q >>= q') := by
  show ((p >>= p') >>= fun b => c >>= fun _ => pure b) = (c >>= fun _ => q >>= q')
  rw [Program.bind_assoc]
  conv_lhs =>
    rhs; ext a
    rw [show (p' a >>= fun b => c >>= fun _ => (Pure.pure b : Program s β))
          = (c >>= fun _ => q' a) from h' a]
  conv_lhs =>
    rhs; ext a
    rw [show (c >>= fun _ => q' a)
          = (c >>= fun _ => (Pure.pure a : Program s α)) >>= q' from by
        rw [Program.bind_assoc]; congr 1; funext _; rw [Program.pure_bind]]
  rw [← Program.bind_assoc]
  rw [show (p >>= fun a => c >>= fun _ => (Pure.pure a : Program s α))
        = (c >>= fun _ => q) from h]
  rw [Program.bind_assoc]

/-! ### `zoom` is a monad morphism, and lifts `transferBy` -/

theorem zoom_pure {s t a : Type} (lens : Lens s t) (x : a) :
    Program.zoom lens (pure x) = (pure x : Program t a) := by
  funext tv
  show ((pure x : Program s a) (lens.get tv)) >>= (fun as => pure (as.1, lens.set as.2 tv))
       = (pure (x, tv) : SubProbability (a × t))
  show (pure (x, lens.get tv) : SubProbability (a × s)) >>= (fun as => pure (as.1, lens.set as.2 tv))
       = (pure (x, tv) : SubProbability (a × t))
  rw [SubProbability.pure_bind]
  simp only [lens.get_set]

theorem zoom_bind {s t a b : Type} (lens : Lens s t)
    (p : Program s a) (k : a → Program s b) :
    Program.zoom lens (p >>= k) = Program.zoom lens p >>= fun a => Program.zoom lens (k a) := by
  funext tv
  show (((p (lens.get tv)) >>= fun as => k as.1 as.2) >>= fun bs => pure (bs.1, lens.set bs.2 tv))
       = ((p (lens.get tv)) >>= fun as => pure (as.1, lens.set as.2 tv))
          >>= fun cs => (k cs.1 (lens.get cs.2)) >>= fun bs => pure (bs.1, lens.set bs.2 cs.2)
  rw [SubProbability.bind_assoc', SubProbability.bind_assoc']
  congr 1; funext as
  rw [SubProbability.pure_bind]
  simp only [lens.set_get, lens.set_set]

/-- `zoom` lifts `transferBy`: a state-level transfer becomes a zoomed one. -/
theorem transferBy_zoom {s t α : Type} (lens : Lens s t)
    {c : Program s Unit} {p q : Program s α} (h : transferBy c p q) :
    transferBy (Program.zoom lens c) (Program.zoom lens p) (Program.zoom lens q) := by
  show (Program.zoom lens p >>= fun a => Program.zoom lens c >>= fun _ => pure a)
      = (Program.zoom lens c >>= fun _ => Program.zoom lens q)
  rw [show (fun a => Program.zoom lens c >>= fun _ => (pure a : Program t α))
        = (fun a => Program.zoom lens (c >>= fun _ => pure a)) from by
      funext a; rw [zoom_bind]; congr 1; funext _; rw [zoom_pure]]
  rw [← zoom_bind, ← zoom_bind]
  rw [show (p >>= fun a => c >>= fun _ => pure a) = (c >>= fun _ => q) from h]

/-! ### Denotation bridges: the procedures *are* `lazy_query`/`random_oracle_query`. -/

theorem procDenotation_RO_eager (args : roSig.ParamType) :
    procedureDenotation RO_eager_proc args = random_oracle_query args := by
  funext st
  simp only [procedureDenotation, RO_eager_proc, RO_eager_body, StmtWithHoles.assign,
    programDenotation, random_oracle_query, Program.get, Program.set,
    bind, StateT.bind, StateT.get, StateT.set, StateT.lift, pure, StateT.pure,
    SubProbability.toProgram, MeasureTheory.Measure.dirac_bind measurable_from_top]
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
    programDenotation, lazy_query, Program.get, Program.set, Program.uniform,
    bind, StateT.bind, StateT.get, StateT.set, StateT.lift, pure, StateT.pure,
    SubProbability.toProgram, MeasureTheory.Measure.dirac_bind measurable_from_top]
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

/-! ## Honest locality + the body induction

`fv_proc` is `sorry` in `FV.lean`, and a *computed* footprint for an opaque
getter/setter is genuinely undefinable.  The honest, usable locality condition
is **semantic**: each of the adversary's own operations commutes with `convert`
(i.e. transfers to itself).  `Loc A` collects exactly these per-leaf facts.  The
oracle hole is exempt — it is handled by the `hhole` hypothesis (later
discharged by the per-query transfer lemma). -/

/-- `p` commutes with `convertL` ("transfers to itself"). -/
def Stable {l α : Type} (p : Program (ProcedureState l) α) : Prop :=
  transferBy convertL p p

/-- **`Stable` from footprint disjointness**: a program confined to the
    complement of the RO table commutes with `convertL`, i.e. is `Stable`.
    The `ProcedureState`-level analogue of `transfer_refl_of_inRange_compl`. -/
theorem stable_of_inRange_compl {l α : Type} [Countable α] [Countable l]
    {p : Program (ProcedureState l) α} (hp : p.inRange (roLift l).compl.range) : Stable p := by
  show (p >>= fun a => convertL >>= fun _ => pure a) = (convertL >>= fun _ => p)
  have hdisj : (roLift l).compl.range ≤ ((roLift l).range)ᶜ :=
    le_of_eq (TotLensRange.complement_range _)
  have h_commute : (p >>= fun a => convertL >>= fun b => pure (a, b))
                 = (convertL >>= fun b => p >>= fun a => pure (a, b)) :=
    Program.commute_of_disjoint_lens hp convertL_inRange hdisj
  have hL : (p >>= fun a => convertL >>= fun b => pure (a, b)) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : Program (ProcedureState l) α))
          = (p >>= fun a => convertL >>= fun _ => (Pure.pure a : Program (ProcedureState l) α)) := by
    rw [Program.bind_assoc]; congr 1; funext a
    rw [Program.bind_assoc]; congr 1; funext _
    rw [Program.pure_bind]
  have hR : (convertL >>= fun b => p >>= fun a => pure (a, b)) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : Program (ProcedureState l) α))
          = (convertL >>= fun _ => p) := by
    rw [Program.bind_assoc]
    congr 1; funext _
    rw [Program.bind_assoc]
    rw [show (fun a : α => pure (a, ()) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : Program (ProcedureState l) α)))
          = (fun a : α => (Pure.pure a : Program (ProcedureState l) α)) from by
        funext a; rw [Program.pure_bind]]
    exact Program.bind_pure _
  rw [← hL, h_commute, hR]

/-! ### Discharging `Stable` from lens-range disjointness (the faithful-for-lens bridge)

For **lens-based** getters/setters, `Stable` (and hence each `Loc` leaf) follows
from the lens's `range` being disjoint from the RO table — the faithful reading of
subtask 3's "`fv(A)` disjoint from `oracle_state`".  No semantic locality needs to
be checked by hand: `inRange_get`/`inRange_set` give the footprint, and
`stable_of_inRange_compl` converts it to `Stable`.

(For a *general*, opaque getter/setter this is impossible: `fv_getter c =
Program.range (Program.get c)` and `p.inRange (Program.range p)` is **false** in
general — it requires the program's commutant to be double-commutant-closed,
which fails for arbitrary kernels.  Lens reads/writes are exactly the case where
it holds, via `inRange_get`/`inRange_set`.) -/

/-- **`Stable` for a lens read disjoint from the RO table.**  Discharges the
    `Loc` obligation for hole reads (`get p`) and `if`/`while` guards. -/
theorem stable_get_lens {l a : Type} [Countable l] [Countable a]
    (c : Lens a (ProcedureState l)) (h : c.range ≤ (roLift l).compl.range) :
    Stable (Program.get c) :=
  stable_of_inRange_compl (Program.inRange_mono (Program.inRange_get c) h)

/-- **`Stable` for a lens write disjoint from the RO table.**  Discharges the
    `Loc` obligation for hole writes (`set x ret`). -/
theorem stable_set_lens {l a : Type} [Countable l]
    (x : Lens a (ProcedureState l)) (h : x.range ≤ (roLift l).compl.range) (v : a) :
    Stable (Program.set x v) :=
  stable_of_inRange_compl (Program.inRange_mono (Program.inRange_set x v) h)

/-- **`Stable` for a `sample` whose read `e` and write `x` are lens-disjoint from
    the RO table.**  Discharges the `Loc` obligation for `.sample` leaves. -/
theorem stable_sample_lens {l a : Type} [Countable l] [Countable a]
    (x : Lens a (ProcedureState l)) (e : Lens (SubProbability a) (ProcedureState l))
    (hx : x.range ≤ (roLift l).compl.range) (he : e.range ≤ (roLift l).compl.range) :
    Stable (programDenotation
      (StmtWithHoles.sample (Lens.toSetter x) (Lens.toGetter e) : Stmt l)) := by
  apply stable_of_inRange_compl
  simp only [programDenotation]
  refine Program.inRange_bind (Program.inRange_mono (Program.inRange_get e) he) ?_
  intro μ
  refine Program.inRange_bind (Program.inRange_toProgram μ _) ?_
  intro v
  exact Program.inRange_mono (Program.inRange_set x v) hx

/-- Locality: every operation of `A` *outside the oracle interface* is `Stable`.
    For a hole, this is the surrounding read (`get p`) and write (`set x`) — the
    oracle query itself is *not* required stable (it transfers, lazy↦eager). -/
def Loc {holes : HoleSigs} {l : Type} : StmtWithHoles holes l → Prop
  | .skip => True
  | .sample x e => Stable (programDenotation (StmtWithHoles.sample x e : Stmt l))
  | .call' x ls b r p => Stable (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l))
  | .hole _ x p => Stable (Program.get p) ∧ (∀ ret, Stable (Program.set x ret))
  | .seq s1 s2 => Loc s1 ∧ Loc s2
  | .ifThenElse c t e => Stable (Program.get c) ∧ Loc t ∧ Loc e
  | .while c t => Stable (Program.get c) ∧ Loc t

/-- **End-to-end: `Loc` from lens-range disjointness.**  For an adversary built
    from lenses whose ranges are disjoint from the RO table, the whole semantic
    `Loc` predicate is discharged mechanically by the `stable_*_lens` lemmas —
    the faithful "`fv(A)` disjoint from `oracle_state`" hypothesis for the
    lens-based fragment.  (Composed with `Program.transfer_instantiate`, this
    gives the lazy=eager equivalence for any such adversary.) -/
example {l a : Type} [Countable l] [Countable a]
    (c : Lens Bool (ProcedureState l))
    (x : Lens a (ProcedureState l)) (e : Lens (SubProbability a) (ProcedureState l))
    (hc : c.range ≤ (roLift l).compl.range)
    (hx : x.range ≤ (roLift l).compl.range) (he : e.range ≤ (roLift l).compl.range) :
    Loc (StmtWithHoles.ifThenElse (Lens.toGetter c)
          (StmtWithHoles.sample (Lens.toSetter x) (Lens.toGetter e))
          StmtWithHoles.skip : StmtWithHoles roHoles l) :=
  ⟨stable_get_lens c hc, stable_sample_lens x e hx he, trivial⟩

/-! ### Generic Kleene closure of `transferBy` under `while_loop`

A state-and-`c`-generic port of `Program.transfer_while_loop`.  The only step
that was RO-specific there (the condition commuting with `convert`) is taken as
a hypothesis `h_cond_comm` here — at the `ProcedureState` level it is supplied
by `Stable cond`. -/

/-- Intermediate iteration: the lazy body, but with `c` in the else branch. -/
private noncomputable def whileBy_Ψ {s : Type} (c : Program s Unit)
    (cond : Program s Bool) (body_lazy : Program s Unit) :
    (Unit → Program s Unit) →𝒄 (Unit → Program s Unit) :=
  OmegaCompletePartialOrder.ContinuousHom.ofFun fun (fp : Unit → Program s Unit) => fun () =>
    do if ← cond then body_lazy; fp () else c

/-- Lazy iterate composed with `c` equals the `Ψ`-iterate. -/
private lemma whileBy_kleene_lazy {s : Type} (c : Program s Unit)
    (cond : Program s Bool) (body_lazy : Program s Unit) :
    ∀ n : ℕ,
    (((while_iteration cond body_lazy)^[n] (⊥ : Unit → Program s Unit)) () >>= (fun _ => c))
    = ((whileBy_Ψ c cond body_lazy)^[n] (⊥ : Unit → Program s Unit)) () := by
  intro n
  induction n with
  | zero =>
    change ((⊥ : Program s Unit) >>= fun _ => c) = (⊥ : Program s Unit)
    exact Program.bot_bind _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (((cond) >>= fun b =>
              if b = true then body_lazy >>= fun _ => ((while_iteration cond body_lazy)^[n] ⊥) ()
              else (pure () : Program s Unit)) >>= fun _ => c)
        = (cond) >>= fun b =>
              if b = true then body_lazy >>= fun _ => ((whileBy_Ψ c cond body_lazy)^[n] ⊥) ()
              else c
    rw [Program.bind_assoc]
    congr 1; funext b
    by_cases h : b = true
    · simp only [h, if_true]; rw [Program.bind_assoc]; congr 1; funext _; exact ih
    · simp only [h, if_false]; exact Program.pure_bind () _

/-- `c` prepended to the eager iterate equals the `Ψ`-iterate. -/
private lemma whileBy_kleene_eager {s : Type} (c : Program s Unit) {cond : Program s Bool}
    (h_cond_comm : ∀ {β : Type} (k : Bool → Program s β),
        (cond >>= fun b => c >>= fun _ => k b) = (c >>= fun _ => cond >>= k))
    {body_lazy body_eager : Program s Unit}
    (h_body : (body_lazy >>= fun _ : Unit => c) = (c >>= fun _ : Unit => body_eager)) :
    ∀ n : ℕ,
    c >>= (fun _ => ((while_iteration cond body_eager)^[n] (⊥ : Unit → Program s Unit)) ())
    = ((whileBy_Ψ c cond body_lazy)^[n] (⊥ : Unit → Program s Unit)) () := by
  intro n
  induction n with
  | zero =>
    change (c >>= fun _ => (⊥ : Program s Unit)) = (⊥ : Program s Unit)
    exact Program.bind_bot _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (c >>= fun _ => (cond) >>= fun b =>
              if b = true then body_eager >>= fun _ => ((while_iteration cond body_eager)^[n] ⊥) ()
              else (pure () : Program s Unit))
        = (cond) >>= fun b =>
              if b = true then body_lazy >>= fun _ => ((whileBy_Ψ c cond body_lazy)^[n] ⊥) ()
              else c
    rw [show (c >>= fun _ => (cond) >>=
              fun b => if b = true then body_eager >>= fun _ =>
                  ((while_iteration cond body_eager)^[n] ⊥) () else (pure () : Program s Unit))
            = ((cond) >>= fun b => c >>= fun _ =>
                if b = true then body_eager >>= fun _ =>
                  ((while_iteration cond body_eager)^[n] ⊥) () else (pure () : Program s Unit)) from
        (h_cond_comm _).symm]
    congr 1; funext b
    by_cases h : b = true
    · simp only [h, if_true]
      rw [← Program.bind_assoc]
      rw [show (c >>= fun _ : Unit => body_eager) = (body_lazy >>= fun _ : Unit => c) from h_body.symm]
      rw [Program.bind_assoc]; congr 1; funext _; exact ih
    · simp only [h, if_false]; exact Program.bind_pure _

/-- **Generic `while_loop` closure for `transferBy`.** -/
theorem transferBy_while_loop {s : Type} (c : Program s Unit) {cond : Program s Bool}
    (h_cond_comm : ∀ {β : Type} (k : Bool → Program s β),
        (cond >>= fun b => c >>= fun _ => k b) = (c >>= fun _ => cond >>= k))
    {body_lazy body_eager : Program s Unit}
    (h_body : (body_lazy >>= fun _ : Unit => c) = (c >>= fun _ : Unit => body_eager)) :
    transferBy c (while_loop cond body_lazy) (while_loop cond body_eager) := by
  show (while_loop cond body_lazy >>= fun u : Unit => c >>= fun _ : Unit => (Pure.pure u : Program s Unit))
      = (c >>= fun _ : Unit => while_loop cond body_eager)
  rw [show (fun u : Unit => c >>= fun _ : Unit => (Pure.pure u : Program s Unit)) = (fun _ : Unit => c) from by
        funext u
        rw [show (Pure.pure u : Program s Unit) = (Pure.pure () : Program s Unit) from rfl]
        exact Program.bind_pure _]
  let F_lazy := while_iteration cond body_lazy
  let F_eager := while_iteration cond body_eager
  have hL_chain : ∀ n, ((F_lazy^[n] ⊥ : Unit → Program s Unit) () >>= (fun _ => c))
                     = ((whileBy_Ψ c cond body_lazy)^[n] ⊥ : Unit → Program s Unit) () :=
    whileBy_kleene_lazy c cond body_lazy
  have hE_chain : ∀ n, c >>= (fun _ => (F_eager^[n] ⊥ : Unit → Program s Unit) ())
                     = ((whileBy_Ψ c cond body_lazy)^[n] ⊥ : Unit → Program s Unit) () :=
    whileBy_kleene_eager c h_cond_comm h_body
  have h_bind_c_cont : OmegaCompletePartialOrder.ωScottContinuous
      (fun (m : Program s Unit) => m >>= fun _ => c) := by fun_prop
  have h_c_bind_cont : OmegaCompletePartialOrder.ωScottContinuous
      (fun (m : Program s Unit) => c >>= fun _ => m) := by fun_prop
  change (F_lazy.lfp ()) >>= (fun _ => c) = c >>= (fun _ => F_eager.lfp ())
  let chain_lazy : OmegaCompletePartialOrder.Chain (Unit → Program s Unit) :=
    ⟨fun n => F_lazy^[n] ⊥, Monotone.monotone_iterate_of_le_map F_lazy.monotone (OrderBot.bot_le _)⟩
  let chain_eager : OmegaCompletePartialOrder.Chain (Unit → Program s Unit) :=
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
theorem transferL_while_loop {l : Type} {c : Program (ProcedureState l) Bool}
    {body_lazy body_eager : Program (ProcedureState l) Unit}
    (hc : Stable c) (hbody : transferBy convertL body_lazy body_eager) :
    transferBy convertL (while_loop c body_lazy) (while_loop c body_eager) := by
  refine transferBy_while_loop convertL (cond := c) ?_ ?_
  · -- condition commutes with convertL, from `Stable c`
    intro β k
    have hc' : (c >>= fun a => convertL >>= fun _ => (pure a : Program (ProcedureState l) Bool))
             = (convertL >>= fun _ => c) := hc
    have h_pair : (c >>= fun b => convertL >>= fun _ => (pure (b, ()) : Program (ProcedureState l) (Bool × Unit)))
                = (convertL >>= fun _ => c >>= fun b => pure (b, ())) := by
      have := congrArg (fun m => m >>= fun b =>
        (pure (b, ()) : Program (ProcedureState l) (Bool × Unit))) hc'
      simpa only [Program.bind_assoc, Program.pure_bind] using this
    have hL : (c >>= fun b => convertL >>= fun _ => k b)
            = (c >>= fun b => convertL >>= fun _ =>
                (pure (b, ()) : Program (ProcedureState l) (Bool × Unit))) >>= fun bu => k bu.1 := by
      simp_rw [Program.bind_assoc]; congr 1; funext b; congr 1; funext u; rw [Program.pure_bind]
    have hR : (convertL >>= fun _ => c >>= k)
            = (convertL >>= fun _ => c >>= fun b =>
                (pure (b, ()) : Program (ProcedureState l) (Bool × Unit))) >>= fun bu => k bu.1 := by
      simp_rw [Program.bind_assoc]; congr 1; funext u; congr 1; funext b; rw [Program.pure_bind]
    rw [hL, hR, h_pair]
  · -- body bind-form, from `hbody`
    calc (body_lazy >>= fun _ : Unit => convertL)
        = (body_lazy >>= fun u : Unit =>
              convertL >>= fun _ : Unit => (Pure.pure u : Program (ProcedureState l) Unit)) := by
          congr 1; funext u
          show convertL = convertL >>= fun _ : Unit => Pure.pure u
          rw [show (Pure.pure u : Program (ProcedureState l) Unit)
                = (Pure.pure () : Program (ProcedureState l) Unit) from rfl]
          exact (Program.bind_pure _).symm
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
          Stable (Program.get p) → (∀ ret, Stable (Program.set x ret)) →
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

/-- The denotation of a procedure call, with the called procedure kept intact
    (`programDenotation` reconstructs `⟨proc.locals, proc.body, proc.return_val⟩`,
    which is `proc` by structure-eta). -/
theorem denote_call {l : Type} {sig : ProcedureSignature}
    (x : Setter sig.ret (ProcedureState l)) (proc : Procedure sig)
    (p : Getter sig.ParamType (ProcedureState l)) :
    programDenotation (StmtWithHoles.call x proc p)
      = (Program.get p >>= fun args =>
          Program.zoom ProcedureState.globalL (procedureDenotation proc args)
            >>= fun ret => Program.set x ret) := by
  simp only [StmtWithHoles.call, programDenotation]; rfl

/-- **Discharge of the oracle hypothesis for RO**: the lazy and eager oracle
    calls transfer, given the surrounding read/write are stable.  This is the
    concrete `hhole` for `body_transfer_gen` with `RO_lazy`/`RO_eager`: the
    query itself transfers by `Program.transfer_lazy_query` (lifted via
    `transferBy_zoom`), and the bridges identify the procedures with the
    semantic queries. -/
theorem ro_hhole {l : Type} {sig : ProcedureSignature} (n : HoleIndex roHoles sig)
    (x : Setter sig.ret (ProcedureState l)) (p : Getter sig.ParamType (ProcedureState l))
    (hp : Stable (Program.get p)) (hx : ∀ ret, Stable (Program.set x ret)) :
    transferBy convertL (programDenotation (StmtWithHoles.call x (RO_lazy n) p))
      (programDenotation (StmtWithHoles.call x (RO_eager n) p)) := by
  cases n with
  | zero =>
      show transferBy convertL (programDenotation (StmtWithHoles.call x RO_lazy_proc p))
          (programDenotation (StmtWithHoles.call x RO_eager_proc p))
      rw [denote_call, denote_call]
      refine transferBy_bind hp (fun args => transferBy_bind ?_ (fun ret => hx ret))
      rw [procDenotation_RO_lazy, procDenotation_RO_eager]
      exact transferBy_zoom ProcedureState.globalL (Program.transfer_lazy_query args)
  | succ m => nomatch m

/-- **Body-level RO transfer** — fully assembled (only `transferL_while_loop`
    remains, via `body_transfer_gen`).  For any syntactic adversary body `A`
    that is `Loc`al (touches the RO table only through the oracle hole), the
    lazy and eager instantiations transfer at the `ProcedureState` level. -/
theorem transfer_instantiate_body {l : Type} (A : StmtWithHoles roHoles l) (hloc : Loc A) :
    transferBy convertL (programDenotation (A.instantiate RO_lazy))
      (programDenotation (A.instantiate RO_eager)) :=
  body_transfer_gen A RO_lazy RO_eager hloc (fun n x p hp hx => ro_hhole n x p hp hx)

/-! ## The two subtask-3 theorems

Here `A : ProcedureWithHoles roHoles sig` is an adversary procedure carrying the
single oracle hole.  `A.instantiate RO_lazy` / `A.instantiate RO_eager` fill that
hole, and `procedureDenotation _ args : Program state sig.ret` runs the result on
the RO global `state`. -/

/-- The procedure denotation as an explicit wrapper: initialise locals, run the
    body, extract `(return_val, global)`. -/
noncomputable def procWrap {sig : ProcedureSignature} {L : Type}
    (rv : Getter sig.ret (ProcedureState L)) (initL : L)
    (B : Program (ProcedureState L) Unit) : Program state sig.ret :=
  fun st => B ⟨st, initL⟩ >>= fun p => pure (rv.get p.2, p.2.global)

/-- `procedureDenotation` of an instantiated procedure is `procWrap` of its body. -/
theorem procedureDenotation_eq_procWrap {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType) (inst : roHoles.Instantiation) :
    procedureDenotation (A.instantiate inst) args
      = procWrap A.return_val (sig.localVariableInit A.locals args)
          (programDenotation (A.body.instantiate inst)) := by
  funext st; simp only [procedureDenotation, ProcedureWithHoles.instantiate, procWrap]; rfl

/-- **`convertL` slides in**: `convert` before the wrapper = `convertL` before the
    body, inside the wrapper.  Structural (no return-value hypothesis). -/
theorem procWrap_convertL_in {sig : ProcedureSignature} {L : Type}
    (rv : Getter sig.ret (ProcedureState L)) (initL : L) (B : Program (ProcedureState L) Unit) :
    procWrap rv initL (convertL >>= fun _ => B) = (convert >>= fun _ => procWrap rv initL B) := by
  funext st
  simp only [procWrap, convertL, Program.zoom, bind, StateT.bind, pure, StateT.pure,
    ProcedureState.globalL]
  generalize convert st = U
  obtain ⟨mu, hmu⟩ := U
  simp only [MeasureTheory.Measure.bind_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, MeasureTheory.Measure.dirac_bind measurable_from_top]
  rfl

/-- `Program.get rv` reads `rv` and threads the state through unchanged. -/
theorem programGet_eq {sig : ProcedureSignature} {L : Type} (rv : Getter sig.ret (ProcedureState L)) :
    (Program.get rv : Program (ProcedureState L) sig.ret) = fun ps => pure (rv.get ps, ps) := by
  funext ps
  simp only [Program.get, StateT.get, AsGetter.toG, bind, StateT.bind, pure, StateT.pure,
    id_eq, SubProbability.pure_bind, MeasureTheory.Measure.dirac_bind measurable_from_top]

/-- From `hret`: reading `rv` commutes with `convertL` (clean `convertL`-form). -/
theorem rv_convertL_stable {sig : ProcedureSignature} {L : Type}
    (rv : Getter sig.ret (ProcedureState L)) (hret : Stable (Program.get rv)) (ps : ProcedureState L) :
    (convertL ps >>= fun q => pure (rv.get ps, q.2)) = (convertL ps >>= fun q => pure (rv.get q.2, q.2)) := by
  have h := congrFun hret ps
  simp only [Stable, transferBy, programGet_eq, bind, StateT.bind, pure, StateT.pure,
    SubProbability.pure_bind, MeasureTheory.Measure.dirac_bind measurable_from_top] at h
  exact h

/-- `key`: reading `rv` is invariant under `convert` changing the table (the global
    component of `rv_convertL_stable`). -/
theorem rv_convert_invariant {sig : ProcedureSignature} {L : Type}
    (rv : Getter sig.ret (ProcedureState L)) (hret : Stable (Program.get rv)) (ps : ProcedureState L) :
    (convert ps.global >>= fun w => pure (rv.get ps, w.2))
      = (convert ps.global >>= fun w => pure (rv.get ⟨w.2, ps.locals⟩, w.2)) := by
  have hc := rv_convertL_stable rv hret ps
  have hp := congrArg (fun (m : SubProbability (sig.ret × ProcedureState L)) =>
      m >>= fun p => (pure (p.1, p.2.global) : SubProbability (sig.ret × state))) hc
  simp only [convertL, Program.zoom, ProcedureState.globalL, bind, StateT.bind, pure, StateT.pure,
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
    (rv : Getter sig.ret (ProcedureState L)) (initL : L) (B : Program (ProcedureState L) Unit)
    (hret : Stable (Program.get rv)) :
    (procWrap rv initL B >>= fun r => convert >>= fun _ => pure r)
      = procWrap rv initL (B >>= fun a => convertL >>= fun _ => pure a) := by
  funext st
  simp only [procWrap, convertL, Program.zoom, ProcedureState.globalL, bind, StateT.bind,
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
    state-level `Program.transfer` of the whole procedure denotation, provided
    the return value is RO-disjoint.  Assembled from `procedureDenotation_eq_procWrap`,
    `procWrap_convert_out` (uses `hret`), `hbody`, and `procWrap_convertL_in`. -/
theorem transfer_wrapper {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hbody : transferBy convertL (programDenotation (A.body.instantiate RO_lazy))
              (programDenotation (A.body.instantiate RO_eager)))
    (hret : Stable (Program.get A.return_val)) :
    Program.transfer
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

/-- **`Program.transfer_instantiate`** (subtask 3, theorem 1).

If `A` touches the RO table only through the oracle hole (honest locality `Loc`
on its body; `fv_proc` is unusable while its leaves are `sorry`), then the lazy
and eager instantiations are related by `Program.transfer` — `convert` slides
across `A`, turning every lazy query into an eager one.  (Direction `lazy ↦
eager` matches the definition of `Program.transfer`; CLAUDE.md writes the pair in
the opposite order.)  Reduces to `transfer_instantiate_body` (proven modulo
`transferL_while_loop`) via `transfer_wrapper`. -/
theorem Program.transfer_instantiate {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hloc : Loc A.body) (hret : Stable (Program.get A.return_val)) :
    Program.transfer
      (procedureDenotation (A.instantiate RO_lazy) args)
      (procedureDenotation (A.instantiate RO_eager) args) :=
  transfer_wrapper A args (transfer_instantiate_body A.body hloc) hret

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

/-- **Locals are disjoint from the RO table.**  `localL.range ≤ (roLift l).compl.range`:
    the RO table lives inside `global`, the adversary's locals are elsewhere. -/
theorem localL_range_le_ro_compl {l : Type} :
    (ProcedureState.localL : Lens l (ProcedureState l)).range ≤ (roLift l).compl.range := by
  refine le_trans
    (Lens.range_le_compl_of_disjoint ProcedureState.localL ProcedureState.globalL) ?_
  rw [TotLensRange.complement_range, TotLensRange.complement_range]
  exact Submonoid.centralizer_le
    (Lens.chain_range_le ProcedureState.globalL random_oracle_state)

/-- **Theorem-1 leaf discharge, general lens form.**  A program confined to *any*
    adversary lens `L_adv` whose range is disjoint from the RO table (the sound,
    faithful "footprint disjoint from `oracle_state`" hypothesis — the lens-range
    analogue of the unsound `fv_proc ≤ (random_oracle_state.range)ᶜ`) is `Stable`.
    This is precisely `commute_of_disjoint_lens` specialised to `convertL`. -/
theorem stable_of_confined_lens {l α advSt : Type} [Countable α] [Countable l]
    (L_adv : Lens advSt (ProcedureState l)) (hdisj : L_adv.range ≤ ((roLift l).range)ᶜ)
    {p : Program (ProcedureState l) α} (hp : p.inRange L_adv.range) : Stable p :=
  stable_of_inRange_compl
    (Program.inRange_mono hp (hdisj.trans (le_of_eq (TotLensRange.complement_range _).symm)))

/-- The locals are one such lens (disjoint from the RO) — the canonical instance. -/
theorem stable_of_inRange_local {l α : Type} [Countable α] [Countable l]
    {p : Program (ProcedureState l) α}
    (hp : p.inRange (ProcedureState.localL : Lens l (ProcedureState l)).range) : Stable p :=
  stable_of_inRange_compl (Program.inRange_mono hp localL_range_le_ro_compl)

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

/-- **Theorem-2 leaf discharge, general lens form.**  A program confined to an
    adversary lens `L_adv` (compatible with `liftRel P` via `heq`/`hset`)
    self-couples under `liftRel P`, for *any* invariant `P`. -/
theorem prhl2_of_inRange_lens {l γ advSt : Type} [Nonempty (ProcedureState l)]
    {P : state → state → Prop}
    (L_adv : Lens advSt (ProcedureState l))
    (heq : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → L_adv.get ps₁ = L_adv.get ps₂)
    (hset : ∀ (c : advSt) ps₁ ps₂, liftRel P ps₁ ps₂ →
        liftRel P (L_adv.set c ps₁) (L_adv.set c ps₂))
    {p : Program (ProcedureState l) γ} (hp : p.inRange L_adv.range) :
    Program.prhl2 (liftRel P) p p (liftRelPost P) := by
  rw [Lens.factor_of_inRange L_adv hp]
  exact prhl2_lift_lens L_adv heq hset (L_adv.factor p)

/-- **Confinement to the adversary's private local state** — the faithful,
    checkable locality: every operation *outside the oracle interface* is
    confined to `ProcedureState.localL`.  Structurally identical to `Loc`/`LocP`,
    but with one uniform leaf condition (`.inRange localL.range`) that discharges
    *both*. -/
def Confined {holes : HoleSigs} {l advSt : Type} (L_adv : Lens advSt (ProcedureState l)) :
    StmtWithHoles holes l → Prop
  | .skip => True
  | .sample x e =>
      (programDenotation (StmtWithHoles.sample x e : Stmt l)).inRange L_adv.range
  | .call' x ls b r p =>
      (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l)).inRange L_adv.range
  | .hole _ x p => (Program.get p).inRange L_adv.range ∧
      (∀ ret, (Program.set x ret).inRange L_adv.range)
  | .seq s1 s2 => Confined L_adv s1 ∧ Confined L_adv s2
  | .ifThenElse c t e =>
      (Program.get c).inRange L_adv.range ∧ Confined L_adv t ∧ Confined L_adv e
  | .while c t => (Program.get c).inRange L_adv.range ∧ Confined L_adv t

/-- The single `roHoles` hole has signature `roSig`, whose query type is
    `Countable`.  (`HoleIndex roHoles sig` forces `sig = roSig`.) -/
private theorem roHole_paramType_countable {sig : ProcedureSignature}
    (n : HoleIndex roHoles sig) : Countable sig.ParamType := by
  cases n with
  | zero => exact inferInstanceAs (Countable input)
  | succ i => exact nomatch i

/-- **Confinement discharges `Loc`** (theorem-1 locality), leaf by leaf.  The
    hole's query type is `Countable` via `hc`. -/
theorem confined_loc {holes : HoleSigs} {l advSt : Type} [Countable l]
    (L_adv : Lens advSt (ProcedureState l)) (hdisj : L_adv.range ≤ ((roLift l).range)ᶜ)
    (hc : ∀ {sig : ProcedureSignature}, HoleIndex holes sig → Countable sig.ParamType) :
    ∀ (A : StmtWithHoles holes l), Confined L_adv A → Loc A
  | .skip, _ => trivial
  | .sample _ _, h => stable_of_confined_lens L_adv hdisj h
  | .call' _ _ _ _ _, h => stable_of_confined_lens L_adv hdisj h
  | .hole n _ _, h =>
      haveI := hc n
      ⟨stable_of_confined_lens L_adv hdisj h.1,
        fun ret => stable_of_confined_lens L_adv hdisj (h.2 ret)⟩
  | .seq s1 s2, h => ⟨confined_loc L_adv hdisj hc s1 h.1, confined_loc L_adv hdisj hc s2 h.2⟩
  | .ifThenElse _ t e, h =>
      ⟨stable_of_confined_lens L_adv hdisj h.1, confined_loc L_adv hdisj hc t h.2.1,
        confined_loc L_adv hdisj hc e h.2.2⟩
  | .«while» _ t, h =>
      ⟨stable_of_confined_lens L_adv hdisj h.1, confined_loc L_adv hdisj hc t h.2⟩

/-- **Confinement discharges `LocP`** (theorem-2 locality) for *any* invariant
    `P` — provided the adversary lens `L_adv` is `liftRel P`-compatible
    (`heq`/`hset`).  No `h'`-style preservation condition on the adversary's ops:
    `heq`/`hset` are conditions on the *region* `L_adv` vs `P`, not on `A`. -/
theorem confined_locP {holes : HoleSigs} {l advSt : Type} [Nonempty (ProcedureState l)]
    {P : state → state → Prop}
    (L_adv : Lens advSt (ProcedureState l))
    (heq : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → L_adv.get ps₁ = L_adv.get ps₂)
    (hset : ∀ (c : advSt) ps₁ ps₂, liftRel P ps₁ ps₂ →
        liftRel P (L_adv.set c ps₁) (L_adv.set c ps₂))
    (hc : ∀ {sig : ProcedureSignature}, HoleIndex holes sig → Countable sig.ParamType) :
    ∀ (A : StmtWithHoles holes l), Confined L_adv A → LocP P A
  | .skip, _ => trivial
  | .sample _ _, h => prhl2_of_inRange_lens L_adv heq hset h
  | .call' _ _ _ _ _, h => prhl2_of_inRange_lens L_adv heq hset h
  | .hole n _ _, h =>
      haveI := hc n
      ⟨prhl2_of_inRange_lens L_adv heq hset h.1,
        fun ret => prhl2_of_inRange_lens L_adv heq hset (h.2 ret)⟩
  | .seq s1 s2, h => ⟨confined_locP L_adv heq hset hc s1 h.1, confined_locP L_adv heq hset hc s2 h.2⟩
  | .ifThenElse _ t e, h =>
      ⟨prhl2_of_inRange_lens L_adv heq hset h.1, confined_locP L_adv heq hset hc t h.2.1,
        confined_locP L_adv heq hset hc e h.2.2⟩
  | .«while» _ t, h =>
      ⟨prhl2_of_inRange_lens L_adv heq hset h.1, confined_locP L_adv heq hset hc t h.2⟩

/-- **Theorem 1, faithful form.**  An adversary confined to *any* lens `L_adv`
    whose range is disjoint from the oracle (`L_adv.range ≤ (roLift _).rangeᶜ` —
    the sound, lens-range rendering of "`fv(A)` disjoint from `oracle_state`")
    cannot distinguish lazy from eager. -/
theorem Program.transfer_instantiate_confined {sig : ProcedureSignature} {advSt : Type}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (L_adv : Lens advSt (ProcedureState (sig.LocalVariableState A.locals)))
    (hdisj : L_adv.range ≤ ((roLift (sig.LocalVariableState A.locals)).range)ᶜ)
    [Countable (sig.LocalVariableState A.locals)] [Countable sig.ret]
    (hconf : Confined L_adv A.body)
    (hret : (Program.get A.return_val).inRange L_adv.range) :
    Program.transfer
      (procedureDenotation (A.instantiate RO_lazy) args)
      (procedureDenotation (A.instantiate RO_eager) args) :=
  Program.transfer_instantiate A args
    (confined_loc L_adv hdisj roHole_paramType_countable A.body hconf)
    (stable_of_confined_lens L_adv hdisj hret)

/-- **Theorem 2, faithful form (general adversary lens).**  An adversary confined
    to *any* lens `L_adv` that is compatible with `liftRel P` (`heq`: `liftRel`
    forces equality on `L_adv`; `hset`: writing `L_adv` preserves `liftRel`) gives
    the relational (coupling) equivalence for that invariant `P`.  `L_adv` may
    include **shared non-RO global variables** wherever `P` already forces them
    equal — not just the locals.  No `h'`-style condition on the adversary's ops. -/
theorem prhl_instantiate_confined {sig : ProcedureSignature} {advSt : Type}
    {P : state → state → Prop}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (L_adv : Lens advSt (ProcedureState (sig.LocalVariableState A.locals)))
    (heq : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → L_adv.get ps₁ = L_adv.get ps₂)
    (hset : ∀ (c : advSt) ps₁ ps₂, liftRel P ps₁ ps₂ →
        liftRel P (L_adv.set c ps₁) (L_adv.set c ps₂))
    [Nonempty (ProcedureState (sig.LocalVariableState A.locals))]
    (h : ∀ inp : input,
        Program.prhl P (random_oracle_query inp) (lazy_query inp) (liftPost P))
    (hconf : Confined L_adv A.body)
    (hret : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → A.return_val.get ps₁ = A.return_val.get ps₂) :
    Program.prhl P
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (liftPost P) :=
  prhl_instantiate A args h
    (confined_locP L_adv heq hset roHole_paramType_countable A.body hconf) hret

/-- **Theorem 2, locals-only instance.**  The canonical case `L_adv = localL`:
    `heq`/`hset` hold for free (`liftRel` pins the locals to equality), so the
    only confinement hypothesis is `Confined localL A.body`. -/
theorem prhl_instantiate_confined_local {sig : ProcedureSignature} {P : state → state → Prop}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    [Nonempty (ProcedureState (sig.LocalVariableState A.locals))]
    (h : ∀ inp : input,
        Program.prhl P (random_oracle_query inp) (lazy_query inp) (liftPost P))
    (hconf : Confined ProcedureState.localL A.body)
    (hret : ∀ ps₁ ps₂, liftRel P ps₁ ps₂ → A.return_val.get ps₁ = A.return_val.get ps₂) :
    Program.prhl P
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (liftPost P) :=
  prhl_instantiate_confined A args ProcedureState.localL
    (fun _ _ hpre => hpre.2) (fun _ _ _ hpre => ⟨hpre.1, rfl⟩) h hconf hret

/-- **Worked corollary: theorem 2 with a shared non-RO *global* variable.**
    The adversary may read/write a global variable `gv` (not just its locals),
    as long as the invariant keeps `gv` equal across the two runs and the oracle
    invariant `Pro` survives `gv`-writes (`hPro` — automatic when `gv` is disjoint
    from the RO table, since then a `gv`-write leaves the RO table fixed).  The
    invariant used is `P g₁ g₂ := gv.get g₁ = gv.get g₂ ∧ Pro g₁ g₂` and the
    confinement region is `globalL.chain gv` (the `gv`-slice of the procedure
    state).  This shows `prhl_instantiate_confined` already covers non-RO globals
    — only the choice of `P` and `L_adv` differs from the locals-only case; no new
    machinery is needed.  (Pair `globalL.chain gv` with `localL` to use both.) -/
theorem prhl_instantiate_confined_global {sig : ProcedureSignature} {γ : Type}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (gv : Lens γ state) (Pro : state → state → Prop)
    (hPro : ∀ (c : γ) g₁ g₂, Pro g₁ g₂ → Pro (gv.set c g₁) (gv.set c g₂))
    [Nonempty (ProcedureState (sig.LocalVariableState A.locals))]
    (h : ∀ inp : input,
        Program.prhl (fun g₁ g₂ => gv.get g₁ = gv.get g₂ ∧ Pro g₁ g₂)
          (random_oracle_query inp) (lazy_query inp)
          (liftPost (fun g₁ g₂ => gv.get g₁ = gv.get g₂ ∧ Pro g₁ g₂)))
    (hconf : Confined (ProcedureState.globalL.chain gv) A.body)
    (hret : ∀ ps₁ ps₂,
        liftRel (fun g₁ g₂ => gv.get g₁ = gv.get g₂ ∧ Pro g₁ g₂) ps₁ ps₂ →
          A.return_val.get ps₁ = A.return_val.get ps₂) :
    Program.prhl (fun g₁ g₂ => gv.get g₁ = gv.get g₂ ∧ Pro g₁ g₂)
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (liftPost (fun g₁ g₂ => gv.get g₁ = gv.get g₂ ∧ Pro g₁ g₂)) :=
  prhl_instantiate_confined A args (ProcedureState.globalL.chain gv)
    (fun _ _ hpre => hpre.1.1)
    (fun c ps₁ ps₂ hpre => by
      refine ⟨⟨?_, hPro c ps₁.global ps₂.global hpre.1.2⟩, hpre.2⟩
      show gv.get (gv.set c ps₁.global) = gv.get (gv.set c ps₂.global)
      rw [gv.set_get, gv.set_get])
    h hconf hret

/-! ## INVESTIGATION (for tomorrow, with Dominique): `fv`-disjointness ⟹ `Confined`?

`fv_stmt A ≤ L_adv.range` is Dominique's `Program.range`-based footprint hypothesis
(the `fv_proc A ≤ (random_oracle_state.range)ᶜ` form, at the `ProcedureState`
level).  `confined_of_fv` below reduces it to `Confined`, **leaf by leaf**:

* the structural cases (`skip`/`sample`/`hole`/`if`/`while`/`seq`) are **proven**;
* the **setter** leaf bridge is the hypothesis `hset` — it is *provable* (writes:
  `Program.range' (Program.set x)` is achieved, so `fv_setter`-soundness holds);
* the **getter** leaf bridge is `get_confined_of_fv` — the **single open `sorry`**,
  the case to study.  (`call'` is a separate `sorry`: a nested procedure runs on
  the global state via `zoom globalL`, so it is not local — orthogonal to the
  get-read issue, and it leans on Dominique's still-`sorry` `fv_reduce`/`fv_extend`.)

So the whole conversion stands or falls on **`get_confined_of_fv`**. -/

/-- **The `get` bridge — THE OPEN CASE (`sorry`).**  Unfolding,
    `fv_getter c = Program.range (Program.get c)`, so this lemma is exactly

      `Program.range (Program.get c) ≤ R  →  (Program.get c).inRange R`,

    which (by monotonicity of `inRange`) is equivalent to **self-range for a read**,
    `(Program.get c).inRange (Program.range (Program.get c))`.  It is FALSE in
    general: a read's `Program.range` collapses (e.g. `Program.range (get fst) = ⊥`
    on `Bool × Bool`), so the premise is vacuous while the conclusion fails.  This
    is the precise obstruction to `fv_proc ≤ ROᶜ ⟹ Confined`. -/
theorem get_confined_of_fv {a l : Type} (c : Getter a (ProcedureState l))
    {R : TotLensRange (ProcedureState l)} (h : fv_getter c ≤ R) :
    (Program.get c).inRange R := by
  sorry

/-- The `fst`-preserving involution `(a,b) ↦ (a, a⊕b)` — a `fst`-preserving update
    that is *not* a pure complement update (it doesn't commute with `fst`-writes). -/
private def gcex : Function.End (Bool × Bool) := fun p => (p.1, xor p.1 p.2)

set_option maxRecDepth 100000 in
/-- **Concrete witness that read-`Program.range` collapses (PROVEN).**  On
    `Bool × Bool`, reading the first component has `Program.range = ⊥`, even though
    `get fst` obviously "uses" `fst`.  Reason: both `{id, gcex}` and `snd.range` are
    double-commutant-closed families of `fst`-preserving updates, so each is a valid
    `Rᶜ` with `(get fst).inRange R`; their meet is `⊥`, so the infimum defining
    `Program.range` is `⊥` and is *not achieved* (`(get fst).inRange ⊥` is false).
    This is exactly why `get_confined_of_fv` (self-range for reads) fails: the two
    finite facts are dispatched by `decide` over the 4-element state. -/
theorem range_get_fst_eq_bot :
    Program.range (Program.get (Lens.fst : Lens Bool (Bool × Bool))) = ⊥ := by
  classical
  letI : Fintype (Function.End (Bool × Bool)) :=
    inferInstanceAs (Fintype (Bool × Bool → Bool × Bool))
  letI : DecidableEq (Function.End (Bool × Bool)) :=
    inferInstanceAs (DecidableEq (Bool × Bool → Bool × Bool))
  -- two finite facts, by `decide`:
  have dec1 : ∀ f : Function.End (Bool × Bool),
      (∀ a : Function.End (Bool × Bool), gcex * a = a * gcex → a * f = f * a) →
      ∀ σ : Bool × Bool, (f σ).1 = σ.1 := by decide
  have dec2 : ∀ w : Bool → Bool,
      gcex * (Lens.fst.update w) = (Lens.fst.update w) * gcex → w = id := by decide
  -- (1) `get fst` lives in `(from {gcex})ᶜ` (every map in its complement preserves `fst`).
  have hR₁ : (Program.get (Lens.fst : Lens Bool (Bool × Bool))).inRange
      ((TotLensRange.from ({gcex} : Set (Function.End (Bool × Bool))))ᶜ) := by
    intro f hf
    rw [TotLensRange.compl_compl] at hf
    have hpres : ∀ σ, (f σ).1 = σ.1 := by
      apply dec1
      intro a hga
      have ha : a ∈ Submonoid.centralizer ({gcex} : Set (Function.End (Bool × Bool))) :=
        Submonoid.mem_centralizer_iff.mpr (fun c hc => by
          rw [Set.mem_singleton_iff] at hc; subst hc; exact hga)
      exact Submonoid.mem_centralizer_iff.mp hf a ha
    apply Program.ext_of_wp; intro F; funext σ
    simp only [wp_bind, wp_liftF, wp_get, wp_pure]
    show F ((f σ).1, f σ) = F (σ.1, f σ)
    rw [hpres σ]
  -- (2) `(from {gcex})ᶜ ⊓ fst.range = ⊥`: the only `fst`-update commuting with `gcex` is `id`.
  have hmeet : (TotLensRange.from ({gcex} : Set (Function.End (Bool × Bool))))ᶜ ⊓ Lens.fst.range
      ≤ (⊥ : TotLensRange (Bool × Bool)) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ :
        u ∈ ((TotLensRange.from ({gcex} : Set (Function.End (Bool × Bool))))ᶜ).updates
          ∧ u ∈ Lens.fst.range.updates := hu
    obtain ⟨w, -, hw⟩ :
        ∃ w, w ∈ (⊤ : Set (Bool → Bool)) ∧ Lens.fst.update w = u := hu2
    have hgu : gcex * u = u * gcex := by
      have hg_mem : gcex ∈ Submonoid.centralizer
          ((Submonoid.centralizer ({gcex} : Set (Function.End (Bool × Bool)))).carrier) :=
        Submonoid.mem_centralizer_iff.mpr (fun b hb =>
          (Submonoid.mem_centralizer_iff.mp hb gcex (Set.mem_singleton gcex)).symm)
      exact Submonoid.mem_centralizer_iff.mp hu1 gcex hg_mem
    have hwid : w = id := dec2 w (by rw [hw]; exact hgu)
    rw [← hw, hwid]
    exact (⊥ : TotLensRange (Bool × Bool)).id
  exact le_antisymm
    ((le_inf (sInf_le hR₁) (sInf_le (Program.inRange_get _))).trans hmeet) bot_le

/-! ### The leaf bridges over `ProbLensRange` — the obstruction removed

The `TotLensRange` conversion "stands or falls on `get_confined_of_fv`" (the `sorry` above), which
is *self-range for a read* — and that is **false** (`range_get_fst_eq_bot`: read-`Program.range`
collapses to `⊥`).  Over `ProbLensRange`, **self-range holds for every program** (it is the litmus
`inProbRange_of_probRange_le` at `R := p.probRange`), so the `get`, `set`, *and* `call'` bridges all
discharge uniformly — no `sorry`, and no `hset`-style hypothesis.  This is the precise payoff of
moving the range theory to sub-probability kernels. -/

/-- **Self-range over `ProbLensRange` (PROVEN).**  For any program with countable return,
    `p.inProbRange p.probRange`.  This is *exactly* the statement that is FALSE for `TotLensRange`
    (witness: `range_get_fst_eq_bot`), whose failure forced `get_confined_of_fv`/`call'` to be
    `sorry`.  Every leaf bridge below is a corollary. -/
theorem inProbRange_selfRange {a s : Type} (p : Program s a) :
    p.inProbRange p.probRange :=
  Program.inProbRange_of_probRange_le (le_refl _)

/-- **The `get` bridge over `ProbLensRange` — PROVEN (the litmus).**  The probabilistic counterpart
    of `get_confined_of_fv` (the open `sorry`): where the `TotLensRange` bridge is self-range for a
    read (false), this is the litmus, which holds for any read with countable result. -/
theorem get_confinedP_of_fv {a l : Type} (c : Getter a (ProcedureState l))
    {R : ProbLensRange (ProcedureState l)} (h : (Program.get c).probRange ≤ R) :
    (Program.get c).inProbRange R :=
  Program.inProbRange_of_probRange_le h

/-- **The setter bridge over `ProbLensRange` — PROVEN (the litmus).**  In `confined_of_fv` the
    setter bridge had to be *assumed* (`hset`); here it is the litmus, for free. -/
theorem set_confinedP_of_fv {a l : Type} (y : Setter a (ProcedureState l)) (w : a)
    {R : ProbLensRange (ProcedureState l)} (h : (Program.set y w).probRange ≤ R) :
    (Program.set y w).inProbRange R :=
  Program.inProbRange_of_probRange_le h

/-- **The probabilistic footprint of a statement.**  The `ProbLensRange` analogue of `fv_stmt`,
    defined *directly* as the join of each leaf's own `probRange` — no `fv_reduce`/`fv_extend`
    machinery is needed, because self-range makes every program its own footprint.  In particular
    the nested `call'` leaf is just `(programDenotation (call' …)).probRange`. -/
noncomputable def fvP_stmt {holes : HoleSigs} {l : Type} :
    StmtWithHoles holes l → ProbLensRange (ProcedureState l)
  | .skip => ⊥
  | .sample x e => (programDenotation (StmtWithHoles.sample x e : Stmt l)).probRange
  | .call' x ls b r p => (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l)).probRange
  | .hole _ x p => (Program.get p).probRange ⊔ (⨆ ret, (Program.set x ret).probRange)
  | .seq s1 s2 => fvP_stmt s1 ⊔ fvP_stmt s2
  | .ifThenElse c t e => (Program.get c).probRange ⊔ fvP_stmt t ⊔ fvP_stmt e
  | .while c t => (Program.get c).probRange ⊔ fvP_stmt t

/-- **`fv`-disjointness ⟹ `Confined`, modulo the `get` bridge.**  Structural
    reduction: every leaf is discharged by `get_confined_of_fv` (the `sorry`),
    the (provable) setter bridge `hset`, and `inRange_toProgram`/`inRange_bind`.
    `call'` is the one orthogonal `sorry` (nested procedure). -/
theorem confined_of_fv {holes : HoleSigs} {l advSt : Type}
    (L_adv : Lens advSt (ProcedureState l))
    (hset : ∀ {b : Type} (y : Setter b (ProcedureState l)) (w : b),
        fv_setter y ≤ L_adv.range → (Program.set y w).inRange L_adv.range) :
    ∀ (A : StmtWithHoles holes l), fv_stmt A ≤ L_adv.range → Confined L_adv A
  | .skip, _ => trivial
  | .sample x e, h => by
      have hx : fv_setter x ≤ L_adv.range := le_sup_left.trans h
      have he : fv_getter e ≤ L_adv.range := le_sup_right.trans h
      show (programDenotation (StmtWithHoles.sample x e : Stmt l)).inRange L_adv.range
      simp only [programDenotation]
      exact Program.inRange_bind (get_confined_of_fv e he)
        (fun μ => Program.inRange_bind (Program.inRange_toProgram μ _)
          (fun v => hset x v hx))
  | .call' x ls b r p, _ => by
      -- nested procedure: `programDenotation (call' …)` runs the sub-procedure on
      -- the global state (`zoom globalL`), so it is not confined to `L_adv` in
      -- general.  Orthogonal to the get-read issue; depends on `fv_reduce`/`fv_extend`.
      sorry
  | .hole _ x p, h =>
      ⟨get_confined_of_fv p (le_sup_right.trans h), fun ret => hset x ret (le_sup_left.trans h)⟩
  | .seq s1 s2, h =>
      ⟨confined_of_fv L_adv hset s1 (le_sup_left.trans h),
        confined_of_fv L_adv hset s2 (le_sup_right.trans h)⟩
  | .ifThenElse c t e, h =>
      ⟨get_confined_of_fv c (le_sup_left.trans h),
        confined_of_fv L_adv hset t (le_sup_left.trans (le_sup_right.trans h)),
        confined_of_fv L_adv hset e (le_sup_right.trans (le_sup_right.trans h))⟩
  | .«while» c t, h =>
      ⟨get_confined_of_fv c (le_sup_left.trans h), confined_of_fv L_adv hset t (le_sup_right.trans h)⟩

/-- **Level translation `State` ↔ `ProcedureState` — MECHANICAL (`sorry`).**
    `fv_proc` lives over `State`; `fv_stmt` over `ProcedureState`.  Concretely
    `fv_proc A = fv_reduce globalL (fv_stmt A.body) ⊔ fv_reduce globalL (fv_getter A.return_val)`,
    where `fv_reduce globalL` pulls the body's footprint back to `State` along the
    global lens (projecting the locals out).  This lemma is the corresponding
    pullback fact: the body's *global* footprint avoiding the RO table lifts to
    the *full* footprint avoiding it.  It is the `fv_reduce`/`fv_extend` adjunction
    through `globalL` — Dominique's machinery (whose supporting lemmas
    `fv_reduce_sup`/`fv_extend_sup`/`fv_reduce_extend` are themselves still `sorry`
    in `FV.lean`).  Orthogonal to the read issue; left as a labeled `sorry`. -/
theorem fv_stmt_le_compl_of_reduce {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig)
    (h : fv_reduce ProcedureState.globalL (fv_stmt A.body) ≤ (random_oracle_state.range)ᶜ) :
    fv_stmt A.body ≤ (roLift (sig.LocalVariableState A.locals)).compl.range := by
  sorry

/-- **EXACTLY the requested implication.**  `fv_proc A ≤ (random_oracle_state.range)ᶜ`
    ⟹ the adversary body is `Confined` to the RO-complement.  The proof is the
    structural reduction `confined_of_fv`, after the level translation
    `fv_stmt_le_compl_of_reduce`.  The single **conceptual** open obligation is
    `get_confined_of_fv` (the read self-range — the case to study).  `hset` is the
    *provable* setter bridge (writes: `range'(set y)` is achieved), supplied as a
    hypothesis to keep the focus on the read case; `call'` (inside `confined_of_fv`)
    and `fv_stmt_le_compl_of_reduce` are the labeled *mechanical* gaps. -/
theorem confined_of_fv_proc {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig)
    (hset : ∀ {b : Type}
        (y : Setter b (ProcedureState (sig.LocalVariableState A.locals))) (w : b),
        fv_setter y ≤ (roLift (sig.LocalVariableState A.locals)).compl.range →
          (Program.set y w).inRange (roLift (sig.LocalVariableState A.locals)).compl.range)
    (hfv : fv_proc A ≤ (random_oracle_state.range)ᶜ) :
    Confined (roLift (sig.LocalVariableState A.locals)).compl A.body :=
  confined_of_fv (roLift (sig.LocalVariableState A.locals)).compl hset A.body
    (fv_stmt_le_compl_of_reduce A (le_sup_left.trans hfv))

/-! ## ProbLensRange path: deriving `Confined` from disjointness

The `TotLensRange`-based `Confined`/`Loc` chain above could not derive its `get`-leaves from a
footprint/disjointness hypothesis (reads collapse under `Program.range`, so the litmus backward
direction fails). The probabilistic `inProbRange` does not have this defect: the litmus
`inProbRange_iff_probRange_le` makes `(get c).inProbRange R` follow from `(get c).probRange ≤ R`
for *opaque* getters. This section rebuilds the leaf bridge (`convertL_inProbRange`,
`stable_of_inProbRange_compl`) over `ProbLensRange`, reusing the existing `Loc`→theorems chain. -/

/-- `zoom` of a read is a read through the chained lens. -/
theorem zoom_get {s t c : Type} (L : Lens s t) (v : Lens c s) :
    Program.zoom L (Program.get v) = Program.get (L.chain v) := by
  funext tv
  show (Program.get v (L.get tv)) >>= (fun as => (pure (as.1, L.set as.2 tv) : SubProbability (c × t)))
     = Program.get (L.chain v) tv
  rw [Program.get_apply, SubProbability.pure_bind, Program.get_apply, L.get_set]; rfl

/-- `zoom` of a write is a write through the chained lens. -/
theorem zoom_set {s t c : Type} (L : Lens s t) (v : Lens c s) (Z : c) :
    Program.zoom L (Program.set v Z) = Program.set (L.chain v) Z := by
  funext tv
  show (Program.set v Z (L.get tv)) >>= (fun as => (pure (as.1, L.set as.2 tv) : SubProbability (Unit × t)))
     = Program.set (L.chain v) Z tv
  rw [Program.set_apply, SubProbability.pure_bind, Program.set_apply]; rfl

/-- `zoom` of a state-free sample is that sample (it touches no state). -/
theorem zoom_uniform {s t α : Type} [Fintype α] [Nonempty α] (L : Lens s t) :
    Program.zoom L (Program.uniform : Program s α) = (Program.uniform : Program t α) := by
  funext tv
  show ((SubProbability.uniform : SubProbability α) >>= fun a => (pure (a, L.get tv) : SubProbability (α × s)))
        >>= (fun as => (pure (as.1, L.set as.2 tv) : SubProbability (α × t)))
     = (SubProbability.uniform : SubProbability α) >>= fun a => (pure (a, tv) : SubProbability (α × t))
  rw [SubProbability.bind_assoc]
  congr 1; funext a
  rw [SubProbability.pure_bind, L.get_set]

-- `convert_inProbRange_ro` now lives in `GaudisCrypt.Lib.RO.Transfer` (imported transitively),
-- next to `convert` and the transfer-reflexivity it drives.

/-! ### Lift framework for `inProbRange` (toward `convertL_inProbRange`)

`convertL = globalL.lift convert` (`zoom = lift`), so `convertL_inProbRange` will be
`lift_inProbRange_chain globalL random_oracle_state convert convert_inProbRange_ro`. The lift
lemmas apply via the elaborator (handling the `state`/`State` defeq), unlike the `zoom`-rewrite
route. `Lens.lift`/`Lens.factor`/`lift_lift_chain` are the (range-independent) constructs from
`ProgramRange`. -/

-- `inProbRange_subprob` now lives in `GaudisCrypt.ProbLensRange` (imported), next to the other
-- `inProbRange` primitives, so the wp-layer (`ProgramRange`) can reuse it.

/-- **Factorization**: a program confined to `L`'s probabilistic range comes from running some
    inner program on the `L`-content. The `inProbRange` analogue of `Lens.factor_of_inRange`. -/
theorem factor_of_inProbRange {c s a : Type} [Nonempty s] (L : Lens c s) {Adv : Program s a}
    (h : Adv.inProbRange L.probRange) : Adv = L.lift (L.factor Adv) := by
  funext σ
  set f : s → s := fun σ' => L.set (L.get σ') σ with hf_def
  have h_fσ_pad : f (L.set (L.get σ) (Classical.arbitrary s)) = σ := by
    show L.set (L.get (L.set (L.get σ) (Classical.arbitrary s))) σ = σ
    rw [L.set_get, L.get_set]
  have h_f_mem : diracKer f ∈ ((L.probRange)ᶜ).updates := by
    refine Submonoid.mem_centralizer_iff.mpr ?_
    intro k hk
    have hfgen : diracKer f ∈
        Submonoid.centralizer (Set.range fun g : Function.End c => diracKer (L.update g)) := by
      refine Submonoid.mem_centralizer_iff.mpr ?_
      rintro _ ⟨g, rfl⟩
      rw [diracKer_mul, diracKer_mul]; congr 1
      show L.update g ∘ f = f ∘ L.update g
      funext σ'
      show L.update g (f σ') = f (L.update g σ')
      simp only [Lens.update, hf_def, L.set_get, L.set_set]
    exact (Submonoid.mem_centralizer_iff.mp hk (diracKer f) hfgen).symm
  have h_iv : Adv σ
      = (Adv (L.set (L.get σ) (Classical.arbitrary s)))
          >>= (fun xs : a × s => (pure (xs.1, f xs.2) : SubProbability (a × s))) := by
    conv_lhs => rw [← h_fσ_pad]
    exact inProbRange_subprob h h_f_mem _
  change Adv σ
      = ((Adv (L.set (L.get σ) (Classical.arbitrary s)))
            >>= fun xσ' : a × s => (pure (xσ'.1, L.get xσ'.2) : SubProbability (a × c)))
          >>= fun xc : a × c => (pure (xc.1, L.set xc.2 σ) : SubProbability (a × s))
  rw [h_iv, SubProbability.bind_assoc']
  congr 1; funext xσ'
  rw [SubProbability.pure_bind]

section
open Classical

/-- **An `M`-localized kernel lies in `M.probRange`.** A kernel that reads only `M.get`, samples a
    new `M`-value, and writes it back (`ρ (M.get st) >>= fun mc' => pure (M.set mc' st)`) commutes
    with the commutant `M.probRangeᶜ` — using that any such `f` preserves `M.get` a.s. and commutes
    with `M.set`, plus the Fubini swap `bind_swap` (countability-free since subtask 4). -/
theorem Mlocalized_in_probRange {c s : Type} (M : Lens c s) (ρ : c → SubProbability c) :
    (fun st => ρ (M.get st) >>= fun mc' => (pure (M.set mc' st) : SubProbability s))
      ∈ M.probRange.updates := by
  rw [ProbLensRange.updates_eq_centralizer_compl M.probRange]
  refine Submonoid.mem_centralizer_iff.mpr ?_
  intro f hf
  have hgen : ∀ g : Function.End c, diracKer (M.update g) ∈ M.probRange.updates :=
    fun g => (ProbLensRange.from_le_iff _ M.probRange).mp le_rfl ⟨g, rfl⟩
  have hset : ∀ (mc' : c) (st : s),
      (f st >>= fun st' => (pure (M.set mc' st') : SubProbability s)) = f (M.set mc' st) := by
    intro mc' st
    have h0 : (f st >>= fun st' => (pure (M.set mc' st') : SubProbability s))
            = (pure (M.set mc' st) : SubProbability s) >>= f :=
      congrFun (Submonoid.mem_centralizer_iff.mp hf (diracKer (M.update (Function.const c mc')))
        (hgen (Function.const c mc'))) st
    rwa [SubProbability.pure_bind] at h0
  have hpres : ∀ st, (f st >>= fun st' => (pure (M.set (M.get st) st') : SubProbability s)) = f st := by
    intro st; rw [hset (M.get st) st, M.get_set]
  funext st
  show (ρ (M.get st) >>= fun mc' => (pure (M.set mc' st) : SubProbability s)) >>= f
     = f st >>= fun st' => ρ (M.get st') >>= fun mc' => (pure (M.set mc' st') : SubProbability s)
  have hL : ((ρ (M.get st) >>= fun mc' => (pure (M.set mc' st) : SubProbability s)) >>= f)
      = f st >>= fun st' => ρ (M.get st) >>= fun mc' => (pure (M.set mc' st') : SubProbability s) := by
    rw [SubProbability.bind_assoc]
    rw [show (fun mc' => (pure (M.set mc' st) : SubProbability s) >>= f)
          = (fun mc' => f st >>= fun st' => (pure (M.set mc' st') : SubProbability s)) from by
        funext mc'; rw [SubProbability.pure_bind, hset mc' st]]
    exact (bind_swap (f st) (ρ (M.get st))
      (fun mc' st' => (pure (M.set mc' st') : SubProbability s))).symm
  have hR : (f st >>= fun st' => ρ (M.get st') >>= fun mc' => (pure (M.set mc' st') : SubProbability s))
      = f st >>= fun st' => ρ (M.get st) >>= fun mc' => (pure (M.set mc' st') : SubProbability s) := by
    conv_lhs => rw [← hpres st]
    rw [SubProbability.bind_assoc]
    congr 1; funext st''
    rw [SubProbability.pure_bind, M.set_get]
    congr 1; funext mc'
    rw [M.set_set]
  rw [hL, hR]

/-- **A lift lives in its lens's probabilistic range** — the `inProbRange` analogue of
    `Lens.lift_inRange_self`. The `y`-generator of `(M.lift Q).probRange` is the `M`-localized
    kernel for `Q` conditioned on returning `y`, so `Mlocalized_in_probRange` applies. -/
theorem lift_inProbRange_self {c s a : Type}
    (M : Lens c s) (Q : Program c a) : (M.lift Q).inProbRange M.probRange := by
  refine Program.inProbRange_of_probRange_le ?_
  refine (ProbLensRange.from_le_iff _ _).mpr ?_
  rintro k ⟨y, rfl⟩
  show (fun st => (M.lift Q) st >>= fun w : a × s => if w.1 = y then pure w.2 else ⊥)
       ∈ M.probRange.updates
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
  exact Mlocalized_in_probRange M (fun mc => Q mc >>= fun xc => if xc.1 = y then pure xc.2 else ⊥)

/-- **Lift confines the footprint through the chained lens** — `inProbRange` analogue of
    `Lens.lift_inRange_chain`. Factor `P` as `v.lift (v.factor P)`, fold the double lift into a
    single `(L.chain v)`-lift (`lift_lift_chain`), and confine via `lift_inProbRange_self`. -/
theorem lift_inProbRange_chain {c s d a : Type} [Nonempty c]
    (L : Lens c s) (v : Lens d c) (P : Program c a) (hP : P.inProbRange v.probRange) :
    (L.lift P).inProbRange (L.chain v).probRange := by
  rw [factor_of_inProbRange v hP, Lens.lift_lift_chain]
  exact lift_inProbRange_self (L.chain v) (v.factor P)

/-- **`convertL` is confined to the (lifted) RO table, as a probabilistic range.** Via the lift
    framework (avoiding the `zoom`-rewrite's `state`/`State` `rw` obstacle): `convertL = globalL.lift
    convert`, and `convert.inProbRange random_oracle_state.probRange` (`convert_inProbRange_ro`). -/
theorem convertL_inProbRange {l : Type} :
    (convertL : Program (ProcedureState l) Unit).inProbRange (roLift l).probRange :=
  lift_inProbRange_chain ProcedureState.globalL random_oracle_state convert convert_inProbRange_ro

/-- **`Stable` from probabilistic footprint disjointness.** A program confined (in the
    `inProbRange` sense) to the complement of the RO table commutes with `convertL`, i.e. is
    `Stable`. The `ProbLensRange` analogue of `stable_of_inRange_compl`; the `ᶜ`-form makes the
    `commute_of_disjoint_prob` disjointness hypothesis `le_refl`, so no `complement_range` analog
    is needed. -/
theorem stable_of_inProbRange_compl {l α : Type}
    {p : Program (ProcedureState l) α} (hp : p.inProbRange ((roLift l).probRange)ᶜ) : Stable p := by
  show (p >>= fun a => convertL >>= fun _ => pure a) = (convertL >>= fun _ => p)
  have h_commute : (p >>= fun a => convertL >>= fun b => pure (a, b))
                 = (convertL >>= fun b => p >>= fun a => pure (a, b)) :=
    Program.commute_of_disjoint_prob hp convertL_inProbRange (le_refl _)
  have hL : (p >>= fun a => convertL >>= fun b => pure (a, b)) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : Program (ProcedureState l) α))
          = (p >>= fun a => convertL >>= fun _ => (Pure.pure a : Program (ProcedureState l) α)) := by
    rw [Program.bind_assoc]; congr 1; funext a
    rw [Program.bind_assoc]; congr 1; funext _
    rw [Program.pure_bind]
  have hR : (convertL >>= fun b => p >>= fun a => pure (a, b)) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : Program (ProcedureState l) α))
          = (convertL >>= fun _ => p) := by
    rw [Program.bind_assoc]
    congr 1; funext _
    rw [Program.bind_assoc]
    rw [show (fun a : α => pure (a, ()) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : Program (ProcedureState l) α)))
          = (fun a : α => (Pure.pure a : Program (ProcedureState l) α)) from by
        funext a; rw [Program.pure_bind]]
    exact Program.bind_pure _
  rw [← hL, h_commute, hR]

/-- **`Stable` from confinement to a lens disjoint from the RO** (probabilistic). The
    `ProbLensRange` analogue of `stable_of_confined_lens`. No `complement_range` needed — the
    `ᶜ`-form bound `hdisj` feeds `inProbRange_mono` directly. -/
theorem stable_of_confinedP_lens {l α advSt : Type}
    (L_adv : Lens advSt (ProcedureState l)) (hdisj : L_adv.probRange ≤ ((roLift l).probRange)ᶜ)
    {p : Program (ProcedureState l) α} (hp : p.inProbRange L_adv.probRange) : Stable p :=
  stable_of_inProbRange_compl (Program.inProbRange_mono hp hdisj)

/-- **Probabilistic confinement predicate.** The `inProbRange`/`probRange` analogue of `Confined`:
    each leaf's footprint lies in the adversary region `L_adv`. Crucially the `get`-leaves are now
    soundly derivable from footprint disjointness (litmus), unlike `Confined` (`TotLensRange`),
    where `get`'s `Program.range` collapses (the `get_confined_of_fv` sorry). -/
def ConfinedP {holes : HoleSigs} {l advSt : Type} (L_adv : Lens advSt (ProcedureState l)) :
    StmtWithHoles holes l → Prop
  | .skip => True
  | .sample x e =>
      (programDenotation (StmtWithHoles.sample x e : Stmt l)).inProbRange L_adv.probRange
  | .call' x ls b r p =>
      (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l)).inProbRange L_adv.probRange
  | .hole _ x p => (Program.get p).inProbRange L_adv.probRange ∧
      (∀ ret, (Program.set x ret).inProbRange L_adv.probRange)
  | .seq s1 s2 => ConfinedP L_adv s1 ∧ ConfinedP L_adv s2
  | .ifThenElse c t e =>
      (Program.get c).inProbRange L_adv.probRange ∧ ConfinedP L_adv t ∧ ConfinedP L_adv e
  | .while c t => (Program.get c).inProbRange L_adv.probRange ∧ ConfinedP L_adv t

/-- **`ConfinedP` discharges `Loc`** (theorem-1 locality), leaf by leaf — reusing the existing
    `Loc`→theorems chain. The `ProbLensRange` analogue of `confined_loc`. -/
theorem confinedP_loc {holes : HoleSigs} {l advSt : Type}
    (L_adv : Lens advSt (ProcedureState l)) (hdisj : L_adv.probRange ≤ ((roLift l).probRange)ᶜ)
    (hc : ∀ {sig : ProcedureSignature}, HoleIndex holes sig → Countable sig.ParamType) :
    ∀ (A : StmtWithHoles holes l), ConfinedP L_adv A → Loc A
  | .skip, _ => trivial
  | .sample _ _, h => stable_of_confinedP_lens L_adv hdisj h
  | .call' _ _ _ _ _, h => stable_of_confinedP_lens L_adv hdisj h
  | .hole n _ _, h =>
      haveI := hc n
      ⟨stable_of_confinedP_lens L_adv hdisj h.1,
        fun ret => stable_of_confinedP_lens L_adv hdisj (h.2 ret)⟩
  | .seq s1 s2, h => ⟨confinedP_loc L_adv hdisj hc s1 h.1, confinedP_loc L_adv hdisj hc s2 h.2⟩
  | .ifThenElse _ t e, h =>
      ⟨stable_of_confinedP_lens L_adv hdisj h.1, confinedP_loc L_adv hdisj hc t h.2.1,
        confinedP_loc L_adv hdisj hc e h.2.2⟩
  | .«while» _ t, h =>
      ⟨stable_of_confinedP_lens L_adv hdisj h.1, confinedP_loc L_adv hdisj hc t h.2⟩

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

/-- **Theorem 1, probabilistic confinement form.**  An adversary confined (in the `inProbRange`
    sense) to any lens `L_adv` whose `probRange` is disjoint from the oracle cannot distinguish
    lazy from eager.  The `ProbLensRange` rendering of `transfer_instantiate_confined`; reuses the
    existing `Loc`→`Program.transfer_instantiate` chain via `confinedP_loc`. -/
theorem Program.transfer_instantiate_confinedP {sig : ProcedureSignature} {advSt : Type}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (L_adv : Lens advSt (ProcedureState (sig.LocalVariableState A.locals)))
    (hdisj : L_adv.probRange ≤ ((roLift (sig.LocalVariableState A.locals)).probRange)ᶜ)
    (hconf : ConfinedP L_adv A.body)
    (hret : (Program.get A.return_val).inProbRange L_adv.probRange) :
    Program.transfer
      (procedureDenotation (A.instantiate RO_lazy) args)
      (procedureDenotation (A.instantiate RO_eager) args) :=
  Program.transfer_instantiate A args
    (confinedP_loc L_adv hdisj roHole_paramType_countable A.body hconf)
    (stable_of_confinedP_lens L_adv hdisj hret)

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

/-- **`fvP`-disjointness ⟹ `ConfinedP` — COMPLETE, no `sorry`.**  The full structural reduction
    that `confined_of_fv` (`TotLensRange`) could only achieve modulo the `get` `sorry`
    (`get_confined_of_fv`), the orthogonal `call'` `sorry`, and an *assumed* setter bridge
    (`hset`).  Over `ProbLensRange` every leaf — get, set, sample, *and the nested `call'`* —
    discharges by the litmus (self-range, `inProbRange_selfRange`), so the reduction is total.
    Composing with `confinedP_loc`/`confinedP_locP` gives the two main theorems directly from a
    footprint-disjointness hypothesis. -/
theorem confinedP_of_fv {holes : HoleSigs} {l advSt : Type}
    (L_adv : Lens advSt (ProcedureState l))
    (hc : ∀ {sig : ProcedureSignature}, HoleIndex holes sig → Countable sig.ParamType) :
    ∀ (A : StmtWithHoles holes l), fvP_stmt A ≤ L_adv.probRange → ConfinedP L_adv A
  | .skip, _ => trivial
  | .sample x e, h => by
      show (programDenotation (StmtWithHoles.sample x e : Stmt l)).inProbRange L_adv.probRange
      exact Program.inProbRange_of_probRange_le h
  | .call' x ls b r p, h => by
      show (programDenotation (StmtWithHoles.call' x ls b r p : Stmt l)).inProbRange L_adv.probRange
      exact Program.inProbRange_of_probRange_le h
  | .hole n x p, h =>
      haveI := hc n
      ⟨get_confinedP_of_fv p (le_sup_left.trans h),
        fun ret => set_confinedP_of_fv x ret
          ((le_iSup (fun ret => (Program.set x ret).probRange) ret).trans (le_sup_right.trans h))⟩
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

/-- **Theorem 1, end-to-end from footprint disjointness.**  Lazy/eager indistinguishability for any
    adversary whose probabilistic footprint (body + return) lies in a region `L_adv` disjoint from
    the RO table — derived entirely from the footprint hypotheses, with no per-leaf confinement to
    check by hand.  The full `fvP → ConfinedP → Loc → transfer` chain in one step. -/
theorem Program.transfer_instantiate_of_fvP {sig : ProcedureSignature} {advSt : Type}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (L_adv : Lens advSt (ProcedureState (sig.LocalVariableState A.locals)))
    (hdisj : L_adv.probRange ≤ ((roLift (sig.LocalVariableState A.locals)).probRange)ᶜ)
    (hbody : fvP_stmt A.body ≤ L_adv.probRange)
    (hret : (Program.get A.return_val).probRange ≤ L_adv.probRange) :
    Program.transfer
      (procedureDenotation (A.instantiate RO_lazy) args)
      (procedureDenotation (A.instantiate RO_eager) args) :=
  Program.transfer_instantiate_confinedP A args L_adv hdisj
    (confinedP_of_fv L_adv roHole_paramType_countable A.body hbody)
    (get_confinedP_of_fv A.return_val hret)

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

end

end GaudisCrypt.Lib.RO.SyntacticEquiv
