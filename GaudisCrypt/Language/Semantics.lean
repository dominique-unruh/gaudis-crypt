import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Uniform
import GaudisCrypt.Misc
import GaudisCrypt.Language.Lens
import GaudisCrypt.Language.SubProbability

open GaudisCrypt

namespace GaudisCrypt

/-!
# General stuff
-/

-- Use this instead of .lfp so make sure the types are right.
@[reducible]
def recursion {a} {b : a → Type*} [∀ x, OmegaCompletePartialOrder (b x)] [∀ x, OrderBot (b x)]
   (F : (∀ x, b x) →𝒄 (∀ x, b x)) : ∀ x, b x :=
  F.lfp

/-!
# Stateful programs
-/

/-- A probabilistic program with state `state` and result `a`: from an initial state, a
sub-distribution over results and final states.

This is `StateT state SubProbability a` unfolded, and deliberately *not* defined as that:
`StateT` puts the state and the result in one universe, but a program's state lives in a higher
universe than its results (variables are indexed by `VariableName`, which contains a `Type`, so
`VariableAssignment` and `ProgramState` are in `Type 1`, while results are `Unit`, `Bool`, …).
The `Monad` instance below and the instances after the monad laws are
`StateT`'s, written out.  The state and the results have independent universes. -/
def ProgramDenotation (state : Type u) (a : Type v) : Type (max u v) :=
  state → SubProbability (a × state)

/-- Run a sub-probability as a program that leaves the state alone (`StateT.lift`).  The bind is
`SubProbability.hbind` since `a` and `a × s` may live in different universes. -/
noncomputable
def SubProbability.toProgramDenotation (p : SubProbability a) : ProgramDenotation s a :=
  fun st => p.hbind fun x => pure (x, st)

noncomputable
def PMF.toProgramDenotation {st α} (p : PMF α) : ProgramDenotation st α :=
  (toSubProbability p).toProgramDenotation

noncomputable
def ProgramDenotation.uniform [h : Fintype α] [h : Nonempty α] : ProgramDenotation s α :=
  SubProbability.uniform.toProgramDenotation

/-- Uniform subprobability over a nonempty finset. -/
noncomputable
def SubProbability.uniformOfFinset {α : Type u} (fs : Finset α) (hs : fs.Nonempty) :
    SubProbability α :=
  toSubProbability (PMF.uniformOfFinset fs hs)

/-- Uniform sampling over a nonempty finset (used e.g. for "sample without
    replacement" — uniform over the complement of the values seen so far). -/
noncomputable
def ProgramDenotation.uniformOfFinset {s : Type u} {α : Type v} (fs : Finset α) (hs : fs.Nonempty) :
    ProgramDenotation s α :=
  (SubProbability.uniformOfFinset fs hs).toProgramDenotation

def ProgramDenotation.finalProb (prog : ProgramDenotation s a) (st : s) (X : Set a) : NNReal :=
  ((prog st).ofEvent (X ×ˢ ⊤))

def ProgramDenotation.finalProb1 (prog : ProgramDenotation s a) (st : s) (x : a) : NNReal :=
  prog.finalProb st {x}


instance : PartialOrder (ProgramDenotation s a) where
  le p q := ∀ s, p s <= q s
  le_refl _ _ := le_refl _
  le_trans _ _ _ hpq hqr s := le_trans (hpq s) (hqr s)
  le_antisymm p q hpq hqp := by
    funext s
    exact Subtype.ext (le_antisymm (hpq s) (hqp s))

instance : OrderBot (ProgramDenotation s a) where
  bot := fun _ => ⟨0, ⟨by simp, discreteMeasure_zero⟩⟩
  bot_le _ _ := MeasureTheory.Measure.zero_le _


noncomputable instance : OmegaCompletePartialOrder (ProgramDenotation s a) where
  ωSup c st :=
    let c_st n := c n st
    let mono : Monotone c_st := by
      intros n m hnm s
      unfold c_st
      apply c.monotone hnm
    OmegaCompletePartialOrder.ωSup ⟨c_st, mono⟩
  le_ωSup c n := by
   intros s
   apply OmegaCompletePartialOrder.le_ωSup
     (⟨fun m => c m s, fun _ _ hmn => c.monotone hmn s⟩)
  ωSup_le c x h s := by
    unfold OmegaCompletePartialOrder.ωSup
    apply OmegaCompletePartialOrder.ωSup_le
    intro n
    apply h n s

noncomputable
instance : Monad (ProgramDenotation s) where
  pure x := fun st => pure (x, st)
  bind p f := fun st => p st >>= fun r => f r.1 r.2

/-- `pure`, applied to a state.  (What `StateT.pure` unfolded to.) -/
theorem ProgramDenotation.pure_apply {s : Type u} {a : Type v} (x : a) (st : s) :
    (pure x : ProgramDenotation s a) st = pure (x, st) := rfl

/-- `bind`, applied to a state.  (What `StateT.bind` unfolded to.) -/
theorem ProgramDenotation.bind_apply {s : Type u} {a b : Type v} (p : ProgramDenotation s a)
    (f : a → ProgramDenotation s b) (st : s) :
    (p >>= f) st = p st >>= fun r => f r.1 r.2 := rfl

/-- Running a sub-probability as a program that leaves the state alone (`StateT.lift`). -/
noncomputable instance {s : Type u} : MonadLift SubProbability (ProgramDenotation s) where
  monadLift := SubProbability.toProgramDenotation

/-- `toProgramDenotation`, applied to a state.  (In one universe, `SubProbability.hbind_eq_bind`
turns the `hbind` into `>>=`.) -/
theorem ProgramDenotation.toProgramDenotation_apply {s : Type u} {a : Type v}
    (μ : SubProbability a) (st : s) :
    μ.toProgramDenotation st = μ.hbind fun x => pure (x, st) := rfl

@[fun_prop]
theorem ProgramDenotation.bind_mono [Preorder i]
  (f : i → ProgramDenotation s a) (g : i → a → ProgramDenotation s b)
  (hf : Monotone f) (hg : Monotone g) :
  Monotone (fun x => f x >>= g x) := by
    intro x y hxy s_val
    exact SubProbability.bind_mono (fun x => f x s_val) (fun x p => g x p.1 p.2)
      (fun _ _ h => hf h s_val) (fun _ _ h p => hg h p.1 p.2) hxy


@[fun_prop]
lemma ProgramDenotation.bind_ωScottContinuous
  [OmegaCompletePartialOrder a]
  (f : a → ProgramDenotation s b) (g : a → b → ProgramDenotation s c)
  (hg : OmegaCompletePartialOrder.ωScottContinuous g)
  (hf : OmegaCompletePartialOrder.ωScottContinuous f) :
  OmegaCompletePartialOrder.ωScottContinuous fun x => (f x) >>= (g x) := by
  simp only [Bind.bind]
  have hg' : OmegaCompletePartialOrder.ωScottContinuous (fun x (p : b × s) => g x p.1 p.2) :=
    OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup
      ⟨fun _ _ hxy p => hg.monotone hxy p.1 p.2,
       fun ch => funext fun p => ((hg.apply₂ p.1).apply₂ p.2).map_ωSup ch⟩
  refine OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup ⟨?mono, ?sup⟩
  case mono => exact ProgramDenotation.bind_mono _ _ hf.monotone hg.monotone
  case sup =>
    intro ch
    funext s_val
    exact (SubProbability.bind_ωScottContinuous (fun x => f x s_val) (fun x p => g x p.1 p.2)
      hg' (hf.apply₂ s_val)).map_ωSup ch

noncomputable
def while_iteration (cond : ProgramDenotation s Bool) (body : ProgramDenotation s Unit) :
  (Unit → ProgramDenotation s Unit) →𝒄 (Unit → ProgramDenotation s Unit) :=
  OmegaCompletePartialOrder.ContinuousHom.ofFun fun (fp : Unit → ProgramDenotation s Unit) => fun ()
      =>
    do if ← cond then body; fp ()
       else return ()

-- TODO Make while loop return non-unit value
noncomputable
def while_loop (cond : ProgramDenotation s Bool) (body : ProgramDenotation s Unit) :
    ProgramDenotation s Unit :=
  recursion (while_iteration cond body) ()

theorem while_unroll (cond : ProgramDenotation s Bool) (body : ProgramDenotation s Unit) :
  while_loop cond body = do
      if ← cond then
        body
        while_loop cond body
      else
        return () := by calc
  _ = recursion (while_iteration cond body) () := rfl
  _ = while_iteration cond body (recursion (while_iteration cond body)) () := by
    simp [ContinuousHom.map_lfp]
  _ = _ := rfl

noncomputable
def ProgramDenotation.get_state : ProgramDenotation s s := fun st => pure (st, st)

/-- Overwrite the whole state. -/
noncomputable
def ProgramDenotation.set_state (st' : s) : ProgramDenotation s Unit := fun _ => pure ((), st')

/-- `ProgramDenotation.get`/`ProgramDenotation.set` accept anything that forgets to a
    `Getter`/`Setter`
    — a `Getter`/`Setter` itself, or a full `Lens`/`Variable`. The value/state
    types are `outParam`s recovered from the argument, which sidesteps the Lean
    4.30 coercion that no longer fires when the value type is a metavariable. -/
class AsGetter (T : Type w) (a : outParam (Type u)) (s : outParam (Type v)) where
  toG : T → Getter a s
class AsSetter (T : Type w) (a : outParam (Type u)) (s : outParam (Type v)) where
  toS : T → Setter a s

instance {a : Type u} {s : Type v} : AsGetter (Getter a s) a s := ⟨id⟩
instance {a : Type u} {s : Type v} : AsGetter (Lens a s) a s := ⟨Lens.toGetter⟩
instance {a : Type u} {s : Type v} : AsSetter (Setter a s) a s := ⟨id⟩
instance {a : Type u} {s : Type v} : AsSetter (Lens a s) a s := ⟨Lens.toSetter⟩

-- `set` and `get` are written on the state directly, not with `do` over `get_state`: that `do`
-- would bind a state-typed result into a `Unit`- or `a`-typed one, and `>>=` needs both result
-- types in one universe.
noncomputable
def ProgramDenotation.set {T : Type w} {a : Type u} {s : Type v} [AsSetter T a s] (v : T) (x : a) :
    ProgramDenotation s Unit :=
  fun st => pure ((), (AsSetter.toS v).set x st)

noncomputable
def ProgramDenotation.get {T : Type w} {a : Type u} {s : Type v} [AsGetter T a s] (v : T) :
    ProgramDenotation s a :=
  fun st => pure ((AsGetter.toG v).get st, st)

noncomputable
def ProgramDenotation.skip : ProgramDenotation s Unit := pure ()

-- TODO: Does this already exist somewhere?
-- TODO: Should be called Lens.liftProgramDenotation by analogy
/-- Run `p` on the part of the state that `lens` selects.  (`s` and `t` may live in different
universes, hence `SubProbability.hbind`.) -/
noncomputable
def ProgramDenotation.zoom (lens : Lens s t) (p : ProgramDenotation s a) : ProgramDenotation t a :=
  fun t_val => (p (lens.get t_val)).hbind fun as => pure (as.1, lens.set as.2 t_val)

/-! ## Monad laws for `ProgramDenotation s` -/

-- The three laws below are what `LawfulMonad (ProgramDenotation s)` is built from (after
-- `bind_bot`); `SubProbability` has no `LawfulMonad` instance to derive them from.
lemma ProgramDenotation.bind_assoc {s : Type u} {a b c : Type v}
    (p : ProgramDenotation s a) (f : a → ProgramDenotation s b) (g : b → ProgramDenotation s c) :
    (p >>= f) >>= g = p >>= fun x => f x >>= g := by
  funext st
  apply Subtype.ext
  letI : MeasurableSpace (a × s) := ⊤
  letI : MeasurableSpace (b × s) := ⊤
  letI : MeasurableSpace (c × s) := ⊤
  exact MeasureTheory.Measure.bind_bind
    measurable_from_top.aemeasurable measurable_from_top.aemeasurable

lemma ProgramDenotation.pure_bind {s : Type u} {a b : Type v} (x : a)
    (f : a → ProgramDenotation s b) :
    (pure x : ProgramDenotation s a) >>= f = f x := by
  funext st
  apply Subtype.ext
  letI : MeasurableSpace (a × s) := ⊤
  letI : MeasurableSpace (b × s) := ⊤
  exact MeasureTheory.Measure.dirac_bind measurable_from_top (x, st)

lemma ProgramDenotation.bind_pure {s : Type u} {a : Type v} (m : ProgramDenotation s a) :
    m >>= pure = m := by
  funext st
  apply Subtype.ext
  letI : MeasurableSpace (a × s) := ⊤
  change MeasureTheory.Measure.bind (m st).1 (fun p => @MeasureTheory.Measure.dirac (a × s) ⊤ p)
      = (m st).1
  rw [show (fun (p : a × s) => @MeasureTheory.Measure.dirac (a × s) ⊤ p) =
          (fun (p : a × s) => @MeasureTheory.Measure.dirac (a × s) ⊤ (id p)) from rfl]
  rw [MeasureTheory.Measure.bind_dirac_eq_map (m st).1 measurable_id]
  exact MeasureTheory.Measure.map_id

lemma ProgramDenotation.bot_bind {s : Type u} {a b : Type v} (f : a → ProgramDenotation s b) :
    (⊥ : ProgramDenotation s a) >>= f = ⊥ := by
  funext st
  apply Subtype.ext
  exact MeasureTheory.Measure.bind_zero_left _

lemma ProgramDenotation.bind_bot {s : Type u} {a b : Type v} (m : ProgramDenotation s a) :
    m >>= (fun _ => (⊥ : ProgramDenotation s b)) = ⊥ := by
  funext st
  apply Subtype.ext
  exact MeasureTheory.Measure.bind_zero_right' _

/-! ## The instances `StateT` used to provide -/

/-- The monad laws.  `StateT` would only have given this from a `LawfulMonad SubProbability`,
which does not exist; here it comes from the three laws proved above. -/
instance {s : Type u} : LawfulMonad (ProgramDenotation.{u, v} s) :=
  LawfulMonad.mk'
    (id_map := fun x => ProgramDenotation.bind_pure x)
    (pure_bind := fun x f => ProgramDenotation.pure_bind x f)
    (bind_assoc := fun p f g => ProgramDenotation.bind_assoc p f g)

/-- Reading and writing the whole state (`get`/`set`/`modify` in `do` notation).  Lean's
`MonadStateOf` puts the state and the results in one universe, so this instance only exists for
results in the state's universe. -/
noncomputable instance {s : Type u} : MonadStateOf s (ProgramDenotation.{u, u} s) where
  get := ProgramDenotation.get_state
  set st' := fun _ => pure (PUnit.unit, st')
  modifyGet f := fun st => pure (f st)

/-! ## `zoom` is a monad morphism -/

theorem ProgramDenotation.zoom_pure {s : Type u} {t : Type v} {a : Type w} (lens : Lens s t)
    (x : a) : ProgramDenotation.zoom lens (pure x) = (pure x : ProgramDenotation t a) := by
  funext tv
  change (pure (x, lens.get tv) : SubProbability (a × s)).hbind
          (fun as => pure (as.1, lens.set as.2 tv))
       = (pure (x, tv) : SubProbability (a × t))
  rw [SubProbability.pure_hbind]
  simp only [lens.get_set]

theorem ProgramDenotation.zoom_bind {s : Type u} {t : Type v} {a b : Type w} (lens : Lens s t)
    (p : ProgramDenotation s a) (k : a → ProgramDenotation s b) :
    ProgramDenotation.zoom lens (p >>= k) = ProgramDenotation.zoom lens p >>= fun a =>
        ProgramDenotation.zoom lens (k a) := by
  funext tv
  change (((p (lens.get tv)).hbind fun as => k as.1 as.2).hbind
            fun bs => pure (bs.1, lens.set bs.2 tv))
       = ((p (lens.get tv)).hbind fun as => pure (as.1, lens.set as.2 tv)).hbind
            fun cs => (k cs.1 (lens.get cs.2)).hbind fun bs => pure (bs.1, lens.set bs.2 cs.2)
  rw [SubProbability.hbind_assoc, SubProbability.hbind_assoc]
  congr 1; funext as
  rw [SubProbability.pure_hbind]
  simp only [lens.set_get, lens.set_set]

/-
noncomputable instance {m : Type*} : Monoid (m → SubProbability m) where
  mul f g := fun x => g x >>= f
  one := pure
  mul_assoc f g h := funext fun x => by
    apply Subtype.ext; letI : MeasurableSpace m := ⊤
    exact (MeasureTheory.Measure.bind_bind
      measurable_from_top.aemeasurable measurable_from_top.aemeasurable).symm
  one_mul f := funext fun x => by
    apply Subtype.ext; letI : MeasurableSpace m := ⊤
    exact MeasureTheory.Measure.bind_dirac
  mul_one f := funext fun x => by
    apply Subtype.ext; letI : MeasurableSpace m := ⊤
    change (MeasureTheory.Measure.dirac x).bind (fun a => (f a).1) = (f x).1
    exact MeasureTheory.Measure.dirac_bind measurable_from_top x



structure Footprint (m : Type _) where
  updates : Set (m -> SubProbability m)
  id : pure ∈ updates
  comp : f ∈ updates → g ∈ updates → (f * g) ∈ updates
  double_commutant : (Submonoid.centralizer (Submonoid.centralizer updates).carrier).carrier = updates

private lemma centralizer_carrier_eq' (S : Set (m → SubProbability m)) :
    (Submonoid.centralizer S).carrier = Set.centralizer S := by
  ext x; simp [Submonoid.mem_centralizer_iff, Set.mem_centralizer_iff]

instance : Compl (Footprint m) where
  compl range := ⟨(Submonoid.centralizer range.updates).carrier,
    Submonoid.one_mem _,
    fun hf hg => Submonoid.mul_mem _ hf hg,
    by simp only [centralizer_carrier_eq']; exact Set.centralizer_centralizer_centralizer _⟩


def _root_.GaudisCrypt.ProgramDenotation.inRange {s a : Type} (p :
    ProgramDenotation s a)
  (R : Footprint s) : Prop :=
  ∀ f ∈ Rᶜ.updates,
    (fun st => do let st' <- f st; let (x, st'') <- p st'; return (x,st''))
  = (fun st => do let (x, st') <- p st; let st'' <- f st'; return (x, st''))

def Footprint.from (generators : Set (m -> SubProbability m)) : Footprint m where
  updates := Submonoid.centralizer (Submonoid.centralizer generators).carrier
  id := Submonoid.one_mem _
  comp := fun hf hg => Submonoid.mul_mem _ hf hg
  double_commutant := by
    simp only [centralizer_carrier_eq']; exact Set.centralizer_centralizer_centralizer _

/- The smallest DetermFootprint in which `p` lives. -/
noncomputable def _root_.GaudisCrypt.ProgramDenotation.rangeUnit2 {s a : Type} (p
    : ProgramDenotation s Unit)
  : Footprint s := Footprint.from { fun st => do let (_,st') <- p st; return st' }

noncomputable def _root_.GaudisCrypt.ProgramDenotation.range2 {s a : Type} (p :
    ProgramDenotation s a)
  : Footprint s := Footprint.from { fun st => do let (x,st') <- p st; if (x ≠ y) then ⊥ else ⊤; return st' | y : a }

/- Litmus test: p.inRange R <-> p.range <= R  -/

-/

end GaudisCrypt
