import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Uniform
import GaudisCrypt.Misc
import GaudisCrypt.Language.Lens
import GaudisCrypt.Language.SubProbability

open GaudisCrypt.Language.Lens

namespace GaudisCrypt.Language.Semantics

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

def ProgramDenotation (state : Type) : Type → Type := StateT state SubProbability

noncomputable
def SubProbability.toProgramDenotation (p : SubProbability a) : ProgramDenotation s a := StateT.lift
    p

noncomputable
def PMF.toProgramDenotation {st α} (p : PMF α) : ProgramDenotation st α := StateT.lift
    (toSubProbability p)

noncomputable
def ProgramDenotation.uniform [h : Fintype α] [h : Nonempty α] : ProgramDenotation s α :=
  SubProbability.uniform.toProgramDenotation

/-- Uniform subprobability over a nonempty finset. -/
noncomputable
def SubProbability.uniformOfFinset {α : Type} (fs : Finset α) (hs : fs.Nonempty) :
    SubProbability α :=
  toSubProbability (PMF.uniformOfFinset fs hs)

/-- Uniform sampling over a nonempty finset (used e.g. for "sample without
    replacement" — uniform over the complement of the values seen so far). -/
noncomputable
def ProgramDenotation.uniformOfFinset {s α : Type} (fs : Finset α) (hs : fs.Nonempty) :
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
instance : Monad (ProgramDenotation s) :=
  (inferInstance : Monad (StateT s SubProbability))

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
def ProgramDenotation.get_state : ProgramDenotation s s := StateT.get

/-- `ProgramDenotation.get`/`ProgramDenotation.set` accept anything that forgets to a
    `Getter`/`Setter`
    — a `Getter`/`Setter` itself, or a full `Lens`/`Variable`. The value/state
    types are `outParam`s recovered from the argument, which sidesteps the Lean
    4.30 coercion that no longer fires when the value type is a metavariable. -/
class AsGetter (T : Type) (a s : outParam Type) where toG : T → Getter a s
class AsSetter (T : Type) (a s : outParam Type) where toS : T → Setter a s

instance {a s : Type} : AsGetter (Getter a s) a s := ⟨id⟩
instance {a s : Type} : AsGetter (Lens a s) a s := ⟨Lens.toGetter⟩
instance {a s : Type} : AsSetter (Setter a s) a s := ⟨id⟩
instance {a s : Type} : AsSetter (Lens a s) a s := ⟨Lens.toSetter⟩

noncomputable
def ProgramDenotation.set {T a s : Type} [AsSetter T a s] (v : T) (x : a) : ProgramDenotation s
    Unit := do
    let st <- StateT.get
    let st' := (AsSetter.toS v).set x st
    StateT.set st'


noncomputable
def ProgramDenotation.get {T a s : Type} [AsGetter T a s] (v : T) : ProgramDenotation s a := do
    let s <- StateT.get
    pure ((AsGetter.toG v).get s)

noncomputable
def ProgramDenotation.skip : ProgramDenotation s Unit := pure ()

-- TODO: Does this already exist somewhere?
noncomputable
def ProgramDenotation.zoom (lens : Lens s t) (p : ProgramDenotation s a) : ProgramDenotation t a :=
    fun t_val => do
  let (a, s') ← p (lens.get t_val)
  return (a, lens.set s' t_val)

/-! ## Monad laws for `ProgramDenotation s` -/

-- TODO remove (should already exist for all Monad typeclasses directly)
lemma ProgramDenotation.bind_assoc {s a b c : Type}
    (p : ProgramDenotation s a) (f : a → ProgramDenotation s b) (g : b → ProgramDenotation s c) :
    (p >>= f) >>= g = p >>= fun x => f x >>= g := by
  funext st
  apply Subtype.ext
  letI : MeasurableSpace (a × s) := ⊤
  letI : MeasurableSpace (b × s) := ⊤
  letI : MeasurableSpace (c × s) := ⊤
  exact MeasureTheory.Measure.bind_bind
    measurable_from_top.aemeasurable measurable_from_top.aemeasurable

-- TODO remove (should already exist for all Monad typeclasses directly)
lemma ProgramDenotation.pure_bind {s a b : Type} (x : a) (f : a → ProgramDenotation s b) :
    (pure x : ProgramDenotation s a) >>= f = f x := by
  funext st
  apply Subtype.ext
  letI : MeasurableSpace (a × s) := ⊤
  letI : MeasurableSpace (b × s) := ⊤
  exact MeasureTheory.Measure.dirac_bind measurable_from_top (x, st)

-- TODO remove (should already exist for all Monad typeclasses directly)
lemma ProgramDenotation.bind_pure {s a : Type} (m : ProgramDenotation s a) :
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

lemma ProgramDenotation.bot_bind {s a b : Type} (f : a → ProgramDenotation s b) :
    (⊥ : ProgramDenotation s a) >>= f = ⊥ := by
  funext st
  apply Subtype.ext
  exact MeasureTheory.Measure.bind_zero_left _

lemma ProgramDenotation.bind_bot {s a b : Type} (m : ProgramDenotation s a) :
    m >>= (fun _ => (⊥ : ProgramDenotation s b)) = ⊥ := by
  funext st
  apply Subtype.ext
  exact MeasureTheory.Measure.bind_zero_right' _

/-! ## `zoom` is a monad morphism -/

theorem ProgramDenotation.zoom_pure {s t a : Type} (lens : Lens s t) (x : a) :
    ProgramDenotation.zoom lens (pure x) = (pure x : ProgramDenotation t a) := by
  funext tv
  change (pure (x, lens.get tv) : SubProbability (a × s))
          >>= (fun as => pure (as.1, lens.set as.2 tv))
       = (pure (x, tv) : SubProbability (a × t))
  rw [SubProbability.pure_bind]
  simp only [lens.get_set]

theorem ProgramDenotation.zoom_bind {s t a b : Type} (lens : Lens s t)
    (p : ProgramDenotation s a) (k : a → ProgramDenotation s b) :
    ProgramDenotation.zoom lens (p >>= k) = ProgramDenotation.zoom lens p >>= fun a =>
        ProgramDenotation.zoom lens (k a) := by
  funext tv
  change (((p (lens.get tv)) >>= fun as => k as.1 as.2) >>= fun bs => pure (bs.1, lens.set bs.2 tv))
       = ((p (lens.get tv)) >>= fun as => pure (as.1, lens.set as.2 tv))
          >>= fun cs => (k cs.1 (lens.get cs.2)) >>= fun bs => pure (bs.1, lens.set bs.2 cs.2)
  rw [SubProbability.bind_assoc, SubProbability.bind_assoc]
  congr 1; funext as
  rw [SubProbability.pure_bind]
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


def _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.inRange {s a : Type} (p :
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
noncomputable def _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.rangeUnit2 {s a : Type} (p
    : ProgramDenotation s Unit)
  : Footprint s := Footprint.from { fun st => do let (_,st') <- p st; return st' }

noncomputable def _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.range2 {s a : Type} (p :
    ProgramDenotation s a)
  : Footprint s := Footprint.from { fun st => do let (x,st') <- p st; if (x ≠ y) then ⊥ else ⊤; return st' | y : a }

/- Litmus test: p.inRange R <-> p.range <= R  -/

-/

end GaudisCrypt.Language.Semantics
