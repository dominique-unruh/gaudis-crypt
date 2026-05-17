import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Uniform
import PlonkLean.Misc

/-!
# General stuff
-/

-- TODO: Should we keep this? It's a very simple rhs
def recursion [OmegaCompletePartialOrder a] [OrderBot a] (F : a →𝒄 a) : a :=
  F.lfp

/-!
# Discrete subprobability monad
-/

def SubProbability (a : Type) := {mu: @MeasureTheory.Measure a ⊤ // mu ⊤ <= 1}

noncomputable
instance : Monad SubProbability where
  pure a :=
    ⟨@MeasureTheory.Measure.dirac _ ⊤ a, by simp⟩
  bind x f :=
    let ⟨mu, h⟩ := x
    ⟨MeasureTheory.Measure.bind mu (fun a => (f a).1), by
        simp only [Set.top_eq_univ]
        rw [MeasureTheory.Measure.bind_apply MeasurableSet.univ measurable_from_top.aemeasurable]
        calc ∫⁻ a, (f a).1 ⊤ ∂mu
            ≤ ∫⁻ _, 1 ∂mu := MeasureTheory.lintegral_mono (fun a => (f a).2)
          _ = mu ⊤ := MeasureTheory.lintegral_one
          _ ≤ 1 := h⟩

noncomputable
def toSubProbability (p : PMF α) : SubProbability α :=
  ⟨@PMF.toMeasure _ ⊤ p, by
    haveI := @PMF.toMeasure.isProbabilityMeasure _ ⊤ p
    exact le_of_eq MeasureTheory.IsProbabilityMeasure.measure_univ⟩

noncomputable
def SubProbability.uniform [h : Fintype α] [h : Nonempty α] : SubProbability α :=
  toSubProbability (PMF.uniformOfFintype α)

def SubProbability.ofEvent (μ : SubProbability a) (e : Set a) := (μ.1 e).toNNReal

instance : CoeFun (SubProbability a) (fun _ => a -> NNReal) where
  coe μ x := μ.ofEvent {x}

instance [Countable a] : FunLike (SubProbability a) a NNReal where
  coe μ x := μ.ofEvent {x}
  coe_injective' μ ν h := by
    apply Subtype.ext
    -- exact @MeasureTheory.Measure.ext_of_singleton a ⊤ _ μ.1 ν.1 (fun x => congr_fun h x)
    sorry




instance : PartialOrder (SubProbability a) where
  le p q := p.1 <= q.1
  le_refl _ _ := le_refl _
  le_trans _ _ _ hpq hqr s := le_trans (hpq s) (hqr s)
  le_antisymm p q hpq hqp := by
    apply Subtype.ext
    exact le_antisymm hpq hqp


instance : OrderBot (SubProbability a) where
  bot := ⟨0, by simp⟩
  bot_le x := MeasureTheory.Measure.zero_le _



noncomputable instance : OmegaCompletePartialOrder (SubProbability a) where
  ωSup c := ⟨⨆ n, (c n).1, by
    have hmono : Monotone fun n => (c n).1 := fun _ _ hmn => c.monotone hmn
    have heq : (⨆ n, (c n).1) Set.univ = ⨆ n, (c n).1 Set.univ := by
      have h := @lintegral_iSup_measure_nat a ⊤
                  (fun n => (c n).1) hmono (fun _ => 1)
      simp only [MeasureTheory.lintegral_one] at h
      exact h
    change (⨆ n, (c n).1) Set.univ ≤ 1
    rw [heq]
    exact iSup_le fun n => (c n).2⟩
  le_ωSup c n := le_iSup (fun m => (c m).1) n
  ωSup_le c x h := show (⨆ n, (c n).1) ≤ x.1 from iSup_le h



/-!
# Stateful programs
-/

@[reducible]
def Program (state : Type) := StateT state SubProbability

noncomputable
def SubProbability.toProgram (p : SubProbability a) : Program s a := StateT.lift p

noncomputable
def PMF.toProgram {st α} (p : PMF α) : Program st α := StateT.lift (toSubProbability p)

noncomputable
def Program.uniform [h : Fintype α] [h : Nonempty α] : Program s α :=
  SubProbability.uniform.toProgram

def Program.finalProb (prog : Program s a) (st : s) (X : Set a) : NNReal :=
  ((prog st).ofEvent (X ×ˢ ⊤))

def Program.finalProb1 (prog : Program s a) (st : s) (x : a) : NNReal :=
  prog.finalProb st {x}


instance : PartialOrder (Program s a) where
  le p q := ∀ s, p s <= q s
  le_refl _ _ := le_refl _
  le_trans _ _ _ hpq hqr s := le_trans (hpq s) (hqr s)
  le_antisymm p q hpq hqp := by
    funext s
    exact Subtype.ext (le_antisymm (hpq s) (hqp s))

instance : OrderBot (Program s a) where
  bot := fun _ => ⟨0, by simp⟩
  bot_le _ _ := MeasureTheory.Measure.zero_le _


noncomputable instance : OmegaCompletePartialOrder (Program s a) where
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
