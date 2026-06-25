import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Uniform
import GaudisCrypt.Misc

namespace GaudisCrypt.Language.Semantics

/-!
# Discrete subprobability monad
-/

def SubProbability (a : Type u) := {mu: @MeasureTheory.Measure a ⊤ // mu ⊤ <= 1}

noncomputable
instance : Monad SubProbability where
  pure a :=
    ⟨@MeasureTheory.Measure.dirac _ ⊤ a, by simp⟩
  bind := fun ⟨mu, h⟩ f =>
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
    letI : MeasurableSpace a := ⊤
    apply MeasureTheory.Measure.ext_of_singleton
    intro x
    have hμ : μ.1 {x} ≠ ⊤ :=
      ((MeasureTheory.measure_mono (Set.subset_univ _)).trans μ.2).trans_lt ENNReal.one_lt_top |>.ne
    have hν : ν.1 {x} ≠ ⊤ :=
      ((MeasureTheory.measure_mono (Set.subset_univ _)).trans ν.2).trans_lt ENNReal.one_lt_top |>.ne
    have hnn : (μ.1 {x}).toNNReal = (ν.1 {x}).toNNReal := congr_fun h x
    rw [← ENNReal.coe_toNNReal hμ, ← ENNReal.coe_toNNReal hν]
    exact_mod_cast hnn

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

theorem Measure.bind_mono [MeasurableSpace a] [MeasurableSpace b] [Preorder i]
  (f : i → MeasureTheory.Measure a) (g : i → a → MeasureTheory.Measure b)
  (hf : Monotone f) (hg : Monotone g)
  (hgm : ∀ x, Measurable (g x)) :
  Monotone (fun x => MeasureTheory.Measure.bind (f x) (g x)) := by
    intro x y hxy
    apply MeasureTheory.Measure.le_iff.mpr; intro A hA
    calc MeasureTheory.Measure.bind (f x) (g x) A
        ≤ ∫⁻ r, g x r A ∂(f x) := MeasureTheory.Measure.bind_apply_le _ hA
      _ ≤ ∫⁻ r, g y r A ∂(f y) :=
          MeasureTheory.lintegral_mono' (hf hxy)
            (fun r => MeasureTheory.Measure.le_iff.mp (hg hxy r) A hA)
      _ = MeasureTheory.Measure.bind (f y) (g y) A :=
          (MeasureTheory.Measure.bind_apply hA (hgm y).aemeasurable).symm

lemma Measure.bind_ωScottContinuous
  [MeasurableSpace b] [MeasurableSpace c]
  [OmegaCompletePartialOrder a]
  (f : a → MeasureTheory.Measure b) (g : a → b → MeasureTheory.Measure c)
  (hgm : ∀ x, Measurable (g x))
  (hg : OmegaCompletePartialOrder.ωScottContinuous g)
  (hf : OmegaCompletePartialOrder.ωScottContinuous f) :
  OmegaCompletePartialOrder.ωScottContinuous fun x => MeasureTheory.Measure.bind (f x) (g x) := by
  refine OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup ⟨?mono, ?sup⟩
  case mono =>
    apply Measure.bind_mono _ _ hf.monotone hg.monotone hgm
  case sup =>
    intro ch
    have hf_mono : Monotone fun n => f (ch n) := fun _ _ hn => hf.monotone (ch.monotone hn)
    have hg_mono : ∀ r : b, Monotone fun n => g (ch n) r :=
      fun r _ _ hn => hg.monotone (ch.monotone hn) r
    have hf_sup : f (OmegaCompletePartialOrder.ωSup ch) = ⨆ n, f (ch n) :=
      hf.map_ωSup ch
    change MeasureTheory.Measure.bind (f (OmegaCompletePartialOrder.ωSup ch))
             (fun r => g (OmegaCompletePartialOrder.ωSup ch) r) =
           ⨆ n, MeasureTheory.Measure.bind (f (ch n)) (fun r => (g (ch n) r))
    apply MeasureTheory.Measure.ext; intro A hA
    have hmeasure_iSup : ∀ (ν : ℕ → MeasureTheory.Measure c) (hν : Monotone ν),
        (⨆ n, ν n) A = ⨆ n, ν n A := fun ν hν => by
      have h := lintegral_iSup_measure_nat hν (f := Set.indicator A 1)
      simp only [MeasureTheory.lintegral_indicator_one hA] at h; exact h
    have hg_eq_A : ∀ r : b, g (OmegaCompletePartialOrder.ωSup ch) r A =
        ⨆ n, g (ch n) r A := fun r => by
      rw [(hg.apply₂ r).map_ωSup ch]
      exact hmeasure_iSup _ (hg_mono r)
    have hbind_eq : ∀ n, MeasureTheory.Measure.bind (f (ch n)) (g (ch n)) A =
        ∫⁻ r, g (ch n) r A ∂(f (ch n)) := fun n =>
      MeasureTheory.Measure.bind_apply hA (hgm (ch n)).aemeasurable
    rw [MeasureTheory.Measure.bind_apply hA (hgm (OmegaCompletePartialOrder.ωSup ch)).aemeasurable,
        hmeasure_iSup _ (fun m n hmn => by
          apply MeasureTheory.Measure.le_iff.mpr; intro A' hA'
          calc MeasureTheory.Measure.bind (f (ch m)) (g (ch m)) A'
              ≤ ∫⁻ r, g (ch m) r A' ∂(f (ch m)) := MeasureTheory.Measure.bind_apply_le _ hA'
            _ ≤ ∫⁻ r, g (ch n) r A' ∂(f (ch n)) :=
                MeasureTheory.lintegral_mono' (hf.monotone (ch.monotone hmn))
                  (fun r => MeasureTheory.Measure.le_iff.mp
                      (hg.monotone (ch.monotone hmn) r) A' hA')
            _ = MeasureTheory.Measure.bind (f (ch n)) (g (ch n)) A' :=
                (MeasureTheory.Measure.bind_apply hA' (hgm (ch n)).aemeasurable).symm)]
    simp_rw [hbind_eq]
    rw [hf_sup]; simp_rw [hg_eq_A]
    rw [lintegral_iSup_measure_nat hf_mono]
    have hmeas : ∀ m, Measurable (fun a_1 : b => (g (ch m) a_1) A) := fun m =>
      (MeasureTheory.Measure.measurable_coe hA).comp (hgm (ch m))
    conv_lhs => arg 1; ext n_outer; rw [MeasureTheory.lintegral_iSup hmeas
        (fun m₁ m₂ hm => fun r => MeasureTheory.Measure.le_iff.mp (hg_mono r hm) A hA)]
    apply le_antisymm
    · apply iSup_le; intro m; apply iSup_le; intro n
      apply le_trans (MeasureTheory.lintegral_mono' (hf_mono (le_max_left m n))
          (fun r => MeasureTheory.Measure.le_iff.mp (hg_mono r (le_max_right m n)) A hA))
      exact le_iSup (fun k => ∫⁻ r : b, (g (ch k) r) A ∂(f (ch k))) (max m n)
    · apply iSup_le; intro k
      apply le_trans (le_iSup (fun n => ∫⁻ r : b, (g (ch n) r) A ∂(f (ch k))) k)
      exact le_iSup (fun m => ⨆ n, ∫⁻ r : b, (g (ch n) r) A ∂(f (ch m))) k


@[fun_prop]
lemma SubProbability.bind_ωScottContinuous
  [OmegaCompletePartialOrder a]
  (f : a → SubProbability b) (g : a → b → SubProbability c)
  (hg : OmegaCompletePartialOrder.ωScottContinuous g)
  (hf : OmegaCompletePartialOrder.ωScottContinuous f) :
  OmegaCompletePartialOrder.ωScottContinuous fun x => (f x) >>= (g x) := by
  letI : MeasurableSpace b := ⊤; letI : MeasurableSpace c := ⊤
  have hf' : OmegaCompletePartialOrder.ωScottContinuous (fun x => (f x).1) :=
    OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup
      ⟨fun _ _ hxy => hf.monotone hxy, fun ch => congr_arg Subtype.val (hf.map_ωSup ch)⟩
  have hg' : OmegaCompletePartialOrder.ωScottContinuous (fun x r => (g x r).1) :=
    OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup
      ⟨fun _ _ hxy r => hg.monotone hxy r,
       fun ch => funext fun r => congr_arg Subtype.val ((hg.apply₂ r).map_ωSup ch)⟩
  have hbind := Measure.bind_ωScottContinuous (fun x => (f x).1) (fun x r => (g x r).1)
    (fun _ => measurable_from_top) hg' hf'
  refine OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup ⟨?mono, ?sup⟩
  case mono => intro x y hxy; exact hbind.monotone hxy
  case sup => intro ch; apply Subtype.ext; exact hbind.map_ωSup ch

@[fun_prop]
theorem SubProbability.bind_mono [Preorder i]
  (f : i → SubProbability a) (g : i → a → SubProbability b)
  (hf : Monotone f) (hg : Monotone g) :
  Monotone (fun x => f x >>= g x) := by
    intro x y hxy
    letI : MeasurableSpace a := ⊤; letI : MeasurableSpace b := ⊤
    exact Measure.bind_mono (fun x => (f x).1) (fun x r => (g x r).1)
      (fun _ _ h => hf h) (fun _ _ h r => hg h r) (fun _ => measurable_from_top) hxy

lemma SubProbability.pure_bind {α β : Type} (x : α) (f : α → SubProbability β) :
    (pure x : SubProbability α) >>= f = f x := by
  apply Subtype.ext
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  exact MeasureTheory.Measure.dirac_bind measurable_from_top x

lemma SubProbability.bind_assoc {α β γ : Type}
    (m : SubProbability α) (f : α → SubProbability β) (g : β → SubProbability γ) :
    (m >>= f) >>= g = m >>= fun x => f x >>= g := by
  apply Subtype.ext
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace γ := ⊤
  exact MeasureTheory.Measure.bind_bind
    measurable_from_top.aemeasurable measurable_from_top.aemeasurable

lemma SubProbability.bind_pure {α : Type} (m : SubProbability α) :
    m >>= pure = m := by
  apply Subtype.ext
  letI : MeasurableSpace α := ⊤
  change MeasureTheory.Measure.bind m.1 (fun a => @MeasureTheory.Measure.dirac α ⊤ a) = m.1
  rw [show (fun a : α => @MeasureTheory.Measure.dirac α ⊤ a)
        = (fun a : α => @MeasureTheory.Measure.dirac α ⊤ (id a)) from rfl]
  rw [MeasureTheory.Measure.bind_dirac_eq_map m.1 measurable_id]
  exact MeasureTheory.Measure.map_id

lemma SubProbability.bot_bind {α β : Type} (f : α → SubProbability β) :
    ((⊥ : SubProbability α) >>= f) = ⊥ := by
  apply Subtype.ext
  exact MeasureTheory.Measure.bind_zero_left _

lemma SubProbability.bind_bot {α β : Type} (m : SubProbability α) :
    (m >>= fun _ => (⊥ : SubProbability β)) = ⊥ := by
  apply Subtype.ext
  exact MeasureTheory.Measure.bind_zero_right' _

/-- Kleisli composition for `SubProbability`: `f * g` applies `g` first, then `f`
    on the result (so `f * g = f ∘ₖ g`), with `pure` as the identity. This is the
    monoid of sub-probability kernels `m → SubProbability m`, the probabilistic
    analogue of `Function.End`. -/
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

end GaudisCrypt.Language.Semantics
