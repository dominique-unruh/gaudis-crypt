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
  (f : i → MeasureTheory.Measure a) (g : i → a → MeasureTheory.Measure b) :
  Monotone (fun x => MeasureTheory.Measure.bind (f x) (g x)) := by
  sorry

@[fun_prop]
lemma Measure.bind_ωScottContinuous
  [MeasurableSpace b] [MeasurableSpace c]
  [OmegaCompletePartialOrder a]
  (f : a → MeasureTheory.Measure b) (g : a → b → MeasureTheory.Measure c)
  (hg : OmegaCompletePartialOrder.ωScottContinuous g)
  (hf : OmegaCompletePartialOrder.ωScottContinuous f) :
  OmegaCompletePartialOrder.ωScottContinuous fun x => MeasureTheory.Measure.bind (f x) (g x) := by
  refine OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup ⟨?mono, ?sup⟩
  case mono => apply Measure.bind_mono
  case sup =>
    intro ch
    have hf_mono : Monotone fun n => f (ch n) := fun _ _ hn => hf.monotone (ch.monotone hn)
    have hg_mono : ∀ r : b, Monotone fun n => g (ch n) r :=
      fun r _ _ hn => hg.monotone (ch.monotone hn) r
    have hf_sup : f (OmegaCompletePartialOrder.ωSup ch) = ⨆ n, f (ch n) :=
      hf.map_ωSup ch
    -- apply Subtype.ext
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
    rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable,
        hmeasure_iSup _ (fun m n hmn => by
          apply MeasureTheory.Measure.le_iff.mpr; intro A' hA'
          rw [MeasureTheory.Measure.bind_apply hA' measurable_from_top.aemeasurable,
              MeasureTheory.Measure.bind_apply hA' measurable_from_top.aemeasurable]
          exact MeasureTheory.lintegral_mono' (hf.monotone (ch.monotone hmn))
            (fun r => MeasureTheory.Measure.le_iff.mp (hg.monotone (ch.monotone hmn) r) A' hA'))]
    simp_rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
    rw [hf_sup]; simp_rw [hg_eq_A]
    rw [lintegral_iSup_measure_nat hf_mono]
    simp_rw [MeasureTheory.lintegral_iSup (fun _ => measurable_from_top)
      (fun m₁ m₂ hm r => MeasureTheory.Measure.le_iff.mp (hg_mono r hm) A hA)]
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
  refine OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup ⟨?mono, ?sup⟩
  case mono =>
    intro x y hxy; change (f x >>= g x).1 ≤ (f y >>= g y).1
    apply MeasureTheory.Measure.le_iff.mpr; intro A hA
    calc (f x >>= g x).1 A
        ≤ ∫⁻ r, (g x r).1 A ∂(f x).1 := MeasureTheory.Measure.bind_apply_le _ hA
      _ ≤ ∫⁻ r, (g y r).1 A ∂(f y).1 :=
          MeasureTheory.lintegral_mono' (hf.monotone hxy)
            (fun r => MeasureTheory.Measure.le_iff.mp (hg.monotone hxy r) A hA)
      _ = (f y >>= g y).1 A :=
          (MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable).symm
  case sup =>
    intro ch
    have hf_mono : Monotone fun n => (f (ch n)).1 := fun _ _ hn => hf.monotone (ch.monotone hn)
    have hg_mono : ∀ r : b, Monotone fun n => (g (ch n) r).1 :=
      fun r _ _ hn => hg.monotone (ch.monotone hn) r
    have hf_sup : (f (OmegaCompletePartialOrder.ωSup ch)).1 = ⨆ n, (f (ch n)).1 :=
      congr_arg Subtype.val (hf.map_ωSup ch)
    apply Subtype.ext
    change MeasureTheory.Measure.bind (f (OmegaCompletePartialOrder.ωSup ch)).1
             (fun r => (g (OmegaCompletePartialOrder.ωSup ch) r).1) =
           ⨆ n, MeasureTheory.Measure.bind (f (ch n)).1 (fun r => (g (ch n) r).1)
    apply MeasureTheory.Measure.ext; intro A hA
    have hmeasure_iSup : ∀ (ν : ℕ → MeasureTheory.Measure c) (hν : Monotone ν),
        (⨆ n, ν n) A = ⨆ n, ν n A := fun ν hν => by
      have h := lintegral_iSup_measure_nat hν (f := Set.indicator A 1)
      simp only [MeasureTheory.lintegral_indicator_one hA] at h; exact h
    have hg_eq_A : ∀ r : b, (g (OmegaCompletePartialOrder.ωSup ch) r).1 A =
        ⨆ n, (g (ch n) r).1 A := fun r => by
      rw [congr_arg Subtype.val ((hg.apply₂ r).map_ωSup ch)]
      exact hmeasure_iSup _ (hg_mono r)
    rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable,
        hmeasure_iSup _ (fun m n hmn => by
          apply MeasureTheory.Measure.le_iff.mpr; intro A' hA'
          rw [MeasureTheory.Measure.bind_apply hA' measurable_from_top.aemeasurable,
              MeasureTheory.Measure.bind_apply hA' measurable_from_top.aemeasurable]
          exact MeasureTheory.lintegral_mono' (hf.monotone (ch.monotone hmn))
            (fun r => MeasureTheory.Measure.le_iff.mp (hg.monotone (ch.monotone hmn) r) A' hA'))]
    simp_rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
    rw [hf_sup]; simp_rw [hg_eq_A]
    rw [lintegral_iSup_measure_nat hf_mono]
    simp_rw [MeasureTheory.lintegral_iSup (fun _ => measurable_from_top)
      (fun m₁ m₂ hm r => MeasureTheory.Measure.le_iff.mp (hg_mono r hm) A hA)]
    apply le_antisymm
    · apply iSup_le; intro m; apply iSup_le; intro n
      apply le_trans (MeasureTheory.lintegral_mono' (hf_mono (le_max_left m n))
          (fun r => MeasureTheory.Measure.le_iff.mp (hg_mono r (le_max_right m n)) A hA))
      exact le_iSup (fun k => ∫⁻ r : b, (g (ch k) r).1 A ∂(f (ch k)).1) (max m n)
    · apply iSup_le; intro k
      apply le_trans (le_iSup (fun n => ∫⁻ r : b, (g (ch n) r).1 A ∂(f (ch k)).1) k)
      exact le_iSup (fun m => ⨆ n, ∫⁻ r : b, (g (ch n) r).1 A ∂(f (ch m)).1) k


/-!
# Stateful programs
-/

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

noncomputable
instance : Monad (Program s) :=
  (inferInstance : Monad (StateT s SubProbability))

@[fun_prop]
lemma Program.bind_ωScottContinuous
  [OmegaCompletePartialOrder a]
  (f : a → Program s b) (g : a → b → Program s c)
  (hg : OmegaCompletePartialOrder.ωScottContinuous g)
  (hf : OmegaCompletePartialOrder.ωScottContinuous f) :
  OmegaCompletePartialOrder.ωScottContinuous fun x => (f x) >>= (g x) := by
  letI : MeasurableSpace b := ⊤
  letI : MeasurableSpace c := ⊤
  letI : MeasurableSpace (b × s) := ⊤
  letI : MeasurableSpace (c × s) := ⊤
  -- (⨆ n, μ n) A = ⨆ n, μ n A for monotone μ_n and measurable A
  have measure_iSup_apply : ∀ {α : Type} [MeasurableSpace α]
      (ν : ℕ → MeasureTheory.Measure α) (hmono : Monotone ν)
      (A : Set α), MeasurableSet A → (⨆ n, ν n) A = ⨆ n, ν n A := by
    intro α _ ν hmono A hA
    have h := lintegral_iSup_measure_nat hmono (f := Set.indicator A 1)
    simp only [MeasureTheory.lintegral_indicator_one hA] at h
    exact h
  refine OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup ⟨?hmono, ?hωSup⟩
  · -- Monotone
    intro x y hxy st
    apply MeasureTheory.Measure.le_iff.mpr
    intro A hA
    change MeasureTheory.Measure.bind (f x st).1 (fun r => (g x r.1 r.2).1) A ≤
           MeasureTheory.Measure.bind (f y st).1 (fun r => (g y r.1 r.2).1) A
    rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable,
        MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
    exact MeasureTheory.lintegral_mono' (hf.monotone hxy st)
      (fun r => MeasureTheory.Measure.le_iff.mp (hg.monotone hxy r.1 r.2) A hA)
  · -- map_ωSup
    intro c
    funext st
    apply Subtype.ext
    change MeasureTheory.Measure.bind (f (OmegaCompletePartialOrder.ωSup c) st).1
             (fun r => (g (OmegaCompletePartialOrder.ωSup c) r.1 r.2).1) =
           ⨆ n, MeasureTheory.Measure.bind (f (c n) st).1 (fun r => (g (c n) r.1 r.2).1)
    apply MeasureTheory.Measure.ext
    intro A hA
    rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable,
        measure_iSup_apply _ (fun n m hnm => by
          apply MeasureTheory.Measure.le_iff.mpr; intro A' hA'
          rw [MeasureTheory.Measure.bind_apply hA' measurable_from_top.aemeasurable,
              MeasureTheory.Measure.bind_apply hA' measurable_from_top.aemeasurable]
          exact MeasureTheory.lintegral_mono' (hf.monotone (c.monotone hnm) st)
            (fun r => MeasureTheory.Measure.le_iff.mp (hg.monotone (c.monotone hnm) r.1 r.2) A' hA'))
          A hA]
    simp_rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
    -- Goal: ∫⁻ r, (g (ωSup c) r.1 r.2).1 A ∂(f (ωSup c) st).1 = ⨆ n, ∫⁻ r, (g (c n) r.1 r.2).1 A ∂(f (c n) st).1
    have hf_eq : (f (OmegaCompletePartialOrder.ωSup c) st).1 = ⨆ n, (f (c n) st).1 :=
      congr_arg Subtype.val (congr_fun (hf.map_ωSup c) st)
    have hg_meas : ∀ r : b × s, (g (OmegaCompletePartialOrder.ωSup c) r.1 r.2).1 =
        ⨆ n, (g (c n) r.1 r.2).1 :=
      fun r => congr_arg Subtype.val (congr_fun (congr_fun (hg.map_ωSup c) r.1) r.2)
    have hg_eq_A : ∀ r : b × s, (g (OmegaCompletePartialOrder.ωSup c) r.1 r.2).1 A =
        ⨆ n, (g (c n) r.1 r.2).1 A := fun r => by
      rw [hg_meas r]
      exact measure_iSup_apply _ (fun n m hnm => hg.monotone (c.monotone hnm) r.1 r.2) A hA
    rw [hf_eq]; simp_rw [hg_eq_A]
    sorry -- Proof below here broke
    -- rw [lintegral_iSup_measure_nat (fun n m hnm => hf.monotone (c.monotone hnm) st)]
    -- simp_rw [MeasureTheory.lintegral_iSup (fun m => measurable_from_top)
    --   (fun m₁ m₂ hm₁m₂ r => MeasureTheory.Measure.le_iff.mp
    --     (hg.monotone (c.monotone hm₁m₂) r.1 r.2) A hA)]
    -- -- Diagonal: ⨆ n, ⨆ m, h n m = ⨆ n, h n n for jointly monotone h
    -- apply le_antisymm
    -- · exact iSup_le fun n => iSup_le fun m =>
    --     (MeasureTheory.lintegral_mono' (hf.monotone (c.monotone (le_max_left n m)) st)
    --       (fun r => MeasureTheory.Measure.le_iff.mp
    --         (hg.monotone (c.monotone (le_max_right n m)) r.1 r.2) A hA)).trans
    --       (le_iSup _ (max n m))
    -- · exact iSup_le fun n => (le_iSup _ n).trans (le_iSup _ n)

-- @[fun_prop]
-- theorem ite_ωScottContinuous
--   [OmegaCompletePartialOrder a]
--   (f : a → Program s b) (g : a → Program s b) (cond)
--   [Decidable cond]
--   (hg : OmegaCompletePartialOrder.ωScottContinuous g) (hf : OmegaCompletePartialOrder.ωScottContinuous f) :
--   OmegaCompletePartialOrder.ωScottContinuous fun x => if cond then f x else g x := by
--   split_ifs
--   · exact hf
--   · exact hg

noncomputable
def while_iteration (cond : Program s Bool) (body : Program s Unit) : Program s Unit →𝒄 Program s Unit :=
  OmegaCompletePartialOrder.ContinuousHom.ofFun fun (fp : Program s Unit) =>
    do
      if ← cond then
        body
        fp
      else
        return ()

noncomputable
def while_loop (cond : Program s Bool) (body : Program s Unit) : Program s Unit :=
  (while_iteration cond body).lfp

theorem while_unroll (cond : Program s Bool) (body : Program s Unit):
  while_loop cond body = do
      if ← cond then
        body
        while_loop cond body
      else
        return () := by calc
  _ = while_iteration cond body (while_loop cond body) := by
    sorry
  _ = _ := rfl
