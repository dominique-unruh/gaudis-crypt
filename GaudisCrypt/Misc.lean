/-

Various mathematical things that we use.
Maybe some should be in mathlib.

-/
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Order.OmegaCompletePartialOrder

def OmegaCompletePartialOrder.ContinuousHom.lfp [OmegaCompletePartialOrder a] [OrderBot a]
    (f : a →𝒄 a) :=
  have prf := Monotone.monotone_iterate_of_le_map f.monotone (OrderBot.bot_le _)
  OmegaCompletePartialOrder.ωSup ⟨fun n => f^[n] ⊥, prf⟩

def IsLfp [LE a] (f : a -> a) (x : a) := IsLeast (Function.fixedPoints f) x

theorem ContinuousHom.lfp_isLfp [OmegaCompletePartialOrder a] [OrderBot a] (f : a →𝒄 a) :
    IsLfp f (f.lfp) := by
  let chain : OmegaCompletePartialOrder.Chain a :=
    ⟨fun n => f^[n] ⊥,
      Monotone.monotone_iterate_of_le_map f.monotone (OrderBot.bot_le _)⟩
  have hlfp : f.lfp = OmegaCompletePartialOrder.ωSup chain := rfl
  refine ⟨?_, ?_⟩
  · -- f.lfp is a fixed point of f.
    change f f.lfp = f.lfp
    rw [hlfp]
    have hmap : f (OmegaCompletePartialOrder.ωSup chain) =
                OmegaCompletePartialOrder.ωSup (chain.map f.toOrderHom) :=
      f.map_ωSup' chain
    rw [hmap]
    -- ωSup (chain.map f.toOrderHom) = ωSup chain (cofinal shift by 1)
    apply le_antisymm
    · apply OmegaCompletePartialOrder.ωSup_le
      intro n
      have hshift : (chain.map f.toOrderHom) n = chain (n+1) := by
        change f (f^[n] (⊥ : a)) = f^[n+1] ⊥
        rw [Function.iterate_succ_apply']
      rw [hshift]
      exact OmegaCompletePartialOrder.le_ωSup chain (n+1)
    · apply OmegaCompletePartialOrder.ωSup_le
      intro n
      calc chain n
          ≤ chain (n+1) := chain.monotone (Nat.le_succ n)
        _ = (chain.map f.toOrderHom) n := by
            change f^[n+1] (⊥ : a) = f (f^[n] ⊥)
            rw [Function.iterate_succ_apply']
        _ ≤ OmegaCompletePartialOrder.ωSup (chain.map f.toOrderHom) :=
            OmegaCompletePartialOrder.le_ωSup _ n
  · -- f.lfp is below every fixed point.
    intro y hy
    rw [hlfp]
    apply OmegaCompletePartialOrder.ωSup_le
    intro n
    change f^[n] (⊥ : a) ≤ y
    induction n with
    | zero => exact bot_le
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc f (f^[k] ⊥) ≤ f y := f.monotone ih
        f y = y := hy


theorem ContinuousHom.map_lfp_comp [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
      [OrderBot α] [OrderBot β] (f : β →𝒄 α) (g : α →𝒄 β) :
  f (g.comp f).lfp = (f.comp g).lfp := by
  apply le_antisymm
  · have h : (g.comp f).lfp ≤ g (f.comp g).lfp :=
      (ContinuousHom.lfp_isLfp (g.comp f)).2
        (congr_arg g (ContinuousHom.lfp_isLfp (f.comp g)).1)
    calc f (g.comp f).lfp
        ≤ f (g (f.comp g).lfp) := f.monotone h
      _ = (f.comp g).lfp := (ContinuousHom.lfp_isLfp (f.comp g)).1
  · exact (ContinuousHom.lfp_isLfp (f.comp g)).2
        (congr_arg f (ContinuousHom.lfp_isLfp (g.comp f)).1)

@[simp]
theorem ContinuousHom.map_lfp [OmegaCompletePartialOrder a] [OrderBot a] (f: a →𝒄 a) :
   f f.lfp = f.lfp :=
  (ContinuousHom.lfp_isLfp f).1


-- MCT for a monotone sequence of measures: ∫⁻ f d(⨆ μ_n) = ⨆ n, ∫⁻ f dμ_n.
theorem lintegral_iSup_measure_nat {α : Type*} [MeasurableSpace α]
    {μ : ℕ → MeasureTheory.Measure α} (hmono : Monotone μ) {f : α → ENNReal} :
    ∫⁻ a, f a ∂(⨆ n, μ n) = ⨆ n, ∫⁻ a, f a ∂μ n := by
  -- Step 1: (⨆ n, μ n) s = ⨆ n, μ n s for measurable s,
  -- proved by constructing the colimit measure ν with ν t = ⨆ n, μ n t.
  have measure_iSup_apply : ∀ s, MeasurableSet s → (⨆ n, μ n) s = ⨆ n, μ n s := fun s hs => by
    -- σ-additivity of ν uses: ⨆ n, ∑' i, g n i = ∑' i, ⨆ n, g n i (monotone g).
    -- Proof via ENNReal.tsum_eq_iSup_sum + iSup_comm + finsetSum_iSup_of_monotone.
    let ν : MeasureTheory.Measure α := MeasureTheory.Measure.ofMeasurable
        (fun t _ => ⨆ n, μ n t) (by simp)
        (fun sets hsets hdisj => by
          simp_rw [MeasureTheory.measure_iUnion hdisj hsets, ENNReal.tsum_eq_iSup_sum]
          rw [iSup_comm]
          congr 1; ext S
          exact (ENNReal.finsetSum_iSup_of_monotone fun i m n hmn =>
            MeasureTheory.Measure.le_iff.mp (hmono hmn) (sets i) (hsets i)).symm)
    have hν : ν = ⨆ n, μ n := le_antisymm
      (MeasureTheory.Measure.le_iff.mpr fun t ht => by
        have heq : ν t = ⨆ n, μ n t := MeasureTheory.Measure.ofMeasurable_apply t ht
        rw [heq]
        exact iSup_le fun n => MeasureTheory.Measure.le_iff.mp (le_iSup μ n) t ht)
      (iSup_le fun n => MeasureTheory.Measure.le_iff.mpr fun t ht => by
        have heq : ν t = ⨆ n, μ n t := MeasureTheory.Measure.ofMeasurable_apply t ht
        rw [heq]
        exact le_iSup (μ · t) n)
    rw [← hν]; exact MeasureTheory.Measure.ofMeasurable_apply s hs
  -- Step 2: g.lintegral (⨆ n, μ n) = ⨆ n, g.lintegral (μ n) for simple g.
  -- Proof: unfold lintegral = ∑ r * μ(preimage), swap mul/iSup, swap sum/iSup.
  have simp_lintegral_iSup : ∀ (g : MeasureTheory.SimpleFunc α ENNReal),
      g.lintegral (⨆ n, μ n) = ⨆ n, g.lintegral (μ n) := fun g => by
    simp only [MeasureTheory.SimpleFunc.lintegral,
      measure_iSup_apply _ (g.measurableSet_preimage _), ENNReal.mul_iSup]
    exact ENNReal.finsetSum_iSup_of_monotone fun r m n hmn =>
      mul_le_mul_right
        (MeasureTheory.Measure.le_iff.mp (hmono hmn) (g ⁻¹' {r}) (g.measurableSet_preimage _)) r
  apply le_antisymm
  · -- ≤: unfold lintegral as sup over simple functions, use simp_lintegral_iSup
    rw [MeasureTheory.lintegral]
    apply iSup₂_le; intro g hg
    rw [simp_lintegral_iSup]
    apply iSup_le; intro n
    calc g.lintegral (μ n)
        = ∫⁻ a, g a ∂μ n := (g.lintegral_eq_lintegral _).symm
      _ ≤ ∫⁻ a, f a ∂μ n := MeasureTheory.lintegral_mono hg
      _ ≤ ⨆ n, ∫⁻ a, f a ∂μ n := le_iSup (fun n => ∫⁻ a, f a ∂μ n) n
  · -- ≥: each μ n ≤ ⨆ n, μ n so lintegral is monotone
    exact iSup_le fun n => MeasureTheory.lintegral_mono' (le_iSup μ n) le_rfl


@[fun_prop]
theorem Bool.rec_ωScottContinuous
    {X : Type*} [OmegaCompletePartialOrder X]
    {α : Bool → Type*} [∀ b, OmegaCompletePartialOrder (α b)]
    (a : Bool) {g : X → α false} {f : X → α true}
    (hg : OmegaCompletePartialOrder.ωScottContinuous g)
    (hf : OmegaCompletePartialOrder.ωScottContinuous f) :
    OmegaCompletePartialOrder.ωScottContinuous
      (fun x => Bool.rec (motive := α) (g x) (f x) a) := by
  cases a <;> [exact hg; exact hf]

@[fun_prop]
theorem ite_ωScottContinuous
  [OmegaCompletePartialOrder a] [OmegaCompletePartialOrder b]
  (f : a → b) (g : a → b) (cond)
  [Decidable cond]
  (hg : OmegaCompletePartialOrder.ωScottContinuous g) (hf : OmegaCompletePartialOrder.ωScottContinuous f) :
  OmegaCompletePartialOrder.ωScottContinuous fun x => if cond then f x else g x := by
  split_ifs
  · exact hf
  · exact hg

attribute [fun_prop] Monotone

@[fun_prop]
theorem Bool.rec_monotone
    {X : Type*} [Preorder X]
    {α : Bool → Type*} [∀ b, Preorder (α b)]
    (a : Bool) {g : X → α false} {f : X → α true}
    (hg : Monotone g) (hf : Monotone f) :
    Monotone (fun x => Bool.rec (motive := α) (g x) (f x) a) := by
  cases a <;> [exact hg; exact hf]

def OrderHom.ofFun [Preorder α] [Preorder β] (f : α → β) (hf : Monotone f := by fun_prop) : α →o β where
  toFun := f
  monotone' := hf

attribute [fun_prop] monotone_const
attribute [fun_prop] monotone_id

@[fun_prop]
theorem monotone_pi_apply [Preorder β] (i : α) : Monotone (fun f : α → β => f i) :=
  fun _ _ h => h i

@[fun_prop]
theorem monotone_pi {X : Type*} {ι : Type*} {A : ι → Type*} [Preorder X] [∀ (i : ι), Preorder (A i)]
   {f : X → (i : ι) → A i} (h : ∀ (i : ι), Monotone fun (a : X) => f a i) :
  Monotone f :=
  fun _ _ hx i => h i hx

@[fun_prop]
theorem monotone_ite (f : a → b) (g : a → b) [Preorder a] [Preorder b] c [Decidable c]
    (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x ↦ if c then f x else g x := by
  split_ifs
  · exact hf
  · exact hg

@[fun_prop]
lemma monotone_comp [Preorder a] [Preorder b] [Preorder c] {f : a → b} {g : c → a} :
  Monotone f → Monotone g → Monotone fun x ↦ f (g x) :=
  fun hf hg _ _ hx => hf (hg hx)

@[fun_prop]
theorem OrderHom.monotone_mk [Preorder a] [Preorder b] [Preorder c]
    {f : a → b → c} (hinner : ∀ x, Monotone (f x))
    (hmono : ∀ v, Monotone (fun x => f x v)) :
    Monotone (fun x => (⟨f x, hinner x⟩ : b →o c)) :=
  fun _ _ hx v => hmono v hx

@[fun_prop]
theorem monotone_fst' [Preorder X] [Preorder Y] [Preorder Z] (f : X → Y × Z) (hf : Monotone f) :
    Monotone (fun x ↦ (f x).fst) :=
  fun _ _ hx => (hf hx).1

@[fun_prop]
theorem monotone_snd' [Preorder X] [Preorder Y] [Preorder Z] (f : X → Y × Z) (hf : Monotone f) :
    Monotone (fun x ↦ (f x).snd) :=
  fun _ _ hx => (hf hx).2

@[fun_prop]
theorem monotone_prod_mk [Preorder X] [Preorder Y] [Preorder Z] (f : X → Y) (g : X → Z)
    (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun x ↦ (f x, g x)) :=
  fun _ _ hx => ⟨hf hx, hg hx⟩

@[fun_prop]
theorem monotone_ContinuousHom [OmegaCompletePartialOrder a] [OmegaCompletePartialOrder b]
  (f : a →𝒄 b) : Monotone (fun x ↦ f x) := f.monotone

@[fun_prop]
theorem monotone_OrderHom_apply [Preorder a] [Preorder b] [Preorder c]
    {f : a → b →o c} (hf : Monotone f) {g : a → b} (hg : Monotone g) :
    Monotone (fun x ↦ f x (g x)) :=
  fun _ _ hx => ((f _).monotone (hg hx)).trans (hf hx _)

@[fun_prop]
theorem OrderHom.lfp_monotone [CompleteLattice c] :
    Monotone (OrderHom.lfp : (c →o c) → c) :=
  fun f g hfg => f.lfp_le (hfg g.lfp |>.trans g.map_lfp.le)

/-- Sum of a 0/1 indicator over a finite type equals the size of the indicated set. -/
lemma sum_indicator_eq_card_ENNReal {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) :
    ∑ y : α, (if y ∈ S then (1 : ENNReal) else 0) = (S.card : ENNReal) := by
  rw [← Finset.sum_filter]
  rw [show (Finset.univ : Finset α).filter (· ∈ S) = S from by ext; simp]
  simp [Finset.sum_const]

/-- `((n + 1 : ℕ) : ENNReal) - 1 = (n : ENNReal)` — the standard ℕ-cast
    successor cancellation in `ENNReal` (with truncated subtraction). Used
    pervasively in birthday-bound arithmetic. -/
lemma ENNReal.natCast_succ_sub_one (n : ℕ) :
    ((n + 1 : ℕ) : ENNReal) - 1 = (n : ENNReal) := by
  push_cast
  exact ENNReal.add_sub_cancel_right (by norm_num)

