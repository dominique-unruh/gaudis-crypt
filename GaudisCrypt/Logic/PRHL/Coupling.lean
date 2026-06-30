import GaudisCrypt.Logic.PRHL.Core
import GaudisCrypt.ProgramRange

namespace GaudisCrypt.Language.Semantics

/-!
# Coupling introduction for `relE` (the symmetric proof principle)

A `relE` judgment is two `rel` directions, and for asymmetric coupling
relations the two directions are not logically interderivable — proving
them separately duplicates the whole case analysis (the "mirror tax"
measured in the up-to-bad client).

This module provides the missing *symmetric introduction form*: an
explicit coupling witness — a joint subdistribution over output pairs
whose marginals are the two runs and whose support lies in the post —
yields **both** directions at once (`ProgramDenotation.relE.of_coupling`). This is
the CertiCrypt/FCF lifting, deliberately confined to its sweet spot:

* **leaves** are proved by exhibiting a coupling (`Coupling.of_pure` for
  deterministic steps, `Coupling.of_uniform` for synchronized sampling —
  the closed wp forms required as inputs are exactly what the `wp`-style
  proofs compute anyway, now stated once instead of once per direction);
* **composition** stays with the wp-lifting rules (`relE.bind`,
  `relE.loop_n`, …), which need no couplings, no measurability, and no
  choice principles.
-/

/-- A coupling witness for the runs `p` from `σ₁` and `q` from `σ₂`: a joint
    subdistribution on output pairs with the two runs as marginals and
    support inside `Post` (stated in CertiCrypt's `range` form, which needs
    no decidability). -/
structure ProgramDenotation.Coupling {s₁ s₂ α β : Type}
    (p : ProgramDenotation s₁ α) (q : ProgramDenotation s₂ β) (σ₁ : s₁) (σ₂ : s₂)
    (Post : α × s₁ → β × s₂ → Prop) where
  /-- The joint subdistribution. -/
  w : SubProbability ((α × s₁) × (β × s₂))
  /-- Left marginal: integrating a left-post recovers `p`'s run. -/
  marg₁ : ∀ F : α × s₁ → ENNReal, w.expected (fun uv => F uv.1) = p.wp F σ₁
  /-- Right marginal. -/
  marg₂ : ∀ G : β × s₂ → ENNReal, w.expected (fun uv => G uv.2) = q.wp G σ₂
  /-- Support condition: any function vanishing on `Post` integrates to 0. -/
  supp : ∀ f : (α × s₁) × (β × s₂) → ENNReal,
    (∀ uv, Post uv.1 uv.2 → f uv = 0) → w.expected f = 0

/-! ## Expected-value helpers -/

lemma SubProbability.expected_mono_pt {γ : Type} (μ : SubProbability γ)
    {f g : γ → ENNReal} (h : ∀ x, f x ≤ g x) :
    μ.expected f ≤ μ.expected g := by
  letI : MeasurableSpace γ := ⊤
  exact MeasureTheory.lintegral_mono h

lemma SubProbability.expected_add {γ : Type} (μ : SubProbability γ)
    (f g : γ → ENNReal) :
    μ.expected (fun x => f x + g x) = μ.expected f + μ.expected g := by
  letI : MeasurableSpace γ := ⊤
  exact MeasureTheory.lintegral_add_left measurable_from_top g

/-- Expected value of the constant-zero post. -/
lemma SubProbability.expected_zero {γ : Type} (μ : SubProbability γ) :
    μ.expected (fun _ => (0 : ENNReal)) = 0 := by
  letI : MeasurableSpace γ := ⊤
  exact MeasureTheory.lintegral_zero

/-- Expected value over the zero subdistribution. -/
lemma SubProbability.expected_bot {γ : Type} (f : γ → ENNReal) :
    (⊥ : SubProbability γ).expected f = 0 := by
  letI : MeasurableSpace γ := ⊤
  exact MeasureTheory.lintegral_zero_measure f

/-- Pointwise congruence for `expected`. -/
lemma SubProbability.expected_congr {γ : Type} (μ : SubProbability γ)
    {f g : γ → ENNReal} (h : ∀ x, f x = g x) :
    μ.expected f = μ.expected g := by
  rw [funext h]

/-- Collapse a constant average. -/
lemma sum_const_div_card {T : Type} [Fintype T] [Nonempty T] (c : ENNReal) :
    (∑ _t : T, c / Fintype.card T) = c := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ENNReal.mul_div_cancel
        (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card T ≠ 0))
        (ENNReal.natCast_ne_top _)]

namespace ProgramDenotation.Coupling

variable {s₁ s₂ α β : Type}
    {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β} {σ₁ : s₁} {σ₂ : s₂}
    {Post : α × s₁ → β × s₂ → Prop}

/-- Domination through the witness: a `Post`-pointwise inequality between
    pair-posts integrates. -/
lemma expected_le (c : ProgramDenotation.Coupling p q σ₁ σ₂ Post)
    {A B : (α × s₁) × (β × s₂) → ENNReal}
    (hAB : ∀ uv, Post uv.1 uv.2 → A uv ≤ B uv) :
    c.w.expected A ≤ c.w.expected B := by
  classical
  calc c.w.expected A
      ≤ c.w.expected (fun uv => B uv + (if Post uv.1 uv.2 then 0 else ⊤)) := by
        apply SubProbability.expected_mono_pt
        intro uv
        by_cases hP : Post uv.1 uv.2
        · simpa [hP] using hAB uv hP
        · simp [hP]
    _ = c.w.expected B
        + c.w.expected (fun uv => if Post uv.1 uv.2 then 0 else ⊤) :=
        SubProbability.expected_add _ _ _
    _ = c.w.expected B := by
        rw [c.supp _ (fun uv hP => if_pos hP), add_zero]

/-- **Deterministic coupling**: both runs are point masses on a
    `Post`-related pair of outputs. -/
noncomputable def of_pure (u₀ : α × s₁) (v₀ : β × s₂)
    (h₁ : ∀ F, p.wp F σ₁ = F u₀) (h₂ : ∀ G, q.wp G σ₂ = G v₀)
    (hP : Post u₀ v₀) : ProgramDenotation.Coupling p q σ₁ σ₂ Post where
  w := pure (u₀, v₀)
  marg₁ F := by rw [expected_pure, h₁]
  marg₂ G := by rw [expected_pure, h₂]
  supp f hf := by rw [expected_pure]; exact hf _ hP

/-- **Sampling coupling along a shared index** (the `rnd` rule with an
    explicit branch matching): both runs are uniform averages over `T`,
    coupled branch-by-branch. -/
noncomputable def of_uniform {T : Type} [Fintype T] [Nonempty T]
    (f₁ : T → α × s₁) (f₂ : T → β × s₂)
    (h₁ : ∀ F, p.wp F σ₁ = ∑ t : T, F (f₁ t) / Fintype.card T)
    (h₂ : ∀ G, q.wp G σ₂ = ∑ t : T, G (f₂ t) / Fintype.card T)
    (hP : ∀ t, Post (f₁ t) (f₂ t)) : ProgramDenotation.Coupling p q σ₁ σ₂ Post where
  w := (SubProbability.uniform : SubProbability T) >>= fun t => pure (f₁ t, f₂ t)
  marg₁ F := by
    rw [SubProbability.expected_bind]
    refine Eq.trans (SubProbability.expected_congr _
      (g := fun t : T => F (f₁ t)) (fun t => ?_)) ?_
    · change ((pure (f₁ t, f₂ t) : SubProbability ((α × s₁) × (β × s₂))).expected
        (fun uv => F uv.1)) = F (f₁ t)
      rw [expected_pure]
    · rw [uniform_expected]
      exact (h₁ F).symm
  marg₂ G := by
    rw [SubProbability.expected_bind]
    refine Eq.trans (SubProbability.expected_congr _
      (g := fun t : T => G (f₂ t)) (fun t => ?_)) ?_
    · change ((pure (f₁ t, f₂ t) : SubProbability ((α × s₁) × (β × s₂))).expected
        (fun uv => G uv.2)) = G (f₂ t)
      rw [expected_pure]
    · rw [uniform_expected]
      exact (h₂ G).symm
  supp f hf := by
    rw [SubProbability.expected_bind]
    refine Eq.trans (SubProbability.expected_congr _
      (g := fun _ : T => (0 : ENNReal)) (fun t => ?_)) ?_
    · change ((pure (f₁ t, f₂ t) : SubProbability ((α × s₁) × (β × s₂))).expected f)
        = 0
      rw [expected_pure]
      exact hf _ (hP t)
    · rw [uniform_expected]
      simp

end ProgramDenotation.Coupling

/-- **Coupling introduction** (the symmetric proof principle): a coupling
    witness at every `Pre`-related state pair yields the full two-sided
    `relE` judgment — both directions from the same witness. -/
lemma ProgramDenotation.relE.of_coupling {s₁ s₂ α β : Type}
    {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : ∀ σ₁ σ₂, Pre σ₁ σ₂ → ProgramDenotation.Coupling p q σ₁ σ₂ Post) :
    p.relE q Pre Post := by
  constructor
  · intro F G hFG σ₁ σ₂ hpre
    have c := h σ₁ σ₂ hpre
    calc p.wp F σ₁ = c.w.expected (fun uv => F uv.1) := (c.marg₁ F).symm
      _ ≤ c.w.expected (fun uv => G uv.2) :=
          c.expected_le (fun uv hP => hFG _ _ hP)
      _ = q.wp G σ₂ := c.marg₂ G
  · intro F G hFG σ₂ σ₁ hpre
    have c := h σ₁ σ₂ hpre
    calc q.wp F σ₂ = c.w.expected (fun uv => F uv.2) := (c.marg₂ F).symm
      _ ≤ c.w.expected (fun uv => G uv.1) :=
          c.expected_le (fun uv hP => hFG _ _ hP)
      _ = p.wp G σ₁ := c.marg₁ G

end GaudisCrypt.Language.Semantics
