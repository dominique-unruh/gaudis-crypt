import GaudisCrypt.Logic.PRHL.Prhl

open GaudisCrypt.Language.Lens

namespace GaudisCrypt.Language.Semantics

/-!
# pRHL, version 2 — the literal explicit-coupling judgment

This module develops the candidate pRHL definition from `CLAUDE.md`
subtask 3 in its **most literal form** and shows it delivers the same rule
set as the existing `Program.prhl` (`PRHL/Prhl.lean`).

## The difference from `Program.prhl`

`Program.prhl` packages the coupling existential inside the `Program.Coupling`
*structure*, whose marginals are stated in **expected-value** form
(`∀ F, μ.expected (F ∘ fst) = c.wp F σ₁`) and whose support uses the
**range** form (`∀ f vanishing on B, ∫ f dμ = 0`).

`Program.prhl2` instead spells out the existential directly, exactly as in
the subtask-3 text:

```
prhl2 A c d B := ∀ σ₁ σ₂, A σ₁ σ₂ →
  ∃ μ, map fst μ = c σ₁ ∧ map snd μ = d σ₂ ∧ satisfy μ B
```

with the marginals as **distribution equality** (`map fst μ = c σ₁`,
written `μ >>= fun x => pure x.1 = c σ₁`) and the support as the **pointwise**
`SubProbability.satisfies` (`∀ x, μ {x} ≠ 0 → B x`).

## What this buys, and what it costs

The two formulations are interderivable, so `prhl2` inherits every rule:

* `Program.prhl.to_prhl2` (forward) is **unconditional** — the
  `Coupling.map_fst/map_snd` lemmas recover the distribution-equality
  marginals, and `satisfies_of_range` turns the range support into the
  pointwise one with no side conditions.
* `Program.prhl2.to_prhl` (backward) needs **`Countable`** on the joint
  type. This is the one real finding: the *pointwise* `satisfies` is only
  as strong as the range form when the integral is a countable sum of
  atoms (`range_of_satisfies`). So every `prhl2` rule that must *consume* a
  coupling — the eliminations (`to_relE`) and the seq rule (`bind`) —
  carries a discreteness hypothesis that the range-form `prhl` avoids. The
  introduction leaves (`pure`, `refl`, `uniform`) and the purely
  structural rules (`conseq`, `exists_pre`, `or_pre`) stay unconditional.

Everything in the crypto layer is over countable/finite carriers, so the
`Countable` hypotheses discharge automatically there.
-/

/-! ## The judgment -/

/-- **Literal coupling-based pRHL**: the subtask-3 existential, with
    marginals as distribution equality and support as the pointwise
    `SubProbability.satisfies`. -/
def Program.prhl2 {s₁ s₂ α β : Type} (A : s₁ → s₂ → Prop)
    (c : Program s₁ α) (d : Program s₂ β)
    (B : α × s₁ → β × s₂ → Prop) : Prop :=
  ∀ σ₁ σ₂, A σ₁ σ₂ →
    ∃ μ : SubProbability ((α × s₁) × (β × s₂)),
      (μ >>= fun x => (pure x.1 : SubProbability (α × s₁))) = c σ₁ ∧
      (μ >>= fun x => (pure x.2 : SubProbability (β × s₂))) = d σ₂ ∧
      μ.satisfies (fun x => B x.1 x.2)

/-- Pushforward of `expected` along a deterministic map: integrating `F`
    against `map g μ` is integrating `F ∘ g` against `μ`. The workhorse for
    manipulating the literal map-marginals. -/
lemma SubProbability.expected_map {γ δ : Type} (μ : SubProbability γ)
    (g : γ → δ) (F : δ → ENNReal) :
    (μ >>= fun x => (pure (g x) : SubProbability δ)).expected F
      = μ.expected (fun x => F (g x)) := by
  rw [SubProbability.expected_bind]
  exact SubProbability.expected_congr _ (fun x => by rw [expected_pure])

/-! ## Discrete disintegration toolkit (for `trans`)

Over countable carriers (the `⊤` σ-algebra) a `SubProbability` is determined
by its atom weights, and the integral is a countable sum of atoms. These
helpers let us build the glued coupling for transitivity as an explicit
atomic measure and reason about its marginals by `tsum` algebra. -/

/-- Integral as a countable sum of atoms. -/
lemma SubProbability.expected_eq_tsum {T : Type} [Countable T]
    (μ : SubProbability T) (F : T → ENNReal) :
    μ.expected F = ∑' t, F t * μ.1 {t} := by
  letI : MeasurableSpace T := ⊤
  haveI : MeasurableSingletonClass T := ⟨fun _ => trivial⟩
  exact MeasureTheory.lintegral_countable' F

/-- An atomic sub-probability built from a summable weight function. -/
noncomputable def SubProbability.ofWeights {T : Type} [Countable T]
    (w : T → ENNReal) (h : ∑' t, w t ≤ 1) : SubProbability T :=
  letI : MeasurableSpace T := ⊤
  ⟨MeasureTheory.Measure.sum (fun t => w t • MeasureTheory.Measure.dirac t), by
    rw [Set.top_eq_univ, MeasureTheory.Measure.sum_apply _ MeasurableSet.univ]
    simp only [MeasureTheory.Measure.smul_apply, MeasureTheory.measure_univ,
      smul_eq_mul, mul_one]
    exact h⟩

/-- The integral against an atomic measure is the weighted sum. -/
lemma SubProbability.ofWeights_expected {T : Type} [Countable T]
    (w : T → ENNReal) (h : ∑' t, w t ≤ 1) (F : T → ENNReal) :
    (SubProbability.ofWeights w h).expected F = ∑' t, F t * w t := by
  letI : MeasurableSpace T := ⊤
  haveI : MeasurableSingletonClass T := ⟨fun _ => trivial⟩
  show ∫⁻ x, F x ∂(MeasureTheory.Measure.sum _) = _
  rw [MeasureTheory.lintegral_sum_measure]
  refine tsum_congr (fun t => ?_)
  rw [MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_dirac]
  rw [smul_eq_mul, mul_comm]

/-- A left-marginal atom is the sum of the joint atoms over the fiber. -/
lemma SubProbability.marginal_fst_singleton {A B : Type} [Countable A] [Countable B]
    (μ : SubProbability (A × B)) (a : A) :
    (μ >>= fun w => (pure w.1 : SubProbability A)).1 {a} = ∑' b, μ.1 {(a, b)} := by
  letI : MeasurableSpace A := ⊤
  letI : MeasurableSpace B := ⊤
  letI : MeasurableSpace (A × B) := ⊤
  have hmap : (μ >>= fun w => (pure w.1 : SubProbability A)).1
      = MeasureTheory.Measure.map Prod.fst μ.1 :=
    MeasureTheory.Measure.bind_dirac_eq_map μ.1 measurable_from_top
  rw [hmap, MeasureTheory.Measure.map_apply measurable_from_top
        (MeasurableSet.singleton a)]
  have hset : Prod.fst ⁻¹' {a} = ⋃ b, {((a, b) : A × B)} := by
    ext ⟨x₁, x₂⟩; simp [eq_comm]
  rw [hset, MeasureTheory.measure_iUnion (fun b b' hbb' => by
        simp only [Set.disjoint_singleton, ne_eq, Prod.mk.injEq, not_and]
        exact fun _ => hbb')
      (fun _ => MeasurableSet.singleton _)]

/-- A right-marginal atom is the sum of the joint atoms over the fiber. -/
lemma SubProbability.marginal_snd_singleton {A B : Type} [Countable A] [Countable B]
    (μ : SubProbability (A × B)) (b : B) :
    (μ >>= fun w => (pure w.2 : SubProbability B)).1 {b} = ∑' a, μ.1 {(a, b)} := by
  letI : MeasurableSpace A := ⊤
  letI : MeasurableSpace B := ⊤
  letI : MeasurableSpace (A × B) := ⊤
  have hmap : (μ >>= fun w => (pure w.2 : SubProbability B)).1
      = MeasureTheory.Measure.map Prod.snd μ.1 :=
    MeasureTheory.Measure.bind_dirac_eq_map μ.1 measurable_from_top
  rw [hmap, MeasureTheory.Measure.map_apply measurable_from_top
        (MeasurableSet.singleton b)]
  have hset : Prod.snd ⁻¹' {b} = ⋃ a, {((a, b) : A × B)} := by
    ext ⟨x₁, x₂⟩; simp [eq_comm]
  rw [hset, MeasureTheory.measure_iUnion (fun a a' haa' => by
        simp only [Set.disjoint_singleton, ne_eq, Prod.mk.injEq, not_and]
        exact fun h => absurd h haa')
      (fun _ => MeasurableSet.singleton _)]

/-- The atom weights of a sub-probability sum to at most one. -/
lemma SubProbability.tsum_singleton_le_one {T : Type} [Countable T]
    (ν : SubProbability T) : ∑' t, ν.1 {t} ≤ 1 := by
  letI : MeasurableSpace T := ⊤
  haveI : MeasurableSingletonClass T := ⟨fun _ => trivial⟩
  rw [← MeasureTheory.measure_iUnion (fun a b hab => by
        simpa [Set.disjoint_singleton] using hab) (fun _ => MeasurableSet.singleton _)]
  calc ν.1 (⋃ t, {t}) ≤ ν.1 Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
    _ ≤ 1 := ν.2

/-! ### Bind algebra and fixed-point helpers (for `while_loop`) -/

/-- Bind of the zero sub-probability is zero. -/
lemma SubProbability.bot_bind {A C : Type} (f : A → SubProbability C) :
    (⊥ : SubProbability A) >>= f = ⊥ := by
  refine SubProbability.ext_of_expected (fun test => ?_)
  rw [SubProbability.expected_bind, SubProbability.expected_bot,
      SubProbability.expected_bot]

/-- Associativity of bind. -/
lemma SubProbability.bind_assoc' {A B C : Type} (μ : SubProbability A)
    (f : A → SubProbability B) (g : B → SubProbability C) :
    (μ >>= f) >>= g = μ >>= fun a => f a >>= g := by
  refine SubProbability.ext_of_expected (fun test => ?_)
  simp only [SubProbability.expected_bind]

/-- A bind whose continuation reads only the first coordinate factors through
    the first marginal. -/
lemma SubProbability.bind_fst_left {A B C : Type} (μ : SubProbability (A × B))
    (H : A → SubProbability C) :
    (μ >>= fun ab => H ab.1) = (μ >>= fun ab => (pure ab.1 : SubProbability A)) >>= H := by
  refine SubProbability.ext_of_expected (fun test => ?_)
  simp only [SubProbability.expected_bind, expected_pure]

/-- A bind whose continuation reads only the second coordinate factors through
    the second marginal. -/
lemma SubProbability.bind_snd_left {A B C : Type} (μ : SubProbability (A × B))
    (H : B → SubProbability C) :
    (μ >>= fun ab => H ab.2) = (μ >>= fun ab => (pure ab.2 : SubProbability B)) >>= H := by
  refine SubProbability.ext_of_expected (fun test => ?_)
  simp only [SubProbability.expected_bind, expected_pure]

/-- Two binds with continuations agreeing on the support are equal. -/
lemma SubProbability.bind_congr_support {A C : Type} [Countable A]
    (μ : SubProbability A) {F F' : A → SubProbability C}
    (h : ∀ a, μ.1 {a} ≠ 0 → F a = F' a) : μ >>= F = μ >>= F' := by
  refine SubProbability.ext_of_expected (fun test => ?_)
  rw [SubProbability.expected_bind, SubProbability.expected_bind,
      SubProbability.expected_eq_tsum, SubProbability.expected_eq_tsum]
  refine tsum_congr (fun a => ?_)
  by_cases ha : μ.1 {a} = 0
  · rw [ha, mul_zero, mul_zero]
  · rw [h a ha]

/-- The integral against a least fixed point is the supremum of the integrals
    against the Kleene iterates (monotone convergence). -/
lemma SubProbability.expected_lfp_eq_iSup {a : Type} {b : a → Type}
    (F : ((x : a) → SubProbability (b x)) →𝒄 ((x : a) → SubProbability (b x)))
    (y : a) (g : b y → ENNReal) :
    (F.lfp y).expected g = ⨆ n, (F^[n] ⊥ y).expected g := by
  simp only [SubProbability.expected]
  letI : MeasurableSpace (b y) := ⊤
  have hmono : Monotone fun n => (F^[n] ⊥ y).1 :=
    fun m n hmn => (Monotone.monotone_iterate_of_le_map F.monotone (OrderBot.bot_le _) hmn) y
  rw [show (F.lfp y).1 = ⨆ n, (F^[n] ⊥ y).1 from rfl, lintegral_iSup_measure_nat hmono]

/-- If every Kleene iterate is supported in `B`, so is the least fixed point. -/
lemma SubProbability.satisfies_lfp {a : Type} {b : a → Type} [∀ y, Countable (b y)]
    (F : ((x : a) → SubProbability (b x)) →𝒄 ((x : a) → SubProbability (b x)))
    (y : a) (B : b y → Prop) (h : ∀ n, (F^[n] ⊥ y).satisfies B) :
    (F.lfp y).satisfies B := by
  refine SubProbability.satisfies_of_range _ _ (fun f hf => ?_)
  rw [SubProbability.expected_lfp_eq_iSup]
  have hz : ∀ n, (F^[n] ⊥ y).expected f = 0 :=
    fun n => (F^[n] ⊥ y).range_of_satisfies B (h n) f hf
  simp [hz]

/-- The zero sub-probability is supported anywhere (vacuously). -/
lemma SubProbability.satisfies_bot {C : Type} (B : C → Prop) :
    (⊥ : SubProbability C).satisfies B := by
  intro y hy
  simp only [show (⊥ : SubProbability C).1 = 0 from rfl, MeasureTheory.Measure.coe_zero,
    Pi.zero_apply, ne_eq, not_true_eq_false] at hy

/-- A point mass is supported at its point. -/
lemma SubProbability.satisfies_pure {C : Type} (x : C) (B : C → Prop) (hB : B x) :
    (pure x : SubProbability C).satisfies B := by
  letI : MeasurableSpace C := ⊤
  haveI : MeasurableSingletonClass C := ⟨fun _ => trivial⟩
  intro y hy
  have hyx : y = x := by
    by_contra hne
    refine hy ?_
    show (MeasureTheory.Measure.dirac x) {y} = 0
    rw [MeasureTheory.Measure.dirac_apply' x (MeasurableSet.singleton y),
      Set.indicator_of_notMem (by simpa [eq_comm] using hne)]
  rwa [hyx]

/-- Support of a bind: if each fibre is supported in `B`, so is the bind. -/
lemma SubProbability.satisfies_bind {A C : Type} [Countable A] [Countable C]
    (μ : SubProbability A) {F : A → SubProbability C} {B : C → Prop}
    (h : ∀ a, μ.1 {a} ≠ 0 → (F a).satisfies B) : (μ >>= F).satisfies B := by
  refine SubProbability.satisfies_of_range _ _ (fun f hf => ?_)
  rw [SubProbability.expected_bind, SubProbability.expected_eq_tsum]
  refine ENNReal.tsum_eq_zero.mpr (fun a => ?_)
  by_cases ha : μ.1 {a} = 0
  · rw [ha, mul_zero]
  · rw [(F a).range_of_satisfies B (h a ha) f hf, zero_mul]

/-- Monotone convergence for the program `while_loop` (curried fixed point). -/
lemma expected_while_lfp_iSup {s : Type} (cond : Program s Bool) (body : Program s Unit)
    (σ : s) (G : Unit × s → ENNReal) :
    (while_loop cond body σ).expected G
      = ⨆ n, ((while_iteration cond body)^[n] ⊥ () σ).expected G := by
  simp only [SubProbability.expected]
  letI : MeasurableSpace (Unit × s) := ⊤
  have hmono : Monotone fun n => ((while_iteration cond body)^[n] ⊥ () σ).1 :=
    fun m n hmn =>
      ((Monotone.monotone_iterate_of_le_map (while_iteration cond body).monotone
        (OrderBot.bot_le _) hmn) ()) σ
  rw [show (while_loop cond body σ).1
        = ⨆ n, ((while_iteration cond body)^[n] ⊥ () σ).1 from rfl,
      lintegral_iSup_measure_nat hmono]

/-- Unfold one step of the `while_iteration` functional at a state. -/
lemma while_iteration_apply {s : Type} (cond : Program s Bool) (body : Program s Unit)
    (fp : Unit → Program s Unit) (σ : s) :
    while_iteration cond body fp () σ
      = cond σ >>= fun bσ =>
          if bσ.1 then body bσ.2 >>= fun uσ => fp () uσ.2
          else pure ((), bσ.2) := by
  show cond σ >>= (fun bσ =>
      (if bσ.1 then (body >>= fun _ => fp ()) else (pure () : Program s Unit)) bσ.2) = _
  congr 1
  funext bσ
  split_ifs with h <;> rfl

/-! ## Bridges to `Program.prhl` -/

/-- **Forward bridge** (unconditional): the structure-packaged judgment
    yields the literal one. Marginals come from `Coupling.map_fst/map_snd`;
    the pointwise support comes from the range support via
    `satisfies_of_range`. -/
theorem Program.prhl.to_prhl2 {s₁ s₂ α β : Type} {A : s₁ → s₂ → Prop}
    {c : Program s₁ α} {d : Program s₂ β} {B : α × s₁ → β × s₂ → Prop}
    (h : Program.prhl A c d B) : Program.prhl2 A c d B := by
  intro σ₁ σ₂ hA
  obtain ⟨μ⟩ := h σ₁ σ₂ hA
  exact ⟨μ.w, μ.map_fst, μ.map_snd,
    μ.w.satisfies_of_range (fun x => B x.1 x.2) (fun f hf => μ.supp f hf)⟩

/-- **Backward bridge** (discrete): the literal judgment yields the
    structure-packaged one. The marginal equalities become the
    expected-value marginals by integrating both sides; the pointwise
    support becomes the range support via `range_of_satisfies`, which is
    where `Countable` is used. -/
theorem Program.prhl2.to_prhl {s₁ s₂ α β : Type}
    [Countable ((α × s₁) × (β × s₂))] {A : s₁ → s₂ → Prop}
    {c : Program s₁ α} {d : Program s₂ β} {B : α × s₁ → β × s₂ → Prop}
    (h : Program.prhl2 A c d B) : Program.prhl A c d B := by
  intro σ₁ σ₂ hA
  obtain ⟨μ, hm1, hm2, hsat⟩ := h σ₁ σ₂ hA
  refine ⟨{ w := μ, marg₁ := ?_, marg₂ := ?_, supp := ?_ }⟩
  · intro F
    show μ.expected (fun uv => F uv.1) = (c σ₁).expected F
    rw [← hm1, SubProbability.expected_bind]
    refine SubProbability.expected_congr _ (fun x => ?_)
    rw [expected_pure]
  · intro G
    show μ.expected (fun uv => G uv.2) = (d σ₂).expected G
    rw [← hm2, SubProbability.expected_bind]
    refine SubProbability.expected_congr _ (fun x => ?_)
    rw [expected_pure]
  · exact μ.range_of_satisfies (fun x => B x.1 x.2) hsat

/-- For discrete (countable) joint type the two formulations coincide. -/
theorem Program.prhl2_iff_prhl {s₁ s₂ α β : Type}
    [Countable ((α × s₁) × (β × s₂))] {A : s₁ → s₂ → Prop}
    {c : Program s₁ α} {d : Program s₂ β} {B : α × s₁ → β × s₂ → Prop} :
    Program.prhl2 A c d B ↔ Program.prhl A c d B :=
  ⟨Program.prhl2.to_prhl, Program.prhl.to_prhl2⟩

/-! ## Soundness with respect to the wp-lifting -/

/-- Every literal coupling judgment yields the two-sided wp-lifting
    judgment (discrete); all `relE` elimination forms transfer. -/
theorem Program.prhl2.to_relE {s₁ s₂ α β : Type}
    [Countable ((α × s₁) × (β × s₂))] {A : s₁ → s₂ → Prop}
    {c : Program s₁ α} {d : Program s₂ β} {B : α × s₁ → β × s₂ → Prop}
    (h : Program.prhl2 A c d B) : c.relE d A B :=
  h.to_prhl.to_relE

/-! ## Structural rules

The leaves and the purely structural rules are unconditional; the seq rule
inherits the discreteness hypothesis (see the module header). -/

namespace Program.prhl2

variable {s₁ s₂ α β : Type} {A : s₁ → s₂ → Prop}
    {B : α × s₁ → β × s₂ → Prop}

/-- Consequence — same witness, the support and precondition only weaken. -/
theorem conseq {c : Program s₁ α} {d : Program s₂ β}
    {A' : s₁ → s₂ → Prop} {B' : α × s₁ → β × s₂ → Prop}
    (h : Program.prhl2 A c d B)
    (hA : ∀ σ₁ σ₂, A' σ₁ σ₂ → A σ₁ σ₂)
    (hB : ∀ u v, B u v → B' u v) :
    Program.prhl2 A' c d B' := by
  intro σ₁ σ₂ hpre
  obtain ⟨μ, hm1, hm2, hsat⟩ := h σ₁ σ₂ (hA σ₁ σ₂ hpre)
  exact ⟨μ, hm1, hm2, fun x hx => hB _ _ (hsat x hx)⟩

/-- Two-sided `pure`. -/
theorem pure_pure {x₁ : α} {x₂ : β}
    (h : ∀ σ₁ σ₂, A σ₁ σ₂ → B (x₁, σ₁) (x₂, σ₂)) :
    Program.prhl2 A (pure x₁ : Program s₁ α) (pure x₂ : Program s₂ β) B :=
  (Program.prhl.pure_pure h).to_prhl2

/-- Reflexivity. -/
theorem refl {s γ : Type} (p : Program s γ) :
    Program.prhl2 Eq p p (fun u v : γ × s => u = v) :=
  (Program.prhl.refl p).to_prhl2

/-- The `rnd` rule: uniform samples coupled along a bijection. -/
theorem uniform {α' β' : Type} [Fintype α'] [Nonempty α'] [Fintype β'] [Nonempty β']
    (e : α' ≃ β') {B : α' × s₁ → β' × s₂ → Prop}
    (h : ∀ t σ₁ σ₂, A σ₁ σ₂ → B (t, σ₁) (e t, σ₂)) :
    Program.prhl2 A (Program.uniform : Program s₁ α')
      (Program.uniform : Program s₂ β') B :=
  (Program.prhl.uniform e h).to_prhl2

/-- Existential in the precondition. -/
theorem exists_pre {ι : Sort*} {A : ι → s₁ → s₂ → Prop}
    {c : Program s₁ α} {d : Program s₂ β}
    (h : ∀ i, Program.prhl2 (A i) c d B) :
    Program.prhl2 (fun σ₁ σ₂ => ∃ i, A i σ₁ σ₂) c d B :=
  fun σ₁ σ₂ hpre => hpre.elim fun i hi => h i σ₁ σ₂ hi

/-- Disjunction in the precondition. -/
theorem or_pre {A₁ A₂ : s₁ → s₂ → Prop}
    {c : Program s₁ α} {d : Program s₂ β}
    (h₁ : Program.prhl2 A₁ c d B) (h₂ : Program.prhl2 A₂ c d B) :
    Program.prhl2 (fun σ₁ σ₂ => A₁ σ₁ σ₂ ∨ A₂ σ₁ σ₂) c d B :=
  fun σ₁ σ₂ hpre => hpre.elim (h₁ σ₁ σ₂) (h₂ σ₁ σ₂)

/-- **The seq rule** (discrete). The composite coupling is built by
    `Program.prhl.bind`; the discreteness hypotheses are what let the
    pointwise-`satisfies` prefixes and continuations be reassembled. -/
theorem bind {s₁ s₂ α₁ α₂ β₁ β₂ : Type}
    [Countable ((α₁ × s₁) × (α₂ × s₂))] [Countable ((β₁ × s₁) × (β₂ × s₂))]
    {p₁ : Program s₁ α₁} {p₂ : Program s₂ α₂}
    {k₁ : α₁ → Program s₁ β₁} {k₂ : α₂ → Program s₂ β₂}
    {A : s₁ → s₂ → Prop} {M : α₁ × s₁ → α₂ × s₂ → Prop}
    {B : β₁ × s₁ → β₂ × s₂ → Prop}
    (h₁ : Program.prhl2 A p₁ p₂ M)
    (h₂ : ∀ x₁ x₂, Program.prhl2 (fun τ₁ τ₂ => M (x₁, τ₁) (x₂, τ₂))
      (k₁ x₁) (k₂ x₂) B) :
    Program.prhl2 A (p₁ >>= k₁) (p₂ >>= k₂) B :=
  (Program.prhl.bind h₁.to_prhl (fun x₁ x₂ => (h₂ x₁ x₂).to_prhl)).to_prhl2

/-- **Symmetry**: a coupling is inherently two-sided — swap the joint
    distribution coordinate-wise. Needs `Countable` because the pointwise
    `satisfies` is propagated through the swap map (via the range form). -/
theorem symm [Countable ((α × s₁) × (β × s₂))]
    {c : Program s₁ α} {d : Program s₂ β}
    (h : Program.prhl2 A c d B) :
    Program.prhl2 (fun σ₂ σ₁ => A σ₁ σ₂) d c (fun v u => B u v) := by
  intro σ₂ σ₁ hA
  obtain ⟨μ, hm1, hm2, hsat⟩ := h σ₁ σ₂ hA
  refine ⟨μ >>= fun x => pure (x.2, x.1), ?_, ?_, ?_⟩
  · refine SubProbability.ext_of_expected (fun F => ?_)
    rw [SubProbability.expected_map _ (fun y : (β × s₂) × (α × s₁) => y.1) F,
        SubProbability.expected_map _ (fun x : (α × s₁) × (β × s₂) => (x.2, x.1)),
        ← hm2, SubProbability.expected_map _ (fun x : (α × s₁) × (β × s₂) => x.2) F]
  · refine SubProbability.ext_of_expected (fun F => ?_)
    rw [SubProbability.expected_map _ (fun y : (β × s₂) × (α × s₁) => y.2) F,
        SubProbability.expected_map _ (fun x : (α × s₁) × (β × s₂) => (x.2, x.1)),
        ← hm1, SubProbability.expected_map _ (fun x : (α × s₁) × (β × s₂) => x.1) F]
  · refine SubProbability.satisfies_of_range _ _ (fun f hf => ?_)
    rw [SubProbability.expected_map _ (fun x : (α × s₁) × (β × s₂) => (x.2, x.1)) f]
    exact μ.range_of_satisfies (fun x => B x.1 x.2) hsat _
      (fun x hx => hf (x.2, x.1) hx)

/-- **Read coupling**: two `get`s relate when the read values (and unchanged
    states) satisfy the post. Unconditional leaf. -/
theorem get {γ₁ γ₂ : Type} (L₁ : Lens γ₁ s₁) (L₂ : Lens γ₂ s₂)
    {B : γ₁ × s₁ → γ₂ × s₂ → Prop}
    (h : ∀ σ₁ σ₂, A σ₁ σ₂ → B (L₁.get σ₁, σ₁) (L₂.get σ₂, σ₂)) :
    Program.prhl2 A (Program.get L₁) (Program.get L₂) B :=
  (show Program.prhl A (Program.get L₁) (Program.get L₂) B from
    fun σ₁ σ₂ hA => ⟨Program.Coupling.of_pure (L₁.get σ₁, σ₁) (L₂.get σ₂, σ₂)
      (fun F => by rw [wp_get]) (fun G => by rw [wp_get]) (h σ₁ σ₂ hA)⟩).to_prhl2

/-- **Write coupling**: two `set`s relate when the updated states satisfy the
    post. Unconditional leaf. -/
theorem set {γ₁ γ₂ : Type} (L₁ : Lens γ₁ s₁) (L₂ : Lens γ₂ s₂) (v₁ : γ₁) (v₂ : γ₂)
    {B : Unit × s₁ → Unit × s₂ → Prop}
    (h : ∀ σ₁ σ₂, A σ₁ σ₂ → B ((), L₁.set v₁ σ₁) ((), L₂.set v₂ σ₂)) :
    Program.prhl2 A (Program.set L₁ v₁) (Program.set L₂ v₂) B :=
  (show Program.prhl A (Program.set L₁ v₁) (Program.set L₂ v₂) B from
    fun σ₁ σ₂ hA => ⟨Program.Coupling.of_pure ((), L₁.set v₁ σ₁) ((), L₂.set v₂ σ₂)
      (fun F => by rw [wp_set]) (fun G => by rw [wp_set]) (h σ₁ σ₂ hA)⟩).to_prhl2

/-- **Bounded-loop congruence**: if the bodies preserve the invariant `Inv`
    relationally, so do their `n`-fold iterates. Proved by induction on `n`
    using `prhl2.bind`; covers the loops the crypto clients actually use
    (`oracle_loop_n`). The unbounded `while` fixed point stays open. -/
theorem loop_n [Countable ((Unit × s₁) × (Unit × s₂))]
    {body₁ : Program s₁ Unit} {body₂ : Program s₂ Unit}
    {Inv : s₁ → s₂ → Prop}
    (h : Program.prhl2 Inv body₁ body₂ (fun u v => Inv u.2 v.2))
    (n : ℕ) :
    Program.prhl2 Inv (loop_n n body₁) (loop_n n body₂)
      (fun u v => Inv u.2 v.2) := by
  induction n with
  | zero => exact Program.prhl2.pure_pure (fun _ _ hp => hp)
  | succ n ih => exact Program.prhl2.bind h (fun _ _ => ih)

/-- **Left footprint**: strengthen the post with a left-side fact `C` that
    holds almost surely for `c` (i.e. fails with probability 0). This is how
    `inRange`-style unary facts enter the coupling logic. Discrete (the
    support is rebalanced). -/
theorem strengthen_left [Countable ((α × s₁) × (β × s₂))]
    {c : Program s₁ α} {d : Program s₂ β} {C : α × s₁ → Prop} [DecidablePred C]
    (h : Program.prhl2 A c d B)
    (hC : ∀ σ₁ σ₂, A σ₁ σ₂ → c.wp (fun u => if C u then 0 else 1) σ₁ = 0) :
    Program.prhl2 A c d (fun u v => B u v ∧ C u) :=
  (show Program.prhl A c d (fun u v => B u v ∧ C u) from
    fun σ₁ σ₂ hA =>
      ⟨(h.to_prhl σ₁ σ₂ hA).some.strengthen_left (hC σ₁ σ₂ hA)⟩).to_prhl2

/-- **Right footprint**: the mirror of `strengthen_left`, obtained by
    symmetry. -/
theorem strengthen_right [Countable ((α × s₁) × (β × s₂))]
    [Countable ((β × s₂) × (α × s₁))]
    {c : Program s₁ α} {d : Program s₂ β} {C : β × s₂ → Prop} [DecidablePred C]
    (h : Program.prhl2 A c d B)
    (hC : ∀ σ₁ σ₂, A σ₁ σ₂ → d.wp (fun v => if C v then 0 else 1) σ₂ = 0) :
    Program.prhl2 A c d (fun u v => B u v ∧ C v) :=
  (h.symm.strengthen_left (C := C) (fun σ₂ σ₁ hA => hC σ₁ σ₂ hA)).symm

/-! ## Tier 2: one-sided/frame rules and rnd generalizations -/

/-- **Left frame**: a left-only prefix `p₀` matched against `skip` on the
    right (carrying `Pre` to `Mid`), then the continuations from `Mid`,
    gives `(p₀; k) ~ q`. Avoids inserting `pure () >>=` on the right by
    hand. Derived from `bind` + the monad law. -/
theorem prefix_left {β₁ β₂ : Type}
    [Countable ((Unit × s₁) × (Unit × s₂))] [Countable ((β₁ × s₁) × (β₂ × s₂))]
    {p₀ : Program s₁ Unit} {k : Program s₁ β₁} {q : Program s₂ β₂}
    {Pre Mid : s₁ → s₂ → Prop} {Post : β₁ × s₁ → β₂ × s₂ → Prop}
    (h₀ : Program.prhl2 Pre p₀ (pure ()) (fun u v => Mid u.2 v.2))
    (h : Program.prhl2 Mid k q Post) :
    Program.prhl2 Pre (p₀ >>= fun _ => k) q Post := by
  have hb := Program.prhl2.bind h₀ (fun _ _ => h)
  rwa [Program.pure_bind] at hb

/-- **Right frame**: the mirror of `prefix_left`. -/
theorem prefix_right {β₁ β₂ : Type}
    [Countable ((Unit × s₁) × (Unit × s₂))] [Countable ((β₁ × s₁) × (β₂ × s₂))]
    {p : Program s₁ β₁} {q₀ : Program s₂ Unit} {k : Program s₂ β₂}
    {Pre Mid : s₁ → s₂ → Prop} {Post : β₁ × s₁ → β₂ × s₂ → Prop}
    (h₀ : Program.prhl2 Pre (pure ()) q₀ (fun u v => Mid u.2 v.2))
    (h : Program.prhl2 Mid p k Post) :
    Program.prhl2 Pre p (q₀ >>= fun _ => k) Post := by
  have hb := Program.prhl2.bind h₀ (fun _ _ => h)
  rwa [Program.pure_bind] at hb

/-- **Left ghost write**: a left-only `set L v` matched against `skip`. The
    coupling analogue of `EquivModuloLens.set_equiv_pure`. Unconditional
    (both sides are point masses). -/
theorem set_skip_left {γ : Type} (L : Lens γ s₁) (v : γ)
    {B : Unit × s₁ → Unit × s₂ → Prop}
    (h : ∀ σ₁ σ₂, A σ₁ σ₂ → B ((), L.set v σ₁) ((), σ₂)) :
    Program.prhl2 A (Program.set L v) (pure ()) B :=
  (show Program.prhl A (Program.set L v) (pure () : Program s₂ Unit) B from
    fun σ₁ σ₂ hA => ⟨Program.Coupling.of_pure ((), L.set v σ₁) ((), σ₂)
      (fun F => by rw [wp_set]) (fun G => by rw [wp_pure]) (h σ₁ σ₂ hA)⟩).to_prhl2

/-- **Right ghost write**: the mirror of `set_skip_left`. -/
theorem set_skip_right {γ : Type} (L : Lens γ s₂) (v : γ)
    {B : Unit × s₁ → Unit × s₂ → Prop}
    (h : ∀ σ₁ σ₂, A σ₁ σ₂ → B ((), σ₁) ((), L.set v σ₂)) :
    Program.prhl2 A (pure ()) (Program.set L v) B :=
  (show Program.prhl A (pure () : Program s₁ Unit) (Program.set L v) B from
    fun σ₁ σ₂ hA => ⟨Program.Coupling.of_pure ((), σ₁) ((), L.set v σ₂)
      (fun F => by rw [wp_pure]) (fun G => by rw [wp_set]) (h σ₁ σ₂ hA)⟩).to_prhl2

/-- **Synchronized sampling** (`rnd` with the identity coupling): both runs
    draw the *same* uniform value. The common special case of `uniform`. -/
theorem uniform_id {α' : Type} [Fintype α'] [Nonempty α']
    {B : α' × s₁ → α' × s₂ → Prop}
    (h : ∀ t σ₁ σ₂, A σ₁ σ₂ → B (t, σ₁) (t, σ₂)) :
    Program.prhl2 A (Program.uniform : Program s₁ α')
      (Program.uniform : Program s₂ α') B :=
  Program.prhl2.uniform (Equiv.refl α') h

/-! ## Tier 3: transitivity by discrete disintegration -/

/-- **Transitivity**: compose a coupling of `(p, q)` with a coupling of
    `(q, r)` into a coupling of `(p, r)`, gluing along the shared middle
    marginal `q σ₂`. The glued weight is
    `ν{(x,z)} = ∑ₘ μ₁{(x,m)}·μ₂{(m,z)} / q{m}` — the discrete disintegration
    (independent given the middle), with the middle weights cancelling in
    each marginal. Needs `Countable` on all three carriers. -/
theorem trans {s₁ s₂ s₃ α β γ : Type}
    [Countable (α × s₁)] [Countable (β × s₂)] [Countable (γ × s₃)]
    {p : Program s₁ α} {q : Program s₂ β} {r : Program s₃ γ}
    {Pre₁ : s₁ → s₂ → Prop} {Post₁ : α × s₁ → β × s₂ → Prop}
    {Pre₂ : s₂ → s₃ → Prop} {Post₂ : β × s₂ → γ × s₃ → Prop}
    (h₁ : Program.prhl2 Pre₁ p q Post₁) (h₂ : Program.prhl2 Pre₂ q r Post₂) :
    Program.prhl2 (fun σ₁ σ₃ => ∃ σ₂, Pre₁ σ₁ σ₂ ∧ Pre₂ σ₂ σ₃) p r
      (fun x z => ∃ y, Post₁ x y ∧ Post₂ y z) := by
  rintro σ₁ σ₃ ⟨σ₂, hPre₁, hPre₂⟩
  obtain ⟨μ₁, hm1₁, hm2₁, hsat₁⟩ := h₁ σ₁ σ₂ hPre₁
  obtain ⟨μ₂, hm1₂, hm2₂, hsat₂⟩ := h₂ σ₂ σ₃ hPre₂
  -- Atom-level marginals.
  have hpσ : ∀ x, ∑' m, μ₁.1 {(x, m)} = (p σ₁).1 {x} :=
    fun x => by rw [← SubProbability.marginal_fst_singleton μ₁ x, hm1₁]
  have hq₁ : ∀ m, ∑' x, μ₁.1 {(x, m)} = (q σ₂).1 {m} :=
    fun m => by rw [← SubProbability.marginal_snd_singleton μ₁ m, hm2₁]
  have hq₂ : ∀ m, ∑' z, μ₂.1 {(m, z)} = (q σ₂).1 {m} :=
    fun m => by rw [← SubProbability.marginal_fst_singleton μ₂ m, hm1₂]
  have hrσ : ∀ z, ∑' m, μ₂.1 {(m, z)} = (r σ₃).1 {z} :=
    fun z => by rw [← SubProbability.marginal_snd_singleton μ₂ z, hm2₂]
  -- Atom domination by the middle weight, and middle weight ≤ 1.
  have haμ₁_le : ∀ x m, μ₁.1 {(x, m)} ≤ (q σ₂).1 {m} :=
    fun x m => by rw [← hq₁ m]; exact ENNReal.le_tsum x
  have haμ₂_le : ∀ m z, μ₂.1 {(m, z)} ≤ (q σ₂).1 {m} :=
    fun m z => by rw [← hq₂ m]; exact ENNReal.le_tsum z
  have hqm_le : ∀ m, (q σ₂).1 {m} ≤ 1 := fun m =>
    (MeasureTheory.measure_mono (Set.subset_univ _)).trans (q σ₂).2
  -- The cancellation `a / q * q = a` (with `q = 0 → a = 0`).
  have hcancel : ∀ a qv : ENNReal, (qv = 0 → a = 0) → qv ≤ 1 → a / qv * qv = a := by
    intro a qv hz hle
    by_cases h : qv = 0
    · simp [h, hz h]
    · exact ENNReal.div_mul_cancel h (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
  have hfac : ∀ a b c : ENNReal, a * b / c = a / c * b :=
    fun a b c => by rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  set wf : (α × s₁) × (γ × s₃) → ENNReal :=
    fun xz => ∑' m, μ₁.1 {(xz.1, m)} * μ₂.1 {(m, xz.2)} / (q σ₂).1 {m} with hwf
  -- Marginals of the glued weight.
  have hXmarg : ∀ x, ∑' z, wf (x, z) = (p σ₁).1 {x} := by
    intro x
    simp only [hwf]
    calc ∑' z, ∑' m, μ₁.1 {(x, m)} * μ₂.1 {(m, z)} / (q σ₂).1 {m}
        = ∑' m, ∑' z, μ₁.1 {(x, m)} * μ₂.1 {(m, z)} / (q σ₂).1 {m} := ENNReal.tsum_comm
      _ = ∑' m, μ₁.1 {(x, m)} / (q σ₂).1 {m} * ∑' z, μ₂.1 {(m, z)} := by
          refine tsum_congr (fun m => ?_)
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr (fun z => hfac _ _ _)
      _ = ∑' m, μ₁.1 {(x, m)} / (q σ₂).1 {m} * (q σ₂).1 {m} := by
          exact tsum_congr (fun m => by rw [hq₂ m])
      _ = ∑' m, μ₁.1 {(x, m)} := tsum_congr (fun m =>
          hcancel _ _ (fun h0 => le_zero_iff.mp (h0 ▸ haμ₁_le x m)) (hqm_le m))
      _ = (p σ₁).1 {x} := hpσ x
  have hZmarg : ∀ z, ∑' x, wf (x, z) = (r σ₃).1 {z} := by
    intro z
    simp only [hwf]
    calc ∑' x, ∑' m, μ₁.1 {(x, m)} * μ₂.1 {(m, z)} / (q σ₂).1 {m}
        = ∑' m, ∑' x, μ₁.1 {(x, m)} * μ₂.1 {(m, z)} / (q σ₂).1 {m} := ENNReal.tsum_comm
      _ = ∑' m, (∑' x, μ₁.1 {(x, m)}) * (μ₂.1 {(m, z)} / (q σ₂).1 {m}) := by
          refine tsum_congr (fun m => ?_)
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr (fun x => by rw [mul_div_assoc])
      _ = ∑' m, (q σ₂).1 {m} * (μ₂.1 {(m, z)} / (q σ₂).1 {m}) := by
          exact tsum_congr (fun m => by rw [hq₁ m])
      _ = ∑' m, μ₂.1 {(m, z)} := tsum_congr (fun m => by
          rw [mul_comm]
          exact hcancel _ _ (fun h0 => le_zero_iff.mp (h0 ▸ haμ₂_le m z)) (hqm_le m))
      _ = (r σ₃).1 {z} := hrσ z
  -- Total mass ≤ 1.
  have hmass : ∑' t, wf t ≤ 1 := by
    rw [ENNReal.tsum_prod']
    calc ∑' x, ∑' z, wf (x, z) = ∑' x, (p σ₁).1 {x} := tsum_congr hXmarg
      _ ≤ 1 := SubProbability.tsum_singleton_le_one (p σ₁)
  refine ⟨SubProbability.ofWeights wf hmass, ?_, ?_, ?_⟩
  · -- left marginal = p σ₁
    refine SubProbability.ext_of_expected (fun F => ?_)
    rw [SubProbability.expected_map, SubProbability.ofWeights_expected,
        SubProbability.expected_eq_tsum, ENNReal.tsum_prod']
    refine tsum_congr (fun x => ?_)
    dsimp only
    rw [ENNReal.tsum_mul_left, hXmarg]
  · -- right marginal = r σ₃
    refine SubProbability.ext_of_expected (fun F => ?_)
    rw [SubProbability.expected_map, SubProbability.ofWeights_expected,
        SubProbability.expected_eq_tsum, ENNReal.tsum_prod', ENNReal.tsum_comm]
    refine tsum_congr (fun z => ?_)
    dsimp only
    rw [ENNReal.tsum_mul_left, hZmarg]
  · -- support ⊆ composed post
    refine SubProbability.satisfies_of_range _ _ (fun f hf => ?_)
    rw [SubProbability.ofWeights_expected]
    refine ENNReal.tsum_eq_zero.mpr (fun t => ?_)
    by_cases hwz : wf t = 0
    · rw [hwz, mul_zero]
    · simp only [hwf] at hwz
      obtain ⟨m, hm⟩ : ∃ m, μ₁.1 {(t.1, m)} * μ₂.1 {(m, t.2)} / (q σ₂).1 {m} ≠ 0 := by
        by_contra h; push_neg at h; exact hwz (ENNReal.tsum_eq_zero.mpr h)
      have h1 : μ₁.1 {(t.1, m)} ≠ 0 := by
        intro h0; exact hm (by rw [h0, zero_mul, ENNReal.zero_div])
      have h2 : μ₂.1 {(m, t.2)} ≠ 0 := by
        intro h0; exact hm (by rw [h0, mul_zero, ENNReal.zero_div])
      rw [hf t ⟨m, hsat₁ (t.1, m) h1, hsat₂ (m, t.2) h2⟩, zero_mul]

/-- **Synchronized while rule** (the coupling least fixed point). Under the
    invariant the guards are coupled to agree (`PostC` records the invariant
    refined by the guard value), the bodies preserve the invariant from
    `PostC true`, and the loops relate at `PostC false`. The witness coupling
    is `Φ.lfp`, the least fixed point of the coupling transformer that runs
    the guard coupling and, while it fires, the body coupling. -/
theorem while_loop {s₁ s₂ : Type}
    [Countable (Unit × s₁)] [Countable (Unit × s₂)]
    [Countable (Bool × s₁)] [Countable (Bool × s₂)]
    {cond₁ : Program s₁ Bool} {body₁ : Program s₁ Unit}
    {cond₂ : Program s₂ Bool} {body₂ : Program s₂ Unit}
    {Inv : s₁ → s₂ → Prop} {PostC : Bool → s₁ → s₂ → Prop}
    (h_cond : Program.prhl2 Inv cond₁ cond₂ (fun u v => u.1 = v.1 ∧ PostC u.1 u.2 v.2))
    (h_body : Program.prhl2 (PostC true) body₁ body₂ (fun u v => Inv u.2 v.2)) :
    Program.prhl2 Inv (while_loop cond₁ body₁) (while_loop cond₂ body₂)
      (fun u v => PostC false u.2 v.2) := by
  classical
  -- Guard and body coupling kernels (⊥ off the relevant relation).
  set Kc : s₁ → s₂ → SubProbability ((Bool × s₁) × (Bool × s₂)) :=
    fun a b => if h : Inv a b then (h_cond a b h).choose else ⊥ with hKc
  set Kb : s₁ → s₂ → SubProbability ((Unit × s₁) × (Unit × s₂)) :=
    fun a b => if h : PostC true a b then (h_body a b h).choose else ⊥ with hKb
  have Kc_fst : ∀ a b, Inv a b → (Kc a b >>= fun w => pure w.1) = cond₁ a := by
    intro a b h; simp only [hKc, dif_pos h]; exact (h_cond a b h).choose_spec.1
  have Kc_snd : ∀ a b, Inv a b → (Kc a b >>= fun w => pure w.2) = cond₂ b := by
    intro a b h; simp only [hKc, dif_pos h]; exact (h_cond a b h).choose_spec.2.1
  have Kc_sat : ∀ a b, Inv a b →
      (Kc a b).satisfies (fun x => x.1.1 = x.2.1 ∧ PostC x.1.1 x.1.2 x.2.2) := by
    intro a b h; simp only [hKc, dif_pos h]; exact (h_cond a b h).choose_spec.2.2
  have Kb_fst : ∀ a b, PostC true a b → (Kb a b >>= fun w => pure w.1) = body₁ a := by
    intro a b h; simp only [hKb, dif_pos h]; exact (h_body a b h).choose_spec.1
  have Kb_snd : ∀ a b, PostC true a b → (Kb a b >>= fun w => pure w.2) = body₂ b := by
    intro a b h; simp only [hKb, dif_pos h]; exact (h_body a b h).choose_spec.2.1
  have Kb_sat : ∀ a b, PostC true a b → (Kb a b).satisfies (fun x => Inv x.1.2 x.2.2) := by
    intro a b h; simp only [hKb, dif_pos h]; exact (h_body a b h).choose_spec.2.2
  -- The coupling transformer and its application lemma.
  set Φ : ((s₁ × s₂) → SubProbability ((Unit × s₁) × (Unit × s₂))) →𝒄
          ((s₁ × s₂) → SubProbability ((Unit × s₁) × (Unit × s₂))) :=
    OmegaCompletePartialOrder.ContinuousHom.ofFun
      (fun φ st => Kc st.1 st.2 >>= fun gp =>
        if gp.1.1 then Kb gp.1.2 gp.2.2 >>= fun bp => φ (bp.1.2, bp.2.2)
        else pure (((), gp.1.2), ((), gp.2.2))) with hΦ
  have hΦ_app : ∀ (φ : (s₁ × s₂) → SubProbability ((Unit × s₁) × (Unit × s₂)))
      (st : s₁ × s₂), Φ φ st = Kc st.1 st.2 >>= fun gp =>
        if gp.1.1 then Kb gp.1.2 gp.2.2 >>= fun bp => φ (bp.1.2, bp.2.2)
        else pure (((), gp.1.2), ((), gp.2.2)) := fun φ st => rfl
  -- Left marginal of each Kleene iterate.
  have hML : ∀ n σ₁ σ₂, Inv σ₁ σ₂ →
      (Φ^[n] ⊥ (σ₁, σ₂)) >>= (fun w => pure w.1)
        = (while_iteration cond₁ body₁)^[n] ⊥ () σ₁ := by
    intro n
    induction n with
    | zero =>
      intro σ₁ σ₂ _
      simp only [Function.iterate_zero, id_eq]
      rw [show (⊥ : (s₁ × s₂) → SubProbability _) (σ₁, σ₂) = ⊥ from rfl,
          show (⊥ : Unit → Program s₁ Unit) () σ₁ = ⊥ from rfl]
      exact SubProbability.bot_bind _
    | succ n ih =>
      intro σ₁ σ₂ hInv
      rw [Function.iterate_succ_apply', hΦ_app]
      dsimp only
      rw [SubProbability.bind_assoc',
          SubProbability.bind_congr_support (Kc σ₁ σ₂)
            (F' := fun gp => if gp.1.1
              then body₁ gp.1.2 >>= fun u => (while_iteration cond₁ body₁)^[n] ⊥ () u.2
              else pure ((), gp.1.2))]
      · rw [SubProbability.bind_fst_left (H := fun b : Bool × s₁ => if b.1
              then body₁ b.2 >>= fun u => (while_iteration cond₁ body₁)^[n] ⊥ () u.2
              else pure ((), b.2)),
          Kc_fst σ₁ σ₂ hInv, Function.iterate_succ_apply', while_iteration_apply]
      · intro gp hgp
        obtain ⟨hb_eq, hpc⟩ := Kc_sat σ₁ σ₂ hInv gp hgp
        by_cases hb : gp.1.1
        · rw [if_pos hb, if_pos hb, SubProbability.bind_assoc',
              SubProbability.bind_congr_support (Kb gp.1.2 gp.2.2)
                (F' := fun bp => (while_iteration cond₁ body₁)^[n] ⊥ () bp.1.2)]
          · rw [SubProbability.bind_fst_left (H := fun u : Unit × s₁ =>
                  (while_iteration cond₁ body₁)^[n] ⊥ () u.2),
              Kb_fst gp.1.2 gp.2.2 (hb ▸ hpc)]
          · intro bp hbp
            exact ih bp.1.2 bp.2.2 (Kb_sat gp.1.2 gp.2.2 (hb ▸ hpc) bp hbp)
        · rw [if_neg hb, if_neg hb, SubProbability.pure_bind]
  -- Right marginal of each Kleene iterate.
  have hMR : ∀ n σ₁ σ₂, Inv σ₁ σ₂ →
      (Φ^[n] ⊥ (σ₁, σ₂)) >>= (fun w => pure w.2)
        = (while_iteration cond₂ body₂)^[n] ⊥ () σ₂ := by
    intro n
    induction n with
    | zero =>
      intro σ₁ σ₂ _
      simp only [Function.iterate_zero, id_eq]
      rw [show (⊥ : (s₁ × s₂) → SubProbability _) (σ₁, σ₂) = ⊥ from rfl,
          show (⊥ : Unit → Program s₂ Unit) () σ₂ = ⊥ from rfl]
      exact SubProbability.bot_bind _
    | succ n ih =>
      intro σ₁ σ₂ hInv
      rw [Function.iterate_succ_apply', hΦ_app]
      dsimp only
      rw [SubProbability.bind_assoc',
          SubProbability.bind_congr_support (Kc σ₁ σ₂)
            (F' := fun gp => if gp.2.1
              then body₂ gp.2.2 >>= fun u => (while_iteration cond₂ body₂)^[n] ⊥ () u.2
              else pure ((), gp.2.2))]
      · rw [SubProbability.bind_snd_left (H := fun b : Bool × s₂ => if b.1
              then body₂ b.2 >>= fun u => (while_iteration cond₂ body₂)^[n] ⊥ () u.2
              else pure ((), b.2)),
          Kc_snd σ₁ σ₂ hInv, Function.iterate_succ_apply', while_iteration_apply]
      · intro gp hgp
        obtain ⟨hb_eq, hpc⟩ := Kc_sat σ₁ σ₂ hInv gp hgp
        by_cases hb : gp.1.1
        · rw [if_pos hb, if_pos (hb_eq ▸ hb : gp.2.1 = true),
              SubProbability.bind_assoc',
              SubProbability.bind_congr_support (Kb gp.1.2 gp.2.2)
                (F' := fun bp => (while_iteration cond₂ body₂)^[n] ⊥ () bp.2.2)]
          · rw [SubProbability.bind_snd_left (H := fun u : Unit × s₂ =>
                  (while_iteration cond₂ body₂)^[n] ⊥ () u.2),
              Kb_snd gp.1.2 gp.2.2 (hb ▸ hpc)]
          · intro bp hbp
            exact ih bp.1.2 bp.2.2 (Kb_sat gp.1.2 gp.2.2 (hb ▸ hpc) bp hbp)
        · rw [if_neg hb, if_neg (by rw [← hb_eq]; exact hb : ¬ gp.2.1 = true),
              SubProbability.pure_bind]
  -- Support of each Kleene iterate.
  have hS : ∀ n σ₁ σ₂, Inv σ₁ σ₂ →
      (Φ^[n] ⊥ (σ₁, σ₂)).satisfies (fun x => PostC false x.1.2 x.2.2) := by
    intro n
    induction n with
    | zero =>
      intro σ₁ σ₂ _
      simp only [Function.iterate_zero, id_eq]
      rw [show (⊥ : (s₁ × s₂) → SubProbability _) (σ₁, σ₂) = ⊥ from rfl]
      exact SubProbability.satisfies_bot _
    | succ n ih =>
      intro σ₁ σ₂ hInv
      rw [Function.iterate_succ_apply', hΦ_app]
      refine SubProbability.satisfies_bind (Kc σ₁ σ₂) (fun gp hgp => ?_)
      obtain ⟨hb_eq, hpc⟩ := Kc_sat σ₁ σ₂ hInv gp hgp
      by_cases hb : gp.1.1
      · rw [if_pos hb]
        exact SubProbability.satisfies_bind (Kb gp.1.2 gp.2.2)
          (fun bp hbp => ih bp.1.2 bp.2.2 (Kb_sat gp.1.2 gp.2.2 (hb ▸ hpc) bp hbp))
      · rw [if_neg hb]
        refine SubProbability.satisfies_pure _ _ ?_
        have : gp.1.1 = false := by simpa using hb
        rw [this] at hpc
        exact hpc
  -- Assemble the coupling witness at each invariant-related state.
  intro σ₁ σ₂ hInv
  refine ⟨Φ.lfp (σ₁, σ₂), ?_, ?_, ?_⟩
  · refine SubProbability.ext_of_expected (fun G => ?_)
    rw [SubProbability.expected_map, SubProbability.expected_lfp_eq_iSup,
        expected_while_lfp_iSup]
    refine iSup_congr (fun n => ?_)
    rw [← SubProbability.expected_map, hML n σ₁ σ₂ hInv]
  · refine SubProbability.ext_of_expected (fun G => ?_)
    rw [SubProbability.expected_map, SubProbability.expected_lfp_eq_iSup,
        expected_while_lfp_iSup]
    refine iSup_congr (fun n => ?_)
    rw [← SubProbability.expected_map, hMR n σ₁ σ₂ hInv]
  · exact SubProbability.satisfies_lfp Φ (σ₁, σ₂) _ (fun n => hS n σ₁ σ₂ hInv)

end Program.prhl2

/-! ## Smoke tests -/

example {s γ : Type} (p : Program s γ) :
    Program.prhl2 Eq p p (fun u v : γ × s => u = v) :=
  Program.prhl2.refl p

example :
    Program.prhl2 Eq
      ((pure true : Program Bool Bool) >>= fun b => pure b)
      ((pure true : Program Bool Bool) >>= fun b => pure b)
      (fun u v => u = v) :=
  Program.prhl2.bind (Program.prhl2.refl _)
    (fun x₁ x₂ => Program.prhl2.pure_pure (fun σ₁ σ₂ h => by
      cases h
      rfl))

/-- The loop rule on a concrete bounded loop. -/
example (n : ℕ) :
    Program.prhl2 Eq (loop_n n (pure () : Program Bool Unit))
      (loop_n n (pure ())) (fun u v => u.2 = v.2) :=
  Program.prhl2.loop_n (Program.prhl2.pure_pure (fun _ _ h => h)) n

/-- Frame a left-only ghost write away, keeping only value equality. -/
example {γ : Type} (L : Lens γ Bool) (v : γ) (x : Nat) :
    Program.prhl2 (fun _ _ => True)
      (Program.set L v >>= fun _ => (pure x : Program Bool Nat))
      (pure x : Program Bool Nat) (fun u v => u.1 = v.1) :=
  Program.prhl2.prefix_left (Mid := fun _ _ => True)
    (Program.prhl2.set_skip_left L v (fun _ _ _ => trivial))
    (Program.prhl2.pure_pure (fun _ _ _ => rfl))

/-- Synchronized sampling draws the same value on both sides. -/
example :
    Program.prhl2 (fun _ _ => True)
      (Program.uniform : Program Bool Bool) (Program.uniform : Program Bool Bool)
      (fun u v => u.1 = v.1) :=
  Program.prhl2.uniform_id (fun _ _ _ _ => rfl)

/-- Transitivity composes two diagonal couplings. -/
example (p : Program Bool Bool) :
    Program.prhl2 (fun σ₁ σ₃ => ∃ σ₂, σ₁ = σ₂ ∧ σ₂ = σ₃) p p
      (fun x z => ∃ y, x = y ∧ y = z) :=
  Program.prhl2.trans (Program.prhl2.refl p) (Program.prhl2.refl p)

/-- The synchronized while rule on a loop that exits immediately. -/
example :
    Program.prhl2 Eq
      (while_loop (pure false : Program Bool Bool) (pure ()))
      (while_loop (pure false : Program Bool Bool) (pure ()))
      (fun u v => u.2 = v.2) :=
  Program.prhl2.while_loop (PostC := fun _ σ₁ σ₂ => σ₁ = σ₂)
    (Program.prhl2.pure_pure (fun _ _ h => ⟨rfl, h⟩))
    (Program.prhl2.pure_pure (fun _ _ h => h))

/-! ## Completeness (`relE → prhl`): the forward half, and the open step

The converse of `prhl2.to_relE` — that the wp-lifting judgment yields a
coupling — is **discrete Strassen** (the coupling-lifting theorem). Its
only proofs go through max-flow–min-cut / LP-duality, none of which is in
Mathlib (no transportation feasibility, no fractional Hall, no
Birkhoff–von Neumann), so it would be a from-scratch standalone
formalization. It remains the single open step between the two logics.

What the wp judgment *does* give directly is the **forward half**:
plugging in indicator post-conditions turns `rel` into Hall's
marginal-domination condition. By the classical (discrete) Strassen
theorem this condition is also *sufficient* for a coupling — so this lemma
isolates exactly the combinatorial fact that is missing. -/

/-- **Hall's condition from `rel`** (the necessary half of discrete
    Strassen): the mass `c` places on any set `A` is dominated by the mass
    `d` places on the `Post`-image of `A`. The converse (Hall ⇒ coupling)
    is the open Strassen step. -/
theorem Program.rel.hall {s₁ s₂ α β : Type} {c : Program s₁ α} {d : Program s₂ β}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : c.rel d Pre Post) {σ₁ : s₁} {σ₂ : s₂} (hpre : Pre σ₁ σ₂)
    (A : Set (α × s₁)) :
    (c σ₁).1 A ≤ (d σ₂).1 {y | ∃ x ∈ A, Post x y} := by
  have key := h (Set.indicator A 1) (Set.indicator {y | ∃ x ∈ A, Post x y} 1)
    (fun x y hxy => by
      by_cases hx : x ∈ A
      · have hy : y ∈ {y | ∃ x ∈ A, Post x y} := ⟨x, hx, hxy⟩
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
        exact le_rfl
      · rw [Set.indicator_of_notMem hx]; exact zero_le')
    σ₁ σ₂ hpre
  rwa [show c.wp (Set.indicator A 1) σ₁ = (c σ₁).1 A from
        MeasureTheory.lintegral_indicator_one trivial,
      show d.wp (Set.indicator {y | ∃ x ∈ A, Post x y} 1) σ₂
          = (d σ₂).1 {y | ∃ x ∈ A, Post x y} from
        MeasureTheory.lintegral_indicator_one trivial] at key

/-- For a two-sided `relE`, Hall's condition holds in **both** directions:
    `d`'s mass on `B` is dominated by `c`'s mass on the `Post`-preimage of
    `B`. -/
theorem Program.relE.hall_right {s₁ s₂ α β : Type} {c : Program s₁ α} {d : Program s₂ β}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : c.relE d Pre Post) {σ₁ : s₁} {σ₂ : s₂} (hpre : Pre σ₁ σ₂)
    (B : Set (β × s₂)) :
    (d σ₂).1 B ≤ (c σ₁).1 {x | ∃ y ∈ B, Post x y} :=
  h.2.hall hpre B

/-! ### Scaling a sub-probability (for the mass-normalization reduction) -/

/-- Scale a sub-probability by `c` (well-defined as a sub-probability when
    `c · (total mass) ≤ 1`). -/
noncomputable def SubProbability.scale {X : Type} (c : ENNReal) (ν : SubProbability X)
    (h : c * ν.1 Set.univ ≤ 1) : SubProbability X :=
  ⟨c • ν.1, by
    rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]; exact h⟩

@[simp] lemma SubProbability.scale_expected {X : Type} (c : ENNReal) (ν : SubProbability X)
    (h : c * ν.1 Set.univ ≤ 1) (g : X → ENNReal) :
    (SubProbability.scale c ν h).expected g = c * ν.expected g := by
  show ∫⁻ x, g x ∂(c • ν.1) = c * ∫⁻ x, g x ∂ν.1
  rw [MeasureTheory.lintegral_smul_measure, smul_eq_mul]

lemma SubProbability.scale_satisfies {X : Type} (c : ENNReal) (ν : SubProbability X)
    (h : c * ν.1 Set.univ ≤ 1) {B : X → Prop} (hν : ν.satisfies B) :
    (SubProbability.scale c ν h).satisfies B := by
  intro w hw
  refine hν w (fun h0 => hw ?_)
  show (c • ν.1) {w} = 0
  rw [MeasureTheory.Measure.smul_apply, h0, smul_zero]

/-- **Discrete Strassen / coupling lifting (axiom), probability-measure
    form.** This is Strassen's 1965 theorem verbatim: over countable
    carriers, two *probability* measures satisfying Hall's marginal-
    domination condition `p(A) ≤ q(R(A))` admit a coupling with those
    marginals supported on the relation. It is **not** available in Mathlib
    (no max-flow–min-cut / fractional Hall / transportation feasibility),
    so we take it as an axiom; `SubProbability.exists_coupling_of_hall`
    below derives the sub-probability form from it by normalization, and
    `Program.rel.hall` shows the hypothesis is exactly what `relE` supplies.

    References (this is a true, classical theorem):
    * V. Strassen, "The existence of probability measures with given
      marginals", Ann. Math. Statist. 36(2):423–439, 1965 — the general
      theorem. A countable discrete space is Polish and every relation on
      it is closed, so the 1965 result applies here directly.
      https://projecteuclid.org/euclid.aoms/1177700153
    * T. Koperberg, "Couplings and Matchings: combinatorial notes on
      Strassen's theorem", Statist. Probab. Lett. (2024), arXiv:2202.02092
      — the finite case in exactly this Hall form, shown equivalent to
      Hall's marriage theorem.
    * Combinatorial proof: max-flow–min-cut / weighted Hall; see
      Lovász & Plummer, "Matching Theory" (1986).
    * Use in coupling-based program logics (the `relE ↔ prhl2`
      correspondence here): Barthe, Espitau, Grégoire, Hsu, Strub,
      "Probabilistic Couplings for Probabilistic Reasoning",
      arXiv:1710.09951. -/
axiom SubProbability.exists_coupling_of_hall_prob {X Y : Type} [Countable X] [Countable Y]
    (p : SubProbability X) (q : SubProbability Y) (R : X → Y → Prop)
    (hp : p.1 Set.univ = 1) (hq : q.1 Set.univ = 1)
    (hpq : ∀ A : Set X, p.1 A ≤ q.1 {y | ∃ x ∈ A, R x y}) :
    ∃ μ : SubProbability (X × Y),
      (μ >>= fun w => (pure w.1 : SubProbability X)) = p ∧
      (μ >>= fun w => (pure w.2 : SubProbability Y)) = q ∧
      μ.satisfies (fun w => R w.1 w.2)

/-- **Coupling lifting, sub-probability form** — *derived* from the
    probability-measure axiom `exists_coupling_of_hall_prob` by mass
    normalization (no new assumption). Two-sided Hall forces equal total
    mass; the zero-mass case is the empty coupling, and otherwise we
    normalize both sides to probability measures, invoke the axiom, and
    scale the resulting coupling back. -/
theorem SubProbability.exists_coupling_of_hall {X Y : Type} [Countable X] [Countable Y]
    (p : SubProbability X) (q : SubProbability Y) (R : X → Y → Prop)
    (hpq : ∀ A : Set X, p.1 A ≤ q.1 {y | ∃ x ∈ A, R x y})
    (hqp : ∀ B : Set Y, q.1 B ≤ p.1 {x | ∃ y ∈ B, R x y}) :
    ∃ μ : SubProbability (X × Y),
      (μ >>= fun w => (pure w.1 : SubProbability X)) = p ∧
      (μ >>= fun w => (pure w.2 : SubProbability Y)) = q ∧
      μ.satisfies (fun w => R w.1 w.2) := by
  -- Equal total mass.
  have hmass : p.1 Set.univ = q.1 Set.univ :=
    le_antisymm ((hpq Set.univ).trans (MeasureTheory.measure_mono (Set.subset_univ _)))
      ((hqp Set.univ).trans (MeasureTheory.measure_mono (Set.subset_univ _)))
  by_cases hm0 : p.1 Set.univ = 0
  · -- Zero mass: both measures vanish; the empty coupling works.
    have hp0 : p = ⊥ := Subtype.ext (by
      rw [MeasureTheory.Measure.measure_univ_eq_zero.mp hm0]; rfl)
    have hq0 : q = ⊥ := Subtype.ext (by
      have hqm0 : q.1 Set.univ = 0 := by rw [← hmass]; exact hm0
      rw [MeasureTheory.Measure.measure_univ_eq_zero.mp hqm0]; rfl)
    exact ⟨⊥, by rw [SubProbability.bot_bind, hp0], by rw [SubProbability.bot_bind, hq0],
      SubProbability.satisfies_bot _⟩
  · -- Positive mass: normalize both sides to probability measures.
    have hm_le : p.1 Set.univ ≤ 1 := p.2
    have hm_top : p.1 Set.univ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hm_le
    have hpscale : (p.1 Set.univ)⁻¹ * p.1 Set.univ ≤ 1 :=
      le_of_eq (ENNReal.inv_mul_cancel hm0 hm_top)
    have hqscale : (p.1 Set.univ)⁻¹ * q.1 Set.univ ≤ 1 :=
      le_of_eq (by rw [← hmass]; exact ENNReal.inv_mul_cancel hm0 hm_top)
    have hp'1 : (SubProbability.scale (p.1 Set.univ)⁻¹ p hpscale).1 Set.univ = 1 := by
      show ((p.1 Set.univ)⁻¹ • p.1) Set.univ = 1
      rw [MeasureTheory.Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hm0 hm_top]
    have hq'1 : (SubProbability.scale (p.1 Set.univ)⁻¹ q hqscale).1 Set.univ = 1 := by
      show ((p.1 Set.univ)⁻¹ • q.1) Set.univ = 1
      rw [MeasureTheory.Measure.smul_apply, smul_eq_mul, ← hmass,
        ENNReal.inv_mul_cancel hm0 hm_top]
    have hp'hall : ∀ A : Set X, (SubProbability.scale (p.1 Set.univ)⁻¹ p hpscale).1 A
        ≤ (SubProbability.scale (p.1 Set.univ)⁻¹ q hqscale).1 {y | ∃ x ∈ A, R x y} := by
      intro A
      show ((p.1 Set.univ)⁻¹ • p.1) A ≤ ((p.1 Set.univ)⁻¹ • q.1) _
      rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.smul_apply,
        smul_eq_mul, smul_eq_mul]
      gcongr
      exact hpq A
    obtain ⟨ν, hν1, hν2, hνsat⟩ := SubProbability.exists_coupling_of_hall_prob
      (SubProbability.scale (p.1 Set.univ)⁻¹ p hpscale)
      (SubProbability.scale (p.1 Set.univ)⁻¹ q hqscale) R hp'1 hq'1 hp'hall
    have hνmass : p.1 Set.univ * ν.1 Set.univ ≤ 1 := by
      calc p.1 Set.univ * ν.1 Set.univ ≤ p.1 Set.univ * 1 := by gcongr; exact ν.2
        _ = p.1 Set.univ := mul_one _
        _ ≤ 1 := hm_le
    refine ⟨SubProbability.scale (p.1 Set.univ) ν hνmass, ?_, ?_, ?_⟩
    · refine SubProbability.ext_of_expected (fun G => ?_)
      have hν1' : ν.expected (fun w => G w.1) = (p.1 Set.univ)⁻¹ * p.expected G := by
        rw [← SubProbability.scale_expected (p.1 Set.univ)⁻¹ p hpscale G, ← hν1,
          SubProbability.expected_map]
      rw [SubProbability.expected_map, SubProbability.scale_expected, hν1',
        ← mul_assoc, ENNReal.mul_inv_cancel hm0 hm_top, one_mul]
    · refine SubProbability.ext_of_expected (fun G => ?_)
      have hν2' : ν.expected (fun w => G w.2) = (p.1 Set.univ)⁻¹ * q.expected G := by
        rw [← SubProbability.scale_expected (p.1 Set.univ)⁻¹ q hqscale G, ← hν2,
          SubProbability.expected_map]
      rw [SubProbability.expected_map, SubProbability.scale_expected, hν2',
        ← mul_assoc, ENNReal.mul_inv_cancel hm0 hm_top, one_mul]
    · exact SubProbability.scale_satisfies (p.1 Set.univ) ν hνmass hνsat

/-- **Completeness** `relE → prhl2` (discrete, modulo the Strassen axiom):
    the wp-lifting judgment yields a coupling. The reduction is real — it
    extracts Hall's condition in both directions from `relE` via
    `rel.hall` and feeds it to `exists_coupling_of_hall`; only the
    combinatorial coupling-existence step is assumed. Together with
    `prhl2.to_relE` this shows the two logics coincide over countable
    carriers. -/
theorem Program.relE.to_prhl2 {s₁ s₂ α β : Type}
    [Countable (α × s₁)] [Countable (β × s₂)]
    {c : Program s₁ α} {d : Program s₂ β}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : c.relE d Pre Post) : Program.prhl2 Pre c d Post :=
  fun σ₁ σ₂ hpre =>
    SubProbability.exists_coupling_of_hall (c σ₁) (d σ₂) Post
      (fun A => h.1.hall hpre A) (fun B => Program.relE.hall_right h hpre B)

/-- The two relational logics **coincide** over countable carriers
    (discrete, modulo the Strassen axiom). -/
theorem Program.prhl2_iff_relE {s₁ s₂ α β : Type}
    [Countable ((α × s₁) × (β × s₂))] [Countable (α × s₁)] [Countable (β × s₂)]
    {c : Program s₁ α} {d : Program s₂ β}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop} :
    Program.prhl2 Pre c d Post ↔ c.relE d Pre Post :=
  ⟨fun h => h.to_relE, fun h => h.to_prhl2⟩

end GaudisCrypt.Language.Semantics
