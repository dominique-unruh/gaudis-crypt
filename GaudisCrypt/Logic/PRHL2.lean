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

end GaudisCrypt.Language.Semantics
