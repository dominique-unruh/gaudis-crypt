import GaudisCrypt.Logic.PRHL.Core
import GaudisCrypt.Logic.PRHL.Coupling

namespace GaudisCrypt.Language.Semantics

/-!
# pRHL with couplings as the primitive judgment (CLAUDE.md subtask 3)

The candidate definition under evaluation:

```
prhl A c d B  :=  ∀ m₁ m₂, A (m₁, m₂) →
  ∃ μ, map fst μ = c m₁ ∧ map snd μ = d m₂ ∧ satisfy (μ, B)
```

Here `Program.prhl A c d B := ∀ σ₁ σ₂, A σ₁ σ₂ → Nonempty (Coupling …)`,
with `Program.Coupling` (PRHL/Coupling.lean) playing the role of the
existential: its `marg₁/marg₂` fields state the marginal conditions in
expected-value form (`Coupling.map_fst/map_snd` below recover the literal
`map fst μ = c m₁` form), and its `supp` field is CertiCrypt's range-form
of `satisfy`. `SubProbability.satisfies` below is the subtask's literal
pointwise form `∀ x, μ x ≠ 0 → B x`; the two are equivalent for discrete
(countable) state — see `satisfies_iff_range`, whose `→` direction is
exactly where countability is needed.

## Evaluation findings (discrete setting)

* **The textbook obstacle dissolves.** In a general Giry-monad setting the
  seq rule needs a *measurable* choice of continuation couplings. With the
  `⊤` σ-algebra every function is measurable, so `Classical.choice`
  composes pointwise and `Coupling.comp` (below) proves `prhl.bind` with
  no side conditions. This is the rule that costs CertiCrypt/SSProve real
  infrastructure.
* **Soundness is one line**: `prhl.to_relE` via `relE.of_coupling` — every
  coupling-judgment yields the wp-lifting judgment, so all `relE`
  elimination forms (`wp_eq`, `bad_eq`, `up_to_bad`) apply to `prhl`.
* **Open: completeness (discrete Strassen).** The converse
  `c.relE d A B → Program.prhl A c d B` is true for countable state but
  amounts to a countable max-flow/min-cut (Hall) argument constructing a
  witness from the family of wp-inequalities; it is not formalized here.
  Until it is, `prhl` is a (possibly strictly) stronger judgment per
  instance, and the two logics interoperate one-way.
* **Open: transitivity.** Gluing two couplings along the common middle
  marginal needs discrete disintegration (division by the middle weights
  in `ENNReal`); deferred. The wp-lifting `rel.trans` needs nothing.
* **Open: while.** A coupling for a loop needs a fixed point of a
  coupling transformer; deferred (the wp-lifting `rel.while_loop` covers
  loops, and transports to `prhl`-provable goals via `to_relE`).
-/

/-! ## The judgment -/

/-- **Coupling-based pRHL** (subtask-3 argument order: predicate, program,
    program, predicate). -/
def Program.prhl {s₁ s₂ α β : Type} (A : s₁ → s₂ → Prop)
    (c : Program s₁ α) (d : Program s₂ β)
    (B : α × s₁ → β × s₂ → Prop) : Prop :=
  ∀ σ₁ σ₂, A σ₁ σ₂ → Nonempty (Program.Coupling c d σ₁ σ₂ B)

/-! ## The witness fields recover the literal subtask-3 conditions -/

/-- Subprobabilities with equal expected values are equal. -/
lemma SubProbability.ext_of_expected {γ : Type} {μ ν : SubProbability γ}
    (h : ∀ f, μ.expected f = ν.expected f) : μ = ν := by
  apply Subtype.ext
  letI : MeasurableSpace γ := ⊤
  apply MeasureTheory.Measure.ext
  intro A hA
  have hf := h (A.indicator 1)
  simp only [SubProbability.expected] at hf
  rwa [MeasureTheory.lintegral_indicator_one hA,
       MeasureTheory.lintegral_indicator_one hA] at hf

namespace Program.Coupling

variable {s₁ s₂ α β : Type}
    {p : Program s₁ α} {q : Program s₂ β} {σ₁ : s₁} {σ₂ : s₂}
    {Post : α × s₁ → β × s₂ → Prop}

/-- `map fst μ = c m₁`, literally. -/
lemma map_fst (c : Program.Coupling p q σ₁ σ₂ Post) :
    (c.w >>= fun uv => (pure uv.1 : SubProbability (α × s₁))) = p σ₁ := by
  refine SubProbability.ext_of_expected fun f => ?_
  rw [SubProbability.expected_bind]
  refine Eq.trans (SubProbability.expected_congr _
    (g := fun uv => f uv.1) (fun uv => ?_)) (c.marg₁ f)
  change ((pure uv.1 : SubProbability (α × s₁)).expected f) = f uv.1
  rw [expected_pure]

/-- `map snd μ = d m₂`, literally. -/
lemma map_snd (c : Program.Coupling p q σ₁ σ₂ Post) :
    (c.w >>= fun uv => (pure uv.2 : SubProbability (β × s₂))) = q σ₂ := by
  refine SubProbability.ext_of_expected fun f => ?_
  rw [SubProbability.expected_bind]
  refine Eq.trans (SubProbability.expected_congr _
    (g := fun uv => f uv.2) (fun uv => ?_)) (c.marg₂ f)
  change ((pure uv.2 : SubProbability (β × s₂)).expected f) = f uv.2
  rw [expected_pure]

/-- Expected values agree for posts that agree on the support. -/
lemma expected_congr (c : Program.Coupling p q σ₁ σ₂ Post)
    {f g : (α × s₁) × (β × s₂) → ENNReal}
    (h : ∀ uv, Post uv.1 uv.2 → f uv = g uv) :
    c.w.expected f = c.w.expected g :=
  le_antisymm (c.expected_le fun uv hP => (h uv hP).le)
    (c.expected_le fun uv hP => (h uv hP).ge)

end Program.Coupling

/-! ## The pointwise `satisfy` and discreteness

Subtask 3 defines `satisfy (μ, B) := ∀ x, μ x ≠ 0 → B x`. The witness
structure uses the range form instead (`∀ f vanishing on B, ∫ f dμ = 0`),
which needs no decidability or countability. The two agree for discrete
state — and the proof shows exactly where countability enters: only in
the direction pointwise → range (summing the atoms). -/

/-- The literal subtask-3 `satisfy`. -/
def SubProbability.satisfies {γ : Type} (μ : SubProbability γ)
    (B : γ → Prop) : Prop :=
  ∀ x, μ.1 {x} ≠ 0 → B x

/-- Range form implies pointwise form — no countability needed. -/
lemma SubProbability.satisfies_of_range {γ : Type} (μ : SubProbability γ)
    (B : γ → Prop)
    (h : ∀ f : γ → ENNReal, (∀ x, B x → f x = 0) → μ.expected f = 0) :
    μ.satisfies B := by
  intro x hx
  by_contra hB
  apply hx
  have h0 := h (Set.indicator {x} (fun _ => 1)) (fun y hBy => by
    have hyx : y ∉ ({x} : Set γ) := by
      intro hy
      exact hB (Set.mem_singleton_iff.mp hy ▸ hBy)
    simp [Set.indicator_of_notMem hyx])
  rw [expectation_indicator, one_mul] at h0
  have hne : μ.1 {x} ≠ ⊤ :=
    ((MeasureTheory.measure_mono (Set.subset_univ _)).trans μ.2.1).trans_lt
      ENNReal.one_lt_top |>.ne
  have : (μ.1 {x}).toNNReal = 0 := by exact_mod_cast h0
  rw [← ENNReal.coe_toNNReal hne, this]
  rfl

/-- Pointwise form implies range form — **this is where discreteness is
    used**: the integral is a countable sum of atoms. -/
lemma SubProbability.range_of_satisfies {γ : Type} [Countable γ]
    (μ : SubProbability γ) (B : γ → Prop) (h : μ.satisfies B) :
    ∀ f : γ → ENNReal, (∀ x, B x → f x = 0) → μ.expected f = 0 := by
  intro f hf
  letI : MeasurableSpace γ := ⊤
  haveI : MeasurableSingletonClass γ := ⟨fun _ => trivial⟩
  change ∫⁻ x, f x ∂μ.1 = 0
  rw [MeasureTheory.lintegral_countable']
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : μ.1 {x} = 0
  · rw [hx, mul_zero]
  · rw [hf x (h x hx), zero_mul]

/-- For discrete state the two `satisfy` formulations coincide. -/
theorem SubProbability.satisfies_iff_range {γ : Type} [Countable γ]
    (μ : SubProbability γ) (B : γ → Prop) :
    μ.satisfies B
    ↔ ∀ f : γ → ENNReal, (∀ x, B x → f x = 0) → μ.expected f = 0 :=
  ⟨μ.range_of_satisfies B, μ.satisfies_of_range B⟩

/-! ## Soundness with respect to the wp-lifting -/

/-- Every coupling judgment yields the (two-sided) wp-lifting judgment;
    all `relE` elimination forms transfer. The converse is discrete
    Strassen — see the module header. -/
theorem Program.prhl.to_relE {s₁ s₂ α β : Type} {A : s₁ → s₂ → Prop}
    {c : Program s₁ α} {d : Program s₂ β} {B : α × s₁ → β × s₂ → Prop}
    (h : Program.prhl A c d B) : c.relE d A B :=
  Program.relE.of_coupling fun σ₁ σ₂ hA => (h σ₁ σ₂ hA).some

/-! ## Structural rules on the coupling judgment -/

namespace Program.prhl

variable {s₁ s₂ α β : Type} {A : s₁ → s₂ → Prop}
    {B : α × s₁ → β × s₂ → Prop}

/-- Consequence. The same witness works: the support condition only
    weakens. -/
theorem conseq {c : Program s₁ α} {d : Program s₂ β}
    {A' : s₁ → s₂ → Prop} {B' : α × s₁ → β × s₂ → Prop}
    (h : Program.prhl A c d B)
    (hA : ∀ σ₁ σ₂, A' σ₁ σ₂ → A σ₁ σ₂)
    (hB : ∀ u v, B u v → B' u v) :
    Program.prhl A' c d B' := by
  intro σ₁ σ₂ hpre
  obtain ⟨μ⟩ := h σ₁ σ₂ (hA σ₁ σ₂ hpre)
  exact ⟨{ w := μ.w, marg₁ := μ.marg₁, marg₂ := μ.marg₂,
           supp := fun f hf => μ.supp f fun uv hP => hf uv (hB _ _ hP) }⟩

/-- Two-sided `pure`. -/
theorem pure_pure {x₁ : α} {x₂ : β}
    (h : ∀ σ₁ σ₂, A σ₁ σ₂ → B (x₁, σ₁) (x₂, σ₂)) :
    Program.prhl A (pure x₁ : Program s₁ α) (pure x₂ : Program s₂ β) B :=
  fun σ₁ σ₂ hA =>
    ⟨Program.Coupling.of_pure (x₁, σ₁) (x₂, σ₂)
      (fun F => by rw [wp_pure]) (fun G => by rw [wp_pure])
      (h σ₁ σ₂ hA)⟩

/-- Diagonal coupling: any program relates to itself at equal states. -/
noncomputable def diagCoupling {s : Type} {γ : Type} (p : Program s γ) (σ : s) :
    Program.Coupling p p σ σ (fun u v : γ × s => u = v) where
  w := (p σ) >>= fun x => (pure (x, x) : SubProbability ((γ × s) × (γ × s)))
  marg₁ F := by
    rw [SubProbability.expected_bind]
    refine Eq.trans (SubProbability.expected_congr _ (g := F) (fun x => ?_)) rfl
    change ((pure (x, x) : SubProbability ((γ × s) × (γ × s))).expected
      (fun uv => F uv.1)) = F x
    rw [expected_pure]
  marg₂ G := by
    rw [SubProbability.expected_bind]
    refine Eq.trans (SubProbability.expected_congr _ (g := G) (fun x => ?_)) rfl
    change ((pure (x, x) : SubProbability ((γ × s) × (γ × s))).expected
      (fun uv => G uv.2)) = G x
    rw [expected_pure]
  supp f hf := by
    rw [SubProbability.expected_bind]
    refine Eq.trans (SubProbability.expected_congr _
      (g := fun _ => (0 : ENNReal)) (fun x => ?_))
      (SubProbability.expected_zero _)
    change ((pure (x, x) : SubProbability ((γ × s) × (γ × s))).expected f) = 0
    rw [expected_pure]
    exact hf _ rfl

/-- Reflexivity. -/
theorem refl {s γ : Type} (p : Program s γ) :
    Program.prhl Eq p p (fun u v : γ × s => u = v) := by
  intro σ₁ σ₂ hA
  cases hA
  exact ⟨diagCoupling p σ₁⟩

/-- The `rnd` rule: uniform samples coupled along a bijection. -/
theorem uniform {α' β' : Type} [Fintype α'] [Nonempty α'] [Fintype β'] [Nonempty β']
    (e : α' ≃ β') {B : α' × s₁ → β' × s₂ → Prop}
    (h : ∀ t σ₁ σ₂, A σ₁ σ₂ → B (t, σ₁) (e t, σ₂)) :
    Program.prhl A (Program.uniform : Program s₁ α')
      (Program.uniform : Program s₂ β') B := by
  intro σ₁ σ₂ hA
  refine ⟨Program.Coupling.of_uniform (T := α')
    (fun t => (t, σ₁)) (fun t => (e t, σ₂)) ?_ ?_ (fun t => h t σ₁ σ₂ hA)⟩
  · intro F
    rw [wp_uniform]
  · intro G
    have hc : (Fintype.card β' : ENNReal) = (Fintype.card α' : ENNReal) := by
      rw [Fintype.card_congr e]
    rw [wp_uniform]
    dsimp only
    rw [← Equiv.sum_comp e (fun b : β' => G (b, σ₂) / (Fintype.card β' : ENNReal)),
        hc]

/-- Case split / existential / disjunction on the precondition. -/
theorem exists_pre {ι : Sort*} {A : ι → s₁ → s₂ → Prop}
    {c : Program s₁ α} {d : Program s₂ β}
    (h : ∀ i, Program.prhl (A i) c d B) :
    Program.prhl (fun σ₁ σ₂ => ∃ i, A i σ₁ σ₂) c d B :=
  fun σ₁ σ₂ hpre => hpre.elim fun i hi => h i σ₁ σ₂ hi

theorem or_pre {A₁ A₂ : s₁ → s₂ → Prop}
    {c : Program s₁ α} {d : Program s₂ β}
    (h₁ : Program.prhl A₁ c d B) (h₂ : Program.prhl A₂ c d B) :
    Program.prhl (fun σ₁ σ₂ => A₁ σ₁ σ₂ ∨ A₂ σ₁ σ₂) c d B :=
  fun σ₁ σ₂ hpre => hpre.elim (h₁ σ₁ σ₂) (h₂ σ₁ σ₂)

end Program.prhl

/-! ## The seq rule (the crux of the evaluation)

In a general measure-theoretic setting this rule requires a *measurable*
selection of continuation couplings — the main technical burden of
coupling-based pRHL semantics. With the `⊤` σ-algebra, every function is
measurable, so a plain `Classical.choice` per support point suffices and
the composite below typechecks with no side conditions. -/

/-- Projection-form `wp_bind` (avoids the pattern-matching lambda). -/
private lemma wp_bind' {s α β : Type} (p : Program s α) (k : α → Program s β)
    (F : β × s → ENNReal) (σ : s) :
    (p >>= k).wp F σ = p.wp (fun x : α × s => (k x.1).wp F x.2) σ := by
  rw [wp_bind]

open scoped Classical in
/-- **Composition of couplings through `bind`**: a coupling for the
    prefixes plus a coupling for the continuations at every support point
    yields a coupling for the composites. -/
noncomputable def Program.Coupling.comp
    {s₁ s₂ α₁ α₂ β₁ β₂ : Type}
    {p₁ : Program s₁ α₁} {p₂ : Program s₂ α₂}
    {k₁ : α₁ → Program s₁ β₁} {k₂ : α₂ → Program s₂ β₂}
    {σ₁ : s₁} {σ₂ : s₂}
    {M : α₁ × s₁ → α₂ × s₂ → Prop} {B : β₁ × s₁ → β₂ × s₂ → Prop}
    (μ : Program.Coupling p₁ p₂ σ₁ σ₂ M)
    (ν : ∀ u v, M u v → Program.Coupling (k₁ u.1) (k₂ v.1) u.2 v.2 B) :
    Program.Coupling (p₁ >>= k₁) (p₂ >>= k₂) σ₁ σ₂ B where
  w := μ.w >>= fun uv =>
    if h : M uv.1 uv.2 then (ν uv.1 uv.2 h).w else ⊥
  marg₁ F := by
    rw [SubProbability.expected_bind, wp_bind',
        ← μ.marg₁ (fun x => (k₁ x.1).wp F x.2)]
    refine μ.expected_congr fun uv hM => ?_
    rw [dif_pos hM]
    exact (ν uv.1 uv.2 hM).marg₁ F
  marg₂ G := by
    rw [SubProbability.expected_bind, wp_bind',
        ← μ.marg₂ (fun x => (k₂ x.1).wp G x.2)]
    refine μ.expected_congr fun uv hM => ?_
    rw [dif_pos hM]
    exact (ν uv.1 uv.2 hM).marg₂ G
  supp f hf := by
    rw [SubProbability.expected_bind,
        SubProbability.expected_congr _ (g := fun _ => (0 : ENNReal))
          (fun uv => ?_)]
    · exact SubProbability.expected_zero _
    · by_cases h : M uv.1 uv.2
      · rw [dif_pos h]
        exact (ν uv.1 uv.2 h).supp f hf
      · rw [dif_neg h]
        exact SubProbability.expected_bot f

/-- **The seq rule.** -/
theorem Program.prhl.bind {s₁ s₂ α₁ α₂ β₁ β₂ : Type}
    {p₁ : Program s₁ α₁} {p₂ : Program s₂ α₂}
    {k₁ : α₁ → Program s₁ β₁} {k₂ : α₂ → Program s₂ β₂}
    {A : s₁ → s₂ → Prop} {M : α₁ × s₁ → α₂ × s₂ → Prop}
    {B : β₁ × s₁ → β₂ × s₂ → Prop}
    (h₁ : Program.prhl A p₁ p₂ M)
    (h₂ : ∀ x₁ x₂, Program.prhl (fun τ₁ τ₂ => M (x₁, τ₁) (x₂, τ₂))
      (k₁ x₁) (k₂ x₂) B) :
    Program.prhl A (p₁ >>= k₁) (p₂ >>= k₂) B := by
  intro σ₁ σ₂ hA
  obtain ⟨μ⟩ := h₁ σ₁ σ₂ hA
  exact ⟨μ.comp fun u v hM => ((h₂ u.1 v.1) u.2 v.2 hM).some⟩

/-! ## Footprint rules: almost-sure unary facts strengthen the post -/

/-- Strengthen the post with an almost-sure left-side fact (the witness is
    unchanged; only the support condition is rebalanced). This is how
    `inRange`-style footprint facts enter the coupling logic. -/
noncomputable def Program.Coupling.strengthen_left
    {s₁ s₂ α β : Type}
    {p : Program s₁ α} {q : Program s₂ β} {σ₁ : s₁} {σ₂ : s₂}
    {Post : α × s₁ → β × s₂ → Prop} {C : α × s₁ → Prop} [DecidablePred C]
    (c : Program.Coupling p q σ₁ σ₂ Post)
    (hC : p.wp (fun u => if C u then 0 else 1) σ₁ = 0) :
    Program.Coupling p q σ₁ σ₂ (fun u v => Post u v ∧ C u) where
  w := c.w
  marg₁ := c.marg₁
  marg₂ := c.marg₂
  supp f hf := by
    classical
    refine le_antisymm ?_ zero_le
    calc c.w.expected f
        ≤ c.w.expected (fun uv =>
            (if Post uv.1 uv.2 then 0 else ⊤)
            + (if C uv.1 then 0 else ⊤)) := by
          apply SubProbability.expected_mono_pt
          intro uv
          by_cases hP : Post uv.1 uv.2
          · by_cases hCu : C uv.1
            · rw [hf uv ⟨hP, hCu⟩]
              exact zero_le
            · simp [hP, hCu]
          · simp [hP]
      _ = c.w.expected (fun uv => if Post uv.1 uv.2 then 0 else ⊤)
          + c.w.expected (fun uv => if C uv.1 then (0 : ENNReal) else ⊤) :=
          SubProbability.expected_add _ _ _
      _ = 0 := by
          rw [c.supp _ (fun uv hP => if_pos hP),
              show (fun uv : (α × s₁) × (β × s₂) =>
                  if C uv.1 then (0 : ENNReal) else ⊤)
                = fun uv => (fun u => ⊤ * (if C u then (0 : ENNReal) else 1)) uv.1
                from by
                funext uv
                by_cases h : C uv.1 <;> simp [h],
              c.marg₁ (fun u => ⊤ * (if C u then (0 : ENNReal) else 1)),
              Program.wp_const_mul, hC, mul_zero, add_zero]

/-! ## Smoke tests -/

example {s γ : Type} (p : Program s γ) :
    Program.prhl Eq p p (fun u v : γ × s => u = v) :=
  Program.prhl.refl p

example :
    Program.prhl Eq
      ((pure true : Program Bool Bool) >>= fun b => pure b)
      ((pure true : Program Bool Bool) >>= fun b => pure b)
      (fun u v => u = v) :=
  Program.prhl.bind (Program.prhl.refl _)
    (fun x₁ x₂ => Program.prhl.pure_pure (fun σ₁ σ₂ h => by
      cases h
      rfl))

end GaudisCrypt.Language.Semantics
