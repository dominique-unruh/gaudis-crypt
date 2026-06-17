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

end GaudisCrypt.Language.Semantics
