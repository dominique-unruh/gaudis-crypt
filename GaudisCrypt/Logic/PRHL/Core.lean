import GaudisCrypt.WeakestPreconditions

open GaudisCrypt

namespace GaudisCrypt

/-!
# pRHL core: a relational wp calculus for `ProgramDenotation`

`ProgramDenotation.rel p q Pre Post` is the asymmetric relational lifting: for every
pair of postconditions compatible with `Post`, the wp of `p` from a
`Pre`-related pair of states is below the wp of `q`. `ProgramDenotation.relE` is the
symmetric (equality) variant, used for bridging game hops; `rel` itself is
the primitive, used for reductions and up-to-bad inequalities.

Design notes:

* The judgment is *defined by* its elimination form, so the probability
  bridges (`rel.wp_le`, `relE.wp_eq`) are definitional and every proof rule
  is a small consequence of the existing unary `wp` lemma base — no witness
  couplings, hence no measurability, countability, or a.e.-support side
  conditions. For discrete subprobabilities this lifting is coextensive with
  the coupling-based one (Strassen) in the direction proofs consume.
* Heterogeneous state and result types are supported (`ProgramDenotation s₁ α` vs
  `ProgramDenotation s₂ β`): the calculus can relate a concrete game to an abstract
  schema, or a program to its lens-factored inner core.
* **Unsound-rule warning**: conjunction of postconditions is NOT admissible.
  From `rel p q Pre Post₁` and `rel p q Pre Post₂` one may NOT conclude
  `rel p q Pre (fun x y => Post₁ x y ∧ Post₂ x y)`. (Standard
  counterexample: for `p = q =` a uniform coin, both post `x₁ = x₂` and post
  `x₁ ≠ x₂` hold relationally — with different implicit couplings — but
  their conjunction is empty.) Do not add such a rule.
-/

/-- **Relational wp judgment** (asymmetric form). `p.rel q Pre Post` holds iff
    for all post-pairs `F ≤ G` along `Post` and all `Pre`-related starting
    states, `p.wp F ≤ q.wp G`. -/
def ProgramDenotation.rel {s₁ s₂ α β : Type} (p : ProgramDenotation s₁ α) (q : ProgramDenotation s₂
    β)
    (Pre : s₁ → s₂ → Prop) (Post : α × s₁ → β × s₂ → Prop) : Prop :=
  ∀ (F : α × s₁ → ENNReal) (G : β × s₂ → ENNReal),
    (∀ x y, Post x y → F x ≤ G y) →
    ∀ σ₁ σ₂, Pre σ₁ σ₂ → p.wp F σ₁ ≤ q.wp G σ₂

/-- **Relational wp equivalence**: `rel` in both directions (with flipped
    relations). The two-sided judgment used for bridging game hops. -/
def ProgramDenotation.relE {s₁ s₂ α β : Type} (p : ProgramDenotation s₁ α) (q : ProgramDenotation s₂
    β)
    (Pre : s₁ → s₂ → Prop) (Post : α × s₁ → β × s₂ → Prop) : Prop :=
  p.rel q Pre Post ∧ q.rel p (fun σ₂ σ₁ => Pre σ₁ σ₂) (fun y x => Post x y)

namespace ProgramDenotation.rel

/-! ## Elimination (Pr-bridges) -/

/-- Elimination form (definitional): a `rel` judgment yields a wp inequality
    at any compatible post-pair. -/
lemma wp_le {s₁ s₂ α β : Type} {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : p.rel q Pre Post)
    {F : α × s₁ → ENNReal} {G : β × s₂ → ENNReal}
    (hFG : ∀ x y, Post x y → F x ≤ G y)
    {σ₁ : s₁} {σ₂ : s₂} (hpre : Pre σ₁ σ₂) :
    p.wp F σ₁ ≤ q.wp G σ₂ :=
  h F G hFG σ₁ σ₂ hpre

/-! ## Structural rules -/

/-- Consequence: weaken the precondition, strengthen the postcondition. -/
lemma conseq {s₁ s₂ α β : Type} {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β}
    {Pre Pre' : s₁ → s₂ → Prop} {Post Post' : α × s₁ → β × s₂ → Prop}
    (h : p.rel q Pre Post)
    (hPre : ∀ σ₁ σ₂, Pre' σ₁ σ₂ → Pre σ₁ σ₂)
    (hPost : ∀ x y, Post x y → Post' x y) :
    p.rel q Pre' Post' :=
  fun F G hFG σ₁ σ₂ hpre =>
    h F G (fun x y hxy => hFG x y (hPost x y hxy)) σ₁ σ₂ (hPre σ₁ σ₂ hpre)

/-- Reflexivity at the diagonal. -/
lemma refl {s α : Type} (p : ProgramDenotation s α) : p.rel p Eq Eq := by
  intro F G hFG σ₁ σ₂ hpre
  subst hpre
  exact ProgramDenotation.wp_le_wp_of_le p F G (fun x => hFG x x rfl) σ₁

/-- Transitivity through a middle program, with composed pre/post relations.
    No PER or losslessness side conditions: the middle postcondition is
    interpolated by `fun y => ⨆ x, ⨆ (_ : Post₁ x y), F x` (possible because
    posts are `ENNReal`-valued and need no measurability). -/
lemma trans {s₁ s₂ s₃ α β γ : Type}
    {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β} {r : ProgramDenotation s₃ γ}
    {Pre₁ : s₁ → s₂ → Prop} {Post₁ : α × s₁ → β × s₂ → Prop}
    {Pre₂ : s₂ → s₃ → Prop} {Post₂ : β × s₂ → γ × s₃ → Prop}
    (h₁ : p.rel q Pre₁ Post₁) (h₂ : q.rel r Pre₂ Post₂) :
    p.rel r (fun σ₁ σ₃ => ∃ σ₂, Pre₁ σ₁ σ₂ ∧ Pre₂ σ₂ σ₃)
            (fun x z => ∃ y, Post₁ x y ∧ Post₂ y z) := by
  intro F G hFG σ₁ σ₃ hpre
  obtain ⟨σ₂, hpre₁, hpre₂⟩ := hpre
  calc p.wp F σ₁
      ≤ q.wp (fun y => ⨆ x, ⨆ (_ : Post₁ x y), F x) σ₂ :=
        h₁ F _ (fun x y hxy => le_iSup₂ (f := fun x (_ : Post₁ x y) => F x) x hxy)
          σ₁ σ₂ hpre₁
    _ ≤ r.wp G σ₃ :=
        h₂ _ G (fun y z hyz => iSup₂_le fun x hxy => hFG x z ⟨y, hxy, hyz⟩)
          σ₂ σ₃ hpre₂

/-- Eliminate an existential in the precondition. -/
lemma exists_pre {s₁ s₂ α β : Type} {ι : Sort*}
    {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β}
    {Pre : ι → s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : ∀ i, p.rel q (Pre i) Post) :
    p.rel q (fun σ₁ σ₂ => ∃ i, Pre i σ₁ σ₂) Post :=
  fun F G hFG σ₁ σ₂ hpre =>
    hpre.elim fun i hi => h i F G hFG σ₁ σ₂ hi

/-- Case split on the precondition. -/
lemma or_pre {s₁ s₂ α β : Type} {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β}
    {Pre₁ Pre₂ : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h₁ : p.rel q Pre₁ Post) (h₂ : p.rel q Pre₂ Post) :
    p.rel q (fun σ₁ σ₂ => Pre₁ σ₁ σ₂ ∨ Pre₂ σ₁ σ₂) Post :=
  fun F G hFG σ₁ σ₂ hpre =>
    hpre.elim (h₁ F G hFG σ₁ σ₂) (h₂ F G hFG σ₁ σ₂)

/-- Two-sided `pure`. -/
lemma pure_pure {s₁ s₂ α β : Type} {x₁ : α} {x₂ : β}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : ∀ σ₁ σ₂, Pre σ₁ σ₂ → Post (x₁, σ₁) (x₂, σ₂)) :
    (pure x₁ : ProgramDenotation s₁ α).rel (pure x₂ : ProgramDenotation s₂ β) Pre Post := by
  intro F G hFG σ₁ σ₂ hpre
  rw [wp_pure, wp_pure]
  exact hFG _ _ (h σ₁ σ₂ hpre)

/-- **Sequence rule** (the workhorse): relate the prefixes at a middle
    relation `Mid`, then the continuations from every `Mid`-related pair. -/
lemma bind {s₁ s₂ α₁ α₂ β₁ β₂ : Type}
    {p₁ : ProgramDenotation s₁ α₁} {p₂ : ProgramDenotation s₂ α₂}
    {k₁ : α₁ → ProgramDenotation s₁ β₁} {k₂ : α₂ → ProgramDenotation s₂ β₂}
    {Pre : s₁ → s₂ → Prop} {Mid : α₁ × s₁ → α₂ × s₂ → Prop}
    {Post : β₁ × s₁ → β₂ × s₂ → Prop}
    (h_p : p₁.rel p₂ Pre Mid)
    (h_k : ∀ x₁ x₂, (k₁ x₁).rel (k₂ x₂)
        (fun τ₁ τ₂ => Mid (x₁, τ₁) (x₂, τ₂)) Post) :
    (p₁ >>= k₁).rel (p₂ >>= k₂) Pre Post := by
  intro F G hFG σ₁ σ₂ hpre
  rw [wp_bind, wp_bind]
  refine h_p _ _ ?_ σ₁ σ₂ hpre
  rintro ⟨x₁, τ₁⟩ ⟨x₂, τ₂⟩ hmid
  exact h_k x₁ x₂ F G hFG τ₁ τ₂ hmid

/-- Prepend a left-only prefix (e.g. a ghost write): if `p₀ ~ skip` carries
    `Pre` to `Mid`, and `k ~ q` from `Mid`, then `(p₀; k) ~ q` from `Pre`.
    Avoids inserting `pure () >>=` on the right by hand. -/
lemma prefix_left {s₁ s₂ α β : Type}
    {p₀ : ProgramDenotation s₁ Unit} {k : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β}
    {Pre Mid : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h₀ : p₀.rel (pure () : ProgramDenotation s₂ Unit) Pre (fun x y => Mid x.2 y.2))
    (h : k.rel q Mid Post) :
    (p₀ >>= fun _ => k).rel q Pre Post := by
  intro F G hFG σ₁ σ₂ hpre
  rw [wp_bind]
  calc p₀.wp (fun xτ : Unit × s₁ => k.wp F xτ.2) σ₁
      ≤ (pure () : ProgramDenotation s₂ Unit).wp (fun yτ : Unit × s₂ => q.wp G yτ.2) σ₂ :=
        h₀ _ _ (fun x y hxy => h F G hFG x.2 y.2 hxy) σ₁ σ₂ hpre
    _ = q.wp G σ₂ := by rw [wp_pure]

/-- Prepend a right-only prefix: mirror image of `prefix_left`. -/
lemma prefix_right {s₁ s₂ α β : Type}
    {p : ProgramDenotation s₁ α} {q₀ : ProgramDenotation s₂ Unit} {k : ProgramDenotation s₂ β}
    {Pre Mid : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h₀ : (pure () : ProgramDenotation s₁ Unit).rel q₀ Pre (fun x y => Mid x.2 y.2))
    (h : p.rel k Mid Post) :
    p.rel (q₀ >>= fun _ => k) Pre Post := by
  intro F G hFG σ₁ σ₂ hpre
  rw [wp_bind]
  calc p.wp F σ₁
      = (pure () : ProgramDenotation s₁ Unit).wp (fun xτ : Unit × s₁ => p.wp F xτ.2) σ₁ := by
        rw [wp_pure]
    _ ≤ q₀.wp (fun yτ : Unit × s₂ => k.wp G yτ.2) σ₂ :=
        h₀ _ _ (fun x y hxy => h F G hFG x.2 y.2 hxy) σ₁ σ₂ hpre

/-- Synchronized conditional with statically equivalent guards. (For
    state-dependent guards, the guards become values bound by `bind`, so they
    are static by the time this rule applies; for genuinely one-sided
    conditionals use `by_cases` at the meta level.) -/
lemma ite_sync {s₁ s₂ α β : Type} {c₁ c₂ : Prop} [Decidable c₁] [Decidable c₂]
    {p₁ q₁ : ProgramDenotation s₁ α} {p₂ q₂ : ProgramDenotation s₂ β}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h_iff : c₁ ↔ c₂)
    (h_t : c₁ → c₂ → p₁.rel p₂ Pre Post)
    (h_f : ¬c₁ → ¬c₂ → q₁.rel q₂ Pre Post) :
    (if c₁ then p₁ else q₁).rel (if c₂ then p₂ else q₂) Pre Post := by
  by_cases h : c₁
  · rw [if_pos h, if_pos (h_iff.mp h)]
    exact h_t h (h_iff.mp h)
  · rw [if_neg h, if_neg (fun hc => h (h_iff.mpr hc))]
    exact h_f h (fun hc => h (h_iff.mpr hc))

/-! ## Assignment rules (`ProgramDenotation.set` / `ProgramDenotation.get`) -/

/-- Two-sided `set`. -/
lemma set_set {s₁ s₂ γ₁ γ₂ : Type} {L₁ : Lens γ₁ s₁} {L₂ : Lens γ₂ s₂}
    {v₁ : γ₁} {v₂ : γ₂}
    {Pre : s₁ → s₂ → Prop} {Post : Unit × s₁ → Unit × s₂ → Prop}
    (h : ∀ σ₁ σ₂, Pre σ₁ σ₂ → Post ((), L₁.set v₁ σ₁) ((), L₂.set v₂ σ₂)) :
    (ProgramDenotation.set L₁ v₁).rel (ProgramDenotation.set L₂ v₂) Pre Post := by
  intro F G hFG σ₁ σ₂ hpre
  rw [wp_set, wp_set]
  exact hFG _ _ (h σ₁ σ₂ hpre)

/-- Left-only `set` (against `pure` on the right): the ghost-write rule. -/
lemma set_left {s₁ s₂ γ β : Type} {L : Lens γ s₁} {v : γ} {x₂ : β}
    {Pre : s₁ → s₂ → Prop} {Post : Unit × s₁ → β × s₂ → Prop}
    (h : ∀ σ₁ σ₂, Pre σ₁ σ₂ → Post ((), L.set v σ₁) (x₂, σ₂)) :
    (ProgramDenotation.set L v).rel (pure x₂ : ProgramDenotation s₂ β) Pre Post := by
  intro F G hFG σ₁ σ₂ hpre
  rw [wp_set, wp_pure]
  exact hFG _ _ (h σ₁ σ₂ hpre)

/-- Right-only `set` (against `pure` on the left). -/
lemma set_right {s₁ s₂ γ α : Type} {x₁ : α} {L : Lens γ s₂} {v : γ}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → Unit × s₂ → Prop}
    (h : ∀ σ₁ σ₂, Pre σ₁ σ₂ → Post (x₁, σ₁) ((), L.set v σ₂)) :
    (pure x₁ : ProgramDenotation s₁ α).rel (ProgramDenotation.set L v) Pre Post := by
  intro F G hFG σ₁ σ₂ hpre
  rw [wp_set, wp_pure]
  exact hFG _ _ (h σ₁ σ₂ hpre)

/-- Two-sided `get`. -/
lemma get_get {s₁ s₂ γ₁ γ₂ : Type} {L₁ : Lens γ₁ s₁} {L₂ : Lens γ₂ s₂}
    {Pre : s₁ → s₂ → Prop} {Post : γ₁ × s₁ → γ₂ × s₂ → Prop}
    (h : ∀ σ₁ σ₂, Pre σ₁ σ₂ → Post (L₁.get σ₁, σ₁) (L₂.get σ₂, σ₂)) :
    (ProgramDenotation.get L₁).rel (ProgramDenotation.get L₂) Pre Post := by
  intro F G hFG σ₁ σ₂ hpre
  rw [wp_get, wp_get]
  exact hFG _ _ (h σ₁ σ₂ hpre)

/-- Left-only `get`. -/
lemma get_left {s₁ s₂ γ β : Type} {L : Lens γ s₁} {x₂ : β}
    {Pre : s₁ → s₂ → Prop} {Post : γ × s₁ → β × s₂ → Prop}
    (h : ∀ σ₁ σ₂, Pre σ₁ σ₂ → Post (L.get σ₁, σ₁) (x₂, σ₂)) :
    (ProgramDenotation.get L).rel (pure x₂ : ProgramDenotation s₂ β) Pre Post := by
  intro F G hFG σ₁ σ₂ hpre
  rw [wp_get, wp_pure]
  exact hFG _ _ (h σ₁ σ₂ hpre)

/-- Right-only `get`. -/
lemma get_right {s₁ s₂ γ α : Type} {x₁ : α} {L : Lens γ s₂}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → γ × s₂ → Prop}
    (h : ∀ σ₁ σ₂, Pre σ₁ σ₂ → Post (x₁, σ₁) (L.get σ₂, σ₂)) :
    (pure x₁ : ProgramDenotation s₁ α).rel (ProgramDenotation.get L) Pre Post := by
  intro F G hFG σ₁ σ₂ hpre
  rw [wp_get, wp_pure]
  exact hFG _ _ (h σ₁ σ₂ hpre)

/-! ## Sampling rules -/

/-- **Coupled sampling along a bijection** (the `rnd` rule): two uniform
    samples are related by pairing `v` with `e v`. -/
lemma uniform_bij {s₁ s₂ α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β)
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : ∀ v σ₁ σ₂, Pre σ₁ σ₂ → Post (v, σ₁) (e v, σ₂)) :
    (ProgramDenotation.uniform : ProgramDenotation s₁ α).rel (ProgramDenotation.uniform :
        ProgramDenotation s₂ β) Pre Post := by
  intro F G hFG σ₁ σ₂ hpre
  rw [wp_uniform, wp_uniform]
  calc ∑ i : α, F (i, σ₁) / (Fintype.card α : ENNReal)
      ≤ ∑ i : α, G (e i, σ₂) / (Fintype.card α : ENNReal) := by
        apply Finset.sum_le_sum
        intro i _
        exact ENNReal.div_le_div_right (hFG _ _ (h i σ₁ σ₂ hpre)) _
    _ = ∑ j : β, G (j, σ₂) / (Fintype.card α : ENNReal) :=
        Equiv.sum_comp e (fun j => G (j, σ₂) / (Fintype.card α : ENNReal))
    _ = ∑ j : β, G (j, σ₂) / (Fintype.card β : ENNReal) := by
        rw [Fintype.card_congr e]

/-- **Left-only sampling**: an average is below any uniform upper bound.
    No mass side condition. -/
lemma sample_left {s₁ s₂ α β₁ β₂ : Type} [Fintype α] [Nonempty α]
    {k : α → ProgramDenotation s₁ β₁} {q : ProgramDenotation s₂ β₂}
    {Pre : s₁ → s₂ → Prop} {Post : β₁ × s₁ → β₂ × s₂ → Prop}
    (h : ∀ v, (k v).rel q Pre Post) :
    ((ProgramDenotation.uniform : ProgramDenotation s₁ α) >>= k).rel q Pre Post := by
  intro F G hFG σ₁ σ₂ hpre
  have hc0 : (Fintype.card α : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  have hct : (Fintype.card α : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : ((ProgramDenotation.uniform : ProgramDenotation s₁ α) >>= k).wp F σ₁
      = ∑ v : α, (k v).wp F σ₁ / (Fintype.card α : ENNReal) := by
    rw [wp_bind, wp_uniform]
  rw [hsum]
  calc ∑ v : α, (k v).wp F σ₁ / (Fintype.card α : ENNReal)
      ≤ ∑ _v : α, q.wp G σ₂ / (Fintype.card α : ENNReal) := by
        apply Finset.sum_le_sum
        intro v _
        exact ENNReal.div_le_div_right (h v F G hFG σ₁ σ₂ hpre) _
    _ = q.wp G σ₂ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.mul_div_cancel hc0 hct]

/-- **Right-only sampling** (sample introduction): a uniform average of lower
    bounds is a lower bound. Mass-1 of `uniform` is what makes this sound. -/
lemma sample_right {s₁ s₂ α β₁ β₂ : Type} [Fintype α] [Nonempty α]
    {p : ProgramDenotation s₁ β₁} {k : α → ProgramDenotation s₂ β₂}
    {Pre : s₁ → s₂ → Prop} {Post : β₁ × s₁ → β₂ × s₂ → Prop}
    (h : ∀ v, p.rel (k v) Pre Post) :
    p.rel ((ProgramDenotation.uniform : ProgramDenotation s₂ α) >>= k) Pre Post := by
  intro F G hFG σ₁ σ₂ hpre
  have hc0 : (Fintype.card α : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  have hct : (Fintype.card α : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : ((ProgramDenotation.uniform : ProgramDenotation s₂ α) >>= k).wp G σ₂
      = ∑ v : α, (k v).wp G σ₂ / (Fintype.card α : ENNReal) := by
    rw [wp_bind, wp_uniform]
  rw [hsum]
  calc p.wp F σ₁
      = ∑ _v : α, p.wp F σ₁ / (Fintype.card α : ENNReal) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.mul_div_cancel hc0 hct]
    _ ≤ ∑ v : α, (k v).wp G σ₂ / (Fintype.card α : ENNReal) := by
        apply Finset.sum_le_sum
        intro v _
        exact ENNReal.div_le_div_right (h v F G hFG σ₁ σ₂ hpre) _

end ProgramDenotation.rel

namespace ProgramDenotation.relE

/-! ## relE: elimination and mechanical two-sided variants -/

/-- Elimination form: a `relE` judgment yields wp *equality* at any post-pair
    that agrees along `Post`. -/
lemma wp_eq {s₁ s₂ α β : Type} {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : p.relE q Pre Post)
    {F : α × s₁ → ENNReal} {G : β × s₂ → ENNReal}
    (hFG : ∀ x y, Post x y → F x = G y)
    {σ₁ : s₁} {σ₂ : s₂} (hpre : Pre σ₁ σ₂) :
    p.wp F σ₁ = q.wp G σ₂ :=
  le_antisymm
    (h.1 F G (fun x y hxy => (hFG x y hxy).le) σ₁ σ₂ hpre)
    (h.2 G F (fun y x hxy => (hFG x y hxy).ge) σ₂ σ₁ hpre)

/-- Reflexivity. -/
lemma refl {s α : Type} (p : ProgramDenotation s α) : p.relE p Eq Eq :=
  ⟨ProgramDenotation.rel.refl p,
   (ProgramDenotation.rel.refl p).conseq (fun _ _ h => h.symm) (fun _ _ h => h.symm)⟩

/-- ProgramDenotation equality gives the diagonal `relE`. -/
lemma of_eq {s α : Type} {p q : ProgramDenotation s α} (h : p = q) :
    p.relE q Eq Eq := by
  subst h
  exact ProgramDenotation.relE.refl p

/-- Symmetry (with flipped relations). -/
lemma symm {s₁ s₂ α β : Type} {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : p.relE q Pre Post) :
    q.relE p (fun σ₂ σ₁ => Pre σ₁ σ₂) (fun y x => Post x y) :=
  ⟨h.2, h.1⟩

/-- Transitivity for `relE` (composed pre/post relations). -/
lemma trans {s₁ s₂ s₃ α β γ : Type}
    {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β} {r : ProgramDenotation s₃ γ}
    {Pre₁ : s₁ → s₂ → Prop} {Post₁ : α × s₁ → β × s₂ → Prop}
    {Pre₂ : s₂ → s₃ → Prop} {Post₂ : β × s₂ → γ × s₃ → Prop}
    (h₁ : p.relE q Pre₁ Post₁) (h₂ : q.relE r Pre₂ Post₂) :
    p.relE r (fun σ₁ σ₃ => ∃ σ₂, Pre₁ σ₁ σ₂ ∧ Pre₂ σ₂ σ₃)
             (fun x z => ∃ y, Post₁ x y ∧ Post₂ y z) := by
  refine ⟨ProgramDenotation.rel.trans h₁.1 h₂.1, ?_⟩
  exact (ProgramDenotation.rel.trans h₂.2 h₁.2).conseq
    (fun σ₃ σ₁ h => h.elim fun σ₂ hh => ⟨σ₂, hh.2, hh.1⟩)
    (fun z x h => h.elim fun y hh => ⟨y, hh.2, hh.1⟩)

/-- Eliminate an existential in the precondition. -/
lemma exists_pre {s₁ s₂ α β : Type} {ι : Sort*}
    {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β}
    {Pre : ι → s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : ∀ i, p.relE q (Pre i) Post) :
    p.relE q (fun σ₁ σ₂ => ∃ i, Pre i σ₁ σ₂) Post :=
  ⟨ProgramDenotation.rel.exists_pre (fun i => (h i).1),
   fun F G hFG σ₂ σ₁ hpre =>
     hpre.elim fun i hi => (h i).2 F G hFG σ₂ σ₁ hi⟩

/-- Case split on the precondition, for `relE`. -/
lemma or_pre {s₁ s₂ α β : Type} {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β}
    {Pre₁ Pre₂ : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h₁ : p.relE q Pre₁ Post) (h₂ : p.relE q Pre₂ Post) :
    p.relE q (fun σ₁ σ₂ => Pre₁ σ₁ σ₂ ∨ Pre₂ σ₁ σ₂) Post :=
  ⟨ProgramDenotation.rel.or_pre h₁.1 h₂.1, ProgramDenotation.rel.or_pre h₁.2 h₂.2⟩

/-- Consequence for `relE`. -/
lemma conseq {s₁ s₂ α β : Type} {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β}
    {Pre Pre' : s₁ → s₂ → Prop} {Post Post' : α × s₁ → β × s₂ → Prop}
    (h : p.relE q Pre Post)
    (hPre : ∀ σ₁ σ₂, Pre' σ₁ σ₂ → Pre σ₁ σ₂)
    (hPost : ∀ x y, Post x y → Post' x y) :
    p.relE q Pre' Post' :=
  ⟨h.1.conseq hPre hPost,
   h.2.conseq (fun σ₂ σ₁ hpre => hPre σ₁ σ₂ hpre) (fun y x hxy => hPost x y hxy)⟩

/-- Two-sided `pure` for `relE`. -/
lemma pure_pure {s₁ s₂ α β : Type} {x₁ : α} {x₂ : β}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : ∀ σ₁ σ₂, Pre σ₁ σ₂ → Post (x₁, σ₁) (x₂, σ₂)) :
    (pure x₁ : ProgramDenotation s₁ α).relE (pure x₂ : ProgramDenotation s₂ β) Pre Post :=
  ⟨ProgramDenotation.rel.pure_pure h, ProgramDenotation.rel.pure_pure (fun σ₂ σ₁ hpre => h σ₁ σ₂
      hpre)⟩

/-- Sequence rule for `relE`. -/
lemma bind {s₁ s₂ α₁ α₂ β₁ β₂ : Type}
    {p₁ : ProgramDenotation s₁ α₁} {p₂ : ProgramDenotation s₂ α₂}
    {k₁ : α₁ → ProgramDenotation s₁ β₁} {k₂ : α₂ → ProgramDenotation s₂ β₂}
    {Pre : s₁ → s₂ → Prop} {Mid : α₁ × s₁ → α₂ × s₂ → Prop}
    {Post : β₁ × s₁ → β₂ × s₂ → Prop}
    (h_p : p₁.relE p₂ Pre Mid)
    (h_k : ∀ x₁ x₂, (k₁ x₁).relE (k₂ x₂)
        (fun τ₁ τ₂ => Mid (x₁, τ₁) (x₂, τ₂)) Post) :
    (p₁ >>= k₁).relE (p₂ >>= k₂) Pre Post :=
  ⟨ProgramDenotation.rel.bind h_p.1 (fun x₁ x₂ => (h_k x₁ x₂).1),
   ProgramDenotation.rel.bind h_p.2 (fun x₂ x₁ => (h_k x₁ x₂).2)⟩

/-- Two-sided `set` for `relE`. -/
lemma set_set {s₁ s₂ γ₁ γ₂ : Type} {L₁ : Lens γ₁ s₁} {L₂ : Lens γ₂ s₂}
    {v₁ : γ₁} {v₂ : γ₂}
    {Pre : s₁ → s₂ → Prop} {Post : Unit × s₁ → Unit × s₂ → Prop}
    (h : ∀ σ₁ σ₂, Pre σ₁ σ₂ → Post ((), L₁.set v₁ σ₁) ((), L₂.set v₂ σ₂)) :
    (ProgramDenotation.set L₁ v₁).relE (ProgramDenotation.set L₂ v₂) Pre Post :=
  ⟨ProgramDenotation.rel.set_set h, ProgramDenotation.rel.set_set (fun σ₂ σ₁ hpre => h σ₁ σ₂ hpre)⟩

/-- Two-sided `get` for `relE`. -/
lemma get_get {s₁ s₂ γ₁ γ₂ : Type} {L₁ : Lens γ₁ s₁} {L₂ : Lens γ₂ s₂}
    {Pre : s₁ → s₂ → Prop} {Post : γ₁ × s₁ → γ₂ × s₂ → Prop}
    (h : ∀ σ₁ σ₂, Pre σ₁ σ₂ → Post (L₁.get σ₁, σ₁) (L₂.get σ₂, σ₂)) :
    (ProgramDenotation.get L₁).relE (ProgramDenotation.get L₂) Pre Post :=
  ⟨ProgramDenotation.rel.get_get h, ProgramDenotation.rel.get_get (fun σ₂ σ₁ hpre => h σ₁ σ₂ hpre)⟩

/-- Coupled sampling along a bijection, for `relE`. -/
lemma uniform_bij {s₁ s₂ α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β)
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : ∀ v σ₁ σ₂, Pre σ₁ σ₂ → Post (v, σ₁) (e v, σ₂)) :
    (ProgramDenotation.uniform : ProgramDenotation s₁ α).relE (ProgramDenotation.uniform :
        ProgramDenotation s₂ β) Pre Post := by
  refine ⟨ProgramDenotation.rel.uniform_bij e h, ProgramDenotation.rel.uniform_bij e.symm ?_⟩
  intro v σ₂ σ₁ hpre
  have := h (e.symm v) σ₁ σ₂ hpre
  rwa [e.apply_symm_apply] at this

/-- Synchronized conditional for `relE`. -/
lemma ite_sync {s₁ s₂ α β : Type} {c₁ c₂ : Prop} [Decidable c₁] [Decidable c₂]
    {p₁ q₁ : ProgramDenotation s₁ α} {p₂ q₂ : ProgramDenotation s₂ β}
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h_iff : c₁ ↔ c₂)
    (h_t : c₁ → c₂ → p₁.relE p₂ Pre Post)
    (h_f : ¬c₁ → ¬c₂ → q₁.relE q₂ Pre Post) :
    (if c₁ then p₁ else q₁).relE (if c₂ then p₂ else q₂) Pre Post :=
  ⟨ProgramDenotation.rel.ite_sync h_iff (fun h1 h2 => (h_t h1 h2).1) (fun h1 h2 => (h_f h1 h2).1),
   ProgramDenotation.rel.ite_sync h_iff.symm (fun h2 h1 => (h_t h1 h2).2) (fun h2 h1 => (h_f h1
       h2).2)⟩

end ProgramDenotation.relE

end GaudisCrypt
