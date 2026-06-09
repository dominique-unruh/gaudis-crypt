import PlonkLean.ProgramRange

/-!
# Equivalence-modulo-lens calculus

We define a relation `Program.EquivModuloLens L p q` capturing
"`p` and `q` have equal wps on any post that doesn't read lens `L`".

This packages the recurring pattern in cryptographic game-hopping where
two games differ only by writes to an auxiliary tracking variable, and
those writes are invisible at the wp level for posts ignoring the
tracking variable.

The calculus has closure rules (reflexivity, symmetry, transitivity,
bind congruence) and base instances (e.g. `pure () ≈ set L v` for any
lens `L`, value `v`). Tracking-flag elision proofs reduce to short
chains of these rules.
-/

/-- A post `F` ignores lens `L` if it doesn't depend on `L`-content of
    its state argument: setting `L` to any value leaves `F` unchanged. -/
def IgnoresLens {γ s α : Type} (L : Lens γ s) (F : α × s → ENNReal) : Prop :=
  ∀ (aσ : α × s) (v : γ), F (aσ.1, L.set v aσ.2) = F aσ

namespace IgnoresLens

/-- L-ignoring is preserved when post-composing with an L-disjoint program. -/
lemma comp_inRange {γ s α β : Type} [DecidableEq γ] {L : Lens γ s}
    {F : β × s → ENNReal} (h_F : IgnoresLens L F)
    (k : α → Program s β) (h_k : ∀ a, (k a).inRange L.compl.range) :
    IgnoresLens L (fun aσ : α × s => (k aσ.1).wp F aσ.2) := by
  intro aσ v
  have hf : (fun s' : s => L.set v s') ∈ ((L.compl.range : LensRange s)ᶜ).updates := by
    rw [show ((L.compl.range : LensRange s)ᶜ) = L.range from by
        rw [LensRange.complement_range, LensRange.compl_compl]]
    exact ⟨Function.const _ v, Set.mem_univ _, rfl⟩
  show (k aσ.1).wp F (L.set v aσ.2) = (k aσ.1).wp F aσ.2
  rw [Program.wp_shift_input (h_k aσ.1) hf]
  congr 1
  funext xs
  exact h_F xs v

end IgnoresLens

/-- `Program.EquivModuloLens L p q` — `p` and `q` have equal wps on any
    `L`-ignoring post. -/
def Program.EquivModuloLens {γ s α : Type} (L : Lens γ s)
    (p q : Program s α) : Prop :=
  ∀ (F : α × s → ENNReal), IgnoresLens L F → ∀ σ : s, p.wp F σ = q.wp F σ

namespace Program.EquivModuloLens

variable {γ s α β : Type} {L : Lens γ s}

@[refl]
lemma refl (p : Program s α) : Program.EquivModuloLens L p p :=
  fun _ _ _ => rfl

@[symm]
lemma symm {p q : Program s α} (h : Program.EquivModuloLens L p q) :
    Program.EquivModuloLens L q p :=
  fun F h_F σ => (h F h_F σ).symm

lemma trans {p q r : Program s α}
    (h1 : Program.EquivModuloLens L p q) (h2 : Program.EquivModuloLens L q r) :
    Program.EquivModuloLens L p r :=
  fun F h_F σ => (h1 F h_F σ).trans (h2 F h_F σ)

/-- Bind with the SAME L-disjoint continuation on both sides: if `p ≈_L p'`
    and `k` doesn't touch `L`, then `p >>= k ≈_L p' >>= k`. -/
lemma bind_eq_k [DecidableEq γ]
    {p p' : Program s α} {k : α → Program s β}
    (h_p : Program.EquivModuloLens L p p')
    (h_k : ∀ a, (k a).inRange L.compl.range) :
    Program.EquivModuloLens L (p >>= k) (p' >>= k) := by
  intro F h_F σ
  rw [wp_bind, wp_bind]
  exact h_p _ (IgnoresLens.comp_inRange h_F k h_k) σ

/-- Bind with the SAME prefix and equivalent continuations: if `∀ a, k a ≈_L k' a`,
    then `p >>= k ≈_L p >>= k'`. -/
lemma bind_eq_p
    {p : Program s α} {k k' : α → Program s β}
    (h_k : ∀ a, Program.EquivModuloLens L (k a) (k' a)) :
    Program.EquivModuloLens L (p >>= k) (p >>= k') := by
  intro F h_F σ
  rw [wp_bind, wp_bind]
  congr 1
  funext aσ
  exact h_k aσ.1 F h_F aσ.2

/-- Full bind congruence: `p ≈_L p'` AND `∀ a, k a ≈_L k' a` AND `k` is
    L-disjoint (per element) → `p >>= k ≈_L p' >>= k'`. -/
lemma bind [DecidableEq γ]
    {p p' : Program s α} {k k' : α → Program s β}
    (h_p : Program.EquivModuloLens L p p')
    (h_k : ∀ a, Program.EquivModuloLens L (k a) (k' a))
    (h_k_inRange : ∀ a, (k a).inRange L.compl.range) :
    Program.EquivModuloLens L (p >>= k) (p' >>= k') :=
  (h_p.bind_eq_k h_k_inRange).trans (bind_eq_p h_k)

/-- A `set L v` is equivalent (modulo L) to `pure ()`. -/
lemma set_equiv_pure (v : γ) :
    Program.EquivModuloLens L (Program.set L v) (pure ()) := by
  intro F h_F σ
  rw [wp_set, wp_pure]
  exact h_F ((), σ) v

/-- `pure ()` is equivalent (modulo L) to `set L v` (symmetric form). -/
lemma pure_equiv_set (v : γ) :
    Program.EquivModuloLens L (pure ()) (Program.set L v) :=
  (set_equiv_pure v).symm

/-- A conditional `set L v` is equivalent to `pure ()`. -/
lemma cond_set_equiv_pure (cond : Prop) [Decidable cond] (v : γ) :
    Program.EquivModuloLens L
      (if cond then Program.set L v else (pure () : Program s Unit))
      (pure ()) := by
  intro F h_F σ
  by_cases h : cond
  · rw [if_pos h, wp_set, wp_pure]
    exact h_F ((), σ) v
  · rw [if_neg h]

/-- Transfer to wp: if `p ≈_L q` and `F` is L-ignoring, then their wps agree. -/
lemma wp_eq {p q : Program s α} (h : Program.EquivModuloLens L p q)
    (F : α × s → ENNReal) (h_F : IgnoresLens L F) (σ : s) :
    p.wp F σ = q.wp F σ := h F h_F σ

end Program.EquivModuloLens
