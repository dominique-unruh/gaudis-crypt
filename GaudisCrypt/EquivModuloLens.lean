import GaudisCrypt.ProgramRange

namespace GaudisCrypt.EquivModuloLens

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics

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

-- `IgnoresLens` and `IgnoresLens.comp_inRange` moved to PlonkLean.ProgramRange
-- (they don't depend on the EquivModuloLens calculus; they're foundational
-- lens-post-invariance facts useful beyond this module).

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

/-- **Loop congruence for the equiv-modulo-lens calculus**: if two bodies are
    `≈_L`-equivalent, so are their `loop_n` iterates. Requires the reference body
    `body` to be `L`-disjoint so that `loop_n n body` is also `L`-disjoint (needed
    by the bind congruence in the inductive step). -/
lemma loop_n_congr {s γ : Type} [DecidableEq γ] {L : Lens γ s}
    {body body' : Program s Unit}
    (h_body : body.inRange L.compl.range)
    (h_eq : Program.EquivModuloLens L body body')
    (n : ℕ) :
    Program.EquivModuloLens L (loop_n n body) (loop_n n body') := by
  induction n with
  | zero => exact Program.EquivModuloLens.refl _
  | succ n ih =>
    show Program.EquivModuloLens L (body >>= fun _ => loop_n n body)
                                   (body' >>= fun _ => loop_n n body')
    exact Program.EquivModuloLens.bind h_eq (fun _ => ih)
      (fun _ => loop_n_inRange body h_body n)

/-- **Loop + trailing congruence**: if `body ≈_L body'` and `final ≈_L final'`,
    with both `body` and `final` being `L`-disjoint, then
    `loop_n n body >>= final  ≈_L  loop_n n body' >>= final'`.

    Combines `loop_n_congr` and `Program.EquivModuloLens.bind` in one step. -/
lemma loop_n_then_congr {s γ : Type} [DecidableEq γ] {L : Lens γ s}
    {body body' final final' : Program s Unit}
    (h_body : body.inRange L.compl.range)
    (h_body_eq : Program.EquivModuloLens L body body')
    (h_final : final.inRange L.compl.range)
    (h_final_eq : Program.EquivModuloLens L final final')
    (n : ℕ) :
    Program.EquivModuloLens L
        (loop_n n body >>= fun _ : Unit => final)
        (loop_n n body' >>= fun _ : Unit => final') :=
  Program.EquivModuloLens.bind
    (loop_n_congr h_body h_body_eq n)
    (fun _ => h_final_eq)
    (fun _ => h_final)

end GaudisCrypt.EquivModuloLens
