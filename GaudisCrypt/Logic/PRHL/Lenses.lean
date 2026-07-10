import GaudisCrypt.Logic.PRHL.Core
import GaudisCrypt.Logic.EquivModuloLens

open GaudisCrypt
namespace GaudisCrypt

/-!
# pRHL lens rules: self-shift, framing, and the EquivModuloLens bridge

These are the rules that interact with the lens-based memory model:

* `ProgramDenotation.rel.self_shift` / `ProgramDenotation.relE.self_lens_set` — relate a program
  to itself from two starting states that differ by an update outside its
  footprint (the relational packaging of `ProgramDenotation.wp_shift_input_prob`). This is
  the rule every client involving an abstract adversary needs.
* `ProgramDenotation.rel.frame` — strengthen a judgment with value constraints on
  lenses outside each side's footprint (the relational packaging of
  `ProgramDenotation.wp_strengthen_lens_preserved_footprint`).
* `ProgramDenotation.EquivModuloLens.to_relE` / `ProgramDenotation.relE.to_equivModuloLens` —
  `EquivModuloLens L p q` is exactly the diagonal `relE` whose post relates
  pairs with equal results and equal `L`-complement content. The existing
  `EquivModuloLens` calculus remains the ergonomic API for the diagonal
  case; this bridge lets its lemmas feed `rel` chains and vice versa.
-/

namespace ProgramDenotation.rel

/-- **Self-shift**: running `p` from `f σ` (for `f` outside `p`'s footprint)
    relates to running `p` from `σ` with the shift carried into the post. -/
lemma self_shift {s α : Type} {p : ProgramDenotation s α} {R : Footprint s}
    (hp : p.inFootprint R) {f : s → s} (hf : diracKer f ∈ Rᶜ.updates) :
    p.rel p (fun σ₁ σ₂ => σ₂ = f σ₁) (fun x y => y.1 = x.1 ∧ y.2 = f x.2) := by
  intro F G hFG σ₁ σ₂ hpre
  subst hpre
  rw [ProgramDenotation.wp_shift_input_prob hp hf]
  apply ProgramDenotation.wp_le_wp_of_le
  intro xs
  exact hFG xs (xs.1, f xs.2) ⟨rfl, rfl⟩

/-- **Framing**: a judgment can be strengthened with value constraints on a
    lens outside each side's footprint. The proof strengthens the left post
    with the `L`-frame (`wp_strengthen_lens_preserved_footprint`) and interpolates the
    right post with a `⊤`-override off the `M`-frame. -/
lemma frame {s₁ s₂ α β γ₁ γ₂ : Type}
    (L : Lens γ₁ s₁) (M : Lens γ₂ s₂)
    {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β}
    (hp : p.inFootprint (L.footprint)ᶜ) (hq : q.inFootprint (M.footprint)ᶜ)
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : p.rel q Pre Post) (v : γ₁) (w : γ₂) :
    p.rel q (fun σ₁ σ₂ => Pre σ₁ σ₂ ∧ L.get σ₁ = v ∧ M.get σ₂ = w)
            (fun x y => Post x y ∧ L.get x.2 = v ∧ M.get y.2 = w) := by
  classical
  intro F G hFG σ₁ σ₂ hpre
  obtain ⟨hpre, hL, hM⟩ := hpre
  calc p.wp F σ₁
      = p.wp (fun x : α × s₁ => if L.get x.2 = L.get σ₁ then F x else 0) σ₁ :=
        ProgramDenotation.wp_strengthen_lens_preserved_footprint L hp F σ₁
    _ ≤ q.wp (fun y : β × s₂ => if M.get y.2 = w then G y else ⊤) σ₂ := by
        apply h.wp_le ?_ hpre
        intro x y hxy
        by_cases hMy : M.get y.2 = w
        · rw [if_pos hMy]
          by_cases hLx : L.get x.2 = L.get σ₁
          · rw [if_pos hLx]
            exact hFG x y ⟨hxy, by rw [hLx, hL], hMy⟩
          · rw [if_neg hLx]
            exact zero_le
        · rw [if_neg hMy]
          exact le_top
    _ = q.wp (fun y : β × s₂ => if M.get y.2 = M.get σ₂ then
          (if M.get y.2 = w then G y else ⊤) else 0) σ₂ :=
        ProgramDenotation.wp_strengthen_lens_preserved_footprint M hq _ σ₂
    _ ≤ q.wp G σ₂ := by
        apply ProgramDenotation.wp_le_wp_of_le
        intro y
        by_cases hMy : M.get y.2 = M.get σ₂
        · rw [if_pos hMy, if_pos (by rw [hMy, hM])]
        · rw [if_neg hMy]
          exact zero_le

end ProgramDenotation.rel

namespace ProgramDenotation.relE

/-- Two-sided form of `ProgramDenotation.rel.self_shift`. -/
lemma self_shift {s α : Type} {p : ProgramDenotation s α} {R : Footprint s}
    (hp : p.inFootprint R) {f : s → s} (hf : diracKer f ∈ Rᶜ.updates) :
    p.relE p (fun σ₁ σ₂ => σ₂ = f σ₁) (fun x y => y.1 = x.1 ∧ y.2 = f x.2) := by
  refine ⟨ProgramDenotation.rel.self_shift hp hf, ?_⟩
  intro F G hFG σ₂ σ₁ hpre
  subst hpre
  rw [ProgramDenotation.wp_shift_input_prob hp hf]
  apply ProgramDenotation.wp_le_wp_of_le
  intro xs
  exact hFG (xs.1, f xs.2) xs ⟨rfl, rfl⟩

/-- Self-shift specialized to a lens write outside `p`'s footprint:
    running `p` from `L.set v σ` vs from `σ`. -/
lemma self_lens_set {s α γ : Type}
    {p : ProgramDenotation s α} (L : Lens γ s) (hp : p.inFootprint (L.footprint)ᶜ) (v : γ) :
    p.relE p (fun σ₁ σ₂ => σ₂ = L.set v σ₁)
             (fun x y => y.1 = x.1 ∧ y.2 = L.set v x.2) := by
  have hf : diracKer (L.liftFunction (Function.const γ v)) ∈ (((L.footprint)ᶜ)ᶜ).updates := by
    rw [Footprint.compl_compl]
    exact L.diracKer_liftFunction_mem_footprint (Function.const γ v)
  exact ProgramDenotation.relE.self_shift hp hf

/-- Two-sided framing. -/
lemma frame {s₁ s₂ α β γ₁ γ₂ : Type}
    (L : Lens γ₁ s₁) (M : Lens γ₂ s₂)
    {p : ProgramDenotation s₁ α} {q : ProgramDenotation s₂ β}
    (hp : p.inFootprint (L.footprint)ᶜ) (hq : q.inFootprint (M.footprint)ᶜ)
    {Pre : s₁ → s₂ → Prop} {Post : α × s₁ → β × s₂ → Prop}
    (h : p.relE q Pre Post) (v : γ₁) (w : γ₂) :
    p.relE q (fun σ₁ σ₂ => Pre σ₁ σ₂ ∧ L.get σ₁ = v ∧ M.get σ₂ = w)
             (fun x y => Post x y ∧ L.get x.2 = v ∧ M.get y.2 = w) := by
  refine ⟨ProgramDenotation.rel.frame L M hp hq h.1 v w, ?_⟩
  exact (ProgramDenotation.rel.frame M L hq hp h.2 w v).conseq
    (fun _ _ hh => ⟨hh.1, hh.2.2, hh.2.1⟩)
    (fun _ _ hh => ⟨hh.1, hh.2.2, hh.2.1⟩)

end ProgramDenotation.relE

/-! ## The EquivModuloLens bridge -/

/-- One direction of the bridge, as a `rel`. -/
private lemma rel_of_equivModuloLens {s α γ : Type} {L : Lens γ s}
    {p q : ProgramDenotation s α} (h : ProgramDenotation.EquivModuloLens L p q) :
    p.rel q Eq (fun x y => x.1 = y.1 ∧ L.compl.get x.2 = L.compl.get y.2) := by
  intro F G hFG σ₁ σ₂ hpre
  subst hpre
  have hH_ign : IgnoresLens L
      (fun x : α × s => ⨅ y : α × s,
        ⨅ (_ : x.1 = y.1 ∧ L.compl.get x.2 = L.compl.get y.2), G y) := by
    intro x v
    have hcg : L.compl.get (L.set v x.2) = L.compl.get x.2 :=
      (Quotient.sound (s := L.equal_outside_setoid) ⟨v, rfl⟩).symm
    dsimp only
    simp only [hcg]
  calc p.wp F σ₁
      ≤ p.wp (fun x : α × s => ⨅ y : α × s,
          ⨅ (_ : x.1 = y.1 ∧ L.compl.get x.2 = L.compl.get y.2), G y) σ₁ := by
        apply ProgramDenotation.wp_le_wp_of_le
        intro x
        exact le_iInf₂ (fun y hy => hFG x y hy)
    _ = q.wp (fun x : α × s => ⨅ y : α × s,
          ⨅ (_ : x.1 = y.1 ∧ L.compl.get x.2 = L.compl.get y.2), G y) σ₁ :=
        h _ hH_ign σ₁
    _ ≤ q.wp G σ₁ := by
        apply ProgramDenotation.wp_le_wp_of_le
        intro x
        exact iInf₂_le x ⟨rfl, rfl⟩

/-- **EquivModuloLens → relE**: an equivalence-modulo-`L` is the diagonal
    `relE` at the post "equal results, equal `L`-complement content". -/
lemma ProgramDenotation.EquivModuloLens.to_relE {s α γ : Type} {L : Lens γ s}
    {p q : ProgramDenotation s α} (h : ProgramDenotation.EquivModuloLens L p q) :
    p.relE q Eq (fun x y => x.1 = y.1 ∧ L.compl.get x.2 = L.compl.get y.2) :=
  ⟨rel_of_equivModuloLens h,
   (rel_of_equivModuloLens h.symm).conseq
     (fun _ _ hab => hab.symm)
     (fun _ _ hyx => ⟨hyx.1.symm, hyx.2.symm⟩)⟩

/-- **relE → EquivModuloLens**: conversely, the diagonal `relE` at the
    `L`-complement-equality post yields an equivalence-modulo-`L`. -/
lemma ProgramDenotation.relE.to_equivModuloLens {s α γ : Type} {L : Lens γ s}
    {p q : ProgramDenotation s α}
    (h : p.relE q Eq (fun x y => x.1 = y.1 ∧ L.compl.get x.2 = L.compl.get y.2)) :
    ProgramDenotation.EquivModuloLens L p q := by
  intro F hF σ
  apply h.wp_eq ?_ rfl
  intro x y hxy
  obtain ⟨h1, h2⟩ := hxy
  have h2' : Quotient.mk L.equal_outside_setoid x.2
           = Quotient.mk L.equal_outside_setoid y.2 := h2
  have hxy2 : L.equal_outside x.2 y.2 := Quotient.exact h2'
  obtain ⟨v, hv⟩ := hxy2
  calc F x = F (x.1, L.set v x.2) := (hF x v).symm
    _ = F (y.1, y.2) := by rw [hv, h1]
    _ = F y := rfl

end GaudisCrypt
