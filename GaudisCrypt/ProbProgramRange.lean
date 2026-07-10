import GaudisCrypt.WeakestPreconditions
import GaudisCrypt.Footprint

/-!
# Prob program-range wp-layer

The `Footprint` analogue of the wp-layer in `ProgramRange` (countability-free): pushing a
deterministic outside-update across `wp` (`wp_shift_input_prob`), and the lens-preservation
bounds (`wp_le_of_factors_footprint` and its 2- and 3-lens forms, `wp_strengthen_lens_preserved_footprint`).
Foundation for migrating the RO crypto stack off `DetermFootprint`/`inRange`.
-/

open GaudisCrypt

namespace GaudisCrypt


/-- **`wp_shift_input` over `Footprint`** — countability-free. The probabilistic analogue of
    `ProgramDenotation.wp_shift_input`: a program in range `R` lets a deterministic outside-update
        `f` (a Dirac
    kernel in `Rᶜ`) be pushed from the input to the output of `wp`.  Same proof, via
    `inFootprint_subprob`. -/
lemma ProgramDenotation.wp_shift_input_prob {s a : Type} {p : ProgramDenotation s a} {R : Footprint
    s}
    (hp : p.inFootprint R) {f : s → s} (hf : diracKer f ∈ Rᶜ.updates) (F : a × s → ENNReal) (σ : s) :
    p.wp F (f σ) = p.wp (fun (xs : a × s) => F (xs.1, f xs.2)) σ := by
  show (p (f σ)).expected F = (p σ).expected (fun (xs : a × s) => F (xs.1, f xs.2))
  rw [inFootprint_subprob hp hf σ]
  rw [SubProbability.expected_bind]
  congr 1
  funext xs
  rw [expected_pure]


/-- **Preservation under in-range, over `Footprint`** — countability-free analogue of
    `ProgramDenotation.wp_le_of_factors`: if `prog`'s probabilistic footprint avoids `L`
        (`inFootprint
    (L.footprint)ᶜ`) and `P` factors through `L.get`, then `prog.wp (P ∘ snd) σ ≤ P σ`. -/
lemma ProgramDenotation.wp_le_of_factors_footprint {s α γ : Type} (L : Lens γ s)
    {prog : ProgramDenotation s α} (h_inRange : prog.inFootprint (L.footprint)ᶜ)
    {P : s → ENNReal}
    (h_factors : ∀ σ σ', L.get σ' = L.get σ → P σ' = P σ)
    (σ : s) :
    prog.wp (fun xs : α × s => P xs.2) σ ≤ P σ := by
  set f : s → s := L.liftFunction (Function.const _ (L.get σ)) with hf_def
  have h_f_in_Rc : diracKer f ∈ (((L.footprint)ᶜ)ᶜ).updates := by
    rw [Footprint.compl_compl]
    exact L.diracKer_liftFunction_mem_footprint _
  have h_f_fix : f σ = σ := by
    show L.set ((Function.const _ (L.get σ)) (L.get σ)) σ = σ
    rw [Function.const_apply, L.get_set]
  have h_f_P : ∀ σ' : s, P (f σ') = P σ := by
    intro σ'
    apply h_factors
    show L.get (L.set ((Function.const _ (L.get σ)) (L.get σ')) σ') = L.get σ
    rw [Function.const_apply, L.set_get]
  have h_shift := ProgramDenotation.wp_shift_input_prob h_inRange h_f_in_Rc (fun xs : α × s => P
      xs.2) σ
  rw [h_f_fix] at h_shift
  rw [h_shift]
  rw [show (fun xs : α × s => P (f xs.2)) = (fun _ : α × s => P σ) from by
    funext xs; exact h_f_P xs.2]
  exact ProgramDenotation.wp_const_le prog (P σ) σ


/-- **Lens-preservation strengthening over `Footprint`** — countability-free analogue of
    `ProgramDenotation.wp_strengthen_lens_preserved`. -/
lemma ProgramDenotation.wp_strengthen_lens_preserved_footprint {s α γ : Type} [DecidableEq γ]
    (L : Lens γ s) {p : ProgramDenotation s α} (h_inRange : p.inFootprint (L.footprint)ᶜ)
    (F : α × s → ENNReal) (σ : s) :
    p.wp F σ
      = p.wp (fun aσ' : α × s => if L.get aσ'.2 = L.get σ then F aσ' else 0) σ := by
  set f : s → s := L.liftFunction (Function.const _ (L.get σ)) with hf_def
  have h_f_in_Rc : diracKer f ∈ (((L.footprint)ᶜ)ᶜ).updates := by
    rw [Footprint.compl_compl]
    exact L.diracKer_liftFunction_mem_footprint _
  have h_f_fix : f σ = σ := by
    show L.set ((Function.const _ (L.get σ)) (L.get σ)) σ = σ
    rw [Function.const_apply, L.get_set]
  have h_f_L_get : ∀ σ' : s, L.get (f σ') = L.get σ := by
    intro σ'
    show L.get (L.set ((Function.const _ (L.get σ)) (L.get σ')) σ') = L.get σ
    rw [Function.const_apply, L.set_get]
  have h_shift_F := ProgramDenotation.wp_shift_input_prob h_inRange h_f_in_Rc F σ
  rw [h_f_fix] at h_shift_F
  have h_shift_strong := ProgramDenotation.wp_shift_input_prob h_inRange h_f_in_Rc
    (fun aσ' : α × s => if L.get aσ'.2 = L.get σ then F aσ' else 0) σ
  rw [h_f_fix] at h_shift_strong
  rw [h_shift_F, h_shift_strong]
  congr 1
  funext xs
  show F (xs.1, f xs.2) = if L.get (f xs.2) = L.get σ then F (xs.1, f xs.2) else 0
  rw [if_pos (h_f_L_get xs.2)]


/-- **Two-lens preservation over `Footprint`** — countability-free analogue of
    `ProgramDenotation.wp_le_of_factors_two`. -/
lemma ProgramDenotation.wp_le_of_factors_two_footprint {s α γ₁ γ₂ : Type}
    [DecidableEq γ₁] [DecidableEq γ₂]
    (L₁ : Lens γ₁ s) (L₂ : Lens γ₂ s)
    {prog : ProgramDenotation s α}
    (h₁ : prog.inFootprint (L₁.footprint)ᶜ) (h₂ : prog.inFootprint (L₂.footprint)ᶜ)
    {P : s → ENNReal}
    (h_factors : ∀ σ σ' : s,
        L₁.get σ' = L₁.get σ → L₂.get σ' = L₂.get σ → P σ' = P σ)
    (σ : s) :
    prog.wp (fun xs : α × s => P xs.2) σ ≤ P σ := by
  rw [ProgramDenotation.wp_strengthen_lens_preserved_footprint L₂ h₂]
  rw [ProgramDenotation.wp_strengthen_lens_preserved_footprint L₁ h₁]
  calc prog.wp _ σ
      ≤ prog.wp (fun _ : α × s => P σ) σ := by
        apply ProgramDenotation.wp_le_wp_of_le
        rintro ⟨_, σ'⟩; dsimp only
        split_ifs with h1 h2
        · exact le_of_eq (h_factors σ σ' h1 h2)
        all_goals exact bot_le
    _ ≤ P σ := ProgramDenotation.wp_const_le prog _ σ


/-- **Three-lens preservation over `Footprint`** — countability-free analogue of
    `ProgramDenotation.wp_le_of_factors_three`. -/
lemma ProgramDenotation.wp_le_of_factors_three_footprint {s α γ₁ γ₂ γ₃ : Type}
    [DecidableEq γ₁] [DecidableEq γ₂] [DecidableEq γ₃]
    (L₁ : Lens γ₁ s) (L₂ : Lens γ₂ s) (L₃ : Lens γ₃ s)
    {prog : ProgramDenotation s α}
    (h₁ : prog.inFootprint (L₁.footprint)ᶜ)
    (h₂ : prog.inFootprint (L₂.footprint)ᶜ)
    (h₃ : prog.inFootprint (L₃.footprint)ᶜ)
    {P : s → ENNReal}
    (h_factors : ∀ σ σ' : s,
        L₁.get σ' = L₁.get σ → L₂.get σ' = L₂.get σ →
        L₃.get σ' = L₃.get σ → P σ' = P σ)
    (σ : s) :
    prog.wp (fun xs : α × s => P xs.2) σ ≤ P σ := by
  rw [ProgramDenotation.wp_strengthen_lens_preserved_footprint L₃ h₃]
  rw [ProgramDenotation.wp_strengthen_lens_preserved_footprint L₂ h₂]
  rw [ProgramDenotation.wp_strengthen_lens_preserved_footprint L₁ h₁]
  calc prog.wp _ σ
      ≤ prog.wp (fun _ : α × s => P σ) σ := by
        apply ProgramDenotation.wp_le_wp_of_le
        rintro ⟨_, σ'⟩; dsimp only
        split_ifs with h1 h2 h3
        · exact le_of_eq (h_factors σ σ' h1 h2 h3)
        all_goals exact bot_le
    _ ≤ P σ := ProgramDenotation.wp_const_le prog _ σ

/-- **Dead write across a disjoint footprint** — the `inFootprint` analogue of
    `ProgramDenotation.wp_set_disjoint_no_op`. If `rest` lives in `(L.footprint)ᶜ` and the post `F`
    ignores `L`, then a preceding `ProgramDenotation.set L v` is a no-op for the `wp`. -/
lemma ProgramDenotation.wp_set_disjoint_no_op_footprint {s γ : Type} [DecidableEq γ] {L : Lens γ s}
    {α : Type} {rest : ProgramDenotation s α} (h_rest : rest.inFootprint (L.footprint)ᶜ)
    (v : γ) (F : α × s → ENNReal)
    (h_F : ∀ aσ : α × s, F (aσ.1, L.set v aσ.2) = F aσ)
    (σ : s) :
    (ProgramDenotation.set L v >>= fun _ => rest).wp F σ = rest.wp F σ := by
  simp only [wp_bind, wp_set]
  set f : s → s := L.liftFunction (Function.const _ v) with hf_def
  have h_f_in_Rc : diracKer f ∈ (((L.footprint)ᶜ)ᶜ).updates := by
    rw [Footprint.compl_compl]
    exact L.diracKer_liftFunction_mem_footprint _
  have h_f_eq : ∀ σ', f σ' = L.set v σ' := fun σ' => by
    show L.set (Function.const _ v (L.get σ')) σ' = L.set v σ'
    rw [Function.const_apply]
  rw [← h_f_eq σ]
  rw [ProgramDenotation.wp_shift_input_prob h_rest h_f_in_Rc]
  congr 1
  funext xs
  rw [h_f_eq xs.2]
  exact h_F xs

end GaudisCrypt
