import GaudisCrypt.WeakestPreconditions
import GaudisCrypt.ProbLensRange

/-!
# Prob program-range wp-layer

The `ProbLensRange` analogue of the wp-layer in `ProgramRange` (countability-free): pushing a
deterministic outside-update across `wp` (`wp_shift_input_prob`), and the lens-preservation
bounds (`wp_le_of_factors_prob` and its 2- and 3-lens forms, `wp_strengthen_lens_preserved_prob`).
Foundation for migrating the RO crypto stack off `TotLensRange`/`inRange`.
-/

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics


/-- **`wp_shift_input` over `ProbLensRange`** — countability-free. The probabilistic analogue of
    `Program.wp_shift_input`: a program in range `R` lets a deterministic outside-update `f` (a Dirac
    kernel in `Rᶜ`) be pushed from the input to the output of `wp`.  Same proof, via
    `inProbRange_subprob`. -/
lemma Program.wp_shift_input_prob {s a : Type} {p : Program s a} {R : ProbLensRange s}
    (hp : p.inProbRange R) {f : s → s} (hf : diracKer f ∈ Rᶜ.updates) (F : a × s → ENNReal) (σ : s) :
    p.wp F (f σ) = p.wp (fun (xs : a × s) => F (xs.1, f xs.2)) σ := by
  show (p (f σ)).expected F = (p σ).expected (fun (xs : a × s) => F (xs.1, f xs.2))
  rw [inProbRange_subprob hp hf σ]
  rw [SubProbability.expected_bind]
  congr 1
  funext xs
  rw [expected_pure]


/-- **Preservation under in-range, over `ProbLensRange`** — countability-free analogue of
    `Program.wp_le_of_factors`: if `prog`'s probabilistic footprint avoids `L` (`inProbRange
    (L.probRange)ᶜ`) and `P` factors through `L.get`, then `prog.wp (P ∘ snd) σ ≤ P σ`. -/
lemma Program.wp_le_of_factors_prob {s α γ : Type} (L : Lens γ s)
    {prog : Program s α} (h_inRange : prog.inProbRange (L.probRange)ᶜ)
    {P : s → ENNReal}
    (h_factors : ∀ σ σ', L.get σ' = L.get σ → P σ' = P σ)
    (σ : s) :
    prog.wp (fun xs : α × s => P xs.2) σ ≤ P σ := by
  set f : s → s := L.liftFunction (Function.const _ (L.get σ)) with hf_def
  have h_f_in_Rc : diracKer f ∈ (((L.probRange)ᶜ)ᶜ).updates := by
    rw [ProbLensRange.compl_compl]
    exact (ProbLensRange.from_le_iff (Set.range fun g : Function.End γ => diracKer (L.liftFunction g))
      L.probRange).mp le_rfl ⟨Function.const _ (L.get σ), rfl⟩
  have h_f_fix : f σ = σ := by
    show L.set ((Function.const _ (L.get σ)) (L.get σ)) σ = σ
    rw [Function.const_apply, L.get_set]
  have h_f_P : ∀ σ' : s, P (f σ') = P σ := by
    intro σ'
    apply h_factors
    show L.get (L.set ((Function.const _ (L.get σ)) (L.get σ')) σ') = L.get σ
    rw [Function.const_apply, L.set_get]
  have h_shift := Program.wp_shift_input_prob h_inRange h_f_in_Rc (fun xs : α × s => P xs.2) σ
  rw [h_f_fix] at h_shift
  rw [h_shift]
  rw [show (fun xs : α × s => P (f xs.2)) = (fun _ : α × s => P σ) from by
    funext xs; exact h_f_P xs.2]
  exact Program.wp_const_le prog (P σ) σ


/-- **Lens-preservation strengthening over `ProbLensRange`** — countability-free analogue of
    `Program.wp_strengthen_lens_preserved`. -/
lemma Program.wp_strengthen_lens_preserved_prob {s α γ : Type} [DecidableEq γ]
    (L : Lens γ s) {p : Program s α} (h_inRange : p.inProbRange (L.probRange)ᶜ)
    (F : α × s → ENNReal) (σ : s) :
    p.wp F σ
      = p.wp (fun aσ' : α × s => if L.get aσ'.2 = L.get σ then F aσ' else 0) σ := by
  set f : s → s := L.liftFunction (Function.const _ (L.get σ)) with hf_def
  have h_f_in_Rc : diracKer f ∈ (((L.probRange)ᶜ)ᶜ).updates := by
    rw [ProbLensRange.compl_compl]
    exact (ProbLensRange.from_le_iff (Set.range fun g : Function.End γ => diracKer (L.liftFunction g))
      L.probRange).mp le_rfl ⟨Function.const _ (L.get σ), rfl⟩
  have h_f_fix : f σ = σ := by
    show L.set ((Function.const _ (L.get σ)) (L.get σ)) σ = σ
    rw [Function.const_apply, L.get_set]
  have h_f_L_get : ∀ σ' : s, L.get (f σ') = L.get σ := by
    intro σ'
    show L.get (L.set ((Function.const _ (L.get σ)) (L.get σ')) σ') = L.get σ
    rw [Function.const_apply, L.set_get]
  have h_shift_F := Program.wp_shift_input_prob h_inRange h_f_in_Rc F σ
  rw [h_f_fix] at h_shift_F
  have h_shift_strong := Program.wp_shift_input_prob h_inRange h_f_in_Rc
    (fun aσ' : α × s => if L.get aσ'.2 = L.get σ then F aσ' else 0) σ
  rw [h_f_fix] at h_shift_strong
  rw [h_shift_F, h_shift_strong]
  congr 1
  funext xs
  show F (xs.1, f xs.2) = if L.get (f xs.2) = L.get σ then F (xs.1, f xs.2) else 0
  rw [if_pos (h_f_L_get xs.2)]


/-- **Two-lens preservation over `ProbLensRange`** — countability-free analogue of
    `Program.wp_le_of_factors_two`. -/
lemma Program.wp_le_of_factors_two_prob {s α γ₁ γ₂ : Type}
    [DecidableEq γ₁] [DecidableEq γ₂]
    (L₁ : Lens γ₁ s) (L₂ : Lens γ₂ s)
    {prog : Program s α}
    (h₁ : prog.inProbRange (L₁.probRange)ᶜ) (h₂ : prog.inProbRange (L₂.probRange)ᶜ)
    {P : s → ENNReal}
    (h_factors : ∀ σ σ' : s,
        L₁.get σ' = L₁.get σ → L₂.get σ' = L₂.get σ → P σ' = P σ)
    (σ : s) :
    prog.wp (fun xs : α × s => P xs.2) σ ≤ P σ := by
  rw [Program.wp_strengthen_lens_preserved_prob L₂ h₂]
  rw [Program.wp_strengthen_lens_preserved_prob L₁ h₁]
  calc prog.wp _ σ
      ≤ prog.wp (fun _ : α × s => P σ) σ := by
        apply Program.wp_le_wp_of_le
        rintro ⟨_, σ'⟩; dsimp only
        split_ifs with h1 h2
        · exact le_of_eq (h_factors σ σ' h1 h2)
        all_goals exact bot_le
    _ ≤ P σ := Program.wp_const_le prog _ σ


/-- **Three-lens preservation over `ProbLensRange`** — countability-free analogue of
    `Program.wp_le_of_factors_three`. -/
lemma Program.wp_le_of_factors_three_prob {s α γ₁ γ₂ γ₃ : Type}
    [DecidableEq γ₁] [DecidableEq γ₂] [DecidableEq γ₃]
    (L₁ : Lens γ₁ s) (L₂ : Lens γ₂ s) (L₃ : Lens γ₃ s)
    {prog : Program s α}
    (h₁ : prog.inProbRange (L₁.probRange)ᶜ)
    (h₂ : prog.inProbRange (L₂.probRange)ᶜ)
    (h₃ : prog.inProbRange (L₃.probRange)ᶜ)
    {P : s → ENNReal}
    (h_factors : ∀ σ σ' : s,
        L₁.get σ' = L₁.get σ → L₂.get σ' = L₂.get σ →
        L₃.get σ' = L₃.get σ → P σ' = P σ)
    (σ : s) :
    prog.wp (fun xs : α × s => P xs.2) σ ≤ P σ := by
  rw [Program.wp_strengthen_lens_preserved_prob L₃ h₃]
  rw [Program.wp_strengthen_lens_preserved_prob L₂ h₂]
  rw [Program.wp_strengthen_lens_preserved_prob L₁ h₁]
  calc prog.wp _ σ
      ≤ prog.wp (fun _ : α × s => P σ) σ := by
        apply Program.wp_le_wp_of_le
        rintro ⟨_, σ'⟩; dsimp only
        split_ifs with h1 h2 h3
        · exact le_of_eq (h_factors σ σ' h1 h2 h3)
        all_goals exact bot_le
    _ ≤ P σ := Program.wp_const_le prog _ σ

/-- **Dead write across a disjoint footprint** — the `inProbRange` analogue of
    `Program.wp_set_disjoint_no_op`. If `rest` lives in `(L.probRange)ᶜ` and the post `F`
    ignores `L`, then a preceding `Program.set L v` is a no-op for the `wp`. -/
lemma Program.wp_set_disjoint_no_op_prob {s γ : Type} [DecidableEq γ] {L : Lens γ s}
    {α : Type} {rest : Program s α} (h_rest : rest.inProbRange (L.probRange)ᶜ)
    (v : γ) (F : α × s → ENNReal)
    (h_F : ∀ aσ : α × s, F (aσ.1, L.set v aσ.2) = F aσ)
    (σ : s) :
    (Program.set L v >>= fun _ => rest).wp F σ = rest.wp F σ := by
  simp only [wp_bind, wp_set]
  set f : s → s := L.liftFunction (Function.const _ v) with hf_def
  have h_f_in_Rc : diracKer f ∈ (((L.probRange)ᶜ)ᶜ).updates := by
    rw [ProbLensRange.compl_compl]
    exact (ProbLensRange.from_le_iff _ L.probRange).mp le_rfl ⟨Function.const _ v, rfl⟩
  have h_f_eq : ∀ σ', f σ' = L.set v σ' := fun σ' => by
    show L.set (Function.const _ v (L.get σ')) σ' = L.set v σ'
    rw [Function.const_apply]
  rw [← h_f_eq σ]
  rw [Program.wp_shift_input_prob h_rest h_f_in_Rc]
  congr 1
  funext xs
  rw [h_f_eq xs.2]
  exact h_F xs
