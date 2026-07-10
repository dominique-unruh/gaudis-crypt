import GaudisCrypt.WeakestPreconditions
import GaudisCrypt.Language.Footprint

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

/-- **wp vanishes on a preserved-lens zero region** — the `inFootprint` analogue of
    `ProgramDenotation.wp_zero_of_lens_preserves`: if `p` avoids `L`, `F` vanishes whenever
    `L.get = v`, and we start at `L.get σ = v`, then `p.wp F σ = 0`. -/
lemma ProgramDenotation.wp_zero_of_lens_preserves_footprint {s α γ : Type} [DecidableEq γ]
    {L : Lens γ s} {p : ProgramDenotation s α} (h_p : p.inFootprint (L.footprint)ᶜ)
    {F : α × s → ENNReal} {v : γ}
    (h_F_zero : ∀ aσ : α × s, L.get aσ.2 = v → F aσ = 0)
    {σ : s} (h_σ : L.get σ = v) :
    p.wp F σ = 0 := by
  rw [ProgramDenotation.wp_strengthen_lens_preserved_footprint L h_p]
  rw [show (fun aσ : α × s =>
            if L.get aσ.2 = L.get σ then F aσ else 0)
          = (fun _ : α × s => (0 : ENNReal)) from by
    funext aσ
    by_cases h : L.get aσ.2 = L.get σ
    · simp only [if_pos h]
      exact h_F_zero aσ (h.trans h_σ)
    · simp only [if_neg h]]
  exact ProgramDenotation.wp_zero_post _ _

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

/-- **Conditional dead write across a disjoint footprint** — the `inFootprint` analogue of
    `ProgramDenotation.wp_conditional_set_disjoint_no_op`. -/
lemma ProgramDenotation.wp_conditional_set_disjoint_no_op_footprint {s γ : Type} [DecidableEq γ]
    {L : Lens γ s} {α : Type} (cond : Prop) [Decidable cond] (v : γ)
    {rest : ProgramDenotation s α} (h_rest : rest.inFootprint (L.footprint)ᶜ)
    (F : α × s → ENNReal)
    (h_F : ∀ aσ : α × s, F (aσ.1, L.set v aσ.2) = F aσ)
    (σ : s) :
    ((if cond then ProgramDenotation.set L v else pure ()) >>= fun _ => rest).wp F σ
    = rest.wp F σ := by
  by_cases h : cond
  · rw [if_pos h]
    exact ProgramDenotation.wp_set_disjoint_no_op_footprint h_rest v F h_F σ
  · rw [if_neg h]
    simp only [wp_bind, wp_pure]

/-- **Get-then-conditional-set is a no-op** across a disjoint footprint — the `inFootprint`
    analogue of `ProgramDenotation.wp_get_then_conditional_set_disjoint_no_op`. -/
lemma ProgramDenotation.wp_get_then_conditional_set_disjoint_no_op_footprint
    {s γ δ : Type} [DecidableEq γ] {L_get : Lens δ s} {L_set : Lens γ s}
    {α : Type} (pred : δ → Prop) [DecidablePred pred] (v : γ)
    {rest : ProgramDenotation s α} (h_rest : rest.inFootprint (L_set.footprint)ᶜ)
    (F : α × s → ENNReal)
    (h_F : ∀ aσ : α × s, F (aσ.1, L_set.set v aσ.2) = F aσ)
    (σ : s) :
    (ProgramDenotation.get L_get >>= fun cx =>
        (if pred cx then ProgramDenotation.set L_set v else (pure () : ProgramDenotation s Unit))
          >>= fun _ => rest).wp F σ
    = rest.wp F σ := by
  rw [wp_bind, wp_get]
  exact ProgramDenotation.wp_conditional_set_disjoint_no_op_footprint
    (pred (L_get.get σ)) v h_rest F h_F σ

/-- **A state-independent sampled value has trivial probabilistic footprint** — the `Footprint`
    analogue of `ProgramDenotation.inRange_toProgramDenotation` (at `⊥`; lift to any `R` with
    `inFootprint_mono … bot_le`). Same swap argument as `inFootprint_uniform`. -/
theorem ProgramDenotation.inFootprint_toProgramDenotation {s a : Type} (μ : SubProbability a) :
    (SubProbability.toProgramDenotation μ : ProgramDenotation s a).inFootprint ⊥ := by
  rw [inFootprint_iff_clean]
  intro f hf
  funext st
  change (f st >>= fun st' => μ >>= fun x => (pure (x, st') : SubProbability (a × s)))
     = ((μ >>= fun x => (pure (x, st) : SubProbability (a × s)))
          >>= fun w : a × s => f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))
  rw [bind_swap (f st) μ (fun x st' => pure (x, st'))]
  rw [SubProbability.bind_assoc]
  congr 1; funext x
  rw [SubProbability.pure_bind]

/-- `ProgramDenotation.uniformOfFinset` has trivial probabilistic footprint — the `Footprint`
    analogue of `ProgramDenotation.inRange_uniformOfFinset`. -/
theorem ProgramDenotation.inFootprint_uniformOfFinset {s α : Type}
    (fs : Finset α) (hs : fs.Nonempty) :
    (ProgramDenotation.uniformOfFinset fs hs : ProgramDenotation s α).inFootprint ⊥ :=
  ProgramDenotation.inFootprint_toProgramDenotation _

/-- `loop_n n body` stays in the same footprint as `body` — the `Footprint` analogue of
    `loop_n_inRange`. -/
lemma loop_n_inFootprint {s : Type} {R : Footprint s}
    (body : ProgramDenotation s Unit) (h_body : body.inFootprint R) (n : ℕ) :
    (loop_n n body).inFootprint R := by
  induction n with
  | zero => exact ProgramDenotation.inFootprint_pure _ _
  | succ n ih =>
    change (body >>= fun _ => loop_n n body).inFootprint R
    exact ProgramDenotation.inFootprint_bind h_body (fun _ => ih)

/-- `L`-ignoring is preserved when post-composing with an `L`-disjoint program — the `Footprint`
    analogue of `IgnoresLens.comp_inRange`. -/
lemma IgnoresLens.comp_inFootprint {γ s α β : Type} {L : Lens γ s}
    {F : β × s → ENNReal} (h_F : IgnoresLens L F)
    (k : α → ProgramDenotation s β) (h_k : ∀ a, (k a).inFootprint (L.footprint)ᶜ) :
    IgnoresLens L (fun aσ : α × s => (k aσ.1).wp F aσ.2) := by
  intro aσ v
  have hf : diracKer (fun s' : s => L.set v s') ∈ (((L.footprint)ᶜ)ᶜ).updates := by
    rw [Footprint.compl_compl]
    exact L.diracKer_liftFunction_mem_footprint (Function.const _ v)
  change (k aσ.1).wp F (L.set v aσ.2) = (k aσ.1).wp F aσ.2
  rw [ProgramDenotation.wp_shift_input_prob (h_k aσ.1) hf]
  congr 1
  funext xs
  exact h_F xs v

/-- **Factorization**: a program confined to `L`'s probabilistic range comes from running some
    inner program on the `L`-content. The `inFootprint` analogue of `Lens.factor_of_inRange`. -/
theorem factor_of_inFootprint {c s a : Type} [Nonempty s] (L : Lens c s) {Adv : ProgramDenotation s
    a}
    (h : Adv.inFootprint L.footprint) : Adv = L.lift (L.factor Adv) := by
  funext σ
  set f : s → s := fun σ' => L.set (L.get σ') σ with hf_def
  have h_fσ_pad : f (L.set (L.get σ) (Classical.arbitrary s)) = σ := by
    show L.set (L.get (L.set (L.get σ) (Classical.arbitrary s))) σ = σ
    rw [L.set_get, L.get_set]
  have h_f_mem : diracKer f ∈ ((L.footprint)ᶜ).updates := by
    haveI : disjoint L.compl L := ⟨fun st v w => by
      induction v using Quotient.inductionOn
      rename_i u
      show L.set (L.get (L.set w st)) u = L.set w (L.set (L.get st) u)
      rw [L.set_get, L.set_set]⟩
    exact Lens.footprint_le_compl_of_disjoint L.compl L
      (L.compl.diracKer_liftFunction_mem_footprint (Function.const _ (Quotient.mk _ σ)))
  have h_iv : Adv σ
      = (Adv (L.set (L.get σ) (Classical.arbitrary s)))
          >>= (fun xs : a × s => (pure (xs.1, f xs.2) : SubProbability (a × s))) := by
    conv_lhs => rw [← h_fσ_pad]
    exact inFootprint_subprob h h_f_mem _
  change Adv σ
      = ((Adv (L.set (L.get σ) (Classical.arbitrary s)))
            >>= fun xσ' : a × s => (pure (xσ'.1, L.get xσ'.2) : SubProbability (a × c)))
          >>= fun xc : a × c => (pure (xc.1, L.set xc.2 σ) : SubProbability (a × s))
  rw [h_iv, SubProbability.bind_assoc']
  congr 1; funext xσ'
  rw [SubProbability.pure_bind]

end GaudisCrypt
