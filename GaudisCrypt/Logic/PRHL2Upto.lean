import GaudisCrypt.Logic.PRHL2

open GaudisCrypt

namespace GaudisCrypt

/-!
# pRHL, version 2 — synchronized `while` with an exit

`ProgramDenotation.prhl2.while_loop` (`PRHL2.lean`) couples two loops whose guards agree at
every iteration.  This module proves `ProgramDenotation.prhl2.while_upto`, the variant needed
for an EasyCrypt-style up-to-bad call rule: at the start of any iteration where the `Exit`
predicate holds (together with the invariant), the guard/body couplings are abandoned and the
two *remaining whole loops* are coupled by a separately supplied coupling `h_exit` (after the
bad event, the runs are typically coupled as a product, and their guards need no longer agree).

## Proof outline

The witness is again the least fixed point of a coupling transformer `Φ`, which at a state
pair runs the exit coupling if `Exit` holds and otherwise the guard coupling followed (while it
fires) by the body coupling and a recursive call.  The support follows by induction on the
Kleene iterates.  The marginals are no longer the loop's Kleene iterates (in the exit branch the
marginal is the *whole* remaining loop), so instead each iterate's marginal is sandwiched, in
expectation, between the loop's `n`-th Kleene iterate and the loop itself
(`while_iterate_le_while_loop`, `while_loop_eq_iteration`); the suprema then agree.
-/

universe u

/-- Monotonicity of `expected` on the support: an integrand that is pointwise smaller on the
    support integrates to a smaller value. -/
lemma SubProbability.expected_mono_of_satisfies {X : Type u} {μ : SubProbability X}
    {P : X → Prop} (hP : μ.satisfies P) {F G : X → ENNReal} (h : ∀ x, P x → F x ≤ G x) :
    μ.expected F ≤ μ.expected G := by
  rw [SubProbability.expected_eq_tsum, SubProbability.expected_eq_tsum]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : μ.1 {x} = 0
  · rw [hx, mul_zero, mul_zero]
  · gcongr
    exact h x (hP x hx)

/-- Expectation of a function of the first coordinate, through the first marginal. -/
private lemma expected_fst_of_map_eq {X Y : Type u} {μ : SubProbability (X × Y)}
    {ν : SubProbability X} (h : (μ >>= fun x => (pure x.1 : SubProbability X)) = ν)
    (F : X → ENNReal) : μ.expected (fun x => F x.1) = ν.expected F := by
  rw [← h, SubProbability.expected_map]

/-- Expectation of a function of the second coordinate, through the second marginal. -/
private lemma expected_snd_of_map_eq {X Y : Type u} {μ : SubProbability (X × Y)}
    {ν : SubProbability Y} (h : (μ >>= fun x => (pure x.2 : SubProbability Y)) = ν)
    (F : Y → ENNReal) : μ.expected (fun x => F x.2) = ν.expected F := by
  rw [← h, SubProbability.expected_map]

/-- The `while` loop is a fixed point of its iteration functional, at every state. -/
lemma while_loop_eq_iteration {s : Type u} (cond : ProgramDenotation s Bool)
    (body : ProgramDenotation s Unit) (σ : s) :
    while_loop cond body σ
      = while_iteration cond body (fun _ => while_loop cond body) () σ :=
  (congrFun (congrFun (ContinuousHom.map_lfp
    (while_iteration cond body)) ()) σ).symm

/-- One step of the `while_iteration` functional, in expectation. -/
lemma expected_while_iteration {s : Type u} (cond : ProgramDenotation s Bool)
    (body : ProgramDenotation s Unit) (fp : Unit → ProgramDenotation s Unit) (σ : s)
    (G : Unit × s → ENNReal) :
    (while_iteration cond body fp () σ).expected G
      = (cond σ).expected (fun b =>
          if b.1 then (body b.2).expected (fun u => (fp () u.2).expected G)
          else G ((), b.2)) := by
  rw [while_iteration_apply, SubProbability.expected_bind]
  refine SubProbability.expected_congr _ (fun b => ?_)
  split_ifs
  · rw [SubProbability.expected_bind]
  · rw [expected_pure]

/-- Every Kleene iterate of the loop is below the loop, in expectation. -/
lemma while_iterate_le_while_loop {s : Type u} (cond : ProgramDenotation s Bool)
    (body : ProgramDenotation s Unit) (n : ℕ) (σ : s) (G : Unit × s → ENNReal) :
    ((while_iteration cond body)^[n] ⊥ () σ).expected G
      ≤ (while_loop cond body σ).expected G := by
  rw [expected_while_lfp_iSup]
  exact le_iSup (fun n => ((while_iteration cond body)^[n] ⊥ () σ).expected G) n

/-- **Synchronized while rule with an exit.**  As `ProgramDenotation.prhl2.while_loop`: under
    the invariant (and while `Exit` fails) the guards are coupled to agree, refining the
    invariant to `PostC`, and the bodies preserve the invariant from `PostC true`.  In addition,
    at the start of any iteration where `Exit` holds, the two remaining whole loops are related
    by the coupling `h_exit` with post `PostE`.  The loops then relate either at `PostC false`
    (both guards failed together, before an exit) or at `PostE` (an exit was taken).

    The witness is `Φ.lfp`, the least fixed point of the coupling transformer that runs the
    exit coupling if `Exit` holds and otherwise the guard coupling and, while it fires, the body
    coupling.  Its marginals are sandwiched between the loop's Kleene iterates and the loop. -/
theorem ProgramDenotation.prhl2.while_upto {s₁ s₂ : Type u}
    {cond₁ : ProgramDenotation s₁ Bool} {body₁ : ProgramDenotation s₁ Unit}
    {cond₂ : ProgramDenotation s₂ Bool} {body₂ : ProgramDenotation s₂ Unit}
    {Inv Exit : s₁ → s₂ → Prop} {PostC : Bool → s₁ → s₂ → Prop}
    {PostE : Unit × s₁ → Unit × s₂ → Prop}
    (h_cond : ProgramDenotation.prhl2 (fun σ₁ σ₂ => Inv σ₁ σ₂ ∧ ¬ Exit σ₁ σ₂) cond₁ cond₂
      (fun u v => u.1 = v.1 ∧ PostC u.1 u.2 v.2))
    (h_body : ProgramDenotation.prhl2 (PostC true) body₁ body₂ (fun u v => Inv u.2 v.2))
    (h_exit : ProgramDenotation.prhl2 (fun σ₁ σ₂ => Inv σ₁ σ₂ ∧ Exit σ₁ σ₂)
      (GaudisCrypt.while_loop cond₁ body₁) (GaudisCrypt.while_loop cond₂ body₂) PostE) :
    ProgramDenotation.prhl2 Inv
      (GaudisCrypt.while_loop cond₁ body₁) (GaudisCrypt.while_loop cond₂ body₂)
      (fun u v => PostC false u.2 v.2 ∨ PostE u v) := by
  classical
  -- Guard, body and exit coupling kernels (⊥ off the relevant relation).
  set Kc : s₁ → s₂ → SubProbability ((Bool × s₁) × (Bool × s₂)) :=
    fun a b => if h : Inv a b ∧ ¬ Exit a b then (h_cond a b h).choose else ⊥ with hKc
  set Kb : s₁ → s₂ → SubProbability ((Unit × s₁) × (Unit × s₂)) :=
    fun a b => if h : PostC true a b then (h_body a b h).choose else ⊥ with hKb
  set Ke : s₁ → s₂ → SubProbability ((Unit × s₁) × (Unit × s₂)) :=
    fun a b => if h : Inv a b ∧ Exit a b then (h_exit a b h).choose else ⊥ with hKe
  have Kc_fst : ∀ a b, Inv a b → ¬ Exit a b →
      (Kc a b >>= fun w => pure w.1) = cond₁ a := by
    intro a b h h'; simp only [hKc, dif_pos (And.intro h h')]
    exact (h_cond a b ⟨h, h'⟩).choose_spec.1
  have Kc_snd : ∀ a b, Inv a b → ¬ Exit a b →
      (Kc a b >>= fun w => pure w.2) = cond₂ b := by
    intro a b h h'; simp only [hKc, dif_pos (And.intro h h')]
    exact (h_cond a b ⟨h, h'⟩).choose_spec.2.1
  have Kc_sat : ∀ a b, Inv a b → ¬ Exit a b →
      (Kc a b).satisfies (fun x => x.1.1 = x.2.1 ∧ PostC x.1.1 x.1.2 x.2.2) := by
    intro a b h h'; simp only [hKc, dif_pos (And.intro h h')]
    exact (h_cond a b ⟨h, h'⟩).choose_spec.2.2
  have Kb_fst : ∀ a b, PostC true a b → (Kb a b >>= fun w => pure w.1) = body₁ a := by
    intro a b h; simp only [hKb, dif_pos h]; exact (h_body a b h).choose_spec.1
  have Kb_snd : ∀ a b, PostC true a b → (Kb a b >>= fun w => pure w.2) = body₂ b := by
    intro a b h; simp only [hKb, dif_pos h]; exact (h_body a b h).choose_spec.2.1
  have Kb_sat : ∀ a b, PostC true a b → (Kb a b).satisfies (fun x => Inv x.1.2 x.2.2) := by
    intro a b h; simp only [hKb, dif_pos h]; exact (h_body a b h).choose_spec.2.2
  have Ke_fst : ∀ a b, Inv a b → Exit a b →
      (Ke a b >>= fun w => pure w.1) = GaudisCrypt.while_loop cond₁ body₁ a := by
    intro a b h h'; simp only [hKe, dif_pos (And.intro h h')]
    exact (h_exit a b ⟨h, h'⟩).choose_spec.1
  have Ke_snd : ∀ a b, Inv a b → Exit a b →
      (Ke a b >>= fun w => pure w.2) = GaudisCrypt.while_loop cond₂ body₂ b := by
    intro a b h h'; simp only [hKe, dif_pos (And.intro h h')]
    exact (h_exit a b ⟨h, h'⟩).choose_spec.2.1
  have Ke_sat : ∀ a b, Inv a b → Exit a b → (Ke a b).satisfies (fun x => PostE x.1 x.2) := by
    intro a b h h'; simp only [hKe, dif_pos (And.intro h h')]
    exact (h_exit a b ⟨h, h'⟩).choose_spec.2.2
  -- The coupling transformer and its application lemma.
  set Φ : ((s₁ × s₂) → SubProbability ((Unit × s₁) × (Unit × s₂))) →𝒄
          ((s₁ × s₂) → SubProbability ((Unit × s₁) × (Unit × s₂))) :=
    OmegaCompletePartialOrder.ContinuousHom.ofFun
      (fun φ st => if Exit st.1 st.2 then Ke st.1 st.2 else
        Kc st.1 st.2 >>= fun gp =>
          if gp.1.1 then Kb gp.1.2 gp.2.2 >>= fun bp => φ (bp.1.2, bp.2.2)
          else pure (((), gp.1.2), ((), gp.2.2))) with hΦ
  have hΦ_app : ∀ (φ : (s₁ × s₂) → SubProbability ((Unit × s₁) × (Unit × s₂)))
      (st : s₁ × s₂), Φ φ st = if Exit st.1 st.2 then Ke st.1 st.2 else
        Kc st.1 st.2 >>= fun gp =>
          if gp.1.1 then Kb gp.1.2 gp.2.2 >>= fun bp => φ (bp.1.2, bp.2.2)
          else pure (((), gp.1.2), ((), gp.2.2)) := fun φ st => rfl
  -- Support of each Kleene iterate.
  have hS : ∀ n σ₁ σ₂, Inv σ₁ σ₂ →
      (Φ^[n] ⊥ (σ₁, σ₂)).satisfies
        (fun x => PostC false x.1.2 x.2.2 ∨ PostE x.1 x.2) := by
    intro n
    induction n with
    | zero =>
      intro σ₁ σ₂ _
      simp only [Function.iterate_zero, id_eq]
      rw [show (⊥ : (s₁ × s₂) → SubProbability _) (σ₁, σ₂) = ⊥ from rfl]
      exact SubProbability.satisfies_bot _
    | succ n ih =>
      intro σ₁ σ₂ hInv
      rw [Function.iterate_succ_apply' (⇑Φ), hΦ_app]
      dsimp only
      by_cases hE : Exit σ₁ σ₂
      · rw [if_pos hE]
        exact fun x hx => Or.inr (Ke_sat σ₁ σ₂ hInv hE x hx)
      rw [if_neg hE]
      refine SubProbability.satisfies_bind (Kc σ₁ σ₂) (fun gp hgp => ?_)
      obtain ⟨hb_eq, hpc⟩ := Kc_sat σ₁ σ₂ hInv hE gp hgp
      by_cases hb : gp.1.1
      · rw [if_pos hb]
        exact SubProbability.satisfies_bind (Kb gp.1.2 gp.2.2)
          (fun bp hbp => ih bp.1.2 bp.2.2 (Kb_sat gp.1.2 gp.2.2 (hb ▸ hpc) bp hbp))
      · rw [if_neg hb]
        refine SubProbability.satisfies_pure _ _ (Or.inl ?_)
        have : gp.1.1 = false := by simpa using hb
        rw [this] at hpc
        exact hpc
  -- Left marginal of each Kleene iterate, sandwiched in expectation.
  have hL : ∀ n σ₁ σ₂, Inv σ₁ σ₂ → ∀ G : Unit × s₁ → ENNReal,
      ((while_iteration cond₁ body₁)^[n] ⊥ () σ₁).expected G
          ≤ (Φ^[n] ⊥ (σ₁, σ₂)).expected (fun x => G x.1) ∧
        (Φ^[n] ⊥ (σ₁, σ₂)).expected (fun x => G x.1)
          ≤ (GaudisCrypt.while_loop cond₁ body₁ σ₁).expected G := by
    intro n
    induction n with
    | zero =>
      intro σ₁ σ₂ _ G
      simp only [Function.iterate_zero, id_eq]
      rw [show (⊥ : (s₁ × s₂) → SubProbability _) (σ₁, σ₂) = ⊥ from rfl,
          show (⊥ : Unit → ProgramDenotation s₁ Unit) () σ₁ = ⊥ from rfl,
          SubProbability.expected_bot, SubProbability.expected_bot]
      exact ⟨le_rfl, by simp⟩
    | succ n ih =>
      intro σ₁ σ₂ hInv G
      rw [Function.iterate_succ_apply' (⇑Φ), hΦ_app]
      dsimp only
      by_cases hE : Exit σ₁ σ₂
      · rw [if_pos hE, expected_fst_of_map_eq (Ke_fst σ₁ σ₂ hInv hE)]
        exact ⟨while_iterate_le_while_loop _ _ _ _ _, le_rfl⟩
      rw [if_neg hE, SubProbability.expected_bind, Function.iterate_succ_apply',
        expected_while_iteration, while_loop_eq_iteration, expected_while_iteration,
        ← expected_fst_of_map_eq (Kc_fst σ₁ σ₂ hInv hE),
        ← expected_fst_of_map_eq (Kc_fst σ₁ σ₂ hInv hE)]
      constructor <;>
      refine SubProbability.expected_mono_of_satisfies (Kc_sat σ₁ σ₂ hInv hE) ?_ <;>
      rintro ⟨⟨b, x₁⟩, ⟨b', x₂⟩⟩ ⟨hbb, hpc⟩ <;>
      dsimp only at hbb hpc ⊢ <;>
      subst hbb <;>
      cases b
      all_goals simp only [Bool.false_eq_true, ↓reduceIte, expected_pure, le_refl,
        SubProbability.expected_bind]
      · rw [← expected_fst_of_map_eq (Kb_fst x₁ x₂ hpc)]
        exact SubProbability.expected_mono_of_satisfies (Kb_sat x₁ x₂ hpc)
          (fun bp hbp => (ih _ _ hbp G).1)
      · rw [← expected_fst_of_map_eq (Kb_fst x₁ x₂ hpc)]
        exact SubProbability.expected_mono_of_satisfies (Kb_sat x₁ x₂ hpc)
          (fun bp hbp => (ih _ _ hbp G).2)
  -- Right marginal of each Kleene iterate, sandwiched in expectation.
  have hR : ∀ n σ₁ σ₂, Inv σ₁ σ₂ → ∀ G : Unit × s₂ → ENNReal,
      ((while_iteration cond₂ body₂)^[n] ⊥ () σ₂).expected G
          ≤ (Φ^[n] ⊥ (σ₁, σ₂)).expected (fun x => G x.2) ∧
        (Φ^[n] ⊥ (σ₁, σ₂)).expected (fun x => G x.2)
          ≤ (GaudisCrypt.while_loop cond₂ body₂ σ₂).expected G := by
    intro n
    induction n with
    | zero =>
      intro σ₁ σ₂ _ G
      simp only [Function.iterate_zero, id_eq]
      rw [show (⊥ : (s₁ × s₂) → SubProbability _) (σ₁, σ₂) = ⊥ from rfl,
          show (⊥ : Unit → ProgramDenotation s₂ Unit) () σ₂ = ⊥ from rfl,
          SubProbability.expected_bot, SubProbability.expected_bot]
      exact ⟨le_rfl, by simp⟩
    | succ n ih =>
      intro σ₁ σ₂ hInv G
      rw [Function.iterate_succ_apply' (⇑Φ), hΦ_app]
      dsimp only
      by_cases hE : Exit σ₁ σ₂
      · rw [if_pos hE, expected_snd_of_map_eq (Ke_snd σ₁ σ₂ hInv hE)]
        exact ⟨while_iterate_le_while_loop _ _ _ _ _, le_rfl⟩
      rw [if_neg hE, SubProbability.expected_bind, Function.iterate_succ_apply',
        expected_while_iteration, while_loop_eq_iteration, expected_while_iteration,
        ← expected_snd_of_map_eq (Kc_snd σ₁ σ₂ hInv hE),
        ← expected_snd_of_map_eq (Kc_snd σ₁ σ₂ hInv hE)]
      constructor <;>
      refine SubProbability.expected_mono_of_satisfies (Kc_sat σ₁ σ₂ hInv hE) ?_ <;>
      rintro ⟨⟨b, x₁⟩, ⟨b', x₂⟩⟩ ⟨hbb, hpc⟩ <;>
      dsimp only at hbb hpc ⊢ <;>
      subst hbb <;>
      cases b
      all_goals simp only [Bool.false_eq_true, ↓reduceIte, expected_pure, le_refl,
        SubProbability.expected_bind]
      · rw [← expected_snd_of_map_eq (Kb_snd x₁ x₂ hpc)]
        exact SubProbability.expected_mono_of_satisfies (Kb_sat x₁ x₂ hpc)
          (fun bp hbp => (ih _ _ hbp G).1)
      · rw [← expected_snd_of_map_eq (Kb_snd x₁ x₂ hpc)]
        exact SubProbability.expected_mono_of_satisfies (Kb_sat x₁ x₂ hpc)
          (fun bp hbp => (ih _ _ hbp G).2)
  -- Assemble the coupling witness at each invariant-related state: the supremum of the
  -- sandwiched iterates is the loop.
  intro σ₁ σ₂ hInv
  refine ⟨Φ.lfp (σ₁, σ₂), ?_, ?_, ?_⟩
  · refine SubProbability.ext_of_expected (fun G => ?_)
    rw [SubProbability.expected_map, SubProbability.expected_lfp_eq_iSup]
    refine le_antisymm (iSup_le fun n => (hL n σ₁ σ₂ hInv G).2) ?_
    rw [expected_while_lfp_iSup]
    exact iSup_mono fun n => (hL n σ₁ σ₂ hInv G).1
  · refine SubProbability.ext_of_expected (fun G => ?_)
    rw [SubProbability.expected_map, SubProbability.expected_lfp_eq_iSup]
    refine le_antisymm (iSup_le fun n => (hR n σ₁ σ₂ hInv G).2) ?_
    rw [expected_while_lfp_iSup]
    exact iSup_mono fun n => (hR n σ₁ σ₂ hInv G).1
  · exact SubProbability.satisfies_lfp Φ (σ₁, σ₂) _ (fun n => hS n σ₁ σ₂ hInv)

end GaudisCrypt
