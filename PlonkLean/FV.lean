-- CHAOS FILE

import PlonkLean.Language.Modules

open Language.Modules
open Language.Programs

variable [ProgramSpec]

opaque FV : Type
-- Placeholder
axiom fv_proc {sig holes} (proc : ProcedureWithHoles holes sig) : Set FV
axiom fv_proc_instantiate {sig holes} (proc : ProcedureWithHoles holes sig) (args) :
  fv_proc (proc.instantiate args) = fv_proc proc ∪ ⋃ i : HoleIndex holes sig, fv_proc (args i)

def fv' {mctx : ModuleContext} {mty : ModuleType} (mex : ModuleExpression mctx mty) : Set FV :=
  match mex with
    | .unit => sorry
    | .proc p => fv_proc p
    | .procHoles n p => fv_proc p
    | .var .zero => {}
    | .var (.succ n) => {}
    | .app a b => fv' a ∪ fv' b
    | .fst a => fv' a
    | .snd a => fv' a
    | .abs body => fv' body
    | .pair a b => fv' a ∪ fv' b

-- Trivially true but not what we want.
-- Unintuitive that modules don't reduce when applying
-- Do we need the operational semantics of the simply typled λ-calculus?
-- I think so, below's the attempt
theorem fv'_app (a : ModuleExpression Γ (ModuleType.arr A B)) (b : ModuleExpression Γ A) :
  fv' (ModuleExpression.app a b) = fv' a ∪ fv' b := rfl

def fv (m : ModuleExpression c t) : Set FV := fv' (reduce m)

private lemma fv'_var_eq {Γ T} (r : ModuleContextIdx Γ T) : fv' (.var r) = {} := by
  cases r <;> rfl

private lemma fv'_rename_eq {Δ U} (m : ModuleExpression Δ U) :
    ∀ {Γ : ModuleContext} (ρ : ∀ {T}, ModuleContextIdx Δ T → ModuleContextIdx Γ T),
    fv' (m.rename ρ) = fv' m := by
  induction m with
  | unit => sorry
  | proc | procHoles | var _ => intros; simp [ModuleExpression.rename, fv', fv'_var_eq]
  | app f a ihf iha => intros Γ ρ; simp [ModuleExpression.rename, fv', ihf ρ, iha ρ]
  | fst e ih => intros Γ ρ; simp [ModuleExpression.rename, fv', ih ρ]
  | snd e ih => intros Γ ρ; simp [ModuleExpression.rename, fv', ih ρ]
  | abs body ih => intros Γ ρ; simp [ModuleExpression.rename, fv', ih (liftRenaming ρ)]
  | pair a b iha ihb => intros Γ ρ; simp [ModuleExpression.rename, fv', iha ρ, ihb ρ]

private lemma fv'_substAll_le {S : Set FV} {Δ U} (m : ModuleExpression Δ U) :
    ∀ {Γ : ModuleContext} (σ : ∀ {T}, ModuleContextIdx Δ T → ModuleExpression Γ T),
    (∀ {T} (r : ModuleContextIdx Δ T), fv' (σ r) ⊆ S) →
    fv' (substituteSimultaneously σ m) ⊆ fv' m ∪ S := by
  induction m with
  | unit => sorry
  | proc | procHoles => intros; simp [substituteSimultaneously, fv']
  | var r =>
      intros Γ σ hσ
      simp only [substituteSimultaneously, fv'_var_eq, Set.empty_union]
      exact hσ r
  | app f a ihf iha =>
      intros Γ σ hσ
      simp only [substituteSimultaneously, fv']
      rintro x (h | h)
      · rcases ihf σ hσ h with h' | h'
        · exact .inl (.inl h')
        · exact .inr h'
      · rcases iha σ hσ h with h' | h'
        · exact .inl (.inr h')
        · exact .inr h'
  | fst e ih => intros Γ σ hσ; simp only [substituteSimultaneously, fv']; exact ih σ hσ
  | snd e ih => intros Γ σ hσ; simp only [substituteSimultaneously, fv']; exact ih σ hσ
  | abs body ih =>
      intros Γ σ hσ
      simp only [substituteSimultaneously, fv']
      apply ih (liftSubstitution σ)
      intro T r
      cases r with
      | zero => simp [liftSubstitution, fv']
      | succ r' => simp only [liftSubstitution]; rw [fv'_rename_eq]; exact hσ r'
  | pair a b iha ihb =>
      intros Γ σ hσ
      simp only [substituteSimultaneously, fv']
      rintro x (h | h)
      · rcases iha σ hσ h with h' | h'
        · exact .inl (.inl h')
        · exact .inr h'
      · rcases ihb σ hσ h with h' | h'
        · exact .inl (.inr h')
        · exact .inr h'

private lemma fv'_subst_le
    (body : ModuleExpression (Δ.append u) t) (arg : ModuleExpression Δ u) :
    fv' (substitute body arg) ⊆ fv' body ∪ fv' arg := by
  simp only [substitute]
  apply fv'_substAll_le body (S := fv' arg)
  intro T r
  cases r with
  | zero => simp [variableSubstitution]
  | succ r' => simp only [variableSubstitution, fv'_var_eq]; exact Set.empty_subset _

/-- The union of `fv_proc` over the entries of a procedure tuple. -/
def fvArgs : (sigs : List ProcedureSignature) →
    typeListToProdGeneric Prod PUnit (sigs.map Procedure) → Set FV
  | [],           _          => {}
  | [_],          p          => fv_proc p
  | _ :: s :: ss, (p, rest)  => fv_proc p ∪ fvArgs (s :: ss) rest


theorem fv_reduction_step (m : ModuleExpression c t) (h : ReductionStep m m') :
  fv' m' ⊆ fv' m := by
  cases h
  all_goals sorry


theorem fv_reduce (m : ModuleExpression c t) : fv m ⊆ fv' m := by
  unfold fv
  -- Having some packaged induction principle for reduce would be nice.
  apply WellFoundedRelation.wf.induction (C := fun m => fv' (reduce m) ⊆ fv' m) m
  intro n ih
  unfold reduce
  split_ifs with h
  · exact Set.Subset.refl _
  · have h1 : ReductionStep n (cbvReductionStep n h) := by apply cbvReductionStep_is_reductionStep
    have h2 := fv_reduction_step _ h1
    have h3 : WellFoundedRelation.rel (cbvReductionStep n h) n := sorry
    have h4 := ih _ h3
    grind

theorem fv_app (a : ModuleExpression Γ (ModuleType.arr A B)) (b : ModuleExpression Γ A) :
    fv (ModuleExpression.app a b) ⊆ fv a ∪ fv b := by
  simp only [fv, ← fv'_app]
  rw [reduce_app]
  exact fv_reduce _
