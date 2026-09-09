import GaudisCrypt.Language.ModuleExpressionBasics

/-! # Confluence of module-expression reduction

The two open facts about `ModuleExpression.MultiStepReduction` that everything downstream of
`reduce` rests on: reduction is confluent (stuck reducts are unique), and termination is
invariant along it.  Split off from `ModuleExpressionBasics.lean` so the syntax, typing,
reduction and normal-form development there stays independent of them;
`ModuleExpression.lean` is where their consequences live. -/

namespace GaudisCrypt

variable [ProgramSpec]

namespace ModuleExpression

/-! ## The de Bruijn σ-calculus laws

`rename` and `substituteSimultaneously` compose in the four standard ways.  The confluence proof
needs them to push a substitution through a β-contractum. -/

omit [ProgramSpec] in
theorem liftRen_comp (ρ ρ' : Nat → Nat) : liftRen ρ' ∘ liftRen ρ = liftRen (ρ' ∘ ρ) :=
  funext fun n => by cases n <;> rfl

theorem rename_rename (ρ ρ' : Nat → Nat) (m : ModuleExpression) :
    (m.rename ρ).rename ρ' = m.rename (ρ' ∘ ρ) := by
  induction m generalizing ρ ρ' with
  | proc p => rfl
  | procHoles ne p => rfl
  | var n => rfl
  | app f a ihf iha => simp only [rename, ihf, iha]
  | fst e ih => simp only [rename, ih]
  | snd e ih => simp only [rename, ih]
  | abs body ih => simp only [rename, ih, liftRen_comp]
  | pair a b iha ihb => simp only [rename, iha, ihb]
  | unit => rfl

theorem liftSubst_comp_liftRen (σ : Nat → ModuleExpression) (ρ : Nat → Nat) :
    liftSubst σ ∘ liftRen ρ = liftSubst (σ ∘ ρ) :=
  funext fun n => by cases n <;> rfl

/-- Substituting into a renamed term is substituting along the composite. -/
theorem substituteSimultaneously_rename (ρ : Nat → Nat) (σ : Nat → ModuleExpression)
    (m : ModuleExpression) :
    (m.rename ρ).substituteSimultaneously σ = m.substituteSimultaneously (σ ∘ ρ) := by
  induction m generalizing ρ σ with
  | proc p => rfl
  | procHoles ne p => rfl
  | var n => rfl
  | app f a ihf iha => simp only [rename, substituteSimultaneously, ihf, iha]
  | fst e ih => simp only [rename, substituteSimultaneously, ih]
  | snd e ih => simp only [rename, substituteSimultaneously, ih]
  | abs body ih => simp only [rename, substituteSimultaneously, ih, liftSubst_comp_liftRen]
  | pair a b iha ihb => simp only [rename, substituteSimultaneously, iha, ihb]
  | unit => rfl

theorem liftSubst_rename (σ : Nat → ModuleExpression) (ρ : Nat → Nat) :
    liftSubst (fun k => (σ k).rename ρ) = fun n => (liftSubst σ n).rename (liftRen ρ) :=
  funext fun n => by
    cases n with
    | zero => rfl
    | succ n => simp only [liftSubst, rename_rename]; rfl

/-- Renaming a substituted term is substituting along the renamed substitution. -/
theorem rename_substituteSimultaneously (ρ : Nat → Nat) (σ : Nat → ModuleExpression)
    (m : ModuleExpression) :
    (m.substituteSimultaneously σ).rename ρ =
      m.substituteSimultaneously (fun n => (σ n).rename ρ) := by
  induction m generalizing ρ σ with
  | proc p => rfl
  | procHoles ne p => rfl
  | var n => rfl
  | app f a ihf iha => simp only [rename, substituteSimultaneously, ihf, iha]
  | fst e ih => simp only [rename, substituteSimultaneously, ih]
  | snd e ih => simp only [rename, substituteSimultaneously, ih]
  | abs body ih => simp only [rename, substituteSimultaneously, ih, liftSubst_rename]
  | pair a b iha ihb => simp only [rename, substituteSimultaneously, iha, ihb]
  | unit => rfl

theorem liftSubst_substituteSimultaneously (σ τ : Nat → ModuleExpression) :
    liftSubst (fun k => (σ k).substituteSimultaneously τ) =
      fun n => (liftSubst σ n).substituteSimultaneously (liftSubst τ) :=
  funext fun n => by
    cases n with
    | zero => rfl
    | succ n =>
        simp only [liftSubst, substituteSimultaneously_rename, rename_substituteSimultaneously]
        rfl

/-- Two substitutions in a row are one substitution along the composite. -/
theorem substituteSimultaneously_substituteSimultaneously (σ τ : Nat → ModuleExpression)
    (m : ModuleExpression) :
    (m.substituteSimultaneously σ).substituteSimultaneously τ =
      m.substituteSimultaneously (fun n => (σ n).substituteSimultaneously τ) := by
  induction m generalizing σ τ with
  | proc p => rfl
  | procHoles ne p => rfl
  | var n => rfl
  | app f a ihf iha => simp only [substituteSimultaneously, ihf, iha]
  | fst e ih => simp only [substituteSimultaneously, ih]
  | snd e ih => simp only [substituteSimultaneously, ih]
  | abs body ih => simp only [substituteSimultaneously, ih, liftSubst_substituteSimultaneously]
  | pair a b iha ihb => simp only [substituteSimultaneously, iha, ihb]
  | unit => rfl

theorem substituteSimultaneously_var (m : ModuleExpression) :
    m.substituteSimultaneously (fun n => .var n) = m := by
  induction m with
  | proc p => rfl
  | procHoles ne p => rfl
  | var n => rfl
  | app f a ihf iha => simp only [substituteSimultaneously, ihf, iha]
  | fst e ih => simp only [substituteSimultaneously, ih]
  | snd e ih => simp only [substituteSimultaneously, ih]
  | abs body ih =>
      simp only [substituteSimultaneously]
      rw [show liftSubst (fun n => ModuleExpression.var n) = fun n => ModuleExpression.var n from
        funext fun n => by cases n <;> rfl, ih]
  | pair a b iha ihb => simp only [substituteSimultaneously, iha, ihb]
  | unit => rfl

/-- Renaming commutes with β-substitution. -/
theorem rename_substitute (ρ : Nat → Nat) (body arg : ModuleExpression) :
    (body.substitute arg).rename ρ = (body.rename (liftRen ρ)).substitute (arg.rename ρ) := by
  simp only [substitute, rename_substituteSimultaneously, substituteSimultaneously_rename]
  refine congrFun (congrArg substituteSimultaneously (funext fun n => ?_)) body
  cases n <;> rfl

/-- A simultaneous substitution commutes with β-substitution. -/
theorem substituteSimultaneously_substitute (σ : Nat → ModuleExpression)
    (body arg : ModuleExpression) :
    (body.substitute arg).substituteSimultaneously σ =
      (body.substituteSimultaneously (liftSubst σ)).substitute
        (arg.substituteSimultaneously σ) := by
  simp only [substitute, substituteSimultaneously_substituteSimultaneously]
  refine congrFun (congrArg substituteSimultaneously (funext fun n => ?_)) body
  cases n with
  | zero => rfl
  | succ n =>
      have hcomp : (variableSubstitution (arg.substituteSimultaneously σ)) ∘ Nat.succ
          = fun k => ModuleExpression.var k := funext fun _ => rfl
      simp only [variableSubstitution, liftSubst, substituteSimultaneously_rename, hcomp,
        substituteSimultaneously_var]
      rfl

end ModuleExpression

/-! ## The argument of a δ-redex

`inst.toModuleExpr` is a closed tuple of procedures: renaming and substitution leave it alone, it
determines `inst`, and — once parallel reduction is in place — nothing reduces inside it.  Together
these say the δ-rule has no critical pair with anything. -/

namespace HoleSigs.Instantiation

theorem toModuleExpr_rename :
    ∀ {holes : HoleSigs} (inst : holes.Instantiation) (ρ : Nat → Nat),
      inst.toModuleExpr.rename ρ = inst.toModuleExpr
  | .empty,             _,    _ => rfl
  | .cons _ .empty,     _,    _ => rfl
  | .cons _ (.cons ..), inst, ρ => by
      simp only [toModuleExpr, ModuleExpression.rename, toModuleExpr_rename inst.2 ρ]

theorem toModuleExpr_substituteSimultaneously :
    ∀ {holes : HoleSigs} (inst : holes.Instantiation) (σ : Nat → ModuleExpression),
      inst.toModuleExpr.substituteSimultaneously σ = inst.toModuleExpr
  | .empty,             _,    _ => rfl
  | .cons _ .empty,     _,    _ => rfl
  | .cons _ (.cons ..), inst, σ => by
      simp only [toModuleExpr, ModuleExpression.substituteSimultaneously,
        toModuleExpr_substituteSimultaneously inst.2 σ]

/-- Distinct instantiations give distinct tuples: the δ-rule's contractum is determined by the
    redex. -/
theorem toModuleExpr_injective :
    ∀ {holes : HoleSigs} (inst inst' : holes.Instantiation),
      inst.toModuleExpr = inst'.toModuleExpr → inst = inst'
  | .empty,             _,    _,     _ => rfl
  | .cons _ .empty,     inst, inst', h => by
      simp only [toModuleExpr, ModuleExpression.pair.injEq, ModuleExpression.proc.injEq,
        heq_eq_eq, true_and, and_true] at h
      exact h
  | .cons _ (.cons ..), inst, inst', h => by
      simp only [toModuleExpr, ModuleExpression.pair.injEq, ModuleExpression.proc.injEq,
        heq_eq_eq, true_and] at h
      exact Prod.ext h.1 (toModuleExpr_injective inst.2 inst'.2 h.2)

end HoleSigs.Instantiation

namespace ModuleExpression

/-! ## Parallel reduction

`ParStep` contracts any set of redexes of a term at once (Tait–Martin-Löf).  It sits between
`ReductionStep` and `MultiStepReduction`, so it has the same transitive-reflexive closure, and —
unlike `ReductionStep` — it has the diamond property, which is what gives confluence. -/

/-- Parallel reduction: contract any set of the redexes present in the term, simultaneously.
    A δ-redex needs no premise for its argument: `inst.toModuleExpr` has no redexes inside. -/
inductive ParStep : ModuleExpression → ModuleExpression → Prop where
  | proc {sig} (p : Procedure sig) : ParStep (.proc p) (.proc p)
  | procHoles {holes sig} (ne : holes.NonEmpty) (p : ProcedureWithHoles holes sig) :
      ParStep (.procHoles ne p) (.procHoles ne p)
  | var (n : Nat) : ParStep (.var n) (.var n)
  | unit : ParStep .unit .unit
  | abs {b b'} : ParStep b b' → ParStep (.abs b) (.abs b')
  | app {f f' a a'} : ParStep f f' → ParStep a a' → ParStep (.app f a) (.app f' a')
  | beta {b b' a a'} : ParStep b b' → ParStep a a' → ParStep (.app (.abs b) a) (b'.substitute a')
  | pair {a a' b b'} : ParStep a a' → ParStep b b' → ParStep (.pair a b) (.pair a' b')
  | fst {e e'} : ParStep e e' → ParStep (.fst e) (.fst e')
  | fstPair {a a' b} : ParStep a a' → ParStep (.fst (.pair a b)) a'
  | snd {e e'} : ParStep e e' → ParStep (.snd e) (.snd e')
  | sndPair {a b b'} : ParStep b b' → ParStep (.snd (.pair a b)) b'
  | delta {holes sigs} (ne : holes.NonEmpty) (p : ProcedureWithHoles holes sigs)
      (inst : holes.Instantiation) :
      ParStep (.app (.procHoles ne p) inst.toModuleExpr) (.proc (p.instantiate inst))

/-- `abs` is a congruence for multi-step reduction. -/
theorem multiStepReduction_abs_cong {b b' : ModuleExpression} (h : b.MultiStepReduction b') :
    (ModuleExpression.abs b).MultiStepReduction (ModuleExpression.abs b') := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (.lam hbc)

/-- `snd` is a congruence for multi-step reduction. -/
theorem multiStepReduction_snd_cong {e e' : ModuleExpression} (h : e.MultiStepReduction e') :
    (ModuleExpression.snd e).MultiStepReduction (ModuleExpression.snd e') := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (.snd hbc)

namespace ParStep

/-- Parallel reduction is reflexive: contract nothing. -/
@[refl] theorem refl : ∀ m : ModuleExpression, ParStep m m
  | .proc p         => .proc p
  | .procHoles ne p => .procHoles ne p
  | .var n          => .var n
  | .app f a        => .app (refl f) (refl a)
  | .fst e          => .fst (refl e)
  | .snd e          => .snd (refl e)
  | .abs b          => .abs (refl b)
  | .pair a b       => .pair (refl a) (refl b)
  | .unit           => .unit

/-- A single reduction step is a parallel step. -/
theorem of_reductionStep {m n : ModuleExpression} (h : m.ReductionStep n) : ParStep m n := by
  induction h with
  | beta => exact .beta (refl _) (refl _)
  | appL _ ih => exact .app ih (refl _)
  | appR _ ih => exact .app (refl _) ih
  | lam _ ih => exact .abs ih
  | pairL _ ih => exact .pair ih (refl _)
  | pairR _ ih => exact .pair (refl _) ih
  | fstPair => exact .fstPair (refl _)
  | fst _ ih => exact .fst ih
  | sndPair => exact .sndPair (refl _)
  | snd _ ih => exact .snd ih
  | delta ne p inst => exact .delta ne p inst

/-- A parallel step is a multi-step reduction. -/
theorem multiStepReduction {m n : ModuleExpression} (h : ParStep m n) : m.MultiStepReduction n := by
  induction h with
  | proc p => exact .refl
  | procHoles ne p => exact .refl
  | var n => exact .refl
  | unit => exact .refl
  | abs _ ih => exact multiStepReduction_abs_cong ih
  | app _ _ ihf iha => exact multiStepReduction_app_cong ihf iha
  | beta _ _ ihb iha =>
      exact (multiStepReduction_app_cong (multiStepReduction_abs_cong ihb) iha).tail .beta
  | pair _ _ iha ihb => exact multiStepReduction_pair_cong iha ihb
  | fst _ ih => exact multiStepReduction_fst_cong ih
  | fstPair _ ih =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single ReductionStep.fstPair) ih
  | snd _ ih => exact multiStepReduction_snd_cong ih
  | sndPair _ ih =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single ReductionStep.sndPair) ih
  | delta ne p inst => exact .single (.delta ne p inst)

/-- Parallel reduction survives a renaming. -/
theorem rename : ∀ {m n : ModuleExpression}, ParStep m n → ∀ ρ : Nat → Nat,
    ParStep (m.rename ρ) (n.rename ρ) := by
  intro m n h
  induction h with
  | proc p => intro ρ; exact .proc p
  | procHoles ne p => intro ρ; exact .procHoles ne p
  | var n => intro ρ; exact .var _
  | unit => intro ρ; exact .unit
  | abs _ ih => intro ρ; exact .abs (ih _)
  | app _ _ ihf iha => intro ρ; exact .app (ihf _) (iha _)
  | beta _ _ ihb iha =>
      intro ρ
      simp only [ModuleExpression.rename, rename_substitute]
      exact .beta (ihb _) (iha _)
  | pair _ _ iha ihb => intro ρ; exact .pair (iha _) (ihb _)
  | fst _ ih => intro ρ; exact .fst (ih _)
  | fstPair _ ih => intro ρ; exact .fstPair (ih _)
  | snd _ ih => intro ρ; exact .snd (ih _)
  | sndPair _ ih => intro ρ; exact .sndPair (ih _)
  | delta ne p inst =>
      intro ρ
      simp only [ModuleExpression.rename, HoleSigs.Instantiation.toModuleExpr_rename]
      exact .delta ne p inst

/-- Two substitutions that agree up to parallel reduction still do so under a binder. -/
theorem liftSubst_of_forall {σ τ : Nat → ModuleExpression} (h : ∀ n, ParStep (σ n) (τ n)) :
    ∀ n, ParStep (liftSubst σ n) (liftSubst τ n)
  | 0     => .var 0
  | n + 1 => (h n).rename Nat.succ

/-- Parallel reduction survives a simultaneous substitution that itself reduces in parallel. -/
theorem substituteSimultaneously : ∀ {m n : ModuleExpression}, ParStep m n →
    ∀ {σ τ : Nat → ModuleExpression}, (∀ k, ParStep (σ k) (τ k)) →
      ParStep (m.substituteSimultaneously σ) (n.substituteSimultaneously τ) := by
  intro m n h
  induction h with
  | proc p => intro σ τ _; exact .proc p
  | procHoles ne p => intro σ τ _; exact .procHoles ne p
  | var n => intro σ τ hσ; exact hσ n
  | unit => intro σ τ _; exact .unit
  | abs _ ih => intro σ τ hσ; exact .abs (ih (liftSubst_of_forall hσ))
  | app _ _ ihf iha => intro σ τ hσ; exact .app (ihf hσ) (iha hσ)
  | beta _ _ ihb iha =>
      intro σ τ hσ
      simp only [ModuleExpression.substituteSimultaneously, substituteSimultaneously_substitute]
      exact .beta (ihb (liftSubst_of_forall hσ)) (iha hσ)
  | pair _ _ iha ihb => intro σ τ hσ; exact .pair (iha hσ) (ihb hσ)
  | fst _ ih => intro σ τ hσ; exact .fst (ih hσ)
  | fstPair _ ih => intro σ τ hσ; exact .fstPair (ih hσ)
  | snd _ ih => intro σ τ hσ; exact .snd (ih hσ)
  | sndPair _ ih => intro σ τ hσ; exact .sndPair (ih hσ)
  | delta ne p inst =>
      intro σ τ _
      simp only [ModuleExpression.substituteSimultaneously,
        HoleSigs.Instantiation.toModuleExpr_substituteSimultaneously]
      exact .delta ne p inst

/-- Parallel reduction survives β-substitution: the key lemma behind the diamond property. -/
theorem substitute {b b' a a' : ModuleExpression} (hb : ParStep b b') (ha : ParStep a a') :
    ParStep (b.substitute a) (b'.substitute a') :=
  hb.substituteSimultaneously fun n => by
    cases n with
    | zero => exact ha
    | succ n => exact .var n

/-- Nothing reduces inside the argument of a δ-redex. -/
theorem eq_toModuleExpr : ∀ {holes : HoleSigs} (inst : holes.Instantiation)
    {n : ModuleExpression}, ParStep inst.toModuleExpr n → n = inst.toModuleExpr
  | .empty, _, _, h => by cases h; rfl
  | .cons _ .empty, inst, n, h => by
      cases h with
      | pair hp hu => cases hp; cases hu; rfl
  | .cons _ (.cons ..), inst, n, h => by
      cases h with
      | pair hp hrest =>
          cases hp
          rw [eq_toModuleExpr inst.2 hrest]
          rfl

/-! ### Inversion -/

theorem abs_inv {b n : ModuleExpression} (h : ParStep (.abs b) n) :
    ∃ b', n = .abs b' ∧ ParStep b b' := by
  cases h with | abs hb => exact ⟨_, rfl, hb⟩

theorem pair_inv {a b n : ModuleExpression} (h : ParStep (.pair a b) n) :
    ∃ a' b', n = .pair a' b' ∧ ParStep a a' ∧ ParStep b b' := by
  cases h with | pair ha hb => exact ⟨_, _, rfl, ha, hb⟩

theorem procHoles_inv {holes sig} {ne : holes.NonEmpty} {p : ProcedureWithHoles holes sig}
    {n : ModuleExpression} (h : ParStep (.procHoles ne p) n) : n = .procHoles ne p := by
  cases h with | procHoles _ _ => rfl

end ParStep

/-! ## The complete development

`completeDevelopment m` contracts every redex `m` has, and nothing else (a δ-redex counts only when
its argument is *already* a procedure tuple).  Takahashi's triangle property — every parallel
reduct of `m` reduces in parallel to `completeDevelopment m` — gives the diamond property, hence
confluence.  Noncomputable only because of the classical test for the δ-rule. -/

open scoped Classical in
/-- Contract every redex of `m` simultaneously. -/
noncomputable def completeDevelopment : ModuleExpression → ModuleExpression
  | .app (.abs b) a => (completeDevelopment b).substitute (completeDevelopment a)
  | .app (.procHoles (holes := holes) ne p) a =>
      if h : ∃ inst : holes.Instantiation, a = inst.toModuleExpr then
        .proc (p.instantiate h.choose)
      else .app (.procHoles ne p) (completeDevelopment a)
  | .app f a => .app (completeDevelopment f) (completeDevelopment a)
  | .fst (.pair a _) => completeDevelopment a
  | .fst e => .fst (completeDevelopment e)
  | .snd (.pair _ b) => completeDevelopment b
  | .snd e => .snd (completeDevelopment e)
  | .abs b => .abs (completeDevelopment b)
  | .pair a b => .pair (completeDevelopment a) (completeDevelopment b)
  | .proc p => .proc p
  | .procHoles ne p => .procHoles ne p
  | .var n => .var n
  | .unit => .unit

/-- A δ-redex develops to its contractum. -/
theorem completeDevelopment_delta {holes sigs} (ne : holes.NonEmpty)
    (p : ProcedureWithHoles holes sigs) (inst : holes.Instantiation) :
    completeDevelopment (.app (.procHoles ne p) inst.toModuleExpr) =
      .proc (p.instantiate inst) := by
  classical
  have hex : ∃ inst' : holes.Instantiation, inst.toModuleExpr = inst'.toModuleExpr := ⟨inst, rfl⟩
  rw [completeDevelopment, dif_pos hex]
  exact congrArg _ (congrArg _
    (HoleSigs.Instantiation.toModuleExpr_injective _ _ hex.choose_spec).symm)

/-- An application of a procedure with holes whose argument is not a procedure tuple develops
    componentwise. -/
theorem completeDevelopment_app_procHoles {holes sigs} (ne : holes.NonEmpty)
    (p : ProcedureWithHoles holes sigs) (a : ModuleExpression)
    (h : ¬ ∃ inst : holes.Instantiation, a = inst.toModuleExpr) :
    completeDevelopment (.app (.procHoles ne p) a) =
      .app (.procHoles ne p) (completeDevelopment a) := by
  classical
  rw [completeDevelopment, dif_neg h]

/-- **Takahashi's triangle property**: every parallel reduct of `m` parallel-reduces to the
    complete development of `m`. -/
theorem ParStep.triangle {m n : ModuleExpression} (h : ParStep m n) :
    ParStep n (completeDevelopment m) := by
  induction h with
  | proc p => exact .proc p
  | procHoles ne p => exact .procHoles ne p
  | var n => exact .var n
  | unit => exact .unit
  | abs _ ih => exact .abs ih
  | beta _ _ ihb iha => exact ihb.substitute iha
  | pair _ _ iha ihb => exact .pair iha ihb
  | fstPair _ ih => exact ih
  | sndPair _ ih => exact ih
  | delta ne p inst => rw [completeDevelopment_delta]
  | @app f f' a a' hf ha ihf iha =>
      cases f with
      | abs b =>
          obtain ⟨b', rfl, _⟩ := ParStep.abs_inv hf
          obtain ⟨b'', hb'', hb'⟩ := ParStep.abs_inv ihf
          rw [completeDevelopment] at hb''
          injection hb'' with hb''
          subst hb''
          rw [completeDevelopment]
          exact .beta hb' iha
      | @procHoles holes sig ne p =>
          cases ParStep.procHoles_inv hf
          by_cases hinst : ∃ inst : holes.Instantiation, a = inst.toModuleExpr
          · obtain ⟨inst, rfl⟩ := hinst
            cases ParStep.eq_toModuleExpr inst ha
            rw [completeDevelopment_delta]
            exact .delta ne p inst
          · rw [completeDevelopment_app_procHoles _ _ _ hinst]
            exact .app (.procHoles ne p) iha
      | proc p => exact .app ihf iha
      | var n => exact .app ihf iha
      | app f₁ f₂ => exact .app ihf iha
      | fst e => exact .app ihf iha
      | snd e => exact .app ihf iha
      | pair a₁ a₂ => exact .app ihf iha
      | unit => exact .app ihf iha
  | @fst e e' he ihe =>
      cases e with
      | pair a b =>
          obtain ⟨a', b', rfl, _, _⟩ := ParStep.pair_inv he
          obtain ⟨a'', b'', hab, ha', _⟩ := ParStep.pair_inv ihe
          rw [completeDevelopment] at hab
          injection hab with hab _
          subst hab
          rw [completeDevelopment]
          exact .fstPair ha'
      | proc p => exact .fst ihe
      | procHoles ne p => exact .fst ihe
      | var n => exact .fst ihe
      | app f₁ f₂ => exact .fst ihe
      | fst e₁ => exact .fst ihe
      | snd e₁ => exact .fst ihe
      | abs b => exact .fst ihe
      | unit => exact .fst ihe
  | @snd e e' he ihe =>
      cases e with
      | pair a b =>
          obtain ⟨a', b', rfl, _, _⟩ := ParStep.pair_inv he
          obtain ⟨a'', b'', hab, _, hb'⟩ := ParStep.pair_inv ihe
          rw [completeDevelopment] at hab
          injection hab with _ hab
          subst hab
          rw [completeDevelopment]
          exact .sndPair hb'
      | proc p => exact .snd ihe
      | procHoles ne p => exact .snd ihe
      | var n => exact .snd ihe
      | app f₁ f₂ => exact .snd ihe
      | fst e₁ => exact .snd ihe
      | snd e₁ => exact .snd ihe
      | abs b => exact .snd ihe
      | unit => exact .snd ihe

/-! ## Confluence

The diamond property of `ParStep` is Takahashi's triangle read twice; `Relation.church_rosser`
turns it into confluence of the transitive-reflexive closure, and that closure is
`MultiStepReduction` because `ParStep` sits between `ReductionStep` and it. -/

/-- **Diamond property** of parallel reduction. -/
theorem ParStep.diamond {m n1 n2 : ModuleExpression} (h1 : ParStep m n1) (h2 : ParStep m n2) :
    ∃ d, ParStep n1 d ∧ ParStep n2 d :=
  ⟨completeDevelopment m, h1.triangle, h2.triangle⟩

theorem reflTransGen_parStep_of_multiStepReduction {m n : ModuleExpression}
    (h : m.MultiStepReduction n) : Relation.ReflTransGen ParStep m n :=
  h.mono fun _ _ => ParStep.of_reductionStep

theorem multiStepReduction_of_reflTransGen_parStep {m n : ModuleExpression}
    (h : Relation.ReflTransGen ParStep m n) : m.MultiStepReduction n := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.trans hbc.multiStepReduction

/-- **Church–Rosser**: a term's reducts can always be brought back together. -/
theorem multiStepReduction_confluent {m n1 n2 : ModuleExpression}
    (h1 : m.MultiStepReduction n1) (h2 : m.MultiStepReduction n2) :
    ∃ d, n1.MultiStepReduction d ∧ n2.MultiStepReduction d := by
  obtain ⟨d, hd1, hd2⟩ :=
    Relation.church_rosser
      (fun _ _ _ hab hac => ⟨_, .single hab.triangle, .single hac.triangle⟩)
      (reflTransGen_parStep_of_multiStepReduction h1)
      (reflTransGen_parStep_of_multiStepReduction h2)
  exact ⟨d, multiStepReduction_of_reflTransGen_parStep hd1,
    multiStepReduction_of_reflTransGen_parStep hd2⟩

/-- A stuck expression reduces to nothing but itself. -/
theorem Stuck.eq_of_multiStepReduction {m n : ModuleExpression} (hm : Stuck m)
    (h : m.MultiStepReduction n) : m = n := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hstep, _⟩
  · rfl
  · exact absurd ⟨c, hstep⟩ hm

end ModuleExpression

end GaudisCrypt
