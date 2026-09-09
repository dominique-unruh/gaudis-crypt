import GaudisCrypt.Language.ModuleExpressionBasics

/-! # Normalization for module expressions

Weak normalization: every well-typed module expression terminates.  Split off from
`ModuleExpressionBasics.lean` (which develops syntax, typing, reduction and normal forms
without it) so that this — the other deep open fact besides confluence — stands on its own;
`ModuleExpression.lean` collects the consequences.

The proof is Tait's reducibility (logical relations) in its Kripke form: `Red T Γ m` says that
`m` is a well-typed weakly normalizing term of type `T` in context `Γ`, *hereditarily* so under
every elimination the type allows.  The function case quantifies over all renamings `Γ → Γ'`,
which is what makes the relation stable under weakening (`Red.rename`) — needed because the
`abs` case of the fundamental lemma goes under a binder.

The three candidate properties are `Red.weaklyNormalizing`/`Red.hasType` (CR1),
`Red.of_step`/`Red.of_multiStep` (backward closure, CR2) and `Red.of_neutral` (CR3, here in the
sharp form "a normal neutral term is reducible", since `Neutral` in this development already
means *normal* neutral).  `HasType.red_substituteSimultaneously` is the fundamental lemma and
`HasType.terminating` its corollary at the identity substitution. -/

namespace GaudisCrypt

variable [ProgramSpec]

namespace ModuleExpression

/-! ## Renaming preserves reduction and normal forms

A de Bruijn renaming touches only variables, so every syntactic notion of the reduction theory
is stable under it.  These are the facts the Kripke clause of `Red` needs. -/

/-- Being a procedure tuple is a property of the term's shape, not of its variables, so a
    renaming cannot create one. -/
theorem isProcTuple_of_rename {m : ModuleExpression} {ρ : Nat → Nat}
    (h : (m.rename ρ).IsProcTuple) : m.IsProcTuple := by
  induction m generalizing ρ with
  | proc p => exact h
  | procHoles ne p => exact h
  | var n => exact h
  | app f a _ _ => exact h
  | fst e _ => exact h
  | snd e _ => exact h
  | abs body _ => exact h
  | unit => trivial
  | pair a b _ ihb => cases a <;> first | exact ihb h | exact h

mutual

/-- Normal forms are stable under renaming. -/
theorem Normal.rename : ∀ {m : ModuleExpression}, m.Normal → ∀ ρ : Nat → Nat,
    (m.rename ρ).Normal
  | _, .neutral h, ρ => .neutral (h.rename ρ)
  | _, .abs hb,    ρ => .abs (hb.rename (liftRen ρ))
  | _, .pair ha hb, ρ => .pair (ha.rename ρ) (hb.rename ρ)
  | _, .proc,      _ => .proc
  | _, .procHoles, _ => .procHoles
  | _, .unit,      _ => .unit

/-- Neutral forms are stable under renaming. -/
theorem Neutral.rename : ∀ {m : ModuleExpression}, m.Neutral → ∀ ρ : Nat → Nat,
    (m.rename ρ).Neutral
  | _, .var,        _ => .var
  | _, .app hf ha,  ρ => .app (hf.rename ρ) (ha.rename ρ)
  | _, .appProcHoles ne ha hpt, ρ =>
      .appProcHoles ne (ha.rename ρ) fun hc => hpt (isProcTuple_of_rename hc)
  | _, .fst he,     ρ => .fst (he.rename ρ)
  | _, .snd he,     ρ => .snd (he.rename ρ)

end

/-- Reduction is stable under renaming. -/
theorem ReductionStep.rename {m n : ModuleExpression} (h : m.ReductionStep n) (ρ : Nat → Nat) :
    (m.rename ρ).ReductionStep (n.rename ρ) := by
  induction h generalizing ρ with
  | beta =>
      simp only [ModuleExpression.rename, rename_substitute]
      exact .beta
  | delta ne proc inst =>
      simp only [ModuleExpression.rename, HoleSigs.Instantiation.toModuleExpr_rename]
      exact .delta ne proc inst
  | appL _ ih => exact .appL (ih ρ)
  | appR _ ih => exact .appR (ih ρ)
  | lam _ ih => exact .lam (ih (liftRen ρ))
  | pairL _ ih => exact .pairL (ih ρ)
  | pairR _ ih => exact .pairR (ih ρ)
  | fstPair => exact .fstPair
  | fst _ ih => exact .fst (ih ρ)
  | sndPair => exact .sndPair
  | snd _ ih => exact .snd (ih ρ)

/-- Multi-step reduction is stable under renaming. -/
theorem MultiStepReduction.rename {m n : ModuleExpression} (h : m.MultiStepReduction n)
    (ρ : Nat → Nat) : (m.rename ρ).MultiStepReduction (n.rename ρ) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (hstep.rename ρ)

/-! ## Weak normalization

`Terminating` asks for a *stuck* reduct; the reducibility argument needs the sharper "reduces to
a **normal** form", which is stable under renaming (a stuck term need not stay stuck under a
renaming for any obvious syntactic reason, whereas a normal term visibly does).  For well-typed
terms the two agree — `Stuck.normal` — and that is how `Terminating` is recovered at the end. -/

/-- `m` reduces to a normal form.  Refines `Terminating`. -/
def WeaklyNormalizing (m : ModuleExpression) : Prop :=
  ∃ n : ModuleExpression, m.MultiStepReduction n ∧ n.Normal

theorem Normal.weaklyNormalizing {m : ModuleExpression} (h : m.Normal) : m.WeaklyNormalizing :=
  ⟨m, .refl, h⟩

theorem WeaklyNormalizing.terminating {m : ModuleExpression} (h : m.WeaklyNormalizing) :
    Terminating m :=
  ⟨h.choose, h.choose_spec.2.stuck, h.choose_spec.1⟩

/-- Weak normalization is closed under expansion by a single step. -/
theorem WeaklyNormalizing.head {m m' : ModuleExpression} (hstep : m.ReductionStep m')
    (h : m'.WeaklyNormalizing) : m.WeaklyNormalizing :=
  ⟨h.choose, .head hstep h.choose_spec.1, h.choose_spec.2⟩

/-- Weak normalization is closed under expansion along a multi-step reduction. -/
theorem WeaklyNormalizing.of_multiStep {m m' : ModuleExpression} (hred : m.MultiStepReduction m')
    (h : m'.WeaklyNormalizing) : m.WeaklyNormalizing :=
  ⟨h.choose, hred.trans h.choose_spec.1, h.choose_spec.2⟩

theorem WeaklyNormalizing.rename {m : ModuleExpression} (h : m.WeaklyNormalizing)
    (ρ : Nat → Nat) : (m.rename ρ).WeaklyNormalizing :=
  ⟨h.choose.rename ρ, h.choose_spec.1.rename ρ, h.choose_spec.2.rename ρ⟩

theorem WeaklyNormalizing.abs {b : ModuleExpression} (h : b.WeaklyNormalizing) :
    (ModuleExpression.abs b).WeaklyNormalizing :=
  ⟨.abs h.choose, multiStepReduction_abs_cong h.choose_spec.1, .abs h.choose_spec.2⟩

theorem WeaklyNormalizing.pair {a b : ModuleExpression} (ha : a.WeaklyNormalizing)
    (hb : b.WeaklyNormalizing) : (ModuleExpression.pair a b).WeaklyNormalizing :=
  ⟨.pair ha.choose hb.choose,
   multiStepReduction_pair_cong ha.choose_spec.1 hb.choose_spec.1,
   .pair ha.choose_spec.2 hb.choose_spec.2⟩

/-! ## Renamings compose -/

namespace HasType

omit [ProgramSpec] in
theorem isRenaming_id {Γ : ModuleContext} : IsRenaming Γ Γ id := fun h => ⟨h, rfl⟩

omit [ProgramSpec] in
theorem IsRenaming.comp {Δ Γ Ξ : ModuleContext} {ρ ρ' : Nat → Nat} (h : IsRenaming Δ Γ ρ)
    (h' : IsRenaming Γ Ξ ρ') : IsRenaming Δ Ξ (ρ' ∘ ρ) := fun hn => by
  obtain ⟨h1, e1⟩ := h hn
  obtain ⟨h2, e2⟩ := h' h1
  exact ⟨h2, e2.trans e1⟩

end HasType

/-! ## The reducibility relation -/

/-- Tait's reducibility candidates, Kripke-style.  `Red T Γ m` says: `m` has type `T` in `Γ` and
    is weakly normalizing, and hereditarily so under the eliminations `T` allows — projections at
    a product type, and application to a reducible argument (in any context reachable from `Γ` by
    a renaming) at a function type. -/
def Red : ModuleTypeRep → ModuleContext → ModuleExpression → Prop
  | .proc sig => fun Γ m => m.HasType Γ (.proc sig) ∧ m.WeaklyNormalizing
  | .unit => fun Γ m => m.HasType Γ .unit ∧ m.WeaklyNormalizing
  | .prod A B => fun Γ m =>
      m.HasType Γ (.prod A B) ∧ m.WeaklyNormalizing ∧ Red A Γ (.fst m) ∧ Red B Γ (.snd m)
  | .arr A B => fun Γ m =>
      m.HasType Γ (.arr A B) ∧ m.WeaklyNormalizing ∧
        ∀ {Γ' : ModuleContext} {ρ : Nat → Nat}, HasType.IsRenaming Γ Γ' ρ →
          ∀ {n : ModuleExpression}, Red A Γ' n → Red B Γ' (.app (m.rename ρ) n)

/-- CR1, typing half. -/
theorem Red.hasType {T : ModuleTypeRep} {Γ : ModuleContext} {m : ModuleExpression}
    (h : Red T Γ m) : m.HasType Γ T := by
  cases T <;> exact h.1

/-- CR1, normalization half. -/
theorem Red.weaklyNormalizing {T : ModuleTypeRep} {Γ : ModuleContext} {m : ModuleExpression}
    (h : Red T Γ m) : m.WeaklyNormalizing := by
  cases T with
  | proc => exact h.2
  | unit => exact h.2
  | prod => exact h.2.1
  | arr => exact h.2.1

/-- CR2: reducibility is closed under expansion by a single step. -/
theorem Red.of_step : ∀ {T : ModuleTypeRep} {Γ : ModuleContext} {m m' : ModuleExpression},
    m.HasType Γ T → m.ReductionStep m' → Red T Γ m' → Red T Γ m := by
  intro T
  induction T with
  | proc sig => intro Γ m m' hty hstep h; exact ⟨hty, .head hstep h.2⟩
  | unit => intro Γ m m' hty hstep h; exact ⟨hty, .head hstep h.2⟩
  | prod A B ihA ihB =>
      intro Γ m m' hty hstep h
      exact ⟨hty, .head hstep h.2.1, ihA (.fst hty) (.fst hstep) h.2.2.1,
        ihB (.snd hty) (.snd hstep) h.2.2.2⟩
  | arr A B _ ihB =>
      intro Γ m m' hty hstep h
      refine ⟨hty, .head hstep h.2.1, ?_⟩
      intro Γ' ρ hρ n hn
      exact ihB (.app (hty.rename hρ) hn.hasType) (.appL (hstep.rename ρ)) (h.2.2 hρ hn)

/-- CR2 along a multi-step reduction. -/
theorem Red.of_multiStep {T : ModuleTypeRep} {Γ : ModuleContext} {m m' : ModuleExpression}
    (hred : m.MultiStepReduction m') (h : Red T Γ m') : m.HasType Γ T → Red T Γ m := by
  induction hred using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; exact h
  | head hstep _ ih => intro hty; exact Red.of_step hty hstep (ih (HasType.preservation hstep hty))

/-- CR3: a well-typed *normal* neutral term is reducible.  (`Neutral` already implies `Normal`
    in this development, so no reasoning about the term's reducts is needed.) -/
theorem Red.of_neutral : ∀ {T : ModuleTypeRep} {Γ : ModuleContext} {m : ModuleExpression},
    m.Neutral → m.HasType Γ T → Red T Γ m := by
  intro T
  induction T with
  | proc sig => intro Γ m hne hty; exact ⟨hty, (Normal.neutral hne).weaklyNormalizing⟩
  | unit => intro Γ m hne hty; exact ⟨hty, (Normal.neutral hne).weaklyNormalizing⟩
  | prod A B ihA ihB =>
      intro Γ m hne hty
      exact ⟨hty, (Normal.neutral hne).weaklyNormalizing, ihA (.fst hne) (.fst hty),
        ihB (.snd hne) (.snd hty)⟩
  | arr A B _ ihB =>
      intro Γ m hne hty
      refine ⟨hty, (Normal.neutral hne).weaklyNormalizing, ?_⟩
      intro Γ' ρ hρ n hn
      obtain ⟨n₀, hred, hnorm⟩ := hn.weaklyNormalizing
      have htyapp : ModuleExpression.HasType (.app (m.rename ρ) n) Γ' B :=
        .app (hty.rename hρ) hn.hasType
      have hcong : (ModuleExpression.app (m.rename ρ) n).MultiStepReduction
          (.app (m.rename ρ) n₀) := multiStepReduction_app_cong .refl hred
      refine Red.of_multiStep hcong (ihB (.app (hne.rename ρ) hnorm) ?_) htyapp
      exact HasType.preservation_multi htyapp hcong

/-- Reducibility is stable under weakening (any renaming of the context). -/
theorem Red.rename : ∀ {T : ModuleTypeRep} {Γ Γ' : ModuleContext} {m : ModuleExpression}
    {ρ : Nat → Nat}, Red T Γ m → HasType.IsRenaming Γ Γ' ρ → Red T Γ' (m.rename ρ) := by
  intro T
  induction T with
  | proc sig => intro Γ Γ' m ρ h hρ; exact ⟨h.1.rename hρ, h.2.rename ρ⟩
  | unit => intro Γ Γ' m ρ h hρ; exact ⟨h.1.rename hρ, h.2.rename ρ⟩
  | prod A B ihA ihB =>
      intro Γ Γ' m ρ h hρ
      exact ⟨h.1.rename hρ, h.2.1.rename ρ, ihA h.2.2.1 hρ, ihB h.2.2.2 hρ⟩
  | arr A B _ ihB =>
      intro Γ Γ' m ρ h hρ
      refine ⟨h.1.rename hρ, h.2.1.rename ρ, ?_⟩
      intro Γ'' ρ' hρ' n hn
      have hcomp := h.2.2 (hρ.comp hρ') hn
      rwa [← rename_rename] at hcomp

/-! ## The fundamental lemma -/

/-- A substitution all of whose values are reducible at the type their index carries. -/
def RedSubst (Δ Γ : ModuleContext) (σ : Nat → ModuleExpression) : Prop :=
  ∀ {n : Nat} (h : n < Δ.length), Red (Δ[n]'h) Γ (σ n)

theorem RedSubst.isSubst {Δ Γ : ModuleContext} {σ : Nat → ModuleExpression}
    (h : RedSubst Δ Γ σ) : HasType.IsSubst Δ Γ σ := fun hn => (h hn).hasType

/-- Lifting a reducible substitution under a binder keeps it reducible. -/
theorem RedSubst.lift {Δ Γ : ModuleContext} {A : ModuleTypeRep} {σ : Nat → ModuleExpression}
    (h : RedSubst Δ Γ σ) : RedSubst (A :: Δ) (A :: Γ) (liftSubst σ) := by
  intro n hn
  cases n with
  | zero =>
      simp only [liftSubst, List.getElem_cons_zero]
      exact Red.of_neutral .var (.var 0 (by simp))
  | succ n' =>
      have hn' : n' < Δ.length := by simpa using hn
      simp only [liftSubst, List.getElem_cons_succ]
      exact (h hn').rename HasType.isRenaming_succ

/-- **The fundamental lemma of the reducibility argument**: a well-typed term is reducible under
    every reducible substitution. -/
theorem HasType.red_substituteSimultaneously {m : ModuleExpression} {Δ : ModuleContext}
    {T : ModuleTypeRep} (h : m.HasType Δ T) :
    ∀ {Γ : ModuleContext} {σ : Nat → ModuleExpression}, RedSubst Δ Γ σ →
      Red T Γ (m.substituteSimultaneously σ) := by
  induction h with
  | proc p => intro Γ σ _; exact ⟨.proc p, Normal.proc.weaklyNormalizing⟩
  | unit => intro Γ σ _; exact ⟨.unit, Normal.unit.weaklyNormalizing⟩
  | var n hn => intro Γ σ hσ; exact hσ hn
  | @procHoles Δ holes sig ne p =>
      intro Γ σ _
      refine ⟨.procHoles ne p, Normal.procHoles.weaklyNormalizing, ?_⟩
      intro Γ' ρ _ n hn
      simp only [ModuleExpression.substituteSimultaneously, ModuleExpression.rename]
      have htyapp : ModuleExpression.HasType (.app (.procHoles ne p) n) Γ' (.proc sig) :=
        .app (.procHoles ne p) hn.hasType
      refine ⟨htyapp, ?_⟩
      obtain ⟨n₀, hred, hnorm⟩ := hn.weaklyNormalizing
      have hty₀ := HasType.preservation_multi hn.hasType hred
      have hcong : (ModuleExpression.app (.procHoles ne p) n).MultiStepReduction
          (.app (.procHoles ne p) n₀) := multiStepReduction_app_cong .refl hred
      refine WeaklyNormalizing.of_multiStep hcong ?_
      by_cases hpt : n₀.IsProcTuple
      · obtain ⟨inst, rfl⟩ := exists_toModuleExpr hty₀ hpt
        exact WeaklyNormalizing.head (.delta ne p inst) Normal.proc.weaklyNormalizing
      · exact (Normal.neutral (.appProcHoles ne hnorm hpt)).weaklyNormalizing
  | app _ _ ihf iha =>
      intro Γ σ hσ
      have hfun := ihf hσ
      have happ := hfun.2.2 HasType.isRenaming_id (iha hσ)
      rwa [rename_id] at happ
  | fst _ ihe => intro Γ σ hσ; exact (ihe hσ).2.2.1
  | snd _ ihe => intro Γ σ hσ; exact (ihe hσ).2.2.2
  | @pair Δ A B a b hta htb iha ihb =>
      intro Γ σ hσ
      have hty : ModuleExpression.HasType
          ((ModuleExpression.pair a b).substituteSimultaneously σ) Γ (.prod A B) :=
        (ModuleExpression.HasType.pair hta htb).substituteSimultaneously hσ.isSubst
      refine ⟨hty, (iha hσ).weaklyNormalizing.pair (ihb hσ).weaklyNormalizing, ?_, ?_⟩
      · exact Red.of_step (.fst hty) .fstPair (iha hσ)
      · exact Red.of_step (.snd hty) .sndPair (ihb hσ)
  | @abs Δ A B body hbody ih =>
      intro Γ σ hσ
      have hty : ModuleExpression.HasType
          ((ModuleExpression.abs body).substituteSimultaneously σ) Γ (.arr A B) :=
        (ModuleExpression.HasType.abs hbody).substituteSimultaneously hσ.isSubst
      refine ⟨hty, ((ih hσ.lift).weaklyNormalizing).abs, ?_⟩
      intro Γ' ρ hρ n hn
      have htyapp : ModuleExpression.HasType
          (.app (((ModuleExpression.abs body).substituteSimultaneously σ).rename ρ) n) Γ' B :=
        .app (hty.rename hρ) hn.hasType
      have hτ : RedSubst (A :: Δ) Γ' (fun j => Nat.rec n (fun k _ => (σ k).rename ρ) j) := by
        intro j hj
        cases j with
        | zero => exact hn
        | succ k =>
            have hk : k < Δ.length := by simpa using hj
            exact (hσ hk).rename hρ
      have heq : ((body.substituteSimultaneously (liftSubst σ)).rename (liftRen ρ)).substitute n
          = body.substituteSimultaneously (fun j => Nat.rec n (fun k _ => (σ k).rename ρ) j) := by
        rw [rename_substituteSimultaneously, ← liftSubst_rename,
          substitute_substituteSimultaneously_liftSubst]
      simp only [ModuleExpression.substituteSimultaneously, ModuleExpression.rename] at htyapp ⊢
      refine Red.of_step htyapp .beta ?_
      rw [heq]
      exact ih hτ

/-! ## Weak normalization -/

/-- **Weak normalization**: every well-typed module expression reduces to a normal form, hence
    terminates.  Instantiate the fundamental lemma at the identity substitution, which is
    reducible because a variable is a normal neutral term. -/
theorem HasType.terminating {m Δ T} (h : m.HasType Δ T) : Terminating m := by
  have hσ : RedSubst Δ Δ (fun n => .var n) := fun hn => Red.of_neutral .var (.var _ hn)
  have hred := h.red_substituteSimultaneously hσ
  rw [substituteSimultaneously_var] at hred
  exact hred.weaklyNormalizing.terminating

end ModuleExpression

end GaudisCrypt
