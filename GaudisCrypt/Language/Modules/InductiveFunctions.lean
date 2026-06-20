import GaudisCrypt.Language.Modules

open GaudisCrypt.Language.Modules
open GaudisCrypt.Language.Programs

namespace GaudisCrypt.Language.Modules.InductiveFunctions

variable [ProgramSpec]

structure InductiveFunction t :=
  nothing : t
  join : t → t → t
  proc {holes sig} (p : ProcedureWithHoles holes sig) : t

class Reducible {t : Type _} (ind : InductiveFunction t)
    extends Preorder t, Std.Commutative ind.join, Std.Associative ind.join where
  join_mono_left : ∀ {a a' b : t}, a' ≤ a → ind.join a' b ≤ ind.join a b
  join_mono_right : ∀ {a b b' : t}, b' ≤ b → ind.join a b' ≤ ind.join a b
  le_join_left : ∀ a b : t, a ≤ ind.join a b
  le_join_right : ∀ a b : t, b ≤ ind.join a b
  join_idem : ∀ x : t, ind.join x x ≤ x
  delta_bound :
    ∀ {holes : HoleSigs} {sig : ProcedureSignature} (proc : ProcedureWithHoles holes sig)
      (args : holes.Instantiation),
        ind.proc (proc.instantiate args)
          ≤ args.toList.foldr (fun p acc => ind.join (ind.proc p.2) acc) (ind.proc proc)

/-- Evaluate an instantiation (a dependent tuple of procedures) by folding over the list
`inst.toList`.

This matches the evaluation of `inst.toModuleTuple` under `evalMexpr` (see
`evalMexpr_toModuleTuple`). -/
def InductiveFunction.evalInstantiationFold {t : Type _} (ind : InductiveFunction t)
    {holes : HoleSigs} (inst : holes.Instantiation) : t :=
  (HoleSigs.Instantiation.toList (holes := holes) inst).foldr
    (fun p acc => ind.join (ind.proc p.2) acc)
    ind.nothing

def InductiveFunction.evalMexpr {t mctx mt} (ind : InductiveFunction t)
  (m : ModuleExpression mctx mt) : t := match m with
  | .proc p => ind.proc p
  | .procHoles _ p => ind.proc p
  | .var _ => ind.nothing
  | .app m n => ind.join (InductiveFunction.evalMexpr ind m) (InductiveFunction.evalMexpr ind n)
  | .fst m => InductiveFunction.evalMexpr ind m
  | .snd m => InductiveFunction.evalMexpr ind m
  | .abs m => InductiveFunction.evalMexpr ind m
  | .pair m n => ind.join (InductiveFunction.evalMexpr ind m) (InductiveFunction.evalMexpr ind n)
  | .unit => ind.nothing

lemma InductiveFunction.evalMexpr_rename {t : Type _} (ind : InductiveFunction t)
    {Δ Γ : ModuleContext} {T : ModuleType} (m : ModuleExpression Δ T)
    (ρ : ∀ {T}, ModuleContextIdx Δ T → ModuleContextIdx Γ T) :
    ind.evalMexpr (m.rename ρ) = ind.evalMexpr m := by
  induction m generalizing Γ with
  | unit => rfl
  | proc p => rfl
  | procHoles ne p => rfl
  | var r => rfl
  | app f a ihf iha =>
      simp [ModuleExpression.rename, InductiveFunction.evalMexpr, ihf (Γ := Γ) ρ, iha (Γ := Γ) ρ]
  | fst e ihe =>
      simpa [ModuleExpression.rename, InductiveFunction.evalMexpr] using ihe (Γ := Γ) ρ
  | snd e ihe =>
      simpa [ModuleExpression.rename, InductiveFunction.evalMexpr] using ihe (Γ := Γ) ρ
  | abs body ih =>
      -- `evalMexpr` ignores binders.
      simpa [ModuleExpression.rename, InductiveFunction.evalMexpr] using
        ih (Γ := ModuleContext.append Γ _) (ρ := liftRenaming ρ)
  | pair a b iha ihb =>
      simp [ModuleExpression.rename, InductiveFunction.evalMexpr, iha (Γ := Γ) ρ, ihb (Γ := Γ) ρ]

lemma InductiveFunction.join_join_right_join_of_idem {t : Type _} (ind : InductiveFunction t)
    [Reducible ind]
    (join_idem : ∀ x : t, ind.join x x ≤ x) (x y e : t) :
    ind.join (ind.join x e) (ind.join y e) ≤ ind.join (ind.join x y) e := by
  -- `(x ⊔ e) ⊔ (y ⊔ e) ≤ (x ⊔ y) ⊔ e`.
  calc
    ind.join (ind.join x e) (ind.join y e)
        = ind.join x (ind.join e (ind.join y e)) := by
            simp [Std.Associative.assoc]
    _ = ind.join x (ind.join (ind.join y e) e) := by
            simp [Std.Commutative.comm]
    _ = ind.join x (ind.join y (ind.join e e)) := by
            simp [Std.Associative.assoc]
    _ ≤ ind.join x (ind.join y e) := by
            -- Replace `e ⊔ e` by `e` using `e ⊔ e ≤ e` and monotonicity.
            have hy : ind.join y (ind.join e e) ≤ ind.join y e :=
              Reducible.join_mono_right (ind := ind) (a := y)
                (b' := ind.join e e) (b := e) (join_idem e)
            exact Reducible.join_mono_right (ind := ind) (a := x)
              (b' := ind.join y (ind.join e e)) (b := ind.join y e) hy
    _ = ind.join (ind.join x y) e := by
            simp [Std.Associative.assoc]

lemma InductiveFunction.evalMexpr_substituteSimultaneously_le {t : Type _} (ind : InductiveFunction t)
    [Reducible ind] :
    ∀ {Δ Γ : ModuleContext} {T : ModuleType} (m : ModuleExpression Δ T)
      (σ : ∀ {T}, ModuleContextIdx Δ T → ModuleExpression Γ T) (extra : t)
      (hσ : ∀ {T} (r : ModuleContextIdx Δ T), ind.evalMexpr (σ r) ≤ ind.join ind.nothing extra),
        ind.evalMexpr (substituteSimultaneously σ m) ≤ ind.join (ind.evalMexpr m) extra := by
  intro Δ Γ T m
  induction m generalizing Γ with
  | unit =>
      intro σ extra hσ
      simpa [substituteSimultaneously, InductiveFunction.evalMexpr] using
        (Reducible.le_join_left (ind := ind) ind.nothing extra)
  | proc p =>
      intro σ extra hσ
      simpa [substituteSimultaneously, InductiveFunction.evalMexpr] using
        (Reducible.le_join_left (ind := ind) (ind.proc p) extra)
  | procHoles ne p =>
      intro σ extra hσ
      simpa [substituteSimultaneously, InductiveFunction.evalMexpr] using
        (Reducible.le_join_left (ind := ind) (ind.proc p) extra)
  | var r =>
      intro σ extra hσ
      simpa [substituteSimultaneously, InductiveFunction.evalMexpr] using (hσ r)
  | app f a ihf iha =>
      intro σ extra hσ
      have hf := ihf (Γ := Γ) (σ := σ) (extra := extra) hσ
      have ha := iha (Γ := Γ) (σ := σ) (extra := extra) hσ
      have h1 :
          ind.join (ind.evalMexpr (substituteSimultaneously σ f))
              (ind.evalMexpr (substituteSimultaneously σ a))
            ≤ ind.join (ind.join (ind.evalMexpr f) extra) (ind.join (ind.evalMexpr a) extra) := by
        have hleft :
            ind.join (ind.evalMexpr (substituteSimultaneously σ f))
                (ind.evalMexpr (substituteSimultaneously σ a))
              ≤ ind.join (ind.join (ind.evalMexpr f) extra)
                  (ind.evalMexpr (substituteSimultaneously σ a)) :=
          Reducible.join_mono_left (ind := ind)
            (b := ind.evalMexpr (substituteSimultaneously σ a)) hf
        have hright :
            ind.join (ind.join (ind.evalMexpr f) extra)
                (ind.evalMexpr (substituteSimultaneously σ a))
              ≤ ind.join (ind.join (ind.evalMexpr f) extra)
                  (ind.join (ind.evalMexpr a) extra) :=
          Reducible.join_mono_right (ind := ind)
            (a := ind.join (ind.evalMexpr f) extra) ha
        exact hleft.trans hright
      have h2 :
          ind.join (ind.join (ind.evalMexpr f) extra) (ind.join (ind.evalMexpr a) extra)
            ≤ ind.join (ind.join (ind.evalMexpr f) (ind.evalMexpr a)) extra :=
        InductiveFunction.join_join_right_join_of_idem ind (Reducible.join_idem (ind := ind)) _ _ _
      -- `evalMexpr` is homomorphic on `app`, so conclude by composing inequalities.
      simpa [substituteSimultaneously, InductiveFunction.evalMexpr] using h1.trans h2
  | fst e ihe =>
      intro σ extra hσ
      simpa [substituteSimultaneously, InductiveFunction.evalMexpr] using
        ihe (Γ := Γ) (σ := σ) (extra := extra) hσ
  | snd e ihe =>
      intro σ extra hσ
      simpa [substituteSimultaneously, InductiveFunction.evalMexpr] using
        ihe (Γ := Γ) (σ := σ) (extra := extra) hσ
  | abs body ih =>
      intro σ extra hσ
      -- `evalMexpr` ignores binders, so we can reuse the IH by instantiating `Γ` and `σ`.
      -- This avoids reasoning about `liftSubstitution`.
      have ih' := ih (Γ := ModuleContext.append Γ _)
        (σ := liftSubstitution (A := _) σ) (extra := extra) (hσ := by
          intro T r
          -- In the lifted context, `.zero` maps to `.var .zero` and `.succ r` maps to a rename of `σ r`.
          cases r with
          | zero =>
              simpa [liftSubstitution, InductiveFunction.evalMexpr] using
                (Reducible.le_join_left (ind := ind) ind.nothing extra)
          | succ r =>
              have := hσ r
              simpa [liftSubstitution,
                InductiveFunction.evalMexpr_rename ind (m := σ r)
                  (ρ := fun {_} r => ModuleContextIdx.succ r)] using this)
      simpa [substituteSimultaneously, InductiveFunction.evalMexpr] using ih'
  | pair a b iha ihb =>
      intro σ extra hσ
      have ha := iha (Γ := Γ) (σ := σ) (extra := extra) hσ
      have hb := ihb (Γ := Γ) (σ := σ) (extra := extra) hσ
      have h1 :
          ind.join (ind.evalMexpr (substituteSimultaneously σ a))
              (ind.evalMexpr (substituteSimultaneously σ b))
            ≤ ind.join (ind.join (ind.evalMexpr a) extra) (ind.join (ind.evalMexpr b) extra) := by
        have hleft :
            ind.join (ind.evalMexpr (substituteSimultaneously σ a))
                (ind.evalMexpr (substituteSimultaneously σ b))
              ≤ ind.join (ind.join (ind.evalMexpr a) extra)
                  (ind.evalMexpr (substituteSimultaneously σ b)) :=
          Reducible.join_mono_left (ind := ind) (b := ind.evalMexpr (substituteSimultaneously σ b)) ha
        have hright :
            ind.join (ind.join (ind.evalMexpr a) extra)
                (ind.evalMexpr (substituteSimultaneously σ b))
              ≤ ind.join (ind.join (ind.evalMexpr a) extra)
                  (ind.join (ind.evalMexpr b) extra) :=
          Reducible.join_mono_right (ind := ind) (a := ind.join (ind.evalMexpr a) extra) hb
        exact hleft.trans hright
      have h2 :
          ind.join (ind.join (ind.evalMexpr a) extra) (ind.join (ind.evalMexpr b) extra)
            ≤ ind.join (ind.join (ind.evalMexpr a) (ind.evalMexpr b)) extra :=
        InductiveFunction.join_join_right_join_of_idem ind (Reducible.join_idem (ind := ind)) _ _ _
      simpa [substituteSimultaneously, InductiveFunction.evalMexpr] using h1.trans h2

lemma InductiveFunction.evalMexpr_substitute_le {t : Type _} (ind : InductiveFunction t)
    [Reducible ind]
    {Δ : ModuleContext} {A T : ModuleType}
    (body : ModuleExpression (ModuleContext.append Δ A) T) (arg : ModuleExpression Δ A) :
    ind.evalMexpr (substitute body arg) ≤ ind.join (ind.evalMexpr body) (ind.evalMexpr arg) := by
  let σ : ∀ {T}, ModuleContextIdx (ModuleContext.append Δ A) T → ModuleExpression Δ T :=
    variableSubstitution arg
  have hσ : ∀ {T} (r : ModuleContextIdx (ModuleContext.append Δ A) T),
      ind.evalMexpr (σ r) ≤ ind.join ind.nothing (ind.evalMexpr arg) := by
    intro T r
    cases r with
    | zero =>
        simpa [σ, variableSubstitution] using Reducible.le_join_right (ind := ind) ind.nothing (ind.evalMexpr arg)
    | succ r =>
        simpa [σ, variableSubstitution, InductiveFunction.evalMexpr] using Reducible.le_join_left (ind := ind) ind.nothing (ind.evalMexpr arg)
  simpa [substitute] using
    (InductiveFunction.evalMexpr_substituteSimultaneously_le (ind := ind)
      (m := body) (σ := σ) (extra := ind.evalMexpr arg) hσ)

def InductiveFunction.eval {t mt} (ind : InductiveFunction t) (m : Module mt) :=
  InductiveFunction.evalMexpr ind (m.expression)

lemma InductiveFunction.evalMexpr_toModuleTuple {t : Type _} (ind : InductiveFunction t) {Δ : ModuleContext} :
    {holes : HoleSigs} → (inst : holes.Instantiation) →
      ind.evalMexpr (HoleSigs.Instantiation.toModuleTuple (Δ := Δ) inst)
        = ind.evalInstantiationFold (holes := holes) inst
  | .empty,       _    => rfl
  | .append _ _, inst => by
      -- Unfold `toModuleTuple` / `evalMexpr` / `evalInstantiation` and apply IH on the tail.
      simp [HoleSigs.Instantiation.toModuleTuple, InductiveFunction.evalMexpr,
        InductiveFunction.evalInstantiationFold, HoleSigs.Instantiation.toList,
        InductiveFunction.evalMexpr_toModuleTuple]

theorem eval_induction_step {t mctx mt} (ind : InductiveFunction t)
    [Reducible ind]
    {m m' : ModuleExpression mctx mt} (h : ReductionStep m m') :
    ind.evalMexpr m' ≤ ind.evalMexpr m := by
  induction h with
  | beta =>
      rename_i Δ A T body arg
      -- `eval (app (abs body) arg)` is `join (eval body) (eval arg)`.
      simpa [InductiveFunction.evalMexpr] using
        InductiveFunction.evalMexpr_substitute_le (ind := ind) body arg
  | appL _ ih =>
      simpa [InductiveFunction.evalMexpr] using
        (Reducible.join_mono_left (ind := ind) (b := ind.evalMexpr _) ih)
  | appR _ ih =>
      simpa [InductiveFunction.evalMexpr] using
        (Reducible.join_mono_right (ind := ind) (a := ind.evalMexpr _) ih)
  | lam _ ih =>
      simpa [InductiveFunction.evalMexpr] using ih
  | pairL _ ih =>
      simpa [InductiveFunction.evalMexpr] using
        (Reducible.join_mono_left (ind := ind) (b := ind.evalMexpr _) ih)
  | pairR _ ih =>
      simpa [InductiveFunction.evalMexpr] using
        (Reducible.join_mono_right (ind := ind) (a := ind.evalMexpr _) ih)
  | fstPair =>
      rename_i Δ A B a b
      simpa [InductiveFunction.evalMexpr] using
        (Reducible.le_join_left (ind := ind) (ind.evalMexpr a) (ind.evalMexpr b))
  | fst _ ih =>
      simpa [InductiveFunction.evalMexpr] using ih
  | sndPair =>
      rename_i Δ A B a b
      simpa [InductiveFunction.evalMexpr] using
        (Reducible.le_join_right (ind := ind) (ind.evalMexpr a) (ind.evalMexpr b))
  | snd _ ih =>
      simpa [InductiveFunction.evalMexpr] using ih
  | delta inst =>
      rename_i Δ holes sigs ne proc
      let tuple : ModuleExpression Δ holes.toModuleTypeTuple :=
        HoleSigs.Instantiation.toModuleTuple (Δ := Δ) (holes := holes) inst
      -- Abbreviation for folding instantiated procedures.
      let f : (Σ sig, Procedure sig) → t → t := fun p acc => ind.join (ind.proc p.2) acc
      let instVal : t := (HoleSigs.Instantiation.toList (holes := holes) inst).foldr f ind.nothing
      have htup0 : ind.evalMexpr tuple = ind.evalInstantiationFold (holes := holes) inst := by
        simpa [tuple] using
          InductiveFunction.evalMexpr_toModuleTuple (ind := ind) (Δ := Δ) (holes := holes) inst
      have htup : ind.evalMexpr tuple = instVal := by
        simpa [InductiveFunction.evalInstantiationFold, instVal, f] using htup0

      -- `delta_bound` is stated with the fold's base = `ind.proc proc`. Convert it into the
      -- form `≤ ind.join (ind.proc proc) instVal` (base `ind.nothing`) using monotonicity.
      have hδ0 : ind.proc (proc.instantiate inst)
            ≤ (HoleSigs.Instantiation.toList (holes := holes) inst).foldr f (ind.proc proc) :=
        (Reducible.delta_bound (ind := ind) (proc := proc) inst)

      have hfold :
          (HoleSigs.Instantiation.toList (holes := holes) inst).foldr f (ind.proc proc)
            ≤ ind.join (ind.proc proc) instVal := by
        -- `instVal` is definitionally the fold with base `nothing`, so rewrite it and
        -- prove a list lemma by induction.
        dsimp [instVal]
        -- Induction on the explicit list.
        -- Induct on the concrete list.
        induction HoleSigs.Instantiation.toList (holes := holes) inst with
        | nil =>
            -- base: `foldr _ (proc proc) [] = proc proc` and RHS is `join (proc proc) nothing`.
            simpa [List.foldr] using
              (Reducible.le_join_left (ind := ind) (ind.proc proc) ind.nothing)
        | cons p ps ih =>
            -- Step: lift IH through the outer `join (proc p)`.
            have ih' : ps.foldr f (ind.proc proc) ≤ ind.join (ind.proc proc) (ps.foldr f ind.nothing) := ih
            have h1 : ind.join (ind.proc p.2) (ps.foldr f (ind.proc proc))
                ≤ ind.join (ind.proc p.2) (ind.join (ind.proc proc) (ps.foldr f ind.nothing)) :=
              (Reducible.join_mono_right (ind := ind) (a := ind.proc p.2) ih')
            have h2 : ind.join (ind.proc p.2) (ind.join (ind.proc proc) (ps.foldr f ind.nothing))
                = ind.join (ind.proc proc) (ind.join (ind.proc p.2) (ps.foldr f ind.nothing)) := by
              calc
                ind.join (ind.proc p.2) (ind.join (ind.proc proc) (ps.foldr f ind.nothing))
                    = ind.join (ind.join (ind.proc p.2) (ind.proc proc)) (ps.foldr f ind.nothing) := by
                        simp [Std.Associative.assoc]
                _ = ind.join (ind.join (ind.proc proc) (ind.proc p.2)) (ps.foldr f ind.nothing) := by
                        simp [Std.Commutative.comm]
                _ = ind.join (ind.proc proc) (ind.join (ind.proc p.2) (ps.foldr f ind.nothing)) := by
                        simp [Std.Associative.assoc]
            simpa [List.foldr, f, h2] using h1

      have hδ : ind.proc (proc.instantiate inst)
            ≤ ind.join (ind.proc proc) instVal :=
        le_trans hδ0 hfold

      have hδ' : ind.proc (proc.instantiate inst)
            ≤ ind.join (ind.proc proc) (ind.evalMexpr tuple) := by
        simpa [htup] using hδ
      -- Unfold `evalMexpr` on the δ-redex.
      simpa [InductiveFunction.evalMexpr, tuple] using hδ'

theorem evalMexpr_reduce {t mctx mt} (ind : InductiveFunction t)
    [Reducible ind] (m : ModuleExpression mctx mt) :
    ind.evalMexpr (reduce m) ≤ ind.evalMexpr m := by
  -- `reduce` computes a normal form reachable by multi-step reduction.
  -- Lift `eval_induction_step` along the `Rewriting.Star` proof.
  have hStar : ∀ {m m' : ModuleExpression mctx mt},
      MultiStepReduction m m' → ind.evalMexpr m' ≤ ind.evalMexpr m := by
    intro m m' h
    induction h with
    | refl =>
        exact le_rfl
    | tail _ hstep ih =>
        exact le_trans (eval_induction_step (ind := ind) hstep) ih
  exact hStar (multiStepReduction_reduce (m := m))


theorem InductiveFunction.app_moduleExpression (ind : InductiveFunction t)
  (a : ModuleExpression Γ (.arr A B)) (b : ModuleExpression Γ A) :
    ind.evalMexpr (.app a b) = ind.join (ind.evalMexpr a) (ind.evalMexpr b) := by
    simp [InductiveFunction.evalMexpr]

theorem InductiveFunction.app (ind : InductiveFunction t) [Reducible ind] (a : Module (.arr A B)) (b : Module A) :
    ind.eval (Module.app a b) ≤ ind.join (ind.eval a) (ind.eval b) := by
  sorry

theorem InductiveFunction.pair_moduleExpression (ind : InductiveFunction t)
  (a : ModuleExpression Γ A) (b : ModuleExpression Γ B) :
    ind.evalMexpr (.pair a b) = ind.join (ind.evalMexpr a) (ind.evalMexpr b) := by
    simp [InductiveFunction.evalMexpr]

theorem InductiveFunction.pair (ind : InductiveFunction t) (a : Module A) (b : Module B) :
    ind.eval (Module.pair a b) = ind.join (ind.eval a) (ind.eval b) := by
  sorry

@[simp]
theorem InductiveFunction.fst_moduleExpression (ind : InductiveFunction t)
  (a : ModuleExpression Γ (.prod A B)) :
    ind.evalMexpr (.fst a) = ind.evalMexpr a := by
    simp [InductiveFunction.evalMexpr]

theorem InductiveFunction.fst (ind : InductiveFunction t) [Reducible ind]
  (a : Module (.prod A B)) :
    ind.eval (.fst a) ≤ ind.eval a := by
    sorry

@[simp]
theorem InductiveFunction.snd_moduleExpression (ind : InductiveFunction t)
  (a : ModuleExpression Γ (.prod A B)) :
    ind.evalMexpr (.snd a) = ind.evalMexpr a := by
    simp [InductiveFunction.evalMexpr]

theorem InductiveFunction.snd (ind : InductiveFunction t) [Reducible ind]
  (a : Module (.prod A B)) :
    ind.eval (.snd a) ≤ ind.eval a := by
    sorry

@[simp]
theorem InductiveFunction.unit_moduleExpression {ctxt} (ind : InductiveFunction t) :
  ind.evalMexpr (.unit : ModuleExpression ctxt _) = ind.nothing := by
    simp [InductiveFunction.evalMexpr]

@[simp]
theorem InductiveFunction.unit (ind : InductiveFunction t) (m : Module .unit) :
  ind.eval m = ind.nothing := by
    sorry

end GaudisCrypt.Language.Modules.InductiveFunctions
