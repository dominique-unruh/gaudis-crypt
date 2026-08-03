import GaudisCrypt.Language.Modules

open GaudisCrypt
open GaudisCrypt

namespace GaudisCrypt

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

def InductiveFunction.evalMexpr {t} (ind : InductiveFunction t)
  (m : ModuleExpression) : t := match m with
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
    (m : ModuleExpression) (ρ : Nat → Nat) :
    ind.evalMexpr (m.rename ρ) = ind.evalMexpr m := by
  induction m generalizing ρ with
  | unit => rfl
  | proc p => rfl
  | procHoles ne p => rfl
  | var r => rfl
  | app f a ihf iha =>
      simp [ModuleExpression.rename, InductiveFunction.evalMexpr, ihf ρ, iha ρ]
  | fst e ihe =>
      simpa [ModuleExpression.rename, InductiveFunction.evalMexpr] using ihe ρ
  | snd e ihe =>
      simpa [ModuleExpression.rename, InductiveFunction.evalMexpr] using ihe ρ
  | abs body ih =>
      -- `evalMexpr` ignores binders.
      simpa [ModuleExpression.rename, InductiveFunction.evalMexpr] using
        ih (ModuleExpression.liftRen ρ)
  | pair a b iha ihb =>
      simp [ModuleExpression.rename, InductiveFunction.evalMexpr, iha ρ, ihb ρ]

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
    ∀ (m : ModuleExpression) (σ : Nat → ModuleExpression) (extra : t)
      (_ : ∀ n, ind.evalMexpr (σ n) ≤ ind.join ind.nothing extra),
        ind.evalMexpr (m.substituteSimultaneously σ) ≤ ind.join (ind.evalMexpr m) extra := by
  intro m
  induction m with
  | unit =>
      intro σ extra hσ
      simpa [ModuleExpression.substituteSimultaneously, InductiveFunction.evalMexpr] using
        (Reducible.le_join_left (ind := ind) ind.nothing extra)
  | proc p =>
      intro σ extra hσ
      simpa [ModuleExpression.substituteSimultaneously, InductiveFunction.evalMexpr] using
        (Reducible.le_join_left (ind := ind) (ind.proc p) extra)
  | procHoles ne p =>
      intro σ extra hσ
      simpa [ModuleExpression.substituteSimultaneously, InductiveFunction.evalMexpr] using
        (Reducible.le_join_left (ind := ind) (ind.proc p) extra)
  | var n =>
      intro σ extra hσ
      simpa [ModuleExpression.substituteSimultaneously, InductiveFunction.evalMexpr] using (hσ n)
  | app f a ihf iha =>
      intro σ extra hσ
      have hf := ihf σ extra hσ
      have ha := iha σ extra hσ
      have h1 :
          ind.join (ind.evalMexpr (f.substituteSimultaneously σ))
              (ind.evalMexpr (a.substituteSimultaneously σ))
            ≤ ind.join (ind.join (ind.evalMexpr f) extra) (ind.join (ind.evalMexpr a) extra) := by
        have hleft :
            ind.join (ind.evalMexpr (f.substituteSimultaneously σ))
                (ind.evalMexpr (a.substituteSimultaneously σ))
              ≤ ind.join (ind.join (ind.evalMexpr f) extra)
                  (ind.evalMexpr (a.substituteSimultaneously σ)) :=
          Reducible.join_mono_left (ind := ind)
            (b := ind.evalMexpr (a.substituteSimultaneously σ)) hf
        have hright :
            ind.join (ind.join (ind.evalMexpr f) extra)
                (ind.evalMexpr (a.substituteSimultaneously σ))
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
      simpa [ModuleExpression.substituteSimultaneously, InductiveFunction.evalMexpr] using h1.trans h2
  | fst e ihe =>
      intro σ extra hσ
      simpa [ModuleExpression.substituteSimultaneously, InductiveFunction.evalMexpr] using
        ihe σ extra hσ
  | snd e ihe =>
      intro σ extra hσ
      simpa [ModuleExpression.substituteSimultaneously, InductiveFunction.evalMexpr] using
        ihe σ extra hσ
  | abs body ih =>
      intro σ extra hσ
      -- `evalMexpr` ignores binders; reuse the IH under `liftSubst σ`.
      have ih' := ih (ModuleExpression.liftSubst σ) extra (by
          intro n
          cases n with
          | zero =>
              simpa [ModuleExpression.liftSubst, InductiveFunction.evalMexpr] using
                (Reducible.le_join_left (ind := ind) ind.nothing extra)
          | succ n =>
              have := hσ n
              simpa [ModuleExpression.liftSubst,
                InductiveFunction.evalMexpr_rename ind (σ n) Nat.succ] using this)
      simpa [ModuleExpression.substituteSimultaneously, InductiveFunction.evalMexpr] using ih'
  | pair a b iha ihb =>
      intro σ extra hσ
      have ha := iha σ extra hσ
      have hb := ihb σ extra hσ
      have h1 :
          ind.join (ind.evalMexpr (a.substituteSimultaneously σ))
              (ind.evalMexpr (b.substituteSimultaneously σ))
            ≤ ind.join (ind.join (ind.evalMexpr a) extra) (ind.join (ind.evalMexpr b) extra) := by
        have hleft :
            ind.join (ind.evalMexpr (a.substituteSimultaneously σ))
                (ind.evalMexpr (b.substituteSimultaneously σ))
              ≤ ind.join (ind.join (ind.evalMexpr a) extra)
                  (ind.evalMexpr (b.substituteSimultaneously σ)) :=
          Reducible.join_mono_left (ind := ind)
            (b := ind.evalMexpr (b.substituteSimultaneously σ)) ha
        have hright :
            ind.join (ind.join (ind.evalMexpr a) extra)
                (ind.evalMexpr (b.substituteSimultaneously σ))
              ≤ ind.join (ind.join (ind.evalMexpr a) extra)
                  (ind.join (ind.evalMexpr b) extra) :=
          Reducible.join_mono_right (ind := ind) (a := ind.join (ind.evalMexpr a) extra) hb
        exact hleft.trans hright
      have h2 :
          ind.join (ind.join (ind.evalMexpr a) extra) (ind.join (ind.evalMexpr b) extra)
            ≤ ind.join (ind.join (ind.evalMexpr a) (ind.evalMexpr b)) extra :=
        InductiveFunction.join_join_right_join_of_idem ind (Reducible.join_idem (ind := ind)) _ _ _
      simpa [ModuleExpression.substituteSimultaneously, InductiveFunction.evalMexpr] using h1.trans h2

lemma InductiveFunction.evalMexpr_substitute_le {t : Type _} (ind : InductiveFunction t)
    [Reducible ind] (body arg : ModuleExpression) :
    ind.evalMexpr (body.substitute arg) ≤ ind.join (ind.evalMexpr body) (ind.evalMexpr arg) := by
  have hσ : ∀ n, ind.evalMexpr (ModuleExpression.variableSubstitution arg n)
      ≤ ind.join ind.nothing (ind.evalMexpr arg) := by
    intro n
    cases n with
    | zero =>
        simpa [ModuleExpression.variableSubstitution] using
          Reducible.le_join_right (ind := ind) ind.nothing (ind.evalMexpr arg)
    | succ n =>
        simpa [ModuleExpression.variableSubstitution, InductiveFunction.evalMexpr] using
          Reducible.le_join_left (ind := ind) ind.nothing (ind.evalMexpr arg)
  simpa [ModuleExpression.substitute] using
    (InductiveFunction.evalMexpr_substituteSimultaneously_le (ind := ind)
      body (ModuleExpression.variableSubstitution arg) (ind.evalMexpr arg) hσ)

def InductiveFunction.eval' {t mt} (ind : InductiveFunction t) (m : Module mt) :=
  ind.evalMexpr m.expression

def InductiveFunction.eval {t} (ind : InductiveFunction t) [i : IsModule M] (m : M) :=
  ind.eval' (Module.cast M m)

lemma InductiveFunction.evalMexpr_toModuleTuple
    {t : Type _} (ind : InductiveFunction t) :
    {holes : HoleSigs} → (inst : holes.Instantiation) →
      ind.evalMexpr (HoleSigs.Instantiation.toModuleExpr inst)
        = ind.evalInstantiationFold (holes := holes) inst
  | .empty,       _    => rfl
  | .append _ _, inst => by
      -- Unfold `toModuleExpr` / `evalMexpr` / `evalInstantiation` and apply IH on the tail.
      simp [HoleSigs.Instantiation.toModuleExpr, InductiveFunction.evalMexpr,
        InductiveFunction.evalInstantiationFold, HoleSigs.Instantiation.toList,
        InductiveFunction.evalMexpr_toModuleTuple]

theorem eval_induction_step {t} (ind : InductiveFunction t)
    [Reducible ind]
    {m m' : ModuleExpression} (h : ModuleExpression.ReductionStep m m') :
    ind.evalMexpr m' ≤ ind.evalMexpr m := by
  induction h with
  | beta =>
      rename_i body arg
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
      rename_i a b
      simpa [InductiveFunction.evalMexpr] using
        (Reducible.le_join_left (ind := ind) (ind.evalMexpr a) (ind.evalMexpr b))
  | fst _ ih =>
      simpa [InductiveFunction.evalMexpr] using ih
  | sndPair =>
      rename_i a b
      simpa [InductiveFunction.evalMexpr] using
        (Reducible.le_join_right (ind := ind) (ind.evalMexpr a) (ind.evalMexpr b))
  | snd _ ih =>
      simpa [InductiveFunction.evalMexpr] using ih
  | delta ne proc inst =>
      rename_i holes sigs
      let tuple : ModuleExpression := HoleSigs.Instantiation.toModuleExpr inst
      -- Abbreviation for folding instantiated procedures.
      let f : (Σ sig, Procedure sig) → t → t := fun p acc => ind.join (ind.proc p.2) acc
      let instVal : t := (HoleSigs.Instantiation.toList (holes := holes) inst).foldr f ind.nothing
      have htup0 : ind.evalMexpr tuple = ind.evalInstantiationFold (holes := holes) inst := by
        simpa [tuple] using
          InductiveFunction.evalMexpr_toModuleTuple (ind := ind) (holes := holes) inst
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

theorem evalMexpr_reduce {t} (ind : InductiveFunction t)
    [Reducible ind] (m : ModuleExpression) (h : m.Terminating) :
    ind.evalMexpr m.reduce ≤ ind.evalMexpr m := by
  -- `reduce` reaches a normal form by multi-step reduction; lift `eval_induction_step`.
  have hStar : ∀ {a b : ModuleExpression},
      a.MultiStepReduction b → ind.evalMexpr b ≤ ind.evalMexpr a := by
    intro a b h
    induction h with
    | refl => exact le_rfl
    | tail _ hstep ih =>
        exact le_trans (eval_induction_step (ind := ind) hstep) ih
  exact hStar (ModuleExpression.multiStepReduction_reduce h)


theorem evalMexpr_upper_bound {t mt} (ind : InductiveFunction t)
    [Reducible ind] {m : ModuleExpression} (h : m.Typed .empty mt) :
    ind.eval (m.toModule h) ≤ ind.evalMexpr m := by
  change ind.evalMexpr m.reduce ≤ ind.evalMexpr m
  exact evalMexpr_reduce ind _ h.terminating

theorem InductiveFunction.app_moduleExpression (ind : InductiveFunction t)
  (a b : ModuleExpression) :
    ind.evalMexpr (.app a b) = ind.join (ind.evalMexpr a) (ind.evalMexpr b) := by
    simp [InductiveFunction.evalMexpr]

theorem InductiveFunction.app' (ind : InductiveFunction t) [Reducible ind] (a : Module (.arr A B)) (b : Module A) :
    ind.eval' (Module.app' a b) ≤ ind.join (ind.eval a) (ind.eval b) :=
  calc ind.eval' (Module.app' a b)
      ≤ ind.evalMexpr (a.expression.pair b.expression) :=
        evalMexpr_reduce ind _ (ModuleExpression.Typed.terminating (.app a.typed b.typed))
    _ = ind.join (ind.eval a) (ind.eval b) := rfl

theorem InductiveFunction.app (ind : InductiveFunction t) [Reducible ind] [IsModule A] [IsModule B]
    (a : Module.Arr A B) (b : A) :
    ind.eval (Module.app a b) ≤ ind.join (ind.eval a) (ind.eval b) := by
  simp only [InductiveFunction.eval, Module.cast_app]
  apply ind.app'


theorem InductiveFunction.pair_moduleExpression (ind : InductiveFunction t)
  (a b : ModuleExpression) :
    ind.evalMexpr (.pair a b) = ind.join (ind.evalMexpr a) (ind.evalMexpr b) := by
    simp [InductiveFunction.evalMexpr]

theorem InductiveFunction.pair' (ind : InductiveFunction t) (a : Module A) (b : Module B) :
    ind.eval' (Module.pair' a b) = ind.join (ind.eval' a) (ind.eval' b) := by
  have h : (a.expression.pair b.expression).reduce = a.expression.pair b.expression :=
    Module.reduce_expression
      ⟨_, ModuleExpression.Typed.pair a.typed b.typed,
        ModuleExpression.NormalClosed.pair a.normal b.normal⟩
  change ind.evalMexpr (a.expression.pair b.expression).reduce = _
  rw [h]
  rfl

theorem InductiveFunction.pair (ind : InductiveFunction t) [IsModule A] [IsModule B]
    (a : A) (b : B) :
    ind.eval (Module.pair a b) = ind.join (ind.eval a) (ind.eval b) := by
  simp only [InductiveFunction.eval, Module.cast, Module.pair, Module.moduleTypeRep, eqRec_eq_cast]
  exact ind.pair' _ _

@[simp]
theorem InductiveFunction.fst_moduleExpression (ind : InductiveFunction t)
  (a : ModuleExpression) :
    ind.evalMexpr (.fst a) = ind.evalMexpr a := by
    simp [InductiveFunction.evalMexpr]

theorem InductiveFunction.fst' (ind : InductiveFunction t) [Reducible ind]
  (a : Module (.prod A B)) :
    ind.eval' (.fst' a) ≤ ind.eval a :=
  calc ind.eval (Module.fst' a)
      ≤ ind.evalMexpr a.expression.fst :=
        evalMexpr_reduce ind _ (ModuleExpression.Typed.terminating (.fst a.typed))
    _ = ind.eval a := InductiveFunction.fst_moduleExpression ind _

theorem InductiveFunction.fst (ind : InductiveFunction t) [Reducible ind] [IsModule A] [IsModule B]
    (a : Module.Prod A B) :
    ind.eval (Module.fst a) ≤ ind.eval a := by
  simp only [InductiveFunction.eval, Module.cast, Module.fst, Module.moduleTypeRep, eqRec_eq_cast,
    cast_cast, cast_eq]
  exact ind.fst' _

@[simp]
theorem InductiveFunction.snd_moduleExpression (ind : InductiveFunction t)
  (a : ModuleExpression) :
    ind.evalMexpr (.snd a) = ind.evalMexpr a := by
    simp [InductiveFunction.evalMexpr]

theorem InductiveFunction.snd' (ind : InductiveFunction t) [Reducible ind]
  (a : Module (.prod A B)) :
    ind.eval' (.snd' a) ≤ ind.eval a :=
  calc ind.eval (Module.snd' a)
      ≤ ind.evalMexpr a.expression.snd :=
        evalMexpr_reduce ind _ (ModuleExpression.Typed.terminating (.snd a.typed))
    _ = ind.eval a := InductiveFunction.snd_moduleExpression ind _

theorem InductiveFunction.snd (ind : InductiveFunction t) [Reducible ind] [IsModule A] [IsModule B]
    (a : Module.Prod A B) :
    ind.eval (Module.snd a) ≤ ind.eval a := by
  simp only [InductiveFunction.eval, Module.cast, Module.snd, Module.moduleTypeRep, eqRec_eq_cast,
    cast_cast, cast_eq]
  exact ind.snd' _

@[simp]
theorem InductiveFunction.unit_moduleExpression (ind : InductiveFunction t) :
  ind.evalMexpr (.unit : ModuleExpression) = ind.nothing := by
    simp [InductiveFunction.evalMexpr]

@[simp]
theorem InductiveFunction.unit (ind : InductiveFunction t) (m : Module .unit) :
  ind.eval m = ind.nothing := by
    have h : m.expression = ModuleExpression.unit := by
      have hn := m.normal
      have ht := m.typed
      generalize he : m.expression = e at hn ht
      cases hn with
      | unit => rfl
      | proc => cases ht
      | procHoles => cases ht
      | abs _ => cases ht
      | pair _ _ => cases ht
    change ind.evalMexpr m.expression = _
    rw [h, InductiveFunction.unit_moduleExpression]



structure InductiveFunctionGettersSetters (T : Type → Type) :=
  nothing : T t
  join : T t → T t → T t
  getter {a s : Type}: Getter a s → T s
  setter {a s : Type}: Setter a s → T s
  reduce (lens : Lens a b) (x : T b) : T a
  extend (lens : Lens a b) (x : T a) : T b

def InductiveFunctionGettersSetters.transfer
  (ind : InductiveFunctionGettersSetters T) (x : T (ProcedureState s)) : T (ProcedureState t) :=
  ind.extend ProcedureState.globalL (ind.reduce ProcedureState.globalL x)

def InductiveFunctionGettersSetters.stmt (ind : InductiveFunctionGettersSetters T) {s} {holes} :
  StmtWithHoles holes s → T (ProcedureState s)
| .skip => ind.nothing
| .sample x e => ind.join (ind.setter x) (ind.getter e)
| .call' x _ b r p =>
    ind.join (ind.setter x)
    (ind.join (ind.transfer (ind.stmt b))
    (ind.join (ind.transfer (ind.getter r)) (ind.getter p)))
| .hole _ x p => ind.join (ind.setter x) (ind.getter p)
| .seq s1 s2 => ind.join (ind.stmt s1) (ind.stmt s2)
| .ifThenElse c t e => ind.join (ind.getter c) (ind.join (ind.stmt t) (ind.stmt e))
| .while c t => ind.join (ind.getter c) (ind.stmt t)

def InductiveFunctionGettersSetters.proc (ind : InductiveFunctionGettersSetters T) {sig holes}
  (proc : ProcedureWithHoles holes sig) : T State :=
  ind.join
  (ind.reduce ProcedureState.globalL (ind.stmt proc.body))
  (ind.reduce ProcedureState.globalL (ind.getter proc.return_val))


class ReducibleGettersSetters {T : Type → Type} (ind : InductiveFunctionGettersSetters T) where
  [preorder : ∀ {t}, Preorder (T t)]
  [comm  : ∀ {t}, Std.Commutative (@ind.join t)]
  [assoc  : ∀ {t}, Std.Associative (@ind.join t)]
  reduce_join (lens : Lens a b) : ind.reduce lens (ind.join r₁ r₂) ≤ ind.join (ind.reduce lens r₁) (ind.reduce lens r₂)
  extend_join (lens : Lens a b) : ind.join (ind.extend lens r₁) (ind.extend lens r₂) ≤ ind.extend lens (ind.join r₁ r₂)
  extend_reduce (lens : Lens a b) (r : T a) : ind.reduce lens (ind.extend lens r) ≤ r
  /-- Monotonicity of `reduce`. Under only a `Preorder` this is not derivable from `reduce_join`
      (the old derivation used antisymmetry to turn `r₁ ≤ r₂` into `join r₁ r₂ = r₂`). -/
  reduce_mono (lens : Lens a b) : r₁ ≤ r₂ → ind.reduce lens r₁ ≤ ind.reduce lens r₂
  /-- Monotonicity of `extend`; see `reduce_mono`. -/
  extend_mono (lens : Lens a b) : r₁ ≤ r₂ → ind.extend lens r₁ ≤ ind.extend lens r₂
  join_mono_left : ∀ {a a' b : T t}, a' ≤ a → ind.join a' b ≤ ind.join a b
  le_join_left : ∀ a b : T t, a ≤ ind.join a b
  join_idem : ∀ x : T t, ind.join x x ≤ x
  nothing_le : ∀ {t} (x : T t), ind.nothing ≤ x

/-! ### Abstract join helpers (replacements for the lattice lemmas `le_sup_*`, `sup_le`, …). -/
section JoinHelpers
variable {T : Type → Type} {ind : InductiveFunctionGettersSetters T}
variable [red : ReducibleGettersSetters ind]
omit [ProgramSpec]

/-- `le_join_right` is derivable from `le_join_left` and `comm`, so it is not assumed by
`ReducibleGettersSetters`. -/
private theorem le_join_right {t} (a b : T t) : red.preorder.le b (ind.join a b) := by
  letI := @red.preorder
  rw [(red.comm (t := t)).comm a b]
  exact red.le_join_left b a

/-- `join_mono_right` is derivable from `join_mono_left` and `comm`, so it is not assumed by
`ReducibleGettersSetters`. -/
private theorem join_mono_right {t} {a b b' : T t} (h : red.preorder.le b' b) :
    red.preorder.le (ind.join a b') (ind.join a b) := by
  letI := @red.preorder
  rw [(red.comm (t := t)).comm a b', (red.comm (t := t)).comm a b]
  exact red.join_mono_left h

private theorem join_le {t} {a b c : T t}
    (ha : red.preorder.le a c) (hb : red.preorder.le b c) :
    red.preorder.le (ind.join a b) c := by
  letI := @red.preorder
  exact le_trans (le_trans (red.join_mono_left ha) (join_mono_right hb)) (red.join_idem c)

private theorem join_mono {t} {a b c d : T t}
    (h₁ : red.preorder.le a c) (h₂ : red.preorder.le b d) :
    red.preorder.le (ind.join a b) (ind.join c d) := by
  letI := @red.preorder
  exact le_trans (red.join_mono_left h₁) (join_mono_right h₂)

private theorem le_join_of_le_left {t} {a b c : T t}
    (h : red.preorder.le a b) : red.preorder.le a (ind.join b c) := by
  letI := @red.preorder
  exact le_trans h (red.le_join_left b c)

private theorem le_join_of_le_right {t} {a b c : T t}
    (h : red.preorder.le a c) : red.preorder.le a (ind.join b c) := by
  letI := @red.preorder
  exact le_trans h (le_join_right b c)

/-- `(x ⊔ e) ⊔ (y ⊔ e) ≤ (x ⊔ y) ⊔ e`, the join-idempotency rearrangement. -/
private theorem join_join_le {t} (x y e : T t) :
    red.preorder.le (ind.join (ind.join x e) (ind.join y e)) (ind.join (ind.join x y) e) := by
  letI := @red.preorder
  have a : ∀ {s} (u v w : T s), ind.join (ind.join u v) w = ind.join u (ind.join v w) :=
    fun {s} => (red.assoc (t := s)).assoc
  have c : ∀ {s} (u v : T s), ind.join u v = ind.join v u :=
    fun {s} => (red.comm (t := s)).comm
  calc
    ind.join (ind.join x e) (ind.join y e)
        = ind.join x (ind.join e (ind.join y e)) := by rw [a]
    _ = ind.join x (ind.join (ind.join y e) e) := by rw [c e (ind.join y e)]
    _ = ind.join x (ind.join y (ind.join e e)) := by rw [a y e e]
    _ ≤ ind.join x (ind.join y e) := join_mono_right (join_mono_right (red.join_idem e))
    _ = ind.join (ind.join x y) e := by rw [a]

end JoinHelpers

/-- The base of a fold can be split off (the direction needed by `proc_instantiate`):
    `base ⊔ foldr … nothing l ≤ foldr … base l`.  Proven with only a `Preorder`; the old
    equality version used antisymmetry. -/
private theorem foldr_sup_base (ind : InductiveFunctionGettersSetters T)
    [red : ReducibleGettersSetters ind] (base : T State) (l : List (Σ sig, Procedure sig)) :
    red.preorder.le
      (ind.join base (List.foldr (fun p acc => ind.join (ind.proc p.2) acc) ind.nothing l))
      (List.foldr (fun p acc => ind.join (ind.proc p.2) acc) base l) := by
  letI := @red.preorder
  have a : ∀ {s} (u v w : T s), ind.join (ind.join u v) w = ind.join u (ind.join v w) :=
    fun {s} => (red.assoc (t := s)).assoc
  have c : ∀ {s} (u v : T s), ind.join u v = ind.join v u :=
    fun {s} => (red.comm (t := s)).comm
  induction l with
  | nil =>
      simp only [List.foldr_nil]
      exact join_le le_rfl (red.nothing_le _)
  | cons p l ih =>
      simp only [List.foldr_cons]
      rw [← a, c base (ind.proc p.2), a]
      exact join_mono_right ih

/-- Every instantiated hole's footprint is bounded by the fold over all of them. -/
private theorem proc_le_toList (ind : InductiveFunctionGettersSetters T) [red : ReducibleGettersSetters ind] :
    letI pre := @red.preorder
    ∀ {holes sig} (n : HoleIndex holes sig) (args : holes.Instantiation),
      ind.proc (args n)
        ≤ args.toList.foldr (fun p acc => ind.join (ind.proc p.2) acc) (ind.nothing : T State)
  | _, _, .zero, args => by
      letI := @red.preorder
      simp only [HoleSigs.Instantiation.toList, List.foldr_cons]; exact red.le_join_left _ _
  | _, _, .succ n', args => by
      letI := @red.preorder
      simp only [HoleSigs.Instantiation.toList, List.foldr_cons]
      exact le_trans (proc_le_toList ind n' (fun idx => args idx.succ)) (le_join_right _ _)

/-- Instantiating a statement only adds the (transferred) footprints of the procedures
plugged into its holes. -/
private theorem stmt_instantiate_le (ind : InductiveFunctionGettersSetters T) [red : ReducibleGettersSetters ind] {holes l} (stmt : StmtWithHoles holes l)
    (args : holes.Instantiation) :
    letI pre := @red.preorder
    ind.stmt (stmt.instantiate args)
      ≤ ind.join (ind.stmt stmt)
        (ind.extend ProcedureState.globalL
            (args.toList.foldr (fun p acc => ind.join (ind.proc p.2) acc) (ind.nothing : T State))) := by
  letI := @red.preorder
  revert args
  induction stmt with
  | skip =>
      intro args
      simp only [StmtWithHoles.instantiate, InductiveFunctionGettersSetters.stmt]
      exact red.le_join_left _ _
  | sample x e =>
      intro args
      simp only [StmtWithHoles.instantiate, InductiveFunctionGettersSetters.stmt]
      exact red.le_join_left _ _
  | call' x ls b r p _ =>
      intro args
      simp only [StmtWithHoles.instantiate, InductiveFunctionGettersSetters.stmt]
      exact red.le_join_left _ _
  | hole n x p =>
      intro args
      have hmem := proc_le_toList ind n args
      simp only [InductiveFunctionGettersSetters.proc] at hmem
      have hb : ind.reduce ProcedureState.globalL (ind.stmt (args n).body)
          ≤ args.toList.foldr (fun p acc => ind.join (ind.proc p.2) acc) (ind.nothing : T State) :=
        le_trans (red.le_join_left _ _) hmem
      have hr : ind.reduce ProcedureState.globalL (ind.getter (args n).return_val)
          ≤ args.toList.foldr (fun p acc => ind.join (ind.proc p.2) acc) (ind.nothing : T State) :=
        le_trans (le_join_right _ _) hmem
      simp only [StmtWithHoles.instantiate, StmtWithHoles.call,
        InductiveFunctionGettersSetters.stmt, InductiveFunctionGettersSetters.transfer]
      refine join_le ?_ (join_le ?_ (join_le ?_ ?_))
      · exact le_join_of_le_left (red.le_join_left _ _)
      · exact le_join_of_le_right (red.extend_mono _ hb)
      · exact le_join_of_le_right (red.extend_mono _ hr)
      · exact le_join_of_le_left (le_join_right _ _)
  | seq s1 s2 ih1 ih2 =>
      intro args
      simp only [StmtWithHoles.instantiate, InductiveFunctionGettersSetters.stmt]
      exact le_trans (join_mono (ih1 args) (ih2 args)) (join_join_le _ _ _)
  | ifThenElse c t e iht ihe =>
      intro args
      simp only [StmtWithHoles.instantiate, InductiveFunctionGettersSetters.stmt]
      refine join_le ?_ (join_le ?_ ?_)
      · exact le_join_of_le_left (red.le_join_left _ _)
      · exact le_trans (iht args) (join_mono (le_join_of_le_right (red.le_join_left _ _)) le_rfl)
      · exact le_trans (ihe args) (join_mono (le_join_of_le_right (le_join_right _ _)) le_rfl)
  | «while» c t iht =>
      intro args
      simp only [StmtWithHoles.instantiate, InductiveFunctionGettersSetters.stmt]
      refine join_le ?_ ?_
      · exact le_join_of_le_left (red.le_join_left _ _)
      · exact le_trans (iht args) (join_mono (le_join_right _ _) le_rfl)

private theorem proc_instantiate (ind : InductiveFunctionGettersSetters T) [red : ReducibleGettersSetters ind] {holes sig} (proc : ProcedureWithHoles holes sig) args :
  letI pre := @red.preorder
  ind.proc (proc.instantiate args) ≤
    List.foldr (fun p acc ↦ ind.join (ind.proc p.snd) acc)
      (ind.proc proc) args.toList := by
  letI := @red.preorder
  have key2 :
      ind.reduce ProcedureState.globalL (ind.stmt (proc.body.instantiate args))
        ≤ ind.join (ind.reduce ProcedureState.globalL (ind.stmt proc.body))
            (args.toList.foldr (fun p acc => ind.join (ind.proc p.2) acc) (ind.nothing : T State)) := by
    refine le_trans (red.reduce_mono _ (stmt_instantiate_le ind proc.body args)) ?_
    exact le_trans (red.reduce_join _) (join_mono_right (red.extend_reduce _ _))
  refine le_trans ?_ (foldr_sup_base ind (ind.proc proc) args.toList)
  change ind.join (ind.reduce ProcedureState.globalL (ind.stmt (proc.body.instantiate args)))
        (ind.reduce ProcedureState.globalL (ind.getter proc.return_val))
      ≤ ind.join
          (ind.join (ind.reduce ProcedureState.globalL (ind.stmt proc.body))
            (ind.reduce ProcedureState.globalL (ind.getter proc.return_val)))
          (args.toList.foldr (fun p acc => ind.join (ind.proc p.2) acc) (ind.nothing : T State))
  refine join_le ?_ ?_
  · exact le_trans key2 (join_mono (red.le_join_left _ _) le_rfl)
  · exact le_join_of_le_left (le_join_right _ _)


def InductiveFunctionGettersSetters.inductiveFunction (ind : InductiveFunctionGettersSetters T) : InductiveFunction (T State) where
  nothing := ind.nothing
  join := ind.join
  proc (p : ProcedureWithHoles _ _) := ind.proc p

def InductiveFunctionGettersSetters.evalMexpr (ind : InductiveFunctionGettersSetters T) :
    ModuleExpression → T State := ind.inductiveFunction.evalMexpr

def InductiveFunctionGettersSetters.eval' (ind : InductiveFunctionGettersSetters T) :
    Module t → T State := ind.inductiveFunction.eval'

def InductiveFunctionGettersSetters.eval (ind : InductiveFunctionGettersSetters T) [IsModule M] :
    M → T State := ind.inductiveFunction.eval

instance {ind : InductiveFunctionGettersSetters T} [red: ReducibleGettersSetters ind] : Reducible ind.inductiveFunction where
  le := red.preorder.le
  le_refl := red.preorder.le_refl
  le_trans := red.preorder.le_trans
  comm := red.comm.comm
  assoc := red.assoc.assoc
  join_mono_left := red.join_mono_left
  join_mono_right := join_mono_right
  le_join_left := red.le_join_left
  le_join_right := le_join_right
  join_idem := red.join_idem
  delta_bound := by apply proc_instantiate


end GaudisCrypt
