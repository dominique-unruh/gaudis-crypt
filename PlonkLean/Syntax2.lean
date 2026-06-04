import Mathlib.Data.List.AList
import Mathlib.Data.List.AList
-- import PlonkLean.Syntax
-- import Init.Data.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import PlonkLean.Syntax
import Metatheory.STLCext.Normalization

inductive MTy where
  | proc   : ProcedureSignature → MTy
  | prod : MTy → MTy → MTy
  | arr    : MTy → MTy → MTy

inductive MCtx where
  | empty  : MCtx
  | append : MCtx → MTy → MCtx

inductive Ref : MCtx → MTy → Type _ where
  | zero {a} {Γ : MCtx} : Ref (Γ.append a) a
  | succ {a b} : Ref Γ a → Ref (Γ.append b) a

def Ref.toNat : Ref Γ T → Nat
| .zero => 0
| .succ n => Nat.succ (n.toNat)

inductive MExpr' [ProgramSpec] : MCtx → MTy → Type _ where
  | const {sig} : Procedure sig → MExpr' Δ (.proc sig)
  | var  : Ref Δ M → MExpr' Δ M
  | app  : MExpr' Δ (.arr A B) → MExpr' Δ A → MExpr' Δ B
  | fst : MExpr' Δ (.prod A B) → MExpr' Δ A
  | snd : MExpr' Δ (.prod A B) → MExpr' Δ B
  | abs : MExpr' (Δ.append A) B → MExpr' Δ (MTy.arr A B)
  | pair : MExpr' Δ A → MExpr' Δ B → MExpr' Δ (MTy.prod A B)

def MExpr [ProgramSpec] : MTy → Type _ := MExpr' .empty

mutual
  /-- Beta-normal form: no beta-redex anywhere in the term. -/
  inductive Normal [ProgramSpec] : MExpr' Δ T → Prop where
    | neutral : Neutral e → Normal e
    | abs     {body : MExpr' (MCtx.append Δ A) B} : Normal body → Normal (.abs body)
    | pair    {a : MExpr' Δ A} {b : MExpr' Δ B} : Normal a → Normal b → Normal (.pair a b)
    | const   : Normal (.const p)

  /-- Neutral form: head is a variable; no outermost redex.
      `Neutral f` in `app` rules out `app (abs ..) ..`.
      `Neutral e` in `fst`/`snd` rules out `fst (pair ..)` / `snd (pair ..)`. -/
  inductive Neutral [ProgramSpec] : MExpr' Δ T → Prop where
    | var : Neutral (.var r)
    | app {f : MExpr' Δ (.arr A B)} {arg : MExpr' Δ A} :
        Neutral f → Normal arg → Neutral (.app f arg)
    | fst : Neutral e → Neutral (.fst e)
    | snd : Neutral e → Neutral (.snd e)
end

private def decidableNormalNeutral [ProgramSpec] (m : MExpr' Δ t) :
    Decidable (Normal m) × Decidable (Neutral m) :=
  match m with
  | .var _  => ⟨.isTrue (.neutral .var), .isTrue .var⟩
  | .const _ => ⟨.isTrue .const, .isFalse fun h => nomatch h⟩
  | .abs body =>
      match (decidableNormalNeutral body).1 with
      | .isTrue hn   => ⟨.isTrue (.abs hn), .isFalse fun h => nomatch h⟩
      | .isFalse hnn =>
          ⟨.isFalse fun h => hnn (match h with | .abs hb => hb | .neutral ne => nomatch ne),
           .isFalse fun h => nomatch h⟩
  | .pair a b =>
      match (decidableNormalNeutral a).1, (decidableNormalNeutral b).1 with
      | .isTrue ha, .isTrue hb =>
          ⟨.isTrue (.pair ha hb), .isFalse fun h => nomatch h⟩
      | .isFalse ha, _ =>
          ⟨.isFalse fun h => ha (match h with | .pair hp _ => hp | .neutral ne => nomatch ne),
           .isFalse fun h => nomatch h⟩
      | .isTrue _, .isFalse hb =>
          ⟨.isFalse fun h => hb (match h with | .pair _ hq => hq | .neutral ne => nomatch ne),
           .isFalse fun h => nomatch h⟩
  | .app f arg =>
      match (decidableNormalNeutral f).2, (decidableNormalNeutral arg).1 with
      | .isTrue nf, .isTrue na =>
          ⟨.isTrue (.neutral (.app nf na)), .isTrue (.app nf na)⟩
      | .isFalse nf, _ =>
          ⟨.isFalse fun h => nf (match h with | .neutral (.app ne _) => ne),
           .isFalse fun h => nf (match h with | .app ne _ => ne)⟩
      | .isTrue _, .isFalse na =>
          ⟨.isFalse fun h => na (match h with | .neutral (.app _ na') => na'),
           .isFalse fun h => na (match h with | .app _ na' => na')⟩
  | .fst e =>
      match (decidableNormalNeutral e).2 with
      | .isTrue hn   => ⟨.isTrue (.neutral (.fst hn)), .isTrue (.fst hn)⟩
      | .isFalse hnn =>
          ⟨.isFalse fun h => hnn (match h with | .neutral (.fst he) => he),
           .isFalse fun h => hnn (match h with | .fst he => he)⟩
  | .snd e =>
      match (decidableNormalNeutral e).2 with
      | .isTrue hn   => ⟨.isTrue (.neutral (.snd hn)), .isTrue (.snd hn)⟩
      | .isFalse hnn =>
          ⟨.isFalse fun h => hnn (match h with | .neutral (.snd he) => he),
           .isFalse fun h => hnn (match h with | .snd he => he)⟩

instance [ProgramSpec] (m : MExpr' Γ A) : Decidable (Normal m) := (decidableNormalNeutral m).1
instance [ProgramSpec] (m : MExpr' Γ A) : Decidable (Neutral m) := (decidableNormalNeutral m).2

/-- Beta-normal form for closed terms (empty context).
    Neutral terms cannot occur (they would require a variable in the empty context),
    so this has fewer cases than `Normal`. The `abs` body is in a one-variable context
    and therefore still uses the general `Normal`. -/
inductive NormalClosed [ProgramSpec] : MExpr' .empty T → Prop where
  | const : NormalClosed (.const p)
  | abs   {body : MExpr' (MCtx.append .empty A) B} : Normal body → NormalClosed (.abs body)
  | pair  {a : MExpr' .empty A} {b : MExpr' .empty B} :
      NormalClosed a → NormalClosed b → NormalClosed (.pair a b)

lemma not_neutral_empty [ProgramSpec] {T : MTy} : {m : MExpr' .empty T} → ¬ Neutral m
  | .var r,   _       => nomatch r
  | .app _ _, .app nf _ => not_neutral_empty nf
  | .fst _,   .fst ne   => not_neutral_empty ne
  | .snd _,   .snd ne   => not_neutral_empty ne

/-- Extends a renaming `ρ : Ref Δ → Ref Γ` to work under one binder of type `A`.
    The bound variable `.zero` maps to itself; outer variables `.succ r` are renamed by `ρ`
    and re-wrapped with `.succ`.  This is the typed analogue of incrementing the cutoff `c`
    in Pierce's shift operation. -/
private def liftRename {Δ Γ : MCtx} {A : MTy}
    (ρ : ∀ {T}, Ref Δ T → Ref Γ T) {T} : Ref (MCtx.append Δ A) T → Ref (MCtx.append Γ A) T
  | .zero   => .zero
  | .succ r => .succ (ρ r)

/-- Applies a renaming `ρ : Ref Δ → Ref Γ` to every variable in a term, producing a term
    over context `Γ`.  Goes under binders by lifting `ρ` with `liftRename`.
    This is the typed analogue of Pierce's shift `↑_c^d`, where `ρ` encodes both the
    cutoff `c` and the displacement `d`. -/
private def MExpr'.rename [ProgramSpec] (ρ : ∀ {T}, Ref Δ T → Ref Γ T) : MExpr' Δ T → MExpr' Γ T
  | .const p  => .const p
  | .var r    => .var (ρ r)
  | .app f a  => .app (f.rename ρ) (a.rename ρ)
  | .fst e    => .fst (e.rename ρ)
  | .snd e    => .snd (e.rename ρ)
  | .abs body => .abs (body.rename (liftRename ρ))
  | .pair a b => .pair (a.rename ρ) (b.rename ρ)

/-- Extends a simultaneous substitution `σ : Ref Δ → MExpr' Γ` to work under one binder
    of type `A`, yielding a substitution `Ref (Δ,A) → MExpr' (Γ,A)`.
    The bound variable `.zero` maps to the fresh variable `.var .zero`;
    outer variables `.succ r` are substituted by `σ r` and then weakened into the
    extended context `Γ,A` by renaming with `.succ`. -/
private def liftSubst [ProgramSpec] {Δ Γ : MCtx} {A : MTy}
    (σ : ∀ {T}, Ref Δ T → MExpr' Γ T) {T} : Ref (MCtx.append Δ A) T → MExpr' (MCtx.append Γ A) T
  | .zero   => .var .zero
  | .succ r => (σ r).rename (fun {_} r => .succ r)

/-- Applies a simultaneous substitution `σ : Ref Δ → MExpr' Γ` to every variable in a
    term, producing a term over context `Γ`.  Goes under binders by lifting `σ` with
    `liftSubst`. -/
private def substGen [ProgramSpec] (σ : ∀ {T}, Ref Δ T → MExpr' Γ T) : MExpr' Δ T → MExpr' Γ T
  | .const p  => .const p
  | .var r    => σ r
  | .app f a  => .app (substGen σ f) (substGen σ a)
  | .fst e    => .fst (substGen σ e)
  | .snd e    => .snd (substGen σ e)
  | .abs body => .abs (substGen (liftSubst σ) body)
  | .pair a b => .pair (substGen σ a) (substGen σ b)

/-- The single-variable substitution map used as the `σ` argument to `substGen`:
    de Bruijn index 0 (the outermost bound variable) maps to `arg`;
    any other index `k+1` maps back to the variable at index `k`. -/
private def substVar [ProgramSpec] {Δ : MCtx} {u : MTy} (arg : MExpr' Δ u) {T} :
    Ref (MCtx.append Δ u) T → MExpr' Δ T
  | .zero   => arg
  | .succ r => .var r

/-- Single-variable de Bruijn substitution: replaces de Bruijn index 0 in `body` with `arg`.
    Implemented via `substGen` with the point substitution `substVar arg`. -/
def subst [ProgramSpec] (body : MExpr' (Δ.append u) t) (arg : MExpr' Δ u) : MExpr' Δ t :=
  substGen (substVar arg) body

instance mexprSTLCspec [ProgramSpec] : Metatheory.STLCext.STLCspec where
  baseTypes := ProcedureSignature
  baseTypeValue := Procedure

def mtyToSTLC [ProgramSpec] : MTy → Metatheory.STLCext.Ty
| .prod A B => .prod (mtyToSTLC A) (mtyToSTLC B)
| .arr A B => .arr (mtyToSTLC A) (mtyToSTLC B)
| .proc sig => .base sig

def mexprToSTLC [ProgramSpec] : MExpr' Γ T → @Metatheory.STLCext.Term mexprSTLCspec
  | .const p => .value p
  | .var n => .var n.toNat
  | .app M N => .app (mexprToSTLC M) (mexprToSTLC N)
  | .fst M => .fst (mexprToSTLC M)
  | .snd M => .snd  (mexprToSTLC M)
  | .abs M => .lam (mexprToSTLC M)
  | .pair M N => .pair (mexprToSTLC M) (mexprToSTLC N)

def mctxtToSTLC [ProgramSpec] : MCtx → Metatheory.STLCext.Context
| .empty => []
| .append Γ T => mtyToSTLC T :: mctxtToSTLC Γ

theorem mexprToSTLCtype [ProgramSpec] (m : MExpr' Γ T) :
  Metatheory.STLCext.HasType (mctxtToSTLC Γ) (mexprToSTLC m) (mtyToSTLC T) := by induction m with
  | const c =>
    simp only [mexprToSTLC, mtyToSTLC]
    exact Metatheory.STLCext.HasType.value c
  | abs M ihM =>
    simp only [mexprToSTLC, mtyToSTLC, mctxtToSTLC] at *
    exact Metatheory.STLCext.HasType.lam ihM
  | pair M N ihM ihN =>
    simp only [mexprToSTLC, mtyToSTLC]
    exact Metatheory.STLCext.HasType.pair ihM ihN
  | app M N ihM ihN =>
    simp only [mexprToSTLC]
    exact Metatheory.STLCext.HasType.app ihM ihN
  | fst M ihM =>
    simp only [mexprToSTLC]
    exact Metatheory.STLCext.HasType.fst ihM
  | snd M ihM =>
    simp only [mexprToSTLC]
    exact Metatheory.STLCext.HasType.snd ihM
  | var n =>
    simp only [mexprToSTLC]
    apply Metatheory.STLCext.HasType.var
    induction n with
    | zero =>
      simp [Ref.toNat, mctxtToSTLC]
    | succ n ih =>
      simp [Ref.toNat, mctxtToSTLC, ih]

-- def destruct_pair [ProgramSpec] (m : MExpr' Δ (.prod T U)) :
  -- PSum (MExpr' Δ T × MExpr' Δ U) (¬ ∃ m1 m2, m = .pair m1 m2) :=
  -- match h: m with
   -- | .pair m1 m2 => .inl (m1,m2)
   -- | .fst _ => .inr (by grind only)
   -- | .snd _ => .inr (by grind only)
   -- | .app _ _ => .inr (by grind only)
   -- | .var _ => .inr (by grind only)

def is_pair [ProgramSpec] (m : MExpr' Δ (.prod T U)) : Prop :=
  match h : m with | .pair _ _ => true | _ => false

instance [ProgramSpec] (m : MExpr' Δ (.prod T U)) : Decidable (is_pair m) :=
  match m with
  | .pair _ _ => isTrue rfl
  | .var _ | .app _ _ | .fst _ | .snd _ => isFalse Bool.false_ne_true

-- def destruct_pair' [ProgramSpec] (m : MExpr' Δ (.prod T U)) (h : is_pair m) : (MExpr' Δ T × MExpr' Δ U) :=
  -- match m with
   -- | .pair m1 m2 => (m1,m2)
   -- | .fst _ => False.elim (by simp [is_pair] at *)
   -- | .snd _ => False.elim (by simp [is_pair] at *)
   -- | .app _ _ => False.elim (by simp [is_pair] at *)
   -- | .var _ => False.elim (by simp [is_pair] at *)

def is_pair.split[ProgramSpec] {m : MExpr' Δ (.prod T U)} (_: is_pair m) : (MExpr' Δ T × MExpr' Δ U) :=
  match m with
   | .pair m1 m2 => (m1,m2)
   | .fst _ => False.elim (by simp [is_pair] at *)
   | .snd _ => False.elim (by simp [is_pair] at *)
   | .app _ _ => False.elim (by simp [is_pair] at *)
   | .var _ => False.elim (by simp [is_pair] at *)

def is_pair.fst [ProgramSpec] {m : MExpr' Δ (.prod T U)} (h: is_pair m) : MExpr' Δ T :=
  h.split.1
def is_pair.snd [ProgramSpec] {m : MExpr' Δ (.prod T U)} (h: is_pair m) : MExpr' Δ U :=
  h.split.2

def is_app [ProgramSpec] (m : MExpr' Δ T) : Prop :=
  match h : m with | .app _ _ => true | _ => false

instance [ProgramSpec] (m : MExpr' Δ (.prod T U)) : Decidable (is_app m) :=
  match m with
  | .app _ _ => isTrue rfl
  | .var _ | .pair _ _ | .fst _ | .snd _ => isFalse Bool.false_ne_true

def is_app.split [ProgramSpec] {m : MExpr' Δ T} (_: is_app m) :
    Σ A, MExpr' Δ (.arr A T) × MExpr' Δ A :=
  match m with
   | .app f arg => ⟨_, f, arg⟩
   | .fst _ => False.elim (by simp [is_app] at *)
   | .snd _ => False.elim (by simp [is_app] at *)
   | .pair _ _ => False.elim (by simp [is_app] at *)
   | .var _ => False.elim (by simp [is_app] at *)

def is_app.hd [ProgramSpec] {m : MExpr' Δ T} (h : is_app m) : Σ A, MExpr' Δ (.arr A T) :=
  ⟨h.split.1, h.split.2.1⟩
def is_app.arg [ProgramSpec] {m : MExpr' Δ T} (h : is_app m) : Σ A, MExpr' Δ A :=
  ⟨h.split.1, h.split.2.2⟩


def is_abs [ProgramSpec] (m : MExpr' Δ T) : Prop :=
  match h : m with | .abs _ => true | _ => false

instance [ProgramSpec] (m : MExpr' Δ T) : Decidable (is_abs m) :=
  match m with
  | .abs _ => isTrue rfl
  | .var _ | .pair _ _ | .fst _ | .snd _ | .app _ _ | .const _ => isFalse Bool.false_ne_true

def is_abs.body [ProgramSpec] {m : MExpr' Δ (.arr T U)} (_: is_abs m) :
    MExpr' (Δ.append T) U :=
  match m with
   | .abs body => body
   | .fst _ => False.elim (by simp [is_abs] at *)
   | .snd _ => False.elim (by simp [is_abs] at *)
   | .var _ => False.elim (by simp [is_abs] at *)
   | .app _ _ => False.elim (by simp [is_abs] at *)


def reduction_step [ProgramSpec] (m : MExpr' Δ t) (nn : ¬ Normal m) : MExpr' Δ t :=
  match m with
  | .app hd arg =>
      if abs : is_abs hd then
        subst abs.body arg
      else
        if nn_hd : ¬ Normal hd then
          .app (reduction_step hd nn_hd) arg
        else
          have nn_arg : ¬ Normal arg := fun ha => nn (.neutral (.app (match not_not.mp nn_hd with | .neutral ne => ne | .abs _ => absurd rfl abs) ha))
          .app hd (reduction_step arg nn_arg)
  | .const p => absurd .const nn
  | .abs body =>
      have nn' : ¬ Normal body := sorry
      .abs (reduction_step body nn')
  | .pair m1 m2 =>
      if nn1: ¬ Normal m1 then
        .pair (reduction_step m1 nn1) m2
      else
        have nn2 : ¬ Normal m2 := sorry
        .pair m1 (reduction_step m2 nn2)
  | .fst m' =>
      if pair: is_pair m' then
        pair.fst
      else
        have nn' : ¬ Normal m' := fun hn => match hn with
          | .neutral ne => nn (.neutral (.fst ne))
          | .pair _ _ => False.elim (by simp [is_pair] at *)
        .fst (reduction_step m' nn')
  | .snd m' =>
      if pair: is_pair m' then
        pair.snd
      else
        have nn' : ¬ Normal m' := fun hn => match hn with
          | .neutral ne => nn (.neutral (.snd ne))
          | .pair _ _ => False.elim (by simp [is_pair] at *)
        .snd (reduction_step m' nn')
  | .var n => absurd (.neutral .var) nn


theorem reduction_step_compat [ProgramSpec] (m : MExpr' Γ T) (nn : ¬ Normal m) :
  Metatheory.STLCext.Step (mexprToSTLC m) (mexprToSTLC (reduction_step m nn)) := by
    cases m
    case const =>
      sorry -- can't happen
    case var =>
      sorry -- can't happen
    case app hd arg =>
      sorry
    case fst m' =>
      sorry
    case snd m' =>
      sorry
    case abs body =>
      sorry
    case pair m1 m2 =>
      sorry

def reduce [ProgramSpec] (m : MExpr' Γ T) : MExpr' Γ T :=
    if h : Normal m then m
    else
      reduce (reduction_step m h)
termination_by false -- TODO Put something suitable here
decreasing_by sorry

theorem reduce_induction [ProgramSpec] {P : MExpr' Γ T → Prop}
    (step : ∀ m, P m → ∀ (nn : ¬ Normal m), P (reduction_step m nn)) :
  ∀ m, P m := sorry

theorem reduceNormal [ProgramSpec] (m : MExpr' Δ t) : Normal (reduce m) := sorry

private lemma Normal.toNormalClosed [ProgramSpec] {T : MTy} {m : MExpr' .empty T} :
    Normal m → NormalClosed m
  | .neutral h  => absurd h not_neutral_empty
  | .const      => .const
  | .abs hb     => .abs hb
  | .pair ha hb => .pair ha.toNormalClosed hb.toNormalClosed


theorem reduceNormalClosed [ProgramSpec] (m : MExpr t) : NormalClosed (reduce m) :=
  (reduceNormal m).toNormalClosed

-- class MtyToType (s : Type) (mty : MTy) (userType : outParam Type)

def mtyToType [ProgramSpec] (mty : MTy) := match mty with
  | .proc sig => Procedure sig
  | .arr a b => mtyToType a -> mtyToType b
  | .prod a b => mtyToType a × mtyToType b

def mctxToType [ProgramSpec] (mctx : MCtx) : Type _ := match mctx with
  | MCtx.empty => PUnit
  | MCtx.append mctx' mty => mctxToType mctx' × mtyToType mty

def mctxToType' [ProgramSpec] (mctx : MCtx) : Type _ := match mctx with
  | MCtx.empty => PUnit
  | MCtx.append mctx' mty => mctxToType mctx' × MExpr' mctx' mty

def evalModule' [ProgramSpec] {mctx : MCtx} {mty : MTy} (mex : MExpr' mctx mty) :
      mctxToType mctx -> mtyToType mty :=
  match mex with
  | .const (sig:=sig) (p : Procedure sig) => fun _ => p
  | .var .zero => fun (_, x) => x
  | .var (.succ n) => fun (mctx', _) => evalModule' (.var n) mctx'
  | .app a b => fun ctx => (evalModule' a ctx) (evalModule' b ctx)
  | .fst a => fun ctx => (evalModule' a ctx).1
  | .snd a => fun ctx => (evalModule' a ctx).2
  | .abs body => fun ctx => fun x => (evalModule' body (ctx, x))
  | .pair a b => fun ctx => (evalModule' a ctx, evalModule' b ctx)

def moduleEqual [ProgramSpec] (a : MExpr' Δ t) b := reduce a = reduce b

@[simp]
theorem reduce_fst [ProgramSpec] (m : MExpr' Γ T) (m' : MExpr' Γ T') :
  reduce (MExpr'.fst (MExpr'.pair m m')) = reduce m := sorry

section Demo

variable [ProgramSpec]

axiom sig : ProcedureSignature
def TestModuleType := MExpr (MTy.prod (MTy.proc sig) (MTy.proc sig))

noncomputable
def TestModuleType.main (m : TestModuleType) : MExpr (MTy.proc sig) := m.fst
noncomputable
def TestModuleType.aux (m : TestModuleType) : MExpr (MTy.proc sig) := m.snd

structure TestModuleTypeStruct where
  main : MExpr (MTy.proc sig)
  aux : MExpr (MTy.proc sig)

noncomputable
def TestModuleType.mk (str : TestModuleTypeStruct) : TestModuleType := str.main.pair str.aux

axiom testMain : MExpr (MTy.proc sig)
axiom testAux : MExpr (MTy.proc sig)

noncomputable
def myMod := TestModuleType.mk {main := testMain, aux := testAux}

-- theorem reduceFstPair {ctx mtya mtyb} (a : MExpr' ctx mtya) (b : MExpr' ctx mtyb) :
  -- reduce (MExpr'.pair a b).fst = reduce a := rfl

theorem test : moduleEqual myMod.main testMain := by
  simp [moduleEqual, TestModuleType.main, myMod, TestModuleType.mk]

end Demo

def evalModule [ProgramSpec.{0}] {mty} (mex : MExpr mty) : mtyToType mty := evalModule'.{0,0} mex PUnit.unit

def MProc [ProgramSpec] sig := MExpr (.proc sig)

def evalProc2 [ProgramSpec] {sig} (mex : MProc sig) : Procedure sig := evalModule mex

opaque FV : Type
-- Placeholder
def fv_proc [ProgramSpec] {sig} (proc : Procedure sig) : Set FV := sorry

def fv' [ProgramSpec] {mctx : MCtx} {mty : MTy} (mex : MExpr' mctx mty) : Set FV :=
  match mex with
    | .const p => fv_proc p
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
theorem fv'_app [ProgramSpec] (a : MExpr' Γ (MTy.arr A B)) (b : MExpr' Γ A) :
  fv' (MExpr'.app a b) = fv' a ∪ fv' b := sorry

def fv [ProgramSpec] (m : MExpr' c t) : Set FV := fv' (reduce m)

theorem fv_reduction_step [ProgramSpec] (m : MExpr' c t) (nn : ¬ Normal m) :
  fv' (reduction_step m nn) ⊆ fv' m := sorry

theorem fv_reduce [ProgramSpec] (m : MExpr' c t) : fv m ⊆ fv' m := by
  unfold fv
  induction reduce m using reduce_induction with
  | step m' ih nn => calc
    fv' (reduction_step m' nn) ⊆ fv' m' := fv_reduction_step _ _
    _ ⊆ fv' m := ih

theorem fv_app [ProgramSpec] (a : MExpr' Γ (MTy.arr A B)) (b : MExpr' Γ A) :
    fv (MExpr'.app a b) ⊆ fv' a ∪ fv' b := by
  simp only [fv, ← fv'_app]
  apply fv_reduce

/-

#eval fv(mymodule) = {a,b,c}
Have: fv(mymodule p) <= fv(mymodule) + fv(p)

def mymodule : proc1 to proc2 x proc3 := MakeModule (fun p1:proc1 =>
  ( {{ call proc1; call proc1 }},
    {{ call proc1 }} )

struct modtype where
  proc1 : procedure
  proc2 : procedure

def mymodule : proc1 to modtype := MakeModule (fun p1:proc1 =>
  { proc1 := {{ call proc1; call proc1 }},
    proc2 := {{ call proc1 }} }



-/