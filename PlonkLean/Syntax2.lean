import Mathlib.Data.List.AList
-- import PlonkLean.Syntax
-- import Init.Data.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import PlonkLean.Syntax

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

inductive MExpr' s : MCtx → MTy → Type _ where
  | const {sig} : Procedure s sig → MExpr' s Δ (.proc sig)
  | var  : Ref Δ M → MExpr' s Δ M
  | app  : MExpr' s Δ (.arr A B) → MExpr' s Δ A → MExpr' s Δ B
  | fst : MExpr' s Δ (.prod A B) → MExpr' s Δ A
  | snd : MExpr' s Δ (.prod A B) → MExpr' s Δ B
  | abs : MExpr' s (Δ.append A) B → MExpr' s Δ (MTy.arr A B)
  | pair : MExpr' s Δ A → MExpr' s Δ B → MExpr' s Δ (MTy.prod A B)

def MExpr (s : Type) : MTy → Type _ := MExpr' s .empty

mutual
  /-- Beta-normal form: no beta-redex anywhere in the term. -/
  inductive Normal {s : Type} : MExpr' s Δ T → Prop where
    | neutral : Neutral e → Normal e
    | abs     {body : MExpr' s (MCtx.append Δ A) B} : Normal body → Normal (.abs body)
    | pair    {a : MExpr' s Δ A} {b : MExpr' s Δ B} : Normal a → Normal b → Normal (.pair a b)
    | const   : Normal (.const p)

  /-- Neutral form: head is a variable; no outermost redex.
      `Neutral f` in `app` rules out `app (abs ..) ..`.
      `Neutral e` in `fst`/`snd` rules out `fst (pair ..)` / `snd (pair ..)`. -/
  inductive Neutral {s : Type} : MExpr' s Δ T → Prop where
    | var : Neutral (.var r)
    | app {f : MExpr' s Δ (.arr A B)} {arg : MExpr' s Δ A} :
        Neutral f → Normal arg → Neutral (.app f arg)
    | fst : Neutral e → Neutral (.fst e)
    | snd : Neutral e → Neutral (.snd e)
end



/-- Beta-normal form for closed terms (empty context).
    Neutral terms cannot occur (they would require a variable in the empty context),
    so this has fewer cases than `Normal`. The `abs` body is in a one-variable context
    and therefore still uses the general `Normal`. -/
inductive NormalClosed {s : Type} : MExpr' s .empty T → Prop where
  | const : NormalClosed (.const p)
  | abs   {body : MExpr' s (MCtx.append .empty A) B} : Normal body → NormalClosed (.abs body)
  | pair  {a : MExpr' s .empty A} {b : MExpr' s .empty B} :
      NormalClosed a → NormalClosed b → NormalClosed (.pair a b)

lemma not_neutral_empty {s : Type} {T : MTy} : {m : MExpr' s .empty T} → ¬ Neutral m
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
private def MExpr'.rename (ρ : ∀ {T}, Ref Δ T → Ref Γ T) : MExpr' s Δ T → MExpr' s Γ T
  | .const p  => .const p
  | .var r    => .var (ρ r)
  | .app f a  => .app (f.rename ρ) (a.rename ρ)
  | .fst e    => .fst (e.rename ρ)
  | .snd e    => .snd (e.rename ρ)
  | .abs body => .abs (body.rename (liftRename ρ))
  | .pair a b => .pair (a.rename ρ) (b.rename ρ)

/-- Extends a simultaneous substitution `σ : Ref Δ → MExpr' s Γ` to work under one binder
    of type `A`, yielding a substitution `Ref (Δ,A) → MExpr' s (Γ,A)`.
    The bound variable `.zero` maps to the fresh variable `.var .zero`;
    outer variables `.succ r` are substituted by `σ r` and then weakened into the
    extended context `Γ,A` by renaming with `.succ`. -/
private def liftSubst {s : Type} {Δ Γ : MCtx} {A : MTy}
    (σ : ∀ {T}, Ref Δ T → MExpr' s Γ T) {T} : Ref (MCtx.append Δ A) T → MExpr' s (MCtx.append Γ A) T
  | .zero   => .var .zero
  | .succ r => (σ r).rename (fun {_} r => .succ r)

/-- Applies a simultaneous substitution `σ : Ref Δ → MExpr' s Γ` to every variable in a
    term, producing a term over context `Γ`.  Goes under binders by lifting `σ` with
    `liftSubst`. -/
private def substGen (σ : ∀ {T}, Ref Δ T → MExpr' s Γ T) : MExpr' s Δ T → MExpr' s Γ T
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
private def substVar {s : Type} {Δ : MCtx} {u : MTy} (arg : MExpr' s Δ u) {T} :
    Ref (MCtx.append Δ u) T → MExpr' s Δ T
  | .zero   => arg
  | .succ r => .var r

/-- Single-variable de Bruijn substitution: replaces de Bruijn index 0 in `body` with `arg`.
    Implemented via `substGen` with the point substitution `substVar arg`. -/
def subst (body : MExpr' s (Δ.append u) t) (arg : MExpr' s Δ u) : MExpr' s Δ t :=
  substGen (substVar arg) body

-- TODO Use some existing STLC library
def reduce (m : MExpr' s Δ t) : MExpr' s Δ t := match m with
  | .app a b =>
      let ra := reduce a
      let rb := reduce b
      match ra with
      | .abs a' => reduce (subst a' rb)
      | _       => .app ra rb
  | .var n    => .var n
  | .pair a b => .pair (reduce a) (reduce b)
  | .abs a    => .abs (reduce a)
  | .fst a    =>
      match reduce a with
      | .pair b _ => b
      | ra        => .fst ra
  | .snd a    =>
      match reduce a with
      | .pair _ c => c
      | ra        => .snd ra
  | .const p  => .const p
termination_by sizeOf m
decreasing_by all_goals sorry

-- TODO Use some existing STLC library
theorem reduceNormal (m : MExpr' s Δ t) : Normal (reduce m) := sorry

private lemma Normal.toNormalClosed {s : Type} {T : MTy} {m : MExpr' s .empty T} :
    Normal m → NormalClosed m
  | .neutral h  => absurd h not_neutral_empty
  | .const      => .const
  | .abs hb     => .abs hb
  | .pair ha hb => .pair ha.toNormalClosed hb.toNormalClosed


theorem reduceNormalClosed (m : MExpr s t) : NormalClosed (reduce m) :=
  (reduceNormal m).toNormalClosed

class MtyToType (s : Type) (mty : MTy) (userType : outParam Type)

def mtyToType (s : Type) (mty : MTy) := match mty with
  | .proc sig => Procedure s sig
  | .arr a b => mtyToType s a -> mtyToType s b
  | .prod a b => mtyToType s a × mtyToType s b

def mctxToType (s : Type) (mctx : MCtx) : Type _ := match mctx with
  | MCtx.empty => PUnit
  | MCtx.append mctx' mty => mctxToType s mctx' × mtyToType s mty

def mctxToType' (s : Type) (mctx : MCtx) : Type _ := match mctx with
  | MCtx.empty => PUnit
  | MCtx.append mctx' mty => mctxToType s mctx' × MExpr' s mctx' mty

def evalModule' {mctx : MCtx} {mty : MTy} (mex : MExpr' s mctx mty) :
      mctxToType s mctx -> mtyToType s mty :=
  match mex with
  | .const (sig:=sig) (p : Procedure s sig) => fun _ => p
  | .var .zero => fun (_, x) => x
  | .var (.succ n) => fun (mctx', _) => evalModule' (s:=s) (.var n) mctx'
  | .app a b => fun ctx => (evalModule' a ctx) (evalModule' b ctx)
  | .fst a => fun ctx => (evalModule' a ctx).1
  | .snd a => fun ctx => (evalModule' a ctx).2
  | .abs body => fun ctx => fun x => (evalModule' body (ctx, x))
  | .pair a b => fun ctx => (evalModule' a ctx, evalModule' b ctx)

axiom sig : ProcedureSignature
def TestModuleType s := MExpr s (MTy.prod (MTy.proc sig) (MTy.proc sig))

noncomputable
def TestModuleType.main (m : TestModuleType s) : MExpr s (MTy.proc sig) := m.fst
noncomputable
def TestModuleType.aux (m : TestModuleType s) : MExpr s (MTy.proc sig) := m.snd

structure TestModuleTypeStruct s where
  main : MExpr s (MTy.proc sig)
  aux : MExpr s (MTy.proc sig)

noncomputable
def TestModuleType.mk (str : TestModuleTypeStruct s) : TestModuleType s := str.main.pair str.aux

axiom testMain : MExpr s (MTy.proc sig)

axiom s : Type
noncomputable
def myMod := TestModuleType.mk (s:=s) {main := testMain, aux := sorry}

-- theorem reduceFstPair {ctx mtya mtyb} (a : MExpr' s ctx mtya) (b : MExpr' s ctx mtyb) :
  -- reduce (MExpr'.pair a b).fst = reduce a := rfl

def moduleEqual (a : MExpr' s Δ t) b := reduce a = reduce b

theorem test : moduleEqual myMod.main testMain := by
  simp only [moduleEqual, TestModuleType.main, myMod, TestModuleType.mk, reduce]

def evalModule {mty} (mex : MExpr s mty) : mtyToType s mty := evalModule'.{0} mex PUnit.unit

def MProc s sig := MExpr s (.proc sig)

def evalProc2 {sig} (mex : MProc s sig) : Procedure s sig := evalModule mex

opaque FV : Type
-- Placeholder
def fv_proc {sig} (proc : Procedure s sig) : Set FV := sorry

def fv' {mctx : MCtx} {mty : MTy} (mex : MExpr' s mctx mty) : Set FV :=
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
theorem fv'_app : fv' (MExpr'.app a b) = fv' a ∪ fv' b := by grind only

def beta_reduce {ctxt} {ty} (m : MExpr' s ctxt ty) : MExpr' s ctxt ty := sorry

def fv (m : MExpr' s c t) : Set FV := fv' (beta_reduce m)

theorem fv_reduce (m : MExpr' s c t) : fv' (beta_reduce m) ⊆ fv' m := sorry

theorem fv_app : fv (MExpr'.app a b) ⊆ fv' a ∪ fv' b := by
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