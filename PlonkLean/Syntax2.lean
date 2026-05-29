import Mathlib.Data.List.AList
-- import PlonkLean.Syntax
-- import Init.Data.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import PlonkLean.Syntax

class TupleLike a (b : outParam Type) (c : outParam Type) where
  iso : a ≃ (b × c)

structure bla where
  x : Nat
  y : Nat
  z : Nat
  -- deriving TupleLike

instance : TupleLike bla Nat (Nat × Nat) := sorry

inductive MTy where
  | proc   : ProcedureSignature → MTy
  | prod : MTy → MTy → MTy
  | arr    : MTy → MTy → MTy

inductive MCtx where
  | nil  : MCtx
  | snoc : MCtx → MTy → MCtx

inductive Ref : MCtx → MTy → Type _ where
  | here {a} : Ref (.snoc Γ a) a
  | there {a b} : Ref Γ a → Ref (.snoc Γ b) a

inductive MExpr' s : MCtx → MTy → Type _ where
  | const {sig} : Procedure s sig → MExpr' s Δ (.proc sig)
  | var  : Ref Δ M → MExpr' s Δ M
  | app  : MExpr' s Δ (.arr A B) → MExpr' s Δ A → MExpr' s Δ B
  | fst : MExpr' s Δ (.prod A B) → MExpr' s Δ A
  | snd : MExpr' s Δ (.prod A B) → MExpr' s Δ B
  | abs : MExpr' s (Δ.snoc A) B → MExpr' s Δ (MTy.arr A B)

def MExpr (s : Type) : MTy → Type _ := MExpr' s .nil

def mtyToType (s : Type) (mty : MTy) := match mty with
  | .proc sig => Procedure s sig
  | .arr a b => mtyToType s a -> mtyToType s b
  | .prod a b => mtyToType s a × mtyToType s b

def mctxToType (s : Type) (mctx : MCtx) : Type _ := match mctx with
  | .nil => PUnit
  | .snoc mctx' mty => mctxToType s mctx' × mtyToType s mty

def mctxToType' (s : Type) (mctx : MCtx) : Type _ := match mctx with
  | .nil => PUnit
  | .snoc mctx' mty => mctxToType s mctx' × MExpr' s mctx' mty

def evalModule' {mctx : MCtx} {mty : MTy} (mex : MExpr' s mctx mty) :
      mctxToType s mctx -> mtyToType s mty :=
  match mex with
  | .const (sig:=sig) (p : Procedure s sig) => fun _ => p
  | .var Ref.here => fun (_, x) => x
  | .var (Ref.there n) => fun (mctx', _) => evalModule' (s:=s) (.var n) mctx'
  | .app a b => fun ctx => (evalModule' a ctx) (evalModule' b ctx)
  | .fst a => fun ctx => (evalModule' a ctx).1
  | .snd a => fun ctx => (evalModule' a ctx).2
  | .abs body => fun ctx => fun x => (evalModule' body (ctx, x))

def evalModule {mty} (mex : MExpr s mty) : mtyToType s mty := evalModule'.{0} mex PUnit.unit

def MProc s sig := MExpr s (.proc sig)

def evalProc {sig} (mex : MProc s sig) : Procedure s sig := evalModule mex

opaque FV : Type
-- Placeholder
def fv_proc {sig} (proc : Procedure s sig) : Set FV := sorry

def fv' {mctx : MCtx} {mty : MTy} (mex : MExpr' s mctx mty) : Set FV :=
  match mex with
    | .const p => fv_proc p
    | .var Ref.here => {}
    | .var (Ref.there n) => {}
    | .app a b => fv' a ∪ fv' b
    | .fst a => fv' a
    | .snd a => fv' a
    | .abs body => fv' body

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