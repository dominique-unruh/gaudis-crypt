import Mathlib.Data.List.AList
-- import PlonkLean.Syntax
import Init.Data.Equiv.Basic

class TupleLike a (b : outParam Type) (c : outParam Type) where
  iso : a ≃ (b × c)

struct bla where
  x : Nat
  y : Nat
  z : Nat
derive TupleLike

instance : TupleLike bla Nat (Nat × Nat)

structure ProcSig where
  params : List Type
  ret    : Type

inductive MTy where
  | proc   : ProcSig → MTy
  | prod : MTy → MTy → MTy
  | arr    : MTy → MTy → MTy

inductive MCtx where
  | nil  : MCtx
  | snoc : MCtx → MTy → MCtx

inductive Ref : MCtx → MTy → Type _ where
  | here {a} : Ref (.snoc Γ a) a
  | there {a b} : Ref Γ a → Ref (.snoc Γ b) a

-- Placeholder
def procSigToType : ProcSig → Type := sorry

inductive MExpr' : MCtx → MTy → Type _ where
  | const {sig} : procSigToType sig → MExpr' Δ (.proc sig)
  | var  : Ref Δ M → MExpr' Δ M
  | app  : MExpr' Δ (.arr A B) → MExpr' Δ A → MExpr' Δ B
  | fst : MExpr' Δ (.prod A B) → MExpr' Δ A
  | snd : MExpr' Δ (.prod A B) → MExpr' Δ B
  | abs : MExpr' (Δ.snoc A) B → MExpr' Δ (MTy.arr A B)

def MExpr : MTy → Type _ := MExpr' .nil

def mtyToType (mty : MTy) := match mty with
  | .proc sig => procSigToType sig
  | .arr a b => mtyToType a -> mtyToType b
  | .prod a b => mtyToType a × mtyToType b

def mctxToType (mctx : MCtx) : Type _ := match mctx with
  | .nil => PUnit
  | .snoc mctx' mty => mctxToType mctx' × mtyToType mty

def mctxToType' (mctx : MCtx) : Type _ := match mctx with
  | .nil => PUnit
  | .snoc mctx' mty => mctxToType mctx' × MExpr' mctx' mty

def evalModule' {mctx : MCtx} {mty : MTy} (mex : MExpr' mctx mty) : mctxToType mctx -> mtyToType mty :=
  match mex with
  | .const p => fun _ => p
  | .var Ref.here => fun (_, x) => x
  | .var (Ref.there n) => fun (mctx', _) => evalModule' (.var n) mctx'
  | .app a b => fun ctx => (evalModule' a ctx) (evalModule' b ctx)
  | .fst a => fun ctx => (evalModule' a ctx).1
  | .snd a => fun ctx => (evalModule' a ctx).2
  | .abs body => fun ctx => fun x => (evalModule' body (ctx, x))

def fv {mctx : MCtx} {mty : MTy} (mex : MExpr' mctx mty) := Set String :=
  match mex with
    | .const p => sorry
    | .var Ref.here => Set.empty
    | .var (Ref.there n) => Set.empty
    | .app a b => fv a ∪ fv b
    | .fst a => fv a
    | .snd a => fv b
    | .abs body => fv body

def evalModule {mty} (mex : MExpr mty) : mtyToType mty := evalModule' mex ()

def evalProc {sig} (mex : MExpr (.proc sig)) : procSigToType sig := evalModule mex
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