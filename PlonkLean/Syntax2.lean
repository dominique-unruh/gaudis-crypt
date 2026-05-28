import Mathlib.Data.List.AList
-- import PlonkLean.Syntax
import Init.Data.Equiv.Basic

class TupleLike a (b : outParam Type) (c : outParam Type) where
  iso : a ≃ (b × c)

structure ProcSig where
  params : List Type
  ret    : Type

inductive MTy where
  | proc   : ProcSig → MTy
  -- | struct : List (String × MTy) → MTy
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
  | const{sig} : procSigToType sig → MExpr' Δ (.proc sig)
  | var  : Ref Δ M → MExpr' Δ M
  | app  : MExpr' Δ (.arr A B) → MExpr' Δ A → MExpr' Δ B
  -- | proj {fs name ty} : MExpr Δ (.struct fs) → HasFieldType fs name ty → MExpr Δ ty
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

def evalModule' {mctx : MCtx} {mty : MTy} (mex : MExpr' mctx mty) : mctxToType mctx -> mtyToType mty :=
  match mex with
  | .const p => fun _ => p
  | .var Ref.here => fun (_, x) => x
  | .var (Ref.there n) => fun (mctx', _) => evalModule' (.var n) mctx'
  | .app a b => fun ctx => (evalModule' a ctx) (evalModule' b ctx)
  | .fst a => fun ctx => (evalModule' a ctx).1
  | .snd a => fun ctx => (evalModule' a ctx).2
  | .abs body => fun ctx => fun x => (evalModule' body (ctx, x))

def evalModule {mty} (mex : MExpr mty) : mtyToType mty := evalModule' mex ()

def evalProc {sig} (mex : MExpr (.proc sig)) : procSigToType sig := evalModule mex
