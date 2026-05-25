import Mathlib.Data.List.AList

/-
A small intrinsically-typed DSL in Lean 4 with

* value expressions (`Expr`),
* typed variables (`Ref`),
* programs/statements (`Program`),
* module expressions (`MExpr`) over a separate module context,
* named tuples of modules (`MTy.struct`) with typed field projection,
* module functions and application,
* procedure calls as typed "holes" obtained from module expressions.

The design follows the requested separation:

* assignment RHSs are pure expressions,
* `ifThenElse` conditions are pure boolean expressions,
* `Program.call` has the form `call <module expression> <arguments>`,
* module expressions are built only from module variables, application,
  and named projection.
-/

/-! ## Object-language value types -/

/-
`VTy` is the type of ordinary runtime values manipulated by expressions
and programs.

We keep it intentionally small here:

* `unit`, `bool`, `nat`
* binary products for ordinary value tuples
-/


/- inductive VTy where
  | unit
  | bool
  | nat
  | prod : VTy → VTy → VTy
  deriving DecidableEq, Repr
 -/

/-! ## Procedure signatures and module types -/

/--
A procedure signature consists of

* a list of parameter types, and
* a return type.

A module of type `MTy.proc sig` represents a module containing exactly one
procedure with signature `sig`.
-/
structure ProcSig where
  params : List Type
  ret    : Type

/--
Module types.

* `proc sig`     : a single procedure module
* `struct fs`    : a named tuple / structure of submodules
* `arr A B`      : a module function from `A` to `B`

The field names of a structure are represented as strings.
The types ensure that projections are only allowed for fields that actually
exist, via the proof object `HasFieldType` defined below.
-/
inductive MTy where
  | proc   : ProcSig → MTy
  | struct : List (String × MTy) → MTy
  | arr    : MTy → MTy → MTy

/-! ## Contexts and typed variables -/

/--
A snoc-list context.

We use the same context shape for

* value-variable contexts (`VCtx := Ctx VTy`), and
* module-variable contexts (`MCtx := Ctx MTy`).

Snoc-lists are pleasant for intrinsically typed syntax because the newest
binding sits at the end, making typed de Bruijn references straightforward.
-/
inductive Ctx (α : Type _) where
  | nil  : Ctx α
  | snoc : Ctx α → α → Ctx α
  deriving Repr

abbrev VCtx := Ctx Type
abbrev MCtx := Ctx MTy

/--
A typed reference into a context.

`Ref Γ τ` means: a variable in context `Γ` whose type is exactly `τ`.

This is preferable to using bare `Fin` indices, because the typing information
is built directly into the reference itself, avoiding equality proofs.
-/
inductive Ref {α : Type u} : Ctx α → α → Type u where
  | here  : Ref (.snoc Γ a) a
  | there : Ref Γ a → Ref (.snoc Γ b) a
  deriving Repr

/-! ## Typed field lookup for named tuples of modules -/

/--
`HasFieldType fs name ty` is evidence that the field list `fs` contains
a field called `name` whose module type is `ty`.

This proof object is what makes named projection intrinsically typed.
A projection is only constructible if such evidence is available.
-/
-- TODO: Introduce a type for `List (String × ?)`. Also: do we need to ensure that the strings are distinct?
inductive HasFieldType : List (String × MTy) → String → MTy → Type 1 where
  | here  : {name : String} → {ty : MTy} → {fs : List (String × MTy)} →
            HasFieldType ((name, ty) :: fs) name ty
  | there : {name : String} → {ty : MTy} → {fs : List (String × MTy)} →
            {other : String} → {otherTy : MTy} →
            HasFieldType fs name ty →
            HasFieldType ((other, otherTy) :: fs) name ty
  deriving Repr

/-! ## Pure value expressions -/

/--
`Expr Γ τ` is the type of pure, side-effect-free expressions that read value
variables from context `Γ` and produce a value of type `τ`.

These are the only terms allowed as

* right-hand sides of assignments,
* arguments to procedure calls,
* conditions of conditionals.
-/
def Expr s a := s → a

/- inductive Expr : VCtx → VTy → Type where
  | var   : Ref Γ τ → Expr Γ τ
  | unit  : Expr Γ .unit
  | bool  : Bool → Expr Γ .bool
  | nat   : Nat → Expr Γ .nat
  | pair  : Expr Γ τ₁ → Expr Γ τ₂ → Expr Γ (.prod τ₁ τ₂)
  | fst   : Expr Γ (.prod τ₁ τ₂) → Expr Γ τ₁
  | snd   : Expr Γ (.prod τ₁ τ₂) → Expr Γ τ₂
  deriving Repr
 -/

/-! ## Typed lists of pure arguments -/

/--
`Exprs Γ ts` is a list of pure expressions whose types are exactly the list `ts`.

This is useful for procedure calls: a procedure with parameter list
`[τ₁, τ₂, ..., τₙ]` can only be called with `Exprs Γ [τ₁, τ₂, ..., τₙ]`.
-/
inductive Exprs s : List Type → Type _ where
  | nil  : Exprs s []
  | cons {t ts} : Expr s t → Exprs s ts → Exprs s (t :: ts)

/-! ## Module expressions -/

/--
`MExpr Δ M` is the type of module expressions built from the module-variable
context `Δ`.

Important design choice:

This syntax contains only

* module variables,
* module application,
* named field projection.

It does *not* contain literal modules directly. That is exactly the requested
shape: modules are referenced from the context, and combined only by
application and projection.
-/
inductive MExpr : MCtx → MTy → Type _ where
  | var  : Ref Δ M → MExpr Δ M
  | app  : MExpr Δ (.arr A B) → MExpr Δ A → MExpr Δ B
  | proj {fs name ty} : MExpr Δ (.struct fs) → HasFieldType fs name ty → MExpr Δ ty

/-! ## Programs / statements -/

/--
`Program Δ Γ τ` is a program which

* may refer to module variables in context `Δ`,
* may refer to value variables in context `Γ`, and
* returns a value of type `τ`.

The constructors reflect the requested language design:

* `pure e` embeds a side-effect-free expression as a trivial program,
* `assign x rhs` assigns a pure expression to a typed variable,
* `ifThenElse c t e` branches on a pure boolean condition,
* `seq p q` sequences two programs, keeping the second result,
* `call f args` calls a procedure obtained from a module expression.

In particular, `call` uses a *module expression* of procedure type,
not a direct procedure literal.
-/
inductive Program s : MCtx → VCtx → Type _ where
  | assign     : Ref Γ τ → Expr s τ → Program s Δ Γ
  | ifThenElse : Expr s Bool → Program s Δ Γ → Program s Δ Γ → Program s Δ Γ
  | seq        : Program s Δ Γ → Program s Δ Γ → Program s Δ Γ
  | call {sig}       : Ref Γ τ → MExpr Δ (.proc sig) → Exprs s sig.params → Program s Δ Γ

structure Procedure (s : Type) (mctx : MCtx) (vctx : VCtx) (return_type : Type) : Type _ where
  body : Program s mctx vctx
  return_value : Expr s return_type


/-! ## Small examples -/

/-- A sample procedure signature: `(Nat, Bool) -> Nat`. -/
def sigNatBoolToNat : ProcSig := {
  params := [Nat, Bool],
  ret := Nat
}

/--
A sample module type:
{ main : proc (Nat, Bool) -> Nat,
util : proc () -> Unit }
-/
def exampleStructTy : MTy :=
  .struct
    [ ("main", .proc sigNatBoolToNat)
    , ("util", .proc { params := [], ret := Unit })
    ]

/--
Evidence that field `"main"` exists in the sample structure with the expected type.
-/
def mainFieldProof :
    HasFieldType
      [ ("main", .proc sigNatBoolToNat)
      , ("util", .proc { params := [], ret := Unit })
      ]
      "main"
      (.proc sigNatBoolToNat) :=
  .here

/--
A tiny module context with one variable of `exampleStructTy`.
-/
def Δ₀ : MCtx := .snoc .nil exampleStructTy

/--
The module expression `M.main`, where `M` is the only module variable in `Δ₀`.
-/
def mainProcExpr : MExpr Δ₀ (.proc sigNatBoolToNat) :=
  .proj (.var Ref.here) mainFieldProof

def example_vctx : VCtx := Ctx.snoc .nil Nat

/--
An example call `M.main(5, true)`.
-/
def exampleCall : Program s Δ₀ example_vctx :=
  .call Ref.here mainProcExpr (.cons (fun _ => 5) (.cons (fun _ => true) .nil))

/--
A slightly larger example:
if true then M.main(5, true) else M.main(7, false)
-/
def exampleIf : Program s Δ₀ example_vctx :=
  .ifThenElse
    (fun _ => true)
    (.call Ref.here mainProcExpr (.cons (fun _ => 5) (.cons (fun _ => true) .nil)))
    (.call Ref.here mainProcExpr (.cons (fun _ => 7) (.cons (fun _ => false) .nil)))
