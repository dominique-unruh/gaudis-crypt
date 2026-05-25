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
* `Program.call` has the form `call result_var proc_expr args`, storing the
  procedure's return value into a typed variable,
* module expressions are built only from module variables, application,
  and named projection.
-/

/-! ## Value types -/

/-
Value types are Lean's native `Type`. The context `VCtx := Ctx Type` stores
one Lean type per value variable, and `Expr s a := s → a` produces a value
of type `a` from a state of type `s`.

The `VTy` inductive below is a draft of an alternative intrinsic design.
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

Field names are strings; uniqueness is not enforced in `MTy` itself (Lean's
nested-inductive restrictions prevent embedding `AList` here). `HasFieldType`
finds the first matching field, so duplicates resolve to the first occurrence.
Projections are only constructible when `HasFieldType` evidence exists.
-/
inductive MTy where
  | proc   : ProcSig → MTy
  | struct : List (String × MTy) → MTy
  | arr    : MTy → MTy → MTy

/-! ## Contexts and typed variables -/

/--
A snoc-list context.

We use the same context shape for

* value-variable contexts (`VCtx := Ctx Type`), and
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

`here` matches the head of the list; `there` skips one entry and recurses.
For lists with duplicate field names this finds the first occurrence.
-/
inductive HasFieldType : List (String × MTy) → String → MTy → Type 1 where
  | here  : {name : String} → {ty : MTy} → {fs : List (String × MTy)} →
            HasFieldType ((name, ty) :: fs) name ty
  | there : {name : String} → {ty : MTy} → {fs : List (String × MTy)} →
            {other : String} → {otherTy : MTy} →
            HasFieldType fs name ty →
            HasFieldType ((other, otherTy) :: fs) name ty
  deriving Repr

/-! ## Expressions -/

/--
`Expr s a` is a pure expression over state `s` producing a value of type `a`.
Concretely, `Expr s a = s → a`.

Expressions are the only terms allowed as

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
`Exprs s ts` is a typed list of pure expressions over state `s` whose result
types are exactly `ts : List Type`.

Used for procedure call arguments: a call to a procedure with parameter list
`[τ₁, ..., τₙ]` requires an `Exprs s [τ₁, ..., τₙ]`.
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
`Program s Δ Γ` is a statement over state `s` which

* may refer to module variables in module context `Δ : MCtx`,
* may read value variables from value context `Γ : VCtx`.

Constructors:

* `assign x rhs` writes the result of pure expression `rhs` into variable `x`,
* `ifThenElse c t e` branches on pure boolean condition `c`,
* `seq p q` sequences two statements,
* `call x f args` calls procedure `f` (a module expression of proc type) with
  arguments `args`, storing the return value into variable `x`.

`call` uses a *module expression* of procedure type, not a direct literal.
-/
inductive Program s : MCtx → VCtx → Type _ where
  | assign     : Ref Γ τ → Expr s τ → Program s Δ Γ
  | ifThenElse : Expr s Bool → Program s Δ Γ → Program s Δ Γ → Program s Δ Γ
  | seq        : Program s Δ Γ → Program s Δ Γ → Program s Δ Γ
  | call {sig}       : Ref Γ τ → MExpr Δ (.proc sig) → Exprs s sig.params → Program s Δ Γ

/--
`Procedure s mctx vctx return_type` bundles a statement body with a pure
expression that computes its return value. The body runs in module context
`mctx` and value context `vctx`; `return_value` reads the result from state `s`.
-/
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
