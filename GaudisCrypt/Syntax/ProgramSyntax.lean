import GaudisCrypt.Syntax.ExpressionSyntax

open GaudisCrypt

/-!
# Concrete syntax for programs and procedures

Surface syntax for the imperative probabilistic language (`StmtWithHoles` /
`ProcedureWithHoles` from `GaudisCrypt`).  Expression syntax (`GaudiExpr[ ]` and the `$`
sigil) is in `ExpressionSyntax.lean`; module syntax is in `ModuleSyntax.lean`.  See
`syntax-ideas.md` for design notes.

## Statements / programs — `GaudiProg[ … ]`

A `;`-terminated sequence of statements.  The statement forms are:
* `skip;`
* `x <- e;`                       — assignment;
* `a, b <- e;`  /  `(a, b) <- e;` — tuple assignment (the parentheses are optional);
* `x <$ e;`                       — sample `x` from distribution `e`;
* `x <- call p (e₁, …, eₙ);`      — call procedure `p`, storing the result in `x`;
* `call p (e₁, …, eₙ);`           — call `p`, discarding the result;
* `if (e) { … } else { … }`       — the `else` branch is optional;
* `while (e) { … }`
* `{ … }`                         — a nested block;
* `let x := e;` / `have h : P := prf;` / `letI …;` / `haveI …;` — an ordinary *Lean*
  binder (not a program statement), scoping over the statements that follow it in the
  same block.

The argument list `( … )` of a `call` is always required (write `()` for no arguments).

The sequence may start with `var x : T, …;` lines, `GaudiProg[ var i : Nat; i <- 0; … ]`, which
declare local variables exactly as in a `proc` (below): each name stands for its slot in the
locals of the `ProgramState`.

Example (`a b c : Lens Nat State`, `inc : Procedure …`):
```
GaudiProg[
  a <- $a + 1;
  b, c <- ($a, $a * 2);
  if ($a == 0) { a <- 1; } else { skip; }
  while ($b == 0) { b <- $b + 1; }
  a <- call inc ($a);
]
```

## Procedures — `proc (…) [uses (…)] [: R] { … }`

A procedure *term*:
```
proc (x : T, y : U) uses (A : (Nat) → Bool, B : (Bool) → Nat) : R {
  var u : V, w : W;     -- zero or more `var …;` lines of local variables
  <statements>
  return e
}
```
* parameters `(x : T, …)` (possibly none).  A binder may name several variables of one type,
  `(x y : T, …)`, and stands for the same list as writing them out one by one — so may a
  local-variable binder, and a module parameter after `using`;
* an optional `uses (…)` clause declaring *holes* (abstract sub-procedures), each written
  `name : (T₁, …, Tₙ) → R`.  Inside the body a hole is invoked with the ordinary
  `call A (…)` syntax — `A` resolves to a hole when it is one of the declared names, and to
  a concrete procedure otherwise;
* an optional return type `: R` (inferred from `return e` when omitted);
* local variables via one or more `var name : T, …;` lines (`var u w : V;` declares two).  A
  parameter or local `x : T` stands for the slot `localVarLens "x" T`
  of the locals; a fresh local starts at an unspecified value (`VariableAssignment.init`), so
  it should be written before it is read;
* a body of statements ending in `return e`.

A `let`/`have`/`letI`/`haveI` statement in the body scopes over the rest of the body *and*
over `return e`.  Body and return value are two separate fields of `ProcedureWithHoles`, so
the binders on the body's *spine* — those of the procedure's own block, each carrying the
rest of it — are repeated around the return value.  A binder nested inside an `if`/`while`/
block, on the other hand, ends with that block and does not reach `return e`.

## Procedure types and signatures

* `proctype (T, U, …) -> W`                    — the type of a closed procedure;
* `proctype (T, …) -> W uses ((T₁,…) → R, …)`   — the type of a procedure with holes;
* `procsig (T, U, …) -> W`                      — the bare `ProcedureSignature`.

`->` is used (rather than `:`) so these nest inside type ascriptions without extra
parentheses; they also pretty-print back into this form.

An argument of any of these may be *named* — `procsig (h : G, m : F) -> Bool` — which a
`ProcedureSignature` cannot record and which is therefore dropped, except by `moduletype`,
which keeps the names in the `@[gaudiProcParamNames]` attribute.  See the *Signature argument
lists* section below.

## Printing

Statements, procedures and the two type forms all *print* in this syntax again, and do so
round-trip faithfully: parsing what was printed gives the same term back.  A variable read
prints as `§x`, the printable spelling of `$x`.  See the *Printing* section at the end of
this file for the delaborators and for the two places where the printed form differs from
what one would write by hand.

e.g. `proctype (Nat, Bool) -> Nat`, `proctype (Nat) -> Nat uses ((Nat) → Bool, (Bool) → Nat)`,
`procsig (Nat, Bool) -> Nat`.  Note `Procedure (procsig (Nat) -> Nat) = proctype (Nat) -> Nat`.

The *module* type of a procedure, `procmod (…) -> R`, is in `ModuleSyntax.lean`.
-/

/-! ## Syntax for programs (`StmtWithHoles`)

Statement syntax over `StmtWithHoles h`.  Each expression position (assignment
RHS, sampling distribution, `if`/`while` condition) is wrapped with `GaudiExpr[ ]`
so the `$x` sigil works.  An l-value (assignment/sample LHS) is a *lens*, lifted
into the current full state `ProgramState` by `liftLens` — so a global `Lens a State`
may be written bare and is lifted with `Lens.intoGlobal`, and a local variable (a lens into
`ProgramState`) is used as it is.

Surface forms (`gaudi_stmt`):

    skip;
    x <- e;                       -- assignment
    a, b <- e;   (a,b) <- e;      -- tuple l-value (parens optional), via `Lens.pair`
    x <$ e;                       -- sampling (e : a distribution expression)
    x <- call p (e₁, …, eₙ);      -- procedure call, result stored in `x`
    call p (e₁, …, eₙ);           -- procedure call, result discarded (Lens.throwaway)
    if (e) { … } else { … }       -- the `else` branch is optional
    while (e) { … }
    { … }                         -- a block (sequence)
    let x := e;   have h : P := prf;   letI …;   haveI …;   -- a Lean binder

The call argument list `( … )` is always required (even `()`); the arguments form a
tuple matching the callee's `ParamType`.  (`hole` is still deferred.)

The four binder forms are not `StmtWithHoles` constructors: they are the ordinary Lean
term binders.  Each *carries* the statements it scopes over as a nested statement list, so
`let x := e;` followed by more statements is a single `gaudi_stmt` holding them, and the
binder is visible exactly there — in the statements that follow it in its own block, and
nowhere else. -/

/-! ## The `@[gaudiProcParamNames]` attribute

A `ProcedureSignature` records parameter *types* only, so the names written in a
`moduletype` field or a `module` procedure would be lost.  They are kept in this attribute
instead, on the declaration that names the procedure — a `moduletype` accessor `MT.f`, a
`module`'s procedure module `X.f` and its `X.f.procedure` — so that notation about a
procedure can bind its parameters by name even when the procedure itself is abstract (a field
of an arbitrary module of a declared module type has no body to read names off).

The attribute's syntax has to be declared under `Lean.Parser.Attr` — that is the namespace
Lean strips to get an attribute's name from its syntax kind — and an `initialize` block cannot
be *used* in the file that declares it, which is why both live here rather than next to the
commands that write them (`ModuleSyntax.lean`). -/

namespace Lean.Parser.Attr

/-- `@[gaudiProcParamNames x, m]` records the parameter names of a procedure-valued
declaration.  Written by the `moduletype` and `module` commands; may also be attached by hand
to an axiomatized procedure. -/
syntax (name := gaudiProcParamNames) "gaudiProcParamNames" ident,* : attr

end Lean.Parser.Attr

open Lean in
/-- The parameter names recorded for a procedure-valued declaration by
`@[gaudiProcParamNames …]`, if any.  Read with
`GaudisCrypt.gaudiProcParamNamesAttr.getParam? env declName`. -/
initialize GaudisCrypt.gaudiProcParamNamesAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `gaudiProcParamNames
    descr := "the parameter names of this procedure-valued declaration"
    getParam := fun _ stx => match stx with
      | `(attr| gaudiProcParamNames $ids,*) => return ids.getElems.map (·.getId)
      | _ => throwError "invalid `gaudiProcParamNames` attribute"
  }

namespace GaudisCrypt

variable [ProgramSpec]

/-- Lift a program variable used as an l-value into a setter on the full current state
`ProgramState`.  Dispatch is on the lens's *container* `M`: a global lens (`M = State`)
is lifted with `Lens.intoGlobal`, a full-state lens (`M = ProgramState`, e.g. a local
variable `localVarLens "x" T`) is kept as-is.  The content type `A` is deliberately
*not* a class parameter — resolution then only needs `M` (always concrete from the
argument), and the result's content unifies with the expected type as an ordinary,
postponable constraint.  (That is what lets a `call` result l-value resolve even before
the callee's `sig` is known.) -/
class LiftLens (M : Type u) where
  lift {A : Type} : Lens A M → Setter A ProgramState

instance : LiftLens State where
  lift x := x.intoGlobal.toSetter
instance : LiftLens ProgramState where lift x := x.toSetter

/-- User-facing l-value lift; the container `M` and the content `A` are inferred.
The result is a `Setter` (l-values only ever `set`). -/
def liftLens {A : Type} {M : Type u} [LiftLens M] (x : Lens A M) : Setter A ProgramState :=
  LiftLens.lift x

/-- The raw (un-lifted) lens for an l-value: a tuple `(x, y, …)` becomes a nested
`Lens.pair`; a single term is itself.  Pairing needs the components to be disjoint
lenses in the same container — the `Lens.Disjoint` instance is resolved at the concrete
lenses, so `(a, b)` requires `Lens.Disjoint a b`. -/
scoped syntax "[lvalRaw| " term "]" : term
macro_rules
  | `([lvalRaw| ($x:term, $y:term)]) => `(Lens.pair [lvalRaw| $x] [lvalRaw| $y])
  | `([lvalRaw| $x:term]) => `($x)

/-- Raw nested `Lens.pair` of a comma-list of l-value components (each component
may itself be a paren-tuple, handled by `[lvalRaw|]`). -/
scoped syntax "[lvalRawList| " term,+ "]" : term
macro_rules
  | `([lvalRawList| $x:term]) => `([lvalRaw| $x])
  | `([lvalRawList| $x:term, $xs:term,*]) => `(Lens.pair [lvalRaw| $x] [lvalRawList| $xs,*])

/-- An l-value lifted into the current full state `ProgramState`.  Accepts a single
lens, a parenthesised tuple `(a, b)`, or a bare comma-list `a, b` (top-level
parens optional) — all interpreted via `Lens.pair`. -/
scoped syntax "[lval| " term,+ "]" : term
macro_rules
  | `([lval| $xs:term,*]) => `(liftLens [lvalRawList| $xs,*])

/-- A single `_` l-value discards the value written to it (`Setter.throwaway`).  Declared
after the general rule so it takes priority. -/
macro_rules
  | `([lval| _]) => `(Setter.throwaway)

/- ### Concrete syntax -/

declare_syntax_cat gaudi_stmt

-- The `ppLine`/`ppSpace` sprinkled over these productions are pretty-printer hints only
-- (they parse as nothing and add no syntax arguments); they are what makes a printed
-- program come out one statement per line.  See the *Printing* section at the end.
syntax ppLine "skip" ";" : gaudi_stmt
syntax ppLine term:max,+ " <- " term ";" : gaudi_stmt
syntax ppLine term:max,+ " <$ " term ";" : gaudi_stmt
syntax (name := callStore) ppLine term:max,+ " <- " "call" ppSpace term:max
  " (" term,* ")" ";" : gaudi_stmt
syntax (name := callVoid) ppLine "call" ppSpace term:max " (" term,* ")" ";" : gaudi_stmt
-- internal: generated by `proc` from `call <holeName>` (users never write `holecall`)
syntax (name := holecallStore) ppLine term:max,+ " <- " "holecall" ppSpace term:max
  " (" term,* ")" ";" : gaudi_stmt
syntax (name := holecallVoid) ppLine "holecall" ppSpace term:max " (" term,* ")" ";" : gaudi_stmt
-- the `ppGroup`s keep a header on one line: a group holding a statement list holds hard
-- line breaks, and would otherwise break at every optional space as well
syntax ppLine ppGroup("if" " (" term ") " "{") gaudi_stmt* ppLine ppGroup("}" " else " "{")
  gaudi_stmt* ppLine "}" : gaudi_stmt
syntax ppLine ppGroup("if" " (" term ") " "{") gaudi_stmt* ppLine "}" : gaudi_stmt
syntax ppLine ppGroup("while" " (" term ") " "{") gaudi_stmt* ppLine "}" : gaudi_stmt
syntax ppLine "{" gaudi_stmt* ppLine "}" : gaudi_stmt
-- Lean binders in statement position.  The atoms are spelled exactly as in the core term
-- parsers (`Lean.Parser.Term.let` etc.), whose `letDecl` opens with its own `ppSpace`.
--
-- Each of these *carries the statements it scopes over* rather than being a statement in its
-- own right, and each is declared at a higher priority than the productions above.  Both are
-- forced by `letI`/`haveI`: unlike `let`/`have` (which are `leadPrec` term parsers), the core
-- `letI`/`haveI` parsers are `maxPrec`, so in
--     letI n : Nat := 1; a <- e;
-- the l-value parser `term:max` of the assignment production happily reads the whole
-- `letI n : Nat := 1; a` as one term.  That parse ends exactly where ours does, so it is only
-- taking the rest of the sequence into the production that makes ours a contender at all
-- (`longestMatch` prefers the longer parse), and only the priority that then settles the tie
-- (without it the two are returned as an ambiguous `choice` node).
-- the `ppGroup` keeps the binder itself on one line; the statements it carries print at the
-- same level as it does, since they are a continuation of the same block, not a nested one
syntax (priority := high) ppLine ppGroup("let" Lean.Parser.Term.letDecl ";")
  ppDedent(gaudi_stmt*) : gaudi_stmt
syntax (priority := high) ppLine ppGroup("have" Lean.Parser.Term.letDecl ";")
  ppDedent(gaudi_stmt*) : gaudi_stmt
syntax (priority := high) ppLine ppGroup("letI " Lean.Parser.Term.letDecl ";")
  ppDedent(gaudi_stmt*) : gaudi_stmt
syntax (priority := high) ppLine ppGroup("haveI " Lean.Parser.Term.letDecl ";")
  ppDedent(gaudi_stmt*) : gaudi_stmt

/-- Translate one statement to a `StmtWithHoles` term. -/
scoped syntax "[gstmt| " gaudi_stmt "]" : term
/-- Translate a statement sequence (fold with `seq`; empty ↦ `skip`). -/
scoped syntax "[gseq| " gaudi_stmt* "]" : term
/-- Top-level program bracket. -/
scoped syntax "GaudiProg[" gaudi_stmt* ppDedent(ppDedent(ppLine)) "]" : term

macro_rules
  | `([gseq| ]) => `(StmtWithHoles.skip)
  | `([gseq| $s:gaudi_stmt]) => `([gstmt| $s])
  | `([gseq| $s:gaudi_stmt $ss:gaudi_stmt*]) =>
      `(StmtWithHoles.seq [gstmt| $s] [gseq| $ss*])


macro_rules
  | `([gstmt| skip;]) => `(StmtWithHoles.skip)
  | `([gstmt| $xs:term,* <- $e:term;]) =>
      `(StmtWithHoles.assign [lval| $xs,*] (GaudiExpr[ $e ]))
  | `([gstmt| $xs:term,* <$ $e:term;]) =>
      `(StmtWithHoles.sample [lval| $xs,*] (GaudiExpr[ $e ]))
  | `([gstmt| if ($c:term) { $t:gaudi_stmt* } else { $e:gaudi_stmt* }]) =>
      `(StmtWithHoles.ifThenElse (GaudiExpr[ $c ]) [gseq| $t*] [gseq| $e*])
  | `([gstmt| if ($c:term) { $t:gaudi_stmt* }]) =>
      `(StmtWithHoles.ifThenElse (GaudiExpr[ $c ]) [gseq| $t*] StmtWithHoles.skip)
  | `([gstmt| while ($c:term) { $body:gaudi_stmt* }]) =>
      `(StmtWithHoles.while (GaudiExpr[ $c ]) [gseq| $body*])
  | `([gstmt| { $ss:gaudi_stmt* }]) => `([gseq| $ss*])
  -- a Lean binder around the translation of the statements it carries
  | `([gstmt| let $d:letDecl; $ss:gaudi_stmt*]) => `(let $d:letDecl; [gseq| $ss*])
  | `([gstmt| have $d:letDecl; $ss:gaudi_stmt*]) => `(have $d:letDecl; [gseq| $ss*])
  | `([gstmt| letI $d:letDecl; $ss:gaudi_stmt*]) => `(letI $d:letDecl; [gseq| $ss*])
  | `([gstmt| haveI $d:letDecl; $ss:gaudi_stmt*]) => `(haveI $d:letDecl; [gseq| $ss*])

open Lean in
/-- Build the (right-nested) argument tuple from a comma-list of arg expressions:
`[]` ↦ `()`, `[e]` ↦ `e`, `e :: es` ↦ `(e, <es>)` — matching `typeListToTuple`. -/
private def mkArgTuple (args : List Term) : MacroM Term := do
  match args with
  | []      => `(())
  | [e]     => pure e
  | e :: es => do `(($e, $(← mkArgTuple es)))

-- `call` (procedure) and `holecall` (hole) statements.  `holecall` is *internal*: the
-- `proc` macro rewrites `call <holeName>` to it; users only ever write `call`.  In both
-- cases the callee is listed first so its `sig` is unified before the result l-value/args.
open Lean in
macro_rules
  | `([gstmt| $xs:term,* <- call $p:term ( $args:term,* );]) => do
      `(StmtWithHoles.call [lval| $xs,*] $p (GaudiExpr[ $(← mkArgTuple args.getElems.toList) ]))
  | `([gstmt| call $p:term ( $args:term,* );]) => do
      `(StmtWithHoles.call Setter.throwaway $p (GaudiExpr[ $(← mkArgTuple args.getElems.toList) ]))
  | `([gstmt| $xs:term,* <- holecall $n:term ( $args:term,* );]) => do
      `(StmtWithHoles.hole $n [lval| $xs,*] (GaudiExpr[ $(← mkArgTuple args.getElems.toList) ]))
  | `([gstmt| holecall $n:term ( $args:term,* );]) => do
      `(StmtWithHoles.hole $n Setter.throwaway (GaudiExpr[ $(← mkArgTuple args.getElems.toList) ]))

macro_rules
  | `(GaudiProg[ $ss:gaudi_stmt* ]) => `([gseq| $ss*])

/- ### Procedures

`proc (x : T, …) [: R] { var u : U, …; <stmts> ; return e }` builds a
`ProcedureWithHoles .empty sig` with `parameterNames := ["x", …]`.  Each parameter and
local-variable name `x : T` is `letI`-bound — the user's identifier spliced in, so hygiene
lines up — to its slot `localVarLens "x" T` in the locals of the
`ProgramState`; a parameter is just a local whose slot the call initialises.  `letI` inlines
its value during elaboration, so the elaborated term holds the slot at every use
and no binder, and Lean's own scoping decides what `x` refers to (a Lean binder in the body
named `x` shadows it).  The body's `$x` and `x <- …` then resolve via the ordinary expression
machinery.  `: R` is optional; without it the return type is inferred from `return e`.

Variable names are strings: an identifier must be atomic (`a.b` is rejected, since it and
`«a.b»` would name the same string), and a name may be declared only once per `proc` (as a
parameter, a local or a hole), so that one name never stands for two slots.

Program variables are *frame-relative* names: inside a `proc` literal nested in another
`proc`'s body (a callee written in place), an outer `x` that the inner `proc` does not declare
still elaborates to the slot `"x"`, which is then the *callee's* slot `"x"`. -/

open Lean in section

declare_syntax_cat proc_binder
syntax ident " : " term : proc_binder
-- several names of the same type in one binder, as in `var m m' : Message;`.  The single-name
-- form above is kept as its own production (it is what the delaborators build), so the two do
-- not overlap: this one needs at least two names.
syntax ident ident+ " : " term : proc_binder

-- The `ProgramSyntax.*` helpers below are implementation details of this file's syntax, but not
-- `private`: `HoareSyntax.lean` builds its own block syntax out of the same pieces, so that
-- the local-variable lenses and the binder wrapping stay in one place.  The `ProgramSyntax`
-- prefix keeps them out of `GaudisCrypt` proper.

/-- The string name of a program variable: the identifier's name, which must be atomic. -/
def ProgramSyntax.varNameString (id : Ident) : MacroM String :=
  match id.getId.eraseMacroScopes with
  | .str .anonymous s => pure s
  | n => Macro.throwErrorAt id s!"program variable names must be atomic, but `{n}` is not"

/-- Reject a name declared twice among the parameters, local variables and holes of one
`proc` (or the `var`s of one `GaudiProg[ ]`). -/
def ProgramSyntax.checkDistinct (ids : Array Ident) : MacroM Unit := do
  let mut seen : Array String := #[]
  for id in ids do
    let s ← ProgramSyntax.varNameString id
    if seen.contains s then Macro.throwErrorAt id s!"`{s}` is declared twice"
    seen := seen.push s

/-- The `letI` binding of a program variable `x : T`: `x` stands for its local slot
`localVarLens "x" T`. -/
def ProgramSyntax.varBinding (id : Ident) (ty : Term) : MacroM (Ident × Term × Term) := do
  let s := Syntax.mkStrLit (← ProgramSyntax.varNameString id)
  return (id, ← `(Lens $ty ProgramState), ← `(localVarLens $s $ty))

/-- Wrap `inner` in the `letI` bindings `bs` (outermost first). -/
def ProgramSyntax.wrapLetI (bs : Array (Ident × Term × Term)) (inner : Term) : MacroM Term :=
  bs.foldrM (fun (id, ty, val) acc => `(letI $id : $ty := $val; $acc)) inner

/-- `Lens.id` followed by a chain of `.ofst` (`true`) / `.osnd` (`false`).  Used for argument
tuples (`hoare[ M (x, m) : … ]`), no longer for local variables. -/
def ProgramSyntax.mkChain (steps : List Bool) : MacroM Term := do
  let mut acc ← `(Lens.id)
  for s in steps do
    acc ← if s then `($(acc).ofst) else `($(acc).osnd)
  pure acc

/-- Steps to reach slot `k` of a right-nested `n`-tuple (the last element is
un-wrapped, so it needs no final `.ofst`). -/
def ProgramSyntax.navSteps (k n : Nat) : List Bool :=
  if k + 1 == n then List.replicate k false else true :: List.replicate k false

/-- The names a binder declares, each paired with the (shared) declared type. -/
def ProgramSyntax.parseBinder : TSyntax `proc_binder → MacroM (List (Ident × Term))
  | `(proc_binder| $id:ident : $ty:term) => pure [(id, ty)]
  | `(proc_binder| $id:ident $ids:ident* : $ty:term) =>
      pure ((id :: ids.toList).map (·, ty))
  | _ => Macro.throwUnsupported

/-- A hole declaration `A : (T₁, …, Tₙ) → R` (an abstract procedure with no locals). -/
declare_syntax_cat hole_binder
syntax ident " : " "(" term,* ")" " → " term : hole_binder

private def ProgramSyntax.parseHoleBinder :
    TSyntax `hole_binder → MacroM (Ident × List Term × Term)
  | `(hole_binder| $id:ident : ( $ps:term,* ) → $ret:term) => pure (id, ps.getElems.toList, ret)
  | _ => Macro.throwUnsupported

/-- Rewrite `call A (…)` → `holecall A (…)` for every callee `A` whose name is a hole
(recursing into `if`/`while`/block bodies); everything else is left untouched. -/
partial def ProgramSyntax.rewriteHoles (holeNames : List Name) (s : TSyntax `gaudi_stmt) :
    MacroM (TSyntax `gaudi_stmt) := do
  let k := s.raw.getKind
  -- `call`/`holecall` statements carry a sepBy arg-list inside parens, which category
  -- quotations cannot match, so we dispatch on the production kind at the `Syntax` level.
  if k == ``callStore || k == ``callVoid then
    -- callee position: `callStore` is `xs,* "<-" "call" callee …`; `callVoid` is `"call" callee …`.
    let calleeIdx := if k == ``callStore then 3 else 1
    let args := s.raw.getArgs
    let callee := args[calleeIdx]!
    if callee.isIdent && holeNames.contains callee.getId then
      -- swap kind to the `holecall*` production and the `"call"` atom → `"holecall"`.
      let newKind := if k == ``callStore then ``holecallStore else ``holecallVoid
      let newArgs := args.map fun a =>
        match a with
        | .atom info "call" => .atom info "holecall"
        | _ => a
      return ⟨(s.raw.setArgs newArgs).setKind newKind⟩
    else
      return s
  match s with
  | `(gaudi_stmt| if ($c:term) { $t:gaudi_stmt* } else { $e:gaudi_stmt* }) => do
      `(gaudi_stmt| if ($c) { $(← t.mapM (rewriteHoles holeNames))* }
                          else { $(← e.mapM (rewriteHoles holeNames))* })
  | `(gaudi_stmt| if ($c:term) { $t:gaudi_stmt* }) => do
      `(gaudi_stmt| if ($c) { $(← t.mapM (rewriteHoles holeNames))* })
  | `(gaudi_stmt| while ($c:term) { $b:gaudi_stmt* }) => do
      `(gaudi_stmt| while ($c) { $(← b.mapM (rewriteHoles holeNames))* })
  | `(gaudi_stmt| { $ss:gaudi_stmt* }) => do
      `(gaudi_stmt| { $(← ss.mapM (rewriteHoles holeNames))* })
  | `(gaudi_stmt| let $d:letDecl; $ss:gaudi_stmt*) => do
      `(gaudi_stmt| let $d:letDecl; $(← ss.mapM (rewriteHoles holeNames))*)
  | `(gaudi_stmt| have $d:letDecl; $ss:gaudi_stmt*) => do
      `(gaudi_stmt| have $d:letDecl; $(← ss.mapM (rewriteHoles holeNames))*)
  | `(gaudi_stmt| letI $d:letDecl; $ss:gaudi_stmt*) => do
      `(gaudi_stmt| letI $d:letDecl; $(← ss.mapM (rewriteHoles holeNames))*)
  | `(gaudi_stmt| haveI $d:letDecl; $ss:gaudi_stmt*) => do
      `(gaudi_stmt| haveI $d:letDecl; $(← ss.mapM (rewriteHoles holeNames))*)
  | _ => pure s

/-- Wrap `e` in the Lean binders on the *spine* of the statement sequence `ss`: the
`let`/`have`/`letI`/`haveI` statements of the sequence itself, not those nested inside an
`if`/`while`/block.  Each such statement carries the rest of its sequence, so the spine is a
chain — at most one binder per level, recursed into.  `proc` uses this to repeat the body's
binders around the return value, which is a separate field of `ProcedureWithHoles`. -/
partial def ProgramSyntax.wrapSpineBinders (ss : Array (TSyntax `gaudi_stmt)) (e : Term) :
    MacroM Term := do
  for s in ss do
    match s with
    | `(gaudi_stmt| let $d:letDecl; $rest:gaudi_stmt*) =>
        return ← `(let $d:letDecl; $(← wrapSpineBinders rest e))
    | `(gaudi_stmt| have $d:letDecl; $rest:gaudi_stmt*) =>
        return ← `(have $d:letDecl; $(← wrapSpineBinders rest e))
    | `(gaudi_stmt| letI $d:letDecl; $rest:gaudi_stmt*) =>
        return ← `(letI $d:letDecl; $(← wrapSpineBinders rest e))
    | `(gaudi_stmt| haveI $d:letDecl; $rest:gaudi_stmt*) =>
        return ← `(haveI $d:letDecl; $(← wrapSpineBinders rest e))
    | _ => pure ()
  return e

syntax ppGroup("proc" " (" proc_binder,* ")" (ppSpace "uses" " (" hole_binder,* ")")?
         (" : " term:max)? " {")
         (ppIndent(ppLine ppGroup("var " proc_binder,* ";")))*
         gaudi_stmt*
         ppIndent(ppLine ppGroup("return " term (";")?))
       ppDedent(ppDedent(ppLine)) "}" : term

macro_rules
  | `(proc ( $params:proc_binder,* ) $[uses ( $holes:hole_binder,* )]? $[: $retTy:term]? {
        $[var $locals:proc_binder,* ;]*
        $stmts:gaudi_stmt*
        return $ret:term $[;]?
      }) => do
    -- a binder may declare several names of one type, and is flattened into one entry each
    let paramBs := (← params.getElems.toList.mapM ProgramSyntax.parseBinder).flatten.toArray
    -- multiple `var …;` lines are concatenated into a single local-variable list
    let localBs := (← (locals.toList.flatMap (·.getElems.toList)).mapM
      ProgramSyntax.parseBinder).flatten.toArray
    let holeBs := (← match holes with
      | some hs => hs.getElems.toList.mapM ProgramSyntax.parseHoleBinder
      | none    => pure []).toArray
    ProgramSyntax.checkDistinct ((paramBs ++ localBs).map (·.1) ++ holeBs.map (·.1))
    -- the signature and the parameter names
    let paramTys := paramBs.map (·.2)
    let retTyTerm ← match retTy with | some r => pure r | none => `(_)
    let sigTerm ← `(({ params := [$paramTys,*], ret := $retTyTerm } : ProcedureSignature))
    let paramNames : Array Term ← paramBs.mapM fun (id, _) => do
      pure ⟨(Syntax.mkStrLit (← ProgramSyntax.varNameString id)).raw⟩
    -- one `letI` per parameter and local variable, binding it to its local slot
    let binds ← (paramBs ++ localBs).mapM fun (id, ty) => ProgramSyntax.varBinding id ty
    -- holes: a `ProcedureSignature` (no locals) each, folded into a `HoleSigs` context,
    -- and one `let` per name binding it to its `HoleIndex` (first-declared = `.zero`).
    let nh := holeBs.size
    let holeSigTerms ← holeBs.mapM fun (_, ps, ret) =>
      `(({ params := [$(ps.toArray),*], ret := $ret } : ProcedureSignature))
    -- a cons list, so it is built from the back of the list forwards; the resulting term still
    -- reads in declaration order, `HoleSigs.cons s₁ (… (HoleSigs.cons sₙ HoleSigs.empty))`
    let mut hCtx ← `(HoleSigs.empty)
    for sigT in holeSigTerms.reverse do hCtx ← `(HoleSigs.cons $sigT $hCtx)
    let mut holeBinds : Array (Ident × Term × Term) := #[]
    for k in [0:nh] do
      let (id, _, _) := holeBs[k]!
      let mut idx ← `(HoleIndex.zero)
      for _ in [0 : k] do idx ← `(HoleIndex.succ $idx)
      holeBinds := holeBinds.push (id, ← `(HoleIndex $hCtx $(holeSigTerms[k]!)), idx)
    let wrapLet (bs : Array (Ident × Term × Term)) (inner : Term) : MacroM Term :=
      bs.foldrM (fun (id, ty, val) acc => `(let $id : $ty := $val; $acc)) inner
    -- rewrite `call A (…)` → `holecall A (…)` for every callee `A` that is a declared hole
    let holeNames := holeBs.toList.map (·.1.getId)
    let stmts' ← stmts.mapM (ProgramSyntax.rewriteHoles holeNames)
    let body ← ProgramSyntax.wrapLetI binds
      (← wrapLet holeBinds (← `((GaudiProg[ $stmts'* ] : StmtWithHoles $hCtx))))
    -- the return value repeats the variable bindings and the body's spine binders
    let retval ← ProgramSyntax.wrapLetI binds
      (← ProgramSyntax.wrapSpineBinders stmts'
        (← `((GaudiExpr[ $ret ] : Getter _ ProgramState))))
    `(({ parameterNames := [$paramNames,*], body := $body, return_val := $retval }
        : ProcedureWithHoles $hCtx $sigTerm))

/-- `GaudiProg[ var x : T, …; <stmts> ]`: a statement sequence with local variables, each bound
to its local slot exactly as in a `proc`.  (The form without `var` lines is the plain
`GaudiProg[ … ]` above.) -/
scoped syntax "GaudiProg[" (ppIndent(ppLine ppGroup("var " proc_binder,* ";")))+ gaudi_stmt*
  ppDedent(ppDedent(ppLine)) "]" : term

macro_rules
  | `(GaudiProg[ $[var $locals:proc_binder,* ;]* $ss:gaudi_stmt* ]) => do
    let localBs := (← (locals.toList.flatMap (·.getElems.toList)).mapM
      ProgramSyntax.parseBinder).flatten.toArray
    ProgramSyntax.checkDistinct (localBs.map (·.1))
    let binds ← localBs.mapM fun (id, ty) => ProgramSyntax.varBinding id ty
    ProgramSyntax.wrapLetI binds (← `([gseq| $ss*]))

end

/-! ### Signature argument lists — `proc_arg`

The argument list of a `procsig`/`proctype`/`procmod`, and of a `proc` field of a
`moduletype`, is a list of types, each of which may carry a name:
`procsig (h : G, m : F) -> Bool`.  A `ProcedureSignature` records only the types, so the names
are dropped everywhere except by `moduletype` and `module`, which put them in
`@[gaudiProcParamNames]`.

Deliberately *not* `proc_binder` (the named binder of `proc`/`var`/`using`).  Serving both
from one category would mean adding a bare-type production to it, and a syntax category being
global, that production would also turn up in the five positions where a name is mandatory:
`var Int;`, `proc (Int) { … }` and `module X using (Int)` would then parse and fail late in
`ProgramSyntax.parseBinder` instead of at the parser. -/

declare_syntax_cat proc_arg
/-- A named argument slot, `x : T`.  The name is documentation except in a `moduletype`. -/
syntax ident " : " term : proc_arg
/-- An unnamed argument slot: just the type. -/
syntax term : proc_arg

open Lean in section

/-- The name (if one was written) and the declared type of one argument slot. -/
def ProgramSyntax.procArgParts? : TSyntax `proc_arg → Option (Option Ident × Term)
  | `(proc_arg| $id:ident : $ty:term) => some (some id, ty)
  | `(proc_arg| $ty:term)             => some (none, ty)
  | _                                 => none

/-- The declared types of an argument list, with the names dropped. -/
def ProgramSyntax.procArgTypes (as : Array (TSyntax `proc_arg)) : Option (Array Term) :=
  as.mapM fun a => (·.2) <$> ProgramSyntax.procArgParts? a

/-- The names an argument list wrote, `none` for a slot that was left unnamed. -/
def ProgramSyntax.procArgNames (as : Array (TSyntax `proc_arg)) : Option (Array (Option Ident)) :=
  as.mapM fun a => (·.1) <$> ProgramSyntax.procArgParts? a

/-- An unnamed argument slot from its type — what the unexpanders build, a printed signature
having no names to show. -/
def ProgramSyntax.mkProcArg {m : Type → Type} [Monad m] [MonadQuotation m] (ty : Term) :
    m (TSyntax `proc_arg) := `(proc_arg| $ty:term)

end

/-! ### Procedure *type* syntax

`proctype (T, U, V) -> W` is the type `Procedure { params := [T, U, V], ret := W }`, and
`proctype (…) -> W uses ((A₁,…) → R₁, …)` is the corresponding `ProcedureWithHoles`, whose
hole context is built from the listed (nameless) procedure signatures.  (Uses `->` rather
than `:` so it needs no extra parentheses inside a type ascription.) -/

/-- A nameless hole signature `(T₁, …, Tₙ) → R` inside a `proctype … uses (…)` clause. -/
declare_syntax_cat hole_sig
syntax "(" term,* ")" " → " term : hole_sig

syntax "proctype " "(" proc_arg,* ")" (" → " <|> " -> ") term
         (" uses " "(" hole_sig,* ")")? : term

open Lean in
macro_rules
  -- unicode `→` spelling delegates to the `->` arm below (distinguished by the arrow atom)
  | `(proctype ( $params:proc_arg,* ) → $ret:term $[uses ( $holes:hole_sig,* )]?) =>
      `(proctype ( $params,* ) -> $ret $[uses ( $holes,* )]?)
  | `(proctype ( $params:proc_arg,* ) -> $ret:term $[uses ( $holes:hole_sig,* )]?) => do
      let some paramTys := ProgramSyntax.procArgTypes params.getElems | Macro.throwUnsupported
      let sigTerm ← `(ProcedureSignature.mk [$paramTys,*] $ret)
      match holes with
      | none    => `(Procedure $sigTerm)
      | some hs =>
        let mut hCtx ← `(HoleSigs.empty)
        for h in hs.getElems.reverse do
          match h with
          | `(hole_sig| ( $ps:term,* ) → $r:term) =>
              hCtx ← `(HoleSigs.cons (ProcedureSignature.mk [$ps,*] $r) $hCtx)
          | _ => Macro.throwUnsupported
        `(ProcedureWithHoles $hCtx $sigTerm)

/-! `proctype` unexpanders.  A signature already prints as `procsig (…) -> …` (the
`ProcedureSignature.mk` unexpander), so we just rewrite `Procedure (procsig …)` and
`ProcedureWithHoles … (procsig …)` to `proctype …`.  Parameter lists are read off the raw
`procsig` node (a category quotation can't match the sepBy inside the parens). -/

open Lean PrettyPrinter in
/-- If `s` is a `procsig ( … ) -> …` node, return its parameter list and return type.
    (Not `private`: `ModuleSyntax.lean` unexpands `procmod` with it.) -/
def procsigParts? (s : Syntax) : Option (Syntax.TSepArray `proc_arg "," × TSyntax `term) :=
  let a := s.getArgs
  if a.size == 6 && a[0]!.getAtomVal == "procsig" then some (⟨a[2]!.getArgs⟩, ⟨a[5]!⟩) else none

open Lean PrettyPrinter in
@[app_unexpander Procedure]
def unexpandProcedure : Unexpander
  | `($_ $sig) => do
      let some (ps, r) := procsigParts? sig.raw | throw ()
      `(proctype ( $ps,* ) → $r)
  | _ => throw ()

open Lean PrettyPrinter in
/-- Collect every `procsig ( … ) -> …` node in `s`, left to right.  (Matching field
notation on `HoleSigs.cons` in a quotation is brittle, so we just gather the leaves.)
A hole context `HoleSigs.cons s₁ (… (HoleSigs.cons sₙ HoleSigs.empty))` has the hole signatures as
its only `procsig` nodes, in declaration order. -/
private partial def collectProcsigParts (s : Syntax) :
    Array (Syntax.TSepArray `proc_arg "," × TSyntax `term) :=
  match procsigParts? s with
  | some pr => #[pr]
  | none    => s.getArgs.foldl (fun acc a => acc ++ collectProcsigParts a) #[]

open Lean PrettyPrinter in
@[app_unexpander ProcedureWithHoles]
def unexpandProcedureWithHoles : Unexpander
  | `($_ $holes $sig) => do
      let some (ps, r) := procsigParts? sig.raw | throw ()
      let holeParts := collectProcsigParts holes.raw
      if holeParts.isEmpty then `(proctype ( $ps,* ) -> $r)
      else
        -- a `hole_sig` is a bare type list (holes are named as a whole, their arguments never),
        -- so the names — which a printed signature has none of anyway — are dropped here
        let holeSyns ← holeParts.mapM fun (hps, hr) => do
          let some htys := ProgramSyntax.procArgTypes hps.getElems | throw ()
          `(hole_sig| ( $htys,* ) → $hr)
        `(proctype ( $ps,* ) → $r uses ( $holeSyns,* ))
  | _ => throw ()

/-! ### Procedure *signature* syntax

`procsig (T, U, V) -> W` is the bare `ProcedureSignature.mk [T, U, V] W` (the same surface
form as `proctype`, minus the holes — a signature has none).  By construction
`Procedure (procsig …) = proctype …`.  The unexpander is on `ProcedureSignature.mk`, so any
signature with a literal parameter list prints back as `procsig (…) -> …`. -/

syntax "procsig " "(" proc_arg,* ")" (" → " <|> " -> ") term : term

open Lean in
macro_rules
  | `(procsig ( $params:proc_arg,* ) → $ret:term) => `(procsig ( $params,* ) -> $ret)
  | `(procsig ( $params:proc_arg,* ) -> $ret:term) => do
      let some paramTys := ProgramSyntax.procArgTypes params.getElems | Macro.throwUnsupported
      `(ProcedureSignature.mk [$paramTys,*] $ret)

open Lean PrettyPrinter in
/-- A signature holds no names, so it prints with unnamed argument slots. -/
@[app_unexpander ProcedureSignature.mk]
def unexpandProcSig : Unexpander
  | `($_ [$ps,*] $r) => do
      let args ← ps.getElems.mapM ProgramSyntax.mkProcArg
      `(procsig ( $args,* ) → $r)
  | _ => throw ()

/-! ## Printing

Delaborators that render elaborated terms back into the surface syntax above: a procedure
built by `proc` prints as `proc (…) uses (…) : R { … }`, a statement prints as
`GaudiProg[ … ]`, and a `Getter` standing on its own prints as `GaudiExpr[ … ]` (with variable
reads as the `§x` sigil, the printable spelling of `$x`).

A `Getter` prints that way only over a `ProgramState`, the only carrier `GaudiExpr[ ]` can
build — a `Getter a State` (an `Expr a`) would print as something that does not elaborate
back.  Inside a statement the expression slots are printed by `delabGaudiExpr` directly, with
no `GaudiExpr[ ]` wrapper, since `$`/`§` already works there.

Printing is *round-trip faithful*: parsing what was printed yields the same term back
(`ProgramSyntaxTest.lean` checks this by printing, re-parsing and re-elaborating).  Hence
the two places where the printed form deviates from what one would write by hand:

* a `seq` in the left position of a `seq` is printed as a block `{ … }`, since re-parsing
  a flat sequence would re-associate it;
* a hole call prints as `call A (…)` only inside the `proc` that declares `A` in its `uses`
  clause (which is where the macro turns `call` back into a hole call), and as the internal
  `holecall n (…)` anywhere else;
* `let`/`have` statements print with their type ascribed (`let x : T := v;`), an anonymous one
  under the `_` it was written as (Lean names it inaccessibly, `x✝`, which is not a name that
  parses back — so a statement that does refer to it makes the delaborators step aside); `letI`/
  `haveI` do not print at all — they *inline* their value during elaboration, so no binder
  of theirs survives in the term to be printed.  What is printed is then the inlined term,
  which is what re-parsing gives back, so the round trip still holds.

Whenever a term does not fit the surface syntax — a `Getter` that is not of the shape
`GaudiExpr[ ]` builds, an l-value that is not a lifted lens, `let`s that `proc` would not
have generated — the delaborators fail and Lean falls back to its default output.  They also
step aside under `pp.explicit` and `set_option pp.notation false`, and under the dedicated
`set_option pp.gaudisCrypt false`, which switches *only* them off and leaves the rest of
Lean's notation alone — the way to look at the underlying term.

`pp.gaudisCrypt` reaches the delaborators above but not the `app_unexpander`s further up this
file (`proctype`/`procsig`, `Procedure`): `UnexpandM` is `ReaderT Syntax (EStateM Unit Unit)`
and carries no `Options`, so an unexpander cannot consult one.  Those still print the *type*
as `proctype (…) -> R` under `pp.gaudisCrypt false`; `pp.notation false` turns them off. -/

section Printing
open Lean PrettyPrinter Delaborator SubExpr

/- The pieces that are not `private` — `guardSurfaceSyntax`,
`delabGaudiExpr`, `withPeeledLets`, `delabGaudiStmts`, `spineLetNames`, and the frame-variable
helpers in `ProgramSyntax` — are shared with the
`hoare[ ]` delaborators in `HoareSyntax.lean`, which has to take a triple apart the same way:
peel the `let`s a `proc`-style binder emits, then print what is underneath. -/

/-- Name given to the state binder of a `GaudiExpr[ ]` getter while delaborating it. -/
private def stateBinderName : Name := `st

private partial def syntaxHasIdent (n : Name) : Syntax → Bool
  | .ident _ _ v _ => v.eraseMacroScopes == n
  | .node _ _ args => args.any (syntaxHasIdent n)
  | _ => false

register_option pp.gaudisCrypt : Bool := {
  defValue := true
  descr := "(pretty printer) print GaudisCrypt statements and procedures in their surface \
syntax (`GaudiProg[ … ]`, `proc … { … }`).  Turn off to see the underlying term while \
keeping the rest of Lean's notation."
}

private def getPPGaudisCrypt (o : Options) : Bool :=
  o.get pp.gaudisCrypt.name pp.gaudisCrypt.defValue

/-- Surface syntax is printed only when Lean is printing readably, and only while
`pp.gaudisCrypt` is on. -/
def guardSurfaceSyntax : DelabM Unit := do
  guard (← getPPOption getPPGaudisCrypt)
  guard (← getPPOption getPPNotation)
  guard <| !(← getPPOption getPPExplicit)

/-- The elements of a literal list `[a, b, c]` at the current position. -/
private partial def delabListElems : DelabM (Array Term) := do
  match (← getExpr).getAppFnArgs with
  | (``List.nil, _) => return #[]
  | (``List.cons, args) => do
      guard (args.size == 3)
      let hd ← withNaryArg 1 delab
      let tl ← withNaryArg 2 delabListElems
      return #[hd] ++ tl
  | _ => failure

/-- The elements of a literal list expression `[a, b, c]`. -/
private partial def listLitElems? (e : Lean.Expr) : Option (Array Lean.Expr) :=
  match e.getAppFnArgs with
  | (``List.nil, _) => some #[]
  | (``List.cons, #[_, hd, tl]) => (#[hd] ++ ·) <$> listLitElems? tl
  | _ => none

/-- The strings of a literal list of string literals `["x", "y"]`. -/
private def stringListLit? (e : Lean.Expr) : Option (Array String) := do
  (← listLitElems? e).mapM fun
    | .lit (.strVal s) => some s
    | _ => none

/-- `ProcedureSignature.mk [T₁, …] R` ↦ its parameter types and its return type. -/
private def delabSigParts : DelabM (Array Term × Term) := do
  guard ((← getExpr).isAppOfArity ``ProcedureSignature.mk 2)
  return (← withNaryArg 0 delabListElems, ← withNaryArg 1 delab)

/-- `HoleSigs.cons s₁ (… (HoleSigs.cons sₙ HoleSigs.empty))` ↦ the `sᵢ`, in declaration order. -/
private partial def delabHoleSigs : DelabM (Array (Array Term × Term)) := do
  match (← getExpr).getAppFnArgs with
  | (``HoleSigs.empty, _) => return #[]
  | (``HoleSigs.cons, args) => do
      guard (args.size == 2)
      let sig ← withNaryArg 0 delabSigParts
      let rest ← withNaryArg 1 delabHoleSigs
      return #[sig] ++ rest
  | _ => failure

/-- `Getter.mk fun st => e` — what `GaudiExpr[ e ]` builds — ↦ `e`.  Fails when the state
binder really occurs in `e`, since then `e` is not expressible in the surface syntax. -/
def delabGaudiExpr : DelabM Term := do
  guard ((← getExpr).isAppOfArity ``Getter.mk 3)
  withNaryArg 2 do
    guard (← getExpr).isLambda
    withBindingBody stateBinderName do
      let stx ← delab
      guard <| !syntaxHasIdent stateBinderName stx
      return stx

/-- A `Getter` standing on its own — not as the expression slot of a statement, where
`delabGaudiExpr` is called directly — prints as `GaudiExpr[ e ]`.

Restricted to getters over a `ProgramState`: that is the only carrier `GaudiExpr[ ]` can
build, since the `CurrentState` instance it installs holds one.  Without the guard a
`Getter a State` (an `Expr a`) would print as something that does not elaborate back. -/
@[delab app.GaudisCrypt.Getter.mk]
private def delabGaudiExprTerm : Delab := do
  guardSurfaceSyntax
  guard (((← getExpr).getArg! 1).isAppOf ``ProgramState)
  `(GaudiExpr[ $(← delabGaudiExpr) ])

/-- One component of an l-value: a nested `Lens.pair` prints as the tuple `(a, b)`. -/
private partial def delabLValueComponent : DelabM Term := do
  match (← getExpr).getAppFnArgs with
  | (``Lens.pair, args) => do
      guard (args.size == 6)
      let x ← withNaryArg 3 delabLValueComponent
      let y ← withNaryArg 4 delabLValueComponent
      `(($x, $y))
  | _ => delab

/-- The top-level comma list of an l-value lens (its right `Lens.pair` spine). -/
private partial def delabLValueList : DelabM (Array Term) := do
  match (← getExpr).getAppFnArgs with
  | (``Lens.pair, args) => do
      guard (args.size == 6)
      let x ← withNaryArg 3 delabLValueComponent
      let ys ← withNaryArg 4 delabLValueList
      return #[x] ++ ys
  | _ => return #[← delab]

/-- The l-value of an assignment/sample/call: `liftLens x` ↦ the components of `x`,
`Setter.throwaway` ↦ `_`. -/
private def delabLValue : DelabM (Array Term) := do
  match (← getExpr).getAppFnArgs with
  | (``Setter.throwaway, _) => return #[← `(_)]
  | (``liftLens, args) => do
      guard (args.size == 5)
      withNaryArg 4 delabLValueList
  | _ => failure

/-- Is the current sub-expression the throwaway l-value (a `call` with no result)? -/
private def isThrowaway : DelabM Bool := return (← getExpr).isAppOf ``Setter.throwaway

/-- The elements of the comma list inside a printed tuple.  The tuple parser keeps the tail
of the list in a further `null` node (`(a, b, c)` is `a , ‹b , ‹c››`), so flatten those. -/
private partial def tupleElems (s : Syntax) : Array Term :=
  s.getSepArgs.flatMap fun e => if e.isOfKind nullKind then tupleElems e else #[⟨e⟩]

/-- Split a printed argument tuple back into an argument list.  Any split is sound: the
`call` macro re-tuples the list with `mkArgTuple`, which is exactly how tuples print. -/
private def splitArgTuple (stx : Term) : Array Term :=
  if stx.raw.isOfKind ``Lean.Parser.Term.tuple then tupleElems (stx.raw.getArg 1) else #[stx]

/-- The name a `let`/`have` binder prints under.  `have _ : T := v;` — the usual spelling of a
binder meant only for instance resolution — gets an inaccessible name from Lean (`x✝`), which is
not a name one can write; it prints as the `_` it was written as. -/
private def binderPrintName (nm : Name) : Name :=
  if nm.hasMacroScopes then `_ else nm

/-- Does `stx` mention this exact name?  Used on an inaccessible binder, whose printed name is
`_`: if the statements it carries refer to it after all, printing them would lose the reference,
so the delaborator steps aside instead.  The comparison keeps the macro scopes — erasing them
would confuse an inaccessible `x✝` with an ordinary variable `x` in the same scope. -/
private partial def syntaxHasExactIdent (n : Name) : Syntax → Bool
  | .ident _ _ v _ => v == n
  | .node _ _ args => args.any (syntaxHasExactIdent n)
  | _ => false

/-- Peel `n` `let`/`have` binders whose values satisfy `isOk`, then run `k` on the binder
names, inside the local context they introduce.  With `anon`, an inaccessible binder is peeled
too and reported under its printed name (see `binderPrintName`). -/
partial def withPeeledLets {α} [Inhabited α] (n : Nat) (isOk : Lean.Expr → Bool)
    (acc : Array Name) (k : Array Name → DelabM α) (anon : Bool := false) : DelabM α := do
  if n == 0 then k acc
  else
    match (← getExpr) with
    | .letE nm _ v _ _ => do
        guard (isOk v)
        guard <| anon || !nm.hasMacroScopes
        withLetBody (withPeeledLets (n - 1) isOk (acc.push (binderPrintName nm)) k anon)
    | _ => failure

private def isHoleIndex (v : Lean.Expr) : Bool :=
  v.isAppOf ``HoleIndex.zero || v.isAppOf ``HoleIndex.succ

/-- The `letDecl` node for `x : T := v`.  `letDecl` is a parser, not a syntax category, so
there is no `` `(letDecl| …) `` quotation for it; we quote a whole `let` term instead and
pick the declaration out of it. -/
private def mkLetDecl (x : Ident) (t v : Term) :
    DelabM (TSyntax ``Lean.Parser.Term.letDecl) := do
  let stx ← `(let $x : $t := $v; ())
  let some d := stx.raw.find? (·.isOfKind ``Lean.Parser.Term.letDecl) | failure
  return ⟨d⟩

/-! #### Program variables

A parameter or `var` of a `proc` (or of a `GaudiProg[ var …; ]`) is `letI`-bound, so the term
holds its slot `localVarLens "x" T` at every use and no binder.  To
print it under its name again, the delaborators

1. *collect* the slots of the frame — every such term with a literal name, outside nested
   `proc` literals (which are frames of their own and print their own variables), together
   with the parameters;
2. *decide* which of them print under their name: exactly one type per name (up to reducible
   defeq), a non-empty name without `»`, and no clash with a constant or a binder of the same
   name in the frame (a clashing name could not be told apart from the variable when parsing
   back);
3. *bind* each printable one to a let-variable of its name, replacing its slot by it, and print
   that term with the ordinary machinery, which shows the variable as `x` (`§x` when read).

A variable that is not printable keeps its slot, which prints as
`§(localVarLens "x" T)` and re-parses to the same term.  A parameter
that is not printable makes the `proc` delaborator step aside: the header has to name it.

`FrameVar`, `frameVars`, `withVarLocals`, `withExpr` and `varBinder` live in `ProgramSyntax` and
are not `private`: the `hoare[ ]` delaborator prints the frame of a statement triple the same
way. -/

namespace ProgramSyntax

/-- `localVarLens "x" T` ↦ `("x", T)`. -/
private def varSlot? (e : Lean.Expr) : Option (String × Lean.Expr) := do
  guard (e.isAppOfArity ``localVarLens 6)
  let .lit (.strVal n) := e.getArg! 1 | none
  return (n, e.getArg! 2)

/-- The variable slots in `e`, outside nested `proc` literals, in order of first occurrence,
each with its name and type. -/
private partial def collectVarSlots (e : Lean.Expr)
    (acc : Array (String × Lean.Expr × Lean.Expr)) : Array (String × Lean.Expr × Lean.Expr) :=
  if e.isAppOf ``ProcedureWithHoles.mk then acc
  else if let some (n, ty) := varSlot? e then
    if e.hasLooseBVars || acc.any (·.2.2 == e) then acc else acc.push (n, ty, e)
  else match e with
    | .app f a => collectVarSlots a (collectVarSlots f acc)
    | .lam _ t b _ | .forallE _ t b _ => collectVarSlots b (collectVarSlots t acc)
    | .letE _ t v b _ => collectVarSlots b (collectVarSlots v (collectVarSlots t acc))
    | .mdata _ b | .proj _ _ b => collectVarSlots b acc
    | _ => acc

/-- `e` with every subterm in `ts` replaced by `fv`, outside nested `proc` literals. -/
private partial def replaceVarSlots (ts : Array Lean.Expr) (fv : Lean.Expr) (e : Lean.Expr) :
    Lean.Expr :=
  if e.isAppOf ``ProcedureWithHoles.mk then e
  else if ts.contains e then fv
  else match e with
    | .app f a => .app (replaceVarSlots ts fv f) (replaceVarSlots ts fv a)
    | .lam n t b bi => .lam n (replaceVarSlots ts fv t) (replaceVarSlots ts fv b) bi
    | .forallE n t b bi => .forallE n (replaceVarSlots ts fv t) (replaceVarSlots ts fv b) bi
    | .letE n t v b nd =>
        .letE n (replaceVarSlots ts fv t) (replaceVarSlots ts fv v) (replaceVarSlots ts fv b) nd
    | .mdata d b => .mdata d (replaceVarSlots ts fv b)
    | .proj s i b => .proj s i (replaceVarSlots ts fv b)
    | e => e

/-- Does a constant or a binder in `e` carry the name `n`?  Then a variable `n` printed as an
identifier could not be told apart from it. -/
private def nameClashes (n : String) (e : Lean.Expr) : Bool :=
  (e.find? fun
    | .const c _ => match c with | .str _ s => s == n | _ => false
    | .lam nm .. | .forallE nm .. | .letE nm .. => nm.eraseMacroScopes == .str .anonymous n
    | _ => false).isSome

/-- A program variable of a frame: its name, its type, the occurrences of its slot, and whether
it prints under its name. -/
structure FrameVar where
  name : String
  type : Lean.Expr
  slots : Array Lean.Expr
  printable : Bool
  deriving Inhabited

/-- The program variables of the frame whose terms are `es`: the parameters `params` first (in
order), then every other variable whose slot occurs in `es`, in order of first occurrence. -/
def frameVars (es : Array Lean.Expr) (params : Array (String × Lean.Expr)) :
    MetaM (Array FrameVar) := do
  let mut vars : Array FrameVar := params.map fun (n, ty) => ⟨n, ty, #[], true⟩
  for (n, ty, t) in es.foldl (fun acc e => collectVarSlots e acc) #[] do
    match vars.findIdx? (·.name == n) with
    | some i =>
        let v := vars[i]!
        if ← Meta.withReducible (Meta.isDefEq v.type ty) then
          vars := vars.set! i { v with slots := v.slots.push t }
        else
          vars := vars.set! i { v with printable := false }
    | none => vars := vars.push ⟨n, ty, #[t], true⟩
  return vars.map fun v =>
    { v with printable := v.printable && !v.name.isEmpty && !v.name.contains '»'
                          && !es.any (nameClashes v.name) }

/-- Bind each variable of `vars` to a let-variable of its name, replace its slots in `es` by it,
and run `k` on the rewritten terms. -/
partial def withVarLocals {α} (vars : List FrameVar) (es : Array Lean.Expr)
    (k : Array Lean.Expr → DelabM α) : DelabM α :=
  match vars with
  | [] => k es
  | v :: rest => do
      let some t := v.slots[0]? | withVarLocals rest es k
      Meta.withLetDecl (.mkSimple v.name) (← Meta.inferType t) t fun fv =>
        withVarLocals rest (es.map (replaceVarSlots v.slots fv)) k

/-- Run `d` on `e` in place of the current expression. -/
def withExpr {α} (e : Lean.Expr) (d : DelabM α) : DelabM α :=
  withTheReader SubExpr (fun s => { s with expr := e }) d

/-- The binder `x : T` of a printable variable, as written after `var`. -/
def varBinder (v : FrameVar) : DelabM (TSyntax `proc_binder) := do
  `(proc_binder| $(mkIdent (.mkSimple v.name)):ident : $(← withExpr v.type delab))

end ProgramSyntax

open ProgramSyntax

/-- A local variable slot prints as `localVarLens "x" T`, which is how it is written (the key and
its proof are filled in by elaboration). -/
@[delab app.GaudisCrypt.localVarLens]
private def delabLocalVarLens : Delab := do
  guardSurfaceSyntax
  guard ((← getExpr).getAppNumArgs == 6)
  let f := mkIdent (← unresolveNameGlobal ``localVarLens)
  `($f $(← withNaryArg 1 delab) $(← withNaryArg 2 delab))

mutual

/-- A statement sequence: the right `seq` spine, flattened.  A Lean binder wrapping the rest
of the sequence (what a `let`/`have` statement elaborates to) becomes one statement carrying
that rest; `have` is the nondependent `let`, which is the only thing that tells the two apart
in the term. -/
partial def delabGaudiStmts (holeNames : Array Name) :
    DelabM (Array (TSyntax `gaudi_stmt)) := do
  if let .letE nm _ _ _ nonDep := (← getExpr) then
    let ty ← withLetVarType delab
    let val ← withLetValue delab
    let decl ← mkLetDecl (mkIdent (binderPrintName nm)) ty val
    let body ← withLetBody (delabGaudiStmts holeNames)
    -- an inaccessible binder prints as `_`, so the statements it carries must not name it
    guard <| !nm.hasMacroScopes || !body.any (syntaxHasExactIdent nm ·.raw)
    return #[← if nonDep then `(gaudi_stmt| have $decl:letDecl; $body:gaudi_stmt*)
               else `(gaudi_stmt| let $decl:letDecl; $body:gaudi_stmt*)]
  match (← getExpr).getAppFnArgs with
  | (``StmtWithHoles.seq, args) => do
      guard (args.size == 4)
      let hd ← withNaryArg 2 (delabGaudiStmtNested holeNames)
      let tl ← withNaryArg 3 (delabGaudiStmts holeNames)
      return #[hd] ++ tl
  | _ => return #[← delabGaudiStmt holeNames]

/-- A statement in the *left* position of a `seq`.  A `seq` there is printed as a block
`{ … }`, or re-parsing would re-associate it; so is a Lean binder, whose carried statement
list would otherwise be re-parsed greedily and swallow the rest of the enclosing sequence. -/
private partial def delabGaudiStmtNested (holeNames : Array Name) :
    DelabM (TSyntax `gaudi_stmt) := do
  if (← getExpr).isAppOf ``StmtWithHoles.seq || (← getExpr).isLet then
    let ss ← delabGaudiStmts holeNames
    `(gaudi_stmt| { $ss:gaudi_stmt* })
  else
    delabGaudiStmt holeNames

private partial def delabGaudiStmt (holeNames : Array Name) :
    DelabM (TSyntax `gaudi_stmt) := do
  match (← getExpr).getAppFnArgs with
  | (``StmtWithHoles.skip, _) => `(gaudi_stmt| skip;)
  | (``StmtWithHoles.assign, args) => do
      guard (args.size == 5)
      let lv ← withNaryArg 3 delabLValue
      let e ← withNaryArg 4 delabGaudiExpr
      `(gaudi_stmt| $lv:term,* <- $e;)
  | (``StmtWithHoles.sample, args) => do
      guard (args.size == 5)
      let lv ← withNaryArg 3 delabLValue
      let e ← withNaryArg 4 delabGaudiExpr
      `(gaudi_stmt| $lv:term,* <$ $e;)
  | (``StmtWithHoles.call, args) => do
      guard (args.size == 6)
      let void ← withNaryArg 3 isThrowaway
      let lv ← withNaryArg 3 delabLValue
      let p ← withNaryArg 4 delab
      let as := splitArgTuple (← withNaryArg 5 delabGaudiExpr)
      if void then `(gaudi_stmt| call $p ( $as:term,* );)
      else `(gaudi_stmt| $lv:term,* <- call $p ( $as:term,* );)
  | (``StmtWithHoles.hole, args) => do
      guard (args.size == 6)
      let idx ← withNaryArg 3 delab
      let void ← withNaryArg 4 isThrowaway
      let lv ← withNaryArg 4 delabLValue
      let as := splitArgTuple (← withNaryArg 5 delabGaudiExpr)
      -- inside its `proc`, a hole is called with `call` (that is what the macro rewrites);
      -- anywhere else the internal `holecall` form is the only faithful spelling.
      if idx.raw.isIdent && holeNames.contains idx.raw.getId then
        if void then `(gaudi_stmt| call $idx ( $as:term,* );)
        else `(gaudi_stmt| $lv:term,* <- call $idx ( $as:term,* );)
      else
        if void then `(gaudi_stmt| holecall $idx ( $as:term,* );)
        else `(gaudi_stmt| $lv:term,* <- holecall $idx ( $as:term,* );)
  | (``StmtWithHoles.ifThenElse, args) => do
      guard (args.size == 5)
      let c ← withNaryArg 2 delabGaudiExpr
      let t ← withNaryArg 3 (delabGaudiStmts holeNames)
      -- `if (c) { … }` elaborates with `skip` as its else branch, so print the short form
      let noElse ← withNaryArg 4 (return (← getExpr).isAppOf ``StmtWithHoles.skip)
      if noElse then `(gaudi_stmt| if ($c) { $t:gaudi_stmt* })
      else
        let f ← withNaryArg 4 (delabGaudiStmts holeNames)
        `(gaudi_stmt| if ($c) { $t:gaudi_stmt* } else { $f:gaudi_stmt* })
  | (``StmtWithHoles.while, args) => do
      guard (args.size == 4)
      let c ← withNaryArg 2 delabGaudiExpr
      let body ← withNaryArg 3 (delabGaudiStmts holeNames)
      `(gaudi_stmt| while ($c) { $body:gaudi_stmt* })
  | _ => failure

end

/-- Print a `StmtWithHoles` as `GaudiProg[ … ]`. -/
@[delab app.GaudisCrypt.StmtWithHoles.skip, delab app.GaudisCrypt.StmtWithHoles.assign,
  delab app.GaudisCrypt.StmtWithHoles.sample, delab app.GaudisCrypt.StmtWithHoles.call,
  delab app.GaudisCrypt.StmtWithHoles.hole, delab app.GaudisCrypt.StmtWithHoles.seq,
  delab app.GaudisCrypt.StmtWithHoles.ifThenElse, delab app.GaudisCrypt.StmtWithHoles.while]
private def delabGaudiProg : Delab := do
  guardSurfaceSyntax
  let vars := (← frameVars #[← getExpr] #[]).filter (·.printable)
  withVarLocals vars.toList #[← getExpr] fun es => do
    let stmts ← withExpr es[0]! (delabGaudiStmts #[])
    let locals ← vars.mapM varBinder
    if locals.isEmpty then `(GaudiProg[ $stmts:gaudi_stmt* ])
    else `(GaudiProg[ var $locals:proc_binder,* ; $stmts:gaudi_stmt* ])

/-- The names bound by the `let`/`have` statements on the spine of a printed statement
sequence, outermost first — exactly the binders `wrapSpineBinders` repeats around the return
value.  (`letI`/`haveI` inline during elaboration, so no binder of theirs is in either term.) -/
partial def spineLetNames (ss : Array (TSyntax `gaudi_stmt)) : Array Name := Id.run do
  for s in ss do
    match s with
    | `(gaudi_stmt| let $d:letDecl; $rest:gaudi_stmt*)
    | `(gaudi_stmt| have $d:letDecl; $rest:gaudi_stmt*) =>
        let n := match d.raw.find? (·.isIdent) with
          | some i => i.getId
          | none => Name.anonymous
        return #[n] ++ spineLetNames rest
    | _ => pure ()
  return #[]

/-- Print a procedure built by `proc` as `proc (…) uses (…) : R { … }`. -/
@[delab app.GaudisCrypt.ProcedureWithHoles.mk]
private def delabProc : Delab := do
  guardSurfaceSyntax
  let e ← getExpr
  guard (e.getAppNumArgs == 8)
  let (paramTys, retTy) ← withNaryArg 2 delabSigParts
  let holeSigs ← withNaryArg 1 delabHoleSigs
  let some paramNames := stringListLit? (e.getArg! 3) | failure
  let some paramTyEs := listLitElems? ((e.getArg! 2).getArg! 0) | failure
  guard (paramNames.size == paramTyEs.size)
  -- the program variables, parameters first; the header has to name every parameter
  let vars ← frameVars #[e.getArg! 6, e.getArg! 7] (paramNames.zip paramTyEs)
  guard ((vars.extract 0 paramNames.size).all (·.printable))
  let printable := vars.filter (·.printable)
  withVarLocals printable.toList #[e.getArg! 6, e.getArg! 7] fun es => do
    -- the body: the hole `let`s, then the statements
    let (holeNames, stmts) ← withExpr es[0]! <|
      withPeeledLets holeSigs.size isHoleIndex #[] fun hs => do
        return (hs, ← delabGaudiStmts hs)
    -- the return value repeats the binders on the body's spine, which scope over it too
    let spineNames := spineLetNames stmts
    let (retSpine, ret) ← withExpr es[1]! <|
      withPeeledLets spineNames.size (fun _ => true) #[] (anon := true) fun bs => do
        return (bs, ← delabGaudiExpr)
    guard (retSpine == spineNames)
    let params ← (paramNames.zip paramTys).mapM fun (n, t) =>
      `(proc_binder| $(mkIdent (.mkSimple n)):ident : $t)
    let locals ← (printable.extract paramNames.size printable.size).mapM varBinder
    let holes ← (holeNames.zip holeSigs).mapM fun (n, (ps, r)) =>
      `(hole_binder| $(mkIdent n):ident : ( $ps:term,* ) → $r)
    let varLines : Array (Syntax.TSepArray `proc_binder ",") :=
      if locals.isEmpty then #[] else #[locals]
    if holes.isEmpty then
      `(proc ( $params:proc_binder,* ) : $retTy {
          $[var $varLines:proc_binder,* ;]*
          $stmts:gaudi_stmt*
          return $ret })
    else
      `(proc ( $params:proc_binder,* ) uses ( $holes:hole_binder,* ) : $retTy {
          $[var $varLines:proc_binder,* ;]*
          $stmts:gaudi_stmt*
          return $ret })

end Printing

end GaudisCrypt

-- TODO: Allow _ inside a *tuple* lvalue too (a bare `_` already becomes Setter.throwaway)
--   (see "L-value pairing" below)
-- TODO: Allow `(x,y) <- ...` where x is a global and y is a local var
--   (see "L-value pairing" below)

/- ### L-value pairing — diagnosis for the two l-value TODOs above

The two are one gap, in `[lvalRaw|]`/`[lvalRawList|]`/`[lval|]` near the top of this file.
`[lval| xs,*]` expands to `liftLens [lvalRawList| xs,*]`: the components are **paired first and
lifted second**.  So `Lens.pair` sees the raw components, and must find two `Lens`es in one
and the same container, while `LiftLens` resolves exactly once, on the finished pair.

Hence:

* a mixed tuple fails to elaborate.  `(x, y) <- …` with `x` a local and `y : Lens Int State`
  gives

      Application type mismatch: The argument
        y
      has type
        Lens ℤ State
      but is expected to have type
        Lens ℤ ProgramState
      in the application
        @Lens.pair ℤ ProgramState ℤ x y

  All-global works (`LiftLens State` lifts the pair with `Lens.intoGlobal`) and all-local
  works (`LiftLens ProgramState` keeps it), because there the two components already agree; a
  mixed pair has no single `M` for the class to be resolved at.  Lifting the global by hand,
  `(x, y.intoGlobal) <- …`, works (the disjointness instance
  `Lens.disjoint_intoLocal_intoGlobal` exists) and round-trips.
* `_` works only at the top level.  `[lval| _]` short-circuits to `Setter.throwaway`, but a `_`
  *inside* a tuple goes through `[lvalRaw| _]` into `Lens.pair`, which wants a `Lens` — and a
  throwaway is a `Setter`, deliberately (it has no getter).

Two ways out:

1. Pair at the `Setter` level: lift each leaf with `liftLens` and combine with a `Setter.pair`
   (which does not exist yet).  This fixes both TODOs at once — `Setter.throwaway` is already a
   `Setter`, so a `_` leaf needs no special case — at the cost of stating the disjointness side
   condition for setters rather than for lenses.
2. Lift each leaf into `ProgramState` and keep pairing lenses there.  Needs a `Lens`-valued
   variant of `LiftLens` (`LiftLens.lift` currently lands in `Setter`); the disjointness
   instances between `Lens.intoGlobal` and `Lens.intoLocal` lenses exist.  This is what the
   hand-written `y.intoGlobal` above does.  It does not fix the `_` TODO.

Either way the delaborators have to follow, or printing stops round-tripping: `delabLValue`
matches `liftLens` at the root of an l-value and `delabLValueList`/`delabLValueComponent` walk
the `Lens.pair` spine underneath it. -/
