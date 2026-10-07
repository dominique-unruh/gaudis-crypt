import GaudisCrypt.Language.Programs

open GaudisCrypt

/-!
# Concrete syntax for expressions

Surface syntax for the expressions of the imperative probabilistic language; see
`syntax-ideas.md` for design notes.

## Expressions — `GaudiExpr[ e ]`

Wraps a Lean expression `e` as a program expression.  Inside, the `$` sigil reads program
variables:
* `$x`   — the value of program variable / lens `x`;
* `$(e)` — the value of an arbitrary lens-valued term `e`.

e.g. `GaudiExpr[ $a + $b * 2 ]`.  Every expression position in a statement is already an
`GaudiExpr`, so `$` may be used directly there (see `ProgramSyntax.lean`).

`§x` is a second spelling of `$x`, with the same meaning.  It exists because it can be
*printed*: `$x` parses as a Lean antiquotation node, and antiquotation nodes cannot be
pretty-printed (`$a + 1` fails to format), so `§x` is what the delaborators emit.
-/

namespace GaudisCrypt

open Lean

/-! ## Ambient current state + variable evaluation

An expression of value type `T` is a `Getter T ProgramState`.  Inside the body we make the
current state available via the typeclass `CurrentState`, so a program variable `x` (a
lens/getter) can be read as a plain value with `eval x`.  `eval` accepts both global variables
(into the globals, a `VariableAssignment`) and full-current-state variables (into
`ProgramState`, e.g. locals lifted with `Lens.intoLocal`); dispatch is on the concrete type of
the argument (see `Evaluatable`). -/

/-- The ambient current state. -/
class CurrentState where
  state : ProgramState

/-- Anything that can be read to a value `T` in the ambient `CurrentState`: program variables
(lenses/getters into the globals `VariableAssignment`, or into the full `ProgramState`), and
anything users later add instances for.  Dispatch is on the concrete type `X` of the argument, so
resolution is never stuck on a metavariable. -/
class Evaluatable (X : Type u) (T : outParam Type) where
  eval : ProgramState → X → T

/-- User-facing variable read in the ambient `CurrentState`. -/
def eval {X : Type u} {T} [Evaluatable X T] [cs : CurrentState] (x : X) : T :=
  Evaluatable.eval cs.state x

/-- The four container shapes, dispatched directly on the argument type.  (No
`Lens → Getter` forwarder: it would overlap these, so we spell out all four.) -/
instance : Evaluatable (Getter T VariableAssignment) T where
  eval cs x := x.get cs.globals
instance : Evaluatable (Getter T ProgramState) T where
  eval cs x := x.get cs
-- TODO: Needed? (We have Lens->Setter coercion)
instance : Evaluatable (Lens T VariableAssignment) T where
  eval cs x := x.get cs.globals
-- TODO: Needed? (We have Lens->Setter coercion)
instance : Evaluatable (Lens T ProgramState) T where
  eval cs x := x.get cs

/-! ## Reduction lemmas (so denotations compute)

`simp` reduces all four cases (global/full × getter/lens) to a plain `.get` read. -/

@[simp] theorem eval_getter_global [cs : CurrentState] (x : Getter T VariableAssignment) :
    eval x = x.get cs.state.globals := rfl

@[simp] theorem eval_getter_full [cs : CurrentState] (x : Getter T ProgramState) :
    eval x = x.get cs.state := rfl

@[simp] theorem eval_lens_global [cs : CurrentState] (x : Lens T VariableAssignment) :
    eval x = x.get cs.state.globals := rfl

@[simp] theorem eval_lens_full [cs : CurrentState] (x : Lens T ProgramState) :
    eval x = x.get cs.state := rfl

/-! ## Sigil syntax for expressions

The `$` sigil is parsed by Lean as a (pseudo) antiquotation node; we intercept
those nodes inside the `GaudiExpr[ ]` macro and rewrite `$e` to `eval e`.

`$x`             ↦ `eval x`     (variable reference)
`$(e)`           ↦ `eval e`     (arbitrary lens-valued term as a variable)
`GaudiExpr[ e ]` wraps an expression body `e` into a `Getter _ ProgramState`, making
the ambient `CurrentState` available inside `e`. -/

/-- Replace every `$e` (antiquotation) leaf in `stx` by `eval e`. -/
private def fixExpr (stx : Syntax) : MacroM Syntax :=
  stx.replaceM fun s => do
    if s.isAntiquot then
      let inner : Term := ⟨s.getAntiquotTerm⟩
      some <$> `(eval $inner)
    else
      pure none

-- the atoms carry pretty-printing spaces (`GaudiExpr[ e ]`); tokenization ignores them, so
-- `GaudiExpr[e]` still parses
scoped macro:max "GaudiExpr[ " e:term " ]" : term => do
  let e' : Term := ⟨← fixExpr e⟩
  `(Getter.mk (fun st => letI : CurrentState := ⟨st⟩; $e'))

/-! ### The printable sigil `§`

`$x` is an antiquotation node, which Lean's formatter cannot print (it fails inside infix
operators, so `$a + 1` would be unprintable).  `§x` means exactly the same — it expands to
`eval x` just like `$x` does — but is an ordinary piece of syntax, so it both parses and
prints.  The `eval` unexpander turns every variable read back into it. -/

/-- `§x` — the value of program variable / lens `x` in the ambient `CurrentState`; the
printable spelling of `$x`. -/
syntax:max "§" noWs term:max : term

macro_rules | `(§$x:term) => `(eval $x)

open Lean PrettyPrinter in
@[app_unexpander GaudisCrypt.eval]
def unexpandEval : Unexpander
  | `($_ $x) => `(§$x)
  | _ => throw ()

end GaudisCrypt
