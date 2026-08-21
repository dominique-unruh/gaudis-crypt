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
-/

namespace GaudisCrypt

open Lean

variable [ProgramSpec]

/-! ## Ambient current state + variable evaluation

An expression of value type `T` living in a statement with local-state `S` is a
`Getter T (State × S)`.  Inside the body we make the current state available via the
typeclass `CurrentState S`, so a program variable `x` (a lens/getter) can be read as
a plain value with `eval x`.  `eval` accepts both global variables (into `State`)
and full-current-state variables (into `State × S`); dispatch is on the concrete
type of the argument (see `Evaluatable`). -/

/-- The ambient current state `State × S`.  The local-state type `S` is an
`outParam`: `[CurrentState S]` resolves by reading off the ambient state's type, so
`S` need not be known up front — this is what lets a *global* variable, whose type
says nothing about `S`, still be evaluated. -/
class CurrentState (S : outParam Type) where
  state : ProcedureState S

/-- Anything that can be read to a value `T` in the ambient `CurrentState S`:
program variables (lenses/getters into `State`, or into the full `ProcedureState S`), and
anything users later add instances for.  Dispatch is on the concrete type `X` of
the argument, so resolution is never stuck on a metavariable. -/
class Evaluatable (S : Type) (X : Type) (T : outParam Type) where
  eval : ProcedureState S → X → T

/-- User-facing variable read, with `S` implicit (inferred from the variable's
container in the full case, from the ambient `CurrentState` in the global case).
Pass `(S := …)` to force a particular state. -/
def eval {S X T} [Evaluatable S X T] [cs : CurrentState S] (x : X) : T :=
  Evaluatable.eval cs.state x

/-- The four container shapes, dispatched directly on the argument type.  (No
`Lens → Getter` forwarder: it would overlap these, so we spell out all four.) -/
instance : Evaluatable S (Getter T State) T where
  eval cs x := x.get cs.global
instance : Evaluatable S (Getter T (ProcedureState S)) T where
  eval cs x := x.get cs
-- TODO: Needed? (We have Lens->Setter coercion)
instance : Evaluatable S (Lens T State) T where
  eval cs x := x.get cs.global
-- TODO: Needed? (We have Lens->Setter coercion)
instance : Evaluatable S (Lens T (ProcedureState S)) T where
  eval cs x := x.get cs

/-! ## Reduction lemmas (so denotations compute)

`simp` reduces all four cases (global/full × getter/lens) to a plain `.get` read.
Making `S` a real parameter (rather than a `cs.L` projection) is what lets the
full-state lemmas match under `simp`. -/

@[simp] theorem eval_getter_global [cs : CurrentState S] (x : Getter T State) :
    eval x = x.get cs.state.global := rfl

@[simp] theorem eval_getter_full [cs : CurrentState S] (x : Getter T (ProcedureState S)) :
    eval x = x.get cs.state := rfl

@[simp] theorem eval_lens_global [cs : CurrentState S] (x : Lens T State) :
    eval x = x.get cs.state.global := rfl

@[simp] theorem eval_lens_full [cs : CurrentState S] (x : Lens T (ProcedureState S)) :
    eval x = x.get cs.state := rfl

/-! ## Sigil syntax for expressions

The `$` sigil is parsed by Lean as a (pseudo) antiquotation node; we intercept
those nodes inside the `GaudiExpr[ ]` macro and rewrite `$e` to `eval e`.

`$x`             ↦ `eval x`     (variable reference)
`$(e)`           ↦ `eval e`     (arbitrary lens-valued term as a variable)
`GaudiExpr[ e ]` wraps an expression body `e` into a `Getter _ (State × S)`, making
the ambient `CurrentState` available inside `e`. -/

/-- Replace every `$e` (antiquotation) leaf in `stx` by `eval e`. -/
private def fixExpr (stx : Syntax) : MacroM Syntax :=
  stx.replaceM fun s => do
    if s.isAntiquot then
      let inner : Term := ⟨s.getAntiquotTerm⟩
      some <$> `(eval $inner)
    else
      pure none

scoped macro:max "GaudiExpr[" e:term "]" : term => do
  let e' : Term := ⟨← fixExpr e⟩
  `(Getter.mk (fun st => letI : CurrentState _ := ⟨st⟩; $e'))

end GaudisCrypt
