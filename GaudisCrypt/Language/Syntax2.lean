import GaudisCrypt.Language.Programs

/-!
Concrete syntax for programs and procedures — take 2.

This file currently implements ONLY the expression layer (sigil `$`), standalone,
without any program/procedure syntax yet. See `syntax-ideas.md` for the design.
-/

namespace GaudisCrypt.Language.Syntax

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Programs
open Lean

variable [ProgramSpec]

/-! ## Ambient current state + variable evaluation

An expression of value type `T` living in a statement with local-state `l` is a
`Getter T (State × l)`.  Inside the body we make the current state available via a
typeclass `CurrentState l`, so a program variable `x` (a lens) can be read as a
plain value with `eval x`.  `eval` accepts both global lenses (`Getter _ State`)
and full-current-state lenses (`Getter _ (State × l)`); `Project` dispatches on the
*head* of the container, which is unambiguous because `State` is a concrete head. -/

/-- The ambient current state.  The local-state type `L` is a *field*, not a type
index, so `[CurrentState]` always resolves (no metavar-indexed instance search),
and nested `letI`s shadow lexically. -/
class CurrentState where
  L : Type
  state : State × L

/-- Internal helper: how to project the ambient `State × l` onto a variable's
container `m` (`State` for a global, `State × l` for a full-state variable).  Not
part of the public interface — only the `Getter` `Evaluatable` instance uses it.
Keeping the container `m` out of the `Evaluatable` head (it lives here instead)
lets `CurrentState` be synthesized *before* this `State`-vs-`State×L` dispatch, so
`cs.L` is already known and resolution never gets stuck. -/
class Project (m : Type) (l : Type) where
  project : State × l → m

instance : Project State l where project := Prod.fst
instance : Project (State × l) l where project := id

/-- Anything that can be read to a value `T` in the ambient `CurrentState`:
program variables (lenses/getters into `State`, or into the full `State × L`), and
anything users later add instances for.  Dispatch is on the concrete type `X` of
the argument, so resolution is never stuck on a metavariable. -/
class Evaluatable (X : Type) (T : outParam Type) where
  eval : X → T

export Evaluatable (eval)

/-- A getter into either `State` or `State × L`; the container dispatch is handled
by `Project` (after `CurrentState` is synthesized). -/
instance [cs : CurrentState] [p : Project m cs.L] : Evaluatable (Getter T m) T where
  eval x := x.get (p.project cs.state)

/-- A `Lens` is evaluated as its underlying `Getter` (one forwarder covers both
container shapes). -/
instance [Evaluatable (Getter T m) T] : Evaluatable (Lens T m) T where
  eval x := eval x.toGetter

/-! ## Reduction lemmas (so denotations compute)

`simp` reduces the global and lens cases.  The full-state case (`eval_getter_full`)
does not reliably fire as a `simp` lemma yet — the `cs.L` in its hypothesis type
blocks matching — so general expressions currently reduce by `rfl`/`decide` instead.
Tightening this into a robust `simp` set is follow-up work. -/

@[simp] theorem eval_getter_global [cs : CurrentState] (x : Getter T State) :
    eval x = x.get cs.state.1 := rfl

@[simp] theorem eval_getter_full [cs : CurrentState] (x : Getter T (State × cs.L)) :
    eval x = x.get cs.state := rfl

omit [ProgramSpec] in
@[simp] theorem eval_lens [Evaluatable (Getter T m) T] (x : Lens T m) :
    eval x = eval x.toGetter := rfl

/-! ## Sigil syntax for expressions

The `$` sigil is parsed by Lean as a (pseudo) antiquotation node; we intercept
those nodes inside the `E[ ]` macro and rewrite `$e` to `eval e`.

`$x`     ↦ `eval x`         (variable reference)
`$(e)`   ↦ `eval e`         (arbitrary lens-valued term as a variable)
`E[ e ]` wraps an expression body `e` into a `Getter _ (State × l)`, making the
ambient `CurrentState` available inside `e`. -/

/-- Replace every `$e` (antiquotation) leaf in `stx` by `eval e`. -/
private def fixExpr (stx : Syntax) : MacroM Syntax :=
  stx.replaceM fun s => do
    if s.isAntiquot then
      let inner : Term := ⟨s.getAntiquotTerm⟩
      some <$> `(eval $inner)
    else
      pure none

scoped macro:max "E[" e:term "]" : term => do
  let e' : Term := ⟨← fixExpr e⟩
  `(Getter.mk (fun st => letI : CurrentState := ⟨_, st⟩; $e'))

end GaudisCrypt.Language.Syntax

/-! ## Experiments -/

namespace GaudisCrypt.Language.Syntax.Test

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Programs
open GaudisCrypt.Language.Syntax

variable [ProgramSpec]

axiom a : Lens Nat State
axiom b : Lens Nat State

-- a global variable, full state has trivial locals
#check (E[ $a + 1 ] : Getter Nat (State × Unit))
#check (E[ $a + $b ] : Getter Nat (State × Unit))
noncomputable def test := (E[ $a + $b ] : Getter Nat (State × Unit))
#print test

-- a full-current-state lens (e.g. a local variable already lifted)
axiom loc : Lens Nat (State × Unit)
#check (E[ $a + $loc ] : Getter Nat (State × Unit))

-- $(...) for a compound lens term
#check (E[ $(a) + 1 ] : Getter Nat (State × Unit))

-- reduction: expressions compute through to plain lens reads
example (st : State × Unit) :
    (E[ $a + 1 ] : Getter Nat (State × Unit)).get st = a.get st.1 + 1 := by
  simp

example (st : State × Unit) :
    (E[ $a + $loc ] : Getter Nat (State × Unit)).get st = a.get st.1 + loc.get st := by
  rfl

end GaudisCrypt.Language.Syntax.Test
