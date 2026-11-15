import GaudisCrypt.Syntax.ModuleVar

/-!
# Tests of `module_var`

A module variable of a theory whose type is one of the theory's types, and one whose type depends
on an operator of the theory (EC's `var qs : rand list` with `rand` the words of length `l`, `l`
an operator: `br93.ec`'s instance).
-/

namespace GaudisCrypt.ModuleVarTest

open GaudisCrypt

/-- A theory with a type and an operator. -/
class Params (α : outParam Type) where
  /-- An operator the type `word` depends on. -/
  n : ℕ
  /-- Another operator. -/
  op : α → α

variable {α : Type} [Inhabited α] [Params α]

/-- A type of the theory that depends on its operator `n`. -/
abbrev word : Type := Fin (Params.n (α := α) + 1)

module_var M.x : α

module_var M.w : List (word (α := α))

-- used alone, as EC's `M.x`: the instance in scope gives the types
noncomputable example : Lens α VariableAssignment := M.x

noncomputable example : Lens (List (word (α := α))) VariableAssignment := M.w

example : Lens.IsGlobalVar (M.w : Lens (List (word (α := α))) VariableAssignment)
    (VariableName.mk "GaudisCrypt.ModuleVarTest.M.w" (List (word (α := α)))) := inferInstance

end GaudisCrypt.ModuleVarTest
