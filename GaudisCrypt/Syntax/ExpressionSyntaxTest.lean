import GaudisCrypt.Syntax.ExpressionSyntax

/-! # Tests for `ExpressionSyntax` -/

/-! ## Experiments for expressions -/

namespace GaudisCrypt.Test

open GaudisCrypt

-- set_option trace.Meta.synthInstance true

axiom a : Lens Nat VariableAssignment
axiom b : Lens Nat VariableAssignment

-- global variables
#check (GaudiExpr[ $a + 1 ] : Getter Nat ProgramState)
#check (GaudiExpr[ $a + $b ] : Getter Nat ProgramState)

-- a full-current-state lens (e.g. a local variable already lifted)
axiom loc : Lens Nat ProgramState
#check (GaudiExpr[ $a + $loc ] : Getter Nat ProgramState)
noncomputable def test := (GaudiExpr[ $a + $loc ] : Getter Nat ProgramState)
#print test

-- $(...) for a compound lens term
#check (GaudiExpr[ $(a) + 1 ] : Getter Nat ProgramState)

-- reduction: expressions compute through to plain lens reads
example (st : ProgramState) :
    (GaudiExpr[ $a + 1 ] : Getter Nat ProgramState).get st = a.get st.globals + 1 := by
  simp

example (st : ProgramState) :
    (GaudiExpr[ $a + $loc ] : Getter Nat ProgramState).get st
      = a.get st.globals + loc.get st := by
  simp

end GaudisCrypt.Test
