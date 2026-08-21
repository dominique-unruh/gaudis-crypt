import GaudisCrypt.Syntax.ExpressionSyntax

/-! # Tests for `ExpressionSyntax` -/

/-! ## Experiments for expressions -/

namespace GaudisCrypt.Test

open GaudisCrypt

variable [ProgramSpec]

-- set_option trace.Meta.synthInstance true

axiom a : Lens Nat State
axiom b : Lens Nat State

-- a global variable, full state has trivial locals
#check (GaudiExpr[ $a + 1 ] : Getter Nat (ProcedureState Unit))
#check (GaudiExpr[ $a + $b ] : Getter Nat (ProcedureState Unit))

-- a full-current-state lens (e.g. a local variable already lifted)
axiom loc : Lens Nat (ProcedureState Unit)
#check (GaudiExpr[ $a + $loc ] : Getter Nat (ProcedureState Unit))
noncomputable def test := (GaudiExpr[ $a + $loc ] : Getter Nat (ProcedureState Unit))
#print test

-- $(...) for a compound lens term
#check (GaudiExpr[ $(a) + 1 ] : Getter Nat (ProcedureState Unit))

-- reduction: expressions compute through to plain lens reads
example (st : ProcedureState Unit) :
    (GaudiExpr[ $a + 1 ] : Getter Nat (ProcedureState Unit)).get st = a.get st.global + 1 := by
  simp

example (st : ProcedureState Unit) :
    (GaudiExpr[ $a + $loc ] : Getter Nat (ProcedureState Unit)).get st
      = a.get st.global + loc.get st := by
  simp

end GaudisCrypt.Test
