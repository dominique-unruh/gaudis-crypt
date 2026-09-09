import GaudisCrypt.Language.ModuleExpressionBasics

/-! # Confluence of module-expression reduction

The two open facts about `ModuleExpression.MultiStepReduction` that everything downstream of
`reduce` rests on: reduction is confluent (stuck reducts are unique), and termination is
invariant along it.  Split off from `ModuleExpressionBasics.lean` so the syntax, typing,
reduction and normal-form development there stays independent of them;
`ModuleExpression.lean` is where their consequences live. -/

namespace GaudisCrypt

variable [ProgramSpec]

namespace ModuleExpression

theorem multiStepReduction_confluence {m n1 n2 : ModuleExpression}
  (_ : m.MultiStepReduction n1) (_ : m.MultiStepReduction n2)
  (_ : n1.Stuck) (_ : n2.Stuck) :
  n1 = n2 := by
  sorry

theorem multiStepReduction_terminating {m n} (h : m.MultiStepReduction n) :
    Terminating m ↔ Terminating n := by
  sorry

end ModuleExpression

end GaudisCrypt
