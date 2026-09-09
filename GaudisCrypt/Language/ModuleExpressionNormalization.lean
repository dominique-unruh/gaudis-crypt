import GaudisCrypt.Language.ModuleExpressionBasics

/-! # Normalization for module expressions

Weak normalization: every well-typed module expression terminates.  Split off from
`ModuleExpressionBasics.lean` (which develops syntax, typing, reduction and normal forms
without it) so that this — the other deep open fact besides confluence — stands on its own;
`ModuleExpression.lean` collects the consequences. -/

namespace GaudisCrypt

variable [ProgramSpec]

namespace ModuleExpression

theorem HasType.terminating {m Δ T} (h : m.HasType Δ T) : Terminating m := by
  sorry

end ModuleExpression

end GaudisCrypt
