import GaudisCrypt.Syntax.ExpressionSyntax
import GaudisCrypt.Syntax.ProgramSyntax
import GaudisCrypt.Syntax.ModuleSyntax
import GaudisCrypt.Syntax.HoareSyntax

/-! # Concrete syntax

Barrel module for the surface syntax of the language: expressions
(`ExpressionSyntax.lean`), statements and procedures (`ProgramSyntax.lean`), modules
(`ModuleSyntax.lean`), and Hoare triples (`HoareSyntax.lean`).

`HoareSyntax.lean` is the one file here that reaches past `Language/` — `hoareStmt` itself lives
in `Logic/Hoare.lean` — so this barrel pulls that in too. -/
