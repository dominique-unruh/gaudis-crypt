import GaudisCrypt.Syntax.ExpressionSyntax
import GaudisCrypt.Syntax.ProgramSyntax
import GaudisCrypt.Syntax.ModuleSyntax
import GaudisCrypt.Syntax.HoareSyntax
import GaudisCrypt.Syntax.PHoareSyntax
import GaudisCrypt.Syntax.ModuleApplicationSyntax
import GaudisCrypt.Syntax.PrSyntax

/-! # Concrete syntax

Barrel module for the surface syntax of the language: expressions
(`ExpressionSyntax.lean`), statements and procedures (`ProgramSyntax.lean`), modules
(`ModuleSyntax.lean`), EasyCrypt's module paths `M(A, B).f` (`ModuleApplicationSyntax.lean`),
Hoare triples (`HoareSyntax.lean`, `PHoareSyntax.lean`) and probabilities `Pr[ M (a) @ &m : E ]`
(`PrSyntax.lean`).

`HoareSyntax.lean` is the one file here that reaches past `Language/` — `hoareStmt` and
`hoareProc` themselves live in `Logic/Hoare.lean` — so this barrel pulls that in too.  It also
imports its sibling `ModuleSyntax.lean`, the procedure-triple form being about a module. -/
