import GaudisCrypt.Language.Programs

/-!
Concrete syntax for programs and procedures
-/

namespace GaudisCrypt.Language.Syntax

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Programs


/- # Syntax of programs -/

declare_syntax_cat gaudi_stmt
declare_syntax_cat gaudi_block
declare_syntax_cat gaudi_var

syntax (name := gaudi_var_single) ident : gaudi_var
syntax (name := gaudi_var_nary) "( " ident (", " ident)* " )" : gaudi_var
syntax gaudi_var " <- " term ";" : gaudi_stmt
syntax gaudi_var " <@ " "[" term "]" term ";" : gaudi_stmt  -- TODO: Funny syntax! Fix!
syntax gaudi_var " <$ " term ";" : gaudi_stmt
syntax "{" gaudi_stmt* "}" : gaudi_stmt
syntax "if" "(" term ")" gaudi_stmt ( "else" gaudi_stmt )? : gaudi_stmt
syntax "while" "(" term ")" gaudi_stmt : gaudi_stmt
syntax "[ec|" gaudi_stmt "]" : term
syntax "[var|" gaudi_var "]" : term
syntax "[expr|" term "]" : term

/-- Translates a term `t` to use $-notation for Lens use.
  Specifically, replaces all occurrences of `$name` by `name.get st`,
  and wraps the whole in `fun st => ...`
-/
private def fixExpression (t : Lean.TSyntax `term) : Lean.MacroM Lean.Syntax := do
  let st <- `(st)
  let t' : Lean.TSyntax `term <- t.replaceM fun subterm => do
    if subterm.isAntiquot ∧ (toString subterm[0] == "\"$\"") then
      let id := subterm[2]
      if id.isIdent then
        let id' := Lean.mkIdent id.getId
        Lean.Macro.trace `grind "ANTI"
        let newTerm <- `(($(id').get $st))
        return some newTerm
      else
        return none
    else
      return none
  `(Getter.mk fun $st => $t')

macro_rules
  | `([expr| $t:term]) => fixExpression t
  | `([ec| $x:gaudi_var <- $e:term;]) => `(StmtWithHoles.assign [var| $x] [expr| $e])
  | `([ec| $x:gaudi_var <$ $e:term;]) => `(StmtWithHoles.sample [var| $x] [expr| $e])
  | `([ec| $x:gaudi_var <@ [ $e:term ] $f:term;]) => `(StmtWithHoles.call [var| $x] [expr| $e] [expr| $f])
  | `([ec| if ($b) $t:gaudi_stmt else $e:gaudi_stmt]) =>
      `(StmtWithHoles.ifThenElse [expr| $b] [ec| $t] [ec| $e])
  | `([ec| if ($b) $t:gaudi_stmt]) =>
      `(StmtWithHoles.ifThenElse [expr| $b] [ec| $t] StmtWithHoles.skip)
  | `([ec| while ($b) $body:gaudi_stmt]) =>
     `(StmtWithHoles.while [expr| $b] [ec| $body])
  | `([ec| {}]) => `(StmtWithHoles.skip)
  | `([ec| { $s }]) => `([ec| $s])
  | `([ec| { $s $ss* }]) => `(StmtWithHoles.seq [ec| $s] [ec| { $ss* }])
  | `([var| $id:ident]) => `($id)
  -- TODO: [var| (x,y,z)] translation for tuples of lenses


/- # Experiments -/

section huhu

variable [ProgramSpec]

axiom x : Lens Nat State
axiom a : Lens Nat State
axiom b : Lens Nat State


-- def $a := 5

#check [expr| $a + 1]

-- TODO fix
noncomputable
def example_program := [ec|
if ($x.ofst == 1) { a.ofst <- 1; b.ofst <- 2; } else {}
]

#print example_program
