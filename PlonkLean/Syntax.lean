

/- # Syntax of programs -/

declare_syntax_cat ec_stmt
declare_syntax_cat ec_block
declare_syntax_cat ec_var

syntax (name := ec_var_single) ident : ec_var
syntax (name := ec_var_nary) "( " ident (", " ident)* " )" : ec_var
syntax ec_var " <- " term ";" : ec_stmt
syntax ec_var " <@ " "[" term "]" term ";" : ec_stmt  -- TODO: Funny syntax! Fix!
syntax ec_var " <$ " term ";" : ec_stmt
syntax "{" ec_stmt* "}" : ec_stmt
syntax "if" "(" term ")" ec_stmt ( "else" ec_stmt )? : ec_stmt
syntax "while" "(" term ")" ec_stmt : ec_stmt
syntax "[ec|" ec_stmt "]" : term
syntax "[var|" ec_var "]" : term
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
  `(fun $st => $t')

macro_rules
  | `([expr| $t:term]) => fixExpression t
  | `([ec| $x:ec_var <- $e:term;]) => `(Stmt.assign [var| $x] [expr| $e])
  | `([ec| $x:ec_var <$ $e:term;]) => `(Stmt.sample [var| $x] [expr| $e])
  | `([ec| $x:ec_var <@ [ $e:term ] $f:term;]) => `(Stmt.call [var| $x] [expr| $e] [expr| $f])
  | `([ec| if ($b) $t:ec_stmt else $e:ec_stmt]) =>
      `(Stmt.ifThenElse [expr| $b] [ec| $t] [ec| $e])
  | `([ec| if ($b) $t:ec_stmt]) =>
      `(Stmt.ifThenElse [expr| $b] [ec| $t] Stmt.skip)
  | `([ec| while ($b) $body:ec_stmt]) =>
     `(Stmt.while [expr| $b] [ec| $body])
  | `([ec| {}]) => `(Stmt.skip)
  | `([ec| { $s }]) => `([ec| $s])
  | `([ec| { $s $ss* }]) => `(Stmt.seq [ec| $s] [ec| { $ss* }])
  | `([var| $id:ident]) => `($id)
  -- TODO: [var| (x,y,z)] translation for tuples of lenses

private def StmtWithHoles.mySize [ProgramSpec] : StmtWithHoles h → ℕ
  | .skip => 0
  | .assign _ _ => 0
  | .sample _ _ => 0
  | .call' _ b _ _ => b.mySize + 1
  | .hole _ _ _ => 0
  | .seq p q => p.mySize + q.mySize + 1
  | .ifThenElse _ t e => t.mySize + e.mySize + 1
  | .while _ t => t.mySize + 1

instance [ProgramSpec] : SizeOf (StmtWithHoles h) where
  sizeOf := StmtWithHoles.mySize

@[reducible]
instance [ProgramSpec] : SizeOf Stmt := instSizeOfStmtWithHoles

noncomputable
def denotation [ProgramSpec] : Stmt → Program State Unit
| .skip => do return ()
| .assign x e => do let st ← Program.get_state; let result := e.get st; Program.set x result
| .sample x e => do
    let st ← Program.get_state
    let result ← (e.get st).toProgram
    Program.set x result
| .call' x b r p => do
    let st₀ ← Program.get_state
    let params := p.get st₀ -- WARNING ignored
    denotation b
    let st₁ ← Program.get_state
    let result := r.get st₁
    Program.set x result
| .ifThenElse c t e => do
    let st ← Program.get_state
    let result := c.get st
    if result then denotation t else denotation e
| .while c t => while_loop (do let st ← Program.get_state; return c.get st) (denotation t)
| .seq p q => do denotation p; denotation q
termination_by stmt => sizeOf (self := instSizeOfStmt) stmt
decreasing_by
  all_goals simp only [SizeOf.sizeOf, StmtWithHoles.mySize]; omega

/- # Experiments -/

-- axiom state : Type
-- axiom x : Lens Nat state
-- axiom a : Lens Nat state
-- axiom b : Lens Nat state
--
-- def $a := 5
--
-- #check [expr| $a + 1]

-- TODO fix
-- noncomputable
-- def example_program := [ec|
-- if ($x==1) { a <- 1; b <- 2; } else {}
-- ]

-- #print example_program
