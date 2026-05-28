import Lean
import Lean.Elab.Term
import PlonkLean.Semantics

-- TODO Just use Getter?
def Expression s a := s → a

/-- Syntactic program (with arbitrary Lean terms as expressions) -/
inductive Stmt (s : Type) : Type 1 where
  | skip : Stmt s
  | assign {a : Type} : Lens a s → Expression s a → Stmt s -- mutation
  | sample {a : Type} : Lens a s → Expression s (SubProbability a) → Stmt s
  | call {a : Type} : Lens a s → Expression s (Program s a) → Stmt s
  | seq : Stmt s → Stmt s → Stmt s                   -- c1; c2
  | ifThenElse : (Expression s Bool) → Stmt s → Stmt s → Stmt s  -- if b then c1 else c2
  | while : (Expression s Bool) → Stmt s → Stmt s           -- while b do c

/- # Syntax of programs -/

declare_syntax_cat ec_stmt
declare_syntax_cat ec_block
declare_syntax_cat ec_var

syntax (name := ec_var_single) ident : ec_var
syntax (name := ec_var_nary) "( " ident (", " ident)* " )" : ec_var
syntax ec_var " <- " term ";" : ec_stmt
syntax ec_var " <@ " term ";" : ec_stmt
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
  | `([ec| $x:ec_var <@ $e:term;]) => `(Stmt.call [var| $x] [expr| $e])
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

noncomputable
def denotation {s : Type} : Stmt s → Program s Unit
| Stmt.skip => do return ()
| Stmt.assign x e => do let st ← Program.get_state; let result := e st; Program.set x result
| Stmt.sample x e => do let st ← Program.get_state; let result ← (e st).toProgram; Program.set x result
| Stmt.call x e => do let st ← Program.get_state; let result ← e st; Program.set x result
| Stmt.ifThenElse c t e => do let st ← Program.get_state; let result := c st; if result then denotation t else denotation e
| Stmt.while c t => while_loop (do let st ← Program.get_state; return c st) (denotation t)
| Stmt.seq p q => do denotation p; denotation q

/- # Experiments -/

axiom state : Type
axiom x : Lens Nat state
axiom a : Lens Nat state
axiom b : Lens Nat state

def $a := 5

#check [expr| $a + 1]

noncomputable
def example_program := [ec|
if ($x==1) { a <- 1; b <- 2; } else {}
]

#print example_program
