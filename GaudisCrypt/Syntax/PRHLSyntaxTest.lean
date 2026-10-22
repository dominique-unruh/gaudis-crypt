import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.PRHLSyntax
-- for `#roundtrip`
import GaudisCrypt.Syntax.ProgramSyntaxTest

/-! Smoke tests for `equiv[ … ]` (`Syntax/PRHLSyntax.lean`). -/

namespace GaudisCrypt.PRHLSyntaxTest

open GaudisCrypt

global_var g : ℕ

-- statements, both sides with their own locals
example : Prop := equiv[ §g{1} = §g{2} ==> ={g} ] {
    var x : ℕ;
    x <- $g + 1;
    g <- $x;
  } ~ {
    var y : ℕ;
    y <- $g;
    g <- $y + 1;
  }

-- a name declared on both sides
example : Prop := equiv[ ={x} ==> §x{1} + 1 = §x{2} ] {
    var x : ℕ;
    x <- $x;
  } ~ {
    var x : ℕ;
    x <- $x + 1;
  }

/-! Printing: sided reads print as `§x{1}`/`§x{2}`, each side with its own `var`s. -/

/--
info: equiv[ §g{1} = §g{2} ==> §g{1} = §g{2} ] {
    var x : ℕ;
    x <- §g + 1;
    g <- §x;
} ~ {
    var y : ℕ;
    y <- §g;
    g <- §y + 1;
}
-/
#guard_msgs in
#roundtrip equiv[ §g{1} = §g{2} ==> ={g} ] {
    var x : ℕ;
    x <- $g + 1;
    g <- $x;
  } ~ {
    var y : ℕ;
    y <- $g;
    g <- $y + 1;
  }

-- reads as plain `get`s, as the wp steps leave them; a variable only the conditions mention is
-- declared on the left
/--
info: equiv[ §g{1} ≤ §g{2} ==> §z{1} = §g{2} ] {
    var z : ℕ;
    g <- 1;
} ~
  {
    g <- 2;
}
-/
#guard_msgs in
#roundtrip prhlStmt (fun σ₁ σ₂ => g.get σ₁.globals ≤ g.get σ₂.globals) GaudiProg[ g <- 1; ]
  GaudiProg[ g <- 2; ] (fun σ₁ σ₂ => (localVarLens "z" ℕ).get σ₁ = g.get σ₂.globals)

moduletype T {
  proc f (n : ℕ) -> ℕ;
}

module M : T {
  proc f (n : ℕ) : ℕ {
    g <- $n;
    return $n + 1
  };
}

-- the procedure form prints with the parameter names, read on each side
/-- info: equiv[ M.f (n) ~ M.f (n) : §n{1} = §n{2} ==> §res{1} = §res{2} ∧ §g{1} = §g{2} ] -/
#guard_msgs in
#roundtrip equiv[ M.f ~ M.f : ={n} ==> ={res, g} ]

/-- info: equiv[ M.f (n) ~ M.f (n) : §n{1} = §n{2} + 1 ∧ §g{1} = 0 ==> §res{1} = §res{2} ] -/
#guard_msgs in
#roundtrip equiv[ M.f ~ M.f : §n{1} = §n{2} + 1 ∧ §g{1} = 0 ==> §res{1} = §res{2} ]

/-- error: in a relational condition, a read says which side it is about: `§x{1}` or `§x{2}` -/
#guard_msgs in
example : Prop := equiv[ M.f ~ M.f : §n = 1 ==> True ]

end GaudisCrypt.PRHLSyntaxTest
