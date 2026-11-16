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
info: equiv[ ={g} ==> ={g} ] {
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
/--
info: equiv[ M.f (n) ~ M.f (n) : ={n} ==> ={res, g} ]
-/
#guard_msgs in
#roundtrip equiv[ M.f ~ M.f : ={n} ==> ={res, g} ]

/--
info: equiv[ M.f (n) ~ M.f (n) : §n{1} = §n{2} + 1 ∧ §g{1} = 0 ==> ={res} ]
-/
#guard_msgs in
#roundtrip equiv[ M.f ~ M.f : §n{1} = §n{2} + 1 ∧ §g{1} = 0 ==> §res{1} = §res{2} ]

/-- error: in a relational condition, a read says which side it is about: `§x{1}` or `§x{2}` -/
#guard_msgs in
example : Prop := equiv[ M.f ~ M.f : §n = 1 ==> True ]

/-- EC's `b{1} => b{2}` on booleans: the reads coerced to propositions (`b = true`). -/
example : equiv[ (§b{1} → §b{2}) ==> (§b{1} → §b{2}) ] {
      var b : Bool;
      skip;
    } ~ {
      var b : Bool;
      skip;
    } =
    equiv[ (§b{1} = true → §b{2} = true) ==> (§b{1} = true → §b{2} = true) ] {
      var b : Bool;
      skip;
    } ~ {
      var b : Bool;
      skip;
    } := rfl

-- a name with one type on the left and another on the right (as inlining leaves them): two
-- variables, `§x{i}` the one of side `i`
/--
info: equiv[ §x{1} = true ∧ §x{2} = 2 ==> §y{1} = §x{1} ∧ §y{2} = §x{2} + 1 ] {
    var y : Bool, x : Bool;
    y <- §x;
} ~ {
    var y : ℕ, x : ℕ;
    y <- §x + 1;
}
-/
#guard_msgs in
#roundtrip equiv[ §x{1} = true ∧ §x{2} = 2 ==> §y{1} = §x{1} ∧ §y{2} = §x{2} + 1 ] {
      var x : Bool, y : Bool;
      y <- $x;
    } ~ {
      var x : Nat, y : Nat;
      y <- $x + 1;
    }

module M2 {
  proc h (a : ℕ, b : ℕ) : ℕ {
    return $a + $b
  };
}

-- two procedures that do not take the same parameters, the conditions reading them
/--
info: equiv[ M.f (n) ~ M2.h (a, b) : §b{2} = 5 ∧ §n{1} = §a{2} ==> ={res} ]
-/
#guard_msgs in
#roundtrip equiv[ M.f ~ M2.h : §b{2} = 5 ∧ §n{1} = §a{2} ==> ={res} ]

-- `={x, y}` is printed for the equations it stands for (joined to the right); `={allGlobals}`
-- is the whole global state
/--
info: equiv[ ={allGlobals} ∧ §x{1} = §y{2} ∧ ={x, y} ==> (={x} ∧ §y{1} ≤ §y{2}) ∧ ={y, g} ] {
    var x : ℕ, y : ℕ;
    y <- §x;
} ~ {
    var x : ℕ, y : ℕ;
    y <- §x;
}
-/
#guard_msgs in
#roundtrip equiv[ ={allGlobals} ∧ §x{1} = §y{2} ∧ ={x, y} ==> (={x} ∧ §y{1} ≤ §y{2}) ∧ ={y, g} ] {
      var x : ℕ, y : ℕ;
      y <- $x;
    } ~ {
      var x : ℕ, y : ℕ;
      y <- $x;
    }

end GaudisCrypt.PRHLSyntaxTest
