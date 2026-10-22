import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.PRHLSyntax

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

moduletype T {
  proc f (n : ℕ) -> ℕ;
}

module M : T {
  proc f (n : ℕ) : ℕ {
    g <- $n;
    return $n + 1
  };
}

example : Prop := equiv[ M.f ~ M.f : ={n} ==> ={res, g} ]

example : Prop := equiv[ M.f ~ M.f : §n{1} = §n{2} + 1 ∧ §g{1} = 0 ==> §res{1} = §res{2} ]

/-- error: in a relational condition, a read says which side it is about: `§x{1}` or `§x{2}` -/
#guard_msgs in
example : Prop := equiv[ M.f ~ M.f : §n = 1 ==> True ]

end GaudisCrypt.PRHLSyntaxTest
