import GaudisCrypt.Syntax.HoareSyntax

/-! # Tests for `HoareSyntax` -/

namespace GaudisCrypt.HoareSyntaxTest

open GaudisCrypt

variable [ProgramSpec]

axiom x : Lens Int State
axiom y : Lens Int State

-- `Lens.pair` needs disjointness of the paired lenses (resolved at the concrete lenses).
axiom x_y_disjoint : Lens.Disjoint x y
attribute [instance] x_y_disjoint

/- ### The basic shape -/

-- globals only, no locals, no binders
example : Prop := hoare[ §x = 1 ==> §x = 2 ] {
  x <- §x + 1;
}

-- `$` and `§` are the same sigil
example : Prop := hoare[ $x = 1 ==> $x = 2 ] {
  x <- $x + 1;
}

/- ### `var` declarations and spine binders

Both are repeated around the pre- and the postcondition, so a condition may mention a
local program variable and a `let` from the body's spine. -/

-- a local variable, mentioned in the postcondition
example : Prop := hoare[ True ==> §u = 2 ] {
  var u : Int;
  u <- 2;
}

-- a body `let`, mentioned in both conditions
example : Prop := hoare[ §x = two - 1 ==> §x = two ] {
  let two := (2 : Int);
  x <- §x + 1;
}

-- several `var` lines, several names per binder, all visible in the conditions
example : Prop := hoare[ §u = 0 ∧ §v = 0 ∧ §w = 0 ==> §u = 1 ] {
  var u v : Int;
  var w : Int;
  u <- §u + 1;
}

-- the user's example: a tuple l-value and a spine `let`
example : Prop := hoare[ §x = 1 ∧ §y = 1 ==> §x = 2 ∧ §y = 2 ] {
  let two := (2 : Int);
  (x, y) <- (§y + 1, two);
}

/- ### Control flow in the body -/

example : Prop := hoare[ §x = 0 ==> §x = 1 ] {
  if (§x == 0) {
    x <- 1;
  } else {
    x <- §x;
  }
}

example : Prop := hoare[ True ==> §x ≥ 0 ] {
  while (§x < 0) {
    x <- §x + 1;
  }
}

-- an empty body is `skip`
example : Prop := hoare[ §x = 1 ==> §x = 1 ] {
}

/- ### What the notation elaborates to

`hoare[ P ==> Q ] { s }` is `hoareStmt` applied to the two predicates and the statement, all
over the local state `ProcedureScope [] locals`. -/

example :
    (hoare[ §x = 1 ==> §x = 2 ] { x <- §x + 1; })
      = hoareStmt (l := ProcedureScope [] [])
          (fun σ => x.get σ.global = 1)
          GaudiProg[ x <- $x + 1; ]
          (fun σ => x.get σ.global = 2) := rfl

/-- The local-state description that a single `var u : Int;` declaration produces. -/
private abbrev oneInt : List (Σ t : Type, Inhabited t) := [⟨Int, inferInstance⟩]

/-- The lens a single `var u : Int;` declaration binds `u` to. -/
private abbrev uLens : Lens Int (ProcedureState (ProcedureScope [] oneInt)) :=
  Lens.intoLocalVars Lens.id

-- a `var` makes the local state carry that slot, and the variable is its `intoLocalVars` lens
example :
    (hoare[ True ==> §u = 2 ] { var u : Int; u <- 2; })
      = hoareStmt (l := ProcedureScope [] oneInt)
          (fun _ => True)
          GaudiProg[ uLens <- (2 : Int); ]
          (fun σ => uLens.get σ = 2) := rfl

/--
info: hoareStmt { get := fun st ↦ §x = 1 }.get
  (GaudiProg[
      x <- §x + 1;
])
  { get := fun st ↦ §x = 2 }.get : Prop
-/
#guard_msgs in
#check hoare[ §x = 1 ==> §x = 2 ] { x <- §x + 1; }

end GaudisCrypt.HoareSyntaxTest
