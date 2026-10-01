import GaudisCrypt.Syntax.HoareSyntax

/-! # Tests for `HoareSyntax` -/

-- a `#guard_msgs` docstring has to reproduce Lean's output exactly, and Lean wraps that at its
-- own width, so some of them cannot be kept inside the line limit
set_option linter.style.longLine false

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
info: hoareStmt GaudiExpr[ §x = 1 ].get
  (GaudiProg[
      x <- §x + 1;
])
  GaudiExpr[ §x = 2 ].get : Prop
-/
#guard_msgs in
#check hoare[ §x = 1 ==> §x = 2 ] { x <- §x + 1; }

/- ### Procedure triples — `hoare[ M (x, m) : P ==> Q ]` -/

moduletype TestSig {
  proc f (a : Int, b : Int) -> Int;
  proc g () -> Bool;
}

module TestMod {
  proc p (u : Int) : Int { return $u; };
}

variable (m : TestSig) (q : Procedure (procsig (Int) -> Int))

-- a module that is still a functor of its module parameters, for the diagnostic below
axiom functorProc : Module.Arr (procmod (Int) -> Int) (procmod (Int) -> Int)

-- parameter names written at the triple; a global is read the same way as a parameter
example : Prop := hoare[ m.f (a, b) : §a = 1 ∧ §y = 0 ==> §res = 2 ]

-- …or left out, and taken from the `@[gaudiProcParamNames]` the `moduletype` field recorded
example : Prop := hoare[ m.f : §a = 1 ∧ §b = 2 ==> §res = 2 ]

-- `§params` is the whole argument tuple, `§res` the result
example : Prop := hoare[ m.f : §params = (1, 2) ==> §res = 2 ]

-- no parameters: an absent list and an explicit `()` mean the same here
example : Prop := hoare[ m.g : §y = 0 ==> §res = true ]
example : Prop := hoare[ m.g () : §y = 0 ==> §res = true ]

-- a `module`-declared procedure, as a module and as the procedure itself (both carry the names)
example : Prop := hoare[ TestMod.p : §u = 1 ==> §res = 1 ]
example : Prop := hoare[ TestMod.p.procedure : §u = 1 ==> §res = 1 ]

-- a bare `Procedure` with nothing recorded: the names have to be written
example : Prop := hoare[ q (v) : §v = 1 ==> §res = 1 ]

/- ### What the procedure notation elaborates to

`hoareProc` applied to two lambdas of exactly its own shape.  A parameter is the body's own
slot chain (`Lens.id.ofst` for the first of two) applied to the argument tuple, and a global
is read off the `σ` binder. -/

example :
    (hoare[ m.f (a, b) : §a = 1 ∧ §y = 0 ==> §res = 2 ])
      = hoareProc (sig := procsig (Int, Int) -> Int)
          (fun (args : Int × Int) σ => (Lens.id.ofst).get args = 1 ∧ y.get σ = 0)
          (Module.Proc.procedure m.f)
          (fun res _ => res = 2) := rfl

-- the second of two parameters is `.osnd`, and the only parameter of one is `Lens.id`
example :
    (hoare[ m.f (a, b) : §b = 1 ==> True ])
      = hoareProc (sig := procsig (Int, Int) -> Int)
          (fun (args : Int × Int) _ => (Lens.id.osnd).get args = 1)
          (Module.Proc.procedure m.f)
          (fun _ _ => True) := rfl

example :
    (hoare[ q (v) : §v = 1 ==> §res = 1 ])
      = hoareProc (sig := procsig (Int) -> Int)
          (fun (args : Int) _ => (Lens.id).get args = 1) q
          (fun (res : Int) _ => res = 1) := rfl

/- ### Diagnostics -/

-- a written name list that does not match the arity
/-- info: this procedure takes 2 parameter(s), but 1 are named here -/
#guard_msgs in
#check_failure hoare[ m.f (a) : True ==> True ]

/-- info: this procedure takes 0 parameter(s), but 2 are named here -/
#guard_msgs in
#check_failure hoare[ m.g (a, b) : True ==> True ]

-- names that disagree with the recorded ones: a warning, and the written names win
/-- warning: the declared parameter names of this procedure are [a, b], not [c, d] -/
#guard_msgs in
example : Prop := hoare[ m.f (c, d) : §c = 1 ==> True ]

-- nothing to take the names from
/--
info: no parameter names are recorded for this procedure; write them at the triple, as in `hoare[ M (x, y) : … ]`
-/
#guard_msgs in
#check_failure hoare[ q : True ==> True ]

-- a module that is still a functor, and something that is no procedure at all
/--
info: a triple is about a procedure, but this module still takes module parameters — apply them first
-/
#guard_msgs in
#check_failure hoare[ functorProc : True ==> True ]

/--
info: expected a procedure or a procedure module `Module.Proc …`, but this has type
  Lens ℤ State
-/
#guard_msgs in
#check_failure hoare[ x : True ==> True ]

/- ### Printing

A procedure triple has no delaborator yet, so it prints as the `hoareProc` application it is:
the conditions as `GaudiExpr[ ]`s applied to the repacked state, with each parameter a nested
`§GaudiExpr[ ]` — the constant getter the notation binds the parameter name to. -/

/--
info: hoareProc (fun args σ ↦ GaudiExpr[ §GaudiExpr[ Lens.id.ofst.get args ] = 1 ].get { global := σ, locals := () })
  m.f.procedure fun res σ ↦ GaudiExpr[ §GaudiExpr[ res ] = 2 ].get { global := σ, locals := () } : Prop
-/
#guard_msgs in
#check hoare[ m.f (a, b) : §a = 1 ==> §res = 2 ]

end GaudisCrypt.HoareSyntaxTest
