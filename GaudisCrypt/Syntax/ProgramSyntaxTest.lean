import GaudisCrypt.Syntax.ProgramSyntax

/-! # Tests for `ProgramSyntax` -/

/-! ## Experiments for programs -/

namespace GaudisCrypt.ProgTest

open GaudisCrypt

variable [ProgramSpec]

axiom a : Lens Nat State
axiom b : Lens Nat State
axiom c : Lens Bool State
axiom d : Lens Nat State

-- `Lens.pair` needs disjointness of the paired lenses (resolved at the concrete lenses).
-- For nested tuples `(a, b), d` the `disjoint3'` instance derives `disjoint (a.pair b) d`
-- from the pairwise ones.
axiom a_b_disjoint : disjoint a b
axiom a_d_disjoint : disjoint a d
axiom b_d_disjoint : disjoint b d
attribute [instance] a_b_disjoint a_d_disjoint b_d_disjoint

noncomputable def prog_assign : Stmt Unit := GaudiProg[
  a <- $a + 1;
  b <- $a + $b;
]

noncomputable def prog_if : Stmt Unit := GaudiProg[
  if ($a == $b) {
    a <- 0;
  } else {
    a <- $b;
  }
]

noncomputable def prog_while : Stmt Unit := GaudiProg[
  while ($a == 0) {
    a <- $a + 1;
  }
]

noncomputable def prog_sample : Stmt Unit := GaudiProg[
  c <$ GaudisCrypt.SubProbability.uniform;
]

noncomputable def split : Stmt Unit := GaudiProg[
  (a,b) <- (1,2);
]

noncomputable def split2 : Stmt Unit := GaudiProg[
  a,b <- (1,2);
]

noncomputable def split3 : Stmt Unit := GaudiProg[
  (a,b),d <- ((1,3),2);
]


#check @prog_assign
#print prog_if

/- ### Procedures -/

-- one param, no locals, return type inferred
noncomputable def proc_inc := proc (x : Nat) {
  return $x + 1
}
#check @proc_inc

-- params + a local + body + explicit return type
noncomputable def proc_sum := proc (x : Nat, y : Nat) : Nat {
  var u : Nat;
  u <- $x + $y;
  return $u
}
#print proc_sum

-- no params, a local, control flow, writes to a global
noncomputable def proc_loop := proc () {
  var i : Nat;
  i <- 0;
  while ($i == 0) {
    i <- $i + 1;
    a <- $a + $i;
  }
  return $i
}
#check @proc_loop

/- ### Procedure calls -/

-- store the result of a one-argument call
noncomputable def prog_call : Stmt Unit := GaudiProg[
  a <- call proc_inc ($a);
]
#print prog_call

-- a two-argument call (the argument tuple matches the callee's `ParamType`)
noncomputable def prog_call2 : Stmt Unit := GaudiProg[
  a <- call proc_sum ($a, $b);
]

-- discard the result (uses `Lens.throwaway`); `()` still required
noncomputable def prog_call_void : Stmt Unit := GaudiProg[
  call proc_inc ($a);
]
#check @prog_call_void

/- ### Holes (adversary placeholders) -/

-- A `uses` clause declares holes; `call A (…)` on a hole name becomes `StmtWithHoles.hole`.
noncomputable def proc_with_hole := proc (x : Nat) uses (A : (Nat) → Nat) : Nat {
  var y : Nat;
  y <- call A ($x);          -- hole call (A is a HoleIndex)
  return $y
}
#print proc_with_hole

-- two holes + a concrete procedure call, mixed in one body
noncomputable def proc_two_holes := proc (x : Nat) uses (A : (Nat) → Bool, B : (Bool) → Nat) {
  var u : Bool;
  var v : Nat;
  u <- call A ($x);          -- hole A
  v <- call B ($u);          -- hole B
  v <- call proc_inc ($v);   -- concrete procedure (still `call`)
  call A ($v);               -- discarded hole result
  return $v
}
#check @proc_two_holes
#print proc_two_holes

/- ### Procedure *type* syntax -/

-- `proctype (…) -> W` is `Procedure { params := […], ret := W }`
example : (proctype (Nat, Bool) -> Nat) = Procedure { params := [Nat, Bool], ret := Nat } := rfl
#check (proc_inc : proctype (Nat) -> Nat)
#check (proc_sum : proctype (Nat, Nat) -> Nat)

-- `proctype (…) -> W uses (…)` is the corresponding `ProcedureWithHoles`
#check (proc_two_holes : proctype (Nat) -> Nat uses ((Nat) → Bool, (Bool) → Nat))
#check (proc_with_hole : proctype (Nat) -> Nat uses ((Nat) → Nat))

-- the types also print back as `proctype …` (unexpanders)
#check proctype (Nat) -> Nat
#check proctype (Nat, Bool) -> Nat uses ((Nat) → Bool, (Bool) → Nat)

-- `procsig (…) -> W` is the bare signature; `Procedure (procsig …) = proctype …`
example : (procsig (Nat, Bool) -> Nat) = ({ params := [Nat, Bool], ret := Nat } : ProcedureSignature) :=
  rfl
example : Procedure (procsig (Nat) -> Nat) = proctype (Nat) -> Nat := rfl
#check procsig (Nat, Bool) -> Nat
#check ProcedureSignature.mk [String,String] Nat
#check Procedure (ProcedureSignature.mk [String,String] Nat)
#check ProcedureWithHoles (.append .empty (procsig () -> Unit)) (ProcedureSignature.mk [String,String] Nat)
-- TODO: Can we make test cases that trigger if the terms above don't print the way we want?

-- both arrow spellings accepted: `->` and `→`
example : (procsig (Nat) → Bool) = (procsig (Nat) -> Bool) := rfl
example : (proctype (Nat) → Bool) = (proctype (Nat) -> Bool) := rfl
#check (proc_two_holes : proctype (Nat) → Nat uses ((Nat) → Bool, (Bool) → Nat))

end GaudisCrypt.ProgTest
