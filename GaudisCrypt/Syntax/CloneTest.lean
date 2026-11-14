import GaudisCrypt.Syntax.Clone

/-!
# Test of `clone`: Lean's reserved names are not aliased

A theory whose operator has a congruence lemma (`T.twice.congr_simp`, made by Lean when `simp`
first needs it; here by naming it).  The clone must not alias it: `C.twice.congr_simp` is then
Lean's own lemma about `C.twice`.  (An alias would be a statement about `T.twice`, found where
`simp` looks for the lemma of `C.twice`.)
-/

namespace GaudisCrypt.CloneTest

namespace T

variable {α : Type}

/-- An operator of the theory. -/
def twice (f : α → α) (x : α) : α := f (f x)

/-- A lemma of the theory. -/
theorem twice_id (x : α) : twice id x = x := rfl

end T

-- the theory's congruence lemma exists before the clone is made
example := @T.twice.congr_simp

clone T as C with type α <- Nat

/--
info: GaudisCrypt.CloneTest.C.twice_id (x : Nat) : C.twice id x = x
-/
#guard_msgs in
#check C.twice_id

/--
info: C.twice.congr_simp : ∀ (f f_1 : Nat → Nat), f = f_1 → ∀ (x x_1 : Nat), x = x_1 → C.twice f x = C.twice f_1 x_1
-/
#guard_msgs in
#check @C.twice.congr_simp

end GaudisCrypt.CloneTest
