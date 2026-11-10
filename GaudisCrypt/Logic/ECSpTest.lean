import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECElim
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Syntax.Syntax

/-! Tests of `stmt_sp` (`Logic/ECSp.lean`). -/

namespace GaudisCrypt.ECSpTest

open GaudisCrypt

/-- EC's `sp` over two assignments, then the rest by wp. -/
example : hoare[ True ==> §y = 2 ] {
      var x : ℕ, y : ℕ;
      x <- 1;
      x <- §x + 1;
      y <- §x;
    } := by
  stmt_sp 2
  hoare_wp 1
  apply hoare_skip_of_imp
  rintro _ ⟨_, ⟨-, h⟩, h'⟩
  simp_all [liftLens, LiftLens.lift, Lens.set_get]

/-- EC's `sp` over `x <- e` with `e` reading `x`: `exists x0, P[x0/x] /\ x = e[x0/x]`, the
existential out by EC's `elim * => x0`. -/
example : hoare[ §x = 1 ==> §x = 2 ] {
      var x : ℕ;
      x <- §x + 1;
    } := by
  stmt_sp
  hoare_elim* => x0
  apply hoare_skip_of_imp
  rintro _ ⟨h, h'⟩
  simp_all [liftLens, LiftLens.lift, Lens.set_get]

/-- EC's `P /\ x = e` with a precondition on a local variable, past an assignment and a reset
(what inlining leaves): `P` kept, the assignment as a read. -/
example : hoare[ §x = 1 ==> §x = 1 ] {
      var x : ℕ, y : ℕ;
      reset_vars {"y"} ∪ stringsStartingWith "@." \ {"@.y"};
      y <- 2;
    } := by
  stmt_sp
  apply hoare_skip_of_imp
  intro _ h
  exact h.1

/-- EC's `sp` on both sides of a relational judgment, as far as the code is deterministic, then
`sim` on what is left. -/
example : equiv[ True ==> ={b} ] {
      var x : ℕ, b : Bool;
      x <- 1;
      b <$ SubProbability.uniform;
    } ~ {
      var x : ℕ, b : Bool;
      x <- 2;
      b <$ SubProbability.uniform;
    } := by
  stmt_sp
  sim

/-- EC's `sp n m` and `wp n m`, positions counted from the start or (negative) the end:
`sp 1 0` the left's first assignment, `wp -2 2` the left's last statement and the right's after
its second, `sp 0 -1` all of the right's first. -/
example : equiv[ True ==> ={b} ] {
      var x : ℕ, b : Bool;
      x <- 1;
      b <$ SubProbability.uniform;
      x <- 3;
    } ~ {
      var x : ℕ, b : Bool;
      x <- 2;
      b <$ SubProbability.uniform;
      x <- 4;
    } := by
  stmt_sp 1 0
  stmt_wp -2 2
  stmt_sp 0 -2
  sim

end GaudisCrypt.ECSpTest
