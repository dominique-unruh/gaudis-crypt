import GaudisCrypt.Logic.ECSp
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
  rintro _ ⟨_, ⟨-, h⟩, rfl⟩
  simp_all [liftLens, LiftLens.lift, Lens.set_get]

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

end GaudisCrypt.ECSpTest
