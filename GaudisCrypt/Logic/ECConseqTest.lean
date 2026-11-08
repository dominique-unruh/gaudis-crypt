import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.PHoareSyntax

/-! Tests of `phoare_hoare` and the `conseq` tactics (`Logic/ECConseq.lean`). -/

namespace GaudisCrypt.ECConseqTest

open GaudisCrypt

/-- EC's `hoare`: an event that cannot happen has probability `0`. -/
example : phoare[ True ==> §y = 3 ] ≤ (0) {
      var y : ℕ;
      y <- 1;
    } := by
  phoare_hoare
  hoare_wp 1
  hoare_skip
  simp

/-- EC's `conseq (: _ ==> Q)` on a Hoare triple: a stronger postcondition, then wp. -/
example : hoare[ True ==> §y ≤ 2 ] {
      var y : ℕ;
      y <- 1;
    } := by
  hoare_conseq (: _ ==> §y = 1)
  · intro σ h
    simp_all
  · hoare_wp 1
    hoare_skip
    simp

/-- EC's `conseq` on a relational judgment, then `sim`. -/
example : equiv[ ={x} ∧ §y{1} = 0 ==> ={x} ] {
      var x : ℕ, y : ℕ;
      x <- §x + 1;
    } ~ {
      var x : ℕ;
      x <- §x + 1;
    } := by
  equiv_conseq (: ={x} ==> _)
  · intro _ _ h
    exact h.1
  · sim

/-- EC's `exists* x; elim* => v`: the start value of `x`, named. -/
example : hoare[ True ==> §y = §x ] {
      var x : ℕ, y : ℕ;
      y <- §x;
    } := by
  stmt_exists* §x
  intro v
  hoare_wp 1
  hoare_skip
  simp

/-- EC's `conseq (_ ==> ={x})`: `y`, which the code does not modify, keeps its equality from the
precondition (EC's frame). -/
example : equiv[ ={x, y} ==> ={x, y} ] {
      var x : ℕ, y : ℕ;
      x <- §x + 1;
    } ~ {
      var x : ℕ, y : ℕ;
      x <- §x + 1 + (§y - §y);
    } := by
  equiv_conseq (: _ ==> ={x})
  · auto_close
  · sim

end GaudisCrypt.ECConseqTest
