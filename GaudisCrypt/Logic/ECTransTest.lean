import GaudisCrypt.Logic.ECTrans
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Syntax.Syntax

/-! Tests of `equiv_trans` (`Logic/ECTrans.lean`). -/

namespace GaudisCrypt.ECTransTest

open GaudisCrypt

/-- EC's `transitivity{1} { y <- 1; } (={y} ==> ={y}) (true ==> ={y})`. -/
example : equiv[ ={y} ==> ={y} ] {
      var x : ℕ, y : ℕ;
      x <- 1;
      y <- §x;
    } ~ {
      var y : ℕ;
      y <- 1;
    } := by
  equiv_trans{1} { y <- 1; } (={y} ==> ={y}) (True ==> ={y})
  · intro σ₁ σ₂ _; exact ⟨σ₁, by auto_close⟩
  · auto_close
  · equiv_auto
  · equiv_auto

end GaudisCrypt.ECTransTest
