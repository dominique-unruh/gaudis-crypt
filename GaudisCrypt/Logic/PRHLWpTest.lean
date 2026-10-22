import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.PRHLWp

/-! Tests of the relational tactics (`Logic/PRHLWp.lean`). -/

namespace GaudisCrypt.PRHLWpTest

open GaudisCrypt

moduletype Adv {
  proc guess (x : ℕ) -> ℕ;
}

/-- EC's `call (_ : ={glob A})`: the same adversary, on equal arguments and its globals equal,
answers the same — whatever else differs. -/
example (A : Adv) (R : Footprint VariableAssignment)
    (hA : ∀ a, (procedureDenotation (Adv.guess A).procedure a).inFootprint R) :
    equiv[ §x{1} = §x{2} ∧ §(R.touched_getter){1} = §(R.touched_getter){2} ==> ={y} ] {
      var x : ℕ, y : ℕ;
      y <- call (Adv.guess A).procedure ($x);
    } ~ {
      var x : ℕ, y : ℕ;
      y <- call (Adv.guess A).procedure ($x);
    } := by
  equiv_call prhlProc_glob hA
  equiv_skip
  exact fun _ _ _ _ h => ⟨h, fun _ _ _ _ h' => h'.1⟩

/-- `rnd` with the negation coupling. -/
example : equiv[ True ==> §b{1} = !§b{2} ] {
      var b : Bool;
      b <$ SubProbability.uniform;
    } ~ {
      var b : Bool;
      b <$ SubProbability.uniform;
    } := by
  equiv_rnd (fun b => !b)
  equiv_skip
  simp

/-- wp on one side, then the other. -/
example : equiv[ ={x} ==> ={x} ] {
      var x : ℕ;
      x <- $x + 2;
      x <- $x - 1;
    } ~ {
      var x : ℕ;
      x <- $x + 1;
    } := by
  stmt_wp{1}
  stmt_wp{2} 1
  equiv_skip
  intro x₁ x₂ h
  omega

/-- A cut, and a case analysis on the initial states. -/
example : equiv[ True ==> ={y} ] {
      var x : ℕ, y : ℕ;
      x <- 1;
      y <- $x;
    } ~ {
      var x : ℕ, y : ℕ;
      x <- 1;
      y <- 1;
    } := by
  equiv_seq 1 1 : §x{1} = 1
  · equiv_case §x{2} = 0
    · stmt_wp
      equiv_skip
      simp
    · stmt_wp
      equiv_skip
      simp
  · stmt_wp
    equiv_skip
    simp

end GaudisCrypt.PRHLWpTest
