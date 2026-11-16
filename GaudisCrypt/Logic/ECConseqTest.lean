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
  · intro σ _ τ _ h
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

/-- EC's `conseq (: _ ==> Q)` on a Hoare triple: `x`, which the code does not modify, keeps its
value from the precondition (EC's frame). -/
example (k : ℕ) : hoare[ §x = k ==> §y = k + 1 ] {
      var x : ℕ, y : ℕ;
      y <- §x + 1;
    } := by
  hoare_conseq (: _ ==> §y = §x + 1)
  · auto_close
  · hoare_wp 1
    hoare_skip
    simp

-- the `post` goal of `hoare_conseq`: the precondition at the start, the frame, `Q' => Q`
/--
trace: case post
k : ℕ
⊢ ∀ (σ : ProgramState),
    GaudiExpr[ §(localVarLens "x" ℕ) = k ].get σ →
      ∀ (τ : ProgramState),
        (localVarLens "x" ℕ).get τ = (localVarLens "x" ℕ).get σ ∧ True →
          GaudiExpr[ §(localVarLens "y" ℕ) = §(localVarLens "x" ℕ) + 1 ].get τ →
            GaudiExpr[ §(localVarLens "y" ℕ) = k + 1 ].get τ

case judgment
k : ℕ
⊢ hoare[ §x = k ==> §y = §x + 1 ] {
      var x : ℕ, y : ℕ;
      y <- §x + 1;
}
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 2 goals and ends with 2 goals, 2 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example (k : ℕ) : hoare[ §x = k ==> §y = k + 1 ] {
      var x : ℕ, y : ℕ;
      y <- §x + 1;
    } := by
  hoare_conseq (: _ ==> §y = §x + 1)
  trace_state
  all_goals sorry

/-- EC's `exists* x{1}, y{2}; elim* => a b` on a relational judgment. -/
example : equiv[ ={x} ∧ §y{2} = 2 ==> §z{1} + 2 = §z{2} ] {
      var x : ℕ, z : ℕ;
      z <- §x;
    } ~ {
      var x : ℕ, y : ℕ, z : ℕ;
      z <- §x + §y;
    } := by
  equiv_exists* §x{1}, §y{2}
  intro a b
  stmt_wp
  equiv_skip
  auto_close

end GaudisCrypt.ECConseqTest
