import GaudisCrypt.Logic.ECConseqHoare
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Syntax.Syntax

/-! Tests of `equiv_conseq (: P ==> Q) _ (: P₂ ==> Q₂)` (`Logic/ECConseqHoare.lean`). -/

namespace GaudisCrypt.ECConseqHoareTest

open GaudisCrypt

-- EC's `conseq (_ : ={x} ==> ={x}) _ (_ : true ==> y = 1)`: what the right program does to `y`
-- is a Hoare triple of its own; goals `pre`, `post` (with EC's frame), `hoare`, `judgment`
/--
trace: case pre
⊢ ∀ (σ₁ σ₂ : ProgramState),
    §(localVarLens "x" ℕ) = §(localVarLens "x" ℕ) → §(localVarLens "x" ℕ) = §(localVarLens "x" ℕ) ∧ True

case post
⊢ ∀ (σ₁ σ₂ : ProgramState),
    §(localVarLens "x" ℕ) = §(localVarLens "x" ℕ) →
      ∀ (τ₁ τ₂ : ProgramState),
        (localVarLens "y" ℕ).get τ₁ = (localVarLens "y" ℕ).get σ₁ ∧ True →
          True →
            §(localVarLens "x" ℕ) = §(localVarLens "x" ℕ) ∧ §(localVarLens "y" ℕ) = 1 →
              §(localVarLens "x" ℕ) = §(localVarLens "x" ℕ) ∧ §(localVarLens "y" ℕ) = 1

case hoare
⊢ hoare[ True ==> §y = 1 ] {
      var x : ℕ, y : ℕ;
      x <- §x + 1;
      y <- 1;
}

case judgment
⊢ equiv[ §x{1} = §x{2} ==> §x{1} = §x{2} ] {
      var x : ℕ;
      x <- §x + 1;
} ~ {
      var x : ℕ, y : ℕ;
      x <- §x + 1;
      y <- 1;
}
---
warning: The following tactic starts with 4 goals and ends with 4 goals, 4 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : equiv[ ={x} ==> ={x} ∧ §y{2} = 1 ] {
      var x : ℕ;
      x <- §x + 1;
    } ~ {
      var x : ℕ, y : ℕ;
      x <- §x + 1;
      y <- 1;
    } := by
  equiv_conseq (: ={x} ==> ={x}) _ (: True ==> §y{2} = 1)
  trace_state
  · auto_close
  · auto_close
  · hoare_auto
  · equiv_auto

-- a condition of the right program's triple that reads the left memory is refused
/--
error: equiv_conseq: a condition of the right program's triple reads the left memory:
  §(localVarLens "x" ℕ) = 1
-/
#guard_msgs in
example : equiv[ ={x} ==> ={x} ] {
      var x : ℕ;
      x <- §x + 1;
    } ~ {
      var x : ℕ;
      x <- §x + 1;
    } := by
  equiv_conseq (: ={x} ==> ={x}) _ (: True ==> §x{1} = 1)

end GaudisCrypt.ECConseqHoareTest
