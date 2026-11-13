import GaudisCrypt.Logic.ECConseqHoare
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Syntax.Syntax

/-! Tests of `equiv_conseq (: P ==> Q) _ (: P₂ ==> Q₂)` and `equiv_conseq_pre H`
(`Logic/ECConseqHoare.lean`). -/

namespace GaudisCrypt.ECConseqHoareTest

open GaudisCrypt

module Twice {
  proc f (x : ℤ) : ℤ {
    return $x + $x
  };
}

theorem Twice_f (v : ℤ) : equiv[ Twice.f (x) ~ Twice.f (x) :
    §x{1} = v ∧ §x{2} = v ==> §res{1} = v + v ∧ §res{2} = v + v ] := by
  equiv_proc; equiv_auto

-- EC's `conseq (Twice_f 2)`: `post` needs what the precondition says about the arguments,
-- and has it (`equiv_conseq H` would leave `∀ r₁ g₁ r₂ g₂, … → r₁ = r₂ ∧ r₁ = 4` only)
/--
trace: case post
w : ℤ
⊢ ∀ (a₁ : (procsig (ℤ) → ℤ).ParamType) (g₁ : VariableAssignment) (a₂ : (procsig (ℤ) → ℤ).ParamType)
    (g₂ : VariableAssignment),
    (let params_1 := GaudiExpr[ a₁ ];
      let x_1 := GaudiExpr[ Lens.id.get a₁ ];
      let params_2 := GaudiExpr[ a₂ ];
      let x_2 := GaudiExpr[ Lens.id.get a₂ ];
      §x_1 = 2 ∧ §x_2 = 2 ∧ w = §x_1) →
      ∀ (r₁ : (procsig (ℤ) → ℤ).ret) (τ₁ : VariableAssignment) (r₂ : (procsig (ℤ) → ℤ).ret) (τ₂ : VariableAssignment),
        (have res_1 := GaudiExpr[ r₁ ];
          have res_2 := GaudiExpr[ r₂ ];
          §res_1 = 2 + 2 ∧ §res_2 = 2 + 2) →
          let res_1 := GaudiExpr[ r₁ ];
          let res_2 := GaudiExpr[ r₂ ];
          §res_1 = §res_2 ∧ §res_1 = w + w
-/
#guard_msgs in
example (w : ℤ) : equiv[ Twice.f (x) ~ Twice.f (x) :
    §x{1} = 2 ∧ §x{2} = 2 ∧ w = §x{1} ==> §res{1} = §res{2} ∧ §res{1} = w + w ] := by
  equiv_conseq_pre (Twice_f 2)
  · exact fun _ _ _ _ h => ⟨h.1, h.2.1⟩
  · trace_state
    rintro a₁ g₁ a₂ g₂ ⟨h1, -, hw⟩ r₁ τ₁ r₂ τ₂ ⟨k1, k2⟩
    replace h1 : @Eq ℤ a₁ 2 := h1
    replace hw : @Eq ℤ w a₁ := hw
    replace k1 : @Eq ℤ r₁ (2 + 2) := k1
    replace k2 : @Eq ℤ r₂ (2 + 2) := k2
    exact ⟨k1.trans k2.symm, by rw [hw, h1]; exact k1⟩

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
