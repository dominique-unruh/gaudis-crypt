import GaudisCrypt.Logic.ECProgress
import GaudisCrypt.Syntax.Syntax

/-!
# Golden tests of the closer on goals about values (`Logic/ECProgress.lean`)

See `Logic/ECAutoTest.lean` for the format; `scripts/update_golden.py` refreshes the expected
text.
-/

namespace GaudisCrypt.ECProgressTest

open GaudisCrypt

variable (P Q : ℤ → Prop)

/-! ## `ec_intros`, `ec_prep` -/

-- every binder introduced: the values under their names, the hypotheses without one
/--
trace: P Q : ℤ → Prop
a b : ℤ
a✝¹ : P a
c : ℤ
a✝ : a = c
⊢ Q b
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∀ a b : ℤ, P a → ∀ c : ℤ, a = c → Q b := by
  ec_intros
  trace_state
  sorry

-- the goal of `Logic/ECCloseTest.lean`'s `auto_prep` test: the same steps, the values named
/--
trace: P Q : ℤ → Prop
b c : ℤ
a✝ : Q c → P b
left✝ : P b
right✝ : b < c
⊢ Q b ∧ P c
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∀ a b c : ℤ, (P a ∧ a = b) ∧ decide (b < c) = true → (Q c → P b) → Q a ∧ P c := by
  ec_prep
  trace_state
  sorry

-- a witness (no name) equal to a value (named): the name stays
/--
trace: P Q : ℤ → Prop
a : ℤ
right✝ : Q a
⊢ P a
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∀ a : ℤ, (∃ w, w = a ∧ Q w) → P a := by
  ec_prep
  trace_state
  sorry

-- after `ec_auto`: the precondition taken apart, the test a proposition
/--
trace: P Q : ℤ → Prop
x : ℤ
left✝ : P x
right✝ : 0 ≤ x
⊢ Q (if x < 3 then x else 3)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : hoare[ P §x ∧ 0 ≤ §x ==> Q §y ] {
      var x : ℤ, y : ℤ;
      if (decide ($x < 3)) { y <- $x; } else { y <- 3; }
    } := by
  ec_auto
  ec_prep
  trace_state
  sorry

-- no step looks at a state: a frame between two states stays as it is (`auto_prep` rewrites
-- the later state's reads)
/--
trace: P Q : ℤ → Prop
x y : Lens ℤ VariableAssignment
σ τ : VariableAssignment
left✝¹ : P (x.get σ)
left✝ : x.get τ = x.get σ
right✝ : y.get τ = y.get σ + 1
⊢ Q (x.get τ + y.get τ)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (x y : Lens ℤ VariableAssignment) (σ τ : VariableAssignment) :
    P (x.get σ) ∧ x.get τ = x.get σ ∧ y.get τ = y.get σ + 1 → Q (x.get τ + y.get τ) := by
  ec_prep
  trace_state
  sorry

-- tuples of variables (EC's `sp` over `(p, n) <- e`): by components, then substituted
/--
trace: P Q : ℤ → Prop
R : ℤ → ℤ → Prop
e : ℤ × ℤ
a✝ : R e.1 e.2
⊢ R e.1 e.2
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) (e : ℤ × ℤ) :
    ∀ p n p' n' : ℤ, (p, n) = e → e = (p', n') → R p n → R p' n' := by
  ec_prep
  trace_state
  sorry

#guard_msgs in
example (R : ℤ → ℤ → Prop) (e : ℤ × ℤ) :
    ∀ p n p' n' : ℤ, (p, n) = e → e = (p', n') → R p n → R p' n' := by
  ec_close

/-! ## `ec_values`: the states first -/

-- a rule's side goal about two states (the guards of a two-sided `if`): the reads are values
/--
trace: P Q : ℤ → Prop
x : Lens ℤ ProgramState
⊢ ∀ (x₁ x₂ : ℤ), x₁ = x₂ ∧ P x₁ → decide (x₁ < 3) = decide (x₂ < 3)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (x : Lens ℤ ProgramState) : ∀ σ₁ σ₂ : ProgramState,
    x.get σ₁ = x.get σ₂ ∧ P (x.get σ₁) → (decide (x.get σ₁ < 3) = decide (x.get σ₂ < 3)) := by
  ec_values
  trace_state
  sorry

-- … and `ec_close` closes it
#guard_msgs in
example (x : Lens ℤ ProgramState) : ∀ σ₁ σ₂ : ProgramState,
    x.get σ₁ = x.get σ₂ ∧ P (x.get σ₁) → (decide (x.get σ₁ < 3) = decide (x.get σ₂ < 3)) := by
  ec_close

-- a state used other than by a read: an error, at the first phase
/--
error: ec_values: a state is still used after the reads are generalized
a state is used other than by a read in normal form in
  R σ✝
goal:
  ∀ (σ : ProgramState), R σ → R σ
-/
#guard_msgs in
example (R : ProgramState → Prop) : ∀ σ : ProgramState, R σ → R σ := by
  ec_close

-- states bound further in (the final memories of a `while` or `conseq`): values too, when the
-- introduction reaches them; the frame `x.get τ = x.get σ` is then an equation of values
/--
trace: P Q : ℤ → Prop
x y : Lens ℤ ProgramState
y1 x2 : ℤ
a✝ : P x2
⊢ Q (x2 + (y1 + 1))
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (x y : Lens ℤ ProgramState) : ∀ σ : ProgramState, P (x.get σ) →
    ∀ τ : ProgramState, x.get τ = x.get σ ∧ y.get τ = y.get σ + 1 → Q (x.get τ + y.get τ) := by
  ec_prep
  trace_state
  sorry

/-! ## `ec_progress`, `ec_close` -/

-- the goal split, what closes closed, the rest left
/--
trace: case right.left
P Q : ℤ → Prop
b : ℤ
left✝ : 0 ≤ b
right✝ : P b
⊢ Q b
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∀ a b : ℤ, 0 ≤ a ∧ a = b ∧ P a → 0 ≤ b + 1 ∧ Q b ∧ P b := by
  ec_progress
  trace_state
  sorry

-- a conditional conclusion: one goal per branch
/--
trace: case pos
P Q : ℤ → Prop
a : ℤ
a✝ : P a
h✝ : a < 3
⊢ Q a
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∀ a : ℤ, P a → if a < 3 then Q a else P a := by
  ec_progress
  trace_state
  sorry

-- `ec_close` closes
#guard_msgs in
example : ∀ a b : ℤ, (0 ≤ a ∧ a = b) → 0 ≤ b + 1 := by
  ec_close

-- … or fails, the goal as it was
/--
error: ec_close: a goal is left (state the lemmas EC's `smt` is given, or close it by hand)
P Q : ℤ → Prop
a : ℤ
a✝ : P a
⊢ Q a
-/
#guard_msgs in
example : ∀ a : ℤ, P a → Q a := by
  ec_close

end GaudisCrypt.ECProgressTest
