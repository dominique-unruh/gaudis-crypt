import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Syntax.Syntax

/-!
# Golden tests of the closers (`Logic/ECClose.lean`)

Each test pins what a closer step leaves (see `Logic/ECAutoTest.lean` for the format;
`scripts/update_golden.py` refreshes the expected text).  The goals are stated over lenses `x`,
`y` into a state and uninterpreted predicates, the shape the judgment tactics leave: reads
`x.get σ`, frames `x.get τ = x.get σ`, tests `decide … = true`.
-/

namespace GaudisCrypt.ECCloseTest

open GaudisCrypt

variable (x y : Lens ℤ VariableAssignment) (z : Lens (ℤ × ℤ) VariableAssignment)
  (σ τ : VariableAssignment) (P Q : ℤ → Prop)

/-! ## `subst_reads` -/

-- a read equal to a named value: the read becomes the name everywhere
/--
trace: x y : Lens ℤ VariableAssignment
z : Lens (ℤ × ℤ) VariableAssignment
σ τ : VariableAssignment
P Q : ℤ → Prop
v : ℤ
h : True
hp : P v
⊢ Q (v + 1)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (v : ℤ) (h : x.get σ = v) (hp : P (x.get σ)) : Q (x.get σ + 1) := by
  subst_reads
  trace_state
  sorry

-- a read equal to an anonymous value: left alone
/--
trace: x y : Lens ℤ VariableAssignment
z : Lens (ℤ × ℤ) VariableAssignment
σ τ : VariableAssignment
P Q : ℤ → Prop
hp : P (x.get σ)
v✝ : ℤ
a✝ : x.get σ = v✝
⊢ Q (x.get σ + 1)
---
warning: declaration uses `sorry`
---
warning: 'subst_reads' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example (hp : P (x.get σ)) : ∀ v : ℤ, x.get σ = v → Q (x.get σ + 1) := by
  intros
  subst_reads
  trace_state
  sorry

-- a read equal to a tuple of names: the read becomes the tuple
/--
trace: x y : Lens ℤ VariableAssignment
z : Lens (ℤ × ℤ) VariableAssignment
σ τ : VariableAssignment
P Q : ℤ → Prop
a b : ℤ
h : True
⊢ Q a
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (a b : ℤ) (h : z.get σ = (a, b)) : Q (z.get σ).1 := by
  subst_reads
  trace_state
  sorry

-- a tuple of reads equal to a read (`sp` over `a, b <- z`): not used (Gconcl_list's GAP 1)
/--
trace: x y : Lens ℤ VariableAssignment
z : Lens (ℤ × ℤ) VariableAssignment
σ τ : VariableAssignment
P Q : ℤ → Prop
h : (x.get σ, y.get σ) = z.get σ
⊢ Q (z.get σ).1
---
warning: declaration uses `sorry`
---
warning: 'subst_reads' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example (h : (x.get σ, y.get σ) = z.get σ) : Q (z.get σ).1 := by
  subst_reads
  trace_state
  sorry

/-! ## `subst_frames` -/

-- a frame `x.get τ = x.get σ`: the later state's read becomes the earlier one's
/--
trace: x y : Lens ℤ VariableAssignment
z : Lens (ℤ × ℤ) VariableAssignment
σ τ : VariableAssignment
P Q : ℤ → Prop
hf : x.get τ = x.get σ
hp : P (x.get σ)
⊢ Q (x.get σ)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (hf : x.get τ = x.get σ) (hp : P (x.get τ)) : Q (x.get τ) := by
  subst_frames
  trace_state
  sorry

-- the same frame stated both ways round: one is dropped
/--
trace: x y : Lens ℤ VariableAssignment
z : Lens (ℤ × ℤ) VariableAssignment
σ τ : VariableAssignment
P Q : ℤ → Prop
hf : x.get τ = x.get σ
hp : P (x.get σ)
⊢ Q (x.get σ)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (hf : x.get τ = x.get σ) (hf' : x.get σ = x.get τ) (hp : P (x.get τ)) : Q (x.get σ) := by
  subst_frames
  trace_state
  sorry

/-! ## `mp_hyps`, `subst_named` -/

-- an implication whose premise is a hypothesis: its conclusion
/--
trace: x y : Lens ℤ VariableAssignment
z : Lens (ℤ × ℤ) VariableAssignment
σ τ : VariableAssignment
P Q : ℤ → Prop
A B : Prop
ha : A
h : B
hq : Q 0
⊢ Q 0
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (A B : Prop) (ha : A) (h : A → B) (hq : B → Q 0) : Q 0 := by
  mp_hyps
  trace_state
  sorry

-- a named value equal to an anonymous one: the anonymous one goes
/--
trace: x y : Lens ℤ VariableAssignment
z : Lens (ℤ × ℤ) VariableAssignment
σ τ : VariableAssignment
P Q : ℤ → Prop
v : ℤ
a✝ : P v
⊢ Q v
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (v : ℤ) : ∀ w : ℤ, v = w → P w → Q v := by
  intro _ _ _
  subst_named
  trace_state
  sorry

/-! ## `auto_prep` -/

-- a typical goal after `skip`: what is introduced, taken apart and substituted, and in which
-- order the hypotheses come out
/--
trace: x y : Lens ℤ VariableAssignment
z : Lens (ℤ × ℤ) VariableAssignment
σ τ : VariableAssignment
P Q : ℤ → Prop
b✝ c✝ : ℤ
a✝ : Q c✝ → P b✝
left✝ : P b✝
right✝ : b✝ < c✝
⊢ Q b✝ ∧ P c✝
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∀ a b c : ℤ, (P a ∧ a = b) ∧ decide (b < c) = true → (Q c → P b) → Q a ∧ P c := by
  auto_prep
  trace_state
  sorry

-- reads of two states with a frame between them
/--
trace: x y : Lens ℤ VariableAssignment
z : Lens (ℤ × ℤ) VariableAssignment
σ τ : VariableAssignment
P Q : ℤ → Prop
left✝¹ : P (x.get σ)
left✝ : x.get τ = x.get σ
right✝ : y.get τ = y.get σ + 1
⊢ Q (x.get σ + y.get τ)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : P (x.get σ) ∧ x.get τ = x.get σ ∧ y.get τ = y.get σ + 1 → Q (x.get τ + y.get τ) := by
  auto_prep
  trace_state
  sorry

/-! ## `auto_close`, `auto_progress`, `smt_close` -/

-- `auto_close` closes or fails; it never leaves a changed goal
#guard_msgs in
example : ∀ a b : ℤ, (0 ≤ a ∧ a = b) → 0 ≤ b + 1 := by
  auto_close

/--
error: auto_close: a goal is left (state the lemmas EC's `smt` is given, or close it by hand)
x y : Lens ℤ VariableAssignment
z : Lens (ℤ × ℤ) VariableAssignment
σ τ : VariableAssignment
P Q : ℤ → Prop
a✝¹ : ℤ
a✝ : P a✝¹
⊢ Q a✝¹
-/
#guard_msgs in
example : ∀ a : ℤ, P a → Q a := by
  auto_close

-- `auto_progress` leaves what it cannot close, one goal per conjunct
/--
trace: case right.left
x y : Lens ℤ VariableAssignment
z : Lens (ℤ × ℤ) VariableAssignment
σ τ : VariableAssignment
P Q : ℤ → Prop
b✝ : ℤ
left✝ : P b✝
⊢ Q b✝
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∀ a b : ℤ, (P a ∧ a = b) → P b ∧ Q a ∧ a ≤ b := by
  auto_progress
  trace_state
  sorry

-- `smt_close` with EC's hint lemmas (constants), instantiated on the goal's terms
#guard_msgs in
example : ∀ a b : ℤ, a = |b| → 0 ≤ a := by
  smt_close [abs_nonneg]

-- a hint must be a constant: a hypothesis is not accepted
/--
error: Unknown constant `hf`
-/
#guard_msgs in
example (f : ℤ → ℤ) (hf : ∀ n, 0 ≤ f n) : ∀ a b : ℤ, a = f b → 0 ≤ a := by
  smt_close [hf]

-- the tuple chain of `sp` over `a, b <- z` (Gconcl_list's GAP 1): `auto_close` does not use it
/--
error: auto_close: a goal is left (state the lemmas EC's `smt` is given, or close it by hand)
x y : Lens ℤ VariableAssignment
z : Lens (ℤ × ℤ) VariableAssignment
σ τ : VariableAssignment
P Q : ℤ → Prop
a✝ : P (x.get σ)
left✝ : (x.get σ, y.get σ) = z.get σ
right✝ : (x.get τ, y.get τ) = z.get σ
⊢ P (x.get τ)
-/
#guard_msgs in
example : (x.get σ, y.get σ) = z.get σ ∧ (x.get τ, y.get τ) = z.get σ → P (x.get σ) → P (x.get τ) := by
  auto_close

end GaudisCrypt.ECCloseTest
