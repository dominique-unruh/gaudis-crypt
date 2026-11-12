import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Syntax.Syntax

/-!
# Golden tests of EC's `auto` (`Logic/ECAuto.lean`)

Each test pins what a tactic leaves: the goals, their order, tags and shape, as `trace_state`
prints them (`#guard_msgs`).  A change of a tactic that changes its output changes a test here;
update the expected text (`scripts/update_golden.py`) only when the change is intended.  The
goals are then given up (`sorry`, its warning part of the expected text): the tests are about
the tactic's output, not about closing it.  The conditions use uninterpreted predicates (`P`,
`Q`, `R`) so that the closers inside the tactic leave the goal.
-/

namespace GaudisCrypt.ECAutoTest

open GaudisCrypt

global_var autoCount : ℤ

/-! ## `hoare_auto` -/

-- straight-line code: wp to the start, then `skip`; the reads are values
/--
trace: P Q : ℤ → Prop
⊢ ∀ (x : ℤ), P x → Q (x + 1)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → Prop) : hoare[ P §x ==> Q §y ] {
      var x : ℤ, y : ℤ;
      y <- $x + 1;
    } := by
  hoare_auto
  trace_state
  sorry

-- a global, a conditional and a sampling
/--
trace: P Q : ℤ → Prop
⊢ ∀ (autoCount : ℤ), P autoCount → ∀ (a : Bool), Q (if a = true then autoCount + 1 else autoCount)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → Prop) : hoare[ P §autoCount ==> Q §autoCount ] {
      var b : Bool;
      b <$ SubProbability.uniform;
      if ($b) {
        autoCount <- $autoCount + 1;
      }
    } := by
  hoare_auto
  trace_state
  sorry

-- after `sp`: the precondition's reads are through the writes `sp` went over, the same values
-- as the postcondition's (Gconcl_list's GAP 3)
/--
trace: case h
P Q : ℤ → Prop
⊢ ∀ (x : ℤ), (∃ v, P v ∧ x = v + 1) → Q x
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → Prop) : hoare[ P §x ==> Q §x ] {
      var x : ℤ;
      x <- $x + 1;
    } := by
  stmt_sp
  hoare_auto
  trace_state
  sorry

-- a goal its closer proves leaves nothing
#guard_msgs in
example : hoare[ 0 ≤ §x ==> 0 < §y ] {
      var x : ℤ, y : ℤ;
      y <- $x + 1;
    } := by
  hoare_auto

/-! ## `equiv_auto` -/

-- deterministic code on both sides: the two sides' reads are values named by side
/--
trace: case h
R : ℤ → ℤ → Prop
⊢ ∀ (x₁ x₂ : ℤ), x₁ = x₂ → R x₁ (x₂ + 1)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) : equiv[ ={x} ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      y <- $x;
    } ~ {
      var x : ℤ, y : ℤ;
      y <- $x + 1;
    } := by
  equiv_auto
  trace_state
  sorry

-- a sampling on both sides: coupled by `rnd`
/--
trace: case h
R : Bool → Bool → Prop
⊢ True → ∀ (a : Bool), R a a
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : Bool → Bool → Prop) : equiv[ True ==> R §b{1} §b{2} ] {
      var b : Bool;
      b <$ SubProbability.uniform;
    } ~ {
      var b : Bool;
      b <$ SubProbability.uniform;
    } := by
  equiv_auto
  trace_state
  sorry

-- a sampling on one side only
/--
trace: case h
R : Bool → ℤ → Prop
⊢ ∀ (x₁ x₂ : ℤ), x₁ = x₂ → ∀ (a : Bool), R a x₂
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : Bool → ℤ → Prop) : equiv[ ={x} ==> R §b{1} §x{2} ] {
      var x : ℤ, b : Bool;
      b <$ SubProbability.uniform;
    } ~ {
      var x : ℤ;
      skip;
    } := by
  equiv_auto
  trace_state
  sorry

-- a goal its closer proves leaves nothing
#guard_msgs in
example : equiv[ ={x} ==> §y{1} ≤ §y{2} ] {
      var x : ℤ, y : ℤ;
      y <- $x;
    } ~ {
      var x : ℤ, y : ℤ;
      y <- $x + 1;
    } := by
  equiv_auto

end GaudisCrypt.ECAutoTest
