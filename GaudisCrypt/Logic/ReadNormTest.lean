import GaudisCrypt.Logic.ReadNorm
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECInline
import GaudisCrypt.Syntax.Syntax

/-!
# Golden tests of the read normal form and `ec_skip` (`Logic/ReadNorm.lean`)

See `Logic/ECAutoTest.lean` for the format; `scripts/update_golden.py` refreshes the expected
text.
-/

namespace GaudisCrypt.ReadNormTest

open GaudisCrypt

global_var rnCount : ℤ

moduletype Tick {
  proc tick (x : ℤ) -> ℤ;
}

module Bound : Tick {
  proc tick (x : ℤ) : ℤ {
    var y : ℤ;
    y <- 0;
    if (decide ($rnCount < 3)) {
      rnCount <- $rnCount + 1;
      y <- $x;
    }
    return $y
  };
}

/-! ## A test in inlined code (`if (decide …)`) -/

-- a procedure with a test, inlined: `hoare_auto` today
/--
warning: hoare_auto: the reads are not generalized: the goal stays about the states
reason: Tactic `generalize` failed: result is not type correct
  ∀ (rnCount : ℤ), P rnCount → Q (if decide (rnCount < 3) = true then rnCount + 1 else rnCount)

P Q : ℤ → Prop
σ✝ : ProgramState
⊢ P (rnCount.get σ✝.globals) →
    Q (if decide (rnCount.get σ✝.globals < 3) = true then rnCount.get σ✝.globals + 1 else rnCount.get σ✝.globals)
---
trace: P Q : ℤ → Prop
⊢ ∀ (σ : ProgramState),
    P (rnCount.get σ.globals) →
      Q (if decide (rnCount.get σ.globals < 3) = true then rnCount.get σ.globals + 1 else rnCount.get σ.globals)
---
warning: declaration uses `sorry`
---
warning: 'hoare_inline*' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example (P Q : ℤ → Prop) : hoare[ Bound.tick : P §rnCount ==> Q §rnCount ] := by
  hoare_proc
  hoare_inline*
  hoare_auto
  trace_state
  sorry

-- the same with `ec_skip`
/--
trace: P Q : ℤ → Prop
⊢ ∀ (rnCount : ℤ), P rnCount → Q (if decide (rnCount < 3) = true then rnCount + 1 else rnCount)
---
warning: declaration uses `sorry`
---
warning: 'hoare_inline*' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example (P Q : ℤ → Prop) : hoare[ Bound.tick : P §rnCount ==> Q §rnCount ] := by
  hoare_proc
  hoare_inline*
  stmt_wp
  ec_skip
  trace_state
  sorry

/-! ## A test in the code (`if (decide …)`) -/

-- today: `hoare_auto` leaves the goal about the state, with a warning (the `decide`'s instance
-- spells the read differently, so the read does not generalize)
/--
trace: P Q : ℤ → Prop
⊢ ∀ (rnCount : ℤ), P rnCount → Q (if decide (rnCount < 3) = true then rnCount + 1 else rnCount)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → Prop) : hoare[ P §rnCount ==> Q §rnCount ] {
      if (decide ($rnCount < 3)) {
        rnCount <- $rnCount + 1;
      }
    } := by
  hoare_auto
  trace_state
  sorry

-- `ec_skip` after `wp`: normalized first, every read a value
/--
trace: P Q : ℤ → Prop
⊢ ∀ (rnCount : ℤ), P rnCount → Q (if decide (rnCount < 3) = true then rnCount + 1 else rnCount)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → Prop) : hoare[ P §rnCount ==> Q §rnCount ] {
      if (decide ($rnCount < 3)) {
        rnCount <- $rnCount + 1;
      }
    } := by
  stmt_wp
  ec_skip
  trace_state
  sorry

/-! ## `ec_skip` on the three judgments -/

-- a Hoare triple, a local and a global
/--
trace: P Q : ℤ → ℤ → Prop
⊢ ∀ (x rnCount : ℤ), P x rnCount → Q (x + 1) (rnCount + (x + 1))
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → ℤ → Prop) : hoare[ P §x §rnCount ==> Q §y §rnCount ] {
      var x : ℤ, y : ℤ;
      y <- $x + 1;
      rnCount <- $rnCount + $y;
    } := by
  stmt_wp
  ec_skip
  trace_state
  sorry

-- after `sp`: the reads through the writes `sp` went over
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
  ec_skip
  trace_state
  sorry

-- a relational judgment: the values named by side
/--
trace: case h
R S : ℤ → ℤ → Prop
⊢ ∀ (x₁ rnCount₂ : ℤ), R x₁ rnCount₂ → S (if decide (x₁ < 3) = true then x₁ else 0) (rnCount₂ + 1)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R S : ℤ → ℤ → Prop) : equiv[ R §x{1} §rnCount{2} ==> S §y{1} §rnCount{2} ] {
      var x : ℤ, y : ℤ;
      if (decide ($x < 3)) { y <- $x; } else { y <- 0; }
    } ~ {
      rnCount <- $rnCount + 1;
    } := by
  stmt_wp
  ec_skip
  trace_state
  sorry

/-! ## `ec_auto`, `ec_intro` -/

-- `ec_auto` on inlined code with a test: wp, then the strict skip
/--
trace: P Q : ℤ → Prop
⊢ ∀ (rnCount : ℤ), P rnCount → Q (if decide (rnCount < 3) = true then rnCount + 1 else rnCount)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → Prop) : hoare[ Bound.tick : P §rnCount ==> Q §rnCount ] := by
  hoare_proc
  ec_auto
  trace_state
  sorry

-- `ec_intro`: the generalized values in the context under their names; the hypotheses stay
/--
trace: P Q : ℤ → ℤ → Prop
x rnCount : ℤ
⊢ P x rnCount → Q (x + 1) rnCount
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → ℤ → Prop) : hoare[ P §x §rnCount ==> Q §y §rnCount ] {
      var x : ℤ, y : ℤ;
      y <- $x + 1;
    } := by
  ec_auto
  ec_intro
  trace_state
  sorry

-- `ec_auto` on a relational judgment with samplings
/--
trace: case h
R : Bool → Bool → Prop
⊢ ∀ (x₁ x₂ : ℤ), x₁ = x₂ → ∀ (a : Bool), R a a ∧ x₁ = x₂
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : Bool → Bool → Prop) : equiv[ ={x} ==> R §b{1} §b{2} ∧ ={x} ] {
      var x : ℤ, b : Bool;
      b <$ SubProbability.uniform;
    } ~ {
      var x : ℤ, b : Bool;
      b <$ SubProbability.uniform;
    } := by
  ec_auto
  trace_state
  sorry

-- a goal `ec_auto`'s closer proves leaves nothing
#guard_msgs in
example : hoare[ 0 ≤ §x ==> 0 < §y ] {
      var x : ℤ, y : ℤ;
      y <- $x + 1;
    } := by
  ec_auto

-- the code not used up (a loop): the judgment is left there
/--
trace: P Q : ℤ → Prop
⊢ hoare[ P §n ==> Q (§i + 1) ] {
      var n : ℤ, i : ℤ;
      while (decide (§i < §n)) {
        i <- §i + 1;
      }
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → Prop) : hoare[ P §n ==> Q §i ] {
      var i : ℤ, n : ℤ;
      while (decide ($i < $n)) { i <- $i + 1; }
      i <- $i + 1;
    } := by
  ec_auto
  trace_state
  sorry

/-! ## The instance of an `if` -/

-- an `if` whose instance is not synthesized (a conjunction with a classical part) and spells the
-- read through a write, as a call rule leaves it: re-made for the condition as it stands
/--
trace: Q : ℤ → Prop
⊢ ∀ (rnCount : ℤ), if 0 ≤ rnCount ∧ ∀ (k : ℕ), ↑k ≤ rnCount then Q rnCount else True
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (Q : ℤ → Prop) :
    hoareStmt (fun _ => True) StmtWithHoles.skip
      (fun σ => @ite Prop
        (0 ≤ rnCount.get σ.globals ∧ ∀ k : ℕ, (k : ℤ) ≤ rnCount.get σ.globals)
        (@instDecidableAnd _ _
          (Classical.propDecidable
            (0 ≤ rnCount.get (ProgramState.globalL.set σ.globals σ).globals))
          (Classical.propDecidable
            (∀ k : ℕ, (k : ℤ) ≤ rnCount.get (ProgramState.globalL.set σ.globals σ).globals)))
        (Q (rnCount.get σ.globals)) True) := by
  ec_skip
  trace_state
  sorry

/-! ## Strictness -/

-- a state used other than by a read: `ec_skip` fails and names the places (`hoare_skip` leaves
-- the goal about the state)
/--
error: ec_skip: a state is still used after the reads are generalized
a state is used other than by a read in normal form in
  P σ✝
  Q σ✝
goal:
  ∀ (σ : ProgramState), P σ → Q σ
-/
#guard_msgs in
example (P Q : ProgramState → Prop) : hoareStmt P StmtWithHoles.skip Q := by
  ec_skip

/--
trace: P Q : ProgramState → Prop
⊢ ∀ (σ : ProgramState), P σ → Q σ
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ProgramState → Prop) : hoareStmt P StmtWithHoles.skip Q := by
  hoare_skip
  trace_state
  sorry

end GaudisCrypt.ReadNormTest
