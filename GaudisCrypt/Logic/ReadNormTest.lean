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

-- the same in strict mode (`set_option ec.strict true`): the old tactic, when the reads do not
-- generalize, normalizes the instances and tries again; the read is a value, no warning
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
set_option ec.strict true in
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

-- a test written in the code itself: `hoare_auto` generalizes the read (the instance is spelled
-- as the test is; it is the procedure's test above that is not)
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

/-! ## The names of the values -/

global_var RnA.c : ℤ
global_var RnB.c : ℤ

-- a module's variable alone: its last name
/--
trace: P Q : ℤ → Prop
⊢ ∀ (c : ℤ), P c → Q (c + 1)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → Prop) : hoare[ P §RnA.c ==> Q §RnA.c ] { RnA.c <- $RnA.c + 1; } := by
  ec_auto
  trace_state
  sorry

-- the name taken in the context: the module's name with it (not a number)
/--
trace: c : ℤ
P Q : ℤ → ℤ → Prop
⊢ ∀ (RnA_c : ℤ), P c RnA_c → Q c (RnA_c + 1)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (c : ℤ) (P Q : ℤ → ℤ → Prop) : hoare[ P c §RnA.c ==> Q c §RnA.c ] {
      RnA.c <- $RnA.c + 1;
    } := by
  ec_auto
  trace_state
  sorry

-- two modules' variables of one name, and a local of that name: the local keeps it
/--
trace: P Q : ℤ → ℤ → ℤ → Prop
⊢ ∀ (RnA_c RnB_c c : ℤ), P RnA_c RnB_c c → Q RnA_c RnB_c (c + 1)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → ℤ → ℤ → Prop) : hoare[ P §RnA.c §RnB.c §c ==> Q §RnA.c §RnB.c §c ] {
      var c : ℤ;
      c <- $c + 1;
    } := by
  ec_auto
  trace_state
  sorry

-- by side on a relational judgment
/--
trace: case h
R S : ℤ → ℤ → ℤ → Prop
⊢ ∀ (RnA_c₁ RnB_c₁ c₂ : ℤ), R RnA_c₁ RnB_c₁ c₂ → S (RnA_c₁ + 1) RnB_c₁ (c₂ + 1)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R S : ℤ → ℤ → ℤ → Prop) :
    equiv[ R §RnA.c{1} §RnB.c{1} §RnA.c{2} ==> S §RnA.c{1} §RnB.c{1} §RnA.c{2} ] {
      RnA.c <- $RnA.c + 1;
    } ~ {
      RnA.c <- $RnA.c + 1;
    } := by
  ec_auto
  trace_state
  sorry

-- a place under a binder is printed with the binder's variable
/--
error: ec_skip: a state is still used after the reads are generalized
a state is used other than by a read in normal form in
  P σ✝ k
goal:
  ∀ (σ : ProgramState), (∀ (k : ℤ), P σ k) → Q
-/
#guard_msgs in
example (P : ProgramState → ℤ → Prop) (Q : Prop) :
    hoareStmt (fun σ => ∀ k : ℤ, P σ k) StmtWithHoles.skip (fun _ => Q) := by
  ec_skip

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
