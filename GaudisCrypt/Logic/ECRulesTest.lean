import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Logic.ECLoop
import GaudisCrypt.Logic.ECSeq
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECWhileRel
import GaudisCrypt.Syntax.Syntax

/-!
# Golden tests of the program-step rules on code without calls

`sp`, `wp`, `skip`, `if`, `rcondt`/`rcondf`, `case`, `seq`, `conseq`, `while`, `splitwhile`,
`unroll`, `rnd`: each test pins the goals a rule leaves (count, order, tags, conditions and code),
as `trace_state` prints them (see `Logic/ECAutoTest.lean` for the format;
`scripts/update_golden.py` refreshes the expected text).  The conditions use uninterpreted
predicates.
-/

namespace GaudisCrypt.ECRulesTest

open GaudisCrypt

global_var rCount : ℤ

/-! ## `sp`, `wp`, `skip` -/

-- `sp` on a Hoare triple: the assignments go into the precondition
/--
trace: case h
P Q : ℤ → ℤ → Prop
⊢ hoare[
      let σ := CurrentState.state;
      ∃ τ,
        (∃ v, (P (x.get τ) v ∧ y.get τ = x.get τ + 1) ∧ rCount.get τ.globals = v + y.get τ) ∧
          σ = if decide (Evaluatable.eval τ y < 3) = true then (liftLens x).set 0 τ else id τ ==>
      Q §x §y ] {
      var x : ℤ, y : ℤ;
      skip;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → ℤ → Prop) : hoare[ P §x §rCount ==> Q §x §y ] {
      var x : ℤ, y : ℤ;
      y <- $x + 1;
      rCount <- $rCount + $y;
      if (decide ($y < 3)) { x <- 0; }
    } := by
  stmt_sp
  trace_state
  sorry

-- `sp` on both sides of a relational judgment
/--
trace: case h
R : ℤ → ℤ → Prop
⊢ prhlStmt
    (fun σ₁ σ₂ ↦
      (∃ v,
          (∃ τ,
              (§(localVarLens "x" ℤ) = §(localVarLens "x" ℤ) ∧
                  (localVarLens "y" ℤ).get τ = GaudiExpr[ §(localVarLens "x" ℤ) ].get τ) ∧
                σ₁ =
                  if GaudiExpr[ decide (§(localVarLens "y" ℤ) < 3) ].get τ = true then
                    (liftLens (localVarLens "y" ℤ)).set (GaudiExpr[ 0 ].get τ) τ
                  else id τ) ∧
            (localVarLens "x" ℤ).get σ₂ = GaudiExpr[ §(localVarLens "x" ℤ) + 1 ].get ((localVarLens "x" ℤ).set v σ₂)) ∧
        (localVarLens "y" ℤ).get σ₂ = GaudiExpr[ §(localVarLens "x" ℤ) ].get σ₂)
    (GaudiProg[
        skip;
  ])
    (GaudiProg[
        skip;
  ])
    fun σ₁ σ₂ ↦ R §(localVarLens "y" ℤ) §(localVarLens "y" ℤ)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) : equiv[ ={x} ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      y <- $x;
      if (decide ($y < 3)) { y <- 0; }
    } ~ {
      var x : ℤ, y : ℤ;
      x <- $x + 1;
      y <- $x;
    } := by
  stmt_sp
  trace_state
  sorry

-- `sp` over a tuple assignment
/--
trace: case h
P Q : ℤ → ℤ → Prop
⊢ hoare[
      let σ := CurrentState.state;
      ∃ τ,
        (P (Evaluatable.eval τ z).1 (Evaluatable.eval τ z).2 ∧ (x.pair y).get τ = Evaluatable.eval τ z) ∧
          σ = if decide (Evaluatable.eval τ x < Evaluatable.eval τ y) = true then (liftLens x).set 0 τ else id τ ==>
      Q §x §y ] {
      var z : ℤ × ℤ, x : ℤ, y : ℤ;
      skip;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → ℤ → Prop) : hoare[ P (§z).1 (§z).2 ==> Q §x §y ] {
      var z : ℤ × ℤ, x : ℤ, y : ℤ;
      x, y <- $z;
      if (decide ($x < $y)) { x <- 0; }
    } := by
  stmt_sp
  trace_state
  sorry

-- `wp` over the trailing deterministic code
/--
trace: R : ℤ → ℤ → Prop
⊢ equiv[ §x{1} = §x{2} ==> R §x{1} (§x{2} + 1) ] {
      var x : ℤ, b : Bool;
      b <$ SubProbability.uniform;
} ~ {
      var b : Bool;
      b <$ SubProbability.uniform;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) : equiv[ ={x} ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ, b : Bool;
      b <$ SubProbability.uniform;
      y <- $x;
    } ~ {
      var x : ℤ, y : ℤ, b : Bool;
      b <$ SubProbability.uniform;
      y <- $x + 1;
    } := by
  stmt_wp
  trace_state
  sorry

-- EC's `wp n m`: the first `n` and `m` statements stay
/--
trace: R : ℤ → ℤ → Prop
⊢ equiv[ §x{1} = §x{2} ==> R (§x{1} + 1) (§x{2} + 1) ] {
      var x : ℤ;
      x <- §x + 1;
} ~
    {
      skip;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) : equiv[ ={x} ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      x <- $x + 1;
      y <- $x;
      y <- $y + 1;
    } ~ {
      var x : ℤ, y : ℤ;
      y <- $x + 1;
    } := by
  stmt_wp 1 0
  trace_state
  sorry

-- `skip` on a relational judgment: EC's form (`equiv_skip_ec`) and the old one (`equiv_skip`)
/--
trace: case h
R S : ℤ → ℤ → Prop
⊢ ∀ (x₁ rCount₂ : ℤ), R x₁ rCount₂ → S x₁ rCount₂
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R S : ℤ → ℤ → Prop) : equiv[ R §x{1} §rCount{2} ==> S §x{1} §rCount{2} ] {
      var x : ℤ;
      skip;
    } ~ {
      skip;
    } := by
  equiv_skip_ec
  trace_state
  sorry

/--
trace: case h
R S : ℤ → ℤ → Prop
⊢ ∀ (x₁ rCount₂ : ℤ), R x₁ rCount₂ → S x₁ rCount₂
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R S : ℤ → ℤ → Prop) : equiv[ R §x{1} §rCount{2} ==> S §x{1} §rCount{2} ] {
      var x : ℤ;
      skip;
    } ~ {
      skip;
    } := by
  equiv_skip
  trace_state
  sorry

-- `skip` on a Hoare triple
/--
trace: P Q : ℤ → Prop
⊢ ∀ (rCount : ℤ), P rCount → Q rCount
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q : ℤ → Prop) : hoare[ P §rCount ==> Q §rCount ] {
      skip;
    } := by
  hoare_skip
  trace_state
  sorry

/-! ## `if`, `rcondt`, `rcondf`, `case` -/

-- `if` on both sides: EC's goals, the guards' agreement, then the branches with the code after
/--
trace: case guard
R : ℤ → ℤ → Prop
⊢ ∀ (σ₁ σ₂ : ProgramState),
    §(localVarLens "x" ℤ) = §(localVarLens "x" ℤ) →
      GaudiExpr[ decide (§(localVarLens "x" ℤ) < 3) ].get σ₁ = GaudiExpr[ decide (§(localVarLens "x" ℤ) < 3) ].get σ₂

case then
R : ℤ → ℤ → Prop
⊢ equiv[ §x{1} = §x{2} ∧ decide (§x{1} < 3) = true ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      y <- 1;
      y <- §y + 1;
} ~ {
      var y : ℤ;
      y <- 3;
}

case else
R : ℤ → ℤ → Prop
⊢ equiv[ §x{1} = §x{2} ∧ decide (§x{1} < 3) = false ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      y <- 2;
      y <- §y + 1;
} ~ {
      var y : ℤ;
      y <- 4;
}
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 3 goals and ends with 3 goals, 3 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) : equiv[ ={x} ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      if (decide ($x < 3)) { y <- 1; } else { y <- 2; }
      y <- $y + 1;
    } ~ {
      var x : ℤ, y : ℤ;
      if (decide ($x < 3)) { y <- 3; } else { y <- 4; }
    } := by
  stmt_if
  trace_state
  all_goals sorry

-- `if{1}`: one side, no guard goal
/--
trace: case then
R : ℤ → ℤ → Prop
⊢ equiv[ §x{1} = §x{2} ∧ decide (§x{1} < 3) = true ==> R §y{1} §y{2} ] {
      var y : ℤ;
      y <- 1;
} ~ {
      var x : ℤ, y : ℤ;
      y <- §x;
}

case else
R : ℤ → ℤ → Prop
⊢ equiv[ §x{1} = §x{2} ∧ decide (§x{1} < 3) = false ==> R §y{1} §y{2} ] {
      skip;
} ~ {
      var x : ℤ, y : ℤ;
      y <- §x;
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
example (R : ℤ → ℤ → Prop) : equiv[ ={x} ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      if (decide ($x < 3)) { y <- 1; }
    } ~ {
      var x : ℤ, y : ℤ;
      y <- $x;
    } := by
  stmt_if{1}
  trace_state
  all_goals sorry

-- `if` on a Hoare triple
/--
trace: case then
P Q : ℤ → Prop
⊢ hoare[ P §x ∧ decide (§x < 3) = true ==> Q §y ] {
      var x : ℤ, y : ℤ;
      y <- 1;
}

case else
P Q : ℤ → Prop
⊢ hoare[ P §x ∧ decide (§x < 3) = false ==> Q §y ] {
      var x : ℤ, y : ℤ;
      y <- 2;
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
example (P Q : ℤ → Prop) : hoare[ P §x ==> Q §y ] {
      var x : ℤ, y : ℤ;
      if (decide ($x < 3)) { y <- 1; } else { y <- 2; }
    } := by
  stmt_if
  trace_state
  all_goals sorry

-- `rcondt{1} n` on a conditional: the test's goal (a Hoare triple on the code before, for every
-- state of the other side), then the judgment with the branch spliced in
/--
trace: case cond
R : ℤ → ℤ → Prop
⊢ ∀ (σ₂ : ProgramState),
    hoare[ §x = Evaluatable.eval σ₂ x ==> decide (§x < 3) = true ] {
        var x : ℤ;
        x <- 0;
  }

case h
R : ℤ → ℤ → Prop
⊢ equiv[ §x{1} = §x{2} ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      x <- 0;
      y <- 1;
} ~ {
      var x : ℤ, y : ℤ;
      y <- §x;
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
example (R : ℤ → ℤ → Prop) : equiv[ ={x} ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      x <- 0;
      if (decide ($x < 3)) { y <- 1; } else { y <- 2; }
    } ~ {
      var x : ℤ, y : ℤ;
      y <- $x;
    } := by
  stmt_rcondt{1} 2
  trace_state
  all_goals sorry

-- `rcondt{1} n` on a loop: unrolled, its body before it
/--
trace: case cond
R : ℤ → ℤ → Prop
⊢ ∀ (σ₂ : ProgramState),
    hoare[ §n = Evaluatable.eval σ₂ n ==> decide (§i < §n) = true ] {
        var n : ℤ, i : ℤ;
        i <- 0;
  }

case h
R : ℤ → ℤ → Prop
⊢ equiv[ §n{1} = §n{2} ==> R §i{1} §n{2} ] {
      var n : ℤ, i : ℤ;
      i <- 0;
      i <- §i + 1;
      while (decide (§i < §n)) {
        i <- §i + 1;
      }
} ~
    {
      skip;
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
example (R : ℤ → ℤ → Prop) : equiv[ ={n} ==> R §i{1} §n{2} ] {
      var i : ℤ, n : ℤ;
      i <- 0;
      while (decide ($i < $n)) { i <- $i + 1; }
    } ~ {
      var n : ℤ;
      skip;
    } := by
  stmt_rcondt{1} 2
  trace_state
  all_goals sorry

-- `rcondf{1} n` on a loop: the loop is gone
/--
trace: case cond
R : ℤ → ℤ → Prop
⊢ ∀ (σ₂ : ProgramState),
    hoare[ §n = Evaluatable.eval σ₂ n ==> decide (§i < §n) = false ] {
        var n : ℤ, i : ℤ;
        i <- §n;
  }

case h
R : ℤ → ℤ → Prop
⊢ equiv[ §n{1} = §n{2} ==> R §i{1} §n{2} ] {
      var n : ℤ, i : ℤ;
      i <- §n;
} ~
    {
      skip;
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
example (R : ℤ → ℤ → Prop) : equiv[ ={n} ==> R §i{1} §n{2} ] {
      var i : ℤ, n : ℤ;
      i <- $n;
      while (decide ($i < $n)) { i <- $i + 1; }
    } ~ {
      var n : ℤ;
      skip;
    } := by
  stmt_rcondf{1} 2
  trace_state
  all_goals sorry

-- `rcondf n` on a Hoare triple
/--
trace: case cond
P Q : ℤ → Prop
⊢ hoare[ P §x ==> decide (§x < 3) = false ] {
      var x : ℤ;
      x <- 5;
}

case h
P Q : ℤ → Prop
⊢ hoare[ P §x ==> Q §y ] {
      var x : ℤ, y : ℤ;
      x <- 5;
      y <- 2;
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
example (P Q : ℤ → Prop) : hoare[ P §x ==> Q §y ] {
      var x : ℤ, y : ℤ;
      x <- 5;
      if (decide ($x < 3)) { y <- 1; } else { y <- 2; }
    } := by
  stmt_rcondf 2
  trace_state
  all_goals sorry

-- `case`: the condition, then its negation, in the precondition
/--
trace: case hp
R : ℤ → ℤ → Prop
⊢ equiv[ §x{1} = §x{2} ∧ 0 < §x{1} ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      y <- §x;
} ~ {
      var x : ℤ, y : ℤ;
      y <- §x;
}

case hn
R : ℤ → ℤ → Prop
⊢ equiv[ §x{1} = §x{2} ∧ ¬0 < §x{1} ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      y <- §x;
} ~ {
      var x : ℤ, y : ℤ;
      y <- §x;
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
example (R : ℤ → ℤ → Prop) : equiv[ ={x} ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      y <- $x;
    } ~ {
      var x : ℤ, y : ℤ;
      y <- $x;
    } := by
  equiv_case (0 < §x{1})
  trace_state
  all_goals sorry

/-! ## `seq`, `conseq` -/

-- EC's `seq n m : P`: the code up to the cut with `P` after it, then the rest from `P`
/--
trace: case h₁
R S : ℤ → ℤ → Prop
⊢ equiv[ §x{1} = §x{2} ==> S §x{1} §x{2} ] {
      var x : ℤ;
      x <- §x + 1;
} ~
    {
      skip;
}

case h₂
R S : ℤ → ℤ → Prop
⊢ equiv[ S §x{1} §x{2} ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      y <- §x;
} ~ {
      var x : ℤ, y : ℤ;
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
example (R S : ℤ → ℤ → Prop) : equiv[ ={x} ==> R §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      x <- $x + 1;
      y <- $x;
    } ~ {
      var x : ℤ, y : ℤ;
      y <- $x + 1;
    } := by
  equiv_seq 1 0 : (S §x{1} §x{2})
  trace_state
  all_goals sorry

-- `conseq (: P ==> Q)`: EC's goals `pre`, `post` (with the frame of what the code keeps), then
-- the judgment
/--
trace: case pre
R S T : ℤ → ℤ → Prop
⊢ ∀ (σ₁ σ₂ : ProgramState),
    R §(localVarLens "x" ℤ) §(localVarLens "x" ℤ) → §(localVarLens "x" ℤ) = §(localVarLens "x" ℤ)

case post
R S T : ℤ → ℤ → Prop
⊢ ∀ (σ₁ σ₂ : ProgramState),
    R §(localVarLens "x" ℤ) §(localVarLens "x" ℤ) →
      ∀ (τ₁ τ₂ : ProgramState),
        (localVarLens "k" ℤ).get τ₁ = (localVarLens "k" ℤ).get σ₁ ∧ True →
          (localVarLens "k" ℤ).get τ₂ = (localVarLens "k" ℤ).get σ₂ ∧ True →
            S §(localVarLens "y" ℤ) §(localVarLens "y" ℤ) → T §(localVarLens "y" ℤ) §(localVarLens "k" ℤ)

case judgment
R S T : ℤ → ℤ → Prop
⊢ equiv[ §x{1} = §x{2} ==> S §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      y <- §x;
} ~ {
      var x : ℤ, y : ℤ;
      y <- §x;
}
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 3 goals and ends with 3 goals, 3 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example (R S T : ℤ → ℤ → Prop) : equiv[ R §x{1} §x{2} ==> T §y{1} §k{2} ] {
      var x : ℤ, y : ℤ;
      y <- $x;
    } ~ {
      var x : ℤ, y : ℤ, k : ℤ;
      y <- $x;
    } := by
  equiv_conseq (: ={x} ==> S §y{1} §y{2})
  trace_state
  all_goals sorry

-- `conseq (: _ ==> Q)`: the precondition kept, no `pre` goal
/--
trace: case post
R S T : ℤ → ℤ → Prop
⊢ ∀ (σ₁ σ₂ : ProgramState),
    R §(localVarLens "x" ℤ) §(localVarLens "x" ℤ) →
      ∀ (τ₁ τ₂ : ProgramState),
        True → True → S §(localVarLens "y" ℤ) §(localVarLens "y" ℤ) → T §(localVarLens "y" ℤ) §(localVarLens "y" ℤ)

case judgment
R S T : ℤ → ℤ → Prop
⊢ equiv[ R §x{1} §x{2} ==> S §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      y <- §x;
} ~ {
      var x : ℤ, y : ℤ;
      y <- §x;
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
example (R S T : ℤ → ℤ → Prop) : equiv[ R §x{1} §x{2} ==> T §y{1} §y{2} ] {
      var x : ℤ, y : ℤ;
      y <- $x;
    } ~ {
      var x : ℤ, y : ℤ;
      y <- $x;
    } := by
  equiv_conseq (: _ ==> S §y{1} §y{2})
  trace_state
  all_goals sorry

-- `conseq` on a Hoare triple
/--
trace: case pre
P P' Q Q' : ℤ → Prop
⊢ ∀ (σ : ProgramState), GaudiExpr[ P §(localVarLens "x" ℤ) ].get σ → GaudiExpr[ P' §(localVarLens "x" ℤ) ].get σ

case post
P P' Q Q' : ℤ → Prop
⊢ ∀ (σ : ProgramState), GaudiExpr[ Q' §(localVarLens "y" ℤ) ].get σ → GaudiExpr[ Q §(localVarLens "y" ℤ) ].get σ

case judgment
P P' Q Q' : ℤ → Prop
⊢ hoare[ P' §x ==> Q' §y ] {
      var x : ℤ, y : ℤ;
      y <- §x;
}
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 3 goals and ends with 3 goals, 3 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example (P P' Q Q' : ℤ → Prop) : hoare[ P §x ==> Q §y ] {
      var x : ℤ, y : ℤ;
      y <- $x;
    } := by
  hoare_conseq (: P' §x ==> Q' §y)
  trace_state
  all_goals sorry

/-! ## `while`, `splitwhile`, `unroll` -/

-- EC's two-sided `while I`: `body`, then `hpre` (the code before, with the exit condition under
-- the frame of what the loops keep)
/--
trace: case body
R : ℤ → ℤ → Prop
⊢ prhlStmt
    (fun σ₁ σ₂ ↦
      (§(localVarLens "i" ℤ) = §(localVarLens "i" ℤ) ∧ §(localVarLens "n" ℤ) = §(localVarLens "n" ℤ)) ∧
        GaudiExpr[ decide (§(localVarLens "i" ℤ) < §(localVarLens "n" ℤ)) ].get σ₁ = true ∧
          GaudiExpr[ decide (§(localVarLens "i" ℤ) < §(localVarLens "n" ℤ)) ].get σ₂ = true)
    (GaudiProg[
        var i : ℤ;
        i <- §i + 1;
  ])
    (GaudiProg[
        var i : ℤ;
        i <- §i + 1;
  ])
    fun σ₁ σ₂ ↦
    (§(localVarLens "i" ℤ) = §(localVarLens "i" ℤ) ∧ §(localVarLens "n" ℤ) = §(localVarLens "n" ℤ)) ∧
      GaudiExpr[ decide (§(localVarLens "i" ℤ) < §(localVarLens "n" ℤ)) ].get σ₁ =
        GaudiExpr[ decide (§(localVarLens "i" ℤ) < §(localVarLens "n" ℤ)) ].get σ₂

case hpre
R : ℤ → ℤ → Prop
⊢ prhlStmt (fun σ₁ σ₂ ↦ §(localVarLens "n" ℤ) = §(localVarLens "n" ℤ) ∧ §(localVarLens "k" ℤ) = §(localVarLens "k" ℤ))
    (GaudiProg[
        var i : ℤ;
        i <- 0;
  ])
    (GaudiProg[
        var i : ℤ;
        i <- 0;
  ])
    fun σ₁ σ₂ ↦
    ((§(localVarLens "i" ℤ) = §(localVarLens "i" ℤ) ∧ §(localVarLens "n" ℤ) = §(localVarLens "n" ℤ)) ∧
        GaudiExpr[ decide (§(localVarLens "i" ℤ) < §(localVarLens "n" ℤ)) ].get σ₁ =
          GaudiExpr[ decide (§(localVarLens "i" ℤ) < §(localVarLens "n" ℤ)) ].get σ₂) ∧
      ∀ (τ₁ τ₂ : ProgramState),
        (localVarLens "k" ℤ).get τ₁ = (localVarLens "k" ℤ).get σ₁ ∧ True →
          (localVarLens "k" ℤ).get τ₂ = (localVarLens "k" ℤ).get σ₂ ∧ True →
            §(localVarLens "i" ℤ) = §(localVarLens "i" ℤ) ∧ §(localVarLens "n" ℤ) = §(localVarLens "n" ℤ) →
              GaudiExpr[ decide (§(localVarLens "i" ℤ) < §(localVarLens "n" ℤ)) ].get τ₁ = false →
                GaudiExpr[ decide (§(localVarLens "i" ℤ) < §(localVarLens "n" ℤ)) ].get τ₂ = false →
                  R §(localVarLens "i" ℤ) §(localVarLens "k" ℤ)
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 2 goals and ends with 2 goals, 2 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) : equiv[ ={n, k} ==> R §i{1} §k{2} ] {
      var i : ℤ, n : ℤ, k : ℤ;
      i <- 0;
      while (decide ($i < $n)) { i <- $i + 1; }
    } ~ {
      var i : ℤ, n : ℤ, k : ℤ;
      i <- 0;
      while (decide ($i < $n)) { i <- $i + 1; }
    } := by
  equiv_while (={i, n})
  trace_state
  all_goals sorry

-- EC's one-sided `while{1} I V`: `lossless`, `variant`, then `hpre`
/--
trace: case lossless
R : ℤ → ℤ → Prop
⊢ ∀ (σ₂ σ : ProgramState),
    §(localVarLens "i" ℤ) ≤ §(localVarLens "n" ℤ) ∨ §(localVarLens "n" ℤ) < 0 →
      GaudiExpr[ decide (§(localVarLens "i" ℤ) < §(localVarLens "n" ℤ)) ].get σ = true →
        Stmt.ewp
            (GaudiProg[
                var i : ℤ;
                i <- §i + 1;
          ])
            (fun x ↦ 1) σ =
          1

case variant
R : ℤ → ℤ → Prop
⊢ ∀ (σ₂ : ProgramState) (k : ℕ),
    hoare[ (§i ≤ §n ∨ §n < 0) ∧ decide (§i < §n) = true ∧ (§n - §i).toNat = k ==>
        (§i ≤ §n ∨ §n < 0) ∧ (§n - §i).toNat < k ] {
        var i : ℤ, n : ℤ;
        i <- §i + 1;
  }

case hpre
R : ℤ → ℤ → Prop
⊢ equiv[ §n{1} = §n{2} ==>
      (§i{1} ≤ §n{1} ∨ §n{1} < 0) ∧
        ∀ (τ : ProgramState),
          n.get τ = §n{1} ∧ True → §i ≤ §n ∨ §n < 0 → GaudiExpr[ decide (§i < §n) ].get τ = false → R §i §n{2} ]
      {
      var n : ℤ, i : ℤ;
      i <- 0;
} ~
    {
      skip;
}
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 3 goals and ends with 3 goals, 3 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) : equiv[ ={n} ==> R §i{1} §n{2} ] {
      var i : ℤ, n : ℤ;
      i <- 0;
      while (decide ($i < $n)) { i <- $i + 1; }
    } ~ {
      var n : ℤ;
      skip;
    } := by
  equiv_while{1} (§i{1} ≤ §n{1} ∨ §n{1} < 0) ((§n{1} - §i{1}).toNat)
  trace_state
  all_goals sorry

-- `while I` on a Hoare triple: `body`, `exit`, then the code before
/--
trace: case body
P Q : ℤ → Prop
⊢ hoare[ (§i ≤ §n ∨ §n < 0) ∧ decide (§i < §n) = true ==> §i ≤ §n ∨ §n < 0 ] {
      var i : ℤ, n : ℤ;
      i <- §i + 1;
}

case exit
P Q : ℤ → Prop
⊢ ∀ (i n : ℤ), i ≤ n ∨ n < 0 → decide (i < n) = false → Q i

case hp
P Q : ℤ → Prop
⊢ hoare[ P §n ==> §i ≤ §n ∨ §n < 0 ] {
      var n : ℤ, i : ℤ;
      i <- 0;
}
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 3 goals and ends with 3 goals, 3 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example (P Q : ℤ → Prop) : hoare[ P §n ==> Q §i ] {
      var i : ℤ, n : ℤ;
      i <- 0;
      while (decide ($i < $n)) { i <- $i + 1; }
    } := by
  hoare_while (§i ≤ §n ∨ §n < 0)
  trace_state
  all_goals sorry

-- `splitwhile{1} n : e`
/--
trace: R : ℤ → ℤ → Prop
⊢ equiv[ §n{1} = §n{2} ==> R §i{1} §n{2} ] {
      var n : ℤ, i : ℤ;
      i <- 0;
      while (decide (§i < §n) && decide (§i + 1 < §n)) {
        i <- §i + 1;
      }
      while (decide (§i < §n)) {
        i <- §i + 1;
      }
} ~
    {
      skip;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) : equiv[ ={n} ==> R §i{1} §n{2} ] {
      var i : ℤ, n : ℤ;
      i <- 0;
      while (decide ($i < $n)) { i <- $i + 1; }
    } ~ {
      var n : ℤ;
      skip;
    } := by
  stmt_splitwhile{1} 2 : §i + 1 < §n
  trace_state
  sorry

-- `unroll{1} n`
/--
trace: R : ℤ → ℤ → Prop
⊢ equiv[ §n{1} = §n{2} ==> R §i{1} §n{2} ] {
      var n : ℤ, i : ℤ;
      i <- 0;
      if (decide (§i < §n)) {
        i <- §i + 1;
        while (decide (§i < §n)) {
          i <- §i + 1;
        }
      }
} ~
    {
      skip;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) : equiv[ ={n} ==> R §i{1} §n{2} ] {
      var i : ℤ, n : ℤ;
      i <- 0;
      while (decide ($i < $n)) { i <- $i + 1; }
    } ~ {
      var n : ℤ;
      skip;
    } := by
  stmt_unroll{1} 2
  trace_state
  sorry

/-! ## `rnd` -/

-- `rnd` with EC's default coupling (the identity), and one-sided
/--
trace: R : Bool → Bool → Prop
⊢ equiv[ True ==> ∀ (a : Bool), R a a ] {
      skip;
} ~
    {
      skip;
}
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
  equiv_rnd
  trace_state
  all_goals sorry

/--
trace: R : Bool → Bool → Prop
⊢ equiv[ True ==> ∀ (a : Bool), R a §b{2} ] {
      var b : Bool;
      skip;
} ~
    {
      skip;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : Bool → Bool → Prop) : equiv[ True ==> R §b{1} §b{2} ] {
      var b : Bool;
      b <$ SubProbability.uniform;
    } ~ {
      var b : Bool;
      skip;
    } := by
  equiv_rnd{1}
  trace_state
  all_goals sorry

end GaudisCrypt.ECRulesTest
