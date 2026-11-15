import GaudisCrypt.Logic.PHoareWhileRev
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.ECWhile
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Syntax.Syntax

/-!
# Golden tests of `phoare_while I V k ε`, and of `conseq`, `rnd` on a lower bound

The goals EC's `while I V k ε` leaves on a loop that flips a coin until it shows heads (see
`Logic/ECAutoTest.lean` for the format; `scripts/update_golden.py` refreshes the expected text).
-/

namespace GaudisCrypt.PHoareWhileRevTest

open GaudisCrypt GaudisCrypt.EC

module Flip {
  proc run () : Bool {
    var b : Bool;
    b <- false;
    while (!$b) {
      b <$ dbool;
    }
    return $b
  };
}

-- EC's goals, in its order, the trivial ones closed (here `pre_inv`, `pre_bound`, `rate`):
-- `term`, `body`, `inv`, `variant`
/--
trace: case term
⊢ ∀ (b : Bool), (if b = true then 0 else 1) ≤ 1 ∧ ((if b = true then 0 else 1) ≤ 0 → (!b) = false)

case body
⊢ ∀ (w : Stmt),
    phoare[ True ==> 1 ] = 1 {
          stmt w;
    } →
      phoare[ True ∧ (!§b) = true ==> 1 ] = 1 {
          var b : Bool;
          b <$ dbool;
          stmt w;
    }

case inv
⊢ phoare[ True ∧ (!§b) = true ==> True ] = 1 {
      var b : Bool;
      b <$ dbool;
}

case variant
⊢ ∀ (z : ℤ),
    phoare[ True ∧ (!§b) = true ∧ (if §b = true then 0 else 1) = z ==>
        (if §b = true then 0 else 1) < z ] ≥ (ENNReal.ofReal (1 / 2)) {
        var b : Bool;
        b <$ dbool;
  }
---
warning: The following tactic starts with 4 goals and ends with 4 goals, 4 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : islossless Flip.run := by
  phoare_proc; phoare_seq_lossless 1 : (True)
  · phoare_auto
  phoare_while True (if §b then 0 else 1) 1 (1 / 2)
  trace_state
  · intro b; cases b <;> simp
  · intro w ih; phoare_seq_lossless 1 : (True)
    · phoare_auto; exact fun _ _ => dbool_ll
    · exact ih
  · phoare_auto; exact fun _ _ => dbool_ll
  · intro z; phoare_conseq (: True ==> §b = true)
    · smt_close
    phoare_rnd (pred1 true); phoare_auto
    smt_close [mu_pred1, dbool1E_mu1, pred1E]

-- EC's `conseq (: P ==> Q)` on a lower bound: `post` may use the precondition
/--
trace: case post
z : ℤ
⊢ ∀ (b : Bool),
    b = false ∧ (if b = true then 0 else 1) = z → ∀ (b1 : Bool), b1 = true → (if b1 = true then 0 else 1) < z

case judgment
z : ℤ
⊢ phoare[ True ==> §b = true ] ≥ (ENNReal.ofReal (1 / 2)) {
      var b : Bool;
      b <$ dbool;
}
---
trace: case judgment
z : ℤ
⊢ phoare[ True ==> 1 / 2 ≤ mu dbool (pred1 true) ∧ ∀ v ∈ dbool.support, pred1 true v → v = true ] = 1 {
      skip;
}
---
warning: The following tactic starts with 2 goals and ends with 2 goals, 2 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : islossless Flip.run := by
  phoare_proc; phoare_seq_lossless 1 : (True)
  · phoare_auto
  phoare_while True (if §b then 0 else 1) 1 (1 / 2)
  · intro b; cases b <;> simp
  · intro w ih; phoare_seq_lossless 1 : (True)
    · phoare_auto; exact fun _ _ => dbool_ll
    · exact ih
  · phoare_auto; exact fun _ _ => dbool_ll
  · intro z; phoare_conseq (: True ==> §b = true)
    trace_state
    · smt_close
    -- EC's `rnd E` on a lower bound: `E` is at least as likely as the bound and gives the event
    phoare_rnd (pred1 true)
    trace_state
    phoare_auto
    smt_close [mu_pred1, dbool1E_mu1, pred1E]

-- the lossless rule `while I V` (`Logic/ECWhile.lean`) with a tactic on the next line: the
-- `k` and `ε` of `while I V k ε` are on the same line or indented further
/--
trace: case body
⊢ ∀ (k : ℕ),
    phoare[ True ∧ decide (§j < 3) = true ∧ 3 - §j = k ==> True ∧ 3 - §j < k ] = 1 {
        var j : ℕ;
        j <- §j + 1;
  }

⊢ phoare[ True ==> True ] = 1 {
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
example : phoare[ True ==> 1 ] = 1 {
      var j : ℕ;
      while (decide ($j < 3)) {
        j <- $j + 1;
      }
    } := by
  phoare_while (True) (3 - §j)
  trace_state
  all_goals sorry

end GaudisCrypt.PHoareWhileRevTest
