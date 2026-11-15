import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Syntax.PrSyntax

/-!
# Golden tests of `phoare_rnd`, `phoare_conseq` on an exact bound, `islossless`

The goals the three steps leave on `Pr[ Game(A).main () @ &m : res ] = 1 / 2`, EC's
`byphoare; proc; rnd (pred1 b'); conseq (: _ ==> true); islossless` (see `Logic/ECAutoTest.lean`
for the format; `scripts/update_golden.py` refreshes the expected text).
-/

namespace GaudisCrypt.PHoareRndTest

open GaudisCrypt GaudisCrypt.EC

moduletype Guesser {
  proc guess () -> Bool;
}

module Game using (A : Guesser) {
  proc main () : Bool {
    var b : Bool, b' : Bool, x : ℕ;
    x <- 0;
    b' <- call A.guess ();
    b <$ dbool;
    return decide ($b' = $b)
  };
}

section

declare module A <: Guesser

variable (A_ll : islossless A.guess)

-- EC's `rnd (pred1 b')`: the event's probability, and the event as the postcondition
/--
trace: case judgment
A : Guesser
inst✝ : Module.Declared A ⊥
A_ll : A.guess.procedure.IsLossless
m : VariableAssignment
⊢ phoare[ () = () ∧ CurrentState.state.globals = m ==>
      mu dbool (pred1 §b') = 1 / 2 ∧ ∀ v ∈ dbool.support, pred1 (§b') v ↔ decide (§b' = v) = true ] = 1 {
      var x : ℕ, b' : Bool;
      x <- 0;
      b' <- call A.guess.procedure ();
}
-/
#guard_msgs in
include A_ll in
example (m : VariableAssignment) : Pr[ Game(A).main () @ &m : §res ] = 1 / 2 := by
  byphoare; phoare_proc
  phoare_rnd (pred1 §b')
  trace_state
  phoare_conseq (: _ ==> True)
  · smt_close [mu_pred1, dbool1E_mu1, pred1E]
  islossless
  exact A_ll

-- EC's `conseq (: _ ==> true)`: the condition for all values, then the lossless code
/--
trace: case post
A : Guesser
inst✝ : Module.Declared A ⊥
A_ll : A.guess.procedure.IsLossless
m : VariableAssignment
⊢ ∀ (b' : Bool), mu dbool (pred1 b') = 1 / 2 ∧ ∀ v ∈ dbool.support, pred1 b' v ↔ decide (b' = v) = true

case judgment
A : Guesser
inst✝ : Module.Declared A ⊥
A_ll : A.guess.procedure.IsLossless
m : VariableAssignment
⊢ phoare[ () = () ∧ CurrentState.state.globals = m ==> 1 ] = 1 {
      var x : ℕ, b' : Bool;
      x <- 0;
      b' <- call A.guess.procedure ();
}
---
warning: The following tactic starts with 2 goals and ends with 2 goals, 2 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
include A_ll in
example (m : VariableAssignment) : Pr[ Game(A).main () @ &m : §res ] = 1 / 2 := by
  byphoare; phoare_proc
  phoare_rnd (pred1 §b')
  phoare_conseq (: _ ==> True)
  trace_state
  · smt_close [mu_pred1, dbool1E_mu1, pred1E]
  islossless
  exact A_ll

-- EC's `islossless`: one goal per call (the assignment and the sampling are closed)
/--
trace: case lossless
A : Guesser
inst✝ : Module.Declared A ⊥
A_ll : A.guess.procedure.IsLossless
m : VariableAssignment
⊢ A.guess.procedure.IsLossless
-/
#guard_msgs in
include A_ll in
example (m : VariableAssignment) : Pr[ Game(A).main () @ &m : §res ] = 1 / 2 := by
  byphoare; phoare_proc
  phoare_rnd (pred1 §b')
  phoare_conseq (: _ ==> True)
  · smt_close [mu_pred1, dbool1E_mu1, pred1E]
  islossless
  trace_state
  exact A_ll

-- `islossless` on a procedure
/--
trace: case lossless
A : Guesser
inst✝ : Module.Declared A ⊥
A_ll : A.guess.procedure.IsLossless
⊢ A.guess.procedure.IsLossless
-/
#guard_msgs in
include A_ll in
example : islossless Game(A).main := by
  islossless
  trace_state
  exact A_ll

-- not an exact bound on an event after a sampling
/--
error: phoare_rnd: not `phoare[ c; x <$ d : P ==> Q ] = r` with `Q` an event and `r` a constant
  phoareStmt GaudiExpr[ () = () ∧ CurrentState.state.globals = m ].get
    (GaudiProg[
        var x : ℕ, b' : Bool, b : Bool;
        {
          x <- 0;
          b' <- call A.guess.procedure ();
        }
        b <$ dbool;
  ])
    GaudiExpr[ indicatorE (decide (§(localVarLens "b'" Bool) = §(localVarLens "b" Bool)) = true) ].get
    (fun x1 x2 ↦ x1 ≤ x2) GaudiExpr[ ENNReal.ofReal (1 / 2) ].get
-/
#guard_msgs in
example (m : VariableAssignment) : Pr[ Game(A).main () @ &m : §res ] ≤ 1 / 2 := by
  byphoare; phoare_proc
  phoare_rnd (pred1 §b')

end

end GaudisCrypt.PHoareRndTest
