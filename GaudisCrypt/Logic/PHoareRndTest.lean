import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Syntax.PrSyntax

/-!
# Golden tests of `phoare_rnd`, `phoare_conseq` on an exact bound, `islossless`, and of the rules
for an event reached with probability `1` (`phoare_call H`, `phoare_rnd`, `phoare_auto`)

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

module Game2 using (A : Guesser) {
  proc main () : Bool {
    var b : Bool, b' : Bool, x : Bool, y : Bool;
    x <$ dbool;
    y <- !$x;
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
        x <- 0;
        b' <- call A.guess.procedure ();
        b <$ dbool;
  ])
    GaudiExpr[ indicatorE (decide (§(localVarLens "b'" Bool) = §(localVarLens "b" Bool)) = true) ].get
    (fun x1 x2 ↦ x1 ≤ x2) GaudiExpr[ ENNReal.ofReal (1 / 2) ].get
-/
#guard_msgs in
example (m : VariableAssignment) : Pr[ Game(A).main () @ &m : §res ] ≤ 1 / 2 := by
  byphoare; phoare_proc
  phoare_rnd (pred1 §b')

/-! ## An event reached with probability `1`: lossless calls, samplings, `auto` -/

-- EC's `call A_ll` on an event: the event for every result
/--
trace: case judgment
A : Guesser
inst✝ : Module.Declared A ⊥
A_ll : A.guess.procedure.IsLossless
m : VariableAssignment
⊢ phoare[ () = () ∧ CurrentState.state.globals = m ==>
      ∀ (v : Bool), mu dbool (pred1 v) = 1 / 2 ∧ ∀ v_1 ∈ dbool.support, pred1 v v_1 ↔ decide (v = v_1) = true ] = 1 {
      var x : Bool, y : Bool;
      x <$ dbool;
      y <- !§x;
}
-/
#guard_msgs in
include A_ll in
example (m : VariableAssignment) : Pr[ Game2(A).main () @ &m : §res ] = 1 / 2 := by
  byphoare; phoare_proc
  phoare_rnd (pred1 §b'); phoare_call A_ll
  trace_state
  phoare_auto
  smt_close [dbool_ll, mu_pred1, dbool1E_mu1, pred1E]

-- EC's `rnd` (no event): the distribution is lossless, the event holds on its support
/--
trace: case judgment
A : Guesser
inst✝ : Module.Declared A ⊥
A_ll : A.guess.procedure.IsLossless
m : VariableAssignment
⊢ phoare[ () = () ∧ CurrentState.state.globals = m ==>
      is_lossless dbool ∧
        ∀ v ∈ dbool.support,
          ∀ (v : Bool),
            mu dbool (pred1 v) = 1 / 2 ∧ ∀ v_1 ∈ dbool.support, pred1 v v_1 ↔ decide (v = v_1) = true ] = 1 {
      skip;
}
-/
#guard_msgs in
include A_ll in
example (m : VariableAssignment) : Pr[ Game2(A).main () @ &m : §res ] = 1 / 2 := by
  byphoare; phoare_proc
  phoare_rnd (pred1 §b'); phoare_call A_ll; stmt_wp; phoare_rnd
  trace_state
  phoare_auto
  smt_close [dbool_ll, mu_pred1, dbool1E_mu1, pred1E]

-- EC's `auto` on an event: `wp` and `rnd` to the start, then the implication
/--
trace: case judgment
A : Guesser
inst✝ : Module.Declared A ⊥
A_ll : A.guess.procedure.IsLossless
m : VariableAssignment
⊢ ∀ (σ : ProgramState),
    σ.globals = m →
      is_lossless dbool ∧
        ∀ v ∈ dbool.support,
          ∀ (v : Bool), mu dbool (pred1 v) = 1 / 2 ∧ ∀ v_1 ∈ dbool.support, pred1 v v_1 ↔ decide (v = v_1) = true
-/
#guard_msgs in
include A_ll in
example (m : VariableAssignment) : Pr[ Game2(A).main () @ &m : §res ] = 1 / 2 := by
  byphoare; phoare_proc
  phoare_rnd (pred1 §b'); phoare_call A_ll; phoare_auto
  trace_state
  smt_close [dbool_ll, mu_pred1, dbool1E_mu1, pred1E]

-- EC's `conseq (: _ ==> true) (: _ ==> Q)` on an event reached with probability `1`: the event
-- as a Hoare judgment, then the statement's losslessness
/--
trace: case hoare
A : Guesser
inst✝ : Module.Declared A ⊥
A_ll : A.guess.procedure.IsLossless
⊢ hoare[ True ==> decide (§b' = §b) = true ∨ ¬decide (§b' = §b) = true ] {
      var x : Bool, y : Bool, b' : Bool, b : Bool;
      x <$ dbool;
      y <- !§x;
      b' <- call A.guess.procedure ();
      b <$ dbool;
}

case lossless
A : Guesser
inst✝ : Module.Declared A ⊥
A_ll : A.guess.procedure.IsLossless
⊢ phoare[ True ==> 1 ] = 1 {
      var x : Bool, y : Bool, b' : Bool, b : Bool;
      x <$ dbool;
      y <- !§x;
      b' <- call A.guess.procedure ();
      b <$ dbool;
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
include A_ll in
example : phoare[ Game2(A).main : True ==> (§res ∨ ¬ §res) ] = 1 := by
  phoare_proc
  phoare_conseq (: _ ==> True) (: _ ==> _)
  trace_state
  all_goals sorry

-- (a judgment that is not an event with the bound `1` goes to the rules on expectations: the
-- `islossless` tests above run `phoare_call` and `phoare_auto` on the expectation `1`)

end

end GaudisCrypt.PHoareRndTest
