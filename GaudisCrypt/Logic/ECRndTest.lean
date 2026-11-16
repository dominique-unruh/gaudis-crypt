import GaudisCrypt.Logic.ECRnd
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Syntax.Syntax

/-!
# Golden tests of `equiv_rnd f g`

The goal EC's `rnd f g` leaves: its three conditions (see `Logic/ECAutoTest.lean` for the
format; `scripts/update_golden.py` refreshes the expected text).
-/

namespace GaudisCrypt.ECRndTest

open GaudisCrypt GaudisCrypt.EC

module L {
  proc f () : (ZMod 7) {
    var k : Bool, x : ZMod 7;
    k <- true;
    x <$ SubProbability.uniform;
    return $x
  };
}

module R {
  proc f () : (ZMod 7) {
    var k : ZMod 7, x : ZMod 7;
    k <- 2;
    x <$ SubProbability.uniform;
    return $x
  };
}

-- a shift and its inverse, on a uniform sampling
/--
trace: ⊢ equiv[ True ==> True ] {
      skip;
} ~
    {
      skip;
}
-/
#guard_msgs in
example : equiv[ True ==> §x{2} = §x{1} + 3 ] {
      var x : ZMod 7;
      x <$ SubProbability.uniform;
    } ~ {
      var x : ZMod 7;
      x <$ SubProbability.uniform;
    } := by
  equiv_rnd (fun z => z + 3) (fun z => z - 3)
  trace_state
  equiv_skip
  auto_progress

-- the functions may read the two memories
/--
trace: ⊢ equiv[ ={k} ==> (∀ (b : ZMod 7), b = b - §k{2} + §k{1}) ∧ ∀ (a : ZMod 7), a = a + §k{1} - §k{2} ] {
      var k : ZMod 7;
      skip;
} ~
    {
      skip;
}
---
warning: Variable name `k` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
example : equiv[ ={k} ==> §x{2} = §x{1} + §k{1} ] {
      var k : ZMod 7, x : ZMod 7;
      x <$ SubProbability.uniform;
    } ~ {
      var k : ZMod 7, x : ZMod 7;
      x <$ SubProbability.uniform;
    } := by
  equiv_rnd (fun z => z + §k{1}) (fun z => z - §k{2})
  trace_state
  equiv_skip
  auto_progress

-- an involution on the coin
/--
trace: ⊢ equiv[ True ==> True ] {
      skip;
} ~
    {
      skip;
}
-/
#guard_msgs in
example : equiv[ True ==> §b{2} = !§b{1} ] {
      var b : Bool;
      b <$ dbool;
    } ~ {
      var b : Bool;
      b <$ dbool;
    } := by
  equiv_rnd (fun b => !b) (fun b => !b)
  trace_state
  equiv_skip
  auto_progress

-- the one-function form with a tactic on the next line: a second function is on the same line
-- or indented further (the one-function rule's goal: the push-forward of the left sampling)
/--
trace: ⊢ equiv[ True ==>
      (do
          let a ← dbool
          pure !a) =
        dbool ]
      {
      skip;
} ~
    {
      skip;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : equiv[ True ==> §b{2} = !§b{1} ] {
      var b : Bool;
      b <$ dbool;
    } ~ {
      var b : Bool;
      b <$ dbool;
    } := by
  equiv_rnd (fun b => !b)
  trace_state
  sorry

-- a name with one type on the left and another on the right (as inlining leaves them): each
-- side's own variable
/--
trace: ⊢ equiv[ True ==> (∀ (b : ZMod 7), b = b - §k{2} + §k{2}) ∧ ∀ (a : ZMod 7), a = a + §k{2} - §k{2} ∧ a + §k{2} = a + 2 ]
      {
      var k : Bool;
      k <- true;
} ~ {
      var k : ZMod 7;
      k <- 2;
}
-/
#guard_msgs in
example : equiv[ L.f ~ R.f : True ==> §res{2} = §res{1} + 2 ] := by
  equiv_proc
  equiv_rnd (fun z => z + §k{2}) (fun z => z - §k{2})
  trace_state
  equiv_auto

-- not two samplings
/--
error: equiv_rnd: the last statement of side 1 is not a sampling (deterministic code first: `stmt_wp`):
  GaudiProg[
      var b : Bool;
      b <- true;
]
-/
#guard_msgs in
example : equiv[ True ==> True ] {
      var b : Bool;
      b <- true;
    } ~ {
      var b : Bool;
      b <$ dbool;
    } := by
  equiv_rnd (fun b => !b) (fun b => !b)

end GaudisCrypt.ECRndTest
