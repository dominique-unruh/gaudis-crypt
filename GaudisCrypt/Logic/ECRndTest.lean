import GaudisCrypt.Logic.ECRnd
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Syntax.Syntax

/-!
# Golden tests of `equiv_rnd f g`

The goal EC's `rnd f g` leaves: its three conditions (see `Logic/ECAutoTest.lean` for the
format; `scripts/update_golden.py` refreshes the expected text).
-/

namespace GaudisCrypt.ECRndTest

open GaudisCrypt GaudisCrypt.EC

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
trace: ⊢ equiv[ §k{1} = §k{2} ==> (∀ (b : ZMod 7), b = b - §k{2} + §k{1}) ∧ ∀ (a : ZMod 7), a = a + §k{1} - §k{2} ] {
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
