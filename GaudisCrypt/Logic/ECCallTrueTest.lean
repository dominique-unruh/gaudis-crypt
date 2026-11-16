import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECCallEquiv
import GaudisCrypt.Logic.ECInline

/-!
# Golden tests of `equiv_call (_ : True)`, of `byequiv` on `≤`, and of `stmt_inline (M(A).f)`
through a module type

EC's `call (_ : true)` on the adversary; the events' implication of `byequiv` on `Pr[…] ≤
Pr[…]`, closed as EC's `=> //`; a procedure named by its module, called through the module type
of an experiment's parameter (see `Logic/ECAutoTest.lean` for the format;
`scripts/update_golden.py` refreshes the expected text).
-/

namespace GaudisCrypt.ECCallTrueTest

open GaudisCrypt

moduletype Guesser {
  proc guess (n : ℕ) -> Bool;
}

module Game using (A : Guesser) {
  proc main () : Bool {
    var b : Bool, k : ℕ;
    k <- 1;
    b <- call A.guess ($k);
    return $b
  };
}

-- an adversary built from another: the experiment calls it through `Guesser`
module Twice using (A : Guesser) {
  proc guess (n : ℕ) : Bool {
    var b : Bool;
    b <- call A.guess ($n + $n);
    return $b
  };
}

section

declare module A <: Guesser

-- EC's `byequiv => //; proc; call (_ : true)`: the adversary keeps its own state equal; the
-- events' implication is closed by `byequiv`
/--
trace: case judgment
A : Guesser
inst✝ : Module.Declared A ⊥
m : VariableAssignment
⊢ equiv[ ={allGlobals} ==> §b{1} = true → §b{2} = true ] {
      var k : ℕ, b : Bool;
      k <- 1;
      b <- call A.guess.procedure (§k);
} ~ {
      var k : ℕ, b : Bool;
      k <- 1;
      b <- call A.guess.procedure (§k);
}
---
trace: case judgment
A : Guesser
inst✝ : Module.Declared A ⊥
m : VariableAssignment
⊢ equiv[ ={allGlobals} ==>
      ={k, glob A} ∧
        ∀ (r₁ : Bool) (g₁ : VariableAssignment) (r₂ : Bool) (g₂ : VariableAssignment),
          r₁ = r₂ ∧ (FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A).touched_getter.get g₂ → r₁ = true → r₂ = true ]
      {
      var k : ℕ;
      k <- 1;
} ~ {
      var k : ℕ;
      k <- 1;
}
-/
#guard_msgs in
example (m : VariableAssignment) :
    Pr[ Game(A).main () @ &m : §res ] ≤ Pr[ Game(A).main () @ &m : §res ] := by
  byequiv; equiv_proc
  trace_state
  equiv_call (_ : True)
  trace_state
  equiv_auto

-- EC's `inline{2} Twice(A).guess`: the call the experiment makes through its module type
/--
trace: case judgment
A : Guesser
inst✝ : Module.Declared A ⊥
m : VariableAssignment
⊢ equiv[ ={allGlobals} ==> §b{1} = true ↔ §b{2} = true ] {
      var k : ℕ, b : Bool;
      k <- 1;
      b <- call Twice(A).guess.procedure (§k);
} ~ {
      var k : ℕ, b : Bool, n : ℕ, b0 : Bool;
      k <- 1;
      reset_vars {"n", "b0"} ∪ stringsStartingWith "@." \ {"@.n", "@.b"};
      n <- §k;
      b0 <- call A.guess.procedure (§n + §n);
      b <- §b0;
}
-/
#guard_msgs in
example (m : VariableAssignment) :
    Pr[ Game(Twice(A)).main () @ &m : §res ] = Pr[ Game(Twice(A)).main () @ &m : §res ] := by
  byequiv; equiv_proc
  stmt_inline{2} (Twice(A).guess)
  trace_state
  stmt_inline{1} (Twice(A).guess)
  sim

end

end GaudisCrypt.ECCallTrueTest
