import GaudisCrypt.Logic.StateEq
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Syntax.Syntax

/-! Tests of `subst_states` (`Logic/StateEq.lean`). -/

namespace GaudisCrypt.StateEqTest

open GaudisCrypt

global_var gA : ℕ
global_var gB : ℕ
global_var gC : ℕ

-- what `sp` leaves over `gC <- 0; gC <- …; gB <- …; gA <- …` on both sides from equal states:
-- the states with the old values written back are equal, and the new values agree
example (g₁ g₂ : VariableAssignment) (v w u v' w' u' : ℕ)
    (h : gA.set v (gB.set w (gC.set u (gC.set 0 g₁))) =
      gA.set v' (gB.set w' (gC.set u' (gC.set 0 g₂))))
    (h1 : gA.get g₁ = 1) (h2 : gB.get g₁ = 2) (h3 : gC.get g₁ = 0)
    (h1' : gA.get g₂ = 1) (h2' : gB.get g₂ = 2) (h3' : gC.get g₂ = 0) : g₁ = g₂ := by
  subst_states
  assumption

-- the new values differ: the states are not known equal, and nothing is peeled
example (g₁ g₂ : VariableAssignment) (v v' : ℕ)
    (_h : gA.set v g₁ = gA.set v' g₂) (_h1 : gA.get g₁ = 1) (_h1' : gA.get g₂ = 2) : True := by
  fail_if_success subst_states
  trivial

-- no equation of states
example (g₁ g₂ : VariableAssignment) (_h : gA.get g₁ = gA.get g₂) : True := by
  fail_if_success subst_states
  trivial

-- `ec_auto` after `sp` over the same initializations on both sides, from equal states: the
-- states are equal again (EC's `auto`; Gconcl_list's lazy/eager steps need `={glob D2(D)}` there)
module Init0 {
  proc main () : Unit {
    gA <- 0;
    gC <- 0;
    gC <- 1;
    return ()
  };
}

#guard_msgs in
example : equiv[ Init0.main ~ Init0.main : ={allGlobals} ==> ={allGlobals} ] := by
  equiv_proc; stmt_sp; ec_auto

end GaudisCrypt.StateEqTest
