import GaudisCrypt.Logic.ByPr
import GaudisCrypt.Logic.ByPrEquiv
import GaudisCrypt.Logic.CallSpec
import GaudisCrypt.Syntax.PrSyntax

/-!
# Golden tests of `bypr`

The goal `bypr` leaves on a `phoare` judgment about a procedure (see `Logic/ECAutoTest.lean` for
the format; `scripts/update_golden.py` refreshes the expected text).
-/

namespace GaudisCrypt.ByPrTest

open GaudisCrypt

moduletype Coin {
  proc flip (b0 : Bool) -> Bool;
}

module FairCoin : Coin {
  proc flip (b0 : Bool) : Bool {
    var b : Bool;
    b <$ SubProbability.uniform;
    return ($b0 && $b)
  };
}

-- `≤`: the probabilities of the runs that satisfy the precondition
/--
trace: x : ℝ
h : ∀ (m : VariableAssignment), Pr[ FairCoin.flip (true) @ &m : §res = true ] ≤ x
⊢ ∀ (a : (procsig (Bool) → Bool).ParamType) (σ : VariableAssignment),
    (let params := GaudiExpr[ a ];
      let b0 := GaudiExpr[ Lens.id.get a ];
      GaudiExpr[ §b0 = true ].get { globals := σ, locals := VariableAssignment.init }) →
      Pr[ FairCoin.flip (a) @ &σ : §res = true ] ≤ x
-/
#guard_msgs in
example (x : ℝ)
    (h : ∀ (m : VariableAssignment), Pr[ FairCoin.flip (true) @ &m : §res = true ] ≤ x) :
    phoare[ FairCoin.flip : §b0 = true ==> §res = true ] ≤ (ENNReal.ofReal x) := by
  bypr
  trace_state
  intro a m ha
  exact ha ▸ h m

global_var seen : Bool

-- EC's `bypr=> &m [#] -> h`: the precondition's conjuncts, about the arguments and the memory
/--
trace: x : ℝ
h : ∀ (m : VariableAssignment), seen.get m = true → Pr[ FairCoin.flip (true) @ &m : §res = true ] ≤ x
a : (procsig (Bool) → Bool).ParamType
m : VariableAssignment
ha : §GaudiExpr[ Lens.id.get a ] = true
hm : true = §seen
⊢ Pr[ FairCoin.flip (a) @ &m : §res = true ] ≤ x
-/
#guard_msgs in
example (x : ℝ)
    (h : ∀ (m : VariableAssignment), seen.get m = true →
      Pr[ FairCoin.flip (true) @ &m : §res = true ] ≤ x) :
    phoare[ FairCoin.flip : §b0 = true ∧ true = §seen ==> §res = true ] ≤ (ENNReal.ofReal x) := by
  bypr
  intro a m ⟨ha, hm⟩
  trace_state
  subst ha
  exact h m hm.symm

-- `=`
/--
trace: x : ℝ
h : ∀ (m : VariableAssignment), Pr[ FairCoin.flip (true) @ &m : §res = true ] = x
⊢ ∀ (a : (procsig (Bool) → Bool).ParamType) (σ : VariableAssignment),
    (let params := GaudiExpr[ a ];
      let b0 := GaudiExpr[ Lens.id.get a ];
      GaudiExpr[ §b0 = true ].get { globals := σ, locals := VariableAssignment.init }) →
      Pr[ FairCoin.flip (a) @ &σ : §res = true ] = x
-/
#guard_msgs in
example (x : ℝ)
    (h : ∀ (m : VariableAssignment), Pr[ FairCoin.flip (true) @ &m : §res = true ] = x) :
    phoare[ FairCoin.flip : §b0 = true ==> §res = true ] = (ENNReal.ofReal x) := by
  bypr
  trace_state
  intro a m ha
  exact ha ▸ h m

-- `≥`
/--
trace: x : ℝ
h : ∀ (m : VariableAssignment), Pr[ FairCoin.flip (true) @ &m : §res = true ] ≥ x
⊢ ∀ (a : (procsig (Bool) → Bool).ParamType) (σ : VariableAssignment),
    (let params := GaudiExpr[ a ];
      let b0 := GaudiExpr[ Lens.id.get a ];
      GaudiExpr[ §b0 = true ].get { globals := σ, locals := VariableAssignment.init }) →
      x ≤ Pr[ FairCoin.flip (a) @ &σ : §res = true ]
-/
#guard_msgs in
example (x : ℝ)
    (h : ∀ (m : VariableAssignment), Pr[ FairCoin.flip (true) @ &m : §res = true ] ≥ x) :
    phoare[ FairCoin.flip : §b0 = true ==> §res = true ] ≥ (ENNReal.ofReal x) := by
  bypr
  trace_state
  intro a m ha
  exact ha ▸ h m

-- the converse of `byphoare (: P ==> _)`
/--
trace: case judgment
m : VariableAssignment
x : ℝ
hx : 0 ≤ x
h : ∀ (m : VariableAssignment), Pr[ FairCoin.flip (true) @ &m : §res = true ] ≤ x
⊢ ∀ (a : (procsig (Bool) → Bool).ParamType) (σ : VariableAssignment),
    (let params := GaudiExpr[ a ];
      let b0 := GaudiExpr[ Lens.id.get a ];
      GaudiExpr[ §b0 = true ].get { globals := σ, locals := VariableAssignment.init }) →
      Pr[ FairCoin.flip (a) @ &σ : §res = true ] ≤ x
-/
#guard_msgs in
example (m : VariableAssignment) (x : ℝ) (hx : 0 ≤ x)
    (h : ∀ (m : VariableAssignment), Pr[ FairCoin.flip (true) @ &m : §res = true ] ≤ x) :
    Pr[ FairCoin.flip (true) @ &m : §res = true ] ≤ x := by
  byphoare (: §b0 = true ==> _)
  bypr
  trace_state
  intro a m ha
  exact ha ▸ h m

-- not a judgment about an event
/--
error: bypr: expected a procedure judgment `phoare[ p : P ==> E ] ≤ r` (or `=`, `≥`), `E` an event and `r` a real bound (`ENNReal.ofReal x`)
-/
#guard_msgs in
example : phoare[ FairCoin.flip : True ==> 1 ] = 1 := by
  bypr

-- EC's `bypr (res{1}) (res{2})` on an `equiv` judgment: the results' probabilities, for all
-- arguments, memories and values (`Logic/ByPrEquiv.lean`)
/--
trace: ⊢ ∀ (a₁ : (procsig (Bool) → Bool).ParamType) (σ₁ : VariableAssignment) (a₂ : (procsig (Bool) → Bool).ParamType)
    (σ₂ : VariableAssignment) (v : Bool),
    (let params_1 := GaudiExpr[ a₁ ];
      let b0_1 := GaudiExpr[ Lens.id.get a₁ ];
      let params_2 := GaudiExpr[ a₂ ];
      let b0_2 := GaudiExpr[ Lens.id.get a₂ ];
      True) →
      ↑(FairCoin.flip.procedure.Pr a₁ σ₁ fun r x ↦ r = v) = ↑(FairCoin.flip.procedure.Pr a₂ σ₂ fun r x ↦ r = v)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : equiv[ FairCoin.flip ~ FairCoin.flip : True ==> ={res} ] := by
  bypr (res{1}) (res{2})
  trace_state
  sorry

-- EC's `byphoare Hl` with `Hl : islossless p`: the probability of `true` is `1`
example (m : VariableAssignment) (Hl : Procedure.IsLossless (Module.Proc.procedure FairCoin.flip)) :
    Pr[ FairCoin.flip (true) @ &m : True ] = 1 := by
  byphoare (Hl)

end GaudisCrypt.ByPrTest
