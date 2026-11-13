import GaudisCrypt.Logic.ECProcInv
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Syntax.Syntax

/-!
# Golden tests of `equiv_proc (I)` and `equiv_conseq_frame H`

(`Logic/ECProcInv.lean`; see `Logic/ECAutoTest.lean` for the format, `scripts/update_golden.py`
refreshes the expected text.)  Two oracles that count in steps of one and of two, a declared
adversary with one procedure, and a declared functor with two procedures, whose oracle lists are
a hypothesis and whose procedures have a rule tagged `@[proc_inv]`.
-/

namespace GaudisCrypt.ECProcInvTest

open GaudisCrypt

global_var pCount : ℤ
global_var pOther : ℤ

moduletype Orc {
  proc get (x : ℤ) -> ℤ;
}

moduletype Two {
  proc p (x : ℤ) -> ℤ;
  proc q (x : ℤ) -> ℤ;
}

/-- An adversary with oracle access. -/
abbrev ADV := Orc →ₘ procmod () → ℤ

/-- A functor with two procedures (a simulator). -/
abbrev SIM := Orc →ₘ Two

module Inc : Orc {
  proc get (x : ℤ) : ℤ {
    pCount <- $pCount + 1;
    return $x
  };
}

module Inc2 : Orc {
  proc get (x : ℤ) : ℤ {
    pCount <- $pCount + 2;
    return $x
  };
}

/-- `Inc.get` touches `pCount` (EC reads a concrete module's globals off its code). -/
@[fp_bound] theorem fvP_Inc_get : FVP.fvP Inc.get ≤ pCount.footprint := by
  fp_module pCount

/-- `Inc2.get` touches `pCount`. -/
@[fp_bound] theorem fvP_Inc2_get : FVP.fvP Inc2.get ≤ pCount.footprint := by
  fp_module pCount

/-- The two oracles keep `pCount{2} = 2 * pCount{1}`. -/
theorem Inc_Inc2 : equiv[ Inc.get (x) ~ Inc2.get (x) :
    ={x} ∧ §pCount{2} = 2 * §pCount{1} ==> ={res} ∧ §pCount{2} = 2 * §pCount{1} ] := by
  equiv_proc; equiv_auto
  rintro _ _ _ _ ⟨rfl, h⟩
  exact ⟨rfl, by rw [h]; ring⟩

/-! ## `equiv_conseq_frame H` -/

-- EC's `conseq H`: `pOther`, which the goal's postcondition reads and the procedures do not
-- write, keeps its value (the two frames of `post`); `pre` is closed
/--
trace: case post
R : ℤ → ℤ → Prop
⊢ ∀ (a₁ : (procsig (ℤ) → ℤ).ParamType) (g₁ : VariableAssignment) (a₂ : (procsig (ℤ) → ℤ).ParamType)
    (g₂ : VariableAssignment),
    a₁ = a₂ ∧ pCount.get g₂ = 2 * pCount.get g₁ →
      ∀ (r₁ : ℤ) (τ₁ : VariableAssignment) (r₂ : ℤ) (τ₂ : VariableAssignment),
        r₁ = r₂ ∧ pCount.get τ₂ = 2 * pCount.get τ₁ →
          pOther.get τ₁ = pOther.get g₁ → pOther.get τ₂ = pOther.get g₂ → R (pOther.get τ₁) (pOther.get τ₂)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) : equiv[ Inc.get (x) ~ Inc2.get (x) :
    ={x} ∧ §pCount{2} = 2 * §pCount{1} ==> R §pOther{1} §pOther{2} ] := by
  equiv_conseq_frame Inc_Inc2
  trace_state
  all_goals sorry

-- both implications trivial: no goal is left (EC's `by conseq H`)
example : equiv[ Inc.get (x) ~ Inc2.get (x) :
    ={x, pOther} ∧ §pCount{2} = 2 * §pCount{1} ==>
    ={res, pOther} ∧ §pCount{2} = 2 * §pCount{1} ] := by
  equiv_conseq_frame Inc_Inc2

/-! ## `equiv_proc (I)` on a declared adversary -/

section

declare module A <: ADV {-pCount, -pOther}

-- EC's `proc (I)`: the oracle's judgment, EC's `={arg} ∧ I ==> ={res} ∧ I` (the oracles' writes
-- keep `glob A`); the two implications are closed
/--
trace: case oracle
A : ADV
inst✝ : Module.Declared A (pCount.footprint ⊔ pOther.footprint)
⊢ prhlProc (fun a₁ g₁ a₂ g₂ ↦ a₁ = a₂ ∧ pCount.get g₂ = 2 * pCount.get g₁) Inc.get.procedure Inc2.get.procedure
    fun r₁ g₁ r₂ g₂ ↦ r₁ = r₂ ∧ pCount.get g₂ = 2 * pCount.get g₁
-/
#guard_msgs in
example : equiv[ A(Inc).run ~ A(Inc2).run :
    ={glob A} ∧ §pCount{2} = 2 * §pCount{1} ==> ={res} ∧ §pCount{2} = 2 * §pCount{1} ] := by
  equiv_proc (§pCount{2} = 2 * §pCount{1})
  trace_state
  exact Inc_Inc2

end

/-! ## `equiv_proc (I)` by a rule (`@[proc_inv]`) -/

abbrev orcHoles : HoleSigs := .cons (procsig (ℤ) -> ℤ) .empty

/-- EC's module type of `S` lists the oracles of its procedures (`proc p(x : int) : int {O.get}`):
each procedure of `S(O)` is code with a hole for `O.get`. -/
def SIM.Rep (S : SIM) : Prop :=
  ∃ pp pq : ProcedureWithHoles orcHoles (procsig (ℤ) -> ℤ),
    (∀ O a, procedureDenotation (Two.p (Module.app S O)).procedure a =
      procedureDenotation (pp.instantiate (Orc.get O).procedure) a) ∧
    (∀ O a, procedureDenotation (Two.q (Module.app S O)).procedure a =
      procedureDenotation (pq.instantiate (Orc.get O).procedure) a) ∧
    FVP.fvP_proc pp ⊔ FVP.fvP_proc pq ≤ FVP.fvP S

/-- The abstract call rule for `S(O).p` (none is given for `S(O).q`). -/
@[proc_inv] theorem SIM.call_p {Ω : Type} (L : Lens Ω VariableAssignment) (S : SIM)
    (hS : SIM.Rep S) (F : Footprint VariableAssignment) (hSF : FVP.fvP S ≤ F)
    (hFL : F ≤ (L.footprint)ᶜ) (I : Ω → Ω → Prop) (O₁ O₂ : Orc)
    (horacle : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L F I g₁ g₂)
      (Orc.get O₁).procedure (Orc.get O₂).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L F I g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L F I g₁ g₂)
      (Two.p (Module.app S O₁)).procedure (Two.p (Module.app S O₂)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L F I g₁ g₂) := by
  obtain ⟨pp, pq, hp, -, hle⟩ := hS
  intro a₁ a₂
  rw [hp O₁ a₁, hp O₂ a₂]
  exact prhlProc_abstract_callF L (show orcHoles.Instantiation from (Orc.get O₁).procedure)
    (show orcHoles.Instantiation from (Orc.get O₂).procedure) pp F
    ((le_sup_left.trans hle).trans hSF) hFL I
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable ℤ)
      | succ n => nomatch n)
    (fun n => by cases n with
      | zero => exact horacle
      | succ n => nomatch n) a₁ a₂

section

declare module S <: SIM {-pCount, -pOther}

variable (S_rep : SIM.Rep S)

-- EC's `proc (I)` on a procedure of the functor: the rule's premises about `S` from the context,
-- the oracle's judgment in EC's form, the two implications closed
include S_rep in
/--
trace: case oracle
S : SIM
inst✝ : Module.Declared S (pCount.footprint ⊔ pOther.footprint)
S_rep : S.Rep
⊢ prhlProc (fun a₁ g₁ a₂ g₂ ↦ a₁ = a₂ ∧ pCount.get g₂ = 2 * pCount.get g₁) Inc.get.procedure Inc2.get.procedure
    fun r₁ g₁ r₂ g₂ ↦ r₁ = r₂ ∧ pCount.get g₂ = 2 * pCount.get g₁
-/
#guard_msgs in
example : equiv[ S(Inc).p (x) ~ S(Inc2).p (x) :
    ={x, glob S} ∧ §pCount{2} = 2 * §pCount{1} ==>
    ={res, glob S} ∧ §pCount{2} = 2 * §pCount{1} ] := by
  equiv_proc (§pCount{2} = 2 * §pCount{1})
  trace_state
  exact Inc_Inc2

-- a procedure without a rule
include S_rep in
/--
error: equiv_proc: no rule (`@[proc_inv]`) for the procedures
  S(Inc).q.procedure
and
  S(Inc2).q.procedure
GaudisCrypt.ECProcInvTest.SIM.call_p: not about the left procedure
-/
#guard_msgs in
example : equiv[ S(Inc).q (x) ~ S(Inc2).q (x) :
    ={x, glob S} ∧ §pCount{2} = 2 * §pCount{1} ==>
    ={res, glob S} ∧ §pCount{2} = 2 * §pCount{1} ] := by
  equiv_proc (§pCount{2} = 2 * §pCount{1})

end

end GaudisCrypt.ECProcInvTest
