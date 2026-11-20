import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECInline
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECCallEquiv
import GaudisCrypt.Logic.ECCallUpto
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.FootprintUpper
import GaudisCrypt.Syntax.Syntax

/-!
# Golden tests of `proc`, `inline`, `call` and `sim`

Each test pins the goals a rule leaves on small modules: a concrete oracle (two spellings of it),
a game calling an abstract adversary with the oracle, and a declared adversary (see
`Logic/ECAutoTest.lean` for the format; `scripts/update_golden.py` refreshes the expected text).
-/

namespace GaudisCrypt.ECCallsTest

open GaudisCrypt

global_var cCount : ℤ
global_var cFlag : Bool

moduletype Orc {
  proc get (x : ℤ) -> ℤ;
}

/-- An adversary with oracle access. -/
abbrev ADV := Orc →ₘ procmod () → ℤ

module Inc : Orc {
  proc get (x : ℤ) : ℤ {
    cCount <- $cCount + 1;
    return $x + $cCount
  };
}

module Inc2 : Orc {
  proc get (x : ℤ) : ℤ {
    var y : ℤ;
    y <- $x;
    cCount <- $cCount + 1;
    return $cCount + $y
  };
}

module Game using (O : Orc, A : ADV) {
  proc main () : ℤ {
    var r : ℤ;
    cFlag <- true;
    r <- call A(O).run ();
    return $r
  };
}

module Twice using (O : Orc) {
  proc main (x : ℤ) : ℤ {
    var r : ℤ;
    r <- call O.get ($x);
    r <- call O.get ($r);
    return $r
  };
}

/-- The two oracles agree. -/
theorem Inc_Inc2 : equiv[ Inc.get ~ Inc2.get : ={arg, cCount} ==> ={res, cCount} ] := by
  equiv_proc; equiv_auto
  rintro _ _ _ _ ⟨rfl, rfl⟩
  exact ⟨by ring, rfl⟩

/-! ## `proc`, `inline` -/

-- `proc` on concrete procedures: the bodies, the parameters as variables
/--
trace: R : ℤ → ℤ → Prop
⊢ equiv[ ={x, cCount} ==> R §r{1} §r{2} ] {
      var x : ℤ, r : ℤ;
      r <- call Inc.get.procedure (§x);
      r <- call Inc.get.procedure (§r);
} ~ {
      var x : ℤ, r : ℤ;
      r <- call Inc2.get.procedure (§x);
      r <- call Inc2.get.procedure (§r);
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) :
    equiv[ Twice(Inc).main ~ Twice(Inc2).main : ={arg, cCount} ==> R §res{1} §res{2} ] := by
  equiv_proc
  trace_state
  sorry

-- `inline*`: the callees' code, their locals named per side
/--
trace: R : ℤ → ℤ → Prop
⊢ equiv[ ={x, cCount} ==> R §r{1} §r{2} ] {
      var x : ℤ, x0 : ℤ, r : ℤ, x1 : ℤ;
      reset_vars {"x0"} ∪ stringsStartingWith "@@." \ {"@@.x"};
      x0 <- §x;
      cCount <- §cCount + 1;
      r <- §x0 + §cCount;
      reset_vars {"x1"} ∪ stringsStartingWith "@." \ {"@.x"};
      x1 <- §r;
      cCount <- §cCount + 1;
      r <- §x1 + §cCount;
} ~ {
      var x : ℤ, x0 : ℤ, r : ℤ, x1 : ℤ, y : ℤ, y0 : ℤ;
      reset_vars {"x0", "y"} ∪ stringsStartingWith "@@." \ {"@@.x", "@@.y"};
      x0 <- §x;
      y <- §x0;
      cCount <- §cCount + 1;
      r <- §cCount + §y;
      reset_vars {"x1", "y0"} ∪ stringsStartingWith "@." \ {"@.x", "@.y"};
      x1 <- §r;
      y0 <- §x1;
      cCount <- §cCount + 1;
      r <- §cCount + §y0;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) :
    equiv[ Twice(Inc).main ~ Twice(Inc2).main : ={arg, cCount} ==> R §res{1} §res{2} ] := by
  equiv_proc; stmt_inline*
  trace_state
  sorry

/-! ## `call` on concrete callees -/

-- `call (_ : P ==> Q)`: the callees' judgment, then the code before
/--
trace: case callee
R : ℤ → ℤ → Prop
⊢ equiv[ Inc.get (x) ~ Inc2.get (x) : ={params, cCount} ==> ={res, cCount} ]

R : ℤ → ℤ → Prop
⊢ equiv[ ={x, cCount} ==>
      ={r, cCount} ∧
        ∀ (r₁ : ℤ) (g₁ : VariableAssignment) (r₂ : ℤ) (g₂ : VariableAssignment),
          r₁ = r₂ ∧ cCount.get g₁ = cCount.get g₂ → R r₁ r₂ ]
      {
      var x : ℤ, r : ℤ;
      r <- call Inc.get.procedure (§x);
} ~ {
      var x : ℤ, r : ℤ;
      r <- call Inc2.get.procedure (§x);
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
example (R : ℤ → ℤ → Prop) :
    equiv[ Twice(Inc).main ~ Twice(Inc2).main : ={arg, cCount} ==> R §res{1} §res{2} ] := by
  equiv_proc
  equiv_call (_ : ={arg, cCount} ==> ={res, cCount})
  trace_state
  all_goals sorry

-- `call H`, `H` a judgment about the callees
/--
trace: R : ℤ → ℤ → Prop
⊢ equiv[ ={x, cCount} ==>
      ={r, cCount} ∧
        ∀ (r₁ : ℤ) (g₁ : VariableAssignment) (r₂ : ℤ) (g₂ : VariableAssignment),
          r₁ = r₂ ∧ cCount.get g₁ = cCount.get g₂ → R r₁ r₂ ]
      {
      var x : ℤ, r : ℤ;
      r <- call Inc.get.procedure (§x);
} ~ {
      var x : ℤ, r : ℤ;
      r <- call Inc2.get.procedure (§x);
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) :
    equiv[ Twice(Inc).main ~ Twice(Inc2).main : ={arg, cCount} ==> R §res{1} §res{2} ] := by
  equiv_proc
  equiv_call Inc_Inc2
  trace_state
  all_goals sorry

-- `call H`, `H` a judgment about procedure aliases of the callees (`proc get = O.get;`, EC's
-- `call (RO_LRO_D (D2(D)))`): the aliases are rewritten to their callees first.  A single-procedure
-- module without a module type (`Fw(Inc).get` is `Fw` applied), and one with a type (`FwT(Inc).get`
-- is `Orc.get` of it applied)
module Fw using (O : Orc) {
  proc get = O.get;
}

module FwT using (O : Orc) : Orc {
  proc get = O.get;
}

theorem Fw_Inc_Inc2 : equiv[ Fw(Inc).get ~ Fw(Inc2).get : ={arg, cCount} ==> ={res, cCount} ] := by
  simp only [Fw.apply_simp, Fw.get.apply_simp]
  exact Inc_Inc2

theorem FwT_Inc_Inc2 :
    equiv[ FwT(Inc).get ~ FwT(Inc2).get : ={arg, cCount} ==> ={res, cCount} ] := by
  simp only [FwT.apply_simp, Orc.get.mk_simp, FwT.get.apply_simp]
  exact Inc_Inc2

/--
trace: R : ℤ → ℤ → Prop
⊢ equiv[ ={x, cCount} ==>
      ={r, cCount} ∧
        ∀ (r₁ : ℤ) (g₁ : VariableAssignment) (r₂ : ℤ) (g₂ : VariableAssignment),
          r₁ = r₂ ∧ cCount.get g₁ = cCount.get g₂ → R r₁ r₂ ]
      {
      var x : ℤ, r : ℤ;
      r <- call Inc.get.procedure (§x);
} ~ {
      var x : ℤ, r : ℤ;
      r <- call Inc2.get.procedure (§x);
}
---
trace: R : ℤ → ℤ → Prop
⊢ equiv[ ={x, cCount} ==>
      ={x, cCount} ∧
        ∀ (r₁ : ℤ) (g₁ : VariableAssignment) (r₂ : ℤ) (g₂ : VariableAssignment),
          r₁ = r₂ ∧ cCount.get g₁ = cCount.get g₂ →
            (r₁ = r₂ ∧ cCount.get g₁ = cCount.get g₂) ∧
              ∀ (r₁ : ℤ) (g₁ : VariableAssignment) (r₂ : ℤ) (g₂ : VariableAssignment),
                r₁ = r₂ ∧ cCount.get g₁ = cCount.get g₂ → R r₁ r₂ ]
      {
      var x : ℤ;
      skip;
} ~
    {
      skip;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) :
    equiv[ Twice(Inc).main ~ Twice(Inc2).main : ={arg, cCount} ==> R §res{1} §res{2} ] := by
  equiv_proc
  equiv_call Fw_Inc_Inc2
  trace_state
  equiv_call FwT_Inc_Inc2
  trace_state
  all_goals sorry

-- `call H` where the program calls the alias as `H` names it (EC's `proc; call (RO_LRO_D Dist _)`,
-- no `inline*` before): the judgment as written fits
#guard_msgs(drop warning) in
example (R : ℤ → ℤ → Prop) :
    equiv[ Twice(FwT(Inc)).main ~ Twice(FwT(Inc2)).main : ={arg, cCount} ==> R §res{1} §res{2} ] := by
  equiv_proc
  equiv_call FwT_Inc_Inc2
  equiv_call FwT_Inc_Inc2
  all_goals sorry

-- `inline*` and a call of a procedure alias: the call is one of the aliased procedure (EC's alias
-- is that procedure), so `FwT(O).get` reads `O.get` and the two sides are the same code
/--
trace: O : Orc
⊢ equiv[ ={x, glob O} ==> ={r, glob O} ] {
      var x : ℤ, r : ℤ;
      r <- call O.get.procedure (§x);
      r <- call O.get.procedure (§r);
} ~ {
      var x : ℤ, r : ℤ;
      r <- call O.get.procedure (§x);
      r <- call O.get.procedure (§r);
}
-/
#guard_msgs in
example (O : Orc) :
    equiv[ Twice(FwT(O)).main ~ Twice(O).main : ={arg, glob O} ==> ={res, glob O} ] := by
  equiv_proc; stmt_inline*
  trace_state
  sim

-- … and a concrete aliased procedure is then inlined as well
example : equiv[ Twice(FwT(Inc)).main ~ Twice(Inc).main : ={arg, cCount} ==> ={res, cCount} ] := by
  equiv_proc; stmt_inline*; sim

-- `call (_ : ={x})` on the same callee on both sides, no footprint stated for it: the one read
-- off its code (`fp_le`), and EC's frame (what the callee does not write is kept)
/--
trace: R : ℤ → ℤ → Prop
⊢ equiv[ ={x, cCount} ==>
      ={r, cCount.footprint.touched_getter} ∧
        ∀ (r₁ : ℤ) (g₁ : VariableAssignment) (r₂ : ℤ) (g₂ : VariableAssignment),
          r₁ = r₂ ∧ cCount.footprint.touched_getter.get g₁ = cCount.footprint.touched_getter.get g₂ → R r₁ r₂ ]
      {
      var x : ℤ, r : ℤ;
      r <- call Inc.get.procedure (§x);
} ~ {
      var x : ℤ, r : ℤ;
      r <- call Inc.get.procedure (§x);
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) :
    equiv[ Twice(Inc).main ~ Twice(Inc).main : ={arg, cCount} ==> R §res{1} §res{2} ] := by
  equiv_proc
  equiv_call (_ : ={cCount})
  trace_state
  all_goals sorry

/-- `Inc` touches `cCount` only (EC reads it off the code). -/
@[fp_bound] theorem fvP_Inc : FVP.fvP Inc ≤ cCount.footprint := by fp_module cCount

-- the same with the callee's footprint known
/--
trace: R : ℤ → ℤ → Prop
⊢ equiv[ ={x, cCount} ==>
      ={r, cCount.footprint.touched_getter} ∧
        ∀ (r₁ : ℤ) (g₁ : VariableAssignment) (r₂ : ℤ) (g₂ : VariableAssignment),
          r₁ = r₂ ∧ cCount.footprint.touched_getter.get g₁ = cCount.footprint.touched_getter.get g₂ → R r₁ r₂ ]
      {
      var x : ℤ, r : ℤ;
      r <- call Inc.get.procedure (§x);
} ~ {
      var x : ℤ, r : ℤ;
      r <- call Inc.get.procedure (§x);
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) :
    equiv[ Twice(Inc).main ~ Twice(Inc).main : ={arg, cCount} ==> R §res{1} §res{2} ] := by
  equiv_proc
  equiv_call (_ : ={cCount})
  trace_state
  all_goals sorry

-- `call` alone on the same callee
/--
trace: case hpre
R : ℤ → ℤ → Prop
⊢ equiv[ ={x, cCount} ==> ={localVarLens "r" ℤ} ∧ ={allGlobals} ∧ ∀ (r : ℤ) (g : VariableAssignment), R r r ] {
      var x : ℤ;
      (localVarLens "r" ℤ) <- call Inc.get.procedure (§x);
} ~ {
      var x : ℤ;
      (localVarLens "r" ℤ) <- call Inc.get.procedure (§x);
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) :
    equiv[ Twice(Inc).main ~ Twice(Inc).main : ={arg, cCount} ==> R §res{1} §res{2} ] := by
  equiv_proc
  equiv_call
  trace_state
  all_goals sorry

/-! ## `call` on a declared adversary -/

section

declare module A <: ADV {-cCount, -cFlag}

-- `call (_ : ={glob A, x})`: the oracles' judgments, then the code before
/--
trace: case oracle
A : ADV
inst✝ : Module.Declared A (cCount.footprint ⊔ cFlag.footprint)
R : ℤ → ℤ → Prop
⊢ prhlProc
    (fun a₁ g₁ a₂ g₂ ↦
      a₁ = a₂ ∧ (FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A).touched_getter.get g₂ ∧ cCount.get g₁ = cCount.get g₂)
    Inc.get.procedure Inc2.get.procedure fun r₁ g₁ r₂ g₂ ↦
    r₁ = r₂ ∧ (FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A).touched_getter.get g₂ ∧ cCount.get g₁ = cCount.get g₂

case pre
A : ADV
inst✝ : Module.Declared A (cCount.footprint ⊔ cFlag.footprint)
R : ℤ → ℤ → Prop
⊢ equiv[ ={glob A, cCount} ==>
      globInvF cCount (FVP.fvP A) Eq §allGlobals{1} §allGlobals{2} ∧
        ∀ (r₁ : ℤ) (g₁ : VariableAssignment) (r₂ : ℤ) (g₂ : VariableAssignment),
          r₁ = r₂ ∧ globInvF cCount (FVP.fvP A) Eq g₁ g₂ → R r₁ r₂ ]
      {
      cFlag <- true;
} ~
    {
      cFlag <- true;
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
example (R : ℤ → ℤ → Prop) :
    equiv[ Game(Inc, A).main ~ Game(Inc2, A).main : ={glob A, cCount} ==> R §res{1} §res{2} ] := by
  equiv_proc
  equiv_call (_ : ={glob A, cCount})
  trace_state
  all_goals sorry

-- `call (_ : ={glob A} ∧ I)`: the oracles keep the invariant
/--
trace: case oracle
A : ADV
inst✝ : Module.Declared A (cCount.footprint ⊔ cFlag.footprint)
R : ℤ → ℤ → Prop
⊢ prhlProc
    (fun a₁ g₁ a₂ g₂ ↦
      a₁ = a₂ ∧
        (FVP.fvP A ⊔ FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A ⊔ FVP.fvP A).touched_getter.get g₂ ∧
          cCount.get g₁ = cCount.get g₂)
    Inc.get.procedure Inc2.get.procedure fun r₁ g₁ r₂ g₂ ↦
    r₁ = r₂ ∧
      (FVP.fvP A ⊔ FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A ⊔ FVP.fvP A).touched_getter.get g₂ ∧
        cCount.get g₁ = cCount.get g₂

case pre
A : ADV
inst✝ : Module.Declared A (cCount.footprint ⊔ cFlag.footprint)
R : ℤ → ℤ → Prop
⊢ prhlStmt
    (fun σ₁ σ₂ ↦
      (FVP.fvP A).touched_getter.get σ₁.globals = (FVP.fvP A).touched_getter.get σ₂.globals ∧
        cCount.get σ₁.globals = cCount.get σ₂.globals)
    (GaudiProg[
        cFlag <- true;
  ])
    (GaudiProg[
        cFlag <- true;
  ])
    fun σ₁ σ₂ ↦
    (() = () ∧
        (FVP.fvP A ⊔ FVP.fvP A).touched_getter.get σ₁.globals = (FVP.fvP A ⊔ FVP.fvP A).touched_getter.get σ₂.globals ∧
          cCount.get σ₁.globals = cCount.get σ₂.globals) ∧
      ∀ (r₁ : ℤ) (g₁ : VariableAssignment) (r₂ : ℤ) (g₂ : VariableAssignment),
        r₁ = r₂ ∧
            (FVP.fvP A ⊔ FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A ⊔ FVP.fvP A).touched_getter.get g₂ ∧
              cCount.get g₁ = cCount.get g₂ →
          R ((localVarLens "r" ℤ).get ((liftLens (localVarLens "r" ℤ)).set r₁ (ProgramState.globalL.set g₁ σ₁)))
            ((localVarLens "r" ℤ).get ((liftLens (localVarLens "r" ℤ)).set r₂ (ProgramState.globalL.set g₂ σ₂)))
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 2 goals and ends with 2 goals, 2 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) :
    equiv[ Game(Inc, A).main ~ Game(Inc2, A).main : ={glob A, cCount} ==> R §res{1} §res{2} ] := by
  equiv_proc
  equiv_call (_ : ={glob A} ∧ §cCount{1} = §cCount{2})
  trace_state
  all_goals sorry

-- `call (_ : ={glob M})`, every item a `glob`: a concrete module's `glob` is its variables,
-- `glob A` is kept without being named, the oracles' goals are EC's `={arg, x} ==> ={res, x}`
/--
trace: case oracle
A : ADV
inst✝ : Module.Declared A (cCount.footprint ⊔ cFlag.footprint)
R : ℤ → ℤ → Prop
⊢ prhlProc (fun a₁ g₁ a₂ g₂ ↦ a₁ = a₂ ∧ cCount.get g₁ = cCount.get g₂) Inc.get.procedure Inc2.get.procedure
    fun r₁ g₁ r₂ g₂ ↦ r₁ = r₂ ∧ cCount.get g₁ = cCount.get g₂

case pre
A : ADV
inst✝ : Module.Declared A (cCount.footprint ⊔ cFlag.footprint)
R : ℤ → ℤ → Prop
⊢ prhlStmt
    (fun σ₁ σ₂ ↦
      (FVP.fvP A).touched_getter.get σ₁.globals = (FVP.fvP A).touched_getter.get σ₂.globals ∧
        cCount.get σ₁.globals = cCount.get σ₂.globals)
    (GaudiProg[
        cFlag <- true;
  ])
    (GaudiProg[
        cFlag <- true;
  ])
    fun σ₁ σ₂ ↦
    (() = () ∧
        (FVP.fvP A).touched_getter.get σ₁.globals = (FVP.fvP A).touched_getter.get σ₂.globals ∧
          cCount.get σ₁.globals = cCount.get σ₂.globals) ∧
      ∀ (r₁ : ℤ) (g₁ : VariableAssignment) (r₂ : ℤ) (g₂ : VariableAssignment),
        r₁ = r₂ ∧
            (FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A).touched_getter.get g₂ ∧ cCount.get g₁ = cCount.get g₂ →
          R ((localVarLens "r" ℤ).get ((liftLens (localVarLens "r" ℤ)).set r₁ (ProgramState.globalL.set g₁ σ₁)))
            ((localVarLens "r" ℤ).get ((liftLens (localVarLens "r" ℤ)).set r₂ (ProgramState.globalL.set g₂ σ₂)))
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 2 goals and ends with 2 goals, 2 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) :
    equiv[ Game(Inc, A).main ~ Game(Inc2, A).main : ={glob A, cCount} ==> R §res{1} §res{2} ] := by
  equiv_proc
  equiv_call (_ : ={glob Inc})
  trace_state
  all_goals sorry

/-! ## `sim` -/

-- `sim` on equal code with an abstract call, after a write of a global on both sides: it asks for
-- all globals equal after the write, which the precondition does not give (EC's `sim` closes
-- this)
/--
warning: sim: no equality set for the call (a region the precondition keeps equal that contains the callee); using the plain call rule, which asks for all globals equal
reason: sim: no region contains the callee
---
error: unsolved goals
case h
A : ADV
inst✝ : Module.Declared A (cCount.footprint ⊔ cFlag.footprint)
⊢ ∀ (globals₁ globals₂ : VariableAssignment),
    (FVP.fvP A).touched_getter.get globals₁ = (FVP.fvP A).touched_getter.get globals₂ ∧
        cCount.get globals₁ = cCount.get globals₂ →
      cFlag.set true globals₁ = cFlag.set true globals₂
-/
#guard_msgs in
example : equiv[ Game(Inc, A).main ~ Game(Inc, A).main : ={glob A, cCount} ==> ={res, cCount} ] := by
  equiv_proc; sim

-- `sim` where the callees differ: it stops there
/--
trace: A : ADV
inst✝ : Module.Declared A (cCount.footprint ⊔ cFlag.footprint)
⊢ equiv[ ={glob A, cCount} ==> ={r} ] {
      var r : ℤ;
      cFlag <- true;
      r <- call (Module.app A Inc).procedure ();
} ~ {
      var r : ℤ;
      cFlag <- true;
      r <- call (Module.app A Inc2).procedure ();
}
---
warning: declaration uses `sorry`
---
warning: 'sim' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example : equiv[ Game(Inc, A).main ~ Game(Inc2, A).main : ={glob A, cCount} ==> ={res} ] := by
  equiv_proc; sim
  trace_state
  all_goals sorry

end

/-! ## A declared adversary with a region for its `glob` (`declare module … with glob R`)

The lemma's hypothesis restricts the oracles against the region `R` (`{-R}`), so that it applies
to an adversary built from a declared one (`Logic/DeclareModule.lean`). -/

section

declare module A <: ADV {-cCount, -cFlag} with glob R

variable (A_ll : ∀ (O <: Orc {-R}), islossless O.get → islossless A(O).run)

-- `call (_ : bad, I)`: `A_ll`'s statement is against the region
include A_ll in
/--
trace: case ll
A : ADV
inst✝² : Module.Declared A (cCount.footprint ⊔ cFlag.footprint)
R : Footprint VariableAssignment
inst✝¹ : Module.ECGlob A R
inst✝ : R.Restricted (cCount.footprint ⊔ cFlag.footprint)
A_ll : ∀ (O : Orc) [Module.Declared O R], O.get.procedure.IsLossless → (Module.app A O).procedure.IsLossless
⊢ ∀ (O0 : Orc) [inst : Module.Declared O0 R], O0.get.procedure.IsLossless → (Module.app A O0).procedure.IsLossless
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : equiv[ Game(Inc, A).main ~ Game(Inc, A).main :
    ={glob A, cCount} ==> ¬ (10 < §cCount{2}) → ={res} ] := by
  equiv_proc
  equiv_call (_ : 10 < §cCount, ={cCount})
  · trace_state
    exact A_ll
  all_goals sorry

-- `call (_ : I)`, `I` without a `={…}` part: `glob A` is kept without being named
/--
trace: case oracle
A : ADV
inst✝² : Module.Declared A (cCount.footprint ⊔ cFlag.footprint)
R✝ : Footprint VariableAssignment
inst✝¹ : Module.ECGlob A R✝
inst✝ : R✝.Restricted (cCount.footprint ⊔ cFlag.footprint)
A_ll : ∀ (O : Orc) [Module.Declared O R✝], O.get.procedure.IsLossless → (Module.app A O).procedure.IsLossless
R : ℤ → ℤ → Prop
⊢ prhlProc (fun a₁ g₁ a₂ g₂ ↦ a₁ = a₂ ∧ cCount.get g₁ = cCount.get g₂) Inc.get.procedure Inc2.get.procedure
    fun r₁ g₁ r₂ g₂ ↦ r₁ = r₂ ∧ cCount.get g₁ = cCount.get g₂

case pre
A : ADV
inst✝² : Module.Declared A (cCount.footprint ⊔ cFlag.footprint)
R✝ : Footprint VariableAssignment
inst✝¹ : Module.ECGlob A R✝
inst✝ : R✝.Restricted (cCount.footprint ⊔ cFlag.footprint)
A_ll : ∀ (O : Orc) [Module.Declared O R✝], O.get.procedure.IsLossless → (Module.app A O).procedure.IsLossless
R : ℤ → ℤ → Prop
⊢ prhlStmt
    (fun σ₁ σ₂ ↦
      (FVP.fvP A).touched_getter.get σ₁.globals = (FVP.fvP A).touched_getter.get σ₂.globals ∧
        cCount.get σ₁.globals = cCount.get σ₂.globals)
    (GaudiProg[
        cFlag <- true;
  ])
    (GaudiProg[
        cFlag <- true;
  ])
    fun σ₁ σ₂ ↦
    (() = () ∧
        (FVP.fvP A).touched_getter.get σ₁.globals = (FVP.fvP A).touched_getter.get σ₂.globals ∧
          cCount.get σ₁.globals = cCount.get σ₂.globals) ∧
      ∀ (r₁ : ℤ) (g₁ : VariableAssignment) (r₂ : ℤ) (g₂ : VariableAssignment),
        r₁ = r₂ ∧
            (FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A).touched_getter.get g₂ ∧ cCount.get g₁ = cCount.get g₂ →
          R ((localVarLens "r" ℤ).get ((liftLens (localVarLens "r" ℤ)).set r₁ (ProgramState.globalL.set g₁ σ₁)))
            ((localVarLens "r" ℤ).get ((liftLens (localVarLens "r" ℤ)).set r₂ (ProgramState.globalL.set g₂ σ₂)))
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 2 goals and ends with 2 goals, 2 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example (R : ℤ → ℤ → Prop) :
    equiv[ Game(Inc, A).main ~ Game(Inc2, A).main : ={glob A, cCount} ==> R §res{1} §res{2} ] := by
  equiv_proc
  equiv_call (_ : §cCount{1} = §cCount{2})
  trace_state
  all_goals sorry

-- the restrictions against the region, as EC checks them: a concrete module (its variables are
-- in `R`'s restriction), a module built from one declared against `R`
example : Module.Declared Inc R := ⟨by fp_finite, by fp_disjoint⟩

example (O : Orc) [Module.Declared O R] : FVP.fvP (Module.app Twice O) ≤ Rᶜ := by fp_disjoint

-- the region is restricted against less (as a declaration is)
example : Footprint.Restricted R cFlag.footprint := inferInstance

example : Module.Declared A cFlag.footprint := inferInstance

-- `sim`'s closer with the restrictions in context (cleared for its `simp_all` attempts, which
-- would otherwise simplify them each time): the implication `equiv_skip` leaves is closed
#guard_msgs in
example : equiv[ ={cCount} ==> ={cCount} ] {
      cCount <- $cCount + 1;
    } ~ {
      cCount <- $cCount + 1;
    } := by
  sim

end

section

declare module B <: Orc {-cCount}
declare module A <: ADV {-cCount, -cFlag, -B} with glob R

-- an abstract module the region is restricted against
example : Module.Declared (Module.app Twice B) R := ⟨by fp_finite, by fp_disjoint⟩

end

end GaudisCrypt.ECCallsTest
