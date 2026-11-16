import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Syntax.ModuleVar
import GaudisCrypt.Language.Variables
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECCallEquiv
import GaudisCrypt.Logic.ECCallUpto
import GaudisCrypt.Logic.StmtSwap
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Lib.EC.Logic
import GaudisCrypt.Lib.EC.ROM
import GaudisCrypt.Syntax.Clone
import GaudisCrypt.Logic.ECInline

/-!
# Golden tests: a declared module with several procedures and an oracle

EC's `module type Adv (O : POr) = { proc a1 … proc a2 … }`, `declare module A <: Adv {-…}`: the
call rules on `A(O).a1`, `A(O).a2` (an accessor of the functor's result): the invariant call
with EC's frame of the untouched globals, the up-to-bad call with EC's full precondition, `swap`
of a sampling into a global past the call, and pHL's `call` with the adversary's losslessness; and
`inline` of the oracle of a cloned theory (`clone import ROM as H`, `H.Lazy.LRO.o`)
(see `Logic/ECAutoTest.lean` for the format; `scripts/update_golden.py` refreshes the expected
text).
-/

namespace GaudisCrypt.ECCallMultiProcTest

open GaudisCrypt GaudisCrypt.EC

global_var O.v : ℕ
global_var G.z : ℕ
global_var G.w : ℕ

moduletype POr {
  proc o (x : ℕ) -> ℕ;
}

module O : POr {
  proc o (x : ℕ) : ℕ {
    O.v <- $O.v + $x;
    return $O.v
  };
}

@[fp_bound] theorem fvP_O : FVP.fvP O ≤ O.v.footprint := by fp_module O.v

moduletype AdvProcs {
  proc a1 (p : ℕ) -> ℕ;
  proc a2 (c : ℕ) -> Bool;
}

abbrev Adv := POr →ₘ AdvProcs

module G using (A : Adv) {
  proc main () : Bool {
    var x : ℕ, b : Bool;
    G.z <$ SubProbability.uniform (α := Fin 2) >>= fun i => pure i.val;
    G.w <$ SubProbability.uniform (α := Fin 2) >>= fun i => pure i.val;
    x <- call A(O).a1 ($G.z);
    b <- call A(O).a2 ($x + $G.z);
    return $b
  };
}

section

declare module A <: Adv {-O, -G}

variable (A_a2_ll : ∀ (X <: POr {-A}), islossless X.o → islossless A(X).a2)

-- the invariant call on `A(O).a2`: the oracle's judgment, then the code before, its
-- postcondition with EC's frame (`G.z`, which neither `A` nor `O` touches, keeps its value)
/--
trace: case oracle
A : Adv
inst✝ : Module.Declared A (O.v.footprint ⊔ G.z.footprint ⊔ G.w.footprint)
A_a2_ll : ∀ (X : POr) [Module.Declared X (FVP.fvP A).glob], X.o.procedure.IsLossless → A(X).a2.procedure.IsLossless
⊢ prhlProc
    (fun a₁ g₁ a₂ g₂ ↦
      a₁ = a₂ ∧ (FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A).touched_getter.get g₂ ∧ O.v.get g₁ = O.v.get g₂)
    O.o.procedure O.o.procedure fun r₁ g₁ r₂ g₂ ↦
    r₁ = r₂ ∧ (FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A).touched_getter.get g₂ ∧ O.v.get g₁ = O.v.get g₂

case pre
A : Adv
inst✝ : Module.Declared A (O.v.footprint ⊔ G.z.footprint ⊔ G.w.footprint)
A_a2_ll : ∀ (X : POr) [Module.Declared X (FVP.fvP A).glob], X.o.procedure.IsLossless → A(X).a2.procedure.IsLossless
⊢ equiv[ ={glob A, O.v, G.z} ==>
      (§x{1} + §G.z{1} = §x{2} + §G.z{2} ∧ ={glob A, O.v}) ∧
        ∀ (r₁ : Bool) (g₁ : VariableAssignment) (r₂ : Bool) (g₂ : VariableAssignment),
          r₁ = r₂ ∧ (FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A).touched_getter.get g₂ ∧ O.v.get g₁ = O.v.get g₂ →
            G.z.get g₁ = §G.z{1} → G.z.get g₂ = §G.z{2} → r₁ = r₂ ∧ G.z.get g₁ = G.z.get g₂ ]
      {
      var x : ℕ;
      G.z <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      G.w <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      x <- call A(O).a1.procedure (§G.z);
} ~ {
      var x : ℕ;
      G.z <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      G.w <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      x <- call A(O).a1.procedure (§G.z);
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
example : equiv[ G(A).main ~ G(A).main : ={glob A, O.v, G.z} ==> ={res, G.z} ] := by
  equiv_proc
  equiv_call (_ : ={glob A, O.v})
  trace_state
  all_goals sorry

-- the up-to-bad call: EC's goals (`ll`, the oracle's `oracle`, `left`, `right`, the deviation
-- `right_ll`), then the code before with EC's precondition `bad ∨ (={args, glob A} ∧ I ∧ ¬bad)`
/--
trace: case ll
A : Adv
inst✝ : Module.Declared A (O.v.footprint ⊔ G.z.footprint ⊔ G.w.footprint)
A_a2_ll : ∀ (X : POr) [Module.Declared X (FVP.fvP A).glob], X.o.procedure.IsLossless → A(X).a2.procedure.IsLossless
⊢ ∀ (O0 : POr) [inst : Module.Declared O0 (FVP.fvP A).glob], O0.o.procedure.IsLossless → A(O0).a2.procedure.IsLossless

case oracle
A : Adv
inst✝ : Module.Declared A (O.v.footprint ⊔ G.z.footprint ⊔ G.w.footprint)
A_a2_ll : ∀ (X : POr) [Module.Declared X (FVP.fvP A).glob], X.o.procedure.IsLossless → A(X).a2.procedure.IsLossless
⊢ prhlProc
    (fun a₁ g₁ a₂ g₂ ↦
      ¬5 < O.v.get g₂ ∧
        a₁ = a₂ ∧ (FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A).touched_getter.get g₂ ∧ O.v.get g₁ = O.v.get g₂)
    O.o.procedure O.o.procedure fun r₁ g₁ r₂ g₂ ↦
    if 5 < O.v.get g₂ then True
    else r₁ = r₂ ∧ (FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A).touched_getter.get g₂ ∧ O.v.get g₁ = O.v.get g₂

case left
A : Adv
inst✝ : Module.Declared A (O.v.footprint ⊔ G.z.footprint ⊔ G.w.footprint)
A_a2_ll : ∀ (X : POr) [Module.Declared X (FVP.fvP A).glob], X.o.procedure.IsLossless → A(X).a2.procedure.IsLossless
⊢ O.o.procedure.IsLossless

case right
A : Adv
inst✝ : Module.Declared A (O.v.footprint ⊔ G.z.footprint ⊔ G.w.footprint)
A_a2_ll : ∀ (X : POr) [Module.Declared X (FVP.fvP A).glob], X.o.procedure.IsLossless → A(X).a2.procedure.IsLossless
ω₁✝ : ℕ
⊢ phoareProc (fun x g ↦ 5 < O.v.get g ∧ True) O.o.procedure (fun x g ↦ indicatorE (5 < O.v.get g ∧ True)) Eq fun x x_1 ↦
    1

case right_ll
A : Adv
inst✝ : Module.Declared A (O.v.footprint ⊔ G.z.footprint ⊔ G.w.footprint)
A_a2_ll : ∀ (X : POr) [Module.Declared X (FVP.fvP A).glob], X.o.procedure.IsLossless → A(X).a2.procedure.IsLossless
⊢ O.o.procedure.IsLossless

case pre
A : Adv
inst✝ : Module.Declared A (O.v.footprint ⊔ G.z.footprint ⊔ G.w.footprint)
A_a2_ll : ∀ (X : POr) [Module.Declared X (FVP.fvP A).glob], X.o.procedure.IsLossless → A(X).a2.procedure.IsLossless
⊢ equiv[ ={glob A, O.v, G.z} ==>
      (5 < §O.v{2} ∨ §x{1} + §G.z{1} = §x{2} + §G.z{2} ∧ ={glob A} ∧ ={O.v} ∧ ¬5 < §O.v{2}) ∧
        ∀ (r₁ : Bool) (g₁ : VariableAssignment) (r₂ : Bool) (g₂ : VariableAssignment),
          5 < O.v.get g₂ ∨
              r₁ = r₂ ∧
                (FVP.fvP A).touched_getter.get g₁ = (FVP.fvP A).touched_getter.get g₂ ∧
                  O.v.get g₁ = O.v.get g₂ ∧ ¬5 < O.v.get g₂ →
            r₁ = r₂ ∨ 5 < O.v.get g₂ ]
      {
      var x : ℕ;
      G.z <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      G.w <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      x <- call A(O).a1.procedure (§G.z);
} ~ {
      var x : ℕ;
      G.z <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      G.w <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      x <- call A(O).a1.procedure (§G.z);
}
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 6 goals and ends with 6 goals, 6 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : equiv[ G(A).main ~ G(A).main : ={glob A, O.v, G.z} ==>
    (§res{1} = §res{2} ∨ 5 < §O.v{2}) ] := by
  equiv_proc
  equiv_call (_ : 5 < §O.v, §O.v{1} = §O.v{2})
  trace_state
  all_goals sorry

-- EC's `swap`: a sampling into a global the adversary is restricted against, past its call
/--
trace: A : Adv
inst✝ : Module.Declared A (O.v.footprint ⊔ G.z.footprint ⊔ G.w.footprint)
A_a2_ll : ∀ (X : POr) [Module.Declared X (FVP.fvP A).glob], X.o.procedure.IsLossless → A(X).a2.procedure.IsLossless
⊢ equiv[ ={glob A, O.v, G.z} ==> ={b, G.z} ] {
      var x : ℕ, b : Bool;
      G.z <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      x <- call A(O).a1.procedure (§G.z);
      G.w <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      b <- call A(O).a2.procedure (§x + §G.z);
} ~ {
      var x : ℕ, b : Bool;
      G.z <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      G.w <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      x <- call A(O).a1.procedure (§G.z);
      b <- call A(O).a2.procedure (§x + §G.z);
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : equiv[ G(A).main ~ G(A).main : ={glob A, O.v, G.z} ==> ={res, G.z} ] := by
  equiv_proc
  stmt_swap{1} 2 1
  trace_state
  sorry

-- pHL's `call (A_ll O ?_)` on an event: the oracle's losslessness, then the event for every
-- result
/--
trace: A : Adv
inst✝ : Module.Declared A (O.v.footprint ⊔ G.z.footprint ⊔ G.w.footprint)
A_a2_ll : ∀ (X : POr) [Module.Declared X (FVP.fvP A).glob], X.o.procedure.IsLossless → A(X).a2.procedure.IsLossless
⊢ phoare[ True ==>
      if ∀ (v : Bool), indicatorE (v = true ∨ ¬v = true) = 1 then 1
      else
        A(O).a2.procedure.ewp (§x + §G.z) (fun v gl ↦ indicatorE (v = true ∨ ¬v = true))
          CurrentState.state.globals ] = 1 {
      var x : ℕ;
      G.z <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      G.w <$ do
      let i ← SubProbability.uniform
      pure ↑i;
      x <- call A(O).a1.procedure (§G.z);
}

case call_3
A : Adv
inst✝ : Module.Declared A (O.v.footprint ⊔ G.z.footprint ⊔ G.w.footprint)
A_a2_ll : ∀ (X : POr) [Module.Declared X (FVP.fvP A).glob], X.o.procedure.IsLossless → A(X).a2.procedure.IsLossless
⊢ O.o.procedure.IsLossless
---
warning: declaration uses `sorry`
---
warning: The following tactic starts with 2 goals and ends with 2 goals, 2 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
include A_a2_ll in
example : phoare[ G(A).main : True ==> §res ∨ ¬ §res ] = 1 := by
  phoare_proc
  phoare_call (@A_a2_ll _ ?_ ?_)
  trace_state
  all_goals sorry

-- as shown: `={glob A}` for the equation on `A`'s globals; two `glob`s stay two equations
-- (`={glob A, glob A}` would be read as one, on the regions joined)
/--
trace: A : Adv
inst✝ : Module.Declared A (O.v.footprint ⊔ G.z.footprint ⊔ G.w.footprint)
A_a2_ll : ∀ (X : POr) [Module.Declared X (FVP.fvP A).glob], X.o.procedure.IsLossless → A(X).a2.procedure.IsLossless
⊢ equiv[ ={glob A, O.v} ∧ ={glob A} ==> ={glob A, O.v} ] {
      skip;
} ~
    {
      skip;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : equiv[ (={glob A} ∧ ={O.v}) ∧ ={glob A} ==> ={glob A, O.v} ] {
      skip;
    } ~ {
      skip;
    } := by
  trace_state
  sorry

end

section CloneOracle

clone import GaudisCrypt.EC.ROM as H with
  type in_t <- ℕ, type out_t <- Bool, type d_in_t <- Unit, type d_out_t <- Bool,
  op dout <- fun _ => dbool

open H.Lazy

module Q {
  proc main (x : ℕ) : Bool {
    var r : Bool;
    r <- call LRO.o ($x);
    return $r
  };
}

-- EC's `inline *` on a call of a cloned theory's module: the body of `LRO.o` at the clone's
-- types and operators
/--
trace: ⊢ hoare[ True ==> True ] {
      var x0 : ℕ, x : ℕ, r0 : Bool, r : Bool;
      reset_vars {"x0", "r0"} ∪ stringsStartingWith "@." \ {"@.x", "@.r"};
      x0 <- §x;
      r0 <$ ROM.dout §x0;
      if (decide ¬(§ROM.Lazy.LRO.m).dom §x0) {
        ROM.Lazy.LRO.m <- (§ROM.Lazy.LRO.m).set §x0 §r0;
      }
      r <- oget ((§ROM.Lazy.LRO.m).get §x0);
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : hoare[ Q.main : True ==> True ] := by
  hoare_proc
  hoare_inline*
  trace_state
  sorry

end CloneOracle

end GaudisCrypt.ECCallMultiProcTest
