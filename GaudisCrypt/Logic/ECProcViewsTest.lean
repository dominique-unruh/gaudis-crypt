import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECInline
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.FootprintUpper
import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.Clone

/-!
# Golden tests: a module read at another module type; a procedure's footprint read off its code

* `equiv_proc` and `stmt_inline` open a procedure of a module read through a view at another
  module type (EasyCrypt's subtyping: a primitive handed on as the distinguisher's view of it),
  with no `module_norm` first (`Flatten.unfoldProcedure` retries through the views where the
  plain pass finds no body; the SHA-3 port's `LowerDist` and `Sponge(PRIMITIVE.view Perm)` are
  the cases the plain pass misses).
* `fp_le` bounds a `module`'s procedure that has no stated `@[fp_bound]` by its code
  (`ModuleFootprint.cachedBound`).
-/

namespace GaudisCrypt.ECProcViewsTest

open GaudisCrypt

global_var cnt : ℤ

moduletype PRIM {
  proc init () -> Unit;
  proc f (x : ℤ) -> ℤ;
}

moduletype DPRIM {
  proc f (x : ℤ) -> ℤ;
}

/-- The distinguisher's view of a primitive (a hand-written record, as the first SHA-3 port's
`PRIMITIVE.view`). -/
noncomputable def PRIM.view (P : PRIM) : DPRIM :=
  DPRIM.mk { f := PRIM.f P }

module Ctr : PRIM {
  proc init () : Unit {
    cnt <- 0;
    return ()
  };
  proc f (x : ℤ) : ℤ {
    cnt <- $cnt + 1;
    return $x + 1
  };
}

/-- `Ctr` as the distinguisher sees it. -/
noncomputable abbrev CtrView : DPRIM := PRIM.view Ctr

-- `proc` on the view's procedure: the body of `Ctr.f`
/--
trace: ⊢ equiv[ ={x, cnt} ==> §x{1} + 1 = §x{2} + 1 ∧ ={cnt} ] {
      var x : ℤ;
      cnt <- §cnt + 1;
} ~
    {
      cnt <- §cnt + 1;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : equiv[ CtrView.f (x) ~ Ctr.f (x) : ={x, cnt} ==> ={res, cnt} ] := by
  equiv_proc
  trace_state
  sorry

module G {
  proc run () : ℤ {
    var y : ℤ;
    y <- call CtrView.f ((1 : ℤ));
    return $y
  };
}

module H {
  proc run () : ℤ {
    var y : ℤ;
    y <- call Ctr.f ((1 : ℤ));
    return $y
  };
}

-- `call` on the view's procedure against the module's: the same-callee rule (tried within a
-- budget) does not see through the view, so their equality is left as the `callee` goal (`sim`
-- closes it by `simp; rfl`)
/--
error: unsolved goals
case callee
⊢ CtrView.f.procedure = Ctr.f.procedure
---
trace: case hpre
⊢ equiv[ ={cnt} ==> ={allGlobals} ] {
      skip;
} ~
    {
      skip;
}

case callee
⊢ CtrView.f.procedure = Ctr.f.procedure
-/
#guard_msgs in
example : equiv[ G.run ~ H.run : ={cnt} ==> ={res, cnt} ] := by
  equiv_proc
  equiv_call
  trace_state
  sorry

-- `call` on the same procedure on both sides: the same-callee rule, no `callee` goal
/--
trace: case hpre
⊢ equiv[ ={cnt} ==> ={allGlobals} ] {
      skip;
} ~
    {
      skip;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : equiv[ H.run ~ H.run : ={cnt} ==> ={res, cnt} ] := by
  equiv_proc
  equiv_call
  trace_state
  sorry

-- `inline` of a call of the view's procedure
#guard_msgs in
example : equiv[ G.run ~ H.run : ={cnt} ==> ={res, cnt} ] := by
  equiv_proc
  stmt_inline*
  equiv_auto

-- a procedure's footprint, with no `@[fp_bound]` stated: read off its code
#guard_msgs in
example : FVP.fvP Ctr.f ≤ cnt.footprint := by
  fp_le

global_var other : ℤ

-- the same procedure as a procedure module (`Module.proc Ctr.f.procedure`, how a call in inlined
-- code names it): read off `Ctr.f.procedure`'s code, for `fp_le` and for `fp_disjoint` (what
-- `stmt_swap` asks)
#guard_msgs in
example : FVP.fvP (Module.proc Ctr.f.procedure) ≤ cnt.footprint := by
  fp_le

#guard_msgs in
example : FVP.fvP (Module.proc Ctr.f.procedure) ≤ (other.footprint)ᶜ := by
  fp_disjoint

-- the bound read off the code is cached (`ModuleFootprint.boundCache`): used again in the same
-- proof, for a variable outside it and (failing) for one in it
#guard_msgs in
example : FVP.fvP Ctr.f ≤ (other.footprint)ᶜ ∧ FVP.fvP Ctr.f ≤ cnt.footprint := by
  refine ⟨by fp_disjoint, by fp_le⟩

#guard_msgs in
example : True := by
  have : FVP.fvP Ctr.f ≤ (other.footprint)ᶜ := by fp_disjoint
  fail_if_success have : FVP.fvP Ctr.f ≤ (cnt.footprint)ᶜ := by fp_disjoint
  trivial

/-! A module read at a clone's module type through another module type's record: the first SHA-3
port's module types (explicit type parameters) are the theory's (instance parameters) at the
clone's types, so a module built with the first port's constructor is one of the clone's module
type, and the clone's accessor (here of a clone inside a cloned theory, as SHA3OSecurity's
`SH.OIndif`) meets that record.  `proc` opens it as it is (SHA3OSecurity's GAP 3, whose hand
`simp only [ODPRIMITIVE_f_mk]` became unnecessary with the procedures across clones' module types,
2026-11-17). -/

namespace FP
variable (p : Type)
moduletype DPRIM2 {
  proc f (x : p) -> p;
}
end FP

namespace TH
/-- The theory's type. -/
class Params (p : outParam Type) : Prop
variable {p : Type} [Params p]
moduletype DPRIM2 {
  proc f (x : p) -> p;
}
end TH

-- a theory that clones `TH` (as `SecureHash` clones `OptionIndifferentiability`)
namespace TH2
/-- The theory's type. -/
class Params (q : outParam Type) : Prop
variable {q : Type} [Params q]
clone TH as I with type p <- q
end TH2

clone TH2 as TC with type q <- ℤ

module Inc2 {
  proc f (x : ℤ) : ℤ {
    cnt <- $cnt + 1;
    return $x + 1
  };
}

/-- `Inc2` handed on at the clone's module type, built with the first port's constructor. -/
noncomputable def Inc2Rec : TC.I.DPRIM2 := FP.DPRIM2.mk ℤ { f := Inc2.f }

-- `proc` on the clone's accessor of that record: the body of `Inc2.f` (EC's `proc`)
/--
trace: ⊢ equiv[ ={x, cnt} ==> §x{1} + 1 = §x{2} + 1 ∧ ={cnt} ] {
      var x : ℤ;
      cnt <- §cnt + 1;
} ~
    {
      cnt <- §cnt + 1;
}
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : equiv[ Inc2Rec.f (x) ~ Inc2.f (x) : ={x, cnt} ==> ={res, cnt} ] := by
  unfold Inc2Rec
  equiv_proc
  trace_state
  sorry


end GaudisCrypt.ECProcViewsTest
