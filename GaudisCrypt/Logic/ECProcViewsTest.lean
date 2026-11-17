import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECInline
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.FootprintUpper
import GaudisCrypt.Syntax.Syntax

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

end GaudisCrypt.ECProcViewsTest
