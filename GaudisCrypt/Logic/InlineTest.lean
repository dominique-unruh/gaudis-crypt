import GaudisCrypt.Logic.Inline
import GaudisCrypt.Syntax.ModuleSyntax

/-! # Tests for `Inline.lean`

One command per pass (§10), so a failure localizes.  `#flattenCall` prints the **uncleaned**
output of §6.1 — full of `applyLens` and `chain*`, which is exactly what makes it a stable
expected-output test: its shape is determined by the input's shape, with no simp set in the loop.
-/

namespace GaudisCrypt.InlineTest

open GaudisCrypt Lean Elab Command Term Meta

/-- A concrete state, so the test procedures are closed terms. -/
instance : ProgramSpec := ⟨Unit⟩

/-- Flatten call `n` of a statement and report the result and the type of its proof. -/
elab "#flattenCall " n:num " in " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let step ← Flatten.flattenCall n.getNat e
    Meta.check step.stmt
    Meta.check step.proof
    let ty ← Meta.inferType step.proof
    logInfo m!"new locals: {step.newLocals}\n\nstatement:{indentExpr step.stmt}\n\n\
      proves:{indentExpr ty}"

/-- Flatten call `n` of a statement, cleaned (§6.4). -/
elab "#flattenCallCleaned " n:num " in " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let step ← Flatten.flattenCallCleaned n.getNat e
    Meta.check step.stmt
    Meta.check step.proof
    logInfo m!"new locals: {step.newLocals}\n\nstatement:{indentExpr step.stmt}\n\n\
      proves:{indentExpr (← Meta.inferType step.proof)}"

/-- Run the whole pass (§6.5). -/
elab "#flatten " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let res ← Flatten.flattenProcedureCalls e
    Meta.check res.stmt
    Meta.check res.proof
    logInfo m!"flattened {res.count} call(s); new locals: {res.newLocals}\n\n\
      statement:{indentExpr res.stmt}\n\nproves:{indentExpr (← Meta.inferType res.proof)}"

/-- §6.3 alone, on a hand-written statement. -/
elab "#flattenSeq " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let (r, p) ← Flatten.flattenSeq e
    Meta.check r
    Meta.check p
    logInfo m!"result:{indentExpr r}\n\nproves:{indentExpr (← Meta.inferType p)}"

/-- §11: unfold a module term to the procedure it denotes. -/
elab "#unfoldProc " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let r ← Flatten.unfoldProcedure e
    Meta.check r.expr
    let proof ← match r.proof? with
      | some h => Meta.check h; pure m!"\n\nproves:{indentExpr (← Meta.inferType h)}"
      | none   => pure m!"\n\n(by definition)"
    logInfo m!"unfolds to:{indentExpr r.expr}{proof}"

/-- §11: unfold the callee of one call site. -/
elab "#inlineRaw " n:num " in " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let r ← Flatten.inlineProcedureRaw n.getNat e
    Meta.check r.expr
    let some h := r.proof? | throwError "expected a proof"
    Meta.check h
    logInfo m!"statement:{indentExpr r.expr}\n\nproves:{indentExpr (← Meta.inferType h)}"

/-- §11: unfold the callee of one call site, then flatten it. -/
elab "#inline " n:num " in " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let step ← Flatten.inlineProcedure n.getNat e
    Meta.check step.stmt
    Meta.check step.proof
    logInfo m!"new locals: {step.newLocals}\n\nstatement:{indentExpr step.stmt}\n\n\
      proves:{indentExpr (← Meta.inferType step.proof)}"

/-- §11 at procedure level: inline one call site of a procedure, printed in surface syntax. -/
elab "#inlineProc " n:num " in " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let (p, proof) ← Flatten.inlineInProcedure n.getNat e
    Meta.check p
    Meta.check proof
    logInfo m!"inlined call site {n.getNat}:{indentExpr p}\n\n\
      proves:{indentExpr (← Meta.inferType proof)}"

/-- §8: the whole pass on a procedure, printed in surface syntax. -/
elab "#flattenProc " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let (p, proof, count) ← Flatten.flattenProcedure e
    Meta.check p
    Meta.check proof
    logInfo m!"flattened {count} call(s):{indentExpr p}\n\n\
      proves:{indentExpr (← Meta.inferType proof)}"

/-! ## A first end-to-end case -/

/-- The callee is spelled out at the call site: §2 accepts only literal callees. -/
noncomputable def caller : proctype () -> Nat :=
  proc () : Nat {
    var x y : Nat;
    x <- 1;
    y <- call (proc (z : Nat) : Nat { var w : Nat; w <- 2 * §z; return §w * §w }) (§x + §x);
    return §y
  }

set_option pp.gaudisCrypt false in
#flattenCall 0 in caller.body

#flattenCallCleaned 0 in caller.body

#flatten caller.body

#flattenProc caller

/-! ## The case list of §10 -/

/-- Two calls in one body, and a name collision: both callees call their local `w`, and so does
the caller.  The caller's `w` keeps its name; the callees' are renamed. -/
noncomputable def twoCalls : proctype () -> Nat :=
  proc () : Nat {
    var w : Nat;
    w <- 1;
    w <- call (proc (z : Nat) : Nat { var w : Nat; w <- §z + 1; return §w }) (§w);
    w <- call (proc (z : Nat) : Nat { var w : Nat; w <- §z * 3; return §w }) (§w);
    return §w
  }

#flatten twoCalls.body

/-- A callee that itself calls: the fixed point of §6.5 needs two rounds. -/
noncomputable def nested : proctype () -> Nat :=
  proc () : Nat {
    var a : Nat;
    a <- 7;
    a <- call (proc (u : Nat) : Nat {
        var b : Nat;
        b <- call (proc (v : Nat) : Nat { return §v + 1 }) (§u);
        return §b * 2
      }) (§a);
    return §a
  }

#flatten nested.body

/-- A call inside `if` and one inside `while`: the guards travel along the lens, and the callee's
locals are re-initialised on every iteration. -/
noncomputable def branching : proctype (Bool) -> Nat :=
  proc (c : Bool) : Nat {
    var n i : Nat;
    if (§c) {
      n <- call (proc (z : Nat) : Nat { var t : Nat; t <- §z + 1; return §t }) (§i);
    } else {
      n <- 0;
    }
    while (§i < 3) {
      i <- §i + 1;
      n <- call (proc (z : Nat) : Nat { var t : Nat; t <- §z + §z; return §t }) (§n);
    }
    return §n
  }

#flatten branching.body

#flattenProc nested
#flattenProc branching

/-- Several parameters (tuple splitting), and a callee with no locals at all. -/
noncomputable def twoParams : proctype () -> Nat :=
  proc () : Nat {
    var x y : Nat;
    x <- 2; y <- 5;
    x <- call (proc (a b : Nat) : Nat { return §a * §b }) (§x, §y);
    return §x
  }

#flatten twoParams.body

/-- A callee with neither parameters nor locals, called from a statement with no locals of its
own — every base case of §4 at once. -/
noncomputable def degenerate : proctype (Nat) -> Nat :=
  proc (p : Nat) : Nat {
    var r : Nat;
    r <- call (proc () : Nat { return 42 }) ();
    return §r + §p
  }

#flatten degenerate.body

/-! ## §6.3 on its own

Nested blocks and `skip`s, with no call anywhere: the spine is re-associated to the right and the
`skip`s disappear, and the proof is a chain of `seq_assoc`/`skip_seq`/`seq_skip`. -/

noncomputable def blocky : proctype () -> Nat :=
  proc () : Nat {
    var x : Nat;
    x <- 1;
    {
      skip;
      x <- 2;
      {
        x <- 3;
        skip;
      }
    }
    x <- 4;
    return §x
  }

#flattenSeq blocky.body

/-! ## What is left alone

A callee that is not spelled out at the call site stays a call (§2), and a statement with no
flattenable call at all is an error. -/

/-- Called through a name, so §2 refuses it: the callee is not literal. -/
noncomputable def opaqueCallee : Procedure (procsig (Nat) -> Nat) :=
  proc (z : Nat) : Nat { var t : Nat; t <- §z + 1; return §t }

noncomputable def callsOpaque : proctype () -> Nat :=
  proc () : Nat {
    var x : Nat;
    x <- 1;
    x <- call opaqueCallee (§x);
    return §x
  }

/--
error: nothing to flatten: the call is not flattenable: its callee is not spelled out at the call site
  opaqueCallee.1
-/
#guard_msgs in
#flatten callsOpaque.body

/-- A statement with no call at all. -/
noncomputable def callFree : proctype () -> Nat :=
  proc () : Nat { var x : Nat; x <- 1; return §x }

/-- error: nothing to flatten: the statement contains no call -/
#guard_msgs in
#flatten callFree.body

/-! ## §11 — modules

A module type with one procedure, a module over it that calls a parameter, and a module that
calls nothing: the two shapes of §11, `T.f ‹module expression›` and `M.f`. -/

moduletype U {
  proc g (Nat) -> Nat;
}

moduletype T {
  proc f (Nat) -> Nat;
  proc h () -> Nat;
}

/- `f` calls the parameter `A` (so it has a hole), `h` does not (so it is its procedure). -/
module M using (A : U) : T {
  proc f (x : Nat) : Nat {
    var y : Nat;
    y <- call A.g (§x);
    return §y + 1;
  };
  proc h () : Nat {
    return 5;
  };
}

/- The same, with no module parameters at all: case (b). -/
module N : T {
  proc f (x : Nat) : Nat {
    var y : Nat;
    y <- §x * 2;
    return §y;
  };
  proc h () : Nat {
    return 7;
  };
}

/- Two parameters and two holes: the module is applied to a `Module.pair`, and the instantiation
that fills the holes is a tuple, looked up by index. -/
module Q using (A B : U) : T {
  proc f (x : Nat) : Nat {
    var y : Nat;
    y <- call A.g (§x);
    y <- call B.g (§y);
    return §y;
  };
  proc h () : Nat {
    return 1;
  };
}

axiom someU : U
axiom otherU : U

/- (a): the accessor of a module applied to a parameter.  Only `M` is evaluated — the callee
`U.g someU` the body calls is left exactly as the module wrote it. -/
#unfoldProc (T.f (Module.app M someU))

/- the same at procedure level: the shape a call site carries -/
#unfoldProc (Module.Proc.procedure (T.f (Module.app M someU)))

/- a procedure of the same module that uses no parameter: `M.h` is `Module.proc M.h.procedure`
by definition, so the unfolding is a substitution -/
#unfoldProc (T.h (Module.app M someU))

/- two parameters, two holes: the argument tuple is taken apart, and so is the instantiation -/
#unfoldProc (T.f (Module.app Q (Module.pair someU otherU)))

/- (b): a module with an empty using-clause, read through the module type … -/
#unfoldProc (T.f N)

/- … and directly -/
#unfoldProc N.f

/- an abstract module has no body to find -/
axiom absM : Module.Arr U T

/--
error: no concrete procedure body: nothing to unfold at the head of
  (Module.app absM someU).f
-/
#guard_msgs in
#unfoldProc (T.f (Module.app absM someU))

/-- A caller whose callee is named through modules: §6 cannot flatten it (the callee is not
spelled out at the call site), §11 can unfold it first. -/
noncomputable def modCaller : proctype () -> Nat :=
  proc () : Nat {
    var n : Nat;
    n <- 3;
    n <- call (Module.Proc.procedure (T.f (Module.app M someU))) (§n);
    return §n
  }

#inlineRaw 0 in modCaller.body

#inline 0 in modCaller.body

/- and the same at procedure level (§8): the callee's body lands in the caller's, its local `y`
becomes a local of the caller, and the `return` travels along -/
#inlineProc 0 in modCaller

/- a callee that is an ordinary definition rather than a module expression: §11 unfolds the
constant, which is what makes `opaqueCallee` — the callee §6 refuses — inlinable -/
#inlineProc 0 in callsOpaque

/-! ### Call sites are numbered including holes

`P.f` calls its module parameter first and a concrete module second, so its body has two call
sites: number 0 is the hole, number 1 the call — and neither pass will renumber them. -/

module P using (A : U) : T {
  proc f (x : Nat) : Nat {
    var y z : Nat;
    y <- call A.g (§x);
    z <- call N.f (§y);
    return §z;
  };
  proc h () : Nat {
    return 0;
  };
}

/-- error: this call site is a hole: it has no callee to unfold -/
#guard_msgs in
#inlineRaw 0 in P.f.procedure.body

/- `M.f`'s body has one call site, and it is a hole: neither pass has anything to work with. -/
/-- error: nothing to flatten: this call site is a hole: it has no callee to flatten -/
#guard_msgs in
#flatten M.f.procedure.body

#inline 1 in P.f.procedure.body

/- A callee named through a module is not spelled out at the call site, so §6 on its own has
nothing to flatten: §11 has to run first. -/
/--
error: nothing to flatten: the call is not flattenable: its callee is not spelled out at the call site
  N.f.procedure.1
-/
#guard_msgs in
#flattenProc (proc () : Nat {
    var n : Nat;
    n <- call (Module.Proc.procedure (T.f N)) (§n);
    return §n
  })

end GaudisCrypt.InlineTest
