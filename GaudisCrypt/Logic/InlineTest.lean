import GaudisCrypt.Logic.Inline
import GaudisCrypt.Syntax.ModuleSyntax
import GaudisCrypt.Syntax.ProgramSyntaxTest

/-! # Tests for `Inline.lean`

One command per pass, so a failure localizes.  Every command checks the proof it gets
(`Meta.check`, and that it proves the expected statement about the input), and every command
that prints surface syntax also re-parses what it printed (`ProgTest.roundtrip`).  `#flattenCall`
prints the **uncleaned** output of `Flatten.flattenCall` — full of `applyLens` and `chain*`; its
shape is determined by the input's shape, with no simp set in the loop.
-/

namespace GaudisCrypt.InlineTest

open GaudisCrypt Lean Elab Command Term Meta

/-- A concrete state, so the test procedures are closed terms. -/
instance : ProgramSpec := ⟨PUnit⟩

/-- Elaborate a test's input term. -/
def elabInput (t : Term) : TermElabM Lean.Expr := do
  let e ← elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- Check that `step.proof` proves `input.EquivInLens step.stmt step.trafo`. -/
def checkStep (input : Lean.Expr) (step : Flatten.FlattenStep) : MetaM Unit := do
  Meta.check step.stmt
  Meta.check step.proof
  let expected ← Flatten.mkEquivInLens step.inst step.hCtx input step.stmt step.trafo
  unless ← isDefEq (← inferType step.proof) expected do
    throwError "the proof proves{indentExpr (← inferType step.proof)}\nnot{indentExpr expected}"

/-- Check that `proof` proves `procedureDenotation p' = procedureDenotation p`. -/
def checkProc (p p' proof : Lean.Expr) : MetaM Unit := do
  Meta.check p'
  Meta.check proof
  let expected ← mkEq (← mkAppM ``procedureDenotation #[p'])
    (← mkAppM ``procedureDenotation #[p])
  unless ← isDefEq (← inferType proof) expected do
    throwError "the proof proves{indentExpr (← inferType proof)}\nnot{indentExpr expected}"

/-- Flatten call `n` of a statement, uncleaned. -/
elab "#flattenCall " n:num " in " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabInput t
    let step ← Flatten.flattenCall n.getNat e
    checkStep e step
    logInfo m!"{step.stmt}"

/-- Flatten call `n` of a statement, cleaned. -/
elab "#flattenCallCleaned " n:num " in " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabInput t
    let step ← Flatten.flattenCallCleaned n.getNat e
    checkStep e step
    logInfo m!"renaming: {step.trafo}\n{← ProgTest.roundtrip step.stmt}"

/-- The whole pass on a statement. -/
elab "#flatten " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabInput t
    let res ← Flatten.flattenProcedureCalls e
    checkStep e res.toFlattenStep
    logInfo m!"flattened {res.count} call(s), renaming: {res.trafo}\n\
      {← ProgTest.roundtrip res.stmt}"

/-- The whole pass on a procedure. -/
elab "#flattenProc " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabInput t
    let (p, proof, count) ← Flatten.flattenProcedure e
    checkProc e p proof
    logInfo m!"flattened {count} call(s):\n{← ProgTest.roundtrip p}"

/-- `flattenSeq` alone. -/
elab "#flattenSeq " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabInput t
    let (r, p) ← Flatten.flattenSeq e
    Meta.check r
    Meta.check p
    unless ← isDefEq (← inferType p) (← mkAppM ``StmtWithHoles.Equiv #[e, r]) do
      throwError "the proof proves{indentExpr (← inferType p)}"
    logInfo (← ProgTest.roundtrip r)

/-- Unfold a module term to the procedure it denotes. -/
elab "#unfoldProc " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabInput t
    let r ← Flatten.unfoldProcedure e
    Meta.check r.expr
    if let some h := r.proof? then
      Meta.check h
      unless ← isDefEq (← inferType h) (← mkEq e r.expr) do
        throwError "the proof proves{indentExpr (← inferType h)}"
    logInfo (← ProgTest.roundtrip r.expr)

/-- Unfold the callee of one call site. -/
elab "#inlineRaw " n:num " in " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabInput t
    let r ← Flatten.inlineProcedureRaw n.getNat e
    Meta.check r.expr
    let some h := r.proof? | throwError "expected a proof"
    Meta.check h
    unless ← isDefEq (← inferType h) (← mkEq e r.expr) do
      throwError "the proof proves{indentExpr (← inferType h)}"
    logInfo (← ProgTest.roundtrip r.expr)

/-- Unfold the callee of one call site, then flatten it. -/
elab "#inline " n:num " in " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabInput t
    let step ← Flatten.inlineProcedure n.getNat e
    checkStep e step
    logInfo m!"renaming: {step.trafo}\n{← ProgTest.roundtrip step.stmt}"

/-- Inline one call site of a procedure. -/
elab "#inlineProc " n:num " in " t:term : command =>
  runTermElabM fun _ => do
    let e ← elabInput t
    let (p, proof) ← Flatten.inlineInProcedure n.getNat e
    checkProc e p proof
    logInfo (← ProgTest.roundtrip p)

/-! ## A first end-to-end case -/

/-- The callee is spelled out at the call site: only literal callees are flattened. -/
noncomputable def caller : proctype () -> Nat :=
  proc () : Nat {
    var x y : Nat;
    x <- 1;
    y <- call (proc (z : Nat) : Nat { var w : Nat; w <- 2 * §z; return §w * §w }) (§x + §x);
    return §y
  }

set_option pp.gaudisCrypt false in
#flattenCall 0 in caller.body

/- one round alone: the callee's variables have the made-up names `«@.z»`, `«@.w»` -/
/--
info: renaming: Flatten.trafo
GaudiProg[
    var x : ℕ, «@.z» : ℕ, «@.w» : ℕ, y : ℕ;
    x <- 1;
    Flatten.calleeFrame.resetSetter <- ();
    «@.z» <- §x + §x;
    «@.w» <- 2 * §«@.z»;
    y <- §«@.w» * §«@.w»;
]
-/
#guard_msgs in
#flattenCallCleaned 0 in caller.body

/- the whole pass ends with the cleanup renaming -/
/--
info: flattened 1 call(s), renaming: (Flatten.rename [("@.z", "z"), ("@.w", "w")]).chain Flatten.trafo
GaudiProg[
    var x : ℕ, z : ℕ, w : ℕ, y : ℕ;
    x <- 1;
    ((Flatten.rename [("@.z", "z"), ("@.w", "w")]).chain Flatten.calleeFrame).resetSetter <- ();
    z <- §x + §x;
    w <- 2 * §z;
    y <- §w * §w;
]
-/
#guard_msgs in
#flatten caller.body

/--
info: flattened 1 call(s):
proc () : ℕ {
    var x : ℕ, z : ℕ, w : ℕ, y : ℕ;
    x <- 1;
    ((Flatten.rename [("@.z", "z"), ("@.w", "w")]).chain Flatten.calleeFrame).resetSetter <- ();
    z <- §x + §x;
    w <- 2 * §z;
    y <- §w * §w;
    return §y
}
-/
#guard_msgs in
#flattenProc caller

/-! ## More cases -/

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

/--
info: flattened 2 call(s), renaming: (Flatten.rename [("@@.z", "z"), ("@@.w", "w0"), ("@.z", "z0"), ("@.w", "w1")]).chain
  (Flatten.trafo.chain Flatten.trafo)
GaudiProg[
    var w : ℕ, z : ℕ, w0 : ℕ, z0 : ℕ, w1 : ℕ;
    w <- 1;
    ((Flatten.rename [("@@.z", "z"), ("@@.w", "w0"), ("@.z", "z0"), ("@.w", "w1")]).chain
        (Flatten.trafo.chain Flatten.calleeFrame)).resetSetter <-
    ();
    z <- §w;
    w0 <- §z + 1;
    w <- §w0;
    ((Flatten.rename [("@@.z", "z"), ("@@.w", "w0"), ("@.z", "z0"), ("@.w", "w1")]).chain
        Flatten.calleeFrame).resetSetter <-
    ();
    z0 <- §w;
    w1 <- §z0 * 3;
    w <- §w1;
]
-/
#guard_msgs in
#flatten twoCalls.body

/-- A callee that itself calls: the fixed point needs two rounds. -/
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

/--
info: flattened 2 call(s), renaming: (Flatten.rename [("@@.u", "u"), ("@.v", "v"), ("@@.b", "b")]).chain
  (Flatten.trafo.chain Flatten.trafo)
GaudiProg[
    var a : ℕ, u : ℕ, v : ℕ, b : ℕ;
    a <- 7;
    ((Flatten.rename [("@@.u", "u"), ("@.v", "v"), ("@@.b", "b")]).chain
        (Flatten.trafo.chain Flatten.calleeFrame)).resetSetter <-
    ();
    u <- §a;
    ((Flatten.rename [("@@.u", "u"), ("@.v", "v"), ("@@.b", "b")]).chain Flatten.calleeFrame).resetSetter <- ();
    v <- §u;
    b <- §v + 1;
    a <- §b * 2;
]
-/
#guard_msgs in
#flatten nested.body

/-- A call inside `if` and one inside `while`: the guards travel along the lens, and the callee's
frame is reset on every iteration. -/
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

/--
info: flattened 2 call(s), renaming: (Flatten.rename [("@@.z", "z"), ("@@.t", "t"), ("@.z", "z0"), ("@.t", "t0")]).chain
  (Flatten.trafo.chain Flatten.trafo)
GaudiProg[
    var c : Bool, z : ℕ, i : ℕ, t : ℕ, n : ℕ, z0 : ℕ, t0 : ℕ;
    if (§c) {
      ((Flatten.rename [("@@.z", "z"), ("@@.t", "t"), ("@.z", "z0"), ("@.t", "t0")]).chain
          (Flatten.trafo.chain Flatten.calleeFrame)).resetSetter <-
      ();
      z <- §i;
      t <- §z + 1;
      n <- §t;
    } else {
      n <- 0;
    }
    while (decide (§i < 3)) {
      i <- §i + 1;
      ((Flatten.rename [("@@.z", "z"), ("@@.t", "t"), ("@.z", "z0"), ("@.t", "t0")]).chain
          Flatten.calleeFrame).resetSetter <-
      ();
      z0 <- §n;
      t0 <- §z0 + §z0;
      n <- §t0;
    }
]
-/
#guard_msgs in
#flatten branching.body

/--
info: flattened 2 call(s):
proc () : ℕ {
    var a : ℕ, u : ℕ, v : ℕ, b : ℕ;
    a <- 7;
    ((Flatten.rename [("@@.u", "u"), ("@.v", "v"), ("@@.b", "b")]).chain
        (Flatten.trafo.chain Flatten.calleeFrame)).resetSetter <-
    ();
    u <- §a;
    ((Flatten.rename [("@@.u", "u"), ("@.v", "v"), ("@@.b", "b")]).chain Flatten.calleeFrame).resetSetter <- ();
    v <- §u;
    b <- §v + 1;
    a <- §b * 2;
    return §a
}
-/
#guard_msgs in
#flattenProc nested

/--
info: flattened 2 call(s):
proc (c : Bool) : ℕ {
    var z : ℕ, i : ℕ, t : ℕ, n : ℕ, z0 : ℕ, t0 : ℕ;
    if (§c) {
      ((Flatten.rename [("@@.z", "z"), ("@@.t", "t"), ("@.z", "z0"), ("@.t", "t0")]).chain
          (Flatten.trafo.chain Flatten.calleeFrame)).resetSetter <-
      ();
      z <- §i;
      t <- §z + 1;
      n <- §t;
    } else {
      n <- 0;
    }
    while (decide (§i < 3)) {
      i <- §i + 1;
      ((Flatten.rename [("@@.z", "z"), ("@@.t", "t"), ("@.z", "z0"), ("@.t", "t0")]).chain
          Flatten.calleeFrame).resetSetter <-
      ();
      z0 <- §n;
      t0 <- §z0 + §z0;
      n <- §t0;
    }
    return §n
}
-/
#guard_msgs in
#flattenProc branching

/-- Several parameters (a tuple assignment), and a callee with no variables but its parameters. -/
noncomputable def twoParams : proctype () -> Nat :=
  proc () : Nat {
    var x y : Nat;
    x <- 2; y <- 5;
    x <- call (proc (a b : Nat) : Nat { return §a * §b }) (§x, §y);
    return §x
  }

/--
info: flattened 1 call(s), renaming: (Flatten.rename [("@.a", "a"), ("@.b", "b")]).chain Flatten.trafo
GaudiProg[
    var x : ℕ, y : ℕ, a : ℕ, b : ℕ;
    x <- 2;
    y <- 5;
    ((Flatten.rename [("@.a", "a"), ("@.b", "b")]).chain Flatten.calleeFrame).resetSetter <- ();
    a, b <- (§x, §y);
    x <- §a * §b;
]
-/
#guard_msgs in
#flatten twoParams.body

/-- A callee with no parameters and no variables. -/
noncomputable def degenerate : proctype (Nat) -> Nat :=
  proc (p : Nat) : Nat {
    var r : Nat;
    r <- call (proc () : Nat { return 42 }) ();
    return §r + §p
  }

/--
info: flattened 1 call(s), renaming: Flatten.trafo
GaudiProg[
    var r : ℕ;
    Flatten.calleeFrame.resetSetter <- ();
    r <- 42;
]
-/
#guard_msgs in
#flatten degenerate.body

/-- A callee whose variable has the name of a parameter of the caller that the body never
mentions: the parameter keeps its name (the entry state has to stay the same), the callee's
variable is renamed. -/
noncomputable def unusedParam : proctype (Nat) -> Nat :=
  proc (q : Nat) : Nat {
    var r : Nat;
    r <- call (proc (q : Nat) : Nat { return §q + 1 }) (Nat.succ 0);
    return §r
  }

/--
info: flattened 1 call(s):
proc (q : ℕ) : ℕ {
    var q0 : ℕ, r : ℕ;
    ((Flatten.rename [("@.q", "q0")]).chain Flatten.calleeFrame).resetSetter <- ();
    q0 <- Nat.succ 0;
    r <- §q0 + 1;
    return §r
}
-/
#guard_msgs in
#flattenProc unusedParam

/-! ## `flattenSeq` on its own

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

/--
info: GaudiProg[
    var x : ℕ;
    x <- 1;
    x <- 2;
    x <- 3;
    x <- 4;
]
-/
#guard_msgs in
#flattenSeq blocky.body

/-! ## What is left alone

A callee that is not spelled out at the call site stays a call, and a statement with no
flattenable call at all is an error. -/

/-- Called through a name, so it is not flattened: the callee is not literal. -/
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
  opaqueCallee.parameterNames
-/
#guard_msgs in
#flatten callsOpaque.body

/-- A statement with no call at all. -/
noncomputable def callFree : proctype () -> Nat :=
  proc () : Nat { var x : Nat; x <- 1; return §x }

/-- error: nothing to flatten: the statement contains no call -/
#guard_msgs in
#flatten callFree.body

/-! ## Inlining: callees named through modules

A module type with one procedure, a module over it that calls a parameter, and a module that
calls nothing: the two shapes inlining evaluates, `T.f ‹module expression›` and `M.f`. -/

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
/--
info: Module.proc
  (proc (x : ℕ) : ℕ {
      var y : ℕ;
      y <- call someU.g.procedure (§x);
      return §y + 1
})
-/
#guard_msgs in
#unfoldProc (T.f (Module.app M someU))

/- the same at procedure level: the shape a call site carries -/
/--
info: proc (x : ℕ) : ℕ {
    var y : ℕ;
    y <- call someU.g.procedure (§x);
    return §y + 1
}
-/
#guard_msgs in
#unfoldProc (Module.Proc.procedure (T.f (Module.app M someU)))

/- a procedure of the same module that uses no parameter: `M.h` is `Module.proc M.h.procedure`
by definition, so the unfolding is a substitution -/
/--
info: Module.proc
  (proc () : ℕ {
      skip;
      return 5
})
-/
#guard_msgs in
#unfoldProc (T.h (Module.app M someU))

/- two parameters, two holes: the argument tuple is taken apart, and so is the instantiation -/
/--
info: Module.proc
  (proc (x : ℕ) : ℕ {
      var y : ℕ;
      y <- call someU.g.procedure (§x);
      y <- call otherU.g.procedure (§y);
      return §y
})
-/
#guard_msgs in
#unfoldProc (T.f (Module.app Q (Module.pair someU otherU)))

/- (b): a module with an empty using-clause, read through the module type … -/
/--
info: Module.proc
  (proc (x : ℕ) : ℕ {
      var y : ℕ;
      y <- §x * 2;
      return §y
})
-/
#guard_msgs in
#unfoldProc (T.f N)

/- … and directly -/
/--
info: Module.proc
  (proc (x : ℕ) : ℕ {
      var y : ℕ;
      y <- §x * 2;
      return §y
})
-/
#guard_msgs in
#unfoldProc N.f

/- an abstract module has no body to find -/
axiom absM : Module.Arr U T

/--
error: no concrete procedure body: nothing to unfold at the head of
  (Module.app absM someU).f
-/
#guard_msgs in
#unfoldProc (T.f (Module.app absM someU))

/-- A caller whose callee is named through modules: flattening cannot handle it (the callee is not
spelled out at the call site), inlining can unfold it first. -/
noncomputable def modCaller : proctype () -> Nat :=
  proc () : Nat {
    var n : Nat;
    n <- 3;
    n <- call (Module.Proc.procedure (T.f (Module.app M someU))) (§n);
    return §n
  }

/--
info: GaudiProg[
    var n : ℕ;
    n <- 3;
    n <- call
    (proc (x : ℕ) : ℕ {
        var y : ℕ;
        y <- call someU.g.procedure (§x);
        return §y + 1
  }) (§n);
]
-/
#guard_msgs in
#inlineRaw 0 in modCaller.body

/--
info: renaming: (Flatten.rename [("@.x", "x"), ("@.y", "y")]).chain Flatten.trafo
GaudiProg[
    var n : ℕ, x : ℕ, y : ℕ;
    n <- 3;
    ((Flatten.rename [("@.x", "x"), ("@.y", "y")]).chain Flatten.calleeFrame).resetSetter <- ();
    x <- §n;
    y <- call someU.g.procedure (§x);
    n <- §y + 1;
]
-/
#guard_msgs in
#inline 0 in modCaller.body

/- and the same at procedure level: the callee's body lands in the caller's, its local `y`
becomes a local of the caller, and the `return` travels along -/
/--
info: proc () : ℕ {
    var n : ℕ, x : ℕ, y : ℕ;
    n <- 3;
    ((Flatten.rename [("@.x", "x"), ("@.y", "y")]).chain Flatten.calleeFrame).resetSetter <- ();
    x <- §n;
    y <- call someU.g.procedure (§x);
    n <- §y + 1;
    return §n
}
-/
#guard_msgs in
#inlineProc 0 in modCaller

/- a callee that is an ordinary definition rather than a module expression: inlining unfolds the
constant, which is what makes `opaqueCallee` — the callee flattening refuses — inlinable -/
/--
info: proc () : ℕ {
    var x : ℕ, z : ℕ, t : ℕ;
    x <- 1;
    ((Flatten.rename [("@.z", "z"), ("@.t", "t")]).chain Flatten.calleeFrame).resetSetter <- ();
    z <- §x;
    t <- §z + 1;
    x <- §t;
    return §x
}
-/
#guard_msgs in
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

/- the hole stays, and so does the `let` that names it -/
/--
info: renaming: (Flatten.rename [("@.x", "x0"), ("@.y", "y0")]).chain Flatten.trafo
let A_g := HoleIndex.zero;
GaudiProg[
    var y : ℕ, x : ℕ, x0 : ℕ, y0 : ℕ, z : ℕ;
    y <- holecall A_g (§x);
    ((Flatten.rename [("@.x", "x0"), ("@.y", "y0")]).chain Flatten.calleeFrame).resetSetter <- ();
    x0 <- §y;
    y0 <- §x0 * 2;
    z <- §y0;
]
-/
#guard_msgs in
#inline 1 in P.f.procedure.body

/- A callee named through a module is not spelled out at the call site, so flattening on its own
has nothing to flatten: inlining has to run first. -/
/--
error: nothing to flatten: the call is not flattenable: its callee is not spelled out at the call site
  N.f.procedure.parameterNames
-/
#guard_msgs in
#flattenProc (proc () : Nat {
    var n : Nat;
    n <- call (Module.Proc.procedure (T.f N)) (§n);
    return §n
  })

end GaudisCrypt.InlineTest
