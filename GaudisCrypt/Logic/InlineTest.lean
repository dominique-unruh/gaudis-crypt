import GaudisCrypt.Logic.Inline

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

end GaudisCrypt.InlineTest
