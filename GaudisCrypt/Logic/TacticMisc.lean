import GaudisCrypt.Logic.StmtEquiv

/-!
# Meta helpers for statement rewriting

Generic pieces of the statement-rewriting tactics: exposing a statement's head (`openStmt`),
re-associating sequences (`flattenSeq`), and running a statement rewriter on the statement of a
Hoare triple (`hoareOnStmt`).  A rewriter returns its result together with a proof of
`StmtWithHoles.Equiv` (`Logic/StmtEquiv.lean`).  Users: `Inline.lean` and `HoareSplit.lean`.
-/

namespace GaudisCrypt.TacticMisc

open Lean Meta

/-! ## Exposing statements -/

/-- The statement heads a traversal stops at.  `call` is one: `whnf` would step through it to the
`call'` it is defined as, which spreads the callee over several arguments and no longer prints as
a call.  `applyLens` and `weaken` are the inliner's (`Inline.lean`, which imports this file), and
so are named unchecked. -/
def stmtHeads : Array Name :=
  #[``StmtWithHoles.skip, ``StmtWithHoles.sample, ``StmtWithHoles.call', ``StmtWithHoles.call,
    ``Stmt.call, ``StmtWithHoles.hole, ``StmtWithHoles.seq, ``StmtWithHoles.ifThenElse,
    ``StmtWithHoles.while, ``StmtWithHoles.assign,
    `GaudisCrypt.StmtWithHoles.applyLens, `GaudisCrypt.StmtWithHoles.weaken]

/-- Head reduction that keeps `let`s: beta, iota and projections only. -/
def whnfNoZeta (e : Lean.Expr) : MetaM Lean.Expr :=
  withConfig (fun c => { c with zeta := false, zetaDelta := false }) (whnfCore e)

/-- Expose a statement position: reduce until a statement head (or a `let`) is visible, without
zeta-reducing and without stepping through `assign` or `call`. -/
partial def openStmt (e : Lean.Expr) : MetaM Lean.Expr := do
  let e' ← whnfNoZeta e
  if e'.isLet then return e'
  if let some n := e'.getAppFn.constName? then
    if stmtHeads.contains n then return e'
  match ← unfoldDefinition? e' with
  | some e'' => openStmt e''
  | none => return e'

/-- Is this `skip`? -/
def isSkip (e : Lean.Expr) : Bool := e.isAppOf ``StmtWithHoles.skip

/-- Is this `_ <- e`, an assignment with no effect? -/
def isThrowawayAssign (e : Lean.Expr) : Bool :=
  e.isAppOfArity ``StmtWithHoles.assign 4 && (e.getArg! 2).isAppOf ``Setter.throwaway

/-- `a.Equiv a`. -/
def mkEquivRefl (s : Lean.Expr) : MetaM Lean.Expr := mkAppM ``StmtWithHoles.Equiv.refl #[s]

/-! ## `flattenSeq` -/

/-- Concatenate two already right-nested sequences, dropping `skip`s and `_ <- e`s: returns the
result together with a proof of `(a.seq b).Equiv result`. -/
partial def concatSeq (a b : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  if isSkip a then return (b, ← mkAppM ``StmtWithHoles.Equiv.skip_seq #[b])
  if isSkip b then return (a, ← mkAppM ``StmtWithHoles.Equiv.seq_skip #[a])
  if isThrowawayAssign a then
    return (b, ← mkAppM ``StmtWithHoles.Equiv.throwaway_seq #[a.getArg! 3, b])
  if isThrowawayAssign b then
    return (a, ← mkAppM ``StmtWithHoles.Equiv.seq_throwaway #[a, b.getArg! 3])
  if a.isAppOfArity ``StmtWithHoles.seq 3 then
    let x := a.getAppArgs[1]!
    let y := a.getAppArgs[2]!
    let (r, p) ← concatSeq y b
    let p₁ ← mkAppM ``StmtWithHoles.Equiv.seq_assoc #[x, y, b]
    let p₂ ← mkAppM ``StmtWithHoles.EquivInLens.seq #[← mkEquivRefl x, p]
    let (r', p₃) ← if isSkip r then pure (x, ← mkAppM ``StmtWithHoles.Equiv.seq_skip #[x])
      else do let s ← mkAppM ``StmtWithHoles.seq #[x, r]; pure (s, ← mkEquivRefl s)
    return (r', ← mkAppM ``StmtWithHoles.Equiv.trans
      #[← mkAppM ``StmtWithHoles.Equiv.trans #[p₁, p₂], p₃])
  let s ← mkAppM ``StmtWithHoles.seq #[a, b]
  return (s, ← mkEquivRefl s)

/-- Re-associate `seq` to the right and drop `skip`s and `_ <- e`s, returning the result and a
proof of `‹input›.Equiv result`.  Never fails; `if`s are not otherwise touched. -/
partial def flattenSeq (s₀ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let s ← openStmt s₀
  match s with
  | .letE n ty val body _ =>
      withLetDecl n ty val fun fv => do
        let (r, p) ← flattenSeq (body.instantiate1 fv)
        return (← mkLetFVars #[fv] r (usedLetOnly := false),
                ← mkLetFVars #[fv] p (usedLetOnly := false))
  | _ =>
    let args := s.getAppArgs
    match s.getAppFn.constName? with
    | some ``StmtWithHoles.seq =>
        let (a, pa) ← flattenSeq args[1]!
        let (b, pb) ← flattenSeq args[2]!
        let (r, p) ← concatSeq a b
        let pseq ← mkAppM ``StmtWithHoles.EquivInLens.seq #[pa, pb]
        return (r, ← mkAppM ``StmtWithHoles.Equiv.trans #[pseq, p])
    | some ``StmtWithHoles.ifThenElse =>
        let (t, pt) ← flattenSeq args[2]!
        let (e, pe) ← flattenSeq args[3]!
        return (← mkAppM ``StmtWithHoles.ifThenElse #[args[1]!, t, e],
                ← mkAppM ``StmtWithHoles.Equiv.ifThenElse #[args[1]!, pt, pe])
    | some ``StmtWithHoles.while =>
        let (b, pb) ← flattenSeq args[2]!
        return (← mkAppM ``StmtWithHoles.while #[args[1]!, b],
                ← mkAppM ``StmtWithHoles.Equiv.while #[args[1]!, pb])
    | _ => return (s, ← mkEquivRefl s)

/-! ## Rewriting the statement of a triple -/

/-- On a goal `hoareStmt A s B`: rewrite the statement with `f`, which returns the new statement
`s'` and a proof of `s.Equiv s'` (as `flattenSeq` and `HoareSplit.splitSeq` do), and continue with
the triple about `s'`.  The conditions are untouched — `conv` for the statement of a triple. -/
def hoareOnStmt (f : Lean.Expr → MetaM (Lean.Expr × Lean.Expr)) (g : MVarId) : MetaM MVarId :=
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOfArity ``hoareStmt 3 do
      throwError "expected a goal `hoareStmt A s B`, got{indentExpr ty}"
    let (A, s, B) := (ty.getArg! 0, ty.getArg! 1, ty.getArg! 2)
    let (s', p) ← f s
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``hoareStmt #[A, s', B]) (← g.getTag)
    g.assign
      (← mkAppOptM ``hoareStmt_of_equiv #[some A, some B, some s, some s', some p, some g'])
    return g'.mvarId!

end GaudisCrypt.TacticMisc
