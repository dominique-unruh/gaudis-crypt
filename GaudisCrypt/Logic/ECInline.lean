import GaudisCrypt.Logic.Inline

/-!
# EasyCrypt's `inline M.f`: inlining by name

    stmt_inline (BlockSponge.Sponge(Perm).f)       -- EC's `inline BlockSponge.Sponge(Perm).f`
    stmt_inline{2} (M.f)                           -- EC's `inline{2} M.f`

Every call of the procedure `M.f` (a procedure module, or a procedure) in the statement, on every
side (or on side `i`), is inlined, in the order of the call sites (`stmt_inline n` inlines call
site `n`).  A callee is the procedure when the two agree at reducible transparency: the path is
the callee as the module command reads it back.
-/

namespace GaudisCrypt

namespace Flatten

open Lean Meta Elab Tactic

/-- The callees of the call sites of a statement, in the pre-order `stmt_inline n` numbers them
(`none` for a hole or a call already spelled out). -/
partial def callees (e₀ : Expr) : MetaM (Array (Option Expr)) := do
  -- `openStmt`, not `unfoldStmt`: `whnf` would turn a `call` into the `call'` it is defined as
  let e ← TacticMisc.openStmt e₀
  if isCallSite e then
    match e.getAppFn.constName? with
    | some ``StmtWithHoles.call | some ``Stmt.call =>
      return #[some e.getAppArgs[e.getAppNumArgs - 2]!]
    | _ => return #[none]
  match e with
  | .letE _ _ _ body _ => callees body
  | _ =>
    let args := e.getAppArgs
    match e.getAppFn.constName? with
    | some ``StmtWithHoles.seq => return (← callees args[1]!) ++ (← callees args[2]!)
    | some ``StmtWithHoles.ifThenElse => return (← callees args[2]!) ++ (← callees args[3]!)
    | some ``StmtWithHoles.while => callees args[2]!
    | _ => return #[]

/-- Inline the calls of `p` on side `side?` of the goal, as long as one is left (at most `fuel`). -/
partial def inlineByName (p : Expr) (g : MVarId) (side? : Option Nat) (fuel : Nat := 32) :
    MetaM MVarId := g.withContext do
  if fuel == 0 then return g
  let (d, ty) ← Judgment.descOf g side?
  let cs ← callees (ty.getAppArgs[d.stmtArg]!)
  let mut k? : Option Nat := none
  for c? in cs, i in [0:cs.size] do
    if let some c := c? then
      if ← withNewMCtxDepth (withReducible (isDefEq c p)) then
        k? := some i
        break
  let some k := k? | return g
  inlineByName p (← judgmentInline k g side?) side? (fuel - 1)

/-- `stmt_inline M`, `stmt_inline{i} M`: see the module docstring. -/
elab "stmt_inline" s:(Judgment.judgmentSide)? ppSpace "(" M:term ")" : tactic => withMainContext do
  let Me ← Term.elabTerm M none
  Term.synthesizeSyntheticMVarsNoPostponing
  let Me ← instantiateMVars Me
  -- a procedure module stands for its procedure
  let p ← try mkAppM ``Module.Proc.procedure #[Me] catch _ => pure Me
  let g ← getMainGoal
  let side? := Judgment.sideOf? s
  let (ds, _) ← Judgment.descsOf g side?
  let mut g := g
  let before := g
  if ds.size == 1 then
    g ← inlineByName p g side?
  else
    for d in ds do g ← inlineByName p g (some d.side)
  if g == before then throwError "stmt_inline: no call of{indentExpr p}"
  replaceMainGoal [g]

end Flatten

end GaudisCrypt
