import GaudisCrypt.Logic.HoareSplit

/-!
# Backwards wp steps, for every registered judgment

`Judgment.wpStep k` processes the last `k` statements of a judgment's statement one at a time,
from the end:

* deterministic code (`Judgment.detOf?`: assignments, resets, `skip`, sequences and conditionals
  of those) by the judgment's `detLemma` — the postcondition after the state update, the same
  shape in every judgment;
* a sampling by the judgment's `sampleLemma`, a call by its `callLemma`, a conditional with
  calls or samplings in its branches by its `ifLemma` — where judgments genuinely differ;

simplifying the postcondition after each step with the judgment's `postSimp`.  `hoare_wp`,
`phoare_wp` and the dispatching `stmt_wp` are this one step.
-/

namespace GaudisCrypt.Judgment

open Lean Meta Elab Tactic

/-- Apply the rule `lem` to the goal `g` (of type `ty`): its conclusion unified with the goal, the
argument of type `Stmt.Det …` (if any) set to `det?`, and the judgment about the remaining
statement — the last argument — returned as the new goal. -/
def applyRule (lem : Name) (g : MVarId) (ty : Lean.Expr) (det? : Option Lean.Expr) :
    MetaM MVarId := do
  let c ← mkConstWithFreshMVarLevels lem
  let (ms, _, concl) ← forallMetaTelescope (← inferType c)
  if let some pf := det? then
    let some hd ← ms.findM? fun m => return (← instantiateMVars (← inferType m)).isAppOf ``Stmt.Det
      | throwError "`{lem}` has no `Stmt.Det` argument"
    unless ← isDefEq hd pf do throwError "`{lem}`: the determinism proof does not fit"
  unless ← isDefEq concl ty do
    throwError "`{lem}` does not apply to{indentExpr ty}"
  let some hJ := ms.back? | throwError "`{lem}` has no arguments"
  let g' ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (← inferType hJ)) (← g.getTag)
  unless ← isDefEq hJ g' do throwError "`{lem}`: cannot set the new judgment"
  g.assign (← instantiateMVars (mkAppN c ms))
  return g'.mvarId!

/-- Simplify argument `i` of the goal with `simpWithNames decls procs`. -/
def simpArg (g : MVarId) (i : Nat) (decls procs : List Name) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let (f, args) := (ty.getAppFn, ty.getAppArgs)
  let some B := args[i]? | throwError "simpArg: no argument {i} in{indentExpr ty}"
  let r ← simpWithNames decls procs B
  let target := mkAppN f (args.set! i r.expr)
  let some h := r.proof? | return ← g.replaceTargetDefEq target
  let motive ← withLocalDeclD `x (← inferType B) fun x =>
    mkLambdaFVars #[x] (mkAppN f (args.set! i x))
  g.replaceTargetEq target (← mkCongrArg motive h)

/-- One backwards step over the last statement of the goal's judgment (of side `side?` of a
relational one).  With `detOnly`, only over deterministic code: anything else is an error. -/
def wpOne (g : MVarId) (side? : Option Nat := none) (detOnly := false) : MetaM MVarId :=
    g.withContext do
  let g ← HoareSplit.hoareSplit 1 g side?
  let (d, ty) ← descOf g side?
  let st := stripLets (ty.getArg! d.stmtArg)
  unless st.isAppOf ``StmtWithHoles.seq do
    throwError "wp: the statement is not a sequence:{indentExpr st}"
  let last := stripLets (st.getArg! 2)
  let g ← if let some (_, pf) ← detOf? last then
      let some lem := d.detLemma | throwError "wp: `{d.head}` has no rule for deterministic code"
      applyRule lem g ty (some pf)
    else if detOnly then
      throwError "wp: not deterministic code:{indentExpr last}"
    else if last.isAppOf ``StmtWithHoles.sample then
      let some lem := d.sampleLemma | throwError "wp: `{d.head}` has no rule for sampling"
      applyRule lem g ty none
    else if last.isAppOf ``StmtWithHoles.call || last.isAppOf ``StmtWithHoles.call' then
      let some lem := d.callLemma
        | throwError "wp: `{d.head}` has no rule for a call without a specification — use the \
            judgment's call tactic (`hoare_call h`, …)"
      applyRule lem g ty none
    else if last.isAppOf ``StmtWithHoles.ifThenElse then
      let some lem := d.ifLemma
        | throwError "wp: `{d.head}` has no rule for a conditional with calls or samplings in its \
            branches"
      applyRule lem g ty none
    else
      throwError "wp: no wp rule for the statement (a loop needs an invariant):{indentExpr last}"
  simpArg g d.postArg d.postSimp d.postSimprocs

/-- `k` backwards steps (`wpOne`), the last statement first; on a relational judgment, `k` on
side `side?`, or on each side for `none`. -/
def wpStep (k : Nat) (g : MVarId) (side? : Option Nat := none) : MetaM MVarId :=
  forSides side? g fun side? g => do
    let mut g := g
    for _ in [0:k] do g ← wpOne g side?
    return g

/-- Backwards steps over the deterministic code at the end of the statement, as many as there
are (EasyCrypt's `wp`): until the statement is `skip` or ends in a sampling, a call or a loop.
On a relational judgment, on side `side?`, or on each side for `none`. -/
def wpDet (g : MVarId) (side? : Option Nat := none) : MetaM MVarId :=
  forSides side? g fun side? g => do
    let mut g := g
    repeat
      let (d, ty) ← descOf g side?
      if (stripLets (ty.getArg! d.stmtArg)).isAppOf ``StmtWithHoles.skip then break
      let s ← saveState
      try g ← wpOne g side? (detOnly := true)
      catch _ => s.restore; break
    return g

/-- `stmt_wp k`: the last `k` statements of any registered judgment's statement, by wp
(`Judgment.wpStep`); `stmt_wp` alone: all the deterministic code at the end (`Judgment.wpDet`).
On a relational judgment, on both sides, or with `stmt_wp{i}` on side `i`. -/
elab "stmt_wp" s:(judgmentSide)? k?:(ppSpace num)? : tactic =>
  liftMetaTactic1 fun g => some <$> match k? with
    | some k => wpStep k.getNat g (sideOf? s)
    | none => wpDet g (sideOf? s)

/-- An EC code position (`n` or `-n`), as in `wp n m`/`sp n m`. -/
declare_syntax_cat ecPos
syntax num : ecPos
syntax "-" num : ecPos

/-- The integer an `ecPos` denotes. -/
def ecPosOf : TSyntax `ecPos → Int
  | `(ecPos| - $n:num) => -(n.getNat : Int)
  | `(ecPos| $n:num) => n.getNat
  | _ => 0

/-- **EC's code gap** (`s_codegap1_0before`): in a statement of `len` statements, `n ≥ 0` is the
gap after the first `n` (before the statement at 0-based index `n`), `-k` the gap after the
`k`-th statement from the end (`-1`: after the last).  The number of statements before it. -/
def ecGap (n : Int) (len : Nat) : MetaM Nat := do
  let gap : Int := if n ≥ 0 then n else len + n + 1
  unless 0 ≤ gap ∧ gap ≤ len do
    throwError "position {n} is outside a statement of {len} statements"
  return gap.toNat

/-- **EC's `wp n`**: the statements after EC's code gap `pos` (`TacticMisc.ecGapIn`: EC's
statements, the resets inlining leaves not counted) by wp (`wpStep`), the ones before kept; on
side `side?` of a relational judgment. -/
def wpAt (pos : Int) (g : MVarId) (side? : Option Nat := none) : MetaM MVarId :=
  forSides side? g fun side? g => do
    let (d, ty) ← descOf g side?
    let st := ty.getArg! d.stmtArg
    let len ← HoareSplit.seqLength (stripLets st)
    wpStep (len - (← TacticMisc.ecGapIn pos st)) g side?

/-- **EC's `wp n m`** on a relational judgment, with EC's code positions (`ecGap`): on the left
the statements after the first `n` by wp, on the right those after the first `m` (`-k`: up to
the `k`-th from the end).  (The one-number `stmt_wp k` counts from the end: the last `k`.) -/
elab "stmt_wp" ppSpace n:ecPos ppSpace m:ecPos : tactic =>
  liftMetaTactic1 fun g => do
    let g ← wpAt (ecPosOf n) g (some 1)
    some <$> wpAt (ecPosOf m) g (some 2)

end GaudisCrypt.Judgment
