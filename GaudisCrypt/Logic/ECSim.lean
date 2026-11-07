import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.Inline

/-!
# EasyCrypt's `inline*` and `sim`

    stmt_inline*     -- EC's `inline*`: every call whose callee is spelled out, on both sides
    stmt_inline*{i}  -- … on side `i`
    phoare_inline*, hoare_inline*
    sim              -- EC's `sim`, on a relational judgment about two statements

`inline*` inlines call sites until only calls of abstract procedures are left (EC's `inline*`,
which does not inline a declared module either).

`sim` goes backwards over the two statements, computing the relation needed before each step
from the one needed after it, as EC's `sim` does with its sets of equal variables, but with any
relation: deterministic code on either side by wp (`stmt_wp`: copies, dead assignments and
the frame resets of inlined calls disappear into the relation), samplings on both sides
coupled by the identity (`equiv_rnd`), calls of the same procedure on both sides from equal
arguments and globals (`equiv_call`), and conditionals on both sides (`prhlStmt_seq_if_bwd`):
equal guards, each branch's relation found by `sim` on the branches.  Where both statements
are used up, the precondition must imply what is left (`equiv_skip`), closed by `simp_all` if it
can; anything else (a loop, calls of different procedures, a sampling against other code) stops
`sim` with that goal.
-/

namespace GaudisCrypt

section Rules

variable {A Aₜ Aₑ B : ProgramState → ProgramState → Prop} {c₁ c₂ : Getter Bool ProgramState}
  {s₁ s₂ t₁ t₂ e₁ e₂ : Stmt}

/-- **Conditionals on both sides, backwards** (EC's `sim` on `if`s): the branches related from
`Aₜ` and `Aₑ`, and before the conditionals equal guards and the branch's relation.  The branches'
judgments come first, so that their relations are found before the code before them is
processed. -/
theorem prhlStmt_seq_if_bwd (ht : prhlStmt Aₜ t₁ t₂ B) (he : prhlStmt Aₑ e₁ e₂ B)
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ => c₁.get σ₁ = c₂.get σ₂ ∧
      (c₁.get σ₁ = true → Aₜ σ₁ σ₂) ∧ (c₁.get σ₁ = false → Aₑ σ₁ σ₂)) :
    prhlStmt A (.seq s₁ (.ifThenElse c₁ t₁ e₁)) (.seq s₂ (.ifThenElse c₂ t₂ e₂)) B := by
  refine prhlStmt_seq (prhlStmt_if (fun _ _ h => h.1) ?_ ?_) h
  · exact prhlStmt_pre ht fun _ _ h => h.1.2.1 h.2
  · exact prhlStmt_pre he fun _ _ h => h.1.2.2 h.2

end Rules

namespace ECSim

open Lean Meta

/-- A write `X.set v s` through a lens `X` (`Setter.set (Lens.toSetter X) v s`): `(X, v, s)`. -/
def lensWrite? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``Setter.set 5 then
    let S := e.getArg! 2
    if S.isAppOfArity ``Lens.toSetter 3 then some (S.getArg! 2, e.getArg! 3, e.getArg! 4)
    else none
  else none

/-- **Chains of writes in normal form** (EC's memory: what a run of assignments leaves): two
writes of the same lens are one (`Setter.set_set`), two writes of disjoint lenses
(`Lens.Disjoint`, by instance search) in a fixed order (`Expr.lt` of the lenses), swapped by
`Lens.Disjoint.commute` when out of order.  Two chains of writes on the same state are equal
once in normal form exactly when they write the same values to the same lenses. -/
simproc_decl lensWriteNorm (Setter.set _ _ (Setter.set _ _ _)) := fun e => do
  let some (X, v, s) := lensWrite? e | return .continue
  let some (Y, w, t) := lensWrite? s | return .continue
  if X == Y then
    -- `X.set v (X.set w t) = X.set v t`
    let pf ← mkAppM ``Setter.set_set #[e.getArg! 2, t, w, v]
    return .visit { expr := mkAppN e.getAppFn ((e.getAppArgs).set! 4 t), proof? := pf }
  unless Y.lt X do return .continue
  let some inst ← (do
      let ty ← mkAppM ``Lens.Disjoint #[X, Y]
      try some <$> synthInstance ty catch _ => pure none) | return .continue
  -- `X.set v (Y.set w t) = Y.set w (X.set v t)`
  let pf ← mkAppOptM ``Lens.Disjoint.commute
    #[none, none, none, X, Y, inst, t, v, w]
  let rhs := (← instantiateMVars (← inferType pf)).appArg!
  return .visit { expr := rhs, proof? := pf }

end ECSim

namespace ECSim

open Lean Meta Elab Tactic PRHLWp

/-- EC's `inline*` on side `side?` of the goal `g` (a registered judgment): call sites inlined
(`Flatten.judgmentInline`) until every one left fails (an abstract procedure). -/
def inlineAll (g : MVarId) (side? : Option Nat) : MetaM MVarId := do
  let mut g := g
  let mut k := 0
  for _ in [0:500] do
    let (d, ty) ← Judgment.descOf g side?
    let n ← Flatten.countCallSites (ty.getArg! d.stmtArg)
    if k ≥ n then break
    let s ← saveState
    try g ← Flatten.judgmentInline k g side?
    catch _ =>
      s.restore
      k := k + 1
  return g

/-- `inlineAll` on both sides of a relational judgment, or on the one statement. -/
def inlineAllSides (g : MVarId) (side? : Option Nat) : MetaM MVarId := do
  let (descs, _) ← Judgment.descsOf g
  if side?.isNone && descs.size == 2 then
    inlineAll (← inlineAll g (some 1)) (some 2)
  else inlineAll g side?

/-- The kind of the last statement of `s`: `skip`, a conditional, a call, a sampling, or other. -/
inductive Last | skip | cond | call | sample | other
  deriving BEq

/-- The last statement of the right-nested `s` (after `stripLets`). -/
partial def lastOf (s : Lean.Expr) : Lean.Expr :=
  let s := stripLets s
  if s.isAppOf ``StmtWithHoles.seq then
    let l := lastOf (s.getArg! 2)
    if (stripLets l).isAppOf ``StmtWithHoles.skip then lastOf (s.getArg! 1) else l
  else s

/-- The kind of the last statement of `s`. -/
def lastKind (s : Lean.Expr) : MetaM Last := do
  let l := stripLets (lastOf s)
  if l.isAppOf ``StmtWithHoles.skip then return .skip
  if l.isAppOf ``StmtWithHoles.ifThenElse then return .cond
  if l.isAppOf ``StmtWithHoles.call' || l.isAppOf ``Stmt.call || l.isAppOf ``StmtWithHoles.call
    then return .call
  if l.isAppOf ``StmtWithHoles.sample then return .sample
  -- a call spelled through a definition
  if let some l' ← unfoldDefinition? l then
    if l'.isAppOf ``StmtWithHoles.call' then return .call
  return .other

/-- Close `∀ …, A → B` (what `equiv_skip` leaves) by `simp_all`, if it can. -/
def closeImp (g : MVarId) : TacticM (List MVarId) := do
  let s ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| first
      | (intros; subst_vars; simp_all; done)
      | (intros; subst_vars; simp_all [lensWriteNorm]; done)
      | (intros; simp_all [Setter.throwaway, ProgramState.globalL, lensWriteNorm]; done))) g
    if gs.isEmpty then return [] else s.restore; return [g]
  catch _ => s.restore; return [g]

/-- Run the tactic `stx` on `g`, the goals it leaves. -/
def runOn (g : MVarId) (stx : TSyntax `tactic) : TacticM (List MVarId) := evalTacticAt stx g

/-- EC's `sim` on the relational goal `g`, backwards (see the module docstring); the goals left.
`open?`: the precondition is a metavariable to be found (a branch of a conditional), assigned the
relation left where the statements are used up. -/
partial def sim (g : MVarId) (fuel : Nat := 400) : TacticM (List MVarId) := do
  if fuel == 0 then return [g]
  -- the deterministic code at the end of both sides
  let g ← Judgment.wpDet g none
  let ty ← prhlGoal g "sim"
  let k₁ ← lastKind (ty.getArg! 1)
  let k₂ ← lastKind (ty.getArg! 2)
  match k₁, k₂ with
  | .skip, .skip =>
    -- both used up: an open precondition is what is left, else the implication
    let pre ← instantiateMVars (ty.getArg! 0)
    if pre.getAppFn.isMVar then
      let ty' ← g.getType
      let post := (← instantiateMVars ty').getArg! 3
      unless ← isDefEq pre post do return [g]
      let gs ← applyLemma ``prhlStmt_skip g
      for h in gs do
        let _ ← evalTacticAt (← `(tactic| exact fun _ _ h => h)) h
      return []
    let g ← equivSkip g
    closeImp g
  | .cond, .cond =>
    let g ← HoareSplit.hoareSplit 1 g
    -- by hand, not `applyLemma`: the branches' relations `Aₜ`, `Aₑ` stay ordinary metavariables,
    -- for the branches' `sim` to assign
    let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_if_bwd
    let cTy ← inferType c
    let names := cTy.getForallBinderNames
    let (ms, _, concl) ← forallMetaTelescope cTy
    unless ← isDefEq concl (← g.getType) do return [g]
    let arg (n : Name) : TacticM MVarId := do
      let some i := names.findIdx? (· == n) | throwError "sim: no argument `{n}`"
      let m := ms[i]!.mvarId!
      m.setKind .syntheticOpaque
      return m
    let ht ← arg `ht
    let he ← arg `he
    let h ← arg `h
    g.assign (mkAppN c ms)
    let rt ← sim ht (fuel - 1)
    let re ← sim he (fuel - 1)
    let h ← Judgment.simpArg h 3 relSimpDecls []
    return rt ++ re ++ (← sim h (fuel - 1))
  | .call, .call =>
    let s ← saveState
    try
      let gs ← runOn g (← `(tactic| (equiv_call; try (case callee => rfl))))
      match gs with
      | [g'] => sim g' (fuel - 1)
      | _ => return gs
    catch _ => s.restore; return [g]
  | .sample, .sample =>
    let s ← saveState
    try
      let gs ← runOn g (← `(tactic| equiv_rnd))
      match gs with
      | [g'] => sim g' (fuel - 1)
      | _ => return gs
    catch _ => s.restore; return [g]
  | _, _ => return [g]

end ECSim

open Lean Elab Tactic ECSim in
/-- **EC's `inline*`** on a statement judgment, on both sides of a relational one or on side `i`
with `stmt_inline*{i}`. -/
-- two tokens: `stmt_inline*` would be read as `stmt_inline` and `*`
elab "stmt_inline" "*" s:(Judgment.judgmentSide)? : tactic =>
  liftMetaTactic1 fun g => some <$> inlineAllSides g (Judgment.sideOf? s)

open Lean Elab Tactic ECSim in
/-- **EC's `inline*`** on a `phoare` statement judgment. -/
elab "phoare_inline" "*" : tactic => liftMetaTactic1 fun g => some <$> inlineAllSides g none

open Lean Elab Tactic ECSim in
/-- **EC's `inline*`** on a Hoare triple about a statement. -/
elab "hoare_inline" "*" : tactic => liftMetaTactic1 fun g => some <$> inlineAllSides g none

open Lean Elab Tactic ECSim in
/-- **EC's `sim`**: see the module docstring. -/
elab "sim" : tactic => do
  let g ← getMainGoal
  let gs ← sim g
  replaceMainGoal gs

end GaudisCrypt
