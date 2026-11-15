import GaudisCrypt.Logic.PHoareExact

/-!
# pHL on exact bounds: the tactics

The rules of `Logic/PHoareExact.lean` as EasyCrypt writes them, on a goal
`phoare[ c : P ==> Q ] = r`:

* `phoare_seq n : E p₁ p₂ p₃ p₄ I` — EC's `seq n : E p₁ p₂ p₃ p₄ I` (`I` may be left out: EC's
  default `true`, its goal closed).  The bounds are reals;
  `_` leaves a bound open where the other bound of its branch is `0` (its goal is not asked).
  On a lower bound `≥ r`: the same goals with `≥`, `_` a bound `0`, and `r ≤ p₁ p₂ + p₃ p₄`.
  Goals in EC's order: `invariant`, `first_E`, `second_E`, `first_notE`, `second_notE`,
  `bound` (the reals' equation when the judgment's bound is `ENNReal.ofReal e`), and `nonneg`
  if `0 ≤ pᵢ` is not found.
* `phoare_case (E)` — EC's `case (E)`: goals `pos`, `neg`.
* `phoare_conseq (: _ ==> _ : = e)` — another bound `e` (a real): goals `bound`, then the
  judgment.
* `phoare_conseq (: P ==> _)` — a weaker precondition: goals `pre`, then the judgment.
* `phoare_conseq (: _ ==> Q₁) (: _ ==> Q₂)` — goals `post` (under `Q₂`, `Q₁` iff the
  judgment's event), `hoare` (the triple for `Q₂`), then the judgment for `Q₁`: EC's order.
* `phoare_conseq H` — from a judgment `H` about the same statement: goals `pre`, `bound`
  (closed when trivial).

Tests: `Logic/PHoareExactTest.lean`.
-/

namespace GaudisCrypt

namespace PHoareExact

open Lean Meta Elab Tactic PHoareWp ECConseq

/-- The main goal is an exact `phoare` judgment about a statement. -/
def isExact : TacticM Bool := withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  return ty.isAppOf ``phoareStmt && (ty.getArg! 3).isAppOf ``Eq

/-- β-reduce the goals' types (the conditions a rule builds: `fun σ => A σ ∧ E σ`). -/
def betaGoals : TacticM Unit := do
  let gs ← (← getGoals).mapM fun g => g.withContext do
    g.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← g.getType)))
  setGoals gs

/-- Clean the goals with the given tags as side conditions (`cleanSideGoal`); those of
`closeTrivial` are dropped when `intros; trivial` or `intros; rfl` closes them. -/
def cleanTagged (tags closeTrivial : List Name) : TacticM Unit := do
  let gs ← (← getGoals).filterMapM fun g => do
    let tag ← g.getTag
    unless tags.contains tag do return some g
    let g ← try cleanSideGoal g catch _ => pure g
    unless closeTrivial.contains tag do return some g
    let s ← saveState
    try
      let rest ← evalTacticAt (← `(tactic| (intros; first | trivial | rfl))) g
      if rest.isEmpty then return none
      s.restore; return some g
    catch _ => s.restore; return some g
  setGoals gs

/-- A goal `∀ σ, A σ → ENNReal.ofReal x = ENNReal.ofReal y`: the equation `x = y` of reals
(EC's bounds are reals); any other goal unchanged. -/
def realBound (g : MVarId) : TacticM MVarId := do
  let s ← saveState
  try
    let [g'] ← evalTacticAt
      (← `(tactic| (intro σ hσ; refine congrArg ENNReal.ofReal ?_; revert σ))) g
      | throwError "no"
    g'.setTag (← g.getTag)
    return g'
  catch _ => s.restore; return g

end PHoareExact

open Lean Meta Elab Tactic PHoareWp ECConseq PHoareExact in
/-- **EC's `case (E)`** on a `phoare` judgment: goals `pos` (`E` added to the precondition),
`neg` (`¬E`). -/
elab "phoare_case " E:term:max : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOf ``phoareStmt do throwError "phoare_case: not a `phoare` judgment"
  let Es ← Term.exprToSyntax (← elabGoalFunction E (mkSort Level.zero))
  refineTagged (← `(phoareStmt_case $Es ?pos ?neg)) [`pos, `neg]
  betaGoals

open Lean Meta Elab Tactic PHoareWp ECConseq PHoareExact in
/-- **EC's `conseq (: _ ==> _ : = e)`**: the bound `e` (a real, read like the judgment's
conditions) for the judgment's.  Goals `bound` (the two bounds are equal under the
precondition; an equation of reals when the judgment's bound is `ENNReal.ofReal _`), then the
judgment. -/
elab "phoare_conseq" " (" ": " "_" " ==> " "_" " : " "= " e:term ")" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOf ``phoareStmt do throwError "phoare_conseq: not a `phoare` judgment"
  let es ← Term.exprToSyntax (← elabGoalFunction e (mkConst ``Real))
  refineTagged (← `(phoareStmt_conseq_bound (fun σ => ENNReal.ofReal ($es σ)) ?bound ?judgment))
    [`bound, `judgment]
  -- the bound: over the reals when both sides are `ENNReal.ofReal _`
  let gs ← (← getGoals).mapM fun g => do
    unless (← g.getTag) == `bound do return g
    realBound g
  setGoals gs
  betaGoals
  cleanTagged [`bound] []
  -- the bounds `0` and `1` as the other rules state them (`hoare` on `= 0`, the event rules on
  -- `= 1`)
  setGoals (← (← getGoals).mapM fun g => do
    unless (← g.getTag) == `judgment do return g
    let s ← saveState
    try
      let [g'] ← evalTacticAt
        (← `(tactic| simp only [ENNReal.ofReal_zero, ENNReal.ofReal_one])) g | throwError "no"
      g'.setTag `judgment
      return g'
    catch _ => s.restore; return g)

open Lean Meta Elab Tactic PHoareWp ECConseq PHoareExact in
/-- **EC's `conseq (: P ==> _)`** on an exact bound: the weaker precondition `P`.  Goals `pre`
(closed when trivial), then the judgment. -/
elab_rules (kind := phoareConseq) : tactic
  | `(tactic| phoare_conseq (: $P ==> $Q)) => withMainContext do
    unless (← isExact) && isHole Q && !isHole P do throwUnsupportedSyntax
    let Ps ← Term.exprToSyntax (← elabGoalFunction P (mkSort Level.zero))
    refineTagged (← `(phoareStmt_conseq_pre $Ps ?pre ?judgment)) [`pre, `judgment]
    betaGoals
    cleanTagged [`pre] [`pre]

open Lean Meta Elab Tactic PHoareWp ECConseq PHoareExact in
/-- **EC's `conseq (: _ ==> Q₁) (: _ ==> Q₂)`** on an exact bound: the judgment for the event
`Q₁`, and `Q₂` in Hoare logic.  Goals in EC's order: `post` (under `Q₂`, `Q₁` iff the judgment's
event), `hoare`, then the judgment. -/
elab "phoare_conseq" " (" ": " "_" " ==> " Q₁:term ")" " (" ": " "_" " ==> " Q₂:term ")" : tactic =>
    withMainContext do
  unless ← isExact do throwUnsupportedSyntax
  -- `conseq (: _ ==> true) (: _ ==> _)` on the bound `1`: the rule of `Logic/PHoareRnd.lean`
  -- (the two forms are one syntax)
  if isHole Q₂ then
    let g ← getMainGoal
    let some g ← PHoareRnd.boundOne g
      | throwError "phoare_conseq: not `phoare[ c : P ==> Q ] = 1`{indentExpr (← g.getType)}"
    let some g ← PHoareRnd.foldEvent g
      | throwError "phoare_conseq: the postcondition is not an event{indentExpr (← g.getType)}"
    replaceMainGoal [g]
    evalTactic (← `(tactic| refine phoareStmt_eq_one_of_hoare_lossless ?lossless ?hoare))
    let gs ← getGoals
    for g in gs do g.setTag (← g.getTag).eraseMacroScopes
    let hoare ← gs.filterM fun g => return (← g.getTag) == `hoare
    setGoals (hoare ++ gs.filter (!hoare.contains ·))
    return
  let g ← getMainGoal
  let some g ← PHoareRnd.foldEvent g
    | throwError "phoare_conseq: the postcondition is not an event{indentExpr (← g.getType)}"
  replaceMainGoal [g]
  let Q₁s ← Term.exprToSyntax (← elabGoalFunction Q₁ (mkSort Level.zero))
  let Q₂s ← Term.exprToSyntax (← elabGoalFunction Q₂ (mkSort Level.zero))
  refineTagged (← `(phoareStmt_conseq_hoare $Q₁s $Q₂s ?post ?hoare ?judgment))
    [`post, `hoare, `judgment]
  betaGoals
  cleanTagged [`post] []

open Lean Meta Elab Tactic PHoareWp ECConseq PHoareExact in
/-- **EC's `conseq H`** on a `phoare` judgment, `H` a judgment about the same statement and
postcondition: goals `pre` (the goal's precondition implies `H`'s) and `bound` (the bounds are
equal under the goal's precondition), each closed when trivial. -/
elab "phoare_conseq " H:ident : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOf ``phoareStmt do throwError "phoare_conseq: not a `phoare` judgment"
  refineTagged (← `(phoareStmt_conseq_of $H ?pre ?bound)) [`pre, `bound]
  setGoals (← (← getGoals).mapM fun g => do
    if (← g.getTag) == `bound then realBound g else pure g)
  betaGoals
  cleanTagged [`pre, `bound] [`pre, `bound]

open Lean Meta Elab Tactic PHoareSeq PHoareWp ECConseq PHoareExact in
/-- **EC's `seq n : E p₁ p₂ p₃ p₄ I`** on an exact bound or a lower bound (see the module
docstring); without `I`, EC's default `true`. -/
elab_rules (kind := phoareSeq) : tactic
  | `(tactic| phoare_seq $n:num : $E:term $p₁:term $p₂:term $p₃:term $p₄:term $[$I?:term]?) => do
    let ty ← withMainContext do instantiateMVars (← getMainTarget)
    unless ty.isAppOf ``phoareStmt do throwUnsupportedSyntax
    let ρ := ty.getArg! 3
    let exact := ρ.isAppOf ``Eq
    let lower := ρ.isAppOf ``GE.ge || (ρ.find? (·.isConstOf ``GE.ge)).isSome
    unless exact || lower do throwUnsupportedSyntax
    -- EC counts the statements of a block (the body of a loop before the rest, as `while`
    -- leaves it): the sequence flattened first
    liftMetaTactic1 fun g => some <$> Judgment.onStmt TacticMisc.flattenSeq g
    liftMetaTactic1 fun g => some <$> Judgment.onStmt (splitLeading n.getNat) g
    let I : Term ← match I? with
      | some I => pure I
      | none => `(True)
    let Es ← Term.exprToSyntax (← elabGoalFunction E (mkSort Level.zero))
    let Is ← Term.exprToSyntax (← elabGoalFunction I (mkSort Level.zero))
    let real (p : Term) : TacticM Term := if isHole p then `((0 : ℝ)) else `(($p : ℝ))
    let (r₁, r₂, r₃, r₄) := (← real p₁, ← real p₂, ← real p₃, ← real p₄)
    if exact then
      -- (`f`, `s`: the branch's two goals, named holes of this call — a hole named by a plain
      -- identifier would be the hole of that name of an earlier `phoare_seq` in the same proof)
      let branch (first second f s : Term) : TacticM Term := do
        if isHole first && isHole second then
          throwError "phoare_seq: both bounds of a branch are `_`"
        else if isHole first then `(PHoareSeqBranch.second_zero _ $s)
        else if isHole second then
          `(PHoareSeqBranch.first_zero _ (fun _ => indicatorE_le_one _) $f)
        else `(PHoareSeqBranch.both hI $f $s)
      let bE ← branch p₁ p₂ (← `(?first_E)) (← `(?second_E))
      let bN ← branch p₃ p₄ (← `(?first_notE)) (← `(?second_notE))
      withMainContext do
        refineTagged (← `(have hI := ?invariant
          phoareStmt_seq_eq $Es $Is $r₁ $r₂ $r₃ $r₄ ?nonneg hI $bE $bN ?bound))
          [`invariant, `first_E, `second_E, `first_notE, `second_notE, `bound, `nonneg]
    else
      -- a lower bound: a bound `_` is `0`, its judgment trivial
      let sub (p : Term) (g : Term) : TacticM Term :=
        if isHole p then `(phoareStmt_ge_zero _ _ _) else pure g
      let (g₁, g₂, g₃, g₄) := (← sub p₁ (← `(?first_E)), ← sub p₂ (← `(?second_E)),
        ← sub p₃ (← `(?first_notE)), ← sub p₄ (← `(?second_notE)))
      withMainContext do
        refineTagged (← `(phoareStmt_seq_ge $Es $Is $r₁ $r₂ $r₃ $r₄ ?nonneg ?invariant
          $g₁ $g₂ $g₃ $g₄ ?bound))
          [`invariant, `first_E, `second_E, `first_notE, `second_notE, `bound, `nonneg]
    -- `0 ≤ pᵢ`: found, or left
    let gs ← (← getGoals).filterMapM fun g => do
      unless (← g.getTag) == `nonneg do return some g
      let s ← saveState
      try
        let rest ← evalTacticAt (← `(tactic| (refine ⟨?_, ?_, ?_, ?_⟩ <;>
          first | positivity | (simp only [EC.mu, EC.mu1]; positivity)))) g
        if rest.isEmpty then return none
        s.restore; return some g
      catch _ => s.restore; return some g
    -- the invariant `true` (EC's default): closed
    let gs ← gs.filterMapM fun g => do
      unless (← g.getTag) == `invariant && I?.isNone do return some g
      let s ← saveState
      try
        let rest ← evalTacticAt
          (← `(tactic| exact hoare_post (hoareStmt_true _ _) fun _ _ => trivial)) g
        if rest.isEmpty then return none
        s.restore; return some g
      catch _ => s.restore; return some g
    -- the bound: over the reals when the judgment's is `ENNReal.ofReal _`
    let gs ← gs.mapM fun g => do
      unless (← g.getTag) == `bound do return g
      if exact then realBound g else
        let s ← saveState
        try
          let [g'] ← evalTacticAt
            (← `(tactic| (intro σ hσ; refine ENNReal.ofReal_le_ofReal ?_; revert σ))) g
            | throwError "no"
          g'.setTag `bound
          return g'
        catch _ => s.restore; return g
    -- the invariant's triple, shared by the branches, is not a hypothesis of the goals
    let gs ← gs.mapM fun g => g.withContext do
      let some d := (← getLCtx).findDecl? fun d =>
        if d.userName.eraseMacroScopes == `hI then some d else none | return g
      try g.clear d.fvarId catch _ => return g
    setGoals gs
    betaGoals
    cleanTagged [`bound] [`bound]

end GaudisCrypt
