import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.PHoareWp

/-!
# The read normal form, and a strict `skip`

What a judgment tactic leaves for the logic is a goal about program states `σ` (one, or two for a
relational judgment).  The closers work on goals about plain values.  The step between the two,
generalizing every read of a state to a value, only works when the reads are spelled one way.

## The read normal form

A proposition `P` is in **read normal form** for the states `σ₁ … σₙ` when

* (atoms) every occurrence of a state is inside a read
  `x.get σ` (a lens or getter `x` on the program state: a local variable) or
  `X.get σ.globals` (a global variable, a region's getter), where `x`, `X` mention no state;
* (no expressions around reads) no `eval`, no `(Getter.mk f).get σ`, no read of a pair or a
  component lens: `(x.pair y).get σ` is `(x.get σ, y.get σ)`;
* (no reads through writes) no state other than the `σᵢ` themselves: `x.get (y.set v σ)` is
  `x.get σ` (or `v`), a reset or an inliner's renaming under a read is gone;
* (tests) the `Decidable` instance of every `decide`/`if` is the one of the proposition as it
  stands, so that a read inside an instance is the same atom as the visible one;
* (regions) a region that is a set of variables is read as the variables
  (`TacticMisc.globTuples`).

`ReadNorm.normalize` brings a goal to this form with the existing steps, all of them, in one
order: `relSimpDecls` (reads through writes), `unfoldReads`, `normDecideGoal`, `globTuples`.
Until now each path applied its own subset (the Hoare and pHL paths no `normDecide`: the reads
then do not generalize, and the goal silently stays about the states).

`ReadNorm.offenders` lists the places where a state is used other than by an atom.

## `ec_skip`

EC's `skip` on a Hoare triple, a `phoare` judgment or a relational one whose code is used up:
the implication, **normalized, with every read generalized to a value**.  Unlike `hoare_skip`,
`phoare_skip` and `equiv_skip`, it fails if a state survives, and says where it is still used.
The generalized values are named after their variables (`x`, or `x₁`/`x₂` by side).

New name, old tactics unchanged: proofs move to it one file at a time
(`notes/SHA3/TacticReview.md`, step 3).
-/

namespace GaudisCrypt.ReadNorm

open Lean Meta TacticMisc

/-- The target of `g`, a proposition about the states `σs` (free variables of its context), in
read normal form (see the module docstring). -/
def normalize (g : MVarId) (σs : Array FVarId) : MetaM MVarId := g.withContext do
  -- reads through writes, resets, renamings
  let g ← do
    let ty ← instantiateMVars (← g.getType)
    let r ← Judgment.simpWithNames PRHLWp.relSimpDecls [] ty
    if r.expr == ty then pure g else applySimpResultToTarget g ty r
  g.withContext do
    -- expressions around reads
    let mut ty ← instantiateMVars (← g.getType)
    for σ in σs do
      ty ← unfoldReads σ ty
    let g ← g.change ty
    -- the tests' instances, then the regions of variables
    let g ← normDecideGoal g
    globTuples g

/-- The subterms of `e` that use a state of `σs` other than by a read in normal form: an
application with a state (or its globals) as an argument that is not a read `x.get σ` with `x`
free of states.  Empty for a proposition in read normal form. -/
partial def offenders (σs : Array FVarId) (e : Lean.Expr) (acc : Array Lean.Expr := #[]) :
    Array Lean.Expr :=
  let isState (s : Lean.Expr) : Bool := σs.any (isStateOf · s)
  let hasState (t : Lean.Expr) : Bool := σs.any t.containsFVar
  if !hasState e then acc
  else if e.isAppOfArity ``Getter.get 4 && isState e.appArg! && !hasState (e.getArg! 2) then acc
  else if e.isAppOfArity ``ProgramState.globals 1 && isState e then acc
  else if e.isApp && e.getAppArgs.any isState then
    if acc.contains e then acc else acc.push e
  else match e with
    | .app f a => offenders σs a (offenders σs f acc)
    | .lam _ t b _ | .forallE _ t b _ => offenders σs b (offenders σs t acc)
    | .letE _ t v b _ => offenders σs b (offenders σs v (offenders σs t acc))
    | .mdata _ b | .proj _ _ b => offenders σs b acc
    | _ => if acc.contains e then acc else acc.push e

/-- A goal `∀ σ₁ … σₙ : ProgramState, P` (`n` is 1 or 2): `P` normalized and every read
generalized, `∀ x₁ … xₖ, P'`.  Fails if a state is still used, naming the places. -/
def generalizeStrict (tac : String) (g : MVarId) : MetaM MVarId := do
  -- the leading states
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let rec count (t : Lean.Expr) (n : Nat) : Nat := match t with
    | .forallE _ dom b _ => if dom.isConstOf ``ProgramState then count b (n + 1) else n
    | _ => n
  let n := count ty 0
  unless n == 1 || n == 2 do
    throwError "{tac}: expected a goal about one or two program states, `∀ σ, …`, got{indentExpr ty}"
  let (σs, g1) ← g.introN n
  let g2 ← normalize g1 σs
  -- where a state is used other than by a read (printed in the states' context)
  let bad ← g2.withContext do
    let bs := offenders σs (← instantiateMVars (← g2.getType))
    if bs.isEmpty then pure m!"" else
      addMessageContext m!"\na state is used other than by a read in normal form in{indentD
        (MessageData.joinSep (bs.toList.map (m!"{·}")) Format.line)}"
  let (_, g3) ← g2.revert σs (preserveOrder := true)
  let g4 ← try
      if n == 1 then generalizeReads g3 else PRHLWp.generalizeReadsRel g3 (normDec := true)
    catch e => throwError "{tac}: the reads cannot be generalized{bad}\n{e.toMessageData}"
  -- no state may be left
  let ty4 ← instantiateMVars (← g4.getType)
  if (count (← whnfR ty4) 0) > 0 then
    throwError "{tac}: a state is still used after the reads are generalized{bad}\
      \ngoal:{indentExpr ty4}"
  return g4

/-- EC's `skip` on a judgment whose code is used up (see the module docstring). -/
def ecSkip (g : MVarId) : MetaM MVarId := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let g ← if ty.isAppOf ``hoareStmt then do
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``hoare_skip_of_imp)
      let [g] := gs | throwError "ec_skip: `hoare_skip_of_imp` left {gs.length} goals"
      pure g
    else if ty.isAppOf ``phoareStmt then do
      let gs ← PHoareWp.applyIffMpr ``phoareStmt_skip_iff g
      let [g] := gs | throwError "ec_skip: `phoareStmt_skip_iff` left {gs.length} goals"
      pure g
    else if ty.isAppOf ``prhlStmt then do
      let gs ← PRHLWp.applyLemma ``prhlStmt_skip g
      let #[g] := gs | throwError "ec_skip: `prhlStmt_skip` left {gs.size} goals"
      pure g
    else throwError "ec_skip: not a Hoare, phoare or relational judgment:{indentExpr ty}"
  let g ← g.withContext do
    g.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← g.getType)))
  generalizeStrict "ec_skip" g

end GaudisCrypt.ReadNorm

open Lean Elab Tactic in
/-- **EC's `skip`, strict**: on a Hoare triple, a `phoare` judgment or a relational judgment
whose code is `skip`, the implication in read normal form with every read a value
(`Logic/ReadNorm.lean`).  Fails if a state survives. -/
elab "ec_skip" : tactic => liftMetaTactic1 fun g => some <$> GaudisCrypt.ReadNorm.ecSkip g
