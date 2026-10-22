import GaudisCrypt.Logic.HoareWp
import GaudisCrypt.Logic.PHoare

/-!
# Backwards reasoning for probabilistic Hoare judgments

The tactics of `Logic/HoareWp.lean` and `Logic/Inline.lean`, for `phoareStmt`:

* `phoare_inline n` — inline call site `n` (the inliner of `hoare_inline`);
* `phoare_split k` — regroup the statement, the last `k` statements in a block of their own;
* `phoare_wp k` — replace the expectation by the exact expectation of the last `k` statements
  (`phoareStmt_seq_iff`).  Exact for every statement but a loop: an abstract call stays a
  symbolic `Procedure.ewp` term;
* `phoare_skip` — at `skip`, the inequality or equation itself, reads generalized.
-/

namespace GaudisCrypt

/-! ## Judgments about equivalent statements -/

theorem SubProbability.expected_mapState {α : Type v} {s t : Type u} (f : t → s)
    (μ : SubProbability (α × t)) (F : α × s → ENNReal) :
    (μ.mapState f).expected F = μ.expected fun p => F (p.1, f p.2) := by
  change (μ >>= fun p => pure (p.1, f p.2)).expected F = _
  rw [SubProbability.expected_bind]
  simp only [expected_pure]

/-- **A judgment about an equivalent statement**: along `s.EquivInLens s' l`, the judgment about
`s` is the one about `s'` with the conditions, the expectation and the bound read through `l`. -/
theorem phoareStmt_iff_of_equivInLens {A : ProgramState → Prop} {s s' : Stmt}
    {g : ProgramState → ENNReal} {ρ : ENNReal → ENNReal → Prop} {r : ProgramState → ENNReal}
    {l : Lens ProgramState ProgramState} (h : s.EquivInLens s' l) :
    phoareStmt A s g ρ r ↔
      phoareStmt (fun τ => A (l.get τ)) s' (fun τ => g (l.get τ)) ρ (fun τ => r (l.get τ)) := by
  have h' : ∀ τ, s.ewp g (l.get τ) = s'.ewp (fun τ => g (l.get τ)) τ := fun τ => by
    have := h ⟨⟩ (l.get τ) τ rfl
    rw [StmtWithHoles.instantiate_empty, StmtWithHoles.instantiate_empty] at this
    simp only [Stmt.ewp, ProgramDenotation.wp, ← this, SubProbability.expected_mapState]
  constructor
  · intro hs τ hA
    rw [← h' τ]
    exact hs _ hA
  · intro hs σ hA
    have hτ : l.get (l.set σ σ) = σ := l.set_get σ σ
    have := hs (l.set σ σ) (show A (l.get (l.set σ σ)) by rw [hτ]; exact hA)
    rw [← h'] at this
    simpa only [hτ] using this

/-- `phoareStmt_iff_of_equivInLens`, backwards, with the conditions given up to an equation:
what `phoare_inline` applies. -/
theorem phoareStmt_of_equivInLens {A A' : ProgramState → Prop} {s s' : Stmt}
    {g g' r r' : ProgramState → ENNReal} {ρ : ENNReal → ENNReal → Prop}
    {l : Lens ProgramState ProgramState} (h : s.EquivInLens s' l)
    (hA : (fun τ => A (l.get τ)) = A') (hg : (fun τ => g (l.get τ)) = g')
    (hr : (fun τ => r (l.get τ)) = r') (h' : phoareStmt A' s' g' ρ r') :
    phoareStmt A s g ρ r := by
  subst hA hg hr
  exact (phoareStmt_iff_of_equivInLens h).mpr h'

/-- A judgment about an equivalent statement, without renaming. -/
theorem phoareStmt_of_equiv {A : ProgramState → Prop} {s s' : Stmt}
    {g r : ProgramState → ENNReal} {ρ : ENNReal → ENNReal → Prop} (h : s.Equiv s')
    (h' : phoareStmt A s' g ρ r) : phoareStmt A s g ρ r :=
  (phoareStmt_iff_of_equivInLens h).mpr h'

/-- `Stmt.ewp_call`, at the spelling the statements carry. -/
theorem StmtWithHoles.ewp_call {sig} (x : Setter sig.ret ProgramState) (p : Procedure sig)
    (args : Getter sig.ParamType ProgramState) (g : ProgramState → ENNReal) :
    Stmt.ewp (StmtWithHoles.call x p args) g
      = fun σ => p.ewp (args.get σ) (fun v gl => g (x.set v (ProgramState.globalL.set gl σ)))
          σ.globals :=
  Stmt.ewp_call x p args g

namespace PHoareWp

open Lean Meta Elab Tactic TacticMisc

/-- Apply the right-to-left direction of the equivalence `lem`, its arguments by unification. -/
def applyIffMpr (lem : Name) (g : MVarId) : MetaM (List MVarId) := do
  let c ← mkConstWithFreshMVarLevels lem
  let (ms, _, ty) ← forallMetaTelescope (← inferType c)
  let some (a, b) := ty.iff? | throwError "applyIffMpr: `{lem}` is not an equivalence"
  -- not `MVarId.apply`: it would unfold the judgment (a `∀`) and guess the arity wrong
  unless ← isDefEq a (← g.getType) do
    throwError "applyIffMpr: `{lem}` does not apply to{indentExpr (← g.getType)}"
  let g' ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars b) (← g.getTag)
  g.assign (mkApp4 (mkConst ``Iff.mpr) a b (mkAppN c ms) g')
  return [g'.mvarId!]

/-- The parts of a goal `phoareStmt A s g ρ r`. -/
def phoareParts (ty : Lean.Expr) : MetaM (Array Lean.Expr) := do
  unless ty.isAppOfArity ``phoareStmt 5 do
    throwError "expected a goal `phoareStmt A s g ρ r`, got{indentExpr ty}"
  return ty.getAppArgs

/-- On a goal `phoareStmt A s g ρ r`: rewrite the statement with `f` (a statement and a proof of
`s.Equiv s'`), and continue with the judgment about the new statement (`hoareOnStmt`). -/
def phoareOnStmt (f : Lean.Expr → MetaM (Lean.Expr × Lean.Expr)) (g : MVarId) : MetaM MVarId :=
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let #[A, s, e, ρ, r] ← phoareParts ty | unreachable!
    let (s', p) ← f s
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``phoareStmt #[A, s', e, ρ, r])
      (← g.getTag)
    g.assign (← mkAppOptM ``phoareStmt_of_equiv
      #[some A, some s, some s', some e, some r, some ρ, some p, some g'])
    return g'.mvarId!

/-- `phoare_split k`: regroup the statement as `{x₁; …; xₙ₋ₖ}; {xₙ₋ₖ₊₁; …; xₙ}`. -/
def phoareSplit (k : Nat) (g : MVarId) : MetaM MVarId :=
  phoareOnStmt (HoareSplit.splitSeq k) g

elab "phoare_split " k:num : tactic =>
  liftMetaTactic1 fun g => some <$> phoareSplit k.getNat g

/-- The simp set computing an expectation: the exact expectations of the statements, the reads of
`simpReads`, and the uniform distribution's average. -/
def ewpDecls : List Name :=
  [``Stmt.ewp_seq, ``Stmt.ewp_skip, ``Stmt.ewp_assign, ``Stmt.ewp_sample,
   ``Stmt.ewp_ifThenElse, ``StmtWithHoles.ewp_call, ``Stmt.ewp_call,
   ``uniform_expected, ``Fintype.sum_bool, ``Fintype.card_bool, ``Nat.cast_ofNat,
   ``Bool.true_eq_false, ``Bool.false_eq_true, ``if_true, ``if_false,
   ``Bool.true_beq, ``Bool.false_beq, ``Bool.not_eq_true', ``Bool.or_eq_true,
   -- events, and the arithmetic they leave
   ``indicatorE_true, ``indicatorE_false, ``ENNReal.zero_div, ``zero_add, ``add_zero, ``mul_one,
   ``one_mul, ``mul_zero, ``zero_mul,
   -- products of events, and constants out of a call's expectation (linearity)
   ``Bool.and_eq_true, ``indicatorE_and, ``Procedure.ewp_const_mul, ``Procedure.ewp_mul_const,
   -- the side conditions of `phoare_call`
   ``le_refl, ``eq_self_iff_true, ``forall_const, ``and_self, ``ite_true, ``ite_false]
  ++ HoareWp.simpReadsDecls

/-- `M.procedure` for a procedure module `M` that evaluates to `Module.proc q` (the inliner's
module evaluation, `Flatten.moduleStep?`) ↦ `q`, the spelling call sites carry after inlining
(`FairCoin.flip.procedure`, say).  Anything else, an abstract module say, is left as it is. -/
partial def procedureConst (p : Lean.Expr) : MetaM Simp.Result := do
  unless p.isAppOfArity ``Module.Proc.procedure 2 do return { expr := p }
  let sig := p.getArg! 0
  let rec go (r : Simp.Result) (fuel : Nat) : MetaM (Option Simp.Result) := do
    if r.expr.isAppOf ``Module.proc then return some r
    if fuel == 0 then return none
    let some step ← Flatten.moduleStep? r.expr | return none
    go (← r.mkEqTrans step) (fuel - 1)
  let some r ← go { expr := p.appArg! } 64 | return { expr := p }
  let q := r.expr.appArg!
  let h₁ ← match r.proof? with
    | some h => mkCongrArg (mkApp (mkConst ``Module.Proc.procedure) sig) h
    | none => mkEqRefl p
  let h₂ ← mkAppM ``Module.procedure_proc' #[q]
  return { expr := q, proof? := some (← mkEqTrans h₁ h₂) }

/-- `M.procedure` ↦ `q` where the procedure module `M` evaluates to `Module.proc q`
(`procedureConst`): one spelling for a callee, whether it came from the notation or from
inlining (where it is often a `moduletype` accessor applied to a record). -/
simproc_decl reduceProcedureConst (Module.Proc.procedure _) := fun e => do
  -- the module evaluation unfolds definitions: not at `simp`'s reducible transparency
  let r ← withDefault (procedureConst e)
  if r.proof?.isNone then return .continue
  return .done r

/-- The default simprocs, and `reduceProcedureConst`. -/
def ewpSimprocs : MetaM Simp.Simprocs := do
  (← Simp.getSimprocs).add ``reduceProcedureConst (post := true)

/-- Simplify `e` with `simp only` over `decls` (theorems rewritten with, definitions unfolded)
    and the default simprocs. -/
def simpExprWith (decls : List Name) (e : Lean.Expr) : MetaM Simp.Result := do
  let mut thms : SimpTheorems := {}
  for n in decls do
    if (← getConstInfo n) matches .thmInfo _ then thms ← thms.addConst n
    else thms ← thms.addDeclToUnfold n
  let ctx ← Simp.mkContext (config := { decide := true }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← simp e ctx #[← ewpSimprocs]).1

/-- Simplify the expectation of a goal `phoareStmt A s g ρ r` (`ewpDecls`, `ewpSimprocs`). -/
def simpPost (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let r ← simpExprWith ewpDecls (ty.getArg! 2)
  let args := ty.getAppArgs
  let target := mkAppN ty.getAppFn (args.set! 2 r.expr)
  let some h := r.proof? | return ← g.replaceTargetDefEq target
  let motive ← withLocalDeclD `x (← inferType (ty.getArg! 2)) fun x =>
    mkLambdaFVars #[x] (mkAppN ty.getAppFn (args.set! 2 x))
  g.replaceTargetEq target (← mkCongrArg motive h)

/-- On a goal `phoareStmt A s g ρ r`: inline call site `n` of `s` and continue with the judgment
about the result, its conditions read through the renaming and cleaned (`hoareInline`). -/
def phoareInline (n : Nat) (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let #[A, s, e, ρ, r] ← phoareParts ty | unreachable!
  let step ← Flatten.inlineProcedure n s (Flatten.namesIn r (Flatten.namesIn e
    (Flatten.namesIn A)))
  -- cleaned by the inliner, then simplified like an expectation (`ewpDecls`): the inliner's own
  -- lemmas do not push `.globals` through its renaming lenses
  let clean (C : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
    let (C', h) ← Flatten.cleanCondition C step.trafo
    let r ← simpExprWith ewpDecls C'
    match r.proof? with
    | some p => return (r.expr, ← mkEqTrans h p)
    | none => return (r.expr, h)
  let (A', hA) ← clean A
  let (e', he) ← clean e
  let (r', hr) ← clean r
  let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``phoareStmt #[A', step.stmt, e', ρ, r'])
    (← g.getTag)
  g.assign (← mkAppOptM ``phoareStmt_of_equivInLens
    #[some A, some A', some s, some step.stmt, some e, some e', some r, some r', some ρ,
      some step.trafo, some step.proof, some hA, some he, some hr, some g'])
  return g'.mvarId!

elab "phoare_inline " n:num : tactic =>
  liftMetaTactic1 fun g => some <$> phoareInline n.getNat g

/-- One backwards step on a goal `phoareStmt A {x₁; …; xₙ} g ρ r`: split off the last `k`
statements (`phoareSplit`), and continue with the judgment about `x₁; …; xₙ₋ₖ`, the expectation
replaced by the exact expectation of the last `k` statements (`phoareStmt_seq_iff`), computed and
simplified (`ewpDecls`). -/
def phoareWpStep (k : Nat) (g : MVarId) : MetaM MVarId := do
  let g ← phoareSplit k g
  let gs ← applyIffMpr ``phoareStmt_seq_iff g
  let [g] := gs | throwError "phoare_wp: `phoareStmt_seq_iff` left {gs.length} goals"
  simpPost g

elab "phoare_wp " k:num : tactic =>
  liftMetaTactic1 fun g => some <$> phoareWpStep k.getNat g

/-- `h : f a₀ … aₙ` with argument `i` replaced by the result `r` of simplifying it. -/
def rewriteArg (h : Lean.Expr) (i : Nat) (r : Simp.Result) : MetaM Lean.Expr := do
  let ty ← instantiateMVars (← inferType h)
  let some pf := r.proof? | return h
  let args := ty.getAppArgs
  let motive ← withLocalDeclD `x (← inferType args[i]!) fun x =>
    mkLambdaFVars #[x] (mkAppN ty.getAppFn (args.set! i x))
  mkEqMP (← mkCongrArg motive pf) h

/-- A procedure judgment `phoareProc P p G ρ R` with its conditions `P`, `G`, `R` in the normal
form `phoare_wp` leaves expectations in (`ewpDecls`): the `phoare[ ]` notation wraps them in
`let`s and `GaudiExpr` getters.  The procedure is left as it is, so that the judgment still
unifies with a call statement. -/
def normalizeSpec (h : Lean.Expr) : MetaM Lean.Expr := do
  let ty ← instantiateMVars (← inferType h)
  unless ty.isAppOfArity ``phoareProc 6 do return h
  let mut h := h
  for i in [1, 3, 5] do
    let ty ← instantiateMVars (← inferType h)
    h ← rewriteArg h i (← simpExprWith ewpDecls (ty.getArg! i))
  return h

/-- One backwards step over a call, on a goal `phoareStmt A {x₁; …; xₙ₋₁; x <- call p (a)} g ρ r`
and a judgment `h` about `p`: close the call by `phoareStmt_call_le`/`_ge`/`_eq` (by the goal's
relation; an exact `h` serves for all three), and continue with the judgment about
`x₁; …; xₙ₋₁`, its expectation the bound of `h` under the side condition, simplified
(`ewpDecls`).  When the continuation is literally `h`'s postcondition and `h`'s precondition
simplifies to `True`, the condition disappears. -/
def phoareCallStep (h : Lean.Expr) (g : MVarId) : MetaM MVarId := do
  let g ← phoareSplit 1 g
  let ty ← instantiateMVars (← g.getType)
  let #[_, _, _, ρ, _] ← phoareParts ty | unreachable!
  let h ← normalizeSpec h
  let hTy ← instantiateMVars (← inferType h)
  unless hTy.isAppOfArity ``phoareProc 6 do
    throwError "phoare_call: not a procedure judgment `phoareProc A p G ρ r`:{indentExpr hTy}"
  let ρ' := hTy.getArg! 4
  let (rule, h) ← if ρ.isAppOf ``Eq then
      if ρ'.isAppOf ``Eq then pure (``phoareStmt_call_eq, h)
      else throwError "phoare_call: an exact goal needs an exact judgment about the callee"
    else if ρ.isAppOf ``LE.le then
      if ρ'.isAppOf ``LE.le then pure (``phoareStmt_call_le, h)
      else if ρ'.isAppOf ``Eq then pure (``phoareStmt_call_le, ← mkAppM ``phoareProc_le_of_eq #[h])
      else throwError "phoare_call: an upper bound needs an upper bound about the callee"
    else if ρ.isAppOf ``GE.ge then
      if ρ'.isAppOf ``GE.ge then pure (``phoareStmt_call_ge, h)
      else if ρ'.isAppOf ``Eq then pure (``phoareStmt_call_ge, ← mkAppM ``phoareProc_ge_of_eq #[h])
      else throwError "phoare_call: a lower bound needs a lower bound about the callee"
    else throwError "phoare_call: the goal's relation is not `=`, `≤` or `≥`:{indentExpr ρ}"
  let c ← mkConstWithFreshMVarLevels rule
  let (ms, _, cty) ← forallMetaTelescope (← inferType c)
  -- the judgment about the callee is the one argument of type `phoareProc …`; the judgment about
  -- the code before the call is the last
  let some hm ← ms.findM? fun m => return (← instantiateMVars (← inferType m)).isAppOf ``phoareProc
    | throwError "phoare_call: `{rule}` has no procedure judgment argument"
  unless ← isDefEq hm h do
    throwError "phoare_call: the judgment{indentExpr (← inferType h)}\ndoes not fit `{rule}`"
  unless ← isDefEq cty ty do
    throwError "phoare_call: the last statement is not a call to the judgment's procedure:\
      {indentExpr ty}"
  g.assign (mkAppN c ms)
  let g' := ms.back!.mvarId!
  g'.setTag (← g.getTag)
  simpPost g'

/-- `phoare_call h`: `phoareCallStep h` on the main goal — the last statement is a call, closed by
the procedure judgment `h` about the callee (EC's `call (_ : P ==> Q)`). -/
elab "phoare_call " h:term : tactic => withMainContext do
  let h ← elabTerm h none
  liftMetaTactic1 fun g => some <$> phoareCallStep h g

/-- A procedure judgment `phoareProc P p G Eq R` as a conditional rewrite rule
`∀ args σ, P args σ → p.ewp args G σ = R args σ`, normalized like the goal (`ewpDecls`,
`ewpSimprocs`).  Bounds (`≤`,
`≥`) are not rewrite rules and are rejected. -/
def specRewrite (h : Lean.Expr) : MetaM Lean.Expr := do
  -- everything normalized, the procedure included (`reduceProcedureConst`), as in the goal
  let r ← simpExprWith ewpDecls (← instantiateMVars (← inferType h))
  let h ← match r.proof? with
    | some pf => mkEqMP pf h
    | none => mkExpectedTypeHint h r.expr
  let ty ← instantiateMVars (← inferType h)
  unless ty.isAppOfArity ``phoareProc 6 && (ty.getArg! 4).isAppOf ``Eq do
    throwError "phoare_simp: not an exact procedure judgment `phoareProc A p G Eq R`:\
      {indentExpr ty}"
  let some unfolded ← unfoldDefinition? ty | throwError "phoare_simp: cannot unfold{indentExpr ty}"
  mkExpectedTypeHint h (← Core.betaReduce unfolded)

/-- `phoare_simp [h₁, …]`: simplify with the simp set of `phoare_wp` (`ewpDecls`) and the exact
procedure judgments `hᵢ` as rewrite rules for their callees' expectations (`specRewrite`).  On a
goal `phoareStmt A s g ρ r` only the expectation `g` is simplified; on any other goal (what
`phoare_skip` leaves, say) the whole goal. -/
syntax (name := phoareSimp) "phoare_simp" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| phoare_simp $[[$hs?,*]]?) => withMainContext do
  let hs : Array Term := (hs?.map (·.getElems)).getD #[]
  let mut thms : SimpTheorems := {}
  for n in ewpDecls do
    if (← getConstInfo n) matches .thmInfo _ then thms ← thms.addConst n
    else thms ← thms.addDeclToUnfold n
  for h in hs do
    let pf ← specRewrite (← elabTerm h none)
    thms ← thms.add (.other `phoare_simp) #[] pf
  let ctx ← Simp.mkContext (config := { decide := true }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  if ty.isAppOfArity ``phoareStmt 5 then
    let B := ty.getArg! 2
    let (r, _) ← simp B ctx #[← ewpSimprocs]
    let args := ty.getAppArgs
    let target := mkAppN ty.getAppFn (args.set! 2 r.expr)
    match r.proof? with
    | none => replaceMainGoal [← g.replaceTargetDefEq target]
    | some pf =>
      let motive ← withLocalDeclD `x (← inferType B) fun x =>
        mkLambdaFVars #[x] (mkAppN ty.getAppFn (args.set! 2 x))
      replaceMainGoal [← g.replaceTargetEq target (← mkCongrArg motive pf)]
  else
    match ← simpTarget g ctx #[← ewpSimprocs] with
    | (none, _) => replaceMainGoal []
    | (some g', _) => replaceMainGoal [g']

/-- A loop step, on a goal `phoareStmt A {x₁; …; xₙ₋₁; while c body} g ≤ r` and an expectation
invariant `I`: `phoareStmt_while_le` closes the loop, leaving three goals, in order: `body` (one
iteration does not increase `I`, from the states where the test passes), `exit` (`g ≤ I` where
the test fails, simplified, reads generalized), and the judgment about `x₁; …; xₙ₋₁` with `I` as
its expectation. -/
def phoareWhileLeStep (I : Lean.Expr) (g : MVarId) : MetaM (List MVarId) := do
  let g ← phoareSplit 1 g
  let rule ← mkConstWithFreshMVarLevels ``phoareStmt_while_le
  let (ms, _, ty) ← forallMetaTelescope (← inferType rule)
  -- `{A pre body c g r} (I) (hbody) (hexit) (hpre)`
  unless ← isDefEq ms[6]! I do
    throwError "phoare_while_le: not an expectation on the program state:\
      {indentExpr (← inferType I)}"
  unless ← isDefEq ty (← g.getType) do
    throwError "phoare_while_le: the goal is not an upper bound about a trailing loop:\
      {indentExpr (← g.getType)}"
  g.assign (mkAppN rule ms)
  let gBody := ms[7]!.mvarId!
  gBody.setTag `body
  -- the exit condition: simplified like an expectation, reads generalized
  let gExit := ms[8]!.mvarId!
  let gExit ← gExit.withContext do
    let t ← Core.betaReduce (← instantiateMVars (← gExit.getType))
    let r ← simpExprWith ewpDecls t
    match r.proof? with
    | some pf => gExit.replaceTargetEq r.expr pf
    | none => gExit.replaceTargetDefEq r.expr
  let gExit ← try generalizeReads gExit catch _ => pure gExit
  gExit.setTag `exit
  let gPre := ms[9]!.mvarId!
  gPre.setTag (← g.getTag)
  return [gBody, gExit, gPre]

open Lean Elab Tactic in
/-- `phoare_while_le I`: `phoareWhileLeStep` on the main goal, with the expectation invariant `I`
written like a condition of a `phoare[ ]` judgment (an `ENNReal` expression; `§x` reads the
program variable `x`, or a global).  Goals: `body`, `exit`, then the code before the loop. -/
elab "phoare_while_le " I:term : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let #[A, s, e, _, r] ← phoareParts ty | unreachable!
  -- the program variables of the goal, each bound to its slot, as a `phoare[ ]` judgment binds
  -- them (see `hoare_while`)
  let vars := (← ProgramSyntax.frameVars #[A, s, e, r] #[]).filter (·.printable)
  let mut stx ← `((GaudiExpr[ $I ] : Getter ENNReal ProgramState).get)
  for v in vars.reverse do
    let some slot := v.slots[0]? | continue
    stx ← `(letI $(mkIdent (.mkSimple v.name)) := $(← Term.exprToSyntax slot); $stx)
  let Ie ← elabTermEnsuringType stx (← mkArrow (mkConst ``ProgramState) (mkConst ``ENNReal))
  Term.synthesizeSyntheticMVarsNoPostponing
  let Ie ← instantiateMVars Ie
  liftMetaTactic fun g => phoareWhileLeStep Ie g

/-- Elaborate an expectation written like a condition of a `phoare[ ]` judgment about the goal's
program: `§x` reads the program variable `x` (bound to its slot, as the notation binds it) or a
global. -/
def elabGoalExpectation (I : Term) : TacticM Lean.Expr := withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let #[A, s, e, _, r] ← phoareParts ty | unreachable!
  let vars := (← ProgramSyntax.frameVars #[A, s, e, r] #[]).filter (·.printable)
  let mut stx ← `((GaudiExpr[ $I ] : Getter ENNReal ProgramState).get)
  for v in vars.reverse do
    let some slot := v.slots[0]? | continue
    stx ← `(letI $(mkIdent (.mkSimple v.name)) := $(← Term.exprToSyntax slot); $stx)
  let Ie ← elabTermEnsuringType stx (← mkArrow (mkConst ``ProgramState) (mkConst ``ENNReal))
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars Ie

/-- A goal `∀ σ, …` about conditions and expectations: β-reduced, simplified like an expectation
(`ewpDecls`), reads generalized. -/
def cleanSideGoal (g : MVarId) : MetaM MVarId := g.withContext do
  let t ← Core.betaReduce (← instantiateMVars (← g.getType))
  let r ← simpExprWith ewpDecls t
  let g ← match r.proof? with
    | some pf => g.replaceTargetEq r.expr pf
    | none => g.replaceTargetDefEq r.expr
  try generalizeReads g catch _ => pure g

/-- A loop step for a lower bound, on `phoareStmt A {x₁; …; xₙ₋₁; while c body} g ≥ r`, with the
invariant `I` and the exit probability `ε` (`phoareStmt_while_ge`).  Goals, in order: `body`,
`exit`, the code before the loop, `lossless`, `progress`, and whichever of `I ≤ 1`, `g ≤ 1`,
`ε ≠ 0`, `ε ≤ 1` `simp` does not close. -/
def phoareWhileGeStep (I ε : Lean.Expr) (g : MVarId) : MetaM (List MVarId) := do
  let g ← phoareSplit 1 g
  let rule ← mkConstWithFreshMVarLevels ``phoareStmt_while_ge
  let (ms, _, ty) ← forallMetaTelescope (← inferType rule)
  -- `{A pre body c g r} (I) (ε) (hbody) (hexit) (hpre) (hll) (hprog) (hI1) (hg1) (hε0) (hε1)`
  unless ← isDefEq ms[6]! I do
    throwError "phoare_while_ge: not an expectation on the program state:\
      {indentExpr (← inferType I)}"
  unless ← isDefEq ms[7]! ε do throwError "phoare_while_ge: `ε` is not an `ENNReal`"
  unless ← isDefEq ty (← g.getType) do
    throwError "phoare_while_ge: the goal is not a lower bound about a trailing loop:\
      {indentExpr (← g.getType)}"
  g.assign (mkAppN rule ms)
  let tagged (i : Nat) (tag : Name) : MetaM MVarId := do
    let m := ms[i]!.mvarId!
    m.setTag tag
    return m
  let gBody ← tagged 8 `body
  let gExit ← cleanSideGoal (← tagged 9 `exit)
  gExit.setTag `exit
  let gPre ← tagged 10 (← g.getTag)
  let gLl ← tagged 11 `lossless
  let gProg ← tagged 12 `progress
  -- the side conditions: try `simp`
  let mut side := []
  for (i, tag) in [(13, `I_le_one), (14, `g_le_one), (15, `ε_ne_zero), (16, `ε_le_one)] do
    let m ← cleanSideGoal (← tagged i tag)
    m.setTag tag
    -- `simp` either closes it or leaves it as it was (a goal it only rewrote would have to be
    -- returned in place of `m`)
    let st ← saveState
    let closed ← try
        let (r?, _) ← simpGoal m (← Simp.mkContext (simpTheorems := #[← getSimpTheorems])
          (congrTheorems := ← getSimpCongrTheorems)) #[← Simp.getSimprocs]
        pure r?.isNone
      catch _ => pure false
    unless closed do
      st.restore
      side := side ++ [m]
  return [gBody, gExit, gPre, gLl, gProg] ++ side

open Lean Elab Tactic in
/-- `phoare_while_le I` for lower bounds: `phoare_while_ge I using ε` (`phoareWhileGeStep`), `I`
written like a condition of a `phoare[ ]` judgment, `ε` a plain `ENNReal`. -/
elab "phoare_while_ge " I:term " using " ε:term : tactic => do
  let Ie ← elabGoalExpectation I
  let εe ← withMainContext do
    let e ← elabTermEnsuringType ε (mkConst ``ENNReal)
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  liftMetaTactic fun g => phoareWhileGeStep Ie εe g

/-- The end of a backwards proof, on a goal `phoareStmt A skip g ρ r`: the relation itself,
`∀ σ, A σ → ρ (g σ) (r σ)` (`phoareStmt_skip_iff`), β-reduced, with the reads of the state
generalized to plain values (`generalizeReads`). -/
def phoareSkip (g : MVarId) : MetaM MVarId := do
  let gs ← applyIffMpr ``phoareStmt_skip_iff g
  let [g] := gs | throwError "phoare_skip: `phoareStmt_skip_iff` left {gs.length} goals"
  let g ← g.withContext do g.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars
    (← g.getType)))
  try generalizeReads g catch _ => pure g

elab "phoare_skip" : tactic =>
  liftMetaTactic1 fun g => some <$> phoareSkip g

end PHoareWp

end GaudisCrypt
