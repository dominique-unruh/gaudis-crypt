import GaudisCrypt.Logic.Inline
import GaudisCrypt.Logic.HoareSplit

/-!
# Backwards wp steps on a Hoare triple

`hoareWpStep k`: split off the last `k` statements of a triple's statement (`hoareSplit`), close
their triple by the wp rules (`hoareWpFull`), and simplify the reads in the resulting
postcondition (`simpReads`).  All three are meta-functions on goals, without tactic syntax.
-/

namespace GaudisCrypt

open Classical in
/-- A local variable read after a reset: its initial value if the reset covers its name, else
    what it was before.  Unconditional, so that `simp` needs no discharger for it; the condition
    is decided afterwards, on the literal set the reset prints with.  The slot is spelled with
    its fields and `@Lens.intoLocal T`, as a slot in a program is: stated for a variable `v`,
    the content type would be the projection `v.type`, which does not unify with `T` before `v`
    is known. -/
theorem intoLocal_varLens_get_resetSetter (n : String) (T : Type) (i : Nonempty T) (k : Nat)
    (hk : k = VariableName.encode n) (S : Set String) (u : Unit) (σ : ProgramState) :
    (@Lens.intoLocal T (varLens (@VariableName.mk n T i k hk))).get ((resetSetter S).set u σ)
      = if n ∈ S then VariableAssignment.init (@VariableName.mk n T i k hk)
        else (@Lens.intoLocal T (varLens (@VariableName.mk n T i k hk))).get σ := by
  by_cases h : n ∈ S <;> simp [resetSetter, Lens.intoLocal, Lens.chain,
    ProgramState.localL, h]

/-! The globals of a state after a write: what a global read in a condition becomes once it is
a plain `g.get σ.globals` (`eval_lens_global`).  `eval` keeps its state in an instance argument,
where `simp` does not rewrite, so the reads are taken out of `eval` first. -/

theorem globals_intoLocal_set {A : Type*} (x : Lens A VariableAssignment) (v : A)
    (τ : ProgramState) : (x.intoLocal.set v τ).globals = τ.globals := rfl

theorem globals_intoGlobal_set {A : Type*} (x : Lens A VariableAssignment) (v : A)
    (τ : ProgramState) : (x.intoGlobal.set v τ).globals = x.set v τ.globals := rfl

theorem globals_resetSetter_set (S : Set String) (u : Unit) (τ : ProgramState) :
    ((resetSetter S).set u τ).globals = τ.globals := rfl

theorem globals_globalL_set (g : VariableAssignment) (τ : ProgramState) :
    (ProgramState.globalL.set g τ).globals = g := rfl

theorem globals_chain_get (l m : Lens ProgramState ProgramState) (τ : ProgramState) :
    ((l.chain m).get τ).globals = (m.get (l.get τ)).globals := rfl

theorem globals_trafo_get (τ : ProgramState) : (Flatten.trafo.get τ).globals = τ.globals := rfl

theorem globals_emb_get (τ : ProgramState) : (Flatten.emb.get τ).globals = τ.globals := rfl

theorem globals_rename_get (ren : List (String × String)) (τ : ProgramState) :
    ((Flatten.rename ren).get τ).globals = τ.globals := rfl

/-- Membership in a prefix region, as a statement about character lists that `decide` settles on
    literals.  A rewrite of the membership only: unfolding `stringsStartingWith` itself would
    also change how the resets in the program print. -/
theorem mem_stringsStartingWith_iff (p n : String) :
    n ∈ stringsStartingWith p ↔ p.toList <+: n.toList :=
  Iff.rfl

namespace HoareWp

open Lean Meta TacticMisc

/-- The simp set of `simpReads`: theorems are rewritten with, definitions unfolded. -/
def simpReadsDecls : List Name :=
  [``liftLens, ``LiftLens.lift, ``eval_lens_full, ``eval_getter_full, ``Lens.pair, ``Lens.set_get,
   ``Lens.get_of_disjoint_set, ``intoLocal_varLens_get_resetSetter, ``Set.mem_union,
   ``Set.mem_insert_iff, ``Set.mem_singleton_iff, ``Set.mem_sdiff, ``mem_stringsStartingWith_iff,
   ``if_pos, ``if_neg, ``not_false_eq_true,
   -- global reads, through writes to the state
   ``eval_lens_global, ``eval_getter_global, ``allGlobals_get,
   ``globals_intoLocal_set, ``globals_intoGlobal_set, ``globals_resetSetter_set,
   ``globals_globalL_set, ``globals_chain_get, ``globals_trafo_get, ``globals_emb_get,
   ``globals_rename_get,
   -- the argument getters of a procedure triple (`hoare_call_wp`)
   ``Lens.id_get, ``Lens.ofst_get, ``Lens.osnd_get,
   -- the trivial parts of a call's precondition (`hoare_call_wp` with `hoareProc_true`)
   ``implies_true, ``true_implies, ``and_true, ``true_and]

/-- Simplify argument `i` of the goal (an application, `hoareStmt A s B` say) with `simp only`
    over the declarations `decls` (theorems are rewritten with, definitions unfolded) and the
    default simprocs, leaving the other arguments alone.  Never fails; an unchanged goal is
    returned as is. -/
def simpGoalArg (decls : List Name) (g : MVarId) (i : Nat) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let (f, args) := (ty.getAppFn, ty.getAppArgs)
  let some B := args[i]? | throwError "simpGoalArg: no argument {i} in{indentExpr ty}"
  let mut thms : SimpTheorems := {}
  for n in decls do
    if (← getConstInfo n) matches .thmInfo _ then thms ← thms.addConst n
    else thms ← thms.addDeclToUnfold n
  let ctx ← Simp.mkContext (config := { decide := true }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp B ctx #[← Simp.getSimprocs]
  let target := mkAppN f (args.set! i r.expr)
  let some h := r.proof? | return ← g.replaceTargetDefEq target
  let motive ← withLocalDeclD `x (← inferType B) fun x =>
    mkLambdaFVars #[x] (mkAppN f (args.set! i x))
  g.replaceTargetEq target (← mkCongrArg motive h)

/-- Reads through writes, in the postcondition of a goal `hoareStmt A s B` (as `hoare_assign_wp`
    leaves it): `liftLens` of a program-state lens is the lens itself, `Lens.pair` splits a tuple
    write into one write per slot, `eval_lens_full` turns a read pinned at a written state into a
    `get`, a read of the written slot is the value (`Lens.set_get`), and a read of a disjoint
    slot ignores the write (`Lens.get_of_disjoint_set`; disjointness by instance search, so for
    slots with literal names), and a read after a reset is decided by whether the reset covers
    the name (`intoLocal_varLens_get_resetSetter`, then membership in the literal set the reset
    prints with, by `decide`).  `simp only` with `simpReadsDecls` and the default simprocs.

    Only the postcondition is rewritten: the same lemmas would also unfold the lenses of the
    statement itself (a tuple l-value into a raw `Setter` structure), which then no longer
    prints in the program syntax.  Never fails; an unchanged goal is returned as is. -/
def simpReads (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``hoareStmt 3 do
    throwError "simpReads: expected a goal `hoareStmt A s B`, got{indentExpr ty}"
  simpGoalArg (← simpReadsDecls.mapM pure) g 2

/-- One backwards step on a goal `hoareStmt A {x₁; …; xₙ} B`: split off the last `k` statements
(`hoareSplit`), close their triple by the wp rules, which fixes the intermediate condition
(`hoare_seq`, `hoareWpFull`), and continue with the triple about `x₁; …; xₙ₋ₖ`, its
postcondition simplified (`simpReads`).  The last `k` statements must be straight-line code. -/
def hoareWpStep (k : Nat) (g : MVarId) : MetaM MVarId := do
  let g ← HoareSplit.hoareSplit k g
  -- as `apply hoare_seq`: the second statement's triple first, the intermediate condition open
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``hoare_seq)
  let gq :: gp :: _ := gs | throwError "hoareWpStep: `hoare_seq` left{gs.length} goals"
  let rest ← hoareWpFull gq
  unless rest.isEmpty do
    throwError "hoareWpStep: the wp rules left goals{rest.map (·.name)}"
  simpReads gp

/-- `hoare_wp k`: `hoareWpStep k` on the main goal — split off the last `k` statements, close
their triple by the wp rules, and simplify the reads in the new postcondition. -/
elab "hoare_wp " k:num : tactic =>
  Elab.Tactic.liftMetaTactic1 fun g => some <$> hoareWpStep k.getNat g

/-- One backwards step over a call, on a goal `hoareStmt A {x₁; …; xₙ₋₁; x <- call p (args)} B`:
close the call (`hoare_seq`), and continue with the triple about `x₁; …; xₙ₋₁`, its
postcondition simplified (`simpReads`).  `h` is either a procedure triple about `p`, used through
`hoare_call_wp` (the new postcondition is `h`'s precondition at the arguments, and `B` after any
result and globals that `h`'s postcondition allows), or a rule concluding a statement triple
about the call itself, such as `hoare_call_frame L hp`, whose remaining arguments are found by
unification.  Arguments of the rule that unification leaves open are returned as goals. -/
def hoareCallStep (h : Lean.Expr) (g : MVarId) : MetaM (List MVarId) := do
  let g ← HoareSplit.hoareSplit 1 g
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``hoare_seq)
  let gq :: gp :: _ := gs | throwError "hoareCallStep: `hoare_seq` left {gs.length} goals"
  let hTy ← whnfR (← instantiateMVars (← inferType h))
  -- a procedure triple goes through `hoare_call_wp`; anything else is the rule itself
  let (rule, ms) ← if hTy.isAppOf ``hoareProc then do
      let rule ← mkConstWithFreshMVarLevels ``hoare_call_wp
      let (ms, _, _) ← forallMetaTelescope (← inferType rule)
      unless ← isDefEq ms[6]! h do
        throwError "hoare_call: not a procedure triple:{indentExpr (← inferType h)}"
      pure (rule, ms)
    else do
      let (ms, _, _) ← forallMetaTelescope (← inferType h)
      pure (h, ms)
  let ty ← instantiateForall (← inferType rule) ms
  unless ← isDefEq ty (← gq.getType) do
    throwError "hoare_call: the call rule{indentExpr (← instantiateMVars ty)}\ndoes not match \
      the last statement{indentExpr (← gq.getType)}"
  gq.assign (← instantiateMVars (mkAppN rule ms))
  let open_ ← ms.filterMapM fun m => do
    let m := m.mvarId!
    if ← m.isAssigned then return none else return some m
  return (← simpReads gp) :: open_.toList

/-- `hoare_call h`: `hoareCallStep h` on the main goal — the last statement is a call, closed by
`h`: a procedure triple about the callee (EC's `call (_ : P ==> Q)`), or a rule for the call
statement, such as `hoare_call_frame L hp` (the callee does not touch `L`).  Without `h`, the
trivial triple `hoareProc_true`: the call may return anything and write any globals. -/
elab "hoare_call" h?:(ppSpace colGt term:max)? : tactic => Elab.Tactic.withMainContext do
  let h ← match h? with
    | some h => Elab.Tactic.elabTerm h none
    | none => do
      let c ← mkConstWithFreshMVarLevels ``hoareProc_true
      let (ms, _, _) ← forallMetaTelescope (← inferType c)
      pure (mkAppN c ms)
  Elab.Tactic.liftMetaTactic fun g => hoareCallStep h g

/-- A loop step, on a goal `hoareStmt A {x₁; …; xₙ₋₁; while c body} B` and an invariant `I`:
`hoare_while` closes the loop, leaving three goals, in order: the body preserves `I` (from
`I ∧ c`), `I` with a failed test implies `B` (reads generalized, `generalizeReads`), and the
triple about `x₁; …; xₙ₋₁` with postcondition `I`. -/
def hoareWhileStep (I : Lean.Expr) (g : MVarId) : MetaM (List MVarId) := do
  let g ← HoareSplit.hoareSplit 1 g
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``hoare_seq)
  let gq :: gp :: _ := gs | throwError "hoareWhileStep: `hoare_seq` left {gs.length} goals"
  let rule ← mkConstWithFreshMVarLevels ``hoare_while
  let (ms, _, ty) ← forallMetaTelescope (← inferType rule)
  unless ← isDefEq ms[2]! I do
    throwError "hoare_while: not a condition on the program state:{indentExpr (← inferType I)}"
  unless ← isDefEq ty (← gq.getType) do
    throwError "hoare_while: the last statement is not a loop:{indentExpr (← gq.getType)}"
  gq.assign (mkAppN rule ms)
  let gBody := ms[4]!.mvarId!
  gBody.setTag `body
  let gExit ← try generalizeReads ms[5]!.mvarId! catch _ => pure ms[5]!.mvarId!
  gExit.setTag `exit
  return [gBody, gExit, gp]

open Lean Elab Tactic in
/-- `hoare_while I`: `hoareWhileStep` on the main goal, with the invariant `I` written like a
condition of a `hoare[ ]` triple — `§x` reads the program variable `x` of the goal's program, or a
global.  Goals: `body`, `exit`, then the code before the loop with postcondition `I`. -/
elab "hoare_while " I:term : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOfArity ``hoareStmt 3 do
    throwError "hoare_while: expected a goal `hoareStmt A s B`, got{indentExpr ty}"
  -- the program variables of the goal, each bound to its slot, as a `hoare[ ]` triple binds them
  let vars := (← ProgramSyntax.frameVars #[ty.getArg! 0, ty.getArg! 1, ty.getArg! 2] #[]).filter
    (·.printable)
  let mut stx ← `((GaudiExpr[ $I ] : Getter Prop ProgramState).get)
  for v in vars.reverse do
    let some slot := v.slots[0]? | continue
    stx ← `(letI $(mkIdent (.mkSimple v.name)) := $(← Term.exprToSyntax slot); $stx)
  let Ie ← elabTermEnsuringType stx (← mkArrow (mkConst ``ProgramState) (mkSort 0))
  Term.synthesizeSyntheticMVarsNoPostponing
  let Ie ← instantiateMVars Ie
  liftMetaTactic fun g => hoareWhileStep Ie g

/-- The end of a backwards proof, on a goal `hoareStmt A skip B` (the statement possibly under
its `let`s): the implication `∀ σ, A σ → B σ` (`hoare_skip_of_imp`), with the reads of the state
in it generalized to plain values (`generalizeReads`), if there are any. -/
def hoareSkip (g : MVarId) : MetaM MVarId := do
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``hoare_skip_of_imp)
  let [g] := gs | throwError "hoareSkip: `hoare_skip_of_imp` left {gs.length} goals"
  try generalizeReads g catch _ => pure g

/-- `hoare_skip`: `hoareSkip` on the main goal — from `hoareStmt A skip B` to `∀ x …, A → B`
with the reads of the state as plain values. -/
elab "hoare_skip" : tactic =>
  Elab.Tactic.liftMetaTactic1 fun g => some <$> hoareSkip g

end HoareWp

end GaudisCrypt
