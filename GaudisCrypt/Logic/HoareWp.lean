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

/-- Membership in a prefix region, as a statement about character lists that `decide` settles on
    literals.  A rewrite of the membership only: unfolding `Flatten.prefixed` itself would also
    change how the resets in the program print. -/
theorem mem_prefixed_iff (p n : String) : n ∈ Flatten.prefixed p ↔ p.toList <+: n.toList :=
  Iff.rfl

namespace HoareWp

open Lean Meta TacticMisc

/-- The simp set of `simpReads`: theorems are rewritten with, definitions unfolded. -/
def simpReadsDecls : List Name :=
  [``liftLens, ``LiftLens.lift, ``eval_lens_full, ``Lens.pair, ``Lens.set_get,
   ``Lens.get_of_disjoint_set, ``intoLocal_varLens_get_resetSetter, ``Set.mem_union,
   ``Set.mem_insert_iff, ``Set.mem_singleton_iff, ``Set.mem_sdiff, ``mem_prefixed_iff, ``if_pos,
   ``if_neg, ``not_false_eq_true]

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
  let (A, s, B) := (ty.getArg! 0, ty.getArg! 1, ty.getArg! 2)
  let mut thms : SimpTheorems := {}
  for n in simpReadsDecls do
    if (← getConstInfo n) matches .thmInfo _ then thms ← thms.addConst n
    else thms ← thms.addDeclToUnfold n
  let ctx ← Simp.mkContext (config := { decide := true }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp B ctx #[← Simp.getSimprocs]
  let some h := r.proof? | return ← g.replaceTargetDefEq (mkApp3 (mkConst ``hoareStmt) A s r.expr)
  g.replaceTargetEq (mkApp3 (mkConst ``hoareStmt) A s r.expr)
    (← mkCongrArg (mkApp2 (mkConst ``hoareStmt) A s) h)

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
