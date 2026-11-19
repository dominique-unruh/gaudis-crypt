import GaudisCrypt.Logic.PRHLWp

/-!
# Equal states after the same writes

    subst_states    -- from `X.set a s₁ = X.set b s₂` (and so on inward), `s₁ = s₂`

EC's `sp` over the same initializations on both sides, from equal memories, leaves the memories
equal: `={glob D}` holds for any `D` after it.  Ours leaves the equation of the two states before
the writes, in the form `∃ old values, (the states with the old values written back) are equal`,
next to the new values (`S.m{1} = FMap.empty`, …).  When the new values agree on both sides,
the states themselves are equal: `subst_states` peels the writes from the outside in
(`Lens.eq_of_set_eq_of_get_eq`, each `X.get sᵢ` read through the inner writes and rewritten with
the hypotheses), down to `σ₁ = σ₂`.
-/

namespace GaudisCrypt

/-- Two states that are equal after a write of the same lens, and agree on that lens before it,
are equal. -/
theorem Lens.eq_of_set_eq_of_get_eq {a m : Type*} (X : Lens a m) {x y : a} {s₁ s₂ : m}
    (h : X.set x s₁ = X.set y s₂) (hg : X.get s₁ = X.get s₂) : s₁ = s₂ :=
  calc s₁ = X.set (X.get s₁) s₁ := (X.get_set s₁).symm
    _ = X.set (X.get s₁) (X.set x s₁) := (X.set_set s₁ x _).symm
    _ = X.set (X.get s₁) (X.set y s₂) := by rw [h]
    _ = X.set (X.get s₁) s₂ := X.set_set s₂ y _
    _ = X.set (X.get s₂) s₂ := by rw [hg]
    _ = s₂ := X.get_set s₂

namespace StateEq

open Lean Meta Elab Tactic

/-- `X.set x s` (a write of the lens `X`): `(X, x, s)`. -/
def lensWrite? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let e := e.consumeMData
  guard (e.isAppOfArity ``Setter.set 5)
  let st := (e.getArg! 2).consumeMData
  guard (st.isAppOfArity ``Lens.toSetter 3)
  return (st.getArg! 2, e.getArg! 3, e.getArg! 4)

/-- A hypothesis `X.set x s₁ = X.set y s₂` (the same lens on both sides). -/
def peelable? (d : LocalDecl) : MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let some (_, l, r) := (← instantiateMVars d.type).eq? | return none
  let some (X₁, _, s₁) := lensWrite? l | return none
  let some (X₂, _, s₂) := lensWrite? r | return none
  unless ← withReducible (isDefEq X₁ X₂) do return none
  return some (X₁, s₁, s₂)

end StateEq

end GaudisCrypt

open Lean Meta Elab Tactic GaudisCrypt StateEq in
/-- **Equal states after the same writes**: see the module docstring.  Each hypothesis
`X.set x s₁ = X.set y s₂` whose `X.get s₁ = X.get s₂` follows from the reads through writes and
the hypotheses (`simp_reads`, `simp only [*]`) is replaced by `s₁ = s₂`, until no write is left on
either side.  Fails if no hypothesis can be peeled. -/
elab "subst_states" : tactic => withMainContext do
  let mut progress := false
  let mut fuel := 64
  while fuel > 0 do
    fuel := fuel - 1
    let g ← getMainGoal
    let found ← g.withContext do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if let some (X, s₁, s₂) ← peelable? d then return some (d, X, s₁, s₂)
      return none
    let some (d, X, s₁, s₂) := found | break
    let step ← g.withContext do
      -- `X.get s₁ = X.get s₂`, by the reads through the inner writes and the hypotheses
      let getter ← mkAppM ``Lens.toGetter #[X]
      let hgTy ← mkEq (← mkAppM ``Getter.get #[getter, s₁]) (← mkAppM ``Getter.get #[getter, s₂])
      let hg ← mkFreshExprSyntheticOpaqueMVar hgTy
      let s ← saveState
      -- without error recovery: a step that does not prove it is a failure, not a `sorry`
      let log ← Core.getMessageLog
      Core.resetMessageLog
      let ok ← try
          let gs ← Term.withoutErrToSorry <| Tactic.run hg.mvarId! <| withoutRecover <|
            evalTactic (← `(tactic| (
              (try simp_reads)
              all_goals first | rfl | (simp only [*]; done) | (simp only [*] at *; done))))
          pure (gs.isEmpty && !(← Core.getMessageLog).hasErrors &&
            !(← instantiateMVars hg).hasSorry)
        catch _ => pure false
      Core.setMessageLog log
      unless ok do s.restore; return none
      let pf ← mkAppM ``Lens.eq_of_set_eq_of_get_eq #[X, d.toExpr, hg]
      let g' ← g.assert d.userName (← inferType pf) pf
      let (_, g') ← g'.intro1P
      return some (← g'.tryClear d.fvarId)
    let some g' := step | break
    replaceMainGoal [g']
    progress := true
  unless progress do throwError "subst_states: no equation of two states after the same writes"
