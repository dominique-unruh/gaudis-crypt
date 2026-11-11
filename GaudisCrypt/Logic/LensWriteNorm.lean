import GaudisCrypt.Language.Lens

/-!
# Chains of lens writes in normal form

`lensWriteNorm` (a simproc): two writes of the same lens are one, two writes of disjoint lenses
in a fixed order.  Used by `sim`'s implications (`Logic/ECSim.lean`) and by `stmt_swap`'s side
goals (`Logic/StmtSwap.lean`): two chains of writes on the same state are equal once in normal
form exactly when they write the same values to the same lenses.
-/

namespace GaudisCrypt

namespace ECSim

open Lean Meta

/-- A write `X.set v s` through a lens `X` (`Setter.set (Lens.toSetter X) v s`): `(X, v, s)`. -/
def lensWrite? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``Setter.set 5 then
    let S := e.getArg! 2
    if S.isAppOfArity ``Lens.toSetter 3 then some (S.getArg! 2, e.getArg! 3, e.getArg! 4)
    else none
  else none

/-- The lens `X` as `lensWriteNorm` compares it: every subterm in reducible normal form (a
variable is `localVarLens n T` or, once a rule has unfolded that `abbrev`,
`(varLens ⟨n, T, …⟩).intoLocal`, its type `T` or `⟨n, T, …⟩.type`) and its proofs erased (the
slot's `Nonempty` and key proofs, which two occurrences of the same variable need not share). -/
def lensKey (X : Lean.Expr) : MetaM Lean.Expr := do
  Meta.transform (← instantiateMVars X)
    (pre := fun e => do
      if ← isProof e then return .done (mkConst ``True.intro) else return .continue)
    (post := fun e => do
      let e' ← whnfR e
      return if e' == e then .done e else .visit e')

/-- **Chains of writes in normal form** (EC's memory: what a run of assignments leaves): two
writes of the same lens are one (`Setter.set_set`), two writes of disjoint lenses
(`Lens.Disjoint`, by instance search) in a fixed order (`Expr.lt` of their `lensKey`s), swapped by
`Lens.Disjoint.commute` when out of order.  Two chains of writes on the same state are equal
once in normal form exactly when they write the same values to the same lenses. -/
simproc_decl lensWriteNorm (Setter.set _ _ (Setter.set _ _ _)) := fun e => do
  let some (X, v, s) := lensWrite? e | return .continue
  let some (Y, w, t) := lensWrite? s | return .continue
  let kX ← lensKey X
  let kY ← lensKey Y
  if kX == kY then
    -- `X.set v (X.set w t) = X.set v t`
    let pf ← mkAppM ``Setter.set_set #[e.getArg! 2, t, w, v]
    return .visit { expr := mkAppN e.getAppFn ((e.getAppArgs).set! 4 t), proof? := pf }
  unless kY.lt kX do return .continue
  let some inst ← (do
      let ty ← mkAppM ``Lens.Disjoint #[X, Y]
      try some <$> synthInstance ty catch _ => pure none) | return .continue
  -- `X.set v (Y.set w t) = Y.set w (X.set v t)`
  let pf ← mkAppOptM ``Lens.Disjoint.commute
    #[none, none, none, X, Y, inst, t, v, w]
  let rhs := (← instantiateMVars (← inferType pf)).appArg!
  return .visit { expr := rhs, proof? := pf }

end ECSim

end GaudisCrypt
