import GaudisCrypt.Logic.PrTactics

/-!
# EasyCrypt's `bypr`, on `phoare` judgments

`bypr` is the converse of `byphoare` (`Logic/PrTactics.lean`): a procedure judgment about an
event,

    phoare[ p : P ==> E ] ≤ (ENNReal.ofReal x)        (or `=`, `≥`)

its bound a real (as `byphoare` and `phoare_call (: P ==> Q)` leave it: EC's bounds are reals),
becomes the statement about the probabilities of the runs that satisfy the precondition,

    ∀ a &m, P a m → Pr[ p (a) @ &m : E ] ≤ x

(EC's goal after `bypr=> &m`: the arguments and the memory are introduced by `intro`).
-/

namespace GaudisCrypt

section Rules

variable {sig : ProcedureSignature} {A : sig.ParamType → VariableAssignment → Prop}
  {p : Procedure sig} {E : sig.ret → VariableAssignment → Prop} {x : ℝ}

/-- `bypr` for `≤`. -/
theorem Procedure.phoareProc_le_of_toReal_Pr_le
    (h : ∀ a σ, A a σ → (p.Pr a σ E : ℝ) ≤ x) :
    phoareProc A p (fun v g => indicatorE (E v g)) (· ≤ ·) (fun _ _ => ENNReal.ofReal x) := by
  intro a σ hA
  change p.ewp a (fun v g => indicatorE (E v g)) σ ≤ ENNReal.ofReal x
  rw [← Procedure.Pr_eq_ewp, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (h a σ hA)

/-- `bypr` for `≥`. -/
theorem Procedure.phoareProc_ge_of_le_toReal_Pr
    (h : ∀ a σ, A a σ → x ≤ (p.Pr a σ E : ℝ)) :
    phoareProc A p (fun v g => indicatorE (E v g)) (· ≥ ·) (fun _ _ => ENNReal.ofReal x) := by
  intro a σ hA
  change ENNReal.ofReal x ≤ p.ewp a (fun v g => indicatorE (E v g)) σ
  rw [← Procedure.Pr_eq_ewp, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (h a σ hA)

/-- `bypr` for `=`. -/
theorem Procedure.phoareProc_eq_of_toReal_Pr_eq
    (h : ∀ a σ, A a σ → (p.Pr a σ E : ℝ) = x) :
    phoareProc A p (fun v g => indicatorE (E v g)) Eq (fun _ _ => ENNReal.ofReal x) := by
  intro a σ hA
  change p.ewp a (fun v g => indicatorE (E v g)) σ = ENNReal.ofReal x
  rw [← Procedure.Pr_eq_ewp, ← ENNReal.ofReal_coe_nnreal, h a σ hA]

end Rules

/-- The event of a postcondition in the shape `phoare[ p : P ==> ev ]` elaborates to,
`fun res σ => let res := …; GaudiExpr[ indicatorE (ev) ].get ⟨σ, init⟩`, in the shape
`Pr[ … : ev ]` elaborates to (`GaudiExpr[ ev ]` read the same way), so that the goal `bypr`
leaves prints as probabilities; `none` for another shape. -/
partial def ByPr.eventOfPost? : Lean.Expr → Option Lean.Expr
  | .lam n t b bi => (eventOfPost? b).map (.lam n t · bi)
  | .letE n t v b nd => (eventOfPost? b).map (.letE n t v · nd)
  | .mdata _ b => eventOfPost? b
  | e => do
    guard (e.isAppOfArity ``Getter.get 4)
    let g := e.getArg! 2
    guard (g.isAppOfArity ``Getter.mk 3)
    let .lam n t b bi := g.getArg! 2 | none
    let b := b.consumeMData
    guard (b.isAppOfArity ``indicatorE 1)
    let ev := Lean.mkAppN g.getAppFn #[.sort 0, g.getArg! 1, .lam n t (b.getArg! 0) bi]
    return Lean.mkAppN e.getAppFn #[.sort 0, e.getArg! 1, ev, e.getArg! 3]

open Lean Elab Tactic in
/-- **EC's `bypr`** on a `phoare` judgment about a procedure, see the module docstring: the goal
`phoare[ p : P ==> E ] ≤ (ENNReal.ofReal x)` (`=`, `≥`) becomes
`∀ a &m, P a m → Pr[ p (a) @ &m : E ] ≤ x`. -/
elab "bypr" : tactic => withMainContext do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  -- the event as `Pr[ … ]` writes it, where the postcondition is `phoare[ … ]`'s
  let E? := if ty.isAppOfArity ``phoareProc 6 then ByPr.eventOfPost? (ty.getArg! 3) else none
  for rule in [``Procedure.phoareProc_le_of_toReal_Pr_le,
      ``Procedure.phoareProc_ge_of_le_toReal_Pr, ``Procedure.phoareProc_eq_of_toReal_Pr_eq] do
    let s ← saveState
    try
      match E? with
      | some E =>
        -- the signature first: the event's type is read off it
        let sig ← Term.exprToSyntax (ty.getArg! 0)
        evalTactic (← `(tactic|
          refine $(mkIdent rule) (sig := $sig) (E := $(← Term.exprToSyntax E)) ?_))
      | none => evalTactic (← `(tactic| refine $(mkIdent rule) ?_))
      try evalTactic (← `(tactic| beta_reduce)) catch _ => pure ()
      return
    catch _ => s.restore
  throwError "bypr: expected a procedure judgment `phoare[ p : P ==> E ] ≤ r` (or `=`, `≥`), \
    `E` an event and `r` a real bound (`ENNReal.ofReal x`)"

end GaudisCrypt
