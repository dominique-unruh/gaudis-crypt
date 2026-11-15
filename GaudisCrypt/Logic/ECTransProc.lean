import GaudisCrypt.Logic.ECTrans
import GaudisCrypt.Logic.PrTactics

/-!
# EasyCrypt's `transitivity` on procedures

    equiv_trans (N.f) (P₁ ==> Q₁) (P₂ ==> Q₂)   -- EC's `transitivity N.f (P₁ ==> Q₁) (P₂ ==> Q₂)`

On `equiv[ p₁ ~ p₂ : P ==> Q ]`: through the middle procedure `N.f`, the judgments
`equiv[ p₁ ~ N.f : P₁ ==> Q₁ ]` and `equiv[ N.f ~ p₂ : P₂ ==> Q₂ ]` (the rule
`prhlProc_trans_ec` of `Logic/ECTrans.lean`).  Goals in EC's order: `hP` (the precondition
gives the middle procedure's argument and memory), `hQ` (the postconditions compose), then
the two judgments `h₁`, `h₂`; `hP` and `hQ` are closed when trivial (EC's `=> //`).
-/

namespace GaudisCrypt

open Lean Meta Elab Tactic in
/-- **EC's `transitivity N.f (P₁ ==> Q₁) (P₂ ==> Q₂)`** on a judgment about two procedures: see
the module docstring. -/
elab "equiv_trans" " (" N:term ")" " (" P₁:term " ==> " Q₁:term ")"
    " (" P₂:term " ==> " Q₂:term ")" : tactic => withMainContext do
  let ty := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  unless ty.isAppOfArity ``prhlProc 6 do
    throwError "equiv_trans: not a judgment `equiv[ p₁ ~ p₂ : P ==> Q ]` about two procedures\
      {indentExpr ty}"
  let p₁ ← Term.exprToSyntax (ty.getArg! 3)
  let p₂ ← Term.exprToSyntax (ty.getArg! 4)
  evalTactic (← `(tactic| refine prhlProc_trans_ec ?hP ?hQ
    (?h₁ : equiv[ $p₁ ~ $N : $P₁ ==> $Q₁ ]) (?h₂ : equiv[ $N ~ $p₂ : $P₂ ==> $Q₂ ])))
  let gs ← getGoals
  for g in gs do g.setTag (← g.getTag).eraseMacroScopes
  -- the side conditions: closed when trivial (a precondition `true` with some middle argument
  -- and memory; postconditions that compose by transitivity of equality)
  let closeP ← `(tactic| (intro a₁ g₁ a₂ g₂ _; first
    | exact ⟨default, g₁, trivial, trivial⟩
    | exact ⟨a₁, g₁, trivial, trivial⟩
    | exact ⟨a₂, g₂, trivial, trivial⟩))
  let closeQ ← `(tactic| first
    | exact fun _ _ _ _ _ _ h₁ h₂ => Eq.trans h₁ h₂
    | exact fun _ _ _ _ _ _ h₁ h₂ => Eq.trans h₁ (congrArg _ h₂)
    | (intros; trivial))
  let mut out := []
  for tag in [`hP, `hQ, `h₁, `h₂] do
    for g in gs do
      unless (← g.getTag) == tag do continue
      if tag == `hP || tag == `hQ then
        let s ← saveState
        try
          let rest ← Tactic.withoutRecover
            (evalTacticAt (if tag == `hP then closeP else closeQ) g)
          if rest.isEmpty then continue
          s.restore
        catch _ => s.restore
      out := out ++ [g]
  setGoals out

end GaudisCrypt
