import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.JudgmentWp

/-!
# EasyCrypt's `elim *` on a judgment's precondition

    equiv_elim* => a b      -- EC's `elim * => a b` (pRHL)
    hoare_elim* => a        -- the same on a Hoare triple

EC's `sp` over `x <- e` with `e` reading `x` leaves `exists x0, P[x0/x] /\ x = e[x0/x]` in the
precondition; `elim *` takes the existentials out, as universally quantified names.  Here: the
existentials of the precondition moved outward over its conjunctions, then introduced one by one
(`prhlStmt_exists_pre` of `Logic/PRHLStmt.lean`, `hoareStmt_exists_pre`), named as written (`_`
for an anonymous one).  The names go as EC's: `sp` nests the right side's existentials outside
the left side's, so a relational judgment's are named from the innermost.
-/

namespace GaudisCrypt

namespace ECElim

theorem and_ex_l {α : Sort*} {p : α → Prop} {q : Prop} : ((∃ x, p x) ∧ q) = ∃ x, p x ∧ q :=
  propext exists_and_right.symm

theorem and_ex_r {α : Sort*} {p : α → Prop} {q : Prop} : (q ∧ ∃ x, p x) = ∃ x, q ∧ p x :=
  propext exists_and_left.symm

end ECElim

/-- An existential in a Hoare precondition, out as a universally quantified value. -/
theorem hoareStmt_exists_pre {ι : Sort*} {P : ι → ProgramState → Prop} {s : Stmt}
    {B : ProgramState → Prop} (h : ∀ v, hoareStmt (P v) s B) :
    hoareStmt (fun σ => ∃ v, P v σ) s B :=
  fun σ ⟨v, hv⟩ => h v σ hv

end GaudisCrypt

namespace GaudisCrypt.ECElim

open Lean Meta Elab Tactic

/-- `elim *` with the rule `lem` (`prhlStmt_exists_pre` / `hoareStmt_exists_pre`). -/
def elimStar (lem : Name) (names : Array Name) (innerFirst := false) : TacticM Unit := do
  -- the existentials, out in front
  let g ← getMainGoal
  let g ← g.withContext <| Judgment.simpArg g 0 [``and_ex_l, ``and_ex_r] []
  replaceMainGoal [g]
  -- how many (to name them from the innermost, the left side's, with `innerFirst`)
  let k ← g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some A := ty.getAppArgs[0]? | throwError "elim*: not a judgment"
    lambdaTelescope A fun _ b => do
      let mut b := b
      let mut k := 0
      while b.isAppOfArity ``Exists 2 do
        k := k + 1
        let .lam _ _ body _ := b.appArg! | break
        b := body
      return k
  let names := if innerFirst then
      (List.range k).toArray.map fun j => (names[k - 1 - j]?).getD `_
    else names
  let mut i := 0
  for _ in [0:64] do
    let g ← getMainGoal
    let g ← g.withContext <| Judgment.simpArg g 0 [``and_ex_l, ``and_ex_r] []
    replaceMainGoal [g]
    let ty ← instantiateMVars (← g.getType)
    let some A := ty.getAppArgs[0]? | throwError "elim*: not a judgment"
    let isEx ← lambdaTelescope A fun _ b => pure (b.isAppOf ``Exists)
    unless isEx do break
    let n := (names[i]?).getD `_
    i := i + 1
    let x ← if n == `_ then pure (mkIdent (← mkFreshUserName `v)) else pure (mkIdent n)
    evalTactic (← `(tactic| refine $(mkIdent lem) fun $x => ?_))

end GaudisCrypt.ECElim

/-- **EC's `elim * => a b`** on a relational judgment (see the module docstring). -/
syntax (name := equivElim) "equiv_elim" "*" (" => " (colGt Lean.binderIdent)*)? : tactic

/-- **EC's `elim * => a`** on a Hoare triple (see the module docstring). -/
syntax (name := hoareElim) "hoare_elim" "*" (" => " (colGt Lean.binderIdent)*)? : tactic

open Lean Elab Tactic in
/-- The names of `=> a b _`. -/
def GaudisCrypt.ECElim.namesOf (xs : Array (TSyntax ``Lean.binderIdent)) : Array Lean.Name :=
  xs.map fun x => match x with
    | `(binderIdent| $i:ident) => i.getId
    | _ => `_

open Lean Elab Tactic GaudisCrypt.ECElim in
elab_rules : tactic
  | `(tactic| equiv_elim* $[=> $xs*]?) =>
    elimStar ``GaudisCrypt.prhlStmt_exists_pre (namesOf (xs.getD #[])) (innerFirst := true)
  | `(tactic| hoare_elim* $[=> $xs*]?) =>
    elimStar ``GaudisCrypt.hoareStmt_exists_pre (namesOf (xs.getD #[]))
