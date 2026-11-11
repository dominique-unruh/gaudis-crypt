import GaudisCrypt.Logic.LoopTransform
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Syntax.PRHLSyntax

/-!
# EasyCrypt's `transitivity`

    equiv_trans{i} { code } (P₁ ==> Q₁) (P₂ ==> Q₂)     -- EC's `transitivity{i} { code } …`

On a relational judgment `c₁ ~ c₂ : P ==> Q`: through the middle code `code` (written over side
`i`'s variables, more declared with `var`), the judgments `c₁ ~ code : P₁ ==> Q₁` and
`code ~ c₂ : P₂ ==> Q₂`.  Goals in EC's order: the precondition splits through a middle state
(`∀ σ₁ σ₂, P σ₁ σ₂ → ∃ σ, P₁ σ₁ σ ∧ P₂ σ σ₂`), the postconditions compose
(`∀ τ₁ τ τ₂, Q₁ τ₁ τ → Q₂ τ τ₂ → Q τ₁ τ₂`), then the two judgments.  The rule is
`prhlStmt.trans` (`Logic/LoopTransform.lean`), by the gluing of couplings.

For procedures, `prhlProc_trans_ec`: the same through a middle procedure (EC's
`transitivity N (P₁ ==> Q₁) (P₂ ==> Q₂)`).
-/

namespace GaudisCrypt

/-- **EC's `transitivity{i} { code } (P₁ ==> Q₁) (P₂ ==> Q₂)`**, its goals in EC's order. -/
theorem prhlStmt_trans_ec {A B P₁ Q₁ P₂ Q₂ : ProgramState → ProgramState → Prop}
    {c₁ c₂ m : Stmt}
    (hP : ∀ σ₁ σ₂, A σ₁ σ₂ → ∃ σ, P₁ σ₁ σ ∧ P₂ σ σ₂)
    (hQ : ∀ τ₁ τ τ₂, Q₁ τ₁ τ → Q₂ τ τ₂ → B τ₁ τ₂)
    (h₁ : prhlStmt P₁ c₁ m Q₁) (h₂ : prhlStmt P₂ m c₂ Q₂) : prhlStmt A c₁ c₂ B :=
  prhlStmt_conseq (prhlStmt.trans h₁ h₂) (fun σ₁ σ₂ h => hP σ₁ σ₂ h)
    (fun τ₁ τ₂ ⟨τ, h₁, h₂⟩ => hQ τ₁ τ τ₂ h₁ h₂)

/-- **EC's `transitivity N (P₁ ==> Q₁) (P₂ ==> Q₂)`** on procedures, its goals in EC's order:
the middle procedure's argument and globals from the two sides', the postconditions composed,
the two judgments. -/
theorem prhlProc_trans_ec {sig₁ sig₂ sig : ProcedureSignature}
    {A : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop}
    {B : sig₁.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop}
    {P₁ : sig₁.ParamType → VariableAssignment → sig.ParamType → VariableAssignment → Prop}
    {Q₁ : sig₁.ret → VariableAssignment → sig.ret → VariableAssignment → Prop}
    {P₂ : sig.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop}
    {Q₂ : sig.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop}
    {p₁ : Procedure sig₁} {p₂ : Procedure sig₂} {n : Procedure sig}
    (hP : ∀ a₁ g₁ a₂ g₂, A a₁ g₁ a₂ g₂ → ∃ a g, P₁ a₁ g₁ a g ∧ P₂ a g a₂ g₂)
    (hQ : ∀ r₁ g₁ r g r₂ g₂, Q₁ r₁ g₁ r g → Q₂ r g r₂ g₂ → B r₁ g₁ r₂ g₂)
    (h₁ : prhlProc P₁ p₁ n Q₁) (h₂ : prhlProc P₂ n p₂ Q₂) : prhlProc A p₁ p₂ B := by
  intro a₁ a₂ g₁ g₂ hA
  obtain ⟨a, g, hP₁, hP₂⟩ := hP a₁ g₁ a₂ g₂ hA
  obtain ⟨μ, m1, m2, sat⟩ := ProgramDenotation.prhl2.trans (h₁ a₁ a) (h₂ a a₂) g₁ g₂
    ⟨g, hP₁, hP₂⟩
  exact ⟨μ, m1, m2, fun x hx => by
    obtain ⟨y, hy₁, hy₂⟩ := sat x hx
    exact hQ _ _ _ _ _ _ hy₁ hy₂⟩

/-- **EC's `transitivity{i} { code } (P₁ ==> Q₁) (P₂ ==> Q₂)`**: see the module docstring. -/
syntax (name := equivTrans) "equiv_trans" Judgment.judgmentSide " {"
    (ppIndent(ppLine ppGroup("var " proc_binder,* ";")))* gaudi_stmt* "}"
    " (" term " ==> " term ")" " (" term " ==> " term ")" : tactic

open Lean Meta Elab Tactic PRHLWp in
elab_rules (kind := equivTrans) : tactic
  | `(tactic| equiv_trans $s { $[var $locals:proc_binder,* ;]* $stmts:gaudi_stmt* }
        ($P₁ ==> $Q₁) ($P₂ ==> $Q₂)) => withMainContext do
    let side := (Judgment.sideOf? (some s)).getD 1
    let g ← getMainGoal
    let ty ← prhlGoal g "equiv_trans"
    let #[A, c₁, c₂, B] := ty.getAppArgs | unreachable!
    -- the middle code, over side `side`'s variables and those it declares
    let st := if side == 1 then c₁ else c₂
    let vars := (← ProgramSyntax.frameVars #[st] #[]).filter (·.nameable)
    let bs ← liftMacroM (RelSyntax.localsOf locals)
    let binds ← liftMacroM (bs.mapM fun (id, ty) => ProgramSyntax.varBinding id ty)
    let mut mstx ← liftMacroM (ProgramSyntax.wrapLetI binds (← `((GaudiProg[ $stmts* ] : Stmt))))
    for v in vars.reverse do
      let some slot := v.slots[0]? | continue
      mstx ← `(letI $(mkIdent (.mkSimple v.name)) := $(← Term.exprToSyntax slot); $mstx)
    let m ← Term.elabTermEnsuringType mstx (← inferType c₁)
    Term.synthesizeSyntheticMVarsNoPostponing
    let m ← instantiateMVars m
    -- the conditions, about `c₁` and `code`, and `code` and `c₂`
    let t₁ := mkAppN (mkConst ``prhlStmt) #[A, c₁, m, B]
    let t₂ := mkAppN (mkConst ``prhlStmt) #[A, m, c₂, B]
    let P₁e ← elabRelCond t₁ P₁
    let Q₁e ← elabRelCond t₁ Q₁
    let P₂e ← elabRelCond t₂ P₂
    let Q₂e ← elabRelCond t₂ Q₂
    let mS ← Term.exprToSyntax m
    let (p₁, q₁, p₂, q₂) := (← Term.exprToSyntax P₁e, ← Term.exprToSyntax Q₁e,
      ← Term.exprToSyntax P₂e, ← Term.exprToSyntax Q₂e)
    evalTactic (← `(tactic| refine prhlStmt_trans_ec (m := $mS) (P₁ := $p₁) (Q₁ := $q₁)
      (P₂ := $p₂) (Q₂ := $q₂) ?hP ?hQ ?h₁ ?h₂))
    -- the judgments' conditions and the side conditions readable
    let gs ← getGoals
    let gs ← gs.mapM fun g => do
      let t ← instantiateMVars (← g.getType)
      if t.isAppOfArity ``prhlStmt 4 then
        let g ← Judgment.simpArg g 0 relSimpDecls []
        Judgment.simpArg g 3 relSimpDecls []
      else
        let r ← Judgment.simpWithNames relSimpDecls [] t
        if r.expr == t then pure g else applySimpResultToTarget g t r
    setGoals gs

end GaudisCrypt
