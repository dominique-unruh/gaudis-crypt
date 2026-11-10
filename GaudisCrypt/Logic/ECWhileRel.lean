import GaudisCrypt.Logic.ECConseqFrame
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.PRHLWp

/-!
# EasyCrypt's two-sided `while I`

    equiv_while_raw (I)      -- EC's `while I` on two loops ending both sides' code

EC's `while I` on `c₁; while b₁ do s₁ ~ c₂; while b₂ do s₂ : P ==> Q` leaves two goals (checked on
opaque modules, `~/easycrypt-transfer-probes/while_if.ec`):

* the bodies: `s₁ ~ s₂ : I ∧ b₁{1} ∧ b₂{2} ==> I ∧ (b₁{1} ⇔ b₂{2})`;
* the code before: `c₁ ~ c₂ : P ==> (I ∧ (b₁{1} ⇔ b₂{2})) ∧ ∀ (modified variables),
  ¬b₁ ⇒ ¬b₂ ⇒ I ⇒ Q`: on exit only what the loops modify has changed.

Here the second is `∀ τ₁ τ₂, F₁ σ₁ τ₁ → F₂ σ₂ τ₂ → I τ₁ τ₂ → b₁ τ₁ = false → b₂ τ₂ = false →
Q τ₁ τ₂`, the frames `F₁`, `F₂` the variables `Q` reads that the loops keep (as for EC's
`conseq`, `Logic/ECConseqFrame.lean`).  The rule (`prhlStmt_seq_while_ec`) is derived from the
loop rule with the invariant `I ∧ b₁ = b₂` and EC's frame (`prhlStmt_conseq_frame`).

The older form, four goals (`body`, `guard`, `exit`, `hpre`) and no frame, is `equiv_while_raw`.
-/

namespace GaudisCrypt

/-- **EC's `while I`** on two loops (see the module docstring). -/
theorem prhlStmt_seq_while_ec {A Q I : ProgramState → ProgramState → Prop} {s₁ s₂ b₁ b₂ : Stmt}
    {c₁ c₂ : Getter Bool ProgramState} (F₁ F₂ : ProgramState → ProgramState → Prop)
    (hF₁ : ∀ σ, (programDenotation (.while c₁ b₁) σ).satisfies fun r => F₁ σ r.2)
    (hF₂ : ∀ σ, (programDenotation (.while c₂ b₂) σ).satisfies fun r => F₂ σ r.2)
    (hb : prhlStmt (fun σ₁ σ₂ => I σ₁ σ₂ ∧ c₁.get σ₁ = true ∧ c₂.get σ₂ = true) b₁ b₂
      fun σ₁ σ₂ => I σ₁ σ₂ ∧ c₁.get σ₁ = c₂.get σ₂)
    (hpre : prhlStmt A s₁ s₂ fun σ₁ σ₂ => (I σ₁ σ₂ ∧ c₁.get σ₁ = c₂.get σ₂) ∧
      ∀ τ₁ τ₂, F₁ σ₁ τ₁ → F₂ σ₂ τ₂ → I τ₁ τ₂ → c₁.get τ₁ = false → c₂.get τ₂ = false →
        Q τ₁ τ₂) :
    prhlStmt A (.seq s₁ (.while c₁ b₁)) (.seq s₂ (.while c₂ b₂)) Q := by
  refine prhlStmt_seq ?_ hpre
  -- the loops under `J := I ∧ c₁ = c₂`, EC's frame for the exit
  have hloop : prhlStmt (fun σ₁ σ₂ => I σ₁ σ₂ ∧ c₁.get σ₁ = c₂.get σ₂) (.while c₁ b₁)
      (.while c₂ b₂) fun σ₁ σ₂ => (I σ₁ σ₂ ∧ c₁.get σ₁ = c₂.get σ₂) ∧ c₁.get σ₁ = false :=
    prhlStmt_while (fun _ _ h => h.2)
      (prhlStmt_conseq hb (fun _ _ h => ⟨h.1.1, h.2, h.1.2 ▸ h.2⟩) fun _ _ h => h)
  refine prhlStmt_conseq_frame F₁ F₂ hF₁ hF₂ hloop (fun _ _ h => h.1) ?_
  rintro σ₁ σ₂ ⟨-, hK⟩ τ₁ τ₂ hf₁ hf₂ ⟨⟨hI, hc⟩, h1⟩
  exact hK τ₁ τ₂ hf₁ hf₂ hI h1 (hc ▸ h1)

end GaudisCrypt

open Lean Meta Elab Tactic GaudisCrypt GaudisCrypt.ECConseq PRHLWp in
/-- **EC's `while I`** on two loops ending the code of both sides: goals `body` and `hpre` (see
the module docstring; `prhlStmt_seq_while_ec`). -/
-- `I` a `term:max` (written in parentheses): a whole term would also read the one-sided
-- `equiv_while{i} (I) (V)` of `Logic/PRHLWp.lean`, as the set literal `{i}` applied
elab "equiv_while " I:term:max : tactic => withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_while"
  let g ← HoareSplit.hoareSplit 1 g
  replaceMainGoal [g]
  withMainContext do
    let ty ← prhlGoal g "equiv_while"
    let Ie ← elabRelCond ty I
    let #[_, c₁, c₂, Q] := ty.getAppArgs | unreachable!
    let loopOf (c : Lean.Expr) : MetaM Lean.Expr := do
      let c ← TacticMisc.openStmt (GaudisCrypt.stripLets (← instantiateMVars c))
      unless c.isAppOfArity ``StmtWithHoles.seq 3 do
        throwError "equiv_while: the code does not end with a loop:{indentExpr c}"
      let w ← TacticMisc.openStmt (c.getArg! 2)
      unless w.isAppOf ``StmtWithHoles.while do
        throwError "equiv_while: the last statement is not a loop:{indentExpr w}"
      return c.getArg! 2
    let (w₁, w₂) := (← loopOf c₁, ← loopOf c₂)
    -- EC's frame: the variables `Q` reads that the loops keep
    let (ls, gls) ← ECSim.varsOf #[Q]
    let xs := ls ++ (← gls.mapM fun x => mkAppM ``Lens.intoGlobal #[x])
    let rs ← ECConseqFrame.regionsOf #[Q]
    let (F₁, hF₁) ← ECConseqFrame.frameOf w₁ xs rs
    let (F₂, hF₂) ← ECConseqFrame.frameOf w₂ xs rs
    let (Is, F₁s, hF₁s, F₂s, hF₂s) := (← Term.exprToSyntax Ie, ← Term.exprToSyntax F₁,
      ← Term.exprToSyntax hF₁, ← Term.exprToSyntax F₂, ← Term.exprToSyntax hF₂)
    refineTagged (← `(prhlStmt_seq_while_ec (I := $Is) $F₁s $F₂s $hF₁s $hF₂s ?body ?hpre))
      [`body, `hpre]
