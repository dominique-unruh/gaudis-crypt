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

/-- **EC's one-sided `while{2} I V`**: the loop ending the right side, run on that side only.
Its exit goes into the precondition goal under EC's frame `F` of the loop (what it keeps): the
code before establishes `I` and, for every final state `τ` of the loop that `F` allows, `I` and
a false guard give `B`. -/
theorem prhlStmt_seq_while_right_ec {A B : ProgramState → ProgramState → Prop} {s₁ s₂ body : Stmt}
    {c : Getter Bool ProgramState} (F : ProgramState → ProgramState → Prop)
    (hF : ∀ σ, (programDenotation (.while c body) σ).satisfies fun r => F σ r.2)
    (I : ProgramState → ProgramState → Prop) (V : ProgramState → ProgramState → ℕ)
    (hll : ∀ σ₁ σ, I σ₁ σ → c.get σ = true → body.ewp (fun _ => 1) σ = 1)
    (hvar : ∀ σ₁ k, hoareStmt (fun σ => I σ₁ σ ∧ c.get σ = true ∧ V σ₁ σ = k) body
      (fun τ => I σ₁ τ ∧ V σ₁ τ < k))
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ =>
      I σ₁ σ₂ ∧ ∀ τ, F σ₂ τ → I σ₁ τ → c.get τ = false → B σ₁ τ) :
    prhlStmt A s₁ (.seq s₂ (.while c body)) B := by
  refine prhlStmt_seq_right (prhlStmt_post h fun σ₁ σ₂ hI => ⟨?_, ?_⟩)
  · exact Stmt.ewp_while_eq_one (I σ₁) (V σ₁) (hll σ₁) (hvar σ₁) σ₂ hI.1
  · have hloop : hoareStmt (I σ₁) (.while c body) (fun τ => I σ₁ τ ∧ c.get τ = false) :=
      hoare_while (I σ₁)
        (fun σ hσ => hoare_post (hvar σ₁ (V σ₁ σ)) (fun τ hτ => hτ.1) σ ⟨hσ.1, hσ.2, rfl⟩)
        (fun τ h₁ h₂ => ⟨h₁, h₂⟩)
    have h₁ := hoareStmt.satisfies hloop hI.1
    intro r hr
    exact hI.2 r.2 (hF σ₂ r hr) (h₁ r hr).1 (h₁ r hr).2

/-- **EC's one-sided `while{1} I V`**: `prhlStmt_seq_while_right_ec` on the left side. -/
theorem prhlStmt_seq_while_left_ec {A B : ProgramState → ProgramState → Prop} {s₁ s₂ body : Stmt}
    {c : Getter Bool ProgramState} (F : ProgramState → ProgramState → Prop)
    (hF : ∀ σ, (programDenotation (.while c body) σ).satisfies fun r => F σ r.2)
    (I : ProgramState → ProgramState → Prop) (V : ProgramState → ProgramState → ℕ)
    (hll : ∀ σ₂ σ, I σ σ₂ → c.get σ = true → body.ewp (fun _ => 1) σ = 1)
    (hvar : ∀ σ₂ k, hoareStmt (fun σ => I σ σ₂ ∧ c.get σ = true ∧ V σ σ₂ = k) body
      (fun τ => I τ σ₂ ∧ V τ σ₂ < k))
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ =>
      I σ₁ σ₂ ∧ ∀ τ, F σ₁ τ → I τ σ₂ → c.get τ = false → B τ σ₂) :
    prhlStmt A (.seq s₁ (.while c body)) s₂ B :=
  (prhlStmt_seq_while_right_ec (A := fun σ₂ σ₁ => A σ₁ σ₂) (B := fun σ₂ σ₁ => B σ₁ σ₂) F hF
    (fun σ₂ σ₁ => I σ₁ σ₂) (fun σ₂ σ₁ => V σ₁ σ₂) hll hvar h.symm).symm

end GaudisCrypt

open Lean Meta Elab Tactic GaudisCrypt GaudisCrypt.ECConseq PRHLWp in
/-- **EC's one-sided `while{i} I V`**: the last statement of side `i` is a loop, run on that side
only, with the invariant `I` and the variant `V : ℕ` (relational).  Goals: `lossless` (the body
terminates under `I` and the guard), `variant` (the body keeps `I` and decreases `V`, a Hoare
triple for each state of the other side and each value of `V`), then the code before the loop:
`I`, and for every final state of the loop that keeps what it does not write (EC's frame, the
variables the postcondition reads), `I` and a false guard give the postcondition
(`prhlStmt_seq_while_left_ec`/`_right_ec`).  The older form, with a separate `exit` goal and no
frame, is `equiv_while_noframe{i}`. -/
elab "equiv_while" s:Judgment.judgmentSide ppSpace I:term:max ppSpace V:term:max : tactic =>
    withMainContext do
  let g ← getMainGoal
  let _ ← prhlGoal g "equiv_while"
  let side := (Judgment.sideOf? (some s)).getD 1
  let g ← HoareSplit.hoareSplit 1 g (some side)
  replaceMainGoal [g]
  withMainContext do
    let ty ← prhlGoal g "equiv_while"
    let Ie ← elabRelCond ty I
    let Ve ← elabRelTerm ty V (mkConst ``Nat)
    let c := ty.getArg! side
    let B := ty.getArg! 3
    let c ← TacticMisc.openStmt (GaudisCrypt.stripLets (← instantiateMVars c))
    unless c.isAppOfArity ``StmtWithHoles.seq 3 do
      throwError "equiv_while: the code of side {side} does not end with a loop:{indentExpr c}"
    let w := c.getArg! 2
    unless (← TacticMisc.openStmt w).isAppOf ``StmtWithHoles.while do
      throwError "equiv_while: the last statement of side {side} is not a loop:{indentExpr w}"
    -- EC's frame: the variables the postcondition reads that the loop keeps
    let (ls, gls) ← ECSim.varsOf #[B]
    let xs := ls ++ (← gls.mapM fun x => mkAppM ``Lens.intoGlobal #[x])
    let rs ← ECConseqFrame.regionsOf #[B]
    let (F, hF) ← ECConseqFrame.frameOf w xs rs
    let lem := if side == 1 then ``prhlStmt_seq_while_left_ec else ``prhlStmt_seq_while_right_ec
    let gs ← try applyLemma lem g #[(`F, F), (`hF, hF), (`I, Ie), (`V, Ve)]
      catch e => throwError "equiv_while: {e.toMessageData}"
    let #[gll, gvar, gPre] := gs
      | throwError "equiv_while: `{lem}` left {gs.size} goals"
    for (m, tag) in [(gll, `lossless), (gvar, `variant), (gPre, `hpre)] do
      m.setTag tag
    replaceMainGoal [gll, gvar, gPre]

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
