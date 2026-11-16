import GaudisCrypt.Logic.ECConseq

/-!
# EasyCrypt's `while I` on a Hoare triple

    hoare_while (I)

EC's `while I` on `hoare[ c; while b do s : P ==> Q ]` leaves two goals:

* the body: `hoare[ s : I ∧ b ==> I ]`;
* the code before: `hoare[ c : P ==> I ∧ ∀ (modified variables), I ⇒ ¬b ⇒ Q ]`: on exit only
  what the loop modifies has changed, so what the precondition says of the other variables is
  still there.

Here the second is `I σ ∧ ∀ τ, F σ τ → I τ → b τ = false → Q τ`, the frame `F` the variables the
conditions read that the loop keeps (as for EC's `conseq`, `Logic/ECConseqFrame.lean`; the rule
is `hoareStmt_seq_while_ec`).

The older form, three goals (`body`, `exit`, the code before with postcondition `I`) and no
frame, is `hoare_while_raw` (`Logic/HoareWp.lean`).
-/

namespace GaudisCrypt

open Lean Meta Elab Tactic GaudisCrypt GaudisCrypt.ECConseq in
/-- **EC's `while I`** on a Hoare triple whose code ends with a loop: goals `body` and `hpre`
(see the module docstring).  `I` is written like a condition of a `hoare[ ]` triple. -/
elab "hoare_while " I:term : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``hoareStmt 3 do
    throwError "hoare_while: expected a goal `hoareStmt A s B`, got{indentExpr ty}"
  let Ie ← elabCond ty 1 I
  let g ← HoareSplit.hoareSplit 1 g
  replaceMainGoal [g]
  withMainContext do
    let ty ← instantiateMVars (← g.getType)
    let #[A, c, Q] := ty.getAppArgs | unreachable!
    let c ← TacticMisc.openStmt (GaudisCrypt.stripLets (← instantiateMVars c))
    unless c.isAppOfArity ``StmtWithHoles.seq 3 do
      throwError "hoare_while: the code does not end with a loop:{indentExpr c}"
    let w := c.getArg! 2
    unless (← TacticMisc.openStmt w).isAppOf ``StmtWithHoles.while do
      throwError "hoare_while: the last statement is not a loop:{indentExpr w}"
    -- EC's frame: the variables the conditions read that the loop keeps
    let (ls, gls) ← ECSim.varsOf #[A, Ie, Q]
    let xs := ls ++ (← gls.mapM fun x => mkAppM ``Lens.intoGlobal #[x])
    let rs ← ECConseqFrame.regionsOf #[A, Ie, Q]
    let (F, hF) ← ECConseqFrame.frameOf w xs rs
    let (Is, Fs, hFs) := (← Term.exprToSyntax Ie, ← Term.exprToSyntax F, ← Term.exprToSyntax hF)
    refineTagged (← `(hoareStmt_seq_while_ec (I := $Is) $Fs $hFs ?body ?hpre)) [`body, `hpre]

end GaudisCrypt
