import GaudisCrypt.Logic.ECConseq

/-!
# Two more forms of EasyCrypt's `conseq`

## With a Hoare triple about one side

    equiv_conseq (: P ==> Q) _ (: P₂ ==> Q₂)     -- EC's `conseq (_ : P ==> Q) _ (_ : P₂ ==> Q₂)`

On a relational judgment `c₁ ~ c₂ : A ==> B`: what the right program guarantees on its own
(`hoare[ c₂ : P₂ ==> Q₂ ]`) is proved apart from the equivalence.  `P₂`, `Q₂` are about the right
memory and are written with its tag (`size §bs{2} = §n{2}`, where EC writes `size bs = n`): a
condition without tags could not name a variable that only the judgment's conditions read.

Goals in EC's order: `pre` (`A` implies `P` and `P₂`), `post` (EC's
`A => (frames) => Q => Q₂ => B`, as `equiv_conseq (: P ==> Q)` states it), `hoare` (the triple
about `c₂`), `judgment` (`c₁ ~ c₂ : P ==> Q`); `_` keeps a condition of the judgment.  The rule
is `prhlStmt_and_hoare_right` under `prhlStmt_conseq_frame`.

## `conseq H` on procedures, the precondition kept

    equiv_conseq_pre H                            -- EC's `conseq H` on `equiv[ f ~ g : P ==> Q ]`

`equiv_conseq H` states `post` as `Q' ⇒ Q` alone.  EC states it under the precondition
(`forall &1 &2, P => forall res…, Q' => Q`), which a proof may need (a fact about the arguments).
`equiv_conseq_pre H` leaves `pre` (`P ⇒ P'`) and that `post`: for the arguments and the initial
globals that satisfy `P`, and every result and final globals, `Q' ⇒ Q`.  The rule is
`prhlProc_conseq_pre`.
-/

namespace GaudisCrypt

open GaudisCrypt.Lib.RO.Instantiate in
/-- A relational judgment and a Hoare triple about its right program, together. -/
theorem prhlStmt_and_hoare_right {A B : ProgramState → ProgramState → Prop}
    {P₂ Q₂ : ProgramState → Prop} {c₁ c₂ : Stmt}
    (h : prhlStmt A c₁ c₂ B) (h₂ : hoareStmt P₂ c₂ Q₂) :
    prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ P₂ σ₂) c₁ c₂ (fun τ₁ τ₂ => B τ₁ τ₂ ∧ Q₂ τ₂) := by
  intro σ₁ σ₂ ⟨hA, hP⟩
  obtain ⟨μ, m1, m2, sat⟩ := h σ₁ σ₂ hA
  have h2 : μ.satisfies fun w => Q₂ w.2.2 :=
    coupling_satisfies_snd (B := fun r : Unit × ProgramState => Q₂ r.2)
      (by rw [m2]; exact h₂.satisfies hP)
  exact ⟨μ, m1, m2, fun w hw => ⟨sat w hw, h2 w hw⟩⟩

open Lean Meta Elab Tactic GaudisCrypt GaudisCrypt.ECConseq PRHLWp in
/-- **EC's `conseq (_ : P ==> Q) _ (_ : P₂ ==> Q₂)`** on a relational judgment about statements:
goals `pre`, `post`, `hoare` (the triple `P₂ ==> Q₂` about the right program), `judgment`
(`P ==> Q`).  `P₂`, `Q₂` are about the right memory, written with its tag (`§x{2}`). -/
elab "equiv_conseq" " (" ": " P:term " ==> " Q:term ")" " _" " (" ": " P₂:term " ==> " Q₂:term ")" :
    tactic => withMainContext do
  let g ← getMainGoal
  let ty ← prhlGoal g "equiv_conseq"
  let #[A, c₁, c₂, B] := ty.getAppArgs | unreachable!
  let Pe ← if isHole P then pure A else elabRelCond ty P
  let Qe ← if isHole Q then pure B else elabRelCond ty Q
  let PS := mkConst ``ProgramState
  -- a condition about the right memory, as a function of it
  let right (t : Term) : TacticM Lean.Expr := do
    let e ← elabRelCond ty t
    withLocalDeclD `σ₁ PS fun s₁ => withLocalDeclD `σ₂ PS fun s₂ => do
      let b := (mkApp2 e s₁ s₂).headBeta
      if b.containsFVar s₁.fvarId! then
        throwError "equiv_conseq: a condition of the right program's triple reads the left \
          memory:{indentExpr b}"
      mkLambdaFVars #[s₂] b
  let P₂e ← right P₂
  let Q₂e ← right Q₂
  let both (R S : Lean.Expr) : MetaM Lean.Expr :=
    withLocalDeclD `σ₁ PS fun s₁ => withLocalDeclD `σ₂ PS fun s₂ =>
      mkLambdaFVars #[s₁, s₂] (mkAnd (mkApp2 R s₁ s₂).headBeta (mkApp S s₂).headBeta)
  let A' ← both Pe P₂e
  let B' ← both Qe Q₂e
  -- EC's frame: what the code does not modify keeps its value from the precondition
  let (ls, gls) ← ECSim.varsOf #[B, B']
  let xs := ls ++ (← gls.mapM fun x => mkAppM ``Lens.intoGlobal #[x])
  let rs ← ECConseqFrame.regionsOf #[B, B']
  let (F₁, hF₁) ← ECConseqFrame.frameOf c₁ xs rs
  let (F₂, hF₂) ← ECConseqFrame.frameOf c₂ xs rs
  let (F₁s, hF₁s, F₂s, hF₂s) := (← Term.exprToSyntax F₁, ← Term.exprToSyntax hF₁,
    ← Term.exprToSyntax F₂, ← Term.exprToSyntax hF₂)
  let (A's, B's, Ps, Qs, P₂s, Q₂s) := (← Term.exprToSyntax A', ← Term.exprToSyntax B',
    ← Term.exprToSyntax Pe, ← Term.exprToSyntax Qe, ← Term.exprToSyntax P₂e,
    ← Term.exprToSyntax Q₂e)
  refineTagged (← `(prhlStmt_conseq_frame (A' := $A's) (B' := $B's) $F₁s $F₂s $hF₁s $hF₂s
      (prhlStmt_and_hoare_right (A := $Ps) (B := $Qs) (P₂ := $P₂s) (Q₂ := $Q₂s)
        ?judgment ?hoare) ?pre ?post)) [`pre, `post, `hoare, `judgment]

/-- A judgment about procedures from another one, the postcondition's implication under the
precondition (EC's `conseq H`: `forall &1 &2, P => forall res…, Q' => Q`). -/
theorem prhlProc_conseq_pre {sig₁ sig₂ : ProcedureSignature} {p₁ : Procedure sig₁}
    {p₂ : Procedure sig₂}
    {A A' : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop}
    {B B' : sig₁.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop}
    (h : prhlProc A' p₁ p₂ B') (hA : ∀ a₁ g₁ a₂ g₂, A a₁ g₁ a₂ g₂ → A' a₁ g₁ a₂ g₂)
    (hB : ∀ a₁ g₁ a₂ g₂, A a₁ g₁ a₂ g₂ →
      ∀ r₁ τ₁ r₂ τ₂, B' r₁ τ₁ r₂ τ₂ → B r₁ τ₁ r₂ τ₂) :
    prhlProc A p₁ p₂ B := by
  intro a₁ a₂ g₁ g₂ hAg
  obtain ⟨μ, m1, m2, sat⟩ := h a₁ a₂ g₁ g₂ (hA _ _ _ _ hAg)
  exact ⟨μ, m1, m2, fun x hx => hB _ _ _ _ hAg _ _ _ _ (sat x hx)⟩

open Lean Meta Elab Tactic GaudisCrypt GaudisCrypt.ECConseq in
/-- **EC's `conseq H`** on a relational judgment about procedures, `post` under the precondition
as EC states it: goals `pre` (the goal's precondition implies `H`'s) and `post` (for arguments
and initial globals satisfying the goal's precondition, `H`'s postcondition implies the
goal's). -/
elab "equiv_conseq_pre " H:term:max : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOfArity ``prhlProc 6 do
    throwError "equiv_conseq_pre: not a relational judgment about procedures"
  refineTagged (← `(prhlProc_conseq_pre $H ?pre ?post)) [`pre, `post]

end GaudisCrypt
