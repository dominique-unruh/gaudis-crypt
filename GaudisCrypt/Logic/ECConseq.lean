import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Lib.EC.Mu
import GaudisCrypt.Logic.ECConseqFrame

/-!
# EasyCrypt's `hoare` and `conseq`

    phoare_hoare                  -- EC's `hoare`: `phoare[c : P ==> Q] ≤ r` (or `= 0`) from
                                  --   `hoare[c : P ==> !Q]`
    stmt_exists* e                -- EC's `exists* e`: `phoare[c : P ∧ e = h ==> Q]` for every
                                  --   `h` (then `intro h`, EC's `elim* => h`)
    hoare_conseq (: P ==> Q)      -- EC's `conseq (: P ==> Q)` on a Hoare triple (`_` keeps one)
    phoare_conseq (: P ==> Q)     -- … on an upper bound `phoare[ … ] ≤ r`
    equiv_conseq (: P ==> Q)      -- … on a relational judgment (`§x{1}`, `§x{2}`)

`conseq`'s goals, as EC's: the implications, then the judgment with the new conditions.  For an
upper bound, the event may only grow: the old event implies the new one.
-/

namespace GaudisCrypt

variable {A A' : ProgramState → Prop} {c : Stmt}

/-- A run after which `g` vanishes: its expectation of `g` is `0`. -/
theorem Stmt.ewp_eq_zero_of_hoare {g : ProgramState → ENNReal}
    (h : hoareStmt A c fun σ => g σ = 0) {σ : ProgramState} (hA : A σ) : c.ewp g σ = 0 := by
  simp only [Stmt.ewp, ProgramDenotation.wp]
  rw [SubProbability.expected_congr_satisfies (h.satisfies hA) (G := fun _ => 0)
    (fun u hu => hu)]
  exact SubProbability.expected_eq_zero_of_support fun _ _ => rfl

/-- **EC's `hoare`** on an upper bound: `g` vanishing after the run bounds its expectation by
anything. -/
theorem phoareStmt_le_of_hoare {g r : ProgramState → ENNReal}
    (h : hoareStmt A c fun σ => g σ = 0) : phoareStmt A c g (· ≤ ·) r :=
  fun _ hA => (Stmt.ewp_eq_zero_of_hoare h hA).trans_le bot_le

/-- **EC's `hoare`** on `phoare[ … ] = 0`. -/
theorem phoareStmt_eq_zero_of_hoare {g : ProgramState → ENNReal}
    (h : hoareStmt A c fun σ => g σ = 0) : phoareStmt A c g Eq fun _ => 0 :=
  fun _ hA => Stmt.ewp_eq_zero_of_hoare h hA

/-- **EC's `exists* e`** on a `phoare` judgment: the judgment for every value `h` of `e` at the
start, the precondition with `e = h`. -/
theorem phoareStmt_exists {α : Type} (e : ProgramState → α) {g r : ProgramState → ENNReal}
    {ρ : ENNReal → ENNReal → Prop} (h : ∀ v, phoareStmt (fun σ => A σ ∧ e σ = v) c g ρ r) :
    phoareStmt A c g ρ r :=
  fun σ hA => h (e σ) σ ⟨hA, rfl⟩

/-- **EC's `exists* e`** on a relational judgment: `e` reads both states. -/
theorem prhlStmt_exists {α : Type} {A B : ProgramState → ProgramState → Prop} {c₁ c₂ : Stmt}
    (e : ProgramState → ProgramState → α)
    (h : ∀ v, prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ e σ₁ σ₂ = v) c₁ c₂ B) : prhlStmt A c₁ c₂ B :=
  prhlStmt_pre (prhlStmt_exists_pre h) fun σ₁ σ₂ hA => ⟨e σ₁ σ₂, hA, rfl⟩

/-- **EC's `exists* e`** on a procedure judgment: `e` reads both sides' arguments and globals. -/
theorem prhlProc_exists {α : Type} {sig₁ sig₂ : ProcedureSignature} {p₁ : Procedure sig₁}
    {p₂ : Procedure sig₂}
    {A : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop}
    {B : sig₁.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop}
    (e : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → α)
    (h : ∀ v, prhlProc (fun a₁ g₁ a₂ g₂ => A a₁ g₁ a₂ g₂ ∧ e a₁ g₁ a₂ g₂ = v) p₁ p₂ B) :
    prhlProc A p₁ p₂ B :=
  fun a₁ a₂ g₁ g₂ hA => h (e a₁ g₁ a₂ g₂) a₁ a₂ g₁ g₂ ⟨hA, rfl⟩

/-- A marker: `equiv_exists*` on a procedure judgment reads `e` off the precondition
`existsMark e` that `equiv[ p₁ ~ p₂ : … ]` elaborates. -/
def ECConseq.existsMark {α : Sort*} (_ : α) : Prop := True

/-- **EC's `exists* e`** on a Hoare triple. -/
theorem hoareStmt_exists {α : Type} (e : ProgramState → α) {B : ProgramState → Prop}
    (h : ∀ v, hoareStmt (fun σ => A σ ∧ e σ = v) c B) : hoareStmt A c B :=
  fun σ hA => h (e σ) σ ⟨hA, rfl⟩

end GaudisCrypt

open Lean Elab Tactic in
/-- **EC's `hoare`** on a `phoare` goal with an upper bound, or the bound `0`: the Hoare triple
that its event fails (`phoareStmt_le_of_hoare`, `phoareStmt_eq_zero_of_hoare`). -/
elab "phoare_hoare" : tactic => do
  evalTactic (← `(tactic| first
    | refine GaudisCrypt.phoareStmt_le_of_hoare ?_
    | refine GaudisCrypt.phoareStmt_eq_zero_of_hoare ?_))
  -- an event's indicator vanishing: the event failing
  evalTactic (← `(tactic| try simp only [GaudisCrypt.indicatorE_eq_zero_iff]))

namespace GaudisCrypt.ECConseq

open Lean Meta Elab Tactic PRHLWp

/-- A condition on one state, written as the judgment's (`§x`, the code's variables by name). -/
def elabCond (ty : Lean.Expr) (stmtIdx : Nat) (P : Term) : TacticM Lean.Expr := do
  let vars := (← ProgramSyntax.frameVars #[ty.getArg! 0, ty.getArg! stmtIdx] #[]).filter
    (·.printable)
  let mut stx ← `((GaudiExpr[ $P ] : Getter Prop ProgramState).get)
  for v in vars.reverse do
    let some slot := v.slots[0]? | continue
    stx ← `(letI $(mkIdent (.mkSimple v.name)) := $(← Term.exprToSyntax slot); $stx)
  let e ← Term.elabTermEnsuringType stx (← mkArrow (mkConst ``ProgramState) (mkSort 0))
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- `_`: the condition kept. -/
def isHole (t : Term) : Bool := t.raw.isOfKind ``Lean.Parser.Term.hole

/-- Run `refine stx`; its goals tagged, the given ones in EC's order (then any others). -/
def refineTagged (stx : TSyntax `term) (order : List Name) : TacticM Unit := do
  evalTactic (← `(tactic| refine $stx))
  let gs ← getGoals
  for g in gs do g.setTag (← g.getTag).eraseMacroScopes
  let mut out := []
  for t in order do
    if let some g ← gs.findM? (fun g => return (← g.getTag) == t) then out := out ++ [g]
  setGoals (out ++ gs.filter (!out.contains ·))

end GaudisCrypt.ECConseq

open Lean Meta Elab Tactic GaudisCrypt GaudisCrypt.ECConseq in
/-- **EC's `conseq (: P ==> Q)`** on a Hoare triple: goals `pre` (the precondition implies `P`),
`post` (`Q` implies the postcondition), then the triple with `P`, `Q`; `_` keeps a condition. -/
elab "hoare_conseq" " (" ": " P:term " ==> " Q:term ")" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOf ``hoareStmt do throwError "hoare_conseq: not a Hoare triple"
  let Pe ← if isHole P then pure (ty.getArg! 0) else elabCond ty 1 P
  let Qe ← if isHole Q then pure (ty.getArg! 2) else elabCond ty 1 Q
  let (Ps, Qs) := (← Term.exprToSyntax Pe, ← Term.exprToSyntax Qe)
  let pre ← if isHole P then `(fun _ h => h) else `(?pre)
  let post ← if isHole Q then `(fun _ h => h) else `(?post)
  refineTagged (← `(hoare_post (B' := $Qs) (hoare_pre (A' := $Ps) ?judgment $pre) $post))
    [`pre, `post, `judgment]

open Lean Meta Elab Tactic GaudisCrypt GaudisCrypt.ECConseq in
/-- **EC's `conseq (: P ==> Q)`** on an upper bound `phoare[ c : A ==> E ] ≤ r`: goals `pre`,
`post` (the old event's expectation below `Q`'s indicator: for an event, `E` implies `Q`), then
the judgment with `P`, `Q`; `_` keeps a condition. -/
elab "phoare_conseq" " (" ": " P:term " ==> " Q:term ")" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOf ``phoareStmt do throwError "phoare_conseq: not a `phoare` judgment"
  let Pe ← if isHole P then pure (ty.getArg! 0) else elabCond ty 1 P
  let Ps ← Term.exprToSyntax Pe
  let pre ← if isHole P then `(fun _ h => h) else `(?pre)
  if isHole Q then
    refineTagged (← `(phoareStmt_pre (A' := $Ps) ?judgment $pre)) [`pre, `judgment]
  else
    let Qs ← Term.exprToSyntax (← elabCond ty 1 Q)
    refineTagged (← `(phoareStmt_le_of_le (g' := fun σ => indicatorE ($Qs σ))
        (phoareStmt_pre (A' := $Ps) ?judgment $pre) ?post)) [`pre, `post, `judgment]
    -- an event's indicator below another's: the implication
    for g in ← getGoals do
      if (← g.getTag) == `post then
        let s ← saveState
        try
          let [g'] ← evalTacticAt (← `(tactic| exact fun σ => indicatorE_le_of_imp (?h σ))) g
            | throwError "no"
          g'.setTag `post
          replaceMainGoal ((← getGoals).map fun x => if x == g then g' else x)
        catch _ => s.restore

open Lean Meta Elab Tactic GaudisCrypt GaudisCrypt.ECConseq PRHLWp in
/-- **EC's `conseq (: P ==> Q)`** on a relational judgment (`§x{1}`, `§x{2}`): goals `pre`,
`post`, then the judgment with `P`, `Q`; `_` keeps a condition.  On statements, `post` is EC's
`P => (frames) => Q' => Q`: the variables `Q` reads that the code does not modify keep their
values from the start (`prhlStmt_conseq_frame`). -/
elab "equiv_conseq" " (" ": " P:term " ==> " Q:term ")" : tactic => withMainContext do
  let g ← getMainGoal
  let ty0 ← instantiateMVars (← g.getType)
  if ty0.isAppOfArity ``prhlProc 6 then
    -- about two procedures: the conditions as `equiv[ p₁ ~ p₂ : P ==> Q ]` reads them (the
    -- parameters, `res`)
    let (p₁, p₂) ← (do return (← Term.exprToSyntax (ty0.getArg! 3),
      ← Term.exprToSyntax (ty0.getArg! 4)) : TermElabM _)
    let P' ← if isHole P then `(True) else pure P
    let Q' ← if isHole Q then `(True) else pure Q
    let j ← Term.elabTerm (← `(equiv[ $p₁ ~ $p₂ : $P' ==> $Q' ])) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let j ← instantiateMVars j
    let Pe := if isHole P then ty0.getArg! 2 else j.getArg! 2
    let Qe := if isHole Q then ty0.getArg! 5 else j.getArg! 5
    let (Ps, Qs) := (← Term.exprToSyntax Pe, ← Term.exprToSyntax Qe)
    let pre ← if isHole P then `(fun _ _ _ _ h => h) else `(?pre)
    let post ← if isHole Q then `(fun _ _ _ _ h => h) else `(?post)
    refineTagged (← `(prhlProc_conseq (A' := $Ps) (B' := $Qs) ?judgment $pre $post))
      [`pre, `post, `judgment]
    return
  let ty ← prhlGoal g "equiv_conseq"
  let Pe ← if isHole P then pure (ty.getArg! 0) else elabRelCond ty P
  let Qe ← if isHole Q then pure (ty.getArg! 3) else elabRelCond ty Q
  let (Ps, Qs) := (← Term.exprToSyntax Pe, ← Term.exprToSyntax Qe)
  let pre ← if isHole P then `(fun _ _ h => h) else `(?pre)
  if isHole Q then
    refineTagged (← `(prhlStmt_conseq (A' := $Ps) (B' := $Qs) ?judgment $pre (fun _ _ h => h)))
      [`pre, `post, `judgment]
    return
  -- EC's frame: what the code does not modify keeps its value from the precondition
  -- (`Logic/ECConseqFrame.lean`)
  let #[_, c₁, c₂, B] := ty.getAppArgs | unreachable!
  -- (those `Q` and the new postcondition read: EC's frame covers every unmodified variable)
  let (ls, gls) ← ECSim.varsOf #[B, Qe]
  let xs := ls ++ (← gls.mapM fun x => mkAppM ``Lens.intoGlobal #[x])
  let rs ← ECConseqFrame.regionsOf #[B, Qe]
  let (F₁, hF₁) ← ECConseqFrame.frameOf c₁ xs rs
  let (F₂, hF₂) ← ECConseqFrame.frameOf c₂ xs rs
  let (F₁s, hF₁s, F₂s, hF₂s) := (← Term.exprToSyntax F₁, ← Term.exprToSyntax hF₁,
    ← Term.exprToSyntax F₂, ← Term.exprToSyntax hF₂)
  refineTagged (← `(prhlStmt_conseq_frame (A' := $Ps) (B' := $Qs) $F₁s $F₂s $hF₁s $hF₂s
      ?judgment $pre ?post)) [`pre, `post, `judgment]

open Lean Meta Elab Tactic GaudisCrypt GaudisCrypt.ECConseq in
/-- **EC's `exists* e`** on a `phoare` judgment or a Hoare triple: `e` an expression of the state
(`§Preimage2.hash`); the goal for every value of it, `∀ v, … : A ∧ e = v …` (EC's `elim* => h` is
`intro h`). -/
elab "stmt_exists" "*" e:term : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let lem ← if ty.isAppOf ``phoareStmt then pure ``phoareStmt_exists
    else if ty.isAppOf ``hoareStmt then pure ``hoareStmt_exists
    else throwError "stmt_exists*: not a `phoare` judgment or a Hoare triple"
  -- `e` as a function of the state, as a condition is (`GaudiExpr`, the code's variables)
  let vars := (← ProgramSyntax.frameVars #[ty.getArg! 0, ty.getArg! 1] #[]).filter (·.printable)
  let mut stx ← `((GaudiExpr[ $e ] : Getter _ ProgramState).get)
  for v in vars.reverse do
    let some slot := v.slots[0]? | continue
    stx ← `(letI $(mkIdent (.mkSimple v.name)) := $(← Term.exprToSyntax slot); $stx)
  let ee ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  let es ← Term.exprToSyntax (← instantiateMVars ee)
  evalTactic (← `(tactic| refine $(mkIdent lem) $es ?_))

open Lean Meta Elab Tactic GaudisCrypt PRHLWp in
/-- **EC's `exists* e₁, …, eₙ`** on a relational judgment: the `eᵢ` relational terms (`§x{1}`,
`§y{2}`); the goal for all their values, `∀ v₁ … vₙ, equiv[ (A ∧ e₁ = v₁) ∧ … ∧ eₙ = vₙ ==> … ]`
(EC's `elim* => v₁ … vₙ` is `intro v₁ … vₙ`). -/
elab "equiv_exists" "*" ts:term,+ : tactic => do
  let mut vs : Array FVarId := #[]
  for t in ts.getElems do
    withMainContext do
      let ty0 ← instantiateMVars (← getMainTarget)
      if ty0.isAppOfArity ``prhlProc 6 then
        -- about two procedures: `e` as `equiv[ p₁ ~ p₂ : … ]` reads a condition (the
        -- parameters, `§x{2}`), as a function of the arguments and globals
        let (p₁, p₂) := (← Term.exprToSyntax (ty0.getArg! 3), ← Term.exprToSyntax (ty0.getArg! 4))
        let j ← Term.elabTerm
          (← `(equiv[ $p₁ ~ $p₂ : GaudisCrypt.ECConseq.existsMark ($t) ==> True ])) none
        Term.synthesizeSyntheticMVarsNoPostponing
        let j ← instantiateMVars j
        let e ← lambdaTelescope (j.getArg! 2) fun xs body => do
          let body ← zetaReduce body
          let body := body.headBeta
          unless body.isAppOfArity ``ECConseq.existsMark 2 do
            throwError "equiv_exists*: could not read{indentExpr body}"
          let e ← Core.betaReduce body.appArg!
          let e ← Meta.transform e (post := fun t => do
            -- `(Getter.mk f).get σ` is `f σ`
            if t.isAppOfArity ``Getter.get 4 && (t.getArg! 2).isAppOfArity ``Getter.mk 3 then
              return .done ((t.getArg! 2).getArg! 2 |>.beta #[t.getArg! 3])
            return .continue)
          mkLambdaFVars xs e
        let es ← Term.exprToSyntax e
        evalTactic (← `(tactic| refine prhlProc_exists $es ?_))
        return
      let ty ← prhlGoal (← getMainGoal) "equiv_exists*"
      let e ← elabRelTerm ty t (← mkFreshTypeMVar)
      let es ← Term.exprToSyntax (← instantiateMVars e)
      evalTactic (← `(tactic| refine prhlStmt_exists $es ?_))
    let (v, g) ← (← getMainGoal).intro `v
    vs := vs.push v
    replaceMainGoal [g]
  let (_, g) ← (← getMainGoal).revert vs (preserveOrder := true)
  replaceMainGoal [g]

open Lean Meta Elab Tactic GaudisCrypt GaudisCrypt.ECConseq in
/-- **EC's `conseq H`** on a relational judgment: the judgment `H` (about the same statements or
procedures) for the goal's; goals `pre` (the goal's precondition implies `H`'s) and `post`
(`H`'s postcondition implies the goal's). -/
elab "equiv_conseq " H:term:max : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  if ty.isAppOfArity ``prhlProc 6 then
    refineTagged (← `(prhlProc_conseq $H ?pre ?post)) [`pre, `post]
  else if ty.isAppOfArity ``prhlStmt 4 then
    refineTagged (← `(prhlStmt_conseq $H ?pre ?post)) [`pre, `post]
  else throwError "equiv_conseq: not a relational judgment"
