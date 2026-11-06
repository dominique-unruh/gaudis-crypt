import GaudisCrypt.Logic.PRHLStmt
import GaudisCrypt.Logic.PHoare

/-!
# EasyCrypt's `byequiv` and `byphoare`, on probabilities

A goal about probabilities, as `Pr[ M (a) @ &m : E ]` writes them (`Syntax/PrSyntax.lean`: the
real `(Procedure.Pr p a m E : ℝ)`), is turned into a judgment:

* `byequiv` — `Pr[ p₁ … ] = Pr[ p₂ … ]` (or `≤`) from `equiv[ p₁ ~ p₂ : P ==> Q ]`, with the
  precondition holding of the two runs' arguments and memories and `Q` relating the events
  (`E₁ ↔ E₂`, for `≤` `E₁ → E₂`).  Without a term, the judgment is the new goal with EC's
  defaults: `P` is `={arg, glob}` (the arguments and the globals agree) when both sides run on the
  same arguments from the same memory, else `arg{i} = aᵢ ∧ glob{i} = mᵢ`; `Q` relates the events.
  With a term `h` (a judgment), the side conditions are the goals.
* `byphoare` — `Pr[ p … ] ≤ x` (or `=`, `≥`) from `phoare[ p : P ==> E ] ≤ r` (`=`, `≥`), the
  bound `r` read at the run's arguments and memory against `ENNReal.ofReal x` (EC's bounds are
  reals).  Without a term, the judgment is the new goal, with the precondition
  `arg = a ∧ glob = m` and the bound `ENNReal.ofReal x`.

The side conditions left are tried by `rfl`/`trivial`/`simp_all`; `0 ≤ x` (a bound below a
probability is non-negative) by `positivity`.
-/

namespace GaudisCrypt

section Rules

variable {sig : ProcedureSignature} {A : sig.ParamType → VariableAssignment → Prop}
  {p : Procedure sig} {E : sig.ret → VariableAssignment → Prop}
  {r : sig.ParamType → VariableAssignment → ENNReal} {a : sig.ParamType}
  {σ : VariableAssignment} {x : ℝ}

/-- `byphoare` for `≤`. -/
theorem Procedure.toReal_Pr_le_of_phoareProc
    (h : phoareProc A p (fun v g => indicatorE (E v g)) (· ≤ ·) r) (hA : A a σ)
    (hr : r a σ ≤ ENNReal.ofReal x) (hx : 0 ≤ x) : (p.Pr a σ E : ℝ) ≤ x := by
  have h1 : ((p.Pr a σ E : NNReal) : ENNReal) ≤ ENNReal.ofReal x :=
    (Procedure.Pr_of_phoareProc h hA).trans hr
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rwa [ENNReal.coe_toReal, ENNReal.toReal_ofReal hx] at this

/-- `byphoare` for `≥`. -/
theorem Procedure.le_toReal_Pr_of_phoareProc
    (h : phoareProc A p (fun v g => indicatorE (E v g)) (· ≥ ·) r) (hA : A a σ)
    (hr : ENNReal.ofReal x ≤ r a σ) : x ≤ (p.Pr a σ E : ℝ) := by
  have h1 : ENNReal.ofReal x ≤ ((p.Pr a σ E : NNReal) : ENNReal) :=
    hr.trans (Procedure.Pr_of_phoareProc h hA)
  have := (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).mp h1
  rwa [ENNReal.coe_toReal] at this

/-- `byphoare` for `=`. -/
theorem Procedure.toReal_Pr_eq_of_phoareProc
    (h : phoareProc A p (fun v g => indicatorE (E v g)) Eq r) (hA : A a σ)
    (hr : r a σ = ENNReal.ofReal x) (hx : 0 ≤ x) : (p.Pr a σ E : ℝ) = x := by
  have h1 : ((p.Pr a σ E : NNReal) : ENNReal) = ENNReal.ofReal x :=
    (Procedure.Pr_of_phoareProc h hA).trans hr
  have := congrArg ENNReal.toReal h1
  rwa [ENNReal.coe_toReal, ENNReal.toReal_ofReal hx] at this

end Rules

section Rules2

variable {sig₁ sig₂ : ProcedureSignature}
  {A : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop}
  {p₁ : Procedure sig₁} {p₂ : Procedure sig₂}
  {B : sig₁.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop}

/-- `byequiv` for `=`, on real probabilities. -/
theorem Procedure.toReal_Pr_eq_of_prhlProc (h : prhlProc A p₁ p₂ B)
    {E₁ : sig₁.ret → VariableAssignment → Prop} {E₂ : sig₂.ret → VariableAssignment → Prop}
    (hE : ∀ r₁ g₁ r₂ g₂, B r₁ g₁ r₂ g₂ → (E₁ r₁ g₁ ↔ E₂ r₂ g₂))
    {a₁ : sig₁.ParamType} {a₂ : sig₂.ParamType} {σ₁ σ₂ : VariableAssignment}
    (hA : A a₁ σ₁ a₂ σ₂) : (p₁.Pr a₁ σ₁ E₁ : ℝ) = p₂.Pr a₂ σ₂ E₂ :=
  congrArg NNReal.toReal (Procedure.Pr_eq_of_prhlProc h hE hA)

/-- `byequiv` for `≤`, on real probabilities. -/
theorem Procedure.toReal_Pr_le_of_prhlProc (h : prhlProc A p₁ p₂ B)
    {E₁ : sig₁.ret → VariableAssignment → Prop} {E₂ : sig₂.ret → VariableAssignment → Prop}
    (hE : ∀ r₁ g₁ r₂ g₂, B r₁ g₁ r₂ g₂ → E₁ r₁ g₁ → E₂ r₂ g₂)
    {a₁ : sig₁.ParamType} {a₂ : sig₂.ParamType} {σ₁ σ₂ : VariableAssignment}
    (hA : A a₁ σ₁ a₂ σ₂) : (p₁.Pr a₁ σ₁ E₁ : ℝ) ≤ p₂.Pr a₂ σ₂ E₂ :=
  NNReal.coe_le_coe.mpr (Procedure.Pr_le_of_prhlProc h hE hA)

end Rules2

namespace PrTactics

open Lean Meta Elab Tactic

/-- `NNReal.toReal (Procedure.Pr p a m E)`: `(sig, p, a, m, E)`. -/
def prParts? (e : Lean.Expr) : Option (Array Lean.Expr) := do
  guard (e.isAppOfArity ``NNReal.toReal 1)
  let pr := e.appArg!
  guard (pr.isAppOfArity ``Procedure.Pr 5)
  return pr.getAppArgs

/-- The goal's relation (`Eq`, `LE.le`, `GE.ge` at `ℝ`) and its two sides. -/
def goalRel : TacticM (Name × Lean.Expr × Lean.Expr) := do
  let ty ← instantiateMVars (← whnfR (← getMainTarget))
  match_expr ty with
  | Eq _ l r => return (``Eq, l, r)
  | LE.le _ _ l r => return (``LE.le, l, r)
  | GE.ge _ _ l r => return (``GE.ge, l, r)
  | _ => throwError "expected a (in)equation between probabilities, got{indentExpr ty}"

/-- Try to close the side goals a rule leaves (each left as it is on failure). -/
def closeSide (gs : List MVarId) : TacticM (List MVarId) := do
  let mut left := []
  for g in gs do
    if ← g.isAssigned then continue
    let s ← saveState
    let closed ← try
        let gs' ← evalTacticAt (← `(tactic| first
          | exact ⟨rfl, rfl⟩ | exact ⟨rfl, rfl, rfl, rfl⟩ | trivial | rfl | exact le_rfl
          | positivity
          | (intros; subst_vars; rfl) | (intros; simp_all))) g
        pure gs'.isEmpty
      catch _ => pure false
    -- a tactic that made progress without closing the goal: undo it
    unless closed do
      s.restore
      left := left ++ [g]
  return left

end PrTactics

open Lean Meta Elab Tactic PrTactics in
/-- **EC's `byequiv`**, see the module docstring. -/
elab "byequiv" h?:(ppSpace colGt term:max)? : tactic => withMainContext do
  let (rel, l, r) ← goalRel
  let some L := prParts? l | throwError "byequiv: the left side is not a probability{indentExpr l}"
  let some R := prParts? r | throwError "byequiv: the right side is not a probability{indentExpr r}"
  let rule ← match rel with
    | ``Eq => pure ``Procedure.toReal_Pr_eq_of_prhlProc
    | ``LE.le => pure ``Procedure.toReal_Pr_le_of_prhlProc
    | _ => throwError "byequiv: `=` or `≤` between two probabilities"
  let (hT, preT?, postT?) ← match h? with
    | some h => pure (h, none, none)
    | none => do
      let E₁ ← Term.exprToSyntax L[4]!
      let E₂ ← Term.exprToSyntax R[4]!
      let sameRun ← withReducible (isDefEq L[2]! R[2]!) <&&> withReducible (isDefEq L[3]! R[3]!)
      let pre ← if sameRun then
          `(fun x₁ g₁ x₂ g₂ => x₁ = x₂ ∧ g₁ = g₂)
        else
          let a₁ ← Term.exprToSyntax L[2]!
          let m₁ ← Term.exprToSyntax L[3]!
          let a₂ ← Term.exprToSyntax R[2]!
          let m₂ ← Term.exprToSyntax R[3]!
          `(fun x₁ g₁ x₂ g₂ => x₁ = $a₁ ∧ g₁ = $m₁ ∧ x₂ = $a₂ ∧ g₂ = $m₂)
      let post ← if rel == ``Eq then
          `(fun r₁ g₁ r₂ g₂ => ($E₁ r₁ g₁ ↔ $E₂ r₂ g₂))
        else `(fun r₁ g₁ r₂ g₂ => ($E₁ r₁ g₁ → $E₂ r₂ g₂))
      pure (← `(?judgment), some pre, some post)
  let ruleId := mkIdent rule
  let stx ← match preT?, postT? with
    | some pre, some post => `(tactic| refine $ruleId (A := $pre) (B := $post) $hT ?hE ?hA)
    | _, _ => `(tactic| refine $ruleId $hT ?hE ?hA)
  evalTactic stx
  let gs ← getGoals
  -- the quotation's tags are hygienic: compared, and left, without their macro scopes
  for g in gs do g.setTag (← g.getTag).eraseMacroScopes
  let judgment ← gs.filterM fun g => return (← g.getTag) == `judgment
  let side := gs.filter (!judgment.contains ·)
  let left ← closeSide side
  setGoals (judgment ++ left)
  if !judgment.isEmpty then
    try evalTactic (← `(tactic| beta_reduce)) catch _ => pure ()

open Lean Meta Elab Tactic PrTactics in
/-- **EC's `byphoare`**, see the module docstring. -/
elab "byphoare" h?:(ppSpace colGt term:max)? : tactic => withMainContext do
  let (rel, l, r) ← goalRel
  -- the probability on the left for `≤`/`=`, on the right for `≥` (`x ≤ Pr` is `Pr ≥ x`)
  let (rule, P, x) ← match rel, prParts? l, prParts? r with
    | ``Eq, some P, _ => pure (``Procedure.toReal_Pr_eq_of_phoareProc, P, r)
    | ``LE.le, some P, _ => pure (``Procedure.toReal_Pr_le_of_phoareProc, P, r)
    | ``LE.le, none, some P => pure (``Procedure.le_toReal_Pr_of_phoareProc, P, l)
    | ``GE.ge, some P, _ => pure (``Procedure.le_toReal_Pr_of_phoareProc, P, r)
    | _, _, _ => throwError "byphoare: expected `Pr[ … ] ≤ x`, `= x` or `≥ x`"
  if rel == ``GE.ge then evalTactic (← `(tactic| show _ ≤ _))
  let ruleId := mkIdent rule
  let xT ← Term.exprToSyntax x
  -- `0 ≤ x` is a premise of the `≤` and `=` rules only
  let hasHx := rule != ``Procedure.le_toReal_Pr_of_phoareProc
  match h? with
  | some h =>
    if hasHx then evalTactic (← `(tactic| refine $ruleId $h ?hA ?hr ?hx))
    else evalTactic (← `(tactic| refine $ruleId $h ?hA ?hr))
  | none =>
    let aT ← Term.exprToSyntax P[2]!
    let mT ← Term.exprToSyntax P[3]!
    -- the signature first: the precondition's `x = a` is elaborated before unification
    let sigT ← Term.exprToSyntax P[0]!
    if hasHx then evalTactic (← `(tactic|
      refine $ruleId (sig := $sigT) (A := fun x g => x = $aT ∧ g = $mT)
        (r := fun _ _ => ENNReal.ofReal $xT) ?judgment ?hA ?hr ?hx))
    else evalTactic (← `(tactic|
      refine $ruleId (sig := $sigT) (A := fun x g => x = $aT ∧ g = $mT)
        (r := fun _ _ => ENNReal.ofReal $xT) ?judgment ?hA ?hr))
  let gs ← getGoals
  -- the quotation's tags are hygienic: compared, and left, without their macro scopes
  for g in gs do g.setTag (← g.getTag).eraseMacroScopes
  let judgment ← gs.filterM fun g => return (← g.getTag) == `judgment
  let side := gs.filter (!judgment.contains ·)
  let left ← closeSide side
  setGoals (judgment ++ left)
  if !judgment.isEmpty then
    try evalTactic (← `(tactic| beta_reduce)) catch _ => pure ()

end GaudisCrypt
