import GaudisCrypt.Logic.SyntacticFrame

/-!
# Footprint and frame tactics, invariant Hoare rules

Small helpers for game proofs that frame oracles against an abstract adversary:
* `fp_mem`: `X ≤ A₁ ⊔ … ⊔ Aₙ` for `X` one of the joinands; `fp_sub`: a join below a join;
* `writes_keep'`: `writes_keep` with the footprint hypotheses found syntactically;
* `hoareProc_const`, `hoare_if_inv`, `hoare_seq_inv`: Hoare rules for an invariant.
-/

namespace GaudisCrypt

/-- `X ≤ A₁ ⊔ … ⊔ Aₙ` for `X` one of the joinands (nested joins included), by backtracking. -/
syntax "fp_mem" : tactic
macro_rules
  | `(tactic| fp_mem) => `(tactic| first
    | with_reducible exact le_rfl
    | (with_reducible apply le_sup_of_le_right); fp_mem
    | (with_reducible apply le_sup_of_le_left); fp_mem)

/-- A join of footprints below a join containing each of its joinands (`fp_mem`, splitting the
left-hand join). -/
syntax "fp_sub" : tactic
macro_rules
  | `(tactic| fp_sub) => `(tactic| first | fp_mem | (refine sup_le ?_ ?_ <;> fp_sub))

open Lean Meta Elab Tactic in
/-- `writes_keep`, the writes to global lenses closed by `touched_set_of_le_compl` with a hypothesis
`X.footprint ≤ Fᶜ` about the written lens `X` itself (found syntactically, not by `assumption`,
which compares the footprints of different lenses by unfolding them). -/
elab "writes_keep'" : tactic => do
  liftMetaTactic (writesKeepSplit ·)
  evalTactic (← `(tactic| all_goals try exact fun _ _ => rfl))
  let gs₀ ← getGoals
  for g in gs₀ do
    if ← g.isAssigned then continue
    let ty ← instantiateMVars (← g.getType)
    let some lift := ty.find? (·.isAppOfArity ``liftLens 4) | continue
    let X := lift.appArg!
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      let dty ← instantiateMVars d.type
      unless dty.isAppOfArity ``LE.le 4 do continue
      let lhs := dty.getArg! 2
      unless lhs.isAppOf ``Lens.footprint && lhs.appArg! == X do continue
      let s ← saveState
      try
        setGoals [g]
        withoutRecover <| evalTactic (← `(tactic| exact fun v σ => touched_set_of_le_compl
          $(mkIdent d.userName) v σ.globals))
        break
      catch _ => s.restore
  setGoals gs₀
  let gs ← gs₀.filterM fun g => return !(← g.isAssigned)
  setGoals gs

/-- A Hoare triple whose pre- and postcondition are the same proposition, independent of the
state. -/
theorem hoareProc_const {sig} (p : Procedure sig) (P : Prop) :
    hoareProc (fun _ _ => P) p (fun _ _ => P) := by
  by_cases hP : P
  · simpa only [hP] using hoareProc_true p
  · exact fun _ _ h => absurd h hP

/-- A conditional keeps an invariant when both branches do. -/
theorem hoare_if_inv {c : Getter Bool ProgramState} {p q : Stmt} {J B : ProgramState → Prop}
    (ht : hoareStmt J p B) (he : hoareStmt J q B) : hoareStmt J (.ifThenElse c p q) B :=
  hoare_pre (hoare_if_wp ht he) fun _ h => ⟨fun _ => h, fun _ => h⟩

/-- Sequencing through an invariant: the first part keeps the precondition. -/
theorem hoare_seq_inv {J C : ProgramState → Prop} {p q : Stmt} (hq : hoareStmt J q C)
    (hp : hoareStmt J p J) : hoareStmt J (.seq p q) C :=
  hoare_seq hq hp

end GaudisCrypt
