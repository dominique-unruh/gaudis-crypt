import GaudisCrypt.Logic.StmtEquiv

/-!
# Programs commuting with a state update, through loops

`ProgramDenotation.CommutesU p u`: running `p` from `u st` is running it from `st` and applying
`u` to the final state.  It is preserved by `⊥`, `pure`, `bind` and the suprema of chains, and so
by `while_loop` (the Kleene argument of `ProgramDenotation.EquivInLens.while_loop`).  This is what
`stmt_swap` and `stmt_alias` need of a loop (`Stmt.CommutesWith.while`, `Logic/StmtSwap.lean`):
a loop whose guard `u` leaves alone and whose body commutes with `u` commutes with `u`.
-/

namespace GaudisCrypt

/-- `p` commutes with the state update `u`. -/
def ProgramDenotation.CommutesU {s : Type u} {α : Type v} (p : ProgramDenotation s α)
    (u : s → s) : Prop :=
  ∀ st, p (u st) = (p st).mapState u

namespace ProgramDenotation.CommutesU

variable {s : Type u} {u : s → s}

theorem bot {α : Type v} : (⊥ : ProgramDenotation s α).CommutesU u := fun st => by
  change (⊥ : SubProbability (α × s)) = (⊥ : SubProbability (α × s)).mapState u
  rw [SubProbability.mapState_eq, SubProbability.bot_bind]

theorem pure {α : Type v} (a : α) : (Pure.pure a : ProgramDenotation s α).CommutesU u :=
  fun st => by
  rw [ProgramDenotation.pure_apply, ProgramDenotation.pure_apply, SubProbability.mapState_eq,
    SubProbability.pure_bind]

theorem bind {α β : Type v} {p : ProgramDenotation s α} {q : α → ProgramDenotation s β}
    (hp : p.CommutesU u) (hq : ∀ a, (q a).CommutesU u) : (p >>= q).CommutesU u := fun st => by
  rw [ProgramDenotation.bind_apply, ProgramDenotation.bind_apply, hp st,
    SubProbability.mapState_eq, SubProbability.mapState_eq, SubProbability.bind_assoc,
    SubProbability.bind_assoc]
  congr 1; funext r
  rw [SubProbability.pure_bind, hq r.1 r.2, SubProbability.mapState_eq]

theorem get {α : Type v} (c : Getter α s) (hc : ∀ st, c.get (u st) = c.get st) :
    (ProgramDenotation.get c).CommutesU u := fun st => by
  rw [ProgramDenotation.get_apply', ProgramDenotation.get_apply', hc, SubProbability.mapState_eq,
    SubProbability.pure_bind]

theorem ωSup {α : Type v} (ch : OmegaCompletePartialOrder.Chain (ProgramDenotation s α))
    (h : ∀ n, (ch n).CommutesU u) : (OmegaCompletePartialOrder.ωSup ch).CommutesU u :=
  fun st => by
  have h₁ : (OmegaCompletePartialOrder.ωSup ch) (u st) = OmegaCompletePartialOrder.ωSup
      (ch.map ⟨fun m => m (u st), fun _ _ hh => Pi.le_def.mp hh (u st)⟩) := rfl
  have h₂ : (OmegaCompletePartialOrder.ωSup ch) st = OmegaCompletePartialOrder.ωSup
      (ch.map ⟨fun m => m st, fun _ _ hh => Pi.le_def.mp hh st⟩) := rfl
  rw [h₁, h₂, (SubProbability.mapState_ωScottContinuous (α := α) u).map_ωSup]
  congr 1
  ext n
  exact h n st

/-- **A loop commutes with `u`** when its guard and its body do. -/
theorem while_loop {cond : ProgramDenotation s Bool} {body : ProgramDenotation s Unit}
    (hc : cond.CommutesU u) (hb : body.CommutesU u) : (while_loop cond body).CommutesU u := by
  let F := while_iteration cond body
  have key : ∀ n : ℕ, ((F^[n] (⊥ : Unit → ProgramDenotation s Unit)) ()).CommutesU u := by
    intro n
    induction n with
    | zero => exact bot
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      change (cond >>= fun b => if b = true then body >>= fun _ => (F^[n] ⊥) ()
                else (Pure.pure () : ProgramDenotation s Unit)).CommutesU u
      refine bind hc fun b => ?_
      by_cases h : b = true
      · simp only [h, if_true]
        exact bind hb fun _ => ih
      · simp only [h, Bool.false_eq_true, if_false]
        exact pure ()
  let chainF : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation s Unit) :=
    ⟨fun n => F^[n] ⊥, Monotone.monotone_iterate_of_le_map F.monotone (OrderBot.bot_le _)⟩
  have hF_at : F.lfp () = OmegaCompletePartialOrder.ωSup
      (chainF.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := rfl
  change (F.lfp ()).CommutesU u
  rw [hF_at]
  exact ωSup _ key

end ProgramDenotation.CommutesU

end GaudisCrypt
