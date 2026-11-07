import GaudisCrypt.Examples.SHA3.SmartCounter.Handle
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECCallUpto
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECIf

/-!
# `Handle.eca`'s `CF_G1` in EC's form — the tactic experiment

EC's `CF_G1` (the game-level equivalence of `CF` and `G1` up to the bad events, through EC's
up-to-bad `call (_: bad, inv, inv')` over the distinguisher's three oracle procedures), stated and
proven as EC does, over the old port's declarations (`SmartCounter/Handle.lean`).  It drives the
tactics the SmartCounter files need (`notes/SHA3/Refactor.md`, phase 3); the declarations move to
EC's form with the port of `SLCommon`, `ConcreteF`, `Handle`.
-/

namespace GaudisCrypt.SHA3.Pilot.Handle

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.ConcreteF
open GaudisCrypt.SHA3.Handle

variable [SLCommon.Params]

/-- EC's `Block.DBlock.dunifin_ll`, as the expectation of `1` (what `auto` leaves). -/
@[simp] theorem bdistr_expected_one : bdistr.expected (fun _ => (1 : ENNReal)) = 1 :=
  (is_lossless_iff_expected _).mp BitWord.dunifin_ll

/-- EC's `Capacity.DCapacity.dunifin_ll`, as the expectation of `1`. -/
@[simp] theorem cdistr_expected_one : cdistr.expected (fun _ => (1 : ENNReal)) = 1 :=
  (is_lossless_iff_expected _).mp BitWord.dunifin_ll

section AUX

declare module D <: DISTINGUISHER {-PF, -F.RO, -ROhandle.RO, -G1, -Redo, -C}


variable (D_ll : ∀ (F <: DFUNCTIONALITY {-D}), ∀ (P <: DPRIMITIVE {-D}),
  islossless P.f → islossless P.fi → islossless F.f → islossless D(F, P).distinguish)

set_option maxHeartbeats 1000000 in
-- the experiment: measuring
include D_ll in
theorem CF_G1 : equiv[ CF(DRestr(D)).main ~ G1(DRestr(D)).main :
    ={glob D} ==> ¬(§G1.bcol{2} ∨ §G1.bext{2}) → ={res} ] := by
  unfold CF -- the old port declares `CF` a `def`, not an alias
  equiv_proc; stmt_inline*; stmt_wp
  equiv_call (_ : §G1.bcol ∨ §G1.bext,
    ={C.c, C.queries} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2},
    FMap.dom §C.queries{2} [])
  · exact D_ll
  -- proofs for G1.S.f
  -- equivalence up to bad of PF.f and G1.S.f
  · equiv_conseq (eq_f D (by fp_disjoint))
    · rintro a₁ g₁ a₂ g₂ ⟨hb, rfl, hC, hI⟩
      simp only [not_or, Bool.not_eq_true] at hb
      exact ⟨hb.1, hb.2, rfl, hC, hI⟩
    · intro _ _ _ _ h
      split_ifs at h ⊢ <;> exact h
  -- lossless PF.f
  · phoare_proc; phoare_inline*; phoare_auto
    -- EC's `smt (@Block.DBlock @Capacity.DCapacity)`: the distributions are lossless
    intro _ _; split_ifs <;> simp
  -- lossless and do not reset bad G1.S.f
  · phoare_proc; phoare_inline*; phoare_auto
    rintro σ ⟨hb | hb, hq⟩ <;> simp [hb, hq, F.dout]
  -- lossless G1.S.f (the deviation: EC needs it only after the bad event, above)
  · phoare_proc; phoare_inline*; phoare_auto
    intro _ _; split_ifs <;> simp [F.dout]
  -- proofs for G1.S.fi
  -- equiv PF.P.fi G1.S.fi
  · equiv_conseq (eq_fi D (by fp_disjoint))
    · rintro a₁ g₁ a₂ g₂ ⟨hb, rfl, hC, hI⟩
      simp only [not_or, Bool.not_eq_true] at hb
      exact ⟨hb.1, hb.2, rfl, hC, hI⟩
    · intro _ _ _ _ h
      split_ifs at h ⊢ <;> first | exact h.2 | exact h
  -- lossless PF.P.fi
  · phoare_proc; phoare_inline*; phoare_auto
    intro _ _; split_ifs <;> simp
  -- lossless and do not reset bad G1.S.fi
  · phoare_proc; phoare_inline*; phoare_auto
    rintro σ ⟨hb | hb, hq⟩ <;> simp [hb, hq]
  -- lossless G1.S.fi
  · phoare_proc; phoare_inline*; phoare_auto
    intro _ _; split_ifs <;> simp
  -- proofs for G1.C.f
  -- equiv PF.C.f G1.C.f
  · equiv_conseq (PFf_Cf D)
    · exact fun _ _ _ _ h => h
    · intro _ _ _ _ h
      split_ifs at h ⊢ <;> first | exact h | exact ⟨h.2.1, h.1, h.2.2⟩
  -- lossless PF.C.f
  · phoare_proc; phoare_inline*; stmt_sp; stmt_if
    · phoare_auto
      trace_state
      sorry
    · sorry
  all_goals sorry

end AUX

end GaudisCrypt.SHA3.Pilot.Handle
