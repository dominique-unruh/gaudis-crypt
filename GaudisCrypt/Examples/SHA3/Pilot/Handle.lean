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
import GaudisCrypt.Logic.ECWhile

/-!
# `Handle.eca`'s `CF_G1` in EC's form — the tactic experiment

EC's `CF_G1` (the game-level equivalence of `CF` and `G1` up to the bad events, through EC's
up-to-bad `call (_: bad, inv, inv')` over the distinguisher's three oracle procedures), stated and
proven as EC does, over the old port's declarations (`SmartCounter/Handle.lean`).  It drove the
tactics the SmartCounter files need (`notes/SHA3/Refactor.md`, phase 3): `equiv_call (_ : bad, I,
J)`, `glob D` in conditions, `equiv_conseq H`, `phoare_while I V`, `sp` keeping the precondition,
`glob_simp`.  The declarations move to EC's form with the port of `SLCommon`, `ConcreteF`,
`Handle`.

Deviations from EC's proof:
* `unfold CF`: the old port declares `CF` a `def`, not a module alias;
* the oracles' steps `eq_f`, `eq_fi`, `PFf_Cf` are the old port's (with its footprint hypothesis
  for `D`, discharged by `fp_disjoint`), and so is `INV_CF_G1_init` (EC's 18 `smt` calls);
* the right oracles' losslessness is one more goal each (exception E11);
* EC splits the right `C.f`'s judgment in a `hoare` (bad kept) and a lossless `phoare` (`conseq
  (: _ ==> true) (: _ ==> G1.bcol \/ G1.bext)`): here one `phoare_while` with the bad event and
  `J` in the invariant;
* EC's closers (`smt`, `/#`, `progress`) are `simp`, `split_ifs`, `omega`.
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

-- EC's `declare axiom D_ll`
variable (D_ll : ∀ (F <: DFUNCTIONALITY {-D}), ∀ (P <: DPRIMITIVE {-D}),
  islossless P.f → islossless P.fi → islossless F.f → islossless D(F, P).distinguish)

set_option maxHeartbeats 1000000 in
-- one declaration: EC's call over three oracles, with their twelve goals
include D_ll in
/-- EC's `equiv CF_G1 : CF(DRestr(D)).main ~ G1(DRestr(D)).main : ={glob D} ==>
!(G1.bcol \/ G1.bext){2} => ={res}`, its proof EC's (see the module docstring). -/
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
    · stmt_if
      · stmt_wp
        phoare_while True ((size §p - §i).toNat)
        · intro k; phoare_auto
          rintro i p - - - - ⟨-, hc, hk⟩
          have h : (size p - (i + 1)).toNat < k := by simp only [decide_eq_true_eq] at hc; omega
          simp [h]
        · phoare_auto
      · phoare_auto
    · phoare_auto
  -- lossless and do not reset bad G1.C.f
  · phoare_proc; phoare_inline*; stmt_sp; stmt_if
    · stmt_if
      · phoare_auto
        phoare_while ((§G1.bcol ∨ §G1.bext) ∧ FMap.dom §C.queries []) ((size §p - §i).toNat)
        · intro k; phoare_auto
          rintro bcol bext queries i p - - - - - - ⟨⟨hb, hq⟩, hc, hk⟩
          have h : (size p - (i + 1)).toNat < k := by simp only [decide_eq_true_eq] at hc; omega
          rcases hb with hb | hb <;> simp [hb, hq, h, indicatorE_of, F.dout]
        · phoare_auto
          intros; simp_all [indicatorE]
        · intros; simp_all [FMap.mem_set]
      · phoare_auto; intros; simp_all [indicatorE]
    · phoare_auto
      intros; simp_all [indicatorE]
  -- lossless G1.C.f
  · phoare_proc; phoare_inline*; stmt_sp; stmt_if
    · stmt_if
      · phoare_auto
        phoare_while True ((size §p - §i).toNat)
        · intro k; phoare_auto
          intros; rename_i hc
          obtain ⟨-, hc, rfl⟩ := hc
          simp only [decide_eq_true_eq] at hc
          split_ifs <;> simp [F.dout, indicatorE, hc]
        · phoare_auto
      · phoare_auto
    · phoare_auto
  -- Init ok
  · stmt_wp; equiv_skip
    intro g₁ g₂ hD
    glob_simp
    refine ⟨⟨hD, INV_CF_G1_init⟩, fun r₁ g₁ r₂ g₂ h hnb => ?_⟩
    rcases h with ⟨hb, -⟩ | ⟨hr, -⟩
    · exact absurd hb hnb
    · exact hr

end AUX

end GaudisCrypt.SHA3.Pilot.Handle
