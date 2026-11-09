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
import GaudisCrypt.Logic.ECCallEquiv
import GaudisCrypt.Syntax.ModuleSubtype
import GaudisCrypt.Logic.ECSeq
import GaudisCrypt.Logic.ECInline

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

-- EC's subtyping `PRIMITIVE <: DPRIMITIVE` (the old port's module types are abbreviations)
module_subtype SLCommon.PRIMITIVE <: DPRIMITIVE

set_option maxHeartbeats 4000000 in
-- one declaration: EC's proof, its two cases on `PF.mi` and three on the handles
/-- EC's `equiv eq_fi (D <: DISTINGUISHER {-PF, -RO, -G1}) : DPRestr(PF).fi ~
DPRestr(G1(DRestr(D)).S).fi : …`, its proof EC's: the call with its invariant, `exists*`, the
ambient cases on `INV_CF_G1`, `PF.mi`, `G1.mi` and the handle's flag, EC's `rcondt`/`rcondf`
positions, and EC's closers (`lemma1'`, `lemma2'`, `m_p_of_INV`; EC's `smt` as `smt_close`).
`D` is not a parameter: neither procedure calls it (EC's restriction only frames the call). -/
theorem eq_fi : equiv[ DPRestr(PF).fi ~ DPRestr(G1.S).fi :
    ¬§G1.bcol{2} ∧ ¬§G1.bext{2} ∧ ={arg} ∧ ={glob C} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}
    ==> if §G1.bcol{2} ∨ §G1.bext{2}
        then FMap.dom §C.queries{1} [] ∧ FMap.dom §C.queries{2} []
        else ={res} ∧ ={glob C} ∧
          INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
            §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2} ] := by
  equiv_proc; stmt_sp; stmt_if <;> equiv_auto
  equiv_call (_ : ¬§G1.bcol{2} ∧ ¬§G1.bext{2} ∧ ={x} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}
    ==> ¬§G1.bcol{2} → ¬§G1.bext{2} → ={res} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}) <;> equiv_auto
  · equiv_exists* §FRO.m{2}, §G1.chandle{2}, §PF.m{1}, §PF.mi{1}, §G1.m{2}, §G1.mi{2}, §G1.mh{2},
      §G1.mhi{2}, §F.RO.m{2}, §G1.paths{2}, §x{2}, §Redo.prefixes{1}, §C.queries{2}
    intro hs ch Pm Pmi Gm Gmi mh mhi ro pi ⟨xa, xc⟩ prefixes queries
    by_cases inv0 : INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries; swap
    · equiv_exfalso; auto_close
    equiv_proc
    rcases Pmi_xaxc : FMap.get Pmi (xa, xc) with _ | ⟨ya, yc⟩
    · have := incli_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0 (xa, xc)
      rcases Gmi_xaxc : FMap.get Gmi (xa, xc) with _ | _; swap
      · simp [Pmi_xaxc, Gmi_xaxc] at this
      stmt_rcondt{1} 1; · hoare_auto; smt_close [FMap.domE]
      stmt_rcondt{2} 1; · hoare_auto; smt_close [FMap.domE]
      rcases hgf : getflag hs xc with _ | f
      · have xc_notrngE1_hs := (getflagP_none _ _).1 hgf
        stmt_rcondt{2} 2; · hoare_auto; smt_close [FMap.rngE]
        stmt_rcondf{2} 8
        · hoare_auto; auto_prep
          rw [huniq_hinvK_h ch _ _ (huniq_addh _ _ _ _ inv0.1.1 xc_notrngE1_hs)
            (FMap.get_set_sameE _ _ _)]
          simp [oget, FMap.domE, notin_hs_notdomE2_mh _ _ _ _ _ inv0.5 (ch_notdomE_hs _ _ inv0.1)]
        equiv_auto
        auto_prep
        rename_i ya _ yc _ _ _ _ _ hcol
        have yc_notrngE1_hs_addh := hinvP (hs.set ch (xc, Known)) yc
        rw [if_pos (by simp at hcol; exact hcol.2)] at yc_notrngE1_hs_addh
        rw [huniq_hinvK_h ch _ _ (huniq_addh _ _ _ _ inv0.1.1 xc_notrngE1_hs)
          (FMap.get_set_sameE _ _ _)]
        simp only [oget, Option.getD_some, FMap.get_set_sameE, true_and]
        rw [show ch + 1 + 1 = ch + 2 by ring]
        have hy2 : ∀ f h, hs.get h ≠ some (yc, f) := fun f h hh => by
          by_cases e : h = ch
          · subst e; simp [ch_notdomE_hs _ _ inv0.1] at hh
          · exact yc_notrngE1_hs_addh h f (by rw [FMap.get_setE, if_neg e]; exact hh)
        refine lemma1' hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries xa xc ya yc inv0 ?_ ?_
          Pmi_xaxc Gmi_xaxc xc_notrngE1_hs hy2
        · rw [FMap.domE]; intro hd
          obtain ⟨⟨a, b⟩, hab⟩ := Option.ne_none_iff_exists'.mp hd
          obtain ⟨hx, fx, -, -, h1, -, -⟩ := inv0.4.1 _ _ _ _ hab
          exact hy2 _ _ h1
        · rintro rfl; exact yc_notrngE1_hs_addh ch Known (FMap.get_set_sameE _ _ _)
      have Hhuniq := inv0.1.1
      cases f
      · have x2_is_U := (getflagP_some _ _ _ Hhuniq).1 hgf
        equiv_conseq (: _ ==> §G1.bext{2})
        · auto_close
        equiv_auto
      have x2_is_K := (getflagP_some _ _ _ Hhuniq).1 hgf
      obtain ⟨hx2, hs_hx2⟩ := id x2_is_K
      stmt_rcondf{2} 2; · hoare_auto
      stmt_rcondf{2} 6
      · hoare_auto; auto_prep
        rw [huniq_hinvK_h hx2 _ _ Hhuniq hs_hx2]
        simp [oget, FMap.domE, notin_m_notin_mh _ _ _ _ _ _ _ inv0.5 Pmi_xaxc hs_hx2]
      equiv_auto
      auto_prep
      rename_i ya _ yc _ _ _ hcol _ _
      have y2_notrngE1_hs := hinvP hs yc
      rw [if_pos (by simp at hcol; exact hcol.2)] at y2_notrngE1_hs
      rw [huniq_hinvK_h hx2 _ _ Hhuniq hs_hx2]
      simp only [oget, Option.getD_some, FMap.get_set_sameE, true_and]
      refine lemma2' hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries xa xc ya yc hx2 inv0 ?_
        Pmi_xaxc Gmi_xaxc hs_hx2 fun f h => y2_notrngE1_hs h f
      rw [FMap.domE]; intro hd
      obtain ⟨⟨a, b⟩, hab⟩ := Option.ne_none_iff_exists'.mp hd
      obtain ⟨hx, fx, -, -, h1, -, -⟩ := inv0.4.1 _ _ _ _ hab
      exact y2_notrngE1_hs _ _ h1
    · stmt_rcondf{1} 1; · hoare_auto; smt_close [FMap.domE]
      rcases Gmi_xaxc : FMap.get Gmi (xa, xc) with _ | ⟨ya', yc'⟩
      · stmt_rcondt{2} 1; · hoare_auto; smt_close [FMap.domE]
        equiv_conseq (: _ ==> §G1.bext{2})
        · auto_close
        equiv_auto
        auto_prep
        -- EC's `have ->: exists hx, hs.[hx] = Some (xc,Unknown)`
        have hU : hs.rng (xc, Unknown) := by
          obtain ⟨hx, fx, hy, fy, hs_hx, hs_hy, hmhi⟩ := inv0.5.1 _ _ _ _ Pmi_xaxc
          obtain ⟨xc', fx', yc', fy', h1, h2, h3⟩ := inv0.8.1 _ _ _ _ ((inv0.3.1 _ _).mpr hmhi)
          simp only [hs_hy, hs_hx, Option.some.injEq, Prod.mk.injEq] at h1 h2
          obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
          cases fx
          · exact ⟨hx, hs_hx⟩
          · simp [(inv0.2.1 _ _).mp h3.1] at Gmi_xaxc
        -- EC's `smt (@Block.DBlock @Capacity.DCapacity)`
        simp [hU]
      have := incli_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0 (xa, xc)
      simp only [Gmi_xaxc, Pmi_xaxc, ne_eq, reduceCtorEq, not_false_eq_true, Option.some.injEq,
        Prod.mk.injEq, forall_const] at this
      obtain ⟨rfl, rfl⟩ := this
      stmt_rcondf{2} 1; · hoare_auto; smt_close [FMap.domE]
      equiv_auto
  · auto_progress
    all_goals
      obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
      smt_close [FMap.domE]

set_option maxHeartbeats 8000000 in
-- one declaration: EC's proof, its cases on `PF.m`, `G1.paths`, the handle's flag and `G1.m`
/-- EC's `equiv eq_f (D <: DISTINGUISHER {-PF, -RO, -G1}) : DPRestr(PF).f ~
DPRestr(G1(DRestr(D)).S).f : …`, its proof EC's: the call with its invariant, `exists*`, the
ambient cases, `seq 2 2`/`seq 0 3`/`seq 0 1` with EC's conditions, `swap{2} 3 -2`, EC's
`rcondt`/`rcondf` positions (`inline F.RO.get` between them), and EC's closers (`lemma1`,
`lemma2`, `lemma3`, `m_p_of_INV`; EC's `smt` as `smt_close`).  Deviations: EC's inline closer of
the path case (~100 lines) is the old port's `f_path_inv`; one `conseq` to `G1.bext{2}` before
the last `auto` of the `Unknown` branch (`auto` with `INV_CF_G1` through the inlined oracle is
too slow). -/
theorem eq_f : equiv[ DPRestr(PF).f ~ DPRestr(G1.S).f :
    ¬§G1.bcol{2} ∧ ¬§G1.bext{2} ∧ ={x} ∧ ={glob C} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}
    ==> if §G1.bcol{2} ∨ §G1.bext{2}
        then FMap.dom §C.queries{2} []
        else ={res} ∧ ={glob C} ∧
          INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
            §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2} ] := by
  equiv_proc; stmt_sp; stmt_if <;> equiv_auto
  equiv_call (_ : ¬§G1.bcol{2} ∧ ¬§G1.bext{2} ∧ ={arg} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}
    ==> if §G1.bcol{2} ∨ §G1.bext{2} then FMap.dom §C.queries{2} []
      else ={res} ∧
        INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
          §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}) <;> equiv_auto
  · equiv_exists* §FRO.m{2}, §G1.chandle{2}, §PF.m{1}, §PF.mi{1}, §G1.m{2}, §G1.mi{2}, §G1.mh{2},
      §G1.mhi{2}, §F.RO.m{2}, §G1.paths{2}, §Redo.prefixes{1}, §C.queries{2}, §x{2}
    intro hs0 ch0 PFm PFmi G1m G1mi G1mh G1mhi ro0 pi0 pref queries ⟨x1, x2⟩
    by_cases inv0 : INV_CF_G1 hs0 ch0 PFm PFmi G1m G1mi G1mh G1mhi ro0 pi0 pref queries; swap
    · equiv_exfalso; auto_close
    equiv_proc
    rcases PFm_x1x2 : FMap.get PFm (x1, x2) with _ | ⟨xa, xc⟩
    · have Gm_x1x2 := notin_m_notin_Gm _ _ (x1, x2) (incl_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0)
        PFm_x1x2
      stmt_rcondt{1} 1; · hoare_auto; smt_close [FMap.domE]
      stmt_rcondt{2} 1; · hoare_auto; smt_close [FMap.domE]
      rcases x2_in_pi : FMap.get pi0 x2 with _ | ⟨p0, v0⟩
      · stmt_rcondf{2} 1; · hoare_auto; smt_close [FMap.domE]
        stmt_rcondf{2} 8; · hoare_auto; smt_close [FMap.domE]
        equiv_seq 2 2 : (hs0 = §FRO.m{2} ∧ ch0 = §G1.chandle{2} ∧ PFm = §PF.m{1} ∧
            PFmi = §PF.mi{1} ∧ G1m = §G1.m{2} ∧ G1mi = §G1.mi{2} ∧ G1mh = §G1.mh{2} ∧
            G1mhi = §G1.mhi{2} ∧ ro0 = §F.RO.m{2} ∧ pi0 = §G1.paths{2} ∧ pref = §Redo.prefixes{1} ∧
            queries = §C.queries{2} ∧ (x1, x2) = §x{2} ∧ ¬§G1.bcol{2} ∧ ¬§G1.bext{2} ∧
            ={x, y1, y2} ∧ INV_CF_G1 hs0 ch0 PFm PFmi G1m G1mi G1mh G1mhi ro0 pi0 pref queries)
        · equiv_auto
        rcases hgf : getflag hs0 x2 with _ | f
        · have x2f_notrngE_hs0 := (getflagP_none _ _).1 hgf
          stmt_rcondt{2} 3; · hoare_auto; smt_close [FMap.rngE]
          stmt_rcondf{2} 6
          · hoare_auto; auto_prep
            rw [huniq_hinvK_h ch0 _ _ (huniq_addh _ _ _ _ inv0.1.1 x2f_notrngE_hs0)
              (FMap.get_set_sameE _ _ _)]
            simp [oget, FMap.domE, notin_hs_notdomE2_mh _ _ _ _ _ inv0.4 (ch_notdomE_hs _ _ inv0.1)]
          equiv_case (x2 ≠ §y2{2} ∧ ∀ f h, hs0.get h ≠ some (§y2{2}, f))
          · equiv_auto; auto_prep
            rename_i _ _ y1 y2 x2_neq_y2 y2_notin_hs _ _ _
            rw [huniq_hinvK_h ch0 _ _ (huniq_addh _ _ _ _ inv0.1.1 x2f_notrngE_hs0)
              (FMap.get_set_sameE _ _ _)]
            obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
            split_ifs
            · simp [FMap.domE, hq]
            simp only [oget, FMap.get_set_sameE, Option.getD_some, true_and]
            rw [show ch0 + 1 + 1 = ch0 + 2 by ring]
            exact lemma1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inv0 x2_neq_y2 PFm_x1x2 Gm_x1x2
              x2f_notrngE_hs0 y2_notin_hs
          · equiv_conseq (: _ ==> §G1.bcol{2})
            · obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
              smt_close [FMap.domE]
            equiv_auto; auto_prep
            rename_i _ _ _ y2 hcase _ _ _
            have hs0_spec := hinvP (hs0.set ch0 (x2, Known)) y2
            split_ifs at hs0_spec with hnone
            · exfalso; apply hcase; constructor
              · rintro rfl; exact hs0_spec ch0 Known (FMap.get_set_sameE _ _ _)
              · intro f h hh
                by_cases e : h = ch0
                · subst e; simp [ch_notdomE_hs _ _ inv0.1] at hh
                · exact hs0_spec h f (by rw [FMap.get_setE, if_neg e]; exact hh)
            · simp [hnone]
        have Hhuniq := inv0.1.1
        cases f
        · have x2_is_U := (getflagP_some _ _ _ Hhuniq).1 hgf
          equiv_conseq (: _ ==> §G1.bext{2})
          · obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
            smt_close [FMap.domE]
          equiv_auto
        have x2_is_K := (getflagP_some _ _ _ Hhuniq).1 hgf
        stmt_rcondf{2} 3; · hoare_auto
        obtain ⟨hx, hs0_hx⟩ := id x2_is_K
        equiv_seq 0 3 : (hs0 = §FRO.m{2} ∧ ch0 = §G1.chandle{2} ∧ PFm = §PF.m{1} ∧
            PFmi = §PF.mi{1} ∧ G1m = §G1.m{2} ∧ G1mi = §G1.mi{2} ∧ G1mh = §G1.mh{2} ∧
            G1mhi = §G1.mhi{2} ∧ ro0 = §F.RO.m{2} ∧ pi0 = §G1.paths{2} ∧ pref = §Redo.prefixes{1} ∧
            queries = §C.queries{2} ∧ (x1, x2) = §x{2} ∧ ¬§G1.bcol{2} ∧ ¬§G1.bext{2} ∧
            ={x, y1, y2} ∧ §y{2} = (§y1{2}, §y2{2}) ∧ §hx2{2} = hx ∧
            INV_CF_G1 hs0 ch0 PFm PFmi G1m G1mi G1mh G1mhi ro0 pi0 pref queries)
        · equiv_auto; auto_progress
          · obtain ⟨h, hs_h⟩ : hs0.rng (x2, Unknown) := by simp_all
            have := Hhuniq _ _ _ _ hs0_hx hs_h rfl; subst this; simp [hs0_hx] at hs_h
          · rw [huniq_hinvK_h hx _ _ Hhuniq hs0_hx]; rfl
        have x1hx_notin_G1m := notin_m_notin_mh _ _ _ _ _ _ _ inv0.4 PFm_x1x2 hs0_hx
        stmt_rcondf{2} 1; · hoare_auto; smt_close [FMap.domE]
        equiv_auto; auto_prep
        rename_i _ _ y1 y2 _ _ _
        obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
        split_ifs with h
        · simp [FMap.domE, hq]
        have hy := hinvP hs0 y2
        rw [if_pos (by simp_all)] at hy
        simp only [oget, FMap.get_set_sameE, Option.getD_some, true_and]
        exact lemma2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inv0 PFm_x1x2 Gm_x1x2 x2_in_pi hs0_hx
          fun f h => hy h f
      obtain ⟨hx2, Hpath, hs_hx2⟩ := (inv0.9.1 _ _ _).mp x2_in_pi
      stmt_rcondt{2} 1; · hoare_auto; smt_close [FMap.domE]
      stmt_rcondf{2} 6; · hoare_auto; hoare_inline*; hoare_auto; smt_close [FMap.rngE]
      stmt_rcondf{2} 7
      · hoare_auto; hoare_inline*; hoare_auto; auto_prep
        rw [huniq_hinvK_h hx2 _ _ inv0.1.1 hs_hx2]
        simp [oget, FMap.domE, notin_m_notin_mh _ _ _ _ _ _ _ inv0.4 PFm_x1x2 hs_hx2]
      stmt_rcondt{2} 15; · hoare_auto; hoare_inline*; hoare_auto; smt_close [FMap.domE]
      stmt_inline (PROM.FullRO.ROmap.get (List block) block F.RO)
      stmt_rcondt{2} 4
      · hoare_auto; auto_prep
        simp [x2_in_pi, oget, FMap.domE,
          f_path_ro_none _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inv0 PFm_x1x2 hs_hx2 Hpath]
      equiv_auto; auto_prep
      rename_i _ _ y1 _ y2 _ _ _ _
      obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
      split_ifs with h
      · simp [FMap.domE, hq]
      have hy : hinv hs0 y2 = none := by simp_all
      simp only [x2_in_pi, oget, Option.getD_some, FMap.get_set_sameE,
        huniq_hinvK_h hx2 _ _ inv0.1.1 hs_hx2, true_and]
      -- EC's inline closer (~100 lines): the old port's lemma
      exact f_path_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inv0 PFm_x1x2 x2_in_pi hs_hx2 Hpath hy
    stmt_rcondf{1} 1; · hoare_auto; smt_close [FMap.domE]
    obtain ⟨hx2, fx2, hy2, fy2, hs_hx2, hs_hy2, G1mh_x1hx2⟩ := inv0.4.1 _ _ _ _ PFm_x1x2
    rcases G1m_x1x2 : FMap.get G1m (x1, x2) with _ | ⟨ya, yc⟩; swap
    · have := incl_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0 (x1, x2)
      simp only [G1m_x1x2, PFm_x1x2, ne_eq, reduceCtorEq, not_false_eq_true, Option.some.injEq,
        Prod.mk.injEq, forall_const] at this
      obtain ⟨rfl, rfl⟩ := this
      stmt_rcondf{2} 1; · hoare_auto; smt_close [FMap.domE]
      equiv_auto
    stmt_rcondt{2} 1; · hoare_auto; smt_close [FMap.domE]
    obtain rfl : fy2 = Unknown := by
      obtain ⟨xc0, xf0, yc0, yf0, h1, h2, h3⟩ := inv0.8.1 _ _ _ _ G1mh_x1hx2
      rw [hs_hx2] at h1; rw [hs_hy2] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
      obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
      cases fy2
      · rfl
      · simp [G1m_x1x2] at h3
    cases fx2
    · stmt_swap{2} 3 -2
      equiv_seq 0 1 : (queries = §C.queries{2} ∧ §G1.bext{2})
      · equiv_auto; smt_close [FMap.rngE]
      equiv_conseq (: _ ==> ¬(§G1.bcol{2} ∨ §G1.bext{2}) → oget (§PF.m{1}.get §x{1}) = §y{2} ∧
          INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
            §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2})
      · obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
        smt_close [FMap.domE]
      stmt_inline*
      -- (not EC's: `auto` through the inlined code with `INV_CF_G1` in the postcondition is
      -- too slow; the postcondition holds as `bext` stays set)
      equiv_conseq (: _ ==> §G1.bext{2})
      · auto_close
      stmt_if{2} <;> equiv_auto
    obtain ⟨xc0, xf0, yc0, yf0, h1, h2, h3⟩ := inv0.8.1 _ _ _ _ G1mh_x1hx2
    rw [hs_hx2] at h1; rw [hs_hy2] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
    simp only [reduceCtorEq, if_false] at h3
    obtain ⟨p0, v0, Hro, Hpath⟩ := h3
    have pi_x2 := (inv0.9.1 x2 p0 v0).2 ⟨hx2, Hpath, hs_hx2⟩
    stmt_rcondt{2} 1; · hoare_auto; smt_close [FMap.domE]
    stmt_inline (PROM.FullRO.ROmap.get (List block) block F.RO)
    stmt_rcondf{2} 4; · hoare_auto; auto_prep; simp [pi_x2, oget, FMap.domE, Hro]
    stmt_rcondf{2} 8; · hoare_auto; smt_close [FMap.rngE]
    stmt_rcondt{2} 9
    · hoare_auto; auto_prep
      rw [huniq_hinvK_h hx2 _ _ inv0.1.1 hs_hx2]
      simp [oget, FMap.domE, G1mh_x1hx2, FMap.in_dom_with, hs_hy2]
    stmt_rcondt{2} 14; · hoare_auto; smt_close [FMap.domE]
    equiv_auto; auto_prep
    refine ⟨by simp [F.dout], fun _ _ => ⟨by simp, fun _ _ => ?_⟩⟩
    rw [huniq_hinvK_h hx2 _ _ inv0.1.1 hs_hx2]
    simp only [pi_x2, oget, Option.getD_some, Hro, G1mh_x1hx2, hs_hy2, PFm_x1x2]
    obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
    split_ifs with h
    · simp [FMap.domE, hq]
    exact ⟨trivial, lemma3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inv0 PFm_x1x2 G1m_x1x2 G1mh_x1hx2
      hs_hx2 hs_hy2 pi_x2⟩
  · auto_close

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
  · equiv_conseq (SHA3.Handle.eq_f D (by fp_disjoint))
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
  · equiv_conseq (SHA3.Handle.eq_fi D (by fp_disjoint))
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
