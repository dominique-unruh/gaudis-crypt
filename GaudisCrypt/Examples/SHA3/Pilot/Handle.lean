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
import GaudisCrypt.Logic.ECWhileRel
import GaudisCrypt.Logic.ECCallEquiv
import GaudisCrypt.Syntax.ModuleSubtype
import GaudisCrypt.Logic.ECSeq
import GaudisCrypt.Logic.ECInline
import GaudisCrypt.Logic.ECLoop
import GaudisCrypt.Logic.ECAlias
import GaudisCrypt.Logic.ECGoals
import GaudisCrypt.Logic.StmtSwap

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

module_subtype FUNCTIONALITY <: DFUNCTIONALITY

/-- EC's first bullet of `PFf_Cf`'s first loop body (`prefix_gt0_mem`, `prefix_take_leq`, the
`m_p` part of the invariant): the next prefix of a queried path is known. -/
theorem PFf_Cf_dom_next (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (pref : FMap (List block) SLCommon.state) (Q : FMap (List block) block) (p : List block) (i : ℤ)
    (hI : INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi pref Q) (hi0 : 0 ≤ i)
    (hi : i < «prefix» p (get_max_prefix p (elems (FMap.fdom Q)))) :
    FMap.dom pref (take (i + 1) p) := by
  have hmp := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ hI
  have hmem : FMap.dom Q (get_max_prefix p (elems (FMap.fdom Q))) :=
    (mem_elems_fdom _ _).1 (prefix_gt0_mem _ _ (by omega))
  rw [prefix_take_leq p (get_max_prefix p (elems (FMap.fdom Q))) (i + 1) (by omega)]
  obtain ⟨-, -, -, Iq, -⟩ := id hmp
  obtain ⟨c, hc⟩ := Iq _ hmem
  exact all_prefixes_of_m_p _ _ _ hmp _ ((FMap.domE _ _).2 (by simp [hc])) _

/-- EC's `smt(get_setE mem_set DBlock.dunifin_ll DCapacity.dunifin_ll)` closing the leaves of
`PFf_Cf`'s second loop in the bad case (the bad event stays, the samplings are lossless), by
hand. -/
local macro "pf_bad_leaf" : tactic => `(tactic| (auto_prep; all_goals (simp_all [FMap.get_setE,
  FMap.mem_set, F.dout, bdistr_expected_one, cdistr_expected_one] <;>
  (intros; (try refine ⟨FMap.get_some _ _ ‹_›, ?_⟩); simp only [← Bool.not_eq_true] at *; tauto))))

/-! Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* GAP 2: the second loop still uses the older `equiv_while_raw` (four goals, no frame); the
  first is EC's `while I` (`equiv_while`) with EC's `auto; progress` and eight bullets.
* GAP 5: the pilot's oracle lemmas (`eq_f`, `eq_fi`, `PFf_Cf`, in EC's paths through
  `module_subtype` coercions) match `CF_G1`'s oracles (the old port's `CF`/`G1` views) only by
  heavy unfolding (~2M heartbeats per `conseq`): goes away with EC-form `CF`/`G1` declarations.
-/

set_option maxHeartbeats 8000000 in
/-- EC's `equiv PFf_Cf (D <: DISTINGUISHER) : DFRestr(SqueezelessSponge(PF)).f ~
DFRestr(G1(DRestr(D)).M).f : …`, its proof EC's, block by block (EC's lines as comments): `proc;
sp; inline*`, the `if`s with `1,3:auto`, `swap`, `wp 1 5`, `conseq`, `seq 1 1`, `splitwhile`,
the two loops with EC's invariants, `alias`, `case`, `rcondt`/`rcondf` at EC's positions.
Deviations: hand closers where `smt_close` fails (EC's `smt`); EC's long inline closers are the
old port's lemmas (`PJ1_step`, `PJ1_PJ2`, `PJ2_known`, `PJ2_fresh`, `PJ2L_step`); `={bs}` added
to the first loop's invariant and the left's samplings swapped for EC's `swap{2} -3` (the gaps
listed above). -/
theorem PFf_Cf : equiv[ DFRestr(SqueezelessSponge(PF)).f ~ DFRestr(G1.M).f :
    ¬(§G1.bcol{2} ∨ §G1.bext{2}) ∧ ={arg} ∧ ={glob C} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}
    ==> if §G1.bcol{2} ∨ §G1.bext{2}
        then FMap.dom §C.queries{2} []
        else ={glob C} ∧ ={res} ∧
          INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
            §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2} ] := by
  -- EC: proc;sp;inline*;sp.
  --     (EC's second `sp` has nothing to do here: dropped)
  equiv_proc; stmt_sp; stmt_inline*
  -- EC: if;1,3:auto;if;1,3:auto;swap{1}4;swap{2}11;sp;wp 1 5.
  stmt_if; on_goals 1, 3 => equiv_auto
  stmt_if; on_goals 1, 3 => equiv_auto
  stmt_swap{1} 4; stmt_swap{2} 11; stmt_sp; stmt_wp 1 5
  -- EC: sp;conseq(:_==> ! (G1.bcol{2} \/ G1.bext{2}) =>
  --         ={glob C, sa} /\
  --         INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2} G1.mh{2}
  --           G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1} C.queries{2}.[bs{1} <- sa{1}] /\
  --         F.RO.m.[p]{2} = Some sa{2});progress.
  --     (EC's `sp` has nothing to do here: dropped)
  equiv_conseq (: _ ==> ¬(§G1.bcol{2} ∨ §G1.bext{2}) →
      ={glob C, sa} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1}
        (FMap.set §C.queries{2} §bs{1} §sa{1}) ∧
      FMap.get §F.RO.m{2} §p{2} = some §sa{2})
  · auto_prep
    split_ifs
    -- EC: + by rewrite mem_set domE;left;have[]_->_ _ _//=:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0.
    · obtain ⟨-, hq, -, -, -⟩ :=
        m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
      smt_close [FMap.mem_set, FMap.domE]
    -- EC: + smt(mem_set).  + smt(mem_set).  + smt(mem_set).
    · auto_close
  -- EC: seq 1 1:
  --       (={i, p, glob C} /\ i{1} = size p{1} /\ p{2} = bs{1} /\
  --         (!(G1.bcol{2} \/ G1.bext{2}) =>
  --         (INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2}
  --           G1.mh{2} G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1}
  --           C.queries{2}.[bs{1} <- sa{1}]
  --         /\ ={sa} /\ F.RO.m.[p]{2} = Some sa{1})));last first.
  equiv_seq 1 1 : (={i, p, glob C} ∧ §i{1} = size §p{1} ∧ §p{2} = §bs{1} ∧
      (¬(§G1.bcol{2} ∨ §G1.bext{2}) →
        INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
          §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1}
          (FMap.set §C.queries{2} §bs{1} §sa{1}) ∧
        ={sa} ∧ FMap.get §F.RO.m{2} §p{2} = some §sa{1}))
  rotate_right
  -- EC: + case : (! (G1.bcol{2} \/ G1.bext{2}));last first.
  · equiv_case (¬(§G1.bcol{2} ∨ §G1.bext{2}))
    rotate_right
    -- EC: - by conseq(:_==>true);progress;auto;smt(DBlock.dunifin_ll DCapacity.dunifin_ll take_size).
    · equiv_conseq (: _ ==> True)
      · auto_close
      · equiv_auto
    -- EC: by rcondf{2}3;auto;smt(domE DBlock.dunifin_ll DCapacity.dunifin_ll take_size).
    · stmt_rcondf{2} 3
      · hoare_auto; smt_close [FMap.domE]
      equiv_auto
      auto_prep; simp_all [F.dout, oget]

  -- EC: conseq(:_==> ={i, p, glob C} /\ i{1} = size p{1} /\ p{2} = bs{1} /\
  --       (!(G1.bcol{2} \/ G1.bext{2}) =>
  --       (INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2}
  --         G1.mh{2} G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1}
  --         C.queries{2}.[take i{2} bs{1} <- sa{1}]
  --       /\ ={sa} /\ F.RO.m.[p]{2} = Some sa{1})));1:smt(take_size).
  equiv_conseq (: _ ==> ={i, p, glob C} ∧ §i{1} = size §p{1} ∧ §p{2} = §bs{1} ∧
      (¬(§G1.bcol{2} ∨ §G1.bext{2}) →
        INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
          §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1}
          (FMap.set §C.queries{2} (take §i{2} §bs{1}) §sa{1}) ∧
        ={sa} ∧ FMap.get §F.RO.m{2} §p{2} = some §sa{1}))
  · smt_close [take_size]
  -- EC: splitwhile{1} 1 : i < prefix p (get_max_prefix p (elems (fdom C.queries))).
  --     splitwhile{2} 1 : i < prefix p (get_max_prefix p (elems (fdom C.queries))).
  stmt_splitwhile{1} 1 : §i < «prefix» §p (get_max_prefix §p (elems (FMap.fdom §C.queries)))
  stmt_splitwhile{2} 1 : §i < «prefix» §p (get_max_prefix §p (elems (FMap.fdom §C.queries)))
  -- EC: seq 1 1 : (={p, i, glob C, bs} /\ bs{2} = p{2} /\
  --       (prefix p (get_max_prefix p (elems (fdom C.queries))) = i){2} /\
  --       (Redo.prefixes.[take i p]{1} = Some (sa,sc){1}) /\
  --       (take i p \in Redo.prefixes){1} /\
  --       (C.queries.[[]] = Some b0){1} /\
  --       (! p{2} \in C.queries{2}) /\
  --       (!(G1.bcol{2} \/ G1.bext{2}) =>
  --         (INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2}
  --           G1.mh{2} G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1}
  --           C.queries{2} /\
  --           ={sa} /\  counter{2} = 0 /\
  --           (exists f, FRO.m.[h]{2} = Some (sc{1}, f)) /\
  --           (build_hpath G1.mh (take i p) = Some (sa,h)){2} /\
  --           if i{2} = 0 then (sa,h){2} = (b0, 0)
  --           else F.RO.m.[take i p]{2} = Some sa{1})) /\
  --       (i{2} = 0 => sa{1} = b0) /\ 0 < size p{2}).
  equiv_seq 1 1 : (={p, i, glob C, bs} ∧ §bs{2} = §p{2} ∧
      «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2}))) = §i{2} ∧
      FMap.get §Redo.prefixes{1} (take §i{1} §p{1}) = some (§sa{1}, §sc{1}) ∧
      FMap.dom §Redo.prefixes{1} (take §i{1} §p{1}) ∧
      FMap.get §C.queries{1} [] = some b0 ∧
      ¬FMap.dom §C.queries{2} §p{2} ∧
      (¬(§G1.bcol{2} ∨ §G1.bext{2}) →
        INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
          §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2} ∧
        ={sa} ∧ §counter{2} = 0 ∧
        (∃ f, FMap.get §FRO.m{2} §h{2} = some (§sc{1}, f)) ∧
        build_hpath §G1.mh{2} (take §i{2} §p{2}) = some (§sa{2}, §h{2}) ∧
        (if §i{2} = 0 then (§sa{2}, §h{2}) = (b0, 0)
          else FMap.get §F.RO.m{2} (take §i{2} §p{2}) = some §sa{1})) ∧
      (§i{2} = 0 → §sa{1} = b0) ∧ 0 < size §p{2})
  -- EC: + while(={p, i, glob C} /\ bs{2} = p{2} /\ (i{2} = 0 => sa{1} = b0) /\
  --         (0 <= i <= prefix p (get_max_prefix p (elems (fdom C.queries)))){2} /\
  --         (Redo.prefixes.[take i p]{1} = Some (sa,sc){1}) /\
  --         (take i p \in Redo.prefixes){1} /\
  --         (C.queries.[[]] = Some b0){1} /\
  --         (! p{2} \in C.queries{2}) /\
  --         (!(G1.bcol{2} \/ G1.bext{2}) =>
  --           (INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2}
  --             G1.mh{2} G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1}
  --             C.queries{2} /\
  --             ={sa} /\  counter{2} = 0 /\
  --             (exists f, FRO.m.[h]{2} = Some (sc{1}, f)) /\
  --             (build_hpath G1.mh (take i p) = Some (sa,h)){2} /\
  --             if i{2} = 0 then (sa,h){2} = (b0, 0)
  --             else F.RO.m.[take i p]{2} = Some sa{1})) /\ 0 < size p{2});last first.
  · equiv_while (={p, i, glob C} ∧ §bs{2} = §p{2} ∧ (§i{2} = 0 → §sa{1} = b0) ∧
        0 ≤ §i{2} ∧ §i{2} ≤ «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2}))) ∧
        FMap.get §Redo.prefixes{1} (take §i{1} §p{1}) = some (§sa{1}, §sc{1}) ∧
        FMap.dom §Redo.prefixes{1} (take §i{1} §p{1}) ∧
        FMap.get §C.queries{1} [] = some b0 ∧
        ¬FMap.dom §C.queries{2} §p{2} ∧
        (¬(§G1.bcol{2} ∨ §G1.bext{2}) →
          INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
            §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2} ∧
          ={sa} ∧ §counter{2} = 0 ∧
          (∃ f, FMap.get §FRO.m{2} §h{2} = some (§sc{1}, f)) ∧
          build_hpath §G1.mh{2} (take §i{2} §p{2}) = some (§sa{2}, §h{2}) ∧
          (if §i{2} = 0 then (§sa{2}, §h{2}) = (b0, 0)
            else FMap.get §F.RO.m{2} (take §i{2} §p{2}) = some §sa{1})) ∧
        0 < size §p{2})
    -- EC: - auto;progress.
    --       * smt(@Prefix).  * by have[]:=m_p_of_INV … H0;smt(take0 domE). (×2)
    --       * by have[]:=m_p_of_INV … H0.  * by have[]:=hs_of_INV … H0;smt(take0 domE).
    --       * by rewrite build_hpathP; apply/Empty=> //; exact/take0.
    --       * by have[]:=m_p_of_INV … H0; smt(take0 domE size_take size_eq0 size_ge0).
    --       * smt(prefix_sizel).
    case hpre =>
      equiv_auto; auto_progress
      -- EC: * smt(@Prefix).
      · exact prefix_ge0 _ _
      -- EC: * by have[]:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0;smt(take0 domE).
      · obtain ⟨hp0, -, -, -, -⟩ :=
          m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
        smt_close [take, FMap.domE]
      -- EC: * by have[]:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0;smt(take0 domE).
      · obtain ⟨hp0, -, -, -, -⟩ :=
          m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
        smt_close [take, FMap.domE]
      -- EC: * by have[]:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0.
      · obtain ⟨-, hq, -, -, -⟩ :=
          m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
        exact hq
      -- EC: * by have[]:=hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0;smt(take0 domE).
      · obtain ⟨-, h0, -⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
        exact ⟨Known, h0⟩
      -- EC: * by have[]:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0;
      --       smt(take0 domE size_take size_eq0 size_ge0).
      · obtain ⟨-, hq, -, -, -⟩ :=
          m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
        by_contra hsz
        simp only [size, not_lt, Nat.cast_nonpos, List.length_eq_zero_iff] at hsz
        subst hsz; simp_all [FMap.domE]
      --     (`bs` kept by the loop: EC's frame, EC's `progress` closes it; `simp_all` cycles on the
      --     frames' equations)
      · exact (by assumption : (localVarLens "bs" (List block)).get _ = _).trans
          (by assumption : (localVarLens "bs" (List block)).get _ = _).symm
      -- EC: * smt(prefix_sizel).
      · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at *
        smt_close [prefix_sizel]
    case body =>
      -- EC: case(G1.bcol{2} \/ G1.bext{2}).
      equiv_case (§G1.bcol{2} ∨ §G1.bext{2})
      -- EC: - by if{1};auto;conseq(:_==> (G1.bcol{2} \/ G1.bext{2}));1,3:smt(domE get_setE);
      --         (if{2};2:if{2});auto;1:smt(DBlock.dunifin_ll DCapacity.dunifin_ll);
      --         sp;if{1};auto;smt(DBlock.dunifin_ll DCapacity.dunifin_ll).
      · stmt_if{1} <;> ((equiv_auto; equiv_conseq (: _ ==> §G1.bcol{2} ∨ §G1.bext{2})) <;> [
          (auto_prep
           all_goals (split_ands <;> (try omega) <;> (try simp only [Prod.mk.eta]) <;>
             (try (apply FMap.get_some; simp_all)) <;> (try simp_all [FMap.domE])));
          (stmt_if{2}; on_goals 2 => stmt_if{2})])
        all_goals equiv_auto
        all_goals try (stmt_sp; stmt_if{1} <;> equiv_auto)
        -- EC's `smt(DBlock.dunifin_ll DCapacity.dunifin_ll)`: the samplings are lossless, the bad
        -- event stays
        all_goals (auto_prep
                   all_goals simp_all [F.dout, bdistr_expected_one, cdistr_expected_one])
      -- EC: conseq(: ={p, i, glob C} /\ bs{2} = p{2} /\ (i{2} = 0 => sa{1} = b0) /\
      --       0 <= i{2} <= prefix p{2} (get_max_prefix p{2} (elems (fdom C.queries{2}))) /\
      --       Redo.prefixes{1}.[take i{1} p{1}] = Some (sa{1}, sc{1}) /\
      --       (C.queries.[[]] = Some b0){1} /\ (! p{2} \in C.queries{2}) /\
      --       (take i{1} p{1} \in Redo.prefixes{1}) /\
      --       (! (G1.bcol{2} \/ G1.bext{2}) =>
      --         INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2}
      --         G1.mh{2} G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1}
      --         C.queries{2} /\
      --         ={sa} /\
      --         counter{2} = 0 /\
      --         (exists (f : flag), FRO.m{2}.[h{2}] = Some (sc{1}, f)) /\
      --           build_hpath G1.mh{2} (take i{2} p{2}) = Some (sa{2}, h{2}) /\
      --         if i{2} = 0 then (sa{2}, h{2}) = (b0, 0)
      --           else F.RO.m{2}.[take i{2} p{2}] = Some sa{1}) /\
      --     (i{1} < size p{1} /\
      --       i{1} < prefix p{1} (get_max_prefix p{1} (elems (fdom C.queries{1})))) /\
      --       i{2} < size p{2} /\
      --       i{2} < prefix p{2} (get_max_prefix p{2} (elems (fdom C.queries{2}))) /\
      --       ! (G1.bcol{2} \/ G1.bext{2}) /\ (take (i+1) p \in Redo.prefixes){1} /\
      --       0 < size p{2}
      --       ==>_);progress.
      · equiv_conseq (: ={p, i, glob C} ∧ §bs{2} = §p{2} ∧ (§i{2} = 0 → §sa{1} = b0) ∧
            0 ≤ §i{2} ∧ §i{2} ≤ «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2}))) ∧
            FMap.get §Redo.prefixes{1} (take §i{1} §p{1}) = some (§sa{1}, §sc{1}) ∧
            FMap.get §C.queries{1} [] = some b0 ∧ ¬FMap.dom §C.queries{2} §p{2} ∧
            FMap.dom §Redo.prefixes{1} (take §i{1} §p{1}) ∧
            (¬(§G1.bcol{2} ∨ §G1.bext{2}) →
              INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
                §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2} ∧
              ={sa} ∧ §counter{2} = 0 ∧
              (∃ f, FMap.get §FRO.m{2} §h{2} = some (§sc{1}, f)) ∧
              build_hpath §G1.mh{2} (take §i{2} §p{2}) = some (§sa{2}, §h{2}) ∧
              (if §i{2} = 0 then (§sa{2}, §h{2}) = (b0, 0)
                else FMap.get §F.RO.m{2} (take §i{2} §p{2}) = some §sa{1})) ∧
            (§i{1} < size §p{1} ∧
              §i{1} < «prefix» §p{1} (get_max_prefix §p{1} (elems (FMap.fdom §C.queries{1})))) ∧
            §i{2} < size §p{2} ∧
            §i{2} < «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2}))) ∧
            ¬(§G1.bcol{2} ∨ §G1.bext{2}) ∧ FMap.dom §Redo.prefixes{1} (take (§i{1} + 1) §p{1}) ∧
            0 < size §p{2} ==> _)
        -- EC: - have:=prefix_gt0_mem p{2} (elems (fdom C.queries{2})) _;1:rewrite/#. … (10 lines)
        --     (as the lemma `PFf_Cf_dom_next`)
        · auto_prep
          simp only [Bool.and_eq_true, decide_eq_true_eq] at *
          casesm* _ ∧ _
          all_goals (split_ands <;> (try assumption) <;>
            (try exact PFf_Cf_dom_next _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_›) <;>
            (try (glob_tuples; simp_all)))
        -- EC: rcondt{1}1;1:auto;progress.
        stmt_rcondt{1} 1
        · hoare_auto
        -- EC: rcondt{2}1;1:auto;progress.
        stmt_rcondt{2} 1
        -- EC: - have[]HINV[]->>/=[]->>/=[]H_h[]H_path H_F_RO:=H6 H11.
        --       have//=:=lemma5 _ _ _ _ _ _ _ _ _ _ _ _ i{hr} p{hr} sa{hr} sc{m} h{hr} HINV _ _ _ _.
        --       … by move=>[]b2 c2 h2[]H_PFm H_Gmh;rewrite domE H_Gmh/=.
        · hoare_auto; auto_prep
          obtain ⟨b', c', h', -, hmh⟩ := lemma5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _› ⟨by omega, by omega⟩ ‹_› ‹_› ⟨_, ‹_›⟩
          simp [FMap.domE, hmh]
        -- EC: auto;progress.
        equiv_auto
        --     (EC's twelve bullets, ~60 lines with `lemma5`, `m_mh_of_INV`, `mh_of_INV`,
        --     `build_hpath_prefix`: the old port's `PJ1_step`, the loop's step — deviation)
        rintro p₁ i₁ c₁ q₁ sa₁ pref sc₁ m₁ mi₁ p₂ i₂ c₂ q₂ bs₂ bcol bext hs ch gm gmi mh mhi ro paths
          sa₂ cnt h ⟨⟨hp, hi, ⟨hc, hqq⟩⟩, hbs2, hsa0, hi0, hiq, hpref, hq0, hq, hdom, hJ,
            ⟨hi1, hi1'⟩, -, -, hbad, hdom1, hsz⟩
        subst hp hi hc hqq
        obtain ⟨hI, rfl, hcnt, ⟨f, hh⟩, hb, hif⟩ := hJ hbad
        have hJ1 : PJ1 hs ch m₁ mi₁ gm gmi mh mhi ro paths pref q₁ p₁ i₁ sa₁ sc₁ h :=
          ⟨hI, hpref, ⟨f, hh⟩, hb, by simpa using hif, hi0, hiq, hq, hsz⟩
        obtain ⟨-, -, he, hI', hpref', hh', hb', hif', hi0', hiq', -, -⟩ :=
          PJ1_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hJ1 hi1'
        refine ⟨⟨⟨rfl, rfl, rfl, rfl⟩, hbs2, fun h0 => absurd h0 (by omega), by omega, hiq',
          hpref', hdom1, hq0, hq, fun _ => ⟨hI', he, hcnt, hh', by rw [← he]; exact hb', ?_⟩, hsz⟩,
          rfl⟩
        rw [if_neg (by omega)] at hif' ⊢
        exact hif'
  -- EC: alias{1} 1 prefixes = Redo.prefixes;sp.
  --     alias{2} 1 bad1     = G1.bcol;sp.
  stmt_alias{1} 1 prefixes = §Redo.prefixes
  stmt_sp
  stmt_alias{2} 1 bad1 = §G1.bcol
  stmt_sp
  -- EC: while (  ={i, p, C.queries, C.c}
  --       /\ prefix p{2} (get_max_prefix p{2} (elems (fdom C.queries{2}))) <=
  --         i{1} <= size p{1}
  --       /\ Redo.prefixes{1}.[take i{2} p{2}] = Some (sa{1}, sc{1})
  --       /\ p{2} = bs{1}
  --       /\ (! p{2} \in C.queries{2})
  --       /\ (! (G1.bcol{2} \/ G1.bext{2}) =>
  --           INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2}
  --             G1.mh{2} G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1}
  --             C.queries{2}.[take i{2} bs{1} <- sa{1}]
  --         /\ ! (bad1{2} \/ G1.bext{2})
  --         /\ m_p PF.m{1} prefixes{1} C.queries{2}
  --         /\ (forall (l : block list),
  --              l \in prefixes{1} => prefixes{1}.[l] = Redo.prefixes{1}.[l])
  --         /\ (forall (l : block list), l \in Redo.prefixes{1} =>
  --              (l \in prefixes{1}) \/
  --              exists (j : int), 0 <= j <= i{2} /\ take j p{2} = l)
  --         /\ ={sa}
  --         /\ counter{2} <= i{2} - prefix p{2}
  --            (get_max_prefix p{2} (elems (fdom C.queries{2})))
  --         /\ (exists (f : flag), FRO.m{2}.[h{2}] = Some (sc{1}, f))
  --         /\ build_hpath G1.mh{2} (take i{2} p{2}) = Some (sa{2}, h{2})
  --         /\ (if i{2} = 0 then (sa{2}, h{2}) = (b0, 0)
  --             else F.RO.m{2}.[take i{2} p{2}] = Some sa{1})
  --         /\ (i{2} < size p{2} => ! take (i{2}+1) p{2} \in Redo.prefixes{1})));last first.
  equiv_while_raw (={i, p, C.queries, C.c} ∧
      «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2}))) ≤ §i{1} ∧
      §i{1} ≤ size §p{1} ∧
      FMap.get §Redo.prefixes{1} (take §i{2} §p{2}) = some (§sa{1}, §sc{1}) ∧
      §p{2} = §bs{1} ∧
      ¬FMap.dom §C.queries{2} §p{2} ∧
      (¬(§G1.bcol{2} ∨ §G1.bext{2}) →
        INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
          §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1}
          (FMap.set §C.queries{2} (take §i{2} §bs{1}) §sa{1}) ∧
        ¬(§bad1{2} ∨ §G1.bext{2}) ∧
        m_p §PF.m{1} §prefixes{1} §C.queries{2} ∧
        (∀ l, FMap.dom §prefixes{1} l → FMap.get §prefixes{1} l = FMap.get §Redo.prefixes{1} l) ∧
        (∀ l, FMap.dom §Redo.prefixes{1} l →
          FMap.dom §prefixes{1} l ∨ ∃ j, 0 ≤ j ∧ j ≤ §i{2} ∧ take j §p{2} = l) ∧
        ={sa} ∧
        §counter{2} ≤ §i{2} - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2}))) ∧
        (∃ f, FMap.get §FRO.m{2} §h{2} = some (§sc{1}, f)) ∧
        build_hpath §G1.mh{2} (take §i{2} §p{2}) = some (§sa{2}, §h{2}) ∧
        (if §i{2} = 0 then (§sa{2}, §h{2}) = (b0, 0)
          else FMap.get §F.RO.m{2} (take §i{2} §p{2}) = some §sa{1}) ∧
        (§i{2} < size §p{2} → ¬FMap.dom §Redo.prefixes{1} (take (§i{2} + 1) §p{2}))))
  case guard => auto_close
  -- EC (of the second goal): part of `auto;progress.`: `rewrite/#`, `smt(take_size)`
  case exit =>
    auto_prep
    rename_i pref sa sc pm pmi pref0 i p q c bcol bext hs ch gm gmi mh mhi ro paths bad1 sa2 cnt h
      hpref hq hpi hi hJ hg
    have hip : i = size p := by omega
    refine ⟨hip, fun hb => ?_⟩
    obtain ⟨hI, -, hmp, -, -, rfl, -, -, -, hif, -⟩ := hJ hb
    obtain ⟨-, hq0, -, -, -⟩ := hmp
    have hp0 : p ≠ [] := by rintro rfl; exact hq ((FMap.domE _ _).2 (by simp [hq0]))
    have hi0 : i ≠ 0 := by
      rw [hip]; cases p with
      | nil => exact absurd rfl hp0
      | cons _ _ => simp only [size, List.length_cons]; omega
    rw [if_neg hi0] at hif
    simp only [hip, take_size] at hI hif ⊢
    exact ⟨hI, by simp, hif⟩
  -- EC: + auto;progress.
  --     (fifteen bullets: `prefix_sizel`, `m_p_of_INV`, `mem_set`, `prefix_exchange_prefix_inv`,
  --     `take_size`; the old port's `PJ1_PJ2`, the first loop's end as the second's start —
  --     deviation)
  case hpre =>
    equiv_auto
    rintro p₁ i₁ c₁ q₁ bs₁ pref sa₁ sc₁ m₁ mi₁ pref0 p₂ i₂ c₂ q₂ bs₂ bcol bext hs ch gm gmi mh mhi ro
      paths sa₂ cnt h bad1 ⟨⟨⟨⟨hp, hi, ⟨hc, hqq⟩, hbs⟩, hbs2, hpi, hpref, -, -, hq, hJ, -, hsz⟩, rfl⟩,
        rfl⟩
    subst hp hi hc hqq hbs hbs2
    refine ⟨⟨rfl, rfl, rfl, rfl⟩, hpi.le, by rw [← hpi]; exact prefix_sizel _ _, hpref, rfl, hq,
      fun hb => ?_⟩
    obtain ⟨hI, rfl, rfl, ⟨f, hh⟩, hb', hif⟩ := hJ hb
    have hJ1 : PJ1 hs ch m₁ mi₁ gm gmi mh mhi ro paths pref0 q₁ bs₁ i₁ sa₁ sc₁ h :=
      ⟨hI, hpref, ⟨f, hh⟩, hb', by simpa using hif, by rw [← hpi]; exact prefix_ge0 _ _, hpi.ge,
        hq, hsz⟩
    obtain ⟨⟨hI2, hmp, -, -, -⟩, ⟨-, -, -, hnext, -⟩⟩ :=
      PJ1_PJ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hJ1 (by unfold qpre; omega)
    exact ⟨hI2, hb, hmp, fun _ _ => rfl, fun _ hl => Or.inl hl, rfl, by omega, ⟨f, hh⟩, hb', hif,
      hnext⟩
  case body =>
    -- EC: case : (! (G1.bcol{2} \/ G1.bext{2}));last first.
    equiv_case (¬(§G1.bcol{2} ∨ §G1.bext{2}))
    rotate_right
    -- EC: - wp 1 1=>/=.
    · stmt_wp 1 1
      -- EC: conseq(:_==> Redo.prefixes{1}.[take (i{1}+1) p{1}] = Some (sa{1}, sc{1})
      --           /\ (take (i{1} + 1) p{1} \in Redo.prefixes{1})
      --           /\ (G1.bcol{2} \/ G1.bext{2}));1:smt(prefix_ge0).
      equiv_conseq (: _ ==>
          FMap.get §Redo.prefixes{1} (take (§i{1} + 1) §p{1}) = some (§sa{1}, §sc{1}) ∧
          FMap.dom §Redo.prefixes{1} (take (§i{1} + 1) §p{1}) ∧ (§G1.bcol{2} ∨ §G1.bext{2}))
      · auto_prep
        all_goals (split_ands <;> (try omega); try simp_all)
      -- EC's closer of every leaf below: smt(get_setE mem_set DBlock.dunifin_ll DCapacity.dunifin_ll)
      -- EC: if {1}; last first.
      stmt_if{1}; rotate_right
      -- EC: + sp; if {1}; if {2}; last first.
      · stmt_sp; stmt_if{1} <;> stmt_if{2}
        rotate_right
        -- EC: + if {2}; sp; auto=> />. (+ smt …) smt …
        · stmt_if{2} <;> equiv_auto <;> pf_bad_leaf
        -- EC: + auto=> />. smt …
        · equiv_auto; pf_bad_leaf
        -- EC: + if {2}; last first. + auto=> />. smt … + swap {2} 4 -3; auto=> />. smt …
        · stmt_if{2}; rotate_right
          · equiv_auto; pf_bad_leaf
          · stmt_swap{2} 4 -3; equiv_auto; pf_bad_leaf
        -- EC: auto=> />. smt …
        · equiv_auto; pf_bad_leaf
      -- EC: if {2}. + auto=> />. smt …  if {2}. + auto=> />. smt …  auto=> />. smt …
      · stmt_if{2}
        · equiv_auto; pf_bad_leaf
        · stmt_if{2}
          · equiv_auto; pf_bad_leaf
          · equiv_auto; pf_bad_leaf
    -- EC: rcondf{1}1;1:auto=>/#.
    stmt_rcondf{1} 1
    · hoare_auto
    -- EC: sp;wp.
    stmt_sp; stmt_wp
    -- EC: if{1};2:rcondt{2}1;first last;3:rcondf{2}1;..3:auto.
    --     (as bullets: the known case first, EC's `first last`)
    stmt_if{1}
    rotate_left
    -- the left's `x` is in `PF.m`: the right's handle path is known
    · stmt_rcondt{2} 1
      -- EC: + progress.
      --     have[]HINV[]Hbad[]HINV0[]Hp1[]Hp2[]->>[]H_counter[]H_h[]H_path[]H_F_RO H_take_not_in:=H3 H6.
      --     have:=lemma5' _ _ _ _ _ _ _ _ _ _ _ _ i{hr} bs{m} sa{hr} sc{m} h{hr} HINV _ _ _.
      --     - smt(prefix_ge0).  - exact H1.  - exact H_h.
      --     by have:=H7;rewrite !domE=>->/=/#.
      · hoare_auto; auto_prep
        rcases lemma5' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
            ⟨le_trans (prefix_ge0 _ _) ‹_›, ‹_›⟩ ‹_› ⟨_, ‹_›⟩ with ⟨b', c', h', -, hmh⟩ | ⟨hP, -⟩
        · simp [FMap.domE, hmh]
        · simp_all [FMap.domE]
      -- EC: + progress. … (the known block, ~60 lines: `m_p_of_INV`, `mem_set`, `get_setE`,
      --     `take_take`, `nth_take`, `prefix_exchange_prefix_inv`, …) — the old port's
      --     `PJ2_known` and `PJ2L_step` (deviation)
      equiv_auto
      auto_prep
      rename_i bcol bext hs ch gm gmi mh mhi ro paths bad1 cnt h w hb hisz hb1 hpp hpbs hpref hext hmp
        hI hpi hq hcnt hpath hi hif hdom f hh hnext
      have hJ : PJ2 hs ch _ _ gm gmi mh mhi ro paths _ _ _ _ _ _ _ h :=
        ⟨by rw [hpbs]; exact hI, hmp, ⟨f, hh⟩, hpath, by simpa using hif⟩
      have hL : PJ2L _ _ _ _ _ _ _ :=
        ⟨hpref, fun l hl => (hpp l hl).symm, hext, fun _ => hnext, hpi, hisz, hq⟩
      set x : SLCommon.state := ((localVarLens "sa" block).get w +^
          nth default ((localVarLens "p" (List block)).get w) ((localVarLens "i" ℤ).get w),
          (localVarLens "sc" capacity).get w) with hx
      have hdomx : FMap.dom (PF.m.get w.globals) x := by simpa using hdom
      obtain ⟨-, hfst, hI', hmp', ⟨f', hh'⟩, hpath', hif'⟩ :=
        PJ2_known _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hJ hL hi hdomx
      have hL' := PJ2L_step _ _ _ _ _ _ _ (oget (FMap.get (PF.m.get w.globals) x)).1
        (oget (FMap.get (PF.m.get w.globals) x)).2 hL hi (all_prefixes_of_m_p _ _ _ hmp)
      simp only [Prod.mk.eta] at hL' ⊢
      obtain ⟨hpref', hpp', hext', hnext', hpi', hisz', -⟩ := hL'
      have h0 := le_trans (prefix_ge0 _ _) hpi
      refine ⟨hpi', hisz', hpref', hpbs, hq, fun _ => ⟨by rw [← hpbs]; exact hI', hb1, hmp,
        fun l hl => (hpp' l hl).symm, hext', hfst, by omega, ⟨f', hh'⟩, by rw [hpath', hfst],
        ?_, hnext'⟩⟩
      rw [if_neg (by omega)] at hif' ⊢
      exact hif'
    -- the left's `x` is fresh: so is the right's
    · stmt_rcondf{2} 1
      -- EC: + progress. … lemma5' … by have:=H7;rewrite !domE=>/=->/=.
      · hoare_auto; auto_prep
        rcases lemma5' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
            ⟨le_trans (prefix_ge0 _ _) ‹_›, ‹_›⟩ ‹_› ⟨_, ‹_›⟩ with ⟨b', c', h', hP, -⟩ | ⟨-, hmh⟩
        · simp_all [FMap.domE]
        · simp [FMap.domE, hmh]
      -- EC: rcondt{2}1;1:auto=>/#.
      stmt_rcondt{2} 1
      · hoare_auto; auto_prep; omega
      -- EC: rcondt{2}5;auto;progress.
      stmt_rcondt{2} 5
      -- EC: * rewrite(@take_nth witness);1:smt(prefix_ge0);rewrite domE. … (~20 lines:
      --       `mh_of_INV`, `lemma5'`) — the old port's `PJ2_fresh` (deviation)
      · hoare_auto; auto_prep
        rename_i bcol bext hs ch gm gmi mh mhi ro paths bad1 cnt h sc' hsc' r w hb hisz hb1 hpp
          hpbs hr hpref hext hmp hI hpi hq hcnt hpath hi hif hdom f hh hnext
        have hJ : PJ2 hs ch _ _ gm gmi mh mhi ro paths _ _ _ _ _ _ _ h :=
          ⟨by rw [hpbs]; exact hI, hmp, ⟨f, hh⟩, hpath, by simpa using hif⟩
        have hL : PJ2L _ _ _ _ _ _ _ :=
          ⟨hpref, fun l hl => (hpp l hl).symm, hext, fun _ => hnext, hpi, hisz, hq⟩
        exact (PJ2_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hJ hL hi (by simpa using hdom)).2.1
      --     (EC's `auto` on the main goal: here only wp — EC's `rnd` cannot pair `y2` with `r`)
      stmt_wp
      -- EC: swap{2}-3;auto;progress.
      stmt_swap{2} -3
      equiv_auto
      --     (EC's closer, ~200 lines: `hs_addh`, `inv_addm`, `m_mh_addh_addm`, `mi_mhi_addh_addmi`,
      --     `build_hpath_up`, `build_hpath_upd_ch_iff`, `known_path_uniq`, … — the old port's
      --     `PJ2_fresh` (with `f_fresh_inv`) and `PJ2L_step`: deviation)
      auto_prep
      rename_i bcol bext hs ch gm gmi mh mhi ro paths bad1 cnt h y1 hy1 y2 hy2 w hb hisz hb1 hpp
        hpbs hpref hext hmp hI hpi hq hcnt hpath hi hif hdom f hh hnext
      have hJ : PJ2 hs ch _ _ gm gmi mh mhi ro paths _ _ _ _ _ _ _ h :=
        ⟨by rw [hpbs]; exact hI, hmp, ⟨f, hh⟩, hpath, by simpa using hif⟩
      have hL : PJ2L _ _ _ _ _ _ _ :=
        ⟨hpref, fun l hl => (hpp l hl).symm, hext, fun _ => hnext, hpi, hisz, hq⟩
      obtain ⟨-, hro, hfr⟩ :=
        PJ2_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hJ hL hi (by simpa using hdom)
      have hL' := PJ2L_step _ _ _ _ _ _ _ y1 y2 hL hi (all_prefixes_of_m_p _ _ _ hmp)
      have h0 := le_trans (prefix_ge0 _ _) hpi
      simp only [FMap.get_set_sameE, oget_some] at hL' ⊢
      obtain ⟨hpref', hpp', hext', hnext', hpi', hisz', -⟩ := hL'
      refine ⟨hpi', hisz', trivial, hpbs, hq, fun hb' => ?_⟩
      have hinv : hinv hs y2 = none := by
        simp only [not_or, Bool.or_eq_true, decide_eq_true_eq, ne_eq, not_not] at hb'
        exact hb'.1.2
      obtain ⟨hI', hmp', -, hpath', -⟩ := hfr y1 y2 hinv
      exact ⟨by rw [← hpbs]; exact hI', hb1, hmp', fun l hl => (hpp' l hl).symm, hext', trivial,
        by omega, ⟨Unknown, rfl⟩, hpath', by rw [if_neg (by omega)]; trivial, hnext'⟩

section AUX

declare module D <: DISTINGUISHER {-PF, -F.RO, -ROhandle.RO, -G1, -Redo, -C}

-- EC's `declare axiom D_ll`
variable (D_ll : ∀ (F <: DFUNCTIONALITY {-D}), ∀ (P <: DPRIMITIVE {-D}),
  islossless P.f → islossless P.fi → islossless F.f → islossless D(F, P).distinguish)

set_option maxHeartbeats 8000000 in
-- one declaration: EC's call over three oracles, with their twelve goals; each `conseq` with a
-- pilot oracle lemma (EC's paths) matches the old declarations' views at ~2M (gap list)
include D_ll in
/-- EC's `equiv CF_G1 : CF(DRestr(D)).main ~ G1(DRestr(D)).main : ={glob D} ==>
!(G1.bcol \/ G1.bext){2} => ={res}`, its proof EC's (see the module docstring). -/
theorem CF_G1 : equiv[ CF(DRestr(D)).main ~ G1(DRestr(D)).main :
    ={glob D} ==> ¬(§G1.bcol{2} ∨ §G1.bext{2}) → ={res} ] := by
  unfold CF -- the old port declares `CF` a `def`, not an alias
  equiv_proc; stmt_inline*; stmt_wp
  equiv_call (_ : §G1.bcol ∨ §G1.bext,
    ={glob C} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2},
    FMap.dom §C.queries{2} [])
  · exact D_ll
  -- proofs for G1.S.f
  -- equivalence up to bad of PF.f and G1.S.f
  -- EC: + conseq (_: !G1.bcol{2} /\ !G1.bext{2} /\ ={x, glob C} /\ INV_CF_G1 … ==>
  --         !G1.bcol{2} => !G1.bext{2} => ={res, glob C} /\ INV_CF_G1 …).
  --       + by move=> &1 &2; rewrite negb_or.
  --       + progress;have[]:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0;smt(domE).
  --       conseq(eq_f D);progress=>/#.
  --     (our up-to-bad call asks one judgment `if bad then … else …` per oracle, which is
  --     `eq_f`'s own: EC's intermediate `conseq` is not needed)
  · equiv_conseq eq_f
    · auto_close
    · auto_close
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
  -- EC: + conseq(eq_fi D)=>/#.
  · equiv_conseq eq_fi
    · auto_close
    · auto_close
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
  -- EC: + conseq(PFf_Cf D);auto=>/#.
  · equiv_conseq PFf_Cf
    · auto_close
    · auto_close
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
