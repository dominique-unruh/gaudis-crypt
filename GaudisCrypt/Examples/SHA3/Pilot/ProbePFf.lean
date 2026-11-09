import GaudisCrypt.Examples.SHA3.Pilot.Handle
import GaudisCrypt.Logic.ECLoop
import GaudisCrypt.Logic.ECAlias
import GaudisCrypt.Logic.ECGoals
import GaudisCrypt.Logic.StmtSwap

namespace GaudisCrypt.SHA3.Pilot.Handle

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.ConcreteF
open GaudisCrypt.SHA3.Handle

variable [SLCommon.Params]

grind_pattern prefix_sizel => «prefix» l1 l2

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
* GAP 2: `equiv_while`'s `exit` has no frame of the variables the loop does not modify (EC's
  `while` keeps them): `={bs}` added to the first loop's invariant.
* GAP 4: a clone's op given as a function (`op dout _ <- bdistr`) is not substituted and
  beta-reduced in code as in EC: `r <$ F.dout x` reads `x`, so EC's `swap{2} 4 -3` fails.
* GAP 3: `grind` patterns of arithmetic lemmas are their normalized inequalities
  (`prefix_sizel`), which never match: `grind_pattern prefix_sizel => «prefix» l1 l2` (to move
  next to the lemma, `SLCommonCore`).
-/

set_option maxHeartbeats 8000000 in
theorem PFf_Cf' : equiv[ DFRestr(SqueezelessSponge(PF)).f ~ DFRestr(G1.M).f :
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
  --     (our `while` leaves `body`, `guard`, `exit`, `hpre`: EC's second goal is `guard`, `exit`
  --     and `hpre` together)
  -- GAP 2: `={bs}` is not EC's: EC's `while` keeps what the loop does not modify (`bs{1}`) by
  -- itself; our `equiv_while` has no frame on `exit`
  · equiv_while (={p, i, glob C, bs} ∧ §bs{2} = §p{2} ∧ (§i{2} = 0 → §sa{1} = b0) ∧
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
    case guard => auto_close
    -- EC (of the second goal): smt(prefix_sizel).
    case exit =>
      auto_prep
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at *
      smt_close [prefix_sizel]
    -- EC: - auto;progress.
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
        auto_prep
        by_contra hsz
        simp only [size, not_lt, Nat.cast_nonpos, List.length_eq_zero_iff] at hsz
        subst hsz; simp_all [FMap.domE]
    case body =>
      -- EC: case(G1.bcol{2} \/ G1.bext{2}).
      equiv_case (§G1.bcol{2} ∨ §G1.bext{2})
      -- EC: - by if{1};auto;conseq(:_==> (G1.bcol{2} \/ G1.bext{2}));1,3:smt(domE get_setE);
      --         (if{2};2:if{2});auto;1:smt(DBlock.dunifin_ll DCapacity.dunifin_ll);
      --         sp;if{1};auto;smt(DBlock.dunifin_ll DCapacity.dunifin_ll).
      · stmt_if{1} <;> (equiv_auto <;> equiv_conseq (: _ ==> §G1.bcol{2} ∨ §G1.bext{2}) <;> [
          (auto_prep
           all_goals (split_ands <;> (try omega) <;> (try simp only [Prod.mk.eta]) <;>
             (try (apply FMap.get_some; simp_all)) <;> (try simp_all [FMap.domE])));
          (stmt_if{2}; on_goals 2 => stmt_if{2})])
        all_goals equiv_auto
        all_goals try (stmt_sp; stmt_if{1} <;> equiv_auto)
        -- EC's `smt(DBlock.dunifin_ll DCapacity.dunifin_ll)`: the samplings are lossless, the bad
        -- event stays
        all_goals (auto_prep
                   all_goals simp_all [F.dout, bdistr_expected_one, cdistr_expected_one, ite_self])
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
      --     (GAP 2: `={bs}` kept, as in the invariant)
      · equiv_conseq (: ={p, i, glob C, bs} ∧ §bs{2} = §p{2} ∧ (§i{2} = 0 → §sa{1} = b0) ∧
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
          all_goals (split_ands <;> (try rfl) <;> (try assumption) <;> (try omega) <;>
            (try exact PFf_Cf_dom_next _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_›) <;>
            (try (glob_tuples; simp_all)) <;> (try (intro; simp_all)))
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
        rintro p₁ i₁ c₁ q₁ bs₁ sa₁ pref sc₁ m₁ mi₁ p₂ i₂ c₂ q₂ bs₂ bcol bext hs ch gm gmi mh mhi ro paths
          sa₂ cnt h ⟨⟨hp, hi, ⟨hc, hqq⟩, hbs⟩, hbs2, hsa0, hi0, hiq, hpref, hq0, hq, hdom, hJ,
            ⟨hi1, hi1'⟩, -, -, hbad, hdom1, hsz⟩
        subst hp hi hc hqq hbs
        obtain ⟨hI, rfl, hcnt, ⟨f, hh⟩, hb, hif⟩ := hJ hbad
        have hJ1 : PJ1 hs ch m₁ mi₁ gm gmi mh mhi ro paths pref q₁ p₁ i₁ sa₁ sc₁ h :=
          ⟨hI, hpref, ⟨f, hh⟩, hb, by simpa using hif, hi0, hiq, hq, hsz⟩
        obtain ⟨-, -, he, hI', hpref', hh', hb', hif', hi0', hiq', -, -⟩ :=
          PJ1_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hJ1 hi1'
        refine ⟨⟨rfl, rfl, ⟨rfl, rfl⟩, rfl⟩, hbs2, fun h0 => absurd h0 (by omega), by omega, hiq',
          hpref', hdom1, hq0, hq, fun _ => ⟨hI', he, hcnt, hh', by rw [← he]; exact hb', ?_⟩, hsz⟩
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
  equiv_while (={i, p, C.queries, C.c} ∧
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
        all_goals (try simp only [Bool.and_eq_true, decide_eq_true_eq] at *)
        all_goals (split_ands <;> (try omega) <;> (try simp_all))
      -- EC's closer of every leaf below: smt(get_setE mem_set DBlock.dunifin_ll DCapacity.dunifin_ll)
      -- EC: if {1}; last first.
      stmt_if{1}; rotate_right
      -- EC: + sp; if {1}; if {2}; last first.
      · stmt_sp; stmt_if{1} <;> stmt_if{2}
        rotate_right
        -- EC: + if {2}; sp; auto=> />. (+ smt …) smt …
        · stmt_if{2} <;> (stmt_sp; equiv_auto) <;> (pf_bad_leaf)
        -- EC: + auto=> />. smt …
        · equiv_auto; pf_bad_leaf
        -- EC: + if {2}; last first. + auto=> />. smt … + swap {2} 4 -3; auto=> />. smt …
        · stmt_if{2}; rotate_right
          · equiv_auto; pf_bad_leaf
          -- GAP 4: our clone keeps `r <$ F.dout x` (EC's `op dout _ <- bdistr` substitutes
          -- `bdistr`), so the sampling reads `x` and does not swap; our `auto` couples without it
          · equiv_auto; pf_bad_leaf
        -- EC: auto=> />. smt …
        · equiv_auto; pf_bad_leaf
      -- EC: if {2}. + auto=> />. smt …  if {2}. + auto=> />. smt …  auto=> />. smt …
      · stmt_if{2}
        · equiv_auto; pf_bad_leaf
        · stmt_if{2}
          · equiv_auto; pf_bad_leaf
          · equiv_auto; pf_bad_leaf
    trace "W2 GOOD"; trace_state; sorry

end GaudisCrypt.SHA3.Pilot.Handle
