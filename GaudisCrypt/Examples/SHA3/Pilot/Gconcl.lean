import GaudisCrypt.Examples.SHA3.Pilot.Gext
import GaudisCrypt.Examples.SHA3.SmartCounter.Gconcl

/-!
# Conclusion of the squeezeless sponge proof (EasyCrypt `proof/smart_counter/Gconcl.ec`) —
EC-fidelity port

The equivalences `G2_G3`, `G3_G4`, `G4_Ideal` in EC's scripts, over the old port's declarations of
`IF`, `S`, `G3`, `G4` (`SmartCounter/Gconcl.lean`), as `Pilot/Gext.lean`.

Translation:
* EC's local `G3(RO)`, `G4(RO)` take `D` as a Lean parameter (the section's `D`): `G3(D, F.LRO)`
  for EC's `G3(F.LRO)`;
* `declare module D <: DISTINGUISHER {-C, -Perm, -F.RO, -F.FRO, -S, -Redo}` with the section's
  `local clone import Gext as Gext0`: the clone's modules are fresh for `D` in EC, here `D`'s
  restriction names them (`G1`, `FRO.m`).
-/

/-! Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* GAP 1: EC's `sim` goes into calls of different concrete procedures (`G4.S(F.LRO).f` against
  `S(IF).f`); ours stops there: `stmt_inline*` first.
* GAP 3: a procedure's parameter (`x` of `G3.S.f`) is not a name of the conditions after `proc`
  (Gext's GAP 4): its read `(localVarLens "x" SLCommon.state)` written out.
* GAP 4: EC's `swap{1} [3..7] -2` in `G2_G3`'s `S.f` (`RRO`'s calls past the conditional
  calling `F.RO.get`).  Footprint disjointness does not apply (both read `x`).  Tried (2026-11-11):
  inlining the `RRO` calls and `F.RO.get` first (EC's later `inline *`) makes the moved block
  deterministic, and the first moved statement then swaps; the next (a deterministic `if` with a
  `reset_vars` in its branch) fails in `StmtSwap.discharge`: it cannot push the left's tuple
  assignment `p, v <- …` through that `if`'s update.  A discharger gap, not read/write sets.
  `G2_G3`'s `S.f` bullet is a `sorry` until then.
* GAP 5: `sim` stops at two loops after `inline*` (`G2_G3`'s `M.f` callee) where EC's goes
  through: `equiv_while` with EC's equality set, the bodies by `sim`.
* GAP 2: the one-sided `equiv_while{i}` has no frame of the variables the loop keeps (the
  two-sided `while` has, `Logic/ECWhileRel.lean`): they go into the invariant.
-/

namespace GaudisCrypt.SHA3.Pilot.Gconcl

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.ConcreteF
open GaudisCrypt.SHA3.Handle
open GaudisCrypt.SHA3.Gext (G2 G2.M G2.S Eager Eager.main2 RRO)
open GaudisCrypt.SHA3.Gconcl (IF S G3 G3.M G3.S G4 G4.C G4.S)

variable [SLCommon.Params]

section

declare module D <: DISTINGUISHER {-C, -Perm, -F.RO, -F.FRO, -S.m, -S.mi, -S.paths, -Redo, -G1,
  -FRO.m}

set_option maxHeartbeats 8000000 in
/-- EC's `local equiv G2_G3: Eager(G2(DRestr(D))).main2 ~ G3(F.LRO).distinguish : ={glob D} ==>
={res}`. -/
theorem G2_G3 : equiv[ Eager(G2(DRestr(D))).main2 ~ G3(D, F.LRO).distinguish :
    ={glob D} ==> ={res} ] := by
  -- EC: proc;wp;call{1} RRO_resample_ll;inline *;wp.
  equiv_proc; stmt_wp
  equiv_call{1} (PROM.FullRO.FullEager.RRO_resample_ll handle capacity ROhandle.dout
    ROhandle.FRO.m (fun _ => BitWord.dunifin_ll))
  stmt_inline*; stmt_wp
  -- EC: call (_: ={FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c,C.queries});
  --       last by auto.
  equiv_call (_ : ={FRO.m, F.RO.m, G1.m, G1.mi, G1.mh, G1.mhi, G1.chandle, G1.paths, C.c,
    C.queries})
  -- EC: + proc;sp;if=> //;sim 1 1.
  --       call (_: ={FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c,C.queries});
  --       2:by auto.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    sim 1 1
    equiv_call (_ : ={FRO.m, F.RO.m, G1.m, G1.mi, G1.mh, G1.mhi, G1.chandle, G1.paths, C.c,
      C.queries})
    on_goals 2 => (equiv_auto; auto_close)
    -- EC: if=> //;2:by sim.
    equiv_proc; stmt_if
    · auto_close
    on_goals 2 => sim
    -- EC: swap{1} [3..7] -2;swap{2} [4..8] -3.
    --     seq 5 5:(={hx2,t,x,FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c,
    --              C.queries} /\ (t = in_dom_with FRO.m (oget G1.mh.[(x.`1, hx2)]).`2 Unknown){1});
    --       1:by inline *;auto.
    --     seq 3 4:(={y,x,FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c,C.queries});
    --       2:by sim.
    --     if=>//.
    --     + seq 2 2:(={y1,hx2,t,x,FRO.m,…} /\ (t = in_dom_with FRO.m (oget G1.mh.[(x.`1, hx2)]).`2
    --                Unknown){1}).
    --       + by inline *;auto=> /> ? _;rewrite Block.DWord.bdistr_ll.
    --       case (((x.`1, hx2) \in G1.mh /\ t){1});
    --           [rcondt{1} 3;2:rcondt{2} 3| rcondf{1} 3;2:rcondf{2} 3];
    --           1,2,4,5:(by move=>?;conseq (_:true);auto);2:by sim.
    --       inline *;rcondt{1} 6;1:by auto=>/>.
    --       by auto => /> *; rewrite !get_setE.
    --     case (((x.`1, hx2) \in G1.mh /\ t){1});
    --           [rcondt{1} 4;2:rcondt{2} 4| rcondf{1} 4;2:rcondf{2} 4];
    --           1,2,4,5:(by move=>?;conseq (_:true);auto);2:by sim.
    --     inline *;rcondt{1} 7;1:by auto=>/>.
    --     by wp;rnd;auto;rnd{1};auto => /> *; rewrite !get_setE.
    --     (GAP 4: our `swap` cannot move the `RRO` calls past the conditional calling `F.RO.get`
    --     (EC: their footprints are disjoint); the bullet waits for it)
    sorry
  -- EC: + proc;sp;if=>//;sim 1 1.
  --       call (_: ={FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c,C.queries});
  --       2:by auto.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    sim 1 1
    equiv_call (_ : ={FRO.m, F.RO.m, G1.m, G1.mi, G1.mh, G1.mhi, G1.chandle, G1.paths, C.c,
      C.queries})
    on_goals 2 => (equiv_auto; auto_close)
    -- EC: if=> //;2:sim.
    equiv_proc; stmt_if
    · auto_close
    on_goals 2 => sim
    -- EC: swap{1} 8 -3.
    stmt_swap{1} 8 -3
    -- EC: seq 6 6 : (={y1,hx2,t,x,FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c,
    --                 C.queries} /\ (t = in_dom_with FRO.m (oget G1.mhi.[(x.`1, hx2)]).`2 Unknown){1}).
    --     + by inline *;auto.
    equiv_seq 6 6 : (={y1, hx2, t, (localVarLens "x" SLCommon.state), FRO.m, F.RO.m, G1.m, G1.mi,
        G1.mh, G1.mhi, G1.chandle, G1.paths, C.c, C.queries} ∧
      §t{1} = decide (FMap.in_dom_with §FRO.m{1}
        (oget (FMap.get §G1.mhi{1} ((§(localVarLens "x" SLCommon.state){1}).1, §hx2{1}))).2 Unknown))
    · stmt_inline*; equiv_auto; auto_close
    -- EC: case (((x.`1, hx2) \in G1.mhi /\ t){1});
    --       [rcondt{1} 3;2:rcondt{2} 3| rcondf{1} 3;2:rcondf{2} 3];
    --       1,2,4,5:(by move=>?;conseq (_:true);auto);2:by sim.
    equiv_case (FMap.dom §G1.mhi{1} ((§(localVarLens "x" SLCommon.state){1}).1, §hx2{1}) ∧
      §t{1} = true)
    · stmt_rcondt{1} 3
      · hoare_auto
      stmt_rcondt{2} 3
      · hoare_auto
      -- EC: inline *;rcondt{1} 6;1:by auto=>/>.
      stmt_inline*; stmt_rcondt{1} 6
      · hoare_auto; simp only [FMap.in_dom_with, PROM.is_, oget] at *; auto_close
      -- EC: by auto => /> *; rewrite !get_setE.
      equiv_auto; auto_progress
      all_goals simp only [FMap.get_set_sameE, oget_some]
    · stmt_rcondf{1} 3
      · hoare_auto
      stmt_rcondf{2} 3
      · hoare_auto
      sim
  -- EC: proc;sp;if=>//;auto;if;[1,3:by auto];sim 2 2.
  --     call (_: ={FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c,C.queries});
  --       2:by auto.
  --     by inline*;sim.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    stmt_sp; stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    sim 2 2
    equiv_call (_ : ={FRO.m, F.RO.m, G1.m, G1.mi, G1.mh, G1.mhi, G1.chandle, G1.paths, C.c,
      C.queries})
    on_goals 2 => (equiv_auto; auto_close)
    equiv_proc; stmt_inline*; sim
    --     (GAP 5: our `sim` stops at the two loops here: EC's equality set as their invariant)
    equiv_while (={i, p, h, counter, sa, FRO.m, F.RO.m, G1.m, G1.mi, G1.mh, G1.mhi, G1.chandle,
      G1.paths, C.c, C.queries})
    · sim
    · equiv_auto
  -- EC: last by auto.
  · equiv_auto; auto_close

set_option maxHeartbeats 4000000 in
/-- EC's `local equiv G3_G4 : G3(F.RO).distinguish ~ G4(F.RO).distinguish : ={glob D} ==>
={res}`. -/
theorem G3_G4 : equiv[ G3(D, F.RO.asRO).distinguish ~ G4(D, F.RO.asRO).distinguish :
    ={glob D} ==> ={res} ] := by
  -- EC: proc;inline *;wp.
  equiv_proc; stmt_inline*; stmt_wp
  -- EC: call (_: ={G1.m,G1.mi,G1.paths,F.RO.m,C.c,C.queries});last by auto.
  equiv_call (_ : ={G1.m, G1.mi, G1.paths, F.RO.m, C.c, C.queries})
  -- EC: + proc;sp;if=>//;sim 1 1.
  --       call (_: ={G1.m,G1.mi,G1.paths,F.RO.m,C.c,C.queries});last by auto.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    sim 1 1
    equiv_call (_ : ={G1.m, G1.mi, G1.paths, F.RO.m, C.c, C.queries})
    on_goals 2 => (equiv_auto; auto_close)
    -- EC: if => //;2:sim.
    equiv_proc; stmt_if
    · auto_close
    on_goals 2 => sim
    -- EC: seq 3 3: (={x,y1,y2,y,G1.m,G1.mi,G1.paths,F.RO.m,C.c,C.queries});1:by sim.
    --     (GAP 3: the procedure's parameter `x` written as its read)
    equiv_seq 3 3 : (={(localVarLens "x" SLCommon.state), y1, y2, y, G1.m, G1.mi, G1.paths,
      F.RO.m, C.c, C.queries})
    · sim
    -- EC: sim;seq 5 0: (={x,y1,y2,y,G1.m,G1.mi,G1.paths,F.RO.m,C.c,C.queries});
    --       1:by inline *;auto.
    sim
    equiv_seq 5 0 : (={(localVarLens "x" SLCommon.state), y1, y2, y, G1.m, G1.mi, G1.paths, F.RO.m,
      C.c, C.queries})
    · stmt_inline*; equiv_auto
    -- EC: by if{1};sim;inline *;auto.
    stmt_if{1}
    all_goals sim
    stmt_inline*; equiv_auto
  -- EC: + proc;sp;if=>//;sim 1 1.
  --       call (_: ={G1.m,G1.mi,G1.paths,F.RO.m,C.c,C.queries});last by auto.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    sim 1 1
    equiv_call (_ : ={G1.m, G1.mi, G1.paths, F.RO.m, C.c, C.queries})
    on_goals 2 => (equiv_auto; auto_close)
    -- EC: if => //;2:sim.
    equiv_proc; stmt_if
    · auto_close
    on_goals 2 => sim
    -- EC: seq 5 0: (={x,G1.m,G1.mi,G1.paths,F.RO.m,C.c,C.queries});1:by inline *;auto.
    equiv_seq 5 0 : (={(localVarLens "x" SLCommon.state), G1.m, G1.mi, G1.paths, F.RO.m, C.c,
      C.queries})
    · stmt_inline*; equiv_auto
    -- EC: seq 3 3: (={x,y1,y2,y,G1.m,G1.mi,G1.paths,F.RO.m,C.c,C.queries});1:by sim.
    equiv_seq 3 3 : (={(localVarLens "x" SLCommon.state), y1, y2, y, G1.m, G1.mi, G1.paths,
      F.RO.m, C.c, C.queries})
    · sim
    -- EC: by if{1};sim;inline *;auto.
    stmt_if{1}
    all_goals sim
    stmt_inline*; equiv_auto
  -- EC: proc;sp;if=>//;auto;if=>//;sim 2 2.
  --     call (_: ={G1.m,G1.mi,G1.paths,F.RO.m,C.c,C.queries});last by auto.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    stmt_sp; stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    sim 2 2
    equiv_call (_ : ={G1.m, G1.mi, G1.paths, F.RO.m, C.c, C.queries})
    on_goals 2 => (equiv_auto; auto_close)
    -- EC: sp;sim; while(={i,p,F.RO.m})=>//.
    equiv_proc; stmt_sp; sim
    equiv_while (={i, p, F.RO.m})
    -- EC: inline F.RO.sample F.RO.get;if{1};1:by auto.
    · stmt_inline*
      stmt_if{1}
      · equiv_auto
      -- EC: if{1};2:by auto.
      stmt_if{1}
      on_goals 2 => equiv_auto
      -- EC: by sim;inline *;auto;progress;smt(DCapacity.dunifin_ll).
      sim; equiv_auto
    · equiv_auto
  -- EC: last by auto.
  · equiv_auto; auto_close

set_option maxHeartbeats 4000000 in
/-- EC's `local equiv G4_Ideal : G4(F.LRO).distinguish ~ IdealIndif(IF,S,DRestr(D)).main :
={glob D} ==> ={res}`. -/
theorem G4_Ideal : equiv[ G4(D, F.LRO).distinguish ~ IdealIndif(IF, S, DRestr(D)).main :
    ={glob D} ==> ={res} ] := by
  -- EC: proc;inline *;wp.
  equiv_proc; stmt_inline*; stmt_wp
  -- EC: call (_: ={C.c,C.queries,F.RO.m} /\ G1.m{1}=S.m{2} /\ G1.mi{1}=S.mi{2} /\
  --          G1.paths{1}=S.paths{2}).
  equiv_call (_ : ={C.c, C.queries, F.RO.m} ∧ §G1.m{1} = §S.m{2} ∧ §G1.mi{1} = §S.mi{2} ∧
    §G1.paths{1} = §S.paths{2})
  -- EC: + by sim. + by sim.
  --     (GAP 1: our `sim` stops at calls of different procedures: inlined first; what it leaves
  --     before the code, by `auto_close`)
  · equiv_proc; stmt_inline*; sim; auto_close
  · equiv_proc; stmt_inline*; sim; auto_close
  -- EC: + proc;sp;if=>//;auto;if=>//;auto.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    on_goals -1 => equiv_auto
    stmt_sp; stmt_if
    · auto_close
    on_goals -1 => equiv_auto
    -- EC: call (_: ={F.RO.m});2:by auto.
    stmt_wp; equiv_call (_ : ={F.RO.m})
    on_goals 2 => (equiv_auto; auto_close)
    -- EC: inline F.LRO.get F.FRO.sample;wp 7 2;sim.
    equiv_proc; stmt_inline*; stmt_wp 7 2; sim
    -- EC: by while{1} (true) (size p - i){1};auto;1:inline*;auto=>/#.
    --     (GAP 2: our one-sided `while` has no frame of what the loop keeps: `p{1} = x{2}` and
    --     `={F.RO.m}` in the invariant, EC's `true`)
    equiv_while{1} (§p{1} = §x{2} ∧ §F.RO.m{1} = §F.RO.m{2}) ((size §p{1} - §i{1}).toNat)
    · while_ll_phoare
      intro σ₂
      phoare_auto
    · intro σ₂ k
      hoare_auto
    · auto_progress
    · equiv_auto
  -- EC: by auto.
  · equiv_auto; auto_close

end

/-! ## `Real_Ideal`

`D`'s restriction also names the local modules of `Gext`, `Gcol` and `ConcreteF` (fresh in EC)
that `Real_G2` excludes. -/

-- EC reads the games' globals off their code (for `RO_LRO_D`'s side conditions)
attribute [fp_bound] GaudisCrypt.SHA3.Gconcl.fvP_G3 GaudisCrypt.SHA3.Gconcl.fvP_G4

section REAL

declare module D <: DISTINGUISHER {-C, -Perm, -F.RO, -F.FRO, -S.m, -S.mi, -S.paths, -Redo, -G1,
  -G2, -PF, -FRO.m, -ROhandle.RO, -Pilot.Gext.ReSample.count, -Pilot.Gcol.Gcol.sample_c,
  -Pilot.ConcreteF.Switching.DBounder, -Pilot.ConcreteF.Switching.ARP,
  -Pilot.ConcreteF.Switching.PRPi.PRPi}

-- EC's `declare axiom D_ll`
variable (D_ll : ∀ (F <: DFUNCTIONALITY {-D}), ∀ (P <: DPRIMITIVE {-D}),
  islossless P.f → islossless P.fi → islossless F.f → islossless D(F, P).distinguish)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
include D_ll in
/-- EC's `lemma Real_Ideal &m: Pr[GReal(D).main() @ &m: res /\ C.c <= max_size] <=
Pr[IdealIndif(IF,S,DRestr(D)).main() @ &m :res] + (max_size ^ 2 - max_size)%r / 2%r * mu dstate
(pred1 witness) + max_size%r * ((2*max_size)%r / (2^c)%r) +
max_size%r * ((2*max_size)%r / (2^c)%r)`. -/
theorem Real_Ideal (m : VariableAssignment) :
    Pr[ (Pilot.SLCommon.GReal D) () @ &m : §res ∧ §C.c ≤ max_size ] ≤
      Pr[ IdealIndif(IF, S, DRestr(D)).main () @ &m : §res ] +
        ((max_size ^ 2 - max_size : ℤ) : ℝ) / 2 * (dstate.1 {default}).toReal +
        (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) +
        (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) := by
  -- EC: apply (ler_trans _ _ _ (Real_G2 D D_ll &m)).
  refine le_trans (Pilot.Gext.Real_G2 D D_ll m) ?_
  -- EC: rewrite !(ler_add2l, ler_add2r);apply lerr_eq.
  suffices e : Pr[ Eager(G2(DRestr(D))).main2 (()) @ &m : §res ] =
      Pr[ IdealIndif(IF, S, DRestr(D)).main () @ &m : §res ] by
    rw [e]
  -- EC: apply (eq_trans _ Pr[G3(F.LRO).distinguish() @ &m : res]);1:by byequiv G2_G3.
  refine Eq.trans (b := Pr[ G3(D, F.LRO).distinguish (()) @ &m : §res ]) ?_ ?_
  · byequiv (G2_G3 D)
  -- EC: apply (eq_trans _ Pr[G3(F.RO ).distinguish() @ &m : res]).
  --     + byequiv (_: ={glob G3, F.RO.m} ==> _)=>//;symmetry;conseq (F.FullEager.RO_LRO_D G3 _)=> //.
  --       by move=> _; exact/Block.DBlock.dunifin_ll.
  refine Eq.trans (b := Pr[ G3(D, F.RO.asRO).distinguish (()) @ &m : §res ]) ?_ ?_
  · symm
    byequiv (PROM.FullRO.FullEager.RO_LRO_D (List block) block Unit Bool F.dout F.FRO.m
      (fun _ => BitWord.dunifin_ll) F.RO.m (G3 D) (by ec_module) (by fp_disjoint))
  -- EC: apply (eq_trans _ Pr[G4(F.RO ).distinguish() @ &m : res]);1:by byequiv G3_G4.
  refine Eq.trans (b := Pr[ G4(D, F.RO.asRO).distinguish (()) @ &m : §res ]) ?_ ?_
  · byequiv (G3_G4 D)
  -- EC: apply (eq_trans _ Pr[G4(F.LRO).distinguish() @ &m : res]).
  --     + byequiv (F.FullEager.RO_LRO_D G4 _)=> //.
  --       by move=> _; exact/Block.DBlock.dunifin_ll.
  refine Eq.trans (b := Pr[ G4(D, F.LRO).distinguish (()) @ &m : §res ]) ?_ ?_
  · byequiv (PROM.FullRO.FullEager.RO_LRO_D (List block) block Unit Bool F.dout F.FRO.m
      (fun _ => BitWord.dunifin_ll) F.RO.m (G4 D) (by ec_module) (by fp_disjoint))
  -- EC: by byequiv G4_Ideal.
  byequiv (G4_Ideal D)

end REAL

end GaudisCrypt.SHA3.Pilot.Gconcl
