import GaudisCrypt.Examples.SHA3.Pilot.Gconcl
import GaudisCrypt.Examples.SHA3.SHA3Indiff

/-!
# Indifferentiability of the sponge (EasyCrypt `proof/SHA3Indiff.ec`) — EC-fidelity port

The lemmas of `SHA3Indiff.ec` in EC's scripts, over the old port's declarations of `Simulator`,
`Cntr`, `FC`, `PC`, `DRestr` (`SHA3Indiff.lean`), as `Pilot/Gconcl.lean` over the old `Gconcl`.

Translation:
* `require import Common Sponge. import BIRO.` is the `open` below.
* EC's section `declare module Dist <: DISTINGUISHER {-…}` and `declare axiom Dist_lossless` are a
  `declare module` and a variable; the restriction also names the modules of the files whose
  lemmas the proofs use (fresh in EC).
-/

/-! Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* GAP 1: inline by name: EC's paths over `Perm` (`BlockSponge.FC(BlockSponge.Sponge(Perm)).f`) do
  not elaborate over the old declarations (`Perm` is not a `BlockSponge.DPRIMITIVE`; Gcol's GAP 2):
  by index.
-/

-- EasyCrypt names the final lemma like its file (`SHA3Indiff.SHA3Indiff`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.Pilot.SHA3Indiff

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.Sponge
open GaudisCrypt.SHA3.Sponge.BIRO
open GaudisCrypt.SHA3.SHA3Indiff (Simulator Cntr FC PC DRestr limit)

export GaudisCrypt.SHA3.Sponge (PRIMITIVE)

variable [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params]

section

declare module Dist <: DISTINGUISHER {-Perm, -Gconcl_list.SimLast, -IRO, -Cntr,
  -BlockSponge.BIRO.IRO, -Simulator, -BlockSponge.C, -Gconcl.S, -SLCommon.F.RO, -SLCommon.F.FRO,
  -SLCommon.Redo, -SLCommon.C, -Gconcl_list.BIRO2.IRO, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
  -Gconcl_list.Simulator}

-- EC's `declare axiom Dist_lossless`
variable (Dist_lossless : ∀ (F <: DFUNCTIONALITY {-Dist}), ∀ (P <: DPRIMITIVE {-Dist}),
  islossless P.f → islossless P.fi → islossless F.f → islossless Dist(F, P).distinguish)

set_option maxHeartbeats 4000000 in
/-- EC's `lemma drestr_commute1 &m`. -/
theorem drestr_commute1 (m : VariableAssignment) :
    Pr[ BlockSponge.RealIndif(BlockSponge.Sponge, Perm, LowerDist(DRestr(Dist))).main ()
        @ &m : §res ] =
      Pr[ BlockSponge.RealIndif(BlockSponge.Sponge, Perm, BlockSponge.DRestr(LowerDist(Dist))).main
        () @ &m : §res ] := by
  -- EC: byequiv=> //; proc.
  byequiv; equiv_proc
  -- EC: seq 2 2 : (={glob Dist} /\ ={Perm.m, Perm.mi} ); first sim.
  equiv_seq 2 2 : (={glob Dist, Perm.m, Perm.mi})
  · sim
  -- EC: inline*; wp; sp.
  stmt_inline*; stmt_wp; stmt_sp
  -- EC: call (_ : ={c}(Cntr, BlockSponge.C) /\ ={Perm.m, Perm.mi}).
  equiv_call (_ : ={Perm.m, Perm.mi} ∧ §Cntr.c{1} = §BlockSponge.C.c{2})
  -- EC: proc; sp; if=> //; sp; sim.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    all_goals (stmt_sp; sim)
  -- EC: proc; sp; if=> //; sp; sim.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    all_goals (stmt_sp; sim)
  -- EC: proc=> /=.
  --     inline BlockSponge.FC(BlockSponge.Sponge(Perm)).f.
  · equiv_proc
    --     (GAP 1: inline by index, the only call on the right: EC's path `BlockSponge.FC(…(Perm))`
    --     does not elaborate over the old declarations, `Perm` is not a `BlockSponge.DPRIMITIVE`)
    stmt_inline{2} 0
    -- EC: wp; sp.
    stmt_wp; stmt_sp
    -- EC: if=> //.
    stmt_if
    -- EC: progress; smt(size_pad2blocks).
    · smt_close [size_pad2blocks]
    -- EC: seq 1 1 :
    --   (={n} /\ nb{2} = (n{2} + r - 1) %/ r /\ bl{2} = pad2blocks bs{1} /\
    --    Cntr.c{1} = BlockSponge.C.c{2} /\ ={Perm.m, Perm.mi}).
    --   auto; progress; by rewrite size_pad2blocks.
    · equiv_seq 1 1 : (={n, Perm.m, Perm.mi} ∧ §nb{2} = (§n{2} + r - 1) / r ∧
          §bl{2} = pad2blocks §bs{1} ∧ §Cntr.c{1} = §BlockSponge.C.c{2})
      · equiv_auto; auto_progress
        smt_close [size_pad2blocks]
      -- EC: inline RaiseFun(BlockSponge.Sponge(Perm)).f.
      --     (GAP 1: by index)
      stmt_inline{1} 0
      -- EC: wp; sp.
      stmt_wp; stmt_sp
      -- EC: call (_ : ={Perm.m, Perm.mi}); first sim.
      --     (the callees' judgment, EC's `first sim`, closed by `equiv_call`: the same procedure)
      equiv_call (_ : ={Perm.m, Perm.mi})
      -- EC: auto.
      equiv_auto
    -- EC: auto; progress; by rewrite blocks2bits_nil.
    · equiv_auto; auto_progress
      simp [blocks2bits_nil, take]
  --     (the code before the call: `auto`)
  · equiv_auto

set_option maxHeartbeats 4000000 in
/-- EC's `lemma drestr_commute2 &m`. -/
theorem drestr_commute2 (m : VariableAssignment) :
    Pr[ BlockSponge.IdealIndif(BlockSponge.BIRO.IRO.asF, Gconcl_list.SimLast(Gconcl.S),
        LowerDist(DRestr(Dist))).main () @ &m : §res ] =
      Pr[ BlockSponge.IdealIndif(BlockSponge.BIRO.IRO.asF, Gconcl_list.SimLast(Gconcl.S),
        BlockSponge.DRestr(LowerDist(Dist))).main () @ &m : §res ] := by
  -- EC: byequiv=> //; proc.
  byequiv; equiv_proc
  -- EC: seq 2 2 :
  --   (={glob Dist, BlockSponge.BIRO.IRO.mp,
  --      glob Gconcl_list.SimLast(Gconcl.S)}); first sim.
  equiv_seq 2 2 : (={glob Dist, BlockSponge.BIRO.IRO.mp, Gconcl.S.m, Gconcl.S.mi, Gconcl.S.paths,
      Gconcl_list.BIRO2.IRO.mp})
  · sim
  -- EC: inline*; wp; sp.
  stmt_inline*; stmt_wp; stmt_sp
  trace_state
  sorry

end

end GaudisCrypt.SHA3.Pilot.SHA3Indiff
