import GaudisCrypt.Examples.SHA3.Pilot.Gconcl
import GaudisCrypt.Examples.SHA3.SHA3Indiff

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

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
* (GAP 3, fixed: `glob IRO` read off its code as `={IRO.mp}`, `Logic/GlobWrites.lean`; the call's
  frame through `RaiseSim(…)(IRO)`.)
* GAP 4: after `byequiv` (all globals equal) and `sp` over the initializations, the two memories'
  equation (`X.set v (…σ₁.globals) = Y.set w (…σ₂.globals)`) is not used for `glob D`'s
  equality: by hand (`congrArg` of `glob D`'s getter, `touched_set_of_le_compl`).
* GAP 5: `RaiseSim(S)` views `S`'s block-level procedures at the bit level (`PRIMITIVE`'s
  parameters spelled differently): the inliner applies `SimLast`'s `apply_simp` there only at
  default transparency, by `set_option inline.defEqApply true` (always on, it inlines further than
  the first port's proofs expect).
* GAP 2: our inliner renames a callee's locals per side (`x3, n0` against `x0, n` in
  `equiv_sim_f`'s IRO loops), so `sim` cannot relate loops by name where EC's does: `while` with
  the renamed variables' equalities.
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

/-- `RaiseSim(S)` touches what `S` and `LowerFun` touch (`Module.comp`).  Not an EC lemma. -/
@[fp_bound] theorem fvP_RaiseSim (S : BlockSponge.SIMULATOR) :
    FVP.fvP (RaiseSim S) ≤ FVP.fvP S ⊔ FVP.fvP LowerFun := by
  unfold RaiseSim; exact FVP.fvP_comp_le _ _

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
  -- EC: call
  --   (_ :  ={BlockSponge.BIRO.IRO.mp,Gconcl_list.BIRO2.IRO.mp} /\
  --    ={c}(Cntr, BlockSponge.C) /\
  --    ={glob Gconcl_list.SimLast(Gconcl.S)}).
  equiv_call (_ : ={BlockSponge.BIRO.IRO.mp, Gconcl_list.BIRO2.IRO.mp, Gconcl.S.m, Gconcl.S.mi,
      Gconcl.S.paths} ∧ §Cntr.c{1} = §BlockSponge.C.c{2})
  -- EC: proc; sp; if=> //; sim.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    all_goals sim
  -- EC: proc; sp; if=> //; sim.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    all_goals sim
  -- EC: proc=> /=.
  --     inline BlockSponge.FC(BlockSponge.BIRO.IRO).f.
  · equiv_proc
    --     (GAP 1: by index)
    stmt_inline{2} 0
    -- EC: sp; wp.
    stmt_sp; stmt_wp
    -- EC: if=> //.
    stmt_if
    -- EC: progress; smt(size_pad2blocks).
    · smt_close [size_pad2blocks]
    -- EC: seq 1 1 :
    --   (={n} /\ nb{2} = (n{2} + r - 1) %/ r /\ bl{2} = pad2blocks bs{1} /\
    --    Cntr.c{1} = BlockSponge.C.c{2} /\
    --    ={BlockSponge.BIRO.IRO.mp, Gconcl_list.BIRO2.IRO.mp,
    --      Gconcl.S.paths, Gconcl.S.mi, Gconcl.S.m}).
    -- EC: auto; progress.
    --     rewrite size_pad2blocks //.
    · equiv_seq 1 1 : (={n, BlockSponge.BIRO.IRO.mp, Gconcl_list.BIRO2.IRO.mp, Gconcl.S.paths,
          Gconcl.S.mi, Gconcl.S.m} ∧ §nb{2} = (§n{2} + r - 1) / r ∧
          §bl{2} = pad2blocks §bs{1} ∧ §Cntr.c{1} = §BlockSponge.C.c{2})
      · equiv_auto; auto_progress
        smt_close [size_pad2blocks]
      -- EC: inline RaiseFun(BlockSponge.BIRO.IRO).f.
      --     (GAP 1: by index)
      stmt_inline{1} 0
      -- EC: wp; sp.
      stmt_wp; stmt_sp
      -- EC: call (_ : ={BlockSponge.BIRO.IRO.mp}); first sim.
      --     (the callees' judgment, EC's `first sim`, closed by `equiv_call`: the same procedure)
      equiv_call (_ : ={BlockSponge.BIRO.IRO.mp})
      -- EC: auto.
      equiv_auto
    -- EC: by auto.
    · equiv_auto; auto_progress
      simp [blocks2bits_nil, take]
  --     (the code before the call: `auto`)
  · equiv_auto

set_option maxHeartbeats 4000000 in
-- (GAP 5: `RaiseSim(S)`'s bit-level view of `S`'s block-level procedures)
set_option inline.defEqApply true in
/-- EC's `local equiv equiv_sim_f (F <: DFUNCTIONALITY{-Gconcl.S, -Simulator}) :
RaiseSim(Gconcl_list.SimLast(Gconcl.S),F).f ~ Simulator(F).f : ={arg, glob F, glob
Gconcl_list.BIRO2.IRO} /\ ={m, mi, paths}(Gconcl.S,Simulator) ==> ={res, glob F, glob
Gconcl_list.BIRO2.IRO} /\ ={m, mi, paths}(Gconcl.S,Simulator)`. -/
theorem equiv_sim_f : ∀ (F <: DFUNCTIONALITY {-Gconcl.S, -Simulator}),
    equiv[ RaiseSim(Gconcl_list.SimLast(Gconcl.S), F).f ~ Simulator(F).f :
      ={arg, glob F, Gconcl_list.BIRO2.IRO.mp} ∧ §Gconcl.S.m{1} = §Simulator.m{2} ∧
        §Gconcl.S.mi{1} = §Simulator.mi{2} ∧ §Gconcl.S.paths{1} = §Simulator.paths{2} ==>
      ={res, glob F, Gconcl_list.BIRO2.IRO.mp} ∧ §Gconcl.S.m{1} = §Simulator.m{2} ∧
        §Gconcl.S.mi{1} = §Simulator.mi{2} ∧ §Gconcl.S.paths{1} = §Simulator.paths{2} ] := by
  intro F _
  -- EC: proc;inline*;if;1,3:auto=>/#.
  --     (our `inline*` leaves the parameter's assignment before the `if`: `sp` first)
  equiv_proc; stmt_inline*; stmt_sp; stmt_if
  · auto_close
  on_goals 2 => equiv_auto
  -- EC: wp;conseq(:_==> ={y1, y2, glob F, glob Gconcl_list.BIRO2.IRO}
  --   /\ ={m, mi, paths}(Gconcl.S,Simulator));progress;sim.
  stmt_wp
  equiv_conseq (: _ ==> ={y1, y2, glob F, Gconcl_list.BIRO2.IRO.mp} ∧
      §Gconcl.S.m{1} = §Simulator.m{2} ∧ §Gconcl.S.mi{1} = §Simulator.mi{2} ∧
      §Gconcl.S.paths{1} = §Simulator.paths{2})
  case post => auto_close
  sim
  -- EC: if;1,3:auto=>/#;wp;sp;if;1:(auto;smt(BlockSponge.parseK BlockSponge.formatK));
  --   last sim;smt(BlockSponge.parseK BlockSponge.formatK).
  stmt_if
  · auto_close
  on_goals 2 => equiv_auto
  stmt_wp; stmt_sp
  stmt_if
  · equiv_auto
    smt_close [BlockSponge.parseK, BlockSponge.formatK]
  --     (GAP 2: `last sim` — our inliner names the IRO's locals differently on the two sides,
  --     `x3, n0` against `x0, n`, so `sim` cannot relate the loops by name: EC's `while` with the
  --     renamed variables' equalities, the bodies by `sim`)
  on_goals -1 =>
    stmt_wp; stmt_sp; stmt_if
    · auto_close
    · equiv_while (§x3{1} = §(localVarLens "x0" (List block)){2} ∧ §n0{1} = §n{2} ∧
          ={i, bs, Gconcl_list.BIRO2.IRO.mp})
      · sim
      · equiv_auto
        smt_close [BlockSponge.parseK, BlockSponge.formatK]
    · equiv_auto
  -- EC: auto; rcondt {1} 5.
  stmt_wp; stmt_rcondt{1} 5
  -- EC: + by auto; call (: true); auto.
  --     (our code before the `if` has no call: `valid q` gives it, by definition)
  · hoare_auto
    smt_close [Gconcl_list.valid, valid_block]
  -- EC: by auto; call (: true); auto=> |> &1 &2; smt(BlockSponge.parseK BlockSponge.formatK).
  stmt_wp
  equiv_call (_ : ={glob F})
  equiv_auto
  smt_close [BlockSponge.parseK, BlockSponge.formatK]

set_option maxHeartbeats 4000000 in
-- (GAP 5: `RaiseSim(S)`'s bit-level view of `S`'s block-level procedures)
set_option inline.defEqApply true in
/-- EC's `local equiv equiv_sim_fi (F <: DFUNCTIONALITY{-Gconcl.S, -Simulator}) :
RaiseSim(Gconcl_list.SimLast(Gconcl.S),F).fi ~ Simulator(F).fi : ={arg, glob F, glob
Gconcl_list.BIRO2.IRO} /\ ={m, mi, paths}(Gconcl.S,Simulator) ==> ={res, glob F, glob
Gconcl_list.BIRO2.IRO} /\ ={m, mi, paths}(Gconcl.S,Simulator)`. -/
theorem equiv_sim_fi : ∀ (F <: DFUNCTIONALITY {-Gconcl.S, -Simulator}),
    equiv[ RaiseSim(Gconcl_list.SimLast(Gconcl.S), F).fi ~ Simulator(F).fi :
      ={arg, glob F, Gconcl_list.BIRO2.IRO.mp} ∧ §Gconcl.S.m{1} = §Simulator.m{2} ∧
        §Gconcl.S.mi{1} = §Simulator.mi{2} ∧ §Gconcl.S.paths{1} = §Simulator.paths{2} ==>
      ={res, glob F, Gconcl_list.BIRO2.IRO.mp} ∧ §Gconcl.S.m{1} = §Simulator.m{2} ∧
        §Gconcl.S.mi{1} = §Simulator.mi{2} ∧ §Gconcl.S.paths{1} = §Simulator.paths{2} ] := by
  intro F _
  -- EC: by proc;inline*;if;auto=>/#.
  --     (our `inline*` leaves the parameter's assignment before the `if`: `sp` first)
  equiv_proc; stmt_inline*; stmt_sp; stmt_if
  all_goals (equiv_auto; try auto_close)

set_option maxHeartbeats 4000000 in
-- (GAP 5)
set_option inline.defEqApply true in
/-- EC's `local lemma replace_simulator &m`. -/
theorem replace_simulator (m : VariableAssignment) :
    Pr[ IdealIndif(IRO.asF, RaiseSim(Gconcl_list.SimLast(Gconcl.S)), DRestr(Dist)).main ()
        @ &m : §res ] =
      Pr[ IdealIndif(IRO.asF, Simulator, DRestr(Dist)).main () @ &m : §res ] := by
  -- EC: byequiv=>//=;proc;inline*;sp;wp.
  byequiv; equiv_proc; stmt_inline*; stmt_sp; stmt_wp
  -- EC: call(: ={glob IRO, glob DRestr, glob Gconcl_list.BIRO2.IRO}
  --   /\ ={m, mi, paths}(Gconcl.S,Simulator));auto.
  equiv_call (_ : ={IRO.mp, Cntr.c, Gconcl_list.BIRO2.IRO.mp} ∧ §Gconcl.S.m{1} = §Simulator.m{2} ∧
      §Gconcl.S.mi{1} = §Simulator.mi{2} ∧ §Gconcl.S.paths{1} = §Simulator.paths{2})
  -- EC: + by proc;sp;if;auto;call(equiv_sim_f IRO);auto.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    · stmt_wp
      --     (EC checks `IRO`'s restriction: its declaration by `fp_finite`, `fp_disjoint`)
      equiv_call (@equiv_sim_f _ _ _
        (Indifferentiability.FUNCTIONALITY.view (block × capacity) (List Bool × ℤ) (List Bool) IRO.asF)
        ⟨by fp_finite, by fp_disjoint⟩)
      equiv_auto
    · equiv_auto
  -- EC: + by proc;sp;if;auto;call(equiv_sim_fi IRO);auto.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    · stmt_wp
      --     (EC checks `IRO`'s restriction: its declaration by `fp_finite`, `fp_disjoint`)
      equiv_call (@equiv_sim_fi _ _ _
        (Indifferentiability.FUNCTIONALITY.view (block × capacity) (List Bool × ℤ) (List Bool) IRO.asF)
        ⟨by fp_finite, by fp_disjoint⟩)
      equiv_auto
    · equiv_auto
  -- EC: by proc;sim.
  · equiv_proc; sim
  --     (EC's `auto` after the call; GAP 4: `glob Dist` from the equation of the two memories
  --     `sp` leaves, by hand)
  · equiv_auto; auto_prep
    have h := congrArg (FVP.fvP Dist).touched_getter.get ‹Gconcl_list.BIRO2.IRO.mp.set _ _ = _›
    simp (disch := fp_disjoint) only [touched_set_of_le_compl] at h
    auto_close

end

end GaudisCrypt.SHA3.Pilot.SHA3Indiff
