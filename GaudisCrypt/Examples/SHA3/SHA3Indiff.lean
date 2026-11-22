import GaudisCrypt.Examples.SHA3.SmartCounter.Gconcl_list
import GaudisCrypt.Examples.SHA3.Sponge
import GaudisCrypt.Logic.EqualOutside
import GaudisCrypt.Logic.FrameTactics
import GaudisCrypt.Logic.GlobMono
import GaudisCrypt.Examples.SHA3.SimulatorRepresentable

/-!
# Indifferentiability of the sponge (EasyCrypt `proof/SHA3Indiff.ec`) — EC-fidelity port, complete

The lemmas of `SHA3Indiff.ec` in EC's scripts, over the old port's declarations of `Simulator`,
`Cntr`, `FC`, `PC`, `DRestr` (section `FirstPort` below), as `SmartCounter/Gconcl.lean` over the
old `Gconcl`.

Translation:
* `require import Common Sponge. import BIRO.` is the `open` below.
* EC's section `declare module Dist <: DISTINGUISHER {-…}` and `declare axiom Dist_lossless` are a
  `declare module` and a variable; the restriction also names the modules of the files whose
  lemmas the proofs use (fresh in EC).  `Dist` has a region for its `glob` (`with glob R`,
  exception E14): `security` applies `Sponge.conclusion` and `Gconcl_list.Real_Ideal` to
  `DRestr(Dist)` and `LowerDist(Dist)`, and `Dist_lossless` restricts its oracles against `R`.
-/

section FirstPort

/-!
## Declarations of the first port

Definitions and plain lemmas of the first port of this file (2026-10/11) that the proofs below
use; its program-logic proofs are gone.

The first port's translation notes (some mention declarations that went with its proofs):
* `require import Common Sponge. import BIRO.` is the `open` below: unqualified names are
  `Sponge`'s (`DISTINGUISHER`, `RealIndif`, `LowerDist` …) and `IRO` is `Sponge.BIRO.IRO`.
* `type state = SLCommon.state`, `op parse = BlockSponge.parse`, `op valid = Gconcl_list.valid`
  and `op limit = SLCommon.max_size` are abbreviations.
* `Simulator` and `FC`, `PC` have no type in EasyCrypt; they are used as a `SIMULATOR`, a
  `FUNCTIONALITY` and a `PRIMITIVE`, and declared at those types.
* The section's `declare module Dist` and its restrictions are hypotheses (`DistRestrictions`);
  `declare axiom Dist_lossless` is the hypothesis `Dist_lossless` of the lemmas whose proofs use it
  (`security`).
-/

-- EasyCrypt names the final lemma like its file (`SHA3Indiff.SHA3Indiff`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.SHA3Indiff

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.Sponge
open GaudisCrypt.SHA3.Sponge.BIRO

-- `PRIMITIVE` also names `Common`'s (the `PRP` clone); here it is `Sponge`'s, imported last
export GaudisCrypt.SHA3.Sponge (PRIMITIVE)

variable [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params]

/-- `op limit : int = SLCommon.max_size`. -/
abbrev limit : ℤ := SLCommon.max_size

/-! ## The last inlined simulator -/

abbrev state := SLCommon.state
abbrev parse := BlockSponge.parse
abbrev valid := Gconcl_list.valid

/-- EC's `Simulator.m`. -/
global_var Simulator.m : FMap state state
/-- EC's `Simulator.mi`. -/
global_var Simulator.mi : FMap state state
/-- EC's `Simulator.paths`. -/
global_var Simulator.paths : FMap capacity (List block × block)

module Simulator using (F : DFUNCTIONALITY) : PRIMITIVE {
  proc init () : Unit {
    Simulator.m <- (FMap.empty : FMap state state);
    Simulator.mi <- (FMap.empty : FMap state state);
    Simulator.paths <- FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0);
    _ <- call Gconcl_list.BIRO2.IRO.init ();
    return ()
  };
  proc f (x : state) : state {
    var p : List block, v : block, z : List block, q : List block, k : ℤ, cs : List Bool,
      y : state, y1 : block, y2 : capacity;
    if (!(decide (FMap.dom ($Simulator.m : FMap state state) $x))) {
      if (decide (FMap.dom ($Simulator.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($Simulator.paths : FMap capacity (List block × block)) ($x).2);
        z <- [];
        q, k <- parse (rcons $p ($v +^ ($x).1));
        if (valid $q) {
          cs <- call F.f ((oget (unpad_blocks $q), $k * r));
          z <- bits2blocks $cs;
        } else {
          z <- call Gconcl_list.BIRO2.IRO.f (($q, $k));
        }
        y1 <- last b0 $z;
      } else {
        y1 <$ bdistr;
      }
      y2 <$ cdistr;
      y <- ($y1, $y2);
      Simulator.m <- FMap.set $Simulator.m $x $y;
      Simulator.mi <- FMap.set $Simulator.mi $y $x;
      if (decide (FMap.dom ($Simulator.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($Simulator.paths : FMap capacity (List block × block)) ($x).2);
        Simulator.paths <- FMap.set $Simulator.paths $y2 (rcons $p ($v +^ ($x).1), ($y).1);
      }
    } else {
      y <- oget (FMap.get ($Simulator.m : FMap state state) $x);
    }
    return $y
  };
  proc fi (x : state) : state {
    var y : state, y1 : block, y2 : capacity;
    if (!(decide (FMap.dom ($Simulator.mi : FMap state state) $x))) {
      y1 <$ bdistr;
      y2 <$ cdistr;
      y <- ($y1, $y2);
      Simulator.mi <- FMap.set $Simulator.mi $x $y;
      Simulator.m <- FMap.set $Simulator.m $y $x;
    } else {
      y <- oget (FMap.get ($Simulator.mi : FMap state state) $x);
    }
    return $y
  };
}

/-! ## Restrictions

The counter for the functionality counts the number of times the underlying primitive is called
inside the functionality.  This number is equal to the sum of the number of blocks in the padding
of the input, plus the number of additional blocks the squeezing phase has to output. -/

/-- EC's `Cntr.c`. -/
global_var Cntr.c : ℤ

module Cntr {
  proc init () : Unit {
    Cntr.c <- 0;
    return ()
  };
}

module FC using (F : DFUNCTIONALITY) : FUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  -- `(size bs + 1) %/ r + 1 = size (pad2blocks bs)`
  proc f (x : List Bool × ℤ) : (List Bool) {
    var bs : List Bool, n : ℤ, z : List Bool;
    bs, n <- $x;
    z <- [];
    if (decide ($Cntr.c + ((size $bs + 1) / r + 1) + max (($n + r - 1) / r - 1) 0 ≤ limit)) {
      Cntr.c <- $Cntr.c + ((size $bs + 1) / r + 1) + max (($n + r - 1) / r - 1) 0;
      z <- call F.f (($bs, $n));
    }
    return $z
  };
}

module PC using (P : DPRIMITIVE) : PRIMITIVE {
  proc init () : Unit {
    return ()
  };
  proc f (a : block × capacity) : (block × capacity) {
    var z : block × capacity;
    z <- (b0, c0);
    if (decide ($Cntr.c + 1 ≤ limit)) {
      z <- call P.f ($a);
      Cntr.c <- $Cntr.c + 1;
    }
    return $z
  };
  proc fi (a : block × capacity) : (block × capacity) {
    var z : block × capacity;
    z <- (b0, c0);
    if (decide ($Cntr.c + 1 ≤ limit)) {
      z <- call P.fi ($a);
      Cntr.c <- $Cntr.c + 1;
    }
    return $z
  };
}

-- EC's `DRestr(D)(F)(P)`, with `D` a Lean parameter so that `DRestr D` is a `DISTINGUISHER`
set_option linter.gaudisCrypt.using false in
module DRestr (D : DISTINGUISHER) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call Cntr.init ();
    b <- call D(FC(F), PC(P)).distinguish ();
    return $b
  };
}

/-! ## The section, with `declare module Dist <: DISTINGUISHER {-Perm, -Gconcl_list.SimLast, -IRO,
-Cntr, -BlockSponge.BIRO.IRO, -Simulator, -BlockSponge.C, -Gconcl.S, -SLCommon.F.RO,
-SLCommon.F.FRO, -SLCommon.Redo, -SLCommon.C, -Gconcl_list.BIRO2.IRO, -Gconcl_list.F2.RO,
-Gconcl_list.F2.FRO, -Gconcl_list.Simulator}` and `declare axiom Dist_lossless` -/

section

/-- EC's `={c}(Cntr, BlockSponge.C)`: `Cntr.c{1} = BlockSponge.C.c{2}`. -/
def cI (x y : ℤ × ℤ) : Prop := x.1 = y.2

/-- `op wit_pair : block * capacity = witness`. -/
def wit_pair : block × capacity := default

/-- `FC` touches `Cntr.c` only.  Not an EC lemma. -/
@[fp_bound] theorem fvP_FC : FVP.fvP FC ≤ Cntr.c.footprint := by
  fp_module Cntr.c

/-- `LowerDist(Dist)` touches what `Dist` does.  Not an EC lemma. -/
theorem fvP_LowerDist (Dist : DISTINGUISHER) : FVP.fvP (LowerDist Dist) ≤ FVP.fvP Dist := by
  fp_module

/-- `DRestr(Dist)` touches `Dist`'s variables and `Cntr.c`.  Not an EC lemma. -/
theorem fvP_DRestr (Dist : DISTINGUISHER) :
    FVP.fvP (DRestr Dist) ≤ FVP.fvP Dist ⊔ Cntr.c.footprint := by
  fp_module Cntr.c

/-- `SimLast(Gconcl.S)` is an EasyCrypt-like simulator: its `init` does not depend on the oracle
(`Gconcl.S.init` calls nothing), so it is representable (`SIMULATOR.representable_of_init`), and
it has finitely many variables.  Not an EC lemma (EasyCrypt's module typing). -/
theorem SimLast_ECModule : Indifferentiability.SIMULATOR.ECModule (block × capacity)
    (List block × ℤ) (List block) (Gconcl_list.SimLast Gconcl.S) := by
  refine ⟨Indifferentiability.SIMULATOR.representable_of_init _ _ _ _ fun F F' => ?_,
    Footprint.FinitelySupported.mono ((Gconcl_list.fvP_SimLast _).trans
      (sup_le_sup_right Gconcl_list.fvP_S _)) ?_⟩
  · simp only [Gconcl_list.SimLast.apply_simp, Gconcl_list.SimLast.init.apply_simp,
      Gconcl.S.apply_simp, Gconcl.S.init.apply_simp, Indifferentiability.PRIMITIVE.init_pair]
  · exact ((Footprint.FinitelySupported.globalVar _).sup
      ((Footprint.FinitelySupported.globalVar _).sup (Footprint.FinitelySupported.globalVar _))).sup
      (Footprint.FinitelySupported.globalVar _)

/-- The bound `(limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r` of
`security` and `SHA3Indiff` (an abbreviation). -/
noncomputable def bound : ℝ :=
  ((limit ^ 2 - limit : ℤ) : ℝ) / ((2 ^ (r + c + 1).toNat : ℤ) : ℝ) +
    ((4 * limit ^ 2 : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)

/-- The bound of `Gconcl_list.Real_Ideal` is `bound`. -/
theorem bound_eq : Gconcl_list.bound = bound := by
  have hr := ge0_r
  have hc := ge0_c
  unfold Gconcl_list.bound bound
  have e : (r + c + 1).toNat = r.toNat + c.toNat + 1 := by omega
  rw [e]
  push_cast
  rw [pow_succ, pow_add]
  field_simp
  ring

end

end GaudisCrypt.SHA3.SHA3Indiff

end FirstPort

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

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
* GAP 2 (closed 2026-11-21): our inliner renames a callee's locals per side (`x2, n0` against
  `x0, n` in `equiv_sim_f`'s IRO loops), as EC's does; `sim` relates them by position (EC's
  equality set of pairs), so `equiv_sim_f` is EC's `last sim; smt(…)`.
* GAP 6 (closed 2026-11-17): `LowerDist(D, F, P)` passes `P`, `BlockSponge`'s primitive, to the
  bit sponge's `D` (one module type in EC); `equiv_proc` opens its procedures as EC's `proc`.
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

-- EC reads the globals of `DRestr(Dist)` and `LowerDist(Dist)` off their code
attribute [local fp_bound] GaudisCrypt.SHA3.SHA3Indiff.fvP_DRestr
  GaudisCrypt.SHA3.SHA3Indiff.fvP_LowerDist

/-- EC's `glob Gconcl_list.SimLast(Gconcl.S)`: the variables of `Gconcl.S` and
`Gconcl_list.BIRO2.IRO.mp`. -/
instance instECGlobSimLast : Module.ECGlob (Gconcl_list.SimLast Gconcl.S)
    (Gconcl.S.m.footprint ⊔ Gconcl.S.mi.footprint ⊔ Gconcl.S.paths.footprint ⊔
      Gconcl_list.BIRO2.IRO.mp.footprint) :=
  ⟨by fp_finite, by fp_le, ⟨_, by fp_finite, Footprint.le_glob _⟩⟩

set_option synthInstance.checkSynthOrder false in
/-- EC's `glob LowerDist(Dist)`: `glob Dist` (`LowerDist` has no variables). -/
instance instECGlobLowerDist (D : DISTINGUISHER) {R : Footprint VariableAssignment}
    [h : Module.ECGlob D R] : Module.ECGlob (LowerDist D) R :=
  ⟨h.finite.mono (GaudisCrypt.SHA3.SHA3Indiff.fvP_LowerDist D),
    (GaudisCrypt.SHA3.SHA3Indiff.fvP_LowerDist D).trans h.le, h.base⟩

section

-- (after EC's list: the modules of the files `security` goes through, fresh for `Dist` in EC,
-- where they are local to their sections or defined after `Dist`'s restriction is checked;
-- `with glob R`, exception E14)
declare module Dist <: DISTINGUISHER {-Perm, -Gconcl_list.SimLast, -IRO, -Cntr,
  -BlockSponge.BIRO.IRO, -Simulator, -BlockSponge.C, -Gconcl.S, -SLCommon.F.RO, -SLCommon.F.FRO,
  -SLCommon.Redo, -SLCommon.C, -Gconcl_list.BIRO2.IRO, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
  -Gconcl_list.Simulator,
  -Pilot.Sponge.HybridIRO.HybridIROLazy.mp, -Pilot.Sponge.HybridIRO.HybridIROEager.mp,
  -Pilot.Sponge.HybridIRO.ERO.RO.m, -Pilot.Sponge.HybridIRO.ERO.FRO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.RO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.FRO.m,
  -GaudisCrypt.SHA3.Handle.G1, -GaudisCrypt.SHA3.Gext.G2, -GaudisCrypt.SHA3.ConcreteF.PF,
  -GaudisCrypt.SHA3.Handle.FRO.m, -GaudisCrypt.SHA3.Handle.ROhandle.RO,
  -Pilot.Gext.ReSample.count, -Pilot.Gcol.Gcol.sample_c, -Pilot.ConcreteF.Switching.DBounder,
  -Pilot.ConcreteF.Switching.ARP, -Pilot.ConcreteF.Switching.PRPi.PRPi} with glob R

-- EC's `declare axiom Dist_lossless` (`glob Dist` as the region `R`)
variable (Dist_lossless : ∀ (F <: DFUNCTIONALITY {-R}), ∀ (P <: DPRIMITIVE {-R}),
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
  -- EC: seq 2 2 : (={glob Dist} /\ ={glob Perm} ); first sim.
  equiv_seq 2 2 : (={glob Dist, Perm.m, Perm.mi})
  · sim
  -- EC: inline*; wp; sp.
  stmt_inline*; stmt_wp; stmt_sp
  -- EC: call (_ : ={c}(Cntr, BlockSponge.C) /\ ={glob Perm}).
  equiv_call (_ : ={glob Perm} ∧ §Cntr.c{1} = §BlockSponge.C.c{2})
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
    --    Cntr.c{1} = BlockSponge.C.c{2} /\ ={glob Perm}).
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
      -- EC: call (_ : ={glob Perm}); first sim.
      --     (the callees' judgment, EC's `first sim`, closed by `equiv_call`: the same procedure)
      equiv_call (_ : ={glob Perm})
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
  equiv_proc; stmt_inline*; stmt_if
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
  on_goals -1 =>
    sim
    smt_close [BlockSponge.parseK, BlockSponge.formatK]
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
  --     (EC's `inline*`: nothing to inline here, `proc` opens `SimLast`'s alias)
  equiv_proc; stmt_if
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

set_option synthInstance.maxHeartbeats 400000 in
-- EC's restriction checks by instance search (`Dist` against the modules of the lemmas used)
set_option synthInstance.maxSize 1024 in
include Dist_lossless in
/-- EC's `lemma security &m :
`|Pr[RealIndif(Sponge, Perm, DRestr(Dist)).main() @ &m : res] -
Pr[IdealIndif(IRO, Simulator, DRestr(Dist)).main() @ &m : res]| <=
(limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r`. -/
theorem security (m : VariableAssignment) :
    |Pr[ RealIndif(Sponge, Perm, DRestr(Dist)).main () @ &m : §res ] -
      Pr[ IdealIndif(IRO.asF, Simulator, DRestr(Dist)).main () @ &m : §res ]| ≤
    ((limit ^ 2 - limit : ℤ) : ℝ) / ((2 ^ (r + c + 1).toNat : ℤ) : ℝ) +
      ((4 * limit ^ 2 : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ) := by
  -- EC: rewrite -(replace_simulator &m).
  rw [← replace_simulator Dist m]
  -- EC: rewrite exprSr 1:addz_ge0 1:ge0_r 1:ge0_c mulrC exprD_nneg 1:ge0_r 1:ge0_c.
  --     have -> : … by rewrite (fromintM 2); smt().
  --     rewrite/=.
  --     have -> : … rewrite exprS // expr1 /#.
  --     rewrite -/SLCommon.dstate /limit.
  --     (the bound as `Gconcl_list.Real_Ideal` states it: the first port's `bound_eq`)
  refine le_of_le_of_eq ?_ GaudisCrypt.SHA3.SHA3Indiff.bound_eq
  -- EC: have->:=conclusion (Gconcl_list.SimLast(Gconcl.S)) (DRestr(Dist)) &m.
  rw [@Pilot.Sponge.conclusion _ _ (Gconcl_list.SimLast Gconcl.S) ⟨by fp_finite, by fp_disjoint⟩ _
    instECGlobSimLast ⟨by fp_finite, by fp_disjoint⟩ (DRestr Dist) ⟨by fp_finite, by fp_disjoint⟩
    GaudisCrypt.SHA3.SHA3Indiff.SimLast_ECModule.1 m]
  -- EC: have//=:=(Gconcl_list.Real_Ideal (LowerDist(Dist))  _ &m).
  have h := @Pilot.Gconcl_list.Real_Ideal _ _ _ (LowerDist Dist) ⟨by fp_finite, by fp_disjoint⟩ R
    inferInstance inferInstance ?_ m
  -- EC: + move=>F P hp hpi hf'//=.
  --       have hf:islossless RaiseFun(F).f.
  --       - proc;call hf';auto.
  --       exact(Dist_lossless (RaiseFun(F)) P hp hpi hf).
  swap
  · intro F _ P _ hp hpi hf'
    have hf : islossless RaiseFun(F).f := by
      phoare_proc; phoare_call hf'; phoare_auto
    --     (E5: `LowerDist(Dist)` wraps EC's alias in a call; EC checks `RaiseFun(F)`'s
    --     restriction, here its declaration by `fp_finite`, `fp_disjoint`)
    phoare_proc
    phoare_call (@Dist_lossless (Module.app RaiseFun F) ⟨by fp_finite, by fp_disjoint⟩ P
      ⟨by fp_finite, by fp_disjoint⟩ hp hpi hf)
    phoare_auto
  -- EC: rewrite(drestr_commute1 &m) (drestr_commute2 &m).
  rw [drestr_commute1 Dist m, drestr_commute2 Dist m]
  -- EC: have->:=Gconcl_list.Simplify_simulator (LowerDist(Dist)) _ &m.
  rw [@Pilot.Gconcl_list.Simplify_Simulator.Simplify_simulator _ _ _ (LowerDist Dist)
    ⟨by fp_finite, by fp_disjoint⟩ m] at h
  -- EC: smt().
  exact h

end

section

declare module Dist <: DISTINGUISHER {-Perm, -Gconcl_list.SimLast, -IRO, -Cntr,
  -BlockSponge.BIRO.IRO, -Simulator, -BlockSponge.C, -Gconcl.S, -SLCommon.F.RO, -SLCommon.F.FRO,
  -SLCommon.Redo, -SLCommon.C, -Gconcl_list.BIRO2.IRO, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
  -Gconcl_list.Simulator,
  -Pilot.Sponge.HybridIRO.HybridIROLazy.mp, -Pilot.Sponge.HybridIRO.HybridIROEager.mp,
  -Pilot.Sponge.HybridIRO.ERO.RO.m, -Pilot.Sponge.HybridIRO.ERO.FRO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.RO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.FRO.m,
  -GaudisCrypt.SHA3.Handle.G1, -GaudisCrypt.SHA3.Gext.G2, -GaudisCrypt.SHA3.ConcreteF.PF,
  -GaudisCrypt.SHA3.Handle.FRO.m, -GaudisCrypt.SHA3.Handle.ROhandle.RO,
  -Pilot.Gext.ReSample.count, -Pilot.Gcol.Gcol.sample_c, -Pilot.ConcreteF.Switching.DBounder,
  -Pilot.ConcreteF.Switching.ARP, -Pilot.ConcreteF.Switching.PRPi.PRPi} with glob R

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
/-- EC's `lemma SHA3Indiff (Dist <: DISTINGUISHER{-Perm, -IRO, -BlockSponge.BIRO.IRO, -Cntr,
-Simulator, -Gconcl_list.SimLast(Gconcl.S), -BlockSponge.C, -Gconcl.S, -SLCommon.F.RO,
-SLCommon.F.FRO, -SLCommon.Redo, -SLCommon.C, -Gconcl_list.BIRO2.IRO, -Gconcl_list.F2.RO,
-Gconcl_list.F2.FRO, -Gconcl_list.Simulator}) &m :
(forall (F <: DFUNCTIONALITY {-Dist}) (P <: DPRIMITIVE {-Dist}), islossless P.f =>
islossless P.fi => islossless F.f => islossless Dist(F,P).distinguish) =>
`|Pr[RealIndif(Sponge, Perm, DRestr(Dist)).main() @ &m : res] -
Pr[IdealIndif(IRO, Simulator, DRestr(Dist)).main() @ &m : res]| <=
(limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r`.

The restriction and `glob Dist` as in the section above. -/
theorem SHA3Indiff (m : VariableAssignment) :
    (∀ (F <: DFUNCTIONALITY {-R}), ∀ (P <: DPRIMITIVE {-R}),
      islossless P.f → islossless P.fi → islossless F.f → islossless Dist(F, P).distinguish) →
    |Pr[ RealIndif(Sponge, Perm, DRestr(Dist)).main () @ &m : §res ] -
      Pr[ IdealIndif(IRO.asF, Simulator, DRestr(Dist)).main () @ &m : §res ]| ≤
    ((limit ^ 2 - limit : ℤ) : ℝ) / ((2 ^ (r + c + 1).toNat : ℤ) : ℝ) +
      ((4 * limit ^ 2 : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ) := by
  -- EC: move=>h;apply (security Dist h &m).
  intro h
  exact security Dist h m

end

end GaudisCrypt.SHA3.Pilot.SHA3Indiff
