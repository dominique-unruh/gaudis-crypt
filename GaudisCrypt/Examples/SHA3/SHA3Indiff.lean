import GaudisCrypt.Examples.SHA3.Sponge
import GaudisCrypt.Examples.SHA3.SmartCounter.Gconcl_list
import GaudisCrypt.Logic.EqualOutside
import GaudisCrypt.Logic.FrameTactics
import GaudisCrypt.Logic.GlobMono
import GaudisCrypt.Examples.SHA3.SimulatorRepresentable

/-!
# Indifferentiability of the sponge (EasyCrypt `proof/SHA3Indiff.ec`)

`SHA3Indiff`: the sponge on the ideal permutation, its distinguisher restricted to `limit` calls
to the permutation (`DRestr`), is indifferentiable from the bit-level infinite random oracle, with
the simulator `Simulator`, up to `(limit² - limit) / 2^(r+c+1) + 4·limit² / 2^c`.

Translation notes (see `notes/SHA3/README.md`):
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
    b <- call (Module.app D (Module.pair
      (Indifferentiability.DFUNCTIONALITY.mk (block × capacity) (List Bool × ℤ) (List Bool)
        { f := Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
            (Module.app FC F) })
      (Indifferentiability.DPRIMITIVE.mk (block × capacity) (List Bool × ℤ) (List Bool)
        { f := Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
            (Module.app PC P)
          fi := Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
            (Module.app PC P) }))) ();
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

/-- `IRO.init` touches its map only.  Not an EC lemma. -/
@[fp_bound] theorem fvP_IRO_init_bool (valid : List Bool → Bool) (d : SubProbability Bool)
    (mp : Lens (FMap (List Bool × ℤ) Bool) VariableAssignment) :
    FVP.fvP (GaudisCrypt.SHA3.IRO.IRO.init Bool (List Bool) valid d mp) ≤ mp.footprint := by
  fp_module mp

/-- `BIRO.IRO` touches `IRO.mp` only.  Not an EC lemma. -/
@[fp_bound] theorem fvP_IRO_asF : FVP.fvP IRO.asF ≤ (IRO.mp).footprint := by
  fp_module IRO.mp

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
