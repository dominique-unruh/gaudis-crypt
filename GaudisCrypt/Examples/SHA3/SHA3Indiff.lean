import GaudisCrypt.Examples.SHA3.Sponge
import GaudisCrypt.Examples.SHA3.SmartCounter.Gconcl_list

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

/-- What the section's restriction on `Dist` excludes (an abbreviation).  `-Gconcl_list.SimLast`
is `Gconcl_list.SimLast(Gconcl.S)`'s footprint, as in `SHA3Indiff`'s statement. -/
noncomputable def DistRestrictions.footprint : Footprint VariableAssignment :=
  (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
    FVP.fvP (Gconcl_list.SimLast Gconcl.S) ⊔ (BIRO.IRO.mp).footprint ⊔ Cntr.c.footprint ⊔
    (BlockSponge.BIRO.IRO.mp).footprint ⊔ (Simulator.m).footprint ⊔ (Simulator.mi).footprint ⊔
    (Simulator.paths).footprint ⊔ BlockSponge.C.c.footprint ⊔ (Gconcl.S.m).footprint ⊔
    (Gconcl.S.mi).footprint ⊔ (Gconcl.S.paths).footprint ⊔ (SLCommon.F.RO.m).footprint ⊔
    (SLCommon.F.FRO.m).footprint ⊔ (SLCommon.Redo.prefixes).footprint ⊔ SLCommon.C.footprint ⊔
    (Gconcl_list.BIRO2.IRO.mp).footprint ⊔ (Gconcl_list.F2.RO.m).footprint ⊔
    (Gconcl_list.F2.FRO.m).footprint ⊔ (Gconcl_list.Simulator.m).footprint ⊔
    (Gconcl_list.Simulator.mi).footprint ⊔ (Gconcl_list.Simulator.paths).footprint ⊔
    (Gconcl_list.Simulator.unvalid_map).footprint

/-- The section's restriction on `Dist` (an abbreviation). -/
def DistRestrictions (Dist : DISTINGUISHER) : Prop :=
  FVP.fvP Dist ≤ DistRestrictions.footprintᶜ

/-- `declare axiom Dist_lossless (F <: DFUNCTIONALITY {-Dist}) (P <: DPRIMITIVE {-Dist}) :
islossless P.f => islossless P.fi => islossless F.f => islossless Dist(F,P).distinguish` (an
abbreviation). -/
def Dist_lossless (Dist : DISTINGUISHER) : Prop :=
  ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP Dist)ᶜ →
    FVP.fvP P ≤ (FVP.fvP Dist)ᶜ →
    (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
      P).procedure.IsLossless →
    (Indifferentiability.DPRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
      P).procedure.IsLossless →
    (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
      F).procedure.IsLossless →
    (Module.app Dist (Module.pair F P)).procedure.IsLossless

theorem drestr_commute1 (Dist : DISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (_hDd : DistRestrictions Dist) (m : VariableAssignment) :
    Procedure.Pr (BlockSponge.RealIndif BlockSponge.Sponge Perm
        (LowerDist (DRestr Dist))).procedure () m (fun r _ => r = true) =
      Procedure.Pr (BlockSponge.RealIndif BlockSponge.Sponge Perm
        (BlockSponge.DRestr (LowerDist Dist))).procedure () m (fun r _ => r = true) := by
  sorry

theorem drestr_commute2 (Dist : DISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (_hDd : DistRestrictions Dist) (m : VariableAssignment) :
    Procedure.Pr (BlockSponge.IdealIndif BlockSponge.BIRO.IRO.asF
        (Gconcl_list.SimLast Gconcl.S) (LowerDist (DRestr Dist))).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (BlockSponge.IdealIndif BlockSponge.BIRO.IRO.asF
        (Gconcl_list.SimLast Gconcl.S) (BlockSponge.DRestr (LowerDist Dist))).procedure () m
        (fun r _ => r = true) := by
  sorry

/-- `op wit_pair : block * capacity = witness`. -/
def wit_pair : block × capacity := default

/-- `={m, mi, paths}(Gconcl.S, Simulator)` (an abbreviation). -/
def eq_S_Simulator (g₁ g₂ : VariableAssignment) : Prop :=
  Gconcl.S.m.get g₁ = Simulator.m.get g₂ ∧ Gconcl.S.mi.get g₁ = Simulator.mi.get g₂ ∧
    Gconcl.S.paths.get g₁ = Simulator.paths.get g₂

/-- `local equiv equiv_sim_f (F <: DFUNCTIONALITY {-Gconcl.S, -Simulator}) :
RaiseSim(Gconcl_list.SimLast(Gconcl.S), F).f ~ Simulator(F).f :
={arg, glob F, glob Gconcl_list.BIRO2.IRO} /\ ={m, mi, paths}(Gconcl.S, Simulator) ==>
={res, glob F, glob Gconcl_list.BIRO2.IRO} /\ ={m, mi, paths}(Gconcl.S, Simulator)`. -/
theorem equiv_sim_f (F : DFUNCTIONALITY)
    (_hF : FVP.fvP F ≤ ((Gconcl.S.m).footprint ⊔ (Gconcl.S.mi).footprint ⊔
      (Gconcl.S.paths).footprint ⊔ (Simulator.m).footprint ⊔ (Simulator.mi).footprint ⊔
      (Simulator.paths).footprint)ᶜ) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ eqGlob F g₁ g₂ ∧
        Gconcl_list.BIRO2.IRO.mp.get g₁ = Gconcl_list.BIRO2.IRO.mp.get g₂ ∧ eq_S_Simulator g₁ g₂)
      (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app (RaiseSim (Gconcl_list.SimLast Gconcl.S)) F)).procedure
      (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app Simulator F)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eqGlob F g₁ g₂ ∧
        Gconcl_list.BIRO2.IRO.mp.get g₁ = Gconcl_list.BIRO2.IRO.mp.get g₂ ∧
        eq_S_Simulator g₁ g₂) := by
  sorry

/-- `local equiv equiv_sim_fi (F <: DFUNCTIONALITY {-Gconcl.S, -Simulator})`, as `equiv_sim_f`
for `fi`. -/
theorem equiv_sim_fi (F : DFUNCTIONALITY)
    (_hF : FVP.fvP F ≤ ((Gconcl.S.m).footprint ⊔ (Gconcl.S.mi).footprint ⊔
      (Gconcl.S.paths).footprint ⊔ (Simulator.m).footprint ⊔ (Simulator.mi).footprint ⊔
      (Simulator.paths).footprint)ᶜ) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ eqGlob F g₁ g₂ ∧
        Gconcl_list.BIRO2.IRO.mp.get g₁ = Gconcl_list.BIRO2.IRO.mp.get g₂ ∧ eq_S_Simulator g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app (RaiseSim (Gconcl_list.SimLast Gconcl.S)) F)).procedure
      (Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app Simulator F)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eqGlob F g₁ g₂ ∧
        Gconcl_list.BIRO2.IRO.mp.get g₁ = Gconcl_list.BIRO2.IRO.mp.get g₂ ∧
        eq_S_Simulator g₁ g₂) := by
  sorry

/-- `local lemma replace_simulator &m`. -/
theorem replace_simulator (Dist : DISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (_hDd : DistRestrictions Dist) (m : VariableAssignment) :
    Procedure.Pr (IdealIndif BIRO.IRO.asF (RaiseSim (Gconcl_list.SimLast Gconcl.S))
        (DRestr Dist)).procedure () m (fun r _ => r = true) =
      Procedure.Pr (IdealIndif BIRO.IRO.asF Simulator (DRestr Dist)).procedure () m
        (fun r _ => r = true) := by
  sorry

/-- The bound `(limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r` of
`security` and `SHA3Indiff` (an abbreviation). -/
noncomputable def bound : ℝ :=
  ((limit ^ 2 - limit : ℤ) : ℝ) / ((2 ^ (r + c + 1).toNat : ℤ) : ℝ) +
    ((4 * limit ^ 2 : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)

/-- EC's `security &m`, for the section's `Dist` and its axiom `Dist_lossless`. -/
theorem security (Dist : DISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (_hDd : DistRestrictions Dist) (_Dist_lossless : Dist_lossless Dist)
    (m : VariableAssignment) :
    |(Procedure.Pr (RealIndif Sponge.Sponge Perm (DRestr Dist)).procedure () m
        (fun r _ => r = true) : ℝ) -
      (Procedure.Pr (IdealIndif BIRO.IRO.asF Simulator (DRestr Dist)).procedure () m
        (fun r _ => r = true) : ℝ)| ≤ bound := by
  sorry

end

/-- EC's `SHA3Indiff (Dist <: DISTINGUISHER {-Perm, -IRO, -BlockSponge.BIRO.IRO, -Cntr, -Simulator,
-Gconcl_list.SimLast(Gconcl.S), -BlockSponge.C, -Gconcl.S, -SLCommon.F.RO, -SLCommon.F.FRO,
-SLCommon.Redo, -SLCommon.C, -Gconcl_list.BIRO2.IRO, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
-Gconcl_list.Simulator}) &m`: the sponge is indifferentiable from the infinite random oracle. -/
theorem SHA3Indiff (Dist : DISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (_hDd : DistRestrictions Dist) (m : VariableAssignment) :
    Dist_lossless Dist →
    |(Procedure.Pr (RealIndif Sponge.Sponge Perm (DRestr Dist)).procedure () m
        (fun r _ => r = true) : ℝ) -
      (Procedure.Pr (IdealIndif BIRO.IRO.asF Simulator (DRestr Dist)).procedure () m
        (fun r _ => r = true) : ℝ)| ≤ bound := by
  sorry

end GaudisCrypt.SHA3.SHA3Indiff
