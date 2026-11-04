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

/-- What the section's restriction on `Dist` excludes (an abbreviation).  `-Gconcl_list.SimLast`
is `Gconcl_list.SimLast(Gconcl.S)`'s footprint, as in `SHA3Indiff`'s statement. -/
noncomputable def DistRestrictions.footprint : Footprint VariableAssignment :=
  (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
    (FVP.fvP (Gconcl_list.SimLast Gconcl.S)).glob ⊔ (BIRO.IRO.mp).footprint ⊔
    Cntr.c.footprint ⊔
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
  ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP Dist).globᶜ →
    FVP.fvP P ≤ (FVP.fvP Dist).globᶜ →
    (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
      P).procedure.IsLossless →
    (Indifferentiability.DPRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
      P).procedure.IsLossless →
    (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
      F).procedure.IsLossless →
    (Module.app Dist (Module.pair F P)).procedure.IsLossless

/-- The two counters: `Cntr.c` (bit level) and `BlockSponge.C.c` (block level).  `drestr_commute`
keeps the states equal outside them, with `Cntr.c{1} = C.c{2}` (`cI`). -/
noncomputable abbrev cL : Lens (ℤ × ℤ) VariableAssignment := Lens.pair Cntr.c BlockSponge.C.c

/-- EC's `={c}(Cntr, BlockSponge.C)`: `Cntr.c{1} = BlockSponge.C.c{2}`. -/
def cI (x y : ℤ × ℤ) : Prop := x.1 = y.2

/-- A write of `Cntr.c` on the left keeps the states equal outside `cL`. -/
theorem cL_Cntr_left {g₁ g₂ : VariableAssignment} (h : cL.equal_outside g₁ g₂) (v : ℤ) :
    cL.equal_outside (Cntr.c.set v g₁) g₂ := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨x, ?_⟩
  simp only [cL, Lens.pair]
  rw [(inferInstance : Lens.Disjoint BlockSponge.C.c Cntr.c).commute, Cntr.c.set_set]

/-- A write of `BlockSponge.C.c` on the right keeps the states equal outside `cL`. -/
theorem cL_C_right {g₁ g₂ : VariableAssignment} (h : cL.equal_outside g₁ g₂) (v : ℤ) :
    cL.equal_outside g₁ (BlockSponge.C.c.set v g₂) := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨(x.1, v), ?_⟩
  simp only [cL, Lens.pair]
  rw [(inferInstance : Lens.Disjoint BlockSponge.C.c Cntr.c).commute, BlockSponge.C.c.set_set]

/-- EC: `proc; sp; if=> //; sp; sim` for `PC(P).f` against `BlockSponge.PC(P).f`. -/
theorem dc_P_f (P : BlockSponge.DPRIMITIVE) (hP : FVP.fvP P ≤ (cL.footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ cL.equal_outside g₁ g₂ ∧ cI (cL.get g₁) (cL.get g₂))
      (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk (block × capacity) (List Bool × ℤ)
          (List Bool)
          { f := Indifferentiability.DPRIMITIVE.f (block × capacity) (List block × ℤ)
              (List block) P,
            fi := Indifferentiability.DPRIMITIVE.fi (block × capacity) (List block × ℤ)
              (List block) P }))).procedure
      (Indifferentiability.PRIMITIVE.f SLCommon.state (List block × ℤ) (List block)
        (Module.app BlockSponge.PC P)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ cL.equal_outside g₁ g₂ ∧ cI (cL.get g₁) (cL.get g₂)) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp]
  have hPf : FVP.fvP (Indifferentiability.DPRIMITIVE.f SLCommon.state (List block × ℤ)
      (List block) P) ≤ (cL.footprint)ᶜ := by fp_disjoint
  stmt_wp
  equiv_seq 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧
      cL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      cI (cL.get §allGlobals{1}) (cL.get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  · equiv_if
    case guard =>
      rintro g₁ g₂ _ _ _ _ ⟨-, -, -, hI⟩
      have hI' : Cntr.c.get g₁ = BlockSponge.C.c.get g₂ := hI
      rw [hI']
    case «then» =>
      stmt_wp
      equiv_call (prhlProc_self_equal_outside_module cL _ hPf cI)
      equiv_skip
      rintro g₁ g₂ a _ _ _ ⟨⟨rfl, -, he, hI⟩, -⟩
      refine ⟨⟨rfl, he, hI⟩, ?_⟩
      rintro r g₁' _ g₂' ⟨rfl, he', hI'⟩
      refine ⟨rfl, cL_C_right (cL_Cntr_left he' _) _, ?_⟩
      have h' : Cntr.c.get g₁' = BlockSponge.C.c.get g₂' := hI'
      show Cntr.c.get g₁' + 1 = BlockSponge.C.c.get g₂' + 1
      omega
    case «else» =>
      equiv_skip
      rintro g₁ g₂ _ _ _ _ ⟨⟨-, rfl, he, hI⟩, -⟩
      exact ⟨rfl, he, hI⟩

/-- EC: `proc; sp; if=> //; sp; sim` for `PC(P).fi` against `BlockSponge.PC(P).fi`. -/
theorem dc_P_fi (P : BlockSponge.DPRIMITIVE) (hP : FVP.fvP P ≤ (cL.footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ cL.equal_outside g₁ g₂ ∧ cI (cL.get g₁) (cL.get g₂))
      (Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk (block × capacity) (List Bool × ℤ)
          (List Bool)
          { f := Indifferentiability.DPRIMITIVE.f (block × capacity) (List block × ℤ)
              (List block) P,
            fi := Indifferentiability.DPRIMITIVE.fi (block × capacity) (List block × ℤ)
              (List block) P }))).procedure
      (Indifferentiability.PRIMITIVE.fi SLCommon.state (List block × ℤ) (List block)
        (Module.app BlockSponge.PC P)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ cL.equal_outside g₁ g₂ ∧ cI (cL.get g₁) (cL.get g₂)) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.fi.mk_simp]
  have hPf : FVP.fvP (Indifferentiability.DPRIMITIVE.fi SLCommon.state (List block × ℤ)
      (List block) P) ≤ (cL.footprint)ᶜ := by fp_disjoint
  stmt_wp
  equiv_seq 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧
      cL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      cI (cL.get §allGlobals{1}) (cL.get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  · equiv_if
    case guard =>
      rintro g₁ g₂ _ _ _ _ ⟨-, -, -, hI⟩
      have hI' : Cntr.c.get g₁ = BlockSponge.C.c.get g₂ := hI
      rw [hI']
    case «then» =>
      stmt_wp
      equiv_call (prhlProc_self_equal_outside_module cL _ hPf cI)
      equiv_skip
      rintro g₁ g₂ a _ _ _ ⟨⟨rfl, -, he, hI⟩, -⟩
      refine ⟨⟨rfl, he, hI⟩, ?_⟩
      rintro r g₁' _ g₂' ⟨rfl, he', hI'⟩
      refine ⟨rfl, cL_C_right (cL_Cntr_left he' _) _, ?_⟩
      have h' : Cntr.c.get g₁' = BlockSponge.C.c.get g₂' := hI'
      show Cntr.c.get g₁' + 1 = BlockSponge.C.c.get g₂' + 1
      omega
    case «else» =>
      equiv_skip
      rintro g₁ g₂ _ _ _ _ ⟨⟨-, rfl, he, hI⟩, -⟩
      exact ⟨rfl, he, hI⟩

/-- `FC(RaiseFun(F)).f` against `RaiseFun(BlockSponge.FC(F)).f`: the guards agree by
`size_pad2blocks` (EC: `if=> //; progress; smt(size_pad2blocks)`), the calls by `sim`. -/
theorem dc_F_f (F : BlockSponge.DFUNCTIONALITY) (hF : FVP.fvP F ≤ (cL.footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ cL.equal_outside g₁ g₂ ∧ cI (cL.get g₁) (cL.get g₂))
      (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app FC (Module.app RaiseFun F))).procedure
      (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app RaiseFun (Indifferentiability.DFUNCTIONALITY.mk SLCommon.state
          (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f SLCommon.state (List block × ℤ) (List block)
              (Module.app BlockSponge.FC F) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ cL.equal_outside g₁ g₂ ∧ cI (cL.get g₁) (cL.get g₂)) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  have hFf : FVP.fvP (Indifferentiability.DFUNCTIONALITY.f SLCommon.state (List block × ℤ)
      (List block) F) ≤ (cL.footprint)ᶜ := by fp_disjoint
  stmt_wp
  equiv_seq 1 1 : (§bs{1} = §bs{2} ∧ §n{1} = §n{2} ∧ §bl{2} = pad2blocks §bs{2} ∧
      §nb{2} = (§n{2} + r - 1) / r ∧ §(localVarLens "z" (List Bool)){1} = [] ∧
      §(localVarLens "z" (List block)){2} = [] ∧
      cL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      cI (cL.get §allGlobals{1}) (cL.get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, he, hI⟩
    exact ⟨rfl, rfl, he, hI⟩
  · equiv_if
    case guard =>
      rintro g₁ g₂ bs n _ _ _ bl nb _ ⟨rfl, rfl, rfl, rfl, -, -, -, hI⟩
      have hI' : Cntr.c.get g₁ = BlockSponge.C.c.get g₂ := hI
      rw [hI', size_pad2blocks]
    case «then» =>
      stmt_wp
      equiv_call (prhlProc_self_equal_outside_module cL _ hFf cI)
      stmt_wp
      equiv_skip
      rintro g₁ g₂ bs n _ _ _ bl nb _ ⟨⟨rfl, rfl, rfl, rfl, -, -, he, hI⟩, -⟩
      have hI' : Cntr.c.get g₁ = BlockSponge.C.c.get g₂ := hI
      refine ⟨⟨rfl, cL_C_right (cL_Cntr_left he _) _, ?_⟩, ?_⟩
      · change Cntr.c.get g₁ + ((size bs + 1) / r + 1) + max ((n + r - 1) / r - 1) 0 =
          BlockSponge.C.c.get g₂ + size (pad2blocks bs) + max ((n + r - 1) / r - 1) 0
        rw [hI', size_pad2blocks]
      · rintro r g₁' _ g₂' ⟨rfl, he', hI'⟩
        exact ⟨rfl, he', hI'⟩
    case «else» =>
      equiv_skip
      rintro g₁ g₂ bs n _ _ _ bl nb _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, he, hI⟩, -⟩
      exact ⟨by simp [blocks2bits_nil, take], he, hI⟩

/-- `LowerDist(DRestr(Dist))` against `BlockSponge.DRestr(LowerDist(Dist))`, for any `F`, `P`
outside the counters: EC's `call (_ : ={c}(Cntr, BlockSponge.C) /\ …)`, as the equal-outside
abstract call over `cL`.  Not an EC lemma: the common part of `drestr_commute1` and `2`. -/
theorem dc_dist (Dist : DISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (hDc : FVP.fvP Dist ≤ (cL.footprint)ᶜ)
    (F : BlockSponge.DFUNCTIONALITY) (hF : FVP.fvP F ≤ (cL.footprint)ᶜ)
    (P : BlockSponge.DPRIMITIVE) (hP : FVP.fvP P ≤ (cL.footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (Module.app (LowerDist (DRestr Dist)) (Module.pair F P)).procedure
      (Module.app (BlockSponge.DRestr (LowerDist Dist)) (Module.pair F P)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ cL.equal_outside g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{2} 1
  stmt_inline{1} 0
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (cL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      cI (cL.get §allGlobals{1}) (cL.get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    rintro g _ rfl
    exact ⟨cL_C_right (cL_Cntr_left (Lens.equal_outside.refl _) 0) 0, rfl⟩
  stmt_split{1} 1
  stmt_split{2} 1
  refine prhlStmt_seq_call (prhlProc_abstract_call_equal_outside_module
    cL Dist distExt hD.1 hDc cI ?hc _ _ ?horacle) ?_
  case hc =>
    intro _ n
    cases n with
    | zero => exact inferInstanceAs (Countable (List Bool × ℤ))
    | succ n => cases n with
      | zero => exact inferInstanceAs (Countable (block × capacity))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable (block × capacity))
        | succ n => nomatch n
  case horacle =>
    intro _ n
    cases n with
    | zero =>
      simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
        Module.fst_pair, Module.snd_pair, Indifferentiability.DFUNCTIONALITY.f.mk_simp,
        Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
      exact dc_F_f F hF
    | succ n => cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
          HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
          Indifferentiability.DFUNCTIONALITY.f.mk_simp, Indifferentiability.DPRIMITIVE.f.mk_simp,
          Indifferentiability.DPRIMITIVE.fi.mk_simp]
        exact dc_P_f P hP
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DFUNCTIONALITY.f.mk_simp, Indifferentiability.DPRIMITIVE.f.mk_simp,
            Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact dc_P_fi P hP
        | succ n => nomatch n
  equiv_skip
  intro σ₁ σ₂ h
  refine ⟨⟨rfl, h⟩, fun r₁ g₁ r₂ g₂ ⟨hr, he, _⟩ => ?_⟩
  simp_reads
  exact ⟨hr, he⟩

/-- `BlockSponge.Sponge` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_BlockSponge_Sponge : FVP.fvP BlockSponge.Sponge ≤ ⊥ := by
  fp_module

/-- EC's `drestr_commute1 &m`. -/
theorem drestr_commute1 (Dist : DISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (_hDd : DistRestrictions Dist) (m : VariableAssignment) :
    Procedure.Pr (BlockSponge.RealIndif BlockSponge.Sponge Perm
        (LowerDist (DRestr Dist))).procedure () m (fun r _ => r = true) =
      Procedure.Pr (BlockSponge.RealIndif BlockSponge.Sponge Perm
        (BlockSponge.DRestr (LowerDist Dist))).procedure () m (fun r _ => r = true) := by
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ g₁ r₂ g₂ h => by rw [h]) rfl
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  have hDc : FVP.fvP Dist ≤ (cL.footprint)ᶜ := by
    unfold DistRestrictions DistRestrictions.footprint at _hDd
    simp only [cL, Footprint.lens_pair]
    fp_disjoint
  equiv_seq 1 1 : (§allGlobals{1} = §allGlobals{2})
  · equiv_sim
  equiv_call (dc_dist Dist hD hDc
    (Indifferentiability.DFUNCTIONALITY.mk SLCommon.state (List block × ℤ) (List block)
      { f := Indifferentiability.FUNCTIONALITY.f SLCommon.state (List block × ℤ) (List block)
          (Module.app BlockSponge.Sponge
            (Indifferentiability.PRIMITIVE.view SLCommon.state (List block × ℤ) (List block)
              Perm)) })
    (by simp only [cL, Footprint.lens_pair]; fp_disjoint)
    (Indifferentiability.DPRIMITIVE.mk SLCommon.state (List block × ℤ) (List block)
      { f := Indifferentiability.PRIMITIVE.f SLCommon.state (List block × ℤ) (List block) Perm,
        fi := Indifferentiability.PRIMITIVE.fi SLCommon.state (List block × ℤ) (List block) Perm })
    (by simp only [cL, Footprint.lens_pair]; fp_disjoint))
  equiv_skip
  intro σ₁ σ₂ h
  exact ⟨h, fun r₁ g₁ r₂ g₂ ⟨hr, _⟩ => hr⟩

/-- EC's `drestr_commute2 &m`. -/
theorem drestr_commute2 (Dist : DISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (_hDd : DistRestrictions Dist) (m : VariableAssignment) :
    Procedure.Pr (BlockSponge.IdealIndif BlockSponge.BIRO.IRO.asF
        (Gconcl_list.SimLast Gconcl.S) (LowerDist (DRestr Dist))).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (BlockSponge.IdealIndif BlockSponge.BIRO.IRO.asF
        (Gconcl_list.SimLast Gconcl.S) (BlockSponge.DRestr (LowerDist Dist))).procedure () m
        (fun r _ => r = true) := by
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ g₁ r₂ g₂ h => by rw [h]) rfl
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  have hDc : FVP.fvP Dist ≤ (cL.footprint)ᶜ := by
    unfold DistRestrictions DistRestrictions.footprint at _hDd
    simp only [cL, Footprint.lens_pair]
    fp_disjoint
  equiv_seq 1 1 : (§allGlobals{1} = §allGlobals{2})
  · equiv_sim
  equiv_call (dc_dist Dist hD hDc
    (Indifferentiability.DFUNCTIONALITY.mk SLCommon.state (List block × ℤ) (List block)
      { f := Indifferentiability.FUNCTIONALITY.f SLCommon.state (List block × ℤ) (List block)
          BlockSponge.BIRO.IRO.asF })
    (by simp only [cL, Footprint.lens_pair]; fp_disjoint)
    (Indifferentiability.DPRIMITIVE.mk SLCommon.state (List block × ℤ) (List block)
      { f := Indifferentiability.PRIMITIVE.f SLCommon.state (List block × ℤ) (List block)
          (Module.app (Gconcl_list.SimLast Gconcl.S)
            (Indifferentiability.FUNCTIONALITY.view SLCommon.state (List block × ℤ) (List block)
              BlockSponge.BIRO.IRO.asF)),
        fi := Indifferentiability.PRIMITIVE.fi SLCommon.state (List block × ℤ) (List block)
          (Module.app (Gconcl_list.SimLast Gconcl.S)
            (Indifferentiability.FUNCTIONALITY.view SLCommon.state (List block × ℤ) (List block)
              BlockSponge.BIRO.IRO.asF)) })
    (by simp only [cL, Footprint.lens_pair]; fp_disjoint))
  equiv_skip
  intro σ₁ σ₂ h
  exact ⟨h, fun r₁ g₁ r₂ g₂ ⟨hr, _⟩ => hr⟩

/-- `op wit_pair : block * capacity = witness`. -/
def wit_pair : block × capacity := default

/-- The variables of `Gconcl.S` and `Simulator`: `replace_simulator` keeps the states equal outside
them, with `={m, mi, paths}(Gconcl.S, Simulator)` (`sI`). -/
noncomputable abbrev sL := Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi (Lens.pair Gconcl.S.paths
  (Lens.pair Simulator.m (Lens.pair Simulator.mi Simulator.paths))))

/-- `RaiseSim(SimLast(Gconcl.S))(F).f` is `SimLast(Gconcl.S)(LowerFun(F)).f`. -/
theorem raiseSim_f (F : DFUNCTIONALITY) :
    Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app (RaiseSim (Gconcl_list.SimLast Gconcl.S)) F) =
      Indifferentiability.PRIMITIVE.f SLCommon.state (List block × ℤ) (List block)
        (Module.app (Gconcl_list.SimLast Gconcl.S) (Module.app LowerFun F)) := by
  rw [RaiseSim, Module.app_comp]; rfl

/-- `RaiseSim(SimLast(Gconcl.S))(F).fi` is `SimLast(Gconcl.S)(LowerFun(F)).fi`. -/
theorem raiseSim_fi (F : DFUNCTIONALITY) :
    Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app (RaiseSim (Gconcl_list.SimLast Gconcl.S)) F) =
      Indifferentiability.PRIMITIVE.fi SLCommon.state (List block × ℤ) (List block)
        (Module.app (Gconcl_list.SimLast Gconcl.S) (Module.app LowerFun F)) := by
  rw [RaiseSim, Module.app_comp]; rfl

/-- `={m, mi, paths}(Gconcl.S, Simulator)` on the contents of `sL` (EC's `eq_S_Simulator`). -/
def sI (x y : FMap SLCommon.state SLCommon.state × FMap SLCommon.state SLCommon.state ×
    FMap capacity (List block × block) × FMap state state × FMap state state ×
    FMap capacity (List block × block)) : Prop :=
  x.1 = y.2.2.2.1 ∧ x.2.1 = y.2.2.2.2.1 ∧ x.2.2.1 = y.2.2.2.2.2

/-- A write of `Gconcl.S.m` keeps a state equal to itself outside `sL`. -/
theorem sL_Sm (g : VariableAssignment) (v) : sL.equal_outside g (Gconcl.S.m.set v g) :=
  Lens.equal_outside.pair_left (Lens.equal_outside_set_self _ g v)
/-- A write of `Gconcl.S.mi` keeps a state equal to itself outside `sL`. -/
theorem sL_Smi (g : VariableAssignment) (v) : sL.equal_outside g (Gconcl.S.mi.set v g) :=
  Lens.equal_outside.pair_right (Lens.equal_outside.pair_left (Lens.equal_outside_set_self _ g v))
/-- A write of `Gconcl.S.paths` keeps a state equal to itself outside `sL`. -/
theorem sL_Spaths (g : VariableAssignment) (v) : sL.equal_outside g (Gconcl.S.paths.set v g) :=
  Lens.equal_outside.pair_right (Lens.equal_outside.pair_right
    (Lens.equal_outside.pair_left (Lens.equal_outside_set_self _ g v)))
/-- A write of `Simulator.m` keeps a state equal to itself outside `sL`. -/
theorem sL_Simm (g : VariableAssignment) (v) : sL.equal_outside g (Simulator.m.set v g) :=
  Lens.equal_outside.pair_right (Lens.equal_outside.pair_right (Lens.equal_outside.pair_right
    (Lens.equal_outside.pair_left (Lens.equal_outside_set_self _ g v))))
/-- A write of `Simulator.mi` keeps a state equal to itself outside `sL`. -/
theorem sL_Simmi (g : VariableAssignment) (v) : sL.equal_outside g (Simulator.mi.set v g) :=
  Lens.equal_outside.pair_right (Lens.equal_outside.pair_right (Lens.equal_outside.pair_right
    (Lens.equal_outside.pair_right (Lens.equal_outside.pair_left
      (Lens.equal_outside_set_self _ g v)))))
/-- A write of `Simulator.paths` keeps a state equal to itself outside `sL`. -/
theorem sL_Simpaths (g : VariableAssignment) (v) : sL.equal_outside g (Simulator.paths.set v g) :=
  Lens.equal_outside.pair_right (Lens.equal_outside.pair_right (Lens.equal_outside.pair_right
    (Lens.equal_outside.pair_right (Lens.equal_outside.pair_right
      (Lens.equal_outside_set_self _ g v)))))

/-- A write inside `sL` on the left keeps the states equal outside `sL`. -/
theorem sL_left {β : Type} {X : Lens β VariableAssignment}
    (hX : ∀ g v, sL.equal_outside g (X.set v g)) {g₁ g₂ : VariableAssignment}
    (h : sL.equal_outside g₁ g₂) (v : β) : sL.equal_outside (X.set v g₁) g₂ :=
  (hX g₁ v).symm.trans h

/-- A write inside `sL` on the right keeps the states equal outside `sL`. -/
theorem sL_right {β : Type} {X : Lens β VariableAssignment}
    (hX : ∀ g v, sL.equal_outside g (X.set v g)) {g₁ g₂ : VariableAssignment}
    (h : sL.equal_outside g₁ g₂) (v : β) : sL.equal_outside g₁ (X.set v g₂) :=
  h.trans (hX g₂ v)

/-- The same write outside `sL` on both sides keeps the states equal outside `sL`. -/
theorem sL_same {β : Type} {X : Lens β VariableAssignment} [Lens.Disjoint X sL]
    {g₁ g₂ : VariableAssignment} (h : sL.equal_outside g₁ g₂) (v : β) :
    sL.equal_outside (X.set v g₁) (X.set v g₂) :=
  h.set_disjoint v

/-- `IRO.init` touches its map only.  Not an EC lemma. -/
@[fp_bound] theorem fvP_IRO_init_bool (valid : List Bool → Bool) (d : SubProbability Bool)
    (mp : Lens (FMap (List Bool × ℤ) Bool) VariableAssignment) :
    FVP.fvP (GaudisCrypt.SHA3.IRO.IRO.init Bool (List Bool) valid d mp) ≤ mp.footprint := by
  fp_module mp

/-- `IRO.f` touches its map only.  Not an EC lemma. -/
@[fp_bound] theorem fvP_IRO_f_bool (valid : List Bool → Bool) (d : SubProbability Bool)
    (mp : Lens (FMap (List Bool × ℤ) Bool) VariableAssignment) :
    FVP.fvP (GaudisCrypt.SHA3.IRO.IRO.f Bool (List Bool) valid d mp) ≤ mp.footprint := by
  fp_module mp

/-- `BIRO.IRO` touches `IRO.mp` only.  Not an EC lemma. -/
@[fp_bound] theorem fvP_IRO_asF : FVP.fvP IRO.asF ≤ (IRO.mp).footprint := by
  fp_module IRO.mp

/-- `FC` touches `Cntr.c` only.  Not an EC lemma. -/
@[fp_bound] theorem fvP_FC : FVP.fvP FC ≤ Cntr.c.footprint := by
  fp_module Cntr.c

/-- `PC` touches `Cntr.c` only.  Not an EC lemma. -/
@[fp_bound] theorem fvP_PC : FVP.fvP PC ≤ Cntr.c.footprint := by
  fp_module Cntr.c

set_option maxHeartbeats 2000000 in
/-- EC's `local equiv equiv_sim_f (F <: DFUNCTIONALITY {-Gconcl.S, -Simulator})`:
`RaiseSim(SimLast(Gconcl.S), F).f ~ Simulator(F).f`.  `={arg, glob F, glob BIRO2.IRO} /\ ={m, mi,
paths}(Gconcl.S, Simulator)` is the states equal outside `sL` (with `F` and `BIRO2.IRO` outside it)
and `sI`.  EC: `proc; inline*; if; …; rcondt{1} 5; smt(parseK formatK)`. -/
theorem equiv_sim_f (F : DFUNCTIONALITY) (hF : FVP.fvP F ≤ (sL.footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sL.equal_outside g₁ g₂ ∧ sI (sL.get g₁) (sL.get g₂))
      (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app (RaiseSim (Gconcl_list.SimLast Gconcl.S)) F)).procedure
      (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app Simulator F)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sL.equal_outside g₁ g₂ ∧ sI (sL.get g₁) (sL.get g₂)) := by
  rw [raiseSim_f]
  have hFf : FVP.fvP (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List Bool × ℤ)
      (List Bool) F) ≤ (sL.footprint)ᶜ := by fp_disjoint
  have hIf : FVP.fvP Gconcl_list.BIRO2.IRO.f ≤ (sL.footprint)ᶜ := by
    simp only [sL, Footprint.lens_pair]; fp_disjoint
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x1{1} = §x0{2} ∧ sL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      sI (sL.get §allGlobals{1}) (sL.get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, he, hI⟩
    exact ⟨rfl, he, hI⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ x _ ⟨rfl, -, hI⟩
    have h1 : Gconcl.S.m.get g₁ = Simulator.m.get g₂ := hI.1
    rw [h1]
  case «else» =>
    stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨⟨rfl, he, hI⟩, -⟩
    have h1 : Gconcl.S.m.get g₁ = Simulator.m.get g₂ := hI.1
    exact ⟨by rw [h1], he, hI⟩
  case «then» =>
    equiv_seq 5 5 : (§y1{1} = §y1{2} ∧ §x1{1} = §x0{2} ∧
        sL.equal_outside §allGlobals{1} §allGlobals{2} ∧
        sI (sL.get §allGlobals{1}) (sL.get §allGlobals{2}))
    · equiv_if
      case guard =>
        rintro g₁ g₂ x _ ⟨⟨rfl, -, hI⟩, -⟩
        have h3 : Gconcl.S.paths.get g₁ = Simulator.paths.get g₂ := hI.2.2
        rw [h3]
      case «else» =>
        stmt_wp
        equiv_rnd
        equiv_skip
        rintro g₁ g₂ x _ ⟨⟨⟨rfl, he, hI⟩, -⟩, -⟩ a _
        exact ⟨rfl, he, hI⟩
      case «then» =>
        stmt_wp
        equiv_seq 1 1 : (§q{1} = §q{2} ∧ §k{1} = §k{2} ∧ §x1{1} = §x0{2} ∧
            sL.equal_outside §allGlobals{1} §allGlobals{2} ∧
            sI (sL.get §allGlobals{1}) (sL.get §allGlobals{2}))
        · stmt_wp
          equiv_skip
          rintro g₁ g₂ x _ ⟨⟨⟨rfl, he, hI⟩, -⟩, -⟩
          have h3 : Gconcl.S.paths.get g₁ = Simulator.paths.get g₂ := hI.2.2
          refine ⟨?_, ?_, rfl, he, hI⟩ <;> rw [h3, BlockSponge.formatK]
        equiv_if
        case guard =>
          rintro g₁ g₂ q k x _ _ _ ⟨rfl, rfl, -⟩
          rfl
        case «else» =>
          stmt_wp
          equiv_call (prhlProc_self_equal_outside_module sL _ hIf sI)
          equiv_skip
          rintro g₁ g₂ q k x _ _ _ ⟨⟨rfl, rfl, rfl, he, hI⟩, -⟩
          exact ⟨⟨rfl, he, hI⟩, fun _ _ _ _ ⟨hr, he', hI'⟩ => ⟨by rw [hr], rfl, he', hI'⟩⟩
        case «then» =>
          stmt_wp
          equiv_seq 1 1 : (§obs{1} = unpad_blocks §q{2} ∧ §n{1} = §k{2} ∧ §obs{1} ≠ none ∧
              §x1{1} = §x0{2} ∧ sL.equal_outside §allGlobals{1} §allGlobals{2} ∧
              sI (sL.get §allGlobals{1}) (sL.get §allGlobals{2}))
          · stmt_wp
            equiv_skip
            rintro g₁ g₂ q k x _ _ _ ⟨⟨rfl, rfl, rfl, he, hI⟩, hv⟩
            refine ⟨rfl, rfl, ?_, rfl, he, hI⟩
            simpa [Gconcl_list.valid, valid_block] using hv
          equiv_if{1}
          case «then» =>
            stmt_wp
            equiv_call (prhlProc_self_equal_outside_module sL _ hFf sI)
            equiv_skip
            rintro g₁ g₂ obs n x q k _ ⟨⟨rfl, rfl, -, rfl, he, hI⟩, -⟩
            exact ⟨⟨rfl, he, hI⟩, fun _ _ _ _ ⟨hr, he', hI'⟩ => ⟨by rw [hr], rfl, he', hI'⟩⟩
          case «else» =>
            refine prhlStmt_pre prhlStmt_false ?_
            rintro σ₁ σ₂ ⟨⟨-, -, hne, -⟩, hg⟩
            simp only [decide_eq_false_iff_not, not_not] at hg
            exact hne hg
    equiv_seq 1 1 : (§y0{1} = §(localVarLens "y" state){2} ∧ (§y0{1}).2 = §y2{2} ∧
        §x1{1} = §x0{2} ∧
        sL.equal_outside §allGlobals{1} §allGlobals{2} ∧
        sI (sL.get §allGlobals{1}) (sL.get §allGlobals{2}))
    · stmt_wp
      equiv_rnd
      equiv_skip
      rintro g₁ g₂ y1 x _ _ ⟨rfl, rfl, he, hI⟩ a _
      have h1 : Gconcl.S.m.get g₁ = Simulator.m.get g₂ := hI.1
      have h2 : Gconcl.S.mi.get g₁ = Simulator.mi.get g₂ := hI.2.1
      have h3 : Gconcl.S.paths.get g₁ = Simulator.paths.get g₂ := hI.2.2
      refine ⟨rfl, rfl, sL_left sL_Smi (sL_left sL_Sm (sL_right sL_Simmi
        (sL_right sL_Simm he _) _) _) _, ?_⟩
      exact ⟨by rw [h1], by rw [h2], h3⟩
    equiv_if
    case guard =>
      rintro g₁ g₂ _ x _ _ _ ⟨-, -, rfl, -, hI⟩
      have h3 : Gconcl.S.paths.get g₁ = Simulator.paths.get g₂ := hI.2.2
      rw [h3]
    case «then» =>
      stmt_wp
      equiv_skip
      rintro g₁ g₂ y0 x _ _ _ ⟨⟨rfl, hy, rfl, he, hI⟩, -⟩
      have h1 : Gconcl.S.m.get g₁ = Simulator.m.get g₂ := hI.1
      have h2 : Gconcl.S.mi.get g₁ = Simulator.mi.get g₂ := hI.2.1
      have h3 : Gconcl.S.paths.get g₁ = Simulator.paths.get g₂ := hI.2.2
      refine ⟨rfl, sL_left sL_Spaths (sL_right sL_Simpaths he _) _, ?_⟩
      exact ⟨h1, h2, by rw [h3, hy]⟩
    case «else» =>
      equiv_skip
      rintro g₁ g₂ y0 x _ _ _ ⟨⟨rfl, -, rfl, he, hI⟩, -⟩
      exact ⟨rfl, he, hI⟩

/-- EC's `local equiv equiv_sim_fi` (as `equiv_sim_f`; EC: `proc; inline*; if; auto`). -/
theorem equiv_sim_fi (F : DFUNCTIONALITY) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sL.equal_outside g₁ g₂ ∧ sI (sL.get g₁) (sL.get g₂))
      (Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app (RaiseSim (Gconcl_list.SimLast Gconcl.S)) F)).procedure
      (Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app Simulator F)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sL.equal_outside g₁ g₂ ∧ sI (sL.get g₁) (sL.get g₂)) := by
  rw [raiseSim_fi]
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x1{1} = §x0{2} ∧ sL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      sI (sL.get §allGlobals{1}) (sL.get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, he, hI⟩
    exact ⟨rfl, he, hI⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ x _ ⟨rfl, -, hI⟩
    have h2 : Gconcl.S.mi.get g₁ = Simulator.mi.get g₂ := hI.2.1
    rw [h2]
  case «else» =>
    stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨⟨rfl, he, hI⟩, -⟩
    have h2 : Gconcl.S.mi.get g₁ = Simulator.mi.get g₂ := hI.2.1
    exact ⟨by rw [h2], he, hI⟩
  case «then» =>
    stmt_wp
    equiv_rnd
    equiv_rnd
    equiv_skip
    rintro g₁ g₂ x _ ⟨⟨rfl, he, hI⟩, -⟩ a _ b _
    have h1 : Gconcl.S.m.get g₁ = Simulator.m.get g₂ := hI.1
    have h2 : Gconcl.S.mi.get g₁ = Simulator.mi.get g₂ := hI.2.1
    have h3 : Gconcl.S.paths.get g₁ = Simulator.paths.get g₂ := hI.2.2
    refine ⟨sL_left sL_Sm (sL_left sL_Smi (sL_right sL_Simm
      (sL_right sL_Simmi he _) _) _) _, ?_⟩
    exact ⟨by rw [h1], by rw [h2], h3⟩


/-- `PC(P1).f ~ PC(P2).f` from `P1.f ~ P2.f` over `sL` (EC: `proc; sp; if; auto; call …`). -/
theorem rs_PC_f (P1 P2 : DPRIMITIVE)
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sL.equal_outside g₁ g₂ ∧ sI (sL.get g₁) (sL.get g₂))
      (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        P1).procedure
      (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        P2).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sL.equal_outside g₁ g₂ ∧ sI (sL.get g₁) (sL.get g₂))) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sL.equal_outside g₁ g₂ ∧ sI (sL.get g₁) (sL.get g₂))
      (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app PC P1)).procedure
      (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app PC P2)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sL.equal_outside g₁ g₂ ∧ sI (sL.get g₁) (sL.get g₂)) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§(localVarLens "a" (block × capacity)){1} =
      §(localVarLens "a" (block × capacity)){2} ∧ §z{1} = §z{2} ∧
      sL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      sI (sL.get §allGlobals{1}) (sL.get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  · equiv_if
    case guard =>
      rintro g₁ g₂ _ _ _ _ ⟨-, -, he, -⟩
      rw [Lens.equal_outside.get_disjoint (X := Cntr.c) he]
    case «then» =>
      stmt_wp
      equiv_call h
      equiv_skip
      rintro g₁ g₂ a _ _ _ ⟨⟨rfl, -, he, hI⟩, -⟩
      refine ⟨⟨rfl, he, hI⟩, ?_⟩
      rintro r g₁' _ g₂' ⟨rfl, he', hI'⟩
      rw [@Lens.equal_outside.get_disjoint _ sL _ Cntr.c
        (inferInstance : Lens.Disjoint Cntr.c sL) _ _ he']
      refine ⟨rfl, @Lens.equal_outside.set_disjoint _ sL _ Cntr.c
        (inferInstance : Lens.Disjoint Cntr.c sL) _ _ he' _, ?_⟩
      exact hI'
    case «else» =>
      equiv_skip
      rintro g₁ g₂ _ _ _ _ ⟨⟨-, rfl, he, hI⟩, -⟩
      exact ⟨rfl, he, hI⟩

/-- `PC(P1).fi ~ PC(P2).fi` from `P1.fi ~ P2.fi` over `sL`. -/
theorem rs_PC_fi (P1 P2 : DPRIMITIVE)
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sL.equal_outside g₁ g₂ ∧ sI (sL.get g₁) (sL.get g₂))
      (Indifferentiability.DPRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
        P1).procedure
      (Indifferentiability.DPRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
        P2).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sL.equal_outside g₁ g₂ ∧ sI (sL.get g₁) (sL.get g₂))) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sL.equal_outside g₁ g₂ ∧ sI (sL.get g₁) (sL.get g₂))
      (Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app PC P1)).procedure
      (Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app PC P2)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sL.equal_outside g₁ g₂ ∧ sI (sL.get g₁) (sL.get g₂)) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§(localVarLens "a" (block × capacity)){1} =
      §(localVarLens "a" (block × capacity)){2} ∧ §z{1} = §z{2} ∧
      sL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      sI (sL.get §allGlobals{1}) (sL.get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  · equiv_if
    case guard =>
      rintro g₁ g₂ _ _ _ _ ⟨-, -, he, -⟩
      rw [Lens.equal_outside.get_disjoint (X := Cntr.c) he]
    case «then» =>
      stmt_wp
      equiv_call h
      equiv_skip
      rintro g₁ g₂ a _ _ _ ⟨⟨rfl, -, he, hI⟩, -⟩
      refine ⟨⟨rfl, he, hI⟩, ?_⟩
      rintro r g₁' _ g₂' ⟨rfl, he', hI'⟩
      rw [@Lens.equal_outside.get_disjoint _ sL _ Cntr.c
        (inferInstance : Lens.Disjoint Cntr.c sL) _ _ he']
      refine ⟨rfl, @Lens.equal_outside.set_disjoint _ sL _ Cntr.c
        (inferInstance : Lens.Disjoint Cntr.c sL) _ _ he' _, ?_⟩
      exact hI'
    case «else» =>
      equiv_skip
      rintro g₁ g₂ _ _ _ _ ⟨⟨-, rfl, he, hI⟩, -⟩
      exact ⟨rfl, he, hI⟩

/-- `RaiseSim(SimLast(Gconcl.S))(F).init` is `SimLast(Gconcl.S)(LowerFun(F)).init`. -/
theorem raiseSim_init (F : DFUNCTIONALITY) :
    Indifferentiability.PRIMITIVE.init (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app (RaiseSim (Gconcl_list.SimLast Gconcl.S)) F) =
      Indifferentiability.PRIMITIVE.init SLCommon.state (List block × ℤ) (List block)
        (Module.app (Gconcl_list.SimLast Gconcl.S) (Module.app LowerFun F)) := by
  rw [RaiseSim, Module.app_comp]; rfl

set_option maxHeartbeats 4000000 in
/-- EC's `local lemma replace_simulator &m` (EC: `call (: ={glob IRO, glob DRestr,
glob BIRO2.IRO} /\ ={m, mi, paths}(Gconcl.S, Simulator))`, the equal-outside abstract call over
`sL`). -/
theorem replace_simulator (Dist : DISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (_hDd : DistRestrictions Dist) (m : VariableAssignment) :
    Procedure.Pr (IdealIndif BIRO.IRO.asF (RaiseSim (Gconcl_list.SimLast Gconcl.S))
        (DRestr Dist)).procedure () m (fun r _ => r = true) =
      Procedure.Pr (IdealIndif BIRO.IRO.asF Simulator (DRestr Dist)).procedure () m
        (fun r _ => r = true) := by
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ g₁ r₂ g₂ h => by rw [h]) rfl
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{1} 2
  stmt_inline{2} 2
  stmt_wp
  equiv_seq 1 1 : (sL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      sI (sL.get §allGlobals{1}) (sL.get §allGlobals{2}))
  · rw [raiseSim_init]
    repeat stmt_inline{1} 0
    repeat stmt_inline{2} 0
    stmt_wp
    equiv_skip
    rintro g _ rfl
    refine ⟨?_, rfl, rfl, rfl⟩
    exact sL_same (sL_same (sL_left sL_Spaths (sL_left sL_Smi (sL_left sL_Sm (sL_same
      (sL_right sL_Simpaths (sL_right sL_Simmi (sL_right sL_Simm (Lens.equal_outside.refl _) _)
        _) _) _) _) _) _) _) _
  have hDs : FVP.fvP Dist ≤ (sL.footprint)ᶜ := by
    unfold DistRestrictions DistRestrictions.footprint at _hDd
    simp only [sL, Footprint.lens_pair]
    fp_disjoint
  have hIRO : FVP.fvP (Indifferentiability.FUNCTIONALITY.view (block × capacity) (List Bool × ℤ)
      (List Bool) IRO.asF) ≤ (sL.footprint)ᶜ := by
    simp only [sL, Footprint.lens_pair]; fp_disjoint
  stmt_split{1} 1
  stmt_split{2} 1
  refine prhlStmt_seq_call (prhlProc_abstract_call_equal_outside_module
    sL Dist distExt hD.1 hDs sI ?hc _ _ ?horacle) ?_
  case hc =>
    intro _ n
    cases n with
    | zero => exact inferInstanceAs (Countable (List Bool × ℤ))
    | succ n => cases n with
      | zero => exact inferInstanceAs (Countable (block × capacity))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable (block × capacity))
        | succ n => nomatch n
  case horacle =>
    intro _ n
    cases n with
    | zero =>
      simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
        Module.fst_pair, Module.snd_pair, Indifferentiability.DFUNCTIONALITY.f.mk_simp,
        Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
      exact prhlProc_self_equal_outside_module sL _ (by
        simp only [sL, Footprint.lens_pair]; fp_disjoint) sI
    | succ n => cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
          HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
          Indifferentiability.DFUNCTIONALITY.f.mk_simp, Indifferentiability.DPRIMITIVE.f.mk_simp,
          Indifferentiability.DPRIMITIVE.fi.mk_simp]
        exact rs_PC_f _ _ (by
          simp only [Indifferentiability.DPRIMITIVE.f.mk_simp]
          exact equiv_sim_f _ hIRO)
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DFUNCTIONALITY.f.mk_simp, Indifferentiability.DPRIMITIVE.f.mk_simp,
            Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact rs_PC_fi _ _ (by
            simp only [Indifferentiability.DPRIMITIVE.fi.mk_simp]
            exact equiv_sim_fi _)
        | succ n => nomatch n
  equiv_skip
  intro σ₁ σ₂ h
  refine ⟨⟨rfl, h⟩, fun r₁ g₁ r₂ g₂ ⟨hr, _⟩ => ?_⟩
  simp_reads
  exact hr

/-- Every distinguisher is representable over `F.f`, `P.f`, `P.fi`.  Not an EC lemma. -/
theorem Distinguisher_representable (D : DISTINGUISHER) : Module.Representable D distExt := by
  refine Module.representable_of_firstOrder ?_ ?_ distExt (fun _ => rfl) D
  · simp [IsModule.moduleTypeRep, ModuleTypeRep.FirstOrder, Module.moduleTypeRep,
      Indifferentiability.DFUNCTIONALITY.typeRep, Indifferentiability.DPRIMITIVE.typeRep]
  · intro sig n
    cases n with
    | zero => exact ⟨fun U hU => by simp at hU; subst hU; exact ⟨([], 0)⟩, ⟨[]⟩⟩
    | succ n => cases n with
      | zero => exact ⟨fun U hU => by simp at hU; subst hU; infer_instance, inferInstance⟩
      | succ n => cases n with
        | zero => exact ⟨fun U hU => by simp at hU; subst hU; infer_instance, inferInstance⟩
        | succ n => nomatch n

/-- `LowerDist(Dist)` touches what `Dist` does.  Not an EC lemma. -/
theorem fvP_LowerDist (Dist : DISTINGUISHER) : FVP.fvP (LowerDist Dist) ≤ FVP.fvP Dist := by
  fp_module

/-- `DRestr(Dist)` touches `Dist`'s variables and `Cntr.c`.  Not an EC lemma. -/
theorem fvP_DRestr (Dist : DISTINGUISHER) :
    FVP.fvP (DRestr Dist) ≤ FVP.fvP Dist ⊔ Cntr.c.footprint := by
  fp_module Cntr.c

/-- `RaiseFun` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_RaiseFun : FVP.fvP RaiseFun ≤ ⊥ := by
  fp_module

/-- `RaiseFun(F).f` is lossless when `F.f` is (EC: `proc; call hf'; auto`). -/
theorem RaiseFun_f_ll (F : BlockSponge.DFUNCTIONALITY)
    (hF : (Indifferentiability.DFUNCTIONALITY.f SLCommon.state (List block × ℤ) (List block)
      F).procedure.IsLossless) :
    (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
      (Module.app RaiseFun F)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hF ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 5
  phoare_simp [hF]
  phoare_skip
  simp

/-- `Gconcl_list.Gext0Fresh` at the bit level: the variables of `Gconcl`'s
`local clone import Gext as Gext0` lie outside `Dist` (exception E13). -/
def Gext0Fresh (Dist : DISTINGUISHER) : Prop :=
  FVP.fvP Dist ≤ ((ConcreteF.PF.m).footprint ⊔ (ConcreteF.PF.mi).footprint ⊔
    (Handle.G1.m).footprint ⊔
    (Handle.G1.mi).footprint ⊔ (Handle.G1.mh).footprint ⊔ (Handle.G1.mhi).footprint ⊔
    Handle.G1.chandle.footprint ⊔ (Handle.G1.paths).footprint ⊔ Handle.G1.bext.footprint ⊔
    Handle.G1.bcol.footprint ⊔ (Handle.FRO.m).footprint ⊔ (Handle.ROhandle.RO.m).footprint)ᶜ

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

/-- EC's `security &m`, for the section's `Dist` and its axiom `Dist_lossless`, with
`Gext0Fresh Dist` (exception E13).  EC: `rewrite -(replace_simulator &m); …; have->:=conclusion
(Gconcl_list.SimLast(Gconcl.S)) (DRestr(Dist)) &m; have:=Gconcl_list.Real_Ideal (LowerDist(Dist));
rewrite (drestr_commute1 &m) (drestr_commute2 &m); have->:=Gconcl_list.Simplify_simulator …`.  Here
`Real_Ideal; Simplify_simulator` is `Gconcl_list.Inefficient_Real_Ideal_at` (the same statement),
`D_ll` of `LowerDist(Dist)` over `glob Dist` (exception E14). -/
theorem security (Dist : DISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (_hDd : DistRestrictions Dist) (_hG : Gext0Fresh Dist) (_Dist_lossless : Dist_lossless Dist)
    (m : VariableAssignment) :
    |(Procedure.Pr (RealIndif Sponge.Sponge Perm (DRestr Dist)).procedure () m
        (fun r _ => r = true) : ℝ) -
      (Procedure.Pr (IdealIndif BIRO.IRO.asF Simulator (DRestr Dist)).procedure () m
        (fun r _ => r = true) : ℝ)| ≤ bound := by
  have hS := SimLast_ECModule
  have hDD : Module.ECModule (DRestr Dist) distExt :=
    ⟨Distinguisher_representable _, (hD.finitelySupported.sup
      (Footprint.FinitelySupported.globalVar _)).mono (fvP_DRestr Dist)⟩
  have hR : Restrictions (Gconcl_list.SimLast Gconcl.S) (DRestr Dist) := by
    refine ⟨by fp_disjoint, (fvP_DRestr Dist).trans (sup_le ?_ ?_)⟩
    · unfold DistRestrictions DistRestrictions.footprint at _hDd
      exact _hDd.trans (Footprint.compl_antimono (by fp_sub))
    · refine (Footprint.le_compl_comm _ _).mpr (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_)
      · fp_disjoint
      · fp_disjoint
      · exact (Footprint.le_compl_comm _ _).mp
          (Footprint.globalVar_le_compl_glob hS.2 Cntr.c (by fp_disjoint))
      · fp_disjoint
      · fp_disjoint
  rw [← replace_simulator Dist hD _hDd m, conclusion _ _ hS hDD hR m,
    drestr_commute1 Dist hD _hDd m, drestr_commute2 Dist hD _hDd m]
  unfold DistRestrictions DistRestrictions.footprint at _hDd
  unfold Gext0Fresh at _hG
  have hDfs := hD.finitelySupported
  have hLD : Module.ECModule (LowerDist Dist) BlockSponge.distExt :=
    ⟨Gconcl_list.Real_Ideal_Abs.Distinguisher_representable _, hDfs.mono (fvP_LowerDist Dist)⟩
  have hLDd : Gconcl_list.DRestrictions_Real_Ideal (LowerDist Dist) :=
    (fvP_LowerDist Dist).trans (_hDd.trans (Footprint.compl_antimono (by
      unfold SLCommon.C.footprint; fp_sub)))
  have hLDg : Gconcl_list.Gext0Fresh (LowerDist Dist) := (fvP_LowerDist Dist).trans _hG
  have hgl : ∀ {T : Type} (x : Lens T VariableAssignment) {v : VariableName}
      [Lens.IsGlobalVar x v], FVP.fvP Dist ≤ x.footprintᶜ →
      x.footprint ≤ (FVP.fvP Dist).globᶜ :=
    fun x _ _ h => Footprint.globalVar_le_compl_glob hDfs x h
  have hGc : (BlockSponge.C.c).footprint ≤ (FVP.fvP Dist).globᶜ := hgl _ (by fp_disjoint)
  have hGX : (FVP.fvP Dist).glob ≤ (SLCommon.C.footprint ⊔
      (ConcreteF.PF.m).footprint ⊔ (ConcreteF.PF.mi).footprint ⊔ (Handle.G1.m).footprint ⊔
      (Handle.G1.mi).footprint ⊔ (Handle.G1.mh).footprint ⊔ (Handle.G1.mhi).footprint ⊔
      Handle.G1.chandle.footprint ⊔ (Handle.G1.paths).footprint ⊔ Handle.G1.bext.footprint ⊔
      Handle.G1.bcol.footprint ⊔ (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (SLCommon.F.RO.m).footprint ⊔ (SLCommon.Redo.prefixes).footprint ⊔
      (Handle.FRO.m).footprint ⊔ (Handle.ROhandle.RO.m).footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mp ?_
    unfold SLCommon.C.footprint
    repeat' refine sup_le ?_ ?_
    all_goals exact hgl _ (by fp_disjoint)
  have hRI : Gconcl_list.RealIdealRegion (FVP.fvP Dist).glob := by
    unfold Gconcl_list.RealIdealRegion
    refine (Footprint.le_compl_comm _ _).mp ?_
    unfold SLCommon.C.footprint
    repeat' refine sup_le ?_ ?_
    all_goals exact hgl _ (by fp_disjoint)
  have hll : Gconcl_list.D_lossless_at (LowerDist Dist) (FVP.fvP Dist).glob := by
    intro F0 P0 hF hP pll pill fll
    have hll := _Dist_lossless (Module.app RaiseFun F0)
      (Indifferentiability.DPRIMITIVE.mk (block × capacity) (List Bool × ℤ) (List Bool)
        { f := Indifferentiability.DPRIMITIVE.f (block × capacity) (List block × ℤ)
            (List block) P0
          fi := Indifferentiability.DPRIMITIVE.fi (block × capacity) (List block × ℤ)
            (List block) P0 })
      (by fp_disjoint) (by fp_disjoint)
      (by simpa only [Indifferentiability.DPRIMITIVE.f.mk_simp] using pll)
      (by simpa only [Indifferentiability.DPRIMITIVE.fi.mk_simp] using pill)
      (RaiseFun_f_ll F0 fll)
    rw [Procedure.isLossless_iff_phoareProc] at hll ⊢
    phoare_proc_to_stmt
    phoare_inline 0
    phoare_wp 3
    phoare_simp [hll]
    phoare_skip
    simp
  exact (Gconcl_list.Inefficient_Real_Ideal_at (LowerDist Dist) hLD hLDd hLDg _ hGc hGX
    (FVP.fvP Dist) hDfs le_rfl hRI hll m).trans (le_of_eq bound_eq)

end

/-- EC's `SHA3Indiff (Dist <: DISTINGUISHER {-Perm, -IRO, -BlockSponge.BIRO.IRO, -Cntr, -Simulator,
-Gconcl_list.SimLast(Gconcl.S), -BlockSponge.C, -Gconcl.S, -SLCommon.F.RO, -SLCommon.F.FRO,
-SLCommon.Redo, -SLCommon.C, -Gconcl_list.BIRO2.IRO, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
-Gconcl_list.Simulator}) &m`: the sponge is indifferentiable from the infinite random oracle.
With `Gext0Fresh Dist` (exception E13).  EC: `move=>h; apply (security Dist h &m)`. -/
theorem SHA3Indiff (Dist : DISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (_hDd : DistRestrictions Dist) (_hG : Gext0Fresh Dist) (m : VariableAssignment) :
    Dist_lossless Dist →
    |(Procedure.Pr (RealIndif Sponge.Sponge Perm (DRestr Dist)).procedure () m
        (fun r _ => r = true) : ℝ) -
      (Procedure.Pr (IdealIndif BIRO.IRO.asF Simulator (DRestr Dist)).procedure () m
        (fun r _ => r = true) : ℝ)| ≤ bound :=
  fun h => security Dist hD _hDd _hG h m

end GaudisCrypt.SHA3.SHA3Indiff
