import GaudisCrypt.Examples.SHA3.SmartCounter.Gext

/-!
# Conclusion of the squeezeless sponge proof (EasyCrypt `proof/smart_counter/Gconcl.ec`)

`Real_Ideal`: the real game with the squeezeless sponge is indifferentiable from the ideal
functionality `IF` (the random oracle `F.RO`) with the simulator `S`, up to the switching bound
and the collision and extension probabilities.

Translation notes (see `notes/SHA3/README.md`):
* `module IF = { proc init = F.RO.init  proc f = F.RO.get }` is a definition assembling the
  aliased procedures.
* The section's `local clone import Gext as Gext0` is `Gext`, opened.
* `G3(RO : F.RO)` and `G4(RO : F.RO)` take the module type `F.RO` (`F.RO_T`, exception E3).  Their
  inner modules depend on `RO` only: they are functors of `RO` (`G3.M`, `G3.S`, `G4.C`, `G4.S`);
  `G3 D`, `G4 D` are the games' `distinguish`, with `D` a Lean parameter.
-/

namespace GaudisCrypt.SHA3.Gconcl

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.ConcreteF
open GaudisCrypt.SHA3.Handle GaudisCrypt.SHA3.Gcol GaudisCrypt.SHA3.Gext

export GaudisCrypt.SHA3.SLCommon (state PRIMITIVE)

variable [SLCommon.Params]

/-- EC's `module IF = { proc init = F.RO.init  proc f = F.RO.get }`. -/
noncomputable def IF : FUNCTIONALITY :=
  Indifferentiability.FUNCTIONALITY.mk state (List block) block
    { init := PROM.FullRO.ROmap.init (List block) block F.RO
      f := PROM.FullRO.ROmap.get (List block) block F.RO }

/-- EC's `S.m`. -/
global_var S.m : smap
/-- EC's `S.mi`. -/
global_var S.mi : smap
/-- EC's `S.paths`. -/
global_var S.paths : FMap capacity (List block × block)

-- The simulator
module S using (F : DFUNCTIONALITY) : PRIMITIVE {
  proc init () : Unit {
    S.m <- (FMap.empty : smap);
    S.mi <- (FMap.empty : smap);
    -- the empty path is initially known by the adversary to lead to capacity 0^c
    S.paths <- FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0);
    return ()
  };
  proc f (x : state) : state {
    var p : List block, v : block, y : state, y1 : block, y2 : capacity;
    if (!(decide (FMap.dom ($S.m : smap) $x))) {
      if (decide (FMap.dom ($S.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($S.paths : FMap capacity (List block × block)) ($x).2);
        y1 <- call F.f (rcons $p ($v +^ ($x).1));
      } else {
        y1 <$ bdistr;
      }
      y2 <$ cdistr;
      y <- ($y1, $y2);
      S.m <- FMap.set $S.m $x $y;
      S.mi <- FMap.set $S.mi $y $x;
      if (decide (FMap.dom ($S.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($S.paths : FMap capacity (List block × block)) ($x).2);
        S.paths <- FMap.set $S.paths ($y).2 (rcons $p ($v +^ ($x).1), ($y).1);
      }
    } else {
      y <- oget (FMap.get ($S.m : smap) $x);
    }
    return $y
  };
  proc fi (x : state) : state {
    var y : state, y1 : block, y2 : capacity;
    if (!(decide (FMap.dom ($S.mi : smap) $x))) {
      y1 <$ bdistr;
      y2 <$ cdistr;
      y <- ($y1, $y2);
      S.mi <- FMap.set $S.mi $x $y;
      S.m <- FMap.set $S.m $y $x;
    } else {
      y <- oget (FMap.get ($S.mi : smap) $x);
    }
    return $y
  };
}

/-! ## The section -/

-- EC's local `G3(RO).M`
module G3.M using (RO : F.RO_T) : DFUNCTIONALITY {
  proc f (p : List block) : block {
    var sa : block, sa' : block, h : handle, i : ℤ, counter : ℤ;
    h <- 0;
    i <- 0;
    counter <- 0;
    sa <- b0;
    while ($i < size $p) {
      if (decide (FMap.dom ($G1.mh : hsmap) ($sa +^ nth default $p $i, $h))) {
        _ <- call RO.sample (take ($i + 1) $p);
        sa, h <- oget (FMap.get ($G1.mh : hsmap) ($sa +^ nth default $p $i, $h));
      } else {
        if (decide ($counter < size $p - «prefix» $p (get_max_prefix $p
            (elems (FMap.fdom ($C.queries : FMap (List block) block)))))) {
          _ <- call (PROM.FullRO.FRO_T.sample handle capacity RRO) ($G1.chandle);
          sa' <- call RO.get (take ($i + 1) $p);
          sa <- $sa +^ nth default $p $i;
          G1.mh <- FMap.set $G1.mh ($sa, $h) ($sa', $G1.chandle);
          G1.mhi <- FMap.set $G1.mhi ($sa', $G1.chandle) ($sa, $h);
          sa, h <- ($sa', $G1.chandle);
          G1.chandle <- $G1.chandle + 1;
          counter <- $counter + 1;
        } else {
          _ <- call RO.sample (take ($i + 1) $p);
        }
      }
      i <- $i + 1;
    }
    sa <- call RO.get ($p);
    return $sa
  };
}

-- EC's local `G3(RO).S`
module G3.S using (RO : F.RO_T) : DPRIMITIVE {
  proc f (x : state) : state {
    var p : List block, v : block, y : state, y1 : block, y2 : capacity, hy2 : handle,
      hx2 : handle, handles_ : FMap handle capacity, t : Bool;
    if (!(decide (FMap.dom ($G1.m : smap) $x))) {
      if (decide (FMap.dom ($G1.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($G1.paths : FMap capacity (List block × block)) ($x).2);
        y1 <- call RO.get (rcons $p ($v +^ ($x).1));
      } else {
        y1 <$ bdistr;
      }
      y2 <$ cdistr;
      y <- ($y1, $y2);
      handles_ <- call (PROM.FullRO.FRO_T.allKnown handle capacity RRO) ();
      if (!(decide (FMap.rng $handles_ ($x).2))) {
        _ <- call (PROM.FullRO.FRO_T.set handle capacity RRO) ($G1.chandle, ($x).2);
        G1.chandle <- $G1.chandle + 1;
      }
      handles_ <- call (PROM.FullRO.FRO_T.allKnown handle capacity RRO) ();
      hx2 <- oget (hinvc $handles_ ($x).2);
      t <- call (PROM.FullRO.FRO_T.queried handle capacity RRO)
        ((oget (FMap.get ($G1.mh : hsmap) (($x).1, $hx2))).2, Unknown);
      if (decide (FMap.dom ($G1.mh : hsmap) (($x).1, $hx2)) && $t) {
        hy2 <- (oget (FMap.get ($G1.mh : hsmap) (($x).1, $hx2))).2;
        FRO.m <- FMap.set $FRO.m $hy2 ($y2, Known);
        G1.m <- FMap.set $G1.m $x $y;
        G1.mi <- FMap.set $G1.mi $y $x;
      } else {
        hy2 <- $G1.chandle;
        G1.chandle <- $G1.chandle + 1;
        _ <- call (PROM.FullRO.FRO_T.set handle capacity RRO) ($hy2, ($y).2);
        G1.m <- FMap.set $G1.m $x $y;
        G1.mh <- FMap.set $G1.mh (($x).1, $hx2) (($y).1, $hy2);
        G1.mi <- FMap.set $G1.mi $y $x;
        G1.mhi <- FMap.set $G1.mhi (($y).1, $hy2) (($x).1, $hx2);
      }
      if (decide (FMap.dom ($G1.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($G1.paths : FMap capacity (List block × block)) ($x).2);
        G1.paths <- FMap.set $G1.paths ($y).2 (rcons $p ($v +^ ($x).1), ($y).1);
      }
    } else {
      y <- oget (FMap.get ($G1.m : smap) $x);
    }
    return $y
  };
  proc fi (x : state) : state {
    var y : state, y1 : block, y2 : capacity, hx2 : handle, hy2 : handle,
      handles_ : FMap handle capacity, t : Bool;
    if (!(decide (FMap.dom ($G1.mi : smap) $x))) {
      handles_ <- call (PROM.FullRO.FRO_T.allKnown handle capacity RRO) ();
      if (!(decide (FMap.rng $handles_ ($x).2))) {
        _ <- call (PROM.FullRO.FRO_T.set handle capacity RRO) ($G1.chandle, ($x).2);
        G1.chandle <- $G1.chandle + 1;
      }
      handles_ <- call (PROM.FullRO.FRO_T.allKnown handle capacity RRO) ();
      hx2 <- oget (hinvc $handles_ ($x).2);
      t <- call (PROM.FullRO.FRO_T.queried handle capacity RRO)
        ((oget (FMap.get ($G1.mhi : hsmap) (($x).1, $hx2))).2, Unknown);
      y1 <$ bdistr;
      y2 <$ cdistr;
      y <- ($y1, $y2);
      if (decide (FMap.dom ($G1.mhi : hsmap) (($x).1, $hx2)) && $t) {
        y1, hy2 <- oget (FMap.get ($G1.mhi : hsmap) (($x).1, $hx2));
        FRO.m <- FMap.set $FRO.m $hy2 ($y2, Known);
        G1.mi <- FMap.set $G1.mi $x $y;
        G1.m <- FMap.set $G1.m $y $x;
      } else {
        hy2 <- $G1.chandle;
        G1.chandle <- $G1.chandle + 1;
        _ <- call (PROM.FullRO.FRO_T.set handle capacity RRO) ($hy2, ($y).2);
        G1.mi <- FMap.set $G1.mi $x $y;
        G1.mhi <- FMap.set $G1.mhi (($x).1, $hx2) (($y).1, $hy2);
        G1.m <- FMap.set $G1.m $y $x;
        G1.mh <- FMap.set $G1.mh (($y).1, $hy2) (($x).1, $hx2);
      }
    } else {
      y <- oget (FMap.get ($G1.mi : smap) $x);
    }
    return $y
  };
}

-- EC's local `G3(RO).distinguish`, with `D` a Lean parameter
set_option linter.gaudisCrypt.using false in
module G3 (D : DISTINGUISHER) using (RO : F.RO_T) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call RO.init ();
    G1.m <- (FMap.empty : smap);
    G1.mi <- (FMap.empty : smap);
    G1.mh <- (FMap.empty : hsmap);
    G1.mhi <- (FMap.empty : hsmap);
    -- the empty path is initially known by the adversary to lead to capacity 0^c
    _ <- call (PROM.FullRO.FRO_T.init handle capacity RRO) ();
    _ <- call (PROM.FullRO.FRO_T.set handle capacity RRO) (0, c0);
    G1.paths <- FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0);
    G1.chandle <- 1;
    b <- call (Module.app (DRestr D) (Module.pair (Module.app G3.M RO) (Module.app G3.S RO))) ();
    return $b
  };
}

-- EC's local `G4(RO).C`
module G4.C using (RO : F.RO_T) : DFUNCTIONALITY {
  proc f (p : List block) : block {
    var sa : block, h : handle, i : ℤ;
    h <- 0;
    i <- 0;
    sa <- b0;
    while ($i < size $p) {
      _ <- call RO.sample (take ($i + 1) $p);
      i <- $i + 1;
    }
    sa <- call RO.get ($p);
    return $sa
  };
}

-- EC's local `G4(RO).S`
module G4.S using (RO : F.RO_T) : DPRIMITIVE {
  proc f (x : state) : state {
    var p : List block, v : block, y : state, y1 : block, y2 : capacity;
    if (!(decide (FMap.dom ($G1.m : smap) $x))) {
      if (decide (FMap.dom ($G1.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($G1.paths : FMap capacity (List block × block)) ($x).2);
        y1 <- call RO.get (rcons $p ($v +^ ($x).1));
      } else {
        y1 <$ bdistr;
      }
      y2 <$ cdistr;
      y <- ($y1, $y2);
      G1.m <- FMap.set $G1.m $x $y;
      G1.mi <- FMap.set $G1.mi $y $x;
      if (decide (FMap.dom ($G1.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($G1.paths : FMap capacity (List block × block)) ($x).2);
        G1.paths <- FMap.set $G1.paths ($y).2 (rcons $p ($v +^ ($x).1), ($y).1);
      }
    } else {
      y <- oget (FMap.get ($G1.m : smap) $x);
    }
    return $y
  };
  proc fi (x : state) : state {
    var y : state, y1 : block, y2 : capacity;
    if (!(decide (FMap.dom ($G1.mi : smap) $x))) {
      y1 <$ bdistr;
      y2 <$ cdistr;
      y <- ($y1, $y2);
      G1.mi <- FMap.set $G1.mi $x $y;
      G1.m <- FMap.set $G1.m $y $x;
    } else {
      y <- oget (FMap.get ($G1.mi : smap) $x);
    }
    return $y
  };
}

-- EC's local `G4(RO).distinguish`, with `D` a Lean parameter
set_option linter.gaudisCrypt.using false in
module G4 (D : DISTINGUISHER) using (RO : F.RO_T) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call RO.init ();
    G1.m <- (FMap.empty : smap);
    G1.mi <- (FMap.empty : smap);
    -- the empty path is initially known by the adversary to lead to capacity 0^c
    G1.paths <- FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0);
    b <- call (Module.app (DRestr D) (Module.pair (Module.app G4.C RO) (Module.app G4.S RO))) ();
    return $b
  };
}

section

variable (D : DISTINGUISHER)

/-- The section's `declare module D <: DISTINGUISHER {-C, -Perm, -F.RO, -F.FRO, -S, -Redo}`. -/
def DRestrictions : Prop :=
  FVP.fvP D ≤ (C.footprint ⊔ (Perm.m).footprint ⊔
    (Perm.mi).footprint ⊔ (F.RO.m).footprint ⊔
    (F.FRO.m).footprint ⊔ (S.m).footprint ⊔
    (S.mi).footprint ⊔ (S.paths).footprint ⊔ (Redo.prefixes).footprint)ᶜ

/-- `local equiv G2_G3 : Eager(G2(DRestr(D))).main2 ~ G3(F.LRO).distinguish : ={glob D} ==>
={res}`. -/
theorem G2_G3 (hD : Module.ECModule D distExt) (_hDd : DRestrictions D) :
    prhlProc
      (fun _ g₁ _ g₂ => (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (Eager.main2 (G2 (DRestr D))).procedure (Module.app (G3 D) F.LRO).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  sorry

/-- `local equiv G3_G4 : G3(F.RO).distinguish ~ G4(F.RO).distinguish : ={glob D} ==> ={res}`. -/
theorem G3_G4 (hD : Module.ECModule D distExt) (_hDd : DRestrictions D) :
    prhlProc
      (fun _ g₁ _ g₂ => (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (Module.app (G3 D) F.RO.asRO).procedure (Module.app (G4 D) F.RO.asRO).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  sorry

/-- `local equiv G4_Ideal : G4(F.LRO).distinguish ~ IdealIndif(IF, S, DRestr(D)).main :
={glob D} ==> ={res}`. -/
theorem G4_Ideal (hD : Module.ECModule D distExt) (_hDd : DRestrictions D) :
    prhlProc
      (fun _ g₁ _ g₂ => (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (Module.app (G4 D) F.LRO).procedure (IdealIndif IF S (DRestr D)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  sorry

/-- EC's `Real_Ideal`, with the axiom `D_ll`. -/
theorem Real_Ideal (hD : Module.ECModule D distExt) (_hDd : DRestrictions D)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D)ᶜ →
      FVP.fvP P ≤ (FVP.fvP D)ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (m : VariableAssignment) :
    (Procedure.Pr (GReal D).procedure () m (fun r g => r = true ∧ C.c.get g ≤ max_size) : ℝ) ≤
      (Procedure.Pr (IdealIndif IF S (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) +
        ((max_size ^ 2 - max_size : ℤ) : ℝ) / 2 * (dstate.1 {default}).toReal +
        (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) +
        (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) := by
  sorry

end

end GaudisCrypt.SHA3.Gconcl
