import GaudisCrypt.Examples.SHA3.SmartCounter.Gext

/-!
# Conclusion of the squeezeless sponge proof (EasyCrypt `proof/smart_counter/Gconcl.ec`)

`Real_Ideal`: the real game with the squeezeless sponge is indifferentiable from the ideal
functionality `IF` (the random oracle `F.RO`) with the simulator `S`, up to the switching bound
and the collision and extension probabilities.

Translation notes (see `notes/SHA3/README.md`):
* `module IF = { proc init = F.RO.init  proc f = F.RO.get }` is a definition assembling the
  aliased procedures.
* The section's `local clone import Gext as Gext0` is `Gext`, opened.  The clone's module
  variables (`G1.m`, `PF.m`, `ROhandle.FRO.m` …) are fixed `global_var`s here, so their freshness
  for `D` is the hypothesis `Gext0Fresh D` (exception E13).
* `G3(RO : F.RO)` and `G4(RO : F.RO)` take the module type `F.RO` (`F.RO_T`, exception E3).  Their
  inner modules depend on `RO` only: they are functors of `RO` (`G3.M`, `G3.S`, `G4.C`, `G4.S`);
  `G3 D`, `G4 D` are the games' `distinguish`, with `D` a Lean parameter, and take EasyCrypt's
  `d_in_t = unit` argument, so that they are `F.RO_Distinguisher`s (for `RO_LRO_D`).
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

-- EC's local `G3(RO).distinguish`, with `D` a Lean parameter (on purpose: `G3 D` is an
-- `F.RO_Distinguisher`); its argument is EasyCrypt's `d_in_t = unit`
set_option linter.gaudisCrypt.using false in
module G3 (D : DISTINGUISHER) using (RO : F.RO_T) {
  proc distinguish (_u : Unit) : Bool {
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

-- EC's local `G4(RO).distinguish`, with `D` a Lean parameter (on purpose: `G4 D` is an
-- `F.RO_Distinguisher`); its argument is EasyCrypt's `d_in_t = unit`
set_option linter.gaudisCrypt.using false in
module G4 (D : DISTINGUISHER) using (RO : F.RO_T) {
  proc distinguish (_u : Unit) : Bool {
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

/-! ## The oracles' steps -/

section

variable (D : DISTINGUISHER)

set_option maxHeartbeats 8000000 in
-- `within_lens` on `G3.S`'s procedures, against a pair of nine variables, is slow
/-- `G3 D` touches `glob D` and the variables of `C` and `G1` and `FRO.m` (not `F.RO.m`, its
oracle's).  Not an EC lemma: EasyCrypt reads a concrete module's globals off its code (for
`RO_LRO_D`'s side conditions, in `Real_Ideal`). -/
theorem fvP_G3 :
    FVP.fvP (G3 D) ≤ FVP.fvP D ⊔ (Lens.pair C.c (Lens.pair C.queries (Lens.pair G1.m
      (Lens.pair G1.mi (Lens.pair G1.mh (Lens.pair G1.mhi (Lens.pair G1.chandle
        (Lens.pair G1.paths ROhandle.FRO.m)))))))).footprint := by
  fp_module (Lens.pair C.c (Lens.pair C.queries (Lens.pair G1.m
      (Lens.pair G1.mi (Lens.pair G1.mh (Lens.pair G1.mhi (Lens.pair G1.chandle
        (Lens.pair G1.paths ROhandle.FRO.m))))))))

set_option maxHeartbeats 2000000 in
-- `within_lens` on `G4.S`'s procedures is slow
/-- `G4 D` touches `glob D` and the variables of `C` and `G1.m`, `G1.mi`, `G1.paths` (as
`fvP_G3`). -/
theorem fvP_G4 :
    FVP.fvP (G4 D) ≤ FVP.fvP D ⊔ (Lens.pair C.c (Lens.pair C.queries (Lens.pair G1.m
      (Lens.pair G1.mi G1.paths)))).footprint := by
  fp_module (Lens.pair C.c (Lens.pair C.queries (Lens.pair G1.m (Lens.pair G1.mi G1.paths))))

end

end GaudisCrypt.SHA3.Gconcl
