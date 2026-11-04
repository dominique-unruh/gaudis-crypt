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

set_option hygiene false in
/-- Close a goal of equalities and `colEq` left by a wp step: the reads through the writes, then
`simp_all`. -/
macro "col_close" : tactic => `(tactic| (
  intros
  simp only [colEq] at *
  (try simp_reads)
  simp_all))

/-- `G4_Ideal`'s invariant: `={C.c, C.queries, F.RO.m} /\ G1.m{1} = S.m{2} /\ G1.mi{1} = S.mi{2}
/\ G1.paths{1} = S.paths{2}`. -/
def g4Inv (g₁ g₂ : VariableAssignment) : Prop :=
  C.c.get g₁ = C.c.get g₂ ∧ C.queries.get g₁ = C.queries.get g₂ ∧ F.RO.m.get g₁ = F.RO.m.get g₂ ∧
  G1.m.get g₁ = S.m.get g₂ ∧ G1.mi.get g₁ = S.mi.get g₂ ∧ G1.paths.get g₁ = S.paths.get g₂

/-- `DPRestr(G4(LRO).S).fi ~ DPRestr(S(IF)).fi` under `g4Inv` (EC: `sim`). -/
theorem DPRestr_fi_G4I :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g4Inv g₁ g₂)
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr (Module.app G4.S F.LRO))).procedure
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr
          (Indifferentiability.DPRIMITIVE.mk state (List block) block
            { f := Indifferentiability.PRIMITIVE.f state (List block) block
                (Module.app S (Indifferentiability.FUNCTIONALITY.view state (List block) block IF)),
              fi := Indifferentiability.PRIMITIVE.fi state (List block) block
                (Module.app S
                  (Indifferentiability.FUNCTIONALITY.view state (List block) block IF))
                      }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g4Inv g₁ g₂) := by
  unfold g4Inv
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §C.c{1} = §C.c{2} ∧
      §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧ §G1.m{1} = §S.m{2} ∧
      §G1.mi{1} = §S.mi{2} ∧ §G1.paths{1} = §S.paths{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» =>
      equiv_skip
      intros; simp_all
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§x1{1} = §x1{2} ∧ §C.c{1} = §C.c{2} ∧
          §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧ §G1.m{1} = §S.m{2} ∧
          §G1.mi{1} = §S.mi{2} ∧ §G1.paths{1} = §S.paths{2})
      · stmt_wp
        equiv_skip
        intros; simp_all
      · equiv_if
        case guard => intros; simp_all
        case «else» =>
          stmt_wp
          equiv_skip
          intros; simp_all
        case «then» =>
          stmt_wp
          equiv_rnd
          equiv_rnd
          equiv_skip
          intros; simp_all

set_option maxHeartbeats 1000000 in
-- the inlined oracles' wp goals are large
/-- `DPRestr(G4(LRO).S).f ~ DPRestr(S(IF)).f` under `g4Inv` (EC: `sim`). -/
theorem DPRestr_f_G4I :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g4Inv g₁ g₂)
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr (Module.app G4.S F.LRO))).procedure
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr
          (Indifferentiability.DPRIMITIVE.mk state (List block) block
            { f := Indifferentiability.PRIMITIVE.f state (List block) block
                (Module.app S (Indifferentiability.FUNCTIONALITY.view state (List block) block IF)),
              fi := Indifferentiability.PRIMITIVE.fi state (List block) block
                (Module.app S
                  (Indifferentiability.FUNCTIONALITY.view state (List block) block IF))
                      }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g4Inv g₁ g₂) := by
  unfold g4Inv
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §C.c{1} = §C.c{2} ∧
      §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧ §G1.m{1} = §S.m{2} ∧
      §G1.mi{1} = §S.mi{2} ∧ §G1.paths{1} = §S.paths{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» =>
      equiv_skip
      intros; simp_all
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§x1{1} = §x1{2} ∧ §C.c{1} = §C.c{2} ∧
          §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧ §G1.m{1} = §S.m{2} ∧
          §G1.mi{1} = §S.mi{2} ∧ §G1.paths{1} = §S.paths{2})
      · stmt_wp
        equiv_skip
        intros; simp_all
      · equiv_if
        case guard => intros; simp_all
        case «else» =>
          stmt_wp
          equiv_skip
          intros; simp_all
        case «then» =>
          stmt_wp
          equiv_rnd
          equiv_if
          case guard => intros; simp_all
          case «else» =>
            equiv_rnd
            equiv_skip
            intros; simp_all
          case «then» =>
            stmt_wp
            equiv_rnd
            stmt_wp
            equiv_skip
            rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -⟩, -⟩ _ - _ -
            and_intros <;> rfl

/-- `DFRestr(G4(LRO).C).f ~ DFRestr(IF).f` under `g4Inv` (EC: `inline F.LRO.get F.FRO.sample;
wp 7 2; sim; while{1} (true) (size p - i){1}`). -/
theorem DFRestr_f_G4I :
    prhlProc (sig₁ := procsig (List block) -> block) (sig₂ := procsig (List block) -> block)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g4Inv g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr (Module.app G4.C F.LRO))).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr
          (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
            { f := Indifferentiability.FUNCTIONALITY.f state (List block) block IF }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g4Inv g₁ g₂) := by
  unfold g4Inv
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§bs{1} = §bs{2} ∧ §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧
      §C.c{1} = §C.c{2} ∧ §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧
      §G1.m{1} = §S.m{2} ∧ §G1.mi{1} = §S.mi{2} ∧ §G1.paths{1} = §S.paths{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» =>
      stmt_wp
      equiv_skip
      intros; simp_all
    case «then» =>
      equiv_if
      case guard => intros; simp_all
      case «else» =>
        equiv_skip
        intros; simp_all
      case «then» =>
        equiv_seq 7 6 : (§p{1} = §bs{2} ∧ §bs{1} = §bs{2} ∧
            §C.c{1} = §C.c{2} ∧ §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧
            §G1.m{1} = §S.m{2} ∧ §G1.mi{1} = §S.mi{2} ∧ §G1.paths{1} = §S.paths{2})
        · equiv_while{1} (§p{1} = §bs{2} ∧ §bs{1} = §bs{2} ∧
              §C.c{1} = §C.c{2} ∧ §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧
              §G1.m{1} = §S.m{2} ∧ §G1.mi{1} = §S.mi{2} ∧ §G1.paths{1} = §S.paths{2})
            (size §p{1} - §i{1}).toNat
          case lossless =>
            intro σ₁ σ _ _
            simp [Stmt.ewp_seq, Stmt.ewp_assign]
          case «variant» =>
            intro σ₂ k
            hoare_wp 3
            hoare_skip
            rintro p bs c queries m m1 mi paths i ⟨h, hc, rfl⟩
            refine ⟨h, ?_⟩
            simp only [decide_eq_true_eq] at hc
            omega
          case exit =>
            intros; simp_all
          stmt_wp
          equiv_skip
          intros; simp_all
        · stmt_wp
          equiv_rnd
          stmt_wp
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ _ -
          and_intros <;> rfl

/-- `G3_G4`'s invariant: `={G1.m, G1.mi, G1.paths, F.RO.m, C.c, C.queries}`. -/
def g34Inv (g₁ g₂ : VariableAssignment) : Prop :=
  C.c.get g₁ = C.c.get g₂ ∧ C.queries.get g₁ = C.queries.get g₂ ∧ F.RO.m.get g₁ = F.RO.m.get g₂ ∧
  G1.m.get g₁ = G1.m.get g₂ ∧ G1.mi.get g₁ = G1.mi.get g₂ ∧ G1.paths.get g₁ = G1.paths.get g₂

set_option maxHeartbeats 2000000 in
-- the inlined oracles' wp goals are large
/-- `DPRestr(G3(RO).S).fi ~ DPRestr(G4(RO).S).fi` under `g34Inv` (EC: `seq 5 0` over `G3`'s
bookkeeping, `seq 3 3` over the samples, `if{1}`). -/
theorem DPRestr_fi_G34 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g34Inv g₁ g₂)
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr (Module.app G3.S F.RO.asRO))).procedure
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr (Module.app G4.S F.RO.asRO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g34Inv g₁ g₂) := by
  unfold g34Inv
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §C.c{1} = §C.c{2} ∧
      §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧ §G1.m{1} = §G1.m{2} ∧
      §G1.mi{1} = §G1.mi{2} ∧ §G1.paths{1} = §G1.paths{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» =>
      equiv_skip
      intros; simp_all
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§x1{1} = §x1{2} ∧ §C.c{1} = §C.c{2} ∧
          §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧ §G1.m{1} = §G1.m{2} ∧
          §G1.mi{1} = §G1.mi{2} ∧ §G1.paths{1} = §G1.paths{2})
      · stmt_wp
        equiv_skip
        intros; simp_all
      · equiv_if
        case guard => intros; simp_all
        case «else» =>
          stmt_wp
          equiv_skip
          intros; simp_all
        case «then» =>
          stmt_wp
          equiv_rnd
          equiv_rnd
          stmt_wp
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -⟩ _ - _ -
          simp only [ite_self, and_self]

set_option maxHeartbeats 2000000 in
-- the inlined oracles' wp goals are large
/-- `DPRestr(G3(RO).S).f ~ DPRestr(G4(RO).S).f` under `g34Inv` (EC: `seq 3 3` over the samples,
`seq 5 0` over `G3`'s bookkeeping, `if{1}`). -/
theorem DPRestr_f_G34 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g34Inv g₁ g₂)
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr (Module.app G3.S F.RO.asRO))).procedure
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr (Module.app G4.S F.RO.asRO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g34Inv g₁ g₂) := by
  unfold g34Inv
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §C.c{1} = §C.c{2} ∧
      §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧ §G1.m{1} = §G1.m{2} ∧
      §G1.mi{1} = §G1.mi{2} ∧ §G1.paths{1} = §G1.paths{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» =>
      equiv_skip
      intros; simp_all
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§x1{1} = §x1{2} ∧ §C.c{1} = §C.c{2} ∧
          §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧ §G1.m{1} = §G1.m{2} ∧
          §G1.mi{1} = §G1.mi{2} ∧ §G1.paths{1} = §G1.paths{2})
      · stmt_wp
        equiv_skip
        intros; simp_all
      · equiv_if
        case guard => intros; simp_all
        case «else» =>
          stmt_wp
          equiv_skip
          intros; simp_all
        case «then» =>
          equiv_seq 2 3 : (§x1{1} = §x1{2} ∧ §y0{1} = §y0{2} ∧ §C.c{1} = §C.c{2} ∧
              §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧ §G1.m{1} = §G1.m{2} ∧
              §G1.mi{1} = §G1.mi{2} ∧ §G1.paths{1} = §G1.paths{2})
          · stmt_wp
            equiv_rnd
            equiv_if
            case guard => intros; simp_all
            case «else» =>
              equiv_rnd
              equiv_skip
              rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -⟩,
                  -⟩ _ - _ -
              simp only [ite_self, and_self]
            case «then» =>
              stmt_wp
              equiv_rnd
              stmt_wp
              equiv_skip
              rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -⟩,
                  -⟩ _ - _ -
              simp only [ite_self, and_self]
          · stmt_wp
            equiv_skip
            rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp only [ite_self, and_self]

set_option maxHeartbeats 4000000 in
-- the inlined oracles' wp goals are large
/-- `DFRestr(G3(RO).M).f ~ DFRestr(G4(RO).C).f` under `g34Inv` (EC: `while (={i, p, F.RO.m})`,
`if{1}` twice, `RRO.sample`'s sample one-sided). -/
theorem DFRestr_f_G34 :
    prhlProc (sig₁ := procsig (List block) -> block) (sig₂ := procsig (List block) -> block)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g34Inv g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr (Module.app G3.M F.RO.asRO))).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr (Module.app G4.C F.RO.asRO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g34Inv g₁ g₂) := by
  unfold g34Inv
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§bs{1} = §bs{2} ∧ §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧
      §C.c{1} = §C.c{2} ∧ §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧
      §G1.m{1} = §G1.m{2} ∧ §G1.mi{1} = §G1.mi{2} ∧ §G1.paths{1} = §G1.paths{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» =>
      stmt_wp
      equiv_skip
      intros; simp_all
    case «then» =>
      equiv_if
      case guard => intros; simp_all
      case «else» =>
        equiv_skip
        intros; simp_all
      case «then» =>
        equiv_seq 7 7 : (§p{1} = §p{2} ∧ §bs{1} = §bs{2} ∧
            §C.c{1} = §C.c{2} ∧ §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧
            §G1.m{1} = §G1.m{2} ∧ §G1.mi{1} = §G1.mi{2} ∧ §G1.paths{1} = §G1.paths{2})
        · equiv_while (§p{1} = §p{2} ∧ §i{1} = §i{2} ∧ §bs{1} = §bs{2} ∧
              §C.c{1} = §C.c{2} ∧ §C.queries{1} = §C.queries{2} ∧ §F.RO.m{1} = §F.RO.m{2} ∧
              §G1.m{1} = §G1.m{2} ∧ §G1.mi{1} = §G1.mi{2} ∧ §G1.paths{1} = §G1.paths{2})
          case body =>
            stmt_wp
            equiv_if{1}
            case «then» =>
              stmt_wp
              equiv_rnd
              stmt_wp
              equiv_skip
              rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -⟩, -⟩ _ -
              and_intros <;> rfl
            case «else» =>
              equiv_if{1}
              case «then» =>
                stmt_wp
                equiv_rnd
                stmt_wp
                stmt_wp{1} 1
                stmt_wp
                equiv_skip
                rintro _ _ _ _ _ _ _ _ _ _ ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -⟩,
                    -⟩, -⟩
                refine ⟨cdistr_expected_one, fun _ _ _ _ => ?_⟩
                simp only [ite_self, and_self]
              case «else» =>
                stmt_wp
                equiv_rnd
                stmt_wp
                equiv_skip
                rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -⟩, -⟩, -⟩ _ -
                simp only [ite_self, and_self]
          case guard => intros; simp_all
          case exit => intros; simp_all
          stmt_wp
          equiv_skip
          intros; simp_all
        · stmt_wp
          equiv_rnd
          stmt_wp
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ _ -
          and_intros <;> rfl

/-- The guard `(x.1, hx2) \in G1.mh /\ t` of `G2.S.f` and `G3.S.f`, from the state before their
bookkeeping (`HS.allKnown`, `HS.set`, `HS.queried`). -/
noncomputable def sfGuard (F : FMap handle (capacity × flag)) (ch : ℤ) (mh : hsmap) (x : state) :
    Bool :=
  let F' := if (!decide ((FMap.restr Known F).rng x.2)) = true then F.set ch (x.2, Known) else F
  let hx2 := oget (hinvc (FMap.restr Known F') x.2)
  decide (FMap.dom mh (x.1, hx2)) &&
    decide (F'.dom (oget (FMap.get mh (x.1, hx2))).2 ∧
      is_ (F'.get (oget (FMap.get mh (x.1, hx2))).2) Unknown)

set_option maxHeartbeats 4000000 in
-- the inlined oracles' wp goals are large
/-- `DPRestr(G2(RRO).S).f ~ DPRestr(G3(LRO).S).f` under `colEq`.  EC moves the bookkeeping before
the samples (`swap`), cases on the guard `(x.1, hx2) \in G1.mh /\ t` and couples `RRO.get`'s
sample with `G3`'s `y2` when it holds (`rcondt`).  Here the case is on `sfGuard` of the state
before the bookkeeping (`stmt_swap` does not commute two `reset_vars`), and when it holds `G3`'s
`y2` is moved past the bookkeeping instead. -/
theorem DPRestr_f_G23 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ colEq g₁ g₂)
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr (Module.app G2.S
          (FullRO.FullEager.RRO handle capacity ROhandle.dout ROhandle.FRO.m)))).procedure
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr (Module.app G3.S F.LRO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ colEq g₁ g₂) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ colEq §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all [colEq]
    case «else» =>
      equiv_skip
      intros; simp_all
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§x1{1} = §x1{2} ∧ colEq §allGlobals{1} §allGlobals{2})
      · stmt_wp
        equiv_skip
        intros; simp_all
      · equiv_if
        case guard => intros; simp_all [colEq]
        case «else» =>
          stmt_wp
          equiv_skip
          rintro g₁ g₂ x1 _ ⟨⟨rfl, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, -⟩
          exact ⟨by rw [e4], by col_eq⟩
        case «then» =>
          equiv_case (sfGuard §ROhandle.FRO.m{1} §G1.chandle{1} §G1.mh{1} §x1{1} = true)
          · stmt_swap{2} 2 9
            stmt_swap{2} 1 9
            equiv_seq 1 1 : (§x1{1} = §x1{2} ∧ §y0{1} = §y0{2} ∧ colEq §allGlobals{1}
                §allGlobals{2})
            · equiv_seq 11 12 : (§x1{1} = §x1{2} ∧ §y1{1} = §y1{2} ∧
                  colEq §allGlobals{1} §allGlobals{2} ∧
                  sfGuard §ROhandle.FRO.m{1} §G1.chandle{1} §G1.mh{1} §x1{1} = true)
              · equiv_if{1}
                case «then» =>
                  stmt_wp{1} 1
                  equiv_if{2}
                  case «then» =>
                    stmt_wp
                    equiv_rnd
                    stmt_wp
                    equiv_skip
                    rintro g₁ g₂ x1 _ ⟨⟨⟨⟨⟨rfl, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, -⟩,
                        hg⟩, -⟩, -⟩
                      a -
                    refine ⟨cdistr_expected_one, fun b _ => ?_⟩
                    simp only [ite_self]
                    exact ⟨trivial, by rw [e1, e3], by col_eq, hg⟩
                  case «else» =>
                    refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
                    obtain ⟨⟨⟨⟨⟨hx, hE⟩, -⟩, -⟩, h1⟩, h2⟩ := h
                    simp [hx, hE.2.2.1] at h1
                    simp [h1] at h2
                case «else» =>
                  stmt_wp{1} 1
                  equiv_if{2}
                  case «then» =>
                    refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
                    obtain ⟨⟨⟨⟨⟨hx, hE⟩, -⟩, -⟩, h1⟩, h2⟩ := h
                    simp [hx, hE.2.2.1] at h1
                    simp [h1] at h2
                  case «else» =>
                    equiv_rnd
                    equiv_skip
                    rintro g₁ g₂ x1 _ ⟨⟨⟨⟨⟨rfl, hE⟩, -⟩, hg⟩, -⟩, -⟩ - -
                    exact ⟨cdistr_expected_one, fun _ _ => ⟨rfl, hE, hg⟩⟩
              · equiv_seq 1 3 : (§x1{1} = §x1{2} ∧ (§y0{1}).1 = §y1{2} ∧ §hx2{1} = §hx2{2} ∧
                    §t{1} = §t{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
                    §t{1} = decide (FMap.dom §ROhandle.FRO.m{1}
                      (oget (FMap.get §G1.mh{1} ((§x1{1}).1, §hx2{1}))).2 ∧
                      is_ (FMap.get §ROhandle.FRO.m{1}
                        (oget (FMap.get §G1.mh{1} ((§x1{1}).1, §hx2{1}))).2) Unknown) ∧
                    (decide (FMap.dom §G1.mh{1} ((§x1{1}).1, §hx2{1})) && §t{1}) = true)
                · stmt_wp
                  equiv_skip
                  rintro g₁ g₂ x1 y1 y2 _ _ ⟨rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9,
                      e10⟩, hg⟩
                  simp only [FRO.m] at e8
                  simp only [ite_self]
                  rw [e8, e6, e7] at hg ⊢
                  simp only [sfGuard] at hg
                  refine ⟨trivial, trivial, rfl, rfl, ?_, hg⟩
                  split_ifs <;> col_eq
                · equiv_if{1}
                  case «then» =>
                    stmt_wp
                    equiv_rnd
                    stmt_wp
                    equiv_skip
                    rintro g₁ g₂ x1 y0 hx2 t _ y1 _ _
                      ⟨⟨rfl, hy, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, ht, -⟩,
                          hg⟩ a -
                    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
                    obtain ⟨hdom, rfl⟩ := hg
                    simp only [eq_comm (a := true), decide_eq_true_eq] at ht
                    simp only [FRO.m] at e8
                    simp only [ht.2, decide_true, Bool.or_true, if_true, ite_self]
                    rw [← e7]
                    simp only [hdom, decide_true, Bool.true_and, if_true, FMap.get_set_sameE, oget]
                    subst hy
                    exact ⟨trivial, rfl, by col_eq⟩
                  case «else» =>
                    refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
                    exact Bool.false_ne_true (h.2.symm.trans h.1.2.2.2.2.2.2)
            · stmt_wp
              equiv_skip
              rintro g₁ g₂ x1 y0 _ _ ⟨rfl, rfl, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩
              rw [e3]
              split_ifs <;> exact ⟨rfl, by col_eq⟩
          · equiv_seq 1 1 : (§x1{1} = §x1{2} ∧ §y0{1} = §y0{2} ∧ colEq §allGlobals{1}
              §allGlobals{2})
            · equiv_seq 11 11 : (§x1{1} = §x1{2} ∧ §y1{1} = §y1{2} ∧ §y2{1} = §y2{2} ∧
                  colEq §allGlobals{1} §allGlobals{2} ∧
                  sfGuard §ROhandle.FRO.m{1} §G1.chandle{1} §G1.mh{1} §x1{1} = false)
              · equiv_if{1}
                case «then» =>
                  equiv_rnd
                  equiv_if{2}
                  case «then» =>
                    stmt_wp
                    equiv_rnd
                    stmt_wp
                    equiv_skip
                    rintro g₁ g₂ x1 _ ⟨⟨⟨⟨⟨rfl, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, -⟩,
                        hg⟩, -⟩, -⟩
                      a - b -
                    simp only [ite_self]
                    refine ⟨trivial, by rw [e1, e3], by col_eq, by simpa using hg⟩
                  case «else» =>
                    refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
                    obtain ⟨⟨⟨⟨⟨hx, hE⟩, -⟩, -⟩, h1⟩, h2⟩ := h
                    simp [hx, hE.2.2.1] at h1
                    simp [h1] at h2
                case «else» =>
                  equiv_rnd
                  equiv_if{2}
                  case «then» =>
                    refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
                    obtain ⟨⟨⟨⟨⟨hx, hE⟩, -⟩, -⟩, h1⟩, h2⟩ := h
                    simp [hx, hE.2.2.1] at h1
                    simp [h1] at h2
                  case «else» =>
                    equiv_rnd
                    equiv_skip
                    rintro g₁ g₂ x1 _ ⟨⟨⟨⟨⟨rfl, hE⟩, -⟩, hg⟩, -⟩, -⟩ - - - -
                    exact ⟨rfl, hE, by simpa using hg⟩
              · equiv_seq 1 1 : (§x1{1} = §x1{2} ∧ §y0{1} = §y0{2} ∧ §hx2{1} = §hx2{2} ∧
                    §t{1} = §t{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
                    (decide (FMap.dom §G1.mh{1} ((§x1{1}).1, §hx2{1})) && §t{1}) = false)
                · stmt_wp
                  equiv_skip
                  rintro g₁ g₂ x1 y1 y2 _ _ _ ⟨rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8,
                      e9, e10⟩,
                    hg⟩
                  simp only [FRO.m] at e8
                  simp only [ite_self]
                  rw [e8, e6, e7] at hg ⊢
                  simp only [sfGuard] at hg
                  refine ⟨trivial, trivial, rfl, rfl, ?_, hg⟩
                  split_ifs <;> col_eq
                · equiv_if
                  case guard =>
                    rintro g₁ g₂ x1 y0 hx2 t _ _ _ _ ⟨rfl, rfl, rfl, rfl, hE, -⟩
                    rw [hE.2.2.2.2.2.2.1]
                  case «then» =>
                    refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
                    exact Bool.false_ne_true (h.1.2.2.2.2.2.symm.trans h.2)
                  case «else» =>
                    stmt_wp
                    equiv_skip
                    rintro g₁ g₂ x1 y0 hx2 t _ _ _ _
                      ⟨⟨rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, -⟩, -⟩
                    exact ⟨rfl, rfl, by col_eq⟩
            · stmt_wp
              equiv_skip
              rintro g₁ g₂ x1 y0 _ _ ⟨rfl, rfl, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩
              rw [e3]
              split_ifs <;> exact ⟨rfl, by col_eq⟩

set_option maxHeartbeats 4000000 in
-- the inlined oracles' wp goals are large
/-- `DPRestr(G2(RRO).S).fi ~ DPRestr(G3(LRO).S).fi` under `colEq` (EC: `swap{1} 8 -3`, `seq 6 6`,
`case` on the guard, `rcondt`, `RRO.get`'s sample coupled with `G3`'s `y2`). -/
theorem DPRestr_fi_G23 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ colEq g₁ g₂)
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr (Module.app G2.S
          (FullRO.FullEager.RRO handle capacity ROhandle.dout ROhandle.FRO.m)))).procedure
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr (Module.app G3.S F.LRO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ colEq g₁ g₂) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ colEq §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all [colEq]
    case «else» =>
      equiv_skip
      intros; simp_all
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§x1{1} = §x1{2} ∧ colEq §allGlobals{1} §allGlobals{2})
      · stmt_wp
        equiv_skip
        intros; simp_all
      · equiv_if
        case guard => intros; simp_all [colEq]
        case «else» =>
          stmt_wp
          equiv_skip
          rintro g₁ g₂ x1 _ ⟨⟨rfl, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, -⟩
          exact ⟨by rw [e2], by col_eq⟩
        case «then» =>
          stmt_swap{1} 9 -3
          stmt_swap{1} 10 -3
          stmt_swap{1} 11 -3
          equiv_seq 4 4 : (§x1{1} = §x1{2} ∧ §hx2{1} = §hx2{2} ∧ §t{1} = §t{2} ∧
              colEq §allGlobals{1} §allGlobals{2} ∧
              §t{1} = decide (FMap.dom §ROhandle.FRO.m{1}
                (oget (FMap.get §G1.mhi{1} ((§x1{1}).1, §hx2{1}))).2 ∧
                is_ (FMap.get §ROhandle.FRO.m{1}
                  (oget (FMap.get §G1.mhi{1} ((§x1{1}).1, §hx2{1}))).2) Unknown))
          · stmt_wp
            equiv_skip
            rintro g₁ g₂ x1 _ ⟨⟨rfl, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, -⟩
            simp only [FRO.m] at e8
            simp only [ite_self]
            rw [e8, e6, e5]
            refine ⟨trivial, rfl, rfl, ?_⟩
            split_ifs <;> col_eq
          · equiv_case ((decide (FMap.dom §G1.mhi{1} ((§x1{1}).1, §hx2{1})) && §t{1}) = true)
            · equiv_seq 1 3 : (§x1{1} = §x1{2} ∧ (§y0{1}).1 = §y1{2} ∧ §hx2{1} = §hx2{2} ∧
                  §t{1} = §t{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
                  §t{1} = decide (FMap.dom §ROhandle.FRO.m{1}
                    (oget (FMap.get §G1.mhi{1} ((§x1{1}).1, §hx2{1}))).2 ∧
                    is_ (FMap.get §ROhandle.FRO.m{1}
                      (oget (FMap.get §G1.mhi{1} ((§x1{1}).1, §hx2{1}))).2) Unknown) ∧
                  (decide (FMap.dom §G1.mhi{1} ((§x1{1}).1, §hx2{1})) && §t{1}) = true)
              · stmt_wp
                stmt_wp{1} 1
                equiv_rnd
                equiv_skip
                rintro g₁ g₂ x1 hx2 t _ _ _ ⟨⟨rfl, rfl, rfl, hE, ht⟩, hg⟩ - -
                exact ⟨cdistr_expected_one, fun _ _ => ⟨rfl, rfl, rfl, hE, ht, hg⟩⟩
              · equiv_if{1}
                case «then» =>
                  stmt_wp
                  equiv_rnd
                  stmt_wp
                  equiv_skip
                  rintro g₁ g₂ x1 y0 hx2 t _ y1 _ _
                    ⟨⟨rfl, hy, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, ht, -⟩, hg⟩ a -
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
                  obtain ⟨hdom, rfl⟩ := hg
                  simp only [eq_comm (a := true), decide_eq_true_eq] at ht
                  simp only [FRO.m] at e8
                  simp only [ht.2, decide_true, Bool.or_true, if_true, ite_self]
                  rw [← e5]
                  simp only [hdom, decide_true, Bool.true_and, if_true, FMap.get_set_sameE, oget]
                  subst hy
                  exact ⟨rfl, by col_eq⟩
                case «else» =>
                  refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
                  exact Bool.false_ne_true (h.2.symm.trans h.1.2.2.2.2.2.2)
            · equiv_seq 1 1 : (§x1{1} = §x1{2} ∧ §y0{1} = §y0{2} ∧ §hx2{1} = §hx2{2} ∧
                  §t{1} = §t{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
                  (decide (FMap.dom §G1.mhi{1} ((§x1{1}).1, §hx2{1})) && §t{1}) = false)
              · stmt_wp
                equiv_rnd
                equiv_rnd
                equiv_skip
                rintro g₁ g₂ x1 hx2 t _ _ _ ⟨⟨rfl, rfl, rfl, hE, -⟩, hg⟩ - - - -
                exact ⟨rfl, rfl, rfl, hE, by simpa using hg⟩
              · equiv_if
                case guard =>
                  rintro g₁ g₂ x1 y0 hx2 t _ _ _ _ ⟨rfl, rfl, rfl, rfl, hE, -⟩
                  rw [hE.2.2.2.2.1]
                case «then» =>
                  refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
                  exact Bool.false_ne_true (h.1.2.2.2.2.2.symm.trans h.2)
                case «else» =>
                  stmt_wp
                  equiv_skip
                  rintro g₁ g₂ x1 y0 hx2 t _ _ _ _
                    ⟨⟨rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, -⟩, -⟩
                  exact ⟨rfl, by col_eq⟩

set_option maxHeartbeats 4000000 in
-- the inlined oracles' wp goals are large
/-- `DFRestr(G2(RRO).M).f ~ DFRestr(G3(LRO).M).f` under `colEq` (EC: `inline*; sim`; `LRO.sample`
does nothing). -/
theorem DFRestr_f_G23 :
    prhlProc (sig₁ := procsig (List block) -> block) (sig₂ := procsig (List block) -> block)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ colEq g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr (Module.app G2.M
          (FullRO.FullEager.RRO handle capacity ROhandle.dout ROhandle.FRO.m)))).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr (Module.app G3.M F.LRO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ colEq g₁ g₂) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§bs{1} = §bs{2} ∧ §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧
      colEq §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => col_close
    case «else» =>
      stmt_wp
      equiv_skip
      col_close
    case «then» =>
      equiv_if
      case guard => col_close
      case «else» =>
        equiv_skip
        intros; simp_all
      case «then» =>
        equiv_seq 7 7 : (§p{1} = §p{2} ∧ §bs{1} = §bs{2} ∧ colEq §allGlobals{1} §allGlobals{2})
        · equiv_while (§p{1} = §p{2} ∧ §i{1} = §i{2} ∧ §bs{1} = §bs{2} ∧
              §(localVarLens "h" handle){1} = §(localVarLens "h" handle){2} ∧ §sa{1} = §sa{2} ∧
              §counter{1} = §counter{2} ∧ colEq §allGlobals{1} §allGlobals{2})
          case body =>
            stmt_wp
            equiv_if
            case guard => col_close
            case «then» =>
              stmt_wp
              equiv_skip
              col_close
            case «else» =>
              equiv_if
              case guard => col_close
              case «then» =>
                stmt_wp
                equiv_rnd
                stmt_wp
                equiv_rnd
                stmt_wp
                equiv_skip
                col_close
              case «else» =>
                stmt_wp
                equiv_skip
                col_close
          case guard => col_close
          case exit => col_close
          stmt_wp
          equiv_skip
          col_close
        · stmt_wp
          equiv_rnd
          stmt_wp
          equiv_skip
          col_close

section

variable (D : DISTINGUISHER)

/-- The section's `declare module D <: DISTINGUISHER {-C, -Perm, -F.RO, -F.FRO, -S, -Redo}`. -/
def DRestrictions : Prop :=
  FVP.fvP D ≤ (C.footprint ⊔ (Perm.m).footprint ⊔
    (Perm.mi).footprint ⊔ (F.RO.m).footprint ⊔
    (F.FRO.m).footprint ⊔ (S.m).footprint ⊔
    (S.mi).footprint ⊔ (S.paths).footprint ⊔ (Redo.prefixes).footprint)ᶜ

/-- The variables of the section's `local clone import Gext as Gext0` lie outside `D`: in EasyCrypt
the clone's modules are new, so `D` cannot touch them; here they are `Handle`'s, `ConcreteF`'s and
`Gext`'s `global_var`s (exception E13). -/
def Gext0Fresh : Prop :=
  FVP.fvP D ≤ ((PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔ (G1.mi).footprint ⊔
    (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔
    G1.bext.footprint ⊔ G1.bcol.footprint ⊔ (FRO.m).footprint ⊔ (ROhandle.RO.m).footprint)ᶜ

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

set_option maxHeartbeats 4000000 in
-- the ten-variable invariant and the oracles' footprint checks
/-- `local equiv G2_G3 : Eager(G2(DRestr(D))).main2 ~ G3(F.LRO).distinguish : ={glob D} ==>
={res}`.  EC: `proc; wp; call{1} RRO_resample_ll; inline *; wp; call (_: ={FRO.m, F.RO.m, G1.m,
G1.mi, G1.mh, G1.mhi, G1.chandle, G1.paths, C.c, C.queries}); last by auto`. -/
theorem G2_G3 (hD : Module.ECModule D distExt) (_hDd : DRestrictions D) (_hG : Gext0Fresh D) :
    prhlProc
      (fun _ g₁ _ g₂ => (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (Eager.main2 (G2 (DRestr D))).procedure (Module.app (G3 D) F.LRO).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hcc : (C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hcq : (C.queries).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hro : (F.RO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hm : (G1.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hmi : (G1.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hmh : (G1.mh).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hmhi : (G1.mhi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hch : (G1.chandle).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hpa : (G1.paths).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hbx : (G1.bext).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hfro : (FRO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  -- the oracles write `FRO.m` as `ROhandle.FRO.m` (`writes_keep'` matches syntactically)
  have hfro' : (ROhandle.FRO.m).footprint ≤ (FVP.fvP D)ᶜ := hfro
  let L := Lens.pair C.c (Lens.pair C.queries (Lens.pair F.RO.m (Lens.pair FRO.m (Lens.pair G1.m
    (Lens.pair G1.mi (Lens.pair G1.mh (Lens.pair G1.mhi (Lens.pair G1.chandle G1.paths))))))))
  let I : ℤ × FMap (List block) block × FMap (List block) block ×
      FMap handle (capacity × flag) × smap × smap × hsmap × hsmap × ℤ ×
      FMap capacity (List block × block) →
      ℤ × FMap (List block) block × FMap (List block) block ×
      FMap handle (capacity × flag) × smap × smap × hsmap × hsmap × ℤ ×
      FMap capacity (List block × block) → Prop := fun x y =>
    x.2.2.1 = y.2.2.1 ∧ x.2.2.2.2.2.1 = y.2.2.2.2.2.1 ∧
      x.2.2.2.2.2.2.2.2.2 = y.2.2.2.2.2.2.2.2.2 ∧ x.2.2.2.2.1 = y.2.2.2.2.1 ∧
      x.2.2.2.2.2.2.2.1 = y.2.2.2.2.2.2.2.1 ∧ x.2.2.2.2.2.2.2.2.1 = y.2.2.2.2.2.2.2.2.1 ∧
      x.2.2.2.2.2.2.1 = y.2.2.2.2.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧ x.1 = y.1 ∧ x.2.1 = y.2.1
  have hI : ∀ g₁ g₂, I (L.get g₁) (L.get g₂) ↔ colEq g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (L.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [L, Footprint.lens_pair]
    exact sup_le hcc (sup_le hcq (sup_le hro (sup_le hfro (sup_le hm (sup_le hmi
      (sup_le hmh (sup_le hmhi (sup_le hch hpa))))))))
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  -- EC's `call{1} RRO_resample_ll`: the trailing `RRO.resample()` is lossless and keeps `res`
  stmt_split{1} 1
  apply prhlStmt_seq_left
  stmt_wp
  equiv_seq 1 1 : (globInvF L (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    refine ⟨?_, (hI _ _).mpr ?_⟩
    · simp only [touched_set_of_le_compl hcc, touched_set_of_le_compl hcq,
        touched_set_of_le_compl hro, touched_set_of_le_compl hm, touched_set_of_le_compl hmi,
        touched_set_of_le_compl hmh, touched_set_of_le_compl hmhi, touched_set_of_le_compl hch,
        touched_set_of_le_compl hpa, touched_set_of_le_compl hbx, touched_set_of_le_compl hfro']
      exact h
    · simp only [colEq]
      simp_reads
      trivial
  · stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_moduleF L D distExt hD.representable
      (FVP.fvP D) le_rfl hL I ?hc _ _ ?horacle) ?_
    case hc =>
      intro _ n
      cases n with
      | zero => exact inferInstanceAs (Countable (List block))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable state)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable state)
          | succ n => nomatch n
    case horacle =>
      intro _ n
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair]
        exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
          DFRestr_f_G23
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair]
          exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
            DPRestr_f_G23
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair]
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              DPRestr_fi_G23
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, -, -⟩
    refine ⟨Stmt.call_wp_one (PROM.FullRO.FullEager.RRO_resample_ll handle capacity ROhandle.dout
      ROhandle.FRO.m (fun _ => BitWord.dunifin_ll)) _ _ _, Stmt.call_satisfies fun r' _ => ?_⟩
    dsimp only
    simp only [Setter.throwaway]
    simp_reads
    trivial

set_option maxHeartbeats 1000000 in
-- the six-variable invariant and the oracles' footprint checks
/-- `local equiv G3_G4 : G3(F.RO).distinguish ~ G4(F.RO).distinguish : ={glob D} ==> ={res}`.
EC: `proc; inline *; wp; call (_: ={G1.m, G1.mi, G1.paths, F.RO.m, C.c, C.queries}); last by
auto`. -/
theorem G3_G4 (hD : Module.ECModule D distExt) (_hDd : DRestrictions D) (_hG : Gext0Fresh D) :
    prhlProc
      (fun _ g₁ _ g₂ => (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (Module.app (G3 D) F.RO.asRO).procedure (Module.app (G4 D) F.RO.asRO).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hcc : (C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hcq : (C.queries).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hro : (F.RO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hm : (G1.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hmi : (G1.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hmh : (G1.mh).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hmhi : (G1.mhi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hch : (G1.chandle).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hpa : (G1.paths).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hfro : (FRO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  -- `G3`'s oracles write `FRO.m` as `ROhandle.FRO.m` (`writes_keep'` matches syntactically)
  have hfro' : (ROhandle.FRO.m).footprint ≤ (FVP.fvP D)ᶜ := hfro
  let L := Lens.pair C.c (Lens.pair C.queries (Lens.pair F.RO.m (Lens.pair G1.m
    (Lens.pair G1.mi G1.paths))))
  let I : ℤ × FMap (List block) block × FMap (List block) block × smap × smap ×
      FMap capacity (List block × block) →
      ℤ × FMap (List block) block × FMap (List block) block × smap × smap ×
      FMap capacity (List block × block) → Prop := fun x y =>
    x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧
      x.2.2.2.2.1 = y.2.2.2.2.1 ∧ x.2.2.2.2.2 = y.2.2.2.2.2
  have hI : ∀ g₁ g₂, I (L.get g₁) (L.get g₂) ↔ g34Inv g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (L.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [L, Footprint.lens_pair]
    exact sup_le hcc (sup_le hcq (sup_le hro (sup_le hm (sup_le hmi hpa))))
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (globInvF L (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    refine ⟨?_, (hI _ _).mpr ?_⟩
    · simp only [touched_set_of_le_compl hcc, touched_set_of_le_compl hcq,
        touched_set_of_le_compl hro, touched_set_of_le_compl hm, touched_set_of_le_compl hmi,
        touched_set_of_le_compl hmh, touched_set_of_le_compl hmhi, touched_set_of_le_compl hch,
        touched_set_of_le_compl hpa, touched_set_of_le_compl hfro']
      exact h
    · simp only [g34Inv]
      simp_reads
      trivial
  · stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_moduleF L D distExt hD.representable
      (FVP.fvP D) le_rfl hL I ?hc _ _ ?horacle) ?_
    case hc =>
      intro _ n
      cases n with
      | zero => exact inferInstanceAs (Countable (List block))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable state)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable state)
          | succ n => nomatch n
    case horacle =>
      intro _ n
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair]
        exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
          DFRestr_f_G34
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair]
          exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
            DPRestr_f_G34
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair]
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              DPRestr_fi_G34
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, -, -⟩
    simp_reads
    trivial

/-- `local equiv G4_Ideal : G4(F.LRO).distinguish ~ IdealIndif(IF, S, DRestr(D)).main :
={glob D} ==> ={res}`.  EC: `proc; inline *; wp; call (_: ={C.c, C.queries, F.RO.m} /\
G1.m{1} = S.m{2} /\ G1.mi{1} = S.mi{2} /\ G1.paths{1} = S.paths{2})`. -/
theorem G4_Ideal (hD : Module.ECModule D distExt) (_hDd : DRestrictions D) (_hG : Gext0Fresh D) :
    prhlProc
      (fun _ g₁ _ g₂ => (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (Module.app (G4 D) F.LRO).procedure (IdealIndif IF S (DRestr D)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hcc : (C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hcq : (C.queries).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hro : (F.RO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hsm : (S.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hsmi : (S.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hspa : (S.paths).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hm : (G1.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hmi : (G1.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  have hpa : (G1.paths).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hG.trans (Footprint.compl_antimono (by gcol_fp)))
  let L := Lens.pair C.c (Lens.pair C.queries (Lens.pair F.RO.m (Lens.pair G1.m
    (Lens.pair G1.mi (Lens.pair G1.paths (Lens.pair S.m (Lens.pair S.mi S.paths)))))))
  let I : ℤ × FMap (List block) block × FMap (List block) block × smap × smap ×
      FMap capacity (List block × block) × smap × smap × FMap capacity (List block × block) →
      ℤ × FMap (List block) block × FMap (List block) block × smap × smap ×
      FMap capacity (List block × block) × smap × smap × FMap capacity (List block × block) →
      Prop := fun x y =>
    x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.2.2.2.1 ∧
      x.2.2.2.2.1 = y.2.2.2.2.2.2.2.1 ∧ x.2.2.2.2.2.1 = y.2.2.2.2.2.2.2.2
  have hI : ∀ g₁ g₂, I (L.get g₁) (L.get g₂) ↔ g4Inv g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (L.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [L, Footprint.lens_pair]
    exact sup_le hcc (sup_le hcq (sup_le hro (sup_le hm (sup_le hmi (sup_le hpa
      (sup_le hsm (sup_le hsmi hspa)))))))
  unfold IdealIndif Indifferentiability.GIdeal
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (globInvF L (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    refine ⟨?_, (hI _ _).mpr ?_⟩
    · simp only [touched_set_of_le_compl hcc, touched_set_of_le_compl hcq,
        touched_set_of_le_compl hro, touched_set_of_le_compl hm, touched_set_of_le_compl hmi,
        touched_set_of_le_compl hpa, touched_set_of_le_compl hsm, touched_set_of_le_compl hsmi,
        touched_set_of_le_compl hspa]
      exact h
    · simp only [g4Inv]
      simp_reads
      trivial
  · stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_moduleF L D distExt hD.representable
      (FVP.fvP D) le_rfl hL I ?hc _ _ ?horacle) ?_
    case hc =>
      intro _ n
      cases n with
      | zero => exact inferInstanceAs (Countable (List block))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable state)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable state)
          | succ n => nomatch n
    case horacle =>
      intro _ n
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair]
        exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
          DFRestr_f_G4I
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair]
          exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
            DPRestr_f_G4I
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair]
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              DPRestr_fi_G4I
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, -, -⟩
    simp_reads
    trivial

/-- EC's `Real_Ideal`, with the axiom `D_ll`, and `Gext0Fresh` (exception E13). -/
theorem Real_Ideal (hD : Module.ECModule D distExt) (_hDd : DRestrictions D) (_hG : Gext0Fresh D)
    (G : Footprint VariableAssignment)
    (_hGd : G ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (F.RO.m).footprint ⊔ (Redo.prefixes).footprint ⊔ (FRO.m).footprint ⊔
      (ROhandle.RO.m).footprint)ᶜ)
    (GF : Footprint VariableAssignment) (hGF : GF.FinitelySupported) (hGGF : G ≤ GF.glob)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ Gᶜ →
      FVP.fvP P ≤ Gᶜ →
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
  -- `D` lies outside the variables of `Gext`'s section `EXT`
  have hA := (Footprint.le_compl_comm _ _).mp _hDd
  have hB := (Footprint.le_compl_comm _ _).mp _hG
  have hX : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (F.RO.m).footprint ⊔ (Redo.prefixes).footprint ⊔ (FRO.m).footprint ⊔
      (ROhandle.RO.m).footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr (le_trans ?_ (sup_le hA hB))
    fp_sub
  -- `G3 D` and `G4 D` are `F.RO` distinguishers outside `F.RO.m` and `F.FRO.m`
  have hfin : (FVP.fvP D ⊔ (Lens.pair C.c (Lens.pair C.queries (Lens.pair G1.m
      (Lens.pair G1.mi (Lens.pair G1.mh (Lens.pair G1.mhi (Lens.pair G1.chandle
        (Lens.pair G1.paths ROhandle.FRO.m)))))))).footprint).FinitelySupported :=
    hD.finitelySupported.sup (by
      simp only [Footprint.lens_pair]
      repeat (first | exact .varLens _ | refine .sup ?_ ?_))
  have hG3 := PROM.FullRO.RO_Distinguisher.ecModule (List block) block Unit Bool (G3 D)
    (hfin.mono (fvP_G3 D))
  have hG4 := PROM.FullRO.RO_Distinguisher.ecModule (List block) block Unit Bool (G4 D)
    (Footprint.FinitelySupported.mono (fvP_G4 D) (hD.finitelySupported.sup (by
      simp only [Footprint.lens_pair]
      repeat (first | exact .varLens _ | refine .sup ?_ ?_))))
  have hG3d : FVP.fvP (G3 D) ≤ ((F.RO.m).footprint ⊔ (F.FRO.m).footprint)ᶜ := by
    refine (fvP_G3 D).trans (sup_le (_hDd.trans (Footprint.compl_antimono (by fp_sub))) ?_)
    simp only [Footprint.lens_pair]
    fp_disjoint
  have hG4d : FVP.fvP (G4 D) ≤ ((F.RO.m).footprint ⊔ (F.FRO.m).footprint)ᶜ := by
    refine (fvP_G4 D).trans (sup_le (_hDd.trans (Footprint.compl_antimono (by fp_sub))) ?_)
    simp only [Footprint.lens_pair]
    fp_disjoint
  -- EC: `apply (ler_trans _ _ _ (Real_G2 D D_ll &m))`, then the chain of `byequiv`s
  have h := Real_G2 D hD hX G _hGd GF hGF hGGF D_ll m
  have e1 := Procedure.Pr_eq_of_prhlProc (G2_G3 D hD _hDd _hG) (E₁ := fun r _ => r = true)
    (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h]) (a₁ := ()) (a₂ := ()) (σ₁ := m)
    (σ₂ := m) rfl
  have e2 := Procedure.Pr_eq_of_prhlProc (PROM.FullRO.FullEager.RO_LRO_D (List block) block Unit
    Bool F.dout F.FRO.m (fun _ => BitWord.dunifin_ll) F.RO.m (G3 D) hG3 hG3d)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h.1])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) ⟨rfl, rfl, rfl⟩
  have e3 := Procedure.Pr_eq_of_prhlProc (G3_G4 D hD _hDd _hG) (E₁ := fun r _ => r = true)
    (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h]) (a₁ := ()) (a₂ := ()) (σ₁ := m)
    (σ₂ := m) rfl
  have e4 := Procedure.Pr_eq_of_prhlProc (PROM.FullRO.FullEager.RO_LRO_D (List block) block Unit
    Bool F.dout F.FRO.m (fun _ => BitWord.dunifin_ll) F.RO.m (G4 D) hG4 hG4d)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h.1])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) ⟨rfl, rfl, rfl⟩
  have e5 := Procedure.Pr_eq_of_prhlProc (G4_Ideal D hD _hDd _hG) (E₁ := fun r _ => r = true)
    (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h]) (a₁ := ()) (a₂ := ()) (σ₁ := m)
    (σ₂ := m) rfl
  rw [e1, ← e2, e3, e4, e5] at h
  exact h

end

end GaudisCrypt.SHA3.Gconcl
