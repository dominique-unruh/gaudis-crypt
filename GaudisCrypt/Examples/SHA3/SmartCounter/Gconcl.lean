import GaudisCrypt.Examples.SHA3.SmartCounter.Gext

/-!
# Conclusion of the squeezeless sponge proof (EasyCrypt `proof/smart_counter/Gconcl.ec`) —
EC-fidelity port

The equivalences `G2_G3`, `G3_G4`, `G4_Ideal` in EC's scripts, over the old port's declarations of
`IF`, `S`, `G3`, `G4` (section `FirstPort` below), as `SmartCounter/Gext.lean`.

Translation:
* EC's local `G3(RO)`, `G4(RO)` take `D` as a Lean parameter (the section's `D`): `G3(D, F.LRO)`
  for EC's `G3(F.LRO)`;
* `declare module D <: DISTINGUISHER {-C, -Perm, -F.RO, -F.FRO, -S, -Redo}` with the section's
  `local clone import Gext as Gext0`: the clone's modules are fresh for `D` in EC, here `D`'s
  restriction names them (`G1`, `FRO.m`).
-/

section FirstPort

/-!
## Declarations of the first port

Definitions and plain lemmas of the first port of this file (2026-10/11) that the proofs below
use; its program-logic proofs are gone.

The first port's translation notes (some mention declarations that went with its proofs):
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
    b <- call DRestr(D, G3.M(RO), G3.S(RO)).distinguish ();
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
    b <- call DRestr(D, G4.C(RO), G4.S(RO)).distinguish ();
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

end FirstPort

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

/-! Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* (GAP 1, fixed: EC's `sim` goes into calls of different concrete procedures, `G4.S(F.LRO).f`
  against `S(IF).f`: where ours makes no progress, it inlines the callees and closes what is left
  by `auto_close`.)
* (GAP 3, fixed as Gext's GAP 4: a procedure's parameter, `x` of `G3.S.f`, is a name of the
  conditions after `proc`.)
* (closed, was GAP 4) EC's `swap{1} [3..7] -2;swap{2} [4..8] -3` in `G2_G3`'s `S.f` moves `RRO`'s
  calls past the conditional calling `F.RO.get`; footprint disjointness does not apply (both
  read `x`).  EC's later `inline *` comes first here: what the block moves past is then
  deterministic code, which our `swap` commutes with it (`StmtSwap.discharge`), at EC's positions
  after the inlining; the rest of EC's script with its `seq`s at the inlined positions.
* (GAP 5, fixed: `sim` through two loops whose relation after them reads what they change: EC's
  equality set as the invariant.)
* (GAP 2, fixed: the one-sided `equiv_while{i}` keeps EC's frame, its exit in the precondition
  goal: EC's invariant `true`.)
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
    --     (EC's later `inline *` first, for `RRO`'s calls and `F.RO.get`: what the block moves
    --     past is then deterministic code, which our `swap` commutes with the block although both
    --     read `x`; EC's positions after the inlining)
    stmt_inline{1} 4; stmt_inline{1} 3; stmt_inline{1} 2; stmt_inline{1} 1; stmt_inline{1} 0
    stmt_inline{2} 4; stmt_inline{2} 3; stmt_inline{2} 2; stmt_inline{2} 1; stmt_inline{2} 0
    stmt_swap{1} [3..8] -2; stmt_swap{2} [4..9] -3
    -- EC: seq 5 5:(={hx2,t,x,FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c,
    --              C.queries} /\ (t = in_dom_with FRO.m (oget G1.mh.[(x.`1, hx2)]).`2 Unknown){1});
    --       1:by inline *;auto.
    --     (`RRO.in_dom` inlined: two statements)
    equiv_seq 6 6 : (={hx2, t, x, FRO.m, F.RO.m, G1.m, G1.mi,
        G1.mh, G1.mhi, G1.chandle, G1.paths, C.c, C.queries} ∧
      §t{1} = decide (FMap.in_dom_with §FRO.m{1}
        (oget (FMap.get §G1.mh{1} ((§x{1}).1, §hx2{1}))).2 Unknown))
    · stmt_inline*; equiv_auto; auto_close
    -- EC: seq 3 4:(={y,x,FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c,C.queries});
    --       2:by sim.
    equiv_seq 3 4 : (={y, x, FRO.m, F.RO.m, G1.m, G1.mi, G1.mh,
      G1.mhi, G1.chandle, G1.paths, C.c, C.queries})
    on_goals 2 => sim
    -- EC: if=>//.
    stmt_if
    · auto_close
    -- EC: + seq 2 2:(={y1,hx2,t,x,FRO.m,…} /\ (t = in_dom_with FRO.m (oget G1.mh.[(x.`1, hx2)]).`2
    --                Unknown){1}).
    --       + by inline *;auto=> /> ? _;rewrite Block.DWord.bdistr_ll.
    --     (`F.RO.get` inlined: five statements)
    · equiv_seq 5 5 : (={y1, hx2, t, x, FRO.m, F.RO.m, G1.m,
          G1.mi, G1.mh, G1.mhi, G1.chandle, G1.paths, C.c, C.queries} ∧
        §t{1} = decide (FMap.in_dom_with §FRO.m{1}
          (oget (FMap.get §G1.mh{1} ((§x{1}).1, §hx2{1}))).2
          Unknown))
      · stmt_inline*; equiv_auto
      -- EC: case (((x.`1, hx2) \in G1.mh /\ t){1});
      --       [rcondt{1} 3;2:rcondt{2} 3| rcondf{1} 3;2:rcondf{2} 3];
      --       1,2,4,5:(by move=>?;conseq (_:true);auto);2:by sim.
      equiv_case (FMap.dom §G1.mh{1} ((§x{1}).1, §hx2{1}) ∧
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
    -- EC: case (((x.`1, hx2) \in G1.mh /\ t){1});
    --       [rcondt{1} 4;2:rcondt{2} 4| rcondf{1} 4;2:rcondf{2} 4];
    --       1,2,4,5:(by move=>?;conseq (_:true);auto);2:by sim.
    · equiv_case (FMap.dom §G1.mh{1} ((§x{1}).1, §hx2{1}) ∧
        §t{1} = true)
      · stmt_rcondt{1} 4
        · hoare_auto
        stmt_rcondt{2} 4
        · hoare_auto
        -- EC: inline *;rcondt{1} 7;1:by auto=>/>.
        stmt_inline*; stmt_rcondt{1} 7
        · hoare_auto; simp only [FMap.in_dom_with, PROM.is_, oget] at *; auto_close
        -- EC: by wp;rnd;auto;rnd{1};auto => /> *; rewrite !get_setE.
        --     (our `auto` takes EC's `rnd{1}` as well)
        stmt_wp; equiv_rnd; equiv_auto; auto_progress
        all_goals simp only [FMap.get_set_sameE, oget_some]
      · stmt_rcondf{1} 4
        · hoare_auto
        stmt_rcondf{2} 4
        · hoare_auto
        sim
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
    equiv_seq 6 6 : (={y1, hx2, t, x, FRO.m, F.RO.m, G1.m, G1.mi,
        G1.mh, G1.mhi, G1.chandle, G1.paths, C.c, C.queries} ∧
      §t{1} = decide (FMap.in_dom_with §FRO.m{1}
        (oget (FMap.get §G1.mhi{1} ((§x{1}).1, §hx2{1}))).2 Unknown))
    · stmt_inline*; equiv_auto; auto_close
    -- EC: case (((x.`1, hx2) \in G1.mhi /\ t){1});
    --       [rcondt{1} 3;2:rcondt{2} 3| rcondf{1} 3;2:rcondf{2} 3];
    --       1,2,4,5:(by move=>?;conseq (_:true);auto);2:by sim.
    equiv_case (FMap.dom §G1.mhi{1} ((§x{1}).1, §hx2{1}) ∧
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
    equiv_seq 3 3 : (={x, y1, y2, y, G1.m, G1.mi, G1.paths,
      F.RO.m, C.c, C.queries})
    · sim
    -- EC: sim;seq 5 0: (={x,y1,y2,y,G1.m,G1.mi,G1.paths,F.RO.m,C.c,C.queries});
    --       1:by inline *;auto.
    sim
    equiv_seq 5 0 : (={x, y1, y2, y, G1.m, G1.mi, G1.paths, F.RO.m,
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
    equiv_seq 5 0 : (={x, G1.m, G1.mi, G1.paths, F.RO.m, C.c,
      C.queries})
    · stmt_inline*; equiv_auto
    -- EC: seq 3 3: (={x,y1,y2,y,G1.m,G1.mi,G1.paths,F.RO.m,C.c,C.queries});1:by sim.
    equiv_seq 3 3 : (={x, y1, y2, y, G1.m, G1.mi, G1.paths,
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
  · equiv_proc; sim
  · equiv_proc; sim
  -- EC: + proc;sp;if=>//;auto;if=>//;auto.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    on_goals -1 => equiv_auto
    stmt_sp; stmt_if
    · auto_close
    on_goals -1 => equiv_auto
    -- EC: call (_: ={F.RO.m});2:by auto.
    stmt_wp; equiv_call (_ : ={F.RO.m})
    on_goals 2 => equiv_auto
    -- EC: inline F.LRO.get F.FRO.sample;wp 7 2;sim.
    equiv_proc; stmt_inline*; stmt_wp 7 2; sim
    -- EC: by while{1} (true) (size p - i){1};auto;1:inline*;auto=>/#.
    equiv_while{1} (True) ((size §p{1} - §i{1}).toNat)
    · while_ll_phoare
      intro σ₂
      phoare_auto
    · intro σ₂ k
      hoare_auto
    equiv_auto
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
  -Pilot.ConcreteF.Switching.PRPi.PRPi} with glob R

-- EC's `declare axiom D_ll` (`glob D` as the region `R`, exception E14)
variable (D_ll : ∀ (F <: DFUNCTIONALITY {-R}), ∀ (P <: DPRIMITIVE {-R}),
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
    byequiv (PROM.FullRO.FullEager.RO_LRO_D (List block) block F.dout F.FRO.m
      (fun _ => BitWord.dunifin_ll) F.RO.m (G3 D) (by ec_module) (by fp_disjoint))
  -- EC: apply (eq_trans _ Pr[G4(F.RO ).distinguish() @ &m : res]);1:by byequiv G3_G4.
  refine Eq.trans (b := Pr[ G4(D, F.RO.asRO).distinguish (()) @ &m : §res ]) ?_ ?_
  · byequiv (G3_G4 D)
  -- EC: apply (eq_trans _ Pr[G4(F.LRO).distinguish() @ &m : res]).
  --     + byequiv (F.FullEager.RO_LRO_D G4 _)=> //.
  --       by move=> _; exact/Block.DBlock.dunifin_ll.
  refine Eq.trans (b := Pr[ G4(D, F.LRO).distinguish (()) @ &m : §res ]) ?_ ?_
  · byequiv (PROM.FullRO.FullEager.RO_LRO_D (List block) block F.dout F.FRO.m
      (fun _ => BitWord.dunifin_ll) F.RO.m (G4 D) (by ec_module) (by fp_disjoint))
  -- EC: by byequiv G4_Ideal.
  byequiv (G4_Ideal D)

end REAL

end GaudisCrypt.SHA3.Pilot.Gconcl
