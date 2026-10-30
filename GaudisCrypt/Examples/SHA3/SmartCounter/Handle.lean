import GaudisCrypt.Examples.SHA3.SmartCounter.ConcreteF

/-!
# The handle-based game `G1` and its invariant (EasyCrypt `proof/smart_counter/Handle.eca`)

`G1` simulates the permutation with handles standing for capacities; `INV_CF_G1` relates it to
the concrete game `CF` of `ConcreteF`.  The headline is `Real_G1`: the real game is bounded by
`G1` plus the switching bound and the probabilities of the two bad events `G1.bcol`, `G1.bext`.

Translation notes (see `notes/SHA3/README.md`):
* `clone export PROM.FullRO as ROhandle with type in_t <- handle, type out_t <- capacity …` is the
  namespace `ROhandle`; its exported `FRO.m` is the alias `FRO.m` here.
* `clone export ConcreteF as ConcreteF1` clones a theory without parameters: it is `ConcreteF`
  itself, opened.
* `G1`'s inner modules `M`, `S` do not depend on `D`: they are the modules `G1.M`, `G1.S`.
  `G1 D` is the game, with `D` a Lean parameter.
* The equivalences relate procedures of modules: they are `prhlProc` statements, with the
  section's `declare module D` and its restrictions as hypotheses.
-/

namespace GaudisCrypt.SHA3.Handle

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.ConcreteF

export GaudisCrypt.SHA3.SLCommon (state PRIMITIVE)

variable [SLCommon.Params]

-- `clone export PROM.FullRO as ROhandle with type in_t <- handle, type out_t <- capacity,
-- op dout _ <- cdistr, type d_in_t <- unit, type d_out_t <- bool`
namespace ROhandle
noncomputable abbrev dout : handle → SubProbability capacity := fun _ => cdistr
noncomputable abbrev RO := PROM.FullRO.RO handle capacity dout
noncomputable abbrev FRO := PROM.FullRO.FRO handle capacity dout
end ROhandle

/-- The exported `FRO.m` of the `ROhandle` clone. -/
noncomputable abbrev FRO.m := PROM.FullRO.FRO.m (in_t := handle) (out_t := capacity)

/-! ## The game `G1` -/

/-- EC's `G1.m`. -/
global_var G1.m : smap
/-- EC's `G1.mi`. -/
global_var G1.mi : smap
/-- EC's `G1.mh`. -/
global_var G1.mh : hsmap
/-- EC's `G1.mhi`. -/
global_var G1.mhi : hsmap
/-- EC's `G1.chandle`. -/
global_var G1.chandle : ℤ
/-- EC's `G1.paths`. -/
global_var G1.paths : FMap capacity (List block × block)
/-- EC's `G1.bext`. -/
global_var G1.bext : Bool
/-- EC's `G1.bcol`. -/
global_var G1.bcol : Bool

-- EC's `G1(D).M`
module G1.M : DFUNCTIONALITY {
  proc f (p : List block) : block {
    var sa : block, sa' : block, sc : capacity, h : handle, i : ℤ, counter : ℤ;
    h <- 0;
    i <- 0;
    counter <- 0;
    sa <- b0;
    sc <- c0;
    while ($i < size $p) {
      if (decide (FMap.dom ($G1.mh : hsmap) ($sa +^ nth default $p $i, $h))) {
        sa, h <- oget (FMap.get ($G1.mh : hsmap) ($sa +^ nth default $p $i, $h));
      } else {
        if (decide ($counter < size $p - «prefix» $p (get_max_prefix $p
            (elems (FMap.fdom ($C.queries : FMap (List block) block)))))) {
          sc <$ cdistr;
          G1.bcol <- $G1.bcol || decide (hinv $FRO.m $sc ≠ none);
          sa' <- call (PROM.FullRO.ROmap.get (List block) block F.RO) (take ($i + 1) $p);
          sa <- $sa +^ nth default $p $i;
          G1.mh <- FMap.set $G1.mh ($sa, $h) ($sa', $G1.chandle);
          G1.mhi <- FMap.set $G1.mhi ($sa', $G1.chandle) ($sa, $h);
          sa, h <- ($sa', $G1.chandle);
          FRO.m <- FMap.set $FRO.m $G1.chandle ($sc, Unknown);
          G1.chandle <- $G1.chandle + 1;
          counter <- $counter + 1;
        }
      }
      i <- $i + 1;
    }
    sa <- call (PROM.FullRO.ROmap.get (List block) block F.RO) ($p);
    return $sa
  };
}

-- EC's `G1(D).S`
module G1.S : DPRIMITIVE {
  proc f (x : state) : state {
    var p : List block, v : block, y : state, y1 : block, y2 : capacity, hy2 : handle,
      hx2 : handle;
    if (!(decide (FMap.dom ($G1.m : smap) $x))) {
      if (decide (FMap.dom ($G1.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($G1.paths : FMap capacity (List block × block)) ($x).2);
        y1 <- call (PROM.FullRO.ROmap.get (List block) block F.RO) (rcons $p ($v +^ ($x).1));
        y2 <$ cdistr;
      } else {
        y1 <$ bdistr;
        y2 <$ cdistr;
      }
      y <- ($y1, $y2);
      G1.bext <- $G1.bext || decide (FMap.rng ($FRO.m : FMap handle (capacity × flag))
        (($x).2, Unknown));
      if (!(decide (FMap.rng ($FRO.m : FMap handle (capacity × flag)) (($x).2, Known)))) {
        FRO.m <- FMap.set $FRO.m $G1.chandle (($x).2, Known);
        G1.chandle <- $G1.chandle + 1;
      }
      hx2 <- oget (hinvK $FRO.m ($x).2);
      if (decide (FMap.dom ($G1.mh : hsmap) (($x).1, $hx2) ∧
          FMap.in_dom_with ($FRO.m : FMap handle (capacity × flag))
            (oget (FMap.get ($G1.mh : hsmap) (($x).1, $hx2))).2 Unknown)) {
        hy2 <- (oget (FMap.get ($G1.mh : hsmap) (($x).1, $hx2))).2;
        y <- (($y).1, (oget (FMap.get ($FRO.m : FMap handle (capacity × flag)) $hy2)).1);
        FRO.m <- FMap.set $FRO.m $hy2 (($y).2, Known);
        G1.m <- FMap.set $G1.m $x $y;
        G1.mi <- FMap.set $G1.mi $y $x;
      } else {
        G1.bcol <- $G1.bcol || decide (hinv $FRO.m ($y).2 ≠ none);
        hy2 <- $G1.chandle;
        G1.chandle <- $G1.chandle + 1;
        FRO.m <- FMap.set $FRO.m $hy2 (($y).2, Known);
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
    var y : state, y1 : block, y2 : capacity, hx2 : handle, hy2 : handle;
    if (!(decide (FMap.dom ($G1.mi : smap) $x))) {
      G1.bext <- $G1.bext || decide (FMap.rng ($FRO.m : FMap handle (capacity × flag))
        (($x).2, Unknown));
      if (!(decide (FMap.rng ($FRO.m : FMap handle (capacity × flag)) (($x).2, Known)))) {
        FRO.m <- FMap.set $FRO.m $G1.chandle (($x).2, Known);
        G1.chandle <- $G1.chandle + 1;
      }
      hx2 <- oget (hinvK $FRO.m ($x).2);
      y1 <$ bdistr;
      y2 <$ cdistr;
      y <- ($y1, $y2);
      if (decide (FMap.dom ($G1.mhi : hsmap) (($x).1, $hx2) ∧
          FMap.in_dom_with ($FRO.m : FMap handle (capacity × flag))
            (oget (FMap.get ($G1.mhi : hsmap) (($x).1, $hx2))).2 Unknown)) {
        y1, hy2 <- oget (FMap.get ($G1.mhi : hsmap) (($x).1, $hx2));
        y <- (($y).1, (oget (FMap.get ($FRO.m : FMap handle (capacity × flag)) $hy2)).1);
        FRO.m <- FMap.set $FRO.m $hy2 (($y).2, Known);
        G1.mi <- FMap.set $G1.mi $x $y;
        G1.m <- FMap.set $G1.m $y $x;
      } else {
        G1.bcol <- $G1.bcol || decide (hinv $FRO.m ($y).2 ≠ none);
        hy2 <- $G1.chandle;
        G1.chandle <- $G1.chandle + 1;
        FRO.m <- FMap.set $FRO.m $hy2 (($y).2, Known);
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

-- EC's `G1(D).main`, with `D` a Lean parameter (on purpose: `G1 D` is the game)
set_option linter.gaudisCrypt.using false in
module G1 (D : DISTINGUISHER) {
  proc main () : Bool {
    var b : Bool;
    F.RO.m <- (FMap.empty : FMap (List block) block);
    G1.m <- (FMap.empty : smap);
    G1.mi <- (FMap.empty : smap);
    G1.mh <- (FMap.empty : hsmap);
    G1.mhi <- (FMap.empty : hsmap);
    G1.bext <- false;
    G1.bcol <- false;
    C.queries <- FMap.set (FMap.empty : FMap (List block) block) [] b0;
    -- the empty path is initially known by the adversary to lead to capacity 0^c
    FRO.m <- FMap.set (FMap.empty : FMap handle (capacity × flag)) 0 (c0, Known);
    G1.paths <- FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0);
    G1.chandle <- 1;
    b <- call (Module.app D (Module.pair G1.M G1.S)) ();
    return $b
  };
}

/-! ## The invariant

The state of `CF` contains the map `PF.m` (the primitive's map) and `Redo.prefixes` (all the prefix
computations of the sponge construction).  The state of `G1` contains the map `hs` from handles to
flagged capacities, `G1.m` (the public view of `PF.m`), `G1.mh` (`PF.m` with handle-based
indirection), the functionality `ro`, and `pi`, the known path to a capacity if it exists. -/

/-- Relational: map, handle-map and handles are compatible. -/
inductive m_mh (hs : handles) (m : smap) (mh : hsmap) : Prop where
  | INV_m_mh :
      (∀ xa xc ya yc, FMap.get m (xa, xc) = some (ya, yc) →
        ∃ hx fx hy fy, FMap.get hs hx = some (xc, fx) ∧ FMap.get hs hy = some (yc, fy) ∧
          FMap.get mh (xa, hx) = some (ya, hy)) →
      (∀ xa hx ya hy, FMap.get mh (xa, hx) = some (ya, hy) →
        ∃ xc fx yc fy, FMap.get hs hx = some (xc, fx) ∧ FMap.get hs hy = some (yc, fy) ∧
          FMap.get m (xa, xc) = some (ya, yc)) →
      m_mh hs m mh

/-- Well-formedness: map and prefixes are compatible. -/
inductive m_p (m : smap) (p : FMap (List block) state) (q : FMap (List block) block) : Prop where
  | INV_m_p :
      FMap.get p [] = some (b0, c0) →
      FMap.get q [] = some b0 →
      (∀ l : List block, FMap.dom p l → ∀ i, 0 ≤ i ∧ i < size l →
        ∃ sa sc, FMap.get p (take i l) = some (sa, sc) ∧
          FMap.get m (sa +^ nth default l i, sc) = FMap.get p (take (i + 1) l)) →
      (∀ l : List block, FMap.dom q l → ∃ c, FMap.get p l = some (oget (FMap.get q l), c)) →
      (∀ l : List block, FMap.dom p l → ∃ l2 : List block, FMap.dom q (l ++ l2)) →
      m_p m p q

/-- Relational: prefixes and the random oracle are compatible. -/
inductive ro_p (ro : FMap (List block) block) (p : FMap (List block) state) : Prop where
  | INV_ro_p : ro = FMap.map («[+]» (fun a : state => a.1)) p → ro_p ro p

/-- Well-formedness: handles, map, handle-map and random oracle are compatible. -/
inductive mh_spec (hs : handles) (Gm : smap) (mh : hsmap) (ro : FMap (List block) block) :
    Prop where
  | INV_mh :
      (∀ xa hx ya hy, FMap.get mh (xa, hx) = some (ya, hy) →
        ∃ xc fx yc fy, FMap.get hs hx = some (xc, fx) ∧ FMap.get hs hy = some (yc, fy) ∧
          if fy = Known then FMap.get Gm (xa, xc) = some (ya, yc) ∧ fx = Known
          else ∃ p v, FMap.get ro (rcons p (v +^ xa)) = some ya ∧
            build_hpath mh p = some (v, hx)) →
      (∀ p bn b, FMap.get ro (rcons p bn) = some b ↔
        ∃ v hx hy, build_hpath mh p = some (v, hx) ∧ FMap.get mh (v +^ bn, hx) = some (b, hy)) →
      (∀ p v p' v' hx, build_hpath mh p = some (v, hx) → build_hpath mh p' = some (v', hx) →
        p = p' ∧ v = v') →
      mh_spec hs Gm mh ro

/-- Well-formedness: handles, handle-map and paths are compatible. -/
inductive pi_spec (hs : handles) (mh : hsmap) (pi : FMap capacity (List block × block)) : Prop where
  | INV_pi :
      (∀ c p v, FMap.get pi c = some (p, v) ↔
        ∃ h, build_hpath mh p = some (v, h) ∧ FMap.get hs h = some (c, Known)) →
      pi_spec hs mh pi

/-- Well-formedness: handles are well formed. -/
inductive hs_spec (hs : handles) (ch : handle) : Prop where
  | INV_hs :
      huniq hs → FMap.get hs 0 = some (c0, Known) → (∀ cf h, FMap.get hs h = some cf → h < ch) →
      hs_spec hs ch

inductive inv_spec {α β : Type} [DecidableEq α] [DecidableEq β] (m : FMap α β) (mi : FMap β α) :
    Prop where
  | INV_inv : (∀ x y, FMap.get m x = some y ↔ FMap.get mi y = some x) → inv_spec m mi

inductive INV_CF_G1 (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (p : FMap (List block) state) (q : FMap (List block) block) : Prop where
  | HCF_G1 :
      hs_spec hs ch → inv_spec Gm Gmi → inv_spec mh mhi → m_mh hs Pm mh → m_mh hs Pmi mhi →
      incl Gm Pm → incl Gmi Pmi → mh_spec hs Gm mh ro → pi_spec hs mh pi → m_p Pm p q →
      INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi p q

/-! ## Structural projections -/

theorem m_mh_of_INV (ch : handle) (mi1 m2 mi2 : smap) (mhi2 : hsmap) (ro : FMap (List block) block)
    (pi : FMap capacity (List block × block)) (hs : handles) (m1 : smap) (mh2 : hsmap)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → m_mh hs m1 mh2 := by
  sorry

theorem mi_mhi_of_INV (ch : handle) (m1 m2 mi2 : smap) (mh2 : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (hs : handles)
    (mi1 : smap) (mhi2 : hsmap) (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → m_mh hs mi1 mhi2 := by
  sorry

theorem incl_of_INV (hs : handles) (ch : handle) (mi1 mi2 : smap) (mh2 mhi2 : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (m1 m2 : smap)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → incl m2 m1 := by
  sorry

theorem incli_of_INV (hs : handles) (ch : handle) (m1 m2 : smap) (mh2 mhi2 : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (mi1 mi2 : smap)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → incl mi2 mi1 := by
  sorry

theorem mh_of_INV (ch : handle) (m1 mi1 mi2 : smap) (mhi2 : hsmap)
    (pi : FMap capacity (List block × block)) (hs : handles) (m2 : smap) (mh2 : hsmap)
    (ro : FMap (List block) block) (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → mh_spec hs m2 mh2 ro := by
  sorry

theorem pi_of_INV (ch : handle) (m1 m2 mi1 mi2 : smap) (mhi2 : hsmap)
    (ro : FMap (List block) block) (hs : handles) (mh2 : hsmap)
    (pi : FMap capacity (List block × block)) (p : FMap (List block) state)
    (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → pi_spec hs mh2 pi := by
  sorry

theorem hs_of_INV (m1 m2 mi1 mi2 : smap) (mh2 mhi2 : hsmap) (ro : FMap (List block) block)
    (pi : FMap capacity (List block × block)) (hs : handles) (ch : handle)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → hs_spec hs ch := by
  sorry

theorem inv_of_INV (hs : handles) (ch : handle) (m1 mi1 m2 mi2 : smap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (mh2 mhi2 : hsmap)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → inv_spec mh2 mhi2 := by
  sorry

theorem invG_of_INV (hs : handles) (ch : handle) (m1 mi1 : smap) (mh2 mhi2 : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (m2 mi2 : smap)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → inv_spec m2 mi2 := by
  sorry

theorem m_p_of_INV (hs : handles) (ch : handle) (m1 mi1 : smap) (mh2 mhi2 : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (m2 mi2 : smap)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → m_p m1 p q := by
  sorry

theorem all_prefixes_of_m_p (m1 : smap) (p : FMap (List block) state)
    (q : FMap (List block) block) : m_p m1 p q → all_prefixes p := by
  sorry

theorem all_prefixes_of_INV (hs : handles) (ch : handle) (m1 mi1 : smap) (mh2 mhi2 : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (m2 mi2 : smap)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → all_prefixes p := by
  sorry

/-! ## Handles -/

theorem ch_gt0 (hs : handles) (ch : handle) : hs_spec hs ch → 0 < ch := by
  sorry

theorem ch_neq0 (hs : handles) (ch : handle) : hs_spec hs ch → 0 ≠ ch := by
  sorry

theorem ch_notdomE_hs (hs : handles) (ch : handle) : hs_spec hs ch → FMap.get hs ch = none := by
  sorry

theorem Sch_notdomE_hs (hs : handles) (ch : handle) :
    hs_spec hs ch → FMap.get hs (ch + 1) = none := by
  sorry

theorem ch_notdomE2_mh (hs : handles) (m : smap) (mh : hsmap) (xa : block) (ch : handle) :
    m_mh hs m mh → hs_spec hs ch → FMap.get mh (xa, ch) = none := by
  sorry

theorem Sch_notdomE2_mh (hs : handles) (m : smap) (mh : hsmap) (xa : block) (ch : handle) :
    m_mh hs m mh → hs_spec hs ch → FMap.get mh (xa, ch + 1) = none := by
  sorry

theorem dom_hs_neq_ch (hs : handles) (ch hx : handle) (xc : capacity) (fx : flag) :
    hs_spec hs ch → FMap.get hs hx = some (xc, fx) → hx ≠ ch := by
  sorry

theorem dom_hs_neq_Sch (hs : handles) (ch hx : handle) (xc : capacity) (fx : flag) :
    hs_spec hs ch → FMap.get hs hx = some (xc, fx) → hx ≠ ch + 1 := by
  sorry

theorem notin_m_notin_mh (hs : handles) (m : smap) (mh : hsmap) (xa : block) (xc : capacity)
    (hx : handle) (fx : flag) :
    m_mh hs m mh → FMap.get m (xa, xc) = none → FMap.get hs hx = some (xc, fx) →
    FMap.get mh (xa, hx) = none := by
  sorry

theorem notin_m_notin_Gm {α β : Type} [DecidableEq α] (m Gm : FMap α β) (x : α) :
    incl Gm m → FMap.get m x = none → FMap.get Gm x = none := by
  sorry

theorem notin_hs_notdomE2_mh (hs : handles) (m : smap) (mh : hsmap) (xa : block) (hx : handle) :
    m_mh hs m mh → FMap.get hs hx = none → FMap.get mh (xa, hx) = none := by
  sorry

theorem m_mh_addh (hs : handles) (ch : handle) (m : smap) (mh : hsmap) (xc : capacity)
    (fx : flag) : hs_spec hs ch → m_mh hs m mh → m_mh (FMap.set hs ch (xc, fx)) m mh := by
  sorry

theorem m_mh_updh (fy0 : flag) (hs : handles) (m : smap) (mh : hsmap) (yc : capacity)
    (hy : handle) (fy : flag) :
    m_mh hs m mh → FMap.get hs hy = some (yc, fy0) → m_mh (FMap.set hs hy (yc, fy)) m mh := by
  sorry

theorem m_mh_addh_addm (hs : handles) (Pm : smap) (mh : hsmap) (hx : handle) (xa : block)
    (xc : capacity) (hy : handle) (ya : block) (yc : capacity) (f f' : flag) :
    m_mh hs Pm mh → huniq hs → FMap.get hs hx = some (xc, f) → FMap.get hs hy = none →
    m_mh (FMap.set hs hy (yc, f')) (FMap.set Pm (xa, xc) (ya, yc))
      (FMap.set mh (xa, hx) (ya, hy)) := by
  sorry

theorem mi_mhi_addh_addmi (hs : handles) (mi : smap) (mhi : hsmap) (hx : handle) (xa : block)
    (xc : capacity) (hy : handle) (ya : block) (yc : capacity) (fx fy : flag) :
    m_mh hs mi mhi → (∀ f h, FMap.get hs h ≠ some (yc, f)) → FMap.get hs hx = some (xc, fx) →
    FMap.get hs hy = none →
    m_mh (FMap.set hs hy (yc, fy)) (FMap.set mi (ya, yc) (xa, xc))
      (FMap.set mhi (ya, hy) (xa, hx)) := by
  sorry

theorem inv_mh_inv_Pm (hs : handles) (Pm Pmi : smap) (mh mhi : hsmap) :
    m_mh hs Pm mh → m_mh hs Pmi mhi → inv_spec mh mhi → inv_spec Pm Pmi := by
  sorry

theorem inv_incl_none {α β : Type} [DecidableEq α] [DecidableEq β] (Pm : FMap α β)
    (Pmi : FMap β α) (Gm : FMap α β) (x : α) (Gmi : FMap β α) (y : β) :
    inv_spec Pm Pmi → inv_spec Gm Gmi → incl Gm Pm → incl Gmi Pmi → FMap.get Pm x = some y →
    (FMap.get Gm x = none ↔ FMap.get Gmi y = none) := by
  sorry

theorem huniq_addh (hs : handles) (h : handle) (c : capacity) (f : flag) :
    huniq hs → (∀ f' h', FMap.get hs h' ≠ some (c, f')) → huniq (FMap.set hs h (c, f)) := by
  sorry

theorem hs_addh (hs : handles) (ch : handle) (xc : capacity) (fx : flag) :
    hs_spec hs ch → (∀ f h, FMap.get hs h ≠ some (xc, f)) →
    hs_spec (FMap.set hs ch (xc, fx)) (ch + 1) := by
  sorry

theorem hs_updh (hs : handles) (ch : handle) (fx : flag) (hx : handle) (xc : capacity)
    (fx' : flag) :
    hs_spec hs ch → 0 ≠ hx → FMap.get hs hx = some (xc, fx) →
    hs_spec (FMap.set hs hx (xc, fx')) ch := by
  sorry

theorem mh_addh (hs : handles) (ch : handle) (Gm : smap) (mh : hsmap)
    (ro : FMap (List block) block) (xc : capacity) (fx : flag) :
    hs_spec hs ch → mh_spec hs Gm mh ro → mh_spec (FMap.set hs ch (xc, fx)) Gm mh ro := by
  sorry

theorem inv_addm {α β : Type} [DecidableEq α] [DecidableEq β] (m : FMap α β) (mi : FMap β α)
    (x : α) (y : β) :
    inv_spec m mi → FMap.get m x = none → FMap.get mi y = none →
    inv_spec (FMap.set m x y) (FMap.set mi y x) := by
  sorry

theorem incl_addm {α β : Type} [DecidableEq α] (m m' : FMap α β) (x : α) (y : β) :
    incl m m' → incl (FMap.set m x y) (FMap.set m' x y) := by
  sorry

noncomputable def getflag (hs : handles) (xc : capacity) : Option flag :=
  ((hinv hs xc).bind (FMap.get hs)).map Prod.snd

theorem getflagP_none (hs : handles) (xc : capacity) :
    getflag hs xc = none ↔ ∀ f h, FMap.get hs h ≠ some (xc, f) := by
  sorry

theorem getflagP_some (hs : handles) (xc : capacity) (f : flag) :
    huniq hs → (getflag hs xc = some f ↔ FMap.rng hs (xc, f)) := by
  sorry

/-! ## Handle paths -/

theorem build_hpath_prefix (mh : hsmap) (p : List block) (b v : block) (h : handle) :
    build_hpath mh (rcons p b) = some (v, h) ↔
      ∃ v' h', build_hpath mh p = some (v', h') ∧ FMap.get mh (v' +^ b, h') = some (v, h) := by
  sorry

theorem build_hpath_up (mh : hsmap) (xa : block) (hx : handle) (ya : block) (hy : handle)
    (p : List block) (za : block) (hz : handle) :
    build_hpath mh p = some (za, hz) → FMap.get mh (xa, hx) = none →
    build_hpath (FMap.set mh (xa, hx) (ya, hy)) p = some (za, hz) := by
  sorry

theorem build_hpath_down (mh : hsmap) (xa : block) (hx : handle) (ya : block) (hy : handle)
    (p : List block) (v : block) (h : handle) :
    (∀ p v, build_hpath mh p ≠ some (v, hx)) →
    build_hpath (FMap.set mh (xa, hx) (ya, hy)) p = some (v, h) →
    build_hpath mh p = some (v, h) := by
  sorry

theorem known_path_uniq (hs : handles) (mh : hsmap) (pi : FMap capacity (List block × block))
    (xc : capacity) (hx : handle) (p : List block) (xa : block) (p' : List block) (xa' : block) :
    pi_spec hs mh pi → FMap.get hs hx = some (xc, Known) → build_hpath mh p = some (xa, hx) →
    build_hpath mh p' = some (xa', hx) → p = p' ∧ xa = xa' := by
  sorry

theorem path_split (hs : handles) (ch : handle) (m : smap) (mh : hsmap) (xc : capacity)
    (hx : handle) (p : List block) (xa : block) :
    hs_spec hs ch → m_mh hs m mh → FMap.get hs hx = some (xc, Unknown) →
    build_hpath mh p = some (xa, hx) →
    ∃ pk ya yc hy b za zc hz pu,
      p = rcons pk b ++ pu ∧ build_hpath mh pk = some (ya, hy) ∧
      FMap.get hs hy = some (yc, Known) ∧ FMap.get mh (ya +^ b, hy) = some (za, hz) ∧
      FMap.get hs hz = some (zc, Unknown) := by
  sorry

/-! ## Preservation of the invariant -/

theorem lemma1 (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (x1 : block)
    (x2 : capacity) (y1 : block) (y2 : capacity) (prefixes : FMap (List block) state)
    (queries : FMap (List block) block) :
    INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries → x2 ≠ y2 →
    FMap.get Pm (x1, x2) = none → FMap.get Gm (x1, x2) = none →
    (∀ f h, FMap.get hs h ≠ some (x2, f)) → (∀ f h, FMap.get hs h ≠ some (y2, f)) →
    INV_CF_G1 (FMap.set (FMap.set hs ch (x2, Known)) (ch + 1) (y2, Known)) (ch + 2)
      (FMap.set Pm (x1, x2) (y1, y2)) (FMap.set Pmi (y1, y2) (x1, x2))
      (FMap.set Gm (x1, x2) (y1, y2)) (FMap.set Gmi (y1, y2) (x1, x2))
      (FMap.set mh (x1, ch) (y1, ch + 1)) (FMap.set mhi (y1, ch + 1) (x1, ch))
      ro pi prefixes queries := by
  sorry

theorem lemma1' (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (x1 : block)
    (x2 : capacity) (y1 : block) (y2 : capacity) :
    INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries → ¬ FMap.dom Pm (y1, y2) →
    x2 ≠ y2 → FMap.get Pmi (x1, x2) = none → FMap.get Gmi (x1, x2) = none →
    (∀ f h, FMap.get hs h ≠ some (x2, f)) → (∀ f h, FMap.get hs h ≠ some (y2, f)) →
    INV_CF_G1 (FMap.set (FMap.set hs ch (x2, Known)) (ch + 1) (y2, Known)) (ch + 2)
      (FMap.set Pm (y1, y2) (x1, x2)) (FMap.set Pmi (x1, x2) (y1, y2))
      (FMap.set Gm (y1, y2) (x1, x2)) (FMap.set Gmi (x1, x2) (y1, y2))
      (FMap.set mh (y1, ch + 1) (x1, ch)) (FMap.set mhi (x1, ch) (y1, ch + 1))
      ro pi prefixes queries := by
  sorry

theorem lemma2 (hs : handles) (ch : handle) (PFm PFmi G1m G1mi : smap) (G1mh G1mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (x1 : block)
    (x2 : capacity) (y1 : block) (y2 : capacity) (hx : handle) :
    INV_CF_G1 hs ch PFm PFmi G1m G1mi G1mh G1mhi ro pi prefixes queries →
    FMap.get PFm (x1, x2) = none → FMap.get G1m (x1, x2) = none → FMap.get pi x2 = none →
    FMap.get hs hx = some (x2, Known) → (∀ f h, FMap.get hs h ≠ some (y2, f)) →
    INV_CF_G1 (FMap.set hs ch (y2, Known)) (ch + 1)
      (FMap.set PFm (x1, x2) (y1, y2)) (FMap.set PFmi (y1, y2) (x1, x2))
      (FMap.set G1m (x1, x2) (y1, y2)) (FMap.set G1mi (y1, y2) (x1, x2))
      (FMap.set G1mh (x1, hx) (y1, ch)) (FMap.set G1mhi (y1, ch) (x1, hx))
      ro pi prefixes queries := by
  sorry

theorem lemma2' (hs : handles) (ch : handle) (PFm PFmi G1m G1mi : smap) (G1mh G1mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (x1 : block)
    (x2 : capacity) (y1 : block) (y2 : capacity) (hx : handle) :
    INV_CF_G1 hs ch PFm PFmi G1m G1mi G1mh G1mhi ro pi prefixes queries →
    ¬ FMap.dom PFm (y1, y2) → FMap.get PFmi (x1, x2) = none → FMap.get G1mi (x1, x2) = none →
    FMap.get hs hx = some (x2, Known) → (∀ f h, FMap.get hs h ≠ some (y2, f)) →
    INV_CF_G1 (FMap.set hs ch (y2, Known)) (ch + 1)
      (FMap.set PFm (y1, y2) (x1, x2)) (FMap.set PFmi (x1, x2) (y1, y2))
      (FMap.set G1m (y1, y2) (x1, x2)) (FMap.set G1mi (x1, x2) (y1, y2))
      (FMap.set G1mh (y1, ch) (x1, hx)) (FMap.set G1mhi (x1, hx) (y1, ch))
      ro pi prefixes queries := by
  sorry

theorem lemma3 (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (xa : block)
    (xc : capacity) (hx : handle) (ya : block) (yc : capacity) (hy : handle) (p : List block)
    (b : block) :
    INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries →
    FMap.get Pm (xa, xc) = some (ya, yc) → FMap.get Gm (xa, xc) = none →
    FMap.get mh (xa, hx) = some (ya, hy) → FMap.get hs hx = some (xc, Known) →
    FMap.get hs hy = some (yc, Unknown) → FMap.get pi xc = some (p, b) →
    INV_CF_G1 (FMap.set hs hy (yc, Known)) ch Pm Pmi
      (FMap.set Gm (xa, xc) (ya, yc)) (FMap.set Gmi (ya, yc) (xa, xc)) mh mhi
      ro (FMap.set pi yc (rcons p (b +^ xa), ya)) prefixes queries := by
  sorry

theorem m_mh_None (hs0 : handles) (PFm : smap) (G1mh : hsmap) (hx2 : handle) (x2 : capacity)
    (k : flag) (x1 : block) :
    m_mh hs0 PFm G1mh → FMap.get hs0 hx2 = some (x2, k) → FMap.get PFm (x1, x2) = none →
    FMap.get G1mh (x1, hx2) = none := by
  sorry

theorem build_hpath_None (G1mh : hsmap) (p : List block) :
    p.foldl (step_hpath G1mh) none = none := by
  sorry

theorem build_hpath_upd_ch (ha ch : handle) (mh : hsmap) (xa ya : block) (p : List block)
    (v : block) (hx : handle) :
    0 ≠ ch → ha ≠ ch →
    (∀ xa xb ha hb, FMap.get mh (xa, ha) = some (xb, hb) → ha ≠ ch ∧ hb ≠ ch) →
    build_hpath (FMap.set mh (xa, ha) (ya, ch)) p = some (v, hx) →
    if hx = ch then
      ∃ p0 x, build_hpath mh p0 = some (x, ha) ∧ p = rcons p0 (x +^ xa) ∧ v = ya
    else build_hpath mh p = some (v, hx) := by
  sorry

theorem build_hpath_up_None (G1mh : hsmap) (bi1 bi2 bi : hstate) (p : List block) :
    FMap.get G1mh bi1 = none → build_hpath G1mh p = some bi →
    build_hpath (FMap.set G1mh bi1 bi2) p = some bi := by
  sorry

theorem build_hpath_down_None (h ch : handle) (mh : hsmap) (xa : block) (ha : handle)
    (ya a : block) (p : List block) :
    h ≠ ch → ha ≠ ch → (∀ ya, FMap.get mh (ya, ch) = none) →
    build_hpath (FMap.set mh (xa, ha) (ya, ch)) p = some (a, h) →
    build_hpath mh p = some (a, h) := by
  sorry

theorem build_hpath_upd_ch_iff (ha ch : handle) (mh : hsmap) (xa ya : block) (p : List block)
    (v : block) (hx : handle) :
    FMap.get mh (xa, ha) = none → 0 ≠ ch → ha ≠ ch →
    (∀ xa xb ha hb, FMap.get mh (xa, ha) = some (xb, hb) → ha ≠ ch ∧ hb ≠ ch) →
    (build_hpath (FMap.set mh (xa, ha) (ya, ch)) p = some (v, hx) ↔
      if hx = ch then
        ∃ p0 x, build_hpath mh p0 = some (x, ha) ∧ p = rcons p0 (x +^ xa) ∧ v = ya
      else build_hpath mh p = some (v, hx)) := by
  sorry

theorem lemma4 (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (i : ℤ)
    (p : List block) (sa : block) (sc : capacity) (h : handle) (f : flag) :
    INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries → 0 ≤ i ∧ i < size p →
    FMap.dom prefixes (take (i + 1) p) → FMap.get prefixes (take i p) = some (sa, sc) →
    build_hpath mh (take i p) = some (sa, h) →
    FMap.get ro (take (i + 1) p) = some (oget (FMap.get prefixes (take (i + 1) p))).1 →
    FMap.get hs h = some (sc, f) → FMap.dom mh (sa +^ nth default p i, h) := by
  sorry

/-! ## The oracles of `CF` and `G1` agree up to the bad events -/

/-- The instance of `INV_CF_G1` that EasyCrypt's equivalences below state between `CF` (left,
`{1}`) and `G1` (right, `{2}`).  An abbreviation of that repeated expression, not an EasyCrypt
declaration. -/
def INV_CF_G1_12 (g₁ g₂ : VariableAssignment) : Prop :=
  INV_CF_G1 (FRO.m.get g₂) (G1.chandle.get g₂) (PF.m.get g₁) (PF.mi.get g₁) (G1.m.get g₂)
    (G1.mi.get g₂) (G1.mh.get g₂) (G1.mhi.get g₂) (F.RO.m.get g₂) (G1.paths.get g₂)
    (Redo.prefixes.get g₁) (C.queries.get g₂)

/-- `={glob C}`: an abbreviation, not an EasyCrypt declaration. -/
def eq_glob_C (g₁ g₂ : VariableAssignment) : Prop :=
  C.c.get g₁ = C.c.get g₂ ∧ C.queries.get g₁ = C.queries.get g₂

/-- `equiv eq_fi (D <: DISTINGUISHER {-PF, -RO, -G1}) : DPRestr(PF).fi ~
DPRestr(G1(DRestr(D)).S).fi : …`. -/
theorem eq_fi (D : DISTINGUISHER)
    (_hD : FVP.fvP D ≤ ((PF.m).footprint ⊔ (PF.mi).footprint ⊔ (F.RO.m).footprint ⊔
      (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint)ᶜ) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => G1.bcol.get g₂ = false ∧ G1.bext.get g₂ = false ∧ a₁ = a₂ ∧
        eq_glob_C g₁ g₂ ∧ INV_CF_G1_12 g₁ g₂)
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr (Indifferentiability.PRIMITIVE.view state (List block) block PF))
        ).procedure
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr G1.S)).procedure
      (fun r₁ g₁ r₂ g₂ =>
        if G1.bcol.get g₂ = true ∨ G1.bext.get g₂ = true then
          FMap.dom (C.queries.get g₁) [] ∧ FMap.dom (C.queries.get g₂) []
        else r₁ = r₂ ∧ eq_glob_C g₁ g₂ ∧ INV_CF_G1_12 g₁ g₂) := by
  sorry

/-- `equiv eq_f (D <: DISTINGUISHER {-PF, -RO, -G1}) : DPRestr(PF).f ~
DPRestr(G1(DRestr(D)).S).f : …`. -/
theorem eq_f (D : DISTINGUISHER)
    (_hD : FVP.fvP D ≤ ((PF.m).footprint ⊔ (PF.mi).footprint ⊔ (F.RO.m).footprint ⊔
      (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint)ᶜ) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => G1.bcol.get g₂ = false ∧ G1.bext.get g₂ = false ∧ a₁ = a₂ ∧
        eq_glob_C g₁ g₂ ∧ INV_CF_G1_12 g₁ g₂)
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr (Indifferentiability.PRIMITIVE.view state (List block) block PF))
        ).procedure
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr G1.S)).procedure
      (fun r₁ g₁ r₂ g₂ =>
        if G1.bcol.get g₂ = true ∨ G1.bext.get g₂ = true then FMap.dom (C.queries.get g₂) []
        else r₁ = r₂ ∧ eq_glob_C g₁ g₂ ∧ INV_CF_G1_12 g₁ g₂) := by
  sorry

theorem head_nth {α : Type} (w : α) (l : List α) : head w l = nth w l 0 := by
  sorry

theorem drop_add {α : Type} (n1 n2 : ℤ) (l : List α) :
    0 ≤ n1 → 0 ≤ n2 → drop (n1 + n2) l = drop n2 (drop n1 l) := by
  sorry

theorem behead_drop {α : Type} (l : List α) : behead l = drop 1 l := by
  sorry

theorem incl_upd_nin {α β : Type} [DecidableEq α] (m1 m2 : FMap α β) (x : α) (y : β) :
    incl m1 m2 → ¬ FMap.dom m2 x → incl m1 (FMap.set m2 x y) := by
  sorry

theorem lemma5 (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (i : ℤ)
    (p : List block) (b : block) (c : capacity) (h : handle) :
    INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries → 0 ≤ i ∧ i < size p →
    FMap.dom prefixes (take (i + 1) p) → FMap.get prefixes (take i p) = some (b, c) →
    (∃ f, FMap.get hs h = some (c, f)) →
    ∃ b' c' h', FMap.get Pm (b +^ nth default p i, c) = some (b', c') ∧
      FMap.get mh (b +^ nth default p i, h) = some (b', h') := by
  sorry

theorem lemma5' (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (i : ℤ)
    (p : List block) (b : block) (c : capacity) (h : handle) :
    INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries → 0 ≤ i ∧ i < size p →
    FMap.get prefixes (take i p) = some (b, c) → (∃ f, FMap.get hs h = some (c, f)) →
    (∃ b' c' h', FMap.get Pm (b +^ nth default p i, c) = some (b', c') ∧
      FMap.get mh (b +^ nth default p i, h) = some (b', h')) ∨
    (FMap.get Pm (b +^ nth default p i, c) = none ∧
      FMap.get mh (b +^ nth default p i, h) = none) := by
  sorry

/-- `equiv PFf_Cf (D <: DISTINGUISHER) : DFRestr(SqueezelessSponge(PF)).f ~
DFRestr(G1(DRestr(D)).M).f : …`. -/
theorem PFf_Cf (_D : DISTINGUISHER) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => ¬ (G1.bcol.get g₂ = true ∨ G1.bext.get g₂ = true) ∧ a₁ = a₂ ∧
        eq_glob_C g₁ g₂ ∧ INV_CF_G1_12 g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr (Indifferentiability.FUNCTIONALITY.view state (List block) block
          (Module.app SqueezelessSponge
            (Indifferentiability.PRIMITIVE.view state (List block) block PF))))).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr G1.M)).procedure
      (fun r₁ g₁ r₂ g₂ =>
        if G1.bcol.get g₂ = true ∨ G1.bext.get g₂ = true then FMap.dom (C.queries.get g₂) []
        else eq_glob_C g₁ g₂ ∧ r₁ = r₂ ∧ INV_CF_G1_12 g₁ g₂) := by
  sorry

section AUX

variable (D : DISTINGUISHER)

/-- `equiv CF_G1 : CF(DRestr(D)).main ~ G1(DRestr(D)).main : ={glob D} ==>
!(G1.bcol \/ G1.bext){2} => ={res}`, for `declare module D <: DISTINGUISHER
{-PF, -RO, -G1, -Redo, -C}` with the axiom `D_ll`. -/
theorem CF_G1 (hD : Module.Representable D distExt)
    (_hDd : FVP.fvP D ≤ ((PF.m).footprint ⊔ (PF.mi).footprint ⊔ (F.RO.m).footprint ⊔
      (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Redo.prefixes).footprint ⊔ C.footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D)ᶜ →
      FVP.fvP P ≤ (FVP.fvP D)ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless) :
    prhlProc
      (fun _ g₁ _ g₂ => (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (CF (DRestr D)).procedure (G1 (DRestr D)).procedure
      (fun r₁ _ r₂ g₂ => ¬ (G1.bcol.get g₂ = true ∨ G1.bext.get g₂ = true) → r₁ = r₂) := by
  sorry

end AUX

section

variable (D : DISTINGUISHER)

/-- EC's `Real_G1`, for `declare module D <: DISTINGUISHER {-Perm, -C, -PF, -G1, -RO, -Redo}`
with the axiom `D_ll`.  `mu dstate (pred1 witness)` is the probability of `default`. -/
theorem Real_G1 (hD : Module.Representable D distExt)
    (_hDd : FVP.fvP D ≤ ((EC.PRP.RP.m (D := state)).footprint ⊔
      (EC.PRP.RP.mi (D := state)).footprint ⊔ C.footprint ⊔ (PF.m).footprint ⊔
      (PF.mi).footprint ⊔ (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔
      (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint ⊔ (F.RO.m).footprint ⊔ (Redo.prefixes).footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D)ᶜ →
      FVP.fvP P ≤ (FVP.fvP D)ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (m : VariableAssignment) :
    (Procedure.Pr (GReal D).procedure () m (fun r g => r = true ∧ C.c.get g ≤ max_size) : ℝ) ≤
      (Procedure.Pr (G1 (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) +
        ((max_size ^ 2 - max_size : ℤ) : ℝ) * (2 : ℝ)⁻¹ * (dstate.1 {default}).toReal +
        (Procedure.Pr (G1 (DRestr D)).procedure () m (fun _ g => G1.bcol.get g = true) : ℝ) +
        (Procedure.Pr (G1 (DRestr D)).procedure () m (fun _ g => G1.bext.get g = true) : ℝ) := by
  sorry

end

end GaudisCrypt.SHA3.Handle
