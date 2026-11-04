import GaudisCrypt.Examples.SHA3.SmartCounter.ConcreteF
import GaudisCrypt.Logic.FrameTactics

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
/-- The clone's module variable `ROhandle.RO.m`. -/
global_var RO.m : FMap handle capacity
/-- The clone's module variable `ROhandle.FRO.m`. -/
global_var FRO.m : FMap handle (capacity × flag)
noncomputable abbrev RO := PROM.FullRO.RO handle capacity dout RO.m
noncomputable abbrev FRO := PROM.FullRO.FRO handle capacity dout FRO.m
end ROhandle

/-- The exported `FRO.m` of the `ROhandle` clone. -/
noncomputable abbrev FRO.m := ROhandle.FRO.m

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
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → m_mh hs m1 mh2 :=
  fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => h4

theorem mi_mhi_of_INV (ch : handle) (m1 m2 mi2 : smap) (mh2 : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (hs : handles)
    (mi1 : smap) (mhi2 : hsmap) (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → m_mh hs mi1 mhi2 :=
  fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => h5

theorem incl_of_INV (hs : handles) (ch : handle) (mi1 mi2 : smap) (mh2 mhi2 : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (m1 m2 : smap)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → incl m2 m1 :=
  fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => h6

theorem incli_of_INV (hs : handles) (ch : handle) (m1 m2 : smap) (mh2 mhi2 : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (mi1 mi2 : smap)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → incl mi2 mi1 :=
  fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => h7

theorem mh_of_INV (ch : handle) (m1 mi1 mi2 : smap) (mhi2 : hsmap)
    (pi : FMap capacity (List block × block)) (hs : handles) (m2 : smap) (mh2 : hsmap)
    (ro : FMap (List block) block) (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → mh_spec hs m2 mh2 ro :=
  fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => h8

theorem pi_of_INV (ch : handle) (m1 m2 mi1 mi2 : smap) (mhi2 : hsmap)
    (ro : FMap (List block) block) (hs : handles) (mh2 : hsmap)
    (pi : FMap capacity (List block × block)) (p : FMap (List block) state)
    (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → pi_spec hs mh2 pi :=
  fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => h9

theorem hs_of_INV (m1 m2 mi1 mi2 : smap) (mh2 mhi2 : hsmap) (ro : FMap (List block) block)
    (pi : FMap capacity (List block × block)) (hs : handles) (ch : handle)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → hs_spec hs ch :=
  fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => h1

theorem inv_of_INV (hs : handles) (ch : handle) (m1 mi1 m2 mi2 : smap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (mh2 mhi2 : hsmap)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → inv_spec mh2 mhi2 :=
  fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => h3

theorem invG_of_INV (hs : handles) (ch : handle) (m1 mi1 : smap) (mh2 mhi2 : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (m2 mi2 : smap)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → inv_spec m2 mi2 :=
  fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => h2

theorem m_p_of_INV (hs : handles) (ch : handle) (m1 mi1 : smap) (mh2 mhi2 : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (m2 mi2 : smap)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → m_p m1 p q :=
  fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => h10

theorem all_prefixes_of_m_p (m1 : smap) (p : FMap (List block) state)
    (q : FMap (List block) block) : m_p m1 p q → all_prefixes p := by
  rintro ⟨h0, -, h1, -, -⟩ l hl i
  by_cases hi0 : i ≤ 0
  · have : take i l = [] := by simp [take, Int.toNat_eq_zero.mpr hi0]
    rw [this]; exact (FMap.domE _ _).mpr (by simp [h0])
  by_cases his : i < size l
  · obtain ⟨sa, sc, hp, -⟩ := h1 l hl i ⟨by omega, his⟩
    exact (FMap.domE _ _).mpr (by simp [hp])
  · have : take i l = l := by
      unfold take; apply List.take_of_length_le; simp [size] at his; omega
    rw [this]; exact hl

theorem all_prefixes_of_INV (hs : handles) (ch : handle) (m1 mi1 : smap) (mh2 mhi2 : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block)) (m2 mi2 : smap)
    (p : FMap (List block) state) (q : FMap (List block) block) :
    INV_CF_G1 hs ch m1 mi1 m2 mi2 mh2 mhi2 ro pi p q → all_prefixes p := by
  rintro ⟨-, -, -, -, -, -, -, -, -, ⟨h0, -, h1, -, -⟩⟩ l hl i
  by_cases hi0 : i ≤ 0
  · have : take i l = [] := by simp [take, Int.toNat_eq_zero.mpr hi0]
    rw [this]; exact (FMap.domE _ _).mpr (by simp [h0])
  by_cases his : i < size l
  · obtain ⟨sa, sc, hp, -⟩ := h1 l hl i ⟨by omega, his⟩
    exact (FMap.domE _ _).mpr (by simp [hp])
  · have : take i l = l := by
      unfold take; apply List.take_of_length_le; simp [size] at his; omega
    rw [this]; exact hl

/-! ## Handles -/

theorem ch_gt0 (hs : handles) (ch : handle) : hs_spec hs ch → 0 < ch :=
  fun ⟨_, h0, hlt⟩ => hlt _ 0 h0

theorem ch_neq0 (hs : handles) (ch : handle) : hs_spec hs ch → 0 ≠ ch :=
  fun ⟨_, h0, hlt⟩ => ne_of_lt (hlt _ 0 h0)

theorem ch_notdomE_hs (hs : handles) (ch : handle) : hs_spec hs ch → FMap.get hs ch = none := by
  rintro ⟨-, -, hlt⟩
  cases h : FMap.get hs ch with
  | none => rfl
  | some cf => exact absurd (hlt cf ch h) (lt_irrefl _)

theorem Sch_notdomE_hs (hs : handles) (ch : handle) :
    hs_spec hs ch → FMap.get hs (ch + 1) = none := by
  rintro ⟨-, -, hlt⟩
  cases h : FMap.get hs (ch + 1) with
  | none => rfl
  | some cf => have := hlt cf _ h; linarith

theorem ch_notdomE2_mh (hs : handles) (m : smap) (mh : hsmap) (xa : block) (ch : handle) :
    m_mh hs m mh → hs_spec hs ch → FMap.get mh (xa, ch) = none := by
  rintro ⟨-, hmh⟩ ⟨-, -, hlt⟩
  cases h : FMap.get mh (xa, ch) with
  | none => rfl
  | some y =>
    obtain ⟨xc, fx, yc, fy, hx, -, -⟩ := hmh xa ch y.1 y.2 h
    exact absurd (hlt _ _ hx) (lt_irrefl _)

theorem Sch_notdomE2_mh (hs : handles) (m : smap) (mh : hsmap) (xa : block) (ch : handle) :
    m_mh hs m mh → hs_spec hs ch → FMap.get mh (xa, ch + 1) = none := by
  rintro ⟨-, hmh⟩ ⟨-, -, hlt⟩
  cases h : FMap.get mh (xa, ch + 1) with
  | none => rfl
  | some y =>
    obtain ⟨xc, fx, yc, fy, hx, -, -⟩ := hmh xa _ y.1 y.2 h
    have := hlt _ _ hx; linarith

theorem dom_hs_neq_ch (hs : handles) (ch hx : handle) (xc : capacity) (fx : flag) :
    hs_spec hs ch → FMap.get hs hx = some (xc, fx) → hx ≠ ch := by
  rintro ⟨-, -, hlt⟩ h
  have := hlt _ _ h; linarith

theorem dom_hs_neq_Sch (hs : handles) (ch hx : handle) (xc : capacity) (fx : flag) :
    hs_spec hs ch → FMap.get hs hx = some (xc, fx) → hx ≠ ch + 1 := by
  rintro ⟨-, -, hlt⟩ h
  have := hlt _ _ h; linarith

theorem notin_m_notin_mh (hs : handles) (m : smap) (mh : hsmap) (xa : block) (xc : capacity)
    (hx : handle) (fx : flag) :
    m_mh hs m mh → FMap.get m (xa, xc) = none → FMap.get hs hx = some (xc, fx) →
    FMap.get mh (xa, hx) = none := by
  rintro ⟨-, hmh⟩ hm hhs
  cases h : FMap.get mh (xa, hx) with
  | none => rfl
  | some y =>
    obtain ⟨xc', fx', yc, fy, hx', -, hm'⟩ := hmh xa hx y.1 y.2 h
    rw [hhs] at hx'
    simp only [Option.some.injEq, Prod.mk.injEq] at hx'
    obtain ⟨rfl, rfl⟩ := hx'
    rw [hm] at hm'; cases hm'

theorem notin_m_notin_Gm {α β : Type} [DecidableEq α] (m Gm : FMap α β) (x : α) :
    incl Gm m → FMap.get m x = none → FMap.get Gm x = none := by
  intro hincl hm
  by_contra h
  have := hincl x h
  rw [hm] at this; exact h this.symm

theorem notin_hs_notdomE2_mh (hs : handles) (m : smap) (mh : hsmap) (xa : block) (hx : handle) :
    m_mh hs m mh → FMap.get hs hx = none → FMap.get mh (xa, hx) = none := by
  rintro ⟨-, hmh⟩ hhs
  cases h : FMap.get mh (xa, hx) with
  | none => rfl
  | some y =>
    obtain ⟨xc', fx', yc, fy, hx', -, -⟩ := hmh xa hx y.1 y.2 h
    rw [hhs] at hx'; cases hx'

theorem m_mh_addh (hs : handles) (ch : handle) (m : smap) (mh : hsmap) (xc : capacity)
    (fx : flag) : hs_spec hs ch → m_mh hs m mh → m_mh (FMap.set hs ch (xc, fx)) m mh := by
  rintro ⟨-, -, hlt⟩ ⟨h1, h2⟩
  have hne : ∀ h cf, FMap.get hs h = some cf → FMap.get (FMap.set hs ch (xc, fx)) h = some cf :=
    fun h cf hh => by rw [FMap.get_set_neqE _ _ _ _ (ne_of_lt (hlt cf h hh))]; exact hh
  constructor
  · intro xa xc' ya yc hm
    obtain ⟨hx, fx', hy, fy, a, b, c⟩ := h1 xa xc' ya yc hm
    exact ⟨hx, fx', hy, fy, hne _ _ a, hne _ _ b, c⟩
  · intro xa hx ya hy hm
    obtain ⟨xc', fx', yc, fy, a, b, c⟩ := h2 xa hx ya hy hm
    exact ⟨xc', fx', yc, fy, hne _ _ a, hne _ _ b, c⟩

theorem m_mh_updh (fy0 : flag) (hs : handles) (m : smap) (mh : hsmap) (yc : capacity)
    (hy : handle) (fy : flag) :
    m_mh hs m mh → FMap.get hs hy = some (yc, fy0) → m_mh (FMap.set hs hy (yc, fy)) m mh := by
  rintro ⟨h1, h2⟩ hhy
  have key : ∀ h c f, FMap.get hs h = some (c, f) →
      ∃ f', FMap.get (FMap.set hs hy (yc, fy)) h = some (c, f') := by
    intro h c f hh
    by_cases e : h = hy
    · rw [e, hhy] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      exact ⟨fy, by rw [e]; simp⟩
    · exact ⟨f, by rw [FMap.get_set_neqE _ _ _ _ e]; exact hh⟩
  constructor
  · intro xa xc ya yc' hm
    obtain ⟨hx, fx, hy', fy', a, b, c⟩ := h1 xa xc ya yc' hm
    obtain ⟨f1, a'⟩ := key _ _ _ a
    obtain ⟨f2, b'⟩ := key _ _ _ b
    exact ⟨hx, f1, hy', f2, a', b', c⟩
  · intro xa hx ya hy' hmh
    obtain ⟨xc, fx, yc', fy', a, b, c⟩ := h2 xa hx ya hy' hmh
    obtain ⟨f1, a'⟩ := key _ _ _ a
    obtain ⟨f2, b'⟩ := key _ _ _ b
    exact ⟨xc, f1, yc', f2, a', b', c⟩

theorem m_mh_addh_addm (hs : handles) (Pm : smap) (mh : hsmap) (hx : handle) (xa : block)
    (xc : capacity) (hy : handle) (ya : block) (yc : capacity) (f f' : flag) :
    m_mh hs Pm mh → huniq hs → FMap.get hs hx = some (xc, f) → FMap.get hs hy = none →
    m_mh (FMap.set hs hy (yc, f')) (FMap.set Pm (xa, xc) (ya, yc))
      (FMap.set mh (xa, hx) (ya, hy)) := by
  rintro ⟨h1, h2⟩ hu hhx hhy
  have hne : ∀ h c, FMap.get hs h = some c → h ≠ hy := fun h c hh e => by
    rw [e, hhy] at hh; cases hh
  have hold : ∀ h c, FMap.get hs h = some c → FMap.get (FMap.set hs hy (yc, f')) h = some c :=
    fun h c hh => by rw [FMap.get_set_neqE _ _ _ _ (hne _ _ hh)]; exact hh
  constructor
  · intro xa0 xc0 ya0 yc0 hm
    rw [FMap.get_setE] at hm
    split_ifs at hm with e
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨hx, f, hy, f', hold _ _ hhx, by simp, by simp⟩
    · obtain ⟨hx0, fx0, hy0, fy0, a, b, c⟩ := h1 _ _ _ _ hm
      refine ⟨hx0, fx0, hy0, fy0, hold _ _ a, hold _ _ b, ?_⟩
      rw [FMap.get_set_neqE]
      · exact c
      · intro e'
        simp only [Prod.mk.injEq] at e'
        obtain ⟨rfl, rfl⟩ := e'
        rw [hhx] at a
        simp only [Option.some.injEq, Prod.mk.injEq] at a
        exact e (by rw [a.1])
  · intro xa0 hx0 ya0 hy0 hm
    rw [FMap.get_setE] at hm
    split_ifs at hm with e
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨xc, f, yc, f', hold _ _ hhx, by simp, by simp⟩
    · obtain ⟨xc0, fx0, yc0, fy0, a, b, c⟩ := h2 _ _ _ _ hm
      refine ⟨xc0, fx0, yc0, fy0, hold _ _ a, hold _ _ b, ?_⟩
      rw [FMap.get_set_neqE]
      · exact c
      · intro e'
        simp only [Prod.mk.injEq] at e'
        obtain ⟨rfl, rfl⟩ := e'
        exact e (by rw [hu _ _ _ _ a hhx rfl])

theorem mi_mhi_addh_addmi (hs : handles) (mi : smap) (mhi : hsmap) (hx : handle) (xa : block)
    (xc : capacity) (hy : handle) (ya : block) (yc : capacity) (fx fy : flag) :
    m_mh hs mi mhi → (∀ f h, FMap.get hs h ≠ some (yc, f)) → FMap.get hs hx = some (xc, fx) →
    FMap.get hs hy = none →
    m_mh (FMap.set hs hy (yc, fy)) (FMap.set mi (ya, yc) (xa, xc))
      (FMap.set mhi (ya, hy) (xa, hx)) := by
  rintro ⟨h1, h2⟩ hyc hhx hhy
  have hne : ∀ h c, FMap.get hs h = some c → h ≠ hy := fun h c hh e => by
    rw [e, hhy] at hh; cases hh
  have hold : ∀ h c, FMap.get hs h = some c → FMap.get (FMap.set hs hy (yc, fy)) h = some c :=
    fun h c hh => by rw [FMap.get_set_neqE _ _ _ _ (hne _ _ hh)]; exact hh
  constructor
  · intro ya0 yc0 xa0 xc0 hm
    rw [FMap.get_setE] at hm
    split_ifs at hm with e
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨hy, fy, hx, fx, by simp, hold _ _ hhx, by simp⟩
    · obtain ⟨hy0, fy0, hx0, fx0, a, b, c⟩ := h1 _ _ _ _ hm
      refine ⟨hy0, fy0, hx0, fx0, hold _ _ a, hold _ _ b, ?_⟩
      rw [FMap.get_set_neqE]
      · exact c
      · intro e'
        simp only [Prod.mk.injEq] at e'
        exact hne _ _ a e'.2
  · intro ya0 hy0 xa0 hx0 hm
    rw [FMap.get_setE] at hm
    split_ifs at hm with e
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨yc, fy, xc, fx, by simp, hold _ _ hhx, by simp⟩
    · obtain ⟨yc0, fy0, xc0, fx0, a, b, c⟩ := h2 _ _ _ _ hm
      refine ⟨yc0, fy0, xc0, fx0, hold _ _ a, hold _ _ b, ?_⟩
      rw [FMap.get_set_neqE]
      · exact c
      · intro e'
        simp only [Prod.mk.injEq] at e'
        obtain ⟨rfl, rfl⟩ := e'
        exact hyc _ _ a

theorem inv_mh_inv_Pm (hs : handles) (Pm Pmi : smap) (mh mhi : hsmap) :
    m_mh hs Pm mh → m_mh hs Pmi mhi → inv_spec mh mhi → inv_spec Pm Pmi := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨hinv⟩
  constructor
  rintro ⟨xa, xc⟩ ⟨ya, yc⟩
  constructor
  · intro h
    obtain ⟨hx, fx, hy, fy, hhx, hhy, hmh⟩ := a1 _ _ _ _ h
    obtain ⟨yc', fy', xc', fx', hhy', hhx', hP⟩ := b2 _ _ _ _ ((hinv _ _).mp hmh)
    rw [hhy] at hhy'; rw [hhx] at hhx'
    simp only [Option.some.injEq, Prod.mk.injEq] at hhy' hhx'
    obtain ⟨rfl, rfl⟩ := hhy'; obtain ⟨rfl, rfl⟩ := hhx'
    exact hP
  · intro h
    obtain ⟨hy, fy, hx, fx, hhy, hhx, hmhi⟩ := b1 _ _ _ _ h
    obtain ⟨xc', fx', yc', fy', hhx', hhy', hP⟩ := a2 _ _ _ _ ((hinv _ _).mpr hmhi)
    rw [hhy] at hhy'; rw [hhx] at hhx'
    simp only [Option.some.injEq, Prod.mk.injEq] at hhy' hhx'
    obtain ⟨rfl, rfl⟩ := hhy'; obtain ⟨rfl, rfl⟩ := hhx'
    exact hP

theorem inv_incl_none {α β : Type} [DecidableEq α] [DecidableEq β] (Pm : FMap α β)
    (Pmi : FMap β α) (Gm : FMap α β) (x : α) (Gmi : FMap β α) (y : β) :
    inv_spec Pm Pmi → inv_spec Gm Gmi → incl Gm Pm → incl Gmi Pmi → FMap.get Pm x = some y →
    (FMap.get Gm x = none ↔ FMap.get Gmi y = none) := by
  rintro ⟨invP⟩ ⟨invG⟩ hG hGi hx
  have hy := (invP x y).mp hx
  constructor
  · intro hGx
    cases h : FMap.get Gmi y with
    | none => rfl
    | some x' =>
      have := hGi y (by rw [h]; simp)
      rw [h, hy] at this
      cases this
      exact absurd ((invG x y).mpr h) (by rw [hGx]; simp)
  · intro hGy
    cases h : FMap.get Gm x with
    | none => rfl
    | some y' =>
      have := hG x (by rw [h]; simp)
      rw [h, hx] at this
      cases this
      exact absurd ((invG x y).mp h) (by rw [hGy]; simp)

theorem huniq_addh (hs : handles) (h : handle) (c : capacity) (f : flag) :
    huniq hs → (∀ f' h', FMap.get hs h' ≠ some (c, f')) → huniq (FMap.set hs h (c, f)) := by
  intro hu hc h1 h2 ⟨c1, f1⟩ ⟨c2, f2⟩ g1 g2 e
  simp only at e; subst e
  rw [FMap.get_setE] at g1 g2
  split_ifs at g1 g2 with e1 e2 e2
  · rw [e1, e2]
  · simp only [Option.some.injEq, Prod.mk.injEq] at g1; obtain ⟨rfl, rfl⟩ := g1
    exact absurd g2 (hc _ _)
  · simp only [Option.some.injEq, Prod.mk.injEq] at g2; obtain ⟨rfl, rfl⟩ := g2
    exact absurd g1 (hc _ _)
  · exact hu _ _ _ _ g1 g2 rfl

theorem hs_addh (hs : handles) (ch : handle) (xc : capacity) (fx : flag) :
    hs_spec hs ch → (∀ f h, FMap.get hs h ≠ some (xc, f)) →
    hs_spec (FMap.set hs ch (xc, fx)) (ch + 1) := by
  rintro ⟨hu, h0, hlt⟩ hxc
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2 ⟨c1, f1⟩ ⟨c2, f2⟩ g1 g2 e
    simp only at e; subst e
    rw [FMap.get_setE] at g1 g2
    split_ifs at g1 g2 with e1 e2 e2
    · rw [e1, e2]
    · simp only [Option.some.injEq, Prod.mk.injEq] at g1; obtain ⟨rfl, rfl⟩ := g1
      exact absurd g2 (hxc _ _)
    · simp only [Option.some.injEq, Prod.mk.injEq] at g2; obtain ⟨rfl, rfl⟩ := g2
      exact absurd g1 (hxc _ _)
    · exact hu _ _ _ _ g1 g2 rfl
  · rw [FMap.get_set_neqE _ _ _ _ (ne_of_lt (hlt _ 0 h0))]; exact h0
  · intro cf h hh
    rw [FMap.get_setE] at hh
    split_ifs at hh with e
    · linarith
    · have := hlt _ _ hh; linarith

theorem hs_updh (hs : handles) (ch : handle) (fx : flag) (hx : handle) (xc : capacity)
    (fx' : flag) :
    hs_spec hs ch → 0 ≠ hx → FMap.get hs hx = some (xc, fx) →
    hs_spec (FMap.set hs hx (xc, fx')) ch := by
  rintro ⟨hu, h0, hlt⟩ hx0 hhx
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2 ⟨c1, f1⟩ ⟨c2, f2⟩ g1 g2 e
    simp only at e; subst e
    rw [FMap.get_setE] at g1 g2
    split_ifs at g1 g2 with e1 e2 e2
    · rw [e1, e2]
    · simp only [Option.some.injEq, Prod.mk.injEq] at g1; obtain ⟨rfl, rfl⟩ := g1
      rw [e1]; exact hu _ _ _ _ hhx g2 rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at g2; obtain ⟨rfl, rfl⟩ := g2
      rw [e2]; exact hu _ _ _ _ g1 hhx rfl
    · exact hu _ _ _ _ g1 g2 rfl
  · rw [FMap.get_set_neqE _ _ _ _ hx0]; exact h0
  · intro cf h hh
    rw [FMap.get_setE] at hh
    split_ifs at hh with e
    · rw [e]; exact hlt _ _ hhx
    · exact hlt _ _ hh

theorem mh_addh (hs : handles) (ch : handle) (Gm : smap) (mh : hsmap)
    (ro : FMap (List block) block) (xc : capacity) (fx : flag) :
    hs_spec hs ch → mh_spec hs Gm mh ro → mh_spec (FMap.set hs ch (xc, fx)) Gm mh ro := by
  rintro ⟨-, -, hlt⟩ ⟨a, b, c⟩
  refine ⟨?_, b, c⟩
  intro xa hx ya hy hmh
  obtain ⟨xc', fx', yc', fy', g1, g2, g3⟩ := a xa hx ya hy hmh
  refine ⟨xc', fx', yc', fy', ?_, ?_, g3⟩
  · rw [FMap.get_set_neqE _ _ _ _ (ne_of_lt (hlt _ _ g1))]; exact g1
  · rw [FMap.get_set_neqE _ _ _ _ (ne_of_lt (hlt _ _ g2))]; exact g2

theorem inv_addm {α β : Type} [DecidableEq α] [DecidableEq β] (m : FMap α β) (mi : FMap β α)
    (x : α) (y : β) :
    inv_spec m mi → FMap.get m x = none → FMap.get mi y = none →
    inv_spec (FMap.set m x y) (FMap.set mi y x) := by
  rintro ⟨hinv⟩ hmx hmiy
  constructor
  intro x' y'
  simp only [FMap.get_setE]
  by_cases ex : x' = x <;> by_cases ey : y' = y
  · subst ex ey; simp
  · subst ex
    simp only [if_true, ey, if_false, Option.some.injEq]
    constructor
    · intro e; exact absurd e.symm ey
    · intro e; rw [(hinv _ _).mpr e] at hmx; cases hmx
  · subst ey
    simp only [if_true, ex, if_false, Option.some.injEq]
    constructor
    · intro e; rw [(hinv _ _).mp e] at hmiy; cases hmiy
    · intro e; exact absurd e.symm ex
  · simp only [ex, ey, if_false]; exact hinv x' y'

theorem incl_addm {α β : Type} [DecidableEq α] (m m' : FMap α β) (x : α) (y : β) :
    incl m m' → incl (FMap.set m x y) (FMap.set m' x y) := by
  intro h x' hx
  by_cases e : x' = x
  · subst e; simp
  · rw [FMap.get_set_neqE _ _ _ _ e] at hx ⊢
    rw [FMap.get_set_neqE _ _ _ _ e]; exact h x' hx

noncomputable def getflag (hs : handles) (xc : capacity) : Option flag :=
  ((hinv hs xc).bind (FMap.get hs)).map Prod.snd

theorem getflagP_none (hs : handles) (xc : capacity) :
    getflag hs xc = none ↔ ∀ f h, FMap.get hs h ≠ some (xc, f) := by
  have hp := hinvP hs xc
  unfold getflag
  split_ifs at hp with hn
  · rw [hn]; exact ⟨fun _ f h => hp h f, fun _ => rfl⟩
  · obtain ⟨f, hf⟩ := hp
    obtain ⟨h, hh⟩ := Option.ne_none_iff_exists'.mp hn
    rw [hh] at hf ⊢
    simp only [oget, Option.getD_some] at hf
    simp only [Option.bind_some, hf, Option.map_some]
    constructor
    · intro e; cases e
    · intro hall; exact absurd hf (hall f h)

theorem getflagP_some (hs : handles) (xc : capacity) (f : flag) :
    huniq hs → (getflag hs xc = some f ↔ FMap.rng hs (xc, f)) := by
  intro hu
  have hp := hinvP hs xc
  unfold getflag
  split_ifs at hp with hn
  · rw [hn]
    constructor
    · intro e; cases e
    · rintro ⟨h, hh⟩; exact absurd hh (hp h f)
  · obtain ⟨f', hf⟩ := hp
    obtain ⟨h, hh⟩ := Option.ne_none_iff_exists'.mp hn
    rw [hh] at hf ⊢
    simp only [oget, Option.getD_some] at hf
    simp only [Option.bind_some, hf, Option.map_some, Option.some.injEq]
    constructor
    · intro e; subst e; exact ⟨h, hf⟩
    · rintro ⟨h', hh'⟩
      have e := hu _ _ _ _ hf hh' rfl
      subst e
      change FMap.get hs h = _ at hh'
      rw [hf] at hh'
      simp only [Option.some.injEq, Prod.mk.injEq] at hh'
      exact hh'.2

/-! ## Handle paths -/

theorem build_hpath_prefix (mh : hsmap) (p : List block) (b v : block) (h : handle) :
    build_hpath mh (rcons p b) = some (v, h) ↔
      ∃ v' h', build_hpath mh p = some (v', h') ∧ FMap.get mh (v' +^ b, h') = some (v, h) := by
  rw [build_hpathP]
  constructor
  · rintro (⟨hnil, -, -⟩ | ⟨p', b', v', h', heq, hb, hm⟩)
    · simp [rcons] at hnil
    · have := List.append_inj' heq rfl
      simp only [List.cons.injEq, and_true] at this
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨v', h', hb, hm⟩
  · rintro ⟨v', h', hb, hm⟩
    exact .Extend p b v' h' rfl hb hm

theorem build_hpath_up (mh : hsmap) (xa : block) (hx : handle) (ya : block) (hy : handle)
    (p : List block) (za : block) (hz : handle) :
    build_hpath mh p = some (za, hz) → FMap.get mh (xa, hx) = none →
    build_hpath (FMap.set mh (xa, hx) (ya, hy)) p = some (za, hz) := by
  intro hp hn
  induction p using List.reverseRecOn generalizing za hz with
  | nil => exact hp
  | append_singleton p b ih =>
    obtain ⟨v', h', hb, hm⟩ := (build_hpath_prefix mh p b za hz).1 hp
    refine (build_hpath_prefix _ p b za hz).2 ⟨v', h', ih v' h' hb, ?_⟩
    rw [FMap.get_setE, if_neg]
    · exact hm
    · intro he
      rw [he, hn] at hm
      cases hm

theorem build_hpath_down (mh : hsmap) (xa : block) (hx : handle) (ya : block) (hy : handle)
    (p : List block) (v : block) (h : handle) :
    (∀ p v, build_hpath mh p ≠ some (v, hx)) →
    build_hpath (FMap.set mh (xa, hx) (ya, hy)) p = some (v, h) →
    build_hpath mh p = some (v, h) := by
  intro hno hp
  induction p using List.reverseRecOn generalizing v h with
  | nil => exact hp
  | append_singleton p b ih =>
    obtain ⟨v', h', hb, hm⟩ := (build_hpath_prefix _ p b v h).1 hp
    have hb' := ih v' h' hb
    refine (build_hpath_prefix mh p b v h).2 ⟨v', h', hb', ?_⟩
    rw [FMap.get_setE, if_neg] at hm
    · exact hm
    · intro he
      simp only [Prod.mk.injEq] at he
      exact hno p v' (he.2 ▸ hb')

theorem known_path_uniq (hs : handles) (mh : hsmap) (pi : FMap capacity (List block × block))
    (xc : capacity) (hx : handle) (p : List block) (xa : block) (p' : List block) (xa' : block) :
    pi_spec hs mh pi → FMap.get hs hx = some (xc, Known) → build_hpath mh p = some (xa, hx) →
    build_hpath mh p' = some (xa', hx) → p = p' ∧ xa = xa' := by
  rintro ⟨Ipi⟩ hs_hx hp hp'
  have h1 := (Ipi xc p xa).2 ⟨hx, hp, hs_hx⟩
  have h2 := (Ipi xc p' xa').2 ⟨hx, hp', hs_hx⟩
  rw [h1] at h2
  simpa using h2

theorem path_split (hs : handles) (ch : handle) (m : smap) (mh : hsmap) (xc : capacity)
    (hx : handle) (p : List block) (xa : block) :
    hs_spec hs ch → m_mh hs m mh → FMap.get hs hx = some (xc, Unknown) →
    build_hpath mh p = some (xa, hx) →
    ∃ pk ya yc hy b za zc hz pu,
      p = rcons pk b ++ pu ∧ build_hpath mh pk = some (ya, hy) ∧
      FMap.get hs hy = some (yc, Known) ∧ FMap.get mh (ya +^ b, hy) = some (za, hz) ∧
      FMap.get hs hz = some (zc, Unknown) := by
  rintro ⟨-, hs0, -⟩ ⟨-, Imh⟩
  induction p using List.reverseRecOn generalizing hx xa xc with
  | nil =>
    intro hs_hx hp
    simp only [build_hpath, List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp
    rw [hs0] at hs_hx
    cases hs_hx
  | append_singleton p b ih =>
    intro hs_hx hp
    obtain ⟨ya, hy, hpy, hm⟩ := (build_hpath_prefix mh p b xa hx).1 hp
    obtain ⟨yc, fy, xc', fx', hs_hy, hs_hx', -⟩ := Imh _ _ _ _ hm
    cases fy with
    | Known => exact ⟨p, ya, yc, hy, b, xa, xc, hx, [], by simp [rcons], hpy, hs_hy, hm, hs_hx⟩
    | Unknown =>
      obtain ⟨pk, ya', yc', hy', b', za, zc, hz, pu, he, h2, h3, h4, h5⟩ :=
        ih (hx := hy) (xa := ya) (xc := yc) hs_hy hpy
      exact ⟨pk, ya', yc', hy', b', za, zc, hz, rcons pu b, by simp [he, rcons], h2, h3, h4, h5⟩

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
  intro HINV hx2y2 Pm_x Gm_x hx2 hy2
  obtain ⟨Hhs, HinvG, Hinvmh, Hmmh, Hmimhi, Hincl, Hincli, Hmh, Hpi, Hmp⟩ := HINV
  obtain ⟨hun, hs0, hlt⟩ := id Hhs
  obtain ⟨Imm1, Imm2⟩ := id Hmmh
  obtain ⟨Imi1, Imi2⟩ := id Hmimhi
  obtain ⟨Imh1, Imh2, Imh3⟩ := Hmh
  have hch0 : 0 < ch := hlt _ 0 hs0
  have hs_ch : FMap.get hs ch = none := ch_notdomE_hs hs ch Hhs
  have hs_Sch : FMap.get hs (ch + 1) = none := Sch_notdomE_hs hs ch Hhs
  have mh_ch : ∀ a, FMap.get mh (a, ch) = none := fun a => ch_notdomE2_mh hs Pm mh a ch Hmmh Hhs
  have hsne : ∀ h cf, FMap.get hs h = some cf →
      FMap.get (FMap.set (FMap.set hs ch (x2, Known)) (ch + 1) (y2, Known)) h = some cf := by
    intro h cf hh
    have := hlt _ _ hh
    rw [FMap.get_set_neqE _ _ _ _ (show h ≠ ch + 1 by linarith),
      FMap.get_set_neqE _ _ _ _ (show h ≠ ch by linarith), hh]
  have notrng : ∀ hc, FMap.get hs hc = none → ∀ a h a', FMap.get mh (a, h) ≠ some (a', hc) := by
    intro hc hn a h a' hm
    obtain ⟨_, _, _, fy, _, h2, _⟩ := Imm2 _ _ _ _ hm
    rw [hn] at h2
    cases h2
  have nopath : ∀ hc, FMap.get hs hc = none → ∀ p v, build_hpath mh p ≠ some (v, hc) := by
    intro hc hn p v hp
    rcases (build_hpathP _ _ _ _).1 hp with ⟨-, -, rfl⟩ | ⟨p', b, v', h', -, -, hm⟩
    · rw [hs0] at hn
      cases hn
    · exact notrng hc hn _ _ _ hm
  have mhup : ∀ p v h, build_hpath mh p = some (v, h) →
      build_hpath (FMap.set mh (x1, ch) (y1, ch + 1)) p = some (v, h) :=
    fun p v h hp => build_hpath_up mh x1 ch y1 (ch + 1) p v h hp (mh_ch x1)
  have mhdown : ∀ p v h, build_hpath (FMap.set mh (x1, ch) (y1, ch + 1)) p = some (v, h) →
      build_hpath mh p = some (v, h) :=
    fun p v h hp => build_hpath_down mh x1 ch y1 (ch + 1) p v h (nopath ch hs_ch) hp
  have Hmp' : ∀ (x y : state), FMap.get Pm x = none → m_p (FMap.set Pm x y) prefixes queries := by
    obtain ⟨c1, c2, c3, c4, c5⟩ := Hmp
    intro x y hx
    refine ⟨c1, c2, ?_, c4, c5⟩
    intro l hl i hi
    obtain ⟨sa, sc, h1, h2⟩ := c3 l hl i hi
    refine ⟨sa, sc, h1, ?_⟩
    have hne : FMap.get prefixes (take (i + 1) l) ≠ none := by
      by_cases hi' : i + 1 < size l
      · obtain ⟨sa', sc', h1', -⟩ := c3 l hl (i + 1) ⟨by omega, hi'⟩
        rw [h1']
        simp
      · have : take (i + 1) l = l := by
          simp only [take, size] at *
          apply List.take_of_length_le
          omega
        rw [this]
        exact (FMap.domE _ _).1 hl
    rw [FMap.get_setE, if_neg]
    · exact h2
    · intro he
      rw [he, hx] at h2
      exact hne h2.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Hmp' _ _ Pm_x⟩
  · rw [show ch + 2 = ch + 1 + 1 by ring]
    refine hs_addh _ _ _ _ (hs_addh hs ch x2 Known Hhs hx2) ?_
    intro f h
    rw [FMap.get_setE]
    split_ifs
    · simp [hx2y2]
    · exact hy2 f h
  · refine inv_addm _ _ _ _ HinvG Gm_x ?_
    cases hg : FMap.get Gmi (y1, y2) with
    | none => rfl
    | some xc =>
      have hp := Hincli (y1, y2) (by rw [hg]; simp)
      rw [hg] at hp
      obtain ⟨_, fx, _, _, h1, _, _⟩ := Imi1 _ _ _ _ hp
      exact absurd h1 (hy2 _ _)
  · exact inv_addm _ _ _ _ Hinvmh (mh_ch x1) (Sch_notdomE2_mh hs Pmi mhi y1 ch Hmimhi Hhs)
  · refine m_mh_addh_addm (FMap.set hs ch (x2, Known)) Pm mh ch x1 x2 (ch + 1) y1 y2 Known Known
      (m_mh_addh hs ch Pm mh x2 Known Hhs Hmmh) (hs_addh hs ch x2 Known Hhs hx2).1
      (FMap.get_set_sameE _ _ _) ?_
    rw [FMap.get_set_neqE _ _ _ _ (show ch + 1 ≠ ch by simp)]
    exact hs_Sch
  · refine mi_mhi_addh_addmi (FMap.set hs ch (x2, Known)) Pmi mhi ch x1 x2 (ch + 1) y1 y2
      Known Known (m_mh_addh hs ch Pmi mhi x2 Known Hhs Hmimhi) ?_ (FMap.get_set_sameE _ _ _) ?_
    · intro f h
      rw [FMap.get_setE]
      split_ifs
      · simp [hx2y2]
      · exact hy2 f h
    · rw [FMap.get_set_neqE _ _ _ _ (show ch + 1 ≠ ch by simp)]
      exact hs_Sch
  · exact incl_addm _ _ _ _ Hincl
  · exact incl_addm _ _ _ _ Hincli
  · refine ⟨?_, ?_, ?_⟩
    · intro xa hx ya hy hm
      rw [FMap.get_setE] at hm
      split_ifs at hm with hk
      · simp only [Prod.mk.injEq, Option.some.injEq] at hk hm
        obtain ⟨hk1, hk2⟩ := hk
        obtain ⟨hm1, hm2⟩ := hm
        subst xa hx ya hy
        refine ⟨x2, Known, y2, Known, ?_, FMap.get_set_sameE _ _ _, ?_⟩
        · rw [FMap.get_set_neqE _ _ _ _ (show ch ≠ ch + 1 by simp), FMap.get_set_sameE]
        · simp
      · obtain ⟨xc, fx, yc, fy, h1, h2, h3⟩ := Imh1 _ _ _ _ hm
        refine ⟨xc, fx, yc, fy, hsne _ _ h1, hsne _ _ h2, ?_⟩
        cases fy with
        | Known =>
          simp only [if_true] at h3 ⊢
          refine ⟨?_, h3.2⟩
          rw [FMap.get_set_neqE]
          · exact h3.1
          · intro he
            rw [he, Gm_x] at h3
            cases h3.1
        | Unknown =>
          simp only [reduceCtorEq, if_false] at h3 ⊢
          obtain ⟨p, v, h4, h5⟩ := h3
          exact ⟨p, v, h4, mhup _ _ _ h5⟩
    · intro p bn b
      rw [Imh2]
      constructor
      · rintro ⟨v, hx, hy, h1, h2⟩
        refine ⟨v, hx, hy, mhup _ _ _ h1, ?_⟩
        rw [FMap.get_set_neqE]
        · exact h2
        · intro he
          rw [he, mh_ch] at h2
          cases h2
      · rintro ⟨v, hx, hy, h1, h2⟩
        have h1' := mhdown _ _ _ h1
        refine ⟨v, hx, hy, h1', ?_⟩
        rw [FMap.get_set_neqE] at h2
        · exact h2
        · intro he
          simp only [Prod.mk.injEq] at he
          exact nopath ch hs_ch p v (he.2 ▸ h1')
    · intro p v p' v' hx h1 h2
      exact Imh3 p v p' v' hx (mhdown _ _ _ h1) (mhdown _ _ _ h2)
  · obtain ⟨Ipi⟩ := Hpi
    refine ⟨fun c p v => ?_⟩
    rw [Ipi]
    constructor
    · rintro ⟨h, h1, h2⟩
      exact ⟨h, mhup _ _ _ h1, hsne _ _ h2⟩
    · rintro ⟨h, h1, h2⟩
      have h1' := mhdown _ _ _ h1
      refine ⟨h, h1', ?_⟩
      have hne1 : h ≠ ch + 1 := by
        intro he
        exact nopath (ch + 1) hs_Sch p v (he ▸ h1')
      have hne2 : h ≠ ch := by
        intro he
        exact nopath ch hs_ch p v (he ▸ h1')
      rwa [FMap.get_set_neqE _ _ _ _ hne1, FMap.get_set_neqE _ _ _ _ hne2] at h2

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
  intro HINV hh hx2y2 Pmi_x Gmi_x hx2 hy2
  obtain ⟨Hhs, HinvG, Hinvmh, Hmmh, Hmimhi, Hincl, Hincli, Hmh, Hpi, Hmp⟩ := HINV
  obtain ⟨hun, hs0, hlt⟩ := id Hhs
  obtain ⟨Imm1, Imm2⟩ := id Hmmh
  obtain ⟨Imh1, Imh2, Imh3⟩ := Hmh
  have Pm_y : FMap.get Pm (y1, y2) = none := by
    rw [FMap.domE] at hh
    simpa using hh
  have hs_ch : FMap.get hs ch = none := ch_notdomE_hs hs ch Hhs
  have hs_Sch : FMap.get hs (ch + 1) = none := Sch_notdomE_hs hs ch Hhs
  have mh_Sch : ∀ a, FMap.get mh (a, ch + 1) = none :=
    fun a => Sch_notdomE2_mh hs Pm mh a ch Hmmh Hhs
  have hsne : ∀ h cf, FMap.get hs h = some cf →
      FMap.get (FMap.set (FMap.set hs ch (x2, Known)) (ch + 1) (y2, Known)) h = some cf := by
    intro h cf hh
    have := hlt _ _ hh
    rw [FMap.get_set_neqE _ _ _ _ (show h ≠ ch + 1 by linarith),
      FMap.get_set_neqE _ _ _ _ (show h ≠ ch by linarith), hh]
  have notrng : ∀ hc, FMap.get hs hc = none → ∀ a h a', FMap.get mh (a, h) ≠ some (a', hc) := by
    intro hc hn a h a' hm
    obtain ⟨_, _, _, fy, _, h2, _⟩ := Imm2 _ _ _ _ hm
    rw [hn] at h2
    cases h2
  have nopath : ∀ hc, FMap.get hs hc = none → ∀ p v, build_hpath mh p ≠ some (v, hc) := by
    intro hc hn p v hp
    rcases (build_hpathP _ _ _ _).1 hp with ⟨-, -, rfl⟩ | ⟨p', b, v', h', -, -, hm⟩
    · rw [hs0] at hn
      cases hn
    · exact notrng hc hn _ _ _ hm
  have mhup : ∀ p v h, build_hpath mh p = some (v, h) →
      build_hpath (FMap.set mh (y1, ch + 1) (x1, ch)) p = some (v, h) :=
    fun p v h hp => build_hpath_up mh y1 (ch + 1) x1 ch p v h hp (mh_Sch y1)
  have mhdown : ∀ p v h, build_hpath (FMap.set mh (y1, ch + 1) (x1, ch)) p = some (v, h) →
      build_hpath mh p = some (v, h) :=
    fun p v h hp => build_hpath_down mh y1 (ch + 1) x1 ch p v h (nopath _ hs_Sch) hp
  have Hmp' : ∀ (x y : state), FMap.get Pm x = none → m_p (FMap.set Pm x y) prefixes queries := by
    obtain ⟨c1, c2, c3, c4, c5⟩ := Hmp
    intro x y hx
    refine ⟨c1, c2, ?_, c4, c5⟩
    intro l hl i hi
    obtain ⟨sa, sc, h1, h2⟩ := c3 l hl i hi
    refine ⟨sa, sc, h1, ?_⟩
    have hne : FMap.get prefixes (take (i + 1) l) ≠ none := by
      by_cases hi' : i + 1 < size l
      · obtain ⟨sa', sc', h1', -⟩ := c3 l hl (i + 1) ⟨by omega, hi'⟩
        rw [h1']
        simp
      · have : take (i + 1) l = l := by
          simp only [take, size] at *
          apply List.take_of_length_le
          omega
        rw [this]
        exact (FMap.domE _ _).1 hl
    rw [FMap.get_setE, if_neg]
    · exact h2
    · intro he
      rw [he, hx] at h2
      exact hne h2.symm
  have hy2' : ∀ f h, FMap.get (FMap.set hs ch (x2, Known)) h ≠ some (y2, f) := by
    intro f h
    rw [FMap.get_setE]
    split_ifs
    · simp [hx2y2]
    · exact hy2 f h
  have hsSch' : FMap.get (FMap.set hs ch (x2, Known)) (ch + 1) = none := by
    rw [FMap.get_set_neqE _ _ _ _ (show ch + 1 ≠ ch by simp)]
    exact hs_Sch
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Hmp' _ _ Pm_y⟩
  · rw [show ch + 2 = ch + 1 + 1 by ring]
    exact hs_addh _ _ _ _ (hs_addh hs ch x2 Known Hhs hx2) hy2'
  · refine inv_addm _ _ _ _ HinvG ?_ Gmi_x
    cases hg : FMap.get Gm (y1, y2) with
    | none => rfl
    | some xc =>
      have hp := Hincl (y1, y2) (by rw [hg]; simp)
      rw [hg, Pm_y] at hp
      cases hp
  · exact inv_addm _ _ _ _ Hinvmh (mh_Sch y1) (ch_notdomE2_mh hs Pmi mhi x1 ch Hmimhi Hhs)
  · exact mi_mhi_addh_addmi (FMap.set hs ch (x2, Known)) Pm mh ch x1 x2 (ch + 1) y1 y2
      Known Known (m_mh_addh hs ch Pm mh x2 Known Hhs Hmmh) hy2' (FMap.get_set_sameE _ _ _)
      hsSch'
  · exact m_mh_addh_addm (FMap.set hs ch (x2, Known)) Pmi mhi ch x1 x2 (ch + 1) y1 y2 Known
      Known (m_mh_addh hs ch Pmi mhi x2 Known Hhs Hmimhi) (hs_addh hs ch x2 Known Hhs hx2).1
      (FMap.get_set_sameE _ _ _) hsSch'
  · exact incl_addm _ _ _ _ Hincl
  · exact incl_addm _ _ _ _ Hincli
  · refine ⟨?_, ?_, ?_⟩
    · intro ya hy xa hx hm
      rw [FMap.get_setE] at hm
      split_ifs at hm with hk
      · simp only [Prod.mk.injEq, Option.some.injEq] at hk hm
        obtain ⟨hk1, hk2⟩ := hk
        obtain ⟨hm1, hm2⟩ := hm
        subst ya hy xa hx
        refine ⟨y2, Known, x2, Known, FMap.get_set_sameE _ _ _, ?_, ?_⟩
        · rw [FMap.get_set_neqE _ _ _ _ (show ch ≠ ch + 1 by simp), FMap.get_set_sameE]
        · simp
      · obtain ⟨yc, fy, xc, fx, h1, h2, h3⟩ := Imh1 _ _ _ _ hm
        refine ⟨yc, fy, xc, fx, hsne _ _ h1, hsne _ _ h2, ?_⟩
        cases fx with
        | Known =>
          simp only [if_true] at h3 ⊢
          refine ⟨?_, h3.2⟩
          rw [FMap.get_set_neqE]
          · exact h3.1
          · intro he
            rw [he] at h3
            have := Hincl _ (by rw [h3.1]; simp)
            rw [h3.1, Pm_y] at this
            cases this
        | Unknown =>
          simp only [reduceCtorEq, if_false] at h3 ⊢
          obtain ⟨p, v, h4, h5⟩ := h3
          exact ⟨p, v, h4, mhup _ _ _ h5⟩
    · intro p bn b
      rw [Imh2]
      constructor
      · rintro ⟨v, hx, hy, h1, h2⟩
        refine ⟨v, hx, hy, mhup _ _ _ h1, ?_⟩
        rw [FMap.get_set_neqE]
        · exact h2
        · intro he
          rw [he, mh_Sch] at h2
          cases h2
      · rintro ⟨v, hx, hy, h1, h2⟩
        have h1' := mhdown _ _ _ h1
        refine ⟨v, hx, hy, h1', ?_⟩
        rw [FMap.get_set_neqE] at h2
        · exact h2
        · intro he
          simp only [Prod.mk.injEq] at he
          exact nopath _ hs_Sch p v (he.2 ▸ h1')
    · intro p v p' v' hx h1 h2
      exact Imh3 p v p' v' hx (mhdown _ _ _ h1) (mhdown _ _ _ h2)
  · obtain ⟨Ipi⟩ := Hpi
    refine ⟨fun c p v => ?_⟩
    rw [Ipi]
    constructor
    · rintro ⟨h, h1, h2⟩
      exact ⟨h, mhup _ _ _ h1, hsne _ _ h2⟩
    · rintro ⟨h, h1, h2⟩
      have h1' := mhdown _ _ _ h1
      refine ⟨h, h1', ?_⟩
      have hne1 : h ≠ ch + 1 := by
        intro he
        exact nopath (ch + 1) hs_Sch p v (he ▸ h1')
      have hne2 : h ≠ ch := by
        intro he
        exact nopath ch hs_ch p v (he ▸ h1')
      rwa [FMap.get_set_neqE _ _ _ _ hne1, FMap.get_set_neqE _ _ _ _ hne2] at h2

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
  intro HINV Pm_x Gm_x pi_x2 hs_hx hy2
  obtain ⟨Hhs, HinvG, Hinvmh, Hmmh, Hmimhi, Hincl, Hincli, Hmh, Hpi, Hmp⟩ := HINV
  obtain ⟨hun, hs0, hlt⟩ := id Hhs
  obtain ⟨Imm1, Imm2⟩ := id Hmmh
  obtain ⟨Imi1, Imi2⟩ := id Hmimhi
  obtain ⟨Imh1, Imh2, Imh3⟩ := Hmh
  obtain ⟨Ipi⟩ := Hpi
  have hs_ch : FMap.get hs ch = none := ch_notdomE_hs hs ch Hhs
  have mh_x : FMap.get G1mh (x1, hx) = none :=
    notin_m_notin_mh hs PFm G1mh x1 x2 hx Known Hmmh Pm_x hs_hx
  have hsne : ∀ h cf, FMap.get hs h = some cf →
      FMap.get (FMap.set hs ch (y2, Known)) h = some cf := by
    intro h cf hh
    have := hlt _ _ hh
    rw [FMap.get_set_neqE _ _ _ _ (show h ≠ ch by linarith), hh]
  have nopath_ch : ∀ p v, build_hpath G1mh p ≠ some (v, ch) := by
    intro p v hp
    rcases (build_hpathP _ _ _ _).1 hp with ⟨-, -, he⟩ | ⟨p', b, v', h', -, -, hm⟩
    · rw [he, hs0] at hs_ch
      cases hs_ch
    · obtain ⟨_, _, _, fy, _, h2, _⟩ := Imm2 _ _ _ _ hm
      rw [hs_ch] at h2
      cases h2
  have nopath_hx : ∀ p v, build_hpath G1mh p ≠ some (v, hx) := by
    intro p v hp
    have := (Ipi x2 p v).2 ⟨hx, hp, hs_hx⟩
    rw [pi_x2] at this
    cases this
  have mhup : ∀ p v h, build_hpath G1mh p = some (v, h) →
      build_hpath (FMap.set G1mh (x1, hx) (y1, ch)) p = some (v, h) :=
    fun p v h hp => build_hpath_up G1mh x1 hx y1 ch p v h hp mh_x
  have mhdown : ∀ p v h, build_hpath (FMap.set G1mh (x1, hx) (y1, ch)) p = some (v, h) →
      build_hpath G1mh p = some (v, h) :=
    fun p v h hp => build_hpath_down G1mh x1 hx y1 ch p v h nopath_hx hp
  have Hmp' : ∀ (x y : state), FMap.get PFm x = none →
      m_p (FMap.set PFm x y) prefixes queries := by
    obtain ⟨c1, c2, c3, c4, c5⟩ := Hmp
    intro x y hx
    refine ⟨c1, c2, ?_, c4, c5⟩
    intro l hl i hi
    obtain ⟨sa, sc, h1, h2⟩ := c3 l hl i hi
    refine ⟨sa, sc, h1, ?_⟩
    have hne : FMap.get prefixes (take (i + 1) l) ≠ none := by
      by_cases hi' : i + 1 < size l
      · obtain ⟨sa', sc', h1', -⟩ := c3 l hl (i + 1) ⟨by omega, hi'⟩
        rw [h1']
        simp
      · have : take (i + 1) l = l := by
          simp only [take, size] at *
          apply List.take_of_length_le
          omega
        rw [this]
        exact (FMap.domE _ _).1 hl
    rw [FMap.get_setE, if_neg]
    · exact h2
    · intro he
      rw [he, hx] at h2
      exact hne h2.symm
  refine ⟨hs_addh hs ch y2 Known Hhs hy2, ?_, ?_, ?_, ?_, incl_addm _ _ _ _ Hincl,
    incl_addm _ _ _ _ Hincli, ?_, ?_, Hmp' _ _ Pm_x⟩
  · refine inv_addm _ _ _ _ HinvG Gm_x ?_
    cases hg : FMap.get G1mi (y1, y2) with
    | none => rfl
    | some xc =>
      have hp := Hincli (y1, y2) (by rw [hg]; simp)
      rw [hg] at hp
      obtain ⟨_, fx, _, _, h1, _, _⟩ := Imi1 _ _ _ _ hp
      exact absurd h1 (hy2 _ _)
  · exact inv_addm _ _ _ _ Hinvmh mh_x (ch_notdomE2_mh hs PFmi G1mhi y1 ch Hmimhi Hhs)
  · exact m_mh_addh_addm hs PFm G1mh hx x1 x2 ch y1 y2 Known Known Hmmh hun hs_hx hs_ch
  · exact mi_mhi_addh_addmi hs PFmi G1mhi hx x1 x2 ch y1 y2 Known Known Hmimhi hy2 hs_hx hs_ch
  · refine ⟨?_, ?_, ?_⟩
    · intro xa hx' ya hy hm
      rw [FMap.get_setE] at hm
      split_ifs at hm with hk
      · simp only [Prod.mk.injEq, Option.some.injEq] at hk hm
        obtain ⟨hk1, hk2⟩ := hk
        obtain ⟨hm1, hm2⟩ := hm
        subst xa hx' ya hy
        refine ⟨x2, Known, y2, Known, hsne _ _ hs_hx, FMap.get_set_sameE _ _ _, ?_⟩
        simp
      · obtain ⟨xc, fx, yc, fy, h1, h2, h3⟩ := Imh1 _ _ _ _ hm
        refine ⟨xc, fx, yc, fy, hsne _ _ h1, hsne _ _ h2, ?_⟩
        cases fy with
        | Known =>
          simp only [if_true] at h3 ⊢
          refine ⟨?_, h3.2⟩
          rw [FMap.get_set_neqE]
          · exact h3.1
          · intro he
            rw [he, Gm_x] at h3
            cases h3.1
        | Unknown =>
          simp only [reduceCtorEq, if_false] at h3 ⊢
          obtain ⟨p, v, h4, h5⟩ := h3
          exact ⟨p, v, h4, mhup _ _ _ h5⟩
    · intro p bn b
      rw [Imh2]
      constructor
      · rintro ⟨v, hi, hf, h1, h2⟩
        refine ⟨v, hi, hf, mhup _ _ _ h1, ?_⟩
        rw [FMap.get_set_neqE]
        · exact h2
        · intro he
          rw [he, mh_x] at h2
          cases h2
      · rintro ⟨v, hi, hf, h1, h2⟩
        have h1' := mhdown _ _ _ h1
        refine ⟨v, hi, hf, h1', ?_⟩
        rw [FMap.get_set_neqE] at h2
        · exact h2
        · intro he
          simp only [Prod.mk.injEq] at he
          exact nopath_hx p v (he.2 ▸ h1')
    · intro p v p' v' h0 h1 h2
      exact Imh3 p v p' v' h0 (mhdown _ _ _ h1) (mhdown _ _ _ h2)
  · refine ⟨fun c p v => ?_⟩
    rw [Ipi]
    constructor
    · rintro ⟨h, h1, h2⟩
      exact ⟨h, mhup _ _ _ h1, hsne _ _ h2⟩
    · rintro ⟨h, h1, h2⟩
      have h1' := mhdown _ _ _ h1
      refine ⟨h, h1', ?_⟩
      have hne : h ≠ ch := by
        intro he
        exact nopath_ch p v (he ▸ h1')
      rwa [FMap.get_set_neqE _ _ _ _ hne] at h2

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
  intro HINV hh Pmi_x Gmi_x hs_hx hy2
  obtain ⟨Hhs, HinvG, Hinvmh, Hmmh, Hmimhi, Hincl, Hincli, Hmh, Hpi, Hmp⟩ := HINV
  obtain ⟨hun, hs0, hlt⟩ := id Hhs
  obtain ⟨Imm1, Imm2⟩ := id Hmmh
  obtain ⟨Imh1, Imh2, Imh3⟩ := Hmh
  obtain ⟨Ipi⟩ := Hpi
  have Pm_y : FMap.get PFm (y1, y2) = none := by
    rw [FMap.domE] at hh
    simpa using hh
  have hs_ch : FMap.get hs ch = none := ch_notdomE_hs hs ch Hhs
  have mh_ch : ∀ a, FMap.get G1mh (a, ch) = none :=
    fun a => ch_notdomE2_mh hs PFm G1mh a ch Hmmh Hhs
  have hsne : ∀ h cf, FMap.get hs h = some cf →
      FMap.get (FMap.set hs ch (y2, Known)) h = some cf := by
    intro h cf hh
    have := hlt _ _ hh
    rw [FMap.get_set_neqE _ _ _ _ (show h ≠ ch by linarith), hh]
  have nopath_ch : ∀ p v, build_hpath G1mh p ≠ some (v, ch) := by
    intro p v hp
    rcases (build_hpathP _ _ _ _).1 hp with ⟨-, -, he⟩ | ⟨p', b, v', h', -, -, hm⟩
    · rw [he, hs0] at hs_ch
      cases hs_ch
    · obtain ⟨_, _, _, fy, _, h2, _⟩ := Imm2 _ _ _ _ hm
      rw [hs_ch] at h2
      cases h2
  have mhup : ∀ p v h, build_hpath G1mh p = some (v, h) →
      build_hpath (FMap.set G1mh (y1, ch) (x1, hx)) p = some (v, h) :=
    fun p v h hp => build_hpath_up G1mh y1 ch x1 hx p v h hp (mh_ch y1)
  have mhdown : ∀ p v h, build_hpath (FMap.set G1mh (y1, ch) (x1, hx)) p = some (v, h) →
      build_hpath G1mh p = some (v, h) :=
    fun p v h hp => build_hpath_down G1mh y1 ch x1 hx p v h nopath_ch hp
  have Hmp' : ∀ (x y : state), FMap.get PFm x = none →
      m_p (FMap.set PFm x y) prefixes queries := by
    obtain ⟨c1, c2, c3, c4, c5⟩ := Hmp
    intro x y hx
    refine ⟨c1, c2, ?_, c4, c5⟩
    intro l hl i hi
    obtain ⟨sa, sc, h1, h2⟩ := c3 l hl i hi
    refine ⟨sa, sc, h1, ?_⟩
    have hne : FMap.get prefixes (take (i + 1) l) ≠ none := by
      by_cases hi' : i + 1 < size l
      · obtain ⟨sa', sc', h1', -⟩ := c3 l hl (i + 1) ⟨by omega, hi'⟩
        rw [h1']
        simp
      · have : take (i + 1) l = l := by
          simp only [take, size] at *
          apply List.take_of_length_le
          omega
        rw [this]
        exact (FMap.domE _ _).1 hl
    rw [FMap.get_setE, if_neg]
    · exact h2
    · intro he
      rw [he, hx] at h2
      exact hne h2.symm
  refine ⟨hs_addh hs ch y2 Known Hhs hy2, ?_, ?_, ?_, ?_, incl_addm _ _ _ _ Hincl,
    incl_addm _ _ _ _ Hincli, ?_, ?_, Hmp' _ _ Pm_y⟩
  · refine inv_addm _ _ _ _ HinvG ?_ Gmi_x
    cases hg : FMap.get G1m (y1, y2) with
    | none => rfl
    | some xc =>
      have hp := Hincl (y1, y2) (by rw [hg]; simp)
      rw [hg, Pm_y] at hp
      cases hp
  · exact inv_addm _ _ _ _ Hinvmh (mh_ch y1)
      (notin_m_notin_mh hs PFmi G1mhi x1 x2 hx Known Hmimhi Pmi_x hs_hx)
  · exact mi_mhi_addh_addmi hs PFm G1mh hx x1 x2 ch y1 y2 Known Known Hmmh hy2 hs_hx hs_ch
  · exact m_mh_addh_addm hs PFmi G1mhi hx x1 x2 ch y1 y2 Known Known Hmimhi hun hs_hx hs_ch
  · refine ⟨?_, ?_, ?_⟩
    · intro ya hy xa hx' hm
      rw [FMap.get_setE] at hm
      split_ifs at hm with hk
      · simp only [Prod.mk.injEq, Option.some.injEq] at hk hm
        obtain ⟨hk1, hk2⟩ := hk
        obtain ⟨hm1, hm2⟩ := hm
        subst ya hy xa hx'
        refine ⟨y2, Known, x2, Known, FMap.get_set_sameE _ _ _, hsne _ _ hs_hx, ?_⟩
        simp
      · obtain ⟨yc, fy, xc, fx, h1, h2, h3⟩ := Imh1 _ _ _ _ hm
        refine ⟨yc, fy, xc, fx, hsne _ _ h1, hsne _ _ h2, ?_⟩
        cases fx with
        | Known =>
          simp only [if_true] at h3 ⊢
          refine ⟨?_, h3.2⟩
          rw [FMap.get_set_neqE]
          · exact h3.1
          · intro he
            rw [he] at h3
            have := Hincl _ (by rw [h3.1]; simp)
            rw [h3.1, Pm_y] at this
            cases this
        | Unknown =>
          simp only [reduceCtorEq, if_false] at h3 ⊢
          obtain ⟨p, v, h4, h5⟩ := h3
          exact ⟨p, v, h4, mhup _ _ _ h5⟩
    · intro p bn b
      rw [Imh2]
      constructor
      · rintro ⟨v, hi, hf, h1, h2⟩
        refine ⟨v, hi, hf, mhup _ _ _ h1, ?_⟩
        rw [FMap.get_set_neqE]
        · exact h2
        · intro he
          rw [he, mh_ch] at h2
          cases h2
      · rintro ⟨v, hi, hf, h1, h2⟩
        have h1' := mhdown _ _ _ h1
        refine ⟨v, hi, hf, h1', ?_⟩
        rw [FMap.get_set_neqE] at h2
        · exact h2
        · intro he
          simp only [Prod.mk.injEq] at he
          exact nopath_ch p v (he.2 ▸ h1')
    · intro p v p' v' h0 h1 h2
      exact Imh3 p v p' v' h0 (mhdown _ _ _ h1) (mhdown _ _ _ h2)
  · refine ⟨fun c p v => ?_⟩
    rw [Ipi]
    constructor
    · rintro ⟨h, h1, h2⟩
      exact ⟨h, mhup _ _ _ h1, hsne _ _ h2⟩
    · rintro ⟨h, h1, h2⟩
      have h1' := mhdown _ _ _ h1
      refine ⟨h, h1', ?_⟩
      have hne : h ≠ ch := by
        intro he
        exact nopath_ch p v (he ▸ h1')
      rwa [FMap.get_set_neqE _ _ _ _ hne] at h2

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
  intro HINV Pm_x Gm_x mh_x hs_hx hs_hy pi_xc
  obtain ⟨Hhs, HinvG, Hinvmh, Hmmh, Hmimhi, Hincl, Hincli, Hmh, Hpi, Hmp⟩ := HINV
  obtain ⟨hun, hs0, hlt⟩ := id Hhs
  obtain ⟨Imh1, Imh2, Imh3⟩ := id Hmh
  obtain ⟨Ipi⟩ := Hpi
  obtain ⟨IG⟩ := id HinvG
  obtain ⟨Imhi⟩ := id Hinvmh
  obtain ⟨IP⟩ := inv_mh_inv_Pm hs Pm Pmi mh mhi Hmmh Hmimhi Hinvmh
  have hxor : ∀ a b : block, a +^ (a +^ b) = b := by
    intro a b
    apply List.Vector.ext
    intro i
    simp [BitWord.xorw, List.Vector.get_map₂]
  have hxy : hx ≠ hy := by
    intro he
    rw [he, hs_hy] at hs_hx
    cases hs_hx
  have Pmi_y : FMap.get Pmi (ya, yc) = some (xa, xc) := (IP _ _).1 Pm_x
  have path_hy : build_hpath mh (rcons p (b +^ xa)) = some (ya, hy) := by
    obtain ⟨h, hp, hsh⟩ := (Ipi xc p b).1 pi_xc
    have := hun _ _ _ _ hsh hs_hx rfl
    subst this
    refine (build_hpath_prefix mh p _ ya hy).2 ⟨b, h, hp, ?_⟩
    rw [hxor]
    exact mh_x
  refine ⟨?_, ?_, Hinvmh, m_mh_updh Unknown hs Pm mh yc hy Known Hmmh hs_hy,
    m_mh_updh Unknown hs Pmi mhi yc hy Known Hmimhi hs_hy, ?_, ?_, ?_, ?_, Hmp⟩
  · refine hs_updh hs ch Unknown hy yc Known Hhs ?_ hs_hy
    intro he
    rw [← he, hs0] at hs_hy
    cases hs_hy
  · refine inv_addm _ _ _ _ HinvG Gm_x ?_
    cases hg : FMap.get Gmi (ya, yc) with
    | none => rfl
    | some z =>
      have hp := Hincli (ya, yc) (by rw [hg]; simp)
      rw [hg, Pmi_y] at hp
      cases hp
      rw [← IG] at hg
      rw [hg] at Gm_x
      cases Gm_x
  · intro z hz
    rw [FMap.get_setE] at hz ⊢
    split_ifs with he
    · rw [he]
      exact Pm_x
    · rw [if_neg he] at hz
      exact Hincl z hz
  · intro z hz
    rw [FMap.get_setE] at hz ⊢
    split_ifs with he
    · rw [he]
      exact Pmi_y
    · rw [if_neg he] at hz
      exact Hincli z hz
  · refine ⟨?_, Imh2, Imh3⟩
    intro xa' hx' ya' hy' hm
    by_cases hk : (xa', hx') = (xa, hx)
    · simp only [Prod.mk.injEq] at hk
      obtain ⟨hk1, hk2⟩ := hk
      subst xa' hx'
      rw [mh_x] at hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨hm1, hm2⟩ := hm
      subst ya' hy'
      refine ⟨xc, Known, yc, Known, ?_, FMap.get_set_sameE _ _ _, ?_⟩
      · rw [FMap.get_set_neqE _ _ _ _ hxy]
        exact hs_hx
      · simp
    obtain ⟨xc', fx', yc', fy', h1, h2, h3⟩ := Imh1 _ _ _ _ hm
    by_cases hyy : hy' = hy
    · subst hyy
      rw [hs_hy] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      simp only [reduceCtorEq, if_false] at h3
      obtain ⟨p', b', h4, h5⟩ := h3
      have path' : build_hpath mh (rcons p' (b' +^ xa')) = some (ya', hy') := by
        refine (build_hpath_prefix mh p' _ ya' hy').2 ⟨b', hx', h5, ?_⟩
        rw [hxor]
        exact hm
      obtain ⟨-, rfl⟩ := Imh3 _ _ _ _ _ path_hy path'
      have e1 := (Imhi _ _).1 hm
      rw [(Imhi _ _).1 mh_x] at e1
      exact absurd (Option.some.inj e1).symm hk
    · have hk' : (xa', xc') ≠ (xa, xc) := by
        intro he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact hk (by rw [hun _ _ _ _ h1 hs_hx rfl])
      by_cases hxy' : hx' = hy
      · subst hxy'
        rw [hs_hy] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        refine ⟨_, Known, yc', fy', FMap.get_set_sameE _ _ _, ?_, ?_⟩
        · rw [FMap.get_set_neqE _ _ _ _ hyy]
          exact h2
        · cases fy' with
          | Known => simp at h3
          | Unknown => simpa using h3
      · refine ⟨xc', fx', yc', fy', ?_, ?_, ?_⟩
        · rw [FMap.get_set_neqE _ _ _ _ hxy']
          exact h1
        · rw [FMap.get_set_neqE _ _ _ _ hyy]
          exact h2
        · cases fy' with
          | Known =>
            simp only [if_true] at h3 ⊢
            exact ⟨by rw [FMap.get_set_neqE _ _ _ _ hk']; exact h3.1, h3.2⟩
          | Unknown => simpa using h3
  · refine ⟨fun c p' v => ?_⟩
    rw [FMap.get_setE]
    by_cases hc : c = yc
    · subst hc
      rw [if_pos rfl]
      constructor
      · intro he
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨hy, path_hy, FMap.get_set_sameE _ _ _⟩
      · rintro ⟨h, h1, h2⟩
        by_cases hhy : h = hy
        · subst hhy
          obtain ⟨rfl, rfl⟩ := Imh3 _ _ _ _ _ path_hy h1
          rfl
        · rw [FMap.get_set_neqE _ _ _ _ hhy] at h2
          exact absurd (hun _ _ _ _ h2 hs_hy rfl) hhy
    · rw [if_neg hc, Ipi]
      constructor
      · rintro ⟨h, h1, h2⟩
        refine ⟨h, h1, ?_⟩
        have hhy : h ≠ hy := by
          intro he
          rw [he, hs_hy] at h2
          cases h2
        rw [FMap.get_set_neqE _ _ _ _ hhy]
        exact h2
      · rintro ⟨h, h1, h2⟩
        refine ⟨h, h1, ?_⟩
        have hhy : h ≠ hy := by
          intro he
          rw [he, FMap.get_set_sameE] at h2
          simp only [Option.some.injEq, Prod.mk.injEq] at h2
          exact hc h2.1.symm
        rw [FMap.get_set_neqE _ _ _ _ hhy] at h2
        exact h2

theorem m_mh_None (hs0 : handles) (PFm : smap) (G1mh : hsmap) (hx2 : handle) (x2 : capacity)
    (k : flag) (x1 : block) :
    m_mh hs0 PFm G1mh → FMap.get hs0 hx2 = some (x2, k) → FMap.get PFm (x1, x2) = none →
    FMap.get G1mh (x1, hx2) = none := by
  rintro ⟨_, h2⟩ hh hP
  cases hg : FMap.get G1mh (x1, hx2) with
  | none => rfl
  | some yh =>
    obtain ⟨xc, fx, yc, fy, h1, -, h3⟩ := h2 x1 hx2 yh.1 yh.2 hg
    rw [hh] at h1
    cases h1
    rw [hP] at h3
    cases h3

theorem build_hpath_None (G1mh : hsmap) (p : List block) :
    p.foldl (step_hpath G1mh) none = none := by
  induction p with
  | nil => rfl
  | cons b p ih => simpa [step_hpath] using ih

theorem build_hpath_upd_ch (ha ch : handle) (mh : hsmap) (xa ya : block) (p : List block)
    (v : block) (hx : handle) :
    0 ≠ ch → ha ≠ ch →
    (∀ xa xb ha hb, FMap.get mh (xa, ha) = some (xb, hb) → ha ≠ ch ∧ hb ≠ ch) →
    build_hpath (FMap.set mh (xa, ha) (ya, ch)) p = some (v, hx) →
    if hx = ch then
      ∃ p0 x, build_hpath mh p0 = some (x, ha) ∧ p = rcons p0 (x +^ xa) ∧ v = ya
    else build_hpath mh p = some (v, hx) := by
  intro Hch0 Hha Hch hp
  have hxor : ∀ a b : block, a +^ (a +^ b) = b := by
    intro a b
    apply List.Vector.ext
    intro i
    simp [BitWord.xorw, List.Vector.get_map₂]
  induction p using List.reverseRecOn generalizing v hx with
  | nil =>
    simp only [build_hpath, List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    rw [if_neg Hch0]
    rfl
  | append_singleton p b ih =>
    obtain ⟨v', h', hb, hm⟩ := (build_hpath_prefix _ p b v hx).1 hp
    have ih' := ih v' h' hb
    by_cases hh' : h' = ch
    · subst hh'
      rw [FMap.get_setE, if_neg (by simp [Ne.symm Hha])] at hm
      exact absurd rfl (Hch _ _ _ _ hm).1
    rw [if_neg hh'] at ih'
    rw [FMap.get_setE] at hm
    split_ifs at hm with hk
    · simp only [Prod.mk.injEq, Option.some.injEq] at hk hm
      obtain ⟨hk1, rfl⟩ := hk
      obtain ⟨rfl, rfl⟩ := hm
      rw [if_pos rfl]
      refine ⟨p, v', ih', ?_, rfl⟩
      rw [← hk1, hxor]
      rfl
    · have hxc : hx ≠ ch := (Hch _ _ _ _ hm).2
      rw [if_neg hxc]
      exact (build_hpath_prefix mh p b v hx).2 ⟨v', h', ih', hm⟩

theorem build_hpath_up_None (G1mh : hsmap) (bi1 bi2 bi : hstate) (p : List block) :
    FMap.get G1mh bi1 = none → build_hpath G1mh p = some bi →
    build_hpath (FMap.set G1mh bi1 bi2) p = some bi := by
  intro hn hp
  induction p using List.reverseRecOn generalizing bi with
  | nil => exact hp
  | append_singleton p b ih =>
    obtain ⟨za, hz⟩ := bi
    obtain ⟨v', h', hb, hm⟩ := (build_hpath_prefix G1mh p b za hz).1 hp
    refine (build_hpath_prefix _ p b za hz).2 ⟨v', h', ih (v', h') hb, ?_⟩
    rw [FMap.get_setE, if_neg]
    · exact hm
    · intro he
      rw [he, hn] at hm
      cases hm

theorem build_hpath_down_None (h ch : handle) (mh : hsmap) (xa : block) (ha : handle)
    (ya a : block) (p : List block) :
    h ≠ ch → ha ≠ ch → (∀ ya, FMap.get mh (ya, ch) = none) →
    build_hpath (FMap.set mh (xa, ha) (ya, ch)) p = some (a, h) →
    build_hpath mh p = some (a, h) := by
  intro Hh Hha Hmh hp
  have aux : ∀ (q : List block) (a : block) (h : handle),
      build_hpath (FMap.set mh (xa, ha) (ya, ch)) q = some (a, h) →
      h = ch ∨ build_hpath mh q = some (a, h) := by
    intro q
    induction q using List.reverseRecOn with
    | nil => intro a h hq; exact Or.inr hq
    | append_singleton q b ih =>
      intro a h hq
      obtain ⟨v', h', hb, hm⟩ := (build_hpath_prefix _ q b a h).1 hq
      rcases ih v' h' hb with rfl | hb'
      · rw [FMap.get_setE, if_neg (by simp [Ne.symm Hha]), Hmh] at hm
        cases hm
      · rw [FMap.get_setE] at hm
        split_ifs at hm
        · simp only [Option.some.injEq, Prod.mk.injEq] at hm
          exact Or.inl hm.2.symm
        · exact Or.inr ((build_hpath_prefix mh q b a h).2 ⟨v', h', hb', hm⟩)
  exact (aux p a h hp).resolve_left Hh

theorem build_hpath_upd_ch_iff (ha ch : handle) (mh : hsmap) (xa ya : block) (p : List block)
    (v : block) (hx : handle) :
    FMap.get mh (xa, ha) = none → 0 ≠ ch → ha ≠ ch →
    (∀ xa xb ha hb, FMap.get mh (xa, ha) = some (xb, hb) → ha ≠ ch ∧ hb ≠ ch) →
    (build_hpath (FMap.set mh (xa, ha) (ya, ch)) p = some (v, hx) ↔
      if hx = ch then
        ∃ p0 x, build_hpath mh p0 = some (x, ha) ∧ p = rcons p0 (x +^ xa) ∧ v = ya
      else build_hpath mh p = some (v, hx)) := by
  intro Ha Hch0 Hha Hch
  have hxor : ∀ a b : block, a +^ (a +^ b) = b := by
    intro a b
    apply List.Vector.ext
    intro i
    simp [BitWord.xorw, List.Vector.get_map₂]
  refine ⟨build_hpath_upd_ch ha ch mh xa ya p v hx Hch0 Hha Hch, ?_⟩
  split_ifs with hxc
  · rintro ⟨p0, x, hp0, rfl, rfl⟩
    subst hxc
    refine (build_hpath_prefix _ p0 _ v hx).2
      ⟨x, ha, build_hpath_up_None mh (xa, ha) (v, hx) (x, ha) p0 Ha hp0, ?_⟩
    rw [hxor]
    exact FMap.get_set_sameE _ _ _
  · exact build_hpath_up_None mh (xa, ha) (ya, ch) (v, hx) p Ha

theorem lemma4 (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (i : ℤ)
    (p : List block) (sa : block) (sc : capacity) (h : handle) (f : flag) :
    INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries → 0 ≤ i ∧ i < size p →
    FMap.dom prefixes (take (i + 1) p) → FMap.get prefixes (take i p) = some (sa, sc) →
    build_hpath mh (take i p) = some (sa, h) →
    FMap.get ro (take (i + 1) p) = some (oget (FMap.get prefixes (take (i + 1) p))).1 →
    FMap.get hs h = some (sc, f) → FMap.dom mh (sa +^ nth default p i, h) := by
  rintro ⟨-, -, -, -, -, -, -, ⟨-, Iro, -⟩, -, -⟩ ⟨hi0, hi⟩ - - hb hro -
  have hrc : take (i + 1) p = rcons (take i p) (nth default p i) := by
    have hlt : i.toNat < p.length := by simp only [size] at hi; omega
    simp only [take, rcons, nth, if_pos hi0, show (i + 1).toNat = i.toNat + 1 by omega,
      List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
      List.getD_eq_getElem?_getD, Option.getD_some]
  rw [hrc] at hro
  obtain ⟨v, hx, hy, hb', hm⟩ := (Iro _ _ _).1 hro
  rw [hb] at hb'
  simp only [Option.some.injEq, Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl⟩ := hb'
  rw [FMap.domE, hm]
  simp

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

theorem fi_none_inv (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (xa y1 : block)
    (xc y2 : capacity)
    (hI : INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries)
    (hP : ¬ FMap.dom Pmi (xa, xc)) (hG : ¬ FMap.dom Gmi (xa, xc))
    (hnone : ∀ f h, FMap.get hs h ≠ some (xc, f))
    (hcol : hinv (FMap.set hs ch (xc, Known)) y2 = none) :
    INV_CF_G1 (FMap.set (FMap.set hs ch (xc, Known)) (ch + 1) (y2, Known)) (ch + 1 + 1)
      (FMap.set Pm (y1, y2) (xa, xc)) (FMap.set Pmi (xa, xc) (y1, y2))
      (FMap.set Gm (y1, y2) (xa, xc)) (FMap.set Gmi (xa, xc) (y1, y2))
      (FMap.set mh (y1, ch + 1) (xa, ch)) (FMap.set mhi (xa, ch) (y1, ch + 1))
      ro pi prefixes queries := by
  have hy := hinvP (FMap.set hs ch (xc, Known)) y2
  rw [if_pos hcol] at hy
  have hxy : xc ≠ y2 := by
    rintro rfl
    exact hy ch Known (FMap.get_set_sameE _ _ _)
  have hy2 : ∀ f h, FMap.get hs h ≠ some (y2, f) := by
    intro f h hh
    by_cases e : h = ch
    · subst e
      rw [ch_notdomE_hs _ _ hI.1] at hh
      cases hh
    · exact hy h f (by rw [FMap.get_set_neqE _ _ _ _ e]; exact hh)
  have hPm : ¬ FMap.dom Pm (y1, y2) := by
    rw [FMap.domE]
    intro hd
    obtain ⟨⟨a, b⟩, hab⟩ := Option.ne_none_iff_exists'.mp hd
    obtain ⟨hx, fx, -, -, h1, -, -⟩ := hI.4.1 _ _ _ _ hab
    exact hy2 _ _ h1
  rw [show ch + 1 + 1 = ch + 2 by ring]
  exact lemma1' hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries xa xc y1 y2 hI hPm hxy
    (by simpa [FMap.domE] using hP) (by simpa [FMap.domE] using hG) hnone hy2

theorem fi_known_inv (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (xa y1 : block)
    (xc y2 : capacity) (hx : handle)
    (hI : INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries)
    (hP : ¬ FMap.dom Pmi (xa, xc)) (hG : ¬ FMap.dom Gmi (xa, xc))
    (hhx : FMap.get hs hx = some (xc, Known))
    (hcol : hinv hs y2 = none) :
    INV_CF_G1 (FMap.set hs ch (y2, Known)) (ch + 1)
      (FMap.set Pm (y1, y2) (xa, xc)) (FMap.set Pmi (xa, xc) (y1, y2))
      (FMap.set Gm (y1, y2) (xa, xc)) (FMap.set Gmi (xa, xc) (y1, y2))
      (FMap.set mh (y1, ch) (xa, hx)) (FMap.set mhi (xa, hx) (y1, ch))
      ro pi prefixes queries := by
  have hy := hinvP hs y2
  rw [if_pos hcol] at hy
  have hy2 : ∀ f h, FMap.get hs h ≠ some (y2, f) := fun f h => hy h f
  have hPm : ¬ FMap.dom Pm (y1, y2) := by
    rw [FMap.domE]
    intro hd
    obtain ⟨⟨a, b⟩, hab⟩ := Option.ne_none_iff_exists'.mp hd
    obtain ⟨hx, fx, -, -, h1, -, -⟩ := hI.4.1 _ _ _ _ hab
    exact hy2 _ _ h1
  exact lemma2' hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries xa xc y1 y2 hx hI hPm
    (by simpa [FMap.domE] using hP) (by simpa [FMap.domE] using hG) hhx hy2

theorem fi_bext (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (xa : block)
    (xc : capacity)
    (hI : INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries)
    (hP : FMap.dom Pmi (xa, xc)) (hG : ¬ FMap.dom Gmi (xa, xc)) :
    FMap.rng hs (xc, Unknown) := by
  obtain ⟨⟨ya, yc⟩, hPy⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hP)
  obtain ⟨hx, fx, hy, fy, hhx, hhy, hmhi⟩ := hI.5.1 _ _ _ _ hPy
  have hmh := (hI.3.1 _ _).mpr hmhi
  obtain ⟨xc', fx', yc', fy', h1, h2, h3⟩ := hI.8.1 _ _ _ _ hmh
  rw [hhy] at h1
  rw [hhx] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨rfl, rfl⟩ := h2
  cases fx with
  | Unknown => exact ⟨hx, hhx⟩
  | Known =>
    rw [if_pos rfl] at h3
    have := (hI.2.1 _ _).mp h3.1
    exact absurd ((FMap.domE _ _).mpr (by rw [this]; simp)) hG

set_option maxHeartbeats 4000000 in
-- the inlined oracles' wp goals are large
/-- The oracle step of EC's `eq_fi`: the `call (: …)` between `PF.fi` and `G1.S.fi`.  The
postcondition also keeps `={glob C}` and `[] \in C.queries{2}` (not modified by the oracles). -/
theorem PF_fi_S_fi :
    prhlProc (sig₁ := procsig (state) -> state) (sig₂ := procsig (state) -> state)
      (fun a₁ g₁ a₂ g₂ => G1.bcol.get g₂ = false ∧ G1.bext.get g₂ = false ∧ a₁ = a₂ ∧
        eq_glob_C g₁ g₂ ∧ INV_CF_G1_12 g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi state (List block) block PF).procedure
      (Indifferentiability.DPRIMITIVE.fi state (List block) block G1.S).procedure
      (fun r₁ g₁ r₂ g₂ => eq_glob_C g₁ g₂ ∧ FMap.dom (C.queries.get g₂) [] ∧
        (G1.bcol.get g₂ = false → G1.bext.get g₂ = false → r₁ = r₂ ∧ INV_CF_G1_12 g₁ g₂)) := by
  unfold PF G1.S
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §G1.bcol{2} = false ∧ §G1.bext{2} = false ∧
      eq_glob_C §allGlobals{1} §allGlobals{2} ∧ INV_CF_G1_12 §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨hc, hb, rfl, hC, hI⟩
    exact ⟨rfl, hc, hb, hC, hI⟩
  · equiv_if{1}
    case «then» =>
      equiv_if{2}
      case «then» =>
        stmt_wp
        equiv_rnd
        equiv_rnd
        stmt_wp
        equiv_skip
        rintro g₁ g₂ x0 _ ⟨⟨⟨rfl, hc, hb, hC, hI⟩, hP⟩, hG⟩ y1 - y2 -
        obtain ⟨xa, xc⟩ := x0
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hP hG
        unfold INV_CF_G1_12 at hI
        have hq : FMap.dom (C.queries.get g₂) [] := by rw [FMap.domE, hI.10.2]; simp
        rcases hgf : getflag (FRO.m.get g₂) xc with _ | f
        · have hnone := (getflagP_none _ _).1 hgf
          have hK : ¬ FMap.rng (FRO.m.get g₂) (xc, Known) := fun ⟨h, hh⟩ => hnone _ h hh
          have hU : ¬ FMap.rng (FRO.m.get g₂) (xc, Unknown) := fun ⟨h, hh⟩ => hnone _ h hh
          simp only [hK, hU, decide_false, Bool.not_false, if_true, Bool.or_false]
          have hx2 : hinvK (FMap.set (FRO.m.get g₂) (G1.chandle.get g₂) (xc, Known)) xc =
              some (G1.chandle.get g₂) :=
            huniq_hinvK_h _ _ _ (huniq_addh _ _ _ _ hI.1.1 hnone) (FMap.get_set_sameE _ _ _)
          have hmhi : ¬ FMap.dom (G1.mhi.get g₂) (xa, G1.chandle.get g₂) := by
            rw [FMap.domE, notin_hs_notdomE2_mh _ _ _ _ _ hI.5 (ch_notdomE_hs _ _ hI.1)]
            simp
          have hx2' : oget (hinvK (FMap.set (FRO.m.get g₂) (G1.chandle.get g₂) (xc, Known)) xc) =
              G1.chandle.get g₂ := by rw [hx2]; rfl
          simp only [hx2', hmhi, false_and, decide_false, Bool.false_eq_true, if_false]
          simp only [eq_glob_C, INV_CF_G1_12] at hC ⊢
          simp_reads
          refine ⟨hC, hq, fun hcol _ => ⟨by simp [oget, FMap.get_set_sameE], ?_⟩⟩
          simp only [hc, Bool.false_or, decide_eq_false_iff_not, not_not] at hcol
          exact fi_none_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI hP hG hnone hcol
        · have hsome := (getflagP_some _ _ f hI.1.1).1 hgf
          cases f with
          | Known =>
            obtain ⟨hx, hhx⟩ := id hsome
            have hU : ¬ FMap.rng (FRO.m.get g₂) (xc, Unknown) := fun h => by
              have := (getflagP_some _ _ Unknown hI.1.1).2 h
              rw [hgf] at this
              cases this
            simp only [hsome, hU, decide_true, decide_false, Bool.not_true, Bool.false_eq_true,
              if_false, Bool.or_false]
            have hx2' : oget (hinvK (FRO.m.get g₂) xc) = hx := by
              rw [huniq_hinvK_h _ _ _ hI.1.1 hhx]; rfl
            have hPn : FMap.get (PF.mi.get g₁) (xa, xc) = none := by simpa [FMap.domE] using hP
            have hmhi : ¬ FMap.dom (G1.mhi.get g₂) (xa, hx) := by
              rw [FMap.domE, notin_m_notin_mh _ _ _ _ _ _ _ hI.5 hPn hhx]
              simp
            simp only [hx2', hmhi, false_and, decide_false, Bool.false_eq_true, if_false]
            simp only [eq_glob_C, INV_CF_G1_12] at hC ⊢
            simp_reads
            refine ⟨hC, hq, fun hcol _ => ⟨by simp [oget, FMap.get_set_sameE], ?_⟩⟩
            simp only [hc, Bool.false_or, decide_eq_false_iff_not, not_not] at hcol
            exact fi_known_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI hP hG hhx hcol
          | Unknown =>
            have hK : ¬ FMap.rng (FRO.m.get g₂) (xc, Known) := fun h => by
              have := (getflagP_some _ _ Known hI.1.1).2 h
              rw [hgf] at this
              cases this
            simp only [hsome, hK, decide_true, decide_false, Bool.or_true]
            simp only [eq_glob_C] at hC ⊢
            simp_reads
            simp only [ite_self]
            exact ⟨hC, hq, fun _ h => absurd h (by simp)⟩
      case «else» =>
        refine prhlStmt_pre prhlStmt_false ?_
        rintro σ₁ σ₂ ⟨⟨⟨hx, -, -, -, hI⟩, hP⟩, hG⟩
        simp only [Bool.not_eq_false', Bool.not_eq_true', decide_eq_true_eq,
          decide_eq_false_iff_not] at hP hG
        rw [hx] at hP
        unfold INV_CF_G1_12 at hI
        have hd := (FMap.domE _ _).mp hG
        exact hP ((FMap.domE _ _).mpr (by rw [hI.7 _ hd]; exact hd))
    case «else» =>
      equiv_if{2}
      case «then» =>
        stmt_wp
        stmt_wp{2} 1
        stmt_wp{2} 1
        stmt_wp
        equiv_skip
        rintro g₁ g₂ x0 _ ⟨⟨⟨rfl, hc, hb, hC, hI⟩, hP⟩, hG⟩
        obtain ⟨xa, xc⟩ := x0
        simp only [Bool.not_eq_false', Bool.not_eq_true', decide_eq_true_eq,
          decide_eq_false_iff_not] at hP hG
        unfold INV_CF_G1_12 at hI
        have hq : FMap.dom (C.queries.get g₂) [] := by rw [FMap.domE, hI.10.2]; simp
        have hU := fi_bext _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI hP hG
        refine ⟨(is_lossless_iff_expected bdistr).mp BitWord.dunifin_ll, fun _ _ =>
          ⟨(is_lossless_iff_expected cdistr).mp BitWord.dunifin_ll, fun _ _ => ?_⟩⟩
        simp only [hU, decide_true, Bool.or_true]
        simp only [eq_glob_C] at hC ⊢
        simp_reads
        simp only [ite_self]
        exact ⟨hC, hq, fun _ h => absurd h (by simp)⟩
      case «else» =>
        stmt_wp
        equiv_skip
        rintro g₁ g₂ x0 _ ⟨⟨⟨rfl, hc, hb, hC, hI⟩, hP⟩, hG⟩
        simp only [Bool.not_eq_false', decide_eq_true_eq] at hP hG
        unfold INV_CF_G1_12 at hI
        have hq : FMap.dom (C.queries.get g₂) [] := by rw [FMap.domE, hI.10.2]; simp
        refine ⟨hC, hq, fun _ _ => ⟨?_, hI⟩⟩
        rw [hI.7 _ (by simpa [FMap.domE] using hG)]

omit [SLCommon.Params] in
/-- `rcons` is injective in both arguments (EC's `rconssI`/`rconsIs`). -/
theorem rcons_inj_both {α : Type} {p q : List α} {a b : α} :
    rcons p a = rcons q b → p = q ∧ a = b := by
  intro h
  have := List.append_inj' h rfl
  simpa using this

/-- Block xor cancels on the left: `a +^ (a +^ b) = b`. -/
theorem xorw_cancel_left (a b : block) : a +^ (a +^ b) = b := by
  apply List.Vector.ext
  intro i
  simp [BitWord.xorw, List.Vector.get_map₂]

/-- In the path case of `eq_f` the query `rcons p0 (v0 +^ x1)` is fresh for `ro`. -/
theorem f_path_ro_none (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (x1 : block)
    (x2 : capacity) (hx2 : handle) (p0 : List block) (v0 : block) :
    INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries →
    FMap.get Pm (x1, x2) = none →
    FMap.get hs hx2 = some (x2, Known) → build_hpath mh p0 = some (v0, hx2) →
    FMap.get ro (rcons p0 (v0 +^ x1)) = none := by
  rintro ⟨-, -, -, Hmmh, -, -, -, ⟨-, Imh2, -⟩, -, -⟩ Pm_x hs_hx2 Hpath
  have mh_x := m_mh_None hs Pm mh hx2 x2 Known x1 Hmmh hs_hx2 Pm_x
  cases hro : FMap.get ro (rcons p0 (v0 +^ x1)) with
  | none => rfl
  | some b =>
    obtain ⟨v, hx, hy, hp, hm⟩ := (Imh2 _ _ _).1 hro
    rw [Hpath] at hp
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    rw [xorw_cancel_left, mh_x] at hm
    cases hm

/-- The path case of EC's `eq_f`: `x2` has a known path `(p0, v0)`, the oracle answers the
fresh query `rcons p0 (v0 +^ x1)` with `y1`. -/
theorem f_path_inv (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (x1 : block)
    (x2 : capacity) (y1 : block) (y2 : capacity) (hx2 : handle) (p0 : List block) (v0 : block) :
    INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries →
    FMap.get Pm (x1, x2) = none → FMap.get pi x2 = some (p0, v0) →
    FMap.get hs hx2 = some (x2, Known) → build_hpath mh p0 = some (v0, hx2) →
    hinv hs y2 = none →
    INV_CF_G1 (FMap.set hs ch (y2, Known)) (ch + 1)
      (FMap.set Pm (x1, x2) (y1, y2)) (FMap.set Pmi (y1, y2) (x1, x2))
      (FMap.set Gm (x1, x2) (y1, y2)) (FMap.set Gmi (y1, y2) (x1, x2))
      (FMap.set mh (x1, hx2) (y1, ch)) (FMap.set mhi (y1, ch) (x1, hx2))
      (FMap.set ro (rcons p0 (v0 +^ x1)) y1) (FMap.set pi y2 (rcons p0 (v0 +^ x1), y1))
      prefixes queries := by
  intro HINV Pm_x _pi_x2 hs_hx2 Hpath hinv0
  obtain ⟨Hhs, HinvG, Hinvmh, Hmmh, Hmimhi, Hincl, Hincli, Hmh, Hpi, Hmp⟩ := HINV
  obtain ⟨hun, -, hlt⟩ := id Hhs
  obtain ⟨-, Imm2⟩ := id Hmmh
  obtain ⟨Imi1, -⟩ := id Hmimhi
  obtain ⟨Imh1, Imh2, Imh3⟩ := Hmh
  obtain ⟨Ipi⟩ := Hpi
  have hy2 : ∀ f h, FMap.get hs h ≠ some (y2, f) := by
    have hp := hinvP hs y2
    rw [if_pos hinv0] at hp
    exact fun f h => hp h f
  have hs_ch : FMap.get hs ch = none := ch_notdomE_hs hs ch Hhs
  have Gm_x : FMap.get Gm (x1, x2) = none := notin_m_notin_Gm Pm Gm _ Hincl Pm_x
  have mh_x : FMap.get mh (x1, hx2) = none := m_mh_None hs Pm mh hx2 x2 Known x1 Hmmh hs_hx2 Pm_x
  have Hhx2 : hx2 ≠ ch := dom_hs_neq_ch hs ch hx2 x2 Known Hhs hs_hx2
  have ch0 : 0 ≠ ch := ch_neq0 hs ch Hhs
  have ch_None : ∀ xa xb ha hb,
      FMap.get mh (xa, ha) = some (xb, hb) → ha ≠ ch ∧ hb ≠ ch := by
    intro xa xb ha hb hm
    obtain ⟨_, _, _, _, h1, h2, -⟩ := Imm2 _ _ _ _ hm
    exact ⟨dom_hs_neq_ch hs ch _ _ _ Hhs h1, dom_hs_neq_ch hs ch _ _ _ Hhs h2⟩
  have hsne : ∀ h cf, FMap.get hs h = some cf →
      FMap.get (FMap.set hs ch (y2, Known)) h = some cf := by
    intro h cf hh
    have := hlt _ _ hh
    rw [FMap.get_set_neqE _ _ _ _ (show h ≠ ch by linarith), hh]
  have mhup : ∀ p v h, build_hpath mh p = some (v, h) →
      build_hpath (FMap.set mh (x1, hx2) (y1, ch)) p = some (v, h) :=
    fun p v h hp => build_hpath_up mh x1 hx2 y1 ch p v h hp mh_x
  have bpiff := fun p v hx =>
    build_hpath_upd_ch_iff hx2 ch mh x1 y1 p v hx mh_x ch0 Hhx2 ch_None
  have Hpath' := mhup _ _ _ Hpath
  have Hmp' : ∀ (x y : state), FMap.get Pm x = none →
      m_p (FMap.set Pm x y) prefixes queries := by
    obtain ⟨c1, c2, c3, c4, c5⟩ := Hmp
    intro x y hx
    refine ⟨c1, c2, ?_, c4, c5⟩
    intro l hl i hi
    obtain ⟨sa, sc, h1, h2⟩ := c3 l hl i hi
    refine ⟨sa, sc, h1, ?_⟩
    have hne : FMap.get prefixes (take (i + 1) l) ≠ none := by
      by_cases hi' : i + 1 < size l
      · obtain ⟨sa', sc', h1', -⟩ := c3 l hl (i + 1) ⟨by omega, hi'⟩
        rw [h1']
        simp
      · have : take (i + 1) l = l := by
          simp only [take, size] at *
          apply List.take_of_length_le
          omega
        rw [this]
        exact (FMap.domE _ _).1 hl
    rw [FMap.get_setE, if_neg]
    · exact h2
    · intro he
      rw [he, hx] at h2
      exact hne h2.symm
  refine ⟨hs_addh hs ch y2 Known Hhs hy2, ?_, ?_, ?_, ?_, incl_addm _ _ _ _ Hincl,
    incl_addm _ _ _ _ Hincli, ?_, ?_, Hmp' _ _ Pm_x⟩
  · refine inv_addm _ _ _ _ HinvG Gm_x ?_
    cases hg : FMap.get Gmi (y1, y2) with
    | none => rfl
    | some xc =>
      have hp := Hincli (y1, y2) (by rw [hg]; simp)
      rw [hg] at hp
      obtain ⟨_, fx, _, _, h1, _, _⟩ := Imi1 _ _ _ _ hp
      exact absurd h1 (hy2 _ _)
  · exact inv_addm _ _ _ _ Hinvmh mh_x (ch_notdomE2_mh hs Pmi mhi y1 ch Hmimhi Hhs)
  · exact m_mh_addh_addm hs Pm mh hx2 x1 x2 ch y1 y2 Known Known Hmmh hun hs_hx2 hs_ch
  · exact mi_mhi_addh_addmi hs Pmi mhi hx2 x1 x2 ch y1 y2 Known Known Hmimhi hy2 hs_hx2 hs_ch
  · refine ⟨?_, ?_, ?_⟩
    · -- first component of `mh_spec`
      intro xa hx' ya hy hm
      rw [FMap.get_setE] at hm
      split_ifs at hm with hk
      · simp only [Prod.mk.injEq, Option.some.injEq] at hk hm
        obtain ⟨hk1, hk2⟩ := hk
        obtain ⟨hm1, hm2⟩ := hm
        subst xa hx' ya hy
        refine ⟨x2, Known, y2, Known, hsne _ _ hs_hx2, FMap.get_set_sameE _ _ _, ?_⟩
        simp
      · obtain ⟨xc, fx, yc, fy, h1, h2, h3⟩ := Imh1 _ _ _ _ hm
        refine ⟨xc, fx, yc, fy, hsne _ _ h1, hsne _ _ h2, ?_⟩
        cases fy with
        | Known =>
          simp only [if_true] at h3 ⊢
          refine ⟨?_, h3.2⟩
          rw [FMap.get_set_neqE]
          · exact h3.1
          · intro he
            rw [he, Gm_x] at h3
            cases h3.1
        | Unknown =>
          simp only [reduceCtorEq, if_false] at h3 ⊢
          obtain ⟨p, v, h4, h5⟩ := h3
          refine ⟨p, v, ?_, mhup _ _ _ h5⟩
          rw [FMap.get_set_neqE _ _ _ _ ?_, h4]
          intro he
          obtain ⟨rfl, he2⟩ := rcons_inj_both he
          rw [Hpath] at h5
          simp only [Option.some.injEq, Prod.mk.injEq] at h5
          obtain ⟨rfl, rfl⟩ := h5
          apply hk
          rw [← xorw_cancel_left v0 xa, he2, xorw_cancel_left]
    · -- second component of `mh_spec`
      intro p bn b
      rw [FMap.get_setE]
      split_ifs with hd
      · obtain ⟨rfl, rfl⟩ := rcons_inj_both hd
        simp only [Option.some.injEq]
        constructor
        · rintro rfl
          refine ⟨v0, hx2, ch, Hpath', ?_⟩
          rw [xorw_cancel_left]
          exact FMap.get_set_sameE _ _ _
        · rintro ⟨v, hx, hy, hp, hm⟩
          rw [Hpath'] at hp
          simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          rw [xorw_cancel_left, FMap.get_set_sameE] at hm
          simp only [Option.some.injEq, Prod.mk.injEq] at hm
          exact hm.1
      · rw [Imh2]
        constructor
        · rintro ⟨v, hx, hy, h1, h2⟩
          refine ⟨v, hx, hy, mhup _ _ _ h1, ?_⟩
          rw [FMap.get_set_neqE]
          · exact h2
          · intro he
            rw [he, mh_x] at h2
            cases h2
        · rintro ⟨v, hx, hy, h1, h2⟩
          rw [bpiff] at h1
          split_ifs at h1 with hxc
          · subst hxc
            rw [FMap.get_set_neqE _ _ _ _ (by simp [Ne.symm Hhx2]),
              ch_notdomE2_mh hs Pm mh _ hx Hmmh Hhs] at h2
            cases h2
          · refine ⟨v, hx, hy, h1, ?_⟩
            rw [FMap.get_setE] at h2
            split_ifs at h2 with hk
            · simp only [Prod.mk.injEq] at hk
              obtain ⟨hk1, rfl⟩ := hk
              obtain ⟨rfl, rfl⟩ := Imh3 _ _ _ _ _ h1 Hpath
              apply absurd _ hd
              rw [← hk1, xorw_cancel_left]
            · exact h2
    · -- third component of `mh_spec`
      intro p v p' v' hx h1 h2
      rw [bpiff] at h1 h2
      split_ifs at h1 h2 with hxc
      · obtain ⟨pa, xa, ha, rfl, rfl⟩ := h1
        obtain ⟨pb, xb, hb, rfl, rfl⟩ := h2
        obtain ⟨rfl, rfl⟩ := Imh3 _ _ _ _ _ ha hb
        exact ⟨rfl, rfl⟩
      · exact Imh3 _ _ _ _ _ h1 h2
  · -- `pi_spec`
    refine ⟨fun c p v => ?_⟩
    rw [FMap.get_setE]
    split_ifs with hc
    · subst hc
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        refine ⟨ch, ?_, FMap.get_set_sameE _ _ _⟩
        rw [bpiff, if_pos rfl]
        exact ⟨p0, v0, Hpath, rfl, rfl⟩
      · rintro ⟨h, h1, h2⟩
        rw [bpiff] at h1
        split_ifs at h1 with hh
        · obtain ⟨pa, xa, ha, rfl, rfl⟩ := h1
          obtain ⟨rfl, rfl⟩ := Imh3 _ _ _ _ _ ha Hpath
          exact ⟨rfl, rfl⟩
        · rw [FMap.get_set_neqE _ _ _ _ hh] at h2
          exact absurd h2 (hy2 _ _)
    · rw [Ipi]
      constructor
      · rintro ⟨h, h1, h2⟩
        exact ⟨h, mhup _ _ _ h1, hsne _ _ h2⟩
      · rintro ⟨h, h1, h2⟩
        rw [bpiff] at h1
        split_ifs at h1 with hh
        · subst hh
          rw [FMap.get_set_sameE] at h2
          simp only [Option.some.injEq, Prod.mk.injEq] at h2
          exact absurd h2.1.symm hc
        · rw [FMap.get_set_neqE _ _ _ _ hh] at h2
          exact ⟨h, h1, h2⟩


theorem f_none_inv (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (xa y1 : block)
    (xc y2 : capacity)
    (hI : INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries)
    (hP : ¬ FMap.dom Pm (xa, xc)) (hG : ¬ FMap.dom Gm (xa, xc))
    (hnone : ∀ f h, FMap.get hs h ≠ some (xc, f))
    (hcol : hinv (FMap.set hs ch (xc, Known)) y2 = none) :
    INV_CF_G1 (FMap.set (FMap.set hs ch (xc, Known)) (ch + 1) (y2, Known)) (ch + 1 + 1)
      (FMap.set Pm (xa, xc) (y1, y2)) (FMap.set Pmi (y1, y2) (xa, xc))
      (FMap.set Gm (xa, xc) (y1, y2)) (FMap.set Gmi (y1, y2) (xa, xc))
      (FMap.set mh (xa, ch) (y1, ch + 1)) (FMap.set mhi (y1, ch + 1) (xa, ch))
      ro pi prefixes queries := by
  have hy := hinvP (FMap.set hs ch (xc, Known)) y2
  rw [if_pos hcol] at hy
  have hxy : xc ≠ y2 := by
    rintro rfl
    exact hy ch Known (FMap.get_set_sameE _ _ _)
  have hy2 : ∀ f h, FMap.get hs h ≠ some (y2, f) := by
    intro f h hh
    by_cases e : h = ch
    · subst e
      rw [ch_notdomE_hs _ _ hI.1] at hh
      cases hh
    · exact hy h f (by rw [FMap.get_set_neqE _ _ _ _ e]; exact hh)
  rw [show ch + 1 + 1 = ch + 2 by ring]
  exact lemma1 hs ch Pm Pmi Gm Gmi mh mhi ro pi xa xc y1 y2 prefixes queries hI hxy
    (by simpa [FMap.domE] using hP) (by simpa [FMap.domE] using hG) hnone hy2

theorem f_known_inv (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (xa y1 : block)
    (xc y2 : capacity) (hx : handle)
    (hI : INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries)
    (hP : ¬ FMap.dom Pm (xa, xc)) (hG : ¬ FMap.dom Gm (xa, xc)) (hpi : ¬ FMap.dom pi xc)
    (hhx : FMap.get hs hx = some (xc, Known))
    (hcol : hinv hs y2 = none) :
    INV_CF_G1 (FMap.set hs ch (y2, Known)) (ch + 1)
      (FMap.set Pm (xa, xc) (y1, y2)) (FMap.set Pmi (y1, y2) (xa, xc))
      (FMap.set Gm (xa, xc) (y1, y2)) (FMap.set Gmi (y1, y2) (xa, xc))
      (FMap.set mh (xa, hx) (y1, ch)) (FMap.set mhi (y1, ch) (xa, hx))
      ro pi prefixes queries := by
  have hy := hinvP hs y2
  rw [if_pos hcol] at hy
  exact lemma2 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries xa xc y1 y2 hx hI
    (by simpa [FMap.domE] using hP) (by simpa [FMap.domE] using hG)
    (by simpa [FMap.domE] using hpi) hhx (fun f h => hy h f)

theorem f_B2_facts (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (xa ya : block)
    (xc yc : capacity)
    (hI : INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries)
    (hP : FMap.get Pm (xa, xc) = some (ya, yc)) (hG : FMap.get Gm (xa, xc) = none) :
    ∃ hx fx hy, FMap.get hs hx = some (xc, fx) ∧ FMap.get hs hy = some (yc, Unknown) ∧
      FMap.get mh (xa, hx) = some (ya, hy) ∧
      (fx = Known → ∃ p v, FMap.get pi xc = some (p, v) ∧
        FMap.get ro (rcons p (v +^ xa)) = some ya ∧ build_hpath mh p = some (v, hx)) := by
  obtain ⟨hx, fx, hy, fy, h1, h2, h3⟩ := hI.4.1 _ _ _ _ hP
  obtain ⟨xc', fx', yc', fy', h1', h2', h4⟩ := hI.8.1 _ _ _ _ h3
  rw [h1] at h1'
  rw [h2] at h2'
  simp only [Option.some.injEq, Prod.mk.injEq] at h1' h2'
  obtain ⟨rfl, rfl⟩ := h1'
  obtain ⟨rfl, rfl⟩ := h2'
  cases fy with
  | Known =>
    rw [if_pos rfl] at h4
    rw [hG] at h4
    cases h4.1
  | Unknown =>
    simp only [reduceCtorEq, if_false] at h4
    obtain ⟨p, v, hro, hb⟩ := h4
    refine ⟨hx, fx, hy, h1, h2, h3, fun hk => ⟨p, v, ?_, hro, hb⟩⟩
    subst hk
    exact (hI.9.1 _ _ _).mpr ⟨hx, hb, h1⟩

set_option maxHeartbeats 4000000 in
-- the inlined oracles' wp goals are large
/-- The oracle step of EC's `eq_f`: the `call (: …)` between `PF.f` and `G1.S.f`. -/
theorem PF_f_S_f :
    prhlProc (sig₁ := procsig (state) -> state) (sig₂ := procsig (state) -> state)
      (fun a₁ g₁ a₂ g₂ => G1.bcol.get g₂ = false ∧ G1.bext.get g₂ = false ∧ a₁ = a₂ ∧
        eq_glob_C g₁ g₂ ∧ INV_CF_G1_12 g₁ g₂)
      (Indifferentiability.PRIMITIVE.f state (List block) block PF).procedure
      (Indifferentiability.DPRIMITIVE.f state (List block) block G1.S).procedure
      (fun r₁ g₁ r₂ g₂ => eq_glob_C g₁ g₂ ∧ FMap.dom (C.queries.get g₂) [] ∧
        (G1.bcol.get g₂ = false → G1.bext.get g₂ = false → r₁ = r₂ ∧ INV_CF_G1_12 g₁ g₂)) := by
  unfold PF G1.S
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §G1.bcol{2} = false ∧ §G1.bext{2} = false ∧
      eq_glob_C §allGlobals{1} §allGlobals{2} ∧ INV_CF_G1_12 §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨hc, hb, rfl, hC, hI⟩
    exact ⟨rfl, hc, hb, hC, hI⟩
  · equiv_if{1}
    case «then» =>
      equiv_if{2}
      case «then» =>
        stmt_wp
        equiv_if{2}
        case «then» =>
          equiv_seq 1 3 : (§y1{1} = §(localVarLens "r" block){2} ∧
              §x1{2} = rcons §p{2} (§v{2} +^ (§x0{2}).1) ∧
              (§p{2}, §v{2}) = oget (FMap.get §G1.paths{2} (§x0{2}).2) ∧
              ¬ FMap.dom §F.RO.m{2} §x1{2} ∧
              §x0{1} = §x0{2} ∧ §G1.bcol{2} = false ∧ §G1.bext{2} = false ∧
              eq_glob_C §allGlobals{1} §allGlobals{2} ∧ INV_CF_G1_12 §allGlobals{1} §allGlobals{2} ∧
              ¬ FMap.dom §PF.m{1} §x0{1} ∧ ¬ FMap.dom §G1.m{2} §x0{2} ∧
              FMap.dom §G1.paths{2} (§x0{2}).2)
          · equiv_rnd
            stmt_wp
            equiv_skip
            rintro g₁ g₂ x0 _ ⟨⟨⟨⟨rfl, hc, hb, hC, hI⟩, hP⟩, hG⟩, hpa⟩ a -
            simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hP hG hpa
            refine ⟨?_, rfl, hc, hb, hC, hI, hP, hG, hpa⟩
            obtain ⟨xa, xc⟩ := x0
            unfold INV_CF_G1_12 at hI
            obtain ⟨⟨p0, v0⟩, hpi⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hpa)
            obtain ⟨h, hbp, hhs⟩ := (hI.9.1 _ _ _).mp hpi
            have := f_path_ro_none _ _ _ _ _ _ _ _ _ _ _ _ xa xc h p0 v0 hI
              (by simpa [FMap.domE] using hP) hhs hbp
            rw [hpi]
            simpa [oget, FMap.domE] using this
          · equiv_rnd
            stmt_wp{2} 1
            equiv_if{2}
            case «then» =>
              stmt_wp
              equiv_skip
              intro g₁ g₂ y1 x0 r x1 p v x0' hR y2 hy2
              obtain ⟨⟨rfl, rfl, hpv, -, rfl, hc, hb, hC, hI, hP, hG, hpa⟩, -⟩ := hR
              obtain ⟨xa, xc⟩ := x0
              unfold INV_CF_G1_12 at hI
              have hq : FMap.dom (C.queries.get g₂) [] := by rw [FMap.domE, hI.10.2]; simp
              obtain ⟨⟨p0, v0⟩, hpi⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hpa)
              rw [hpi] at hpv
              simp only [oget, Option.getD_some, Prod.mk.injEq] at hpv
              obtain ⟨rfl, rfl⟩ := hpv
              obtain ⟨h, hbp, hhs⟩ := (hI.9.1 _ _ _).mp hpi
              have hK : FMap.rng (FRO.m.get g₂) (xc, Known) := ⟨h, hhs⟩
              have hgf := (getflagP_some _ _ Known hI.1.1).2 hK
              have hU : ¬ FMap.rng (FRO.m.get g₂) (xc, Unknown) := fun hu => by
                have := (getflagP_some _ _ Unknown hI.1.1).2 hu
                rw [hgf] at this
                cases this
              have hx2' : oget (hinvK (FRO.m.get g₂) xc) = h := by
                rw [huniq_hinvK_h _ _ _ hI.1.1 hhs]; rfl
              have hPn : FMap.get (PF.m.get g₁) (xa, xc) = none := by simpa [FMap.domE] using hP
              have hmh : ¬ FMap.dom (G1.mh.get g₂) (xa, h) := by
                rw [FMap.domE, m_mh_None _ _ _ _ _ _ _ hI.4 hhs hPn]
                simp
              simp only [hK, hU, decide_true, decide_false, Bool.not_true, Bool.false_eq_true,
                if_false, Bool.or_false, hx2', hmh, false_and]
              simp only [eq_glob_C, INV_CF_G1_12] at hC ⊢
              simp_reads
              simp only [hpa, decide_true, if_true, FMap.get_set_sameE, hpi]
              simp only [oget, Option.getD_some]
              refine ⟨hC, hq, fun hcol _ => ⟨trivial, ?_⟩⟩
              simp only [hc, Bool.false_or, decide_eq_false_iff_not, not_not] at hcol
              exact f_path_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI hPn hpi hhs hbp hcol
            case «else» =>
              refine prhlStmt_pre prhlStmt_false ?_
              rintro σ₁ σ₂ ⟨⟨-, -, -, hro, -⟩, hg⟩
              simp only [Bool.not_eq_false', decide_eq_true_eq] at hg
              exact hro hg
        case «else» =>
          equiv_rnd
          equiv_rnd
          equiv_skip
          rintro g₁ g₂ x0 _ ⟨⟨⟨⟨rfl, hc, hb, hC, hI⟩, hP⟩, hG⟩, hpa⟩ y1 - y2 -
          obtain ⟨xa, xc⟩ := x0
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hP hG hpa
          unfold INV_CF_G1_12 at hI
          have hq : FMap.dom (C.queries.get g₂) [] := by rw [FMap.domE, hI.10.2]; simp
          rcases hgf : getflag (FRO.m.get g₂) xc with _ | f
          · have hnone := (getflagP_none _ _).1 hgf
            have hK : ¬ FMap.rng (FRO.m.get g₂) (xc, Known) := fun ⟨h, hh⟩ => hnone _ h hh
            have hU : ¬ FMap.rng (FRO.m.get g₂) (xc, Unknown) := fun ⟨h, hh⟩ => hnone _ h hh
            simp only [hK, hU, decide_false, Bool.not_false, if_true, Bool.or_false]
            have hx2 : hinvK (FMap.set (FRO.m.get g₂) (G1.chandle.get g₂) (xc, Known)) xc =
                some (G1.chandle.get g₂) :=
              huniq_hinvK_h _ _ _ (huniq_addh _ _ _ _ hI.1.1 hnone) (FMap.get_set_sameE _ _ _)
            have hx2' : oget (hinvK (FMap.set (FRO.m.get g₂) (G1.chandle.get g₂) (xc, Known))
                xc) = G1.chandle.get g₂ := by rw [hx2]; rfl
            have hmh : ¬ FMap.dom (G1.mh.get g₂) (xa, G1.chandle.get g₂) := by
              rw [FMap.domE, notin_hs_notdomE2_mh _ _ _ _ _ hI.4 (ch_notdomE_hs _ _ hI.1)]
              simp
            simp only [hx2', hmh, false_and, decide_false, Bool.false_eq_true, if_false]
            simp only [eq_glob_C, INV_CF_G1_12] at hC ⊢
            simp_reads
            simp only [hpa, decide_false, Bool.false_eq_true, if_false]
            refine ⟨hC, hq, fun hcol _ => ⟨by simp [oget, FMap.get_set_sameE], ?_⟩⟩
            simp only [hc, Bool.false_or, decide_eq_false_iff_not, not_not] at hcol
            exact f_none_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI hP hG hnone hcol
          · have hsome := (getflagP_some _ _ f hI.1.1).1 hgf
            cases f with
            | Known =>
              obtain ⟨hx, hhx⟩ := id hsome
              have hU : ¬ FMap.rng (FRO.m.get g₂) (xc, Unknown) := fun h => by
                have := (getflagP_some _ _ Unknown hI.1.1).2 h
                rw [hgf] at this
                cases this
              simp only [hsome, hU, decide_true, decide_false, Bool.not_true, Bool.false_eq_true,
                if_false, Bool.or_false]
              have hx2' : oget (hinvK (FRO.m.get g₂) xc) = hx := by
                rw [huniq_hinvK_h _ _ _ hI.1.1 hhx]; rfl
              have hPn : FMap.get (PF.m.get g₁) (xa, xc) = none := by simpa [FMap.domE] using hP
              have hmh : ¬ FMap.dom (G1.mh.get g₂) (xa, hx) := by
                rw [FMap.domE, m_mh_None _ _ _ _ _ _ _ hI.4 hhx hPn]
                simp
              simp only [hx2', hmh, false_and, decide_false, Bool.false_eq_true, if_false]
              simp only [eq_glob_C, INV_CF_G1_12] at hC ⊢
              simp_reads
              simp only [hpa, decide_false, Bool.false_eq_true, if_false]
              refine ⟨hC, hq, fun hcol _ => ⟨by simp [oget, FMap.get_set_sameE], ?_⟩⟩
              simp only [hc, Bool.false_or, decide_eq_false_iff_not, not_not] at hcol
              exact f_known_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI hP hG hpa hhx hcol
            | Unknown =>
              have hK : ¬ FMap.rng (FRO.m.get g₂) (xc, Known) := fun h => by
                have := (getflagP_some _ _ Known hI.1.1).2 h
                rw [hgf] at this
                cases this
              simp only [hsome, hK, decide_true, decide_false, Bool.or_true]
              simp only [eq_glob_C] at hC ⊢
              simp_reads
              simp only [ite_self]
              exact ⟨hC, hq, fun _ h => absurd h (by simp)⟩
      case «else» =>
        refine prhlStmt_pre prhlStmt_false ?_
        rintro σ₁ σ₂ ⟨⟨⟨hx, -, -, -, hI⟩, hP⟩, hG⟩
        simp only [Bool.not_eq_false', Bool.not_eq_true', decide_eq_true_eq,
          decide_eq_false_iff_not] at hP hG
        rw [hx] at hP
        unfold INV_CF_G1_12 at hI
        have hd := (FMap.domE _ _).mp hG
        exact hP ((FMap.domE _ _).mpr (by rw [hI.6 _ hd]; exact hd))
    case «else» =>
      equiv_if{2}
      case «then» =>
        stmt_wp
        equiv_if{2}
        case «then» =>
          equiv_seq 0 3 : (§x1{2} = rcons §p{2} (§v{2} +^ (§x0{2}).1) ∧
              (§p{2}, §v{2}) = oget (FMap.get §G1.paths{2} (§x0{2}).2) ∧
              §x0{1} = §x0{2} ∧ §G1.bcol{2} = false ∧ §G1.bext{2} = false ∧
              eq_glob_C §allGlobals{1} §allGlobals{2} ∧ INV_CF_G1_12 §allGlobals{1} §allGlobals{2} ∧
              FMap.dom §PF.m{1} §x0{1} ∧ ¬ FMap.dom §G1.m{2} §x0{2} ∧
              FMap.dom §G1.paths{2} (§x0{2}).2)
          · stmt_wp{2} 1
            stmt_wp
            equiv_skip
            rintro g₁ g₂ x0 _ ⟨⟨⟨⟨rfl, hc, hb, hC, hI⟩, hP⟩, hG⟩, hpa⟩
            simp only [Bool.not_eq_false', Bool.not_eq_true', decide_eq_true_eq,
              decide_eq_false_iff_not] at hP hG hpa
            exact ⟨(is_lossless_iff_expected bdistr).mp BitWord.dunifin_ll,
              fun _ _ => ⟨rfl, hc, hb, hC, hI, hP, hG, hpa⟩⟩
          · stmt_wp{2} 1
            stmt_wp{2} 1
            equiv_if{2}
            case «then» =>
              stmt_wp
              equiv_skip
              intro g₁ g₂ x0 x1 p v x0' r hR
              refine ⟨(is_lossless_iff_expected cdistr).mp BitWord.dunifin_ll, fun y2 _ => ?_⟩
              obtain ⟨⟨hx1, hpv, hx0, hc, hb, hC, hI, hP, hG, hpa⟩, hro⟩ := hR
              subst hx0
              obtain ⟨xa, xc⟩ := x0
              simp only [Bool.not_eq_true', Bool.not_eq_false', decide_eq_false_iff_not,
                decide_eq_true_eq] at hro
              unfold INV_CF_G1_12 at hI
              have hq : FMap.dom (C.queries.get g₂) [] := by rw [FMap.domE, hI.10.2]; simp
              obtain ⟨⟨ya, yc⟩, hPy⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hP)
              have hGn : FMap.get (G1.m.get g₂) (xa, xc) = none := by simpa [FMap.domE] using hG
              obtain ⟨hx, fx, hy, hhx, hhy, hmh, hKp⟩ :=
                f_B2_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI hPy hGn
              cases fx with
              | Unknown =>
                have hU : FMap.rng (FRO.m.get g₂) (xc, Unknown) := ⟨hx, hhx⟩
                simp only [hU, decide_true, Bool.or_true]
                simp only [eq_glob_C] at hC ⊢
                simp_reads
                simp only [ite_self]
                exact ⟨hC, hq, fun _ h => absurd h (by simp)⟩
              | Known =>
                obtain ⟨p0, v0, hpi, hroy, hbp⟩ := hKp rfl
                rw [hpi] at hpv
                simp only [oget, Option.getD_some, Prod.mk.injEq] at hpv
                obtain ⟨rfl, rfl⟩ := hpv
                subst hx1
                exact absurd ((FMap.domE _ _).mpr (by rw [hroy]; simp)) hro
            case «else» =>
              equiv_skip
              intro g₁ g₂ x0 x1 p v x0' hR
              refine ⟨(is_lossless_iff_expected cdistr).mp BitWord.dunifin_ll, fun y2 _ => ?_⟩
              obtain ⟨⟨hx1, hpv, hx0, hc, hb, hC, hI, hP, hG, hpa⟩, hro⟩ := hR
              subst hx0
              obtain ⟨xa, xc⟩ := x0
              simp only [Bool.not_eq_true', Bool.not_eq_false', decide_eq_false_iff_not,
                decide_eq_true_eq] at hro
              unfold INV_CF_G1_12 at hI
              have hq : FMap.dom (C.queries.get g₂) [] := by rw [FMap.domE, hI.10.2]; simp
              obtain ⟨⟨ya, yc⟩, hPy⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hP)
              have hGn : FMap.get (G1.m.get g₂) (xa, xc) = none := by simpa [FMap.domE] using hG
              obtain ⟨hx, fx, hy, hhx, hhy, hmh, hKp⟩ :=
                f_B2_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI hPy hGn
              cases fx with
              | Unknown =>
                have hU : FMap.rng (FRO.m.get g₂) (xc, Unknown) := ⟨hx, hhx⟩
                simp only [hU, decide_true, Bool.or_true]
                simp only [eq_glob_C] at hC ⊢
                simp_reads
                simp only [ite_self]
                exact ⟨hC, hq, fun _ h => absurd h (by simp)⟩
              | Known =>
                obtain ⟨p0, v0, hpi, hroy, hbp⟩ := hKp rfl
                rw [hpi] at hpv
                simp only [oget, Option.getD_some, Prod.mk.injEq] at hpv
                obtain ⟨rfl, rfl⟩ := hpv
                subst hx1
                have hK : FMap.rng (FRO.m.get g₂) (xc, Known) := ⟨hx, hhx⟩
                have hgf := (getflagP_some _ _ Known hI.1.1).2 hK
                have hU : ¬ FMap.rng (FRO.m.get g₂) (xc, Unknown) := fun hu => by
                  have := (getflagP_some _ _ Unknown hI.1.1).2 hu
                  rw [hgf] at this
                  cases this
                have hx2' : oget (hinvK (FRO.m.get g₂) xc) = hx := by
                  rw [huniq_hinvK_h _ _ _ hI.1.1 hhx]; rfl
                have hmhd : FMap.dom (G1.mh.get g₂) (xa, hx) := by rw [FMap.domE, hmh]; simp
                have hidw : FMap.in_dom_with (FRO.m.get g₂) hy Unknown := by
                  refine ⟨by rw [FMap.domE, hhy]; simp, ?_⟩
                  rw [hhy]; rfl
                have hmh' : oget (FMap.get (G1.mh.get g₂) (xa, hx)) = (ya, hy) := by rw [hmh]; rfl
                have hhy' : oget (FMap.get (FRO.m.get g₂) hy) = (yc, Unknown) := by rw [hhy]; rfl
                have hroy' : oget (FMap.get (F.RO.m.get g₂) (rcons p (v +^ xa))) = ya := by
                  rw [hroy]; rfl
                have hpi' : oget (FMap.get (G1.paths.get g₂) xc) = (p, v) := by rw [hpi]; rfl
                simp only [hK, hU, decide_true, decide_false, Bool.not_true, Bool.false_eq_true,
                  if_false, Bool.or_false, hx2', hmhd, hmh', hidw, true_and, if_true]
                simp only [eq_glob_C, INV_CF_G1_12] at hC ⊢
                simp_reads
                simp only [hhy', hroy', hpi', hpa, decide_true, if_true]
                exact ⟨hC, hq, fun _ _ => ⟨by rw [hPy]; rfl, lemma3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  _ _ hI hPy hGn hmh hhx hhy hpi⟩⟩
        case «else» =>
          stmt_wp{2} 1
          stmt_wp{2} 1
          equiv_skip
          intro g₁ g₂ x0 x0' hR
          refine ⟨(is_lossless_iff_expected bdistr).mp BitWord.dunifin_ll, fun y1 _ =>
            ⟨(is_lossless_iff_expected cdistr).mp BitWord.dunifin_ll, fun y2 _ => ?_⟩⟩
          obtain ⟨⟨⟨⟨hx0, hc, hb, hC, hI⟩, hP⟩, hG⟩, hpa⟩ := hR
          subst hx0
          obtain ⟨xa, xc⟩ := x0
          simp only [Bool.not_eq_true', Bool.not_eq_false', decide_eq_false_iff_not,
            decide_eq_true_eq] at hP hG hpa
          unfold INV_CF_G1_12 at hI
          have hq : FMap.dom (C.queries.get g₂) [] := by rw [FMap.domE, hI.10.2]; simp
          obtain ⟨⟨ya, yc⟩, hPy⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hP)
          have hGn : FMap.get (G1.m.get g₂) (xa, xc) = none := by simpa [FMap.domE] using hG
          obtain ⟨hx, fx, hy, hhx, hhy, hmh, hKp⟩ :=
            f_B2_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI hPy hGn
          cases fx with
          | Unknown =>
            have hU : FMap.rng (FRO.m.get g₂) (xc, Unknown) := ⟨hx, hhx⟩
            simp only [hU, decide_true, Bool.or_true]
            simp only [eq_glob_C] at hC ⊢
            simp_reads
            simp only [ite_self]
            exact ⟨hC, hq, fun _ h => absurd h (by simp)⟩
          | Known =>
            obtain ⟨p0, v0, hpi, -, -⟩ := hKp rfl
            exact absurd ((FMap.domE _ _).mpr (by rw [hpi]; simp)) hpa
      case «else» =>
        stmt_wp
        equiv_skip
        rintro g₁ g₂ x0 _ ⟨⟨⟨rfl, hc, hb, hC, hI⟩, hP⟩, hG⟩
        simp only [Bool.not_eq_false', decide_eq_true_eq] at hP hG
        unfold INV_CF_G1_12 at hI
        have hq : FMap.dom (C.queries.get g₂) [] := by rw [FMap.domE, hI.10.2]; simp
        refine ⟨hC, hq, fun _ _ => ⟨?_, hI⟩⟩
        rw [hI.6 _ (by simpa [FMap.domE] using hG)]

/-- `equiv eq_fi (D <: DISTINGUISHER {-PF, -RO, -G1}) : DPRestr(PF).fi ~
DPRestr(G1(DRestr(D)).S).fi : …`. -/
theorem eq_fi (D : DISTINGUISHER)
    (_hD : FVP.fvP D ≤ ((PF.m).footprint ⊔ (PF.mi).footprint ⊔ (F.RO.m).footprint ⊔
      (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (ROhandle.RO.m).footprint ⊔ (ROhandle.FRO.m).footprint ⊔ (C.queries).footprint)ᶜ) :
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
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  rw [Indifferentiability.PRIMITIVE.view_fi]
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §G1.bcol{2} = false ∧ §G1.bext{2} = false ∧
      eq_glob_C §allGlobals{1} §allGlobals{2} ∧ INV_CF_G1_12 §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨hc, hb, rfl, hC, hI⟩
    exact ⟨rfl, hc, hb, hC, hI⟩
  · equiv_if
    case guard =>
      rintro g₁ g₂ _ _ _ _ ⟨-, -, -, -, hC, -⟩
      rw [hC.1]
    case «then» =>
      stmt_wp
      equiv_call PF_fi_S_fi
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨rfl, rfl, hc, hb, hC, hI⟩, hg⟩
      refine ⟨⟨hc, hb, rfl, hC, hI⟩, ?_⟩
      rintro r₁ g₁' r₂ g₂' ⟨hC', hq, hpost⟩
      split_ifs with hbad
      · exact ⟨by rw [hC'.2]; exact hq, hq⟩
      · simp only [not_or, Bool.not_eq_true] at hbad
        obtain ⟨hr, hI'⟩ := hpost hbad.1 hbad.2
        refine ⟨hr, ?_, ?_⟩
        · simp only [eq_glob_C] at hC' ⊢
          simp_reads
          exact ⟨by rw [hC'.1], hC'.2⟩
        · simp only [INV_CF_G1_12] at hI' ⊢
          simp_reads
          exact hI'
    case «else» =>
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨rfl, rfl, hc, hb, hC, hI⟩, -⟩
      simp only [hc, hb, Bool.false_eq_true, or_self, if_false]
      exact ⟨trivial, hC, hI⟩

/-- `equiv eq_f (D <: DISTINGUISHER {-PF, -RO, -G1}) : DPRestr(PF).f ~
DPRestr(G1(DRestr(D)).S).f : …`. -/
theorem eq_f (D : DISTINGUISHER)
    (_hD : FVP.fvP D ≤ ((PF.m).footprint ⊔ (PF.mi).footprint ⊔ (F.RO.m).footprint ⊔
      (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (ROhandle.RO.m).footprint ⊔ (ROhandle.FRO.m).footprint ⊔ (C.queries).footprint)ᶜ) :
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
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  rw [Indifferentiability.PRIMITIVE.view_f]
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §G1.bcol{2} = false ∧ §G1.bext{2} = false ∧
      eq_glob_C §allGlobals{1} §allGlobals{2} ∧ INV_CF_G1_12 §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨hc, hb, rfl, hC, hI⟩
    exact ⟨rfl, hc, hb, hC, hI⟩
  · equiv_if
    case guard =>
      rintro g₁ g₂ _ _ _ _ ⟨-, -, -, -, hC, -⟩
      rw [hC.1]
    case «then» =>
      stmt_wp
      equiv_call PF_f_S_f
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨rfl, rfl, hc, hb, hC, hI⟩, hg⟩
      refine ⟨⟨hc, hb, rfl, hC, hI⟩, ?_⟩
      rintro r₁ g₁' r₂ g₂' ⟨hC', hq, hpost⟩
      split_ifs with hbad
      · exact hq
      · simp only [not_or, Bool.not_eq_true] at hbad
        obtain ⟨hr, hI'⟩ := hpost hbad.1 hbad.2
        refine ⟨hr, ?_, ?_⟩
        · simp only [eq_glob_C] at hC' ⊢
          simp_reads
          exact ⟨by rw [hC'.1], hC'.2⟩
        · simp only [INV_CF_G1_12] at hI' ⊢
          simp_reads
          exact hI'
    case «else» =>
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨rfl, rfl, hc, hb, hC, hI⟩, -⟩
      simp only [hc, hb, Bool.false_eq_true, or_self, if_false]
      exact ⟨trivial, hC, hI⟩

theorem head_nth {α : Type} (w : α) (l : List α) : head w l = nth w l 0 := by
  cases l <;> rfl

theorem drop_add {α : Type} (n1 n2 : ℤ) (l : List α) :
    0 ≤ n1 → 0 ≤ n2 → drop (n1 + n2) l = drop n2 (drop n1 l) := by
  intro h1 h2
  simp only [drop, List.drop_drop]
  congr 1
  omega

theorem behead_drop {α : Type} (l : List α) : behead l = drop 1 l := by
  cases l <;> rfl

theorem incl_upd_nin {α β : Type} [DecidableEq α] (m1 m2 : FMap α β) (x : α) (y : β) :
    incl m1 m2 → ¬ FMap.dom m2 x → incl m1 (FMap.set m2 x y) := by
  intro hi hx z hz
  rw [FMap.get_setE]
  split_ifs with h
  · subst h
    exact absurd ((FMap.domE _ _).mpr (by rw [hi z hz]; exact hz)) hx
  · exact hi z hz

theorem lemma5 (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block) (i : ℤ)
    (p : List block) (b : block) (c : capacity) (h : handle) :
    INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries → 0 ≤ i ∧ i < size p →
    FMap.dom prefixes (take (i + 1) p) → FMap.get prefixes (take i p) = some (b, c) →
    (∃ f, FMap.get hs h = some (c, f)) →
    ∃ b' c' h', FMap.get Pm (b +^ nth default p i, c) = some (b', c') ∧
      FMap.get mh (b +^ nth default p i, h) = some (b', h') := by
  rintro ⟨⟨hun, -, -⟩, -, -, ⟨Im, -⟩, -, -, -, -, -, ⟨-, -, Ip, -, -⟩⟩ ⟨hi0, hi⟩ hdom hb ⟨f, hh⟩
  have hlt : i.toNat < p.length := by simp only [size] at hi; omega
  have hsz : 0 ≤ i ∧ i < size (take (i + 1) p) := by
    refine ⟨hi0, ?_⟩
    simp only [size, take, List.length_take]
    omega
  obtain ⟨sa, sc, h1, h2⟩ := Ip _ hdom i hsz
  have htt : take i (take (i + 1) p) = take i p := by
    simp only [take, List.take_take]
    congr 1
    omega
  have htt' : take (i + 1) (take (i + 1) p) = take (i + 1) p := by
    simp only [take, List.take_take, min_self]
  have hnth : nth default (take (i + 1) p) i = nth default p i := by
    simp only [nth, if_pos hi0, take, List.getD_eq_getElem?_getD, List.getElem?_take]
    rw [if_pos (by omega)]
  rw [htt, hb] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  rw [hnth, htt'] at h2
  rw [FMap.domE] at hdom
  obtain ⟨⟨b', c'⟩, hpre⟩ := Option.ne_none_iff_exists'.1 hdom
  rw [hpre] at h2
  obtain ⟨hx, fx, hy, fy, h3, -, h5⟩ := Im _ _ _ _ h2
  have := hun _ _ _ _ hh h3 rfl
  subst this
  exact ⟨b', c', hy, h2, h5⟩

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
  rintro ⟨⟨hun, -, -⟩, -, -, ⟨Im, Imh⟩, -, -, -, -, -, -⟩ - - ⟨f, hh⟩
  cases hP : FMap.get Pm (b +^ nth default p i, c) with
  | none =>
    refine Or.inr ⟨rfl, ?_⟩
    cases hM : FMap.get mh (b +^ nth default p i, h) with
    | none => rfl
    | some yh =>
      obtain ⟨xc, fx, yc, fy, h1, -, h3⟩ := Imh _ _ yh.1 yh.2 hM
      rw [hh] at h1
      cases h1
      rw [hP] at h3
      cases h3
  | some bc =>
    obtain ⟨b', c'⟩ := bc
    obtain ⟨hx, fx, hy, fy, h3, -, h5⟩ := Im _ _ _ _ hP
    have := hun _ _ _ _ hh h3 rfl
    subst this
    exact Or.inl ⟨b', c', hy, rfl, h5⟩

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

/-! ## `CF_G1`: the oracles' losslessness, footprints, and EC's invariant -/

/-- `PF.f` is lossless.  Not an EC lemma: EC proves it inline in `CF_G1`. -/
theorem PF_f_ll :
    (Indifferentiability.PRIMITIVE.f state (List block) block PF).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  unfold PF
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 4
  phoare_skip
  simp [(is_lossless_iff_expected bdistr).mp BitWord.dunifin_ll,
    (is_lossless_iff_expected cdistr).mp BitWord.dunifin_ll]

/-- `PF.fi` is lossless.  Not an EC lemma: EC proves it inline in `CF_G1`. -/
theorem PF_fi_ll :
    (Indifferentiability.PRIMITIVE.fi state (List block) block PF).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  unfold PF
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 4
  phoare_skip
  simp [(is_lossless_iff_expected bdistr).mp BitWord.dunifin_ll,
    (is_lossless_iff_expected cdistr).mp BitWord.dunifin_ll]

/-- `G1.S.fi` is lossless.  Not an EC lemma: EC proves it inline in `CF_G1`. -/
theorem G1_S_fi_ll :
    (Indifferentiability.DPRIMITIVE.fi state (List block) block G1.S).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  unfold G1.S
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 4
  phoare_skip
  simp [(is_lossless_iff_expected bdistr).mp BitWord.dunifin_ll,
    (is_lossless_iff_expected cdistr).mp BitWord.dunifin_ll]

/-- `G1.S.f` is lossless.  Not an EC lemma: EC proves it inline in `CF_G1`. -/
theorem G1_S_f_ll :
    (Indifferentiability.DPRIMITIVE.f state (List block) block G1.S).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  unfold G1.S
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_wp 4
  phoare_skip
  simp [(is_lossless_iff_expected bdistr).mp BitWord.dunifin_ll,
    (is_lossless_iff_expected cdistr).mp BitWord.dunifin_ll]

/-- `SqueezelessSponge(P).f` is lossless when `P.f` is: its loop is counted (variant
`size p - i`).  Not an EC lemma: EC proves it inline in `CF_G1`. -/
theorem SqueezelessSponge_f_ll (P : DPRIMITIVE)
    (hP : (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless) :
    (Indifferentiability.FUNCTIONALITY.f state (List block) block
      (Module.app SqueezelessSponge P)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hP ⊢
  refine phoareProc_eq_of_le_ge (fun _ _ _ => Procedure.ewp_const_le _ _ _ _) ?_
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_ge 1 variant (size §p - §i).toNat
  case body =>
    phoare_wp 4
    phoare_simp [hP]
    phoare_skip
    intros
    split <;> simp
  case exit => trivial
  case decreases =>
    intro k
    hoare_wp 1
    hoare_split 1
    refine hoare_seq (hoare_if_wp (At := ?At) (Ae := ?Ae) ?_ ?_) ?_
    rotate_left 2
    · hoare_wp 1
      exact hoare_skip_wp _
    · hoare_wp 1
      hoare_call
      hoare_wp 1
      exact hoare_skip_wp _
    hoare_skip
    rintro i p _ ⟨hlt, rfl⟩
    simp only [decide_eq_true_eq] at hlt
    exact ⟨fun _ => by omega, fun _ _ _ => by omega⟩
  phoare_wp 4
  phoare_skip
  intros; exact le_rfl

/-- `G1.M.f` is lossless: its loop is counted (variant `size p - i`).  Not an EC lemma: EC proves
it inline in `CF_G1`. -/
theorem G1_M_f_ll :
    (Indifferentiability.DFUNCTIONALITY.f state (List block) block G1.M).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  refine phoareProc_eq_of_le_ge (fun _ _ _ => Procedure.ewp_const_le _ _ _ _) ?_
  unfold G1.M
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_wp 6
  simp only [F.dout, (is_lossless_iff_expected bdistr).mp BitWord.dunifin_ll]
  phoare_while_ge 1 variant (size §p - §i).toNat
  case body =>
    phoare_wp 2
    phoare_skip
    intros
    split_ifs <;> simp [(is_lossless_iff_expected bdistr).mp BitWord.dunifin_ll,
      (is_lossless_iff_expected cdistr).mp BitWord.dunifin_ll]
  case exit => trivial
  case decreases =>
    intro k
    hoare_wp 1
    hoare_split 1
    refine hoare_seq (hoare_if_wp (At := ?At) (Ae := ?Ae) ?_ ?_) ?_
    rotate_left 2
    · hoare_wp 1
      exact hoare_skip_wp _
    · hoare_split 1
      refine hoare_seq (hoare_if_wp (At := ?At') (Ae := ?Ae') ?_ ?_) ?_
      rotate_left 2
      · hoare_wp 14
        exact hoare_skip_wp _
      · exact hoare_skip_wp _
      · exact hoare_skip_wp _
    hoare_skip
    rintro i p - - - - - - ⟨hlt, rfl⟩
    simp only [decide_eq_true_eq] at hlt
    refine ⟨fun _ => by omega, fun _ => ⟨fun _ _ _ _ _ => ?_, fun _ => by omega⟩⟩
    split <;> omega
  phoare_wp 7
  phoare_skip
  intros; exact le_rfl

/-- `DFRestr(G1.M).f` keeps the bad event and `[] ∈ C.queries` (EC: "lossless and do not reset
bad", its Hoare part).  Not an EC lemma: EC proves it inline in `CF_G1`. -/
theorem DFRestr_M_f_bad :
    hoareProc
      (fun _ g => (G1.bcol.get g = true ∨ G1.bext.get g = true) ∧ FMap.dom (C.queries.get g) [])
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr G1.M)).procedure
      (fun _ g => (G1.bcol.get g = true ∨ G1.bext.get g = true) ∧
        FMap.dom (C.queries.get g) []) := by
  unfold G1.M
  hoare_proc_to_stmt
  repeat hoare_inline 0
  hoare_wp 1
  hoare_split 1
  refine hoare_seq (hoare_if_wp (At := ?At) (Ae := ?Ae) ?_ ?_) ?_
  rotate_left 2
  · hoare_split 1
    refine hoare_seq (hoare_if_wp (At := ?At') (Ae := ?Ae') ?_ ?_) ?_
    rotate_left 2
    · hoare_wp 7
      hoare_while (§G1.bcol = true ∨ §G1.bext = true) ∧ (§C.queries).dom []
      case body =>
        hoare_wp 1
        hoare_split 1
        refine hoare_seq (hoare_if_wp (At := ?At'') (Ae := ?Ae'') ?_ ?_) ?_
        rotate_left 2
        · hoare_wp 1
          exact hoare_skip_wp _
        · hoare_split 1
          refine hoare_seq (hoare_if_wp (At := ?At''') (Ae := ?Ae''') ?_ ?_) ?_
          rotate_left 2
          · hoare_wp 14
            exact hoare_skip_wp _
          · exact hoare_skip_wp _
          · exact hoare_skip_wp _
        hoare_skip
        rintro _ _ _ _ _ _ _ _ _ _ _ ⟨⟨hb, hq⟩, -⟩
        refine ⟨fun _ => ⟨hb, hq⟩, fun _ => ⟨fun _ _ _ _ _ => ?_, fun _ => ⟨hb, hq⟩⟩⟩
        simp only [ite_self, Bool.or_eq_true]
        exact ⟨hb.imp_left Or.inl, hq⟩
      case exit =>
        rintro _ _ _ _ _ _ _ ⟨hb, hq⟩ _ _ _
        simp only [ite_self]
        exact ⟨hb, (FMap.mem_set _ _ _ _).mpr (Or.inl hq)⟩
      hoare_wp 8
      exact hoare_skip_wp _
    · exact hoare_skip_wp _
    · exact hoare_skip_wp _
  · hoare_wp 1
    exact hoare_skip_wp _
  hoare_wp 3
  hoare_skip
  exact fun _ _ _ _ _ h => ⟨fun _ => ⟨fun _ => h, fun _ => h⟩, fun _ => h⟩

/-- `DPRestr(G1.S).f` keeps the bad event and `[] ∈ C.queries` (as `DFRestr_M_f_bad`).  Not an
EC lemma: EC proves it inline in `CF_G1`. -/
theorem DPRestr_S_f_bad :
    hoareProc
      (fun _ g => (G1.bcol.get g = true ∨ G1.bext.get g = true) ∧ FMap.dom (C.queries.get g) [])
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr G1.S)).procedure
      (fun _ g => (G1.bcol.get g = true ∨ G1.bext.get g = true) ∧
        FMap.dom (C.queries.get g) []) := by
  unfold G1.S
  hoare_proc_to_stmt
  repeat hoare_inline 0
  hoare_split 2
  refine hoare_seq_inv ?_ ?_
  · hoare_wp 1
    hoare_split 1
    refine hoare_seq_inv (hoare_if_inv ?_ ?_) (hoare_skip_wp _)
    · hoare_wp 2
      hoare_split 1
      refine hoare_seq_inv (hoare_if_inv ?_ ?_) ?_
      · hoare_split 1
        refine hoare_seq_inv (hoare_if_inv ?_ ?_) ?_
        · hoare_wp 2
          hoare_skip
          exact fun _ _ _ h => h
        · hoare_skip
          exact fun _ _ _ h => h
        hoare_split 1
        refine hoare_seq_inv (hoare_if_inv ?_ ?_) ?_
        · hoare_wp 5
          hoare_skip
          exact fun _ _ _ h => h
        · hoare_wp 8
          hoare_skip
          rintro _ _ _ _ _ ⟨hb, hq⟩
          exact ⟨by simp only [Bool.or_eq_true]; tauto, hq⟩
        hoare_split 2
        refine hoare_seq_inv ?_ ?_
        · hoare_wp 1
          hoare_split 1
          refine hoare_seq_inv (hoare_if_inv ?_ ?_) (hoare_skip_wp _)
          · hoare_wp 2
            hoare_skip
            exact fun _ _ _ h => h
          · hoare_skip
            exact fun _ _ _ h => h
        hoare_wp 2
        hoare_split 1
        refine hoare_seq_inv (hoare_if_inv ?_ ?_) (hoare_skip_wp _)
        · hoare_wp 2
          hoare_split 1
          refine hoare_seq_inv (hoare_if_inv ?_ ?_) ?_
          · hoare_wp 1
            hoare_skip
            rintro _ _ _ _ _ ⟨hb, hq⟩ _ _
            exact ⟨by simp only [Bool.or_eq_true]; tauto, hq⟩
          · hoare_skip
            rintro _ _ _ _ _ ⟨hb, hq⟩ _ _
            exact ⟨by simp only [Bool.or_eq_true]; tauto, hq⟩
          hoare_wp 4
          hoare_skip
          exact fun _ _ _ _ _ h _ _ => h
        · hoare_wp 2
          hoare_skip
          rintro _ _ _ _ _ ⟨hb, hq⟩ _ _ _ _
          exact ⟨by simp only [Bool.or_eq_true]; tauto, hq⟩
      · hoare_wp 1
        hoare_skip
        exact fun _ _ _ h => h
      hoare_wp 2
      hoare_skip
      exact fun _ _ _ h => h
    · hoare_skip
      exact fun _ _ _ h => h
  hoare_wp 3
  hoare_skip
  exact fun _ _ _ h => h

/-- `DPRestr(G1.S).fi` keeps the bad event and `[] ∈ C.queries` (as `DFRestr_M_f_bad`).  Not an
EC lemma: EC proves it inline in `CF_G1`. -/
theorem DPRestr_S_fi_bad :
    hoareProc
      (fun _ g => (G1.bcol.get g = true ∨ G1.bext.get g = true) ∧ FMap.dom (C.queries.get g) [])
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr G1.S)).procedure
      (fun _ g => (G1.bcol.get g = true ∨ G1.bext.get g = true) ∧
        FMap.dom (C.queries.get g) []) := by
  unfold G1.S
  hoare_proc_to_stmt
  repeat hoare_inline 0
  hoare_split 2
  refine hoare_seq_inv ?_ ?_
  · hoare_wp 1
    hoare_split 1
    refine hoare_seq_inv (hoare_if_inv ?_ ?_) (hoare_skip_wp _)
    · hoare_wp 2
      hoare_split 1
      refine hoare_seq_inv (hoare_if_inv ?_ ?_) ?_
      · hoare_split 1
        refine hoare_seq_inv (hoare_if_inv ?_ ?_) ?_
        · hoare_wp 5
          hoare_skip
          exact fun _ _ _ h => h
        · hoare_wp 8
          hoare_skip
          rintro _ _ _ _ _ ⟨hb, hq⟩
          exact ⟨by simp only [Bool.or_eq_true]; tauto, hq⟩
        hoare_wp 4
        hoare_split 1
        refine hoare_seq_inv (hoare_if_inv ?_ ?_) ?_
        · hoare_wp 2
          hoare_skip
          exact fun _ _ _ h _ _ _ _ => h
        · hoare_skip
          exact fun _ _ _ h _ _ _ _ => h
        hoare_wp 1
        hoare_skip
        rintro _ _ _ _ _ ⟨hb, hq⟩
        exact ⟨by simp only [Bool.or_eq_true]; tauto, hq⟩
      · hoare_wp 1
        hoare_skip
        exact fun _ _ _ h => h
      hoare_wp 2
      hoare_skip
      exact fun _ _ _ h => h
    · hoare_skip
      exact fun _ _ _ h => h
  hoare_wp 3
  hoare_skip
  exact fun _ _ _ h => h

/-- The invariant holds of the initial states.  Not an EC lemma: EC proves it inline in `CF_G1`
(`smt (get_setE emptyE build_hpath_map0)`). -/
theorem INV_CF_G1_init :
    INV_CF_G1 (FMap.set (FMap.empty : FMap handle (capacity × flag)) 0 (c0, Known)) 1
      FMap.empty FMap.empty FMap.empty FMap.empty FMap.empty FMap.empty FMap.empty
      (FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0))
      (FMap.set (FMap.empty : FMap (List block) state) [] (b0, c0))
      (FMap.set (FMap.empty : FMap (List block) block) [] b0) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_⟩, ⟨?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro h1 h2 cf1 cf2 hh1 hh2 _
    rw [FMap.get_setE] at hh1 hh2
    split_ifs at hh1 hh2 <;> simp_all
  · simp
  · intro cf h hh
    rw [FMap.get_setE] at hh
    split_ifs at hh with h0
    · simp [h0]
    · simp at hh
  all_goals try simp [incl]
  · intro p v p' v' hx h1 h2
    rw [build_hpath_map0] at h1 h2
    split_ifs at h1 h2
    simp_all
  · intro c p v
    rw [FMap.get_setE, build_hpath_map0]
    by_cases hp : p = []
    · by_cases hc : c = c0
      · simp [hc, hp, FMap.get_setE]
      · simp only [hc, hp, FMap.get_setE]
        simpa using fun _ h => hc h.symm
    · simp [hp]
  · intro l hl
    obtain rfl : l = [] := by simpa [FMap.mem_set, FMap.mem_empty] using hl
    intro i _ hi
    simp [size] at hi
    omega
  · intro l hl
    obtain rfl : l = [] := by simpa [FMap.mem_set, FMap.mem_empty] using hl
    exact ⟨c0, by simp [oget]⟩
  · intro l hl
    obtain rfl : l = [] := by simpa [FMap.mem_set, FMap.mem_empty] using hl
    exact ⟨[], by simp [FMap.mem_set]⟩

/-- `PF.init` touches `PF.m`, `PF.mi`.  Not an EC lemma (EC reads it off the code). -/
@[fp_bound] theorem fvP_PF_init : FVP.fvP PF.init ≤ PF.m.footprint ⊔ PF.mi.footprint := by
  have h : FVP.fvP PF.init ≤ (Lens.pair PF.m PF.mi).footprint := by
    fp_module (Lens.pair PF.m PF.mi)
  simpa only [Footprint.lens_pair] using h

/-- `PF.f` touches `PF.m`, `PF.mi`.  Not an EC lemma (EC reads it off the code). -/
@[fp_bound] theorem fvP_PF_f : FVP.fvP PF.f ≤ PF.m.footprint ⊔ PF.mi.footprint := by
  have h : FVP.fvP PF.f ≤ (Lens.pair PF.m PF.mi).footprint := by
    fp_module (Lens.pair PF.m PF.mi)
  simpa only [Footprint.lens_pair] using h

/-- `PF.fi` touches `PF.m`, `PF.mi`.  Not an EC lemma (EC reads it off the code). -/
@[fp_bound] theorem fvP_PF_fi : FVP.fvP PF.fi ≤ PF.m.footprint ⊔ PF.mi.footprint := by
  have h : FVP.fvP PF.fi ≤ (Lens.pair PF.m PF.mi).footprint := by
    fp_module (Lens.pair PF.m PF.mi)
  simpa only [Footprint.lens_pair] using h

/-- `SqueezelessSponge` touches `Redo.prefixes`.  Not an EC lemma. -/
@[fp_bound] theorem fvP_SqueezelessSponge :
    FVP.fvP SqueezelessSponge ≤ Redo.prefixes.footprint := by
  fp_module Redo.prefixes

set_option maxHeartbeats 8000000 in
-- `within_lens` against a pair of seven variables is slow
/-- `G1.M.f` touches `C.queries`, `F.RO.m`, `FRO.m`, `G1.mh`, `G1.mhi`, `G1.chandle`, `G1.bcol`.
Not an EC lemma. -/
@[fp_bound] theorem fvP_G1M_f : FVP.fvP G1.M.f ≤
    (Lens.pair C.queries (Lens.pair F.RO.m (Lens.pair FRO.m (Lens.pair G1.mh
    (Lens.pair G1.mhi (Lens.pair G1.chandle G1.bcol)))))).footprint := by
  fp_module (Lens.pair C.queries (Lens.pair F.RO.m (Lens.pair FRO.m (Lens.pair G1.mh
    (Lens.pair G1.mhi (Lens.pair G1.chandle G1.bcol))))))

set_option maxHeartbeats 8000000 in
-- `within_lens` against a pair of ten variables is slow
/-- `G1.S.f` touches `F.RO.m`, `FRO.m` and the variables of `G1`.  Not an EC lemma. -/
@[fp_bound] theorem fvP_G1S_f : FVP.fvP G1.S.f ≤
    (Lens.pair F.RO.m (Lens.pair FRO.m (Lens.pair G1.m (Lens.pair G1.mi
    (Lens.pair G1.mh (Lens.pair G1.mhi (Lens.pair G1.chandle (Lens.pair G1.paths
      (Lens.pair G1.bext G1.bcol))))))))).footprint := by
  fp_module (Lens.pair F.RO.m (Lens.pair FRO.m (Lens.pair G1.m (Lens.pair G1.mi
    (Lens.pair G1.mh (Lens.pair G1.mhi (Lens.pair G1.chandle (Lens.pair G1.paths
      (Lens.pair G1.bext G1.bcol)))))))))

set_option maxHeartbeats 8000000 in
-- `within_lens` against a pair of ten variables is slow
/-- `G1.S.fi` touches what `G1.S.f` does.  Not an EC lemma. -/
@[fp_bound] theorem fvP_G1S_fi : FVP.fvP G1.S.fi ≤
    (Lens.pair F.RO.m (Lens.pair FRO.m (Lens.pair G1.m (Lens.pair G1.mi
    (Lens.pair G1.mh (Lens.pair G1.mhi (Lens.pair G1.chandle (Lens.pair G1.paths
      (Lens.pair G1.bext G1.bcol))))))))).footprint := by
  fp_module (Lens.pair F.RO.m (Lens.pair FRO.m (Lens.pair G1.m (Lens.pair G1.mi
    (Lens.pair G1.mh (Lens.pair G1.mhi (Lens.pair G1.chandle (Lens.pair G1.paths
      (Lens.pair G1.bext G1.bcol)))))))))

set_option maxHeartbeats 8000000 in
-- `within_lens` against a pair of seven variables is slow
/-- `G1.M` touches what `G1.M.f` does (for `D_ll`'s side conditions in `CF_G1`).  Not an EC
lemma. -/
theorem fvP_G1M : FVP.fvP G1.M ≤
    (Lens.pair C.queries (Lens.pair F.RO.m (Lens.pair FRO.m (Lens.pair G1.mh
    (Lens.pair G1.mhi (Lens.pair G1.chandle G1.bcol)))))).footprint := by
  fp_module (Lens.pair C.queries (Lens.pair F.RO.m (Lens.pair FRO.m (Lens.pair G1.mh
    (Lens.pair G1.mhi (Lens.pair G1.chandle G1.bcol))))))

set_option maxHeartbeats 8000000 in
-- `within_lens` against a pair of ten variables is slow
/-- `G1.S` touches what `G1.S.f` does (for `D_ll`'s side conditions in `CF_G1`).  Not an EC
lemma. -/
theorem fvP_G1S : FVP.fvP G1.S ≤
    (Lens.pair F.RO.m (Lens.pair FRO.m (Lens.pair G1.m (Lens.pair G1.mi
    (Lens.pair G1.mh (Lens.pair G1.mhi (Lens.pair G1.chandle (Lens.pair G1.paths
      (Lens.pair G1.bext G1.bcol))))))))).footprint := by
  fp_module (Lens.pair F.RO.m (Lens.pair FRO.m (Lens.pair G1.m (Lens.pair G1.mi
    (Lens.pair G1.mh (Lens.pair G1.mhi (Lens.pair G1.chandle (Lens.pair G1.paths
      (Lens.pair G1.bext G1.bcol)))))))))

/-- `DFRestr(F).f` is lossless when `F.f` is: `rf_ll` without `{-C}`, which its proof does not
use (`G1.M` reads `C.queries`).  Not an EC lemma (EC proves it inline in `CF_G1`). -/
theorem rf_ll' (F : DFUNCTIONALITY) :
    (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
    (Indifferentiability.DFUNCTIONALITY.f state (List block) block
      (Module.app DFRestr F)).procedure.IsLossless := by
  intro hll
  rw [Procedure.isLossless_iff_phoareProc] at hll ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 5
  phoare_simp [hll]
  phoare_skip
  simp

/-- `PF` repackaged as `Indif` presents it to the distinguisher is its view. -/
theorem view_PF_eq : Indifferentiability.DPRIMITIVE.mk state (List block) block
    { f := Indifferentiability.PRIMITIVE.f state (List block) block PF,
      fi := Indifferentiability.PRIMITIVE.fi state (List block) block PF } =
    Indifferentiability.PRIMITIVE.view state (List block) block PF := rfl

/-- `PF` is the record of its procedures (eta). -/
theorem PF_eta : Module.pair PF.init (Module.pair PF.f PF.fi) = PF := rfl

/-- `fp_disjoint` with `C.footprint` unfolded (in the goal, when it is there). -/
macro "fp_disj'" : tactic => `(tactic| ((try unfold C.footprint); fp_disjoint))

/-- The values of the variables EC's invariant of `CF_G1` reads: `C.c`, `C.queries`, `PF.m`,
`PF.mi`, `Redo.prefixes`, `FRO.m`, `G1.chandle`, `G1.m`, `G1.mi`, `G1.mh`, `G1.mhi`, `F.RO.m`,
`G1.paths`, `G1.bcol`, `G1.bext`. -/
abbrev CFState : Type :=
  ℤ × FMap (List block) block × smap × smap × FMap (List block) state ×
    FMap handle (capacity × flag) × ℤ × smap × smap × hsmap × hsmap × FMap (List block) block ×
    FMap capacity (List block × block) × Bool × Bool

/-- The lens of the variables EC's invariant of `CF_G1` reads. -/
noncomputable abbrev cfL : Lens CFState VariableAssignment :=
  Lens.pair C.c (Lens.pair C.queries (Lens.pair PF.m (Lens.pair PF.mi (Lens.pair Redo.prefixes
    (Lens.pair FRO.m (Lens.pair G1.chandle (Lens.pair G1.m (Lens.pair G1.mi (Lens.pair G1.mh
      (Lens.pair G1.mhi (Lens.pair F.RO.m (Lens.pair G1.paths
        (Lens.pair G1.bcol G1.bext)))))))))))))

/-- EC's invariant of `CF_G1` (`={glob C} /\ INV_CF_G1 …`), on the values of `cfL`. -/
def cfI (x y : CFState) : Prop :=
  (x.1 = y.1 ∧ x.2.1 = y.2.1) ∧
    INV_CF_G1 y.2.2.2.2.2.1 y.2.2.2.2.2.2.1 x.2.2.1 x.2.2.2.1 y.2.2.2.2.2.2.2.1
      y.2.2.2.2.2.2.2.2.1 y.2.2.2.2.2.2.2.2.2.1 y.2.2.2.2.2.2.2.2.2.2.1
      y.2.2.2.2.2.2.2.2.2.2.2.1 y.2.2.2.2.2.2.2.2.2.2.2.2.1 x.2.2.2.2.1 y.2.1

/-- EC's bad event `G1.bcol \/ G1.bext`, on the values of `cfL`. -/
def cfBad (y : CFState) : Prop :=
  y.2.2.2.2.2.2.2.2.2.2.2.2.2.1 = true ∨ y.2.2.2.2.2.2.2.2.2.2.2.2.2.2 = true

/-- EC's invariant after the bad event, `[] \in C.queries{2}`, on the values of `cfL`. -/
def cfQ (_ y : CFState) : Prop :=
  FMap.dom y.2.1 []

theorem cfI_iff (g₁ g₂ : VariableAssignment) :
    cfI (cfL.get g₁) (cfL.get g₂) ↔ eq_glob_C g₁ g₂ ∧ INV_CF_G1_12 g₁ g₂ := Iff.rfl

theorem cfBad_iff (g : VariableAssignment) :
    cfBad (cfL.get g) ↔ G1.bcol.get g = true ∨ G1.bext.get g = true := Iff.rfl

section AUX

variable (D : DISTINGUISHER)

set_option maxHeartbeats 4000000 in
-- the oracles' footprint and frame checks
/-- `equiv CF_G1 : CF(DRestr(D)).main ~ G1(DRestr(D)).main : ={glob D} ==>
!(G1.bcol \/ G1.bext){2} => ={res}`, for `declare module D <: DISTINGUISHER
{-PF, -RO, -G1, -Redo, -C}` with the axiom `D_ll`. -/
theorem CF_G1 (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ ((PF.m).footprint ⊔ (PF.mi).footprint ⊔ (F.RO.m).footprint ⊔
      (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Redo.prefixes).footprint ⊔ C.footprint ⊔ (ROhandle.RO.m).footprint ⊔
      (ROhandle.FRO.m).footprint)ᶜ)
    (G : Footprint VariableAssignment)
    (_hGd : G ≤ ((PF.m).footprint ⊔ (PF.mi).footprint ⊔ (F.RO.m).footprint ⊔
      (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Redo.prefixes).footprint ⊔ C.footprint ⊔ (ROhandle.RO.m).footprint ⊔
      (ROhandle.FRO.m).footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ Gᶜ →
      FVP.fvP P ≤ Gᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless) :
    prhlProc
      (fun _ g₁ _ g₂ => (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (CF (DRestr D)).procedure (G1 (DRestr D)).procedure
      (fun r₁ _ r₂ g₂ => ¬ (G1.bcol.get g₂ = true ∨ G1.bext.get g₂ = true) → r₁ = r₂) := by
  unfold C.footprint at _hDd _hGd
  have hcc : (C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hcq : (C.queries).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hpm : (PF.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hpmi : (PF.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hpre : (Redo.prefixes).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hfro : (FRO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hch : (G1.chandle).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hm : (G1.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hmi : (G1.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hmh : (G1.mh).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hmhi : (G1.mhi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hro : (F.RO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hpa : (G1.paths).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hbc : (G1.bcol).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hbx : (G1.bext).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      (try unfold C.footprint); fp_mem)))
  have hGv : ∀ {X : Footprint VariableAssignment}, X ≤ PF.m.footprint ⊔ PF.mi.footprint ⊔
      F.RO.m.footprint ⊔ G1.m.footprint ⊔ G1.mi.footprint ⊔ G1.mh.footprint ⊔ G1.mhi.footprint ⊔
      G1.chandle.footprint ⊔ G1.paths.footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      Redo.prefixes.footprint ⊔ (C.c.footprint ⊔ C.queries.footprint) ⊔
      ROhandle.RO.m.footprint ⊔ ROhandle.FRO.m.footprint → X ≤ Gᶜ :=
    fun hX => hX.trans ((Footprint.le_compl_comm _ _).mp _hGd)
  have hL : FVP.fvP D ≤ (cfL.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [cfL, Footprint.lens_pair]
    exact sup_le hcc (sup_le hcq (sup_le hpm (sup_le hpmi (sup_le hpre (sup_le hfro (sup_le hch
      (sup_le hm (sup_le hmi (sup_le hmh (sup_le hmhi (sup_le hro (sup_le hpa
        (sup_le hbc hbx)))))))))))))
  unfold CF G1 PF
  equiv_proc
  repeat stmt_inline{2} 0
  repeat stmt_inline{1} 0
  rw [PF_eta, view_PF_eq]
  stmt_wp
  equiv_seq 1 1 : (syncInv cfL (FVP.fvP D) cfI cfBad §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    refine ⟨?_, (cfI_iff _ _).mpr ?_, ?_⟩
    · simp only [touched_set_of_le_compl hcc, touched_set_of_le_compl hcq,
        touched_set_of_le_compl hpm, touched_set_of_le_compl hpmi, touched_set_of_le_compl hpre,
        touched_set_of_le_compl hfro, touched_set_of_le_compl hch, touched_set_of_le_compl hm,
        touched_set_of_le_compl hmi, touched_set_of_le_compl hmh, touched_set_of_le_compl hmhi,
        touched_set_of_le_compl hro, touched_set_of_le_compl hpa, touched_set_of_le_compl hbc,
        touched_set_of_le_compl hbx]
      exact h
    · simp only [eq_glob_C, INV_CF_G1_12]
      simp_reads
      exact INV_CF_G1_init
    · simp only [cfBad]
      simp_reads
      simp
  · stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_upto_module cfL D distExt hD.representable
      (FVP.fvP D) le_rfl hL ?hc cfBad cfI cfQ _ _ ?hll₁ ?hll₂ ?horacle ?hQ₁ ?hQ₂) ?_
    case hc =>
      intro _ n
      cases n with
      | zero => exact inferInstanceAs (Countable (List block))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable state)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable state)
          | succ n => nomatch n
    case hll₁ =>
      exact D_ll _ _ (by fp_disj') (by fp_disj')
        (rp_ll _ (by fp_disj') (by rw [Indifferentiability.PRIMITIVE.view_f]; exact PF_f_ll))
        (rpi_ll _ (by fp_disj') (by rw [Indifferentiability.PRIMITIVE.view_fi]; exact PF_fi_ll))
        (rf_ll' _ (SqueezelessSponge_f_ll _
          (by rw [Indifferentiability.PRIMITIVE.view_f]; exact PF_f_ll)))
    case hll₂ =>
      exact D_ll _ _ ((FVP.fvP_app _ _).trans (sup_le (fvP_DFRestr.trans (hGv (by
          unfold C.footprint; fp_sub))) (fvP_G1M.trans (hGv (by
          simp only [Footprint.lens_pair]; fp_sub)))))
        ((FVP.fvP_app _ _).trans (sup_le (fvP_DPRestr.trans (hGv (by
          unfold C.footprint; fp_sub))) (fvP_G1S.trans (hGv (by
          simp only [Footprint.lens_pair]; fp_sub)))))
        (rp_ll _ (by fp_disj') G1_S_f_ll) (rpi_ll _ (by fp_disj') G1_S_fi_ll)
        (rf_ll' _ G1_M_f_ll)
    case horacle =>
      intro _ n
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair]
        unfold PF G1.M
        refine prhlProc_upto_of_writesKeep _ (by writes_keep') (by writes_keep')
          (prhlProc_conseq (PFf_Cf D) (fun a₁ g₁ a₂ g₂ ⟨ha, hI, hb⟩ => ⟨hb, ha, hI.1, hI.2⟩)
            (fun r₁ g₁ r₂ g₂ h => ?_))
        split_ifs at h with hb
        · exact Or.inl ⟨hb, h⟩
        · exact Or.inr ⟨h.2.1, ⟨h.1, h.2.2⟩, hb⟩
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair]
          unfold PF G1.S
          refine prhlProc_upto_of_writesKeep _ (by writes_keep') (by writes_keep')
            (prhlProc_conseq (eq_f D (_hDd.trans (Footprint.compl_antimono (by fp_sub))))
              (fun a₁ g₁ a₂ g₂ ⟨ha, hI, hb⟩ => ?_)
              (fun r₁ g₁ r₂ g₂ h => ?_))
          · simp only [cfBad_iff, not_or, Bool.not_eq_true] at hb
            exact ⟨hb.1, hb.2, ha, hI.1, hI.2⟩
          · split_ifs at h with hb
            · exact Or.inl ⟨hb, h⟩
            · exact Or.inr ⟨h.1, h.2, hb⟩
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair]
            unfold PF G1.S
            refine prhlProc_upto_of_writesKeep _ (by writes_keep') (by writes_keep')
              (prhlProc_conseq (eq_fi D (_hDd.trans (Footprint.compl_antimono (by fp_sub))))
                (fun a₁ g₁ a₂ g₂ ⟨ha, hI, hb⟩ => ?_)
                (fun r₁ g₁ r₂ g₂ h => ?_))
            · simp only [cfBad_iff, not_or, Bool.not_eq_true] at hb
              exact ⟨hb.1, hb.2, ha, hI.1, hI.2⟩
            · split_ifs at h with hb
              · exact Or.inl ⟨hb, h.2⟩
              · exact Or.inr ⟨h.1, h.2, hb⟩
          | succ n => nomatch n
    case hQ₁ =>
      intro _ n ω₂ _
      exact hoareProc_const _ _
    case hQ₂ =>
      intro _ n ω₁
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair]
        exact DFRestr_M_f_bad
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.snd_pair]
          exact DPRestr_S_f_bad
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.snd_pair]
            exact DPRestr_S_fi_bad
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨Or.inr ⟨rfl, h⟩, ?_⟩
    rintro r₁ g₁ r₂ g₂ hpost
    simp_reads
    intro hnb
    rcases hpost with ⟨hb, -⟩ | ⟨hr, -⟩
    · exact absurd ((cfBad_iff _).mp hb) hnb
    · exact hr

end AUX

section

variable (D : DISTINGUISHER)

/-- EC's `Real_G1`, for `declare module D <: DISTINGUISHER {-Perm, -C, -PF, -G1, -RO, -Redo}`
with the axiom `D_ll`.  `mu dstate (pred1 witness)` is the probability of `default`. -/
theorem Real_G1 (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ ((Perm.m).footprint ⊔
      (Perm.mi).footprint ⊔ C.footprint ⊔ (PF.m).footprint ⊔
      (PF.mi).footprint ⊔ (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔
      (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint ⊔ (F.RO.m).footprint ⊔ (Redo.prefixes).footprint ⊔
      (ROhandle.RO.m).footprint ⊔ (ROhandle.FRO.m).footprint)ᶜ)
    (G : Footprint VariableAssignment)
    (_hGd : G ≤ ((Perm.m).footprint ⊔
      (Perm.mi).footprint ⊔ C.footprint ⊔ (PF.m).footprint ⊔
      (PF.mi).footprint ⊔ (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔
      (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint ⊔ (F.RO.m).footprint ⊔ (Redo.prefixes).footprint ⊔
      (ROhandle.RO.m).footprint ⊔ (ROhandle.FRO.m).footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ Gᶜ →
      FVP.fvP P ≤ Gᶜ →
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
  have hR := Real_Concrete D hD
    (_hDd.trans (Footprint.compl_antimono (by (try unfold C.footprint); fp_sub)))
    G (_hGd.trans (Footprint.compl_antimono (by (try unfold C.footprint); fp_sub))) D_ll m
  have hC : Procedure.Pr (CF (DRestr D)).procedure () m (fun r _ => r = true) ≤
      Procedure.Pr (G1 (DRestr D)).procedure () m (fun r g => r = true ∨
        (G1.bcol.get g = true ∨ G1.bext.get g = true)) :=
    Procedure.Pr_le_of_prhlProc (CF_G1 D hD
      (_hDd.trans (Footprint.compl_antimono (by (try unfold C.footprint); fp_sub)))
      G (_hGd.trans (Footprint.compl_antimono (by (try unfold C.footprint); fp_sub))) D_ll)
      (fun r₁ g₁ r₂ g₂ hB h₁ => by
        by_cases hb : G1.bcol.get g₂ = true ∨ G1.bext.get g₂ = true
        · exact Or.inr hb
        · exact Or.inl (hB hb ▸ h₁))
      rfl
  have h1 := Procedure.Pr_or_le (G1 (DRestr D)).procedure () m (fun r _ => r = true)
    (fun _ g => G1.bcol.get g = true ∨ G1.bext.get g = true)
  have h2 := Procedure.Pr_or_le (G1 (DRestr D)).procedure () m (fun _ g => G1.bcol.get g = true)
    (fun _ g => G1.bext.get g = true)
  have hC' := NNReal.coe_le_coe.mpr (hC.trans (h1.trans (add_le_add le_rfl h2)))
  push_cast at hC'
  have e : ((max_size ^ 2 - max_size : ℤ) : ℝ) / 2 * (dstate.1 {default}).toReal =
      ((max_size ^ 2 - max_size : ℤ) : ℝ) * (2 : ℝ)⁻¹ * (dstate.1 {default}).toReal := by ring
  linarith

end

end GaudisCrypt.SHA3.Handle
