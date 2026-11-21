import GaudisCrypt.Examples.SHA3.SmartCounter.ConcreteF
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECCallUpto
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Logic.ECWhile
import GaudisCrypt.Logic.ECWhileRel
import GaudisCrypt.Logic.ECCallEquiv
import GaudisCrypt.Syntax.ModuleSubtype
import GaudisCrypt.Logic.ECSeq
import GaudisCrypt.Logic.ECInline
import GaudisCrypt.Logic.ECLoop
import GaudisCrypt.Logic.ECAlias
import GaudisCrypt.Logic.ECGoals
import GaudisCrypt.Logic.StmtSwap
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.FrameTactics
import GaudisCrypt.Logic.LoopTransform
import GaudisCrypt.Lib.EC.BitWordRing

/-!
# `Handle.eca`'s `CF_G1` in EC's form — the tactic experiment

EC's `CF_G1` (the game-level equivalence of `CF` and `G1` up to the bad events, through EC's
up-to-bad `call (_: bad, inv, inv')` over the distinguisher's three oracle procedures), stated and
proven as EC does, over the old port's declarations (section `FirstPort` below).  It drove the
tactics the SmartCounter files need (`notes/SHA3/Refactor.md`, phase 3): `equiv_call (_ : bad, I,
J)`, `glob D` in conditions, `equiv_conseq H`, `phoare_while I V`, `sp` keeping the precondition,
`glob_simp`.  The declarations move to EC's form with the port of `SLCommon`, `ConcreteF`,
`Handle`.

Deviations from EC's proof:
* the oracles' steps `eq_f`, `eq_fi`, `PFf_Cf` are the old port's (with its footprint hypothesis
  for `D`, discharged by `fp_disjoint`), and so is `INV_CF_G1_init` (EC's 18 `smt` calls);
* the right oracles' losslessness is one more goal each (exception E11);
* EC splits the right `C.f`'s judgment in a `hoare` (bad kept) and a lossless `phoare` (`conseq
  (: _ ==> true) (: _ ==> G1.bcol \/ G1.bext)`): here one `phoare_while` with the bad event and
  `J` in the invariant;
* EC's closers (`smt`, `/#`, `progress`) are `simp`, `split_ifs`, `omega`.
-/

section FirstPort

/-!
## Declarations of the first port

Definitions and plain lemmas of the first port of this file (2026-10/11) that the proofs below
use; its program-logic proofs are gone.

The first port's translation notes (some mention declarations that went with its proofs):
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
open GaudisCrypt.EC.BitWord (xorwA xorwK xorwC xorw0)

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
    b <- call D(G1.M, G1.S).distinguish ();
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

/-- EC's `lemma lemma1`, in EC's script. -/
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
  -- EC: move=> HINV x2_neq_y2 Pm_x Gm_x x2_notrngE1_hs y2_notrngE1_hs; split.
  intro HINV x2_neq_y2 Pm_x Gm_x x2_notrngE1_hs y2_notrngE1_hs
  constructor
  -- EC: + rewrite (@addzA ch 1 1); apply/hs_addh.
  · rw [show ch + 2 = ch + 1 + 1 by ring]; apply hs_addh
    -- EC: + by move: HINV=> /hs_of_INV/hs_addh=> ->.
    · exact hs_addh _ _ _ _ (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV) x2_notrngE1_hs
    -- EC: by move=> f h; rewrite get_setE; case: (h = ch)=> [/#|_]; exact/y2_notrngE1_hs.
    · intro f h; rw [FMap.get_setE]; split_ifs; · simp [x2_neq_y2]
      exact y2_notrngE1_hs f h
  -- EC: + apply/inv_addm=> //; 1:by case: HINV.
  · refine inv_addm _ _ _ _ (by cases HINV; assumption) Gm_x ?_
    -- EC: case: {-1}(Gmi.[(y1,y2)]) (eq_refl Gmi.[(y1,y2)])=> [//|[xa xc]].
    rcases h : FMap.get Gmi (y1, y2) with _ | ⟨xa, xc⟩; · rfl
    -- EC: + have /incli_of_INV @/incl + ^h - <- := HINV; 1: by rewrite h.
    have hi := incli_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV (y1, y2) (by simp [h])
    rw [h] at hi
    -- EC: have /mi_mhi_of_INV [] H _ /H {H} [hx fx hy fy] [#] := HINV.
    obtain ⟨H, -⟩ := mi_mhi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    obtain ⟨hx, fx, hy, fy, hs_hx, -, -⟩ := H _ _ _ _ hi
    -- EC: by rewrite y2_notrngE1_hs.
    exact absurd hs_hx (y2_notrngE1_hs _ _)
  -- EC: + apply/inv_addm; 1:by case: HINV.
  · apply inv_addm; · cases HINV; assumption
    -- EC: + have ^ /m_mh_of_INV Hm_mh /hs_of_INV Hhs := HINV.
    --       by apply/(ch_notdomE2_mh _ _ Hm_mh Hhs).
    · exact ch_notdomE2_mh _ _ _ _ _ (m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
        (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
    -- EC: have ^ /mi_mhi_of_INV Hmi_mhi /hs_of_INV Hhs := HINV.
    --     by apply/(Sch_notdomE2_mh _ _ Hmi_mhi Hhs).
    exact Sch_notdomE2_mh _ _ _ _ _ (mi_mhi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
      (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
  -- EC: + apply/(@m_mh_addh_addm hs.[ch <- (x2,Known)] Pm mh ch x1 x2 (ch + 1) y1 y2 Known).
  · apply m_mh_addh_addm (FMap.set hs ch (x2, Known)) Pm mh ch x1 x2 (ch + 1) y1 y2 Known
    -- EC: + by move: HINV=> ^/hs_of_INV Hhs /m_mh_of_INV; exact/(m_mh_addh Hhs).
    · exact m_mh_addh _ _ _ _ _ _ (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
        (m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
    -- EC: + by move: HINV => /hs_of_INV /hs_addh /(_ x2 Known _) // [].
    · exact (hs_addh _ _ x2 Known (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV) x2_notrngE1_hs).1
    -- EC: + by rewrite get_setE.
    · simp
    -- EC: by rewrite get_setE gtr_eqF 1:/# /=; apply/Sch_notdomE_hs; case: HINV.
    · rw [FMap.get_set_neqE _ ch (ch + 1) _ (by simp)]
      exact Sch_notdomE_hs _ _ (by cases HINV; assumption)
  -- EC: + apply/(@mi_mhi_addh_addmi hs.[ch <- (x2,Known)] Pmi mhi ch x1 x2 (ch + 1) y1 y2
  --       Known Known).
  · apply mi_mhi_addh_addmi (FMap.set hs ch (x2, Known)) Pmi mhi ch x1 x2 (ch + 1) y1 y2
      Known Known
    -- EC: + by move: HINV=> ^/hs_of_INV Hhs /mi_mhi_of_INV; exact/(m_mh_addh Hhs).
    · exact m_mh_addh _ _ _ _ _ _ (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
        (mi_mhi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
    -- EC: + move=> f h; rewrite get_setE; case: (h = ch)=> [_ //=|_ //=];
    --       first by rewrite x2_neq_y2.
    --     by rewrite y2_notrngE1_hs.
    · intro f h; rw [FMap.get_setE]; split_ifs; · simp [x2_neq_y2]
      exact y2_notrngE1_hs f h
    -- EC: + by rewrite get_setE.
    · simp
    -- EC: by rewrite get_setE gtr_eqF 1:/# /=; apply/Sch_notdomE_hs; case: HINV.
    · rw [FMap.get_set_neqE _ ch (ch + 1) _ (by simp)]
      exact Sch_notdomE_hs _ _ (by cases HINV; assumption)
  -- EC: + by apply/incl_addm; case: HINV.
  · exact incl_addm _ _ _ _ (by cases HINV; assumption)
  -- EC: + by apply/incl_addm; case: HINV.
  · exact incl_addm _ _ _ _ (by cases HINV; assumption)
  -- EC: + split.
  · constructor
    -- EC: + move=> xa hx ya hy; rewrite get_setE; case: ((xa,hx) = (x1,ch))=> [|].
    · intro xa hx ya hy; rw [FMap.get_setE]; split_ifs with hk
      -- EC: + by move=> [#] <*> [#] <*>; exists x2 Known y2 Known; rewrite !get_setE /#.
      · intro he; obtain ⟨h1, h2⟩ := Prod.mk.inj hk
        obtain ⟨h3, h4⟩ := Prod.mk.inj (Option.some.inj he); subst xa hx ya hy
        exact ⟨x2, Known, y2, Known, by simp [FMap.get_setE], by simp, by simp⟩
      -- EC: move=> xahx_neq_x1ch; have ^ /hs_of_INV Hhs /mh_of_INV [] Hmh _ _ /Hmh {Hmh} := HINV.
      intro hm
      have Hhs := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      obtain ⟨Hmh, -, -⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      -- EC: move=> [xc fx yc fy] [#] hs_hx hs_hy Hite.
      obtain ⟨xc, fx, yc, fy, hs_hx, hs_hy, Hite⟩ := Hmh _ _ _ _ hm
      -- EC: exists xc fx yc fy; do 2?split; first 2 by smt (dom_hs_neq_ch dom_hs_neq_Sch get_setE).
      refine ⟨xc, fx, yc, fy, ?_, ?_, ?_⟩
      on_goals 1, 2 => smt_close [dom_hs_neq_ch, dom_hs_neq_Sch, FMap.get_setE]
      -- EC: case: fy Hite hs_hy=> /= [[p v] [Hro Hpath] hs_hy|[#] Gm_xaxc <*> hs_hy] /=;
      --       last first.
      cases fy with
      | Known =>
        obtain ⟨Gm_xaxc, rfl⟩ := by simpa using Hite
        -- EC: + by rewrite get_setE; case: ((xa,xc) = (x1,x2))=> [/#|].
        rw [if_pos rfl, FMap.get_setE]; split_ifs with he
        · rw [he, Gm_x] at Gm_xaxc; cases Gm_xaxc
        exact ⟨Gm_xaxc, rfl⟩
      | Unknown =>
        obtain ⟨p, v, Hro, Hpath⟩ := by simpa using Hite
        -- EC: exists p v; rewrite Hro /=; apply/build_hpath_up=> //.
        rw [if_neg (by decide)]
        refine ⟨p, v, Hro, build_hpath_up _ _ _ _ _ _ _ _ Hpath ?_⟩
        -- EC: have /m_mh_of_INV /notin_hs_notdomE2_mh H:= HINV.
        --     exact/H/ch_notdomE_hs/Hhs.
        exact notin_hs_notdomE2_mh _ _ _ _ _ (m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
          (ch_notdomE_hs _ _ Hhs)
    -- EC: + move=> p xa b; have /mh_of_INV [] _ -> _ := HINV.
    · intro p xa b
      obtain ⟨-, Hro, -⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      rw [Hro]
      -- EC: apply/exists_iff=> v /=; apply/exists_iff=> hx /=; apply/exists_iff=> hy /=.
      refine exists_congr fun v => exists_congr fun hx => exists_congr fun hy => ?_
      -- EC: have mh_x1ch: mh.[(x1,ch)] = None.
      --     + by apply/(notin_hs_notdomE2_mh hs Pm)/ch_notdomE_hs; case: HINV.
      have mh_x1ch : FMap.get mh (x1, ch) = none :=
        notin_hs_notdomE2_mh hs Pm _ _ _ (by cases HINV; assumption)
          (ch_notdomE_hs _ _ (by cases HINV; assumption))
      -- EC: have ch_notrngE2_mh: forall a h a', mh.[(a,h)] <> Some (a',ch).
      --     + move=> a h a'; rewrite -negP; have /m_mh_of_INV [] _ Hmh_m /Hmh_m {Hmh_m} := HINV.
      --       by move=> [xc fx yc fy] [#] _; rewrite ch_notdomE_hs; case: HINV.
      have ch_notrngE2_mh : ∀ a h a', FMap.get mh (a, h) ≠ some (a', ch) := by
        intro a h a' hm
        obtain ⟨-, Hmh_m⟩ := m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        obtain ⟨xc, fx, yc, fy, -, hs_ch, -⟩ := Hmh_m _ _ _ _ hm
        rw [ch_notdomE_hs _ _ (by cases HINV; assumption)] at hs_ch; cases hs_ch
      -- EC: split=> -[#].
      constructor
      -- EC: + move=> Hpath mh_vxahx; rewrite get_setE; case: ((v +^ xa,hx) = (x1,ch))=> [/#|_].
      · rintro ⟨Hpath, mh_vxahx⟩
        rw [FMap.get_setE]; split_ifs with he
        · rw [he, mh_x1ch] at mh_vxahx; cases mh_vxahx
        -- EC: by rewrite mh_vxahx //=; apply/build_hpath_up=> //=; rewrite mh_x1ch.
        exact ⟨build_hpath_up _ _ _ _ _ _ _ _ Hpath mh_x1ch, mh_vxahx⟩
      -- EC: have H /H {H}:= build_hpath_down mh x1 ch y1 (ch + 1) p v hx _.
      rintro ⟨Hpath', mh_vxahx'⟩
      have Hpath := build_hpath_down mh x1 ch y1 (ch + 1) p v hx ?_ Hpath'
      -- EC: move=> ^ /build_hpathP + -> /=; rewrite get_setE.
      --     by case=> [<*>|/#]; move: HINV=> /hs_of_INV [] _ + H - /H {H} /#.
      · refine ⟨Hpath, ?_⟩
        rw [FMap.get_setE] at mh_vxahx'; split_ifs at mh_vxahx' with he; rotate_right
        · exact mh_vxahx'
        rcases (build_hpathP _ _ _ _).1 Hpath with ⟨-, -, rfl⟩ | ⟨p', b', v', h', -, -, hm⟩
        · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
          have := Hlt _ _ h0; have := (Prod.mk.inj he).2; linarith
        · exact absurd ((Prod.mk.inj he).2 ▸ hm) (ch_notrngE2_mh _ _ _)
      -- EC: + move=> p0 v0; rewrite -negP=> /build_hpathP [<*>|].
      intro p0 v0 hp
      rcases (build_hpathP _ _ _ _).1 hp with ⟨-, -, hch⟩ | ⟨p', b', v', h', -, -, hm⟩
      -- EC: + by have /hs_of_INV [] _ + H - /H {H} := HINV.
      · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        have := Hlt _ _ h0; linarith
      -- EC: by move=> p' b' v' h' <*>; rewrite ch_notrngE2_mh.
      · exact ch_notrngE2_mh _ _ _ hm
    -- EC: move=> p v p' v' hx.
    intro p v p' v' hx
    -- EC: have: (forall p v, build_hpath mh p <> Some (v,ch)).
    have nopath : ∀ p0 v0, build_hpath mh p0 ≠ some (v0, ch) := by
      -- EC: + move=> p0 v0; rewrite -negP=> /build_hpathP [<*>|].
      intro p0 v0 hp
      rcases (build_hpathP _ _ _ _).1 hp with ⟨-, -, hch⟩ | ⟨p'0, b'0, v'0, h'0, -, -, hm⟩
      -- EC: + by have /hs_of_INV [] _ + H - /H {H} := HINV.
      · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        have := Hlt _ _ h0; linarith
      -- EC: move=> p'0 b'0 v'0 h'0 <*> _; have /m_mh_of_INV [] _ H /H {H} := HINV.
      --     by move=> [xc fx yc fy] [#] _; have /hs_of_INV [] _ _ H /H {H}:= HINV.
      · obtain ⟨-, H⟩ := m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        obtain ⟨xc, fx, yc, fy, -, hs_ch, -⟩ := H _ _ _ _ hm
        obtain ⟨-, -, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        have := Hlt _ _ hs_ch; linarith
    -- EC: move=> ^ + /build_hpath_down H /H {H} - /build_hpath_down H + /H {H}.
    --     by have /mh_of_INV [] _ _ /(_ p v p' v' hx) := HINV.
    intro h1 h2
    obtain ⟨-, -, Huniq⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    exact Huniq p v p' v' hx (build_hpath_down _ _ _ _ _ _ _ _ nopath h1)
      (build_hpath_down _ _ _ _ _ _ _ _ nopath h2)
  -- EC: split=> c p v; have ^/hs_of_INV [] _ _ dom_hs /pi_of_INV [] -> := HINV.
  · refine ⟨fun c p v => ?_⟩
    obtain ⟨-, -, dom_hs⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    obtain ⟨Ipi⟩ := pi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    rw [Ipi]
    -- EC: apply/exists_iff=> h /=; split=> [#].
    refine exists_congr fun h => ?_
    constructor
    -- EC: + move=> /(build_hpath_up mh x1 ch y1 (ch + 1) p v h) /(_ _).
    --       + by apply/(notin_hs_notdomE2_mh hs Pm)/ch_notdomE_hs; case: HINV.
    --       by move=> -> /= ^ /dom_hs; rewrite !get_setE /#.
    · rintro ⟨Hpath, hs_h⟩
      refine ⟨build_hpath_up mh x1 ch y1 (ch + 1) p v h Hpath
        (notin_hs_notdomE2_mh hs Pm _ _ _ (by cases HINV; assumption)
          (ch_notdomE_hs _ _ (by cases HINV; assumption))), ?_⟩
      have := dom_hs _ _ hs_h
      rw [FMap.get_set_neqE _ (ch + 1) h _ (ne_of_lt (by linarith)),
        FMap.get_set_neqE _ ch h _ this.ne, hs_h]
    -- EC: have ch_notrngE2_mh: forall a h a', mh.[(a,h)] <> Some (a',ch). (…)
    --     have Sch_notrngE2_mh: forall a h a', mh.[(a,h)] <> Some (a',ch + 1). (…)
    rintro ⟨Hpath', hs_h⟩
    have ch_notrngE2_mh : ∀ a h a', FMap.get mh (a, h) ≠ some (a', ch) := by
      intro a h' a' hm
      obtain ⟨-, Hmh_m⟩ := m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      obtain ⟨xc, fx, yc, fy, -, hs_ch, -⟩ := Hmh_m _ _ _ _ hm
      rw [ch_notdomE_hs _ _ (by cases HINV; assumption)] at hs_ch; cases hs_ch
    have Sch_notrngE2_mh : ∀ a h a', FMap.get mh (a, h) ≠ some (a', ch + 1) := by
      intro a h' a' hm
      obtain ⟨-, Hmh_m⟩ := m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      obtain ⟨xc, fx, yc, fy, -, hs_Sch, -⟩ := Hmh_m _ _ _ _ hm
      rw [Sch_notdomE_hs _ _ (by cases HINV; assumption)] at hs_Sch; cases hs_Sch
    -- EC: have H /H {H}:= build_hpath_down mh x1 ch y1 (ch + 1) p v h _.
    have Hpath := build_hpath_down mh x1 ch y1 (ch + 1) p v h ?_ Hpath'
    -- EC: + move=> ^ /build_hpathP + -> /=; rewrite !get_setE.
    --       by case=> [<*>|/#]; move: HINV=> /hs_of_INV [] _ + H - /H {H} /#.
    · refine ⟨Hpath, ?_⟩
      rcases (build_hpathP _ _ _ _).1 Hpath with ⟨-, -, rfl⟩ | ⟨p', b', v', h', -, -, hm⟩
      · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        have := Hlt _ _ h0
        rwa [FMap.get_set_neqE _ (ch + 1) 0 _ (ne_of_lt (by linarith)),
          FMap.get_set_neqE _ ch 0 _ this.ne] at hs_h
      · rwa [FMap.get_set_neqE _ _ _ _ (fun e => Sch_notrngE2_mh _ _ _ (e ▸ hm)),
          FMap.get_set_neqE _ _ _ _ (fun e => ch_notrngE2_mh _ _ _ (e ▸ hm))] at hs_h
    -- EC: + move=> p0 v0; rewrite -negP=> /build_hpathP [<*>|].
    --       + by have /hs_of_INV [] _ + H - /H {H} := HINV.
    --       by move=> p' b' v' h' <*>; rewrite ch_notrngE2_mh.
    intro p0 v0 hp
    rcases (build_hpathP _ _ _ _).1 hp with ⟨-, -, hch⟩ | ⟨p', b', v', h', -, -, hm⟩
    · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      have := Hlt _ _ h0; linarith
    · exact ch_notrngE2_mh _ _ _ hm
  -- EC: split=>[].
  · constructor
    -- EC: + by case:HINV=>_ _ _ _ _ _ _ _ (* _ *) [] _ [] ->//.
    · obtain ⟨c1, -, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c1
    -- EC: + by case:HINV=>_ _ _ _ _ _ _ _ (* _ *) [] _ [] //.
    · obtain ⟨-, c2, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c2
    -- EC: + move=>l hmem i hi.
    · intro l hmem i hi
      -- EC: have[]_ _ h2 h3:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV.
      obtain ⟨-, -, h2, h3, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      -- EC: have[]sa sc[]:=h2 l hmem i hi.
      obtain ⟨sa, sc, h4, h5⟩ := h2 l hmem i hi
      -- EC: have h1:=all_prefixes_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV.
      have h1 := all_prefixes_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      -- EC: smt(domE get_setE).
      refine ⟨sa, sc, h4, ?_⟩
      rw [FMap.get_setE, if_neg]; · exact h5
      intro he; rw [he, Pm_x] at h5
      exact (FMap.domE _ _).1 (h1 l hmem (i + 1)) h5.symm
    -- EC: by case:HINV=>_ _ _ _ _ _ _ _ _ [].
    · obtain ⟨-, -, -, c4, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c4
    -- EC: by case:HINV=>_ _ _ _ _ _ _ _ _ [].
    · obtain ⟨-, -, -, -, c5⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c5

/-- EC's `lemma lemma1'`, in EC's script. -/
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
  -- EC: move=> HINV hh x2_neq_y2 Pm_x Gm_x xc_notrngE1_hs yc_notrngE1_hs; split.
  intro HINV hh x2_neq_y2 Pm_x Gm_x xc_notrngE1_hs yc_notrngE1_hs
  constructor
  -- EC: + rewrite (@addzA ch 1 1); apply/hs_addh.
  · rw [show ch + 2 = ch + 1 + 1 by ring]; apply hs_addh
    -- EC: + by move: HINV=> /hs_of_INV/hs_addh=> ->.
    · exact hs_addh _ _ _ _ (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV) xc_notrngE1_hs
    -- EC: by move=> f h; rewrite get_setE; case: (h = ch)=> [/#|_]; exact/yc_notrngE1_hs.
    · intro f h; rw [FMap.get_setE]; split_ifs; · simp [x2_neq_y2]
      exact yc_notrngE1_hs f h
  -- EC: + apply/inv_addm=> //; 1:by case: HINV.
  · refine inv_addm _ _ _ _ (by cases HINV; assumption) ?_ Gm_x
    -- EC: case: {-1}(Gm.[(y1,y2)]) (eq_refl Gm.[(y1,y2)])=> [//|[xa xc]].
    rcases h : FMap.get Gm (y1, y2) with _ | ⟨xa, xc⟩; · rfl
    -- EC: + have /incl_of_INV + ^h - <- := HINV; 1: by rewrite h.
    have hi := incl_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV (y1, y2) (by simp [h])
    rw [h] at hi
    -- EC: have /m_mh_of_INV [] H _ /H {H} [hx fx hy fy] [#] := HINV.
    obtain ⟨H, -⟩ := m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    obtain ⟨hx, fx, hy, fy, hs_hx, -, -⟩ := H _ _ _ _ hi
    -- EC: by rewrite yc_notrngE1_hs.
    exact absurd hs_hx (yc_notrngE1_hs _ _)
  -- EC: + apply/inv_addm; 1:by case: HINV.
  · apply inv_addm; · cases HINV; assumption
    -- EC: + have ^ /m_mh_of_INV Hm_mh /hs_of_INV Hhs := HINV.
    --       by apply/(Sch_notdomE2_mh _ _ Hm_mh Hhs).
    · exact Sch_notdomE2_mh _ _ _ _ _ (m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
        (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
    -- EC: have ^ /mi_mhi_of_INV Hmi_mhi /hs_of_INV Hhs := HINV.
    --     by apply/(ch_notdomE2_mh _ _ Hmi_mhi Hhs).
    exact ch_notdomE2_mh _ _ _ _ _ (mi_mhi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
      (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
  -- EC: + apply/(@mi_mhi_addh_addmi hs.[ch <- (x2,Known)] Pm mh ch x1 x2 (ch + 1) y1 y2
  --       Known Known).
  · apply mi_mhi_addh_addmi (FMap.set hs ch (x2, Known)) Pm mh ch x1 x2 (ch + 1) y1 y2 Known Known
    -- EC: + by move: HINV=> ^/hs_of_INV Hhs /m_mh_of_INV; exact/(m_mh_addh Hhs).
    · exact m_mh_addh _ _ _ _ _ _ (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
        (m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
    -- EC: + by move=> f h; rewrite get_setE; case: (h = ch)=> [<*> /#|]; rewrite yc_notrngE1_hs.
    · intro f h; rw [FMap.get_setE]; split_ifs; · simp [x2_neq_y2]
      exact yc_notrngE1_hs f h
    -- EC: + by rewrite get_setE.
    · simp
    -- EC: by rewrite get_setE gtr_eqF 1:/# /=; apply/Sch_notdomE_hs; case: HINV.
    · rw [FMap.get_set_neqE _ ch (ch + 1) _ (by simp)]
      exact Sch_notdomE_hs _ _ (by cases HINV; assumption)
  -- EC: + apply/(@m_mh_addh_addm hs.[ch <- (x2,Known)] Pmi mhi ch x1 x2 (ch + 1) y1 y2 Known).
  · apply m_mh_addh_addm (FMap.set hs ch (x2, Known)) Pmi mhi ch x1 x2 (ch + 1) y1 y2 Known
    -- EC: + by move: HINV=> ^/hs_of_INV Hhs /mi_mhi_of_INV; exact/(m_mh_addh Hhs).
    · exact m_mh_addh _ _ _ _ _ _ (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
        (mi_mhi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
    -- EC: + by have /hs_of_INV /hs_addh /(_ x2 Known _) // []:= HINV.
    · exact (hs_addh _ _ x2 Known (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV) xc_notrngE1_hs).1
    -- EC: + by rewrite get_setE.
    · simp
    -- EC: by rewrite get_setE gtr_eqF 1:/# /=; apply/Sch_notdomE_hs; case: HINV.
    · rw [FMap.get_set_neqE _ ch (ch + 1) _ (by simp)]
      exact Sch_notdomE_hs _ _ (by cases HINV; assumption)
  -- EC: + by apply/incl_addm; case: HINV.
  · exact incl_addm _ _ _ _ (by cases HINV; assumption)
  -- EC: + by apply/incl_addm; case: HINV.
  · exact incl_addm _ _ _ _ (by cases HINV; assumption)
  -- EC: + split.
  · constructor
    -- EC: + move=> ya hy xa hx; rewrite get_setE; case: ((ya,hy) = (y1,ch + 1))=> [|].
    · intro ya hy xa hx; rw [FMap.get_setE]; split_ifs with hk
      -- EC: + by move=> [#] <*> [#] <*>; exists y2 Known x2 Known; rewrite !get_setE /#.
      · intro he; obtain ⟨h1, h2⟩ := Prod.mk.inj hk
        obtain ⟨h3, h4⟩ := Prod.mk.inj (Option.some.inj he); subst ya hy xa hx
        exact ⟨y2, Known, x2, Known, by simp, by simp [FMap.get_setE], by simp⟩
      -- EC: move=> yahy_neq_y1Sch; have ^ /hs_of_INV Hhs /mh_of_INV [] Hmh _ _ /Hmh {Hmh} := HINV.
      intro hm
      have Hhs := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      obtain ⟨Hmh, -, -⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      -- EC: move=> [yc fy xc fx] [#] hs_hy hs_hx Hite.
      obtain ⟨yc, fy, xc, fx, hs_hy, hs_hx, Hite⟩ := Hmh _ _ _ _ hm
      -- EC: exists yc fy xc fx; do 2?split; first 2 by smt (dom_hs_neq_ch dom_hs_neq_Sch get_setE).
      refine ⟨yc, fy, xc, fx, ?_, ?_, ?_⟩
      on_goals 1, 2 => smt_close [dom_hs_neq_ch, dom_hs_neq_Sch, FMap.get_setE]
      -- EC: case: fx Hite hs_hx=> /= [[p v] [Hro Hpath] hs_hx|[#] Gm_yayc <*> hs_hx] /=;
      --       last first.
      cases fx with
      | Known =>
        obtain ⟨Gm_yayc, rfl⟩ := by simpa using Hite
        -- EC: + by rewrite get_setE; case: ((ya,yc) = (y1,y2))=> [/#|].
        rw [if_pos rfl, FMap.get_setE]; split_ifs with he
        · rw [he] at Gm_yayc
          have := incl_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV (y1, y2) (by simp [Gm_yayc])
          exact absurd ((FMap.domE _ _).2 (by simp [this, Gm_yayc])) hh
        exact ⟨Gm_yayc, rfl⟩
      | Unknown =>
        obtain ⟨p, v, Hro, Hpath⟩ := by simpa using Hite
        -- EC: exists p v; rewrite Hro /=; apply/build_hpath_up=> //.
        rw [if_neg (by decide)]
        refine ⟨p, v, Hro, build_hpath_up _ _ _ _ _ _ _ _ Hpath ?_⟩
        -- EC: have /m_mh_of_INV /notin_hs_notdomE2_mh H:= HINV.
        --     exact/H/Sch_notdomE_hs/Hhs.
        exact notin_hs_notdomE2_mh _ _ _ _ _ (m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
          (Sch_notdomE_hs _ _ Hhs)
    -- EC: + move=> p ya b; have /mh_of_INV [] _ -> _ := HINV.
    · intro p ya b
      obtain ⟨-, Hro, -⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      rw [Hro]
      -- EC: apply/exists_iff=> v /=; apply/exists_iff=> hx /=; apply/exists_iff=> hy /=.
      refine exists_congr fun v => exists_congr fun hx => exists_congr fun hy => ?_
      -- EC: have mh_y1Sch: mh.[(y1,ch + 1)] = None.
      --     + by apply/(notin_hs_notdomE2_mh hs Pm)/Sch_notdomE_hs; case: HINV.
      have mh_y1Sch : FMap.get mh (y1, ch + 1) = none :=
        notin_hs_notdomE2_mh hs Pm _ _ _ (by cases HINV; assumption)
          (Sch_notdomE_hs _ _ (by cases HINV; assumption))
      -- EC: have Sch_notrngE2_mh: forall a h a', mh.[(a,h)] <> Some (a',ch + 1).
      --     + move=> a h a'; rewrite -negP; have /m_mh_of_INV [] _ Hmh_m /Hmh_m {Hmh_m} := HINV.
      --       by move=> [yc fy xc fx] [#] _; rewrite Sch_notdomE_hs; case: HINV.
      have Sch_notrngE2_mh : ∀ a h a', FMap.get mh (a, h) ≠ some (a', ch + 1) := by
        intro a h a' hm
        obtain ⟨-, Hmh_m⟩ := m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        obtain ⟨yc, fy, xc, fx, -, hs_Sch, -⟩ := Hmh_m _ _ _ _ hm
        rw [Sch_notdomE_hs _ _ (by cases HINV; assumption)] at hs_Sch; cases hs_Sch
      -- EC: split=> -[#].
      constructor
      -- EC: + move=> Hpath mh_vxahx; rewrite get_setE; case: ((v +^ ya,hx) = (y1,ch + 1))=> [/#|_].
      · rintro ⟨Hpath, mh_vxahx⟩
        rw [FMap.get_setE]; split_ifs with he
        · rw [he, mh_y1Sch] at mh_vxahx; cases mh_vxahx
        -- EC: by rewrite mh_vxahx //=; apply/build_hpath_up=> //=; rewrite mh_y1ch.
        exact ⟨build_hpath_up _ _ _ _ _ _ _ _ Hpath mh_y1Sch, mh_vxahx⟩
      -- EC: have H /H {H}:= build_hpath_down mh y1 (ch + 1) x1 ch p v hx _.
      rintro ⟨Hpath', mh_vxahx'⟩
      have Hpath := build_hpath_down mh y1 (ch + 1) x1 ch p v hx ?_ Hpath'
      -- EC: move=> ^ /build_hpathP + -> /=; rewrite get_setE.
      --     by case=> [<*>|/#]; move: HINV=> /hs_of_INV [] _ + H - /H {H} /#.
      · refine ⟨Hpath, ?_⟩
        rw [FMap.get_setE] at mh_vxahx'; split_ifs at mh_vxahx' with he; rotate_right
        · exact mh_vxahx'
        rcases (build_hpathP _ _ _ _).1 Hpath with ⟨-, -, rfl⟩ | ⟨p', b', v', h', -, -, hm⟩
        · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
          have := Hlt _ _ h0; have := (Prod.mk.inj he).2; linarith
        · exact absurd ((Prod.mk.inj he).2 ▸ hm) (Sch_notrngE2_mh _ _ _)
      -- EC: + move=> p0 v0; rewrite -negP=> /build_hpathP [<*>|].
      intro p0 v0 hp
      rcases (build_hpathP _ _ _ _).1 hp with ⟨-, -, hch⟩ | ⟨p', b', v', h', -, -, hm⟩
      -- EC: + by have /hs_of_INV [] _ + H - /H {H} /# := HINV.
      · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        have := Hlt _ _ h0; linarith
      -- EC: by move=> p' b' v' h' <*>; rewrite Sch_notrngE2_mh.
      · exact Sch_notrngE2_mh _ _ _ hm
    -- EC: move=> p v p' v' hx.
    intro p v p' v' hx
    -- EC: have: (forall p v, build_hpath mh p <> Some (v,ch + 1)).
    have nopath : ∀ p0 v0, build_hpath mh p0 ≠ some (v0, ch + 1) := by
      -- EC: + move=> p0 v0; rewrite -negP=> /build_hpathP [<*>|].
      intro p0 v0 hp
      rcases (build_hpathP _ _ _ _).1 hp with ⟨-, -, hch⟩ | ⟨p'0, b'0, v'0, h'0, -, -, hm⟩
      -- EC: + by have /hs_of_INV [] _ + H - /H {H} /# := HINV.
      · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        have := Hlt _ _ h0; linarith
      -- EC: move=> p'0 b'0 v'0 h'0 <*> _; have /m_mh_of_INV [] _ H /H {H} := HINV.
      --     by move=> [xc fx yc fy] [#] _; have /hs_of_INV [] _ _ H /H {H} /#:= HINV.
      · obtain ⟨-, H⟩ := m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        obtain ⟨xc, fx, yc, fy, -, hs_Sch, -⟩ := H _ _ _ _ hm
        obtain ⟨-, -, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        have := Hlt _ _ hs_Sch; linarith
    -- EC: move=> ^ + /build_hpath_down H /H {H} - /build_hpath_down H + /H {H}.
    --     by have /mh_of_INV [] _ _ /(_ p v p' v' hx) := HINV.
    intro h1 h2
    obtain ⟨-, -, Huniq⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    exact Huniq p v p' v' hx (build_hpath_down _ _ _ _ _ _ _ _ nopath h1)
      (build_hpath_down _ _ _ _ _ _ _ _ nopath h2)
  -- EC: split=> c p v; have ^/hs_of_INV [] _ _ dom_hs /pi_of_INV [] -> := HINV.
  · refine ⟨fun c p v => ?_⟩
    obtain ⟨-, -, dom_hs⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    obtain ⟨Ipi⟩ := pi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    rw [Ipi]
    -- EC: apply/exists_iff=> h /=; split=> [#].
    refine exists_congr fun h => ?_
    constructor
    -- EC: + move=> /(build_hpath_up mh y1 (ch + 1) x1 ch p v h) /(_ _).
    --       + by apply/(notin_hs_notdomE2_mh hs Pm)/Sch_notdomE_hs; case: HINV.
    --       by move=> -> /= ^ /dom_hs; rewrite !get_setE /#.
    · rintro ⟨Hpath, hs_h⟩
      refine ⟨build_hpath_up mh y1 (ch + 1) x1 ch p v h Hpath
        (notin_hs_notdomE2_mh hs Pm _ _ _ (by cases HINV; assumption)
          (Sch_notdomE_hs _ _ (by cases HINV; assumption))), ?_⟩
      have := dom_hs _ _ hs_h
      rw [FMap.get_set_neqE _ (ch + 1) h _ (ne_of_lt (by linarith)),
        FMap.get_set_neqE _ ch h _ this.ne, hs_h]
    -- EC: have ch_notrngE2_mh: forall a h a', mh.[(a,h)] <> Some (a',ch). (…)
    --     have Sch_notrngE2_mh: forall a h a', mh.[(a,h)] <> Some (a',ch + 1). (…)
    rintro ⟨Hpath', hs_h⟩
    have ch_notrngE2_mh : ∀ a h a', FMap.get mh (a, h) ≠ some (a', ch) := by
      intro a h' a' hm
      obtain ⟨-, Hmh_m⟩ := m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      obtain ⟨xc, fx, yc, fy, -, hs_ch, -⟩ := Hmh_m _ _ _ _ hm
      rw [ch_notdomE_hs _ _ (by cases HINV; assumption)] at hs_ch; cases hs_ch
    have Sch_notrngE2_mh : ∀ a h a', FMap.get mh (a, h) ≠ some (a', ch + 1) := by
      intro a h' a' hm
      obtain ⟨-, Hmh_m⟩ := m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      obtain ⟨xc, fx, yc, fy, -, hs_Sch, -⟩ := Hmh_m _ _ _ _ hm
      rw [Sch_notdomE_hs _ _ (by cases HINV; assumption)] at hs_Sch; cases hs_Sch
    -- EC: have H /H {H}:= build_hpath_down mh y1 (ch + 1) x1 ch p v h _.
    have Hpath := build_hpath_down mh y1 (ch + 1) x1 ch p v h ?_ Hpath'
    -- EC: + move=> ^ /build_hpathP + -> /=; rewrite !get_setE.
    --       by case=> [<*>|/#]; move: HINV=> /hs_of_INV [] _ + H - /H {H} /#.
    · refine ⟨Hpath, ?_⟩
      rcases (build_hpathP _ _ _ _).1 Hpath with ⟨-, -, rfl⟩ | ⟨p', b', v', h', -, -, hm⟩
      · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        have := Hlt _ _ h0
        rwa [FMap.get_set_neqE _ (ch + 1) 0 _ (ne_of_lt (by linarith)),
          FMap.get_set_neqE _ ch 0 _ this.ne] at hs_h
      · rwa [FMap.get_set_neqE _ _ _ _ (fun e => Sch_notrngE2_mh _ _ _ (e ▸ hm)),
          FMap.get_set_neqE _ _ _ _ (fun e => ch_notrngE2_mh _ _ _ (e ▸ hm))] at hs_h
    -- EC: + move=> p0 v0; rewrite -negP=> /build_hpathP [<*>|].
    --       + by have /hs_of_INV [] _ + H - /H {H} /# := HINV.
    --       by move=> p' b' v' h' <*>; rewrite Sch_notrngE2_mh.
    intro p0 v0 hp
    rcases (build_hpathP _ _ _ _).1 hp with ⟨-, -, hch⟩ | ⟨p', b', v', h', -, -, hm⟩
    · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      have := Hlt _ _ h0; linarith
    · exact Sch_notrngE2_mh _ _ _ hm
  -- EC: split=>[].
  · constructor
    -- EC: + by case:HINV=>_ _ _ _ _ _ _ _ (* _ *) [] _ [] ->//.
    · obtain ⟨c1, -, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c1
    -- EC: + by case:HINV=>_ _ _ _ _ _ _ _ (* _ *) [] _ [].
    · obtain ⟨-, c2, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c2
    -- EC: + move=>l hmem i hi.
    · intro l hmem i hi
      -- EC: have[]_ _ h2 h3:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV.
      obtain ⟨-, -, h2, h3, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      -- EC: have[]sa sc[]:=h2 l hmem i hi.
      obtain ⟨sa, sc, h4, h5⟩ := h2 l hmem i hi
      -- EC: have h1:=all_prefixes_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV.
      have h1 := all_prefixes_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      -- EC: smt(domE get_setE).
      refine ⟨sa, sc, h4, ?_⟩
      rw [FMap.get_setE, if_neg]; · exact h5
      intro he; rw [he] at h5
      have := (FMap.domE _ _).1 (h1 l hmem (i + 1)); rw [← h5] at this
      exact hh ((FMap.domE _ _).2 this)
    -- EC: by case:HINV=>_ _ _ _ _ _ _ _ _ [].
    · obtain ⟨-, -, -, c4, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c4
    -- EC: by case:HINV=>_ _ _ _ _ _ _ _ _ [].
    · obtain ⟨-, -, -, -, c5⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c5

/-- EC's `lemma lemma2`, in EC's script. -/
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
  -- EC: move=> HINV PFm_x1x2 G1m_x1x2 pi_x2 hs_hx y2_notrngE1_hs.
  intro HINV PFm_x1x2 G1m_x1x2 pi_x2 hs_hx y2_notrngE1_hs
  -- EC: split.
  constructor
  -- EC: + by apply/hs_addh=> //=; case: HINV.
  · exact hs_addh _ _ _ _ (by cases HINV; assumption) y2_notrngE1_hs
  -- EC: + apply/inv_addm=> //; 1:by case: HINV.
  · refine inv_addm _ _ _ _ (by cases HINV; assumption) G1m_x1x2 ?_
    -- EC: case: {-1}(G1mi.[(y1,y2)]) (eq_refl G1mi.[(y1,y2)])=> [//|[xa xc]].
    rcases h : FMap.get G1mi (y1, y2) with _ | ⟨xa, xc⟩; · rfl
    -- EC: + have /incli_of_INV @/incl + ^h - <- := HINV; 1: by rewrite h.
    have hi := incli_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV (y1, y2) (by simp [h])
    rw [h] at hi
    -- EC: have /mi_mhi_of_INV [] H _ /H {H} [hx' fx' hy' fy'] [#] := HINV.
    obtain ⟨H, -⟩ := mi_mhi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    obtain ⟨hx', fx', hy', fy', hs_hx', -, -⟩ := H _ _ _ _ hi
    -- EC: by rewrite y2_notrngE1_hs.
    exact absurd hs_hx' (y2_notrngE1_hs _ _)
  -- EC: + apply/inv_addm; 1:by case: HINV.
  · apply inv_addm; · cases HINV; assumption
    -- EC: + have ^ /m_mh_of_INV Hm_mh /hs_of_INV Hhs := HINV.
    --       by apply/(notin_m_notin_mh _ _ _ _ Hm_mh PFm_x1x2 hs_hx).
    · exact notin_m_notin_mh _ _ _ _ _ _ _ (m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
        PFm_x1x2 hs_hx
    -- EC: have ^ /mi_mhi_of_INV Hmi_mhi /hs_of_INV Hhs := HINV.
    --     by apply/(ch_notdomE2_mh _ _ Hmi_mhi Hhs).
    exact ch_notdomE2_mh _ _ _ _ _ (mi_mhi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
      (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
  -- EC: + have ^ /hs_of_INV ^ Hhs [] Hhuniq _ _ /m_mh_of_INV := HINV.
  --       move=> /m_mh_addh_addm /(_ hx x1 x2 ch y1 y2 Known Known Hhuniq hs_hx _) //.
  --       exact/ch_notdomE_hs.
  · have Hhs := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; obtain ⟨Hhuniq, -, -⟩ := id Hhs
    exact m_mh_addh_addm _ _ _ hx x1 x2 ch y1 y2 Known Known
      (m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV) Hhuniq hs_hx (ch_notdomE_hs _ _ Hhs)
  -- EC: + have ^ /hs_of_INV ^ Hhs [] Hhuniq _ _ /mi_mhi_of_INV := HINV.
  --       move=> /mi_mhi_addh_addmi /(_ hx x1 x2 ch y1 y2 Known Known _ hs_hx _) //.
  --       exact/ch_notdomE_hs.
  · have Hhs := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    exact mi_mhi_addh_addmi _ _ _ hx x1 x2 ch y1 y2 Known Known
      (mi_mhi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV) y2_notrngE1_hs hs_hx (ch_notdomE_hs _ _ Hhs)
  -- EC: + by have /incl_of_INV/incl_addm ->:= HINV.
  · exact incl_addm _ _ _ _ (incl_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
  -- EC: + by have /incli_of_INV/incl_addm ->:= HINV.
  · exact incl_addm _ _ _ _ (incli_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
  -- EC: + split.
  · constructor
    -- EC: + move=> xa' hx' ya' hy'; rewrite get_setE;
    --       case: ((xa',hx') = (x1,hx))=> [[#] <*>> [#] <<*> /=|].
    · intro xa' hx' ya' hy'; rw [FMap.get_setE]; split_ifs with hk
      · intro he; obtain ⟨h1, h2⟩ := Prod.mk.inj hk
        obtain ⟨h3, h4⟩ := Prod.mk.inj (Option.some.inj he); subst xa' hx' ya' hy'
        -- EC: + exists x2 Known y2 Known=> //=; rewrite !get_setE /=.
        --       by have /hs_of_INV [] _ _ dom_hs /#:= HINV.
        obtain ⟨-, -, dom_hs⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        exact ⟨x2, Known, y2, Known,
          by rw [FMap.get_set_neqE _ ch hx _ (dom_hs _ _ hs_hx).ne]; exact hs_hx,
          by simp, by simp⟩
      -- EC: move=> xahx'_neq_x1hx; have /mh_of_INV [] Hmh _ _ /Hmh {Hmh} := HINV.
      intro hm
      obtain ⟨Hmh, -, -⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      have Hhs := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      -- EC: move=> [xc fx yc] [] /= [#] hs_hx' hs_hy'=> [[p v] [Hro Hpath]|<*> Gm_xa'xc].
      obtain ⟨xc, fx, yc, fy, hs_hx', hs_hy', Hite⟩ := Hmh _ _ _ _ hm
      cases fy with
      | Unknown =>
        obtain ⟨p, v, Hro, Hpath⟩ := by simpa using Hite
        -- EC: + exists xc fx yc Unknown=> /=; rewrite !get_setE hs_hx' hs_hy'.
        --       rewrite (dom_hs_neq_ch hs xc fx _ hs_hx') /=; 1:by case: HINV.
        --       rewrite (dom_hs_neq_ch hs yc Unknown _ hs_hy')/= ; 1:by case: HINV.
        refine ⟨xc, fx, yc, Unknown,
          by rwa [FMap.get_set_neqE _ _ _ _ (dom_hs_neq_ch _ _ _ _ _ Hhs hs_hx')],
          by rwa [FMap.get_set_neqE _ _ _ _ (dom_hs_neq_ch _ _ _ _ _ Hhs hs_hy')], ?_⟩
        -- EC: exists p v; rewrite Hro /=;
        --       apply/build_hpath_up/(notin_m_notin_mh _ _ _ _ _ PFm_x1x2 hs_hx).
        --     + done.
        --     by case: HINV.
        rw [if_neg (by decide)]
        exact ⟨p, v, Hro, build_hpath_up _ _ _ _ _ _ _ _ Hpath
          (notin_m_notin_mh _ _ _ _ _ _ _ (by cases HINV; assumption) PFm_x1x2 hs_hx)⟩
      | Known =>
        obtain ⟨Gm_xa'xc, rfl⟩ := by simpa using Hite
        -- EC: exists xc Known yc Known=> //=; rewrite !get_setE;
        --       case: ((xa',xc) = (x1,x2))=> [/#|].
        -- EC: rewrite Gm_xa'xc /= (dom_hs_neq_ch hs xc Known _ hs_hx') /=; 1:by case: HINV.
        --     by rewrite (dom_hs_neq_ch hs yc Known _ hs_hy')/= ; 1:by case: HINV.
        refine ⟨xc, Known, yc, Known,
          by rwa [FMap.get_set_neqE _ _ _ _ (dom_hs_neq_ch _ _ _ _ _ Hhs hs_hx')],
          by rwa [FMap.get_set_neqE _ _ _ _ (dom_hs_neq_ch _ _ _ _ _ Hhs hs_hy')], ?_⟩
        rw [if_pos rfl, FMap.get_setE]; split_ifs with he
        · rw [he, G1m_x1x2] at Gm_xa'xc; cases Gm_xa'xc
        exact ⟨Gm_xa'xc, rfl⟩
    -- EC: + move=> p xa b; have /mh_of_INV [] _ -> _ := HINV; split.
    · intro p xa b
      obtain ⟨-, Hro, -⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      rw [Hro]; constructor
      -- EC: + move=> [v hi hf] [#] Hpath mh_vxahi; exists v hi hf.
      · rintro ⟨v, hi, hf, Hpath, mh_vxahi⟩
        refine ⟨v, hi, hf, ?_⟩
        -- EC: rewrite get_setE; case: ((v +^ xa,hi) = (x1,hx))=> [[#] <*>|_].
        rw [FMap.get_setE]; split_ifs with he
        -- EC: + move: mh_vxahi; have /m_mh_of_INV [] _ H /H {H}:= HINV.
        --       by move=> [xc fx yc fy] [#]; rewrite hs_hx=> [#] <*>; rewrite PFm_x1x2.
        · rw [he] at mh_vxahi
          obtain ⟨-, H⟩ := m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
          obtain ⟨xc, fx, yc, fy, hs_hx', -, hP⟩ := H _ _ _ _ mh_vxahi
          rw [hs_hx] at hs_hx'; obtain ⟨rfl, rfl⟩ := by simpa using hs_hx'
          rw [PFm_x1x2] at hP; cases hP
        -- EC: rewrite mh_vxahi /=; apply/build_hpath_up=> //.
        --     by apply/(notin_m_notin_mh _ _ _ _ _ PFm_x1x2 hs_hx); case: HINV.
        exact ⟨build_hpath_up _ _ _ _ _ _ _ _ Hpath
          (notin_m_notin_mh _ _ _ _ _ _ _ (by cases HINV; assumption) PFm_x1x2 hs_hx), mh_vxahi⟩
      -- EC: move=> [v hi hf] [#].
      rintro ⟨v, hi, hf, Hpath', Hextend⟩
      -- EC: have no_path_to_hx: forall p0 v0, build_hpath G1mh p0 <> Some (v0,hx).
      --     + have /pi_of_INV [] /(_ x2):= HINV; rewrite pi_x2 /=.
      --       by move=> + p0 v0 - /(_ p0 v0) /negb_exists /(_ hx) /=; rewrite hs_hx.
      have no_path_to_hx : ∀ p0 v0, build_hpath G1mh p0 ≠ some (v0, hx) := by
        intro p0 v0 hp
        obtain ⟨Ipi⟩ := pi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        have := (Ipi x2 p0 v0).2 ⟨hx, hp, hs_hx⟩; rw [pi_x2] at this; cases this
      -- EC: have H /H {H} := build_hpath_down G1mh x1 hx y1 ch p v hi no_path_to_hx.
      have Hpath := build_hpath_down G1mh x1 hx y1 ch p v hi no_path_to_hx Hpath'
      -- EC: rewrite get_setE. case: ((v +^ xa,hi) = (x1,hx))=> [[#] <*>|_ Hpath Hextend].
      rw [FMap.get_setE] at Hextend; split_ifs at Hextend with he
      -- EC: + by rewrite no_path_to_hx.
      · exact absurd ((Prod.mk.inj he).2 ▸ Hpath) (no_path_to_hx _ _)
      -- EC: by exists v hi hf.
      exact ⟨v, hi, hf, Hpath, Hextend⟩
    -- EC: move=> p v p' v' h0.
    intro p v p' v' h0
    -- EC: have: forall p0 v0, build_hpath G1mh p0 <> Some (v0,hx).
    --     + have /pi_of_INV [] /(_ x2):= HINV; rewrite pi_x2 /=.
    --       by move=> + p0 v0 - /(_ p0 v0) /negb_exists /(_ hx) /=; rewrite hs_hx.
    have no_path_to_hx : ∀ p0 v0, build_hpath G1mh p0 ≠ some (v0, hx) := by
      intro p0 v0 hp
      obtain ⟨Ipi⟩ := pi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      have := (Ipi x2 p0 v0).2 ⟨hx, hp, hs_hx⟩; rw [pi_x2] at this; cases this
    -- EC: move=> ^ + /build_hpath_down H /H {H} - /build_hpath_down H + /H {H}.
    --     by have /mh_of_INV [] _ _ /(_ p v p' v' h0):= HINV.
    intro h1 h2
    obtain ⟨-, -, Huniq⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    exact Huniq p v p' v' h0 (build_hpath_down _ _ _ _ _ _ _ _ no_path_to_hx h1)
      (build_hpath_down _ _ _ _ _ _ _ _ no_path_to_hx h2)
  -- EC: split=> c p v; have /pi_of_INV [] -> := HINV.
  · refine ⟨fun c p v => ?_⟩
    obtain ⟨Ipi⟩ := pi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    rw [Ipi]
    -- EC: apply/exists_iff=> h /=; split=> [#].
    refine exists_congr fun h => ?_
    constructor
    -- EC: + move=> /build_hpath_up /(_ x1 hx y1 ch _).
    --       + by apply/(notin_m_notin_mh hs PFm x2 Known); case:HINV.
    --       move=> -> /=; rewrite get_setE.
    --       by have /hs_of_INV [] _ _ dom_hs ^ + /dom_hs /#:= HINV.
    · rintro ⟨Hpath, hs_h⟩
      refine ⟨build_hpath_up _ x1 hx y1 ch _ _ _ Hpath
        (notin_m_notin_mh _ _ _ _ _ _ _ (by cases HINV; assumption) PFm_x1x2 hs_hx), ?_⟩
      obtain ⟨-, -, dom_hs⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      rw [FMap.get_set_neqE _ ch h _ (dom_hs _ _ hs_h).ne, hs_h]
    -- EC: have no_path_to_hx: forall p0 v0, build_hpath G1mh p0 <> Some (v0,hx). (…)
    have no_path_to_hx : ∀ p0 v0, build_hpath G1mh p0 ≠ some (v0, hx) := by
      intro p0 v0 hp
      have := (Ipi x2 p0 v0).2 ⟨hx, hp, hs_hx⟩; rw [pi_x2] at this; cases this
    -- EC: have H /H {H} := build_hpath_down G1mh x1 hx y1 ch p v h no_path_to_hx.
    rintro ⟨Hpath', hs_h⟩
    have Hpath := build_hpath_down G1mh x1 hx y1 ch p v h no_path_to_hx Hpath'
    -- EC: move=> ^ Hpath -> /=; rewrite get_setE; case: (h = ch)=> [<*> /= [#] <*>|//=].
    refine ⟨Hpath, ?_⟩
    rw [FMap.get_setE] at hs_h; split_ifs at hs_h with hch; rotate_right; · exact hs_h
    subst h
    -- EC: move: Hpath=> /build_hpathP [<*>|].
    rcases (build_hpathP _ _ _ _).1 Hpath with ⟨-, -, hch⟩ | ⟨p', b', v', h', -, -, hm⟩
    -- EC: + by have /hs_of_INV [] _ + H - /H {H}:= HINV.
    · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      have := Hlt _ _ h0; linarith
    -- EC: + move=> p' b' v' h' <*> _; have /m_mh_of_INV [] _ H /H {H}:= HINV.
    --       by move=> [xc fx yc fy] [#] _; have /hs_of_INV [] _ _ H /H {H}:= HINV.
    · obtain ⟨-, H⟩ := m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      obtain ⟨xc, fx, yc, fy, -, hs_ch, -⟩ := H _ _ _ _ hm
      obtain ⟨-, -, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      have := Hlt _ _ hs_ch; linarith
  -- EC: split=>[].
  · constructor
    -- EC: + by case:HINV=>_ _ _ _ _ _ _ _ (* _ *) [] _ [] ->//.
    · obtain ⟨c1, -, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c1
    -- EC: + by case:HINV=>_ _ _ _ _ _ _ _ (* _ *) [] _ [].
    · obtain ⟨-, c2, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c2
    -- EC: + move=>l hmem i hi.
    · intro l hmem i hi
      -- EC: have[]_ _ h2 _:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _  _ HINV.
      obtain ⟨-, -, h2, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      -- EC: have[]sa sc[]:=h2 l hmem i hi.
      obtain ⟨sa, sc, h4, h5⟩ := h2 l hmem i hi
      -- EC: have h1:=all_prefixes_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV.
      have h1 := all_prefixes_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      -- EC: smt(domE get_setE).
      refine ⟨sa, sc, h4, ?_⟩
      rw [FMap.get_setE, if_neg]; · exact h5
      intro he; rw [he, PFm_x1x2] at h5
      exact (FMap.domE _ _).1 (h1 l hmem (i + 1)) h5.symm
    -- EC: by case:HINV=>_ _ _ _ _ _ _ _ _ [].
    · obtain ⟨-, -, -, c4, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c4
    -- EC: by case:HINV=>_ _ _ _ _ _ _ _ _ [].
    · obtain ⟨-, -, -, -, c5⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c5

/-- EC's `lemma lemma2'`, in EC's script. -/
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
  -- EC: move=> HINV hh PFmi_x1x2 G1mi_x1x2 hs_hx y2_notrngE1_hs.
  intro HINV hh PFmi_x1x2 G1mi_x1x2 hs_hx y2_notrngE1_hs
  -- EC: split.
  constructor
  -- EC: + by apply/hs_addh=> //=; case: HINV.
  · exact hs_addh _ _ _ _ (by cases HINV; assumption) y2_notrngE1_hs
  -- EC: + apply/inv_addm=> //; 1:by case: HINV.
  · refine inv_addm _ _ _ _ (by cases HINV; assumption) ?_ G1mi_x1x2
    -- EC: case: {-1}(G1m.[(y1,y2)]) (eq_refl G1m.[(y1,y2)])=> [//|[xa xc]].
    rcases h : FMap.get G1m (y1, y2) with _ | ⟨xa, xc⟩; · rfl
    -- EC: + have /incl_of_INV + ^h - <- := HINV; 1: by rewrite h.
    have hi := incl_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV (y1, y2) (by simp [h])
    rw [h] at hi
    -- EC: have /m_mh_of_INV [] H _ /H {H} [hx' fx' hy' fy'] [#] := HINV.
    obtain ⟨H, -⟩ := m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    obtain ⟨hx', fx', hy', fy', hs_hx', -, -⟩ := H _ _ _ _ hi
    -- EC: by rewrite y2_notrngE1_hs.
    exact absurd hs_hx' (y2_notrngE1_hs _ _)
  -- EC: + apply/inv_addm; 1:by case: HINV.
  · apply inv_addm; · cases HINV; assumption
    -- EC: + have ^ /m_mh_of_INV Hm_mh /hs_of_INV Hhs := HINV.
    --       by apply/(ch_notdomE2_mh _ _ Hm_mh Hhs).
    · exact ch_notdomE2_mh _ _ _ _ _ (m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
        (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
    -- EC: have ^ /mi_mhi_of_INV Hm_mh /hs_of_INV Hhs := HINV.
    --     by apply/(notin_m_notin_mh _ _ _ _ Hm_mh PFmi_x1x2 hs_hx).
    exact notin_m_notin_mh _ _ _ _ _ _ _ (mi_mhi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
      PFmi_x1x2 hs_hx
  -- EC: + have ^ /hs_of_INV ^ Hhs [] Hhuniq _ _ /m_mh_of_INV := HINV.
  --       move=> /mi_mhi_addh_addmi /(_ hx x1 x2 ch y1 y2 Known Known _ hs_hx _) //.
  --       exact/ch_notdomE_hs.
  · have Hhs := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    exact mi_mhi_addh_addmi _ _ _ hx x1 x2 ch y1 y2 Known Known
      (m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV) y2_notrngE1_hs hs_hx (ch_notdomE_hs _ _ Hhs)
  -- EC: + have ^ /hs_of_INV ^ Hhs [] Hhuniq _ _ /mi_mhi_of_INV := HINV.
  --       move=> /m_mh_addh_addm /(_ hx x1 x2 ch y1 y2 Known Known _ hs_hx _) //.
  --       exact/ch_notdomE_hs.
  · have Hhs := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; obtain ⟨Hhuniq, -, -⟩ := id Hhs
    exact m_mh_addh_addm _ _ _ hx x1 x2 ch y1 y2 Known Known
      (mi_mhi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV) Hhuniq hs_hx (ch_notdomE_hs _ _ Hhs)
  -- EC: + by have /incl_of_INV/incl_addm ->:= HINV.
  · exact incl_addm _ _ _ _ (incl_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
  -- EC: + by have /incli_of_INV/incl_addm ->:= HINV.
  · exact incl_addm _ _ _ _ (incli_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
  -- EC: + split.
  · constructor
    -- EC: + move=> ya' hy' xa' hx'; rewrite get_setE;
    --       case: ((ya',hy') = (y1,ch))=> [[#] <*>> [#] <<*> /=|].
    · intro ya' hy' xa' hx'; rw [FMap.get_setE]; split_ifs with hk
      · intro he; obtain ⟨h1, h2⟩ := Prod.mk.inj hk
        obtain ⟨h3, h4⟩ := Prod.mk.inj (Option.some.inj he); subst ya' hy' xa' hx'
        -- EC: + exists y2 Known x2 Known=> //=; rewrite !get_setE /=.
        --       by have /hs_of_INV [] _ _ dom_hs /#:= HINV.
        obtain ⟨-, -, dom_hs⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        exact ⟨y2, Known, x2, Known, by simp,
          by rw [FMap.get_set_neqE _ ch hx _ (dom_hs _ _ hs_hx).ne]; exact hs_hx, by simp⟩
      -- EC: move=> yahy'_neq_y1ch; have /mh_of_INV [] Hmh _ _ /Hmh {Hmh} := HINV.
      intro hm
      obtain ⟨Hmh, -, -⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      have Hhs := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      -- EC: move=> [yc fy xc] [] /= [#] hs_hy' hs_hx'=> [[p v] [#] Hro Hpath|Gm_ya'yc <*>].
      obtain ⟨yc, fy, xc, fx, hs_hy', hs_hx', Hite⟩ := Hmh _ _ _ _ hm
      cases fx with
      | Unknown =>
        obtain ⟨p, v, Hro, Hpath⟩ := by simpa using Hite
        -- EC: + exists yc fy xc Unknown => /=; rewrite !get_setE hs_hx' hs_hy'.
        --       rewrite (dom_hs_neq_ch hs yc fy _ hs_hy') /=; 1:by case: HINV.
        --       rewrite (dom_hs_neq_ch hs xc Unknown _ hs_hx')/= ; 1:by case: HINV.
        refine ⟨yc, fy, xc, Unknown,
          by rwa [FMap.get_set_neqE _ _ _ _ (dom_hs_neq_ch _ _ _ _ _ Hhs hs_hy')],
          by rwa [FMap.get_set_neqE _ _ _ _ (dom_hs_neq_ch _ _ _ _ _ Hhs hs_hx')], ?_⟩
        -- EC: exists p v; rewrite Hro /=; apply/build_hpath_up=> //.
        rw [if_neg (by decide)]
        refine ⟨p, v, Hro, build_hpath_up _ _ _ _ _ _ _ _ Hpath ?_⟩
        -- EC: case: {-1}(G1mh.[(y1,ch)]) (eq_refl G1mh.[(y1,ch)])=> [//|[za zc]].
        --     have /m_mh_of_INV [] _ H /H {H} [? ? ? ?] [#]:= HINV.
        --     by have /hs_of_INV [] _ _ H /H {H} := HINV.
        exact ch_notdomE2_mh _ _ _ _ _ (m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV) Hhs
      | Known =>
        obtain ⟨Gm_ya'yc, rfl⟩ := by simpa using Hite
        -- EC: exists yc Known xc Known=> //=; rewrite !get_setE;
        --       case: ((ya',yc) = (y1,y2))=> [/#|].
        -- EC: rewrite Gm_ya'yc /= (dom_hs_neq_ch hs yc Known _ hs_hy') /=; 1:by case: HINV.
        --     by rewrite (dom_hs_neq_ch hs xc Known _ hs_hx')/= ; 1:by case: HINV.
        refine ⟨yc, Known, xc, Known,
          by rwa [FMap.get_set_neqE _ _ _ _ (dom_hs_neq_ch _ _ _ _ _ Hhs hs_hy')],
          by rwa [FMap.get_set_neqE _ _ _ _ (dom_hs_neq_ch _ _ _ _ _ Hhs hs_hx')], ?_⟩
        rw [if_pos rfl, FMap.get_setE]; split_ifs with he
        · rw [he] at Gm_ya'yc
          have := incl_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV (y1, y2) (by simp [Gm_ya'yc])
          exact absurd ((FMap.domE _ _).2 (by simp [this, Gm_ya'yc])) hh
        exact ⟨Gm_ya'yc, rfl⟩
    -- EC: + move=> p ya b; have /mh_of_INV [] _ -> _ := HINV.
    · intro p ya b
      obtain ⟨-, Hro, -⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      rw [Hro]
      -- EC: apply/exists_iff=> v /=; apply/exists_iff=> hx' /=; apply/exists_iff=> hy' /=.
      refine exists_congr fun v => exists_congr fun hx' => exists_congr fun hy' => ?_
      -- EC: split=> [#].
      constructor
      -- EC: + move=> /(@build_hpath_up _ y1 ch x1 hx) /(_ _).
      --       + apply/(@notin_hs_notdomE2_mh hs PFm)/(ch_notdomE_hs); by case: HINV.
      · rintro ⟨Hpath, mh_vyahx'⟩
        refine ⟨build_hpath_up _ y1 ch x1 hx _ _ _ Hpath
          (notin_hs_notdomE2_mh hs PFm _ _ _ (by cases HINV; assumption)
            (ch_notdomE_hs _ _ (by cases HINV; assumption))), ?_⟩
        -- EC: move=> -> /=; rewrite get_setE /=; case: (hx' = ch)=> <*> //.
        rw [FMap.get_setE, if_neg]; · exact mh_vyahx'
        -- EC: have /m_mh_of_INV [] _ H /H {H} [xc fx yc fy] [#] := HINV.
        --     by have /hs_of_INV [] _ _ H /H {H} := HINV.
        intro he
        obtain ⟨-, H⟩ := m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        obtain ⟨xc, fx, yc, fy, hs_ch, -, -⟩ := H _ _ _ _ mh_vyahx'
        obtain ⟨-, -, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        rw [(Prod.mk.inj he).2] at hs_ch; have := Hlt _ _ hs_ch; linarith
      -- EC: have no_path_to_ch: forall p0 v0, build_hpath G1mh p0 <> Some (v0,ch).
      --     + move=> p0 v0; elim/last_ind: p0.
      --       + by have /hs_of_INV [] /# := HINV.
      --       move=> p0 b0 _; rewrite build_hpath_prefix.
      --       apply/negb_exists=> b' /=; apply/negb_exists=> h' /=; apply/negb_and=> /=; right.
      --       rewrite -negP; have /mh_of_INV [] H _ _ /H {H} [? ? ? ?] [#] _ := HINV.
      --       by have /hs_of_INV [] _ _ H /H {H} := HINV.
      have no_path_to_ch : ∀ p0 v0, build_hpath G1mh p0 ≠ some (v0, ch) := by
        intro p0 v0 hp
        rcases (build_hpathP _ _ _ _).1 hp with ⟨-, -, hch⟩ | ⟨p', b', v', h', -, -, hm⟩
        · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
          have := Hlt _ _ h0; linarith
        · obtain ⟨H, -, -⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
          obtain ⟨xc, fx, yc, fy, -, hs_ch, -⟩ := H _ _ _ _ hm
          obtain ⟨-, -, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
          have := Hlt _ _ hs_ch; linarith
      -- EC: have H /H {H} := build_hpath_down G1mh y1 ch x1 hx p v hx' no_path_to_ch.
      rintro ⟨Hpath', Hextend⟩
      have Hpath := build_hpath_down G1mh y1 ch x1 hx p v hx' no_path_to_ch Hpath'
      -- EC: rewrite get_setE. case: ((v +^ ya,hx') = (y1,ch))=> [[#] <*>|_ Hpath Hextend //=].
      --     by rewrite no_path_to_ch.
      rw [FMap.get_setE] at Hextend; split_ifs at Hextend with he
      · exact absurd ((Prod.mk.inj he).2 ▸ Hpath) (no_path_to_ch _ _)
      exact ⟨Hpath, Hextend⟩
    -- EC: move=> p v p' v' h0.
    intro p v p' v' h0
    -- EC: have: forall p0 v0, build_hpath G1mh p0 <> Some (v0,ch). (… as above)
    have no_path_to_ch : ∀ p0 v0, build_hpath G1mh p0 ≠ some (v0, ch) := by
      intro p0 v0 hp
      rcases (build_hpathP _ _ _ _).1 hp with ⟨-, -, hch⟩ | ⟨p', b', v', h', -, -, hm⟩
      · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        have := Hlt _ _ h0; linarith
      · obtain ⟨H, -, -⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        obtain ⟨xc, fx, yc, fy, -, hs_ch, -⟩ := H _ _ _ _ hm
        obtain ⟨-, -, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        have := Hlt _ _ hs_ch; linarith
    -- EC: move=> ^ + /build_hpath_down H /H {H} - /build_hpath_down H + /H {H}.
    --     by have /mh_of_INV [] _ _ /(_ p v p' v' h0):= HINV.
    intro h1 h2
    obtain ⟨-, -, Huniq⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    exact Huniq p v p' v' h0 (build_hpath_down _ _ _ _ _ _ _ _ no_path_to_ch h1)
      (build_hpath_down _ _ _ _ _ _ _ _ no_path_to_ch h2)
  -- EC: split=> c p v; have /pi_of_INV [] -> := HINV.
  · refine ⟨fun c p v => ?_⟩
    obtain ⟨Ipi⟩ := pi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    rw [Ipi]
    -- EC: apply/exists_iff=> h /=; split=> [#].
    refine exists_congr fun h => ?_
    constructor
    -- EC: + move=> /build_hpath_up /(_ y1 ch x1 hx _).
    --       + have ^ /m_mh_of_INV [] _ H /hs_of_INV [] _ _ H' := HINV.
    --         case: {-1}(G1mh.[(y1,ch)]) (eq_refl (G1mh.[(y1,ch)]))=> [//|].
    --         by move=> [za zc] /H [? ? ? ?] [#] /H'.
    --       move=> -> /=; rewrite get_setE.
    --       by have /hs_of_INV [] _ _ dom_hs ^ + /dom_hs /#:= HINV.
    · rintro ⟨Hpath, hs_h⟩
      refine ⟨build_hpath_up _ y1 ch x1 hx _ _ _ Hpath
        (ch_notdomE2_mh _ _ _ _ _ (m_mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)
          (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV)), ?_⟩
      obtain ⟨-, -, dom_hs⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      rw [FMap.get_set_neqE _ ch h _ (dom_hs _ _ hs_h).ne, hs_h]
    -- EC: have no_path_to_ch: forall p0 v0, build_hpath G1mh p0 <> Some (v0,ch). (…)
    have no_path_to_ch : ∀ p0 v0, build_hpath G1mh p0 ≠ some (v0, ch) := by
      intro p0 v0 hp
      rcases (build_hpathP _ _ _ _).1 hp with ⟨-, -, hch⟩ | ⟨p', b', v', h', -, -, hm⟩
      · obtain ⟨-, h0, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        have := Hlt _ _ h0; linarith
      · obtain ⟨H, -, -⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        obtain ⟨xc, fx, yc, fy, -, hs_ch, -⟩ := H _ _ _ _ hm
        obtain ⟨-, -, Hlt⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        have := Hlt _ _ hs_ch; linarith
    -- EC: + have H /H {H} := build_hpath_down G1mh y1 ch x1 hx p v h no_path_to_ch.
    rintro ⟨Hpath', hs_h⟩
    have Hpath := build_hpath_down G1mh y1 ch x1 hx p v h no_path_to_ch Hpath'
    -- EC: move=> ^ Hpath -> /=; rewrite get_setE; case: (h = ch)=> [<*> /= [#] <*>|//=].
    refine ⟨Hpath, ?_⟩
    rw [FMap.get_setE] at hs_h; split_ifs at hs_h with hch; rotate_right; · exact hs_h
    subst h
    -- EC: move: Hpath=> /build_hpathP [<*>|].
    --     + by have /hs_of_INV [] _ + H - /H {H}:= HINV.
    --     move=> p' b' v' h' <*> _; have /m_mh_of_INV [] _ H /H {H}:= HINV.
    --     by move=> [xc fx yc fy] [#] _; have /hs_of_INV [] _ _ H /H {H}:= HINV.
    exact absurd Hpath (no_path_to_ch _ _)
  -- EC: split=>[].
  · constructor
    -- EC: + by case:HINV=>_ _ _ _ _ _ _ _ (* _ *) [] _ [].
    · obtain ⟨c1, -, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c1
    -- EC: + by case:HINV=>_ _ _ _ _ _ _ _ (* _ *) [] _ [].
    · obtain ⟨-, c2, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c2
    -- EC: + move=>l hmem i hi.
    · intro l hmem i hi
      -- EC: have[]_ _ h2 _:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV.
      obtain ⟨-, -, h2, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      -- EC: have[]sa sc[]:=h2 l hmem i hi.
      obtain ⟨sa, sc, h4, h5⟩ := h2 l hmem i hi
      -- EC: have h1:=all_prefixes_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV.
      have h1 := all_prefixes_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      -- EC: smt(domE get_setE).
      refine ⟨sa, sc, h4, ?_⟩
      rw [FMap.get_setE, if_neg]; · exact h5
      intro he; rw [he] at h5
      have := (FMap.domE _ _).1 (h1 l hmem (i + 1)); rw [← h5] at this
      exact hh ((FMap.domE _ _).2 this)
    -- EC: by case:HINV=>_ _ _ _ _ _ _ _ _ [].
    · obtain ⟨-, -, -, c4, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c4
    -- EC: by case:HINV=>_ _ _ _ _ _ _ _ _ [].
    · obtain ⟨-, -, -, -, c5⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; exact c5

/-- EC's `lemma lemma3`, in EC's script. -/
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
  -- EC: move=> HINV Pm_xaxc Gm_xaxc mh_xahx hs_hx hs_hy pi_xc.
  intro HINV Pm_xaxc Gm_xaxc mh_xahx hs_hx hs_hy pi_xc
  -- EC: split.
  constructor
  -- EC: + have /hs_of_INV /hs_updh /(_ Unknown) H := HINV; apply/H=> {H} //.
  · refine hs_updh _ _ Unknown _ _ _ (hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV) ?_ hs_hy
    -- EC: by rewrite -negP=> <*>; move: hs_hy; have /hs_of_INV [] _ -> := HINV.
    rintro rfl; obtain ⟨-, h0, -⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV; simp [h0] at hs_hy
  -- EC: + apply/inv_addm=> //; 1:by case: HINV.
  · refine inv_addm _ _ _ _ (invG_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV) Gm_xaxc ?_
    -- EC: case: {-1}(Gmi.[(ya,yc)]) (eq_refl Gmi.[(ya,yc)])=> [//|[xa' xc']].
    rcases h : FMap.get Gmi (ya, yc) with _ | ⟨xa', xc'⟩; · rfl
    -- EC: have /incli_of_INV + ^h - <- := HINV; 1:by rewrite h.
    have hi := incli_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV (ya, yc) (by simp [h])
    -- EC: move: Pm_xaxc; have [] -> -> /= := inv_mh_inv_Pm hs Pm Pmi mh mhi _ _ _;
    --       first 3 by case: HINV.
    obtain ⟨IP⟩ := inv_mh_inv_Pm hs Pm Pmi mh mhi (by cases HINV; assumption)
      (by cases HINV; assumption) (by cases HINV; assumption)
    -- EC: rewrite -negP=> [#] <<*>.
    rw [h, (IP _ _).1 Pm_xaxc] at hi; obtain ⟨rfl, rfl⟩ := by simpa using hi
    -- EC: move: h; have /invG_of_INV [] <- := HINV.
    --     by rewrite Gm_xaxc.
    obtain ⟨IG⟩ := invG_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    rw [← IG, Gm_xaxc] at h; cases h
  -- EC: + by case: HINV.
  · cases HINV; assumption
  -- EC: + by apply/(m_mh_updh Unknown)=> //; case: HINV.
  · exact m_mh_updh Unknown _ _ _ _ _ _ (by cases HINV; assumption) hs_hy
  -- EC: + by apply/(m_mh_updh Unknown)=> //; case: HINV.
  · exact m_mh_updh Unknown _ _ _ _ _ _ (by cases HINV; assumption) hs_hy
  -- EC: + move=> [za zc]; rewrite get_setE; case: ((za,zc) = (xa,xc))=> // _.
  · rintro ⟨za, zc⟩; rw [FMap.get_setE]; split_ifs with hz; · simp [hz, Pm_xaxc]
    -- EC: by have /incl_of_INV H /H {H}:= HINV.
    exact incl_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV _
  -- EC: + move: mh_xahx; have /inv_of_INV [] H /H {H}:= HINV.
  · obtain ⟨H⟩ := inv_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    -- EC: have /mi_mhi_of_INV [] _ H /H {H} [xct fxt yct fyt] [#] := HINV.
    obtain ⟨-, H'⟩ := mi_mhi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    obtain ⟨xct, fxt, yct, fyt, h1, h2, Pmi_yayc⟩ := H' _ _ _ _ ((H _ _).1 mh_xahx)
    -- EC: rewrite hs_hx hs_hy=> /= [#] 2!<<- [#] 2!<<- Pmi_yayc.
    rw [hs_hy] at h1; rw [hs_hx] at h2
    obtain ⟨rfl, rfl⟩ := by simpa using h1
    obtain ⟨rfl, rfl⟩ := by simpa using h2
    -- EC: move=> [za zc]; rewrite get_setE; case: ((za,zc) = (ya,yc))=> // _.
    rintro ⟨za, zc⟩; rw [FMap.get_setE]; split_ifs with hz; · simp [hz, Pmi_yayc]
    -- EC: by have /incli_of_INV H /H {H}:= HINV.
    exact incli_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV _
  -- EC: + split; last 2 by have /mh_of_INV [] _:= HINV.
  · obtain ⟨Imh, ro_def, Huniq⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    refine ⟨?_, ro_def, Huniq⟩
    -- EC: move=> xa' hx' ya' hy'; case: ((xa',hx') = (xa,hx))=> [[#] <*>|].
    intro xa' hx' ya' hy'
    by_cases Hxahx' : (xa', hx') = (xa, hx)
    · obtain ⟨h1, h2⟩ := Prod.mk.inj Hxahx'; subst xa' hx'
      -- EC: + rewrite mh_xahx=> /= [#] <<*>; rewrite !get_setE /=.
      rw [mh_xahx]; intro he; obtain ⟨rfl, rfl⟩ := by simpa using he
      -- EC: case: (hx = hy)=> [<*>|_]; first by move: hs_hx; rewrite hs_hy.
      have hxy : hx ≠ hy := by rintro rfl; simp [hs_hy] at hs_hx
      -- EC: by exists xc Known yc Known; rewrite get_setE.
      exact ⟨xc, Known, yc, Known, by simp [FMap.get_setE, hxy, hs_hx], by simp, by simp⟩
    -- EC: move=> Hxahx' mh_xahx'.
    intro mh_xahx'
    -- EC: have ^path_to_hy: build_hpath mh (rcons p (b +^ xa)) = Some (ya,hy).
    have path_to_hy : build_hpath mh (rcons p (b +^ xa)) = some (ya, hy) := by
      -- EC: + apply/build_hpath_prefix; exists b hx.
      refine (build_hpath_prefix _ _ _ _ _).2 ⟨b, hx, ?_, ?_⟩
      -- EC: move: pi_xc; have /pi_of_INV [] -> [h] [#] := HINV.
      --     by have /hs_of_INV [] H _ _ + /H {H} /(_ _ _ hs_hx _) := HINV.
      · obtain ⟨Ipi⟩ := pi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        obtain ⟨h, hp, hs_h⟩ := (Ipi _ _ _).1 pi_xc
        obtain ⟨Hu, -, -⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
        rwa [Hu _ _ _ _ hs_h hs_hx rfl] at hp
      -- EC: rewrite xorwA xorwK xorwC xorw0 mh_xahx /=.
      · rw [xorwA, xorwK, xorwC, xorw0, mh_xahx]
    -- EC: have /mh_of_INV [] /(_ _ _ _ _ mh_xahx') + ro_def H /H {H} unique_path_to_hy := HINV.
    have unique_path_to_hy := fun p' v' => Huniq _ _ p' v' _ path_to_hy
    -- EC: move=> [xc' fx' yc' fy'] /= [#].
    obtain ⟨xc', fx', yc', fy', hs_hx', hs_hy', Hite⟩ := Imh _ _ _ _ mh_xahx'
    -- EC: case: (hy' = hy)=> [<*> hs_hx'|Hhy'].
    by_cases Hhy' : hy' = hy
    · subst hy'
      -- EC: + rewrite hs_hy=> /= [#] <<*> /= [p' b'] [#] ro_pbxa' path_hx'.
      rw [hs_hy] at hs_hy'; obtain ⟨rfl, rfl⟩ := by simpa using hs_hy'
      obtain ⟨p', b', ro_pbxa', path_hx'⟩ := by simpa using Hite
      -- EC: have:= unique_path_to_hy (rcons p' (b' +^ xa')) ya' _.
      --     + by apply/build_hpath_prefix; exists b' hx'; rewrite xorwA xorwK xorwC xorw0.
      have := unique_path_to_hy (rcons p' (b' +^ xa')) ya' <|
        (build_hpath_prefix _ _ _ _ _).2
          ⟨b', hx', path_hx', by rw [xorwA, xorwK, xorwC, xorw0]; exact mh_xahx'⟩
      -- EC: move=> [#] ^/rconsIs + /rconssI - <<*>.
      obtain ⟨-, rfl⟩ := this
      -- EC: by move: mh_xahx' Hxahx' mh_xahx; have /inv_of_INV [] ^ + -> - -> -> /= -> := HINV.
      obtain ⟨H⟩ := inv_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      have e := (H _ _).1 mh_xahx'; rw [(H _ _).1 mh_xahx] at e
      exact absurd (Option.some.inj e).symm Hxahx'
    -- EC: rewrite (@get_set_neqE _ _ hy' _ Hhy')=> /= hs_hx' ^ hs_hy' -> Hite.
    -- EC: exists xc' (if hx' = hy then Known else fx') yc' fy'.
    refine ⟨xc', if hx' = hy then Known else fx', yc', fy', ?_,
      by rwa [FMap.get_set_neqE _ _ _ _ Hhy'], ?_⟩
    -- EC: rewrite get_setE; case: (hx' = hy)=> /= [<*>|//].
    --     move: hs_hx'; rewrite hs_hy=> /= [#] <<*> /=.
    · rw [FMap.get_setE]; split_ifs with hz; rotate_right; · exact hs_hx'
      subst hx'; rw [hs_hy] at hs_hx'; obtain ⟨rfl, rfl⟩ := by simpa using hs_hx'
      rfl
    -- EC: rewrite (@get_setE Gm) (_: (xa',xc') <> (xa,xc)) /=.
    -- EC: + move: Hxahx'=> /=; case: (xa' = xa)=> [<*> /=|//].
    --       by apply/contra=> <*>; have /hs_of_INV [] + _ _ - /(_ _ _ _ _ hs_hx' hs_hx _) := HINV.
    have hne : (xa', xc') ≠ (xa, xc) := by
      intro he; obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      obtain ⟨Hu, -, -⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
      exact Hxahx' (by rw [Hu _ _ _ _ hs_hx' hs_hx rfl])
    -- EC: by move: Hite=> /= [#]; case: fy' hs_hy'=> //= _ ->.
    rw [FMap.get_set_neqE _ _ _ _ hne]
    cases fy' with
    | Known => obtain ⟨hG, rfl⟩ := by simpa using Hite
               simp [hG]
    | Unknown => simpa using Hite
  -- EC: + split=> c p' b'; rewrite !get_setE; case: (yc = c)=> [<<*> /=|yc_neq_c]; last first.
  · obtain ⟨Ipi⟩ := pi_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    obtain ⟨Hu, -, -⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    obtain ⟨-, -, Huniq⟩ := mh_of_INV _ _ _ _ _ _ _ _ _ _ _ _ HINV
    have path_to_hy : build_hpath mh (rcons p (b +^ xa)) = some (ya, hy) := by
      -- EC: apply/build_hpath_prefix; exists b hx; rewrite xorwA xorwK xorwC xorw0 mh_xahx /=.
      refine (build_hpath_prefix _ _ _ _ _).2 ⟨b, hx, ?_, ?_⟩
      -- EC: move: pi_xc; have /pi_of_INV [] -> [h] [#] + hs_h:= HINV.
      --     by have /hs_of_INV [] + _ _ - /(_ _ _ _ _ hs_hx hs_h _) := HINV.
      · obtain ⟨h, hp, hs_h⟩ := (Ipi _ _ _).1 pi_xc
        rwa [Hu _ _ _ _ hs_h hs_hx rfl] at hp
      · rw [xorwA, xorwK, xorwC, xorw0, mh_xahx]
    refine ⟨fun c p' b' => ?_⟩
    rw [FMap.get_setE]; split_ifs with yc_eq_c; rotate_right
    -- EC: + rewrite (@eq_sym c) yc_neq_c /=; have /pi_of_INV [] -> := HINV.
    · rw [Ipi]
      -- EC: apply/exists_iff=> h /=; rewrite get_setE; case: (h = hy)=> [<*> /=|//=].
      refine exists_congr fun h => ?_
      rw [FMap.get_setE]; split_ifs with hh; rotate_right; · rfl
      -- EC: by rewrite yc_neq_c hs_hy /=.
      subst hh; simp [hs_hy, Ne.symm yc_eq_c]
    -- EC: split=> [[#] <<*>|].
    constructor
    -- EC: + exists hy; rewrite get_setE /=; apply/build_hpath_prefix. (… the path to `hy`)
    · intro he; obtain ⟨rfl, rfl⟩ := by simpa using he
      exact ⟨hy, path_to_hy, by simp [yc_eq_c]⟩
    -- EC: move=> [h]; rewrite get_setE; case: (h = hy)=> [<*> /=|]; last first.
    rintro ⟨h, hp, hh⟩
    rw [FMap.get_setE] at hh; split_ifs at hh with hhy; rotate_right
    -- EC: + by have /hs_of_INV [] H _ _ + [#] _ /H {H} /(_ _ _ hs_hy _) // <*> := HINV.
    · exact absurd (Hu _ _ _ _ hh hs_hy yc_eq_c) hhy
    -- EC: have /mh_of_INV [] _ _ /(_ p' b') H /H {H} /(_ (rcons p (b +^ xa)) ya _) //:= HINV.
    --     (… the path to `hy`)
    subst hhy
    obtain ⟨rfl, rfl⟩ := Huniq _ _ _ _ _ path_to_hy hp
    rfl
  -- EC: + by case:HINV.
  · cases HINV; assumption

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

/-! ## The invariants of `PFf_Cf`'s two loops and their steps -/

/-- The longest prefix of `p` in the queries `Q`, EC's `prefix p (get_max_prefix p (elems (fdom
C.queries)))`.  An abbreviation, not an EC declaration. -/
noncomputable abbrev qpre (p : List block) (Q : FMap (List block) block) : ℤ :=
  «prefix» p (get_max_prefix p (elems (FMap.fdom Q)))

/-- The invariant of `PFf_Cf`'s first loop (the blocks of `p` already queried): EC's
`while (…)` invariant of the first `splitwhile` half, without the bad event (which this loop does
not touch).  `pref` is `Redo.prefixes{1}`; `(sa, sc)` the left state, `(sa, h)` the right one. -/
def PJ1 (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (pref : FMap (List block) state) (Q : FMap (List block) block) (p : List block) (i : ℤ)
    (sa : block) (sc : capacity) (h : handle) : Prop :=
  INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi pref Q ∧
  FMap.get pref (take i p) = some (sa, sc) ∧ (∃ f, FMap.get hs h = some (sc, f)) ∧
  build_hpath mh (take i p) = some (sa, h) ∧
  (if i = 0 then (sa, h) = (b0, 0) else FMap.get ro (take i p) = some sa) ∧
  0 ≤ i ∧ i ≤ qpre p Q ∧ ¬ FMap.dom Q p ∧ 0 < size p

/-- The left-hand part of the invariant of `PFf_Cf`'s second loop (the new blocks), which holds
whatever the bad event: `pref0` is `Redo.prefixes{1}` before the loop (EC's `alias`). -/
def PJ2L (pref pref0 : FMap (List block) state) (Q : FMap (List block) block) (p : List block)
    (i : ℤ) (sa : block) (sc : capacity) : Prop :=
  FMap.get pref (take i p) = some (sa, sc) ∧
  (∀ l, FMap.dom pref0 l → FMap.get pref l = FMap.get pref0 l) ∧
  (∀ l, FMap.dom pref l → FMap.dom pref0 l ∨ ∃ j, 0 ≤ j ∧ j ≤ i ∧ take j p = l) ∧
  (i < size p → ¬ FMap.dom pref (take (i + 1) p)) ∧
  qpre p Q ≤ i ∧ i ≤ size p ∧ ¬ FMap.dom Q p

/-- The invariant of `PFf_Cf`'s second loop before the bad event (EC's `!(G1.bcol{2} \/
G1.bext{2}) => …`): `INV_CF_G1` with the query `take i p` answered `sa`. -/
def PJ2 (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (pref pref0 : FMap (List block) state) (Q : FMap (List block) block) (p : List block)
    (i : ℤ) (sa : block) (sc : capacity) (h : handle) : Prop :=
  INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi pref (FMap.set Q (take i p) sa) ∧
  m_p Pm pref0 Q ∧ (∃ f, FMap.get hs h = some (sc, f)) ∧
  build_hpath mh (take i p) = some (sa, h) ∧
  (if i = 0 then (sa, h) = (b0, 0) else FMap.get ro (take i p) = some sa)

omit [SLCommon.Params] in
/-- A prefix of `p` of length `k` has size `k` (for `0 ≤ k ≤ size p`). -/
theorem size_take_of_le {α : Type} (k : ℤ) (p : List α) (h0 : 0 ≤ k) (h : k ≤ size p) :
    size (take k p) = k := by
  simp only [size, take, List.length_take] at *
  omega

omit [SLCommon.Params] in
/-- Prefixes of `p` of different lengths (within `size p`) differ. -/
theorem take_ne_take_of_ne {α : Type} (j k : ℤ) (p : List α) (hj0 : 0 ≤ j) (hj : j ≤ size p)
    (hk0 : 0 ≤ k) (hk : k ≤ size p) (hne : j ≠ k) : take j p ≠ take k p := by
  intro he
  have := congrArg size he
  rw [size_take_of_le j p hj0 hj, size_take_of_le k p hk0 hk] at this
  exact hne this

omit [SLCommon.Params] in
/-- A shorter prefix of a prefix is a prefix. -/
theorem take_take_of_le {α : Type} (j k : ℤ) (p : List α) (h : j ≤ k) :
    take j (take k p) = take j p := by
  rw [take_take, min_eq_left h]

omit [SLCommon.Params] in
/-- The blocks of a prefix are those of the list. -/
theorem nth_take_of_lt {α : Type} (x0 : α) (j k : ℤ) (p : List α) (h0 : 0 ≤ j) (h : j < k) :
    nth x0 (take k p) j = nth x0 p j := by
  simp only [nth, if_pos h0, take, List.getD_eq_getElem?_getD, List.getElem?_take]
  rw [if_pos (by omega)]

/-- `m_p`'s third component at a step: `Pm` maps the state recorded for `take i p`, xored with
the next block, to the state recorded for `take (i + 1) p`. -/
theorem m_p_step (Pm : smap) (pref : FMap (List block) state) (Q : FMap (List block) block)
    (p : List block) (i : ℤ) (sa : block) (sc : capacity) :
    m_p Pm pref Q → 0 ≤ i ∧ i < size p → FMap.dom pref (take (i + 1) p) →
    FMap.get pref (take i p) = some (sa, sc) →
    FMap.get Pm (sa +^ nth default p i, sc) = FMap.get pref (take (i + 1) p) := by
  rintro ⟨-, -, Ip, -, -⟩ ⟨hi0, hi⟩ hdom hb
  have hsz : 0 ≤ i ∧ i < size (take (i + 1) p) := by
    rw [size_take_of_le _ _ (by omega) (by omega)]
    omega
  obtain ⟨sa', sc', h1, h2⟩ := Ip _ hdom i hsz
  rw [take_take_of_le _ _ _ (by omega), hb] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  rwa [nth_take_of_lt _ _ _ _ hi0 (by omega), take_take_of_le _ _ _ le_rfl] at h2

/-- A step of the first loop: both sides find the block known. -/
theorem PJ1_step (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (pref : FMap (List block) state) (Q : FMap (List block) block) (p : List block) (i : ℤ)
    (sa : block) (sc : capacity) (h : handle)
    (hJ : PJ1 hs ch Pm Pmi Gm Gmi mh mhi ro pi pref Q p i sa sc h) (hi : i < qpre p Q) :
    FMap.dom pref (take (i + 1) p) ∧ FMap.dom mh (sa +^ nth default p i, h) ∧
    (oget (FMap.get pref (take (i + 1) p))).1 =
      (oget (FMap.get mh (sa +^ nth default p i, h))).1 ∧
    PJ1 hs ch Pm Pmi Gm Gmi mh mhi ro pi pref Q p (i + 1)
      (oget (FMap.get pref (take (i + 1) p))).1 (oget (FMap.get pref (take (i + 1) p))).2
      (oget (FMap.get mh (sa +^ nth default p i, h))).2 := by
  obtain ⟨hI, hpre, ⟨f, hh⟩, hb, -, hi0, -, hQ, hsz⟩ := hJ
  obtain ⟨-, -, -, ⟨-, Imh⟩, -, -, -, ⟨-, Iro, -⟩, -, hmp⟩ := id hI
  unfold qpre at hi
  have hqs := prefix_sizel p (get_max_prefix p (elems (FMap.fdom Q)))
  have hip : 0 ≤ i ∧ i < size p := ⟨hi0, by omega⟩
  have hmem : FMap.dom Q (get_max_prefix p (elems (FMap.fdom Q))) :=
    (mem_elems_fdom _ _).1 (prefix_gt0_mem _ _ (by omega))
  have hdom : FMap.dom pref (take (i + 1) p) := by
    rw [prefix_take_leq p (get_max_prefix p (elems (FMap.fdom Q))) (i + 1) (by omega)]
    obtain ⟨-, -, -, Iq, -⟩ := id hmp
    obtain ⟨c, hc⟩ := Iq _ hmem
    exact all_prefixes_of_m_p _ _ _ hmp _ ((FMap.domE _ _).2 (by simp [hc])) _
  obtain ⟨b', c', h', hPm, hmh⟩ := lemma5 hs ch Pm Pmi Gm Gmi mh mhi ro pi pref Q i p sa sc h
    hI hip hdom hpre ⟨f, hh⟩
  have hpre' : FMap.get pref (take (i + 1) p) = some (b', c') := by
    rw [← m_p_step Pm pref Q p i sa sc hmp hip hdom hpre, hPm]
  obtain ⟨xc, fx, yc, fy, hx, hy, hPm'⟩ := Imh _ _ _ _ hmh
  rw [hh] at hx
  cases hx
  rw [hPm] at hPm'
  cases hPm'
  have hb' : build_hpath mh (take (i + 1) p) = some (b', h') := by
    rw [take_nth default i p hip]
    exact (build_hpath_prefix _ _ _ _ _).2 ⟨sa, h, hb, hmh⟩
  have hro : FMap.get ro (take (i + 1) p) = some b' := by
    rw [take_nth default i p hip]
    exact (Iro _ _ _).2 ⟨sa, h, h', hb, hmh⟩
  rw [hpre', hmh]
  simp only [oget, Option.getD_some]
  refine ⟨(FMap.domE _ _).2 (by simp [hpre']), (FMap.domE _ _).2 (by simp [hmh]), trivial, hI,
    hpre', ⟨fy, hy⟩, hb', ?_, by omega, by unfold qpre; omega, hQ, hsz⟩
  rw [if_neg (by omega)]
  exact hro

/-- From the first loop to the second: at `i = qpre p Q`. -/
theorem PJ1_PJ2 (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (pref : FMap (List block) state) (Q : FMap (List block) block) (p : List block) (i : ℤ)
    (sa : block) (sc : capacity) (h : handle)
    (hJ : PJ1 hs ch Pm Pmi Gm Gmi mh mhi ro pi pref Q p i sa sc h) (hi : ¬ i < qpre p Q) :
    PJ2 hs ch Pm Pmi Gm Gmi mh mhi ro pi pref pref Q p i sa sc h ∧
    PJ2L pref pref Q p i sa sc := by
  obtain ⟨hI, hpre, hh, hb, hif, hi0, hiq, hQ, hsz⟩ := hJ
  have hieq : i = qpre p Q := by omega
  obtain ⟨hs_, hG, hmhi, Imm, Imi, hinc, hinci, hmhs, hpis, hmp⟩ := hI
  obtain ⟨hp0, hq0, Ip, Iq, Iext⟩ := id hmp
  have hqs : qpre p Q ≤ size p := prefix_sizel _ _
  refine ⟨⟨⟨hs_, hG, hmhi, Imm, Imi, hinc, hinci, hmhs, hpis, ?_⟩, hmp, hh, hb, hif⟩,
    ⟨hpre, fun _ _ => rfl, fun _ h => Or.inl h, ?_, le_of_eq hieq.symm, by omega, hQ⟩⟩
  · refine ⟨hp0, ?_, Ip, ?_, ?_⟩
    · rw [FMap.get_setE]
      split_ifs with he
      · rw [← he, hp0] at hpre
        simp only [Option.some.injEq, Prod.mk.injEq] at hpre
        rw [hpre.1]
      · exact hq0
    · intro l hl
      rw [FMap.mem_set] at hl
      by_cases he : l = take i p
      · subst he
        exact ⟨sc, by simp [hpre, oget]⟩
      · rw [FMap.get_set_neqE _ _ _ _ he]
        exact Iq l (hl.resolve_right he)
    · intro l hl
      obtain ⟨l2, h2⟩ := Iext l hl
      exact ⟨l2, (FMap.mem_set _ _ _ _).2 (Or.inl h2)⟩
  · intro hlt hd
    obtain ⟨l2, h2⟩ := Iext _ hd
    have h3 := get_max_prefix_max p _ _ ((mem_elems_fdom _ _).2 h2)
    have hs1 : size (take (i + 1) p) = i + 1 := size_take_of_le _ _ (by omega) (by omega)
    have h4 : i + 1 ≤ «prefix» p (take (i + 1) p ++ l2) := by
      apply prefix_leq_take
      · refine ⟨by omega, le_min (by omega) ?_⟩
        have : size (take (i + 1) p ++ l2) = size (take (i + 1) p) + size l2 := by
          simp [size]
        have : 0 ≤ size l2 := by simp [size]
        omega
      · simp only [take] at hs1 ⊢
        rw [List.take_append_of_le_length (by simp only [size] at hs1; omega),
          List.take_take, min_self]
    unfold qpre at hieq
    omega

/-- The left-hand part of the second loop's invariant, through a step (whatever the bad
event): the new prefix `take (i + 1) p` gets the state `(a, b)`.  Needs `pref0` closed under
prefixes. -/
theorem PJ2L_step (pref pref0 : FMap (List block) state) (Q : FMap (List block) block)
    (p : List block) (i : ℤ) (sa : block) (sc : capacity) (a : block) (b : capacity)
    (hJ : PJ2L pref pref0 Q p i sa sc) (hi : i < size p) (hpre0 : all_prefixes pref0) :
    PJ2L (FMap.set pref (take (i + 1) p) (a, b)) pref0 Q p (i + 1) a b := by
  obtain ⟨-, Hagree, Hext, Hnot, hqi, his, hQ⟩ := hJ
  have hq0 : 0 ≤ qpre p Q := prefix_ge0 _ _
  have hnd := Hnot hi
  have hdom0 : ∀ l, FMap.dom pref0 l → FMap.dom pref l := fun l hl =>
    (FMap.domE _ _).2 (by rw [Hagree _ hl]; exact (FMap.domE _ _).1 hl)
  refine ⟨FMap.get_set_sameE _ _ _, ?_, ?_, ?_, by omega, by omega, hQ⟩
  · intro l hl
    have hne : l ≠ take (i + 1) p := by
      rintro rfl
      exact hnd (hdom0 _ hl)
    rw [FMap.get_set_neqE _ _ _ _ hne, Hagree _ hl]
  · intro l hl
    rw [FMap.mem_set] at hl
    rcases hl with hl | rfl
    · rcases Hext l hl with h | ⟨j, hj0, hji, hj⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj0, by omega, hj⟩
    · exact Or.inr ⟨i + 1, by omega, le_refl _, rfl⟩
  · intro hlt hd
    rw [FMap.mem_set] at hd
    rcases hd with hd | he
    · rcases Hext _ hd with h0 | ⟨j, hj0, hji, hj⟩
      · have h1 := hpre0 _ h0 (i + 1)
        rw [take_take_of_le _ _ _ (by omega)] at h1
        exact hnd (hdom0 _ h1)
      · exact take_ne_take_of_ne j (i + 1 + 1) p hj0 (by omega) (by omega) (by omega)
          (by omega) hj
    · exact take_ne_take_of_ne (i + 1 + 1) (i + 1) p (by omega) (by omega) (by omega)
        (by omega) (by omega) he

/-- A step of the second loop on a known block: `PF.m` and `G1.mh` both know it (`lemma5'`). -/
theorem PJ2_known (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (pref pref0 : FMap (List block) state) (Q : FMap (List block) block) (p : List block)
    (i : ℤ) (sa : block) (sc : capacity) (h : handle)
    (hJ : PJ2 hs ch Pm Pmi Gm Gmi mh mhi ro pi pref pref0 Q p i sa sc h)
    (hL : PJ2L pref pref0 Q p i sa sc) (hi : i < size p)
    (hd : FMap.dom Pm (sa +^ nth default p i, sc)) :
    FMap.dom mh (sa +^ nth default p i, h) ∧
    (oget (FMap.get Pm (sa +^ nth default p i, sc))).1 =
      (oget (FMap.get mh (sa +^ nth default p i, h))).1 ∧
    PJ2 hs ch Pm Pmi Gm Gmi mh mhi ro pi
      (FMap.set pref (take (i + 1) p) (oget (FMap.get Pm (sa +^ nth default p i, sc)))) pref0 Q p
      (i + 1) (oget (FMap.get Pm (sa +^ nth default p i, sc))).1
      (oget (FMap.get Pm (sa +^ nth default p i, sc))).2
      (oget (FMap.get mh (sa +^ nth default p i, h))).2 := by
  obtain ⟨hI, hmp0, ⟨f, hh⟩, hb, -⟩ := hJ
  obtain ⟨hpre, Hagree, -, Hnot, hqi, his, hQ⟩ := hL
  have hq0 : 0 ≤ qpre p Q := prefix_ge0 _ _
  have hip : 0 ≤ i ∧ i < size p := ⟨by omega, hi⟩
  have hnd := Hnot hi
  rcases lemma5' hs ch Pm Pmi Gm Gmi mh mhi ro pi pref _ i p sa sc h hI hip hpre ⟨f, hh⟩ with
    ⟨b', c', h', hPm, hmh⟩ | ⟨hPm, -⟩
  swap
  · exact absurd hPm ((FMap.domE _ _).1 hd)
  have hall : all_prefixes pref := all_prefixes_of_INV _ _ _ _ _ _ _ _ _ _ _ _ hI
  obtain ⟨hs_, hG, hmhi, Imm, Imi, hinc, hinci, hmhs, hpis, hmp⟩ := hI
  obtain ⟨-, Iro, -⟩ := id hmhs
  obtain ⟨-, Imh⟩ := id Imm
  obtain ⟨hp0, -, Ip, -, Iext⟩ := hmp
  obtain ⟨-, hq0', -, Iq0, -⟩ := id hmp0
  obtain ⟨xc, fx, yc, fy, hx, hy, hPm'⟩ := Imh _ _ _ _ hmh
  rw [hh] at hx
  cases hx
  rw [hPm] at hPm'
  cases hPm'
  have hb' : build_hpath mh (take (i + 1) p) = some (b', h') := by
    rw [take_nth default i p hip]
    exact (build_hpath_prefix _ _ _ _ _).2 ⟨sa, h, hb, hmh⟩
  have hro : FMap.get ro (take (i + 1) p) = some b' := by
    rw [take_nth default i p hip]
    exact (Iro _ _ _).2 ⟨sa, h, h', hb, hmh⟩
  have hne0 : ([] : List block) ≠ take (i + 1) p := by
    have := take_ne_take_of_ne 0 (i + 1) p le_rfl (by omega) (by omega) (by omega) (by omega)
    simpa [take] using this
  rw [hPm, hmh]
  simp only [oget, Option.getD_some]
  refine ⟨(FMap.domE _ _).2 (by simp [hmh]), trivial,
    ⟨hs_, hG, hmhi, Imm, Imi, hinc, hinci, hmhs, hpis, ?_⟩, hmp0, ⟨fy, hy⟩, hb', ?_⟩
  swap
  · rw [if_neg (by omega)]
    exact hro
  refine ⟨by rw [FMap.get_set_neqE _ _ _ _ hne0]; exact hp0,
    by rw [FMap.get_set_neqE _ _ _ _ hne0]; exact hq0', ?_, ?_, ?_⟩
  · intro l hl j hj
    rw [FMap.mem_set] at hl
    rcases hl with hl | rfl
    · have hne : ∀ k, take k l ≠ take (i + 1) p := fun k he => hnd (he ▸ hall l hl k)
      obtain ⟨s1, s2, h1, h2⟩ := Ip l hl j hj
      exact ⟨s1, s2, by rw [FMap.get_set_neqE _ _ _ _ (hne j)]; exact h1,
        by rw [FMap.get_set_neqE _ _ _ _ (hne (j + 1))]; exact h2⟩
    · rw [size_take_of_le _ _ (by omega) (by omega)] at hj
      rw [take_take_of_le _ _ _ (by omega : j ≤ i + 1),
        take_take_of_le _ _ _ (by omega : j + 1 ≤ i + 1), nth_take_of_lt _ _ _ _ hj.1 hj.2]
      have hnej : take j p ≠ take (i + 1) p :=
        take_ne_take_of_ne _ _ p hj.1 (by omega) (by omega) (by omega) (by omega)
      rw [FMap.get_set_neqE _ _ _ _ hnej]
      rcases lt_or_eq_of_le (show j ≤ i by omega) with hji | rfl
      · have hdi : FMap.dom pref (take i p) := (FMap.domE _ _).2 (by simp [hpre])
        obtain ⟨s1, s2, h1, h2⟩ := Ip _ hdi j
          ⟨hj.1, by rw [size_take_of_le _ _ (by omega) (by omega)]; exact hji⟩
        rw [take_take_of_le _ _ _ (by omega : j ≤ i)] at h1
        rw [take_take_of_le _ _ _ (by omega : j + 1 ≤ i), nth_take_of_lt _ _ _ _ hj.1 hji] at h2
        have hnej1 : take (j + 1) p ≠ take (i + 1) p :=
          take_ne_take_of_ne _ _ p (by omega) (by omega) (by omega) (by omega) (by omega)
        exact ⟨s1, s2, h1, by rw [FMap.get_set_neqE _ _ _ _ hnej1]; exact h2⟩
      · exact ⟨sa, sc, hpre, by rw [FMap.get_set_sameE, hPm]⟩
  · intro l hl
    rw [FMap.mem_set] at hl
    by_cases he : l = take (i + 1) p
    · subst he
      exact ⟨c', by simp [oget]⟩
    · obtain ⟨c, hc⟩ := Iq0 l (hl.resolve_right he)
      have hd0 : FMap.dom pref0 l := (FMap.domE _ _).2 (by simp [hc])
      exact ⟨c, by rw [FMap.get_set_neqE _ _ _ _ he, FMap.get_set_neqE _ _ _ _ he,
        Hagree _ hd0, hc]⟩
  · intro l hl
    rw [FMap.mem_set] at hl
    rcases hl with hl | rfl
    · obtain ⟨l2, h2⟩ := Iext l hl
      rw [FMap.mem_set] at h2
      rcases h2 with h2 | h2
      · exact ⟨l2, (FMap.mem_set _ _ _ _).2 (Or.inl h2)⟩
      · refine ⟨l2 ++ [nth default p i], (FMap.mem_set _ _ _ _).2 (Or.inr ?_)⟩
        rw [take_nth default i p hip, ← h2, rcons, List.append_assoc]
    · exact ⟨[], (FMap.mem_set _ _ _ _).2 (Or.inr (List.append_nil _))⟩

/-- `m_p` survives adding a fresh entry to the map: every prefix step `PF.m` already answers. -/
theorem m_p_set_none (Pm : smap) (pref : FMap (List block) state) (q : FMap (List block) block)
    (x y : state) :
    m_p Pm pref q → FMap.get Pm x = none → m_p (FMap.set Pm x y) pref q := by
  rintro ⟨c1, c2, c3, c4, c5⟩ hx
  refine ⟨c1, c2, ?_, c4, c5⟩
  intro l hl i hi
  obtain ⟨sa, sc, h1, h2⟩ := c3 l hl i hi
  refine ⟨sa, sc, h1, ?_⟩
  have hne : FMap.get pref (take (i + 1) l) ≠ none := by
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

/-- The fresh-block step of `G1.M.f` (EC's `PFf_Cf`, second loop): the block `x1` after the
known path `(p0, v0)` to the handle `hx2` is unknown to `PF.m`; the oracle answers the fresh
query `rcons p0 (v0 +^ x1)` with `y1`, the new handle `ch` gets the unknown capacity `y2`.  The
prefix part `m_p` of the invariant is a hypothesis (the prefixes change with the caller). -/
theorem f_fresh_inv (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (prefixes : FMap (List block) state) (queries : FMap (List block) block)
    (prefixes' : FMap (List block) state) (queries' : FMap (List block) block) (x1 : block)
    (x2 : capacity) (y1 : block) (y2 : capacity) (hx2 : handle) (fx : flag) (p0 : List block)
    (v0 : block) :
    INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries →
    FMap.get Pm (x1, x2) = none → FMap.get hs hx2 = some (x2, fx) →
    build_hpath mh p0 = some (v0, hx2) → hinv hs y2 = none →
    m_p (FMap.set Pm (x1, x2) (y1, y2)) prefixes' queries' →
    INV_CF_G1 (FMap.set hs ch (y2, Unknown)) (ch + 1)
      (FMap.set Pm (x1, x2) (y1, y2)) (FMap.set Pmi (y1, y2) (x1, x2)) Gm Gmi
      (FMap.set mh (x1, hx2) (y1, ch)) (FMap.set mhi (y1, ch) (x1, hx2))
      (FMap.set ro (rcons p0 (v0 +^ x1)) y1) pi prefixes' queries' := by
  intro HINV Pm_x hs_hx2 Hpath hinv0 Hmp'
  obtain ⟨Hhs, HinvG, Hinvmh, Hmmh, Hmimhi, Hincl, Hincli, Hmh, Hpi, -⟩ := HINV
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
  have mh_x : FMap.get mh (x1, hx2) = none := m_mh_None hs Pm mh hx2 x2 fx x1 Hmmh hs_hx2 Pm_x
  have Hhx2 : hx2 ≠ ch := dom_hs_neq_ch hs ch hx2 x2 fx Hhs hs_hx2
  have ch0 : 0 ≠ ch := ch_neq0 hs ch Hhs
  have ch_None : ∀ xa xb ha hb,
      FMap.get mh (xa, ha) = some (xb, hb) → ha ≠ ch ∧ hb ≠ ch := by
    intro xa xb ha hb hm
    obtain ⟨_, _, _, _, h1, h2, -⟩ := Imm2 _ _ _ _ hm
    exact ⟨dom_hs_neq_ch hs ch _ _ _ Hhs h1, dom_hs_neq_ch hs ch _ _ _ Hhs h2⟩
  have hsne : ∀ h cf, FMap.get hs h = some cf →
      FMap.get (FMap.set hs ch (y2, Unknown)) h = some cf := by
    intro h cf hh
    have := hlt _ _ hh
    rw [FMap.get_set_neqE _ _ _ _ (show h ≠ ch by linarith), hh]
  have mhup : ∀ p v h, build_hpath mh p = some (v, h) →
      build_hpath (FMap.set mh (x1, hx2) (y1, ch)) p = some (v, h) :=
    fun p v h hp => build_hpath_up mh x1 hx2 y1 ch p v h hp mh_x
  have bpiff := fun p v hx =>
    build_hpath_upd_ch_iff hx2 ch mh x1 y1 p v hx mh_x ch0 Hhx2 ch_None
  have Hpath' := mhup _ _ _ Hpath
  refine ⟨hs_addh hs ch y2 Unknown Hhs hy2, HinvG, ?_, ?_, ?_,
    incl_upd_nin _ _ _ _ Hincl (by simpa [FMap.domE] using Pm_x), ?_, ?_, ?_, Hmp'⟩
  · exact inv_addm _ _ _ _ Hinvmh mh_x (ch_notdomE2_mh hs Pmi mhi y1 ch Hmimhi Hhs)
  · exact m_mh_addh_addm hs Pm mh hx2 x1 x2 ch y1 y2 fx Unknown Hmmh hun hs_hx2 hs_ch
  · exact mi_mhi_addh_addmi hs Pmi mhi hx2 x1 x2 ch y1 y2 fx Unknown Hmimhi hy2 hs_hx2 hs_ch
  · refine incl_upd_nin _ _ _ _ Hincli ?_
    rw [FMap.domE]
    intro hg
    obtain ⟨xc, hp⟩ := Option.ne_none_iff_exists'.1 hg
    obtain ⟨_, _, _, _, h1, -, -⟩ := Imi1 _ _ _ _ hp
    exact absurd h1 (hy2 _ _)
  · refine ⟨?_, ?_, ?_⟩
    · -- first component of `mh_spec`
      intro xa hx' ya hy hm
      rw [FMap.get_setE] at hm
      split_ifs at hm with hk
      · simp only [Prod.mk.injEq, Option.some.injEq] at hk hm
        obtain ⟨hk1, hk2⟩ := hk
        obtain ⟨hm1, hm2⟩ := hm
        subst xa hx' ya hy
        refine ⟨x2, fx, y2, Unknown, hsne _ _ hs_hx2, FMap.get_set_sameE _ _ _, ?_⟩
        simp only [reduceCtorEq, if_false]
        exact ⟨p0, v0, FMap.get_set_sameE _ _ _, Hpath'⟩
      · obtain ⟨xc, fx0, yc, fy, h1, h2, h3⟩ := Imh1 _ _ _ _ hm
        refine ⟨xc, fx0, yc, fy, hsne _ _ h1, hsne _ _ h2, ?_⟩
        cases fy with
        | Known => exact h3
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
  · -- `pi_spec`: the new handle is not known
    refine ⟨fun c p v => ?_⟩
    rw [Ipi]
    constructor
    · rintro ⟨h, h1, h2⟩
      exact ⟨h, mhup _ _ _ h1, hsne _ _ h2⟩
    · rintro ⟨h, h1, h2⟩
      rw [bpiff] at h1
      split_ifs at h1 with hh
      · subst hh
        rw [FMap.get_set_sameE] at h2
        simp at h2
      · rw [FMap.get_set_neqE _ _ _ _ hh] at h2
        exact ⟨h, h1, h2⟩

/-- A step of the second loop on a fresh block: neither `PF.m` nor `G1.mh` know it, nor `ro` the
query `take (i + 1) p`; the new block gets `(y1, y2)` on both sides (EC's big inline proof). -/
theorem PJ2_fresh (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (pref pref0 : FMap (List block) state) (Q : FMap (List block) block) (p : List block)
    (i : ℤ) (sa : block) (sc : capacity) (h : handle)
    (hJ : PJ2 hs ch Pm Pmi Gm Gmi mh mhi ro pi pref pref0 Q p i sa sc h)
    (hL : PJ2L pref pref0 Q p i sa sc) (hi : i < size p)
    (hd : ¬ FMap.dom Pm (sa +^ nth default p i, sc)) :
    ¬ FMap.dom mh (sa +^ nth default p i, h) ∧ ¬ FMap.dom ro (take (i + 1) p) ∧
    ∀ y1 y2, hinv hs y2 = none →
      PJ2 (FMap.set hs ch (y2, Unknown)) (ch + 1)
        (FMap.set Pm (sa +^ nth default p i, sc) (y1, y2))
        (FMap.set Pmi (y1, y2) (sa +^ nth default p i, sc)) Gm Gmi
        (FMap.set mh (sa +^ nth default p i, h) (y1, ch))
        (FMap.set mhi (y1, ch) (sa +^ nth default p i, h))
        (FMap.set ro (take (i + 1) p) y1) pi
        (FMap.set pref (take (i + 1) p) (y1, y2)) pref0 Q p (i + 1) y1 y2 ch := by
  obtain ⟨HINV, Hmp0, ⟨f, hs_h⟩, Hpath, -⟩ := hJ
  obtain ⟨hpre, hp1, -, hp3, -, -, -⟩ := hL
  have hnd : ¬ FMap.dom pref (take (i + 1) p) := hp3 hi
  have hdom_pre : FMap.dom pref (take i p) := (FMap.domE _ _).2 (by rw [hpre]; simp)
  have hi0 : 0 ≤ i := by
    by_contra hneg
    apply hnd
    have : take (i + 1) p = take i p := by simp only [take]; congr 1; omega
    rwa [this]
  have ht : take (i + 1) p = rcons (take i p) (nth default p i) :=
    take_nth default i p ⟨hi0, hi⟩
  have Pm_k : FMap.get Pm (sa +^ nth default p i, sc) = none := by
    simpa [FMap.domE] using hd
  have mh_k : FMap.get mh (sa +^ nth default p i, h) = none :=
    m_mh_None hs Pm mh h sc f _ HINV.4 hs_h Pm_k
  -- the query `take (i + 1) p` is fresh for `ro` (`mh_spec`, second component)
  have ro_t : FMap.get ro (take (i + 1) p) = none := by
    cases hro : FMap.get ro (take (i + 1) p) with
    | none => rfl
    | some b =>
      rw [ht] at hro
      obtain ⟨v, hx, hy, hp, hm⟩ := (HINV.8.2 _ _ _).1 hro
      rw [Hpath] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [mh_k] at hm
      cases hm
  refine ⟨by simpa [FMap.domE] using mh_k, by simpa [FMap.domE] using ro_t, ?_⟩
  intro y1 y2 hinv0
  have Hmp := HINV.10
  have hall := all_prefixes_of_m_p _ _ _ Hmp
  -- the new prefix only changes `pref` at `take (i + 1) p`, which it does not know yet
  have pref_keep : ∀ l, FMap.dom pref l →
      FMap.get (FMap.set pref (take (i + 1) p) (y1, y2)) l = FMap.get pref l :=
    fun l hl => FMap.get_set_neqE _ _ _ _ (fun e => hnd (e ▸ hl))
  -- `m_p` with the new prefix and the query `take (i + 1) p` answered `y1`
  have Hmp_new : m_p (FMap.set Pm (sa +^ nth default p i, sc) (y1, y2))
      (FMap.set pref (take (i + 1) p) (y1, y2)) (FMap.set Q (take (i + 1) p) y1) := by
    obtain ⟨c1, -, c3, -, c5⟩ := m_p_set_none _ _ _ _ (y1, y2) Hmp Pm_k
    obtain ⟨-, d2, -, d4, -⟩ := Hmp0
    have hnil_dom : FMap.dom pref [] := (FMap.domE _ _).2 (by rw [c1]; simp)
    have hnil : ([] : List block) ≠ take (i + 1) p := fun e => hnd (e ▸ hnil_dom)
    have c3' : ∀ l, FMap.dom pref l → ∀ j, 0 ≤ j ∧ j < size l →
        ∃ a b, FMap.get (FMap.set pref (take (i + 1) p) (y1, y2)) (take j l) = some (a, b) ∧
          FMap.get (FMap.set Pm (sa +^ nth default p i, sc) (y1, y2)) (a +^ nth default l j, b) =
            FMap.get (FMap.set pref (take (i + 1) p) (y1, y2)) (take (j + 1) l) := by
      intro l hl j hj
      rw [pref_keep _ (hall l hl j), pref_keep _ (hall l hl (j + 1))]
      exact c3 l hl j hj
    refine ⟨by rw [pref_keep _ hnil_dom]; exact c1,
      by rw [FMap.get_set_neqE _ _ _ _ hnil]; exact d2, ?_, ?_, ?_⟩
    · intro l hl j hj
      rw [FMap.mem_set] at hl
      rcases hl with hl | rfl
      · exact c3' l hl j hj
      · have hlen : i.toNat < p.length := by simp only [size] at hi; omega
        have hsz : size (take (i + 1) p) = i + 1 := by
          simp only [size, take, List.length_take]; omega
        by_cases hji : j < i
        · have e1 : take j (take (i + 1) p) = take j (take i p) := by
            simp only [take, List.take_take]; congr 1; omega
          have e2 : take (j + 1) (take (i + 1) p) = take (j + 1) (take i p) := by
            simp only [take, List.take_take]; congr 1; omega
          have e3 : nth default (take (i + 1) p) j = nth default (take i p) j := by
            simp only [nth, if_pos hj.1, take, List.getD_eq_getElem?_getD, List.getElem?_take]
            rw [if_pos (by omega), if_pos (by omega)]
          rw [e1, e2, e3]
          refine c3' _ hdom_pre j ⟨hj.1, ?_⟩
          simp only [size, take, List.length_take]; omega
        · have hj' : j = i := by omega
          subst hj'
          have e1 : take j (take (j + 1) p) = take j p := by
            simp only [take, List.take_take]; congr 1; omega
          have e2 : take (j + 1) (take (j + 1) p) = take (j + 1) p := by
            simp only [take, List.take_take, min_self]
          have e3 : nth default (take (j + 1) p) j = nth default p j := by
            simp only [nth, if_pos hj.1, take, List.getD_eq_getElem?_getD, List.getElem?_take]
            rw [if_pos (by omega)]
          rw [e1, e2, e3, pref_keep _ hdom_pre, hpre]
          exact ⟨sa, sc, rfl, by simp⟩
    · intro l hl
      rw [FMap.mem_set] at hl
      by_cases e : l = take (i + 1) p
      · subst e
        exact ⟨y2, by simp [oget]⟩
      · rcases hl with hl | rfl
        · rw [FMap.get_set_neqE _ _ _ _ e, FMap.get_set_neqE _ _ _ _ e]
          obtain ⟨c, hc⟩ := d4 l hl
          refine ⟨c, ?_⟩
          rw [hp1 l ((FMap.domE _ _).2 (by rw [hc]; simp)), hc]
        · exact absurd rfl e
    · intro l hl
      rw [FMap.mem_set] at hl
      rcases hl with hl | rfl
      · obtain ⟨l2, hl2⟩ := c5 l hl
        rw [FMap.mem_set] at hl2
        rcases hl2 with hq | he
        · exact ⟨l2, (FMap.mem_set _ _ _ _).2 (Or.inl hq)⟩
        · refine ⟨l2 ++ [nth default p i], (FMap.mem_set _ _ _ _).2 (Or.inr ?_)⟩
          rw [ht, ← he]
          simp [rcons]
      · exact ⟨[], (FMap.mem_set _ _ _ _).2 (Or.inr (by simp))⟩
  have hro_key : take (i + 1) p = rcons (take i p) (sa +^ (sa +^ nth default p i)) := by
    rw [xorw_cancel_left]; exact ht
  refine ⟨?_, m_p_set_none _ _ _ _ _ Hmp0 Pm_k, ⟨Unknown, FMap.get_set_sameE _ _ _⟩, ?_, ?_⟩
  · -- the invariant
    have := f_fresh_inv hs ch Pm Pmi Gm Gmi mh mhi ro pi pref _ _ _ (sa +^ nth default p i) sc
      y1 y2 h f (take i p) sa HINV Pm_k hs_h Hpath hinv0 Hmp_new
    rwa [← hro_key] at this
  · -- the path to the new block
    rw [ht, build_hpath_prefix]
    exact ⟨sa, h, build_hpath_up mh _ h y1 ch _ sa h Hpath mh_k, FMap.get_set_sameE _ _ _⟩
  · rw [if_neg (by omega)]
    exact FMap.get_set_sameE _ _ _

/-! ## `CF_G1`: the oracles' losslessness, footprints, and EC's invariant -/

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

end GaudisCrypt.SHA3.Handle

end FirstPort

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

namespace GaudisCrypt.SHA3.Pilot.Handle

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.ConcreteF
open GaudisCrypt.SHA3.Handle
open GaudisCrypt.SHA3.Pilot.ConcreteF (CF)

variable [SLCommon.Params]

/-- EC's `Block.DBlock.dunifin_ll`, as the expectation of `1` (what `auto` leaves). -/
@[simp] theorem bdistr_expected_one : bdistr.expected (fun _ => (1 : ENNReal)) = 1 :=
  (is_lossless_iff_expected _).mp BitWord.dunifin_ll

/-- EC's `Capacity.DCapacity.dunifin_ll`, as the expectation of `1`. -/
@[simp] theorem cdistr_expected_one : cdistr.expected (fun _ => (1 : ENNReal)) = 1 :=
  (is_lossless_iff_expected _).mp BitWord.dunifin_ll

-- (a local tactic macro of the proofs below, declared before them: a syntax declaration waits for
-- every proof before it, its parser run at once)
/-- EC's `smt(get_setE mem_set DBlock.dunifin_ll DCapacity.dunifin_ll)` closing the leaves of
`PFf_Cf`'s second loop in the bad case (the bad event stays, the samplings are lossless), by
hand. -/
local macro "pf_bad_leaf" : tactic => `(tactic| (auto_prep; all_goals (simp_all [FMap.get_setE,
  FMap.mem_set, F.dout, bdistr_expected_one, cdistr_expected_one] <;>
  (intros; (try refine ⟨FMap.get_some _ _ ‹_›, ?_⟩); simp only [← Bool.not_eq_true] at *; tauto))))

-- EC's subtyping `PRIMITIVE <: DPRIMITIVE` (the old port's module types are abbreviations)
module_subtype SLCommon.PRIMITIVE <: DPRIMITIVE

set_option maxHeartbeats 4000000 in
-- one declaration: EC's proof, its two cases on `PF.mi` and three on the handles
/-- EC's `equiv eq_fi (D <: DISTINGUISHER {-PF, -RO, -G1}) : DPRestr(PF).fi ~
DPRestr(G1(DRestr(D)).S).fi : …`, its proof EC's: the call with its invariant, `exists*`, the
ambient cases on `INV_CF_G1`, `PF.mi`, `G1.mi` and the handle's flag, EC's `rcondt`/`rcondf`
positions, and EC's closers (`lemma1'`, `lemma2'`, `m_p_of_INV`; EC's `smt` as `smt_close`).
`D` is not a parameter: neither procedure calls it (EC's restriction only frames the call). -/
theorem eq_fi : equiv[ DPRestr(PF).fi ~ DPRestr(G1.S).fi :
    ¬§G1.bcol{2} ∧ ¬§G1.bext{2} ∧ ={arg} ∧ ={glob C} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}
    ==> if §G1.bcol{2} ∨ §G1.bext{2}
        then FMap.dom §C.queries{1} [] ∧ FMap.dom §C.queries{2} []
        else ={res} ∧ ={glob C} ∧
          INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
            §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2} ] := by
  equiv_proc; stmt_sp; stmt_if <;> equiv_auto
  equiv_call (_ : ¬§G1.bcol{2} ∧ ¬§G1.bext{2} ∧ ={x} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}
    ==> ¬§G1.bcol{2} → ¬§G1.bext{2} → ={res} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}) <;> equiv_auto
  · equiv_exists* §FRO.m{2}, §G1.chandle{2}, §PF.m{1}, §PF.mi{1}, §G1.m{2}, §G1.mi{2}, §G1.mh{2},
      §G1.mhi{2}, §F.RO.m{2}, §G1.paths{2}, §x{2}, §Redo.prefixes{1}, §C.queries{2}
    intro hs ch Pm Pmi Gm Gmi mh mhi ro pi ⟨xa, xc⟩ prefixes queries
    by_cases inv0 : INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries; swap
    · equiv_exfalso; auto_close
    equiv_proc
    rcases Pmi_xaxc : FMap.get Pmi (xa, xc) with _ | ⟨ya, yc⟩
    · have := incli_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0 (xa, xc)
      rcases Gmi_xaxc : FMap.get Gmi (xa, xc) with _ | _; swap
      · simp [Pmi_xaxc, Gmi_xaxc] at this
      stmt_rcondt{1} 1; · hoare_auto; smt_close [FMap.domE]
      stmt_rcondt{2} 1; · hoare_auto; smt_close [FMap.domE]
      rcases hgf : getflag hs xc with _ | f
      · have xc_notrngE1_hs := (getflagP_none _ _).1 hgf
        stmt_rcondt{2} 2; · hoare_auto; smt_close [FMap.rngE]
        stmt_rcondf{2} 8
        · hoare_auto; auto_prep
          rw [huniq_hinvK_h ch _ _ (huniq_addh _ _ _ _ inv0.1.1 xc_notrngE1_hs)
            (FMap.get_set_sameE _ _ _)]
          simp [oget, FMap.domE, notin_hs_notdomE2_mh _ _ _ _ _ inv0.5 (ch_notdomE_hs _ _ inv0.1)]
        equiv_auto
        auto_prep
        rename_i ya _ yc _ _ _ _ _ hcol
        have yc_notrngE1_hs_addh := hinvP (hs.set ch (xc, Known)) yc
        rw [if_pos (by simp at hcol; exact hcol.2)] at yc_notrngE1_hs_addh
        rw [huniq_hinvK_h ch _ _ (huniq_addh _ _ _ _ inv0.1.1 xc_notrngE1_hs)
          (FMap.get_set_sameE _ _ _)]
        simp only [oget, Option.getD_some, FMap.get_set_sameE, true_and]
        rw [show ch + 1 + 1 = ch + 2 by ring]
        have hy2 : ∀ f h, hs.get h ≠ some (yc, f) := fun f h hh => by
          by_cases e : h = ch
          · subst e; simp [ch_notdomE_hs _ _ inv0.1] at hh
          · exact yc_notrngE1_hs_addh h f (by rw [FMap.get_setE, if_neg e]; exact hh)
        refine lemma1' hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries xa xc ya yc inv0 ?_ ?_
          Pmi_xaxc Gmi_xaxc xc_notrngE1_hs hy2
        · rw [FMap.domE]; intro hd
          obtain ⟨⟨a, b⟩, hab⟩ := Option.ne_none_iff_exists'.mp hd
          obtain ⟨hx, fx, -, -, h1, -, -⟩ := inv0.4.1 _ _ _ _ hab
          exact hy2 _ _ h1
        · rintro rfl; exact yc_notrngE1_hs_addh ch Known (FMap.get_set_sameE _ _ _)
      have Hhuniq := inv0.1.1
      cases f
      · have x2_is_U := (getflagP_some _ _ _ Hhuniq).1 hgf
        equiv_conseq (: _ ==> §G1.bext{2})
        · auto_close
        equiv_auto
      have x2_is_K := (getflagP_some _ _ _ Hhuniq).1 hgf
      obtain ⟨hx2, hs_hx2⟩ := id x2_is_K
      stmt_rcondf{2} 2; · hoare_auto
      stmt_rcondf{2} 6
      · hoare_auto; auto_prep
        rw [huniq_hinvK_h hx2 _ _ Hhuniq hs_hx2]
        simp [oget, FMap.domE, notin_m_notin_mh _ _ _ _ _ _ _ inv0.5 Pmi_xaxc hs_hx2]
      equiv_auto
      auto_prep
      rename_i ya _ yc _ _ _ hcol _ _
      have y2_notrngE1_hs := hinvP hs yc
      rw [if_pos (by simp at hcol; exact hcol.2)] at y2_notrngE1_hs
      rw [huniq_hinvK_h hx2 _ _ Hhuniq hs_hx2]
      simp only [oget, Option.getD_some, FMap.get_set_sameE, true_and]
      refine lemma2' hs ch Pm Pmi Gm Gmi mh mhi ro pi prefixes queries xa xc ya yc hx2 inv0 ?_
        Pmi_xaxc Gmi_xaxc hs_hx2 fun f h => y2_notrngE1_hs h f
      rw [FMap.domE]; intro hd
      obtain ⟨⟨a, b⟩, hab⟩ := Option.ne_none_iff_exists'.mp hd
      obtain ⟨hx, fx, -, -, h1, -, -⟩ := inv0.4.1 _ _ _ _ hab
      exact y2_notrngE1_hs _ _ h1
    · stmt_rcondf{1} 1; · hoare_auto; smt_close [FMap.domE]
      rcases Gmi_xaxc : FMap.get Gmi (xa, xc) with _ | ⟨ya', yc'⟩
      · stmt_rcondt{2} 1; · hoare_auto; smt_close [FMap.domE]
        equiv_conseq (: _ ==> §G1.bext{2})
        · auto_close
        equiv_auto
        auto_prep
        -- EC's `have ->: exists hx, hs.[hx] = Some (xc,Unknown)`
        have hU : hs.rng (xc, Unknown) := by
          obtain ⟨hx, fx, hy, fy, hs_hx, hs_hy, hmhi⟩ := inv0.5.1 _ _ _ _ Pmi_xaxc
          obtain ⟨xc', fx', yc', fy', h1, h2, h3⟩ := inv0.8.1 _ _ _ _ ((inv0.3.1 _ _).mpr hmhi)
          simp only [hs_hy, hs_hx, Option.some.injEq, Prod.mk.injEq] at h1 h2
          obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
          cases fx
          · exact ⟨hx, hs_hx⟩
          · simp [(inv0.2.1 _ _).mp h3.1] at Gmi_xaxc
        -- EC's `smt (@Block.DBlock @Capacity.DCapacity)`
        simp [hU]
      have := incli_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0 (xa, xc)
      simp only [Gmi_xaxc, Pmi_xaxc, ne_eq, reduceCtorEq, not_false_eq_true, Option.some.injEq,
        Prod.mk.injEq, forall_const] at this
      obtain ⟨rfl, rfl⟩ := this
      stmt_rcondf{2} 1; · hoare_auto; smt_close [FMap.domE]
      equiv_auto
  · auto_progress
    all_goals
      obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
      smt_close [FMap.domE]

set_option maxHeartbeats 8000000 in
-- one declaration: EC's proof, its cases on `PF.m`, `G1.paths`, the handle's flag and `G1.m`
/-- EC's `equiv eq_f (D <: DISTINGUISHER {-PF, -RO, -G1}) : DPRestr(PF).f ~
DPRestr(G1(DRestr(D)).S).f : …`, its proof EC's: the call with its invariant, `exists*`, the
ambient cases, `seq 2 2`/`seq 0 3`/`seq 0 1` with EC's conditions, `swap{2} 3 -2`, EC's
`rcondt`/`rcondf` positions (`inline F.RO.get` between them), and EC's closers (`lemma1`,
`lemma2`, `lemma3`, `m_p_of_INV`; EC's `smt` as `smt_close`).  Deviations: EC's inline closer of
the path case (~100 lines) is the old port's `f_path_inv`; one `conseq` to `G1.bext{2}` before
the last `auto` of the `Unknown` branch (`auto` with `INV_CF_G1` through the inlined oracle is
too slow). -/
theorem eq_f : equiv[ DPRestr(PF).f ~ DPRestr(G1.S).f :
    ¬§G1.bcol{2} ∧ ¬§G1.bext{2} ∧ ={x} ∧ ={glob C} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}
    ==> if §G1.bcol{2} ∨ §G1.bext{2}
        then FMap.dom §C.queries{2} []
        else ={res} ∧ ={glob C} ∧
          INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
            §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2} ] := by
  equiv_proc; stmt_sp; stmt_if <;> equiv_auto
  equiv_call (_ : ¬§G1.bcol{2} ∧ ¬§G1.bext{2} ∧ ={arg} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}
    ==> if §G1.bcol{2} ∨ §G1.bext{2} then FMap.dom §C.queries{2} []
      else ={res} ∧
        INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
          §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}) <;> equiv_auto
  · equiv_exists* §FRO.m{2}, §G1.chandle{2}, §PF.m{1}, §PF.mi{1}, §G1.m{2}, §G1.mi{2}, §G1.mh{2},
      §G1.mhi{2}, §F.RO.m{2}, §G1.paths{2}, §Redo.prefixes{1}, §C.queries{2}, §x{2}
    intro hs0 ch0 PFm PFmi G1m G1mi G1mh G1mhi ro0 pi0 pref queries ⟨x1, x2⟩
    by_cases inv0 : INV_CF_G1 hs0 ch0 PFm PFmi G1m G1mi G1mh G1mhi ro0 pi0 pref queries; swap
    · equiv_exfalso; auto_close
    equiv_proc
    rcases PFm_x1x2 : FMap.get PFm (x1, x2) with _ | ⟨xa, xc⟩
    · have Gm_x1x2 := notin_m_notin_Gm _ _ (x1, x2) (incl_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0)
        PFm_x1x2
      stmt_rcondt{1} 1; · hoare_auto; smt_close [FMap.domE]
      stmt_rcondt{2} 1; · hoare_auto; smt_close [FMap.domE]
      rcases x2_in_pi : FMap.get pi0 x2 with _ | ⟨p0, v0⟩
      · stmt_rcondf{2} 1; · hoare_auto; smt_close [FMap.domE]
        stmt_rcondf{2} 8; · hoare_auto; smt_close [FMap.domE]
        equiv_seq 2 2 : (hs0 = §FRO.m{2} ∧ ch0 = §G1.chandle{2} ∧ PFm = §PF.m{1} ∧
            PFmi = §PF.mi{1} ∧ G1m = §G1.m{2} ∧ G1mi = §G1.mi{2} ∧ G1mh = §G1.mh{2} ∧
            G1mhi = §G1.mhi{2} ∧ ro0 = §F.RO.m{2} ∧ pi0 = §G1.paths{2} ∧ pref = §Redo.prefixes{1} ∧
            queries = §C.queries{2} ∧ (x1, x2) = §x{2} ∧ ¬§G1.bcol{2} ∧ ¬§G1.bext{2} ∧
            ={x, y1, y2} ∧ INV_CF_G1 hs0 ch0 PFm PFmi G1m G1mi G1mh G1mhi ro0 pi0 pref queries)
        · equiv_auto
        rcases hgf : getflag hs0 x2 with _ | f
        · have x2f_notrngE_hs0 := (getflagP_none _ _).1 hgf
          stmt_rcondt{2} 3; · hoare_auto; smt_close [FMap.rngE]
          stmt_rcondf{2} 6
          · hoare_auto; auto_prep
            rw [huniq_hinvK_h ch0 _ _ (huniq_addh _ _ _ _ inv0.1.1 x2f_notrngE_hs0)
              (FMap.get_set_sameE _ _ _)]
            simp [oget, FMap.domE, notin_hs_notdomE2_mh _ _ _ _ _ inv0.4 (ch_notdomE_hs _ _ inv0.1)]
          equiv_case (x2 ≠ §y2{2} ∧ ∀ f h, hs0.get h ≠ some (§y2{2}, f))
          · equiv_auto; auto_prep
            rename_i _ _ y1 y2 x2_neq_y2 y2_notin_hs _ _ _
            rw [huniq_hinvK_h ch0 _ _ (huniq_addh _ _ _ _ inv0.1.1 x2f_notrngE_hs0)
              (FMap.get_set_sameE _ _ _)]
            obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
            split_ifs
            · simp [FMap.domE, hq]
            simp only [oget, FMap.get_set_sameE, Option.getD_some, true_and]
            rw [show ch0 + 1 + 1 = ch0 + 2 by ring]
            exact lemma1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inv0 x2_neq_y2 PFm_x1x2 Gm_x1x2
              x2f_notrngE_hs0 y2_notin_hs
          · equiv_conseq (: _ ==> §G1.bcol{2})
            · obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
              smt_close [FMap.domE]
            equiv_auto; auto_prep
            rename_i _ _ _ y2 hcase _ _ _
            have hs0_spec := hinvP (hs0.set ch0 (x2, Known)) y2
            split_ifs at hs0_spec with hnone
            · exfalso; apply hcase; constructor
              · rintro rfl; exact hs0_spec ch0 Known (FMap.get_set_sameE _ _ _)
              · intro f h hh
                by_cases e : h = ch0
                · subst e; simp [ch_notdomE_hs _ _ inv0.1] at hh
                · exact hs0_spec h f (by rw [FMap.get_setE, if_neg e]; exact hh)
            · simp [hnone]
        have Hhuniq := inv0.1.1
        cases f
        · have x2_is_U := (getflagP_some _ _ _ Hhuniq).1 hgf
          equiv_conseq (: _ ==> §G1.bext{2})
          · obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
            smt_close [FMap.domE]
          equiv_auto
        have x2_is_K := (getflagP_some _ _ _ Hhuniq).1 hgf
        stmt_rcondf{2} 3; · hoare_auto
        obtain ⟨hx, hs0_hx⟩ := id x2_is_K
        equiv_seq 0 3 : (hs0 = §FRO.m{2} ∧ ch0 = §G1.chandle{2} ∧ PFm = §PF.m{1} ∧
            PFmi = §PF.mi{1} ∧ G1m = §G1.m{2} ∧ G1mi = §G1.mi{2} ∧ G1mh = §G1.mh{2} ∧
            G1mhi = §G1.mhi{2} ∧ ro0 = §F.RO.m{2} ∧ pi0 = §G1.paths{2} ∧ pref = §Redo.prefixes{1} ∧
            queries = §C.queries{2} ∧ (x1, x2) = §x{2} ∧ ¬§G1.bcol{2} ∧ ¬§G1.bext{2} ∧
            ={x, y1, y2} ∧ §y{2} = (§y1{2}, §y2{2}) ∧ §hx2{2} = hx ∧
            INV_CF_G1 hs0 ch0 PFm PFmi G1m G1mi G1mh G1mhi ro0 pi0 pref queries)
        · equiv_auto; auto_progress
          · obtain ⟨h, hs_h⟩ : hs0.rng (x2, Unknown) := by simp_all
            have := Hhuniq _ _ _ _ hs0_hx hs_h rfl; subst this; simp [hs0_hx] at hs_h
          · rw [huniq_hinvK_h hx _ _ Hhuniq hs0_hx]; rfl
        have x1hx_notin_G1m := notin_m_notin_mh _ _ _ _ _ _ _ inv0.4 PFm_x1x2 hs0_hx
        stmt_rcondf{2} 1; · hoare_auto; smt_close [FMap.domE]
        equiv_auto; auto_prep
        rename_i _ _ y1 y2 _ _ _
        obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
        split_ifs with h
        · simp [FMap.domE, hq]
        have hy := hinvP hs0 y2
        rw [if_pos (by simp_all)] at hy
        simp only [oget, FMap.get_set_sameE, Option.getD_some, true_and]
        exact lemma2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inv0 PFm_x1x2 Gm_x1x2 x2_in_pi hs0_hx
          fun f h => hy h f
      obtain ⟨hx2, Hpath, hs_hx2⟩ := (inv0.9.1 _ _ _).mp x2_in_pi
      stmt_rcondt{2} 1; · hoare_auto; smt_close [FMap.domE]
      stmt_rcondf{2} 6; · hoare_auto; hoare_inline*; hoare_auto; smt_close [FMap.rngE]
      stmt_rcondf{2} 7
      · hoare_auto; hoare_inline*; hoare_auto; auto_prep
        rw [huniq_hinvK_h hx2 _ _ inv0.1.1 hs_hx2]
        simp [oget, FMap.domE, notin_m_notin_mh _ _ _ _ _ _ _ inv0.4 PFm_x1x2 hs_hx2]
      stmt_rcondt{2} 15; · hoare_auto; hoare_inline*; hoare_auto; smt_close [FMap.domE]
      stmt_inline (PROM.FullRO.ROmap.get (List block) block F.RO)
      stmt_rcondt{2} 4
      · hoare_auto; auto_prep
        simp [x2_in_pi, oget, FMap.domE,
          f_path_ro_none _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inv0 PFm_x1x2 hs_hx2 Hpath]
      equiv_auto; auto_prep
      rename_i _ _ y1 _ y2 _ _ _ _
      obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
      split_ifs with h
      · simp [FMap.domE, hq]
      have hy : hinv hs0 y2 = none := by simp_all
      simp only [x2_in_pi, oget, Option.getD_some, FMap.get_set_sameE,
        huniq_hinvK_h hx2 _ _ inv0.1.1 hs_hx2, true_and]
      -- EC's inline closer (~100 lines): the old port's lemma
      exact f_path_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inv0 PFm_x1x2 x2_in_pi hs_hx2 Hpath hy
    stmt_rcondf{1} 1; · hoare_auto; smt_close [FMap.domE]
    obtain ⟨hx2, fx2, hy2, fy2, hs_hx2, hs_hy2, G1mh_x1hx2⟩ := inv0.4.1 _ _ _ _ PFm_x1x2
    rcases G1m_x1x2 : FMap.get G1m (x1, x2) with _ | ⟨ya, yc⟩; swap
    · have := incl_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0 (x1, x2)
      simp only [G1m_x1x2, PFm_x1x2, ne_eq, reduceCtorEq, not_false_eq_true, Option.some.injEq,
        Prod.mk.injEq, forall_const] at this
      obtain ⟨rfl, rfl⟩ := this
      stmt_rcondf{2} 1; · hoare_auto; smt_close [FMap.domE]
      equiv_auto
    stmt_rcondt{2} 1; · hoare_auto; smt_close [FMap.domE]
    obtain rfl : fy2 = Unknown := by
      obtain ⟨xc0, xf0, yc0, yf0, h1, h2, h3⟩ := inv0.8.1 _ _ _ _ G1mh_x1hx2
      rw [hs_hx2] at h1; rw [hs_hy2] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
      obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
      cases fy2
      · rfl
      · simp [G1m_x1x2] at h3
    cases fx2
    · stmt_swap{2} 3 -2
      equiv_seq 0 1 : (queries = §C.queries{2} ∧ §G1.bext{2})
      · equiv_auto; smt_close [FMap.rngE]
      equiv_conseq (: _ ==> ¬(§G1.bcol{2} ∨ §G1.bext{2}) → oget (§PF.m{1}.get §x{1}) = §y{2} ∧
          INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
            §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2})
      · obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
        smt_close [FMap.domE]
      stmt_inline*
      -- (not EC's: `auto` through the inlined code with `INV_CF_G1` in the postcondition is
      -- too slow; the postcondition holds as `bext` stays set)
      equiv_conseq (: _ ==> §G1.bext{2})
      · auto_close
      stmt_if{2} <;> equiv_auto
    obtain ⟨xc0, xf0, yc0, yf0, h1, h2, h3⟩ := inv0.8.1 _ _ _ _ G1mh_x1hx2
    rw [hs_hx2] at h1; rw [hs_hy2] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
    simp only [reduceCtorEq, if_false] at h3
    obtain ⟨p0, v0, Hro, Hpath⟩ := h3
    have pi_x2 := (inv0.9.1 x2 p0 v0).2 ⟨hx2, Hpath, hs_hx2⟩
    stmt_rcondt{2} 1; · hoare_auto; smt_close [FMap.domE]
    stmt_inline (PROM.FullRO.ROmap.get (List block) block F.RO)
    stmt_rcondf{2} 4; · hoare_auto; auto_prep; simp [pi_x2, oget, FMap.domE, Hro]
    stmt_rcondf{2} 8; · hoare_auto; smt_close [FMap.rngE]
    stmt_rcondt{2} 9
    · hoare_auto; auto_prep
      rw [huniq_hinvK_h hx2 _ _ inv0.1.1 hs_hx2]
      simp [oget, FMap.domE, G1mh_x1hx2, FMap.in_dom_with, hs_hy2]
    stmt_rcondt{2} 14; · hoare_auto; smt_close [FMap.domE]
    equiv_auto; auto_prep
    refine ⟨by simp [F.dout], fun _ _ => ⟨by simp, fun _ _ => ?_⟩⟩
    rw [huniq_hinvK_h hx2 _ _ inv0.1.1 hs_hx2]
    simp only [pi_x2, oget, Option.getD_some, Hro, G1mh_x1hx2, hs_hy2, PFm_x1x2]
    obtain ⟨-, hq, -, -, -⟩ := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ inv0
    split_ifs with h
    · simp [FMap.domE, hq]
    exact ⟨trivial, lemma3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inv0 PFm_x1x2 G1m_x1x2 G1mh_x1hx2
      hs_hx2 hs_hy2 pi_x2⟩

module_subtype FUNCTIONALITY <: DFUNCTIONALITY

/-- EC's first bullet of `PFf_Cf`'s first loop body (`prefix_gt0_mem`, `prefix_take_leq`, the
`m_p` part of the invariant): the next prefix of a queried path is known. -/
theorem PFf_Cf_dom_next (hs : handles) (ch : handle) (Pm Pmi Gm Gmi : smap) (mh mhi : hsmap)
    (ro : FMap (List block) block) (pi : FMap capacity (List block × block))
    (pref : FMap (List block) SLCommon.state) (Q : FMap (List block) block) (p : List block) (i : ℤ)
    (hI : INV_CF_G1 hs ch Pm Pmi Gm Gmi mh mhi ro pi pref Q) (hi0 : 0 ≤ i)
    (hi : i < «prefix» p (get_max_prefix p (elems (FMap.fdom Q)))) :
    FMap.dom pref (take (i + 1) p) := by
  have hmp := m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ hI
  have hmem : FMap.dom Q (get_max_prefix p (elems (FMap.fdom Q))) :=
    (mem_elems_fdom _ _).1 (prefix_gt0_mem _ _ (by omega))
  rw [prefix_take_leq p (get_max_prefix p (elems (FMap.fdom Q))) (i + 1) (by omega)]
  obtain ⟨-, -, -, Iq, -⟩ := id hmp
  obtain ⟨c, hc⟩ := Iq _ hmem
  exact all_prefixes_of_m_p _ _ _ hmp _ ((FMap.domE _ _).2 (by simp [hc])) _

/-! Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* GAP 2: the second loop still uses the older `equiv_while_raw` (four goals, no frame); the
  first is EC's `while I` (`equiv_while`) with EC's `auto; progress` and its bullets.
* GAP 5: the pilot's oracle lemmas (`eq_f`, `eq_fi`, `PFf_Cf`, in EC's paths through
  `module_subtype` coercions) match `CF_G1`'s oracles (the old port's `CF`/`G1` views) only by
  heavy unfolding (~2M heartbeats per `conseq`): goes away with EC-form `CF`/`G1` declarations.
-/

set_option maxHeartbeats 8000000 in
/-- EC's `equiv PFf_Cf (D <: DISTINGUISHER) : DFRestr(SqueezelessSponge(PF)).f ~
DFRestr(G1(DRestr(D)).M).f : …`, its proof EC's, block by block (EC's lines as comments): `proc;
sp; inline*`, the `if`s with `1,3:auto`, `swap`, `wp 1 5`, `conseq`, `seq 1 1`, `splitwhile`,
the two loops with EC's invariants, `alias`, `case`, `rcondt`/`rcondf` at EC's positions.
Deviations: hand closers where `smt_close` fails (EC's `smt`); EC's long inline closers are the
old port's lemmas (`PJ1_step`, `PJ1_PJ2`, `PJ2_known`, `PJ2_fresh`, `PJ2L_step`); `={bs}` added
to the first loop's invariant and the left's samplings swapped for EC's `swap{2} -3` (the gaps
listed above). -/
theorem PFf_Cf : equiv[ DFRestr(SqueezelessSponge(PF)).f ~ DFRestr(G1.M).f :
    ¬(§G1.bcol{2} ∨ §G1.bext{2}) ∧ ={arg} ∧ ={glob C} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2}
    ==> if §G1.bcol{2} ∨ §G1.bext{2}
        then FMap.dom §C.queries{2} []
        else ={glob C} ∧ ={res} ∧
          INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
            §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2} ] := by
  -- EC: proc;sp;inline*;sp.
  --     (EC's second `sp` has nothing to do here: dropped)
  equiv_proc; stmt_sp; stmt_inline*
  -- EC: if;1,3:auto;if;1,3:auto;swap{1}4;swap{2}11;sp;wp 1 5.
  stmt_if; on_goals 1, 3 => equiv_auto
  stmt_if; on_goals 1, 3 => equiv_auto
  stmt_swap{1} 4; stmt_swap{2} 11; stmt_sp; stmt_wp 1 5
  -- EC: sp;conseq(:_==> ! (G1.bcol{2} \/ G1.bext{2}) =>
  --         ={glob C, sa} /\
  --         INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2} G1.mh{2}
  --           G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1} C.queries{2}.[bs{1} <- sa{1}] /\
  --         F.RO.m.[p]{2} = Some sa{2});progress.
  --     (EC's `sp` has nothing to do here: dropped)
  equiv_conseq (: _ ==> ¬(§G1.bcol{2} ∨ §G1.bext{2}) →
      ={glob C, sa} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1}
        (FMap.set §C.queries{2} §bs{1} §sa{1}) ∧
      FMap.get §F.RO.m{2} §p{2} = some §sa{2})
  · auto_prep
    split_ifs
    -- EC: + by rewrite mem_set domE;left;have[]_->_ _ _//=:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0.
    · obtain ⟨-, hq, -, -, -⟩ :=
        m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
      smt_close [FMap.mem_set, FMap.domE]
    -- EC: + smt(mem_set).  + smt(mem_set).  + smt(mem_set).
    · auto_close
  -- EC: seq 1 1:
  --       (={i, p, glob C} /\ i{1} = size p{1} /\ p{2} = bs{1} /\
  --         (!(G1.bcol{2} \/ G1.bext{2}) =>
  --         (INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2}
  --           G1.mh{2} G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1}
  --           C.queries{2}.[bs{1} <- sa{1}]
  --         /\ ={sa} /\ F.RO.m.[p]{2} = Some sa{1})));last first.
  equiv_seq 1 1 : (={i, p, glob C} ∧ §i{1} = size §p{1} ∧ §p{2} = §bs{1} ∧
      (¬(§G1.bcol{2} ∨ §G1.bext{2}) →
        INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
          §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1}
          (FMap.set §C.queries{2} §bs{1} §sa{1}) ∧
        ={sa} ∧ FMap.get §F.RO.m{2} §p{2} = some §sa{1}))
  rotate_right
  -- EC: + case : (! (G1.bcol{2} \/ G1.bext{2}));last first.
  · equiv_case (¬(§G1.bcol{2} ∨ §G1.bext{2}))
    rotate_right
    -- EC: - by conseq(:_==>true);progress;auto;smt(DBlock.dunifin_ll DCapacity.dunifin_ll take_size).
    · equiv_conseq (: _ ==> True)
      · auto_close
      · equiv_auto
    -- EC: by rcondf{2}3;auto;smt(domE DBlock.dunifin_ll DCapacity.dunifin_ll take_size).
    · stmt_rcondf{2} 3
      · hoare_auto; smt_close [FMap.domE]
      equiv_auto
      auto_prep; simp_all [F.dout, oget]

  -- EC: conseq(:_==> ={i, p, glob C} /\ i{1} = size p{1} /\ p{2} = bs{1} /\
  --       (!(G1.bcol{2} \/ G1.bext{2}) =>
  --       (INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2}
  --         G1.mh{2} G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1}
  --         C.queries{2}.[take i{2} bs{1} <- sa{1}]
  --       /\ ={sa} /\ F.RO.m.[p]{2} = Some sa{1})));1:smt(take_size).
  equiv_conseq (: _ ==> ={i, p, glob C} ∧ §i{1} = size §p{1} ∧ §p{2} = §bs{1} ∧
      (¬(§G1.bcol{2} ∨ §G1.bext{2}) →
        INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
          §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1}
          (FMap.set §C.queries{2} (take §i{2} §bs{1}) §sa{1}) ∧
        ={sa} ∧ FMap.get §F.RO.m{2} §p{2} = some §sa{1}))
  · smt_close [take_size]
  -- EC: splitwhile{1} 1 : i < prefix p (get_max_prefix p (elems (fdom C.queries))).
  --     splitwhile{2} 1 : i < prefix p (get_max_prefix p (elems (fdom C.queries))).
  stmt_splitwhile{1} 1 : §i < «prefix» §p (get_max_prefix §p (elems (FMap.fdom §C.queries)))
  stmt_splitwhile{2} 1 : §i < «prefix» §p (get_max_prefix §p (elems (FMap.fdom §C.queries)))
  -- EC: seq 1 1 : (={p, i, glob C, bs} /\ bs{2} = p{2} /\
  --       (prefix p (get_max_prefix p (elems (fdom C.queries))) = i){2} /\
  --       (Redo.prefixes.[take i p]{1} = Some (sa,sc){1}) /\
  --       (take i p \in Redo.prefixes){1} /\
  --       (C.queries.[[]] = Some b0){1} /\
  --       (! p{2} \in C.queries{2}) /\
  --       (!(G1.bcol{2} \/ G1.bext{2}) =>
  --         (INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2}
  --           G1.mh{2} G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1}
  --           C.queries{2} /\
  --           ={sa} /\  counter{2} = 0 /\
  --           (exists f, FRO.m.[h]{2} = Some (sc{1}, f)) /\
  --           (build_hpath G1.mh (take i p) = Some (sa,h)){2} /\
  --           if i{2} = 0 then (sa,h){2} = (b0, 0)
  --           else F.RO.m.[take i p]{2} = Some sa{1})) /\
  --       (i{2} = 0 => sa{1} = b0) /\ 0 < size p{2}).
  equiv_seq 1 1 : (={p, i, glob C, bs} ∧ §bs{2} = §p{2} ∧
      «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2}))) = §i{2} ∧
      FMap.get §Redo.prefixes{1} (take §i{1} §p{1}) = some (§sa{1}, §sc{1}) ∧
      FMap.dom §Redo.prefixes{1} (take §i{1} §p{1}) ∧
      FMap.get §C.queries{1} [] = some b0 ∧
      ¬FMap.dom §C.queries{2} §p{2} ∧
      (¬(§G1.bcol{2} ∨ §G1.bext{2}) →
        INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
          §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2} ∧
        ={sa} ∧ §counter{2} = 0 ∧
        (∃ f, FMap.get §FRO.m{2} §h{2} = some (§sc{1}, f)) ∧
        build_hpath §G1.mh{2} (take §i{2} §p{2}) = some (§sa{2}, §h{2}) ∧
        (if §i{2} = 0 then (§sa{2}, §h{2}) = (b0, 0)
          else FMap.get §F.RO.m{2} (take §i{2} §p{2}) = some §sa{1})) ∧
      (§i{2} = 0 → §sa{1} = b0) ∧ 0 < size §p{2})
  -- EC: + while(={p, i, glob C} /\ bs{2} = p{2} /\ (i{2} = 0 => sa{1} = b0) /\
  --         (0 <= i <= prefix p (get_max_prefix p (elems (fdom C.queries)))){2} /\
  --         (Redo.prefixes.[take i p]{1} = Some (sa,sc){1}) /\
  --         (take i p \in Redo.prefixes){1} /\
  --         (C.queries.[[]] = Some b0){1} /\
  --         (! p{2} \in C.queries{2}) /\
  --         (!(G1.bcol{2} \/ G1.bext{2}) =>
  --           (INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2}
  --             G1.mh{2} G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1}
  --             C.queries{2} /\
  --             ={sa} /\  counter{2} = 0 /\
  --             (exists f, FRO.m.[h]{2} = Some (sc{1}, f)) /\
  --             (build_hpath G1.mh (take i p) = Some (sa,h)){2} /\
  --             if i{2} = 0 then (sa,h){2} = (b0, 0)
  --             else F.RO.m.[take i p]{2} = Some sa{1})) /\ 0 < size p{2});last first.
  · equiv_while (={p, i, glob C} ∧ §bs{2} = §p{2} ∧ (§i{2} = 0 → §sa{1} = b0) ∧
        0 ≤ §i{2} ∧ §i{2} ≤ «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2}))) ∧
        FMap.get §Redo.prefixes{1} (take §i{1} §p{1}) = some (§sa{1}, §sc{1}) ∧
        FMap.dom §Redo.prefixes{1} (take §i{1} §p{1}) ∧
        FMap.get §C.queries{1} [] = some b0 ∧
        ¬FMap.dom §C.queries{2} §p{2} ∧
        (¬(§G1.bcol{2} ∨ §G1.bext{2}) →
          INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
            §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2} ∧
          ={sa} ∧ §counter{2} = 0 ∧
          (∃ f, FMap.get §FRO.m{2} §h{2} = some (§sc{1}, f)) ∧
          build_hpath §G1.mh{2} (take §i{2} §p{2}) = some (§sa{2}, §h{2}) ∧
          (if §i{2} = 0 then (§sa{2}, §h{2}) = (b0, 0)
            else FMap.get §F.RO.m{2} (take §i{2} §p{2}) = some §sa{1})) ∧
        0 < size §p{2})
    -- EC: - auto;progress.
    --       * smt(@Prefix).  * by have[]:=m_p_of_INV … H0;smt(take0 domE). (×2)
    --       * by have[]:=m_p_of_INV … H0.  * by have[]:=hs_of_INV … H0;smt(take0 domE).
    --       * by rewrite build_hpathP; apply/Empty=> //; exact/take0.
    --       * by have[]:=m_p_of_INV … H0; smt(take0 domE size_take size_eq0 size_ge0).
    --       * smt(prefix_sizel).
    case hpre =>
      equiv_auto; auto_progress
      -- EC: * smt(@Prefix).
      · exact prefix_ge0 _ _
      -- EC: * by have[]:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0;smt(take0 domE).
      · obtain ⟨hp0, -, -, -, -⟩ :=
          m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
        smt_close [take, FMap.domE]
      -- EC: * by have[]:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0;smt(take0 domE).
      · obtain ⟨hp0, -, -, -, -⟩ :=
          m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
        smt_close [take, FMap.domE]
      -- EC: * by have[]:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0.
      · obtain ⟨-, hq, -, -, -⟩ :=
          m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
        exact hq
      -- EC: * by have[]:=hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0;smt(take0 domE).
      · obtain ⟨-, h0, -⟩ := hs_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
        exact ⟨Known, h0⟩
      -- EC: * by have[]:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0;
      --       smt(take0 domE size_take size_eq0 size_ge0).
      · obtain ⟨-, hq, -, -, -⟩ :=
          m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
        by_contra hsz
        simp only [size, not_lt, Nat.cast_nonpos, List.length_eq_zero_iff] at hsz
        subst hsz; simp_all [FMap.domE]
      -- EC: * smt(prefix_sizel).
      · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at *
        smt_close [prefix_sizel]
    case body =>
      -- EC: case(G1.bcol{2} \/ G1.bext{2}).
      equiv_case (§G1.bcol{2} ∨ §G1.bext{2})
      -- EC: - by if{1};auto;conseq(:_==> (G1.bcol{2} \/ G1.bext{2}));1,3:smt(domE get_setE);
      --         (if{2};2:if{2});auto;1:smt(DBlock.dunifin_ll DCapacity.dunifin_ll);
      --         sp;if{1};auto;smt(DBlock.dunifin_ll DCapacity.dunifin_ll).
      · stmt_if{1} <;> ((equiv_auto; equiv_conseq (: _ ==> §G1.bcol{2} ∨ §G1.bext{2})) <;> [
          (auto_prep
           all_goals (split_ands <;> (try omega) <;> (try simp only [Prod.mk.eta]) <;>
             (try (apply FMap.get_some; simp_all)) <;> (try simp_all [FMap.domE])));
          (stmt_if{2}; on_goals 2 => stmt_if{2})])
        all_goals equiv_auto
        all_goals try (stmt_sp; stmt_if{1} <;> equiv_auto)
        -- EC's `smt(DBlock.dunifin_ll DCapacity.dunifin_ll)`: the samplings are lossless, the bad
        -- event stays
        all_goals (auto_prep
                   all_goals simp_all [F.dout, bdistr_expected_one, cdistr_expected_one])
      -- EC: conseq(: ={p, i, glob C} /\ bs{2} = p{2} /\ (i{2} = 0 => sa{1} = b0) /\
      --       0 <= i{2} <= prefix p{2} (get_max_prefix p{2} (elems (fdom C.queries{2}))) /\
      --       Redo.prefixes{1}.[take i{1} p{1}] = Some (sa{1}, sc{1}) /\
      --       (C.queries.[[]] = Some b0){1} /\ (! p{2} \in C.queries{2}) /\
      --       (take i{1} p{1} \in Redo.prefixes{1}) /\
      --       (! (G1.bcol{2} \/ G1.bext{2}) =>
      --         INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2}
      --         G1.mh{2} G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1}
      --         C.queries{2} /\
      --         ={sa} /\
      --         counter{2} = 0 /\
      --         (exists (f : flag), FRO.m{2}.[h{2}] = Some (sc{1}, f)) /\
      --           build_hpath G1.mh{2} (take i{2} p{2}) = Some (sa{2}, h{2}) /\
      --         if i{2} = 0 then (sa{2}, h{2}) = (b0, 0)
      --           else F.RO.m{2}.[take i{2} p{2}] = Some sa{1}) /\
      --     (i{1} < size p{1} /\
      --       i{1} < prefix p{1} (get_max_prefix p{1} (elems (fdom C.queries{1})))) /\
      --       i{2} < size p{2} /\
      --       i{2} < prefix p{2} (get_max_prefix p{2} (elems (fdom C.queries{2}))) /\
      --       ! (G1.bcol{2} \/ G1.bext{2}) /\ (take (i+1) p \in Redo.prefixes){1} /\
      --       0 < size p{2}
      --       ==>_);progress.
      · equiv_conseq (: ={p, i, glob C} ∧ §bs{2} = §p{2} ∧ (§i{2} = 0 → §sa{1} = b0) ∧
            0 ≤ §i{2} ∧ §i{2} ≤ «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2}))) ∧
            FMap.get §Redo.prefixes{1} (take §i{1} §p{1}) = some (§sa{1}, §sc{1}) ∧
            FMap.get §C.queries{1} [] = some b0 ∧ ¬FMap.dom §C.queries{2} §p{2} ∧
            FMap.dom §Redo.prefixes{1} (take §i{1} §p{1}) ∧
            (¬(§G1.bcol{2} ∨ §G1.bext{2}) →
              INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
                §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2} ∧
              ={sa} ∧ §counter{2} = 0 ∧
              (∃ f, FMap.get §FRO.m{2} §h{2} = some (§sc{1}, f)) ∧
              build_hpath §G1.mh{2} (take §i{2} §p{2}) = some (§sa{2}, §h{2}) ∧
              (if §i{2} = 0 then (§sa{2}, §h{2}) = (b0, 0)
                else FMap.get §F.RO.m{2} (take §i{2} §p{2}) = some §sa{1})) ∧
            (§i{1} < size §p{1} ∧
              §i{1} < «prefix» §p{1} (get_max_prefix §p{1} (elems (FMap.fdom §C.queries{1})))) ∧
            §i{2} < size §p{2} ∧
            §i{2} < «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2}))) ∧
            ¬(§G1.bcol{2} ∨ §G1.bext{2}) ∧ FMap.dom §Redo.prefixes{1} (take (§i{1} + 1) §p{1}) ∧
            0 < size §p{2} ==> _)
        -- EC: - have:=prefix_gt0_mem p{2} (elems (fdom C.queries{2})) _;1:rewrite/#. … (10 lines)
        --     (as the lemma `PFf_Cf_dom_next`)
        · auto_prep
          simp only [Bool.and_eq_true, decide_eq_true_eq] at *
          casesm* _ ∧ _
          all_goals (split_ands <;> (try assumption) <;>
            (try exact PFf_Cf_dom_next _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_›) <;>
            (try (glob_tuples; simp_all)))
        -- EC: rcondt{1}1;1:auto;progress.
        stmt_rcondt{1} 1; on_goals 1 => hoare_auto
        -- EC: rcondt{2}1;1:auto;progress.
        stmt_rcondt{2} 1
        -- EC: - have[]HINV[]->>/=[]->>/=[]H_h[]H_path H_F_RO:=H6 H11.
        --       have//=:=lemma5 _ _ _ _ _ _ _ _ _ _ _ _ i{hr} p{hr} sa{hr} sc{m} h{hr} HINV _ _ _ _.
        --       … by move=>[]b2 c2 h2[]H_PFm H_Gmh;rewrite domE H_Gmh/=.
        · hoare_auto; auto_prep
          obtain ⟨b', c', h', -, hmh⟩ := lemma5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _› ⟨by omega, by omega⟩ ‹_› ‹_› ⟨_, ‹_›⟩
          simp [FMap.domE, hmh]
        -- EC: auto;progress.
        equiv_auto
        --     (EC's twelve bullets, ~60 lines with `lemma5`, `m_mh_of_INV`, `mh_of_INV`,
        --     `build_hpath_prefix`: the old port's `PJ1_step`, the loop's step — deviation)
        rintro p₁ i₁ c₁ q₁ sa₁ pref sc₁ m₁ mi₁ p₂ i₂ c₂ q₂ bs₂ bcol bext hs ch gm gmi mh mhi ro paths
          sa₂ cnt h ⟨⟨hp, hi, ⟨hc, hqq⟩⟩, hbs2, hsa0, hi0, hiq, hpref, hq0, hq, hdom, hJ,
            ⟨hi1, hi1'⟩, -, -, hbad, hdom1, hsz⟩
        subst hp hi hc hqq
        obtain ⟨hI, rfl, hcnt, ⟨f, hh⟩, hb, hif⟩ := hJ hbad
        have hJ1 : PJ1 hs ch m₁ mi₁ gm gmi mh mhi ro paths pref q₁ p₁ i₁ sa₁ sc₁ h :=
          ⟨hI, hpref, ⟨f, hh⟩, hb, by simpa using hif, hi0, hiq, hq, hsz⟩
        obtain ⟨-, -, he, hI', hpref', hh', hb', hif', hi0', hiq', -, -⟩ :=
          PJ1_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hJ1 hi1'
        refine ⟨⟨⟨rfl, rfl, rfl, rfl⟩, hbs2, fun h0 => absurd h0 (by omega), by omega, hiq',
          hpref', hdom1, hq0, hq, fun _ => ⟨hI', he, hcnt, hh', by rw [← he]; exact hb', ?_⟩, hsz⟩,
          rfl⟩
        rw [if_neg (by omega)] at hif' ⊢
        exact hif'
  -- EC: alias{1} 1 prefixes = Redo.prefixes;sp.
  --     alias{2} 1 bad1     = G1.bcol;sp.
  stmt_alias{1} 1 prefixes = §Redo.prefixes
  stmt_sp
  stmt_alias{2} 1 bad1 = §G1.bcol
  stmt_sp
  -- EC: while (  ={i, p, C.queries, C.c}
  --       /\ prefix p{2} (get_max_prefix p{2} (elems (fdom C.queries{2}))) <=
  --         i{1} <= size p{1}
  --       /\ Redo.prefixes{1}.[take i{2} p{2}] = Some (sa{1}, sc{1})
  --       /\ p{2} = bs{1}
  --       /\ (! p{2} \in C.queries{2})
  --       /\ (! (G1.bcol{2} \/ G1.bext{2}) =>
  --           INV_CF_G1 FRO.m{2} G1.chandle{2} PF.m{1} PF.mi{1} G1.m{2} G1.mi{2}
  --             G1.mh{2} G1.mhi{2} F.RO.m{2} G1.paths{2} Redo.prefixes{1}
  --             C.queries{2}.[take i{2} bs{1} <- sa{1}]
  --         /\ ! (bad1{2} \/ G1.bext{2})
  --         /\ m_p PF.m{1} prefixes{1} C.queries{2}
  --         /\ (forall (l : block list),
  --              l \in prefixes{1} => prefixes{1}.[l] = Redo.prefixes{1}.[l])
  --         /\ (forall (l : block list), l \in Redo.prefixes{1} =>
  --              (l \in prefixes{1}) \/
  --              exists (j : int), 0 <= j <= i{2} /\ take j p{2} = l)
  --         /\ ={sa}
  --         /\ counter{2} <= i{2} - prefix p{2}
  --            (get_max_prefix p{2} (elems (fdom C.queries{2})))
  --         /\ (exists (f : flag), FRO.m{2}.[h{2}] = Some (sc{1}, f))
  --         /\ build_hpath G1.mh{2} (take i{2} p{2}) = Some (sa{2}, h{2})
  --         /\ (if i{2} = 0 then (sa{2}, h{2}) = (b0, 0)
  --             else F.RO.m{2}.[take i{2} p{2}] = Some sa{1})
  --         /\ (i{2} < size p{2} => ! take (i{2}+1) p{2} \in Redo.prefixes{1})));last first.
  equiv_while_raw (={i, p, C.queries, C.c} ∧
      «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2}))) ≤ §i{1} ∧
      §i{1} ≤ size §p{1} ∧
      FMap.get §Redo.prefixes{1} (take §i{2} §p{2}) = some (§sa{1}, §sc{1}) ∧
      §p{2} = §bs{1} ∧
      ¬FMap.dom §C.queries{2} §p{2} ∧
      (¬(§G1.bcol{2} ∨ §G1.bext{2}) →
        INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
          §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1}
          (FMap.set §C.queries{2} (take §i{2} §bs{1}) §sa{1}) ∧
        ¬(§bad1{2} ∨ §G1.bext{2}) ∧
        m_p §PF.m{1} §prefixes{1} §C.queries{2} ∧
        (∀ l, FMap.dom §prefixes{1} l → FMap.get §prefixes{1} l = FMap.get §Redo.prefixes{1} l) ∧
        (∀ l, FMap.dom §Redo.prefixes{1} l →
          FMap.dom §prefixes{1} l ∨ ∃ j, 0 ≤ j ∧ j ≤ §i{2} ∧ take j §p{2} = l) ∧
        ={sa} ∧
        §counter{2} ≤ §i{2} - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2}))) ∧
        (∃ f, FMap.get §FRO.m{2} §h{2} = some (§sc{1}, f)) ∧
        build_hpath §G1.mh{2} (take §i{2} §p{2}) = some (§sa{2}, §h{2}) ∧
        (if §i{2} = 0 then (§sa{2}, §h{2}) = (b0, 0)
          else FMap.get §F.RO.m{2} (take §i{2} §p{2}) = some §sa{1}) ∧
        (§i{2} < size §p{2} → ¬FMap.dom §Redo.prefixes{1} (take (§i{2} + 1) §p{2}))))
  case guard => auto_close
  -- EC (of the second goal): part of `auto;progress.`: `rewrite/#`, `smt(take_size)`
  case exit =>
    auto_prep
    rename_i pref sa sc pm pmi pref0 i p q c bcol bext hs ch gm gmi mh mhi ro paths bad1 sa2 cnt h
      hpref hq hpi hi hJ hg
    have hip : i = size p := by omega
    refine ⟨hip, fun hb => ?_⟩
    obtain ⟨hI, -, hmp, -, -, rfl, -, -, -, hif, -⟩ := hJ hb
    obtain ⟨-, hq0, -, -, -⟩ := hmp
    have hp0 : p ≠ [] := by rintro rfl; exact hq ((FMap.domE _ _).2 (by simp [hq0]))
    have hi0 : i ≠ 0 := by
      rw [hip]; cases p with
      | nil => exact absurd rfl hp0
      | cons _ _ => simp only [size, List.length_cons]; omega
    rw [if_neg hi0] at hif
    simp only [hip, take_size] at hI hif ⊢
    exact ⟨hI, by simp, hif⟩
  -- EC: + auto;progress.
  --     (fifteen bullets: `prefix_sizel`, `m_p_of_INV`, `mem_set`, `prefix_exchange_prefix_inv`,
  --     `take_size`; the old port's `PJ1_PJ2`, the first loop's end as the second's start —
  --     deviation)
  case hpre =>
    equiv_auto
    rintro p₁ i₁ c₁ q₁ bs₁ pref sa₁ sc₁ m₁ mi₁ pref0 p₂ i₂ c₂ q₂ bs₂ bcol bext hs ch gm gmi mh mhi ro
      paths sa₂ cnt h bad1 ⟨⟨⟨⟨hp, hi, ⟨hc, hqq⟩, hbs⟩, hbs2, hpi, hpref, -, -, hq, hJ, -, hsz⟩, rfl⟩,
        rfl⟩
    subst hp hi hc hqq hbs hbs2
    refine ⟨⟨rfl, rfl, rfl, rfl⟩, hpi.le, by rw [← hpi]; exact prefix_sizel _ _, hpref, rfl, hq,
      fun hb => ?_⟩
    obtain ⟨hI, rfl, rfl, ⟨f, hh⟩, hb', hif⟩ := hJ hb
    have hJ1 : PJ1 hs ch m₁ mi₁ gm gmi mh mhi ro paths pref0 q₁ bs₁ i₁ sa₁ sc₁ h :=
      ⟨hI, hpref, ⟨f, hh⟩, hb', by simpa using hif, by rw [← hpi]; exact prefix_ge0 _ _, hpi.ge,
        hq, hsz⟩
    obtain ⟨⟨hI2, hmp, -, -, -⟩, ⟨-, -, -, hnext, -⟩⟩ :=
      PJ1_PJ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hJ1 (by unfold qpre; omega)
    exact ⟨hI2, hb, hmp, fun _ _ => rfl, fun _ hl => Or.inl hl, rfl, by omega, ⟨f, hh⟩, hb', hif,
      hnext⟩
  case body =>
    -- EC: case : (! (G1.bcol{2} \/ G1.bext{2}));last first.
    equiv_case (¬(§G1.bcol{2} ∨ §G1.bext{2}))
    rotate_right
    -- EC: - wp 1 1=>/=.
    · stmt_wp 1 1
      -- EC: conseq(:_==> Redo.prefixes{1}.[take (i{1}+1) p{1}] = Some (sa{1}, sc{1})
      --           /\ (take (i{1} + 1) p{1} \in Redo.prefixes{1})
      --           /\ (G1.bcol{2} \/ G1.bext{2}));1:smt(prefix_ge0).
      equiv_conseq (: _ ==>
          FMap.get §Redo.prefixes{1} (take (§i{1} + 1) §p{1}) = some (§sa{1}, §sc{1}) ∧
          FMap.dom §Redo.prefixes{1} (take (§i{1} + 1) §p{1}) ∧ (§G1.bcol{2} ∨ §G1.bext{2}))
      · auto_prep
        all_goals (split_ands <;> (try omega); try simp_all)
      -- EC's closer of every leaf below: smt(get_setE mem_set DBlock.dunifin_ll DCapacity.dunifin_ll)
      -- EC: if {1}; last first.
      stmt_if{1}; rotate_right
      -- EC: + sp; if {1}; if {2}; last first.
      · stmt_sp; stmt_if{1} <;> stmt_if{2}
        rotate_right
        -- EC: + if {2}; sp; auto=> />. (+ smt …) smt …
        · stmt_if{2} <;> equiv_auto <;> pf_bad_leaf
        -- EC: + auto=> />. smt …
        · equiv_auto; pf_bad_leaf
        -- EC: + if {2}; last first. + auto=> />. smt … + swap {2} 4 -3; auto=> />. smt …
        · stmt_if{2}; rotate_right
          · equiv_auto; pf_bad_leaf
          · stmt_swap{2} 4 -3; equiv_auto; pf_bad_leaf
        -- EC: auto=> />. smt …
        · equiv_auto; pf_bad_leaf
      -- EC: if {2}. + auto=> />. smt …  if {2}. + auto=> />. smt …  auto=> />. smt …
      · stmt_if{2}
        · equiv_auto; pf_bad_leaf
        · stmt_if{2}
          · equiv_auto; pf_bad_leaf
          · equiv_auto; pf_bad_leaf
    -- EC: rcondf{1}1;1:auto=>/#.
    stmt_rcondf{1} 1; on_goals 1 => hoare_auto
    -- EC: sp;wp.
    stmt_sp; stmt_wp
    -- EC: if{1};2:rcondt{2}1;first last;3:rcondf{2}1;..3:auto.
    --     (as bullets: the known case first, EC's `first last`)
    stmt_if{1}
    rotate_left
    -- the left's `x` is in `PF.m`: the right's handle path is known
    · stmt_rcondt{2} 1
      -- EC: + progress.
      --     have[]HINV[]Hbad[]HINV0[]Hp1[]Hp2[]->>[]H_counter[]H_h[]H_path[]H_F_RO H_take_not_in:=H3 H6.
      --     have:=lemma5' _ _ _ _ _ _ _ _ _ _ _ _ i{hr} bs{m} sa{hr} sc{m} h{hr} HINV _ _ _.
      --     - smt(prefix_ge0).  - exact H1.  - exact H_h.
      --     by have:=H7;rewrite !domE=>->/=/#.
      · hoare_auto; auto_prep
        rcases lemma5' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
            ⟨le_trans (prefix_ge0 _ _) ‹_›, ‹_›⟩ ‹_› ⟨_, ‹_›⟩ with ⟨b', c', h', -, hmh⟩ | ⟨hP, -⟩
        · simp [FMap.domE, hmh]
        · simp_all [FMap.domE]
      -- EC: + progress. … (the known block, ~60 lines: `m_p_of_INV`, `mem_set`, `get_setE`,
      --     `take_take`, `nth_take`, `prefix_exchange_prefix_inv`, …) — the old port's
      --     `PJ2_known` and `PJ2L_step` (deviation)
      equiv_auto
      auto_prep
      rename_i pref m mi pref0 i p q c bcol bext hs ch gm gmi mh mhi ro paths bad1 cnt h w hb hpref
        hq hb1 hmp hpp hext hcnt hqi hisz hI hpath hi hif f hh hnd hdom
      have hJ : PJ2 hs ch m mi gm gmi mh mhi ro paths pref pref0 q p i w.1 w.2 h :=
        ⟨hI, hmp, ⟨f, hh⟩, hpath, by simpa using hif⟩
      have hL : PJ2L pref pref0 q p i w.1 w.2 :=
        ⟨hpref, fun l hl => (hpp l hl).symm, hext, fun _ => hnd, hqi, hisz, hq⟩
      obtain ⟨-, hfst, hI', hmp', ⟨f', hh'⟩, hpath', hif'⟩ :=
        PJ2_known _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hJ hL hi (by simpa using hdom)
      have hL' := PJ2L_step _ _ _ _ _ _ _ (oget (FMap.get m (w.1 +^ nth default p i, w.2))).1
        (oget (FMap.get m (w.1 +^ nth default p i, w.2))).2 hL hi (all_prefixes_of_m_p _ _ _ hmp)
      simp only [Prod.mk.eta] at hL' ⊢
      obtain ⟨hpref', hpp', hext', hnext', hpi', hisz', -⟩ := hL'
      have h0 := le_trans (prefix_ge0 _ _) hqi
      refine ⟨hpi', hisz', hpref', hq, fun _ => ⟨hI', hb1, hmp, fun l hl => (hpp' l hl).symm, hext',
        hfst, by omega, ⟨f', hh'⟩, by rw [hpath', hfst], ?_, hnext'⟩⟩
      rw [if_neg (by omega)] at hif' ⊢
      exact hif'
    -- the left's `x` is fresh: so is the right's
    · stmt_rcondf{2} 1
      -- EC: + progress. … lemma5' … by have:=H7;rewrite !domE=>/=->/=.
      · hoare_auto; auto_prep
        rcases lemma5' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹INV_CF_G1 _ _ _ _ _ _ _ _ _ _ _ _›
            ⟨le_trans (prefix_ge0 _ _) ‹_›, ‹_›⟩ ‹_› ⟨_, ‹_›⟩ with ⟨b', c', h', hP, -⟩ | ⟨-, hmh⟩
        · simp_all [FMap.domE]
        · simp [FMap.domE, hmh]
      -- EC: rcondt{2}1;1:auto=>/#.
      stmt_rcondt{2} 1; on_goals 1 => (hoare_auto; auto_prep; omega)
      -- EC: rcondt{2}5;auto;progress.
      stmt_rcondt{2} 5
      -- EC: * rewrite(@take_nth witness);1:smt(prefix_ge0);rewrite domE. … (~20 lines:
      --       `mh_of_INV`, `lemma5'`) — the old port's `PJ2_fresh` (deviation)
      · hoare_auto; auto_prep
        rename_i σ bcol bext hs ch gm gmi mh mhi ro paths bad1 cnt h y2 hy2 y1 hx w hb hisz hb1 hpp
          hpbs hy1 hpref hext hmp hI hqi hq hcnt hpath hdom hi hif f hh hsa hsc hnd
        rw [← hpbs] at hI
        have hJ : PJ2 hs ch _ _ gm gmi mh mhi ro paths _ _ _ _ _ w.1 w.2 h :=
          ⟨hI, hmp, ⟨f, hh⟩, hpath, by simpa using hif⟩
        have hL : PJ2L _ _ _ _ _ w.1 w.2 :=
          ⟨hpref, fun l hl => (hpp l hl).symm, hext, fun _ => hnd, hqi, hisz, hq⟩
        exact (PJ2_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hJ hL hi
          (by rwa [hx, hsa, hsc] at hdom)).2.1
      --     (EC's `auto` on the main goal: here only wp — EC's `rnd` cannot pair `y2` with `r`)
      stmt_wp
      -- EC: swap{2}-3;auto;progress.
      stmt_swap{2} -3
      equiv_auto
      --     (EC's closer, ~200 lines: `hs_addh`, `inv_addm`, `m_mh_addh_addm`, `mi_mhi_addh_addmi`,
      --     `build_hpath_up`, `build_hpath_upd_ch_iff`, `known_path_uniq`, … — the old port's
      --     `PJ2_fresh` (with `f_fresh_inv`) and `PJ2L_step`: deviation)
      auto_prep
      rename_i pref m mi pref0 i p q c bcol bext hs ch gm gmi mh mhi ro paths bad1 cnt h y1 hy1 y2 hy2
        w hb hpref hq hb1 hmp hpp hext hcnt hqi hisz hI hpath hi hif f hh hnd hdom
      have hJ : PJ2 hs ch m mi gm gmi mh mhi ro paths pref pref0 q p i w.1 w.2 h :=
        ⟨hI, hmp, ⟨f, hh⟩, hpath, by simpa using hif⟩
      have hL : PJ2L pref pref0 q p i w.1 w.2 :=
        ⟨hpref, fun l hl => (hpp l hl).symm, hext, fun _ => hnd, hqi, hisz, hq⟩
      obtain ⟨-, hro, hfr⟩ :=
        PJ2_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hJ hL hi (by simpa using hdom)
      have hL' := PJ2L_step _ _ _ _ _ _ _ y1 y2 hL hi (all_prefixes_of_m_p _ _ _ hmp)
      have h0 := le_trans (prefix_ge0 _ _) hqi
      simp only [FMap.get_set_sameE, oget_some] at hL' ⊢
      obtain ⟨hpref', hpp', hext', hnext', hpi', hisz', -⟩ := hL'
      refine ⟨hpi', hisz', trivial, hq, fun hb' => ?_⟩
      have hinv : hinv hs y2 = none := by
        simp only [not_or, Bool.or_eq_true, decide_eq_true_eq, ne_eq, not_not] at hb'
        exact hb'.1.2
      obtain ⟨hI', hmp', -, hpath', -⟩ := hfr y1 y2 hinv
      exact ⟨hI', hb1, hmp', fun l hl => (hpp' l hl).symm, hext', trivial,
        by omega, ⟨Unknown, rfl⟩, hpath', by rw [if_neg (by omega)]; trivial, hnext'⟩

section AUX

-- (`Real_G1` uses `ConcreteF`'s `Real_Concrete`, whose `D` stays outside the section's local
-- `clone Strong_RP_RF as Switching`: in EC a local clone is fresh, here its modules are named)
declare module D <: DISTINGUISHER {-PF, -F.RO, -ROhandle.RO, -G1, -Redo, -C, -Perm,
  -Pilot.ConcreteF.Switching.DBounder, -Pilot.ConcreteF.Switching.ARP,
  -Pilot.ConcreteF.Switching.PRPi.PRPi} with glob R

-- EC's `declare axiom D_ll` (`glob D` as the region `R`, exception E14)
variable (D_ll : ∀ (F <: DFUNCTIONALITY {-R}), ∀ (P <: DPRIMITIVE {-R}),
  islossless P.f → islossless P.fi → islossless F.f → islossless D(F, P).distinguish)

set_option maxHeartbeats 8000000 in
-- one declaration: EC's call over three oracles, with their twelve goals; each `conseq` with a
-- pilot oracle lemma (EC's paths) matches the old declarations' views at ~2M (gap list)
include D_ll in
/-- EC's `equiv CF_G1 : CF(DRestr(D)).main ~ G1(DRestr(D)).main : ={glob D} ==>
!(G1.bcol \/ G1.bext){2} => ={res}`, its proof EC's (see the module docstring). -/
theorem CF_G1 : equiv[ CF(DRestr(D)).main ~ G1(DRestr(D)).main :
    ={glob D} ==> ¬(§G1.bcol{2} ∨ §G1.bext{2}) → ={res} ] := by
  equiv_proc; stmt_inline*; stmt_wp
  equiv_call (_ : §G1.bcol ∨ §G1.bext,
    ={glob C} ∧
      INV_CF_G1 §FRO.m{2} §G1.chandle{2} §PF.m{1} §PF.mi{1} §G1.m{2} §G1.mi{2} §G1.mh{2}
        §G1.mhi{2} §F.RO.m{2} §G1.paths{2} §Redo.prefixes{1} §C.queries{2},
    FMap.dom §C.queries{2} [])
  · exact D_ll
  -- proofs for G1.S.f
  -- equivalence up to bad of PF.f and G1.S.f
  -- EC: + conseq (_: !G1.bcol{2} /\ !G1.bext{2} /\ ={x, glob C} /\ INV_CF_G1 … ==>
  --         !G1.bcol{2} => !G1.bext{2} => ={res, glob C} /\ INV_CF_G1 …).
  --       + by move=> &1 &2; rewrite negb_or.
  --       + progress;have[]:=m_p_of_INV _ _ _ _ _ _ _ _ _ _ _ _ H0;smt(domE).
  --       conseq(eq_f D);progress=>/#.
  --     (our up-to-bad call asks one judgment `if bad then … else …` per oracle, which is
  --     `eq_f`'s own: EC's intermediate `conseq` is not needed)
  · equiv_conseq eq_f
    · auto_close
    · auto_close
  -- lossless PF.f
  -- (EC's `smt (@Block.DBlock @Capacity.DCapacity)`, the distributions are lossless: `ec_auto`)
  · phoare_proc; phoare_inline*; ec_auto
  -- lossless and do not reset bad G1.S.f
  · phoare_proc; phoare_inline*; ec_auto
    ec_intro
    rintro ⟨hb | hb, hq⟩ <;> simp [hb, hq, F.dout]
  -- lossless G1.S.f (the deviation: EC needs it only after the bad event, above)
  · phoare_proc; phoare_inline*; ec_auto
  -- proofs for G1.S.fi
  -- equiv PF.P.fi G1.S.fi
  -- EC: + conseq(eq_fi D)=>/#.
  · equiv_conseq eq_fi
    · auto_close
    · auto_close
  -- lossless PF.P.fi
  · phoare_proc; phoare_inline*; ec_auto
  -- lossless and do not reset bad G1.S.fi
  · phoare_proc; phoare_inline*; ec_auto
    ec_intro
    rintro ⟨hb | hb, hq⟩ <;> simp [hb, hq]
  -- lossless G1.S.fi
  · phoare_proc; phoare_inline*; ec_auto
  -- proofs for G1.C.f
  -- equiv PF.C.f G1.C.f
  -- EC: + conseq(PFf_Cf D);auto=>/#.
  · equiv_conseq PFf_Cf
    · auto_close
    · auto_close
  -- lossless PF.C.f
  · phoare_proc; phoare_inline*; stmt_sp; stmt_if
    · stmt_if
      · stmt_wp
        phoare_while True ((size §p - §i).toNat)
        · intro k; phoare_auto
          rintro i p - - - - ⟨-, hc, hk⟩
          have h : (size p - (i + 1)).toNat < k := by simp only [decide_eq_true_eq] at hc; omega
          simp [h]
        · phoare_auto
      · phoare_auto
    · phoare_auto
  -- lossless and do not reset bad G1.C.f
  · phoare_proc; phoare_inline*; stmt_sp; stmt_if
    · stmt_if
      · phoare_auto
        phoare_while ((§G1.bcol ∨ §G1.bext) ∧ FMap.dom §C.queries []) ((size §p - §i).toNat)
        · intro k; phoare_auto
          rintro bcol bext queries i p - - - - - - ⟨⟨hb, hq⟩, hc, hk⟩
          have h : (size p - (i + 1)).toNat < k := by simp only [decide_eq_true_eq] at hc; omega
          rcases hb with hb | hb <;> simp [hb, hq, h, indicatorE_of, F.dout]
        · phoare_auto
          intros; simp_all [indicatorE]
        · intros; simp_all [FMap.mem_set]
      · phoare_auto; intros; simp_all [indicatorE]
    · phoare_auto
      intros; simp_all [indicatorE]
  -- lossless G1.C.f
  · phoare_proc; phoare_inline*; stmt_sp; stmt_if
    · stmt_if
      · phoare_auto
        phoare_while True ((size §p - §i).toNat)
        · intro k; phoare_auto
          intros; rename_i hc
          obtain ⟨-, hc, rfl⟩ := hc
          simp only [decide_eq_true_eq] at hc
          split_ifs <;> simp [F.dout, indicatorE, hc]
        · phoare_auto
      · phoare_auto
    · phoare_auto
  -- Init ok
  · stmt_wp; equiv_skip
    intro g₁ g₂ hD
    glob_simp
    refine ⟨⟨hD, INV_CF_G1_init⟩, fun r₁ g₁ r₂ g₂ h hnb => ?_⟩
    rcases h with ⟨hb, -⟩ | ⟨hr, -⟩
    · exact absurd hb hnb
    · exact hr

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
include D_ll in
/-- EC's `lemma Real_G1 &m : Pr[GReal(D).main() @ &m: res /\ C.c <= max_size] <=
Pr[G1(DRestr(D)).main() @ &m: res] + (max_size ^ 2 - max_size)%r * inv 2%r * mu dstate
(pred1 witness) + Pr[G1(DRestr(D)).main() @&m: G1.bcol] + Pr[G1(DRestr(D)).main() @&m:
G1.bext]`. -/
theorem Real_G1 (m : VariableAssignment) :
    Pr[ (Pilot.SLCommon.GReal D) () @ &m : §res ∧ §C.c ≤ max_size ] ≤
      Pr[ G1(DRestr(D)).main () @ &m : §res ] +
        ((max_size ^ 2 - max_size : ℤ) : ℝ) * (2 : ℝ)⁻¹ * (dstate.1 {default}).toReal +
        Pr[ G1(DRestr(D)).main () @ &m : §G1.bcol ] +
        Pr[ G1(DRestr(D)).main () @ &m : §G1.bext ] := by
  -- EC: apply (@RealOrder.ler_trans _ _ _ (Real_Concrete D _ &m))=>//=.
  --     + exact: D_ll.
  refine le_trans (Pilot.ConcreteF.Real_Concrete D D_ll m) ?_
  -- EC: have : Pr[CF(DRestr(D)).main() @ &m : res] <=
  --           Pr[G1(DRestr(D)).main() @ &m : res] +
  --           Pr[G1(DRestr(D)).main() @ &m : G1.bcol \/ G1.bext].
  --     + by byequiv (CF_G1 D D_ll)=>//=/#.
  have h : Pr[ CF(DRestr(D)).main () @ &m : §res ] ≤ Pr[ G1(DRestr(D)).main () @ &m : §res ] +
      Pr[ G1(DRestr(D)).main () @ &m : §G1.bcol ∨ §G1.bext ] := by
    byequiv (CF_G1 D D_ll)
    --     (EC's `/#`: the result is `true` unless the bad event happened)
    auto_prep
    exact or_iff_not_imp_right.mpr fun hb => Eq.symm (‹¬_ → true = _› hb)
  -- EC: have/#:Pr[G1(DRestr(D)).main() @ &m : G1.bcol \/ G1.bext]
  --             <= Pr[G1(DRestr(D)).main() @&m: G1.bcol]
  --             + Pr[G1(DRestr(D)).main() @&m: G1.bext].
  --     by rewrite Pr[mu_or];smt(Distr.mu_bounded).
  have h' : Pr[ G1(DRestr(D)).main () @ &m : §G1.bcol ∨ §G1.bext ] ≤
      Pr[ G1(DRestr(D)).main () @ &m : §G1.bcol ] + Pr[ G1(DRestr(D)).main () @ &m : §G1.bext ] := by
    exact_mod_cast Procedure.Pr_or_le _ _ _ _ _
  linarith

end AUX

end GaudisCrypt.SHA3.Pilot.Handle
