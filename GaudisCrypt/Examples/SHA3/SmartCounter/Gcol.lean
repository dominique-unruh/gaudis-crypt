import GaudisCrypt.Examples.SHA3.SmartCounter.Handle

/-!
# The collision event of `G1` (EasyCrypt `proof/smart_counter/Gcol.eca`)

`Pr_G1col` bounds the probability of `G1.bcol` by `max_size · (2 max_size / 2^c)`, through the
game `Gcol` that counts the capacity samples (the `fel` argument of `Pr_col`).

Translation notes (see `notes/SHA3/README.md`):
* `clone export Handle as Handle0` clones a theory without parameters: it is `Handle`, opened.
* The local module `Gcol` calls `sample_c` from its inner modules `M`, `S`: these are the modules
  `Gcol.sample_c`, `Gcol.M`, `Gcol.S`, and `Gcol D` the game (with `D` a Lean parameter).
* The local module `Gcol`'s variable `count` is the lens parameter `Gcol_count` of the local
  declarations (`Gcol.sample_c`, `Gcol.M`, `Gcol.S`, `Gcol`, `Pr_col`, `G1_col`), fresh by
  hypothesis; `Pr_G1col` does not mention it (exception E6).
* EasyCrypt's `2^c` (an `int` power, `c > 0`) is `2 ^ c.toNat`; `card` (an `int`) is the
  cardinality cast to `ℤ`.
-/

-- EasyCrypt names the local module after the file (`Gcol.Gcol`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.Gcol

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.ConcreteF
open GaudisCrypt.SHA3.Handle

export GaudisCrypt.SHA3.SLCommon (state PRIMITIVE)

variable [SLCommon.Params]

theorem c_gt0r : (0 : ℝ) < ((2 ^ c.toNat : ℤ) : ℝ) := by
  sorry

theorem c_ge0r : (0 : ℝ) ≤ ((2 ^ c.toNat : ℤ) : ℝ) := by
  sorry

theorem eps_ge0 : (0 : ℝ) ≤ ((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ) := by
  sorry

/-! ## The section `PROOF` -/

/-! The local module `Gcol`'s variable `Gcol.count` is the lens parameter `Gcol_count` of the local
declarations that mention it, fresh by hypothesis (exception E6). -/
variable (Gcol_count : Lens ℤ VariableAssignment)

module Gcol.sample_c {
  proc sample_c () : capacity {
    var c : capacity;
    c <- c0;
    if (decide (((Finset.image Prod.fst
          (FMap.frng ($FRO.m : FMap handle (capacity × flag)))).card : ℤ) ≤ 2 * max_size ∧
        $Gcol_count < max_size)) {
      c <$ cdistr;
      G1.bcol <- $G1.bcol || decide ($c ∈ Finset.image Prod.fst
        (FMap.frng ($FRO.m : FMap handle (capacity × flag))));
      Gcol_count <- $Gcol_count + 1;
    }
    return $c
  };
}

-- EC's `Gcol.M`
module Gcol.M : DFUNCTIONALITY {
  proc f (p : List block) : block {
    var sa : block, sa' : block, sc : capacity, h : handle, i : ℤ, counter : ℤ;
    h <- 0;
    i <- 0;
    counter <- 0;
    sa <- b0;
    while ($i < size $p) {
      if (decide (FMap.dom ($G1.mh : hsmap) ($sa +^ nth default $p $i, $h))) {
        sa, h <- oget (FMap.get ($G1.mh : hsmap) ($sa +^ nth default $p $i, $h));
      } else {
        if (decide ($counter < size $p - «prefix» $p (get_max_prefix $p
            (elems (FMap.fdom ($C.queries : FMap (List block) block)))))) {
          sc <- call (Gcol.sample_c Gcol_count) ();
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

-- EC's `Gcol.S`
module Gcol.S : DPRIMITIVE {
  proc f (x : state) : state {
    var p : List block, v : block, y : state, y1 : block, y2 : capacity, hy2 : handle,
      hx2 : handle;
    if (!(decide (FMap.dom ($G1.m : smap) $x))) {
      y <- (b0, c0);
      if (!(decide (FMap.rng ($FRO.m : FMap handle (capacity × flag)) (($x).2, Known)))) {
        FRO.m <- FMap.set $FRO.m $G1.chandle (($x).2, Known);
        G1.chandle <- $G1.chandle + 1;
      }
      hx2 <- oget (hinvK $FRO.m ($x).2);
      if (decide (FMap.dom ($G1.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($G1.paths : FMap capacity (List block × block)) ($x).2);
        y1 <- call (PROM.FullRO.ROmap.get (List block) block F.RO) (rcons $p ($v +^ ($x).1));
        y2 <- call (Gcol.sample_c Gcol_count) ();
      } else {
        y1 <$ bdistr;
        y2 <- call (Gcol.sample_c Gcol_count) ();
      }
      y <- ($y1, $y2);
      if (decide (FMap.dom ($G1.mh : hsmap) (($x).1, $hx2) ∧
          FMap.in_dom_with ($FRO.m : FMap handle (capacity × flag))
            (oget (FMap.get ($G1.mh : hsmap) (($x).1, $hx2))).2 Unknown)) {
        hy2 <- (oget (FMap.get ($G1.mh : hsmap) (($x).1, $hx2))).2;
        y <- (($y).1, (oget (FMap.get ($FRO.m : FMap handle (capacity × flag)) $hy2)).1);
        FRO.m <- FMap.set $FRO.m $hy2 (($y).2, Known);
        G1.m <- FMap.set $G1.m $x $y;
        G1.mi <- FMap.set $G1.mi $y $x;
      } else {
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
      y <- (b0, c0);
      if (!(decide (FMap.rng ($FRO.m : FMap handle (capacity × flag)) (($x).2, Known)))) {
        FRO.m <- FMap.set $FRO.m $G1.chandle (($x).2, Known);
        G1.chandle <- $G1.chandle + 1;
      }
      hx2 <- oget (hinvK $FRO.m ($x).2);
      y1 <$ bdistr;
      y2 <- call (Gcol.sample_c Gcol_count) ();
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

-- EC's local module `Gcol`'s `main`, with `D` a Lean parameter (on purpose: `Gcol D` is the game)
set_option linter.gaudisCrypt.using false in
module Gcol (D : DISTINGUISHER) {
  proc main () : Bool {
    var b : Bool;
    F.RO.m <- (FMap.empty : FMap (List block) block);
    G1.m <- (FMap.empty : smap);
    G1.mi <- (FMap.empty : smap);
    G1.mh <- (FMap.empty : hsmap);
    G1.mhi <- (FMap.empty : hsmap);
    G1.bcol <- false;
    FRO.m <- FMap.set (FMap.empty : FMap handle (capacity × flag)) 0 (c0, Known);
    G1.paths <- FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0);
    G1.chandle <- 1;
    Gcol_count <- 0;
    b <- call (Module.app (DRestr D) (Module.pair (Gcol.M Gcol_count) (Gcol.S Gcol_count))) ();
    return $b
  };
}

theorem card_rng_set {α β : Type} [DecidableEq α] [DecidableEq β] (m : FMap α β) (x : α) (y : β) :
    ((FMap.frng (FMap.set m x y)).card : ℤ) ≤ (FMap.frng m).card + 1 := by
  sorry

theorem hinv_image (handles : handles) (c : capacity) :
    hinv handles c ≠ none → c ∈ Finset.image Prod.fst (FMap.frng handles) := by
  sorry

section PROOF

variable (D : DISTINGUISHER)

/-- `local lemma Pr_col`, for `declare module D <: DISTINGUISHER {-C, -PF, -G1}` with `D_ll`. -/
theorem Pr_col (hD : Module.Representable D distExt)
    (_hfresh : Gcol_count.footprint ≤ (FVP.fvP D ⊔ C.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint ⊔ (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔
      (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint)ᶜ)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D)ᶜ →
      FVP.fvP P ≤ (FVP.fvP D)ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (m : VariableAssignment) :
    (Procedure.Pr (Gcol Gcol_count D).procedure () m
        (fun _ g => G1.bcol.get g = true ∧ Gcol_count.get g ≤ max_size) : ℝ) ≤
      (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) := by
  sorry

/-- `local equiv G1_col : G1(DRestr(D)).main ~ Gcol.main : ={glob D} ==>
(G1.bcol{1} => G1.bcol{2}) /\ Gcol.count{2} <= max_size`. -/
theorem G1_col (hD : Module.Representable D distExt)
    (_hfresh : Gcol_count.footprint ≤ (FVP.fvP D ⊔ C.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint ⊔ (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔
      (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint)ᶜ)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D)ᶜ →
      FVP.fvP P ≤ (FVP.fvP D)ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless) :
    prhlProc
      (fun _ g₁ _ g₂ => (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (G1 (DRestr D)).procedure (Gcol Gcol_count D).procedure
      (fun _ g₁ _ g₂ => (G1.bcol.get g₁ = true → G1.bcol.get g₂ = true) ∧
        Gcol_count.get g₂ ≤ max_size) := by
  sorry

/-- EC's `Pr_G1col`. -/
theorem Pr_G1col (hD : Module.Representable D distExt)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D)ᶜ →
      FVP.fvP P ≤ (FVP.fvP D)ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (m : VariableAssignment) :
    (Procedure.Pr (G1 (DRestr D)).procedure () m (fun _ g => G1.bcol.get g = true) : ℝ) ≤
      (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) := by
  sorry

end PROOF

end GaudisCrypt.SHA3.Gcol
