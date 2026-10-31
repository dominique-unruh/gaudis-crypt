import GaudisCrypt.Examples.SHA3.SmartCounter.Gcol

/-!
# The extension event (EasyCrypt `proof/smart_counter/Gext.eca`)

`G2` is `G1` with the handles in a programmable random oracle `HS`.  `Real_G2` bounds the real game
by the eager `G2` plus the switching bound and the probabilities of collisions and extensions
(`Pr_ext`, through the resampling game `Gext`).

Translation notes (see `notes/SHA3/README.md`):
* `clone export Gcol as Gcol0` clones a theory without parameters: it is `Gcol`, opened.
* `G2(D, HS)`: its inner modules `M`, `S` depend on `HS` only: they are the functors `G2.M`, `G2.S`
  of `HS`.  `G2 D` is the `FRO` distinguisher, with `D` a Lean parameter.
* `clone include EagerCore` is the `ROhandle` instance of `PROM.FullRO.FullEager`: `Eager`, `RRO`.
* The local module `ReSample`'s variable `count` is the lens parameter `ReSample_count` of the
  local declarations that mention it, fresh by hypothesis (exception E6).
* The local modules `ReSample`, `Gext` are modules; `Gext.resample` is its own module, and
  `Gext D` the game (with `D` a Lean parameter).
-/

-- EasyCrypt names the local module after the file (`Gext.Gext`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.Gext

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.ConcreteF
open GaudisCrypt.SHA3.Handle GaudisCrypt.SHA3.Gcol

export GaudisCrypt.SHA3.SLCommon (state PRIMITIVE)

variable [SLCommon.Params]

def bad_ext (m mi : smap) (y : capacity) : Prop :=
  y ∈ Finset.image Prod.snd (FMap.fdom m) ∨ y ∈ Finset.image Prod.snd (FMap.fdom mi)

instance (m mi : smap) (y : capacity) : Decidable (bad_ext m mi y) :=
  inferInstanceAs (Decidable (_ ∨ _))

noncomputable def hinvc (m : FMap handle capacity) (c : capacity) : Option handle :=
  FMap.find (fun _ y => decide (y = c)) m

/-- The handle oracle's type: `FRO` at `handle`, `capacity`. -/
abbrev HFRO := PROM.FullRO.FRO_T handle capacity

/-! ## The game `G2` -/

-- EC's `G2(D, HS).M`
module G2.M using (HS : HFRO) : DFUNCTIONALITY {
  proc f (p : List block) : block {
    var sa : block, sa' : block, h : handle, i : ℤ, counter : ℤ;
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
          _ <- call HS.sample ($G1.chandle);
          sa' <- call (PROM.FullRO.ROmap.get (List block) block F.RO) (take ($i + 1) $p);
          sa <- $sa +^ nth default $p $i;
          G1.mh <- FMap.set $G1.mh ($sa, $h) ($sa', $G1.chandle);
          G1.mhi <- FMap.set $G1.mhi ($sa', $G1.chandle) ($sa, $h);
          sa, h <- ($sa', $G1.chandle);
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

-- EC's `G2(D, HS).S`
module G2.S using (HS : HFRO) : DPRIMITIVE {
  proc f (x : state) : state {
    var p : List block, v : block, y : state, y1 : block, y2 : capacity, hy2 : handle,
      hx2 : handle, handles_ : FMap handle capacity, t : Bool;
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
      handles_ <- call HS.allKnown ();
      if (!(decide (FMap.rng $handles_ ($x).2))) {
        _ <- call HS.set ($G1.chandle, ($x).2);
        G1.chandle <- $G1.chandle + 1;
      }
      handles_ <- call HS.allKnown ();
      hx2 <- oget (hinvc $handles_ ($x).2);
      t <- call HS.queried ((oget (FMap.get ($G1.mh : hsmap) (($x).1, $hx2))).2, Unknown);
      if (decide (FMap.dom ($G1.mh : hsmap) (($x).1, $hx2)) && $t) {
        hy2 <- (oget (FMap.get ($G1.mh : hsmap) (($x).1, $hx2))).2;
        y2 <- call HS.get ($hy2);
        G1.bext <- $G1.bext || decide (bad_ext $G1.m $G1.mi $y2) || decide ($y2 = ($x).2);
        y <- (($y).1, $y2);
        G1.m <- FMap.set $G1.m $x $y;
        G1.mi <- FMap.set $G1.mi $y $x;
      } else {
        hy2 <- $G1.chandle;
        G1.chandle <- $G1.chandle + 1;
        _ <- call HS.set ($hy2, ($y).2);
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
      handles_ <- call HS.allKnown ();
      if (!(decide (FMap.rng $handles_ ($x).2))) {
        _ <- call HS.set ($G1.chandle, ($x).2);
        G1.chandle <- $G1.chandle + 1;
      }
      handles_ <- call HS.allKnown ();
      hx2 <- oget (hinvc $handles_ ($x).2);
      y1 <$ bdistr;
      y2 <$ cdistr;
      y <- ($y1, $y2);
      t <- call HS.queried ((oget (FMap.get ($G1.mhi : hsmap) (($x).1, $hx2))).2, Unknown);
      if (decide (FMap.dom ($G1.mhi : hsmap) (($x).1, $hx2)) && $t) {
        y1, hy2 <- oget (FMap.get ($G1.mhi : hsmap) (($x).1, $hx2));
        y2 <- call HS.get ($hy2);
        y <- (($y).1, $y2);
        G1.bext <- $G1.bext || decide (bad_ext $G1.m $G1.mi $y2) || decide ($y2 = ($x).2);
        G1.mi <- FMap.set $G1.mi $x $y;
        G1.m <- FMap.set $G1.m $y $x;
      } else {
        hy2 <- $G1.chandle;
        G1.chandle <- $G1.chandle + 1;
        _ <- call HS.set ($hy2, ($y).2);
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

-- EC's `G2(D, HS).distinguish`, with `D` a Lean parameter (on purpose: `G2 D` is an `FRO`
-- distinguisher); its argument is EasyCrypt's `d_in_t = unit`
set_option linter.gaudisCrypt.using false in
module G2 (D : DISTINGUISHER) using (HS : HFRO) {
  proc distinguish (_u : Unit) : Bool {
    var b : Bool;
    F.RO.m <- (FMap.empty : FMap (List block) block);
    G1.m <- (FMap.empty : smap);
    G1.mi <- (FMap.empty : smap);
    G1.mh <- (FMap.empty : hsmap);
    G1.mhi <- (FMap.empty : hsmap);
    G1.bext <- false;
    C.queries <- FMap.set (FMap.empty : FMap (List block) block) [] b0;
    -- the empty path is initially known by the adversary to lead to capacity 0^c
    _ <- call HS.set (0, c0);
    G1.paths <- FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0);
    G1.chandle <- 1;
    b <- call (Module.app D (Module.pair (Module.app G2.M HS) (Module.app G2.S HS))) ();
    return $b
  };
}

-- `clone include EagerCore` (of `ROhandle`'s `FullEager`)
noncomputable abbrev Eager :=
  PROM.FullRO.FullEager.Eager handle capacity Unit Bool ROhandle.dout ROhandle.FRO.m
noncomputable abbrev Eager.main1 :=
  PROM.FullRO.FullEager.Eager.main1 handle capacity Unit Bool ROhandle.dout ROhandle.FRO.m
noncomputable abbrev Eager.main2 :=
  PROM.FullRO.FullEager.Eager.main2 handle capacity Unit Bool ROhandle.dout ROhandle.FRO.m
noncomputable abbrev RRO := PROM.FullRO.FullEager.RRO handle capacity ROhandle.dout ROhandle.FRO.m
noncomputable abbrev RRO.resample := PROM.FullRO.FullEager.RRO.own.resample handle capacity
  ROhandle.dout ROhandle.FRO.m

/-! ## The first section: `G1` and the lazy `G2` -/

def inv_ext (m mi : smap) (FROm : handles) : Prop :=
  ∃ x h, x ∈ FMap.fdom m ∪ FMap.fdom mi ∧ FMap.get FROm h = some (x.2, Unknown)

def inv_ext1 (bext1 bext2 : Bool) (m mi : smap) (FROm : handles) : Prop :=
  bext1 = true → bext2 = true ∨ inv_ext m mi FROm

theorem rng_restr {«from» «to» φ : Type} [DecidableEq «from»] [DecidableEq φ]
    (m : FMap «from» («to» × φ)) (f : φ) (x : «to») :
    FMap.rng (FMap.restr f m) x ↔ FMap.rng m (x, f) := by
  sorry

section

variable (D : DISTINGUISHER)

/-- `equiv G1_G2 : G1(DRestr(D)).main ~ Eager(G2(DRestr(D))).main1 : ={glob D} ==>
={res} /\ inv_ext1 G1.bext{1} G1.bext{2} G1.m{2} G1.mi{2} FRO.m{2}`, for
`declare module D <: DISTINGUISHER {-G1, -G2, -FRO, -C}`. -/
theorem G1_G2 (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ ((G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔
      (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint ⊔ (FRO.m).footprint ⊔ C.footprint)ᶜ) :
    prhlProc
      (fun _ g₁ _ g₂ => (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (G1 (DRestr D)).procedure (Eager.main1 (G2 (DRestr D))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        inv_ext1 (G1.bext.get g₁) (G1.bext.get g₂) (G1.m.get g₂) (G1.mi.get g₂)
          (FRO.m.get g₂)) := by
  sorry

end

/-! ## The section `EXT` -/

/-! The local module `ReSample`'s variable `ReSample.count` is the lens parameter `ReSample_count`
of the local declarations that mention it, fresh by hypothesis (exception E6). -/
variable (ReSample_count : Lens ℤ VariableAssignment)

module ReSample {
  proc f (h : handle) : Unit {
    var c : capacity;
    c <$ cdistr;
    if (decide (((FMap.fdom ($G1.m : smap)).card : ℤ) ≤ max_size ∧
        ((FMap.fdom ($G1.mi : smap)).card : ℤ) ≤ max_size ∧ $ReSample_count < max_size)) {
      G1.bext <- $G1.bext || decide ($c ∈ Finset.image Prod.snd
        (FMap.fdom ($G1.m : smap) ∪ FMap.fdom ($G1.mi : smap)));
      FRO.m <- FMap.set $FRO.m $h ($c, Unknown);
      ReSample_count <- $ReSample_count + 1;
    }
    return ()
  };
  proc f1 (x : capacity, h : handle) : Unit {
    var c : capacity;
    c <$ cdistr;
    if (decide (((FMap.fdom ($G1.m : smap)).card : ℤ) < max_size ∧
        ((FMap.fdom ($G1.mi : smap)).card : ℤ) < max_size ∧ $ReSample_count < max_size)) {
      G1.bext <- $G1.bext || decide ($c ∈ Finset.image Prod.snd
        (FMap.fdom ($G1.m : smap) ∪ FMap.fdom ($G1.mi : smap)) ∪ fset1 $x);
      FRO.m <- FMap.set $FRO.m $h ($c, Unknown);
      ReSample_count <- $ReSample_count + 1;
    }
    return ()
  };
}

-- EC's `Gext.resample`
module Gext.resample {
  proc resample () : Unit {
    _ <- call (Module.app (IterProc.Iter handle)
        (IterProc.Orcl.mk handle { f := ReSample.f ReSample_count }))
      ((FMap.fdom (FMap.restr Unknown ($FRO.m : FMap handle (capacity × flag)))).toList);
    return ()
  };
}

-- EC's `Gext.M`
module Gext.M : DFUNCTIONALITY {
  proc f (p : List block) : block {
    var sa : block, sa' : block, h : handle, i : ℤ, counter : ℤ;
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
          _ <- call (PROM.FullRO.FRO_T.sample handle capacity RRO) ($G1.chandle);
          sa' <- call (PROM.FullRO.ROmap.get (List block) block F.RO) (take ($i + 1) $p);
          sa <- $sa +^ nth default $p $i;
          G1.mh <- FMap.set $G1.mh ($sa, $h) ($sa', $G1.chandle);
          G1.mhi <- FMap.set $G1.mhi ($sa', $G1.chandle) ($sa, $h);
          sa, h <- ($sa', $G1.chandle);
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

-- EC's `Gext.S`
module Gext.S : DPRIMITIVE {
  proc f (x : state) : state {
    var p : List block, v : block, y : state, y1 : block, y2 : capacity, hy2 : handle,
      hx2 : handle, handles_ : FMap handle capacity, t : Bool;
    if (!(decide (FMap.dom ($G1.m : smap) $x))) {
      if (decide (FMap.dom ($G1.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($G1.paths : FMap capacity (List block × block)) ($x).2);
        y1 <- call (PROM.FullRO.ROmap.get (List block) block F.RO) (rcons $p ($v +^ ($x).1));
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
        _ <- call (ReSample.f1 ReSample_count) (($x).2, $hy2);
        y2 <- call (PROM.FullRO.FRO_T.get handle capacity ROhandle.FRO) ($hy2);
        y <- (($y).1, $y2);
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
      y1 <$ bdistr;
      y2 <$ cdistr;
      y <- ($y1, $y2);
      t <- call (PROM.FullRO.FRO_T.queried handle capacity RRO)
        ((oget (FMap.get ($G1.mhi : hsmap) (($x).1, $hx2))).2, Unknown);
      if (decide (FMap.dom ($G1.mhi : hsmap) (($x).1, $hx2)) && $t) {
        y1, hy2 <- oget (FMap.get ($G1.mhi : hsmap) (($x).1, $hx2));
        _ <- call (ReSample.f1 ReSample_count) (($x).2, $hy2);
        y2 <- call (PROM.FullRO.FRO_T.get handle capacity ROhandle.FRO) ($hy2);
        y <- (($y).1, $y2);
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

-- EC's `Gext.distinguish`, with `D` a Lean parameter (on purpose: `Gext D` is the game)
set_option linter.gaudisCrypt.using false in
module Gext (D : DISTINGUISHER) {
  proc distinguish () : Bool {
    var b : Bool;
    C.c <- 0;
    F.RO.m <- (FMap.empty : FMap (List block) block);
    G1.m <- (FMap.empty : smap);
    G1.mi <- (FMap.empty : smap);
    G1.mh <- (FMap.empty : hsmap);
    G1.mhi <- (FMap.empty : hsmap);
    G1.bext <- false;
    ReSample_count <- 0;
    FRO.m <- (FMap.empty : FMap handle (capacity × flag));
    -- the empty path is initially known by the adversary to lead to capacity 0^c
    _ <- call (PROM.FullRO.FRO_T.set handle capacity RRO) (0, c0);
    G1.paths <- FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0);
    G1.chandle <- 1;
    b <- call (Module.app (DRestr D) (Module.pair Gext.M (Gext.S ReSample_count))) ();
    _ <- call (Gext.resample ReSample_count) ();
    return $b
  };
}

def inv_lt (m2 mi2 : smap) (c1 : ℤ) (Fm2 : handles) (count2 : ℤ) : Prop :=
  ((FMap.fdom m2).card : ℤ) < c1 ∧ ((FMap.fdom mi2).card : ℤ) < c1 ∧
    count2 + (FMap.fdom (FMap.restr Unknown Fm2)).card < c1 ∧ c1 ≤ max_size

def inv_le (m2 mi2 : smap) (c1 : ℤ) (Fm2 : handles) (count2 : ℤ) : Prop :=
  ((FMap.fdom m2).card : ℤ) ≤ c1 ∧ ((FMap.fdom mi2).card : ℤ) ≤ c1 ∧
    count2 + (FMap.fdom (FMap.restr Unknown Fm2)).card ≤ c1 ∧ c1 ≤ max_size

theorem fset0_eqP {α : Type} (s : FSet α) : s = fset0 ↔ ∀ x, x ∉ s := by
  sorry

theorem size_set {α β : Type} [DecidableEq α] (m : FMap α β) (x : α) (y : β) :
    ((FMap.fdom (FMap.set m x y)).card : ℤ) =
      if FMap.dom m x then (FMap.fdom m).card else (FMap.fdom m).card + 1 := by
  sorry

theorem size_set_le {α β : Type} [DecidableEq α] (m : FMap α β) (x : α) (y : β) :
    ((FMap.fdom (FMap.set m x y)).card : ℤ) ≤ (FMap.fdom m).card + 1 := by
  sorry

theorem size_rem {α β : Type} [DecidableEq α] (m : FMap α β) (x : α) :
    ((FMap.fdom (FMap.rem m x)).card : ℤ) =
      if FMap.dom m x then (FMap.fdom m).card - 1 else (FMap.fdom m).card := by
  sorry

theorem size_rem_le {α β : Type} [DecidableEq α] (m : FMap α β) (x : α) :
    ((FMap.fdom (FMap.rem m x)).card : ℤ) ≤ (FMap.fdom m).card := by
  sorry

theorem size_ge0 {α β : Type} (m : FMap α β) : 0 ≤ ((FMap.fdom m).card : ℤ) := by
  sorry

theorem size0 {α β : Type} [DecidableEq α] :
    ((FMap.fdom (FMap.empty : FMap α β)).card : ℤ) = 0 := by
  sorry

section EXT

variable (D : DISTINGUISHER)

/-- `local equiv RROset_inv_lt : RRO.set ~ RRO.set : ={x, y, FRO.m} /\ inv_lt G1.m{2} G1.mi{2}
C.c{1} FRO.m{2} ReSample.count{2} ==> ={res, FRO.m} /\ inv_lt …`. -/
theorem RROset_inv_lt :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ FRO.m.get g₁ = FRO.m.get g₂ ∧
        inv_lt (G1.m.get g₂) (G1.mi.get g₂) (C.c.get g₁) (FRO.m.get g₂) (ReSample_count.get g₂))
      (PROM.FullRO.FRO_T.set handle capacity RRO).procedure
      (PROM.FullRO.FRO_T.set handle capacity RRO).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ FRO.m.get g₁ = FRO.m.get g₂ ∧
        inv_lt (G1.m.get g₂) (G1.mi.get g₂) (C.c.get g₁) (FRO.m.get g₂)
          (ReSample_count.get g₂)) := by
  sorry

/-- `local lemma Pr_ext`, for `declare module D <: DISTINGUISHER {-C, -PF, -G1, -G2, -Perm, -RO,
-Redo}` with `D_ll`. -/
theorem Pr_ext (hD : Module.ECModule D distExt)
    (_hfresh : ReSample_count.footprint ≤ (FVP.fvP D ⊔ C.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint ⊔ (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔
      (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint)ᶜ)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (F.RO.m).footprint ⊔ (Redo.prefixes).footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D)ᶜ →
      FVP.fvP P ≤ (FVP.fvP D)ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (m : VariableAssignment) :
    (Procedure.Pr (Gext ReSample_count D).procedure () m
        (fun _ g => G1.bext.get g = true ∧ ReSample_count.get g ≤ max_size) : ℝ) ≤
      (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) := by
  sorry

/-- `local equiv EG2_Gext : Eager(G2(DRestr(D))).main2 ~ Gext.distinguish : ={glob D} ==>
ReSample.count{2} <= max_size /\ ((G1.bext{1} \/ inv_ext G1.m{1} G1.mi{1} FRO.m{1}) =>
G1.bext{2})`. -/
theorem EG2_Gext (hD : Module.ECModule D distExt)
    (_hfresh : ReSample_count.footprint ≤ (FVP.fvP D ⊔ C.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint ⊔ (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔
      (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint)ᶜ)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (F.RO.m).footprint ⊔ (Redo.prefixes).footprint)ᶜ) :
    prhlProc
      (fun _ g₁ _ g₂ => (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (Eager.main2 (G2 (DRestr D))).procedure (Gext ReSample_count D).procedure
      (fun _ g₁ _ g₂ => ReSample_count.get g₂ ≤ max_size ∧
        (G1.bext.get g₁ = true ∨ inv_ext (G1.m.get g₁) (G1.mi.get g₁) (FRO.m.get g₁) →
          G1.bext.get g₂ = true)) := by
  sorry

/-- EC's `Real_G2`, with the axiom `D_ll`. -/
theorem Real_G2 (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (F.RO.m).footprint ⊔ (Redo.prefixes).footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D)ᶜ →
      FVP.fvP P ≤ (FVP.fvP D)ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (m : VariableAssignment) :
    (Procedure.Pr (GReal D).procedure () m (fun r g => r = true ∧ C.c.get g ≤ max_size) : ℝ) ≤
      (Procedure.Pr (Eager.main2 (G2 (DRestr D))).procedure () m (fun r _ => r = true) : ℝ) +
        ((max_size ^ 2 - max_size : ℤ) : ℝ) / 2 * (dstate.1 {default}).toReal +
        (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) +
        (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) := by
  sorry

end EXT

end GaudisCrypt.SHA3.Gext
