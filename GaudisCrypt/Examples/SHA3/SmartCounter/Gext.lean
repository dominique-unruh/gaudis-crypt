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

set_option maxHeartbeats 8000000 in
-- `within_lens` on `G2.S`'s procedures, against a pair of ten variables, is slow
/-- `G2(DRestr(D))` touches `glob D` and the variables of `C`, `F.RO` and `G1` (not `FRO.m`).  Not
an EC lemma: EasyCrypt reads a concrete module's globals off its code (for `Eager_1_2`'s side
conditions, in `Real_G2`). -/
theorem fvP_G2 (D : DISTINGUISHER) :
    FVP.fvP (G2 (DRestr D)) ≤ FVP.fvP D ⊔ (Lens.pair C.c (Lens.pair C.queries (Lens.pair F.RO.m
      (Lens.pair G1.m (Lens.pair G1.mi (Lens.pair G1.mh (Lens.pair G1.mhi (Lens.pair G1.chandle
        (Lens.pair G1.paths G1.bext))))))))).footprint := by
  fp_module (Lens.pair C.c (Lens.pair C.queries (Lens.pair F.RO.m
      (Lens.pair G1.m (Lens.pair G1.mi (Lens.pair G1.mh (Lens.pair G1.mhi (Lens.pair G1.chandle
        (Lens.pair G1.paths G1.bext)))))))))

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

omit [SLCommon.Params] in
theorem rng_restr {«from» «to» φ : Type} [DecidableEq «from»] [DecidableEq φ]
    (m : FMap «from» («to» × φ)) (f : φ) (x : «to») :
    FMap.rng (FMap.restr f m) x ↔ FMap.rng m (x, f) := by
  rw [FMap.rngE, FMap.rngE]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [FMap.restrP] at hz
    rcases hm : FMap.get m z with _ | ⟨t, f'⟩
    · simp [hm] at hz
    · simp only [hm, Option.bind_some] at hz
      split_ifs at hz with hf
      · simp only [Option.some.injEq] at hz
        simp [hz, hf]
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [FMap.restrP, hz]; simp⟩

section

variable (D : DISTINGUISHER)

/-- `equiv G1_G2 : G1(DRestr(D)).main ~ Eager(G2(DRestr(D))).main1 : ={glob D} ==>
={res} /\ inv_ext1 G1.bext{1} G1.bext{2} G1.m{2} G1.mi{2} FRO.m{2}`, for
`declare module D <: DISTINGUISHER {-G1, -G2, -FRO, -C}`. -/
theorem G1_G2 (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ ((G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔
      (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint ⊔ (FRO.m).footprint ⊔ C.footprint ⊔ (F.RO.m).footprint)ᶜ) :
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

omit [SLCommon.Params] in
theorem fset0_eqP {α : Type} (s : FSet α) : s = fset0 ↔ ∀ x, x ∉ s := by
  simp only [fset0]
  exact Finset.eq_empty_iff_forall_notMem

omit [SLCommon.Params] in
theorem size_set {α β : Type} [DecidableEq α] (m : FMap α β) (x : α) (y : β) :
    ((FMap.fdom (FMap.set m x y)).card : ℤ) =
      if FMap.dom m x then (FMap.fdom m).card else (FMap.fdom m).card + 1 := by
  rw [FMap.fdom_set]
  split_ifs with hx
  · rw [Finset.insert_eq_of_mem ((FMap.mem_fdom _ _).mpr hx)]
  · rw [Finset.card_insert_of_notMem (fun h => hx ((FMap.mem_fdom _ _).mp h))]

omit [SLCommon.Params] in
theorem size_set_le {α β : Type} [DecidableEq α] (m : FMap α β) (x : α) (y : β) :
    ((FMap.fdom (FMap.set m x y)).card : ℤ) ≤ (FMap.fdom m).card + 1 := by
  rw [size_set]; split_ifs <;> omega

omit [SLCommon.Params] in
theorem size_rem {α β : Type} [DecidableEq α] (m : FMap α β) (x : α) :
    ((FMap.fdom (FMap.rem m x)).card : ℤ) =
      if FMap.dom m x then (FMap.fdom m).card - 1 else (FMap.fdom m).card := by
  have he : FMap.fdom (FMap.rem m x) = (FMap.fdom m).erase x := by
    ext z; simp [FMap.fdom, FMap.rem, Finmap.mem_keys]
  rw [he]
  split_ifs with hx
  · rw [Finset.card_erase_of_mem ((FMap.mem_fdom _ _).mpr hx)]
  · rw [Finset.erase_eq_of_notMem (fun h => hx ((FMap.mem_fdom _ _).mp h))]

omit [SLCommon.Params] in
theorem size_rem_le {α β : Type} [DecidableEq α] (m : FMap α β) (x : α) :
    ((FMap.fdom (FMap.rem m x)).card : ℤ) ≤ (FMap.fdom m).card := by
  rw [size_rem]; split_ifs <;> omega

omit [SLCommon.Params] in
theorem size_ge0 {α β : Type} (m : FMap α β) : 0 ≤ ((FMap.fdom m).card : ℤ) := by
  positivity

omit [SLCommon.Params] in
theorem size0 {α β : Type} :
    ((FMap.fdom (FMap.empty : FMap α β)).card : ℤ) = 0 := by
  simp

/-- `fcard_image_leq` and `fcardU` for the capacities of `G1.m`, `G1.mi`. -/
theorem card_image_snd_le {m mi : smap} (k : ℤ) (hm : ((FMap.fdom m).card : ℤ) ≤ k)
    (hmi : ((FMap.fdom mi).card : ℤ) ≤ k) :
    ((Finset.image Prod.snd (FMap.fdom m ∪ FMap.fdom mi)).card : ℤ) ≤ 2 * k := by
  have := (Finset.card_image_le (s := FMap.fdom m ∪ FMap.fdom mi) (f := Prod.snd)).trans
    (Finset.card_union_le _ _)
  have : ((Finset.image Prod.snd (FMap.fdom m ∪ FMap.fdom mi)).card : ℤ) ≤
      (FMap.fdom m).card + (FMap.fdom mi).card := by exact_mod_cast this
  omega

omit [SLCommon.Params] in
/-- `fcardU` and `fcard1`. -/
theorem card_union_fset1_le {α : Type} [DecidableEq α] (s : FSet α) (x : α) :
    ((s ∪ fset1 x).card : ℤ) ≤ s.card + 1 := by
  exact_mod_cast (Finset.card_union_le _ _).trans (by simp [fset1])

/-- One call of `ReSample.f` does not increase `gcolPotential` on `(G1.bext, ReSample.count)` (EC's
`fel` step `rnd (mem (image snd (fdom G1.m `|` fdom G1.mi)))` and `Mu_mem.mu_mem`). -/
theorem ReSample_f_potential [Lens.Disjoint G1.bext ReSample_count]
    (hfr : GcolFresh ReSample_count) :
    phoareProc (fun _ _ => True) (ReSample.f ReSample_count).procedure
      (fun _ g => gcolPotential ((Lens.pair G1.bext ReSample_count).get g)) (· ≤ ·)
      (fun _ g => gcolPotential ((Lens.pair G1.bext ReSample_count).get g)) := by
  gcol_disj hfr ReSample_count
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  split_ifs with h
  · exact gcolPotential_step _ _ _ (card_image_snd_le _ h.1 h.2.1) h.2.2
  · exact Strong_RP_RF.expected_const_le_self _ _

/-- `ReSample_f_potential` for `ReSample.f1` (EC's `rnd (mem (image snd (fdom G1.m `|` fdom G1.mi)
`|` fset1 x))`). -/
theorem ReSample_f1_potential [Lens.Disjoint G1.bext ReSample_count]
    (hfr : GcolFresh ReSample_count) :
    phoareProc (fun _ _ => True) (ReSample.f1 ReSample_count).procedure
      (fun _ g => gcolPotential ((Lens.pair G1.bext ReSample_count).get g)) (· ≤ ·)
      (fun _ g => gcolPotential ((Lens.pair G1.bext ReSample_count).get g)) := by
  gcol_disj hfr ReSample_count
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  split_ifs with h
  · refine gcolPotential_step _ _ _ ?_ h.2.2
    have h1 := card_image_snd_le _ (Int.le_sub_one_of_lt h.1) (Int.le_sub_one_of_lt h.2.1)
    refine (card_union_fset1_le _ _).trans ?_
    omega
  · exact Strong_RP_RF.expected_const_le_self _ _

/-- A join of footprints below a join containing each of its joinands (`fp_mem`, splitting the
left-hand join). -/
syntax "fp_sub" : tactic
macro_rules
  | `(tactic| fp_sub) => `(tactic| first | fp_mem | (refine sup_le ?_ ?_ <;> fp_sub))

section EXT

variable (D : DISTINGUISHER)

/-- `local equiv RROset_inv_lt : RRO.set ~ RRO.set : ={x, y, FRO.m} /\ inv_lt G1.m{2} G1.mi{2}
C.c{1} FRO.m{2} ReSample.count{2} ==> ={res, FRO.m} /\ inv_lt …`, with `ReSample.count` outside the
variables of `G1` and `C` (exception E6: `GcolFresh`). -/
theorem RROset_inv_lt (hfr : GcolFresh ReSample_count) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ FRO.m.get g₁ = FRO.m.get g₂ ∧
        inv_lt (G1.m.get g₂) (G1.mi.get g₂) (C.c.get g₁) (FRO.m.get g₂) (ReSample_count.get g₂))
      (PROM.FullRO.FRO_T.set handle capacity RRO).procedure
      (PROM.FullRO.FRO_T.set handle capacity RRO).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ FRO.m.get g₁ = FRO.m.get g₂ ∧
        inv_lt (G1.m.get g₂) (G1.mi.get g₂) (C.c.get g₁) (FRO.m.get g₂)
          (ReSample_count.get g₂)) := by
  gcol_disj hfr ReSample_count
  simp only [RRO, PROM.FullRO.FullEager.RRO, PROM.FullRO.FRO_T.set.mk_simp]
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_skip
  rintro x y m c _ _ _ _ _ n ⟨h, rfl, h1, h2, h3, h4⟩
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  refine ⟨rfl, h1, h2, ?_, h4⟩
  rw [FMap.restr_set, if_neg (by decide)]
  have := size_rem_le (FMap.restr Unknown m) x
  dsimp only
  omega

set_option maxHeartbeats 2000000 in
-- the reads of the initial state through fifteen writes
/-- EC's `fel 8 ReSample.count (fun x=> (2*max_size)%r / (2^c)%r) max_size G1.bext [ReSample.f : …;
ReSample.f1 : …]` in `Pr_ext`, as a supermartingale: `Gext.distinguish` ends with `gcolPotential`
on `(G1.bext, ReSample.count)` at most `max_size · 2 max_size / 2^c` (`Module.ewp_app_le` for the
oracles of `DRestr(D)`, `exp_decr` for them and for `Gext.resample`, with the steps
`ReSample_f_potential`, `ReSample_f1_potential`). -/
theorem Gext_potential [Lens.Disjoint G1.bext ReSample_count] (hD : Module.ECModule D distExt)
    (_hfresh : ReSample_count.footprint ≤ (FVP.fvP D ⊔ C.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint ⊔ (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔
      (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint)ᶜ)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (F.RO.m).footprint ⊔ (Redo.prefixes).footprint ⊔ (FRO.m).footprint ⊔
      (ROhandle.RO.m).footprint)ᶜ) :
    phoareProc (fun _ _ => True) (Gext ReSample_count D).procedure
      (fun _ g => gcolPotential ((Lens.pair G1.bext ReSample_count).get g)) (· ≤ ·)
      (fun _ _ => gcolEps * (max_size.toNat : ENNReal)) := by
  have hfr : GcolFresh ReSample_count :=
    _hfresh.trans (Footprint.compl_antimono (by
      unfold C.footprint
      iterate 11 refine sup_le ?_ ?_
      all_goals gcol_fp))
  gcol_disj hfr ReSample_count
  have hL : (Lens.pair G1.bext ReSample_count).footprint =
      G1.bext.footprint ⊔ ReSample_count.footprint := Footprint.lens_pair _ _
  -- the oracles' writes are outside `(G1.bext, ReSample.count)`
  have h1 : (C.c).footprint ≤ ((Lens.pair G1.bext ReSample_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h2 : (C.queries).footprint ≤ ((Lens.pair G1.bext ReSample_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h3 : (G1.m).footprint ≤ ((Lens.pair G1.bext ReSample_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h4 : (G1.mi).footprint ≤ ((Lens.pair G1.bext ReSample_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h5 : (G1.mh).footprint ≤ ((Lens.pair G1.bext ReSample_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h6 : (G1.mhi).footprint ≤ ((Lens.pair G1.bext ReSample_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h7 : (G1.chandle).footprint ≤ ((Lens.pair G1.bext ReSample_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h8 : (G1.paths).footprint ≤ ((Lens.pair G1.bext ReSample_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h9 : (FRO.m).footprint ≤ ((Lens.pair G1.bext ReSample_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h10 : (F.RO.m).footprint ≤ ((Lens.pair G1.bext ReSample_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have hDL : FVP.fvP D ≤ ((Lens.pair G1.bext ReSample_count).footprint)ᶜ := by
    rw [hL]
    refine (Footprint.le_compl_comm _ _).mpr (sup_le ?_ ?_)
    · exact (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_mem)))
    · exact _hfresh.trans (Footprint.compl_antimono (by fp_mem))
  -- the steps of `ReSample.f`, `ReSample.f1`
  have hsf : ∀ a g, Procedure.ewp (ReSample.f ReSample_count).procedure a
      (fun _ g' => gcolPotential ((Lens.pair G1.bext ReSample_count).get g')) g ≤
        gcolPotential ((Lens.pair G1.bext ReSample_count).get g) :=
    fun a g => ReSample_f_potential ReSample_count hfr a g trivial
  have hsf1 : ∀ a g, Procedure.ewp (ReSample.f1 ReSample_count).procedure a
      (fun _ g' => gcolPotential ((Lens.pair G1.bext ReSample_count).get g')) g ≤
        gcolPotential ((Lens.pair G1.bext ReSample_count).get g) :=
    fun a g => ReSample_f1_potential ReSample_count hfr a g trivial
  -- `ReSample.f` as `Iter`'s oracle (the spelling `exp_decr` meets in `Gext.resample`)
  have hsfI : ∀ a g, Procedure.ewp (IterProc.Orcl.f handle
      (IterProc.Orcl.mk handle { f := ReSample.f ReSample_count })).procedure a
      (fun _ g' => gcolPotential ((Lens.pair G1.bext ReSample_count).get g')) g ≤
        gcolPotential ((Lens.pair G1.bext ReSample_count).get g) := hsf
  phoare_proc_to_stmt
  phoare_inline 0
  repeat phoare_inline 0
  intro σ _
  simp only [Stmt.ewp_seq, Stmt.ewp_assign]
  simp_reads
  -- EC: the final `Gext.resample` (the iteration of `ReSample.f`) keeps the potential
  refine le_trans (Stmt.ewp_mono _ (fun τ => Stmt.ewp_le_of_expDecr
    (Lens.pair G1.bext ReSample_count).get gcolPotential _ ?_ _) _) ?_
  · exp_decr
  simp_reads
  erw [Stmt.ewp_call]
  simp_reads
  -- EC's `fel` on the oracles of `DRestr(D)`: they change `(G1.bext, ReSample.count)` only through
  -- `ReSample.f1`
  refine le_trans (Module.ewp_app_le (Lens.pair G1.bext ReSample_count) D distExt hD.representable
    hDL (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable (List block))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable state)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable state)
          | succ n => nomatch n)
    _ gcolPotential (fun n a g => ?_) _ _) ?_
  · cases n with
    | zero =>
      simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
        Module.fst_pair, Module.snd_pair]
      exact Procedure.ewp_le_of_expDecr _ _ _ (by exp_decr) a g
    | succ n => cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
          HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair]
        unfold Gext.S
        exact Procedure.ewp_le_of_expDecr _ _ _ (by exp_decr) a g
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair]
          unfold Gext.S
          exact Procedure.ewp_le_of_expDecr _ _ _ (by exp_decr) a g
        | succ n => nomatch n
  · change gcolPotential (G1.bext.get _, ReSample_count.get _) ≤ _
    simp_reads
    simp only [gcolPotential, Bool.false_eq_true, if_false, zero_add, sub_zero, le_refl]

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
      (F.RO.m).footprint ⊔ (Redo.prefixes).footprint ⊔ (FRO.m).footprint ⊔
      (ROhandle.RO.m).footprint)ᶜ)
    (_D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D).globᶜ →
      FVP.fvP P ≤ (FVP.fvP D).globᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (m : VariableAssignment) :
    (Procedure.Pr (Gext ReSample_count D).procedure () m
        (fun _ g => G1.bext.get g = true ∧ ReSample_count.get g ≤ max_size) : ℝ) ≤
      (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) := by
  -- EC: `fel 8 ReSample.count … [ReSample.f : …; ReSample.f1 : …]`, as the supermartingale
  -- `Gext_potential`
  haveI : Lens.Disjoint G1.bext ReSample_count := Lens.disjoint_of_footprint_le_compl _ _
    ((Footprint.le_compl_comm _ _).mp (_hfresh.trans (Footprint.compl_antimono (by fp_mem))))
  have hE : (Procedure.Pr (Gext ReSample_count D).procedure () m
      (fun _ g => G1.bext.get g = true ∧ ReSample_count.get g ≤ max_size) : ENNReal) ≤
      gcolEps * (max_size.toNat : ENNReal) := by
    rw [Procedure.Pr_eq_ewp]
    refine (Procedure.ewp_mono _ _ (G := fun _ g =>
      gcolPotential ((Lens.pair G1.bext ReSample_count).get g)) (fun _ g => ?_) _).trans
      (Gext_potential ReSample_count D hD _hfresh _hDd () m trivial)
    simp only [indicatorE, Lens.pair, gcolPotential]
    split_ifs with h h'
    · exact le_self_add
    · exact absurd h.1 h'
    all_goals exact bot_le
  have hmax := max_ge0
  have hfin : gcolEps * (max_size.toNat : ENNReal) ≠ ⊤ := by
    unfold gcolEps
    exact ENNReal.mul_ne_top (ENNReal.div_ne_top (by simp) (by simp)) (by simp)
  have h := ENNReal.toReal_mono hfin hE
  rw [ENNReal.coe_toReal] at h
  refine h.trans (le_of_eq ?_)
  unfold gcolEps
  rw [ENNReal.toReal_mul, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  push_cast
  rw [show ((2 * max_size).toNat : ℝ) = 2 * (max_size : ℝ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring,
    show (max_size.toNat : ℝ) = (max_size : ℝ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hmax]]
  ring


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
      (F.RO.m).footprint ⊔ (Redo.prefixes).footprint ⊔ (FRO.m).footprint ⊔
      (ROhandle.RO.m).footprint)ᶜ) :
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
      (F.RO.m).footprint ⊔ (Redo.prefixes).footprint ⊔ (FRO.m).footprint ⊔
      (ROhandle.RO.m).footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D).globᶜ →
      FVP.fvP P ≤ (FVP.fvP D).globᶜ →
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
  -- the local module `ReSample`'s variable `count`, fresh (exception E6)
  have hF : (FVP.fvP D ⊔ C.footprint ⊔ (F.RO.m).footprint ⊔ (FRO.m).footprint ⊔
      (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint).FinitelySupported := by
    unfold C.footprint
    repeat (first | exact hD.finitelySupported | exact .varLens _ | refine .sup ?_ ?_)
  obtain ⟨RC, hc, -⟩ := Footprint.exists_fresh ℤ hF
  -- `G2(DRestr(D))` is an `FRO` distinguisher outside `FRO.m`
  have hG2d : FVP.fvP (G2 (DRestr D)) ≤ ((FRO.m).footprint)ᶜ := by
    refine (fvP_G2 D).trans (sup_le (_hDd.trans (Footprint.compl_antimono (by fp_mem))) ?_)
    simp only [Footprint.lens_pair]
    fp_disjoint
  have hG2 : Module.ECModule (G2 (DRestr D)) (PROM.FullRO.FRO_ext handle capacity) :=
    ⟨PROM.FullRO.FRO_Distinguisher.representable handle capacity Unit Bool _,
      Footprint.FinitelySupported.mono (fvP_G2 D) (hD.finitelySupported.sup (by
        simp only [Footprint.lens_pair]
        repeat (first | exact .varLens _ | refine .sup ?_ ?_)))⟩
  -- EC's `byequiv (Eager_1_2 (G2(DRestr(D))))`: `main2` runs as `main1`
  have heq : ∀ E, Procedure.Pr (Eager.main2 (G2 (DRestr D))).procedure () m E =
      Procedure.Pr (Eager.main1 (G2 (DRestr D))).procedure () m E := fun E => by
    unfold Procedure.Pr
    rw [PROM.FullRO.FullEager.Eager.main2_eq_main1 handle capacity Unit Bool ROhandle.dout
      ROhandle.FRO.m (fun _ => BitWord.dunifin_ll) _ hG2 hG2d]
  -- EC: `apply (ler_trans _ _ _ (Real_G1 D D_ll &m))`, then the four summands
  have hG1G2 := G1_G2 D hD (_hDd.trans (Footprint.compl_antimono (by fp_sub)))
  have h1 := Real_G1 D hD (_hDd.trans (Footprint.compl_antimono (by fp_sub))) D_ll m
  have h2 : Procedure.Pr (G1 (DRestr D)).procedure () m (fun r _ => r = true) =
      Procedure.Pr (Eager.main2 (G2 (DRestr D))).procedure () m (fun r _ => r = true) :=
    (Procedure.Pr_eq_of_prhlProc hG1G2 (fun _ _ _ _ h => by rw [h.1]) (a₂ := ()) rfl).trans
      (heq _).symm
  have h3 := Pr_G1col D hD (_hDd.trans (Footprint.compl_antimono (by fp_sub))) D_ll m
  have h4 : Procedure.Pr (G1 (DRestr D)).procedure () m (fun _ g => G1.bext.get g = true) ≤
      Procedure.Pr (Gext RC D).procedure () m
        (fun _ g => G1.bext.get g = true ∧ RC.get g ≤ max_size) := by
    -- EC: `byequiv (G1_G2 D)`, `byequiv (Eager_1_2 …)`, `byequiv EG2_Gext`
    refine (Procedure.Pr_le_of_prhlProc hG1G2 (E₂ := fun _ g => G1.bext.get g = true ∨
      inv_ext (G1.m.get g) (G1.mi.get g) (FRO.m.get g)) (fun _ _ _ _ h hb => h.2 hb) (a₂ := ())
      rfl).trans ?_
    rw [← heq]
    exact Procedure.Pr_le_of_prhlProc (EG2_Gext RC D hD hc _hDd)
      (fun _ _ _ _ h hb => ⟨h.2 hb, h.1⟩) (a₁ := ()) (a₂ := ()) rfl
  have h5 := Pr_ext RC D hD hc _hDd D_ll m
  have h4' : (Procedure.Pr (G1 (DRestr D)).procedure () m (fun _ g => G1.bext.get g = true) : ℝ) ≤
      _ := (NNReal.coe_le_coe.mpr h4).trans h5
  rw [h2] at h1
  refine h1.trans (le_of_le_of_eq (add_le_add (add_le_add le_rfl h3) h4') ?_)
  ring

end EXT

end GaudisCrypt.SHA3.Gext
