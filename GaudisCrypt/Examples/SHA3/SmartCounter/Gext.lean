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

/-- `cdistr` is lossless (`DCapacity.dunifin_ll`), as an expectation. -/
theorem cdistr_expected_one : cdistr.expected (fun _ => (1 : ENNReal)) = 1 :=
  (is_lossless_iff_expected cdistr).mp BitWord.dunifin_ll

/-- A write at a fresh handle keeps `inv_ext`. -/
theorem inv_ext_set_fresh {m mi : smap} {F : handles} {ch : ℤ}
    (hf : ∀ h : ℤ, FMap.dom F h → h < ch) (v : capacity × flag) (h : inv_ext m mi F) :
    inv_ext m mi (FMap.set F ch v) := by
  obtain ⟨x, h, hx, hget⟩ := h
  have hne : h ≠ ch := fun he => by
    have : (h : ℤ) < ch := hf h (by rw [FMap.domE, hget]; simp)
    exact lt_irrefl _ (he ▸ this)
  exact ⟨x, h, hx, by rw [FMap.get_set_neqE _ _ _ _ hne]; exact hget⟩

/-- The handles stay below `G1.chandle` after a write at it and its increment. -/
theorem fresh_set {F : handles} {ch : ℤ} (hf : ∀ h : ℤ, FMap.dom F h → h < ch)
    (v : capacity × flag) : ∀ h : ℤ, FMap.dom (FMap.set F ch v) h → h < ch + 1 := by
  intro h hd
  rcases (FMap.mem_set _ _ _ _).mp hd with hd | rfl
  · have : h < ch := hf h hd
    omega
  · omega

/-- A fresh write keeps the bindings of `F`. -/
theorem get_set_fresh {F : handles} {ch : ℤ} (hf : ∀ h : ℤ, FMap.dom F h → h < ch)
    (w : capacity × flag) :
    ∀ h v, FMap.get F h = some v → FMap.get (FMap.set F ch w) h = some v := by
  intro h v hv
  have hne : h ≠ ch := fun he => by
    have : (h : ℤ) < ch := hf h (by rw [FMap.domE, hv]; simp)
    exact lt_irrefl _ (he ▸ this)
  rw [FMap.get_set_neqE _ _ _ _ hne, hv]

/-- `inv_ext` for an extension of `F`. -/
theorem inv_ext_mono {m mi m' mi' : smap} {F F' : handles}
    (hm : FMap.fdom m ∪ FMap.fdom mi ⊆ FMap.fdom m' ∪ FMap.fdom mi')
    (hF : ∀ h v, FMap.get F h = some v → FMap.get F' h = some v) :
    inv_ext m mi F → inv_ext m' mi' F' := by
  rintro ⟨x, h, hx, hget⟩
  exact ⟨x, h, hm hx, hF _ _ hget⟩

/-- `G1`'s update of `G1.bext` at the start of `S.f`, `S.fi`, against `inv_ext1`: the bad event, an
unknown handle for `x.2`, or `inv_ext`, all for the (extended) map `F'`. -/
theorem bext_pre {b1 b2 : Bool} {m mi : smap} {F F' : handles} {c : capacity}
    (hb : inv_ext1 b1 b2 m mi F) (hF : ∀ h v, FMap.get F h = some v → FMap.get F' h = some v) :
    (b1 || decide (FMap.rng F (c, Unknown))) = true →
      b2 = true ∨ FMap.rng F' (c, Unknown) ∨ inv_ext m mi F' := by
  intro h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · rcases hb h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (inv_ext_mono (fun _ h => h) hF h))
  · obtain ⟨z, hz⟩ := (FMap.rngE _ _).mp h
    exact Or.inr (Or.inl ((FMap.rngE _ _).mpr ⟨z, hF _ _ hz⟩))

/-- Back to `inv_ext1` from the weakened implication, after `x` entered `G1.m` or `G1.mi` and `F`
grew. -/
theorem inv_ext1_of_weak {b1 b2 : Bool} {m mi m' mi' : smap} {F F' : handles} {x : state}
    (hb : b1 = true → b2 = true ∨ FMap.rng F (x.2, Unknown) ∨ inv_ext m mi F)
    (hx : x ∈ FMap.fdom m' ∪ FMap.fdom mi')
    (hm : FMap.fdom m ∪ FMap.fdom mi ⊆ FMap.fdom m' ∪ FMap.fdom mi')
    (hF : ∀ h v, FMap.get F h = some v → FMap.get F' h = some v) :
    inv_ext1 b1 b2 m' mi' F' := by
  intro h1
  rcases hb h1 with h | h | h
  · exact Or.inl h
  · obtain ⟨z, hz⟩ := (FMap.rngE _ _).mp h
    exact Or.inr ⟨x, z, hx, hF _ _ hz⟩
  · exact Or.inr (inv_ext_mono hm hF h)

/-- `inv_ext1_of_weak` when the unknown handle `hy` is resampled (`G2`'s `FRO.get`): a witness at
`hy` makes `G2`'s update of `G1.bext` fire. -/
theorem inv_ext1_hit {b1 b2 : Bool} {m mi m' mi' : smap} {F : handles} {x : state} {hy : handle}
    (hb : b1 = true → b2 = true ∨ FMap.rng F (x.2, Unknown) ∨ inv_ext m mi F)
    (hx : x ∈ FMap.fdom m' ∪ FMap.fdom mi')
    (hm : FMap.fdom m ∪ FMap.fdom mi ⊆ FMap.fdom m' ∪ FMap.fdom mi') (w : capacity × flag) :
    inv_ext1 b1 (b2 || decide (bad_ext m mi (oget (FMap.get F hy)).1) ||
      decide ((oget (FMap.get F hy)).1 = x.2)) m' mi' (FMap.set F hy w) := by
  intro h1
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rcases hb h1 with h | h | ⟨x', z, hx', hz⟩
  · exact Or.inl (Or.inl (Or.inl h))
  · obtain ⟨z, hz⟩ := (FMap.rngE _ _).mp h
    by_cases hzy : z = hy
    · subst hzy
      exact Or.inl (Or.inr (by rw [hz]; rfl))
    · exact Or.inr ⟨x, z, hx, by rw [FMap.get_set_neqE _ _ _ _ hzy, hz]⟩
  · by_cases hzy : z = hy
    · subst hzy
      refine Or.inl (Or.inl (Or.inr ?_))
      rw [hz]
      simp only [bad_ext, oget, Option.getD_some, ← Finset.mem_union, ← Finset.image_union]
      exact Finset.mem_image.mpr ⟨x', hx', rfl⟩
    · exact Or.inr ⟨x', z, hm hx', by rw [FMap.get_set_neqE _ _ _ _ hzy, hz]⟩

/-! ## The section `EXT` -/

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

section EXT

/-- One oracle step from `inv_lt` to `inv_le`: each of `G1.m`, `G1.mi` gains at most a binding, and
the count plus the unknown handles does not grow. -/
theorem inv_lt.step {m2 mi2 m2' mi2' : smap} {c1 : ℤ} {Fm2 Fm2' : handles} {count2 count2' : ℤ}
    (h : inv_lt m2 mi2 c1 Fm2 count2)
    (hm : ((FMap.fdom m2').card : ℤ) ≤ (FMap.fdom m2).card + 1)
    (hmi : ((FMap.fdom mi2').card : ℤ) ≤ (FMap.fdom mi2).card + 1)
    (hF : count2' + (FMap.fdom (FMap.restr Unknown Fm2')).card ≤
      count2 + (FMap.fdom (FMap.restr Unknown Fm2)).card) :
    inv_le m2' mi2' c1 Fm2' count2' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by omega, by omega, by omega, h4⟩

omit [SLCommon.Params] in
/-- `set_set_eqE`. -/
theorem set_set_same {α β : Type} [DecidableEq α] (m : FMap α β) (x : α) (b c : β) :
    FMap.set (FMap.set m x b) x c = FMap.set m x c := by
  rw [FMap.set_setE, if_pos rfl]

/-- `G2`'s update of `G1.bext` is `ReSample.f1`'s: `bad_ext` is membership in the capacities of
`G1.m`, `G1.mi`. -/
theorem bext_eq (b : Bool) (m mi : smap) (c x : capacity) :
    (b || decide (bad_ext m mi c) || decide (c = x)) =
      (b || decide (c ∈ Finset.image Prod.snd (FMap.fdom m ∪ FMap.fdom mi) ∪ fset1 x)) := by
  simp only [bad_ext, fset1, Finset.image_union, Finset.mem_union, Finset.mem_singleton,
    Bool.or_assoc, ← Bool.decide_or]

/-- `inv_le` at a larger budget (below `max_size`). -/
theorem inv_le.mono {m2 mi2 : smap} {c1 c1' : ℤ} {Fm2 : handles} {count2 : ℤ}
    (h : inv_le m2 mi2 c1 Fm2 count2) (hc : c1 ≤ c1') (hc' : c1' ≤ max_size) :
    inv_le m2 mi2 c1' Fm2 count2 := by
  obtain ⟨h1, h2, h3, -⟩ := h
  exact ⟨by omega, by omega, by omega, hc'⟩

end EXT

end GaudisCrypt.SHA3.Gext
