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

/-- The invariant of EC's `call (_: ={F.RO.m, G1.m, G1.mi, G1.mh, G1.mhi, G1.paths, G1.chandle,
FRO.m, C.queries, C.c} /\ inv_ext1 G1.bext{1} G1.bext{2} G1.m{2} G1.mi{2} FRO.m{2} /\
(forall h, h \in FRO.m => h < G1.chandle){1})` in `G1_G2`. -/
def g12Inv (g₁ g₂ : VariableAssignment) : Prop :=
  colEq g₁ g₂ ∧ inv_ext1 (G1.bext.get g₁) (G1.bext.get g₂) (G1.m.get g₂) (G1.mi.get g₂)
    (FRO.m.get g₂) ∧ ∀ h : ℤ, FMap.dom (FRO.m.get g₁) h → h < G1.chandle.get g₁

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

set_option maxHeartbeats 4000000 in
-- the inlined oracles' wp goals are large
/-- EC's `M.f` step in `G1_G2`: `G1` writes the unknown handle `G1.chandle`, `FRO.sample` does
too, as it is fresh. -/
theorem M_f_G12 :
    prhlProc (sig₁ := procsig (List block) -> block) (sig₂ := procsig (List block) -> block)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g12Inv g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block G1.M).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app G2.M ROhandle.FRO)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g12Inv g₁ g₂) := by
  unfold g12Inv
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_while (§p{1} = §p{2} ∧ §(localVarLens "h" handle){1} = §(localVarLens "h" handle){2} ∧
      §i{1} = §i{2} ∧ §sa{1} = §sa{2} ∧ §counter{1} = §counter{2} ∧
      colEq §allGlobals{1} §allGlobals{2} ∧
      inv_ext1 §G1.bext{1} §G1.bext{2} §G1.m{2} §G1.mi{2} §FRO.m{2} ∧
      ∀ h : ℤ, FMap.dom §FRO.m{1} h → h < §G1.chandle{1})
  case body =>
    stmt_wp
    equiv_if
    case guard =>
      rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, hE, -⟩, -⟩
      rw [hE.2.2.2.2.2.2.1]
    case «then» =>
      stmt_wp
      equiv_skip
      rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, hE, rest⟩, -⟩, -⟩
      rw [hE.2.2.2.2.2.2.1]
      exact ⟨rfl, rfl, rfl, rfl, rfl, hE, rest⟩
    case «else» =>
      equiv_if
      case guard =>
        rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, hE, -⟩, -⟩, -⟩
        rw [hE.2.2.2.2.2.2.2.2.2]
      case «else» =>
        equiv_skip
        rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rest⟩, -⟩, -⟩, -⟩
        exact ⟨rfl, rfl, rfl, rfl, rfl, rest⟩
      case «then» =>
        stmt_wp
        equiv_rnd
        stmt_wp
        equiv_rnd
        stmt_wp
        equiv_skip
        rintro σ₂ g₁ p h i sa c ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, hE, hb, hf⟩, -⟩, -⟩, -⟩ a - r -
        simp only [colEq] at hE
        obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hE
        rw [e8, e6] at hf
        have hd : ¬ FMap.dom (FRO.m.get σ₂.globals) (G1.chandle.get σ₂.globals) := fun hd =>
          lt_irrefl _ (hf _ hd)
        simp only [hd, decide_false, Bool.not_false, if_true]
        col_rw
        split_ifs <;> exact ⟨trivial, trivial, trivial, trivial, trivial, by col_eq,
          fun h1 => (hb h1).imp_right (inv_ext_set_fresh hf _), fresh_set hf _⟩
  case guard =>
    rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, -⟩
    rfl
  case exit =>
    rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9,
      e10⟩, hb, hf⟩ - a -
    rw [e8, e6] at hf
    col_rw
    split_ifs <;> exact ⟨by trivial, by col_eq, hb, hf⟩
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x _ ⟨rfl, hE, hb, hf⟩
  exact ⟨rfl, hE, hb, hf⟩

set_option maxHeartbeats 4000000 in
-- the inlined oracles' wp goals are large
/-- EC's `S.fi` step in `G1_G2` (`seq 6 8`, then `if`, `rcondt{2} 4`). -/
theorem S_fi_G12 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g12Inv g₁ g₂)
      (Indifferentiability.DPRIMITIVE.fi state (List block) block G1.S).procedure
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app G2.S ROhandle.FRO)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g12Inv g₁ g₂) := by
  unfold g12Inv G1.S
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
      inv_ext1 §G1.bext{1} §G1.bext{2} §G1.m{2} §G1.mi{2} §FRO.m{2} ∧
      ∀ h : ℤ, FMap.dom §FRO.m{1} h → h < §G1.chandle{1})
  · stmt_wp
    equiv_skip
    intro _ _ _ _ h
    exact h
  · equiv_if
    case guard =>
      rintro g₁ g₂ x _ ⟨rfl, ⟨-, e2, -⟩, -⟩
      rw [e2]
    case «else» =>
      stmt_wp
      equiv_skip
      rintro g₁ g₂ x _ ⟨⟨rfl, hE, hb, hf⟩, -⟩
      exact ⟨by rw [hE.2.1], hE, hb, hf⟩
    case «then» =>
      equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §hx2{1} = §hx2{2} ∧ §y{1} = §y{2} ∧
          §t{2} = decide (FMap.in_dom_with §FRO.m{1}
            (oget (FMap.get §G1.mhi{1} ((§x0{1}).1, §hx2{1}))).2 Unknown) ∧
          colEq §allGlobals{1} §allGlobals{2} ∧
          (§G1.bext{1} = true → §G1.bext{2} = true ∨ FMap.rng §FRO.m{2} ((§x0{2}).2, Unknown) ∨
            inv_ext §G1.m{2} §G1.mi{2} §FRO.m{2}) ∧
          ∀ h : ℤ, FMap.dom §FRO.m{1} h → h < §G1.chandle{1})
      · stmt_wp
        equiv_rnd
        equiv_rnd
        stmt_wp
        equiv_skip
        rintro g₁ g₂ x0 _ ⟨⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb, hf⟩, -⟩ a - b -
        rw [e8, e6] at hf
        simp only [rng_restr]
        col_rw
        simp only [FRO.m] at hb hf ⊢
        by_cases hk : FMap.rng (ROhandle.FRO.m.get g₂) (x0.2, Known)
        · simp only [hk, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
          exact ⟨trivial, rfl, decide_eq_decide.mpr Iff.rfl, by col_eq,
            bext_pre hb (fun _ _ h => h), hf⟩
        · simp only [hk, decide_false, Bool.not_false, if_true]
          exact ⟨trivial, rfl, decide_eq_decide.mpr Iff.rfl, by col_eq,
            bext_pre hb (get_set_fresh hf _), fresh_set hf _⟩
      · equiv_if
        case guard =>
          rintro g₁ g₂ x0 hx2 y _ _ _ t ⟨rfl, rfl, rfl, rfl, ⟨-, -, -, -, e5, -⟩, -⟩
          rw [e5, Bool.decide_and]
        case «else» =>
          stmt_wp
          equiv_skip
          rintro g₁ g₂ x0 hx2 y _ _ _ t ⟨⟨rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9,
            e10⟩, hb, hf⟩, -⟩
          rw [e8, e6] at hf
          col_rw
          simp only [FRO.m] at hb hf ⊢
          refine ⟨trivial, by col_eq, inv_ext1_of_weak hb ?_ ?_ (get_set_fresh hf _),
            fresh_set hf _⟩
          · simp [FMap.fdom_set]
          · intro z hz
            simp only [FMap.fdom_set, Finset.mem_union, Finset.mem_insert] at hz ⊢
            tauto
        case «then» =>
          stmt_wp
          stmt_wp{2} 1
          stmt_wp
          equiv_skip
          rintro g₁ g₂ x0 hx2 y _ _ _ t ⟨⟨rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9,
            e10⟩, hb, hf⟩, hg⟩
          refine ⟨cdistr_expected_one, fun a _ => ?_⟩
          simp only [decide_eq_true_eq] at hg
          obtain ⟨-, hin⟩ := hg
          rw [e8, e6] at hf
          rw [e5, e8] at hin
          col_rw
          simp only [FRO.m] at hb hf hin ⊢
          have h1 := hin.1
          simp only [h1, decide_true, if_true]
          refine ⟨trivial, by col_eq, inv_ext1_hit hb ?_ ?_ _, ?_⟩
          · simp [FMap.fdom_set]
          · intro z hz
            simp only [FMap.fdom_set, Finset.mem_union, Finset.mem_insert] at hz ⊢
            tauto
          · intro h hd
            rcases (FMap.mem_set _ _ _ _).mp hd with hd | rfl
            · exact hf h hd
            · exact hf _ h1

set_option maxHeartbeats 4000000 in
-- the inlined oracles' wp goals are large
/-- EC's `S.f` step in `G1_G2` (`seq 2 2`, `seq 3 5`, `seq 1 1`). -/
theorem S_f_G12 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g12Inv g₁ g₂)
      (Indifferentiability.DPRIMITIVE.f state (List block) block G1.S).procedure
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app G2.S ROhandle.FRO)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g12Inv g₁ g₂) := by
  unfold g12Inv G1.S
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
          inv_ext1 §G1.bext{1} §G1.bext{2} §G1.m{2} §G1.mi{2} §FRO.m{2} ∧
          ∀ h : ℤ, FMap.dom §FRO.m{1} h → h < §G1.chandle{1})
  · stmt_wp
    equiv_skip
    intro _ _ _ _ h
    exact h
  · equiv_if
    case guard =>
      rintro g₁ g₂ x _ ⟨rfl, ⟨-, -, -, e4, -⟩, -⟩
      rw [e4]
    case «else» =>
      stmt_wp
      equiv_skip
      rintro g₁ g₂ x _ ⟨⟨rfl, hE, hb, hf⟩, -⟩
      exact ⟨by rw [hE.2.2.2.1], hE, hb, hf⟩
    case «then» =>
      equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
          inv_ext1 §G1.bext{1} §G1.bext{2} §G1.m{2} §G1.mi{2} §FRO.m{2} ∧
          ∀ h : ℤ, FMap.dom §FRO.m{1} h → h < §G1.chandle{1})
      · equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §hx2{1} = §hx2{2} ∧
            §t{2} = decide (FMap.in_dom_with §FRO.m{1}
              (oget (FMap.get §G1.mh{1} ((§x0{1}).1, §hx2{1}))).2 Unknown) ∧
            colEq §allGlobals{1} §allGlobals{2} ∧
            (§G1.bext{1} = true → §G1.bext{2} = true ∨ FMap.rng §FRO.m{2} ((§x0{2}).2, Unknown) ∨
              inv_ext §G1.m{2} §G1.mi{2} §FRO.m{2}) ∧
            ∀ h : ℤ, FMap.dom §FRO.m{1} h → h < §G1.chandle{1})
        · equiv_seq 3 9 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
              inv_ext1 §G1.bext{1} §G1.bext{2} §G1.m{2} §G1.mi{2} §FRO.m{2} ∧
              ∀ h : ℤ, FMap.dom §FRO.m{1} h → h < §G1.chandle{1})
          · stmt_wp
            equiv_if
            case guard =>
              rintro g₁ g₂ x _ ⟨⟨rfl, ⟨-, -, e3, -⟩, -⟩, -⟩
              rw [e3]
            case «then» =>
              equiv_rnd
              stmt_wp
              equiv_rnd
              stmt_wp
              equiv_skip
              rintro g₁ g₂ x0 _ ⟨⟨⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb, hf⟩, -⟩,
                -⟩ a - b -
              rw [e8, e6] at hf
              col_rw
              split_ifs <;> exact ⟨trivial, trivial, by col_eq, hb, hf⟩
            case «else» =>
              equiv_rnd
              equiv_rnd
              equiv_skip
              rintro g₁ g₂ x0 _ ⟨⟨⟨rfl, hE, hb, hf⟩, -⟩, -⟩ a - b -
              exact ⟨rfl, hE, hb, hf⟩
          · stmt_wp
            equiv_skip
            rintro g₁ g₂ x0 y _ _ ⟨rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb, hf⟩
            rw [e8, e6] at hf
            simp only [rng_restr]
            col_rw
            simp only [FRO.m] at hb hf ⊢
            by_cases hk : FMap.rng (ROhandle.FRO.m.get g₂) (x0.2, Known)
            · simp only [hk, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
              exact ⟨trivial, trivial, rfl, decide_eq_decide.mpr Iff.rfl, by col_eq,
                bext_pre hb (fun _ _ h => h), hf⟩
            · simp only [hk, decide_false, Bool.not_false, if_true]
              exact ⟨trivial, trivial, rfl, decide_eq_decide.mpr Iff.rfl, by col_eq,
                bext_pre hb (get_set_fresh hf _), fresh_set hf _⟩
        · equiv_if
          case guard =>
            rintro g₁ g₂ x0 y hx2 _ _ _ t ⟨rfl, rfl, rfl, rfl, ⟨-, -, -, -, -, -, e7, -⟩, -⟩
            rw [e7, Bool.decide_and]
          case «else» =>
            stmt_wp
            equiv_skip
            rintro g₁ g₂ x0 y hx2 _ _ _ t ⟨⟨rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9,
              e10⟩, hb, hf⟩, -⟩
            rw [e8, e6] at hf
            col_rw
            simp only [FRO.m] at hb hf ⊢
            refine ⟨trivial, trivial, by col_eq, inv_ext1_of_weak hb ?_ ?_ (get_set_fresh hf _),
              fresh_set hf _⟩
            · simp [FMap.fdom_set]
            · intro z hz
              simp only [FMap.fdom_set, Finset.mem_union, Finset.mem_insert] at hz ⊢
              tauto
          case «then» =>
            stmt_wp
            stmt_wp{2} 1
            stmt_wp
            equiv_skip
            rintro g₁ g₂ x0 y hx2 _ _ _ t ⟨⟨rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9,
              e10⟩, hb, hf⟩, hg⟩
            refine ⟨cdistr_expected_one, fun a _ => ?_⟩
            simp only [decide_eq_true_eq] at hg
            obtain ⟨-, hin⟩ := hg
            rw [e8, e6] at hf
            rw [e7, e8] at hin
            col_rw
            simp only [FRO.m] at hb hf hin ⊢
            have h1 := hin.1
            simp only [h1, decide_true, if_true]
            refine ⟨trivial, trivial, by col_eq, inv_ext1_hit hb ?_ ?_ _, ?_⟩
            · simp [FMap.fdom_set]
            · intro z hz
              simp only [FMap.fdom_set, Finset.mem_union, Finset.mem_insert] at hz ⊢
              tauto
            · intro h hd
              rcases (FMap.mem_set _ _ _ _).mp hd with hd | rfl
              · exact hf h hd
              · exact hf _ h1
      · stmt_wp
        equiv_skip
        rintro g₁ g₂ x0 y _ _ ⟨rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb, hf⟩
        rw [e8, e6] at hf
        col_rw
        split_ifs <;> exact ⟨trivial, by col_eq, hb, hf⟩

set_option maxHeartbeats 1000000 in
-- the inlined oracles' wp goals are large
/-- `DPRestr(S).fi` under `g12Inv` (`S_fi_G12`). -/
theorem DPRestr_fi_G12 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g12Inv g₁ g₂)
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr G1.S)).procedure
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr (Module.app G2.S ROhandle.FRO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g12Inv g₁ g₂) := by
  unfold g12Inv
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
      inv_ext1 §G1.bext{1} §G1.bext{2} §G1.m{2} §G1.mi{2} §FRO.m{2} ∧
      ∀ h : ℤ, FMap.dom §FRO.m{1} h → h < §G1.chandle{1})
  · stmt_wp
    equiv_skip
    intro _ _ _ _ h
    exact h
  · equiv_if
    case guard =>
      rintro g₁ g₂ _ _ _ _ ⟨-, -, hE, -⟩
      rw [hE.2.2.2.2.2.2.2.2.1]
    case «then» =>
      stmt_wp
      equiv_call S_fi_G12
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨rfl, rfl, hE, hb, hf⟩, -⟩
      refine ⟨⟨rfl, hE, hb, hf⟩, ?_⟩
      rintro r g₁' _ g₂' ⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb', hf'⟩
      exact ⟨rfl, by col_eq, hb', hf'⟩
    case «else» =>
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨-, rfl, rest⟩, -⟩
      exact ⟨rfl, rest⟩

set_option maxHeartbeats 1000000 in
-- the inlined oracles' wp goals are large
/-- `DPRestr(S).f` under `g12Inv` (`S_f_G12`). -/
theorem DPRestr_f_G12 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g12Inv g₁ g₂)
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr G1.S)).procedure
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr (Module.app G2.S ROhandle.FRO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g12Inv g₁ g₂) := by
  unfold g12Inv
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
      inv_ext1 §G1.bext{1} §G1.bext{2} §G1.m{2} §G1.mi{2} §FRO.m{2} ∧
      ∀ h : ℤ, FMap.dom §FRO.m{1} h → h < §G1.chandle{1})
  · stmt_wp
    equiv_skip
    intro _ _ _ _ h
    exact h
  · equiv_if
    case guard =>
      rintro g₁ g₂ _ _ _ _ ⟨-, -, hE, -⟩
      rw [hE.2.2.2.2.2.2.2.2.1]
    case «then» =>
      stmt_wp
      equiv_call S_f_G12
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨rfl, rfl, hE, hb, hf⟩, -⟩
      refine ⟨⟨rfl, hE, hb, hf⟩, ?_⟩
      rintro r g₁' _ g₂' ⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb', hf'⟩
      exact ⟨rfl, by col_eq, hb', hf'⟩
    case «else» =>
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨-, rfl, rest⟩, -⟩
      exact ⟨rfl, rest⟩

set_option maxHeartbeats 1000000 in
-- the inlined oracles' wp goals are large
/-- `DFRestr(M).f` under `g12Inv` (`M_f_G12`). -/
theorem DFRestr_f_G12 :
    prhlProc (sig₁ := procsig (List block) -> block) (sig₂ := procsig (List block) -> block)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g12Inv g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr G1.M)).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr (Module.app G2.M ROhandle.FRO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g12Inv g₁ g₂) := by
  unfold g12Inv
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§bs{1} = §bs{2} ∧ §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧
      colEq §allGlobals{1} §allGlobals{2} ∧
      inv_ext1 §G1.bext{1} §G1.bext{2} §G1.m{2} §G1.mi{2} §FRO.m{2} ∧
      ∀ h : ℤ, FMap.dom §FRO.m{1} h → h < §G1.chandle{1})
  · stmt_wp
    equiv_skip
    intro _ _ _ _ h
    exact h
  · equiv_if
    case guard =>
      rintro g₁ g₂ bs _ _ _ ⟨rfl, -, hE, -⟩
      rw [hE.2.2.2.2.2.2.2.2.2]
    case «else» =>
      stmt_wp
      equiv_skip
      rintro g₁ g₂ bs _ b _ ⟨⟨rfl, rfl, hE, rest⟩, -⟩
      rw [hE.2.2.2.2.2.2.2.2.2]
      exact ⟨rfl, hE, rest⟩
    case «then» =>
      equiv_if
      case guard =>
        rintro g₁ g₂ bs _ _ _ ⟨⟨rfl, -, hE, -⟩, -⟩
        rw [hE.2.2.2.2.2.2.2.2.1, hE.2.2.2.2.2.2.2.2.2]
      case «else» =>
        equiv_skip
        rintro g₁ g₂ bs _ b _ ⟨⟨⟨rfl, rfl, rest⟩, -⟩, -⟩
        exact ⟨rfl, rest⟩
      case «then» =>
        stmt_wp
        equiv_call M_f_G12
        stmt_wp
        equiv_skip
        rintro g₁ g₂ bs _ b _ ⟨⟨⟨rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb, hf⟩, -⟩,
          -⟩
        refine ⟨⟨by trivial, by col_eq, by simp_reads; exact hb, by simp_reads; exact hf⟩, ?_⟩
        rintro r g₁' _ g₂' ⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb', hf'⟩
        exact ⟨rfl, by col_eq, hb', hf'⟩

section

variable (D : DISTINGUISHER)

set_option maxHeartbeats 4000000 in
-- the eleven-variable invariant and the oracles' footprint checks
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
  -- the variables of `G1`, `C` and `FRO` lie outside `glob D`
  have hcc : (C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hcq : (C.queries).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hro : (F.RO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hfro : (FRO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  -- `G2`'s oracles write `FRO.m` as `ROhandle.FRO.m` (`writes_keep'` matches syntactically)
  have hfro' : (ROhandle.FRO.m).footprint ≤ (FVP.fvP D)ᶜ := hfro
  have hm : (G1.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hmi : (G1.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hmh : (G1.mh).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hmhi : (G1.mhi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hch : (G1.chandle).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hpa : (G1.paths).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hbx : (G1.bext).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hbc : (G1.bcol).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  -- EC's invariant, on the values of the variables it reads
  let L := Lens.pair C.c (Lens.pair C.queries (Lens.pair F.RO.m (Lens.pair FRO.m (Lens.pair G1.m
    (Lens.pair G1.mi (Lens.pair G1.mh (Lens.pair G1.mhi (Lens.pair G1.chandle
      (Lens.pair G1.paths G1.bext)))))))))
  let I : ℤ × FMap (List block) block × FMap (List block) block ×
      FMap handle (capacity × flag) × smap × smap × hsmap × hsmap × ℤ ×
      FMap capacity (List block × block) × Bool →
      ℤ × FMap (List block) block × FMap (List block) block ×
      FMap handle (capacity × flag) × smap × smap × hsmap × hsmap × ℤ ×
      FMap capacity (List block × block) × Bool → Prop := fun x y =>
    (x.2.2.1 = y.2.2.1 ∧ x.2.2.2.2.2.1 = y.2.2.2.2.2.1 ∧
      x.2.2.2.2.2.2.2.2.2.1 = y.2.2.2.2.2.2.2.2.2.1 ∧ x.2.2.2.2.1 = y.2.2.2.2.1 ∧
      x.2.2.2.2.2.2.2.1 = y.2.2.2.2.2.2.2.1 ∧ x.2.2.2.2.2.2.2.2.1 = y.2.2.2.2.2.2.2.2.1 ∧
      x.2.2.2.2.2.2.1 = y.2.2.2.2.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧ x.1 = y.1 ∧
      x.2.1 = y.2.1) ∧
    inv_ext1 x.2.2.2.2.2.2.2.2.2.2 y.2.2.2.2.2.2.2.2.2.2 y.2.2.2.2.1 y.2.2.2.2.2.1 y.2.2.2.1 ∧
    ∀ h : ℤ, FMap.dom x.2.2.2.1 h → h < x.2.2.2.2.2.2.2.2.1
  have hI : ∀ g₁ g₂, I (L.get g₁) (L.get g₂) ↔ g12Inv g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (L.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [L, Footprint.lens_pair]
    exact sup_le hcc (sup_le hcq (sup_le hro (sup_le hfro (sup_le hm (sup_le hmi
      (sup_le hmh (sup_le hmhi (sup_le hch (sup_le hpa hbx)))))))))
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
        touched_set_of_le_compl hro, touched_set_of_le_compl hfro, touched_set_of_le_compl hm,
        touched_set_of_le_compl hmi, touched_set_of_le_compl hmh,
        touched_set_of_le_compl hmhi, touched_set_of_le_compl hch, touched_set_of_le_compl hpa,
        touched_set_of_le_compl hbx, touched_set_of_le_compl hbc]
      exact h
    · simp only [g12Inv, colEq]
      simp_reads
      refine ⟨fun h => absurd h (by decide), fun h hd => ?_⟩
      rcases (FMap.mem_set _ _ _ _).mp hd with hd | rfl
      · exact absurd hd (FMap.mem_empty _)
      · norm_num
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
          DFRestr_f_G12
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair]
          unfold G1.S
          exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
            DPRestr_f_G12
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair]
            unfold G1.S
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              DPRestr_fi_G12
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, -, hI'⟩
    have hc := (hI g₁ g₂).mp hI'
    simp_reads
    exact hc.2.1


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
    (G : Footprint VariableAssignment)
    (_hGd : G ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (F.RO.m).footprint ⊔ (Redo.prefixes).footprint ⊔ (FRO.m).footprint ⊔
      (ROhandle.RO.m).footprint)ᶜ)
    (_D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ Gᶜ →
      FVP.fvP P ≤ Gᶜ →
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

/-- `inv_lt` gives `inv_le`. -/
theorem inv_lt.le {m2 mi2 : smap} {c1 : ℤ} {Fm2 : handles} {count2 : ℤ}
    (h : inv_lt m2 mi2 c1 Fm2 count2) : inv_le m2 mi2 c1 Fm2 count2 :=
  ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2⟩

/-- A `Known` write (`RRO.set`) keeps `inv_lt` (as `RROset_inv_lt`). -/
theorem inv_lt_set_known {m2 mi2 : smap} {c1 : ℤ} {Fm2 : handles} {count2 : ℤ}
    (h : inv_lt m2 mi2 c1 Fm2 count2) (x : handle) (y : capacity) :
    inv_lt m2 mi2 c1 (FMap.set Fm2 x (y, Known)) count2 := by
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  rw [FMap.restr_set, if_neg (by decide)]
  have := size_rem_le (FMap.restr Unknown Fm2) x
  have := h.2.2.1
  omega

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

set_option maxHeartbeats 1000000 in
-- the inlined oracles' wp goals are large
/-- EC's inner `call (_: ={x, …} /\ inv_lt … ==> ={res, …} /\ inv_le …)` for `S.fi` in `EG2_Gext`,
with `C.c` already incremented (EC's `swap -1`): `rcondt{1} 4`, `rcondt{2} 5`, `rcondt{2} 10`, the
left `RRO.get`'s sample coupled with `ReSample.f1`'s, `rnd{2}` for `FRO.get`'s. -/
theorem S_fi_ext (hfr : GcolFresh ReSample_count) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ colEq g₁ g₂ ∧ G1.bext.get g₁ = G1.bext.get g₂ ∧
        inv_lt (G1.m.get g₂) (G1.mi.get g₂) (C.c.get g₁ + 1) (FRO.m.get g₂)
          (ReSample_count.get g₂))
      (Indifferentiability.DPRIMITIVE.fi state (List block) block (Module.app G2.S RRO)).procedure
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Gext.S ReSample_count)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ colEq g₁ g₂ ∧ G1.bext.get g₁ = G1.bext.get g₂ ∧
        inv_le (G1.m.get g₂) (G1.mi.get g₂) (C.c.get g₁ + 1) (FRO.m.get g₂)
          (ReSample_count.get g₂)) := by
  gcol_disj hfr ReSample_count
  unfold Gext.S
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
      §G1.bext{1} = §G1.bext{2} ∧
      inv_lt §G1.m{2} §G1.mi{2} (§C.c{1} + 1) §FRO.m{2} §ReSample_count{2})
  · stmt_wp
    equiv_skip
    intro _ _ _ _ h
    exact h
  · equiv_if
    case guard =>
      rintro g₁ g₂ x _ ⟨rfl, ⟨-, e2, -⟩, -⟩
      rw [e2]
    case «else» =>
      stmt_wp
      equiv_skip
      rintro g₁ g₂ x _ ⟨⟨rfl, hE, hb, hI⟩, -⟩
      exact ⟨by rw [hE.2.1], hE, hb, hI.le⟩
    case «then» =>
      equiv_seq 7 7 : (§x0{1} = §x0{2} ∧ §hx2{1} = §hx2{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
          §G1.bext{1} = §G1.bext{2} ∧
          inv_lt §G1.m{2} §G1.mi{2} (§C.c{1} + 1) §FRO.m{2} §ReSample_count{2})
      · stmt_wp
        equiv_skip
        rintro g₁ g₂ x0 _ ⟨⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb, hI⟩, -⟩
        rw [e9] at hI
        col_rw
        split_ifs with h
        · exact ⟨trivial, trivial, by col_eq, hb, inv_lt_set_known hI _ _⟩
        · exact ⟨trivial, trivial, by col_eq, hb, hI⟩
      · equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §hx2{1} = §hx2{2} ∧ §y{1} = §y{2} ∧ §t{1} = §t{2} ∧
            colEq §allGlobals{1} §allGlobals{2} ∧ §G1.bext{1} = §G1.bext{2} ∧
            inv_lt §G1.m{2} §G1.mi{2} (§C.c{1} + 1) §FRO.m{2} §ReSample_count{2} ∧
            (§t{1} = true → FMap.in_dom_with §FRO.m{1}
              (oget (FMap.get §G1.mhi{1} ((§x0{1}).1, §hx2{1}))).2 Unknown))
        · stmt_wp
          equiv_rnd
          equiv_rnd
          equiv_skip
          rintro g₁ g₂ x0 hx2 _ _ ⟨rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb,
              hI⟩ a - b -
          rw [e9] at hI
          col_rw
          exact ⟨trivial, trivial, trivial, by col_eq, hb, hI, fun h => of_decide_eq_true h⟩
        · equiv_if
          case guard =>
            rintro g₁ g₂ x0 hx2 y t _ _ _ _ ⟨rfl, rfl, rfl, rfl, ⟨-, -, -, -, e5, -⟩, -⟩
            rw [e5]
          case «else» =>
            stmt_wp
            equiv_skip
            rintro g₁ g₂ x0 hx2 y t _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7,
                e8, e9,
              e10⟩, hb, hI, -⟩, -⟩
            rw [e9] at hI
            col_rw
            refine ⟨trivial, by col_eq, hb, hI.step (size_set_le _ _ _) (size_set_le _ _ _) ?_⟩
            rw [FMap.restr_set, if_neg (by decide)]
            have := size_rem_le (FMap.restr Unknown (ROhandle.FRO.m.get g₂)) (G1.chandle.get g₂)
            change _ ≤ _ + ((FMap.fdom (FMap.restr Unknown (ROhandle.FRO.m.get g₂))).card : ℤ)
            omega
          case «then» =>
            equiv_seq 6 10 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §hy2{1} = §hy2{2} ∧
                §hy2{1} = §(localVarLens "x3" handle){1} ∧ §hy2{2} = §h{2} ∧
                (§x0{2}).2 = §(localVarLens "x3" capacity){2} ∧
                §(localVarLens "r" capacity){1} = §(localVarLens "c" capacity){2} ∧
                colEq §allGlobals{1} §allGlobals{2} ∧ §G1.bext{1} = §G1.bext{2} ∧
                inv_lt §G1.m{2} §G1.mi{2} (§C.c{1} + 1) §FRO.m{2} §ReSample_count{2} ∧
                FMap.in_dom_with §FRO.m{1} §hy2{1} Unknown)
            · equiv_rnd
              stmt_wp
              equiv_skip
              rintro g₁ g₂ x0 hx2 y t _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7,
                  e8, e9,
                e10⟩, hb, hI, hin⟩, hg⟩ a -
              rw [e9] at hI
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
              have hin' := hin hg.2
              col_rw
              rw [e5, e8] at hin'
              exact ⟨trivial, trivial, trivial, by col_eq, hb, hI, hin'⟩
            · stmt_wp
              stmt_wp{2} 1
              stmt_wp
              equiv_skip
              rintro g₁ g₂ x0 y hy2 x3 r _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨e1, e2,
                  e3, e4,
                e5, e6, e7, e8, e9, e10⟩, hb, hI, hin⟩
              refine ⟨cdistr_expected_one, fun a _ => ?_⟩
              rw [e9] at hI
              col_rw
              rw [e8] at hin
              have h1 : FMap.dom (FRO.m.get g₂) hy2 := hin.1
              have h2 : is_ ((FRO.m.get g₂).get hy2) Unknown := hin.2
              have hk := size_ge0 (FMap.restr Unknown (FRO.m.get g₂))
              have hR : ((FMap.fdom (G1.m.get g₂)).card : ℤ) < max_size ∧
                  ((FMap.fdom (G1.mi.get g₂)).card : ℤ) < max_size ∧
                  ReSample_count.get g₂ < max_size := by
                obtain ⟨hm, hmi, hc, hmax⟩ := hI
                exact ⟨by omega, by omega, by omega⟩
              simp only [h1, h2, hR, decide_true, Bool.not_true, Bool.false_or, if_true, and_self,
                FMap.mem_set, or_true, FMap.get_set_sameE, set_set_same, oget, Option.getD_some]
              refine ⟨trivial, by col_eq, by rw [hb, bext_eq],
                hI.step (size_set_le _ _ _) (size_set_le _ _ _) ?_⟩
              rw [FMap.restr_set, if_neg (by decide), size_rem,
                if_pos ((FMap.dom_restr _ _ _).mpr hin)]
              have := Finset.card_pos.mpr ⟨hy2,
                  (FMap.mem_fdom _ _).mpr ((FMap.dom_restr _ _ _).mpr hin)⟩
              omega

set_option maxHeartbeats 1000000 in
-- the inlined oracles' wp goals are large
/-- `S_fi_ext` for `S.f` (EC's `seq 2 3` first: `y2` sampled in both branches on the left, after
them
on the right). -/
theorem S_f_ext (hfr : GcolFresh ReSample_count) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ colEq g₁ g₂ ∧ G1.bext.get g₁ = G1.bext.get g₂ ∧
        inv_lt (G1.m.get g₂) (G1.mi.get g₂) (C.c.get g₁ + 1) (FRO.m.get g₂)
          (ReSample_count.get g₂))
      (Indifferentiability.DPRIMITIVE.f state (List block) block (Module.app G2.S RRO)).procedure
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Gext.S ReSample_count)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ colEq g₁ g₂ ∧ G1.bext.get g₁ = G1.bext.get g₂ ∧
        inv_le (G1.m.get g₂) (G1.mi.get g₂) (C.c.get g₁ + 1) (FRO.m.get g₂)
          (ReSample_count.get g₂)) := by
  gcol_disj hfr ReSample_count
  unfold Gext.S
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
      §G1.bext{1} = §G1.bext{2} ∧
      inv_lt §G1.m{2} §G1.mi{2} (§C.c{1} + 1) §FRO.m{2} §ReSample_count{2})
  · stmt_wp
    equiv_skip
    intro _ _ _ _ h
    exact h
  · equiv_if
    case guard =>
      rintro g₁ g₂ x _ ⟨rfl, ⟨-, -, -, e4, -⟩, -⟩
      rw [e4]
    case «else» =>
      stmt_wp
      equiv_skip
      rintro g₁ g₂ x _ ⟨⟨rfl, hE, hb, hI⟩, -⟩
      exact ⟨by rw [hE.2.2.2.1], hE, hb, hI.le⟩
    case «then» =>
      equiv_seq 12 12 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧ §y2{1} = §y2{2} ∧
          colEq §allGlobals{1} §allGlobals{2} ∧ §G1.bext{1} = §G1.bext{2} ∧
          inv_lt §G1.m{2} §G1.mi{2} (§C.c{1} + 1) §FRO.m{2} §ReSample_count{2})
      · equiv_if{1}
        case «then» =>
          equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧
              colEq §allGlobals{1} §allGlobals{2} ∧ §G1.bext{1} = §G1.bext{2} ∧
              inv_lt §G1.m{2} §G1.mi{2} (§C.c{1} + 1) §FRO.m{2} §ReSample_count{2})
          · equiv_if{2}
            case «then» =>
              stmt_wp
              equiv_rnd
              stmt_wp
              equiv_skip
              rintro g₁ g₂ x0 _ ⟨⟨⟨⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb, hI⟩, -⟩, -⟩,
                -⟩ a -
              rw [e9] at hI
              col_rw
              split_ifs <;> exact ⟨trivial, trivial, by col_eq, hb, hI⟩
            case «else» =>
              refine prhlStmt_pre prhlStmt_false ?_
              rintro σ₁ σ₂ ⟨⟨⟨⟨hx, ⟨-, -, e3, -⟩, -⟩, -⟩, h1⟩, h2⟩
              simp only [e3, hx, decide_eq_true_eq] at h1
              exact (of_decide_eq_false h2) h1
          · equiv_rnd
            equiv_skip
            exact fun _ _ _ _ _ _ h _ _ => h
        case «else» =>
          equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧
              colEq §allGlobals{1} §allGlobals{2} ∧ §G1.bext{1} = §G1.bext{2} ∧
              inv_lt §G1.m{2} §G1.mi{2} (§C.c{1} + 1) §FRO.m{2} §ReSample_count{2})
          · equiv_if{2}
            case «then» =>
              refine prhlStmt_pre prhlStmt_false ?_
              rintro σ₁ σ₂ ⟨⟨⟨⟨hx, ⟨-, -, e3, -⟩, -⟩, -⟩, h1⟩, h2⟩
              simp only [e3, hx, decide_eq_false_iff_not] at h1
              exact h1 (of_decide_eq_true h2)
            case «else» =>
              equiv_rnd
              equiv_skip
              rintro g₁ g₂ x0 _ ⟨⟨⟨⟨rfl, hE, hb, hI⟩, -⟩, -⟩, -⟩ a -
              exact ⟨by trivial, hE, hb, hI⟩
          · equiv_rnd
            equiv_skip
            exact fun _ _ _ _ _ _ h _ _ => h
      · equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧
            colEq §allGlobals{1} §allGlobals{2} ∧ §G1.bext{1} = §G1.bext{2} ∧
            inv_le §G1.m{2} §G1.mi{2} (§C.c{1} + 1) §FRO.m{2} §ReSample_count{2})
        · equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §hx2{1} = §hx2{2} ∧ §y{1} = §y{2} ∧ §t{1} = §t{2} ∧
              colEq §allGlobals{1} §allGlobals{2} ∧ §G1.bext{1} = §G1.bext{2} ∧
              inv_lt §G1.m{2} §G1.mi{2} (§C.c{1} + 1) §FRO.m{2} §ReSample_count{2} ∧
              (§t{1} = true → FMap.in_dom_with §FRO.m{1}
                (oget (FMap.get §G1.mh{1} ((§x0{1}).1, §hx2{1}))).2 Unknown))
          · equiv_seq 3 3 : (§x0{1} = §x0{2} ∧ §hx2{1} = §hx2{2} ∧ §y{1} = §y{2} ∧
                colEq §allGlobals{1} §allGlobals{2} ∧ §G1.bext{1} = §G1.bext{2} ∧
                inv_lt §G1.m{2} §G1.mi{2} (§C.c{1} + 1) §FRO.m{2} §ReSample_count{2})
            · stmt_wp
              equiv_skip
              rintro g₁ g₂ x0 y1 y2 _ _ _ ⟨rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩,
                hb, hI⟩
              rw [e9] at hI
              col_rw
              split_ifs
              · exact ⟨trivial, trivial, trivial, by col_eq, hb, inv_lt_set_known hI _ _⟩
              · exact ⟨trivial, trivial, trivial, by col_eq, hb, hI⟩
            · stmt_wp
              equiv_skip
              rintro g₁ g₂ x0 hx2 y _ _ _ ⟨rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩,
                hb, hI⟩
              rw [e9] at hI
              col_rw
              exact ⟨trivial, trivial, trivial, trivial, by col_eq, hb, hI,
                  fun h => of_decide_eq_true h⟩
          · equiv_if
            case guard =>
              rintro g₁ g₂ x0 hx2 y t _ _ _ _ ⟨rfl, rfl, rfl, rfl, ⟨-, -, -, -, -, -, e7, -⟩, -⟩
              rw [e7]
            case «else» =>
              stmt_wp
              equiv_skip
              rintro g₁ g₂ x0 hx2 y t _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7,
                  e8, e9,
                e10⟩, hb, hI, -⟩, -⟩
              rw [e9] at hI
              col_rw
              refine ⟨trivial, trivial, by col_eq, hb,
                  hI.step (size_set_le _ _ _) (size_set_le _ _ _) ?_⟩
              rw [FMap.restr_set, if_neg (by decide)]
              have := size_rem_le (FMap.restr Unknown (ROhandle.FRO.m.get g₂)) (G1.chandle.get g₂)
              change _ ≤ _ + ((FMap.fdom (FMap.restr Unknown (ROhandle.FRO.m.get g₂))).card : ℤ)
              omega
            case «then» =>
              equiv_seq 6 10 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §hy2{1} = §hy2{2} ∧
                  §hy2{1} = §(localVarLens "x4" handle){1} ∧ §hy2{2} = §h{2} ∧
                  (§x0{2}).2 = §(localVarLens "x4" capacity){2} ∧
                  §r0{1} = §(localVarLens "c" capacity){2} ∧
                  colEq §allGlobals{1} §allGlobals{2} ∧ §G1.bext{1} = §G1.bext{2} ∧
                  inv_lt §G1.m{2} §G1.mi{2} (§C.c{1} + 1) §FRO.m{2} §ReSample_count{2} ∧
                  FMap.in_dom_with §FRO.m{1} §hy2{1} Unknown)
              · equiv_rnd
                stmt_wp
                equiv_skip
                rintro g₁ g₂ x0 hx2 y t _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6,
                    e7, e8, e9,
                  e10⟩, hb, hI, hin⟩, hg⟩ a -
                rw [e9] at hI
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
                have hin' := hin hg.2
                col_rw
                rw [e7, e8] at hin'
                exact ⟨trivial, trivial, trivial, by col_eq, hb, hI, hin'⟩
              · stmt_wp
                stmt_wp{2} 1
                stmt_wp
                equiv_skip
                rintro g₁ g₂ x0 y hy2 x4 r _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨e1,
                    e2, e3,
                  e4, e5, e6, e7, e8, e9, e10⟩, hb, hI, hin⟩
                refine ⟨cdistr_expected_one, fun a _ => ?_⟩
                rw [e9] at hI
                col_rw
                rw [e8] at hin
                have h1 : FMap.dom (FRO.m.get g₂) hy2 := hin.1
                have h2 : is_ ((FRO.m.get g₂).get hy2) Unknown := hin.2
                have hk := size_ge0 (FMap.restr Unknown (FRO.m.get g₂))
                have hR : ((FMap.fdom (G1.m.get g₂)).card : ℤ) < max_size ∧
                    ((FMap.fdom (G1.mi.get g₂)).card : ℤ) < max_size ∧
                    ReSample_count.get g₂ < max_size := by
                  obtain ⟨hm, hmi, hc, hmax⟩ := hI
                  exact ⟨by omega, by omega, by omega⟩
                simp only [h1, h2, hR, decide_true, Bool.not_true, Bool.false_or, if_true, and_self,
                  FMap.mem_set, or_true, FMap.get_set_sameE, set_set_same, oget, Option.getD_some]
                refine ⟨trivial, trivial, by col_eq, by rw [hb, bext_eq],
                  hI.step (size_set_le _ _ _) (size_set_le _ _ _) ?_⟩
                rw [FMap.restr_set, if_neg (by decide), size_rem,
                  if_pos ((FMap.dom_restr _ _ _).mpr hin)]
                have := Finset.card_pos.mpr
                  ⟨hy2, (FMap.mem_fdom _ _).mpr ((FMap.dom_restr _ _ _).mpr hin)⟩
                omega
        · stmt_wp
          equiv_skip
          rintro g₁ g₂ x0 y _ _ ⟨rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb, hI⟩
          rw [e9] at hI
          col_rw
          split_ifs <;> exact ⟨trivial, by col_eq, hb, hI⟩

/-- `inv_le` at a larger budget (below `max_size`). -/
theorem inv_le.mono {m2 mi2 : smap} {c1 c1' : ℤ} {Fm2 : handles} {count2 : ℤ}
    (h : inv_le m2 mi2 c1 Fm2 count2) (hc : c1 ≤ c1') (hc' : c1' ≤ max_size) :
    inv_le m2 mi2 c1' Fm2 count2 := by
  obtain ⟨h1, h2, h3, -⟩ := h
  exact ⟨by omega, by omega, by omega, hc'⟩

/-- `FRO.sample` adds at most one unknown handle. -/
theorem card_restr_sample (F : handles) (x : handle) (c : capacity) :
    ((FMap.fdom (FMap.restr Unknown
        (if FMap.dom F x then F else FMap.set F x (c, Unknown)))).card : ℤ) ≤
      (FMap.fdom (FMap.restr Unknown F)).card + 1 := by
  split_ifs
  · omega
  · rw [FMap.restr_set_eq]; exact size_set_le _ _ _

set_option maxHeartbeats 4000000 in
-- the inlined oracles' wp goals are large
/-- EC's `M.f` step in `EG2_Gext`: the loop with `inv_le` at the budget `C.c - qcost + counter`
(`DFRestr` charges `qcost` before the call), each counted step adding at most an unknown handle. -/
theorem M_f_ext (hfr : GcolFresh ReSample_count) :
    prhlProc (sig₁ := procsig (List block) -> block) (sig₂ := procsig (List block) -> block)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ colEq g₁ g₂ ∧ G1.bext.get g₁ = G1.bext.get g₂ ∧
        inv_le (G1.m.get g₂) (G1.mi.get g₂) (C.c.get g₁ - qcost a₁ g₁) (FRO.m.get g₂)
          (ReSample_count.get g₂) ∧ C.c.get g₁ ≤ max_size)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app G2.M RRO)).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block Gext.M).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ colEq g₁ g₂ ∧ G1.bext.get g₁ = G1.bext.get g₂ ∧
        inv_le (G1.m.get g₂) (G1.mi.get g₂) (C.c.get g₁) (FRO.m.get g₂)
          (ReSample_count.get g₂)) := by
  gcol_disj hfr ReSample_count
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_while (§p{1} = §p{2} ∧ §h{1} = §h{2} ∧ §i{1} = §i{2} ∧ §sa{1} = §sa{2} ∧
      §counter{1} = §counter{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
      §G1.bext{1} = §G1.bext{2} ∧ 0 ≤ §counter{2} ∧ §counter{2} ≤ (size §p{2}
          - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2})))) ∧
      inv_le §G1.m{2} §G1.mi{2} (§C.c{2} - (size §p{2}
          - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2})))) +
              §counter{2}) §FRO.m{2} §ReSample_count{2} ∧ §C.c{2} ≤ max_size)
  case body =>
    stmt_wp
    equiv_if
    case guard =>
      rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, hE, -⟩, -⟩
      rw [hE.2.2.2.2.2.2.1]
    case «then» =>
      stmt_wp
      equiv_skip
      rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, hE, rest⟩, -⟩, -⟩
      rw [hE.2.2.2.2.2.2.1]
      exact ⟨rfl, rfl, rfl, rfl, rfl, hE, rest⟩
    case «else» =>
      equiv_if
      case guard =>
        rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, hE, -⟩, -⟩, -⟩
        rw [hE.2.2.2.2.2.2.2.2.2]
      case «else» =>
        equiv_skip
        rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rest⟩, -⟩, -⟩, -⟩
        exact ⟨rfl, rfl, rfl, rfl, rfl, rest⟩
      case «then» =>
        equiv_seq 11 11 : (§p{1} = §p{2} ∧ §h{1} = §h{2} ∧ §i{1} = §i{2} ∧ §sa{1} = §sa{2} ∧
              §counter{1} = §counter{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
              §G1.bext{1} = §G1.bext{2} ∧ 0 ≤ §counter{2} ∧ §counter{2} < (size §p{2}
                - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2})))) ∧
              inv_le §G1.m{2} §G1.mi{2} (§C.c{2} - (size §p{2}
                - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2})))) +
                  §counter{2} + 1) §FRO.m{2} §ReSample_count{2} ∧ §C.c{2} ≤ max_size)
        · stmt_wp
          equiv_rnd
          stmt_wp
          equiv_skip
          rintro σ₁ σ₂ ⟨⟨⟨⟨hp, hh, hi, hsa, hc, hE, hb, h0, hle, hI, hm⟩, -⟩, -⟩, hlt⟩ a -
          simp only [colEq] at hE
          obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hE
          simp only [decide_eq_true_eq] at hlt
          simp only [hp, hc, e10] at hlt
          simp only [hp, hh, hi, hsa, hc]
          by_cases hd : FMap.dom (FRO.m.get σ₂.globals) (G1.chandle.get σ₂.globals)
          · have hd1 : FMap.dom (FRO.m.get σ₁.globals) (G1.chandle.get σ₁.globals) := by
              rw [e8, e6]; exact hd
            simp only [hd, hd1, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
            exact ⟨by trivial, by trivial, by trivial, by trivial, by trivial, by col_eq, hb, h0,
                hlt,
              hI.mono (by omega) (by omega), hm⟩
          · have hd1 : ¬ FMap.dom (FRO.m.get σ₁.globals) (G1.chandle.get σ₁.globals) := by
              rw [e8, e6]; exact hd
            simp only [hd, hd1, decide_false, Bool.not_false, if_true]
            col_rw
            refine ⟨by trivial, by trivial, by trivial, by trivial, by trivial, by col_eq, hb,
                h0, hlt,
              ?_, hm⟩
            obtain ⟨h1, h2, h3, h4⟩ := hI
            have := card_restr_sample (FRO.m.get σ₂.globals) (G1.chandle.get σ₂.globals) a
            rw [if_neg hd] at this
            simp only [FRO.m] at h3 this ⊢
            exact ⟨by omega, by omega, by omega, by omega⟩
        · stmt_wp
          equiv_rnd
          stmt_wp
          equiv_skip
          rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6,
              e7, e8,
            e9, e10⟩, hb, h0, hlt, hI, hm⟩ a -
          col_rw
          split_ifs <;> exact ⟨by trivial, by trivial, by trivial, by trivial, by trivial,
              by col_eq, hb, by omega, by omega, by simpa [add_assoc] using hI, hm⟩
  case guard =>
    rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, -⟩
    rfl
  case exit =>
    rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9,
      e10⟩, hb, h0, hle, hI, hm⟩ - a -
    col_rw
    split_ifs <;> exact ⟨by trivial, by col_eq, hb, hI.mono (by omega) hm⟩
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x _ ⟨rfl, hE, hb, hI, hm⟩
  have e9 : C.c.get g₁ = C.c.get g₂ := hE.2.2.2.2.2.2.2.2.1
  have e10 : C.queries.get g₁ = C.queries.get g₂ := hE.2.2.2.2.2.2.2.2.2
  unfold qcost at hI
  rw [e9, e10] at hI
  rw [e9] at hm
  have := prefix_sizel x (get_max_prefix x (elems (FMap.fdom (C.queries.get g₂))))
  exact ⟨rfl, hE, hb, by omega, by simpa using hI, hm⟩

/-- The invariant of EC's `call (_: ={F.RO.m, FRO.m, G1.paths, G1.mh, G1.mhi, G1.m, G1.mi,
G1.chandle,
G1.bext, C.c, C.queries} /\ inv_le G1.m{2} G1.mi{2} C.c{1} FRO.m{2} ReSample.count{2})` in
`EG2_Gext`. -/
def extInv (g₁ g₂ : VariableAssignment) : Prop :=
  colEq g₁ g₂ ∧ G1.bext.get g₁ = G1.bext.get g₂ ∧
    inv_le (G1.m.get g₂) (G1.mi.get g₂) (C.c.get g₁) (FRO.m.get g₂) (ReSample_count.get g₂)

/-- `inv_le` at `c` gives `inv_lt` at `c + 1` (`DPRestr`'s guard, EC's `swap -1`). -/
theorem inv_le.lt_succ {m2 mi2 : smap} {c1 : ℤ} {Fm2 : handles} {count2 : ℤ}
    (h : inv_le m2 mi2 c1 Fm2 count2) (hc : c1 + 1 ≤ max_size) :
    inv_lt m2 mi2 (c1 + 1) Fm2 count2 := by
  obtain ⟨h1, h2, h3, -⟩ := h
  exact ⟨by omega, by omega, by omega, hc⟩

set_option maxHeartbeats 1000000 in
-- the inlined oracles' wp goals are large
/-- `DPRestr(S).fi` under `extInv` (`S_fi_ext`). -/
theorem DPRestr_fi_ext (hfr : GcolFresh ReSample_count) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ extInv ReSample_count g₁ g₂)
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr (Module.app G2.S RRO))).procedure
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr (Gext.S ReSample_count))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ extInv ReSample_count g₁ g₂) := by
  gcol_disj hfr ReSample_count
  unfold extInv
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
      §G1.bext{1} = §G1.bext{2} ∧
      inv_le §G1.m{2} §G1.mi{2} §C.c{1} §FRO.m{2} §ReSample_count{2})
  · stmt_wp
    equiv_skip
    intro _ _ _ _ h
    exact h
  · equiv_if
    case guard =>
      rintro g₁ g₂ _ _ _ _ ⟨-, -, hE, -⟩
      rw [hE.2.2.2.2.2.2.2.2.1]
    case «then» =>
      stmt_wp
      equiv_call (S_fi_ext ReSample_count hfr)
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨rfl, rfl, hE, hb, hI⟩, hg⟩
      simp only [decide_eq_true_eq] at hg
      refine ⟨⟨rfl, hE, hb, hI.lt_succ hg⟩, ?_⟩
      rintro r g₁' _ g₂' ⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb', hI'⟩
      exact ⟨rfl, by col_eq, hb', hI'⟩
    case «else» =>
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨-, rfl, rest⟩, -⟩
      exact ⟨rfl, rest⟩

set_option maxHeartbeats 1000000 in
-- the inlined oracles' wp goals are large
/-- `DPRestr(S).f` under `extInv` (`S_f_ext`). -/
theorem DPRestr_f_ext (hfr : GcolFresh ReSample_count) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ extInv ReSample_count g₁ g₂)
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr (Module.app G2.S RRO))).procedure
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr (Gext.S ReSample_count))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ extInv ReSample_count g₁ g₂) := by
  gcol_disj hfr ReSample_count
  unfold extInv
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
      §G1.bext{1} = §G1.bext{2} ∧
      inv_le §G1.m{2} §G1.mi{2} §C.c{1} §FRO.m{2} §ReSample_count{2})
  · stmt_wp
    equiv_skip
    intro _ _ _ _ h
    exact h
  · equiv_if
    case guard =>
      rintro g₁ g₂ _ _ _ _ ⟨-, -, hE, -⟩
      rw [hE.2.2.2.2.2.2.2.2.1]
    case «then» =>
      stmt_wp
      equiv_call (S_f_ext ReSample_count hfr)
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨rfl, rfl, hE, hb, hI⟩, hg⟩
      simp only [decide_eq_true_eq] at hg
      refine ⟨⟨rfl, hE, hb, hI.lt_succ hg⟩, ?_⟩
      rintro r g₁' _ g₂' ⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb', hI'⟩
      exact ⟨rfl, by col_eq, hb', hI'⟩
    case «else» =>
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨-, rfl, rest⟩, -⟩
      exact ⟨rfl, rest⟩

set_option maxHeartbeats 1000000 in
-- the inlined oracles' wp goals are large
/-- `DFRestr(M).f` under `extInv` (`M_f_ext`). -/
theorem DFRestr_f_ext (hfr : GcolFresh ReSample_count) :
    prhlProc (sig₁ := procsig (List block) -> block) (sig₂ := procsig (List block) -> block)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ extInv ReSample_count g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr (Module.app G2.M RRO))).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr Gext.M)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ extInv ReSample_count g₁ g₂) := by
  gcol_disj hfr ReSample_count
  unfold extInv
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§bs{1} = §bs{2} ∧ §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧
      colEq §allGlobals{1} §allGlobals{2} ∧ §G1.bext{1} = §G1.bext{2} ∧
      inv_le §G1.m{2} §G1.mi{2} §C.c{1} §FRO.m{2} §ReSample_count{2})
  · stmt_wp
    equiv_skip
    intro _ _ _ _ h
    exact h
  · equiv_if
    case guard =>
      rintro g₁ g₂ bs _ _ _ ⟨rfl, -, hE, -⟩
      rw [hE.2.2.2.2.2.2.2.2.2]
    case «else» =>
      stmt_wp
      equiv_skip
      rintro g₁ g₂ bs _ b _ ⟨⟨rfl, rfl, hE, rest⟩, -⟩
      rw [hE.2.2.2.2.2.2.2.2.2]
      exact ⟨rfl, hE, rest⟩
    case «then» =>
      equiv_if
      case guard =>
        rintro g₁ g₂ bs _ _ _ ⟨⟨rfl, -, hE, -⟩, -⟩
        rw [hE.2.2.2.2.2.2.2.2.1, hE.2.2.2.2.2.2.2.2.2]
      case «else» =>
        equiv_skip
        rintro g₁ g₂ bs _ b _ ⟨⟨⟨rfl, rfl, rest⟩, -⟩, -⟩
        exact ⟨rfl, rest⟩
      case «then» =>
        stmt_wp
        equiv_call (M_f_ext ReSample_count hfr)
        stmt_wp
        equiv_skip
        rintro g₁ g₂ bs _ b _ ⟨⟨⟨rfl, rfl, hE, hb, hI⟩, -⟩, hg⟩
        simp only [decide_eq_true_eq] at hg
        unfold qcost
        simp_reads
        obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hE
        refine ⟨⟨by col_eq, hb, ?_, hg⟩, ?_⟩
        · rw [show ∀ a b c : ℤ, a + b - c - (b - c) = a from fun a b c => by ring]
          exact hI
        · rintro r g₁' _ g₂' ⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb', hI'⟩
          exact ⟨rfl, by col_eq, hb', hI'⟩

set_option maxHeartbeats 4000000 in
-- the twelve-variable invariant and the oracles' footprint checks
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
  have hfr : GcolFresh ReSample_count :=
    _hfresh.trans (Footprint.compl_antimono (by
      unfold C.footprint
      iterate 11 refine sup_le ?_ ?_
      all_goals gcol_fp))
  gcol_disj hfr ReSample_count
  -- the variables of `G1`, `C`, `FRO` and `ReSample.count` lie outside `glob D`
  have hcc : (C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hcq : (C.queries).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hro : (F.RO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hfro : (FRO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  -- the oracles write `FRO.m` as `ROhandle.FRO.m` (`writes_keep'` matches syntactically)
  have hfro' : (ROhandle.FRO.m).footprint ≤ (FVP.fvP D)ᶜ := hfro
  have hm : (G1.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hmi : (G1.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hmh : (G1.mh).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hmhi : (G1.mhi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hch : (G1.chandle).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hpa : (G1.paths).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hbx : (G1.bext).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hgc : ReSample_count.footprint ≤ (FVP.fvP D)ᶜ :=
    _hfresh.trans (Footprint.compl_antimono (by gcol_fp))
  -- EC's invariant, on the values of the variables it reads
  let L := Lens.pair ReSample_count (Lens.pair C.c (Lens.pair C.queries (Lens.pair F.RO.m
    (Lens.pair FRO.m (Lens.pair G1.m (Lens.pair G1.mi (Lens.pair G1.mh (Lens.pair G1.mhi
      (Lens.pair G1.chandle (Lens.pair G1.paths G1.bext))))))))))
  let I : ℤ × ℤ × FMap (List block) block × FMap (List block) block ×
      FMap handle (capacity × flag) × smap × smap × hsmap × hsmap × ℤ ×
      FMap capacity (List block × block) × Bool →
      ℤ × ℤ × FMap (List block) block × FMap (List block) block ×
      FMap handle (capacity × flag) × smap × smap × hsmap × hsmap × ℤ ×
      FMap capacity (List block × block) × Bool → Prop := fun x y =>
    (x.2.2.2.1 = y.2.2.2.1 ∧ x.2.2.2.2.2.2.1 = y.2.2.2.2.2.2.1 ∧
      x.2.2.2.2.2.2.2.2.2.2.1 = y.2.2.2.2.2.2.2.2.2.2.1 ∧ x.2.2.2.2.2.1 = y.2.2.2.2.2.1 ∧
      x.2.2.2.2.2.2.2.2.1 = y.2.2.2.2.2.2.2.2.1 ∧ x.2.2.2.2.2.2.2.2.2.1 = y.2.2.2.2.2.2.2.2.2.1 ∧
      x.2.2.2.2.2.2.2.1 = y.2.2.2.2.2.2.2.1 ∧ x.2.2.2.2.1 = y.2.2.2.2.1 ∧ x.2.1 = y.2.1 ∧
      x.2.2.1 = y.2.2.1) ∧
    x.2.2.2.2.2.2.2.2.2.2.2 = y.2.2.2.2.2.2.2.2.2.2.2 ∧
    inv_le y.2.2.2.2.2.1 y.2.2.2.2.2.2.1 x.2.1 y.2.2.2.2.1 y.1
  have hI : ∀ g₁ g₂, I (L.get g₁) (L.get g₂) ↔ extInv ReSample_count g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (L.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [L, Footprint.lens_pair]
    exact sup_le hgc (sup_le hcc (sup_le hcq (sup_le hro (sup_le hfro (sup_le hm (sup_le hmi
      (sup_le hmh (sup_le hmhi (sup_le hch (sup_le hpa hbx))))))))))
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  repeat stmt_inline{1} 1
  repeat stmt_inline{2} 1
  stmt_wp
  equiv_seq 6 5 : (colEq §allGlobals{1} §allGlobals{2} ∧ §G1.bext{1} = §G1.bext{2} ∧
      inv_le §G1.m{2} §G1.mi{2} §C.c{1} §FRO.m{2} §ReSample_count{2})
  · equiv_seq 1 1 : (globInvF L (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
    · stmt_wp
      equiv_skip
      intro g₁ g₂ h
      refine ⟨?_, (hI _ _).mpr ?_⟩
      · simp only [touched_set_of_le_compl hcc, touched_set_of_le_compl hcq,
          touched_set_of_le_compl hro, touched_set_of_le_compl hfro', touched_set_of_le_compl hm,
          touched_set_of_le_compl hmi, touched_set_of_le_compl hmh, touched_set_of_le_compl hmhi,
          touched_set_of_le_compl hch, touched_set_of_le_compl hpa, touched_set_of_le_compl hbx,
          touched_set_of_le_compl hgc]
        exact h
      · simp only [extInv, colEq]
        simp_reads
        refine ⟨by simp, by simp, ?_, max_ge0⟩
        rw [FMap.restr_set, if_neg (by decide), FMap.restr0]
        simp
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
            (DFRestr_f_ext ReSample_count hfr)
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair]
            unfold Gext.S
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              (DPRestr_f_ext ReSample_count hfr)
          | succ n => cases n with
            | zero =>
              simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
                HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair]
              unfold Gext.S
              exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
                (DPRestr_fi_ext ReSample_count hfr)
            | succ n => nomatch n
      equiv_skip
      intro σ₁ σ₂ h
      refine ⟨⟨rfl, h⟩, ?_⟩
      rintro r g₁ _ g₂ ⟨rfl, -, hI'⟩
      have hc := (hI g₁ g₂).mp hI'
      simp_reads
      exact hc
  · equiv_while (§l{1} = §l{2} ∧ §FRO.m{1} = §FRO.m{2} ∧ §G1.m{1} = §G1.m{2} ∧
        §G1.mi{1} = §G1.mi{2} ∧ ((FMap.fdom §G1.m{2}).card : ℤ) ≤ max_size ∧
        ((FMap.fdom §G1.mi{2}).card : ℤ) ≤ max_size ∧
        §ReSample_count{2} + ((§l{2}).length : ℤ) ≤ max_size ∧
        ((§G1.bext{1} = true ∨ ∃ (x : state) (h : handle),
            x ∈ FMap.fdom §G1.m{1} ∪ FMap.fdom §G1.mi{1} ∧
            FMap.get §FRO.m{1} h = some (x.2, Unknown) ∧ h ∉ §l{1}) → §G1.bext{2} = true))
    case body =>
      stmt_wp
      equiv_rnd
      stmt_wp
      equiv_skip
      rintro σ₂ l m mm mi b ⟨⟨rfl, rfl, rfl, rfl, hcm, hcmi, hn, hb⟩, hne⟩ a -
      generalize (localVarLens "l" (List handle)).get σ₂ = L at *
      cases L with
      | nil => simp at hne
      | cons hd tl =>
        have hg : ((FMap.fdom (G1.m.get σ₂.globals)).card : ℤ) ≤ max_size ∧
            ((FMap.fdom (G1.mi.get σ₂.globals)).card : ℤ) ≤ max_size ∧
            ReSample_count.get σ₂.globals < max_size := by
          simp only [List.length_cons] at hn
          exact ⟨hcm, hcmi, by omega⟩
        simp only [hg, and_self, decide_true, if_true, head]
        refine ⟨trivial, trivial, trivial, trivial, trivial, trivial,
          ?_, ?_⟩
        · change _ + 1 + ((tl.length : ℕ) : ℤ) ≤ _
          simp only [List.length_cons] at hn
          push_cast at hn
          omega
        rintro (h | ⟨x, h, hx, hget, hnot⟩)
        · simp [hb (Or.inl h)]
        · change h ∉ tl at hnot
          change ((FRO.m.get σ₂.globals).set hd (a, Unknown)).get h = some (x.2, Unknown) at hget
          by_cases hh : h = hd
          · subst hh
            rw [FMap.get_set_sameE] at hget
            simp only [Option.some.injEq, Prod.mk.injEq] at hget
            have : a ∈ Finset.image Prod.snd (FMap.fdom (G1.m.get σ₂.globals) ∪
                FMap.fdom (G1.mi.get σ₂.globals)) := Finset.mem_image.mpr ⟨x, hx, hget.1.symm⟩
            simp [this]
          · rw [FMap.get_set_neqE _ _ _ _ hh] at hget
            have := hb (Or.inr ⟨x, h, hx, hget, by simp [hh, hnot]⟩)
            simp [this]
    case guard =>
      rintro l m mm mi b _ _ _ _ _ _ ⟨rfl, -⟩
      rfl
    case exit =>
      rintro l m mm mi b _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, -, -, hn, hb⟩ hl
      simp only [Bool.not_eq_false', List.isEmpty_iff] at hl
      subst hl
      refine ⟨by simpa using hn, ?_⟩
      rintro (h | ⟨x, h, hx, hget⟩)
      · exact hb (Or.inl h)
      · exact hb (Or.inr ⟨x, h, hx, hget, List.not_mem_nil⟩)
    stmt_wp
    equiv_skip
    rintro g₁ g₂ ⟨⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb, h1, h2, h3, h4⟩
    have hk := size_ge0 (FMap.restr Unknown (FRO.m.get g₂))
    refine ⟨by rw [← e8], e8, e4, e2, by omega, by omega,
      by simp only [Finset.length_toList]; omega, ?_⟩
    rintro (h | ⟨x, h, -, hget, hnot⟩)
    · rw [← hb]; exact h
    · exfalso
      apply hnot
      rw [Finset.mem_toList, FMap.mem_fdom, FMap.dom_restr]
      refine ⟨by rw [FMap.domE, hget]; simp, by rw [hget]; rfl⟩

/-- EC's `Real_G2`, with the axiom `D_ll`. -/
theorem Real_G2 (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (F.RO.m).footprint ⊔ (Redo.prefixes).footprint ⊔ (FRO.m).footprint ⊔
      (ROhandle.RO.m).footprint)ᶜ)
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
  have h1 := Real_G1 D hD (_hDd.trans (Footprint.compl_antimono (by fp_sub))) G
    (_hGd.trans (Footprint.compl_antimono (by fp_sub))) GF hGF hGGF D_ll m
  have h2 : Procedure.Pr (G1 (DRestr D)).procedure () m (fun r _ => r = true) =
      Procedure.Pr (Eager.main2 (G2 (DRestr D))).procedure () m (fun r _ => r = true) :=
    (Procedure.Pr_eq_of_prhlProc hG1G2 (fun _ _ _ _ h => by rw [h.1]) (a₂ := ()) rfl).trans
      (heq _).symm
  have h3 := Pr_G1col D hD (_hDd.trans (Footprint.compl_antimono (by fp_sub))) G
    (_hGd.trans (Footprint.compl_antimono (by fp_sub))) D_ll m
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
  have h5 := Pr_ext RC D hD hc _hDd G _hGd D_ll m
  have h4' : (Procedure.Pr (G1 (DRestr D)).procedure () m (fun _ g => G1.bext.get g = true) : ℝ) ≤
      _ := (NNReal.coe_le_coe.mpr h4).trans h5
  rw [h2] at h1
  refine h1.trans (le_of_le_of_eq (add_le_add (add_le_add le_rfl h3) h4') ?_)
  ring

end EXT

end GaudisCrypt.SHA3.Gext
