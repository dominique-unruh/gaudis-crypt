import GaudisCrypt.Examples.SHA3.SmartCounter.Handle
import GaudisCrypt.Logic.ExpectationFrame

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
  positivity

theorem c_ge0r : (0 : ℝ) ≤ ((2 ^ c.toNat : ℤ) : ℝ) := by
  positivity

theorem eps_ge0 : (0 : ℝ) ≤ ((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ) := by
  have := max_ge0
  exact div_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ 2 * max_size)) c_ge0r

/-- `mu1 cdistr x = 1 / 2^c`. -/
theorem cdistr1E (x : capacity) : cdistr.1 {x} = 1 / (2 ^ c.toNat : ENNReal) := by
  letI : MeasurableSpace capacity := ⊤
  change (PMF.uniformOfFintype capacity).toMeasure {x} = _
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x)]
  simp [capacity, BitWord.word, card_vector]

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
  have hsub : FMap.frng (FMap.set m x y) ⊆ insert y (FMap.frng m) := by
    intro b hb
    rw [FMap.mem_frng, FMap.rngE] at hb
    obtain ⟨a, ha⟩ := hb
    rw [FMap.get_setE] at ha
    split_ifs at ha with hax
    · simp at ha; simp [ha]
    · exact Finset.mem_insert_of_mem ((FMap.mem_frng _ _).mpr ⟨a, ha⟩)
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

theorem hinv_image (handles : handles) (c : capacity) :
    hinv handles c ≠ none → c ∈ Finset.image Prod.fst (FMap.frng handles) := by
  intro hn
  have hP := hinvP handles c
  rw [if_neg hn] at hP
  obtain ⟨f, hf⟩ := hP
  exact Finset.mem_image.mpr ⟨(c, f), (FMap.mem_frng _ _).mpr ⟨_, hf⟩, rfl⟩

/-- EC's `fel` bound per sample, `2 max_size / 2^c`. -/
noncomputable def gcolEps : ENNReal := ((2 * max_size).toNat : ENNReal) / (2 ^ c.toNat : ENNReal)

/-- The potential of EC's `fel` in `Pr_col`, on `(G1.bcol, Gcol.count)`: the bad event, plus
`gcolEps` for each sample still allowed. -/
noncomputable def gcolPotential (x : Bool × ℤ) : ENNReal :=
  (if x.1 then 1 else 0) + gcolEps * ((max_size - x.2).toNat : ENNReal)

omit [SLCommon.Params] in
private theorem expected_mono_le {γ : Type} {μ : SubProbability γ} {f g : γ → ENNReal}
    (h : ∀ a, f a ≤ g a) : μ.expected f ≤ μ.expected g := by
  rw [SubProbability.expected_eq_tsum, SubProbability.expected_eq_tsum]
  exact ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

omit [SLCommon.Params] in
private theorem expected_const_le_self {γ : Type} (μ : SubProbability γ) (c : ENNReal) :
    μ.expected (fun _ => c) ≤ c := by
  letI : MeasurableSpace γ := ⊤
  change ∫⁻ _, c ∂μ.1 ≤ c
  rw [MeasureTheory.lintegral_const]
  calc c * μ.1 Set.univ ≤ c * 1 := by gcongr; exact μ.2.1
    _ = c := mul_one c

/-- EC's `Mu_mem.mu_mem` for `cdistr`: a set of capacities has probability `card S / 2^c`. -/
theorem cdistr_expected_mem (S : Finset capacity) :
    cdistr.expected (fun a => if a ∈ S then (1 : ENNReal) else 0) =
      (S.card : ENNReal) * (1 / (2 ^ c.toNat : ENNReal)) := by
  rw [SubProbability.expected_eq_tsum]
  calc ∑' a, (if a ∈ S then (1 : ENNReal) else 0) * cdistr.1 {a}
      = ∑' a, if a ∈ S then cdistr.1 {a} else 0 := tsum_congr fun a => by split_ifs <;> simp
    _ = ∑ a ∈ S, cdistr.1 {a} := by
        rw [tsum_eq_sum (s := S) (fun a ha => by simp [ha])]
        exact Finset.sum_congr rfl fun a ha => by simp [ha]
    _ = _ := by rw [Finset.sum_congr rfl fun a _ => cdistr1E a, Finset.sum_const, nsmul_eq_mul]

/-- One sample of `Gcol.sample_c` under its guard does not increase `gcolPotential` (EC's
`rnd (mem (image fst (frng FRO.m)))` and `Mu_mem.mu_mem`). -/
theorem gcolPotential_step (S : Finset capacity) (b : Bool) (n : ℤ)
    (hS : (S.card : ℤ) ≤ 2 * max_size) (hn : n < max_size) :
    cdistr.expected (fun a => gcolPotential (b || decide (a ∈ S), n + 1)) ≤
      gcolPotential (b, n) := by
  have hk : ((max_size - n).toNat : ENNReal) = ((max_size - (n + 1)).toNat : ENNReal) + 1 := by
    rw [show (max_size - n).toNat = (max_size - (n + 1)).toNat + 1 by omega]; push_cast; rfl
  cases b with
  | true =>
    refine (expected_mono_le fun a => ?_).trans (expected_const_le_self cdistr _)
    simp only [gcolPotential, Bool.true_or, if_true]
    gcongr
    exact_mod_cast (show (max_size - (n + 1)).toNat ≤ (max_size - n).toNat by omega)
  | false =>
    simp only [gcolPotential, Bool.false_or, decide_eq_true_eq, Bool.false_eq_true, if_false,
      zero_add]
    calc cdistr.expected (fun a => (if a ∈ S then (1 : ENNReal) else 0) +
          gcolEps * ((max_size - (n + 1)).toNat : ENNReal))
        = cdistr.expected (fun a => if a ∈ S then (1 : ENNReal) else 0) +
            cdistr.expected (fun _ => gcolEps * ((max_size - (n + 1)).toNat : ENNReal)) :=
          SubProbability.expected_add _ _ _
      _ ≤ gcolEps + gcolEps * ((max_size - (n + 1)).toNat : ENNReal) := by
          refine add_le_add ?_ (expected_const_le_self cdistr _)
          rw [cdistr_expected_mem, gcolEps, ← div_eq_mul_one_div]
          exact ENNReal.div_le_div_right
            (by exact_mod_cast (show S.card ≤ (2 * max_size).toNat by omega)) _
      _ = gcolEps * ((max_size - n).toNat : ENNReal) := by rw [hk, mul_add, mul_one, add_comm]

theorem sample_c_potential [Lens.Disjoint G1.bcol Gcol_count] :
    phoareProc (fun _ _ => True) (Gcol.sample_c Gcol_count).procedure
      (fun _ g => gcolPotential ((Lens.pair G1.bcol Gcol_count).get g)) (· ≤ ·)
      (fun _ g => gcolPotential ((Lens.pair G1.bcol Gcol_count).get g)) := by
  haveI := (inferInstance : Lens.Disjoint G1.bcol Gcol_count).symm
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  split_ifs with h
  · exact gcolPotential_step _ _ _ h.1 h.2
  · exact le_rfl

section PROOF

variable (D : DISTINGUISHER)

/-- EC's `fel 10 Gcol.count (fun x=> (2*max_size)%r / (2^c)%r) max_size G1.bcol
[Gcol.sample_c : …]` in `Pr_col`, as a supermartingale: `Gcol.main` ends with `gcolPotential` at
most `max_size · 2 max_size / 2^c` (`Module.ewp_app_le`; the oracles of `DRestr(D)` change
`(G1.bcol, Gcol.count)` only through `Gcol.sample_c`, `sample_c_potential`, which `exp_decr`
checks syntactically). -/
theorem Gcol_potential [Lens.Disjoint G1.bcol Gcol_count] (hD : Module.ECModule D distExt)
    (_hfresh : Gcol_count.footprint ≤ (FVP.fvP D ⊔ C.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint ⊔ (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔
      (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint)ᶜ)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint)ᶜ) :
    phoareProc (fun _ _ => True) (Gcol Gcol_count D).procedure
      (fun _ g => gcolPotential ((Lens.pair G1.bcol Gcol_count).get g)) (· ≤ ·)
      (fun _ _ => gcolEps * (max_size.toNat : ENNReal)) := by
  unfold C.footprint at _hfresh _hDd
  have hL : (Lens.pair G1.bcol Gcol_count).footprint = G1.bcol.footprint ⊔ Gcol_count.footprint :=
    Footprint.lens_pair _ _
  -- the oracles' writes are outside `(G1.bcol, Gcol.count)`
  have h1 : (C.c).footprint ≤ ((Lens.pair G1.bcol Gcol_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h2 : (C.queries).footprint ≤ ((Lens.pair G1.bcol Gcol_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h3 : (G1.m).footprint ≤ ((Lens.pair G1.bcol Gcol_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h4 : (G1.mi).footprint ≤ ((Lens.pair G1.bcol Gcol_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h5 : (G1.mh).footprint ≤ ((Lens.pair G1.bcol Gcol_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h6 : (G1.mhi).footprint ≤ ((Lens.pair G1.bcol Gcol_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h7 : (G1.chandle).footprint ≤ ((Lens.pair G1.bcol Gcol_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h8 : (G1.paths).footprint ≤ ((Lens.pair G1.bcol Gcol_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h9 : (FRO.m).footprint ≤ ((Lens.pair G1.bcol Gcol_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have h10 : (F.RO.m).footprint ≤ ((Lens.pair G1.bcol Gcol_count).footprint)ᶜ := by
    rw [hL]; fp_disjoint
  have hDL : FVP.fvP D ≤ ((Lens.pair G1.bcol Gcol_count).footprint)ᶜ := by
    rw [hL]
    refine (Footprint.le_compl_comm _ _).mpr (sup_le ?_ ?_)
    · exact (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono
        (by repeat (first | exact le_rfl | exact le_sup_right | apply le_sup_of_le_left))))
    · exact _hfresh.trans (Footprint.compl_antimono
        (by repeat (first | exact le_rfl | apply le_sup_of_le_left)))
  phoare_proc_to_stmt
  phoare_inline 0
  repeat phoare_inline 0
  intro σ _
  simp only [Stmt.ewp_seq, Stmt.ewp_assign]
  simp_reads
  erw [Stmt.ewp_call]
  simp_reads
  have hsc : ∀ a g, Procedure.ewp (Gcol.sample_c Gcol_count).procedure a
      (fun _ g' => gcolPotential ((Lens.pair G1.bcol Gcol_count).get g')) g ≤
        gcolPotential ((Lens.pair G1.bcol Gcol_count).get g) :=
    fun a g => sample_c_potential Gcol_count a g trivial
  refine le_trans (Module.ewp_app_le (Lens.pair G1.bcol Gcol_count) D distExt hD.representable hDL
    (fun n => by cases n with
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
        unfold Gcol.S
        exact Procedure.ewp_le_of_expDecr _ _ _ (by exp_decr) a g
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair]
          unfold Gcol.S
          exact Procedure.ewp_le_of_expDecr _ _ _ (by exp_decr) a g
        | succ n => nomatch n
  · have hC : C.c.footprint ⊔ C.queries.footprint ≤ (FVP.fvP D ⊔ (C.c.footprint ⊔
        C.queries.footprint) ⊔ F.RO.m.footprint ⊔ FRO.m.footprint ⊔ G1.m.footprint ⊔
        G1.mi.footprint ⊔ G1.mh.footprint ⊔ G1.mhi.footprint ⊔ G1.chandle.footprint ⊔
        G1.paths.footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint) := by
      iterate 10 apply le_sup_of_le_left
      exact le_sup_right
    haveI : Lens.Disjoint C.c Gcol_count := Lens.disjoint_of_footprint_le_compl _ _
      ((Footprint.le_compl_comm _ _).mp
        (_hfresh.trans (Footprint.compl_antimono (le_sup_left.trans hC))))
    haveI : Lens.Disjoint C.queries Gcol_count := Lens.disjoint_of_footprint_le_compl _ _
      ((Footprint.le_compl_comm _ _).mp
        (_hfresh.trans (Footprint.compl_antimono (le_sup_right.trans hC))))
    haveI := (inferInstance : Lens.Disjoint G1.bcol Gcol_count).symm
    simp only [Lens.pair, Lens.set_get, Lens.get_of_disjoint_set, gcolPotential,
      Bool.false_eq_true, if_false, zero_add, sub_zero, le_refl]

/-- `local lemma Pr_col`, for `declare module D <: DISTINGUISHER {-C, -PF, -G1}` with `D_ll`. -/
theorem Pr_col (hD : Module.ECModule D distExt)
    (_hfresh : Gcol_count.footprint ≤ (FVP.fvP D ⊔ C.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint ⊔ (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔
      (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint)ᶜ)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D).globᶜ →
      FVP.fvP P ≤ (FVP.fvP D).globᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (m : VariableAssignment) :
    (Procedure.Pr (Gcol Gcol_count D).procedure () m
        (fun _ g => G1.bcol.get g = true ∧ Gcol_count.get g ≤ max_size) : ℝ) ≤
      (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) := by
  -- EC: `fel 10 Gcol.count … [Gcol.sample_c : …]`, as the supermartingale `Gcol_potential`
  haveI : Lens.Disjoint G1.bcol Gcol_count := Lens.disjoint_of_footprint_le_compl _ _
    ((Footprint.le_compl_comm _ _).mp (_hfresh.trans (Footprint.compl_antimono le_sup_right)))
  have hE : (Procedure.Pr (Gcol Gcol_count D).procedure () m
      (fun _ g => G1.bcol.get g = true ∧ Gcol_count.get g ≤ max_size) : ENNReal) ≤
      gcolEps * (max_size.toNat : ENNReal) := by
    rw [Procedure.Pr_eq_ewp]
    refine (Procedure.ewp_mono _ _ (G := fun _ g =>
      gcolPotential ((Lens.pair G1.bcol Gcol_count).get g)) (fun _ g => ?_) _).trans
      (Gcol_potential Gcol_count D hD _hfresh _hDd () m trivial)
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

/-- `local equiv G1_col : G1(DRestr(D)).main ~ Gcol.main : ={glob D} ==>
(G1.bcol{1} => G1.bcol{2}) /\ Gcol.count{2} <= max_size`. -/
theorem G1_col (hD : Module.ECModule D distExt)
    (_hfresh : Gcol_count.footprint ≤ (FVP.fvP D ⊔ C.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint ⊔ (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔
      (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint)ᶜ)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D).globᶜ →
      FVP.fvP P ≤ (FVP.fvP D).globᶜ →
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
theorem Pr_G1col (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D).globᶜ →
      FVP.fvP P ≤ (FVP.fvP D).globᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (m : VariableAssignment) :
    (Procedure.Pr (G1 (DRestr D)).procedure () m (fun _ g => G1.bcol.get g = true) : ℝ) ≤
      (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) := by
  -- the local module `Gcol`'s variable `count`, fresh (exception E6)
  have hF : (FVP.fvP D ⊔ C.footprint ⊔ (F.RO.m).footprint ⊔ (FRO.m).footprint ⊔
      (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔
      G1.bcol.footprint).FinitelySupported := by
    unfold C.footprint
    repeat (first | exact hD.finitelySupported | exact .varLens _ | refine .sup ?_ ?_)
  obtain ⟨Gcol_count, hc, -⟩ := Footprint.exists_fresh ℤ hF
  -- EC: `apply (ler_trans Pr[Gcol.main()@&m : G1.bcol /\ Gcol.count <= max_size])`,
  -- `byequiv G1_col=> //#` and `apply (Pr_col &m)`
  refine le_trans ?_ (Pr_col Gcol_count D hD hc _hDd D_ll m)
  exact_mod_cast Procedure.Pr_le_of_prhlProc (G1_col Gcol_count D hD hc _hDd D_ll)
    (E₁ := fun _ g => G1.bcol.get g = true)
    (E₂ := fun _ g => G1.bcol.get g = true ∧ Gcol_count.get g ≤ max_size)
    (fun _ _ _ _ h h1 => ⟨h.1 h1, h.2⟩) (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl

end PROOF

end GaudisCrypt.SHA3.Gcol
