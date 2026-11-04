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

omit [SLCommon.Params] in
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

/-! ## The invariant of `G1_col` and the oracles' steps -/

/-- The ten equalities of `colInv`. -/
def colEq (g₁ g₂ : VariableAssignment) : Prop :=
  F.RO.m.get g₁ = F.RO.m.get g₂ ∧ G1.mi.get g₁ = G1.mi.get g₂ ∧
  G1.paths.get g₁ = G1.paths.get g₂ ∧ G1.m.get g₁ = G1.m.get g₂ ∧
  G1.mhi.get g₁ = G1.mhi.get g₂ ∧ G1.chandle.get g₁ = G1.chandle.get g₂ ∧
  G1.mh.get g₁ = G1.mh.get g₂ ∧ FRO.m.get g₁ = FRO.m.get g₂ ∧ C.c.get g₁ = C.c.get g₂ ∧
  C.queries.get g₁ = C.queries.get g₂

/-- `Gcol.count` lies outside the variables of `G1` and `C` (the freshness of `Gcol_count`, as
`G1_col`'s hypothesis without `glob D`). -/
def GcolFresh : Prop :=
  Gcol_count.footprint ≤ (C.footprint ⊔ (F.RO.m).footprint ⊔ (FRO.m).footprint ⊔
    (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
    G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint)ᶜ

theorem GcolFresh.disj (h : GcolFresh Gcol_count) {α : Type} {X : Lens α VariableAssignment}
    (hX : X.footprint ≤ C.footprint ⊔ (F.RO.m).footprint ⊔ (FRO.m).footprint ⊔
      (G1.m).footprint ⊔ (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint) :
    Lens.Disjoint X Gcol_count :=
  Lens.disjoint_of_footprint_le_compl _ _
    ((Footprint.le_compl_comm _ _).mp (h.trans (Footprint.compl_antimono hX)))

/-- `X ≤ A₁ ⊔ … ⊔ Aₙ` for `X` one of the joinands (nested joins included), by backtracking. -/
syntax "fp_mem" : tactic
macro_rules
  | `(tactic| fp_mem) => `(tactic| first
    | with_reducible exact le_rfl
    | (with_reducible apply le_sup_of_le_right); fp_mem
    | (with_reducible apply le_sup_of_le_left); fp_mem)

/-- A variable's footprint below a join of footprints it is a joinand of (`C.footprint`
unfolded). -/
macro "gcol_fp" : tactic => `(tactic| ((try unfold C.footprint); fp_mem))

/-- The instances `Lens.Disjoint X Gcol_count` (and symmetric) for the variables `X` of `G1`, `C`,
from `h : GcolFresh Gcol_count`. -/
macro "gcol_disj " h:ident c:ident : tactic => `(tactic| (
  haveI : Lens.Disjoint C.c $c := GcolFresh.disj _ $h (by gcol_fp)
  haveI := (inferInstance : Lens.Disjoint C.c $c).symm
  haveI : Lens.Disjoint C.queries $c := GcolFresh.disj _ $h (by gcol_fp)
  haveI := (inferInstance : Lens.Disjoint C.queries $c).symm
  haveI : Lens.Disjoint F.RO.m $c := GcolFresh.disj _ $h (by gcol_fp)
  haveI := (inferInstance : Lens.Disjoint F.RO.m $c).symm
  haveI : Lens.Disjoint FRO.m $c := GcolFresh.disj _ $h (by gcol_fp)
  haveI := (inferInstance : Lens.Disjoint FRO.m $c).symm
  haveI : Lens.Disjoint G1.m $c := GcolFresh.disj _ $h (by gcol_fp)
  haveI := (inferInstance : Lens.Disjoint G1.m $c).symm
  haveI : Lens.Disjoint G1.mi $c := GcolFresh.disj _ $h (by gcol_fp)
  haveI := (inferInstance : Lens.Disjoint G1.mi $c).symm
  haveI : Lens.Disjoint G1.mh $c := GcolFresh.disj _ $h (by gcol_fp)
  haveI := (inferInstance : Lens.Disjoint G1.mh $c).symm
  haveI : Lens.Disjoint G1.mhi $c := GcolFresh.disj _ $h (by gcol_fp)
  haveI := (inferInstance : Lens.Disjoint G1.mhi $c).symm
  haveI : Lens.Disjoint G1.chandle $c := GcolFresh.disj _ $h (by gcol_fp)
  haveI := (inferInstance : Lens.Disjoint G1.chandle $c).symm
  haveI : Lens.Disjoint G1.paths $c := GcolFresh.disj _ $h (by gcol_fp)
  haveI := (inferInstance : Lens.Disjoint G1.paths $c).symm
  haveI : Lens.Disjoint G1.bext $c := GcolFresh.disj _ $h (by gcol_fp)
  haveI := (inferInstance : Lens.Disjoint G1.bext $c).symm
  haveI : Lens.Disjoint G1.bcol $c := GcolFresh.disj _ $h (by gcol_fp)
  haveI := (inferInstance : Lens.Disjoint G1.bcol $c).symm))

open Lean Meta Elab Tactic in
/-- `writes_keep`, the writes to global lenses closed by `touched_set_of_le_compl` with a hypothesis
`X.footprint ≤ Fᶜ` about the written lens `X` itself (found syntactically, not by `assumption`,
which compares the footprints of different lenses by unfolding them). -/
elab "writes_keep'" : tactic => do
  liftMetaTactic (writesKeepSplit ·)
  evalTactic (← `(tactic| all_goals try exact fun _ _ => rfl))
  let gs₀ ← getGoals
  for g in gs₀ do
    if ← g.isAssigned then continue
    let ty ← instantiateMVars (← g.getType)
    let some lift := ty.find? (·.isAppOfArity ``liftLens 4) | continue
    let X := lift.appArg!
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      let dty ← instantiateMVars d.type
      unless dty.isAppOfArity ``LE.le 4 do continue
      let lhs := dty.getArg! 2
      unless lhs.isAppOf ``Lens.footprint && lhs.appArg! == X do continue
      let s ← saveState
      try
        setGoals [g]
        withoutRecover <| evalTactic (← `(tactic| exact fun v σ => touched_set_of_le_compl
          $(mkIdent d.userName) v σ.globals))
        break
      catch _ => s.restore
  setGoals gs₀
  let gs ← gs₀.filterM fun g => return !(← g.isAssigned)
  setGoals gs

set_option hygiene false in
/-- `colEq` of two states after writes, from the equalities `e1`, …, `e10` of `colEq` before them:
the reads through the writes, then the equalities. -/
macro "col_eq" : tactic => `(tactic| (
  (try simp only [rngUpd_set])
  simp only [colEq]
  simp_reads
  (try simp only [rngUpd_get])
  (try simp only [e1]); (try simp only [e2]); (try simp only [e3]); (try simp only [e4])
  (try simp only [e5]); (try simp only [e6]); (try simp only [e7]); (try simp only [e8])
  (try simp only [e9]); (try simp only [e10])
  try simp))

set_option hygiene false in
/-- Rewrite the reads of the left state by `colEq`'s equalities `e1`, …, `e10`. -/
macro "col_rw" : tactic => `(tactic| (
  (try simp only [e1]); (try simp only [e2]); (try simp only [e3]); (try simp only [e4])
  (try simp only [e5]); (try simp only [e6]); (try simp only [e7]); (try simp only [e8])
  (try simp only [e9]); (try simp only [e10])))

set_option maxHeartbeats 1000000 in
-- the inlined oracles' wp goals are large
theorem S_fi_col (hfr : GcolFresh Gcol_count) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ colEq g₁ g₂ ∧
        (G1.bcol.get g₁ = true → G1.bcol.get g₂ = true) ∧
        ((FMap.frng (FRO.m.get g₂)).card : ℤ) ≤ 2 * C.c.get g₂ + 1 ∧
        Gcol_count.get g₂ ≤ C.c.get g₂ ∧ C.c.get g₂ + 1 ≤ max_size)
      (Indifferentiability.DPRIMITIVE.fi state (List block) block G1.S).procedure
      (Indifferentiability.DPRIMITIVE.fi state (List block) block (Gcol.S Gcol_count)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ colEq g₁ g₂ ∧
        (G1.bcol.get g₁ = true → G1.bcol.get g₂ = true) ∧
        ((FMap.frng (FRO.m.get g₂)).card : ℤ) ≤ 2 * C.c.get g₂ + 3 ∧
        Gcol_count.get g₂ ≤ C.c.get g₂ + 1 ∧ C.c.get g₂ + 1 ≤ max_size) := by
  gcol_disj hfr Gcol_count
  unfold G1.S Gcol.S
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
      (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
      ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} + 1 ∧
      §Gcol_count{2} ≤ §C.c{2} ∧ §C.c{2} + 1 ≤ max_size)
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
      rintro g₁ g₂ x _ ⟨⟨rfl, hE, hb, hc, hk, hm⟩, -⟩
      exact ⟨by rw [hE.2.1], hE, hb, by omega, by omega, hm⟩
    case «then» =>
      equiv_seq 2 3 : (§x0{1} = §x0{2} ∧ §hx2{1} = §hx2{2} ∧ §y1{1} = §y1{2} ∧
          §y2{1} = §(localVarLens "c" capacity){2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
          ((§G1.bcol{1} = true ∨ hinv §FRO.m{1} §y2{1} ≠ none) → §G1.bcol{2} = true) ∧
          ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} + 2 ∧
          §Gcol_count{2} ≤ §C.c{2} + 1 ∧ §C.c{2} + 1 ≤ max_size)
      · equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §hx2{1} = §hx2{2} ∧ §y1{1} = §y1{2} ∧
            colEq §allGlobals{1} §allGlobals{2} ∧
            (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
            ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} + 2 ∧
            §Gcol_count{2} ≤ §C.c{2} ∧ §C.c{2} + 1 ≤ max_size)
        · stmt_wp{2} 2
          equiv_rnd
          stmt_wp
          equiv_skip
          rintro g₁ g₂ x0 _ ⟨⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb, hc, hk, hm⟩,
              -⟩ a -
          col_rw
          split_ifs with h
          · exact ⟨trivial, trivial, by col_eq, hb, (card_rng_set _ _ _).trans (by omega), hk, hm⟩
          · exact ⟨trivial, trivial, by col_eq, hb, by omega, hk, hm⟩
        · equiv_if{2}
          case «then» =>
            stmt_wp{2} 2
            equiv_rnd
            equiv_skip
            rintro g₁ g₂ x0 hx2 y1 _ _ _ ⟨⟨rfl, rfl, rfl, hE, hb, hc, hk, hm⟩, -⟩ a -
            refine ⟨rfl, rfl, rfl, by simp only [colEq]; simp_reads; exact hE, ?_, by omega,
                by omega,
              hm⟩
            rintro (h | h)
            · simp [hb h]
            · simp [hinv_image _ _ (hE.2.2.2.2.2.2.2.1 ▸ h)]
          case «else» =>
            refine prhlStmt_pre prhlStmt_false ?_
            rintro σ₁ σ₂ ⟨⟨-, -, -, -, -, hc, hk, hm⟩, hg⟩
            simp only [decide_eq_false_iff_not, not_and, not_lt] at hg
            have := Finset.card_image_le (s := FMap.frng (FRO.m.get σ₂.globals)) (f := Prod.fst)
            have := hg (by omega)
            omega
      · stmt_wp
        equiv_skip
        rintro g₁ g₂ x0 hx2 y1 y2 _ _ _ _ ⟨rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9,
          e10⟩, hb, hc, hk, hm⟩
        col_rw
        split_ifs with h
        · refine ⟨trivial, by col_eq, fun h => hb (Or.inl h),
            (card_rng_set _ _ _).trans (by omega), hk,
            hm⟩
        · refine ⟨trivial, by col_eq, fun h => hb ?_, (card_rng_set _ _ _).trans (by omega), hk, hm⟩
          rw [e8]
          simpa using h

/-- The update of `S.f`, `S.fi` that makes `x.2` a known capacity (`FRO.m.[G1.chandle] <-
(x.2, Known); G1.chandle <- G1.chandle + 1` unless it is one already). -/
noncomputable def rngUpd (x : state) (g : VariableAssignment) : VariableAssignment :=
  if FMap.rng (FRO.m.get g) (x.2, Known) then g
  else G1.chandle.set (G1.chandle.get g + 1)
    (FRO.m.set ((FRO.m.get g).set (G1.chandle.get g) (x.2, Known)) g)

/-- Reads of other variables pass `rngUpd`. -/
theorem rngUpd_get {α : Type} (X : Lens α VariableAssignment) [Lens.Disjoint FRO.m X]
    [Lens.Disjoint G1.chandle X] (x : state) (g : VariableAssignment) :
    X.get (rngUpd x g) = X.get g := by
  unfold rngUpd
  split_ifs
  · rfl
  · rw [Lens.get_of_disjoint_set, Lens.get_of_disjoint_set]

/-- Writes to other variables commute with `rngUpd`. -/
theorem rngUpd_set {α : Type} (X : Lens α VariableAssignment) [Lens.Disjoint FRO.m X]
    [Lens.Disjoint G1.chandle X] [Lens.Disjoint X FRO.m] [Lens.Disjoint X G1.chandle] (x : state)
    (v : α) (g : VariableAssignment) :
    rngUpd x (X.set v g) = X.set v (rngUpd x g) := by
  unfold rngUpd
  rw [Lens.get_of_disjoint_set FRO.m X, Lens.get_of_disjoint_set G1.chandle X]
  split_ifs
  · rfl
  · rw [(inferInstance : Lens.Disjoint FRO.m X).commute,
      (inferInstance : Lens.Disjoint G1.chandle X).commute]

set_option maxHeartbeats 4000000 in
-- the inlined oracles' wp goals are large
theorem S_f_col (hfr : GcolFresh Gcol_count) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ colEq g₁ g₂ ∧
        (G1.bcol.get g₁ = true → G1.bcol.get g₂ = true) ∧
        ((FMap.frng (FRO.m.get g₂)).card : ℤ) ≤ 2 * C.c.get g₂ + 1 ∧
        Gcol_count.get g₂ ≤ C.c.get g₂ ∧ C.c.get g₂ + 1 ≤ max_size)
      (Indifferentiability.DPRIMITIVE.f state (List block) block G1.S).procedure
      (Indifferentiability.DPRIMITIVE.f state (List block) block (Gcol.S Gcol_count)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ colEq g₁ g₂ ∧
        (G1.bcol.get g₁ = true → G1.bcol.get g₂ = true) ∧
        ((FMap.frng (FRO.m.get g₂)).card : ℤ) ≤ 2 * C.c.get g₂ + 3 ∧
        Gcol_count.get g₂ ≤ C.c.get g₂ + 1 ∧ C.c.get g₂ + 1 ≤ max_size) := by
  gcol_disj hfr Gcol_count
  unfold G1.S Gcol.S
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
      (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
      ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} + 1 ∧
      §Gcol_count{2} ≤ §C.c{2} ∧ §C.c{2} + 1 ≤ max_size)
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
      rintro g₁ g₂ x _ ⟨⟨rfl, hE, hb, hc, hk, hm⟩, -⟩
      exact ⟨by rw [hE.2.2.2.1], hE, hb, by omega, by omega, hm⟩
    case «then» =>
      equiv_seq 7 4 : (§x0{1} = §x0{2} ∧ colEq (rngUpd §x0{1} §allGlobals{1}) §allGlobals{2} ∧
          §hx2{2} = oget (hinvK §FRO.m{2} (§x0{2}).2) ∧
          (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
          ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} + 2 ∧
          §Gcol_count{2} ≤ §C.c{2} ∧ §C.c{2} + 1 ≤ max_size)
      · stmt_wp
        equiv_skip
        rintro g₁ g₂ x0 _ ⟨⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb, hc, hk, hm⟩, -⟩
        simp only [rngUpd, Bool.not_eq_true', decide_eq_false_iff_not]
        col_rw
        split_ifs with hr
        · exact ⟨rfl, by col_eq, hb, by omega, hk, hm⟩
        · exact ⟨rfl, by col_eq, hb, (card_rng_set _ _ _).trans (by omega), hk, hm⟩
      · equiv_seq 6 3 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧ §y2{1} = §y2{2} ∧
            colEq (rngUpd §x0{1} §allGlobals{1}) §allGlobals{2} ∧
            §hx2{2} = oget (hinvK §FRO.m{2} (§x0{2}).2) ∧
            ((§G1.bcol{1} = true ∨ hinv §FRO.m{2} §y2{1} ≠ none) → §G1.bcol{2} = true) ∧
            ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} + 2 ∧
            §Gcol_count{2} ≤ §C.c{2} + 1 ∧ §C.c{2} + 1 ≤ max_size)
        · equiv_if
          case guard =>
            rintro g₁ g₂ x0 _ _ ⟨rfl, hE, -⟩
            have e3 : G1.paths.get g₁ = G1.paths.get g₂ := by
              rw [← hE.2.2.1, rngUpd]; split_ifs <;> simp_reads <;> trivial
            rw [e3]
          case «then» =>
            stmt_wp{2} 1
            equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧
                colEq (rngUpd §x0{1} §allGlobals{1}) §allGlobals{2} ∧
                §hx2{2} = oget (hinvK §FRO.m{2} (§x0{2}).2) ∧
                (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
                ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} + 2 ∧
                §Gcol_count{2} ≤ §C.c{2} ∧ §C.c{2} + 1 ≤ max_size)
            · stmt_wp
              equiv_rnd
              stmt_wp
              equiv_skip
              rintro g₁ g₂ x0 _ hx2 ⟨⟨rfl, hE, rfl, hb, hc, hk, hm⟩, -⟩ a -
              simp only [colEq, rngUpd_get] at hE
              obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hE
              col_rw
              split_ifs with hr
              · exact ⟨by trivial, by trivial, by col_eq, by trivial, hb, hc, hk, hm⟩
              · exact ⟨by trivial, by trivial, by col_eq, by trivial, hb, hc, hk, hm⟩
            · equiv_if{2}
              case «then» =>
                stmt_wp{2} 2
                equiv_rnd
                equiv_skip
                rintro g₁ g₂ x0 y1 _ _ hx2 ⟨⟨rfl, rfl, hE, rfl, hb, hc, hk, hm⟩, -⟩ a -
                refine ⟨by trivial, by trivial, by simp only [colEq]; simp_reads; exact hE,
                    by trivial,
                  ?_, by omega, by omega, hm⟩
                rintro (h | h)
                · simp [hb h]
                · simp [hinv_image _ _ h]
              case «else» =>
                refine prhlStmt_pre prhlStmt_false ?_
                rintro σ₁ σ₂ ⟨⟨-, -, -, -, -, hc, hk, hm⟩, hg⟩
                simp only [decide_eq_false_iff_not, not_and, not_lt] at hg
                have := Finset.card_image_le (s := FMap.frng (FRO.m.get σ₂.globals)) (f := Prod.fst)
                have := hg (by omega)
                omega
          case «else» =>
            stmt_wp{2} 1
            equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧
                colEq (rngUpd §x0{1} §allGlobals{1}) §allGlobals{2} ∧
                §hx2{2} = oget (hinvK §FRO.m{2} (§x0{2}).2) ∧
                (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
                ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} + 2 ∧
                §Gcol_count{2} ≤ §C.c{2} ∧ §C.c{2} + 1 ≤ max_size)
            · stmt_wp{2} 2
              equiv_rnd
              equiv_skip
              rintro g₁ g₂ x0 _ hx2 ⟨⟨rfl, hE, rfl, hb, hc, hk, hm⟩, -⟩ a -
              exact ⟨by trivial, hE, by trivial, hb, hc, hk, hm⟩
            · equiv_if{2}
              case «then» =>
                stmt_wp{2} 2
                equiv_rnd
                equiv_skip
                rintro g₁ g₂ x0 y1 _ _ hx2 ⟨⟨rfl, rfl, hE, rfl, hb, hc, hk, hm⟩, -⟩ a -
                refine ⟨by trivial, by trivial, by simp only [colEq]; simp_reads; exact hE,
                    by trivial,
                  ?_, by omega, by omega, hm⟩
                rintro (h | h)
                · simp [hb h]
                · simp [hinv_image _ _ h]
              case «else» =>
                refine prhlStmt_pre prhlStmt_false ?_
                rintro σ₁ σ₂ ⟨⟨-, -, -, -, -, hc, hk, hm⟩, hg⟩
                simp only [decide_eq_false_iff_not, not_and, not_lt] at hg
                have := Finset.card_image_le (s := FMap.frng (FRO.m.get σ₂.globals)) (f := Prod.fst)
                have := hg (by omega)
                omega
        · stmt_wp
          equiv_skip
          rintro g₁ g₂ x0 y1 y2 _ _ _ hx2 ⟨rfl, rfl, rfl, hE, rfl, hb, hc, hk, hm⟩
          simp only [Bool.not_eq_true', decide_eq_false_iff_not]
          by_cases hr : FMap.rng (FRO.m.get g₁) (x0.2, Known)
          · simp only [rngUpd, hr, if_true, not_true_eq_false, if_false] at hE ⊢
            obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hE
            col_rw
            split_ifs <;> refine ⟨by trivial, by col_eq, ?_,
                (card_rng_set _ _ _).trans (by omega), hk, hm⟩
            all_goals first
              | exact fun h => hb (Or.inl h)
              | (intro h; apply hb; simpa using h)
          · simp only [rngUpd, hr, if_false, not_false_eq_true, if_true] at hE ⊢
            simp only [colEq, Lens.get_of_disjoint_set, Lens.set_get] at hE
            obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hE
            col_rw
            split_ifs <;> refine ⟨by trivial, by col_eq, ?_,
                (card_rng_set _ _ _).trans (by omega), hk, hm⟩
            all_goals first
              | exact fun h => hb (Or.inl h)
              | (intro h; apply hb; simpa using h)

/-- `DFRestr`'s charge for a query `p`: the blocks of `p` past its longest known prefix. -/
noncomputable def qcost (p : List block) (g : VariableAssignment) : ℤ :=
  size p - «prefix» p (get_max_prefix p (elems (FMap.fdom (C.queries.get g))))

set_option maxHeartbeats 4000000 in
-- the inlined oracles' wp goals are large
theorem M_f_col (hfr : GcolFresh Gcol_count) :
    prhlProc (sig₁ := procsig (List block) -> block) (sig₂ := procsig (List block) -> block)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ colEq g₁ g₂ ∧
        (G1.bcol.get g₁ = true → G1.bcol.get g₂ = true) ∧
        ((FMap.frng (FRO.m.get g₂)).card : ℤ) ≤ 2 * (C.c.get g₂ - qcost a₂ g₂) + 1 ∧
        Gcol_count.get g₂ ≤ C.c.get g₂ - qcost a₂ g₂ ∧ C.c.get g₂ ≤ max_size)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block G1.M).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block (Gcol.M Gcol_count)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ colEq g₁ g₂ ∧
        (G1.bcol.get g₁ = true → G1.bcol.get g₂ = true) ∧
        ((FMap.frng (FRO.m.get g₂)).card : ℤ) ≤ 2 * C.c.get g₂ + 1 ∧
        Gcol_count.get g₂ ≤ C.c.get g₂ ∧ C.c.get g₂ ≤ max_size) := by
  gcol_disj hfr Gcol_count
  unfold G1.M Gcol.M
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_while (§p{1} = §p{2} ∧ §h{1} = §h{2} ∧ §i{1} = §i{2} ∧ §sa{1} = §sa{2} ∧
      §counter{1} = §counter{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
      (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧ 0 ≤ §counter{2} ∧ §counter{2} ≤ (size §p{2}
          - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2})))) ∧
      ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * (§C.c{2} - (size §p{2}
          - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2})))) +
              §counter{2}) + 1 ∧
      §Gcol_count{2} ≤ §C.c{2} - (size §p{2}
          - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2})))) + §counter{2}
              ∧ §C.c{2} ≤ max_size)
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
        equiv_seq 9 9 : (§p{1} = §p{2} ∧ §h{1} = §h{2} ∧ §i{1} = §i{2} ∧ §sa{1} = §sa{2} ∧
              §counter{1} = §counter{2} ∧ §sc{1} = §sc{2} ∧ §x0{1} = §x0{2} ∧
              §(localVarLens "r" block){1} = §(localVarLens "r" block){2} ∧
              colEq §allGlobals{1} §allGlobals{2} ∧
              (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧ 0 ≤ §counter{2} ∧
              §counter{2} < (size §p{2}
                  - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2})))) ∧
              ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * (§C.c{2} - (size §p{2}
                  - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2})))) +
                      §counter{2}) + 1 ∧
              §Gcol_count{2} ≤ §C.c{2} - (size §p{2}
                  - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2})))) +
                      §counter{2} + 1 ∧ §C.c{2} ≤ max_size)
        · equiv_rnd
          stmt_wp
          equiv_seq 1 1 : (§p{1} = §p{2} ∧ §h{1} = §h{2} ∧ §i{1} = §i{2} ∧ §sa{1} = §sa{2} ∧
                  §counter{1} = §counter{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
                  (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧ 0 ≤ §counter{2} ∧
                  §counter{2} < (size §p{2}
                      - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2})))) ∧
                  ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * (§C.c{2} - (size §p{2}
                      - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2})))) +
                          §counter{2}) + 1 ∧
                  §Gcol_count{2} ≤ §C.c{2} - (size §p{2}
                      - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{2})))) +
                          §counter{2} ∧ §C.c{2} ≤ max_size)
          · stmt_wp
            equiv_skip
            rintro g₁ g₂ p h i sa c _ _ _ _ _
              ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, hE, hb, h0, -, hc, hk, hm⟩, -⟩, -⟩, hlt⟩
            simp only [decide_eq_true_eq] at hlt
            rw [hE.2.2.2.2.2.2.2.2.2] at hlt
            exact ⟨rfl, rfl, rfl, rfl, rfl, hE, hb, h0, hlt, hc, hk, hm⟩
          · equiv_if{2}
            case «then» =>
              stmt_wp{2} 2
              equiv_rnd
              equiv_skip
              rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, hE, hb, h0, hlt, hc,
                  hk, hm⟩, -⟩
                a - r -
              refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp only [colEq]; simp_reads; exact hE,
                  ?_, h0,
                hlt, hc, by omega, hm⟩
              simp only [Bool.or_eq_true, decide_eq_true_eq]
              rintro (h | h)
              · exact Or.inl (hb h)
              · exact Or.inr (hinv_image _ _ (hE.2.2.2.2.2.2.2.1 ▸ h))
            case «else» =>
              refine prhlStmt_pre prhlStmt_false ?_
              rintro σ₁ σ₂ ⟨⟨-, -, -, -, -, -, -, h0, hlt, hc, hk, hm⟩, hg⟩
              simp only [decide_eq_false_iff_not, not_and, not_lt] at hg
              have := Finset.card_image_le (s := FMap.frng (FRO.m.get σ₂.globals)) (f := Prod.fst)
              have := hg (by omega)
              omega
        · stmt_wp
          equiv_skip
          rintro g₁ g₂ p h i sa c sc x0 r _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb, h0, hlt, hc, hk, hm⟩
          col_rw
          split_ifs <;> exact ⟨by trivial, by trivial, by trivial, by trivial, by trivial,
              by col_eq,
            hb, by omega, by omega, (card_rng_set _ _ _).trans (by omega), by omega, hm⟩
  case guard =>
    rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, -⟩
    rfl
  case exit =>
    rintro g₁ g₂ p h i sa c _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9,
      e10⟩, hb, h0, hle, hc, hk, hm⟩ - a -
    col_rw
    split_ifs <;> exact ⟨by trivial, by col_eq, hb, by omega, by omega, hm⟩
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x _ ⟨rfl, hE, hb, hc, hk, hm⟩
  unfold qcost at hc hk
  have := prefix_sizel x (get_max_prefix x (elems (FMap.fdom (C.queries.get g₂))))
  exact ⟨rfl, hE, hb, by omega, by omega, by omega, hm⟩

/-- The invariant of EC's `call (_: …)` in `G1_col`. -/
def colInv (g₁ g₂ : VariableAssignment) : Prop :=
  colEq g₁ g₂ ∧ (G1.bcol.get g₁ = true → G1.bcol.get g₂ = true) ∧
    ((FMap.frng (FRO.m.get g₂)).card : ℤ) ≤ 2 * C.c.get g₂ + 1 ∧
    Gcol_count.get g₂ ≤ C.c.get g₂ ∧ C.c.get g₂ ≤ max_size

set_option maxHeartbeats 1000000 in
-- the inlined oracles' wp goals are large
theorem DPRestr_fi_col (hfr : GcolFresh Gcol_count) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ colInv Gcol_count g₁ g₂)
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr G1.S)).procedure
      (Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr (Gcol.S Gcol_count))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ colInv Gcol_count g₁ g₂) := by
  gcol_disj hfr Gcol_count
  unfold colInv
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
      (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
      ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} + 1 ∧
      §Gcol_count{2} ≤ §C.c{2} ∧ §C.c{2} ≤ max_size)
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
      equiv_call (S_fi_col Gcol_count hfr)
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨rfl, rfl, hE, hb, hc, hk, hm⟩, hg⟩
      simp only [decide_eq_true_eq] at hg
      rw [hE.2.2.2.2.2.2.2.2.1] at hg
      refine ⟨⟨rfl, hE, hb, hc, hk, hg⟩, ?_⟩
      rintro r g₁' _ g₂' ⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb', hc', hk', hm'⟩
      exact ⟨rfl, by col_eq, hb', by omega, hk', hm'⟩
    case «else» =>
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨-, rfl, rest⟩, -⟩
      exact ⟨rfl, rest⟩

set_option maxHeartbeats 1000000 in
-- the inlined oracles' wp goals are large
theorem DPRestr_f_col (hfr : GcolFresh Gcol_count) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ colInv Gcol_count g₁ g₂)
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr G1.S)).procedure
      (Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr (Gcol.S Gcol_count))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ colInv Gcol_count g₁ g₂) := by
  gcol_disj hfr Gcol_count
  unfold colInv
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ colEq §allGlobals{1} §allGlobals{2} ∧
      (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
      ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} + 1 ∧
      §Gcol_count{2} ≤ §C.c{2} ∧ §C.c{2} ≤ max_size)
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
      equiv_call (S_f_col Gcol_count hfr)
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨rfl, rfl, hE, hb, hc, hk, hm⟩, hg⟩
      simp only [decide_eq_true_eq] at hg
      rw [hE.2.2.2.2.2.2.2.2.1] at hg
      refine ⟨⟨rfl, hE, hb, hc, hk, hg⟩, ?_⟩
      rintro r g₁' _ g₂' ⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb', hc', hk', hm'⟩
      exact ⟨rfl, by col_eq, hb', by omega, hk', hm'⟩
    case «else» =>
      equiv_skip
      rintro g₁ g₂ x _ y _ ⟨⟨-, rfl, rest⟩, -⟩
      exact ⟨rfl, rest⟩

set_option maxHeartbeats 1000000 in
-- the inlined oracles' wp goals are large
theorem DFRestr_f_col (hfr : GcolFresh Gcol_count) :
    prhlProc (sig₁ := procsig (List block) -> block) (sig₂ := procsig (List block) -> block)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ colInv Gcol_count g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr G1.M)).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr (Gcol.M Gcol_count))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ colInv Gcol_count g₁ g₂) := by
  gcol_disj hfr Gcol_count
  unfold colInv
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§bs{1} = §bs{2} ∧ §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧
      colEq §allGlobals{1} §allGlobals{2} ∧
      (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
      ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} + 1 ∧
      §Gcol_count{2} ≤ §C.c{2} ∧ §C.c{2} ≤ max_size)
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
        equiv_call (M_f_col Gcol_count hfr)
        stmt_wp
        equiv_skip
        rintro g₁ g₂ bs _ b _ ⟨⟨⟨rfl, rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb, hc, hk,
            hm⟩,
          -⟩, hg⟩
        simp only [decide_eq_true_eq] at hg
        rw [e9, e10] at hg
        unfold qcost
        simp_reads
        refine ⟨⟨by col_eq, hb, by omega, by omega, hg⟩, ?_⟩
        rintro r g₁' _ g₂' ⟨rfl, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, hb', hc', hk', hm'⟩
        exact ⟨rfl, by col_eq, hb', hc', hk', hm'⟩

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
    (G : Footprint VariableAssignment)
    (_hGd : G ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint)ᶜ)
    (_D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ Gᶜ →
      FVP.fvP P ≤ Gᶜ →
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

set_option maxHeartbeats 4000000 in
-- the twelve-variable invariant and the oracles' footprint checks
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
    (G : Footprint VariableAssignment)
    (_hGd : G ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint)ᶜ)
    (_D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ Gᶜ →
      FVP.fvP P ≤ Gᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless) :
    prhlProc
      (fun _ g₁ _ g₂ => (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (G1 (DRestr D)).procedure (Gcol Gcol_count D).procedure
      (fun _ g₁ _ g₂ => (G1.bcol.get g₁ = true → G1.bcol.get g₂ = true) ∧
        Gcol_count.get g₂ ≤ max_size) := by
  have hfr : GcolFresh Gcol_count :=
    _hfresh.trans (Footprint.compl_antimono (by
      unfold C.footprint
      iterate 11 refine sup_le ?_ ?_
      all_goals gcol_fp))
  gcol_disj hfr Gcol_count
  -- the variables of `G1`, `C` and `Gcol.count` lie outside `glob D`
  have hcc : (C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hcq : (C.queries).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hro : (F.RO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hfro : (FRO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
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
  have hgc : Gcol_count.footprint ≤ (FVP.fvP D)ᶜ :=
    _hfresh.trans (Footprint.compl_antimono (by gcol_fp))
  -- EC's invariant, on the values of the variables it reads
  let L := Lens.pair Gcol_count (Lens.pair C.c (Lens.pair C.queries (Lens.pair F.RO.m
    (Lens.pair FRO.m (Lens.pair G1.m (Lens.pair G1.mi (Lens.pair G1.mh (Lens.pair G1.mhi
      (Lens.pair G1.chandle (Lens.pair G1.paths G1.bcol))))))))))
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
    (x.2.2.2.2.2.2.2.2.2.2.2 = true → y.2.2.2.2.2.2.2.2.2.2.2 = true) ∧
    ((FMap.frng y.2.2.2.2.1).card : ℤ) ≤ 2 * y.2.1 + 1 ∧ y.1 ≤ y.2.1 ∧ y.2.1 ≤ max_size
  have hI : ∀ g₁ g₂, I (L.get g₁) (L.get g₂) ↔ colInv Gcol_count g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (L.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [L, Footprint.lens_pair]
    exact sup_le hgc (sup_le hcc (sup_le hcq (sup_le hro (sup_le hfro (sup_le hm (sup_le hmi
      (sup_le hmh (sup_le hmhi (sup_le hch (sup_le hpa hbc))))))))))
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (globInvF L (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    refine ⟨?_, (hI _ _).mpr ?_⟩
    · simp only [touched_set_of_le_compl hcc, touched_set_of_le_compl hcq,
        touched_set_of_le_compl hro, touched_set_of_le_compl hfro, touched_set_of_le_compl hm,
        touched_set_of_le_compl hmi, touched_set_of_le_compl hmh, touched_set_of_le_compl hmhi,
        touched_set_of_le_compl hch, touched_set_of_le_compl hpa, touched_set_of_le_compl hbx,
        touched_set_of_le_compl hbc, touched_set_of_le_compl hgc]
      exact h
    · simp only [colInv, colEq]
      simp_reads
      have := card_rng_set (FMap.empty : FMap handle (capacity × flag)) 0 (c0, Known)
      have h0 : (FMap.frng (FMap.empty : FMap handle (capacity × flag))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro y hy
        obtain ⟨k, hk⟩ := (FMap.mem_frng _ y).mp hy
        have hk' : FMap.get (FMap.empty : FMap handle (capacity × flag)) k = some y := hk
        rw [FMap.emptyE] at hk'
        cases hk'
      exact ⟨by omega, max_ge0⟩
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
          (DFRestr_f_col Gcol_count hfr)
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair]
          unfold G1.S Gcol.S
          exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
            (DPRestr_f_col Gcol_count hfr)
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair]
            unfold G1.S Gcol.S
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              (DPRestr_fi_col Gcol_count hfr)
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, -, hI'⟩
    have hc := (hI g₁ g₂).mp hI'
    simp_reads
    exact ⟨hc.2.1, hc.2.2.2.1.trans hc.2.2.2.2⟩

/-- EC's `Pr_G1col`. -/
theorem Pr_G1col (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint)ᶜ)
    (G : Footprint VariableAssignment)
    (_hGd : G ≤ (C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
      (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔ (F.RO.m).footprint ⊔
      (FRO.m).footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ Gᶜ →
      FVP.fvP P ≤ Gᶜ →
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
  refine le_trans ?_ (Pr_col Gcol_count D hD hc _hDd G _hGd D_ll m)
  exact_mod_cast Procedure.Pr_le_of_prhlProc (G1_col Gcol_count D hD hc _hDd G _hGd D_ll)
    (E₁ := fun _ g => G1.bcol.get g = true)
    (E₂ := fun _ g => G1.bcol.get g = true ∧ Gcol_count.get g ≤ max_size)
    (fun _ _ _ _ h h1 => ⟨h.1 h1, h.2⟩) (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl

end PROOF

end GaudisCrypt.SHA3.Gcol
