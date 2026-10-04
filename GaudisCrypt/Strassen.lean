/-
Strassen's coupling theorem, discrete form. Only depends on Mathlib.

Proof outline:
* A finite, real-weighted (one-sided) Hall theorem: if `p(A) ≤ q(R(A))` for all `A ⊆ F`, then
  there is a flow `μ ≥ 0` supported on `R ∩ F × G` with row sums `p` and column sums `≤ q`.
  Proved by strong induction on `|F| + |G|`: push mass along an edge `(x, y)` as far as Hall
  permits; then either `p x` or `q y` is exhausted, or a proper subset becomes tight and the
  problem splits.
* A compactness argument: truncating `p` by the tail mass of `q` outside a finite `G` gives finite
  Hall problems; their flows lie in the compact set `∏ [0, q y]`, and an ultrafilter limit is the
  coupling (rows by dominated convergence, columns `≤ q` and hence `= q` by total mass).
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace GaudisCrypt

open Finset Filter Topology

noncomputable section

variable {X Y : Type*}

/-! ### Finite weighted Hall theorem -/

section Finite

open Classical in
/-- The neighbourhood of `A` inside `G`. -/
private def nbhd (R : X → Y → Prop) (G : Finset Y) (A : Finset X) : Finset Y :=
  G.filter (fun y => ∃ x ∈ A, R x y)

private lemma mem_nbhd {R : X → Y → Prop} {G : Finset Y} {A : Finset X} {y : Y} :
    y ∈ nbhd R G A ↔ y ∈ G ∧ ∃ x ∈ A, R x y := by
  simp [nbhd]

/-- Hall's condition for weights `p` on `F` and `q` on `G`. -/
private def Hall (R : X → Y → Prop) (F : Finset X) (G : Finset Y) (p : X → ℝ) (q : Y → ℝ) :
    Prop :=
  ∀ A ⊆ F, ∑ x ∈ A, p x ≤ ∑ y ∈ nbhd R G A, q y

/-- `μ` is a flow from `p` (on `F`) into `q` (on `G`) along `R`. -/
private structure IsFlow (R : X → Y → Prop) (F : Finset X) (G : Finset Y) (p : X → ℝ)
    (q : Y → ℝ) (μ : X → Y → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ μ x y
  supp : ∀ x y, μ x y ≠ 0 → x ∈ F ∧ y ∈ G ∧ R x y
  row : ∀ x ∈ F, ∑ y ∈ G, μ x y = p x
  col : ∀ y ∈ G, ∑ x ∈ F, μ x y ≤ q y

variable {R : X → Y → Prop}

private lemma IsFlow.zero_of_notMem_left {F : Finset X} {G : Finset Y} {p : X → ℝ} {q : Y → ℝ}
    {μ : X → Y → ℝ} (h : IsFlow R F G p q μ) {x : X} (hx : x ∉ F) (y : Y) : μ x y = 0 := by
  by_contra h'; exact hx (h.supp x y h').1

private lemma IsFlow.zero_of_notMem_right {F : Finset X} {G : Finset Y} {p : X → ℝ}
    {q : Y → ℝ} {μ : X → Y → ℝ} (h : IsFlow R F G p q μ) (x : X) {y : Y} (hy : y ∉ G) :
    μ x y = 0 := by
  by_contra h'; exact hy (h.supp x y h').2.1

private lemma IsFlow.sum_le {F : Finset X} {G : Finset Y} {p : X → ℝ} {q : Y → ℝ}
    {μ : X → Y → ℝ} (h : IsFlow R F G p q μ) (hq : ∀ y, 0 ≤ q y) (S : Finset X) (y : Y) :
    ∑ x ∈ S, μ x y ≤ q y := by
  classical
  by_cases hy : y ∈ G
  · calc ∑ x ∈ S, μ x y ≤ ∑ x ∈ S ∪ F, μ x y :=
          sum_le_sum_of_subset_of_nonneg subset_union_left fun x _ _ => h.nonneg x y
      _ = ∑ x ∈ F, μ x y :=
          (sum_subset subset_union_right fun x _ hx => h.zero_of_notMem_left hx y).symm
      _ ≤ q y := h.col y hy
  · rw [sum_eq_zero fun x _ => h.zero_of_notMem_right x hy]
    exact hq y

private lemma IsFlow.le {F : Finset X} {G : Finset Y} {p : X → ℝ} {q : Y → ℝ}
    {μ : X → Y → ℝ} (h : IsFlow R F G p q μ) (hq : ∀ y, 0 ≤ q y) (x : X) (y : Y) :
    μ x y ≤ q y := by
  simpa using h.sum_le hq {x} y

open Classical in
private lemma flow_split {F : Finset X} {G : Finset Y} {p : X → ℝ} {q : Y → ℝ} {A : Finset X}
    (hAF : A ⊆ F) {μ₁ μ₂ : X → Y → ℝ} (h₁ : IsFlow R A (nbhd R G A) p q μ₁)
    (h₂ : IsFlow R (F \ A) (G \ nbhd R G A) p q μ₂) :
    IsFlow R F G p q (fun x y => μ₁ x y + μ₂ x y) where
  nonneg x y := add_nonneg (h₁.nonneg x y) (h₂.nonneg x y)
  supp x y hxy := by
    by_cases h : μ₁ x y = 0
    · rw [h, zero_add] at hxy
      obtain ⟨hx, hy, hr⟩ := h₂.supp x y hxy
      exact ⟨(mem_sdiff.1 hx).1, (mem_sdiff.1 hy).1, hr⟩
    · obtain ⟨hx, hy, hr⟩ := h₁.supp x y h
      exact ⟨hAF hx, (mem_nbhd.1 hy).1, hr⟩
  row x hx := by
    rw [sum_add_distrib]
    by_cases hxA : x ∈ A
    · have h0 : ∑ y ∈ G, μ₂ x y = 0 :=
        sum_eq_zero fun y _ => h₂.zero_of_notMem_left (fun h => (mem_sdiff.1 h).2 hxA) y
      rw [h0, add_zero, ← h₁.row x hxA]
      exact (sum_subset (filter_subset _ _)
        fun y _ hy => h₁.zero_of_notMem_right x hy).symm
    · have h0 : ∑ y ∈ G, μ₁ x y = 0 := sum_eq_zero fun y _ => h₁.zero_of_notMem_left hxA y
      rw [h0, zero_add, ← h₂.row x (mem_sdiff.2 ⟨hx, hxA⟩)]
      exact (sum_subset sdiff_subset fun y _ hy => h₂.zero_of_notMem_right x hy).symm
  col y hy := by
    rw [sum_add_distrib]
    by_cases hyN : y ∈ nbhd R G A
    · have h0 : ∑ x ∈ F, μ₂ x y = 0 :=
        sum_eq_zero fun x _ => h₂.zero_of_notMem_right x (fun h => (mem_sdiff.1 h).2 hyN)
      rw [h0, add_zero, ← sum_subset hAF fun x _ hx => h₁.zero_of_notMem_left hx y]
      exact h₁.col y hyN
    · have h0 : ∑ x ∈ F, μ₁ x y = 0 := sum_eq_zero fun x _ => h₁.zero_of_notMem_right x hyN
      rw [h0, zero_add, ← sum_subset sdiff_subset fun x _ hx => h₂.zero_of_notMem_left hx y]
      exact h₂.col y (mem_sdiff.2 ⟨hy, hyN⟩)

open Classical in
private lemma flow_of_erase_left {F : Finset X} {G : Finset Y} {p : X → ℝ} {q : Y → ℝ}
    {μ : X → Y → ℝ} {x : X} (hpx : p x = 0) (h : IsFlow R (F.erase x) G p q μ) :
    IsFlow R F G p q μ where
  nonneg := h.nonneg
  supp a b hab := (h.supp a b hab).imp_left mem_of_mem_erase
  row a ha := by
    by_cases hax : a = x
    · subst hax
      rw [hpx]
      exact sum_eq_zero fun b _ => h.zero_of_notMem_left (notMem_erase a F) b
    · exact h.row a (mem_erase.2 ⟨hax, ha⟩)
  col b hb := by
    rw [← sum_erase F (h.zero_of_notMem_left (notMem_erase x F) b)]
    exact h.col b hb

open Classical in
private lemma flow_of_erase_right {F : Finset X} {G : Finset Y} {p : X → ℝ} {q : Y → ℝ}
    {μ : X → Y → ℝ} {y : Y} (hqy : 0 ≤ q y) (h : IsFlow R F (G.erase y) p q μ) :
    IsFlow R F G p q μ where
  nonneg := h.nonneg
  supp a b hab := (h.supp a b hab).imp_right (And.imp_left mem_of_mem_erase)
  row a ha := by
    rw [← sum_erase G (h.zero_of_notMem_right a (notMem_erase y G))]
    exact h.row a ha
  col b hb := by
    by_cases hby : b = y
    · subst hby
      rw [sum_eq_zero fun a _ => h.zero_of_notMem_right a (notMem_erase b G)]
      exact hqy
    · exact h.col b (mem_erase.2 ⟨hby, hb⟩)

open Classical in
private lemma flow_push {F : Finset X} {G : Finset Y} {p : X → ℝ} {q : Y → ℝ} {μ : X → Y → ℝ}
    {x : X} {y : Y} {t : ℝ} (hxy : R x y) (hx : x ∈ F) (hy : y ∈ G) (ht : 0 ≤ t)
    (h : IsFlow R F G (fun a => p a - if a = x then t else 0)
      (fun b => q b - if b = y then t else 0) μ) :
    IsFlow R F G p q (fun a b => μ a b + if a = x ∧ b = y then t else 0) where
  nonneg a b := add_nonneg (h.nonneg a b) (by split_ifs <;> simp [ht])
  supp a b hab := by
    by_cases h0 : μ a b = 0
    · rw [h0, zero_add] at hab
      split_ifs at hab with hab'
      · obtain ⟨rfl, rfl⟩ := hab'
        exact ⟨hx, hy, hxy⟩
      · exact absurd rfl hab
    · exact h.supp a b h0
  row a ha := by
    rw [sum_add_distrib, h.row a ha]
    by_cases hax : a = x <;> simp [hax, hy]
  col b hb := by
    rw [sum_add_distrib]
    have := h.col b hb
    by_cases hby : b = y
    · subst hby
      simp only [and_true, sum_ite_eq', hx, if_true] at this ⊢
      linarith
    · simp_all

open Classical in
/-- Pushing `t` along `(x, y)` keeps Hall's condition, provided `t` is at most the slack of every
`A ∌ x` whose neighbourhood contains `y`. -/
private lemma hall_push {F : Finset X} {G : Finset Y} {p : X → ℝ} {q : Y → ℝ} {x : X} {y : Y}
    {t : ℝ} (hall : Hall R F G p q) (hxy : R x y) (hy : y ∈ G)
    (hslack : ∀ A ⊆ F.erase x, y ∈ nbhd R G A →
      t ≤ ∑ b ∈ nbhd R G A, q b - ∑ a ∈ A, p a) :
    Hall R F G (fun a => p a - if a = x then t else 0) (fun b => q b - if b = y then t else 0) := by
  intro A hA
  have h := hall A hA
  simp only [sum_sub_distrib, sum_ite_eq']
  by_cases hxA : x ∈ A
  · have hyN : y ∈ nbhd R G A := mem_nbhd.2 ⟨hy, x, hxA, hxy⟩
    simp only [hxA, hyN, if_true]
    linarith
  · simp only [hxA, if_false]
    by_cases hyN : y ∈ nbhd R G A
    · have := hslack A (fun a ha => mem_erase.2 ⟨fun h => hxA (h ▸ ha), hA ha⟩) hyN
      simp only [hyN, if_true]
      linarith
    · simp only [hyN, if_false]
      linarith

private lemma nbhd_nbhd {G : Finset Y} {A B : Finset X} (hBA : B ⊆ A) :
    nbhd R (nbhd R G A) B = nbhd R G B := by
  ext y
  simp only [mem_nbhd]
  constructor
  · rintro ⟨⟨hy, -⟩, h⟩
    exact ⟨hy, h⟩
  · rintro ⟨hy, b, hb, hr⟩
    exact ⟨⟨hy, b, hBA hb, hr⟩, b, hb, hr⟩

open Classical in
private lemma nbhd_sdiff {G : Finset Y} {A B : Finset X} :
    nbhd R (G \ nbhd R G A) B = nbhd R G (A ∪ B) \ nbhd R G A := by
  ext y
  simp only [Finset.mem_sdiff, mem_nbhd, Finset.mem_union]
  constructor
  · rintro ⟨⟨hy, hn⟩, b, hb, hr⟩
    exact ⟨⟨hy, b, Or.inr hb, hr⟩, hn⟩
  · rintro ⟨⟨hy, b, hb, hr⟩, hn⟩
    exact ⟨⟨hy, hn⟩, b, hb.resolve_left fun hb => hn ⟨hy, b, hb, hr⟩, hr⟩

private lemma nbhd_mono {G : Finset Y} {A B : Finset X} (hAB : A ⊆ B) :
    nbhd R G A ⊆ nbhd R G B := fun _ hy =>
  let ⟨hy, a, ha, hr⟩ := mem_nbhd.1 hy
  mem_nbhd.2 ⟨hy, a, hAB ha, hr⟩

open Classical in
/-- A tight proper nonempty subset splits the problem into two smaller ones. -/
private lemma split_step {F : Finset X} {G : Finset Y} {p : X → ℝ} {q : Y → ℝ}
    (ih : ∀ (F' : Finset X) (G' : Finset Y) (p : X → ℝ) (q : Y → ℝ),
      F'.card + G'.card < F.card + G.card → (∀ x, 0 ≤ p x) → (∀ y, 0 ≤ q y) →
      Hall R F' G' p q → ∃ μ, IsFlow R F' G' p q μ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y) (hall : Hall R F G p q) {A : Finset X}
    (hAF : A ⊆ F) (hne : A.Nonempty) (hAF' : A ≠ F)
    (htight : ∑ x ∈ A, p x = ∑ y ∈ nbhd R G A, q y) : ∃ μ, IsFlow R F G p q μ := by
  have hA_lt : A.card < F.card := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hAF, hAF'⟩)
  have hN : (nbhd R G A).card ≤ G.card := card_le_card (filter_subset _ _)
  have hFA_lt : (F \ A).card < F.card := card_lt_card (sdiff_ssubset hAF hne)
  have hGN : (G \ nbhd R G A).card ≤ G.card := card_le_card sdiff_subset
  obtain ⟨μ₁, h₁⟩ := ih A (nbhd R G A) p q (by omega) hp hq fun B hB => by
    rw [nbhd_nbhd hB]; exact hall B (hB.trans hAF)
  obtain ⟨μ₂, h₂⟩ := ih (F \ A) (G \ nbhd R G A) p q (by omega) hp hq fun B hB => by
    have hdisj : Disjoint A B := disjoint_of_subset_right hB disjoint_sdiff
    have h := hall (A ∪ B) (union_subset hAF (hB.trans sdiff_subset))
    rw [nbhd_sdiff, sum_sdiff_eq_sub (nbhd_mono subset_union_left)]
    rw [sum_union hdisj] at h
    linarith
  exact ⟨_, flow_split hAF h₁ h₂⟩

/-- **Finite weighted Hall theorem.** -/
private theorem exists_flow (R : X → Y → Prop) : ∀ (n : ℕ) (F : Finset X) (G : Finset Y)
    (p : X → ℝ) (q : Y → ℝ), F.card + G.card = n → (∀ x, 0 ≤ p x) → (∀ y, 0 ≤ q y) →
    Hall R F G p q → ∃ μ, IsFlow R F G p q μ := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F G p q hn hp hq hall
  have ih' : ∀ (F' : Finset X) (G' : Finset Y) (p : X → ℝ) (q : Y → ℝ),
      F'.card + G'.card < F.card + G.card → (∀ x, 0 ≤ p x) → (∀ y, 0 ≤ q y) →
      Hall R F' G' p q → ∃ μ, IsFlow R F' G' p q μ :=
    fun F' G' p q hlt => ih _ (hn ▸ hlt) F' G' p q rfl
  rcases F.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact ⟨0, fun _ _ => le_rfl, fun _ _ h => absurd rfl h, fun _ h => absurd h (notMem_empty _),
      fun y _ => by simpa using hq y⟩
  by_cases hpx : p x = 0
  · obtain ⟨μ, hμ⟩ := ih' (F.erase x) G p q (by have := card_erase_lt_of_mem hx; omega) hp hq
      fun A hA => hall A (hA.trans (erase_subset _ _))
    exact ⟨μ, flow_of_erase_left hpx hμ⟩
  -- a neighbour `y` of `x`
  have hsum : ∑ y ∈ nbhd R G {x}, q y ≠ 0 := by
    have h := hall {x} (singleton_subset_iff.2 hx)
    rw [sum_singleton] at h
    have := lt_of_le_of_ne (hp x) (Ne.symm hpx)
    linarith
  obtain ⟨y, hyN⟩ := nonempty_of_sum_ne_zero hsum
  obtain ⟨hy, x', hx', hxy⟩ := mem_nbhd.1 hyN
  rw [mem_singleton] at hx'
  subst hx'
  -- the amount `t` to push along `(x, y)`
  let sl : Finset X → ℝ := fun A => ∑ b ∈ nbhd R G A, q b - ∑ a ∈ A, p a
  let S := (F.erase x').powerset.filter (fun A => y ∈ nbhd R G A)
  let T : Finset ℝ := insert (p x') (insert (q y) (S.image sl))
  have hT : T.Nonempty := insert_nonempty _ _
  set t := T.min' hT with ht_def
  have ht_le : ∀ s ∈ T, t ≤ s := fun s hs => min'_le T s hs
  have ht_px : t ≤ p x' := ht_le _ (mem_insert_self _ _)
  have ht_qy : t ≤ q y := ht_le _ (mem_insert_of_mem (mem_insert_self _ _))
  have hsl_nonneg : ∀ A ∈ S, 0 ≤ sl A := fun A hA => by
    have hA := (mem_powerset.1 (mem_filter.1 hA).1).trans (erase_subset _ _)
    have := hall A hA
    simp only [sl]
    linarith
  have ht_mem : t = p x' ∨ t = q y ∨ ∃ A ∈ S, sl A = t := by
    have h := min'_mem T hT
    rw [← ht_def] at h
    simp only [T, mem_insert, mem_image] at h
    exact h
  have ht0 : 0 ≤ t := by
    rcases ht_mem with h | h | ⟨A, hA, h⟩
    · exact h ▸ hp x'
    · exact h ▸ hq y
    · exact h ▸ hsl_nonneg A hA
  set p' : X → ℝ := fun a => p a - if a = x' then t else 0 with hp'_def
  set q' : Y → ℝ := fun b => q b - if b = y then t else 0 with hq'_def
  have hp' : ∀ a, 0 ≤ p' a := fun a => by
    simp only [p']; split_ifs with h
    · subst h; linarith
    · linarith [hp a]
  have hq' : ∀ b, 0 ≤ q' b := fun b => by
    simp only [q']; split_ifs with h
    · subst h; linarith
    · linarith [hq b]
  have hall' : Hall R F G p' q' := hall_push hall hxy hy fun A hA hyA =>
    ht_le _ (mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem sl
      (mem_filter.2 ⟨mem_powerset.2 hA, hyA⟩))))
  suffices h : ∃ μ, IsFlow R F G p' q' μ by
    obtain ⟨μ, hμ⟩ := h
    exact ⟨_, flow_push hxy hx hy ht0 hμ⟩
  clear_value t
  rcases ht_mem with h | h | ⟨A, hA, hslA⟩
  · -- `p x` is exhausted
    have hpx' : p' x' = 0 := by simp [p', h]
    obtain ⟨μ, hμ⟩ := ih' (F.erase x') G p' q' (by have := card_erase_lt_of_mem hx; omega)
      hp' hq' fun A hA => hall' A (hA.trans (erase_subset _ _))
    exact ⟨μ, flow_of_erase_left hpx' hμ⟩
  · -- `q y` is exhausted
    have hqy' : q' y = 0 := by simp [q', h]
    obtain ⟨μ, hμ⟩ := ih' F (G.erase y) p' q' (by have := card_erase_lt_of_mem hy; omega)
      hp' hq' fun A hA => by
        have hN : nbhd R (G.erase y) A = (nbhd R G A).erase y := by
          simp only [nbhd, filter_erase]
        rw [hN, sum_erase _ hqy']
        exact hall' A hA
    exact ⟨μ, flow_of_erase_right (hq' y) hμ⟩
  · -- a proper subset becomes tight
    obtain ⟨hApow, hyA⟩ := mem_filter.1 hA
    have hAx : A ⊆ F.erase x' := mem_powerset.1 hApow
    have hxA : x' ∉ A := fun h => notMem_erase x' F (hAx h)
    obtain ⟨-, a, ha, -⟩ := mem_nbhd.1 hyA
    refine split_step ih' hp' hq' hall' (hAx.trans (erase_subset _ _)) ⟨a, ha⟩
      (fun h => hxA (h ▸ hx)) ?_
    simp only [p', q', sum_sub_distrib, sum_ite_eq', hxA, hyA, if_true, if_false]
    simp only [sl] at hslA
    linarith

end Finite

/-! ### From finite flows to a coupling -/

/-- **Discrete Strassen theorem (coupling lifting).** Two discrete probability
    distributions `p`, `q` satisfying Hall's marginal-domination condition
    `p(A) ≤ q(R(A))` for all `A` admit a coupling `μ` with marginals `p` and `q`
    that is supported on `R`.

    `SubProbability.exists_coupling_of_hall` in `GaudisCrypt/Logic/PRHL2.lean`
    transfers this to `SubProbability`s.

    References: V. Strassen, "The existence of probability measures with given
    marginals", Ann. Math. Statist. 36(2):423–439, 1965; for the finite case in
    exactly this Hall form, T. Koperberg, "Couplings and Matchings: combinatorial
    notes on Strassen's theorem", arXiv:2202.02092. -/
theorem PMF.exists_coupling_of_hall {X Y : Type*}
    (p : PMF X) (q : PMF Y) (R : X → Y → Prop)
    (hpq : ∀ A : Set X, p.toOuterMeasure A ≤ q.toOuterMeasure {y | ∃ x ∈ A, R x y}) :
    ∃ μ : PMF (X × Y),
      μ.map Prod.fst = p ∧
      μ.map Prod.snd = q ∧
      ∀ w ∈ μ.support, R w.1 w.2 := by
  classical
  have hq1 : ∑' y, q y ≠ ⊤ := q.tsum_coe ▸ ENNReal.one_ne_top
  have hqS : ∀ s : Set Y, q.toOuterMeasure s ≠ ⊤ := fun s => by
    rw [PMF.toOuterMeasure_apply]
    exact ne_top_of_le_ne_top hq1 (ENNReal.tsum_le_tsum fun y => Set.indicator_le_self _ _ y)
  -- real-valued weights
  set pr : X → ℝ := fun x => (p x).toReal
  set qr : Y → ℝ := fun y => (q y).toReal
  have hqr0 : ∀ y, 0 ≤ qr y := fun y => ENNReal.toReal_nonneg
  have hqr_sum : Summable qr := ENNReal.summable_toReal hq1
  -- the tail mass of `q` outside a finite `G`, and the truncated weights `pG`
  let δ : Finset Y → ℝ := fun G => (q.toOuterMeasure (↑G)ᶜ).toReal
  have hδ0 : ∀ G, 0 ≤ δ G := fun G => ENNReal.toReal_nonneg
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h' : Tendsto (fun G : Finset Y => q.toOuterMeasure (↑G)ᶜ) atTop (𝓝 0) := by
      refine (ENNReal.tendsto_tsum_compl_atTop_zero hq1).congr fun G => ?_
      rw [PMF.toOuterMeasure_apply, ← _root_.tsum_subtype]
      rfl
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h'
    rwa [ENNReal.toReal_zero] at this
  let pG : Finset Y → X → ℝ := fun G x => max (pr x - δ G) 0
  have hall_fin : ∀ (F : Finset X) (G : Finset Y), Hall R F G (pG G) qr := by
    intro F G A _
    by_cases h : ∃ a ∈ A, δ G < pr a
    · obtain ⟨a, ha, hlt⟩ := h
      have h1 : ∑ x ∈ A, pG G x ≤ ∑ x ∈ A, pr x - δ G := by
        rw [← add_sum_erase A _ ha, ← add_sum_erase A _ ha]
        have : pG G a = pr a - δ G := max_eq_left (by linarith)
        have h2 : ∑ x ∈ A.erase a, pG G x ≤ ∑ x ∈ A.erase a, pr x :=
          sum_le_sum fun x _ => max_le (by linarith [hδ0 G]) ENNReal.toReal_nonneg
        linarith
      have h3 : ∑ x ∈ A, p x ≤ ∑ y ∈ nbhd R G A, q y + q.toOuterMeasure (↑G)ᶜ := by
        rw [← PMF.toOuterMeasure_apply_finset, ← PMF.toOuterMeasure_apply_finset]
        refine (hpq ↑A).trans ((MeasureTheory.measure_mono ?_).trans
          (MeasureTheory.measure_union_le _ _))
        rintro y ⟨x, hx, hr⟩
        exact if hy : y ∈ G then Or.inl (mem_coe.2 (mem_nbhd.2 ⟨hy, x, hx, hr⟩)) else Or.inr hy
      have hsum_ne : ∑ y ∈ nbhd R G A, q y ≠ ⊤ := ENNReal.sum_ne_top.2 fun y _ => q.apply_ne_top y
      have h4 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsum_ne, hqS _⟩) h3
      rw [ENNReal.toReal_add hsum_ne (hqS _), ENNReal.toReal_sum fun y _ => q.apply_ne_top y,
        ENNReal.toReal_sum fun x _ => p.apply_ne_top x] at h4
      linarith
    · simp only [not_exists, not_and, not_lt] at h
      rw [sum_eq_zero fun x hx => max_eq_right (by linarith [h x hx])]
      exact sum_nonneg fun y _ => hqr0 y
  -- finite flows, indexed by `(F, G)`
  have hflow : ∀ i : Finset X × Finset Y, ∃ μ, IsFlow R i.1 i.2 (pG i.2) qr μ :=
    fun i => exists_flow R _ i.1 i.2 _ _ rfl (fun _ => le_max_right _ _) hqr0 (hall_fin i.1 i.2)
  choose μ hμ using hflow
  -- an ultrafilter limit point `ν` of the flows
  let L : Filter (Finset X × Finset Y) := atTop ×ˢ atTop
  let U : Ultrafilter (Finset X × Finset Y) := Ultrafilter.of L
  have hUL : (U : Filter _) ≤ L := Ultrafilter.of_le L
  let m : Finset X × Finset Y → X × Y → ℝ := fun i w => μ i w.1 w.2
  have hmK : ∀ i, m i ∈ Set.univ.pi (fun w : X × Y => Set.Icc (0 : ℝ) (qr w.2)) :=
    fun i w _ => ⟨(hμ i).nonneg w.1 w.2, (hμ i).le hqr0 w.1 w.2⟩
  obtain ⟨ν, hνK, hν⟩ := (isCompact_univ_pi fun w : X × Y => isCompact_Icc).ultrafilter_le_nhds
    (U.map m) (by rw [Ultrafilter.coe_map]; exact tendsto_principal.2 (Eventually.of_forall hmK))
  rw [Ultrafilter.coe_map] at hν
  have hlim : ∀ w, Tendsto (fun i => m i w) U (𝓝 (ν w)) := tendsto_pi_nhds.1 hν
  have hν0 : ∀ w, 0 ≤ ν w := fun w => (hνK w (Set.mem_univ _)).1
  have hνq : ∀ w, ν w ≤ qr w.2 := fun w => (hνK w (Set.mem_univ _)).2
  have hνR : ∀ w, ν w ≠ 0 → R w.1 w.2 := by
    intro w hw
    by_contra hr
    have h0 : ∀ i, m i w = 0 := fun i => by_contra fun h => hr ((hμ i).supp w.1 w.2 h).2.2
    exact hw (tendsto_nhds_unique (hlim w) (by simp only [h0]; exact tendsto_const_nhds))
  -- rows: dominated convergence
  have hrow : ∀ x, ∑' y, ν (x, y) = pr x := by
    intro x
    have h1 : Tendsto (fun i => ∑' y, m i (x, y)) U (𝓝 (∑' y, ν (x, y))) :=
      tendsto_tsum_of_dominated_convergence hqr_sum (fun y => hlim (x, y))
        (Eventually.of_forall fun i y => by
          rw [Real.norm_eq_abs, abs_of_nonneg ((hμ i).nonneg x y)]
          exact (hμ i).le hqr0 x y)
    have hpG : Tendsto (fun i : Finset X × Finset Y => pG i.2 x) L (𝓝 (pr x)) := by
      have e : max (pr x - 0) 0 = pr x := by rw [sub_zero]; exact max_eq_left ENNReal.toReal_nonneg
      exact e ▸ (tendsto_const_nhds.sub (hδ.comp tendsto_snd)).max tendsto_const_nhds
    have hev : ∀ᶠ i in L, x ∈ i.1 :=
      ((eventually_ge_atTop {x}).prod_inl atTop).mono fun i hi => hi (mem_singleton_self x)
    have h2 : Tendsto (fun i => ∑' y, m i (x, y)) U (𝓝 (pr x)) := by
      refine Tendsto.congr' ?_ (hpG.mono_left hUL)
      filter_upwards [hUL hev] with i hi
      rw [tsum_eq_sum (s := i.2) fun y hy => (hμ i).zero_of_notMem_right x hy]
      exact ((hμ i).row x hi).symm
    exact tendsto_nhds_unique h1 h2
  -- columns: bounded by `q`
  have hcol_fin : ∀ y (S : Finset X), ∑ x ∈ S, ν (x, y) ≤ qr y := fun y S =>
    le_of_tendsto' (tendsto_finsetSum S fun x _ => hlim (x, y)) fun i => (hμ i).sum_le hqr0 S y
  -- the coupling
  let w : X × Y → ENNReal := fun z => ENNReal.ofReal (ν z)
  have hwrow : ∀ x, ∑' y, w (x, y) = p x := by
    intro x
    have hs : Summable fun y => ν (x, y) :=
      Summable.of_nonneg_of_le (fun y => hν0 (x, y)) (fun y => hνq (x, y)) hqr_sum
    have := ENNReal.ofReal_tsum_of_nonneg (fun y => hν0 (x, y)) hs
    rw [hrow x, ENNReal.ofReal_toReal (p.apply_ne_top x)] at this
    exact this.symm
  have hwcol : ∀ y, ∑' x, w (x, y) ≤ q y := by
    intro y
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun S => ?_
    simp only [w]
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => hν0 _, ← ENNReal.ofReal_toReal (q.apply_ne_top y)]
    exact ENNReal.ofReal_le_ofReal (hcol_fin y S)
  have htot : ∑' z, w z = 1 := by
    rw [ENNReal.tsum_prod']
    simp only [hwrow]
    exact p.tsum_coe
  have htot' : ∑' y, ∑' x, w (x, y) = 1 := by
    rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod', htot]
  have hwcol_eq : ∀ y, ∑' x, w (x, y) = q y := by
    intro y
    refine le_antisymm (hwcol y) (not_lt.1 fun hlt => ?_)
    have := ENNReal.tsum_lt_tsum (f := fun y => ∑' x, w (x, y)) (g := q) (i := y)
      (htot' ▸ ENNReal.one_ne_top) hwcol hlt
    rw [htot', q.tsum_coe] at this
    exact lt_irrefl _ this
  let μ' : PMF (X × Y) := ⟨w, htot ▸ ENNReal.summable.hasSum⟩
  have hμ' : ∀ z, μ' z = w z := fun _ => rfl
  refine ⟨μ', ?_, ?_, ?_⟩
  · ext x
    rw [PMF.map_apply, ENNReal.tsum_prod', ← hwrow x,
      tsum_eq_single x fun x' hx' => by simp [Ne.symm hx']]
    simp [hμ']
  · ext y
    rw [PMF.map_apply, ENNReal.tsum_prod', ← hwcol_eq y]
    refine tsum_congr fun x => ?_
    rw [tsum_eq_single y fun y' hy' => by simp [Ne.symm hy']]
    simp [hμ']
  · intro z hz
    rw [PMF.mem_support_iff, hμ'] at hz
    exact hνR z fun h0 => hz (by simp [w, h0])

end

end GaudisCrypt
