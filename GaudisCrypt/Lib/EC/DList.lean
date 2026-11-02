import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Logic.PHoareWp
import GaudisCrypt.Logic.PRHL.Prhl

/-!
# EasyCrypt's list distributions (`theories/distributions/DList.ec`)

`dlist d n` samples `n` values from `d`, independently.  The abstract theory `Program`'s type `t`
and operator `d` are section variables, so a `clone` is an application.  Only what ported
developments use is here.
-/

namespace GaudisCrypt.EC

variable {α : Type}

/-- `dlist d n`: a list of `n` independent samples of `d` (the empty list for `n ≤ 0`). -/
noncomputable def dlist (d : SubProbability α) (n : ℤ) : SubProbability (List α) :=
  go n.toNat
where
  /-- `dlist d n` for `n : ℕ`. -/
  go : ℕ → SubProbability (List α)
    | 0 => pure []
    | k + 1 => d >>= fun a => go k >>= fun l => pure (a :: l)

/-- `lemma dlist0`: no samples for `n <= 0`. -/
theorem dlist0 (d : SubProbability α) (n : ℤ) (hn : n ≤ 0) : dlist d n = pure [] := by
  unfold dlist; rw [show n.toNat = 0 by omega]; rfl

/-- One sample, then `n - 1` more (EC's `dlistS`, at `n - 1`, as a monadic bind). -/
theorem dlist_succ (d : SubProbability α) (n : ℤ) (hn : 0 < n) :
    dlist d n = d >>= fun a => dlist d (n - 1) >>= fun l => pure (a :: l) := by
  unfold dlist; rw [show n.toNat = (n - 1).toNat + 1 by omega]; rfl

variable {β : Type}

open Classical in
/-- The point mass of `dlist d` at a list of its length: the product of the elements'. -/
theorem dlist_go1E (d : SubProbability α) (xs : List α) :
    (dlist.go d xs.length).1 {xs} = (xs.map fun x => d.1 {x}).prod := by
  classical
  induction xs with
  | nil =>
    simp only [List.length_nil, dlist.go, List.map_nil, List.prod_nil]
    rw [mu1_eq_expected, expected_pure]; simp
  | cons a l ih =>
    simp only [List.length_cons, dlist.go, List.map_cons, List.prod_cons]
    rw [mu1_eq_expected, SubProbability.expected_bind]
    simp only [SubProbability.expected_bind, expected_pure, List.cons.injEq, ite_and]
    letI : MeasurableSpace α := ⊤
    have h : ∀ a', (dlist.go d l.length).expected
        (fun l' => if a' = a then (if l' = l then (1 : ENNReal) else 0) else 0) =
        (if a' = a then 1 else 0) * (dlist.go d l.length).1 {l} := fun a' => by
      by_cases ha : a' = a
      · simp only [ha, if_true, one_mul]
        convert (mu1_eq_expected _ _).symm
      · simp [ha, SubProbability.expected]
    simp only [h]
    rw [← ih]
    change ∫⁻ a', (if a' = a then (1 : ENNReal) else 0) * _ ∂d.1 = _
    rw [MeasureTheory.lintegral_mul_const _ (measurable_from_top (f := fun a' : α =>
      if a' = a then (1 : ENNReal) else 0))]
    congr 1
    rw [mu1_eq_expected]; rfl

open Classical in
/-- `dlist.go d k` only gives lists of length `k`. -/
theorem dlist_go_supp (d : SubProbability α) (k : ℕ) (xs : List α) (h : xs.length ≠ k) :
    (dlist.go d k).1 {xs} = 0 := by
  induction k generalizing xs with
  | zero =>
    rw [mu1_eq_expected]
    simp only [dlist.go, expected_pure]
    rw [if_neg (by rintro rfl; exact h rfl)]
  | succ k ih =>
    rw [mu1_eq_expected]
    simp only [dlist.go, SubProbability.expected_bind, expected_pure]
    cases xs with
    | nil => simp [SubProbability.expected]
    | cons x xs =>
      have hk : xs.length ≠ k := fun h' => h (by simp [h'])
      have : ∀ a, (dlist.go d k).expected (fun l => if a :: l = x :: xs then (1 : ENNReal) else 0)
          = 0 := fun a => by
        by_cases ha : a = x
        · subst ha
          simp only [List.cons.injEq, true_and]
          have := mu1_eq_expected (dlist.go d k) xs
          rw [ih xs hk] at this
          convert this.symm
        · simp [ha, SubProbability.expected]
      refine Eq.trans ?_ ((congrArg d.expected (funext this)).trans MeasureTheory.lintegral_zero)
      congr 1
      funext a
      congr 1
      funext l
      congr

/-- `lemma supp_dlist` (one direction): `dlist d n` only gives lists of length `max 0 n`. -/
theorem dlist_supp (d : SubProbability α) (n : ℤ) (xs : List α) (h : (xs.length : ℤ) ≠ max 0 n) :
    (dlist d n).1 {xs} = 0 :=
  dlist_go_supp d _ xs (by omega)
/-- `lemma dlist1E` (lists of the right size). -/
theorem dlist1E (d : SubProbability α) (n : ℤ) (xs : List α) (h : (xs.length : ℤ) = n) :
    (dlist d n).1 {xs} = (xs.map fun x => d.1 {x}).prod := by
  have : n.toNat = xs.length := by omega
  rw [dlist, this, dlist_go1E]

open Classical in
/-- The image of a distribution by an injective function, at an image point. -/
theorem map_mu1_inj (d : SubProbability α) {f : α → β} (hf : Function.Injective f) (x : α) :
    (d >>= fun a => (pure (f a) : SubProbability β)).1 {f x} = d.1 {x} := by
  rw [mu1_eq_expected, mu1_eq_expected d, SubProbability.expected_bind]
  simp only [expected_pure, hf.eq_iff]
namespace DList.Program

open GaudisCrypt

variable (t : Type) [Inhabited t] (d : SubProbability t)

module LoopSnoc {
  proc sample (n : ℤ) : (List t) {
    var i : ℤ, r : t, l : List t;
    i <- 0;
    l <- [];
    while ($i < $n) {
      r <$ d;
      l <- $l ++ [$r];
      i <- $i + 1;
    }
    return $l
  };
}

/-- The expectation after `LoopSnoc.sample`, from above (the loop's invariant: the samples still to
come are a `dlist` of the remaining length). -/
private theorem LoopSnoc.sample_ewp_le (G : List t → VariableAssignment → ENNReal) :
    phoareProc (fun _ _ => True) (LoopSnoc.sample t d).procedure G LE.le
      (fun n g => (dlist d n).expected fun l => G l g) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_le ((dlist d (§n0 - §i)).expected fun l' =>
    G (§(localVarLens "l" (List t)) ++ l') CurrentState.state.globals)
  case body =>
    phoare_wp 3
    phoare_skip
    intro σ i n0 l hg
    simp only [decide_eq_true_eq] at hg
    rw [dlist_succ d (n0 - i) (by omega), SubProbability.expected_bind]
    refine le_of_eq (congrArg d.expected (funext fun a => ?_))
    rw [SubProbability.expected_bind, show n0 - i - 1 = n0 - (i + 1) by ring]
    simp only [expected_pure, List.append_assoc, List.singleton_append]
  case exit =>
    intro σ i n0 l hg
    simp only [decide_eq_false_iff_not, not_lt] at hg
    rw [dlist0 _ _ (by omega)]
    simp [expected_pure]
  · phoare_wp 4
    phoare_skip
    intro σ n _
    simp

/-- The expectation after `LoopSnoc.sample`, from below (the same invariant, the variant
`n0 - i`). -/
private theorem LoopSnoc.sample_ewp_ge (G : List t → VariableAssignment → ENNReal) :
    phoareProc (fun _ _ => True) (LoopSnoc.sample t d).procedure G GE.ge
      (fun n g => (dlist d n).expected fun l => G l g) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_ge ((dlist d (§n0 - §i)).expected fun l' =>
    G (§(localVarLens "l" (List t)) ++ l') CurrentState.state.globals) variant ((§n0 - §i).toNat)
  case body =>
    phoare_wp 3
    phoare_skip
    intro σ i n0 l hg
    simp only [decide_eq_true_eq] at hg
    rw [dlist_succ d (n0 - i) (by omega), SubProbability.expected_bind]
    refine le_of_eq (congrArg d.expected (funext fun a => ?_)).symm
    rw [SubProbability.expected_bind, show n0 - i - 1 = n0 - (i + 1) by ring]
    simp only [expected_pure, List.append_assoc, List.singleton_append]
  case exit =>
    intro σ i n0 l hg
    simp only [decide_eq_false_iff_not, not_lt] at hg
    rw [dlist0 _ _ (by omega)]
    simp [expected_pure]
  case decreases =>
    intro k
    hoare_wp 3
    hoare_skip
    rintro i n0 ⟨hg, rfl⟩ _ _
    simp only [decide_eq_true_eq] at hg
    omega
  · phoare_wp 4
    phoare_skip
    intro σ n _
    simp

/-- `LoopSnoc.sample n` samples `dlist d n` (EC's `Sample_LoopSnoc_eq`, with `Sample.sample n`
being `r <$ dlist d n`), as expectations. -/
theorem LoopSnoc.sample_ewp (G : List t → VariableAssignment → ENNReal) (n : ℤ)
    (g : VariableAssignment) :
    (LoopSnoc.sample t d).procedure.ewp n G g = (dlist d n).expected fun l => G l g :=
  phoareProc_eq_of_le_ge (LoopSnoc.sample_ewp_le t d G) (LoopSnoc.sample_ewp_ge t d G) n g trivial

/-- `LoopSnoc.sample n`'s run: a sample of `dlist d n`, the globals kept. -/
theorem LoopSnoc.sample_denotation (n : ℤ) (g : VariableAssignment) :
    procedureDenotation (LoopSnoc.sample t d).procedure n g =
      (dlist d n).hbind fun l => pure (l, g) :=
  SubProbability.ext_of_expected fun F => by
    have := LoopSnoc.sample_ewp t d (fun l g => F (l, g)) n g
    simp only [Procedure.ewp, ProgramDenotation.wp] at this
    rw [SubProbability.expected_hbind]
    simp only [expected_pure]
    exact this

/-- EC's `pr_Sample` for `LoopSnoc` (`Sample_LoopSnoc_eq` and `pr_Sample`):
`Pr[LoopSnoc.sample(n) @ &m : res = xs] = mu1 (dlist d n) xs`. -/
theorem LoopSnoc.pr_sample (n : ℤ) (m : VariableAssignment) (xs : List t) :
    ((LoopSnoc.sample t d).procedure.Pr n m (fun res _ => res = xs) : ENNReal) =
      (dlist d n).1 {xs} := by
  rw [Procedure.Pr_eq_ewp, LoopSnoc.sample_ewp, mu1_eq_expected]
  simp [indicatorE]

end DList.Program

end GaudisCrypt.EC
