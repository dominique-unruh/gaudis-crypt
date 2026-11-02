import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Lib.EC.Distr

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

end DList.Program

end GaudisCrypt.EC
