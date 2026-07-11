import Mathlib.Data.Finset.Sort
import GaudisCrypt.Language.Lens
import GaudisCrypt.Attic.DetermFootprint
import Mathlib.Data.List.Basic
import Mathlib.Data.FinEnum
import Mathlib.SetTheory.Cardinal.Basic

/-!

Shows that the following theorem is wrong:

- Given two lenses, there exists a smallest lens containing both (`no_least_lens`)

-/

namespace GaudisCrypt.CounterExamples

open GaudisCrypt

def example_lens_1 : Lens bit (bit × bit × bit) where
  get := fun (x,y,z) => x + y
  set := fun a (x,y,z) => (x, x+a, z)
  set_get := by decide
  get_set := by decide
  set_set := by decide

def example_lens_2 : Lens bit (bit × bit × bit) where
  get := fun (x,y,z) => y + z
  set := fun a (x,y,z) => (x, z+a, z)
  set_get := by decide
  get_set := by decide
  set_set := by decide

def upper_bound_1 : Lens (bit × bit) (bit × bit × bit) where
  get := fun (x,y,z) => (x + y, y + z)
  set := fun (a,b) (x,y,z) => (x,a+x,a+b+x)
  set_get := by decide
  get_set := by decide
  set_set := by decide

def upper_bound_2 : Lens (bit × bit) (bit × bit × bit) where
  get := fun (x,y,z) => (x + y, y + z)
  set := fun (a,b) (x,y,z) => (a+b+z, b+z, z)
  set_get := by decide
  get_set := by decide
  set_set := by decide

private def z1 : Lens bit (bit × bit) where
  get := Prod.fst
  set := fun a (u,v) => (a, u+v+a)
  set_get := by decide
  set_set := by decide
  get_set := by decide

private def z2 : Lens bit (bit × bit) where
  get := Prod.snd
  set := fun a (u,v) => (u+v+a, a)
  set_get := by decide
  set_set := by decide
  get_set := by decide

private def proveChain (ub : Lens (bit × bit) (bit × bit × bit))
    (ex : Lens bit (bit × bit × bit)) (z : Lens bit (bit × bit)) :
    ub.chain z = ex → LensIn.mk' ub ≥ LensIn.mk' ex := fun h => ⟨z, h⟩

lemma ub11 : LensIn.mk' upper_bound_1 ≥ LensIn.mk' example_lens_1 :=
  proveChain _ _ z1 (by apply Lens.ext; decide)

lemma ub12 : LensIn.mk' upper_bound_1 ≥ LensIn.mk' example_lens_2 :=
  proveChain _ _ z2 (by apply Lens.ext; decide)

lemma ub21 : LensIn.mk' upper_bound_2 ≥ LensIn.mk' example_lens_1 :=
  proveChain _ _ z1 (by apply Lens.ext; decide)

lemma ub22 : LensIn.mk' upper_bound_2 ≥ LensIn.mk' example_lens_2 :=
  proveChain _ _ z2 (by apply Lens.ext; decide)

theorem no_least_lens : ¬ exists l : LensIn (bit × bit × bit),
  IsLUB {LensIn.mk' example_lens_1, LensIn.mk' example_lens_2} l := by
  /-
  Proof sketch:
  - Both upper_bound_1 and upper_bound_2 are upper bounds.
  - upper_bound_1 and upper_bound_2 are incomparable. Reason:
      - If  upper_bound_1 = chain upper_bound_2 x,
        then (chain upper_bound_2 x).set cannot modify the third component of the (bit x bit x bit) memory
        but upper_bound_1 does. So they can't be equal.
      - Analogous in the other direction
  - So if the LUB l exists, it must be strictly smaller than both upper_bound_1 and upper_bound_2
  - If l is strictly smaller than upper_bound_1, then l.content must have smaller cardinality than
    (LensIn.mk' upper_bound_1).content. And it must be a divider of that cardinality.
  - Since that cardinality is 4, l.content must have cardinality 2.
  - l >= example_lens_2, example_lens_2.content and l.content have same cardinality (namely 2)
  - Consequence: l ~~ example_lens_2  (~~ meaning both <= and >=).
  - Since l is an upper bound of example_lens_1, this implies example_lens_1 <= example_lens_2.
  - But that's incorrect, since example_lens_1.set can change the first component of the memory, and example_lens_2.set only the second
  - We have a contradiction, so l cannot exist
  -/
  intro ⟨l, hlub⟩
  have hincomp1 : ¬ LensIn.mk' upper_bound_1 ≤ LensIn.mk' upper_bound_2 := by
    -- chain upper_bound_2 z always preserves the 3rd component, but upper_bound_1.set can change it
    intro ⟨z, hz⟩
    have heq : upper_bound_2.chain z = upper_bound_1 := hz
    have hthird : ∀ a (s : bit × bit × bit), ((upper_bound_2.chain z).set a s).2.2 = s.2.2 := by
      intro a ⟨x, y, w⟩; simp [Lens.chain, upper_bound_2]
    have h := hthird (1, 0) (0, 0, 0)
    rw [heq] at h; simp [upper_bound_1] at h
  have hincomp2 : ¬ LensIn.mk' upper_bound_2 ≤ LensIn.mk' upper_bound_1 := by
    -- chain upper_bound_1 z always preserves the 1st component, but upper_bound_2.set can change it
    intro ⟨z, hz⟩
    have heq : Lens.chain upper_bound_1 z = upper_bound_2 := hz
    have hfst : ∀ a (s : bit × bit × bit), ((Lens.chain upper_bound_1 z).set a s).1 = s.1 := by
      intro a ⟨x, y, w⟩; simp [Lens.chain, upper_bound_1]
    have h := hfst (1, 0) (0, 0, 0)
    rw [heq] at h; simp [upper_bound_2] at h
  have l_leq : l < LensIn.mk' upper_bound_1 := by
    have hl_le_ub1 : l ≤ LensIn.mk' upper_bound_1 := hlub.2 (fun x hx => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl; exact ub11; exact ub12)
    have hl_le_ub2 : l ≤ LensIn.mk' upper_bound_2 := hlub.2 (fun x hx => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl; exact ub21; exact ub22)
    have hub1_not_le_l : ¬ LensIn.mk' upper_bound_1 ≤ l := fun h => hincomp1 (h.trans hl_le_ub2)
    exact lt_of_le_not_ge hl_le_ub1 hub1_not_le_l
  -- Fintype l.content from injection l.content → bit × bit
  obtain ⟨z_ub, _⟩ := l_leq.le
  haveI : Fintype (LensIn.mk' upper_bound_1).content := inferInstanceAs (Fintype (bit × bit))
  haveI : Fintype l.content :=
    Fintype.ofInjective (fun x => z_ub.set x (0, 0)) (fun x₁ x₂ h => by
      simpa [z_ub.set_get] using congr_arg z_ub.get h)
  haveI : Nonempty (bit × bit × bit) := ⟨(0, 0, 0)⟩
  have l_lt_4 : Fintype.card l.content < Fintype.card (LensIn.mk' upper_bound_1).content :=
    lens_lt_content_lt l (LensIn.mk' upper_bound_1) l_leq
  have l_div_4 : Fintype.card l.content ∣ Fintype.card (LensIn.mk' upper_bound_1).content :=
    lens_le_content_div l (LensIn.mk' upper_bound_1) l_leq.le
  -- l is upper bound of example_lens_2; get injection bit → l.content
  have hex2_le_l : LensIn.mk' example_lens_2 ≤ l := hlub.1 (Set.mem_insert_of_mem _ rfl)
  obtain ⟨(z_ex2 : Lens bit l.content), hchain_ex2⟩ := hex2_le_l
  let s₀ : l.content := l.lens.get (Classical.choice inferInstance)
  have l_ge_2 : Fintype.card bit ≤ Fintype.card l.content :=
    Fintype.card_le_of_injective (fun a : bit => z_ex2.set a s₀) (fun a₁ a₂ h => by
      simpa [z_ex2.set_get] using congr_arg z_ex2.get h)
  have l_eq_2 : Fintype.card l.content = Fintype.card bit := by
    have h4 : Fintype.card (LensIn.mk' upper_bound_1).content = 4 := by
      have heq : (LensIn.mk' upper_bound_1).content = (bit × bit) := rfl
      rw [Fintype.card_congr (Equiv.cast heq)]; decide
    have h2 : Fintype.card bit = 2 := by decide
    have hlt : Fintype.card l.content < 4 := h4 ▸ l_lt_4
    have hge : 2 ≤ Fintype.card l.content := h2 ▸ l_ge_2
    obtain ⟨k, hk⟩ := h4 ▸ l_div_4
    have hkpos : 0 < k := by nlinarith
    have hkle : k ≤ 2 := by nlinarith
    rcases Nat.lt_or_eq_of_le hkle with hlt2 | rfl
    · have : k = 1 := by omega
      subst this; omega
    · omega
  -- z_ex2 has bijective get (equal cardinalities), so l ≤ example_lens_2
  haveI : Nonempty l.content := ⟨s₀⟩
  have f_inj_ex2 : Function.Injective (fun a : bit => z_ex2.set a s₀) := fun a₁ a₂ h => by
    simpa [z_ex2.set_get] using congr_arg z_ex2.get h
  have f_surj_ex2 : Function.Surjective (fun a : bit => z_ex2.set a s₀) :=
    f_inj_ex2.surjective_of_finite (Fintype.equivOfCardEq l_eq_2.symm)
  have hinj_ex2 : Function.Injective z_ex2.get := fun y₁ y₂ hy => by
    obtain ⟨a₁, rfl⟩ := f_surj_ex2 y₁; obtain ⟨a₂, rfl⟩ := f_surj_ex2 y₂
    simp only [z_ex2.set_get] at hy; rw [hy]
  have l_le_ex2 : l ≤ LensIn.mk' example_lens_2 :=
    iso_lens_ge example_lens_2 l.lens (get_injective_iso_lens z_ex2 hinj_ex2) hchain_ex2
  -- example_lens_1 ≤ l ≤ example_lens_2 → contradiction
  have hex1_le_l : LensIn.mk' example_lens_1 ≤ l := hlub.1 (Set.mem_insert _ _)
  obtain ⟨(z_12 : Lens bit bit), hchain_12⟩ := hex1_le_l.trans l_le_ex2
  have h1 : z_12.get (0 : bit) = (0 : bit) := by
    have := congr_fun (congr_arg (fun l : Lens bit (bit × bit × bit) => l.get) hchain_12)
      ((0, 0, 0) : bit × bit × bit)
    simpa [Lens.chain, example_lens_1, example_lens_2, LensIn.mk'] using this
  have h2 : z_12.get (0 : bit) = (1 : bit) := by
    have := congr_fun (congr_arg (fun l : Lens bit (bit × bit × bit) => l.get) hchain_12)
      ((1, 0, 0) : bit × bit × bit)
    simpa [Lens.chain, example_lens_1, example_lens_2, LensIn.mk'] using this
  exact absurd (show (0 : bit) = 1 from h1.symm.trans h2) (by decide)



end GaudisCrypt.CounterExamples
