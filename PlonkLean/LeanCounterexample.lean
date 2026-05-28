import Mathlib.Data.Finset.Sort
import PlonkLean.Lens
import PlonkLean.LensRange
import Mathlib.Data.List.Basic
import Mathlib.Data.FinEnum
import Mathlib.SetTheory.Cardinal.Basic

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
    chain ub z = ex → LensIn.mk' ub ≥ LensIn.mk' ex := fun h => ⟨z, h⟩

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
    have heq : chain upper_bound_2 z = upper_bound_1 := hz
    have hthird : ∀ a (s : bit × bit × bit), ((chain upper_bound_2 z).set a s).2.2 = s.2.2 := by
      intro a ⟨x, y, w⟩; simp [chain, upper_bound_2]
    have h := hthird (1, 0) (0, 0, 0)
    rw [heq] at h; simp [upper_bound_1] at h
  have hincomp2 : ¬ LensIn.mk' upper_bound_2 ≤ LensIn.mk' upper_bound_1 := by
    -- chain upper_bound_1 z always preserves the 1st component, but upper_bound_2.set can change it
    intro ⟨z, hz⟩
    have heq : chain upper_bound_1 z = upper_bound_2 := hz
    have hfst : ∀ a (s : bit × bit × bit), ((chain upper_bound_1 z).set a s).1 = s.1 := by
      intro a ⟨x, y, w⟩; simp [chain, upper_bound_1]
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
  haveI : Fintype l.content :=
    Fintype.ofInjective (fun x => z_ub.set x (0, 0)) (fun x₁ x₂ h => by
      simpa [z_ub.set_get] using congr_arg z_ub.get h)
  haveI : Nonempty (bit × bit × bit) := ⟨(0, 0, 0)⟩
  have l_lt_4 : Fintype.card l.content < Fintype.card (bit × bit) :=
    lens_lt_content_lt l (LensIn.mk' upper_bound_1) l_leq
  have l_div_4 : Fintype.card l.content ∣ Fintype.card (bit × bit) :=
    lens_le_content_div l (LensIn.mk' upper_bound_1) l_leq.le
  -- l is upper bound of example_lens_2; get injection bit → l.content
  have hex2_le_l : LensIn.mk' example_lens_2 ≤ l := hlub.1 (Set.mem_insert_of_mem _ rfl)
  obtain ⟨z_ex2, hchain_ex2⟩ := hex2_le_l
  let s₀ : l.content := l.lens.get (Classical.choice inferInstance)
  have l_ge_2 : Fintype.card bit ≤ Fintype.card l.content :=
    Fintype.card_le_of_injective (fun a : bit => z_ex2.set a s₀) (fun a₁ a₂ h => by
      simpa [z_ex2.set_get] using congr_arg z_ex2.get h)
  have l_eq_2 : Fintype.card l.content = Fintype.card bit := by
    have h4 : Fintype.card (bit × bit) = 4 := by decide
    have h2 : Fintype.card bit = 2 := by decide
    omega
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
  obtain ⟨z_12, hchain_12⟩ := hex1_le_l.trans l_le_ex2
  have h1 : z_12.get (0 : bit) = 0 := by
    have := congr_fun (congr_arg Lens.get hchain_12) ((0, 0, 0) : bit × bit × bit)
    simpa [chain, example_lens_1, example_lens_2] using this
  have h2 : z_12.get (0 : bit) = 1 := by
    have := congr_fun (congr_arg Lens.get hchain_12) ((1, 0, 0) : bit × bit × bit)
    simpa [chain, example_lens_1, example_lens_2] using this
  exact absurd (h1.symm.trans h2) (by decide)




/-- `{id, Bool.not}` centralizes itself: the centralizer of `{id, Bool.not}` in `Bool → Bool`
    is exactly `{id, Bool.not}`. -/
private lemma bool_not_centralizer :
    (Submonoid.centralizer ({id, Bool.not} : Set (Bool → Bool))).carrier = {id, Bool.not} := by
  ext f
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    -- f commutes with Bool.not, so f(¬b) = ¬f(b) for all b
    have key : ∀ b : Bool, f (Bool.not b) = Bool.not (f b) := fun b => by
      have := congr_fun (h Bool.not (Or.inr rfl)) b
      simpa [HMul.hMul, Mul.mul, Function.comp] using this.symm
    cases hff : f false
    · left; funext b; cases b
      · exact hff
      · have := key false; rw [hff] at this; simpa using this
    · right; funext b; cases b
      · exact hff
      · have := key false; rw [hff] at this; simpa using this
  · rintro (rfl | rfl) g (rfl | rfl) <;>
    simp [HMul.hMul, Mul.mul]

private def lr_ext' : ∀ {x y : LensRange m}, x.updates = y.updates → x = y := by
  intro x y h; obtain ⟨_,_,_,_⟩ := x; obtain ⟨_,_,_,_⟩ := y
  simp only at h; subst h; rfl

/-- Counterexample: `{id, Bool.not}` is a valid `LensRange Bool` that is its own complement,
    disproving `LensRange.compl_is_compl` for general `LensRange`s. -/
def flipRange : LensRange Bool where
  updates := {id, Bool.not}
  id := Set.mem_insert _ _
  comp := by
    intro f g hf hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf hg ⊢
    rcases hf with rfl | rfl <;> rcases hg with rfl | rfl <;>
      decide
  double_commutant := by rw [bool_not_centralizer]; exact bool_not_centralizer

theorem flipRange_compl_eq_self : flipRangeᶜ = flipRange :=
  lr_ext' (by simp only [Compl.compl, flipRange, bool_not_centralizer])

