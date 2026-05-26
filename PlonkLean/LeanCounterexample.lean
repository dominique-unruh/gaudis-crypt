import Mathlib.Data.Finset.Sort
import PlonkLean.Lens
import PlonkLean.LensRange
import Mathlib.Data.List.Basic
import Mathlib.Data.FinEnum

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
  proveChain _ _ z1 (Lens.ext (by decide) (by decide))

lemma ub12 : LensIn.mk' upper_bound_1 ≥ LensIn.mk' example_lens_2 :=
  proveChain _ _ z2 (Lens.ext (by decide) (by decide))

lemma ub21 : LensIn.mk' upper_bound_2 ≥ LensIn.mk' example_lens_1 :=
  proveChain _ _ z1 (Lens.ext (by decide) (by decide))

lemma ub22 : LensIn.mk' upper_bound_2 ≥ LensIn.mk' example_lens_2 :=
  proveChain _ _ z2 (Lens.ext (by decide) (by decide))


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
  sorry




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

