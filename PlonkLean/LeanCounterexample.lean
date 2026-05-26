import PlonkLean.Lens

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
