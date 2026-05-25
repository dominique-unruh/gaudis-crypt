import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Submonoid.Centralizer
import PlonkLean.Misc

@[ext]
structure Lens (a : Type u) (b : Type v) where
  get : b -> a
  set : a -> b -> b
  set_get : ∀ s x, get (set x s) = x
  set_set : ∀ s x y, set y (set x s) = set y s
  get_set : ∀ s, set (get s) s = s

/-- Lenses `x` and `y` are disjoint, i.e., refer to different parts of the memory -/
class disjoint (x : Lens a m) (y : Lens b m) where
  commute : ∀ s v w, x.set v (y.set w s) = y.set w (x.set v s)

theorem disjoint.iff : disjoint x y ↔ ∀ s v w, x.set v (y.set w s) = y.set w (x.set v s) :=
  ⟨fun h => h.commute, fun h => ⟨h⟩⟩

def pair (x : Lens a m) (y : Lens b m) [disj : disjoint x y] : Lens (a × b) m :=
  { get := fun s => (x.get s, y.get s)
    set := fun (u,v) s => x.set u (y.set v s)
    set_get := by
      simp [x.set_get]
      simp [disj.commute, y.set_get]
    set_set := by
     simp [disj.commute, y.set_set, x.set_set]
    get_set := by
      simp [y.get_set, x.get_set] }

def chain {a b c} (x : Lens b c) (y : Lens a b) : Lens a c := {
  get s := y.get (x.get s)
  set a s := x.set (y.set a (x.get s)) s
  set_get := by simp [x.set_get, y.set_get]
  set_set := by simp [x.set_get, y.set_set, x.set_set]
  get_set := by simp [x.get_set, y.get_set]
}

def fst : Lens a (a×b) := {
  get := fun (x,y) => x
  set := fun x' (x,y) => (x',y)
  set_get := by simp
  set_set := by simp
  get_set := by simp
}

def snd : Lens b (a×b) := {
  get := fun (x,y) => y
  set := fun y' (x,y) => (x,y')
  set_get := by simp
  set_set := by simp
  get_set := by simp
}

theorem pair_fst (x : Lens a m) (y : Lens b m) [disj : disjoint x y] :
  chain (pair x y) fst = x := by
    simp [chain, pair, fst, y.get_set]

theorem pair_snd (x : Lens a m) (y : Lens b m) [disj : disjoint x y] :
  chain (@pair _ _ _ x y disj) snd = y :=
    by simp [chain, pair, snd, disj.commute, x.get_set]

instance disjoint3 [xy : disjoint x y] [xz : disjoint x z] [yz : disjoint y z] :
  disjoint x (pair y z) :=
  by
    simp only [pair, disjoint.iff]
    intros
    simp [xy.commute, xz.commute]

instance disjoint3' [xy : disjoint x y] [xz : disjoint x z] [yz : disjoint y z] :
    disjoint (pair x y) z := by
  simp only [pair, disjoint.iff]
  intros
  simp [yz.commute, xz.commute]

def Lens.bijection (e : a ≃ b) : Lens a b where
  get := e.symm
  set x _ := e x
  set_get _ x := e.symm_apply_apply x
  set_set _ _ _ := rfl
  get_set s := e.apply_symm_apply s

structure LensIn.{u,v} (m : Type u) : Type _ where
  content : Type v
  lens : Lens content m

def LensIn.mk' (lens : Lens a m) : LensIn m := ⟨a, lens⟩

def IsoLens (lens : Lens a b) := Function.Bijective lens.get

instance : Preorder (LensIn m) where
  le x y := exists z : Lens x.content y.content, chain y.lens z = x.lens
  le_refl := fun x => by
    refine ⟨⟨id, fun a _ => a, fun _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩, ?_⟩
    obtain ⟨_, _, _, _, _⟩ := x.lens
    rfl
  le_trans := fun x y z hxy hyz => by
    obtain ⟨f, hf_chain⟩ := hxy
    obtain ⟨g, hg_chain⟩ := hyz
    refine ⟨chain g f, ?_⟩
    have assoc : chain z.lens (chain g f) = chain (chain z.lens g) f := by
      obtain ⟨_, _, _, _, _⟩ := f
      obtain ⟨_, _, _, _, _⟩ := g
      obtain ⟨_, _, _, _, _⟩ := z.lens
      rfl
    rw [assoc, hg_chain, hf_chain]

abbrev bit := ZMod 2

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

def Lens.update (lens : Lens a m) (f : a → a) : m → m := fun x => lens.set (f (lens.get x)) x

instance : Monoid (m → m) := sorry

structure LensRange (m : Type _) where
  updates : Set (m → m)
  id : id ∈ updates
  comp : f ∈ updates → g ∈ updates → (f ∘ g) ∈ updates
  double_commutant : (Submonoid.centralizer (Submonoid.centralizer updates).carrier).carrier = updates



def Lens.range (lens : Lens a m) : LensRange m where
  updates := Set.image lens.update ⊤
  id := sorry
  comp := sorry
  double_commutant := sorry

def LensRange.from (generators : Set (m → m)) : LensRange m where
  updates := Submonoid.centralizer (Submonoid.centralizer generators).carrier
  id := sorry
  comp := sorry
  double_commutant := sorry

instance : PartialOrder (LensRange m) where
  le x y := x.updates ≤ y.updates
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

instance : Lattice (LensRange m) where
  sup x y := LensRange.from (x.updates ∪ x.updates) -- double commutant of union
  inf x y := ⟨x.updates ∩ y.updates, sorry, sorry, sorry⟩  -- intersection
  le_sup_left := sorry
  le_sup_right := sorry
  le_inf := sorry
  sup_le := sorry
  inf_le_left := sorry
  inf_le_right := sorry

instance : BoundedOrder (LensRange m) where
  top := ⟨⊤, sorry, sorry, sorry⟩
  bot := ⟨⊥, sorry, sorry, sorry⟩
  bot_le := sorry
  le_top := sorry

instance : CompleteSemilatticeSup (LensRange m) where
  sSup s := sorry -- LensRange.from (union of all .updates in s)   -- double commutant of union
  isLUB_sSup := sorry

instance : CompleteSemilatticeInf (LensRange m) where
  sInf := sorry -- double commutant of intersection
  isGLB_sInf := sorry

instance : CompleteLattice (LensRange m) where


theorem Lens.range_defines_preorder (x : Lens a m) (y : Lens b m) :
  x.range ≤ y.range ↔ LensIn.mk' x ≤ LensIn.mk' y := sorry
