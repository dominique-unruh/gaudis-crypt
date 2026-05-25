import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Submonoid.Centralizer
import PlonkLean.Misc

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
  le x y := exists z : Lens x.content y.content, IsoLens z ∧ chain y.lens z = x.lens
  le_refl := sorry
  le_trans := sorry

abbrev bit := ZMod 2

def example_lens_1 : Lens bit (bit × bit × bit) where
  get := fun (x,y,z) => x + y
  set := fun a (x,y,z) => (x, x+a, z)
  set_get := sorry
  get_set := sorry
  set_set := sorry

def example_lens_2 : Lens bit (bit × bit × bit) where
  get := fun (x,y,z) => y + z
  set := fun a (x,y,z) => (x, z+a, z)
  set_get := sorry
  get_set := sorry
  set_set := sorry

def upper_bound_1 : Lens (bit × bit) (bit × bit × bit) where
  get := fun (x,y,z) => (x + y, y + z)
  set := fun (a,b) (x,y,z) => (x,a+x,a+b+x)
  set_get := sorry
  get_set := sorry
  set_set := sorry

def upper_bound_2 : Lens (bit × bit) (bit × bit × bit) where
  get := fun (x,y,z) => (x + y, y + z)
  set := fun (a,b) (x,y,z) => (a+b+z, b+z, z)
  set_get := sorry
  get_set := sorry
  set_set := sorry

lemma ub11 : LensIn.mk' upper_bound_1 ≥ LensIn.mk' example_lens_1 := sorry
lemma ub12 : LensIn.mk' upper_bound_1 ≥ LensIn.mk' example_lens_2 := sorry
lemma ub21 : LensIn.mk' upper_bound_2 ≥ LensIn.mk' example_lens_1 := sorry
lemma ub22 : LensIn.mk' upper_bound_2 ≥ LensIn.mk' example_lens_2 := sorry

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


structure LensRange (m : Type _) where
  updates :
    letI inst : Monoid (m → m) := sorry
    Submonoid (m → m)
  double_commutant :
    letI inst : Monoid (m → m) := _
    Submonoid.centralizer (Submonoid.centralizer updates.carrier).carrier = updates



def Lens.range (lens : Lens a m) : LensRange m where
  updates :=
    letI inst : Monoid (m → m) := _
    ⟨⟨Set.image lens.update ⊤, sorry⟩, sorry⟩
  double_commutant := sorry

instance : CompleteLattice (LensRange m) where
  le x y := x.updates ≤ y.updates
  bot := sorry -- only id
  top := sorry -- everything
  inf := sorry -- intersection
  sup := sorry -- double commutant of union
  sSup := sorry -- double commutant of union
  sInf := sorry -- intersection
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry
  le_sup_left := sorry
  le_sup_right := sorry
  le_inf := sorry
  sup_le := sorry
  inf_le_left := sorry
  bot_le := sorry
  inf_le_right := sorry
  isLUB_sSup := sorry
  isGLB_sInf := sorry
  le_top := sorry


theorem Lens.range_defines_preorder (x : Lens a m) (y : Lens b m) :
  x.range ≤ y.range ↔ LensIn.mk' x ≤ LensIn.mk' y := sorry
