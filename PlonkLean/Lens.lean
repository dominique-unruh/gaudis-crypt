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


def Lens.update (lens : Lens a m) (f : a → a) : m → m := fun x => lens.set (f (lens.get x)) x


/-- `s ~ s'` iff they differ only in the part the lens controls:
    `∃ a, lens.set a s = s'`. -/
def Lens.equal_outside (lens : Lens a m) (s s' : m) : Prop :=
  ∃ x, lens.set x s = s'

/-- The relation `equal_outside` is an equivalence.
- refl:  `set (get s) s = s`  (by `get_set`)
- symm:  `set x s = s'`  →  `set (get s) s' = set (get s) (set x s) = set (get s) s = s`
         (first step by `set_set`, second by `get_set`)
- trans: `set x s = s'`, `set y s' = s''`  →  `set y s = set y (set x s) = s''`  (by `set_set`) -/
def Lens.equal_outside_setoid (lens : Lens a m) : Setoid m where
  r := lens.equal_outside
  iseqv := {
    refl  := fun s =>
      ⟨lens.get s, lens.get_set s⟩
    symm  := fun {s s'} ⟨x, hx⟩ =>
      ⟨lens.get s, by rw [← hx, lens.set_set, lens.get_set]⟩
    trans := fun {s _ s''} ⟨x, hx⟩ ⟨y, hy⟩ =>
      ⟨y, by rw [← hy, ← hx, lens.set_set]⟩
  }

def Lens.compl (lens : Lens a m) : Lens (Quotient lens.equal_outside_setoid) m where
  get mem := Quotient.mk'' mem
  set a mem := Quotient.lift (lens.set (lens.get mem))
    (fun _ _ h => by obtain ⟨x, hx⟩ := h; rw [← hx, lens.set_set]) a
  get_set s := by simp [lens.get_set]
  set_get s a := by
    induction a using Quotient.inductionOn
    rename_i v
    exact Quotient.sound ⟨lens.get v, (lens.set_set v _ _).trans (lens.get_set v)⟩
  set_set s a b := by
    induction a using Quotient.inductionOn
    rename_i v
    simp [lens.set_get]

