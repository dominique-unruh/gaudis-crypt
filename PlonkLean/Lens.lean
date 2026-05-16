import Mathlib.CategoryTheory.Category.Basic

structure Lens (a : Type) (b : Type) where
  get : b -> a
  set : a -> b -> b
  set_get : ∀ s x, get (set x s) = x
  set_set : ∀ s x y, set y (set x s) = set y s
  get_set : ∀ s, set (get s) s = s

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
