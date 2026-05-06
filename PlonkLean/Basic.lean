import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Uniform

def Distr (a : Type) := {mu: @MeasureTheory.Measure a ⊤ // mu ⊤ <= 1}

-- Just an example state
structure state where
  x : Nat
  y : Nat

-- def Semantics := state → Distr state

noncomputable
instance instDistr : Monad Distr where
  pure a :=
    ⟨@MeasureTheory.Measure.dirac _ ⊤ a, by simp⟩
  bind x f :=
    let ⟨mu, h⟩ := x
    ⟨MeasureTheory.Measure.bind mu (fun a => (f a).1), by
        simp only [Set.top_eq_univ]
        rw [MeasureTheory.Measure.bind_apply MeasurableSet.univ measurable_from_top.aemeasurable]
        calc ∫⁻ a, (f a).1 ⊤ ∂mu
            ≤ ∫⁻ _, 1 ∂mu := MeasureTheory.lintegral_mono (fun a => (f a).2)
          _ = mu ⊤ := MeasureTheory.lintegral_one
          _ ≤ 1 := h⟩


@[reducible]
def Program0 := StateT state Distr

def Program input output := input -> Program0 output

noncomputable
def toDistr (p : PMF α) : Distr α :=
  ⟨@PMF.toMeasure _ ⊤ p, by
    haveI := @PMF.toMeasure.isProbabilityMeasure _ ⊤ p
    exact le_of_eq MeasureTheory.IsProbabilityMeasure.measure_univ⟩

noncomputable
def toProgram0 (p : PMF α) : Program0 α :=
  StateT.lift (toDistr p)

noncomputable
def sampleUniform [h : Fintype α] [h : Nonempty α] : Program0 α :=
  toProgram0 (PMF.uniformOfFintype α)

noncomputable
def coinToss : Program0 Bool := sampleUniform

structure Lens (a : Type) (b : Type) where
  get : b -> a
  set : a -> b -> b
  set_get : ∀ s x, get (set x s) = x
  set_set : ∀ s x y, set y (set x s) = set y s
  get_set : ∀ s, set (get s) s = s


@[reducible]
def Variable a := Lens a state

-- inconsistent
-- instance {a : Type} [N : Nonempty a] : Nonempty (Variable a) := sorry

-- Don't remember if that's the right def
class disjoint (x : Lens a m) (y : Lens b m) where
  commute : ∀ s v w, x.set v (y.set w s) = y.set w (x.set v s)

theorem disjoint.iff : disjoint x y ↔ ∀ s v w, x.set v (y.set w s) = y.set w (x.set v s) :=
  ⟨fun h => h.commute, fun h => ⟨h⟩⟩

noncomputable
def setVar {a : Type} (v : Variable a) (x : a) : Program0 Unit := do
    let s <- StateT.get
    let s' := v.set x s
    StateT.set s'


noncomputable
def getVar {a : Type} (v : Variable a) : Program0 a := do
    let s <- StateT.get
    pure (v.get s)

def X : Variable Nat := {
  get := fun s => s.x,
  set := fun x s => {s with x := x},
  set_get := by simp,
  set_set := by simp,
  get_set := by simp
}

def Y : Variable Nat := {
  get := fun s => s.y,
  set := fun y s => {s with y := y},
  set_get := by simp,
  set_set := by simp,
  get_set := by simp
}

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

def fstL : Lens a (a×b) := {
  get := fun (x,y) => x
  set := fun x' (x,y) => (x',y)
  set_get := by simp
  set_set := by simp
  get_set := by simp
}

def sndL : Lens b (a×b) := {
  get := fun (x,y) => y
  set := fun y' (x,y) => (x,y')
  set_get := by simp
  set_set := by simp
  get_set := by simp
}

theorem pair_fst (x : Lens a m) (y : Lens b m) [disj : disjoint x y] :
  chain (pair x y) fstL = x := by
    simp [chain, pair, fstL, y.get_set]

theorem pair_snd (x : Lens a m) (y : Lens b m) [disj : disjoint x y] :
  chain (@pair _ _ _ x y disj) sndL = y :=
    by simp [chain, pair, sndL, disj.commute, x.get_set]

instance disjoint3 [xy : disjoint x y] [xz : disjoint x z] [yz : disjoint y z] :
  disjoint x (pair y z) :=
  -- let xy' : ∀ s v w, x.set v (y.set w s) = y.set w (x.set v s) := xy
  -- let xz' : ∀ s v w, x.set v (z.set w s) = z.set w (x.set v s) := xz
  by
    simp only [pair, disjoint.iff]
    intros
    simp [xy.commute, xz.commute]


instance disjoint3' [xy : disjoint x y] [xz : disjoint x z] [yz : disjoint y z] :
    disjoint (pair x y) z := by
  simp only [pair, disjoint.iff]
  intros
  simp [yz.commute, xz.commute]

instance disjXY : disjoint X Y := by
  apply disjoint.mk
  simp [X, Y]

-- Allows to write a set of variables.
def LensX m := Σx:Type, Lens x m

def Lens.toX (x : Lens a m) : LensX m := Sigma.mk a x

#check X.toX

#check [X.toX, Y.toX]

def disjoint_from_all (x : Lens a m) (ys : List (LensX m)) : Prop :=
  match ys with
  | [] => True
  | (⟨_, y⟩ :: xs) => disjoint x y ∧ disjoint_from_all x xs

def mutually_disjoint (xs : List (LensX m)) : Prop := match xs with
  | [] => True
  | (⟨_, x⟩ :: xs') => disjoint_from_all x xs' ∧ mutually_disjoint xs'

/-
From a list of [X.toX, Y.toX, ...] one can derive every pairwise disjointness.
So that's a compact way to mention mutual disjointness.
However, it's hard to extract the pairwise disjointnesses automatically.

Idea: (inspired by what we do in Isabelle):
have some syntax that adds all pairwise disjointnesses as instance.

Alternative (or mixed with that):
A syntactic sugar "disjoint_many (X, Y, Z, ...)" that's unfolded to a conjunction of many disjointnesses, and then we can use that to derive the pairwise disjointnesses.
-/

noncomputable
def myProg : Program0 Nat := do
  let x ← coinToss
  if x then setVar X 1 else setVar X 2
  let y <- getVar X
  pure y

opaque Z : Variable String := sorry

instance disjXZ : disjoint X Z := sorry
instance disjYZ : disjoint Y Z := sorry

instance disjoint_sym [disjoint X Y] : disjoint Y X := by
  simp only [disjoint.iff]
  simp [disjoint.iff.mp disjXY]

-- Works!
#synth disjoint (pair Y X) Z
