import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Order.FixedPoints
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.OmegaCompletePartialOrder

import PlonkLean.Misc
import PlonkLean.Semantics
import PlonkLean.WeakestPreconditions
import PlonkLean.Lens

structure state where
  x : Nat
  y : Nat

abbrev Variable a := Lens a state

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
def myProg : Program state Nat := do
  let (x:Bool) ← Program.uniform
  if x then Program.set X 1 else Program.set X 2
  let y <- Program.get X
  pure y

opaque Z : Variable String := sorry

instance disjXZ : disjoint X Z := sorry
instance disjYZ : disjoint Y Z := sorry

instance disjoint_sym [disjoint X Y] : disjoint Y X := by
  simp only [disjoint.iff]
  simp [disjoint.iff.mp disjXY]

-- Works!
#synth disjoint (pair Y X) Z


theorem prfinal_coinToss (b : Bool) (st : state) : Program.uniform.finalProb1 st b = 1/2 := by
  simp [final_probability_wp', wp_uniform]
  cases b <;> simp
  sorry -- trivial1
  sorry -- trivial1





/- A better version of the prfinal_myProg_1 proof
   It doesn't try to reduce to `prfinal coinToss` because that doesn't work canonically.
-/
theorem prfinal_myProg_1_better (s : state) : myProg.finalProb1 s 1 = 1/2 := by
  simp only [final_probability_wp']
  simp [myProg, wp_bind, wp_ite, wp_set, wp_get, wp_pure, X.set_get, wp_uniform]
  sorry


-- Mutual recursion example

noncomputable
def prog1 (prog2 : Program s String) : Program s Nat := do
  let b : Bool <- Program.uniform
  if b then
    let x <- prog2
    return x.length
  else
    return 0

noncomputable
def prog2 (prog1 : Program s Nat) : Program s String := do
  let x <- prog1
  return toString x

noncomputable
def iter (prog12 : ∀ b:Bool, Program s (if b then Nat else String)) (b:Bool) :
  Program s (if b then Nat else String) :=
  match b with
    | true => prog1 (prog12 false)
    | false => prog2 (prog12 true)

theorem iter_cont {s} : OmegaCompletePartialOrder.ωScottContinuous (iter (s:=s)) :=
  sorry

noncomputable
def prog12 : ∀ b:Bool, Program s (if b then Nat else String) :=
  recursion (OmegaCompletePartialOrder.ContinuousHom.ofFun iter (hf := iter_cont))

-- Note: the wp-theorems don't allow us to analyze this yet,
-- because the return type of prog12 is dependent on b and the theorems
-- are stated nondependently. Fix!

-- I think prog1 outputs 0/1 with probability 1/2 each. Can we show this?
-- Proof idea: represent the wp as an lfp of some function iter_wp.
-- Manually iterate iter_wp starting at bot.
-- I think this converges after 2 steps or so.
