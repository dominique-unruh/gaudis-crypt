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



/- Legacy placeholders. Remove. -/
structure state where
  x : Nat
  y : Nat
abbrev Distr := SubProbability
noncomputable abbrev toDistr {α : Type} := @toSubProbability α
abbrev Program0 := Program state
noncomputable abbrev toProgram0 (p: PMF a) : Program0 a := p.toProgram
noncomputable
abbrev wp {a : Type} (prog : Program0 a) (f : a × state → ENNReal) (s : state) : ENNReal :=
  prog.wp f s
-- Can delete this, it's easy enough to write Program.uniform
noncomputable
abbrev coinToss : Program state Bool := Program.uniform

-- Probability that prog returns value x starting from state s.
-- The post-expectation x=y (Prop) is coerced to the {0,1}-indicator if y=x then 1 else 0.
noncomputable
abbrev prfinal {a : Type} [DecidableEq a] (prog : Program0 a) (x : a) (s : state) : ENNReal :=
  prog.finalProb1 s x


/- End legacy placeholders -/





@[reducible]
def Variable a := Lens a state

-- inconsistent
-- instance {a : Type} [N : Nonempty a] : Nonempty (Variable a) := sorry

noncomputable
def setVar {a : Type} (v : Lens a s) (x : a) : Program s Unit := do
    let st <- StateT.get
    let st' := v.set x st
    StateT.set st'


noncomputable
def getVar {a : Type} (v : Lens a s) : Program s a := do
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


theorem prfinal_coinToss (b : Bool) (st : state) : coinToss.finalProb1 st b = 1/2 := by
  simp [final_probability_wp', wp_uniform]
  cases b <;> simp
  sorry -- trivial1
  sorry -- trivial1


theorem wp_getVar {α : Type} (v : Variable α) (f : α × state → ENNReal) (s : state) :
    Program.wp (getVar v) f s = f (v.get s, s) := by
    simp [getVar, wp_bind, wp_pure, wp_get]

theorem wp_setVar {α : Type} (v : Lens α s) (x : α) (f : Program.Post s Unit) :
    (setVar v x).wp f = fun st => f ((), v.set x st) := by
    simp [setVar, wp_bind, wp_get, wp_set]


-- Loop invariant rule: if I is a pre-fixed-point of Ψ, then wp_while_val ≤ I.
-- Concretely: if (∀ s, if b s then wp body (fun (_, s') => I s') s else f ((), s)) ≤ I s,
-- then the loop's wp is bounded by I.

-- Broken... while_iteration_wp doesn't have the right types. Need to fix this in the spirit of the original
theorem wp_while_invariant (b : Program s Bool) (body : Program s Unit)
    (I : Program.Pre s) (f : Program.Post s Unit)
    (h : (b.wp fun (x,st) ↦ if x then body.wp (fun (x,st) ↦ (while_loop b body).wp (fun (_,st) => I st) st) st else f ((), st))
         <= I) :
    (while_loop b body).wp f ≤ I := by
    simp [wp_while]
    intros
    let xxx := @(while_iteration_wp''' b body).lfp_le
    apply (Ψ b body f).lfp_le h s
    exact (Ψ b body f).lfp_le h s

/- A better version of the prfinal_myProg_1 proof
   It doesn't try to reduce to `prfinal coinToss` because that doesn't work canonically.
-/
theorem prfinal_myProg_1_better (s : state) : prfinal myProg 1 s = 1/2 := by
  simp only [prfinal, final_probability_wp']
  simp [myProg, wp_bind, wp_ite, wp_setVar, wp_getVar, wp_pure, X.set_get, wp_uniform]
  sorry
