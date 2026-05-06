

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

structure Variable (a : Type) [N : Nonempty a] where
  get : state -> a
  set : a -> state -> state
  set_get : ∀ s x, get (set x s) = x
  set_set : ∀ s x y, set y (set x s) = set y s
  get_set : ∀ s, let x := get s; get (set x s) = x


-- inconsistent
-- instance {a : Type} [N : Nonempty a] : Nonempty (Variable a) := sorry

-- Don't remember if that's the right def
def disjoint [Nonempty a] [Nonempty b] (x : Variable a) (y : Variable b) : Prop :=
  ∀ s v w, x.set v (y.set w s) = y.set w (x.set v s)

noncomputable
def setVar {a : Type} [Nonempty a] (v : Variable a) (x : a) : Program0 Unit := do
    let s <- StateT.get
    let s' := v.set x s
    StateT.set s'


noncomputable
def getVar {a : Type} [Nonempty a] (v : Variable a) : Program0 a := do
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


theorem disjXY : disjoint X Y := by
  intros s v w
  simp [X, Y]

noncomputable
def myProg : Program0 Nat := do
  let x ← coinToss
  if x then setVar X 1 else setVar X 2
  let y <- getVar X
  pure y
