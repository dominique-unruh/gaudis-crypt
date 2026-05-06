

import Lean
import Mathlib

import Init.Control.State

def Distr (a : Type) := {mu: @MeasureTheory.Measure a ⊤ // mu ⊤ <= 1}

opaque state : Type

-- def Semantics := state → Distr state

noncomputable
instance instDistr : Monad Distr where
  pure a :=
    ⟨@MeasureTheory.Measure.dirac _ ⊤ a, sorry⟩
  bind x f :=
    let ⟨mu, h⟩ := x
    ⟨MeasureTheory.Measure.bind mu (fun a => (f a).1), sorry⟩


@[reducible]
def Program0 := StateT state Distr

def Program input output := input -> Program0 output

noncomputable
def toDistr (p: PMF α) : Distr α :=
  ⟨@PMF.toMeasure _ ⊤ p, sorry⟩

noncomputable
def toProgram0 (p: PMF α) : Program0 α :=
  StateT.lift (toDistr p)

noncomputable
def sampleUniform [h : Fintype α] [h : Nonempty α] : Program0 α :=
  toProgram0 (PMF.uniformOfFintype α)

noncomputable
def coinToss : Program0 Bool := sampleUniform

structure Variable (a : Type) [N : Nonempty a] where
  get : state -> a
  set : a -> state -> state
  -- TODO lens axioms

-- inconsistent
-- instance {a : Type} [N : Nonempty a] : Nonempty (Variable a) := sorry

opaque disjoint [Nonempty a] [Nonempty b] : Variable a -> Variable b -> Prop

noncomputable
def setVar {a : Type} [Nonempty a] (v : Variable a) (x : a) : Program0 Unit := do
    let s <- StateT.get
    let s' := v.set x s
    StateT.set s'


noncomputable
def getVar {a : Type} [Nonempty a] (v : Variable a) : Program0 a := do
    let s <- StateT.get
    pure (v.get s)

noncomputable
axiom X : Variable Nat
axiom Y : Variable Nat
axiom disjXY : disjoint X Y

noncomputable
def myProg: Program0 Nat := do
  let x ← coinToss
  if x then setVar X 1 else setVar X 2
  let y <- getVar X
  pure y
