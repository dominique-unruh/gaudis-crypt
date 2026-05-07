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

-- Theorem: coinToss returns `true` with probability 1/2.
--
-- The output type of `coinToss` is `Program0 Bool = state → Distr (Bool × state)`.
-- Applied to an initial state `s`, it yields a sub-probability measure on `Bool × state`.
-- We prove that the measure of the event {p | p.1 = true} (coin came up heads,
-- regardless of final state) is exactly 1/2.
--
-- Proof outline:
--  1. Unfold coinToss → sampleUniform → toProgram0 → StateT.lift. The monadic bind/pure in
--     Distr reduce definitionally (by rfl), exposing the underlying measure as
--     Measure.bind (PMF.toMeasure (uniformOfFintype Bool)) (Measure.dirac ∘ (·, s)).
--  2. Convert bind-with-Dirac to a pushforward via Measure.bind_dirac_eq_map:
--       Measure.bind μ (Dirac ∘ f) = Measure.map f μ.
--     We use `letI : MeasurableSpace (Bool × state) := ⊤` as a *transparent* binding (not
--     haveI) so the kernel can unify it with the ⊤ already baked into Measure.dirac.
--  3. Apply the pushforward formula (Measure.map_apply):
--       (Measure.map f μ) S = μ (f⁻¹' S).
--     MeasurableSet is trivial because ⊤ makes every set measurable.
--  4. Simplify the preimage: (b ↦ (b, s))⁻¹' {p | p.1 = true} = {true}.
--  5. Reduce PMF.toMeasure on a singleton via PMF.toMeasure_apply_singleton:
--       PMF.toMeasure {true} = uniformOfFintype Bool true.
--  6. Evaluate: uniformOfFintype Bool true = (card Bool)⁻¹ = 2⁻¹ = 1/2.
theorem coinToss_prob_true (s : state) :
    (coinToss s).1 {p : Bool × state | p.1 = true} = 1/2 := by
  -- Step 1: unfold the monadic chain to expose the underlying Measure.bind of Dirac deltas.
  -- After unfolding: coinToss s = bind (toDistr (uniformOfFintype Bool)) (fun b => pure (b, s))
  -- whose underlying measure is Measure.bind (PMF.toMeasure ...) (Measure.dirac ∘ (·, s)).
  have h_bind : (coinToss s).1 =
      MeasureTheory.Measure.bind
        (@PMF.toMeasure Bool ⊤ (PMF.uniformOfFintype Bool))
        (fun b : Bool => @MeasureTheory.Measure.dirac (Bool × state) ⊤ (b, s)) := by
    simp only [coinToss, sampleUniform, toProgram0, toDistr]
    unfold StateT.lift
    rfl
  rw [h_bind]
  -- state has no default MeasurableSpace; use letI (transparent) so the kernel
  -- can equate this instance with the ⊤ already baked into Measure.dirac in h_bind.
  letI : MeasurableSpace (Bool × state) := ⊤
  -- Step 2: Measure.bind (Dirac ∘ f) = Measure.map f  (bind_dirac_eq_map)
  rw [MeasureTheory.Measure.bind_dirac_eq_map _ measurable_from_top]
  -- Step 3: pushforward formula — (Measure.map f μ) S = μ (f⁻¹' S)
  rw [MeasureTheory.Measure.map_apply measurable_from_top (by trivial)]
  -- Step 4: compute the preimage — {b | (b,s).1 = true} = {true}
  have hpre : (fun b : Bool => (b, s)) ⁻¹' {p : Bool × state | p.1 = true} = {true} := by
    ext b; simp
  rw [hpre]
  -- Step 5: PMF.toMeasure {a} = p a  (toMeasure_apply_singleton)
  rw [PMF.toMeasure_apply_singleton _ _ (by trivial)]
  -- Step 6: uniformOfFintype Bool true = (card Bool)⁻¹ = 2⁻¹ = 1/2
  simp [PMF.uniformOfFintype_apply, Fintype.card_bool]
