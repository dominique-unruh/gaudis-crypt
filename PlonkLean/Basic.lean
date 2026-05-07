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

-- Weakest pre-expectation: expected value of f applied to the output of prog starting from state s.
-- prog s : Distr (a × state) is a sub-probability measure on (value, final-state) pairs,
-- and we integrate f against it using the Lebesgue integral.
noncomputable
def wp {a : Type} (prog : Program0 a) (f : a × state → ENNReal) (s : state) : ENNReal :=
  ∫⁻ x, f x ∂(prog s).1

-- Probability that prog returns value x starting from state s.
-- The post-expectation x=y (Prop) is coerced to the {0,1}-indicator if y=x then 1 else 0.
noncomputable
def prfinal {a : Type} [DecidableEq a] (prog : Program0 a) (x : a) (s : state) : ENNReal :=
  wp prog (fun (y, _) => if y = x then 1 else 0) s

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
theorem prfinal_coinToss (b : Bool) (s : state) : prfinal coinToss b s = 1/2 := by
  simp only [prfinal, wp]
  have h_bind : (coinToss s).1 =
      MeasureTheory.Measure.bind
        (@PMF.toMeasure Bool ⊤ (PMF.uniformOfFintype Bool))
        (fun b' : Bool => @MeasureTheory.Measure.dirac (Bool × state) ⊤ (b', s)) := by
    simp only [coinToss, sampleUniform, toProgram0, toDistr]
    unfold StateT.lift; rfl
  rw [h_bind]
  letI : MeasurableSpace (Bool × state) := ⊤
  have hind : ∀ x : Bool × state, (if x.1 = b then (1 : ENNReal) else 0) =
      ({x | x.1 = b} : Set (Bool × state)).indicator 1 x := by
    intro ⟨y, _⟩; simp [Set.indicator]
  simp_rw [hind]
  rw [MeasureTheory.lintegral_indicator_one (by trivial)]
  rw [MeasureTheory.Measure.bind_dirac_eq_map _ measurable_from_top,
      MeasureTheory.Measure.map_apply measurable_from_top (by trivial)]
  have hpre : (fun b' : Bool => (b', s)) ⁻¹' {x : Bool × state | x.1 = b} = {b} := by
    ext b'; simp
  rw [hpre, PMF.toMeasure_apply_singleton _ _ (by trivial), PMF.uniformOfFintype_apply]
  simp [Fintype.card_bool]

theorem coinToss_prob (s : state) (b : Bool) :
    (coinToss s).1 {p : Bool × state | p.1 = b} = 1/2 := by
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
  -- Step 4: compute the preimage — {b | (b,s).1 = b} = {b}
  have hpre : (fun b : Bool => (b, s)) ⁻¹' {p : Bool × state | p.1 = b} = {b} := by
    ext b'; simp
  rw [hpre]
  -- Step 5: PMF.toMeasure {a} = p a  (toMeasure_apply_singleton)
  rw [PMF.toMeasure_apply_singleton _ _ (by trivial)]
  -- Step 6: uniformOfFintype Bool b = (card Bool)⁻¹ = 2⁻¹ = 1/2
  simp [PMF.uniformOfFintype_apply, Fintype.card_bool]

noncomputable
def pbind {α β : Type} (mu : Program0 α) (f : α → Program0 β) : Program0 β :=
  fun s => instDistr.bind (mu s) (fun (a, s') => f a s')

-- Bind law for wp (sequential composition / chain rule).
--
-- wp (pbind mu f) g s = wp mu (fun (a, s') => wp (f a) g s') s
--
-- The expected value of g after "mu >>= f" equals the expected value under mu
-- of the function mapping each intermediate result (a, s') to the expected
-- value of g under "f a" starting from s'.
--
-- Proof outline:
--  1. Unfold wp and pbind: the goal becomes an integral of g against the
--     underlying Measure.bind of the Distr monad's bind.
--     h_bind (proved by rfl) exposes (instDistr.bind mu s).1 as the explicit
--     Measure.bind (mu s).1 (fun as' => (f as'.1 as'.2).1).
--  2. Apply Measure.lintegral_bind (Fubini for bind measures):
--       ∫⁻ x, g x ∂(Measure.bind μ κ) = ∫⁻ a, ∫⁻ x, g x ∂κ a ∂μ
--     Measurability of κ and g is trivial since all σ-algebras are ⊤.
--  3. The resulting double integral matches the unfolding of the RHS by rfl.
theorem wp_bind {α β : Type} (mu : Program0 α) (f : α → Program0 β)
    (g : β × state → ENNReal) (s : state) :
    wp (pbind mu f) g s = wp mu (fun (a, s') => wp (f a) g s') s := by
  simp only [wp, pbind]
  letI : MeasurableSpace (α × state) := ⊤
  letI : MeasurableSpace (β × state) := ⊤
  have h_bind : (instDistr.bind (mu s) (fun (a, s') => f a s')).1 =
      MeasureTheory.Measure.bind (mu s).1 (fun as' => (f as'.1 as'.2).1) := rfl
  rw [h_bind, MeasureTheory.Measure.lintegral_bind
      measurable_from_top.aemeasurable measurable_from_top.aemeasurable]

noncomputable
def seq {α β : Type} (p1 : Program0 α) (p2 : Program0 β) : Program0 β :=
  pbind p1 (fun _ => p2)

theorem wp_seq {α β : Type} (p1 : Program0 α) (p2 : Program0 β)
    (f : β × state → ENNReal) (s : state) :
    wp (seq p1 p2) f s = wp p1 (fun (_, s') => wp p2 f s') s :=
  wp_bind p1 (fun _ => p2) f s

theorem wp_ite {α : Type} (b : Bool) (p1 p2 : Program0 α)
    (f : α × state → ENNReal) (s : state) :
    wp (if b then p1 else p2) f s = if b then wp p1 f s else wp p2 f s := by
  cases b <;> rfl

theorem wp_pure {α : Type} (x : α) (f : α × state → ENNReal) (s : state) :
    wp (pure x) f s = f (x, s) := by
  simp only [wp]
  letI : MeasurableSpace (α × state) := ⊤
  have h : ((pure x : Program0 α) s).1 = @MeasureTheory.Measure.dirac (α × state) ⊤ (x, s) := rfl
  rw [h, MeasureTheory.lintegral_dirac' (x, s) measurable_from_top]

theorem wp_get (f : state × state → ENNReal) (s : state) :
    wp (StateT.get) f s = f (s, s) := by
  simp only [wp]
  letI : MeasurableSpace (state × state) := ⊤
  have h : (StateT.get s : Distr (state × state)).1 =
      @MeasureTheory.Measure.dirac (state × state) ⊤ (s, s) := rfl
  rw [h, MeasureTheory.lintegral_dirac' (s, s) measurable_from_top]

theorem wp_getVar {α : Type} (v : Variable α) (f : α × state → ENNReal) (s : state) :
    wp (getVar v) f s = f (v.get s, s) := by
  have hdef : getVar v = pbind StateT.get (fun s' => pure (v.get s')) := rfl
  rw [hdef, wp_bind, wp_get]
  simp [wp_pure]

theorem wp_set (s' : state) (f : Unit × state → ENNReal) (s : state) :
    wp (StateT.set s') f s = f ((), s') := by
  simp only [wp]
  letI : MeasurableSpace (Unit × state) := ⊤
  have h : (StateT.set s' s : Distr (Unit × state)).1 =
      @MeasureTheory.Measure.dirac (Unit × state) ⊤ ((), s') := rfl
  rw [h, MeasureTheory.lintegral_dirac' ((), s') measurable_from_top]

theorem wp_setVar {α : Type} (v : Variable α) (x : α) (f : Unit × state → ENNReal) (s : state) :
    wp (setVar v x) f s = f ((), v.set x s) := by
  have hdef : setVar v x = pbind StateT.get (fun s => StateT.set (v.set x s)) := rfl
  rw [hdef, wp_bind, wp_get]
  simp [wp_set]
