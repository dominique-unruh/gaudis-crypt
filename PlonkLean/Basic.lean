import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Order.FixedPoints
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.OmegaCompletePartialOrder

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

-- wp_bind lifted to the >>= (do-notation bind) for Program0.
-- The do-notation in myProg uses Bind.bind (via StateT.bind), while wp_bind works for pbind.
-- They give the same measure: both unfold to instDistr.bind, so Subtype.ext + simp closes the gap.
theorem wp_bind_do {α β : Type} (mu : Program0 α) (f : α → Program0 β)
    (g : β × state → ENNReal) (s : state) :
    wp (mu >>= f) g s = wp mu (fun (a, s') => wp (f a) g s') s := by
  have heq : mu >>= f = pbind mu f := by
    funext s
    apply Subtype.ext
    simp only [Bind.bind, StateT.bind, pbind]
  rw [heq]
  exact wp_bind mu f g s

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


-- Finite approximants of the while loop.
-- while_iter b body 0 is the "bottom" approximant (zero measure — never terminates).
-- while_iter b body (n+1) runs the body once (if b holds) then applies n more iterations.
noncomputable def while_iter (b : state → Bool) (body : Program0 Unit) : ℕ → Program0 Unit
  | 0     => fun _ => ⟨0, by simp⟩
  | n + 1 => fun s =>
      if b s then pbind body (fun _ => while_iter b body n) s
      else (pure () : Program0 Unit) s

-- Expectation transformer for while loops:
-- Ψ b body f W s = if b holds at s, run body and apply W; else deliver f.
noncomputable def Ψ (b : state → Bool) (body : Program0 Unit)
    (f : Unit × state → ENNReal) : (state → ENNReal) →o (state → ENNReal) where
  toFun W s := if b s then wp body (fun (_, s') => W s') s else f ((), s)
  monotone' _ _ hWW' s := by
    dsimp only
    split_ifs
    · exact MeasureTheory.lintegral_mono fun ⟨_, s'⟩ => hWW' s'
    · exact le_refl _

-- wp of while_iter n equals the n-th iterate of Ψ from ⊥.
theorem Ψ_iterate (b : state → Bool) (body : Program0 Unit)
    (f : Unit × state → ENNReal) :
    ∀ n s, wp (while_iter b body n) f s = (Ψ b body f)^[n] ⊥ s := by
  intro n
  induction n with
  | zero =>
    intro s
    simp only [Function.iterate_zero, id, Pi.bot_apply, bot_eq_zero]
    simp only [while_iter, wp]
    exact MeasureTheory.lintegral_zero_measure _
  | succ n ih =>
    intro s
    simp only [Function.iterate_succ', Function.comp]
    -- (Ψ b body f) W s unfolds by the OrderHom definition
    have hΨ : (Ψ b body f) ((Ψ b body f)^[n] ⊥) s =
              if b s then wp body (fun (_, s') => (Ψ b body f)^[n] ⊥ s') s else f ((), s) := rfl
    rw [hΨ]
    -- while_iter (n+1) s unfolds by the recursive definition
    have hws : while_iter b body (n + 1) s =
        if b s then pbind body (fun _ => while_iter b body n) s
        else (pure () : Program0 Unit) s := rfl
    simp only [wp, hws]
    split_ifs with h
    · -- b s = true: apply wp_bind + IH
      have hbind := wp_bind body (fun _ => while_iter b body n) f s
      simp only [wp] at hbind
      rw [hbind]; congr 1; ext ⟨_, s'⟩; exact ih s'
    · -- b s = false: apply wp_pure
      have hpure := wp_pure () f s
      simp only [wp] at hpure
      exact hpure

-- Ψ is ω-Scott continuous: it preserves suprema of ω-chains.
-- The key is lintegral_iSup (MCT for functions) applied to the chain of integrands.
theorem Ψ_ωScottContinuous (b : state → Bool) (body : Program0 Unit)
    (f : Unit × state → ENNReal) :
    OmegaCompletePartialOrder.ωScottContinuous (Ψ b body f) := by
  rw [OmegaCompletePartialOrder.ωScottContinuous_iff_map_ωSup_of_orderHom]
  intro c
  ext s
  have hωSup_eq : OmegaCompletePartialOrder.ωSup c = ⨆ n, (c n : state → ENNReal) := by
    apply le_antisymm
    · apply OmegaCompletePartialOrder.ωSup_le; exact le_iSup (c ·)
    · apply iSup_le; exact OmegaCompletePartialOrder.le_ωSup c
  have hωSup_map_eq :
      OmegaCompletePartialOrder.ωSup (OmegaCompletePartialOrder.Chain.map c (Ψ b body f)) =
      ⨆ n, (Ψ b body f) (c n) := by
    apply le_antisymm
    · apply OmegaCompletePartialOrder.ωSup_le
      intro n
      simp only [OmegaCompletePartialOrder.Chain.map_coe, Function.comp]
      exact le_iSup (fun n => (Ψ b body f) (c n)) n
    · apply iSup_le; intro n
      have h := OmegaCompletePartialOrder.le_ωSup (OmegaCompletePartialOrder.Chain.map c (Ψ b body f)) n
      simp only [OmegaCompletePartialOrder.Chain.map_coe, Function.comp] at h
      exact h
  -- Rewrite RHS before unfolding Ψ (avoids c.map {...} vs c.map (Ψ ...) mismatch)
  rw [hωSup_map_eq, iSup_apply]
  -- Unfold Ψ on both sides; LHS has ωSup c inside lambda, RHS is fully unfolded
  simp only [Ψ, OrderHom.coe_mk]
  -- Rewrite ωSup c to ⨆ n, c n inside the lambda using simp (works under binders)
  simp only [hωSup_eq, iSup_apply]
  split_ifs with h
  · -- b s = true: swap ⨆ and ∫ via MCT (lintegral_iSup)
    simp only [wp]
    rw [← MeasureTheory.lintegral_iSup
          (f := fun n (x : Unit × state) => c n x.2)
          (fun _ => measurable_from_top)
          (fun _ _ hmn ⟨_, s'⟩ => c.2 hmn s')]
  · -- b s = false: constant chain, sup = constant
    exact (iSup_const (a := f ((), s))).symm

-- The lfp of Ψ gives the wp of the while loop.
-- By Kleene's theorem: lfp Ψ = ⨆ n, Ψ^[n] ⊥ = ⨆ n, wp (while_iter n).
noncomputable def wp_while_val (b : state → Bool) (body : Program0 Unit)
    (f : Unit × state → ENNReal) (s : state) : ENNReal :=
  (Ψ b body f).lfp s

-- Equivalent characterization as iterated supremum
theorem wp_while_val_eq_iSup (b : state → Bool) (body : Program0 Unit)
    (f : Unit × state → ENNReal) (s : state) :
    wp_while_val b body f s = ⨆ n, wp (while_iter b body n) f s := by
  simp only [wp_while_val]
  rw [fixedPoints.lfp_eq_sSup_iterate (Ψ b body f) (Ψ_ωScottContinuous b body f)]
  rw [iSup_apply]
  congr 1; ext n; exact (Ψ_iterate b body f n s).symm

-- Unfolding rule: wp_while_val satisfies the fixed-point equation for Ψ.
theorem wp_while_unfold (b : state → Bool) (body : Program0 Unit)
    (f : Unit × state → ENNReal) (s : state) :
    wp_while_val b body f s =
      if b s then wp body (fun (_, s') => wp_while_val b body f s') s else f ((), s) := by
  simp only [wp_while_val, Ψ, OrderHom.coe_mk]
  exact congr_fun (Ψ b body f).map_lfp s |>.symm

-- Loop invariant rule: if I is a pre-fixed-point of Ψ, then wp_while_val ≤ I.
-- Concretely: if (∀ s, if b s then wp body (fun (_, s') => I s') s else f ((), s)) ≤ I s,
-- then the loop's wp is bounded by I.
theorem wp_while_invariant (b : state → Bool) (body : Program0 Unit)
    (I : state → ENNReal) (f : Unit × state → ENNReal)
    (h : ∀ s, Ψ b body f I s ≤ I s) :
    ∀ s, wp_while_val b body f s ≤ I s := by
  intro s
  simp only [wp_while_val]
  exact (Ψ b body f).lfp_le h s

-- MCT for a monotone sequence of measures: ∫⁻ f d(⨆ μ_n) = ⨆ n, ∫⁻ f dμ_n.
private theorem lintegral_iSup_measure_nat {α : Type*} [MeasurableSpace α]
    {μ : ℕ → MeasureTheory.Measure α} (hmono : Monotone μ) {f : α → ENNReal} :
    ∫⁻ a, f a ∂(⨆ n, μ n) = ⨆ n, ∫⁻ a, f a ∂μ n := by
  -- Step 1: (⨆ n, μ n) s = ⨆ n, μ n s for measurable s,
  -- proved by constructing the colimit measure ν with ν t = ⨆ n, μ n t.
  have measure_iSup_apply : ∀ s, MeasurableSet s → (⨆ n, μ n) s = ⨆ n, μ n s := fun s hs => by
    -- σ-additivity of ν uses: ⨆ n, ∑' i, g n i = ∑' i, ⨆ n, g n i (monotone g).
    -- Proof via ENNReal.tsum_eq_iSup_sum + iSup_comm + finsetSum_iSup_of_monotone.
    let ν : MeasureTheory.Measure α := MeasureTheory.Measure.ofMeasurable
        (fun t _ => ⨆ n, μ n t) (by simp)
        (fun sets hsets hdisj => by
          simp_rw [MeasureTheory.measure_iUnion hdisj hsets, ENNReal.tsum_eq_iSup_sum]
          rw [iSup_comm]
          congr 1; ext S
          exact (ENNReal.finsetSum_iSup_of_monotone fun i m n hmn =>
            MeasureTheory.Measure.le_iff.mp (hmono hmn) (sets i) (hsets i)).symm)
    have hν : ν = ⨆ n, μ n := le_antisymm
      (MeasureTheory.Measure.le_iff.mpr fun t ht => by
        have heq : ν t = ⨆ n, μ n t := MeasureTheory.Measure.ofMeasurable_apply t ht
        rw [heq]
        exact iSup_le fun n => MeasureTheory.Measure.le_iff.mp (le_iSup μ n) t ht)
      (iSup_le fun n => MeasureTheory.Measure.le_iff.mpr fun t ht => by
        have heq : ν t = ⨆ n, μ n t := MeasureTheory.Measure.ofMeasurable_apply t ht
        rw [heq]
        exact le_iSup (μ · t) n)
    rw [← hν]; exact MeasureTheory.Measure.ofMeasurable_apply s hs
  -- Step 2: g.lintegral (⨆ n, μ n) = ⨆ n, g.lintegral (μ n) for simple g.
  -- Proof: unfold lintegral = ∑ r * μ(preimage), swap mul/iSup, swap sum/iSup.
  have simp_lintegral_iSup : ∀ (g : MeasureTheory.SimpleFunc α ENNReal),
      g.lintegral (⨆ n, μ n) = ⨆ n, g.lintegral (μ n) := fun g => by
    simp only [MeasureTheory.SimpleFunc.lintegral,
      measure_iSup_apply _ (g.measurableSet_preimage _), ENNReal.mul_iSup]
    exact ENNReal.finsetSum_iSup_of_monotone fun r m n hmn =>
      mul_le_mul_left'
        (MeasureTheory.Measure.le_iff.mp (hmono hmn) (g ⁻¹' {r}) (g.measurableSet_preimage _)) r
  apply le_antisymm
  · -- ≤: unfold lintegral as sup over simple functions, use simp_lintegral_iSup
    rw [MeasureTheory.lintegral]
    apply iSup₂_le; intro g hg
    rw [simp_lintegral_iSup]
    apply iSup_le; intro n
    calc g.lintegral (μ n)
        = ∫⁻ a, g a ∂μ n := (g.lintegral_eq_lintegral _).symm
      _ ≤ ∫⁻ a, f a ∂μ n := MeasureTheory.lintegral_mono hg
      _ ≤ ⨆ n, ∫⁻ a, f a ∂μ n := le_iSup (fun n => ∫⁻ a, f a ∂μ n) n
  · -- ≥: each μ n ≤ ⨆ n, μ n so lintegral is monotone
    exact iSup_le fun n => MeasureTheory.lintegral_mono' (le_iSup μ n) le_rfl

-- Measures of while_iter approximants are monotone in n.
private theorem while_iter_measure_mono (b : state → Bool) (body : Program0 Unit) (n : ℕ) :
    ∀ s, (while_iter b body n s).1 ≤ (while_iter b body (n + 1) s).1 := by
  induction n with
  | zero => intro s; exact bot_le
  | succ n ih =>
    intro s
    -- Use change to unfold exactly one level without expanding while_iter recursively
    change (if b s then pbind body (fun _ => while_iter b body n) s
                   else (pure () : Program0 Unit) s).1 ≤
           (if b s then pbind body (fun _ => while_iter b body (n + 1)) s
                   else (pure () : Program0 Unit) s).1
    split_ifs
    · apply MeasureTheory.Measure.le_iff.mpr
      intro A hA
      have key : ∀ m, (pbind body (fun _ => while_iter b body m) s).1 A =
          ∫⁻ x, (while_iter b body m x.2).1 A ∂(body s).1 := fun m => by
        have heq : (pbind body (fun _ => while_iter b body m) s).1 =
            MeasureTheory.Measure.bind (body s).1
              (fun x => (while_iter b body m x.2).1) := rfl
        rw [heq, MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
      rw [key n, key (n + 1)]
      exact MeasureTheory.lintegral_mono
        fun ⟨_, s'⟩ => MeasureTheory.Measure.le_iff.mp (ih s') A hA
    · exact le_refl _

private theorem while_iter_measure_monotone (b : state → Bool) (body : Program0 Unit)
    (s : state) : Monotone (fun n => (while_iter b body n s).1) := by
  intro m n hmn
  induction hmn with
  | refl => exact le_refl _
  | step _ ih => exact ih.trans (while_iter_measure_mono b body _ s)

-- The while loop as a Program0: colimit of the finite approximants.
-- Its distribution at state s is the supremum of the while_iter distributions.
noncomputable def while_ (b : state → Bool) (body : Program0 Unit) : Program0 Unit :=
  fun s => ⟨⨆ n, (while_iter b body n s).1, by
    have hmono := while_iter_measure_monotone b body s
    -- Total mass: (⨆ μ_n) univ = ⨆ n, μ_n univ ≤ 1
    -- via lintegral_one and lintegral_iSup_measure_nat
    have heq : (⨆ n, (while_iter b body n s).1) Set.univ =
               ⨆ n, (while_iter b body n s).1 Set.univ := by
      have h := @lintegral_iSup_measure_nat (Unit × state) ⊤
                  (fun n => (while_iter b body n s).1) hmono (fun _ => 1)
      simp only [MeasureTheory.lintegral_one] at h
      exact h
    show (⨆ n, (while_iter b body n s).1) Set.univ ≤ 1
    rw [heq]; exact iSup_le fun n => (while_iter b body n s).2⟩

-- wp of the while loop equals the least fixed point (wp_while_val).
-- The two inequalities use: ≤ from lintegral_iSup_measure_nat, ≥ from lintegral_mono'.
theorem wp_while (b : state → Bool) (body : Program0 Unit)
    (f : Unit × state → ENNReal) (s : state) :
    wp (while_ b body) f s = wp_while_val b body f s := by
  apply le_antisymm
  · simp only [wp, while_, wp_while_val_eq_iSup]
    exact (@lintegral_iSup_measure_nat (Unit × state) ⊤
            (fun n => (while_iter b body n s).1) (while_iter_measure_monotone b body s) f).le
  · rw [wp_while_val_eq_iSup]
    apply iSup_le; intro n
    apply MeasureTheory.lintegral_mono' _ le_rfl
    -- (while_iter n s).1 ≤ ⨆ m, (while_iter m s).1 = (while_ b body s).1
    simp only [while_]
    exact le_iSup (fun m => (while_iter b body m s).1) n

theorem prfinal_myProg_1 (s : state) : prfinal myProg 1 s = 1/2 := by
  simp only [prfinal]
  -- Unfold myProg to expose the >>= chain, then reduce with wp_bind_do + wp_* rules
  simp only [myProg, wp_bind_do, wp_ite, wp_setVar, wp_getVar, wp_pure, X.set_get,
             show (2 : Nat) ≠ 1 from by decide, ite_false]
  exact prfinal_coinToss true s

-- Can say a lot more than LE. In particular partial order, and omega-cpo (even cpo?)
instance : LE (Program0 a) where
  le p q := ∀ s, (p s).1 <= (q s).1

instance : PartialOrder (Program0 a) where
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

instance : OrderBot (Program0 a) where
  bot := fun s => ⟨0, by simp⟩
  bot_le := sorry

-- Could also directly define while_F' instead without this intermediate def
noncomputable
def while_F (b : state → Bool) (body : Program0 Unit) (loop : Program0 Unit) : Program0 Unit :=
    fun s => if b s then pbind body (fun _ => loop) s else (pure () : Program0 Unit) s

theorem while_F_while_iter (b : state → Bool) (body : Program0 Unit) (n : ℕ) :
  while_iter b body n = (while_F b body)^[n] ⊥ :=
  sorry

instance : OmegaCompletePartialOrder (Program0 a) where
  ωSup := sorry
  le_ωSup := sorry
  ωSup_le := sorry

noncomputable
def while_F' (b : state → Bool) (body : Program0 Unit) : Program0 Unit →𝒄 Program0 Unit where
  toFun := while_F b body
  monotone' := sorry
  map_ωSup' := sorry

-- Why doesn't this exist?
def OmegaCompletePartialOrder.ContinuousHom.lfp [OmegaCompletePartialOrder a] [OrderBot a] (f : a →𝒄 a) :=
  OmegaCompletePartialOrder.ωSup (⟨fun n => f^[n] ⊥, sorry⟩ : OmegaCompletePartialOrder.Chain a)

-- Doesn't this exist?
def IsLfp [LE a] (f : a -> a) (x : a) := IsLeast (Function.fixedPoints f) x

theorem my_lfp_is_lfp [OmegaCompletePartialOrder a] [OrderBot a] (f : a →𝒄 a) :
  IsLfp f (f.lfp) := sorry

noncomputable
def while2 (b : state → Bool) (body : Program0 Unit) : Program0 Unit :=
  (while_F' b body).lfp

theorem all_the_same {b body} : while_ b body = while2 b body := sorry
