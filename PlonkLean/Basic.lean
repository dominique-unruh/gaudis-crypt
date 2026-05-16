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
  simp [prfinal, final_probability_wp, wp_uniform]
  cases b; simp
  sorry

/-
  simp only [prfinal, wp]
  have h_bind : (coinToss s).1 =
      MeasureTheory.Measure.bind
        (@PMF.toMeasure Bool ⊤ (PMF.uniformOfFintype Bool))
        (fun b' : Bool => @MeasureTheory.Measure.dirac (Bool × state) ⊤ (b', s)) := by
    simp only [coinToss, Program.uniform]
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
-/

theorem coinToss_prob (s : state) (b : Bool) :
    (coinToss s).1 {p : Bool × state | p.1 = b} = 1/2 := by calc
      (coinToss s).1 {p : Bool × state | p.1 = b} = prfinal coinToss b s := by
          simp [prfinal, Program.finalProb1, Program.finalProb, SubProbability.ofEvent]
          sorry
      _ = 1/2 := by apply prfinal_coinToss

  /-- That's more or less the same as prfinal_coinToss above. Remove? -/
  /-
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
-/

-- TODO remove (use bind)
noncomputable
def pbind {α β : Type} (mu : Program0 α) (f : α → Program0 β) : Program0 β :=
  fun s => instMonadSubProbability.bind (mu s) (fun (a, s') => f a s')

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
--     h_bind (proved by rfl) exposes (instMonadSubProbability.bind mu s).1 as the explicit
--     Measure.bind (mu s).1 (fun as' => (f as'.1 as'.2).1).
--  2. Apply Measure.lintegral_bind (Fubini for bind measures):
--       ∫⁻ x, g x ∂(Measure.bind μ κ) = ∫⁻ a, ∫⁻ x, g x ∂κ a ∂μ
--     Measurability of κ and g is trivial since all σ-algebras are ⊤.
--  3. The resulting double integral matches the unfolding of the RHS by rfl.

-- TODO remove (use bind)
/-
theorem wp_bind {α β : Type} (mu : Program0 α) (f : α → Program0 β)
    (g : β × state → ENNReal) (s : state) :
    wp (pbind mu f) g s = wp mu (fun (a, s') => wp (f a) g s') s := by
  simp only [wp, pbind]
  letI : MeasurableSpace (α × state) := ⊤
  letI : MeasurableSpace (β × state) := ⊤
  have h_bind : (instMonadSubProbability.bind (mu s) (fun (a, s') => f a s')).1 =
      MeasureTheory.Measure.bind (mu s).1 (fun as' => (f as'.1 as'.2).1) := rfl
  rw [h_bind, MeasureTheory.Measure.lintegral_bind
      measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
-/

-- wp_bind lifted to the >>= (do-notation bind) for Program0.
-- The do-notation in myProg uses Bind.bind (via StateT.bind), while wp_bind works for pbind.
-- They give the same measure: both unfold to instMonadSubProbability.bind, so Subtype.ext + simp closes the gap.

-- That's WeakestPreconditions.wp_bind now
/-
theorem wp_bind_do {α β : Type} (mu : Program0 α) (f : α → Program0 β)
    (g : β × state → ENNReal) (s : state) :
    wp (mu >>= f) g s = wp mu (fun (a, s') => wp (f a) g s') s := by
  have heq : mu >>= f = pbind mu f := by
    funext s
    apply Subtype.ext
    simp only [Bind.bind, StateT.bind, pbind]
  rw [heq]
  exact wp_bind mu f g s
-/

-- noncomputable
-- def seq {α β : Type} (p1 : Program0 α) (p2 : Program0 β) : Program0 β :=
--   p1 >>= (fun _ => p2)

-- theorem wp_seq {α β : Type} (p1 : Program s α) (p2 : Program s β)
--     (f : Program.WP s β) (st : state) :
--     (p1 *> p2).wp f = p1.wp (fun (_, s') => p2.wp f s') := by
--   simp [seqRight]
--   -- simp [wp_bind]  -- I don't understand why this doesn't rewrite...
--   sorry

theorem wp_getVar {α : Type} (v : Variable α) (f : α × state → ENNReal) (s : state) :
    Program.wp (getVar v) f s = f (v.get s, s) := by
    simp [getVar, wp_bind, wp_pure, wp_get]
       -- Why doesn't wp_bind apply?



theorem wp_setVar {α : Type} (v : Variable α) (x : α) (f : Unit × state → ENNReal) (s : state) :
    wp (setVar v x) f s = f ((), v.set x s) := by
    simp [setVar, wp_bind, wp_get, wp_set]
       -- Why doesn't wp_bind apply?


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

-- TODO: Should be defined generically: as a function of while_F (below)
--       Something like Ψ F (wp X) = wp (F X), and let F := while_F
--       Also: Ψ, while_F should be of suitable bundled types
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
    simp only [Function.iterate_zero, id,  bot_eq_zero]
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
      sorry
      -- rw [hbind]; congr 1; ext ⟨_, s'⟩; exact ih s'
    · -- b s = false: apply wp_pure
      sorry
      -- have hpure := wp_pure () f s
      -- simp only [wp] at hpure
      -- exact hpure

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
    sorry
  sorry
  --   rw [← MeasureTheory.lintegral_iSup
  --         (f := fun n (x : Unit × state) => c n x.2)
  --         (fun _ => measurable_from_top)
  --         (fun _ _ hmn ⟨_, s'⟩ => c.2 hmn s')]
  -- · -- b s = false: constant chain, sup = constant
  --   exact (iSup_const (a := f ((), s))).symm

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

-- theorem prfinal_myProg_1 (s : state) : prfinal myProg 1 s = 1/2 := by
--   simp only [prfinal]
--   -- Unfold myProg to expose the >>= chain, then reduce with wp_bind_do + wp_* rules
--   simp only [myProg, wp_bind_do, wp_ite, wp_setVar, wp_getVar, wp_pure, X.set_get,
--              show (2 : Nat) ≠ 1 from by decide, ite_false]
--   exact prfinal_coinToss true s



-- Could also directly define while_F' instead without this intermediate def
noncomputable
def while_F (b : state → Bool) (body : Program0 Unit) (loop : Program0 Unit) : Program0 Unit :=
    fun s => if b s then pbind body (fun _ => loop) s else (pure () : Program0 Unit) s

theorem while_F_while_iter (b : state → Bool) (body : Program0 Unit) (n : ℕ) :
  while_iter b body n = (while_F b body)^[n] ⊥ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

-- (⨆ μ_n) S = ⨆ μ_n S for monotone chains of measures and measurable S.
-- Derived from lintegral_iSup_measure_nat by integrating against the indicator of S.
private theorem measure_iSup_apply_nat {α : Type*} [MeasurableSpace α]
    {μ : ℕ → MeasureTheory.Measure α} (hmono : Monotone μ) {A : Set α}
    (hA : MeasurableSet A) : (⨆ n, μ n) A = ⨆ n, μ n A := by
  have h := @lintegral_iSup_measure_nat α _ μ hmono (A.indicator 1)
  simp_rw [MeasureTheory.lintegral_indicator_one hA] at h
  exact h

private theorem while_F_monotone (b : state → Bool) (body : Program0 Unit) :
    Monotone (while_F b body) := fun p q hpq s => by
  simp only [while_F]
  split_ifs with hb
  · apply MeasureTheory.Measure.le_iff.mpr
    intro A hA
    have hp : (pbind body (fun _ => p) s).1 A =
        ∫⁻ x, (p x.2).1 A ∂(body s).1 := by
      have heq : (pbind body (fun _ => p) s).1 =
          MeasureTheory.Measure.bind (body s).1 (fun x => (p x.2).1) := rfl
      rw [heq, MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
    have hq : (pbind body (fun _ => q) s).1 A =
        ∫⁻ x, (q x.2).1 A ∂(body s).1 := by
      have heq : (pbind body (fun _ => q) s).1 =
          MeasureTheory.Measure.bind (body s).1 (fun x => (q x.2).1) := rfl
      rw [heq, MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
    rw [hp, hq]
    exact MeasureTheory.lintegral_mono fun x =>
      MeasureTheory.Measure.le_iff.mp (hpq x.2) A hA
  · exact le_refl _

-- ωScott continuity of while_F: bind commutes with directed sups via MCT.
private theorem while_F_map_ωSup (b : state → Bool) (body : Program0 Unit)
    (c : OmegaCompletePartialOrder.Chain (Program0 Unit)) :
    while_F b body (OmegaCompletePartialOrder.ωSup c) =
    OmegaCompletePartialOrder.ωSup
      (c.map ⟨while_F b body, while_F_monotone b body⟩) := by sorry


noncomputable
def while_F' (b : state → Bool) (body : Program0 Unit) : Program0 Unit →𝒄 Program0 Unit where
  toFun := while_F b body
  monotone' := while_F_monotone b body
  map_ωSup' := while_F_map_ωSup b body

noncomputable
def while2 (b : state → Bool) (body : Program0 Unit) : Program0 Unit :=
  (while_F' b body).lfp

theorem all_the_same {b body} : while_ b body = while2 b body := by
  funext s
  apply Subtype.ext
  change (⨆ n, (while_iter b body n s).1) =
         ⨆ n, ((while_F b body)^[n] (⊥ : Program0 Unit) s).1
  congr 1
  funext n
  rw [while_F_while_iter]

-- theorem wp_toProgram0 (p : PMF α) f :
--   wp (toProgram0 p) f = fun s => ∑' x:α, p x * f (x,s)
--  := sorry

-- theorem wp_sampleUniform [h : Fintype α] [h : Nonempty α] (f : (α × state) -> ENNReal):
--   wp sampleUniform f = (fun s => ∑ i:α, f (i,s) / Fintype.card α) := by
--   simp [sampleUniform, wp_toProgram0]
--   sorry

theorem wp_coinToss : coinToss.wp f = (fun s => f (True, s) / 2 + f (False, s) / 2) := by
  simp [coinToss, wp_uniform]

/- A better version of the prfinal_myProg_1 proof
   It doesn't try to reduce to `prfinal coinToss` because that doesn't work canonically.
-/
theorem prfinal_myProg_1_better (s : state) : prfinal myProg 1 s = 1/2 := by
  simp only [prfinal, final_probability_wp']
  simp [myProg, wp_bind, wp_ite, wp_setVar, wp_getVar, wp_pure, X.set_get, wp_coinToss]
  sorry

-- Question: why did you define `pbind`? Doesn't `bind` already work on Program0 since the following is resolved:
#synth Monad Program0
