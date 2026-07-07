import GaudisCrypt.Language.Semantics
import GaudisCrypt.Misc

open GaudisCrypt.Language.Semantics
open GaudisCrypt.Language.Lens

-- TODO Namespace GaudisCrypt

/-!
# Probabilistic lens-ranges (`Footprint`)

The sub-probability analogue of `DetermFootprint`. A *region* of the state `m` is a set
of sub-probability kernels `m → SubProbability m`, closed under Kleisli composition
(`*`, with `pure` as identity — see the `Monoid (m → SubProbability m)` instance in
`GaudisCrypt.Language.SubProbability`) and equal to its own double commutant.

The whole lattice/complement tower (`Compl`, `from`, `PartialOrder`, `Lattice`,
`BoundedOrder`, `compl_compl`, `CompleteLattice`) is built purely from generic
monoid–centralizer facts, so it mirrors `DetermFootprint` verbatim, only over the
Kleisli monoid of kernels instead of `Function.End`. The genuinely probabilistic
content — relating a `ProgramDenotation` to a `Footprint` — lives in `ProgramDenotation.inFootprint`
and `ProgramDenotation.footprint` at the bottom of this file.
-/

structure Footprint (m : Type _) where
  updates : Set (m → SubProbability m)
  id : pure ∈ updates
  comp : f ∈ updates → g ∈ updates → (f * g) ∈ updates
  double_commutant :
    (Set.centralizer (Set.centralizer updates)) = updates

private lemma centralizer_carrier_eq (S : Set (m → SubProbability m)) :
    (Submonoid.centralizer S).carrier = Set.centralizer S := by
  ext x; simp [Submonoid.mem_centralizer_iff, Set.mem_centralizer_iff]

instance : Compl (Footprint m) where
  compl range := ⟨(Submonoid.centralizer range.updates).carrier,
    Submonoid.one_mem _,
    fun hf hg => Submonoid.mul_mem _ hf hg,
    by simp only [centralizer_carrier_eq]; exact Set.centralizer_centralizer_centralizer _⟩

def Footprint.from (generators : Set (m → SubProbability m)) : Footprint m where
  -- TODO: Write Set.centralizer instead of Submonoid.centralizer, more
  updates := Submonoid.centralizer (Submonoid.centralizer generators).carrier
  id := Submonoid.one_mem _
  comp := fun hf hg => Submonoid.mul_mem _ hf hg
  double_commutant := by
    simp only [centralizer_carrier_eq]
    exact Set.centralizer_centralizer_centralizer _

@[simp]
lemma Footprint.from_updates {m} (G : Set (m → SubProbability m)) :
    (Footprint.from G).updates = Set.centralizer (Set.centralizer G) := by
  change (Submonoid.centralizer ((Submonoid.centralizer G).carrier) : Set (m → SubProbability m))
      = Set.centralizer (Set.centralizer G)
  rw [Submonoid.coe_centralizer]
  rfl

instance : PartialOrder (Footprint m) where
  le x y := x.updates ≤ y.updates
  le_refl x := le_refl x.updates
  le_trans _ _ _ h1 h2 := le_trans h1 h2
  le_antisymm := by
    intro x y hxy hyx
    obtain ⟨xu, xid, xcomp, xdc⟩ := x
    obtain ⟨yu, yid, ycomp, ydc⟩ := y
    simp only at hxy hyx
    obtain rfl := le_antisymm hxy hyx
    rfl

instance : Lattice (Footprint m) where
  sup x y := Footprint.from (x.updates ∪ y.updates) -- double commutant of union
  inf x y := ⟨x.updates ∩ y.updates, ⟨x.id, y.id⟩,
    fun hf hg => ⟨x.comp hf.1 hg.1, y.comp hf.2 hg.2⟩, by
      apply Set.Subset.antisymm
      · apply Set.subset_inter
        · have hx := x.double_commutant
          conv_rhs => rw [← hx]
          exact Set.centralizer_subset (Set.centralizer_subset Set.inter_subset_left)
        · have hy := y.double_commutant
          conv_rhs => rw [← hy]
          exact Set.centralizer_subset (Set.centralizer_subset Set.inter_subset_right)
      · exact Set.subset_centralizer_centralizer⟩  -- intersection
  le_sup_left := fun x y => by
    change x.updates ⊆
      (Submonoid.centralizer (Submonoid.centralizer (x.updates ∪ y.updates)).carrier).carrier
    conv_lhs => rw [← x.double_commutant]
    exact Submonoid.centralizer_le (Submonoid.centralizer_le Set.subset_union_left)
  le_sup_right := fun x y => by
    change y.updates ⊆
      (Submonoid.centralizer (Submonoid.centralizer (x.updates ∪ y.updates)).carrier).carrier
    conv_lhs => rw [← y.double_commutant]
    exact Submonoid.centralizer_le (Submonoid.centralizer_le Set.subset_union_right)
  le_inf := fun _ _ _ h1 h2 => Set.subset_inter h1 h2
  sup_le := fun x y z hxz hyz => by
    change (Submonoid.centralizer (Submonoid.centralizer (x.updates ∪ y.updates)).carrier).carrier ⊆
      z.updates
    conv_rhs => rw [← z.double_commutant]
    exact Submonoid.centralizer_le
      (Submonoid.centralizer_le (Set.union_subset hxz hyz))
  inf_le_left := fun _ _ => Set.inter_subset_left
  inf_le_right := fun _ _ => Set.inter_subset_right

instance : BoundedOrder (Footprint m) where
  top := ⟨⊤, Set.mem_univ _, fun _ _ => Set.mem_univ _, by
    simp only [centralizer_carrier_eq, Set.top_eq_univ, Set.centralizer_univ]
    exact Set.centralizer_eq_top_iff_subset.mpr (Set.Subset.refl _)⟩
  bot := Footprint.from ∅
  bot_le := fun x => by
    change (Submonoid.centralizer (Submonoid.centralizer ∅).carrier).carrier ⊆ x.updates
    conv_rhs => rw [← x.double_commutant]
    exact Submonoid.centralizer_le (Submonoid.centralizer_le (Set.empty_subset _))
  le_top := fun x => Set.subset_univ _

/-- The complement (commutant) is antitone. -/
theorem Footprint.compl_le_compl {m : Type _} {R S : Footprint m} (h : R ≤ S) : Sᶜ ≤ Rᶜ := by
  show (Submonoid.centralizer S.updates).carrier ⊆ (Submonoid.centralizer R.updates).carrier
  intro x hx
  exact Submonoid.mem_centralizer_iff.mpr
    (fun g hg => Submonoid.mem_centralizer_iff.mp hx g (h hg))

theorem Footprint.compl_compl (x : Footprint a) : xᶜᶜ = x := by
  have key : ∀ {p q : Footprint a}, p.updates = q.updates → p = q := by
    intro p q h; obtain ⟨_,_,_,_⟩ := p; obtain ⟨_,_,_,_⟩ := q
    simp only at h; subst h; rfl
  apply key; simp only [Compl.compl]; exact x.double_commutant

/-- A range equals the centralizer of its own complement (double-commutant closure,
    stated with the commutant on the inside). -/
theorem Footprint.updates_eq_centralizer_compl {m : Type _} (R : Footprint m) :
    R.updates = (Submonoid.centralizer Rᶜ.updates).carrier := by
  show R.updates = (Submonoid.centralizer (Submonoid.centralizer R.updates).carrier).carrier
  exact R.double_commutant.symm

/-- **Galois connection for `from`**: `from G` is the smallest range whose updates
    contain `G`. Since `R` is double-commutant-closed, `from G ≤ R` iff `G ⊆ R.updates`. -/
theorem Footprint.from_le_iff {m : Type _} (G : Set (m → SubProbability m))
    (R : Footprint m) : Footprint.from G ≤ R ↔ G ⊆ R.updates := by
  constructor
  · intro h
    intro x hx
    apply h
    show x ∈ (Submonoid.centralizer (Submonoid.centralizer G).carrier).carrier
    simp only [centralizer_carrier_eq]
    exact Set.subset_centralizer_centralizer hx
  · intro h
    show (Submonoid.centralizer (Submonoid.centralizer G).carrier).carrier ⊆ R.updates
    conv_rhs => rw [← R.double_commutant]
    exact Submonoid.centralizer_le (Submonoid.centralizer_le h)

instance : CompleteSemilatticeSup (Footprint m) where
  sSup s := Footprint.from (⋃ x ∈ s, x.updates)
  isLUB_sSup s := by
    constructor
    · intro a ha
      change a.updates ⊆
        (Submonoid.centralizer (Submonoid.centralizer (⋃ x ∈ s, x.updates)).carrier).carrier
      conv_lhs => rw [← a.double_commutant]
      exact Submonoid.centralizer_le
        (Submonoid.centralizer_le (Set.subset_iUnion₂_of_subset a ha (le_refl _)))
    · intro b hb
      change (Submonoid.centralizer (Submonoid.centralizer (⋃ x ∈ s, x.updates)).carrier).carrier ⊆
        b.updates
      conv_rhs => rw [← b.double_commutant]
      exact Submonoid.centralizer_le
        (Submonoid.centralizer_le (Set.iUnion₂_subset (fun x hx => hb hx)))

instance : CompleteSemilatticeInf (Footprint m) where
  sInf s := ⟨⋂ x ∈ s, x.updates,
    Set.mem_iInter₂.mpr fun x hx => x.id,
    fun hf hg => Set.mem_iInter₂.mpr fun x hx =>
      x.comp (Set.mem_iInter₂.mp hf x hx) (Set.mem_iInter₂.mp hg x hx),
    by
      apply Set.Subset.antisymm
      · apply Set.subset_iInter₂
        intro x hx
        have hx_dc := x.double_commutant
        conv_rhs => rw [← hx_dc]
        exact Set.centralizer_subset (Set.centralizer_subset (Set.iInter₂_subset x hx))
      · exact Set.subset_centralizer_centralizer⟩
  isGLB_sInf s := by
    constructor
    · intro a ha; exact Set.iInter₂_subset a ha
    · intro b hb; exact Set.subset_iInter₂ (fun x hx => hb hx)

instance : CompleteLattice (Footprint m) where

lemma Footprint.from_mono {m} {G G' : Set (m → SubProbability m)} (h : G ⊆ G') :
    Footprint.from G ≤ Footprint.from G' := by
  rw [Footprint.from_le_iff]
  exact h.trans Set.subset_centralizer_centralizer


noncomputable def _root_.GaudisCrypt.Language.Lens.Lens.liftSubProbability
    {a b : Type} (lens : Lens a b) (κ : a → SubProbability a) (x : b) : SubProbability b :=
  do let a ← κ (lens.get x); return lens.set a x

noncomputable
def _root_.GaudisCrypt.Language.Lens.Lens.liftFootprint {a b} (lens : Lens a b) (range : Footprint a) : Footprint b :=
  Footprint.from (lens.liftSubProbability '' range.updates)

lemma _root_.GaudisCrypt.Language.Lens.Lens.liftFootprint_mono {a b} (lens : Lens a b) {r r' : Footprint a} (h : r ≤ r') :
    Lens.liftFootprint lens r ≤ Lens.liftFootprint lens r' := by
  have hsub : r.updates ⊆ r'.updates := h
  unfold Lens.liftFootprint
  apply Footprint.from_mono
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, hsub hg, rfl⟩

/-! ## Programs and probabilistic ranges -/

/-- A program `p` lies in the probabilistic range `R` iff it commutes with every
    kernel outside `R` (i.e. in the commutant `Rᶜ`): running an outside kernel `f`
    on the state and then `p` is the same as running `p` and then `f` on the
    resulting state. This is the sub-probability analogue of `ProgramDenotation.inRange`. -/
def _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.inFootprint {s a : Type} (p :
    ProgramDenotation s a)
    (R : Footprint s) : Prop :=
  ∀ f ∈ Rᶜ.updates,
    (fun st => do let st' ← f st; let (x, st'') ← p st'; return (x, st''))
  = (fun st => do let (x, st') ← p st; let st'' ← f st'; return (x, st''))

/-- The probabilistic range of a `Unit`-returning program: the `Footprint`
    generated by its single induced state kernel (run `p`, forget the result).
    Ported from the `rangeUnit2` sketch in `Language/Semantics.lean`. -/
noncomputable def _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.footprintUnit {s : Type}
    (p : ProgramDenotation s Unit) : Footprint s :=
  Footprint.from {fun st => do let (_, st') ← p st; return st'}

open Classical in
/-- The probabilistic range of a program `p : ProgramDenotation s a`: the `Footprint`
    generated by the family of return-value-conditioned state kernels. For each
    possible return value `y : a`, the kernel runs `p`, keeps only the mass that
    returns `y` (killing the rest with `⊥`), and forgets the result, leaving a
    kernel `s → SubProbability s`. Indexing by `y` records how the final state
    correlates with what `p` returns. Ported from the `range2` sketch in
    `Language/Semantics.lean`. -/
noncomputable def _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.footprint {s a : Type}
    (p : ProgramDenotation s a) : Footprint s :=
  Footprint.from
    (Set.range fun (y : a) (st : s) =>
      (do let (x, st') ← p st; if x = y then pure st' else ⊥ : SubProbability s))

/-! ## Litmus test: `p.inFootprint R ↔ p.footprint ≤ R`

The probabilistic analogue of the bicommutant litmus test. The key device is the
return-value slice `projK y`: post-composing a kernel into `a × s` with `projK y`
keeps only the mass that returns `y` and projects to the state. Slicing turns the
joint commutation equation defining `inFootprint` into per-`y` commutations of the
conditioned kernels `kᵧ` (the generators of `footprint`) with the commutant `Rᶜ`,
i.e. `kᵧ ∈ centralizer Rᶜ = R.updates`. The forward direction is pure slicing; the
backward direction reassembles the joint kernel from its slices, which needs the
return type `a` to be `Countable`. -/

section Litmus
open Classical MeasureTheory

/-- Return-value slice: `projK y (x, s') = pure s'` if `x = y`, else `⊥`.
    Post-composing a kernel into `a × s` keeps the `y`-returning mass and forgets `y`. -/
private noncomputable def projK {s a : Type} (y : a) : a × s → SubProbability s :=
  fun xs => if xs.1 = y then pure xs.2 else ⊥

/-- Slicing the "run outside-kernel then `p`" side gives `kᵧ ∘ₖ f`. -/
private lemma lhs_slice {s a : Type} (p : ProgramDenotation s a) (f : s → SubProbability s) (y : a)
    (st : s) :
    ((f st >>= fun st' => p st' >>= fun w => (pure (w.1, w.2) : SubProbability (a × s))) >>= projK y)
    = f st >>= (fun st' => p st' >>= projK y) := by
  rw [SubProbability.bind_assoc]; congr 1; funext st'
  rw [SubProbability.bind_assoc]; congr 1; funext w
  rw [SubProbability.pure_bind]

/-- Slicing the "run `p` then outside-kernel" side gives `f ∘ₖ kᵧ`. -/
private lemma rhs_slice {s a : Type} (p : ProgramDenotation s a) (f : s → SubProbability s) (y : a)
    (st : s) :
    ((p st >>= fun w : a × s => f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))
      >>= projK y)
    = (p st >>= projK y) >>= f := by
  rw [SubProbability.bind_assoc, SubProbability.bind_assoc]
  congr 1; funext w
  rw [SubProbability.bind_assoc]
  show (f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)) >>= projK y) = projK y w >>= f
  unfold projK
  by_cases hwy : w.1 = y
  · rw [if_pos hwy]
    rw [show (fun st'' : s => (pure (w.1, st'') : SubProbability (a × s))
              >>= fun xs : a × s => if xs.1 = y then (pure xs.2 : SubProbability s) else ⊥)
          = (pure : s → SubProbability s) from by
        funext st''; rw [SubProbability.pure_bind, if_pos hwy]]
    rw [SubProbability.bind_pure, SubProbability.pure_bind]
  · rw [if_neg hwy]
    rw [show (fun st'' : s => (pure (w.1, st'') : SubProbability (a × s))
              >>= fun xs : a × s => if xs.1 = y then (pure xs.2 : SubProbability s) else ⊥)
          = (fun _ : s => (⊥ : SubProbability s)) from by
        funext st''; rw [SubProbability.pure_bind, if_neg hwy]]
    rw [SubProbability.bind_bot, SubProbability.bot_bind]

/-- The `y`-slice of a kernel evaluates to its mass on the `{y}`-fibre rectangle. -/
private lemma slice_apply {s a : Type} (μ : SubProbability (a × s)) (y : a) (B : Set s) :
    (μ >>= projK y).1 B = μ.1 ({y} ×ˢ B) := by
  letI : MeasurableSpace (a × s) := ⊤
  letI : MeasurableSpace s := ⊤
  show (Measure.bind μ.1 (fun w => (projK y w).1)) B = μ.1 ({y} ×ˢ B)
  rw [Measure.bind_apply (by trivial) (by exact measurable_from_top.aemeasurable)]
  rw [show (fun w : a × s => (projK y w).1 B) = Set.indicator ({y} ×ˢ B) 1 from ?_]
  · rw [lintegral_indicator_one (by trivial)]
  · funext w
    unfold projK
    by_cases hwy : w.1 = y
    · rw [if_pos hwy]
      show (@MeasureTheory.Measure.dirac s ⊤ w.2) B = Set.indicator ({y} ×ˢ B) 1 w
      rw [MeasureTheory.Measure.dirac_apply' w.2 (by trivial)]
      simp only [Set.indicator, Set.mem_prod, Set.mem_singleton_iff, hwy, true_and, Pi.one_apply]
    · rw [if_neg hwy]
      show (⊥ : SubProbability s).1 B = Set.indicator ({y} ×ˢ B) 1 w
      rw [show ((⊥ : SubProbability s).1 : Measure s) = 0 from rfl]
      simp only [Measure.coe_zero, Pi.zero_apply, Set.indicator, Set.mem_prod,
        Set.mem_singleton_iff, hwy, false_and, if_false]

/-- **A kernel into `a × s` is determined by its return-value slices.**  This is the disintegration
    fact powering the backward litmus direction.  Countability-free: it goes through the discreteness
    invariant (`discreteMeasure.ext`), comparing the two kernels on singletons `{(y, s')}`, each of
    which `slice_apply` exposes as the `y`-slice evaluated at `{s'}`. -/
private lemma ext_of_slices {s a : Type} (μ ν : SubProbability (a × s))
    (h : ∀ y, μ >>= projK y = ν >>= projK y) : μ = ν := by
  apply Subtype.ext
  refine discreteMeasure.ext μ.2.2 ν.2.2 (fun z => ?_)
  obtain ⟨y, s'⟩ := z
  have key : ∀ ρ : SubProbability (a × s), ρ.1 {((y, s') : a × s)} = (ρ >>= projK y).1 {s'} :=
    fun ρ => by
      rw [slice_apply ρ y {s'}, show ({y} ×ˢ ({s'} : Set s)) = {((y, s') : a × s)} from by
        ext w; simp [Prod.ext_iff]]
  rw [key μ, key ν, h y]

/-- **Litmus test, forward (soundness)**: if `p` commutes with the commutant `Rᶜ`,
    its constructive `footprint` is contained in `R`. No countability needed — this is
    pure slicing of the commutation equation. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.footprint_le_of_inFootprint
    {s a : Type} {p : ProgramDenotation s a} {R : Footprint s}
    (h : p.inFootprint R) : p.footprint ≤ R := by
  refine (Footprint.from_le_iff _ R).mpr ?_
  rintro k ⟨y, rfl⟩
  show (fun st => p st >>= projK y) ∈ R.updates
  rw [Footprint.updates_eq_centralizer_compl R]
  refine Submonoid.mem_centralizer_iff.mpr ?_
  intro f hf
  funext st
  show (p st >>= projK y) >>= f = f st >>= (fun st' => p st' >>= projK y)
  have hjoint := congrFun (h f hf) st
  have hs : (f st >>= fun st' => p st' >>= fun w : a × s => (pure (w.1, w.2) : SubProbability (a × s)))
              >>= projK y
          = (p st >>= fun w : a × s => f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))
              >>= projK y :=
    congrArg (fun μ : SubProbability (a × s) => μ >>= projK y) hjoint
  rw [lhs_slice, rhs_slice] at hs
  exact hs.symm

/-- **Litmus test, backward (completeness)**: if `p`'s constructive `footprint` is
    contained in `R`, then `p` commutes with the commutant `Rᶜ`.  Countability-free (subtask 4):
    the joint kernel is reassembled from its slices via the discreteness invariant
    (`ext_of_slices`), not from countability of the return type. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.inFootprint_of_footprint_le
    {s a : Type} {p : ProgramDenotation s a} {R : Footprint s}
    (h : p.footprint ≤ R) : p.inFootprint R := by
  intro f hf
  have h' := (Footprint.from_le_iff _ R).mp h
  funext st
  apply ext_of_slices
  intro y
  have hky : (fun st => p st >>= projK y) ∈ R.updates := h' ⟨y, rfl⟩
  rw [Footprint.updates_eq_centralizer_compl R] at hky
  have hcomm := Submonoid.mem_centralizer_iff.mp hky f hf
  show (f st >>= fun st' => p st' >>= fun w : a × s => (pure (w.1, w.2) : SubProbability (a × s)))
         >>= projK y
     = (p st >>= fun w : a × s => f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))
         >>= projK y
  rw [lhs_slice, rhs_slice]
  exact (congrFun hcomm st).symm

/-- **Litmus test**: a program lies in the range `R` (commutes with the commutant)
    iff its constructive `footprint` is `≤ R`. Ported from the `Litmus test` note in
    `Language/Semantics.lean`. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.inFootprint_iff_footprint_le
    {s a : Type} {p : ProgramDenotation s a} {R : Footprint s} :
    p.inFootprint R ↔ p.footprint ≤ R :=
  ⟨ProgramDenotation.footprint_le_of_inFootprint, ProgramDenotation.inFootprint_of_footprint_le⟩

/-! ## Closure properties of `inFootprint` / `footprint` -/

/-- Clean reformulation of `inFootprint`: strip the trailing `pure`-repack from the
    "run outside-kernel first" side via `bind_pure`. -/
lemma inFootprint_iff_clean {s c : Type} {P : ProgramDenotation s c} {R : Footprint s} :
    P.inFootprint R ↔ ∀ f ∈ Rᶜ.updates,
      (fun st => f st >>= P)
    = (fun st => P st >>= fun w : c × s =>
        f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (c × s))) := by
  have eL : ∀ f : s → SubProbability s, (fun st => f st >>= P)
      = (fun st => f st >>= fun st' =>
          P st' >>= fun w : c × s => (pure (w.1, w.2) : SubProbability (c × s))) := fun f => by
    funext st; congr 1; funext st'; exact (SubProbability.bind_pure (P st')).symm
  constructor
  · intro h f hf; exact (eL f).trans (h f hf)
  · intro h f hf; exact (eL f).symm.trans (h f hf)

/-- **Monotonicity**: a larger range still contains the program. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.inFootprint_mono {s c : Type}
    {P : ProgramDenotation s c} {R R' : Footprint s} (h : P.inFootprint R) (hR : R ≤ R') :
    P.inFootprint R' := by
  intro f hf
  apply h
  have hsub : R'ᶜ.updates ⊆ Rᶜ.updates := by
    change (Submonoid.centralizer R'.updates).carrier ⊆ (Submonoid.centralizer R.updates).carrier
    exact Submonoid.centralizer_le hR
  exact hsub hf

/-- **Commutation composes through `bind`**: if `p` and every `q x` commute with the
    commutant `Rᶜ`, so does `p >>= q`. Pure Kleisli algebra — no countability needed.
    The slogan is `pre`/`post` (run-`f`-first / run-`f`-last) compose via `bind_assoc`,
    and the hypotheses swap `pre ↔ post` at `p` and at each `q x`. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.inFootprint_bind {s a b : Type}
    {p : ProgramDenotation s a} {q : a → ProgramDenotation s b} {R : Footprint s}
    (hp : p.inFootprint R) (hq : ∀ x, (q x).inFootprint R) : (p >>= q).inFootprint R := by
  rw [inFootprint_iff_clean]
  intro f hf
  have hp' := (inFootprint_iff_clean.mp hp) f hf
  have hq' := fun x => (inFootprint_iff_clean.mp (hq x)) f hf
  funext st
  calc f st >>= (p >>= q)
      = (f st >>= p) >>= (fun v : a × s => q v.1 v.2) := (SubProbability.bind_assoc (f st) p _).symm
    _ = (p st >>= fun w : a × s => f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))
          >>= (fun v : a × s => q v.1 v.2) := by rw [congrFun hp' st]
    _ = p st >>= fun w : a × s => f w.2 >>= fun st'' => q w.1 st'' := by
        rw [SubProbability.bind_assoc]; congr 1; funext w
        rw [SubProbability.bind_assoc]; congr 1; funext st''
        rw [SubProbability.pure_bind]
    _ = p st >>= fun w : a × s => f w.2 >>= (q w.1) := rfl
    _ = (p st >>= fun v : a × s => q v.1 v.2)
          >>= (fun u : b × s => f u.2 >>= fun st''' => (pure (u.1, st''') : SubProbability (b × s))) := by
        rw [SubProbability.bind_assoc]; congr 1; funext w
        rw [← congrFun (hq' w.1) w.2]
    _ = (p >>= q) st
          >>= (fun u : b × s => f u.2 >>= fun st''' => (pure (u.1, st''') : SubProbability (b × s))) := rfl

/-- **Range of a `bind`**: `(p >>= q).footprint ≤ p.footprint ⊔ ⨆ x, (q x).footprint`.
    The footprint of a sequenced computation is contained in `p`'s footprint together
    with the union of the continuations' footprints. Countability-free (subtask 4): the
    self-range step (`inFootprint_of_footprint_le`) no longer needs countable return types. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.footprint_bind_le {s a b : Type}
    (p : ProgramDenotation s a) (q : a → ProgramDenotation s b) :
    (p >>= q).footprint ≤ p.footprint ⊔ ⨆ x, (q x).footprint := by
  apply ProgramDenotation.footprint_le_of_inFootprint
  apply ProgramDenotation.inFootprint_bind
  · exact ProgramDenotation.inFootprint_of_footprint_le le_sup_left
  · intro x
    exact ProgramDenotation.inFootprint_of_footprint_le
      ((le_iSup (fun x => (q x).footprint) x).trans le_sup_right)

end Litmus

/-! ## Parity primitives: `Lens.footprint` and primitive ranges

The probabilistic analogues of `Lens.range` / `ProgramDenotation.inRange_pure/set/get`, mirroring
    the
`DetermFootprint` leaves so consumers can migrate. A deterministic state update embeds as a Dirac
kernel via `diracKer`; `Lens.footprint` is generated by the lens-localized ones. -/

/-- A deterministic state update `f : Function.End s` as a Dirac kernel. The Kleisli embedding
    `Function.End s ↪ (s → SubProbability s)`. -/
noncomputable def diracKer {s : Type} (f : Function.End s) : s → SubProbability s :=
  fun st => pure (f st)

/-- The `R`-orbit equivalence on `m`: `s ~ s'` iff `s'` is reachable from `s` via the
    *deterministic* updates of `R` — Dirac kernels `diracKer f ∈ R.updates`.  The `Footprint`
    analogue of `DetermFootprint.orbit_setoid`. -/
def Footprint.orbit_setoid {m : Type} (R : Footprint m) : Setoid m where
  r := Relation.EqvGen (fun s s' => ∃ f : Function.End m, diracKer f ∈ R.updates ∧ f s = s')
  iseqv := Relation.EqvGen.is_equivalence _

/-- The "global getter" of a `Footprint`: the quotient projection onto `R`-orbit classes.
    Two states read equal iff they lie in the same `R`-orbit (differ only within `R`). -/
def Footprint.global_getter {m : Type} (R : Footprint m) : Getter (Quotient R.orbit_setoid) m where
  get := Quotient.mk R.orbit_setoid

/-- The "touched" getter: `global_getter` of the commutant `Rᶜ`.  Two states read equal iff they
    differ only in `Rᶜ` — i.e. they **agree on the content `R` owns**.  For `R = fvP_proc A` this
    is `glob A` (EasyCrypt's `={glob A}` is exactly `touched_getter x = touched_getter y`). -/
def Footprint.touched_getter {m : Type} (R : Footprint m) : Getter (Quotient Rᶜ.orbit_setoid) m :=
  Rᶜ.global_getter

/-- A single deterministic `Rᶜ`-update cannot move the touched getter: `f σ` and `σ` lie in
    the same `Rᶜ`-orbit.  The pointwise engine for "`={glob A}` is preserved by writes outside
    `A`'s footprint" (e.g. oracle writes, for an oracle-disjoint `A`). -/
theorem Footprint.touched_getter_get_eq_of_mem {m : Type} {R : Footprint m}
    {f : Function.End m} (hf : diracKer f ∈ Rᶜ.updates) (σ : m) :
    R.touched_getter.get (f σ) = R.touched_getter.get σ := by
  refine (Quotient.sound ?_).symm
  show Relation.EqvGen (fun s s' => ∃ f : Function.End m, diracKer f ∈ Rᶜ.updates ∧ f s = s')
    σ (f σ)
  exact Relation.EqvGen.rel _ _ ⟨f, hf, rfl⟩

/-- A `Footprint S` is **resettable at `σ`** if it admits an `S`-update that overwrites its own
    content (`S.touched_getter`) with `σ`'s value while fixing `σ`.  This is the "`S` is a genuine,
    overwritable memory region" property: every lens footprint has it (`Lens.footprint_hasReset`),
    an abelian bicommutant one need not.  It is the frame's faithfulness witness, living on the
    (lens-derived) oracle region rather than on the adversary. -/
def Footprint.HasReset {m : Type} (S : Footprint m) (σ : m) : Prop :=
  ∃ f : Function.End m, diracKer f ∈ S.updates ∧ f σ = σ ∧
    ∀ s, S.touched_getter.get (f s) = S.touched_getter.get σ

/-! ## Observational indistinguishability through a footprint

An `R`-**test** observes a state by running one `R`-update and reading off its acceptance
probability — the total weight `SubProbability.mass` of the result.  `Footprint.indistinguishable`
is the induced observational equivalence: no `R`-test separates the two states
(`indistinguishable_iff_testsOf`).  The touched getter is *sound* for it
(`indistinguishable_of_touched_getter_eq`): states agreeing on the content `R` owns pass every
`R`-test with the same probability.  (Tests comparing the weight against an *interval* rather than
a single value separate exactly as well as the exact-weight ones formalized here.) -/

/-- Two states are **indistinguishable through `R`** when every update of `R` accepts both with
    the same total weight (`SubProbability.mass`). -/
def Footprint.indistinguishable {m : Type _} (R : Footprint m) (σ σ' : m) : Prop :=
  ∀ h ∈ R.updates, (h σ).mass = (h σ').mass

-- def Footprint.indistinguishable {s : Type} (F : Footprint s) : Setoid s where
--  r x y := ∀ f ∈ F.updates, (f x).ofEvent ⊤ = (f y).ofEvent ⊤
--  iseqv := sorry

--def Footprint.read_glob (F : Footprint s) m : Quotient (Footprint.indistinguishable F) := Quotient.mk'' m

/-- `Footprint.indistinguishable` is an equivalence relation. -/
theorem Footprint.indistinguishable_equivalence {m : Type _} (R : Footprint m) :
    Equivalence R.indistinguishable where
  refl _ _ _ := rfl
  symm h k hk := (h k hk).symm
  trans h₁ h₂ k hk := (h₁ k hk).trans (h₂ k hk)

/-- `Footprint.indistinguishable` is antitone in the footprint: a larger footprint has more
    tests, hence a finer indistinguishability. -/
theorem Footprint.indistinguishable.anti {m : Type _} {R S : Footprint m} {σ σ' : m}
    (h : S.indistinguishable σ σ') (hRS : R ≤ S) : R.indistinguishable σ σ' :=
  fun k hk => h k (hRS hk)

/-- The **tests** of a footprint: the state predicates decided by comparing the acceptance
    probability of a single `R`-update against a fixed weight. -/
def Footprint.testsOf {m : Type _} (R : Footprint m) : Set (m → Prop) :=
  { g | ∃ h ∈ R.updates, ∃ r : NNReal, ∀ σ, g σ ↔ (h σ).mass = r }

/-- Indistinguishability is exactly "passing the same tests". -/
theorem Footprint.indistinguishable_iff_testsOf {m : Type _} (R : Footprint m) (σ σ' : m) :
    R.indistinguishable σ σ' ↔ ∀ g ∈ R.testsOf, (g σ ↔ g σ') := by
  constructor
  · rintro hind g ⟨h, hh, r, hg⟩
    rw [hg σ, hg σ', hind h hh]
  · intro htests h hh
    exact ((htests _ ⟨h, hh, (h σ).mass, fun _ => Iff.rfl⟩).mp rfl).symm

/-- **Soundness of the touched getter for tests**: states with equal `R`-owned content (equal
    `R.touched_getter` — EasyCrypt's `={glob}`) are indistinguishable through `R`.  Each
    `Rᶜ`-orbit step is a deterministic outside update; every `R`-update commutes with it (the
    centralizer equation), and deterministic post-composition preserves mass
    (`SubProbability.mass_bind_dirac`). -/
theorem Footprint.indistinguishable_of_touched_getter_eq {m : Type} {R : Footprint m}
    {σ σ' : m} (hg : R.touched_getter.get σ = R.touched_getter.get σ') :
    R.indistinguishable σ σ' := by
  intro h hh
  have horb : Relation.EqvGen
      (fun s s' => ∃ f : Function.End m, diracKer f ∈ Rᶜ.updates ∧ f s = s') σ σ' :=
    Quotient.exact hg
  clear hg
  induction horb with
  | rel s s' hstep =>
      obtain ⟨f, hf, rfl⟩ := hstep
      have hf' : diracKer f ∈ (Submonoid.centralizer R.updates).carrier := hf
      have hcomm : h * diracKer f = diracKer f * h :=
        Submonoid.mem_centralizer_iff.mp hf' h hh
      have hkey : h (f s) = h s >>= fun x => (pure (f x) : SubProbability m) :=
        calc h (f s) = (pure (f s) : SubProbability m) >>= h :=
              (SubProbability.pure_bind _ _).symm
          _ = (h * diracKer f) s := rfl
          _ = (diracKer f * h) s := congrFun hcomm s
          _ = h s >>= fun x => (pure (f x) : SubProbability m) := rfl
      rw [hkey, SubProbability.mass_bind_dirac]
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The probabilistic range of a lens: generated by the Dirac kernels of its localized
    deterministic updates `lens.liftFunction g`. The sub-probability analogue of `Lens.range`. -/
noncomputable def _root_.GaudisCrypt.Language.Lens.Lens.footprint {a s : Type} (lens : Lens a s) :
    Footprint s :=
    Footprint.from (Set.range lens.liftSubProbability)
  -- Was before: Footprint.from (Set.range fun g : Function.End a => diracKer (lens.liftFunction g))

/-- Lifting a Dirac kernel along a lens is the Dirac kernel of the lifted function. -/
lemma _root_.GaudisCrypt.Language.Lens.Lens.liftSubProbability_diracKer {a s : Type}
    (lens : Lens a s) (g : Function.End a) :
    lens.liftSubProbability (diracKer g) = diracKer (lens.liftFunction g) := by
  funext st
  show (pure (g (lens.get st)) : SubProbability a) >>= (fun a' => pure (lens.set a' st))
     = pure (lens.liftFunction g st)
  rw [SubProbability.pure_bind]; rfl

/-- `diracKer (lens.liftFunction g)` is a `lens.footprint` generator: it equals
    `lens.liftSubProbability (diracKer g)`, hence lies in `lens.footprint.updates`. -/
lemma _root_.GaudisCrypt.Language.Lens.Lens.diracKer_liftFunction_mem_footprint {a s : Type}
    (lens : Lens a s) (g : Function.End a) :
    diracKer (lens.liftFunction g) ∈ lens.footprint.updates := by
  rw [Lens.footprint, Footprint.from_updates]
  exact Set.subset_centralizer_centralizer ⟨diracKer g, lens.liftSubProbability_diracKer g⟩

/-- **Kernel-shift extraction**: a program in range `R` commutes with a deterministic
    outside-update `f` (as a Dirac kernel). The `inFootprint` analogue of
        `ProgramDenotation.inRange_subprob`. -/
theorem inFootprint_subprob
    {s a : Type} {p : ProgramDenotation s a} {R : Footprint s}
    (h : p.inFootprint R) {f : s → s} (hf : diracKer f ∈ Rᶜ.updates) (σ : s) :
    p (f σ) = (p σ) >>= (fun xs : a × s => (pure (xs.1, f xs.2) : SubProbability (a × s))) := by
  have hcs := congrFun ((inFootprint_iff_clean.mp h) (diracKer f) hf) σ
  rw [show (diracKer f σ : SubProbability s) = pure (f σ) from rfl, SubProbability.pure_bind] at hcs
  rw [hcs]; congr 1; funext xs
  rw [show (diracKer f xs.2 : SubProbability s) = pure (f xs.2) from rfl, SubProbability.pure_bind]

/-- `ProgramDenotation.set v x` applied at a state: a deterministic write. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.set_apply {a s : Type}
    (v : Lens a s) (x : a) (st : s) : (ProgramDenotation.set v x) st = pure ((), v.set x st) := by
  show (pure (st, st) : SubProbability (s × s))
        >>= (fun p : s × s => (pure ((), (AsSetter.toS v).set x p.1) : SubProbability (Unit × s)))
      = pure ((), v.set x st)
  rw [SubProbability.pure_bind]; rfl

/-- `ProgramDenotation.get v` applied at a state: a read leaving the state unchanged. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.get_apply {a s : Type}
    (v : Lens a s) (st : s) : (ProgramDenotation.get v) st = pure (v.get st, st) := by
  show (pure (st, st) : SubProbability (s × s))
        >>= (fun p : s × s => (pure ((AsGetter.toG v).get p.1, p.2) : SubProbability (a × s)))
      = pure (v.get st, st)
  rw [SubProbability.pure_bind]; rfl

/-- `pure x` is in every probabilistic range — it touches no state. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.inFootprint_pure {s a : Type}
    (x : a) (R : Footprint s) : (pure x : ProgramDenotation s a).inFootprint R := by
  rw [inFootprint_iff_clean]
  intro f hf
  funext st
  show (f st >>= fun st' => (pure (x, st') : SubProbability (a × s)))
     = (pure (x, st) : SubProbability (a × s))
        >>= (fun w : a × s => f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))
  rw [SubProbability.pure_bind]

/-- `ProgramDenotation.set v x` lives in `v.footprint`. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.inFootprint_set {a s : Type}
    (v : Lens a s) (x : a) : (ProgramDenotation.set v x).inFootprint v.footprint := by
  rw [inFootprint_iff_clean]
  intro f hf
  have hmem : diracKer (v.set x) ∈ v.footprint.updates :=
    v.diracKer_liftFunction_mem_footprint (fun _ => x)
  have hcomm := (Submonoid.mem_centralizer_iff.mp hf) (diracKer (v.set x)) hmem
  funext st
  have key : (f st >>= fun st' => (pure (v.set x st') : SubProbability s)) = f (v.set x st) := by
    have hcs : (f st >>= fun st' => (pure (v.set x st') : SubProbability s))
             = (pure (v.set x st) : SubProbability s) >>= f := congrFun hcomm st
    rw [SubProbability.pure_bind] at hcs
    exact hcs
  show (f st >>= (ProgramDenotation.set v x))
     = ((ProgramDenotation.set v x) st >>= fun w : Unit × s =>
          f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (Unit × s)))
  rw [ProgramDenotation.set_apply, SubProbability.pure_bind]
  rw [show (ProgramDenotation.set v x) = (fun st' => (pure ((), v.set x st') : SubProbability (Unit
      × s)))
        from funext (fun st' => ProgramDenotation.set_apply v x st')]
  rw [← key, SubProbability.bind_assoc]
  congr 1; funext st'
  rw [SubProbability.pure_bind]

/-- `ProgramDenotation.get v` lives in `v.footprint`: it reads `v`, never writes. The extraction
    `hstar` says any commutant kernel `f` preserves `v.get` almost surely. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.inFootprint_get {a s : Type}
    (v : Lens a s) : (ProgramDenotation.get v).inFootprint v.footprint := by
  rw [inFootprint_iff_clean]
  intro f hf
  funext st
  have hmem : diracKer (v.liftFunction (fun _ => v.get st)) ∈ v.footprint.updates :=
    v.diracKer_liftFunction_mem_footprint (fun _ => v.get st)
  have hcomm := (Submonoid.mem_centralizer_iff.mp hf) (diracKer (v.liftFunction (fun _ => v.get st))) hmem
  have hstar : (f st >>= fun st' => (pure (v.set (v.get st) st') : SubProbability s)) = f st := by
    have h0 : (f st >>= fun st' => (pure (v.set (v.get st) st') : SubProbability s))
            = (pure (v.set (v.get st) st) : SubProbability s) >>= f := congrFun hcomm st
    rw [SubProbability.pure_bind] at h0
    rwa [v.get_set] at h0
  have hL : (f st >>= fun st' => (pure (v.get st', st') : SubProbability (a × s)))
          = f st >>= fun st' => (pure (v.get st, v.set (v.get st) st') : SubProbability (a × s)) := by
    conv_lhs => rw [← hstar]
    rw [SubProbability.bind_assoc]; congr 1; funext st'
    rw [SubProbability.pure_bind, v.set_get]
  have hR : (f st >>= fun st'' => (pure (v.get st, st'') : SubProbability (a × s)))
          = f st >>= fun st' => (pure (v.get st, v.set (v.get st) st') : SubProbability (a × s)) := by
    conv_lhs => rw [← hstar]
    rw [SubProbability.bind_assoc]; congr 1; funext st'
    rw [SubProbability.pure_bind]
  show (f st >>= (ProgramDenotation.get v))
     = ((ProgramDenotation.get v) st >>= fun w : a × s =>
          f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))
  rw [ProgramDenotation.get_apply, SubProbability.pure_bind]
  rw [show (ProgramDenotation.get v) = (fun st' => (pure (v.get st', st') : SubProbability (a × s)))
        from funext (fun st' => ProgramDenotation.get_apply v st')]
  rw [hL, hR]

/-- `diracKer` is a monoid homomorphism `Function.End s → (s → SubProbability s)`. -/
lemma diracKer_mul {s : Type} (p q : Function.End s) :
    diracKer p * diracKer q = diracKer (p * q) := by
  funext st
  show (pure (q st) : SubProbability s) >>= diracKer p = pure ((p * q) st)
  rw [SubProbability.pure_bind]; rfl

open MeasureTheory in
/-- **Commute two binds** — a Fubini swap for sub-probability kernels. -/
lemma bind_swap {s α γ : Type} (ν : SubProbability s) (μ : SubProbability α)
    (k : α → s → SubProbability γ) :
    (ν >>= fun st' => μ >>= fun a => k a st') = (μ >>= fun a => ν >>= fun st' => k a st') := by
  apply Subtype.ext
  letI : MeasurableSpace s := ⊤
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace γ := ⊤
  apply Measure.ext
  intro C hC
  show Measure.bind ν.1 (fun st' => (μ >>= fun a => k a st').1) C
     = Measure.bind μ.1 (fun a => (ν >>= fun st' => k a st').1) C
  rw [Measure.bind_apply hC (measurable_from_top.aemeasurable),
      Measure.bind_apply hC (measurable_from_top.aemeasurable)]
  have hL : ∀ st', (μ >>= fun a => k a st').1 C = ∫⁻ a, (k a st').1 C ∂μ.1 := fun st' => by
    rw [show (μ >>= fun a => k a st').1 = Measure.bind μ.1 (fun a => (k a st').1) from rfl,
        Measure.bind_apply hC (measurable_from_top.aemeasurable)]
  have hR : ∀ a, (ν >>= fun st' => k a st').1 C = ∫⁻ st', (k a st').1 C ∂ν.1 := fun a => by
    rw [show (ν >>= fun st' => k a st').1 = Measure.bind ν.1 (fun st' => (k a st').1) from rfl,
        Measure.bind_apply hC (measurable_from_top.aemeasurable)]
  simp only [hL, hR]
  exact lintegral_lintegral_swap_discrete μ.2.2 ν.2.2 (fun a st' => (k a st').1 C)

/-- **Disjoint lenses' localized kernels commute** (Fubini via `bind_swap`). -/
lemma _root_.GaudisCrypt.Language.Lens.Lens.liftSubProbability_comm_of_disjoint
    {a b s : Type} (v : Lens a s) (L : Lens b s) [hd : disjoint v L]
    (κ : a → SubProbability a) (ρ : b → SubProbability b) :
    v.liftSubProbability κ * L.liftSubProbability ρ
      = L.liftSubProbability ρ * v.liftSubProbability κ := by
  haveI := hd.symm
  funext x
  show (L.liftSubProbability ρ x) >>= (v.liftSubProbability κ)
     = (v.liftSubProbability κ x) >>= (L.liftSubProbability ρ)
  simp only [Lens.liftSubProbability, SubProbability.bind_assoc, SubProbability.pure_bind,
    Lens.get_of_disjoint_set v L, Lens.get_of_disjoint_set L v, hd.commute]
  exact bind_swap (ρ (L.get x)) (κ (v.get x)) (fun a' b' => pure (L.set b' (v.set a' x)))

/-- **Disjoint lenses have ranges in each other's complements**: `disjoint v L` gives
    `v.footprint ≤ (L.footprint)ᶜ`. -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.footprint_le_compl_of_disjoint
    {a b s : Type} (v : Lens a s) (L : Lens b s) [hd : disjoint v L] :
    v.footprint ≤ (L.footprint)ᶜ := by
  refine (Footprint.from_le_iff _ _).mpr ?_
  rintro _ ⟨g, rfl⟩
  show v.liftSubProbability g ∈ Submonoid.centralizer (L.footprint).updates
  rw [Submonoid.mem_centralizer_iff]
  intro k hk
  have hg : v.liftSubProbability g ∈ Set.centralizer (Set.range L.liftSubProbability) := by
    rw [Set.mem_centralizer_iff]
    rintro _ ⟨ρ, rfl⟩
    exact (v.liftSubProbability_comm_of_disjoint L g ρ).symm
  simp only [Lens.footprint, Footprint.from_updates] at hk
  exact (Set.mem_centralizer_iff.mp hk (v.liftSubProbability g) hg).symm

/-- **Every lens footprint is resettable** — the probabilistic `HasReset` analogue of
    `Lens.range_hasOrbitCollapse`.  The reset is the lens overwrite `l.set (l.get σ)`; it lands every
    state in `σ`'s `(l.footprint)ᶜ`-orbit, so `touched_getter` collapses to `σ`'s value. -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.footprint_hasReset {c m : Type} (l : Lens c m) (σ : m) :
    (l.footprint).HasReset σ := by
  refine ⟨l.liftFunction (Function.const _ (l.get σ)), ?_, ?_, ?_⟩
  · -- generator membership: diracKer (l.liftFunction (const (l.get σ))) ∈ (l.footprint).updates
    exact l.diracKer_liftFunction_mem_footprint (Function.const _ (l.get σ))
  · -- f σ = σ
    show l.set ((Function.const _ (l.get σ)) (l.get σ)) σ = σ
    simp only [Function.const_apply]
    exact l.get_set σ
  · -- ∀ s, touched_getter.get (f s) = touched_getter.get σ
    intro s
    -- The reset kernel on the complement lens that maps σ ↦ f s and lives in (l.footprint)ᶜ.
    -- diracKer g ∈ (l.footprint)ᶜ.updates = centralizer (l.footprint).updates
    have hg_mem : diracKer (l.compl.liftFunction (Function.const _ (l.compl.get s)))
        ∈ (l.footprint)ᶜ.updates := by
      haveI : disjoint l.compl l := ⟨fun st v w => by
        induction v using Quotient.inductionOn
        rename_i u
        show l.set (l.get (l.set w st)) u = l.set w (l.set (l.get st) u)
        rw [l.set_get, l.set_set]⟩
      exact Lens.footprint_le_compl_of_disjoint l.compl l
        (l.compl.diracKer_liftFunction_mem_footprint (Function.const _ (l.compl.get s)))
    -- g σ = f s  (the lens identity)
    have hg_eq : l.compl.liftFunction (Function.const _ (l.compl.get s)) σ
        = l.liftFunction (Function.const _ (l.get σ)) s := by
      show l.compl.set ((Function.const _ (l.compl.get s)) (l.compl.get σ)) σ
         = l.set ((Function.const _ (l.get σ)) (l.get s)) s
      simp only [Function.const_apply, Lens.compl, Quotient.lift_mk]
    -- Assemble the EqvGen (base step + symmetry) and close via Quotient.sound.
    apply Quotient.sound
    refine (Relation.EqvGen.rel _ _ ?_).symm
    exact ⟨l.compl.liftFunction (Function.const _ (l.compl.get s)), hg_mem, hg_eq⟩

/-- `pure` is injective on `SubProbability` (it is the Dirac embedding): `pure x = pure y → x = y`.
    Lets us extract a *plain* pointwise state equation from a Dirac-kernel commutation identity. -/
private theorem subProbability_pure_injective {a : Type} :
    Function.Injective (pure : a → SubProbability a) := by
  letI : MeasurableSpace a := ⊤
  intro x y h
  by_contra hne
  have hcoe : ((pure x : SubProbability a) : a → NNReal) x
            = ((pure y : SubProbability a) : a → NNReal) x :=
    congrFun (congrArg DFunLike.coe h) x
  have hx : ((pure x : SubProbability a) : a → NNReal) x = 1 := by
    show ((@MeasureTheory.Measure.dirac a ⊤ x) {x}).toNNReal = 1
    rw [MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_singleton x)]; rfl
  have hy : ((pure y : SubProbability a) : a → NNReal) x = 0 := by
    show ((@MeasureTheory.Measure.dirac a ⊤ y) {x}).toNNReal = 0
    rw [MeasureTheory.Measure.dirac_apply' y (MeasurableSet.of_discrete),
      Set.indicator_of_notMem (fun hmem => hne (Set.mem_singleton_iff.mp hmem).symm)]; rfl
  rw [hx, hy] at hcoe
  exact one_ne_zero hcoe


/-- **`(l.footprint)ᶜ`-updates preserve `l.get`.** Any deterministic update `f` whose Dirac kernel
    lives in the complement of `l`'s footprint fixes `l`'s content: `l.get (f a) = l.get a`. It
    commutes with the overwrite generator `l.liftFunction (const (l.get a))`, and evaluating that
    commutation at `a` (via `subProbability_pure_injective`) forces `f` to leave `l.get` fixed. -/
private theorem footprint_compl_update_preserves_get {c m : Type} (l : Lens c m)
    (f : Function.End m) (hf : diracKer f ∈ (l.footprint)ᶜ.updates) (a : m) :
    l.get (f a) = l.get a := by
  have hmem : diracKer (l.liftFunction (Function.const _ (l.get a))) ∈ (l.footprint).updates :=
    l.diracKer_liftFunction_mem_footprint (Function.const _ (l.get a))
  have hcomm := (Submonoid.mem_centralizer_iff.mp hf)
      (diracKer (l.liftFunction (Function.const _ (l.get a)))) hmem
  rw [diracKer_mul, diracKer_mul] at hcomm
  have hpt := congrFun hcomm a
  have heq : (l.liftFunction (Function.const _ (l.get a)) * f) a
           = (f * l.liftFunction (Function.const _ (l.get a))) a :=
    subProbability_pure_injective hpt
  have hPfa : (l.liftFunction (Function.const _ (l.get a)) * f) a
            = l.set (l.get a) (f a) := rfl
  have hfPa : (f * l.liftFunction (Function.const _ (l.get a))) a = f a := by
    show f (l.set ((Function.const _ (l.get a)) (l.get a)) a) = f a
    simp only [Function.const_apply]; rw [l.get_set]
  rw [hPfa, hfPa] at heq
  calc l.get (f a) = l.get (l.set (l.get a) (f a)) := by rw [heq]
    _ = l.get a := l.set_get (f a) (l.get a)

/-- The complement reset generator `l.compl.liftFunction (const (l.compl.get a))` lives in
    `(l.footprint)ᶜ.updates` — the centralizer step reused from `Lens.footprint_hasReset`. -/
private theorem footprint_compl_gen_mem {c m : Type} (l : Lens c m) (a : m) :
    diracKer (l.compl.liftFunction (Function.const _ (l.compl.get a)))
      ∈ (l.footprint)ᶜ.updates := by
  haveI : disjoint l.compl l := ⟨fun st v w => by
    induction v using Quotient.inductionOn
    rename_i u
    show l.set (l.get (l.set w st)) u = l.set w (l.set (l.get st) u)
    rw [l.set_get, l.set_set]⟩
  exact Lens.footprint_le_compl_of_disjoint l.compl l
    (l.compl.diracKer_liftFunction_mem_footprint (Function.const _ (l.compl.get a)))

/-- **`l.footprint`-updates preserve `l.compl.get`.** The `Oᶜ` mirror of
    `footprint_compl_update_preserves_get`: any `f` with `diracKer f ∈ (l.footprint).updates` leaves
    the outside-`l` content fixed, `l.compl.get (f a) = l.compl.get a`.  It commutes with the
    complement reset generator (`footprint_compl_gen_mem`), evaluated at `a`. -/
private theorem footprint_update_preserves_compl_get {c m : Type} (l : Lens c m)
    (f : Function.End m) (hf : diracKer f ∈ (l.footprint).updates) (a : m) :
    l.compl.get (f a) = l.compl.get a := by
  rw [Footprint.updates_eq_centralizer_compl l.footprint] at hf
  have hgen := footprint_compl_gen_mem l a
  have hcomm := (Submonoid.mem_centralizer_iff.mp hf)
      (diracKer (l.compl.liftFunction (Function.const _ (l.compl.get a)))) hgen
  rw [diracKer_mul, diracKer_mul] at hcomm
  have hpt := congrFun hcomm a
  have heq : (l.compl.liftFunction (Function.const _ (l.compl.get a)) * f) a
           = (f * l.compl.liftFunction (Function.const _ (l.compl.get a))) a :=
    subProbability_pure_injective hpt
  have hQfa : (l.compl.liftFunction (Function.const _ (l.compl.get a)) * f) a
            = l.compl.set (l.compl.get a) (f a) := rfl
  have hfQa : (f * l.compl.liftFunction (Function.const _ (l.compl.get a))) a = f a := by
    show f (l.compl.set ((Function.const _ (l.compl.get a)) (l.compl.get a)) a) = f a
    simp only [Function.const_apply]; rw [l.compl.get_set]
  rw [hQfa, hfQa] at heq
  calc l.compl.get (f a) = l.compl.get (l.compl.set (l.compl.get a) (f a)) := by rw [heq]
    _ = l.compl.get a := l.compl.set_get (f a) (l.compl.get a)

/-- **A lens with subsingleton content has trivial footprint.**  Its localized kernels can only
    resample the unique content value, so they are scaled identities — central in the kernel
    monoid, hence inside every footprint, in particular `⊥`. -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.footprint_eq_bot_of_subsingleton {a s : Type}
    [Subsingleton a] (l : Lens a s) : l.footprint = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [Lens.footprint, Footprint.from_le_iff]
  rintro _ ⟨κ, rfl⟩
  show l.liftSubProbability κ ∈ (Footprint.from ∅).updates
  rw [Footprint.from_updates]
  refine Set.mem_centralizer_iff.mpr fun k _ => ?_
  have hlift : ∀ τ : s, l.liftSubProbability κ τ = κ (l.get τ) >>= fun _ => pure τ := by
    intro τ
    show κ (l.get τ) >>= (fun a' => (pure (l.set a' τ) : SubProbability s)) = _
    congr 1
    funext a'
    rw [Subsingleton.elim a' (l.get τ), l.get_set]
  funext σ
  show l.liftSubProbability κ σ >>= k = k σ >>= l.liftSubProbability κ
  calc l.liftSubProbability κ σ >>= k
      = (κ (l.get σ) >>= fun _ => pure σ) >>= k := by rw [hlift]
    _ = κ (l.get σ) >>= fun _ => k σ := by
        rw [SubProbability.bind_assoc]
        congr 1; funext _; rw [SubProbability.pure_bind]
    _ = κ (l.get σ) >>= fun _ => k σ >>= fun τ => pure τ := by
        congr 1; funext _; rw [SubProbability.bind_pure]
    _ = k σ >>= fun τ => κ (l.get σ) >>= fun _ => pure τ :=
        (bind_swap (k σ) (κ (l.get σ)) (fun _ τ => pure τ)).symm
    _ = k σ >>= l.liftSubProbability κ := by
        congr 1; funext τ
        rw [hlift τ, Subsingleton.elim (l.get τ) (l.get σ)]

/-- **A lens footprint inside its own commutant is trivial.**  Self-commutation makes any two
    constant writes commute, which (evaluated at a state and read back through the lens) forces
    all content values to coincide — so the content is a subsingleton and
    `Lens.footprint_eq_bot_of_subsingleton` applies. -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.footprint_eq_bot_of_le_compl {a s : Type}
    (l : Lens a s) (h : l.footprint ≤ (l.footprint)ᶜ) : l.footprint = ⊥ := by
  by_cases hs : Nonempty s
  · haveI : Subsingleton a := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨σ⟩ := hs
      have hx := l.diracKer_liftFunction_mem_footprint (Function.const _ x)
      have hy := l.diracKer_liftFunction_mem_footprint (Function.const _ y)
      have hcomm := Submonoid.mem_centralizer_iff.mp (h hx)
        (diracKer (l.liftFunction (Function.const _ y))) hy
      rw [diracKer_mul, diracKer_mul] at hcomm
      have hpt := subProbability_pure_injective (congrFun hcomm σ)
      have hxy : l.set y (l.set x σ) = l.set x (l.set y σ) := hpt
      rw [l.set_set, l.set_set] at hxy
      calc x = l.get (l.set x σ) := (l.set_get σ x).symm
        _ = l.get (l.set y σ) := by rw [hxy]
        _ = y := l.set_get σ y
    exact l.footprint_eq_bot_of_subsingleton
  · refine le_antisymm (fun u hu => ?_) bot_le
    have : u = pure := funext fun σ => absurd ⟨σ⟩ hs
    rw [this]
    exact (⊥ : Footprint s).id

/-- **A lens footprint's touched content is its lens getter.**  For a lens `l`, the opaque orbit
    quotient `(l.footprint).touched_getter` collapses to `l.get`: two states have equal touched
    content iff they agree on `l.get`.  Lets glob endpoints state their premises via the concrete
    `l.get` instead of the quotient. -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.footprint_touched_getter_eq_iff {c m : Type}
    (l : Lens c m) (x y : m) :
    (l.footprint).touched_getter.get x = (l.footprint).touched_getter.get y ↔ l.get x = l.get y := by
  constructor
  · intro h
    -- `h` is a `Quotient.mk` equality on `(l.footprint)ᶜ`-orbits; extract the generating relation.
    have hrel := Quotient.exact h
    clear h
    induction hrel with
    | rel a b hab =>
      obtain ⟨f, hf_mem, hf_eq⟩ := hab
      rw [← hf_eq]
      exact (footprint_compl_update_preserves_get l f hf_mem a).symm
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b d _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    -- One generating step suffices: the complement reset `g` maps `x ↦ y` and lives in `(l.footprint)ᶜ`.
    apply Quotient.sound
    refine Relation.EqvGen.rel _ _ ?_
    refine ⟨l.compl.liftFunction (Function.const _ (l.compl.get y)),
      footprint_compl_gen_mem l y, ?_⟩
    show l.compl.set ((Function.const _ (l.compl.get y)) (l.compl.get x)) x = y
    simp only [Function.const_apply, Lens.compl, Quotient.lift_mk]
    rw [h, l.get_set]

theorem Footprint.touchedGetter_is_getter [Nonempty s] (lens : Lens a s) :
  ∃ f : Equiv (Quotient (lens.footprint)ᶜ.orbit_setoid) a,
    f.toFun ∘ lens.footprint.touched_getter.get = lens.get := by
  refine ⟨{
    toFun := Quotient.lift lens.get
      (fun x y hxy => (lens.footprint_touched_getter_eq_iff x y).mp (Quotient.sound hxy))
    invFun := fun v => Quotient.mk _ (lens.set v (Classical.arbitrary s))
    left_inv := Quotient.ind fun x =>
      (lens.footprint_touched_getter_eq_iff (lens.set (lens.get x) (Classical.arbitrary s)) x).mpr
        (lens.set_get (Classical.arbitrary s) (lens.get x))
    right_inv := fun v => lens.set_get (Classical.arbitrary s) v }, ?_⟩
  funext x
  rfl

/-- **A lens footprint's *complement* touched content is the complement lens's getter.**  For a lens
    `l`, `((l.footprint)ᶜ).touched_getter` collapses to `l.compl.get`: two states have equal
    outside-`l` content iff they agree on `l.compl.get`.  The `Oᶜ` companion of
    `Lens.footprint_touched_getter_eq_iff` (folds in `compl_compl`). -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.footprint_compl_touched_getter_eq_iff {c m : Type}
    (l : Lens c m) (x y : m) :
    ((l.footprint)ᶜ).touched_getter.get x = ((l.footprint)ᶜ).touched_getter.get y
      ↔ l.compl.get x = l.compl.get y := by
  -- `touched_getter` of `(l.footprint)ᶜ` is `(l.footprint)ᶜᶜ`-orbits; fold in `compl_compl`.
  show (((l.footprint)ᶜ)ᶜ).global_getter.get x = (((l.footprint)ᶜ)ᶜ).global_getter.get y
      ↔ l.compl.get x = l.compl.get y
  rw [Footprint.compl_compl]
  constructor
  · intro h
    have hrel := Quotient.exact h
    clear h
    induction hrel with
    | rel a b hab =>
      obtain ⟨f, hf_mem, hf_eq⟩ := hab
      rw [← hf_eq]
      exact (footprint_update_preserves_compl_get l f hf_mem a).symm
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b d _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    -- One generating step: the `l`-overwrite generator maps `x ↦ y` and lives in `l.footprint`.
    apply Quotient.sound
    refine Relation.EqvGen.rel _ _ ?_
    refine ⟨l.liftFunction (Function.const _ (l.get y)),
      l.diracKer_liftFunction_mem_footprint (Function.const _ (l.get y)), ?_⟩
    show l.set ((Function.const _ (l.get y)) (l.get x)) x = y
    simp only [Function.const_apply]
    -- `l.set (l.get y) x = l.compl.set (l.compl.get x) y`; then rewrite with `h` and `compl.get_set`.
    have hid : l.set (l.get y) x = l.compl.set (l.compl.get x) y := rfl
    rw [hid, h]
    exact l.compl.get_set y

/-! ## The lens converse: tests recover the lens content

For a **lens** footprint the observational equivalence coincides with the touched getter: the
*conditional abort* `Lens.testKer l x₀` (keep the state iff the lens reads `x₀`) lies in
`l.footprint` — it commutes with everything commuting with the lens *writes* — and its acceptance
mass reads the lens.  So `Footprint.indistinguishable` pins the lens content exactly: this is the
tomography converse of `Footprint.indistinguishable_of_touched_getter_eq`, which
`CounterExamples/IndistinguishableVsGlob.lean` shows fails for general (abelian) footprints. -/

open Classical in
/-- The conditional-abort **test** of a lens at `x₀`: keep the state if the lens reads `x₀`,
    abort otherwise.  Acceptance probability = "the lens reads `x₀`". -/
noncomputable def _root_.GaudisCrypt.Language.Lens.Lens.testKer {a s : Type} (l : Lens a s)
    (x₀ : a) : s → SubProbability s :=
  fun σ => if l.get σ = x₀ then pure σ else ⊥

/-- The conditional abort is an honest `l`-test: it lies in the lens footprint.  It commutes with
    any kernel `k` commuting with the constant writes, because such a `k` satisfies
    `k σ >>= (pure ∘ l.set c) = k (l.set c σ)` — its output's `l`-content is pinned by a write —
    so the abort filter passes `k`'s output through untouched (accept branch) or kills it
    entirely (reject branch). -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.testKer_mem_footprint {a s : Type}
    (l : Lens a s) (x₀ : a) : l.testKer x₀ ∈ l.footprint.updates := by
  classical
  rw [Lens.footprint, Footprint.from_updates]
  refine Set.mem_centralizer_iff.mpr (fun k hk => ?_)
  -- `k` commutes with every constant write (a lifted Dirac kernel, hence a generator)
  have hwrite : ∀ (c : a) (σ : s),
      (k σ >>= fun τ => (pure (l.set c τ) : SubProbability s)) = k (l.set c σ) := by
    intro c σ
    have hcomm := Set.mem_centralizer_iff.mp hk
      (diracKer (l.liftFunction (Function.const _ c)))
      ⟨diracKer (Function.const _ c), l.liftSubProbability_diracKer _⟩
    calc (k σ >>= fun τ => (pure (l.set c τ) : SubProbability s))
        = (diracKer (l.liftFunction (Function.const _ c)) * k) σ := rfl
      _ = (k * diracKer (l.liftFunction (Function.const _ c))) σ := congrFun hcomm σ
      _ = k (l.set c σ) := by
          show diracKer (l.liftFunction (Function.const _ c)) σ >>= k = k (l.set c σ)
          rw [show diracKer (l.liftFunction (Function.const _ c)) σ
                = (pure (l.set c σ) : SubProbability s) from rfl,
            SubProbability.pure_bind]
  funext σ
  show l.testKer x₀ σ >>= k = k σ >>= l.testKer x₀
  by_cases h : l.get σ = x₀
  · -- accept branch: both sides are `k σ`
    have hset : l.set x₀ σ = σ := by rw [← h]; exact l.get_set σ
    have hR : k σ >>= l.testKer x₀ = k σ :=
      calc k σ >>= l.testKer x₀
          = (k σ >>= fun τ => (pure (l.set x₀ τ) : SubProbability s)) >>= l.testKer x₀ := by
            rw [hwrite x₀ σ, hset]
        _ = k σ >>= fun τ => l.testKer x₀ (l.set x₀ τ) := by
            rw [SubProbability.bind_assoc]; simp only [SubProbability.pure_bind]
        _ = k σ >>= fun τ => (pure (l.set x₀ τ) : SubProbability s) := by
            refine congrArg (fun f => k σ >>= f) (funext fun τ => ?_)
            show (if l.get (l.set x₀ τ) = x₀ then (pure (l.set x₀ τ) : SubProbability s) else ⊥)
                = (pure (l.set x₀ τ) : SubProbability s)
            rw [l.set_get, if_pos rfl]
        _ = k (l.set x₀ σ) := hwrite x₀ σ
        _ = k σ := by rw [hset]
    rw [show l.testKer x₀ σ = pure σ from if_pos h, SubProbability.pure_bind, hR]
  · -- reject branch: both sides are `⊥`
    have hset : l.set (l.get σ) σ = σ := l.get_set σ
    have hR : k σ >>= l.testKer x₀ = (⊥ : SubProbability s) :=
      calc k σ >>= l.testKer x₀
          = (k σ >>= fun τ => (pure (l.set (l.get σ) τ) : SubProbability s)) >>= l.testKer x₀ := by
            rw [hwrite (l.get σ) σ, hset]
        _ = k σ >>= fun τ => l.testKer x₀ (l.set (l.get σ) τ) := by
            rw [SubProbability.bind_assoc]; simp only [SubProbability.pure_bind]
        _ = k σ >>= fun _ => (⊥ : SubProbability s) := by
            refine congrArg (fun f => k σ >>= f) (funext fun τ => ?_)
            show (if l.get (l.set (l.get σ) τ) = x₀
                then (pure (l.set (l.get σ) τ) : SubProbability s) else ⊥) = ⊥
            rw [l.set_get, if_neg h]
        _ = ⊥ := SubProbability.bind_bot _
    rw [show l.testKer x₀ σ = ⊥ from if_neg h, SubProbability.bot_bind, hR]

/-- **Tests recover the lens content**: states indistinguishable through a lens footprint have
    equal lens reads — apply the conditional abort at `l.get σ`. -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.get_eq_of_indistinguishable {a s : Type}
    {l : Lens a s} {σ σ' : s} (h : l.footprint.indistinguishable σ σ') :
    l.get σ = l.get σ' := by
  classical
  have hm := h (l.testKer (l.get σ)) (l.testKer_mem_footprint (l.get σ))
  by_contra hne
  rw [show l.testKer (l.get σ) σ = pure σ from if_pos rfl,
    show l.testKer (l.get σ) σ' = ⊥ from if_neg (fun hc => hne hc.symm),
    SubProbability.mass_pure, SubProbability.mass_bot] at hm
  exact one_ne_zero hm

/-- **On lens footprints the two notions agree**: observational indistinguishability = equal
    touched getter (= equal lens content, via `Lens.footprint_touched_getter_eq_iff`).  This is
    the tomography converse that fails for general footprints — for a *genuine memory region*,
    what the tests see is exactly what the getter reads. -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.footprint_indistinguishable_iff_touched_getter_eq
    {a s : Type} (l : Lens a s) (σ σ' : s) :
    l.footprint.indistinguishable σ σ' ↔
      l.footprint.touched_getter.get σ = l.footprint.touched_getter.get σ' :=
  ⟨fun h => (l.footprint_touched_getter_eq_iff σ σ').mpr (Lens.get_eq_of_indistinguishable h),
    Footprint.indistinguishable_of_touched_getter_eq⟩

/-- The lens-content form of the agreement. -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.footprint_indistinguishable_iff_get_eq
    {a s : Type} (l : Lens a s) (σ σ' : s) :
    l.footprint.indistinguishable σ σ' ↔ l.get σ = l.get σ' :=
  (l.footprint_indistinguishable_iff_touched_getter_eq σ σ').trans
    (l.footprint_touched_getter_eq_iff σ σ')

/-- The agreement transfers along an identification of a footprint with a lens region — the form
    consumed for *syntactic* adversaries, whose assigned region (`FVP.fvP_proc`) is a variable
    (lens) region. -/
theorem Footprint.indistinguishable_iff_touched_getter_eq_of_eq_lens {a m : Type}
    {R : Footprint m} {l : Lens a m} (hR : R = l.footprint) (σ σ' : m) :
    R.indistinguishable σ σ' ↔ R.touched_getter.get σ = R.touched_getter.get σ' := by
  subst hR
  exact l.footprint_indistinguishable_iff_touched_getter_eq σ σ'

/-- Tests pin the lens content **pointwise**: any footprint merely *containing the
    conditional-abort tests of `l`* (not necessarily all of `l.footprint`) already separates
    states by `l.get`. -/
theorem Footprint.get_eq_of_indistinguishable_of_testKer_mem {a m : Type} {R : Footprint m}
    {l : Lens a m} (htest : ∀ x₀ : a, l.testKer x₀ ∈ R.updates)
    {σ σ' : m} (h : R.indistinguishable σ σ') : l.get σ = l.get σ' := by
  classical
  have hm := h (l.testKer (l.get σ)) (htest (l.get σ))
  by_contra hne
  rw [show l.testKer (l.get σ) σ = pure σ from if_pos rfl,
    show l.testKer (l.get σ) σ' = ⊥ from if_neg (fun hc => hne hc.symm),
    SubProbability.mass_pure, SubProbability.mass_bot] at hm
  exact one_ne_zero hm

/-- `touched_getter` equality is antitone in the footprint: a smaller footprint has a coarser
    touched getter, so `S`-touched equality descends to `R`-touched equality along `R ≤ S`. -/
theorem Footprint.touched_getter_eq_of_le {m : Type} {R S : Footprint m} (h : R ≤ S)
    {σ σ' : m} (hg : S.touched_getter.get σ = S.touched_getter.get σ') :
    R.touched_getter.get σ = R.touched_getter.get σ' := by
  have horb : Relation.EqvGen (fun s s' => ∃ f : Function.End m,
      diracKer f ∈ Sᶜ.updates ∧ f s = s') σ σ' := Quotient.exact hg
  clear hg
  apply Quotient.sound
  show Relation.EqvGen (fun s s' => ∃ f : Function.End m,
      diracKer f ∈ Rᶜ.updates ∧ f s = s') σ σ'
  induction horb with
  | rel s s' hstep =>
      obtain ⟨f, hf, rfl⟩ := hstep
      exact Relation.EqvGen.rel _ _ ⟨f, Footprint.compl_le_compl h hf, rfl⟩
  | refl s => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- **Pointwise sandwich agreement**: for a footprint `R` that (i) contains `l`'s tests and
    (ii) is bounded by `l`'s region, indistinguishability through `R` **is** touched-getter
    equality — no identification `R = l.footprint` needed.  This is the form for syntactic
    over-approximations (`FVP.fvP_proc`): (ii) is the standard upper-bound computation, and (i)
    is a single generator membership (the reduced read-slices *are* the tests). -/
theorem Footprint.indistinguishable_iff_touched_getter_eq_of_sandwich {a m : Type}
    {R : Footprint m} {l : Lens a m}
    (htest : ∀ x₀ : a, l.testKer x₀ ∈ R.updates) (hle : R ≤ l.footprint) (σ σ' : m) :
    R.indistinguishable σ σ' ↔ R.touched_getter.get σ = R.touched_getter.get σ' := by
  constructor
  · intro h
    exact Footprint.touched_getter_eq_of_le hle
      ((l.footprint_touched_getter_eq_iff σ σ').mpr
        (Footprint.get_eq_of_indistinguishable_of_testKer_mem htest h))
  · exact Footprint.indistinguishable_of_touched_getter_eq

/-! ## Disjointness bridge -/


/-- **`ProgramDenotation.set v x` lives in `L.footprintᶜ`** when `v` is disjoint from `L`. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.set_inFootprint_compl_of_disjoint
    {a b s : Type} (v : Lens a s) (L : Lens b s) [disjoint v L] (x : a) :
    (ProgramDenotation.set v x).inFootprint (L.footprint)ᶜ :=
  ProgramDenotation.inFootprint_mono (ProgramDenotation.inFootprint_set v x)
      (Lens.footprint_le_compl_of_disjoint v L)

/-- **`ProgramDenotation.get v` lives in `L.footprintᶜ`** when `v` is disjoint from `L`. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.get_inFootprint_compl_of_disjoint
    {a b s : Type} (v : Lens a s) (L : Lens b s) [disjoint v L] :
    (ProgramDenotation.get v).inFootprint (L.footprint)ᶜ :=
  ProgramDenotation.inFootprint_mono (ProgramDenotation.inFootprint_get v)
      (Lens.footprint_le_compl_of_disjoint v L)

/-! ## Sampling: `ProgramDenotation.uniform`

`ProgramDenotation.uniform` lives in the trivial range `⊥` — it samples a value without touching the
    state.
Because `⊥ᶜ = univ`, this means it commutes with *every* kernel, which is a Fubini swap between the
sampling and an arbitrary state-kernel. The swap (`bind_swap`) is countability-free (subtask 4): it
goes through the discreteness invariant, so neither the sampled type nor the (possibly uncountable)
state need be countable. -/

section Uniform
open MeasureTheory

/-- `ProgramDenotation.uniform` lives in the trivial range `⊥` — it samples a value, touching no
    state.
    Needs only `Fintype α` (the sampled type), not countability of the state. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.inFootprint_uniform {s α : Type}
    [Fintype α] [Nonempty α] : (ProgramDenotation.uniform : ProgramDenotation s α).inFootprint
        ⊥ := by
  rw [inFootprint_iff_clean]
  intro f hf
  funext st
  show (f st >>= fun st' =>
          (SubProbability.uniform : SubProbability α) >>= fun a => (pure (a, st') : SubProbability (α × s)))
     = (((SubProbability.uniform : SubProbability α) >>= fun a => (pure (a, st) : SubProbability (α × s)))
          >>= fun w : α × s => f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (α × s)))
  rw [bind_swap (f st) SubProbability.uniform (fun a st' => pure (a, st'))]
  rw [SubProbability.bind_assoc]
  congr 1; funext a
  rw [SubProbability.pure_bind]

end Uniform

/-! ## Localized kernels lie in the lens's range -/

/-- **An `M`-localized kernel lies in `M.footprint`.** A kernel that reads only `M.get`, samples a
    new `M`-value, and writes it back (`ρ (M.get st) >>= fun mc' => pure (M.set mc' st)`) commutes
    with the commutant `M.footprintᶜ` — using that any such `f` preserves `M.get` a.s. and commutes
    with `M.set`, plus the Fubini swap `bind_swap` (countability-free since subtask 4). -/
theorem Mlocalized_in_footprint {c s : Type} (M : Lens c s) (ρ : c → SubProbability c) :
    (fun st => ρ (M.get st) >>= fun mc' => (pure (M.set mc' st) : SubProbability s))
      ∈ M.footprint.updates := by
  rw [Footprint.updates_eq_centralizer_compl M.footprint]
  refine Submonoid.mem_centralizer_iff.mpr ?_
  intro f hf
  have hgen : ∀ g : Function.End c, diracKer (M.liftFunction g) ∈ M.footprint.updates :=
    fun g => M.diracKer_liftFunction_mem_footprint g
  have hset : ∀ (mc' : c) (st : s),
      (f st >>= fun st' => (pure (M.set mc' st') : SubProbability s)) = f (M.set mc' st) := by
    intro mc' st
    have h0 : (f st >>= fun st' => (pure (M.set mc' st') : SubProbability s))
            = (pure (M.set mc' st) : SubProbability s) >>= f :=
      congrFun (Submonoid.mem_centralizer_iff.mp hf (diracKer (M.liftFunction (Function.const c mc')))
        (hgen (Function.const c mc'))) st
    rwa [SubProbability.pure_bind] at h0
  have hpres : ∀ st, (f st >>= fun st' => (pure (M.set (M.get st) st') : SubProbability s)) = f st := by
    intro st; rw [hset (M.get st) st, M.get_set]
  funext st
  show (ρ (M.get st) >>= fun mc' => (pure (M.set mc' st) : SubProbability s)) >>= f
     = f st >>= fun st' => ρ (M.get st') >>= fun mc' => (pure (M.set mc' st') : SubProbability s)
  have hL : ((ρ (M.get st) >>= fun mc' => (pure (M.set mc' st) : SubProbability s)) >>= f)
      = f st >>= fun st' => ρ (M.get st) >>= fun mc' => (pure (M.set mc' st') : SubProbability s) := by
    rw [SubProbability.bind_assoc]
    rw [show (fun mc' => (pure (M.set mc' st) : SubProbability s) >>= f)
          = (fun mc' => f st >>= fun st' => (pure (M.set mc' st') : SubProbability s)) from by
        funext mc'; rw [SubProbability.pure_bind, hset mc' st]]
    exact (bind_swap (f st) (ρ (M.get st))
      (fun mc' st' => (pure (M.set mc' st') : SubProbability s))).symm
  have hR : (f st >>= fun st' => ρ (M.get st') >>= fun mc' => (pure (M.set mc' st') : SubProbability s))
      = f st >>= fun st' => ρ (M.get st) >>= fun mc' => (pure (M.set mc' st') : SubProbability s) := by
    conv_lhs => rw [← hpres st]
    rw [SubProbability.bind_assoc]
    congr 1; funext st''
    rw [SubProbability.pure_bind, M.set_get]
    congr 1; funext mc'
    rw [M.set_set]
  rw [hL, hR]

/-! ## Disjoint programs commute (no orbit machinery)

Programs with disjoint probabilistic ranges can be run in either order with the same joint
`(output, state)` distribution. Unlike the `DetermFootprint` version (`commute_of_disjoint`, which
needs `HasOrbitCollapse` preconditions *and* `[Countable s]`), this follows directly from the
constructive `footprint` + litmus: slicing the joint by the return value `(x₀, y₀)` collapses each
side to a product of the return-conditioned kernels `kp`/`kq`, which commute because they live in
the disjoint ranges `R`, `R'`. After subtask 4 this needs **no countability at all** — neither the
state `s` nor the return types — since slice-reassembly (`ext_of_slices`) goes through the
discreteness invariant. -/

section Commute
open Classical

variable {s a b : Type}

/-- `p`'s state-kernel conditioned on returning `x₀` — the `x₀`-generator of `p.footprint`. -/
private noncomputable def kp (p : ProgramDenotation s a) (x0 : a) : s → SubProbability s :=
  fun st => p st >>= fun w => if w.1 = x0 then pure w.2 else ⊥

/-- `q`'s state-kernel conditioned on returning `y₀` — the `y₀`-generator of `q.footprint`. -/
private noncomputable def kq (q : ProgramDenotation s b) (y0 : b) : s → SubProbability s :=
  fun st => q st >>= fun w => if w.1 = y0 then pure w.2 else ⊥

/-- Slicing the run-`p`-then-`q` side at return `(x₀,y₀)` collapses to `kp x₀ ∘ₖ kq y₀`. -/
private lemma slice_pq (p : ProgramDenotation s a) (q : ProgramDenotation s b) (x0 : a) (y0 : b) (σ
    : s) :
    ((p σ >>= fun w1 : a × s => q w1.2 >>= fun w2 : b × s =>
        (pure ((w1.1, w2.1), w2.2) : SubProbability ((a × b) × s))) >>= projK (x0, y0))
    = kp p x0 σ >>= kq q y0 := by
  show _ = (p σ >>= fun w1 : a × s => if w1.1 = x0 then pure w1.2 else ⊥) >>= kq q y0
  rw [SubProbability.bind_assoc, SubProbability.bind_assoc]
  congr 1; funext w1
  rw [SubProbability.bind_assoc]
  by_cases hx : w1.1 = x0
  · rw [if_pos hx, SubProbability.pure_bind]
    show (q w1.2 >>= fun w2 : b × s =>
            (pure ((w1.1, w2.1), w2.2) : SubProbability ((a × b) × s)) >>= projK (x0, y0))
       = q w1.2 >>= fun w2 : b × s => if w2.1 = y0 then pure w2.2 else ⊥
    congr 1; funext w2
    rw [SubProbability.pure_bind]
    simp only [projK, hx, Prod.mk.injEq, true_and]
  · rw [if_neg hx, SubProbability.bot_bind]
    rw [show (fun w2 : b × s =>
              (pure ((w1.1, w2.1), w2.2) : SubProbability ((a × b) × s)) >>= projK (x0, y0))
          = (fun _ : b × s => (⊥ : SubProbability s)) from by
        funext w2
        rw [SubProbability.pure_bind]
        simp only [projK, hx, Prod.mk.injEq, false_and, if_false]]
    rw [SubProbability.bind_bot]

/-- Slicing the run-`q`-then-`p` side at return `(x₀,y₀)` collapses to `kq y₀ ∘ₖ kp x₀`. -/
private lemma slice_qp (p : ProgramDenotation s a) (q : ProgramDenotation s b) (x0 : a) (y0 : b) (σ
    : s) :
    ((q σ >>= fun w1 : b × s => p w1.2 >>= fun w2 : a × s =>
        (pure ((w2.1, w1.1), w2.2) : SubProbability ((a × b) × s))) >>= projK (x0, y0))
    = kq q y0 σ >>= kp p x0 := by
  show _ = (q σ >>= fun w1 : b × s => if w1.1 = y0 then pure w1.2 else ⊥) >>= kp p x0
  rw [SubProbability.bind_assoc, SubProbability.bind_assoc]
  congr 1; funext w1
  rw [SubProbability.bind_assoc]
  by_cases hy : w1.1 = y0
  · rw [if_pos hy, SubProbability.pure_bind]
    show (p w1.2 >>= fun w2 : a × s =>
            (pure ((w2.1, w1.1), w2.2) : SubProbability ((a × b) × s)) >>= projK (x0, y0))
       = p w1.2 >>= fun w2 : a × s => if w2.1 = x0 then pure w2.2 else ⊥
    congr 1; funext w2
    rw [SubProbability.pure_bind]
    simp only [projK, hy, Prod.mk.injEq, and_true]
  · rw [if_neg hy, SubProbability.bot_bind]
    rw [show (fun w2 : a × s =>
              (pure ((w2.1, w1.1), w2.2) : SubProbability ((a × b) × s)) >>= projK (x0, y0))
          = (fun _ : a × s => (⊥ : SubProbability s)) from by
        funext w2
        rw [SubProbability.pure_bind]
        simp only [projK, hy, Prod.mk.injEq, and_false, if_false]]
    rw [SubProbability.bind_bot]

/-- **Disjoint programs commute.** If `p` lives in `R`, `q` in `R'`, and `R ≤ R'ᶜ`, then `p` and
    `q` may be run in either order with the same `(output, state)` distribution. The probabilistic
    analogue of `ProgramDenotation.commute_of_disjoint` — but with **no** `HasOrbitCollapse`
        hypotheses and,
    after subtask 4, **no countability whatsoever** (the joint kernel is reassembled from its
    slices via the discreteness invariant, not from countable state or return types). -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.commute_of_disjoint_footprint
    {p : ProgramDenotation s a} {q : ProgramDenotation s b} {R R' : Footprint s}
    (hp : p.inFootprint R) (hq : q.inFootprint R') (hdisj : R ≤ R'ᶜ) :
    (p >>= fun x => q >>= fun y => pure (x, y))
  = (q >>= fun y => p >>= fun x => pure (x, y)) := by
  funext σ
  apply ext_of_slices
  rintro ⟨x0, y0⟩
  show ((p σ >>= fun w1 : a × s => q w1.2 >>= fun w2 : b × s =>
            (pure ((w1.1, w2.1), w2.2) : SubProbability ((a × b) × s))) >>= projK (x0, y0))
     = ((q σ >>= fun w1 : b × s => p w1.2 >>= fun w2 : a × s =>
            (pure ((w2.1, w1.1), w2.2) : SubProbability ((a × b) × s))) >>= projK (x0, y0))
  rw [slice_pq, slice_qp]
  have hcomm : kq q y0 * kp p x0 = kp p x0 * kq q y0 :=
    Submonoid.mem_centralizer_iff.mp
      (hdisj ((ProgramDenotation.footprint_le_of_inFootprint hp)
        ((Footprint.from_le_iff _ p.footprint).mp le_rfl ⟨x0, rfl⟩)))
      (kq q y0)
      ((ProgramDenotation.footprint_le_of_inFootprint hq)
        ((Footprint.from_le_iff _ q.footprint).mp le_rfl ⟨y0, rfl⟩))
  exact congrFun hcomm σ

/-- Lens-range specialisation of `commute_of_disjoint_footprint`. A thin wrapper (no
    `HasOrbitCollapse` to discharge, unlike the `DetermFootprint` `commute_of_disjoint_lens`),
    matching that API for drop-in migration. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.commute_of_disjoint_footprint_lens
    {c d : Type}
    {p : ProgramDenotation s a} {q : ProgramDenotation s b} {l : Lens c s} {l' : Lens d s}
    (hp : p.inFootprint l.footprint) (hq : q.inFootprint l'.footprint)
    (hdisj : l.footprint ≤ (l'.footprint)ᶜ) :
    (p >>= fun x => q >>= fun y => pure (x, y))
  = (q >>= fun y => p >>= fun x => pure (x, y)) :=
  ProgramDenotation.commute_of_disjoint_footprint hp hq hdisj

/-- When the lenses `l`, `l'` are `disjoint`, the disjointness of their probabilistic ranges is
    automatic (`Lens.footprint_le_compl_of_disjoint`), so the caller supplies only the two
    `inFootprint` confinement proofs. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.commute_of_disjoint_lenses
    {c d : Type}
    {p : ProgramDenotation s a} {q : ProgramDenotation s b} {l : Lens c s} {l' : Lens d s} [disjoint
        l l']
    (hp : p.inFootprint l.footprint) (hq : q.inFootprint l'.footprint) :
    (p >>= fun x => q >>= fun y => pure (x, y))
  = (q >>= fun y => p >>= fun x => pure (x, y)) :=
  ProgramDenotation.commute_of_disjoint_footprint hp hq (Lens.footprint_le_compl_of_disjoint l l')

/-! ### Corollaries: disjoint reads/writes commute

End-to-end payoff of the toolkit — the primitives (`inFootprint_set`/`get`) feed straight into
`commute_of_disjoint_lenses`, so independent operations on disjoint lenses may be reordered. -/

/-- Two writes to disjoint lenses commute. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.set_set_commute_of_disjoint
    {γ δ : Type} (l : Lens γ s) (l' : Lens δ s) [disjoint l l'] (x : γ) (y : δ) :
    (ProgramDenotation.set l x >>= fun a => ProgramDenotation.set l' y >>= fun b => pure (a, b))
  = (ProgramDenotation.set l' y >>= fun b => ProgramDenotation.set l x >>= fun a => pure (a, b)) :=
  ProgramDenotation.commute_of_disjoint_lenses (ProgramDenotation.inFootprint_set l x)
      (ProgramDenotation.inFootprint_set l' y)

/-- A read and a write to disjoint lenses commute. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.get_set_commute_of_disjoint
    {γ δ : Type} (l : Lens γ s) (l' : Lens δ s) [disjoint l l'] (y : δ) :
    (ProgramDenotation.get l >>= fun a => ProgramDenotation.set l' y >>= fun b => pure (a, b))
  = (ProgramDenotation.set l' y >>= fun b => ProgramDenotation.get l >>= fun a => pure (a, b)) :=
  ProgramDenotation.commute_of_disjoint_lenses (ProgramDenotation.inFootprint_get l)
      (ProgramDenotation.inFootprint_set l' y)

/-- Two reads of disjoint lenses commute. -/
theorem _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.get_get_commute_of_disjoint
    {γ δ : Type} (l : Lens γ s) (l' : Lens δ s) [disjoint l l'] :
    (ProgramDenotation.get l >>= fun a => ProgramDenotation.get l' >>= fun b => pure (a, b))
  = (ProgramDenotation.get l' >>= fun b => ProgramDenotation.get l >>= fun a => pure (a, b)) :=
  ProgramDenotation.commute_of_disjoint_lenses (ProgramDenotation.inFootprint_get l)
      (ProgramDenotation.inFootprint_get l')

end Commute


/-! ## `while_loop` confinement (fixpoint)

A while loop whose guard and body are confined to `R` is itself confined to `R`.  The loop is the
least fixpoint of `while_iteration`; each Kleene iterate is confined and confinement is closed under
ω-suprema of chains. -/

/-- `⊥` (the always-diverging program) lies in every footprint: it commutes with all kernels. -/
theorem inFootprint_bot {s a : Type} (R : Footprint s) :
    (⊥ : ProgramDenotation s a).inFootprint R := by
  rw [inFootprint_iff_clean]
  intro f hf
  funext st
  show (f st >>= fun _ => (⊥ : SubProbability (a × s)))
     = ((⊥ : SubProbability (a × s)) >>= fun w => f w.2 >>= fun st'' => pure (w.1, st''))
  rw [SubProbability.bot_bind, SubProbability.bind_bot]

open OmegaCompletePartialOrder in
/-- The "run outside kernel first" side of the `inFootprint` equation, as a map of the program `p`,
    is ω-Scott-continuous (rewritten as a `ProgramDenotation` bind so `bind_ωScottContinuous`
    applies). -/
theorem inFootprint_sideL_cont {s a : Type} (f : s → SubProbability s) :
    ωScottContinuous (fun p : ProgramDenotation s a => (fun st => f st >>= fun st' => p st')) := by
  set pf : ProgramDenotation s Unit :=
    (fun st => f st >>= fun st' => (pure ((), st') : SubProbability (Unit × s))) with hpf
  have hbind : ∀ p : ProgramDenotation s a,
      (fun st => f st >>= fun st' => p st') = pf >>= (fun _ => p) := by
    intro p; funext st
    show f st >>= (fun st' => p st')
       = (f st >>= fun st' => (pure ((), st') : SubProbability (Unit × s))) >>= (fun w => p w.2)
    rw [SubProbability.bind_assoc]; congr 1; funext st'; rw [SubProbability.pure_bind]
  rw [show (fun p : ProgramDenotation s a => (fun st => f st >>= fun st' => p st'))
      = (fun p : ProgramDenotation s a => pf >>= (fun _ => p)) from funext hbind]
  refine ProgramDenotation.bind_ωScottContinuous (fun _ => pf) (fun p _ => p) ?_
    ωScottContinuous.const
  exact ωScottContinuous.of_monotone_map_ωSup ⟨fun _ _ hle _ => hle, fun ch => by funext _; rfl⟩

open OmegaCompletePartialOrder in
/-- The "run outside kernel last" side of the `inFootprint` equation is ω-Scott-continuous. -/
theorem inFootprint_sideR_cont {s a : Type} (f : s → SubProbability s) :
    ωScottContinuous (fun p : ProgramDenotation s a =>
      (fun st => p st >>= fun w : a × s =>
        f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))) :=
  ProgramDenotation.bind_ωScottContinuous (fun p => p)
    (fun _ (w : a) (st' : s) => f st' >>= fun st'' => (pure (w, st'') : SubProbability (a × s)))
    ωScottContinuous.const ωScottContinuous.id

open OmegaCompletePartialOrder in
/-- **`inFootprint R` is closed under ω-suprema of chains.**  Both sides of the clean commutation
    equation are ω-Scott-continuous in the program, so if every chain element self-commutes, the
    supremum does too — the admissibility needed for the `while_loop` fixpoint. -/
theorem inFootprint_ωSup {s a : Type} (R : Footprint s)
    (c : Chain (ProgramDenotation s a)) (hc : ∀ n, (c n).inFootprint R) :
    (ωSup c).inFootprint R := by
  rw [inFootprint_iff_clean]
  intro f hf
  have hLeq := (inFootprint_sideL_cont (a := a) f).map_ωSup c
  have hReq := (inFootprint_sideR_cont (a := a) f).map_ωSup c
  show (fun st => f st >>= fun st' => (ωSup c) st') = _
  rw [hLeq, hReq]
  apply congrArg ωSup
  refine Chain.ext (funext fun n => ?_)
  show (fun st => f st >>= fun st' => (c n) st') = _
  exact (inFootprint_iff_clean.mp (hc n)) f hf

/-- One unrolling of the `while_iteration` operator preserves `inFootprint R` (given the guard and
    body do). -/
theorem while_iter_inFootprint {s : Type} (R : Footprint s)
    (cond : ProgramDenotation s Bool) (body : ProgramDenotation s Unit)
    (hcond : cond.inFootprint R) (hbody : body.inFootprint R)
    (g : Unit → ProgramDenotation s Unit) (hg : (g ()).inFootprint R) :
    ((while_iteration cond body) g ()).inFootprint R := by
  show ((do if ← cond then body; g () else return ()) : ProgramDenotation s Unit).inFootprint R
  apply ProgramDenotation.inFootprint_bind hcond
  intro bc
  cases bc with
  | true => exact ProgramDenotation.inFootprint_bind hbody (fun _ => hg)
  | false => exact ProgramDenotation.inFootprint_pure () R

open OmegaCompletePartialOrder in
/-- **`while_loop` confinement.**  A while loop whose guard and body are confined to `R` is itself
    confined to `R`.  The loop is the least fixpoint `⨆ₙ Fⁿ⊥` of `while_iteration`; each Kleene
    iterate is confined (`inFootprint_bot`/`while_iter_inFootprint`), and `inFootprint_ωSup` passes
    this to the supremum. -/
theorem while_loop_inFootprint {s : Type} (R : Footprint s)
    (cond : ProgramDenotation s Bool) (body : ProgramDenotation s Unit)
    (hcond : cond.inFootprint R) (hbody : body.inFootprint R) :
    (while_loop cond body).inFootprint R := by
  set F := while_iteration cond body with hF
  have hmono : Monotone (fun n => (⇑F)^[n] ⊥) := by
    apply monotone_nat_of_le_succ
    intro n
    induction n with
    | zero => simp only [Function.iterate_zero, id_eq, Function.iterate_one]; exact bot_le
    | succ m ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact F.monotone ih
  have hiter : ∀ n, ((⇑F)^[n] ⊥ ()).inFootprint R := by
    intro n
    induction n with
    | zero => exact inFootprint_bot R
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact while_iter_inFootprint R cond body hcond hbody _ ih
  show (F.lfp ()).inFootprint R
  rw [show F.lfp
      = ωSup (⟨fun n => (⇑F)^[n] ⊥, hmono⟩ : Chain (Unit → ProgramDenotation s Unit)) from rfl]
  show (ωSup (⟨fun n => (⇑F)^[n] ⊥ (), fun _ _ hmn => hmono hmn ()⟩ :
      Chain (ProgramDenotation s Unit))).inFootprint R
  exact inFootprint_ωSup R _ hiter

/-!

## Reconstructing lenses from footprints

-/

/- Note: the definition would work equivalently with other types instead of
   `Quotient Fᶜ.orbit_setoid`, as long as we have some construction of a getter
   with that type that is, for actual lens-footprints, equivalent to the original getter. -/
def Footprint.FromLens (F : Footprint s) :=
  ∃ (l : Lens (Quotient Fᶜ.orbit_setoid) s), F = l.footprint

noncomputable
def Footprint.FromLens.lens {F : Footprint s} (h : F.FromLens) :
  Lens (Quotient Fᶜ.orbit_setoid) s :=
  Classical.choose h -- Can probably be made constructive

theorem Lens.liftSubProbability_chain {lens1 : Lens a b} {lens2 : Lens b c} :
  (lens2.chain lens1).liftSubProbability = lens2.liftSubProbability ∘ lens1.liftSubProbability := by
  funext κ x
  simp only [Function.comp_apply, Lens.liftSubProbability, Lens.chain, SubProbability.bind_assoc,
    SubProbability.pure_bind]


/-- **Lifting the top footprint through a lens recovers the lens's own footprint.** -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.liftFootprint_top {a b : Type} (lens : Lens a b) :
    lens.liftFootprint ⊤ = lens.footprint := by
    simp [Lens.liftFootprint, Lens.footprint, Top.top]

@[simp]
theorem Lens.id_footprint :
  (Lens.id : Lens s s).footprint = ⊤ := by
  refine le_antisymm le_top fun k _ => ?_
  rw [Lens.footprint, Footprint.from_updates]
  exact Set.subset_centralizer_centralizer ⟨k, funext fun x => SubProbability.bind_pure (k x)⟩

/-- **A bijection lens touches all of the state**: its footprint is `⊤`.  Every kernel `k` is the
    lift of its `e`-conjugate, so the generators already exhaust the kernel monoid. -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.bijection_footprint {a b : Type} (e : a ≃ b) :
    (Lens.bijection e).footprint = ⊤ := by
  refine le_antisymm le_top fun k _ => ?_
  rw [Lens.footprint, Footprint.from_updates]
  refine Set.subset_centralizer_centralizer
    ⟨fun x => k (e x) >>= fun y => pure (e.symm y), ?_⟩
  funext σ
  show (k (e (e.symm σ)) >>= fun y => (pure (e.symm y) : SubProbability a))
      >>= (fun x => (pure (e x) : SubProbability b)) = k σ
  rw [e.apply_symm_apply, SubProbability.bind_assoc]
  calc k σ >>= (fun y =>
        (pure (e.symm y) : SubProbability a) >>= fun x => (pure (e x) : SubProbability b))
      = k σ >>= fun y => pure y := by
        congr 1; funext y; rw [SubProbability.pure_bind, e.apply_symm_apply]
    _ = k σ := SubProbability.bind_pure (k σ)

theorem Lens.footprint_fromLens {a b : Type} (l : Lens a b) : (l.footprint).FromLens := by
  sorry
