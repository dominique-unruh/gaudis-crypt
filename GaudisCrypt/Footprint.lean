import GaudisCrypt.Language.Semantics

open GaudisCrypt.Language.Semantics
open GaudisCrypt.Language.Lens

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
    (Submonoid.centralizer (Submonoid.centralizer updates).carrier).carrier = updates

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
      simp only [centralizer_carrier_eq]
      apply Set.Subset.antisymm
      · apply Set.subset_inter
        · have hx := x.double_commutant
          simp only [centralizer_carrier_eq] at hx
          conv_rhs => rw [← hx]
          exact Set.centralizer_subset (Set.centralizer_subset Set.inter_subset_left)
        · have hy := y.double_commutant
          simp only [centralizer_carrier_eq] at hy
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
      simp only [centralizer_carrier_eq]
      apply Set.Subset.antisymm
      · apply Set.subset_iInter₂
        intro x hx
        have hx_dc := x.double_commutant
        simp only [centralizer_carrier_eq] at hx_dc
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

/-- The probabilistic range of a lens: generated by the Dirac kernels of its localized
    deterministic updates `lens.liftFunction g`. The sub-probability analogue of `Lens.range`. -/
noncomputable def _root_.GaudisCrypt.Language.Lens.Lens.footprint {a s : Type} (lens : Lens a s) :
    Footprint s :=
  Footprint.from (Set.range fun g : Function.End a => diracKer (lens.liftFunction g))

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
    (Footprint.from_le_iff (Set.range fun g : Function.End a => diracKer (v.liftFunction g))
      v.footprint).mp le_rfl ⟨fun _ => x, rfl⟩
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
    (Footprint.from_le_iff (Set.range fun g : Function.End a => diracKer (v.liftFunction g))
      v.footprint).mp le_rfl ⟨fun _ => v.get st, rfl⟩
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

/-! ## Disjointness bridge -/

/-- `diracKer` is a monoid homomorphism `Function.End s → (s → SubProbability s)`. -/
lemma diracKer_mul {s : Type} (p q : Function.End s) :
    diracKer p * diracKer q = diracKer (p * q) := by
  funext st
  show (pure (q st) : SubProbability s) >>= diracKer p = pure ((p * q) st)
  rw [SubProbability.pure_bind]; rfl

/-- **Disjoint lenses have ranges in each other's complements**: if `disjoint v L`, then every
    `v`-localized kernel commutes with every `L`-localized kernel, so `v.footprint ≤ (L.footprint)ᶜ`.
    The sub-probability analogue of `Lens.range_le_compl_of_disjoint`. -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.footprint_le_compl_of_disjoint
    {a b s : Type} (v : Lens a s) (L : Lens b s) [hd : disjoint v L] :
    v.footprint ≤ (L.footprint)ᶜ := by
  refine (Footprint.from_le_iff _ _).mpr ?_
  rintro _ ⟨g, rfl⟩
  show diracKer (v.liftFunction g) ∈ Submonoid.centralizer (L.footprint).updates
  rw [Submonoid.mem_centralizer_iff]
  intro k hk
  have hjmem : diracKer (v.liftFunction g)
      ∈ Submonoid.centralizer (Set.range fun h : Function.End b => diracKer (L.liftFunction h)) := by
    rw [Submonoid.mem_centralizer_iff]
    rintro _ ⟨h, rfl⟩
    rw [diracKer_mul, diracKer_mul]
    congr 1
    show L.liftFunction h ∘ v.liftFunction g = v.liftFunction g ∘ L.liftFunction h
    funext σ
    show L.liftFunction h (v.liftFunction g σ) = v.liftFunction g (L.liftFunction h σ)
    letI := hd.symm
    simp only [Lens.liftFunction]
    have hL_get : L.get (v.set (g (v.get σ)) σ) = L.get σ := Lens.get_of_disjoint_set L v _ σ
    have hv_get : v.get (L.set (h (L.get σ)) σ) = v.get σ := Lens.get_of_disjoint_set v L _ σ
    rw [hL_get, hv_get]
    exact (hd.commute σ (g (v.get σ)) (h (L.get σ))).symm
  exact (Submonoid.mem_centralizer_iff.mp hk (diracKer (v.liftFunction g)) hjmem).symm

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

/-- **Commute two binds** — a Fubini swap for sub-probability kernels.  Countability-free
    (subtask 4): the swap goes through the discreteness invariant (`lintegral_lintegral_swap_discrete`
    / `ENNReal.tsum_comm`), not σ-finiteness or product-σ-algebra measurability. -/
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
    fun g => (Footprint.from_le_iff _ M.footprint).mp le_rfl ⟨g, rfl⟩
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
