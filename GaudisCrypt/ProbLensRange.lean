import GaudisCrypt.Language.Semantics

open GaudisCrypt.Language.Semantics
open GaudisCrypt.Language.Lens

/-!
# Probabilistic lens-ranges (`ProbLensRange`)

The sub-probability analogue of `TotLensRange`. A *region* of the state `m` is a set
of sub-probability kernels `m → SubProbability m`, closed under Kleisli composition
(`*`, with `pure` as identity — see the `Monoid (m → SubProbability m)` instance in
`GaudisCrypt.Language.SubProbability`) and equal to its own double commutant.

The whole lattice/complement tower (`Compl`, `from`, `PartialOrder`, `Lattice`,
`BoundedOrder`, `compl_compl`, `CompleteLattice`) is built purely from generic
monoid–centralizer facts, so it mirrors `TotLensRange` verbatim, only over the
Kleisli monoid of kernels instead of `Function.End`. The genuinely probabilistic
content — relating a `Program` to a `ProbLensRange` — lives in `Program.inProbRange`
and `Program.probRange` at the bottom of this file.
-/

structure ProbLensRange (m : Type _) where
  updates : Set (m → SubProbability m)
  id : pure ∈ updates
  comp : f ∈ updates → g ∈ updates → (f * g) ∈ updates
  double_commutant :
    (Submonoid.centralizer (Submonoid.centralizer updates).carrier).carrier = updates

private lemma centralizer_carrier_eq (S : Set (m → SubProbability m)) :
    (Submonoid.centralizer S).carrier = Set.centralizer S := by
  ext x; simp [Submonoid.mem_centralizer_iff, Set.mem_centralizer_iff]

instance : Compl (ProbLensRange m) where
  compl range := ⟨(Submonoid.centralizer range.updates).carrier,
    Submonoid.one_mem _,
    fun hf hg => Submonoid.mul_mem _ hf hg,
    by simp only [centralizer_carrier_eq]; exact Set.centralizer_centralizer_centralizer _⟩

def ProbLensRange.from (generators : Set (m → SubProbability m)) : ProbLensRange m where
  updates := Submonoid.centralizer (Submonoid.centralizer generators).carrier
  id := Submonoid.one_mem _
  comp := fun hf hg => Submonoid.mul_mem _ hf hg
  double_commutant := by
    simp only [centralizer_carrier_eq]
    exact Set.centralizer_centralizer_centralizer _

instance : PartialOrder (ProbLensRange m) where
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

instance : Lattice (ProbLensRange m) where
  sup x y := ProbLensRange.from (x.updates ∪ y.updates) -- double commutant of union
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

instance : BoundedOrder (ProbLensRange m) where
  top := ⟨⊤, Set.mem_univ _, fun _ _ => Set.mem_univ _, by
    simp only [centralizer_carrier_eq, Set.top_eq_univ, Set.centralizer_univ]
    exact Set.centralizer_eq_top_iff_subset.mpr (Set.Subset.refl _)⟩
  bot := ProbLensRange.from ∅
  bot_le := fun x => by
    change (Submonoid.centralizer (Submonoid.centralizer ∅).carrier).carrier ⊆ x.updates
    conv_rhs => rw [← x.double_commutant]
    exact Submonoid.centralizer_le (Submonoid.centralizer_le (Set.empty_subset _))
  le_top := fun x => Set.subset_univ _

theorem ProbLensRange.compl_compl (x : ProbLensRange a) : xᶜᶜ = x := by
  have key : ∀ {p q : ProbLensRange a}, p.updates = q.updates → p = q := by
    intro p q h; obtain ⟨_,_,_,_⟩ := p; obtain ⟨_,_,_,_⟩ := q
    simp only at h; subst h; rfl
  apply key; simp only [Compl.compl]; exact x.double_commutant

/-- A range equals the centralizer of its own complement (double-commutant closure,
    stated with the commutant on the inside). -/
theorem ProbLensRange.updates_eq_centralizer_compl {m : Type _} (R : ProbLensRange m) :
    R.updates = (Submonoid.centralizer Rᶜ.updates).carrier := by
  show R.updates = (Submonoid.centralizer (Submonoid.centralizer R.updates).carrier).carrier
  exact R.double_commutant.symm

/-- **Galois connection for `from`**: `from G` is the smallest range whose updates
    contain `G`. Since `R` is double-commutant-closed, `from G ≤ R` iff `G ⊆ R.updates`. -/
theorem ProbLensRange.from_le_iff {m : Type _} (G : Set (m → SubProbability m))
    (R : ProbLensRange m) : ProbLensRange.from G ≤ R ↔ G ⊆ R.updates := by
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

instance : CompleteSemilatticeSup (ProbLensRange m) where
  sSup s := ProbLensRange.from (⋃ x ∈ s, x.updates)
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

instance : CompleteSemilatticeInf (ProbLensRange m) where
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

instance : CompleteLattice (ProbLensRange m) where

/-! ## Programs and probabilistic ranges -/

/-- A program `p` lies in the probabilistic range `R` iff it commutes with every
    kernel outside `R` (i.e. in the commutant `Rᶜ`): running an outside kernel `f`
    on the state and then `p` is the same as running `p` and then `f` on the
    resulting state. This is the sub-probability analogue of `Program.inRange`. -/
def _root_.GaudisCrypt.Language.Semantics.Program.inProbRange {s a : Type} (p : Program s a)
    (R : ProbLensRange s) : Prop :=
  ∀ f ∈ Rᶜ.updates,
    (fun st => do let st' ← f st; let (x, st'') ← p st'; return (x, st''))
  = (fun st => do let (x, st') ← p st; let st'' ← f st'; return (x, st''))

/-- The probabilistic range of a `Unit`-returning program: the `ProbLensRange`
    generated by its single induced state kernel (run `p`, forget the result).
    Ported from the `rangeUnit2` sketch in `Language/Semantics.lean`. -/
noncomputable def _root_.GaudisCrypt.Language.Semantics.Program.probRangeUnit {s : Type}
    (p : Program s Unit) : ProbLensRange s :=
  ProbLensRange.from {fun st => do let (_, st') ← p st; return st'}

open Classical in
/-- The probabilistic range of a program `p : Program s a`: the `ProbLensRange`
    generated by the family of return-value-conditioned state kernels. For each
    possible return value `y : a`, the kernel runs `p`, keeps only the mass that
    returns `y` (killing the rest with `⊥`), and forgets the result, leaving a
    kernel `s → SubProbability s`. Indexing by `y` records how the final state
    correlates with what `p` returns. Ported from the `range2` sketch in
    `Language/Semantics.lean`. -/
noncomputable def _root_.GaudisCrypt.Language.Semantics.Program.probRange {s a : Type}
    (p : Program s a) : ProbLensRange s :=
  ProbLensRange.from
    (Set.range fun (y : a) (st : s) =>
      (do let (x, st') ← p st; if x = y then pure st' else ⊥ : SubProbability s))

/-! ## Litmus test: `p.inProbRange R ↔ p.probRange ≤ R`

The probabilistic analogue of the bicommutant litmus test. The key device is the
return-value slice `projK y`: post-composing a kernel into `a × s` with `projK y`
keeps only the mass that returns `y` and projects to the state. Slicing turns the
joint commutation equation defining `inProbRange` into per-`y` commutations of the
conditioned kernels `kᵧ` (the generators of `probRange`) with the commutant `Rᶜ`,
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
private lemma lhs_slice {s a : Type} (p : Program s a) (f : s → SubProbability s) (y : a) (st : s) :
    ((f st >>= fun st' => p st' >>= fun w => (pure (w.1, w.2) : SubProbability (a × s))) >>= projK y)
    = f st >>= (fun st' => p st' >>= projK y) := by
  rw [SubProbability.bind_assoc]; congr 1; funext st'
  rw [SubProbability.bind_assoc]; congr 1; funext w
  rw [SubProbability.pure_bind]

/-- Slicing the "run `p` then outside-kernel" side gives `f ∘ₖ kᵧ`. -/
private lemma rhs_slice {s a : Type} (p : Program s a) (f : s → SubProbability s) (y : a) (st : s) :
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
    its constructive `probRange` is contained in `R`. No countability needed — this is
    pure slicing of the commutation equation. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.probRange_le_of_inProbRange
    {s a : Type} {p : Program s a} {R : ProbLensRange s}
    (h : p.inProbRange R) : p.probRange ≤ R := by
  refine (ProbLensRange.from_le_iff _ R).mpr ?_
  rintro k ⟨y, rfl⟩
  show (fun st => p st >>= projK y) ∈ R.updates
  rw [ProbLensRange.updates_eq_centralizer_compl R]
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

/-- **Litmus test, backward (completeness)**: if `p`'s constructive `probRange` is
    contained in `R`, then `p` commutes with the commutant `Rᶜ`.  Countability-free (subtask 4):
    the joint kernel is reassembled from its slices via the discreteness invariant
    (`ext_of_slices`), not from countability of the return type. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.inProbRange_of_probRange_le
    {s a : Type} {p : Program s a} {R : ProbLensRange s}
    (h : p.probRange ≤ R) : p.inProbRange R := by
  intro f hf
  have h' := (ProbLensRange.from_le_iff _ R).mp h
  funext st
  apply ext_of_slices
  intro y
  have hky : (fun st => p st >>= projK y) ∈ R.updates := h' ⟨y, rfl⟩
  rw [ProbLensRange.updates_eq_centralizer_compl R] at hky
  have hcomm := Submonoid.mem_centralizer_iff.mp hky f hf
  show (f st >>= fun st' => p st' >>= fun w : a × s => (pure (w.1, w.2) : SubProbability (a × s)))
         >>= projK y
     = (p st >>= fun w : a × s => f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))
         >>= projK y
  rw [lhs_slice, rhs_slice]
  exact (congrFun hcomm st).symm

/-- **Litmus test**: a program lies in the range `R` (commutes with the commutant)
    iff its constructive `probRange` is `≤ R`. Ported from the `Litmus test` note in
    `Language/Semantics.lean`. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.inProbRange_iff_probRange_le
    {s a : Type} {p : Program s a} {R : ProbLensRange s} :
    p.inProbRange R ↔ p.probRange ≤ R :=
  ⟨Program.probRange_le_of_inProbRange, Program.inProbRange_of_probRange_le⟩

/-! ## Closure properties of `inProbRange` / `probRange` -/

/-- Clean reformulation of `inProbRange`: strip the trailing `pure`-repack from the
    "run outside-kernel first" side via `bind_pure`. -/
lemma inProbRange_iff_clean {s c : Type} {P : Program s c} {R : ProbLensRange s} :
    P.inProbRange R ↔ ∀ f ∈ Rᶜ.updates,
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
theorem _root_.GaudisCrypt.Language.Semantics.Program.inProbRange_mono {s c : Type}
    {P : Program s c} {R R' : ProbLensRange s} (h : P.inProbRange R) (hR : R ≤ R') :
    P.inProbRange R' := by
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
theorem _root_.GaudisCrypt.Language.Semantics.Program.inProbRange_bind {s a b : Type}
    {p : Program s a} {q : a → Program s b} {R : ProbLensRange s}
    (hp : p.inProbRange R) (hq : ∀ x, (q x).inProbRange R) : (p >>= q).inProbRange R := by
  rw [inProbRange_iff_clean]
  intro f hf
  have hp' := (inProbRange_iff_clean.mp hp) f hf
  have hq' := fun x => (inProbRange_iff_clean.mp (hq x)) f hf
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

/-- **Range of a `bind`**: `(p >>= q).probRange ≤ p.probRange ⊔ ⨆ x, (q x).probRange`.
    The footprint of a sequenced computation is contained in `p`'s footprint together
    with the union of the continuations' footprints. Countability-free (subtask 4): the
    self-range step (`inProbRange_of_probRange_le`) no longer needs countable return types. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.probRange_bind_le {s a b : Type}
    (p : Program s a) (q : a → Program s b) :
    (p >>= q).probRange ≤ p.probRange ⊔ ⨆ x, (q x).probRange := by
  apply Program.probRange_le_of_inProbRange
  apply Program.inProbRange_bind
  · exact Program.inProbRange_of_probRange_le le_sup_left
  · intro x
    exact Program.inProbRange_of_probRange_le
      ((le_iSup (fun x => (q x).probRange) x).trans le_sup_right)

end Litmus

/-! ## Parity primitives: `Lens.probRange` and primitive ranges

The probabilistic analogues of `Lens.range` / `Program.inRange_pure/set/get`, mirroring the
`TotLensRange` leaves so consumers can migrate. A deterministic state update embeds as a Dirac
kernel via `diracKer`; `Lens.probRange` is generated by the lens-localized ones. -/

/-- A deterministic state update `f : Function.End s` as a Dirac kernel. The Kleisli embedding
    `Function.End s ↪ (s → SubProbability s)`. -/
noncomputable def diracKer {s : Type} (f : Function.End s) : s → SubProbability s :=
  fun st => pure (f st)

/-- The probabilistic range of a lens: generated by the Dirac kernels of its localized
    deterministic updates `lens.update g`. The sub-probability analogue of `Lens.range`. -/
noncomputable def _root_.GaudisCrypt.Language.Lens.Lens.probRange {a s : Type} (lens : Lens a s) :
    ProbLensRange s :=
  ProbLensRange.from (Set.range fun g : Function.End a => diracKer (lens.update g))

/-- `Program.set v x` applied at a state: a deterministic write. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.set_apply {a s : Type}
    (v : Lens a s) (x : a) (st : s) : (Program.set v x) st = pure ((), v.set x st) := by
  show (pure (st, st) : SubProbability (s × s))
        >>= (fun p : s × s => (pure ((), (AsSetter.toS v).set x p.1) : SubProbability (Unit × s)))
      = pure ((), v.set x st)
  rw [SubProbability.pure_bind]; rfl

/-- `Program.get v` applied at a state: a read leaving the state unchanged. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.get_apply {a s : Type}
    (v : Lens a s) (st : s) : (Program.get v) st = pure (v.get st, st) := by
  show (pure (st, st) : SubProbability (s × s))
        >>= (fun p : s × s => (pure ((AsGetter.toG v).get p.1, p.2) : SubProbability (a × s)))
      = pure (v.get st, st)
  rw [SubProbability.pure_bind]; rfl

/-- `pure x` is in every probabilistic range — it touches no state. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.inProbRange_pure {s a : Type}
    (x : a) (R : ProbLensRange s) : (pure x : Program s a).inProbRange R := by
  rw [inProbRange_iff_clean]
  intro f hf
  funext st
  show (f st >>= fun st' => (pure (x, st') : SubProbability (a × s)))
     = (pure (x, st) : SubProbability (a × s))
        >>= (fun w : a × s => f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))
  rw [SubProbability.pure_bind]

/-- `Program.set v x` lives in `v.probRange`. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.inProbRange_set {a s : Type}
    (v : Lens a s) (x : a) : (Program.set v x).inProbRange v.probRange := by
  rw [inProbRange_iff_clean]
  intro f hf
  have hmem : diracKer (v.set x) ∈ v.probRange.updates :=
    (ProbLensRange.from_le_iff (Set.range fun g : Function.End a => diracKer (v.update g))
      v.probRange).mp le_rfl ⟨fun _ => x, rfl⟩
  have hcomm := (Submonoid.mem_centralizer_iff.mp hf) (diracKer (v.set x)) hmem
  funext st
  have key : (f st >>= fun st' => (pure (v.set x st') : SubProbability s)) = f (v.set x st) := by
    have hcs : (f st >>= fun st' => (pure (v.set x st') : SubProbability s))
             = (pure (v.set x st) : SubProbability s) >>= f := congrFun hcomm st
    rw [SubProbability.pure_bind] at hcs
    exact hcs
  show (f st >>= (Program.set v x))
     = ((Program.set v x) st >>= fun w : Unit × s =>
          f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (Unit × s)))
  rw [Program.set_apply, SubProbability.pure_bind]
  rw [show (Program.set v x) = (fun st' => (pure ((), v.set x st') : SubProbability (Unit × s)))
        from funext (fun st' => Program.set_apply v x st')]
  rw [← key, SubProbability.bind_assoc]
  congr 1; funext st'
  rw [SubProbability.pure_bind]

/-- `Program.get v` lives in `v.probRange`: it reads `v`, never writes. The extraction
    `hstar` says any commutant kernel `f` preserves `v.get` almost surely. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.inProbRange_get {a s : Type}
    (v : Lens a s) : (Program.get v).inProbRange v.probRange := by
  rw [inProbRange_iff_clean]
  intro f hf
  funext st
  have hmem : diracKer (v.update (fun _ => v.get st)) ∈ v.probRange.updates :=
    (ProbLensRange.from_le_iff (Set.range fun g : Function.End a => diracKer (v.update g))
      v.probRange).mp le_rfl ⟨fun _ => v.get st, rfl⟩
  have hcomm := (Submonoid.mem_centralizer_iff.mp hf) (diracKer (v.update (fun _ => v.get st))) hmem
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
  show (f st >>= (Program.get v))
     = ((Program.get v) st >>= fun w : a × s =>
          f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))
  rw [Program.get_apply, SubProbability.pure_bind]
  rw [show (Program.get v) = (fun st' => (pure (v.get st', st') : SubProbability (a × s)))
        from funext (fun st' => Program.get_apply v st')]
  rw [hL, hR]

/-! ## Disjointness bridge -/

/-- `diracKer` is a monoid homomorphism `Function.End s → (s → SubProbability s)`. -/
lemma diracKer_mul {s : Type} (p q : Function.End s) :
    diracKer p * diracKer q = diracKer (p * q) := by
  funext st
  show (pure (q st) : SubProbability s) >>= diracKer p = pure ((p * q) st)
  rw [SubProbability.pure_bind]; rfl

/-- **Disjoint lenses have ranges in each other's complements**: if `disjoint v L`, then every
    `v`-localized kernel commutes with every `L`-localized kernel, so `v.probRange ≤ (L.probRange)ᶜ`.
    The sub-probability analogue of `Lens.range_le_compl_of_disjoint`. -/
theorem _root_.GaudisCrypt.Language.Lens.Lens.probRange_le_compl_of_disjoint
    {a b s : Type} (v : Lens a s) (L : Lens b s) [hd : disjoint v L] :
    v.probRange ≤ (L.probRange)ᶜ := by
  refine (ProbLensRange.from_le_iff _ _).mpr ?_
  rintro _ ⟨g, rfl⟩
  show diracKer (v.update g) ∈ Submonoid.centralizer (L.probRange).updates
  rw [Submonoid.mem_centralizer_iff]
  intro k hk
  have hjmem : diracKer (v.update g)
      ∈ Submonoid.centralizer (Set.range fun h : Function.End b => diracKer (L.update h)) := by
    rw [Submonoid.mem_centralizer_iff]
    rintro _ ⟨h, rfl⟩
    rw [diracKer_mul, diracKer_mul]
    congr 1
    show L.update h ∘ v.update g = v.update g ∘ L.update h
    funext σ
    show L.update h (v.update g σ) = v.update g (L.update h σ)
    letI := hd.symm
    simp only [Lens.update]
    have hL_get : L.get (v.set (g (v.get σ)) σ) = L.get σ := Lens.get_of_disjoint_set L v _ σ
    have hv_get : v.get (L.set (h (L.get σ)) σ) = v.get σ := Lens.get_of_disjoint_set v L _ σ
    rw [hL_get, hv_get]
    exact (hd.commute σ (g (v.get σ)) (h (L.get σ))).symm
  exact (Submonoid.mem_centralizer_iff.mp hk (diracKer (v.update g)) hjmem).symm

/-- **`Program.set v x` lives in `L.probRangeᶜ`** when `v` is disjoint from `L`. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.set_inProbRange_compl_of_disjoint
    {a b s : Type} (v : Lens a s) (L : Lens b s) [disjoint v L] (x : a) :
    (Program.set v x).inProbRange (L.probRange)ᶜ :=
  Program.inProbRange_mono (Program.inProbRange_set v x) (Lens.probRange_le_compl_of_disjoint v L)

/-- **`Program.get v` lives in `L.probRangeᶜ`** when `v` is disjoint from `L`. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.get_inProbRange_compl_of_disjoint
    {a b s : Type} (v : Lens a s) (L : Lens b s) [disjoint v L] :
    (Program.get v).inProbRange (L.probRange)ᶜ :=
  Program.inProbRange_mono (Program.inProbRange_get v) (Lens.probRange_le_compl_of_disjoint v L)

/-! ## Sampling: `Program.uniform`

`Program.uniform` lives in the trivial range `⊥` — it samples a value without touching the state.
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

/-- `Program.uniform` lives in the trivial range `⊥` — it samples a value, touching no state.
    Needs only `Fintype α` (the sampled type), not countability of the state. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.inProbRange_uniform {s α : Type}
    [Fintype α] [Nonempty α] : (Program.uniform : Program s α).inProbRange ⊥ := by
  rw [inProbRange_iff_clean]
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

/-! ## Disjoint programs commute (no orbit machinery)

Programs with disjoint probabilistic ranges can be run in either order with the same joint
`(output, state)` distribution. Unlike the `TotLensRange` version (`commute_of_disjoint`, which
needs `HasOrbitCollapse` preconditions *and* `[Countable s]`), this follows directly from the
constructive `probRange` + litmus: slicing the joint by the return value `(x₀, y₀)` collapses each
side to a product of the return-conditioned kernels `kp`/`kq`, which commute because they live in
the disjoint ranges `R`, `R'`. After subtask 4 this needs **no countability at all** — neither the
state `s` nor the return types — since slice-reassembly (`ext_of_slices`) goes through the
discreteness invariant. -/

section Commute
open Classical

variable {s a b : Type}

/-- `p`'s state-kernel conditioned on returning `x₀` — the `x₀`-generator of `p.probRange`. -/
private noncomputable def kp (p : Program s a) (x0 : a) : s → SubProbability s :=
  fun st => p st >>= fun w => if w.1 = x0 then pure w.2 else ⊥

/-- `q`'s state-kernel conditioned on returning `y₀` — the `y₀`-generator of `q.probRange`. -/
private noncomputable def kq (q : Program s b) (y0 : b) : s → SubProbability s :=
  fun st => q st >>= fun w => if w.1 = y0 then pure w.2 else ⊥

/-- Slicing the run-`p`-then-`q` side at return `(x₀,y₀)` collapses to `kp x₀ ∘ₖ kq y₀`. -/
private lemma slice_pq (p : Program s a) (q : Program s b) (x0 : a) (y0 : b) (σ : s) :
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
private lemma slice_qp (p : Program s a) (q : Program s b) (x0 : a) (y0 : b) (σ : s) :
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
    analogue of `Program.commute_of_disjoint` — but with **no** `HasOrbitCollapse` hypotheses and,
    after subtask 4, **no countability whatsoever** (the joint kernel is reassembled from its
    slices via the discreteness invariant, not from countable state or return types). -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.commute_of_disjoint_prob
    {p : Program s a} {q : Program s b} {R R' : ProbLensRange s}
    (hp : p.inProbRange R) (hq : q.inProbRange R') (hdisj : R ≤ R'ᶜ) :
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
      (hdisj ((Program.probRange_le_of_inProbRange hp)
        ((ProbLensRange.from_le_iff _ p.probRange).mp le_rfl ⟨x0, rfl⟩)))
      (kq q y0)
      ((Program.probRange_le_of_inProbRange hq)
        ((ProbLensRange.from_le_iff _ q.probRange).mp le_rfl ⟨y0, rfl⟩))
  exact congrFun hcomm σ

/-- Lens-range specialisation of `commute_of_disjoint_prob`. A thin wrapper (no
    `HasOrbitCollapse` to discharge, unlike the `TotLensRange` `commute_of_disjoint_lens`),
    matching that API for drop-in migration. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.commute_of_disjoint_prob_lens
    {c d : Type}
    {p : Program s a} {q : Program s b} {l : Lens c s} {l' : Lens d s}
    (hp : p.inProbRange l.probRange) (hq : q.inProbRange l'.probRange)
    (hdisj : l.probRange ≤ (l'.probRange)ᶜ) :
    (p >>= fun x => q >>= fun y => pure (x, y))
  = (q >>= fun y => p >>= fun x => pure (x, y)) :=
  Program.commute_of_disjoint_prob hp hq hdisj

/-- When the lenses `l`, `l'` are `disjoint`, the disjointness of their probabilistic ranges is
    automatic (`Lens.probRange_le_compl_of_disjoint`), so the caller supplies only the two
    `inProbRange` confinement proofs. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.commute_of_disjoint_lenses
    {c d : Type}
    {p : Program s a} {q : Program s b} {l : Lens c s} {l' : Lens d s} [disjoint l l']
    (hp : p.inProbRange l.probRange) (hq : q.inProbRange l'.probRange) :
    (p >>= fun x => q >>= fun y => pure (x, y))
  = (q >>= fun y => p >>= fun x => pure (x, y)) :=
  Program.commute_of_disjoint_prob hp hq (Lens.probRange_le_compl_of_disjoint l l')

/-! ### Corollaries: disjoint reads/writes commute

End-to-end payoff of the toolkit — the primitives (`inProbRange_set`/`get`) feed straight into
`commute_of_disjoint_lenses`, so independent operations on disjoint lenses may be reordered. -/

/-- Two writes to disjoint lenses commute. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.set_set_commute_of_disjoint
    {γ δ : Type} (l : Lens γ s) (l' : Lens δ s) [disjoint l l'] (x : γ) (y : δ) :
    (Program.set l x >>= fun a => Program.set l' y >>= fun b => pure (a, b))
  = (Program.set l' y >>= fun b => Program.set l x >>= fun a => pure (a, b)) :=
  Program.commute_of_disjoint_lenses (Program.inProbRange_set l x) (Program.inProbRange_set l' y)

/-- A read and a write to disjoint lenses commute. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.get_set_commute_of_disjoint
    {γ δ : Type} (l : Lens γ s) (l' : Lens δ s) [disjoint l l'] (y : δ) :
    (Program.get l >>= fun a => Program.set l' y >>= fun b => pure (a, b))
  = (Program.set l' y >>= fun b => Program.get l >>= fun a => pure (a, b)) :=
  Program.commute_of_disjoint_lenses (Program.inProbRange_get l) (Program.inProbRange_set l' y)

/-- Two reads of disjoint lenses commute. -/
theorem _root_.GaudisCrypt.Language.Semantics.Program.get_get_commute_of_disjoint
    {γ δ : Type} (l : Lens γ s) (l' : Lens δ s) [disjoint l l'] :
    (Program.get l >>= fun a => Program.get l' >>= fun b => pure (a, b))
  = (Program.get l' >>= fun b => Program.get l >>= fun a => pure (a, b)) :=
  Program.commute_of_disjoint_lenses (Program.inProbRange_get l) (Program.inProbRange_get l')

end Commute
