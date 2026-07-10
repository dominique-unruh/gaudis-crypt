import GaudisCrypt.Language.Modules.InductiveFunctions
import GaudisCrypt.Language.Footprint

/-!
# `fvP`: the computed-footprint (free-variables) layer over `Footprint`

The probabilistic re-incarnation of the old `FV` development (now quarantined as
`CounterExamples/FV.lean`), rebased from the deterministic `DetermFootprint`/`Function.End`
foundation onto `Footprint` and the Kleisli monoid of sub-probability kernels
`m → SubProbability m`.

It instantiates the generic `InductiveFunctionGettersSetters`/`ReducibleGettersSetters`
machinery (from `Language.Modules.InductiveFunctions`) at `T := Footprint`, giving a
syntactic over-approximation `fvP` of the part of the state a `Module`/`Procedure` can
read or modify, together with the soundness bound `fvP (m.toModule) ≤ fvPMexpr m`.

-/

open GaudisCrypt


/-! # fvP_extend_sup -/

-- fvP_extend_sup now called Lens.liftFootprint

/-- Two `Footprint`s with the same `updates` are equal. -/
@[ext]
lemma footprint_eq_of_updates {m} {x y : Footprint m} (h : x.updates = y.updates) :
    x = y := by
  obtain ⟨_, _, _, _⟩ := x
  obtain ⟨_, _, _, _⟩ := y
  simp only at h
  subst h
  rfl

private lemma submonoid_centralizer_carrier {m} (S : Set (m → SubProbability m)) :
    (Submonoid.centralizer S).carrier = Set.centralizer S := by
  ext x; simp [Submonoid.mem_centralizer_iff, Set.mem_centralizer_iff]

/-- Every `Footprint` is its own bicommutant (the `double_commutant` field, in `Set` form). -/
@[simp]
lemma footprint_updates_cc {m} (r : Footprint m) :
    Set.centralizer (Set.centralizer r.updates) = r.updates := by
  have h := r.double_commutant
  simpa only [submonoid_centralizer_carrier] using h

/-- The `updates` of a join is the double centralizer of the union of the `updates`. -/
private lemma footprint_sup_updates {m} (x y : Footprint m) :
    (x ⊔ y).updates = Set.centralizer (Set.centralizer (x.updates ∪ y.updates)) := by
  change (Footprint.from (x.updates ∪ y.updates)).updates = _
  exact Footprint.from_updates _

/-- Bicommutant closure `cⁿ²` is monotone. -/
private lemma cl_mono {m} {A B : Set (m → SubProbability m)} (h : A ⊆ B) :
    Set.centralizer (Set.centralizer A) ⊆ Set.centralizer (Set.centralizer B) :=
  Set.centralizer_subset (Set.centralizer_subset h)


/-- `Footprint.from` turns unions into joins. -/
lemma footprint_from_union {m} (A B : Set (m → SubProbability m)) :
    Footprint.from A ⊔ Footprint.from B = Footprint.from (A ∪ B) := by
  apply footprint_eq_of_updates
  rw [footprint_sup_updates, Footprint.from_updates, Footprint.from_updates,
      Footprint.from_updates]
  apply Set.Subset.antisymm
  · calc Set.centralizer (Set.centralizer
            (Set.centralizer (Set.centralizer A) ∪ Set.centralizer (Set.centralizer B)))
        ⊆ Set.centralizer (Set.centralizer (Set.centralizer (Set.centralizer (A ∪ B)))) :=
          cl_mono (Set.union_subset (cl_mono Set.subset_union_left)
            (cl_mono Set.subset_union_right))
      _ = Set.centralizer (Set.centralizer (A ∪ B)) :=
          Set.centralizer_centralizer_centralizer (Set.centralizer (A ∪ B))
  · exact cl_mono (Set.union_subset_union Set.subset_centralizer_centralizer
      Set.subset_centralizer_centralizer)

/-- **Read-back**: post-composing a localized kernel with `lens.get` recovers the base kernel
    (`lens.set_get` collapses the write, `bind_pure` the trivial bind). -/
private lemma updateK_get_inv {a s : Type} (lens : Lens a s) (κ : a → SubProbability a) (st : s) :
    (lens.liftSubProbability κ st >>= fun st' => pure (lens.get st')) = κ (lens.get st) := by
  show (κ (lens.get st) >>= fun a' => pure (lens.set a' st)) >>= (fun st' => pure (lens.get st'))
     = κ (lens.get st)
  rw [SubProbability.bind_assoc]
  rw [show (fun a' => (pure (lens.set a' st) : SubProbability s) >>= fun st' => pure (lens.get st'))
        = (fun a' => (pure a' : SubProbability a)) from by
      funext a'; rw [SubProbability.pure_bind, lens.set_get]]
  exact SubProbability.bind_pure _


/-- **`lens.liftSubProbability` is injective** when the state is inhabited
    (every focus value is some `lens.get st`, and read-back recovers the kernel there). -/
lemma updateK_injective {a s : Type} [Nonempty s] (lens : Lens a s) :
    Function.Injective lens.liftSubProbability := by
  intro κ κ' h
  funext v
  have reduce : ∀ (ρ : a → SubProbability a),
      lens.liftSubProbability ρ (lens.set v (Classical.arbitrary s))
        >>= (fun st' => pure (lens.get st')) = ρ v := fun ρ => by
    change (ρ (lens.get (lens.set v (Classical.arbitrary s)))
        >>= fun a' => pure (lens.set a' (lens.set v (Classical.arbitrary s))))
      >>= (fun st' => pure (lens.get st')) = ρ v
    rw [lens.set_get, SubProbability.bind_assoc,
        show (fun a' => (pure (lens.set a' (lens.set v (Classical.arbitrary s))) : SubProbability s)
              >>= fun st' => pure (lens.get st'))
            = (fun a' => (pure a' : SubProbability a)) from
          funext fun a' => by rw [SubProbability.pure_bind, lens.set_get],
        SubProbability.bind_pure]
  have hsub : (lens.liftSubProbability κ (lens.set v (Classical.arbitrary s))
        >>= fun st' => pure (lens.get st'))
      = (lens.liftSubProbability κ' (lens.set v (Classical.arbitrary s))
        >>= fun st' => pure (lens.get st')) :=
    congrArg (· >>= fun st' => pure (lens.get st'))
      (congrFun h (lens.set v (Classical.arbitrary s)))
  rw [reduce κ, reduce κ'] at hsub
  exact hsub


/-- **`lens.liftSubProbability` is multiplicative**, hence a monoid homomorphism on kernels. The lens
    laws (`set_get`, `set_set`) make the two localizations of a Kleisli composition agree. -/
lemma updateK_mul {a b} (lens : Lens a b) (κ₁ κ₂ : a → SubProbability a) :
    lens.liftSubProbability (κ₁ * κ₂) = lens.liftSubProbability κ₁ * lens.liftSubProbability κ₂ := by
  funext st
  -- `(f * g) x` is definitionally `g x >>= f`; unfold both Kleisli products directly.
  change lens.liftSubProbability (fun x => κ₂ x >>= κ₁) st
      = lens.liftSubProbability κ₂ st >>= lens.liftSubProbability κ₁
  simp only [Lens.liftSubProbability]
  rw [SubProbability.bind_assoc, SubProbability.bind_assoc]
  congr 1
  funext a'
  rw [SubProbability.pure_bind, Lens.liftSubProbability, lens.set_get]
  congr 1
  funext a''
  rw [lens.set_set]

/-- **Bridge identity.** Pushing a lens-localized kernel `lens.liftSubProbability f` through the split
bijection `b ≃ a × lens.ComplContent` yields exactly the `a`-component lift `Lens.fst.liftSubProbability f`.
This is what
makes the centralizer footprint `fvP_reduce` agree with the split-then-reduce construction. -/
private lemma bijection_split_updateK {a b : Type} (lens : Lens a b) (f : a → SubProbability a) :
    (Lens.bijection (Lens.splitSpace lens)).liftSubProbability (lens.liftSubProbability f)
      = (Lens.fst).liftSubProbability f := by
  funext p
  have hA : lens.get ((Lens.splitSpace lens).symm p) = p.1 := by
    calc lens.get ((Lens.splitSpace lens).symm p)
        = ((Lens.splitSpace lens) ((Lens.splitSpace lens).symm p)).1 := rfl
      _ = p.1 := by rw [(Lens.splitSpace lens).apply_symm_apply]
  have hB : ∀ a', (Lens.splitSpace lens) (lens.set a' ((Lens.splitSpace lens).symm p)) = (a', p.2) := by
    intro a'
    have hcompl : lens.compl.get (lens.set a' ((Lens.splitSpace lens).symm p))
        = lens.compl.get ((Lens.splitSpace lens).symm p) :=
      Quotient.sound ⟨lens.get ((Lens.splitSpace lens).symm p), by rw [lens.set_set, lens.get_set]⟩
    have hp2 : lens.compl.get ((Lens.splitSpace lens).symm p) = p.2 := by
      calc lens.compl.get ((Lens.splitSpace lens).symm p)
          = ((Lens.splitSpace lens) ((Lens.splitSpace lens).symm p)).2 := rfl
        _ = p.2 := by rw [(Lens.splitSpace lens).apply_symm_apply]
    show (lens.get (lens.set a' ((Lens.splitSpace lens).symm p)),
          lens.compl.get (lens.set a' ((Lens.splitSpace lens).symm p))) = (a', p.2)
    rw [lens.set_get, hcompl, hp2]
  simp only [Lens.liftSubProbability, Lens.bijection, SubProbability.bind_assoc, SubProbability.pure_bind]
  rw [hA]
  simp only [hB]
  rfl

/-- Kleisli product of `a × b`-kernels in bind form. -/
-- TODO not needed, just use def on *
theorem kmul_prod_apply {a b : Type} (F G : a × b → SubProbability (a × b)) (x : a × b) :
    (F * G) x = G x >>= F := rfl


instance [Nonempty s] (lens : Lens a s) : Nonempty lens.ComplContent :=
  ⟨Quotient.mk lens.equal_outside_setoid (Classical.arbitrary s)⟩

@[reducible] def _root_.GaudisCrypt.Lens.instContentNonempty [Nonempty s]
    (lens : Lens a s) : Nonempty a := ⟨lens.get (Classical.arbitrary s)⟩

lemma _root_.GaudisCrypt.Footprint.empty_trivial (h : ¬ Nonempty a) (r s : Footprint a) : r = s := by
  haveI : IsEmpty a := not_nonempty_iff.mp h
  apply footprint_eq_of_updates
  ext f
  have hf : f = pure := funext fun x => isEmptyElim x
  subst hf
  exact ⟨fun _ => s.id, fun _ => r.id⟩





/-- **`Lens.liftFootprint` distributes over joins** (i.e. `extend` is a join-homomorphism), for an arbitrary
lens. The reverse (`≥`) direction is monotonicity; the hard (`≤`) direction reduces — exactly as in
`fvP_extend_sup_simpler` — to the extend-side double-commutant inclusion, here in its general form
`Lens.liftSubProbability_double_commutant`. -/
theorem Lens.liftFootprint_sup {a b} (lens : Lens a b) (r₁ r₂ : Footprint a) :
    Lens.liftFootprint lens (r₁ ⊔ r₂) = Lens.liftFootprint lens r₁ ⊔ Lens.liftFootprint lens r₂ := by
  wlog ne : Nonempty b; { apply Footprint.empty_trivial ne }
  refine le_antisymm ?_
    (sup_le (Lens.liftFootprint_mono lens le_sup_left) (Lens.liftFootprint_mono lens le_sup_right))
  unfold Lens.liftFootprint
  rw [footprint_from_union, ← Set.image_union, footprint_sup_updates,
      Footprint.from_le_iff, Footprint.from_updates]
  exact Lens.liftSubProbability_double_commutant lens _

/-- **`Lens.liftFootprint` distributes over arbitrary indexed suprema.**
    Generalises `Lens.liftFootprint_sup` from binary joins to indexed families. -/
theorem Lens.liftFootprint_iSup {a b : Type} {ι : Sort*} (lens : Lens a b)
    (rs : ι → Footprint a) :
    Lens.liftFootprint lens (⨆ i, rs i) = ⨆ i, Lens.liftFootprint lens (rs i) := by
  wlog ne : Nonempty b; { apply Footprint.empty_trivial ne }
  refine le_antisymm ?_ (iSup_le fun i => Lens.liftFootprint_mono lens (le_iSup rs i))
  change Footprint.from (lens.liftSubProbability '' (⨆ i, rs i).updates) ≤
       ⨆ i, Lens.liftFootprint lens (rs i)
  rw [Footprint.from_le_iff]
  have hiSup_rs : (⨆ i, rs i).updates =
      Set.centralizer (Set.centralizer (⋃ i, (rs i).updates)) := by
    change (Footprint.from (⋃ x ∈ Set.range rs, x.updates)).updates = _
    rw [Footprint.from_updates, Set.biUnion_range]
  have hiSup_lift : (⨆ i, Lens.liftFootprint lens (rs i)).updates =
      Set.centralizer (Set.centralizer (⋃ i, (Lens.liftFootprint lens (rs i)).updates)) := by
    change (Footprint.from
        (⋃ x ∈ Set.range (Lens.liftFootprint lens ∘ rs), x.updates)).updates = _
    rw [Footprint.from_updates, Set.biUnion_range]
    simp [Function.comp]
  rw [hiSup_rs, hiSup_lift]
  calc lens.liftSubProbability '' Set.centralizer (Set.centralizer (⋃ i, (rs i).updates))
      ⊆ Set.centralizer (Set.centralizer (lens.liftSubProbability '' ⋃ i, (rs i).updates)) :=
          Lens.liftSubProbability_double_commutant lens _
    _ = Set.centralizer (Set.centralizer (⋃ i, lens.liftSubProbability '' (rs i).updates)) := by
          rw [Set.image_iUnion]
    _ ⊆ Set.centralizer (Set.centralizer (⋃ i, (Lens.liftFootprint lens (rs i)).updates)) :=
          cl_mono (Set.iUnion_mono fun i => by
            simp only [Lens.liftFootprint, Footprint.from_updates]
            exact Set.subset_centralizer_centralizer)

/-! # End of fvP_extend_sup -/

/-! # fvP_reduce_sup -/


-- DOMINIQUE READING

noncomputable
def fvP_reduce {a b} (lens : Lens a b) (range : Footprint b) : Footprint a :=
  Footprint.from (Lens.reduceSubProbability lens '' (range.updates ×ˢ Set.univ ×ˢ Set.univ))


/-- `fvP_reduce` is monotone: a larger range gives a larger reduced range. -/
theorem fvP_reduce_mono {a b} (lens : Lens a b) {r r' : Footprint b} (h : r ≤ r') :
    fvP_reduce lens r ≤ fvP_reduce lens r' := by
  have hsub : r.updates ⊆ r'.updates := h
  apply Footprint.from_mono
  gcongr


/-- `fvP_reduce` as `Footprint.from` of the named generator set. -/
theorem fvP_reduce_eq_from {a b : Type} (lens : Lens a b) (range : Footprint b) :
    fvP_reduce lens range
      = Footprint.from (Lens.reduceSubProbability lens '' (range.updates ×ˢ Set.univ ×ˢ Set.univ)) := rfl

/-- **`fvP_reduce'` and `fvP_reduce` have the same generator centralizer.** The
centralizer of the reduced-generator image is exactly the lift-commutation constraint defining
`fvP_reduce'`: by the Fubini identities, `h` commutes with every `Lens.reduceSubProbability (g, i, o)`
(over all `i, o`) iff `Lens.fst.liftSubProbability h` commutes with `g` (the `⟸` direction is immediate;
the `⟹` uses
slice determination `reduceBaseExt`). -/
theorem centralizer_reduceBaseGen_image {a b : Type} (lens : Lens a b) (range : Footprint b) :
    Set.centralizer (Lens.reduceSubProbability lens '' (range.updates ×ˢ Set.univ ×ˢ Set.univ))
      = { f | ∀ g ∈ range.updates,
          (lens.liftSubProbability f : b → SubProbability b) * g
            = g * lens.liftSubProbability f } := by
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_centralizer_iff]
  constructor
  · intro hcomm g hg
    apply Lens.reduceSubProbability_ext lens
    intro i o
    rw [← Lens.reduceSubProbability_mul_left, ← Lens.reduceSubProbability_mul_right]
    exact (hcomm (Lens.reduceSubProbability lens (g, i, o))
      ⟨(g, i, o), ⟨hg, Set.mem_univ _, Set.mem_univ _⟩, rfl⟩).symm
  · intro hcon k hk
    obtain ⟨⟨g, i, o⟩, ⟨hg, -, -⟩, rfl⟩ := hk
    rw [Lens.reduceSubProbability_mul_right, Lens.reduceSubProbability_mul_left, hcon g hg]


theorem fvP_reduce_alt_def {a b : Type} (lens : Lens a b) (range : Footprint b) :
    fvP_reduce lens range =
    Footprint.from
    { f | ∀ g ∈ range.updates,
        (lens.liftSubProbability f : b → SubProbability b) * g
          = g * lens.liftSubProbability f }.centralizer := by
  apply footprint_eq_of_updates
  rw [fvP_reduce_eq_from, Footprint.from_updates, centralizer_reduceBaseGen_image]
  rw [Footprint.from_updates, Set.centralizer_centralizer_centralizer]


/-- For a **bijective** monoid homomorphism `u`, the bicommutant transports through the image:
`u '' CC(W) ⊆ CC(u '' W)`. (Surjectivity lets us pull back an arbitrary commutant element;
injectivity lets us cancel `u`.) -/
private lemma image_cc_subset {M N : Type*} [Monoid M] [Monoid N]
    (u : M → N) (hu : ∀ x y, u (x * y) = u x * u y)
    (hsurj : Function.Surjective u) (hinj : Function.Injective u) (W : Set M) :
    u '' Set.centralizer (Set.centralizer W) ⊆ Set.centralizer (Set.centralizer (u '' W)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Set.mem_centralizer_iff]
  intro y hy
  obtain ⟨y', rfl⟩ := hsurj y
  have hy' : y' ∈ Set.centralizer W := by
    rw [Set.mem_centralizer_iff]
    intro w hw
    apply hinj
    rw [hu, hu, (Set.mem_centralizer_iff.mp hy) (u w) ⟨w, hw, rfl⟩]
  have hc := (Set.mem_centralizer_iff.mp hx) y' hy'
  rw [← hu, ← hu, hc]

/-- **The crux of `fvP_reduce_sup2`.** Every generator of the reduced join lies in the bicommutant
closure of the union of the two reduced generator sets — the double-commutant direction.

The proof needs **no disintegration**: with `ĥ = Lens.fst.liftSubProbability h` the `h ⊗ id_b` lift, the two
Fubini
identities (`Lens.reduceSubProbability_mul_left`/`_right`) turn `h`-commutation of reduced generators into
`ĥ`-commutation of the joint kernels. Slice determination (`reduceBaseExt`) lifts any
`h ∈ commutant(gen r₁ ∪ gen r₂)` to `ĥ ∈ commutant(r₁.updates ∪ r₂.updates)`; then `f` in the
bicommutant commutes with `ĥ`, and the identities push that back down to `h`. -/
theorem reduceBaseGen_sup_subset {a b : Type} (lens : Lens a b) (r₁ r₂ : Footprint b) :
    Lens.reduceSubProbability lens '' ((r₁ ⊔ r₂).updates ×ˢ Set.univ ×ˢ Set.univ)
      ⊆ Set.centralizer (Set.centralizer
          ((Lens.reduceSubProbability lens '' (r₁.updates ×ˢ Set.univ ×ˢ Set.univ))
            ∪ (Lens.reduceSubProbability lens '' (r₂.updates ×ˢ Set.univ ×ˢ Set.univ)))) := by
  rintro _ ⟨⟨f, i, o⟩, ⟨hf, -, -⟩, rfl⟩
  rw [Set.mem_centralizer_iff]
  intro h hh
  -- The `h ⊗ id_b` lift commutes with `r₁.updates ∪ r₂.updates`.
  have hĥ : (lens.liftSubProbability h : b → _)
      ∈ Set.centralizer (r₁.updates ∪ r₂.updates) := by
    rw [Set.mem_centralizer_iff]
    intro g hg
    apply Lens.reduceSubProbability_ext lens
    intro i' o'
    rw [← Lens.reduceSubProbability_mul_right, ← Lens.reduceSubProbability_mul_left]
    have hmem : Lens.reduceSubProbability lens (g, i', o')
        ∈ (Lens.reduceSubProbability lens '' (r₁.updates ×ˢ Set.univ ×ˢ Set.univ))
          ∪ (Lens.reduceSubProbability lens '' (r₂.updates ×ˢ Set.univ ×ˢ Set.univ)) := by
      cases hg with
      | inl hg1 => exact Or.inl ⟨(g, i', o'), ⟨hg1, Set.mem_univ _, Set.mem_univ _⟩, rfl⟩
      | inr hg2 => exact Or.inr ⟨(g, i', o'), ⟨hg2, Set.mem_univ _, Set.mem_univ _⟩, rfl⟩
    exact (Set.mem_centralizer_iff.mp hh) (Lens.reduceSubProbability lens (g, i', o')) hmem
  -- `f` is in the bicommutant of the union, so it commutes with the lift.
  have hfĥ : (lens.liftSubProbability h : b → _) * f
      = f * lens.liftSubProbability h := by
    rw [footprint_sup_updates] at hf
    exact (Set.mem_centralizer_iff.mp hf) (lens.liftSubProbability h) hĥ
  rw [Lens.reduceSubProbability_mul_left, Lens.reduceSubProbability_mul_right, hfĥ]


theorem fvP_reduce_sup {a b} (lens : Lens a b) (r₁ r₂ : Footprint b) :
    fvP_reduce lens (r₁ ⊔ r₂) = fvP_reduce lens r₁ ⊔ fvP_reduce lens r₂ := by
  apply le_antisymm
  · rw [fvP_reduce_eq_from, fvP_reduce_eq_from, fvP_reduce_eq_from,
      Footprint.from_le_iff]
    set Z := Footprint.from (Lens.reduceSubProbability lens '' (r₁.updates ×ˢ Set.univ ×ˢ Set.univ))
        ⊔ Footprint.from (Lens.reduceSubProbability lens '' (r₂.updates ×ˢ Set.univ ×ˢ Set.univ)) with hZ
    have h1 : Lens.reduceSubProbability lens '' (r₁.updates ×ˢ Set.univ ×ˢ Set.univ) ⊆ Z.updates :=
      (Footprint.from_le_iff _ _).mp le_sup_left
    have h2 : Lens.reduceSubProbability lens '' (r₂.updates ×ˢ Set.univ ×ˢ Set.univ) ⊆ Z.updates :=
      (Footprint.from_le_iff _ _).mp le_sup_right
    refine (reduceBaseGen_sup_subset lens r₁ r₂).trans ?_
    rw [← footprint_updates_cc Z]
    exact Set.centralizer_subset (Set.centralizer_subset (Set.union_subset h1 h2))
  · exact sup_le (fvP_reduce_mono lens le_sup_left) (fvP_reduce_mono lens le_sup_right)




/-! # End of fvP_reduce_sup -/

namespace FVP

variable [ProgramSpec]

/-- Family version of `ProgramDenotation.footprint`: the supremum of the per-input ranges. Used to
give a setter (which is a *family* `a → ProgramDenotation s Unit`, one program per written value) a
single footprint. -/
noncomputable def _root_.GaudisCrypt.ProgramDenotation.footprint'
    {s a b : Type} (progs : a → ProgramDenotation s b) : Footprint s :=
  ⨆ x, (progs x).footprint

noncomputable
-- TODO: Inline
def fvP_getter (getter : Getter a s) : Footprint s := ProgramDenotation.footprint
    (ProgramDenotation.get getter)

noncomputable
-- TODO: Inline
def fvP_setter (setter : Setter a s) : Footprint s := ProgramDenotation.footprint'
    (ProgramDenotation.set setter)

noncomputable
-- TODO rename to something Lens-related
def fvP_reduce_new {a b : Type} (lens : Lens a b) (range : Footprint b) :
    Footprint a :=
  -- transport `range` along `lens.splitSpace : b ≃ a × lens.ComplContent` (via the bijection lens),
  -- then reduce away the complement component with `fvP_reduce`.
  fvP_reduce Lens.fst (Lens.liftFootprint (Lens.bijection (Lens.splitSpace lens)) range)



/-! ### Properties of `fvP_reduce` / `Lens.liftFootprint` needed for the framework instance.

 -/


omit [ProgramSpec] in
/-- The `fvP_reduce` constraint set is `lens.liftSubProbability ⁻¹'` of a centralizer. -/
private lemma fvP_reduce_constraint {a b} (lens : Lens a b) (V : Set (b → SubProbability b)) :
    {f : a → SubProbability a | ∀ g ∈ V, lens.liftSubProbability f * g = g * lens.liftSubProbability f}
      = lens.liftSubProbability ⁻¹' (Set.centralizer V) := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_centralizer_iff]
  exact ⟨fun h g hg => (h g hg).symm, fun h g hg => (h g hg).symm⟩

/-! ### `lens.liftSubProbability` is a monoid homomorphism, and the resulting closure algebra. -/

omit [ProgramSpec] in
/-- **`lens.liftSubProbability` preserves the identity kernel.** -/
lemma updateK_one {a b} (lens : Lens a b) :
    lens.liftSubProbability (1 : a → SubProbability a) = 1 := by
  funext st
  show (pure (lens.get st) : SubProbability a) >>= (fun a' => pure (lens.set a' st)) = pure st
  rw [SubProbability.pure_bind, lens.get_set]

omit [ProgramSpec] in
/-- The bicommutant retraction inequality for a multiplicative `u`:
    `C(u⁻¹'(C(u '' R))) ⊆ CC(R)`.  The engine behind `fvP_reduce_extend`: if `q` commutes
    with `R` then `u q` commutes with `u '' R` (by multiplicativity), so `q` lies in the
    preimage that `f` centralizes, whence `q * f = f * q`. -/
private lemma centralizer_preimage_image_subset {M N : Type*} [Monoid M] [Monoid N]
    (u : M → N) (hu : ∀ x y, u (x * y) = u x * u y) (R : Set M) :
    Set.centralizer (u ⁻¹' Set.centralizer (u '' R)) ⊆ Set.centralizer (Set.centralizer R) := by
  intro f hf
  rw [Set.mem_centralizer_iff]
  intro q hq
  have hqmem : q ∈ u ⁻¹' Set.centralizer (u '' R) := by
    show u q ∈ Set.centralizer (u '' R)
    rw [Set.mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    rw [← hu, ← hu, (Set.mem_centralizer_iff.mp hq) r hr]
  exact (Set.mem_centralizer_iff.mp hf) q hqmem

omit [ProgramSpec] in
/-- A `diracKer` of a localized deterministic update is the `updateK` of the base `diracKer`
    (alias of `Lens.liftSubProbability_diracKer`, kept under the `updateK` naming of this file). -/
lemma updateK_diracKer {a s : Type} (lens : Lens a s) (g : Function.End a) :
    lens.liftSubProbability (diracKer g) = diracKer (lens.liftFunction g) :=
  lens.liftSubProbability_diracKer g

omit [ProgramSpec] in
/-- The bicommutant closure of the full set of `lens`-localized kernels is exactly
    `lens.footprint`.  Since `Lens.footprint` is now *generated* by all localized kernels
    (`Set.range lens.liftSubProbability = lens.liftSubProbability '' univ`), this is definitional
    — what used to be the hard half of the lens-corner double-commutant theorem. -/
theorem updateK_image_univ_cc {a s : Type} (lens : Lens a s) :
    Set.centralizer (Set.centralizer (lens.liftSubProbability '' (Set.univ : Set (a → SubProbability a))))
      = lens.footprint.updates := by
  rw [Set.image_univ, Lens.footprint, Footprint.from_updates]

omit [ProgramSpec] in
/-- `fvP_reduce` is monotone in its range argument (double-antitone via the two centralizers). -/
private lemma fvP_reduce_mono {a b} (lens : Lens a b) {r r' : Footprint b} (h : r ≤ r') :
    fvP_reduce lens r ≤ fvP_reduce lens r' := by
  have hsub : r.updates ⊆ r'.updates := h
  unfold fvP_reduce
  apply Footprint.from_mono
  gcongr

/-! ### Extraction: `lens.footprint` is exactly the localized kernels.

The bicommutant closure of the lens-image does *not* enlarge it — `fvP_extend_updates` is a genuine
equality. The two ingredients (per the proof sketch): every kernel in `lens.footprint` is `lens.liftSubProbability`
of some base kernel (`footprint_updateK_image`), and `lens.liftSubProbability` is injective (so commutation
transfers through it). -/



omit [ProgramSpec] in
/-- A kernel in `lens.footprint` is **equivariant under complement updates**: it commutes with every
    Dirac complement-update (`diracKer (lens.compl.update h) ∈ lens.footprintᶜ`), so it intertwines
    `lens.compl.update h`. -/
private lemma footprint_equivariant {a s : Type} (lens : Lens a s)
    {p : s → SubProbability s} (hp : p ∈ lens.footprint.updates)
    (h : Function.End lens.ComplContent) (st : s) :
    p (lens.compl.liftFunction h st) = (p st >>= fun st' => pure (lens.compl.liftFunction h st')) := by
  haveI : disjoint lens.compl lens := ⟨fun st v w => by
    induction v using Quotient.inductionOn
    rename_i u
    show lens.set (lens.get (lens.set w st)) u = lens.set w (lens.set (lens.get st) u)
    rw [lens.set_get, lens.set_set]⟩
  have hsub : lens.compl.footprint.updates ⊆ (lens.footprint)ᶜ.updates :=
    Lens.footprint_le_compl_of_disjoint lens.compl lens
  have hk : diracKer (lens.compl.liftFunction h) ∈ (lens.footprint)ᶜ.updates :=
    hsub (lens.compl.diracKer_liftFunction_mem_footprint h)
  rw [Footprint.updates_eq_centralizer_compl lens.footprint] at hp
  have hcomm := Submonoid.mem_centralizer_iff.mp hp (diracKer (lens.compl.liftFunction h)) hk
  have hst := congrFun hcomm st
  -- `(f * g) st` is definitionally `g st >>= f`; unfold both Kleisli products directly.
  change p st >>= diracKer (lens.compl.liftFunction h)
      = diracKer (lens.compl.liftFunction h) st >>= p at hst
  rw [show (diracKer (lens.compl.liftFunction h) st) = pure (lens.compl.liftFunction h st) from rfl,
      SubProbability.pure_bind] at hst
  exact hst.symm

omit [ProgramSpec] in
/-- **Extraction**: every kernel in `lens.footprint` is `lens.liftSubProbability` of a base kernel. The witness
    reads the base at a fixed `st₀`; equivariance + the `Lens.compl.set ⟦st⟧ st' = lens.set (lens.get st') st`
    identity make `lens.liftSubProbability (read-back) = p`. -/
private lemma footprint_updateK_image {a s : Type} (lens : Lens a s) (st₀ : s)
    {p : s → SubProbability s} (hp : p ∈ lens.footprint.updates) :
    lens.liftSubProbability (fun v => p (lens.set v st₀) >>= fun st' => pure (lens.get st')) = p := by
  funext st
  have hLHS :
      lens.liftSubProbability (fun v => p (lens.set v st₀) >>= fun st' => pure (lens.get st')) st
      = p (lens.set (lens.get st) st₀) >>= fun st' => pure (lens.set (lens.get st') st) := by
    show ((p (lens.set (lens.get st) st₀) >>= fun st' => pure (lens.get st'))
            >>= fun a' => pure (lens.set a' st))
       = p (lens.set (lens.get st) st₀) >>= fun st' => pure (lens.set (lens.get st') st)
    rw [SubProbability.bind_assoc]
    congr 1; funext st'
    rw [SubProbability.pure_bind]
  rw [hLHS]
  have hrecon : lens.compl.liftFunction (Function.const _ (lens.compl.get st))
      (lens.set (lens.get st) st₀) = st := by
    show lens.set (lens.get (lens.set (lens.get st) st₀)) st = st
    rw [lens.set_get]; exact lens.get_set st
  have heq := footprint_equivariant lens hp (Function.const _ (lens.compl.get st))
    (lens.set (lens.get st) st₀)
  rw [hrecon] at heq
  rw [heq]
  congr 1

omit [ProgramSpec] in
/-- **`Lens.liftFootprint` is exactly the lens-image of the footprint** (`[Nonempty b]`). The `⊇` half is the
    generic `X ⊆ CC X`; the `⊆` half is the proof sketch: `Lens.liftFootprint` lands in `lens.footprint`, every
    such element extracts as `lens.liftSubProbability q`, and (`updateK` being an injective hom) `q` inherits the
    commutation defining `range.updates`. Correcting the deterministic original's *false* conjecture —
    over a lens corner the bicommutant closure does **not** enlarge the image. -/
theorem fvP_extend_updates {a b} [Nonempty b] (lens : Lens a b) (range : Footprint a) :
    (Lens.liftFootprint lens range).updates = lens.liftSubProbability '' range.updates := by
  apply Set.Subset.antisymm
  · intro p hp
    have hp_lens : p ∈ lens.footprint.updates := by
      have h1 : (Lens.liftFootprint lens range).updates ⊆ lens.footprint.updates := by
        rw [← updateK_image_univ_cc lens]
        unfold Lens.liftFootprint
        rw [Footprint.from_updates]
        exact cl_mono (Set.image_mono (Set.subset_univ _))
      exact h1 hp
    have hpC : p ∈ Set.centralizer (Set.centralizer (lens.liftSubProbability '' range.updates)) := by
      have hfe : (Lens.liftFootprint lens range).updates
          = Set.centralizer (Set.centralizer (lens.liftSubProbability '' range.updates)) := by
        unfold Lens.liftFootprint; exact Footprint.from_updates _
      rwa [hfe] at hp
    obtain ⟨q, hq⟩ : ∃ q, lens.liftSubProbability q = p :=
      ⟨_, footprint_updateK_image lens (Classical.arbitrary b) hp_lens⟩
    refine ⟨q, ?_, hq⟩
    rw [← footprint_updates_cc range, Set.mem_centralizer_iff]
    intro r hr
    have hur : lens.liftSubProbability r ∈ Set.centralizer (lens.liftSubProbability '' range.updates) := by
      rw [Set.mem_centralizer_iff]
      rintro _ ⟨t, ht, rfl⟩
      rw [← updateK_mul, ← updateK_mul, (Set.mem_centralizer_iff.mp hr) t ht]
    have hcomm := (Set.mem_centralizer_iff.mp hpC) (lens.liftSubProbability r) hur
    rw [← hq, ← updateK_mul, ← updateK_mul] at hcomm
    exact updateK_injective lens hcomm
  · unfold Lens.liftFootprint
    rw [Footprint.from_updates]
    exact Set.subset_centralizer_centralizer

omit [ProgramSpec] in
/-- **`fvP_reduce` is a retraction of `Lens.liftFootprint`** (`reduce (extend r) ≤ r`):
    pushing a footprint forward along a lens and pulling it back recovers at most it.
    Proven in full from `updateK` being a monoid homomorphism
    (`centralizer_preimage_image_subset`). -/
theorem fvP_reduce_extend_le {a b} (lens : Lens a b) (r : Footprint a) :
    fvP_reduce lens (Lens.liftFootprint lens r) ≤ r := by
  rw [fvP_reduce_alt_def]
  rw [Footprint.from_le_iff, fvP_reduce_constraint]
  have hext : Set.centralizer (Lens.liftFootprint lens r).updates
            = Set.centralizer (lens.liftSubProbability '' r.updates) := by
    unfold Lens.liftFootprint
    rw [Footprint.from_updates, Set.centralizer_centralizer_centralizer]
  rw [hext]
  have key := centralizer_preimage_image_subset lens.liftSubProbability (updateK_mul lens) r.updates
  rw [footprint_updates_cc] at key
  exact key

omit [ProgramSpec] in
/-- **`fvP_reduce` is an exact left inverse of `Lens.liftFootprint`** (strengthening
    `fvP_reduce_extend` to equality): every `p ∈ r.updates` is itself
    `Lens.reduceSubProbability lens (lens.liftSubProbability p, i, o)` for the trivial
    `i () = pure β` / `o _ = pure ()`, hence lies in the generator set defining `fvP_reduce`. -/
theorem fvP_reduce_extend {a b} [Nonempty b] (lens : Lens a b) (r : Footprint a) :
    fvP_reduce lens (Lens.liftFootprint lens r) = r := by
  apply le_antisymm
  · apply fvP_reduce_extend_le
  · change r.updates ≤ (fvP_reduce lens (Lens.liftFootprint lens r)).updates
    rw [fvP_reduce_eq_from, Footprint.from_updates]
    apply Set.Subset.trans _ Set.subset_centralizer_centralizer
    intro p hp
    let β : lens.ComplContent := Classical.arbitrary lens.ComplContent
    refine ⟨(lens.liftSubProbability p, fun _ => pure β, fun _ => pure ()),
      ⟨?_, Set.mem_univ _, Set.mem_univ _⟩, ?_⟩
    · change lens.liftSubProbability p ∈ (Lens.liftFootprint lens r).updates
      unfold Lens.liftFootprint
      rw [Footprint.from_updates]
      exact Set.subset_centralizer_centralizer ⟨p, hp, rfl⟩
    · funext m
      simp only [Lens.reduceSubProbability, Lens.liftSubProbability, SubProbability.pure_bind,
                SubProbability.bind_assoc, Lens.splitSpace_invFun_get, Lens.splitSpace_invFun_set,
                SubProbability.bind_pure]

noncomputable
def fvpInductiveFunctionGS : InductiveFunctionGettersSetters Footprint where
  nothing := ⊥
  join := (· ⊔ ·)
  getter g := ProgramDenotation.footprint (ProgramDenotation.get g)
  setter s := ProgramDenotation.footprint' (ProgramDenotation.set s)
  reduce := fvP_reduce
  extend := Lens.liftFootprint

noncomputable
def fvPMexpr {ctx t} (m : ModuleExpression ctx t) : (Footprint State) :=
  fvpInductiveFunctionGS.evalMexpr m

noncomputable
def fvP (m : Module t) : Footprint State := fvpInductiveFunctionGS.eval m

scoped instance : ReducibleGettersSetters fvpInductiveFunctionGS where
  comm := ⟨sup_comm⟩
  assoc := ⟨sup_assoc⟩
  join_idem := fun _ => sup_le le_rfl le_rfl
  join_mono_left := fun h => sup_le_sup_right h _
  le_join_left := fun _ _ => le_sup_left
  nothing_le := fun _ => bot_le
  reduce_join := by
    intro a b r1 r2 lens
    exact le_of_eq (fvP_reduce_sup lens r1 r2)
  extend_join := by
    intro a b r1 r2 lens
    exact (Lens.liftFootprint_sup lens r1 r2).symm.le
  extend_reduce := by
    intro a b lens r
    exact fvP_reduce_extend_le lens r
  reduce_mono := fun lens h => fvP_reduce_mono lens h
  extend_mono := fun lens h => Lens.liftFootprint_mono lens h


theorem fvPMexpr_upper_bound : fvP (m.toModule) ≤ fvPMexpr m :=
  evalMexpr_upper_bound fvpInductiveFunctionGS.inductiveFunction m

theorem fvP_app (a : Module (.arr A B)) (b : Module A) :
    fvP (.app a b) ≤ fvP a ⊔ fvP b :=
    InductiveFunction.app _ _ _

theorem fvP_pair (a : Module A) (b : Module B) :
    fvP (.pair a b) = fvP a ⊔ fvP b :=
    InductiveFunction.pair _ _ _

theorem fvP_fst (a : Module (.prod A B)) :
    fvP (.fst a) ≤ fvP a :=
    InductiveFunction.fst _ _

theorem fvP_snd (a : Module (.prod A B)) :
    fvP (.snd a) ≤ fvP a :=
    InductiveFunction.snd _ _

@[simp]
theorem fvP_unit (a : Module .unit) : fvP a = ⊥ :=
 InductiveFunction.unit _ _

noncomputable
def fvP_proc {sig holes} (proc : ProcedureWithHoles holes sig) : Footprint State :=
  fvpInductiveFunctionGS.proc proc

noncomputable
def fvP_stmt {s holes} (stmt : StmtWithHoles holes s) : Footprint (ProcedureState s) :=
  fvpInductiveFunctionGS.stmt stmt

/-- **EasyCrypt's `glob A`**: the getter reading everything the procedure `A` may touch —
    the `touched_getter` of its computed footprint.  `={glob A}` between two states is
    `(glob A).get σ₁ = (glob A).get σ₂`: the states differ only by updates *outside*
    `fvP_proc A`. -/
noncomputable
def glob {sig holes} (A : ProcedureWithHoles holes sig) :
    Getter (Quotient ((fvP_proc A)ᶜ.orbit_setoid)) State :=
  (fvP_proc A).touched_getter

end FVP


/-! ## Footprint/reduce/lift algebra

General footprint, `fvP_reduce` and `Lens.liftFootprint` facts, independent of any particular
program spec. -/

/-- **Complement is order-reversing on `Footprint`** (`le`/`compl` swap): `R ≤ Sᶜ ↔ S ≤ Rᶜ`.
    Both sides say every `R`-update commutes with every `S`-update, so the relation is symmetric in
    `R`, `S`. -/
theorem _root_.GaudisCrypt.Footprint.le_compl_comm {m : Type} (R S : Footprint m) : R ≤ Sᶜ ↔ S ≤ Rᶜ := by
  constructor <;>
  · intro h
    intro k hk
    show k ∈ Submonoid.centralizer _
    rw [Submonoid.mem_centralizer_iff]
    intro j hj
    exact ((Submonoid.mem_centralizer_iff.mp (h hj)) k hk).symm

/-- **A chained lens's footprint is the `liftFootprint` of the inner lens's footprint through the
    outer lens** (generator-level): `diracKer ((L.chain v).liftFunction g)` is exactly
    `L.liftSubProbability (diracKer (v.liftFunction g))`.  The chained overwrite is the inner
    overwrite performed on the `L`-content and written back. -/
theorem chain_liftFunction_diracKer {a b c : Type} (L : Lens b c) (v : Lens a b)
    (g : Function.End a) :
    diracKer ((L.chain v).liftFunction g) = L.liftSubProbability (diracKer (v.liftFunction g)) := by
  funext x
  show (pure ((L.chain v).liftFunction g x) : SubProbability c)
     = (diracKer (v.liftFunction g) (L.get x)) >>= fun a' => pure (L.set a' x)
  rw [show (diracKer (v.liftFunction g) (L.get x) : SubProbability b)
        = pure (v.liftFunction g (L.get x)) from rfl, SubProbability.pure_bind]
  rfl

/-- **The lift of an update commutes with every `R`-update**, when the update commutes with
    the `L`-reduction of `R` (membership form: `f ∈ (fvP_reduce L R)ᶜ.updates`).  The reduced
    generators `reduceSubProbability L (k, i, o)` of `k ∈ R.updates` lie in
    `(fvP_reduce L R).updates`, so `hf` makes them commute with `f`; the Fubini identities
    (`Lens.reduceSubProbability_mul_left`/`_right`) turn that into commutation of `L.liftSubProbability f`
    with `k` (via `reduceSubProbability_ext`). -/
theorem liftSubProbability_comm_of_mem_reduce_compl {s c : Type} {L : Lens s c}
    {R : Footprint c}
    {f : s → SubProbability s} (hf : f ∈ ((fvP_reduce L R)ᶜ).updates)
    {k : c → SubProbability c} (hk : k ∈ R.updates) :
    L.liftSubProbability f * k = k * L.liftSubProbability f := by
  apply Lens.reduceSubProbability_ext L
  intro i o
  -- Each reduced generator of `k` is a generator of `fvP_reduce L R`, hence commutes with `f`.
  have hgen : Lens.reduceSubProbability L (k, i, o) ∈ (fvP_reduce L R).updates := by
    rw [fvP_reduce_eq_from, Footprint.from_updates]
    exact Set.subset_centralizer_centralizer
      ⟨(k, i, o), ⟨hk, Set.mem_univ _, Set.mem_univ _⟩, rfl⟩
  have hcomm : f * Lens.reduceSubProbability L (k, i, o)
      = Lens.reduceSubProbability L (k, i, o) * f :=
    ((Submonoid.mem_centralizer_iff.mp hf) _ hgen).symm
  rw [Lens.reduceSubProbability_mul_left, Lens.reduceSubProbability_mul_right] at hcomm
  exact hcomm

/-- **The lift of a `v.footprint`-update commutes with every `R`-update**, when the
    `L`-reduction of `R` is disjoint from `v.footprint` — the lens-region instance of
    `liftSubProbability_comm_of_mem_reduce_compl`. -/
theorem liftSubProbability_comm_of_reduce_disj {t s c : Type} {L : Lens s c}
    {v : Lens t s} {R : Footprint c}
    (hred : fvP_reduce L R ≤ (v.footprint)ᶜ)
    {f : s → SubProbability s} (hf : f ∈ v.footprint.updates)
    {k : c → SubProbability c} (hk : k ∈ R.updates) :
    L.liftSubProbability f * k = k * L.liftSubProbability f :=
  liftSubProbability_comm_of_mem_reduce_compl
    ((Footprint.le_compl_comm _ _).mp hred hf) hk

/-- **A chained lens's footprint lies in `Rᶜ` whenever the inner footprint's `L`-reduction does**:
    from `fvP_reduce L R ≤ (v.footprint)ᶜ` conclude `R ≤ ((L.chain v).footprint)ᶜ`.  Route: flip the
    goal via `le_compl_comm` to `(L.chain v).footprint ≤ Rᶜ`, then show each generator
    `L.liftSubProbability (diracKer (v.liftFunction g))` commutes with every `k ∈ R.updates` via
    `liftSubProbability_comm_of_reduce_disj`. -/
theorem reduce_chain_le_compl {t s c : Type} {L : Lens s c} {v : Lens t s} {R : Footprint c}
    (hred : fvP_reduce L R ≤ (v.footprint)ᶜ) :
    R ≤ ((L.chain v).footprint)ᶜ := by
  rw [Footprint.le_compl_comm]
  refine (Footprint.from_le_iff _ _).mpr ?_
  rintro _ ⟨g, rfl⟩
  -- Goal: (L.chain v).liftSubProbability g ∈ Rᶜ.updates = centralizer R.updates
  show (L.chain v).liftSubProbability g ∈ Rᶜ.updates
  rw [Lens.liftSubProbability_chain]
  show L.liftSubProbability (v.liftSubProbability g) ∈ Submonoid.centralizer R.updates
  rw [Submonoid.mem_centralizer_iff]
  intro k hk
  exact (liftSubProbability_comm_of_reduce_disj hred (Mlocalized_in_footprint v g) hk).symm

open MeasureTheory in
/-- `globalL.liftSubProbability f` applied to a padded state applies `f` to the global. -/
theorem globalL_liftSubProbability_pad [ProgramSpec] {l : Type} (f : State → SubProbability State)
    (g : State) (loc : l) :
    (ProcedureState.globalL.liftSubProbability f) ⟨g, loc⟩
      = f g >>= fun a => pure (⟨a, loc⟩ : ProcedureState l) := by
  simp only [Lens.liftSubProbability]; rfl

/-- Reading the global out of `globalL.liftSubProbability f` recovers `f` on the global. -/
theorem globalL_liftSubProbability_global [ProgramSpec] {l : Type}
    (f : State → SubProbability State)
    (w2 : ProcedureState l) {ρ : Type} (x : ρ) :
    ((ProcedureState.globalL.liftSubProbability f) w2 >>= fun s'' => pure (x, s''.global))
      = f w2.global >>= fun a => pure (x, a) := by
  simp only [Lens.liftSubProbability]
  rw [SubProbability.bind_assoc]; congr 1; funext a; rw [SubProbability.pure_bind]; rfl

/-- **A sampled value's footprint is trivial** — `μ.toProgramDenotation` only draws its result, it
    touches no state, so it lies in `⊥` (mirrors `inFootprint_uniform` for an arbitrary `μ`). -/
theorem inFootprint_toProgramDenotation {s a : Type} (μ : SubProbability a) :
    (SubProbability.toProgramDenotation μ : ProgramDenotation s a).inFootprint ⊥ := by
  rw [inFootprint_iff_clean]
  intro f hf
  funext st
  show (f st >>= fun st' =>
          μ >>= fun v => (pure (v, st') : SubProbability (a × s)))
     = ((μ >>= fun v => (pure (v, st) : SubProbability (a × s)))
          >>= fun w : a × s => f w.2 >>= fun st'' => (pure (w.1, st'') : SubProbability (a × s)))
  rw [bind_swap (f st) μ (fun v st' => pure (v, st'))]
  rw [SubProbability.bind_assoc]
  congr 1; funext v
  rw [SubProbability.pure_bind]

/-! ## Chained and `FromLens` footprints

Moved here from `Footprint.lean`: the chain law's nontrivial inclusion — the intermediate
bicommutant closure adds nothing — is exactly the `FVP.fvP_extend_updates` extraction. -/

/-- **A chained lens's footprint-lift composes**: lifting a base footprint through
    `lens.chain lens2` is lifting through `lens2` and then through `lens`. -/
theorem _root_.GaudisCrypt.Lens.liftFootprint_chain {a b c : Type}
    (lens : Lens b c) (lens2 : Lens a b) (F : Footprint a) :
    (lens.chain lens2).liftFootprint F = lens.liftFootprint (lens2.liftFootprint F) := by
  by_cases hb : Nonempty b
  · haveI := hb
    -- `FVP.fvP_extend_updates` drags a vestigial section `[ProgramSpec]`; any spec will do
    haveI : ProgramSpec.{0} := ⟨PUnit⟩
    calc (lens.chain lens2).liftFootprint F
        = Footprint.from ((lens.chain lens2).liftSubProbability '' F.updates) := rfl
      _ = Footprint.from (lens.liftSubProbability '' (lens2.liftSubProbability '' F.updates)) := by
          rw [Lens.liftSubProbability_chain, Set.image_comp]
      _ = Footprint.from (lens.liftSubProbability '' (lens2.liftFootprint F).updates) := by
          rw [FVP.fvP_extend_updates lens2 F]
      _ = lens.liftFootprint (lens2.liftFootprint F) := rfl
  · -- with `b` empty, `c` is empty too, and all footprints on `c` coincide
    have hc : ¬ Nonempty c := fun ⟨x⟩ => hb ⟨lens.get x⟩
    have hall : ∀ R S : Footprint c, R ≤ S := fun R S u _ => by
      have hu : u = pure := funext fun σ => absurd ⟨σ⟩ hc
      rw [hu]; exact S.id
    exact le_antisymm (hall _ _) (hall _ _)

/-- **A chained lens's footprint is the `liftFootprint` of the inner lens's footprint.** -/
theorem _root_.GaudisCrypt.Lens.chain_footprint {a b c : Type}
    (lens : Lens b c) (lens2 : Lens a b) :
    (lens.chain lens2).footprint = lens.liftFootprint lens2.footprint := by
  simp [← Lens.liftFootprint_top, Lens.liftFootprint_chain]

theorem _root_.GaudisCrypt.Footprint.FromLens.from_lens {a s : Type} (lens : Lens a s) :
    Footprint.FromLens lens.footprint := by
  wlog ne : Nonempty s
  · -- if `s` is empty every kernel is `pure`, so all footprints coincide and any lens works
    have hall : ∀ R S : Footprint s, R ≤ S := fun R S u _ => by
      have hu : u = pure := funext fun σ => absurd ⟨σ⟩ ne
      rw [hu]; exact S.id
    exact ⟨{ get := fun σ => Quotient.mk _ σ, set := fun _ σ => σ,
             set_get := fun σ _ => (ne ⟨σ⟩).elim, set_set := fun _ _ _ => rfl,
             get_set := fun _ => rfl }, le_antisymm (hall _ _) (hall _ _)⟩
  obtain ⟨f, hf⟩ := Footprint.touchedGetter_is_getter lens
  existsi lens.chain (Lens.bijection f)
  rw [Lens.chain_footprint, Lens.bijection_footprint, Lens.liftFootprint_top]

/-- **A lens footprint's complement is its complement lens's footprint.**
    The `≤` inclusion `l.compl.footprint ≤ (l.footprint)ᶜ` already exists
    (`Lens.footprint_le_compl_of_disjoint l.compl l`, used in `footprint_equivariant`);
    the reverse `(l.footprint)ᶜ ≤ l.compl.footprint` is the substantive half. -/
theorem _root_.GaudisCrypt.Lens.compl_footprint {a s : Type} (l : Lens a s) :
    (l.footprint)ᶜ = l.compl.footprint := by
  haveI : disjoint l.compl l := ⟨fun st v w => by
    induction v using Quotient.inductionOn
    rename_i u
    change l.set (l.get (l.set w st)) u = l.set w (l.set (l.get st) u)
    rw [l.set_get, l.set_set]⟩
  refine le_antisymm ?_ (Lens.footprint_le_compl_of_disjoint l.compl l)
  -- SUBSTANTIVE HALF: `(l.footprint)ᶜ ≤ l.compl.footprint`.  Every kernel `t` commuting with all
  -- `l`-updates is the `l.compl`-lift of its own complement marginal: write-equivariance against
  -- constant `l`-writes lets the surrounding overwrites reassemble `t` exactly.
  intro t ht
  by_cases hs : Nonempty s
  · obtain ⟨σ₀⟩ := hs
    -- write-equivariance of `t` against constant `l`-writes
    have hequiv : ∀ (x : a) (σ : s), t (l.set x σ) = t σ >>= fun τ => pure (l.set x τ) := by
      intro x σ
      have hcomm := Submonoid.mem_centralizer_iff.mp ht
        (diracKer (l.liftFunction (Function.const a x)))
        (l.diracKer_liftFunction_mem_footprint (Function.const a x))
      have h1 := congrFun hcomm σ
      calc t (l.set x σ)
          = (pure (l.set x σ) : SubProbability s) >>= t := by rw [SubProbability.pure_bind]
        _ = t σ >>= fun τ => pure (l.set x τ) := h1.symm
    -- `t` is the `l.compl`-lift of its complement marginal at `σ₀`
    have hlift : l.compl.liftSubProbability
        (fun q => t (l.compl.set q σ₀) >>= fun τ => pure (l.compl.get τ)) = t := by
      funext σ
      change (t (l.compl.set (l.compl.get σ) σ₀)
              >>= fun τ => (pure (l.compl.get τ) : SubProbability l.ComplContent))
          >>= (fun q => (pure (l.compl.set q σ) : SubProbability s)) = t σ
      have e1 : l.compl.set (l.compl.get σ) σ₀ = l.set (l.get σ₀) σ := rfl
      rw [e1, hequiv (l.get σ₀) σ, SubProbability.bind_assoc, SubProbability.bind_assoc]
      have step : ∀ τ' : s,
          ((pure (l.set (l.get σ₀) τ') : SubProbability s) >>= fun τ =>
            (pure (l.compl.get τ) : SubProbability l.ComplContent) >>= fun q =>
              (pure (l.compl.set q σ) : SubProbability s))
          = pure (l.set (l.get σ) τ') := fun τ' => by
        rw [SubProbability.pure_bind, SubProbability.pure_bind, Lens.compl_get_set]
        rfl
      have h2 : t σ >>= (fun τ' => (pure (l.set (l.get σ) τ') : SubProbability s)) = t σ :=
        (hequiv (l.get σ) σ).symm.trans (congrArg t (l.get_set σ))
      refine Eq.trans ?_ h2
      congr 1
      funext τ'
      exact step τ'
    rw [← hlift]
    exact Mlocalized_in_footprint l.compl
      (fun q => t (l.compl.set q σ₀) >>= fun τ => pure (l.compl.get τ))
  · -- empty state: every kernel is `pure`
    have ht' : t = pure := funext fun σ => absurd ⟨σ⟩ hs
    rw [ht']
    exact l.compl.footprint.id


/-- **The complement of `Lens.fst`, as a footprint, is `Lens.snd`.** `(Lens.fst).compl`
    has abstract `ComplContent` type, so this is a footprint equality (via the getter
    that identifies `fst.compl.get` with `snd.get`), not a lens equality. -/
theorem _root_.GaudisCrypt.Lens.fst_compl_footprint {a b : Type} :
    (Lens.fst : Lens a (a × b)).compl.footprint = (Lens.snd : Lens b (a × b)).footprint := by
  haveI : disjoint (Lens.fst : Lens a (a × b)).compl (Lens.snd : Lens b (a × b)).compl :=
    ⟨fun st v w => by
      induction v using Quotient.inductionOn
      induction w using Quotient.inductionOn
      rfl⟩
  haveI : disjoint (Lens.snd : Lens b (a × b)) (Lens.fst : Lens a (a × b)) :=
    ⟨fun _ _ _ => rfl⟩
  refine le_antisymm ?_ ?_
  · have h := Lens.footprint_le_compl_of_disjoint
      (Lens.fst : Lens a (a × b)).compl (Lens.snd : Lens b (a × b)).compl
    rw [← Lens.compl_footprint (Lens.snd : Lens b (a × b)), Footprint.compl_compl] at h
    exact h
  · rw [← Lens.compl_footprint]
    exact Lens.footprint_le_compl_of_disjoint _ _


theorem disjoint_lenses_footprint_inf (l1 : Lens a s) (l2 : Lens b s) [disjoint l1 l2] :
  l1.footprint ⊓ l2.footprint = ⊥ := by
  refine le_antisymm (fun u hu => ?_) bot_le
  obtain ⟨hu1, hu2⟩ := hu
  -- `⊥ = CC ∅` is the centre of the kernel monoid: show `u` commutes with every kernel.
  show u ∈ (Footprint.from ∅).updates
  rw [Footprint.from_updates]
  refine Set.mem_centralizer_iff.mpr fun k _ => ?_
  by_cases hs : Nonempty s
  · obtain ⟨σ₀⟩ := hs
    haveI : Nonempty s := ⟨σ₀⟩
    haveI : ProgramSpec.{0} := ⟨PUnit⟩   -- vestigial section instance on the extraction lemma
    -- extraction: `u` is an `l1`-localized kernel
    obtain ⟨κ, hκ⟩ : ∃ κ, l1.liftSubProbability κ = u :=
      ⟨_, FVP.footprint_updateK_image l1 σ₀ hu1⟩
    -- `u` commutes with every `l1`-lift, hence `κ` is central in the base kernel monoid
    haveI : disjoint l2 l1 := disjoint.symm ‹disjoint l1 l2›
    have hcompl : u ∈ (l1.footprint)ᶜ.updates :=
      Lens.footprint_le_compl_of_disjoint l2 l1 hu2
    have hκcen : ∀ ρ : a → SubProbability a, κ * ρ = ρ * κ := fun ρ => by
      have hcomm := Submonoid.mem_centralizer_iff.mp hcompl
        (l1.liftSubProbability ρ) (Mlocalized_in_footprint l1 ρ)
      refine updateK_injective l1 ?_
      rw [updateK_mul, updateK_mul, hκ]
      exact hcomm.symm
    -- constant-mass transport: `κ v` is `κ (l1.get σ₀)` with the value overwritten
    have htrans : ∀ v : a, κ v = κ (l1.get σ₀) >>= fun _ => pure v := fun v => by
      have h := congrFun (hκcen (diracKer (Function.const a v))) (l1.get σ₀)
      calc κ v
          = (pure v : SubProbability a) >>= κ := by rw [SubProbability.pure_bind]
        _ = κ (l1.get σ₀) >>= diracKer (Function.const a v) := h
        _ = κ (l1.get σ₀) >>= fun _ => pure v := rfl
    -- hence `u` is a mass-scaled identity …
    have hu_form : ∀ σ : s, u σ = κ (l1.get σ₀) >>= fun _ => pure σ := fun σ => by
      rw [← hκ]
      show κ (l1.get σ) >>= (fun w => (pure (l1.set w σ) : SubProbability s)) = _
      rw [htrans (l1.get σ), SubProbability.bind_assoc]
      congr 1; funext _
      rw [SubProbability.pure_bind, l1.get_set]
    -- … and mass-scaled identities are central
    funext σ
    show u σ >>= k = k σ >>= u
    rw [hu_form σ, SubProbability.bind_assoc]
    calc (κ (l1.get σ₀) >>= fun _ => ((pure σ : SubProbability s) >>= k))
        = κ (l1.get σ₀) >>= fun _ => k σ := by
          congr 1; funext _; rw [SubProbability.pure_bind]
      _ = k σ >>= fun τ => κ (l1.get σ₀) >>= fun _ => pure τ := by
          rw [bind_swap (k σ) (κ (l1.get σ₀)) (fun _ τ => pure τ)]
          congr 1; funext _
          rw [SubProbability.bind_pure]
      _ = k σ >>= u := by
          congr 1; funext τ
          rw [hu_form τ]
  · exact funext fun σ => absurd ⟨σ⟩ hs


private theorem pair_footprint_fst_snd :
    (Lens.fst : Lens a (a×b)).footprint ⊔ (Lens.snd : Lens b (a×b)).footprint = ⊤ := by
  haveI : disjoint (Lens.fst : Lens a (a × b)).compl (Lens.snd : Lens b (a × b)).compl :=
    ⟨fun st v w => by
      induction v using Quotient.inductionOn
      induction w using Quotient.inductionOn
      rfl⟩
  -- the complement of the join is the meet of the complement corners, which is trivial
  have hcompl : ((Lens.fst : Lens a (a×b)).footprint ⊔ (Lens.snd : Lens b (a×b)).footprint)ᶜ
      = ⊥ := by
    refine le_antisymm ?_ bot_le
    refine le_trans (le_inf (Footprint.compl_le_compl le_sup_left)
      (Footprint.compl_le_compl le_sup_right)) ?_
    rw [Lens.compl_footprint, Lens.compl_footprint]
    exact le_of_eq (disjoint_lenses_footprint_inf _ _)
  -- `⊥ᶜ = ⊤`: everything commutes with the centre
  have hbot : ((⊥ : Footprint (a × b))ᶜ : Footprint (a × b)) = ⊤ := by
    refine le_antisymm le_top fun u _ => ?_
    refine Submonoid.mem_centralizer_iff.mpr fun z hz => ?_
    have hu : u ∈ Set.centralizer (∅ : Set ((a × b) → SubProbability (a × b))) :=
      Set.mem_centralizer_iff.mpr fun m hm => absurd hm (Set.notMem_empty m)
    exact (Set.mem_centralizer_iff.mp hz u hu).symm
  calc (Lens.fst : Lens a (a×b)).footprint ⊔ (Lens.snd : Lens b (a×b)).footprint
      = (((Lens.fst : Lens a (a×b)).footprint ⊔ (Lens.snd : Lens b (a×b)).footprint)ᶜ)ᶜ :=
        (Footprint.compl_compl _).symm
    _ = ((⊥ : Footprint (a × b))ᶜ : Footprint (a × b)) := by rw [hcompl]
    _ = ⊤ := hbot

/-- **The footprint of a paired lens is the join of the components' footprints.**

    The `≥` direction is elementary: each component factors through the pair
    (`pair_fst`/`pair_snd`), so its footprint is a `liftFootprint` of a sub-`⊤`
    footprint, hence `≤` the pair's own footprint.

    The `≤` direction is the product/"corner"-structure theorem: lifting through the
    pair distributes over `pair_footprint_fst_snd` via `Lens.liftFootprint_sup`, and the
    two lifted corners are the component footprints by `chain_footprint` + `pair_fst`/`pair_snd`. -/
theorem pair_footprint {a b m : Type} (x : Lens a m) (y : Lens b m) [disjoint x y] :
    (Lens.pair x y).footprint = x.footprint ⊔ y.footprint := by
  calc (Lens.pair x y).footprint
      = (Lens.pair x y).liftFootprint ⊤ := (Lens.liftFootprint_top _).symm
    _ = (Lens.pair x y).liftFootprint
          ((Lens.fst : Lens a (a×b)).footprint ⊔ (Lens.snd : Lens b (a×b)).footprint) := by
        rw [pair_footprint_fst_snd]
    _ = (Lens.pair x y).liftFootprint (Lens.fst : Lens a (a×b)).footprint
          ⊔ (Lens.pair x y).liftFootprint (Lens.snd : Lens b (a×b)).footprint :=
        Lens.liftFootprint_sup _ _ _
    _ = (Lens.chain (Lens.pair x y) Lens.fst).footprint
          ⊔ (Lens.chain (Lens.pair x y) Lens.snd).footprint := by
        rw [← Lens.chain_footprint, ← Lens.chain_footprint]
    _ = x.footprint ⊔ y.footprint := by rw [pair_fst, pair_snd]
