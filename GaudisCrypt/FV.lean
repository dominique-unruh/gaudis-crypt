import GaudisCrypt.Language.Modules.InductiveFunctions
import GaudisCrypt.Footprint

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

open GaudisCrypt.Language.Modules
open GaudisCrypt.Language.Modules.InductiveFunctions
open GaudisCrypt.Language.Programs
open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics


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


private lemma kmul_apply {m} (f g : m → SubProbability m) (x : m) : (f * g) x = g x >>= f := rfl

/-- **`lens.liftSubProbability` is multiplicative**, hence a monoid homomorphism on kernels. The lens
    laws (`set_get`, `set_set`) make the two localizations of a Kleisli composition agree. -/
lemma updateK_mul {a b} (lens : Lens a b) (κ₁ κ₂ : a → SubProbability a) :
    lens.liftSubProbability (κ₁ * κ₂) = lens.liftSubProbability κ₁ * lens.liftSubProbability κ₂ := by
  funext st
  simp only [kmul_apply, Lens.liftSubProbability]
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

/-- The generator transform underlying `fvP_reduce`: given a joint kernel `f` on `a × b`,
an input distribution `i` on `b`, and a weighting `o` on the `b`-output, produce the `a`-kernel
that feeds `i`, runs `f`, and weights/discards the `b`-component via `o`. Named so the
`fvP_reduce_sup` reasoning can manipulate the generator set without the inline lambda. -/
noncomputable def _root_.GaudisCrypt.Language.Lens.Lens.reduceSubProbability {a b : Type} (lens : Lens a b)
    (p : (b → SubProbability b) × (Unit → SubProbability lens.ComplContent) × (lens.ComplContent → SubProbability Unit)) :
    a → SubProbability a :=
  fun m => do
    let m' ← p.2.1 ()
    let m'' ← p.1 (lens.splitSpace.invFun (m, m'))
    let _ ← p.2.2 (lens.compl.get m'')
    return lens.get m''

/-- Reading the focus of a reconstructed state recovers the focus component. -/
private lemma splitSpace_invFun_get {a b} (lens : Lens a b) (m : a) (c : lens.ComplContent) :
    lens.get (lens.splitSpace.invFun (m, c)) = m :=
  congrArg Prod.fst (lens.splitSpace.apply_symm_apply (m, c))

/-- Reading the complement of a reconstructed state recovers the complement component. -/
private lemma splitSpace_invFun_compl_get {a b} (lens : Lens a b) (m : a) (c : lens.ComplContent) :
    lens.compl.get (lens.splitSpace.invFun (m, c)) = c :=
  congrArg Prod.snd (lens.splitSpace.apply_symm_apply (m, c))

/-- Overwriting the focus of a reconstructed state is the same as reconstructing with a new focus. -/
private lemma splitSpace_invFun_set {a b} (lens : Lens a b) (m a' : a) (c : lens.ComplContent) :
    lens.set a' (lens.splitSpace.invFun (m, c)) = lens.splitSpace.invFun (a', c) := by
  apply lens.splitSpace.injective
  rw [show lens.splitSpace (lens.splitSpace.invFun (a', c)) = (a', c) from
        lens.splitSpace.apply_symm_apply (a', c)]
  refine Prod.ext ?_ ?_
  · show lens.get (lens.set a' (lens.splitSpace.invFun (m, c))) = a'
    rw [lens.set_get]
  · show lens.compl.get (lens.set a' (lens.splitSpace.invFun (m, c))) = c
    rw [show lens.compl.get (lens.set a' (lens.splitSpace.invFun (m, c)))
          = lens.compl.get (lens.splitSpace.invFun (m, c)) from
        Quotient.sound ⟨lens.get (lens.splitSpace.invFun (m, c)), by rw [lens.set_set, lens.get_set]⟩,
      splitSpace_invFun_compl_get]

/-- Kleisli product of `a × b`-kernels in bind form. -/
-- TODO not needed, just use def on *
theorem kmul_prod_apply {a b : Type} (F G : a × b → SubProbability (a × b)) (x : a × b) :
    (F * G) x = G x >>= F := rfl


/-- Post-composing with a localized kernel, evaluated pointwise. -/
private lemma mul_updateK_apply {a b} (lens : Lens a b) (f : b → SubProbability b)
    (h : a → SubProbability a) (s : b) :
    (f * lens.liftSubProbability h) s = h (lens.get s) >>= fun a'' => f (lens.set a'' s) := by
  simp only [kmul_apply, Lens.liftSubProbability, SubProbability.bind_assoc, SubProbability.pure_bind]

/-- Pre-composing with a localized kernel, evaluated pointwise. -/
private lemma updateK_mul_apply {a b} (lens : Lens a b) (f : b → SubProbability b)
    (h : a → SubProbability a) (s : b) :
    (lens.liftSubProbability h * f) s
      = f s >>= fun s' => h (lens.get s') >>= fun a'' => pure (lens.set a'' s') := by
  rw [kmul_apply]; rfl

/-- Overwriting the focus leaves the complement class unchanged. -/
private lemma compl_get_set {a b} (lens : Lens a b) (a' : a) (x : b) :
    lens.compl.get (lens.set a' x) = lens.compl.get x :=
  Quotient.sound ⟨lens.get x, by rw [lens.set_set, lens.get_set]⟩

/-- **Left Fubini identity.** Pre-composing a reduced generator with `h` equals reducing the joint
kernel pre-composed with the lift `lens.liftSubProbability h`. -/
theorem reduceBaseGen_mul_left {a b : Type} (lens : Lens a b)
    (f : b → SubProbability b) (i : Unit → SubProbability lens.ComplContent)
    (o : lens.ComplContent → SubProbability Unit) (h : a → SubProbability a) :
    h * Lens.reduceSubProbability lens (f, i, o)
      = Lens.reduceSubProbability lens (lens.liftSubProbability h * f, i, o) := by
  funext m
  have lhs : (h * Lens.reduceSubProbability lens (f, i, o)) m
      = i () >>= fun m' => f (lens.splitSpace.invFun (m, m')) >>= fun m'' =>
          o (lens.compl.get m'') >>= fun _ => h (lens.get m'') := by
    change Lens.reduceSubProbability lens (f, i, o) m >>= h = _
    simp only [Lens.reduceSubProbability]
    rw [SubProbability.bind_assoc]
    congr 1; funext m'
    rw [SubProbability.bind_assoc]
    congr 1; funext m''
    rw [SubProbability.bind_assoc]
    congr 1; funext _
    rw [SubProbability.pure_bind]
  have rhs : Lens.reduceSubProbability lens (lens.liftSubProbability h * f, i, o) m
      = i () >>= fun m' => f (lens.splitSpace.invFun (m, m')) >>= fun m'' =>
          h (lens.get m'') >>= fun a'' => o (lens.compl.get m'') >>= fun _ => pure a'' := by
    simp only [Lens.reduceSubProbability]
    congr 1; funext m'
    rw [updateK_mul_apply, SubProbability.bind_assoc]
    congr 1; funext m''
    rw [SubProbability.bind_assoc]
    congr 1; funext a''
    rw [SubProbability.pure_bind, compl_get_set, lens.set_get]
  have inner : ∀ m'' : b,
      o (lens.compl.get m'') >>= (fun _ => h (lens.get m''))
        = h (lens.get m'') >>= fun a'' => o (lens.compl.get m'') >>= fun _ => pure a'' := by
    intro m''
    conv_lhs => rw [← SubProbability.bind_pure (h (lens.get m''))]
    exact bind_swap (o (lens.compl.get m'')) (h (lens.get m'')) (fun a'' _ => pure a'')
  rw [lhs, rhs]
  congr 1; funext m'
  congr 1; funext m''
  exact inner m''

/-- **Right Fubini identity.** Post-composing a reduced generator with `h` equals reducing the
joint kernel post-composed with the lift `lens.liftSubProbability h`. -/
theorem reduceBaseGen_mul_right {a b : Type} (lens : Lens a b)
    (f : b → SubProbability b) (i : Unit → SubProbability lens.ComplContent)
    (o : lens.ComplContent → SubProbability Unit) (h : a → SubProbability a) :
    Lens.reduceSubProbability lens (f, i, o) * h = Lens.reduceSubProbability lens (f * lens.liftSubProbability h, i, o) := by
  funext m
  have lhs : (Lens.reduceSubProbability lens (f, i, o) * h) m
      = h m >>= fun a'' => i () >>= fun m' =>
          f (lens.splitSpace.invFun (a'', m')) >>= fun m'' =>
            o (lens.compl.get m'') >>= fun _ => pure (lens.get m'') := rfl
  have rhs : Lens.reduceSubProbability lens (f * lens.liftSubProbability h, i, o) m
      = i () >>= fun m' => h m >>= fun a'' =>
          f (lens.splitSpace.invFun (a'', m')) >>= fun m'' =>
            o (lens.compl.get m'') >>= fun _ => pure (lens.get m'') := by
    simp only [Lens.reduceSubProbability]
    congr 1; funext m'
    rw [mul_updateK_apply, splitSpace_invFun_get, SubProbability.bind_assoc]
    congr 1; funext a''
    rw [splitSpace_invFun_set]
  rw [lhs, rhs]
  exact bind_swap (h m) (i ()) (fun m' a'' =>
    f (lens.splitSpace.invFun (a'', m')) >>= fun m'' =>
      o (lens.compl.get m'') >>= fun _ => pure (lens.get m''))

open Classical MeasureTheory in
/-- **Slice determination.** A kernel `K : b → SubProbability b` is determined by all its reduced
generators for a fixed `lens`: feeding a point input `i = δ_β` and an indicator weight `o = [· = γ]`
recovers `K` on the slice `splitSpace.invFun (·, β)` restricted to complement-output `γ`. Ranging
over all `(β, γ)` pins down `K` on every state. This is the one genuinely measure-theoretic
ingredient (`discreteMeasure.ext` on singletons). -/
theorem Lens.reduceSubProbability_ext {a b : Type} (lens : Lens a b) (K L : b → SubProbability b)
    (hKL : ∀ i o, Lens.reduceSubProbability lens (K, i, o) = Lens.reduceSubProbability lens (L, i, o)) : K = L := by
  -- A point input + indicator weight turns `Lens.reduceSubProbability` into a coordinate slice.
  have reduceEq : ∀ (M : b → SubProbability b) (m : a) (β γ : lens.ComplContent),
      Lens.reduceSubProbability lens (M, (fun _ => pure β), (fun c => if c = γ then pure () else ⊥)) m
        = M (lens.splitSpace.invFun (m, β)) >>= fun s =>
            if lens.compl.get s = γ then (pure (lens.get s) : SubProbability a) else ⊥ := by
    intro M m β γ
    simp only [Lens.reduceSubProbability]
    rw [SubProbability.pure_bind]
    congr 1; funext s
    by_cases hs : lens.compl.get s = γ
    · rw [if_pos hs, if_pos hs, SubProbability.pure_bind]
    · rw [if_neg hs, if_neg hs, SubProbability.bot_bind]
  -- The slice's mass is the joint kernel's mass on the lens-rectangle `get⁻¹ B ∩ compl⁻¹ {γ}`.
  have slice_apply2 : ∀ (μ : SubProbability b) (γ : lens.ComplContent) (B : Set a),
      (μ >>= fun s =>
          if lens.compl.get s = γ then (pure (lens.get s) : SubProbability a) else ⊥).1 B
        = μ.1 (lens.get ⁻¹' B ∩ lens.compl.get ⁻¹' {γ}) := by
    intro μ γ B
    letI : MeasurableSpace b := ⊤
    letI : MeasurableSpace a := ⊤
    change (Measure.bind μ.1 (fun s =>
        (if lens.compl.get s = γ then (pure (lens.get s) : SubProbability a) else ⊥).1)) B
      = μ.1 (lens.get ⁻¹' B ∩ lens.compl.get ⁻¹' {γ})
    rw [Measure.bind_apply (by trivial) (measurable_from_top.aemeasurable)]
    rw [show (fun s : b =>
          (if lens.compl.get s = γ then (pure (lens.get s) : SubProbability a) else ⊥).1 B)
          = Set.indicator (lens.get ⁻¹' B ∩ lens.compl.get ⁻¹' {γ}) 1 from ?_]
    · rw [lintegral_indicator_one (by trivial)]
    · funext s
      by_cases hs : lens.compl.get s = γ
      · rw [if_pos hs]
        change (@MeasureTheory.Measure.dirac a ⊤ (lens.get s)) B
            = Set.indicator (lens.get ⁻¹' B ∩ lens.compl.get ⁻¹' {γ}) 1 s
        rw [MeasureTheory.Measure.dirac_apply' (lens.get s) (by trivial)]
        simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, hs,
          and_true, Pi.one_apply]
      · rw [if_neg hs]
        rw [show ((⊥ : SubProbability a).1 : Measure a) = 0 from rfl]
        simp only [Measure.coe_zero, Pi.zero_apply, Set.indicator, Set.mem_inter_iff,
          Set.mem_preimage, Set.mem_singleton_iff, hs, and_false, if_false]
  have splitSpace_eq : ∀ s : b, lens.splitSpace.invFun (lens.get s, lens.compl.get s) = s :=
    fun s => lens.splitSpace.symm_apply_apply s
  funext s₀
  apply Subtype.ext
  refine discreteMeasure.ext (K s₀).2.2 (L s₀).2.2 (fun s => ?_)
  have hsingle : lens.get ⁻¹' {lens.get s} ∩ lens.compl.get ⁻¹' {lens.compl.get s} = {s} := by
    ext s'
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      apply lens.splitSpace.injective
      show (lens.get s', lens.compl.get s') = (lens.get s, lens.compl.get s)
      rw [h1, h2]
    · rintro rfl; exact ⟨rfl, rfl⟩
  have key : ∀ ρ : SubProbability b,
      ρ.1 {s}
        = (ρ >>= fun s' =>
            if lens.compl.get s' = lens.compl.get s then (pure (lens.get s') : SubProbability a)
            else ⊥).1 {lens.get s} := by
    intro ρ
    rw [slice_apply2 ρ (lens.compl.get s) {lens.get s}, hsingle]
  rw [key (K s₀), key (L s₀)]
  have hcomm := congrFun (hKL (fun _ => pure (lens.compl.get s₀))
    (fun c => if c = lens.compl.get s then pure () else ⊥)) (lens.get s₀)
  rw [reduceEq K (lens.get s₀) (lens.compl.get s₀) (lens.compl.get s),
      reduceEq L (lens.get s₀) (lens.compl.get s₀) (lens.compl.get s),
      splitSpace_eq s₀] at hcomm
  rw [hcomm]

instance [Nonempty s] (lens : Lens a s) : Nonempty lens.ComplContent :=
  ⟨Quotient.mk lens.equal_outside_setoid (Classical.arbitrary s)⟩

@[reducible] def _root_.GaudisCrypt.Language.Lens.Lens.instContentNonempty [Nonempty s]
    (lens : Lens a s) : Nonempty a := ⟨lens.get (Classical.arbitrary s)⟩

lemma Footprint.empty_trivial (h : ¬ Nonempty a) (r s : Footprint a) : r = s := by
  haveI : IsEmpty a := not_nonempty_iff.mp h
  apply footprint_eq_of_updates
  ext f
  have hf : f = pure := funext fun x => isEmptyElim x
  subst hf
  exact ⟨fun _ => s.id, fun _ => r.id⟩


lemma updateK_image_cc_subset {a b : Type} (lens : Lens a b)
    (W : Set (a → SubProbability a)) :
    lens.liftSubProbability '' Set.centralizer (Set.centralizer W)
      ⊆ Set.centralizer (Set.centralizer (lens.liftSubProbability '' W)) := by
  rintro _ ⟨h, hh, rfl⟩
  rw [Set.mem_centralizer_iff]
  intro G hG
  -- Every reduced generator of `G` commutes with `W`.
  have hred : ∀ i o, Lens.reduceSubProbability lens (G, i, o) ∈ Set.centralizer W := by
    intro i o
    rw [Set.mem_centralizer_iff]
    intro w hw
    rw [reduceBaseGen_mul_left, reduceBaseGen_mul_right]
    rw [(Set.mem_centralizer_iff.mp hG) (lens.liftSubProbability w) ⟨w, hw, rfl⟩]
  -- `h` commutes with each of those generators, so the lifts agree on every slice.
  apply Lens.reduceSubProbability_ext lens
  intro i o
  rw [← reduceBaseGen_mul_right, ← reduceBaseGen_mul_left]
  exact (Set.mem_centralizer_iff.mp hh) (Lens.reduceSubProbability lens (G, i, o)) (hred i o)




/-- **`Lens.liftFootprint` distributes over joins** (i.e. `extend` is a join-homomorphism), for an arbitrary
lens. The reverse (`≥`) direction is monotonicity; the hard (`≤`) direction reduces — exactly as in
`fvP_extend_sup_simpler` — to the extend-side double-commutant inclusion, here in its general form
`updateK_image_cc_subset`. -/
theorem Lens.liftFootprint_sup {a b} (lens : Lens a b) (r₁ r₂ : Footprint a) :
    Lens.liftFootprint lens (r₁ ⊔ r₂) = Lens.liftFootprint lens r₁ ⊔ Lens.liftFootprint lens r₂ := by
  wlog ne : Nonempty b; { apply Footprint.empty_trivial ne }
  refine le_antisymm ?_
    (sup_le (Lens.liftFootprint_mono lens le_sup_left) (Lens.liftFootprint_mono lens le_sup_right))
  unfold Lens.liftFootprint
  rw [footprint_from_union, ← Set.image_union, footprint_sup_updates,
      Footprint.from_le_iff, Footprint.from_updates]
  exact updateK_image_cc_subset lens _

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
          updateK_image_cc_subset lens _
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
    rw [← reduceBaseGen_mul_left, ← reduceBaseGen_mul_right]
    exact (hcomm (Lens.reduceSubProbability lens (g, i, o))
      ⟨(g, i, o), ⟨hg, Set.mem_univ _, Set.mem_univ _⟩, rfl⟩).symm
  · intro hcon k hk
    obtain ⟨⟨g, i, o⟩, ⟨hg, -, -⟩, rfl⟩ := hk
    rw [reduceBaseGen_mul_right, reduceBaseGen_mul_left, hcon g hg]


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
identities (`reduceBaseGen_mul_left`/`_right`) turn `h`-commutation of reduced generators into
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
    rw [← reduceBaseGen_mul_right, ← reduceBaseGen_mul_left]
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
  rw [reduceBaseGen_mul_left, reduceBaseGen_mul_right, hfĥ]


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
noncomputable def _root_.GaudisCrypt.Language.Semantics.ProgramDenotation.footprint'
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
    (so the `diracKer` generators of `lens.footprint` all sit inside the localized-kernel image). -/
private lemma updateK_diracKer {a s : Type} (lens : Lens a s) (g : Function.End a) :
    lens.liftSubProbability (diracKer g) = diracKer (lens.liftFunction g) := by
  funext st
  show (pure (g (lens.get st)) : SubProbability a) >>= (fun a' => pure (lens.set a' st))
     = pure (lens.set (g (lens.get st)) st)
  rw [SubProbability.pure_bind]

omit [ProgramSpec] in
/-- **The cheap half of the lens-corner double-commutant theorem.** The bicommutant closure of the
    full set of `lens`-localized kernels is exactly `lens.footprint`: the `diracKer` generators of
    `lens.footprint` lie inside the localized image (`updateK_diracKer`), and every localized kernel
    lies in `lens.footprint` (`Mlocalized_in_footprint`), so both sides share a bicommutant closure.

    This is scaffolding toward closing `fvP_reduce_sup` / `fvP_extend_sup`.  The genuinely hard,
    still-open part is that this image is *already* closed — i.e.
    `lens.footprint.updates ⊆ lens.liftSubProbability '' univ` (every range element is a localized kernel) plus
    injectivity of `updateK` — which together would give the lens-corner tensor/commutant
    factorization the two `_sup` reverse directions need. -/
theorem updateK_image_univ_cc {a s : Type} (lens : Lens a s) :
    Set.centralizer (Set.centralizer (lens.liftSubProbability '' (Set.univ : Set (a → SubProbability a))))
      = lens.footprint.updates := by
  have hI : lens.liftSubProbability '' (Set.univ : Set (a → SubProbability a)) ⊆ lens.footprint.updates := by
    rintro _ ⟨ρ, _, rfl⟩
    exact Mlocalized_in_footprint lens ρ
  have hD : (Set.range fun g : Function.End a => diracKer (lens.liftFunction g))
      ⊆ lens.liftSubProbability '' (Set.univ : Set (a → SubProbability a)) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨diracKer g, Set.mem_univ _, updateK_diracKer lens g⟩
  have hprD : lens.footprint.updates
      = Set.centralizer (Set.centralizer
          (Set.range fun g : Function.End a => diracKer (lens.liftFunction g))) :=
    Footprint.from_updates _
  apply Set.Subset.antisymm
  · calc Set.centralizer (Set.centralizer (lens.liftSubProbability '' (Set.univ : Set (a → SubProbability a))))
        ⊆ Set.centralizer (Set.centralizer lens.footprint.updates) := cl_mono hI
      _ = lens.footprint.updates := footprint_updates_cc lens.footprint
  · rw [hprD]
    exact cl_mono hD

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
    hsub ((Footprint.from_le_iff _ lens.compl.footprint).mp le_rfl ⟨h, rfl⟩)
  rw [Footprint.updates_eq_centralizer_compl lens.footprint] at hp
  have hcomm := Submonoid.mem_centralizer_iff.mp hp (diracKer (lens.compl.liftFunction h)) hk
  have hst := congrFun hcomm st
  simp only [kmul_apply] at hst
  rw [show (diracKer (lens.compl.liftFunction h) st) = pure (lens.compl.liftFunction h st) from rfl,
      SubProbability.pure_bind] at hst
  exact hst.symm

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
                SubProbability.bind_assoc, splitSpace_invFun_get, splitSpace_invFun_set,
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

end FVP


/-! ## Footprint/reduce/lift algebra

General footprint, `fvP_reduce` and `Lens.liftFootprint` facts, independent of any particular
program spec. -/

/-- **Complement is order-reversing on `Footprint`** (`le`/`compl` swap): `R ≤ Sᶜ ↔ S ≤ Rᶜ`.
    Both sides say every `R`-update commutes with every `S`-update, so the relation is symmetric in
    `R`, `S`. -/
theorem Footprint.le_compl_comm {m : Type} (R S : Footprint m) : R ≤ Sᶜ ↔ S ≤ Rᶜ := by
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

/-- **The lift of a `v.footprint`-update commutes with every `R`-update**, when the
    `L`-reduction of `R` is disjoint from `v.footprint`.  For `f ∈ v.footprint.updates` and
    `k ∈ R.updates`, the reduced generators `reduceSubProbability L (k, i, o)` lie in
    `(fvP_reduce L R).updates`, so `hred` makes them commute with `f`; the Fubini identities
    (`reduceBaseGen_mul_left`/`_right`) turn that into commutation of `L.liftSubProbability f`
    with `k` (via `reduceSubProbability_ext`). -/
theorem liftSubProbability_comm_of_reduce_disj {t s c : Type} {L : Lens s c}
    {v : Lens t s} {R : Footprint c}
    (hred : fvP_reduce L R ≤ (v.footprint)ᶜ)
    {f : s → SubProbability s} (hf : f ∈ v.footprint.updates)
    {k : c → SubProbability c} (hk : k ∈ R.updates) :
    L.liftSubProbability f * k = k * L.liftSubProbability f := by
  apply Lens.reduceSubProbability_ext L
  intro i o
  -- Each reduced generator of `k` is a generator of `fvP_reduce L R`, hence (by `hred`)
  -- commutes with `f ∈ v.footprint.updates`.
  have hgen : Lens.reduceSubProbability L (k, i, o) ∈ (fvP_reduce L R).updates := by
    rw [fvP_reduce_eq_from, Footprint.from_updates]
    exact Set.subset_centralizer_centralizer
      ⟨(k, i, o), ⟨hk, Set.mem_univ _, Set.mem_univ _⟩, rfl⟩
  have hcomm : f * Lens.reduceSubProbability L (k, i, o)
      = Lens.reduceSubProbability L (k, i, o) * f :=
    (Submonoid.mem_centralizer_iff.mp (hred hgen)) f hf
  rw [reduceBaseGen_mul_left, reduceBaseGen_mul_right] at hcomm
  exact hcomm

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
  -- Goal: diracKer ((L.chain v).liftFunction g) ∈ Rᶜ.updates = centralizer R.updates
  show diracKer ((L.chain v).liftFunction g) ∈ Rᶜ.updates
  rw [chain_liftFunction_diracKer]
  show L.liftSubProbability (diracKer (v.liftFunction g)) ∈ Submonoid.centralizer R.updates
  rw [Submonoid.mem_centralizer_iff]
  intro k hk
  have hg_mem : diracKer (v.liftFunction g) ∈ v.footprint.updates :=
    (Footprint.from_le_iff (Set.range fun h : Function.End t =>
      diracKer (v.liftFunction h)) v.footprint).mp le_rfl ⟨g, rfl⟩
  exact (liftSubProbability_comm_of_reduce_disj hred hg_mem hk).symm

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
