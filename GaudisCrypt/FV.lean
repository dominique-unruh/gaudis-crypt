import GaudisCrypt.Language.Modules.InductiveFunctions
import GaudisCrypt.ProbLensRange

/-!
# `fvP`: the computed-footprint (free-variables) layer over `ProbLensRange`

The probabilistic re-incarnation of the old `FV` development (now quarantined as
`CounterExamples/FV.lean`), rebased from the deterministic `TotLensRange`/`Function.End`
foundation onto `ProbLensRange` and the Kleisli monoid of sub-probability kernels
`m → SubProbability m`.

It instantiates the generic `InductiveFunctionGettersSetters`/`ReducibleGettersSetters`
machinery (from `Language.Modules.InductiveFunctions`) at `T := ProbLensRange`, giving a
syntactic over-approximation `fvP` of the part of the state a `Module`/`Procedure` can
read or modify, together with the soundness bound `fvP (m.toModule) ≤ fvPMexpr m`.

-/

open GaudisCrypt.Language.Modules
open GaudisCrypt.Language.Modules.InductiveFunctions
open GaudisCrypt.Language.Programs
open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics


/-! # fvP_extend_sup -/

-- fvP_extend_sup now called Lens.liftProbLensRange

/-- Two `ProbLensRange`s with the same `updates` are equal. -/
@[ext]
lemma probLensRange_eq_of_updates {m} {x y : ProbLensRange m} (h : x.updates = y.updates) :
    x = y := by
  obtain ⟨_, _, _, _⟩ := x
  obtain ⟨_, _, _, _⟩ := y
  simp only at h
  subst h
  rfl

private lemma submonoid_centralizer_carrier {m} (S : Set (m → SubProbability m)) :
    (Submonoid.centralizer S).carrier = Set.centralizer S := by
  ext x; simp [Submonoid.mem_centralizer_iff, Set.mem_centralizer_iff]

/-- Every `ProbLensRange` is its own bicommutant (the `double_commutant` field, in `Set` form). -/
@[simp]
lemma probLensRange_updates_cc {m} (r : ProbLensRange m) :
    Set.centralizer (Set.centralizer r.updates) = r.updates := by
  have h := r.double_commutant
  simpa only [submonoid_centralizer_carrier] using h

/-- The `updates` of a join is the double centralizer of the union of the `updates`. -/
private lemma probLensRange_sup_updates {m} (x y : ProbLensRange m) :
    (x ⊔ y).updates = Set.centralizer (Set.centralizer (x.updates ∪ y.updates)) := by
  change (ProbLensRange.from (x.updates ∪ y.updates)).updates = _
  exact ProbLensRange.from_updates _

/-- Bicommutant closure `cⁿ²` is monotone. -/
private lemma cl_mono {m} {A B : Set (m → SubProbability m)} (h : A ⊆ B) :
    Set.centralizer (Set.centralizer A) ⊆ Set.centralizer (Set.centralizer B) :=
  Set.centralizer_subset (Set.centralizer_subset h)


/-- `ProbLensRange.from` turns unions into joins. -/
lemma probLensRange_from_union {m} (A B : Set (m → SubProbability m)) :
    ProbLensRange.from A ⊔ ProbLensRange.from B = ProbLensRange.from (A ∪ B) := by
  apply probLensRange_eq_of_updates
  rw [probLensRange_sup_updates, ProbLensRange.from_updates, ProbLensRange.from_updates,
      ProbLensRange.from_updates]
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

lemma ProbLensRange.empty_trivial (h : ¬ Nonempty a) (r s : ProbLensRange a) : r = s := by
  haveI : IsEmpty a := not_nonempty_iff.mp h
  apply probLensRange_eq_of_updates
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




/-- **`Lens.liftProbLensRange` distributes over joins** (i.e. `extend` is a join-homomorphism), for an arbitrary
lens. The reverse (`≥`) direction is monotonicity; the hard (`≤`) direction reduces — exactly as in
`fvP_extend_sup_simpler` — to the extend-side double-commutant inclusion, here in its general form
`updateK_image_cc_subset`. -/
theorem Lens.liftProbLensRange_sup {a b} (lens : Lens a b) (r₁ r₂ : ProbLensRange a) :
    Lens.liftProbLensRange lens (r₁ ⊔ r₂) = Lens.liftProbLensRange lens r₁ ⊔ Lens.liftProbLensRange lens r₂ := by
  wlog ne : Nonempty b; { apply ProbLensRange.empty_trivial ne }
  refine le_antisymm ?_
    (sup_le (Lens.liftProbLensRange_mono lens le_sup_left) (Lens.liftProbLensRange_mono lens le_sup_right))
  unfold Lens.liftProbLensRange
  rw [probLensRange_from_union, ← Set.image_union, probLensRange_sup_updates,
      ProbLensRange.from_le_iff, ProbLensRange.from_updates]
  exact updateK_image_cc_subset lens _

/-- **`Lens.liftProbLensRange` distributes over arbitrary indexed suprema.**
    Generalises `Lens.liftProbLensRange_sup` from binary joins to indexed families. -/
theorem Lens.liftProbLensRange_iSup {a b : Type} {ι : Sort*} (lens : Lens a b)
    (rs : ι → ProbLensRange a) :
    Lens.liftProbLensRange lens (⨆ i, rs i) = ⨆ i, Lens.liftProbLensRange lens (rs i) := by
  wlog ne : Nonempty b; { apply ProbLensRange.empty_trivial ne }
  refine le_antisymm ?_ (iSup_le fun i => Lens.liftProbLensRange_mono lens (le_iSup rs i))
  change ProbLensRange.from (lens.liftSubProbability '' (⨆ i, rs i).updates) ≤
       ⨆ i, Lens.liftProbLensRange lens (rs i)
  rw [ProbLensRange.from_le_iff]
  have hiSup_rs : (⨆ i, rs i).updates =
      Set.centralizer (Set.centralizer (⋃ i, (rs i).updates)) := by
    change (ProbLensRange.from (⋃ x ∈ Set.range rs, x.updates)).updates = _
    rw [ProbLensRange.from_updates, Set.biUnion_range]
  have hiSup_lift : (⨆ i, Lens.liftProbLensRange lens (rs i)).updates =
      Set.centralizer (Set.centralizer (⋃ i, (Lens.liftProbLensRange lens (rs i)).updates)) := by
    change (ProbLensRange.from
        (⋃ x ∈ Set.range (Lens.liftProbLensRange lens ∘ rs), x.updates)).updates = _
    rw [ProbLensRange.from_updates, Set.biUnion_range]
    simp [Function.comp]
  rw [hiSup_rs, hiSup_lift]
  calc lens.liftSubProbability '' Set.centralizer (Set.centralizer (⋃ i, (rs i).updates))
      ⊆ Set.centralizer (Set.centralizer (lens.liftSubProbability '' ⋃ i, (rs i).updates)) :=
          updateK_image_cc_subset lens _
    _ = Set.centralizer (Set.centralizer (⋃ i, lens.liftSubProbability '' (rs i).updates)) := by
          rw [Set.image_iUnion]
    _ ⊆ Set.centralizer (Set.centralizer (⋃ i, (Lens.liftProbLensRange lens (rs i)).updates)) :=
          cl_mono (Set.iUnion_mono fun i => by
            simp only [Lens.liftProbLensRange, ProbLensRange.from_updates]
            exact Set.subset_centralizer_centralizer)

/-! # End of fvP_extend_sup -/

/-! # fvP_reduce_sup -/


-- DOMINIQUE READING

noncomputable
def fvP_reduce' {a b : Type} (lens : Lens a b) (range : ProbLensRange b) : ProbLensRange a :=
  ProbLensRange.from
    { f | ∀ g ∈ range.updates,
        (lens.liftSubProbability f : b → SubProbability b) * g
          = g * lens.liftSubProbability f }.centralizer

noncomputable
def fvP_reduce {a b} (lens : Lens a b) (range : ProbLensRange b) : ProbLensRange a :=
  ProbLensRange.from (Lens.reduceSubProbability lens '' (range.updates ×ˢ Set.univ ×ˢ Set.univ))

-- noncomputable
-- -- TODO: Just rename the above (later)
-- def fvP_reduce {a b} (lens : Lens a b) (range : ProbLensRange b) : ProbLensRange a :=
--   fvP_reduce lens range



/-- `fvP_reduce` is monotone: a larger range gives a larger reduced range. -/
theorem fvP_reduce_mono {a b} (lens : Lens a b) {r r' : ProbLensRange b} (h : r ≤ r') :
    fvP_reduce lens r ≤ fvP_reduce lens r' := by
  have hsub : r.updates ⊆ r'.updates := h
  apply ProbLensRange.from_mono
  gcongr


/-- `fvP_reduce` as `ProbLensRange.from` of the named generator set. -/
theorem fvP_reduce_eq_from {a b : Type} (lens : Lens a b) (range : ProbLensRange b) :
    fvP_reduce lens range
      = ProbLensRange.from (Lens.reduceSubProbability lens '' (range.updates ×ˢ Set.univ ×ˢ Set.univ)) := rfl

/-- **`fvP_reduce'` and `fvP_reduce` have the same generator centralizer.** The
centralizer of the reduced-generator image is exactly the lift-commutation constraint defining
`fvP_reduce'`: by the Fubini identities, `h` commutes with every `Lens.reduceSubProbability (g, i, o)`
(over all `i, o`) iff `Lens.fst.liftSubProbability h` commutes with `g` (the `⟸` direction is immediate;
the `⟹` uses
slice determination `reduceBaseExt`). -/
theorem centralizer_reduceBaseGen_image {a b : Type} (lens : Lens a b) (range : ProbLensRange b) :
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


/-- **`fvP_reduce'` equals `fvP_reduce`.** Both `ProbLensRange`s have `updates` equal to
the centralizer of the lift-commutation constraint set (`centralizer_reduceBaseGen_image` plus the
triple-centralizer collapse), so the restated lift-commutation form is literally the same footprint
as the explicit reduce-transform image. -/
theorem fvP_reduce'_eq {a b : Type} (lens : Lens a b) (range : ProbLensRange b) :
    fvP_reduce' lens range = fvP_reduce lens range := by
  apply probLensRange_eq_of_updates
  rw [fvP_reduce_eq_from, ProbLensRange.from_updates, centralizer_reduceBaseGen_image]
  unfold fvP_reduce'
  rw [ProbLensRange.from_updates, Set.centralizer_centralizer_centralizer]


/- /-- **The centralizer footprint `fvP_reduce` equals the split-then-reduce construction.** Bridges
the abstract `lens.liftSubProbability`-commutation definition with the concrete
`fvP_reduce ∘ Lens.liftProbLensRange ∘ split` pipeline (i.e. `fvP_reduce_new`), via the lift identity
`bijection_split_updateK` and the fact that the split pushforward `updateK` is an injective monoid
homomorphism. -/
theorem fvP_reduce_via_base' {a b : Type} (lens : Lens a b) (range : ProbLensRange b) :
    fvP_reduce lens range
      = fvP_reduce Lens.fst (Lens.liftProbLensRange (Lens.bijection (Lens.splitSpace lens)) range) := by
  rw [← fvP_reduce'_eq]
  unfold fvP_reduce fvP_reduce'
  congr 1
  congr 1
  ext f
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hf g hg
    have hmem : (Lens.fst).liftSubProbability f ∈
        Set.centralizer ((Lens.bijection (Lens.splitSpace lens)).liftSubProbability '' range.updates) := by
      rw [Set.mem_centralizer_iff]
      rintro _ ⟨g', hg', rfl⟩
      rw [← bijection_split_updateK, ← updateK_mul, ← updateK_mul, hf g' hg']
    have hcent : Set.centralizer ((Lens.liftProbLensRange (Lens.bijection (Lens.splitSpace lens)) range).updates)
        = Set.centralizer ((Lens.bijection (Lens.splitSpace lens)).liftSubProbability '' range.updates) := by
      unfold Lens.liftProbLensRange
      rw [ProbLensRange.from_updates, Set.centralizer_centralizer_centralizer]
    exact ((Set.mem_centralizer_iff.mp (hcent ▸ hmem)) g hg).symm
  · intro hf g hg
    have hgmem : (Lens.bijection (Lens.splitSpace lens)).liftSubProbability g
        ∈ (Lens.liftProbLensRange (Lens.bijection (Lens.splitSpace lens)) range).updates := by
      unfold Lens.liftProbLensRange
      rw [ProbLensRange.from_updates]
      exact Set.subset_centralizer_centralizer ⟨g, hg, rfl⟩
    have hcomm := hf _ hgmem
    rw [← bijection_split_updateK, ← updateK_mul, ← updateK_mul] at hcomm
    by_cases hne : Nonempty b
    · haveI := hne
      haveI : Nonempty (a × lens.ComplContent) := ⟨Lens.splitSpace lens (Classical.arbitrary b)⟩
      exact updateK_injective (Lens.bijection (Lens.splitSpace lens)) hcomm
    · funext st
      exact (hne ⟨st⟩).elim
 -/

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
theorem reduceBaseGen_sup_subset {a b : Type} (lens : Lens a b) (r₁ r₂ : ProbLensRange b) :
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
    rw [probLensRange_sup_updates] at hf
    exact (Set.mem_centralizer_iff.mp hf) (lens.liftSubProbability h) hĥ
  rw [reduceBaseGen_mul_left, reduceBaseGen_mul_right, hfĥ]


-- TODO: Do the =-case
theorem fvP_reduce_sup2 {a b} (lens : Lens a b) (r₁ r₂ : ProbLensRange b) :
    fvP_reduce lens (r₁ ⊔ r₂) ≤ fvP_reduce lens r₁ ⊔ fvP_reduce lens r₂ := by
  rw [fvP_reduce_eq_from, fvP_reduce_eq_from, fvP_reduce_eq_from,
    ProbLensRange.from_le_iff]
  set Z := ProbLensRange.from (Lens.reduceSubProbability lens '' (r₁.updates ×ˢ Set.univ ×ˢ Set.univ))
      ⊔ ProbLensRange.from (Lens.reduceSubProbability lens '' (r₂.updates ×ˢ Set.univ ×ˢ Set.univ)) with hZ
  have h1 : Lens.reduceSubProbability lens '' (r₁.updates ×ˢ Set.univ ×ˢ Set.univ) ⊆ Z.updates :=
    (ProbLensRange.from_le_iff _ _).mp le_sup_left
  have h2 : Lens.reduceSubProbability lens '' (r₂.updates ×ˢ Set.univ ×ˢ Set.univ) ⊆ Z.updates :=
    (ProbLensRange.from_le_iff _ _).mp le_sup_right
  refine (reduceBaseGen_sup_subset lens r₁ r₂).trans ?_
  rw [← probLensRange_updates_cc Z]
  exact Set.centralizer_subset (Set.centralizer_subset (Set.union_subset h1 h2))


/-- The reverse (`≤`) direction of `fvP_reduce'`'s join law — the genuinely hard
double-commutant direction — reduced to the already-proven `fvP_reduce_sup2` via the identification
`fvP_reduce' = fvP_reduce`. -/
-- TODO: Do the = case
theorem fvP_reduce'_sup2 {a b : Type} (lens : Lens a b) (r₁ r₂ : ProbLensRange b) :
    fvP_reduce' lens (r₁ ⊔ r₂) ≤ fvP_reduce' lens r₁ ⊔ fvP_reduce' lens r₂ := by
  rw [fvP_reduce'_eq, fvP_reduce'_eq, fvP_reduce'_eq]
  exact fvP_reduce_sup2 lens r₁ r₂

theorem fvP_reduce_sup1 {a b} (lens : Lens a b) (r₁ r₂ : ProbLensRange b) :
    fvP_reduce lens (r₁ ⊔ r₂) ≥ fvP_reduce lens r₁ ⊔ fvP_reduce lens r₂ :=
  sup_le (fvP_reduce_mono lens le_sup_left) (fvP_reduce_mono lens le_sup_right)


/-- The reduced footprint join law for `fvP_reduce`: both inequalities combine
(`fvP_reduce_sup1` and `fvP_reduce'_sup2`). -/
lemma fvP_reduce_sup {a b : Type} (lens : Lens a b) (r₁ r₂ : ProbLensRange b) :
    fvP_reduce lens (r₁ ⊔ r₂) = fvP_reduce lens r₁ ⊔ fvP_reduce lens r₂ := by
  refine le_antisymm ?_ (fvP_reduce_sup1 lens r₁ r₂)
  rw [← fvP_reduce'_eq, ← fvP_reduce'_eq, ← fvP_reduce'_eq]
  exact fvP_reduce'_sup2 lens r₁ r₂


/-- `(Lens.bijection e).liftSubProbability` is surjective (the `e.symm`-pushforward is a right inverse). -/
private lemma bijection_updateK_surjective {α β : Type} (e : α ≃ β) :
    Function.Surjective (Lens.bijection e).liftSubProbability := by
  intro k'
  refine ⟨fun st => k' (e st) >>= fun p => pure (e.symm p), ?_⟩
  funext st
  simp only [Lens.liftSubProbability, Lens.bijection, SubProbability.bind_assoc, SubProbability.pure_bind,
    Equiv.apply_symm_apply, SubProbability.bind_pure]


/-- **`Lens.liftProbLensRange` along a bijection sub-distributes over joins** (the `≤` direction). For a
bijection lens the pushforward `updateK` is an injective monoid hom, so `image_cc_subset`
applies. -/
private lemma fvP_extend_bijection_sup_le {α β : Type} [Nonempty β] (e : α ≃ β)
    (r₁ r₂ : ProbLensRange α) :
    Lens.liftProbLensRange (Lens.bijection e) (r₁ ⊔ r₂)
      ≤ Lens.liftProbLensRange (Lens.bijection e) r₁ ⊔ Lens.liftProbLensRange (Lens.bijection e) r₂ := by
  unfold Lens.liftProbLensRange
  rw [probLensRange_from_union, ← Set.image_union, probLensRange_sup_updates,
      ProbLensRange.from_le_iff, ProbLensRange.from_updates]
  exact image_cc_subset (Lens.bijection e).liftSubProbability (updateK_mul (Lens.bijection e))
    (bijection_updateK_surjective e) (updateK_injective (Lens.bijection e)) (r₁.updates ∪ r₂.updates)


/-! # End of fvP_reduce_sup -/

namespace FVP

variable [ProgramSpec]

/-- Family version of `Program.probRange`: the supremum of the per-input ranges. Used to
give a setter (which is a *family* `a → Program s Unit`, one program per written value) a
single footprint. -/
noncomputable def _root_.GaudisCrypt.Language.Semantics.Program.probRange'
    {s a b : Type} (progs : a → Program s b) : ProbLensRange s :=
  ⨆ x, (progs x).probRange

noncomputable
-- TODO: Inline
def fvP_getter (getter : Getter a s) : ProbLensRange s := Program.probRange (Program.get getter)

noncomputable
-- TODO: Inline
def fvP_setter (setter : Setter a s) : ProbLensRange s := Program.probRange' (Program.set setter)

noncomputable
-- TODO rename to something Lens-related
def fvP_reduce_new {a b : Type} (lens : Lens a b) (range : ProbLensRange b) :
    ProbLensRange a :=
  -- transport `range` along `lens.splitSpace : b ≃ a × lens.ComplContent` (via the bijection lens),
  -- then reduce away the complement component with `fvP_reduce`.
  fvP_reduce Lens.fst (Lens.liftProbLensRange (Lens.bijection (Lens.splitSpace lens)) range)



/-! ### Properties of `fvP_reduce` / `Lens.liftProbLensRange` needed for the framework instance.

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
    (so the `diracKer` generators of `lens.probRange` all sit inside the localized-kernel image). -/
private lemma updateK_diracKer {a s : Type} (lens : Lens a s) (g : Function.End a) :
    lens.liftSubProbability (diracKer g) = diracKer (lens.liftFunction g) := by
  funext st
  show (pure (g (lens.get st)) : SubProbability a) >>= (fun a' => pure (lens.set a' st))
     = pure (lens.set (g (lens.get st)) st)
  rw [SubProbability.pure_bind]

omit [ProgramSpec] in
/-- **The cheap half of the lens-corner double-commutant theorem.** The bicommutant closure of the
    full set of `lens`-localized kernels is exactly `lens.probRange`: the `diracKer` generators of
    `lens.probRange` lie inside the localized image (`updateK_diracKer`), and every localized kernel
    lies in `lens.probRange` (`Mlocalized_in_probRange`), so both sides share a bicommutant closure.

    This is scaffolding toward closing `fvP_reduce_sup` / `fvP_extend_sup`.  The genuinely hard,
    still-open part is that this image is *already* closed — i.e.
    `lens.probRange.updates ⊆ lens.liftSubProbability '' univ` (every range element is a localized kernel) plus
    injectivity of `updateK` — which together would give the lens-corner tensor/commutant
    factorization the two `_sup` reverse directions need. -/
theorem updateK_image_univ_cc {a s : Type} (lens : Lens a s) :
    Set.centralizer (Set.centralizer (lens.liftSubProbability '' (Set.univ : Set (a → SubProbability a))))
      = lens.probRange.updates := by
  have hI : lens.liftSubProbability '' (Set.univ : Set (a → SubProbability a)) ⊆ lens.probRange.updates := by
    rintro _ ⟨ρ, _, rfl⟩
    exact Mlocalized_in_probRange lens ρ
  have hD : (Set.range fun g : Function.End a => diracKer (lens.liftFunction g))
      ⊆ lens.liftSubProbability '' (Set.univ : Set (a → SubProbability a)) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨diracKer g, Set.mem_univ _, updateK_diracKer lens g⟩
  have hprD : lens.probRange.updates
      = Set.centralizer (Set.centralizer
          (Set.range fun g : Function.End a => diracKer (lens.liftFunction g))) :=
    ProbLensRange.from_updates _
  apply Set.Subset.antisymm
  · calc Set.centralizer (Set.centralizer (lens.liftSubProbability '' (Set.univ : Set (a → SubProbability a))))
        ⊆ Set.centralizer (Set.centralizer lens.probRange.updates) := cl_mono hI
      _ = lens.probRange.updates := probLensRange_updates_cc lens.probRange
  · rw [hprD]
    exact cl_mono hD

omit [ProgramSpec] in
/-- `fvP_reduce` is monotone in its range argument (double-antitone via the two centralizers). -/
private lemma fvP_reduce_mono {a b} (lens : Lens a b) {r r' : ProbLensRange b} (h : r ≤ r') :
    fvP_reduce lens r ≤ fvP_reduce lens r' := by
  have hsub : r.updates ⊆ r'.updates := h
  unfold fvP_reduce
  apply ProbLensRange.from_mono
  gcongr

/-! ### Extraction: `lens.probRange` is exactly the localized kernels.

The bicommutant closure of the lens-image does *not* enlarge it — `fvP_extend_updates` is a genuine
equality. The two ingredients (per the proof sketch): every kernel in `lens.probRange` is `lens.liftSubProbability`
of some base kernel (`probRange_updateK_image`), and `lens.liftSubProbability` is injective (so commutation
transfers through it). -/



omit [ProgramSpec] in
/-- A kernel in `lens.probRange` is **equivariant under complement updates**: it commutes with every
    Dirac complement-update (`diracKer (lens.compl.update h) ∈ lens.probRangeᶜ`), so it intertwines
    `lens.compl.update h`. -/
private lemma probRange_equivariant {a s : Type} (lens : Lens a s)
    {p : s → SubProbability s} (hp : p ∈ lens.probRange.updates)
    (h : Function.End lens.ComplContent) (st : s) :
    p (lens.compl.liftFunction h st) = (p st >>= fun st' => pure (lens.compl.liftFunction h st')) := by
  haveI : disjoint lens.compl lens := ⟨fun st v w => by
    induction v using Quotient.inductionOn
    rename_i u
    show lens.set (lens.get (lens.set w st)) u = lens.set w (lens.set (lens.get st) u)
    rw [lens.set_get, lens.set_set]⟩
  have hsub : lens.compl.probRange.updates ⊆ (lens.probRange)ᶜ.updates :=
    Lens.probRange_le_compl_of_disjoint lens.compl lens
  have hk : diracKer (lens.compl.liftFunction h) ∈ (lens.probRange)ᶜ.updates :=
    hsub ((ProbLensRange.from_le_iff _ lens.compl.probRange).mp le_rfl ⟨h, rfl⟩)
  rw [ProbLensRange.updates_eq_centralizer_compl lens.probRange] at hp
  have hcomm := Submonoid.mem_centralizer_iff.mp hp (diracKer (lens.compl.liftFunction h)) hk
  have hst := congrFun hcomm st
  simp only [kmul_apply] at hst
  rw [show (diracKer (lens.compl.liftFunction h) st) = pure (lens.compl.liftFunction h st) from rfl,
      SubProbability.pure_bind] at hst
  exact hst.symm

/-- **Extraction**: every kernel in `lens.probRange` is `lens.liftSubProbability` of a base kernel. The witness
    reads the base at a fixed `st₀`; equivariance + the `Lens.compl.set ⟦st⟧ st' = lens.set (lens.get st') st`
    identity make `lens.liftSubProbability (read-back) = p`. -/
private lemma probRange_updateK_image {a s : Type} (lens : Lens a s) (st₀ : s)
    {p : s → SubProbability s} (hp : p ∈ lens.probRange.updates) :
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
  have heq := probRange_equivariant lens hp (Function.const _ (lens.compl.get st))
    (lens.set (lens.get st) st₀)
  rw [hrecon] at heq
  rw [heq]
  congr 1

/-- **`Lens.liftProbLensRange` is exactly the lens-image of the footprint** (`[Nonempty b]`). The `⊇` half is the
    generic `X ⊆ CC X`; the `⊆` half is the proof sketch: `Lens.liftProbLensRange` lands in `lens.probRange`, every
    such element extracts as `lens.liftSubProbability q`, and (`updateK` being an injective hom) `q` inherits the
    commutation defining `range.updates`. Correcting the deterministic original's *false* conjecture —
    over a lens corner the bicommutant closure does **not** enlarge the image. -/
theorem fvP_extend_updates {a b} [Nonempty b] (lens : Lens a b) (range : ProbLensRange a) :
    (Lens.liftProbLensRange lens range).updates = lens.liftSubProbability '' range.updates := by
  apply Set.Subset.antisymm
  · intro p hp
    have hp_lens : p ∈ lens.probRange.updates := by
      have h1 : (Lens.liftProbLensRange lens range).updates ⊆ lens.probRange.updates := by
        rw [← updateK_image_univ_cc lens]
        unfold Lens.liftProbLensRange
        rw [ProbLensRange.from_updates]
        exact cl_mono (Set.image_mono (Set.subset_univ _))
      exact h1 hp
    have hpC : p ∈ Set.centralizer (Set.centralizer (lens.liftSubProbability '' range.updates)) := by
      have hfe : (Lens.liftProbLensRange lens range).updates
          = Set.centralizer (Set.centralizer (lens.liftSubProbability '' range.updates)) := by
        unfold Lens.liftProbLensRange; exact ProbLensRange.from_updates _
      rwa [hfe] at hp
    obtain ⟨q, hq⟩ : ∃ q, lens.liftSubProbability q = p :=
      ⟨_, probRange_updateK_image lens (Classical.arbitrary b) hp_lens⟩
    refine ⟨q, ?_, hq⟩
    rw [← probLensRange_updates_cc range, Set.mem_centralizer_iff]
    intro r hr
    have hur : lens.liftSubProbability r ∈ Set.centralizer (lens.liftSubProbability '' range.updates) := by
      rw [Set.mem_centralizer_iff]
      rintro _ ⟨t, ht, rfl⟩
      rw [← updateK_mul, ← updateK_mul, (Set.mem_centralizer_iff.mp hr) t ht]
    have hcomm := (Set.mem_centralizer_iff.mp hpC) (lens.liftSubProbability r) hur
    rw [← hq, ← updateK_mul, ← updateK_mul] at hcomm
    exact updateK_injective lens hcomm
  · unfold Lens.liftProbLensRange
    rw [ProbLensRange.from_updates]
    exact Set.subset_centralizer_centralizer

omit [ProgramSpec] in
/-- **`fvP_reduce` is a retraction of `Lens.liftProbLensRange`** (`reduce (extend r) ≤ r`):
    pushing a footprint forward along a lens and pulling it back recovers at most it.
    Proven in full from `updateK` being a monoid homomorphism
    (`centralizer_preimage_image_subset`). -/
theorem fvP_reduce_extend {a b} (lens : Lens a b) (r : ProbLensRange a) :
    fvP_reduce lens (Lens.liftProbLensRange lens r) ≤ r := by
  rw [← fvP_reduce'_eq]
  unfold fvP_reduce'
  rw [ProbLensRange.from_le_iff, fvP_reduce_constraint]
  have hext : Set.centralizer (Lens.liftProbLensRange lens r).updates
            = Set.centralizer (lens.liftSubProbability '' r.updates) := by
    unfold Lens.liftProbLensRange
    rw [ProbLensRange.from_updates, Set.centralizer_centralizer_centralizer]
  rw [hext]
  have key := centralizer_preimage_image_subset lens.liftSubProbability (updateK_mul lens) r.updates
  rw [probLensRange_updates_cc] at key
  exact key

noncomputable
def fvpInductiveFunctionGS : InductiveFunctionGettersSetters ProbLensRange where
  nothing := ⊥
  join := (· ⊔ ·)
  getter g := Program.probRange (Program.get g)
  setter s := Program.probRange' (Program.set s)
  reduce := fvP_reduce
  extend := Lens.liftProbLensRange

noncomputable
def fvPMexpr {ctx t} (m : ModuleExpression ctx t) : (ProbLensRange State) :=
  fvpInductiveFunctionGS.evalMexpr m

noncomputable
def fvP (m : Module t) : ProbLensRange State := fvpInductiveFunctionGS.eval m

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
    exact sup_le (Lens.liftProbLensRange_mono lens le_sup_left) (Lens.liftProbLensRange_mono lens le_sup_right)
  extend_reduce := by
    intro a b lens r
    exact fvP_reduce_extend lens r
  reduce_mono := fun lens h => fvP_reduce_mono lens h
  extend_mono := fun lens h => Lens.liftProbLensRange_mono lens h


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
def fvP_proc {sig holes} (proc : ProcedureWithHoles holes sig) : ProbLensRange State :=
  fvpInductiveFunctionGS.proc proc

noncomputable
def fvP_stmt {s holes} (stmt : StmtWithHoles holes s) : ProbLensRange (ProcedureState s) :=
  fvpInductiveFunctionGS.stmt stmt

end FVP
