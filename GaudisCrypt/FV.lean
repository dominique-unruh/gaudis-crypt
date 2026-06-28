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

namespace GaudisCrypt.Language.Lens

/-- **Kernel-level lens update.** Localize a sub-probability kernel `κ` on the focus `a`
to a kernel on the whole state `b`: read the focus with `lens.get`, run `κ` there, and
write the result back with `lens.set`. This is the Kleisli analogue of `Lens.update`
(`Function.End a → Function.End b`); on Dirac kernels it agrees with `diracKer ∘ lens.update`. -/
noncomputable def Lens.updateK {a b : Type} (lens : Lens a b)
    (κ : a → SubProbability a) : b → SubProbability b :=
  fun st => κ (lens.get st) >>= fun a' => pure (lens.set a' st)

end GaudisCrypt.Language.Lens

namespace FVP

variable [ProgramSpec]

/-- The footprint type: a `ProbLensRange` over the full program `State`. -/
abbrev FVP := ProbLensRange State

/-- Family version of `Program.probRange`: the supremum of the per-input ranges. Used to
give a setter (which is a *family* `a → Program s Unit`, one program per written value) a
single footprint. -/
noncomputable def _root_.GaudisCrypt.Language.Semantics.Program.probRange'
    {s a b : Type} (progs : a → Program s b) : ProbLensRange s :=
  ⨆ x, (progs x).probRange

noncomputable
def fvP_getter (getter : Getter a s) : ProbLensRange s := Program.probRange (Program.get getter)

noncomputable
def fvP_setter (setter : Setter a s) : ProbLensRange s := Program.probRange' (Program.set setter)

noncomputable
def fvP_reduce_base {a b} (range : ProbLensRange (a × b)) : ProbLensRange a :=
  ProbLensRange.from
  ((fun ((f : a × b → SubProbability (a × b)),
         (i : Unit -> SubProbability b),
         (o : b -> SubProbability Unit)) =>
    fun m => do let m' <- i (); let (m, m') <- f (m, m'); let _ <- o m'; return m)
   '' (range.updates ×ˢ Set.univ ×ˢ Set.univ))

omit [ProgramSpec] in
/-- `fvP_reduce_base` is monotone: a larger range gives a larger reduced range. -/
theorem fvP_reduce_base_mono {a b} {r r' : ProbLensRange (a × b)} (h : r ≤ r') :
    fvP_reduce_base r ≤ fvP_reduce_base r' := by
  have hsub : r.updates ⊆ r'.updates := h
  unfold fvP_reduce_base
  rw [ProbLensRange.from_le_iff]
  refine Set.Subset.trans ?_ ((ProbLensRange.from_le_iff _ _).mp le_rfl)
  gcongr

omit [ProgramSpec] in
theorem fvP_reduce_sup1 {a b} (r₁ r₂ : ProbLensRange (a × b)) :
    fvP_reduce_base (r₁ ⊔ r₂) ≥ fvP_reduce_base r₁ ⊔ fvP_reduce_base r₂ :=
  sup_le (fvP_reduce_base_mono le_sup_left) (fvP_reduce_base_mono le_sup_right)



/-- The generator transform underlying `fvP_reduce_base`: given a joint kernel `f` on `a × b`,
an input distribution `i` on `b`, and a weighting `o` on the `b`-output, produce the `a`-kernel
that feeds `i`, runs `f`, and weights/discards the `b`-component via `o`. Named so the
`fvP_reduce_sup` reasoning can manipulate the generator set without the inline lambda. -/
noncomputable def reduceBaseGen {a b : Type}
    (p : (a × b → SubProbability (a × b)) × (Unit → SubProbability b) × (b → SubProbability Unit)) :
    a → SubProbability a :=
  fun m => do let m' ← p.2.1 (); let (m, m') ← p.1 (m, m'); let _ ← p.2.2 m'; pure m

omit [ProgramSpec] in
/-- `fvP_reduce_base` as `ProbLensRange.from` of the named generator set. -/
theorem fvP_reduce_base_eq_from {a b : Type} (range : ProbLensRange (a × b)) :
    fvP_reduce_base range
      = ProbLensRange.from (reduceBaseGen '' (range.updates ×ˢ Set.univ ×ˢ Set.univ)) := rfl

/-- The `h ⊗ id_b` lift of an `a`-kernel to an `a × b`-kernel: act by `h` on the `a` component,
leave the `b` component untouched. -/
noncomputable def liftA {a b : Type} (h : a → SubProbability a) : a × b → SubProbability (a × b) :=
  fun mb => h mb.1 >>= fun a'' => pure (a'', mb.2)

omit [ProgramSpec] in
/-- `reduceBaseGen` in clean (bind, projection) form on an explicit triple. -/
theorem reduceBaseGen_apply {a b : Type}
    (f : a × b → SubProbability (a × b)) (i : Unit → SubProbability b) (o : b → SubProbability Unit)
    (m : a) :
    reduceBaseGen (f, i, o) m
      = i () >>= fun m' => f (m, m') >>= fun x => o x.2 >>= fun _ => pure x.1 := rfl

omit [ProgramSpec] in
/-- Kleisli product of `a × b`-kernels in bind form. -/
theorem kmul_prod_apply {a b : Type} (F G : a × b → SubProbability (a × b)) (x : a × b) :
    (F * G) x = G x >>= F := rfl

omit [ProgramSpec] in
/-- `liftA h` post-composed simplifies the write-back away. -/
theorem liftA_mul_apply {a b : Type} (f : a × b → SubProbability (a × b)) (h : a → SubProbability a)
    (m : a) (m' : b) :
    (f * (liftA h : a × b → SubProbability (a × b))) (m, m') = h m >>= fun a'' => f (a'', m') := by
  simp only [kmul_prod_apply, liftA, SubProbability.bind_assoc, SubProbability.pure_bind]

omit [ProgramSpec] in
/-- `liftA h` pre-composed pushes `h` through the `a`-output. -/
theorem mul_liftA_apply {a b : Type} (g : a × b → SubProbability (a × b)) (h : a → SubProbability a)
    (m : a) (m' : b) :
    ((liftA h : a × b → SubProbability (a × b)) * g) (m, m')
      = g (m, m') >>= fun x => h x.1 >>= fun a'' => pure (a'', x.2) := by
  rw [kmul_prod_apply]; rfl

omit [ProgramSpec] in
/-- **Right Fubini identity.** Post-composing a reduced generator with `h` equals reducing the
joint kernel post-composed with the lift `ĥ = liftA h`. Pure Kleisli algebra + one `bind_swap`. -/
theorem reduceBaseGen_mul_right {a b : Type}
    (f : a × b → SubProbability (a × b)) (i : Unit → SubProbability b) (o : b → SubProbability Unit)
    (h : a → SubProbability a) :
    reduceBaseGen (f, i, o) * h = reduceBaseGen (f * liftA h, i, o) := by
  funext m
  have lhs : (reduceBaseGen (f, i, o) * h) m
      = h m >>= fun a'' => i () >>= fun m' =>
          f (a'', m') >>= fun x => o x.2 >>= fun _ => pure x.1 := rfl
  have rhs : reduceBaseGen (f * liftA h, i, o) m
      = i () >>= fun m' => h m >>= fun a'' =>
          f (a'', m') >>= fun x => o x.2 >>= fun _ => pure x.1 := by
    rw [reduceBaseGen_apply]
    congr 1; funext m'
    rw [liftA_mul_apply, SubProbability.bind_assoc]
  rw [lhs, rhs]
  exact bind_swap (h m) (i ()) (fun m' a'' => f (a'', m') >>= fun x => o x.2 >>= fun _ => pure x.1)

omit [ProgramSpec] in
/-- **Left Fubini identity.** Pre-composing a reduced generator with `h` equals reducing the joint
kernel pre-composed with the lift `ĥ = liftA h`. Needs two `bind_swap`s (one to push `h` past the
input integral, one to commute the `o`-weight past `h`). -/
theorem reduceBaseGen_mul_left {a b : Type}
    (f : a × b → SubProbability (a × b)) (i : Unit → SubProbability b) (o : b → SubProbability Unit)
    (h : a → SubProbability a) :
    h * reduceBaseGen (f, i, o)
      = reduceBaseGen ((liftA h : a × b → SubProbability (a × b)) * f, i, o) := by
  funext m
  have lhs : (h * reduceBaseGen (f, i, o)) m
      = i () >>= fun m' => f (m, m') >>= fun x => o x.2 >>= fun _ => h x.1 := by
    change reduceBaseGen (f, i, o) m >>= h = _
    rw [reduceBaseGen_apply, SubProbability.bind_assoc]
    congr 1; funext m'
    rw [SubProbability.bind_assoc]
    congr 1; funext x
    rw [SubProbability.bind_assoc]
    congr 1; funext _
    rw [SubProbability.pure_bind]
  have rhs : reduceBaseGen ((liftA h : a × b → SubProbability (a × b)) * f, i, o) m
      = i () >>= fun m' => f (m, m') >>= fun x =>
          h x.1 >>= fun a'' => o x.2 >>= fun _ => pure a'' := by
    rw [reduceBaseGen_apply]
    congr 1; funext m'
    rw [mul_liftA_apply, SubProbability.bind_assoc]
    congr 1; funext x
    rw [SubProbability.bind_assoc]
    congr 1; funext a''
    rw [SubProbability.pure_bind]
  have inner : ∀ x : a × b,
      o x.2 >>= (fun _ => h x.1) = h x.1 >>= fun a'' => o x.2 >>= fun _ => pure a'' := by
    intro x
    conv_lhs => rw [← SubProbability.bind_pure (h x.1)]
    exact bind_swap (o x.2) (h x.1) (fun a'' _ => pure a'')
  rw [lhs, rhs]
  congr 1; funext m'
  congr 1; funext x
  exact inner x

open Classical MeasureTheory in
omit [ProgramSpec] in
/-- **Slice determination.** A joint kernel `K : a × b → SubProbability (a × b)` is determined by
all its reduced generators: feeding a point input `i = δ_β` and an indicator weight `o = [·=γ]`
recovers `K(m, β)` restricted to `b`-output `γ`, projected to `a`. Ranging over all `(β, γ)` pins
down `K` on every input/output point. This is the one genuinely measure-theoretic ingredient
(`discreteMeasure.ext` on singletons), the second-coordinate analogue of `ProbLensRange`'s
`ext_of_slices`. -/
theorem reduceBaseExt {a b : Type} (K L : a × b → SubProbability (a × b))
    (hKL : ∀ i o, reduceBaseGen (K, i, o) = reduceBaseGen (L, i, o)) : K = L := by
  -- A point input + indicator weight turns `reduceBaseGen` into a coordinate slice.
  have reduceEq : ∀ (M : a × b → SubProbability (a × b)) (m : a) (β γ : b),
      reduceBaseGen (M, (fun _ => pure β), (fun c => if c = γ then pure () else ⊥)) m
        = M (m, β) >>= fun x => if x.2 = γ then (pure x.1 : SubProbability a) else ⊥ := by
    intro M m β γ
    rw [reduceBaseGen_apply, SubProbability.pure_bind]
    congr 1; funext x
    by_cases hx : x.2 = γ
    · rw [if_pos hx, if_pos hx, SubProbability.pure_bind]
    · rw [if_neg hx, if_neg hx, SubProbability.bot_bind]
  -- The slice's mass is the joint kernel's mass on the `{γ}`-fibre rectangle.
  have slice_apply2 : ∀ (μ : SubProbability (a × b)) (γ : b) (B : Set a),
      (μ >>= fun x => if x.2 = γ then (pure x.1 : SubProbability a) else ⊥).1 B
        = μ.1 (B ×ˢ {γ}) := by
    intro μ γ B
    letI : MeasurableSpace (a × b) := ⊤
    letI : MeasurableSpace a := ⊤
    change (Measure.bind μ.1 (fun x => (if x.2 = γ then (pure x.1 : SubProbability a) else ⊥).1)) B
        = μ.1 (B ×ˢ {γ})
    rw [Measure.bind_apply (by trivial) (measurable_from_top.aemeasurable)]
    rw [show (fun x : a × b => (if x.2 = γ then (pure x.1 : SubProbability a) else ⊥).1 B)
          = Set.indicator (B ×ˢ {γ}) 1 from ?_]
    · rw [lintegral_indicator_one (by trivial)]
    · funext x
      by_cases hx : x.2 = γ
      · rw [if_pos hx]
        change (@MeasureTheory.Measure.dirac a ⊤ x.1) B = Set.indicator (B ×ˢ {γ}) 1 x
        rw [MeasureTheory.Measure.dirac_apply' x.1 (by trivial)]
        simp only [Set.indicator, Set.mem_prod, Set.mem_singleton_iff, hx, and_true, Pi.one_apply]
      · rw [if_neg hx]
        rw [show ((⊥ : SubProbability a).1 : Measure a) = 0 from rfl]
        simp only [Measure.coe_zero, Pi.zero_apply, Set.indicator, Set.mem_prod,
          Set.mem_singleton_iff, hx, and_false, if_false]
  funext mb
  obtain ⟨m, β⟩ := mb
  apply Subtype.ext
  refine discreteMeasure.ext (K (m, β)).2.2 (L (m, β)).2.2 (fun z => ?_)
  obtain ⟨a', γ⟩ := z
  have key : ∀ ρ : SubProbability (a × b),
      ρ.1 {((a', γ) : a × b)}
        = (ρ >>= fun x => if x.2 = γ then (pure x.1 : SubProbability a) else ⊥).1 {a'} := by
    intro ρ
    rw [slice_apply2 ρ γ {a'},
      show (({a'} : Set a) ×ˢ ({γ} : Set b)) = {((a', γ) : a × b)} from by
        ext w; simp [Prod.ext_iff]]
  rw [key (K (m, β)), key (L (m, β))]
  have hcomm := congrFun (hKL (fun _ => pure β) (fun c => if c = γ then pure () else ⊥)) m
  rw [reduceEq K m β γ, reduceEq L m β γ] at hcomm
  rw [hcomm]

omit [ProgramSpec] in
/-- **The crux of `fvP_reduce_sup2`.** Every generator of the reduced join lies in the bicommutant
closure of the union of the two reduced generator sets — the double-commutant direction.

The proof needs **no disintegration**: with `ĥ = liftA h` the `h ⊗ id_b` lift, the two Fubini
identities (`reduceBaseGen_mul_left`/`_right`) turn `h`-commutation of reduced generators into
`ĥ`-commutation of the joint kernels. Slice determination (`reduceBaseExt`) lifts any
`h ∈ commutant(gen r₁ ∪ gen r₂)` to `ĥ ∈ commutant(r₁.updates ∪ r₂.updates)`; then `f` in the
bicommutant commutes with `ĥ`, and the identities push that back down to `h`. -/
theorem reduceBaseGen_sup_subset {a b : Type} (r₁ r₂ : ProbLensRange (a × b)) :
    reduceBaseGen '' ((r₁ ⊔ r₂).updates ×ˢ Set.univ ×ˢ Set.univ)
      ⊆ Set.centralizer (Set.centralizer
          ((reduceBaseGen '' (r₁.updates ×ˢ Set.univ ×ˢ Set.univ))
            ∪ (reduceBaseGen '' (r₂.updates ×ˢ Set.univ ×ˢ Set.univ)))) := by
  have hcc : ∀ (S : Set (a × b → SubProbability (a × b))),
      (Submonoid.centralizer S).carrier = Set.centralizer S := fun S => by
    ext x; simp [Submonoid.mem_centralizer_iff, Set.mem_centralizer_iff]
  rintro _ ⟨⟨f, i, o⟩, ⟨hf, -, -⟩, rfl⟩
  rw [Set.mem_centralizer_iff]
  intro h hh
  -- The `h ⊗ id_b` lift commutes with `r₁.updates ∪ r₂.updates`.
  have hĥ : (liftA h : a × b → SubProbability (a × b))
      ∈ Set.centralizer (r₁.updates ∪ r₂.updates) := by
    rw [Set.mem_centralizer_iff]
    intro g hg
    apply reduceBaseExt
    intro i' o'
    rw [← reduceBaseGen_mul_right, ← reduceBaseGen_mul_left]
    have hmem : reduceBaseGen (g, i', o')
        ∈ (reduceBaseGen '' (r₁.updates ×ˢ Set.univ ×ˢ Set.univ))
          ∪ (reduceBaseGen '' (r₂.updates ×ˢ Set.univ ×ˢ Set.univ)) := by
      cases hg with
      | inl hg1 => exact Or.inl ⟨(g, i', o'), ⟨hg1, Set.mem_univ _, Set.mem_univ _⟩, rfl⟩
      | inr hg2 => exact Or.inr ⟨(g, i', o'), ⟨hg2, Set.mem_univ _, Set.mem_univ _⟩, rfl⟩
    exact (Set.mem_centralizer_iff.mp hh) (reduceBaseGen (g, i', o')) hmem
  -- `f` is in the bicommutant of the union, so it commutes with the lift.
  have hsup : (r₁ ⊔ r₂).updates = Set.centralizer (Set.centralizer (r₁.updates ∪ r₂.updates)) := by
    change (Submonoid.centralizer
      (Submonoid.centralizer (r₁.updates ∪ r₂.updates)).carrier).carrier = _
    rw [hcc, hcc]
  have hfĥ : (liftA h : a × b → SubProbability (a × b)) * f = f * liftA h := by
    rw [hsup] at hf
    exact (Set.mem_centralizer_iff.mp hf) (liftA h) hĥ
  rw [reduceBaseGen_mul_left, reduceBaseGen_mul_right, hfĥ]

omit [ProgramSpec] in
theorem fvP_reduce_sup2 {a b} (r₁ r₂ : ProbLensRange (a × b)) :
    fvP_reduce_base (r₁ ⊔ r₂) ≤ fvP_reduce_base r₁ ⊔ fvP_reduce_base r₂ := by
  rw [fvP_reduce_base_eq_from, fvP_reduce_base_eq_from, fvP_reduce_base_eq_from,
    ProbLensRange.from_le_iff]
  set Z := ProbLensRange.from (reduceBaseGen '' (r₁.updates ×ˢ Set.univ ×ˢ Set.univ))
      ⊔ ProbLensRange.from (reduceBaseGen '' (r₂.updates ×ˢ Set.univ ×ˢ Set.univ)) with hZ
  have h1 : reduceBaseGen '' (r₁.updates ×ˢ Set.univ ×ˢ Set.univ) ⊆ Z.updates :=
    (ProbLensRange.from_le_iff _ _).mp le_sup_left
  have h2 : reduceBaseGen '' (r₂.updates ×ˢ Set.univ ×ˢ Set.univ) ⊆ Z.updates :=
    (ProbLensRange.from_le_iff _ _).mp le_sup_right
  have hcc : ∀ (S : Set (a → SubProbability a)),
      (Submonoid.centralizer S).carrier = Set.centralizer S := fun S => by
    ext x; simp [Submonoid.mem_centralizer_iff, Set.mem_centralizer_iff]
  have hclosed : Set.centralizer (Set.centralizer Z.updates) = Z.updates := by
    have h := Z.double_commutant
    rw [hcc, hcc] at h
    exact h
  refine (reduceBaseGen_sup_subset r₁ r₂).trans ?_
  rw [← hclosed]
  exact Set.centralizer_subset (Set.centralizer_subset (Set.union_subset h1 h2))


noncomputable
def fvP_reduce_base' {a b : Type} (range : ProbLensRange (a × b)) : ProbLensRange a :=
  ProbLensRange.from
    { f | ∀ g ∈ range.updates,
        (liftA f : a × b → SubProbability (a × b)) * g = g * liftA f }.centralizer


noncomputable
def fvP_reduce {a b} (lens : Lens a b) (range : ProbLensRange b) : ProbLensRange a :=
  ProbLensRange.from { f | ∀ g ∈ range.updates, lens.updateK f * g = g * lens.updateK f}.centralizer

noncomputable
def fvP_extend {a b} (lens : Lens a b) (range : ProbLensRange a) : ProbLensRange b :=
  ProbLensRange.from (lens.updateK '' range.updates)


/-! ### Properties of `fvP_reduce` / `fvP_extend` needed for the framework instance.

These mirror the deterministic `FV` development.  The three obligations consumed by the
`ReducibleGettersSetters` instance (`fvP_reduce_sup`, `fvP_extend_sup`, `fvP_reduce_extend`),
together with `fvP_extend_updates`, were left as `sorry` in the deterministic original and
remain so here — they are nontrivial facts about the bicommutant closure of a lens-localized
kernel set.  Note: the soundness proof `fvPMexpr_upper_bound` uses `fvP_getter`/`fvP_setter`
only *opaquely*, so no properties of those are needed. -/

section FvReduceSup
omit [ProgramSpec]

/-- Two `ProbLensRange`s with the same `updates` are equal. -/
private lemma probLensRange_eq_of_updates {m} {x y : ProbLensRange m} (h : x.updates = y.updates) :
    x = y := by
  obtain ⟨_, _, _, _⟩ := x
  obtain ⟨_, _, _, _⟩ := y
  simp only at h
  subst h
  rfl

/-- `ProbLensRange.from G` has the double-centralizer of `G` as its `updates`. -/
private lemma probLensRange_from_updates {m} (G : Set (m → SubProbability m)) :
    (ProbLensRange.from G).updates = Set.centralizer (Set.centralizer G) := by
  change (Submonoid.centralizer ((Submonoid.centralizer G).carrier) : Set (m → SubProbability m))
      = Set.centralizer (Set.centralizer G)
  rw [Submonoid.coe_centralizer]
  rfl

/-- The `updates` of a join is the double centralizer of the union of the `updates`. -/
private lemma probLensRange_sup_updates {m} (x y : ProbLensRange m) :
    (x ⊔ y).updates = Set.centralizer (Set.centralizer (x.updates ∪ y.updates)) := by
  change (ProbLensRange.from (x.updates ∪ y.updates)).updates = _
  exact probLensRange_from_updates _

/-- Bicommutant closure `cⁿ²` is monotone. -/
private lemma cl_mono {m} {A B : Set (m → SubProbability m)} (h : A ⊆ B) :
    Set.centralizer (Set.centralizer A) ⊆ Set.centralizer (Set.centralizer B) :=
  Set.centralizer_subset (Set.centralizer_subset h)

/-- `ProbLensRange.from` turns unions into joins. -/
private lemma probLensRange_from_union {m} (A B : Set (m → SubProbability m)) :
    ProbLensRange.from A ⊔ ProbLensRange.from B = ProbLensRange.from (A ∪ B) := by
  apply probLensRange_eq_of_updates
  rw [probLensRange_sup_updates, probLensRange_from_updates, probLensRange_from_updates,
      probLensRange_from_updates]
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

/-- The `fvP_reduce` constraint set is `lens.updateK ⁻¹'` of a centralizer. -/
private lemma fvP_reduce_constraint {a b} (lens : Lens a b) (V : Set (b → SubProbability b)) :
    {f : a → SubProbability a | ∀ g ∈ V, lens.updateK f * g = g * lens.updateK f}
      = lens.updateK ⁻¹' (Set.centralizer V) := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_centralizer_iff]
  exact ⟨fun h g hg => (h g hg).symm, fun h g hg => (h g hg).symm⟩

/-! ### `lens.updateK` is a monoid homomorphism, and the resulting closure algebra. -/

private lemma updateK_apply {a b} (lens : Lens a b) (κ : a → SubProbability a) (st : b) :
    lens.updateK κ st = κ (lens.get st) >>= fun a' => pure (lens.set a' st) := rfl

private lemma kmul_apply {m} (f g : m → SubProbability m) (x : m) : (f * g) x = g x >>= f := rfl

/-- **`lens.updateK` preserves the identity kernel.** -/
lemma updateK_one {a b} (lens : Lens a b) :
    lens.updateK (1 : a → SubProbability a) = 1 := by
  funext st
  show (pure (lens.get st) : SubProbability a) >>= (fun a' => pure (lens.set a' st)) = pure st
  rw [SubProbability.pure_bind, lens.get_set]

/-- **`lens.updateK` is multiplicative**, hence a monoid homomorphism on kernels. The lens
    laws (`set_get`, `set_set`) make the two localizations of a Kleisli composition agree. -/
lemma updateK_mul {a b} (lens : Lens a b) (κ₁ κ₂ : a → SubProbability a) :
    lens.updateK (κ₁ * κ₂) = lens.updateK κ₁ * lens.updateK κ₂ := by
  funext st
  simp only [kmul_apply, updateK_apply]
  rw [SubProbability.bind_assoc, SubProbability.bind_assoc]
  congr 1
  funext a'
  rw [SubProbability.pure_bind, updateK_apply, lens.set_get]
  congr 1
  funext a''
  rw [lens.set_set]

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

private lemma submonoid_centralizer_carrier {m} (S : Set (m → SubProbability m)) :
    (Submonoid.centralizer S).carrier = Set.centralizer S := by
  ext x; simp [Submonoid.mem_centralizer_iff, Set.mem_centralizer_iff]

/-- Every `ProbLensRange` is its own bicommutant (the `double_commutant` field, in `Set` form). -/
private lemma probLensRange_updates_cc {m} (r : ProbLensRange m) :
    Set.centralizer (Set.centralizer r.updates) = r.updates := by
  have h := r.double_commutant
  simpa only [submonoid_centralizer_carrier] using h

/-- `ProbLensRange.from` is monotone. -/
private lemma from_mono {m} {G G' : Set (m → SubProbability m)} (h : G ⊆ G') :
    ProbLensRange.from G ≤ ProbLensRange.from G' := by
  rw [ProbLensRange.from_le_iff, probLensRange_from_updates]
  exact h.trans Set.subset_centralizer_centralizer

/-- A `diracKer` of a localized deterministic update is the `updateK` of the base `diracKer`
    (so the `diracKer` generators of `lens.probRange` all sit inside the localized-kernel image). -/
private lemma updateK_diracKer {a s : Type} (lens : Lens a s) (g : Function.End a) :
    lens.updateK (diracKer g) = diracKer (lens.update g) := by
  funext st
  show (pure (g (lens.get st)) : SubProbability a) >>= (fun a' => pure (lens.set a' st))
     = pure (lens.set (g (lens.get st)) st)
  rw [SubProbability.pure_bind]

/-- **The cheap half of the lens-corner double-commutant theorem.** The bicommutant closure of the
    full set of `lens`-localized kernels is exactly `lens.probRange`: the `diracKer` generators of
    `lens.probRange` lie inside the localized image (`updateK_diracKer`), and every localized kernel
    lies in `lens.probRange` (`Mlocalized_in_probRange`), so both sides share a bicommutant closure.

    This is scaffolding toward closing `fvP_reduce_sup` / `fvP_extend_sup`.  The genuinely hard,
    still-open part is that this image is *already* closed — i.e.
    `lens.probRange.updates ⊆ lens.updateK '' univ` (every range element is a localized kernel) plus
    injectivity of `updateK` — which together would give the lens-corner tensor/commutant
    factorization the two `_sup` reverse directions need. -/
theorem updateK_image_univ_cc {a s : Type} (lens : Lens a s) :
    Set.centralizer (Set.centralizer (lens.updateK '' (Set.univ : Set (a → SubProbability a))))
      = lens.probRange.updates := by
  have hI : lens.updateK '' (Set.univ : Set (a → SubProbability a)) ⊆ lens.probRange.updates := by
    rintro _ ⟨ρ, _, rfl⟩
    exact Mlocalized_in_probRange lens ρ
  have hD : (Set.range fun g : Function.End a => diracKer (lens.update g))
      ⊆ lens.updateK '' (Set.univ : Set (a → SubProbability a)) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨diracKer g, Set.mem_univ _, updateK_diracKer lens g⟩
  have hprD : lens.probRange.updates
      = Set.centralizer (Set.centralizer
          (Set.range fun g : Function.End a => diracKer (lens.update g))) :=
    probLensRange_from_updates _
  apply Set.Subset.antisymm
  · calc Set.centralizer (Set.centralizer (lens.updateK '' (Set.univ : Set (a → SubProbability a))))
        ⊆ Set.centralizer (Set.centralizer lens.probRange.updates) := cl_mono hI
      _ = lens.probRange.updates := probLensRange_updates_cc lens.probRange
  · rw [hprD]
    exact cl_mono hD

/-- `fvP_reduce` is monotone in its range argument (double-antitone via the two centralizers). -/
private lemma fvP_reduce_mono {a b} (lens : Lens a b) {r r' : ProbLensRange b} (h : r ≤ r') :
    fvP_reduce lens r ≤ fvP_reduce lens r' := by
  have hsub : r.updates ⊆ r'.updates := h
  unfold fvP_reduce
  apply from_mono
  rw [fvP_reduce_constraint, fvP_reduce_constraint]
  exact Set.centralizer_subset (Set.preimage_mono (Set.centralizer_subset hsub))

/-- `fvP_extend` is monotone in its range argument. -/
private lemma fvP_extend_mono {a b} (lens : Lens a b) {r r' : ProbLensRange a} (h : r ≤ r') :
    fvP_extend lens r ≤ fvP_extend lens r' := by
  have hsub : r.updates ⊆ r'.updates := h
  unfold fvP_extend
  apply from_mono
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, hsub hg, rfl⟩

/-- `fvP_reduce` distributes over joins.

    Status: **true** (computationally verified in the deterministic `Function.End` model — see
    `CounterExamples/ExtendSupProbe`), but the reverse `≤` is open. Only the `≤`-half
    (`reduce r₁ ⊔ reduce r₂ ≤ reduce (r₁ ⊔ r₂)`, monotonicity) is proven here. (Unlike `extend_join`,
    the framework's `reduce_join` still demands the full `=`.) The reverse reduces — via the
    `extend ⊣ pull` adjunction — to the single kernel-monoid double-commutant theorem
    `u '' (CC W) ⊆ CC (u '' W)`. Its converse `CC (u '' W) ⊆ u '' (CC W)` is
    proven (`centralizer_preimage_image_subset`/extraction); this direction is the open structure
    theorem (the probe shows the obstructing "correlating" commutant elements are benign). -/
theorem fvP_reduce_sup {a b} (lens : Lens a b) (r₁ r₂ : ProbLensRange b) :
    fvP_reduce lens (r₁ ⊔ r₂) = fvP_reduce lens r₁ ⊔ fvP_reduce lens r₂ :=
  le_antisymm
    (by sorry)
    (sup_le (fvP_reduce_mono lens le_sup_left) (fvP_reduce_mono lens le_sup_right))

/-- **`fvP_reduce_base'` and `fvP_reduce_base` have the same generator centralizer.** The
centralizer of the reduced-generator image is exactly the lift-commutation constraint defining
`fvP_reduce_base'`: by the Fubini identities, `h` commutes with every `reduceBaseGen (g, i, o)`
(over all `i, o`) iff `liftA h` commutes with `g` (the `⟸` direction is immediate; the `⟹` uses
slice determination `reduceBaseExt`). -/
theorem centralizer_reduceBaseGen_image {a b : Type} (range : ProbLensRange (a × b)) :
    Set.centralizer (reduceBaseGen '' (range.updates ×ˢ Set.univ ×ˢ Set.univ))
      = { f | ∀ g ∈ range.updates,
          (liftA f : a × b → SubProbability (a × b)) * g = g * liftA f } := by
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_centralizer_iff]
  constructor
  · intro hcomm g hg
    apply reduceBaseExt
    intro i o
    rw [← reduceBaseGen_mul_left, ← reduceBaseGen_mul_right]
    exact (hcomm (reduceBaseGen (g, i, o))
      ⟨(g, i, o), ⟨hg, Set.mem_univ _, Set.mem_univ _⟩, rfl⟩).symm
  · intro hcon k hk
    obtain ⟨⟨g, i, o⟩, ⟨hg, -, -⟩, rfl⟩ := hk
    rw [reduceBaseGen_mul_right, reduceBaseGen_mul_left, hcon g hg]

/-- **`fvP_reduce_base'` equals `fvP_reduce_base`.** Both `ProbLensRange`s have `updates` equal to
the centralizer of the lift-commutation constraint set (`centralizer_reduceBaseGen_image` plus the
triple-centralizer collapse), so the restated lift-commutation form is literally the same footprint
as the explicit reduce-transform image. -/
theorem fvP_reduce_base'_eq {a b : Type} (range : ProbLensRange (a × b)) :
    fvP_reduce_base' range = fvP_reduce_base range := by
  apply probLensRange_eq_of_updates
  rw [fvP_reduce_base_eq_from, probLensRange_from_updates, centralizer_reduceBaseGen_image]
  unfold fvP_reduce_base'
  rw [probLensRange_from_updates, Set.centralizer_centralizer_centralizer]

/-- The reverse (`≤`) direction of `fvP_reduce_base'`'s join law — the genuinely hard
double-commutant direction — reduced to the already-proven `fvP_reduce_sup2` via the identification
`fvP_reduce_base' = fvP_reduce_base`. -/
theorem fvP_reduce_base'_sup2 {a b : Type} (r₁ r₂ : ProbLensRange (a × b)) :
    fvP_reduce_base' (r₁ ⊔ r₂) ≤ fvP_reduce_base' r₁ ⊔ fvP_reduce_base' r₂ := by
  rw [fvP_reduce_base'_eq, fvP_reduce_base'_eq, fvP_reduce_base'_eq]
  exact fvP_reduce_sup2 r₁ r₂


end FvReduceSup

/-- **`fvP_extend` distributes over joins** (i.e. `extend` is a join-homomorphism).

    Studied here for the framework's own sake, **not** because anything needs it: since the merge,
    `ReducibleGettersSetters.extend_join` requires only the `≤`-half (`extend r₁ ⊔ extend r₂ ≤
    extend (r₁ ⊔ r₂)`, = monotonicity, `fvP_extend_mono`), which the instance supplies directly.

    Status of the equality: the `≤`-half is proven; the reverse `extend (r₁ ⊔ r₂) ≤ extend r₁ ⊔ extend r₂`
    is **open** — it reduces (via `fvP_extend_updates`) to the kernel-monoid double-commutant theorem
    `u '' (CC Y) = CC (u '' Y)`, whose `CC(u '' Y) ⊆ u '' (CC Y)` half is proven (extraction) and whose
    `u '' (CC Y) ⊆ CC (u '' Y)` half is the `sorry`.  The equality is *true* in the finite deterministic
    model (no counterexample, `CounterExamples/ExtendSupProbe`); a general proof needs measure-theoretic
    disintegration. -/
theorem fvP_extend_sup {a b} (lens : Lens a b) (r₁ r₂ : ProbLensRange a) :
    fvP_extend lens (r₁ ⊔ r₂) = fvP_extend lens r₁ ⊔ fvP_extend lens r₂ :=
  le_antisymm
    (by sorry)
    (sup_le (fvP_extend_mono lens le_sup_left) (fvP_extend_mono lens le_sup_right))

/-! ### Extraction: `lens.probRange` is exactly the localized kernels.

The bicommutant closure of the lens-image does *not* enlarge it — `fvP_extend_updates` is a genuine
equality. The two ingredients (per the proof sketch): every kernel in `lens.probRange` is `lens.updateK`
of some base kernel (`probRange_updateK_image`), and `lens.updateK` is injective (so commutation
transfers through it). -/

/-- **Read-back**: post-composing a localized kernel with `lens.get` recovers the base kernel
    (`lens.set_get` collapses the write, `bind_pure` the trivial bind). -/
private lemma updateK_get_inv {a s : Type} (lens : Lens a s) (κ : a → SubProbability a) (st : s) :
    (lens.updateK κ st >>= fun st' => pure (lens.get st')) = κ (lens.get st) := by
  show (κ (lens.get st) >>= fun a' => pure (lens.set a' st)) >>= (fun st' => pure (lens.get st'))
     = κ (lens.get st)
  rw [SubProbability.bind_assoc]
  rw [show (fun a' => (pure (lens.set a' st) : SubProbability s) >>= fun st' => pure (lens.get st'))
        = (fun a' => (pure a' : SubProbability a)) from by
      funext a'; rw [SubProbability.pure_bind, lens.set_get]]
  exact SubProbability.bind_pure _

/-- **`lens.updateK` is injective** when the state is inhabited (every focus value is some
    `lens.get st`, and read-back recovers the kernel there). -/
private lemma updateK_injective {a s : Type} [Nonempty s] (lens : Lens a s) :
    Function.Injective lens.updateK := by
  intro κ κ' h
  funext v
  have hsub := congrArg
    (fun k : s → SubProbability s => k (lens.set v (Classical.arbitrary s)) >>= fun st' => pure (lens.get st')) h
  simp only [updateK_get_inv, lens.set_get] at hsub
  exact hsub

/-- A kernel in `lens.probRange` is **equivariant under complement updates**: it commutes with every
    Dirac complement-update (`diracKer (lens.compl.update h) ∈ lens.probRangeᶜ`), so it intertwines
    `lens.compl.update h`. -/
private lemma probRange_equivariant {a s : Type} (lens : Lens a s)
    {p : s → SubProbability s} (hp : p ∈ lens.probRange.updates)
    (h : Function.End (Quotient lens.equal_outside_setoid)) (st : s) :
    p (lens.compl.update h st) = (p st >>= fun st' => pure (lens.compl.update h st')) := by
  haveI : disjoint lens.compl lens := ⟨fun st v w => by
    induction v using Quotient.inductionOn
    rename_i u
    show lens.set (lens.get (lens.set w st)) u = lens.set w (lens.set (lens.get st) u)
    rw [lens.set_get, lens.set_set]⟩
  have hsub : lens.compl.probRange.updates ⊆ (lens.probRange)ᶜ.updates :=
    Lens.probRange_le_compl_of_disjoint lens.compl lens
  have hk : diracKer (lens.compl.update h) ∈ (lens.probRange)ᶜ.updates :=
    hsub ((ProbLensRange.from_le_iff _ lens.compl.probRange).mp le_rfl ⟨h, rfl⟩)
  rw [ProbLensRange.updates_eq_centralizer_compl lens.probRange] at hp
  have hcomm := Submonoid.mem_centralizer_iff.mp hp (diracKer (lens.compl.update h)) hk
  have hst := congrFun hcomm st
  simp only [kmul_apply] at hst
  rw [show (diracKer (lens.compl.update h) st) = pure (lens.compl.update h st) from rfl,
      SubProbability.pure_bind] at hst
  exact hst.symm

/-- **Extraction**: every kernel in `lens.probRange` is `lens.updateK` of a base kernel. The witness
    reads the base at a fixed `st₀`; equivariance + the `Lens.compl.set ⟦st⟧ st' = lens.set (lens.get st') st`
    identity make `lens.updateK (read-back) = p`. -/
private lemma probRange_updateK_image {a s : Type} (lens : Lens a s) (st₀ : s)
    {p : s → SubProbability s} (hp : p ∈ lens.probRange.updates) :
    lens.updateK (fun v => p (lens.set v st₀) >>= fun st' => pure (lens.get st')) = p := by
  funext st
  have hLHS :
      lens.updateK (fun v => p (lens.set v st₀) >>= fun st' => pure (lens.get st')) st
      = p (lens.set (lens.get st) st₀) >>= fun st' => pure (lens.set (lens.get st') st) := by
    show ((p (lens.set (lens.get st) st₀) >>= fun st' => pure (lens.get st'))
            >>= fun a' => pure (lens.set a' st))
       = p (lens.set (lens.get st) st₀) >>= fun st' => pure (lens.set (lens.get st') st)
    rw [SubProbability.bind_assoc]
    congr 1; funext st'
    rw [SubProbability.pure_bind]
  rw [hLHS]
  have hrecon : lens.compl.update (Function.const _ (lens.compl.get st))
      (lens.set (lens.get st) st₀) = st := by
    show lens.set (lens.get (lens.set (lens.get st) st₀)) st = st
    rw [lens.set_get]; exact lens.get_set st
  have heq := probRange_equivariant lens hp (Function.const _ (lens.compl.get st))
    (lens.set (lens.get st) st₀)
  rw [hrecon] at heq
  rw [heq]
  congr 1

/-- **`fvP_extend` is exactly the lens-image of the footprint** (`[Nonempty b]`). The `⊇` half is the
    generic `X ⊆ CC X`; the `⊆` half is the proof sketch: `fvP_extend` lands in `lens.probRange`, every
    such element extracts as `lens.updateK q`, and (`updateK` being an injective hom) `q` inherits the
    commutation defining `range.updates`. Correcting the deterministic original's *false* conjecture —
    over a lens corner the bicommutant closure does **not** enlarge the image. -/
theorem fvP_extend_updates {a b} [Nonempty b] (lens : Lens a b) (range : ProbLensRange a) :
    (fvP_extend lens range).updates = lens.updateK '' range.updates := by
  apply Set.Subset.antisymm
  · intro p hp
    have hp_lens : p ∈ lens.probRange.updates := by
      have h1 : (fvP_extend lens range).updates ⊆ lens.probRange.updates := by
        rw [← updateK_image_univ_cc lens]
        unfold fvP_extend
        rw [probLensRange_from_updates]
        exact cl_mono (Set.image_mono (Set.subset_univ _))
      exact h1 hp
    have hpC : p ∈ Set.centralizer (Set.centralizer (lens.updateK '' range.updates)) := by
      have hfe : (fvP_extend lens range).updates
          = Set.centralizer (Set.centralizer (lens.updateK '' range.updates)) := by
        unfold fvP_extend; exact probLensRange_from_updates _
      rwa [hfe] at hp
    obtain ⟨q, hq⟩ : ∃ q, lens.updateK q = p :=
      ⟨_, probRange_updateK_image lens (Classical.arbitrary b) hp_lens⟩
    refine ⟨q, ?_, hq⟩
    rw [← probLensRange_updates_cc range, Set.mem_centralizer_iff]
    intro r hr
    have hur : lens.updateK r ∈ Set.centralizer (lens.updateK '' range.updates) := by
      rw [Set.mem_centralizer_iff]
      rintro _ ⟨t, ht, rfl⟩
      rw [← updateK_mul, ← updateK_mul, (Set.mem_centralizer_iff.mp hr) t ht]
    have hcomm := (Set.mem_centralizer_iff.mp hpC) (lens.updateK r) hur
    rw [← hq, ← updateK_mul, ← updateK_mul] at hcomm
    exact updateK_injective lens hcomm
  · unfold fvP_extend
    rw [probLensRange_from_updates]
    exact Set.subset_centralizer_centralizer

/-- **`fvP_reduce` is a retraction of `fvP_extend`** (`reduce (extend r) ≤ r`): pushing a
    footprint forward along a lens and pulling it back recovers at most it.  Proven in full from
    `updateK` being a monoid homomorphism (`centralizer_preimage_image_subset`). -/
theorem fvP_reduce_extend {a b} (lens : Lens a b) (r : ProbLensRange a) :
    fvP_reduce lens (fvP_extend lens r) ≤ r := by
  unfold fvP_reduce
  rw [ProbLensRange.from_le_iff, fvP_reduce_constraint]
  have hext : Set.centralizer (fvP_extend lens r).updates
            = Set.centralizer (lens.updateK '' r.updates) := by
    unfold fvP_extend
    rw [probLensRange_from_updates, Set.centralizer_centralizer_centralizer]
  rw [hext]
  have key := centralizer_preimage_image_subset lens.updateK (updateK_mul lens) r.updates
  rw [probLensRange_updates_cc] at key
  exact key

noncomputable
def fvpInductiveFunctionGS : InductiveFunctionGettersSetters ProbLensRange where
  nothing := ⊥
  join := (· ⊔ ·)
  getter := fvP_getter
  setter := fvP_setter
  reduce := fvP_reduce
  extend := fvP_extend

noncomputable
def fvPMexpr {ctx t} (m : ModuleExpression ctx t) : (ProbLensRange State) :=
  fvpInductiveFunctionGS.evalMexpr m

noncomputable
def fvP (m : Module t) : FVP := fvpInductiveFunctionGS.eval m

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
    exact sup_le (fvP_extend_mono lens le_sup_left) (fvP_extend_mono lens le_sup_right)
  extend_reduce := by
    intro a b lens r
    exact fvP_reduce_extend lens r
  reduce_mono := fun lens h => fvP_reduce_mono lens h
  extend_mono := fun lens h => fvP_extend_mono lens h


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
