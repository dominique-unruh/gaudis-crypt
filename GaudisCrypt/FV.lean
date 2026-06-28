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

The four framework obligations `fvP_reduce_sup`, `fvP_extend_sup`, `fvP_extend_updates`
and `fvP_reduce_extend` were already left as `sorry` in the deterministic original ("stated
as axioms for review"); they remain `sorry` here. Everything else — the definitions, the
generic centralizer helpers, and the soundness combinators — is complete.

The genuinely *total* (sorry-free) probabilistic footprint used by the RO-instantiate
development is the separate, directly-defined `fvP_stmt`/`confinedP_of_fv` in
`Lib/RO/InstantiateCommon`; this file is the more general `Module`-level computed footprint.
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
    (`reduce r₁ ⊔ reduce r₂ ≤ reduce (r₁ ⊔ r₂)`, monotonicity) is proven here. The reverse reduces —
    like `fvP_extend_sup` and via the same `extend ⊣ pull` adjunction — to the single kernel-monoid
    double-commutant theorem `u '' (CC W) ⊆ CC (u '' W)`. Its converse `CC (u '' W) ⊆ u '' (CC W)` is
    proven (`centralizer_preimage_image_subset`/extraction); this direction is the open structure
    theorem (the probe shows the obstructing "correlating" commutant elements are benign). -/
theorem fvP_reduce_sup {a b} (lens : Lens a b) (r₁ r₂ : ProbLensRange b) :
    fvP_reduce lens (r₁ ⊔ r₂) = fvP_reduce lens r₁ ⊔ fvP_reduce lens r₂ :=
  le_antisymm
    (by sorry)
    (sup_le (fvP_reduce_mono lens le_sup_left) (fvP_reduce_mono lens le_sup_right))

end FvReduceSup

/-- `fvP_extend` distributes over joins.

    Status: **true** (computationally verified in the deterministic `Function.End` model — see
    `CounterExamples/ExtendSupProbe`, which also checks `u⁻¹'(R)` is bicommutant-closed, i.e. `extend`
    has a right adjoint), but the reverse `≤` is open. Only the `≤`-half
    (`extend r₁ ⊔ extend r₂ ≤ extend (r₁ ⊔ r₂)`, monotonicity) is proven here. The reverse reduces to
    `u '' (CC Y) ⊆ CC (u '' Y)` (image of a bicommutant ⊆ bicommutant of the image). Its converse is
    proven via extraction; this direction is the open kernel-monoid double-commutant / tensor-commutant
    theorem (the probe shows the obstructing "correlating" commutant elements are benign). -/
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
  join_mono_right := fun h => sup_le_sup_left h _
  le_join_left := fun _ _ => le_sup_left
  le_join_right := fun _ _ => le_sup_right
  nothing_le := fun _ => bot_le
  reduce_join := by
    intro a b r1 r2 lens
    apply fvP_reduce_sup lens r1 r2
  extend_join := by
    intro a b r1 r2 lens
    apply fvP_extend_sup lens r1 r2
  extend_reduce := by
    intro a b lens r
    exact fvP_reduce_extend lens r


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
