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

namespace GaudisCrypt


/-! # fvP_extend_sup -/

-- fvP_extend_sup now called Lens.liftFootprint

-- `Footprint.ext`, `submonoid_centralizer_carrier`, `Footprint.double_commutant_closed`,
-- `Footprint.sup_updates` and `Footprint.from_union` moved to
-- `GaudisCrypt/Language/Footprint.lean`;
-- `SubProbability.double_commutant_mono` moved to `GaudisCrypt/Language/SubProbability.lean`.

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


-- `Lens.liftSubProbability_injective` and `Lens.liftSubProbability_mul` moved to
-- `GaudisCrypt/Language/Footprint.lean`.

/-- **Bridge identity.** Pushing a lens-localized kernel `lens.liftSubProbability f` through the split
bijection `b ≃ a × lens.ComplContent` yields exactly the `a`-component lift `Lens.fst.liftSubProbability f`.
This is what
makes the centralizer footprint `Lens.reduceFootprint` agree with the split-then-reduce construction. -/
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

-- `Footprint.empty_trivial` moved to `GaudisCrypt/Language/Footprint.lean`.





-- `Lens.liftFootprint_sup` moved to `GaudisCrypt/Language/Footprint.lean`.

/-- **`Lens.liftFootprint` distributes over arbitrary indexed suprema.**
    Generalises `Lens.liftFootprint_sup` from binary joins to indexed families. -/
theorem Lens.liftFootprint_iSup {a b : Type} {ι : Sort*} (lens : Lens a b)
    (rs : ι → Footprint a) :
    Lens.liftFootprint lens (⨆ i, rs i) = ⨆ i, Lens.liftFootprint lens (rs i) := by
  wlog ne : Nonempty b; { have := not_nonempty_iff.mp ne; apply Subsingleton.elim }
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
          SubProbability.double_commutant_mono (Set.iUnion_mono fun i => by
            simp only [Lens.liftFootprint, Footprint.from_updates]
            exact Set.subset_centralizer_centralizer)

/-! # End of fvP_extend_sup -/

/-! # Lens.reduceFootprint_sup -/


-- `Lens.reduceFootprint`, `Lens.reduceFootprint_mono`, `Lens.reduceFootprint_eq_from`,
-- `centralizer_reduceBaseGen_image` and `Lens.reduceFootprint_alt_def` moved to
-- `GaudisCrypt/Language/Footprint.lean`.


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

-- `reduceBaseGen_sup_subset` and `Lens.reduceFootprint_sup` moved to
-- `GaudisCrypt/Language/Footprint.lean`.




/-! # End of Lens.reduceFootprint_sup -/

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
def Lens.reduceFootprint_new {a b : Type} (lens : Lens a b) (range : Footprint b) :
    Footprint a :=
  -- transport `range` along `lens.splitSpace : b ≃ a × lens.ComplContent` (via the bijection lens),
  -- then reduce away the complement component with `Lens.reduceFootprint`.
  Lens.reduceFootprint Lens.fst (Lens.liftFootprint (Lens.bijection (Lens.splitSpace lens)) range)



/-! ### Properties of `Lens.reduceFootprint` / `Lens.liftFootprint` needed for the framework instance.

 -/


omit [ProgramSpec] in
/-- The `Lens.reduceFootprint` constraint set is `lens.liftSubProbability ⁻¹'` of a centralizer. -/
private lemma Lens.reduceFootprint_constraint {a b} (lens : Lens a b) (V : Set (b → SubProbability b)) :
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
    `C(u⁻¹'(C(u '' R))) ⊆ CC(R)`.  The engine behind `Lens.reduceFootprint_extend`: if `q` commutes
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

-- `updateK_image_univ_cc` moved to `GaudisCrypt/Language/Footprint.lean` (and out of `FVP`).

-- `footprint_equivariant`, `footprint_liftSubProbability_image` and
-- `Lens.liftFootprint_updates` moved to `GaudisCrypt/Language/Footprint.lean` (and out of `FVP`).

omit [ProgramSpec] in
/-- **`Lens.reduceFootprint` is a retraction of `Lens.liftFootprint`** (`reduce (extend r) ≤ r`):
    pushing a footprint forward along a lens and pulling it back recovers at most it.
    Proven in full from `updateK` being a monoid homomorphism
    (`centralizer_preimage_image_subset`). -/
theorem Lens.reduceFootprint_extend_le {a b} (lens : Lens a b) (r : Footprint a) :
    Lens.reduceFootprint lens (Lens.liftFootprint lens r) ≤ r := by
  rw [Lens.reduceFootprint_alt_def]
  rw [Footprint.from_le_iff, Lens.reduceFootprint_constraint]
  have hext : Set.centralizer (Lens.liftFootprint lens r).updates
            = Set.centralizer (lens.liftSubProbability '' r.updates) := by
    unfold Lens.liftFootprint
    rw [Footprint.from_updates, Set.centralizer_centralizer_centralizer]
  rw [hext]
  have key := centralizer_preimage_image_subset lens.liftSubProbability (Lens.liftSubProbability_mul lens) r.updates
  rw [Footprint.double_commutant_closed] at key
  exact key

omit [ProgramSpec] in
/-- **`Lens.reduceFootprint` is an exact left inverse of `Lens.liftFootprint`** (strengthening
    `Lens.reduceFootprint_extend` to equality): every `p ∈ r.updates` is itself
    `Lens.reduceSubProbability lens (lens.liftSubProbability p, i, o)` for the trivial
    `i () = pure β` / `o _ = pure ()`, hence lies in the generator set defining `Lens.reduceFootprint`. -/
theorem Lens.reduceFootprint_extend {a b} [Nonempty b] (lens : Lens a b) (r : Footprint a) :
    Lens.reduceFootprint lens (Lens.liftFootprint lens r) = r := by
  apply le_antisymm
  · apply Lens.reduceFootprint_extend_le
  · change r.updates ≤ (Lens.reduceFootprint lens (Lens.liftFootprint lens r)).updates
    rw [Lens.reduceFootprint_eq_from, Footprint.from_updates]
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
  reduce := Lens.reduceFootprint
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
    exact le_of_eq (Lens.reduceFootprint_sup lens r1 r2)
  extend_join := by
    intro a b r1 r2 lens
    exact (Lens.liftFootprint_sup lens r1 r2).symm.le
  extend_reduce := by
    intro a b lens r
    exact Lens.reduceFootprint_extend_le lens r
  reduce_mono := fun lens h => Lens.reduceFootprint_mono lens h
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

General footprint, `Lens.reduceFootprint` and `Lens.liftFootprint` facts, independent of any particular
program spec. -/

-- `Footprint.le_compl_comm` moved to `GaudisCrypt/Language/Footprint.lean`.

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

-- `liftSubProbability_comm_of_mem_reduce_compl` moved to
-- `GaudisCrypt/Language/Footprint.lean`.

/-- **The lift of a `v.footprint`-update commutes with every `R`-update**, when the
    `L`-reduction of `R` is disjoint from `v.footprint` — the lens-region instance of
    `liftSubProbability_comm_of_mem_reduce_compl`. -/
theorem liftSubProbability_comm_of_reduce_disj {t s c : Type} {L : Lens s c}
    {v : Lens t s} {R : Footprint c}
    (hred : Lens.reduceFootprint L R ≤ (v.footprint)ᶜ)
    {f : s → SubProbability s} (hf : f ∈ v.footprint.updates)
    {k : c → SubProbability c} (hk : k ∈ R.updates) :
    L.liftSubProbability f * k = k * L.liftSubProbability f :=
  liftSubProbability_comm_of_mem_reduce_compl
    ((Footprint.le_compl_comm _ _).mp hred hf) hk

/-- **A chained lens's footprint lies in `Rᶜ` whenever the inner footprint's `L`-reduction does**:
    from `Lens.reduceFootprint L R ≤ (v.footprint)ᶜ` conclude `R ≤ ((L.chain v).footprint)ᶜ`.  Route: flip the
    goal via `le_compl_comm` to `(L.chain v).footprint ≤ Rᶜ`, then show each generator
    `L.liftSubProbability (diracKer (v.liftFunction g))` commutes with every `k ∈ R.updates` via
    `liftSubProbability_comm_of_reduce_disj`. -/
theorem reduce_chain_le_compl {t s c : Type} {L : Lens s c} {v : Lens t s} {R : Footprint c}
    (hred : Lens.reduceFootprint L R ≤ (v.footprint)ᶜ) :
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
bicommutant closure adds nothing — is exactly the `Lens.liftFootprint_updates` extraction. -/

-- `Lens.liftFootprint_chain` and `Lens.chain_footprint` moved to
-- `GaudisCrypt/Language/Footprint.lean`.

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
  rw [Lens.footprint_chain, Lens.bijection_footprint, Lens.liftFootprint_top]

-- `Lens.compl_footprint` moved to `GaudisCrypt/Language/Footprint.lean`.


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


-- `Footprint.disjoint_lens_footprint_inf`, `pair_footprint_fst_snd` and `Footprint.lens_pair`
-- moved to `GaudisCrypt/Language/Footprint.lean`.

end GaudisCrypt
