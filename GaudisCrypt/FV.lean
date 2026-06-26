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

theorem fvP_reduce_sup {a b} (lens : Lens a b) (r₁ r₂ : ProbLensRange b) :
    fvP_reduce lens (r₁ ⊔ r₂) = fvP_reduce lens r₁ ⊔ fvP_reduce lens r₂ := by
  sorry

end FvReduceSup

/-- `fvP_extend` distributes over joins. -/
theorem fvP_extend_sup {a b} (lens : Lens a b) (r₁ r₂ : ProbLensRange a) :
    fvP_extend lens (r₁ ⊔ r₂) = fvP_extend lens r₁ ⊔ fvP_extend lens r₂ := sorry

theorem fvP_extend_updates {a b} (lens : Lens a b) (range : ProbLensRange a) :
    (fvP_extend lens range).updates = lens.updateK '' range.updates := by
  sorry

/-- `fvP_reduce` is a retraction of `fvP_extend`: pushing a footprint forward along a
    lens and pulling it back recovers it.  (Only `≤` is used in the proof.) -/
theorem fvP_reduce_extend {a b} (lens : Lens a b) (r : ProbLensRange a) :
    fvP_reduce lens (fvP_extend lens r) ≤ r := by
    sorry

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
