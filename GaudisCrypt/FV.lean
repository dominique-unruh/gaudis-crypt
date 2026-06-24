-- CHAOS FILE

import GaudisCrypt.Language.Modules.InductiveFunctions
import GaudisCrypt.TotLensRange
import GaudisCrypt.ProgramRange

open GaudisCrypt.Language.Modules
open GaudisCrypt.Language.Modules.InductiveFunctions
open GaudisCrypt.Language.Programs
open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics

namespace FV

variable [ProgramSpec]

abbrev FV := TotLensRange State


noncomputable
def fv_getter (getter : Getter a s) : TotLensRange s := Program.range (Program.get getter)

noncomputable
def fv_setter (setter : Setter a s) : TotLensRange s := Program.range' (Program.set setter)

def fv_reduce {a b} (lens : Lens a b) (range : TotLensRange b) : TotLensRange a :=
  TotLensRange.from { f | ∀ g ∈ range.updates, lens.update f * g = g * lens.update f}.centralizer

def fv_extend {a b} (lens : Lens a b) (range : TotLensRange a) : TotLensRange b :=
  TotLensRange.from (lens.update '' range.updates)


/-! ### Properties of `fv_reduce` / `fv_extend` needed for `fv_proc_instantiate`.

These are stated as axioms for review.  Once `fv_reduce`/`fv_extend` have real
definitions they should become theorems.  Note: the proof of `fv_proc_instantiate`
needs *no* properties of `fv_getter`/`fv_setter` — they are used opaquely. -/

section FvReduceSup
omit [ProgramSpec]

/-- Two `TotLensRange`s with the same `updates` are equal. -/
private lemma lensRange_eq_of_updates {m} {x y : TotLensRange m} (h : x.updates = y.updates) :
    x = y := by
  obtain ⟨_, _, _, _⟩ := x
  obtain ⟨_, _, _, _⟩ := y
  simp only at h
  subst h
  rfl

/-- `TotLensRange.from G` has the double-centralizer of `G` as its `updates`. -/
private lemma lensRange_from_updates {m} (G : Set (Function.End m)) :
    (TotLensRange.from G).updates = Set.centralizer (Set.centralizer G) := by
  change (Submonoid.centralizer ((Submonoid.centralizer G).carrier) : Set (Function.End m))
      = Set.centralizer (Set.centralizer G)
  rw [Submonoid.coe_centralizer]
  rfl

/-- The `updates` of a join is the double centralizer of the union of the `updates`. -/
private lemma lensRange_sup_updates {m} (x y : TotLensRange m) :
    (x ⊔ y).updates = Set.centralizer (Set.centralizer (x.updates ∪ y.updates)) := by
  change (TotLensRange.from (x.updates ∪ y.updates)).updates = _
  exact lensRange_from_updates _

/-- Bicommutant closure `cⁿ²` is monotone. -/
private lemma cl_mono {m} {A B : Set (Function.End m)} (h : A ⊆ B) :
    Set.centralizer (Set.centralizer A) ⊆ Set.centralizer (Set.centralizer B) :=
  Set.centralizer_subset (Set.centralizer_subset h)

/-- `TotLensRange.from` turns unions into joins. -/
private lemma lensRange_from_union {m} (A B : Set (Function.End m)) :
    TotLensRange.from A ⊔ TotLensRange.from B = TotLensRange.from (A ∪ B) := by
  apply lensRange_eq_of_updates
  rw [lensRange_sup_updates, lensRange_from_updates, lensRange_from_updates,
      lensRange_from_updates]
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

/-- The `fv_reduce` constraint set is `lens.update ⁻¹'` of a centralizer. -/
private lemma fv_reduce_constraint {a b} (lens : Lens a b) (V : Set (Function.End b)) :
    {f : Function.End a | ∀ g ∈ V, lens.update f * g = g * lens.update f}
      = lens.update ⁻¹' (Set.centralizer V) := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_centralizer_iff]
  exact ⟨fun h g hg => (h g hg).symm, fun h g hg => (h g hg).symm⟩

theorem fv_reduce_sup {a b} (lens : Lens a b) (r₁ r₂ : TotLensRange b) :
    fv_reduce lens (r₁ ⊔ r₂) = fv_reduce lens r₁ ⊔ fv_reduce lens r₂ := by
  sorry

end FvReduceSup

/-- `fv_extend` distributes over joins. -/
theorem fv_extend_sup {a b} (lens : Lens a b) (r₁ r₂ : TotLensRange a) :
    fv_extend lens (r₁ ⊔ r₂) = fv_extend lens r₁ ⊔ fv_extend lens r₂ := sorry

theorem fv_extend_updates(lens : Lens a b) (range : TotLensRange a) :
  (fv_extend lens range).updates = lens.update '' range.updates := by
  sorry

/-- `fv_reduce` is a retraction of `fv_extend`: pushing a footprint forward along a
    lens and pulling it back recovers it.  (Only `≤` is used in the proof.) -/
theorem fv_reduce_extend {a b} (lens : Lens a b) (r : TotLensRange a) :
    fv_reduce lens (fv_extend lens r) ≤ r := by
    sorry

noncomputable
def fvInductiveFunctionGS : InductiveFunctionGettersSetters TotLensRange where
  nothing := ⊥
  join := (· ⊔ ·)
  getter := fv_getter
  setter := fv_setter
  reduce := fv_reduce
  extend := fv_extend

noncomputable
def fvMexpr {ctx t} (m : ModuleExpression ctx t) : (TotLensRange State) := fvInductiveFunctionGS.evalMexpr m

noncomputable
def fv (m : Module t) : FV := fvInductiveFunctionGS.eval m

scoped instance : ReducibleGettersSetters fvInductiveFunctionGS where
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
    apply fv_reduce_sup lens r1 r2
  extend_join := by
    intro a b r1 r2 lens
    apply fv_extend_sup lens r1 r2
  extend_reduce := by
    intro a b lens r
    exact fv_reduce_extend lens r


theorem fvMexpr_upper_bound : fv (m.toModule) ≤ fvMexpr m :=
  evalMexpr_upper_bound fvInductiveFunctionGS.inductiveFunction m

theorem fv_app (a : Module (.arr A B)) (b : Module A) :
    fv (.app a b) ≤ fv a ⊔ fv b :=
    InductiveFunction.app _ _ _

theorem fv_pair (a : Module A) (b : Module B) :
    fv (.pair a b) = fv a ⊔ fv b :=
    InductiveFunction.pair _ _ _

theorem fv_fst (a : Module (.prod A B)) :
    fv (.fst a) ≤ fv a :=
    InductiveFunction.fst _ _

theorem fv_snd (a : Module (.prod A B)) :
    fv (.snd a) ≤ fv a :=
    InductiveFunction.snd _ _

@[simp]
theorem fv_unit (a : Module .unit) : fv a = ⊥ :=
 InductiveFunction.unit _ _

noncomputable
def fv_proc {sig holes} (proc : ProcedureWithHoles holes sig) : TotLensRange State := fvInductiveFunctionGS.proc proc

noncomputable
def fv_stmt {s holes} (stmt : StmtWithHoles holes s) : TotLensRange (ProcedureState s) := fvInductiveFunctionGS.stmt stmt

end FV
