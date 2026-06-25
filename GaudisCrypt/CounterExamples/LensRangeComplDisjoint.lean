import Mathlib.Data.Finset.Sort
import GaudisCrypt.Language.Lens
import GaudisCrypt.TotLensRange
import Mathlib.Data.List.Basic
import Mathlib.Data.FinEnum
import Mathlib.SetTheory.Cardinal.Basic

/-!

Counterexample to the theorem:

A lens range has trivial intersection with its complement.

(It even shows: there is a lens range that is its own complement)

-/

namespace GaudisCrypt.CounterExamples

/-- `{id, Bool.not}` centralizes itself: the centralizer of `{id, Bool.not}` in `Bool → Bool`
    is exactly `{id, Bool.not}`. -/
private lemma bool_not_centralizer :
    (Submonoid.centralizer ({id, Bool.not} : Set (Function.End Bool))).carrier = {id, Bool.not} := by
  ext f
  simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup]
  constructor
  · intro h
    -- f commutes with Bool.not, so f(¬b) = ¬f(b) for all b
    have key : ∀ b : Bool, f (Bool.not b) = Bool.not (f b) := fun b => by
      have := congr_fun (h Bool.not (Or.inr rfl)) b
      simpa [HMul.hMul, Mul.mul, Function.comp] using this.symm
    cases hff : f false
    · left; funext b; cases b
      · exact hff
      · have := key false; rw [hff] at this; simpa using this
    · right; funext b; cases b
      · exact hff
      · have := key false; rw [hff] at this; simpa using this
  · rintro (rfl | rfl) g (rfl | rfl) <;>
    simp [HMul.hMul, Mul.mul]

private def lr_ext' : ∀ {x y : TotLensRange m}, x.updates = y.updates → x = y := by
  intro x y h; obtain ⟨_,_,_,_⟩ := x; obtain ⟨_,_,_,_⟩ := y
  simp only at h; subst h; rfl

/-- Counterexample: `{id, Bool.not}` is a valid `TotLensRange Bool` that is its own complement,
    disproving `TotLensRange.compl_is_compl` for general `TotLensRange`s. -/
def flipRange : TotLensRange Bool where
  updates := {id, Bool.not}
  id := Set.mem_insert _ _
  comp := by
    intro f g hf hg
    change f ∘ g = id ∨ f ∘ g = not
    rcases hf with rfl | rfl <;> rcases hg with rfl | rfl <;>
      decide
  double_commutant := by rw [bool_not_centralizer]; exact bool_not_centralizer

theorem flipRange_compl_eq_self : flipRangeᶜ = flipRange :=
  lr_ext' (by simp only [Compl.compl, flipRange, bool_not_centralizer])

end GaudisCrypt.CounterExamples
