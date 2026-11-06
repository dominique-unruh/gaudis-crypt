import GaudisCrypt.Logic.ExpectationCall
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

/-!
# EasyCrypt's `fel` (the failure event lemma), once

EC's

    fel init cntr step q bad [O₁: pre₁, …] inv

bounds the probability of a failure event `bad` after an abstract module's run by
`∑_{i ∈ [init, q)} step i`: each oracle call that may set `bad` (its `preᵢ` holds) does so with
probability at most `step cntr` and increases the counter `cntr`; the other calls leave `bad` and
`cntr` alone; `inv` holds throughout.

Here the same premises, for the oracles of `Module.app D O` with `D` abstract, give the bound,
by `Module.ewp_app_le` (the supermartingale abstract call) on one potential, `felPotential`, once
for all games: `⊤` off the invariant, `1` once `bad` holds, else the bound still to pay,
`∑_{i ∈ [cntr, q)} step i`.  The state the premises talk about is the view `L.get g` of the
globals through a lens `L` that `D` does not touch (the counter, the variables of `bad` and
`inv`).

Deviation from EC: `bad` must persist (`FelOracle.keep`), where EC's conclusion is about `bad`
at the end however it got there; the events of the SHA-3 games are monotone.  The premises are
Hoare and pHL judgments about the oracle procedures, proven with the usual tactics.
-/

namespace GaudisCrypt

/-- A procedure's expectation is monotone in the function on the outcomes a Hoare triple allows. -/
theorem Procedure.ewp_mono_of_hoare {sig} {A : sig.ParamType → VariableAssignment → Prop}
    {p : Procedure sig} {B : sig.ret → VariableAssignment → Prop} (h : hoareProc A p B)
    {args : sig.ParamType} {σ : VariableAssignment} (hA : A args σ)
    {F G : sig.ret → VariableAssignment → ENNReal} (hFG : ∀ v g, B v g → F v g ≤ G v g) :
    p.ewp args F σ ≤ p.ewp args G σ :=
  SubProbability.expected_mono_of_null (h args σ hA) fun x hx => hFG x.1 x.2 (not_not.mp hx)

variable {Ω : Type} (L : Lens Ω VariableAssignment) (cntr : Ω → ℤ) (step : ℤ → ENNReal) (q : ℤ)
  (bad inv : Ω → Prop)

open Classical in
/-- The potential of EC's `fel`: `⊤` off the invariant, `1` once `bad` holds, else the bound
still to pay for the calls from `cntr` to `q`. -/
noncomputable def felPotential (s : Ω) : ENNReal :=
  if ¬ inv s then ⊤ else if bad s then 1 else ∑ i ∈ Finset.Ico (cntr s) q, step i

/-- The premises of EC's `fel` for one oracle procedure `p` with precondition `pre` (the calls
that may set `bad`), over the view `L.get` of the globals. -/
structure FelOracle {sig : ProcedureSignature} (pre : Ω → Prop) (p : Procedure sig) : Prop where
  /-- a call that may set `bad` is one of the `q` the bound pays for -/
  lt : ∀ s, inv s → ¬ bad s → pre s → cntr s < q
  /-- … and sets it with probability at most `step cntr` -/
  step : phoareProc (fun _ g => inv (L.get g) ∧ ¬ bad (L.get g) ∧ pre (L.get g)) p
    (fun _ g' => indicatorE (bad (L.get g'))) (· ≤ ·) (fun _ g => step (cntr (L.get g)))
  /-- … and increases the counter (unless it set `bad`) -/
  incr : ∀ c, hoareProc (fun _ g => inv (L.get g) ∧ ¬ bad (L.get g) ∧ pre (L.get g) ∧
      cntr (L.get g) = c) p (fun _ g' => inv (L.get g') ∧ (bad (L.get g') ∨ c < cntr (L.get g')))
  /-- the other calls do not set `bad` nor decrease the counter -/
  same : ∀ c, hoareProc (fun _ g => inv (L.get g) ∧ ¬ bad (L.get g) ∧ ¬ pre (L.get g) ∧
      cntr (L.get g) = c) p (fun _ g' => inv (L.get g') ∧ ¬ bad (L.get g') ∧ c ≤ cntr (L.get g'))
  /-- `bad` persists -/
  keep : hoareProc (fun _ g => inv (L.get g) ∧ bad (L.get g)) p
    (fun _ g' => inv (L.get g') ∧ bad (L.get g'))

variable {L cntr step q bad inv}

/-- The sum still to pay shrinks as the counter grows. -/
theorem felPotential_sum_anti {c c' : ℤ} (h : c ≤ c') :
    ∑ i ∈ Finset.Ico c' q, step i ≤ ∑ i ∈ Finset.Ico c q, step i :=
  Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_left h)

/-- **The step of the potential**: an oracle call with `fel`'s premises does not increase the
potential in expectation. -/
theorem FelOracle.ewp_le {sig : ProcedureSignature} {pre : Ω → Prop} {p : Procedure sig}
    (h : FelOracle L cntr step q bad inv pre p) (a : sig.ParamType) (g : VariableAssignment) :
    p.ewp a (fun _ g' => felPotential cntr step q bad inv (L.get g')) g ≤
      felPotential cntr step q bad inv (L.get g) := by
  classical
  by_cases hi : inv (L.get g)
  swap
  · simp only [felPotential, hi, not_false_eq_true, if_true]
    exact le_top
  by_cases hb : bad (L.get g)
  · -- `bad` persists: the potential stays `1`
    rw [show felPotential cntr step q bad inv (L.get g) = 1 by simp [felPotential, hi, hb]]
    refine (Procedure.ewp_mono_of_hoare h.keep ⟨hi, hb⟩ (G := fun _ _ => 1)
      fun v g' ⟨hi', hb'⟩ => by simp [felPotential, hi', hb']).trans ?_
    exact Procedure.ewp_const_le _ _ _ _
  have hpot : felPotential cntr step q bad inv (L.get g) =
      ∑ i ∈ Finset.Ico (cntr (L.get g)) q, step i := by simp [felPotential, hi, hb]
  rw [hpot]
  set c := cntr (L.get g)
  by_cases hp : pre (L.get g)
  · -- a call that may set `bad`: at most `step c` for it, the rest from `c + 1` on
    have hlt := h.lt _ hi hb hp
    refine (Procedure.ewp_mono_of_hoare (h.incr c) ⟨hi, hb, hp, rfl⟩
      (G := fun _ g' => indicatorE (bad (L.get g')) + ∑ i ∈ Finset.Ico (c + 1) q, step i)
      fun v g' ⟨hi', hc'⟩ => ?_).trans ?_
    · by_cases hb' : bad (L.get g')
      · simp [felPotential, hi', hb']
      · have hc'' : c + 1 ≤ cntr (L.get g') := (hc'.resolve_left hb')
        simp only [felPotential, hi', not_true_eq_false, if_false, hb', indicatorE_false,
          zero_add]
        exact felPotential_sum_anti hc''
    rw [Procedure.ewp_add]
    refine (add_le_add (h.step a g ⟨hi, hb, hp⟩) (Procedure.ewp_const_le _ _ _ _)).trans
      (le_of_eq ?_)
    rw [← Finset.insert_Ico_add_one_left_eq_Ico hlt, Finset.sum_insert (by simp)]
  · -- any other call: `bad` stays false, the counter does not decrease
    refine (Procedure.ewp_mono_of_hoare (h.same c) ⟨hi, hb, hp, rfl⟩
      (G := fun _ _ => ∑ i ∈ Finset.Ico c q, step i)
      fun v g' ⟨hi', hb', hc'⟩ => ?_).trans (Procedure.ewp_const_le _ _ _ _)
    simp only [felPotential, hi', not_true_eq_false, if_false, hb']
    exact felPotential_sum_anti hc'

/-- **EC's `fel`, for an abstract module**: if every oracle satisfies `fel`'s premises
(`FelOracle`), then `D` applied to the oracles, started where `inv` holds and `bad` does not,
ends in `bad` with probability at most `∑_{i ∈ [cntr, q)} step i` (`Module.ewp_app_le` on
`felPotential`). -/
theorem Module.fel {T : Type 1} [IsModule T] {sig : ProcedureSignature} {holes : HoleSigs}
    (D : Module.Arr T (Module.Proc sig)) (ext : T → holes.Instantiation)
    (hD : Module.Representable D ext) (hdisj : FVP.fvP D ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (O : T) (pre : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Ω → Prop)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      FelOracle L cntr step q bad inv (pre n) ((ext O).lookup n))
    (a : sig.ParamType) (g : VariableAssignment) (hi : inv (L.get g)) (hb : ¬ bad (L.get g)) :
    (Module.app D O).procedure.ewp a (fun _ g' => indicatorE (bad (L.get g'))) g ≤
      ∑ i ∈ Finset.Ico (cntr (L.get g)) q, step i := by
  classical
  have hpot := Module.ewp_app_le (L := L) D ext hD hdisj hc O (felPotential cntr step q bad inv)
    (fun n a g => (horacle n).ewp_le a g) a g
  refine (Procedure.ewp_mono _ _ (fun v g' => ?_) _).trans (hpot.trans (le_of_eq ?_))
  · by_cases hi' : inv (L.get g')
    · by_cases hb' : bad (L.get g') <;> simp [felPotential, hi', hb']
    · simp [felPotential, hi']
  · simp [felPotential, hi, hb]

end GaudisCrypt
