import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.PHoareWp

/-!
# EasyCrypt's `auto` and `rnd` steps for `hoare` and `phoare`

    phoare_auto, hoare_auto   -- EC's `auto`: wp over the code back to the last call, then `skip`

Our `phoare` is computed by wp, samplings included (exact averages), so EC's `rnd` steps on a
`phoare` goal become, once `phoare_auto` has gone through the code, steps on an expectation
`d.expected f ≤ r` left by a sampling:

    rnd_pred1 v    -- EC's `rnd (pred1 v)`: `f a ≤ [v = a]`, bounded by `d {v}`
    rnd_bound      -- EC's `rnd` with a lossless distribution: `f a ≤ r` for every `a`
    rnd_null       -- EC's `hoare`: `f` is `0` on the support, whatever the bound

Each leaves the pointwise goal (the obligation EC's `auto` would leave after the step).
-/

namespace GaudisCrypt

namespace SubProbability

variable {α : Type} {d : SubProbability α} {f : α → ENNReal} {r : ENNReal}

/-- EC's `rnd (pred1 v)` on an upper bound: an expectation below the indicator of `v` is at most
the mass of `v`. -/
theorem expected_le_of_le_pred1 (v : α) (h : ∀ a, f a ≤ indicatorE (v = a))
    (hv : d.1 {v} ≤ r) : d.expected f ≤ r := by
  refine le_trans ?_ hv
  calc d.expected f ≤ d.expected (fun a => indicatorE (v = a)) := by
        rw [SubProbability.expected_eq_tsum, SubProbability.expected_eq_tsum]
        exact ENNReal.tsum_le_tsum fun a => by gcongr; exact h a
    _ ≤ d.1 {v} := by
        rw [SubProbability.expected_eq_tsum,
          tsum_eq_single v (fun a ha => by simp [indicatorE, Ne.symm ha])]
        simp [indicatorE]

/-- EC's `rnd` on a lossless distribution: a pointwise bound is a bound of the expectation (the
total mass is at most `1`). -/
theorem expected_le_of_le (h : ∀ a, f a ≤ r) : d.expected f ≤ r := by
  calc d.expected f ≤ d.expected (fun _ => r) := by
        rw [SubProbability.expected_eq_tsum, SubProbability.expected_eq_tsum]
        exact ENNReal.tsum_le_tsum fun a => by gcongr; exact h a
    _ ≤ r := by
        letI : MeasurableSpace α := ⊤
        change ∫⁻ _, r ∂d.1 ≤ r
        rw [MeasureTheory.lintegral_const]
        calc r * d.1 Set.univ ≤ r * 1 := by gcongr; exact d.2.1
          _ = r := mul_one r

/-- EC's `hoare` (probability `0`): an expectation null on the support is below anything. -/
theorem expected_le_of_null (h : ∀ a ∈ d.support, f a = 0) : d.expected f ≤ r :=
  (le_of_eq (SubProbability.expected_eq_zero_of_support h)).trans bot_le

end SubProbability

namespace ECAuto

open Lean Meta Elab Tactic

/-- EC's `auto` on the statement judgment `g` (a registered one): wp over the statements from the
end (`Judgment.wpOne`: deterministic code, samplings, conditionals) until a call or `skip`. -/
def wpAll (g : MVarId) : MetaM MVarId := do
  let mut g := g
  for _ in [0:1000] do
    let (d, ty) ← Judgment.descOf g none
    let st := ty.getArg! d.stmtArg
    let k ← ECSim.lastKind st
    if k == .skip || k == .call then break
    let s ← saveState
    try g ← Judgment.wpOne g none
    catch _ =>
      s.restore
      break
  return g

end ECAuto

open Lean Elab Tactic ECAuto in
/-- **EC's `auto`** on a `phoare` statement judgment: wp back to the last call, then `skip` if
the code is used up. -/
elab "phoare_auto" : tactic => do
  liftMetaTactic1 fun g => some <$> wpAll g
  evalTactic (← `(tactic| try phoare_skip))

open Lean Elab Tactic ECAuto in
/-- **EC's `auto`** on a Hoare triple about a statement. -/
elab "hoare_auto" : tactic => do
  liftMetaTactic1 fun g => some <$> wpAll g
  evalTactic (← `(tactic| try hoare_skip))

-- the variables the steps introduce (`a`, `ha`) are the proof's to name: not hygienic
set_option hygiene false

/-- **EC's `rnd (pred1 v)`** on a goal `d.expected f ≤ r`: the goal `f a ≤ [v = a]` for every
`a` (`a` introduced), then `d {v} ≤ r` unless `le_rfl` closes it. -/
macro "rnd_pred1 " v:term:max : tactic => `(tactic|
  (refine SubProbability.expected_le_of_le_pred1 $v (fun a => ?_) ?_
   rotate_left
   first | exact le_rfl | rotate_right))

/-- **EC's `rnd`** with a lossless distribution, on a goal `d.expected f ≤ r`: the goal
`f a ≤ r` for every `a` (`a` introduced). -/
macro "rnd_bound" : tactic => `(tactic|
  refine SubProbability.expected_le_of_le (fun a => ?_))

/-- **EC's `hoare`** (probability `0`) on a goal `d.expected f ≤ r`: the goal `f a = 0` for every
`a` in the support (`a`, `ha` introduced). -/
macro "rnd_null" : tactic => `(tactic|
  refine SubProbability.expected_le_of_null (fun a ha => ?_))

set_option hygiene true

end GaudisCrypt
