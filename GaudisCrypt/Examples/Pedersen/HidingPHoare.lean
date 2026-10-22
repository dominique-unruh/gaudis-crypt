import GaudisCrypt.Examples.Pedersen.Hiding
import GaudisCrypt.Logic.PHoareWp
import GaudisCrypt.Syntax.PHoareSyntax

/-!
# Pedersen hiding, the probabilistic part with `phoare`

EC's `fakecommit_half` and `hi_ll` (`Hiding.lean` proves them by hand), with the `phoare` tactics.
-/

namespace GaudisCrypt.Examples.Pedersen

open GaudisCrypt

variable (group : PedersenGroup)

/-- EC's `fakecommit_half`, as the judgment EC's `byphoare` reduces it to:
```
proc; wp; swap 4 3; rnd (pred1 b'); call ug_ll; wp; rnd; call uc_ll; auto.
```
Here no `swap`/`rnd (pred1 b')` is needed: `phoare_wp` computes the game's exact expectation, with
the adversary's two calls symbolic, and losslessness plus linearity finish it. -/
theorem fakecommit_half_phoare (U : Unhider group.types)
    (uc_ll : (Unhider.choose group.types U).procedure.IsLossless)
    (ug_ll : (Unhider.guess group.types U).procedure.IsLossless) :
    phoare[ (fakeGame group U) : True ==> §res = true ] = (1 / 2) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 9
  phoare_skip
  intro σ _
  -- the two coin branches of `U.guess` partition (`indicatorE_add_not`), so the coin averages to
  -- `1/2` whatever `U.guess` does; `U.choose` then only contributes its mass
  simp only [← ENNReal.add_div, ← Finset.sum_add_distrib, ← Procedure.ewp_add,
    ← Bool.not_eq_true, indicatorE_add_not, ug_ll.ewp_const, ENNReal.sum_div_card,
    uc_ll.ewp_const]

/-- EC's `fakecommit_half`, from the judgment (`byphoare`). -/
theorem fakecommit_half' (U : Unhider group.types) (σ : VariableAssignment)
    (uc_ll : IsLossless (Unhider.choose group.types U).procedure)
    (ug_ll : IsLossless (Unhider.guess group.types U).procedure) :
    Pr (fakeGame group U) σ = 1 / 2 := by
  have h := Procedure.Pr_of_phoareProc (fakecommit_half_phoare group U uc_ll ug_ll)
    (args := ()) (σ := σ) trivial
  refine ENNReal.coe_inj.mp (h.trans ?_)
  norm_num

/-- EC's `hi_ll`: the fake game is lossless. -/
theorem hi_ll_phoare (U : Unhider group.types)
    (uc_ll : (Unhider.choose group.types U).procedure.IsLossless)
    (ug_ll : (Unhider.guess group.types U).procedure.IsLossless) :
    phoare[ (fakeGame group U) : True ==> True ] = 1 := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 9
  phoare_skip
  intro σ _
  simp only [ug_ll.ewp_const, ENNReal.sum_div_card, uc_ll.ewp_const, ENNReal.add_halves]

end GaudisCrypt.Examples.Pedersen
