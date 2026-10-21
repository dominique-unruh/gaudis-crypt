import GaudisCrypt.Examples.Pedersen.Hiding

/-!
# A Hoare triple about the Pedersen hiding game

A test of the `hoare[…]` tactics on `HidingExperiment(Pedersen, U).main`, with the adversary
calls left abstract.  `hoareStmt`/`hoareProc` is partial correctness, so hiding itself (a
probability of `1/2`) is out of reach; the triple here is a smaller fact that still needs
Pedersen's algebra.  See `notes/HoareTacticsIssues.md` for what this test turned up.
-/

namespace GaudisCrypt.Examples.Pedersen

open GaudisCrypt

variable (group : PedersenGroup)

/-- If `U.guess` diverges on every commitment in `⟨g⟩`, then so does the whole hiding game:
    Pedersen's commitment `g^d * (g^x)^m` is always `g^(d + x*m)`. -/
theorem hiding_diverges_of_guess_diverges (U : Unhider group.types)
    (hU : hoare[ (Unhider.guess group.types U) : ∃ e : group.F, $c = group.g ^ e ==> False ]) :
    hoare[ (hidingGame group U) : True ==> False ] := by
  hoare_proc_to_stmt
  hoare_inline 0
  hoare_inline 2
  hoare_inline 0
  hoare_wp 1
  hoare_call hU
  hoare_wp 6
  hoare_call
  hoare_wp 5
  hoare_skip
  -- what is left is EC's closing `algebra`: the commitment is `g ^ (d + x * m)`
  exact fun _ x _ _ _ _ _ d _ => ⟨_, commit_shift group x _ d⟩

end GaudisCrypt.Examples.Pedersen
