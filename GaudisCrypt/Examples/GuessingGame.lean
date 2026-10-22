import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.PHoareWp

/-!
# A guessing game: the union bound over a loop

An abstract guesser plays `q` rounds; in each a fresh uniform secret is drawn after its guess, and
`hit` records whether a guess matched.  The claim is the union bound `Pr[hit] ≤ q / |X|`, proved
with the loop rule `phoare_while_le` and the potential
`indicatorE hit + (q − i) / |X|` — EC's `fel`, in the explicit-loop form.
-/

namespace GaudisCrypt.Examples.GuessingGame

open GaudisCrypt

/-- The space the secrets and guesses live in. -/
structure Space where
  X : Type
  [fintype : Fintype X]
  [inhabited : Inhabited X]

@[reducible] instance (S : Space) : Fintype S.X := S.fintype
@[reducible] instance (S : Space) : Inhabited S.X := S.inhabited
@[reducible] noncomputable instance (S : Space) : DecidableEq S.X := Classical.decEq _

variable (S : Space)

moduletype Guesser {
  proc guess (i : ℕ) -> S.X;
}

module Game using (A : Guesser S) {
  proc main (q : ℕ) : Bool {
    var i : ℕ, g : S.X, s : S.X, hit : Bool;
    i <- 0;
    hit <- false;
    while ($i < $q) {
      g <- call A.guess ($i);
      s <$ SubProbability.uniform;
      hit <- $hit || $g == $s;
      i <- $i + 1;
    }
    return $hit
  };
}

theorem game_hit_le (A : Guesser S) (n : ℕ) :
    phoare[ (Module.app (Game S) A) (q) : §q = n ==> §res = true ]
      ≤ ((n : ENNReal) / Fintype.card S.X) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_le indicatorE (§hit = true) + ((§q - §i : ℕ) : ENNReal) / Fintype.card S.X
  case body =>
    phoare_wp 4
    phoare_skip
    intro σ i q hit hlt
    simp only [decide_eq_true_eq] at hlt
    set D : ENNReal := ((q - (i + 1) : ℕ) : ENNReal) / Fintype.card S.X
    -- one round adds at most a fresh `1/|X|` chance: bound the expectation after the guess by a
    -- constant, which any procedure's expectation is below (`Procedure.ewp_const_le`)
    calc _ ≤ (Guesser.guess S A).procedure.ewp i
          (fun _ _ => indicatorE (hit = true) + 1 / Fintype.card S.X + D) σ.globals :=
          Procedure.ewp_mono _ _ (fun v _ => ?_) _
      _ ≤ indicatorE (hit = true) + 1 / Fintype.card S.X + D := Procedure.ewp_const_le _ _ _ _
      _ = _ := ?_
    · calc ∑ x, (indicatorE (hit = true ∨ (v == x) = true) + D) / Fintype.card S.X
          = ∑ x, indicatorE (hit = true ∨ v = x) / Fintype.card S.X + D := by
            simp only [beq_iff_eq, ENNReal.add_div, Finset.sum_add_distrib, ENNReal.sum_div_card]
        _ ≤ ∑ x, (indicatorE (hit = true) + indicatorE (v = x)) / Fintype.card S.X + D := by
            gcongr with x
            exact indicatorE_or_le _ _
        _ = indicatorE (hit = true) + 1 / Fintype.card S.X + D := by
            simp only [ENNReal.add_div, Finset.sum_add_distrib, ENNReal.sum_div_card,
              ENNReal.sum_indicatorE_eq_div_card]
    · -- the fresh chance and the remaining rounds are the rounds left before this one
      rw [add_assoc, ← ENNReal.add_div]
      congr 2
      rw [show q - i = (q - (i + 1)) + 1 by omega]
      push_cast
      ring
  case exit => exact fun _ _ _ _ => le_self_add
  phoare_wp 4
  phoare_skip
  intro _ h
  simp [h]

end GaudisCrypt.Examples.GuessingGame
