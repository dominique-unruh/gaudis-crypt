import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.HoareWp
import GaudisCrypt.Logic.HoareFrame

/-!
# Counting oracle queries

An adversary that interacts with an oracle for `q` rounds; the oracle counts its queries in a
global.  The adversary is abstract, constrained only by a footprint hypothesis (EC's
`A <: Adv {-count}`), and the claim is the loop invariant you would state in EC:

```
hoare[ Game(A, CountingOracle).main : q = n ==> count = n ]
```
-/

namespace GaudisCrypt.Examples.QueryCounting

open GaudisCrypt

/-- The number of queries the oracle has answered. -/
global_var count : ℕ

moduletype Oracle {
  proc query (x : ℕ) -> ℕ;
}

moduletype Adversary {
  proc next (y : ℕ) -> ℕ;
}

-- answers a query with a fresh coin flip, and counts it
module CountingOracle : Oracle {
  proc query(x : ℕ) : ℕ {
    var b : Bool;
    count <- $count + 1;
    b <$ SubProbability.uniform;
    return if $b then $x else 0
  };
}

module Game using (A : Adversary, O : Oracle) {
  proc main(q : ℕ) : Unit {
    var i : ℕ, x : ℕ, y : ℕ;
    count <- 0;
    i <- 0;
    y <- 0;
    while ($i < $q) {
      x <- call A.next ($y);
      y <- call O.query ($x);
      i <- $i + 1;
    }
    return ()
  };
}

/-- The game makes exactly `q` oracle queries, for any adversary that does not touch the counter
    (EC: `A <: Adversary {-count}`). -/
theorem game_query_count (A : Adversary) (n : ℕ)
    (hA : ∀ a, (procedureDenotation (Adversary.next A).procedure a).inFootprint
      (count.footprint)ᶜ) :
    hoare[ (Module.app Game (Module.pair A CountingOracle)) (q) : $q = n ==> $count = n ] := by
  hoare_proc_to_stmt
  hoare_inline 0
  hoare_wp 1
  hoare_while §count = §i ∧ §i ≤ §q ∧ §q = n
  case body =>
    hoare_wp 1
    hoare_inline 1
    hoare_wp 5
    hoare_call (hoare_call_frame count hA)
    hoare_skip
    intro c i q ⟨⟨h1, h2, h3⟩, hlt⟩ r g hg _ _
    simp at hlt
    omega
  case exit =>
    intro c i q ⟨h1, h2, h3⟩ h
    simp at h
    omega
  hoare_wp 5
  hoare_skip
  exact fun _ h => ⟨Nat.zero_le _, h⟩

end GaudisCrypt.Examples.QueryCounting


namespace GaudisCrypt.Examples.QueryCounting

/- `hoare_wp` through a conditional. -/
example : hoare[ True ==> §u ≤ 1 ] {
    var u : ℕ, b : Bool;
    b <$ SubProbability.uniform;
    if ($b) { u <- 1; } else { u <- 0; }
  } := by
  hoare_wp 2
  hoare_skip
  -- the conditional stays inside the value (`Stmt.Det.ite`): `(if b then 1 else 0) ≤ 1`
  exact fun _ a _ => by split <;> simp

end GaudisCrypt.Examples.QueryCounting
