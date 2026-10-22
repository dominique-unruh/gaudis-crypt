import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.PHoareWp

/-!
# Plug and pray (EasyCrypt `theories/modules/PlugAndPray.eca`)

Run an abstract game, then guess an index uniformly: the guess matches any function `ψ` of the
game's final state and result with probability `1/|I|`, independently of the game's event `φ`.
EasyCrypt:

```
module Guess (G:Game) = {
  proc main(x:tin): tval * tres = {
    var o,i;
    o <@ G.main(x);
    i <$ duniform indices;
    return (i,o);
  }
}.

lemma PBound (G <: Game ) (phi : (glob G) -> tres -> bool) (psi : (glob G) -> tres -> tval) x0 &m:
  (forall gG o, phi gG o => psi gG o \\in indices) =>
  (1%r/card%r) * Pr[G.main(x0) @ &m: phi (glob G) res]
  = Pr[Guess(G).main(x0) @ &m: phi (glob G) res.`2 /\\ res.`1 = psi (glob G) res.`2].
proof.
move=> psi_in_indices.
byphoare (_: (glob G) = (glob G){m} /\\ x0 = x ==>
             phi (glob G) (snd res) /\\
             res.`1 = psi (glob G) res.`2)=> //.
pose p:= Pr[G.main(x0) @ &m: phi (glob G) res].
proc.
seq  1: (phi (glob G) o)
        (p) (1%r/card%r)
        _ 0%r => //.
  (* FIXME: This is more verbose than it should be! *)
+ call (: (glob G) = (glob G){m} /\\ x = x0 ==> phi (glob G) res) => //.
  bypr=> &m0 @/p [#] eq_globs ->.
  byequiv (: ={glob G, x} ==> ={glob G, res})=> //=.
  by proc true.
+ rnd (pred1 (psi (glob G) o)); skip=> /> &m0 hphi.
  by rewrite duniform1E psi_in_indices.
by hoare; auto=> /> &m0 ->.
qed.
```

Adaptation: EC's `glob G` (the game's state) is the whole global state, `§allGlobals`; EC's
index list is a finite type, so `ψ ∈ indices` is automatic.  The judgment's bound
may depend on the initial state, so `(1/|I|) · Pr[G.main(x0) : φ]` is the bound itself — no
`seq`, `call`, `bypr` or `byequiv`: `phoare_wp` leaves the game's expectation symbolic and the
uniform guess averages out.
-/

namespace GaudisCrypt.Examples.EasyCryptBench.PlugAndPray

open GaudisCrypt

/-- EC's abstract types `tin`, `tres`, `tval`; the indices are a finite type. -/
structure Types where
  tin : Type
  tres : Type
  tval : Type
  [tin_inhabited : Inhabited tin]
  [tres_inhabited : Inhabited tres]
  [tval_inhabited : Inhabited tval]
  [tval_fintype : Fintype tval]

@[reducible] instance (T : Types) : Inhabited T.tin := T.tin_inhabited
@[reducible] instance (T : Types) : Inhabited T.tres := T.tres_inhabited
@[reducible] instance (T : Types) : Inhabited T.tval := T.tval_inhabited
@[reducible] instance (T : Types) : Fintype T.tval := T.tval_fintype
@[reducible] noncomputable instance (T : Types) : DecidableEq T.tval := Classical.decEq _

variable (T : Types)

moduletype Game {
  proc main (x : T.tin) -> T.tres;
}

module Guess using (G : Game T) {
  proc main (x : T.tin) : (T.tval × T.tres) {
    var o : T.tres, i : T.tval;
    o <- call G.main ($x);
    i <$ SubProbability.uniform;
    return ($i, $o)
  };
}

/-- EC's `PBound`, as a judgment whose bound is `G`'s own expectation of `φ` from the initial
    state, scaled.  `§allGlobals` is the whole global state — EC's `glob G` in the postcondition,
    and `&m` in the bound. -/
theorem pbound_phoare (G : Game T) (φ : VariableAssignment → T.tres → Prop)
    (ψ : VariableAssignment → T.tres → T.tval) :
    phoare[ (Module.app (Guess T) G) (x) : True ==>
        φ §allGlobals (§res).2 ∧ (§res).1 = ψ §allGlobals (§res).2 ]
      = ((Module.Proc.procedure (Game.main T G)).ewp §x (fun r g => indicatorE (φ g r))
          §allGlobals / Fintype.card T.tval) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 5
  phoare_skip
  intro σ x _
  -- whatever the game did, the uniform guess hits `ψ` with probability `1/|I|`
  have hguess : ∀ v gl, ∑ i : T.tval, indicatorE (φ gl v) * indicatorE (i = ψ gl v)
      / (Fintype.card T.tval : ENNReal) = indicatorE (φ gl v) * (1 / Fintype.card T.tval) := by
    intro v gl
    simp_rw [mul_div_assoc]
    rw [← Finset.mul_sum]
    congr 1
    simpa only [eq_comm] using ENNReal.sum_indicatorE_eq_div_card (ψ gl v)
  simp only [hguess]
  rw [Procedure.ewp_mul_const, ← div_eq_mul_one_div]

/-- **EC's `PBound`**, as EC states it. -/
theorem pbound (G : Game T) (φ : VariableAssignment → T.tres → Prop)
    (ψ : VariableAssignment → T.tres → T.tval) (x₀ : T.tin) (σ : VariableAssignment) :
    (1 / Fintype.card T.tval : ENNReal) *
        (Module.Proc.procedure (Game.main T G)).Pr x₀ σ (fun r g => φ g r)
      = (Module.Proc.procedure (Module.app (Guess T) G)).Pr x₀ σ
          (fun r g => φ g r.2 ∧ r.1 = ψ g r.2) := by
  rw [Procedure.Pr_eq_ewp, Procedure.Pr_eq_ewp, mul_comm, ← div_eq_mul_one_div]
  -- the judgment's conditions, as the notation elaborates them, are these up to unfolding
  exact (pbound_phoare T G φ ψ x₀ σ trivial).symm

end GaudisCrypt.Examples.EasyCryptBench.PlugAndPray
