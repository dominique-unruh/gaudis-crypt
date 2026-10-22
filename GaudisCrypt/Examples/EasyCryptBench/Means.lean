import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.PHoareWp

/-!
# Means (EasyCrypt `theories/encryption/Means.ec`)

An abstract worker run on an input drawn from `d`: the probability of an event is the
`d`-weighted mean of the worker's probabilities on each input.  EasyCrypt:

```
module Rand (W : Worker) = {
  proc main() : input * output = {
    var x, r;
    x <$ d;
    r <@ W.work(x);
    return (x,r);
  }
}.

lemma prCond (A <: Worker) &m (v:input)
             (ev:input -> glob A -> output -> bool):
    Pr[Rand(A).main() @ &m: ev v (glob A) (snd res) /\ v = fst res]
  = (mu1 d v) * Pr[A.work(v) @ &m : ev v (glob A) res].
proof.
byphoare (: (glob A) = (glob A){m}
            ==> ev (fst res) (glob A) (snd res) /\ fst res = v) => //.
pose pr:= Pr[A.work(v) @ &m: ev v (glob A) res].
proc.
seq 1: (v = x) (mu1 d v) pr 1%r 0%r ((glob A) = (glob A){m})=> //.
+ by rnd.
+ by rnd; auto=> />; rewrite pred1E.
+ call (: (glob A) = (glob A){m} /\ x = v
          ==> ev v (glob A) res)=> //.
  rewrite /pr; bypr=> /> &0 eqGlob.
  by byequiv (: ={glob A, x} ==> ={res, glob A})=> //; proc true.
by hoare => /=; call (: true); auto=> /#.
qed.

lemma Mean (A <: Worker) &m (ev:input -> glob A -> output -> bool):
     is_finite (support d)
  => let sup = to_seq (support d) in
       Pr[Rand(A).main()@ &m: ev (fst res) (glob A) (snd res)]
     = big predT (fun v, mu1 d v * Pr[A.work(v)@ &m:ev v (glob A) res]) sup.
proof.
  (* … via `introOrs` (a byequiv) and an induction over the support, using `prCond`
     and `Pr[mu_disjoint]` — about 30 lines *)
qed.
```

EC's `glob A` is the whole global state, `§allGlobals`.  Here `Mean` is what `phoare_wp`
computes outright: the exact expectation of the game, with the
worker's expectation left symbolic; the sum over `d` is `SubProbability.expected_eq_sum`.
`prCond` is the same with the event pinned to one input.
-/

namespace GaudisCrypt.Examples.EasyCryptBench.Means

open GaudisCrypt

/-- EC's abstract types and the input distribution `d` (finite input space). -/
structure Types where
  input : Type
  output : Type
  [input_inhabited : Inhabited input]
  [output_inhabited : Inhabited output]
  [input_fintype : Fintype input]
  d : SubProbability input

@[reducible] instance (T : Types) : Inhabited T.input := T.input_inhabited
@[reducible] instance (T : Types) : Inhabited T.output := T.output_inhabited
@[reducible] instance (T : Types) : Fintype T.input := T.input_fintype
@[reducible] noncomputable instance (T : Types) : DecidableEq T.input := Classical.decEq _

variable (T : Types)

/-- EC's `mu1 d v`. -/
noncomputable def mu1 (v : T.input) : ENNReal := T.d.1 {v}

moduletype Worker {
  proc work (x : T.input) -> T.output;
}

module Rand using (W : Worker T) {
  proc main () : (T.input × T.output) {
    var x : T.input, r : T.output;
    x <$ T.d;
    r <- call W.work ($x);
    return ($x, $r)
  };
}

/-- **EC's `Mean`**: the event's probability is the `d`-weighted mean of the worker's. -/
theorem mean_phoare (A : Worker T) (ev : T.input → VariableAssignment → T.output → Prop) :
    phoare[ (Module.app (Rand T) A) : True ==> ev (§res).1 §allGlobals (§res).2 ]
      = (∑ v, mu1 T v * (Module.Proc.procedure (Worker.work T A)).ewp v
          (fun r g => indicatorE (ev v g r)) §allGlobals) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 4
  phoare_skip
  intro σ _
  rw [SubProbability.expected_eq_sum]
  rfl

/-- **EC's `prCond`**: the event, pinned to the input `v`, has probability `μ(v)` times the
    worker's on `v`. -/
theorem prCond_phoare (A : Worker T) (v : T.input)
    (ev : T.input → VariableAssignment → T.output → Prop) :
    phoare[ (Module.app (Rand T) A) : True ==> ev v §allGlobals (§res).2 ∧ v = (§res).1 ]
      = (mu1 T v * (Module.Proc.procedure (Worker.work T A)).ewp v
          (fun r g => indicatorE (ev v g r)) §allGlobals) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 4
  phoare_skip
  intro σ _
  rw [SubProbability.expected_eq_sum]
  -- only the input `v` contributes
  rw [Finset.sum_eq_single v
      (fun b _ hb => by rw [indicatorE_of_not (Ne.symm hb), mul_zero, mul_zero])
      (by simp), indicatorE_of rfl, mul_one]
  rfl

/-! ## As EC states them -/

/-- EC's `prCond`. -/
theorem prCond (A : Worker T) (v : T.input) (ev : T.input → VariableAssignment → T.output → Prop)
    (σ : VariableAssignment) :
    ((Module.Proc.procedure (Module.app (Rand T) A)).Pr () σ (fun r g => ev v g r.2 ∧ v = r.1)
        : ENNReal)
      = mu1 T v * (Module.Proc.procedure (Worker.work T A)).Pr v σ (fun r g => ev v g r) := by
  rw [Procedure.Pr_eq_ewp, Procedure.Pr_eq_ewp]
  exact prCond_phoare T A v ev () σ trivial

/-- EC's `Mean`. -/
theorem mean (A : Worker T) (ev : T.input → VariableAssignment → T.output → Prop)
    (σ : VariableAssignment) :
    ((Module.Proc.procedure (Module.app (Rand T) A)).Pr () σ (fun r g => ev r.1 g r.2) : ENNReal)
      = ∑ v, mu1 T v * (Module.Proc.procedure (Worker.work T A)).Pr v σ (fun r g => ev v g r) := by
  simp only [Procedure.Pr_eq_ewp]
  exact mean_phoare T A ev () σ trivial

end GaudisCrypt.Examples.EasyCryptBench.Means
