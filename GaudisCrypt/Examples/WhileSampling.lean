import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.PHoareWhileRev
import GaudisCrypt.Lib.EC.Logic

/-!
# Sampling until a test fails terminates (EasyCrypt `examples/WhileSampling.ec`)

Draw from a lossless distribution until a test fails; if the test fails with positive
probability, the loop terminates with probability `1`.  EC's file, line by line; its one lemma,
`Sample_lossless`, is proven with EC's script.

Translation:
* `type t. op sample … axiom sample_ll … op test … axiom pr_ntest` are the class `Params`
  (the file is its own theory).
* EC's `while I V k ε` is `phoare_while I V k ε` (`Logic/PHoareWhileRev.lean`): the loop
  terminates because the integer variant `V`, at most `k` and positive while the test passes,
  decreases in each round with probability at least `ε`.

Gap list:
* GAP 1: EC's `=> //` after `seq` and `while` closes a goal that is a hypothesis (`ih`, the
  axiom `pr_ntest`); here `exact ih`, `exact pr_ntest`.
* GAP 2 (goals as shown): the body goal of `phoare_while` has EC's abstract statement `w` (the
  loop to come) as a variable of type `Stmt`; a judgment about `w` prints as a term
  (`phoareStmt … w …`), not as `phoare[ … ]`.
-/

set_option ec.strict true

namespace GaudisCrypt.Examples.WhileSampling

open GaudisCrypt GaudisCrypt.EC

/-- EC's `type t. op sample: t distr. axiom sample_ll: is_lossless sample. op test: t -> bool.
axiom pr_ntest: 0%r < mu sample (predC test).` -/
class Params (t : outParam Type) where
  sample : SubProbability t
  sample_ll : is_lossless sample
  test : t → Bool
  pr_ntest : 0 < mu sample (predC test)

export Params (sample sample_ll test pr_ntest)

variable {t : Type} [Inhabited t] [Params t]

module Sample {
  proc sample () : t {
    var r : t;
    r <$ sample;
    while (test $r) {
      r <$ sample;
    }
    return $r
  };
}

/-- EC's `lemma Sample_lossless: islossless Sample.sample`. -/
theorem Sample_lossless : islossless Sample.sample := by
  -- EC: proc; seq  1: true=> //.
  phoare_proc; phoare_seq_lossless 1 : (True)
  -- EC: + by auto=> />; exact/sample_ll.
  · phoare_auto; exact sample_ll
  -- EC: while true (if test r then 1 else 0) 1 (mu sample (predC test))=> //.
  phoare_while True (if test §r then 1 else 0) 1 (mu sample (predC test))
  -- EC: + by move=> _ r; case: (test r).
  · intro r; cases test r <;> simp
  -- EC: + move=> ih; seq  1: true=> //.
  --       by auto; rewrite sample_ll.
  --     (GAP 1: the loop to come, by `ih`)
  · intro w ih; phoare_seq_lossless 1 : (True)
    · phoare_auto; exact fun _ _ => sample_ll
    · exact ih
  -- EC: + by auto; rewrite sample_ll.
  · phoare_auto; exact fun _ _ => sample_ll
  -- EC: rewrite pr_ntest=> /= z; conseq (: true ==> !test r).
  --     (GAP 1)
  · exact pr_ntest
  · intro z; phoare_conseq (: True ==> test §r = false)
    -- EC: + smt().
    · smt_close
    -- EC: by rnd; auto=> />.
    phoare_rnd; phoare_auto

end GaudisCrypt.Examples.WhileSampling
