import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.ModuleVar
import GaudisCrypt.Syntax.ModuleSubtype
import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Lib.EC.FMap
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ConcreteFootprint
import GaudisCrypt.Logic.FootprintUpper
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.PHoareRnd

/-!
# Random oracles (EasyCrypt `theories/crypto/ROM.eca`)

The module types of an oracle and the lazy random oracle `Lazy.LRO`, with its losslessness.
(`FiniteEager`, and the equivalences between the lazy and the eager oracle, are not ported:
`Lib/EC/PROM.lean` has EC's programmable oracles and their lazy/eager theory.)

The theory's types `in_t`, `out_t`, `d_in_t`, `d_out_t` are `outParam`s of the class `Params`,
its operator `dout` the class's field: a clone is `clone import GaudisCrypt.EC.ROM as H with
type in_t <- …, op dout <- …`.  The module variable `LRO.m` is a `module_var`.
-/

set_option ec.strict true

namespace GaudisCrypt.EC.ROM

open GaudisCrypt GaudisCrypt.EC

/-- EC's `type in_t, out_t. op dout: in_t -> out_t distr. type d_in_t, d_out_t.` -/
class Params (in_t out_t d_in_t d_out_t : outParam Type) where
  dout : in_t → SubProbability out_t

export Params (dout)

variable {in_t out_t d_in_t d_out_t : Type} [Inhabited in_t] [Inhabited out_t]
  [Inhabited d_in_t] [Inhabited d_out_t] [DecidableEq in_t]
  [Params in_t out_t d_in_t d_out_t]

-- A signature for oracles from "in_t" to "out_t"
moduletype POracle {
  proc o (x : in_t) -> out_t;
}

/-- A Distinguisher (or distinguishing context) is a single algorithm that has access to an
oracle, and has some input/output behaviour: EC's `module type Distinguisher (H : POracle) =
{ proc run(_ : d_in_t): d_out_t }`. -/
abbrev Distinguisher := POracle →ₘ procmod (d_in_t) → d_out_t

-- The oracle may be stateful, and its state might need initialized
moduletype Oracle {
  proc init () -> Unit;
  proc o (x : in_t) -> out_t;
}

/-- An `Oracle` is a `POracle` (its `o`). -/
module_subtype Oracle <: POracle

module Exp using (H : Oracle, D : Distinguisher) {
  proc main (x : d_in_t) : d_out_t {
    var r : d_out_t;
    _ <- call H.init ();
    r <- call D(H).run ($x);
    return $r
  };
}

/-! ## `theory Lazy` -/

namespace Lazy

module_var LRO.m : FMap in_t out_t

module LRO : Oracle {
  proc init () : Unit {
    LRO.m <- FMap.empty;
    return ()
  };
  proc o (x : in_t) : out_t {
    var r : out_t;
    r <$ dout $x;
    if (decide (¬ FMap.dom $LRO.m $x)) {
      LRO.m <- FMap.set $LRO.m $x $r;
    }
    return oget (FMap.get $LRO.m $x)
  };
}

/-- `glob LRO`: its map `LRO.m` (read off the code; for the footprint tactics). -/
@[fp_bound] theorem fvP_LRO : FVP.fvP (LRO : Oracle (in_t := in_t) (out_t := out_t)) ≤
    (LRO.m (in_t := in_t) (out_t := out_t) (d_in_t := d_in_t) (d_out_t := d_out_t)).footprint := by
  fp_module LRO.m

/-- EC's `lemma LRO_init_ll : islossless LRO.init`. -/
theorem LRO_init_ll : islossless LRO.init := by
  -- EC: by proc; auto.
  phoare_proc; phoare_auto

/-- EC's `lemma LRO_o_ll : (forall x, is_lossless (dout x)) => islossless LRO.o`. -/
theorem LRO_o_ll : (∀ x : in_t, is_lossless (dout x)) → islossless LRO.o := by
  -- EC: by move=> dout_ll; proc; auto=> &0; rewrite dout_ll.
  intro dout_ll; phoare_proc; phoare_auto; exact dout_ll

end Lazy

end GaudisCrypt.EC.ROM
