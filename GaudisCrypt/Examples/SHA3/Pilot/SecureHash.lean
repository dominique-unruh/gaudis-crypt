import GaudisCrypt.Examples.SHA3.Pilot.OptionIndifferentiability
import GaudisCrypt.Syntax.Clone
import GaudisCrypt.Lib.EC.Distr

/-!
# Security games for hash functions with failing oracles (EasyCrypt `proof/SecureHash.eca`) —
EC-fidelity port

Preimage, second-preimage and collision games for a construction `F : OCONSTRUCTION` over a
primitive `P : OPRIMITIVE`, against an adversary whose oracle calls are bounded by `bound`
(`FBounder`, `PBounder`).  The file has no lemmas: `SHA3OSecurity` clones it.

Translation (as the pilot `SecureRO`'s):
* the theory's operators and axioms are the class `Params from to block`, whose types are
  `outParam`s (a clone is an instance), so they are written without types, as in EC;
* `clone import OptionIndifferentiability as OIndif with …` is `clone` (`Syntax/Clone.lean`);
* `Bounder.bounder` is a `global_var`; EC's paths `A(FBounder(F(P)), PBounder(P))` are terms, the
  subtyping `OPRIMITIVE <: ODPRIMITIVE` a coercion on the arguments;
* the games' results `m1 <> m2 /\ exists y, …` are decided classically, as EC's logic is;
* EC's commented-out `PROM.GenEager` clone and module type `RF` are left out.
-/

namespace GaudisCrypt.SHA3.Pilot.SecureHash

open GaudisCrypt GaudisCrypt.EC

/-- EC's `type from, to, block.`, `op sampleto`, `op bound`, `op increase_counter` and their
axioms.  The types are `outParam`s: a clone of the theory is an instance. -/
class Params («from» «to» block : outParam Type) where
  sampleto : SubProbability «to»
  bound : ℤ
  bound_ge0 : 0 ≤ bound
  sampleto_ll : is_lossless sampleto
  sampleto_full : is_full sampleto
  sampleto_fu : is_funiform sampleto
  increase_counter : ℤ → «from» → ℤ
  increase_counter_spec : ∀ c m, c ≤ increase_counter c m

export Params (sampleto bound bound_ge0 sampleto_ll sampleto_full sampleto_fu increase_counter
  increase_counter_spec)

variable {«from» «to» block : Type} [Inhabited «from»] [Inhabited «to»] [Inhabited block]
  [Params «from» «to» block]

clone import GaudisCrypt.SHA3.Pilot.OptionIndifferentiability as OIndif with
  type p <- block, type f_in <- «from», type f_out <- «to»

global_var Bounder.bounder : ℤ

module Bounder {
  proc init () : Unit {
    Bounder.bounder <- 0;
    return ()
  };
}

module FBounder using (F : OFUNCTIONALITY) : OFUNCTIONALITY {
  proc init () : Unit {
    _ <- call Bounder.init ();
    _ <- call F.init ();
    return ()
  };
  proc f (x : «from») : (Option «to») {
    var y : Option «to»;
    y <- (none : Option «to»);
    if (decide (increase_counter $Bounder.bounder $x ≤ bound)) {
      Bounder.bounder <- increase_counter $Bounder.bounder $x;
      y <- call F.f ($x);
    }
    return $y
  };
}

module PBounder using (P : OPRIMITIVE) : OPRIMITIVE {
  proc init () : Unit {
    _ <- call P.init ();
    _ <- call Bounder.init ();
    return ()
  };
  proc f (x : block) : (Option block) {
    var y : Option block;
    y <- (none : Option block);
    if (decide ($Bounder.bounder < bound)) {
      y <- call P.f ($x);
      Bounder.bounder <- $Bounder.bounder + 1;
    }
    return $y
  };
  proc fi (x : block) : (Option block) {
    var y : Option block;
    y <- (none : Option block);
    if (decide ($Bounder.bounder < bound)) {
      y <- call P.fi ($x);
      Bounder.bounder <- $Bounder.bounder + 1;
    }
    return $y
  };
}

/-- EC's `module type AdvPreimage (F : ODFUNCTIONALITY) (P : ODPRIMITIVE) =
{ proc guess(h : to) : from }`. -/
abbrev AdvPreimage := ODFUNCTIONALITY ×ₘ ODPRIMITIVE →ₘ procmod («to») → «from»

set_option maxHeartbeats 400000 in
-- the `module` command's `apply_simp` proof normalises the adversary's callee
-- `A(FBounder(F(P)), PBounder(P))`, the coercions to `OD…` duplicating its arguments: ~160k alone
open Classical in
module Preimage using (A : AdvPreimage, F : OCONSTRUCTION, P : OPRIMITIVE) {
  proc main () : Bool {
    var m : «from», hash : «to», hash' : Option «to»;
    hash <$ sampleto;
    _ <- call PBounder(P).init ();
    _ <- call FBounder(F(P)).init ();
    m <- call A(FBounder(F(P)), PBounder(P)).guess ($hash);
    hash' <- call FBounder(F(P)).f ($m);
    return decide ($hash' = some $hash)
  };
}

/-! ### Second preimage -/

/-- EC's `module type AdvSecondPreimage (F : ODFUNCTIONALITY) (P : ODPRIMITIVE) =
{ proc guess(m : from) : from }`. -/
abbrev AdvSecondPreimage := ODFUNCTIONALITY ×ₘ ODPRIMITIVE →ₘ procmod («from») → «from»

set_option maxHeartbeats 400000 in
-- the `module` command's `apply_simp` proof normalises the adversary's callee
-- `A(FBounder(F(P)), PBounder(P))`, the coercions to `OD…` duplicating its arguments: ~160k alone
open Classical in
module SecondPreimage using (A : AdvSecondPreimage, F : OCONSTRUCTION, P : OPRIMITIVE) {
  proc main (m1 : «from») : Bool {
    var m2 : «from», hash1 : Option «to», hash2 : Option «to»;
    _ <- call PBounder(P).init ();
    _ <- call FBounder(F(P)).init ();
    m2 <- call A(FBounder(F(P)), PBounder(P)).guess ($m1);
    hash1 <- call FBounder(F(P)).f ($m1);
    hash2 <- call FBounder(F(P)).f ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

/-! ### Collision -/

/-- EC's `module type AdvCollision (F : ODFUNCTIONALITY) (P : ODPRIMITIVE) =
{ proc guess() : from * from }`. -/
abbrev AdvCollision := ODFUNCTIONALITY ×ₘ ODPRIMITIVE →ₘ procmod () → («from» × «from»)

set_option maxHeartbeats 400000 in
-- the `module` command's `apply_simp` proof normalises the adversary's callee
-- `A(FBounder(F(P)), PBounder(P))`, the coercions to `OD…` duplicating its arguments: ~160k alone
open Classical in
module Collision using (A : AdvCollision, F : OCONSTRUCTION, P : OPRIMITIVE) {
  proc main () : Bool {
    var m1 : «from», m2 : «from», hash1 : Option «to», hash2 : Option «to»;
    _ <- call PBounder(P).init ();
    _ <- call FBounder(F(P)).init ();
    m1, m2 <- call A(FBounder(F(P)), PBounder(P)).guess ();
    hash1 <- call FBounder(F(P)).f ($m1);
    hash2 <- call FBounder(F(P)).f ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

end GaudisCrypt.SHA3.Pilot.SecureHash
