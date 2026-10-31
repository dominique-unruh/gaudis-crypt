import GaudisCrypt.Examples.SHA3.OptionIndifferentiability
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Lib.EC.Distr

/-!
# Security games for hash functions with failing oracles (EasyCrypt `proof/SecureHash.eca`)

Preimage, second-preimage and collision resistance of a construction `F : OCONSTRUCTION` over a
primitive `P : OPRIMITIVE`, against an adversary whose oracle calls are bounded by `bound`
(`FBounder`, `PBounder`).

Translation notes (see `notes/SHA3/README.md`):
* The abstract theory's types `from`, `to`, `block` and operators `sampleto`, `bound`,
  `increase_counter` are section variables; its axioms are hypotheses (`bound_ge0` …), supplied by a
  clone's `realize`s.  `from` and `to` are keywords, hence `«from»` and `«to»`.
* `clone import OptionIndifferentiability as OIndif with type p <- block, type f_in <- from,
  type f_out <- to` is `OptionIndifferentiability` applied to these types.
* `Bounder`'s module variable `bounder` is a lens parameter: each clone declares its own.
* The games' results `m1 <> m2 /\ exists y, …` are decided classically, as EasyCrypt's logic is.
-/

namespace GaudisCrypt.SHA3.SecureHash

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.OptionIndifferentiability

variable («from» «to» block : Type) [Inhabited «from»] [Inhabited «to»] [Inhabited block]
variable (sampleto : SubProbability «to»)
variable (bound : ℤ)
variable (increase_counter : ℤ → «from» → ℤ)

/-- EasyCrypt's axioms on the theory's operators (hypotheses, realized by a clone). -/
structure Axioms : Prop where
  bound_ge0 : 0 ≤ bound
  sampleto_ll : is_lossless sampleto
  sampleto_full : is_full sampleto
  sampleto_fu : is_funiform sampleto
  increase_counter_spec : ∀ c m, c ≤ increase_counter c m

/-! `Bounder`'s module variable `bounder` is a parameter: a clone declares its own. -/
variable (Bounder_bounder : Lens ℤ VariableAssignment)

module Bounder {
  proc init () : Unit {
    Bounder_bounder <- 0;
    return ()
  };
}

module FBounder using (F : OFUNCTIONALITY block «from» «to») : (OFUNCTIONALITY block «from» «to») {
  proc init () : Unit {
    _ <- call (Bounder Bounder_bounder) ();
    _ <- call F.init ();
    return ()
  };
  proc f (x : «from») : (Option «to») {
    var y : Option «to»;
    y <- (none : Option «to»);
    if (decide (increase_counter $Bounder_bounder $x ≤ bound)) {
      Bounder_bounder <- increase_counter $Bounder_bounder $x;
      y <- call F.f ($x);
    }
    return $y
  };
}

module PBounder using (P : OPRIMITIVE block «from» «to») : (OPRIMITIVE block «from» «to») {
  proc init () : Unit {
    _ <- call P.init ();
    _ <- call (Bounder Bounder_bounder) ();
    return ()
  };
  proc f (x : block) : (Option block) {
    var y : Option block;
    y <- (none : Option block);
    if (decide ($Bounder_bounder < bound)) {
      y <- call P.f ($x);
      Bounder_bounder <- $Bounder_bounder + 1;
    }
    return $y
  };
  proc fi (x : block) : (Option block) {
    var y : Option block;
    y <- (none : Option block);
    if (decide ($Bounder_bounder < bound)) {
      y <- call P.fi ($x);
      Bounder_bounder <- $Bounder_bounder + 1;
    }
    return $y
  };
}

/-- EasyCrypt's `module type AdvPreimage (F : ODFUNCTIONALITY) (P : ODPRIMITIVE) =
{ proc guess(h : to) : from }`. -/
abbrev AdvPreimage :=
  ODFUNCTIONALITY block «from» «to» ×ₘ ODPRIMITIVE block «from» «to» →ₘ procmod («to») → «from»

open Classical in
module Preimage using (A : AdvPreimage «from» «to» block, F : OCONSTRUCTION block «from» «to»,
    P : OPRIMITIVE block «from» «to») {
  proc main () : Bool {
    var m : «from», hash : «to», hash' : Option «to»;
    hash <$ sampleto;
    _ <- call (OPRIMITIVE.init block «from» «to»
      (Module.app (PBounder «from» «to» block bound Bounder_bounder) P)) ();
    _ <- call (OFUNCTIONALITY.init block «from» «to»
      (Module.app (FBounder «from» «to» block bound increase_counter Bounder_bounder)
        (Module.app F (ODPRIMITIVE.mk block «from» «to»
          { f := OPRIMITIVE.f block «from» «to» P, fi := OPRIMITIVE.fi block «from» «to» P })))) ();
    m <- call (Module.app A (Module.pair
      (ODFUNCTIONALITY.mk block «from» «to»
        { f := OFUNCTIONALITY.f block «from» «to»
            (Module.app (FBounder «from» «to» block bound increase_counter Bounder_bounder)
              (Module.app F (ODPRIMITIVE.mk block «from» «to»
                { f := OPRIMITIVE.f block «from» «to» P,
                  fi := OPRIMITIVE.fi block «from» «to» P }))) })
      (ODPRIMITIVE.mk block «from» «to»
        { f := OPRIMITIVE.f block «from» «to»
            (Module.app (PBounder «from» «to» block bound Bounder_bounder) P)
          fi := OPRIMITIVE.fi block «from» «to»
            (Module.app (PBounder «from» «to» block bound Bounder_bounder) P) }))) ($hash);
    hash' <- call (OFUNCTIONALITY.f block «from» «to»
      (Module.app (FBounder «from» «to» block bound increase_counter Bounder_bounder)
        (Module.app F (ODPRIMITIVE.mk block «from» «to»
          { f := OPRIMITIVE.f block «from» «to» P,
            fi := OPRIMITIVE.fi block «from» «to» P })))) ($m);
    return decide ($hash' = some $hash)
  };
}

/-- EasyCrypt's `module type AdvSecondPreimage (F : ODFUNCTIONALITY) (P : ODPRIMITIVE) =
{ proc guess(m : from) : from }`. -/
abbrev AdvSecondPreimage :=
  ODFUNCTIONALITY block «from» «to» ×ₘ ODPRIMITIVE block «from» «to» →ₘ procmod («from») → «from»

open Classical in
module SecondPreimage using (A : AdvSecondPreimage «from» «to» block,
    F : OCONSTRUCTION block «from» «to», P : OPRIMITIVE block «from» «to») {
  proc main (m1 : «from») : Bool {
    var m2 : «from», hash1 : Option «to», hash2 : Option «to»;
    _ <- call (OPRIMITIVE.init block «from» «to»
      (Module.app (PBounder «from» «to» block bound Bounder_bounder) P)) ();
    _ <- call (OFUNCTIONALITY.init block «from» «to»
      (Module.app (FBounder «from» «to» block bound increase_counter Bounder_bounder)
        (Module.app F (ODPRIMITIVE.mk block «from» «to»
          { f := OPRIMITIVE.f block «from» «to» P, fi := OPRIMITIVE.fi block «from» «to» P })))) ();
    m2 <- call (Module.app A (Module.pair
      (ODFUNCTIONALITY.mk block «from» «to»
        { f := OFUNCTIONALITY.f block «from» «to»
            (Module.app (FBounder «from» «to» block bound increase_counter Bounder_bounder)
              (Module.app F (ODPRIMITIVE.mk block «from» «to»
                { f := OPRIMITIVE.f block «from» «to» P,
                  fi := OPRIMITIVE.fi block «from» «to» P }))) })
      (ODPRIMITIVE.mk block «from» «to»
        { f := OPRIMITIVE.f block «from» «to»
            (Module.app (PBounder «from» «to» block bound Bounder_bounder) P)
          fi := OPRIMITIVE.fi block «from» «to»
            (Module.app (PBounder «from» «to» block bound Bounder_bounder) P) }))) ($m1);
    hash1 <- call (OFUNCTIONALITY.f block «from» «to»
      (Module.app (FBounder «from» «to» block bound increase_counter Bounder_bounder)
        (Module.app F (ODPRIMITIVE.mk block «from» «to»
          { f := OPRIMITIVE.f block «from» «to» P,
            fi := OPRIMITIVE.fi block «from» «to» P })))) ($m1);
    hash2 <- call (OFUNCTIONALITY.f block «from» «to»
      (Module.app (FBounder «from» «to» block bound increase_counter Bounder_bounder)
        (Module.app F (ODPRIMITIVE.mk block «from» «to»
          { f := OPRIMITIVE.f block «from» «to» P,
            fi := OPRIMITIVE.fi block «from» «to» P })))) ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

/-- EasyCrypt's `module type AdvCollision (F : ODFUNCTIONALITY) (P : ODPRIMITIVE) =
{ proc guess() : from * from }`. -/
abbrev AdvCollision :=
  ODFUNCTIONALITY block «from» «to» ×ₘ ODPRIMITIVE block «from» «to» →ₘ
    procmod () → («from» × «from»)

open Classical in
module Collision using (A : AdvCollision «from» «to» block, F : OCONSTRUCTION block «from» «to»,
    P : OPRIMITIVE block «from» «to») {
  proc main () : Bool {
    var m1 : «from», m2 : «from», hash1 : Option «to», hash2 : Option «to»;
    _ <- call (OPRIMITIVE.init block «from» «to»
      (Module.app (PBounder «from» «to» block bound Bounder_bounder) P)) ();
    _ <- call (OFUNCTIONALITY.init block «from» «to»
      (Module.app (FBounder «from» «to» block bound increase_counter Bounder_bounder)
        (Module.app F (ODPRIMITIVE.mk block «from» «to»
          { f := OPRIMITIVE.f block «from» «to» P, fi := OPRIMITIVE.fi block «from» «to» P })))) ();
    m1, m2 <- call (Module.app A (Module.pair
      (ODFUNCTIONALITY.mk block «from» «to»
        { f := OFUNCTIONALITY.f block «from» «to»
            (Module.app (FBounder «from» «to» block bound increase_counter Bounder_bounder)
              (Module.app F (ODPRIMITIVE.mk block «from» «to»
                { f := OPRIMITIVE.f block «from» «to» P,
                  fi := OPRIMITIVE.fi block «from» «to» P }))) })
      (ODPRIMITIVE.mk block «from» «to»
        { f := OPRIMITIVE.f block «from» «to»
            (Module.app (PBounder «from» «to» block bound Bounder_bounder) P)
          fi := OPRIMITIVE.fi block «from» «to»
            (Module.app (PBounder «from» «to» block bound Bounder_bounder) P) }))) ();
    hash1 <- call (OFUNCTIONALITY.f block «from» «to»
      (Module.app (FBounder «from» «to» block bound increase_counter Bounder_bounder)
        (Module.app F (ODPRIMITIVE.mk block «from» «to»
          { f := OPRIMITIVE.f block «from» «to» P,
            fi := OPRIMITIVE.fi block «from» «to» P })))) ($m1);
    hash2 <- call (OFUNCTIONALITY.f block «from» «to»
      (Module.app (FBounder «from» «to» block bound increase_counter Bounder_bounder)
        (Module.app F (ODPRIMITIVE.mk block «from» «to»
          { f := OPRIMITIVE.f block «from» «to» P,
            fi := OPRIMITIVE.fi block «from» «to» P })))) ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

end GaudisCrypt.SHA3.SecureHash
