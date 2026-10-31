import GaudisCrypt.Lib.EC.PROM
import GaudisCrypt.Lib.EC.Distr

/-!
# Random oracles are preimage, second-preimage and collision resistant
(EasyCrypt `proof/SecureRO.eca`)

The games `Preimage`, `SecondPreimage`, `Collision` against a random oracle `F : RF` whose
queries are bounded (`Bounder`), and the bounds for the random oracle `RO` of `PROM`.

Translation notes (see `notes/SHA3/README.md`):
* The abstract theory's types `from`, `to` and operators `sampleto`, `bound`, `increase_counter`,
  `bound_counter` are section variables; its axioms are the structure `Axioms`, a hypothesis of the
  lemmas.  `from` and `to` are keywords, hence `«from»` and `«to»`.
* `clone import PROM.FullRO as RO with type in_t <- from, type out_t <- to, op dout _ <- sampleto,
  type d_in_t <- unit, type d_out_t <- bool` is `PROM.FullRO` applied to these, through the
  abbreviations `RO.RO_T` (EasyCrypt's module type `RO`), `RO.RO`, `RO.LRO`.
* The module variables (`Counter.c`, `Bounder.bounder`, and the clone's `RO.m`, `FRO.m`) are lens
  parameters: a clone of the theory declares its own.  So are those of the sections' local modules
  (`SecondPreimage2.m2`, `D1.m1`), which only the proofs use (exception E6).
* The sections' local modules go into a namespace named after the section (`Preimage.FEL`,
  `SecondPreimage.FEL`, `Collision.FEL`): EasyCrypt reuses the name `FEL` in each.
* A module restriction `{-M}` on a module `M` without variables of its own (`-Preimage`) excludes
  the variables `M`'s code touches (`Counter.c`, `Bounder.bounder`).
* `RO` passed where an `RF` is expected is its `RF` view, written out (`RF.mk …`).
* The games' results (`hash = hash'`, `… /\ m1 <> m2`) are decided classically.
-/

-- the clone `RO` contains the module `RO` (`RO.RO`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.SecureRO

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM

variable («from» «to» : Type) [DecidableEq «from»] [Inhabited «from»] [Inhabited «to»]
variable (sampleto : SubProbability «to»)
variable (bound : ℤ)
variable (increase_counter : ℤ → «from» → ℤ)
variable (bound_counter : ℤ)

/-- EasyCrypt's axioms on the theory's operators (a hypothesis, realized by a clone). -/
structure Axioms : Prop where
  bound_gt0 : 0 < bound
  sampleto_ll : is_lossless sampleto
  sampleto_full : is_full sampleto
  sampleto_fu : is_funiform sampleto
  increase_counter_spec : ∀ c m, c ≤ increase_counter c m
  bound_counter_ge0 : 0 ≤ bound_counter

/-! `clone import PROM.FullRO as RO with type in_t <- from, type out_t <- to,
op dout _ <- sampleto, type d_in_t <- unit, type d_out_t <- bool`; its module variables `RO.m`,
`FRO.m` are the lens parameters `RO_m`, `FRO_m`. -/

-- one binder each: a `module` takes a whole binder group when it mentions one of its names
variable (RO_m : Lens (FMap «from» «to») VariableAssignment)
variable (FRO_m : Lens (FMap «from» («to» × flag)) VariableAssignment)

namespace RO
/-- EasyCrypt's module type `RO` of the clone. -/
abbrev RO_T := PROM.FullRO.RO_T «from» «to»
abbrev RO_Distinguisher := PROM.FullRO.RO_Distinguisher «from» «to» Unit Bool
noncomputable abbrev RO := PROM.FullRO.RO.asRO «from» «to» (fun _ => sampleto) RO_m
noncomputable abbrev LRO := PROM.FullRO.LRO «from» «to» (fun _ => sampleto) RO_m
end RO

/-! `Counter`'s and `Bounder`'s module variables are the lens parameters `Counter_c`,
`Bounder_bounder`. -/
variable (Counter_c : Lens ℤ VariableAssignment)
variable (Bounder_bounder : Lens ℤ VariableAssignment)

module Counter {
  proc init () : Unit {
    Counter_c <- 0;
    return ()
  };
}

moduletype RF {
  proc init () -> Unit;
  proc get (x : «from») -> «to»;
}

module Bounder using (F : RF «from» «to») : (RF «from» «to») {
  proc init () : Unit {
    Bounder_bounder <- 0;
    _ <- call (Counter Counter_c) ();
    _ <- call F.init ();
    return ()
  };
  proc get (x : «from») : «to» {
    var y : «to»;
    y <- (default : «to»);
    if (decide ($Bounder_bounder < bound)) {
      Bounder_bounder <- $Bounder_bounder + 1;
      if (decide (increase_counter $Counter_c $x < bound_counter)) {
        Counter_c <- increase_counter $Counter_c $x;
        y <- call F.get ($x);
      }
    }
    return $y
  };
}

/-- `RO` at the module type `RF` (its procedures `init` and `get`). -/
noncomputable def RO.asRF : RF «from» «to» :=
  RF.mk «from» «to»
    { init := PROM.FullRO.RO_T.init «from» «to» (RO.RO «from» «to» sampleto RO_m)
      get := PROM.FullRO.RO_T.get «from» «to» (RO.RO «from» «to» sampleto RO_m) }

-- EasyCrypt's `module type Oracle = { proc get(x : from) : to {} }`
moduletype Oracle {
  proc get (x : «from») -> «to»;
}

/-- The oracle procedure an adversary with an `Oracle` may call: `F.get`.  The hole of its
representation (`Module.Representable`, exception E2). -/
abbrev Oracle.holes : HoleSigs := .cons (procsig («from») -> «to») .empty

/-- `F.get` out of the oracle `F`. -/
noncomputable def Oracle.ext (F : Oracle «from» «to») : (Oracle.holes «from» «to»).Instantiation :=
  (Oracle.get «from» «to» F).procedure

/-- EasyCrypt's `module type AdvPreimage (F : Oracle) = { proc guess(h : to) : from }`. -/
abbrev AdvPreimage := Oracle «from» «to» →ₘ procmod («to») → «from»

open Classical in
module Preimage using (A : AdvPreimage «from» «to», F : RF «from» «to») {
  proc main (hash : «to») : Bool {
    var b : Bool, m : «from», hash' : «to»;
    _ <- call (Counter Counter_c) ();
    _ <- call (RF.init «from» «to»
      (Module.app (Bounder «from» «to» bound increase_counter bound_counter Counter_c
        Bounder_bounder) F)) ();
    m <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF.get «from» «to»
          (Module.app (Bounder «from» «to» bound increase_counter bound_counter Counter_c
            Bounder_bounder) F) })) ($hash);
    if (decide (increase_counter $Counter_c $m < bound_counter)) {
      hash' <- call F.get ($m);
      b <- decide ($hash = $hash');
    } else {
      b <- false;
    }
    return $b
  };
}

/-! ### The section `Preimage`, with `declare module A <: AdvPreimage {-RO, -Preimage}` (its local
modules in the namespace `Preimage`) -/

namespace Preimage

module FEL using (A : AdvPreimage «from» «to», F : RF «from» «to») {
  proc main (hash : «to») : «from» {
    var m : «from»;
    _ <- call (RF.init «from» «to»
      (Module.app (Bounder «from» «to» bound increase_counter bound_counter Counter_c
        Bounder_bounder) F)) ();
    m <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF.get «from» «to»
          (Module.app (Bounder «from» «to» bound increase_counter bound_counter Counter_c
            Bounder_bounder) F) })) ($hash);
    return $m
  };
}

open Classical in
module Preimage2 using (A : AdvPreimage «from» «to», F : RF «from» «to») {
  proc main (hash : «to») : Bool {
    var b : Bool, m : «from», hash' : «to»;
    m <- call (Module.app (FEL «from» «to» bound increase_counter bound_counter Counter_c
      Bounder_bounder) (Module.pair A F)) ($hash);
    if (decide (increase_counter $Counter_c $m < bound_counter)) {
      hash' <- call F.get ($m);
      b <- decide ($hash = $hash');
    } else {
      b <- false;
    }
    return $b
  };
}

end Preimage

/-- EC's `RO_is_preimage_resistant &m (h : to)`, for the section's `A`. -/
theorem RO_is_preimage_resistant
    (hax : Axioms «from» «to» sampleto bound increase_counter bound_counter)
    (A : AdvPreimage «from» «to») (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (_hAd : FVP.fvP A ≤ (RO_m.footprint ⊔ Counter_c.footprint ⊔ Bounder_bounder.footprint)ᶜ)
    (m : VariableAssignment) (h : «to») :
    (Procedure.Pr (Module.app (Preimage «from» «to» bound increase_counter bound_counter Counter_c
        Bounder_bounder) (Module.pair A (RO.asRF «from» «to» sampleto RO_m))).procedure h m
        (fun r _ => r = true) : ℝ) ≤
      ((bound + 1 : ℤ) : ℝ) * (sampleto.1 {h}).toReal := by
  sorry

/-- EasyCrypt's `module type AdvSecondPreimage (F : Oracle) = { proc guess(m : from) : from }`. -/
abbrev AdvSecondPreimage := Oracle «from» «to» →ₘ procmod («from») → «from»

open Classical in
module SecondPreimage using (A : AdvSecondPreimage «from» «to», F : RF «from» «to») {
  proc main (m1 : «from») : Bool {
    var b : Bool, m2 : «from», hash1 : «to», hash2 : «to»;
    _ <- call (RF.init «from» «to»
      (Module.app (Bounder «from» «to» bound increase_counter bound_counter Counter_c
        Bounder_bounder) F)) ();
    m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF.get «from» «to»
          (Module.app (Bounder «from» «to» bound increase_counter bound_counter Counter_c
            Bounder_bounder) F) })) ($m1);
    if (decide (increase_counter $Counter_c $m1 < bound_counter)) {
      Counter_c <- increase_counter $Counter_c $m1;
      hash1 <- call F.get ($m1);
      if (decide (increase_counter $Counter_c $m2 < bound_counter)) {
        Counter_c <- increase_counter $Counter_c $m2;
        hash2 <- call F.get ($m2);
        b <- decide ($hash1 = $hash2 ∧ $m1 ≠ $m2);
      } else {
        b <- false;
      }
    } else {
      b <- false;
    }
    return $b
  };
}

/-! ### The section `SecondPreimage`, with `declare module A <: AdvSecondPreimage {-Bounder, -RO,
-FRO}` (its local modules in the namespace `SecondPreimage`) -/

namespace SecondPreimage

module FEL using (A : AdvSecondPreimage «from» «to», F : RO.RO_T «from» «to») {
  proc main (m1 : «from») : «from» {
    var m2 : «from»;
    _ <- call (RF.init «from» «to»
      (Module.app (Bounder «from» «to» bound increase_counter bound_counter Counter_c
        Bounder_bounder) (RF.mk «from» «to»
          { init := PROM.FullRO.RO_T.init «from» «to» F,
            get := PROM.FullRO.RO_T.get «from» «to» F }))) ();
    _ <- call F.sample ($m1);
    m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF.get «from» «to»
          (Module.app (Bounder «from» «to» bound increase_counter bound_counter Counter_c
            Bounder_bounder) (RF.mk «from» «to»
              { init := PROM.FullRO.RO_T.init «from» «to» F,
                get := PROM.FullRO.RO_T.get «from» «to» F })) })) ($m1);
    return $m2
  };
}

/-! The local modules' variables `SecondPreimage2.m2`, `D1.m1` are the lens parameters
`SecondPreimage2_m2`, `D1_m1` (exception E6). -/
variable (SecondPreimage2_m2 : Lens «from» VariableAssignment)
variable (D1_m1 : Lens «from» VariableAssignment)

open Classical in
module SecondPreimage2 using (A : AdvSecondPreimage «from» «to», F : RO.RO_T «from» «to») {
  proc main (m1 : «from») : Bool {
    var b : Bool, hash1 : «to», hash2 : «to»;
    SecondPreimage2_m2 <- call (Module.app (FEL «from» «to» bound increase_counter bound_counter
      Counter_c Bounder_bounder) (Module.pair A F)) ($m1);
    if (decide (increase_counter $Counter_c $m1 < bound_counter)) {
      Counter_c <- increase_counter $Counter_c $m1;
      hash1 <- call F.get ($m1);
      if (decide (increase_counter $Counter_c $SecondPreimage2_m2 < bound_counter)) {
        Counter_c <- increase_counter $Counter_c $SecondPreimage2_m2;
        hash2 <- call F.get ($SecondPreimage2_m2);
        b <- decide ($hash1 = $hash2 ∧ $m1 ≠ $SecondPreimage2_m2);
      } else {
        b <- false;
      }
    } else {
      b <- false;
    }
    return $b
  };
}

-- EC's local `D1(A : AdvSecondPreimage, F : RO)`.  Its proof uses `D1(A)` as an
-- `RO_Distinguisher` (`RO_LRO_D (D1(A))`), so its `distinguish` takes that type's `unit`
module D1 using (A : AdvSecondPreimage «from» «to», F : RO.RO_T «from» «to») {
  proc distinguish (_x : Unit) : Bool {
    var b : Bool;
    b <- call (Module.app (SecondPreimage2 «from» «to» bound increase_counter bound_counter
      Counter_c Bounder_bounder SecondPreimage2_m2) (Module.pair A F)) ($D1_m1);
    return $b
  };
}

module SecondPreimage3 using (A : AdvSecondPreimage «from» «to», F : RO.RO_T «from» «to») {
  proc main (m1 : «from») : Bool {
    var b : Bool;
    SecondPreimage2_m2 <- (default : «from»);
    D1_m1 <- $m1;
    _ <- call (RF.init «from» «to»
      (Module.app (Bounder «from» «to» bound increase_counter bound_counter Counter_c
        Bounder_bounder) (RF.mk «from» «to»
          { init := PROM.FullRO.RO_T.init «from» «to» F,
            get := PROM.FullRO.RO_T.get «from» «to» F }))) ();
    b <- call (Module.app (D1 «from» «to» bound increase_counter bound_counter Counter_c
      Bounder_bounder SecondPreimage2_m2 D1_m1) (Module.pair A F)) (());
    return $b
  };
}

end SecondPreimage

/-- EC's `RO_is_second_preimage_resistant &m (mess1 : from)`, for the section's `A`. -/
theorem RO_is_second_preimage_resistant
    (hax : Axioms «from» «to» sampleto bound increase_counter bound_counter)
    (A : AdvSecondPreimage «from» «to») (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (_hAd : FVP.fvP A ≤ (Bounder_bounder.footprint ⊔ RO_m.footprint ⊔ FRO_m.footprint)ᶜ)
    (m : VariableAssignment) (mess1 : «from») :
    (Procedure.Pr (Module.app (SecondPreimage «from» «to» bound increase_counter bound_counter
        Counter_c Bounder_bounder) (Module.pair A (RO.asRF «from» «to» sampleto RO_m))).procedure
        mess1 m (fun r _ => r = true) : ℝ) ≤
      ((bound + 1 : ℤ) : ℝ) * (sampleto.1 {default}).toReal := by
  sorry

/-- EasyCrypt's `module type AdvCollision (F : Oracle) = { proc guess() : from * from }`. -/
abbrev AdvCollision := Oracle «from» «to» →ₘ procmod () → («from» × «from»)

open Classical in
module Collision using (A : AdvCollision «from» «to», F : RO.RO_T «from» «to») {
  proc main () : Bool {
    var b : Bool, m1 : «from», m2 : «from», hash1 : «to», hash2 : «to»;
    _ <- call (RF.init «from» «to»
      (Module.app (Bounder «from» «to» bound increase_counter bound_counter Counter_c
        Bounder_bounder) (RF.mk «from» «to»
          { init := PROM.FullRO.RO_T.init «from» «to» F,
            get := PROM.FullRO.RO_T.get «from» «to» F }))) ();
    m1, m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF.get «from» «to»
          (Module.app (Bounder «from» «to» bound increase_counter bound_counter Counter_c
            Bounder_bounder) (RF.mk «from» «to»
              { init := PROM.FullRO.RO_T.init «from» «to» F,
                get := PROM.FullRO.RO_T.get «from» «to» F })) })) ();
    if (decide (increase_counter $Counter_c $m1 < bound_counter)) {
      Counter_c <- increase_counter $Counter_c $m1;
      hash1 <- call F.get ($m1);
      if (decide (increase_counter $Counter_c $m2 < bound_counter)) {
        Counter_c <- increase_counter $Counter_c $m2;
        hash2 <- call F.get ($m2);
        b <- decide ($hash1 = $hash2 ∧ $m1 ≠ $m2);
      } else {
        b <- false;
      }
    } else {
      b <- false;
    }
    return $b
  };
}

/-! ### The section `Collision`, with `declare module A <: AdvCollision {-RO, -FRO, -Bounder}` (its
local modules in the namespace `Collision`) -/

namespace Collision

module FEL using (A : AdvCollision «from» «to», F : RO.RO_T «from» «to») {
  proc main () : («from» × «from») {
    var m1 : «from», m2 : «from»;
    _ <- call (RF.init «from» «to»
      (Module.app (Bounder «from» «to» bound increase_counter bound_counter Counter_c
        Bounder_bounder) (RF.mk «from» «to»
          { init := PROM.FullRO.RO_T.init «from» «to» F,
            get := PROM.FullRO.RO_T.get «from» «to» F }))) ();
    m1, m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF.get «from» «to»
          (Module.app (Bounder «from» «to» bound increase_counter bound_counter Counter_c
            Bounder_bounder) (RF.mk «from» «to»
              { init := PROM.FullRO.RO_T.init «from» «to» F,
                get := PROM.FullRO.RO_T.get «from» «to» F })) })) ();
    return ($m1, $m2)
  };
}

open Classical in
module Collision2 using (A : AdvCollision «from» «to», F : RO.RO_T «from» «to») {
  proc main () : Bool {
    var b : Bool, m1 : «from», m2 : «from», hash1 : «to», hash2 : «to»;
    m1, m2 <- call (Module.app (FEL «from» «to» bound increase_counter bound_counter Counter_c
      Bounder_bounder) (Module.pair A F)) ();
    if (decide (increase_counter $Counter_c $m1 < bound_counter)) {
      Counter_c <- increase_counter $Counter_c $m1;
      hash1 <- call F.get ($m1);
      if (decide (increase_counter $Counter_c $m2 < bound_counter)) {
        Counter_c <- increase_counter $Counter_c $m2;
        hash2 <- call F.get ($m2);
        b <- decide ($hash1 = $hash2 ∧ $m1 ≠ $m2);
      } else {
        b <- false;
      }
    } else {
      b <- false;
    }
    return $b
  };
}

end Collision

/-- The section's `op collision (m : ('a, 'b) fmap)`: two distinct keys with the same value. -/
def collision {α β : Type} [DecidableEq α] (m : FMap α β) : Prop :=
  ∃ m1 m2, m1 ≠ m2 ∧ FMap.dom m m1 ∧ FMap.dom m m2 ∧ FMap.get m m1 = FMap.get m m2

/-- EC's `RO_is_collision_resistant &m`, for the section's `A`. -/
theorem RO_is_collision_resistant
    (hax : Axioms «from» «to» sampleto bound increase_counter bound_counter)
    (A : AdvCollision «from» «to») (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (_hAd : FVP.fvP A ≤ (RO_m.footprint ⊔ FRO_m.footprint ⊔ Bounder_bounder.footprint)ᶜ)
    (m : VariableAssignment) :
    (Procedure.Pr (Module.app (Collision «from» «to» bound increase_counter bound_counter
        Counter_c Bounder_bounder) (Module.pair A (RO.RO «from» «to» sampleto RO_m))).procedure ()
        m (fun r _ => r = true) : ℝ) ≤
      ((bound * (bound - 1) + 2 : ℤ) : ℝ) / 2 * (sampleto.1 {default}).toReal := by
  sorry

end GaudisCrypt.SHA3.SecureRO
