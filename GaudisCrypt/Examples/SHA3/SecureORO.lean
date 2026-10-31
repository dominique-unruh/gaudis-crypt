import GaudisCrypt.Lib.EC.PROM
import GaudisCrypt.Lib.EC.Distr

/-!
# Random oracles with failing queries are preimage, second-preimage and collision resistant
(EasyCrypt `proof/SecureORO.eca`)

`SecureRO` for oracles returning `option`s: `Bounder` answers `None` once its `bound` queries are
spent, and the games compare `Some` hashes.

Translation notes (see `notes/SHA3/README.md` and `SecureRO.lean`, whose translation this follows):
* EasyCrypt's module type `RF` and module `RF` share a name; the module type is `RF_T`
  (exception E3).
* `RF(R)` (`proc init = R.init`, `proc sample = R.sample`) and `Bounder(F)` (`proc sample =
  F.sample`) are used as functors, so their aliased procedures call the aliased ones (exception E5).
* The module variables (`Bounder.bounder`, the clone's `RO.m`, `FRO.m`, and the sections' local
  `Preimage2.hash`, `SecondPreimage2.m2`, `D1.m1`) are lens parameters (exception E6 for the local
  ones).
-/

-- the clone `RO` contains the module `RO` (`RO.RO`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.SecureORO

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM

variable («from» «to» : Type) [DecidableEq «from»] [Inhabited «from»] [Inhabited «to»]
variable (sampleto : SubProbability «to»)
variable (bound : ℤ)
variable (increase_counter : ℤ → «from» → ℤ)

/-- EasyCrypt's axioms on the theory's operators (a hypothesis, realized by a clone). -/
structure Axioms : Prop where
  bound_ge0 : 0 ≤ bound
  sampleto_ll : is_lossless sampleto
  sampleto_full : is_full sampleto
  sampleto_fu : is_funiform sampleto
  increase_counter_spec : ∀ c m, c ≤ increase_counter c m

/-! `clone import PROM.FullRO as RO with type in_t <- from, type out_t <- to,
op dout _ <- sampleto, type d_in_t <- unit, type d_out_t <- bool`; its module variables `RO.m`,
`FRO.m` are the lens parameters `RO_m`, `FRO_m`. -/

-- one binder each: a `module` takes a whole binder group when it mentions one of its names
variable (RO_m : Lens (FMap «from» «to») VariableAssignment)
variable (FRO_m : Lens (FMap «from» («to» × flag)) VariableAssignment)

namespace RO
/-- EasyCrypt's module type `RO` of the clone. -/
abbrev RO_T := PROM.FullRO.RO_T «from» «to»
noncomputable abbrev RO := PROM.FullRO.RO.asRO «from» «to» (fun _ => sampleto) RO_m
noncomputable abbrev LRO := PROM.FullRO.LRO «from» «to» (fun _ => sampleto) RO_m
end RO

-- EC's `module type RF` (renamed: exception E3)
moduletype RF_T {
  proc init () -> Unit;
  proc get (x : «from») -> (Option «to»);
  proc sample (x : «from») -> Unit;
}

-- EC's `module RF (R : RO) : RF`; its aliases `proc init = R.init`, `proc sample = R.sample` are
-- wrapped in a call, as `RF` is used as a functor (exception E5)
module RF using (R : RO.RO_T «from» «to») : (RF_T «from» «to») {
  proc init () : Unit {
    _ <- call R.init ();
    return ()
  };
  proc get (x : «from») : (Option «to») {
    var y : «to»;
    y <- call R.get ($x);
    return some $y
  };
  proc sample (x : «from») : Unit {
    _ <- call R.sample ($x);
    return ()
  };
}

/-! `Bounder`'s module variable `bounder` is the lens parameter `Bounder_bounder`. -/
variable (Bounder_bounder : Lens ℤ VariableAssignment)

-- `proc sample = F.sample` is wrapped in a call, as `Bounder` is used as a functor (exception E5)
module Bounder using (F : RF_T «from» «to») : (RF_T «from» «to») {
  proc init () : Unit {
    Bounder_bounder <- 0;
    _ <- call F.init ();
    return ()
  };
  proc get (x : «from») : (Option «to») {
    var y : Option «to»;
    y <- (none : Option «to»);
    if (decide ($Bounder_bounder < bound)) {
      Bounder_bounder <- $Bounder_bounder + 1;
      y <- call F.get ($x);
    }
    return $y
  };
  proc sample (x : «from») : Unit {
    _ <- call F.sample ($x);
    return ()
  };
}

-- EasyCrypt's `module type Oracle = { proc get(x : from) : to option {} }`
moduletype Oracle {
  proc get (x : «from») -> (Option «to»);
}

/-- The oracle procedure an adversary with an `Oracle` may call: `F.get` (E2). -/
abbrev Oracle.holes : HoleSigs := .cons (procsig («from») -> (Option «to»)) .empty

/-- `F.get` out of the oracle `F`. -/
noncomputable def Oracle.ext (F : Oracle «from» «to») : (Oracle.holes «from» «to»).Instantiation :=
  (Oracle.get «from» «to» F).procedure

/-- EasyCrypt's `module type AdvPreimage (F : Oracle) = { proc guess(h : to) : from }`. -/
abbrev AdvPreimage := Oracle «from» «to» →ₘ procmod («to») → «from»

open Classical in
module Preimage using (A : AdvPreimage «from» «to», F : RF_T «from» «to») {
  proc main () : Bool {
    var m : «from», hash : «to», hash' : Option «to»;
    hash <$ sampleto;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ();
    m <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to»
          (Module.app (Bounder «from» «to» bound Bounder_bounder) F) })) ($hash);
    hash' <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m);
    return decide ($hash' = some $hash)
  };
}

/-! ### The section `Preimage`, with `declare module A <: AdvPreimage {-RO, -Preimage}` (its local
modules in the namespace `Preimage`) -/

namespace Preimage

module FEL using (A : AdvPreimage «from» «to», F : RF_T «from» «to») {
  proc main (hash : «to») : «from» {
    var m : «from»;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ();
    m <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to»
          (Module.app (Bounder «from» «to» bound Bounder_bounder) F) })) ($hash);
    return $m
  };
}

/-! The local module's variable `Preimage2.hash` is the lens parameter `Preimage2_hash` (E6). -/
variable (Preimage2_hash : Lens «to» VariableAssignment)

open Classical in
module Preimage2 using (A : AdvPreimage «from» «to», F : RF_T «from» «to») {
  proc main () : Bool {
    var m : «from», hash' : Option «to»;
    Preimage2_hash <$ sampleto;
    m <- call (Module.app (FEL «from» «to» bound Bounder_bounder) (Module.pair A F))
      ($Preimage2_hash);
    hash' <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m);
    return decide ($hash' = some $Preimage2_hash)
  };
}

end Preimage

/-- EC's `RO_is_preimage_resistant &m`, for the section's `A`. -/
theorem RO_is_preimage_resistant (hax : Axioms «from» «to» sampleto bound increase_counter)
    (A : AdvPreimage «from» «to») (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (_hAd : FVP.fvP A ≤ (RO_m.footprint ⊔ Bounder_bounder.footprint)ᶜ) (m : VariableAssignment) :
    (Procedure.Pr (Module.app (Preimage «from» «to» sampleto bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
        () m (fun r _ => r = true) : ℝ) ≤
      ((bound + 1 : ℤ) : ℝ) * (sampleto.1 {default}).toReal := by
  sorry

/-- EasyCrypt's `module type AdvSecondPreimage (F : Oracle) = { proc guess(m : from) : from }`. -/
abbrev AdvSecondPreimage := Oracle «from» «to» →ₘ procmod («from») → «from»

open Classical in
module SecondPreimage using (A : AdvSecondPreimage «from» «to», F : RF_T «from» «to») {
  proc main (m1 : «from») : Bool {
    var m2 : «from», hash1 : Option «to», hash2 : Option «to»;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ();
    m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to»
          (Module.app (Bounder «from» «to» bound Bounder_bounder) F) })) ($m1);
    hash1 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m1);
    hash2 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

/-! ### The section `SecondPreimage`, with `declare module A <: AdvSecondPreimage {-Bounder, -RO,
-FRO}` (its local modules in the namespace `SecondPreimage`) -/

namespace SecondPreimage

module FEL using (A : AdvSecondPreimage «from» «to», F : RF_T «from» «to») {
  proc main (m1 : «from») : «from» {
    var m2 : «from»;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ();
    _ <- call (RF_T.sample «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m1);
    m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to»
          (Module.app (Bounder «from» «to» bound Bounder_bounder) F) })) ($m1);
    return $m2
  };
}

/-! The local modules' variables `SecondPreimage2.m2`, `D1.m1` are the lens parameters
`SecondPreimage2_m2`, `D1_m1` (exception E6). -/
variable (SecondPreimage2_m2 : Lens «from» VariableAssignment)
variable (D1_m1 : Lens «from» VariableAssignment)

open Classical in
module SecondPreimage2 using (A : AdvSecondPreimage «from» «to», F : RF_T «from» «to») {
  proc main (m1 : «from») : Bool {
    var hash1 : Option «to», hash2 : Option «to»;
    SecondPreimage2_m2 <- call (Module.app (FEL «from» «to» bound Bounder_bounder)
      (Module.pair A F)) ($m1);
    hash1 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m1);
    hash2 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($SecondPreimage2_m2);
    return decide ($m1 ≠ $SecondPreimage2_m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

-- EC's local `D1(A : AdvSecondPreimage, F : RO)`.  Its proof uses `D1(A)` as an
-- `RO_Distinguisher`, so its `distinguish` takes that type's `unit`
module D1 using (A : AdvSecondPreimage «from» «to», F : RO.RO_T «from» «to») {
  proc distinguish (_x : Unit) : Bool {
    var b : Bool;
    b <- call (Module.app (SecondPreimage2 «from» «to» bound Bounder_bounder SecondPreimage2_m2)
      (Module.pair A (Module.app (RF «from» «to») F))) ($D1_m1);
    return $b
  };
}

module SecondPreimage3 using (A : AdvSecondPreimage «from» «to», F : RO.RO_T «from» «to») {
  proc main (m1 : «from») : Bool {
    var b : Bool;
    SecondPreimage2_m2 <- (default : «from»);
    D1_m1 <- $m1;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder)
        (Module.app (RF «from» «to») F))) ();
    b <- call (Module.app (D1 «from» «to» bound Bounder_bounder SecondPreimage2_m2 D1_m1)
      (Module.pair A F)) (());
    return $b
  };
}

end SecondPreimage

/-- EC's `RO_is_second_preimage_resistant &m (mess1 : from)`, for the section's `A`. -/
theorem RO_is_second_preimage_resistant
    (hax : Axioms «from» «to» sampleto bound increase_counter)
    (A : AdvSecondPreimage «from» «to») (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (_hAd : FVP.fvP A ≤ (Bounder_bounder.footprint ⊔ RO_m.footprint ⊔ FRO_m.footprint)ᶜ)
    (m : VariableAssignment) (mess1 : «from») :
    (Procedure.Pr (Module.app (SecondPreimage «from» «to» bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
        mess1 m (fun r _ => r = true) : ℝ) ≤
      ((bound + 1 : ℤ) : ℝ) * (sampleto.1 {default}).toReal := by
  sorry

/-- EasyCrypt's `module type AdvCollision (F : Oracle) = { proc guess() : from * from }`. -/
abbrev AdvCollision := Oracle «from» «to» →ₘ procmod () → («from» × «from»)

open Classical in
module Collision using (A : AdvCollision «from» «to», F : RF_T «from» «to») {
  proc main () : Bool {
    var m1 : «from», m2 : «from», hash1 : Option «to», hash2 : Option «to»;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ();
    m1, m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to»
          (Module.app (Bounder «from» «to» bound Bounder_bounder) F) })) ();
    hash1 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m1);
    hash2 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

/-! ### The section `Collision`, with `declare module A <: AdvCollision {-RO, -FRO, -Bounder}` (its
local modules in the namespace `Collision`) -/

namespace Collision

module FEL using (A : AdvCollision «from» «to», F : RF_T «from» «to») {
  proc main () : («from» × «from») {
    var m1 : «from», m2 : «from»;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ();
    m1, m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to»
          (Module.app (Bounder «from» «to» bound Bounder_bounder) F) })) ();
    return ($m1, $m2)
  };
}

open Classical in
module Collision2 using (A : AdvCollision «from» «to», F : RF_T «from» «to») {
  proc main () : Bool {
    var m1 : «from», m2 : «from», hash1 : Option «to», hash2 : Option «to»;
    m1, m2 <- call (Module.app (FEL «from» «to» bound Bounder_bounder) (Module.pair A F)) ();
    hash1 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m1);
    hash2 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

end Collision

/-- The section's `op collision (m : ('a, 'b) fmap)`: two distinct keys with the same value. -/
def collision {α β : Type} [DecidableEq α] (m : FMap α β) : Prop :=
  ∃ m1 m2, m1 ≠ m2 ∧ FMap.dom m m1 ∧ FMap.dom m m2 ∧ FMap.get m m1 = FMap.get m m2

/-- EC's `RO_is_collision_resistant &m`, for the section's `A`. -/
theorem RO_is_collision_resistant (hax : Axioms «from» «to» sampleto bound increase_counter)
    (A : AdvCollision «from» «to») (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (_hAd : FVP.fvP A ≤ (RO_m.footprint ⊔ FRO_m.footprint ⊔ Bounder_bounder.footprint)ᶜ)
    (m : VariableAssignment) :
    (Procedure.Pr (Module.app (Collision «from» «to» bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
        () m (fun r _ => r = true) : ℝ) ≤
      ((bound * (bound - 1) + 2 : ℤ) : ℝ) / 2 * (sampleto.1 {default}).toReal := by
  sorry

end GaudisCrypt.SHA3.SecureORO
