import GaudisCrypt.Lib.EC.PROM
import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Logic.PHoareWp
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.ExpectationCall

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
    (_hAd : FVP.fvP A ≤ (Bounder_bounder.footprint ⊔ Counter_c.footprint ⊔ RO_m.footprint ⊔
      FRO_m.footprint)ᶜ)
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

/-! ### The lemmas of EC's `fel` in `RO_is_collision_resistant` (on `FMap` and the potential)

Not EasyCrypt statements: EC's proof settles these by `smt` (`fcardU`, `mem_set`, `mu_mem`); here
they are lemmas for the potential `collisionPotential`, whose expectation the oracle does not
increase (`collisionPotential_step`, the step of the failure event lemma). -/

section CollisionPotential

variable {α β : Type} [DecidableEq α]


theorem keys_set (m : FMap α β) (x : α) (r : β) :
    (FMap.set m x r).keys = insert x m.keys := by
  ext k; simp [FMap.set, Finmap.mem_keys, Finmap.mem_insert]

theorem dom_set_iff {m : FMap α β} {x k : α} {r : β} :
    FMap.dom (FMap.set m x r) k ↔ k = x ∨ FMap.dom m k := by
  simp only [FMap.dom, keys_set, Finset.mem_insert]

theorem collision_set_of_not_dom {m : FMap α β} {x : α} (hx : ¬ FMap.dom m x)
    (hc : collision m) (r : β) : collision (FMap.set m x r) := by
  obtain ⟨k₁, k₂, hne, hd₁, hd₂, heq⟩ := hc
  have h₁ : k₁ ≠ x := fun h => hx (h ▸ hd₁)
  have h₂ : k₂ ≠ x := fun h => hx (h ▸ hd₂)
  refine ⟨k₁, k₂, hne, ?_, ?_, ?_⟩
  · exact dom_set_iff.mpr (Or.inr hd₁)
  · exact dom_set_iff.mpr (Or.inr hd₂)
  · simp only [FMap.get, FMap.set, Finmap.lookup_insert_of_ne _ h₁, Finmap.lookup_insert_of_ne _ h₂]
    exact heq

theorem rng_of_collision_set {m : FMap α β} {x : α} (hx : ¬ FMap.dom m x)
    (hc : ¬ collision m) {r : β} (hcs : collision (FMap.set m x r)) :
    ∃ k, FMap.dom m k ∧ FMap.get m k = some r := by
  obtain ⟨k₁, k₂, hne, hd₁, hd₂, heq⟩ := hcs
  rw [dom_set_iff] at hd₁ hd₂
  simp only [FMap.get, FMap.set] at heq
  by_cases h₁ : k₁ = x
  · subst h₁
    have h₂ : k₂ ≠ k₁ := fun h => hne h.symm
    rw [Finmap.lookup_insert, Finmap.lookup_insert_of_ne _ h₂] at heq
    exact ⟨k₂, hd₂.resolve_left h₂, heq.symm⟩
  by_cases h₂ : k₂ = x
  · subst h₂
    rw [Finmap.lookup_insert, Finmap.lookup_insert_of_ne _ h₁] at heq
    exact ⟨k₁, hd₁.resolve_left h₁, heq⟩
  · exact absurd ⟨k₁, k₂, hne, hd₁.resolve_left h₁, hd₂.resolve_left h₂, by
      rwa [Finmap.lookup_insert_of_ne _ h₁, Finmap.lookup_insert_of_ne _ h₂] at heq⟩ hc

theorem card_fdom_set {m : FMap α β} {x : α} (hx : ¬ FMap.dom m x) (r : β) :
    (FMap.fdom (FMap.set m x r)).card = (FMap.fdom m).card + 1 := by
  simp only [FMap.fdom, keys_set]
  exact Finset.card_insert_of_notMem hx

theorem not_collision_empty : ¬ collision (FMap.empty : FMap α β) := by
  rintro ⟨k₁, -, -, hd, -⟩
  simp [FMap.dom, FMap.empty] at hd

open Classical in
/-- A uniform sample hits the values of `m` with probability at most `|dom m| · μ`. -/
theorem expected_rng_le {α β : Type} [DecidableEq α] [Inhabited β] {d : SubProbability β}
    (hfu : is_funiform d) (m : FMap α β) :
    d.expected (fun a => indicatorE (∃ k, FMap.dom m k ∧ FMap.get m k = some a)) ≤
      (FMap.fdom m).card * d.1 {default} := by
  let S : Finset β := (FMap.fdom m).image fun k => (FMap.get m k).getD default
  have hS : ∀ a, (∃ k, FMap.dom m k ∧ FMap.get m k = some a) → a ∈ S := by
    rintro a ⟨k, hk, hget⟩
    exact Finset.mem_image.mpr ⟨k, hk, by simp [hget]⟩
  rw [SubProbability.expected_eq_tsum]
  calc ∑' a, indicatorE (∃ k, FMap.dom m k ∧ FMap.get m k = some a) * d.1 {a}
      ≤ ∑' a, if a ∈ S then d.1 {a} else 0 := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases h : ∃ k, FMap.dom m k ∧ FMap.get m k = some a
        · simp [indicatorE, h, hS a h]
        · simp [indicatorE, h]
    _ = ∑ a ∈ S, d.1 {a} := by
        rw [tsum_eq_sum (s := S) (fun a ha => by simp [ha])]
        exact Finset.sum_congr rfl fun a ha => by simp [ha]
    _ = S.card * d.1 {default} := by
        rw [Finset.sum_congr rfl fun a _ => hfu a default, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (FMap.fdom m).card * d.1 {default} := by
        gcongr
        exact_mod_cast Finset.card_image_le

theorem expected_mono' {γ : Type} {μ : SubProbability γ} {f g : γ → ENNReal}
    (h : ∀ a, f a ≤ g a) : μ.expected f ≤ μ.expected g := by
  rw [SubProbability.expected_eq_tsum, SubProbability.expected_eq_tsum]
  exact ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

theorem expected_const_le' {γ : Type} (μ : SubProbability γ) (c : ENNReal) :
    μ.expected (fun _ => c) ≤ c := by
  letI : MeasurableSpace γ := ⊤
  change ∫⁻ _, c ∂μ.1 ≤ c
  rw [MeasureTheory.lintegral_const]
  calc c * μ.1 Set.univ ≤ c * 1 := by gcongr; exact μ.2.1
    _ = c := mul_one c


open Classical in
/-- The potential of EC's `fel` in `RO_is_collision_resistant`: `1` once `m` has a collision, the
bound still to pay for the queries from `b` on while `|dom m| ≤ b`, and `⊤` otherwise. -/
noncomputable def collisionPotential (bound : ℤ) (μ : ENNReal) (s : ℤ × ℤ × FMap α β) : ENNReal :=
  if collision s.2.2 then 1
  else if 0 ≤ s.1 ∧ ((FMap.fdom s.2.2).card : ℤ) ≤ s.1 then
    ∑ i ∈ Finset.Ico s.1.toNat bound.toNat, (i : ENNReal) * μ
  else ⊤

open Classical in
/-- **The step of EC's `fel`**: one query of `Bounder(RO).get` does not increase the potential in
expectation. -/
theorem collisionPotential_step [Inhabited β] {d : SubProbability β} (hfu : is_funiform d)
    (bound : ℤ) (b c c' : ℤ) (m : FMap α β) (x : α) (Q : Prop) [Decidable Q] :
    (if b < bound then
      (if Q then d.expected (fun a => if ¬ FMap.dom m x then
          collisionPotential bound (d.1 {default}) (b + 1, c', FMap.set m x a)
        else collisionPotential bound (d.1 {default}) (b + 1, c', m))
      else collisionPotential bound (d.1 {default}) (b + 1, c, m))
    else collisionPotential bound (d.1 {default}) (b, c, m)) ≤
      collisionPotential bound (d.1 {default}) (b, c, m) := by
  set μ := d.1 {default}
  by_cases hb : b < bound
  swap
  · simp [hb]
  rw [if_pos hb]
  by_cases hcol : collision m
  · have h1 : ∀ c₀, collisionPotential bound μ (b + 1, c₀, m) = 1 := fun _ => by
      simp [collisionPotential, hcol]
    have hφ : collisionPotential bound μ (b, c, m) = 1 := by simp [collisionPotential, hcol]
    rw [hφ]
    by_cases hQ : Q
    · simp only [hQ, if_true]
      by_cases hx : FMap.dom m x
      · simp only [hx, not_true_eq_false, if_false, h1]
        exact expected_const_le' d 1
      · simp only [hx, not_false_eq_true, if_true]
        refine (expected_mono' fun a => ?_).trans (expected_const_le' d 1)
        simp [collisionPotential, collision_set_of_not_dom hx hcol]
    · simp only [hQ, if_false, h1, le_refl]
  by_cases hinv : 0 ≤ b ∧ ((FMap.fdom m).card : ℤ) ≤ b
  swap
  · simp [collisionPotential, hcol, hinv]
  have hinv' : 0 ≤ b + 1 ∧ ((FMap.fdom m).card : ℤ) ≤ b + 1 := ⟨by omega, by omega⟩
  set T := ∑ i ∈ Finset.Ico (b + 1).toNat bound.toNat, (i : ENNReal) * μ
  have hφ : collisionPotential bound μ (b, c, m) = (b.toNat : ENNReal) * μ + T := by
    simp only [collisionPotential, hcol, hinv, if_false, and_self, if_true]
    rw [Finset.sum_eq_sum_Ico_succ_bot (show b.toNat < bound.toNat by omega),
      show b.toNat + 1 = (b + 1).toNat by omega]
  have hT : ∀ c₀, collisionPotential bound μ (b + 1, c₀, m) = T := fun _ => by
    simp only [collisionPotential, hcol, hinv', if_false, and_self, if_true]
    rfl
  rw [hφ]
  by_cases hQ : Q
  · simp only [hQ, if_true]
    by_cases hx : FMap.dom m x
    · simp only [hx, not_true_eq_false, if_false, hT]
      exact (expected_const_le' d T).trans le_add_self
    · simp only [hx, not_false_eq_true, if_true]
      calc d.expected (fun a => collisionPotential bound μ (b + 1, c', FMap.set m x a))
          ≤ d.expected (fun a =>
              indicatorE (∃ k, FMap.dom m k ∧ FMap.get m k = some a) + T) := by
            refine expected_mono' fun a => ?_
            by_cases hca : collision (FMap.set m x a)
            · simp [collisionPotential, hca, indicatorE_of (rng_of_collision_set hx hcol hca)]
            · have hinv'' : 0 ≤ b + 1 ∧ ((FMap.fdom (FMap.set m x a)).card : ℤ) ≤ b + 1 := by
                rw [card_fdom_set hx]; push_cast; omega
              simp [collisionPotential, hca, hinv'', T]
        _ = d.expected (fun a => indicatorE (∃ k, FMap.dom m k ∧ FMap.get m k = some a)) +
              d.expected (fun _ => T) := SubProbability.expected_add _ _ _
        _ ≤ (FMap.fdom m).card * μ + T := add_le_add (expected_rng_le hfu m) (expected_const_le' d T)
        _ ≤ (b.toNat : ENNReal) * μ + T := by
            gcongr
            exact_mod_cast (show (FMap.fdom m).card ≤ b.toNat by omega)
  · simp only [hQ, if_false, hT]; exact le_add_self

end CollisionPotential

/-- The oracle premise of EC's `fel` in `RO_is_collision_resistant`: a query of `Bounder(RO).get`
does not increase the potential `collisionPotential` of `(Bounder.bounder, Counter.c, RO.m)` in
expectation (`collisionPotential_step`). -/
theorem Bounder_RO_get_potential [Lens.Disjoint Bounder_bounder Counter_c] [Lens.Disjoint Bounder_bounder RO_m]
    [Lens.Disjoint Counter_c RO_m] (hfu : is_funiform sampleto) :
    phoareProc (fun _ _ => True)
      (RF.get «from» «to» (Module.app (Bounder «from» «to» bound increase_counter bound_counter
        Counter_c Bounder_bounder) (RF.mk «from» «to»
          { init := PROM.FullRO.RO_T.init «from» «to» (RO.RO «from» «to» sampleto RO_m),
            get := PROM.FullRO.RO_T.get «from» «to» (RO.RO «from» «to» sampleto RO_m) }))).procedure
      (fun _ g => collisionPotential bound (sampleto.1 {default})
        ((Lens.pair Bounder_bounder (Lens.pair Counter_c RO_m)).get g))
      (· ≤ ·)
      (fun _ g => collisionPotential bound (sampleto.1 {default})
        ((Lens.pair Bounder_bounder (Lens.pair Counter_c RO_m)).get g)) := by
  have := (inferInstance : Lens.Disjoint Counter_c RO_m).symm
  have := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
  have := (inferInstance : Lens.Disjoint Bounder_bounder Counter_c).symm
  phoare_proc_to_stmt
  repeat phoare_inline 0
  intro σ _
  simp only [Stmt.ewp_seq, Stmt.ewp_ifThenElse, Stmt.ewp_assign, Stmt.ewp_sample, Stmt.ewp_skip]
  simp_reads
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  exact collisionPotential_step hfu bound _ _ _ _ _ _

/-- EC's `RO_is_collision_resistant &m`, for the section's `A`. -/
theorem RO_is_collision_resistant
    (hax : Axioms «from» «to» sampleto bound increase_counter bound_counter)
    (A : AdvCollision «from» «to») (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (_hAd : FVP.fvP A ≤ (RO_m.footprint ⊔ FRO_m.footprint ⊔ Bounder_bounder.footprint ⊔
      Counter_c.footprint)ᶜ)
    (m : VariableAssignment) :
    (Procedure.Pr (Module.app (Collision «from» «to» bound increase_counter bound_counter
        Counter_c Bounder_bounder) (Module.pair A (RO.RO «from» «to» sampleto RO_m))).procedure ()
        m (fun r _ => r = true) : ℝ) ≤
      ((bound * (bound - 1) + 2 : ℤ) : ℝ) / 2 * (sampleto.1 {default}).toReal := by
  sorry

end GaudisCrypt.SHA3.SecureRO
