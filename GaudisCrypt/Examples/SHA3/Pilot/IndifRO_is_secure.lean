import GaudisCrypt.Examples.SHA3.Pilot.SecureRO
import GaudisCrypt.Examples.SHA3.Pilot.Indifferentiability
import GaudisCrypt.Syntax.Clone
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECCallOneSided
import GaudisCrypt.Logic.ECCallAbstract

/-!
# A construction indifferentiable from a random oracle is secure — the EC-fidelity port
(EasyCrypt `proof/IndifRO_is_secure.ec`)

Collision, preimage and second-preimage resistance of `FM(C, P)` (a construction `C` over a
primitive `P`), from the resistance of the random oracle (`SecureRO`) and the indifferentiability
of `C(P)` from it, up to `bound`.

Translation (as the pilot `SecureRO`'s):
* the file's types and operators, and their axioms, are the class `Params block f_in f_out`
  (`SHA3Security`'s clone is an instance of it);
* `clone import SecureRO as SRO with …` and `clone import Indifferentiability as Indiff0 with …`
  are `clone` (`Syntax/Clone.lean`): the instances `SRO.params`, `Indiff0.params`, and the
  aliases `SRO.Bounder`, `SRO.RO_is_collision_resistant`, `Indiff0.GReal`, … opened;
* EC's `SRO.RO.RO` is the pilot's `RO` (the pilot's clone of `PROM.FullRO` is flattened into
  `RO`, `RO.LRO`, `FRO`, `RO.m`), so here `SRO.RO`;
* the procedure aliases of `FInit`, `GetF`, `SInit`, `FM`, `DColl` are wrapped in a call
  (exception E5; `RO`'s are its procedures themselves); `FInit` and `FM` are declared at `SRO`'s
  module type `RO_T` (EC's `RO`), their procedure `f`, which nothing calls, left out (EC types
  them structurally), `FM`'s `rem` before `sample` as the module type has them;
* EC's `C(P)` is `«C»(P)`: `C(` is Mathlib's notation for continuous maps.
-/

namespace GaudisCrypt.SHA3.Pilot.IndifRO_is_secure

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM

/-- The file's operators and their axioms: `sampleto`, `limit`, `bound`, `bound_counter`,
`increase_counter`.  The types are `outParam`s: a clone is an instance. -/
class Params (block f_in f_out : outParam Type) where
  sampleto : SubProbability f_out
  sampleto_ll : is_lossless sampleto
  sampleto_fu : is_funiform sampleto
  sampleto_full : is_full sampleto
  limit : ℤ
  limit_gt0 : 0 < limit
  bound : ℝ
  bound_counter : ℤ
  bound_counter_ge0 : 0 ≤ bound_counter
  increase_counter : ℤ → f_in → ℤ
  increase_counter_spec : ∀ c m, c ≤ increase_counter c m

export Params (sampleto sampleto_ll sampleto_fu sampleto_full limit limit_gt0 bound bound_counter
  bound_counter_ge0 increase_counter increase_counter_spec)

variable {block f_in f_out : Type} [Inhabited block] [DecidableEq f_in] [Inhabited f_in]
  [Inhabited f_out] [Params block f_in f_out]

clone import GaudisCrypt.SHA3.Pilot.SecureRO as SRO with
  type «from» <- f_in, type «to» <- f_out,
  op bound <- limit,
  op sampleto <- sampleto,
  op increase_counter <- increase_counter,
  op bound_counter <- bound_counter
  proof * by first
    | exact sampleto_fu | exact sampleto_ll | exact sampleto_full | exact limit_gt0
    | exact increase_counter_spec | exact bound_counter_ge0

clone import GaudisCrypt.SHA3.Pilot.Indifferentiability as Indiff0 with
  type p <- block, type f_in <- f_in, type f_out <- f_out

/-- EC's `module RO : FUNCTIONALITY = { proc init = SRO.RO.RO.init proc f = SRO.RO.RO.get }`: its
aliases are `SRO.RO`'s procedures themselves. -/
noncomputable abbrev RO : FUNCTIONALITY :=
  FUNCTIONALITY.mk { init := SRO.RO.init, f := SRO.RO.get }

module FInit using (F : DFUNCTIONALITY) : (PROM.FullRO.RO_T f_in f_out) {
  proc init () : Unit {
    return ()
  };
  proc get (x : f_in) : f_out {
    var y : f_out;
    y <- call F.f ($x);
    return $y
  };
  proc set (a : f_in, b : f_out) : Unit {
    return ()
  };
  proc rem (a : f_in) : Unit {
    return ()
  };
  proc sample (a : f_in) : Unit {
    return ()
  };
}

module GetF using (F : RO_T) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (x : f_in) : f_out {
    var y : f_out;
    y <- call F.get ($x);
    return $y
  };
}

module SInit using (F : RO_T, S : SIMULATOR) : (PROM.FullRO.RO_T f_in f_out) {
  proc init () : Unit {
    _ <- call S(GetF(F)).init ();
    _ <- call F.init ();
    return ()
  };
  proc get (x : f_in) : f_out {
    var y : f_out;
    y <- call F.get ($x);
    return $y
  };
  proc set (x : f_in, y : f_out) : Unit {
    _ <- call F.set ($x, $y);
    return ()
  };
  proc rem (x : f_in) : Unit {
    _ <- call F.rem ($x);
    return ()
  };
  proc sample (x : f_in) : Unit {
    _ <- call F.sample ($x);
    return ()
  };
}

module FM using (C : CONSTRUCTION, P : PRIMITIVE) : (PROM.FullRO.RO_T f_in f_out) {
  proc init () : Unit {
    _ <- call P.init ();
    _ <- call «C»(P).init ();
    return ()
  };
  proc get (x : f_in) : f_out {
    var y : f_out;
    y <- call «C»(P).f ($x);
    return $y
  };
  proc set (a : f_in, b : f_out) : Unit {
    return ()
  };
  proc rem (a : f_in) : Unit {
    return ()
  };
  proc sample (a : f_in) : Unit {
    return ()
  };
}

module DColl (A : AdvCollision) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    b <- call Collision(A, FInit(F)).main ();
    return $b
  };
}

/-! ### The section `Collision` -/

section Collision

declare module A <: AdvCollision {-Bounder, -SRO.RO, -SRO.FRO}

section
declare module «C» <: CONSTRUCTION {-A, -Bounder}
declare module P <: PRIMITIVE {-«C», -A, -Bounder}

set_option maxHeartbeats 2000000 in -- one declaration: EC's two `have`s, their `byequiv`s
/-- EC's `coll_resistant_if_indifferentiable (C <: CONSTRUCTION{-A, -Bounder})
(P <: PRIMITIVE{-C, -A, -Bounder}) &m`. -/
theorem coll_resistant_if_indifferentiable [Countable f_in] (m : VariableAssignment) :
    (∃ (S <: SIMULATOR {-Bounder, -A}),
      (∀ (F <: FUNCTIONALITY), islossless F.f → islossless S(F).init) ∧
      |Pr[ GReal(«C», P, DColl(A)).main () @ &m : §res ] -
        Pr[ GIdeal(RO, S, DColl(A)).main () @ &m : §res ]| ≤ bound) →
    Pr[ Collision(A, FM(«C», P)).main () @ &m : §res ] ≤
      bound + ((limit * (limit - 1) + 2 : ℤ) : ℝ) / 2 * mu1 sampleto default := by
  rintro ⟨S, _, S_ll, Hbound⟩
  calc Pr[ Collision(A, FM(«C», P)).main () @ &m : §res ]
      = Pr[ GReal(«C», P, DColl(A)).main () @ &m : §res ] := by
        byequiv; equiv_proc; stmt_inline*
        stmt_swap{1} [1..2] 2; sim
    _ ≤ _ := by
      have : Pr[ GIdeal(RO, S, DColl(A)).main () @ &m : §res ]
          ≤ ((limit * (limit - 1) + 2 : ℤ) : ℝ) / 2 * mu1 sampleto default := by
        calc _ = Pr[ Collision(A, SRO.RO).main () @ &m : §res ] := by
              byequiv; equiv_proc; stmt_inline*; sim
              equiv_call (_ : ={glob A, Bounder.bounder, Counter.c, SRO.RO.m})
              · equiv_proc; stmt_inline*; sim
              · stmt_wp
                equiv_call{1} (S_ll RO ?_) / glob A
                · sim
                · phoare_proc; phoare_auto
                  exact fun _ => (is_lossless_iff_expected _).mp sampleto_ll
          _ ≤ _ := RO_is_collision_resistant A m
      linarith [(abs_le.mp Hbound).1, (abs_le.mp Hbound).2]

end

end Collision

module_var DPre.h : f_out

module DPre (A : AdvPreimage) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    b <- call Preimage(A, FInit(F)).main ($DPre.h);
    return $b
  };
}

/-! ### The section `Preimage` -/

section Preimage

declare module A <: AdvPreimage {-Bounder, -SRO.RO, -SRO.FRO, -DPre}

section
declare module «C» <: CONSTRUCTION {-A, -Bounder, -DPre}
declare module P <: PRIMITIVE {-«C», -A, -Bounder, -DPre}

set_option maxHeartbeats 2000000 in -- one declaration: EC's two `have`s, their `byequiv`s
/-- EC's `preimage_resistant_if_indifferentiable (C <: CONSTRUCTION{-A, -Bounder, -DPre})
(P <: PRIMITIVE{-C, -A, -Bounder, -DPre}) &m hash`. -/
theorem preimage_resistant_if_indifferentiable [Countable f_in] (m : VariableAssignment)
    (hash : f_out) :
    DPre.h.get m = hash →
    (∃ (S <: SIMULATOR {-Bounder, -A, -DPre}),
      (∀ (F <: FUNCTIONALITY), islossless F.f → islossless S(F).init) ∧
      |Pr[ GReal(«C», P, DPre(A)).main () @ &m : §res ] -
        Pr[ GIdeal(RO, S, DPre(A)).main () @ &m : §res ]| ≤ bound) →
    Pr[ Preimage(A, FM(«C», P)).main (hash) @ &m : §res ] ≤
      bound + ((limit + 1 : ℤ) : ℝ) * mu1 sampleto hash := by
  rintro init_hash ⟨S, _, S_ll, Hbound⟩
  calc Pr[ Preimage(A, FM(«C», P)).main (hash) @ &m : §res ]
      = Pr[ GReal(«C», P, DPre(A)).main () @ &m : §res ] := by
        byequiv; equiv_proc; stmt_inline*; stmt_swap{2} [1..2] 4; sim
    _ ≤ _ := by
      have : Pr[ GIdeal(RO, S, DPre(A)).main () @ &m : §res ]
          ≤ ((limit + 1 : ℤ) : ℝ) * mu1 sampleto hash := by
        calc _ = Pr[ Preimage(A, SRO.RO).main (hash) @ &m : §res ] := by
              byequiv; equiv_proc; stmt_inline*; sim
              equiv_call (_ : ={glob A, Bounder.bounder, Counter.c, SRO.RO.m})
              · equiv_proc; stmt_inline*; sim
              · stmt_wp
                equiv_call{1} (S_ll RO ?_) / glob A, DPre.h
                · sim
                · phoare_proc; phoare_auto
                  exact fun _ => (is_lossless_iff_expected _).mp sampleto_ll

          _ ≤ _ := RO_is_preimage_resistant A m hash
      linarith [(abs_le.mp Hbound).1, (abs_le.mp Hbound).2]

end

end Preimage

module_var D2Pre.m2 : f_in

module D2Pre (A : AdvSecondPreimage) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    b <- call SecondPreimage(A, FInit(F)).main ($D2Pre.m2);
    return $b
  };
}

/-! ### The section `SecondPreimage` -/

section SecondPreimage

-- EC: `{-Bounder, -SRO.RO.RO, -SRO.RO.FRO, -D2Pre}`; `SRO`'s section-local modules' variables are
-- fresh in EC, here a restriction (as in `SecureRO`'s section)
declare module A <: AdvSecondPreimage
  {-Bounder, -SRO.RO, -SRO.FRO, -D2Pre, -SRO.SecondPreimage.SecondPreimage2, -SRO.SecondPreimage.D1}

section
declare module «C» <: CONSTRUCTION {-A, -Bounder, -D2Pre}
declare module P <: PRIMITIVE {-«C», -A, -Bounder, -D2Pre}

set_option maxHeartbeats 2000000 in -- one declaration: EC's two `have`s, their `byequiv`s
/-- EC's `second_preimage_resistant_if_indifferentiable (C <: CONSTRUCTION{-A, -Bounder, -D2Pre})
(P <: PRIMITIVE{-C, -A, -Bounder, -D2Pre}) &m mess`. -/
theorem second_preimage_resistant_if_indifferentiable [Countable f_in] [Countable f_out]
    (m : VariableAssignment) (mess : f_in) :
    D2Pre.m2.get m = mess →
    (∃ (S <: SIMULATOR {-Bounder, -A, -D2Pre}),
      (∀ (F <: FUNCTIONALITY), islossless F.f → islossless S(F).init) ∧
      |Pr[ GReal(«C», P, D2Pre(A)).main () @ &m : §res ] -
        Pr[ GIdeal(RO, S, D2Pre(A)).main () @ &m : §res ]| ≤ bound) →
    Pr[ SecondPreimage(A, FM(«C», P)).main (mess) @ &m : §res ] ≤
      bound + ((limit + 1 : ℤ) : ℝ) * mu1 sampleto default := by
  rintro init_mess ⟨S, _, S_ll, Hbound⟩
  calc Pr[ SecondPreimage(A, FM(«C», P)).main (mess) @ &m : §res ]
      = Pr[ GReal(«C», P, D2Pre(A)).main () @ &m : §res ] := by
        byequiv; equiv_proc; stmt_inline*; stmt_swap{2} [1..2] 3; sim
    _ ≤ _ := by
      have : Pr[ GIdeal(RO, S, D2Pre(A)).main () @ &m : §res ]
          ≤ ((limit + 1 : ℤ) : ℝ) * mu1 sampleto default := by
        calc _ = Pr[ SecondPreimage(A, SRO.RO).main (mess) @ &m : §res ] := by
              byequiv; equiv_proc; stmt_inline*; sim
              equiv_call (_ : ={glob A, Bounder.bounder, Counter.c, SRO.RO.m})
              · equiv_proc; stmt_inline*; sim
              · stmt_wp
                equiv_call{1} (S_ll RO ?_) / glob A, D2Pre.m2
                · sim
                · phoare_proc; phoare_auto
                  exact fun _ => (is_lossless_iff_expected _).mp sampleto_ll
          _ ≤ _ := RO_is_second_preimage_resistant A m mess
      linarith [(abs_le.mp Hbound).1, (abs_le.mp Hbound).2]

end

end SecondPreimage

end GaudisCrypt.SHA3.Pilot.IndifRO_is_secure
