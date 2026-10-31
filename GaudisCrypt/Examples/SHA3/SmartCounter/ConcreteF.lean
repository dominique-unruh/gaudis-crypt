import GaudisCrypt.Examples.SHA3.SmartCounter.SLCommon
import GaudisCrypt.Lib.EC.Strong_RP_RF

/-!
# From the permutation to a random function (EasyCrypt `proof/smart_counter/ConcreteF.eca`)

The real game with the ideal permutation is close to the same game with `PF`, a random function
with an inverse, up to the PRP/PRF switching bound (`Real_Concrete`).

Translation notes (see `notes/SHA3/README.md`):
* The section's `declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo}` and `declare axiom
  D_ll` are hypotheses of the lemmas.  So are the local modules' parameters.
* `local clone import Strong_RP_RF as Switching with type D <- state, op uD <- dstate,
  type K <- unit, op dK <- dunit tt, op q <- max_size` is the namespace `Switching`, and its
  realized axioms `ge0_q`, `uD_uf_fu` are lemmas.
* EasyCrypt checks this file only up to an anomaly at line 418 (inside the proof of
  `Real_Concrete`); see `notes/SHA3/README.md`.
-/

namespace GaudisCrypt.SHA3.ConcreteF

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.SLCommon
open GaudisCrypt.SHA3.SLCommon.Prefix

-- `state` also names the RO library's globals (`Lib/RO/Basic.lean`, at the root), and
-- `PRIMITIVE` also `Common`'s (the `PRP` clone); here they are `SLCommon`'s, which EasyCrypt's
-- `clone include Indifferentiability` puts in scope last
export GaudisCrypt.SHA3.SLCommon (state PRIMITIVE)

variable [SLCommon.Params]

/-- EC's `PF.m`. -/
global_var PF.m : FMap state state
/-- EC's `PF.mi`. -/
global_var PF.mi : FMap state state

module PF : PRIMITIVE {
  proc init () : Unit {
    PF.m <- (FMap.empty : FMap state state);
    PF.mi <- (FMap.empty : FMap state state);
    return ()
  };
  proc f (x : state) : state {
    var y1 : block, y2 : capacity;
    if (!(decide (FMap.dom ($PF.m : FMap state state) $x))) {
      y1 <$ bdistr;
      y2 <$ cdistr;
      PF.m <- FMap.set $PF.m $x ($y1, $y2);
      PF.mi <- FMap.set $PF.mi ($y1, $y2) $x;
    }
    return oget (FMap.get ($PF.m : FMap state state) $x)
  };
  proc fi (x : state) : state {
    var y1 : block, y2 : capacity;
    if (!(decide (FMap.dom ($PF.mi : FMap state state) $x))) {
      y1 <$ bdistr;
      y2 <$ cdistr;
      PF.mi <- FMap.set $PF.mi $x ($y1, $y2);
      PF.m <- FMap.set $PF.m ($y1, $y2) $x;
    }
    return oget (FMap.get ($PF.mi : FMap state state) $x)
  };
}

/-- `module CF(D : DISTINGUISHER) = Indif(SqueezelessSponge(PF), PF, D)`. -/
noncomputable def CF (D : DISTINGUISHER) : procmod () → Bool :=
  Module.app Indif (Module.pair
    (Module.app SqueezelessSponge (Indifferentiability.PRIMITIVE.view state (List block) block PF))
    (Module.pair PF D))

/-! ## The section -/

section

variable (D : DISTINGUISHER)

/-- `local module GReal' = Indif(FC(SqueezelessSponge(Perm)), PC(Perm), D)`. -/
noncomputable def GReal' : procmod () → Bool :=
  Module.app Indif (Module.pair
    (Module.app FC (Module.app SqueezelessSponge
      (Indifferentiability.PRIMITIVE.view state (List block) block Perm)))
    (Module.pair (Module.app PC Perm) D))

/-! `local clone import Strong_RP_RF as Switching with type D <- state, op uD <- dstate,
type K <- unit, op dK <- (MUnit.dunit<:unit> tt), op q <- max_size` -/

namespace Switching
/-- The clone's module variables. -/
global_var PRPi.m : FMap state state
global_var PRPi.mi : FMap state state
global_var ARP.coll : Bool
global_var ARP.m : FMap state state
global_var ARP.mi : FMap state state
global_var DBounder.FBounder.c : ℤ
noncomputable abbrev PRPi.PRPi := Strong_RP_RF.PRPi.PRPi state dstate PRPi.m PRPi.mi
noncomputable abbrev ARP := Strong_RP_RF.ARP state dstate ARP.coll ARP.m ARP.mi
noncomputable abbrev DBounder := Strong_RP_RF.DBounder state max_size DBounder.FBounder.c
abbrev PRPSec.PRP := EC.PRP.StrongPRP.PRP state
abbrev PRPSec.SPRP_Oracles := EC.PRP.StrongPRP.SPRP_Oracles state
abbrev PRPSec.Distinguisher := EC.PRP.StrongPRP.Distinguisher state
noncomputable abbrev PRPSec.IND := EC.PRP.StrongPRP.IND state

/-- `realize ge0_q`. -/
theorem ge0_q : 0 ≤ (max_size : ℤ) := max_ge0

/-- `realize uD_uf_fu`: `dstate` is uniform, lossless and full. -/
theorem uD_uf_fu : dstate.1 Set.univ = 1 ∧ ∀ x y, dstate.1 {x} = dstate.1 {y} := by
  sorry
end Switching

theorem size_behead {α : Type} (l : List α) : l ≠ [] → size (behead l) = size l - 1 := by
  sorry

-- `local module (D' : PRPSec.Distinguisher) (P' : PRPSec.SPRP_Oracles)`, with `D` a Lean
-- parameter
set_option linter.gaudisCrypt.using false in
module D' (D : DISTINGUISHER) using (P' : Switching.PRPSec.SPRP_Oracles) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call Redo.init ();
    b <- call (Module.app (DRestr D) (Module.pair
      (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
        { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
            (Module.app SqueezelessSponge P') })
      P')) ();
    return $b
  };
}

/-- `local lemma DoubleBounding (P <: PRPSec.PRP {-D, -C, -DBounder, -Redo})`. -/
theorem DoubleBounding (P : Switching.PRPSec.PRP)
    (_hP : FVP.fvP P ≤ (FVP.fvP D ⊔ C.footprint ⊔ (Switching.DBounder.FBounder.c).footprint ⊔
      (Redo.prefixes).footprint)ᶜ)
    (m : VariableAssignment) :
    Procedure.Pr (Module.app Switching.PRPSec.IND (Module.pair P (D' D))).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (Module.app Switching.PRPSec.IND
        (Module.pair P (Switching.DBounder (D' D)))).procedure () m (fun r _ => r = true) := by
  sorry

/-- `local clone import ProdSampling with type t1 <- block, type t2 <- capacity`. -/
noncomputable abbrev S := DProd.ProdSampling.S block capacity

/-- EC's `Real_Concrete`, for `declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo}` with
the axiom `D_ll`.  `mu dstate (pred1 witness)` is the probability of `default`. -/
theorem Real_Concrete (hD : Module.Representable D distExt)
    (_hDd : FVP.fvP D ≤ ((Perm.m).footprint ⊔
      (Perm.mi).footprint ⊔ C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔
      (Redo.prefixes).footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D)ᶜ →
      FVP.fvP P ≤ (FVP.fvP D)ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (m : VariableAssignment) :
    (Procedure.Pr (GReal D).procedure () m (fun r g => r = true ∧ C.c.get g ≤ max_size) : ℝ) ≤
      (Procedure.Pr (CF (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) +
        ((max_size ^ 2 - max_size : ℤ) : ℝ) / 2 * (dstate.1 {default}).toReal := by
  sorry

end

end GaudisCrypt.SHA3.ConcreteF
