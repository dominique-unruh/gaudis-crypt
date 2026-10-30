import GaudisCrypt.Lib.EC.PRP
import GaudisCrypt.Logic.PHoare
import GaudisCrypt.FV

/-!
# EasyCrypt's PRP/PRF switching lemma (`theories/crypto/prp_prf/Strong_RP_RF.eca`)

The abstract theory's types `D`, `K` and operators `uD`, `dK`, `q` are section variables (with
their axioms as hypotheses where used), so a `clone` is an application.  Only what ported
developments use is here: `ARP`, `DBounder` and the statement of `Conclusion`.

The `PRPi` clone (`clone import RP as PRPi with op dD <- uD rename "RP" as "PRPi"`) is
`PRP.RP.RP D uD`.  Its module variables are the generic `PRP.RP.m`/`mi`, shared with any other
`RP` clone at the same type (exception E4 of the SHA-3 port).
-/

namespace GaudisCrypt.EC.Strong_RP_RF

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PRP.StrongPRP

variable (D : Type) [DecidableEq D] [Inhabited D]

section Variables
variable {D}
/-- EC's `ARP.coll`. -/
global_var ARP.coll : Bool
/-- EC's `ARP.m`. -/
global_var ARP.m : FMap D D
/-- EC's `ARP.mi`. -/
global_var ARP.mi : FMap D D
end Variables

/-- EC's `DBounder.FBounder.c`. -/
global_var DBounder.FBounder.c : ℤ

variable (uD : SubProbability D) (q : ℤ)

/-- `clone import RP as PRPi with op dD <- uD rename "RP" as "PRPi"`. -/
noncomputable abbrev PRPi.PRPi := PRP.RP.RP D uD

-- An "almost random permutation": it keeps track of collisions explicitly.
module ARP : (PRP D) {
  proc init () : Unit {
    ARP.m <- (FMap.empty : FMap D D);
    ARP.mi <- (FMap.empty : FMap D D);
    ARP.coll <- false;
    return ()
  };
  proc f (x : D) : D {
    var y : D;
    if (!(decide (FMap.dom ($ARP.m : FMap D D) $x))) {
      y <$ uD;
      ARP.coll <- $ARP.coll || decide (FMap.rng ($ARP.m : FMap D D) $y);
      ARP.m <- FMap.set $ARP.m $x $y;
      ARP.mi <- FMap.set $ARP.mi $y $x;
    }
    return oget (FMap.get $ARP.m $x)
  };
  proc fi (y : D) : D {
    var x : D;
    if (!(decide (FMap.dom ($ARP.mi : FMap D D) $y))) {
      x <$ uD;
      ARP.coll <- $ARP.coll || decide (FMap.rng ($ARP.mi : FMap D D) $x);
      ARP.m <- FMap.set $ARP.m $x $y;
      ARP.mi <- FMap.set $ARP.mi $y $x;
    }
    return oget (FMap.get $ARP.mi $y)
  };
}

-- EC's `DBounder(D, F).FBounder`
module DBounder.FBounder using (F : SPRP_Oracles D) : (SPRP_Oracles D) {
  proc f (x : D) : D {
    var r : D;
    r <- default;
    if (decide ($DBounder.FBounder.c < q)) {
      r <- call F.f ($x);
      DBounder.FBounder.c <- $DBounder.FBounder.c + 1;
    }
    return $r
  };
  proc fi (x : D) : D {
    var r : D;
    r <- default;
    if (decide ($DBounder.FBounder.c < q)) {
      r <- call F.fi ($x);
      DBounder.FBounder.c <- $DBounder.FBounder.c + 1;
    }
    return $r
  };
}

-- EC's `DBounder(D : Distinguisher, F : SPRP_Oracles)`, with `D` a Lean parameter so that
-- `DBounder Dist` is a `Distinguisher`
set_option linter.gaudisCrypt.using false in
module DBounder (Dist : Distinguisher D) using (F : SPRP_Oracles D) {
  proc distinguish () : Bool {
    var b : Bool;
    DBounder.FBounder.c <- 0;
    b <- call (Module.app Dist (Module.app (DBounder.FBounder D q) F)) ();
    return $b
  };
}

/-- EC's `Conclusion`, for `D <: Distinguisher {-PRPi, -ARP, -DBounder}`, under the theory's
axiom `uD_uf_fu` (`uD` uniform, lossless and full).  `mu uD (pred1 witness)` is the probability of
`default`. -/
theorem Conclusion (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y})
    (Dist : Distinguisher D)
    (_hD : FVP.fvP Dist ≤ ((PRP.RP.m (D := D)).footprint ⊔ (PRP.RP.mi (D := D)).footprint ⊔
      (ARP.m (D := D)).footprint ⊔ (ARP.mi (D := D)).footprint ⊔ ARP.coll.footprint ⊔
      DBounder.FBounder.c.footprint)ᶜ)
    (m : VariableAssignment) :
    (∀ O : SPRP_Oracles D, FVP.fvP O ≤ (FVP.fvP Dist)ᶜ →
      (SPRP_Oracles.f D O).procedure.IsLossless → (SPRP_Oracles.fi D O).procedure.IsLossless →
      (Module.app Dist O).procedure.IsLossless) →
    |(Procedure.Pr (Module.app (IND D) (Module.pair (PRPi.PRPi D uD) (DBounder D q Dist))).procedure
        () m (fun r _ => r = true) : ℝ) -
      (Procedure.Pr (Module.app (IND D) (Module.pair (ARP D uD) (DBounder D q Dist))).procedure
        () m (fun r _ => r = true) : ℝ)| ≤
      ((q ^ 2 - q : ℤ) : ℝ) / 2 * (uD.1 {default}).toReal := by
  sorry

end GaudisCrypt.EC.Strong_RP_RF
