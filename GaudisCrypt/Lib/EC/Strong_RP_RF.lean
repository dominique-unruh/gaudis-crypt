import GaudisCrypt.Lib.EC.PRP
import GaudisCrypt.Logic.PHoare
import GaudisCrypt.FV

/-!
# EasyCrypt's PRP/PRF switching lemma (`theories/crypto/prp_prf/Strong_RP_RF.eca`)

The abstract theory's types `D`, `K` and operators `uD`, `dK`, `q` are section variables (with
their axioms as hypotheses where used), so a `clone` is an application.  Only what ported
developments use is here: `ARP`, `DBounder` and the statement of `Conclusion`.

The `PRPi` clone (`clone import RP as PRPi with op dD <- uD rename "RP" as "PRPi"`) is
`PRP.RP.RP D uD`.  Module variables (`PRPi.m`, `ARP.coll` …) are parameters: a clone of this theory
declares its own `global_var`s and passes them.
-/

namespace GaudisCrypt.EC.Strong_RP_RF

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PRP.StrongPRP

variable (D : Type) [DecidableEq D] [Inhabited D]

variable (uD : SubProbability D) (q : ℤ)

/-- `clone import RP as PRPi with op dD <- uD rename "RP" as "PRPi"`, with its module variables
`PRPi.m`, `PRPi.mi` passed by the clone. -/
noncomputable abbrev PRPi.PRPi (m mi : Lens (FMap D D) VariableAssignment) := PRP.RP.RP D uD m mi

section ARP
/-! `ARP`'s module variables `coll`, `m`, `mi` are parameters (see `PRP.lean`). -/
variable (coll : Lens Bool VariableAssignment) (m mi : Lens (FMap D D) VariableAssignment)

-- An "almost random permutation": it keeps track of collisions explicitly.
module ARP : (PRP D) {
  proc init () : Unit {
    m <- (FMap.empty : FMap D D);
    mi <- (FMap.empty : FMap D D);
    coll <- false;
    return ()
  };
  proc f (x : D) : D {
    var y : D;
    if (!(decide (FMap.dom ($m : FMap D D) $x))) {
      y <$ uD;
      coll <- $coll || decide (FMap.rng ($m : FMap D D) $y);
      m <- FMap.set $m $x $y;
      mi <- FMap.set $mi $y $x;
    }
    return oget (FMap.get $m $x)
  };
  proc fi (y : D) : D {
    var x : D;
    if (!(decide (FMap.dom ($mi : FMap D D) $y))) {
      x <$ uD;
      coll <- $coll || decide (FMap.rng ($mi : FMap D D) $x);
      m <- FMap.set $m $x $y;
      mi <- FMap.set $mi $y $x;
    }
    return oget (FMap.get $mi $y)
  };
}

end ARP

section DBounder
/-! `DBounder.FBounder`'s module variable `c` is a parameter (see `PRP.lean`). -/
variable (c : Lens ℤ VariableAssignment)

-- EC's `DBounder(D, F).FBounder`
module DBounder.FBounder using (F : SPRP_Oracles D) : (SPRP_Oracles D) {
  proc f (x : D) : D {
    var r : D;
    r <- default;
    if (decide ($c < q)) {
      r <- call F.f ($x);
      c <- $c + 1;
    }
    return $r
  };
  proc fi (x : D) : D {
    var r : D;
    r <- default;
    if (decide ($c < q)) {
      r <- call F.fi ($x);
      c <- $c + 1;
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
    c <- 0;
    b <- call (Module.app Dist (Module.app (DBounder.FBounder D q c) F)) ();
    return $b
  };
}

end DBounder

/-- EC's `Conclusion`, for `D <: Distinguisher {-PRPi, -ARP, -DBounder}`, under the theory's
axiom `uD_uf_fu` (`uD` uniform, lossless and full).  `mu uD (pred1 witness)` is the probability of
`default`. -/
theorem Conclusion (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y})
    (PRPi_m PRPi_mi ARP_m ARP_mi : Lens (FMap D D) VariableAssignment)
    (ARP_coll : Lens Bool VariableAssignment) (FBounder_c : Lens ℤ VariableAssignment)
    (Dist : Distinguisher D)
    (_hD : FVP.fvP Dist ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ ARP_m.footprint ⊔
      ARP_mi.footprint ⊔ ARP_coll.footprint ⊔ FBounder_c.footprint)ᶜ)
    (m : VariableAssignment) :
    (∀ O : SPRP_Oracles D, FVP.fvP O ≤ (FVP.fvP Dist)ᶜ →
      (SPRP_Oracles.f D O).procedure.IsLossless → (SPRP_Oracles.fi D O).procedure.IsLossless →
      (Module.app Dist O).procedure.IsLossless) →
    |(Procedure.Pr (Module.app (IND D) (Module.pair (PRPi.PRPi D uD PRPi_m PRPi_mi)
        (DBounder D q FBounder_c Dist))).procedure () m (fun r _ => r = true) : ℝ) -
      (Procedure.Pr (Module.app (IND D) (Module.pair (ARP D uD ARP_coll ARP_m ARP_mi)
        (DBounder D q FBounder_c Dist))).procedure () m (fun r _ => r = true) : ℝ)| ≤
      ((q ^ 2 - q : ℤ) : ℝ) / 2 * (uD.1 {default}).toReal := by
  sorry

end GaudisCrypt.EC.Strong_RP_RF
