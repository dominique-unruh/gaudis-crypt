import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Lib.EC.FMap
import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Lib.EC.Dexcepted
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECIf

/-!
# EasyCrypt's pseudo-random permutations (`theories/crypto/PRP.eca`)

The abstract type `D` and the operator `dD` are Lean parameters, so EasyCrypt's
`clone PRP with type D <- …` and `clone RP with op dD <- …` are applications.  So are the module
variables (`RP.m`, `RP.mi`): a clone declares its own `global_var`s and passes them.  The sub-theories
`StrongPRP` and `RP` are namespaces.  Only what ported developments use is here (`WeakPRP` is not).
-/

-- EasyCrypt names a module after its theory (`RP.RP`, `IRO.IRO`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.EC.PRP

open GaudisCrypt GaudisCrypt.EC

variable (D : Type) [DecidableEq D] [Inhabited D]

namespace StrongPRP

-- EC's `StrongPRP.PRP`
moduletype PRP {
  proc init () -> Unit;
  proc f (x : D) -> D;
  proc fi (x : D) -> D;
}

-- EC's `StrongPRP.SPRP_Oracles`
moduletype SPRP_Oracles {
  proc f (x : D) -> D;
  proc fi (x : D) -> D;
}

/-- EC's `StrongPRP.Distinguisher (P : SPRP_Oracles)`. -/
abbrev Distinguisher := SPRP_Oracles D →ₘ procmod () → Bool

module IND using (P : PRP D, Dist : Distinguisher D) {
  proc main () : Bool {
    var b : Bool;
    _ <- call P.init ();
    b <- call (Module.app Dist (SPRP_Oracles.mk D { f := PRP.f D P, fi := PRP.fi D P })) ();
    return $b
  };
}

end StrongPRP

namespace RP

/-! The module variables `RP.m`, `RP.mi` are parameters: each clone declares its own (EasyCrypt's
`clone RP as Perm` has `Perm.m`, `Perm.mi`), so two clones never share them. -/

variable (dD : SubProbability D) (m mi : Lens (FMap D D) VariableAssignment)

-- EC's `RP.RP`
module RP : (StrongPRP.PRP D) {
  proc init () : Unit {
    m <- (FMap.empty : FMap D D);
    mi <- (FMap.empty : FMap D D);
    return ()
  };
  proc f (x : D) : D {
    var y : D;
    if (!(decide (FMap.dom $m $x))) {
      y <$ dexcepted dD (FMap.rng $m);
      m <- FMap.set $m $x $y;
      mi <- FMap.set $mi $y $x;
    }
    return oget (FMap.get $m $x)
  };
  proc fi (y : D) : D {
    var x : D;
    if (!(decide (FMap.dom $mi $y))) {
      x <$ dexcepted dD (FMap.rng $mi);
      mi <- FMap.set $mi $y $x;
      m <- FMap.set $m $x $y;
    }
    return oget (FMap.get $mi $y)
  };
}

-- the clone's parameters, as EC's `f_ll _` leaves them: implicit
variable {D dD m mi}

/-- `lemma f_ll: is_full dD => islossless RP.f` (with the theory's axiom `dD_ll`): `RP.f`
samples from `dD \ rng RP.m`, which keeps a value when `RP.m` misses the queried key
(`endo_dom_rng`). -/
theorem f_ll (dD_ll : is_lossless dD) (dD_fu : is_full dD) :
    (StrongPRP.PRP.f D (RP D dD m mi)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  phoare_proc; stmt_if
  · phoare_auto
    intro m1 x h
    obtain ⟨y, hy⟩ := FMap.endo_dom_rng m1 ⟨x, by simpa using h⟩
    exact (is_lossless_iff_expected _).mp (dexcepted_ll dD _ dD_ll ⟨y, hy, (dD_fu y).ne'⟩)
  · phoare_auto

/-- `lemma fi_ll: is_full dD => islossless RP.fi` (as `f_ll`). -/
theorem fi_ll (dD_ll : is_lossless dD) (dD_fu : is_full dD) :
    (StrongPRP.PRP.fi D (RP D dD m mi)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  phoare_proc; stmt_if
  · phoare_auto
    intro m1 y h
    obtain ⟨x, hx⟩ := FMap.endo_dom_rng m1 ⟨y, by simpa using h⟩
    exact (is_lossless_iff_expected _).mp (dexcepted_ll dD _ dD_ll ⟨x, hx, (dD_fu x).ne'⟩)
  · phoare_auto

end RP

end GaudisCrypt.EC.PRP
