import GaudisCrypt.Examples.SHA3.SHA3Indiff
import GaudisCrypt.Examples.SHA3.OptionIndifferentiability

/-!
# Indifferentiability of the sponge with failing oracles (EasyCrypt `proof/SHA3_OIndiff.ec`)

`SHA3OIndiff`: `SHA3Indiff` restated for `OptionIndifferentiability`, whose oracles return
`option`s and whose restriction to `limit` calls makes the oracles fail (`None`) beyond it.  The
proof reduces it to `SHA3Indiff.security`.

Translation notes (see `notes/SHA3/README.md`):
* `clone import OptionIndifferentiability as OIndif with type p <- state, type f_out <- bool list,
  type f_in <- bool list * int` is the namespace `OIndif` of abbreviations, opened.
* `require import SHA3Indiff` comes last, so its `state`, `parse` and `valid` win over the
  root-level `state` and `Sponge.BIRO.valid`; stated with `export`.
* `FSome(F)` has `proc init = F.init` and is used as a functor (`CSome`): its `init` calls `F.init`
  (exception E5).  `PSome(P)` is only applied to `Perm`: it is a Lean function assembling
  `P.init` with its own `f`, `fi` (`PSome.own`).  `CSome(C)(P) = FSome(C(Poget(P)))` is
  `Module.comp FSome (Module.comp C Poget)`.
* `OSimulator`, `OFC`, `OPC`, `DFSome`, `DPSome` have no type in EasyCrypt; they are declared at the
  types they are used as.
* The section's `declare module Dist` is used by none of its lemmas: `SHA3OIndiff` quantifies its
  own `Dist`.
-/

-- the clone `OIndif` contains the module `OIndif` (`OIndif.OIndif`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.SHA3_OIndiff

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.Sponge
open GaudisCrypt.SHA3.Sponge.BIRO GaudisCrypt.SHA3.SHA3Indiff

-- EasyCrypt's last import, `SHA3Indiff`, shadows the root-level `state` and `Sponge.BIRO.valid`;
-- `PRIMITIVE` is `Sponge`'s (over `Common`'s), as in `SHA3Indiff`
export GaudisCrypt.SHA3.SHA3Indiff (state parse valid PRIMITIVE)

variable [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params]

/-! ## `clone import OptionIndifferentiability as OIndif with type p <- state,
type f_out <- bool list, type f_in <- bool list * int` -/

namespace OIndif
abbrev OPRIMITIVE := OptionIndifferentiability.OPRIMITIVE state (List Bool × ℤ) (List Bool)
abbrev ODPRIMITIVE := OptionIndifferentiability.ODPRIMITIVE state (List Bool × ℤ) (List Bool)
abbrev OFUNCTIONALITY :=
  OptionIndifferentiability.OFUNCTIONALITY state (List Bool × ℤ) (List Bool)
abbrev ODFUNCTIONALITY :=
  OptionIndifferentiability.ODFUNCTIONALITY state (List Bool × ℤ) (List Bool)
abbrev OCONSTRUCTION := OptionIndifferentiability.OCONSTRUCTION state (List Bool × ℤ) (List Bool)
abbrev OSIMULATOR := OptionIndifferentiability.OSIMULATOR state (List Bool × ℤ) (List Bool)
abbrev ODISTINGUISHER :=
  OptionIndifferentiability.ODISTINGUISHER state (List Bool × ℤ) (List Bool)
noncomputable abbrev OIndif := OptionIndifferentiability.OIndif state (List Bool × ℤ) (List Bool)
noncomputable abbrev OGReal := OptionIndifferentiability.OGReal state (List Bool × ℤ) (List Bool)
noncomputable abbrev OGIdeal := OptionIndifferentiability.OGIdeal state (List Bool × ℤ) (List Bool)
abbrev distHoles := OptionIndifferentiability.distHoles state (List Bool × ℤ) (List Bool)
noncomputable abbrev distExt :=
  OptionIndifferentiability.distExt state (List Bool × ℤ) (List Bool)
end OIndif

open OIndif

-- EC's `FSome (F : FUNCTIONALITY) : OFUNCTIONALITY`; its `proc init = F.init` is wrapped in a call,
-- as `FSome` is used as a functor (`CSome`; exception E5)
module FSome using (F : FUNCTIONALITY) : OFUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (x : List Bool × ℤ) : (Option (List Bool)) {
    var z : List Bool;
    z <- call F.f ($x);
    return some $z
  };
}

-- `PSome(P).f` and `PSome(P).fi`, the procedures of `PSome` that are not `P`'s
module PSome.own using (P : PRIMITIVE) {
  proc f (x : state) : (Option state) {
    var z : state;
    z <- call P.f ($x);
    return some $z
  };
  proc fi (x : state) : (Option state) {
    var z : state;
    z <- call P.fi ($x);
    return some $z
  };
}

/-- EC's `PSome (P : PRIMITIVE) : OPRIMITIVE`: `proc init = P.init`, and `proc f`, `proc fi`. -/
noncomputable def PSome (P : PRIMITIVE) : OPRIMITIVE :=
  OptionIndifferentiability.OPRIMITIVE.mk state (List Bool × ℤ) (List Bool)
    { init := Indifferentiability.PRIMITIVE.init (block × capacity) (List Bool × ℤ) (List Bool) P
      f := Module.app PSome.own.f P
      fi := Module.app PSome.own.fi P }

module Poget using (P : ODPRIMITIVE) : DPRIMITIVE {
  proc f (x : state) : state {
    var z : Option state;
    z <- call P.f ($x);
    return oget $z
  };
  proc fi (x : state) : state {
    var z : Option state;
    z <- call P.fi ($x);
    return oget $z
  };
}

/-- `module (CSome (C : CONSTRUCTION) : OCONSTRUCTION) (P : ODPRIMITIVE) = FSome(C(Poget(P)))`. -/
noncomputable def CSome (C : CONSTRUCTION) : OCONSTRUCTION :=
  Module.comp FSome (Module.comp C Poget)

module OSimulator using (F : ODFUNCTIONALITY) : OPRIMITIVE {
  proc init () : Unit {
    Simulator.m <- (FMap.empty : FMap state state);
    Simulator.mi <- (FMap.empty : FMap state state);
    Simulator.paths <- FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0);
    _ <- call Gconcl_list.BIRO2.IRO.init ();
    return ()
  };
  proc f (x : state) : (Option state) {
    var p : List block, v : block, z : List block, q : List block, k : ℤ, cs : List Bool,
      y : state, y1 : block, y2 : capacity, o : Option (List Bool);
    if (!(decide (FMap.dom ($Simulator.m : FMap state state) $x))) {
      if (decide (FMap.dom ($Simulator.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($Simulator.paths : FMap capacity (List block × block)) ($x).2);
        z <- [];
        q, k <- parse (rcons $p ($v +^ ($x).1));
        if (valid $q) {
          o <- call F.f ((oget (unpad_blocks $q), $k * r));
          cs <- oget $o;
          z <- bits2blocks $cs;
        } else {
          z <- call Gconcl_list.BIRO2.IRO.f (($q, $k));
        }
        y1 <- last b0 $z;
      } else {
        y1 <$ bdistr;
      }
      y2 <$ cdistr;
      y <- ($y1, $y2);
      Simulator.m <- FMap.set $Simulator.m $x $y;
      Simulator.mi <- FMap.set $Simulator.mi $y $x;
      if (decide (FMap.dom ($Simulator.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($Simulator.paths : FMap capacity (List block × block)) ($x).2);
        Simulator.paths <- FMap.set $Simulator.paths $y2 (rcons $p ($v +^ ($x).1), ($y).1);
      }
    } else {
      y <- oget (FMap.get ($Simulator.m : FMap state state) $x);
    }
    return some $y
  };
  proc fi (x : state) : (Option state) {
    var y : state, y1 : block, y2 : capacity;
    if (!(decide (FMap.dom ($Simulator.mi : FMap state state) $x))) {
      y1 <$ bdistr;
      y2 <$ cdistr;
      y <- ($y1, $y2);
      Simulator.mi <- FMap.set $Simulator.mi $x $y;
      Simulator.m <- FMap.set $Simulator.m $y $x;
    } else {
      y <- oget (FMap.get ($Simulator.mi : FMap state state) $x);
    }
    return some $y
  };
}

/-- EC's `Counter.c`. -/
global_var Counter.c : ℤ

module Counter {
  proc init () : Unit {
    Counter.c <- 0;
    return ()
  };
}

def increase_counter {α : Type} (c : ℤ) (l : List α) (n : ℤ) : ℤ :=
  c + ((size l + 1) / r + 1) + max ((n + r - 1) / r - 1) 0

module OFC using (F : ODFUNCTIONALITY) : OFUNCTIONALITY {
  proc init () : Unit {
    _ <- call Counter.init ();
    return ()
  };
  proc f (x : List Bool × ℤ) : (Option (List Bool)) {
    var l : List Bool, k : ℤ, o : Option (List Bool);
    l, k <- $x;
    o <- (none : Option (List Bool));
    if (decide (increase_counter $Counter.c $l $k ≤ limit)) {
      o <- call F.f (($l, $k));
      Counter.c <- increase_counter $Counter.c $l $k;
    }
    return $o
  };
}

module OPC using (P : ODPRIMITIVE) : OPRIMITIVE {
  proc init () : Unit {
    return ()
  };
  proc f (x : state) : (Option state) {
    var o : Option state;
    o <- (none : Option state);
    if (decide ($Counter.c + 1 ≤ limit)) {
      o <- call P.f ($x);
      Counter.c <- $Counter.c + 1;
    }
    return $o
  };
  proc fi (x : state) : (Option state) {
    var o : Option state;
    o <- (none : Option state);
    if (decide ($Counter.c + 1 ≤ limit)) {
      o <- call P.fi ($x);
      Counter.c <- $Counter.c + 1;
    }
    return $o
  };
}

-- EC's `ODRestr(D)(F)(P)`, with `D` a Lean parameter so that `ODRestr D` is an `ODISTINGUISHER`
set_option linter.gaudisCrypt.using false in
module ODRestr (D : ODISTINGUISHER) using (F : ODFUNCTIONALITY, P : ODPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call Counter.init ();
    b <- call (Module.app D (Module.pair
      (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app OFC F) })
      (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OPC P)
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OPC P) }))) ();
    return $b
  };
}

/-! ## The section, with `declare module Dist <: ODISTINGUISHER {-Perm, -Gconcl_list.SimLast, …}`
(used by none of its lemmas) -/

section

module DFSome using (F : DFUNCTIONALITY) : ODFUNCTIONALITY {
  proc f (x : List Bool × ℤ) : (Option (List Bool)) {
    var z : List Bool;
    z <- call F.f ($x);
    return some $z
  };
}

module DPSome using (P : DPRIMITIVE) : ODPRIMITIVE {
  proc f (x : state) : (Option state) {
    var z : state;
    z <- call P.f ($x);
    return some $z
  };
  proc fi (x : state) : (Option state) {
    var z : state;
    z <- call P.fi ($x);
    return some $z
  };
}

-- EC's local `(OD (D : ODISTINGUISHER) : DISTINGUISHER) (F : DFUNCTIONALITY) (P : DPRIMITIVE)`,
-- with `D` a Lean parameter so that `OD D` is a `DISTINGUISHER`
set_option linter.gaudisCrypt.using false in
module OD (D : ODISTINGUISHER) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call Counter.init ();
    b <- call (Module.app D (Module.pair
      (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app OFC (Module.app DFSome F)) })
      (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OPC (Module.app DPSome P))
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OPC (Module.app DPSome P)) }))) ();
    return $b
  };
}

/-- `SHA3OIndiff`'s restriction `{-Counter, -Perm, -IRO, -BlockSponge.BIRO.IRO, -Cntr, -Simulator,
-Gconcl_list.SimLast(Gconcl.S), -BlockSponge.C, -Gconcl.S, -SLCommon.F.RO, -SLCommon.F.FRO,
-SLCommon.Redo, -SLCommon.C, -Gconcl_list.BIRO2.IRO, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
-Gconcl_list.Simulator, -OSimulator}`: `SHA3Indiff`'s, and `Counter`, `OSimulator` (an
abbreviation). -/
def ODistRestrictions (Dist : ODISTINGUISHER) : Prop :=
  FVP.fvP Dist ≤ (DistRestrictions.footprint ⊔ Counter.c.footprint ⊔ FVP.fvP OSimulator)ᶜ

/-- EC's `SHA3OIndiff (Dist <: ODISTINGUISHER {…}) &m`, whose hypothesis that `Dist` is lossless
for lossless oracles puts no restriction on the oracles. -/
theorem SHA3OIndiff (Dist : ODISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (_hDd : ODistRestrictions Dist) (m : VariableAssignment) :
    (∀ (F : ODFUNCTIONALITY) (P : ODPRIMITIVE),
      (OptionIndifferentiability.ODPRIMITIVE.f state (List Bool × ℤ) (List Bool)
        P).procedure.IsLossless →
      (OptionIndifferentiability.ODPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
        P).procedure.IsLossless →
      (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        F).procedure.IsLossless →
      (Module.app Dist (Module.pair F P)).procedure.IsLossless) →
    |(Procedure.Pr (OGReal (CSome Sponge.Sponge) (PSome Perm) (ODRestr Dist)).procedure () m
        (fun r _ => r = true) : ℝ) -
      (Procedure.Pr (OGIdeal (Module.app FSome BIRO.IRO.asF) OSimulator (ODRestr Dist)).procedure
        () m (fun r _ => r = true) : ℝ)| ≤ bound := by
  sorry

end

end GaudisCrypt.SHA3.SHA3_OIndiff
