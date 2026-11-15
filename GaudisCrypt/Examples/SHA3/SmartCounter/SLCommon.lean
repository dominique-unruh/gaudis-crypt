import GaudisCrypt.Examples.SHA3.SmartCounter.SLCommonCore
import GaudisCrypt.Examples.SHA3.Indifferentiability
import GaudisCrypt.Lib.EC.FSet
import GaudisCrypt.Lib.EC.PROM
import GaudisCrypt.Lib.EC.DProd
import GaudisCrypt.Lib.EC.Tuple
import GaudisCrypt.Logic.PHoare
import GaudisCrypt.Logic.AbstractCallUpto
import GaudisCrypt.Logic.HoareFrame

/-!
# The squeezeless sponge: common definitions (EasyCrypt `proof/smart_counter/SLCommon.ec`)

The squeezeless sponge, whose ideal functionality is a fixed-output-length random oracle whose
output length is the input block size; its security holds even when the padding is not
prefix-free.  This file has the construction, the counting and restricting wrappers, the prefix
operators and the handle operators used by the whole `smart_counter` proof.

Translation notes (see `notes/SHA3/README.md`):
* `op max_size : { int | 0 <= max_size } as max_ge0` extends the parameter class: `Params`.
* `prefix` is a Lean keyword, hence `«prefix»`.
* `clone include Indifferentiability with type p <- state …` is the abbreviations below
  (`PRIMITIVE` …, `Indif`, `RealIndif`, `IdealIndif`); `clone import FullRO as F …` is the
  namespace `F`.
* Modules whose procedures alias another module's (`PRestr`, `FRestr`: `proc f = DPRestr(P).f`)
  are Lean functions assembling the procedures with `T.mk`.
* `DRestr(D : DISTINGUISHER, F, P)` takes `D` as a Lean parameter, so that `DRestr D` is a
  `DISTINGUISHER` (EasyCrypt uses it partially applied, `DRestr(D)`).
* A memory restriction `{-C}` is a footprint hypothesis against `C.footprint`.
-/

namespace GaudisCrypt.SHA3.SLCommon

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common

variable [Params]

/-! ## `clone include Indifferentiability with type p <- state, type f_in <- block list,
type f_out <- block rename [module] "GReal" as "RealIndif" [module] "GIdeal" as "IdealIndif"` -/

abbrev PRIMITIVE := Indifferentiability.PRIMITIVE state (List block) block
abbrev DPRIMITIVE := Indifferentiability.DPRIMITIVE state (List block) block
abbrev FUNCTIONALITY := Indifferentiability.FUNCTIONALITY state (List block) block
abbrev DFUNCTIONALITY := Indifferentiability.DFUNCTIONALITY state (List block) block
abbrev CONSTRUCTION := Indifferentiability.CONSTRUCTION state (List block) block
abbrev SIMULATOR := Indifferentiability.SIMULATOR state (List block) block
abbrev DISTINGUISHER := Indifferentiability.DISTINGUISHER state (List block) block
noncomputable abbrev Indif := Indifferentiability.Indif state (List block) block
noncomputable abbrev RealIndif := Indifferentiability.GReal state (List block) block
noncomputable abbrev IdealIndif := Indifferentiability.GIdeal state (List block) block

/-! ## The ideal functionality -/

-- `clone import FullRO as F with type in_t <- block list, type out_t <- block,
-- op dout _ <- bdistr, type d_in_t <- unit, type d_out_t <- bool`
namespace F
noncomputable abbrev dout : List block → SubProbability block := fun _ => bdistr
/-- The clone's module variable `F.RO.m`. -/
global_var RO.m : FMap (List block) block
/-- The clone's module variable `F.FRO.m`. -/
global_var FRO.m : FMap (List block) (block × flag)
noncomputable abbrev RO := PROM.FullRO.RO (List block) block dout RO.m
/-- `F.RO` as its type `RO` (`PROM.FullRO.RO.asRO`). -/
noncomputable abbrev RO.asRO := PROM.FullRO.RO.asRO (List block) block dout RO.m
/-- The module type `F.RO` (exception E3). -/
abbrev RO_T := PROM.FullRO.RO_T (List block) block
noncomputable abbrev LRO := PROM.FullRO.LRO (List block) block dout RO.m
noncomputable abbrev FRO := PROM.FullRO.FRO (List block) block dout FRO.m
abbrev RO_Distinguisher := PROM.FullRO.RO_Distinguisher (List block) block Unit Bool
namespace FullEager
noncomputable abbrev RRO := PROM.FullRO.FullEager.RRO (List block) block dout FRO.m
end FullEager
end F

/-! ## The squeezeless sponge -/

/-- EC's `Redo.prefixes`. -/
global_var Redo.prefixes : FMap (List block) state

module Redo {
  proc init () : Unit {
    Redo.prefixes <- FMap.set (FMap.empty : FMap (List block) state) [] (b0, c0);
    return ()
  };
}

-- The squeezeless sponge construction
module SqueezelessSponge using (P : DPRIMITIVE) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call Redo.init ();
    return ()
  };
  proc f (p : List block) : block {
    var sa : block, sc : capacity, i : ℤ;
    sa, sc <- (b0, c0);
    i <- 0;
    while ($i < size $p) {
      if (decide (FMap.dom ($Redo.prefixes : FMap (List block) state) (take ($i + 1) $p))) {
        sa, sc <- oget (FMap.get ($Redo.prefixes : FMap (List block) state) (take ($i + 1) $p));
      } else {
        sa, sc <- ($sa +^ nth default $p $i, $sc);
        sa, sc <- call P.f (($sa, $sc));
        Redo.prefixes <- FMap.set $Redo.prefixes (take ($i + 1) $p) ($sa, $sc);
      }
      i <- $i + 1;
    }
    return $sa
  };
}

open Prefix

/-! ## Counting and restricting -/

/-- EC's `C.c`. -/
global_var C.c : ℤ
/-- EC's `C.queries`. -/
global_var C.queries : FMap (List block) block

module C {
  proc init () : Unit {
    C.c <- 0;
    C.queries <- FMap.set (FMap.empty : FMap (List block) block) [] b0;
    return ()
  };
}

/-- What `C` touches: the restriction `{-C}`. -/
noncomputable def C.footprint : Footprint VariableAssignment :=
  C.c.footprint ⊔ (C.queries).footprint

module PC using (P : PRIMITIVE) : PRIMITIVE {
  proc init () : Unit {
    _ <- call C.init ();
    _ <- call P.init ();
    return ()
  };
  proc f (x : state) : state {
    var y : state;
    y <- (b0, c0);
    y <- call P.f ($x);
    C.c <- $C.c + 1;
    return $y
  };
  proc fi (x : state) : state {
    var y : state;
    y <- (b0, c0);
    y <- call P.fi ($x);
    C.c <- $C.c + 1;
    return $y
  };
}

module DPRestr using (P : DPRIMITIVE) : DPRIMITIVE {
  proc f (x : state) : state {
    var y : state;
    y <- (b0, c0);
    if (decide ($C.c + 1 ≤ max_size)) {
      y <- call P.f ($x);
      C.c <- $C.c + 1;
    }
    return $y
  };
  proc fi (x : state) : state {
    var y : state;
    y <- (b0, c0);
    if (decide ($C.c + 1 ≤ max_size)) {
      y <- call P.fi ($x);
      C.c <- $C.c + 1;
    }
    return $y
  };
}

module FC using (F : FUNCTIONALITY) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (bs : List block) : block {
    var b : block;
    b <- b0;
    if (!(decide (FMap.dom ($C.queries : FMap (List block) block) $bs))) {
      C.c <- $C.c + size $bs - «prefix» $bs (get_max_prefix $bs (elems (FMap.fdom
        ($C.queries : FMap (List block) block))));
      b <- call F.f ($bs);
      C.queries <- FMap.set $C.queries $bs $b;
    } else {
      b <- oget (FMap.get $C.queries $bs);
    }
    return $b
  };
}

module DFRestr using (F : DFUNCTIONALITY) : DFUNCTIONALITY {
  proc f (bs : List block) : block {
    var b : block;
    b <- b0;
    if (!(decide (FMap.dom ($C.queries : FMap (List block) block) $bs))) {
      if (decide ($C.c + size $bs - «prefix» $bs (get_max_prefix $bs (elems (FMap.fdom
          ($C.queries : FMap (List block) block)))) ≤ max_size)) {
        C.c <- $C.c + size $bs - «prefix» $bs (get_max_prefix $bs (elems (FMap.fdom
          ($C.queries : FMap (List block) block))));
        b <- call F.f ($bs);
        C.queries <- FMap.set $C.queries $bs $b;
      }
    } else {
      b <- oget (FMap.get $C.queries $bs);
    }
    return $b
  };
}

-- EC's `DRestr(D : DISTINGUISHER, F : DFUNCTIONALITY, P : DPRIMITIVE)`, with `D` a Lean parameter
-- so that `DRestr D` is a `DISTINGUISHER`
set_option linter.gaudisCrypt.using false in
module DRestr (D : DISTINGUISHER) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call C.init ();
    b <- call (Module.app D (Module.pair (Module.app DFRestr F) (Module.app DPRestr P))) ();
    return $b
  };
}

/-- `DFRestr` touches `C`'s variables only.  Not an EC lemma: EasyCrypt reads a concrete
module's globals off its code (for `fp_disjoint`, as `glob DRestr(D)`'s side conditions). -/
@[fp_bound] theorem fvP_DFRestr : FVP.fvP DFRestr ≤ C.footprint := by
  fp_module (Lens.pair C.c C.queries)

/-- `DPRestr` touches `C`'s variables only.  Not an EC lemma (as `fvP_DFRestr`). -/
@[fp_bound] theorem fvP_DPRestr : FVP.fvP DPRestr ≤ C.footprint := by
  fp_module (Lens.pair C.c C.queries)

/-- `FC` touches `C`'s variables only.  Not an EC lemma (as `fvP_DFRestr`). -/
@[fp_bound] theorem fvP_FC : FVP.fvP FC ≤ C.footprint := by
  fp_module (Lens.pair C.c C.queries)

/-- `PC` touches `C`'s variables only.  Not an EC lemma (as `fvP_DFRestr`). -/
@[fp_bound] theorem fvP_PC : FVP.fvP PC ≤ C.footprint := by
  fp_module (Lens.pair C.c C.queries)

end GaudisCrypt.SHA3.SLCommon
