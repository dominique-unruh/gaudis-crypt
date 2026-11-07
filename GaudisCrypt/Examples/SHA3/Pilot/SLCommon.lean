import GaudisCrypt.Examples.SHA3.SmartCounter.SLCommonCore
import GaudisCrypt.Examples.SHA3.Pilot.Indifferentiability
import GaudisCrypt.Syntax.Clone
import GaudisCrypt.Syntax.ModuleSubtype
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECCallUpto
import GaudisCrypt.Logic.ECInline
import GaudisCrypt.Logic.ECSeq
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.CallSpec

/-!
# The squeezeless sponge: common definitions (EasyCrypt `proof/smart_counter/SLCommon.ec`) —
EC-fidelity port

The construction `SqueezelessSponge`, the counting and restricting wrappers `C`, `PC`, `DPRestr`,
`FC`, `DFRestr`, `DRestr`, and their lemmas.  The operators without modules (the parameter class
with `max_size`, `state`, the `Prefix` theory, the handle operators) are
`SmartCounter/SLCommonCore.lean`, shared with the first port.

Translation (as the pilots' `IndifRO_is_secure`):
* `clone include Indifferentiability with type p <- state, … rename [module] "GReal" as
  "RealIndif" [module] "GIdeal" as "IdealIndif"` is `clone import … as Indiff` (`clone` has no
  `include` and no `rename`), `RealIndif` and `IdealIndif` aliases of `GReal`, `GIdeal`;
* `clone import FullRO as F with …` is the namespace `F` of `PROM.FullRO` at the clone's types,
  its module variables `global_var`s;
* the procedure aliases of `PRestr`, `FRestr` (`proc f = DPRestr(P).f`) are wrapped in a call
  (exception E5);
* `DRestr(D, F, P)` takes `D` as a Lean parameter: `DRestr(D)` is EC's partial application.
-/

namespace GaudisCrypt.SHA3.Pilot.SLCommon

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM
open GaudisCrypt.SHA3.Common hiding PRIMITIVE
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix

variable [SLCommon.Params]

/-- EC's `type state = block * capacity` (`SLCommonCore`'s, named here: a root `state` exists). -/
abbrev state := GaudisCrypt.SHA3.SLCommon.state

clone import GaudisCrypt.SHA3.Pilot.Indifferentiability as Indiff with
  type p <- state, type f_in <- List block, type f_out <- block

/-- EC's `rename [module] "GReal" as "RealIndif"`. -/
noncomputable abbrev RealIndif := @Indiff.GReal

/-- EC's `rename [module] "GIdeal" as "IdealIndif"`. -/
noncomputable abbrev IdealIndif := @Indiff.GIdeal

/-! `clone import FullRO as F with type in_t <- block list, type out_t <- block,
op dout _ <- bdistr, type d_in_t <- unit, type d_out_t <- bool`. -/

namespace F

noncomputable abbrev dout : List block → SubProbability block := fun _ => bdistr

global_var RO.m : FMap (List block) block

global_var FRO.m : FMap (List block) (block × flag)

/-- The clone's `RO`. -/
noncomputable abbrev RO := PROM.FullRO.RO.asRO (List block) block dout RO.m

/-- The clone's lazy `LRO`. -/
noncomputable abbrev LRO := PROM.FullRO.LRO (List block) block dout RO.m

/-- The clone's `FRO`. -/
noncomputable abbrev FRO := PROM.FullRO.FRO (List block) block dout FRO.m

end F

global_var Redo.prefixes : FMap (List block) state

module Redo {
  proc init () : Unit {
    Redo.prefixes <- FMap.set FMap.empty [] (b0, c0);
    return ()
  };
}

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
      if (decide (FMap.dom $Redo.prefixes (take ($i + 1) $p))) {
        sa, sc <- oget (FMap.get $Redo.prefixes (take ($i + 1) $p));
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

/-! ### Counting and restricting -/

global_var C.c : ℤ

global_var C.queries : FMap (List block) block

module C {
  proc init () : Unit {
    C.c <- 0;
    C.queries <- FMap.set FMap.empty [] b0;
    return ()
  };
}

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

module PRestr using (P : PRIMITIVE) : PRIMITIVE {
  proc init () : Unit {
    _ <- call C.init ();
    _ <- call P.init ();
    return ()
  };
  proc f (x : state) : state {
    var y : state;
    y <- call DPRestr(P).f ($x);
    return $y
  };
  proc fi (x : state) : state {
    var y : state;
    y <- call DPRestr(P).fi ($x);
    return $y
  };
}

-- the generated `FC.init` lemmas do not need the theory's parameters
set_option linter.unusedSectionVars false in
module FC using (F : FUNCTIONALITY) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (bs : List block) : block {
    var b : block;
    b <- b0;
    if (!(decide (FMap.dom $C.queries $bs))) {
      C.c <- $C.c + size $bs - «prefix» $bs (get_max_prefix $bs (elems (FMap.fdom $C.queries)));
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
    if (!(decide (FMap.dom $C.queries $bs))) {
      if (decide ($C.c + size $bs - «prefix» $bs (get_max_prefix $bs (elems (FMap.fdom $C.queries)))
          ≤ max_size)) {
        C.c <- $C.c + size $bs - «prefix» $bs (get_max_prefix $bs (elems (FMap.fdom $C.queries)));
        b <- call F.f ($bs);
        C.queries <- FMap.set $C.queries $bs $b;
      }
    } else {
      b <- oget (FMap.get $C.queries $bs);
    }
    return $b
  };
}

module FRestr using (F : FUNCTIONALITY) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call Redo.init ();
    _ <- call F.init ();
    return ()
  };
  proc f (bs : List block) : block {
    var b : block;
    b <- call DFRestr(F).f ($bs);
    return $b
  };
}

-- EC's `DRestr(D, F, P)`, `D` a Lean parameter: `DRestr(D)` is EC's partial application
set_option linter.gaudisCrypt.using false in
module DRestr (D : DISTINGUISHER) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call C.init ();
    b <- call D(DFRestr(F), DPRestr(P)).distinguish ();
    return $b
  };
}


/-- EC's `lemma rp_ll (P <: DPRIMITIVE{-C}): islossless P.f => islossless DPRestr(P).f`. -/
theorem rp_ll : ∀ (P <: DPRIMITIVE {-C}), islossless P.f → islossless DPRestr(P).f := by
  intro P _ Hll; phoare_proc; stmt_sp; stmt_if
  · phoare_auto; phoare_call Hll; phoare_auto
  · phoare_auto

/-- EC's `lemma rpi_ll (P <: DPRIMITIVE{-C}): islossless P.fi => islossless DPRestr(P).fi`. -/
theorem rpi_ll : ∀ (P <: DPRIMITIVE {-C}), islossless P.fi → islossless DPRestr(P).fi := by
  intro P _ Hll; phoare_proc; stmt_sp; stmt_if
  · phoare_auto; phoare_call Hll; phoare_auto
  · phoare_auto

/-- EC's `lemma rf_ll (F <: DFUNCTIONALITY{-C}): islossless F.f => islossless DFRestr(F).f`. -/
theorem rf_ll : ∀ (F <: DFUNCTIONALITY {-C}), islossless F.f → islossless DFRestr(F).f := by
  intro F _ Hll; phoare_proc; stmt_sp; stmt_if
  · stmt_if
    · phoare_auto; phoare_call Hll; phoare_auto
    · phoare_auto
  · phoare_auto

/-- EC's `lemma DRestr_ll (D <: DISTINGUISHER{-C}): (forall (F <: DFUNCTIONALITY{-D})
(P <: DPRIMITIVE{-D}), islossless P.f => islossless P.fi => islossless F.f =>
islossless D(F,P).distinguish) => forall (F <: DFUNCTIONALITY{-DRestr(D)})
(P <: DPRIMITIVE{-DRestr(D)}), islossless P.f => islossless P.fi => islossless F.f =>
islossless DRestr(D, F, P).distinguish`; `{-DRestr(D)}` is `{-D, -C}`, its globals. -/
theorem DRestr_ll : ∀ (D <: DISTINGUISHER {-C}),
    (∀ (F <: DFUNCTIONALITY {-D}), ∀ (P <: DPRIMITIVE {-D}),
      islossless P.f → islossless P.fi → islossless F.f → islossless D(F, P).distinguish) →
    ∀ (F <: DFUNCTIONALITY {-D, -C}), ∀ (P <: DPRIMITIVE {-D, -C}),
      islossless P.f → islossless P.fi → islossless F.f →
        islossless DRestr(D, F, P).distinguish := by
  intro D _ D_ll F _ P _ p_ll pi_ll f_ll
  phoare_proc
  phoare_call (@D_ll (Module.app DFRestr F) ⟨by fp_finite, by fp_disjoint⟩
    (Module.app DPRestr P) ⟨by fp_finite, by fp_disjoint⟩ (rp_ll P p_ll) (rpi_ll P pi_ll)
    (rf_ll F f_ll))
  phoare_inline*; phoare_auto

/-! ### Section `RESTR` -/

section RESTR

declare module F <: FUNCTIONALITY {-C, -Redo}
declare module P <: PRIMITIVE {-C, -F, -Redo}
declare module D <: DISTINGUISHER {-F, -P, -C, -Redo}

set_option maxHeartbeats 500000 in
-- one declaration: the distinguisher's call over three oracles, each by `sim`
/-- EC's `lemma swap_restr &m: Pr[Indif(FRestr(F), PRestr(P), D).main() @ &m: res] =
Pr[Indif(F,P,DRestr(D)).main() @ &m: res]`. -/
theorem swap_restr (m : VariableAssignment) :
    Pr[ Indif(FRestr(F), PRestr(P), D).main () @ &m : §res ] =
      Pr[ Indif(F, P, DRestr(D)).main () @ &m : §res ] := by
  byequiv; equiv_proc; stmt_inline*; stmt_wp
  stmt_swap{1} [1..2] 3
  equiv_call (_ : ={glob D, glob F, glob P, C.c, C.queries})
  · equiv_proc; stmt_inline*; sim
  · equiv_proc; stmt_inline*; sim
  · equiv_proc; stmt_inline*; sim
  · stmt_swap{1} [2..2] 3
    sim

end RESTR

/-- `module GReal(D : DISTINGUISHER) = RealIndif(SqueezelessSponge, PC(Perm), D)`, `Perm` the
`PRIMITIVE` of `Common`'s permutation (EC's clone of `RP` at `block * capacity`). -/
module_subtype (EC.PRP.StrongPRP.PRP (block × capacity)) <:
  GaudisCrypt.SHA3.Pilot.Indifferentiability.PRIMITIVE

noncomputable abbrev GReal (D : DISTINGUISHER) : procmod () → Bool :=
  RealIndif SqueezelessSponge (Module.app PC (Perm : PRIMITIVE)) D

end GaudisCrypt.SHA3.Pilot.SLCommon
