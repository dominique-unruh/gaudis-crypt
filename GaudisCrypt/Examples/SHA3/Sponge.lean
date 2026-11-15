import GaudisCrypt.Examples.SHA3.BlockSponge
import GaudisCrypt.Lib.EC.PROM
import GaudisCrypt.Lib.EC.DList
import GaudisCrypt.Lib.EC.Int
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.LoopTransform
import GaudisCrypt.Logic.ModuleComp
import GaudisCrypt.Examples.SHA3.IndifferentiabilityCalls
import GaudisCrypt.Logic.SyntacticFrame
import GaudisCrypt.Logic.ConcreteFootprint
import GaudisCrypt.Logic.FootprintSolver

/-!
# The sponge construction (EasyCrypt `proof/Sponge.ec`)

The sponge on bits (`Sponge`, padding its input and squeezing `n` bits) is indifferentiable from
the infinite random oracle on bits `BIRO.IRO`, exactly as well as the block sponge is from the
block-level `BlockSponge.BIRO.IRO` (`conclusion`).  The ideal side goes through the abstract
theory `HybridIRO` of hybrid oracles (bits indexed by block lists), lazy and eager.

Translation notes (see `notes/SHA3/README.md` and `Exceptions.md`):
* `clone include Indifferentiability with type p <- block * capacity, type f_in <- bool list *
  int, type f_out <- bool list rename … "Indif" as "Experiment" …` is the abbreviations below.
* `clone import IRO as BIRO with type from <- bool list, type to <- bool, op valid <-
  valid_toplevel, op dto <- dbool` is the namespace `BIRO`; EasyCrypt's unqualified `IRO` is
  `BIRO.IRO`.
* Procedures whose EasyCrypt parameters `(bs, n)` are the module type's single parameter take that
  pair and name its components, as in `BlockSponge`.  `HYBRID_IRO.f` is not a functionality: it
  keeps its two parameters.
* `LowerDist(D, F) = D(RaiseFun(F))` is used as `LowerDist(Dist) : BlockSponge.DISTINGUISHER`:
  `D` is a Lean parameter, and the alias is wrapped in a call (exception E5).  `RaiseSim(S, F) =
  S(LowerFun(F))` is the composite `Module.comp S LowerFun`.
* The abstract theory `HybridIRO` is the namespace `HybridIRO`.  Its modules' variables
  (`HybridIROLazy.mp`, `HybridIROEager.mp`) are lens parameters, as for every generic theory.
* Variables of *local* clones (`ERO` in `HybridIRO`, `HIRO` in the last section) are lens
  parameters of the local declarations that mention them, with hypotheses that they are fresh
  for the section's modules; the non-local results do not mention them (exception E6).
* EasyCrypt's `proc distinguish()` is a `RO_Distinguisher`, whose procedure takes `unit`; here
  `RODist`'s `distinguish` takes that `Unit` parameter.
-/

-- EasyCrypt names the module `Sponge` like its file (`Sponge.Sponge`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.Sponge

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common

variable [SLCommon.Params] [BlockSponge.Params]

/-! ## Indifferentiability: `clone include Indifferentiability with type p <- block * capacity,
type f_in <- bool list * int, type f_out <- bool list rename [module] "Indif" as "Experiment"
[module] "GReal" as "RealIndif" [module] "GIdeal" as "IdealIndif"` -/

abbrev PRIMITIVE := Indifferentiability.PRIMITIVE (block × capacity) (List Bool × ℤ) (List Bool)
abbrev DPRIMITIVE := Indifferentiability.DPRIMITIVE (block × capacity) (List Bool × ℤ) (List Bool)
abbrev FUNCTIONALITY :=
  Indifferentiability.FUNCTIONALITY (block × capacity) (List Bool × ℤ) (List Bool)
abbrev DFUNCTIONALITY :=
  Indifferentiability.DFUNCTIONALITY (block × capacity) (List Bool × ℤ) (List Bool)
abbrev CONSTRUCTION :=
  Indifferentiability.CONSTRUCTION (block × capacity) (List Bool × ℤ) (List Bool)
abbrev SIMULATOR := Indifferentiability.SIMULATOR (block × capacity) (List Bool × ℤ) (List Bool)
abbrev DISTINGUISHER :=
  Indifferentiability.DISTINGUISHER (block × capacity) (List Bool × ℤ) (List Bool)
noncomputable abbrev Experiment :=
  Indifferentiability.Indif (block × capacity) (List Bool × ℤ) (List Bool)
noncomputable abbrev RealIndif :=
  Indifferentiability.GReal (block × capacity) (List Bool × ℤ) (List Bool)
noncomputable abbrev IdealIndif :=
  Indifferentiability.GIdeal (block × capacity) (List Bool × ℤ) (List Bool)

/-! ## The ideal functionality: `clone import IRO as BIRO with type from <- bool list,
type to <- bool, op valid <- valid_toplevel, op dto <- dbool` -/

namespace BIRO
/-- `op valid <- valid_toplevel`, as a test. -/
def valid (bs : List Bool) : Bool := decide (valid_toplevel bs)
abbrev IRO_T := IRO.IRO_T Bool (List Bool)
/-- The clone's module variable `BIRO.IRO.mp`. -/
global_var IRO.mp : FMap (List Bool × ℤ) Bool
noncomputable abbrev IRO := IRO.IRO Bool (List Bool) valid dbool IRO.mp
noncomputable abbrev IRO.init := GaudisCrypt.SHA3.IRO.IRO.init Bool (List Bool) valid dbool IRO.mp
noncomputable abbrev IRO.fill_in :=
  GaudisCrypt.SHA3.IRO.IRO.fill_in Bool (List Bool) valid dbool IRO.mp
noncomputable abbrev IRO.f := GaudisCrypt.SHA3.IRO.IRO.f Bool (List Bool) valid dbool IRO.mp
/-- `BIRO.IRO` as the functionality it is used as (its procedures `init` and `f`). -/
noncomputable def IRO.asF : FUNCTIONALITY :=
  Indifferentiability.FUNCTIONALITY.mk (block × capacity) (List Bool × ℤ) (List Bool)
    { init := IRO.init, f := IRO.f }
end BIRO

/-! ## The sponge construction -/

module StdSponge using (P : DPRIMITIVE) {
  proc init () : Unit {
    return ()
  };
  proc f (x : List Bool × ℤ) : (List Bool) {
    var bs : List Bool, n : ℤ, z : List Bool, sa : block, sc : capacity, finished : Bool,
      xs : List block;
    bs, n <- $x;
    z <- [];
    sa, sc <- (b0, Capacity.c0);
    finished <- false;
    xs <- pad2blocks $bs;
    -- absorption
    while (!(List.isEmpty $xs)) {
      sa, sc <- call P.f (($sa +^ head b0 $xs, $sc));
      xs <- behead $xs;
    }
    -- squeezing
    while (!$finished) {
      z <- $z ++ ofblock $sa;
      if (decide (size $z < $n)) {
        sa, sc <- call P.f (($sa, $sc));
      } else {
        finished <- true;
      }
    }
    return take $n $z
  };
}

module Sponge using (P : DPRIMITIVE) : FUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (x : List Bool × ℤ) : (List Bool) {
    var bs : List Bool, n : ℤ, z : List Bool, sa : block, sc : capacity, i : ℤ, xs : List block;
    bs, n <- $x;
    z <- [];
    sa, sc <- (b0, Capacity.c0);
    i <- 0;
    xs <- pad2blocks $bs;
    -- absorption
    while (!(List.isEmpty $xs)) {
      sa, sc <- call P.f (($sa +^ head b0 $xs, $sc));
      xs <- behead $xs;
    }
    -- squeezing
    while ($i < ($n + r - 1) / r) {
      z <- $z ++ ofblock $sa;
      i <- $i + 1;
      if ($i < ($n + r - 1) / r) {
        sa, sc <- call P.f (($sa, $sc));
      }
    }
    return take $n $z
  };
}

theorem loop_cond (i n : ℤ) : 0 ≤ i → 0 ≤ n → (r * i < n ↔ i < (n + r - 1) / r) := by
  intro _ _
  have hr := gt0_r
  rw [← Int.add_one_le_iff (b := (n + r - 1) / r), Int.le_ediv_iff_mul_le hr]
  constructor <;> intro h <;> nlinarith

/-! ## Simulator and distinguisher constructions -/

module LowerFun using (F : DFUNCTIONALITY) : BlockSponge.DFUNCTIONALITY {
  proc f (x : List block × ℤ) : (List block) {
    var xs : List block, n : ℤ, cs : List Bool, obs : Option (List Bool), ys : List block;
    xs, n <- $x;
    ys <- [];
    obs <- unpad_blocks $xs;
    if (decide ($obs ≠ none)) {
      cs <- call F.f ((oget $obs, $n * r)); -- size cs = n * r
      ys <- bits2blocks $cs; -- size ys = n
    }
    return $ys
  };
}

module RaiseFun using (F : BlockSponge.DFUNCTIONALITY) : DFUNCTIONALITY {
  proc f (x : List Bool × ℤ) : (List Bool) {
    var bs : List Bool, n : ℤ, xs : List block;
    bs, n <- $x;
    xs <- call F.f ((pad2blocks $bs, ($n + r - 1) / r));
    return take $n (blocks2bits $xs)
  };
}

-- EC's `LowerDist(D : DISTINGUISHER, F : BlockSponge.DFUNCTIONALITY) = D(RaiseFun(F))`, with `D`
-- a Lean parameter so that `LowerDist D` is a `BlockSponge.DISTINGUISHER`; the alias is wrapped
-- in a call (exception E5)
set_option linter.gaudisCrypt.using false in
module LowerDist (D : DISTINGUISHER)
    using (F : BlockSponge.DFUNCTIONALITY, P : BlockSponge.DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    b <- call (Module.app D (Module.pair (Module.app RaiseFun F)
      (Indifferentiability.DPRIMITIVE.mk (block × capacity) (List Bool × ℤ) (List Bool)
        { f := Indifferentiability.DPRIMITIVE.f (block × capacity) (List block × ℤ)
            (List block) P
          fi := Indifferentiability.DPRIMITIVE.fi (block × capacity) (List block × ℤ)
            (List block) P }))) ();
    return $b
  };
}

/-- `module RaiseSim (S : BlockSponge.SIMULATOR, F : DFUNCTIONALITY) = S(LowerFun(F))`, used as
`RaiseSim(S) : SIMULATOR`. -/
noncomputable def RaiseSim (S : BlockSponge.SIMULATOR) : SIMULATOR := Module.comp S LowerFun

/-! ## The abstract theory of hybrid IROs (`abstract theory HybridIRO`)

Hybrid IROs map a block list and an index to a bit.  The theory's module variables are lens
parameters: its one clone (`HIRO`, in the last section) passes its own. -/

namespace HybridIRO

moduletype HYBRID_IRO {
  -- initialization
  proc init () -> Unit;
  -- hashing block lists, giving `n` bits
  proc f (x : List block, n : ℤ) -> (List Bool);
}

/-- `module type HYBRID_IRO_DIST (HI : HYBRID_IRO) = { proc distinguish() : bool {HI.f} }`:
distinguisher for hybrid IROs. -/
abbrev HYBRID_IRO_DIST := HYBRID_IRO →ₘ procmod () → Bool

/-- The oracle procedure a `HYBRID_IRO_DIST` may call (EasyCrypt's `{HI.f}`): `HI.f`.  The hole of
its representation (`Module.Representable`, exception E2). -/
abbrev HYBRID_IRO_DIST.holes : HoleSigs := .cons (procsig (List block, ℤ) -> (List Bool)) .empty

-- Experiments for hybrid IROs
module HybridIROExper using (HI : HYBRID_IRO, D : HYBRID_IRO_DIST) {
  proc main () : Bool {
    var b : Bool;
    _ <- call HI.init ();
    b <- call (Module.app D HI) ();
    return $b
  };
}

section HybridIROLazy
/-! `HybridIROLazy`'s module variable `mp` is a parameter. -/
variable (HybridIROLazy_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)

-- Lazy implementation of hybrid IROs (EC: `module HybridIROLazy : HYBRID_IRO`; it has more
-- procedures than `HYBRID_IRO`, so no type annotation: `HybridIROLazy.asHI` is its view)
module HybridIROLazy {
  proc init () : Unit {
    HybridIROLazy_mp <- (FMap.empty : FMap (List block × ℤ) Bool);
    return ()
  };
  proc fill_in (xs : List block, i : ℤ) : Bool {
    var r : Bool;
    if (!(decide (FMap.dom ($HybridIROLazy_mp : FMap (List block × ℤ) Bool) ($xs, $i)))) {
      r <$ dbool;
      HybridIROLazy_mp <- FMap.set $HybridIROLazy_mp ($xs, $i) $r;
    }
    return oget (FMap.get $HybridIROLazy_mp ($xs, $i))
  };
  proc f (xs : List block, n : ℤ) : (List Bool) {
    var b : Bool, bs : List Bool, i : ℤ;
    i <- 0;
    bs <- [];
    if (decide (valid_block $xs)) {
      while ($i < $n) {
        b <- call (HybridIROLazy.fill_in HybridIROLazy_mp) ($xs, $i);
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
    }
    return $bs
  };
}

/-- `HybridIROLazy` at its type `HYBRID_IRO`. -/
noncomputable def HybridIROLazy.asHI : HYBRID_IRO :=
  HYBRID_IRO.mk
    { init := HybridIROLazy.init HybridIROLazy_mp, f := HybridIROLazy.f HybridIROLazy_mp }

end HybridIROLazy

section HybridIROEager
/-! `HybridIROEager`'s module variable `mp` is a parameter. -/
variable (HybridIROEager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)

-- Eager implementation of hybrid IROs: the lazy one, except that `f` also fills in the bits up to
-- the next multiple of `r` (EC: `module HybridIROEager : HYBRID_IRO`; no type annotation, as for
-- `HybridIROLazy`)
module HybridIROEager {
  proc init () : Unit {
    HybridIROEager_mp <- (FMap.empty : FMap (List block × ℤ) Bool);
    return ()
  };
  proc fill_in (xs : List block, i : ℤ) : Bool {
    var r : Bool;
    if (!(decide (FMap.dom ($HybridIROEager_mp : FMap (List block × ℤ) Bool) ($xs, $i)))) {
      r <$ dbool;
      HybridIROEager_mp <- FMap.set $HybridIROEager_mp ($xs, $i) $r;
    }
    return oget (FMap.get $HybridIROEager_mp ($xs, $i))
  };
  proc f (xs : List block, n : ℤ) : (List Bool) {
    var b : Bool, bs : List Bool, m : ℤ, i : ℤ;
    m <- ($n + r - 1) / r * r; -- eager part
    i <- 0;
    bs <- [];
    if (decide (valid_block $xs)) {
      while ($i < $n) {
        b <- call (HybridIROEager.fill_in HybridIROEager_mp) ($xs, $i);
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
      while ($i < $m) { -- eager part
        _ <- call (HybridIROEager.fill_in HybridIROEager_mp) ($xs, $i);
        i <- $i + 1;
      }
    }
    return $bs
  };
}

/-- `HybridIROEager` at its type `HYBRID_IRO`. -/
noncomputable def HybridIROEager.asHI : HYBRID_IRO :=
  HYBRID_IRO.mk
    { init := HybridIROEager.init HybridIROEager_mp, f := HybridIROEager.f HybridIROEager_mp }

end HybridIROEager

/-! ### Lazy = eager: EasyCrypt's section with `declare module D <: HYBRID_IRO_DIST
{-HybridIROEager, -HybridIROLazy}`

`local clone import PROM.FullRO as ERO with type in_t <- block list * int, type out_t <- bool,
op dout _ <- dbool, type d_in_t <- unit, type d_out_t <- bool`: the clone is local, so its module
variables `ERO.RO.m`, `ERO.FRO.m` are the lens parameters `ERO_RO_m`, `ERO_FRO_m` of the local
declarations, fresh for `D` by hypothesis (exception E6). -/

namespace ERO
noncomputable abbrev dout : List block × ℤ → SubProbability Bool := fun _ => dbool
abbrev RO_T := PROM.FullRO.RO_T (List block × ℤ) Bool
abbrev RO_Distinguisher := PROM.FullRO.RO_Distinguisher (List block × ℤ) Bool Unit Bool
noncomputable abbrev RO_ext := PROM.FullRO.RO_ext (List block × ℤ) Bool
section
variable (ERO_RO_m : Lens (FMap (List block × ℤ) Bool) VariableAssignment)
noncomputable abbrev RO := PROM.FullRO.RO.asRO (List block × ℤ) Bool dout ERO_RO_m
noncomputable abbrev LRO := PROM.FullRO.LRO (List block × ℤ) Bool dout ERO_RO_m
end
end ERO

section LazyEager

-- one binder each: a `module` takes a whole binder group when it mentions one of its names
variable (HybridIROLazy_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)
  (HybridIROEager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)

module EROExper using (O : ERO.RO_T, D : ERO.RO_Distinguisher) {
  proc main () : Bool {
    var b : Bool;
    _ <- call O.init ();
    b <- call (Module.app D O) (());
    return $b
  };
}

-- Make a hybrid IRO out of a random oracle (EC's local `HIRO(RO : ERO.RO) : HYBRID_IRO`)
module HIRO using (RO : ERO.RO_T) : HYBRID_IRO {
  proc init () : Unit {
    _ <- call RO.init ();
    return ()
  };
  proc f (xs : List block, n : ℤ) : (List Bool) {
    var b : Bool, bs : List Bool, m : ℤ, i : ℤ;
    m <- ($n + r - 1) / r * r;
    i <- 0;
    bs <- [];
    if (decide (valid_block $xs)) {
      while ($i < $n) {
        b <- call RO.get (($xs, $i));
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
      while ($i < $m) {
        _ <- call RO.sample (($xs, $i));
        i <- $i + 1;
      }
    }
    return $bs
  };
}

-- Make a distinguisher for random oracles out of `HIRO` and `D` (EC's local `RODist(RO : ERO.RO)`,
-- with the section's `D` a Lean parameter; its `distinguish` takes `RO_Distinguisher`'s `unit`)
set_option linter.gaudisCrypt.using false in
module RODist (D : HYBRID_IRO_DIST) using (RO : ERO.RO_T) {
  proc distinguish (_x : Unit) : Bool {
    var b : Bool;
    b <- call (Module.app D (Module.app HIRO RO)) ();
    return $b
  };
}

local notation "E" => FVP.fvpInductiveFunctionGS.evalMexpr

omit [BlockSponge.Params] in
/-- `HIRO` has no globals of its own. -/
theorem fvP_HIRO : FVP.fvP HIRO = ⊥ := by
  refine le_antisymm ?_ bot_le
  show E HIRO.expression ≤ ⊥
  unfold HIRO
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs, evalMexpr_pair, evalMexpr_app, evalMexpr_var, sup_bot_eq]
  refine sup_le ?_ ?_
  · unfold HIRO.init
    refine (evalMexpr_toModule_le _ _).trans ?_
    simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_fst, evalMexpr_var,
      evalMexpr_unit, sup_bot_eq]
    exact (evalMexpr_procWithHoles_le _).trans
      (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)
  · unfold HIRO.f
    refine (evalMexpr_toModule_le _ _).trans ?_
    simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_fst, evalMexpr_snd,
      evalMexpr_var, evalMexpr_unit, sup_bot_eq]
    exact (evalMexpr_procWithHoles_le _).trans
      (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)

/-- `RODist(D)` touches what `D` does. -/
theorem fvP_RODist_le (D : HYBRID_IRO_DIST) : FVP.fvP (RODist D) ≤ FVP.fvP D := by
  show E (RODist D).expression ≤ E D.expression
  unfold RODist
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_var, sup_bot_eq]
  unfold RODist.distinguish
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_var, evalMexpr_unit,
    sup_bot_eq]
  refine sup_le ((evalMexpr_procWithHoles_le _).trans
    (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)) (sup_le le_rfl ?_)
  exact (show E HIRO.expression = ⊥ from fvP_HIRO).le.trans bot_le

end LazyEager

section Hybrid

variable (HybridIROEager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)

-- Turn a hybrid IRO implementation (lazy or eager) into the top-level ideal functionality
module RaiseHybridIRO using (HI : HYBRID_IRO) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call HI.init ();
    return ()
  };
  proc f (x : List Bool × ℤ) : (List Bool) {
    var bs : List Bool, n : ℤ, cs : List Bool;
    bs, n <- $x;
    cs <- call HI.f (pad2blocks $bs, $n);
    return $cs
  };
}

-- Turn a hybrid IRO implementation (lazy or eager) into the lower-level ideal distinguisher
-- functionality
module LowerHybridIRO using (HI : HYBRID_IRO) : BlockSponge.DFUNCTIONALITY {
  proc f (x : List block × ℤ) : (List block) {
    var xs : List block, n : ℤ, bs : List Bool, ys : List block;
    xs, n <- $x;
    bs <- call HI.f ($xs, $n * r);
    ys <- bits2blocks $bs;
    return $ys
  };
}

/-- Invariant relating the maps of `BIRO.IRO` and `HybridIROLazy`. -/
def lazy_invar (mp1 : FMap (List Bool × ℤ) Bool) (mp2 : FMap (List block × ℤ) Bool) : Prop :=
  (∀ (bs : List Bool) (n : ℤ), FMap.dom mp1 (bs, n) ↔ FMap.dom mp2 (pad2blocks bs, n)) ∧
  (∀ (xs : List block) (n : ℤ), FMap.dom mp2 (xs, n) → valid_block xs) ∧
  (∀ (bs : List Bool) (n : ℤ), FMap.dom mp1 (bs, n) →
    oget (FMap.get mp1 (bs, n)) = oget (FMap.get mp2 (pad2blocks bs, n)))

theorem lazy_invar0 : lazy_invar FMap.empty FMap.empty :=
  ⟨fun _ _ => iff_of_false (FMap.mem_empty _) (FMap.mem_empty _),
    fun _ _ h => absurd h (FMap.mem_empty _), fun _ _ h => absurd h (FMap.mem_empty _)⟩

theorem lazy_invar_mem_pad2blocks_l2r (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs : List Bool) (i : ℤ) :
    lazy_invar mp1 mp2 → FMap.dom mp1 (bs, i) → FMap.dom mp2 (pad2blocks bs, i) :=
  fun li h => (li.1 bs i).mp h

theorem lazy_invar_mem_pad2blocks_r2l (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs : List Bool) (i : ℤ) :
    lazy_invar mp1 mp2 → FMap.dom mp2 (pad2blocks bs, i) → FMap.dom mp1 (bs, i) :=
  fun li h => (li.1 bs i).mpr h

theorem lazy_invar_vb (mp1 : FMap (List Bool × ℤ) Bool) (mp2 : FMap (List block × ℤ) Bool)
    (xs : List block) (n : ℤ) :
    lazy_invar mp1 mp2 → FMap.dom mp2 (xs, n) → valid_block xs :=
  fun li h => li.2.1 xs n h

theorem lazy_invar_lookup_eq (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs : List Bool) (n : ℤ) :
    lazy_invar mp1 mp2 → FMap.dom mp1 (bs, n) →
    oget (FMap.get mp1 (bs, n)) = oget (FMap.get mp2 (pad2blocks bs, n)) :=
  fun li h => li.2.2 bs n h

theorem lazy_invar_upd_mem_dom_iff (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs cs : List Bool) (n m : ℤ) (b : Bool) :
    lazy_invar mp1 mp2 →
    (FMap.dom (FMap.set mp1 (bs, n) b) (cs, m) ↔
      FMap.dom (FMap.set mp2 (pad2blocks bs, n) b) (pad2blocks cs, m)) := by
  intro li
  rw [FMap.mem_set, FMap.mem_set, li.1 cs m]
  simp only [Prod.mk.injEq]
  constructor
  · rintro (h | ⟨rfl, rfl⟩) <;> simp_all
  · rintro (h | ⟨h1, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨pad2blocks_inj h1, rfl⟩

theorem lazy_invar_upd2_vb (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs : List Bool) (xs : List block) (n m : ℤ) (b : Bool) :
    lazy_invar mp1 mp2 → FMap.dom (FMap.set mp2 (pad2blocks bs, n) b) (xs, m) →
    valid_block xs := by
  intro li h
  rcases (FMap.mem_set _ _ _ _).mp h with h | h
  · exact li.2.1 xs m h
  · simp only [Prod.mk.injEq] at h
    rw [h.1]; exact valid_pad2blocks bs

theorem lazy_invar_upd_lu_eq (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs cs : List Bool) (n m : ℤ) (b : Bool) :
    lazy_invar mp1 mp2 → FMap.dom (FMap.set mp1 (bs, n) b) (cs, m) →
    oget (FMap.get (FMap.set mp1 (bs, n) b) (cs, m)) =
      oget (FMap.get (FMap.set mp2 (pad2blocks bs, n) b) (pad2blocks cs, m)) := by
  intro li h
  rw [FMap.get_setE, FMap.get_setE]
  by_cases hc : (cs, m) = (bs, n)
  · simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp
  · have hp : (pad2blocks cs, m) ≠ (pad2blocks bs, n) := fun h' => hc (by
      simp only [Prod.mk.injEq] at h' ⊢; exact ⟨pad2blocks_inj h'.1, h'.2⟩)
    rw [if_neg hc, if_neg hp]
    rcases (FMap.mem_set _ _ _ _).mp h with h | h
    · exact li.2.2 cs m h
    · exact absurd h hc

/-- Invariant relating the maps of `BlockSponge.BIRO.IRO` and `HybridIROEager`. -/
def eager_invar (mp1 : FMap (List block × ℤ) block) (mp2 : FMap (List block × ℤ) Bool) : Prop :=
  (∀ (xs : List block) (i : ℤ), FMap.dom mp1 (xs, i) →
    0 ≤ i ∧
    ∀ (j : ℤ), i * r ≤ j ∧ j < (i + 1) * r →
      FMap.get mp2 (xs, j) = some (nth false (ofblock (oget (FMap.get mp1 (xs, i)))) (j - i * r))) ∧
  (∀ (xs : List block) (j : ℤ), FMap.dom mp2 (xs, j) → FMap.dom mp1 (xs, j / r))

def block_bits_all_in_dom (xs : List block) (i : ℤ) (mp : FMap (List block × ℤ) Bool) : Prop :=
  ∀ (j : ℤ), i ≤ j ∧ j < i + r → FMap.dom mp (xs, j)

def block_bits_all_out_dom (xs : List block) (i : ℤ) (mp : FMap (List block × ℤ) Bool) : Prop :=
  ∀ (j : ℤ), i ≤ j ∧ j < i + r → ¬ FMap.dom mp (xs, j)

def block_bits_dom_all_in_or_out (xs : List block) (i : ℤ) (mp : FMap (List block × ℤ) Bool) :
    Prop :=
  block_bits_all_in_dom xs i mp ∨ block_bits_all_out_dom xs i mp

omit [BlockSponge.Params] in
/-- `j / r = i` for `j` in the `i`th block of bits.  Not an EC lemma (EC: `divzDl`,
`divz_small`). -/
theorem div_r_eq {i j : ℤ} (h1 : i * r ≤ j) (h2 : j < (i + 1) * r) : j / r = i := by
  have hr := gt0_r
  have a := (Int.le_ediv_iff_mul_le hr).mpr h1
  have b := (Int.ediv_lt_iff_lt_mul hr).mpr h2
  omega

theorem eager_inv_mem_mp1_ge0 (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) :
    eager_invar mp1 mp2 → FMap.dom mp1 (xs, i) → 0 ≤ i :=
  fun ei h => (ei.1 xs i h).1

theorem eager_inv_mem_mp2_ge0 (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (j : ℤ) :
    eager_invar mp1 mp2 → FMap.dom mp2 (xs, j) → 0 ≤ j := by
  intro ei h
  have := (ei.1 xs (j / r) (ei.2 xs j h)).1
  simpa using (Int.le_ediv_iff_mul_le gt0_r).mp this

theorem eager_invar0 : eager_invar FMap.empty FMap.empty :=
  ⟨fun _ _ h => absurd h (FMap.mem_empty _), fun _ _ h => absurd h (FMap.mem_empty _)⟩

theorem eager_inv_imp_block_bits_dom (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) :
    0 ≤ i → r ∣ i → eager_invar mp1 mp2 → block_bits_dom_all_in_or_out xs i mp2 := by
  intro _ hdvd ei
  obtain ⟨k, rfl⟩ := hdvd
  rw [mul_comm]
  by_cases h : FMap.dom mp1 (xs, k)
  · left
    intro j hj
    rw [FMap.domE, (ei.1 xs k h).2 j ⟨hj.1, by nlinarith [hj.2]⟩]
    simp
  · right
    intro j hj hd
    have := ei.2 xs j hd
    rw [div_r_eq hj.1 (by nlinarith [hj.2])] at this
    exact h this

theorem eager_inv_mem_dom1 (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) :
    eager_invar mp1 mp2 → FMap.dom mp1 (xs, i) → block_bits_all_in_dom xs (i * r) mp2 := by
  intro ei h j hj
  rw [FMap.domE, (ei.1 xs i h).2 j ⟨hj.1, by nlinarith [hj.2]⟩]
  simp

theorem eager_inv_not_mem_dom1 (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) :
    eager_invar mp1 mp2 → 0 ≤ i → ¬ FMap.dom mp1 (xs, i) →
    block_bits_all_out_dom xs (i * r) mp2 := by
  intro ei _ h j hj hd
  have := ei.2 xs j hd
  rw [div_r_eq hj.1 (by nlinarith [hj.2])] at this
  exact h this

theorem block_bits_dom_first_in_imp_all_in (xs : List block) (i : ℤ)
    (mp : FMap (List block × ℤ) Bool) :
    block_bits_dom_all_in_or_out xs i mp → FMap.dom mp (xs, i) →
    block_bits_all_in_dom xs i mp := by
  rintro (h | h) hd
  · exact h
  · exact absurd hd (h i ⟨le_rfl, by have := gt0_r; omega⟩)

theorem block_bits_dom_first_out_imp_all_out (xs : List block) (i : ℤ)
    (mp : FMap (List block × ℤ) Bool) :
    block_bits_dom_all_in_or_out xs i mp → ¬ FMap.dom mp (xs, i) →
    block_bits_all_out_dom xs i mp := by
  rintro (h | h) hd
  · exact absurd (h i ⟨le_rfl, by have := gt0_r; omega⟩) hd
  · exact h

-- Module needed for applying the transitivity tactic in connection with `HybridIROEager`
module HybridIROEagerTrans {
  -- getting the next block of bits; assuming `m = i + r` and `size bs = i`
  proc next_block (xs : List block, i : ℤ, m : ℤ, bs : List Bool) : (List Bool × ℤ) {
    var b : Bool;
    while ($i < $m) {
      b <- call (HybridIROEager.fill_in HybridIROEager_mp) ($xs, $i);
      bs <- rcons $bs $b;
      i <- $i + 1;
    }
    return ($bs, $i)
  };
  -- `next_block` split into cases; assuming `m = i + r`, `size bs = i` and
  -- `block_bits_dom_all_in_or_out xs i HybridIROEager.mp`
  proc next_block_split (xs : List block, i : ℤ, m : ℤ, bs : List Bool) : (List Bool × ℤ) {
    var b : Bool, j : ℤ, cs : List Bool;
    if (decide (FMap.dom ($HybridIROEager_mp : FMap (List block × ℤ) Bool) ($xs, $i))) {
      while ($i < $m) {
        b <- oget (FMap.get ($HybridIROEager_mp : FMap (List block × ℤ) Bool) ($xs, $i));
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
    } else {
      j <- 0;
      cs <- [];
      while ($j < r) {
        b <$ dbool;
        cs <- rcons $cs $b;
        j <- $j + 1;
      }
      bs <- $bs ++ $cs;
      while ($i < $m) {
        HybridIROEager_mp <- FMap.set $HybridIROEager_mp ($xs, $i) (nth true $bs $i);
        i <- $i + 1;
      }
    }
    return ($bs, $i)
  };
  -- loop getting `n * r` bits of hash
  proc loop (n : ℤ, xs : List block) : (ℤ × List Bool) {
    var b : Bool, i : ℤ, bs : List Bool;
    i <- 0;
    bs <- [];
    while ($i < $n * r) {
      b <- call (HybridIROEager.fill_in HybridIROEager_mp) ($xs, $i);
      bs <- rcons $bs $b;
      i <- $i + 1;
    }
    return ($i, $bs)
  };
}

/-- Two maps are the same except (perhaps) on a range of bits for a single block list. -/
def eager_eq_except (xs : List block) (i j : ℤ) (mp1 mp2 : FMap (List block × ℤ) Bool) : Prop :=
  ∀ (ys : List block) (k : ℤ), ys ≠ xs ∨ k < i ∨ j ≤ k → FMap.get mp1 (ys, k) = FMap.get mp2 (ys, k)

theorem eager_eq_except_mem_iff (xs ys : List block) (i j k : ℤ)
    (mp1 mp2 : FMap (List block × ℤ) Bool) :
    eager_eq_except xs i j mp1 mp2 → ys ≠ xs ∨ k < i ∨ j ≤ k →
    (FMap.dom mp1 (ys, k) ↔ FMap.dom mp2 (ys, k)) := by
  intro h hk
  rw [FMap.domE, FMap.domE, h ys k hk]

theorem eager_eq_except_upd1_eq_in (xs : List block) (i j k : ℤ) (y : Bool)
    (mp1 mp2 : FMap (List block × ℤ) Bool) :
    eager_eq_except xs i j mp1 mp2 → i ≤ k → k < j →
    eager_eq_except xs i j (FMap.set mp1 (xs, k) y) mp2 := by
  intro h hik hkj ys l hl
  rw [FMap.get_setE,
    if_neg (by rintro ⟨⟩; rcases hl with h' | h' | h' <;> first | exact h' rfl | omega),
    h ys l hl]

theorem eager_eq_except_upd2_eq_in (xs : List block) (i j k : ℤ) (y : Bool)
    (mp1 mp2 : FMap (List block × ℤ) Bool) :
    eager_eq_except xs i j mp1 mp2 → i ≤ k → k < j →
    eager_eq_except xs i j mp1 (FMap.set mp2 (xs, k) y) := by
  intro h hik hkj ys l hl
  rw [FMap.get_setE,
    if_neg (by rintro ⟨⟩; rcases hl with h' | h' | h' <;> first | exact h' rfl | omega),
    h ys l hl]

theorem eager_eq_except_maps_eq (xs : List block) (i j : ℤ) (_y : Bool)
    (mp1 mp2 : FMap (List block × ℤ) Bool) :
    i ≤ j → eager_eq_except xs i j mp1 mp2 →
    (∀ (k : ℤ), i ≤ k ∧ k < j → FMap.get mp1 (xs, k) = FMap.get mp2 (xs, k)) → mp1 = mp2 := by
  intro _ h hr
  refine (FMap.fmap_eqP _ _).mp fun ⟨ys, k⟩ => ?_
  by_cases hys : ys = xs
  · subst hys
    by_cases hk : i ≤ k ∧ k < j
    · exact hr k hk
    · exact h ys k (Or.inr (by omega))
  · exact h ys k (Or.inl hys)

theorem eager_invar_eq_except_upd1 (mp1 : FMap (List block × ℤ) block)
    (mp2 mp2' : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) (y : block) :
    0 ≤ i → eager_invar mp1 mp2 → eager_eq_except xs (i * r) ((i + 1) * r) mp2 mp2' →
    (∀ (j : ℤ), i * r ≤ j ∧ j < (i + 1) * r →
      FMap.get mp2' (xs, j) = some (nth false (ofblock y) (j - i * r))) →
    eager_invar (FMap.set mp1 (xs, i) y) mp2' := by
  intro hi ei ee hran
  have hr := gt0_r
  refine ⟨fun ys k hd => ?_, fun ys j hd => ?_⟩
  · by_cases hyk : (ys, k) = (xs, i)
    · simp only [Prod.mk.injEq] at hyk
      obtain ⟨rfl, rfl⟩ := hyk
      refine ⟨hi, fun j hj => ?_⟩
      rw [FMap.get_set_sameE]
      exact hran j hj
    · have hd1 : FMap.dom mp1 (ys, k) := ((FMap.mem_set _ _ _ _).mp hd).resolve_right hyk
      obtain ⟨hk, hb⟩ := ei.1 ys k hd1
      refine ⟨hk, fun j hj => ?_⟩
      rw [FMap.get_setE, if_neg hyk, ← hb j hj]
      refine (ee ys j ?_).symm
      by_cases hys : ys = xs
      · subst hys
        have hki : k ≠ i := fun h => hyk (by rw [h])
        rcases lt_or_gt_of_ne hki with hlt | hgt
        · exact Or.inr (Or.inl (by nlinarith [hj.2]))
        · exact Or.inr (Or.inr (by nlinarith [hj.1]))
      · exact Or.inl hys
  · rw [FMap.mem_set]
    by_cases hex : ys ≠ xs ∨ j < i * r ∨ (i + 1) * r ≤ j
    · left
      apply ei.2
      rw [FMap.domE] at hd ⊢
      rwa [ee ys j hex]
    · right
      simp only [ne_eq, not_or, not_not, not_lt] at hex
      obtain ⟨rfl, h1, h2⟩ := hex
      rw [div_r_eq h1 (by omega)]

-- Module needed for applying the transitivity tactic in connection with `BlockSponge.BIRO.IRO`
module BlockSpongeTrans {
  -- getting the next block; assumes `size bs = i`
  proc next_block (x : List block, i : ℤ, bs : List block) : (List block × ℤ) {
    var b : block;
    b <- call BlockSponge.BIRO.IRO.fill_in ($x, $i);
    bs <- rcons $bs $b;
    i <- $i + 1;
    return ($bs, $i)
  };
  -- loop getting `n` blocks
  proc loop (n : ℤ, xs : List block) : (ℤ × List block) {
    var b : block, i : ℤ, bs : List block;
    i <- 0;
    bs <- [];
    while ($i < $n) {
      b <- call BlockSponge.BIRO.IRO.fill_in ($xs, $i);
      bs <- rcons $bs $b;
      i <- $i + 1;
    }
    return ($i, $bs)
  };
}

/-! `clone Program as Prog with type t = bool, op d = {0,1}` (the `Program` abstract theory of
`DList`) -/

namespace Prog
noncomputable abbrev LoopSnoc.sample := DList.Program.LoopSnoc.sample Bool dbool
end Prog

theorem PrLoopSnoc_sample (m : VariableAssignment) (bs : List Bool) :
    (Procedure.Pr Prog.LoopSnoc.sample.procedure r m (fun res _ => res = bs) : ENNReal) =
      (dlist dbool r).1 {bs} :=
  -- EC: `Sample_LoopSnoc_eq` then `pr_Sample`, together `LoopSnoc.pr_sample`
  DList.Program.LoopSnoc.pr_sample Bool dbool r m bs

theorem iter_mul_one_half_pos (n : ℤ) :
    0 < n → iter n ((1 / 2 : ℝ) * ·) 1 = (((2 ^ n.toNat : ℤ) : ℝ))⁻¹ := by
  intro _
  have h : ∀ k : ℕ, ((1 / 2 : ℝ) * ·)^[k] 1 = ((2 : ℝ) ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ]; field_simp
  simp only [iter, h]
  push_cast
  rfl

-- Module for adapting `PrLoopSnoc_sample` to block generation
module BlockGen {
  proc loop () : block {
    var b : Bool, j : ℤ, cs : List Bool;
    j <- 0;
    cs <- [];
    while ($j < r) {
      b <$ dbool;
      cs <- rcons $cs $b;
      j <- $j + 1;
    }
    return mkblock $cs
  };
  proc direct () : block {
    var w : block;
    w <$ bdistr;
    return $w
  };
}

omit [BlockSponge.Params] in
open Classical in
/-- `bdistr` is `r` fair bits made a block (in EC's `BlockGen_loop_direct`: `mu1 bdistr w =
1 / 2 ^ r`, and the same for the bits of `w` under `dlist {0,1} r`). -/
theorem bdistr_dlist : bdistr = (dlist dbool r).hbind fun l => pure (mkblock l) := by
  have hr := gt0_r
  refine eq_distr fun w => ?_
  symm
  rw [mu1_eq_expected, SubProbability.expected_hbind]
  simp only [expected_pure]
  have hlen : ((ofblock w).length : ℤ) = r := by
    have := BitWord.size_word hr.le w
    simpa [size, ofblock] using this
  change ∫⁻ l, _ ∂(dlist dbool r).1 = _
  rw [lintegral_eq_tsum_smul (dlist dbool r).2.2, tsum_eq_single (ofblock w) ?_]
  · rw [show mkblock (ofblock w) = w from BitWord.mkwordK w, if_pos rfl, mul_one,
      dlist1E _ _ _ hlen]
    simp only [dbool1E, List.map_const', List.prod_replicate]
    letI : MeasurableSpace block := ⊤
    change _ = (PMF.uniformOfFintype block).toMeasure {w}
    rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton w)]
    simp only [PMF.uniformOfFintype_apply, card_vector, Fintype.card_bool, Nat.cast_pow,
      ENNReal.inv_pow]
    congr 1
    omega
  · intro l hl
    by_cases hl' : (l.length : ℤ) = r
    · rw [if_neg]; · simp
      rintro rfl
      exact hl (BitWord.ofwordK l (by simp [size]; omega)).symm
    · rw [dlist_supp _ _ _ (by omega), zero_mul]

-- Auxiliary (not in EC): `BlockGen.loop` with its loop the call `Prog.LoopSnoc.sample(r)`, for
-- EC's `byequiv` step of `BlockGen_loop_direct`
module BlockGenCall {
  proc loop () : block {
    var cs : List Bool;
    cs <- call Prog.LoopSnoc.sample (r);
    return mkblock $cs
  };
}

/-- EC's `byequiv` step of `BlockGen_loop_direct`: `BlockGen.loop`'s loop is
`Prog.LoopSnoc.sample(r)`'s. -/
theorem BlockGen_loop_BlockGenCall (P : VariableAssignment → VariableAssignment → Prop) :
    prhlProc (fun _ g₁ _ g₂ => P g₁ g₂) BlockGen.loop.procedure BlockGenCall.loop.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ P g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§j{1} = §i{2} ∧ §cs{1} = §(localVarLens "l" (List Bool)){2} ∧ §n{2} = r ∧
      P §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_while_raw (§j{1} = §i{2} ∧ §cs{1} = §(localVarLens "l" (List Bool)){2} ∧ §n{2} = r ∧
        P §allGlobals{1} §allGlobals{2})
    case body =>
      stmt_wp
      equiv_rnd
      equiv_skip
      intros; simp_all [rcons]
    case guard => intros; simp_all
    case exit => intros; simp_all
    · equiv_skip; intros; simp_all

/-- `BlockGen.direct` against `BlockGenCall.loop`: the bits from `LoopSnoc.sample` are `dlist {0,1}
r` (`LoopSnoc.sample_denotation`), whose image by `mkblock` is `bdistr` (`bdistr_dlist`). -/
theorem BlockGen_direct_BlockGenCall (P : VariableAssignment → VariableAssignment → Prop) :
    prhlProc (fun _ g₁ _ g₂ => P g₁ g₂) BlockGen.direct.procedure BlockGenCall.loop.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ P g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  stmt_split{1} 1
  stmt_split{2} 1
  refine prhlStmt_seq_sample_run_map_right (x₂ := liftLens (localVarLens "cs" (List Bool)))
    (fun _ _ => dlist dbool r) mkblock ?_
  stmt_wp
  equiv_skip
  intro τ _ hP
  refine ⟨?_, bdistr_dlist, fun _ _ => hP⟩
  generalize (resetSetter _).set () τ = σ
  refine (programDenotation_call_apply _ _ _ σ).trans ?_
  erw [DList.Program.LoopSnoc.sample_denotation]
  refine SubProbability.ext_of_expected fun F => ?_
  simp only [SubProbability.expected_hbind, expected_pure]
  rw [show ProgramState.globalL.set σ.globals σ = σ from ProgramState.globalL.get_set σ]

/-- `lemma BlockGen_loop_direct : equiv[BlockGen.loop ~ BlockGen.direct : true ==> ={res}]`.
EC: `bypr`, comparing `Pr[_ : res = w]` (`PrLoopSnoc_sample`, `iter_mul_one_half_pos`); here the
two equivalences above, composed (the same facts as distributions). -/
theorem BlockGen_loop_direct :
    prhlProc (fun _ _ _ _ => True) BlockGen.loop.procedure BlockGen.direct.procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) :=
  prhlProc_conseq (prhlProc.trans (BlockGen_loop_BlockGenCall fun _ _ => True)
      (prhlProc.symm (BlockGen_direct_BlockGenCall fun _ _ => True)))
    (fun _ g _ _ _ => ⟨(), g, trivial, trivial⟩)
    (fun _ _ _ _ ⟨_, _, h, h'⟩ => h.1.trans h'.1.symm)

end Hybrid

end HybridIRO

/-! ## The main result: EasyCrypt's section with `declare module BlockSim <: BlockSponge.SIMULATOR
{-IRO, -BlockSponge.BIRO.IRO}` and `declare module Dist <: DISTINGUISHER {-Perm, -BlockSim, -IRO,
-BlockSponge.BIRO.IRO}`

`local clone HybridIRO as HIRO`: the clone is local, so its module variables
`HIRO.HybridIROLazy.mp`, `HIRO.HybridIROEager.mp` are the lens parameters `HIRO_Lazy_mp`,
`HIRO_Eager_mp` of the local declarations that mention them, fresh by hypothesis (`HIRO_fresh`,
exception E6).  `HIRO.X` is `HybridIRO.X` at these lenses. -/

section Main

/-! ### The ideal side -/

-- Make a hybrid IRO distinguisher from `BlockSim` and `Dist` (`HI.f` is used by `BlockSim`, and
-- by `HIRO.RaiseHybridIRO`; `HI.init` is unused).  EC's local
-- `(HybridIRODist : HIRO.HYBRID_IRO_DIST) (HI : HIRO.HYBRID_IRO)`, with the section's `BlockSim`,
-- `Dist` Lean parameters.
set_option linter.gaudisCrypt.using false in
module HybridIRODist (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    using (HI : HybridIRO.HYBRID_IRO) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call (Indifferentiability.PRIMITIVE.init (block × capacity) (List block × ℤ) (List block)
      (Module.app BlockSim (Module.app HybridIRO.LowerHybridIRO HI))) ();
    b <- call (Module.app Dist (Module.pair
      (Indifferentiability.DFUNCTIONALITY.mk (block × capacity) (List Bool × ℤ) (List Bool)
        { f := Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
            (Module.app HybridIRO.RaiseHybridIRO HI) })
      (Indifferentiability.DPRIMITIVE.mk (block × capacity) (List Bool × ℤ) (List Bool)
        { f := Indifferentiability.PRIMITIVE.f (block × capacity) (List block × ℤ) (List block)
            (Module.app BlockSim (Module.app HybridIRO.LowerHybridIRO HI))
          fi := Indifferentiability.PRIMITIVE.fi (block × capacity) (List block × ℤ) (List block)
            (Module.app BlockSim (Module.app HybridIRO.LowerHybridIRO HI)) }))) ();
    return $b
  };
}

local notation "E" => FVP.fvpInductiveFunctionGS.evalMexpr

omit [BlockSponge.Params] in
/-- `LowerHybridIRO` has no globals of its own. -/
theorem fvP_LowerHybridIRO : FVP.fvP HybridIRO.LowerHybridIRO = ⊥ := by
  refine le_antisymm ?_ bot_le
  show E HybridIRO.LowerHybridIRO.expression ≤ ⊥
  unfold HybridIRO.LowerHybridIRO
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_var, sup_bot_eq]
  unfold HybridIRO.LowerHybridIRO.f
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_snd, evalMexpr_var,
    evalMexpr_unit, sup_bot_eq]
  exact (evalMexpr_procWithHoles_le _).trans
    (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)

omit [BlockSponge.Params] in
/-- `RaiseHybridIRO` has no globals of its own. -/
theorem fvP_RaiseHybridIRO : FVP.fvP HybridIRO.RaiseHybridIRO = ⊥ := by
  refine le_antisymm ?_ bot_le
  show E HybridIRO.RaiseHybridIRO.expression ≤ ⊥
  unfold HybridIRO.RaiseHybridIRO
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs]
  refine sup_le ?_ ?_
  · unfold HybridIRO.RaiseHybridIRO.init
    show E (ModuleExpression.app _ _) ≤ ⊥
    simp only [evalMexpr_app, evalMexpr_var, sup_bot_eq]
    refine (evalMexpr_toModule_le _ _).trans ?_
    simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_fst, evalMexpr_var,
      evalMexpr_unit, sup_bot_eq]
    exact (evalMexpr_procWithHoles_le _).trans
      (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)
  · unfold HybridIRO.RaiseHybridIRO.f
    show E (ModuleExpression.app _ _) ≤ ⊥
    simp only [evalMexpr_app, evalMexpr_var, sup_bot_eq]
    refine (evalMexpr_toModule_le _ _).trans ?_
    simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_snd, evalMexpr_var,
      evalMexpr_unit, sup_bot_eq]
    exact (evalMexpr_procWithHoles_le _).trans
      (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)

/-- `HybridIRODist` touches what `BlockSim` and `Dist` do. -/
theorem fvP_HybridIRODist_le (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER) :
    FVP.fvP (HybridIRODist BlockSim Dist) ≤ FVP.fvP BlockSim ⊔ FVP.fvP Dist := by
  show E (HybridIRODist BlockSim Dist).expression ≤ E BlockSim.expression ⊔ E Dist.expression
  unfold HybridIRODist
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_var, sup_bot_eq]
  unfold HybridIRODist.distinguish
  refine (evalMexpr_toModule_le _ _).trans ?_
  have hL : E HybridIRO.LowerHybridIRO.expression = ⊥ := fvP_LowerHybridIRO
  have hR : E HybridIRO.RaiseHybridIRO.expression = ⊥ := fvP_RaiseHybridIRO
  simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_fst, evalMexpr_snd,
    evalMexpr_var, evalMexpr_unit, sup_bot_eq, hL, hR]
  refine sup_le ((evalMexpr_procWithHoles_le _).trans
    (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)) ?_
  exact sup_le le_sup_left (sup_le le_sup_right (sup_le bot_le (sup_le le_sup_left le_sup_left)))

end Main

end GaudisCrypt.SHA3.Sponge
