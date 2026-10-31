import GaudisCrypt.Examples.SHA3.BlockSponge
import GaudisCrypt.Lib.EC.PROM
import GaudisCrypt.Lib.EC.DList
import GaudisCrypt.Lib.EC.Int
import GaudisCrypt.Logic.PRHLWp

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
abbrev distHoles := Indifferentiability.distHoles (block × capacity) (List Bool × ℤ) (List Bool)
noncomputable abbrev distExt :=
  Indifferentiability.distExt (block × capacity) (List Bool × ℤ) (List Bool)

/-- `={glob M}`: agreement on what `M` may touch (an abbreviation, not an EasyCrypt
declaration). -/
def eqGlob {M : Type 1} [IsModule M] (X : M) (g₁ g₂ : VariableAssignment) : Prop :=
  (FVP.fvP X).touched_getter.get g₁ = (FVP.fvP X).touched_getter.get g₂

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
  sorry

/-- `equiv Sponge_is_StdSponge (P <: DPRIMITIVE) : StdSponge(P).f ~ Sponge(P).f :
={glob P, bs, n} ==> ={glob P, res}`. -/
theorem Sponge_is_StdSponge (P : DPRIMITIVE) :
    prhlProc (fun a₁ g₁ a₂ g₂ => eqGlob P g₁ g₂ ∧ a₁ = a₂)
      (Module.app StdSponge.f P).procedure (Module.app Sponge.f P).procedure
      (fun r₁ g₁ r₂ g₂ => eqGlob P g₁ g₂ ∧ r₁ = r₂) := by
  sorry

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

/-- `HI.f` out of the oracle `HI`. -/
noncomputable def HYBRID_IRO_DIST.ext (HI : HYBRID_IRO) : HYBRID_IRO_DIST.holes.Instantiation :=
  (HYBRID_IRO.f HI).procedure

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
  (ERO_RO_m : Lens (FMap (List block × ℤ) Bool) VariableAssignment)
  (ERO_FRO_m : Lens (FMap (List block × ℤ) (Bool × flag)) VariableAssignment)

/-- The section's restriction `{-HybridIROEager, -HybridIROLazy}` (an abbreviation). -/
def DRestrictions (D : HYBRID_IRO_DIST) : Prop :=
  FVP.fvP D ≤ (HybridIROEager_mp.footprint ⊔ HybridIROLazy_mp.footprint)ᶜ

module EROExper using (O : ERO.RO_T, D : ERO.RO_Distinguisher) {
  proc main () : Bool {
    var b : Bool;
    _ <- call O.init ();
    b <- call (Module.app D O) (());
    return $b
  };
}

/-- `local lemma LRO_RO (D <: ERO.RO_Distinguisher {-ERO.RO, -ERO.FRO}) &m`. -/
theorem LRO_RO (D : ERO.RO_Distinguisher) (hD : Module.ECModule D ERO.RO_ext)
    (_hDd : FVP.fvP D ≤ (ERO_RO_m.footprint ⊔ ERO_FRO_m.footprint)ᶜ) (m : VariableAssignment) :
    Procedure.Pr (Module.app EROExper (Module.pair (ERO.LRO ERO_RO_m) D)).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (Module.app EROExper (Module.pair (ERO.RO ERO_RO_m) D)).procedure () m
        (fun r _ => r = true) := by
  sorry

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

/-- `local lemma HybridIROLazy_HIRO_LRO_init : equiv[HybridIROLazy.init ~ HIRO(LRO).init :
true ==> HybridIROLazy.mp{1} = ERO.RO.m{2}]`. -/
theorem HybridIROLazy_HIRO_LRO_init :
    prhlProc (fun _ _ _ _ => True)
      (HybridIROLazy.init HybridIROLazy_mp).procedure
      (Module.app HIRO.init (ERO.LRO ERO_RO_m)).procedure
      (fun _ g₁ _ g₂ => HybridIROLazy_mp.get g₁ = ERO_RO_m.get g₂) := by
  sorry

/-- `local lemma HybridIROLazy_fill_in_LRO_get : equiv[HybridIROLazy.fill_in ~ LRO.get :
(xs, i){1} = x{2} /\ HybridIROLazy.mp{1} = ERO.RO.m{2} ==>
={res} /\ HybridIROLazy.mp{1} = ERO.RO.m{2}]`. -/
theorem HybridIROLazy_fill_in_LRO_get :
    prhlProc (sig₁ := procsig (List block, ℤ) -> Bool)
      (sig₂ := procsig (List block × ℤ) -> Bool)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ HybridIROLazy_mp.get g₁ = ERO_RO_m.get g₂)
      (HybridIROLazy.fill_in HybridIROLazy_mp).procedure
      (PROM.FullRO.RO_T.get (List block × ℤ) Bool (ERO.LRO ERO_RO_m)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ HybridIROLazy_mp.get g₁ = ERO_RO_m.get g₂) := by
  -- EC: `case (dom mp (xs, i)); rcondf{1} 1; rcondf{2} 2; rnd{2} …; rcondt{1} 1; rcondt{2} 2;
  -- wp; rnd`: here the case split is `equiv_if{1}` on the lazy test
  equiv_proc
  repeat stmt_inline{2} 0
  stmt_inline{1} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{2} = (§xs0{1}, §i0{1}) ∧ §HybridIROLazy_mp{1} = §ERO_RO_m{2})
  · equiv_sim
  · equiv_if{1}
    case «then» =>
      stmt_wp{1}
      equiv_rnd
      equiv_skip
      rintro xs i mp x m ⟨⟨rfl, rfl⟩, hd⟩ a -
      simp [hd]
    case «else» =>
      stmt_wp{2} 1
      equiv_skip
      rintro xs i mp x m ⟨⟨rfl, rfl⟩, hd⟩
      refine ⟨?_, fun a _ => by simp [hd]⟩
      simp [ERO.dout, dbool, uniform_expected]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- `local lemma HybridIROLazy_HIRO_LRO_f : equiv[HybridIROLazy.f ~ HIRO(LRO).f :
={xs, n} /\ HybridIROLazy.mp{1} = ERO.RO.m{2} ==> ={res} /\ HybridIROLazy.mp{1} = ERO.RO.m{2}]`. -/
theorem HybridIROLazy_HIRO_LRO_f :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ HybridIROLazy_mp.get g₁ = ERO_RO_m.get g₂)
      (HybridIROLazy.f HybridIROLazy_mp).procedure
      (Module.app HIRO.f (ERO.LRO ERO_RO_m)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ HybridIROLazy_mp.get g₁ = ERO_RO_m.get g₂) := by
  sorry

/-- `local lemma HIRO_RO_HybridIROEager_init : equiv[HIRO(ERO.RO).init ~ HybridIROEager.init :
true ==> ={res} /\ ERO.RO.m{1} = HybridIROEager.mp{2}]`. -/
theorem HIRO_RO_HybridIROEager_init :
    prhlProc (fun _ _ _ _ => True)
      (Module.app HIRO.init (ERO.RO ERO_RO_m)).procedure
      (HybridIROEager.init HybridIROEager_mp).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ERO_RO_m.get g₁ = HybridIROEager_mp.get g₂) := by
  sorry

/-- `local lemma RO_get_HybridIROEager_fill_in : equiv[ERO.RO.get ~ HybridIROEager.fill_in :
x{1} = (xs, i){2} /\ ERO.RO.m{1} = HybridIROEager.mp{2} ==>
={res} /\ ERO.RO.m{1} = HybridIROEager.mp{2}]`. -/
theorem RO_get_HybridIROEager_fill_in :
    prhlProc (sig₁ := procsig (List block × ℤ) -> Bool)
      (sig₂ := procsig (List block, ℤ) -> Bool)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ERO_RO_m.get g₁ = HybridIROEager_mp.get g₂)
      (PROM.FullRO.RO_T.get (List block × ℤ) Bool (ERO.RO ERO_RO_m)).procedure
      (HybridIROEager.fill_in HybridIROEager_mp).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ERO_RO_m.get g₁ = HybridIROEager_mp.get g₂) := by
  -- EC: `case (dom mp (xs, i)); rcondf{1} 2; rcondf{2} 1; rnd{1} …; rcondt{1} 2; rcondt{2} 1;
  -- wp; rnd`: the case split is `equiv_if{2}` on the eager test
  equiv_proc
  repeat stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = (§xs0{2}, §i0{2}) ∧ §ERO_RO_m{1} = §HybridIROEager_mp{2})
  · equiv_sim
  · equiv_if{2}
    case «then» =>
      stmt_wp{2}
      equiv_rnd
      equiv_skip
      rintro x m xs i mp ⟨⟨rfl, rfl⟩, hd⟩ a -
      simp [hd]
    case «else» =>
      stmt_wp{1} 1
      equiv_skip
      rintro x m xs i mp ⟨⟨rfl, rfl⟩, hd⟩
      refine ⟨?_, fun a _ => by simp [hd]⟩
      simp [ERO.dout, dbool, uniform_expected]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- `local lemma RO_sample_HybridIROEager_fill_in : equiv[ERO.RO.sample ~ HybridIROEager.fill_in :
x{1} = (xs, i){2} /\ ERO.RO.m{1} = HybridIROEager.mp{2} ==> ERO.RO.m{1} = HybridIROEager.mp{2}]`. -/
theorem RO_sample_HybridIROEager_fill_in :
    prhlProc (sig₁ := procsig (List block × ℤ) -> Unit)
      (sig₂ := procsig (List block, ℤ) -> Bool)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ERO_RO_m.get g₁ = HybridIROEager_mp.get g₂)
      (PROM.FullRO.RO_T.sample (List block × ℤ) Bool (ERO.RO ERO_RO_m)).procedure
      (HybridIROEager.fill_in HybridIROEager_mp).procedure
      (fun _ g₁ _ g₂ => ERO_RO_m.get g₁ = HybridIROEager_mp.get g₂) := by
  -- EC: `proc; inline ERO.RO.get; sp; case …`, as `RO_get_HybridIROEager_fill_in`
  equiv_proc
  repeat stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x1{1} = (§xs0{2}, §i0{2}) ∧ §ERO_RO_m{1} = §HybridIROEager_mp{2})
  · equiv_sim
  · equiv_if{2}
    case «then» =>
      stmt_wp{2}
      equiv_rnd
      equiv_skip
      rintro x m xs i mp ⟨⟨rfl, rfl⟩, hd⟩ a -
      simp [hd]
    case «else» =>
      stmt_wp{1} 1
      equiv_skip
      rintro x m xs i mp ⟨⟨rfl, rfl⟩, hd⟩
      refine ⟨?_, fun a _ => by simp [hd]⟩
      simp [ERO.dout, dbool, uniform_expected]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- `local lemma HIRO_RO_HybridIROEager_f : equiv[HIRO(ERO.RO).f ~ HybridIROEager.f :
={xs, n} /\ ERO.RO.m{1} = HybridIROEager.mp{2} ==>
={res} /\ ERO.RO.m{1} = HybridIROEager.mp{2}]`. -/
theorem HIRO_RO_HybridIROEager_f :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ERO_RO_m.get g₁ = HybridIROEager_mp.get g₂)
      (Module.app HIRO.f (ERO.RO ERO_RO_m)).procedure
      (HybridIROEager.f HybridIROEager_mp).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ERO_RO_m.get g₁ = HybridIROEager_mp.get g₂) := by
  sorry

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

/-- `local lemma Exper_HybridIROLazy_LRO &m`, for the section's `D`. -/
theorem Exper_HybridIROLazy_LRO (D : HYBRID_IRO_DIST)
    (hD : Module.ECModule D HYBRID_IRO_DIST.ext)
    (_hDd : DRestrictions HybridIROLazy_mp HybridIROEager_mp D)
    (_hERO : FVP.fvP D ≤ (ERO_RO_m.footprint)ᶜ) (m : VariableAssignment) :
    Procedure.Pr (Module.app HybridIROExper (Module.pair (HybridIROLazy.asHI HybridIROLazy_mp) D)
        ).procedure () m (fun r _ => r = true) =
      Procedure.Pr (Module.app EROExper (Module.pair (ERO.LRO ERO_RO_m) (RODist D))).procedure ()
        m (fun r _ => r = true) := by
  sorry

/-- `local lemma Exper_RO_HybridIROEager &m`, for the section's `D`. -/
theorem Exper_RO_HybridIROEager (D : HYBRID_IRO_DIST)
    (hD : Module.ECModule D HYBRID_IRO_DIST.ext)
    (_hDd : DRestrictions HybridIROLazy_mp HybridIROEager_mp D)
    (_hERO : FVP.fvP D ≤ (ERO_RO_m.footprint)ᶜ) (m : VariableAssignment) :
    Procedure.Pr (Module.app EROExper (Module.pair (ERO.RO ERO_RO_m) (RODist D))).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (Module.app HybridIROExper
        (Module.pair (HybridIROEager.asHI HybridIROEager_mp) D)).procedure () m
        (fun r _ => r = true) := by
  sorry

/-- EC's `HybridIROExper_Lazy_Eager' &m`, for the section's `D`.  Not local: it does not mention
`ERO` (whose variables its proof takes fresh). -/
theorem HybridIROExper_Lazy_Eager' (D : HYBRID_IRO_DIST)
    (hD : Module.ECModule D HYBRID_IRO_DIST.ext)
    (_hDd : DRestrictions HybridIROLazy_mp HybridIROEager_mp D) (m : VariableAssignment) :
    Procedure.Pr (Module.app HybridIROExper (Module.pair (HybridIROLazy.asHI HybridIROLazy_mp) D)
        ).procedure () m (fun r _ => r = true) =
      Procedure.Pr (Module.app HybridIROExper
        (Module.pair (HybridIROEager.asHI HybridIROEager_mp) D)).procedure () m
        (fun r _ => r = true) := by
  sorry

end LazyEager

section Hybrid

-- one binder each: a `module` takes a whole binder group when it mentions one of its names
variable (HybridIROLazy_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)
  (HybridIROEager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)

/-- EC's `HybridIROExper_Lazy_Eager (D <: HYBRID_IRO_DIST {-HybridIROEager, -HybridIROLazy}) &m`. -/
theorem HybridIROExper_Lazy_Eager (D : HYBRID_IRO_DIST)
    (hD : Module.ECModule D HYBRID_IRO_DIST.ext)
    (_hDd : DRestrictions HybridIROLazy_mp HybridIROEager_mp D) (m : VariableAssignment) :
    Procedure.Pr (Module.app HybridIROExper (Module.pair (HybridIROLazy.asHI HybridIROLazy_mp) D)
        ).procedure () m (fun r _ => r = true) =
      Procedure.Pr (Module.app HybridIROExper
        (Module.pair (HybridIROEager.asHI HybridIROEager_mp) D)).procedure () m
        (fun r _ => r = true) := by
  sorry

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

theorem lazy_invar0 : lazy_invar FMap.empty FMap.empty := by
  sorry

theorem lazy_invar_mem_pad2blocks_l2r (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs : List Bool) (i : ℤ) :
    lazy_invar mp1 mp2 → FMap.dom mp1 (bs, i) → FMap.dom mp2 (pad2blocks bs, i) := by
  sorry

theorem lazy_invar_mem_pad2blocks_r2l (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs : List Bool) (i : ℤ) :
    lazy_invar mp1 mp2 → FMap.dom mp2 (pad2blocks bs, i) → FMap.dom mp1 (bs, i) := by
  sorry

theorem lazy_invar_vb (mp1 : FMap (List Bool × ℤ) Bool) (mp2 : FMap (List block × ℤ) Bool)
    (xs : List block) (n : ℤ) :
    lazy_invar mp1 mp2 → FMap.dom mp2 (xs, n) → valid_block xs := by
  sorry

theorem lazy_invar_lookup_eq (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs : List Bool) (n : ℤ) :
    lazy_invar mp1 mp2 → FMap.dom mp1 (bs, n) →
    oget (FMap.get mp1 (bs, n)) = oget (FMap.get mp2 (pad2blocks bs, n)) := by
  sorry

theorem lazy_invar_upd_mem_dom_iff (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs cs : List Bool) (n m : ℤ) (b : Bool) :
    lazy_invar mp1 mp2 →
    (FMap.dom (FMap.set mp1 (bs, n) b) (cs, m) ↔
      FMap.dom (FMap.set mp2 (pad2blocks bs, n) b) (pad2blocks cs, m)) := by
  sorry

theorem lazy_invar_upd2_vb (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs : List Bool) (xs : List block) (n m : ℤ) (b : Bool) :
    lazy_invar mp1 mp2 → FMap.dom (FMap.set mp2 (pad2blocks bs, n) b) (xs, m) →
    valid_block xs := by
  sorry

theorem lazy_invar_upd_lu_eq (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs cs : List Bool) (n m : ℤ) (b : Bool) :
    lazy_invar mp1 mp2 → FMap.dom (FMap.set mp1 (bs, n) b) (cs, m) →
    oget (FMap.get (FMap.set mp1 (bs, n) b) (cs, m)) =
      oget (FMap.get (FMap.set mp2 (pad2blocks bs, n) b) (pad2blocks cs, m)) := by
  sorry

/-- `lemma LowerFun_IRO_HybridIROLazy_f : equiv[LowerFun(IRO).f ~
LowerHybridIRO(HybridIROLazy).f : ={xs, n} /\ lazy_invar IRO.mp{1} HybridIROLazy.mp{2} ==>
={res} /\ lazy_invar IRO.mp{1} HybridIROLazy.mp{2}]`. -/
theorem LowerFun_IRO_HybridIROLazy_f :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ lazy_invar (BIRO.IRO.mp.get g₁) (HybridIROLazy_mp.get g₂))
      (Module.app LowerFun.f (Indifferentiability.FUNCTIONALITY.view (block × capacity)
        (List Bool × ℤ) (List Bool) BIRO.IRO.asF)).procedure
      (Module.app LowerHybridIRO.f (HybridIROLazy.asHI HybridIROLazy_mp)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ lazy_invar (BIRO.IRO.mp.get g₁) (HybridIROLazy_mp.get g₂)) := by
  sorry

/-- `lemma IRO_RaiseHybridIRO_HybridIROLazy_f : equiv[IRO.f ~ RaiseHybridIRO(HybridIROLazy).f :
={n} /\ x{1} = bs{2} /\ lazy_invar IRO.mp{1} HybridIROLazy.mp{2} ==>
={res} /\ lazy_invar IRO.mp{1} HybridIROLazy.mp{2}]`. -/
theorem IRO_RaiseHybridIRO_HybridIROLazy_f :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ lazy_invar (BIRO.IRO.mp.get g₁) (HybridIROLazy_mp.get g₂))
      BIRO.IRO.f.procedure
      (Module.app RaiseHybridIRO.f (HybridIROLazy.asHI HybridIROLazy_mp)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ lazy_invar (BIRO.IRO.mp.get g₁) (HybridIROLazy_mp.get g₂)) := by
  sorry

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

theorem eager_inv_mem_mp1_ge0 (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) :
    eager_invar mp1 mp2 → FMap.dom mp1 (xs, i) → 0 ≤ i := by
  sorry

theorem eager_inv_mem_mp2_ge0 (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (j : ℤ) :
    eager_invar mp1 mp2 → FMap.dom mp2 (xs, j) → 0 ≤ j := by
  sorry

theorem eager_invar0 : eager_invar FMap.empty FMap.empty := by
  sorry

theorem eager_inv_imp_block_bits_dom (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) :
    0 ≤ i → r ∣ i → eager_invar mp1 mp2 → block_bits_dom_all_in_or_out xs i mp2 := by
  sorry

theorem eager_inv_mem_dom1 (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) :
    eager_invar mp1 mp2 → FMap.dom mp1 (xs, i) → block_bits_all_in_dom xs (i * r) mp2 := by
  sorry

theorem eager_inv_not_mem_dom1 (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) :
    eager_invar mp1 mp2 → 0 ≤ i → ¬ FMap.dom mp1 (xs, i) →
    block_bits_all_out_dom xs (i * r) mp2 := by
  sorry

theorem block_bits_dom_first_in_imp_all_in (xs : List block) (i : ℤ)
    (mp : FMap (List block × ℤ) Bool) :
    block_bits_dom_all_in_or_out xs i mp → FMap.dom mp (xs, i) →
    block_bits_all_in_dom xs i mp := by
  sorry

theorem block_bits_dom_first_out_imp_all_out (xs : List block) (i : ℤ)
    (mp : FMap (List block × ℤ) Bool) :
    block_bits_dom_all_in_or_out xs i mp → ¬ FMap.dom mp (xs, i) →
    block_bits_all_out_dom xs i mp := by
  sorry

/-- `lemma Lower_HybridIROEager_f : equiv[LowerHybridIRO(HybridIROEager).f ~ HybridIROEager.f :
={xs, HybridIROEager.mp} /\ n{1} * r = n{2} ==> res{1} = bits2blocks res{2} /\
={HybridIROEager.mp}]`. -/
theorem Lower_HybridIROEager_f :
    prhlProc (sig₁ := procsig (List block × ℤ) -> (List block))
      (sig₂ := procsig (List block, ℤ) -> (List Bool))
     
      (fun a₁ g₁ a₂ g₂ => a₁.1 = a₂.1 ∧ HybridIROEager_mp.get g₁ = HybridIROEager_mp.get g₂ ∧
        a₁.2 * r = a₂.2)
      (Module.app LowerHybridIRO.f (HybridIROEager.asHI HybridIROEager_mp)).procedure
      (HybridIROEager.f HybridIROEager_mp).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = bits2blocks r₂ ∧
        HybridIROEager_mp.get g₁ = HybridIROEager_mp.get g₂) := by
  sorry

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
  sorry

theorem eager_eq_except_upd1_eq_in (xs : List block) (i j k : ℤ) (y : Bool)
    (mp1 mp2 : FMap (List block × ℤ) Bool) :
    eager_eq_except xs i j mp1 mp2 → i ≤ k → k < j →
    eager_eq_except xs i j (FMap.set mp1 (xs, k) y) mp2 := by
  sorry

theorem eager_eq_except_upd2_eq_in (xs : List block) (i j k : ℤ) (y : Bool)
    (mp1 mp2 : FMap (List block × ℤ) Bool) :
    eager_eq_except xs i j mp1 mp2 → i ≤ k → k < j →
    eager_eq_except xs i j mp1 (FMap.set mp2 (xs, k) y) := by
  sorry

theorem eager_eq_except_maps_eq (xs : List block) (i j : ℤ) (_y : Bool)
    (mp1 mp2 : FMap (List block × ℤ) Bool) :
    i ≤ j → eager_eq_except xs i j mp1 mp2 →
    (∀ (k : ℤ), i ≤ k ∧ k < j → FMap.get mp1 (xs, k) = FMap.get mp2 (xs, k)) → mp1 = mp2 := by
  sorry

theorem eager_invar_eq_except_upd1 (mp1 : FMap (List block × ℤ) block)
    (mp2 mp2' : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) (y : block) :
    0 ≤ i → eager_invar mp1 mp2 → eager_eq_except xs (i * r) ((i + 1) * r) mp2 mp2' →
    (∀ (j : ℤ), i * r ≤ j ∧ j < (i + 1) * r →
      FMap.get mp2' (xs, j) = some (nth false (ofblock y) (j - i * r))) →
    eager_invar (FMap.set mp1 (xs, i) y) mp2' := by
  sorry

/-- `lemma HybridIROEagerTrans_next_block_split : equiv[HybridIROEagerTrans.next_block ~
HybridIROEagerTrans.next_block_split : ={i, m, xs, bs, HybridIROEager.mp} /\ m{1} = i{1} + r /\
size bs{1} = i{1} /\ block_bits_dom_all_in_or_out xs{1} i{1} HybridIROEager.mp{1} ==>
={res, HybridIROEager.mp}]`; the arguments are `(xs, i, m, bs)`. -/
theorem HybridIROEagerTrans_next_block_split :
    prhlProc (sig₁ := procsig (List block, ℤ, ℤ, List Bool) -> (List Bool × ℤ))
      (sig₂ := procsig (List block, ℤ, ℤ, List Bool) -> (List Bool × ℤ))
     
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ HybridIROEager_mp.get g₁ = HybridIROEager_mp.get g₂ ∧
        a₁.2.2.1 = a₁.2.1 + r ∧ size a₁.2.2.2 = a₁.2.1 ∧
        block_bits_dom_all_in_or_out a₁.1 a₁.2.1 (HybridIROEager_mp.get g₁))
      (HybridIROEagerTrans.next_block HybridIROEager_mp).procedure
      (HybridIROEagerTrans.next_block_split HybridIROEager_mp).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ HybridIROEager_mp.get g₁ = HybridIROEager_mp.get g₂) := by
  sorry

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
      (dlist dbool r).1 {bs} := by
  sorry

theorem iter_mul_one_half_pos (n : ℤ) :
    0 < n → iter n ((1 / 2 : ℝ) * ·) 1 = (((2 ^ n.toNat : ℤ) : ℝ))⁻¹ := by
  sorry

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

/-- `lemma BlockGen_loop_direct : equiv[BlockGen.loop ~ BlockGen.direct : true ==> ={res}]`. -/
theorem BlockGen_loop_direct :
    prhlProc (fun _ _ _ _ => True) BlockGen.loop.procedure BlockGen.direct.procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  sorry

/-- `lemma HybridIROEagerTrans_BlockSpongeTrans_next_block (i2 : int) :
equiv[HybridIROEagerTrans.next_block ~ BlockSpongeTrans.next_block : …]`; the arguments are
`(xs, i, m, bs)` and `(x, i, bs)`. -/
theorem HybridIROEagerTrans_BlockSpongeTrans_next_block (i2 : ℤ) :
    prhlProc (sig₁ := procsig (List block, ℤ, ℤ, List Bool) -> (List Bool × ℤ))
      (sig₂ := procsig (List block, ℤ, List block) -> (List block × ℤ))
     
      (fun a₁ g₁ a₂ g₂ => i2 = a₂.2.1 ∧ 0 ≤ a₂.2.1 ∧ a₁.1 = a₂.1 ∧ a₁.2.1 = a₂.2.1 * r ∧
        a₁.2.2.1 - a₁.2.1 = r ∧ a₁.2.2.2 = blocks2bits a₂.2.2 ∧ size a₂.2.2 = a₂.2.1 ∧
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁))
      (HybridIROEagerTrans.next_block HybridIROEager_mp).procedure
      (BlockSpongeTrans.next_block).procedure
      (fun r₁ g₁ r₂ g₂ => r₁.1 = blocks2bits r₂.1 ∧ r₁.2 = r₂.2 * r ∧ r₂.2 = i2 + 1 ∧
        size r₂.1 = i2 + 1 ∧
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁)) := by
  sorry

/-- `lemma HybridIROEagerTrans_BlockSpongeTrans_loop (n' : int) : equiv[HybridIROEagerTrans.loop
~ BlockSpongeTrans.loop : …]`; the arguments are `(n, xs)`. -/
theorem HybridIROEagerTrans_BlockSpongeTrans_loop (n' : ℤ) :
    prhlProc (sig₁ := procsig (ℤ, List block) -> (ℤ × List Bool))
      (sig₂ := procsig (ℤ, List block) -> (ℤ × List block))
     
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ n' = a₁.1 ∧ 0 ≤ n' ∧
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁))
      (HybridIROEagerTrans.loop HybridIROEager_mp).procedure
      (BlockSpongeTrans.loop).procedure
      (fun r₁ g₁ r₂ g₂ => r₁.1 = n' * r ∧ r₂.1 = n' ∧ size r₂.2 = n' ∧
        r₁.2 = blocks2bits r₂.2 ∧
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁)) := by
  sorry

/-- `lemma HybridIROEager_f_BlockIRO_f (n1 : int) (x2 : block list) : equiv[HybridIROEager.f ~
BlockSponge.BIRO.IRO.f : …]`; the arguments are `(xs, n)` and `(x, n)`. -/
theorem HybridIROEager_f_BlockIRO_f (n1 : ℤ) (x2 : List block) :
    prhlProc (sig₁ := procsig (List block, ℤ) -> (List Bool))
      (sig₂ := procsig (List block × ℤ) -> (List block))
     
      (fun a₁ g₁ a₂ g₂ => n1 = a₁.2 ∧ x2 = a₂.1 ∧ a₁.1 = a₂.1 ∧ a₂.2 = (a₁.2 + r - 1) / r ∧
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁))
      (HybridIROEager.f HybridIROEager_mp).procedure
      BlockSponge.BIRO.IRO.f.procedure
      (fun r₁ g₁ r₂ g₂ =>
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁) ∧
        (valid_block x2 →
          (n1 ≤ 0 → r₁ = [] ∧ r₂ = []) ∧
          (0 < n1 → r₁ = take n1 (blocks2bits r₂) ∧ size r₂ = (n1 + r - 1) / r)) ∧
        (¬ valid_block x2 → r₁ = [] ∧ r₂ = [])) := by
  sorry

/-- `lemma HybridIROEager_BlockIRO_f : equiv[LowerHybridIRO(HybridIROEager).f ~
BlockSponge.BIRO.IRO.f : xs{1} = x{2} /\ ={n} /\
eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
={res} /\ eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}]`. -/
theorem HybridIROEager_BlockIRO_f :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁))
      (Module.app LowerHybridIRO.f (HybridIROEager.asHI HybridIROEager_mp)).procedure
      BlockSponge.BIRO.IRO.f.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁)) := by
  sorry

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

/-- The section's restrictions `{-IRO, -BlockSponge.BIRO.IRO}` on `BlockSim` and
`{-Perm, -BlockSim, -IRO, -BlockSponge.BIRO.IRO}` on `Dist` (an abbreviation). -/
def Restrictions (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER) : Prop :=
  FVP.fvP BlockSim ≤ ((BIRO.IRO.mp).footprint ⊔ (BlockSponge.BIRO.IRO.mp).footprint)ᶜ ∧
  FVP.fvP Dist ≤ ((Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ (FVP.fvP BlockSim).glob ⊔
    (BIRO.IRO.mp).footprint ⊔ (BlockSponge.BIRO.IRO.mp).footprint)ᶜ

/-- The local clone `HIRO`'s variables are fresh: disjoint from each other, from `BlockSim`,
`Dist` and the other games' variables (EasyCrypt's semantics of a local clone; exception E6). -/
def HIRO_fresh (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (HIRO_Lazy_mp HIRO_Eager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment) : Prop :=
  (HIRO_Lazy_mp).footprint ⊔ (HIRO_Eager_mp).footprint ≤ (FVP.fvP BlockSim ⊔ FVP.fvP Dist ⊔
    (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ (BIRO.IRO.mp).footprint ⊔
    (BlockSponge.BIRO.IRO.mp).footprint)ᶜ ∧
  (HIRO_Lazy_mp).footprint ≤ (HIRO_Eager_mp).footprintᶜ

/-- `Experiment(HIRO.RaiseHybridIRO(HI), BlockSim(HIRO.LowerHybridIRO(HI)), Dist)`, the game the
ideal side goes through, for `HI` the lazy or the eager hybrid IRO (an abbreviation). -/
noncomputable def HybridExperiment (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (HI : HybridIRO.HYBRID_IRO) : procmod () → Bool :=
  Module.app Experiment (Module.pair (Module.app HybridIRO.RaiseHybridIRO HI)
    (Module.pair (Module.app BlockSim (Module.app HybridIRO.LowerHybridIRO HI)) Dist))

/-! ### The real side -/

/-- `local lemma Sponge_Raise_BlockSponge_f : equiv[Sponge(Perm).f ~
RaiseFun(BlockSponge.Sponge(Perm)).f : ={bs, n, glob Perm} ==> ={res, glob Perm}]`. -/
theorem Sponge_Raise_BlockSponge_f :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ eqGlob Perm g₁ g₂)
      (Module.app Sponge.f (Indifferentiability.PRIMITIVE.view (block × capacity)
        (List Bool × ℤ) (List Bool) Perm)).procedure
      (Module.app RaiseFun.f (Indifferentiability.FUNCTIONALITY.view (block × capacity)
        (List block × ℤ) (List block) (Module.app BlockSponge.Sponge
          (Indifferentiability.PRIMITIVE.view (block × capacity) (List block × ℤ) (List block)
            Perm)))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eqGlob Perm g₁ g₂) := by
  sorry

/-- `local lemma RealIndif_Sponge_BlockSponge &m`. -/
theorem RealIndif_Sponge_BlockSponge (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (hD : Module.ECModule Dist distExt) (_hR : Restrictions BlockSim Dist)
    (m : VariableAssignment) :
    Procedure.Pr (RealIndif Sponge Perm Dist).procedure () m (fun r _ => r = true) =
      Procedure.Pr (BlockSponge.RealIndif BlockSponge.Sponge Perm (LowerDist Dist)).procedure () m
        (fun r _ => r = true) := by
  sorry

/-! ### The ideal side -/

/-- `local lemma Ideal_IRO_Experiment_HybridLazy &m`: first step of the ideal side. -/
theorem Ideal_IRO_Experiment_HybridLazy (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (hS : Indifferentiability.SIMULATOR.ECModule (block × capacity) (List block × ℤ)
      (List block) BlockSim)
    (hD : Module.ECModule Dist distExt) (_hR : Restrictions BlockSim Dist)
    (HIRO_Lazy_mp HIRO_Eager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)
    (_hfresh : HIRO_fresh BlockSim Dist HIRO_Lazy_mp HIRO_Eager_mp) (m : VariableAssignment) :
    Procedure.Pr (IdealIndif BIRO.IRO.asF (RaiseSim BlockSim) Dist).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (HybridExperiment BlockSim Dist
        (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp)).procedure () m (fun r _ => r = true) := by
  sorry

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

/-- `local lemma Experiment_HybridIROExper_Lazy &m`: initial bridging step. -/
theorem Experiment_HybridIROExper_Lazy (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (hS : Indifferentiability.SIMULATOR.ECModule (block × capacity) (List block × ℤ)
      (List block) BlockSim)
    (hD : Module.ECModule Dist distExt) (_hR : Restrictions BlockSim Dist)
    (HIRO_Lazy_mp HIRO_Eager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)
    (_hfresh : HIRO_fresh BlockSim Dist HIRO_Lazy_mp HIRO_Eager_mp) (m : VariableAssignment) :
    Procedure.Pr (HybridExperiment BlockSim Dist
        (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp)).procedure () m (fun r _ => r = true) =
      Procedure.Pr (Module.app HybridIRO.HybridIROExper
        (Module.pair (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp)
          (HybridIRODist BlockSim Dist))).procedure () m (fun r _ => r = true) := by
  sorry

/-- `local lemma HybridIROExper_Experiment_Eager &m`: final bridging step. -/
theorem HybridIROExper_Experiment_Eager (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (hS : Indifferentiability.SIMULATOR.ECModule (block × capacity) (List block × ℤ)
      (List block) BlockSim)
    (hD : Module.ECModule Dist distExt) (_hR : Restrictions BlockSim Dist)
    (HIRO_Lazy_mp HIRO_Eager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)
    (_hfresh : HIRO_fresh BlockSim Dist HIRO_Lazy_mp HIRO_Eager_mp) (m : VariableAssignment) :
    Procedure.Pr (Module.app HybridIRO.HybridIROExper
        (Module.pair (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)
          (HybridIRODist BlockSim Dist))).procedure () m (fun r _ => r = true) =
      Procedure.Pr (HybridExperiment BlockSim Dist
        (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)).procedure () m (fun r _ => r = true) := by
  sorry

/-- `local lemma Experiment_Hybrid_Lazy_Eager &m`: middle step of the ideal side, taking
`HIRO.HybridIROLazy` to `HIRO.HybridIROEager`. -/
theorem Experiment_Hybrid_Lazy_Eager (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (hS : Indifferentiability.SIMULATOR.ECModule (block × capacity) (List block × ℤ)
      (List block) BlockSim)
    (hD : Module.ECModule Dist distExt) (_hR : Restrictions BlockSim Dist)
    (HIRO_Lazy_mp HIRO_Eager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)
    (_hfresh : HIRO_fresh BlockSim Dist HIRO_Lazy_mp HIRO_Eager_mp) (m : VariableAssignment) :
    Procedure.Pr (HybridExperiment BlockSim Dist
        (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp)).procedure () m (fun r _ => r = true) =
      Procedure.Pr (HybridExperiment BlockSim Dist
        (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)).procedure () m (fun r _ => r = true) := by
  sorry

/-- `local lemma RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f :
equiv[HIRO.RaiseHybridIRO(HIRO.HybridIROEager).f ~ RaiseFun(BlockSponge.BIRO.IRO).f :
={bs, n} /\ ={glob BlockSim} /\ HIRO.eager_invar BlockSponge.BIRO.IRO.mp{2}
HIRO.HybridIROEager.mp{1} ==> ={res} /\ ={glob BlockSim} /\ HIRO.eager_invar …]`. -/
theorem RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f (BlockSim : BlockSponge.SIMULATOR)
    (Dist : DISTINGUISHER) (_hR : Restrictions BlockSim Dist)
    (HIRO_Lazy_mp HIRO_Eager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)
    (_hfresh : HIRO_fresh BlockSim Dist HIRO_Lazy_mp HIRO_Eager_mp) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ eqGlob BlockSim g₁ g₂ ∧
        HybridIRO.eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HIRO_Eager_mp.get g₁))
      (Module.app HybridIRO.RaiseHybridIRO.f
        (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)).procedure
      (Module.app RaiseFun.f (Indifferentiability.FUNCTIONALITY.view (block × capacity)
        (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eqGlob BlockSim g₁ g₂ ∧
        HybridIRO.eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HIRO_Eager_mp.get g₁)) := by
  sorry

/-- `local lemma Experiment_HybridEager_Ideal_BlockIRO &m`: last step of the ideal side. -/
theorem Experiment_HybridEager_Ideal_BlockIRO (BlockSim : BlockSponge.SIMULATOR)
    (Dist : DISTINGUISHER)
    (hS : Indifferentiability.SIMULATOR.ECModule (block × capacity) (List block × ℤ)
      (List block) BlockSim)
    (hD : Module.ECModule Dist distExt) (_hR : Restrictions BlockSim Dist)
    (HIRO_Lazy_mp HIRO_Eager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)
    (_hfresh : HIRO_fresh BlockSim Dist HIRO_Lazy_mp HIRO_Eager_mp) (m : VariableAssignment) :
    Procedure.Pr (HybridExperiment BlockSim Dist
        (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)).procedure () m (fun r _ => r = true) =
      Procedure.Pr (BlockSponge.IdealIndif BlockSponge.BIRO.IRO.asF BlockSim
        (LowerDist Dist)).procedure () m (fun r _ => r = true) := by
  sorry

/-- `local lemma IdealIndif_IRO_BlockIRO &m`: the ideal side of the main result.  It does not
mention `HIRO`, whose variables its proof takes fresh. -/
theorem IdealIndif_IRO_BlockIRO (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (hS : Indifferentiability.SIMULATOR.ECModule (block × capacity) (List block × ℤ)
      (List block) BlockSim)
    (hD : Module.ECModule Dist distExt) (_hR : Restrictions BlockSim Dist)
    (m : VariableAssignment) :
    Procedure.Pr (IdealIndif BIRO.IRO.asF (RaiseSim BlockSim) Dist).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (BlockSponge.IdealIndif BlockSponge.BIRO.IRO.asF BlockSim
        (LowerDist Dist)).procedure () m (fun r _ => r = true) := by
  sorry

/-- EC's `conclu &m`, for the section's `BlockSim` and `Dist`. -/
theorem conclu (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (hS : Indifferentiability.SIMULATOR.ECModule (block × capacity) (List block × ℤ)
      (List block) BlockSim)
    (hD : Module.ECModule Dist distExt) (_hR : Restrictions BlockSim Dist)
    (m : VariableAssignment) :
    |(Procedure.Pr (RealIndif Sponge Perm Dist).procedure () m (fun r _ => r = true) : ℝ) -
        (Procedure.Pr (IdealIndif BIRO.IRO.asF (RaiseSim BlockSim) Dist).procedure () m
          (fun r _ => r = true) : ℝ)| =
      |(Procedure.Pr (BlockSponge.RealIndif BlockSponge.Sponge Perm (LowerDist Dist)).procedure ()
          m (fun r _ => r = true) : ℝ) -
        (Procedure.Pr (BlockSponge.IdealIndif BlockSponge.BIRO.IRO.asF BlockSim
          (LowerDist Dist)).procedure () m (fun r _ => r = true) : ℝ)| := by
  sorry

end Main

/-! ## Conclusion -/

/-- EC's `conclusion (BlockSim <: BlockSponge.SIMULATOR {-IRO, -BlockSponge.BIRO.IRO})
(Dist <: DISTINGUISHER {-Perm, -BlockSim, -IRO, -BlockSponge.BIRO.IRO}) &m`: the sponge is as
indifferentiable from the bit-level IRO as the block sponge is from the block-level one. -/
theorem conclusion (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (hS : Indifferentiability.SIMULATOR.ECModule (block × capacity) (List block × ℤ)
      (List block) BlockSim)
    (hD : Module.ECModule Dist distExt) (_hR : Restrictions BlockSim Dist)
    (m : VariableAssignment) :
    |(Procedure.Pr (RealIndif Sponge Perm Dist).procedure () m (fun r _ => r = true) : ℝ) -
        (Procedure.Pr (IdealIndif BIRO.IRO.asF (RaiseSim BlockSim) Dist).procedure () m
          (fun r _ => r = true) : ℝ)| =
      |(Procedure.Pr (BlockSponge.RealIndif BlockSponge.Sponge Perm (LowerDist Dist)).procedure ()
          m (fun r _ => r = true) : ℝ) -
        (Procedure.Pr (BlockSponge.IdealIndif BlockSponge.BIRO.IRO.asF BlockSim
          (LowerDist Dist)).procedure () m (fun r _ => r = true) : ℝ)| := by
  sorry

end GaudisCrypt.SHA3.Sponge
