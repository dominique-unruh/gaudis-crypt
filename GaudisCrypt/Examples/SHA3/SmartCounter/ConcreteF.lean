import GaudisCrypt.Examples.SHA3.SmartCounter.SLCommon
import GaudisCrypt.Lib.EC.Strong_RP_RF
import GaudisCrypt.Logic.FrameTactics
import GaudisCrypt.Logic.EqualOutside
import GaudisCrypt.Logic.LoopTransform
import GaudisCrypt.Logic.GlobMono

/-!
# From the permutation to a random function (EasyCrypt `proof/smart_counter/ConcreteF.eca`)

The real game with the ideal permutation is close to the same game with `PF`, a random function
with an inverse, up to the PRP/PRF switching bound (`Real_Concrete`).

Translation notes (see `notes/SHA3/README.md`):
* The section's `declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo}` and `declare axiom
  D_ll` are hypotheses of the lemmas.  So are the local modules' parameters.
* `local clone import Strong_RP_RF as Switching with type D <- state, op uD <- dstate,
  type K <- unit, op dK <- dunit tt, op q <- max_size` is the namespace `Switching`, and its
  realized axioms `ge0_q`, `uD_uf_fu` are lemmas.  The clone is local, so its module variables are
  lens parameters of the local declarations that mention them (exception E6).
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

/-! `local clone import Strong_RP_RF as Switching with type D <- state, op uD <- dstate,
type K <- unit, op dK <- (MUnit.dunit<:unit> tt), op q <- max_size` -/

namespace Switching
/-! The clone is local: its module variables (`PRPi.m`, `PRPi.mi`, `ARP.coll`, `ARP.m`, `ARP.mi`,
`DBounder.FBounder.c`) are lens parameters of the local declarations that mention them, fresh by
hypothesis (exception E6). -/
-- one binder each: a declaration takes only the variables it mentions
variable (PRPi_m : Lens (FMap state state) VariableAssignment)
variable (PRPi_mi : Lens (FMap state state) VariableAssignment)
variable (ARP_coll : Lens Bool VariableAssignment)
variable (ARP_m : Lens (FMap state state) VariableAssignment)
variable (ARP_mi : Lens (FMap state state) VariableAssignment)
variable (DBounder_FBounder_c : Lens ℤ VariableAssignment)
noncomputable abbrev PRPi.PRPi := Strong_RP_RF.PRPi.PRPi state dstate PRPi_m PRPi_mi
noncomputable abbrev ARP := Strong_RP_RF.ARP state dstate ARP_coll ARP_m ARP_mi
noncomputable abbrev DBounder := Strong_RP_RF.DBounder state max_size DBounder_FBounder_c
abbrev PRPSec.PRP := EC.PRP.StrongPRP.PRP state
abbrev PRPSec.SPRP_Oracles := EC.PRP.StrongPRP.SPRP_Oracles state
abbrev PRPSec.Distinguisher := EC.PRP.StrongPRP.Distinguisher state
noncomputable abbrev PRPSec.IND := EC.PRP.StrongPRP.IND state

/-- `realize uD_uf_fu`: `dstate` is uniform, lossless and full. -/
theorem uD_uf_fu : dstate.1 Set.univ = 1 ∧ ∀ x y, dstate.1 {x} = dstate.1 {y} := by
  refine ⟨dprod_ll BitWord.dunifin_ll BitWord.dunifin_ll, ?_⟩
  rintro ⟨x1, x2⟩ ⟨y1, y2⟩
  rw [dstate, dprod1E, dprod1E, bdistr, cdistr, Block.DBlock.dunifin, Capacity.DCapacity.dunifin,
    BitWord.dunifin_funi x1 y1, BitWord.dunifin_funi x2 y2]
end Switching

/-! ## `DoubleBounding`'s invariant and oracle steps -/

/-- `PRPSec.SPRP_Oracles` and `DPRIMITIVE` are the same module type: the same `f`. -/
theorem DPRIMITIVE_f_eq (X : Switching.PRPSec.SPRP_Oracles) :
    Indifferentiability.DPRIMITIVE.f state (List block) block X =
      PRP.StrongPRP.SPRP_Oracles.f state X := rfl

/-- The view of a PRP as `DPRIMITIVE`: its `f`. -/
theorem dprim_f_mk (P : Switching.PRPSec.PRP) :
    Indifferentiability.DPRIMITIVE.f state (List block) block
      (PRP.StrongPRP.SPRP_Oracles.mk state
        { f := PRP.StrongPRP.PRP.f state P, fi := PRP.StrongPRP.PRP.fi state P }) =
      PRP.StrongPRP.PRP.f state P := by
  rw [DPRIMITIVE_f_eq]; simp

/-- `local clone import ProdSampling with type t1 <- block, type t2 <- capacity`. -/
noncomputable abbrev S := DProd.ProdSampling.S block capacity

/-! ### `Real_Concrete`'s game steps

EC's `byequiv; proc; inline *; sim` steps between `Indif`, `CF` and `PRPSec.IND` (the module
views bridged by `rfl`/`simp` lemmas), and the `ARP`/`PF` step (`ARP` with `PF`'s maps, its
`coll` flag outside `PF`). -/

theorem view_Perm_eq : Indifferentiability.PRIMITIVE.view state (List block) block Perm =
    PRP.StrongPRP.SPRP_Oracles.mk state
      { f := PRP.StrongPRP.PRP.f state (Switching.PRPi.PRPi Perm.m Perm.mi),
        fi := PRP.StrongPRP.PRP.fi state (Switching.PRPi.PRPi Perm.m Perm.mi) } := rfl

/-! ## `GReal ~ GReal'` (the first step of `Real_Concrete`) -/

/-- `Perm` touches `Perm.m`, `Perm.mi`.  Not an EC lemma (EC reads it off the code). -/
theorem fvP_Perm : FVP.fvP Perm ≤ (Lens.pair Perm.m Perm.mi).footprint := by
  fp_module (Lens.pair Perm.m Perm.mi)

/-- `SqueezelessSponge` touches `Redo.prefixes`.  Not an EC lemma. -/
@[fp_bound] theorem fvP_SqueezelessSponge :
    FVP.fvP SqueezelessSponge ≤ Redo.prefixes.footprint := by
  fp_module Redo.prefixes

/-- `Perm` touches `Perm.m` and `Perm.mi` (the joined form of `fvP_Perm`). -/
@[fp_bound] theorem fvP_Perm_sup : FVP.fvP Perm ≤ (Perm.m).footprint ⊔ (Perm.mi).footprint := by
  simpa only [Footprint.lens_pair] using fvP_Perm

/-- EC's `p_ll := f_ll _` (`RP`'s `f_ll`: `dstate` is full).  `Perm.f` samples from
`dstate \ rng Perm.m`, lossless since `Perm.m` misses the queried key (`excepted_lossless`). -/
theorem Perm_f_ll :
    (Indifferentiability.PRIMITIVE.f state (List block) block Perm).procedure.IsLossless := by
  rw [← Indifferentiability.PRIMITIVE.view_f, view_Perm_eq, dprim_f_mk,
    Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  rename_i σ _
  split_ifs with hd
  · rfl
  · have h2 := (is_lossless_iff_expected _).mp
      (Strong_RP_RF.excepted_lossless state dstate Switching.uD_uf_fu (Perm.m.get σ.globals)
        ⟨_, hd⟩)
    simp [h2]

end

end GaudisCrypt.SHA3.ConcreteF
