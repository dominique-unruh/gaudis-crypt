import GaudisCrypt.Examples.SHA3.Pilot.SLCommon
import GaudisCrypt.Lib.EC.Strong_RP_RF
import GaudisCrypt.Logic.ECLoop
import GaudisCrypt.Logic.ECTrans
import GaudisCrypt.Logic.ECAlias

/-!
# From the permutation to a random function (EasyCrypt `proof/smart_counter/ConcreteF.eca`) —
EC-fidelity port

The real game with the ideal permutation is close to the same game with `PF`, a random function
with an inverse, up to the PRP/PRF switching bound (`Real_Concrete`).

Translation (as `Pilot/SLCommon.lean`):
* `local clone import Strong_RP_RF as Switching with type D <- state, op uD <- dstate, …` is the
  namespace `Switching`: the clone's module variables (`PRPi.m`, `ARP.coll`, `DBounder.FBounder.c`,
  …) `global_var`s, its modules the library's (`Lib/EC/Strong_RP_RF.lean`) at them, its realized
  axioms lemmas.  (EC's `local` has no counterpart: the clone's names stay visible.)
* `declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo}` and `declare axiom D_ll` as in
  EC; the local modules `GReal'`, `D'` are definitions (`D'` with `D` a Lean parameter, as
  `DRestr`).
-/

namespace GaudisCrypt.SHA3.Pilot.ConcreteF

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet
open GaudisCrypt.SHA3.Common hiding PRIMITIVE
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix
open GaudisCrypt.SHA3.Pilot.SLCommon GaudisCrypt.SHA3.Pilot.SLCommon.Indiff

variable [SLCommon.Params]

/-- EC's `state` (`SLCommonCore`'s, named here: a root `state` exists). -/
abbrev state := GaudisCrypt.SHA3.SLCommon.state

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
noncomputable abbrev CF (D : DISTINGUISHER) : procmod () → Bool :=
  Module.app Indif (Module.pair (Module.app SqueezelessSponge (PF : DPRIMITIVE))
    (Module.pair PF D))

/-! `local clone import Strong_RP_RF as Switching with type D <- state, op uD <- dstate,
type K <- unit, op dK <- (MUnit.dunit<:unit> tt), op q <- max_size`. -/

namespace Switching

global_var PRPi.m : FMap state state
global_var PRPi.mi : FMap state state
global_var ARP.coll : Bool
global_var ARP.m : FMap state state
global_var ARP.mi : FMap state state
global_var DBounder.FBounder.c : ℤ

set_option linter.dupNamespace false in
-- EasyCrypt names the module after its theory (exception E1)
/-- The clone's `PRPi.PRPi` (the theory's `clone import RP as PRPi`). -/
noncomputable abbrev PRPi.PRPi := Strong_RP_RF.PRPi.PRPi state dstate PRPi.m PRPi.mi
/-- The clone's `ARP`. -/
noncomputable abbrev ARP := Strong_RP_RF.ARP state dstate ARP.coll ARP.m ARP.mi
/-- The clone's `DBounder`. -/
noncomputable abbrev DBounder := Strong_RP_RF.DBounder state max_size DBounder.FBounder.c
abbrev PRPSec.PRP := EC.PRP.StrongPRP.PRP state
abbrev PRPSec.SPRP_Oracles := EC.PRP.StrongPRP.SPRP_Oracles state
abbrev PRPSec.Distinguisher := EC.PRP.StrongPRP.Distinguisher state
noncomputable abbrev PRPSec.IND := EC.PRP.StrongPRP.IND state

/-- `realize ge0_q by smt w=max_ge0`. -/
theorem ge0_q : 0 ≤ (max_size : ℤ) := max_ge0

/-- `realize uD_uf_fu`: `dstate` is uniform, lossless and full. -/
theorem uD_uf_fu : dstate.1 Set.univ = 1 ∧ ∀ x y, dstate.1 {x} = dstate.1 {y} := by
  refine ⟨dprod_ll BitWord.dunifin_ll BitWord.dunifin_ll, ?_⟩
  rintro ⟨x1, x2⟩ ⟨y1, y2⟩
  rw [dstate, dprod1E, dprod1E, bdistr, cdistr, Block.DBlock.dunifin, Capacity.DCapacity.dunifin,
    BitWord.dunifin_funi x1 y1, BitWord.dunifin_funi x2 y2]

end Switching

open Switching

omit [SLCommon.Params] in
/-- EC's `lemma size_behead (l : 'a list) : l <> [] => size (behead l) = size l - 1`. -/
theorem size_behead {α : Type} (l : List α) : l ≠ [] → size (behead l) = size l - 1 := by
  cases l with
  | nil => intro h; exact absurd rfl h
  | cons a l => intro _; simp [size, behead]

/-- A `PRPSec.SPRP_Oracles` is a `DPRIMITIVE` (its `f`, `fi`). -/
module_subtype (EC.PRP.StrongPRP.SPRP_Oracles state) <:
  GaudisCrypt.SHA3.Pilot.Indifferentiability.DPRIMITIVE

section

declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo}

-- EC's `declare axiom D_ll`
variable (D_ll : ∀ (F <: DFUNCTIONALITY {-D}), ∀ (P <: DPRIMITIVE {-D}),
  islossless P.f → islossless P.fi → islossless F.f → islossless D(F, P).distinguish)

/-- `local module GReal' = Indif(FC(SqueezelessSponge(Perm)), PC(Perm), D)`. -/
noncomputable abbrev GReal' : procmod () → Bool :=
  Module.app Indif (Module.pair (Module.app FC (Module.app SqueezelessSponge
    ((Perm : PRIMITIVE) : DPRIMITIVE))) (Module.pair (Module.app PC (Perm : PRIMITIVE)) D))

end

-- EC's `local module (D' : PRPSec.Distinguisher) (P' : PRPSec.SPRP_Oracles)`, `D` a Lean
-- parameter (as `DRestr`)
set_option linter.gaudisCrypt.using false in
module D' (D : DISTINGUISHER) using (P' : Switching.PRPSec.SPRP_Oracles) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call Redo.init ();
    b <- call DRestr(D, SqueezelessSponge(P'), P').distinguish ();
    return $b
  };
}

section

-- EC's `{-Perm, -C, -PF, -Redo}`, and the local clone's modules (declared after `D` in EC's
-- section, so fresh for it: EC's freshness, as the pilots' `SecureRO`)
declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo, -DBounder, -ARP, -PRPi.PRPi}

set_option maxHeartbeats 2000000 in
-- one declaration: EC's call over three oracles, with the loops of `SqueezelessSponge`
/-- EC's `local lemma DoubleBounding (P <: PRPSec.PRP {-D, -C, -DBounder, -Redo}) &m:
Pr[PRPSec.IND(P,D').main() @ &m: res] = Pr[PRPSec.IND(P,DBounder(D')).main() @ &m: res]`. -/
theorem DoubleBounding : ∀ (P <: Switching.PRPSec.PRP {-D, -C, -DBounder, -Redo}),
    ∀ m : VariableAssignment,
    Pr[ Switching.PRPSec.IND(P, D'(D)).main () @ &m : §res ] =
      Pr[ Switching.PRPSec.IND(P, DBounder(D'(D))).main () @ &m : §res ] := by
  intro P _ m
  byequiv; equiv_proc; stmt_inline*; stmt_wp
  equiv_call (_ : ={glob C, glob P, glob Redo} ∧ all_prefixes §Redo.prefixes{2} ∧
      FMap.get §Redo.prefixes{2} [] = some (b0, c0) ∧
      (∀ x, FMap.dom §C.queries{2} x → FMap.dom §Redo.prefixes{2} x) ∧
      prefix_inv §C.queries{2} §Redo.prefixes{2} ∧ §DBounder.FBounder.c{2} = §C.c{2})
  -- `P.f`
  · equiv_proc; stmt_sp; equiv_if
    · stmt_inline*
      stmt_rcondt{2} 3
      · hoare_auto
      sim; auto_close
    · equiv_skip; auto_close
    · auto_close
  -- `P.fi`
  · equiv_proc; stmt_sp; equiv_if
    · stmt_inline*
      stmt_rcondt{2} 3
      · hoare_auto
      sim; auto_close
    · equiv_skip; auto_close
    · auto_close
  -- `F.f`
  · equiv_proc; stmt_sp; equiv_if
    · stmt_inline*
      equiv_if
      · stmt_splitwhile{1} 5 : FMap.dom §Redo.prefixes (take (§i + 1) §p)
        stmt_splitwhile{2} 5 : FMap.dom §Redo.prefixes (take (§i + 1) §p)
        stmt_alias{1} 1 pref = §Redo.prefixes
        stmt_alias{2} 1 pref = §Redo.prefixes
        stmt_sp 1
        stmt_alias{1} 1 query = §C.queries
        stmt_alias{2} 1 query = §C.queries
        stmt_sp 1
        sorry
      · equiv_skip; auto_close
      · auto_close
    · stmt_wp; equiv_skip; auto_close
    · auto_close
  all_goals sorry

end

end GaudisCrypt.SHA3.Pilot.ConcreteF
