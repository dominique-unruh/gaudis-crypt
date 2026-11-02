import GaudisCrypt.Examples.SHA3.SHA3_OIndiff
import GaudisCrypt.Examples.SHA3.SecureORO
import GaudisCrypt.Examples.SHA3.SecureHash
import GaudisCrypt.Lib.EC.DList

/-!
# Top-level proof of SHA-3 security with failing oracles (EasyCrypt `proof/SHA3OSecurity.ec`)

Preimage, second-preimage and collision resistance of the sponge with outputs of `size_out` bits
(`OSponge`) in `SecureHash`'s games, against adversaries making `sigma` queries.  Each proof goes
through `SHA3_OIndiff` and the resistance of the random oracle (`SecureORO`).

Translation notes (see `notes/SHA3/README.md`):
* The file-level abstract type `f_out`, operators `size_out`, `dout`, `to_list`, `of_list` and the
  axioms (including `sigma_ge0`, an axiom about the defined `sigma`) are the parameter class
  `Params`, as in `SHA3Security`.
* Name resolution follows EasyCrypt's (checked with `print`): unqualified `OFUNCTIONALITY` …
  are `SHA3_OIndiff.OIndif`'s; `OIndif.X` is `SH.OIndif.X` (the clone `SH` comes later); `Oracle`
  and `RF` are `SORO`'s; `RO`, `FRO`, `LRO` are `Eager`'s.
* `clone import SecureORO as SORO`, `clone import SecureHash as SH`, `clone import FullRO as Eager`
  are namespaces of abbreviations that declare the clones' module variables; their `realize`s are
  `SORO.axioms`, `SH.axioms`.
* `FSetSize` and `ExtendOutput` have `proc get = f`, a procedure outside their type: it is
  `FSetSize.get`, the same procedure as `FSetSize.f` (an abbreviation).  Their aliases of a
  parameter's procedures are wrapped in a call (exception E5), as in the sections' `FInit`,
  `PInit`, `OF`, `ExtendSample`, `Fill_In` and `Dist`.  `OSponge(P) = FSetSize(CSome(Sponge, P))`
  is `Module.comp FSetSize (CSome Sponge)`; `OFC2(F) = OFC(ExtendOutputSize(F))` is
  `Module.comp OFC ExtendOutputSize`, written out where it is called inside a module body.
* The sections' local modules have variables (`Log.m`, `RFList.m`, `Dist_of_P2Adv.m`): lens
  parameters of the local declarations, with freshness hypotheses (`LocalFresh`, exception E6).
  `Log` has only its variable, so it is that lens alone.  The sections' local declarations go into
  namespaces named after the sections.
* `Dist(F)` is used as an `RO_Distinguisher` (`RO_LRO_D Dist`): its `distinguish` takes `Unit`.
* `OIndif(F, OSimulator(F), D)` (from `SHA3_OIndiff`) is written `IdealGame F D`.
-/

-- EasyCrypt's clones contain modules named like them (`SORO.RO.RO`, `SH.OIndif` …); kept (E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.SHA3OSecurity

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.Sponge GaudisCrypt.SHA3.Sponge.BIRO
open GaudisCrypt.SHA3.SHA3Indiff GaudisCrypt.SHA3.SHA3_OIndiff GaudisCrypt.SHA3.SHA3_OIndiff.OIndif

-- the last imports (`Sponge`, `SHA3_OIndiff`) win over `Common`'s and the root-level names
export GaudisCrypt.SHA3.SHA3_OIndiff (state PRIMITIVE)

variable [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params]

/-- EasyCrypt's file-level abstract type and operators, with their axioms: `op size_out` with
`size_out_gt0`, `axiom sigma_ge0`, `type f_out`, `op dout` with `dout_ll`, `dout_fu`, `dout_full`,
`op to_list`, `op of_list` with `spec_dout`, `spec2_dout`, `to_list_inj`, `to_listK` and
`dout_equal_dlist`. -/
class Params : Type 1 where
  size_out : ℤ
  size_out_gt0 : 0 < size_out
  sigma_ge0 : 0 ≤ SHA3Indiff.limit
  f_out : Type
  f_out_inhabited : Inhabited f_out
  dout : SubProbability f_out
  dout_ll : is_lossless dout
  dout_fu : is_funiform dout
  dout_full : is_full dout
  to_list : f_out → List Bool
  of_list : List Bool → Option f_out
  spec_dout : ∀ l, size (to_list l) = size_out
  spec2_dout : ∀ l, size l = size_out → of_list l ≠ none
  to_list_inj : Function.Injective to_list
  to_listK : ∀ e l, to_list e = l ↔ of_list l = some e
  dout_equal_dlist : (dout >>= fun x => pure (to_list x)) = dlist dbool size_out

variable [Params]

def size_out : ℤ := Params.size_out
/-- `op sigma : int = SHA3Indiff.limit`. -/
def sigma : ℤ := SHA3Indiff.limit
/-- `op limit : int = sigma`. -/
def limit : ℤ := sigma
abbrev f_out : Type := Params.f_out
instance : Inhabited f_out := Params.f_out_inhabited
noncomputable def dout : SubProbability f_out := Params.dout
def to_list : f_out → List Bool := Params.to_list
def of_list : List Bool → Option f_out := Params.of_list

theorem doutE1 (x : f_out) : (dout.1 {x}).toReal = ((2 : ℝ) ^ size_out)⁻¹ := by
  have hlen : ((to_list x).length : ℤ) = size_out := Params.spec_dout x
  have h := map_mu1_inj dout Params.to_list_inj x
  change (Params.dout >>= fun a => (pure (Params.to_list a) : SubProbability _)).1
    {Params.to_list x} = _ at h
  rw [Params.dout_equal_dlist, dlist1E _ _ (Params.to_list x) (Params.spec_dout x)] at h
  change _ = dout.1 {x} at h
  rw [← h]
  simp only [dbool1E, List.map_const', List.prod_replicate, ENNReal.toReal_pow,
    ENNReal.toReal_inv]
  have hl : ((Params.to_list x).length : ℤ) = size_out := hlen
  rw [← zpow_natCast, hl, ENNReal.toReal_ofNat, inv_zpow]

/-- `fun c m => c + ((size m + 1) %/ r + 1) + max ((size_out + r - 1) %/ r - 1) 0`, the clones'
`increase_counter` (an abbreviation, not an EasyCrypt declaration). -/
def clone_increase_counter (c : ℤ) (m : List Bool) : ℤ :=
  c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0

/-! ## `clone import SecureORO as SORO with type from <- bool list, type to <- f_out,
op sampleto <- dout, op bound <- sigma, op increase_counter <- …` -/

namespace SORO
/-- The clone's module variables. -/
global_var RO.RO.m : FMap (List Bool) f_out
global_var RO.FRO.m : FMap (List Bool) (f_out × flag)
global_var Bounder.bounder : ℤ
abbrev RF_T := SecureORO.RF_T (List Bool) f_out
noncomputable abbrev RF := SecureORO.RF (List Bool) f_out
abbrev Oracle := SecureORO.Oracle (List Bool) f_out
abbrev AdvPreimage := SecureORO.AdvPreimage (List Bool) f_out
abbrev AdvSecondPreimage := SecureORO.AdvSecondPreimage (List Bool) f_out
abbrev AdvCollision := SecureORO.AdvCollision (List Bool) f_out
noncomputable abbrev Bounder := SecureORO.Bounder (List Bool) f_out sigma Bounder.bounder
noncomputable abbrev Preimage := SecureORO.Preimage (List Bool) f_out dout sigma Bounder.bounder
noncomputable abbrev SecondPreimage := SecureORO.SecondPreimage (List Bool) f_out sigma
  Bounder.bounder
noncomputable abbrev Collision := SecureORO.Collision (List Bool) f_out sigma Bounder.bounder
noncomputable abbrev RO.RO := SecureORO.RO.RO (List Bool) f_out dout RO.RO.m
/-- The clone's `realize bound_ge0`, `sampleto_ll`, `sampleto_fu`, `sampleto_full`,
`increase_counter_spec`. -/
theorem axioms : SecureORO.Axioms (List Bool) f_out dout sigma clone_increase_counter := by
  sorry
end SORO

/-! ## `clone import SecureHash as SH with type from <- bool list, type to <- f_out,
type block <- state, op sampleto <- dout, op bound <- sigma, op increase_counter <- …` -/

namespace SH
/-- The clone's module variable. -/
global_var Bounder.bounder : ℤ
namespace OIndif
abbrev OPRIMITIVE := OptionIndifferentiability.OPRIMITIVE state (List Bool) f_out
abbrev ODPRIMITIVE := OptionIndifferentiability.ODPRIMITIVE state (List Bool) f_out
abbrev OFUNCTIONALITY := OptionIndifferentiability.OFUNCTIONALITY state (List Bool) f_out
abbrev ODFUNCTIONALITY := OptionIndifferentiability.ODFUNCTIONALITY state (List Bool) f_out
abbrev OCONSTRUCTION := OptionIndifferentiability.OCONSTRUCTION state (List Bool) f_out
noncomputable abbrev distExt := OptionIndifferentiability.distExt state (List Bool) f_out
end OIndif
abbrev AdvPreimage := SecureHash.AdvPreimage (List Bool) f_out state
abbrev AdvSecondPreimage := SecureHash.AdvSecondPreimage (List Bool) f_out state
abbrev AdvCollision := SecureHash.AdvCollision (List Bool) f_out state
noncomputable abbrev Preimage := SecureHash.Preimage (List Bool) f_out state dout sigma
  clone_increase_counter Bounder.bounder
noncomputable abbrev SecondPreimage := SecureHash.SecondPreimage (List Bool) f_out state sigma
  clone_increase_counter Bounder.bounder
noncomputable abbrev Collision := SecureHash.Collision (List Bool) f_out state sigma
  clone_increase_counter Bounder.bounder
/-- The clone's `realize sampleto_ll`, `sampleto_fu`, `sampleto_full`, `bound_ge0`,
`increase_counter_spec`. -/
theorem axioms : SecureHash.Axioms (List Bool) f_out dout sigma clone_increase_counter := by
  sorry
end SH

-- EC's `FSetSize(F : OFUNCTIONALITY) : OIndif.OFUNCTIONALITY`; its `proc init = F.init` is wrapped
-- in a call (exception E5); `proc get = f`, outside the type, is `FSetSize.get`
module FSetSize using (F : OFUNCTIONALITY) : SH.OIndif.OFUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (x : List Bool) : (Option f_out) {
    var y : Option (List Bool), r : Option f_out;
    y <- call F.f (($x, size_out));
    r <- if $y ≠ none then of_list (oget $y) else none;
    return $r
  };
}

/-- `FSetSize`'s `proc get = f`: the same procedure as `FSetSize.f`. -/
noncomputable abbrev FSetSize.get := FSetSize.f

module DFSetSize using (F : ODFUNCTIONALITY) : SH.OIndif.OFUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (x : List Bool) : (Option f_out) {
    var y : Option (List Bool), r : Option f_out;
    y <- call F.f (($x, size_out));
    r <- if $y ≠ none then of_list (oget $y) else none;
    return $r
  };
}

module FIgnoreSize using (F : SH.OIndif.ODFUNCTIONALITY) : OFUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (xi : List Bool × ℤ) : (Option (List Bool)) {
    var x : List Bool, i : ℤ, y : Option f_out, r : Option f_out;
    x, i <- $xi;
    y <- (default : Option f_out);
    r <- (default : Option f_out);
    y <- call F.f ($x);
    return Option.map to_list $r
  };
}

/-- `module (OSponge : OIndif.OCONSTRUCTION) (P : OIndif.ODPRIMITIVE) = FSetSize(CSome(Sponge,
P))`. -/
noncomputable def OSponge : SH.OIndif.OCONSTRUCTION := Module.comp FSetSize (CSome Sponge.Sponge)

/-! `clone import Program as PBool with type t <- bool, op d <- dbool` -/

namespace PBool
noncomputable abbrev LoopSnoc.sample := DList.Program.LoopSnoc.sample Bool dbool
end PBool

/-! `clone import FullRO as Eager with type in_t <- bool list * int, type out_t <- bool,
op dout _ <- dbool, type d_in_t <- unit, type d_out_t <- bool` -/

namespace Eager
/-- The clone's module variables. -/
global_var RO.m : FMap (List Bool × ℤ) Bool
global_var FRO.m : FMap (List Bool × ℤ) (Bool × flag)
abbrev RO_T := PROM.FullRO.RO_T (List Bool × ℤ) Bool
abbrev RO_Distinguisher := PROM.FullRO.RO_Distinguisher (List Bool × ℤ) Bool Unit Bool
noncomputable abbrev RO := PROM.FullRO.RO.asRO (List Bool × ℤ) Bool (fun _ => dbool) RO.m
noncomputable abbrev LRO := PROM.FullRO.LRO (List Bool × ℤ) Bool (fun _ => dbool) RO.m
end Eager

/-- The restriction on the sections' `A` that their closed statements keep: `{-Perm, -F.RO, -F.FRO,
-Redo, -C, -Gconcl.S, -BlockSponge.BIRO.IRO, -BlockSponge.C, -BIRO.IRO, -Gconcl_list.BIRO2.IRO,
-Gconcl_list.F2.RO, -Gconcl_list.F2.FRO, -Gconcl_list.Simulator, -SHA3Indiff.Simulator,
-SHA3Indiff.Cntr, -SHA3_OIndiff.Counter, -SORO.RO.RO, -SORO.Bounder, -SH.Bounder, -Eager.RO,
-Eager.FRO}` (as printed by EasyCrypt), without `SecondPreimage`'s and `Collision`'s
`-SORO.RO.FRO` (an abbreviation). -/
noncomputable def ARestrictions.footprint : Footprint VariableAssignment :=
  (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ (SLCommon.F.RO.m).footprint ⊔
    (SLCommon.F.FRO.m).footprint ⊔ (SLCommon.Redo.prefixes).footprint ⊔ SLCommon.C.footprint ⊔
    (Gconcl.S.m).footprint ⊔ (Gconcl.S.mi).footprint ⊔ (Gconcl.S.paths).footprint ⊔
    (BlockSponge.BIRO.IRO.mp).footprint ⊔ BlockSponge.C.c.footprint ⊔ (BIRO.IRO.mp).footprint ⊔
    (Gconcl_list.BIRO2.IRO.mp).footprint ⊔ (Gconcl_list.F2.RO.m).footprint ⊔
    (Gconcl_list.F2.FRO.m).footprint ⊔ (Gconcl_list.Simulator.m).footprint ⊔
    (Gconcl_list.Simulator.mi).footprint ⊔ (Gconcl_list.Simulator.paths).footprint ⊔
    (Gconcl_list.Simulator.unvalid_map).footprint ⊔ (SHA3Indiff.Simulator.m).footprint ⊔
    (SHA3Indiff.Simulator.mi).footprint ⊔ (SHA3Indiff.Simulator.paths).footprint ⊔
    SHA3Indiff.Cntr.c.footprint ⊔ SHA3_OIndiff.Counter.c.footprint ⊔ (SORO.RO.RO.m).footprint ⊔
    SORO.Bounder.bounder.footprint ⊔ SH.Bounder.bounder.footprint ⊔ (Eager.RO.m).footprint ⊔
    (Eager.FRO.m).footprint

/-- The bound `(limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r` of the
headline lemmas, at this file's `limit` (an abbreviation). -/
noncomputable def bound : ℝ :=
  ((limit ^ 2 - limit : ℤ) : ℝ) / ((2 ^ (r + c + 1).toNat : ℤ) : ℝ) +
    ((4 * limit ^ 2 : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)

/-- `OIndif(F, OSimulator(F), D)`, `SHA3_OIndiff.OIndif.OIndif` with the simulator `OSimulator`
on `F` (an abbreviation). -/
noncomputable def IdealGame (F : OFUNCTIONALITY) (D : ODISTINGUISHER) : procmod () → Bool :=
  Module.app OIndif.OIndif (Module.pair F (Module.pair
    (Module.app OSimulator (OptionIndifferentiability.OFUNCTIONALITY.view state (List Bool × ℤ)
      (List Bool) F)) D))

/-- The headline lemmas' hypothesis on `A`: `forall (F <: OIndif.ODFUNCTIONALITY)
(P <: OIndif.ODPRIMITIVE), islossless F.f => islossless P.f => islossless P.fi =>
islossless A(F, P).guess` (an abbreviation). -/
def A_lossless {sig : ProcedureSignature}
    (A : SH.OIndif.ODFUNCTIONALITY ×ₘ SH.OIndif.ODPRIMITIVE →ₘ Module.Proc sig) : Prop :=
  ∀ (F : SH.OIndif.ODFUNCTIONALITY) (P : SH.OIndif.ODPRIMITIVE),
    (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool) f_out F).procedure.IsLossless →
    (OptionIndifferentiability.ODPRIMITIVE.f state (List Bool) f_out P).procedure.IsLossless →
    (OptionIndifferentiability.ODPRIMITIVE.fi state (List Bool) f_out P).procedure.IsLossless →
    (Module.app A (Module.pair F P)).procedure.IsLossless

/-- The section `Preimage`'s op `inv`: the map of `BIRO.IRO` and `RFList.m` agree on the first
`size_out` bits. -/
def inv (m1 : FMap (List Bool × ℤ) Bool) (m2 : FMap (List Bool) f_out) : Prop :=
  (∀ l i, FMap.dom m1 (l, i) → 0 ≤ i ∧ i < size_out) ∧
  (∀ l i, FMap.dom m1 (l, i) → FMap.dom m2 l) ∧
  (∀ l, FMap.dom m2 l → ∀ i, 0 ≤ i ∧ i < size_out → FMap.dom m1 (l, i)) ∧
  (∀ l i, FMap.dom m1 (l, i) →
    FMap.get m1 (l, i) = some (nth default (to_list (oget (FMap.get m2 l))) i))

/-- The section `Preimage`'s op `eq_extend_size`. -/
def eq_extend_size (m1 m2 m3 : FMap (List Bool × ℤ) Bool) : Prop :=
  (∀ x j, 0 ≤ j ∧ j < size_out → FMap.get m1 (x, j) = FMap.get m2 (x, j)) ∧
  (∀ x j, size_out ≤ j → FMap.get m1 (x, j) = FMap.get m3 (x, j)) ∧
  (∀ x j, FMap.dom m1 (x, j) → 0 ≤ j)

/-- The sections' local variables are fresh (EasyCrypt's semantics of local modules; exception E6):
disjoint from each other and from the games' variables (an abbreviation). -/
def LocalFresh (Log_m : Lens (FMap (List Bool × ℤ) Bool) VariableAssignment)
    (RFList_m : Lens (FMap (List Bool) f_out) VariableAssignment) : Prop :=
  Log_m.footprint ⊔ RFList_m.footprint ≤ ARestrictions.footprintᶜ ∧
    Log_m.footprint ≤ RFList_m.footprintᶜ

/-! ## The section `Preimage`, with `declare module A <: SH.AdvPreimage {…}` (its local
declarations in the namespace `Preimage`) -/

namespace Preimage

/-! The local modules' variables `Log.m`, `RFList.m` are the lens parameters `Log_m`,
`RFList_m` (exception E6). -/
-- one binder each: a `module` takes a whole binder group when it mentions one of its names
variable (Log_m : Lens (FMap (List Bool × ℤ) Bool) VariableAssignment)
variable (RFList_m : Lens (FMap (List Bool) f_out) VariableAssignment)

-- EC's local `FInit(F : OIndif.ODFUNCTIONALITY) : OIndif.OFUNCTIONALITY`; `proc f = F.f` is
-- wrapped in a call (exception E5)
module FInit using (F : SH.OIndif.ODFUNCTIONALITY) : SH.OIndif.OFUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (x : List Bool) : (Option f_out) {
    var y : Option f_out;
    y <- call F.f ($x);
    return $y
  };
}

-- EC's local `PInit(P : ODPRIMITIVE) : OPRIMITIVE`; its aliases are wrapped in a call (E5)
module PInit using (P : ODPRIMITIVE) : OPRIMITIVE {
  proc init () : Unit {
    return ()
  };
  proc f (x : state) : (Option state) {
    var y : Option state;
    y <- call P.f ($x);
    return $y
  };
  proc fi (x : state) : (Option state) {
    var y : Option state;
    y <- call P.fi ($x);
    return $y
  };
}

-- EC's local `OF(F : Oracle) : OIndif.ODFUNCTIONALITY`; `proc f = F.get` is wrapped in a call (E5)
module OF using (F : SORO.Oracle) : SH.OIndif.ODFUNCTIONALITY {
  proc f (x : List Bool) : (Option f_out) {
    var y : Option f_out;
    y <- call F.get ($x);
    return $y
  };
}

module ExtendOutputSize using (F : SORO.Oracle) : ODFUNCTIONALITY {
  proc f (xk : List Bool × ℤ) : (Option (List Bool)) {
    var x : List Bool, k : ℤ, o : Option f_out, l : Option (List Bool), suffix : List Bool,
      «prefix» : List Bool, i : ℤ, r : Bool;
    x, k <- $xk;
    l <- (none : Option (List Bool));
    «prefix» <- [];
    suffix <- [];
    o <- call F.get ($x);
    «prefix» <- take $k (to_list (oget $o));
    i <- size_out;
    while ($i < $k) {
      if (!(decide (FMap.dom ($Log_m : FMap (List Bool × ℤ) Bool) ($x, $i)))) {
        r <$ dbool;
        Log_m <- FMap.set $Log_m ($x, $i) $r;
      }
      suffix <- rcons $suffix (oget (FMap.get $Log_m ($x, $i)));
      i <- $i + 1;
    }
    l <- some ($«prefix» ++ $suffix);
    return $l
  };
}

/-- `local module OFC2 (F : Oracle) = OFC(ExtendOutputSize(F))`. -/
noncomputable def OFC2 : SORO.Oracle →ₘ OFUNCTIONALITY := Module.comp OFC (ExtendOutputSize Log_m)

-- EC's local `ExtendOutput(F : RF)`; `proc f = ExtendOutputSize(F).f` is wrapped in a call
-- (E5), and `proc get = f` is `ExtendOutput.get`
module ExtendOutput using (F : SORO.RF_T) {
  proc init () : Unit {
    Log_m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    _ <- call F.init ();
    return ()
  };
  proc f (xk : List Bool × ℤ) : (Option (List Bool)) {
    var y : Option (List Bool);
    y <- call (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
      (Module.app (ExtendOutputSize Log_m) (SecureORO.Oracle.mk (List Bool) f_out
        { get := SecureORO.RF_T.get (List Bool) f_out F }))) ($xk);
    return $y
  };
}

/-- `ExtendOutput`'s `proc get = f`: the same procedure as `ExtendOutput.f`. -/
noncomputable abbrev ExtendOutput.get := ExtendOutput.f

-- EC's local `(Dist_of_P1Adv (A : SH.AdvPreimage) : ODISTINGUISHER)
-- (F : ODFUNCTIONALITY) (P : ODPRIMITIVE)`, with `A` a Lean parameter
open Classical in
set_option linter.gaudisCrypt.using false in
module Dist_of_P1Adv (A : SH.AdvPreimage) using (F : ODFUNCTIONALITY, P : ODPRIMITIVE) {
  proc distinguish () : Bool {
    var hash : f_out, hash' : Option f_out, m : List Bool;
    Log_m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    hash <$ dout;
    m <- call (Module.app A (Module.pair (OptionIndifferentiability.ODFUNCTIONALITY.mk state
        (List Bool) f_out
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
            (Module.app DFSetSize F) }) P)) ($hash);
    hash' <- call (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
        (Module.app DFSetSize F)) ($m);
    return decide ($hash' = some $hash)
  };
}

-- EC's local `(SORO_P1 (A : SH.AdvPreimage) : SORO.AdvPreimage)
-- (F : Oracle)`, with `A` a Lean parameter; `OFC2(F)` is written out as
-- `OFC(ExtendOutputSize(F))`
set_option maxHeartbeats 10000000 in
-- the `module` command's typing proof of this nest of oracles is slow (about 20 s)
set_option linter.gaudisCrypt.using false in
module SORO_P1 (A : SH.AdvPreimage) using (F : SORO.Oracle) {
  proc guess (h : f_out) : (List Bool) {
    var mi : List Bool;
    Log_m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    SHA3_OIndiff.Counter.c <- 0;
    _ <- call (OptionIndifferentiability.OPRIMITIVE.init state (List Bool × ℤ) (List Bool)
      (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F))) ();
    mi <- call (Module.app A (Module.pair
      (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool) f_out
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
            (Module.app DFSetSize (OptionIndifferentiability.ODFUNCTIONALITY.mk state
                (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app OFC (Module.app (ExtendOutputSize Log_m) F)) })) })
      (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool) f_out
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OPC (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool × ℤ)
                (List Bool)
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F))
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F)) }))
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OPC (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool × ℤ)
                (List Bool)
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F))
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F)) })) }))) ($h);
    return $mi
  };
}

module RFList : SORO.RF_T {
  proc init () : Unit {
    RFList_m <- (FMap.empty : FMap (List Bool) f_out);
    return ()
  };
  proc get (x : List Bool) : (Option f_out) {
    var z : List Bool;
    if (!(decide (FMap.dom ($RFList_m : FMap (List Bool) f_out) $x))) {
      z <$ dlist dbool size_out;
      RFList_m <- FMap.set $RFList_m $x (oget (of_list $z));
    }
    return FMap.get ($RFList_m : FMap (List Bool) f_out) $x
  };
  proc sample (_x : List Bool) : Unit {
    return ()
  };
}

module RFWhile : SORO.RF_T {
  proc init () : Unit {
    RFList_m <- (FMap.empty : FMap (List Bool) f_out);
    return ()
  };
  proc get (x : List Bool) : (Option f_out) {
    var l : List Bool, i : ℤ, b : Bool;
    if (!(decide (FMap.dom ($RFList_m : FMap (List Bool) f_out) $x))) {
      i <- 0;
      l <- [];
      while ($i < size_out) {
        b <$ dbool;
        l <- rcons $l $b;
        i <- $i + 1;
      }
      RFList_m <- FMap.set $RFList_m $x (oget (of_list $l));
    }
    return FMap.get ($RFList_m : FMap (List Bool) f_out) $x
  };
  proc sample (_x : List Bool) : Unit {
    return ()
  };
}

/-- `local equiv rw_RF_List_While : RFList.get ~ RFWhile.get : ={arg, glob RFList} ==>
={res, glob RFWhile}`. -/
theorem rw_RF_List_While :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ RFList_m.get g₁ = RFList_m.get g₂)
      (SecureORO.RF_T.get (List Bool) f_out (RFList RFList_m)).procedure
      (SecureORO.RF_T.get (List Bool) f_out (RFWhile RFList_m)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ RFList_m.get g₁ = RFList_m.get g₂) := by
  sorry

/-- `local equiv eq_IRO_RFWhile : BIRO.IRO.f ~ RFWhile.get : arg{1} = (x{2}, size_out) /\
inv BIRO.IRO.mp{1} RFList.m{2} ==> res{2} = of_list res{1} /\ size res{1} = size_out /\
inv BIRO.IRO.mp{1} RFList.m{2}`. -/
theorem eq_IRO_RFWhile (_hfresh : LocalFresh Log_m RFList_m) :
    prhlProc (sig₁ := procsig (List Bool × ℤ) -> (List Bool))
      (sig₂ := procsig (List Bool) -> (Option f_out))
      (fun a₁ g₁ a₂ g₂ => a₁ = (a₂, size_out) ∧ inv (BIRO.IRO.mp.get g₁) (RFList_m.get g₂))
      BIRO.IRO.f.procedure (SecureORO.RF_T.get (List Bool) f_out (RFWhile RFList_m)).procedure
      (fun r₁ g₁ r₂ g₂ => r₂ = of_list r₁ ∧ size r₁ = size_out ∧
        inv (BIRO.IRO.mp.get g₁) (RFList_m.get g₂)) := by
  sorry

-- EC's local `ExtendSample(F : OFUNCTIONALITY)`; `proc init = F.init` is wrapped in a call (E5)
module ExtendSample using (F : OFUNCTIONALITY) : OFUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (xk : List Bool × ℤ) : (Option (List Bool)) {
    var x : List Bool, k : ℤ, y : Option (List Bool);
    x, k <- $xk;
    if (decide ($k ≤ size_out)) {
      y <- call F.f (($x, size_out));
      y <- Option.map (take $k) $y;
    } else {
      y <- call F.f (($x, $k));
    }
    return $y
  };
}

/-- `local equiv eq_extend : ExtendSample(FSome(BIRO.IRO)).f ~
ExtendOutputSize(FSetSize(FSome(BIRO.IRO))).f : ={arg} /\
eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2} ==> ={res} /\ …`. -/
theorem eq_extend (_hfresh : LocalFresh Log_m RFList_m) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧
        eq_extend_size (BIRO.IRO.mp.get g₁) (BIRO.IRO.mp.get g₂) (Log_m.get g₂))
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))).procedure
      (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app (ExtendOutputSize Log_m) (SecureORO.Oracle.mk (List Bool) f_out
          { get := Module.app FSetSize.get (Module.app FSome BIRO.IRO.asF) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        eq_extend_size (BIRO.IRO.mp.get g₁) (BIRO.IRO.mp.get g₂) (Log_m.get g₂)) := by
  sorry

theorem of_listK (l : f_out) : of_list (to_list l) = some l :=
  (Params.to_listK l (to_list l)).mp rfl

-- EC's local `Fill_In(F : RO)`; `proc init = F.init` is wrapped in a call (E5)
module Fill_In using (F : Eager.RO_T) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (xn : List Bool × ℤ) : (List Bool) {
    var x : List Bool, n : ℤ, l : List Bool, b : Bool, i : ℤ;
    x, n <- $xn;
    i <- 0;
    l <- [];
    while ($i < $n) {
      b <- call F.get (($x, $i));
      l <- rcons $l $b;
      i <- $i + 1;
    }
    while ($i < size_out) {
      _ <- call F.sample (($x, $i));
      i <- $i + 1;
    }
    return $l
  };
}

/-- `local equiv eq_eager_ideal : BIRO.IRO.f ~ Fill_In(LRO).f : ={arg} /\ BIRO.IRO.mp{1} = RO.m{2}
==> ={res} /\ BIRO.IRO.mp{1} = RO.m{2}`. -/
theorem eq_eager_ideal :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂)
      BIRO.IRO.f.procedure (Module.app Fill_In.f Eager.LRO).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂) := by
  sorry

/-- `local equiv eq_eager_ideal2 : ExtendSample(FSome(BIRO.IRO)).f ~ FSome(Fill_In(RO)).f :
={arg} /\ BIRO.IRO.mp{1} = RO.m{2} ==> ={res} /\ BIRO.IRO.mp{1} = RO.m{2}`. -/
theorem eq_eager_ideal2 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂)
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))).procedure
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app FSome (Module.app Fill_In Eager.RO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂) := by
  sorry

-- EC's local `Dist(F : RO)`, `proc distinguish = SHA3_OIndiff.OIndif.OIndif(FSome(Fill_In(F)),
-- OSimulator(FSome(Fill_In(F))), ODRestr(Dist_of_P1Adv(A))).main`, with the section's `A` a Lean
-- parameter; the alias is wrapped in a call (E5), and `distinguish` takes `RO_Distinguisher`'s
-- `unit` (`RO_LRO_D Dist`)
set_option linter.gaudisCrypt.using false in
module Dist (A : SH.AdvPreimage) using (F : Eager.RO_T) {
  proc distinguish (_x : Unit) : Bool {
    var b : Bool;
    b <- call (Module.app OIndif.OIndif (Module.pair (Module.app FSome (Module.app Fill_In F))
      (Module.pair (Module.app OSimulator (OptionIndifferentiability.ODFUNCTIONALITY.mk state
          (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app FSome (Module.app Fill_In F)) }))
        (ODRestr (Dist_of_P1Adv Log_m A))))) ();
    return $b
  };
}

-- EC's local `Game(F : RO)`, with the section's `A` a Lean parameter
set_option linter.gaudisCrypt.using false in
module Game (A : SH.AdvPreimage) using (F : Eager.RO_T) {
  proc distinguish () : Bool {
    var bo : Bool;
    _ <- call (OptionIndifferentiability.OPRIMITIVE.init state (List Bool × ℤ) (List Bool)
      (Module.app OSimulator (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool × ℤ)
          (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app FSome (Module.app Fill_In F)) }))) ();
    SHA3_OIndiff.Counter.c <- 0;
    Log_m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    _ <- call F.init ();
    bo <- call (Module.app (Dist Log_m A) F) (());
    return $bo
  };
}

/-- `local lemma eager_ideal &m`. -/
theorem eager_ideal (A : SH.AdvPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_P1Adv Log_m A))).procedure () m (fun r _ => r = true) =
      Procedure.Pr (IdealGame (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))
        (ODRestr (Dist_of_P1Adv Log_m A))).procedure () m (fun r _ => r = true) := by
  sorry

/-- `local lemma rw_ideal_2 &m`. -/
theorem rw_ideal_2 (A : SH.AdvPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    (Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_P1Adv Log_m A))).procedure () m (fun r _ => r = true) : ℝ) ≤
      Procedure.Pr (Module.app SORO.Preimage (Module.pair (SORO_P1 Log_m A)
        (RFList RFList_m))).procedure () m (fun r _ => r = true) := by
  sorry

/-- `local lemma rw_ideal &m`. -/
theorem rw_ideal (A : SH.AdvPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    (Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_P1Adv Log_m A))).procedure () m (fun r _ => r = true) : ℝ) ≤
      Procedure.Pr (Module.app SORO.Preimage (Module.pair (SORO_P1 Log_m A)
        (Module.app SORO.RF SORO.RO.RO))).procedure () m (fun r _ => r = true) := by
  sorry

/-- `local lemma leq_ideal &m`. -/
theorem leq_ideal (A : SH.AdvPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    (Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_P1Adv Log_m A))).procedure () m (fun r _ => r = true) : ℝ) ≤
      ((sigma + 1 : ℤ) : ℝ) / (2 : ℝ) ^ size_out := by
  sorry

/-- `local lemma rw_real &m`. -/
theorem rw_real (A : SH.AdvPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    Procedure.Pr (Module.app SH.Preimage (Module.pair A (Module.pair OSponge
        (PSome Perm)))).procedure
        () m (fun r _ => r = true) =
      Procedure.Pr (Module.app OIndif.OIndif (Module.pair
        (Module.app FSome (Module.app Sponge.Sponge (Module.app Poget
          (OptionIndifferentiability.OPRIMITIVE.view state (List Bool × ℤ) (List Bool)
              (PSome Perm)))))
        (Module.pair (PSome Perm) (ODRestr (Dist_of_P1Adv Log_m A))))).procedure () m
            (fun r _ => r = true) := by
  sorry

end Preimage

/-- EC's `Sponge_preimage_resistant (A <: SH.AdvPreimage {…}) &m`.
-/
theorem Sponge_preimage_resistant (A : SH.AdvPreimage)
    (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint)ᶜ)
    (m : VariableAssignment) :
    A_lossless A →
    (Procedure.Pr (Module.app SH.Preimage (Module.pair A (Module.pair OSponge
        (PSome Perm)))).procedure
        () m (fun r _ => r = true) : ℝ) ≤
      bound + ((sigma + 1 : ℤ) : ℝ) / (2 : ℝ) ^ size_out := by
  sorry

/-! ## The section `SecondPreimage`, with `declare module A <: SH.AdvSecondPreimage {…,
-SORO.RO.FRO}` (its local
declarations in the namespace `SecondPreimage`) -/

namespace SecondPreimage

/-! The local modules' variables `Log.m`, `RFList.m`, `Dist_of_P2Adv.m` are the lens parameters
`Log_m`,
`RFList_m`, `Dist_of_P2Adv_m` (exception E6). -/
-- one binder each: a `module` takes a whole binder group when it mentions one of its names
variable (Log_m : Lens (FMap (List Bool × ℤ) Bool) VariableAssignment)
variable (RFList_m : Lens (FMap (List Bool) f_out) VariableAssignment)
variable (Dist_of_P2Adv_m : Lens (List Bool) VariableAssignment)

-- EC's local `FInit(F : OIndif.ODFUNCTIONALITY) : OIndif.OFUNCTIONALITY`; `proc f = F.f` is
-- wrapped in a call (exception E5)
module FInit using (F : SH.OIndif.ODFUNCTIONALITY) : SH.OIndif.OFUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (x : List Bool) : (Option f_out) {
    var y : Option f_out;
    y <- call F.f ($x);
    return $y
  };
}

-- EC's local `PInit(P : ODPRIMITIVE) : OPRIMITIVE`; its aliases are wrapped in a call (E5)
module PInit using (P : ODPRIMITIVE) : OPRIMITIVE {
  proc init () : Unit {
    return ()
  };
  proc f (x : state) : (Option state) {
    var y : Option state;
    y <- call P.f ($x);
    return $y
  };
  proc fi (x : state) : (Option state) {
    var y : Option state;
    y <- call P.fi ($x);
    return $y
  };
}

-- EC's local `OF(F : Oracle) : OIndif.ODFUNCTIONALITY`; `proc f = F.get` is wrapped in a call (E5)
module OF using (F : SORO.Oracle) : SH.OIndif.ODFUNCTIONALITY {
  proc f (x : List Bool) : (Option f_out) {
    var y : Option f_out;
    y <- call F.get ($x);
    return $y
  };
}

module ExtendOutputSize using (F : SORO.Oracle) : ODFUNCTIONALITY {
  proc f (xk : List Bool × ℤ) : (Option (List Bool)) {
    var x : List Bool, k : ℤ, o : Option f_out, l : Option (List Bool), suffix : List Bool,
      «prefix» : List Bool, i : ℤ, r : Bool;
    x, k <- $xk;
    l <- (none : Option (List Bool));
    «prefix» <- [];
    suffix <- [];
    o <- call F.get ($x);
    «prefix» <- take $k (to_list (oget $o));
    i <- size_out;
    while ($i < $k) {
      if (!(decide (FMap.dom ($Log_m : FMap (List Bool × ℤ) Bool) ($x, $i)))) {
        r <$ dbool;
        Log_m <- FMap.set $Log_m ($x, $i) $r;
      }
      suffix <- rcons $suffix (oget (FMap.get $Log_m ($x, $i)));
      i <- $i + 1;
    }
    l <- some ($«prefix» ++ $suffix);
    return $l
  };
}

/-- `local module OFC2 (F : Oracle) = OFC(ExtendOutputSize(F))`. -/
noncomputable def OFC2 : SORO.Oracle →ₘ OFUNCTIONALITY := Module.comp OFC (ExtendOutputSize Log_m)

-- EC's local `ExtendOutput(F : RF)`; `proc f = ExtendOutputSize(F).f` is wrapped in a call
-- (E5), and `proc get = f` is `ExtendOutput.get`
module ExtendOutput using (F : SORO.RF_T) {
  proc init () : Unit {
    Log_m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    _ <- call F.init ();
    return ()
  };
  proc f (xk : List Bool × ℤ) : (Option (List Bool)) {
    var y : Option (List Bool);
    y <- call (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
      (Module.app (ExtendOutputSize Log_m) (SecureORO.Oracle.mk (List Bool) f_out
        { get := SecureORO.RF_T.get (List Bool) f_out F }))) ($xk);
    return $y
  };
}

/-- `ExtendOutput`'s `proc get = f`: the same procedure as `ExtendOutput.f`. -/
noncomputable abbrev ExtendOutput.get := ExtendOutput.f

-- EC's local `(Dist_of_P2Adv (A : SH.AdvSecondPreimage) : ODISTINGUISHER)
-- (F : ODFUNCTIONALITY) (P : ODPRIMITIVE)`, with `A` a Lean parameter
open Classical in
set_option linter.gaudisCrypt.using false in
module Dist_of_P2Adv (A : SH.AdvSecondPreimage) using (F : ODFUNCTIONALITY, P : ODPRIMITIVE) {
  proc distinguish () : Bool {
    var hash : Option f_out, hash' : Option f_out, m' : List Bool;
    Log_m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    m' <- call (Module.app A (Module.pair (OptionIndifferentiability.ODFUNCTIONALITY.mk state
        (List Bool) f_out
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
            (Module.app DFSetSize F) }) P)) ($Dist_of_P2Adv_m);
    hash <- call (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
        (Module.app DFSetSize F))
      ($Dist_of_P2Adv_m);
    hash' <- call (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
        (Module.app DFSetSize F)) ($m');
    return decide ($Dist_of_P2Adv_m ≠ $m' ∧ ∃ y, $hash' = some y ∧ $hash = some y)
  };
}

-- EC's local `(SORO_P2 (A : SH.AdvSecondPreimage) : SORO.AdvSecondPreimage)
-- (F : Oracle)`, with `A` a Lean parameter; `OFC2(F)` is written out as
-- `OFC(ExtendOutputSize(F))`
set_option maxHeartbeats 10000000 in
-- the `module` command's typing proof of this nest of oracles is slow (about 20 s)
set_option linter.gaudisCrypt.using false in
module SORO_P2 (A : SH.AdvSecondPreimage) using (F : SORO.Oracle) {
  proc guess (m : List Bool) : (List Bool) {
    var mi : List Bool;
    Log_m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    SHA3_OIndiff.Counter.c <- 0;
    Dist_of_P2Adv_m <- $m;
    _ <- call (OptionIndifferentiability.OPRIMITIVE.init state (List Bool × ℤ) (List Bool)
      (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F))) ();
    mi <- call (Module.app A (Module.pair
      (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool) f_out
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
            (Module.app DFSetSize (OptionIndifferentiability.ODFUNCTIONALITY.mk state
                (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app OFC (Module.app (ExtendOutputSize Log_m) F)) })) })
      (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool) f_out
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OPC (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool × ℤ)
                (List Bool)
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F))
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F)) }))
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OPC (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool × ℤ)
                (List Bool)
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F))
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F)) })) }))) ($m);
    return $mi
  };
}

module RFList : SORO.RF_T {
  proc init () : Unit {
    RFList_m <- (FMap.empty : FMap (List Bool) f_out);
    return ()
  };
  proc get (x : List Bool) : (Option f_out) {
    var z : List Bool;
    if (!(decide (FMap.dom ($RFList_m : FMap (List Bool) f_out) $x))) {
      z <$ dlist dbool size_out;
      RFList_m <- FMap.set $RFList_m $x (oget (of_list $z));
    }
    return FMap.get ($RFList_m : FMap (List Bool) f_out) $x
  };
  proc sample (_x : List Bool) : Unit {
    return ()
  };
}

module RFWhile : SORO.RF_T {
  proc init () : Unit {
    RFList_m <- (FMap.empty : FMap (List Bool) f_out);
    return ()
  };
  proc get (x : List Bool) : (Option f_out) {
    var l : List Bool, i : ℤ, b : Bool;
    if (!(decide (FMap.dom ($RFList_m : FMap (List Bool) f_out) $x))) {
      i <- 0;
      l <- [];
      while ($i < size_out) {
        b <$ dbool;
        l <- rcons $l $b;
        i <- $i + 1;
      }
      RFList_m <- FMap.set $RFList_m $x (oget (of_list $l));
    }
    return FMap.get ($RFList_m : FMap (List Bool) f_out) $x
  };
  proc sample (_x : List Bool) : Unit {
    return ()
  };
}

/-- `local equiv rw_RF_List_While : RFList.get ~ RFWhile.get : ={arg, glob RFList} ==>
={res, glob RFWhile}`. -/
theorem rw_RF_List_While :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ RFList_m.get g₁ = RFList_m.get g₂)
      (SecureORO.RF_T.get (List Bool) f_out (RFList RFList_m)).procedure
      (SecureORO.RF_T.get (List Bool) f_out (RFWhile RFList_m)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ RFList_m.get g₁ = RFList_m.get g₂) := by
  sorry

/-- `local equiv eq_IRO_RFWhile : BIRO.IRO.f ~ RFWhile.get : arg{1} = (x{2}, size_out) /\
inv BIRO.IRO.mp{1} RFList.m{2} ==> res{2} = of_list res{1} /\ size res{1} = size_out /\
inv BIRO.IRO.mp{1} RFList.m{2}`. -/
theorem eq_IRO_RFWhile (_hfresh : LocalFresh Log_m RFList_m) :
    prhlProc (sig₁ := procsig (List Bool × ℤ) -> (List Bool))
      (sig₂ := procsig (List Bool) -> (Option f_out))
      (fun a₁ g₁ a₂ g₂ => a₁ = (a₂, size_out) ∧ inv (BIRO.IRO.mp.get g₁) (RFList_m.get g₂))
      BIRO.IRO.f.procedure (SecureORO.RF_T.get (List Bool) f_out (RFWhile RFList_m)).procedure
      (fun r₁ g₁ r₂ g₂ => r₂ = of_list r₁ ∧ size r₁ = size_out ∧
        inv (BIRO.IRO.mp.get g₁) (RFList_m.get g₂)) := by
  sorry

-- EC's local `ExtendSample(F : OFUNCTIONALITY)`; `proc init = F.init` is wrapped in a call (E5)
module ExtendSample using (F : OFUNCTIONALITY) : OFUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (xk : List Bool × ℤ) : (Option (List Bool)) {
    var x : List Bool, k : ℤ, y : Option (List Bool);
    x, k <- $xk;
    if (decide ($k ≤ size_out)) {
      y <- call F.f (($x, size_out));
      y <- Option.map (take $k) $y;
    } else {
      y <- call F.f (($x, $k));
    }
    return $y
  };
}

/-- `local equiv eq_extend : ExtendSample(FSome(BIRO.IRO)).f ~
ExtendOutputSize(FSetSize(FSome(BIRO.IRO))).f : ={arg} /\
eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2} ==> ={res} /\ …`. -/
theorem eq_extend (_hfresh : LocalFresh Log_m RFList_m) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧
        eq_extend_size (BIRO.IRO.mp.get g₁) (BIRO.IRO.mp.get g₂) (Log_m.get g₂))
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))).procedure
      (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app (ExtendOutputSize Log_m) (SecureORO.Oracle.mk (List Bool) f_out
          { get := Module.app FSetSize.get (Module.app FSome BIRO.IRO.asF) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        eq_extend_size (BIRO.IRO.mp.get g₁) (BIRO.IRO.mp.get g₂) (Log_m.get g₂)) := by
  sorry

theorem of_listK (l : f_out) : of_list (to_list l) = some l :=
  (Params.to_listK l (to_list l)).mp rfl

-- EC's local `Fill_In(F : RO)`; `proc init = F.init` is wrapped in a call (E5)
module Fill_In using (F : Eager.RO_T) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (xn : List Bool × ℤ) : (List Bool) {
    var x : List Bool, n : ℤ, l : List Bool, b : Bool, i : ℤ;
    x, n <- $xn;
    i <- 0;
    l <- [];
    while ($i < $n) {
      b <- call F.get (($x, $i));
      l <- rcons $l $b;
      i <- $i + 1;
    }
    while ($i < size_out) {
      _ <- call F.sample (($x, $i));
      i <- $i + 1;
    }
    return $l
  };
}

/-- `local equiv eq_eager_ideal : BIRO.IRO.f ~ Fill_In(LRO).f : ={arg} /\ BIRO.IRO.mp{1} = RO.m{2}
==> ={res} /\ BIRO.IRO.mp{1} = RO.m{2}`. -/
theorem eq_eager_ideal :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂)
      BIRO.IRO.f.procedure (Module.app Fill_In.f Eager.LRO).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂) := by
  sorry

/-- `local equiv eq_eager_ideal2 : ExtendSample(FSome(BIRO.IRO)).f ~ FSome(Fill_In(RO)).f :
={arg} /\ BIRO.IRO.mp{1} = RO.m{2} ==> ={res} /\ BIRO.IRO.mp{1} = RO.m{2}`. -/
theorem eq_eager_ideal2 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂)
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))).procedure
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app FSome (Module.app Fill_In Eager.RO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂) := by
  sorry

-- EC's local `Dist(F : RO)`, `proc distinguish = SHA3_OIndiff.OIndif.OIndif(FSome(Fill_In(F)),
-- OSimulator(FSome(Fill_In(F))), ODRestr(Dist_of_P2Adv(A))).main`, with the section's `A` a Lean
-- parameter; the alias is wrapped in a call (E5), and `distinguish` takes `RO_Distinguisher`'s
-- `unit` (`RO_LRO_D Dist`)
set_option linter.gaudisCrypt.using false in
module Dist (A : SH.AdvSecondPreimage) using (F : Eager.RO_T) {
  proc distinguish (_x : Unit) : Bool {
    var b : Bool;
    b <- call (Module.app OIndif.OIndif (Module.pair (Module.app FSome (Module.app Fill_In F))
      (Module.pair (Module.app OSimulator (OptionIndifferentiability.ODFUNCTIONALITY.mk state
          (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app FSome (Module.app Fill_In F)) }))
        (ODRestr (Dist_of_P2Adv Log_m Dist_of_P2Adv_m A))))) ();
    return $b
  };
}

-- EC's local `Game(F : RO)`, with the section's `A` a Lean parameter
set_option linter.gaudisCrypt.using false in
module Game (A : SH.AdvSecondPreimage) using (F : Eager.RO_T) {
  proc distinguish () : Bool {
    var bo : Bool;
    _ <- call (OptionIndifferentiability.OPRIMITIVE.init state (List Bool × ℤ) (List Bool)
      (Module.app OSimulator (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool × ℤ)
          (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app FSome (Module.app Fill_In F)) }))) ();
    SHA3_OIndiff.Counter.c <- 0;
    Log_m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    _ <- call F.init ();
    bo <- call (Module.app (Dist Log_m Dist_of_P2Adv_m A) F) (());
    return $bo
  };
}

/-- `DFSetSize(OFC(ExtendSample(FSome(BIRO.IRO)))).f`, a side of the sections' `toto`, `titi` (an
abbreviation). -/
noncomputable def DFSetSize_OFC_ExtendSample : procmod (List Bool) → (Option f_out) :=
  OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
    (Module.app DFSetSize (OptionIndifferentiability.OFUNCTIONALITY.view state (List Bool × ℤ)
      (List Bool) (Module.app OFC (OptionIndifferentiability.OFUNCTIONALITY.view state
        (List Bool × ℤ) (List Bool) (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))))))

/-- `local equiv toto : DFSetSize(OFC(ExtendSample(FSome(BIRO.IRO)))).f ~
DFSetSize(OFC(ExtendSample(FSome(BIRO.IRO)))).f : ={glob OFC, arg} /\
eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2} ==> ={glob OFC, res} /\ …`. -/
theorem toto (_hfresh : LocalFresh Log_m RFList_m) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ SHA3_OIndiff.Counter.c.get g₁ = SHA3_OIndiff.Counter.c.get g₂ ∧
        eq_extend_size (BIRO.IRO.mp.get g₁) (BIRO.IRO.mp.get g₂) (Log_m.get g₂))
      DFSetSize_OFC_ExtendSample.procedure DFSetSize_OFC_ExtendSample.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ SHA3_OIndiff.Counter.c.get g₁ = SHA3_OIndiff.Counter.c.get g₂ ∧
        eq_extend_size (BIRO.IRO.mp.get g₁) (BIRO.IRO.mp.get g₂) (Log_m.get g₂)) := by
  sorry

/-- `local equiv titi mess c : DFSetSize(OFC(ExtendSample(FSome(BIRO.IRO)))).f ~
SORO.Bounder(RFWhile).get : …`. -/
theorem titi (_hfresh : LocalFresh Log_m RFList_m) (mess : List Bool) (c : ℤ) :
    prhlProc (sig₁ := procsig (List Bool) -> (Option f_out))
      (sig₂ := procsig (List Bool) -> (Option f_out))
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ a₁ = mess ∧ SHA3_OIndiff.Counter.c.get g₁ = c ∧
        SORO.Bounder.bounder.get g₂ ≤ SHA3_OIndiff.Counter.c.get g₁ ∧
        inv (BIRO.IRO.mp.get g₁) (RFList_m.get g₂))
      DFSetSize_OFC_ExtendSample.procedure
      (SecureORO.RF_T.get (List Bool) f_out (Module.app SORO.Bounder (RFWhile RFList_m))).procedure
      (fun r₁ g₁ r₂ g₂ =>
        if SHA3_OIndiff.increase_counter c mess size_out ≤ sigma then
          (∃ y, r₁ = some y ∧ r₂ = some y ∧
            SORO.Bounder.bounder.get g₂ ≤ SHA3_OIndiff.Counter.c.get g₁ ∧
            SHA3_OIndiff.Counter.c.get g₁ = SHA3_OIndiff.increase_counter c mess size_out ∧
            inv (BIRO.IRO.mp.get g₁) (RFList_m.get g₂))
        else r₁ = none) := by
  sorry

/-- `local lemma eager_ideal &m`. -/
theorem eager_ideal (A : SH.AdvSecondPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ (SORO.RO.FRO.m).footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint ⊔ Dist_of_P2Adv_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_P2Adv Log_m Dist_of_P2Adv_m A))).procedure () m (fun r _ => r = true) =
      Procedure.Pr (IdealGame (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))
        (ODRestr (Dist_of_P2Adv Log_m Dist_of_P2Adv_m A))).procedure () m
            (fun r _ => r = true) := by
  sorry

/-- `local lemma rw_ideal_2 &m (mess : List Bool)`. -/
theorem rw_ideal_2 (A : SH.AdvSecondPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ (SORO.RO.FRO.m).footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint ⊔ Dist_of_P2Adv_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) (mess : List Bool) :
    Dist_of_P2Adv_m.get m = mess →
    (Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_P2Adv Log_m Dist_of_P2Adv_m A))).procedure () m (fun r _ => r = true) : ℝ) ≤
      Procedure.Pr (Module.app SORO.SecondPreimage (Module.pair (SORO_P2 Log_m Dist_of_P2Adv_m A)
        (RFList RFList_m))).procedure mess m (fun r _ => r = true) := by
  sorry

/-- `local lemma rw_ideal &m (mess : List Bool)`. -/
theorem rw_ideal (A : SH.AdvSecondPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ (SORO.RO.FRO.m).footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint ⊔ Dist_of_P2Adv_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) (mess : List Bool) :
    Dist_of_P2Adv_m.get m = mess →
    (Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_P2Adv Log_m Dist_of_P2Adv_m A))).procedure () m (fun r _ => r = true) : ℝ) ≤
      Procedure.Pr (Module.app SORO.SecondPreimage (Module.pair (SORO_P2 Log_m Dist_of_P2Adv_m A)
        (Module.app SORO.RF SORO.RO.RO))).procedure mess m (fun r _ => r = true) := by
  sorry

/-- `local lemma leq_ideal &m (mess : List Bool)`. -/
theorem leq_ideal (A : SH.AdvSecondPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ (SORO.RO.FRO.m).footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint ⊔ Dist_of_P2Adv_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) (mess : List Bool) :
    Dist_of_P2Adv_m.get m = mess →
    (Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_P2Adv Log_m Dist_of_P2Adv_m A))).procedure () m (fun r _ => r = true) : ℝ) ≤
      ((sigma + 1 : ℤ) : ℝ) / (2 : ℝ) ^ size_out := by
  sorry

/-- `local lemma rw_real &m (mess : List Bool)`. -/
theorem rw_real (A : SH.AdvSecondPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ (SORO.RO.FRO.m).footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint ⊔ Dist_of_P2Adv_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) (mess : List Bool) :
    Dist_of_P2Adv_m.get m = mess →
    Procedure.Pr (Module.app SH.SecondPreimage (Module.pair A (Module.pair OSponge
        (PSome Perm)))).procedure
        mess m (fun r _ => r = true) =
      Procedure.Pr (Module.app OIndif.OIndif (Module.pair
        (Module.app FSome (Module.app Sponge.Sponge (Module.app Poget
          (OptionIndifferentiability.OPRIMITIVE.view state (List Bool × ℤ) (List Bool)
              (PSome Perm)))))
        (Module.pair (PSome Perm) (ODRestr (Dist_of_P2Adv Log_m Dist_of_P2Adv_m A))))).procedure
            () m (fun r _ => r = true) := by
  sorry

-- EC's local `TOTO`, with the section's `A` a Lean parameter
set_option linter.gaudisCrypt.using false in
module TOTO (A : SH.AdvSecondPreimage) {
  proc main (m : List Bool) : Bool {
    var b : Bool;
    Dist_of_P2Adv_m <- $m;
    b <- call (Module.app SH.SecondPreimage (Module.pair A (Module.pair OSponge (PSome Perm))))
      ($m);
    return $b
  };
}

end SecondPreimage

/-- EC's `Sponge_second_preimage_resistant (A <: SH.AdvSecondPreimage {…}) &m (mess : List Bool)`.
-/
theorem Sponge_second_preimage_resistant (A : SH.AdvSecondPreimage)
    (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ (SORO.RO.FRO.m).footprint)ᶜ)
    (m : VariableAssignment) (mess : List Bool) :
    A_lossless A →
    (Procedure.Pr (Module.app SH.SecondPreimage (Module.pair A (Module.pair OSponge
        (PSome Perm)))).procedure
        mess m (fun r _ => r = true) : ℝ) ≤
      bound + ((sigma + 1 : ℤ) : ℝ) / (2 : ℝ) ^ size_out := by
  sorry

/-! ## The section `Collision`, with `declare module A <: SH.AdvCollision {…, -SORO.RO.FRO}` (its
local declarations in the namespace `Collision`) -/

namespace Collision

/-! The local modules' variables `Log.m`, `RFList.m` are the lens parameters `Log_m`,
`RFList_m` (exception E6). -/
-- one binder each: a `module` takes a whole binder group when it mentions one of its names
variable (Log_m : Lens (FMap (List Bool × ℤ) Bool) VariableAssignment)
variable (RFList_m : Lens (FMap (List Bool) f_out) VariableAssignment)

-- EC's local `FInit(F : OIndif.ODFUNCTIONALITY) : OIndif.OFUNCTIONALITY`; `proc f = F.f` is
-- wrapped in a call (exception E5)
module FInit using (F : SH.OIndif.ODFUNCTIONALITY) : SH.OIndif.OFUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (x : List Bool) : (Option f_out) {
    var y : Option f_out;
    y <- call F.f ($x);
    return $y
  };
}

-- EC's local `PInit(P : ODPRIMITIVE) : OPRIMITIVE`; its aliases are wrapped in a call (E5)
module PInit using (P : ODPRIMITIVE) : OPRIMITIVE {
  proc init () : Unit {
    return ()
  };
  proc f (x : state) : (Option state) {
    var y : Option state;
    y <- call P.f ($x);
    return $y
  };
  proc fi (x : state) : (Option state) {
    var y : Option state;
    y <- call P.fi ($x);
    return $y
  };
}

-- EC's local `OF(F : Oracle) : OIndif.ODFUNCTIONALITY`; `proc f = F.get` is wrapped in a call (E5)
module OF using (F : SORO.Oracle) : SH.OIndif.ODFUNCTIONALITY {
  proc f (x : List Bool) : (Option f_out) {
    var y : Option f_out;
    y <- call F.get ($x);
    return $y
  };
}

module ExtendOutputSize using (F : SORO.Oracle) : ODFUNCTIONALITY {
  proc f (xk : List Bool × ℤ) : (Option (List Bool)) {
    var x : List Bool, k : ℤ, o : Option f_out, l : Option (List Bool), suffix : List Bool,
      «prefix» : List Bool, i : ℤ, r : Bool;
    x, k <- $xk;
    l <- (none : Option (List Bool));
    «prefix» <- [];
    suffix <- [];
    o <- call F.get ($x);
    «prefix» <- take $k (to_list (oget $o));
    i <- size_out;
    while ($i < $k) {
      if (!(decide (FMap.dom ($Log_m : FMap (List Bool × ℤ) Bool) ($x, $i)))) {
        r <$ dbool;
        Log_m <- FMap.set $Log_m ($x, $i) $r;
      }
      suffix <- rcons $suffix (oget (FMap.get $Log_m ($x, $i)));
      i <- $i + 1;
    }
    l <- some ($«prefix» ++ $suffix);
    return $l
  };
}

/-- `local module OFC2 (F : Oracle) = OFC(ExtendOutputSize(F))`. -/
noncomputable def OFC2 : SORO.Oracle →ₘ OFUNCTIONALITY := Module.comp OFC (ExtendOutputSize Log_m)

-- EC's local `ExtendOutput(F : RF)`; `proc f = ExtendOutputSize(F).f` is wrapped in a call
-- (E5), and `proc get = f` is `ExtendOutput.get`
module ExtendOutput using (F : SORO.RF_T) {
  proc init () : Unit {
    Log_m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    _ <- call F.init ();
    return ()
  };
  proc f (xk : List Bool × ℤ) : (Option (List Bool)) {
    var y : Option (List Bool);
    y <- call (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
      (Module.app (ExtendOutputSize Log_m) (SecureORO.Oracle.mk (List Bool) f_out
        { get := SecureORO.RF_T.get (List Bool) f_out F }))) ($xk);
    return $y
  };
}

/-- `ExtendOutput`'s `proc get = f`: the same procedure as `ExtendOutput.f`. -/
noncomputable abbrev ExtendOutput.get := ExtendOutput.f

-- EC's local `(Dist_of_CollAdv (A : SH.AdvCollision) : ODISTINGUISHER)
-- (F : ODFUNCTIONALITY) (P : ODPRIMITIVE)`, with `A` a Lean parameter
open Classical in
set_option linter.gaudisCrypt.using false in
module Dist_of_CollAdv (A : SH.AdvCollision) using (F : ODFUNCTIONALITY, P : ODPRIMITIVE) {
  proc distinguish () : Bool {
    var hash1 : Option f_out, hash2 : Option f_out, m1 : List Bool, m2 : List Bool;
    Log_m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    m1, m2 <- call (Module.app A (Module.pair (OptionIndifferentiability.ODFUNCTIONALITY.mk state
        (List Bool) f_out
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
            (Module.app DFSetSize F) }) P)) ();
    hash1 <- call (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
        (Module.app DFSetSize F)) ($m1);
    hash2 <- call (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
        (Module.app DFSetSize F)) ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, $hash1 = some y ∧ $hash2 = some y)
  };
}

-- EC's local `(SORO_Coll (A : SH.AdvCollision) : SORO.AdvCollision)
-- (F : Oracle)`, with `A` a Lean parameter; `OFC2(F)` is written out as
-- `OFC(ExtendOutputSize(F))`
set_option maxHeartbeats 10000000 in
-- the `module` command's typing proof of this nest of oracles is slow (about 20 s)
set_option linter.gaudisCrypt.using false in
module SORO_Coll (A : SH.AdvCollision) using (F : SORO.Oracle) {
  proc guess () : (List Bool × List Bool) {
    var mi : List Bool × List Bool;
    Log_m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    SHA3_OIndiff.Counter.c <- 0;
    _ <- call (OptionIndifferentiability.OPRIMITIVE.init state (List Bool × ℤ) (List Bool)
      (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F))) ();
    mi <- call (Module.app A (Module.pair
      (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool) f_out
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
            (Module.app DFSetSize (OptionIndifferentiability.ODFUNCTIONALITY.mk state
                (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app OFC (Module.app (ExtendOutputSize Log_m) F)) })) })
      (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool) f_out
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OPC (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool × ℤ)
                (List Bool)
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F))
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F)) }))
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OPC (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool × ℤ)
                (List Bool)
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F))
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OSimulator (Module.app (ExtendOutputSize Log_m) F)) })) }))) ();
    return $mi
  };
}

module RFList : SORO.RF_T {
  proc init () : Unit {
    RFList_m <- (FMap.empty : FMap (List Bool) f_out);
    return ()
  };
  proc get (x : List Bool) : (Option f_out) {
    var z : List Bool;
    if (!(decide (FMap.dom ($RFList_m : FMap (List Bool) f_out) $x))) {
      z <$ dlist dbool size_out;
      RFList_m <- FMap.set $RFList_m $x (oget (of_list $z));
    }
    return FMap.get ($RFList_m : FMap (List Bool) f_out) $x
  };
  proc sample (_x : List Bool) : Unit {
    return ()
  };
}

module RFWhile : SORO.RF_T {
  proc init () : Unit {
    RFList_m <- (FMap.empty : FMap (List Bool) f_out);
    return ()
  };
  proc get (x : List Bool) : (Option f_out) {
    var l : List Bool, i : ℤ, b : Bool;
    if (!(decide (FMap.dom ($RFList_m : FMap (List Bool) f_out) $x))) {
      i <- 0;
      l <- [];
      while ($i < size_out) {
        b <$ dbool;
        l <- rcons $l $b;
        i <- $i + 1;
      }
      RFList_m <- FMap.set $RFList_m $x (oget (of_list $l));
    }
    return FMap.get ($RFList_m : FMap (List Bool) f_out) $x
  };
  proc sample (_x : List Bool) : Unit {
    return ()
  };
}

/-- `local equiv rw_RF_List_While : RFList.get ~ RFWhile.get : ={arg, glob RFList} ==>
={res, glob RFWhile}`. -/
theorem rw_RF_List_While :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ RFList_m.get g₁ = RFList_m.get g₂)
      (SecureORO.RF_T.get (List Bool) f_out (RFList RFList_m)).procedure
      (SecureORO.RF_T.get (List Bool) f_out (RFWhile RFList_m)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ RFList_m.get g₁ = RFList_m.get g₂) := by
  sorry

/-- `local equiv eq_IRO_RFWhile : BIRO.IRO.f ~ RFWhile.get : arg{1} = (x{2}, size_out) /\
inv BIRO.IRO.mp{1} RFList.m{2} ==> res{2} = of_list res{1} /\ size res{1} = size_out /\
inv BIRO.IRO.mp{1} RFList.m{2}`. -/
theorem eq_IRO_RFWhile (_hfresh : LocalFresh Log_m RFList_m) :
    prhlProc (sig₁ := procsig (List Bool × ℤ) -> (List Bool))
      (sig₂ := procsig (List Bool) -> (Option f_out))
      (fun a₁ g₁ a₂ g₂ => a₁ = (a₂, size_out) ∧ inv (BIRO.IRO.mp.get g₁) (RFList_m.get g₂))
      BIRO.IRO.f.procedure (SecureORO.RF_T.get (List Bool) f_out (RFWhile RFList_m)).procedure
      (fun r₁ g₁ r₂ g₂ => r₂ = of_list r₁ ∧ size r₁ = size_out ∧
        inv (BIRO.IRO.mp.get g₁) (RFList_m.get g₂)) := by
  sorry

-- EC's local `ExtendSample(F : OFUNCTIONALITY)`; `proc init = F.init` is wrapped in a call (E5)
module ExtendSample using (F : OFUNCTIONALITY) : OFUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (xk : List Bool × ℤ) : (Option (List Bool)) {
    var x : List Bool, k : ℤ, y : Option (List Bool);
    x, k <- $xk;
    if (decide ($k ≤ size_out)) {
      y <- call F.f (($x, size_out));
      y <- Option.map (take $k) $y;
    } else {
      y <- call F.f (($x, $k));
    }
    return $y
  };
}

/-- `local equiv eq_extend : ExtendSample(FSome(BIRO.IRO)).f ~
ExtendOutputSize(FSetSize(FSome(BIRO.IRO))).f : ={arg} /\
eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2} ==> ={res} /\ …`. -/
theorem eq_extend (_hfresh : LocalFresh Log_m RFList_m) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧
        eq_extend_size (BIRO.IRO.mp.get g₁) (BIRO.IRO.mp.get g₂) (Log_m.get g₂))
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))).procedure
      (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app (ExtendOutputSize Log_m) (SecureORO.Oracle.mk (List Bool) f_out
          { get := Module.app FSetSize.get (Module.app FSome BIRO.IRO.asF) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        eq_extend_size (BIRO.IRO.mp.get g₁) (BIRO.IRO.mp.get g₂) (Log_m.get g₂)) := by
  sorry

theorem of_listK (l : f_out) : of_list (to_list l) = some l :=
  (Params.to_listK l (to_list l)).mp rfl

-- EC's local `Fill_In(F : RO)`; `proc init = F.init` is wrapped in a call (E5)
module Fill_In using (F : Eager.RO_T) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (xn : List Bool × ℤ) : (List Bool) {
    var x : List Bool, n : ℤ, l : List Bool, b : Bool, i : ℤ;
    x, n <- $xn;
    i <- 0;
    l <- [];
    while ($i < $n) {
      b <- call F.get (($x, $i));
      l <- rcons $l $b;
      i <- $i + 1;
    }
    while ($i < size_out) {
      _ <- call F.sample (($x, $i));
      i <- $i + 1;
    }
    return $l
  };
}

/-- `local equiv eq_eager_ideal : BIRO.IRO.f ~ Fill_In(LRO).f : ={arg} /\ BIRO.IRO.mp{1} = RO.m{2}
==> ={res} /\ BIRO.IRO.mp{1} = RO.m{2}`. -/
theorem eq_eager_ideal :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂)
      BIRO.IRO.f.procedure (Module.app Fill_In.f Eager.LRO).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂) := by
  sorry

/-- `local equiv eq_eager_ideal2 : ExtendSample(FSome(BIRO.IRO)).f ~ FSome(Fill_In(RO)).f :
={arg} /\ BIRO.IRO.mp{1} = RO.m{2} ==> ={res} /\ BIRO.IRO.mp{1} = RO.m{2}`. -/
theorem eq_eager_ideal2 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂)
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))).procedure
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app FSome (Module.app Fill_In Eager.RO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂) := by
  sorry

-- EC's local `Dist(F : RO)`, `proc distinguish = SHA3_OIndiff.OIndif.OIndif(FSome(Fill_In(F)),
-- OSimulator(FSome(Fill_In(F))), ODRestr(Dist_of_CollAdv(A))).main`, with the section's `A` a Lean
-- parameter; the alias is wrapped in a call (E5), and `distinguish` takes `RO_Distinguisher`'s
-- `unit` (`RO_LRO_D Dist`)
set_option linter.gaudisCrypt.using false in
module Dist (A : SH.AdvCollision) using (F : Eager.RO_T) {
  proc distinguish (_x : Unit) : Bool {
    var b : Bool;
    b <- call (Module.app OIndif.OIndif (Module.pair (Module.app FSome (Module.app Fill_In F))
      (Module.pair (Module.app OSimulator (OptionIndifferentiability.ODFUNCTIONALITY.mk state
          (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app FSome (Module.app Fill_In F)) }))
        (ODRestr (Dist_of_CollAdv Log_m A))))) ();
    return $b
  };
}

-- EC's local `Game(F : RO)`, with the section's `A` a Lean parameter
set_option linter.gaudisCrypt.using false in
module Game (A : SH.AdvCollision) using (F : Eager.RO_T) {
  proc distinguish () : Bool {
    var bo : Bool;
    _ <- call (OptionIndifferentiability.OPRIMITIVE.init state (List Bool × ℤ) (List Bool)
      (Module.app OSimulator (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool × ℤ)
          (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app FSome (Module.app Fill_In F)) }))) ();
    SHA3_OIndiff.Counter.c <- 0;
    Log_m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    _ <- call F.init ();
    bo <- call (Module.app (Dist Log_m A) F) (());
    return $bo
  };
}

/-- `DFSetSize(OFC(ExtendSample(FSome(BIRO.IRO)))).f`, a side of the sections' `toto`, `titi` (an
abbreviation). -/
noncomputable def DFSetSize_OFC_ExtendSample : procmod (List Bool) → (Option f_out) :=
  OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
    (Module.app DFSetSize (OptionIndifferentiability.OFUNCTIONALITY.view state (List Bool × ℤ)
      (List Bool) (Module.app OFC (OptionIndifferentiability.OFUNCTIONALITY.view state
        (List Bool × ℤ) (List Bool) (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))))))

/-- `local equiv toto : DFSetSize(OFC(ExtendSample(FSome(BIRO.IRO)))).f ~
DFSetSize(OFC(ExtendSample(FSome(BIRO.IRO)))).f : ={glob OFC, arg} /\
eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2} ==> ={glob OFC, res} /\ …`. -/
theorem toto (_hfresh : LocalFresh Log_m RFList_m) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ SHA3_OIndiff.Counter.c.get g₁ = SHA3_OIndiff.Counter.c.get g₂ ∧
        eq_extend_size (BIRO.IRO.mp.get g₁) (BIRO.IRO.mp.get g₂) (Log_m.get g₂))
      DFSetSize_OFC_ExtendSample.procedure DFSetSize_OFC_ExtendSample.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ SHA3_OIndiff.Counter.c.get g₁ = SHA3_OIndiff.Counter.c.get g₂ ∧
        eq_extend_size (BIRO.IRO.mp.get g₁) (BIRO.IRO.mp.get g₂) (Log_m.get g₂)) := by
  sorry

/-- `local equiv titi mess c : DFSetSize(OFC(ExtendSample(FSome(BIRO.IRO)))).f ~
SORO.Bounder(RFWhile).get : …`. -/
theorem titi (_hfresh : LocalFresh Log_m RFList_m) (mess : List Bool) (c : ℤ) :
    prhlProc (sig₁ := procsig (List Bool) -> (Option f_out))
      (sig₂ := procsig (List Bool) -> (Option f_out))
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ a₁ = mess ∧ SHA3_OIndiff.Counter.c.get g₁ = c ∧
        SORO.Bounder.bounder.get g₂ ≤ SHA3_OIndiff.Counter.c.get g₁ ∧
        inv (BIRO.IRO.mp.get g₁) (RFList_m.get g₂))
      DFSetSize_OFC_ExtendSample.procedure
      (SecureORO.RF_T.get (List Bool) f_out (Module.app SORO.Bounder (RFWhile RFList_m))).procedure
      (fun r₁ g₁ r₂ g₂ =>
        if SHA3_OIndiff.increase_counter c mess size_out ≤ sigma then
          (∃ y, r₁ = some y ∧ r₂ = some y ∧
            SORO.Bounder.bounder.get g₂ ≤ SHA3_OIndiff.Counter.c.get g₁ ∧
            SHA3_OIndiff.Counter.c.get g₁ = SHA3_OIndiff.increase_counter c mess size_out ∧
            inv (BIRO.IRO.mp.get g₁) (RFList_m.get g₂))
        else r₁ = none) := by
  sorry

/-- `local lemma eager_ideal &m`. -/
theorem eager_ideal (A : SH.AdvCollision) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ (SORO.RO.FRO.m).footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_CollAdv Log_m A))).procedure () m (fun r _ => r = true) =
      Procedure.Pr (IdealGame (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))
        (ODRestr (Dist_of_CollAdv Log_m A))).procedure () m (fun r _ => r = true) := by
  sorry

/-- `local lemma rw_ideal_2 &m`. -/
theorem rw_ideal_2 (A : SH.AdvCollision) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ (SORO.RO.FRO.m).footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    (Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_CollAdv Log_m A))).procedure () m (fun r _ => r = true) : ℝ) ≤
      Procedure.Pr (Module.app SORO.Collision (Module.pair (SORO_Coll Log_m A)
        (RFList RFList_m))).procedure () m (fun r _ => r = true) := by
  sorry

/-- `local lemma rw_ideal &m`. -/
theorem rw_ideal (A : SH.AdvCollision) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ (SORO.RO.FRO.m).footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    (Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_CollAdv Log_m A))).procedure () m (fun r _ => r = true) : ℝ) ≤
      Procedure.Pr (Module.app SORO.Collision (Module.pair (SORO_Coll Log_m A)
        (Module.app SORO.RF SORO.RO.RO))).procedure () m (fun r _ => r = true) := by
  sorry

/-- `local lemma leq_ideal &m`. -/
theorem leq_ideal (A : SH.AdvCollision) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ (SORO.RO.FRO.m).footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    (Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_CollAdv Log_m A))).procedure () m (fun r _ => r = true) : ℝ) ≤
      ((sigma * (sigma - 1) + 2 : ℤ) : ℝ) / 2 / (2 : ℝ) ^ size_out := by
  sorry

/-- `local lemma rw_real &m`. -/
theorem rw_real (A : SH.AdvCollision) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ (SORO.RO.FRO.m).footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    Procedure.Pr (Module.app SH.Collision (Module.pair A (Module.pair OSponge
        (PSome Perm)))).procedure
        () m (fun r _ => r = true) =
      Procedure.Pr (Module.app OIndif.OIndif (Module.pair
        (Module.app FSome (Module.app Sponge.Sponge (Module.app Poget
          (OptionIndifferentiability.OPRIMITIVE.view state (List Bool × ℤ) (List Bool)
              (PSome Perm)))))
        (Module.pair (PSome Perm) (ODRestr (Dist_of_CollAdv Log_m A))))).procedure () m
            (fun r _ => r = true) := by
  sorry

end Collision

/-- EC's `Sponge_collision_resistant (A <: SH.AdvCollision {…}) &m`.
-/
theorem Sponge_collision_resistant (A : SH.AdvCollision)
    (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ (SORO.RO.FRO.m).footprint)ᶜ)
    (m : VariableAssignment) :
    A_lossless A →
    (Procedure.Pr (Module.app SH.Collision (Module.pair A (Module.pair OSponge
        (PSome Perm)))).procedure
        () m (fun r _ => r = true) : ℝ) ≤
      bound + ((sigma * (sigma - 1) + 2 : ℤ) : ℝ) / 2 / (2 : ℝ) ^ size_out := by
  sorry

end GaudisCrypt.SHA3.SHA3OSecurity
