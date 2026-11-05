import GaudisCrypt.Examples.SHA3.SHA3_OIndiff
import GaudisCrypt.Examples.SHA3.SecureORO
import GaudisCrypt.Examples.SHA3.SecureHash
import GaudisCrypt.Lib.EC.DList
import GaudisCrypt.Lib.EC.DListCall
import GaudisCrypt.Logic.FootprintUpper
import GaudisCrypt.Logic.PRHLFrame

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
-- the parameter classes are section variables of every declaration, used or not
set_option linter.unusedSectionVars false

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
theorem axioms : SecureORO.Axioms (List Bool) f_out dout sigma clone_increase_counter where
  bound_ge0 := Params.sigma_ge0
  sampleto_ll := Params.dout_ll
  sampleto_full := Params.dout_full
  sampleto_fu := Params.dout_fu
  increase_counter_spec c m := by
    have hr := gt0_r
    have h1 : 0 ≤ (size m + 1) / r :=
      Int.ediv_nonneg (by unfold size; omega) hr.le
    unfold clone_increase_counter
    have := le_max_right ((size_out + r - 1) / r - 1) 0
    omega
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
theorem axioms : SecureHash.Axioms (List Bool) f_out dout sigma clone_increase_counter where
  bound_ge0 := Params.sigma_ge0
  sampleto_ll := Params.dout_ll
  sampleto_full := Params.dout_full
  sampleto_fu := Params.dout_fu
  increase_counter_spec c m := by
    have hr := gt0_r
    have h1 : 0 ≤ (size m + 1) / r :=
      Int.ediv_nonneg (by unfold size; omega) hr.le
    unfold clone_increase_counter
    have := le_max_right ((size_out + r - 1) / r - 1) 0
    omega
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

/-- Every `ODISTINGUISHER` is representable over `F.f`, `P.f`, `P.fi`.  Not an EC lemma. -/
theorem ODistinguisher_representable (D : ODISTINGUISHER) :
    Module.Representable D OIndif.distExt := by
  refine Module.representable_of_firstOrder ?_ ?_ OIndif.distExt (fun _ => rfl) D
  · simp [IsModule.moduleTypeRep, ModuleTypeRep.FirstOrder, Module.moduleTypeRep,
      OptionIndifferentiability.ODFUNCTIONALITY.typeRep,
      OptionIndifferentiability.ODPRIMITIVE.typeRep]
  · intro sig n
    cases n with
    | zero => exact ⟨fun U hU => by simp at hU; subst hU; exact ⟨([], 0)⟩, ⟨none⟩⟩
    | succ n => cases n with
      | zero => exact ⟨fun U hU => by simp at hU; subst hU; infer_instance, inferInstance⟩
      | succ n => cases n with
        | zero => exact ⟨fun U hU => by simp at hU; subst hU; infer_instance, inferInstance⟩
        | succ n => nomatch n

/-- `FSome` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_FSome : FVP.fvP FSome ≤ ⊥ := by
  fp_module

/-- `Poget` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_Poget : FVP.fvP Poget ≤ ⊥ := by
  fp_module

/-- `PSome`'s `f` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_PSome_own_f : FVP.fvP PSome.own.f ≤ ⊥ := by
  fp_module

/-- `PSome`'s `fi` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_PSome_own_fi : FVP.fvP PSome.own.fi ≤ ⊥ := by
  fp_module

/-- `Sponge` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_Sponge : FVP.fvP Sponge.Sponge ≤ ⊥ := by
  fp_module

/-- `PSome(P).init` is `P.init`, at the clone's types. -/
theorem PSome_init' (P : PRIMITIVE) :
    OptionIndifferentiability.OPRIMITIVE.init state (List Bool) f_out (PSome P) =
      Indifferentiability.PRIMITIVE.init (block × capacity) (List Bool × ℤ) (List Bool) P :=
  PSome_init P

/-- `OSponge(P)` is `FSetSize(FSome(Sponge(Poget(P))))`. -/
theorem OSponge_app (P : ODPRIMITIVE) :
    Module.app OSponge P =
      Module.app FSetSize (Module.app FSome (Module.app Sponge.Sponge (Module.app Poget P))) := by
  unfold OSponge CSome
  erw [Module.app_comp, Module.app_comp, Module.app_comp]
  rfl

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

/-- `size (rcons s z) = size s + 1`. -/
theorem size_rcons' {α : Type} (s : List α) (z : α) : size (rcons s z) = size s + 1 := by
  simp only [size, rcons, List.length_append, List.length_singleton]
  push_cast
  rfl

/-- `take k (rcons s z) = take k s` when `k ≤ size s`. -/
theorem take_rcons_le {α : Type} (k : ℤ) (s : List α) (z : α) (h : k ≤ size s) :
    take k (rcons s z) = take k s := by
  unfold take rcons size at *
  exact List.take_append_of_le_length (by omega)

/-- `of_list` inverts `to_list` on lists of length `size_out` (`spec2_dout`, `to_listK`). -/
theorem to_list_oget_of_list (l : List Bool) (h : size l = size_out) :
    to_list (oget (of_list l)) = l := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (Params.spec2_dout l h)
  have := (Params.to_listK v l).mpr hv
  simp only [of_list, to_list, hv, oget, Option.getD_some]
  exact this

/-- The exit of `eq_IRO_RFWhile`'s fresh case: `inv` after the loop sampled `bs` for `x` into
`BIRO.IRO.mp` and `RFList.m` gets `x`.  Not an EC lemma (EC's `smt` after the `while`). -/
theorem inv_fresh (m mp0 : FMap (List Bool × ℤ) Bool) (m2 : FMap (List Bool) f_out)
    (x bs : List Bool) (h0 : inv mp0 m2) (hx : ¬ FMap.dom m2 x) (hsz : size bs = size_out)
    (h1 : ∀ l j, l ≠ x → FMap.get m (l, j) = FMap.get mp0 (l, j))
    (h2 : ∀ j, FMap.dom m (x, j) ↔ 0 ≤ j ∧ j < size_out)
    (h3 : ∀ j, 0 ≤ j → j < size_out → FMap.get m (x, j) = some (nth default bs j)) :
    inv m (FMap.set m2 x (oget (of_list bs))) := by
  have hdom : ∀ l j, l ≠ x → (FMap.dom m (l, j) ↔ FMap.dom mp0 (l, j)) := fun l j hl => by
    rw [FMap.domE, FMap.domE, h1 l j hl]
  refine ⟨fun l i h => ?_, fun l i h => ?_, fun l h i hi => ?_, fun l i h => ?_⟩
  · by_cases hl : l = x
    · subst hl
      exact (h2 i).mp h
    · exact h0.1 l i ((hdom l i hl).mp h)
  · by_cases hl : l = x
    · exact (FMap.mem_set _ _ _ _).mpr (Or.inr hl)
    · exact (FMap.mem_set _ _ _ _).mpr (Or.inl (h0.2.1 l i ((hdom l i hl).mp h)))
  · by_cases hl : l = x
    · subst hl
      exact (h2 i).mpr hi
    · have hl2 : FMap.dom m2 l := ((FMap.mem_set _ _ _ _).mp h).resolve_right hl
      exact (hdom l i hl).mpr (h0.2.2.1 l hl2 i hi)
  · by_cases hl : l = x
    · subst hl
      have hi := (h2 i).mp h
      rw [h3 i hi.1 hi.2, FMap.get_set_sameE]
      simp only [oget, Option.getD_some]
      rw [show Option.getD (of_list bs) default = oget (of_list bs) from rfl,
        to_list_oget_of_list bs hsz]
    · rw [FMap.get_set_neqE _ _ _ _ hl, h1 l i hl]
      exact h0.2.2.2 l i ((hdom l i hl).mp h)

/-- The section `Preimage`'s op `eq_extend_size`. -/
def eq_extend_size (m1 m2 m3 : FMap (List Bool × ℤ) Bool) : Prop :=
  (∀ x j, 0 ≤ j ∧ j < size_out → FMap.get m1 (x, j) = FMap.get m2 (x, j)) ∧
  (∀ x j, size_out ≤ j → FMap.get m1 (x, j) = FMap.get m3 (x, j)) ∧
  (∀ x j, FMap.dom m1 (x, j) → 0 ≤ j)

/-- The variables of `Gconcl`'s local `Gext` clone (an abbreviation). -/
noncomputable def Gext0Vars.footprint : Footprint VariableAssignment :=
  (ConcreteF.PF.m).footprint ⊔ (ConcreteF.PF.mi).footprint ⊔
    (Handle.G1.m).footprint ⊔
    (Handle.G1.mi).footprint ⊔ (Handle.G1.mh).footprint ⊔ (Handle.G1.mhi).footprint ⊔
    Handle.G1.chandle.footprint ⊔ (Handle.G1.paths).footprint ⊔ Handle.G1.bext.footprint ⊔
    Handle.G1.bcol.footprint ⊔ (Handle.FRO.m).footprint ⊔ (Handle.ROhandle.RO.m).footprint

/-- `Gext0Vars.footprint` is finitely supported. -/
theorem Gext0Vars_fs : Gext0Vars.footprint.FinitelySupported := by
  unfold Gext0Vars.footprint
  repeat' first
    | exact Footprint.FinitelySupported.globalVar _
    | apply Footprint.FinitelySupported.sup

/-- The adversary avoids the variables of `Gconcl`'s local `Gext` clone (exception E13, as
`SHA3_OIndiff.OGext0Fresh` for a distinguisher). -/
def AGext0Fresh {T : Type 1} [IsModule T] (A : T) : Prop :=
  FVP.fvP A ≤ Gext0Vars.footprintᶜ

/-- `ARestrictions.footprint` is finitely supported (a join of global variables). -/
theorem ARestrictions_fs : ARestrictions.footprint.FinitelySupported := by
  unfold ARestrictions.footprint SLCommon.C.footprint
  repeat' first
    | exact Footprint.FinitelySupported.globalVar _
    | apply Footprint.FinitelySupported.sup

set_option maxHeartbeats 4000000 in
-- `fp_module` through the simulator's code
/-- `OSimulator` touches the simulator's maps and `Gconcl_list.BIRO2.IRO.mp`.  Not an EC lemma. -/
theorem fvP_OSimulator : FVP.fvP OSimulator ≤ (Lens.pair SHA3Indiff.Simulator.m
    (Lens.pair SHA3Indiff.Simulator.mi (Lens.pair SHA3Indiff.Simulator.paths
      Gconcl_list.BIRO2.IRO.mp))).footprint := by
  fp_module (Lens.pair SHA3Indiff.Simulator.m (Lens.pair SHA3Indiff.Simulator.mi
    (Lens.pair SHA3Indiff.Simulator.paths Gconcl_list.BIRO2.IRO.mp)))

/-- `OSimulator` has finitely many variables. -/
theorem OSimulator_fs : (FVP.fvP OSimulator).FinitelySupported := by
  refine Footprint.FinitelySupported.mono fvP_OSimulator ?_
  simp only [Footprint.lens_pair]
  repeat' first
    | exact Footprint.FinitelySupported.globalVar _
    | apply Footprint.FinitelySupported.sup

/-- `SHA3OIndiff`'s restrictions are among `ARestrictions` and the `glob`s of `SimLast(Gconcl.S)` and
`OSimulator`.  Not an EC lemma. -/
theorem ODistRestrictions_cover : DistRestrictions.footprint ⊔ Counter.c.footprint ⊔
    (FVP.fvP OSimulator).glob ≤ ARestrictions.footprint ⊔
      (FVP.fvP (Gconcl_list.SimLast Gconcl.S)).glob ⊔ (FVP.fvP OSimulator).glob := by
  unfold DistRestrictions.footprint ARestrictions.footprint SLCommon.C.footprint
  fp_sub

/-- A disjointness `X ≤ Yᶜ` from `X ≤ Y₁ᶜ` and `X ≤ Y₂ᶜ`. -/
theorem le_compl_sup {X Y₁ Y₂ : Footprint VariableAssignment} (h₁ : X ≤ Y₁ᶜ) (h₂ : X ≤ Y₂ᶜ) :
    X ≤ (Y₁ ⊔ Y₂)ᶜ :=
  (Footprint.le_compl_comm _ _).mpr
    (sup_le ((Footprint.le_compl_comm _ _).mp h₁) ((Footprint.le_compl_comm _ _).mp h₂))

/-- An adversary under the sections' restrictions is outside `SHA3OIndiff`'s (`ODistRestrictions`
of a distinguisher built from it).  Not an EC lemma. -/
theorem A_ODistRestrictions {T : Type 1} [IsModule T] (A : T)
    (hAfs : (FVP.fvP A).FinitelySupported) (hAd : FVP.fvP A ≤ ARestrictions.footprintᶜ) :
    FVP.fvP A ≤ (DistRestrictions.footprint ⊔ Counter.c.footprint ⊔
      (FVP.fvP OSimulator).glob)ᶜ := by
  have hSL : (FVP.fvP (Gconcl_list.SimLast Gconcl.S)).FinitelySupported := SimLast_ECModule.2
  refine le_trans ?_ (Footprint.compl_antimono ODistRestrictions_cover)
  refine le_compl_sup (le_compl_sup hAd ?_) ?_
  · unfold ARestrictions.footprint at hAd
    exact Footprint.le_compl_glob_symm hSL (by fp_disjoint)
  · refine Footprint.le_compl_glob_symm OSimulator_fs (fvP_OSimulator.trans ?_)
    unfold ARestrictions.footprint at hAd
    simp only [Footprint.lens_pair]
    repeat' refine sup_le ?_ ?_
    all_goals exact Footprint.globalVar_le_compl_glob hAfs _ (by fp_disjoint)

/-- A variable outside `ARestrictions` and the `glob`s of `SimLast(Gconcl.S)` and `OSimulator` is
outside `SHA3OIndiff`'s restrictions.  Not an EC lemma. -/
theorem X_ODistRestrictions {X : Footprint VariableAssignment} (hXA : X ≤ ARestrictions.footprintᶜ)
    (hXg : X ≤ (FVP.fvP (Gconcl_list.SimLast Gconcl.S) ⊔ FVP.fvP OSimulator).globᶜ) :
    X ≤ (DistRestrictions.footprint ⊔ Counter.c.footprint ⊔ (FVP.fvP OSimulator).glob)ᶜ := by
  refine le_trans ?_ (Footprint.compl_antimono ODistRestrictions_cover)
  refine le_compl_sup (le_compl_sup hXA ?_) ?_
  · exact hXg.trans (Footprint.compl_antimono (Footprint.glob_mono le_sup_left))
  · exact hXg.trans (Footprint.compl_antimono (Footprint.glob_mono le_sup_right))

/-- The global variables of `SORO_P1`'s oracles: `Counter.c`, the simulator's maps,
`Gconcl_list.BIRO2.IRO.mp` (an abbreviation). -/
noncomputable abbrev soroG :
    Lens (ℤ × FMap SHA3Indiff.state SHA3Indiff.state × FMap SHA3Indiff.state SHA3Indiff.state ×
      FMap capacity (List block × block) × FMap (List block × ℤ) block) VariableAssignment :=
  Lens.pair Counter.c (Lens.pair SHA3Indiff.Simulator.m (Lens.pair SHA3Indiff.Simulator.mi
    (Lens.pair SHA3Indiff.Simulator.paths Gconcl_list.BIRO2.IRO.mp)))

/-- The sections' local variables are fresh (EasyCrypt's semantics of local modules; exception E6):
disjoint from each other and from the games' variables (an abbreviation). -/
def LocalFresh (Log_m : Lens (FMap (List Bool × ℤ) Bool) VariableAssignment)
    (RFList_m : Lens (FMap (List Bool) f_out) VariableAssignment) : Prop :=
  Log_m.footprint ⊔ RFList_m.footprint ≤ ARestrictions.footprintᶜ ∧
    Log_m.footprint ≤ RFList_m.footprintᶜ ∧ Log_m.footprint.FinitelySupported

/-! ### Ideal games over two functionalities related outside a lens

EasyCrypt's `call (: ={glob OFC, glob OSimulator} /\ …)` through `OIndif(F, OSimulator(F), D)`,
for two functionalities `F₁`, `F₂` whose states are related by a relation `I` of the contents of a
lens `L` (the states equal outside `L`): the simulator's code is the same on both sides but for
its call of `F.f`, and the distinguisher is an abstract module outside `L`. -/

section IdealCongr

variable {Ω : Type} (L : Lens Ω VariableAssignment) (I : Ω → Ω → Prop)

/-- `OSimulator(F₁).fi ~ OSimulator(F₂).fi` over the states equal outside `L`: the same code on
variables outside `L` (EC: `proc; inline*; sim`).  Not an EC lemma. -/
theorem osim_congr_fi [Lens.Disjoint SHA3Indiff.Simulator.m L]
    [Lens.Disjoint SHA3Indiff.Simulator.mi L] (F₁ F₂ : OFUNCTIONALITY) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))
      (OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
        (Module.app OSimulator (OptionIndifferentiability.OFUNCTIONALITY.view state
          (List Bool × ℤ) (List Bool) F₁))).procedure
      (OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
        (Module.app OSimulator (OptionIndifferentiability.OFUNCTIONALITY.view state
          (List Bool × ℤ) (List Bool) F₂))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂)) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ L.equal_outside §allGlobals{1} §allGlobals{2} ∧
      I (L.get §allGlobals{1}) (L.get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  equiv_if
  case guard =>
    rintro g₁ g₂ _ _ ⟨rfl, he, -⟩
    rw [he.get_disjoint]
  case «else» =>
    stmt_wp
    equiv_skip
    rintro g₁ g₂ _ _ ⟨⟨rfl, he, hI⟩, -⟩
    exact ⟨by rw [he.get_disjoint], he, hI⟩
  case «then» =>
    stmt_wp
    equiv_rnd
    equiv_rnd
    equiv_skip
    rintro g₁ g₂ _ _ ⟨⟨rfl, he, hI⟩, -⟩
    intro _ _ _ _
    rw [he.get_disjoint (X := SHA3Indiff.Simulator.m),
      he.get_disjoint (X := SHA3Indiff.Simulator.mi)]
    exact ⟨(he.set_disjoint _).set_disjoint _, hI⟩

/-- `OSimulator(F₁).f ~ OSimulator(F₂).f` over the states equal outside `L`, from
`F₁.f ~ F₂.f` (EC: `proc; sp; if; …; call (: …)`): the relation `I` of the contents of `L` before,
a weaker `J` after (the simulator calls `F.f` at most once).  Not an EC lemma. -/
theorem osim_congr_f [Lens.Disjoint SHA3Indiff.Simulator.m L]
    [Lens.Disjoint SHA3Indiff.Simulator.mi L] [Lens.Disjoint SHA3Indiff.Simulator.paths L]
    (J : Ω → Ω → Prop) (hIJ : ∀ v w, I v w → J v w)
    (hB : FVP.fvP Gconcl_list.BIRO2.IRO.f ≤ (L.footprint)ᶜ) (F₁ F₂ : ODFUNCTIONALITY)
    (hF : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))
      (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool × ℤ) (List Bool) F₁).procedure
      (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool × ℤ) (List Bool) F₂).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L.equal_outside g₁ g₂ ∧ J (L.get g₁) (L.get g₂))) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))
      (OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
        (Module.app OSimulator F₁)).procedure
      (OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
        (Module.app OSimulator F₂)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L.equal_outside g₁ g₂ ∧ J (L.get g₁) (L.get g₂)) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ L.equal_outside §allGlobals{1} §allGlobals{2} ∧
      I (L.get §allGlobals{1}) (L.get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  equiv_if
  case guard =>
    rintro g₁ g₂ _ _ ⟨rfl, he, -⟩
    rw [he.get_disjoint]
  case «else» =>
    stmt_wp
    equiv_skip
    rintro g₁ g₂ _ _ ⟨⟨rfl, he, hI⟩, -⟩
    exact ⟨by rw [he.get_disjoint], he, hIJ _ _ hI⟩
  case «then» =>
    equiv_seq 5 5 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧
        L.equal_outside §allGlobals{1} §allGlobals{2} ∧
        J (L.get §allGlobals{1}) (L.get §allGlobals{2}))
    · equiv_if
      case guard =>
        rintro g₁ g₂ _ _ ⟨⟨rfl, he, -⟩, -⟩
        rw [he.get_disjoint]
      case «then» =>
        stmt_wp
        equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧
            L.equal_outside §allGlobals{1} §allGlobals{2} ∧
            I (L.get §allGlobals{1}) (L.get §allGlobals{2}))
        · stmt_wp
          equiv_skip
          rintro g₁ g₂ _ _ ⟨⟨⟨rfl, he, hI⟩, -⟩, -⟩
          rw [he.get_disjoint]
          exact ⟨rfl, rfl, rfl, he, hI⟩
        equiv_if
        case guard =>
          rintro g₁ g₂ _ _ _ _ _ _ ⟨rfl, rfl, rfl, -, -⟩
          rfl
        case «then» =>
          stmt_wp
          equiv_call hF
          equiv_skip
          rintro g₁ g₂ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, he, hI⟩, -⟩
          exact ⟨⟨rfl, he, hI⟩, fun _ _ _ _ ⟨hr, he', hJ'⟩ => ⟨rfl, by rw [hr], he', hJ'⟩⟩
        case «else» =>
          equiv_call (prhlProc_self_equal_outside_module L _ hB I)
          equiv_skip
          rintro g₁ g₂ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, he, hI⟩, -⟩
          exact ⟨⟨rfl, he, hI⟩, fun _ _ _ _ ⟨rfl, he', hI'⟩ => ⟨rfl, rfl, he', hIJ _ _ hI'⟩⟩
      case «else» =>
        equiv_rnd
        equiv_skip
        rintro g₁ g₂ _ _ ⟨⟨⟨rfl, he, hI⟩, -⟩, -⟩
        exact fun _ _ => ⟨rfl, he, hIJ _ _ hI⟩
    equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §y2{1} = §y2{2} ∧
        L.equal_outside §allGlobals{1} §allGlobals{2} ∧
        J (L.get §allGlobals{1}) (L.get §allGlobals{2}))
    · stmt_wp
      equiv_rnd
      equiv_skip
      rintro g₁ g₂ _ _ _ _ ⟨rfl, rfl, he, hJ⟩
      intro _ _
      rw [he.get_disjoint (X := SHA3Indiff.Simulator.m),
        he.get_disjoint (X := SHA3Indiff.Simulator.mi)]
      exact ⟨rfl, rfl, (he.set_disjoint _).set_disjoint _, hJ⟩
    equiv_if
    case guard =>
      rintro g₁ g₂ _ _ _ _ _ _ ⟨rfl, -, -, he, -⟩
      rw [he.get_disjoint]
    case «then» =>
      stmt_wp
      equiv_skip
      rintro g₁ g₂ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, he, hJ⟩, -⟩
      rw [he.get_disjoint (X := SHA3Indiff.Simulator.paths)]
      exact ⟨rfl, he.set_disjoint _, hJ⟩
    case «else» =>
      equiv_skip
      rintro g₁ g₂ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, he, hJ⟩, -⟩
      exact ⟨rfl, he, hJ⟩

/-- EC's `byequiv` on `OIndif(F₁, OSimulator(F₁), D) ~ OIndif(F₂, OSimulator(F₂), D)` for a
distinguisher `D` outside `L`: the initializations (premise `hinit`) and one equal-outside abstract
call to `D`, its oracles `F.f` (premise `hf`) and the simulator's (`osim_congr_f`,
`osim_congr_fi`).  Not an EC lemma. -/
theorem ideal_game_congr [Lens.Disjoint SHA3Indiff.Simulator.m L]
    [Lens.Disjoint SHA3Indiff.Simulator.mi L] [Lens.Disjoint SHA3Indiff.Simulator.paths L]
    (hB : FVP.fvP Gconcl_list.BIRO2.IRO.f ≤ (L.footprint)ᶜ) (F₁ F₂ : OFUNCTIONALITY)
    (D : ODISTINGUISHER) (hD : Module.ECModule D OIndif.distExt) (hDL : FVP.fvP D ≤ (L.footprint)ᶜ)
    (hinit : prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (OptionIndifferentiability.OFUNCTIONALITY.init state (List Bool × ℤ) (List Bool) F₁).procedure
      (OptionIndifferentiability.OFUNCTIONALITY.init state (List Bool × ℤ) (List Bool) F₂).procedure
      (fun _ g₁ _ g₂ => L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂)))
    (hf : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool) F₁).procedure
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool) F₂).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂) (IdealGame F₁ D).procedure (IdealGame F₂ D).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  unfold IdealGame
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (L.equal_outside §allGlobals{1} §allGlobals{2} ∧
      I (L.get §allGlobals{1}) (L.get §allGlobals{2}))
  · equiv_call hinit
    stmt_wp
    equiv_skip
    intro σ₁ σ₂ h
    exact ⟨by rw [h], fun r₁ g₁ r₂ g₂ hpost => hpost⟩
  stmt_split{1} 1
  stmt_split{2} 1
  refine prhlStmt_seq_call (prhlProc_abstract_call_equal_outside_module
    L D OIndif.distExt hD.1 hDL I ?hc _ _ ?horacle) ?_
  case hc =>
    intro _ n
    cases n with
    | zero => exact inferInstanceAs (Countable (List Bool × ℤ))
    | succ n => cases n with
      | zero => exact inferInstanceAs (Countable (block × capacity))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable (block × capacity))
        | succ n => nomatch n
  case horacle =>
    intro _ n
    cases n with
    | zero =>
      simp only [OIndif.distExt, OptionIndifferentiability.distExt,
        HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
        OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
        OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
        OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
      exact hf
    | succ n => cases n with
      | zero =>
        simp only [OIndif.distExt, OptionIndifferentiability.distExt,
          HoleSigs.Instantiation.lookup_succ, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair, OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
          OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
          OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
        exact osim_congr_f L I I (fun _ _ h => h) hB _ _ (by
          simp only [OptionIndifferentiability.OFUNCTIONALITY.view,
            OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp]
          exact hf)
      | succ n => cases n with
        | zero =>
          simp only [OIndif.distExt, OptionIndifferentiability.distExt,
            HoleSigs.Instantiation.lookup_succ, HoleSigs.Instantiation.lookup_zero_single,
            Module.fst_pair, Module.snd_pair, OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
            OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
            OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
          exact osim_congr_fi L I F₁ F₂
        | succ n => nomatch n
  equiv_skip
  intro σ₁ σ₂ h
  refine ⟨⟨rfl, h⟩, fun r₁ g₁ r₂ g₂ ⟨hr, _⟩ => ?_⟩
  simp_reads
  exact hr

end IdealCongr

/-- The variables of `eager_ideal`'s invariant: `BIRO.IRO.mp` (left), `Eager.RO.m` (right) (an
abbreviation). -/
noncomputable abbrev eagerL :
    Lens (FMap (List Bool × ℤ) Bool × FMap (List Bool × ℤ) Bool) VariableAssignment :=
  Lens.pair BIRO.IRO.mp Eager.RO.m

/-- EC's `BIRO.IRO.mp{1} = RO.m{2}`, on the contents of `eagerL`. -/
def eagerI (v₁ v₂ : FMap (List Bool × ℤ) Bool × FMap (List Bool × ℤ) Bool) : Prop := v₁.1 = v₂.2

/-- The simulator's `Gconcl_list.BIRO2.IRO` lies outside `eagerL`. -/
theorem eagerL_BIRO2 : FVP.fvP Gconcl_list.BIRO2.IRO.f ≤ (eagerL.footprint)ᶜ := by
  simp only [eagerL, Footprint.lens_pair]
  fp_disjoint

/-- A write of `BIRO.IRO.mp` keeps a state equal to itself outside `eagerL`. -/
theorem eagerL_IRO (g : VariableAssignment) (v : FMap (List Bool × ℤ) Bool) :
    eagerL.equal_outside g (BIRO.IRO.mp.set v g) :=
  (Lens.equal_outside_set_self _ g v).pair_left

/-- A write of `Eager.RO.m` keeps a state equal to itself outside `eagerL`. -/
theorem eagerL_RO (g : VariableAssignment) (v : FMap (List Bool × ℤ) Bool) :
    eagerL.equal_outside g (Eager.RO.m.set v g) :=
  (Lens.equal_outside_set_self _ g v).pair_right


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

/-- `RFList.get` is the module of its procedure. -/
theorem RFList_get :
    SecureORO.RF_T.get (List Bool) f_out (RFList RFList_m) = RFList.get RFList_m := by
  unfold RFList SecureORO.RF_T.get
  erw [Module.snd'_pair_prod, Module.fst'_pair_proc]

/-- `RFList.init` is the module of its procedure. -/
theorem RFList_init :
    SecureORO.RF_T.init (List Bool) f_out (RFList RFList_m) = RFList.init RFList_m := by
  unfold RFList SecureORO.RF_T.init
  erw [Module.fst'_pair_proc]

/-- `RFWhile.get` is the module of its procedure. -/
theorem RFWhile_get :
    SecureORO.RF_T.get (List Bool) f_out (RFWhile RFList_m) = RFWhile.get RFList_m := by
  unfold RFWhile SecureORO.RF_T.get
  erw [Module.snd'_pair_prod, Module.fst'_pair_proc]

/-- `RFWhile.init` is the module of its procedure. -/
theorem RFWhile_init :
    SecureORO.RF_T.init (List Bool) f_out (RFWhile RFList_m) = RFWhile.init RFList_m := by
  unfold RFWhile SecureORO.RF_T.init
  erw [Module.fst'_pair_proc]

/-- `RFList.get` touches `RFList.m` only. -/
theorem fvP_RFList_get : FVP.fvP (RFList.get RFList_m) ≤ RFList_m.footprint := by
  fp_module RFList_m

/-- `RFWhile.get` touches `RFList.m` only. -/
theorem fvP_RFWhile_get : FVP.fvP (RFWhile.get RFList_m) ≤ RFList_m.footprint := by
  fp_module RFList_m

/-- `local equiv rw_RF_List_While : RFList.get ~ RFWhile.get : ={arg, glob RFList} ==>
={res, glob RFWhile}`. -/
theorem rw_RF_List_While :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ RFList_m.get g₁ = RFList_m.get g₂)
      (SecureORO.RF_T.get (List Bool) f_out (RFList RFList_m)).procedure
      (SecureORO.RF_T.get (List Bool) f_out (RFWhile RFList_m)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ RFList_m.get g₁ = RFList_m.get g₂) := by
  rw [RFList_get, RFWhile_get]
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §RFList_m{1} = §RFList_m{2})
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  equiv_if
  case guard =>
    rintro g₁ g₂ _ _ ⟨rfl, h⟩
    rw [h]
  case «else» =>
    equiv_skip
    rintro g₁ g₂ _ _ ⟨⟨rfl, h⟩, -⟩
    exact ⟨by rw [h], h⟩
  case «then» =>
    stmt_wp
    refine prhlStmt_dlist_left _ { get := fun _ => size_out } (fun _ => rfl) ?_
    stmt_inline{1} 0
    stmt_wp
    equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §RFList_m{1} = §RFList_m{2} ∧ §n{1} = size_out ∧
        §i{1} = §i{2} ∧ §l0{1} = §l{2})
    · stmt_wp
      equiv_skip
      exact fun _ _ h => h.1
    equiv_while (§x0{1} = §x0{2} ∧ §RFList_m{1} = §RFList_m{2} ∧ §n{1} = size_out ∧
        §i{1} = §i{2} ∧ §l0{1} = §l{2})
    case body =>
      stmt_wp
      equiv_rnd
      equiv_skip
      rintro _ _ _ _ _ _ _ _ _ ⟨⟨rfl, h, rfl, rfl, rfl⟩, -⟩ _ _
      exact ⟨rfl, h, rfl, rfl, rfl⟩
    case guard =>
      rintro _ _ _ _ _ _ _ _ _ ⟨rfl, -, rfl, rfl, -⟩
      rfl
    case exit =>
      rintro _ _ _ _ _ _ _ _ _ ⟨rfl, h, -, -, rfl⟩ -
      exact ⟨by rw [h], by rw [h]⟩
    case hpre =>
      equiv_skip
      intros
      assumption

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
  rw [RFWhile_get]
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{1} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §n{1} = size_out ∧ §i{1} = 0 ∧ §bs{1} = [] ∧
      inv §IRO.mp{1} §RFList_m{2})
  · stmt_wp
    equiv_skip
    intros
    simp_all
  equiv_if{1}
  case «else» =>
    refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
    obtain ⟨-, hg⟩ := h
    simp [BIRO.valid, valid_toplevel] at hg
  case «then» =>
    equiv_if{2}
    case «then» =>
      stmt_wp
      refine prhlStmt_fix_left (fun σ => BIRO.IRO.mp.get σ.globals) fun mp0 => ?_
      refine prhlStmt_fix_right (fun σ => RFList_m.get σ.globals) fun m2 => ?_
      equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §n{1} = size_out ∧ §i{1} = §i{2} ∧ §bs{1} = §l{2} ∧
          0 ≤ §i{1} ∧ §i{1} ≤ size_out ∧ size §bs{1} = §i{1} ∧ §RFList_m{2} = m2 ∧
          ¬ FMap.dom m2 §x0{1} ∧ inv mp0 m2 ∧
          (∀ y j, y ≠ §x0{1} → FMap.get §IRO.mp{1} (y, j) = FMap.get mp0 (y, j)) ∧
          (∀ j, FMap.dom §IRO.mp{1} (§x0{1}, j) ↔ 0 ≤ j ∧ j < §i{1}) ∧
          (∀ j, 0 ≤ j → j < §i{1} → FMap.get §IRO.mp{1} (§x0{1}, j) = some (nth default §bs{1} j)))
      · stmt_wp
        equiv_skip
        rintro x0 n i bs mp x0' rf ⟨⟨⟨⟨⟨rfl, rfl, rfl, rfl, hinv⟩, -⟩, hd⟩, rfl⟩, rfl⟩
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hd
        exact ⟨rfl, rfl, rfl, rfl, le_rfl, Params.size_out_gt0.le, rfl, rfl, hd, hinv,
          fun _ _ _ => rfl, fun j => ⟨fun h => absurd (hinv.2.1 _ _ h) hd, fun h => by omega⟩,
          fun j _ h => by omega⟩
      equiv_while (§x0{1} = §x0{2} ∧ §n{1} = size_out ∧ §i{1} = §i{2} ∧ §bs{1} = §l{2} ∧
          0 ≤ §i{1} ∧ §i{1} ≤ size_out ∧ size §bs{1} = §i{1} ∧ §RFList_m{2} = m2 ∧
          ¬ FMap.dom m2 §x0{1} ∧ inv mp0 m2 ∧
          (∀ y j, y ≠ §x0{1} → FMap.get §IRO.mp{1} (y, j) = FMap.get mp0 (y, j)) ∧
          (∀ j, FMap.dom §IRO.mp{1} (§x0{1}, j) ↔ 0 ≤ j ∧ j < §i{1}) ∧
          (∀ j, 0 ≤ j → j < §i{1} → FMap.get §IRO.mp{1} (§x0{1}, j) = some (nth default §bs{1} j)))
      case body =>
        stmt_wp
        equiv_seq 1 1 : ((§x0{1} = §x0{2} ∧ §n{1} = size_out ∧ §i{1} = §i{2} ∧ §bs{1} = §l{2} ∧
            0 ≤ §i{1} ∧ §i{1} ≤ size_out ∧ size §bs{1} = §i{1} ∧ §RFList_m{2} = m2 ∧
            ¬ FMap.dom m2 §x0{1} ∧ inv mp0 m2 ∧
            (∀ y j, y ≠ §x0{1} → FMap.get §IRO.mp{1} (y, j) = FMap.get mp0 (y, j)) ∧
            (∀ j, FMap.dom §IRO.mp{1} (§x0{1}, j) ↔ 0 ≤ j ∧ j < §i{1}) ∧
            (∀ j, 0 ≤ j → j < §i{1} →
              FMap.get §IRO.mp{1} (§x0{1}, j) = some (nth default §bs{1} j))) ∧
            §i{1} < §n{1} ∧
            §x1{1} = §x0{1} ∧ §n0{1} = §i{1})
        · stmt_wp
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ ⟨hJ, hg⟩
          simp only [decide_eq_true_eq] at hg
          exact ⟨hJ, hg⟩
        equiv_if{1}
        case «then» =>
          stmt_wp
          equiv_rnd
          equiv_skip
          rintro x0 n i bs mp x1 n0 x0' i' l rf
            ⟨⟨⟨hx, hn, hi, hbs, hi0, hile, hsz, hrf, hdx, hinv, h1, h2, h3⟩, hlt, hx1, hn0⟩, -⟩ a _
          subst hx hn hi hbs
          rw [hx1, hn0, FMap.get_set_sameE]
          simp only [show (oget (some a) : Bool) = a from rfl]
          have hsz' : size (rcons bs a) = size bs + 1 := by
            simp only [size, rcons, List.length_append, List.length_singleton]
            push_cast
            rfl
          refine ⟨trivial, trivial, trivial, trivial, by omega, by omega, by omega, hrf, hdx, hinv,
            fun y j hy => ?_, fun j => ?_, fun j hj0 hj => ?_⟩
          · rw [FMap.get_set_neqE _ _ _ _ (fun e => hy (Prod.mk.inj e).1)]
            exact h1 y j hy
          · rw [FMap.mem_set, h2]
            constructor
            · rintro (⟨h, h'⟩ | e)
              · omega
              · obtain ⟨-, rfl⟩ := Prod.mk.inj e
                omega
            · rintro ⟨h, h'⟩
              by_cases hji : j = i
              · exact Or.inr (by rw [hji])
              · exact Or.inl ⟨h, by omega⟩
          · rw [nth_rcons]
            by_cases hji : j = i
            · subst hji
              rw [FMap.get_set_sameE, if_neg (by omega), if_pos hsz.symm]
            · rw [FMap.get_set_neqE _ _ _ _ (fun e => hji (Prod.mk.inj e).2),
                h3 j hj0 (by omega), if_pos (by omega)]
        case «else» =>
          refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
          obtain ⟨⟨⟨-, -, -, -, -, -, -, -, -, -, -, h2, -⟩, -, hx1, hn0⟩, hg⟩ := h
          simp only [Bool.not_eq_false', decide_eq_true_eq] at hg
          rw [hx1, hn0, h2] at hg
          omega
      case guard =>
        rintro _ _ _ _ _ _ _ _ _ ⟨-, hn, hi, -⟩
        rw [hn, hi]
      case exit =>
        rintro x0 n i bs mp x0' i' l rf
          ⟨hx, hn, hi, hbs, hi0, hile, hsz, hrf, hdx, hinv, h1, h2, h3⟩ hg
        subst hx hn hi hbs hrf
        simp only [decide_eq_false_iff_not, not_lt] at hg
        have hiu : i = size_out := by omega
        have hsz2 : size bs = size_out := by omega
        refine ⟨?_, hsz2, inv_fresh mp mp0 _ x0 bs hinv hdx hsz2 h1
          (fun j => by rw [h2 j, hiu]) (fun j hj0 hj => h3 j hj0 (by omega))⟩
        rw [FMap.get_set_sameE]
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (Params.spec2_dout bs hsz2)
        simp only [of_list] at hv ⊢
        rw [hv]
        rfl
      case hpre =>
        equiv_skip
        intros
        assumption
    case «else» =>
      equiv_while{1} (§x0{1} = §x0{2} ∧ §n{1} = size_out ∧ 0 ≤ §i{1} ∧ §i{1} ≤ size_out ∧
          FMap.dom §RFList_m{2} §x0{1} ∧ inv §IRO.mp{1} §RFList_m{2} ∧
          §bs{1} = take §i{1} (to_list (oget (FMap.get §RFList_m{2} §x0{1}))))
        ((size_out - §i{1}).toNat)
      case lossless =>
        intro σ₁ σ _ _
        have h1 := (is_lossless_iff_expected _).mp dbool_ll
        simp [Stmt.ewp_seq, Stmt.ewp_assign, Stmt.ewp_ifThenElse, Stmt.ewp_sample, Stmt.ewp_skip,
          h1]
      case «variant» =>
        intro σ₂ k
        hoare_wp 3
        hoare_split 1
        refine hoare_seq (hoare_if_wp (At := fun _ => False) (fun _ h => h.elim)
          (hoare_skip_wp _)) ?_
        hoare_wp 2
        hoare_skip
        rintro x0 n i mp bs ⟨⟨hx, rfl, hi0, hile, hd, hinv, rfl⟩, hg, hk⟩
        simp only [decide_eq_true_eq] at hg
        have hdom : FMap.dom mp (x0, i) := hinv.2.2.1 _ hd i ⟨hi0, hg⟩
        refine ⟨fun h => ?_, fun _ => ⟨⟨hx, rfl, by omega, by omega, hd, hinv, ?_⟩, by omega⟩⟩
        · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h
          exact h hdom
        · have hL : size (to_list (oget (FMap.get (RFList_m.get σ₂.globals) x0))) = size_out :=
            Params.spec_dout _
          rw [hinv.2.2.2 _ _ hdom, take_nth default i _ ⟨hi0, by omega⟩]
          rfl
      case exit =>
        rintro x0 rf x0' n i mp bs ⟨rfl, rfl, hi0, hile, hd, hinv, rfl⟩ hg
        simp only [decide_eq_false_iff_not, not_lt] at hg
        have hiu : i = size_out := by omega
        have hL : size (to_list (oget (FMap.get rf x0'))) = size_out := Params.spec_dout _
        rw [hiu, ← hL, take_size]
        refine ⟨?_, rfl, hinv⟩
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd)
        rw [hv]
        exact ((Params.to_listK v (to_list v)).mp rfl).symm
      equiv_skip
      rintro _ _ _ _ _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, hinv⟩, -⟩, hd⟩
      simp only [Bool.not_eq_false', decide_eq_true_eq] at hd
      exact ⟨rfl, rfl, le_rfl, Params.size_out_gt0.le, hd, hinv, rfl⟩

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

/-- `eq_extend_size` survives a common update of the first two maps below `size_out`. -/
theorem eq_extend_size_set_lt {m1 m2 m3 : FMap (List Bool × ℤ) Bool} {x : List Bool} {j : ℤ}
    (b : Bool) (h : eq_extend_size m1 m2 m3) (hj0 : 0 ≤ j) (hj : j < size_out) :
    eq_extend_size (FMap.set m1 (x, j) b) (FMap.set m2 (x, j) b) m3 := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun x' j' hj' => ?_, fun x' j' hj' => ?_, fun x' j' hd => ?_⟩
  · rw [FMap.get_setE, FMap.get_setE, h1 x' j' hj']
  · have : (x', j') ≠ (x, j) := fun he => by
      obtain ⟨-, rfl⟩ := Prod.mk.inj he
      omega
    rw [FMap.get_set_neqE _ _ _ _ this, h2 x' j' hj']
  · rcases (FMap.mem_set _ _ _ _).mp hd with hd | he
    · exact h3 x' j' hd
    · obtain ⟨-, rfl⟩ := Prod.mk.inj he
      exact hj0

/-- `eq_extend_size` survives a common update of the first and the third map from `size_out`. -/
theorem eq_extend_size_set_ge {m1 m2 m3 : FMap (List Bool × ℤ) Bool} {x : List Bool} {j : ℤ}
    (b : Bool) (h : eq_extend_size m1 m2 m3) (hj : size_out ≤ j) :
    eq_extend_size (FMap.set m1 (x, j) b) m2 (FMap.set m3 (x, j) b) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hs : (0 : ℤ) < size_out := Params.size_out_gt0
  refine ⟨fun x' j' hj' => ?_, fun x' j' hj' => ?_, fun x' j' hd => ?_⟩
  · have : (x', j') ≠ (x, j) := fun he => by
      obtain ⟨-, rfl⟩ := Prod.mk.inj he
      omega
    rw [FMap.get_set_neqE _ _ _ _ this, h1 x' j' hj']
  · rw [FMap.get_setE, FMap.get_setE, h2 x' j' hj']
  · rcases (FMap.mem_set _ _ _ _).mp hd with hd | he
    · exact h3 x' j' hd
    · obtain ⟨-, rfl⟩ := Prod.mk.inj he
      omega

theorem eq_extend_size_dom_lt {m1 m2 m3 : FMap (List Bool × ℤ) Bool} {x : List Bool} {j : ℤ}
    (h : eq_extend_size m1 m2 m3) (hj0 : 0 ≤ j) (hj : j < size_out) :
    FMap.dom m1 (x, j) ↔ FMap.dom m2 (x, j) := by
  rw [FMap.domE, FMap.domE, h.1 x j ⟨hj0, hj⟩]

theorem eq_extend_size_dom_ge {m1 m2 m3 : FMap (List Bool × ℤ) Bool} {x : List Bool} {j : ℤ}
    (h : eq_extend_size m1 m2 m3) (hj : size_out ≤ j) :
    FMap.dom m1 (x, j) ↔ FMap.dom m3 (x, j) := by
  rw [FMap.domE, FMap.domE, h.2.1 x j hj]

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
  have hLA : Log_m.footprint ≤ ARestrictions.footprintᶜ := le_sup_left.trans _hfresh.1
  haveI : Lens.Disjoint BIRO.IRO.mp Log_m := Lens.disjoint_of_footprint_le_compl _ _
    ((Footprint.le_compl_comm _ _).mp (hLA.trans (Footprint.compl_antimono (by
      unfold ARestrictions.footprint; fp_sub))))
  haveI : Lens.Disjoint Log_m BIRO.IRO.mp := Lens.disjoint_of_footprint_le_compl _ _
    (hLA.trans (Footprint.compl_antimono (by unfold ARestrictions.footprint; fp_sub)))
  have hs : (0 : ℤ) < size_out := Params.size_out_gt0
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [FSetSize.get]
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 8 : (§x0{1} = §x0{2} ∧ §k{1} = §k{2} ∧ §x3{2} = §x0{2} ∧ §n{2} = size_out ∧
      §i0{2} = 0 ∧ §bs{2} = [] ∧ §suffix{2} = [] ∧
      eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log_m{2})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ _ ⟨rfl, h⟩
    exact ⟨rfl, rfl, h⟩
  equiv_if{1}
  case «then» =>
    stmt_wp
    equiv_rcondf{2}
    stmt_wp
    equiv_seq 1 1 : (§x2{1} = §x3{2} ∧ §n{1} = §n{2} ∧ §n{2} = size_out ∧ §i{1} = §i0{2} ∧
        §i{1} = 0 ∧ §bs{1} = §bs{2} ∧ §bs{1} = [] ∧ §k{1} = §k{2} ∧ §k{1} ≤ size_out ∧
        §suffix{2} = [] ∧ eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log_m{2})
    · stmt_wp
      equiv_skip
      rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h⟩, hk⟩
      simp only [decide_eq_true_eq] at hk
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hk, rfl, h⟩
    equiv_if
    case guard =>
      rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, -⟩
      rfl
    case «else» =>
      refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
      simp [BIRO.valid, valid_toplevel] at h
    case «then» =>
      equiv_while (§x2{1} = §x3{2} ∧ §n{1} = §n{2} ∧ §n{2} = size_out ∧ §i{1} = §i0{2} ∧
        0 ≤ §i{1} ∧ §i{1} ≤ size_out ∧ §bs{1} = §bs{2} ∧ size §bs{1} = §i{1} ∧ §k{1} = §k{2} ∧
        §k{1} ≤ size_out ∧ §suffix{2} = [] ∧ eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log_m{2})
      case body =>
        stmt_wp
        equiv_seq 1 1 : (§x2{1} = §x3{2} ∧ §n{1} = §n{2} ∧ §n{2} = size_out ∧ §i{1} = §i0{2} ∧
            0 ≤ §i{1} ∧ §i{1} ≤ size_out ∧ §bs{1} = §bs{2} ∧ size §bs{1} = §i{1} ∧
            §k{1} = §k{2} ∧ §k{1} ≤ size_out ∧ §suffix{2} = [] ∧
            eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log_m{2} ∧ §i{1} < §n{1} ∧
            §x3{1} = §x2{1} ∧ §n0{1} = §i{1} ∧ §x4{2} = §x3{2} ∧ §n0{2} = §i0{2})
        · stmt_wp
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _
            ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, hg⟩
          simp only [decide_eq_true_eq] at hg
          exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hg⟩
        equiv_if
        case guard =>
          rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            ⟨rfl, rfl, rfl, rfl, h0, hle, rfl, hsz, rfl, hk, rfl, hinv, hlt, rfl, rfl, rfl, rfl⟩
          simp only [eq_extend_size_dom_lt hinv h0 hlt]
        case «then» =>
          stmt_wp
          equiv_rnd
          equiv_skip
          rintro g₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            ⟨⟨rfl, rfl, rfl, rfl, h0, hle, rfl, hsz, rfl, hk, rfl, hinv, hlt, rfl, rfl, rfl, rfl⟩,
              -⟩ a _
          refine ⟨rfl, rfl, rfl, rfl, by omega, by omega, by simp only [FMap.get_set_sameE],
            by rw [size_rcons', hsz], rfl, hk, rfl, eq_extend_size_set_lt a hinv h0 (by omega)⟩
        case «else» =>
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            ⟨⟨rfl, rfl, rfl, rfl, h0, hle, rfl, hsz, rfl, hk, rfl, hinv, hlt, rfl, rfl, rfl, rfl⟩,
              -⟩
          refine ⟨rfl, rfl, rfl, rfl, by omega, by omega, ?_, by rw [size_rcons', hsz], rfl, hk,
            rfl, hinv⟩
          rw [hinv.1 _ _ ⟨h0, by omega⟩]
      case guard =>
        rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨-, rfl, -, rfl, -⟩
        rfl
      case exit =>
        rintro x2 n i bs k mp x3 n' i0 bs' k' suf mp' Log
          ⟨rfl, rfl, rfl, rfl, h0, hle, rfl, hsz, rfl, hk, rfl, hinv⟩ hg
        simp only [decide_eq_false_iff_not, not_lt] at hg
        have hsz' : size bs = size_out := by omega
        refine ⟨decide_eq_false (by omega), ?_, hinv⟩
        rw [if_pos (Option.some_ne_none bs), show oget (some bs) = bs from rfl,
          to_list_oget_of_list bs hsz', List.append_nil]
        rfl
      all_goals
        equiv_skip
        intros
        rename_i h
        obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, -⟩ := h
        have hs : (0 : ℤ) < size_out := Params.size_out_gt0
        refine ⟨h1, h2, h3, h4, by omega, by omega, h6, by rw [h7, h5]; rfl, h8, h9, h10, h11⟩
  case «else» =>
    stmt_wp
    equiv_seq 1 8 : (§x5{1} = §x0{2} ∧ §n1{1} = §k{2} ∧ size_out < §k{2} ∧ §i0{1} = 0 ∧
        §bs0{1} = [] ∧ §x3{2} = §x0{2} ∧ §n{2} = size_out ∧ §i0{2} = 0 ∧ §bs{2} = [] ∧
        §suffix{2} = [] ∧ eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log_m{2})
    · stmt_wp
      equiv_skip
      rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, hk⟩
      simp only [decide_eq_false_iff_not, not_le] at hk
      exact ⟨h1, h2, h2 ▸ hk, h3, h4, h5, h6, h7, h8⟩
    equiv_if{1}
    case «else» =>
      refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
      simp [BIRO.valid, valid_toplevel] at h
    case «then» =>
      refine prhlStmt_splitwhile_left
        ⟨fun σ => decide ((localVarLens "i0" ℤ).get σ < size_out)⟩
        (fun σ => ((localVarLens "n1" ℤ).get σ - (localVarLens "i0" ℤ).get σ).toNat) ?_ ?_
      · intro k'
        simp only [Getter.andB_get, Bool.and_eq_true]
        hoare_wp 3
        hoare_split 1
        refine hoare_seq (hoare_if_wp (At := fun σ =>
          ((localVarLens "n1" ℤ).get σ - ((localVarLens "i0" ℤ).get σ + 1)).toNat < k') ?_
          (hoare_skip_wp _)) ?_
        · hoare_wp 2
          hoare_skip
          intro _ _ h _ _
          exact h
        · hoare_wp 2
          hoare_skip
          rintro i0 n1 mp x5 ⟨⟨h1, -⟩, hk⟩
          simp only [decide_eq_true_eq] at h1
          exact ⟨fun _ => by omega, fun _ => by omega⟩
      equiv_seq 1 1 : (§i0{1} = §i{2} ∧ §n1{1} = §k{2} ∧ §x5{1} = §x0{2} ∧
          §bs0{1} = §«prefix»{2} ++ §suffix{2} ∧ size_out ≤ §i{2} ∧ §i{2} ≤ §k{2} ∧
          eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log_m{2})
      · stmt_wp
        equiv_if{2}
        case «else» =>
          refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
          simp [BIRO.valid, valid_toplevel] at h
        case «then» =>
          simp only [Getter.andB]
          equiv_while (§x5{1} = §x0{2} ∧ §x3{2} = §x0{2} ∧ §n1{1} = §k{2} ∧ size_out < §k{2} ∧
            §n{2} = size_out ∧ §i0{1} = §i0{2} ∧ 0 ≤ §i0{1} ∧ §i0{1} ≤ size_out ∧
            §bs0{1} = §bs{2} ∧ size §bs0{1} = §i0{1} ∧ §suffix{2} = [] ∧
            eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log_m{2})
          case body =>
            stmt_wp
            equiv_seq 1 1 : (§x5{1} = §x0{2} ∧ §x3{2} = §x0{2} ∧ §n1{1} = §k{2} ∧
                size_out < §k{2} ∧ §n{2} = size_out ∧ §i0{1} = §i0{2} ∧ 0 ≤ §i0{1} ∧
                §i0{1} ≤ size_out ∧ §bs0{1} = §bs{2} ∧ size §bs0{1} = §i0{1} ∧ §suffix{2} = [] ∧
                eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log_m{2} ∧ §i0{1} < size_out ∧
                §x6{1} = §x5{1} ∧ §n2{1} = §i0{1} ∧ §x4{2} = §x3{2} ∧ §n0{2} = §i0{2})
            · stmt_wp
              equiv_skip
              intros
              rename_i h
              obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, hg⟩ := h
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
              exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hg.2⟩
            equiv_if
            case guard =>
              intros
              rename_i h
              obtain ⟨rfl, rfl, rfl, hk, rfl, rfl, h0, hle, rfl, hsz, rfl, hinv, hlt, rfl, rfl, rfl,
                rfl⟩ := h
              simp only [eq_extend_size_dom_lt hinv h0 hlt]
            case «then» =>
              stmt_wp
              equiv_rnd
              equiv_skip
              intros
              rename_i h a _
              obtain ⟨⟨rfl, rfl, rfl, hk, rfl, rfl, h0, hle, rfl, hsz, rfl, hinv, hlt, rfl, rfl,
                rfl, rfl⟩, -⟩ := h
              refine ⟨rfl, rfl, rfl, hk, rfl, rfl, by omega, by omega,
                by simp only [FMap.get_set_sameE], by rw [size_rcons', hsz], rfl,
                eq_extend_size_set_lt a hinv h0 hlt⟩
            case «else» =>
              equiv_skip
              intros
              rename_i h
              obtain ⟨⟨rfl, rfl, rfl, hk, rfl, rfl, h0, hle, rfl, hsz, rfl, hinv, hlt, rfl, rfl,
                rfl, rfl⟩, -⟩ := h
              refine ⟨rfl, rfl, rfl, hk, rfl, rfl, by omega, by omega, ?_, by rw [size_rcons', hsz],
                rfl, hinv⟩
              rw [hinv.1 _ _ ⟨h0, hlt⟩]
          case guard =>
            intros
            rename_i h
            obtain ⟨-, -, rfl, hk, rfl, rfl, -⟩ := h
            rw [Bool.eq_iff_iff]
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            constructor <;> intro h <;> omega
          case exit =>
            intros
            rename_i h hg
            obtain ⟨rfl, rfl, rfl, hk, rfl, rfl, h0, hle, rfl, hsz, rfl, hinv⟩ := h
            simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hg
            refine ⟨by omega, rfl, rfl, ?_, le_rfl, by omega, hinv⟩
            rw [if_pos (Option.some_ne_none _), show ∀ l : List Bool, oget (some l) = l from
              fun _ => rfl, to_list_oget_of_list, List.append_nil]
            · unfold take size at *
              exact (List.take_of_length_le (by omega)).symm
            · omega
          all_goals
            equiv_skip
            intros
            rename_i h
            obtain ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, -⟩, -⟩ := h
            refine ⟨h1, h6, h2, h3, h7, by rw [h4, h8], by omega, by omega, by rw [h5, h9],
              by rw [h5, h4]; rfl, h10, h11⟩
      equiv_while (§i0{1} = §i{2} ∧ §n1{1} = §k{2} ∧ §x5{1} = §x0{2} ∧
          §bs0{1} = §«prefix»{2} ++ §suffix{2} ∧ size_out ≤ §i{2} ∧ §i{2} ≤ §k{2} ∧
          eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log_m{2})
      case body =>
        stmt_wp
        equiv_seq 1 1 : (§i0{1} = §i{2} ∧ §n1{1} = §k{2} ∧ §x5{1} = §x0{2} ∧
            §bs0{1} = §«prefix»{2} ++ §suffix{2} ∧ size_out ≤ §i{2} ∧ §i{2} ≤ §k{2} ∧
            eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log_m{2} ∧ §i0{1} < §n1{1} ∧
            §x6{1} = §x5{1} ∧ §n2{1} = §i0{1})
        · stmt_wp
          equiv_skip
          intros
          rename_i h
          obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hg⟩ := h
          simp only [decide_eq_true_eq] at hg
          exact ⟨h1, h2, h3, h4, h5, h6, h7, hg⟩
        equiv_if
        case guard =>
          intros
          rename_i h
          obtain ⟨rfl, rfl, rfl, -, hle, -, hinv, -, rfl, rfl⟩ := h
          simp only [eq_extend_size_dom_ge hinv hle]
        case «then» =>
          stmt_wp
          equiv_rnd
          equiv_skip
          intros
          rename_i h a _
          obtain ⟨⟨rfl, rfl, rfl, rfl, hle, hik, hinv, hlt, rfl, rfl⟩, -⟩ := h
          refine ⟨rfl, rfl, rfl, ?_, by omega, by omega, eq_extend_size_set_ge a hinv hle⟩
          simp only [FMap.get_set_sameE, rcons, List.append_assoc]
        case «else» =>
          equiv_skip
          intros
          rename_i h
          obtain ⟨⟨rfl, rfl, rfl, rfl, hle, hik, hinv, hlt, rfl, rfl⟩, -⟩ := h
          refine ⟨rfl, rfl, rfl, ?_, by omega, by omega, hinv⟩
          rw [hinv.2.1 _ _ hle]
          simp only [rcons, List.append_assoc]
      case guard =>
        intros
        rename_i h
        obtain ⟨rfl, rfl, -⟩ := h
        rfl
      case exit =>
        intros
        rename_i h _
        obtain ⟨-, -, -, rfl, -, -, hinv⟩ := h
        exact ⟨rfl, hinv⟩
      all_goals
        equiv_skip
        intros
        rename_i h
        exact h

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
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [PROM.FullRO.LRO, PROM.FullRO.RO_T.get.mk_simp, PROM.FullRO.RO_T.sample.mk_simp]
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_while{2} (§bs{1} = §l{2} ∧ §IRO.mp{1} = §Eager.RO.m{2}) ((size_out - §i{2}).toNat)
  case lossless =>
    intro σ₁ σ _ _
    simp [Stmt.ewp_seq, Stmt.ewp_assign]
  case «variant» =>
    intro σ₁ k
    hoare_wp 3
    hoare_skip
    rintro _ _ _ ⟨h, hg, hk⟩
    simp only [decide_eq_true_eq] at hg
    exact ⟨h, by omega⟩
  case exit =>
    rintro _ _ _ _ _ h _
    exact h
  equiv_seq 1 1 : (§x{1} = §x{2} ∧ §n{1} = §n{2} ∧ §i{1} = §i{2} ∧ §bs{1} = §l{2} ∧
      §IRO.mp{1} = §Eager.RO.m{2})
  · stmt_wp
    equiv_skip
    intros
    simp_all
  equiv_if{1}
  case «else» =>
    refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
    obtain ⟨-, hg⟩ := h
    simp [BIRO.valid, valid_toplevel] at hg
  case «then» =>
    equiv_while (§x{1} = §x{2} ∧ §n{1} = §n{2} ∧ §i{1} = §i{2} ∧ §bs{1} = §l{2} ∧
      §IRO.mp{1} = §Eager.RO.m{2})
    case body =>
      stmt_wp
      equiv_seq 1 1 : (§x{1} = §x{2} ∧ §n{1} = §n{2} ∧ §i{1} = §i{2} ∧ §bs{1} = §l{2} ∧
      §IRO.mp{1} = §Eager.RO.m{2} ∧ §i{1} < §n{1} ∧
          §(localVarLens "x0" (List Bool)){1} = §x{1} ∧ §n0{1} = §i{1} ∧
          §(localVarLens "x0" (List Bool × ℤ)){2} = (§x{2}, §i{2}))
      · stmt_wp
        equiv_skip
        rintro _ _ _ _ _ _ _ _ _ _ ⟨⟨hx, hn, hi, hb, hm⟩, hg⟩
        simp only [decide_eq_true_eq] at hg
        exact ⟨hx, hn, hi, hb, hm, hg⟩
      equiv_if{1}
      case «then» =>
        stmt_wp
        equiv_rnd
        equiv_skip
        rintro x n i bs mp x0 n0 x' n' i' l m x0'
          ⟨⟨rfl, rfl, rfl, rfl, rfl, hlt, rfl, rfl, rfl⟩, hd⟩ a _
        simp [hd]
      case «else» =>
        stmt_split{2} 1
        refine prhlStmt_seq_sample_right ?_
        equiv_skip
        rintro σ₂ x n i bs mp x0 n0 ⟨⟨hx, hn, hi, hb, hm, hlt, rfl, rfl, hx0⟩, hd⟩
        refine ⟨(is_lossless_iff_expected _).mp dbool_ll, fun a _ => ?_⟩
        simp_reads
        rw [hx0, ← hm]
        simp only [Bool.not_eq_false', decide_eq_true_eq] at hd
        rw [hx, hi] at hd
        simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        subst hx hi hb hn
        exact ⟨rfl, rfl, rfl, rfl, trivial⟩
    case guard =>
      rintro _ _ _ _ _ _ _ _ _ _ ⟨-, hn, hi, -⟩
      rw [hn, hi]
    case exit =>
      rintro _ _ _ _ _ _ _ _ _ _ ⟨-, -, -, hb, hm⟩ _
      exact ⟨hb, hm⟩
    all_goals
      equiv_skip
      intros
      simp_all

/-- `local equiv eq_eager_ideal2 : ExtendSample(FSome(BIRO.IRO)).f ~ FSome(Fill_In(RO)).f :
={arg} /\ BIRO.IRO.mp{1} = RO.m{2} ==> ={res} /\ BIRO.IRO.mp{1} = RO.m{2}`. -/
theorem eq_eager_ideal2 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂)
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))).procedure
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app FSome (Module.app Fill_In Eager.RO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{2} 0
  simp only [PROM.FullRO.RO.asRO, PROM.FullRO.RO_T.get.mk_simp, PROM.FullRO.RO_T.sample.mk_simp]
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 2 : (§(localVarLens "x0" (List Bool)){1} = §(localVarLens "x1" (List Bool)){2} ∧
      §k{1} = §n{2} ∧ §i{2} = 0 ∧ §l{2} = [] ∧ §IRO.mp{1} = §Eager.RO.m{2})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  equiv_if{1}
  case «then» =>
    stmt_wp
    equiv_seq 1 2 : (§(localVarLens "x2" (List Bool)){1} = §(localVarLens "x1" (List Bool)){2} ∧
        §n{1} = size_out ∧ §k{1} = §n{2} ∧ §k{1} ≤ size_out ∧ §i{1} = 0 ∧ §i{2} = 0 ∧
        §bs{1} = [] ∧ §l{2} = [] ∧ §IRO.mp{1} = §Eager.RO.m{2})
    · stmt_wp
      equiv_skip
      rintro _ _ _ _ _ _ _ _ ⟨⟨hx, hk, hi, hl, hm⟩, hg⟩
      simp only [decide_eq_true_eq] at hg
      exact ⟨hx, hk, hg, hi, hl, hm⟩
    equiv_if{1}
    case «else» =>
      refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
      obtain ⟨-, hg⟩ := h
      simp [BIRO.valid, valid_toplevel] at hg
    case «then» =>
      refine prhlStmt_splitwhile_left
        ⟨fun σ => decide ((localVarLens "i" ℤ).get σ < (localVarLens "k" ℤ).get σ)⟩
        (fun σ => ((localVarLens "n" ℤ).get σ - (localVarLens "i" ℤ).get σ).toNat) ?_ ?_
      · intro k'
        simp only [Getter.andB_get, Bool.and_eq_true]
        hoare_wp 3
        hoare_split 1
        refine hoare_seq (hoare_if_wp (At := fun σ =>
          ((localVarLens "n" ℤ).get σ - ((localVarLens "i" ℤ).get σ + 1)).toNat < k') ?_
          (hoare_skip_wp _)) ?_
        · hoare_wp 2
          hoare_skip
          intro _ _ h _ _
          exact h
        · hoare_wp 2
          hoare_skip
          rintro i n k mp x2 ⟨⟨h1, -⟩, hk⟩
          simp only [decide_eq_true_eq] at h1
          exact ⟨fun _ => by omega, fun _ => by omega⟩
      equiv_seq 1 1 : (§(localVarLens "x2" (List Bool)){1} = §(localVarLens "x1" (List Bool)){2} ∧
          §n{1} = size_out ∧ §i{1} = §i{2} ∧ take §k{1} §bs{1} = §l{2} ∧
          §IRO.mp{1} = §Eager.RO.m{2} ∧ §k{1} ≤ §i{1} ∧ size §bs{1} = §i{1})
      · simp only [Getter.andB]
        equiv_while (§(localVarLens "x2" (List Bool)){1} = §(localVarLens "x1" (List Bool)){2} ∧
          §n{1} = size_out ∧ §k{1} = §n{2} ∧ §k{1} ≤ size_out ∧ §i{1} = §i{2} ∧ §bs{1} = §l{2} ∧
          §IRO.mp{1} = §Eager.RO.m{2} ∧ 0 ≤ §i{1} ∧ §i{1} ≤ max 0 §k{1} ∧ size §bs{1} = §i{1})
        case body =>
          simp only [Bool.and_eq_true]
          stmt_wp
          equiv_seq 1 1 : (§(localVarLens "x2" (List Bool)){1} =
              §(localVarLens "x1" (List Bool)){2} ∧
              §n{1} = size_out ∧ §k{1} = §n{2} ∧ §k{1} ≤ size_out ∧ §i{1} = §i{2} ∧
              §bs{1} = §l{2} ∧ §IRO.mp{1} = §Eager.RO.m{2} ∧ 0 ≤ §i{1} ∧ §i{1} ≤ max 0 §k{1} ∧
              size §bs{1} = §i{1} ∧ §i{1} < §k{1} ∧ §x3{1} = §(localVarLens "x2" (List Bool)){1} ∧
              §n0{1} = §i{1} ∧ §(localVarLens "x2" (List Bool × ℤ)){2} = (§x1{2}, §i{2}))
          · stmt_wp
            equiv_skip
            rintro _ _ _ _ _ _ _ _ _ _ _ ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, -, hk⟩
            simp only [decide_eq_true_eq] at hk
            exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hk⟩
          equiv_if{1}
          case «then» =>
            stmt_wp
            equiv_rnd
            equiv_skip
            rintro x2 n k i bs mp x3 n0 x1' n' i' l m x2'
              ⟨⟨rfl, rfl, rfl, hkle, rfl, rfl, rfl, hi0, himax, hsz, hlt, rfl, rfl, rfl⟩, hd⟩ a _
            simp only [hd, ↓reduceIte, FMap.get_set_sameE, size_rcons']
            exact ⟨trivial, trivial, trivial, hkle, trivial, trivial, trivial, by omega, by omega,
              by omega⟩
          case «else» =>
            stmt_split{2} 1
            refine prhlStmt_seq_sample_right ?_
            equiv_skip
            rintro σ₂ x2 n k i bs mp x3 n0
              ⟨⟨hx, hn, hk, hkle, hi, hb, hm, hi0, himax, hsz, hlt, rfl, rfl, hx0⟩, hd⟩
            refine ⟨(is_lossless_iff_expected _).mp dbool_ll, fun a _ => ?_⟩
            simp_reads
            rw [hx0, ← hm]
            simp only [Bool.not_eq_false', decide_eq_true_eq] at hd
            rw [hx, hi] at hd
            simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              size_rcons']
            subst hx hi hb hk hn
            exact ⟨rfl, rfl, rfl, hkle, rfl, rfl, trivial, by omega, by omega, by omega⟩
        case guard =>
          rintro _ _ k i _ _ _ _ _ _ _ ⟨-, rfl, rfl, hkle, rfl, -⟩
          rcases lt_or_ge i k with h' | h'
          · rw [decide_eq_true h', decide_eq_true (show i < size_out by omega)]
            rfl
          · rw [decide_eq_false (not_lt.mpr h'), Bool.and_false]
        case exit =>
          rintro _ _ k i bs _ _ _ _ _ _ ⟨hx, hn, hk, hkle, hi, hb, hm, hi0, himax, hsz⟩ hg
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hg
          have hki : k ≤ i := by omega
          refine ⟨hx, hn, hi, ?_, hm, hki, hsz⟩
          rw [← hb]
          unfold take size at *
          exact List.take_of_length_le (by omega)
        all_goals
          equiv_skip
          intros
          rename_i h
          obtain ⟨⟨hx, hn, hk, hkle, hi1, hi2, hb, hl, hm⟩, -⟩ := h
          refine ⟨hx, hn, hk, hkle, by rw [hi1, hi2], by rw [hb, hl], hm, by omega, by omega, ?_⟩
          rw [hb, hi1]
          rfl
      equiv_while (§(localVarLens "x2" (List Bool)){1} = §(localVarLens "x1" (List Bool)){2} ∧
          §n{1} = size_out ∧ §i{1} = §i{2} ∧ take §k{1} §bs{1} = §l{2} ∧
          §IRO.mp{1} = §Eager.RO.m{2} ∧ §k{1} ≤ §i{1} ∧ size §bs{1} = §i{1})
      case body =>
        stmt_wp
        equiv_seq 1 1 : (§(localVarLens "x2" (List Bool)){1} = §(localVarLens "x1" (List Bool)){2} ∧
            §n{1} = size_out ∧ §i{1} = §i{2} ∧ take §k{1} §bs{1} = §l{2} ∧
            §IRO.mp{1} = §Eager.RO.m{2} ∧ §k{1} ≤ §i{1} ∧ size §bs{1} = §i{1} ∧ §i{1} < §n{1} ∧
            §(localVarLens "x3" (List Bool)){1} = §(localVarLens "x2" (List Bool)){1} ∧
            §n0{1} = §i{1} ∧ §x4{2} = (§(localVarLens "x1" (List Bool)){2}, §i{2}))
        · stmt_wp
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hg⟩
          simp only [decide_eq_true_eq] at hg
          exact ⟨h1, h2, h3, h4, h5, h6, h7, hg⟩
        equiv_if{1}
        case «then» =>
          stmt_wp
          equiv_rnd
          equiv_skip
          rintro x2 n i k bs mp x3 n0 x1' i' l m x4
            ⟨⟨rfl, rfl, rfl, rfl, rfl, hki, hsz, hlt, rfl, rfl, rfl⟩, hd⟩ a _
          simp only [hd, ↓reduceIte, FMap.get_set_sameE, size_rcons',
            take_rcons_le _ _ _ (show k ≤ size bs by omega)]
          exact ⟨trivial, trivial, trivial, trivial, trivial, by omega, by omega⟩
        case «else» =>
          stmt_split{2} 1
          refine prhlStmt_seq_sample_right ?_
          equiv_skip
          rintro σ₂ x2 n i k bs mp x3 n0 ⟨⟨hx, hn, hi, ht, hm, hki, hsz, hlt, rfl, rfl, hx4⟩, hd⟩
          refine ⟨(is_lossless_iff_expected _).mp dbool_ll, fun a _ => ?_⟩
          simp_reads
          rw [hx4, ← hm]
          simp only [Bool.not_eq_false', decide_eq_true_eq] at hd
          rw [hx, hi] at hd
          simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, size_rcons',
            take_rcons_le _ _ _ (show k ≤ size bs by omega)]
          subst hx hi hn
          exact ⟨rfl, rfl, rfl, ht, trivial, by omega, by omega⟩
      case guard =>
        rintro _ _ _ _ _ _ _ _ _ _ ⟨-, hn, hi, -⟩
        rw [hn, hi]
      case exit =>
        rintro _ _ _ _ _ _ _ _ _ _ ⟨-, -, -, ht, hm, -⟩ _
        exact ⟨by rw [← ht]; rfl, hm⟩
      all_goals
        equiv_skip
        intros
        simp_all
        try omega
  case «else» =>
    stmt_wp
    equiv_rcondf{2}
    equiv_seq 1 1 : (§x5{1} = §x1{2} ∧ §n1{1} = §n{2} ∧ §i0{1} = §i{2} ∧ §bs0{1} = §l{2} ∧
        §IRO.mp{1} = §Eager.RO.m{2} ∧ size_out < §n{2})
    · stmt_wp
      equiv_skip
      rintro _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, hg⟩
      simp only [decide_eq_false_iff_not, not_le] at hg
      exact ⟨rfl, rfl, rfl, rfl, rfl, hg⟩
    equiv_if{1}
    case «else» =>
      refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
      obtain ⟨-, hg⟩ := h
      simp [BIRO.valid, valid_toplevel] at hg
    case «then» =>
      equiv_while (§x5{1} = §x1{2} ∧ §n1{1} = §n{2} ∧ §i0{1} = §i{2} ∧ §bs0{1} = §l{2} ∧
        §IRO.mp{1} = §Eager.RO.m{2} ∧ size_out < §n{2})
      case body =>
        stmt_wp
        equiv_seq 1 1 : (§x5{1} = §x1{2} ∧ §n1{1} = §n{2} ∧ §i0{1} = §i{2} ∧ §bs0{1} = §l{2} ∧
        §IRO.mp{1} = §Eager.RO.m{2} ∧ size_out < §n{2} ∧ §i0{1} < §n1{1} ∧
            §x6{1} = §x5{1} ∧ §n2{1} = §i0{1} ∧ §x2{2} = (§x1{2}, §i{2}))
        · stmt_wp
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ ⟨⟨hx, hn, hi, hb, hm, hs⟩, hg⟩
          simp only [decide_eq_true_eq] at hg
          exact ⟨hx, hn, hi, hb, hm, hs, hg⟩
        equiv_if{1}
        case «then» =>
          stmt_wp
          equiv_rnd
          equiv_skip
          rintro x n i bs mp x0 n0 x' n' i' l m x0'
            ⟨⟨rfl, rfl, rfl, rfl, rfl, hs, hlt, rfl, rfl, rfl⟩, hd⟩ a _
          simp [hd, hs]
        case «else» =>
          stmt_split{2} 1
          refine prhlStmt_seq_sample_right ?_
          equiv_skip
          rintro σ₂ x n i bs mp x0 n0 ⟨⟨hx, hn, hi, hb, hm, hs, hlt, rfl, rfl, hx0⟩, hd⟩
          refine ⟨(is_lossless_iff_expected _).mp dbool_ll, fun a _ => ?_⟩
          simp_reads
          rw [hx0, ← hm]
          simp only [Bool.not_eq_false', decide_eq_true_eq] at hd
          rw [hx, hi] at hd
          simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          subst hx hi hb hn
          exact ⟨rfl, rfl, rfl, rfl, trivial, hs⟩
      case guard =>
        rintro _ _ _ _ _ _ _ _ _ _ ⟨-, hn, hi, -⟩
        rw [hn, hi]
      case exit =>
        rintro _ _ _ _ _ _ _ _ _ _ ⟨-, hn, hi, hb, hm, hs⟩ hg
        simp only [decide_eq_false_iff_not, not_lt] at hg
        refine ⟨?_, by rw [hb], hm⟩
        simp only [decide_eq_false_iff_not, not_lt]
        omega
      all_goals
        equiv_skip
        intros
        simp_all

/-- `FSome(BIRO.IRO).init ~ FSome(Fill_In(LRO)).init`: both maps empty.  Not an EC lemma. -/
theorem eager_init_lazy :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (OptionIndifferentiability.OFUNCTIONALITY.init state (List Bool × ℤ) (List Bool)
        (Module.app FSome BIRO.IRO.asF)).procedure
      (OptionIndifferentiability.OFUNCTIONALITY.init state (List Bool × ℤ) (List Bool)
        (Module.app FSome (Module.app Fill_In Eager.LRO))).procedure
      (fun _ g₁ _ g₂ => eagerL.equal_outside g₁ g₂ ∧ eagerI (eagerL.get g₁) (eagerL.get g₂)) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_skip
  rintro g _ rfl
  exact ⟨(eagerL_IRO g _).symm.trans (eagerL_RO g _), rfl⟩

/-- `ExtendSample(FSome(BIRO.IRO)).init ~ FSome(Fill_In(RO)).init`: both maps empty.  Not an EC
lemma. -/
theorem eager_init_ext :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (OptionIndifferentiability.OFUNCTIONALITY.init state (List Bool × ℤ) (List Bool)
        (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))).procedure
      (OptionIndifferentiability.OFUNCTIONALITY.init state (List Bool × ℤ) (List Bool)
        (Module.app FSome (Module.app Fill_In Eager.RO))).procedure
      (fun _ g₁ _ g₂ => eagerL.equal_outside g₁ g₂ ∧ eagerI (eagerL.get g₁) (eagerL.get g₂)) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_skip
  rintro g _ rfl
  exact ⟨(eagerL_IRO g _).symm.trans (eagerL_RO g _), rfl⟩

set_option maxHeartbeats 4000000 in
-- `fp_module` through the functionalities
/-- `eq_eager_ideal` through `FSome`, over the states equal outside `eagerL` (EC: `inline{1} 1;
inline{2} 1; sp; sim 1 1; by call eq_eager_ideal; auto`).  Not an EC lemma. -/
theorem eager_f_lazy :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ eagerL.equal_outside g₁ g₂ ∧
        eagerI (eagerL.get g₁) (eagerL.get g₂))
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app FSome BIRO.IRO.asF)).procedure
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app FSome (Module.app Fill_In Eager.LRO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eagerL.equal_outside g₁ g₂ ∧
        eagerI (eagerL.get g₁) (eagerL.get g₂)) := by
  have h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂)
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app FSome BIRO.IRO.asF)).procedure
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app FSome (Module.app Fill_In Eager.LRO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ BIRO.IRO.mp.get g₁ = Eager.RO.m.get g₂) := by
    have e₁ : (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ)
        (List Bool) BIRO.IRO.asF).procedure = BIRO.IRO.f.procedure := by
      simp [BIRO.IRO.asF]
    have e₂ : (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ)
        (List Bool) (Module.app Fill_In Eager.LRO)).procedure =
        (Module.app Fill_In.f Eager.LRO).procedure := by
      simp only [Fill_In.apply_simp]
      unfold Indifferentiability.FUNCTIONALITY.f
      erw [Module.snd'_pair_proc]
    equiv_proc
    stmt_inline{1} 0
    stmt_inline{2} 0
    stmt_wp
    rw [e₁, e₂]
    equiv_call eq_eager_ideal
    stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => ⟨h, fun _ _ _ _ ⟨hr, hm⟩ => ⟨by rw [hr], hm⟩⟩
  have h₁ : FVP.fvP (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
      (Module.app FSome BIRO.IRO.asF)) ≤ eagerL.footprint := by
    fp_module eagerL
  have h₂ : FVP.fvP (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
      (Module.app FSome (Module.app Fill_In Eager.LRO))) ≤ eagerL.footprint := by
    fp_module eagerL
  exact prhlProc_conseq (prhlProc_frame_equal_outside_module eagerL _ _ h₁ h₂ h)
    (fun _ _ _ _ ⟨ha, he, hI⟩ => ⟨⟨ha, hI⟩, he⟩) (fun _ _ _ _ ⟨⟨hr, hI⟩, he⟩ => ⟨hr, he, hI⟩)

set_option maxHeartbeats 4000000 in
-- `fp_module` through the functionalities
/-- `eq_eager_ideal2` over the states equal outside `eagerL`.  Not an EC lemma. -/
theorem eager_f_ext :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ eagerL.equal_outside g₁ g₂ ∧
        eagerI (eagerL.get g₁) (eagerL.get g₂))
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))).procedure
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app FSome (Module.app Fill_In Eager.RO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eagerL.equal_outside g₁ g₂ ∧
        eagerI (eagerL.get g₁) (eagerL.get g₂)) := by
  have h₁ : FVP.fvP (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
      (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))) ≤ eagerL.footprint := by
    fp_module eagerL
  have h₂ : FVP.fvP (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
      (Module.app FSome (Module.app Fill_In Eager.RO))) ≤ eagerL.footprint := by
    fp_module eagerL
  exact prhlProc_conseq (prhlProc_frame_equal_outside_module eagerL _ _ h₁ h₂ eq_eager_ideal2)
    (fun _ _ _ _ ⟨ha, he, hI⟩ => ⟨⟨ha, hI⟩, he⟩) (fun _ _ _ _ ⟨⟨hr, hI⟩, he⟩ => ⟨hr, he, hI⟩)

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

/-- `Dist(F).distinguish` is the ideal game over `FSome(Fill_In(F))` that it calls.  Not an EC
lemma. -/
theorem Dist_game (A : SH.AdvPreimage) (F : Eager.RO_T) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂) (Module.app (Dist Log_m A) F).procedure
      (IdealGame (Module.app FSome (Module.app Fill_In F))
        (ODRestr (Dist_of_P1Adv Log_m A))).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  unfold IdealGame
  equiv_proc
  stmt_inline{1} 0
  stmt_wp
  simp only [OptionIndifferentiability.OFUNCTIONALITY.view]
  equiv_call (prhlProc_refl _)
  stmt_wp
  equiv_skip
  exact fun _ _ h => ⟨h, fun _ _ _ _ h => h.1⟩

set_option maxHeartbeats 4000000 in
-- `fp_module` through the adversary's oracles
/-- `ODRestr(Dist_of_P1Adv(A))` touches `A`'s variables, `Log.m` and `Counter.c`.  Not an EC
lemma. -/
theorem fvP_ODRestr_P1 [Lens.Disjoint Log_m Counter.c] [Lens.Disjoint Counter.c Log_m]
    (A : SH.AdvPreimage) :
    FVP.fvP (ODRestr (Dist_of_P1Adv Log_m A)) ≤
      FVP.fvP A ⊔ (Lens.pair Log_m Counter.c).footprint := by
  fp_module (Lens.pair Log_m Counter.c)

set_option maxHeartbeats 10000000 in
-- `fp_module` through `Dist`'s nest of oracles
/-- `Dist(A)` touches `A`'s variables, `Log.m`, `Counter.c`, the simulator's maps and
`Gconcl_list.BIRO2.IRO.mp`.  Not an EC lemma. -/
theorem fvP_Dist [Lens.Disjoint Log_m Counter.c] [Lens.Disjoint Counter.c Log_m]
    [Lens.Disjoint Log_m SHA3Indiff.Simulator.m] [Lens.Disjoint SHA3Indiff.Simulator.m Log_m]
    [Lens.Disjoint Log_m SHA3Indiff.Simulator.mi] [Lens.Disjoint SHA3Indiff.Simulator.mi Log_m]
    [Lens.Disjoint Log_m SHA3Indiff.Simulator.paths]
    [Lens.Disjoint SHA3Indiff.Simulator.paths Log_m]
    [Lens.Disjoint Log_m Gconcl_list.BIRO2.IRO.mp] [Lens.Disjoint Gconcl_list.BIRO2.IRO.mp Log_m]
    (A : SH.AdvPreimage) :
    FVP.fvP (Dist Log_m A) ≤ FVP.fvP A ⊔ (Lens.pair Log_m soroG).footprint := by
  fp_module (Lens.pair Log_m soroG)

set_option maxHeartbeats 4000000 in
-- the restrictions' `fp_sub`/`fp_disjoint`
/-- `local lemma eager_ideal &m`. -/
theorem eager_ideal (A : SH.AdvPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_P1Adv Log_m A))).procedure () m (fun r _ => r = true) =
      Procedure.Pr (IdealGame (Module.app ExtendSample (Module.app FSome BIRO.IRO.asF))
        (ODRestr (Dist_of_P1Adv Log_m A))).procedure () m (fun r _ => r = true) := by
  have hLA : Log_m.footprint ≤ ARestrictions.footprintᶜ := le_sup_left.trans _hfresh.1
  have hAA : FVP.fvP A ≤ ARestrictions.footprintᶜ :=
    _hAd.trans (Footprint.compl_antimono (le_sup_left.trans le_sup_left))
  have hLX : ∀ {β : Type} (X : Lens β VariableAssignment),
      X.footprint ≤ ARestrictions.footprint → Lens.Disjoint Log_m X ∧ Lens.Disjoint X Log_m :=
    fun X hX => ⟨Lens.disjoint_of_footprint_le_compl _ _ (hLA.trans (Footprint.compl_antimono hX)),
      Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp
        (hLA.trans (Footprint.compl_antimono hX)))⟩
  have hC := hLX Counter.c (by unfold ARestrictions.footprint; fp_sub)
  have hSm := hLX SHA3Indiff.Simulator.m (by unfold ARestrictions.footprint; fp_sub)
  have hSmi := hLX SHA3Indiff.Simulator.mi (by unfold ARestrictions.footprint; fp_sub)
  have hSp := hLX SHA3Indiff.Simulator.paths (by unfold ARestrictions.footprint; fp_sub)
  have hB2 := hLX Gconcl_list.BIRO2.IRO.mp (by unfold ARestrictions.footprint; fp_sub)
  haveI := hC.1
  haveI := hC.2
  haveI := hSm.1
  haveI := hSm.2
  haveI := hSmi.1
  haveI := hSmi.2
  haveI := hSp.1
  haveI := hSp.2
  haveI := hB2.1
  haveI := hB2.2
  have hLe : Log_m.footprint ≤ (eagerL.footprint)ᶜ := hLA.trans (Footprint.compl_antimono (by
    simp only [eagerL, Footprint.lens_pair]
    unfold ARestrictions.footprint
    fp_sub))
  have hAe : FVP.fvP A ≤ (eagerL.footprint)ᶜ := hAA.trans (Footprint.compl_antimono (by
    simp only [eagerL, Footprint.lens_pair]
    unfold ARestrictions.footprint
    fp_sub))
  -- the distinguisher `ODRestr(Dist_of_P1Adv(A))`, outside `eagerL`
  have hOD := fvP_ODRestr_P1 Log_m A
  rw [Footprint.lens_pair] at hOD
  have hODec : Module.ECModule (ODRestr (Dist_of_P1Adv Log_m A)) OIndif.distExt :=
    ⟨ODistinguisher_representable _, Footprint.FinitelySupported.mono hOD
      (hA.2.sup (_hfresh.2.2.sup (Footprint.FinitelySupported.globalVar _)))⟩
  have hODL : FVP.fvP (ODRestr (Dist_of_P1Adv Log_m A)) ≤ (eagerL.footprint)ᶜ := by
    refine hOD.trans (sup_le hAe (sup_le hLe ?_))
    simp only [eagerL, Footprint.lens_pair]
    fp_disjoint
  have h1 := ideal_game_congr eagerL eagerI eagerL_BIRO2 _ _ _ hODec hODL eager_init_lazy
    eager_f_lazy
  have h2 := ideal_game_congr eagerL eagerI eagerL_BIRO2 _ _ _ hODec hODL eager_init_ext
    eager_f_ext
  -- EC's `call (RO_LRO_D Dist _)`
  have hD := fvP_Dist Log_m A
  rw [Footprint.lens_pair] at hD
  have hDfs : (FVP.fvP (Dist Log_m A)).FinitelySupported := by
    refine Footprint.FinitelySupported.mono hD (hA.2.sup (_hfresh.2.2.sup ?_))
    simp only [soroG, Footprint.lens_pair]
    repeat' first
      | exact Footprint.FinitelySupported.globalVar _
      | apply Footprint.FinitelySupported.sup
  have hmod := PROM.FullRO.RO_Distinguisher.ecModule (List Bool × ℤ) Bool Unit Bool
    (Dist Log_m A) hDfs
  have hdisj : FVP.fvP (Dist Log_m A) ≤ ((Eager.RO.m).footprint ⊔ (Eager.FRO.m).footprint)ᶜ := by
    have hRA : (Eager.RO.m).footprint ⊔ (Eager.FRO.m).footprint ≤ ARestrictions.footprint := by
      unfold ARestrictions.footprint
      fp_sub
    refine hD.trans (sup_le (hAA.trans (Footprint.compl_antimono hRA))
      (sup_le (hLA.trans (Footprint.compl_antimono hRA)) ?_))
    simp only [soroG, Footprint.lens_pair]
    fp_disjoint
  have hRO := PROM.FullRO.FullEager.RO_LRO_D (List Bool × ℤ) Bool Unit Bool (fun _ => dbool)
    Eager.FRO.m (fun _ => dbool_ll) Eager.RO.m (Dist Log_m A) hmod hdisj
  have hE : ∀ (r₁ : Bool) (g₁ : VariableAssignment) (r₂ : Bool) (g₂ : VariableAssignment),
      r₁ = r₂ → (r₁ = true ↔ r₂ = true) := fun _ _ _ _ h => by rw [h]
  exact (Procedure.Pr_eq_of_prhlProc (a₁ := ()) (a₂ := ()) h1 hE rfl).trans
    ((Procedure.Pr_eq_of_prhlProc (a₁ := ()) (a₂ := ()) (Dist_game Log_m A Eager.LRO) hE
      rfl).symm.trans
    ((Procedure.Pr_eq_of_prhlProc (a₁ := ()) (a₂ := ()) hRO
      (fun r₁ g₁ r₂ g₂ h => hE r₁ g₁ r₂ g₂ h.1)
      ⟨rfl, rfl, rfl⟩).symm.trans
    ((Procedure.Pr_eq_of_prhlProc (a₁ := ()) (a₂ := ()) (Dist_game Log_m A Eager.RO) hE
      rfl).trans
    (Procedure.Pr_eq_of_prhlProc (a₁ := ()) (a₂ := ()) h2 hE rfl).symm)))

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

/-- `dlist dbool size_out` read back by `of_list` is `dout` (`dout_equal_dlist`, `of_listK`). -/
theorem dlist_dout :
    (dlist dbool size_out >>= fun l => (pure (oget (of_list l)) : SubProbability f_out)) =
      dout := by
  refine SubProbability.ext_of_expected fun F => ?_
  rw [SubProbability.expected_bind]
  change (dlist dbool Params.size_out).expected _ = Params.dout.expected F
  rw [← Params.dout_equal_dlist, SubProbability.expected_bind]
  simp only [expected_pure]
  refine congrArg Params.dout.expected (funext fun x => ?_)
  have := (Params.to_listK x (Params.to_list x)).mp rfl
  simp only [of_list, this, oget, Option.getD_some]

/-- The variables of `rw_ideal`'s invariant: `RFList.m` (left), `SORO.RO.RO.m` (right). -/
noncomputable def riL [Lens.Disjoint RFList_m SORO.RO.RO.m] :
    Lens (FMap (List Bool) f_out × FMap (List Bool) f_out) VariableAssignment :=
  Lens.pair RFList_m SORO.RO.RO.m

/-- EC's `RFList.m{1} = SORO.RO.RO.m{2}`, on the contents of `riL`. -/
def riI (v₁ v₂ : FMap (List Bool) f_out × FMap (List Bool) f_out) : Prop := v₁.1 = v₂.2

section
variable [Lens.Disjoint RFList_m SORO.RO.RO.m]

theorem riL_footprint : (riL RFList_m).footprint =
    RFList_m.footprint ⊔ (SORO.RO.RO.m).footprint := by
  simp only [riL, Footprint.lens_pair]

/-- A write of `RFList.m` keeps a state equal to itself outside `riL`. -/
theorem riL_RFList (g : VariableAssignment) (v : FMap (List Bool) f_out) :
    (riL RFList_m).equal_outside g (RFList_m.set v g) :=
  (Lens.equal_outside_set_self _ g v).pair_left

/-- A write of `SORO.RO.RO.m` keeps a state equal to itself outside `riL`. -/
theorem riL_RO (g : VariableAssignment) (v : FMap (List Bool) f_out) :
    (riL RFList_m).equal_outside g ((SORO.RO.RO.m).set v g) :=
  (Lens.equal_outside_set_self _ g v).pair_right

/-- EC's `if{1}; …; rnd (fun l => oget (of_list l)) to_list` on `RFList.get ~ RF(RO).get`, the
leaf of `rw_ideal`'s oracle premise.  Not an EC lemma. -/
theorem ri_get :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ (riL RFList_m).equal_outside g₁ g₂ ∧
        riI ((riL RFList_m).get g₁) ((riL RFList_m).get g₂))
      (SecureORO.RF_T.get (List Bool) f_out (RFList RFList_m)).procedure
      (SecureORO.RF_T.get (List Bool) f_out (Module.app SORO.RF SORO.RO.RO)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ (riL RFList_m).equal_outside g₁ g₂ ∧
        riI ((riL RFList_m).get g₁) ((riL RFList_m).get g₂)) := by
  rw [RFList_get]
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [PROM.FullRO.RO.asRO, PROM.FullRO.RO_T.get.mk_simp]
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x1{2} ∧ (riL RFList_m).equal_outside §allGlobals{1} §allGlobals{2} ∧
      riI ((riL RFList_m).get §allGlobals{1}) ((riL RFList_m).get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ ⟨rfl, he, hI⟩
    exact ⟨rfl, he, hI⟩
  equiv_if{1}
  case «then» =>
    stmt_wp
    equiv_rnd (fun l => oget (of_list l))
    equiv_skip
    rintro g₁ g₂ x0 x1 ⟨⟨rfl, he, hI⟩, hg⟩
    change RFList_m.get g₁ = SORO.RO.RO.m.get g₂ at hI
    rw [hI] at hg
    refine ⟨dlist_dout, fun a _ => ?_⟩
    simp only [hg, ↓reduceIte]
    refine ⟨by rw [FMap.get_set_sameE, FMap.get_set_sameE]; rfl, ?_, ?_⟩
    · rw [hI]
      exact (riL_RFList RFList_m _ _).symm.trans (he.trans (riL_RO RFList_m _ _))
    · change RFList_m.get (RFList_m.set _ g₁) = SORO.RO.RO.m.get (SORO.RO.RO.m.set _ g₂)
      rw [RFList_m.set_get, SORO.RO.RO.m.set_get, hI]
  case «else» =>
    stmt_split{2} 1
    refine prhlStmt_seq_sample_right ?_
    equiv_skip
    rintro σ₂ g₁ x0 ⟨⟨hx, he, hI⟩, hg⟩
    change RFList_m.get g₁ = SORO.RO.RO.m.get σ₂.globals at hI
    refine ⟨(is_lossless_iff_expected _).mp Params.dout_ll, fun a _ => ?_⟩
    simp_reads
    rw [hI, hx] at hg
    simp only [hg]
    refine ⟨?_, he, hI⟩
    rw [hI, hx]
    simp only [Bool.not_eq_false', decide_eq_true_eq] at hg
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hg)
    simp only [Bool.false_eq_true, ↓reduceIte, hv]
    rfl

end

/-- EC's `proc; sp; if; auto; call (: …)` on `Bounder(F₁).get ~ Bounder(F₂).get`: a premise
`F₁.get ~ F₂.get` over the states equal outside a lens `L` (with a relation `I` of its contents) is
kept by `Bounder`, whose counter lies outside `L`.  Not an EC lemma. -/
theorem bounder_get_congr {Ω : Type} (L : Lens Ω VariableAssignment) (I : Ω → Ω → Prop)
    [Lens.Disjoint SORO.Bounder.bounder L] (F₁ F₂ : SORO.RF_T)
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))
      (SecureORO.RF_T.get (List Bool) f_out F₁).procedure
      (SecureORO.RF_T.get (List Bool) f_out F₂).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))
      (SecureORO.RF_T.get (List Bool) f_out (Module.app SORO.Bounder F₁)).procedure
      (SecureORO.RF_T.get (List Bool) f_out (Module.app SORO.Bounder F₂)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂)) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧
      §(localVarLens "y" (Option f_out)){1} = §(localVarLens "y" (Option f_out)){2} ∧
      L.equal_outside §allGlobals{1} §allGlobals{2} ∧ I (L.get §allGlobals{1}) (L.get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  equiv_if
  case guard =>
    rintro g₁ g₂ _ _ _ _ ⟨-, -, he, -⟩
    rw [he.get_disjoint]
  case «else» =>
    equiv_skip
    rintro g₁ g₂ _ _ _ _ ⟨⟨-, hy, he, hI⟩, -⟩
    exact ⟨hy, he, hI⟩
  case «then» =>
    equiv_call h
    stmt_wp
    equiv_skip
    rintro g₁ g₂ _ _ _ _ ⟨⟨rfl, -, he, hI⟩, -⟩
    refine ⟨⟨rfl, ?_, ?_⟩, fun _ _ _ _ h => h⟩
    · rw [he.get_disjoint]
      exact he.set_disjoint _
    · exact hI

section
variable [Lens.Disjoint RFList_m SORO.RO.RO.m] [Lens.Disjoint SORO.Bounder.bounder RFList_m]

/-- `Bounder(RFList).get ~ Bounder(RF(RO)).get`: the oracle premise of `rw_ideal`'s `call`. -/
theorem ri_bget :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ (riL RFList_m).equal_outside g₁ g₂ ∧
        riI ((riL RFList_m).get g₁) ((riL RFList_m).get g₂))
      (SecureORO.RF_T.get (List Bool) f_out
        (Module.app SORO.Bounder (RFList RFList_m))).procedure
      (SecureORO.RF_T.get (List Bool) f_out
        (Module.app SORO.Bounder (Module.app SORO.RF SORO.RO.RO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ (riL RFList_m).equal_outside g₁ g₂ ∧
        riI ((riL RFList_m).get g₁) ((riL RFList_m).get g₂)) := by
  haveI : Lens.Disjoint SORO.Bounder.bounder (riL RFList_m) := by unfold riL; infer_instance
  exact bounder_get_congr _ _ _ _ (ri_get RFList_m)

end

set_option maxHeartbeats 10000000 in
-- `fp_module` through `SORO_P1`'s nest of oracles (its typing alone takes about 20 s)
/-- `SORO_P1(A)` touches `A`'s variables, `Log.m`, `Counter.c`, the simulator's maps and
`Gconcl_list.BIRO2.IRO.mp`.  Not an EC lemma. -/
theorem fvP_SORO_P1 [Lens.Disjoint Log_m Counter.c] [Lens.Disjoint Counter.c Log_m]
    [Lens.Disjoint Log_m SHA3Indiff.Simulator.m] [Lens.Disjoint SHA3Indiff.Simulator.m Log_m]
    [Lens.Disjoint Log_m SHA3Indiff.Simulator.mi] [Lens.Disjoint SHA3Indiff.Simulator.mi Log_m]
    [Lens.Disjoint Log_m SHA3Indiff.Simulator.paths]
    [Lens.Disjoint SHA3Indiff.Simulator.paths Log_m]
    [Lens.Disjoint Log_m Gconcl_list.BIRO2.IRO.mp] [Lens.Disjoint Gconcl_list.BIRO2.IRO.mp Log_m]
    (A : SH.AdvPreimage) :
    FVP.fvP (SORO_P1 Log_m A) ≤ FVP.fvP A ⊔ (Lens.pair Log_m soroG).footprint := by
  fp_module (Lens.pair Log_m soroG)

/-- `SORO_P1(A)` is an EasyCrypt-like module (representable over `Oracle.get`, finitely many
variables), touching `A`'s variables, `Log.m` and `soroG`'s.  Not an EC lemma. -/
theorem SORO_P1_ec (A : SH.AdvPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (hfresh : LocalFresh Log_m RFList_m) :
    Module.ECModule (SORO_P1 Log_m A) (SecureORO.Oracle.ext (List Bool) f_out) ∧
      FVP.fvP (SORO_P1 Log_m A) ≤ FVP.fvP A ⊔ (Log_m.footprint ⊔ soroG.footprint) := by
  have hLA : Log_m.footprint ≤ ARestrictions.footprintᶜ := le_sup_left.trans hfresh.1
  have hLX : ∀ {β : Type} (X : Lens β VariableAssignment),
      X.footprint ≤ ARestrictions.footprint → Lens.Disjoint Log_m X ∧ Lens.Disjoint X Log_m :=
    fun X hX => ⟨Lens.disjoint_of_footprint_le_compl _ _ (hLA.trans (Footprint.compl_antimono hX)),
      Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp
        (hLA.trans (Footprint.compl_antimono hX)))⟩
  have hC := hLX Counter.c (by unfold ARestrictions.footprint; fp_sub)
  have hSm := hLX SHA3Indiff.Simulator.m (by unfold ARestrictions.footprint; fp_sub)
  have hSmi := hLX SHA3Indiff.Simulator.mi (by unfold ARestrictions.footprint; fp_sub)
  have hSp := hLX SHA3Indiff.Simulator.paths (by unfold ARestrictions.footprint; fp_sub)
  have hB2 := hLX Gconcl_list.BIRO2.IRO.mp (by unfold ARestrictions.footprint; fp_sub)
  haveI := hC.1
  haveI := hC.2
  haveI := hSm.1
  haveI := hSm.2
  haveI := hSmi.1
  haveI := hSmi.2
  haveI := hSp.1
  haveI := hSp.2
  haveI := hB2.1
  haveI := hB2.2
  have hfp := fvP_SORO_P1 Log_m A
  rw [Footprint.lens_pair] at hfp
  have hGfs : (Log_m.footprint ⊔ soroG.footprint).FinitelySupported := by
    refine hfresh.2.2.sup ?_
    simp only [soroG, Footprint.lens_pair]
    repeat' first
      | exact Footprint.FinitelySupported.globalVar _
      | apply Footprint.FinitelySupported.sup
  refine ⟨⟨Module.representable_of_firstOrder ?_ ?_ (SecureORO.Oracle.ext (List Bool) f_out)
    (fun _ => rfl) _, Footprint.FinitelySupported.mono hfp (hA.2.sup hGfs)⟩, hfp⟩
  · simp [IsModule.moduleTypeRep, ModuleTypeRep.FirstOrder, Module.moduleTypeRep,
      SecureORO.Oracle.typeRep]
  · intro sig n
    cases n with
    | zero => exact ⟨fun U hU => by simp at hU; subst hU; infer_instance, inferInstance⟩
    | succ n => nomatch n

/-- EC's `byequiv` on `SORO.Preimage(D, F₁) ~ SORO.Preimage(D, F₂)` for a module `D` outside a lens
`L`: the initializations (premise `hinit`), one equal-outside abstract call to `D` (its oracle
premise `hget`) and the last `get` (`hget` again).  Not an EC lemma. -/
theorem soro_pre_game {Ω : Type} (L : Lens Ω VariableAssignment) (I : Ω → Ω → Prop)
    [Lens.Disjoint SORO.Bounder.bounder L] (F₁ F₂ : SORO.RF_T) (D : SORO.AdvPreimage)
    (hD : Module.ECModule D (SecureORO.Oracle.ext (List Bool) f_out))
    (hDL : FVP.fvP D ≤ L.footprintᶜ)
    (hinit : prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (SecureORO.RF_T.init (List Bool) f_out F₁).procedure
      (SecureORO.RF_T.init (List Bool) f_out F₂).procedure
      (fun _ g₁ _ g₂ => L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂)))
    (hget : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L.equal_outside g₁ g₂ ∧
        I (L.get g₁) (L.get g₂))
      (SecureORO.RF_T.get (List Bool) f_out (Module.app SORO.Bounder F₁)).procedure
      (SecureORO.RF_T.get (List Bool) f_out (Module.app SORO.Bounder F₂)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L.equal_outside g₁ g₂ ∧ I (L.get g₁) (L.get g₂))) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (Module.app SORO.Preimage (Module.pair D F₁)).procedure
      (Module.app SORO.Preimage (Module.pair D F₂)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  stmt_swap{1} 1 3
  stmt_swap{2} 1 3
  equiv_seq 2 2 : (§hash{1} = §hash{2} ∧ L.equal_outside §allGlobals{1} §allGlobals{2} ∧
      I (L.get §allGlobals{1}) (L.get §allGlobals{2}))
  · equiv_rnd
    equiv_call hinit
    stmt_wp
    equiv_skip
    rintro σ₁ σ₂ h
    rw [h]
    exact ⟨rfl, fun _ _ _ _ h' _ _ => h'⟩
  equiv_seq 1 1 : (§(localVarLens "m" (List Bool)){1} = §(localVarLens "m" (List Bool)){2} ∧
      §hash{1} = §hash{2} ∧ L.equal_outside §allGlobals{1} §allGlobals{2} ∧
      I (L.get §allGlobals{1}) (L.get §allGlobals{2}))
  swap
  · equiv_call hget
    equiv_skip
    rintro g₁ g₂ m₁ hash₁ m₂ hash₂ ⟨hm, hh, he, hI⟩
    exact ⟨⟨hm, he, hI⟩, fun r₁ _ r₂ _ h => by rw [h.1, hh]⟩
  stmt_split{1} 1
  stmt_split{2} 1
  refine prhlStmt_seq_call (prhlProc_abstract_call_equal_outside_module
    L D (SecureORO.Oracle.ext (List Bool) f_out) hD.1 hDL I ?hc _ _ ?horacle) ?_
  case hc =>
    intro _ n
    cases n with
    | zero => exact inferInstanceAs (Countable (List Bool))
    | succ n => nomatch n
  case horacle =>
    intro _ n
    cases n with
    | zero =>
      simp only [SecureORO.Oracle.ext, HoleSigs.Instantiation.lookup_zero_single,
        SecureORO.Oracle.get.mk_simp]
      exact hget
    | succ n => nomatch n
  equiv_skip
  rintro σ₁ σ₂ ⟨hh, he, hI⟩
  refine ⟨⟨hh, he, hI⟩, fun r₁ g₁ r₂ g₂ ⟨hr, he', hI'⟩ => ?_⟩
  simp_reads
  exact ⟨hr, hh, he', hI'⟩

/-- `RFList.init ~ RF(RO).init`: both maps empty.  Not an EC lemma. -/
theorem ri_init [Lens.Disjoint RFList_m SORO.RO.RO.m] :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (SecureORO.RF_T.init (List Bool) f_out (RFList RFList_m)).procedure
      (SecureORO.RF_T.init (List Bool) f_out (Module.app SORO.RF SORO.RO.RO)).procedure
      (fun _ g₁ _ g₂ => (riL RFList_m).equal_outside g₁ g₂ ∧
        riI ((riL RFList_m).get g₁) ((riL RFList_m).get g₂)) := by
  rw [RFList_init]
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [PROM.FullRO.RO.asRO, PROM.FullRO.RO_T.init.mk_simp]
  stmt_inline{2} 0
  stmt_wp
  equiv_skip
  rintro σ₁ σ₂ h
  rw [h]
  refine ⟨(riL_RFList RFList_m _ _).symm.trans (riL_RO RFList_m _ _), ?_⟩
  change RFList_m.get (RFList_m.set _ _) = SORO.RO.RO.m.get (SORO.RO.RO.m.set _ _)
  rw [RFList_m.set_get, SORO.RO.RO.m.set_get]

/-- EC's `byequiv(: ={glob A} ==> _)` in `rw_ideal`: `Preimage(SORO_P1(A), RFList)` against
`Preimage(SORO_P1(A), RF(RO))`, the states equal outside `riL` with `RFList.m{1} = RO.m{2}`;
`SORO_P1(A)` is one abstract call (`soro_pre_game`; its oracles' trees are its own code), its
oracle premise `ri_bget`.  Not an EC lemma. -/
theorem ri_game (A : SH.AdvPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ Log_m.footprint ⊔ RFList_m.footprint)ᶜ)
    (hfresh : LocalFresh Log_m RFList_m) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (Module.app SORO.Preimage (Module.pair (SORO_P1 Log_m A) (RFList RFList_m))).procedure
      (Module.app SORO.Preimage (Module.pair (SORO_P1 Log_m A)
        (Module.app SORO.RF SORO.RO.RO))).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hRA : RFList_m.footprint ≤ ARestrictions.footprintᶜ := le_sup_right.trans hfresh.1
  have hLA : Log_m.footprint ≤ ARestrictions.footprintᶜ := le_sup_left.trans hfresh.1
  haveI : Lens.Disjoint RFList_m SORO.RO.RO.m := Lens.disjoint_of_footprint_le_compl _ _
    (hRA.trans (Footprint.compl_antimono (by unfold ARestrictions.footprint; fp_sub)))
  haveI : Lens.Disjoint SORO.Bounder.bounder RFList_m := Lens.disjoint_of_footprint_le_compl _ _
    ((Footprint.le_compl_comm _ _).mp
      (hRA.trans (Footprint.compl_antimono (by unfold ARestrictions.footprint; fp_sub))))
  haveI : Lens.Disjoint SORO.Bounder.bounder (riL RFList_m) := by unfold riL; infer_instance
  obtain ⟨hP, hfp⟩ := SORO_P1_ec Log_m RFList_m A hA hfresh
  have hPL : FVP.fvP (SORO_P1 Log_m A) ≤ ((riL RFList_m).footprint)ᶜ := by
    rw [riL_footprint]
    refine hfp.trans (sup_le (hAd.trans (Footprint.compl_antimono ?_)) (sup_le ?_ ?_))
    · unfold ARestrictions.footprint
      fp_sub
    · exact le_compl_sup hfresh.2.1
        (hLA.trans (Footprint.compl_antimono (by unfold ARestrictions.footprint; fp_sub)))
    · refine le_compl_sup ((Footprint.le_compl_comm _ _).mp
        (hRA.trans (Footprint.compl_antimono ?_))) ?_
      · simp only [soroG, Footprint.lens_pair]
        unfold ARestrictions.footprint
        fp_sub
      · simp only [soroG, Footprint.lens_pair]
        fp_disjoint
  exact soro_pre_game (riL RFList_m) riI _ _ (SORO_P1 Log_m A) hP hPL (ri_init RFList_m)
    (ri_bget RFList_m)

/-- `rw_RF_List_While` over the states equal outside `RFList.m` (the two procedures touch it only,
`prhlProc_frame_equal_outside_module`), at `Bounder`.  Not an EC lemma. -/
theorem rl_bget [Lens.Disjoint SORO.Bounder.bounder RFList_m] :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ RFList_m.equal_outside g₁ g₂ ∧
        RFList_m.get g₁ = RFList_m.get g₂)
      (SecureORO.RF_T.get (List Bool) f_out
        (Module.app SORO.Bounder (RFList RFList_m))).procedure
      (SecureORO.RF_T.get (List Bool) f_out
        (Module.app SORO.Bounder (RFWhile RFList_m))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ RFList_m.equal_outside g₁ g₂ ∧
        RFList_m.get g₁ = RFList_m.get g₂) := by
  refine bounder_get_congr RFList_m (· = ·) _ _ ?_
  have h := rw_RF_List_While RFList_m
  rw [RFList_get, RFWhile_get] at h ⊢
  have h' := prhlProc_frame_equal_outside_module RFList_m _ _ (fvP_RFList_get RFList_m)
    (fvP_RFWhile_get RFList_m) h
  exact prhlProc_conseq h' (fun _ _ _ _ ⟨ha, he, hg⟩ => ⟨⟨ha, hg⟩, he⟩)
    (fun _ _ _ _ ⟨⟨hr, hg⟩, he⟩ => ⟨hr, he, hg⟩)

/-- `RFList.init ~ RFWhile.init`: both maps empty.  Not an EC lemma. -/
theorem rl_init :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (SecureORO.RF_T.init (List Bool) f_out (RFList RFList_m)).procedure
      (SecureORO.RF_T.init (List Bool) f_out (RFWhile RFList_m)).procedure
      (fun _ g₁ _ g₂ => RFList_m.equal_outside g₁ g₂ ∧ RFList_m.get g₁ = RFList_m.get g₂) := by
  rw [RFList_init, RFWhile_init]
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_skip
  rintro σ₁ σ₂ h
  rw [h]
  exact Lens.equal_outside.refl _

/-- EC's first `have` of `rw_ideal_2`: `Pr[SORO.Preimage(SORO_P1(A), RFList)] =
Pr[SORO.Preimage(SORO_P1(A), RFWhile)]` (`byequiv … call (rw_RF_List_While)`), one abstract call to
`SORO_P1(A)` (`soro_pre_game`).  Not an EC lemma. -/
theorem rl_game (A : SH.AdvPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ Log_m.footprint ⊔ RFList_m.footprint)ᶜ)
    (hfresh : LocalFresh Log_m RFList_m) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (Module.app SORO.Preimage (Module.pair (SORO_P1 Log_m A) (RFList RFList_m))).procedure
      (Module.app SORO.Preimage (Module.pair (SORO_P1 Log_m A) (RFWhile RFList_m))).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hRA : RFList_m.footprint ≤ ARestrictions.footprintᶜ := le_sup_right.trans hfresh.1
  have hLA : Log_m.footprint ≤ ARestrictions.footprintᶜ := le_sup_left.trans hfresh.1
  haveI : Lens.Disjoint SORO.Bounder.bounder RFList_m := Lens.disjoint_of_footprint_le_compl _ _
    ((Footprint.le_compl_comm _ _).mp
      (hRA.trans (Footprint.compl_antimono (by unfold ARestrictions.footprint; fp_sub))))
  obtain ⟨hP, hfp⟩ := SORO_P1_ec Log_m RFList_m A hA hfresh
  have hPL : FVP.fvP (SORO_P1 Log_m A) ≤ RFList_m.footprintᶜ := by
    refine hfp.trans (sup_le (hAd.trans (Footprint.compl_antimono le_sup_right)) (sup_le
      hfresh.2.1 ?_))
    refine (Footprint.le_compl_comm _ _).mp (hRA.trans (Footprint.compl_antimono ?_))
    simp only [soroG, Footprint.lens_pair]
    unfold ARestrictions.footprint
    fp_sub
  exact soro_pre_game RFList_m (· = ·) _ _ (SORO_P1 Log_m A) hP hPL (rl_init RFList_m)
    (rl_bget RFList_m)

/-- `local lemma rw_ideal &m`. -/
theorem rw_ideal (A : SH.AdvPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    (Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_P1Adv Log_m A))).procedure () m (fun r _ => r = true) : ℝ) ≤
      Procedure.Pr (Module.app SORO.Preimage (Module.pair (SORO_P1 Log_m A)
        (Module.app SORO.RF SORO.RO.RO))).procedure () m (fun r _ => r = true) := by
  rw [← Procedure.Pr_eq_of_prhlProc (a₁ := ()) (a₂ := ())
    (ri_game Log_m RFList_m A hA _hAd _hfresh) (fun r₁ g₁ r₂ g₂ h => by rw [h]) rfl]
  exact rw_ideal_2 Log_m RFList_m A hA _hAd _hfresh m

/-- `local lemma leq_ideal &m`. -/
theorem leq_ideal (A : SH.AdvPreimage) (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ Log_m.footprint ⊔
      RFList_m.footprint)ᶜ)
    (_hfresh : LocalFresh Log_m RFList_m) (m : VariableAssignment) :
    (Procedure.Pr (IdealGame (Module.app FSome BIRO.IRO.asF) (ODRestr
        (Dist_of_P1Adv Log_m A))).procedure () m (fun r _ => r = true) : ℝ) ≤
      ((sigma + 1 : ℤ) : ℝ) / (2 : ℝ) ^ size_out := by
  have hLA : Log_m.footprint ≤ ARestrictions.footprintᶜ := le_sup_left.trans _hfresh.1
  obtain ⟨hP, hfp⟩ := SORO_P1_ec Log_m RFList_m A hA _hfresh
  have hPd : FVP.fvP (SORO_P1 Log_m A) ≤
      ((SORO.RO.RO.m).footprint ⊔ SORO.Bounder.bounder.footprint)ᶜ := by
    refine hfp.trans (sup_le (_hAd.trans (Footprint.compl_antimono ?_)) (sup_le ?_ ?_))
    · unfold ARestrictions.footprint
      fp_sub
    · refine hLA.trans (Footprint.compl_antimono ?_)
      unfold ARestrictions.footprint
      fp_sub
    · simp only [soroG, Footprint.lens_pair]
      fp_disjoint
  have h1 := rw_ideal Log_m RFList_m A hA _hAd _hfresh m
  have h2 := SecureORO.RO_is_preimage_resistant (List Bool) f_out dout sigma clone_increase_counter
    SORO.RO.RO.m SORO.Bounder.bounder (Footprint.FinitelySupported.globalVar _)
    (Footprint.FinitelySupported.globalVar _) SORO.axioms (SORO_P1 Log_m A) hP hPd m
  rw [doutE1 default] at h2
  rw [div_eq_mul_inv]
  exact h1.trans h2

/-- The variables of `rw_real`'s invariant: `SH.Bounder.bounder` (left), `Counter.c` and `Log.m`
(right). -/
noncomputable def rrL [Lens.Disjoint Counter.c Log_m] [Lens.Disjoint SH.Bounder.bounder Log_m] :
    Lens (ℤ × ℤ × FMap (List Bool × ℤ) Bool) VariableAssignment :=
  Lens.pair SH.Bounder.bounder (Lens.pair Counter.c Log_m)

/-- EC's `Bounder.bounder{1} = Counter.c{2}`, on the contents of `rrL`. -/
def rrI (v₁ v₂ : ℤ × ℤ × FMap (List Bool × ℤ) Bool) : Prop := v₁.1 = v₂.2.1

section
variable [Lens.Disjoint Counter.c Log_m] [Lens.Disjoint SH.Bounder.bounder Log_m]

@[simp] theorem rrL_get (g : VariableAssignment) :
    (rrL Log_m).get g = (SH.Bounder.bounder.get g, Counter.c.get g, Log_m.get g) := rfl

theorem rrL_footprint : (rrL Log_m).footprint =
    SH.Bounder.bounder.footprint ⊔ (Counter.c.footprint ⊔ Log_m.footprint) := by
  simp only [rrL, Footprint.lens_pair]

/-- A write of `SH.Bounder.bounder` keeps a state equal to itself outside `rrL`. -/
theorem rrL_bounder (g : VariableAssignment) (v : ℤ) :
    (rrL Log_m).equal_outside g (SH.Bounder.bounder.set v g) :=
  (Lens.equal_outside_set_self _ g v).pair_left

/-- A write of `Counter.c` keeps a state equal to itself outside `rrL`. -/
theorem rrL_Counter (g : VariableAssignment) (v : ℤ) :
    (rrL Log_m).equal_outside g (Counter.c.set v g) :=
  ((Lens.equal_outside_set_self _ g v).pair_left).pair_right

/-- A write of `Log.m` keeps a state equal to itself outside `rrL`. -/
theorem rrL_Log (g : VariableAssignment) (v : FMap (List Bool × ℤ) Bool) :
    (rrL Log_m).equal_outside g (Log_m.set v g) :=
  ((Lens.equal_outside_set_self _ g v).pair_right).pair_right

end

section
variable [Lens.Disjoint Counter.c Log_m] [Lens.Disjoint SH.Bounder.bounder Log_m]

/-- EC's `proc; inline*; sp; if; auto` on `PBounder(PSome(Perm)).f ~ OPC(PSome(Perm)).f` in
`rw_real`'s `call`.  Not an EC lemma. -/
theorem rr_Pf (hP : FVP.fvP (OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ)
      (List Bool) (PSome Perm)) ≤ ((rrL Log_m).footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ (rrL Log_m).equal_outside g₁ g₂ ∧
        rrI ((rrL Log_m).get g₁) ((rrL Log_m).get g₂))
      (OptionIndifferentiability.OPRIMITIVE.f state (List Bool) f_out
        (Module.app (SecureHash.PBounder (List Bool) f_out state sigma SH.Bounder.bounder)
          (PSome Perm))).procedure
      (OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
        (Module.app OPC (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool × ℤ) (List Bool)
          { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
              (PSome Perm),
            fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
              (PSome Perm) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ (rrL Log_m).equal_outside g₁ g₂ ∧
        rrI ((rrL Log_m).get g₁) ((rrL Log_m).get g₂)) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [OptionIndifferentiability.ODPRIMITIVE.f.mk_simp]
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §o{2} ∧
      (rrL Log_m).equal_outside §allGlobals{1} §allGlobals{2} ∧
      rrI ((rrL Log_m).get §allGlobals{1}) ((rrL Log_m).get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  equiv_if
  case guard =>
    rintro g₁ g₂ _ _ _ _ ⟨-, -, -, hI⟩
    change SH.Bounder.bounder.get g₁ = Counter.c.get g₂ at hI
    rw [hI]
    simp only [sigma, decide_eq_decide]
    omega
  case «else» =>
    equiv_skip
    rintro g₁ g₂ _ _ _ _ ⟨⟨-, hy, he, hI⟩, -⟩
    exact ⟨hy, he, hI⟩
  case «then» =>
    stmt_wp
    equiv_call (prhlProc_self_equal_outside_module (rrL Log_m) _ hP rrI)
    equiv_skip
    rintro g₁ g₂ _ _ _ _ ⟨⟨rfl, -, he, hI⟩, -⟩
    refine ⟨⟨rfl, he, hI⟩, fun r g₁' _ g₂' ⟨rfl, he', hI'⟩ => ⟨rfl, ?_, ?_⟩⟩
    · exact (rrL_bounder Log_m g₁' _).symm.trans (he'.trans (rrL_Counter Log_m g₂' _))
    · change SH.Bounder.bounder.get g₁' = Counter.c.get g₂' at hI'
      change SH.Bounder.bounder.get (SH.Bounder.bounder.set _ g₁') =
        Counter.c.get (Counter.c.set _ g₂')
      rw [SH.Bounder.bounder.set_get, Counter.c.set_get, hI']


/-- EC's `proc; inline*; sp; if; auto` on `PBounder(PSome(Perm)).fi ~ OPC(PSome(Perm)).fi` in
`rw_real`'s `call`.  Not an EC lemma. -/
theorem rr_Pfi (hP : FVP.fvP (OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ)
      (List Bool) (PSome Perm)) ≤ ((rrL Log_m).footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ (rrL Log_m).equal_outside g₁ g₂ ∧
        rrI ((rrL Log_m).get g₁) ((rrL Log_m).get g₂))
      (OptionIndifferentiability.OPRIMITIVE.fi state (List Bool) f_out
        (Module.app (SecureHash.PBounder (List Bool) f_out state sigma SH.Bounder.bounder)
          (PSome Perm))).procedure
      (OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
        (Module.app OPC (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool × ℤ) (List Bool)
          { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
              (PSome Perm),
            fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
              (PSome Perm) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ (rrL Log_m).equal_outside g₁ g₂ ∧
        rrI ((rrL Log_m).get g₁) ((rrL Log_m).get g₂)) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §o{2} ∧
      (rrL Log_m).equal_outside §allGlobals{1} §allGlobals{2} ∧
      rrI ((rrL Log_m).get §allGlobals{1}) ((rrL Log_m).get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  equiv_if
  case guard =>
    rintro g₁ g₂ _ _ _ _ ⟨-, -, -, hI⟩
    change SH.Bounder.bounder.get g₁ = Counter.c.get g₂ at hI
    rw [hI]
    simp only [sigma, decide_eq_decide]
    omega
  case «else» =>
    equiv_skip
    rintro g₁ g₂ _ _ _ _ ⟨⟨-, hy, he, hI⟩, -⟩
    exact ⟨hy, he, hI⟩
  case «then» =>
    stmt_wp
    equiv_call (prhlProc_self_equal_outside_module (rrL Log_m) _ hP rrI)
    equiv_skip
    rintro g₁ g₂ _ _ _ _ ⟨⟨rfl, -, he, hI⟩, -⟩
    refine ⟨⟨rfl, he, hI⟩, fun r g₁' _ g₂' ⟨rfl, he', hI'⟩ => ⟨rfl, ?_, ?_⟩⟩
    · exact (rrL_bounder Log_m g₁' _).symm.trans (he'.trans (rrL_Counter Log_m g₂' _))
    · change SH.Bounder.bounder.get g₁' = Counter.c.get g₂' at hI'
      change SH.Bounder.bounder.get (SH.Bounder.bounder.set _ g₁') =
        Counter.c.get (Counter.c.set _ g₂')
      rw [SH.Bounder.bounder.set_get, Counter.c.set_get, hI']

end

section
variable [Lens.Disjoint Counter.c Log_m] [Lens.Disjoint SH.Bounder.bounder Log_m]

/-- EC's `proc; inline*; sp; if; auto; sp; …; sim` on `FBounder(OSponge(PSome(Perm))).f ~
DFSetSize(OFC(FSome(Sponge(Poget(PSome(Perm)))))).f` in `rw_real`'s `call` (and its last call).
Not an EC lemma. -/
theorem rr_F (hF : FVP.fvP (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ)
      (List Bool) (Module.app FSome (Module.app Sponge.Sponge (Module.app Poget
        (OptionIndifferentiability.OPRIMITIVE.view state (List Bool × ℤ) (List Bool)
          (PSome Perm)))))) ≤ ((rrL Log_m).footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ (rrL Log_m).equal_outside g₁ g₂ ∧
        rrI ((rrL Log_m).get g₁) ((rrL Log_m).get g₂))
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
        (Module.app (SecureHash.FBounder (List Bool) f_out state sigma clone_increase_counter
          SH.Bounder.bounder)
          (Module.app FSetSize (Module.app FSome (Module.app Sponge.Sponge (Module.app Poget
            (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool) f_out
              { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool) f_out (PSome Perm),
                fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool) f_out
                  (PSome Perm) }))))))).procedure
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
        (Module.app DFSetSize
          (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool × ℤ) (List Bool)
            { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
                (Module.app OFC
                  (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool × ℤ) (List Bool)
                    { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ)
                        (List Bool) (Module.app FSome (Module.app Sponge.Sponge (Module.app Poget
                          (OptionIndifferentiability.OPRIMITIVE.view state (List Bool × ℤ)
                            (List Bool) (PSome Perm))))) })) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ (rrL Log_m).equal_outside g₁ g₂ ∧
        rrI ((rrL Log_m).get g₁) ((rrL Log_m).get g₂)) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp]
  stmt_inline{2} 0
  simp only [OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp]
  stmt_inline{1} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §l{2} ∧ §k{2} = size_out ∧
      §(localVarLens "y" (Option f_out)){1} = none ∧ §o{2} = none ∧
      (rrL Log_m).equal_outside §allGlobals{1} §allGlobals{2} ∧
      rrI ((rrL Log_m).get §allGlobals{1}) ((rrL Log_m).get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ ⟨rfl, he, hI⟩
    exact ⟨rfl, he, hI⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ _ _ _ _ _ ⟨rfl, rfl, -, -, -, hI⟩
    change SH.Bounder.bounder.get g₁ = Counter.c.get g₂ at hI
    rw [hI]
    rfl
  case «else» =>
    equiv_skip
    rintro g₁ g₂ _ _ _ _ _ ⟨⟨-, -, rfl, rfl, he, hI⟩, -⟩
    exact ⟨by simp, he, hI⟩
  case «then» =>
    refine prhlStmt_fix_left (fun σ => (localVarLens "x0" (List Bool)).get σ) fun q => ?_
    stmt_wp
    equiv_call (prhlProc_self_equal_outside_module (rrL Log_m) _ hF
      (fun v₁ v₂ => v₁.1 = clone_increase_counter v₂.2.1 q))
    stmt_wp
    equiv_skip
    rintro g₁ g₂ x0 y l k o ⟨⟨⟨rfl, rfl, -, -, he, hI⟩, -⟩, rfl⟩
    change SH.Bounder.bounder.get g₁ = Counter.c.get g₂ at hI
    refine ⟨⟨rfl, (rrL_bounder Log_m g₁ _).symm.trans he, ?_⟩, ?_⟩
    · change SH.Bounder.bounder.get (SH.Bounder.bounder.set _ g₁) = _
      rw [SH.Bounder.bounder.set_get, hI]
      rfl
    · rintro r₁ g₁' r₂ g₂' ⟨rfl, he', hJ⟩
      change SH.Bounder.bounder.get g₁' = clone_increase_counter (Counter.c.get g₂') x0 at hJ
      refine ⟨rfl, he'.trans (rrL_Counter Log_m g₂' _), ?_⟩
      change SH.Bounder.bounder.get g₁' = Counter.c.get (Counter.c.set _ g₂')
      rw [Counter.c.set_get, hJ]
      rfl

end

set_option maxHeartbeats 4000000 in
-- `fp_module` through the adversary's oracles
/-- `Dist_of_P1Adv(A)` touches `A`'s variables and `Log.m`.  Not an EC lemma. -/
theorem fvP_Dist_of_P1Adv (A : SH.AdvPreimage) :
    FVP.fvP (Dist_of_P1Adv Log_m A) ≤ FVP.fvP A ⊔ Log_m.footprint := by
  fp_module Log_m

/-- `DFSetSize(F).f` is lossless when `F.f` is (EC: `proc; inline*; auto; call Hf; auto`). -/
theorem DFSetSize_f_ll (F : ODFUNCTIONALITY)
    (hF : (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
      F).procedure.IsLossless) :
    (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
      (Module.app DFSetSize F)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hF ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 5
  phoare_simp [hF]
  phoare_skip
  simp

/-- EC's `move=> F P Hp Hpi Hf; proc; inline*; sp; auto; call Hf; auto; call (A_ll (DFSetSize(F)) P
_ Hp Hpi); auto`: `Dist_of_P1Adv(A)` is lossless for lossless oracles. -/
theorem Dist_of_P1Adv_ll (A : SH.AdvPreimage) (hll : A_lossless A) (F : ODFUNCTIONALITY)
    (P : ODPRIMITIVE)
    (hp : (OptionIndifferentiability.ODPRIMITIVE.f state (List Bool × ℤ) (List Bool)
      P).procedure.IsLossless)
    (hpi : (OptionIndifferentiability.ODPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
      P).procedure.IsLossless)
    (hf : (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
      F).procedure.IsLossless) :
    (Module.app (Dist_of_P1Adv Log_m A) (Module.pair F P)).procedure.IsLossless := by
  have hD := DFSetSize_f_ll F hf
  have hA := hll (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool) f_out
      { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool) f_out
          (Module.app DFSetSize F) }) P
    (by simpa only [OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp] using hD) hp hpi
  have hdout := (is_lossless_iff_expected _).mp Params.dout_ll
  rw [Procedure.isLossless_iff_phoareProc] at hA hD ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 6
  phoare_simp [hA, hD]
  phoare_skip
  intro _
  exact hdout

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
  have hLA : Log_m.footprint ≤ ARestrictions.footprintᶜ := le_sup_left.trans _hfresh.1
  haveI : Lens.Disjoint Counter.c Log_m := Lens.disjoint_of_footprint_le_compl _ _
    ((Footprint.le_compl_comm _ _).mp (hLA.trans (Footprint.compl_antimono (by
      unfold ARestrictions.footprint; fp_sub))))
  haveI : Lens.Disjoint SH.Bounder.bounder Log_m := Lens.disjoint_of_footprint_le_compl _ _
    ((Footprint.le_compl_comm _ _).mp (hLA.trans (Footprint.compl_antimono (by
      unfold ARestrictions.footprint; fp_sub))))
  have hAL : FVP.fvP A ≤ ((rrL Log_m).footprint)ᶜ := by
    rw [rrL_footprint]
    refine _hAd.trans (Footprint.compl_antimono ?_)
    unfold ARestrictions.footprint
    fp_sub
  have hPerm : (Perm.m).footprint ⊔ (Perm.mi).footprint ≤ ((rrL Log_m).footprint)ᶜ := by
    rw [rrL_footprint]
    refine (Footprint.le_compl_comm _ _).mpr (sup_le (by fp_disjoint) (sup_le (by fp_disjoint) ?_))
    exact hLA.trans (Footprint.compl_antimono (by unfold ARestrictions.footprint; fp_sub))
  have hF : FVP.fvP (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ)
      (List Bool) (Module.app FSome (Module.app Sponge.Sponge (Module.app Poget
        (OptionIndifferentiability.OPRIMITIVE.view state (List Bool × ℤ) (List Bool)
          (PSome Perm)))))) ≤ ((rrL Log_m).footprint)ᶜ :=
    le_trans (by fp_le) hPerm
  have hPf : FVP.fvP (OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ)
      (List Bool) (PSome Perm)) ≤ ((rrL Log_m).footprint)ᶜ :=
    le_trans (by fp_le) hPerm
  have hPfi : FVP.fvP (OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ)
      (List Bool) (PSome Perm)) ≤ ((rrL Log_m).footprint)ᶜ :=
    le_trans (by fp_le) hPerm
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ g₁ r₂ g₂ h => by rw [h]) rfl
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  simp only [PSome_init, PSome_init']
  erw [OSponge_app]
  repeat stmt_inline{1} 1
  repeat stmt_inline{2} 1
  stmt_wp
  stmt_swap{1} 1 10
  equiv_seq 2 2 : (§hash{1} = §hash{2} ∧
      (rrL Log_m).equal_outside §allGlobals{1} §allGlobals{2} ∧
      rrI ((rrL Log_m).get §allGlobals{1}) ((rrL Log_m).get §allGlobals{2}))
  · equiv_rnd
    stmt_wp
    equiv_call (prhlProc_refl
      (Indifferentiability.PRIMITIVE.init (block × capacity) (List Bool × ℤ) (List Bool)
        Perm).procedure)
    stmt_wp
    equiv_skip
    rintro σ₁ σ₂ h
    refine ⟨h, fun _ g₁ _ g₂ hg => ?_⟩
    subst hg
    intro _ _
    refine ⟨((rrL_bounder Log_m _ 0).trans (rrL_bounder Log_m _ 0)).symm.trans
      ((rrL_Counter Log_m _ 0).trans (rrL_Log Log_m _ _)), ?_⟩
    change SH.Bounder.bounder.get (SH.Bounder.bounder.set 0 _) =
      Counter.c.get (Log_m.set _ (Counter.c.set 0 _))
    rw [SH.Bounder.bounder.set_get,
      @Lens.get_of_disjoint_set _ _ _ Counter.c Log_m (‹Lens.Disjoint Counter.c Log_m›.symm),
      Counter.c.set_get]
  equiv_seq 1 1 : (§m{1} = §m{2} ∧ §hash{1} = §hash{2} ∧
      (rrL Log_m).equal_outside §allGlobals{1} §allGlobals{2} ∧
      rrI ((rrL Log_m).get §allGlobals{1}) ((rrL Log_m).get §allGlobals{2}))
  swap
  · equiv_call (rr_F Log_m hF)
    equiv_skip
    rintro g₁ g₂ m₁ hash₁ m₂ hash₂ ⟨hm, hh, he, hI⟩
    exact ⟨⟨hm, he, hI⟩, fun r₁ _ r₂ _ h => by rw [h.1, hh]⟩
  stmt_split{1} 1
  stmt_split{2} 1
  refine prhlStmt_seq_call (prhlProc_abstract_call_equal_outside_module
    (rrL Log_m) A SH.OIndif.distExt hA.1 hAL rrI ?hc _ _ ?horacle) ?_
  case hc =>
    intro _ n
    cases n with
    | zero => exact inferInstanceAs (Countable (List Bool))
    | succ n => cases n with
      | zero => exact inferInstanceAs (Countable (block × capacity))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable (block × capacity))
        | succ n => nomatch n
  case horacle =>
    intro _ n
    cases n with
    | zero =>
      simp only [OptionIndifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
        Module.fst_pair, Module.snd_pair, OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
        OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
        OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
      exact rr_F Log_m hF
    | succ n => cases n with
      | zero =>
        simp only [OptionIndifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
          HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
          OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
          OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
          OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
        erw [OptionIndifferentiability.ODPRIMITIVE.f.mk_simp]
        exact rr_Pf Log_m hPf
      | succ n => cases n with
        | zero =>
          simp only [OptionIndifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
            OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
            OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
            OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
          erw [OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
          exact rr_Pfi Log_m hPfi
        | succ n => nomatch n
  equiv_skip
  rintro σ₁ σ₂ ⟨hh, he, hI⟩
  refine ⟨⟨hh, he, hI⟩, fun r₁ g₁ r₂ g₂ ⟨hr, he', hI'⟩ => ?_⟩
  simp_reads
  exact ⟨hr, hh, he', hI'⟩

end Preimage

/-- `OGReal(CSome(Sponge), PSome(Perm))` is
`OIndif(FSome(Sponge(Poget(PSome(Perm)))), PSome(Perm))`. -/
theorem OGReal_eq (D : ODISTINGUISHER) :
    OGReal (CSome Sponge.Sponge) (PSome Perm) D =
      Module.app OIndif.OIndif (Module.pair
        (Module.app FSome (Module.app Sponge.Sponge (Module.app Poget
          (OptionIndifferentiability.OPRIMITIVE.view state (List Bool × ℤ) (List Bool)
              (PSome Perm)))))
        (Module.pair (PSome Perm) D)) := by
  unfold OIndif.OGReal OptionIndifferentiability.OGReal CSome
  erw [Module.app_comp, Module.app_comp]

/-- EC's `Sponge_preimage_resistant (A <: SH.AdvPreimage {…}) &m`, with `AGext0Fresh A`
(exception E13).  EC: `move=> A_ll; rewrite (rw_real &m); have := SHA3OIndiff (Dist_of_P1Adv(A)) &m
_; …; have/#:=leq_ideal &m`.  The sections' local variables `Log.m`, `RFList.m` are chosen fresh
(`Footprint.exists_fresh_glob`, exception E6). -/
theorem Sponge_preimage_resistant (A : SH.AdvPreimage)
    (hA : Module.ECModule A SH.OIndif.distExt)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint)ᶜ) (_hG : AGext0Fresh A)
    (m : VariableAssignment) :
    A_lossless A →
    (Procedure.Pr (Module.app SH.Preimage (Module.pair A (Module.pair OSponge
        (PSome Perm)))).procedure
        () m (fun r _ => r = true) : ℝ) ≤
      bound + ((sigma + 1 : ℤ) : ℝ) / (2 : ℝ) ^ size_out := by
  intro hll
  have hAfs := hA.2
  have hSL : (FVP.fvP (Gconcl_list.SimLast Gconcl.S)).FinitelySupported := SimLast_ECModule.2
  obtain ⟨Log_m, hL1, hL2, hLfs⟩ := Footprint.exists_fresh_glob (FMap (List Bool × ℤ) Bool)
    (hSL.sup OSimulator_fs) ((hAfs.sup ARestrictions_fs).sup Gext0Vars_fs)
  obtain ⟨RFList_m, hR, -⟩ := Footprint.exists_fresh (FMap (List Bool) f_out)
    (((hSL.sup OSimulator_fs).sup ((hAfs.sup ARestrictions_fs).sup Gext0Vars_fs)).sup hLfs)
  -- what the fresh variables avoid
  have hLA : Log_m.footprint ≤ ARestrictions.footprintᶜ :=
    hL2.trans (Footprint.compl_antimono (le_sup_of_le_right (le_sup_of_le_left le_sup_right)))
  have hLAd : Log_m.footprint ≤ (FVP.fvP A)ᶜ :=
    hL2.trans (Footprint.compl_antimono (le_sup_of_le_right (le_sup_of_le_left le_sup_left)))
  have hLG : Log_m.footprint ≤ Gext0Vars.footprintᶜ :=
    hL2.trans (Footprint.compl_antimono (le_sup_of_le_right le_sup_right))
  have hRA : RFList_m.footprint ≤ ARestrictions.footprintᶜ :=
    hR.trans (Footprint.compl_antimono
      (le_sup_of_le_left (le_sup_of_le_right (le_sup_of_le_left le_sup_right))))
  have hRAd : RFList_m.footprint ≤ (FVP.fvP A)ᶜ :=
    hR.trans (Footprint.compl_antimono
      (le_sup_of_le_left (le_sup_of_le_right (le_sup_of_le_left le_sup_left))))
  have hRL : RFList_m.footprint ≤ Log_m.footprintᶜ :=
    hR.trans (Footprint.compl_antimono le_sup_right)
  have hfresh : LocalFresh Log_m RFList_m :=
    ⟨sup_le hLA hRA, (Footprint.le_compl_comm _ _).mp hRL, hLfs⟩
  have hAd' : FVP.fvP A ≤ (ARestrictions.footprint ⊔ Log_m.footprint ⊔ RFList_m.footprint)ᶜ :=
    le_compl_sup (le_compl_sup _hAd ((Footprint.le_compl_comm _ _).mp hLAd))
      ((Footprint.le_compl_comm _ _).mp hRAd)
  -- the distinguisher of `SHA3OIndiff`
  have hDfp := Preimage.fvP_Dist_of_P1Adv Log_m A
  have hD : Module.ECModule (Preimage.Dist_of_P1Adv Log_m A) OIndif.distExt :=
    ⟨ODistinguisher_representable _, (hAfs.sup hLfs).mono hDfp⟩
  have hDd : ODistRestrictions (Preimage.Dist_of_P1Adv Log_m A) :=
    hDfp.trans (sup_le (A_ODistRestrictions A hAfs _hAd) (X_ODistRestrictions hLA hL1))
  have hDg : OGext0Fresh (Preimage.Dist_of_P1Adv Log_m A) :=
    hDfp.trans (sup_le _hG hLG)
  have h1 := SHA3OIndiff (Preimage.Dist_of_P1Adv Log_m A) hD hDd hDg m
    (fun F P hp hpi hf => Preimage.Dist_of_P1Adv_ll Log_m A hll F P hp hpi hf)
  have h2 := Preimage.leq_ideal Log_m RFList_m A hA hAd' hfresh m
  rw [Preimage.rw_real Log_m RFList_m A hA hAd' hfresh m, ← OGReal_eq]
  have h3 := (abs_sub_le_iff.mp h1).1
  have hb : SHA3Indiff.bound = bound := rfl
  change (Procedure.Pr (OGIdeal (Module.app FSome BIRO.IRO.asF) OSimulator
    (ODRestr (Preimage.Dist_of_P1Adv Log_m A))).procedure () m (fun r _ => r = true) : ℝ) ≤ _
    at h2
  linarith

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
