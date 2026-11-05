import GaudisCrypt.Examples.SHA3.SHA3Indiff
import GaudisCrypt.Examples.SHA3.IndifRO_is_secure
import GaudisCrypt.Lib.EC.DList
import GaudisCrypt.Lib.EC.ListRange
import GaudisCrypt.Logic.PRHLTransitivity

/-!
# Top-level proof of SHA-3 security (EasyCrypt `proof/SHA3Security.ec`)

Preimage, second-preimage and collision resistance of the sponge with outputs of `size_out` bits
(`CSetSize(Sponge)`), against adversaries making `sigma` queries: `IndifRO_is_secure` applied to
`SHA3Indiff`.  `SHA3_coll_resistant` is the collision resistance of `SHA3`'s padding.

Translation notes (see `notes/SHA3/README.md`):
* The file-level abstract type `f_out`, operators `size_out`, `sigma`, `dout`, `to_list`,
  `of_list` and their axioms are the parameter class `Params` (as `Common.Params`).
* `clone import IndifRO_is_secure as S with …` is the namespace `S` of abbreviations, opened.  The
  clone declares its module variables (`S.SRO.RO.RO.m` …); its `realize`s are `S.axioms`.
* `CSetSize(F)(P)`, `FSetSize(F)` alias `init` and are applied to module parameters: the alias is
  wrapped in a call (exception E5), as is `DSetSize(D)(F)(P) = D(DFSetSize(F), P)`.
  `SimSetSize(S)(F) = S(FGetSize(F))` is `Module.comp S FGetSize`.
* The sections' local lemmas, repeated in each section, go into namespaces named after the sections
  (`Preimage.invmC` …).  Their `clone import Program as Prog` (`Prog2`, `Prog3`) are
  `DList.Program` at `bool`, `dbool`.
* `declare axiom A_ll` is the hypothesis `_A_ll` (`S.D_ll`).
-/

-- the clone `S.SRO.RO` contains the module `RO` (`S.SRO.RO.RO`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.SHA3Security

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.SLCommon.Prefix
open GaudisCrypt.SHA3.Sponge GaudisCrypt.SHA3.Sponge.BIRO GaudisCrypt.SHA3.SHA3Indiff

-- the last imports (`Sponge`, `SHA3Indiff`) win over `Common`'s and the root-level names
export GaudisCrypt.SHA3.SHA3Indiff (state PRIMITIVE limit)

variable [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params]

module SHA3 using (P : DPRIMITIVE) {
  proc init () : Unit {
    return ()
  };
  proc f (x : List Bool × ℤ) : (List Bool) {
    var bl : List Bool, n : ℤ, r : List Bool;
    bl, n <- $x;
    r <- call (Module.app Sponge.Sponge.f P) (($bl ++ [false, true], $n));
    return $r
  };
}

/-- EasyCrypt's file-level abstract type and operators, with their axioms: `op size_out` with
`size_out_gt0`, `op sigma` with `sigma_gt0`, `type f_out`, `op dout` with `dout_ll`, `dout_fu`,
`dout_full`, `op to_list`, `op of_list` with `spec_dout`, `spec2_dout`, `to_list_inj`, `to_listK`
and `dout_equal_dlist`. -/
class Params : Type 1 where
  size_out : ℤ
  size_out_gt0 : 0 < size_out
  sigma : ℤ
  sigma_gt0 : 0 < sigma
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
def sigma : ℤ := Params.sigma
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

-- EC's `CSetSize(F : CONSTRUCTION)(P : DPRIMITIVE)`, with `F` a Lean parameter so that
-- `CSetSize F` is a construction; its `proc init = F(P).init` is wrapped in a call (exception E5)
set_option linter.gaudisCrypt.using false in
module CSetSize (F : CONSTRUCTION) using (P : DPRIMITIVE)
    : (Indifferentiability.FUNCTIONALITY (block × capacity) (List Bool) f_out) {
  proc init () : Unit {
    _ <- call (Indifferentiability.FUNCTIONALITY.init (block × capacity) (List Bool × ℤ)
      (List Bool) (Module.app F P)) ();
    return ()
  };
  proc f (x : List Bool) : f_out {
    var r : List Bool;
    r <- call (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ)
      (List Bool) (Module.app F P)) (($x, size_out));
    return oget (of_list $r)
  };
}

-- EC's `FSetSize(F : FUNCTIONALITY)`; its `proc init = F.init` is wrapped in a call (exception E5)
module FSetSize using (F : FUNCTIONALITY)
    : (Indifferentiability.FUNCTIONALITY (block × capacity) (List Bool) f_out) {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (x : List Bool) : f_out {
    var r : List Bool;
    r <- call F.f (($x, size_out));
    return oget (of_list $r)
  };
}

/-- `fun c m => c + ((size m + 1) %/ r + 1) + max ((size_out + r - 1) %/ r - 1) 0`, the clone's
`increase_counter`. -/
def increase_counter (c : ℤ) (m : List Bool) : ℤ :=
  c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0

/-! ## `clone import IndifRO_is_secure as S with type block <- block * capacity,
type f_in <- bool list, type f_out <- f_out, op sampleto <- dout, op bound <- (limit ^ 2 - limit)%r
/ (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r, op limit <- sigma, op bound_counter <- limit,
op increase_counter <- …` -/

namespace S
/-- The clone's module variables. -/
global_var SRO.RO.RO.m : FMap (List Bool) f_out
global_var SRO.RO.FRO.m : FMap (List Bool) (f_out × PROM.flag)
global_var SRO.Counter.c : ℤ
global_var SRO.Bounder.bounder : ℤ
global_var DPre.h : f_out
global_var D2Pre.m2 : List Bool

namespace Indiff0
abbrev PRIMITIVE := Indifferentiability.PRIMITIVE (block × capacity) (List Bool) f_out
abbrev DPRIMITIVE := Indifferentiability.DPRIMITIVE (block × capacity) (List Bool) f_out
abbrev FUNCTIONALITY := Indifferentiability.FUNCTIONALITY (block × capacity) (List Bool) f_out
abbrev DFUNCTIONALITY := Indifferentiability.DFUNCTIONALITY (block × capacity) (List Bool) f_out
abbrev CONSTRUCTION := Indifferentiability.CONSTRUCTION (block × capacity) (List Bool) f_out
abbrev SIMULATOR := Indifferentiability.SIMULATOR (block × capacity) (List Bool) f_out
abbrev DISTINGUISHER := Indifferentiability.DISTINGUISHER (block × capacity) (List Bool) f_out
end Indiff0

namespace SRO
abbrev Oracle := SecureRO.Oracle (List Bool) f_out
noncomputable abbrev Oracle.ext := SecureRO.Oracle.ext (List Bool) f_out
abbrev AdvPreimage := SecureRO.AdvPreimage (List Bool) f_out
abbrev AdvSecondPreimage := SecureRO.AdvSecondPreimage (List Bool) f_out
abbrev AdvCollision := SecureRO.AdvCollision (List Bool) f_out
noncomputable abbrev Preimage := IndifRO_is_secure.SRO.Preimage (List Bool) f_out sigma limit
  increase_counter SRO.Counter.c SRO.Bounder.bounder
noncomputable abbrev SecondPreimage := IndifRO_is_secure.SRO.SecondPreimage (List Bool) f_out sigma
  limit increase_counter SRO.Counter.c SRO.Bounder.bounder
noncomputable abbrev Collision := IndifRO_is_secure.SRO.Collision (List Bool) f_out sigma limit
  increase_counter SRO.Counter.c SRO.Bounder.bounder
end SRO

noncomputable abbrev RO := IndifRO_is_secure.RO (block × capacity) (List Bool) f_out dout
  SRO.RO.RO.m
noncomputable abbrev FInit.get := IndifRO_is_secure.FInit.get (block × capacity) (List Bool) f_out
noncomputable abbrev FM.asRF := IndifRO_is_secure.FM.asRF (block × capacity) (List Bool) f_out
noncomputable abbrev FM.asRO := IndifRO_is_secure.FM.asRO (block × capacity) (List Bool) f_out

/-- The clone's `realize bound_counter_ge0`, `limit_gt0`, `sampleto_ll`, `sampleto_fu`,
`sampleto_full`, `increase_counter_spec`. -/
theorem axioms :
    IndifRO_is_secure.Axioms (List Bool) f_out dout sigma limit increase_counter where
  sampleto_ll := Params.dout_ll
  sampleto_fu := Params.dout_fu
  sampleto_full := Params.dout_full
  limit_gt0 := Params.sigma_gt0
  bound_counter_ge0 := SLCommon.max_ge0
  increase_counter_spec c m := by
    have hr := gt0_r
    have h1 : 0 ≤ (size m + 1) / r :=
      Int.ediv_nonneg (by unfold size; omega) hr.le
    unfold increase_counter
    have := le_max_right ((size_out + r - 1) / r - 1) 0
    omega
end S

open S

module FGetSize using (F : Indiff0.DFUNCTIONALITY) : DFUNCTIONALITY {
  proc f (xi : List Bool × ℤ) : (List Bool) {
    var x : List Bool, i : ℤ, r : f_out;
    x, i <- $xi;
    r <- call F.f ($x);
    return to_list $r
  };
}

/-- `module SimSetSize (S : SIMULATOR) (F : Indiff0.DFUNCTIONALITY) = S(FGetSize(F))`. -/
noncomputable def SimSetSize (S : SIMULATOR) : Indiff0.SIMULATOR := Module.comp S FGetSize

module DFSetSize using (F : DFUNCTIONALITY) : Indiff0.DFUNCTIONALITY {
  proc f (x : List Bool) : f_out {
    var r : List Bool;
    r <- call F.f (($x, size_out));
    return oget (of_list $r)
  };
}

-- EC's `(DSetSize (D : Indiff0.DISTINGUISHER) : DISTINGUISHER) (F) (P) = D(DFSetSize(F), P)`, with
-- `D` a Lean parameter; the alias is wrapped in a call (exception E5)
set_option linter.gaudisCrypt.using false in
module DSetSize (D : Indiff0.DISTINGUISHER) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    b <- call (Module.app D (Module.pair (Module.app DFSetSize F)
      (Indifferentiability.DPRIMITIVE.mk (block × capacity) (List Bool) f_out
        { f := Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool) P
          fi := Indifferentiability.DPRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
            P }))) ();
    return $b
  };
}

/-- The sections' restriction on `A`, `{-SRO.RO.RO, -SRO.RO.FRO, -SRO.Bounder, -Perm,
-Gconcl_list.BIRO2.IRO, -Simulator, -Cntr, -BIRO.IRO, -F.RO, -F.FRO, -Redo, -C, -Gconcl.S,
-BlockSponge.BIRO.IRO, -BlockSponge.C, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
-Gconcl_list.Simulator}`, without the per-section `-DPre`/`-D2Pre` (an abbreviation). -/
noncomputable def ARestrictions.footprint : Footprint VariableAssignment :=
  (SRO.RO.RO.m).footprint ⊔ (SRO.RO.FRO.m).footprint ⊔ SRO.Bounder.bounder.footprint ⊔
    SRO.Counter.c.footprint ⊔ (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
    (Gconcl_list.BIRO2.IRO.mp).footprint ⊔
    (Simulator.m).footprint ⊔ (Simulator.mi).footprint ⊔ (Simulator.paths).footprint ⊔
    Cntr.c.footprint ⊔ (BIRO.IRO.mp).footprint ⊔ (SLCommon.F.RO.m).footprint ⊔
    (SLCommon.F.FRO.m).footprint ⊔ (SLCommon.Redo.prefixes).footprint ⊔ SLCommon.C.footprint ⊔
    (Gconcl.S.m).footprint ⊔ (Gconcl.S.mi).footprint ⊔ (Gconcl.S.paths).footprint ⊔
    (BlockSponge.BIRO.IRO.mp).footprint ⊔ BlockSponge.C.c.footprint ⊔
    (Gconcl_list.F2.RO.m).footprint ⊔ (Gconcl_list.F2.FRO.m).footprint ⊔
    (Gconcl_list.Simulator.m).footprint ⊔ (Gconcl_list.Simulator.mi).footprint ⊔
    (Gconcl_list.Simulator.paths).footprint ⊔ (Gconcl_list.Simulator.unvalid_map).footprint

/-- The bound of `SHA3Indiff`, `(limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r +
(4 * limit ^ 2)%r / (2 ^ c)%r`, the clone's `bound`. -/
noncomputable abbrev bound : ℝ := SHA3Indiff.bound

/-- The section's ops `same_ro`, `same_ro2`: the map of `SRO.RO.RO` agrees with that of
`BIRO.IRO` on the first `size_out` bits. -/
def same_ro (m1 : FMap (List Bool) f_out) (m2 : FMap (List Bool × ℤ) Bool) : Prop :=
  (∀ m, FMap.dom m1 m → ∀ i, 0 ≤ i ∧ i < size_out → FMap.dom m2 (m, i)) ∧
  (∀ m, (∃ i, 0 ≤ i ∧ i < size_out ∧ FMap.dom m2 (m, i)) → FMap.dom m1 m) ∧
  (∀ m, FMap.dom m1 m →
    to_list (oget (FMap.get m1 m)) = (range 0 size_out).map fun i => oget (FMap.get m2 (m, i)))

def same_ro2 (m1 : FMap (List Bool) (List Bool)) (m2 : FMap (List Bool × ℤ) Bool) : Prop :=
  (∀ m, FMap.dom m1 m → ∀ i, 0 ≤ i ∧ i < size_out → FMap.dom m2 (m, i)) ∧
  (∀ m, (∃ i, 0 ≤ i ∧ i < size_out ∧ FMap.dom m2 (m, i)) → FMap.dom m1 m) ∧
  (∀ m, FMap.dom m1 m →
    oget (FMap.get m1 m) = (range 0 size_out).map fun i => oget (FMap.get m2 (m, i)))

/-- EC's `={glob Perm}`: `Perm.m` and `Perm.mi` agree (EasyCrypt's `glob Perm` is the module's
variables). -/
def eqPerm (g₁ g₂ : VariableAssignment) : Prop :=
  Perm.m.get g₁ = Perm.m.get g₂ ∧ Perm.mi.get g₁ = Perm.mi.get g₂

/-- The invariant of `equiv_sponge_perm`'s `call (: ={glob Perm} /\ invm Perm.m{1} Perm.mi{1})`,
with the counter `Cntr.c{2} = k` it frames. -/
def permInv (k : ℤ) (g₁ g₂ : VariableAssignment) : Prop :=
  Perm.m.get g₁ = Perm.m.get g₂ ∧ Perm.mi.get g₁ = Perm.mi.get g₂ ∧
    invm (Perm.m.get g₁) (Perm.mi.get g₁) ∧ Cntr.c.get g₂ = k

/-- `Perm.f`, through the distinguisher's view, is `RP.f`. -/
theorem Perm_f_eq : Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
    (Indifferentiability.PRIMITIVE.view (block × capacity) (List Bool × ℤ) (List Bool) Perm) =
    PRP.RP.RP.f (block × capacity) dD Perm.m Perm.mi := by
  rw [Indifferentiability.PRIMITIVE.view_f]
  unfold Perm PRP.RP.RP
  simp [Indifferentiability.PRIMITIVE.f, PRP.StrongPRP.PRP.mk]

/-- `Perm.f ~ Perm.f` keeps `permInv` (`invm_set`): the oracle premise of `equiv_sponge_perm`'s
`call`. -/
theorem Perm_f_perm (k : ℤ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ permInv k g₁ g₂)
      (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Indifferentiability.PRIMITIVE.view (block × capacity) (List Bool × ℤ) (List Bool)
          Perm)).procedure
      (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Indifferentiability.PRIMITIVE.view (block × capacity) (List Bool × ℤ) (List Bool)
          Perm)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ permInv k g₁ g₂) := by
  rw [Perm_f_eq]
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ permInv k §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, h⟩
    exact ⟨rfl, h⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ x _ ⟨rfl, hm, -, -⟩
    rw [hm]
  case «else» =>
    equiv_skip
    rintro g₁ g₂ x _ ⟨⟨rfl, hm, hmi, hinv⟩, -⟩
    exact ⟨by rw [hm], hm, hmi, hinv⟩
  case «then» =>
    stmt_wp
    equiv_rnd
    equiv_skip
    rintro g₁ g₂ x _ ⟨⟨rfl, hm, hmi, hinv, hc⟩, hg⟩
    refine ⟨by rw [hm], fun a ha => ?_⟩
    simp only [permInv]
    simp_reads
    refine ⟨by rw [hm], by rw [hm], by rw [hmi], ?_, hc⟩
    exact invm_set _ _ _ _ (by simpa using hg) (not_of_mem_support_dexcepted ha) hinv

/-- EC's `call (: I); inline*; while (…); …` on `Sponge(P).f ~ Sponge(P).f`: an invariant `I` kept
by `P.f` is kept by the sponge (both loops in lockstep).  Not an EC lemma. -/
theorem Sponge_f_inv (P : DPRIMITIVE) (I : VariableAssignment → VariableAssignment → Prop)
    (hPf : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ I g₁ g₂)
      (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool) P).procedure
      (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool) P).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ I g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ I g₁ g₂)
      (Module.app Sponge.f P).procedure (Module.app Sponge.f P).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ I g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 2 2 : (§n{1} = §n{2} ∧ §z{1} = §z{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧
      §i{1} = §i{2} ∧ §xs{1} = §xs{2} ∧ I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ ⟨rfl, hg⟩
    exact ⟨rfl, rfl, hg⟩
  equiv_seq 1 1 : (§n{1} = §n{2} ∧ §z{1} = §z{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧
      §i{1} = §i{2} ∧ I §allGlobals{1} §allGlobals{2})
  · equiv_while (§n{1} = §n{2} ∧ §z{1} = §z{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧
        §i{1} = §i{2} ∧ §xs{1} = §xs{2} ∧ I §allGlobals{1} §allGlobals{2})
    case body =>
      stmt_wp
      equiv_call hPf
      equiv_skip
      rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, hg⟩, -⟩
      exact ⟨⟨rfl, hg⟩, fun _ _ _ _ ⟨rfl, hg'⟩ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, hg'⟩⟩
    case guard => intros; simp_all
    case exit =>
      rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, -, hg⟩ -
      exact ⟨rfl, rfl, rfl, rfl, rfl, hg⟩
    · equiv_skip
      intros; simp_all
  · equiv_while (§n{1} = §n{2} ∧ §z{1} = §z{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧
        §i{1} = §i{2} ∧ I §allGlobals{1} §allGlobals{2})
    case body =>
      equiv_seq 1 1 : ((§n{1} = §n{2} ∧ §z{1} = §z{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧
        §i{1} = §i{2} ∧ I §allGlobals{1} §allGlobals{2}) ∧ §i{1} = §i{2})
      · stmt_wp
        equiv_skip
        intros; simp_all
      · equiv_if
        case guard => intros; simp_all
        case «then» =>
          equiv_call hPf
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, hg⟩, -⟩, -⟩
          exact ⟨⟨rfl, hg⟩, fun _ _ _ _ ⟨rfl, hg'⟩ => ⟨rfl, rfl, rfl, rfl, rfl, hg'⟩⟩
        case «else» => equiv_skip; intros; simp_all
    case guard => intros; simp_all
    case exit =>
      rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, hg⟩ -
      exact ⟨rfl, hg⟩
    · equiv_skip
      intros; simp_all

/-- `of_list` inverts `to_list` on lists of length `size_out` (`spec2_dout`, `to_listK`). -/
theorem to_list_oget_of_list (l : List Bool) (h : size l = size_out) :
    to_list (oget (of_list l)) = l := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (Params.spec2_dout l h)
  have := (Params.to_listK v l).mpr hv
  simp only [of_list, to_list, hv, oget, Option.getD_some]
  exact this

/-- The exit of `equiv_ro_iro`'s loops: `same_ro` after `SRO.RO.RO.m` gets the fresh `x0`, with the
bits the loop sampled for `x0` (EC's `progress` after the `conseq`). -/
theorem same_ro_set_fresh (m1 : FMap (List Bool) f_out) (mp mp2 : FMap (List Bool × ℤ) Bool)
    (x0 l0 : List Bool) (hs : same_ro m1 mp) (hdom : ¬ FMap.dom m1 x0)
    (h1 : ∀ l j, FMap.dom mp (l, j) → FMap.dom mp2 (l, j))
    (h2 : ∀ l j, FMap.dom mp (l, j) → FMap.get mp2 (l, j) = FMap.get mp (l, j))
    (h3 : ∀ l j, FMap.dom mp2 (l, j) → FMap.dom mp (l, j) ∨ (l = x0 ∧ 0 ≤ j ∧ j < size_out))
    (h4 : ∀ j, 0 ≤ j ∧ j < size_out → FMap.dom mp2 (x0, j))
    (hsz : size l0 = size_out)
    (hbs : l0 = (range 0 size_out).map fun j => oget (FMap.get mp2 (x0, j))) :
    same_ro (FMap.set m1 x0 (oget (of_list l0))) mp2 := by
  refine ⟨fun m' hm i hi => ?_, fun m' ⟨i, hi0, hi1, hi⟩ => ?_, fun m' hm => ?_⟩
  · rcases (FMap.mem_set _ _ _ _).mp hm with hm | rfl
    · exact h1 _ _ (hs.1 m' hm i hi)
    · exact h4 i hi
  · rcases h3 _ _ hi with h | ⟨rfl, -⟩
    · exact (FMap.mem_set _ _ _ _).mpr (Or.inl (hs.2.1 m' ⟨i, hi0, hi1, h⟩))
    · exact (FMap.mem_set _ _ _ _).mpr (Or.inr rfl)
  · by_cases hx : m' = x0
    · subst hx
      rw [FMap.get_set_sameE]
      simp only [oget, Option.getD_some]
      rw [show (Option.getD (of_list l0) default) = oget (of_list l0) from rfl,
        to_list_oget_of_list l0 hsz]
      exact hbs
    · rw [FMap.get_set_neqE _ _ _ _ hx]
      have hd : FMap.dom m1 m' := ((FMap.mem_set _ _ _ _).mp hm).resolve_right hx
      rw [hs.2.2 m' hd]
      refine List.map_congr_left fun i hi => ?_
      rw [h2 _ _ (hs.1 m' hd i ((mem_range 0 size_out i).mp hi))]

/-- `dout` is `dlist dbool size_out` read back by `of_list` (`dout_equal_dlist`, `to_listK`). -/
theorem dout_dlist : dout = (dlist dbool size_out).hbind fun l => pure (oget (of_list l)) := by
  refine SubProbability.ext_of_expected fun F => ?_
  rw [SubProbability.expected_hbind]
  change _ = (dlist dbool Params.size_out).expected _
  rw [← Params.dout_equal_dlist, SubProbability.expected_bind]
  simp only [expected_pure]
  refine congrArg (Params.dout.expected) (funext fun x => ?_)
  have := (Params.to_listK x (Params.to_list x)).mp rfl
  simp only [of_list, this, oget, Option.getD_some]

/-- The pre- and post-condition parts of the sections' `equiv_sponge_perm`, `equiv_ro_iro`
on the counter: `Cntr.c{2} = c /\ arg{2} = m /\ (Cntr.c + … <= limit){2}` (an abbreviation). -/
def counter_pre (c : ℤ) (m : List Bool) (arg : List Bool) (g₂ : VariableAssignment) : Prop :=
  Cntr.c.get g₂ = c ∧ arg = m ∧
    Cntr.c.get g₂ + ((size arg + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0 ≤ limit

/-- `FInit(CSetSize(Sponge, Perm)).get` and `FInit(DFSetSize(FC(Sponge(Perm)))).get`, the sides
of `equiv_sponge_perm` (abbreviations). -/
noncomputable def sponge_perm_left : procmod (List Bool) → f_out :=
  Module.app FInit.get (Indifferentiability.FUNCTIONALITY.view (block × capacity) (List Bool) f_out
    (Module.app (CSetSize Sponge.Sponge)
      (Indifferentiability.PRIMITIVE.view (block × capacity) (List Bool × ℤ) (List Bool) Perm)))

noncomputable def sponge_perm_right : procmod (List Bool) → f_out :=
  Module.app FInit.get (Module.app DFSetSize
    (Indifferentiability.FUNCTIONALITY.view (block × capacity) (List Bool × ℤ) (List Bool)
      (Module.app FC (Indifferentiability.FUNCTIONALITY.view (block × capacity) (List Bool × ℤ)
        (List Bool) (Module.app Sponge.Sponge
          (Indifferentiability.PRIMITIVE.view (block × capacity) (List Bool × ℤ) (List Bool)
            Perm))))))

/-- `FInit(RO).get` and `FInit(DFSetSize(FC(BIRO.IRO))).get`, the sides of `equiv_ro_iro`
(abbreviations). -/
noncomputable def ro_iro_left : procmod (List Bool) → f_out :=
  Module.app FInit.get (Indifferentiability.FUNCTIONALITY.view (block × capacity) (List Bool) f_out
    RO)

noncomputable def ro_iro_right : procmod (List Bool) → f_out :=
  Module.app FInit.get (Module.app DFSetSize
    (Indifferentiability.FUNCTIONALITY.view (block × capacity) (List Bool × ℤ) (List Bool)
      (Module.app FC (Indifferentiability.FUNCTIONALITY.view (block × capacity) (List Bool × ℤ)
        (List Bool) BIRO.IRO.asF))))

/-- `local equiv equiv_sponge_perm c m : FInit(CSetSize(Sponge, Perm)).get ~
FInit(DFSetSize(FC(Sponge(Perm)))).get : ={arg, glob Perm} /\ invm Perm.m{1} Perm.mi{1} /\
Cntr.c{2} = c /\ arg{2} = m /\ (…){2} ==> ={res, glob Perm} /\ invm Perm.m{1} Perm.mi{1} /\
Cntr.c{2} = c + …`, the statement shared by the three sections (an abbreviation). -/
def equiv_sponge_perm.statement (c : ℤ) (m : List Bool) : Prop :=
  prhlProc (sig₁ := procsig (List Bool) -> f_out) (sig₂ := procsig (List Bool) -> f_out)
    (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ eqPerm g₁ g₂ ∧ invm (Perm.m.get g₁) (Perm.mi.get g₁) ∧
      counter_pre c m a₂ g₂)
    sponge_perm_left.procedure sponge_perm_right.procedure
    (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eqPerm g₁ g₂ ∧ invm (Perm.m.get g₁) (Perm.mi.get g₁) ∧
      Cntr.c.get g₂ = c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0)

/-- `local equiv equiv_ro_iro c m : FInit(RO).get ~ FInit(DFSetSize(FC(BIRO.IRO))).get : ={arg} /\
same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ Cntr.c{2} = c /\ arg{2} = m /\ (…){2} ==> ={res} /\
same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ Cntr.c{2} = c + …`, the statement shared by the three
sections (an abbreviation). -/
def equiv_ro_iro.statement (c : ℤ) (m : List Bool) : Prop :=
  prhlProc (sig₁ := procsig (List Bool) -> f_out) (sig₂ := procsig (List Bool) -> f_out)
    (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ same_ro (SRO.RO.RO.m.get g₁) (BIRO.IRO.mp.get g₂) ∧
      counter_pre c m a₂ g₂)
    ro_iro_left.procedure ro_iro_right.procedure
    (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ same_ro (SRO.RO.RO.m.get g₁) (BIRO.IRO.mp.get g₂) ∧
      Cntr.c.get g₂ = c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0)

/-! ## The section `Preimage`, with `declare module A <: SRO.AdvPreimage {…, -DPre}` and
`declare axiom A_ll` (its local declarations in the namespace `Preimage`) -/

namespace Preimage

theorem invm_dom_rng (m mi : FMap state state) : invm m mi → FMap.dom m = FMap.rng mi := by
  intro h
  funext x
  apply propext
  rw [FMap.domE, FMap.rngE]
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hx
    exact ⟨v, (h x v).mp hv⟩
  · rintro ⟨a, ha⟩
    rw [(h x a).mpr ha]
    simp

theorem invmC' (m mi : FMap state state) : invm m mi → invm mi m :=
  fun h x y => (h y x).symm

theorem invmC (m mi : FMap state state) : invm m mi ↔ invm mi m :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

theorem useful (m mi : FMap state state) (a : state) :
    invm m mi → ¬ FMap.dom m a → is_lossless (dexcepted (dprod bdistr cdistr) (FMap.rng m)) :=
  fun _ h => EC.Strong_RP_RF.excepted_lossless state SLCommon.dstate ConcreteF.Switching.uD_uf_fu m
    ⟨a, h⟩

theorem equiv_sponge_perm (c : ℤ) (m : List Bool) : equiv_sponge_perm.statement c m := by
  unfold equiv_sponge_perm.statement
  unfold sponge_perm_left sponge_perm_right
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{2} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §bs{2} ∧ §n{2} = size_out ∧ eqPerm §allGlobals{1} §allGlobals{2} ∧
      invm §Perm.m{1} §Perm.mi{1} ∧ §Cntr.c{2} = c ∧ §bs{2} = m ∧
      c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0 ≤ limit)
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ a₁ a₂ ⟨rfl, hp, hinv, hc, rfl, hle⟩
    exact ⟨rfl, hp, hinv, hc, rfl, by rw [← hc]; exact hle⟩
  have hS := Sponge_f_inv (Indifferentiability.PRIMITIVE.view (block × capacity) (List Bool × ℤ)
    (List Bool) Perm) (permInv (c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0))
    (Perm_f_perm _)
  equiv_if{2}
  case «else» =>
    refine prhlStmt_pre prhlStmt_false ?_
    rintro g₁ g₂ ⟨⟨h1, h2, -, -, hc, h3, hle⟩, hg⟩
    simp only [decide_eq_false_iff_not] at hg
    rw [h2, h3, hc] at hg
    exact hg hle
  case «then» =>
    have e : ∀ P : DPRIMITIVE, Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ)
        (List Bool) (Module.app Sponge P) = Module.app Sponge.f P := fun P => by
      rw [Sponge.apply_simp]; exact Module.snd_pair _ _
    rw [Indifferentiability.FUNCTIONALITY.view_f, e]
    equiv_call hS
    stmt_wp
    equiv_skip
    rintro g₁ g₂ x0 bs n ⟨⟨rfl, rfl, ⟨hm, hmi⟩, hinv, hc, rfl, -⟩, -⟩
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · simp only [permInv]
      simp_reads
      exact ⟨hm, hmi, hinv, by rw [hc]⟩
    · rintro r₁ g₁' r₂ g₂' ⟨rfl, hm', hmi', hinv', hc'⟩
      exact ⟨rfl, ⟨hm', hmi'⟩, hinv', hc'⟩

/-- `clone import Program as Prog with type t <- bool, op d <- dbool`. -/
noncomputable abbrev Prog.LoopSnoc.sample := DList.Program.LoopSnoc.sample Bool dbool

theorem equiv_ro_iro (c : ℤ) (m : List Bool) : equiv_ro_iro.statement c m := by
  unfold equiv_ro_iro.statement ro_iro_left ro_iro_right
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §bs{2} ∧ §n{2} = size_out ∧ same_ro §S.SRO.RO.RO.m{1} §IRO.mp{2} ∧
      §Cntr.c{2} = c ∧ §bs{2} = m ∧
      c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0 ≤ limit)
  · stmt_wp
    equiv_skip
    rintro g a1 m1 a2 ⟨rfl, hs, hc, rfl, hle⟩
    exact ⟨rfl, hs, hc, rfl, by rw [← hc]; exact hle⟩
  equiv_if{2}
  case «else» =>
    refine prhlStmt_pre prhlStmt_false ?_
    rintro g₁ g₂ ⟨⟨-, h2, -, hc, h3, hle⟩, hg⟩
    simp only [decide_eq_false_iff_not] at hg
    rw [h2, h3, hc] at hg
    exact hg hle
  case «then» =>
    stmt_wp
    equiv_seq 1 1 : (§x2{2} = §x0{1} ∧ §n0{2} = size_out ∧ §i{2} = 0 ∧ §bs0{2} = [] ∧
        same_ro §S.SRO.RO.RO.m{1} §IRO.mp{2} ∧
        §Cntr.c{2} = c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0)
    · stmt_wp
      equiv_skip
      rintro x0 m1 bs n mp c2 ⟨⟨rfl, rfl, hs, rfl, rfl, -⟩, -⟩
      exact ⟨rfl, rfl, hs, rfl⟩
    equiv_if{2}
    case «else» =>
      refine prhlStmt_pre prhlStmt_false ?_
      rintro g₁ g₂ ⟨-, hg⟩
      simp [BIRO.valid, valid_toplevel] at hg
    case «then» =>
      equiv_case (FMap.dom §S.SRO.RO.RO.m{1} §x0{1})
      · equiv_while{2} (§x2{2} = §x0{1} ∧ §n0{2} = size_out ∧ FMap.dom §S.SRO.RO.RO.m{1} §x0{1} ∧
            0 ≤ §i{2} ∧ §i{2} ≤ size_out ∧ same_ro §S.SRO.RO.RO.m{1} §IRO.mp{2} ∧
            §bs0{2} = (range 0 §i{2}).map (fun j => oget (FMap.get §IRO.mp{2} (§x2{2}, j))) ∧
            §Cntr.c{2} = c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0)
          ((size_out - §i{2}).toNat)
        case lossless =>
          intro σ₁ σ _ _
          have h1 := (is_lossless_iff_expected _).mp dbool_ll
          simp [Stmt.ewp_seq, Stmt.ewp_assign, Stmt.ewp_ifThenElse, Stmt.ewp_sample, Stmt.ewp_skip,
            h1]
        case «variant» =>
          intro σ₁ k
          hoare_wp 3
          hoare_split 1
          refine hoare_seq (hoare_if_wp (At := fun _ => False) (fun _ h => h.elim)
            (hoare_skip_wp _)) ?_
          hoare_wp 2
          hoare_skip
          rintro x2 n0 i mp bs0 c1 ⟨⟨rfl, rfl, hdom, hi0, hile, hs, rfl, hc⟩, hg, hk⟩
          simp only [decide_eq_true_eq] at hg
          refine ⟨fun h => ?_, fun _ => ⟨⟨rfl, rfl, hdom, by omega, by omega, hs, ?_, hc⟩, by omega⟩⟩
          · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h
            exact h (hs.1 _ hdom i ⟨hi0, hg⟩)
          · rw [rangeSr 0 i hi0]
            simp only [rcons, List.map_append, List.map_cons, List.map_nil]
        case exit =>
          rintro x0 m1 r1 x2 n0 i mp bs0 c2 ⟨rfl, rfl, hdom, hi0, hile, hs, rfl, hc⟩ hg
          simp only [decide_eq_false_iff_not, not_lt] at hg
          have hi : i = size_out := by omega
          subst hi
          simp only [hdom, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
          refine ⟨?_, hs, hc⟩
          rw [← hs.2.2 x2 hdom]
          have := (Params.to_listK (oget (FMap.get m1 x2)) (Params.to_list (oget (FMap.get m1 x2)))).mp rfl
          simp only [of_list, to_list]
          rw [this]
          rfl
        · stmt_split{1} 1
          refine prhlStmt_seq_sample_left ?_
          equiv_skip
          rintro σ₁ x2 n0 i bs0 mp c2 ⟨⟨⟨rfl, rfl, rfl, rfl, hs, rfl⟩, -⟩, hdom⟩
          refine ⟨(is_lossless_iff_expected _).mp Params.dout_ll, fun a _ => ?_⟩
          simp_reads
          have h0 : (0 : ℤ) ≤ size_out := Params.size_out_gt0.le
          simp [hdom, hs, h0, range_geq]
      · have leg1 : equiv[ §allGlobals{1} = §allGlobals{2} ∧ §x0{1} = §x0{2} ==>
            §allGlobals{1} = §allGlobals{2} ∧ §x0{1} = §x0{2} ∧
              §(localVarLens "r" f_out){1} = §(localVarLens "r" f_out){2} ]
            { var x0 : List Bool; (localVarLens "r" f_out) <$ dout; } ~
            { var x0 : List Bool, l : List Bool;
              l <- call Prog.LoopSnoc.sample.procedure (size_out);
              (localVarLens "r" f_out) <- oget (of_list $l); } := by
          stmt_wp
          stmt_split{1} 1
          stmt_split{2} 1
          refine prhlStmt_seq_sample_run_map_right (x₂ := liftLens (localVarLens "l" (List Bool)))
            (fun _ _ => dlist dbool size_out) (fun l => oget (of_list l)) ?_
          equiv_skip
          intro τ₁ τ₂ hP
          refine ⟨?_, dout_dlist, fun _ _ => ?_⟩
          · refine (programDenotation_call_apply _ _ _ τ₂).trans ?_
            erw [DList.Program.LoopSnoc.sample_denotation]
            refine SubProbability.ext_of_expected fun F => ?_
            simp only [SubProbability.expected_hbind, expected_pure]
            rw [show ProgramState.globalL.set τ₂.globals τ₂ = τ₂ from ProgramState.globalL.get_set τ₂]
          · simp_reads
            exact ⟨hP.1, hP.2⟩
        refine prhlStmt.trans_left leg1 (fun _ => ⟨rfl, rfl⟩) ?_
        stmt_wp
        stmt_inline{1} 0
        stmt_wp
        refine prhlStmt_fix_right (fun σ => IRO.mp.get σ.globals) fun mp => ?_
        equiv_while (§x2{2} = §x0{1} ∧ §n0{2} = size_out ∧ §n{1} = size_out ∧ §i0{1} = §i{2} ∧
            0 ≤ §i{2} ∧ §i{2} ≤ size_out ∧ size §l0{1} = §i{2} ∧
            same_ro §S.SRO.RO.RO.m{1} mp ∧ ¬ FMap.dom §S.SRO.RO.RO.m{1} §x0{1} ∧
            (∀ l j, FMap.dom mp (l, j) → FMap.dom §IRO.mp{2} (l, j)) ∧
            (∀ l j, FMap.dom mp (l, j) → FMap.get §IRO.mp{2} (l, j) = FMap.get mp (l, j)) ∧
            (∀ l j, FMap.dom §IRO.mp{2} (l, j) →
              FMap.dom mp (l, j) ∨ (l = §x0{1} ∧ 0 ≤ j ∧ j < §i{2})) ∧
            (∀ j, 0 ≤ j ∧ j < §i{2} → FMap.dom §IRO.mp{2} (§x0{1}, j)) ∧
            §l0{1} = §bs0{2} ∧
            §bs0{2} = (range 0 §i{2}).map (fun j => oget (FMap.get §IRO.mp{2} (§x0{1}, j))) ∧
            §Cntr.c{2} = c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0)
        case body =>
          stmt_wp
          equiv_seq 1 1 : ((§x2{2} = §x0{1} ∧ §n0{2} = size_out ∧ §n{1} = size_out ∧ §i0{1} = §i{2} ∧
            0 ≤ §i{2} ∧ §i{2} ≤ size_out ∧ size §l0{1} = §i{2} ∧
            same_ro §S.SRO.RO.RO.m{1} mp ∧ ¬ FMap.dom §S.SRO.RO.RO.m{1} §x0{1} ∧
            (∀ l j, FMap.dom mp (l, j) → FMap.dom §IRO.mp{2} (l, j)) ∧
            (∀ l j, FMap.dom mp (l, j) → FMap.get §IRO.mp{2} (l, j) = FMap.get mp (l, j)) ∧
            (∀ l j, FMap.dom §IRO.mp{2} (l, j) →
              FMap.dom mp (l, j) ∨ (l = §x0{1} ∧ 0 ≤ j ∧ j < §i{2})) ∧
            (∀ j, 0 ≤ j ∧ j < §i{2} → FMap.dom §IRO.mp{2} (§x0{1}, j)) ∧
            §l0{1} = §bs0{2} ∧
            §bs0{2} = (range 0 §i{2}).map (fun j => oget (FMap.get §IRO.mp{2} (§x0{1}, j))) ∧
            §Cntr.c{2} = c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0) ∧ §i{2} < size_out ∧ §x3{2} = §x0{1} ∧ §n1{2} = §i{2})
          · stmt_wp
            equiv_skip
            rintro x0 n i0 l0 m1 x2 n0 i mp2 bs0 c2 ⟨hJ, hg⟩
            simp only [decide_eq_true_eq] at hg
            exact ⟨hJ, by rw [hJ.2.2.1, hJ.2.2.2.1] at hg; exact hg, hJ.1⟩
          equiv_if{2}
          case «else» =>
            refine prhlStmt_pre prhlStmt_false ?_
            rintro σ₁ σ₂ ⟨⟨⟨-, -, -, -, hi0, -, -, hs, hdom, -, -, h3, -⟩, hlt, hx3, hn1⟩, hg⟩
            simp only [Bool.not_eq_false', decide_eq_true_eq] at hg
            rw [hx3, hn1] at hg
            rcases h3 _ _ hg with h | ⟨-, -, h⟩
            · exact hdom (hs.2.1 _ ⟨_, hi0, hlt, h⟩)
            · omega
          case «then» =>
            stmt_wp
            equiv_rnd
            equiv_skip
            rintro x0 n i0 l0 m1 x2 n0 i mp2 bs0 c2 x3 n1
              ⟨⟨⟨hx2, hn0, hn, hii, hi0, hile, hsz, hs, hdom, h1, h2, h3, h4, hl, hbs, hc⟩, hlt, hx3,
                hn1⟩, hg⟩ a _
            subst x2 x3 n0 n i0 n1
            have hfresh : ¬ FMap.dom mp2 (x0, i) := by simpa using hg
            have hmp : ¬ FMap.dom mp (x0, i) := fun h => hdom (hs.2.1 _ ⟨i, hi0, hlt, h⟩)
            refine ⟨rfl, rfl, rfl, rfl, by omega, by omega, ?_, hs, hdom,
              fun l j h => (FMap.mem_set _ _ _ _).mpr (Or.inl (h1 l j h)), fun l j h => ?_,
              fun l j h => ?_, fun j hj => ?_, ?_, ?_, hc⟩
            · simp only [size, List.length_append, List.length_singleton] at hsz ⊢
              omega
            · have hne : (l, j) ≠ (x0, i) := fun e => hmp (e ▸ h)
              rw [FMap.get_set_neqE _ _ _ _ hne, h2 l j h]
            · rcases (FMap.mem_set _ _ _ _).mp h with h | h
              · rcases h3 l j h with h | ⟨rfl, hj0, hj⟩
                · exact Or.inl h
                · exact Or.inr ⟨rfl, hj0, by omega⟩
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                exact Or.inr ⟨rfl, hi0, by omega⟩
            · by_cases hji : j = i
              · subst hji
                exact (FMap.mem_set _ _ _ _).mpr (Or.inr rfl)
              · exact (FMap.mem_set _ _ _ _).mpr (Or.inl (h4 j ⟨hj.1, by omega⟩))
            · simp [rcons, oget, hl]
            · rw [rangeSr 0 i hi0]
              simp only [rcons, List.map_append, List.map_cons, List.map_nil, FMap.get_set_sameE]
              congr 1
              rw [hbs]
              refine List.map_congr_left fun j hj => ?_
              have hj' := (mem_range 0 i j).mp hj
              rw [FMap.get_set_neqE _ _ _ _ (fun e => by
                obtain ⟨-, e⟩ := Prod.mk.inj e; omega)]
        case guard =>
          rintro x0 n i0 l0 m1 x2 n0 i mp2 bs0 c2 ⟨rfl, rfl, rfl, rfl, -⟩
          rfl
        case exit =>
          rintro g x0 n i0 l0 x2 n0 i mp2 bs0 c2
            ⟨rfl, rfl, rfl, rfl, hi0, hile, hsz, hs, hdom, h1, h2, h3, h4, rfl, hbs, hc⟩ hg τ
            ⟨hτg, hτx, hτr⟩
          simp only [decide_eq_false_iff_not, not_lt] at hg
          have hi : i0 = size_out := by omega
          subst hi
          simp only [hτg, hτx, hτr, hdom, decide_false, Bool.not_false, if_true,
            FMap.get_set_sameE]
          refine ⟨rfl, same_ro_set_fresh _ mp _ _ _ hs hdom h1 h2 (fun l j h => ?_) h4 hsz hbs, hc⟩
          exact h3 l j h
        · stmt_wp
          equiv_skip
          rintro x0 m1 x2 n0 i bs0 mp2 c2 ⟨⟨⟨⟨rfl, rfl, rfl, rfl, hs, hc⟩, -⟩, hdom⟩, rfl⟩
          exact ⟨rfl, rfl, rfl, le_rfl, Params.size_out_gt0.le, rfl, hs, hdom, fun _ _ h => h,
            fun _ _ _ => rfl, fun _ _ h => Or.inl h, fun j hj => absurd hj.2 (by omega), rfl,
            by rw [range_geq 0 0 le_rfl]; rfl, hc⟩

end Preimage

/-- EC's `Sponge_preimage_resistant &m ha`, for the section's `A` and its axiom `A_ll`. -/
theorem Sponge_preimage_resistant (A : SRO.AdvPreimage)
    (hA : Module.ECModule A SRO.Oracle.ext)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ DPre.h.footprint)ᶜ)
    (_A_ll : IndifRO_is_secure.D_ll (List Bool) f_out A)
    (m : VariableAssignment) (ha : f_out) :
    DPre.h.get m = ha →
    (Procedure.Pr (Module.app SRO.Preimage
        (Module.pair A (FM.asRF (CSetSize Sponge.Sponge) Perm))).procedure ha m
        (fun r _ => r = true) : ℝ) ≤
      bound + ((sigma + 1 : ℤ) : ℝ) / (2 : ℝ) ^ size_out := by
  sorry

/-! ## The section `SecondPreimage`, with `declare module A <: SRO.AdvSecondPreimage
{…, -D2Pre}` and `declare axiom A_ll` (its local declarations in the namespace
`SecondPreimage`) -/

namespace SecondPreimage

theorem invm_dom_rng (m mi : FMap state state) : invm m mi → FMap.dom m = FMap.rng mi := by
  intro h
  funext x
  apply propext
  rw [FMap.domE, FMap.rngE]
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hx
    exact ⟨v, (h x v).mp hv⟩
  · rintro ⟨a, ha⟩
    rw [(h x a).mpr ha]
    simp

theorem invmC' (m mi : FMap state state) : invm m mi → invm mi m :=
  fun h x y => (h y x).symm

theorem invmC (m mi : FMap state state) : invm m mi ↔ invm mi m :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

theorem useful (m mi : FMap state state) (a : state) :
    invm m mi → ¬ FMap.dom m a → is_lossless (dexcepted (dprod bdistr cdistr) (FMap.rng m)) :=
  fun _ h => EC.Strong_RP_RF.excepted_lossless state SLCommon.dstate ConcreteF.Switching.uD_uf_fu m
    ⟨a, h⟩

/-- EC repeats the section's proof (`Preimage.equiv_sponge_perm`). -/
theorem equiv_sponge_perm (c : ℤ) (m : List Bool) : equiv_sponge_perm.statement c m :=
  Preimage.equiv_sponge_perm c m

/-- `clone import Program as Prog2 with type t <- bool, op d <- dbool`. -/
noncomputable abbrev Prog2.LoopSnoc.sample := DList.Program.LoopSnoc.sample Bool dbool

/-- EC repeats the section's proof (`Preimage.equiv_ro_iro`). -/
theorem equiv_ro_iro (c : ℤ) (m : List Bool) : equiv_ro_iro.statement c m :=
  Preimage.equiv_ro_iro c m

end SecondPreimage

/-- EC's `Sponge_second_preimage_resistant &m mess`, for the section's `A` and its axiom
`A_ll`. -/
theorem Sponge_second_preimage_resistant (A : SRO.AdvSecondPreimage)
    (hA : Module.ECModule A SRO.Oracle.ext)
    (_hAd : FVP.fvP A ≤ (ARestrictions.footprint ⊔ D2Pre.m2.footprint)ᶜ)
    (_A_ll : IndifRO_is_secure.D_ll (List Bool) f_out A)
    (m : VariableAssignment) (mess : List Bool) :
    D2Pre.m2.get m = mess →
    (Procedure.Pr (Module.app SRO.SecondPreimage
        (Module.pair A (FM.asRF (CSetSize Sponge.Sponge) Perm))).procedure mess m
        (fun r _ => r = true) : ℝ) ≤
      bound + ((sigma + 1 : ℤ) : ℝ) / (2 : ℝ) ^ size_out := by
  sorry

/-! ## The section `Collision`, with `declare module A <: SRO.AdvCollision {…}` and
`declare axiom A_ll` (its local declarations in the namespace `Collision`) -/

namespace Collision

theorem invm_dom_rng (m mi : FMap state state) : invm m mi → FMap.dom m = FMap.rng mi := by
  intro h
  funext x
  apply propext
  rw [FMap.domE, FMap.rngE]
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hx
    exact ⟨v, (h x v).mp hv⟩
  · rintro ⟨a, ha⟩
    rw [(h x a).mpr ha]
    simp

theorem invmC' (m mi : FMap state state) : invm m mi → invm mi m :=
  fun h x y => (h y x).symm

theorem invmC (m mi : FMap state state) : invm m mi ↔ invm mi m :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

theorem useful (m mi : FMap state state) (a : state) :
    invm m mi → ¬ FMap.dom m a → is_lossless (dexcepted (dprod bdistr cdistr) (FMap.rng m)) :=
  fun _ h => EC.Strong_RP_RF.excepted_lossless state SLCommon.dstate ConcreteF.Switching.uD_uf_fu m
    ⟨a, h⟩

/-- EC repeats the section's proof (`Preimage.equiv_sponge_perm`). -/
theorem equiv_sponge_perm (c : ℤ) (m : List Bool) : equiv_sponge_perm.statement c m :=
  Preimage.equiv_sponge_perm c m

/-- `clone import Program as Prog3 with type t <- bool, op d <- dbool`. -/
noncomputable abbrev Prog3.LoopSnoc.sample := DList.Program.LoopSnoc.sample Bool dbool

/-- EC repeats the section's proof (`Preimage.equiv_ro_iro`). -/
theorem equiv_ro_iro (c : ℤ) (m : List Bool) : equiv_ro_iro.statement c m :=
  Preimage.equiv_ro_iro c m

end Collision

/-- EC's `Sponge_coll_resistant &m`, for the section's `A` and its axiom `A_ll`. -/
theorem Sponge_coll_resistant (A : SRO.AdvCollision)
    (hA : Module.ECModule A SRO.Oracle.ext)
    (_hAd : FVP.fvP A ≤ ARestrictions.footprintᶜ)
    (_A_ll : IndifRO_is_secure.D_ll (List Bool) f_out A)
    (m : VariableAssignment) :
    (Procedure.Pr (Module.app SRO.Collision
        (Module.pair A (FM.asRO (CSetSize Sponge.Sponge) Perm))).procedure () m
        (fun r _ => r = true) : ℝ) ≤
      bound + ((sigma * (sigma - 1) + 2 : ℤ) : ℝ) / 2 / (2 : ℝ) ^ size_out := by
  sorry

module X using (F : SRO.Oracle) : SRO.Oracle {
  proc get (bl : List Bool) : f_out {
    var r : f_out;
    r <- call F.get ($bl ++ [false, true]);
    return $r
  };
}

-- EC's `AdvCollisionSHA3(A : SRO.AdvCollision)(F : SRO.Oracle)`, with `A` a Lean parameter so
-- that `AdvCollisionSHA3 A` is an `SRO.AdvCollision`
set_option linter.gaudisCrypt.using false in
module AdvCollisionSHA3 (A : SRO.AdvCollision) using (F : SRO.Oracle) {
  proc guess () : (List Bool × List Bool) {
    var m1 : List Bool, m2 : List Bool;
    m1, m2 <- call (Module.app A (Module.app X F)) ();
    return ($m1 ++ [false, true], $m2 ++ [false, true])
  };
}

/-! ## The section `SHA3_Collision`, with `declare module A <: SRO.AdvCollision {…}` and
`declare axiom A_ll` -/

/-- EC's `SHA3_coll_resistant &m`, for the section's `A` and its axiom `A_ll`. -/
theorem SHA3_coll_resistant (A : SRO.AdvCollision)
    (hA : Module.ECModule A SRO.Oracle.ext)
    (_hAd : FVP.fvP A ≤ ARestrictions.footprintᶜ)
    (_A_ll : IndifRO_is_secure.D_ll (List Bool) f_out A)
    (m : VariableAssignment) :
    (Procedure.Pr (Module.app SRO.Collision
        (Module.pair (AdvCollisionSHA3 A) (FM.asRO (CSetSize Sponge.Sponge) Perm))).procedure ()
        m (fun r _ => r = true) : ℝ) ≤
      bound + ((sigma * (sigma - 1) + 2 : ℤ) : ℝ) / 2 / (2 : ℝ) ^ size_out := by
  sorry

end GaudisCrypt.SHA3.SHA3Security
