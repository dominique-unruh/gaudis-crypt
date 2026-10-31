import GaudisCrypt.Examples.SHA3.SHA3Indiff
import GaudisCrypt.Examples.SHA3.IndifRO_is_secure
import GaudisCrypt.Lib.EC.DList

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
  sorry

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
    IndifRO_is_secure.Axioms (List Bool) f_out dout sigma limit increase_counter := by
  sorry
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
    (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ (Gconcl_list.BIRO2.IRO.mp).footprint ⊔
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
    (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ eqGlob Perm g₁ g₂ ∧ invm (Perm.m.get g₁) (Perm.mi.get g₁) ∧
      counter_pre c m a₂ g₂)
    sponge_perm_left.procedure sponge_perm_right.procedure
    (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eqGlob Perm g₁ g₂ ∧ invm (Perm.m.get g₁) (Perm.mi.get g₁) ∧
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
  sorry

theorem invmC' (m mi : FMap state state) : invm m mi → invm mi m := by
  sorry

theorem invmC (m mi : FMap state state) : invm m mi ↔ invm mi m := by
  sorry

theorem useful (m mi : FMap state state) (a : state) :
    invm m mi → ¬ FMap.dom m a → is_lossless (dexcepted (dprod bdistr cdistr) (FMap.rng m)) := by
  sorry

theorem equiv_sponge_perm (c : ℤ) (m : List Bool) : equiv_sponge_perm.statement c m := by
  sorry

/-- `clone import Program as Prog with type t <- bool, op d <- dbool`. -/
noncomputable abbrev Prog.LoopSnoc.sample := DList.Program.LoopSnoc.sample Bool dbool

theorem equiv_ro_iro (c : ℤ) (m : List Bool) : equiv_ro_iro.statement c m := by
  sorry

end Preimage

/-- EC's `Sponge_preimage_resistant &m ha`, for the section's `A` and its axiom `A_ll`. -/
theorem Sponge_preimage_resistant (A : SRO.AdvPreimage)
    (hA : Module.Representable A SRO.Oracle.ext)
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
  sorry

theorem invmC' (m mi : FMap state state) : invm m mi → invm mi m := by
  sorry

theorem invmC (m mi : FMap state state) : invm m mi ↔ invm mi m := by
  sorry

theorem useful (m mi : FMap state state) (a : state) :
    invm m mi → ¬ FMap.dom m a → is_lossless (dexcepted (dprod bdistr cdistr) (FMap.rng m)) := by
  sorry

theorem equiv_sponge_perm (c : ℤ) (m : List Bool) : equiv_sponge_perm.statement c m := by
  sorry

/-- `clone import Program as Prog2 with type t <- bool, op d <- dbool`. -/
noncomputable abbrev Prog2.LoopSnoc.sample := DList.Program.LoopSnoc.sample Bool dbool

theorem equiv_ro_iro (c : ℤ) (m : List Bool) : equiv_ro_iro.statement c m := by
  sorry

end SecondPreimage

/-- EC's `Sponge_second_preimage_resistant &m mess`, for the section's `A` and its axiom
`A_ll`. -/
theorem Sponge_second_preimage_resistant (A : SRO.AdvSecondPreimage)
    (hA : Module.Representable A SRO.Oracle.ext)
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
  sorry

theorem invmC' (m mi : FMap state state) : invm m mi → invm mi m := by
  sorry

theorem invmC (m mi : FMap state state) : invm m mi ↔ invm mi m := by
  sorry

theorem useful (m mi : FMap state state) (a : state) :
    invm m mi → ¬ FMap.dom m a → is_lossless (dexcepted (dprod bdistr cdistr) (FMap.rng m)) := by
  sorry

theorem equiv_sponge_perm (c : ℤ) (m : List Bool) : equiv_sponge_perm.statement c m := by
  sorry

/-- `clone import Program as Prog3 with type t <- bool, op d <- dbool`. -/
noncomputable abbrev Prog3.LoopSnoc.sample := DList.Program.LoopSnoc.sample Bool dbool

theorem equiv_ro_iro (c : ℤ) (m : List Bool) : equiv_ro_iro.statement c m := by
  sorry

end Collision

/-- EC's `Sponge_coll_resistant &m`, for the section's `A` and its axiom `A_ll`. -/
theorem Sponge_coll_resistant (A : SRO.AdvCollision)
    (hA : Module.Representable A SRO.Oracle.ext)
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
    (hA : Module.Representable A SRO.Oracle.ext)
    (_hAd : FVP.fvP A ≤ ARestrictions.footprintᶜ)
    (_A_ll : IndifRO_is_secure.D_ll (List Bool) f_out A)
    (m : VariableAssignment) :
    (Procedure.Pr (Module.app SRO.Collision
        (Module.pair (AdvCollisionSHA3 A) (FM.asRO (CSetSize Sponge.Sponge) Perm))).procedure ()
        m (fun r _ => r = true) : ℝ) ≤
      bound + ((sigma * (sigma - 1) + 2 : ℤ) : ℝ) / 2 / (2 : ℝ) ^ size_out := by
  sorry

end GaudisCrypt.SHA3.SHA3Security
