import GaudisCrypt.Examples.SHA3.SecureRO
import GaudisCrypt.Examples.SHA3.Indifferentiability

/-!
# A construction indifferentiable from a random oracle is secure
(EasyCrypt `proof/IndifRO_is_secure.ec`)

Collision, preimage and second-preimage resistance of `FM(C, P)` (a construction `C` over a
primitive `P`), from the resistance of the random oracle (`SecureRO`) and the indifferentiability
of `C(P)` from it, up to `bound`.

Translation notes (see `notes/SHA3/README.md`):
* EasyCrypt declares the file's types `block`, `f_in`, `f_out` and operators `sampleto`, `limit`,
  `bound`, `bound_counter`, `increase_counter` abstractly, and `SHA3Security` clones the file.  So
  they are section variables, as for an abstract theory, and the axioms are the structure `Axioms`.
* `clone import SecureRO as SRO with type from <- f_in, type to <- f_out, op bound <- limit, …` is
  the namespace `SRO` of abbreviations; `clone import Indifferentiability as Indiff0 with type p <-
  block, …` is `Indifferentiability` at `block f_in f_out`.
* The module variables (`SRO`'s `RO.m`, `FRO.m`, `Counter.c`, `Bounder.bounder`, and `DPre.h`,
  `D2Pre.m2`) are lens parameters: the clone in `SHA3Security` declares its own.
* `RO` (`proc init = SRO.RO.RO.init`, `proc f = SRO.RO.RO.get`) is only used as it stands: a Lean
  definition assembling the aliased procedures.  `FInit(F)`, `GetF(F)`, `SInit(F)(S)`, `FM(C)(P)`
  and `DColl(A)(F)(P)` are applied to module parameters, so their aliases are wrapped in a call
  (exception E5).  `FInit` and `FM` have more procedures than `SRO.RF` and `SRO.RO.RO_T`: they are
  declared without a type, and their views are written out.
* The sections' `declare axiom D_ll` is a hypothesis of each lemma (EasyCrypt's closed statements
  keep it).  `exists (S <: SIMULATOR {…})` ranges over representable simulators with that
  footprint (exception E2).
-/

-- the clone `SRO.RO` contains the module `RO` (`SRO.RO.RO`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.IndifRO_is_secure

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Indifferentiability

variable (block f_in f_out : Type) [Inhabited block] [DecidableEq f_in] [Inhabited f_in]
  [Inhabited f_out]
variable (sampleto : SubProbability f_out)
variable (limit : ℤ)
variable (bound : ℝ)
variable (bound_counter : ℤ)
variable (increase_counter : ℤ → f_in → ℤ)

/-- EasyCrypt's axioms on the file's operators (a hypothesis, realized by a clone). -/
structure Axioms : Prop where
  sampleto_ll : is_lossless sampleto
  sampleto_fu : is_funiform sampleto
  sampleto_full : is_full sampleto
  limit_gt0 : 0 < limit
  bound_counter_ge0 : 0 ≤ bound_counter
  increase_counter_spec : ∀ c m, c ≤ increase_counter c m

/-! `clone import SecureRO as SRO with type from <- f_in, type to <- f_out, op bound <- limit,
op sampleto <- sampleto, op increase_counter <- increase_counter,
op bound_counter <- bound_counter`; its module variables are the lens parameters `SRO_RO_m`,
`SRO_FRO_m`, `SRO_Counter_c`, `SRO_Bounder_bounder`. -/

-- one binder each: a `module` takes a whole binder group when it mentions one of its names
variable (SRO_RO_m : Lens (FMap f_in f_out) VariableAssignment)
variable (SRO_FRO_m : Lens (FMap f_in (f_out × PROM.flag)) VariableAssignment)
variable (SRO_Counter_c : Lens ℤ VariableAssignment)
variable (SRO_Bounder_bounder : Lens ℤ VariableAssignment)

namespace SRO
abbrev RF := SecureRO.RF f_in f_out
abbrev Oracle := SecureRO.Oracle f_in f_out
noncomputable abbrev Oracle.ext := SecureRO.Oracle.ext f_in f_out
abbrev AdvPreimage := SecureRO.AdvPreimage f_in f_out
abbrev AdvSecondPreimage := SecureRO.AdvSecondPreimage f_in f_out
abbrev AdvCollision := SecureRO.AdvCollision f_in f_out
noncomputable abbrev Preimage := SecureRO.Preimage f_in f_out limit increase_counter bound_counter
  SRO_Counter_c SRO_Bounder_bounder
noncomputable abbrev SecondPreimage := SecureRO.SecondPreimage f_in f_out limit increase_counter
  bound_counter SRO_Counter_c SRO_Bounder_bounder
noncomputable abbrev Collision := SecureRO.Collision f_in f_out limit increase_counter
  bound_counter SRO_Counter_c SRO_Bounder_bounder
namespace RO
abbrev RO_T := SecureRO.RO.RO_T f_in f_out
noncomputable abbrev RO := SecureRO.RO.RO f_in f_out sampleto SRO_RO_m
noncomputable abbrev RO.asRF := SecureRO.RO.asRF f_in f_out sampleto SRO_RO_m
end RO
end SRO

/-- EasyCrypt's `module RO : FUNCTIONALITY = { proc init = SRO.RO.RO.init proc f =
SRO.RO.RO.get }`. -/
noncomputable def RO : FUNCTIONALITY block f_in f_out :=
  FUNCTIONALITY.mk block f_in f_out
    { init := PROM.FullRO.RO_T.init f_in f_out (SRO.RO.RO f_in f_out sampleto SRO_RO_m)
      f := PROM.FullRO.RO_T.get f_in f_out (SRO.RO.RO f_in f_out sampleto SRO_RO_m) }

-- EC's `FInit(F : DFUNCTIONALITY)`, with `proc get = F.f` and `proc f = F.f` wrapped in a call
-- (exception E5); no type annotation (it has more procedures than `SRO.RO.RO_T`)
module FInit using (F : DFUNCTIONALITY block f_in f_out) {
  proc init () : Unit {
    return ()
  };
  proc get (x : f_in) : f_out {
    var y : f_out;
    y <- call F.f ($x);
    return $y
  };
  proc f (x : f_in) : f_out {
    var y : f_out;
    y <- call F.f ($x);
    return $y
  };
  proc set (_a : f_in, _b : f_out) : Unit {
    return ()
  };
  proc sample (_a : f_in) : Unit {
    return ()
  };
  proc rem (_a : f_in) : Unit {
    return ()
  };
}

/-- `FInit(F)` at `SRO.RF`. -/
noncomputable def FInit.asRF (F : DFUNCTIONALITY block f_in f_out) : SRO.RF f_in f_out :=
  SecureRO.RF.mk f_in f_out
    { init := FInit.init block f_in f_out, get := Module.app (FInit.get block f_in f_out) F }

/-- `FInit(F)` at `SRO.RO.RO_T`. -/
noncomputable def FInit.asRO (F : DFUNCTIONALITY block f_in f_out) : SRO.RO.RO_T f_in f_out :=
  PROM.FullRO.RO_T.mk f_in f_out
    { init := FInit.init block f_in f_out, get := Module.app (FInit.get block f_in f_out) F,
      set := FInit.set block f_in f_out, rem := FInit.rem block f_in f_out,
      sample := FInit.sample block f_in f_out }

-- EC's `GetF(F : SRO.RO.RO)`, with `proc init = F.init`, `proc f = F.get` wrapped in a call
-- (exception E5)
module GetF using (F : SRO.RO.RO_T f_in f_out) : (FUNCTIONALITY block f_in f_out) {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (x : f_in) : f_out {
    var y : f_out;
    y <- call F.get ($x);
    return $y
  };
}

-- EC's `SInit(F : SRO.RO.RO)(S : SIMULATOR)`, with its aliases of `F`'s procedures wrapped in a
-- call (exception E5)
module SInit using (F : SRO.RO.RO_T f_in f_out, S : SIMULATOR block f_in f_out)
    : (SRO.RO.RO_T f_in f_out) {
  proc init () : Unit {
    _ <- call (PRIMITIVE.init block f_in f_out (Module.app S
      (DFUNCTIONALITY.mk block f_in f_out
        { f := FUNCTIONALITY.f block f_in f_out (Module.app (GetF block f_in f_out) F) }))) ();
    _ <- call F.init ();
    return ()
  };
  proc get (x : f_in) : f_out {
    var y : f_out;
    y <- call F.get ($x);
    return $y
  };
  proc set (x : f_in, y : f_out) : Unit {
    _ <- call F.set ($x, $y);
    return ()
  };
  proc rem (x : f_in) : Unit {
    _ <- call F.rem ($x);
    return ()
  };
  proc sample (x : f_in) : Unit {
    _ <- call F.sample ($x);
    return ()
  };
}

-- EC's `FM(C : CONSTRUCTION)(P : PRIMITIVE)`, with `proc get = C(P).f`, `proc f = C(P).f` wrapped
-- in a call (exception E5); no type annotation (it has more procedures than `SRO.RO.RO_T`)
module FM using (C : CONSTRUCTION block f_in f_out, P : PRIMITIVE block f_in f_out) {
  proc init () : Unit {
    _ <- call P.init ();
    _ <- call (FUNCTIONALITY.init block f_in f_out (Module.app C
      (DPRIMITIVE.mk block f_in f_out
        { f := PRIMITIVE.f block f_in f_out P, fi := PRIMITIVE.fi block f_in f_out P }))) ();
    return ()
  };
  proc get (x : f_in) : f_out {
    var y : f_out;
    y <- call (FUNCTIONALITY.f block f_in f_out (Module.app C
      (DPRIMITIVE.mk block f_in f_out
        { f := PRIMITIVE.f block f_in f_out P, fi := PRIMITIVE.fi block f_in f_out P }))) ($x);
    return $y
  };
  proc f (x : f_in) : f_out {
    var y : f_out;
    y <- call (FUNCTIONALITY.f block f_in f_out (Module.app C
      (DPRIMITIVE.mk block f_in f_out
        { f := PRIMITIVE.f block f_in f_out P, fi := PRIMITIVE.fi block f_in f_out P }))) ($x);
    return $y
  };
  proc set (_a : f_in, _b : f_out) : Unit {
    return ()
  };
  proc sample (_a : f_in) : Unit {
    return ()
  };
  proc rem (_a : f_in) : Unit {
    return ()
  };
}

/-- `FM(C, P)` at `SRO.RF`. -/
noncomputable def FM.asRF (C : CONSTRUCTION block f_in f_out) (P : PRIMITIVE block f_in f_out) :
    SRO.RF f_in f_out :=
  SecureRO.RF.mk f_in f_out
    { init := Module.app (Module.app (FM.init block f_in f_out) C) P
      get := Module.app (Module.app (FM.get block f_in f_out) C) P }

/-- `FM(C, P)` at `SRO.RO.RO_T`. -/
noncomputable def FM.asRO (C : CONSTRUCTION block f_in f_out) (P : PRIMITIVE block f_in f_out) :
    SRO.RO.RO_T f_in f_out :=
  PROM.FullRO.RO_T.mk f_in f_out
    { init := Module.app (Module.app (FM.init block f_in f_out) C) P
      get := Module.app (Module.app (FM.get block f_in f_out) C) P
      set := FM.set block f_in f_out, rem := FM.rem block f_in f_out,
      sample := FM.sample block f_in f_out }

-- EC's `DColl(A : AdvCollision)(F)(P)`, with `A` a Lean parameter so that `DColl A` is a
-- `DISTINGUISHER`; its `proc distinguish = Collision(A, FInit(F)).main` is wrapped in a call
-- (exception E5)
set_option linter.gaudisCrypt.using false in
module DColl (A : SRO.AdvCollision f_in f_out)
    using (F : DFUNCTIONALITY block f_in f_out, P : DPRIMITIVE block f_in f_out) {
  proc distinguish () : Bool {
    var b : Bool;
    b <- call (Module.app (SRO.Collision f_in f_out limit bound_counter increase_counter
      SRO_Counter_c SRO_Bounder_bounder) (Module.pair A
        (PROM.FullRO.RO_T.mk f_in f_out
          { init := FInit.init block f_in f_out, get := Module.app (FInit.get block f_in f_out) F,
            set := FInit.set block f_in f_out, rem := FInit.rem block f_in f_out,
            sample := FInit.sample block f_in f_out }))) ();
    return $b
  };
}

/-- The sections' `declare axiom D_ll (F <: Oracle {-A}) : islossless F.get =>
islossless A(F).guess` (an abbreviation). -/
def D_ll {sig : ProcedureSignature} (A : SRO.Oracle f_in f_out →ₘ Module.Proc sig) : Prop :=
  ∀ F : SRO.Oracle f_in f_out, FVP.fvP F ≤ (FVP.fvP A)ᶜ →
    (SecureRO.Oracle.get f_in f_out F).procedure.IsLossless →
    (Module.app A F).procedure.IsLossless

/-- `forall (F <: FUNCTIONALITY), islossless F.f => islossless S(F).init` (an abbreviation). -/
def S_ll (S : SIMULATOR block f_in f_out) : Prop :=
  ∀ F : FUNCTIONALITY block f_in f_out, (FUNCTIONALITY.f block f_in f_out F).procedure.IsLossless →
    (PRIMITIVE.init block f_in f_out
      (Module.app S (FUNCTIONALITY.view block f_in f_out F))).procedure.IsLossless

/-! ## The section `Collision`, with `declare module A <: AdvCollision {-Bounder, -SRO.RO.RO,
-SRO.RO.FRO}` and `declare axiom D_ll` -/

/-- EC's `coll_resistant_if_indifferentiable (C <: CONSTRUCTION {-A, -Bounder})
(P <: PRIMITIVE {-C, -A, -Bounder}) &m`, for the section's `A`. -/
theorem coll_resistant_if_indifferentiable
    (hax : Axioms f_in f_out sampleto limit bound_counter increase_counter)
    (A : SRO.AdvCollision f_in f_out) (hA : Module.ECModule A (SRO.Oracle.ext f_in f_out))
    (_hAd : FVP.fvP A ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_RO_m.footprint ⊔
      SRO_FRO_m.footprint)ᶜ)
    (_D_ll : D_ll f_in f_out A)
    (C : CONSTRUCTION block f_in f_out)
    (_hC : FVP.fvP C ≤ (FVP.fvP A ⊔ SRO_Bounder_bounder.footprint)ᶜ)
    (P : PRIMITIVE block f_in f_out)
    (_hP : FVP.fvP P ≤ (FVP.fvP C ⊔ FVP.fvP A ⊔ SRO_Bounder_bounder.footprint)ᶜ)
    (m : VariableAssignment) :
    (∃ S : SIMULATOR block f_in f_out, SIMULATOR.ECModule block f_in f_out S ∧
      FVP.fvP S ≤ (SRO_Bounder_bounder.footprint ⊔ FVP.fvP A)ᶜ ∧
      S_ll block f_in f_out S ∧
      |(Procedure.Pr (GReal block f_in f_out C P (DColl block f_in f_out limit bound_counter
          increase_counter SRO_Counter_c SRO_Bounder_bounder A)).procedure () m
          (fun r _ => r = true) : ℝ) -
        (Procedure.Pr (GIdeal block f_in f_out (RO block f_in f_out sampleto SRO_RO_m) S
          (DColl block f_in f_out limit bound_counter increase_counter SRO_Counter_c
            SRO_Bounder_bounder A)).procedure () m (fun r _ => r = true) : ℝ)| ≤ bound) →
    (Procedure.Pr (Module.app (SRO.Collision f_in f_out limit bound_counter increase_counter
        SRO_Counter_c SRO_Bounder_bounder) (Module.pair A (FM.asRO block f_in f_out C P))).procedure
        () m (fun r _ => r = true) : ℝ) ≤
      bound + ((limit * (limit - 1) + 2 : ℤ) : ℝ) / 2 * (sampleto.1 {default}).toReal := by
  sorry

/-! `DPre`'s and `D2Pre`'s module variables `h`, `m2` are the lens parameters `DPre_h`,
`D2Pre_m2`. -/
variable (DPre_h : Lens f_out VariableAssignment)
variable (D2Pre_m2 : Lens f_in VariableAssignment)

-- EC's `DPre(A : AdvPreimage)(F)(P)`, with `A` a Lean parameter so that `DPre A` is a
-- `DISTINGUISHER`
set_option linter.gaudisCrypt.using false in
module DPre (A : SRO.AdvPreimage f_in f_out)
    using (F : DFUNCTIONALITY block f_in f_out, P : DPRIMITIVE block f_in f_out) {
  proc distinguish () : Bool {
    var b : Bool;
    b <- call (Module.app (SRO.Preimage f_in f_out limit bound_counter increase_counter
      SRO_Counter_c SRO_Bounder_bounder) (Module.pair A
        (SecureRO.RF.mk f_in f_out
          { init := FInit.init block f_in f_out,
            get := Module.app (FInit.get block f_in f_out) F }))) ($DPre_h);
    return $b
  };
}

/-! ## The section `Preimage`, with `declare module A <: AdvPreimage {-Bounder, -SRO.RO.RO,
-SRO.RO.FRO, -DPre}` and `declare axiom D_ll` -/

/-- EC's `preimage_resistant_if_indifferentiable (C <: CONSTRUCTION {-A, -Bounder, -DPre})
(P <: PRIMITIVE {-C, -A, -Bounder, -DPre}) &m hash`, for the section's `A`. -/
theorem preimage_resistant_if_indifferentiable
    (hax : Axioms f_in f_out sampleto limit bound_counter increase_counter)
    (A : SRO.AdvPreimage f_in f_out) (hA : Module.ECModule A (SRO.Oracle.ext f_in f_out))
    (_hAd : FVP.fvP A ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_RO_m.footprint ⊔
      SRO_FRO_m.footprint ⊔ DPre_h.footprint)ᶜ)
    (_D_ll : D_ll f_in f_out A)
    (C : CONSTRUCTION block f_in f_out)
    (_hC : FVP.fvP C ≤ (FVP.fvP A ⊔ SRO_Bounder_bounder.footprint ⊔ DPre_h.footprint)ᶜ)
    (P : PRIMITIVE block f_in f_out)
    (_hP : FVP.fvP P ≤ (FVP.fvP C ⊔ FVP.fvP A ⊔ SRO_Bounder_bounder.footprint ⊔
      DPre_h.footprint)ᶜ)
    (m : VariableAssignment) (hash : f_out) :
    DPre_h.get m = hash →
    (∃ S : SIMULATOR block f_in f_out, SIMULATOR.ECModule block f_in f_out S ∧
      FVP.fvP S ≤ (SRO_Bounder_bounder.footprint ⊔ FVP.fvP A ⊔ DPre_h.footprint)ᶜ ∧
      S_ll block f_in f_out S ∧
      |(Procedure.Pr (GReal block f_in f_out C P (DPre block f_in f_out limit bound_counter
          increase_counter SRO_Counter_c SRO_Bounder_bounder DPre_h A)).procedure () m
          (fun r _ => r = true) : ℝ) -
        (Procedure.Pr (GIdeal block f_in f_out (RO block f_in f_out sampleto SRO_RO_m) S
          (DPre block f_in f_out limit bound_counter increase_counter SRO_Counter_c
            SRO_Bounder_bounder DPre_h A)).procedure () m (fun r _ => r = true) : ℝ)| ≤ bound) →
    (Procedure.Pr (Module.app (SRO.Preimage f_in f_out limit bound_counter increase_counter
        SRO_Counter_c SRO_Bounder_bounder) (Module.pair A (FM.asRF block f_in f_out C P))).procedure
        hash m (fun r _ => r = true) : ℝ) ≤
      bound + ((limit + 1 : ℤ) : ℝ) * (sampleto.1 {hash}).toReal := by
  sorry

-- EC's `D2Pre(A : AdvSecondPreimage)(F)(P)`, with `A` a Lean parameter so that `D2Pre A` is a
-- `DISTINGUISHER`
set_option linter.gaudisCrypt.using false in
module D2Pre (A : SRO.AdvSecondPreimage f_in f_out)
    using (F : DFUNCTIONALITY block f_in f_out, P : DPRIMITIVE block f_in f_out) {
  proc distinguish () : Bool {
    var b : Bool;
    b <- call (Module.app (SRO.SecondPreimage f_in f_out limit bound_counter increase_counter
      SRO_Counter_c SRO_Bounder_bounder) (Module.pair A
        (SecureRO.RF.mk f_in f_out
          { init := FInit.init block f_in f_out,
            get := Module.app (FInit.get block f_in f_out) F }))) ($D2Pre_m2);
    return $b
  };
}

/-! ## The section `SecondPreimage`, with `declare module A <: AdvSecondPreimage {-Bounder,
-SRO.RO.RO, -SRO.RO.FRO, -D2Pre}` and `declare axiom D_ll` -/

/-- EC's `second_preimage_resistant_if_indifferentiable (C <: CONSTRUCTION {-A, -Bounder, -D2Pre})
(P <: PRIMITIVE {-C, -A, -Bounder, -D2Pre}) &m mess`, for the section's `A`. -/
theorem second_preimage_resistant_if_indifferentiable
    (hax : Axioms f_in f_out sampleto limit bound_counter increase_counter)
    (A : SRO.AdvSecondPreimage f_in f_out)
    (hA : Module.ECModule A (SRO.Oracle.ext f_in f_out))
    (_hAd : FVP.fvP A ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_RO_m.footprint ⊔
      SRO_FRO_m.footprint ⊔ D2Pre_m2.footprint)ᶜ)
    (_D_ll : D_ll f_in f_out A)
    (C : CONSTRUCTION block f_in f_out)
    (_hC : FVP.fvP C ≤ (FVP.fvP A ⊔ SRO_Bounder_bounder.footprint ⊔ D2Pre_m2.footprint)ᶜ)
    (P : PRIMITIVE block f_in f_out)
    (_hP : FVP.fvP P ≤ (FVP.fvP C ⊔ FVP.fvP A ⊔ SRO_Bounder_bounder.footprint ⊔
      D2Pre_m2.footprint)ᶜ)
    (m : VariableAssignment) (mess : f_in) :
    D2Pre_m2.get m = mess →
    (∃ S : SIMULATOR block f_in f_out, SIMULATOR.ECModule block f_in f_out S ∧
      FVP.fvP S ≤ (SRO_Bounder_bounder.footprint ⊔ FVP.fvP A ⊔ D2Pre_m2.footprint)ᶜ ∧
      S_ll block f_in f_out S ∧
      |(Procedure.Pr (GReal block f_in f_out C P (D2Pre block f_in f_out limit bound_counter
          increase_counter SRO_Counter_c SRO_Bounder_bounder D2Pre_m2 A)).procedure () m
          (fun r _ => r = true) : ℝ) -
        (Procedure.Pr (GIdeal block f_in f_out (RO block f_in f_out sampleto SRO_RO_m) S
          (D2Pre block f_in f_out limit bound_counter increase_counter SRO_Counter_c
            SRO_Bounder_bounder D2Pre_m2 A)).procedure () m (fun r _ => r = true) : ℝ)| ≤
        bound) →
    (Procedure.Pr (Module.app (SRO.SecondPreimage f_in f_out limit bound_counter increase_counter
        SRO_Counter_c SRO_Bounder_bounder) (Module.pair A (FM.asRF block f_in f_out C P))).procedure
        mess m (fun r _ => r = true) : ℝ) ≤
      bound + ((limit + 1 : ℤ) : ℝ) * (sampleto.1 {default}).toReal := by
  sorry

end GaudisCrypt.SHA3.IndifRO_is_secure
