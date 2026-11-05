import GaudisCrypt.Examples.SHA3.SecureRO
import GaudisCrypt.Examples.SHA3.Indifferentiability
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.PHoareWp

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
  ∀ F : SRO.Oracle f_in f_out, FVP.fvP F ≤ (FVP.fvP A).globᶜ →
    (SecureRO.Oracle.get f_in f_out F).procedure.IsLossless →
    (Module.app A F).procedure.IsLossless

/-- `D_ll` for the oracles outside a region `G` instead of `glob A` (exception E14): what an adversary
built from an abstract one satisfies (EasyCrypt's `glob` is syntactic: `glob AdvCollisionSHA3(A) =
glob A`).  `D_ll A` is `D_ll_at A (glob A)`. -/
def D_ll_at {sig : ProcedureSignature} (A : SRO.Oracle f_in f_out →ₘ Module.Proc sig)
    (G : Footprint VariableAssignment) : Prop :=
  ∀ F : SRO.Oracle f_in f_out, FVP.fvP F ≤ Gᶜ →
    (SecureRO.Oracle.get f_in f_out F).procedure.IsLossless →
    (Module.app A F).procedure.IsLossless

/-- `forall (F <: FUNCTIONALITY), islossless F.f => islossless S(F).init` (an abbreviation). -/
def S_ll (S : SIMULATOR block f_in f_out) : Prop :=
  ∀ F : FUNCTIONALITY block f_in f_out, (FUNCTIONALITY.f block f_in f_out F).procedure.IsLossless →
    (PRIMITIVE.init block f_in f_out
      (Module.app S (FUNCTIONALITY.view block f_in f_out F))).procedure.IsLossless

/-! ## The section `Collision`, with `declare module A <: AdvCollision {-Bounder, -SRO.RO.RO,
-SRO.RO.FRO}` and `declare axiom D_ll` -/

/-- The first `have` of EC's proof of `coll_resistant_if_indifferentiable`, as an equivalence:
`Collision(A, FM(C, P)).main ~ GReal(C, P, DColl(A)).main : ={glob} ==> ={res}`, by EC's
`proc; inline*; wp; sim. by swap {1} [1..2] 2; sim.` -/
theorem Collision_FM_GReal (A : SRO.AdvCollision f_in f_out) (C : CONSTRUCTION block f_in f_out)
    (P : PRIMITIVE block f_in f_out)
    (_hC : FVP.fvP C ≤ ((FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔
      SRO_Counter_c.footprint)ᶜ)
    (_hP : FVP.fvP P ≤ ((FVP.fvP C).glob ⊔ (FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔
      SRO_Counter_c.footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (Module.app (SRO.Collision f_in f_out limit bound_counter increase_counter
        SRO_Counter_c SRO_Bounder_bounder) (Module.pair A (FM.asRO block f_in f_out C P))).procedure
      (GReal block f_in f_out C P (DColl block f_in f_out limit bound_counter
          increase_counter SRO_Counter_c SRO_Bounder_bounder A)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  -- `proc; inline*` (the swap is EC's second step, done here between the inlining steps)
  equiv_proc
  stmt_inline 0
  stmt_inline{1} 0
  stmt_inline{2} 2
  stmt_inline{1} 0
  stmt_inline{1} 0
  -- `swap {1} [1..2] 2`: `Bounder.bounder <- 0; Counter.c <- 0` past `P.init(); C(P).init()`
  stmt_swap{1} 4 3
  stmt_swap{1} 2 4
  stmt_inline{2} 2
  stmt_inline{2} 2
  stmt_inline{2} 2
  stmt_inline{2} 2
  stmt_inline{1} 3
  stmt_inline{1} 4
  stmt_inline{2} 3
  stmt_inline{2} 4
  -- `wp; sim`: `equiv_sim` on straight-line code, the conditionals cut by hand
  stmt_wp
  equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧ §allGlobals{1} = §allGlobals{2})
  · equiv_sim
    -- the adversary's oracles, `Bounder(FM(C,P))` and `Bounder(FInit(DColl…))`, are equal
    case callee =>
      simp only [SecureRO.Bounder.apply_simp, SecureRO.RF.get.mk_simp,
        SecureRO.Bounder.get.apply_simp, SecureRO.Bounder.get.procedure.apply_simp,
        HoleSigs.Instantiation.lookup_zero_single, PROM.FullRO.RO_T.get.mk_simp, FM.asRO,
        FM.get.apply_simp, FInit.get.apply_simp, Module.procedure_proc', DFUNCTIONALITY.f.mk_simp,
        PRIMITIVE.view]
      rfl
  · equiv_if
    case «then» =>
      equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧ §allGlobals{1} = §allGlobals{2} ∧
        §hash1{1} = §hash1{2})
      · equiv_sim
      · equiv_if
        case «then» => equiv_sim
        case «else» => equiv_sim
        case guard => intros; simp_all
    case «else» => equiv_sim
    case guard => intros; simp_all

/-- A helper of EC's `sim` in `GIdeal_Collision_RO`: `FInit(RO).get` (`RO.get` behind `FInit`'s
alias) and `SRO.RO.RO.get`, on equal arguments, `Counter.c` and `RO.m`, return equal results and
leave `Counter.c` and `RO.m` equal. -/
theorem RO_get_FInit_equiv [Lens.Disjoint SRO_Counter_c SRO_RO_m] :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ SRO_Counter_c.get g₁ = SRO_Counter_c.get g₂ ∧
        SRO_RO_m.get g₁ = SRO_RO_m.get g₂)
      (PROM.FullRO.RO_T.get f_in f_out
        (PROM.FullRO.RO_T.mk f_in f_out
          { init := FInit.init block f_in f_out,
            get := Module.app (FInit.get block f_in f_out)
              (DFUNCTIONALITY.mk block f_in f_out
                { f := FUNCTIONALITY.f block f_in f_out (RO block f_in f_out sampleto SRO_RO_m) }),
            set := FInit.set block f_in f_out, rem := FInit.rem block f_in f_out,
            sample := FInit.sample block f_in f_out })).procedure
      (PROM.FullRO.RO_T.get f_in f_out (SRO.RO.RO f_in f_out sampleto SRO_RO_m)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ SRO_Counter_c.get g₁ = SRO_Counter_c.get g₂ ∧
        SRO_RO_m.get g₁ = SRO_RO_m.get g₂) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  haveI := (inferInstance : Lens.Disjoint SRO_Counter_c SRO_RO_m).symm
  rintro g₁ g₂ x _ ⟨rfl, hc, hm⟩ a _
  simp only [hm]
  split_ifs <;> simp [hc, Lens.get_of_disjoint_set]

/-- The oracle premise of EC's `call (_: ={glob A, Bounder.bounder, Counter.c, RO.m})` in
`GIdeal_Collision_RO`: `Bounder(FInit(RO)).get` and `Bounder(RO).get` keep the invariant
`={glob} ∧ ={bounder, c, m}` (`globInvF` over the oracle state), for any region `F` outside the
oracle state. -/
theorem Bounder_FInit_get_equiv [Lens.Disjoint SRO_Bounder_bounder SRO_Counter_c]
    [Lens.Disjoint SRO_Bounder_bounder SRO_RO_m] [Lens.Disjoint SRO_Counter_c SRO_RO_m]
    (F : Footprint VariableAssignment)
    (hF : F ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔ SRO_RO_m.footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF
        (Lens.pair SRO_Bounder_bounder (Lens.pair SRO_Counter_c SRO_RO_m)) F Eq g₁ g₂)
      (SecureRO.RF.get f_in f_out
        (Module.app (SecureRO.Bounder f_in f_out limit increase_counter bound_counter
            SRO_Counter_c SRO_Bounder_bounder)
          (SecureRO.RF.mk f_in f_out
            { init := PROM.FullRO.RO_T.init f_in f_out
                (PROM.FullRO.RO_T.mk f_in f_out
                  { init := FInit.init block f_in f_out,
                    get := Module.app (FInit.get block f_in f_out)
                      (DFUNCTIONALITY.mk block f_in f_out
                        { f := FUNCTIONALITY.f block f_in f_out
                            (RO block f_in f_out sampleto SRO_RO_m) }),
                    set := FInit.set block f_in f_out, rem := FInit.rem block f_in f_out,
                    sample := FInit.sample block f_in f_out }),
              get := PROM.FullRO.RO_T.get f_in f_out
                (PROM.FullRO.RO_T.mk f_in f_out
                  { init := FInit.init block f_in f_out,
                    get := Module.app (FInit.get block f_in f_out)
                      (DFUNCTIONALITY.mk block f_in f_out
                        { f := FUNCTIONALITY.f block f_in f_out
                            (RO block f_in f_out sampleto SRO_RO_m) }),
                    set := FInit.set block f_in f_out, rem := FInit.rem block f_in f_out,
                    sample := FInit.sample block f_in f_out }) }))).procedure
      (SecureRO.RF.get f_in f_out
        (Module.app (SecureRO.Bounder f_in f_out limit increase_counter bound_counter
            SRO_Counter_c SRO_Bounder_bounder)
          (SecureRO.RF.mk f_in f_out
            { init := PROM.FullRO.RO_T.init f_in f_out (SRO.RO.RO f_in f_out sampleto SRO_RO_m),
              get := PROM.FullRO.RO_T.get f_in f_out
                (SRO.RO.RO f_in f_out sampleto SRO_RO_m) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF
        (Lens.pair SRO_Bounder_bounder (Lens.pair SRO_Counter_c SRO_RO_m)) F Eq g₁ g₂) := by
  have hb : SRO_Bounder_bounder.footprint ≤ Fᶜ := (Footprint.le_compl_comm _ _).mp
    (hF.trans (Footprint.compl_antimono (le_sup_left.trans le_sup_left)))
  have hc : SRO_Counter_c.footprint ≤ Fᶜ := (Footprint.le_compl_comm _ _).mp
    (hF.trans (Footprint.compl_antimono (le_sup_right.trans le_sup_left)))
  have hm : SRO_RO_m.footprint ≤ Fᶜ := (Footprint.le_compl_comm _ _).mp
    (hF.trans (Footprint.compl_antimono le_sup_right))
  have := (inferInstance : Lens.Disjoint SRO_Counter_c SRO_RO_m).symm
  have := (inferInstance : Lens.Disjoint SRO_Bounder_bounder SRO_RO_m).symm
  have := (inferInstance : Lens.Disjoint SRO_Bounder_bounder SRO_Counter_c).symm
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §(localVarLens "y" f_out){1} = §(localVarLens "y" f_out){2} ∧
    globInvF (Lens.pair SRO_Bounder_bounder (Lens.pair SRO_Counter_c SRO_RO_m)) F Eq
      §allGlobals{1} §allGlobals{2})
  · equiv_sim
  · equiv_if
    case «then» =>
      equiv_seq 1 1 : (§x0{1} = §x0{2} ∧
        §(localVarLens "y" f_out){1} = §(localVarLens "y" f_out){2} ∧
        globInvF (Lens.pair SRO_Bounder_bounder (Lens.pair SRO_Counter_c SRO_RO_m)) F Eq
          §allGlobals{1} §allGlobals{2})
      · equiv_sim
        intros
        simp_all [globInvF, Lens.pair, Prod.ext_iff, touched_set_of_le_compl hb,
          touched_set_of_le_compl hc,
            touched_set_of_le_compl hm, Lens.set_get, Lens.get_of_disjoint_set]
      · equiv_if
        case «then» =>
          stmt_wp
          equiv_rnd
          stmt_wp
          equiv_skip
          intros
          simp_all [globInvF, Lens.pair, Prod.ext_iff, touched_set_of_le_compl hb,
            touched_set_of_le_compl hc,
            touched_set_of_le_compl hm, Lens.set_get, Lens.get_of_disjoint_set]
          split_ifs <;> simp_all [globInvF, Lens.pair, Prod.ext_iff, touched_set_of_le_compl hb,
            touched_set_of_le_compl hc, touched_set_of_le_compl hm, Lens.set_get,
            Lens.get_of_disjoint_set]
        case «else» => equiv_sim
        case guard =>
          intros
          simp_all [globInvF, Lens.pair, Prod.ext_iff, touched_set_of_le_compl hb,
            touched_set_of_le_compl hc,
            touched_set_of_le_compl hm, Lens.set_get, Lens.get_of_disjoint_set]
    case «else» => equiv_sim
    case guard =>
      intros
      simp_all [globInvF, Lens.pair, Prod.ext_iff, touched_set_of_le_compl hb,
        touched_set_of_le_compl hc,
            touched_set_of_le_compl hm, Lens.set_get, Lens.get_of_disjoint_set]

/-- `RO.f` (`SRO.RO.RO.get`) is lossless: EC's `proc; auto; smt(sampleto_ll)`. -/
theorem RO_f_lossless (hll : is_lossless sampleto) :
    (FUNCTIONALITY.f block f_in f_out
      (RO block f_in f_out sampleto SRO_RO_m)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 5
  phoare_skip
  intro _
  letI : MeasurableSpace f_out := ⊤
  change ∫⁻ _, 1 ∂sampleto.1 = 1
  rw [MeasureTheory.lintegral_one]
  exact hll

/-- The second `have` of EC's proof of `coll_resistant_if_indifferentiable`:
`GIdeal(RO, S, DColl(A)).main ~ Collision(A, SRO.RO.RO).main : ={glob} ==> ={res}`, by EC's
`proc; inline DColl(A, RO, S(RO)).distinguish; wp; sim 3 1. inline*; swap{2} 1 1; wp.
call{1} (S_ll RO _); auto. by proc; auto; smt(sampleto_ll).`

Here: the adversary call by the abstract call rule, its invariant `={glob A}` and `={bounder, c, m}`
(EC's `sim`); the one-sided `S(RO).init` by `S_ll` and the frame of `glob A` (exception E7); the
oracle calls after it by `RO_get_FInit_equiv`.  The abstract call rule needs the oracle's argument
type countable and the oracle's variables one lens (exception E8). -/
theorem GIdeal_Collision_RO [Countable f_in] [Lens.Disjoint SRO_Bounder_bounder SRO_Counter_c]
    [Lens.Disjoint SRO_Bounder_bounder SRO_RO_m] [Lens.Disjoint SRO_Counter_c SRO_RO_m]
    (hax : Axioms f_in f_out sampleto limit bound_counter increase_counter)
    (A : SRO.AdvCollision f_in f_out) (hA : Module.ECModule A (SRO.Oracle.ext f_in f_out))
    (hAd : FVP.fvP A ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
      SRO_RO_m.footprint)ᶜ)
    (S : SIMULATOR block f_in f_out) (hS : SIMULATOR.ECModule block f_in f_out S)
    (hS_ll : S_ll block f_in f_out S)
    (hSd : FVP.fvP S ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
      (FVP.fvP A).glob)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (GIdeal block f_in f_out (RO block f_in f_out sampleto SRO_RO_m) S
          (DColl block f_in f_out limit bound_counter increase_counter SRO_Counter_c
            SRO_Bounder_bounder A)).procedure
      (Module.app (SRO.Collision f_in f_out limit bound_counter increase_counter
        SRO_Counter_c SRO_Bounder_bounder) (Module.pair A (SRO.RO.RO f_in f_out sampleto
          SRO_RO_m))).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  -- the adversary call: EC's `call (_: ={glob A, Bounder.bounder, Counter.c, RO.m})`
  have hL : FVP.fvP A ≤ ((Lens.pair SRO_Bounder_bounder
      (Lens.pair SRO_Counter_c SRO_RO_m)).footprint)ᶜ := by
    rw [Footprint.lens_pair, Footprint.lens_pair, ← sup_assoc]
    exact hAd
  have hAcall := prhlProc_abstract_call_module
    (Lens.pair SRO_Bounder_bounder (Lens.pair SRO_Counter_c SRO_RO_m)) A
    (SRO.Oracle.ext f_in f_out) hA.representable hL Eq
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable f_in)
      | succ m => nomatch m)
    _ _ (fun n => by cases n with
      | zero =>
        simp only [SecureRO.Oracle.ext, HoleSigs.Instantiation.lookup_zero_single,
          SecureRO.Oracle.get.mk_simp]
        exact Bounder_FInit_get_equiv block f_in f_out sampleto limit bound_counter
          increase_counter SRO_RO_m SRO_Counter_c SRO_Bounder_bounder _ hAd
      | succ m => nomatch m)
  equiv_proc
  stmt_inline{1} 0
  repeat stmt_inline{1} 1
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧
    §SRO_Counter_c{1} = §SRO_Counter_c{2} ∧ §SRO_RO_m{1} = §SRO_RO_m{2})
  · equiv_call hAcall
    stmt_wp
    apply prhlStmt_seq_left
    stmt_wp
    refine prhlStmt_skip fun σ₁ σ₂ hσ => ?_
    -- EC's `call{1} (S_ll RO _)`: `S(RO).init` is lossless, and keeps `glob A`
    obtain ⟨⟨pinit, pf, pfi, hrep⟩, -⟩ := hS
    have hll := hS_ll (RO block f_in f_out sampleto SRO_RO_m)
      (RO_f_lossless block f_in f_out sampleto SRO_RO_m hax.sampleto_ll)
    have hfp : ∀ a, (procedureDenotation (PRIMITIVE.init block f_in f_out
        (Module.app S (FUNCTIONALITY.view block f_in f_out
          (RO block f_in f_out sampleto SRO_RO_m)))).procedure a).inFootprint (FVP.fvP S) := by
      intro a
      rw [hrep.init]
      refine ProgramDenotation.inFootprint_mono
        (Lib.RO.Instantiate.procedureDenotation_inFootprint_fvP_proc _ a) ?_
      rw [ProcedureWithHoles.instantiate_empty]
      exact le_sup_left.trans (le_sup_left.trans hrep.fvP_le)
    have hSA : FVP.fvP S ≤ (FVP.fvP A).globᶜ := hSd.trans
      (Footprint.compl_antimono le_sup_right)
    refine ⟨Stmt.call_wp_one hll _ _ _, Stmt.call_satisfies fun r hr => ?_⟩
    have ht := ProgramDenotation.preserves_touched_of_glob (hfp _) hA.finitelySupported hSA _ r hr
    have hb : SRO_Bounder_bounder.footprint ≤ (FVP.fvP A)ᶜ := (Footprint.le_compl_comm _ _).mp
      (hAd.trans (Footprint.compl_antimono (le_sup_left.trans le_sup_left)))
    have hc : SRO_Counter_c.footprint ≤ (FVP.fvP A)ᶜ := (Footprint.le_compl_comm _ _).mp
      (hAd.trans (Footprint.compl_antimono (le_sup_right.trans le_sup_left)))
    have hm : SRO_RO_m.footprint ≤ (FVP.fvP A)ᶜ := (Footprint.le_compl_comm _ _).mp
      (hAd.trans (Footprint.compl_antimono le_sup_right))
    have := (inferInstance : Lens.Disjoint SRO_Counter_c SRO_RO_m).symm
    have := (inferInstance : Lens.Disjoint SRO_Bounder_bounder SRO_RO_m).symm
    have := (inferInstance : Lens.Disjoint SRO_Bounder_bounder SRO_Counter_c).symm
    simp only [globals_resetSetter_set] at ht
    simp_all [globInvF, Prod.ext_iff, Setter.throwaway, ProgramState.globalL,
      touched_set_of_le_compl hb, touched_set_of_le_compl hc, touched_set_of_le_compl hm,
      Lens.set_get, Lens.get_of_disjoint_set]
  · -- the rest: EC's `sim`, the oracle calls by `RO_get_FInit_equiv`
    have hget := RO_get_FInit_equiv block f_in f_out sampleto SRO_RO_m SRO_Counter_c
    equiv_if
    case «then» =>
      equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧
        §SRO_Counter_c{1} = §SRO_Counter_c{2} ∧ §SRO_RO_m{1} = §SRO_RO_m{2} ∧
        §hash1{1} = §hash1{2})
      · equiv_call hget
        stmt_wp
        equiv_skip
        intros
        simp_all
      · equiv_if
        case «then» =>
          stmt_wp
          equiv_call hget
          stmt_wp
          equiv_skip
          intros
          simp_all
        case «else» => equiv_sim
        case guard =>
          intros
          simp_all
    case «else» => equiv_sim
    case guard =>
      intros
      simp_all

/-- `coll_resistant_if_indifferentiable` with the section's axiom `D_ll` over a region `G`
(`D_ll_at`, exception E14; the proof does not use it, as EasyCrypt's). -/
theorem coll_resistant_if_indifferentiable_at
    [Countable f_in] [Lens.Disjoint SRO_Bounder_bounder SRO_Counter_c]
    [Lens.Disjoint SRO_Bounder_bounder SRO_RO_m] [Lens.Disjoint SRO_Counter_c SRO_RO_m]
    (hax : Axioms f_in f_out sampleto limit bound_counter increase_counter)
    (A : SRO.AdvCollision f_in f_out) (hA : Module.ECModule A (SRO.Oracle.ext f_in f_out))
    (_hAd : FVP.fvP A ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
      SRO_RO_m.footprint ⊔ SRO_FRO_m.footprint)ᶜ)
    (G : Footprint VariableAssignment) (_D_ll : D_ll_at f_in f_out A G)
    (C : CONSTRUCTION block f_in f_out)
    (_hC : FVP.fvP C ≤ ((FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔
      SRO_Counter_c.footprint)ᶜ)
    (P : PRIMITIVE block f_in f_out)
    (_hP : FVP.fvP P ≤ ((FVP.fvP C).glob ⊔ (FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔
      SRO_Counter_c.footprint)ᶜ)
    (m : VariableAssignment) :
    (∃ S : SIMULATOR block f_in f_out, SIMULATOR.ECModule block f_in f_out S ∧
      FVP.fvP S ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
        (FVP.fvP A).glob)ᶜ ∧
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
  rintro ⟨S, hS, hSd, hS_ll, hbound⟩
  -- `have->: Pr[Collision(A, FM(C,P)).main() @ &m : res] = Pr[GReal(C, P, DColl(A)).main() …]`
  have h1 := Procedure.Pr_eq_of_prhlProc
    (Collision_FM_GReal block f_in f_out limit bound_counter increase_counter SRO_Counter_c
      SRO_Bounder_bounder A C P _hC _hP)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true)
    (fun r₁ _ r₂ _ h => by rw [h]) (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl
  -- `have->: Pr[GIdeal(RO, S, DColl(A)).main() @ &m : res] = Pr[Collision(A, SRO.RO.RO).main() …]`
  have h2 := Procedure.Pr_eq_of_prhlProc
    (GIdeal_Collision_RO block f_in f_out sampleto limit bound_counter increase_counter
      SRO_RO_m SRO_Counter_c SRO_Bounder_bounder hax A hA (by fp_disjoint) S hS hS_ll hSd)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true)
    (fun r₁ _ r₂ _ h => by rw [h]) (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl
  -- `exact (RO_is_collision_resistant A &m)`
  have h3 := SecureRO.RO_is_collision_resistant f_in f_out sampleto limit increase_counter
    bound_counter SRO_RO_m SRO_FRO_m SRO_Counter_c SRO_Bounder_bounder
    ⟨hax.limit_gt0, hax.sampleto_ll, hax.sampleto_full, hax.sampleto_fu,
      hax.increase_counter_spec, hax.bound_counter_ge0⟩ A hA (by fp_disjoint) m
  rw [h1]
  rw [h2] at hbound
  have := (abs_le.mp hbound).2
  linarith

/-- EC's `coll_resistant_if_indifferentiable (C <: CONSTRUCTION {-A, -Bounder})
(P <: PRIMITIVE {-C, -A, -Bounder}) &m`, for the section's `A`. -/
theorem coll_resistant_if_indifferentiable
    [Countable f_in] [Lens.Disjoint SRO_Bounder_bounder SRO_Counter_c]
    [Lens.Disjoint SRO_Bounder_bounder SRO_RO_m] [Lens.Disjoint SRO_Counter_c SRO_RO_m]
    (hax : Axioms f_in f_out sampleto limit bound_counter increase_counter)
    (A : SRO.AdvCollision f_in f_out) (hA : Module.ECModule A (SRO.Oracle.ext f_in f_out))
    (_hAd : FVP.fvP A ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
      SRO_RO_m.footprint ⊔ SRO_FRO_m.footprint)ᶜ)
    (_D_ll : D_ll f_in f_out A)
    (C : CONSTRUCTION block f_in f_out)
    (_hC : FVP.fvP C ≤ ((FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔
      SRO_Counter_c.footprint)ᶜ)
    (P : PRIMITIVE block f_in f_out)
    (_hP : FVP.fvP P ≤ ((FVP.fvP C).glob ⊔ (FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔
      SRO_Counter_c.footprint)ᶜ)
    (m : VariableAssignment) :
    (∃ S : SIMULATOR block f_in f_out, SIMULATOR.ECModule block f_in f_out S ∧
      FVP.fvP S ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
        (FVP.fvP A).glob)ᶜ ∧
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
      bound + ((limit * (limit - 1) + 2 : ℤ) : ℝ) / 2 * (sampleto.1 {default}).toReal :=
  coll_resistant_if_indifferentiable_at block f_in f_out sampleto limit bound bound_counter
    increase_counter SRO_RO_m SRO_FRO_m SRO_Counter_c SRO_Bounder_bounder hax A hA _hAd _
    _D_ll C _hC P _hP m

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

/-- The first `have` of EC's proof of `preimage_resistant_if_indifferentiable`:
`Preimage(A, FM(C,P)).main ~ GReal(C, P, DPre(A)).main : ={glob} ∧ arg{1} = DPre.h{2} ==> ={res}`,
by EC's `proc; inline*; wp; sp; wp; sim. by swap {2} [1..2] 4; sim; auto; smt().`  The swap is
mirrored (`P.init(); C(P).init()` moved first on the left); `DPre.h` survives them by their
restrictions (`equiv_call_frame`). -/
theorem Preimage_FM_GReal (A : SRO.AdvPreimage f_in f_out) (C : CONSTRUCTION block f_in f_out)
    (P : PRIMITIVE block f_in f_out)
    (_hC : FVP.fvP C ≤ ((FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔
      SRO_Counter_c.footprint ⊔ DPre_h.footprint)ᶜ)
    (_hP : FVP.fvP P ≤ ((FVP.fvP C).glob ⊔ (FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔
      SRO_Counter_c.footprint ⊔ DPre_h.footprint)ᶜ) :
    prhlProc (sig₁ := procsig (f_out) -> Bool) (sig₂ := procsig () -> Bool)
      (fun a₁ g₁ _ g₂ => g₁ = g₂ ∧ a₁ = DPre_h.get g₂)
      (Module.app (SRO.Preimage f_in f_out limit bound_counter increase_counter
        SRO_Counter_c SRO_Bounder_bounder) (Module.pair A (FM.asRF block f_in f_out C P))).procedure
      (GReal block f_in f_out C P (DPre block f_in f_out limit bound_counter
          increase_counter SRO_Counter_c SRO_Bounder_bounder DPre_h A)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  -- `proc; inline*`, and the swap
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 2
  stmt_swap{1} 9 -8
  stmt_swap{1} 10 -8
  repeat stmt_inline{1} 3
  repeat stmt_inline{2} 3
  stmt_wp
  equiv_seq 1 1 : (§m{1} = §m{2} ∧ §hash{1} = §hash{2} ∧ §allGlobals{1} = §allGlobals{2})
  · equiv_call
    · stmt_wp
      equiv_call_frame DPre_h
      equiv_call_frame DPre_h
      stmt_wp
      refine prhlStmt_skip fun σ₁ σ₂ ⟨hg, ha⟩ => ?_
      simp [Setter.throwaway, globals_globalL_set, Lens.get_of_disjoint_set,
        intoLocal_varLens_get_resetSetter, mem_stringsStartingWith_iff, hg]
      intro g hg₁ g₁ hg₂
      exact ⟨ha.trans (hg₂.trans hg₁).symm, ha.trans (hg₂.trans hg₁).symm⟩
    · simp only [SecureRO.Bounder.apply_simp, SecureRO.RF.get.mk_simp,
        SecureRO.Bounder.get.apply_simp, SecureRO.Bounder.get.procedure.apply_simp,
        HoleSigs.Instantiation.lookup_zero_single, FM.asRF, FM.get.apply_simp,
        FInit.get.apply_simp, Module.procedure_proc', DFUNCTIONALITY.f.mk_simp, PRIMITIVE.view]
      rfl
  · equiv_if
    case «then» =>
      equiv_sim
    case «else» => equiv_sim
    case guard => intros; simp_all

/-- The second `have` of EC's proof of `preimage_resistant_if_indifferentiable`:
`GIdeal(RO, S, DPre(A)).main ~ Preimage(A, SRO.RO.RO).main : ={glob} ∧ arg{2} = DPre.h{1} ==>
={res}`, as `GIdeal_Collision_RO`; `DPre.h` survives the one-sided `S(RO).init` by `S`'s
restriction `{-DPre}`, and `RO.init` by the disjointness of `RO.m` and `DPre.h` (exception E8). -/
theorem GIdeal_Preimage_RO [Countable f_in] [Lens.Disjoint SRO_Bounder_bounder SRO_Counter_c]
    [Lens.Disjoint SRO_Bounder_bounder SRO_RO_m] [Lens.Disjoint SRO_Counter_c SRO_RO_m]
    [Lens.Disjoint SRO_RO_m DPre_h]
    (hax : Axioms f_in f_out sampleto limit bound_counter increase_counter)
    (A : SRO.AdvPreimage f_in f_out) (hA : Module.ECModule A (SRO.Oracle.ext f_in f_out))
    (hAd : FVP.fvP A ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
      SRO_RO_m.footprint)ᶜ)
    (S : SIMULATOR block f_in f_out) (hS : SIMULATOR.ECModule block f_in f_out S)
    (hS_ll : S_ll block f_in f_out S)
    (hSd : FVP.fvP S ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
      (FVP.fvP A).glob ⊔ DPre_h.footprint)ᶜ) :
    prhlProc (sig₁ := procsig () -> Bool) (sig₂ := procsig (f_out) -> Bool)
      (fun _ g₁ a₂ g₂ => g₁ = g₂ ∧ a₂ = DPre_h.get g₁)
      (GIdeal block f_in f_out (RO block f_in f_out sampleto SRO_RO_m) S
          (DPre block f_in f_out limit bound_counter increase_counter SRO_Counter_c
            SRO_Bounder_bounder DPre_h A)).procedure
      (Module.app (SRO.Preimage f_in f_out limit bound_counter increase_counter
        SRO_Counter_c SRO_Bounder_bounder) (Module.pair A (SRO.RO.RO.asRF f_in f_out sampleto
          SRO_RO_m))).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hL : FVP.fvP A ≤ ((Lens.pair SRO_Bounder_bounder
      (Lens.pair SRO_Counter_c SRO_RO_m)).footprint)ᶜ := by
    rw [Footprint.lens_pair, Footprint.lens_pair, ← sup_assoc]
    exact hAd
  have hAcall := prhlProc_abstract_call_module
    (Lens.pair SRO_Bounder_bounder (Lens.pair SRO_Counter_c SRO_RO_m)) A
    (SRO.Oracle.ext f_in f_out) hA.representable hL Eq
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable f_in)
      | succ m => nomatch m)
    (SecureRO.Oracle.mk f_in f_out
      { get := SecureRO.RF.get f_in f_out
          (Module.app (SecureRO.Bounder f_in f_out limit increase_counter bound_counter
              SRO_Counter_c SRO_Bounder_bounder)
            (SecureRO.RF.mk f_in f_out
              { init := FInit.init block f_in f_out,
                get := Module.app (FInit.get block f_in f_out)
                  (DFUNCTIONALITY.mk block f_in f_out
                    { f := FUNCTIONALITY.f block f_in f_out
                        (RO block f_in f_out sampleto SRO_RO_m) }) })) })
    (SecureRO.Oracle.mk f_in f_out
      { get := SecureRO.RF.get f_in f_out
          (Module.app (SecureRO.Bounder f_in f_out limit increase_counter bound_counter
              SRO_Counter_c SRO_Bounder_bounder)
            (SRO.RO.RO.asRF f_in f_out sampleto SRO_RO_m)) })
    (fun n => by cases n with
      | zero =>
        have h := Bounder_FInit_get_equiv block f_in f_out sampleto limit bound_counter
          increase_counter SRO_RO_m SRO_Counter_c SRO_Bounder_bounder _ hAd
        simp only [SecureRO.Oracle.ext, HoleSigs.Instantiation.lookup_zero_single,
          SecureRO.Oracle.get.mk_simp, SecureRO.Bounder.apply_simp, SecureRO.RF.get.mk_simp,
          SecureRO.Bounder.get.apply_simp,
          PROM.FullRO.RO_T.get.mk_simp, SecureRO.RO.asRF] at h ⊢
        exact h
      | succ m => nomatch m)
  have hget := RO_get_FInit_equiv block f_in f_out sampleto SRO_RO_m SRO_Counter_c
  simp only [PROM.FullRO.RO_T.get.mk_simp] at hget
  equiv_proc
  stmt_inline{1} 0
  repeat stmt_inline{1} 1
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§m{1} = §m{2} ∧ §hash{1} = §hash{2} ∧
    §SRO_Counter_c{1} = §SRO_Counter_c{2} ∧ §SRO_RO_m{1} = §SRO_RO_m{2})
  · equiv_call hAcall
    stmt_wp
    apply prhlStmt_seq_left
    stmt_wp
    refine prhlStmt_skip fun σ₁ σ₂ hσ => ?_
    obtain ⟨⟨pinit, pf, pfi, hrep⟩, -⟩ := hS
    have hll := hS_ll (RO block f_in f_out sampleto SRO_RO_m)
      (RO_f_lossless block f_in f_out sampleto SRO_RO_m hax.sampleto_ll)
    have hfp : ∀ a, (procedureDenotation (PRIMITIVE.init block f_in f_out
        (Module.app S (FUNCTIONALITY.view block f_in f_out
          (RO block f_in f_out sampleto SRO_RO_m)))).procedure a).inFootprint (FVP.fvP S) := by
      intro a
      rw [hrep.init]
      refine ProgramDenotation.inFootprint_mono
        (Lib.RO.Instantiate.procedureDenotation_inFootprint_fvP_proc _ a) ?_
      rw [ProcedureWithHoles.instantiate_empty]
      exact le_sup_left.trans (le_sup_left.trans hrep.fvP_le)
    have hSA : FVP.fvP S ≤ (FVP.fvP A).globᶜ :=
      hSd.trans (Footprint.compl_antimono (le_sup_right.trans le_sup_left))
    have hSh : DPre_h.footprint ≤ (FVP.fvP S)ᶜ :=
      (Footprint.le_compl_comm _ _).mp (hSd.trans (Footprint.compl_antimono le_sup_right))
    refine ⟨Stmt.call_wp_one hll _ _ _, Stmt.call_satisfies fun r hr => ?_⟩
    have ht := ProgramDenotation.preserves_touched_of_glob (hfp _) hA.finitelySupported hSA _ r hr
    have hh := Procedure.satisfies_frame hfp DPre_h hSh _ _ r hr
    have hb : SRO_Bounder_bounder.footprint ≤ (FVP.fvP A)ᶜ := (Footprint.le_compl_comm _ _).mp
      (hAd.trans (Footprint.compl_antimono (le_sup_left.trans le_sup_left)))
    have hc : SRO_Counter_c.footprint ≤ (FVP.fvP A)ᶜ := (Footprint.le_compl_comm _ _).mp
      (hAd.trans (Footprint.compl_antimono (le_sup_right.trans le_sup_left)))
    have hm : SRO_RO_m.footprint ≤ (FVP.fvP A)ᶜ := (Footprint.le_compl_comm _ _).mp
      (hAd.trans (Footprint.compl_antimono le_sup_right))
    have := (inferInstance : Lens.Disjoint SRO_Counter_c SRO_RO_m).symm
    have := (inferInstance : Lens.Disjoint SRO_Bounder_bounder SRO_RO_m).symm
    have := (inferInstance : Lens.Disjoint SRO_Bounder_bounder SRO_Counter_c).symm
    simp only [globals_resetSetter_set] at ht hh
    simp_all [globInvF, Prod.ext_iff, Setter.throwaway, ProgramState.globalL,
      touched_set_of_le_compl hb, touched_set_of_le_compl hc, touched_set_of_le_compl hm,
      Lens.set_get, Lens.get_of_disjoint_set]
  · equiv_if
    case «then» =>
      simp only [SecureRO.RF.get.mk_simp, SecureRO.RO.asRF]
      stmt_wp
      equiv_call hget
      stmt_wp
      equiv_skip
      intros
      simp_all
    case «else» => equiv_sim
    case guard =>
      intros
      simp_all

/-! ## The section `Preimage`, with `declare module A <: AdvPreimage {-Bounder, -SRO.RO.RO,
-SRO.RO.FRO, -DPre}` and `declare axiom D_ll` -/

/-- EC's `preimage_resistant_if_indifferentiable (C <: CONSTRUCTION {-A, -Bounder, -DPre})
(P <: PRIMITIVE {-C, -A, -Bounder, -DPre}) &m hash`, for the section's `A`. -/
theorem preimage_resistant_if_indifferentiable
    [Countable f_in] [Lens.Disjoint SRO_Bounder_bounder SRO_Counter_c]
    [Lens.Disjoint SRO_Bounder_bounder SRO_RO_m] [Lens.Disjoint SRO_Counter_c SRO_RO_m]
    [Lens.Disjoint SRO_RO_m DPre_h]
    (hax : Axioms f_in f_out sampleto limit bound_counter increase_counter)
    (A : SRO.AdvPreimage f_in f_out) (hA : Module.ECModule A (SRO.Oracle.ext f_in f_out))
    (_hAd : FVP.fvP A ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
      SRO_RO_m.footprint ⊔ SRO_FRO_m.footprint ⊔ DPre_h.footprint)ᶜ)
    (_D_ll : D_ll f_in f_out A)
    (C : CONSTRUCTION block f_in f_out)
    (_hC : FVP.fvP C ≤ ((FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
      DPre_h.footprint)ᶜ)
    (P : PRIMITIVE block f_in f_out)
    (_hP : FVP.fvP P ≤ ((FVP.fvP C).glob ⊔ (FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔
      SRO_Counter_c.footprint ⊔ DPre_h.footprint)ᶜ)
    (m : VariableAssignment) (hash : f_out) :
    DPre_h.get m = hash →
    (∃ S : SIMULATOR block f_in f_out, SIMULATOR.ECModule block f_in f_out S ∧
      FVP.fvP S ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
        (FVP.fvP A).glob ⊔ DPre_h.footprint)ᶜ ∧
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
  intro hinit ⟨S, hS, hSd, hS_ll, hbound⟩
  -- `have->: Pr[Preimage(A, FM(C,P)).main(hash) @ &m : res] = Pr[GReal(C, P, DPre(A)).main() …]`
  have h1 := Procedure.Pr_eq_of_prhlProc
    (Preimage_FM_GReal block f_in f_out limit bound_counter increase_counter SRO_Counter_c
      SRO_Bounder_bounder DPre_h A C P _hC _hP)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true)
    (fun r₁ _ r₂ _ h => by rw [h]) (a₁ := hash) (a₂ := ()) (σ₁ := m) (σ₂ := m) ⟨rfl, hinit.symm⟩
  -- `have->: Pr[GIdeal(RO, S, DPre(A)).main() @ &m : res] = Pr[Preimage(A, SRO.RO.RO).main(hash)]`
  have h2 := Procedure.Pr_eq_of_prhlProc
    (GIdeal_Preimage_RO block f_in f_out sampleto limit bound_counter increase_counter
      SRO_RO_m SRO_Counter_c SRO_Bounder_bounder DPre_h hax A hA (by fp_disjoint) S hS hS_ll hSd)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true)
    (fun r₁ _ r₂ _ h => by rw [h]) (a₁ := ()) (a₂ := hash) (σ₁ := m) (σ₂ := m) ⟨rfl, hinit.symm⟩
  -- `exact (RO_is_preimage_resistant A &m hash)`
  have h3 := SecureRO.RO_is_preimage_resistant f_in f_out sampleto limit increase_counter
    bound_counter SRO_RO_m SRO_Counter_c SRO_Bounder_bounder
    ⟨hax.limit_gt0, hax.sampleto_ll, hax.sampleto_full, hax.sampleto_fu,
      hax.increase_counter_spec, hax.bound_counter_ge0⟩ A hA (by fp_disjoint) m hash
  rw [h1]
  rw [h2] at hbound
  have := (abs_le.mp hbound).2
  linarith

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

/-- The first `have` of EC's proof of `second_preimage_resistant_if_indifferentiable`:
`SecondPreimage(A, FM(C,P)).main ~ GReal(C, P, D2Pre(A)).main : ={glob} ∧ arg{1} = D2Pre.m2{2}
==> ={res}`, by EC's `proc; inline*; wp; sp; wp; sim. by swap {2} [1..2] 3; sim; auto; smt().`,
as `Preimage_FM_GReal`. -/
theorem SecondPreimage_FM_GReal (A : SRO.AdvSecondPreimage f_in f_out)
    (C : CONSTRUCTION block f_in f_out)
    (P : PRIMITIVE block f_in f_out)
    (_hC : FVP.fvP C ≤ ((FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔
      SRO_Counter_c.footprint ⊔ D2Pre_m2.footprint)ᶜ)
    (_hP : FVP.fvP P ≤ ((FVP.fvP C).glob ⊔ (FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔
      SRO_Counter_c.footprint ⊔ D2Pre_m2.footprint)ᶜ) :
    prhlProc (sig₁ := procsig (f_in) -> Bool) (sig₂ := procsig () -> Bool)
      (fun a₁ g₁ _ g₂ => g₁ = g₂ ∧ a₁ = D2Pre_m2.get g₂)
      (Module.app (SRO.SecondPreimage f_in f_out limit bound_counter increase_counter
        SRO_Counter_c SRO_Bounder_bounder) (Module.pair A (FM.asRF block f_in f_out C P))).procedure
      (GReal block f_in f_out C P (D2Pre block f_in f_out limit bound_counter
          increase_counter SRO_Counter_c SRO_Bounder_bounder D2Pre_m2 A)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  -- `proc; inline*`, and the swap
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 2
  stmt_swap{1} 7 -6
  stmt_swap{1} 8 -6
  repeat stmt_inline{1} 3
  repeat stmt_inline{1} 4
  repeat stmt_inline{2} 3
  repeat stmt_inline{2} 4
  stmt_wp
  equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧ §allGlobals{1} = §allGlobals{2})
  · equiv_call
    · stmt_wp
      equiv_call_frame D2Pre_m2
      equiv_call_frame D2Pre_m2
      stmt_wp
      refine prhlStmt_skip fun σ₁ σ₂ ⟨hg, ha⟩ => ?_
      simp [Setter.throwaway, globals_globalL_set, Lens.get_of_disjoint_set,
        intoLocal_varLens_get_resetSetter, mem_stringsStartingWith_iff, hg]
      intro g hg₁ g₁ hg₂
      exact ⟨ha.trans (hg₂.trans hg₁).symm, ha.trans (hg₂.trans hg₁).symm⟩
    · simp only [SecureRO.Bounder.apply_simp, SecureRO.RF.get.mk_simp,
        SecureRO.Bounder.get.apply_simp, SecureRO.Bounder.get.procedure.apply_simp,
        HoleSigs.Instantiation.lookup_zero_single, FM.asRF, FM.get.apply_simp,
        FInit.get.apply_simp, Module.procedure_proc', DFUNCTIONALITY.f.mk_simp, PRIMITIVE.view]
      rfl
  · equiv_if
    case «then» =>
      equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧ §allGlobals{1} = §allGlobals{2} ∧
        §hash1{1} = §hash1{2})
      · equiv_sim
      · equiv_if
        case «then» => equiv_sim
        case «else» => equiv_sim
        case guard => intros; simp_all
    case «else» => equiv_sim
    case guard => intros; simp_all

/-- The second `have` of EC's proof of `second_preimage_resistant_if_indifferentiable`:
`GIdeal(RO, S, D2Pre(A)).main ~ SecondPreimage(A, SRO.RO.RO).main : ={glob} ∧
arg{2} = D2Pre.m2{1} ==> ={res}`, as `GIdeal_Preimage_RO`. -/
theorem GIdeal_SecondPreimage_RO [Countable f_in] [Lens.Disjoint SRO_Bounder_bounder SRO_Counter_c]
    [Lens.Disjoint SRO_Bounder_bounder SRO_RO_m] [Lens.Disjoint SRO_Counter_c SRO_RO_m]
    [Lens.Disjoint SRO_RO_m D2Pre_m2]
    (hax : Axioms f_in f_out sampleto limit bound_counter increase_counter)
    (A : SRO.AdvSecondPreimage f_in f_out) (hA : Module.ECModule A (SRO.Oracle.ext f_in f_out))
    (hAd : FVP.fvP A ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
      SRO_RO_m.footprint)ᶜ)
    (S : SIMULATOR block f_in f_out) (hS : SIMULATOR.ECModule block f_in f_out S)
    (hS_ll : S_ll block f_in f_out S)
    (hSd : FVP.fvP S ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
      (FVP.fvP A).glob ⊔ D2Pre_m2.footprint)ᶜ) :
    prhlProc (sig₁ := procsig () -> Bool) (sig₂ := procsig (f_in) -> Bool)
      (fun _ g₁ a₂ g₂ => g₁ = g₂ ∧ a₂ = D2Pre_m2.get g₁)
      (GIdeal block f_in f_out (RO block f_in f_out sampleto SRO_RO_m) S
          (D2Pre block f_in f_out limit bound_counter increase_counter SRO_Counter_c
            SRO_Bounder_bounder D2Pre_m2 A)).procedure
      (Module.app (SRO.SecondPreimage f_in f_out limit bound_counter increase_counter
        SRO_Counter_c SRO_Bounder_bounder) (Module.pair A (SRO.RO.RO.asRF f_in f_out sampleto
          SRO_RO_m))).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hL : FVP.fvP A ≤ ((Lens.pair SRO_Bounder_bounder
      (Lens.pair SRO_Counter_c SRO_RO_m)).footprint)ᶜ := by
    rw [Footprint.lens_pair, Footprint.lens_pair, ← sup_assoc]
    exact hAd
  have hAcall := prhlProc_abstract_call_module
    (Lens.pair SRO_Bounder_bounder (Lens.pair SRO_Counter_c SRO_RO_m)) A
    (SRO.Oracle.ext f_in f_out) hA.representable hL Eq
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable f_in)
      | succ m => nomatch m)
    (SecureRO.Oracle.mk f_in f_out
      { get := SecureRO.RF.get f_in f_out
          (Module.app (SecureRO.Bounder f_in f_out limit increase_counter bound_counter
              SRO_Counter_c SRO_Bounder_bounder)
            (SecureRO.RF.mk f_in f_out
              { init := FInit.init block f_in f_out,
                get := Module.app (FInit.get block f_in f_out)
                  (DFUNCTIONALITY.mk block f_in f_out
                    { f := FUNCTIONALITY.f block f_in f_out
                        (RO block f_in f_out sampleto SRO_RO_m) }) })) })
    (SecureRO.Oracle.mk f_in f_out
      { get := SecureRO.RF.get f_in f_out
          (Module.app (SecureRO.Bounder f_in f_out limit increase_counter bound_counter
              SRO_Counter_c SRO_Bounder_bounder)
            (SRO.RO.RO.asRF f_in f_out sampleto SRO_RO_m)) })
    (fun n => by cases n with
      | zero =>
        have h := Bounder_FInit_get_equiv block f_in f_out sampleto limit bound_counter
          increase_counter SRO_RO_m SRO_Counter_c SRO_Bounder_bounder _ hAd
        simp only [SecureRO.Oracle.ext, HoleSigs.Instantiation.lookup_zero_single,
          SecureRO.Oracle.get.mk_simp, SecureRO.Bounder.apply_simp, SecureRO.RF.get.mk_simp,
          SecureRO.Bounder.get.apply_simp,
          PROM.FullRO.RO_T.get.mk_simp, SecureRO.RO.asRF] at h ⊢
        exact h
      | succ m => nomatch m)
  have hget := RO_get_FInit_equiv block f_in f_out sampleto SRO_RO_m SRO_Counter_c
  simp only [PROM.FullRO.RO_T.get.mk_simp] at hget
  equiv_proc
  stmt_inline{1} 0
  repeat stmt_inline{1} 1
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧
    §SRO_Counter_c{1} = §SRO_Counter_c{2} ∧ §SRO_RO_m{1} = §SRO_RO_m{2})
  · equiv_call hAcall
    stmt_wp
    apply prhlStmt_seq_left
    stmt_wp
    refine prhlStmt_skip fun σ₁ σ₂ hσ => ?_
    obtain ⟨⟨pinit, pf, pfi, hrep⟩, -⟩ := hS
    have hll := hS_ll (RO block f_in f_out sampleto SRO_RO_m)
      (RO_f_lossless block f_in f_out sampleto SRO_RO_m hax.sampleto_ll)
    have hfp : ∀ a, (procedureDenotation (PRIMITIVE.init block f_in f_out
        (Module.app S (FUNCTIONALITY.view block f_in f_out
          (RO block f_in f_out sampleto SRO_RO_m)))).procedure a).inFootprint (FVP.fvP S) := by
      intro a
      rw [hrep.init]
      refine ProgramDenotation.inFootprint_mono
        (Lib.RO.Instantiate.procedureDenotation_inFootprint_fvP_proc _ a) ?_
      rw [ProcedureWithHoles.instantiate_empty]
      exact le_sup_left.trans (le_sup_left.trans hrep.fvP_le)
    have hSA : FVP.fvP S ≤ (FVP.fvP A).globᶜ :=
      hSd.trans (Footprint.compl_antimono (le_sup_right.trans le_sup_left))
    have hSh : D2Pre_m2.footprint ≤ (FVP.fvP S)ᶜ :=
      (Footprint.le_compl_comm _ _).mp (hSd.trans (Footprint.compl_antimono le_sup_right))
    refine ⟨Stmt.call_wp_one hll _ _ _, Stmt.call_satisfies fun r hr => ?_⟩
    have ht := ProgramDenotation.preserves_touched_of_glob (hfp _) hA.finitelySupported hSA _ r hr
    have hh := Procedure.satisfies_frame hfp D2Pre_m2 hSh _ _ r hr
    have hb : SRO_Bounder_bounder.footprint ≤ (FVP.fvP A)ᶜ := (Footprint.le_compl_comm _ _).mp
      (hAd.trans (Footprint.compl_antimono (le_sup_left.trans le_sup_left)))
    have hc : SRO_Counter_c.footprint ≤ (FVP.fvP A)ᶜ := (Footprint.le_compl_comm _ _).mp
      (hAd.trans (Footprint.compl_antimono (le_sup_right.trans le_sup_left)))
    have hm : SRO_RO_m.footprint ≤ (FVP.fvP A)ᶜ := (Footprint.le_compl_comm _ _).mp
      (hAd.trans (Footprint.compl_antimono le_sup_right))
    have := (inferInstance : Lens.Disjoint SRO_Counter_c SRO_RO_m).symm
    have := (inferInstance : Lens.Disjoint SRO_Bounder_bounder SRO_RO_m).symm
    have := (inferInstance : Lens.Disjoint SRO_Bounder_bounder SRO_Counter_c).symm
    simp only [globals_resetSetter_set] at ht hh
    simp_all [globInvF, Prod.ext_iff, Setter.throwaway, ProgramState.globalL,
      touched_set_of_le_compl hb, touched_set_of_le_compl hc, touched_set_of_le_compl hm,
      Lens.set_get, Lens.get_of_disjoint_set]
  · simp only [SecureRO.RF.get.mk_simp, SecureRO.RO.asRF]
    equiv_if
    case «then» =>
      equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧
        §SRO_Counter_c{1} = §SRO_Counter_c{2} ∧ §SRO_RO_m{1} = §SRO_RO_m{2} ∧
        §hash1{1} = §hash1{2})
      · equiv_call hget
        stmt_wp
        equiv_skip
        intros
        simp_all
      · equiv_if
        case «then» =>
          stmt_wp
          equiv_call hget
          stmt_wp
          equiv_skip
          intros
          simp_all
        case «else» => equiv_sim
        case guard =>
          intros
          simp_all
    case «else» => equiv_sim
    case guard =>
      intros
      simp_all

/-! ## The section `SecondPreimage`, with `declare module A <: AdvSecondPreimage {-Bounder,
-SRO.RO.RO, -SRO.RO.FRO, -D2Pre}` and `declare axiom D_ll` -/

/-- EC's `second_preimage_resistant_if_indifferentiable (C <: CONSTRUCTION {-A, -Bounder, -D2Pre})
(P <: PRIMITIVE {-C, -A, -Bounder, -D2Pre}) &m mess`, for the section's `A`. -/
theorem second_preimage_resistant_if_indifferentiable
    [Countable f_in] [Countable f_out] [Lens.Disjoint SRO_Bounder_bounder SRO_Counter_c]
    [Lens.Disjoint SRO_Bounder_bounder SRO_RO_m] [Lens.Disjoint SRO_Counter_c SRO_RO_m]
    [Lens.Disjoint SRO_RO_m D2Pre_m2] [Lens.Disjoint SRO_RO_m SRO_FRO_m]
    [Lens.Disjoint SRO_Bounder_bounder SRO_FRO_m] [Lens.Disjoint SRO_Counter_c SRO_FRO_m]
    (hBfs : SRO_Bounder_bounder.footprint.FinitelySupported)
    (hCfs : SRO_Counter_c.footprint.FinitelySupported)
    (hROfs : SRO_RO_m.footprint.FinitelySupported)
    (hFROfs : SRO_FRO_m.footprint.FinitelySupported)
    (hax : Axioms f_in f_out sampleto limit bound_counter increase_counter)
    (A : SRO.AdvSecondPreimage f_in f_out)
    (hA : Module.ECModule A (SRO.Oracle.ext f_in f_out))
    (_hAd : FVP.fvP A ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
      SRO_RO_m.footprint ⊔ SRO_FRO_m.footprint ⊔ D2Pre_m2.footprint)ᶜ)
    (_D_ll : D_ll f_in f_out A)
    (C : CONSTRUCTION block f_in f_out)
    (_hC : FVP.fvP C ≤ ((FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
      D2Pre_m2.footprint)ᶜ)
    (P : PRIMITIVE block f_in f_out)
    (_hP : FVP.fvP P ≤ ((FVP.fvP C).glob ⊔ (FVP.fvP A).glob ⊔ SRO_Bounder_bounder.footprint ⊔
      SRO_Counter_c.footprint ⊔ D2Pre_m2.footprint)ᶜ)
    (m : VariableAssignment) (mess : f_in) :
    D2Pre_m2.get m = mess →
    (∃ S : SIMULATOR block f_in f_out, SIMULATOR.ECModule block f_in f_out S ∧
      FVP.fvP S ≤ (SRO_Bounder_bounder.footprint ⊔ SRO_Counter_c.footprint ⊔
        (FVP.fvP A).glob ⊔ D2Pre_m2.footprint)ᶜ ∧
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
  intro hinit ⟨S, hS, hSd, hS_ll, hbound⟩
  -- `have->: Pr[SecondPreimage(A, FM(C,P)).main(mess) @ &m : res] = Pr[GReal(C, P, D2Pre(A)) …]`
  have h1 := Procedure.Pr_eq_of_prhlProc
    (SecondPreimage_FM_GReal block f_in f_out limit bound_counter increase_counter SRO_Counter_c
      SRO_Bounder_bounder D2Pre_m2 A C P _hC _hP)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true)
    (fun r₁ _ r₂ _ h => by rw [h]) (a₁ := mess) (a₂ := ()) (σ₁ := m) (σ₂ := m) ⟨rfl, hinit.symm⟩
  -- `have->: Pr[GIdeal(RO, S, D2Pre(A)).main() @ &m : res] = Pr[SecondPreimage(A, SRO.RO.RO) …]`
  have h2 := Procedure.Pr_eq_of_prhlProc
    (GIdeal_SecondPreimage_RO block f_in f_out sampleto limit bound_counter increase_counter
      SRO_RO_m SRO_Counter_c SRO_Bounder_bounder D2Pre_m2 hax A hA (by fp_disjoint) S hS hS_ll
      hSd)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true)
    (fun r₁ _ r₂ _ h => by rw [h]) (a₁ := ()) (a₂ := mess) (σ₁ := m) (σ₂ := m) ⟨rfl, hinit.symm⟩
  -- `exact (RO_is_second_preimage_resistant A &m mess)`
  have h3 := SecureRO.RO_is_second_preimage_resistant f_in f_out sampleto limit increase_counter
    bound_counter SRO_RO_m SRO_FRO_m SRO_Counter_c SRO_Bounder_bounder hBfs hCfs hROfs hFROfs
    ⟨hax.limit_gt0, hax.sampleto_ll, hax.sampleto_full, hax.sampleto_fu,
      hax.increase_counter_spec, hax.bound_counter_ge0⟩ A hA (by fp_disjoint) m mess
  rw [h1]
  rw [h2] at hbound
  have := (abs_le.mp hbound).2
  linarith

end GaudisCrypt.SHA3.IndifRO_is_secure
