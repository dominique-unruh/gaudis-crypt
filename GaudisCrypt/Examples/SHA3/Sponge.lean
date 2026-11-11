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
  intro _ _
  have hr := gt0_r
  rw [← Int.add_one_le_iff (b := (n + r - 1) / r), Int.le_ediv_iff_mul_le hr]
  constructor <;> intro h <;> nlinarith

/-- `equiv Sponge_is_StdSponge (P <: DPRIMITIVE) : StdSponge(P).f ~ Sponge(P).f :
={glob P, bs, n} ==> ={glob P, res}`. -/
theorem Sponge_is_StdSponge (P : DPRIMITIVE) :
    prhlProc (fun a₁ g₁ a₂ g₂ => eqGlob P g₁ g₂ ∧ a₁ = a₂)
      (Module.app StdSponge.f P).procedure (Module.app Sponge.f P).procedure
      (fun r₁ g₁ r₂ g₂ => eqGlob P g₁ g₂ ∧ r₁ = r₂) := by
  -- EC's `call (: true)` on `P.f`: `={glob P}` kept
  have hPf := prhlProc_glob (R := FVP.fvP P)
    (p := (Indifferentiability.DPRIMITIVE.f _ _ _ P).procedure)
    (fun a => ProgramDenotation.inFootprint_mono (Module.Proc.inFootprint_fvP _ a)
      (FVP.fvP_fst' _))
  have hsb : ∀ x, size (ofblock x) = r := fun x => by
    rw [← blocks2bits_sing, size_blocks2bits]; simp [size]
  have hsz : ∀ (z : List Bool) x, size (z ++ ofblock x) = size z + r := fun z x => by
    rw [← hsb x]; simp [size]
  have hr := gt0_r
  equiv_proc_to_stmt
  stmt_inline 0
  stmt_wp
  equiv_seq_last 1 1 : (eqGlob P §allGlobals{1} §allGlobals{2} ∧ ={z, sa, sc, n} ∧
      §finished{1} = false ∧ §i{2} = 0 ∧ §z{1} = [])
  · equiv_while_raw (eqGlob P §allGlobals{1} §allGlobals{2} ∧ ={z, sa, sc, n, xs} ∧
        §finished{1} = false ∧ §i{2} = 0 ∧ §z{1} = [])
    case body =>
      stmt_wp
      equiv_call hPf
      equiv_skip
      intros; simp_all [eqGlob]; aesop
    case guard => intros; simp_all
    case exit => intros; simp_all; aesop
    · stmt_wp
      equiv_skip
      intros; simp_all
  · equiv_case (§n{1} ≤ 0)
    · equiv_rcondf{2}
      equiv_while_noframe{1} (eqGlob P §allGlobals{1} §allGlobals{2} ∧ §n{1} = §n{2} ∧ §n{1} ≤ 0 ∧
          §i{2} = 0) (if §finished{1} then 0 else 1)
      case lossless =>
        intro σ₂ σ hI hg
        simp only [Stmt.ewp_seq, Stmt.ewp_assign, Stmt.ewp_ifThenElse]
        simp_reads
        have hn : (localVarLens "n" ℤ).get σ ≤ 0 := hI.2.2.1
        rw [if_neg (by
          simp only [decide_eq_true_eq, not_lt]
          refine hn.trans ?_
          simp only [size]; positivity)]
      case «variant» =>
        intro σ₂ k
        hoare_split 1
        refine hoare_seq (hoare_if_wp (At := fun _ => False) (fun _ h => h.elim)
          (hoare_assign_wp _ _ _)) ?_
        hoare_wp 1
        refine hoare_skip_of_imp fun σ h => ?_
        obtain ⟨hI, hf, hk⟩ := h
        have hn : (localVarLens "n" ℤ).get σ ≤ 0 := hI.2.2.1
        refine ⟨fun hlt => ?_, fun _ => ⟨hI, ?_⟩⟩
        · simp only [decide_eq_true_eq] at hlt
          have : (0 : ℤ) ≤ size ((localVarLens "z" (List Bool)).get σ ++
              ofblock ((localVarLens "sa" block).get σ)) := by simp only [size]; positivity
          exact absurd hlt (not_lt.mpr (hn.trans this))
        · have hf' : (localVarLens "finished" Bool).get σ = false := by simpa using hf
          rw [← hk]
          simp [hf']
      case exit =>
        rintro g₁ g₂ n₁ i₁ z₁ n₂ f₂ z₂ ⟨hg, rfl, hn, rfl⟩ -
        refine ⟨?_, hg, ?_⟩
        · simp only [decide_eq_false_iff_not, not_lt]
          have := (Int.ediv_lt_iff_lt_mul hr).mpr (show n₂ + r - 1 < 1 * r by omega)
          omega
        · simp [take, show n₂.toNat = 0 by omega]
      · equiv_skip
        rintro g₁ g₂ z₁ sa₁ sc₁ n₁ f₁ z₂ sa₂ sc₂ n₂ i₂ ⟨⟨hg, ⟨-, -, -, rfl⟩, -, rfl, -⟩, hn⟩
        exact ⟨hg, rfl, hn, rfl⟩
    · equiv_while_raw (eqGlob P §allGlobals{1} §allGlobals{2} ∧ ={z, sa, sc, n} ∧
          (§finished{1} = true ↔ §n{1} ≤ size §z{1}) ∧ size §z{1} = r * §i{2} ∧ 0 < §n{1} ∧
          0 ≤ §i{2})
      case body =>
        equiv_seq_last 1 1 : (eqGlob P §allGlobals{1} §allGlobals{2} ∧ ={z, sa, sc, n} ∧
          §finished{1} = false ∧ size §z{1} = r * §i{2} ∧ 0 < §n{1} ∧ 1 ≤ §i{2})
        · stmt_wp
          equiv_skip
          rintro g₁ g₂ z₁ sa₁ sc₁ n₁ f₁ z₂ sa₂ sc₂ n₂ i₂
            ⟨⟨hg, ⟨rfl, rfl, rfl, rfl⟩, -, hs, hn, hi⟩, hnf⟩
          refine ⟨hg, ⟨rfl, rfl, rfl, rfl⟩, by simpa using hnf, by rw [hsz, hs]; ring, hn, by omega⟩
        · equiv_if
          case guard =>
            rintro g₁ g₂ z₁ sa₁ sc₁ n₁ f₁ z₂ sa₂ sc₂ n₂ i₂ ⟨hg, ⟨rfl, rfl, rfl, rfl⟩, -, hs, hn, hi⟩
            rw [hs]
            exact decide_eq_decide.mpr (loop_cond i₂ n₁ (by omega) hn.le)
          case «then» =>
            equiv_call hPf
            equiv_skip
            rintro g₁ g₂ z₁ sa₁ sc₁ n₁ f₁ z₂ sa₂ sc₂ n₂ i₂
              ⟨⟨hg, ⟨rfl, rfl, rfl, rfl⟩, rfl, hs, hn, hi⟩, hlt⟩
            refine ⟨⟨rfl, hg⟩, ?_⟩
            rintro r₁ g₁' r₂ g₂' ⟨rfl, hg'⟩
            simp only [decide_eq_true_eq] at hlt
            exact ⟨hg', ⟨rfl, rfl, rfl, rfl⟩, by simp; omega, hs, hn, by omega⟩
          case «else» =>
            stmt_wp
            equiv_skip
            rintro g₁ g₂ z₁ sa₁ sc₁ n₁ f₁ z₂ sa₂ sc₂ n₂ i₂
              ⟨⟨hg, ⟨rfl, rfl, rfl, rfl⟩, rfl, hs, hn, hi⟩, hlt⟩
            simp only [decide_eq_false_iff_not] at hlt
            exact ⟨hg, ⟨rfl, rfl, rfl, rfl⟩, by simp; omega, hs, hn, by omega⟩
      case guard =>
        rintro g₁ g₂ z₁ sa₁ sc₁ n₁ f₁ z₂ sa₂ sc₂ n₂ i₂ ⟨hg, ⟨rfl, rfl, rfl, rfl⟩, hf, hs, hn, hi⟩
        have hl := loop_cond i₂ n₁ hi hn.le
        have key : f₁ = true ↔ ¬ r * i₂ < n₁ := by
          rw [hf, hs]; constructor <;> intro <;> omega
        rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_true_eq, ← hl]
        cases f₁ <;> simp at key ⊢ <;> omega
      case exit =>
        rintro g₁ g₂ z₁ sa₁ sc₁ n₁ f₁ z₂ sa₂ sc₂ n₂ i₂ ⟨hg, ⟨rfl, rfl, rfl, rfl⟩, -⟩ -
        exact ⟨hg, rfl⟩
      · equiv_skip
        rintro g₁ g₂ z₁ sa₁ sc₁ n₁ f₁ z₂ sa₂ sc₂ n₂ i₂
          ⟨⟨hg, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, hn⟩
        refine ⟨hg, ⟨rfl, rfl, rfl, rfl⟩, ?_, by simp [size], by omega, le_rfl⟩
        simp [size]; omega

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

/-- An `init` that does nothing (for `HYBRID_IRO_DIST.representable_of_f`). -/
noncomputable def noInit := proc () : Unit { return () }

/-- **A `HYBRID_IRO_DIST` that calls only `HI.f` is representable over `HI.f`**
(`HYBRID_IRO_DIST.ext`): EasyCrypt's `{HI.f}` restriction, derived from a congruence (`D HI` only
depends on `HI.f`).  The representation is the general one over all of `HI`'s procedures
(`Module.representable_of_firstOrder`), its `init` hole filled with `noInit`. -/
theorem HYBRID_IRO_DIST.representable_of_f (D : HYBRID_IRO_DIST)
    (hD : ∀ HI HI' : HYBRID_IRO, HYBRID_IRO.f HI = HYBRID_IRO.f HI' →
      Module.app D HI = Module.app D HI') :
    Module.Representable D HYBRID_IRO_DIST.ext := by
  have hne : ∀ T ∈ (procsig (List block, ℤ) -> (List Bool)).params, Nonempty T := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨[]⟩, ⟨0⟩⟩
  obtain ⟨p, hp⟩ := Module.representable_of_firstOrder (M := HYBRID_IRO)
    (by show HYBRID_IRO.typeRep.FirstOrder
        simp only [HYBRID_IRO.typeRep, ModuleTypeRep.FirstOrder, and_self])
    (fun n => by
      cases n with
      | zero => exact ⟨by simp, inferInstance⟩
      | succ n => cases n with
        | zero => exact ⟨hne, ⟨[]⟩⟩
        | succ n => nomatch n)
    (fun HI => ((HYBRID_IRO.init HI).procedure, (HYBRID_IRO.f HI).procedure)) (fun _ => rfl) D
  -- the `init` hole gets a procedure that does nothing, the `f` hole the wrapper of `HI.f`
  let q : ∀ {sig : ProcedureSignature}, HoleIndex (.cons (procsig () -> Unit)
      HYBRID_IRO_DIST.holes) sig → ProcedureWithHoles HYBRID_IRO_DIST.holes sig :=
    HoleIndex.consFun (F := ProcedureWithHoles HYBRID_IRO_DIST.holes)
      (ProcedureWithHoles.ofProc noInit)
      (HoleIndex.consFun (F := ProcedureWithHoles HYBRID_IRO_DIST.holes)
        (ProcedureWithHoles.ofHole .zero hne)
        (fun {_} (n : HoleIndex .empty _) => nomatch n))
  refine ⟨p.substHoles q, fun HI a => ?_, ?_⟩
  · let HI₀ : HYBRID_IRO := HYBRID_IRO.mk { init := Module.proc noInit, f := HYBRID_IRO.f HI }
    rw [hD HI HI₀ (by simp [HI₀]), hp.denote HI₀ a,
      p.procedureDenotation_substHoles q (noInit,
        (ProcedureWithHoles.ofHole (H := HYBRID_IRO_DIST.holes) .zero hne).instantiate
          (HYBRID_IRO_DIST.ext HI))
        (HYBRID_IRO_DIST.ext HI) (fun n => by
          cases n with
          | zero => exact (ProcedureWithHoles.ofProc_instantiate _ _).symm
          | succ n => cases n with
            | zero => rfl
            | succ n => nomatch n)]
    refine congrFun (p.procedureDenotation_instantiate_congr fun n => ?_) a
    cases n with
    | zero =>
      show procedureDenotation (HYBRID_IRO.init HI₀).procedure = procedureDenotation noInit
      simp [HI₀, Module.procedure_proc']
    | succ n => cases n with
      | zero =>
        refine Eq.trans ?_ (ProcedureWithHoles.procedureDenotation_ofHole _ _ _).symm
        show procedureDenotation (HYBRID_IRO.f HI₀).procedure =
          procedureDenotation (HYBRID_IRO.f HI).procedure
        simp [HI₀]
      | succ n => nomatch n
  · refine (FVP.fvP_proc_substHoles_le p q ⊥ fun n => ?_).trans (sup_le hp.fvP_le bot_le)
    cases n with
    | zero =>
      show FVP.fvP_proc (ProcedureWithHoles.ofProc noInit) ≤ ⊥
      rw [FVP.fvP_proc_ofProc]
      exact FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _
    | succ n => cases n with
      | zero => exact FVP.fvP_proc_ofHole_le _ _ ⊥
      | succ n => nomatch n

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

/-- `local lemma LRO_RO (D <: ERO.RO_Distinguisher {-ERO.RO, -ERO.FRO}) &m`.  `ERO.RO.m` and
`ERO.FRO.m` are distinct variables (exception E8). -/
theorem LRO_RO [Lens.Disjoint ERO_RO_m ERO_FRO_m] (D : ERO.RO_Distinguisher)
    (hD : Module.ECModule D ERO.RO_ext)
    (_hDd : FVP.fvP D ≤ (ERO_RO_m.footprint ⊔ ERO_FRO_m.footprint)ᶜ) (m : VariableAssignment) :
    Procedure.Pr (Module.app EROExper (Module.pair (ERO.LRO ERO_RO_m) D)).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (Module.app EROExper (Module.pair (ERO.RO ERO_RO_m) D)).procedure () m
        (fun r _ => r = true) := by
  have hcall := PROM.FullRO.FullEager.RO_LRO_D (List block × ℤ) Bool Unit Bool ERO.dout ERO_FRO_m
    (fun _ => dbool_ll) ERO_RO_m D hD _hDd
  -- EC: `byequiv => //; proc; seq 1 1 : (={glob D, ERO.RO.m}); first sim;
  -- by symmetry; call (FullEager.RO_LRO_D D _); auto; rewrite dbool_ll`
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ _ r₂ _ h => by rw [h]) rfl
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  equiv_sym
  stmt_wp
  equiv_call hcall
  stmt_wp
  equiv_skip
  rintro g _ rfl
  exact ⟨rfl, fun _ _ _ _ h => h.1.symm⟩

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
  -- EC: `proc; inline*; auto`
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  equiv_sim

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
  equiv_proc_to_stmt
  repeat stmt_inline{2} 0
  stmt_inline{1} 0
  stmt_wp
  equiv_seq_last 1 1 : (§x0{2} = (§xs0{1}, §i0{1}) ∧ §HybridIROLazy_mp{1} = §ERO_RO_m{2})
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
  -- EC: `proc; inline LRO.sample; sp; if => //`
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{2} 1
  stmt_wp
  equiv_seq_last 1 1 : (={xs0, n0, i, bs} ∧ §HybridIROLazy_mp{1} = §ERO_RO_m{2})
  · equiv_sim
    rintro _ _ _ _ _ _ ⟨h, rfl⟩
    exact ⟨Prod.mk.inj h, rfl⟩
  · equiv_if
    case «then» =>
      -- EC: `while{2} (true) (m{2} - i{2}); progress; auto; progress; smt()`: the invariant
      -- carries the relation the loop does not touch (EC folds it into the precondition)
      equiv_while_noframe{2} (§bs{1} = §bs{2} ∧ §HybridIROLazy_mp{1} = §ERO_RO_m{2})
        (§m{2} - §i{2}).toNat
      case lossless =>
        intro σ₁ σ _ _
        simp [Stmt.ewp_seq, Stmt.ewp_assign]
      case «variant» =>
        intro σ₁ k
        hoare_wp 3
        hoare_skip
        rintro bs mp i m ⟨h, hc, rfl⟩
        refine ⟨h, ?_⟩
        simp only [decide_eq_true_eq] at hc
        omega
      case exit =>
        intro _ _ _ _ _ _ h _
        exact h
      -- EC: `while (={xs, n, i, bs} /\ HybridIROLazy.mp{1} = ERO.RO.m{2}); wp;
      -- call HybridIROLazy_fill_in_LRO_get; auto`
      equiv_while_raw (={xs0, n0, i, bs} ∧ §HybridIROLazy_mp{1} = §ERO_RO_m{2})
      case body =>
        stmt_wp
        equiv_call (HybridIROLazy_fill_in_LRO_get HybridIROLazy_mp ERO_RO_m)
        equiv_skip
        rintro xs n i bs mp _ _ _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩, -⟩
        exact ⟨⟨rfl, rfl⟩, fun r₁ g₁ r₂ g₂ ⟨hr, hg⟩ => ⟨⟨rfl, rfl, rfl, hr ▸ rfl⟩, hg⟩⟩
      case guard => simp_all
      case exit => simp_all
      equiv_skip
      simp_all
    case «else» =>
      equiv_skip
      simp_all
    case guard => simp_all

/-- `local lemma HIRO_RO_HybridIROEager_init : equiv[HIRO(ERO.RO).init ~ HybridIROEager.init :
true ==> ={res} /\ ERO.RO.m{1} = HybridIROEager.mp{2}]`. -/
theorem HIRO_RO_HybridIROEager_init :
    prhlProc (fun _ _ _ _ => True)
      (Module.app HIRO.init (ERO.RO ERO_RO_m)).procedure
      (HybridIROEager.init HybridIROEager_mp).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ERO_RO_m.get g₁ = HybridIROEager_mp.get g₂) := by
  -- EC: `proc; inline*; auto`
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  equiv_sim

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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§x0{1} = (§xs0{2}, §i0{2}) ∧ §ERO_RO_m{1} = §HybridIROEager_mp{2})
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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§x1{1} = (§xs0{2}, §i0{2}) ∧ §ERO_RO_m{1} = §HybridIROEager_mp{2})
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
  -- EC: `proc; sp; if => //`
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (={xs0, n0, m, i, bs} ∧ §ERO_RO_m{1} = §HybridIROEager_mp{2})
  · equiv_sim
    rintro _ _ _ _ _ _ ⟨h, rfl⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  · equiv_if
    case «then» =>
      -- EC: `while (={i, m, xs} /\ ERO.RO.m{1} = HybridIROEager.mp{2}); wp;
      -- call RO_sample_HybridIROEager_fill_in; auto` (`bs` in the invariant: EC frames it)
      equiv_while_raw (={xs0, m, i, bs} ∧ §ERO_RO_m{1} = §HybridIROEager_mp{2})
      case body =>
        stmt_wp
        equiv_call (RO_sample_HybridIROEager_fill_in HybridIROEager_mp ERO_RO_m)
        equiv_skip
        rintro σ₁ σ₂ ⟨⟨⟨h1, h2, h3, h4⟩, h5⟩, -⟩
        exact ⟨⟨by rw [h1, h3], h5⟩, fun _ _ _ _ hg => ⟨⟨h1, h2, congrArg (· + 1) h3, h4⟩, hg⟩⟩
      case guard => simp_all
      case exit => simp_all
      -- EC: `while (={i, n, xs, bs} /\ ERO.RO.m{1} = HybridIROEager.mp{2}); wp;
      -- call RO_get_HybridIROEager_fill_in; auto` (`m` in the invariant: EC frames it)
      equiv_while_raw (={xs0, n0, m, i, bs} ∧ §ERO_RO_m{1} = §HybridIROEager_mp{2})
      case body =>
        stmt_wp
        equiv_call (RO_get_HybridIROEager_fill_in HybridIROEager_mp ERO_RO_m)
        equiv_skip
        rintro xs n m i bs mp _ _ _ _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, -⟩
        exact ⟨⟨rfl, rfl⟩, fun r₁ g₁ r₂ g₂ ⟨hr, hg⟩ => ⟨⟨rfl, rfl, rfl, rfl, hr ▸ rfl⟩, hg⟩⟩
      case guard => simp_all
      case exit => simp_all
      equiv_skip
      simp_all
    case «else» =>
      equiv_skip
      simp_all
    case guard => simp_all

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

/-- `RODist(D)` is an EasyCrypt-like `RO_Distinguisher` (EC: by construction): representable
over all of `RO`'s procedures (`RO_Distinguisher.representable`), and its globals are `D`'s. -/
theorem RODist.ecModule (D : HYBRID_IRO_DIST) (hD : Module.ECModule D HYBRID_IRO_DIST.ext) :
    Module.ECModule (RODist D) ERO.RO_ext :=
  PROM.FullRO.RO_Distinguisher.ecModule _ _ _ _ (RODist D)
    (hD.finitelySupported.mono (fvP_RODist_le D))

/-- `local lemma Exper_HybridIROLazy_LRO &m`, for the section's `D`.  `ERO.RO.m` and
`HybridIROLazy.mp` are distinct variables (exception E8: `Lens.Disjoint`). -/
theorem Exper_HybridIROLazy_LRO [Lens.Disjoint HybridIROLazy_mp ERO_RO_m] (D : HYBRID_IRO_DIST)
    (hD : Module.ECModule D HYBRID_IRO_DIST.ext)
    (_hDd : DRestrictions HybridIROLazy_mp HybridIROEager_mp D)
    (_hERO : FVP.fvP D ≤ (ERO_RO_m.footprint)ᶜ) (m : VariableAssignment) :
    Procedure.Pr (Module.app HybridIROExper (Module.pair (HybridIROLazy.asHI HybridIROLazy_mp) D)
        ).procedure () m (fun r _ => r = true) =
      Procedure.Pr (Module.app EROExper (Module.pair (ERO.LRO ERO_RO_m) (RODist D))).procedure ()
        m (fun r _ => r = true) := by
  unfold DRestrictions at _hDd
  have hmp : HybridIROLazy_mp.footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hm : ERO_RO_m.footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hL : FVP.fvP D ≤ ((Lens.pair HybridIROLazy_mp ERO_RO_m).footprint)ᶜ := by
    rw [Footprint.lens_pair]; exact Footprint.le_compl_of_fvP (sup_le hmp hm)
  -- EC's `call (_ : HybridIROLazy.mp{1} = ERO.RO.m{2}); conseq HybridIROLazy_HIRO_LRO_f`:
  -- `={glob D}` across the oracles by the syntactic frame (`writes_keep`)
  have hAcall := prhlProc_abstract_call_module (Lens.pair HybridIROLazy_mp ERO_RO_m) D
    HYBRID_IRO_DIST.ext hD.representable hL (fun a b => a.1 = b.2)
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable (List block × ℤ))
      | succ m => nomatch m)
    (HybridIROLazy.asHI HybridIROLazy_mp) (Module.app HIRO (ERO.LRO ERO_RO_m)) (fun n => by
      cases n with
      | zero =>
        simp only [HYBRID_IRO_DIST.ext, HoleSigs.Instantiation.lookup_zero_single]
        refine prhlProc_globInvF_of_writesKeep _ (by writes_keep) (by writes_keep) ?_
        simp only [HybridIROLazy.asHI, HYBRID_IRO.f.mk_simp, HIRO.apply_simp]
        exact HybridIROLazy_HIRO_LRO_f HybridIROLazy_mp ERO_RO_m
      | succ m => nomatch m)
  -- EC: `byequiv => //; proc; inline*; wp; seq 1 1 : (={glob D} /\ HybridIROLazy.mp{1} =
  -- ERO.RO.m{2}); first auto; call (…); auto`
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ _ r₂ _ h => by rw [h]) rfl
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_call hAcall
  stmt_wp
  equiv_skip
  rintro g _ rfl
  refine ⟨⟨?_, ?_⟩, fun _ _ _ _ h => h.1⟩
  · rw [touched_set_of_le_compl hmp, touched_set_of_le_compl hm]
  · simp [Lens.set_get]

/-- `local lemma Exper_RO_HybridIROEager &m`, for the section's `D`.  `ERO.RO.m` and
`HybridIROEager.mp` are distinct variables (exception E8: `Lens.Disjoint`). -/
theorem Exper_RO_HybridIROEager [Lens.Disjoint ERO_RO_m HybridIROEager_mp] (D : HYBRID_IRO_DIST)
    (hD : Module.ECModule D HYBRID_IRO_DIST.ext)
    (_hDd : DRestrictions HybridIROLazy_mp HybridIROEager_mp D)
    (_hERO : FVP.fvP D ≤ (ERO_RO_m.footprint)ᶜ) (m : VariableAssignment) :
    Procedure.Pr (Module.app EROExper (Module.pair (ERO.RO ERO_RO_m) (RODist D))).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (Module.app HybridIROExper
        (Module.pair (HybridIROEager.asHI HybridIROEager_mp) D)).procedure () m
        (fun r _ => r = true) := by
  unfold DRestrictions at _hDd
  have hm : ERO_RO_m.footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hmp : HybridIROEager_mp.footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hL : FVP.fvP D ≤ ((Lens.pair ERO_RO_m HybridIROEager_mp).footprint)ᶜ := by
    rw [Footprint.lens_pair]; exact Footprint.le_compl_of_fvP (sup_le hm hmp)
  -- EC's `call (_ : ERO.RO.m{1} = HybridIROEager.mp{2}); conseq HIRO_RO_HybridIROEager_f`
  have hAcall := prhlProc_abstract_call_module (Lens.pair ERO_RO_m HybridIROEager_mp) D
    HYBRID_IRO_DIST.ext hD.representable hL (fun a b => a.1 = b.2)
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable (List block × ℤ))
      | succ m => nomatch m)
    (Module.app HIRO (ERO.RO ERO_RO_m)) (HybridIROEager.asHI HybridIROEager_mp) (fun n => by
      cases n with
      | zero =>
        simp only [HYBRID_IRO_DIST.ext, HoleSigs.Instantiation.lookup_zero_single]
        refine prhlProc_globInvF_of_writesKeep _ (by writes_keep) (by writes_keep) ?_
        simp only [HybridIROEager.asHI, HYBRID_IRO.f.mk_simp, HIRO.apply_simp]
        exact HIRO_RO_HybridIROEager_f HybridIROEager_mp ERO_RO_m
      | succ m => nomatch m)
  -- EC: `byequiv => //; proc; inline*; wp; seq 1 1 : (={glob D} /\ ERO.RO.m{1} =
  -- HybridIROEager.mp{2}); first auto; call (…); auto`
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ _ r₂ _ h => by rw [h]) rfl
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_call hAcall
  stmt_wp
  equiv_skip
  rintro g _ rfl
  refine ⟨⟨?_, ?_⟩, fun _ _ _ _ h => h.1⟩
  · rw [touched_set_of_le_compl hmp, touched_set_of_le_compl hm]
  · simp [Lens.set_get]

/-- EC's `HybridIROExper_Lazy_Eager' &m`, for the section's `D`.  Not local: it does not mention
`ERO` (whose variables its proof takes fresh). -/
theorem HybridIROExper_Lazy_Eager'
    (hLazy : HybridIROLazy_mp.footprint.FinitelySupported)
    (hEager : HybridIROEager_mp.footprint.FinitelySupported) (D : HYBRID_IRO_DIST)
    (hD : Module.ECModule D HYBRID_IRO_DIST.ext)
    (_hDd : DRestrictions HybridIROLazy_mp HybridIROEager_mp D) (m : VariableAssignment) :
    Procedure.Pr (Module.app HybridIROExper (Module.pair (HybridIROLazy.asHI HybridIROLazy_mp) D)
        ).procedure () m (fun r _ => r = true) =
      Procedure.Pr (Module.app HybridIROExper
        (Module.pair (HybridIROEager.asHI HybridIROEager_mp) D)).procedure () m
        (fun r _ => r = true) := by
  -- the local clone `ERO`'s variables, fresh (exception E6)
  have hF := (hD.finitelySupported.sup hLazy).sup hEager
  haveI : Nonempty (FMap (List block × ℤ) Bool) := ⟨FMap.empty⟩
  haveI : Nonempty (FMap (List block × ℤ) (Bool × PROM.flag)) := ⟨FMap.empty⟩
  obtain ⟨ERO_RO_m, hRO, hROfs⟩ := Footprint.exists_fresh (FMap (List block × ℤ) Bool) hF
  obtain ⟨ERO_FRO_m, hFRO', -⟩ := Footprint.exists_fresh (FMap (List block × ℤ) (Bool × PROM.flag))
    (hD.finitelySupported.sup hROfs)
  have hFRO : ERO_FRO_m.footprint ≤ (FVP.fvP D)ᶜ :=
    hFRO'.trans (Footprint.compl_antimono le_sup_left)
  haveI : Lens.Disjoint ERO_RO_m ERO_FRO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp
      (hFRO'.trans (Footprint.compl_antimono le_sup_right)))
  have hRO_D : FVP.fvP D ≤ (ERO_RO_m.footprint)ᶜ := (Footprint.le_compl_comm _ _).mp
    (hRO.trans (Footprint.compl_antimono (le_sup_left.trans le_sup_left)))
  have hFRO_D : FVP.fvP D ≤ (ERO_FRO_m.footprint)ᶜ := (Footprint.le_compl_comm _ _).mp hFRO
  haveI : Lens.Disjoint HybridIROLazy_mp ERO_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp
      (hRO.trans (Footprint.compl_antimono (le_sup_right.trans le_sup_left))))
  haveI : Lens.Disjoint ERO_RO_m HybridIROEager_mp :=
    Lens.disjoint_of_footprint_le_compl _ _
      (hRO.trans (Footprint.compl_antimono le_sup_right))
  -- EC: `rewrite (Exper_HybridIROLazy_LRO &m) (LRO_RO RODist &m) (Exper_RO_HybridIROEager &m)`
  rw [Exper_HybridIROLazy_LRO HybridIROLazy_mp HybridIROEager_mp ERO_RO_m D hD _hDd hRO_D m,
    LRO_RO ERO_RO_m ERO_FRO_m (RODist D) (RODist.ecModule D hD)
      ((fvP_RODist_le D).trans ((Footprint.le_compl_comm _ _).mpr
        (sup_le ((Footprint.le_compl_comm _ _).mp hRO_D)
          ((Footprint.le_compl_comm _ _).mp hFRO_D)))) m,
    Exper_RO_HybridIROEager HybridIROLazy_mp HybridIROEager_mp ERO_RO_m D hD _hDd hRO_D m]

end LazyEager

section Hybrid

-- one binder each: a `module` takes a whole binder group when it mentions one of its names
variable (HybridIROLazy_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)
  (HybridIROEager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)

/-- EC's `HybridIROExper_Lazy_Eager (D <: HYBRID_IRO_DIST {-HybridIROEager, -HybridIROLazy}) &m`. -/
theorem HybridIROExper_Lazy_Eager
    (hLazy : HybridIROLazy_mp.footprint.FinitelySupported)
    (hEager : HybridIROEager_mp.footprint.FinitelySupported) (D : HYBRID_IRO_DIST)
    (hD : Module.ECModule D HYBRID_IRO_DIST.ext)
    (_hDd : DRestrictions HybridIROLazy_mp HybridIROEager_mp D) (m : VariableAssignment) :
    Procedure.Pr (Module.app HybridIROExper (Module.pair (HybridIROLazy.asHI HybridIROLazy_mp) D)
        ).procedure () m (fun r _ => r = true) =
      Procedure.Pr (Module.app HybridIROExper
        (Module.pair (HybridIROEager.asHI HybridIROEager_mp) D)).procedure () m
        (fun r _ => r = true) :=
  -- EC: `apply (HybridIROExper_Lazy_Eager' D &m)`
  HybridIROExper_Lazy_Eager' HybridIROLazy_mp HybridIROEager_mp hLazy hEager D hD _hDd m

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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§xs{1} = §xs0{2} ∧ §n{1} * r = §n0{2} ∧ §ys{1} = [] ∧ §bs0{2} = [] ∧
      §i{2} = 0 ∧ §obs{1} = unpad_blocks §xs{1} ∧ lazy_invar §BIRO.IRO.mp{1} §HybridIROLazy_mp{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard =>
      rintro _ _ _ _ _ _ _ _ _ _ ⟨rfl, -, -, -, -, rfl, -⟩
      simp [valid_block]
    case «else» =>
      equiv_skip
      rintro _ _ _ _ _ _ _ _ _ _ ⟨⟨-, -, rfl, rfl, -, -, li⟩, -⟩
      exact ⟨bits2blocks_nil.symm, li⟩
    case «then» =>
      stmt_wp
      equiv_seq_last 1 1 : (pad2blocks §x0{1} = §xs0{2} ∧ §n0{1} = §n0{2} ∧ §i{1} = §i{2} ∧
          §bs{1} = §bs0{2} ∧ lazy_invar §BIRO.IRO.mp{1} §HybridIROLazy_mp{2})
      · stmt_wp
        equiv_skip
        rintro xs₁ _ _ obs _ _ _ _ _ _ ⟨⟨rfl, rfl, -, rfl, rfl, rfl, li⟩, h⟩
        refine ⟨?_, rfl, rfl, rfl, li⟩
        simp only [decide_eq_true_eq] at h
        obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp h
        have := unpadBlocksK xs₁
        rw [hy] at this ⊢
        exact this
      · equiv_if{1}
        case «else» =>
          refine prhlStmt_conseq prhlStmt_false (fun _ _ h => ?_) (fun _ _ h => h)
          simp [BIRO.valid, valid_toplevel] at h
        case «then» =>
          equiv_while_raw (pad2blocks §x0{1} = §xs0{2} ∧ §n0{1} = §n0{2} ∧ §i{1} = §i{2} ∧
              §bs{1} = §bs0{2} ∧ lazy_invar §BIRO.IRO.mp{1} §HybridIROLazy_mp{2})
          case body =>
            stmt_wp
            equiv_seq_last 1 1 : (pad2blocks §x0{1} = §xs0{2} ∧ §n0{1} = §n0{2} ∧ §i{1} = §i{2} ∧
              §bs{1} = §bs0{2} ∧ lazy_invar §BIRO.IRO.mp{1} §HybridIROLazy_mp{2} ∧
              §x1{1} = §x0{1} ∧ §n1{1} = §i{1} ∧ §xs1{2} = §xs0{2} ∧ §i0{2} = §i{2})
            · stmt_wp
              equiv_skip
              rintro _ _ _ _ _ _ _ _ _ _ ⟨h, -⟩; exact h
            · equiv_if
              case guard =>
                rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, li, rfl, rfl, rfl, rfl⟩
                simp only [Bool.not_inj_iff, decide_eq_decide]
                exact li.1 _ _
              case «else» =>
                equiv_skip
                rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, li, rfl, rfl, rfl, rfl⟩, h⟩
                simp only [Bool.not_eq_false', decide_eq_true_eq] at h
                exact ⟨rfl, rfl, rfl, by rw [lazy_invar_lookup_eq _ _ _ _ li h], li⟩
              case «then» =>
                stmt_wp
                equiv_rnd
                equiv_skip
                rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  ⟨⟨rfl, rfl, rfl, rfl, li, rfl, rfl, rfl, rfl⟩, -⟩ b -
                refine ⟨rfl, rfl, rfl, by simp [FMap.get_set_sameE], ?_, ?_, ?_⟩
                · exact fun bs n => lazy_invar_upd_mem_dom_iff _ _ _ _ _ _ _ li
                · exact fun xs n => lazy_invar_upd2_vb _ _ _ _ _ _ _ li
                · exact fun bs n => lazy_invar_upd_lu_eq _ _ _ _ _ _ _ li
          case guard =>
            rintro _ _ _ _ _ _ _ _ _ _ ⟨-, rfl, rfl, -⟩; rfl
          case exit =>
            rintro _ _ _ _ _ _ _ _ _ _ ⟨-, -, -, rfl, li⟩ -; exact ⟨rfl, li⟩
          · equiv_skip
            rintro _ _ _ _ _ _ _ _ _ _ ⟨h, -⟩; exact h

/-- `lemma IRO_RaiseHybridIRO_HybridIROLazy_f : equiv[IRO.f ~ RaiseHybridIRO(HybridIROLazy).f :
={n} /\ x{1} = bs{2} /\ lazy_invar IRO.mp{1} HybridIROLazy.mp{2} ==>
={res} /\ lazy_invar IRO.mp{1} HybridIROLazy.mp{2}]`. -/
theorem IRO_RaiseHybridIRO_HybridIROLazy_f :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ lazy_invar (BIRO.IRO.mp.get g₁) (HybridIROLazy_mp.get g₂))
      BIRO.IRO.f.procedure
      (Module.app RaiseHybridIRO.f (HybridIROLazy.asHI HybridIROLazy_mp)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ lazy_invar (BIRO.IRO.mp.get g₁) (HybridIROLazy_mp.get g₂)) := by
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§(localVarLens "x" (List Bool)){1} = §bs{2} ∧ §xs{2} = pad2blocks §bs{2} ∧
      §n{1} = §n0{2} ∧ §i{1} = §i{2} ∧ §bs{1} = §bs0{2} ∧
      lazy_invar §BIRO.IRO.mp{1} §HybridIROLazy_mp{2})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ ⟨rfl, h⟩
    exact ⟨rfl, rfl, h⟩
  · equiv_if
    case guard =>
      rintro _ _ _ _ _ _ _ _ _ _ _ ⟨-, rfl, -⟩
      simp [BIRO.valid, valid_toplevel, valid_pad2blocks]
    case «else» => equiv_skip; intros; simp_all
    case «then» =>
      equiv_while_raw (§xs{2} = pad2blocks §(localVarLens "x" (List Bool)){1} ∧ §n{1} = §n0{2} ∧
          §i{1} = §i{2} ∧ §bs{1} = §bs0{2} ∧ lazy_invar §BIRO.IRO.mp{1} §HybridIROLazy_mp{2})
      case body =>
        stmt_wp
        equiv_seq_last 1 1 : (§xs{2} = pad2blocks §(localVarLens "x" (List Bool)){1} ∧
          §n{1} = §n0{2} ∧ §i{1} = §i{2} ∧ §bs{1} = §bs0{2} ∧
          lazy_invar §BIRO.IRO.mp{1} §HybridIROLazy_mp{2} ∧
          §x0{1} = §(localVarLens "x" (List Bool)){1} ∧
          §n0{1} = §i{1} ∧ §xs0{2} = §xs{2} ∧ §i0{2} = §i{2})
        · stmt_wp
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ ⟨h, -⟩; exact h
        · equiv_if
          case guard =>
            rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, li, rfl, rfl, rfl, rfl⟩
            simp only [Bool.not_inj_iff, decide_eq_decide]
            exact li.1 _ _
          case «else» =>
            equiv_skip
            rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, li, rfl, rfl, rfl, rfl⟩, h⟩
            simp only [Bool.not_eq_false', decide_eq_true_eq] at h
            exact ⟨rfl, rfl, rfl, by rw [lazy_invar_lookup_eq _ _ _ _ li h], li⟩
          case «then» =>
            stmt_wp
            equiv_rnd
            equiv_skip
            rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, li, rfl, rfl, rfl, rfl⟩, -⟩ b -
            refine ⟨rfl, rfl, rfl, by simp [FMap.get_set_sameE], ?_, ?_, ?_⟩
            · exact fun bs n => lazy_invar_upd_mem_dom_iff _ _ _ _ _ _ _ li
            · exact fun xs n => lazy_invar_upd2_vb _ _ _ _ _ _ _ li
            · exact fun bs n => lazy_invar_upd_lu_eq _ _ _ _ _ _ _ li
      case guard =>
        rintro _ _ _ _ _ _ _ _ _ _ ⟨-, rfl, rfl, -⟩; rfl
      case exit =>
        rintro _ _ _ _ _ _ _ _ _ _ ⟨-, -, -, h, li⟩ -; exact ⟨h, li⟩
      · equiv_skip
        rintro _ _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, h⟩, -⟩; exact h

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
  -- EC: `inline*`, `seq 5 3`, then `if`, and the two loops in lockstep
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§xs1{1} = §xs0{2} ∧ §n1{1} = §n0{2} ∧ §m{1} = §m{2} ∧ §i{1} = §i{2} ∧
      §bs0{1} = §bs{2} ∧ §HybridIROEager_mp{1} = §HybridIROEager_mp{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» => equiv_skip; intros; simp_all
    case «then» =>
      equiv_seq_last 1 1 : (§xs1{1} = §xs0{2} ∧ §n1{1} = §n0{2} ∧ §m{1} = §m{2} ∧ §i{1} = §i{2} ∧
          §bs0{1} = §bs{2} ∧ §HybridIROEager_mp{1} = §HybridIROEager_mp{2})
      · equiv_while_raw (§xs1{1} = §xs0{2} ∧ §n1{1} = §n0{2} ∧ §m{1} = §m{2} ∧ §i{1} = §i{2} ∧
            §bs0{1} = §bs{2} ∧ §HybridIROEager_mp{1} = §HybridIROEager_mp{2})
        case body =>
          stmt_wp
          equiv_seq_last 1 1 : ((§xs1{1} = §xs0{2} ∧ §n1{1} = §n0{2} ∧ §m{1} = §m{2} ∧ §i{1} = §i{2} ∧
              §bs0{1} = §bs{2} ∧ §HybridIROEager_mp{1} = §HybridIROEager_mp{2}) ∧
              §xs2{1} = §xs1{1} ∧ §i0{1} = §i{1} ∧ §xs1{2} = §xs0{2} ∧ §i0{2} = §i{2})
          · stmt_wp
            equiv_skip
            intros; simp_all
          · equiv_if
            case guard => intros; simp_all
            case «else» => equiv_skip; intros; simp_all
            case «then» =>
              stmt_wp
              equiv_rnd
              equiv_skip
              intros; simp_all
        case guard => intros; simp_all
        case exit => intros; simp_all
        · equiv_skip; intros; simp_all
      · equiv_while_raw (§xs1{1} = §xs0{2} ∧ §n1{1} = §n0{2} ∧ §m{1} = §m{2} ∧ §i{1} = §i{2} ∧
            §bs0{1} = §bs{2} ∧ §HybridIROEager_mp{1} = §HybridIROEager_mp{2})
        case body =>
          stmt_wp
          equiv_seq_last 1 1 : ((§xs1{1} = §xs0{2} ∧ §n1{1} = §n0{2} ∧ §m{1} = §m{2} ∧ §i{1} = §i{2} ∧
              §bs0{1} = §bs{2} ∧ §HybridIROEager_mp{1} = §HybridIROEager_mp{2}) ∧
              §xs3{1} = §xs1{1} ∧ §i1{1} = §i{1} ∧ §xs2{2} = §xs0{2} ∧ §i1{2} = §i{2})
          · stmt_wp
            equiv_skip
            intros; simp_all
          · equiv_if
            case guard => intros; simp_all
            case «else» => equiv_skip; intros; simp_all
            case «then» =>
              stmt_wp
              equiv_rnd
              equiv_skip
              intros; simp_all
        case guard => intros; simp_all
        case exit => intros; simp_all
        · equiv_skip; intros; simp_all

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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  have hr := gt0_r
  equiv_seq_last 1 1 : (§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧ §bs0{1} = §bs0{2} ∧
      §HybridIROEager_mp{1} = §HybridIROEager_mp{2} ∧ §m0{1} = §i0{1} + r ∧
      size §bs0{1} = §i0{1} ∧ block_bits_dom_all_in_or_out §xs0{1} §i0{1} §HybridIROEager_mp{1})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ _ _ _ _ _ _ ⟨⟨⟩, rfl, hm, hs, hb⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl, hm, hs, hb⟩
  · equiv_if{2}
    case «then» =>
      equiv_while_raw (§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧ §bs0{1} = §bs0{2} ∧
          §HybridIROEager_mp{1} = §HybridIROEager_mp{2} ∧ §i0{1} ≤ §m0{1} ∧
          ∀ j, §i0{1} ≤ j ∧ j < §m0{1} → FMap.dom §HybridIROEager_mp{1} (§xs0{1}, j))
      case body =>
        stmt_wp
        equiv_seq_last 1 0 : (§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧
          §bs0{1} = §bs0{2} ∧ §HybridIROEager_mp{1} = §HybridIROEager_mp{2} ∧ §i0{1} < §m0{1} ∧
          (∀ j, §i0{1} ≤ j ∧ j < §m0{1} → FMap.dom §HybridIROEager_mp{1} (§xs0{1}, j)) ∧
          §xs1{1} = §xs0{1} ∧ §i1{1} = §i0{1})
        · stmt_wp
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, -, hall⟩, hg⟩
          simp only [decide_eq_true_eq] at hg
          exact ⟨rfl, rfl, rfl, rfl, rfl, hg, hall⟩
        · equiv_if{1}
          case «then» =>
            refine prhlStmt_conseq prhlStmt_false (fun _ _ h => ?_) (fun _ _ h => h)
            obtain ⟨⟨-, -, -, -, -, hlt, hall, hx, hi⟩, hd⟩ := h
            simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hd
            rw [hx, hi] at hd
            exact hd (hall _ ⟨le_rfl, hlt⟩)
          case «else» =>
            equiv_skip
            rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, hlt, hall, rfl, rfl⟩, -⟩
            exact ⟨rfl, rfl, rfl, rfl, rfl, by omega, fun j hj => hall j ⟨by omega, hj.2⟩⟩
      case guard => intros; simp_all
      case exit =>
        rintro _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, -⟩ -
        exact ⟨rfl, rfl⟩
      · equiv_skip
        rintro _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, hm, -, hb⟩, hd⟩
        simp only [decide_eq_true_eq] at hd
        exact ⟨rfl, rfl, rfl, rfl, rfl, by omega,
          fun j hj => block_bits_dom_first_in_imp_all_in _ _ _ hb hd j ⟨hj.1, by omega⟩⟩
    case «else» =>
      equiv_seq_last 0 1 : (§xs0{1} = §xs0{2} ∧ §m0{1} = §m0{2} ∧ §bs0{1} = §bs0{2} ∧
          §i0{2} = §m0{1} - r ∧ §i0{1} = §m0{1} ∧ size §bs0{1} = §m0{1} ∧
          (∀ k, §m0{1} - r ≤ k ∧ k < §m0{1} →
            FMap.get §HybridIROEager_mp{1} (§xs0{1}, k) = some (nth true §bs0{1} k)) ∧
          eager_eq_except §xs0{1} (§m0{1} - r) §m0{1} §HybridIROEager_mp{1} §HybridIROEager_mp{2})
      · stmt_wp
        equiv_seq_last 1 1 : (§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧
            §bs0{1} = §bs0{2} ∧ §j{2} = 0 ∧ §cs{2} = [] ∧ §m0{1} = §i0{1} + r ∧
            size §bs0{1} = §i0{1} ∧
            (∀ k, §i0{1} ≤ k ∧ k < §m0{1} → ¬ FMap.dom §HybridIROEager_mp{1} (§xs0{1}, k)) ∧
            §HybridIROEager_mp{1} = §HybridIROEager_mp{2})
        · stmt_wp
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, hm, hs, hb⟩, hd⟩
          simp only [decide_eq_false_iff_not] at hd
          exact ⟨rfl, rfl, rfl, rfl, hm, hs,
            fun k hk => block_bits_dom_first_out_imp_all_out _ _ _ hb hd k ⟨hk.1, by omega⟩, rfl⟩
        · equiv_while_raw (§xs0{1} = §xs0{2} ∧ §m0{1} = §m0{2} ∧ §i0{2} = §m0{1} - r ∧
              §i0{2} ≤ §i0{1} ∧ §i0{1} ≤ §m0{1} ∧ §i0{1} - §i0{2} = §j{2} ∧
              size §bs0{1} = §i0{1} ∧ §bs0{1} = §bs0{2} ++ §cs{2} ∧
              (∀ k, §i0{2} ≤ k ∧ k < §i0{1} →
                FMap.get §HybridIROEager_mp{1} (§xs0{1}, k) = some (nth true §bs0{1} k)) ∧
              (∀ k, §i0{1} ≤ k ∧ k < §m0{1} → ¬ FMap.dom §HybridIROEager_mp{1} (§xs0{1}, k)) ∧
              eager_eq_except §xs0{1} §i0{2} §m0{1} §HybridIROEager_mp{1} §HybridIROEager_mp{2})
          case body =>
            stmt_wp
            equiv_seq_last 1 1 : ((§xs0{1} = §xs0{2} ∧ §m0{1} = §m0{2} ∧ §i0{2} = §m0{1} - r ∧
                §i0{2} ≤ §i0{1} ∧ §i0{1} ≤ §m0{1} ∧ §i0{1} - §i0{2} = §j{2} ∧
                size §bs0{1} = §i0{1} ∧ §bs0{1} = §bs0{2} ++ §cs{2} ∧
                (∀ k, §i0{2} ≤ k ∧ k < §i0{1} →
                  FMap.get §HybridIROEager_mp{1} (§xs0{1}, k) = some (nth true §bs0{1} k)) ∧
                (∀ k, §i0{1} ≤ k ∧ k < §m0{1} →
                  ¬ FMap.dom §HybridIROEager_mp{1} (§xs0{1}, k)) ∧
                eager_eq_except §xs0{1} §i0{2} §m0{1} §HybridIROEager_mp{1}
                  §HybridIROEager_mp{2}) ∧
                §i0{1} < §m0{1} ∧ §xs1{1} = §xs0{1} ∧ §i1{1} = §i0{1})
            · stmt_wp
              equiv_skip
              rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨h, hg⟩
              simp only [decide_eq_true_eq] at hg
              exact ⟨h, hg⟩
            · equiv_if{1}
              case «then» =>
                stmt_wp
                equiv_rnd
                equiv_skip
                rintro _ m _ _ mp xs i _ _ _ _ _ _ _
                  ⟨⟨⟨rfl, rfl, rfl, h1, h2, rfl, hs, rfl, hget, hnd, hee⟩, hlt, rfl, rfl⟩, -⟩ a -
                have e : oget (FMap.get (FMap.set mp (xs, i) a) (xs, i)) = a := by
                  simp [FMap.get_set_sameE, oget]
                rw [e]
                refine ⟨rfl, rfl, rfl, by omega, by omega, by omega, ?_, by simp [rcons], ?_, ?_,
                  eager_eq_except_upd1_eq_in _ _ _ _ _ _ _ hee (by omega) (by omega)⟩
                · simp only [size, rcons, List.length_append, List.length_singleton] at hs ⊢
                  push_cast; omega
                · intro k hk
                  rw [nth_rcons]
                  by_cases hki : k = i
                  · subst hki
                    rw [FMap.get_set_sameE, if_neg (by omega), if_pos (by omega)]
                  · rw [FMap.get_setE, if_neg (by rintro ⟨⟩; exact hki rfl), if_pos (by omega)]
                    exact hget k ⟨hk.1, by omega⟩
                · intro k hk hd
                  rcases (FMap.mem_set _ _ _ _).mp hd with hd | hd
                  · exact hnd k ⟨by omega, hk.2⟩ hd
                  · simp only [Prod.mk.injEq] at hd; omega
              case «else» =>
                refine prhlStmt_conseq prhlStmt_false (fun _ _ h => ?_) (fun _ _ h => h)
                obtain ⟨⟨⟨-, -, -, -, -, -, -, -, -, hnd, -⟩, hlt, hx, hi⟩, hd⟩ := h
                simp only [Bool.not_eq_false', decide_eq_true_eq] at hd
                rw [hx, hi] at hd
                exact hnd _ ⟨le_rfl, hlt⟩ hd
          case guard =>
            rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨-, -, rfl, -, -, rfl, -⟩
            rw [decide_eq_decide]; omega
          case exit =>
            rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, h1, h2, rfl, hs, rfl, hget, -, hee⟩ hg
            simp only [decide_eq_false_iff_not, not_lt] at hg
            exact ⟨rfl, rfl, rfl, rfl, by omega, by omega, fun k hk => hget k ⟨hk.1, by omega⟩,
              hee⟩
          · equiv_skip
            rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, hm, hs, hnd, rfl⟩
            exact ⟨rfl, rfl, by omega, le_rfl, by omega, by omega, hs, (List.append_nil _).symm,
              fun k hk => absurd hk.2 (by omega), hnd, fun _ _ _ => rfl⟩
      · equiv_while_noframe{2} (§xs0{1} = §xs0{2} ∧ §m0{1} = §m0{2} ∧ §bs0{1} = §bs0{2} ∧
            §m0{1} - r ≤ §i0{2} ∧ §i0{2} ≤ §m0{1} ∧ §i0{1} = §m0{1} ∧ size §bs0{1} = §m0{1} ∧
            (∀ k, §m0{1} - r ≤ k ∧ k < §i0{2} →
              FMap.get §HybridIROEager_mp{1} (§xs0{1}, k) =
                FMap.get §HybridIROEager_mp{2} (§xs0{1}, k)) ∧
            (∀ k, §i0{2} ≤ k ∧ k < §m0{1} →
              FMap.get §HybridIROEager_mp{1} (§xs0{1}, k) = some (nth true §bs0{1} k)) ∧
            eager_eq_except §xs0{1} (§m0{1} - r) §m0{1} §HybridIROEager_mp{1}
              §HybridIROEager_mp{2}) ((§m0{2} - §i0{2}).toNat)
        case lossless =>
          intros
          simp [Stmt.ewp_seq, Stmt.ewp_assign]
        case «variant» =>
          intro σ₁ k
          hoare_wp 2
          hoare_skip
          rintro _ _ _ i mp ⟨⟨rfl, rfl, rfl, h4, h5, h6, h7, h8, h9, h10⟩, hg, hk⟩
          simp only [eval_lens_full, eval_lens_global, decide_eq_true_eq] at *
          refine ⟨⟨trivial, trivial, trivial, by omega, by omega, h6, h7, fun j hj => ?_,
            fun j hj => h9 j ⟨by omega, hj.2⟩,
            eager_eq_except_upd2_eq_in _ _ _ _ _ _ _ h10 (by omega) (by omega)⟩, by omega⟩
          by_cases hji : j = i
          · subst hji
            rw [FMap.get_set_sameE]
            exact h9 j ⟨le_rfl, by omega⟩
          · rw [FMap.get_setE, if_neg (by rintro ⟨⟩; exact hji rfl)]
            exact h8 j ⟨hj.1, by omega⟩
        case exit =>
          rintro _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, h1, h2, hi, hs, heq, -, hee⟩ hg
          simp only [decide_eq_false_iff_not, not_lt] at hg
          refine ⟨Prod.ext rfl (by simp only; omega),
            eager_eq_except_maps_eq _ _ _ true _ _ (by omega) hee
              fun k hk => heq k ⟨hk.1, by omega⟩⟩
        · equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, h1, hi, hs, hget, hee⟩
          exact ⟨rfl, rfl, rfl, by omega, by omega, hi, hs, fun k hk => absurd hk.2 (by omega),
            fun k hk => hget k ⟨by omega, hk.2⟩, hee⟩

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

/-- `BlockGen_loop_direct`, keeping the globals equal (for EC's `call BlockGen_loop_direct`, which
frames the caller's state). -/
theorem BlockGen_loop_direct_eq :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂) BlockGen.loop.procedure BlockGen.direct.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) :=
  prhlProc_conseq (prhlProc.trans (BlockGen_loop_BlockGenCall Eq)
      (prhlProc.symm (BlockGen_direct_BlockGenCall Eq)))
    (fun _ g _ _ h => ⟨(), g, rfl, h.symm⟩)
    (fun _ _ _ _ ⟨_, _, h, h'⟩ => ⟨h.1.trans h'.1.symm, h.2.trans h'.2.symm⟩)

-- Auxiliary (not in EC, exception E12): `HybridIROEagerTrans.next_block_split` with its loop of
-- bits the call `BlockGen.loop()`, resp. `BlockGen.direct()`: EC's `transitivity{2}` through
-- `{ w <@ BlockGen.loop(); }` and `{ w <@ BlockGen.direct(); }` in
-- `HybridIROEagerTrans_BlockSpongeTrans_next_block`
module NextBlockSplitLoop {
  proc next_block_split (xs : List block, i : ℤ, m : ℤ, bs : List Bool) : (List Bool × ℤ) {
    var b : Bool, w : block, cs : List Bool;
    if (decide (FMap.dom ($HybridIROEager_mp : FMap (List block × ℤ) Bool) ($xs, $i))) {
      while ($i < $m) {
        b <- oget (FMap.get ($HybridIROEager_mp : FMap (List block × ℤ) Bool) ($xs, $i));
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
    } else {
      w <- call BlockGen.loop ();
      cs <- ofblock $w;
      bs <- $bs ++ $cs;
      while ($i < $m) {
        HybridIROEager_mp <- FMap.set $HybridIROEager_mp ($xs, $i) (nth true $bs $i);
        i <- $i + 1;
      }
    }
    return ($bs, $i)
  };
}

module NextBlockSplitDirect {
  proc next_block_split (xs : List block, i : ℤ, m : ℤ, bs : List Bool) : (List Bool × ℤ) {
    var b : Bool, w : block, cs : List Bool;
    if (decide (FMap.dom ($HybridIROEager_mp : FMap (List block × ℤ) Bool) ($xs, $i))) {
      while ($i < $m) {
        b <- oget (FMap.get ($HybridIROEager_mp : FMap (List block × ℤ) Bool) ($xs, $i));
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
    } else {
      w <- call BlockGen.direct ();
      cs <- ofblock $w;
      bs <- $bs ++ $cs;
      while ($i < $m) {
        HybridIROEager_mp <- FMap.set $HybridIROEager_mp ($xs, $i) (nth true $bs $i);
        i <- $i + 1;
      }
    }
    return ($bs, $i)
  };
}

/-- EC's `transitivity{2}` through `{ w <@ BlockGen.loop(); }` (the first step of the case
`! dom BlockSponge.BIRO.IRO.mp{2} (x0{2}, n{2})` of
`HybridIROEagerTrans_BlockSpongeTrans_next_block`): the loop of bits is `BlockGen.loop`'s. -/
theorem next_block_split_NextBlockSplitLoop :
    prhlProc (sig₁ := procsig (List block, ℤ, ℤ, List Bool) -> (List Bool × ℤ))
      (sig₂ := procsig (List block, ℤ, ℤ, List Bool) -> (List Bool × ℤ))
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (HybridIROEagerTrans.next_block_split HybridIROEager_mp).procedure
      (NextBlockSplitLoop.next_block_split HybridIROEager_mp).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧
      §bs0{1} = §bs0{2} ∧ §allGlobals{1} = §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ _ _ _ _ _ _ ⟨⟨⟩, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · equiv_if
    case guard => intros; simp_all
    case «then» =>
      equiv_while_raw (§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧
          §bs0{1} = §bs0{2} ∧ §allGlobals{1} = §allGlobals{2})
      case body =>
        stmt_wp
        equiv_skip
        intros; simp_all
      case guard => intros; simp_all
      case exit => intros; simp_all
      · equiv_skip; intros; simp_all
    case «else» =>
      equiv_seq_last 1 1 : (§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧
          §bs0{1} = §bs0{2} ∧ §allGlobals{1} = §allGlobals{2})
      · stmt_wp
        equiv_seq_last 1 1 : ((§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧
            §bs0{1} = §bs0{2} ∧ §allGlobals{1} = §allGlobals{2}) ∧ §j{1} = §j{2} ∧
            §cs{1} = §cs0{2} ∧ size §cs{1} = §j{1} ∧ 0 ≤ §j{1} ∧ §j{1} ≤ r)
        · stmt_wp
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ ⟨h, -⟩
          exact ⟨h, ge0_r⟩
        · equiv_while_raw ((§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧
              §bs0{1} = §bs0{2} ∧ §allGlobals{1} = §allGlobals{2}) ∧ §j{1} = §j{2} ∧
              §cs{1} = §cs0{2} ∧ size §cs{1} = §j{1} ∧ 0 ≤ §j{1} ∧ §j{1} ≤ r)
          case body =>
            stmt_wp
            equiv_rnd
            equiv_skip
            rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨h, rfl, rfl, hs, h0, -⟩, hg⟩ a -
            simp only [decide_eq_true_eq] at hg
            refine ⟨h, rfl, rfl, ?_, by omega, by omega⟩
            simp only [size, rcons, List.length_append, List.length_singleton] at hs ⊢
            push_cast; omega
          case guard => intros; simp_all
          case exit =>
            rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, hs, -, hj⟩ hg
            simp only [decide_eq_false_iff_not, not_lt] at hg
            refine ⟨rfl, rfl, rfl, ?_, rfl⟩
            rw [show ofblock (mkblock _) = _ from BitWord.ofwordK _ (by omega)]
          · equiv_skip
            intros; assumption
      · equiv_while_raw (§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧
          §bs0{1} = §bs0{2} ∧ §allGlobals{1} = §allGlobals{2})
        case body =>
          stmt_wp
          equiv_skip
          intros; simp_all
        case guard => intros; simp_all
        case exit => intros; simp_all
        · equiv_skip; intros; simp_all

/-- EC's `transitivity{2}` from `{ w <@ BlockGen.loop(); }` to `{ w <@ BlockGen.direct(); }`
(`call BlockGen_loop_direct`). -/
theorem NextBlockSplitLoop_NextBlockSplitDirect :
    prhlProc (sig₁ := procsig (List block, ℤ, ℤ, List Bool) -> (List Bool × ℤ))
      (sig₂ := procsig (List block, ℤ, ℤ, List Bool) -> (List Bool × ℤ))
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (NextBlockSplitLoop.next_block_split HybridIROEager_mp).procedure
      (NextBlockSplitDirect.next_block_split HybridIROEager_mp).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧
      §bs0{1} = §bs0{2} ∧ §allGlobals{1} = §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ _ _ _ _ _ _ ⟨⟨⟩, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · equiv_if
    case guard => intros; simp_all
    case «then» =>
      equiv_while_raw (§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧
          §bs0{1} = §bs0{2} ∧ §allGlobals{1} = §allGlobals{2})
      case body =>
        stmt_wp
        equiv_skip
        intros; simp_all
      case guard => intros; simp_all
      case exit => intros; simp_all
      · equiv_skip; intros; simp_all
    case «else» =>
      equiv_seq_last 1 1 : (§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧
          §bs0{1} = §bs0{2} ∧ §allGlobals{1} = §allGlobals{2})
      · stmt_wp
        have hc : prhlProc (fun _ g₁ _ g₂ => g₁ = g₂) (BlockGen.loop).procedure
            (BlockGen.direct).procedure (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) :=
          by simpa using BlockGen_loop_direct_eq
        equiv_call hc
        equiv_skip
        rintro _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, -⟩
        exact ⟨rfl, by rintro _ _ _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      · equiv_while_raw (§xs0{1} = §xs0{2} ∧ §i0{1} = §i0{2} ∧ §m0{1} = §m0{2} ∧
          §bs0{1} = §bs0{2} ∧ §allGlobals{1} = §allGlobals{2})
        case body =>
          stmt_wp
          equiv_skip
          intros; simp_all
        case guard => intros; simp_all
        case exit => intros; simp_all
        · equiv_skip; intros; simp_all

/-- The rest of EC's proof of `HybridIROEagerTrans_BlockSpongeTrans_next_block` after its
`transitivity HybridIROEagerTrans.next_block_split`, on `NextBlockSplitDirect` (EC's
`BlockGen.direct` step done): in the case `dom BlockSponge.BIRO.IRO.mp{2} (x0{2}, n{2})` the
bits are read (`while{1}`, EC's ghosts `i1`, `bs1` read from the right side); otherwise the block
is the right side's sample (`rnd`) and its bits are written (`while{1}`, EC's `eager_eq_except`
invariant, with the old map of the right side folded into the statement it is used for). -/
theorem NextBlockSplitDirect_BlockSpongeTrans_next_block (i2 : ℤ) :
    prhlProc (sig₁ := procsig (List block, ℤ, ℤ, List Bool) -> (List Bool × ℤ))
      (sig₂ := procsig (List block, ℤ, List block) -> (List block × ℤ))
      (fun a₁ g₁ a₂ g₂ => i2 = a₂.2.1 ∧ 0 ≤ a₂.2.1 ∧ a₁.1 = a₂.1 ∧ a₁.2.1 = a₂.2.1 * r ∧
        a₁.2.2.1 - a₁.2.1 = r ∧ a₁.2.2.2 = blocks2bits a₂.2.2 ∧ size a₂.2.2 = a₂.2.1 ∧
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁))
      (NextBlockSplitDirect.next_block_split HybridIROEager_mp).procedure
      (BlockSpongeTrans.next_block).procedure
      (fun r₁ g₁ r₂ g₂ => r₁.1 = blocks2bits r₂.1 ∧ r₁.2 = r₂.2 * r ∧ r₂.2 = i2 + 1 ∧
        size r₂.1 = i2 + 1 ∧
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁)) := by
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  have hr := gt0_r
  equiv_seq_last 1 1 : (i2 = §i0{2} ∧ 0 ≤ §i0{2} ∧ §xs0{1} = §x1{2} ∧ §n{2} = §i0{2} ∧
      §i0{1} = §i0{2} * r ∧ §m0{1} - §i0{1} = r ∧
      §(localVarLens "bs0" (List Bool)){1} = blocks2bits §(localVarLens "bs0" (List block)){2} ∧
      size §(localVarLens "bs0" (List block)){2} = §i0{2} ∧
      eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager_mp{1})
  · stmt_wp
    equiv_skip
    intros; assumption
  · equiv_if{1}
    case «then» =>
      equiv_if{2}
      case «then» =>
        refine prhlStmt_conseq prhlStmt_false (fun _ _ h => ?_) (fun _ _ h => h)
        obtain ⟨⟨⟨-, -, hx, hn, hi, -, -, -, ei⟩, hd1⟩, hd2⟩ := h
        simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hd1 hd2
        apply hd2
        rw [hn, ← hx]
        have := ei.2 _ _ hd1
        rwa [hi, Int.mul_ediv_cancel _ (ne_of_gt hr)] at this
      case «else» =>
        equiv_while_noframe{1} (i2 = §i0{2} ∧ 0 ≤ §i0{2} ∧ §xs0{1} = §x1{2} ∧ §n{2} = §i0{2} ∧
            §i0{2} * r ≤ §i0{1} ∧ §i0{1} ≤ §m0{1} ∧ §m0{1} - §i0{2} * r = r ∧
            size §(localVarLens "bs0" (List Bool)){1} = §i0{1} ∧
            §(localVarLens "bs0" (List Bool)){1} =
              blocks2bits §(localVarLens "bs0" (List block)){2} ++ take (§i0{1} - §i0{2} * r)
                (ofblock (oget (FMap.get §BlockSponge.BIRO.IRO.mp{2} (§x1{2}, §n{2})))) ∧
            FMap.dom §BlockSponge.BIRO.IRO.mp{2} (§x1{2}, §n{2}) ∧
            size §(localVarLens "bs0" (List block)){2} = §i0{2} ∧
            eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager_mp{1})
          ((§m0{1} - §i0{1}).toNat)
        case lossless =>
          intros
          simp [Stmt.ewp_seq, Stmt.ewp_assign]
        case «variant» =>
          intro σ₂ k
          hoare_wp 3
          hoare_skip
          rintro xs i m bs mp ⟨⟨h1, h2, hx, h4, h5, h6, h7, hs, hbs, hd, hs2, ei⟩, hg, hk⟩
          simp only [eval_lens_full, eval_lens_global, decide_eq_true_eq] at *
          generalize (localVarLens "i0" ℤ).get σ₂ = I2 at *
          generalize (localVarLens "n" ℤ).get σ₂ = N at *
          generalize (localVarLens "x1" (List block)).get σ₂ = X1 at *
          generalize (localVarLens "bs0" (List block)).get σ₂ = B2 at *
          generalize BlockSponge.BIRO.IRO.mp.get σ₂.globals = M2 at *
          subst hx h4
          have hsz : size (ofblock (oget (M2.get (xs, N)))) = r := BitWord.size_word ge0_r _
          have hget := (ei.1 _ _ hd).2 i ⟨by omega, by linarith⟩
          refine ⟨⟨h1, h2, rfl, rfl, by omega, by omega, h7, ?_, ?_, hd, hs2, ei⟩, by omega⟩
          · simp only [size, rcons, List.length_append, List.length_singleton] at hs ⊢
            push_cast; omega
          · have hi1 : 0 ≤ i - N * r := by omega
            have hi2 : i - N * r < size (ofblock (oget (M2.get (xs, N)))) := by rw [hsz]; omega
            rw [hget, hbs, show i + 1 - N * r = (i - N * r) + 1 by ring,
              take_nth false _ _ ⟨hi1, hi2⟩]
            simp [rcons, oget]
        case exit =>
          rintro i0₂ x1 n bs2 mp xs i m bs1 hm ⟨h1, h2, rfl, rfl, h5, h6, h7, hs, hbs, hd, hs2, ei⟩
            hg
          simp only [decide_eq_false_iff_not, not_lt] at hg
          have hsz : size (ofblock (oget (mp.get (xs, n)))) = r := BitWord.size_word ge0_r _
          refine ⟨?_, by linarith, by omega, ?_, ei⟩
          · rw [hbs, show i - n * r = size (ofblock (oget (mp.get (xs, n)))) by omega]
            simp only [take, size, rcons, blocks2bits_cat, blocks2bits_sing]
            simp
          · simp only [size, rcons, List.length_append, List.length_singleton] at hs2 ⊢
            push_cast; omega
        · equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ ⟨⟨⟨h1, h2, hx, hn, hi, hm, hbs, hs2, ei⟩, -⟩, hd2⟩
          simp only [Bool.not_eq_false', decide_eq_true_eq] at hd2
          refine ⟨h1, h2, hx, hn, by rw [hi], by omega, by omega, ?_, ?_, hd2, hs2, ei⟩
          · rw [hbs, size_blocks2bits, hs2, hi, mul_comm]
          · rw [hi, sub_self]
            simp [take, hbs]
    case «else» =>
      equiv_if{2}
      case «else» =>
        refine prhlStmt_conseq prhlStmt_false (fun _ _ h => ?_) (fun _ _ h => h)
        obtain ⟨⟨⟨-, -, hx, hn, hi, -, -, -, ei⟩, hd1⟩, hd2⟩ := h
        simp only [decide_eq_false_iff_not, Bool.not_eq_false', decide_eq_true_eq] at hd1 hd2
        apply hd1
        rw [hn, ← hx] at hd2
        rw [hi]
        exact eager_inv_mem_dom1 _ _ _ _ ei hd2 _ ⟨le_rfl, by linarith⟩
      case «then» =>
        equiv_seq_last 1 0 : (i2 = §i0{2} ∧ 0 ≤ §i0{2} ∧ §xs0{1} = §x1{2} ∧ §n{2} = §i0{2} ∧
            §i0{2} * r ≤ §i0{1} ∧ §i0{1} ≤ §m0{1} ∧ §m0{1} - §i0{2} * r = r ∧
            size §(localVarLens "bs0" (List block)){2} = §i0{2} ∧
            §(localVarLens "bs0" (List Bool)){1} =
              blocks2bits §(localVarLens "bs0" (List block)){2} ++ ofblock §w{1} ∧
            FMap.get §BlockSponge.BIRO.IRO.mp{2} (§x1{2}, §n{2}) = some §w{1} ∧
            (∀ j, §i0{2} * r ≤ j ∧ j < §i0{1} →
              FMap.get §HybridIROEager_mp{1} (§xs0{1}, j) =
                some (nth true §(localVarLens "bs0" (List Bool)){1} j)) ∧
            (∀ mq, eager_eq_except §xs0{1} (§i0{2} * r) ((§i0{2} + 1) * r)
                §HybridIROEager_mp{1} mq →
              (∀ j, §i0{2} * r ≤ j ∧ j < (§i0{2} + 1) * r →
                FMap.get mq (§xs0{1}, j) = some (nth false (ofblock §w{1}) (j - §i0{2} * r))) →
              eager_invar §BlockSponge.BIRO.IRO.mp{2} mq))
        · stmt_wp
          equiv_rnd
          stmt_wp
          equiv_skip
          rintro xs i m bs mp1 i0 x1 n bs2 mp2 ⟨⟨⟨h1, h2, hx, hn, hi, hm, hbs, hs2, ei⟩, -⟩, -⟩ a -
          subst hx hn
          refine ⟨h1, h2, rfl, rfl, by rw [hi], by omega, by omega, hs2, by rw [hbs],
            by rw [FMap.get_set_sameE], fun j hj => absurd hj.2 (by omega),
            fun mq hee hrange => eager_invar_eq_except_upd1 _ _ _ _ _ _ h2 ei hee hrange⟩
        · equiv_while_noframe{1} (i2 = §i0{2} ∧ 0 ≤ §i0{2} ∧ §xs0{1} = §x1{2} ∧ §n{2} = §i0{2} ∧
            §i0{2} * r ≤ §i0{1} ∧ §i0{1} ≤ §m0{1} ∧ §m0{1} - §i0{2} * r = r ∧
            size §(localVarLens "bs0" (List block)){2} = §i0{2} ∧
            §(localVarLens "bs0" (List Bool)){1} =
              blocks2bits §(localVarLens "bs0" (List block)){2} ++ ofblock §w{1} ∧
            FMap.get §BlockSponge.BIRO.IRO.mp{2} (§x1{2}, §n{2}) = some §w{1} ∧
            (∀ j, §i0{2} * r ≤ j ∧ j < §i0{1} →
              FMap.get §HybridIROEager_mp{1} (§xs0{1}, j) =
                some (nth true §(localVarLens "bs0" (List Bool)){1} j)) ∧
            (∀ mq, eager_eq_except §xs0{1} (§i0{2} * r) ((§i0{2} + 1) * r)
                §HybridIROEager_mp{1} mq →
              (∀ j, §i0{2} * r ≤ j ∧ j < (§i0{2} + 1) * r →
                FMap.get mq (§xs0{1}, j) = some (nth false (ofblock §w{1}) (j - §i0{2} * r))) →
              eager_invar §BlockSponge.BIRO.IRO.mp{2} mq)) ((§m0{1} - §i0{1}).toNat)
          case lossless =>
            intros
            simp [Stmt.ewp_seq, Stmt.ewp_assign]
          case «variant» =>
            intro σ₂ k
            hoare_wp 2
            hoare_skip
            rintro xs i m bs w mp ⟨⟨h1, h2, hx, h4, h5, h6, h7, hs2, hbs, hget, hrng, hL⟩, hg, hk⟩
            simp only [eval_lens_full, eval_lens_global, decide_eq_true_eq] at *
            generalize (localVarLens "i0" ℤ).get σ₂ = I2 at *
            generalize (localVarLens "n" ℤ).get σ₂ = N at *
            generalize (localVarLens "x1" (List block)).get σ₂ = X1 at *
            generalize (localVarLens "bs0" (List block)).get σ₂ = B2 at *
            generalize BlockSponge.BIRO.IRO.mp.get σ₂.globals = M2 at *
            subst hx
            have hI : (I2 + 1) * r = I2 * r + r := by ring
            refine ⟨⟨h1, h2, rfl, h4, by omega, by omega, h7, hs2, hbs, hget, fun j hj => ?_,
              fun mq hee hr' => hL mq (fun ys l hl => ?_) hr'⟩, by omega⟩
            · by_cases hji : j = i
              · subst hji
                rw [FMap.get_set_sameE]
              · rw [FMap.get_setE, if_neg (by rintro ⟨⟩; exact hji rfl)]
                exact hrng j ⟨hj.1, by omega⟩
            · rw [← hee ys l hl, FMap.get_setE,
                if_neg (by rintro ⟨⟩; rcases hl with h' | h' | h' <;> first | exact h' rfl | omega)]
          case exit =>
            rintro i0 x1 n bs2 mp xs i m bs w mp1
              ⟨h1, h2, hx, hn, h5, h6, h7, hs2, hbs, hget, hrng, hL⟩
              hg
            subst hx hn
            simp only [decide_eq_false_iff_not, not_lt] at hg
            have hsz : size (ofblock w) = r := BitWord.size_word ge0_r _
            have hsb : size (blocks2bits bs2) = n * r := by rw [size_blocks2bits, hs2, mul_comm]
            rw [hget]
            simp only [oget, Option.getD_some]
            refine ⟨by rw [hbs, rcons, blocks2bits_cat, blocks2bits_sing], by linarith, by omega,
              ?_, hL mp1 (fun _ _ _ => rfl) fun j hj => ?_⟩
            · simp only [size, rcons, List.length_append, List.length_singleton] at hs2 ⊢
              push_cast; omega
            · rw [hrng j ⟨hj.1, by linarith⟩, hbs, nth_cat, if_neg (by omega), hsb,
                set_nth_default true false _ _ ⟨by omega, by rw [hsz]; linarith⟩]
          · equiv_skip
            intros; assumption

/-- `lemma HybridIROEagerTrans_BlockSpongeTrans_next_block (i2 : int) :
equiv[HybridIROEagerTrans.next_block ~ BlockSpongeTrans.next_block : …]`; the arguments are
`(xs, i, m, bs)` and `(x, i, bs)`.
EC: `transitivity HybridIROEagerTrans.next_block_split` (`HybridIROEagerTrans_next_block_split`),
then the auxiliary steps above (exception E12). -/
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
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁)) :=
  prhlProc_conseq
    (prhlProc.trans (HybridIROEagerTrans_next_block_split HybridIROEager_mp)
      (prhlProc.trans (next_block_split_NextBlockSplitLoop HybridIROEager_mp)
        (prhlProc.trans (NextBlockSplitLoop_NextBlockSplitDirect HybridIROEager_mp)
          (NextBlockSplitDirect_BlockSpongeTrans_next_block HybridIROEager_mp i2))))
    (fun a₁ g₁ a₂ g₂ h => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, ei⟩ := h
      refine ⟨a₁, g₁, ⟨rfl, rfl, by omega, ?_, ?_⟩, a₁, g₁, ⟨rfl, rfl⟩, a₁, g₁, ⟨rfl, rfl⟩,
        h1, h2, h3, h4, h5, h6, h7, ei⟩
      · rw [h6, size_blocks2bits, h7, h4, mul_comm]
      · exact eager_inv_imp_block_bits_dom _ _ _ _ (by rw [h4]; exact mul_nonneg h2 ge0_r)
          (by rw [h4]; exact Dvd.intro_left _ rfl) ei)
    (fun r₁ g₁ r₂ g₂ h => by
      obtain ⟨_, g₂', ⟨rfl, hg⟩, _, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, h1, h2, h3, h4, ei⟩ := h
      exact ⟨h1, h2, h3, h4, hg ▸ ei⟩)

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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§n0{1} = n' ∧ §n0{2} = n' ∧ §xs0{1} = §xs0{2} ∧ §i{1} = §i{2} * r ∧ 0 ≤ §i{2} ∧
      §i{2} ≤ n' ∧ size §(localVarLens "bs" (List block)){2} = §i{2} ∧
      §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
      eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager_mp{1})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ _ _ ⟨⟨⟩, rfl, h0, ei⟩
    exact ⟨rfl, rfl, rfl, by ring, h0, rfl, rfl, ei⟩
  · refine prhlStmt_of_forall_nat (fun _ σ₂ => (n' - (localVarLens "i" ℤ).get σ₂).toNat) fun k => ?_
    induction k with
    | zero =>
      equiv_rcondf{1}
      equiv_rcondf{2}
      equiv_skip
      rintro n0₁ _ i₁ _ _ n0₂ _ i₂ _ _ ⟨⟨hn1, hn2, -, hi, h0, hn, hs, hbs, ei⟩, hk⟩
      have : i₂ = n' := by omega
      subst this
      exact ⟨by simp [hn2], by simp [hn1, hi], hi, rfl, hs, hbs, ei⟩
    | succ k ih =>
      refine prhlStmt_splitwhile_left
        ⟨fun σ => decide ((localVarLens "i" ℤ).get σ < ((localVarLens "n0" ℤ).get σ - k) * r)⟩
        (fun σ => ((localVarLens "n0" ℤ).get σ * r - (localVarLens "i" ℤ).get σ).toNat) ?_ ?_
      · intro k'
        simp only [Getter.andB_get, Bool.and_eq_true]
        hoare_wp 2
        hoare_call
        hoare_skip
        rintro i n0 ⟨⟨h1, -⟩, hk⟩ _ _
        simp only [decide_eq_true_eq] at h1
        omega
      refine prhlStmt_unroll_right ?_
      equiv_if{2}
      case «else» =>
        refine prhlStmt_conseq prhlStmt_false (fun _ _ h => ?_) (fun _ _ h => h)
        obtain ⟨⟨⟨-, hn, -, -, -, -, -, -, -⟩, hk⟩, hg⟩ := h
        simp only [decide_eq_false_iff_not, not_lt] at hg
        dsimp only [localVarLens] at hk
        omega
      case «then» =>
        equiv_seq_last 1 1 : ((§n0{1} = n' ∧ §n0{2} = n' ∧ §xs0{1} = §xs0{2} ∧ §i{1} = §i{2} * r ∧
            0 ≤ §i{2} ∧
            §i{2} ≤ n' ∧ size §(localVarLens "bs" (List block)){2} = §i{2} ∧
            §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
            eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager_mp{1}) ∧ (n' - §i{2}).toNat = k)
        · have legB : equiv[ §n0{1} = n' ∧ §n0{2} = n' ∧ §xs0{1} = §xs0{2} ∧
              n' - ((k : ℤ) + 1) = §i{2} ∧ 0 ≤ §i{2} ∧ §i{1} = §i{2} * r ∧
              (§n0{1} - (k : ℤ)) * r - §i{1} = r ∧
              §(localVarLens "bs" (List Bool)){1} =
                blocks2bits §(localVarLens "bs" (List block)){2} ∧
              size §(localVarLens "bs" (List block)){2} = §i{2} ∧
              eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager_mp{1} ==>
              (§n0{1} = n' ∧ §n0{2} = n' ∧ §xs0{1} = §xs0{2} ∧ §i{1} = §i{2} * r ∧
              0 ≤ §i{2} ∧ §i{2} ≤ n' ∧ size §(localVarLens "bs" (List block)){2} = §i{2} ∧
              §(localVarLens "bs" (List Bool)){1} =
                blocks2bits §(localVarLens "bs" (List block)){2} ∧
              eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager_mp{1}) ∧
              (n' - §i{2}).toNat = k ]
              { var res1 : List Bool × ℤ, xs0 : List block, i : ℤ, n0 : ℤ;
                res1 <- call (HybridIROEagerTrans.next_block HybridIROEager_mp).procedure
                  ($xs0, $i, ($n0 - (k : ℤ)) * r, $(localVarLens "bs" (List Bool)));
                (localVarLens "bs" (List Bool)), i <- $res1; } ~
              { var res2 : List block × ℤ, xs0 : List block, i : ℤ;
                res2 <- call (BlockSpongeTrans.next_block).procedure
                  ($xs0, $i, $(localVarLens "bs" (List block)));
                (localVarLens "bs" (List block)), i <- $res2; } := by
            stmt_wp
            equiv_call (HybridIROEagerTrans_BlockSpongeTrans_next_block HybridIROEager_mp
              (n' - ((k : ℤ) + 1)))
            equiv_skip
            rintro _ _ _ _ _ _ _ _ _ _ ⟨hn1, hn2, hx, hi2, h0, hi, hm, hbs, hs, ei⟩
            refine ⟨⟨hi2, h0, hx, hi, hm, hbs, hs, ei⟩, ?_⟩
            rintro r₁ g₁ r₂ g₂ ⟨h1, h2, h3, h4, ei'⟩
            exact ⟨⟨hn1, hn2, hx, h2, by omega, by omega, by rw [h4, h3], h1, ei'⟩, by omega⟩
          have legC : equiv[ §n0{1} = §n0{2} ∧ §xs0{1} = §xs0{2} ∧ §i{1} = §i{2} ∧
              §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2} ∧
              §allGlobals{1} = §allGlobals{2} ==>
              §n0{1} = §n0{2} ∧ §xs0{1} = §xs0{2} ∧ §i{1} = §i{2} ∧
              §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2} ∧
              §allGlobals{1} = §allGlobals{2} ]
              { var res2 : List block × ℤ, xs0 : List block, i : ℤ, n0 : ℤ;
                res2 <- call (BlockSpongeTrans.next_block).procedure
                  ($xs0, $i, $(localVarLens "bs" (List block)));
                (localVarLens "bs" (List block)), i <- $res2; } ~
              { var xs0 : List block, i : ℤ, b : block, n0 : ℤ;
                b <- call BlockSponge.BIRO.IRO.fill_in.procedure ($xs0, $i);
                (localVarLens "bs" (List block)) <- rcons $(localVarLens "bs" (List block)) $b;
                i <- $i + 1; } := by
            stmt_inline{1} 0
            stmt_wp
            equiv_call
            stmt_wp
            equiv_skip
            intros; simp_all
          refine prhlStmt_conseq (prhlStmt.trans
            (A := fun σ σ' => (localVarLens "n0" ℤ).get σ = (localVarLens "n0" ℤ).get σ' ∧
              (localVarLens "xs0" (List block)).get σ = (localVarLens "xs0" (List block)).get σ' ∧
              (localVarLens "i" ℤ).get σ = (localVarLens "i" ℤ).get σ' ∧
              (localVarLens "bs" (List Bool)).get σ = (localVarLens "bs" (List Bool)).get σ' ∧
              σ.globals = σ'.globals)
            (B := fun σ σ' => (localVarLens "n0" ℤ).get σ = (localVarLens "n0" ℤ).get σ' ∧
              (localVarLens "xs0" (List block)).get σ = (localVarLens "xs0" (List block)).get σ' ∧
              (localVarLens "i" ℤ).get σ = (localVarLens "i" ℤ).get σ' ∧
              (localVarLens "bs" (List Bool)).get σ = (localVarLens "bs" (List Bool)).get σ' ∧
              σ.globals = σ'.globals) ?_ (prhlStmt.trans legB legC)) ?_ ?_
          · stmt_inline{2} 0
            stmt_wp
            unfold Getter.andB
            have hr := gt0_r
            equiv_seq_last 1 1 : (§n0{1} = §n0{2} ∧ §xs0{1} = §xs0{2} ∧ §xs{2} = §xs0{2} ∧
                §m{2} = (§n0{1} - (k : ℤ)) * r ∧ §i{1} = §i0{2} ∧ §bs{1} = §bs0{2} ∧
                §allGlobals{1} = §allGlobals{2})
            · stmt_wp
              equiv_skip
              intros; simp_all
            · equiv_while_raw (§n0{1} = §n0{2} ∧ §xs0{1} = §xs0{2} ∧ §xs{2} = §xs0{2} ∧
                §m{2} = (§n0{1} - (k : ℤ)) * r ∧ §i{1} = §i0{2} ∧ §bs{1} = §bs0{2} ∧
                §allGlobals{1} = §allGlobals{2})
              case body =>
                stmt_wp
                equiv_call
                equiv_skip
                intros; simp_all
              case guard =>
                rintro _ _ n0 _ i _ _ _ _ _ _ _ ⟨rfl, -, -, rfl, rfl, -⟩
                have hk : (n0 - (k : ℤ)) * r ≤ n0 * r := by nlinarith
                by_cases h : i < (n0 - (k : ℤ)) * r
                · simp [h, show i < n0 * r by omega]
                · simp [h]
              case exit => intros; simp_all
              · equiv_skip; intros; simp_all
          · rintro σ₁ σ₂ ⟨⟨⟨hn1, hn2, hx, hi, h0, hle, hs, hbs, ei⟩, hk⟩, -⟩
            have hi2 : n' - ((k : ℤ) + 1) = (localVarLens "i" ℤ).get σ₂ := by omega
            refine ⟨σ₁, ⟨rfl, rfl, rfl, rfl, rfl⟩, σ₂, ⟨hn1, hn2, hx, hi2, h0, hi, ?_, hbs, hs, ei⟩,
              rfl, rfl, rfl, rfl, rfl⟩
            change ((localVarLens "n0" ℤ).get σ₁ - k) * r - (localVarLens "i" ℤ).get σ₁ = r
            rw [hn1, hi, ← hi2]
            ring
          · rintro τ₁ τ₂ ⟨τm, ⟨hn, hx, hi, hbs, hg⟩, τm', ⟨⟨hn1, hn2, hx', hi', h0, hle, hs, hbs',
              ei⟩,
              hk⟩, hn'', hx'', hi'', hbs'', hg''⟩
            simp only [eval_lens_full, eval_lens_global, eval_getter_full, eval_getter_global,
              allGlobals_get] at *
            rw [hn, hx, hi, hbs, hg, ← hn'', ← hx'', ← hi'', ← hbs'']
            rw [← hg''] at *
            exact ⟨⟨hn1, hn2, hx', hi', h0, hle, hs, hbs', ei⟩, hk⟩
        · exact ih

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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  have hr := gt0_r
  equiv_seq_last 1 1 : (§n0{1} = n1 ∧ §xs0{1} = §(localVarLens "x" (List block)){2} ∧
      x2 = §(localVarLens "x" (List block)){2} ∧ §n0{2} = (n1 + r - 1) / r ∧
      §m{1} = §n0{2} * r ∧ §i{1} = 0 ∧ §i{2} = 0 ∧ §(localVarLens "bs" (List Bool)){1} = [] ∧
      §(localVarLens "bs" (List block)){2} = [] ∧
      eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager_mp{1})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ _ ⟨rfl, h2, h3, h4, ei⟩
    exact ⟨rfl, h3, h2, h4, by rw [h4], ei⟩
  · equiv_if
    case guard =>
      rintro _ _ _ _ _ _ _ _ _ _ _ ⟨-, rfl, -⟩
      simp [BlockSponge.BIRO.valid]
    case «else» =>
      equiv_skip
      rintro _ _ _ _ _ _ _ _ _ _ _ ⟨⟨-, rfl, rfl, -, -, -, -, rfl, rfl, ei⟩, hv⟩
      simp only [decide_eq_false_iff_not] at hv
      exact ⟨ei, fun h => absurd h hv, fun _ => ⟨rfl, rfl⟩⟩
    case «then» =>
      equiv_case (n1 ≤ 0)
      · equiv_rcondf{1}
        equiv_rcondf{1}
        equiv_rcondf{2}
        equiv_skip
        rintro _ _ _ _ _ _ _ _ _ _ _ ⟨⟨⟨hn0, -, -, hn0', hm, rfl, rfl, rfl, rfl, ei⟩, -⟩, hn⟩
        have h1 := needed_blocks_non_pos _ hn
        refine ⟨by simp; omega, by simp; omega, by simp; nlinarith, ei,
          fun _ => ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by omega)⟩, fun _ => ⟨rfl, rfl⟩⟩
      · refine prhlStmt_of_equiv_left (StmtWithHoles.EquivInLens.seq
          (Stmt.Equiv.splitwhile _ ⟨fun σ => decide ((localVarLens "i" ℤ).get σ < n1 / r * r)⟩ _
            (fun σ => (n1 / r * r - (localVarLens "i" ℤ).get σ).toNat) ?_)
          (StmtWithHoles.Equiv.refl _)) ?_
        · intro k
          simp only [Getter.andB_get, Bool.and_eq_true]
          hoare_wp 2
          hoare_call
          hoare_skip
          rintro i n0 ⟨⟨-, h⟩, hk⟩ _ _
          simp only [decide_eq_true_eq] at h
          omega
        refine prhlStmt_splitwhile_right ⟨fun σ => decide ((localVarLens "i" ℤ).get σ < n1 / r)⟩
          (fun σ => (n1 / r - (localVarLens "i" ℤ).get σ).toNat) ?_ ?_
        · intro k
          simp only [Getter.andB_get, Bool.and_eq_true]
          hoare_wp 2
          hoare_call
          hoare_skip
          rintro i n0 ⟨⟨-, h⟩, hk⟩ _ _
          simp only [decide_eq_true_eq] at h
          omega
        refine prhlStmt_of_equiv_left (StmtWithHoles.Equiv.seq_assoc _ _ _) ?_
        equiv_seq_last 2 1 : (§n0{1} = n1 ∧ §xs0{1} = §(localVarLens "x" (List block)){2} ∧
            x2 = §(localVarLens "x" (List block)){2} ∧ §n0{2} = (n1 + r - 1) / r ∧
            §m{1} = §n0{2} * r ∧ §i{1} = n1 / r * r ∧ §i{2} = n1 / r ∧
            size §(localVarLens "bs" (List block)){2} = n1 / r ∧
            §(localVarLens "bs" (List Bool)){1} =
              blocks2bits §(localVarLens "bs" (List block)){2} ∧ 0 < n1 ∧
            eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager_mp{1} ∧ valid_block x2)
        · have legB : equiv[ §n0{1} = n1 ∧ §xs0{1} = §(localVarLens "x" (List block)){2} ∧
            x2 = §(localVarLens "x" (List block)){2} ∧
              §n0{2} = (n1 + r - 1) / r ∧ §m{1} = §n0{2} * r ∧ 0 < n1 ∧
              eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager_mp{1} ∧ valid_block x2 ==>
              §n0{1} = n1 ∧ §xs0{1} = §(localVarLens "x" (List block)){2} ∧
              x2 = §(localVarLens "x" (List block)){2} ∧ §n0{2} = (n1 + r - 1) / r ∧
              §m{1} = §n0{2} * r ∧ §i{1} = n1 / r * r ∧ §i{2} = n1 / r ∧
              size §(localVarLens "bs" (List block)){2} = n1 / r ∧
              §(localVarLens "bs" (List Bool)){1} =
                blocks2bits §(localVarLens "bs" (List block)){2} ∧ 0 < n1 ∧
              eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager_mp{1} ∧ valid_block x2 ]
              { var res1 : ℤ × List Bool, xs0 : List block, i : ℤ, n0 : ℤ, m : ℤ;
                res1 <- call (HybridIROEagerTrans.loop HybridIROEager_mp).procedure (n1 / r, $xs0);
                i, (localVarLens "bs" (List Bool)) <- $res1; } ~
              { var res2 : ℤ × List block, x : List block, i : ℤ, n0 : ℤ;
                res2 <- call (BlockSpongeTrans.loop).procedure (n1 / r, $x);
                i, (localVarLens "bs" (List block)) <- $res2; } := by
            stmt_wp
            equiv_call (HybridIROEagerTrans_BlockSpongeTrans_loop HybridIROEager_mp (n1 / r))
            equiv_skip
            rintro _ _ _ _ _ _ _ ⟨h1, rfl, h3, h4, h5, h6, ei, hv⟩
            exact ⟨⟨rfl, Int.ediv_nonneg (by omega) hr.le, ei⟩,
              fun r₁ g₁ r₂ g₂ ⟨a, b, c, d, e⟩ => ⟨h1, rfl, h3, h4, h5, a, b, c, d, h6, e, hv⟩⟩
          refine prhlStmt_conseq (prhlStmt.trans
            (A := fun σ σ' => (localVarLens "n0" ℤ).get σ = (localVarLens "n0" ℤ).get σ' ∧
            (localVarLens "xs0" (List block)).get σ = (localVarLens "xs0" (List block)).get σ' ∧
            (localVarLens "m" ℤ).get σ = (localVarLens "m" ℤ).get σ' ∧
              (localVarLens "i" ℤ).get σ = 0 ∧ (localVarLens "bs" (List Bool)).get σ = [] ∧
              (localVarLens "n0" ℤ).get σ = n1 ∧ 0 < n1 ∧ σ.globals = σ'.globals)
            (B := fun σ σ' => (localVarLens "n0" ℤ).get σ = (localVarLens "n0" ℤ).get σ' ∧
            (localVarLens "xs0" (List block)).get σ = (localVarLens "xs0" (List block)).get σ' ∧
            (localVarLens "m" ℤ).get σ = (localVarLens "m" ℤ).get σ' ∧
              (localVarLens "i" ℤ).get σ = (localVarLens "i" ℤ).get σ' ∧
              (localVarLens "bs" (List Bool)).get σ = (localVarLens "bs" (List Bool)).get σ' ∧
              σ.globals = σ'.globals) ?_
            (prhlStmt.trans
              (A₂ := fun σ σ' => (localVarLens "n0" ℤ).get σ = (localVarLens "n0" ℤ).get σ' ∧
              (localVarLens "x" (List block)).get σ = (localVarLens "x" (List block)).get σ' ∧
              (localVarLens "i" ℤ).get σ' = 0 ∧
                (localVarLens "bs" (List block)).get σ' = [] ∧
                (localVarLens "n0" ℤ).get σ' = (n1 + r - 1) / r ∧ 0 < n1 ∧ σ.globals = σ'.globals)
              (B₂ := fun σ σ' => (localVarLens "n0" ℤ).get σ = (localVarLens "n0" ℤ).get σ' ∧
              (localVarLens "x" (List block)).get σ = (localVarLens "x" (List block)).get σ' ∧
              (localVarLens "i" ℤ).get σ = (localVarLens "i" ℤ).get σ' ∧
                (localVarLens "bs" (List block)).get σ = (localVarLens "bs" (List block)).get σ' ∧
                σ.globals = σ'.globals) legB ?_)) ?_ ?_
          · stmt_inline{2} 0
            stmt_wp
            unfold Getter.andB
            equiv_seq_last 1 1 : (§n0{1} = §n0{2} ∧ §xs0{1} = §xs0{2} ∧ §m{1} = §m{2} ∧
                §xs{2} = §xs0{2} ∧
                §n{2} = n1 / r ∧ §i{1} = §i0{2} ∧ §bs{1} = §bs0{2} ∧ §n0{1} = n1 ∧ 0 < n1 ∧
                §allGlobals{1} = §allGlobals{2})
            · stmt_wp
              equiv_skip
              intros; simp_all; aesop
            · equiv_while_raw (§n0{1} = §n0{2} ∧ §xs0{1} = §xs0{2} ∧ §m{1} = §m{2} ∧ §xs{2} = §xs0{2} ∧
                §n{2} = n1 / r ∧ §i{1} = §i0{2} ∧ §bs{1} = §bs0{2} ∧ §n0{1} = n1 ∧ 0 < n1 ∧
                §allGlobals{1} = §allGlobals{2})
              case body =>
                stmt_wp
                equiv_call
                equiv_skip
                intros; simp_all; aesop
              case guard =>
                rintro _ _ n0 _ _ i _ _ _ _ _ _ _ _ ⟨rfl, -, -, -, rfl, rfl, -, rfl, h0, -⟩
                have := Int.ediv_mul_le n0 (ne_of_gt hr)
                by_cases h : i < n0 / r * r
                · simp [h, show i < n0 by omega]
                · simp [h]
              case exit => intros; simp_all
              · equiv_skip; intros; simp_all; aesop
          · stmt_inline{1} 0
            stmt_wp
            unfold Getter.andB
            equiv_seq_last 1 1 : (§n0{1} = §n0{2} ∧
                §(localVarLens "x" (List block)){1} = §(localVarLens "x" (List block)){2} ∧
                §xs{1} = §(localVarLens "x" (List block)){1} ∧
                §n{1} = n1 / r ∧ §i0{1} = §i{2} ∧ §bs0{1} = §bs{2} ∧
                §n0{2} = (n1 + r - 1) / r ∧ 0 < n1 ∧ §allGlobals{1} = §allGlobals{2})
            · stmt_wp
              equiv_skip
              intros; simp_all
            · equiv_while_raw (§n0{1} = §n0{2} ∧
                §(localVarLens "x" (List block)){1} = §(localVarLens "x" (List block)){2} ∧
                §xs{1} = §(localVarLens "x" (List block)){1} ∧
                §n{1} = n1 / r ∧ §i0{1} = §i{2} ∧ §bs0{1} = §bs{2} ∧
                §n0{2} = (n1 + r - 1) / r ∧ 0 < n1 ∧ §allGlobals{1} = §allGlobals{2})
              case body =>
                stmt_wp
                equiv_call
                equiv_skip
                intros; simp_all
              case guard =>
                rintro _ _ _ _ _ _ i _ _ _ _ _ ⟨-, -, -, rfl, rfl, -, rfl, h0, -⟩
                have : n1 / r ≤ (n1 + r - 1) / r := Int.ediv_le_ediv hr (by omega)
                by_cases h : i < n1 / r
                · simp [h, show i < (n1 + r - 1) / r by omega]
                · simp [h]
              case exit => intros; simp_all
              · equiv_skip; intros; simp_all
          · rintro σ₁ σ₂ ⟨⟨⟨hn0, hx, hx2, hn0', hm, hi, hi', hbs, hbs', ei⟩, hv⟩, hn⟩
            have h0 : 0 < n1 := by omega
            have hv' : valid_block x2 := by
              simp only [decide_eq_true_eq] at hv; rw [hx2, ← hx]; exact hv
            exact ⟨σ₁, ⟨rfl, rfl, rfl, hi, hbs, hn0, h0, rfl⟩, σ₂,
              ⟨hn0, hx, hx2, hn0', hm, h0, ei, hv'⟩, rfl, rfl, hi', hbs', hn0', h0, rfl⟩
          · rintro τ₁ τ₂ ⟨τm, ⟨hn, hx, hm, hi, hbs, hg⟩, τm', ⟨hn1, hx1, hx2, hn2, hm1, hi1, hi2,
              hs, hbs1,
              h0, ei, hv⟩, hn'', hx'', hi'', hbs'', hg''⟩
            simp only [eval_lens_full, eval_lens_global] at *
            rw [hn, hx, hm, hi, hbs, hg, ← hn'', ← hx'', ← hi'', ← hbs'']
            rw [← hg''] at *
            exact ⟨hn1, hx1, hx2, hn2, hm1, hi1, hi2, hs, hbs1, h0, ei, hv⟩
        · equiv_case (§i{2} = §n0{2})
          · equiv_rcondf{1}
            equiv_rcondf{1}
            equiv_rcondf{2}
            equiv_skip
            rintro _ _ _ _ _ _ _ _ _ bs₂ _ ⟨⟨hn0, -, -, hn0', hm, hi1, hi2, hs, hbs, h0, ei, hv⟩,
                heq⟩
            have hd : n1 / r = (n1 + r - 1) / r := by omega
            have hmul : n1 / r * r = n1 := Int.ediv_mul_cancel ((needed_blocks_eq_div_r n1).mpr hd)
            have hsz : size (blocks2bits bs₂) = n1 := by rw [size_blocks2bits, hs, mul_comm, hmul]
            refine ⟨by simp; omega, by simp; omega, by simp; rw [hm, hn0', ← hd, hi1], ei,
              fun _ => ⟨fun h => absurd h (by omega), fun _ => ⟨?_, by rw [hs, hd]⟩⟩,
              fun h => absurd hv h⟩
            rw [hbs]
            simp only [take]
            rw [List.take_of_length_le (by simp only [size] at hsz; omega)]
          · refine prhlStmt_unroll_right ?_
            equiv_if{2}
            case «else» =>
              refine prhlStmt_conseq prhlStmt_false (fun _ _ h => ?_) (fun _ _ h => h)
              obtain ⟨⟨⟨-, -, -, hn0', -, -, hi2, -, -, -, -, -⟩, hne⟩, hg⟩ := h
              simp only [decide_eq_false_iff_not, not_lt] at hg
              have := needed_blocks_rel_div_r n1
              omega
            case «then» =>
              equiv_rcondf{2}
              have leg2 : equiv[ §xs0{1} = §xs0{2} ∧ §i{1} = §i{2} ∧ §m{1} = §m{2} ∧
                  §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2} ∧
                  §allGlobals{1} = §allGlobals{2} ==>
                  §xs0{1} = §xs0{2} ∧ §i{1} = §i{2} ∧ §m{1} = §m{2} ∧
                  §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2} ∧
                  §allGlobals{1} = §allGlobals{2} ]
                  { var i : ℤ, m : ℤ, xs0 : List block, b : Bool;
                    while ($i < $m) {
                      b <- call (HybridIROEager.fill_in HybridIROEager_mp).procedure ($xs0, $i);
                      (localVarLens "bs" (List Bool)) <- rcons $(localVarLens "bs" (List Bool)) $b;
                      i <- $i + 1;
                    } } ~
                  { var res1 : List Bool × ℤ, xs0 : List block, i : ℤ, m : ℤ;
                    res1 <- call (HybridIROEagerTrans.next_block HybridIROEager_mp).procedure
                      ($xs0, $i, $m, $(localVarLens "bs" (List Bool)));
                    (localVarLens "bs" (List Bool)), i <- $res1; } := by
                stmt_inline{2} 0
                stmt_wp
                equiv_seq_last 1 1 : (§xs0{1} = §xs0{2} ∧ §xs{2} = §xs0{2} ∧ §i{1} = §i0{2} ∧
                    §m{1} = §m{2} ∧
                    §m0{2} = §m{2} ∧ §bs{1} = §bs0{2} ∧ §allGlobals{1} = §allGlobals{2})
                · stmt_wp
                  equiv_skip
                  intros; simp_all
                · equiv_while_raw (§xs0{1} = §xs0{2} ∧ §xs{2} = §xs0{2} ∧ §i{1} = §i0{2} ∧
                    §m{1} = §m{2} ∧
                    §m0{2} = §m{2} ∧ §bs{1} = §bs0{2} ∧ §allGlobals{1} = §allGlobals{2})
                  case body =>
                    stmt_wp
                    equiv_call
                    equiv_skip
                    intros; simp_all
                  case guard => intros; simp_all
                  case exit => intros; simp_all
                  · equiv_skip; intros; simp_all
              have leg3 : equiv[ n1 / r = §i{2} ∧ 0 ≤ §i{2} ∧
                  §xs0{1} = §(localVarLens "x" (List block)){2} ∧
                  §i{1} = §i{2} * r ∧ §m{1} - §i{1} = r ∧
                  §(localVarLens "bs" (List Bool)){1} =
                    blocks2bits §(localVarLens "bs" (List block)){2} ∧
                  size §(localVarLens "bs" (List block)){2} = §i{2} ∧
                  eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager_mp{1} ∧
                  §n0{2} = (n1 + r - 1) / r ∧ n1 / r + 1 = (n1 + r - 1) / r ∧ valid_block x2 ∧
                  0 < n1 ==>
                  §(localVarLens "bs" (List Bool)){1} =
                    blocks2bits §(localVarLens "bs" (List block)){2} ∧ §i{2} = n1 / r + 1 ∧
                  size §(localVarLens "bs" (List block)){2} = n1 / r + 1 ∧
                  eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager_mp{1} ∧
                  §n0{2} = (n1 + r - 1) / r ∧ n1 / r + 1 = (n1 + r - 1) / r ∧ valid_block x2 ∧
                  0 < n1 ]
                  { var res1 : List Bool × ℤ, xs0 : List block, i : ℤ, m : ℤ;
                    res1 <- call (HybridIROEagerTrans.next_block HybridIROEager_mp).procedure
                      ($xs0, $i, $m, $(localVarLens "bs" (List Bool)));
                    (localVarLens "bs" (List Bool)), i <- $res1; } ~
                  { var res2 : List block × ℤ, x : List block, i : ℤ, n0 : ℤ;
                    res2 <- call (BlockSpongeTrans.next_block).procedure
                      ($x, $i, $(localVarLens "bs" (List block)));
                    (localVarLens "bs" (List block)), i <- $res2; } := by
                stmt_wp
                equiv_call (HybridIROEagerTrans_BlockSpongeTrans_next_block HybridIROEager_mp
                  (n1 / r))
                equiv_skip
                intros
                rename_i h
                obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hn, hq, hv, h0⟩ := h
                exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩,
                  fun _ _ _ _ ⟨a, _, c, d, e⟩ => ⟨a, c, d, e, hn, hq, hv, h0⟩⟩
              have leg4 : equiv[ §(localVarLens "x" (List block)){1} =
                §(localVarLens "x" (List block)){2} ∧ §i{1} = §i{2} ∧
                §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2} ∧
                  §allGlobals{1} = §allGlobals{2} ∧ §n0{1} = §n0{2} ==>
                  §(localVarLens "x" (List block)){1} = §(localVarLens "x" (List block)){2} ∧
                  §i{1} = §i{2} ∧
                  §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2} ∧
                  §allGlobals{1} = §allGlobals{2} ∧ §n0{1} = §n0{2} ]
                  { var res2 : List block × ℤ, x : List block, i : ℤ, n0 : ℤ;
                    res2 <- call (BlockSpongeTrans.next_block).procedure
                      ($x, $i, $(localVarLens "bs" (List block)));
                    (localVarLens "bs" (List block)), i <- $res2; } ~
                  { var x : List block, i : ℤ, b : block, n0 : ℤ;
                    b <- call (IRO.IRO.fill_in block (List block) BlockSponge.BIRO.valid bdistr
                      BlockSponge.BIRO.IRO.mp).procedure ($x, $i);
                    (localVarLens "bs" (List block)) <- rcons $(localVarLens "bs" (List block)) $b;
                    i <- $i + 1; } := by
                stmt_inline{1} 0
                stmt_wp
                equiv_call
                stmt_wp
                equiv_skip
                intros; simp_all
              refine prhlStmt_conseq (prhlStmt.trans
                (A := fun σ σ' => (localVarLens "n0" ℤ).get σ = n1 ∧
                (localVarLens "xs0" (List block)).get σ =
                  (localVarLens "xs0" (List block)).get σ' ∧
                  (localVarLens "m" ℤ).get σ = (localVarLens "m" ℤ).get σ' ∧
                  (localVarLens "i" ℤ).get σ = (localVarLens "i" ℤ).get σ' ∧
                  (localVarLens "bs" (List Bool)).get σ = (localVarLens "bs" (List Bool)).get σ' ∧
                  σ.globals = σ'.globals ∧
                  n1 ≤ (localVarLens "m" ℤ).get σ ∧ (localVarLens "i" ℤ).get σ ≤ n1 ∧
                      size ((localVarLens "bs" (List Bool)).get σ) = (localVarLens "i" ℤ).get σ ∧
                      (localVarLens "n0" ℤ).get σ' = n1)
                (B := fun τ τ' => (localVarLens "xs0" (List block)).get τ =
                  (localVarLens "xs0" (List block)).get τ' ∧
                  (localVarLens "i" ℤ).get τ = (localVarLens "i" ℤ).get τ' ∧
                  (localVarLens "m" ℤ).get τ = (localVarLens "m" ℤ).get τ' ∧
                  (localVarLens "bs" (List Bool)).get τ =
                    take n1 ((localVarLens "bs" (List Bool)).get τ') ∧ τ.globals = τ'.globals) ?_
                (prhlStmt.trans leg2 (prhlStmt.trans leg3 leg4))) ?_ ?_
              · refine prhlStmt_splitwhile_right ⟨fun σ => decide ((localVarLens "i" ℤ).get σ <
                (localVarLens "n0" ℤ).get σ)⟩
                  (fun σ => ((localVarLens "m" ℤ).get σ - (localVarLens "i" ℤ).get σ).toNat) ?_ ?_
                · intro k
                  simp only [Getter.andB_get, Bool.and_eq_true]
                  hoare_wp 2
                  hoare_call
                  hoare_skip
                  intros
                  simp_all only [decide_eq_true_eq]
                  omega
                unfold Getter.andB
                equiv_seq_last 1 1 : (§xs0{1} = §xs0{2} ∧ §m{1} = §m{2} ∧ §i{1} = §i{2} ∧
                    §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2} ∧
                    §allGlobals{1} = §allGlobals{2} ∧ §i{1} = n1 ∧
                    n1 ≤ §m{1} ∧ size §(localVarLens "bs" (List Bool)){2} = n1)
                · equiv_while_raw (§n0{1} = n1 ∧ §n0{2} = n1 ∧ §xs0{1} = §xs0{2} ∧ §m{1} = §m{2} ∧
                    §i{1} = §i{2} ∧
                    §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2} ∧
                    §allGlobals{1} = §allGlobals{2} ∧
                    n1 ≤ §m{1} ∧ §i{1} ≤ n1 ∧ size §(localVarLens "bs" (List Bool)){1} = §i{1})
                  case body =>
                    stmt_wp
                    equiv_call
                    equiv_skip
                    rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨hn1, hn2, rfl, rfl, rfl, rfl, rfl, hm, hi,
                        hs⟩, hg⟩
                    simp only [decide_eq_true_eq] at hg
                    refine ⟨rfl, rfl, fun _ _ => ⟨hn1, hn2, rfl, rfl, rfl, rfl, hm, by omega, ?_⟩⟩
                    simp only [size, rcons, List.length_append, List.length_singleton] at hs ⊢
                    push_cast; omega
                  case guard =>
                    rintro _ _ _ _ m i _ _ _ _ _ _ ⟨hn1, hn2, rfl, rfl, rfl, rfl, rfl, hm, hi, hs⟩
                    rw [hn1, hn2]
                    by_cases h : i < n1
                    · simp [h, show i < m by omega]
                    · simp [h]
                  case exit =>
                    rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨hn1, hn2, rfl, rfl, rfl, rfl, rfl, hm, hi,
                        hs⟩ hg
                    simp only [decide_eq_false_iff_not, not_lt] at hg
                    exact ⟨rfl, rfl, rfl, rfl, rfl, by omega, hm, by omega⟩
                  · equiv_skip
                    rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨hn1, rfl, rfl, rfl, rfl, rfl, hm, hi, hs, hn2⟩
                    exact ⟨hn1, hn2, rfl, rfl, rfl, rfl, rfl, hm, hi, hs⟩
                · equiv_while_raw (§xs0{1} = §xs0{2} ∧ §m{1} = §m{2} ∧ §i{1} = §i{2} ∧
                    §allGlobals{1} = §allGlobals{2} ∧ n1 ≤ §i{1} ∧
                    n1 ≤ size §(localVarLens "bs" (List Bool)){2} ∧
                    §(localVarLens "bs" (List Bool)){1} =
                      take n1 §(localVarLens "bs" (List Bool)){2})
                  case body =>
                    stmt_wp
                    equiv_call
                    equiv_skip
                    rintro σ₁ _ _ _ _ bs₂ ⟨⟨rfl, rfl, rfl, rfl, h1, h2, hbs⟩, -⟩
                    refine ⟨rfl, rfl, fun r g => ?_⟩
                    simp only [Setter.throwaway]
                    simp_reads
                    have hsz : n1 ≤ (bs₂.length : ℤ) := by simpa [size] using h2
                    dsimp only [localVarLens] at h1 ⊢
                    refine ⟨by omega, ?_, ?_⟩
                    · simp only [size, rcons, List.length_append, List.length_singleton]
                      push_cast; omega
                    rw [hbs]
                    simp only [take, rcons]
                    rw [List.take_append_of_le_length (by omega)]
                  case guard => intros; simp_all
                  case exit => intros; simp_all
                  · equiv_skip
                    rintro _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, hi, hm, hs⟩
                    refine ⟨rfl, rfl, rfl, rfl, by omega, by omega, ?_⟩
                    simp only [take]
                    rw [List.take_of_length_le (by simp only [size] at hs; omega)]
              · rintro σ₁ σ₂ ⟨⟨⟨hn0, hx, hx2, hn0', hm, hi1, hi2, hs, hbs, h0, ei, hv⟩, hne⟩, -⟩
                have hq : n1 / r + 1 = (n1 + r - 1) / r := by
                  rcases needed_blocks_rel_div_r n1 with h | h <;> omega
                have hm' : (localVarLens "m" ℤ).get σ₁ = (n1 / r + 1) * r := by rw [hm, hn0', hq]
                have hle := Int.ediv_mul_le n1 (ne_of_gt hr)
                have hsuff := needed_blocks_suff n1
                have hq0 : 0 ≤ n1 / r := Int.ediv_nonneg h0.le hr.le
                refine ⟨σ₁, ⟨hn0, rfl, rfl, rfl, rfl, rfl, by rw [hm, hn0']; exact hsuff,
                  by rw [hi1]; exact hle, ?_, hn0⟩, σ₁, ⟨rfl, rfl, rfl, rfl, rfl⟩, σ₂,
                  ⟨hi2.symm, (by rw [hi2]; exact hq0 : 0 ≤ (localVarLens "i" ℤ).get σ₂), hx,
                    (by rw [hi1, hi2] : (localVarLens "i" ℤ).get σ₁ =
                      (localVarLens "i" ℤ).get σ₂ * r), ?_, hbs,
                    (by rw [hs, hi2] : size ((localVarLens "bs" (List block)).get σ₂) =
                      (localVarLens "i" ℤ).get σ₂), ei, hn0', hq, hv, h0⟩, rfl, rfl, rfl, rfl, rfl⟩
                · rw [hbs, size_blocks2bits, hs, hi1, mul_comm]
                · change (localVarLens "m" ℤ).get σ₁ - (localVarLens "i" ℤ).get σ₁ = r
                  rw [hm', hi1]; ring
              · rintro τ₁ τ₂ ⟨τm, ⟨hx, hi, hm, hbs, hg⟩, τm', ⟨hx', hi', hm', hbs', hg'⟩, τm'',
                  ⟨hb3, hi3, hs3, ei, hn3, hq, hv, h0⟩, hx'', hi'', hbs'', hg'', hn''⟩
                simp only [eval_lens_full, eval_lens_global, eval_getter_full, allGlobals_get] at *
                rw [hbs, hbs', hb3, hbs'', hg, hg', ← hg'']
                refine ⟨?_, ei, fun _ => ⟨fun h => absurd h (by omega), fun _ => ⟨?_, ?_⟩⟩,
                  fun h => absurd hv h⟩
                · simp only [decide_eq_false_iff_not, not_lt]
                  dsimp only [localVarLens] at *
                  omega
                · rfl
                · rw [← hbs'', hs3, hq]

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
  have hr := gt0_r
  -- EC: `exists* n{1}, xs{1}` and `conseq (HybridIROEager_f_BlockIRO_f n1 xs')`
  have core : prhlProc (sig₁ := procsig (List block, ℤ) -> (List Bool))
      (sig₂ := procsig (List block × ℤ) -> (List block))
      (fun a₁ g₁ a₂ g₂ => a₁.1 = a₂.1 ∧ a₁.2 = a₂.2 * r ∧
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁))
      (HybridIROEager.f HybridIROEager_mp).procedure BlockSponge.BIRO.IRO.f.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = blocks2bits r₂ ∧
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁)) := by
    intro a₁ a₂ g₁ g₂ ⟨hx, hn, ei⟩
    refine prhlProc_conseq
      (B := fun r₁ g₁ r₂ g₂ => r₁ = blocks2bits r₂ ∧
        eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager_mp.get g₁))
      (HybridIROEager_f_BlockIRO_f HybridIROEager_mp a₁.2 a₂.1)
      (fun _ _ _ _ h => h) ?_ a₁ a₂ g₁ g₂ ⟨rfl, rfl, hx, by rw [hn, needed_blocks_prod_r], ei⟩
    rintro r₁ g₁' r₂ g₂' ⟨ei', hv, hnv⟩
    refine ⟨?_, ei'⟩
    by_cases hvb : valid_block a₂.1
    · obtain ⟨hle, hgt⟩ := hv hvb
      by_cases h0 : a₁.2 ≤ 0
      · obtain ⟨rfl, rfl⟩ := hle h0
        rfl
      · obtain ⟨rfl, hs⟩ := hgt (not_le.mp h0)
        have hsz : size (blocks2bits r₂) = a₁.2 := by
          rw [size_blocks2bits, hs, hn, needed_blocks_prod_r, mul_comm]
        simp only [take]
        rw [List.take_of_length_le (by simp only [size] at hsz; omega)]
    · obtain ⟨rfl, rfl⟩ := hnv hvb
      rfl
  refine prhlProc_conseq (prhlProc.trans (Lower_HybridIROEager_f HybridIROEager_mp) core) ?_ ?_
  · rintro a₁ g₁ a₂ g₂ ⟨rfl, ei⟩
    exact ⟨(a₁.1, a₁.2 * r), g₁, ⟨rfl, rfl, rfl⟩, rfl, rfl, ei⟩
  · rintro r₁ g₁ r₂ g₂ ⟨rm, gm, ⟨rfl, hg⟩, rfl, ei⟩
    exact ⟨blocks2bitsK r₂, hg ▸ ei⟩

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
`Dist` and the other games' variables, and single variables (finitely supported) (EasyCrypt's
semantics of a local clone; exception E6). -/
def HIRO_fresh (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (HIRO_Lazy_mp HIRO_Eager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment) : Prop :=
  (HIRO_Lazy_mp).footprint ⊔ (HIRO_Eager_mp).footprint ≤ (FVP.fvP BlockSim ⊔ FVP.fvP Dist ⊔
    (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ (BIRO.IRO.mp).footprint ⊔
    (BlockSponge.BIRO.IRO.mp).footprint)ᶜ ∧
  (HIRO_Lazy_mp).footprint ≤ (HIRO_Eager_mp).footprintᶜ ∧
  (HIRO_Lazy_mp).footprint.FinitelySupported ∧ (HIRO_Eager_mp).footprint.FinitelySupported

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
  have hPf0 := prhlProc_glob (R := FVP.fvP Perm)
    (p := (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        Perm).procedure)
    (fun a => ProgramDenotation.inFootprint_mono (Module.Proc.inFootprint_fvP _ a)
      ((FVP.fvP_fst' _).trans (FVP.fvP_snd' _)))
  have hPf : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ eqGlob Perm g₁ g₂)
      (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Indifferentiability.PRIMITIVE.view (block × capacity) (List Bool × ℤ) (List Bool)
          Perm)).procedure
      (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Indifferentiability.PRIMITIVE.view (block × capacity) (List Bool × ℤ) (List Bool)
          Perm)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eqGlob Perm g₁ g₂) := by
    rw [Indifferentiability.PRIMITIVE.view_f]; exact hPf0
  equiv_proc_to_stmt
  stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 2 1 : (§n{1} = §n{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧ §i{1} = §i{2} ∧
      §xs{1} = §xs0{2} ∧ §(localVarLens "z" (List Bool)){1} = [] ∧
        §(localVarLens "z" (List block)){2} = [] ∧ §n0{2} = (§n{1} + r - 1) / r ∧
      valid_block §xs0{2} ∧ eqGlob Perm §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ ⟨rfl, hg⟩
    exact ⟨rfl, rfl, rfl, valid_pad2blocks _, hg⟩
  · equiv_if{2}
    case «else» =>
      refine prhlStmt_conseq prhlStmt_false (fun _ _ h => ?_) (fun _ _ h => h)
      obtain ⟨⟨-, -, -, -, -, -, -, -, hv, -⟩, hg⟩ := h
      simp only [decide_eq_false_iff_not] at hg
      exact hg hv
    case «then» =>
      equiv_seq_last 1 1 : (§n{1} = §n{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧ §i{1} = §i{2} ∧
          §(localVarLens "z" (List Bool)){1} = blocks2bits §(localVarLens "z" (List block)){2} ∧
            §n0{2} = (§n{1} + r - 1) / r ∧
          eqGlob Perm §allGlobals{1} §allGlobals{2})
      · equiv_while_raw (§n{1} = §n{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧ §i{1} = §i{2} ∧
            §xs{1} = §xs0{2} ∧ §(localVarLens "z" (List Bool)){1} = [] ∧
              §(localVarLens "z" (List block)){2} = [] ∧ §n0{2} = (§n{1} + r - 1) / r ∧
            eqGlob Perm §allGlobals{1} §allGlobals{2})
        case body =>
          stmt_wp
          equiv_call hPf
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hg⟩, -⟩
          exact ⟨⟨rfl, hg⟩, fun _ _ _ _ ⟨rfl, hg'⟩ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hg'⟩⟩
        case guard => intros; simp_all
        case exit =>
          rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, -, rfl, rfl, rfl, hg⟩ -
          exact ⟨rfl, rfl, rfl, rfl, by simp [blocks2bits], rfl, hg⟩
        · equiv_skip
          intros; simp_all
      · equiv_while_raw (§n{1} = §n{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧ §i{1} = §i{2} ∧
          §(localVarLens "z" (List Bool)){1} = blocks2bits §(localVarLens "z" (List block)){2} ∧
            §n0{2} = (§n{1} + r - 1) / r ∧
          eqGlob Perm §allGlobals{1} §allGlobals{2})
        case body =>
          equiv_seq_last 1 1 : ((§n{1} = §n{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧ §i{1} = §i{2} ∧
          §(localVarLens "z" (List Bool)){1} = blocks2bits §(localVarLens "z" (List block)){2} ∧
            §n0{2} = (§n{1} + r - 1) / r ∧
          eqGlob Perm §allGlobals{1} §allGlobals{2}) ∧ §i{1} = §i{2})
          · stmt_wp
            equiv_skip
            rintro _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, hg⟩, -⟩
            exact ⟨⟨rfl, rfl, rfl, rfl, by rw [rcons, blocks2bits_cat, blocks2bits_sing], rfl, hg⟩,
              rfl⟩
          · equiv_if
            case guard => intros; simp_all
            case «then» =>
              equiv_call hPf
              equiv_skip
              rintro _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, hg⟩, -⟩, -⟩
              exact ⟨⟨rfl, hg⟩, fun _ _ _ _ ⟨rfl, hg'⟩ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, hg'⟩⟩
            case «else» => equiv_skip; intros; simp_all
        case guard => intros; simp_all
        case exit =>
          rintro _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, hg⟩ -
          exact ⟨rfl, hg⟩
        · equiv_skip
          intros; simp_all

/-- `Sponge_Raise_BlockSponge_f` on the distinguisher's view of the two functionalities, with all
the globals kept equal (Sponge and the block sponge touch only `Perm`): the oracle premise of EC's
`call (_ : ={glob Perm})` in `RealIndif_Sponge_BlockSponge`. -/
theorem Sponge_Raise_BlockSponge_f_oracle :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app Sponge (Indifferentiability.PRIMITIVE.view (block × capacity)
          (List Bool × ℤ) (List Bool) Perm))).procedure
      (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app RaiseFun (Indifferentiability.DFUNCTIONALITY.mk SLCommon.state
          (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f SLCommon.state (List block × ℤ) (List block)
              (Module.app BlockSponge.Sponge (Indifferentiability.PRIMITIVE.view SLCommon.state
                (List block × ℤ) (List block) Perm)) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 2 1 : (§n{1} = §n{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧ §i{1} = §i{2} ∧
      §xs{1} = §xs0{2} ∧ §(localVarLens "z" (List Bool)){1} = [] ∧
        §(localVarLens "z" (List block)){2} = [] ∧ §n0{2} = (§n{1} + r - 1) / r ∧
      valid_block §xs0{2} ∧ §allGlobals{1} = §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ ⟨rfl, hg⟩
    exact ⟨rfl, rfl, rfl, valid_pad2blocks _, hg⟩
  · equiv_if{2}
    case «else» =>
      refine prhlStmt_conseq prhlStmt_false (fun _ _ h => ?_) (fun _ _ h => h)
      obtain ⟨⟨-, -, -, -, -, -, -, -, hv, -⟩, hg⟩ := h
      simp only [decide_eq_false_iff_not] at hg
      exact hg hv
    case «then» =>
      equiv_seq_last 1 1 : (§n{1} = §n{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧ §i{1} = §i{2} ∧
          §(localVarLens "z" (List Bool)){1} = blocks2bits §(localVarLens "z" (List block)){2} ∧
            §n0{2} = (§n{1} + r - 1) / r ∧
          §allGlobals{1} = §allGlobals{2})
      · equiv_while_raw (§n{1} = §n{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧ §i{1} = §i{2} ∧
            §xs{1} = §xs0{2} ∧ §(localVarLens "z" (List Bool)){1} = [] ∧
              §(localVarLens "z" (List block)){2} = [] ∧ §n0{2} = (§n{1} + r - 1) / r ∧
            §allGlobals{1} = §allGlobals{2})
        case body =>
          stmt_wp
          equiv_call
          equiv_skip
          intros; simp_all
        case guard => intros; simp_all
        case exit =>
          rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, -, rfl, rfl, rfl, hg⟩ -
          exact ⟨rfl, rfl, rfl, rfl, by simp [blocks2bits], rfl, hg⟩
        · equiv_skip
          intros; simp_all
      · equiv_while_raw (§n{1} = §n{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧ §i{1} = §i{2} ∧
          §(localVarLens "z" (List Bool)){1} = blocks2bits §(localVarLens "z" (List block)){2} ∧
            §n0{2} = (§n{1} + r - 1) / r ∧
          §allGlobals{1} = §allGlobals{2})
        case body =>
          equiv_seq_last 1 1 : ((§n{1} = §n{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧ §i{1} = §i{2} ∧
          §(localVarLens "z" (List Bool)){1} = blocks2bits §(localVarLens "z" (List block)){2} ∧
            §n0{2} = (§n{1} + r - 1) / r ∧
          §allGlobals{1} = §allGlobals{2}) ∧ §i{1} = §i{2})
          · stmt_wp
            equiv_skip
            rintro _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, hg⟩, -⟩
            exact ⟨⟨rfl, rfl, rfl, rfl, by rw [rcons, blocks2bits_cat, blocks2bits_sing], rfl, hg⟩,
              rfl⟩
          · equiv_if
            case guard => intros; simp_all
            case «then» =>
              equiv_call
              equiv_skip
              intros; simp_all
            case «else» => equiv_skip; intros; simp_all
        case guard => intros; simp_all
        case exit =>
          rintro _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, hg⟩ -
          exact ⟨rfl, hg⟩
        · equiv_skip
          intros; simp_all

/-- The `byequiv` of EC's `RealIndif_Sponge_BlockSponge`: the initializations are the same, and
`Dist`'s oracles differ only in `F.f` (`Sponge_Raise_BlockSponge_f_oracle`), by the abstract call
rule, `Dist` disjoint from `Perm`. -/
theorem RealIndif_Sponge_BlockSponge_equiv (Dist : DISTINGUISHER) (hD : Module.ECModule Dist
  distExt)
    (hdisj : FVP.fvP Dist ≤ (Lens.pair Perm.m Perm.mi).footprintᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂) (RealIndif Sponge Perm Dist).procedure
      (BlockSponge.RealIndif BlockSponge.Sponge Perm (LowerDist Dist)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{2} 2
  stmt_wp
  equiv_seq_last 1 1 : (§allGlobals{1} = §allGlobals{2})
  · have hinit : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
        (Indifferentiability.FUNCTIONALITY.init (block × capacity) (List Bool × ℤ) (List Bool)
          (Module.app Sponge (Indifferentiability.PRIMITIVE.view (block × capacity)
            (List Bool × ℤ) (List Bool) Perm))).procedure
        (Indifferentiability.FUNCTIONALITY.init SLCommon.state (List block × ℤ) (List block)
          (Module.app BlockSponge.Sponge (Indifferentiability.PRIMITIVE.view SLCommon.state
            (List block × ℤ) (List block) Perm))).procedure
        (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
      equiv_proc_to_stmt
      repeat stmt_inline{1} 0
      repeat stmt_inline{2} 0
      stmt_wp
      equiv_skip
      intros; simp_all
    stmt_wp
    equiv_call hinit
    equiv_call
    stmt_wp
    equiv_skip
    intro σ₁ σ₂ h
    exact ⟨h, fun _ _ => ⟨rfl, fun _ _ _ _ hg => by subst hg; rfl⟩⟩
  · stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_equal_outside_module
      (Lens.pair Perm.m Perm.mi) Dist distExt hD.1 hdisj Eq ?hc _ _ ?horacle) ?_
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
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Lens.equal_outside_and_get_eq_iff, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DFUNCTIONALITY.f.mk_simp,
          Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
        exact Sponge_Raise_BlockSponge_f_oracle
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Lens.equal_outside_and_get_eq_iff,
            Module.fst_pair, Module.snd_pair, Indifferentiability.DFUNCTIONALITY.f.mk_simp,
            Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact prhlProc_refl _
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Lens.equal_outside_and_get_eq_iff,
              Module.fst_pair, Module.snd_pair, Indifferentiability.DFUNCTIONALITY.f.mk_simp,
            Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
            exact prhlProc_refl _
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, ⟨(Lens.pair Perm.m Perm.mi).get σ₁.globals, ?_⟩, ?_⟩,
      fun r₁ g₁ r₂ g₂ ⟨hr, _⟩ => by simp_reads; exact hr⟩
    · rw [(Lens.pair Perm.m Perm.mi).get_set, h]
    · simp [h]

/-- `local lemma RealIndif_Sponge_BlockSponge &m`. -/
theorem RealIndif_Sponge_BlockSponge (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (hD : Module.ECModule Dist distExt) (_hR : Restrictions BlockSim Dist)
    (m : VariableAssignment) :
    Procedure.Pr (RealIndif Sponge Perm Dist).procedure () m (fun r _ => r = true) =
      Procedure.Pr (BlockSponge.RealIndif BlockSponge.Sponge Perm (LowerDist Dist)).procedure () m
        (fun r _ => r = true) :=
  -- EC: `byequiv=> //; proc; seq 2 2 : (={glob Dist, glob Perm}); call (_ : ={glob Perm})`
  Procedure.Pr_eq_of_prhlProc
    (RealIndif_Sponge_BlockSponge_equiv Dist hD
      (by rw [Footprint.lens_pair]
          refine _hR.2.trans (Footprint.compl_antimono (sup_le ?_ ?_))
          · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
          · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))))
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true) (fun r₁ _ r₂ _ h => by rw [h])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl

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
  unfold Restrictions at _hR
  unfold HIRO_fresh at _hfresh
  obtain ⟨hSR, hDR⟩ := _hR
  obtain ⟨hfr, -⟩ := _hfresh
  have h1 : BIRO.IRO.mp.footprint ≤ (FVP.fvP Dist)ᶜ := by fp_disjoint
  have hL := le_sup_left.trans hfr
  have h2 : HIRO_Lazy_mp.footprint ≤ (FVP.fvP Dist)ᶜ := hL.trans (Footprint.compl_antimono
    (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))
  have h3 : BIRO.IRO.mp.footprint ≤ (FVP.fvP BlockSim)ᶜ := by fp_disjoint
  have h4 : HIRO_Lazy_mp.footprint ≤ (FVP.fvP BlockSim)ᶜ := hL.trans (Footprint.compl_antimono
    (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))
  have h5 : HIRO_Lazy_mp.footprint ≤ (BIRO.IRO.mp.footprint)ᶜ := hL.trans (Footprint.compl_antimono
    (le_sup_right.trans le_sup_left))
  haveI : Lens.Disjoint HIRO_Lazy_mp BIRO.IRO.mp :=
    Lens.disjoint_of_footprint_le_compl _ _ h5
  haveI : Lens.Disjoint BIRO.IRO.mp HIRO_Lazy_mp := (inferInstance : Lens.Disjoint HIRO_Lazy_mp
    _).symm
  have hRL : FVP.fvP Dist ⊔ FVP.fvP BlockSim ≤
      ((Lens.pair BIRO.IRO.mp HIRO_Lazy_mp).footprint)ᶜ := by
    rw [Footprint.lens_pair]
    exact sup_le (Footprint.le_compl_of_fvP (sup_le h1 h2))
      (Footprint.le_compl_of_fvP (sup_le h3 h4))
  have hIR : BIRO.IRO.mp.footprint ≤ (FVP.fvP Dist ⊔ FVP.fvP BlockSim)ᶜ :=
    (Footprint.le_compl_comm _ _).mpr (sup_le ((Footprint.le_compl_comm _ _).mp h1)
    ((Footprint.le_compl_comm _ _).mp h3))
  have hLR : HIRO_Lazy_mp.footprint ≤ (FVP.fvP Dist ⊔ FVP.fvP BlockSim)ᶜ :=
    (Footprint.le_compl_comm _ _).mpr (sup_le ((Footprint.le_compl_comm _ _).mp h2)
    ((Footprint.le_compl_comm _ _).mp h4))
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ _ r₂ _ h => by rw [h]) rfl
  unfold HybridExperiment
  have eS : Module.app (RaiseSim BlockSim) (Indifferentiability.FUNCTIONALITY.view
      (block × capacity) (List Bool × ℤ) (List Bool) BIRO.IRO.asF) =
      Module.app BlockSim (Module.app LowerFun (Indifferentiability.FUNCTIONALITY.view
        (block × capacity) (List Bool × ℤ) (List Bool) BIRO.IRO.asF)) :=
    Module.app_comp _ _ _
  have eF₁ : (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
      BIRO.IRO.asF).procedure = BIRO.IRO.f.procedure := by
    simp [BIRO.IRO.asF]
  have eF₂ : (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
      (Module.app HybridIRO.RaiseHybridIRO (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp))).procedure =
      (Module.app HybridIRO.RaiseHybridIRO.f
        (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp)).procedure := by
    simp only [HybridIRO.RaiseHybridIRO.apply_simp, HybridIRO.RaiseHybridIRO.f.apply_simp]
    unfold Indifferentiability.FUNCTIONALITY.f
    erw [Module.snd'_pair_proc]
  have eL₁ : (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List block × ℤ) (List block)
      (Module.app LowerFun (Indifferentiability.FUNCTIONALITY.view (block × capacity)
        (List Bool × ℤ) (List Bool) BIRO.IRO.asF))).procedure =
      (Module.app LowerFun.f (Indifferentiability.FUNCTIONALITY.view (block × capacity)
        (List Bool × ℤ) (List Bool) BIRO.IRO.asF)).procedure := by
    simp only [LowerFun.apply_simp, LowerFun.f.apply_simp]
    unfold Indifferentiability.DFUNCTIONALITY.f
    rfl
  have eL₂ : (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List block × ℤ) (List block)
      (Module.app HybridIRO.LowerHybridIRO (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp))).procedure =
      (Module.app HybridIRO.LowerHybridIRO.f
        (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp)).procedure := by
    simp only [HybridIRO.LowerHybridIRO.apply_simp, HybridIRO.LowerHybridIRO.f.apply_simp]
    unfold Indifferentiability.DFUNCTIONALITY.f
    rfl
  have hinner : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧
      globInvF (Lens.pair BIRO.IRO.mp HIRO_Lazy_mp) (FVP.fvP Dist ⊔ FVP.fvP BlockSim)
        (fun x y => HybridIRO.lazy_invar x.1 y.2) g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List block × ℤ) (List block)
        (Module.app LowerFun (Indifferentiability.FUNCTIONALITY.view (block × capacity)
          (List Bool × ℤ) (List Bool) BIRO.IRO.asF))).procedure
      (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List block × ℤ) (List block)
        (Module.app HybridIRO.LowerHybridIRO (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        globInvF (Lens.pair BIRO.IRO.mp HIRO_Lazy_mp) (FVP.fvP Dist ⊔ FVP.fvP BlockSim)
          (fun x y => HybridIRO.lazy_invar x.1 y.2) g₁ g₂) := by
    refine prhlProc_globInvF_of_writesKeep _ (by writes_keep) (by writes_keep) ?_
    rw [eL₁, eL₂]
    exact HybridIRO.LowerFun_IRO_HybridIROLazy_f HIRO_Lazy_mp
  have hinit : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (Indifferentiability.PRIMITIVE.init (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app (RaiseSim BlockSim) (Indifferentiability.FUNCTIONALITY.view
          (block × capacity) (List Bool × ℤ) (List Bool) BIRO.IRO.asF))).procedure
      (Indifferentiability.PRIMITIVE.init (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app BlockSim (Module.app HybridIRO.LowerHybridIRO
          (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp)))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
    rw [eS]
    exact Indifferentiability.SIMULATOR.init_eq _ _ _ BlockSim hS.1 _ _
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (globInvF (Lens.pair BIRO.IRO.mp HIRO_Lazy_mp) (FVP.fvP Dist ⊔ FVP.fvP BlockSim)
      (fun x y => HybridIRO.lazy_invar x.1 y.2) §allGlobals{1} §allGlobals{2})
  · stmt_inline{1} 1
    repeat stmt_inline{2} 1
    stmt_wp
    equiv_call hinit
    stmt_wp
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨h, fun r₁ g₁ r₂ g₂ hg => ?_⟩
    subst hg
    refine ⟨?_, ?_⟩
    · simp only [Setter.throwaway]
      rw [touched_set_of_le_compl hIR, touched_set_of_le_compl hLR]
      rfl
    · simp [Lens.set_get]
      exact HybridIRO.lazy_invar0
  · stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_moduleF (Lens.pair BIRO.IRO.mp HIRO_Lazy_mp)
      Dist distExt hD.1 (FVP.fvP Dist ⊔ FVP.fvP BlockSim) le_sup_left hRL
      (fun x y => HybridIRO.lazy_invar x.1 y.2) ?hc _ _ ?horacle) ?_
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
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair, Indifferentiability.DFUNCTIONALITY.f.mk_simp,
          Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
        refine prhlProc_globInvF_of_writesKeep _ (by writes_keep) (by writes_keep) ?_
        rw [eF₁, eF₂]
        exact HybridIRO.IRO_RaiseHybridIRO_HybridIROLazy_f HIRO_Lazy_mp
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          HoleSigs.Instantiation.lookup_succ, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DFUNCTIONALITY.f.mk_simp,
          Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
          rw [eS]
          exact Indifferentiability.SIMULATOR.call_f _ _ _ _ BlockSim hS.1 _ le_sup_right hRL _ _ _
            hinner
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
          HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DFUNCTIONALITY.f.mk_simp,
          Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
            rw [eS]
            exact Indifferentiability.SIMULATOR.call_fi _ _ _ _ BlockSim hS.1 _ le_sup_right hRL _
              _ _
              hinner
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ _
    exact ⟨⟨rfl, ‹_›⟩, fun r₁ _ r₂ _ ⟨hr, _⟩ => by simp_reads; exact hr⟩

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

/-- `HybridIRODist` calls only `HI.f` (EasyCrypt's `{HI.f}` for `HIRO.HYBRID_IRO_DIST`). -/
theorem HybridIRODist.app_congr (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (HI HI' : HybridIRO.HYBRID_IRO)
    (h : HybridIRO.HYBRID_IRO.f HI = HybridIRO.HYBRID_IRO.f HI') :
    Module.app (HybridIRODist BlockSim Dist) HI = Module.app (HybridIRODist BlockSim Dist) HI' := by
  have eL : Module.app HybridIRO.LowerHybridIRO HI = Module.app HybridIRO.LowerHybridIRO HI' := by
    simp only [HybridIRO.LowerHybridIRO.apply_simp, HybridIRO.LowerHybridIRO.f.apply_simp, h]
  have eR : Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
      (Module.app HybridIRO.RaiseHybridIRO HI) =
      Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
      (Module.app HybridIRO.RaiseHybridIRO HI') := by
    simp only [HybridIRO.RaiseHybridIRO.apply_simp, HybridIRO.RaiseHybridIRO.f.apply_simp, h]
    unfold Indifferentiability.FUNCTIONALITY.f
    erw [Module.snd'_pair_proc, Module.snd'_pair_proc]
  simp only [HybridIRODist.apply_simp, HybridIRODist.distinguish.apply_simp, eL, eR]

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

/-- `HybridIRODist` is an EasyCrypt-like `HIRO.HYBRID_IRO_DIST` (EC: by construction): it calls
only `HI.f` (`HybridIRODist.app_congr`), and its globals are `BlockSim`'s and `Dist`'s. -/
theorem HybridIRODist.ecModule (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (hS : Indifferentiability.SIMULATOR.ECModule (block × capacity) (List block × ℤ)
      (List block) BlockSim)
    (hD : Module.ECModule Dist distExt) :
    Module.ECModule (HybridIRODist BlockSim Dist) HybridIRO.HYBRID_IRO_DIST.ext :=
  ⟨HybridIRO.HYBRID_IRO_DIST.representable_of_f _ (HybridIRODist.app_congr BlockSim Dist),
    (hS.2.sup hD.finitelySupported).mono (fvP_HybridIRODist_le BlockSim Dist)⟩

/-- `local lemma Experiment_HybridIROExper_Lazy &m`: initial bridging step. -/
theorem Experiment_HybridIROExper_Lazy (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (hS : Indifferentiability.SIMULATOR.ECModule (block × capacity) (List block × ℤ)
      (List block) BlockSim)
    (_hD : Module.ECModule Dist distExt) (_hR : Restrictions BlockSim Dist)
    (HIRO_Lazy_mp HIRO_Eager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)
    (_hfresh : HIRO_fresh BlockSim Dist HIRO_Lazy_mp HIRO_Eager_mp) (m : VariableAssignment) :
    Procedure.Pr (HybridExperiment BlockSim Dist
        (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp)).procedure () m (fun r _ => r = true) =
      Procedure.Pr (Module.app HybridIRO.HybridIROExper
        (Module.pair (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp)
          (HybridIRODist BlockSim Dist))).procedure () m (fun r _ => r = true) := by
  unfold HIRO_fresh at _hfresh
  obtain ⟨hfr, -⟩ := _hfresh
  have hL := le_sup_left.trans hfr
  have h4 : HIRO_Lazy_mp.footprint ≤ (FVP.fvP BlockSim)ᶜ := hL.trans (Footprint.compl_antimono
    (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))
  have hinit : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ HIRO_Lazy_mp.equal_outside g₁ g₂ ∧
      HIRO_Lazy_mp.get g₂ = FMap.empty)
      (Indifferentiability.PRIMITIVE.init (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app BlockSim (Module.app HybridIRO.LowerHybridIRO
          (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp)))).procedure
      (Indifferentiability.PRIMITIVE.init (block × capacity) (List block × ℤ) (List block)
        (Module.app BlockSim (Module.app HybridIRO.LowerHybridIRO
          (HybridIRO.HybridIROLazy.asHI HIRO_Lazy_mp)))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ HIRO_Lazy_mp.equal_outside g₁ g₂ ∧
        HIRO_Lazy_mp.get g₂ = FMap.empty) := by
    have e : ∀ g₁ g₂, globInvF HIRO_Lazy_mp HIRO_Lazy_mp.compl.footprint
        (fun _ y => y = FMap.empty) g₁ g₂ ↔
        HIRO_Lazy_mp.equal_outside g₁ g₂ ∧ HIRO_Lazy_mp.get g₂ = FMap.empty := fun g₁ g₂ => by
      rw [globInvF, Lens.footprint_touched_getter_eq_iff, Lens.equal_outside_iff_compl]
    refine prhlProc_conseq (Indifferentiability.SIMULATOR.call_init _ _ _ HIRO_Lazy_mp BlockSim
      hS.1 HIRO_Lazy_mp.compl.footprint
      (by rw [← Lens.compl_footprint]; exact Footprint.le_compl_of_fvP h4)
      (by rw [← Lens.compl_footprint]) (fun _ y => y = FMap.empty) _ _)
      (fun a₁ g₁ a₂ g₂ ⟨ha, hg⟩ => ⟨ha, (e g₁ g₂).mpr hg⟩)
      (fun r₁ g₁ r₂ g₂ ⟨hr, hg⟩ => ⟨hr, (e g₁ g₂).mp hg⟩)
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ _ r₂ _ h => by rw [h]) rfl
  unfold HybridExperiment
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  repeat stmt_inline{1} 1
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§allGlobals{1} = §allGlobals{2})
  · stmt_wp
    equiv_seq_last 1 1 : (HIRO_Lazy_mp.equal_outside §allGlobals{1} §allGlobals{2} ∧
        HIRO_Lazy_mp.get §allGlobals{2} = FMap.empty)
    · stmt_wp
      equiv_skip
      rintro g _ rfl
      exact ⟨FMap.empty, rfl⟩
    · equiv_call hinit
      equiv_skip
      rintro σ₁ σ₂ h
      refine ⟨h, fun r₁ g₁ r₂ g₂ ⟨⟨x, hx⟩, he⟩ => ?_⟩
      show HIRO_Lazy_mp.set FMap.empty g₁ = g₂
      subst hx
      rw [Lens.set_get] at he
      subst he
      rfl
  · equiv_call
    equiv_skip
    exact fun _ _ h => h

/-- `HybridIROExper_Experiment_Eager`, in the direction of `Experiment_HybridIROExper_Lazy` (the
same proof, for `HIRO.HybridIROEager`). -/
theorem Experiment_HybridIROExper_Eager (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    (hS : Indifferentiability.SIMULATOR.ECModule (block × capacity) (List block × ℤ)
      (List block) BlockSim)
    (_hD : Module.ECModule Dist distExt) (_hR : Restrictions BlockSim Dist)
    (HIRO_Lazy_mp HIRO_Eager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment)
    (_hfresh : HIRO_fresh BlockSim Dist HIRO_Lazy_mp HIRO_Eager_mp) (m : VariableAssignment) :
    Procedure.Pr (HybridExperiment BlockSim Dist
        (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)).procedure () m (fun r _ => r = true) =
      Procedure.Pr (Module.app HybridIRO.HybridIROExper
        (Module.pair (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)
          (HybridIRODist BlockSim Dist))).procedure () m (fun r _ => r = true) := by
  unfold HIRO_fresh at _hfresh
  obtain ⟨hfr, -⟩ := _hfresh
  have hL := le_sup_right.trans hfr
  have h4 : HIRO_Eager_mp.footprint ≤ (FVP.fvP BlockSim)ᶜ := hL.trans (Footprint.compl_antimono
    (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))
  have hinit : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ HIRO_Eager_mp.equal_outside g₁ g₂ ∧
      HIRO_Eager_mp.get g₂ = FMap.empty)
      (Indifferentiability.PRIMITIVE.init (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app BlockSim (Module.app HybridIRO.LowerHybridIRO
          (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)))).procedure
      (Indifferentiability.PRIMITIVE.init (block × capacity) (List block × ℤ) (List block)
        (Module.app BlockSim (Module.app HybridIRO.LowerHybridIRO
          (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ HIRO_Eager_mp.equal_outside g₁ g₂ ∧
        HIRO_Eager_mp.get g₂ = FMap.empty) := by
    have e : ∀ g₁ g₂, globInvF HIRO_Eager_mp HIRO_Eager_mp.compl.footprint
        (fun _ y => y = FMap.empty) g₁ g₂ ↔
        HIRO_Eager_mp.equal_outside g₁ g₂ ∧ HIRO_Eager_mp.get g₂ = FMap.empty := fun g₁ g₂ => by
      rw [globInvF, Lens.footprint_touched_getter_eq_iff, Lens.equal_outside_iff_compl]
    refine prhlProc_conseq (Indifferentiability.SIMULATOR.call_init _ _ _ HIRO_Eager_mp BlockSim
      hS.1 HIRO_Eager_mp.compl.footprint
      (by rw [← Lens.compl_footprint]; exact Footprint.le_compl_of_fvP h4)
      (by rw [← Lens.compl_footprint]) (fun _ y => y = FMap.empty) _ _)
      (fun a₁ g₁ a₂ g₂ ⟨ha, hg⟩ => ⟨ha, (e g₁ g₂).mpr hg⟩)
      (fun r₁ g₁ r₂ g₂ ⟨hr, hg⟩ => ⟨hr, (e g₁ g₂).mp hg⟩)
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ _ r₂ _ h => by rw [h]) rfl
  unfold HybridExperiment
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  repeat stmt_inline{1} 1
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§allGlobals{1} = §allGlobals{2})
  · stmt_wp
    equiv_seq_last 1 1 : (HIRO_Eager_mp.equal_outside §allGlobals{1} §allGlobals{2} ∧
        HIRO_Eager_mp.get §allGlobals{2} = FMap.empty)
    · stmt_wp
      equiv_skip
      rintro g _ rfl
      exact ⟨FMap.empty, rfl⟩
    · equiv_call hinit
      equiv_skip
      rintro σ₁ σ₂ h
      refine ⟨h, fun r₁ g₁ r₂ g₂ ⟨⟨x, hx⟩, he⟩ => ?_⟩
      show HIRO_Eager_mp.set FMap.empty g₁ = g₂
      subst hx
      rw [Lens.set_get] at he
      subst he
      rfl
  · equiv_call
    equiv_skip
    exact fun _ _ h => h

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
        (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)).procedure () m (fun r _ => r = true) :=
  -- EC: `byequiv; proc; inline*; seq 2 2; swap{2} 1 1; …; sim`, as for the lazy one
  (Experiment_HybridIROExper_Eager BlockSim Dist hS hD _hR HIRO_Lazy_mp HIRO_Eager_mp _hfresh
    m).symm

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
  -- EC: `by rewrite (Experiment_HybridIROExper_Lazy &m) (HIRO.HybridIROExper_Lazy_Eager
  -- HybridIRODist &m) (HybridIROExper_Experiment_Eager &m)`
  have hf := _hfresh
  unfold HIRO_fresh at hf
  obtain ⟨hfr, -, hLfs, hEfs⟩ := hf
  have hDd : HybridIRO.DRestrictions HIRO_Lazy_mp HIRO_Eager_mp (HybridIRODist BlockSim Dist) :=
    (fvP_HybridIRODist_le BlockSim Dist).trans ((Footprint.le_compl_comm _ _).mp
      ((sup_comm _ _).le.trans (hfr.trans (Footprint.compl_antimono
        (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left)))))))
  rw [Experiment_HybridIROExper_Lazy BlockSim Dist hS hD _hR HIRO_Lazy_mp HIRO_Eager_mp _hfresh m,
    HybridIRO.HybridIROExper_Lazy_Eager HIRO_Lazy_mp HIRO_Eager_mp hLfs hEfs
      (HybridIRODist BlockSim Dist) (HybridIRODist.ecModule BlockSim Dist hS hD) hDd m,
    HybridIROExper_Experiment_Eager BlockSim Dist hS hD _hR HIRO_Lazy_mp HIRO_Eager_mp _hfresh m]

/-- `RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f` on the invariant alone, without
`={glob BlockSim}`: what the oracle premise of `Experiment_HybridEager_Ideal_BlockIRO` frames (at
`glob Dist` and `glob BlockSim`), and `RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f` (at
`glob BlockSim`), syntactically (`prhlProc_globInvF_of_writesKeep`).  Its proof is EC's. -/
theorem RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f_inv
    (HIRO_Eager_mp : Lens (FMap (List block × ℤ) Bool) VariableAssignment) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧
        HybridIRO.eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HIRO_Eager_mp.get g₁))
      (Module.app HybridIRO.RaiseHybridIRO.f
        (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)).procedure
      (Module.app RaiseFun.f (Indifferentiability.FUNCTIONALITY.view (block × capacity)
        (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        HybridIRO.eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HIRO_Eager_mp.get g₁)) := by
  -- EC: `proc=> /=`
  have hr := gt0_r
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  have e₁ : (HybridIRO.HYBRID_IRO.f (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)).procedure =
      (HybridIRO.HybridIROEager.f HIRO_Eager_mp).procedure := by
    simp [HybridIRO.HybridIROEager.asHI]
  have e₂ : (Indifferentiability.DFUNCTIONALITY.f SLCommon.state (List block × ℤ) (List block)
      (Indifferentiability.FUNCTIONALITY.view (block × capacity) (List block × ℤ) (List block)
        BlockSponge.BIRO.IRO.asF)).procedure = BlockSponge.BIRO.IRO.f.procedure := by
    rw [Indifferentiability.FUNCTIONALITY.view_f]
    simp [BlockSponge.BIRO.IRO.asF]
  rw [e₁, e₂]
  stmt_wp
  equiv_seq_last 1 1 : (§bs{1} = §bs{2} ∧ §n{1} = §n{2} ∧
      HybridIRO.eager_invar §BlockSponge.BIRO.IRO.mp{2} §HIRO_Eager_mp{1})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ ⟨rfl, ei⟩
    exact ⟨rfl, rfl, ei⟩
  -- EC: 
  refine prhlStmt_fix_left (fun σ₁ => (localVarLens "n" ℤ).get σ₁) fun n' => ?_
  refine prhlStmt_fix_right (fun σ₂ => pad2blocks ((localVarLens "bs" (List Bool)).get σ₂))
    fun xs2 => ?_
  -- EC: 
  equiv_call (HybridIRO.HybridIROEager_f_BlockIRO_f HIRO_Eager_mp n' xs2)
  equiv_skip
  rintro bs₁ n₁ _ _ _ _ ⟨⟨⟨rfl, rfl, ei⟩, rfl⟩, rfl⟩
  refine ⟨⟨rfl, rfl, rfl, rfl, ei⟩, fun r₁ g₁ r₂ g₂ ⟨ei', hv, hnv⟩ => ⟨?_, ei'⟩⟩
  by_cases hvb : valid_block (pad2blocks bs₁)
  · obtain ⟨hle, hgt⟩ := hv hvb
    by_cases h0 : n₁ ≤ 0
    · obtain ⟨rfl, rfl⟩ := hle h0
      simp [blocks2bits_nil, take]
    · exact (hgt (not_le.mp h0)).1
  · obtain ⟨rfl, rfl⟩ := hnv hvb
    simp [blocks2bits_nil, take]

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
  unfold Restrictions at _hR
  unfold HIRO_fresh at _hfresh
  obtain ⟨hSR, -⟩ := _hR
  obtain ⟨hfr, -⟩ := _hfresh
  have hE' := le_sup_right.trans hfr
  have hE : HIRO_Eager_mp.footprint ≤ (FVP.fvP BlockSim)ᶜ := hE'.trans (Footprint.compl_antimono
    (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))
  have hB : BlockSponge.BIRO.IRO.mp.footprint ≤ (FVP.fvP BlockSim)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (hSR.trans (Footprint.compl_antimono le_sup_right))
  haveI : Lens.Disjoint HIRO_Eager_mp BlockSponge.BIRO.IRO.mp :=
    Lens.disjoint_of_footprint_le_compl _ _ (hE'.trans (Footprint.compl_antimono le_sup_right))
  -- EC's `={glob BlockSim}`: neither procedure writes `BlockSim`'s globals
  exact prhlProc_globInvF_of_writesKeep (L := Lens.pair HIRO_Eager_mp BlockSponge.BIRO.IRO.mp)
    (I := fun x y => HybridIRO.eager_invar y.2 x.1) (by writes_keep) (by writes_keep)
    (RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f_inv HIRO_Eager_mp)

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
  unfold Restrictions at _hR
  unfold HIRO_fresh at _hfresh
  obtain ⟨hSR, hDR⟩ := _hR
  obtain ⟨hfr, -⟩ := _hfresh
  have hE' := le_sup_right.trans hfr
  have h1 : BlockSponge.BIRO.IRO.mp.footprint ≤ (FVP.fvP Dist)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (hDR.trans (Footprint.compl_antimono le_sup_right))
  have h2 : HIRO_Eager_mp.footprint ≤ (FVP.fvP Dist)ᶜ := hE'.trans (Footprint.compl_antimono
    (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))
  have h3 : BlockSponge.BIRO.IRO.mp.footprint ≤ (FVP.fvP BlockSim)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (hSR.trans (Footprint.compl_antimono le_sup_right))
  have h4 : HIRO_Eager_mp.footprint ≤ (FVP.fvP BlockSim)ᶜ := hE'.trans (Footprint.compl_antimono
    (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))
  haveI : Lens.Disjoint HIRO_Eager_mp BlockSponge.BIRO.IRO.mp :=
    Lens.disjoint_of_footprint_le_compl _ _ (hE'.trans (Footprint.compl_antimono le_sup_right))
  have hRL : FVP.fvP Dist ⊔ FVP.fvP BlockSim ≤
      ((Lens.pair HIRO_Eager_mp BlockSponge.BIRO.IRO.mp).footprint)ᶜ := by
    rw [Footprint.lens_pair]
    exact sup_le (Footprint.le_compl_of_fvP (sup_le h2 h1))
      (Footprint.le_compl_of_fvP (sup_le h4 h3))
  have hER : HIRO_Eager_mp.footprint ≤ (FVP.fvP Dist ⊔ FVP.fvP BlockSim)ᶜ :=
    (Footprint.le_compl_comm _ _).mpr (sup_le ((Footprint.le_compl_comm _ _).mp h2)
    ((Footprint.le_compl_comm _ _).mp h4))
  have hBR : BlockSponge.BIRO.IRO.mp.footprint ≤ (FVP.fvP Dist ⊔ FVP.fvP BlockSim)ᶜ :=
    (Footprint.le_compl_comm _ _).mpr (sup_le ((Footprint.le_compl_comm _ _).mp h1)
    ((Footprint.le_compl_comm _ _).mp h3))
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ _ r₂ _ h => by rw [h]) rfl
  -- EC: `byequiv=> //; proc`
  unfold HybridExperiment
  have hinit : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (Indifferentiability.PRIMITIVE.init (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app BlockSim (Module.app HybridIRO.LowerHybridIRO
          (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)))).procedure
      (Indifferentiability.PRIMITIVE.init SLCommon.state (List block × ℤ) (List block)
        (Module.app BlockSim (Indifferentiability.FUNCTIONALITY.view SLCommon.state
          (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) :=
    Indifferentiability.SIMULATOR.init_eq _ _ _ BlockSim hS.1 _ _
  have eF₁ : (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
      (Module.app HybridIRO.RaiseHybridIRO
        (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp))).procedure =
      (Module.app HybridIRO.RaiseHybridIRO.f
        (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)).procedure := by
    simp only [HybridIRO.RaiseHybridIRO.apply_simp, HybridIRO.RaiseHybridIRO.f.apply_simp]
    unfold Indifferentiability.FUNCTIONALITY.f
    erw [Module.snd'_pair_proc]
  have eF₂ : (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
      (Module.app RaiseFun (Indifferentiability.DFUNCTIONALITY.mk SLCommon.state (List block × ℤ)
        (List block)
        { f := Indifferentiability.FUNCTIONALITY.f SLCommon.state (List block × ℤ) (List block)
            BlockSponge.BIRO.IRO.asF }))).procedure =
      (Module.app RaiseFun.f (Indifferentiability.FUNCTIONALITY.view SLCommon.state
        (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF)).procedure := by
    simp only [RaiseFun.apply_simp, RaiseFun.f.apply_simp]
    unfold Indifferentiability.DFUNCTIONALITY.f
    rfl
  have eL₁ : (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List block × ℤ) (List block)
      (Module.app HybridIRO.LowerHybridIRO
        (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp))).procedure =
      (Module.app HybridIRO.LowerHybridIRO.f
        (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp)).procedure := by
    simp only [HybridIRO.LowerHybridIRO.apply_simp, HybridIRO.LowerHybridIRO.f.apply_simp]
    unfold Indifferentiability.DFUNCTIONALITY.f
    rfl
  have eL₂ : (Indifferentiability.DFUNCTIONALITY.f SLCommon.state (List block × ℤ) (List block)
      (Indifferentiability.FUNCTIONALITY.view (block × capacity) (List block × ℤ) (List block)
        BlockSponge.BIRO.IRO.asF)).procedure = BlockSponge.BIRO.IRO.f.procedure := by
    rw [Indifferentiability.FUNCTIONALITY.view_f]
    simp [BlockSponge.BIRO.IRO.asF]
  have hinner : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧
      globInvF (Lens.pair HIRO_Eager_mp BlockSponge.BIRO.IRO.mp) (FVP.fvP Dist ⊔ FVP.fvP BlockSim)
        (fun x y => HybridIRO.eager_invar y.2 x.1) g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List block × ℤ) (List block)
        (Module.app HybridIRO.LowerHybridIRO
          (HybridIRO.HybridIROEager.asHI HIRO_Eager_mp))).procedure
      (Indifferentiability.DFUNCTIONALITY.f SLCommon.state (List block × ℤ) (List block)
        (Indifferentiability.FUNCTIONALITY.view (block × capacity) (List block × ℤ) (List block)
          BlockSponge.BIRO.IRO.asF)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        globInvF (Lens.pair HIRO_Eager_mp BlockSponge.BIRO.IRO.mp)
          (FVP.fvP Dist ⊔ FVP.fvP BlockSim) (fun x y => HybridIRO.eager_invar y.2 x.1) g₁ g₂) := by
    refine prhlProc_globInvF_of_writesKeep _ (by writes_keep) (by writes_keep) ?_
    rw [eL₁, eL₂]
    exact HybridIRO.HybridIROEager_BlockIRO_f HIRO_Eager_mp
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  -- EC: `seq 2 2 : (={glob Dist, glob BlockSim} /\ HIRO.HybridIROEager.mp{1} = empty /\
  -- BlockSponge.BIRO.IRO.mp{2} = empty); inline*; wp; call (_ : true); auto`, with the
  -- invariant of the call that follows
  equiv_seq_last 1 1 : (globInvF (Lens.pair HIRO_Eager_mp BlockSponge.BIRO.IRO.mp)
      (FVP.fvP Dist ⊔ FVP.fvP BlockSim) (fun x y => HybridIRO.eager_invar y.2 x.1)
      §allGlobals{1} §allGlobals{2})
  · repeat stmt_inline{1} 1
    stmt_inline{2} 1
    stmt_wp
    equiv_call hinit
    stmt_wp
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨h, fun r₁ g₁ r₂ g₂ hg => ?_⟩
    subst hg
    refine ⟨?_, ?_⟩
    · simp only [Setter.throwaway]
      rw [touched_set_of_le_compl hER, touched_set_of_le_compl hBR]
      rfl
    · simp only [Lens.set_get]
      exact HybridIRO.eager_invar0
  · -- EC: `call (_ : … ==> ={res}). proc (={glob BlockSim} /\ HIRO.eager_invar …)`, its oracles
    -- `conseq HIRO.HybridIROEager_BlockIRO_f` (inside `BlockSim`'s `proc (HIRO.eager_invar …)`)
    -- and `conseq RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f`; `LowerDist`'s wrapper call
    -- inlined (exception E5)
    stmt_inline{2} 0
    stmt_wp
    stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_moduleF
      (Lens.pair HIRO_Eager_mp BlockSponge.BIRO.IRO.mp)
      Dist distExt hD.1 (FVP.fvP Dist ⊔ FVP.fvP BlockSim) le_sup_left hRL
      (fun x y => HybridIRO.eager_invar y.2 x.1) ?hc _ _ ?horacle) ?_
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
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair, Indifferentiability.DFUNCTIONALITY.f.mk_simp,
          Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
        refine prhlProc_globInvF_of_writesKeep _ (by writes_keep) (by writes_keep) ?_
        rw [eF₁, eF₂]
        exact RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f_inv HIRO_Eager_mp
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
            HoleSigs.Instantiation.lookup_succ, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DFUNCTIONALITY.f.mk_simp,
            Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact Indifferentiability.SIMULATOR.call_f _ _ _ _ BlockSim hS.1 _ le_sup_right hRL _ _ _
            hinner
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
              Indifferentiability.DFUNCTIONALITY.f.mk_simp,
              Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
            exact Indifferentiability.SIMULATOR.call_fi _ _ _ _ BlockSim hS.1 _ le_sup_right hRL _
              _ _ hinner
          | succ n => nomatch n
    stmt_wp
    equiv_skip
    intro _ _ h
    exact ⟨h, fun _ _ _ _ ⟨hr, _⟩ => hr⟩

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
  -- the local clone `HIRO`'s variables, fresh (exception E6)
  have hG : (FVP.fvP BlockSim ⊔ FVP.fvP Dist ⊔ (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (BIRO.IRO.mp).footprint ⊔ (BlockSponge.BIRO.IRO.mp).footprint).FinitelySupported :=
    ((((hS.2.sup hD.finitelySupported).sup (.varLens _)).sup (.varLens _)).sup (.varLens _)).sup
      (.varLens _)
  haveI : Nonempty (FMap (List block × ℤ) Bool) := ⟨FMap.empty⟩
  obtain ⟨HIRO_Lazy_mp, hL, hLfs⟩ := Footprint.exists_fresh (FMap (List block × ℤ) Bool) hG
  obtain ⟨HIRO_Eager_mp, hE, hEfs⟩ :=
    Footprint.exists_fresh (FMap (List block × ℤ) Bool) (hG.sup hLfs)
  have hfresh : HIRO_fresh BlockSim Dist HIRO_Lazy_mp HIRO_Eager_mp :=
    ⟨sup_le hL (hE.trans (Footprint.compl_antimono le_sup_left)),
      (Footprint.le_compl_comm _ _).mp (hE.trans (Footprint.compl_antimono le_sup_right)), hLfs,
      hEfs⟩
  -- EC: `by rewrite (Ideal_IRO_Experiment_HybridLazy &m) (Experiment_Hybrid_Lazy_Eager &m)
  -- (Experiment_HybridEager_Ideal_BlockIRO &m)`
  rw [Ideal_IRO_Experiment_HybridLazy BlockSim Dist hS hD _hR HIRO_Lazy_mp HIRO_Eager_mp hfresh m,
    Experiment_Hybrid_Lazy_Eager BlockSim Dist hS hD _hR HIRO_Lazy_mp HIRO_Eager_mp hfresh m,
    Experiment_HybridEager_Ideal_BlockIRO BlockSim Dist hS hD _hR HIRO_Lazy_mp HIRO_Eager_mp hfresh
      m]

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
  -- EC: `by rewrite (RealIndif_Sponge_BlockSponge &m) (IdealIndif_IRO_BlockIRO &m)`
  rw [RealIndif_Sponge_BlockSponge BlockSim Dist hD _hR m,
    IdealIndif_IRO_BlockIRO BlockSim Dist hS hD _hR m]

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
          (LowerDist Dist)).procedure () m (fun r _ => r = true) : ℝ)| :=
  -- EC: `by apply (conclu BlockSim Dist &m)`
  conclu BlockSim Dist hS hD _hR m

end GaudisCrypt.SHA3.Sponge
