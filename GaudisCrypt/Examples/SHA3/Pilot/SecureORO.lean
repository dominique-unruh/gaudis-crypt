import GaudisCrypt.Lib.EC.PROM
import GaudisCrypt.Lib.EC.Mu
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.FelTactic
import GaudisCrypt.Logic.PHoareSeq
import GaudisCrypt.Logic.CallSpec
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECCallFrame
import GaudisCrypt.Lib.EC.StdBigop
import GaudisCrypt.Logic.ModuleFootprint
import GaudisCrypt.Syntax.ModuleVar
import GaudisCrypt.Syntax.ModuleSubtype

/-!
# Random oracles with failing queries are preimage, second-preimage and collision resistant —
the EC-fidelity port (EasyCrypt `proof/SecureORO.eca`)

`SecureRO` (`Pilot/SecureRO.lean`) for oracles returning `option`s: `Bounder` answers `None` once
its `bound` queries are used up.  Translated as the pilot `SecureRO`:
* the theory's operators and axioms are the class `Params from to` (`outParam` types: a clone is
  an instance), the module types and modules written as EC's (`RF`, `Bounder(F)`, `A(Bounder(F))`);
* `clone import PROM.FullRO as RO` is the clone's `RO.m`, `FRO.m`, `RO`, `RO.LRO`, `FRO`,
  `RO_LRO_D` (as the pilot `SecureRO`'s);
* the procedure aliases of `RF(R)` (`proc init = R.init`, `proc sample = R.sample`) and of
  `Bounder` (`proc sample = F.sample`) are wrapped in a call (exception E5).
-/

namespace GaudisCrypt.SHA3.Pilot.SecureORO

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM

/-- EC's `op sampleto`, `op bound`, `op increase_counter` and their axioms.  The types are
`outParam`s: a clone of the theory is an instance. -/
class Params («from» «to» : outParam Type) where
  sampleto : SubProbability «to»
  bound : ℤ
  bound_ge0 : 0 ≤ bound
  sampleto_ll : is_lossless sampleto
  sampleto_full : is_full sampleto
  sampleto_fu : is_funiform sampleto
  increase_counter : ℤ → «from» → ℤ
  increase_counter_spec : ∀ c m, c ≤ increase_counter c m

export Params (sampleto bound bound_ge0 sampleto_ll sampleto_full sampleto_fu increase_counter
  increase_counter_spec)

variable {«from» «to» : Type} [DecidableEq «from»] [Inhabited «from»] [Inhabited «to»]

/-! `clone import PROM.FullRO as RO with type in_t <- from, type out_t <- to,
op dout _ <- sampleto, type d_in_t <- unit, type d_out_t <- bool`. -/

variable [Params «from» «to»]

module_var RO.m : FMap «from» «to»

module_var FRO.m : FMap «from» («to» × flag)

omit [Params «from» «to»] in
/-- EC's module type `RO` of the clone (`F : RO`): `PROM`'s `RO_T` at the theory's types. -/
@[nolint unusedArguments]
abbrev RO_T [Params «from» «to»] : Type 1 := PROM.FullRO.RO_T «from» «to»

/-- The clone's `RO`. -/
noncomputable abbrev RO : PROM.FullRO.RO_T «from» «to» :=
  PROM.FullRO.RO.asRO «from» «to» (fun _ => sampleto) RO.m

/-- The clone's lazy `LRO`. -/
noncomputable abbrev RO.LRO : PROM.FullRO.RO_T «from» «to» :=
  PROM.FullRO.LRO «from» «to» (fun _ => sampleto) RO.m

/-- The clone's `FRO`. -/
noncomputable abbrev FRO : PROM.FullRO.FRO_T «from» «to» :=
  PROM.FullRO.FRO «from» «to» (fun _ => sampleto) FRO.m

/-- The clone's `RO_LRO_D`, its side conditions found (`ec_module`, `fp_disjoint`). -/
theorem RO_LRO_D [Countable «from»] [Countable «to»] {d_in d_out : Type} [Inhabited d_in]
    [Inhabited d_out] (D : PROM.FullRO.RO_Distinguisher «from» «to» d_in d_out)
    (hD : Module.ECModule D (PROM.FullRO.RO_ext «from» «to») := by ec_module)
    (hdisj : FVP.fvP D ≤ (RO.m.footprint ⊔ FRO.m.footprint)ᶜ := by fp_disjoint) :
    type_of% (PROM.FullRO.FullEager.RO_LRO_D «from» «to» d_in d_out (fun _ => sampleto) FRO.m
      (fun _ => sampleto_ll) RO.m D hD hdisj) :=
  PROM.FullRO.FullEager.RO_LRO_D «from» «to» d_in d_out (fun _ => sampleto) FRO.m
    (fun _ => sampleto_ll) RO.m D hD hdisj

-- EC's `module type RF`, renamed: EC names the module `RF` too (exception E3)
moduletype RF_T {
  proc init () -> Unit;
  proc get (x : «from») -> (Option «to»);
  proc sample (x : «from») -> Unit;
}

-- EC's `module RF (R : RO) : RF`; its aliases `proc init = R.init`, `proc sample = R.sample` are
-- wrapped in a call (exception E5)
module RF using (R : RO_T) : RF_T {
  proc init () : Unit {
    _ <- call R.init ();
    return ()
  };
  proc get (x : «from») : (Option «to») {
    var y : «to»;
    y <- call R.get ($x);
    return some $y
  };
  proc sample (x : «from») : Unit {
    _ <- call R.sample ($x);
    return ()
  };
}

global_var Bounder.bounder : ℤ

-- `proc sample = F.sample` is wrapped in a call (exception E5)
module Bounder using (F : RF_T) : RF_T {
  proc init () : Unit {
    Bounder.bounder <- 0;
    _ <- call F.init ();
    return ()
  };
  proc get (x : «from») : (Option «to») {
    var y : Option «to»;
    y <- none;
    if (decide ($Bounder.bounder < bound)) {
      Bounder.bounder <- $Bounder.bounder + 1;
      y <- call F.get ($x);
    }
    return $y
  };
  proc sample (x : «from») : Unit {
    _ <- call F.sample ($x);
    return ()
  };
}

-- EasyCrypt's `module type Oracle = { proc get(x : from) : to option {} }`
moduletype Oracle {
  proc get (x : «from») -> (Option «to»);
}

/-- The oracle procedure an adversary with an `Oracle` may call: `F.get` (exception E2). -/
abbrev Oracle.holes : HoleSigs := .cons (procsig («from») -> (Option «to»)) .empty

/-- `F.get` out of the oracle `F`. -/
noncomputable def Oracle.ext (F : Oracle) : (@Oracle.holes «from» «to»).Instantiation :=
  (Oracle.get F).procedure

/-- An `RF` is an `Oracle` (its `get`). -/
module_subtype RF_T <: Oracle

/-- EC's `module type AdvPreimage (F : Oracle) = { proc guess(h : to) : from }`. -/
abbrev AdvPreimage := Oracle →ₘ procmod («to») → «from»

open Classical in
module Preimage using (A : AdvPreimage, F : RF_T) {
  proc main () : Bool {
    var m : «from», hash : «to», hash' : Option «to»;
    hash <$ sampleto;
    _ <- call Bounder(F).init ();
    m <- call A(Bounder(F)).guess ($hash);
    hash' <- call Bounder(F).get ($m);
    return decide ($hash' = some $hash)
  };
}

/-! ### The section `Preimage` -/

namespace Preimage

module FEL using (A : AdvPreimage, F : RF_T) {
  proc main (hash : «to») : «from» {
    var m : «from»;
    _ <- call Bounder(F).init ();
    m <- call A(Bounder(F)).guess ($hash);
    return $m
  };
}

module_var Preimage2.hash : «to»

open Classical in
module Preimage2 using (A : AdvPreimage, F : RF_T) {
  proc main () : Bool {
    var m : «from», hash' : Option «to»;
    Preimage2.hash <$ sampleto;
    m <- call FEL(A, F).main ($Preimage2.hash);
    hash' <- call Bounder(F).get ($m);
    return decide ($hash' = some $Preimage2.hash)
  };
}

end Preimage

section Preimage

declare module A <: AdvPreimage {-RO, -Preimage, -Preimage.Preimage2}

open Preimage in
/-- EC's `RO_is_preimage_resistant &m`. -/
theorem RO_is_preimage_resistant [Countable «from»] (m : VariableAssignment) :
    Pr[ Preimage(A, RF(RO)).main () @ &m : §res ] ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto default := by
  calc Pr[ Preimage(A, RF(RO)).main () @ &m : §res ]
      = Pr[ Preimage2(A, RF(RO)).main () @ &m : §res ] := by
        byequiv; equiv_proc; stmt_inline*; sim / Preimage2.hash
    _ ≤ _ := by
      byphoare (: _ ==> _)
      · phoare_proc
        phoare_seq 2 : (FMap.rng §RO.m §Preimage2.hash)
          (∑ _i ∈ Finset.Ico (0 : ℤ) bound, sampleto.1 {default}) 1 1 (sampleto.1 {default})
          ((FMap.fdom §RO.m).card ≤ §Bounder.bounder ∧ §Bounder.bounder ≤ bound)
        case invariant =>
          hoare_inline*
          hoare_auto
          hoare_call (: (FMap.fdom §RO.m).card ≤ §Bounder.bounder ∧ §Bounder.bounder ≤ bound)
          · hoare_auto
            exact fun _ _ _ => ⟨⟨by simp [FMap.fdom, FMap.empty], bound_ge0⟩, fun _ _ h => h⟩
          · -- the oracle keeps the invariant: a fresh key costs one query (EC's `fcardU`)
            hoare_proc
            hoare_inline*
            hoare_auto
            rintro σ ⟨hc, hb⟩
            split_ifs with hlt
            · simp only [decide_eq_true_eq] at hlt
              refine fun _ _ => ⟨fun hx => ?_, fun _ => ⟨by omega, by omega⟩⟩
              rw [FMap.fcard_set (by simpa using hx)]
              push_cast
              constructor <;> omega
            · exact ⟨hc, hb⟩
        case first_E =>
          phoare_seq 1 : True 1 (∑ _i ∈ Finset.Ico (0 : ℤ) bound, sampleto.1 {default}) 0 _ True
          case invariant => hoare_auto; simp
          case first_notE => phoare_hoare; hoare_auto; simp
          case bound => intros; simp
          case second_E =>
            stmt_exists* §Preimage2.hash
            intro h
            phoare_call (: §Preimage2.hash = h ∧ h = §hash ==> FMap.rng §RO.m h) / Preimage2.hash
            · -- EC's `bypr; have H; exact (H &m)`, then `fel`: here `fel` on the judgment itself
              phoare_proc
              phoare_inline*
              fel §Bounder.bounder (fun _ => sampleto.1 {default}) bound (FMap.rng §RO.m h)
                [(FMap.fdom §RO.m).card ≤ §Bounder.bounder ∧ §Bounder.bounder < bound]
                ((FMap.fdom §RO.m).card ≤ §Bounder.bounder ∧ §Bounder.bounder ≤ bound)
              case sum => exact le_rfl
              case init =>
                hoare_auto
                exact fun _ _ _ => ⟨⟨by simp [FMap.fdom, FMap.empty], bound_ge0⟩, FMap.rng_empty h⟩
              case step =>
                phoare_proc
                phoare_inline*
                phoare_auto
                rintro σ ⟨-, hr, -, -⟩
                split_ifs
                · -- a fresh key's value hits `h` (EC's `rnd (pred1 h)`)
                  rnd_pred1 h
                  · exact indicatorE_le_of_imp fun hs => (FMap.eq_of_rng_set hr hs).symm
                  · exact le_of_eq (sampleto_fu _ _)
                · -- a known key: nothing new in the range (EC's `hoare`)
                  rnd_null
                  exact indicatorE_of_not hr
                · rw [indicatorE_of_not hr]
                  exact bot_le
              case incr =>
                intro c
                hoare_proc
                hoare_inline*
                hoare_auto
                rintro σ ⟨-, -, ⟨hc, hlt⟩, rfl⟩
                split_ifs
                · refine fun _ _ => ⟨fun hx => ⟨?_, Or.inr (by omega)⟩,
                    fun _ => ⟨⟨by omega, by omega⟩, Or.inr (by omega)⟩⟩
                  rw [FMap.fcard_set (by simpa using hx)]
                  push_cast
                  constructor <;> omega
                · simp_all
              case same =>
                intro c
                hoare_proc
                hoare_inline*
                hoare_auto
                rintro σ ⟨⟨hc, hb⟩, hr, hn, rfl⟩
                split_ifs with hlt
                · simp only [decide_eq_true_eq] at hlt
                  exact absurd ⟨hc, hlt⟩ hn
                · exact ⟨⟨hc, hb⟩, hr, le_rfl⟩
              case keep =>
                hoare_proc
                hoare_inline*
                hoare_auto
                rintro σ ⟨⟨hc, hb⟩, hr⟩
                split_ifs with hlt
                · simp only [decide_eq_true_eq] at hlt
                  refine fun a _ => ⟨fun hx => ⟨?_, FMap.rng_set_of_rng (by simpa using hx) hr a⟩,
                    fun _ => ⟨⟨by omega, by omega⟩, hr⟩⟩
                  rw [FMap.fcard_set (by simpa using hx)]
                  push_cast
                  constructor <;> omega
                · exact ⟨⟨hc, hb⟩, hr⟩
            · phoare_skip
              rintro σ ⟨-, hh⟩
              have hh' : Preimage2.hash.get σ.globals = h := hh
              rw [if_pos ⟨⟨hh', hh'.symm⟩, fun _ gl hg => by rw [hg, hh']⟩]
        case second_notE =>
          phoare_inline*
          phoare_auto
          rintro σ ⟨hr, -, -⟩
          split_ifs with hb hd
          · -- a fresh `m`: its value hits `Preimage2.hash` (EC's `rnd (pred1 Preimage2.hash)`)
            rnd_pred1 (Preimage2.hash.get σ.globals)
            · simp only [FMap.get_set_sameE, oget, Option.some.injEq, decide_eq_true_eq]
              exact indicatorE_le_of_imp fun h => h.symm
            · exact le_of_eq (sampleto_fu _ _)
          · -- `m` in `RO.m`: its value is not `Preimage2.hash` (EC's `hoare`)
            rnd_null
            refine indicatorE_of_not ?_
            simp only [Option.some.injEq, decide_eq_true_eq]
            intro he
            apply hr
            have hd' : FMap.dom (RO.m.get σ.globals) ((localVarLens "m" «from»).get σ) := by
              simpa using hd
            obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd')
            refine ⟨(localVarLens "m" «from»).get σ, ?_⟩
            rw [← he]
            simp only [FMap.get] at hv ⊢
            rw [hv]
            rfl
          · exact bot_le
        case bound =>
          -- EC's arithmetic: `∑_{i < bound} μ + μ = (bound + 1) · μ`
          intro _ _
          have := bound_ge0
          show _ ≤ ENNReal.ofReal _
          rw [ofReal_intCast_mul_mu1, sum_Ico_const,
            show (bound + 1).toNat = bound.toNat + 1 by omega]
          push_cast; ring_nf; exact le_rfl
      · have hb := bound_ge0
        exact mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ bound + 1))
          ENNReal.toReal_nonneg

end Preimage

end GaudisCrypt.SHA3.Pilot.SecureORO
