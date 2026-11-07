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
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECCallOneSided
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
    Pr[ Preimage(A, RF(RO)).main () @ &m : §res ]
      ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto default := by
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
          · hoare_auto
            exact fun _ _ _ => ⟨⟨by simp [FMap.fdom, FMap.empty], bound_ge0⟩, fun _ _ h => h⟩
        case first_E =>
          phoare_seq 1 : True 1 (∑ _i ∈ Finset.Ico (0 : ℤ) bound, sampleto.1 {default}) 0 _ True
          case invariant => hoare_auto
          case first_notE => phoare_hoare; hoare_auto
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
          change _ ≤ ENNReal.ofReal _
          rw [ofReal_intCast_mul_mu1, sum_Ico_const,
            show (bound + 1).toNat = bound.toNat + 1 by omega]
          push_cast; ring_nf; exact le_rfl
      · have hb := bound_ge0
        exact mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ bound + 1))
          ENNReal.toReal_nonneg

end Preimage

/-! ## The section `SecondPreimage` -/

/-- EC's `module type AdvSecondPreimage (F : Oracle) = { proc guess(m : from) : from }`. -/
abbrev AdvSecondPreimage := Oracle →ₘ procmod («from») → «from»

open Classical in
module SecondPreimage using (A : AdvSecondPreimage, F : RF_T) {
  proc main (m1 : «from») : Bool {
    var m2 : «from», hash1 : Option «to», hash2 : Option «to»;
    _ <- call Bounder(F).init ();
    m2 <- call A(Bounder(F)).guess ($m1);
    hash1 <- call Bounder(F).get ($m1);
    hash2 <- call Bounder(F).get ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

/-! ### The section `SecondPreimage`, its local modules in the namespace `SecondPreimage` -/

namespace SecondPreimage

module FEL using (A : AdvSecondPreimage, F : RF_T) {
  proc main (m1 : «from») : «from» {
    var m2 : «from»;
    _ <- call Bounder(F).init ();
    _ <- call Bounder(F).sample ($m1);
    m2 <- call A(Bounder(F)).guess ($m1);
    return $m2
  };
}

/-! EC's module variables `SecondPreimage2.m2`, `D1.m1` of the local modules.  The declared
adversary is restricted against the local modules, as EC's local modules are fresh. -/

module_var SecondPreimage2.m2 : «from»

module_var D1.m1 : «from»

open Classical in
module SecondPreimage2 using (A : AdvSecondPreimage, F : RF_T) {
  proc main (m1 : «from») : Bool {
    var hash1 : Option «to», hash2 : Option «to»;
    SecondPreimage2.m2 <- call FEL(A, F).main ($m1);
    hash1 <- call Bounder(F).get ($m1);
    hash2 <- call Bounder(F).get ($SecondPreimage2.m2);
    return decide ($m1 ≠ $SecondPreimage2.m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

-- EC's `D1(A, F)`, used as the `RO_Distinguisher` `D1(A)` (`RO_LRO_D (D1(A))`): `A` is a Lean
-- parameter, so that `D1 A` is a module of its own; `D1(A, F)` is still written as in EC.  Its
-- `distinguish` takes that type's `unit`.
module D1 (A : AdvSecondPreimage) using (F : RO_T) {
  proc distinguish (_x : Unit) : Bool {
    var b : Bool;
    b <- call SecondPreimage2(A, RF(F)).main ($D1.m1);
    return $b
  };
}

-- `A` a Lean parameter, as in `D1`
module SecondPreimage3 (A : AdvSecondPreimage) using (F : RO_T) {
  proc main (m1 : «from») : Bool {
    var b : Bool;
    SecondPreimage2.m2 <- (default : «from»);
    D1.m1 <- $m1;
    _ <- call Bounder(RF(F)).init ();
    b <- call D1(A, F).distinguish (());
    return $b
  };
}

end SecondPreimage

section SecondPreimageSection

-- EC: `{-Bounder, -RO, -FRO}`; the local modules' variables are fresh in EC, here a restriction
declare module A <: AdvSecondPreimage
  {-Bounder, -RO, -FRO, -SecondPreimage.SecondPreimage2, -SecondPreimage.D1}

set_option maxHeartbeats 2000000 in -- one declaration: EC's `have`s, its `byphoare`, its `fel`
open SecondPreimage in
/-- EC's `RO_is_second_preimage_resistant &m (mess1 : from)`, its proof EC's: the chain of
`have->:` (`calc` steps) from `RF(RO)` to `RF(LRO)` (EC's `sim`, its call of `A` EC's
`call (_ : ={glob A, …})`), to `SecondPreimage2`, `SecondPreimage3` and back to `RF(RO)` (the
third and fifth EC's `sim`s, with the local modules' variables as the frame), then
`byphoare(: arg = mess1 ==> _)`, `proc`, `seq 1`, its invariant EC's `call(: … /\ mess1 \in
RO.m)` and its first `E` goal EC's `call(: arg = mess1 ==> rng (rem RO.m mess1) (oget
RO.m.[mess1]))` with EC's `fel 2` (`bad` without its `mess1 \in RO.m`, which is in the
invariant: here `bad` is the event).  The last goal's EC's `rcondt`s, `swap`s and `case`s are
the conditionals split by `split_ifs`. -/
theorem RO_is_second_preimage_resistant [Countable «from»] [Countable «to»]
    (m : VariableAssignment) (mess1 : «from») :
    Pr[ SecondPreimage(A, RF(RO)).main (mess1) @ &m : §res ]
      ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto default := by
  calc Pr[ SecondPreimage(A, RF(RO)).main (mess1) @ &m : §res ]
      = Pr[ SecondPreimage(A, RF(RO.LRO)).main (mess1) @ &m : §res ] := by
        byequiv; equiv_proc; stmt_inline*; sim
        equiv_call (_ : ={glob A, Bounder.bounder, RO.m})
        · equiv_proc; stmt_inline*; sim
        · sim
    _ = Pr[ SecondPreimage2(A, RF(RO.LRO)).main (mess1) @ &m : §res ] := by
        byequiv; equiv_proc; stmt_inline*; sim
    _ = Pr[ SecondPreimage3(A, RO.LRO).main (mess1) @ &m : §res ] := by
        -- EC's `inline*; wp 14 -2; sim`
        byequiv; equiv_proc; stmt_inline*; sim / SecondPreimage2.m2, D1.m1
    _ = Pr[ SecondPreimage3(A, RO).main (mess1) @ &m : §res ] := by
        -- EC's `rewrite eq_sym; byequiv; proc; call (RO_LRO_D (D1(A)) _); inline*; auto`
        symm
        byequiv; equiv_proc
        equiv_call (RO_LRO_D (D1 A))
        stmt_inline*; sim
    _ = Pr[ SecondPreimage2(A, RF(RO)).main (mess1) @ &m : §res ] := by
        -- EC's `inline*; wp -2 17; sim`
        symm
        byequiv; equiv_proc; stmt_inline*; sim / SecondPreimage2.m2, D1.m1
    _ ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto default := by
        byphoare (: §m1 = mess1 ==> _)
        · phoare_proc
          phoare_seq 1 : (FMap.rng (FMap.rem §RO.m mess1) (oget ((§RO.m).get mess1)))
            (∑ _i ∈ Finset.Ico (0 : ℤ) bound, sampleto.1 {default}) 1 1 (sampleto.1 {default})
            (((FMap.fdom §RO.m).card : ℤ) - 1 ≤ §Bounder.bounder ∧ §Bounder.bounder ≤ bound ∧
              FMap.dom §RO.m mess1 ∧ mess1 = §m1)
          case invariant =>
            -- EC's `inline*; auto; call (: … /\ mess1 \in RO.m)`
            hoare_inline*
            hoare_auto
            hoare_call (: ((FMap.fdom §RO.m).card : ℤ) - 1 ≤ §Bounder.bounder ∧
              §Bounder.bounder ≤ bound ∧ FMap.dom §RO.m mess1)
            · -- the oracle keeps it: a fresh key costs one query (EC's `fcardU`)
              hoare_proc
              hoare_inline*
              hoare_auto
              rintro σ ⟨hc, hb, hd⟩
              split_ifs with hlt
              · simp only [decide_eq_true_eq] at hlt
                refine fun a _ => ⟨fun hx => ⟨?_, by omega, (FMap.mem_set _ _ _ _).mpr (Or.inl hd)⟩,
                  fun _ => ⟨by omega, by omega, hd⟩⟩
                rw [FMap.fcard_set (by simpa using hx)]
                push_cast
                omega
              · exact ⟨hc, hb, hd⟩
            · hoare_auto
              rintro m1 rfl a -
              have he : (!decide (FMap.dom (FMap.empty : FMap «from» «to») m1)) = true := by
                simp [FMap.mem_empty]
              simp only [he, if_true]
              refine ⟨⟨?_, bound_ge0, (FMap.mem_set _ _ _ _).mpr (Or.inr rfl)⟩,
                fun _ _ h => ⟨h.1, h.2.1, h.2.2, trivial⟩⟩
              rw [FMap.fcard_set (FMap.mem_empty _)]
              simp [FMap.fdom, FMap.empty]
          case first_E =>
            -- EC's `call(: arg = mess1 ==> rng (rem RO.m mess1) (oget RO.m.[mess1])); auto`
            phoare_call (: §m1 = mess1 ==>
                FMap.rng (FMap.rem §RO.m mess1) (oget ((§RO.m).get mess1)))
            · -- EC's `bypr`, then `fel 2 Bounder.bounder (fun _, mu1 sampleto witness) bound …`;
              -- the event `mess1 \in RO.m` of EC's `bad` is in the invariant
              phoare_proc
              phoare_inline*
              fel §Bounder.bounder (fun _ => sampleto.1 {default}) bound
                (FMap.rng (FMap.rem §RO.m mess1) (oget ((§RO.m).get mess1)))
                [((FMap.fdom §RO.m).card : ℤ) - 1 ≤ §Bounder.bounder ∧ §Bounder.bounder < bound]
                (((FMap.fdom §RO.m).card : ℤ) - 1 ≤ §Bounder.bounder ∧ §Bounder.bounder ≤ bound ∧
                  FMap.dom §RO.m mess1)
              case sum => exact le_rfl
              case init =>
                -- `F.sample(m1)` on the empty `RO.m`: `mess1` in it, nothing else
                hoare_auto
                rintro m1 rfl a -
                have he : (!decide (FMap.dom (FMap.empty : FMap «from» «to») m1)) = true := by
                  simp [FMap.mem_empty]
                simp only [he, if_true]
                refine ⟨⟨?_, bound_ge0, (FMap.mem_set _ _ _ _).mpr (Or.inr rfl)⟩, ?_, trivial⟩
                · rw [FMap.fcard_set (FMap.mem_empty _)]
                  simp [FMap.fdom, FMap.empty]
                · rintro ⟨k, hk⟩
                  by_cases hk1 : k = m1
                  · subst hk1; simp [FMap.rem] at hk
                  · simp [FMap.rem, FMap.set, FMap.empty, Finmap.lookup_erase_ne hk1,
                      Finmap.lookup_insert_of_ne _ hk1] at hk
              case step =>
                phoare_proc
                phoare_inline*
                phoare_auto
                rintro τ ⟨⟨-, -, hd⟩, hr, -⟩
                simp only [indicatorE_of_not hr]
                split_ifs with _ hx
                · -- a fresh key `x ≠ mess1`: the new value hits `RO.m.[mess1]`
                  -- (EC's `rnd (pred1 _)`)
                  have hx' :
                      ¬ FMap.dom (RO.m.get τ.globals) ((localVarLens "x" «from»).get τ) := by
                    simpa using hx
                  have hne : mess1 ≠ (localVarLens "x" «from»).get τ := fun h => hx' (h ▸ hd)
                  rnd_pred1 (oget ((RO.m.get τ.globals).get mess1))
                  · refine indicatorE_le_of_imp fun hs =>
                      (FMap.eq_of_rng_rem_set (x := (localVarLens "x" «from»).get τ) hr ?_).symm
                    rwa [FMap.get_set_neqE _ _ _ _ hne] at hs
                  · exact le_of_eq (sampleto_fu _ _)
                all_goals first
                  | exact bot_le
                  | (rnd_null; rfl)
              case incr =>
                intro c
                hoare_proc
                hoare_inline*
                hoare_auto
                rintro σ ⟨⟨-, -, hd⟩, -, ⟨hc, hlt⟩, rfl⟩
                have hdom := fun x a =>
                  (FMap.mem_set (RO.m.get σ.globals) x a mess1).mpr (Or.inl hd)
                split_ifs
                · refine fun _ _ => ⟨fun hx => ⟨⟨?_, by omega, hdom _ _⟩, Or.inr (by omega)⟩,
                    fun _ => ⟨⟨by omega, by omega, hd⟩, Or.inr (by omega)⟩⟩
                  rw [FMap.fcard_set (by simpa using hx)]
                  push_cast
                  omega
                · simp_all
              case same =>
                intro c
                hoare_proc
                hoare_inline*
                hoare_auto
              case keep =>
                hoare_proc
                hoare_inline*
                hoare_auto
                rintro σ ⟨⟨hc, hb, hd⟩, hr⟩
                split_ifs with hlt
                · simp only [decide_eq_true_eq] at hlt
                  have hdom := fun x a =>
                    (FMap.mem_set (RO.m.get σ.globals) x a mess1).mpr (Or.inl hd)
                  refine fun a _ => ⟨fun hx => ⟨⟨?_, by omega, hdom _ _⟩, ?_⟩,
                    fun _ => ⟨⟨by omega, by omega, hd⟩, hr⟩⟩
                  · rw [FMap.fcard_set (by simpa using hx)]
                    push_cast
                    omega
                  · have hx' :
                        ¬ FMap.dom (RO.m.get σ.globals) ((localVarLens "x" «from»).get σ) := by
                      simpa using hx
                    have hne : mess1 ≠ (localVarLens "x" «from»).get σ := fun h => hx' (h ▸ hd)
                    rw [FMap.get_set_neqE _ _ _ _ hne]
                    exact FMap.rng_rem_set_of_rng hx' hr a
                · exact ⟨⟨hc, hb, hd⟩, hr⟩
            · phoare_skip
              exact fun _ h => le_of_eq (if_pos h)
          case second_notE =>
            phoare_inline*
            phoare_auto
            rintro σ ⟨hr, -, -, hd, hm⟩
            rw [hm] at hr hd
            split_ifs with h1 h2 h3 h4 h5 h6
            · simp [hd] at h2
            · simp [hd] at h2
            · -- a fresh `m2`: its value hits `RO.m.[m1]` (EC's `rnd (pred1 (oget RO.m.[x3]))`); the
              -- first query's sample is not used (`m1` is in `RO.m`)
              rnd_bound
              rnd_pred1 (oget ((RO.m.get σ.globals).get ((localVarLens "m1" «from»).get σ)))
              · refine indicatorE_le_of_imp fun hP => ?_
                simp only [decide_eq_true_eq, FMap.get_set_sameE, oget, Option.some.injEq] at hP
                obtain ⟨-, y, rfl, rfl⟩ := hP
                rfl
              · exact le_of_eq (sampleto_fu _ _)
            · -- `m2` already in `RO.m`, not `m1`: its value is not `RO.m.[m1]`
              -- (`¬ rng (rem RO.m m1) _`)
              rnd_bound
              rnd_null
              refine indicatorE_of_not ?_
              simp only [decide_eq_true_eq, Option.some.injEq]
              rintro ⟨hne, y, hy1, hy2⟩
              apply hr
              have hd2 : FMap.dom (RO.m.get σ.globals) (SecondPreimage2.m2.get σ.globals) := by
                simpa using h5
              obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd2)
              refine ⟨SecondPreimage2.m2.get σ.globals, ?_⟩
              have he := hy1.symm.trans hy2
              have h1 : (FMap.rem (RO.m.get σ.globals) ((localVarLens "m1" «from»).get σ)).get
                  (SecondPreimage2.m2.get σ.globals) = (RO.m.get σ.globals).get
                    (SecondPreimage2.m2.get σ.globals) := by
                rw [FMap.remE, if_neg (Ne.symm hne)]
              simp only [FMap.get] at h1 hw he ⊢
              rw [h1, hw, he, hw]
              rfl
            all_goals first
              | exact absurd h6 h1
              | (rnd_null; refine indicatorE_of_not ?_; simp)
              | (rw [indicatorE_of_not (by simp)]; exact bot_le)
          case bound =>
            -- EC's arithmetic: `∑_{i < bound} μ + μ = (bound + 1) · μ`
            intro _ _
            have := bound_ge0
            change _ ≤ ENNReal.ofReal _
            rw [ofReal_intCast_mul_mu1, sum_Ico_const,
              show (bound + 1).toNat = bound.toNat + 1 by omega]
            push_cast; ring_nf; exact le_rfl
        · have hb := bound_ge0
          exact mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ bound + 1))
            ENNReal.toReal_nonneg


end SecondPreimageSection

/-! ## The section `Collision` -/

/-- EC's `module type AdvCollision (F : Oracle) = { proc guess() : from * from }`. -/
abbrev AdvCollision := Oracle →ₘ procmod () → («from» × «from»)

open Classical in
module Collision using (A : AdvCollision, F : RF_T) {
  proc main () : Bool {
    var m1 : «from», m2 : «from», hash1 : Option «to», hash2 : Option «to»;
    _ <- call Bounder(F).init ();
    m1, m2 <- call A(Bounder(F)).guess ();
    hash1 <- call Bounder(F).get ($m1);
    hash2 <- call Bounder(F).get ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

/-! ### The section `Collision`, with `declare module A <: AdvCollision {-RO, -FRO, -Bounder}` (its
local modules in the namespace `Collision`) -/

namespace Collision

module FEL using (A : AdvCollision, F : RF_T) {
  proc main () : («from» × «from») {
    var m1 : «from», m2 : «from»;
    _ <- call Bounder(F).init ();
    m1, m2 <- call A(Bounder(F)).guess ();
    return ($m1, $m2)
  };
}

open Classical in
module Collision2 using (A : AdvCollision, F : RF_T) {
  proc main () : Bool {
    var m1 : «from», m2 : «from», hash1 : Option «to», hash2 : Option «to»;
    m1, m2 <- call FEL(A, F).main ();
    hash1 <- call Bounder(F).get ($m1);
    hash2 <- call Bounder(F).get ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

end Collision

section CollisionSection

declare module A <: AdvCollision {-RO, -FRO, -Bounder}

-- EC's `op collision`, generic as EC's (`Lib/EC/FMap.lean`)
open FMap (collision)

set_option maxHeartbeats 1000000 in -- one declaration: EC's `have`, its `byphoare`, its `fel`
/-- EC's `RO_is_collision_resistant &m`, its proof EC's: the `have->:` by `byequiv` (a `calc`
step), then `byphoare`, `proc`, `seq 1`, its invariant EC's `call(: card (fdom RO.m) <=
Bounder.bounder <= bound)`, its first `E` goal EC's `call(: true ==> collision RO.m)` with EC's
`fel 1`, its last goal's EC's `rcondt`s, `swap`s and `case`s the conditionals split by
`split_ifs` and EC's `case`s on `m1 = m2`, `m2 \in RO.m` (`by_cases`), and the arithmetic of EC's
last `smt()` in the `bound` goal. -/
theorem RO_is_collision_resistant [Countable «from»] (m : VariableAssignment) :
    Pr[ Collision(A, RF(RO)).main () @ &m : §res ]
      ≤ ((bound * (bound - 1) + 2 : ℤ) : ℝ) / 2 * mu1 sampleto default := by
  have hb := bound_ge0
  calc Pr[ Collision(A, RF(RO)).main () @ &m : §res ]
      = Pr[ Collision.Collision2(A, RF(RO)).main () @ &m : §res ] := by
        byequiv; equiv_proc; stmt_inline*; sim
    _ ≤ ((bound * (bound - 1) + 2 : ℤ) : ℝ) / 2 * mu1 sampleto default := by
        byphoare
        · phoare_proc
          phoare_seq 1 : (collision §RO.m)
            (∑ i ∈ Finset.Ico (0 : ℤ) bound, (i.toNat : ENNReal) * sampleto.1 {default}) 1 1
            (sampleto.1 {default})
            (((FMap.fdom §RO.m).card : ℤ) ≤ §Bounder.bounder ∧ §Bounder.bounder ≤ bound)
          case invariant =>
            -- EC's `inline*; wp; call(: card (fdom RO.m) <= Bounder.bounder <= bound); auto`
            hoare_inline*
            hoare_auto
            hoare_call (: ((FMap.fdom §RO.m).card : ℤ) ≤ §Bounder.bounder ∧
              §Bounder.bounder ≤ bound)
            · -- the oracle keeps it: a fresh key costs one query (EC's `fcardU`)
              hoare_proc
              hoare_inline*
              hoare_auto
              rintro σ ⟨hc, hcb⟩
              split_ifs with hlt
              · simp only [decide_eq_true_eq] at hlt
                refine fun _ _ => ⟨fun hx => ⟨?_, by omega⟩, fun _ => ⟨by omega, by omega⟩⟩
                rw [FMap.fcard_set (by simpa using hx)]
                push_cast
                omega
              · exact ⟨hc, hcb⟩
            · hoare_auto
          case first_E =>
            -- EC's `call(: true ==> collision RO.m); auto`
            phoare_call (: True ==> collision §RO.m)
            · -- EC's `bypr`, then `fel 1 Bounder.bounder (fun i, i%r * mu1 sampleto witness) bound
              -- (collision RO.m) …`
              phoare_proc
              phoare_inline*
              fel §Bounder.bounder (fun i => (i.toNat : ENNReal) * sampleto.1 {default}) bound
                (collision §RO.m)
                [((FMap.fdom §RO.m).card : ℤ) ≤ §Bounder.bounder ∧ §Bounder.bounder < bound]
                (((FMap.fdom §RO.m).card : ℤ) ≤ §Bounder.bounder ∧ §Bounder.bounder ≤ bound)
              case sum => exact le_rfl
              case init =>
                hoare_auto
                exact fun _ => ⟨⟨by simp [FMap.fdom, FMap.empty], hb⟩, FMap.collision_empty⟩
              case step =>
                phoare_proc
                phoare_inline*
                phoare_auto
                rintro τ ⟨-, hc, hi, -⟩
                simp only [indicatorE_of_not hc]
                split_ifs with _ hx
                · -- a fresh key: a collision only if its value is already in `RO.m` (EC's `mu_mem`)
                  have hx' :
                      ¬ FMap.dom (RO.m.get τ.globals) ((localVarLens "x" «from»).get τ) := by
                    simpa using hx
                  refine (mu_le fun a => indicatorE_le_of_imp
                    (FMap.rng_of_collision_set hx' hc)).trans ?_
                  refine (FMap.mu_rng_le sampleto_fu _).trans ?_
                  gcongr
                  have :
                      (FMap.fdom (RO.m.get τ.globals)).card ≤
                        (Bounder.bounder.get τ.globals).toNat := by
                    omega
                  exact_mod_cast this
                all_goals first
                  | exact bot_le
                  | (rnd_null; rfl)
              case incr =>
                intro c
                hoare_proc
                hoare_inline*
                hoare_auto
                rintro σ ⟨-, -, ⟨hc, hlt⟩, rfl⟩
                split_ifs
                · refine fun _ _ => ⟨fun hx => ⟨⟨?_, by omega⟩, Or.inr (by omega)⟩,
                    fun _ => ⟨⟨by omega, by omega⟩, Or.inr (by omega)⟩⟩
                  rw [FMap.fcard_set (by simpa using hx)]
                  push_cast
                  omega
                · simp_all
              case same =>
                intro c
                hoare_proc
                hoare_inline*
                hoare_auto
              case keep =>
                hoare_proc
                hoare_inline*
                hoare_auto
                rintro σ ⟨⟨hc, hcb⟩, hr⟩
                split_ifs with hlt
                · simp only [decide_eq_true_eq] at hlt
                  refine fun a _ => ⟨fun hx => ⟨⟨?_, by omega⟩,
                    FMap.collision_set (by simpa using hx) hr a⟩,
                    fun _ => ⟨⟨by omega, by omega⟩, hr⟩⟩
                  rw [FMap.fcard_set (by simpa using hx)]
                  push_cast
                  omega
                · exact ⟨⟨hc, hcb⟩, hr⟩
            · phoare_skip
              intros
              exact le_rfl
          case second_notE =>
            phoare_inline*
            phoare_auto
            rintro σ ⟨hnc, -, -⟩
            have hfu := sampleto_fu
            set ROm := RO.m.get σ.globals
            set m1 := (localVarLens "m1" «from»).get σ
            set m2 := (localVarLens "m2" «from»).get σ
            split_ifs with h1 h2 h3 h4 h5 h6
            · -- `m1` fresh, sampled `a`; by cases on `m2` (EC's `case: (m1 = m2)`,
              -- `case: (m2 \in RO.m)`)
              have hd1 : ¬ FMap.dom ROm m1 := by simpa using h2
              by_cases hk1 : m2 = m1
              · -- `m2 = m1`: the event wants them distinct
                rnd_bound
                rnd_null
                split_ifs <;> exact indicatorE_of_not (by simp [hk1])
              by_cases hk2 : FMap.dom ROm m2
              · -- `m2` already in `RO.m`: `m1`'s value hits it
                -- (EC's `rnd (pred1 (oget RO.m.[m2]))`)
                rnd_pred1 (oget (ROm.get m2))
                · split_ifs with hc
                  · rnd_bound
                    exact absurd ((FMap.mem_set _ _ _ _).mpr (Or.inl hk2)) (by simpa using hc)
                  · rnd_bound
                    refine indicatorE_le_of_imp fun hP => ?_
                    simp only [decide_eq_true_eq, FMap.get_set_sameE, FMap.get_set_neqE _ _ _ _ hk1,
                      oget, Option.some.injEq] at hP
                    obtain ⟨-, y, rfl, h⟩ := hP
                    exact h.symm
                · exact le_of_eq (hfu _ _)
              · -- `m2` fresh too: its value hits `a` (EC's `rnd (pred1 r)`)
                rnd_bound
                split_ifs with hc
                · rnd_pred1 a
                  · refine indicatorE_le_of_imp fun hP => ?_
                    simp only [decide_eq_true_eq, FMap.get_set_sameE, oget, Option.some.injEq] at hP
                    obtain ⟨-, y, rfl, h⟩ := hP
                    exact h
                  · exact le_of_eq (hfu _ _)
                · exact absurd (by simpa using hc) fun h =>
                    ((FMap.mem_set _ _ _ _).mp h).elim hk2 hk1
            · (rnd_null; refine indicatorE_of_not ?_; simp)
            · -- `m1` in `RO.m` (its sample unused), `m2` fresh: `m2`'s value hits `RO.m.[m1]`
              rnd_bound
              rnd_pred1 (oget (ROm.get m1))
              · refine indicatorE_le_of_imp fun hP => ?_
                simp only [decide_eq_true_eq, FMap.get_set_sameE, oget, Option.some.injEq] at hP
                obtain ⟨-, y, rfl, rfl⟩ := hP
                rfl
              · exact le_of_eq (hfu _ _)
            · -- both in `RO.m`: equal values would be a collision already
              rnd_bound
              rnd_null
              refine indicatorE_of_not ?_
              simp only [decide_eq_true_eq, Option.some.injEq]
              rintro ⟨hne, y, hy1, hy2⟩
              apply hnc
              have hd1 : FMap.dom ROm m1 := by simpa using h2
              have hd2 : FMap.dom ROm m2 := by simpa using h5
              obtain ⟨v1, hv1⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd1)
              obtain ⟨v2, hv2⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd2)
              refine ⟨_, _, hne, hd1, hd2, ?_⟩
              have he := hy1.symm.trans hy2
              rw [hv1, hv2] at he ⊢
              simp only [oget, Option.getD_some] at he
              rw [he]
            all_goals first
              | exact absurd h6 h1
              | (rnd_null; refine indicatorE_of_not ?_; simp)
              | (rw [indicatorE_of_not (by simp)]; exact bot_le)
          case bound =>
            -- EC's arithmetic: `∑_{i < bound} i · μ + μ = (bound (bound - 1) + 2) / 2 · μ`
            intros
            simp only [mul_one, one_mul]
            have hμ := mu_ne_top sampleto default
            obtain ⟨n, hn'⟩ : ∃ n : ℕ, bound = n := ⟨bound.toNat, (Int.toNat_of_nonneg hb).symm⟩
            rw [hn', sum_Ico_toNat n (fun i => (i : ENNReal) * sampleto.1 {default})]
            have hsum_ne : (∑ i ∈ Finset.range n, (i : ENNReal) * sampleto.1 {default}) ≠ ⊤ :=
              ENNReal.sum_ne_top.mpr fun i _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top i) hμ
            rw [← ENNReal.ofReal_toReal (ENNReal.add_ne_top.mpr ⟨hsum_ne, hμ⟩)]
            refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
            rw [ENNReal.toReal_add hsum_ne hμ, ENNReal.toReal_sum (fun i _ =>
              ENNReal.mul_ne_top (ENNReal.natCast_ne_top i) hμ)]
            simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast]
            rw [← Finset.sum_mul, mu1]
            have hsum : (∑ i ∈ Finset.range n, (i : ℝ)) * 2 = n * (n - 1) := by
              rcases Nat.eq_zero_or_pos n with rfl | hn
              · simp
              have := Finset.sum_range_id_mul_two n
              have h' : ((∑ i ∈ Finset.range n, i : ℕ) : ℝ) * 2 = (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
                exact_mod_cast this
              rw [Nat.cast_sum, Nat.cast_sub hn, Nat.cast_one] at h'
              exact h'
            have hs : (∑ i ∈ Finset.range n, (i : ℝ)) = n * (n - 1) / 2 := by linarith [hsum]
            push_cast
            rw [hs]
            ring
        · have h0 : (0 : ℤ) ≤ bound * (bound - 1) + 2 := by nlinarith [sq_nonneg (bound - 1)]
          exact mul_nonneg (div_nonneg (by exact_mod_cast h0) (by norm_num))
            ENNReal.toReal_nonneg

end CollisionSection

end GaudisCrypt.SHA3.Pilot.SecureORO
