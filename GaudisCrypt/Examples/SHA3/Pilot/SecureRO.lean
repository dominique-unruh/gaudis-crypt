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
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Lib.EC.StdBigop
import GaudisCrypt.Logic.ModuleFootprint
import GaudisCrypt.Syntax.ModuleVar
import GaudisCrypt.Syntax.ModuleSubtype

/-!
# Random oracles are preimage, second-preimage and collision resistant — the EC-fidelity pilot
(EasyCrypt `proof/SecureRO.eca`)

The refactor pilot of `notes/SHA3/Refactor.md`: EC's file transcribed one to one, its
declarations and its proofs EC's (`Examples/SHA3/SecureRO.lean` is the first port).  The facts
EC's `smt()` finds on maps and bounds are `Lib/EC/FMap.lean`'s and `Lib/EC/Mu.lean`'s.

Translation:
* the theory's operators and axioms are the class `Params from to`, whose types are `outParam`s:
  the one instance in scope (EC's clone) fixes them, so `bound`, `sampleto`, the module types
  `RF`, `Oracle`, `RO_T` are written without types, as in EC;
* module variables are `global_var`s and `module_var`s (`Counter.c`, `RO.m`, `D1.m1`), found
  disjoint by instance search; `declare module A <: T {-…}` is EC's declaration;
* EC's paths `M(A, B).f` are terms (`Syntax/ModuleApplicationSyntax.lean`), EC's subtyping of
  module types coercions (`module_subtype`), inserted on the arguments (`A(Bounder(F))`);
* the proofs use EC's tactics under prefixed names: `proc`, `inline*`, `sim`, `auto`, `seq`,
  `call (: …)`, `fel`, `rnd`, `byequiv`, `byphoare` (`notes/SHA3/Refactor.md`, phase 2).
-/

namespace GaudisCrypt.SHA3.Pilot.SecureRO

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM

/-! `type from, to.`, the operators and their axioms. -/

/-- EC's `op sampleto`, `op bound`, `op increase_counter`, `op bound_counter` and their axioms.
The types are `outParam`s: a clone of the theory is an instance. -/
class Params («from» «to» : outParam Type) where
  sampleto : SubProbability «to»
  bound : ℤ
  bound_gt0 : 0 < bound
  sampleto_ll : is_lossless sampleto
  sampleto_full : is_full sampleto
  sampleto_fu : is_funiform sampleto
  increase_counter : ℤ → «from» → ℤ
  increase_counter_spec : ∀ c m, c ≤ increase_counter c m
  bound_counter : ℤ
  bound_counter_ge0 : 0 ≤ bound_counter

export Params (sampleto bound bound_gt0 sampleto_ll sampleto_full sampleto_fu increase_counter
  increase_counter_spec bound_counter bound_counter_ge0)

variable {«from» «to» : Type} [DecidableEq «from»] [Inhabited «from»] [Inhabited «to»]


/-! `clone import PROM.FullRO as RO with type in_t <- from, type out_t <- to,
op dout _ <- sampleto, …`: its module variable `RO.m`, and its module `RO`. -/

variable [Params «from» «to»]

/-- The clone's module variables `RO.m`, `FRO.m` (`module_var`: they take the theory's instance,
whose `outParam`s fix their types). -/
module_var RO.m : FMap «from» «to»

module_var FRO.m : FMap «from» («to» × flag)

/-! The module types.  Their types are the theory's (implicit, fixed by `Params`'s `outParam`s), so
they are written as in EC: `RF`, `Oracle`, `AdvPreimage`. -/

moduletype RF {
  proc init () -> Unit;
  proc get (x : «from») -> «to»;
}

-- EasyCrypt's `module type Oracle = { proc get(x : from) : to {} }`
moduletype Oracle {
  proc get (x : «from») -> «to»;
}

/-- The oracle procedure an adversary with an `Oracle` may call: `F.get`.  The hole of its
representation (`Module.Representable`, exception E2). -/
abbrev Oracle.holes : HoleSigs := .cons (procsig («from») -> «to») .empty

/-- `F.get` out of the oracle `F`. -/
noncomputable def Oracle.ext (F : Oracle) : (@Oracle.holes «from» «to»).Instantiation :=
  (Oracle.get F).procedure

/-- EC's `module type AdvPreimage (F : Oracle) = { proc guess(h : to) : from }`. -/
abbrev AdvPreimage := Oracle →ₘ procmod («to») → «from»

/-- EC's `module type AdvSecondPreimage (F : Oracle) = { proc guess(m : from) : from }`. -/
abbrev AdvSecondPreimage := Oracle →ₘ procmod («from») → «from»

/-- EC's `module type AdvCollision (F : Oracle) = { proc guess() : from * from }`. -/
abbrev AdvCollision := Oracle →ₘ procmod () → («from» × «from»)

/-! EC's subtyping of module types, as coercions.  Each is a `fun` building the smaller module
in place: the coercion then unfolds to that record, which is what the `module` command reads a
callee like `A(Bounder(F))` back from (a named coercion function it would not see through). -/

/-- An `RF` is an `Oracle` (its `get`). -/
module_subtype RF <: Oracle

/-- The random oracle (`PROM`'s `RO`) is an `RF` (its `init` and `get`). -/
module_subtype (PROM.FullRO.RO_T «from» «to») <: RF

omit [Params «from» «to»] in
/-- EC's module type `RO` of the clone (`F : RO`): `PROM`'s `RO_T` at the theory's types, which
the instance fixes (EC names the module type and the module alike; here the module is `RO`). -/
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

/-- The clone's `RO_LRO_D` (`PROM.FullRO`'s, at the clone's `dout` and module variables, its
`dout_ll` the theory's `sampleto_ll`): a distinguisher cannot tell `RO` from `LRO`.  Its side
conditions, which EC checks itself, are found (`ec_module`, `fp_disjoint`). -/
theorem RO_LRO_D [Countable «from»] [Countable «to»] {d_in d_out : Type} [Inhabited d_in]
    [Inhabited d_out] (D : PROM.FullRO.RO_Distinguisher «from» «to» d_in d_out)
    (hD : Module.ECModule D (PROM.FullRO.RO_ext «from» «to») := by ec_module)
    (hdisj : FVP.fvP D ≤ (RO.m.footprint ⊔ FRO.m.footprint)ᶜ := by fp_disjoint) :
    type_of% (PROM.FullRO.FullEager.RO_LRO_D «from» «to» d_in d_out (fun _ => sampleto) FRO.m
      (fun _ => sampleto_ll) RO.m D hD hdisj) :=
  PROM.FullRO.FullEager.RO_LRO_D «from» «to» d_in d_out (fun _ => sampleto) FRO.m
    (fun _ => sampleto_ll) RO.m D hD hdisj

/-- `RO` at the module type `RF` (the coercion, written out where a name is wanted). -/
noncomputable abbrev RO.asRF : RF := (RO : RF)

global_var Counter.c : ℤ

module Counter {
  proc init () : Unit {
    Counter.c <- 0;
    return ()
  };
}

global_var Bounder.bounder : ℤ

module Bounder using (F : RF) : RF {
  proc init () : Unit {
    Bounder.bounder <- 0;
    _ <- call Counter.init ();
    _ <- call F.init ();
    return ()
  };
  proc get (x : «from») : «to» {
    var y : «to»;
    y <- (default : «to»);
    if (decide ($Bounder.bounder < bound)) {
      Bounder.bounder <- $Bounder.bounder + 1;
      if (decide (increase_counter $Counter.c $x < bound_counter)) {
        Counter.c <- increase_counter $Counter.c $x;
        y <- call F.get ($x);
      }
    }
    return $y
  };
}

open Classical in
module Preimage using (A : AdvPreimage, F : RF) {
  proc main (hash : «to») : Bool {
    var b : Bool, m : «from», hash' : «to»;
    _ <- call Counter.init ();
    _ <- call Bounder(F).init ();
    m <- call A(Bounder(F)).guess ($hash);
    if (decide (increase_counter $Counter.c $m < bound_counter)) {
      hash' <- call F.get ($m);
      b <- decide ($hash = $hash');
    } else {
      b <- false;
    }
    return $b
  };
}

/-! ### The section `Preimage` -/

namespace Preimage

module FEL using (A : AdvPreimage, F : RF) {
  proc main (hash : «to») : «from» {
    var m : «from»;
    _ <- call Bounder(F).init ();
    m <- call A(Bounder(F)).guess ($hash);
    return $m
  };
}

open Classical in
module Preimage2 using (A : AdvPreimage, F : RF) {
  proc main (hash : «to») : Bool {
    var b : Bool, m : «from», hash' : «to»;
    m <- call FEL(A, F).main ($hash);
    if (decide (increase_counter $Counter.c $m < bound_counter)) {
      hash' <- call F.get ($m);
      b <- decide ($hash = $hash');
    } else {
      b <- false;
    }
    return $b
  };
}

end Preimage

-- after the section's local modules, whose parameter `A` is their own
section Preimage

declare module A <: AdvPreimage {-RO, -Preimage}

/-! ### The proof of `RO_is_preimage_resistant`

One proof, as EC's: EC's `fel` is the tactic `fel` (`Logic/FelTactic.lean`), EC's inline
specifications `call (: P ==> Q)` and `byphoare (: P ==> _)` are `Logic/CallSpec.lean`'s. -/

/-- EC's `RO_is_preimage_resistant &m (h : to)`, its proof EC's: the `have->:` by `byequiv`
(here a `calc` step), then `byphoare(: arg = h ==> _)`, `proc`, `seq 1`, its first `E` goal
EC's `call(: true ==> rng RO.m h)` with EC's `fel`, and the arithmetic of EC's last `smt()` in
the `bound` goal.  The oracle's bullets are EC's `proc; inline*; auto`, then the logic EC leaves
to `smt()`, its `FMap` facts `Lib/EC/FMap.lean`'s. -/
theorem RO_is_preimage_resistant [Countable «from»] (m : VariableAssignment) (h : «to») :
    Pr[ Preimage(A, RO).main (h) @ &m : §res ] ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto h := by
  calc Pr[ Preimage(A, RO).main (h) @ &m : §res ]
      = Pr[ Preimage.Preimage2(A, RO).main (h) @ &m : §res ] := by
        byequiv; equiv_proc; stmt_inline*; sim
    _ ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto h := by
      byphoare (: §hash = h ==> _)
      · phoare_proc
        phoare_seq 1 : (FMap.rng §RO.m h) (∑ _i ∈ Finset.Ico (0 : ℤ) bound, sampleto.1 {h})
          1 1 (sampleto.1 {h}) (§hash = h)
        case invariant =>
          hoare_call
          hoare_skip
          exact fun _ h _ _ => h
        case first_E =>
          phoare_call (: True ==> FMap.rng §RO.m h)
          · phoare_proc
            phoare_inline*
            fel §Bounder.bounder (fun _ => sampleto.1 {h}) bound (FMap.rng §RO.m h)
              [§Bounder.bounder < bound] True
            case sum => exact le_rfl
            case init =>
              hoare_auto
              intros
              simp [FMap.rng_empty]
            case step =>
              phoare_proc
              phoare_inline*
              ec_auto
              ec_intro
              rintro ⟨hr, _⟩
              simp only [indicatorE_of_not hr]
              split_ifs
              · rnd_pred1 h
                exact indicatorE_le_of_imp fun hs => (FMap.eq_of_rng_set hr hs).symm
              all_goals first
                | exact bot_le
                | (rnd_null; rfl)
            case incr =>
              intro c
              hoare_proc
              hoare_inline*
              ec_auto
            case same =>
              intro c
              hoare_proc
              hoare_inline*
              ec_auto
            case keep =>
              hoare_proc
              hoare_inline*
              ec_auto
              ec_intro
              intro hr
              split_ifs <;> simp_all [FMap.rng_set_of_rng]
          · phoare_skip
            intros
            exact le_rfl
        case second_notE =>
          phoare_inline*
          phoare_auto
          rintro ROm hash c x ⟨hr, rfl⟩
          split_ifs with _ hd
          · rnd_pred1 hash
            simp only [FMap.get_set_sameE, decide_eq_true_eq]
            exact le_rfl
          · have hne : hash ≠ oget (ROm.get x) := by
              intro he
              apply hr
              have hd' : FMap.dom ROm x := by simpa using hd
              obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd')
              refine ⟨x, ?_⟩
              rw [he]
              simp only [FMap.get] at hv ⊢
              rw [hv]
              rfl
            rnd_null
            exact indicatorE_of_not (by simpa only [decide_eq_true_eq] using hne)
          · exact bot_le
        case bound =>
          -- EC's arithmetic: `∑_{i < bound} μ + μ = (bound + 1) · μ`
          intro _ _
          have := bound_gt0
          show _ ≤ ENNReal.ofReal _
          rw [ofReal_intCast_mul_mu1, sum_Ico_const,
            show (bound + 1).toNat = bound.toNat + 1 by omega]
          push_cast; ring_nf; exact le_rfl
      · have hb := bound_gt0
        exact mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ bound + 1))
          ENNReal.toReal_nonneg

end Preimage

/-! ## The section `SecondPreimage` -/

open Classical in
module SecondPreimage using (A : AdvSecondPreimage, F : RF) {
  proc main (m1 : «from») : Bool {
    var b : Bool, m2 : «from», hash1 : «to», hash2 : «to»;
    _ <- call Bounder(F).init ();
    m2 <- call A(Bounder(F)).guess ($m1);
    if (decide (increase_counter $Counter.c $m1 < bound_counter)) {
      Counter.c <- increase_counter $Counter.c $m1;
      hash1 <- call F.get ($m1);
      if (decide (increase_counter $Counter.c $m2 < bound_counter)) {
        Counter.c <- increase_counter $Counter.c $m2;
        hash2 <- call F.get ($m2);
        b <- decide ($hash1 = $hash2 ∧ $m1 ≠ $m2);
      } else {
        b <- false;
      }
    } else {
      b <- false;
    }
    return $b
  };
}

/-! ### The section `SecondPreimage`, with `declare module A <: AdvSecondPreimage {-Bounder, -RO,
-FRO}` (its local modules in the namespace `SecondPreimage`) -/

namespace SecondPreimage

module FEL using (A : AdvSecondPreimage, F : RO_T) {
  proc main (m1 : «from») : «from» {
    var m2 : «from»;
    _ <- call Bounder(F).init ();
    _ <- call F.sample ($m1);
    m2 <- call A(Bounder(F)).guess ($m1);
    return $m2
  };
}

/-! EC's module variables `SecondPreimage2.m2`, `D1.m1` of the local modules.  The declared
adversary is restricted against the local modules, as EC's local modules are fresh. -/

module_var SecondPreimage2.m2 : «from»

module_var D1.m1 : «from»

open Classical in
module SecondPreimage2 using (A : AdvSecondPreimage, F : RO_T) {
  proc main (m1 : «from») : Bool {
    var b : Bool, hash1 : «to», hash2 : «to»;
    SecondPreimage2.m2 <- call FEL(A, F).main ($m1);
    if (decide (increase_counter $Counter.c $m1 < bound_counter)) {
      Counter.c <- increase_counter $Counter.c $m1;
      hash1 <- call F.get ($m1);
      if (decide (increase_counter $Counter.c $SecondPreimage2.m2 < bound_counter)) {
        Counter.c <- increase_counter $Counter.c $SecondPreimage2.m2;
        hash2 <- call F.get ($SecondPreimage2.m2);
        b <- decide ($hash1 = $hash2 ∧ $m1 ≠ $SecondPreimage2.m2);
      } else {
        b <- false;
      }
    } else {
      b <- false;
    }
    return $b
  };
}

-- EC's `D1(A, F)`, used as the `RO_Distinguisher` `D1(A)` (`RO_LRO_D (D1(A))`): `A` is a Lean
-- parameter, so that `D1 A` is a module of its own; `D1(A, F)` is still written as in EC.  Its
-- `distinguish` takes that type's `unit`.
module D1 (A : AdvSecondPreimage) using (F : RO_T) {
  proc distinguish (_x : Unit) : Bool {
    var b : Bool;
    b <- call SecondPreimage2(A, F).main ($D1.m1);
    return $b
  };
}

-- `A` a Lean parameter, as in `D1`
module SecondPreimage3 (A : AdvSecondPreimage) using (F : RO_T) {
  proc main (m1 : «from») : Bool {
    var b : Bool;
    SecondPreimage2.m2 <- (default : «from»);
    D1.m1 <- $m1;
    _ <- call Bounder(F).init ();
    b <- call D1(A, F).distinguish (());
    return $b
  };
}

end SecondPreimage

section SecondPreimageSection

-- EC: `{-Bounder, -RO, -FRO}`; the local modules' variables are fresh in EC, here a restriction
declare module A <: AdvSecondPreimage
  {-Bounder, -RO, -FRO, -SecondPreimage.SecondPreimage2, -SecondPreimage.D1}

set_option maxHeartbeats 1000000 in -- one declaration: EC's `have`s, its `byphoare`, its `fel`
open SecondPreimage in
/-- EC's `RO_is_second_preimage_resistant &m (mess1 : from)`, its proof EC's: the chain of
`have->:` (`calc` steps) from `RO` to `LRO`, to `SecondPreimage2`, `SecondPreimage3` and back to
`RO` (the third and fifth EC's `sim`s, with the local modules' variables as the frame), then
`byphoare(: arg = mess1 ==> _)`, `proc`, `seq 1`, its invariant EC's
`call(: … /\ mess1 \in RO.m)` and its first `E` goal EC's `call(: arg = mess1 ==> rng (rem RO.m
mess1) (oget RO.m.[mess1]))` with EC's `fel 2`, and the arithmetic of EC's last `smt()` in the
`bound` goal. -/
theorem RO_is_second_preimage_resistant [Countable «from»] [Countable «to»]
    (m : VariableAssignment) (mess1 : «from») :
    Pr[ SecondPreimage(A, RO).main (mess1) @ &m : §res ]
      ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto default := by
  calc Pr[ SecondPreimage(A, RO).main (mess1) @ &m : §res ]
      = Pr[ SecondPreimage(A, RO.LRO).main (mess1) @ &m : §res ] := by
        -- at the module type `RF`, `RO` and `LRO` are the same module (they differ in `sample`)
        simp only [RO, RO.LRO, PROM.FullRO.LRO, PROM.FullRO.RO.asRO,
          PROM.FullRO.RO_T.init.mk_simp, PROM.FullRO.RO_T.get.mk_simp]
    _ = Pr[ SecondPreimage.SecondPreimage2(A, RO.LRO).main (mess1) @ &m : §res ] := by
        byequiv; equiv_proc; stmt_inline*; sim
    _ = Pr[ SecondPreimage3(A, RO.LRO).main (mess1) @ &m : §res ] := by
        -- EC's `inline*; wp 8 -2; sim`: the states differ in the local modules' variables
        byequiv; equiv_proc; stmt_inline*; sim / SecondPreimage2.m2, D1.m1
    _ = Pr[ SecondPreimage3(A, RO).main (mess1) @ &m : §res ] := by
        -- EC's `proc; call (RO_LRO_D (D1(A)) _); inline*; auto`
        symm
        byequiv; equiv_proc
        equiv_call (RO_LRO_D (D1 A))
        stmt_inline*; sim
    _ = Pr[ SecondPreimage.SecondPreimage2(A, RO).main (mess1) @ &m : §res ] := by
        -- EC's `inline*; wp -2 11; sim`
        symm
        byequiv; equiv_proc; stmt_inline*; sim / SecondPreimage2.m2, D1.m1
    _ ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto default := by
        byphoare (: §m1 = mess1 ==> _)
        · phoare_proc
          phoare_seq 1 : (FMap.rng (FMap.rem §RO.m mess1) (oget ((§RO.m).get mess1)))
            (∑ _i ∈ Finset.Ico (0 : ℤ) bound, sampleto.1 {default}) 1 1 (sampleto.1 {default})
            (FMap.dom §RO.m mess1 ∧ §m1 = mess1)
          case invariant =>
            hoare_call (: §m1 = mess1 ==> FMap.dom §RO.m mess1)
            · -- EC's `call (: … /\ mess1 \in RO.m)` on `FEL`: `mess1` is in `RO.m` afterwards
              hoare_proc
              hoare_inline*
              hoare_call (: FMap.dom §RO.m mess1)
              case oracle =>
                -- `Bounder(RO).get` keeps a key in `RO.m`
                hoare_proc
                hoare_inline*
                ec_auto
                ec_intro
                intro hd
                have hdom : ∀ x a, FMap.dom (FMap.set m1 x a) mess1 :=
                  fun _ _ => (FMap.mem_set _ _ _ _).mpr (Or.inl hd)
                split_ifs <;> simp_all
              case pre =>
                hoare_auto
                intro m1 hm1 a _
                subst hm1
                refine ⟨?_, fun _ _ h => h⟩
                rw [if_pos (by simp [FMap.dom, FMap.empty])]
                exact (FMap.mem_set _ _ _ _).mpr (Or.inr rfl)
            · hoare_skip
              exact fun _ h => ⟨h, fun _ _ hd => ⟨hd, h⟩⟩
          case first_E =>
            phoare_call (: §m1 = mess1 ==>
                FMap.rng (FMap.rem §RO.m mess1) (oget ((§RO.m).get mess1)))
            · -- EC's `fel 2 Bounder.bounder (fun _, mu1 sampleto witness) bound …`
              phoare_proc
              phoare_inline*
              fel §Bounder.bounder (fun _ => sampleto.1 {default}) bound
                (FMap.rng (FMap.rem §RO.m mess1) (oget ((§RO.m).get mess1)))
                [§Bounder.bounder < bound]
                (FMap.dom §RO.m mess1)
              case sum => exact le_rfl
              case init =>
                -- `F.sample(m1)` on the empty `RO.m`: `mess1` in it, nothing else
                hoare_auto
                intro m1 hm1 a _
                subst hm1
                have he : (!decide (FMap.dom (FMap.empty : FMap «from» «to») m1)) = true := by
                  simp [FMap.dom, FMap.empty]
                split_ifs
                refine ⟨(FMap.mem_set _ _ _ _).mpr (Or.inr rfl), ?_, rfl⟩
                rintro ⟨k, hk⟩
                by_cases hk1 : k = m1
                · subst hk1; simp [FMap.rem] at hk
                · simp [FMap.rem, FMap.set, FMap.empty, Finmap.lookup_erase_ne hk1,
                    Finmap.lookup_insert_of_ne _ hk1] at hk
              case step =>
                phoare_proc
                phoare_inline*
                ec_auto
                ec_intro
                rintro ⟨hd, hr, _⟩
                simp only [indicatorE_of_not hr]
                split_ifs with _ _ hx
                · -- a fresh key `x ≠ mess1`: the new value hits `RO.m.[mess1]`
                  -- (EC's `rnd (pred1 _)`)
                  have hx' :
                      ¬ FMap.dom m1 x1 := by
                    simpa using hx
                  have hne : mess1 ≠ x1 := fun h => hx' (h ▸ hd)
                  rnd_pred1 (oget (m1.get mess1))
                  · refine indicatorE_le_of_imp fun hs =>
                      (FMap.eq_of_rng_rem_set (x := x1) hr ?_).symm
                    rwa [FMap.get_set_neqE _ _ _ _ hne] at hs
                  · exact le_of_eq (sampleto_fu _ _)
                all_goals first
                  | exact bot_le
                  | (rnd_null; rfl)
              case incr =>
                intro c
                hoare_proc
                hoare_inline*
                ec_auto
                ec_intro
                rintro ⟨hd, hr, hb, hc⟩
                have hdom : ∀ x a, FMap.dom (FMap.set m1 x a) mess1 :=
                  fun _ _ => (FMap.mem_set _ _ _ _).mpr (Or.inl hd)
                split_ifs <;> simp_all
              case same =>
                intro c
                hoare_proc
                hoare_inline*
                ec_auto
              case keep =>
                hoare_proc
                hoare_inline*
                ec_auto
                ec_intro
                rintro ⟨hd, hr⟩
                have key : ∀ (x : «from») (a : «to»), ¬ FMap.dom m1 x →
                    FMap.dom (FMap.set m1 x a) mess1 ∧
                    FMap.rng (FMap.rem (FMap.set m1 x a) mess1)
                      (oget ((FMap.set m1 x a).get mess1)) := fun x a hx =>
                  ⟨(FMap.mem_set _ _ _ _).mpr (Or.inl hd), by
                    rw [FMap.get_set_neqE _ _ _ _ (fun (h : mess1 = x) => hx (h ▸ hd))]
                    exact FMap.rng_rem_set_of_rng hx hr a⟩
                split_ifs <;> simp_all
            · phoare_skip
              exact fun _ h => le_of_eq (if_pos h)
          case second_notE =>
            phoare_inline*
            phoare_auto
            intro ROm m1 c m2 ⟨hr, hd, hm⟩
            subst hm
            split_ifs with h1 h2 h3 h4 h5
            · exact absurd hd (by simpa using h2)
            · exact absurd hd (by simpa using h2)
            · -- a fresh `m2`: its value hits `RO.m.[m1]` (EC's `rnd (pred1 _)`); the first query's
              -- sample is not used (`m1` is in `RO.m`)
              rnd_bound
              rnd_pred1 (oget (ROm.get m1))
              · refine indicatorE_le_of_imp fun hP => ?_
                simp only [decide_eq_true_eq, FMap.get_set_sameE, oget] at hP
                exact hP.1
              · exact le_of_eq (sampleto_fu _ _)
            · -- `m2` already in `RO.m`, not `m1`: its value is not `RO.m.[m1]`
              -- (`¬ rng (rem RO.m m1) _`)
              rnd_bound
              rnd_null
              refine indicatorE_of_not ?_
              simp only [decide_eq_true_eq]
              rintro ⟨he, hne⟩
              apply hr
              have hd2 : FMap.dom ROm m2 := by simpa using h5
              obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd2)
              refine ⟨m2, ?_⟩
              have h1 : (FMap.rem ROm m1).get m2 = ROm.get m2 := by
                rw [FMap.remE, if_neg (Ne.symm hne)]
              simp only [FMap.get] at h1 hw he ⊢
              rw [h1, hw, he, hw]
              rfl
            · (rnd_null; rfl)
            · exact bot_le
          case bound =>
            -- EC's arithmetic: `∑_{i < bound} μ + μ = (bound + 1) · μ`
            intro _ _
            have := bound_gt0
            show _ ≤ ENNReal.ofReal _
            rw [ofReal_intCast_mul_mu1, sum_Ico_const,
              show (bound + 1).toNat = bound.toNat + 1 by omega]
            push_cast; ring_nf; exact le_rfl
        · have hb := bound_gt0
          exact mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ bound + 1))
            ENNReal.toReal_nonneg

end SecondPreimageSection

/-! ## The section `Collision` -/

-- EC's `op collision`, generic as EC's (`Lib/EC/FMap.lean`)
open FMap (collision)

open Classical in
module Collision using (A : AdvCollision, F : RO_T) {
  proc main () : Bool {
    var b : Bool, m1 : «from», m2 : «from», hash1 : «to», hash2 : «to»;
    _ <- call Bounder(F).init ();
    m1, m2 <- call A(Bounder(F)).guess ();
    if (decide (increase_counter $Counter.c $m1 < bound_counter)) {
      Counter.c <- increase_counter $Counter.c $m1;
      hash1 <- call F.get ($m1);
      if (decide (increase_counter $Counter.c $m2 < bound_counter)) {
        Counter.c <- increase_counter $Counter.c $m2;
        hash2 <- call F.get ($m2);
        b <- decide ($hash1 = $hash2 ∧ $m1 ≠ $m2);
      } else {
        b <- false;
      }
    } else {
      b <- false;
    }
    return $b
  };
}

/-! ### The section `Collision`, with `declare module A <: AdvCollision {-RO, -FRO, -Bounder}` (its
local modules in the namespace `Collision`) -/

namespace Collision

module FEL using (A : AdvCollision, F : RO_T) {
  proc main () : («from» × «from») {
    var m1 : «from», m2 : «from»;
    _ <- call Bounder(F).init ();
    m1, m2 <- call A(Bounder(F)).guess ();
    return ($m1, $m2)
  };
}

open Classical in
module Collision2 using (A : AdvCollision, F : RO_T) {
  proc main () : Bool {
    var b : Bool, m1 : «from», m2 : «from», hash1 : «to», hash2 : «to»;
    m1, m2 <- call FEL(A, F).main ();
    if (decide (increase_counter $Counter.c $m1 < bound_counter)) {
      Counter.c <- increase_counter $Counter.c $m1;
      hash1 <- call F.get ($m1);
      if (decide (increase_counter $Counter.c $m2 < bound_counter)) {
        Counter.c <- increase_counter $Counter.c $m2;
        hash2 <- call F.get ($m2);
        b <- decide ($hash1 = $hash2 ∧ $m1 ≠ $m2);
      } else {
        b <- false;
      }
    } else {
      b <- false;
    }
    return $b
  };
}

end Collision

section CollisionSection

declare module A <: AdvCollision {-RO, -FRO, -Bounder}

/-- EC's `RO_is_collision_resistant &m`, its proof EC's: the `have->:` by `byequiv` (a `calc`
step), then `byphoare`, `proc`, `seq 1`, its first `E`
goal EC's `call(: true ==> collision RO.m)` with EC's `fel`, and the arithmetic of EC's last
`smt()` in the `bound` goal. -/
theorem RO_is_collision_resistant [Countable «from»] (m : VariableAssignment) :
    Pr[ Collision(A, RO).main () @ &m : §res ]
      ≤ ((bound * (bound - 1) + 2 : ℤ) : ℝ) / 2 * mu1 sampleto default := by
  have hb := bound_gt0
  calc Pr[ Collision(A, RO).main () @ &m : §res ]
      = Pr[ Collision.Collision2(A, RO).main () @ &m : §res ] := by
        byequiv; equiv_proc; stmt_inline*; sim
    _ ≤ ((bound * (bound - 1) + 2 : ℤ) : ℝ) / 2 * mu1 sampleto default := by
        byphoare
        · phoare_proc
          phoare_seq 1 : (collision §RO.m)
            (∑ i ∈ Finset.Ico (0 : ℤ) bound, (i.toNat : ENNReal) * sampleto.1 {default}) 1 1
            (sampleto.1 {default}) True
          case invariant =>
            hoare_call
            hoare_skip
            intros; trivial
          case first_E =>
            phoare_call (: True ==> collision §RO.m)
            · -- EC's `fel 1 Bounder.bounder (fun i, i%r * mu1 sampleto witness) bound (collision
              -- RO.m) …`
              phoare_proc
              phoare_inline*
              fel §Bounder.bounder (fun i => (i.toNat : ENNReal) * sampleto.1 {default}) bound
                (collision §RO.m) [§Bounder.bounder < bound]
                  (((FMap.fdom §RO.m).card : ℤ) ≤ §Bounder.bounder)
              case sum => exact le_rfl
              case init =>
                hoare_auto
                intros
                simpa [FMap.fdom, FMap.empty] using FMap.collision_empty (α := «from») (β := «to»)
              case step =>
                phoare_proc
                phoare_inline*
                ec_auto
                ec_intro
                rintro ⟨hi, hc, _⟩
                simp only [indicatorE_of_not hc]
                split_ifs with _ _ hx
                · -- a fresh key: a collision only if its value is already in `RO.m` (EC's `mu_mem`)
                  have hx' : ¬ FMap.dom m1 x1 := by
                    simpa using hx
                  refine (mu_le fun a => indicatorE_le_of_imp
                    (FMap.rng_of_collision_set hx' hc)).trans ?_
                  refine (FMap.mu_rng_le sampleto_fu _).trans ?_
                  gcongr
                  have :
                      (FMap.fdom m1).card ≤
                        bounder.toNat := by
                    omega
                  exact_mod_cast this
                all_goals first
                  | exact bot_le
                  | (rnd_null; rfl)
              case incr =>
                intro c
                hoare_proc
                hoare_inline*
                ec_auto
                ec_intro
                rintro ⟨hi, hc, hb, hcc⟩
                have hcard : ∀ x a, ¬ FMap.dom m1 x →
                    ((FMap.fdom (FMap.set m1 x a)).card : ℤ) ≤
                      bounder + 1 := fun x a hx => by
                  rw [FMap.fcard_set hx]; push_cast; omega
                have hi1 :
                    ((FMap.fdom m1).card : ℤ) ≤ bounder + 1
                      := by
                  omega
                split_ifs <;> simp_all
              case same =>
                intro c
                hoare_proc
                hoare_inline*
                ec_auto
              case keep =>
                hoare_proc
                hoare_inline*
                ec_auto
                ec_intro
                rintro ⟨hi, hc⟩
                have hcard : ∀ x a, ¬ FMap.dom m1 x →
                    ((FMap.fdom (FMap.set m1 x a)).card : ℤ) ≤
                      bounder + 1 := fun x a hx => by
                  rw [FMap.fcard_set hx]; push_cast; omega
                have hcoll : ∀ x a, ¬ FMap.dom m1 x →
                    collision (FMap.set m1 x a) :=
                  fun x a hx => FMap.collision_set hx hc a
                have hi1 :
                    ((FMap.fdom m1).card : ℤ) ≤ bounder + 1
                      := by
                  omega
                split_ifs <;> simp_all
            · phoare_skip
              intros
              exact le_rfl
          case second_notE =>
            phoare_inline*
            phoare_auto
            intro ROm c m1 m2 hnc
            have hfu := sampleto_fu
            split_ifs with h1 h2 h3 h4 h5
            · -- `m1` fresh, sampled `a`; by cases on `m2` (EC's `case: (m2 \in RO.m)`, `m1 = m2`)
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
                      oget] at hP
                    exact hP.1.symm
                · exact le_of_eq (hfu _ _)
              · -- `m2` fresh too: its value hits `a` (EC's `rnd (pred1 r)`)
                rnd_bound
                split_ifs with hc
                · rnd_pred1 a
                  · refine indicatorE_le_of_imp fun hP => ?_
                    simp only [decide_eq_true_eq, FMap.get_set_sameE, oget] at hP
                    exact hP.1
                  · exact le_of_eq (hfu _ _)
                · exact absurd (by simpa using hc) fun h => ((FMap.mem_set _ _ _ _).mp h).elim hk2 hk1
            · (rnd_null; rfl)
            · -- `m1` in `RO.m` (its sample unused), `m2` fresh: `m2`'s value hits `RO.m.[m1]`
              rnd_bound
              rnd_pred1 (oget (ROm.get m1))
              · refine indicatorE_le_of_imp fun hP => ?_
                simp only [decide_eq_true_eq, FMap.get_set_sameE, oget] at hP
                exact hP.1
              · exact le_of_eq (hfu _ _)
            · -- both in `RO.m`: equal values would be a collision already
              rnd_bound
              rnd_null
              refine indicatorE_of_not ?_
              simp only [decide_eq_true_eq]
              rintro ⟨he, hne⟩
              apply hnc
              have hd1 : FMap.dom ROm m1 := by simpa using h2
              have hd2 : FMap.dom ROm m2 := by simpa using h5
              obtain ⟨v1, hv1⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd1)
              obtain ⟨v2, hv2⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd2)
              refine ⟨_, _, hne, hd1, hd2, ?_⟩
              rw [hv1, hv2] at he ⊢
              simp only [oget, Option.getD_some] at he
              rw [he]
            · (rnd_null; rfl)
            · exact bot_le
          case bound =>
            -- EC's arithmetic: `∑_{i < bound} i · μ + μ = (bound (bound - 1) + 2) / 2 · μ`
            intros
            simp only [mul_one, one_mul]
            have hμ := mu_ne_top sampleto default
            obtain ⟨n, hn'⟩ : ∃ n : ℕ, bound = n := ⟨bound.toNat, (Int.toNat_of_nonneg hb.le).symm⟩
            have hn : 1 ≤ n := by omega
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
              have := Finset.sum_range_id_mul_two n
              have h' : ((∑ i ∈ Finset.range n, i : ℕ) : ℝ) * 2 = (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
                exact_mod_cast this
              rw [Nat.cast_sum, Nat.cast_sub hn, Nat.cast_one] at h'
              exact h'
            have hs : (∑ i ∈ Finset.range n, (i : ℝ)) = n * (n - 1) / 2 := by linarith [hsum]
            push_cast
            rw [hs]
            ring
        · have h0 : (0 : ℤ) ≤ bound * (bound - 1) + 2 := by nlinarith
          exact mul_nonneg (div_nonneg (by exact_mod_cast h0) (by norm_num))
            ENNReal.toReal_nonneg

end CollisionSection

end GaudisCrypt.SHA3.Pilot.SecureRO
