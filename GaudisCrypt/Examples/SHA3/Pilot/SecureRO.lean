import GaudisCrypt.Examples.SHA3.SecureRO
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.FelTactic
import GaudisCrypt.Logic.PHoareSeq
import GaudisCrypt.Logic.CallSpec
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Syntax.ModuleVar
import GaudisCrypt.Syntax.ModuleSubtype

/-!
# Random oracles are preimage resistant — the EC-fidelity pilot
(EasyCrypt `proof/SecureRO.eca`, section `Preimage`)

The refactor pilot of `notes/SHA3/Refactor.md`: `Examples/SHA3/SecureRO.lean` transcribed so that
the declarations read as the EasyCrypt ones.  It replaces that file once complete; until then the
two live side by side (the generic `FMap`/potential lemmas are taken from it).

Translation, against the old file:
* the theory's operators and axioms are the class `Params from to`, whose type arguments are
  `outParam`s: the one instance in scope (EC's clone) fixes them, so `bound`, `sampleto`, … are
  written without types, as in EC;
* the module variables are `global_var`s (`Counter.c`, `Bounder.bounder`, the clone's `RO.m`), found
  disjoint by instance search;
* the types are explicit arguments of the module types and implicit ones of the modules, so a
  module is a name and EC's `Preimage(A, RO).main` is a term
  (`Syntax/ModuleApplicationSyntax.lean`);
* EC's subtyping of module types (an `RF` passed where an `Oracle` is expected, the `RO` where an
  `RF` is) is a coercion, which a module path inserts on its arguments (`A(Bounder(F))`).
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

open GaudisCrypt.SHA3.SecureRO (not_rng_empty eq_of_rng_set
  rng_set_of_rng indicatorE_le_of_imp)

/-- EC's `RO_is_preimage_resistant &m (h : to)`, its proof EC's: the `have->:` by `byequiv`
(here a `calc` step), then `byphoare(: arg = h ==> _)`, `proc`, `seq 1`, its first `E` goal
EC's `call(: true ==> rng RO.m h)` with EC's `fel`, and the arithmetic of EC's last `smt()` in
the `bound` goal.  The oracle's bullets are proven with
`hoare_wp`/`phoare_wp`; the generic `FMap` facts are the old file's. -/
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
              simp [not_rng_empty]
            case step =>
              phoare_proc
              phoare_inline*
              phoare_auto
              intro τ ⟨hr, _⟩
              simp only [indicatorE_of_not hr]
              split_ifs
              · rnd_pred1 h
                exact indicatorE_le_of_imp fun hs => (eq_of_rng_set hr hs).symm
              all_goals first
                | exact bot_le
                | (rnd_null; rfl)
            case incr =>
              intro c
              hoare_proc
              hoare_inline*
              hoare_auto
              rintro τ ⟨-, hr, hb, hc⟩
              simp only [Lens.pair, eval_lens_global] at hr hb hc
              split_ifs <;> simp_all
            case same =>
              intro c
              hoare_proc
              hoare_inline*
              hoare_auto
              rintro τ ⟨-, hr, hb, hc⟩
              simp only [Lens.pair, eval_lens_global] at hr hb hc
              split_ifs <;> simp_all
              omega
            case keep =>
              hoare_proc
              hoare_inline*
              hoare_auto
              rintro τ ⟨-, hr⟩
              simp only [Lens.pair, eval_lens_global] at hr
              split_ifs <;> simp_all [rng_set_of_rng]
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
          intros
          have hμ := mu_ne_top sampleto h
          have hb := bound_gt0
          have hn : ((bound.toNat : ℕ) : ℤ) = bound := Int.toNat_of_nonneg hb.le
          simp only [mul_one, one_mul, Finset.sum_const, Int.card_Ico, sub_zero, nsmul_eq_mul]
          refine le_of_eq ?_
          rw [mu1, ENNReal.ofReal_mul (by exact_mod_cast (by omega : (0 : ℤ) ≤ bound + 1)),
            ENNReal.ofReal_toReal hμ,
            show (((bound + 1 : ℤ)) : ℝ) = ((bound.toNat + 1 : ℕ) : ℝ) by
              push_cast; rw [show ((bound.toNat : ℕ) : ℝ) = (bound : ℝ) by exact_mod_cast hn],
            ENNReal.ofReal_natCast]
          push_cast
          rw [add_mul, one_mul]
      · have hb := bound_gt0
        exact mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ bound + 1))
          ENNReal.toReal_nonneg

end Preimage

end GaudisCrypt.SHA3.Pilot.SecureRO
