import GaudisCrypt.Examples.SHA3.SecureRO
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.Fel
import GaudisCrypt.Logic.PHoareSeq

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

variable («from» «to» : Type) [DecidableEq «from»] [Inhabited «from»] [Inhabited «to»]

/-! The module types: their types are explicit. -/

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
noncomputable def Oracle.ext (F : Oracle «from» «to») : (Oracle.holes «from» «to»).Instantiation :=
  (Oracle.get «from» «to» F).procedure

/-- EC's `module type AdvPreimage (F : Oracle) = { proc guess(h : to) : from }`. -/
abbrev AdvPreimage := Oracle «from» «to» →ₘ procmod («to») → «from»

/-- EC's `module type AdvSecondPreimage (F : Oracle) = { proc guess(m : from) : from }`. -/
abbrev AdvSecondPreimage := Oracle «from» «to» →ₘ procmod («from») → «from»

/-- EC's `module type AdvCollision (F : Oracle) = { proc guess() : from * from }`. -/
abbrev AdvCollision := Oracle «from» «to» →ₘ procmod () → («from» × «from»)

/-! EC's subtyping of module types, as coercions.  Each is a `fun` building the smaller module
in place: the coercion then unfolds to that record, which is what the `module` command reads a
callee like `A(Bounder(F))` back from (a named coercion function it would not see through). -/

/-- An `RF` is an `Oracle` (its `get`). -/
noncomputable instance : Coe (RF «from» «to») (Oracle «from» «to») :=
  ⟨fun F => Oracle.mk «from» «to» { get := RF.get «from» «to» F }⟩

/-- The random oracle (`PROM`'s `RO`) is an `RF` (its `init` and `get`). -/
noncomputable instance : Coe (PROM.FullRO.RO_T «from» «to») (RF «from» «to») :=
  ⟨fun F => RF.mk «from» «to» { init := PROM.FullRO.RO_T.init «from» «to» F
                                get := PROM.FullRO.RO_T.get «from» «to» F }⟩

variable {«from» «to»}

/-! `clone import PROM.FullRO as RO with type in_t <- from, type out_t <- to,
op dout _ <- sampleto, …`: its module variable `RO.m`, and its module `RO`. -/

/-- The clone's module variable `RO.m`: `global_var RO.m : FMap from to`, written out so that it
takes the theory's instance — through its `outParam`s, `RO.m` alone then determines its types,
as in EC.  (`global_var` only takes the section variables its type mentions.) -/
@[nolint unusedArguments]
noncomputable def RO.m [Params «from» «to»] : Lens (FMap «from» «to») VariableAssignment :=
  varLens (VariableName.mk "GaudisCrypt.SHA3.Pilot.SecureRO.RO.m" (FMap «from» «to»))

instance [Params «from» «to»] : Lens.IsGlobalVar (RO.m : Lens (FMap «from» «to») VariableAssignment)
    (VariableName.mk "GaudisCrypt.SHA3.Pilot.SecureRO.RO.m" (FMap «from» «to»)) :=
  ⟨rfl, HEq.rfl⟩

/-- The clone's `FRO.m`, written out as `RO.m` is. -/
@[nolint unusedArguments]
noncomputable def FRO.m [Params «from» «to»] :
    Lens (FMap «from» («to» × flag)) VariableAssignment :=
  varLens (VariableName.mk "GaudisCrypt.SHA3.Pilot.SecureRO.FRO.m" (FMap «from» («to» × flag)))

instance [Params «from» «to»] :
    Lens.IsGlobalVar (FRO.m : Lens (FMap «from» («to» × flag)) VariableAssignment)
    (VariableName.mk "GaudisCrypt.SHA3.Pilot.SecureRO.FRO.m" (FMap «from» («to» × flag))) :=
  ⟨rfl, HEq.rfl⟩

variable [Params «from» «to»]

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
noncomputable abbrev RO.asRF : RF «from» «to» := (RO : RF «from» «to»)

global_var Counter.c : ℤ

module Counter {
  proc init () : Unit {
    Counter.c <- 0;
    return ()
  };
}

global_var Bounder.bounder : ℤ

module Bounder using (F : RF «from» «to») : (RF «from» «to») {
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
module Preimage using (A : AdvPreimage «from» «to», F : RF «from» «to») {
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

module FEL using (A : AdvPreimage «from» «to», F : RF «from» «to») {
  proc main (hash : «to») : «from» {
    var m : «from»;
    _ <- call Bounder(F).init ();
    m <- call A(Bounder(F)).guess ($hash);
    return $m
  };
}

open Classical in
module Preimage2 using (A : AdvPreimage «from» «to», F : RF «from» «to») {
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

declare module A <: AdvPreimage «from» «to» {-RO, -Preimage}

/-! ### The proof of `RO_is_preimage_resistant`

EC's `fel` is the library rule `Module.fel` (`Logic/Fel.lean`), its oracle premises
(`Bounder_RO_get_fel`) proven with `hoare_wp`/`phoare_wp`; the generic `FMap` facts are the old
file's. -/

open GaudisCrypt.SHA3.SecureRO (not_rng_empty expected_mono' expected_point' eq_of_rng_set
  rng_set_of_rng indicatorE_le_of_imp)

/-- EC's `fel` premises for the oracle `Bounder(RO).get`, over `(Bounder.bounder, RO.m)`. -/
theorem Bounder_RO_get_fel (h : «to») :
    FelOracle (Lens.pair Bounder.bounder RO.m) (fun s => s.1) (fun _ => sampleto.1 {h}) bound
      (fun s => FMap.rng s.2 h) (fun _ => True) (fun s => s.1 < bound)
      Bounder(RO).get.procedure where
  lt := fun _ _ _ hp => hp
  -- EC: `proc; sp; if; auto; sp; inline*; sp; wp; rnd (pred1 h)`
  step := by
    phoare_proc_to_stmt
    repeat phoare_inline 0
    phoare_wp 20
    phoare_skip
    intro τ ⟨hr, _⟩
    simp only [indicatorE_of_not hr]
    split_ifs
    · -- a fresh entry hits `h` only if the sample is `h`
      refine (expected_mono' fun a => ?_).trans (expected_point' h)
      exact indicatorE_le_of_imp fun hs => (eq_of_rng_set hr hs).symm
    all_goals first
      | exact bot_le
      | exact (le_of_eq (SubProbability.expected_eq_zero_of_support fun _ _ => rfl)).trans bot_le
  incr := fun c => by
    hoare_proc_to_stmt
    repeat hoare_inline 0
    hoare_wp 20
    hoare_skip
    rintro τ ⟨-, hr, hb, hc⟩
    simp only [Lens.pair, eval_lens_global] at hr hb hc
    split_ifs <;> simp_all
  same := fun c => by
    hoare_proc_to_stmt
    repeat hoare_inline 0
    hoare_wp 20
    hoare_skip
    rintro τ ⟨-, hr, hb, hc⟩
    simp only [Lens.pair, eval_lens_global] at hr hb hc
    split_ifs <;> simp_all
    omega
  keep := by
    hoare_proc_to_stmt
    repeat hoare_inline 0
    hoare_wp 20
    hoare_skip
    rintro τ ⟨-, hr⟩
    simp only [Lens.pair, eval_lens_global] at hr
    split_ifs <;> simp_all [rng_set_of_rng]

/-- EC's `fel 1 Bounder.bounder (fun _, mu1 sampleto h) bound (rng RO.m h)
[Bounder(RO).get: …]`: `FEL(A, RO).main` ends with `h` in the range of `RO.m` with probability at
most `bound · μ1 sampleto h` (`Module.fel`, the oracle's premises `Bounder_RO_get_fel`). -/
theorem FEL_rng [Countable «from»] (h : «to») :
    phoare[ Preimage.FEL(A, RO).main : True ==> FMap.rng §RO.m h ]
      ≤ (∑ _i ∈ Finset.Ico (0 : ℤ) bound, sampleto.1 {h}) := by
  have hL : FVP.fvP A ≤ ((Lens.pair Bounder.bounder RO.m).footprint)ᶜ := by
    rw [Footprint.lens_pair]
    fp_disjoint
  phoare_proc_to_stmt
  phoare_inline 0
  repeat phoare_inline 0
  intro σ _
  simp only [Stmt.ewp_seq, Stmt.ewp_assign]
  simp_reads
  erw [Stmt.ewp_call]
  simp_reads
  refine le_trans (Module.fel (L := Lens.pair Bounder.bounder RO.m) (cntr := fun s => s.1)
    (step := fun _ => sampleto.1 {h}) (q := bound) (bad := fun s => FMap.rng s.2 h)
    (inv := fun _ => True) A (Oracle.ext «from» «to»)
    (Module.Declared.ecModule A (Oracle.ext «from» «to»)).representable hL
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable «from»)
      | succ m => nomatch m)
    _ (fun _ s => s.1 < bound)
    (fun n => by cases n with
      | zero =>
        simp only [Oracle.ext, HoleSigs.Instantiation.lookup_zero_single, Oracle.get.mk_simp]
        exact Bounder_RO_get_fel h
      | succ m => nomatch m) _ _ trivial ?_) ?_
  · simpa [Lens.pair, Lens.set_get] using not_rng_empty (α := «from») h
  · simp [Lens.pair, Lens.get_of_disjoint_set, Lens.set_get]

/-- EC's `byphoare(: arg = h ==> _); proc; seq 1 : (rng RO.m h) (bound%r * mu1 sampleto h) 1%r 1%r
(mu1 sampleto h) (hash = h)`: after the adversary (`FEL`), the last query hits `h` only if `h` was
already in the range of `RO.m` (EC's `fel`, `FEL_rng`) or with probability `μ1 sampleto h`.  (Our
`seq` counts the two statements `proc` adds for the argument.) -/
theorem Preimage2_le [Countable «from»] (h : «to») :
    phoare[ Preimage.Preimage2(A, RO).main : §hash = h ==> §res ]
      ≤ ((∑ _i ∈ Finset.Ico (0 : ℤ) bound, sampleto.1 {h}) + sampleto.1 {h}) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_seq 3 : (FMap.rng §RO.m h) (∑ _i ∈ Finset.Ico (0 : ℤ) bound, sampleto.1 {h}) 1 1
    (sampleto.1 {h}) (§hash = h)
  case invariant =>
    hoare_call
    hoare_wp 2
    hoare_skip
    exact fun _ h _ _ => h
  case first_E =>
    phoare_call (FEL_rng A h)
    phoare_wp 2
    phoare_skip
    intros
    exact le_rfl
  case second_notE =>
    phoare_inline 0
    phoare_wp 10
    phoare_skip
    rintro σ ⟨hr, hh⟩
    set x := (localVarLens "m" «from»).get σ
    split_ifs with _ hd
    · -- a fresh entry: EC's `rnd (pred1 h)`
      refine (expected_mono' fun a => ?_).trans (expected_point' h)
      simp only [hh, FMap.get_set_sameE, decide_eq_true_eq]
      exact le_rfl
    · -- an entry already there is not `h` (`¬ rng RO.m h`)
      have hne : (localVarLens "hash" «to»).get σ ≠ oget ((RO.m.get σ.globals).get x) := by
        rw [hh]
        intro he
        apply hr
        have hd' : FMap.dom (RO.m.get σ.globals) x := by simpa using hd
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd')
        refine ⟨x, ?_⟩
        rw [he]
        simp only [FMap.get] at hv ⊢
        rw [hv]
        rfl
      refine (le_of_eq (SubProbability.expected_eq_zero_of_support fun a _ => ?_)).trans bot_le
      exact indicatorE_of_not (by simpa only [decide_eq_true_eq] using hne)
    · exact bot_le
  case bound =>
    intros
    simp

/-- The first `have` of EC's proof: `Preimage(A, RO).main ~ Preimage2(A, RO).main`, by EC's
`byequiv; proc; inline*; sim` (`Counter.init` is dead: `Bounder.init` runs it again). -/
theorem Preimage_Preimage2 :
    equiv[ Preimage(A, RO).main ~ Preimage.Preimage2(A, RO).main :
      ={hash, allGlobals} ==> ={res} ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline{1} 0
  stmt_inline{2} 0
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  equiv_seq 3 4 : (§hash{1} = §hash0{2} ∧ §hash{1} = §hash{2} ∧ §allGlobals{1} = §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ a₁ a₂ ⟨ha, hg⟩
    refine ⟨ha, ha, ?_⟩
    rw [hg, (inferInstance : Lens.Disjoint Bounder.bounder Counter.c).commute, Counter.c.set_set]
  · equiv_seq 2 2 : (§m{1} = §m{2} ∧ §hash{1} = §hash{2} ∧ §allGlobals{1} = §allGlobals{2})
    · equiv_sim
      rintro _ _ _ _ _ ⟨h1, h2, h3⟩
      exact ⟨h1, h3, fun _ _ => h2⟩
    · stmt_wp
      equiv_if
      case «then» => equiv_sim
      case «else» => equiv_sim
      case guard => intros; simp_all

/-- EC's `RO_is_preimage_resistant &m (h : to)`. -/
theorem RO_is_preimage_resistant [Countable «from»] (m : VariableAssignment) (h : «to») :
    Pr[ Preimage(A, RO).main (h) @ &m : §res ] ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto h := by
  calc Pr[ Preimage(A, RO).main (h) @ &m : §res ]
      = Pr[ Preimage.Preimage2(A, RO).main (h) @ &m : §res ] := by
        byequiv (Preimage_Preimage2 A)
    _ ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto h := by
        byphoare (Preimage2_le A h)
        -- EC's arithmetic: `∑_{i < bound} μ + μ = (bound + 1) · μ`
        · have hμ : sampleto.1 {h} ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
            ((MeasureTheory.measure_mono (Set.subset_univ _)).trans sampleto.2.1)
          have hb := bound_gt0 (self := inferInstance)
          have hn : ((bound.toNat : ℕ) : ℤ) = bound := Int.toNat_of_nonneg hb.le
          simp only [Finset.sum_const, Int.card_Ico, sub_zero, nsmul_eq_mul]
          refine le_of_eq ?_
          rw [mu1, ENNReal.ofReal_mul (by exact_mod_cast (by omega : (0 : ℤ) ≤ bound + 1)),
            ENNReal.ofReal_toReal hμ,
            show (((bound + 1 : ℤ)) : ℝ) = ((bound.toNat + 1 : ℕ) : ℝ) by
              push_cast; rw [show ((bound.toNat : ℕ) : ℝ) = (bound : ℝ) by exact_mod_cast hn],
            ENNReal.ofReal_natCast]
          push_cast
          rw [add_mul, one_mul]
        · have hb := bound_gt0 (self := inferInstance)
          exact mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ bound + 1))
            ENNReal.toReal_nonneg

end Preimage

end GaudisCrypt.SHA3.Pilot.SecureRO
