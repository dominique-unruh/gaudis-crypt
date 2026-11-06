import GaudisCrypt.Examples.SHA3.SecureRO
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Logic.DeclareModule

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

variable [Params «from» «to»]

/-- The clone's `RO`. -/
noncomputable abbrev RO : PROM.FullRO.RO_T «from» «to» :=
  PROM.FullRO.RO.asRO «from» «to» (fun _ => sampleto) RO.m

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

As in the old file (`SecureRO.lean`), EC's `fel` is a supermartingale argument on the potential
`SecureRO.preimagePotential`; the steps are those of the old proofs, without the lens parameters
and their disjointness (instance search on the `global_var`s). -/

open GaudisCrypt.SHA3.SecureRO (preimagePotential preimagePotential_step
  indicatorE_rng_le_preimagePotential not_rng_empty preimage_tail_le)

/-- The oracle premise of EC's `fel`: a query of `Bounder(RO).get` does not increase the potential
of `(Bounder.bounder, Counter.c, RO.m)` in expectation. -/
theorem Bounder_RO_get_preimagePotential (h : «to») :
    phoareProc (fun _ _ => True) Bounder(RO).get.procedure
      (fun _ g => preimagePotential bound (sampleto.1 {h}) h
        ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).get g))
      (· ≤ ·)
      (fun _ g => preimagePotential bound (sampleto.1 {h}) h
        ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).get g)) := by
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  exact preimagePotential_step h bound _ _ _ _ _ _

/-- EC's `fel` in `RO_is_preimage_resistant`, as a supermartingale: `FEL(A, RO).main` ends with the
potential at most `bound · μ1 sampleto h`. -/
theorem FEL_preimagePotential [Countable «from»] (h : «to») :
    phoareProc (fun _ _ => True) Preimage.FEL(A, RO).main.procedure
      (fun _ g => preimagePotential bound (sampleto.1 {h}) h
        ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).get g))
      (· ≤ ·)
      (fun _ _ => ∑ _i ∈ Finset.Ico (0 : ℤ).toNat bound.toNat, sampleto.1 {h}) := by
  have hL : FVP.fvP A ≤ ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).footprint)ᶜ := by
    rw [Footprint.lens_pair, Footprint.lens_pair]
    fp_disjoint
  phoare_proc_to_stmt
  phoare_inline 0
  repeat phoare_inline 0
  intro σ _
  simp only [Stmt.ewp_seq, Stmt.ewp_assign]
  simp_reads
  erw [Stmt.ewp_call]
  simp_reads
  refine le_trans (Module.ewp_app_le (Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)) A
    (Oracle.ext «from» «to») (Module.Declared.ecModule A (Oracle.ext «from» «to»)).representable hL
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable «from»)
      | succ m => nomatch m)
    _ (preimagePotential bound (sampleto.1 {h}) h)
    (fun n a g => by cases n with
      | zero =>
        simp only [Oracle.ext, HoleSigs.Instantiation.lookup_zero_single, Oracle.get.mk_simp]
        exact Bounder_RO_get_preimagePotential h a g trivial
      | succ m => nomatch m) _ _) ?_
  simp only [Lens.pair, Lens.set_get, Lens.get_of_disjoint_set, preimagePotential]
  rw [if_neg (not_rng_empty h), if_pos le_rfl]
  exact le_rfl

/-- EC's `byphoare(: arg = h ==> _); proc; seq 1 : (rng RO.m h) …`: after the adversary, the last
query hits `h` only if `h` was already in the range of `RO.m` (EC's `fel`) or with probability
`μ1 sampleto h`. -/
theorem Preimage2_le [Countable «from»] :
    phoareProc (fun _ _ => True) Preimage.Preimage2(A, RO).main.procedure
      (fun r _ => indicatorE (r = true)) (· ≤ ·)
      (fun h _ => (∑ _i ∈ Finset.Ico (0 : ℤ).toNat bound.toNat, sampleto.1 {h}) +
        sampleto.1 {h}) := by
  have hFEL := FEL_preimagePotential A
  phoare_proc_to_stmt
  phoare_inline 0
  repeat phoare_inline 1
  phoare_ewp
  erw [Stmt.ewp_call]
  simp_reads
  generalize (localVarLens "arg1" «to»).get _ = h
  refine (Procedure.ewp_mono _ _ (G := fun _ g => indicatorE ((RO.m.get g).rng h) +
    sampleto.1 {h}) (fun v g => ?_) _).trans ?_
  · exact preimage_tail_le _ _ _ _
  rw [Procedure.ewp_add]
  refine add_le_add ?_ (Procedure.ewp_const_le _ _ _ _)
  refine (Procedure.ewp_mono _ _ (fun v g => indicatorE_rng_le_preimagePotential bound
    (sampleto.1 {h}) h ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).get g)) _).trans ?_
  exact hFEL h h _ trivial

/-- The first `have` of EC's proof: `Preimage(A, RO).main ~ Preimage2(A, RO).main`, by EC's
`byequiv; proc; inline*; sim` (`Counter.init` is dead: `Bounder.init` runs it again). -/
theorem Preimage_Preimage2 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      Preimage(A, RO).main.procedure Preimage.Preimage2(A, RO).main.procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
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
  -- `have->: Pr[Preimage(A,RO).main(h) @ &m : res] = Pr[Preimage2(A,RO).main(h) @ &m : res]`
  show (Procedure.Pr Preimage(A, RO).main.procedure h m (fun r _ => r = true) : ℝ) ≤ _
  rw [Procedure.Pr_eq_of_prhlProc (Preimage_Preimage2 A)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true)
    (fun r₁ _ r₂ _ hr => by rw [hr]) (a₁ := h) (a₂ := h) (σ₁ := m) (σ₂ := m) ⟨rfl, rfl⟩]
  -- `byphoare`, `seq 1`, `fel`
  have hB := Preimage2_le A h m trivial
  rw [← Procedure.Pr_eq_ewp] at hB
  -- the arithmetic: `∑_{i < bound} μ + μ = (bound + 1) · μ`
  set μ := sampleto.1 {h}
  have hμ : μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((MeasureTheory.measure_mono (Set.subset_univ _)).trans sampleto.2.1)
  simp only [Finset.sum_const, Int.toNat_zero, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul] at hB
  have hR := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hμ, hμ⟩) hB
  rw [ENNReal.coe_toReal, ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hμ) hμ,
    ENNReal.toReal_mul, ENNReal.toReal_natCast] at hR
  refine hR.trans (le_of_eq ?_)
  have hb := bound_gt0 (self := inferInstance)
  rw [show ((bound.toNat : ℕ) : ℝ) = (bound : ℝ) by exact_mod_cast Int.toNat_of_nonneg hb.le]
  unfold mu1
  push_cast
  ring

end Preimage

end GaudisCrypt.SHA3.Pilot.SecureRO
