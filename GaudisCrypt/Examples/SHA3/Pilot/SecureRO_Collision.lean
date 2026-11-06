import GaudisCrypt.Examples.SHA3.Pilot.SecureRO

/-!
# Random oracles are collision resistant — the EC-fidelity pilot, continued
(EasyCrypt `proof/SecureRO.eca`, section `Collision`)

Split from `Pilot/SecureRO.lean` while it is ported (one file in EC).
-/

namespace GaudisCrypt.SHA3.Pilot.SecureRO

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM

variable {«from» «to» : Type} [DecidableEq «from»] [Inhabited «from»] [Inhabited «to»]
  [Params «from» «to»]

open GaudisCrypt.SHA3.SecureRO (collision collision_set_of_not_dom rng_of_collision_set
  card_fdom_set not_collision_empty expected_rng_le collisionPotential collisionPotential_step
  expected_point collision_tail_le indicatorE_collision_le_potential expected_mono' keys_set
  dom_set_iff get_set_self get_set_ne)

open Classical in
module Collision using (A : AdvCollision «from» «to», F : PROM.FullRO.RO_T «from» «to») {
  proc main () : Bool {
    var b : Bool, m1 : «from», m2 : «from», hash1 : «to», hash2 : «to»;
    _ <- call (RF.init «from» «to»
      (Module.app (Bounder) (RF.mk «from» «to»
          { init := PROM.FullRO.RO_T.init «from» «to» F,
            get := PROM.FullRO.RO_T.get «from» «to» F }))) ();
    m1, m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF.get «from» «to»
          (Module.app (Bounder) (RF.mk «from» «to»
              { init := PROM.FullRO.RO_T.init «from» «to» F,
                get := PROM.FullRO.RO_T.get «from» «to» F })) })) ();
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

module FEL using (A : AdvCollision «from» «to», F : PROM.FullRO.RO_T «from» «to») {
  proc main () : («from» × «from») {
    var m1 : «from», m2 : «from»;
    _ <- call (RF.init «from» «to»
      (Module.app (Bounder) (RF.mk «from» «to»
          { init := PROM.FullRO.RO_T.init «from» «to» F,
            get := PROM.FullRO.RO_T.get «from» «to» F }))) ();
    m1, m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF.get «from» «to»
          (Module.app (Bounder) (RF.mk «from» «to»
              { init := PROM.FullRO.RO_T.init «from» «to» F,
                get := PROM.FullRO.RO_T.get «from» «to» F })) })) ();
    return ($m1, $m2)
  };
}

open Classical in
module Collision2 using (A : AdvCollision «from» «to», F : PROM.FullRO.RO_T «from» «to») {
  proc main () : Bool {
    var b : Bool, m1 : «from», m2 : «from», hash1 : «to», hash2 : «to»;
    m1, m2 <- call (Module.app (FEL) (Module.pair A F)) ();
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


/-! ### The lemmas of EC's `fel` in `RO_is_collision_resistant` (on `FMap` and the potential)

Not EasyCrypt statements: EC's proof settles these by `smt` (`fcardU`, `mem_set`, `mu_mem`); here
they are lemmas for the potential `collisionPotential`, whose expectation the oracle does not
increase (`collisionPotential_step`, the step of the failure event lemma). -/


/-- The first `have` of EC's proof of `RO_is_collision_resistant`:
`Collision(A, RO).main ~ Collision2(A, RO).main : ={glob} ==> ={res}`, by EC's
`byequiv; proc; inline*; sim`. -/
theorem Collision_Collision2 (A : AdvCollision «from» «to») :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (Module.app (Collision) (Module.pair A RO)).procedure
      (Module.app (Collision.Collision2) (Module.pair A RO)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  equiv_proc
  stmt_inline 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧ §allGlobals{1} = §allGlobals{2})
  · equiv_sim
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

/-- The oracle premise of EC's `fel` in `RO_is_collision_resistant`: a query of `Bounder(RO).get`
does not increase the potential `collisionPotential` of `(Bounder.bounder, Counter.c, RO.m)` in
expectation (`collisionPotential_step`). -/
theorem Bounder_RO_get_potential (hfu : is_funiform sampleto) :
    phoareProc (fun _ _ => True)
      (RF.get «from» «to» (Module.app (Bounder) (RF.mk «from» «to»
          { init := PROM.FullRO.RO_T.init «from» «to» RO,
            get := PROM.FullRO.RO_T.get «from» «to» RO }))).procedure
      (fun _ g => collisionPotential bound (sampleto.1 {default})
        ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).get g))
      (· ≤ ·)
      (fun _ g => collisionPotential bound (sampleto.1 {default})
        ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).get g)) := by
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  exact collisionPotential_step hfu bound _ _ _ _ _ _

/-- EC's `fel` in `RO_is_collision_resistant`, as a supermartingale: `FEL(A, RO).main` (the
initialization, then the adversary) ends with the potential at most its value after the
initialization, `∑_{i < bound} i · μ` (`Module.ewp_app_le`, the oracle by
`Bounder_RO_get_potential`). -/
theorem FEL_potential [Countable «from»]
    (hfu : is_funiform sampleto) (A : AdvCollision «from» «to»)
    (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (hAd : FVP.fvP A ≤ (Bounder.bounder.footprint ⊔ Counter.c.footprint ⊔ RO.m.footprint)ᶜ) :
    phoareProc (fun _ _ => True)
      (Module.app (Collision.FEL) (Module.pair A RO)).procedure
      (fun _ g => collisionPotential bound (sampleto.1 {default})
        ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).get g))
      (· ≤ ·)
      (fun _ _ => ∑ i ∈ Finset.Ico (0 : ℤ).toNat bound.toNat,
        (i : ENNReal) * sampleto.1 {default}) := by
  have hL : FVP.fvP A ≤ ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).footprint)ᶜ := by
    rw [Footprint.lens_pair, Footprint.lens_pair, ← sup_assoc]
    exact hAd
  phoare_proc_to_stmt
  phoare_inline 0
  repeat phoare_inline 0
  intro σ _
  simp only [Stmt.ewp_seq, Stmt.ewp_assign]
  simp_reads
  erw [Stmt.ewp_call]
  simp_reads
  refine le_trans (Module.ewp_app_le (Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)) A
    (Oracle.ext «from» «to») hA.representable hL
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable «from»)
      | succ m => nomatch m)
    _ (collisionPotential bound (sampleto.1 {default}))
    (fun n a g => by cases n with
      | zero =>
        simp only [Oracle.ext, HoleSigs.Instantiation.lookup_zero_single, Oracle.get.mk_simp]
        exact Bounder_RO_get_potential hfu a g trivial
      | succ m => nomatch m) _ _) ?_
  simp only [Lens.pair, Lens.set_get, Lens.get_of_disjoint_set, collisionPotential]
  split_ifs with hc hinv
  · rw [RO.m.set_get] at hc
    exact absurd hc not_collision_empty
  · exact le_rfl
  · exact absurd ⟨le_rfl, by simp [FMap.fdom, FMap.empty]⟩ hinv

/-- EC's `byphoare=> //; proc; seq 1 : (collision RO.m) …` in `RO_is_collision_resistant`: after the
adversary (`FEL`), a collision of the two queries needs a collision already in `RO.m` (bounded by
EC's `fel`, `FEL_potential`) or a fresh sample hitting a fixed value (`μ`, `collision_tail_le`). -/
theorem Collision2_le [Countable «from»]
    (hfu : is_funiform sampleto) (A : AdvCollision «from» «to»)
    (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (hAd : FVP.fvP A ≤ (Bounder.bounder.footprint ⊔ Counter.c.footprint ⊔ RO.m.footprint)ᶜ) :
    phoareProc (fun _ _ => True)
      (Module.app (Collision.Collision2) (Module.pair A RO)).procedure
      (fun r _ => indicatorE (r = true)) (· ≤ ·)
      (fun _ _ => (∑ i ∈ Finset.Ico (0 : ℤ).toNat bound.toNat,
        (i : ENNReal) * sampleto.1 {default}) +
        sampleto.1 {default}) := by
  have hFEL := FEL_potential hfu A hA hAd
  phoare_proc_to_stmt
  phoare_inline 0
  repeat phoare_inline 1
  phoare_ewp
  -- the tail: `[collision RO.m] + μ` (EC's `seq 1 : (collision RO.m) …`)
  refine (Stmt.ewp_mono _ (fun τ => collision_tail_le hfu _ _ _ _ _) _).trans ?_
  rw [Stmt.ewp_add]
  refine add_le_add ?_ (Stmt.ewp_const_le _ _ _)
  -- the adversary: EC's `fel`
  erw [Stmt.ewp_call]
  simp_reads
  refine le_trans (ProgramDenotation.wp_le_wp_of_le _ _ _ (fun r =>
    indicatorE_collision_le_potential bound (sampleto.1 {default})
      ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).get r.2)) _) ?_
  exact hFEL () _ trivial

section CollisionSection

declare module A <: AdvCollision «from» «to» {-RO, -FRO, -Bounder}

/-- EC's `RO_is_collision_resistant &m`. -/
theorem RO_is_collision_resistant [Countable «from»] (m : VariableAssignment) :
    Pr[ Collision(A, RO).main () @ &m : §res ]
      ≤ ((bound * (bound - 1) + 2 : ℤ) : ℝ) / 2 * mu1 sampleto default := by
  have hb := bound_gt0 (self := inferInstance)
  calc Pr[ Collision(A, RO).main () @ &m : §res ]
      = Pr[ Collision.Collision2(A, RO).main () @ &m : §res ] := by
        byequiv (Collision_Collision2 A)
    _ ≤ ((bound * (bound - 1) + 2 : ℤ) : ℝ) / 2 * mu1 sampleto default := by
        byphoare (Collision2_le (sampleto_fu (self := inferInstance)) A
          (Module.Declared.ecModule A (Oracle.ext «from» «to»)) (by fp_disjoint))
        -- EC's arithmetic: `∑_{i < bound} i · μ + μ = (bound (bound - 1) + 2) / 2 · μ`
        · have hμ : sampleto.1 {default} ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
            ((MeasureTheory.measure_mono (Set.subset_univ _)).trans sampleto.2.1)
          have hsum_ne : (∑ i ∈ Finset.Ico (Int.toNat 0) bound.toNat,
              (i : ENNReal) * sampleto.1 {default}) ≠ ⊤ :=
            ENNReal.sum_ne_top.mpr fun i _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top i) hμ
          rw [← ENNReal.ofReal_toReal (ENNReal.add_ne_top.mpr ⟨hsum_ne, hμ⟩)]
          refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
          rw [ENNReal.toReal_add hsum_ne hμ, ENNReal.toReal_sum (fun i _ =>
            ENNReal.mul_ne_top (ENNReal.natCast_ne_top i) hμ)]
          simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, Int.toNat_zero]
          obtain ⟨n, hn'⟩ : ∃ n : ℕ, bound = n := ⟨bound.toNat, (Int.toNat_of_nonneg hb.le).symm⟩
          have hn : 1 ≤ n := by omega
          rw [hn', Int.toNat_natCast, ← Finset.range_eq_Ico, ← Finset.sum_mul, mu1]
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
