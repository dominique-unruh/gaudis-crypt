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
  card_fdom_set not_collision_empty expected_rng_le expected_mono' expected_const_le'
  expected_point' indicatorE_le_of_imp dom_set_iff get_set_ne)

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

section CollisionSection

declare module A <: AdvCollision «from» «to» {-RO, -FRO, -Bounder}





/-- The first `have` of EC's proof of `RO_is_collision_resistant`:
`Collision(A, RO).main ~ Collision2(A, RO).main : ={glob} ==> ={res}`, by EC's
`byequiv; proc; inline*; sim`. -/
theorem Collision_Collision2 (A : AdvCollision «from» «to») :
    equiv[ Collision(A, RO).main ~ Collision.Collision2(A, RO).main :
      ={allGlobals} ==> ={res} ] := by
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

/-- EC's `fel` premises for the oracle `Bounder(RO).get` in `RO_is_collision_resistant`, over
`(Bounder.bounder, RO.m)`: the event `collision RO.m`, the step `Bounder.bounder · μ1 sampleto _`,
the invariant `card (fdom RO.m) <= Bounder.bounder`. -/
theorem Bounder_RO_get_fel_coll :
    FelOracle (Lens.pair Bounder.bounder RO.m) (fun s => s.1)
      (fun i => (i.toNat : ENNReal) * sampleto.1 {default}) bound (fun s => collision s.2)
      (fun s => ((FMap.fdom s.2).card : ℤ) ≤ s.1) (fun s => s.1 < bound)
      Bounder(RO).get.procedure where
  lt := fun _ _ _ hp => hp
  step := by
    phoare_proc_to_stmt
    repeat phoare_inline 0
    phoare_wp 20
    phoare_skip
    rintro τ ⟨hi, hc, _⟩
    simp only [indicatorE_of_not hc]
    split_ifs with _ _ hx
    · -- a fresh key: a collision only if its value is already in `RO.m` (EC's `mu_mem`)
      have hx' : ¬ FMap.dom (RO.m.get τ.globals) ((localVarLens "x" «from»).get τ) := by
        simpa using hx
      refine (expected_mono' fun a => indicatorE_le_of_imp
        (rng_of_collision_set hx' hc)).trans ?_
      refine (expected_rng_le (sampleto_fu (self := inferInstance)) _).trans ?_
      gcongr
      have : (FMap.fdom (RO.m.get τ.globals)).card ≤ (Bounder.bounder.get τ.globals).toNat := by
        omega
      exact_mod_cast this
    all_goals first
      | exact bot_le
      | exact (le_of_eq (SubProbability.expected_eq_zero_of_support fun _ _ => rfl)).trans bot_le
  incr := fun c => by
    hoare_proc_to_stmt
    repeat hoare_inline 0
    hoare_wp 20
    hoare_skip
    rintro τ ⟨hi, hc, hb, hcc⟩
    simp only [Lens.pair, eval_lens_global] at hi hc hb hcc
    have hcard : ∀ x a, ¬ FMap.dom (RO.m.get τ.globals) x →
        ((FMap.fdom (FMap.set (RO.m.get τ.globals) x a)).card : ℤ) ≤
          Bounder.bounder.get τ.globals + 1 := fun x a hx => by
      rw [card_fdom_set hx]; push_cast; omega
    have hi1 : ((FMap.fdom (RO.m.get τ.globals)).card : ℤ) ≤ Bounder.bounder.get τ.globals + 1 := by
      omega
    split_ifs <;> simp_all
  same := fun c => by
    hoare_proc_to_stmt
    repeat hoare_inline 0
    hoare_wp 20
    hoare_skip
    rintro τ ⟨hi, hc, hb, hcc⟩
    simp only [Lens.pair, eval_lens_global] at hi hc hb hcc
    split_ifs <;> simp_all
    omega
  keep := by
    hoare_proc_to_stmt
    repeat hoare_inline 0
    hoare_wp 20
    hoare_skip
    rintro τ ⟨hi, hc⟩
    simp only [Lens.pair, eval_lens_global] at hi hc
    have hcard : ∀ x a, ¬ FMap.dom (RO.m.get τ.globals) x →
        ((FMap.fdom (FMap.set (RO.m.get τ.globals) x a)).card : ℤ) ≤
          Bounder.bounder.get τ.globals + 1 := fun x a hx => by
      rw [card_fdom_set hx]; push_cast; omega
    have hcoll : ∀ x a, ¬ FMap.dom (RO.m.get τ.globals) x →
        collision (FMap.set (RO.m.get τ.globals) x a) :=
      fun x a hx => collision_set_of_not_dom hx hc a
    have hi1 : ((FMap.fdom (RO.m.get τ.globals)).card : ℤ) ≤ Bounder.bounder.get τ.globals + 1 := by
      omega
    split_ifs <;> simp_all


/-- EC's `fel 1 Bounder.bounder (fun i, i%r * mu1 sampleto witness) bound (collision RO.m)
[Bounder(RO).get: …] (card (fdom RO.m) <= Bounder.bounder <= bound)`. -/
theorem FEL_coll [Countable «from»] :
    phoare[ Collision.FEL(A, RO).main : True ==> collision §RO.m ]
      ≤ (∑ i ∈ Finset.Ico (0 : ℤ) bound, (i.toNat : ENNReal) * sampleto.1 {default}) := by
  have hA := Module.Declared.ecModule A (Oracle.ext «from» «to»)
  have hL : FVP.fvP A ≤ ((Lens.pair Bounder.bounder RO.m).footprint)ᶜ := by
    rw [Footprint.lens_pair]
    fp_disjoint
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  rename_i σ _
  erw [Stmt.ewp_call]
  simp_reads
  refine le_trans (Module.fel (L := Lens.pair Bounder.bounder RO.m) (cntr := fun s => s.1)
    (step := fun i => (i.toNat : ENNReal) * sampleto.1 {default}) (q := bound)
    (bad := fun s => collision s.2) (inv := fun s => ((FMap.fdom s.2).card : ℤ) ≤ s.1)
    A (Oracle.ext «from» «to») hA.representable hL
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable «from»)
      | succ m => nomatch m)
    _ (fun _ s => s.1 < bound)
    (fun n => by cases n with
      | zero =>
        simp only [Oracle.ext, HoleSigs.Instantiation.lookup_zero_single]
        exact Bounder_RO_get_fel_coll
      | succ m => nomatch m) _ _ ?_ ?_) ?_
  · simp [Lens.pair, Lens.set_get, Lens.get_of_disjoint_set, FMap.fdom, FMap.empty]
  · simpa [Lens.pair, Lens.set_get, Lens.get_of_disjoint_set] using
      not_collision_empty (α := «from») (β := «to»)
  · simp [Lens.pair, Lens.get_of_disjoint_set, Lens.set_get]

/-- EC's `byphoare=> //; proc; seq 1 : (collision RO.m)
((bound * (bound - 1))%r / 2%r * mu1 sampleto witness) 1%r 1%r (mu1 sampleto witness) (…)`.
(Our `seq` counts the `reset_vars` `proc` adds.) -/
theorem Collision2_le [Countable «from»] :
    phoare[ Collision.Collision2(A, RO).main : True ==> §res ]
      ≤ ((∑ i ∈ Finset.Ico (0 : ℤ) bound, (i.toNat : ENNReal) * sampleto.1 {default}) +
          sampleto.1 {default}) := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_seq 2 : (collision §RO.m)
    (∑ i ∈ Finset.Ico (0 : ℤ) bound, (i.toNat : ENNReal) * sampleto.1 {default}) 1 1
    (sampleto.1 {default}) True
  case invariant =>
    hoare_call
    hoare_wp 1
    hoare_skip
    intros; trivial
  case first_E =>
    phoare_call (FEL_coll A)
    phoare_wp 1
    phoare_skip
    intros
    exact le_rfl
  case second_notE =>
    repeat phoare_inline 0
    phoare_wp 40
    phoare_skip
    intro σ hnc
    have hfu := sampleto_fu (self := inferInstance)
    split_ifs with h1 h2 h3 h4 h5
    · -- `m1` fresh, sampled `a`; by cases on `m2` (EC's `case: (m2 \in RO.m)`, `m1 = m2`)
      have hd1 : ¬ FMap.dom (RO.m.get σ.globals) ((localVarLens "m1" «from»).get σ) := by
        simpa using h2
      by_cases hk1 : (localVarLens "m2" «from»).get σ = (localVarLens "m1" «from»).get σ
      · -- `m2 = m1`: the event wants them distinct
        refine (expected_mono' fun a => ?_).trans
          (expected_const_le' sampleto (sampleto.1 {default}))
        refine (le_of_eq (SubProbability.expected_eq_zero_of_support fun b _ => ?_)).trans bot_le
        split_ifs <;> exact indicatorE_of_not (by simp [hk1])
      by_cases hk2 : FMap.dom (RO.m.get σ.globals) ((localVarLens "m2" «from»).get σ)
      · -- `m2` already in `RO.m`: `m1`'s value hits it (EC's `rnd (pred1 (oget RO.m.[m2]))`)
        refine (expected_mono' (g := fun a => indicatorE
          (oget ((RO.m.get σ.globals).get ((localVarLens "m2" «from»).get σ)) = a))
          fun a => ?_).trans ((expected_point' _).trans (le_of_eq (hfu _ _)))
        refine (expected_mono' fun b => ?_).trans (expected_const_le' _ _)
        split_ifs with hc
        · exact absurd (dom_set_iff.mpr (Or.inr hk2)) (by simpa using hc)
        · refine indicatorE_le_of_imp fun hP => ?_
          simp only [decide_eq_true_eq, FMap.get_set_sameE, get_set_ne _ _ hk1, oget] at hP
          exact hP.1.symm
      · -- `m2` fresh too: its value hits `a` (EC's `rnd (pred1 r)`)
        refine (expected_mono' fun a => ?_).trans
          (expected_const_le' sampleto (sampleto.1 {default}))
        refine (expected_mono' (g := fun b => indicatorE (a = b)) fun b => ?_).trans
          ((expected_point' a).trans (le_of_eq (hfu _ _)))
        split_ifs with hc
        · refine indicatorE_le_of_imp fun hP => ?_
          simp only [decide_eq_true_eq, FMap.get_set_sameE, oget] at hP
          exact hP.1
        · exact absurd (by simpa using hc) fun h => (dom_set_iff.mp h).elim hk1 hk2
    · exact (le_of_eq (SubProbability.expected_eq_zero_of_support fun _ _ => rfl)).trans bot_le
    · -- `m1` in `RO.m` (its sample unused), `m2` fresh: `m2`'s value hits `RO.m.[m1]`
      refine (expected_mono' fun _ => ?_).trans (expected_const_le' sampleto (sampleto.1 {default}))
      refine (expected_mono' fun b => indicatorE_le_of_imp fun hP => ?_).trans
        ((expected_point'
          (oget ((RO.m.get σ.globals).get ((localVarLens "m1" «from»).get σ)))).trans
          (le_of_eq (hfu _ _)))
      simp only [decide_eq_true_eq, FMap.get_set_sameE, oget] at hP
      exact hP.1
    · -- both in `RO.m`: equal values would be a collision already
      refine (expected_mono' fun _ => ?_).trans (expected_const_le' sampleto (sampleto.1 {default}))
      refine (le_of_eq (SubProbability.expected_eq_zero_of_support fun _ _ =>
        indicatorE_of_not ?_)).trans bot_le
      simp only [decide_eq_true_eq]
      rintro ⟨he, hne⟩
      apply hnc
      have hd1 : FMap.dom (RO.m.get σ.globals) ((localVarLens "m1" «from»).get σ) := by
        simpa using h2
      have hd2 : FMap.dom (RO.m.get σ.globals) ((localVarLens "m2" «from»).get σ) := by
        simpa using h5
      obtain ⟨v1, hv1⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd1)
      obtain ⟨v2, hv2⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd2)
      refine ⟨_, _, hne, hd1, hd2, ?_⟩
      rw [hv1, hv2] at he ⊢
      simp only [oget, Option.getD_some] at he
      rw [he]
    · exact (le_of_eq (SubProbability.expected_eq_zero_of_support fun _ _ => rfl)).trans bot_le
    · exact bot_le
  case bound =>
    intros
    simp

/-- `∑_{i ∈ [0, n)} f i` over `ℤ` (EC's `range 0 n`) and over `ℕ`. -/
private theorem sum_Ico_int_toNat (n : ℕ) (f : ℕ → ENNReal) :
    ∑ i ∈ Finset.Ico (0 : ℤ) n, f i.toNat = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, Nat.cast_succ,
      ← Finset.insert_Ico_right_eq_Ico_add_one (Int.natCast_nonneg k),
      Finset.sum_insert (by simp), add_comm, Int.toNat_natCast]

/-- EC's `RO_is_collision_resistant &m`. -/
theorem RO_is_collision_resistant [Countable «from»] (m : VariableAssignment) :
    Pr[ Collision(A, RO).main () @ &m : §res ]
      ≤ ((bound * (bound - 1) + 2 : ℤ) : ℝ) / 2 * mu1 sampleto default := by
  have hb := bound_gt0 (self := inferInstance)
  calc Pr[ Collision(A, RO).main () @ &m : §res ]
      = Pr[ Collision.Collision2(A, RO).main () @ &m : §res ] := by
        byequiv (Collision_Collision2 A)
    _ ≤ ((bound * (bound - 1) + 2 : ℤ) : ℝ) / 2 * mu1 sampleto default := by
        byphoare (Collision2_le A)
        -- EC's arithmetic: `∑_{i < bound} i · μ + μ = (bound (bound - 1) + 2) / 2 · μ`
        · have hμ := mu_ne_top sampleto default
          obtain ⟨n, hn'⟩ : ∃ n : ℕ, bound = n := ⟨bound.toNat, (Int.toNat_of_nonneg hb.le).symm⟩
          have hn : 1 ≤ n := by omega
          rw [hn', sum_Ico_int_toNat n (fun i => (i : ENNReal) * sampleto.1 {default})]
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
