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
  card_fdom_set not_collision_empty expected_rng_le expected_mono' indicatorE_le_of_imp dom_set_iff
  get_set_ne)

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

/-- `∑_{i ∈ [0, n)} f i` over `ℤ` (EC's `range 0 n`) and over `ℕ`. -/
private theorem sum_Ico_int_toNat (n : ℕ) (f : ℕ → ENNReal) :
    ∑ i ∈ Finset.Ico (0 : ℤ) n, f i.toNat = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, Nat.cast_succ,
      ← Finset.insert_Ico_right_eq_Ico_add_one (Int.natCast_nonneg k),
      Finset.sum_insert (by simp), add_comm, Int.toNat_natCast]

set_option maxHeartbeats 1000000 in -- one declaration: EC's `have`, its `byphoare`, its `fel`
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
                simpa [FMap.fdom, FMap.empty] using not_collision_empty (α := «from») (β := «to»)
              case step =>
                phoare_proc
                phoare_inline*
                phoare_auto
                rintro τ ⟨hi, hc, _⟩
                simp only [indicatorE_of_not hc]
                split_ifs with _ _ hx
                · -- a fresh key: a collision only if its value is already in `RO.m` (EC's `mu_mem`)
                  have hx' : ¬ FMap.dom (RO.m.get τ.globals) ((localVarLens "x" «from»).get τ) := by
                    simpa using hx
                  refine (expected_mono' fun a => indicatorE_le_of_imp
                    (rng_of_collision_set hx' hc)).trans ?_
                  refine (expected_rng_le sampleto_fu _).trans ?_
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
                rintro τ ⟨hi, hc, hb, hcc⟩
                simp only [Lens.pair, eval_lens_global] at hi hc hb hcc
                have hcard : ∀ x a, ¬ FMap.dom (RO.m.get τ.globals) x →
                    ((FMap.fdom (FMap.set (RO.m.get τ.globals) x a)).card : ℤ) ≤
                      Bounder.bounder.get τ.globals + 1 := fun x a hx => by
                  rw [card_fdom_set hx]; push_cast; omega
                have hi1 :
                    ((FMap.fdom (RO.m.get τ.globals)).card : ℤ) ≤ Bounder.bounder.get τ.globals + 1
                      := by
                  omega
                split_ifs <;> simp_all
              case same =>
                intro c
                hoare_proc
                hoare_inline*
                hoare_auto
                rintro τ ⟨hi, hc, hb, hcc⟩
                simp only [Lens.pair, eval_lens_global] at hi hc hb hcc
                split_ifs <;> simp_all
                omega
              case keep =>
                hoare_proc
                hoare_inline*
                hoare_auto
                rintro τ ⟨hi, hc⟩
                simp only [Lens.pair, eval_lens_global] at hi hc
                have hcard : ∀ x a, ¬ FMap.dom (RO.m.get τ.globals) x →
                    ((FMap.fdom (FMap.set (RO.m.get τ.globals) x a)).card : ℤ) ≤
                      Bounder.bounder.get τ.globals + 1 := fun x a hx => by
                  rw [card_fdom_set hx]; push_cast; omega
                have hcoll : ∀ x a, ¬ FMap.dom (RO.m.get τ.globals) x →
                    collision (FMap.set (RO.m.get τ.globals) x a) :=
                  fun x a hx => collision_set_of_not_dom hx hc a
                have hi1 :
                    ((FMap.fdom (RO.m.get τ.globals)).card : ℤ) ≤ Bounder.bounder.get τ.globals + 1
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
                    exact absurd (dom_set_iff.mpr (Or.inr hk2)) (by simpa using hc)
                  · rnd_bound
                    refine indicatorE_le_of_imp fun hP => ?_
                    simp only [decide_eq_true_eq, FMap.get_set_sameE, get_set_ne _ _ hk1,
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
                · exact absurd (by simpa using hc) fun h => (dom_set_iff.mp h).elim hk1 hk2
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
