import GaudisCrypt.Examples.SHA3.Pilot.SecureRO
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ModuleFootprint

/-!
# Random oracles are second-preimage resistant — the EC-fidelity pilot, continued
(EasyCrypt `proof/SecureRO.eca`, section `SecondPreimage`)

Split from `Pilot/SecureRO.lean` while it is ported (one file in EC).
-/

namespace GaudisCrypt.SHA3.Pilot.SecureRO

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM

variable {«from» «to» : Type} [DecidableEq «from»] [Inhabited «from»] [Inhabited «to»]
  [Params «from» «to»]

/-! ## The section `SecondPreimage` -/

open GaudisCrypt.SHA3.SecureRO (get_rem_ne rng_rem_set_of_rng eq_of_rng_rem_set expected_const_le'
  dom_set_iff get_set_ne expected_mono' expected_point' indicatorE_le_of_imp)

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

namespace SecondPreimage

set_option maxHeartbeats 1600000 in -- disjointness of named variables, as for `fvP_D1`
/-- The third and fifth `have`s of EC's proof of `RO_is_second_preimage_resistant`:
`SecondPreimage2(A,F).main ~ SecondPreimage3(A,F).main : ={arg, glob} ==> ={res}` for `F` = `LRO`
(EC's `inline*; wp 8 -2; sim`) and `F` = `RO` (EC's `inline*; wp -2 11; sim`, symmetrically): the
states differ only in `SecondPreimage2.m2` and `D1.m1`, which the adversary and the oracle do not
touch (`prhlProc_self_equal_outside`). -/
theorem SecondPreimage2_SecondPreimage3
    (F : RO_T)
    (hinit : F.init = RO.LRO.init) (hgetF : F.get = RO.LRO.get)
    (hsample : FVP.fvP F.sample ≤ (SecondPreimage2.m2.footprint ⊔ D1.m1.footprint)ᶜ := by
      fp_disjoint) :
    equiv[ SecondPreimage2(A, F).main ~ SecondPreimage3(A, F).main :
      ={m1, allGlobals} ==> ={res} ] := by
  equiv_proc_to_stmt
  stmt_inline 0
  repeat (first | stmt_inline{1} 0 | stmt_inline{2} 0 | simp only [hinit, hgetF])
  have hfpL : (Lens.pair SecondPreimage2.m2 D1.m1).footprint =
      SecondPreimage2.m2.footprint ⊔ D1.m1.footprint := Footprint.lens_pair _ _
  have hSP2 : ∀ v g, SecondPreimage2.m2.set v g =
      (Lens.pair SecondPreimage2.m2 D1.m1).set (v, D1.m1.get g) g := fun v g => by
    simp only [Lens.pair, D1.m1.get_set]
  have hD1 : ∀ v g, D1.m1.set v g =
      (Lens.pair SecondPreimage2.m2 D1.m1).set (SecondPreimage2.m2.get g, v) g := fun v g => by
    simp only [Lens.pair]
    rw [← Lens.get_of_disjoint_set' SecondPreimage2.m2 D1.m1 v g, SecondPreimage2.m2.get_set]
  have hSP2get : ∀ g, SecondPreimage2.m2.get g = ((Lens.pair SecondPreimage2.m2 D1.m1).get g).1 :=
    fun g => rfl
  have hCL : Lens.Disjoint Counter.c (Lens.pair SecondPreimage2.m2 D1.m1) := inferInstance
  have hBL : Lens.Disjoint Bounder.bounder (Lens.pair SecondPreimage2.m2 D1.m1) := inferInstance
  have hRL : Lens.Disjoint RO.m (Lens.pair SecondPreimage2.m2 D1.m1) := inferInstance
  generalize Lens.pair SecondPreimage2.m2 D1.m1 = L at hfpL hSP2 hD1 hSP2get hCL hBL hRL ⊢
  have hget := prhlProc_self_equal_outside_module L
    RO.LRO.get
    (by rw [hfpL]; fp_disjoint) (fun x y => x.1 = y.1)
  have hA := prhlProc_self_equal_outside_module L
    A(Bounder(RO.LRO)).guess
    (by rw [hfpL]; fp_disjoint) (fun _ _ => True)
  have hsamp := prhlProc_self_equal_outside_module L F.sample
    (by rw [hfpL]; exact hsample) (fun _ _ => True)
  stmt_wp
  equiv_seq 2 2 : (§m1{1} = §m10{2} ∧ §m2{1} = §m2{2} ∧
      L.equal_outside §allGlobals{1} §allGlobals{2})
  · equiv_seq 1 1 : (§m10{1} = §m11{2} ∧ §m1{1} = §m10{2} ∧
        L.equal_outside §allGlobals{1} §allGlobals{2})
    · equiv_seq 1 1 : (§m10{1} = §m11{2} ∧ §m1{1} = §m10{2} ∧
          L.equal_outside §allGlobals{1} §allGlobals{2})
      · stmt_wp
        equiv_skip
        rintro g₁ g₂ a₁ a₂ ⟨rfl, rfl⟩
        refine ⟨rfl, rfl, ?_⟩
        simp only [(inferInstance : Lens.Disjoint Bounder.bounder Counter.c).commute,
          (inferInstance : Lens.Disjoint Bounder.bounder RO.m).commute,
          (inferInstance : Lens.Disjoint Counter.c RO.m).commute,
          RO.m.set_set, Counter.c.set_set, Bounder.bounder.set_set]
        refine ((Lens.equal_outside.set_disjoint ?_ _).set_disjoint _).set_disjoint _
        rw [hSP2, hD1]
        exact ((Lens.equal_outside.refl _).set_right _).set_right _
      · equiv_call hsamp
        equiv_skip
        rintro σ₁ σ₂ ⟨h1, h2, h⟩
        exact ⟨⟨h1, h⟩, fun _ _ _ _ h' => ⟨h1, h2, h'⟩⟩
    · equiv_call hA
      equiv_skip
      rintro g₁ g₂ a₁ b₁ a₂ b₂ ⟨h1, h2, h⟩
      exact ⟨⟨h1, h⟩, fun _ _ _ _ h' => ⟨h2, h'.1, h'.2⟩⟩
  · equiv_seq 1 1 : (§m1{1} = §m10{2} ∧ L.equal_outside §allGlobals{1} §allGlobals{2} ∧
      §SecondPreimage2.m2{1} = §SecondPreimage2.m2{2})
    · stmt_wp
      equiv_skip
      rintro g₁ g₂ a₁ b₁ a₂ b₂ ⟨h1, rfl, h⟩
      refine ⟨h1, ?_, rfl⟩
      rw [hSP2, hSP2]
      exact (h.set_left _).set_right _
    · equiv_if
      case guard =>
        rintro g₁ g₂ a₁ a₂ ⟨rfl, h, -⟩
        rw [h.get_disjoint (X := Counter.c)]
      case «else» => stmt_wp; equiv_skip; intros; trivial
      case «then» =>
        equiv_seq 1 1 : (§m1{1} = §m10{2} ∧ L.equal_outside §allGlobals{1} §allGlobals{2} ∧
          §SecondPreimage2.m2{1} = §SecondPreimage2.m2{2} ∧ §hash1{1} = §hash1{2})
        · equiv_call hget
          stmt_wp
          equiv_skip
          rintro g₁ g₂ a₁ a₂ ⟨⟨rfl, h, hs⟩, -⟩
          rw [h.get_disjoint (X := Counter.c)]
          refine ⟨⟨rfl, h.set_disjoint _, by rw [← hSP2get, ← hSP2get, hs]⟩, ?_⟩
          rintro r₁ g₁' r₂ g₂' ⟨rfl, h', hs'⟩
          exact ⟨rfl, h', by rw [hSP2get, hSP2get, hs'], rfl⟩
        · equiv_if
          case guard =>
            rintro g₁ g₂ a₁ b₁ a₂ b₂ ⟨rfl, h, hs, -⟩
            rw [h.get_disjoint (X := Counter.c), hs]
          case «else» => stmt_wp; equiv_skip; intros; trivial
          case «then» =>
            stmt_wp
            equiv_call hget
            stmt_wp
            equiv_skip
            rintro g₁ g₂ a₁ b₁ a₂ b₂ ⟨⟨rfl, h, hs, rfl⟩, -⟩
            rw [h.get_disjoint (X := Counter.c), hs]
            refine ⟨⟨rfl, h.set_disjoint _, by rw [← hSP2get, ← hSP2get, hs]⟩, ?_⟩
            rintro r₁ g₁' r₂ g₂' ⟨rfl, h', hs'⟩
            rw [hSP2get g₁', hSP2get g₂', hs']

end SecondPreimage

set_option maxHeartbeats 2000000 in -- one declaration: EC's `have`s, its `byphoare`, its `fel`
set_option maxRecDepth 8192 in
open SecondPreimage in
/-- EC's `RO_is_second_preimage_resistant &m (mess1 : from)`, its proof EC's: the chain of
`have->:` (`calc` steps) from `RO` to `LRO`, to `SecondPreimage2`, `SecondPreimage3` and back to
`RO` (the third and fifth by the one lemma `SecondPreimage2_SecondPreimage3`, EC's two `sim`s), then
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
        -- EC's `inline*; sim` (EC's `sim` relates `m2{1}` to `SecondPreimage2.m2{2}`; here the
        -- queries after the adversary are inlined and coupled one by one, `equiv_rnd`)
        byequiv
        equiv_proc_to_stmt
        stmt_inline 0
        repeat stmt_inline{1} 0
        repeat stmt_inline{2} 0
        stmt_inline{1} 1
        stmt_inline{1} 1
        stmt_inline{2} 1
        stmt_inline{2} 1
        stmt_wp
        equiv_seq 1 2 :
          (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧ §allGlobals{1} = §allGlobals{2})
        · equiv_sim
        · have := (inferInstance : Lens.Disjoint Counter.c RO.m).symm
          equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §SecondPreimage2.m2{2} ∧
            §Counter.c{1} = §Counter.c{2} ∧ §RO.m{1} = §RO.m{2})
          · stmt_wp
            equiv_skip
            intros; simp_all
          · equiv_if
            case guard => intros; simp_all
            case «else» => stmt_wp; equiv_skip; intros; trivial
            case «then» =>
              equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §SecondPreimage2.m2{2} ∧
                §Counter.c{1} = §Counter.c{2} ∧ §RO.m{1} = §RO.m{2} ∧
                §hash1{1} = §hash1{2})
              · stmt_wp
                equiv_rnd
                stmt_wp
                equiv_skip
                intros; simp_all
              · equiv_if
                case guard => intros; simp_all
                case «else» => stmt_wp; equiv_skip; intros; trivial
                case «then» =>
                  stmt_wp
                  equiv_rnd
                  stmt_wp
                  equiv_skip
                  intros; simp_all
    _ = Pr[ SecondPreimage3(A, RO.LRO).main (mess1) @ &m : §res ] := by
        byequiv (SecondPreimage.SecondPreimage2_SecondPreimage3 A _ rfl rfl)
    _ = Pr[ SecondPreimage3(A, RO).main (mess1) @ &m : §res ] := by
        -- EC's `proc; call (RO_LRO_D (D1(A)) _); inline*; auto`
        symm
        byequiv
        equiv_proc_to_stmt
        stmt_inline 0
        stmt_inline 0
        stmt_inline 0
        stmt_inline 0
        stmt_wp
        equiv_call (PROM.FullRO.FullEager.RO_LRO_D «from» «to» Unit Bool (fun _ => sampleto) FRO.m
          (fun _ => sampleto_ll) RO.m (D1 A) (by ec_module) (by fp_disjoint))
        stmt_wp
        equiv_skip
        rintro g₁ g₂ a₁ a₂ ⟨rfl, rfl⟩
        exact ⟨rfl, fun _ _ _ _ h => by rw [h.1]⟩
    _ = Pr[ SecondPreimage.SecondPreimage2(A, RO).main (mess1) @ &m : §res ] := by
        symm
        byequiv (SecondPreimage.SecondPreimage2_SecondPreimage3 A _
          (by simp only [RO, RO.LRO, PROM.FullRO.LRO, PROM.FullRO.RO.asRO,
            PROM.FullRO.RO_T.init.mk_simp])
          (by simp only [RO, RO.LRO, PROM.FullRO.LRO, PROM.FullRO.RO.asRO,
            PROM.FullRO.RO_T.get.mk_simp]))
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
              repeat hoare_inline 0
              hoare_call (: FMap.dom §RO.m mess1)
              case oracle =>
                -- `Bounder(RO).get` keeps a key in `RO.m`
                hoare_proc
                repeat hoare_inline 0
                hoare_wp 20
                hoare_skip
                intro τ hd
                have hdom : ∀ x a, FMap.dom (FMap.set (RO.m.get τ.globals) x a) mess1 :=
                  fun _ _ => dom_set_iff.mpr (Or.inr hd)
                split_ifs <;> simp_all
              case pre =>
                hoare_wp 20
                hoare_skip
                intro σ hσ a _
                refine ⟨?_, fun _ _ h => h⟩
                have hx : (localVarLens "m1" «from»).get σ = mess1 := hσ
                rw [if_pos (by simp [FMap.dom, FMap.empty]), hx]
                exact dom_set_iff.mpr (Or.inl rfl)
            · hoare_skip
              exact fun _ h => ⟨h, fun _ _ hd => ⟨hd, h⟩⟩
          case first_E =>
            phoare_call (: §m1 = mess1 ==>
                FMap.rng (FMap.rem §RO.m mess1) (oget ((§RO.m).get mess1)))
            · -- EC's `fel 2 Bounder.bounder (fun _, mu1 sampleto witness) bound …`
              phoare_proc
              repeat phoare_inline 0
              fel §Bounder.bounder (fun _ => sampleto.1 {default}) bound
                (FMap.rng (FMap.rem §RO.m mess1) (oget ((§RO.m).get mess1)))
                [§Bounder.bounder < bound]
                (FMap.dom §RO.m mess1)
              case sum => exact le_rfl
              case init =>
                -- `F.sample(m1)` on the empty `RO.m`: `mess1` in it, nothing else
                hoare_wp 20
                hoare_skip
                intro σ hσ a _
                subst hσ
                have he : (!decide (FMap.dom (FMap.empty : FMap «from» «to»)
                    ((localVarLens "m1" «from»).get σ))) = true := by
                      simp [FMap.dom, FMap.empty]
                split_ifs with hc
                swap
                · exact absurd he hc
                refine ⟨dom_set_iff.mpr (Or.inl rfl), ?_, rfl⟩
                rintro ⟨k, hk⟩
                by_cases hk1 : k = (localVarLens "m1" «from»).get σ
                · subst hk1; simp [FMap.rem] at hk
                · simp [FMap.rem, FMap.set, FMap.empty, Finmap.lookup_erase_ne hk1,
                    Finmap.lookup_insert_of_ne _ hk1] at hk
              case step =>
                phoare_proc
                repeat phoare_inline 0
                phoare_wp 20
                phoare_skip
                rintro τ ⟨hd, hr, _⟩
                simp only [indicatorE_of_not hr]
                split_ifs with _ _ hx
                · -- a fresh key `x ≠ mess1`: the new value hits `RO.m.[mess1]`
                  -- (EC's `rnd (pred1 _)`)
                  have hx' :
                      ¬ FMap.dom (RO.m.get τ.globals) ((localVarLens "x" «from»).get τ) := by
                    simpa using hx
                  have hne : mess1 ≠ (localVarLens "x" «from»).get τ := fun h => hx' (h ▸ hd)
                  refine (expected_mono' fun a => ?_).trans
                    ((expected_point' (oget ((RO.m.get τ.globals).get mess1))).trans
                      (le_of_eq (sampleto_fu  _ _)))
                  refine indicatorE_le_of_imp fun hs =>
                    (eq_of_rng_rem_set (x := (localVarLens "x" «from»).get τ)
                    hr ?_).symm
                  rwa [get_set_ne _ _ hne] at hs
                all_goals first
                  | exact bot_le
                  | exact (le_of_eq (SubProbability.expected_eq_zero_of_support
                      fun _ _ => rfl)).trans bot_le
              case incr =>
                intro c
                hoare_proc
                repeat hoare_inline 0
                hoare_wp 20
                hoare_skip
                rintro τ ⟨hd, hr, hb, hc⟩
                simp only [Lens.pair, eval_lens_global] at hd hr hb hc
                have hdom : ∀ x a, FMap.dom (FMap.set (RO.m.get τ.globals) x a) mess1 :=
                  fun _ _ => dom_set_iff.mpr (Or.inr hd)
                split_ifs <;> simp_all
              case same =>
                intro c
                hoare_proc
                repeat hoare_inline 0
                hoare_wp 20
                hoare_skip
                rintro τ ⟨hd, hr, hb, hc⟩
                simp only [Lens.pair, eval_lens_global] at hd hr hb hc
                split_ifs <;> simp_all
                omega
              case keep =>
                hoare_proc
                repeat hoare_inline 0
                hoare_wp 20
                hoare_skip
                rintro τ ⟨hd, hr⟩
                simp only [Lens.pair, eval_lens_global] at hd hr
                have key : ∀ (x : «from») (a : «to»), ¬ FMap.dom (RO.m.get τ.globals) x →
                    FMap.dom (FMap.set (RO.m.get τ.globals) x a) mess1 ∧
                    FMap.rng (FMap.rem (FMap.set (RO.m.get τ.globals) x a) mess1)
                      (oget ((FMap.set (RO.m.get τ.globals) x a).get mess1)) := fun x a hx =>
                  ⟨dom_set_iff.mpr (Or.inr hd), by
                    rw [get_set_ne _ _ (fun (h : mess1 = x) => hx (h ▸ hd))]
                    exact rng_rem_set_of_rng hx hr a⟩
                split_ifs <;> simp_all
            · phoare_skip
              exact fun _ h => le_of_eq (if_pos h)
          case second_notE =>
            repeat phoare_inline 0
            phoare_wp 40
            phoare_skip
            rintro σ ⟨hr, hd, hm⟩
            have hdm : FMap.dom (RO.m.get σ.globals) ((localVarLens "m1" «from»).get σ) :=
              hm ▸ hd
            split_ifs with h1 h2 h3 h4 h5
            · exact absurd hdm (by simpa using h2)
            · exact absurd hdm (by simpa using h2)
            · -- a fresh `m2`: its value hits `RO.m.[m1]` (EC's `rnd (pred1 _)`); the first query's
              -- sample is not used (`m1` is in `RO.m`)
              refine (expected_mono' fun _ => ?_).trans
                (expected_const_le' sampleto (sampleto.1 {default}))
              refine (expected_mono' fun b => ?_).trans
                ((expected_point' (oget ((RO.m.get σ.globals).get mess1))).trans
                  (le_of_eq (sampleto_fu  _ _)))
              refine indicatorE_le_of_imp fun hP => ?_
              simp only [decide_eq_true_eq, FMap.get_set_sameE, oget] at hP
              rw [← hm]
              exact hP.1
            · -- `m2` already in `RO.m`, not `m1`: its value is not `RO.m.[m1]`
              -- (`¬ rng (rem RO.m m1) _`)
              refine (expected_mono' fun _ => ?_).trans
                (expected_const_le' sampleto (sampleto.1 {default}))
              refine (le_of_eq (SubProbability.expected_eq_zero_of_support fun b _ =>
                indicatorE_of_not ?_)).trans bot_le
              simp only [decide_eq_true_eq]
              rintro ⟨he, hne⟩
              apply hr
              have hd2 :
                  FMap.dom (RO.m.get σ.globals) (SecondPreimage2.m2.get σ.globals) :=
                by simpa using h5
              obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd2)
              refine ⟨SecondPreimage.SecondPreimage2.m2.get σ.globals, ?_⟩
              have hk : SecondPreimage.SecondPreimage2.m2.get σ.globals ≠ mess1 :=
                fun h => hne (hm.trans h.symm)
              have h1 := get_rem_ne (RO.m.get σ.globals) hk
              simp only [FMap.get] at h1 hw he ⊢
              rw [h1, hw, ← hm, he, hw]
              rfl
            · exact (le_of_eq (SubProbability.expected_eq_zero_of_support
                fun _ _ => rfl)).trans bot_le
            · exact bot_le
          case bound =>
            -- EC's arithmetic: `∑_{i < bound} μ + μ = (bound + 1) · μ`
            intros
            have hμ := mu_ne_top sampleto default
            have hb := bound_gt0
            have hn : ((bound.toNat : ℕ) : ℤ) = bound := Int.toNat_of_nonneg hb.le
            simp only [mul_one, one_mul, Finset.sum_const, Int.card_Ico, sub_zero, nsmul_eq_mul]
            refine le_of_eq ?_
            rw [mu1, ENNReal.ofReal_mul (by exact_mod_cast (by omega : (0 : ℤ) ≤ bound + 1)),
              ENNReal.ofReal_toReal hμ,
              show (((bound + 1 : ℤ)) : ℝ) = ((bound.toNat + 1 : ℕ) : ℝ) by
                push_cast
                rw [show ((bound.toNat : ℕ) : ℝ) = (bound : ℝ) by exact_mod_cast hn],
              ENNReal.ofReal_natCast]
            push_cast
            rw [add_mul, one_mul]
        · have hb := bound_gt0
          exact mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ bound + 1))
            ENNReal.toReal_nonneg

end SecondPreimageSection

end GaudisCrypt.SHA3.Pilot.SecureRO
