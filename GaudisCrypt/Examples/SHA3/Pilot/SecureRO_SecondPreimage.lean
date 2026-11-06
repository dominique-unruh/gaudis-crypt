import GaudisCrypt.Examples.SHA3.Pilot.SecureRO

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

open GaudisCrypt.SHA3.SecureRO (get_rem_ne rng_rem_set_of_rng eq_of_rng_rem_set
  secondPreimagePotential secondPreimagePotential_step indicatorE_secondPreimage_le_potential
  expected_le_one_of indicatorE_le_one' secondPreimage_tail_le expected_const_le' keys_set
  dom_set_iff get_set_self get_set_ne expected_mono')

open Classical in
module SecondPreimage using (A : AdvSecondPreimage «from» «to», F : RF «from» «to») {
  proc main (m1 : «from») : Bool {
    var b : Bool, m2 : «from», hash1 : «to», hash2 : «to»;
    _ <- call (RF.init «from» «to»
      (Module.app (Bounder) F)) ();
    m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF.get «from» «to»
          (Module.app (Bounder) F) })) ($m1);
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

module FEL using (A : AdvSecondPreimage «from» «to», F : PROM.FullRO.RO_T «from» «to») {
  proc main (m1 : «from») : «from» {
    var m2 : «from»;
    _ <- call (RF.init «from» «to»
      (Module.app (Bounder) (RF.mk «from» «to»
          { init := PROM.FullRO.RO_T.init «from» «to» F,
            get := PROM.FullRO.RO_T.get «from» «to» F }))) ();
    _ <- call F.sample ($m1);
    m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF.get «from» «to»
          (Module.app (Bounder) (RF.mk «from» «to»
              { init := PROM.FullRO.RO_T.init «from» «to» F,
                get := PROM.FullRO.RO_T.get «from» «to» F })) })) ($m1);
    return $m2
  };
}

/-! The local modules' variables, `global_var`s (no fresh-variable argument, exception E6, is
needed: they are disjoint from the theory's by instance search, and the declared adversary is
restricted against the local modules, as EC's local modules are fresh). -/

set_option linter.overlappingInstances false in
/-- EC's `SecondPreimage2.m2` (as `RO.m`, with the theory's instance, which fixes its type). -/
@[nolint unusedArguments]
noncomputable def SecondPreimage2.m2 [Params «from» «to»] : Lens «from» VariableAssignment :=
  varLens (VariableName.mk "GaudisCrypt.SHA3.Pilot.SecureRO.SecondPreimage.SecondPreimage2.m2" «from»)

set_option linter.overlappingInstances false in
instance [Params «from» «to»] : Lens.IsGlobalVar (SecondPreimage2.m2 : Lens «from» VariableAssignment)
    (VariableName.mk "GaudisCrypt.SHA3.Pilot.SecureRO.SecondPreimage.SecondPreimage2.m2" «from») := ⟨rfl, HEq.rfl⟩

set_option linter.overlappingInstances false in
/-- EC's `D1.m1` (as `RO.m`, with the theory's instance, which fixes its type). -/
@[nolint unusedArguments]
noncomputable def D1.m1 [Params «from» «to»] : Lens «from» VariableAssignment :=
  varLens (VariableName.mk "GaudisCrypt.SHA3.Pilot.SecureRO.SecondPreimage.D1.m1" «from»)

set_option linter.overlappingInstances false in
instance [Params «from» «to»] : Lens.IsGlobalVar (D1.m1 : Lens «from» VariableAssignment)
    (VariableName.mk "GaudisCrypt.SHA3.Pilot.SecureRO.SecondPreimage.D1.m1" «from») := ⟨rfl, HEq.rfl⟩

open Classical in
module SecondPreimage2 using (A : AdvSecondPreimage «from» «to», F : PROM.FullRO.RO_T «from» «to») {
  proc main (m1 : «from») : Bool {
    var b : Bool, hash1 : «to», hash2 : «to»;
    SecondPreimage2.m2 <- call (Module.app (FEL) (Module.pair A F)) ($m1);
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

-- EC's local `D1(A : AdvSecondPreimage, F : RO)`.  Its proof uses `D1(A)` as an
-- `RO_Distinguisher` (`RO_LRO_D (D1(A))`), so its `distinguish` takes that type's `unit`, and `A`
-- is a Lean parameter so that `D1 A` is one (as `IndifRO_is_secure`'s `D2Pre`)
set_option linter.gaudisCrypt.using false in
module D1 (A : AdvSecondPreimage «from» «to») using (F : PROM.FullRO.RO_T «from» «to») {
  proc distinguish (_x : Unit) : Bool {
    var b : Bool;
    b <- call (Module.app (SecondPreimage2) (Module.pair A F)) ($D1.m1);
    return $b
  };
}

-- `A` a Lean parameter, as in `D1`, which it applies to `A`
set_option linter.gaudisCrypt.using false in
module SecondPreimage3 (A : AdvSecondPreimage «from» «to») using (F : PROM.FullRO.RO_T «from» «to») {
  proc main (m1 : «from») : Bool {
    var b : Bool;
    SecondPreimage2.m2 <- (default : «from»);
    D1.m1 <- $m1;
    _ <- call (RF.init «from» «to»
      (Module.app (Bounder) (RF.mk «from» «to»
          { init := PROM.FullRO.RO_T.init «from» «to» F,
            get := PROM.FullRO.RO_T.get «from» «to» F }))) ();
    b <- call (Module.app (D1 A) F) (());
    return $b
  };
}

end SecondPreimage
/-! ### The lemmas of EC's `fel` in `RO_is_second_preimage_resistant` (on `FMap` and the
potential)

Not EasyCrypt statements, as for `RO_is_preimage_resistant`: EC's `smt` facts on `rem`/`set`, the
potential `secondPreimagePotential`, its step, and the tail bound. -/


/-- `LRO` at the module type `RF` (its procedures `init` and `get`), as `RO.asRF`. -/
noncomputable def RO.LRO_asRF : RF «from» «to» :=
  RF.mk «from» «to»
    { init := PROM.FullRO.RO_T.init «from» «to» (RO.LRO)
      get := PROM.FullRO.RO_T.get «from» «to» (RO.LRO) }

/-- The first `have` of EC's proof of `RO_is_second_preimage_resistant`,
`SecondPreimage(A,RO) ~ SecondPreimage(A,LRO)` (`inline*; sim`): at the module type `RF`, `RO` and
`LRO` are the same module (they differ in `sample` only). -/
theorem RO.LRO_asRF_eq :
    RO.LRO_asRF = RO.asRF := by
  simp only [RO.LRO_asRF, RO.asRF, PROM.FullRO.LRO, PROM.FullRO.RO.asRO,
    PROM.FullRO.RO_T.init.mk_simp, PROM.FullRO.RO_T.get.mk_simp]

@[fp_bound] theorem fvP_LRO_init :
    FVP.fvP (PROM.FullRO.RO_T.init «from» «to» (RO.LRO)) ≤
      RO.m.footprint := by
  fp_module RO.m

@[fp_bound] theorem fvP_LRO_get :
    FVP.fvP (PROM.FullRO.RO_T.get «from» «to» (RO.LRO)) ≤
      RO.m.footprint := by
  fp_module RO.m

@[fp_bound] theorem fvP_RO_sample :
    FVP.fvP (PROM.FullRO.RO_T.sample «from» «to» RO) ≤
      RO.m.footprint := by
  fp_module RO.m

@[fp_bound] theorem fvP_LRO_sample :
    FVP.fvP (PROM.FullRO.RO_T.sample «from» «to» (RO.LRO)) ≤
      RO.m.footprint := by
  fp_module RO.m

@[fp_bound] theorem fvP_Bounder :
    FVP.fvP (Bounder) ≤
      Bounder.bounder.footprint ⊔ Counter.c.footprint := by
  fp_module (Lens.pair Bounder.bounder Counter.c)

namespace SecondPreimage


set_option maxHeartbeats 2000000 in
/-- `D1(A)` touches `A`'s variables, `Bounder`'s and `Counter`'s, and its own. -/
theorem fvP_D1
    (A : AdvSecondPreimage «from» «to») :
    FVP.fvP (D1 A) ≤
      FVP.fvP A ⊔ (Lens.pair (Lens.pair Bounder.bounder Counter.c)
        (Lens.pair SecondPreimage2.m2 D1.m1)).footprint := by
  fp_module (Lens.pair (Lens.pair Bounder.bounder Counter.c) (Lens.pair SecondPreimage2.m2 D1.m1))

/-- The second `have` of EC's proof of `RO_is_second_preimage_resistant`:
`SecondPreimage(A,LRO).main ~ SecondPreimage2(A,LRO).main : ={arg, glob} ==> ={res}`, by EC's
`inline*; sim` (EC's `sim` relates `m2{1}` to `SecondPreimage2.m2{2}`; here the queries after the
adversary are inlined and coupled one by one, `equiv_rnd`). -/
theorem SecondPreimage_SecondPreimage2 (A : AdvSecondPreimage «from» «to») :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (Module.app (SecondPreimage) (Module.pair A (RO.LRO_asRF))).procedure
      (Module.app (SecondPreimage2)
        (Module.pair A (RO.LRO))).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_inline{1} 1
  stmt_inline{1} 1
  stmt_inline{2} 1
  stmt_inline{2} 1
  stmt_wp
  equiv_seq 1 2 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧ §allGlobals{1} = §allGlobals{2})
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
          §Counter.c{1} = §Counter.c{2} ∧ §RO.m{1} = §RO.m{2} ∧ §hash1{1} = §hash1{2})
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

set_option maxHeartbeats 1600000 in
/-- The third and fifth `have`s of EC's proof of `RO_is_second_preimage_resistant`:
`SecondPreimage2(A,F).main ~ SecondPreimage3(A,F).main : ={arg, glob} ==> ={res}` for `F` = `LRO`
(EC's `inline*; wp 8 -2; sim`) and `F` = `RO` (EC's `inline*; wp -2 11; sim`, symmetrically): the
states differ only in `SecondPreimage2.m2` and `D1.m1`, which the adversary and the oracle do not
touch (`prhlProc_self_equal_outside`). -/
theorem SecondPreimage2_SecondPreimage3
    (A : AdvSecondPreimage «from» «to»)
    (hAd : FVP.fvP A ≤ (SecondPreimage2.m2.footprint ⊔ D1.m1.footprint)ᶜ)
    (F : PROM.FullRO.RO_T «from» «to»)
    (hinit : PROM.FullRO.RO_T.init «from» «to» F =
      PROM.FullRO.RO_T.init «from» «to» (RO.LRO))
    (hgetF : PROM.FullRO.RO_T.get «from» «to» F =
      PROM.FullRO.RO_T.get «from» «to» (RO.LRO))
    (hsample : FVP.fvP (PROM.FullRO.RO_T.sample «from» «to» F) ≤ RO.m.footprint) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (Module.app (SecondPreimage2) (Module.pair A F)).procedure
      (Module.app (SecondPreimage3 A) F).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  equiv_proc
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
    (PROM.FullRO.RO_T.get «from» «to» (RO.LRO))
    (by rw [hfpL]; fp_disjoint) (fun x y => x.1 = y.1)
  have hA := prhlProc_self_equal_outside_module L
    (Module.app A (Oracle.mk «from» «to»
      { get := RF.get «from» «to»
          (Module.app (Bounder) (RF.mk «from» «to»
              { init := PROM.FullRO.RO_T.init «from» «to» (RO.LRO),
                get := PROM.FullRO.RO_T.get «from» «to» (RO.LRO) })) }))
    (by rw [hfpL]; fp_disjoint) (fun _ _ => True)
  have hsamp := prhlProc_self_equal_outside_module L (PROM.FullRO.RO_T.sample «from» «to» F)
    (hsample.trans (by rw [hfpL]; fp_disjoint)) (fun _ _ => True)
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

/-- The fourth `have` of EC's proof of `RO_is_second_preimage_resistant`:
`SecondPreimage3(A,RO).main ~ SecondPreimage3(A,LRO).main : ={arg, glob} ==> ={res}`, by EC's
`proc; call (RO_LRO_D (D1(A)) _); inline*; auto`. -/
theorem SecondPreimage3_RO_LRO [Countable «from»] [Countable «to»]
    (hll : is_lossless sampleto) (A : AdvSecondPreimage «from» «to»)
    (hD : Module.ECModule (D1 A) (PROM.FullRO.RO_ext «from» «to»))
    (hdisj : FVP.fvP (D1 A) ≤ (RO.m.footprint ⊔ FRO.m.footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (Module.app (SecondPreimage3 A)
        RO).procedure
      (Module.app (SecondPreimage3 A)
        (RO.LRO)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hcall := PROM.FullRO.FullEager.RO_LRO_D «from» «to» Unit Bool (fun _ => sampleto) FRO.m
    (fun _ => hll) RO.m _ hD hdisj
  equiv_proc
  stmt_inline 0
  stmt_inline 0
  stmt_inline 0
  stmt_inline 0
  stmt_wp
  equiv_call hcall
  stmt_wp
  equiv_skip
  rintro g₁ g₂ a₁ a₂ ⟨rfl, rfl⟩
  exact ⟨rfl, fun _ _ _ _ h => h.1⟩

theorem Bounder_RO_get_secondPreimagePotential (hfu : is_funiform sampleto)
    (m1 : «from») :
    phoareProc (fun _ _ => True)
      (RF.get «from» «to» (Module.app (Bounder) (RF.mk «from» «to»
          { init := PROM.FullRO.RO_T.init «from» «to» RO,
            get := PROM.FullRO.RO_T.get «from» «to» RO }))).procedure
      (fun _ g => secondPreimagePotential bound (sampleto.1 {default}) m1
        ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).get g))
      (· ≤ ·)
      (fun _ g => secondPreimagePotential bound (sampleto.1 {default}) m1
        ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).get g)) := by
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  exact secondPreimagePotential_step hfu m1 bound _ _ _ _ _ _

theorem FEL2_potential [Countable «from»]
    (hfu : is_funiform sampleto) (A : AdvSecondPreimage «from» «to»)
    (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (hAd : FVP.fvP A ≤ (Bounder.bounder.footprint ⊔ Counter.c.footprint ⊔ RO.m.footprint)ᶜ)
    (m1 : «from») :
    @phoareProc (procsig («from») -> «from») (fun a _ => a = m1)
      (Module.app (SecondPreimage.FEL) (Module.pair A RO)).procedure
      (fun _ g => secondPreimagePotential bound (sampleto.1 {default}) m1
        ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).get g))
      (· ≤ ·)
      (fun _ _ => ∑ _i ∈ Finset.Ico (0 : ℤ).toNat bound.toNat, sampleto.1 {default}) := by
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  rename_i σ hσ
  have hL : FVP.fvP A ≤ ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).footprint)ᶜ := by
    rw [Footprint.lens_pair, Footprint.lens_pair, ← sup_assoc]
    exact hAd
  refine (expected_mono' fun a => ?_).trans (expected_const_le' _ _)
  rw [if_pos (by simp [FMap.dom, FMap.empty])]
  erw [Stmt.ewp_call]
  simp_reads
  refine le_trans (Module.ewp_app_le (Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)) A
    (Oracle.ext «from» «to») hA.representable hL
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable «from»)
      | succ m => nomatch m)
    _ (secondPreimagePotential bound (sampleto.1 {default}) m1)
    (fun n a g => by cases n with
      | zero =>
        simp only [Oracle.ext, HoleSigs.Instantiation.lookup_zero_single, Oracle.get.mk_simp]
        exact Bounder_RO_get_secondPreimagePotential hfu m1 a g trivial
      | succ m => nomatch m) _ _) ?_
  simp only [Lens.pair, Lens.set_get, Lens.get_of_disjoint_set, hσ]
  have hd : FMap.dom (FMap.set FMap.empty m1 a) m1 := dom_set_iff.mpr (Or.inl rfl)
  have hr : ∀ v, ¬ FMap.rng (FMap.rem (FMap.set (FMap.empty : FMap «from» «to») m1 a) m1) v := by
    rintro v ⟨k, hk⟩
    by_cases hk1 : k = m1
    · subst hk1; simp [FMap.rem] at hk
    · simp [FMap.rem, FMap.set, FMap.empty, Finmap.lookup_erase_ne hk1,
        Finmap.lookup_insert_of_ne _ hk1] at hk
  simp only [secondPreimagePotential, hd, not_true_eq_false, if_false]
  rw [if_neg (hr _), if_pos le_rfl]
  exact le_rfl

theorem SecondPreimage2_le [Countable «from»]
    (hfu : is_funiform sampleto) (A : AdvSecondPreimage «from» «to»)
    (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (hAd : FVP.fvP A ≤ (Bounder.bounder.footprint ⊔ Counter.c.footprint ⊔ RO.m.footprint)ᶜ)
    (m1 : «from») :
    @phoareProc (procsig («from») -> Bool) (fun a _ => a = m1)
      (Module.app (SecondPreimage.SecondPreimage2)
        (Module.pair A RO)).procedure
      (fun r _ => indicatorE (r = true)) (· ≤ ·)
      (fun _ _ => (∑ _i ∈ Finset.Ico (0 : ℤ).toNat bound.toNat, sampleto.1 {default}) +
        sampleto.1 {default}) := by
  have hFEL := FEL2_potential hfu A hA hAd m1
  phoare_proc_to_stmt
  phoare_inline 0
  repeat phoare_inline 1
  phoare_ewp
  rename_i σ hσ
  erw [Stmt.ewp_call]
  simp_reads
  rw [hσ]
  refine (Procedure.ewp_mono _ _ (G := fun _ g => indicatorE (¬ FMap.dom (RO.m.get g) m1 ∨
    FMap.rng (FMap.rem (RO.m.get g) m1) (oget ((RO.m.get g).get m1))) + sampleto.1 {default})
    (fun v g => ?_) _).trans ?_
  · exact secondPreimage_tail_le hfu _ _ _ _ _
  rw [Procedure.ewp_add]
  refine add_le_add ?_ (Procedure.ewp_const_le _ _ _ _)
  refine (Procedure.ewp_mono _ _ (fun v g => indicatorE_secondPreimage_le_potential bound
    (sampleto.1 {default}) m1 ((Lens.pair Bounder.bounder (Lens.pair Counter.c RO.m)).get g))
    _).trans ?_
  exact hFEL _ _ rfl

end SecondPreimage
section SecondPreimageSection

-- EC: `{-Bounder, -RO, -FRO}`; the local modules' variables are fresh in EC, here a restriction
declare module A <: AdvSecondPreimage «from» «to»
  {-Bounder, -RO, -FRO, -SecondPreimage.SecondPreimage2, -SecondPreimage.D1}

/-- EC's `RO_is_second_preimage_resistant &m (mess1 : from)`. -/
theorem RO_is_second_preimage_resistant [Countable «from»] [Countable «to»]
    (m : VariableAssignment) (mess1 : «from») :
    Pr[ SecondPreimage(A, RO).main (mess1) @ &m : §res ]
      ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto default := by
  have hA := Module.Declared.ecModule A (Oracle.ext «from» «to»)
  -- `D1(A)` is an EasyCrypt-like `RO_Distinguisher`, outside `RO` and `FRO`
  have hD1ec : Module.ECModule (SecondPreimage.D1 A) (PROM.FullRO.RO_ext «from» «to») :=
    PROM.FullRO.RO_Distinguisher.ecModule «from» «to» Unit Bool _
      (Footprint.FinitelySupported.mono (SecondPreimage.fvP_D1 A)
        (hA.finitelySupported.sup (by
          simp only [Footprint.lens_pair]
          exact ((Lens.IsGlobalVar.footprint_finitelySupported _).sup
            (Lens.IsGlobalVar.footprint_finitelySupported _)).sup
            ((Lens.IsGlobalVar.footprint_finitelySupported _).sup
              (Lens.IsGlobalVar.footprint_finitelySupported _)))))
  have hD1d : FVP.fvP (SecondPreimage.D1 A) ≤ (RO.m.footprint ⊔ FRO.m.footprint)ᶜ := by
    refine (SecondPreimage.fvP_D1 A).trans ?_
    simp only [Footprint.lens_pair]
    fp_disjoint
  -- EC's chain of `have->`: `RO` to `LRO`, to `SecondPreimage2`, `SecondPreimage3`, back to `RO`
  calc Pr[ SecondPreimage(A, RO).main (mess1) @ &m : §res ]
      = Pr[ SecondPreimage(A, RO.LRO).main (mess1) @ &m : §res ] := by
        -- at the module type `RF`, `RO` and `LRO` are the same module (they differ in `sample`)
        simp only [RO, RO.LRO, PROM.FullRO.LRO, PROM.FullRO.RO.asRO,
          PROM.FullRO.RO_T.init.mk_simp, PROM.FullRO.RO_T.get.mk_simp]
    _ = Pr[ SecondPreimage.SecondPreimage2(A, RO.LRO).main (mess1) @ &m : §res ] := by
        byequiv (SecondPreimage.SecondPreimage_SecondPreimage2 A)
    _ = Pr[ (Module.app (SecondPreimage.SecondPreimage3 A) RO.LRO) (mess1) @ &m : §res ] := by
        byequiv (SecondPreimage.SecondPreimage2_SecondPreimage3 A (by fp_disjoint) _ rfl rfl
          fvP_LRO_sample)
    _ = Pr[ (Module.app (SecondPreimage.SecondPreimage3 A) RO) (mess1) @ &m : §res ] := by
        symm
        byequiv (SecondPreimage.SecondPreimage3_RO_LRO (sampleto_ll (self := inferInstance)) A
          hD1ec hD1d)
    _ = Pr[ SecondPreimage.SecondPreimage2(A, RO).main (mess1) @ &m : §res ] := by
        symm
        byequiv (SecondPreimage.SecondPreimage2_SecondPreimage3 A (by fp_disjoint) _
          (by simp only [RO, RO.LRO, PROM.FullRO.LRO, PROM.FullRO.RO.asRO,
            PROM.FullRO.RO_T.init.mk_simp])
          (by simp only [RO, RO.LRO, PROM.FullRO.LRO, PROM.FullRO.RO.asRO,
            PROM.FullRO.RO_T.get.mk_simp])
          fvP_RO_sample)
    _ ≤ ((bound + 1 : ℤ) : ℝ) * mu1 sampleto default := by
        byphoare (SecondPreimage.SecondPreimage2_le (sampleto_fu (self := inferInstance)) A hA
          (by fp_disjoint) mess1)
        -- EC's arithmetic: `∑_{i < bound} μ + μ = (bound + 1) · μ`
        · have hμ : sampleto.1 {default} ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
            ((MeasureTheory.measure_mono (Set.subset_univ _)).trans sampleto.2.1)
          have hb := bound_gt0 (self := inferInstance)
          have hn : ((bound.toNat : ℕ) : ℤ) = bound := Int.toNat_of_nonneg hb.le
          simp only [Finset.sum_const, Int.toNat_zero, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul]
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

end SecondPreimageSection

end GaudisCrypt.SHA3.Pilot.SecureRO
