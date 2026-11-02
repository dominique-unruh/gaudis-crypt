import GaudisCrypt.Lib.EC.PROM
import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Examples.SHA3.SecureRO

/-!
# Random oracles with failing queries are preimage, second-preimage and collision resistant
(EasyCrypt `proof/SecureORO.eca`)

`SecureRO` for oracles returning `option`s: `Bounder` answers `None` once its `bound` queries are
spent, and the games compare `Some` hashes.

Translation notes (see `notes/SHA3/README.md` and `SecureRO.lean`, whose translation this follows):
* EasyCrypt's module type `RF` and module `RF` share a name; the module type is `RF_T`
  (exception E3).
* `RF(R)` (`proc init = R.init`, `proc sample = R.sample`) and `Bounder(F)` (`proc sample =
  F.sample`) are used as functors, so their aliased procedures call the aliased ones (exception E5).
* The module variables (`Bounder.bounder`, the clone's `RO.m`, `FRO.m`, and the sections' local
  `Preimage2.hash`, `SecondPreimage2.m2`, `D1.m1`) are lens parameters (exception E6 for the local
  ones).
* The proofs are `SecureRO`'s, step for step; the potentials of EC's `fel` and the lemmas on them
  are `SecureRO`'s (their counter component `0`: there is no `Counter` here).
-/

-- the clone `RO` contains the module `RO` (`RO.RO`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.SecureORO

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM
open SecureRO (expected_mono' expected_const_le' preimagePotential secondPreimagePotential
  collisionPotential)

variable («from» «to» : Type) [DecidableEq «from»] [Inhabited «from»] [Inhabited «to»]
variable (sampleto : SubProbability «to»)
variable (bound : ℤ)
variable (increase_counter : ℤ → «from» → ℤ)

/-- EasyCrypt's axioms on the theory's operators (a hypothesis, realized by a clone). -/
structure Axioms : Prop where
  bound_ge0 : 0 ≤ bound
  sampleto_ll : is_lossless sampleto
  sampleto_full : is_full sampleto
  sampleto_fu : is_funiform sampleto
  increase_counter_spec : ∀ c m, c ≤ increase_counter c m

/-! `clone import PROM.FullRO as RO with type in_t <- from, type out_t <- to,
op dout _ <- sampleto, type d_in_t <- unit, type d_out_t <- bool`; its module variables `RO.m`,
`FRO.m` are the lens parameters `RO_m`, `FRO_m`. -/

-- one binder each: a `module` takes a whole binder group when it mentions one of its names
variable (RO_m : Lens (FMap «from» «to») VariableAssignment)
variable (FRO_m : Lens (FMap «from» («to» × flag)) VariableAssignment)

namespace RO
/-- EasyCrypt's module type `RO` of the clone. -/
abbrev RO_T := PROM.FullRO.RO_T «from» «to»
noncomputable abbrev RO := PROM.FullRO.RO.asRO «from» «to» (fun _ => sampleto) RO_m
noncomputable abbrev LRO := PROM.FullRO.LRO «from» «to» (fun _ => sampleto) RO_m
end RO

-- EC's `module type RF` (renamed: exception E3)
moduletype RF_T {
  proc init () -> Unit;
  proc get (x : «from») -> (Option «to»);
  proc sample (x : «from») -> Unit;
}

-- EC's `module RF (R : RO) : RF`; its aliases `proc init = R.init`, `proc sample = R.sample` are
-- wrapped in a call, as `RF` is used as a functor (exception E5)
module RF using (R : RO.RO_T «from» «to») : (RF_T «from» «to») {
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

/-! `Bounder`'s module variable `bounder` is the lens parameter `Bounder_bounder`. -/
variable (Bounder_bounder : Lens ℤ VariableAssignment)

-- `proc sample = F.sample` is wrapped in a call, as `Bounder` is used as a functor (exception E5)
module Bounder using (F : RF_T «from» «to») : (RF_T «from» «to») {
  proc init () : Unit {
    Bounder_bounder <- 0;
    _ <- call F.init ();
    return ()
  };
  proc get (x : «from») : (Option «to») {
    var y : Option «to»;
    y <- (none : Option «to»);
    if (decide ($Bounder_bounder < bound)) {
      Bounder_bounder <- $Bounder_bounder + 1;
      y <- call F.get ($x);
    }
    return $y
  };
  proc sample (x : «from») : Unit {
    _ <- call F.sample ($x);
    return ()
  };
}

/-! The footprints of the theory's modules (EasyCrypt reads them off the code; `fp_disjoint` uses
them). -/

@[fp_bound] theorem fvP_Bounder :
    FVP.fvP (Bounder «from» «to» bound Bounder_bounder) ≤ Bounder_bounder.footprint := by
  fp_module Bounder_bounder

@[fp_bound] theorem fvP_RF : FVP.fvP (RF «from» «to») ≤ ⊥ := by
  fp_module

@[fp_bound] theorem fvP_RO :
    FVP.fvP (RO.RO «from» «to» sampleto RO_m) ≤ RO_m.footprint := by
  fp_module RO_m

@[fp_bound] theorem fvP_LRO :
    FVP.fvP (RO.LRO «from» «to» sampleto RO_m) ≤ RO_m.footprint := by
  fp_module RO_m

-- EasyCrypt's `module type Oracle = { proc get(x : from) : to option {} }`
moduletype Oracle {
  proc get (x : «from») -> (Option «to»);
}

/-- The oracle procedure an adversary with an `Oracle` may call: `F.get` (E2). -/
abbrev Oracle.holes : HoleSigs := .cons (procsig («from») -> (Option «to»)) .empty

/-- `F.get` out of the oracle `F`. -/
noncomputable def Oracle.ext (F : Oracle «from» «to») : (Oracle.holes «from» «to»).Instantiation :=
  (Oracle.get «from» «to» F).procedure

/-- EasyCrypt's `module type AdvPreimage (F : Oracle) = { proc guess(h : to) : from }`. -/
abbrev AdvPreimage := Oracle «from» «to» →ₘ procmod («to») → «from»

open Classical in
module Preimage using (A : AdvPreimage «from» «to», F : RF_T «from» «to») {
  proc main () : Bool {
    var m : «from», hash : «to», hash' : Option «to»;
    hash <$ sampleto;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ();
    m <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to»
          (Module.app (Bounder «from» «to» bound Bounder_bounder) F) })) ($hash);
    hash' <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m);
    return decide ($hash' = some $hash)
  };
}

/-! ### The section `Preimage`, with `declare module A <: AdvPreimage {-RO, -Preimage}` (its local
modules in the namespace `Preimage`) -/

namespace Preimage

module FEL using (A : AdvPreimage «from» «to», F : RF_T «from» «to») {
  proc main (hash : «to») : «from» {
    var m : «from»;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ();
    m <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to»
          (Module.app (Bounder «from» «to» bound Bounder_bounder) F) })) ($hash);
    return $m
  };
}

/-! The local module's variable `Preimage2.hash` is the lens parameter `Preimage2_hash` (E6). -/
variable (Preimage2_hash : Lens «to» VariableAssignment)

open Classical in
module Preimage2 using (A : AdvPreimage «from» «to», F : RF_T «from» «to») {
  proc main () : Bool {
    var m : «from», hash' : Option «to»;
    Preimage2_hash <$ sampleto;
    m <- call (Module.app (FEL «from» «to» bound Bounder_bounder) (Module.pair A F))
      ($Preimage2_hash);
    hash' <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m);
    return decide ($hash' = some $Preimage2_hash)
  };
}

/-- The first `have` of EC's proof of `RO_is_preimage_resistant`:
`Preimage(A, RF(RO)).main ~ Preimage2(A, RF(RO)).main : ={glob} ==> ={res}`, by EC's
`byequiv; proc; inline*; sim`.  The states differ in `Preimage2.hash` only, which holds `hash{1}`
(`prhlProc_self_equal_outside_module`; EC's `sim` relates the two). -/
theorem Preimage_Preimage2 [Lens.Disjoint Bounder_bounder RO_m]
    [Lens.Disjoint Preimage2_hash Bounder_bounder] [Lens.Disjoint Preimage2_hash RO_m]
    (A : AdvPreimage «from» «to») (hAd : FVP.fvP A ≤ (Preimage2_hash.footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (Module.app (Preimage «from» «to» sampleto bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (Module.app (Preimage.Preimage2 «from» «to» sampleto bound Bounder_bounder Preimage2_hash)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have := (inferInstance : Lens.Disjoint Preimage2_hash Bounder_bounder).symm
  have := (inferInstance : Lens.Disjoint Preimage2_hash RO_m).symm
  have hA := fun h : «to» => prhlProc_self_equal_outside_module Preimage2_hash
    (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to»
          (Module.app (Bounder «from» «to» bound Bounder_bounder)
            (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m))) }))
    (by fp_disjoint) (fun _ y => y = h)
  have hget := fun h : «to» => prhlProc_self_equal_outside_module Preimage2_hash
    (RF_T.get «from» «to» (Module.app (Bounder «from» «to» bound Bounder_bounder)
      (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m))))
    (by fp_disjoint) (fun _ y => y = h)
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 2 3 : (§hash{1} = §hash{2} ∧ §hash{1} = §Preimage2_hash{2} ∧
      Preimage2_hash.equal_outside §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_rnd
    stmt_wp
    equiv_skip
    rintro g₁ g₂ rfl a -
    exact (((Lens.equal_outside.refl _).set_right _).set_disjoint _).set_disjoint _
  · equiv_seq 1 2 : (§m{1} = §m0{2} ∧ §hash{1} = §Preimage2_hash{2} ∧
        Preimage2_hash.equal_outside §allGlobals{1} §allGlobals{2})
    · refine prhlStmt_fix_right (fun σ₂ => Preimage2_hash.get σ₂.globals) fun h => ?_
      equiv_call (hA h)
      equiv_skip
      rintro g₁ g₂ h₁ h₂ ⟨⟨rfl, hh, he⟩, rfl⟩
      exact ⟨⟨rfl, he, rfl⟩, fun r₁ g₁' r₂ g₂' ⟨hr, he', hg⟩ => ⟨hr, hh.trans hg.symm, he'⟩⟩
    · refine prhlStmt_fix_right (fun σ₂ => Preimage2_hash.get σ₂.globals) fun h => ?_
      equiv_call (hget h)
      stmt_wp
      equiv_skip
      rintro g₁ g₂ m₁ hash₁ m0₂ ⟨⟨rfl, hh, he⟩, rfl⟩
      exact ⟨⟨rfl, he, rfl⟩, fun r₁ g₁' r₂ g₂' ⟨hr, _, hg⟩ => by rw [hr, hg, hh]⟩


/-- The oracle premise of EC's `fel` in `RO_is_preimage_resistant`: a query of
`Bounder(RF(RO)).get` does not increase the potential `SecureRO.preimagePotential` of
`(Bounder.bounder, RO.m)`, at the hash `Preimage2.hash` (`SecureRO.preimagePotential_step`, whose
counter is `0` here). -/
theorem Bounder_RO_get_preimagePotential [Lens.Disjoint Bounder_bounder RO_m]
    [Lens.Disjoint Preimage2_hash Bounder_bounder] [Lens.Disjoint Preimage2_hash RO_m]
    (hfu : is_funiform sampleto) :
    phoareProc (fun _ _ => True)
      (RF_T.get «from» «to» (Module.app (Bounder «from» «to» bound Bounder_bounder)
        (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (fun _ g => preimagePotential bound (sampleto.1 {default}) (Preimage2_hash.get g)
        (Bounder_bounder.get g, 0, RO_m.get g))
      (· ≤ ·)
      (fun _ g => preimagePotential bound (sampleto.1 {default}) (Preimage2_hash.get g)
        (Bounder_bounder.get g, 0, RO_m.get g)) := by
  have := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
  have := (inferInstance : Lens.Disjoint Preimage2_hash Bounder_bounder).symm
  have := (inferInstance : Lens.Disjoint Preimage2_hash RO_m).symm
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  rename_i σ _
  have h := SecureRO.preimagePotential_step (d := sampleto) (Preimage2_hash.get σ.globals) bound
    (Bounder_bounder.get σ.globals) 0 0 (RO_m.get σ.globals) ((localVarLens "x" «from»).get σ) True
  rw [hfu _ default] at h
  exact h

/-- EC's `fel 1 Bounder.bounder (fun _, mu1 sampleto witness) bound (rng RO.m h) …` in
`RO_is_preimage_resistant`, as a supermartingale: `FEL(A, RF(RO)).main` ends with the potential at
most its value after the initialization, `bound · μ1 sampleto witness` (`Module.ewp_app_le`). -/
theorem FEL_preimagePotential [Countable «from»] [Lens.Disjoint Bounder_bounder RO_m]
    [Lens.Disjoint Preimage2_hash Bounder_bounder] [Lens.Disjoint Preimage2_hash RO_m]
    (hfu : is_funiform sampleto) (A : AdvPreimage «from» «to»)
    (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (hAd : FVP.fvP A ≤ (Bounder_bounder.footprint ⊔ Preimage2_hash.footprint ⊔ RO_m.footprint)ᶜ) :
    phoareProc (fun _ _ => True)
      (Module.app (Preimage.FEL «from» «to» bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (fun _ g => preimagePotential bound (sampleto.1 {default}) (Preimage2_hash.get g)
        (Bounder_bounder.get g, 0, RO_m.get g))
      (· ≤ ·)
      (fun _ _ => ∑ _i ∈ Finset.Ico (0 : ℤ).toNat bound.toNat, sampleto.1 {default}) := by
  have := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
  have := (inferInstance : Lens.Disjoint Preimage2_hash Bounder_bounder).symm
  have := (inferInstance : Lens.Disjoint Preimage2_hash RO_m).symm
  have hL : FVP.fvP A ≤
      ((Lens.pair Bounder_bounder (Lens.pair Preimage2_hash RO_m)).footprint)ᶜ := by
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
  refine le_trans (Module.ewp_app_le (Lens.pair Bounder_bounder (Lens.pair Preimage2_hash RO_m)) A
    (Oracle.ext «from» «to») hA.representable hL
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable «from»)
      | succ m => nomatch m)
    _ (fun s => preimagePotential bound (sampleto.1 {default}) s.2.1 (s.1, 0, s.2.2))
    (fun n a g => by cases n with
      | zero =>
        simp only [Oracle.ext, HoleSigs.Instantiation.lookup_zero_single, Oracle.get.mk_simp]
        exact Bounder_RO_get_preimagePotential «from» «to» sampleto bound RO_m Bounder_bounder
          Preimage2_hash hfu a g trivial
      | succ m => nomatch m) _ _) ?_
  simp only [Lens.pair, Lens.set_get, Lens.get_of_disjoint_set, preimagePotential]
  rw [if_neg (SecureRO.not_rng_empty _), if_pos le_rfl]
  exact le_rfl

/-- EC's `byphoare(: _ ==> _); proc; seq 2 : (rng RO.m Preimage2.hash) …` in
`RO_is_preimage_resistant`: after the adversary (`FEL`), the last query hits `Preimage2.hash` only
if it was already in the range of `RO.m` (EC's `fel`, `FEL_preimagePotential`) or with probability
`μ1 sampleto witness` (`SecureRO.preimage_tail_le`). -/
theorem Preimage2_le [Countable «from»] [Lens.Disjoint Bounder_bounder RO_m]
    [Lens.Disjoint Preimage2_hash Bounder_bounder] [Lens.Disjoint Preimage2_hash RO_m]
    (hfu : is_funiform sampleto) (A : AdvPreimage «from» «to»)
    (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (hAd : FVP.fvP A ≤ (Bounder_bounder.footprint ⊔ Preimage2_hash.footprint ⊔ RO_m.footprint)ᶜ) :
    phoareProc (fun _ _ => True)
      (Module.app (Preimage.Preimage2 «from» «to» sampleto bound Bounder_bounder Preimage2_hash)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (fun r _ => indicatorE (r = true)) (· ≤ ·)
      (fun _ _ => (∑ _i ∈ Finset.Ico (0 : ℤ).toNat bound.toNat, sampleto.1 {default}) +
        sampleto.1 {default}) := by
  have hFEL := FEL_preimagePotential «from» «to» sampleto bound RO_m Bounder_bounder Preimage2_hash
    hfu A hA hAd
  have := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
  have := (inferInstance : Lens.Disjoint Preimage2_hash Bounder_bounder).symm
  have := (inferInstance : Lens.Disjoint Preimage2_hash RO_m).symm
  phoare_proc_to_stmt
  phoare_inline 0
  repeat phoare_inline 1
  phoare_ewp
  refine (expected_mono' fun a => ?_).trans (expected_const_le' _ _)
  -- the tail: `[rng RO.m Preimage2.hash] + μ` (EC's `seq 2 : (rng RO.m Preimage2.hash) …`)
  refine (Stmt.ewp_mono _ (G := fun σ => indicatorE (FMap.rng (RO_m.get σ.globals)
    (Preimage2_hash.get σ.globals)) + sampleto.1 {default}) (fun τ => ?_) _).trans ?_
  · have h := SecureRO.preimage_tail_le (d := sampleto) (RO_m.get τ.globals)
      ((localVarLens "m" «from»).get τ) (Preimage2_hash.get τ.globals)
      (Bounder_bounder.get τ.globals < bound)
    rw [hfu _ default] at h
    refine le_trans (le_of_eq ?_) h
    simp only [Option.some.injEq, eq_comm]
  rw [Stmt.ewp_add]
  refine add_le_add ?_ (Stmt.ewp_const_le _ _ _)
  -- the adversary: EC's `fel`
  erw [Stmt.ewp_call]
  simp_reads
  refine le_trans (ProgramDenotation.wp_le_wp_of_le _ _ _ (fun r =>
    SecureRO.indicatorE_rng_le_preimagePotential bound (sampleto.1 {default})
      (Preimage2_hash.get r.2) (Bounder_bounder.get r.2, 0, RO_m.get r.2)) _) ?_
  exact hFEL _ _ trivial

end Preimage

/-- EC's `RO_is_preimage_resistant &m`, for the section's `A`.  The local module's variable
`Preimage2.hash` is chosen fresh (exception E6), which needs the theory's variables finitely
supported. -/
theorem RO_is_preimage_resistant [Countable «from»] [Lens.Disjoint Bounder_bounder RO_m]
    (hBfs : Bounder_bounder.footprint.FinitelySupported)
    (hROfs : RO_m.footprint.FinitelySupported)
    (hax : Axioms «from» «to» sampleto bound increase_counter)
    (A : AdvPreimage «from» «to») (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (_hAd : FVP.fvP A ≤ (RO_m.footprint ⊔ Bounder_bounder.footprint)ᶜ) (m : VariableAssignment) :
    (Procedure.Pr (Module.app (Preimage «from» «to» sampleto bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
        () m (fun r _ => r = true) : ℝ) ≤
      ((bound + 1 : ℤ) : ℝ) * (sampleto.1 {default}).toReal := by
  -- the local module's variable `Preimage2.hash`, fresh (exception E6)
  obtain ⟨H, hH, -⟩ := Footprint.exists_fresh «to» ((hA.finitelySupported.sup hBfs).sup hROfs)
  have hH' : ∀ {X : Footprint VariableAssignment},
      X ≤ FVP.fvP A ⊔ Bounder_bounder.footprint ⊔ RO_m.footprint → H.footprint ≤ Xᶜ :=
    fun h => hH.trans (Footprint.compl_antimono h)
  haveI : Lens.Disjoint H Bounder_bounder := Lens.disjoint_of_footprint_le_compl _ _ (hH' (by
    repeat (first | exact le_rfl | exact le_sup_right | apply le_sup_of_le_left)))
  haveI : Lens.Disjoint H RO_m := Lens.disjoint_of_footprint_le_compl _ _ (hH' (by
    repeat (first | exact le_rfl | exact le_sup_right | apply le_sup_of_le_left)))
  have hAH : FVP.fvP A ≤ (H.footprint)ᶜ := (Footprint.le_compl_comm _ _).mp (hH' (by
    repeat (first | exact le_rfl | exact le_sup_right | apply le_sup_of_le_left)))
  -- `have->: Pr[Preimage(A,RF(RO)).main() @ &m : res] = Pr[Preimage2(A,RF(RO)).main() @ &m : res]`
  rw [Procedure.Pr_eq_of_prhlProc
    (Preimage.Preimage_Preimage2 «from» «to» sampleto bound RO_m Bounder_bounder H A hAH)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true)
    (fun r₁ _ r₂ _ h => by rw [h]) (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl]
  -- `byphoare`, `seq 2`, `fel`
  have hB := Preimage.Preimage2_le «from» «to» sampleto bound RO_m Bounder_bounder H
    hax.sampleto_fu A hA
    ((Footprint.le_compl_comm _ _).mpr (sup_le (sup_le
      (le_sup_right.trans ((Footprint.le_compl_comm _ _).mp _hAd))
      ((Footprint.le_compl_comm _ _).mp hAH))
      (le_sup_left.trans ((Footprint.le_compl_comm _ _).mp _hAd)))) () m trivial
  rw [← Procedure.Pr_eq_ewp] at hB
  -- the arithmetic: `∑_{i < bound} μ + μ = (bound + 1) · μ`
  set μ := sampleto.1 {default}
  have hμ : μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((MeasureTheory.measure_mono (Set.subset_univ _)).trans sampleto.2.1)
  simp only [Finset.sum_const, Int.toNat_zero, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul] at hB
  have hR := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hμ, hμ⟩) hB
  rw [ENNReal.coe_toReal, ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hμ) hμ,
    ENNReal.toReal_mul, ENNReal.toReal_natCast] at hR
  refine hR.trans (le_of_eq ?_)
  rw [show ((bound.toNat : ℕ) : ℝ) = (bound : ℝ) by
    exact_mod_cast Int.toNat_of_nonneg hax.bound_ge0]
  push_cast
  ring

/-- EasyCrypt's `module type AdvSecondPreimage (F : Oracle) = { proc guess(m : from) : from }`. -/
abbrev AdvSecondPreimage := Oracle «from» «to» →ₘ procmod («from») → «from»

open Classical in
module SecondPreimage using (A : AdvSecondPreimage «from» «to», F : RF_T «from» «to») {
  proc main (m1 : «from») : Bool {
    var m2 : «from», hash1 : Option «to», hash2 : Option «to»;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ();
    m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to»
          (Module.app (Bounder «from» «to» bound Bounder_bounder) F) })) ($m1);
    hash1 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m1);
    hash2 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

/-! ### The section `SecondPreimage`, with `declare module A <: AdvSecondPreimage {-Bounder, -RO,
-FRO}` (its local modules in the namespace `SecondPreimage`) -/

namespace SecondPreimage

module FEL using (A : AdvSecondPreimage «from» «to», F : RF_T «from» «to») {
  proc main (m1 : «from») : «from» {
    var m2 : «from»;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ();
    _ <- call (RF_T.sample «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m1);
    m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to»
          (Module.app (Bounder «from» «to» bound Bounder_bounder) F) })) ($m1);
    return $m2
  };
}

/-! The local modules' variables `SecondPreimage2.m2`, `D1.m1` are the lens parameters
`SecondPreimage2_m2`, `D1_m1` (exception E6). -/
variable (SecondPreimage2_m2 : Lens «from» VariableAssignment)
variable (D1_m1 : Lens «from» VariableAssignment)

open Classical in
module SecondPreimage2 using (A : AdvSecondPreimage «from» «to», F : RF_T «from» «to») {
  proc main (m1 : «from») : Bool {
    var hash1 : Option «to», hash2 : Option «to»;
    SecondPreimage2_m2 <- call (Module.app (FEL «from» «to» bound Bounder_bounder)
      (Module.pair A F)) ($m1);
    hash1 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m1);
    hash2 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($SecondPreimage2_m2);
    return decide ($m1 ≠ $SecondPreimage2_m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

-- EC's local `D1(A : AdvSecondPreimage, F : RO)`.  Its proof uses `D1(A)` as an
-- `RO_Distinguisher` (`RO_LRO_D (D1(A))`), so its `distinguish` takes that type's `unit`, and `A`
-- is a Lean parameter so that `D1 A` is one (as in `SecureRO`)
set_option linter.gaudisCrypt.using false in
module D1 (A : AdvSecondPreimage «from» «to») using (F : RO.RO_T «from» «to») {
  proc distinguish (_x : Unit) : Bool {
    var b : Bool;
    b <- call (Module.app (SecondPreimage2 «from» «to» bound Bounder_bounder SecondPreimage2_m2)
      (Module.pair A (Module.app (RF «from» «to») F))) ($D1_m1);
    return $b
  };
}

-- `A` a Lean parameter, as in `D1`, which it applies to `A`
set_option linter.gaudisCrypt.using false in
module SecondPreimage3 (A : AdvSecondPreimage «from» «to») using (F : RO.RO_T «from» «to») {
  proc main (m1 : «from») : Bool {
    var b : Bool;
    SecondPreimage2_m2 <- (default : «from»);
    D1_m1 <- $m1;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder)
        (Module.app (RF «from» «to») F))) ();
    b <- call (Module.app (D1 «from» «to» bound Bounder_bounder SecondPreimage2_m2 D1_m1 A) F)
      (());
    return $b
  };
}

/-- The first `have` of EC's proof of `RO_is_second_preimage_resistant`,
`SecondPreimage(A, RF(RO)) ~ SecondPreimage(A, RF(LRO))` (`inline*; sim`): the games do not call
`sample`, in which `RO` and `LRO` differ.  EC's `sim` across the adversary, whose oracles differ in
code (`prhlProc_abstract_call_equal_outside_module` at `L = (Bounder.bounder, RO.m)`, `I`
equality). -/
theorem SecondPreimage_RO_LRO [Countable «from»] [Lens.Disjoint Bounder_bounder RO_m]
    (A : AdvSecondPreimage «from» «to») (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (hAd : FVP.fvP A ≤ (Bounder_bounder.footprint ⊔ RO_m.footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (Module.app (SecondPreimage «from» «to» bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (Module.app (SecondPreimage «from» «to» bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.LRO «from» «to» sampleto RO_m)))).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
  have hget : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (RF_T.get «from» «to» (Module.app (Bounder «from» «to» bound Bounder_bounder)
        (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (RF_T.get «from» «to» (Module.app (Bounder «from» «to» bound Bounder_bounder)
        (Module.app (RF «from» «to») (RO.LRO «from» «to» sampleto RO_m)))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
    equiv_proc
    repeat stmt_inline{1} 0
    repeat stmt_inline{2} 0
    stmt_wp
    equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §allGlobals{1} = §allGlobals{2})
    · stmt_wp
      equiv_skip
      intros; simp_all
    · equiv_if
      case guard => intros; simp_all
      case «else» => equiv_skip; intros; simp_all
      case «then» =>
        stmt_wp
        equiv_rnd
        stmt_wp
        equiv_skip
        intros; simp_all
  have hA' := prhlProc_abstract_call_equal_outside_module (Lens.pair Bounder_bounder RO_m) A
    (Oracle.ext «from» «to») hA.representable (by rw [Footprint.lens_pair]; exact hAd) Eq
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable «from»)
      | succ m => nomatch m)
    (Oracle.mk «from» «to» { get := RF_T.get «from» «to» (Module.app (Bounder «from» «to» bound
      Bounder_bounder) (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m))) })
    (Oracle.mk «from» «to» { get := RF_T.get «from» «to» (Module.app (Bounder «from» «to» bound
      Bounder_bounder) (Module.app (RF «from» «to») (RO.LRO «from» «to» sampleto RO_m))) })
    (fun n => by cases n with
      | zero =>
        simp only [Oracle.ext, HoleSigs.Instantiation.lookup_zero_single, Oracle.get.mk_simp,
          Lens.equal_outside_and_get_eq_iff]
        exact hget
      | succ m => nomatch m)
  simp only [Lens.equal_outside_and_get_eq_iff] at hA'
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 2 2 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧ §allGlobals{1} = §allGlobals{2})
  · equiv_call hA'
    stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧ §allGlobals{1} = §allGlobals{2} ∧
        §hash1{1} = §hash1{2})
    · equiv_call hget
      equiv_skip
      intros; simp_all
    · equiv_call hget
      equiv_skip
      intros; simp_all

/-- The second `have` of EC's proof of `RO_is_second_preimage_resistant`:
`SecondPreimage(A, RF(LRO)).main ~ SecondPreimage2(A, RF(LRO)).main : ={arg, glob} ==> ={res}`, by
EC's `inline*; sim` (`LRO.sample` does nothing; EC's `sim` relates `m2{1}` to
`SecondPreimage2.m2{2}`; the queries after the adversary are inlined and coupled, `equiv_rnd`). -/
theorem SecondPreimage_SecondPreimage2 [Lens.Disjoint Bounder_bounder RO_m]
    [Lens.Disjoint SecondPreimage2_m2 Bounder_bounder] [Lens.Disjoint SecondPreimage2_m2 RO_m]
    (A : AdvSecondPreimage «from» «to») :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (Module.app (SecondPreimage «from» «to» bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.LRO «from» «to» sampleto RO_m)))).procedure
      (Module.app (SecondPreimage2 «from» «to» bound Bounder_bounder SecondPreimage2_m2)
        (Module.pair A (Module.app (RF «from» «to») (RO.LRO «from» «to» sampleto RO_m)))).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
  have := (inferInstance : Lens.Disjoint SecondPreimage2_m2 Bounder_bounder).symm
  have := (inferInstance : Lens.Disjoint SecondPreimage2_m2 RO_m).symm
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  repeat stmt_inline{1} 1
  repeat stmt_inline{2} 1
  stmt_wp
  equiv_seq 9 10 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧ §allGlobals{1} = §allGlobals{2})
  · equiv_sim
  · equiv_seq 5 5 : (§m1{1} = §m1{2} ∧ §m2{1} = §SecondPreimage2_m2{2} ∧
        §Bounder_bounder{1} = §Bounder_bounder{2} ∧ §RO_m{1} = §RO_m{2} ∧
        §(localVarLens "y" (Option «to»)){1} = §(localVarLens "y" (Option «to»)){2})
    · equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §SecondPreimage2_m2{2} ∧
          §Bounder_bounder{1} = §Bounder_bounder{2} ∧ §RO_m{1} = §RO_m{2} ∧ §x{1} = §x2{2} ∧
          §y{1} = §y{2})
      · stmt_wp
        equiv_skip
        intros; simp_all
      · equiv_if
        case guard => intros; simp_all
        case «else» => equiv_skip; intros; simp_all
        case «then» =>
          stmt_wp
          equiv_rnd
          stmt_wp
          equiv_skip
          intros; simp_all
    · equiv_seq 1 1 : (§m1{1} = §m1{2} ∧ §m2{1} = §SecondPreimage2_m2{2} ∧
          §Bounder_bounder{1} = §Bounder_bounder{2} ∧ §RO_m{1} = §RO_m{2} ∧ §hash1{1} = §hash1{2} ∧
          §x2{1} = §x5{2} ∧ §y1{1} = §y1{2})
      · stmt_wp
        equiv_skip
        intros; simp_all
      · equiv_if
        case guard => intros; simp_all
        case «else» => equiv_skip; intros; simp_all
        case «then» =>
          stmt_wp
          equiv_rnd
          stmt_wp
          equiv_skip
          intros; simp_all

/-- The third and fifth `have`s of EC's proof of `RO_is_second_preimage_resistant`:
`SecondPreimage2(A, RF(F)).main ~ SecondPreimage3(A, F).main : ={arg, glob} ==> ={res}` for `F` =
`LRO` (EC's `inline*; wp 14 -2; sim`) and `F` = `RO` (EC's `inline*; wp -2 17; sim`): the states
differ only in `SecondPreimage2.m2` and `D1.m1`, which the adversary and the oracle do not touch
(`prhlProc_self_equal_outside_module`). -/
theorem SecondPreimage2_SecondPreimage3 [Lens.Disjoint Bounder_bounder RO_m]
    [Lens.Disjoint SecondPreimage2_m2 Bounder_bounder] [Lens.Disjoint SecondPreimage2_m2 RO_m]
    [Lens.Disjoint SecondPreimage2_m2 D1_m1] [Lens.Disjoint D1_m1 Bounder_bounder]
    [Lens.Disjoint D1_m1 RO_m]
    (A : AdvSecondPreimage «from» «to»)
    (hAd : FVP.fvP A ≤ (SecondPreimage2_m2.footprint ⊔ D1_m1.footprint)ᶜ)
    (F : RO.RO_T «from» «to»)
    (hinit : PROM.FullRO.RO_T.init «from» «to» F =
      PROM.FullRO.RO_T.init «from» «to» (RO.LRO «from» «to» sampleto RO_m))
    (hF : FVP.fvP F ≤ RO_m.footprint) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (Module.app (SecondPreimage2 «from» «to» bound Bounder_bounder SecondPreimage2_m2)
        (Module.pair A (Module.app (RF «from» «to») F))).procedure
      (Module.app (SecondPreimage3 «from» «to» bound Bounder_bounder SecondPreimage2_m2 D1_m1 A)
        F).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  equiv_proc
  stmt_inline 0
  repeat (first | stmt_inline{1} 0 | stmt_inline{2} 0 | simp only [hinit])
  have := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
  have := (inferInstance : Lens.Disjoint SecondPreimage2_m2 Bounder_bounder).symm
  have := (inferInstance : Lens.Disjoint SecondPreimage2_m2 RO_m).symm
  have := (inferInstance : Lens.Disjoint D1_m1 Bounder_bounder).symm
  have := (inferInstance : Lens.Disjoint D1_m1 RO_m).symm
  have hFL : FVP.fvP F ≤ (SecondPreimage2_m2.footprint ⊔ D1_m1.footprint)ᶜ :=
    hF.trans (by fp_disjoint)
  have hfpL : (Lens.pair SecondPreimage2_m2 D1_m1).footprint =
      SecondPreimage2_m2.footprint ⊔ D1_m1.footprint := Footprint.lens_pair _ _
  have hSP2 : ∀ v g, SecondPreimage2_m2.set v g =
      (Lens.pair SecondPreimage2_m2 D1_m1).set (v, D1_m1.get g) g := fun v g => by
    simp only [Lens.pair, D1_m1.get_set]
  have hD1 : ∀ v g, D1_m1.set v g =
      (Lens.pair SecondPreimage2_m2 D1_m1).set (SecondPreimage2_m2.get g, v) g := fun v g => by
    simp only [Lens.pair]
    rw [← Lens.get_of_disjoint_set' SecondPreimage2_m2 D1_m1 v g, SecondPreimage2_m2.get_set]
  have hSP2get : ∀ g, SecondPreimage2_m2.get g = ((Lens.pair SecondPreimage2_m2 D1_m1).get g).1 :=
    fun g => rfl
  have hBL : Lens.Disjoint Bounder_bounder (Lens.pair SecondPreimage2_m2 D1_m1) := inferInstance
  have hRL : Lens.Disjoint RO_m (Lens.pair SecondPreimage2_m2 D1_m1) := inferInstance
  have hget := prhlProc_self_equal_outside_module (Lens.pair SecondPreimage2_m2 D1_m1)
    (RF_T.get «from» «to» (Module.app (Bounder «from» «to» bound Bounder_bounder)
      (Module.app (RF «from» «to») F)))
    (by rw [hfpL]; fp_disjoint) (fun x y => x.1 = y.1)
  have hA := prhlProc_self_equal_outside_module (Lens.pair SecondPreimage2_m2 D1_m1)
    (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to» (Module.app (Bounder «from» «to» bound Bounder_bounder)
          (Module.app (RF «from» «to») F)) }))
    (by rw [hfpL]; fp_disjoint) (fun _ _ => True)
  have hsamp := prhlProc_self_equal_outside_module (Lens.pair SecondPreimage2_m2 D1_m1)
    (PROM.FullRO.RO_T.sample «from» «to» F) (by rw [hfpL]; fp_disjoint) (fun _ _ => True)
  generalize Lens.pair SecondPreimage2_m2 D1_m1 = L at hfpL hSP2 hD1 hSP2get hBL hRL hget hA hsamp ⊢
  stmt_wp
  equiv_seq 3 3 : (§m1{1} = §m10{2} ∧ §m2{1} = §m2{2} ∧
      L.equal_outside §allGlobals{1} §allGlobals{2})
  · equiv_seq 1 1 : (§m10{1} = §m11{2} ∧ §m1{1} = §m10{2} ∧
        L.equal_outside §allGlobals{1} §allGlobals{2})
    · equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §m10{1} = §m11{2} ∧ §m1{1} = §m10{2} ∧
          L.equal_outside §allGlobals{1} §allGlobals{2})
      · stmt_wp
        equiv_skip
        rintro g₁ g₂ a₁ a₂ ⟨rfl, rfl⟩
        refine ⟨rfl, rfl, rfl, ?_⟩
        simp only [(inferInstance : Lens.Disjoint Bounder_bounder RO_m).commute,
          RO_m.set_set, Bounder_bounder.set_set]
        refine (Lens.equal_outside.set_disjoint ?_ _).set_disjoint _
        rw [hSP2, hD1]
        exact ((Lens.equal_outside.refl _).set_right _).set_right _
      · equiv_call hsamp
        equiv_skip
        rintro σ₁ σ₂ ⟨h0, h1, h2, h⟩
        exact ⟨⟨h0, h⟩, fun _ _ _ _ h' => ⟨h1, h2, h'⟩⟩
    · equiv_call hA
      equiv_skip
      rintro g₁ g₂ a₁ b₁ a₂ b₂ ⟨h1, h2, h⟩
      exact ⟨⟨h1, h⟩, fun _ _ _ _ h' => ⟨h2, h'.1, h'.2⟩⟩
  · equiv_seq 2 2 : (§m1{1} = §m10{2} ∧ L.equal_outside §allGlobals{1} §allGlobals{2} ∧
        §SecondPreimage2_m2{1} = §SecondPreimage2_m2{2})
    · stmt_wp
      equiv_skip
      rintro g₁ g₂ a₁ b₁ a₂ b₂ ⟨h1, rfl, h⟩
      refine ⟨h1, ?_, rfl⟩
      rw [hSP2, hSP2]
      exact (h.set_left _).set_right _
    · equiv_seq 1 1 : (§m1{1} = §m10{2} ∧ L.equal_outside §allGlobals{1} §allGlobals{2} ∧
          §SecondPreimage2_m2{1} = §SecondPreimage2_m2{2} ∧ §hash1{1} = §hash1{2})
      · equiv_call hget
        equiv_skip
        rintro g₁ g₂ a₁ a₂ ⟨h1, h, hs⟩
        refine ⟨⟨h1, h, by rw [← hSP2get, ← hSP2get, hs]⟩, ?_⟩
        rintro r₁ g₁' r₂ g₂' ⟨rfl, h', hs'⟩
        exact ⟨h1, h', by rw [hSP2get, hSP2get, hs'], rfl⟩
      · equiv_call hget
        equiv_skip
        rintro g₁ g₂ a₁ b₁ a₂ b₂ ⟨rfl, h, hs, rfl⟩
        refine ⟨⟨hs, h, by rw [← hSP2get, ← hSP2get, hs]⟩, ?_⟩
        rintro r₁ g₁' r₂ g₂' ⟨rfl, h', hs'⟩
        rw [hSP2get g₁', hSP2get g₂', hs']

/-- `D1(A)` touches `A`'s variables, `Bounder`'s, and its own. -/
theorem fvP_D1 [Lens.Disjoint SecondPreimage2_m2 D1_m1]
    [Lens.Disjoint Bounder_bounder SecondPreimage2_m2] [Lens.Disjoint Bounder_bounder D1_m1]
    (A : AdvSecondPreimage «from» «to») :
    FVP.fvP (D1 «from» «to» bound Bounder_bounder SecondPreimage2_m2 D1_m1 A) ≤
      FVP.fvP A ⊔ (Lens.pair Bounder_bounder (Lens.pair SecondPreimage2_m2 D1_m1)).footprint := by
  fp_module (Lens.pair Bounder_bounder (Lens.pair SecondPreimage2_m2 D1_m1))

/-- The fourth `have` of EC's proof of `RO_is_second_preimage_resistant`:
`SecondPreimage3(A, RO).main ~ SecondPreimage3(A, LRO).main : ={arg, glob} ==> ={res}`, by EC's
`proc; call (RO_LRO_D (D1(A)) _); inline*; auto`. -/
theorem SecondPreimage3_RO_LRO [Countable «from»] [Countable «to»] [Lens.Disjoint RO_m FRO_m]
    (hll : is_lossless sampleto) (A : AdvSecondPreimage «from» «to»)
    (hD : Module.ECModule (D1 «from» «to» bound Bounder_bounder SecondPreimage2_m2 D1_m1 A)
      (PROM.FullRO.RO_ext «from» «to»))
    (hdisj : FVP.fvP (D1 «from» «to» bound Bounder_bounder SecondPreimage2_m2 D1_m1 A) ≤
      (RO_m.footprint ⊔ FRO_m.footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (Module.app (SecondPreimage3 «from» «to» bound Bounder_bounder SecondPreimage2_m2 D1_m1 A)
        (RO.RO «from» «to» sampleto RO_m)).procedure
      (Module.app (SecondPreimage3 «from» «to» bound Bounder_bounder SecondPreimage2_m2 D1_m1 A)
        (RO.LRO «from» «to» sampleto RO_m)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hcall := PROM.FullRO.FullEager.RO_LRO_D «from» «to» Unit Bool (fun _ => sampleto) FRO_m
    (fun _ => hll) RO_m _ hD hdisj
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

/-- The oracle premise of EC's `fel 2` in `RO_is_second_preimage_resistant`: a query of
`Bounder(RF(RO)).get` does not increase the potential `SecureRO.secondPreimagePotential` of
`(Bounder.bounder, RO.m)` (`SecureRO.secondPreimagePotential_step`, its counter `0`). -/
theorem Bounder_RO_get_secondPreimagePotential [Lens.Disjoint Bounder_bounder RO_m]
    (hfu : is_funiform sampleto) (m1 : «from») :
    phoareProc (fun _ _ => True)
      (RF_T.get «from» «to» (Module.app (Bounder «from» «to» bound Bounder_bounder)
        (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (fun _ g => secondPreimagePotential bound (sampleto.1 {default}) m1
        (Bounder_bounder.get g, 0, RO_m.get g))
      (· ≤ ·)
      (fun _ g => secondPreimagePotential bound (sampleto.1 {default}) m1
        (Bounder_bounder.get g, 0, RO_m.get g)) := by
  have := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  exact SecureRO.secondPreimagePotential_step hfu m1 bound _ 0 0 _ _ True

/-- EC's `fel 2 Bounder.bounder (fun _, mu1 sampleto witness) bound …` in
`RO_is_second_preimage_resistant`, as a supermartingale: `FEL(A, RF(RO)).main(m1)` (the
initialization, `sample(m1)`, the adversary) ends with the potential at most `bound · μ`. -/
theorem FEL_potential [Countable «from»] [Lens.Disjoint Bounder_bounder RO_m]
    (hfu : is_funiform sampleto) (A : AdvSecondPreimage «from» «to»)
    (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (hAd : FVP.fvP A ≤ (Bounder_bounder.footprint ⊔ RO_m.footprint)ᶜ) (m1 : «from») :
    @phoareProc (procsig («from») -> «from») (fun a _ => a = m1)
      (Module.app (SecondPreimage.FEL «from» «to» bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (fun _ g => secondPreimagePotential bound (sampleto.1 {default}) m1
        (Bounder_bounder.get g, 0, RO_m.get g))
      (· ≤ ·)
      (fun _ _ => ∑ _i ∈ Finset.Ico (0 : ℤ).toNat bound.toNat, sampleto.1 {default}) := by
  have := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
  have hL : FVP.fvP A ≤ ((Lens.pair Bounder_bounder RO_m).footprint)ᶜ := by
    rw [Footprint.lens_pair]
    exact hAd
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  rename_i σ hσ
  refine (expected_mono' fun a => ?_).trans (expected_const_le' _ _)
  rw [if_pos (by simp [FMap.dom, FMap.empty])]
  erw [Stmt.ewp_call]
  simp_reads
  refine le_trans (Module.ewp_app_le (Lens.pair Bounder_bounder RO_m) A
    (Oracle.ext «from» «to») hA.representable hL
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable «from»)
      | succ m => nomatch m)
    _ (fun s => secondPreimagePotential bound (sampleto.1 {default}) m1 (s.1, 0, s.2))
    (fun n a g => by cases n with
      | zero =>
        simp only [Oracle.ext, HoleSigs.Instantiation.lookup_zero_single, Oracle.get.mk_simp]
        exact Bounder_RO_get_secondPreimagePotential «from» «to» sampleto bound RO_m
          Bounder_bounder hfu m1 a g trivial
      | succ m => nomatch m) _ _) ?_
  simp only [Lens.pair, Lens.set_get, Lens.get_of_disjoint_set, hσ]
  have hd : FMap.dom (FMap.set FMap.empty m1 a) m1 := SecureRO.dom_set_iff.mpr (Or.inl rfl)
  have hr : ∀ v, ¬ FMap.rng (FMap.rem (FMap.set (FMap.empty : FMap «from» «to») m1 a) m1) v := by
    rintro v ⟨k, hk⟩
    by_cases hk1 : k = m1
    · subst hk1; simp [FMap.rem] at hk
    · simp [FMap.rem, FMap.set, FMap.empty, Finmap.lookup_erase_ne hk1,
        Finmap.lookup_insert_of_ne _ hk1] at hk
  simp only [secondPreimagePotential, hd, not_true_eq_false, if_false]
  rw [if_neg (hr _), if_pos le_rfl]
  exact le_rfl

/-- EC's `byphoare(: arg = mess1 ==> _); proc; seq 1 : (rng (rem RO.m mess1) (oget RO.m.[mess1])) …`
in `RO_is_second_preimage_resistant`: after `FEL`, the second query hits `RO.m.[m1]` only if it was
already in the range of the rest of `RO.m` (EC's `fel 2`, `FEL_potential`) or with probability
`μ1 sampleto witness` (`SecureRO.secondPreimage_tail_le`). -/
theorem SecondPreimage2_le [Countable «from»] [Lens.Disjoint Bounder_bounder RO_m]
    [Lens.Disjoint SecondPreimage2_m2 Bounder_bounder] [Lens.Disjoint SecondPreimage2_m2 RO_m]
    (hfu : is_funiform sampleto) (A : AdvSecondPreimage «from» «to»)
    (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (hAd : FVP.fvP A ≤ (Bounder_bounder.footprint ⊔ RO_m.footprint)ᶜ) (m1 : «from») :
    @phoareProc (procsig («from») -> Bool) (fun a _ => a = m1)
      (Module.app (SecondPreimage2 «from» «to» bound Bounder_bounder SecondPreimage2_m2)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (fun r _ => indicatorE (r = true)) (· ≤ ·)
      (fun _ _ => (∑ _i ∈ Finset.Ico (0 : ℤ).toNat bound.toNat, sampleto.1 {default}) +
        sampleto.1 {default}) := by
  have hFEL := FEL_potential «from» «to» sampleto bound RO_m Bounder_bounder hfu A hA hAd m1
  have := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
  have := (inferInstance : Lens.Disjoint SecondPreimage2_m2 Bounder_bounder).symm
  have := (inferInstance : Lens.Disjoint SecondPreimage2_m2 RO_m).symm
  phoare_proc_to_stmt
  phoare_inline 0
  repeat phoare_inline 1
  phoare_ewp
  rename_i σ hσ
  -- the tail: `[RO.m.[m1] in the range of the rest of RO.m] + μ` (EC's `seq 1 : (rng …)`)
  refine (Stmt.ewp_mono _ (G := fun τ => indicatorE (¬ FMap.dom (RO_m.get τ.globals)
    ((localVarLens "m1" «from»).get τ) ∨ FMap.rng (FMap.rem (RO_m.get τ.globals)
    ((localVarLens "m1" «from»).get τ)) (oget ((RO_m.get τ.globals).get
    ((localVarLens "m1" «from»).get τ)))) + sampleto.1 {default}) (fun τ => ?_) _).trans ?_
  · by_cases hb : Bounder_bounder.get τ.globals < bound
    · simp only [hb, if_true, Option.some.injEq, exists_eq_left, and_false, exists_false]
      refine le_trans (le_of_eq ?_) (SecureRO.secondPreimage_tail_le hfu (RO_m.get τ.globals)
        ((localVarLens "m1" «from»).get τ) (SecondPreimage2_m2.get τ.globals) True
        (Bounder_bounder.get τ.globals + 1 < bound))
      simp only [if_true, and_comm]
    · simp [hb]
  rw [Stmt.ewp_add]
  refine add_le_add ?_ (Stmt.ewp_const_le _ _ _)
  -- the adversary: EC's `fel 2`
  erw [Stmt.ewp_call]
  simp_reads
  rw [hσ]
  refine le_trans (ProgramDenotation.wp_le_wp_of_le _ _ _ (fun r =>
    SecureRO.indicatorE_secondPreimage_le_potential bound (sampleto.1 {default}) m1
      (Bounder_bounder.get r.2, 0, RO_m.get r.2)) _) ?_
  exact hFEL _ _ rfl

end SecondPreimage

/-- EC's `RO_is_second_preimage_resistant &m (mess1 : from)`, for the section's `A`.  The local
modules' variables `SecondPreimage2.m2`, `D1.m1` are chosen fresh (exception E6), which needs the
theory's variables finitely supported. -/
theorem RO_is_second_preimage_resistant [Countable «from»] [Countable «to»]
    [Lens.Disjoint Bounder_bounder RO_m] [Lens.Disjoint RO_m FRO_m]
    [Lens.Disjoint Bounder_bounder FRO_m]
    (hBfs : Bounder_bounder.footprint.FinitelySupported)
    (hROfs : RO_m.footprint.FinitelySupported) (hFROfs : FRO_m.footprint.FinitelySupported)
    (hax : Axioms «from» «to» sampleto bound increase_counter)
    (A : AdvSecondPreimage «from» «to») (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (_hAd : FVP.fvP A ≤ (Bounder_bounder.footprint ⊔ RO_m.footprint ⊔ FRO_m.footprint)ᶜ)
    (m : VariableAssignment) (mess1 : «from») :
    (Procedure.Pr (Module.app (SecondPreimage «from» «to» bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
        mess1 m (fun r _ => r = true) : ℝ) ≤
      ((bound + 1 : ℤ) : ℝ) * (sampleto.1 {default}).toReal := by
  -- the local modules' variables, fresh (exception E6)
  have hF := ((hA.finitelySupported.sup hBfs).sup hROfs).sup hFROfs
  obtain ⟨S, hS, hSfs⟩ := Footprint.exists_fresh «from» hF
  obtain ⟨D, hD, hDfs⟩ := Footprint.exists_fresh «from» (hF.sup hSfs)
  have hS' : ∀ {X : Footprint VariableAssignment}, X ≤ FVP.fvP A ⊔ Bounder_bounder.footprint ⊔
      RO_m.footprint ⊔ FRO_m.footprint → S.footprint ≤ Xᶜ :=
    fun h => hS.trans (Footprint.compl_antimono h)
  have hD' : ∀ {X : Footprint VariableAssignment}, X ≤ FVP.fvP A ⊔ Bounder_bounder.footprint ⊔
      RO_m.footprint ⊔ FRO_m.footprint ⊔ S.footprint → D.footprint ≤ Xᶜ :=
    fun h => hD.trans (Footprint.compl_antimono h)
  haveI : Lens.Disjoint S Bounder_bounder := Lens.disjoint_of_footprint_le_compl _ _ (hS' (by
    repeat (first | exact le_rfl | exact le_sup_right | apply le_sup_of_le_left)))
  haveI : Lens.Disjoint S RO_m := Lens.disjoint_of_footprint_le_compl _ _ (hS' (by
    repeat (first | exact le_rfl | exact le_sup_right | apply le_sup_of_le_left)))
  haveI : Lens.Disjoint S FRO_m := Lens.disjoint_of_footprint_le_compl _ _ (hS' (by
    repeat (first | exact le_rfl | exact le_sup_right | apply le_sup_of_le_left)))
  haveI : Lens.Disjoint D Bounder_bounder := Lens.disjoint_of_footprint_le_compl _ _ (hD' (by
    repeat (first | exact le_rfl | exact le_sup_right | apply le_sup_of_le_left)))
  haveI : Lens.Disjoint D RO_m := Lens.disjoint_of_footprint_le_compl _ _ (hD' (by
    repeat (first | exact le_rfl | exact le_sup_right | apply le_sup_of_le_left)))
  haveI : Lens.Disjoint D FRO_m := Lens.disjoint_of_footprint_le_compl _ _ (hD' (by
    repeat (first | exact le_rfl | exact le_sup_right | apply le_sup_of_le_left)))
  haveI : Lens.Disjoint D S := Lens.disjoint_of_footprint_le_compl _ _ (hD' (by
    repeat (first | exact le_rfl | exact le_sup_right | apply le_sup_of_le_left)))
  haveI : Lens.Disjoint S D := (inferInstance : Lens.Disjoint D S).symm
  haveI := (inferInstance : Lens.Disjoint S Bounder_bounder).symm
  haveI := (inferInstance : Lens.Disjoint D Bounder_bounder).symm
  have hAS : FVP.fvP A ≤ (S.footprint)ᶜ := (Footprint.le_compl_comm _ _).mp (hS' (by
    repeat (first | exact le_rfl | exact le_sup_right | apply le_sup_of_le_left)))
  have hAD : FVP.fvP A ≤ (D.footprint)ᶜ := (Footprint.le_compl_comm _ _).mp (hD' (by
    repeat (first | exact le_rfl | exact le_sup_right | apply le_sup_of_le_left)))
  have hASD : FVP.fvP A ≤ (S.footprint ⊔ D.footprint)ᶜ :=
    (Footprint.le_compl_comm _ _).mpr (sup_le ((Footprint.le_compl_comm _ _).mp hAS)
      ((Footprint.le_compl_comm _ _).mp hAD))
  have hABR : FVP.fvP A ≤ (Bounder_bounder.footprint ⊔ RO_m.footprint)ᶜ :=
    _hAd.trans (Footprint.compl_antimono le_sup_left)
  -- `D1(A)` is an EasyCrypt-like `RO_Distinguisher`, outside `RO` and `FRO`
  have hD1 := SecondPreimage.fvP_D1 «from» «to» bound Bounder_bounder S D A
  have hD1ec : Module.ECModule (SecondPreimage.D1 «from» «to» bound Bounder_bounder S D A)
      (PROM.FullRO.RO_ext «from» «to») :=
    PROM.FullRO.RO_Distinguisher.ecModule «from» «to» Unit Bool _
      (Footprint.FinitelySupported.mono hD1
      (hA.finitelySupported.sup (by
        simp only [Footprint.lens_pair]
        exact hBfs.sup (hSfs.sup hDfs))))
  have hD1d : FVP.fvP (SecondPreimage.D1 «from» «to» bound Bounder_bounder S D A) ≤
      (RO_m.footprint ⊔ FRO_m.footprint)ᶜ := by
    haveI := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
    haveI := (inferInstance : Lens.Disjoint Bounder_bounder FRO_m).symm
    refine hD1.trans ?_
    simp only [Footprint.lens_pair]
    fp_disjoint
  have hpr := fun {p q : Procedure (procsig («from») -> Bool)} (h : prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂) p q (fun r₁ _ r₂ _ => r₁ = r₂)) =>
    Procedure.Pr_eq_of_prhlProc h (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true)
      (fun r₁ _ r₂ _ hr => by rw [hr]) (a₁ := mess1) (a₂ := mess1) (σ₁ := m) (σ₂ := m) ⟨rfl, rfl⟩
  -- EC's chain of `have->`: `RO` to `LRO`, to `SecondPreimage2`, `SecondPreimage3`, back to `RO`
  rw [hpr (SecondPreimage.SecondPreimage_RO_LRO «from» «to» sampleto bound RO_m Bounder_bounder A
      hA hABR),
    hpr (SecondPreimage.SecondPreimage_SecondPreimage2 «from» «to» sampleto bound RO_m
      Bounder_bounder S A),
    hpr (SecondPreimage.SecondPreimage2_SecondPreimage3 «from» «to» sampleto bound RO_m
      Bounder_bounder S D A hASD _ rfl (fvP_LRO «from» «to» sampleto RO_m)),
    ← hpr (SecondPreimage.SecondPreimage3_RO_LRO «from» «to» sampleto bound RO_m FRO_m
      Bounder_bounder S D hax.sampleto_ll A hD1ec hD1d),
    ← hpr (SecondPreimage.SecondPreimage2_SecondPreimage3 «from» «to» sampleto bound RO_m
      Bounder_bounder S D A hASD _
      (by simp only [RO.RO, RO.LRO, PROM.FullRO.LRO, PROM.FullRO.RO.asRO,
        PROM.FullRO.RO_T.init.mk_simp])
      (fvP_RO «from» «to» sampleto RO_m))]
  -- `byphoare`, `seq 1`, `fel 2`
  have hB := SecondPreimage.SecondPreimage2_le «from» «to» sampleto bound RO_m Bounder_bounder S
    hax.sampleto_fu A hA hABR mess1 mess1 m rfl
  rw [← Procedure.Pr_eq_ewp] at hB
  -- the arithmetic: `∑_{i < bound} μ + μ = (bound + 1) · μ`
  set μ := sampleto.1 {default}
  have hμ : μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((MeasureTheory.measure_mono (Set.subset_univ _)).trans sampleto.2.1)
  simp only [Finset.sum_const, Int.toNat_zero, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul] at hB
  have hR := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hμ, hμ⟩) hB
  rw [ENNReal.coe_toReal, ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hμ) hμ,
    ENNReal.toReal_mul, ENNReal.toReal_natCast] at hR
  refine hR.trans (le_of_eq ?_)
  rw [show ((bound.toNat : ℕ) : ℝ) = (bound : ℝ) by
    exact_mod_cast Int.toNat_of_nonneg hax.bound_ge0]
  push_cast
  ring

/-- EasyCrypt's `module type AdvCollision (F : Oracle) = { proc guess() : from * from }`. -/
abbrev AdvCollision := Oracle «from» «to» →ₘ procmod () → («from» × «from»)

open Classical in
module Collision using (A : AdvCollision «from» «to», F : RF_T «from» «to») {
  proc main () : Bool {
    var m1 : «from», m2 : «from», hash1 : Option «to», hash2 : Option «to»;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ();
    m1, m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to»
          (Module.app (Bounder «from» «to» bound Bounder_bounder) F) })) ();
    hash1 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m1);
    hash2 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

/-! ### The section `Collision`, with `declare module A <: AdvCollision {-RO, -FRO, -Bounder}` (its
local modules in the namespace `Collision`) -/

namespace Collision

module FEL using (A : AdvCollision «from» «to», F : RF_T «from» «to») {
  proc main () : («from» × «from») {
    var m1 : «from», m2 : «from»;
    _ <- call (RF_T.init «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ();
    m1, m2 <- call (Module.app A (Oracle.mk «from» «to»
      { get := RF_T.get «from» «to»
          (Module.app (Bounder «from» «to» bound Bounder_bounder) F) })) ();
    return ($m1, $m2)
  };
}

open Classical in
module Collision2 using (A : AdvCollision «from» «to», F : RF_T «from» «to») {
  proc main () : Bool {
    var m1 : «from», m2 : «from», hash1 : Option «to», hash2 : Option «to»;
    m1, m2 <- call (Module.app (FEL «from» «to» bound Bounder_bounder) (Module.pair A F)) ();
    hash1 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m1);
    hash2 <- call (RF_T.get «from» «to»
      (Module.app (Bounder «from» «to» bound Bounder_bounder) F)) ($m2);
    return decide ($m1 ≠ $m2 ∧ ∃ y, some y = $hash1 ∧ some y = $hash2)
  };
}

/-- The first `have` of EC's proof of `RO_is_collision_resistant`:
`Collision(A, RF(RO)).main ~ Collision2(A, RF(RO)).main : ={glob} ==> ={res}`, by EC's
`byequiv; proc; inline*; sim`. -/
theorem Collision_Collision2 (A : AdvCollision «from» «to») :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (Module.app (Collision «from» «to» bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (Module.app (Collision.Collision2 «from» «to» bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  equiv_proc
  stmt_inline 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 2 2 : (§m1{1} = §m1{2} ∧ §m2{1} = §m2{2} ∧ §allGlobals{1} = §allGlobals{2})
  · equiv_sim
  · equiv_sim

/-- The oracle premise of EC's `fel` in `RO_is_collision_resistant`: a query of
`Bounder(RF(RO)).get` does not increase the potential `SecureRO.collisionPotential` of
`(Bounder.bounder, RO.m)` (`SecureRO.collisionPotential_step`, its counter `0`). -/
theorem Bounder_RO_get_potential [Lens.Disjoint Bounder_bounder RO_m] (hfu : is_funiform sampleto) :
    phoareProc (fun _ _ => True)
      (RF_T.get «from» «to» (Module.app (Bounder «from» «to» bound Bounder_bounder)
        (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (fun _ g => collisionPotential bound (sampleto.1 {default})
        ((Bounder_bounder.get g, 0, RO_m.get g)))
      (· ≤ ·)
      (fun _ g => collisionPotential bound (sampleto.1 {default})
        ((Bounder_bounder.get g, 0, RO_m.get g))) := by
  have := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  exact SecureRO.collisionPotential_step hfu bound _ 0 0 _ _ True


/-- EC's `fel 1 Bounder.bounder (fun i, i%r * mu1 sampleto witness) bound (collision RO.m) …` in
`RO_is_collision_resistant`, as a supermartingale: `FEL(A, RF(RO)).main` ends with the potential at
most `∑_{i < bound} i · μ` (`Module.ewp_app_le`). -/
theorem FEL_potential [Countable «from»] [Lens.Disjoint Bounder_bounder RO_m]
    (hfu : is_funiform sampleto) (A : AdvCollision «from» «to»)
    (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (hAd : FVP.fvP A ≤ (Bounder_bounder.footprint ⊔ RO_m.footprint)ᶜ) :
    phoareProc (fun _ _ => True)
      (Module.app (Collision.FEL «from» «to» bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (fun _ g => collisionPotential bound (sampleto.1 {default})
        ((Bounder_bounder.get g, 0, RO_m.get g)))
      (· ≤ ·)
      (fun _ _ => ∑ i ∈ Finset.Ico (0 : ℤ).toNat bound.toNat,
        (i : ENNReal) * sampleto.1 {default}) := by
  have := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
  have hL : FVP.fvP A ≤ ((Lens.pair Bounder_bounder RO_m).footprint)ᶜ := by
    rw [Footprint.lens_pair]
    exact hAd
  phoare_proc_to_stmt
  phoare_inline 0
  repeat phoare_inline 0
  intro σ _
  simp only [Stmt.ewp_seq, Stmt.ewp_assign]
  simp_reads
  erw [Stmt.ewp_call]
  simp_reads
  refine le_trans (Module.ewp_app_le (Lens.pair Bounder_bounder RO_m) A
    (Oracle.ext «from» «to») hA.representable hL
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable «from»)
      | succ m => nomatch m)
    _ (fun s => collisionPotential bound (sampleto.1 {default}) (s.1, 0, s.2))
    (fun n a g => by cases n with
      | zero =>
        simp only [Oracle.ext, HoleSigs.Instantiation.lookup_zero_single, Oracle.get.mk_simp]
        exact Bounder_RO_get_potential «from» «to» sampleto bound RO_m Bounder_bounder hfu a g
          trivial
      | succ m => nomatch m) _ _) ?_
  simp only [Lens.pair, Lens.set_get, Lens.get_of_disjoint_set, collisionPotential]
  split_ifs with hc hinv
  · rw [RO_m.set_get] at hc
    exact absurd hc SecureRO.not_collision_empty
  · exact le_rfl
  · exact absurd ⟨le_rfl, by simp [FMap.fdom, FMap.empty]⟩ hinv


/-- EC's `byphoare=> //; proc; seq 1 : (collision RO.m) …` in `RO_is_collision_resistant`: after
the adversary (`FEL`), a collision of the two queries needs a collision already in `RO.m` (EC's
`fel`, `FEL_potential`) or a fresh sample hitting a fixed value (`SecureRO.collision_tail_le`, once
the `None` answers of a spent `Bounder` are normalized away). -/
theorem Collision2_le [Countable «from»] [Lens.Disjoint Bounder_bounder RO_m]
    (hfu : is_funiform sampleto) (A : AdvCollision «from» «to»)
    (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (hAd : FVP.fvP A ≤ (Bounder_bounder.footprint ⊔ RO_m.footprint)ᶜ) :
    phoareProc (fun _ _ => True)
      (Module.app (Collision.Collision2 «from» «to» bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
      (fun r _ => indicatorE (r = true)) (· ≤ ·)
      (fun _ _ => (∑ i ∈ Finset.Ico (0 : ℤ).toNat bound.toNat,
        (i : ENNReal) * sampleto.1 {default}) +
        sampleto.1 {default}) := by
  have hFEL := FEL_potential «from» «to» sampleto bound RO_m Bounder_bounder hfu A hA hAd
  have := (inferInstance : Lens.Disjoint Bounder_bounder RO_m).symm
  phoare_proc_to_stmt
  phoare_inline 0
  repeat phoare_inline 1
  phoare_ewp
  refine (Stmt.ewp_mono _ (G := fun σ => indicatorE (SecureRO.collision (RO_m.get σ.globals)) +
    sampleto.1 {default}) (fun τ => ?_) _).trans ?_
  · by_cases hb : Bounder_bounder.get τ.globals < bound
    · simp only [hb, if_true, Option.some.injEq, exists_eq_left, and_false, exists_false]
      refine le_trans (le_of_eq ?_) (SecureRO.collision_tail_le hfu (RO_m.get τ.globals)
        ((localVarLens "m1" «from»).get τ) ((localVarLens "m2" «from»).get τ) True
        (Bounder_bounder.get τ.globals + 1 < bound))
      simp only [if_true, and_comm]
    · simp [hb]
  rw [Stmt.ewp_add]
  refine add_le_add ?_ (Stmt.ewp_const_le _ _ _)
  erw [Stmt.ewp_call]
  simp_reads
  refine le_trans (ProgramDenotation.wp_le_wp_of_le _ _ _ (fun r =>
    SecureRO.indicatorE_collision_le_potential bound (sampleto.1 {default})
      (Bounder_bounder.get r.2, 0, RO_m.get r.2)) _) ?_
  exact hFEL () _ trivial

end Collision

/-- The section's `op collision (m : ('a, 'b) fmap)`: two distinct keys with the same value. -/
def collision {α β : Type} [DecidableEq α] (m : FMap α β) : Prop :=
  ∃ m1 m2, m1 ≠ m2 ∧ FMap.dom m m1 ∧ FMap.dom m m2 ∧ FMap.get m m1 = FMap.get m m2

/-- EC's `RO_is_collision_resistant &m`, for the section's `A`. -/
theorem RO_is_collision_resistant [Countable «from»] [Lens.Disjoint Bounder_bounder RO_m]
    (hax : Axioms «from» «to» sampleto bound increase_counter)
    (A : AdvCollision «from» «to») (hA : Module.ECModule A (Oracle.ext «from» «to»))
    (_hAd : FVP.fvP A ≤ (RO_m.footprint ⊔ FRO_m.footprint ⊔ Bounder_bounder.footprint)ᶜ)
    (m : VariableAssignment) :
    (Procedure.Pr (Module.app (Collision «from» «to» bound Bounder_bounder)
        (Module.pair A (Module.app (RF «from» «to») (RO.RO «from» «to» sampleto RO_m)))).procedure
        () m (fun r _ => r = true) : ℝ) ≤
      ((bound * (bound - 1) + 2 : ℤ) : ℝ) / 2 * (sampleto.1 {default}).toReal := by
  -- `have->: Pr[Collision(A,RF(RO)).main() @ &m : res] =
  --         Pr[Collision2(A,RF(RO)).main() @ &m : res]`
  rw [Procedure.Pr_eq_of_prhlProc
    (Collision.Collision_Collision2 «from» «to» sampleto bound RO_m Bounder_bounder A)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true)
    (fun r₁ _ r₂ _ h => by rw [h]) (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl]
  -- `byphoare`, `seq 1`, `fel`
  have hB := Collision.Collision2_le «from» «to» sampleto bound RO_m Bounder_bounder
    hax.sampleto_fu A hA
    (by fp_disjoint) () m trivial
  rw [← Procedure.Pr_eq_ewp] at hB
  -- the arithmetic: `∑_{i < bound} i · μ + μ = (bound (bound - 1) + 2) / 2 · μ`
  set μ := sampleto.1 {default}
  have hμ : μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((MeasureTheory.measure_mono (Set.subset_univ _)).trans sampleto.2.1)
  have hfin : (∑ i ∈ Finset.Ico (Int.toNat 0) bound.toNat, (i : ENNReal) * μ + μ) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun i _ =>
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top i) hμ, hμ⟩
  have hR := ENNReal.toReal_mono hfin hB
  rw [ENNReal.coe_toReal, ENNReal.toReal_add (ENNReal.sum_ne_top.mpr fun i _ =>
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top i) hμ) hμ, ENNReal.toReal_sum (fun i _ =>
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top i) hμ)] at hR
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, Int.toNat_zero] at hR
  refine hR.trans (le_of_eq ?_)
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, bound = n := ⟨bound.toNat, (Int.toNat_of_nonneg hax.bound_ge0).symm⟩
  rw [Int.toNat_natCast, ← Finset.range_eq_Ico, ← Finset.sum_mul]
  have hs : (∑ i ∈ Finset.range n, (i : ℝ)) = n * (n - 1) / 2 := by
    rw [← Nat.cast_sum, Finset.sum_range_id]
    rcases n with _ | n
    · simp
    · rw [Nat.cast_div (Nat.even_mul_pred_self (n + 1)).two_dvd (by norm_num)]
      push_cast
      ring
  push_cast
  rw [hs]
  ring

end GaudisCrypt.SHA3.SecureORO
