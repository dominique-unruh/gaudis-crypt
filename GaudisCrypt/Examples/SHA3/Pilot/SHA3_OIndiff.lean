import GaudisCrypt.Examples.SHA3.Pilot.SHA3Indiff
import GaudisCrypt.Examples.SHA3.SHA3_OIndiff

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

/-!
# Indifferentiability of the sponge with failing oracles (EasyCrypt `proof/SHA3_OIndiff.ec`) —
EC-fidelity port

`SHA3OIndiff`, the one lemma of `SHA3_OIndiff.ec`, in EC's script, over the first port's
declarations of the file's modules (`Examples/SHA3/SHA3_OIndiff.lean`: `FSome`, `PSome`, `Poget`,
`CSome`, `OSimulator`, `Counter`, `OFC`, `OPC`, `ODRestr`, `DFSome`, `DPSome`, `OD`), as
`Pilot/SHA3Indiff.lean` over the first port's.

Translation:
* the lemma quantifies its own `Dist` (the section's `declare module Dist` is used by none of its
  lemmas): a `declare module` in a section of its own; the restriction also names the modules of
  the files `security` goes through (fresh in EC), and `Dist` has a region for its `glob`
  (`with glob R`, exception E14), since `security` is applied to `OD(Dist)`;
* EC's hypothesis on `Dist` has no restriction on `F` and `P`; `security`'s has (`{-OD(Dist)}`).

Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* GAP 1: `PSome(Perm).init` and `Perm.f` behind the first port's records and views are not opened
  by `inline*`: unfolded first (`simp only [PSome, …]`, `simp only [PRIMITIVE.view, Perm, …]`).
* GAP 2: `sim` does not go through the loops of the inlined `IRO.f` and `Sponge.f` (GAP 2 of
  `Pilot/SHA3Indiff.lean`): the `while` rule with the variables' equalities.  In the body of
  `Sponge.f`'s second loop the closers split `={sa, sc}` at `x <- (sa, sc)` into components, and
  the pair's equation is put back by hand.
* GAP 3: EC's `sim n m` and `sp` at the start of the two games are positions in EC's inlined
  code; ours has the inliner's `reset_vars` statements: `wp` for the last assignments, and the
  initializations stay before the call (EC's `auto` after it takes them).
* GAP 4: the first port's `OD(D, F, P)` passes the oracles on as records of their procedures:
  the hypothesis on `Dist` is applied at those records (as GAP 6 of `Pilot/SHA3Indiff.lean`).
-/

-- the clone `OIndif` contains the module `OIndif` (`OIndif.OIndif`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.Pilot.SHA3_OIndiff

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.Sponge
open GaudisCrypt.SHA3.Sponge.BIRO
open GaudisCrypt.SHA3.SHA3Indiff (Simulator Cntr FC PC DRestr limit)
open GaudisCrypt.SHA3.SHA3_OIndiff (FSome PSome Poget CSome OSimulator Counter OFC OPC ODRestr
  DFSome DPSome OD)
open GaudisCrypt.SHA3.SHA3_OIndiff.OIndif

variable [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params]

-- EC reads the globals of `OD(Dist)` off its code
attribute [local fp_bound] GaudisCrypt.SHA3.SHA3_OIndiff.fvP_OD

set_option synthInstance.checkSynthOrder false in
/-- EC's `glob OD(Dist)`: `glob Dist` (the region given for `Dist`) and `Counter.c`. -/
instance instECGlobOD (D : ODISTINGUISHER) {R : Footprint VariableAssignment}
    [h : Module.ECGlob D R] : Module.ECGlob (OD D) (R ⊔ Counter.c.footprint) := by
  obtain ⟨GF, hGF, hRGF⟩ := h.base
  exact ⟨(h.finite.sup (by fp_finite)).mono (GaudisCrypt.SHA3.SHA3_OIndiff.fvP_OD D),
    (GaudisCrypt.SHA3.SHA3_OIndiff.fvP_OD D).trans (sup_le_sup_right h.le _),
    ⟨GF ⊔ Counter.c.footprint, hGF.sup (by fp_finite),
      sup_le (hRGF.trans (Footprint.glob_mono le_sup_left))
        (Footprint.le_glob_of_le le_sup_right)⟩⟩

section

declare module Dist <: ODISTINGUISHER {-Counter, -Perm, -IRO, -BlockSponge.BIRO.IRO, -Cntr,
  -Simulator, -Gconcl_list.SimLast, -BlockSponge.C, -Gconcl.S, -SLCommon.F.RO, -SLCommon.F.FRO,
  -SLCommon.Redo, -SLCommon.C, -Gconcl_list.BIRO2.IRO, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
  -Gconcl_list.Simulator, -OSimulator,
  -Pilot.Sponge.HybridIRO.HybridIROLazy.mp, -Pilot.Sponge.HybridIRO.HybridIROEager.mp,
  -Pilot.Sponge.HybridIRO.ERO.RO.m, -Pilot.Sponge.HybridIRO.ERO.FRO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.RO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.FRO.m,
  -GaudisCrypt.SHA3.Handle.G1, -GaudisCrypt.SHA3.Gext.G2, -GaudisCrypt.SHA3.ConcreteF.PF,
  -GaudisCrypt.SHA3.Handle.FRO.m, -GaudisCrypt.SHA3.Handle.ROhandle.RO,
  -Pilot.Gext.ReSample.count, -Pilot.Gcol.Gcol.sample_c, -Pilot.ConcreteF.Switching.DBounder,
  -Pilot.ConcreteF.Switching.ARP, -Pilot.ConcreteF.Switching.PRPi.PRPi} with glob R

include R

set_option maxHeartbeats 40000000 in
-- one declaration: EC's two `have`s, each a `byequiv` over the distinguisher's three oracles
set_option synthInstance.maxHeartbeats 400000 in
-- EC's restriction checks by instance search (`Dist` against the modules of `security`)
set_option synthInstance.maxSize 1024 in
/-- EC's `lemma SHA3OIndiff (Dist <: ODISTINGUISHER{-Counter, -Perm, -IRO, -BlockSponge.BIRO.IRO,
-Cntr, -Simulator, -Gconcl_list.SimLast(Gconcl.S), -BlockSponge.C, -Gconcl.S, -SLCommon.F.RO,
-SLCommon.F.FRO, -SLCommon.Redo, -SLCommon.C, -Gconcl_list.BIRO2.IRO, -Gconcl_list.F2.RO,
-Gconcl_list.F2.FRO, -Gconcl_list.Simulator, -OSimulator}) &m :
(forall (F <: ODFUNCTIONALITY) (P <: ODPRIMITIVE), islossless P.f => islossless P.fi =>
islossless F.f => islossless Dist(F,P).distinguish) =>
`|Pr[OGReal(CSome(Sponge), PSome(Perm), ODRestr(Dist)).main() @ &m : res] -
Pr[OGIdeal(FSome(IRO), OSimulator, ODRestr(Dist)).main() @ &m : res]| <=
(limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r`. -/
theorem SHA3OIndiff (m : VariableAssignment) :
    (∀ (F <: ODFUNCTIONALITY), ∀ (P <: ODPRIMITIVE),
      islossless P.f → islossless P.fi → islossless F.f → islossless Dist(F, P).distinguish) →
    |Pr[ OGReal(CSome(Sponge), PSome(Perm), ODRestr(Dist)).main () @ &m : §res ] -
      Pr[ OGIdeal(FSome(IRO.asF), OSimulator, ODRestr(Dist)).main () @ &m : §res ]| ≤
    ((limit ^ 2 - limit : ℤ) : ℝ) / ((2 ^ (r + c + 1).toNat : ℤ) : ℝ) +
      ((4 * limit ^ 2 : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ) := by
  -- EC: move=>h.
  intro h
  -- EC: have->: Pr[OGReal(CSome(Sponge), PSome(Perm), ODRestr(Dist)).main() @ &m : res] =
  --       Pr[RealIndif(Sponge, Perm, DRestr(OD(Dist))).main() @ &m : res].
  have h1 : Pr[ OGReal(CSome(Sponge), PSome(Perm), ODRestr(Dist)).main () @ &m : §res ] =
      Pr[ RealIndif(Sponge, Perm, DRestr(OD(Dist))).main () @ &m : §res ] := by
    -- EC: byequiv=>//=; proc; inline*; sim 4 5; sp.
    --     (GAP 1: `PSome(Perm).init` is `Perm.init` behind the first port's record, opened first;
    --     EC's `sim 4 5` is the two sides' last assignments, `wp`; the initializations stay
    --     before the call, for the last `auto`)
    byequiv; equiv_proc
    simp only [PSome, OptionIndifferentiability.OPRIMITIVE.init.mk_simp]
    stmt_inline*
    stmt_wp
    -- EC: call(: ={glob Perm, glob Counter} /\ ={c}(Counter,Cntr))=>/>; auto.
    equiv_call (_ : ={Perm.m, Perm.mi, Counter.c} ∧ §Counter.c{1} = §Cntr.c{2})
    -- EC: - proc; inline*; sp; auto; if; 1, 3: auto; sp.
    --       by rcondt{2} 1; 1: auto; sp; if; auto.
    · equiv_proc; stmt_inline*; stmt_sp
      stmt_if
      · ec_close
      · stmt_sp
        stmt_rcondt{2} 1
        · hoare_auto
        stmt_sp; stmt_if
        · ec_close
        · ec_auto
        · ec_auto
      · ec_auto
    -- EC: - proc; inline*; sp; auto; if; auto; sp.
    --       by rcondt{2} 1; 1: auto; sp; if; auto.
    · equiv_proc; stmt_inline*; stmt_sp
      stmt_if
      · ec_close
      · stmt_sp
        stmt_rcondt{2} 1
        · hoare_auto
        stmt_sp; stmt_if
        · ec_close
        · ec_auto
        · ec_auto
      · ec_auto
    -- EC: proc; inline*; sp; auto; sp; if; auto; sp.
    --     (GAP 1: `Perm.f` behind the first port's views on the right, opened and inlined; EC's
    --     `auto` unfolds the operator `increase_counter`)
    · equiv_proc; stmt_inline*
      simp only [Indifferentiability.PRIMITIVE.view, Perm, PRP.RP.RP, PRP.StrongPRP.PRP.mk,
        SHA3_OIndiff.increase_counter]
      stmt_inline*
      stmt_sp
      stmt_if
      · ec_close
      · stmt_sp
        -- EC: rcondt{2} 1; auto; sp=>/>.
        stmt_rcondt{2} 1
        · hoare_auto
        stmt_wp; stmt_sp
        -- EC: conseq(:_==> ={glob Perm} /\ n{1} = n0{2} /\ z0{1} = z1{2})=> />; sim.
        equiv_conseq (: _ ==> ={Perm.m, Perm.mi} ∧ §n{1} = §n0{2} ∧
          §z0{1} = §(localVarLens "z1" (List Bool)){2})
        · ec_close
        -- EC: while(={glob Perm, sa, sc, i} /\ (n,z0){1} = (n0,z1){2}); auto.
        equiv_while (={Perm.m, Perm.mi, sa, sc, i} ∧ §n{1} = §n0{2} ∧
          §z0{1} = §(localVarLens "z1" (List Bool)){2})
        -- EC: - by sp; if; auto; sp; if; auto.
        --     (GAP 2: the closers split `={sa, sc}` at the pair `x4 <- (sa, sc)` into components;
        --     the pair's equation is put back by hand)
        · stmt_sp; stmt_if
          · ec_close
          · stmt_sp; stmt_if
            · ec_progress
              have e : x7₁ = x4₂ := Prod.ext ‹x7₁.1 = x4₂.1› ‹x7₁.2 = x4₂.2›
              simp [e]
            · ec_auto; ec_prep
              have e : x7₁ = x4₂ := Prod.ext ‹x7₁.1 = x4₂.1› ‹x7₁.2 = x4₂.2›
              subst e
              ec_close
            · ec_auto; ec_prep
              have e : x7₁ = x4₂ := Prod.ext ‹x7₁.1 = x4₂.1› ‹x7₁.2 = x4₂.2›
              subst e
              ec_close
          · ec_auto; ec_close
        -- EC: conseq(:_==> ={glob Perm, sa, sc})=> />; sim.
        equiv_conseq (: _ ==> ={Perm.m, Perm.mi, sa, sc})
        · ec_close
        -- EC: by while(={glob Perm, sa, sc, xs}); auto; sp; if; auto=> />.
        equiv_while (={Perm.m, Perm.mi, sa, sc, xs})
        · stmt_sp; stmt_if
          · ec_close
          · ec_auto; ec_close
          · ec_auto; ec_close
        ec_auto
      · ec_auto
    --     (EC's `auto` after the call; GAP 14 of `Pilot/Gconcl_list.lean`: `glob Dist` past the
    --     initializations)
    ec_auto
    simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl]
    ec_close
  -- EC: have->: Pr[OGIdeal(FSome(IRO), OSimulator, ODRestr(Dist)).main() @ &m : res] =
  --       Pr[IdealIndif(IRO, Simulator, DRestr(OD(Dist))).main() @ &m : res].
  have h2 : Pr[ OGIdeal(FSome(IRO.asF), OSimulator, ODRestr(Dist)).main () @ &m : §res ] =
      Pr[ IdealIndif(IRO.asF, Simulator, DRestr(OD(Dist))).main () @ &m : §res ] := by
    -- EC: byequiv=>//=; proc; inline*; sim 7 8; sp.
    --     (EC's `sim 7 8` is the two sides' last assignments, `wp`; the initializations stay
    --     before the call, for the last `auto`)
    byequiv; equiv_proc
    stmt_inline*
    stmt_wp
    -- EC: call(: ={glob IRO, glob Simulator, glob Counter} /\ ={c}(Counter,Cntr)); auto.
    equiv_call (_ : ={IRO.mp, Simulator.m, Simulator.mi, Simulator.paths,
        Gconcl_list.BIRO2.IRO.mp, Counter.c} ∧ §Counter.c{1} = §Cntr.c{2})
    -- EC: - proc; inline*; auto; sp; if; auto; sp.
    · equiv_proc; stmt_inline*; stmt_sp
      stmt_if
      · ec_close
      · stmt_sp
        -- EC: rcondt{2} 1; auto; sp; if; 1, 3: auto; sim; if; 1, 3: auto; sp; sim.
        stmt_rcondt{2} 1
        · hoare_auto
        stmt_wp; stmt_sp
        --     (EC's `sim` before a conditional: `sim 1 1`, the code after it, and `wp`)
        stmt_if
        · ec_close
        · sim 1 1
          stmt_if
          · ec_close
          · stmt_sp; stmt_wp
            -- EC: if; [1:by auto=> /> &1 &2 <- /> <- />|3:auto=> />]; sp.
            stmt_if
            · ec_close
            -- EC: * if; auto=> />.
            --       conseq(:_==> ={IRO.mp} /\ bs0{1} = bs{2})=> />; sim=> />.
            --       by move=> &1 &2 <- /> <- />.
            --     (GAP 2: `sim` through the loop is the `while` rule, the variables equal)
            · stmt_sp
              stmt_if
              · ec_close
              · stmt_wp
                equiv_conseq (: _ ==> ={IRO.mp} ∧ §bs{1} = §bs{2})
                · ec_close
                equiv_while (={IRO.mp, i, n, x2, bs})
                · stmt_sp; stmt_if
                  · ec_close
                  · ec_auto
                  · ec_auto
                ec_auto; ec_close
              · ec_auto; ec_close
            -- EC: by if; auto=> />; sim=> &1 &2 /> <- /> <- /= ->.
            · stmt_sp
              stmt_if
              · ec_close
              · stmt_wp
                equiv_while (={Gconcl_list.BIRO2.IRO.mp, i0, n1, x4, bs0})
                · stmt_sp; stmt_if
                  · ec_close
                  · ec_auto
                  · ec_auto
                ec_auto; ec_close
              · ec_auto
          · ec_auto
        · ec_auto
      · ec_auto
    -- EC: - proc; inline*; sp; auto; if; auto; sp.
    --       by rcondt{2} 1; auto; sp; if; auto.
    · equiv_proc; stmt_inline*; stmt_sp
      stmt_if
      · ec_close
      · stmt_sp
        stmt_rcondt{2} 1
        · hoare_auto
        stmt_sp; stmt_if
        · ec_close
        · ec_auto
        · ec_auto
      · ec_auto
    -- EC: proc; inline*; sp; auto; if; auto; sp.
    --     (EC's `auto` unfolds the operator `increase_counter`)
    · equiv_proc; stmt_inline*
      simp only [SHA3_OIndiff.increase_counter]
      stmt_sp
      stmt_if
      · ec_close
      · stmt_sp
        -- EC: rcondt{2} 1; auto; sp; if; auto=> />.
        stmt_rcondt{2} 1
        · hoare_auto
        stmt_wp; stmt_sp
        stmt_if
        · ec_close
        -- EC: by conseq(:_==> bs{1} = bs0{2} /\ ={IRO.mp, glob Simulator})=> />; sim.
        · equiv_conseq (: _ ==> §bs{1} = §bs0{2} ∧ ={IRO.mp, Simulator.m, Simulator.mi,
            Simulator.paths, Gconcl_list.BIRO2.IRO.mp})
          · ec_close
          --     (GAP 2: `sim` through the loop is the `while` rule; the two sides' `x1`, `x2` have
          --     different types elsewhere in the procedures and are named by their slots)
          equiv_while (={IRO.mp, i} ∧
            §(localVarLens "x1" (List Bool)){1} = §(localVarLens "x2" (List Bool)){2} ∧
            §n{1} = §n0{2} ∧ §bs{1} = §bs0{2})
          · stmt_sp; stmt_if
            · ec_close
            · ec_auto
            · ec_auto
          ec_auto
        · ec_auto; ec_close
      · ec_auto
    --     (EC's `auto` after the call; GAP 14 of `Pilot/Gconcl_list.lean`: `glob Dist` past the
    --     initializations)
    ec_auto
    simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl]
    ec_close
  rw [h1, h2]
  -- EC: apply (security (OD(Dist)) _ &m).
  refine @Pilot.SHA3Indiff.security _ _ _ (OD Dist) ⟨by fp_finite, by fp_disjoint⟩
    (R ⊔ Counter.c.footprint) inferInstance
    ⟨‹Footprint.Restricted R _›.finite.sup (by fp_finite), by fp_disjoint⟩ ?_ m
  -- EC: move=> F P hp hpi hf; proc; inline*; sp.
  intro F _ P _ hp hpi hf
  -- EC: + by proc; inline*; sp; if; auto; call hp; auto.
  have hp' : islossless OPC(DPSome(P)).f := by
    phoare_proc; phoare_inline*; stmt_sp; stmt_if
    · phoare_auto; phoare_call hp; phoare_auto
    · phoare_auto
  -- EC: + by proc; inline*; sp; if; auto; call hpi; auto.
  have hpi' : islossless OPC(DPSome(P)).fi := by
    phoare_proc; phoare_inline*; stmt_sp; stmt_if
    · phoare_auto; phoare_call hpi; phoare_auto
    · phoare_auto
  -- EC: by proc; inline*; sp; if; auto; call hf; auto.
  have hf' : islossless OFC(DFSome(F)).f := by
    phoare_proc; phoare_inline*; stmt_sp; stmt_if
    · phoare_auto; phoare_call hf; phoare_auto
    · phoare_auto
  -- EC: call (h (OFC(DFSome(F))) (OPC(DPSome(P))) _ _ _); auto.
  --     (GAP 4: `OD` passes the oracles on as the records of their procedures; EC's three goals
  --     are the facts above)
  phoare_proc
  phoare_call (h
    (SHA3.OptionIndifferentiability.ODFUNCTIONALITY.mk SHA3.SHA3Indiff.state (List Bool × ℤ)
      (List Bool)
      { f := SHA3.OptionIndifferentiability.OFUNCTIONALITY.f SHA3.SHA3Indiff.state (List Bool × ℤ)
          (List Bool) (Module.app OFC (Module.app DFSome F)) })
    (SHA3.OptionIndifferentiability.ODPRIMITIVE.mk SHA3.SHA3Indiff.state (List Bool × ℤ)
      (List Bool)
      { f := SHA3.OptionIndifferentiability.OPRIMITIVE.f SHA3.SHA3Indiff.state (List Bool × ℤ)
          (List Bool) (Module.app OPC (Module.app DPSome P))
        fi := SHA3.OptionIndifferentiability.OPRIMITIVE.fi SHA3.SHA3Indiff.state (List Bool × ℤ)
          (List Bool) (Module.app OPC (Module.app DPSome P)) })
    (by simpa only [SHA3.OptionIndifferentiability.ODPRIMITIVE.f.mk_simp] using hp')
    (by simpa only [SHA3.OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp] using hpi')
    (by simpa only [SHA3.OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp] using hf'))
  phoare_inline*; phoare_auto

end

end GaudisCrypt.SHA3.Pilot.SHA3_OIndiff
