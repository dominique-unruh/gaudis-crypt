import GaudisCrypt.Examples.SHA3.Pilot.IndifRO_is_secure
import GaudisCrypt.Examples.SHA3.Pilot.SHA3Indiff
import GaudisCrypt.Examples.SHA3.SHA3Security

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

/-!
# Top-level proof of SHA-3 security (EasyCrypt `proof/SHA3Security.ec`) — EC-fidelity port

All of `SHA3Security.ec`: the file's modules, the clone `S` of `IndifRO_is_secure`, and the
sections `Preimage` (`Sponge_preimage_resistant`), `SecondPreimage`
(`Sponge_second_preimage_resistant`), `Collision` (`Sponge_coll_resistant`), `SHA3_Collision`
(`SHA3_coll_resistant`).

Translation:
* the file-level type `f_out`, the operators `size_out`, `sigma`, `dout`, `to_list`, `of_list` and
  their axioms are the first port's class `SHA3Security.Params`; `doutE1` is the first port's;
* `clone import IndifRO_is_secure as S with …` is `clone` over the pilot `IndifRO_is_secure`
  (`Syntax/Clone.lean`), its `realize`s the clone's `proof *`.  The clone's module types
  (`Indiff0.FUNCTIONALITY`, …) are the pilot's; the sponge's (`CONSTRUCTION`, `DPRIMITIVE`, …)
  are the first port's, which EC's `Sponge`, `Perm`, `Simulator` are declared at.  A module of a
  first-port module type is one of the pilot's with the same procedures, by definition
  (`CSetSize(Sponge)` is an `Indiff0.CONSTRUCTION`, `Perm` an `Indiff0.PRIMITIVE`);
* `CSetSize(F)(P)`, `FSetSize(F)` alias `init` and take module parameters: the alias is wrapped
  in a call (exception E5); `CSetSize`'s `F` and `DSetSize`'s `D` are Lean parameters;
  `SimSetSize(S)(F) = S(FGetSize(F))` is `Module.comp S FGetSize`;
* the sections' local lemmas about values (`invm_dom_rng`, `invmC'`, `invmC`, `useful`) are the
  first port's (`SHA3Security.Preimage.*`).  EC states and proves them, and the local
  `equiv_sponge_perm`, `equiv_ro_iro`, again in each section, word for word: here once, in
  `Preimage`, and opened in `SecondPreimage` and `Collision`.
* EC's theory `Program` (`Sample`, `LoopSnoc`, `Sample_LoopSnoc_eq`) is not ported as modules:
  the first port has `LoopSnoc.sample` and its run (`LoopSnoc.sample_denotation`).  EC's two
  `transitivity` steps of `equiv_ro_iro`, through `Sample.sample` and through `LoopSnoc.sample`,
  are one step through `LoopSnoc.sample`, with the lemma `dout_LoopSnoc` as its first leg
  (as in exception E12: a sampling against the call of `LoopSnoc.sample`, by the first port's
  rule `prhlStmt_seq_sample_run_map_right`; the only lemma of the file not in EC's script).

Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* GAP 1: `Perm.f` behind the first port's views is not opened by `inline*`: unfolded first
  (`simp only [PRIMITIVE.view, Perm, …]`).
* GAP 2: the closers split `={sa, sc}` at `x <- (sa, sc)` into components; the pair's equation is
  put back by hand before the leaf is closed (as in `Pilot/SHA3_OIndiff.lean`).
* GAP 3: `FInit(F).get` is `F.f` in EC (an alias); here a call (E5), inlined first.  EC's path
  `inline FC(Sponge(Perm)).f` does not elaborate over the first port's views: by index.  EC's
  lists of procedures to inline in front of an adversary's call are `repeat stmt_inline{i} 0`
  (the calls before the abstract one, by call site).
* GAP 4: the exit goal of a one-sided `while` does not frame a variable of the other side that
  only the invariant reads: the conjunct is added to the invariant (GAP 7 of `Pilot/Sponge.lean`).
* GAP 6: the clone's games apply `CSetSize(Sponge)`, `SimSetSize(Simulator)` at the clone's
  module types, where `inline` and the lemmas stated at the sponge's types do not see them:
  rewritten right after `proc` by `CSetSize_Sponge_Perm_init`, `CSetSize_Sponge_Perm_f`,
  `SimSetSize_init_eq` (they hold by `rfl`).
* GAP 7: after `sp` through a game's initializations, `DPre.h` and `glob A` are equal in the
  two memories by the memories' equation, taken out by hand (`congrArg` of the getter,
  `simp_reads_all` / `touched_set_of_le_compl`); GAP 14 of `Pilot/Gconcl_list.lean`.
* GAP 8: `conseq (: _ ==> Q)` in front of the adversary's call does not keep `DPre.h`, which the
  adversary does not write (EC's does): `DPre.h{1} = ha` goes through the call's invariant.
* GAP 5: the strict `auto` runs out of recursion depth on a goal with quantified invariant
  conjuncts over a map being set (GAP 6 of `Pilot/Sponge.lean`): `rnd`, the plain `skip` and
  `progress` (or EC's argument by hand) instead.
-/

-- the clone `S.SRO` contains a module named like its theory; kept (exception E1)
set_option linter.dupNamespace false
-- the `module` command's lemmas do not use every parameter class
set_option linter.unusedSectionVars false

namespace GaudisCrypt.SHA3.Pilot.SHA3Security

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.Sponge
open GaudisCrypt.SHA3.Sponge.BIRO
open GaudisCrypt.SHA3.SHA3Indiff (Simulator Cntr FC PC DRestr)
open GaudisCrypt.SHA3.SHA3Security (size_out sigma f_out dout to_list of_list doutE1 same_ro)

variable [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params]
  [GaudisCrypt.SHA3.SHA3Security.Params]

-- EC's `module SHA3 (P : DPRIMITIVE)`
module SHA3 using (P : DPRIMITIVE) {
  proc init () : Unit {
    return ()
  };
  proc f (bl : List Bool, n : ℤ) : (List Bool) {
    var r : List Bool;
    r <- call Sponge(P).f (($bl ++ [false, true], $n));
    return $r
  };
}

/-! ## `clone import IndifRO_is_secure as S with …` (EC l. 80–100) -/

clone import GaudisCrypt.SHA3.Pilot.IndifRO_is_secure as S with
  type block <- block × capacity, type f_in <- List Bool, type f_out <- f_out,
  op sampleto <- dout,
  op bound <-
    ((GaudisCrypt.SHA3.SHA3Indiff.limit ^ 2 - GaudisCrypt.SHA3.SHA3Indiff.limit : ℤ) : ℝ) /
        ((2 ^ (r + c + 1).toNat : ℤ) : ℝ) +
      ((4 * GaudisCrypt.SHA3.SHA3Indiff.limit ^ 2 : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ),
  op limit <- sigma,
  op bound_counter <- GaudisCrypt.SHA3.SHA3Indiff.limit,
  op increase_counter <- fun (c : ℤ) (m : List Bool) =>
    c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0
  -- EC: realize bound_counter_ge0 by exact(SLCommon.max_ge0).
  --     realize limit_gt0 by exact(sigma_gt0).
  --     realize sampleto_ll by exact(dout_ll).   (likewise `sampleto_fu`, `sampleto_full`)
  --     realize increase_counter_spec by smt(List.size_ge0 divz_ge0 gt0_r).
  proof * by first
    | exact SLCommon.max_ge0
    | exact GaudisCrypt.SHA3.SHA3Security.Params.sigma_gt0
    | exact GaudisCrypt.SHA3.SHA3Security.Params.dout_ll
    | exact GaudisCrypt.SHA3.SHA3Security.Params.dout_fu
    | exact GaudisCrypt.SHA3.SHA3Security.Params.dout_full
    | (intro c m
       have hr := gt0_r
       have h1 : 0 ≤ (size m + 1) / r := Int.ediv_nonneg (by unfold size; omega) hr.le
       have := le_max_right ((size_out + r - 1) / r - 1) 0
       omega)

/-! ## The file's modules (EC l. 62–123) -/

-- EC's `CSetSize(F : CONSTRUCTION)(P : DPRIMITIVE)`, with `F` a Lean parameter so that
-- `CSetSize F` is a construction of the clone; `proc init = F(P).init` wrapped in a call (E5)
set_option linter.gaudisCrypt.using false in
module CSetSize (F : CONSTRUCTION) using (P : DPRIMITIVE) : Indiff0.FUNCTIONALITY {
  proc init () : Unit {
    _ <- call F(P).init ();
    return ()
  };
  proc f (x : List Bool) : f_out {
    var r : List Bool;
    r <- call F(P).f (($x, size_out));
    return oget (of_list $r)
  };
}

-- EC's `FSetSize(F : FUNCTIONALITY)`; `proc init = F.init` wrapped in a call (E5)
module FSetSize using (F : FUNCTIONALITY) : Indiff0.FUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (x : List Bool) : f_out {
    var r : List Bool;
    r <- call F.f (($x, size_out));
    return oget (of_list $r)
  };
}

-- EC's `FGetSize (F : Indiff0.DFUNCTIONALITY)`
module FGetSize using (F : Indiff0.DFUNCTIONALITY) : DFUNCTIONALITY {
  proc f (xi : List Bool × ℤ) : (List Bool) {
    var x : List Bool, i : ℤ, r : f_out;
    x, i <- $xi;
    r <- call F.f ($x);
    return to_list $r
  };
}

/-- EC's `module SimSetSize (S : SIMULATOR) (F : Indiff0.DFUNCTIONALITY) = S(FGetSize(F))`. -/
noncomputable def SimSetSize (S : SIMULATOR) : Indiff0.SIMULATOR := Module.comp S FGetSize

-- EC's `DFSetSize (F : DFUNCTIONALITY)`
module DFSetSize using (F : DFUNCTIONALITY) : Indiff0.DFUNCTIONALITY {
  proc f (x : List Bool) : f_out {
    var r : List Bool;
    r <- call F.f (($x, size_out));
    return oget (of_list $r)
  };
}

/-! ## The globals of the file's modules, and the modules under the clone's module types

EC reads a concrete module's globals off its code, and a module of a sponge module type is one
of the clone's.  Here the bounds are stated (`@[fp_bound]`, `Module.GlobBound` at the clone's
module types: what the clone's lemmas ask), and the modules that the clone's games apply at its
types are the file's by equations that hold by definition (GAP 6). -/

-- EC's `module (DSetSize (D : Indiff0.DISTINGUISHER) : DISTINGUISHER) (F : DFUNCTIONALITY)
-- (P : DPRIMITIVE) = D(DFSetSize(F),P)`, with `D` a Lean parameter; the alias is wrapped in a
-- call (E5)
set_option linter.gaudisCrypt.using false in
module DSetSize (D : Indiff0.DISTINGUISHER) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    b <- call D(DFSetSize(F), P).distinguish ();
    return $b
  };
}

set_option maxHeartbeats 4000000 in
-- `fp_module` through the nest of `DPre`, `Preimage`, `Bounder`
/-- `DSetSize(DPre(A))` touches `A`'s variables, `SRO.Counter.c`, `SRO.Bounder.bounder` and
`DPre.h` (EC reads the globals off the code). -/
@[fp_bound] theorem fvP_DSetSize_DPre (A : SRO.AdvPreimage) :
    FVP.fvP (DSetSize (DPre A)) ≤ FVP.fvP A ⊔
      (SRO.Counter.c.footprint ⊔ (SRO.Bounder.bounder.footprint ⊔ DPre.h.footprint)) := by
  have h : FVP.fvP (DSetSize (DPre A)) ≤ FVP.fvP A ⊔
      (Lens.pair SRO.Counter.c (Lens.pair SRO.Bounder.bounder DPre.h)).footprint := by
    fp_module (Lens.pair SRO.Counter.c (Lens.pair SRO.Bounder.bounder DPre.h))
  simpa only [Footprint.lens_pair] using h

set_option maxHeartbeats 4000000 in
-- `fp_module` through the nest of `D2Pre`, `SecondPreimage`, `Bounder`
/-- `DSetSize(D2Pre(A))` touches `A`'s variables, `SRO.Counter.c`, `SRO.Bounder.bounder` and
`D2Pre.m2` (EC reads the globals off the code). -/
@[fp_bound] theorem fvP_DSetSize_D2Pre (A : SRO.AdvSecondPreimage) :
    FVP.fvP (DSetSize (D2Pre A)) ≤ FVP.fvP A ⊔
      (SRO.Counter.c.footprint ⊔ (SRO.Bounder.bounder.footprint ⊔ D2Pre.m2.footprint)) := by
  have h : FVP.fvP (DSetSize (D2Pre A)) ≤ FVP.fvP A ⊔
      (Lens.pair SRO.Counter.c (Lens.pair SRO.Bounder.bounder D2Pre.m2)).footprint := by
    fp_module (Lens.pair SRO.Counter.c (Lens.pair SRO.Bounder.bounder D2Pre.m2))
  simpa only [Footprint.lens_pair] using h

set_option synthInstance.checkSynthOrder false in
/-- EC's `glob DSetSize(D2Pre(A))`: `glob A` (the region given for `A`), `SRO.Counter.c`,
`SRO.Bounder.bounder` and `D2Pre.m2`. -/
instance instECGlobDSetSizeD2Pre (A : SRO.AdvSecondPreimage) {R : Footprint VariableAssignment}
    [h : Module.ECGlob A R] : Module.ECGlob (DSetSize (D2Pre A))
      (R ⊔ (SRO.Counter.c.footprint ⊔ (SRO.Bounder.bounder.footprint ⊔ D2Pre.m2.footprint))) := by
  obtain ⟨GF, hGF, hRGF⟩ := h.base
  exact ⟨(h.finite.sup (by fp_finite)).mono (fvP_DSetSize_D2Pre A),
    (fvP_DSetSize_D2Pre A).trans (sup_le_sup_right h.le _),
    ⟨GF ⊔ (SRO.Counter.c.footprint ⊔ (SRO.Bounder.bounder.footprint ⊔ D2Pre.m2.footprint)),
      hGF.sup (by fp_finite),
      sup_le (hRGF.trans (Footprint.glob_mono le_sup_left))
        (Footprint.le_glob_of_le le_sup_right)⟩⟩

set_option maxHeartbeats 4000000 in
-- `fp_module` through the nest of `DColl`, `Collision`, `Bounder`
/-- `DSetSize(DColl(A))` touches `A`'s variables, `SRO.Counter.c` and `SRO.Bounder.bounder` (EC
reads the globals off the code). -/
@[fp_bound] theorem fvP_DSetSize_DColl (A : SRO.AdvCollision) :
    FVP.fvP (DSetSize (DColl A)) ≤ FVP.fvP A ⊔
      (SRO.Counter.c.footprint ⊔ SRO.Bounder.bounder.footprint) := by
  have h : FVP.fvP (DSetSize (DColl A)) ≤ FVP.fvP A ⊔
      (Lens.pair SRO.Counter.c SRO.Bounder.bounder).footprint := by
    fp_module (Lens.pair SRO.Counter.c SRO.Bounder.bounder)
  simpa only [Footprint.lens_pair] using h

set_option synthInstance.checkSynthOrder false in
/-- EC's `glob DSetSize(DColl(A))`: `glob A` (the region given for `A`), `SRO.Counter.c` and
`SRO.Bounder.bounder`. -/
instance instECGlobDSetSizeDColl (A : SRO.AdvCollision) {R : Footprint VariableAssignment}
    [h : Module.ECGlob A R] : Module.ECGlob (DSetSize (DColl A))
      (R ⊔ (SRO.Counter.c.footprint ⊔ SRO.Bounder.bounder.footprint)) := by
  obtain ⟨GF, hGF, hRGF⟩ := h.base
  exact ⟨(h.finite.sup (by fp_finite)).mono (fvP_DSetSize_DColl A),
    (fvP_DSetSize_DColl A).trans (sup_le_sup_right h.le _),
    ⟨GF ⊔ (SRO.Counter.c.footprint ⊔ SRO.Bounder.bounder.footprint),
      hGF.sup (by fp_finite),
      sup_le (hRGF.trans (Footprint.glob_mono le_sup_left))
        (Footprint.le_glob_of_le le_sup_right)⟩⟩

set_option synthInstance.checkSynthOrder false in
/-- EC's `glob DSetSize(DPre(A))`: `glob A` (the region given for `A`), `SRO.Counter.c`,
`SRO.Bounder.bounder` and `DPre.h`. -/
instance instECGlobDSetSizeDPre (A : SRO.AdvPreimage) {R : Footprint VariableAssignment}
    [h : Module.ECGlob A R] : Module.ECGlob (DSetSize (DPre A))
      (R ⊔ (SRO.Counter.c.footprint ⊔ (SRO.Bounder.bounder.footprint ⊔ DPre.h.footprint))) := by
  obtain ⟨GF, hGF, hRGF⟩ := h.base
  exact ⟨(h.finite.sup (by fp_finite)).mono (fvP_DSetSize_DPre A),
    (fvP_DSetSize_DPre A).trans (sup_le_sup_right h.le _),
    ⟨GF ⊔ (SRO.Counter.c.footprint ⊔ (SRO.Bounder.bounder.footprint ⊔ DPre.h.footprint)),
      hGF.sup (by fp_finite),
      sup_le (hRGF.trans (Footprint.glob_mono le_sup_left))
        (Footprint.le_glob_of_le le_sup_right)⟩⟩

/-- `CSetSize(Sponge)` has no globals (EC reads it off the code), at the clone's module type. -/
@[fp_bound] theorem fvP_CSetSize_Sponge :
    @FVP.fvP Indiff0.CONSTRUCTION _ (CSetSize Sponge) ≤ ⊥ := by
  (fp_module)

instance : @Module.GlobBound Indiff0.CONSTRUCTION _ (CSetSize Sponge) ⊥ :=
  ⟨fvP_CSetSize_Sponge, by fp_finite⟩

/-- `FGetSize` has no globals. -/
@[fp_bound] theorem fvP_FGetSize : FVP.fvP FGetSize ≤ ⊥ := by
  (fp_module)

set_option maxHeartbeats 2000000 in
-- `fp_module` through `Perm`'s procedures
/-- `Perm` touches `Perm.m`, `Perm.mi`, at the clone's module type (`Perm` is an
`Indiff0.PRIMITIVE` by definition). -/
@[fp_bound] theorem fvP_Perm :
    @FVP.fvP Indiff0.PRIMITIVE _ Perm ≤ Perm.m.footprint ⊔ Perm.mi.footprint := by
  rw [← Footprint.lens_pair]
  fp_module (Lens.pair Perm.m Perm.mi)

instance : @Module.GlobBound Indiff0.PRIMITIVE _ Perm (Perm.m.footprint ⊔ Perm.mi.footprint) :=
  ⟨fvP_Perm, by fp_finite⟩

set_option maxHeartbeats 4000000 in
-- `fp_module` through the simulator's three procedures
/-- `SimSetSize(Simulator)` touches `Simulator`'s maps and `Gconcl_list.BIRO2.IRO.mp` (EC reads
it off the code), at the clone's module type. -/
@[fp_bound] theorem fvP_SimSetSize_Simulator :
    @FVP.fvP Indiff0.SIMULATOR _ (SimSetSize Simulator) ≤ Simulator.m.footprint ⊔
      Simulator.mi.footprint ⊔ Simulator.paths.footprint ⊔
      Gconcl_list.BIRO2.IRO.mp.footprint := by
  refine (FVP.fvP_comp_le _ _).trans (sup_le
    (GaudisCrypt.SHA3.SHA3Security.fvP_Simulator.trans ?_) (fvP_FGetSize.trans bot_le))
  simp only [sup_assoc, le_refl]

instance : @Module.GlobBound Indiff0.SIMULATOR _ (SimSetSize Simulator)
    (Simulator.m.footprint ⊔ Simulator.mi.footprint ⊔ Simulator.paths.footprint ⊔
      Gconcl_list.BIRO2.IRO.mp.footprint) :=
  ⟨fvP_SimSetSize_Simulator, by fp_finite⟩

/-- `SimSetSize(Simulator, F).init` is `Simulator.init`: the simulator is the first port's
module, which `proc` does not open behind the clone's accessor (GAP 6). -/
theorem SimSetSize_init_eq (F : Indiff0.FUNCTIONALITY) :
    SimSetSize(Simulator, F).init = Simulator.init := by
  unfold SimSetSize
  rw [Module.app_comp]
  erw [Simulator.apply_simp]
  exact Module.fst_pair _ _

/-- `CSetSize(Sponge)` applied to `Perm` at the clone's module types (in `Indiff0.GReal`) is
`CSetSize(Sponge, Perm)` at the sponge's, by definition: `init`. -/
theorem CSetSize_Sponge_Perm_init (C : Indiff0.CONSTRUCTION) (P : Indiff0.PRIMITIVE)
    (hC : C = CSetSize Sponge) (hP : P = Perm) :
    «C»(P).init = CSetSize(Sponge, Perm).init := by
  subst hC hP
  rfl

/-- As `CSetSize_Sponge_Perm_init`: `f`. -/
theorem CSetSize_Sponge_Perm_f (C : Indiff0.CONSTRUCTION) (P : Indiff0.PRIMITIVE)
    (hC : C = CSetSize Sponge) (hP : P = Perm) :
    «C»(P).f = CSetSize(Sponge, Perm).f := by
  subst hC hP
  rfl


/-! ## Section `Preimage` (EC l. 125–475) -/

namespace Preimage

open GaudisCrypt.SHA3.SLCommon.Prefix (invm)
open GaudisCrypt.SHA3.SHA3Security.Preimage (invm_dom_rng invmC' invmC useful)

set_option maxHeartbeats 4000000 in
-- one declaration: the sponge's two loops with the permutation inlined
/-- EC's `local equiv equiv_sponge_perm c m :
FInit(CSetSize(Sponge, Perm)).get ~ FInit(DFSetSize(FC(Sponge(Perm)))).get :
={arg, glob Perm} /\ invm Perm.m{1} Perm.mi{1} /\ Cntr.c{2} = c /\ arg{2} = m /\
(Cntr.c + ((size arg + 1) %/ Common.r + 1) + max ((size_out + Common.r - 1) %/ Common.r - 1) 0 <=
limit){2} ==>
={res, glob Perm} /\ invm Perm.m{1} Perm.mi{1} /\
Cntr.c{2} = c + ((size m + 1) %/ Common.r + 1) + max ((size_out + Common.r - 1) %/ Common.r - 1) 0`.
(EC's `c` is `c'`: `c` is the capacity.) -/
theorem equiv_sponge_perm (c' : ℤ) (m : List Bool) :
    equiv[ FInit(CSetSize(Sponge, Perm)).get (x) ~ FInit(DFSetSize(FC(Sponge(Perm)))).get (x) :
      ={x, Perm.m, Perm.mi} ∧ invm §Perm.m{1} §Perm.mi{1} ∧ §Cntr.c{2} = c' ∧ §x{2} = m ∧
        §Cntr.c{2} + ((size §x{2} + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0 ≤
          GaudisCrypt.SHA3.SHA3Indiff.limit ==>
      ={res, Perm.m, Perm.mi} ∧ invm §Perm.m{1} §Perm.mi{1} ∧
        §Cntr.c{2} = c' + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0 ] := by
  -- EC: proc; inline FC(Sponge(Perm)).f; sp.
  --     (GAP 3: `FInit`'s alias is a call, inlined on both sides; `FC(…).f` by index)
  equiv_proc
  stmt_inline{1} 0; stmt_inline{2} 0; stmt_inline{2} 0
  stmt_sp
  -- EC: rcondt{2} 1; auto; sp.
  stmt_rcondt{2} 1
  · hoare_auto
  stmt_wp; stmt_sp
  -- EC: call(: ={glob Perm} /\ invm Perm.m{1} Perm.mi{1})=>/=; auto; inline*.
  equiv_call (_ : ={arg, Perm.m, Perm.mi} ∧ invm §Perm.m{1} §Perm.mi{1} ==>
    ={res, Perm.m, Perm.mi} ∧ invm §Perm.m{1} §Perm.mi{1})
  · equiv_proc
    --     (GAP 1)
    simp only [Indifferentiability.PRIMITIVE.view, Perm, PRP.RP.RP, PRP.StrongPRP.PRP.mk]
    stmt_inline*
    -- EC: while(={i, n, sa, sc, z, glob Perm} /\ invm Perm.m{1} Perm.mi{1}); auto.
    equiv_while (={i, n, sa, sc, z, Perm.m, Perm.mi} ∧ invm §Perm.m{1} §Perm.mi{1})
    -- EC: + sp; if; auto; sp; if; auto; progress.
    --       rewrite invm_set //=.
    --       by move:H4; rewrite supp_dexcepted.
    --     (GAP 2: the pair `x1` back from its components)
    · stmt_sp; stmt_if
      · ec_close
      · stmt_sp; stmt_if
        · ec_progress
          have e : x1₁ = x1₂ := Prod.ext ‹x1₁.1 = x1₂.1› ‹x1₁.2 = x1₂.2›
          simp [e]
        · ec_auto; ec_prep
          have e : x1₁ = x1₂ := Prod.ext ‹x1₁.1 = x1₂.1› ‹x1₁.2 = x1₂.2›
          subst e
          exact fun a ha => ⟨⟨rfl, rfl, rfl, rfl⟩,
            SLCommon.Prefix.invm_set _ _ _ _ ‹_› (EC.not_of_mem_support_dexcepted ha) ‹_›⟩
        · ec_auto; ec_prep
          have e : x1₁ = x1₂ := Prod.ext ‹x1₁.1 = x1₂.1› ‹x1₁.2 = x1₂.2›
          subst e
          ec_close
      · ec_auto; ec_close
    -- EC: sp; conseq(:_==> ={i, n, sa, sc, glob Perm} /\ invm Perm.m{1} Perm.mi{1}); auto.
    stmt_sp
    equiv_conseq (: _ ==> ={i, n, sa, sc, Perm.m, Perm.mi} ∧ invm §Perm.m{1} §Perm.mi{1})
    · ec_close
    -- EC: while(={xs, sa, sc, glob Perm} /\ invm Perm.m{1} Perm.mi{1}); auto.
    equiv_while (={xs, sa, sc, Perm.m, Perm.mi} ∧ invm §Perm.m{1} §Perm.mi{1})
    -- EC: sp; if; auto; progress.
    --     rewrite invm_set=>//=.
    --     by move:H4; rewrite supp_dexcepted.
    · stmt_sp; stmt_if
      · ec_close
      · ec_auto; ec_prep
        exact fun a ha =>
          SLCommon.Prefix.invm_set _ _ _ _ ‹_› (EC.not_of_mem_support_dexcepted ha) ‹_›
      · ec_auto
    ec_auto
  ec_auto

/-- EC's `Sample_LoopSnoc_eq` (theory `Program`) under `rnd to_list (fun x => oget (of_list x))`:
sampling `dout` is running `LoopSnoc.sample(size_out)` and reading the list back.  EC's module
`Sample` is not ported (the first port has `LoopSnoc` and its run, `LoopSnoc.sample_denotation`):
EC's two `transitivity` steps of `equiv_ro_iro` through `Sample.sample` and `LoopSnoc.sample`
are one, with this as its first leg, proved by the first port's rule. -/
theorem dout_LoopSnoc :
    equiv[ §allGlobals{1} = §allGlobals{2} ==>
        §allGlobals{1} = §allGlobals{2} ∧
          §(localVarLens "r" f_out){1} = §(localVarLens "r" f_out){2} ]
      { var l : List Bool;
        l <- [];
        (localVarLens "r" f_out) <$ dout; } ~
      { var l : List Bool;
        l <- call
          (GaudisCrypt.SHA3.SHA3Security.Preimage.Prog.LoopSnoc.sample).procedure (size_out);
        (localVarLens "r" f_out) <- oget (of_list §l); } := by
  stmt_wp; stmt_sp
  stmt_split{1} 1
  stmt_split{2} 1
  refine prhlStmt_seq_sample_run_map_right (x₂ := liftLens (localVarLens "l" (List Bool)))
    (fun _ _ => dlist dbool size_out) (fun l => oget (of_list l)) ?_
  equiv_skip
  intro τ₁ τ₂ hP
  refine ⟨?_, GaudisCrypt.SHA3.SHA3Security.dout_dlist, fun _ _ => ?_⟩
  · refine (programDenotation_call_apply _ _ _ τ₂).trans ?_
    erw [DList.Program.LoopSnoc.sample_denotation]
    refine SubProbability.ext_of_expected fun F => ?_
    simp only [SubProbability.expected_hbind, expected_pure]
    rw [show ProgramState.globalL.set τ₂.globals τ₂ = τ₂ from ProgramState.globalL.get_set τ₂]
  · simp_reads
    exact hP.1

set_option maxHeartbeats 4000000 in
-- one declaration: both cases of the oracle, each with a loop
/-- EC's `local equiv equiv_ro_iro c m :
FInit(RO).get ~ FInit(DFSetSize(FC(BIRO.IRO))).get :
={arg} /\ m = x{2} /\ Cntr.c{2} = c /\
(Cntr.c + ((size arg + 1) %/ Common.r + 1) + max ((size_out + Common.r - 1) %/ Common.r - 1) 0 <=
limit){2} /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} ==>
={res} /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\
Cntr.c{2} = c + ((size m + 1) %/ Common.r + 1) + max ((size_out + Common.r - 1) %/ Common.r - 1) 0`.
(EC's `c` is `c'`.) -/
theorem equiv_ro_iro (c' : ℤ) (m : List Bool) :
    equiv[ FInit(RO).get (x) ~ FInit(DFSetSize(FC(IRO.asF))).get (x) :
      ={x} ∧ same_ro §SRO.RO.m{1} §IRO.mp{2} ∧ §x{2} = m ∧ §Cntr.c{2} = c' ∧
        §Cntr.c{2} + ((size §x{2} + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0 ≤
          GaudisCrypt.SHA3.SHA3Indiff.limit ==>
      ={res} ∧ same_ro §SRO.RO.m{1} §IRO.mp{2} ∧
        §Cntr.c{2} = c' + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0 ] := by
  -- EC: proc; inline *; sp; rcondt{2} 1; 1: auto.
  equiv_proc; stmt_inline*; stmt_sp
  stmt_rcondt{2} 1
  · hoare_auto
  -- EC: swap{2} 1 5; sp; wp 2 1.
  stmt_sp; stmt_wp 2 1
  -- EC: conseq(:_==> oget SRO.RO.RO.m{1}.[x{1}] = oget (of_list bs0{2}) /\
  --       same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); 1:by auto.
  equiv_conseq (: _ ==> oget (FMap.get §SRO.RO.m{1} §x0{1}) = oget (of_list §bs0{2}) ∧
    same_ro §SRO.RO.m{1} §IRO.mp{2})
  · ec_close
  -- EC: rcondt{2} 1; 1: auto.
  stmt_rcondt{2} 1
  · hoare_auto
  -- EC: case: (x{1} \in SRO.RO.RO.m{1}).
  equiv_case (FMap.dom §SRO.RO.m{1} §x0{1})
  -- EC: + rcondf{1} 2; auto.
  · stmt_rcondf{1} 2
    · hoare_auto
    --     exists* BIRO.IRO.mp{2}; elim* => mp.
    equiv_exists* §IRO.mp{2}
    intro mp
    --     while{2}(bs0{2} = map (fun j => oget BIRO.IRO.mp{2}.[(x0{2},j)]) (range 0 i{2})
    --         /\ n0{2} = size_out /\ x0{2} \in SRO.RO.RO.m{1} /\ 0 <= i{2} <= size_out
    --         /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ BIRO.IRO.mp{2} = mp)
    --       (size_out - i{2}); auto.
    --     (GAP 4: the exit goal does not frame `x{1}`, read only by the invariant: the conjunct
    --     `x0{2} = x{1}` is added)
    equiv_while{2} (§bs0{2} =
          List.map (fun j => oget (FMap.get §IRO.mp{2} (§x2{2}, j))) (range 0 §i{2}) ∧
        §n0{2} = size_out ∧ FMap.dom §SRO.RO.m{1} §x2{2} ∧ 0 ≤ §i{2} ∧ §i{2} ≤ size_out ∧
        same_ro §SRO.RO.m{1} §IRO.mp{2} ∧ §IRO.mp{2} = mp ∧ §x2{2} = §x0{1})
      ((size_out - §i{2}).toNat)
    · while_ll_phoare
      intro σ₁
      ec_auto
      intros
      split_ifs
      · exact (is_lossless_iff_expected _).mp dbool_ll
      · rfl
    --     - sp; rcondf 1; auto; 1: smt().
    · intro σ₁ k
      stmt_sp; stmt_rcondf 1
      · hoare_auto
        ec_prep
        have h := (‹same_ro (SRO.RO.m.get σ₁.globals) IRO_mp›).1 _
          ‹(SRO.RO.m.get σ₁.globals).dom _› n1 ⟨‹0 ≤ n1›, ‹n1 < size_out›⟩
        simp [h]
      --       progress.
      --       * have/=<-:= map_rcons (fun (j : int) => oget BIRO.IRO.mp{hr}.[(x0{hr}, j)])
      --           (range 0 i{hr}) i{hr}.
      --         by rewrite !rangeSr //=.
      hoare_auto
      ec_progress
      rw [rangeSr 0 _ ‹_›]
      simp [rcons]
    --     progress.
    · ec_auto
      ec_progress
      --     - exact(dout_ll).
      · exact (is_lossless_iff_expected _).mp GaudisCrypt.SHA3.SHA3Security.Params.dout_ll
      --     - smt(size_out_gt0).
      · exact GaudisCrypt.SHA3.SHA3Security.Params.size_out_gt0.le
      --     - have[] h[#] h1 h2 := H.
      --       have->:i_R = size_out by smt().
      --       have<-:=h2 _ H3.
      --       smt(to_listK).
      · have hi : i = size_out := le_antisymm ‹i ≤ size_out› ‹size_out ≤ i›
        subst hi
        have h2 := (‹same_ro m₁ mp›).2.2 _ ‹m₁.dom _›
        have hk : of_list (to_list (oget (m₁.get xn₂.1))) = some (oget (m₁.get xn₂.1)) :=
          (GaudisCrypt.SHA3.SHA3Security.Params.to_listK _ _).mp rfl
        rw [← h2, hk]
        rfl
  -- EC: rcondt{1} 2; 1: auto; wp =>/=.
  · stmt_rcondt{1} 2
    · hoare_auto
    stmt_wp
    -- EC: exists* BIRO.IRO.mp{2}; elim* => mp.
    equiv_exists* §IRO.mp{2}
    intro mp
    -- EC: conseq(:_==> same_ro SRO.RO.RO.m{1} mp /\ i{2} = size_out /\ … ); progress=>//=.
    equiv_conseq (: _ ==> same_ro §SRO.RO.m{1} mp ∧ §i{2} = size_out ∧
      (∀ l j, FMap.dom mp (l, j) → FMap.dom §IRO.mp{2} (l, j)) ∧
      (∀ l j, FMap.dom mp (l, j) → FMap.get §IRO.mp{2} (l, j) = FMap.get mp (l, j)) ∧
      (∀ l j, FMap.dom §IRO.mp{2} (l, j) → FMap.dom mp (l, j) ∨ l = §x2{2} ∧ 0 ≤ j ∧ j < §i{2}) ∧
      (∀ j, 0 ≤ j ∧ j < §i{2} → FMap.dom §IRO.mp{2} (§x2{2}, j)) ∧
      take §i{2} (to_list §(localVarLens "r" f_out){1}) = §bs0{2} ∧
      take §i{2} (to_list §(localVarLens "r" f_out){1}) =
        List.map (fun j => oget (FMap.get §IRO.mp{2} (§x2{2}, j))) (range 0 §i{2}))
    · ec_progress
      -- EC: + by rewrite get_set_sameE /= oget_some; have[]//=h h1:=to_listK …; smt(…spec_dout).
      · have ht : take size_out (to_list r₁) = to_list r₁ :=
          take_oversize _ _ (le_of_eq (GaudisCrypt.SHA3.SHA3Security.Params.spec_dout r₁))
        have hk : of_list (to_list r₁) = some r₁ :=
          (GaudisCrypt.SHA3.SHA3Security.Params.to_listK _ _).mp rfl
        rw [FMap.get_set_sameE, ht, hk]
      -- EC: + move:H8; rewrite mem_set=>[][]//=h; 1:rewrite(H3 _ _)//=. …
      · rcases (FMap.mem_set _ _ _ _).mp ‹_› with h | rfl
        · exact ‹∀ l j, mp₂.dom (l, j) → IRO_mp₂.dom (l, j)› _ _
            ((‹same_ro RO_m₁ mp₂›).1 _ h i ⟨‹0 ≤ i›, ‹i < size_out›⟩)
        · exact ‹∀ j, 0 ≤ j ∧ j < size_out → IRO_mp₂.dom (xn₂.1, j)› i ⟨‹_›, ‹_›⟩
      -- EC: + rewrite mem_set//=; have[]//=->//=:=H5 _ _ H11; … by exists i0=>//=.
      · rw [FMap.mem_set]
        rcases ‹∀ l j, IRO_mp₂.dom (l, j) → _› _ _ ‹IRO_mp₂.dom (m, _)› with h | ⟨h, -, -⟩
        · refine Or.inl ((‹same_ro RO_m₁ mp₂›).2.1 _ ⟨_, ?_, ?_, h⟩) <;> assumption
        · exact Or.inr h
      -- EC: + move:H7; rewrite take_oversize 1:spec_dout//= => H7. move:H10; rewrite mem_set. …
      · rcases (FMap.mem_set _ _ _ _).mp ‹_› with h | rfl
        · have hne : m ≠ xn₂.1 := fun e => ‹¬RO_m₁.dom xn₂.1› (e ▸ h)
          rw [FMap.get_set_neqE _ _ _ _ hne, (‹same_ro RO_m₁ mp₂›).2.2 _ h]
          refine List.map_congr_left fun j hj => ?_
          have hj' := (mem_range 0 _ j).mp hj
          rw [‹∀ l j, mp₂.dom (l, j) → IRO_mp₂.get (l, j) = mp₂.get (l, j)› _ _
            ((‹same_ro RO_m₁ mp₂›).1 _ h j hj')]
        · rw [FMap.get_set_sameE]
          exact (take_oversize _ _
            (le_of_eq (GaudisCrypt.SHA3.SHA3Security.Params.spec_dout r₁))).symm.trans ‹_›
    -- EC: alias{1} 1 l = [<:bool>].
    stmt_alias{1} 1 l = ([] : List Bool)
    -- EC: transitivity {1} { l <@ Sample.sample(size_out); r <- oget (of_list l); } (…) (…)
    --     … transitivity{1} { l <@ LoopSnoc.sample(size_out); } (…) (…)
    --     (one step: EC's module `Sample` is not ported, `dout_LoopSnoc`)
    equiv_trans{1} {
        l <- call
          (GaudisCrypt.SHA3.SHA3Security.Preimage.Prog.LoopSnoc.sample).procedure (size_out);
        (localVarLens "r" f_out) <- oget (of_list §l); }
      (§allGlobals{1} = §allGlobals{2} ==>
        §allGlobals{1} = §allGlobals{2} ∧
          §(localVarLens "r" f_out){1} = §(localVarLens "r" f_out){2})
      (§x0{1} = §x2{2} ∧ §i{2} = 0 ∧ §n0{2} = size_out ∧ mp = §IRO.mp{2} ∧
          same_ro §SRO.RO.m{1} §IRO.mp{2} ∧ ¬ FMap.dom §SRO.RO.m{1} §x0{1} ∧ §bs0{2} = [] ==>
        same_ro §SRO.RO.m{1} mp ∧ §i{2} = size_out ∧
        (∀ l j, FMap.dom mp (l, j) → FMap.dom §IRO.mp{2} (l, j)) ∧
        (∀ l j, FMap.dom mp (l, j) → FMap.get §IRO.mp{2} (l, j) = FMap.get mp (l, j)) ∧
        (∀ l j, FMap.dom §IRO.mp{2} (l, j) → FMap.dom mp (l, j) ∨ l = §x2{2} ∧ 0 ≤ j ∧ j < §i{2}) ∧
        (∀ j, 0 ≤ j ∧ j < §i{2} → FMap.dom §IRO.mp{2} (§x2{2}, j)) ∧
        take §i{2} (to_list §(localVarLens "r" f_out){1}) = §bs0{2} ∧
        take §i{2} (to_list §(localVarLens "r" f_out){1}) =
          List.map (fun j => oget (FMap.get §IRO.mp{2} (§x2{2}, j))) (range 0 §i{2}))
    · intro σ₁ σ₂ h
      refine ⟨σ₁, rfl, ?_⟩
      ec_close
    · rintro τ₁ τ τ₂ ⟨hg, hr⟩ h
      rw [hg, hr]
      exact h
    · exact dout_LoopSnoc
    -- EC: inline*; sp; wp.
    · stmt_inline*; stmt_sp; stmt_wp
      -- EC: conseq(:_==> i{2} = size_out /\ size l0{1} = i{2} /\ … ); progress.
      equiv_conseq (: _ ==> §i{2} = size_out ∧ size §l0{1} = §i{2} ∧ same_ro §SRO.RO.m{1} mp ∧
        ¬ FMap.dom §SRO.RO.m{1} §x2{2} ∧
        (∀ l j, FMap.dom mp (l, j) → FMap.dom §IRO.mp{2} (l, j)) ∧
        (∀ l j, FMap.dom mp (l, j) → FMap.get §IRO.mp{2} (l, j) = FMap.get mp (l, j)) ∧
        (∀ l j, FMap.dom §IRO.mp{2} (l, j) → FMap.dom mp (l, j) ∨ l = §x2{2} ∧ 0 ≤ j ∧ j < §i{2}) ∧
        (∀ j, 0 ≤ j ∧ j < §i{2} → FMap.dom §IRO.mp{2} (§x2{2}, j)) ∧
        §l0{1} = §bs0{2} ∧
        §bs0{2} = List.map (fun j => oget (FMap.get §IRO.mp{2} (§x2{2}, j))) (range 0 §i{2}))
      --     + smt(take_oversize).
      --     + smt(take_oversize).
      --     (EC's first `conseq` after `Sample` is folded in: `to_list (oget (of_list l)) = l`
      --     for `size l = size_out`, the first port's `to_list_oget_of_list`)
      · ec_progress
        all_goals
          rw [GaudisCrypt.SHA3.SHA3Security.to_list_oget_of_list _ ‹_›]
          exact take_oversize _ _ (le_of_eq ‹_›)
      -- EC: while(0 <= i{2} <= size_out /\ size l0{1} = i{2} /\ n0{2} = size_out /\ ={i} /\
      --       n{1} = n0{2} /\ … ).
      equiv_while (0 ≤ §i{2} ∧ §i{2} ≤ size_out ∧ size §l0{1} = §i{2} ∧ §n0{2} = size_out ∧
        §i0{1} = §i{2} ∧ §n{1} = §n0{2} ∧ same_ro §SRO.RO.m{1} mp ∧
        ¬ FMap.dom §SRO.RO.m{1} §x2{2} ∧
        (∀ l j, FMap.dom mp (l, j) → FMap.dom §IRO.mp{2} (l, j)) ∧
        (∀ l j, FMap.dom mp (l, j) → FMap.get §IRO.mp{2} (l, j) = FMap.get mp (l, j)) ∧
        (∀ l j, FMap.dom §IRO.mp{2} (l, j) → FMap.dom mp (l, j) ∨ l = §x2{2} ∧ 0 ≤ j ∧ j < §i{2}) ∧
        (∀ j, 0 ≤ j ∧ j < §i{2} → FMap.dom §IRO.mp{2} (§x2{2}, j)) ∧
        §l0{1} = §bs0{2} ∧
        §bs0{2} = List.map (fun j => oget (FMap.get §IRO.mp{2} (§x2{2}, j))) (range 0 §i{2}))
      -- EC: + sp; wp=> //=.
      --       rcondt{2} 1; 1:auto; progress.
      · stmt_sp; stmt_wp
        stmt_rcondt{2} 1
        · intro σ₁
          --     (GAP 5: the strict `auto` runs out of recursion depth on
          --     this one-sided goal; the plain `skip`, and EC's argument by hand)
          --     - have[]h1 [] h2 h3 := H1.
          --       have:=h2 x0{hr}; rewrite H2/= negb_exists/= =>/(_ (size bs0{hr})).
          --       rewrite size_ge0 H9/=; apply absurd =>/= h.
          --       by have //=:= H5 _ _ h.
          hoare_skip
          rintro i n0 x2 IRO_mp bs0 x3 n1
            ⟨⟨⟨h0, -, -, rfl, -, -, hs, hnd, -, -, h5, -, -, -⟩, -, hlt⟩, hx⟩
          have e := Prod.mk.inj hx
          rw [e.1, e.2]
          simp only [Bool.not_eq_true', decide_eq_false_iff_not]
          intro hd
          rcases h5 _ _ hd with h | ⟨-, -, h⟩
          · exact hnd (hs.2.1 _ ⟨i, h0, of_decide_eq_true hlt, h⟩)
          · exact lt_irrefl _ h
        -- EC: wp; rnd; auto; progress.
        --     (GAP 5 again: `rnd`, the plain `skip` and `progress` for `auto; progress`)
        --     - smt(size_ge0).
        --     - smt().
        stmt_wp; equiv_rnd; equiv_skip; ec_progress
        -- EC: - by rewrite size_cat/=.
        · rw [size_cat]; rfl
        -- EC: - by rewrite mem_set; left; rewrite H3.
        · rw [FMap.mem_set]; left; exact ‹∀ l j, mp.dom (l, j) → mp₂.dom (l, j)› _ _ ‹_›
        -- EC: - rewrite get_setE (H4 _ _ H11). have/#: !(l1, j) = (x0{2}, size bs0{2}). …
        · have hne : (l, j) ≠ (x3₂, size bs0₂) := by
            rintro e
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
            exact ‹¬m₁.dom _› ((‹same_ro m₁ mp›).2.1 _
              ⟨_, ‹0 ≤ size bs0₂›, ‹size bs0₂ < size_out›, ‹mp.dom _›⟩)
          rw [FMap.get_set_neqE _ _ _ _ hne]
          exact ‹∀ l j, mp.dom (l, j) → mp₂.get (l, j) = mp.get (l, j)› _ _ ‹_›
        -- EC: - move:H11; rewrite mem_set. case((l1, j) \in BIRO.IRO.mp{2})=>//= h; 1: smt(). …
        · rcases (FMap.mem_set _ _ _ _).mp ‹_› with h | h
          · rcases ‹∀ l j, mp₂.dom (l, j) → _› _ _ h with h | ⟨h1, h2, h3⟩
            · exact Or.inl h
            · exact Or.inr ⟨h1, h2, by omega⟩
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
            exact Or.inr ⟨rfl, ‹0 ≤ size bs0₂›, by omega⟩
        -- EC: - rewrite mem_set. case(j = size bs0{2})=>//=. … by apply H6.
        · rw [FMap.mem_set]
          by_cases hj : j = size bs0₂
          · right; rw [hj]
          · left; exact ‹∀ j, 0 ≤ j ∧ j < size bs0₂ → mp₂.dom (x3₂, j)› j ⟨‹0 ≤ j›, by omega⟩
        -- EC: - by rewrite cats1 get_set_sameE oget_some.
        · rw [FMap.get_set_sameE]; rfl
        -- EC: - rewrite get_set_sameE oget_some H7 rangeSr. … by rewrite get_set_neqE //=; smt().
        · rw [FMap.get_set_sameE, rangeSr 0 _ ‹0 ≤ size bs0₂›]
          simp only [rcons, List.map_append, List.map_cons, List.map_nil, FMap.get_set_sameE]
          congr 1
          refine Eq.trans (b := List.map (fun j => oget (mp₂.get (x3₂, j))) (range 0 (size bs0₂)))
            ‹_› (List.map_congr_left fun j hj => ?_)
          have hj' := (mem_range 0 _ j).mp hj
          rw [FMap.get_set_neqE _ _ _ _ (fun e => by obtain ⟨-, e⟩ := Prod.mk.inj e; omega)]
      -- EC: auto; progress.  (… smt(size_out_gt0) …)
      ec_auto
      ec_progress
      exact GaudisCrypt.SHA3.SHA3Security.Params.size_out_gt0.le

section

-- (the restriction as for `Dist` in `Pilot/SHA3Indiff.lean`: EC's, and the variables of the
-- sections' local modules, which are fresh in EC)
-- EC: declare module A <: SRO.AdvPreimage {-SRO.RO.RO, -SRO.RO.FRO, -SRO.Bounder, -Perm,
--   -Gconcl_list.BIRO2.IRO, -Simulator, -Cntr, -BIRO.IRO, -F.RO, -F.FRO, -Redo, -C, -Gconcl.S,
--   -BlockSponge.BIRO.IRO, -BlockSponge.C, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
--   -Gconcl_list.Simulator, -DPre}.
declare module A <: SRO.AdvPreimage {-SRO.RO, -SRO.FRO, -SRO.Bounder, -Perm,
  -Gconcl_list.BIRO2.IRO, -Simulator, -Cntr, -IRO, -SLCommon.F.RO, -SLCommon.F.FRO,
  -SLCommon.Redo, -SLCommon.C, -Gconcl.S, -BlockSponge.BIRO.IRO, -BlockSponge.C,
  -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO, -Gconcl_list.Simulator, -DPre,
  -Gconcl_list.SimLast,
  -Pilot.Sponge.HybridIRO.HybridIROLazy.mp, -Pilot.Sponge.HybridIRO.HybridIROEager.mp,
  -Pilot.Sponge.HybridIRO.ERO.RO.m, -Pilot.Sponge.HybridIRO.ERO.FRO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.RO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.FRO.m,
  -GaudisCrypt.SHA3.Handle.G1, -GaudisCrypt.SHA3.Gext.G2, -GaudisCrypt.SHA3.ConcreteF.PF,
  -GaudisCrypt.SHA3.Handle.FRO.m, -GaudisCrypt.SHA3.Handle.ROhandle.RO,
  -Pilot.Gext.ReSample.count, -Pilot.Gcol.Gcol.sample_c, -Pilot.ConcreteF.Switching.DBounder,
  -Pilot.ConcreteF.Switching.ARP, -Pilot.ConcreteF.Switching.PRPi.PRPi} with glob R

-- EC: declare axiom A_ll (F <: SRO.Oracle {-A}) : islossless F.get => islossless A(F).guess.
variable (A_ll : ∀ (F <: SRO.Oracle {-R}), islossless F.get → islossless A(F).guess)

include R A_ll

set_option maxHeartbeats 40000000 in
-- one declaration: EC's two `have`s, each a `byequiv` through the adversary's oracle
set_option synthInstance.maxHeartbeats 400000 in
-- EC's restriction checks by instance search (`A` against the modules of the lemmas applied)
set_option synthInstance.maxSize 1024 in
/-- EC's `lemma Sponge_preimage_resistant &m ha :
(DPre.h{m} = ha) =>
Pr[SRO.Preimage(A, FM(CSetSize(Sponge), Perm)).main(ha) @ &m : res] <=
(limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r +
(sigma + 1)%r / (2%r ^ size_out)`. -/
theorem Sponge_preimage_resistant (m : VariableAssignment) (ha : f_out) :
    DPre.h.get m = ha →
    Pr[ SRO.Preimage(A, FM(CSetSize(Sponge), Perm)).main (ha) @ &m : §res ] ≤
      ((GaudisCrypt.SHA3.SHA3Indiff.limit ^ 2 - GaudisCrypt.SHA3.SHA3Indiff.limit : ℤ) : ℝ) /
          ((2 ^ (r + c + 1).toNat : ℤ) : ℝ) +
        ((4 * GaudisCrypt.SHA3.SHA3Indiff.limit ^ 2 : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ) +
      ((sigma + 1 : ℤ) : ℝ) / (2 : ℝ) ^ size_out := by
  intro init_ha
  -- EC: rewrite -(doutE1 ha).
  rw [div_eq_mul_inv ((sigma + 1 : ℤ) : ℝ), ← doutE1 ha]
  -- EC: rewrite(preimage_resistant_if_indifferentiable A A_ll (CSetSize(Sponge)) Perm &m ha
  --       init_ha).
  refine S.preimage_resistant_if_indifferentiable A (CSetSize Sponge) Perm m ha init_ha ?_
  -- EC: exists (SimSetSize(Simulator))=>//=; split.
  refine ⟨SimSetSize Simulator, inferInstance, ?_, ?_⟩
  -- EC: + by move=> F _; proc; inline*; auto.
  · intro F _
    rw [SimSetSize_init_eq]
    phoare_proc; phoare_inline*; phoare_auto
  -- EC: have->//:Pr[Indiff0.Indif(CSetSize(Sponge, Perm), Perm, DPre(A)).main() @ &m : res] =
  --       Pr[RealIndif(Sponge, Perm, DRestr(DSetSize(DPre(A)))).main() @ &m : res].
  have h1 : Pr[ Indiff0.GReal(CSetSize(Sponge), Perm, DPre(A)).main () @ &m : §res ] =
      Pr[ RealIndif(Sponge, Perm, DRestr(DSetSize(DPre(A)))).main () @ &m : §res ] := by
    -- EC: byequiv=>//=; proc.
    byequiv (_ : §allGlobals{1} = §allGlobals{2} ∧ §DPre.h{1} = ha ==> ={res})
    case judgment =>
      equiv_proc
      --     (GAP 6: `CSetSize(Sponge)` applied to `Perm` at the clone's module types)
      erw [CSetSize_Sponge_Perm_init _ _ rfl rfl, CSetSize_Sponge_Perm_f _ _ rfl rfl]
      -- EC: inline DPre(A, CSetSize(Sponge, Perm), Perm).distinguish.
      --     inline SRO.Preimage(A, FInit(CSetSize(Sponge, Perm))).main.
      --     (GAP 3: the paths do not elaborate over the first port's views: by call site)
      stmt_inline{1} 2; stmt_inline{1} 2
      -- EC: inline DRestr(DSetSize(DPre(A)), Sponge(Perm), Perm).distinguish
      --       DSetSize(DPre(A), FC(Sponge(Perm)), PC(Perm)).distinguish
      --       SRO.Preimage(A, FInit(DFSetSize(FC(Sponge(Perm))))).main.
      stmt_inline{2} 2; stmt_inline{2} 3; stmt_inline{2} 3; stmt_inline{2} 3
      -- EC: inline Perm.init CSetSize(Sponge, Perm).init Sponge(Perm).init
      --       FC(Sponge(Perm)).init SRO.Counter.init Cntr.init
      --       SRO.Bounder(FInit(CSetSize(Sponge, Perm))).init
      --       SRO.Bounder(FInit(DFSetSize(FC(Sponge(Perm))))).init
      --       FInit(CSetSize(Sponge, Perm)).init
      --       FInit(DFSetSize(FC(Sponge(Perm)))).init; sp.
      repeat stmt_inline{1} 0
      repeat stmt_inline{2} 0
      stmt_sp
      -- EC: wp; sp; sim 2 2.
      stmt_wp
      -- EC: seq 1 1 : (={m, hash, glob DPre, glob SRO.Counter, glob Perm}
      --       /\ invm Perm.m{1} Perm.mi{1} /\ DPre.h{1} = ha
      --       /\ ={c}(SRO.Counter,Cntr)); last first.
      equiv_seq 1 1 : (={m, hash, DPre.h, SRO.Counter.c, Perm.m, Perm.mi} ∧
        invm §Perm.m{1} §Perm.mi{1} ∧ §DPre.h{1} = ha ∧ §SRO.Counter.c{1} = §Cntr.c{2})
      swap
      -- EC: - if; auto; sp.
      · stmt_if
        · ec_close
        · -- EC: exists* m{1}, SRO.Counter.c{1}; elim* => mess c.
          equiv_exists* §m{1}, §SRO.Counter.c{1}
          intro mess c
          -- EC: by call(equiv_sponge_perm c mess); auto; smt().
          stmt_wp
          equiv_call (equiv_sponge_perm c mess)
          --     (the clone's `increase_counter`, `bound_counter` are the file's by definition)
          ec_auto; ec_progress
          exact le_of_lt ‹_›
        · ec_auto
      -- EC: call(: ={glob SRO.Counter, glob Perm, glob DPre, glob SRO.Bounder}
      --       /\ DPre.h{1} = ha
      --       /\ invm Perm.m{1} Perm.mi{1} /\ ={c}(SRO.Counter,Cntr)).
      equiv_call (_ : ={SRO.Counter.c, Perm.m, Perm.mi, DPre.h, SRO.Bounder.bounder} ∧
        §DPre.h{1} = ha ∧ invm §Perm.m{1} §Perm.mi{1} ∧ §SRO.Counter.c{1} = §Cntr.c{2})
      -- EC: + proc; sp; if; auto; sp; if; auto; sp.
      · equiv_proc; stmt_sp
        stmt_if
        · ec_close
        · stmt_sp
          stmt_if
          · ec_close
          · stmt_sp
            -- EC: exists * x{1}; elim* => m c1 c2 b1 b2.
            equiv_exists* §x{1}, §Cntr.c{2}
            intro m' c1
            -- EC: by call(equiv_sponge_perm c1 m); auto; smt().
            equiv_call (equiv_sponge_perm c1 m')
            ec_auto; ec_progress
            · exact le_of_lt ‹SecureRO.increase_counter _ _ < _›
            · exact (‹SRO.Counter.c.get g₁ = _›).trans (‹Cntr.c.get g₂ = _›).symm
          · ec_auto; ec_close
        · ec_auto
      -- EC: auto; progress.
      --     by rewrite /invm=> x y; rewrite 2!emptyE.
      --     (GAP 7: `DPre.h` and `glob A` past the initializations' writes, from the two
      --     memories' equation, by hand)
      ec_auto; ec_progress
      · have h := congrArg DPre.h.get ‹Perm.m.set _ _ = _›
        simp_reads_all; exact h
      · have h := congrArg (FVP.fvP A).touched_getter.get ‹Perm.m.set _ _ = _›
        simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at h
        exact h
      · have h := congrArg DPre.h.get ‹Perm.m.set _ _ = _›
        simp_reads_all; exact h
      · have h := congrArg DPre.h.get ‹Perm.m.set _ _ = _›
        simp_reads_all; exact h
  -- EC: have->//:Pr[Indiff0.Indif(RO, SimSetSize(Simulator, RO), DPre(A)).main() @ &m : res] =
  --       Pr[IdealIndif(BIRO.IRO, Simulator, DRestr(DSetSize(DPre(A)))).main() @ &m : res].
  have h2 : Pr[ Indiff0.GIdeal(RO, SimSetSize(Simulator), DPre(A)).main () @ &m : §res ] =
      Pr[ IdealIndif(IRO.asF, Simulator, DRestr(DSetSize(DPre(A)))).main () @ &m : §res ] := by
    -- EC: byequiv=>//=; proc.
    byequiv (_ : §allGlobals{1} = §allGlobals{2} ∧ §DPre.h{1} = ha ==> ={res})
    case judgment =>
      equiv_proc
      --     (GAP 6: `SimSetSize(Simulator, RO).init` is `Simulator.init`)
      rw [SimSetSize_init_eq]
      repeat stmt_inline{1} 0
      repeat stmt_inline{2} 0
      stmt_sp; stmt_wp
      -- EC: seq 1 1 : (={m, glob SRO.Counter, glob DPre, hash}
      --       /\ ={c}(SRO.Counter,Cntr) /\ DPre.h{1} = hash{1}
      --       /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); last first.
      equiv_seq 1 1 : (={m, SRO.Counter.c, DPre.h, hash} ∧ §SRO.Counter.c{1} = §Cntr.c{2} ∧
        §DPre.h{1} = §hash{1} ∧ same_ro §SRO.RO.m{1} §IRO.mp{2})
      swap
      -- EC: - if; auto; sp.
      · stmt_if
        · ec_close
        · -- EC: exists * m{1}, SRO.Counter.c{1}; elim* => mess c.
          equiv_exists* §m{1}, §SRO.Counter.c{1}
          intro mess c
          -- EC: by call(equiv_ro_iro c mess); auto; smt().
          stmt_wp
          equiv_call (equiv_ro_iro c mess)
          ec_auto
          ec_progress
          exact le_of_lt ‹_›
        · ec_auto
      -- EC: conseq(:_==> ={m, glob SRO.Counter, glob SRO.Bounder, glob DPre}
      --       /\ ={c}(SRO.Counter,Cntr)
      --       /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); progress.
      --     (GAP 8: EC's `conseq` keeps `DPre.h`, which the adversary does not write; here the
      --     fact `DPre.h{1} = ha` goes through the call's invariant, as on the real side)
      equiv_conseq (: _ ==> ={m, SRO.Counter.c, SRO.Bounder.bounder, DPre.h} ∧
        §SRO.Counter.c{1} = §Cntr.c{2} ∧ same_ro §SRO.RO.m{1} §IRO.mp{2} ∧ §DPre.h{1} = ha)
      · ec_progress
        have h := congrArg DPre.h.get ‹Simulator.m.set _ _ = _›
        simp_reads_all; exact h
      -- EC: call(: ={glob SRO.Counter, glob SRO.Bounder, glob DPre}
      --       /\ ={c}(SRO.Counter,Cntr)
      --       /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); auto.
      equiv_call (_ : ={SRO.Counter.c, SRO.Bounder.bounder, DPre.h} ∧
        §SRO.Counter.c{1} = §Cntr.c{2} ∧ same_ro §SRO.RO.m{1} §IRO.mp{2} ∧ §DPre.h{1} = ha)
      -- EC: + proc; sp; if; auto; sp; if; auto; sp.
      · equiv_proc; stmt_sp
        stmt_if
        · ec_close
        · stmt_sp
          stmt_if
          · ec_close
          · -- EC: exists* x{1}; elim* => a c1 c2 b1 b2.
            equiv_exists* §x{1}, §Cntr.c{2}
            intro a c1
            -- EC: call(equiv_ro_iro c1 a); auto; smt().
            equiv_call (equiv_ro_iro c1 a)
            ec_auto; ec_progress
            · exact le_of_lt ‹SecureRO.increase_counter _ _ < _›
            · exact (‹SRO.Counter.c.get g₁ = _›).trans (‹Cntr.c.get g₂ = _›).symm
          · ec_auto; ec_close
        · ec_auto
      --     (GAP 7: `DPre.h` and `glob A` past the initializations' writes)
      ec_auto; ec_progress
      · have h := congrArg DPre.h.get ‹Simulator.m.set _ _ = _›
        simp_reads_all; exact h
      · have h := congrArg (FVP.fvP A).touched_getter.get ‹Simulator.m.set _ _ = _›
        simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at h
        exact h
      · have h := congrArg DPre.h.get ‹Simulator.m.set _ _ = _›
        simp_reads_all; exact h
      -- EC: smt(mem_empty).
      · have h := ‹(SRO.RO.m.get globals₁).dom m›
        rw [‹SRO.RO.m.get globals₁ = FMap.empty›] at h
        exact absurd h (FMap.mem_empty _)
      · have h := ‹(IRO.mp.get globals₂).dom _›
        rw [‹IRO.mp.get globals₂ = FMap.empty›] at h
        exact absurd h (FMap.mem_empty _)
      · have h := ‹(SRO.RO.m.get globals₁).dom m›
        rw [‹SRO.RO.m.get globals₁ = FMap.empty›] at h
        exact absurd h (FMap.mem_empty _)
  rw [h1, h2]
  -- EC: have->//=:= SHA3Indiff (DSetSize(DPre(A))) &m _.
  refine @Pilot.SHA3Indiff.SHA3Indiff _ _ _ (DSetSize (DPre A)) ⟨by fp_finite, by fp_disjoint⟩
    (R ⊔ (SRO.Counter.c.footprint ⊔ (SRO.Bounder.bounder.footprint ⊔ DPre.h.footprint)))
    inferInstance ⟨‹Footprint.Restricted R _›.finite.sup (by fp_finite), by fp_disjoint⟩ m ?_
  -- EC: move=> F P P_f_ll P_fi_ll F_ll; proc; inline*; auto; sp; auto.
  intro F _ P _ P_f_ll P_fi_ll F_ll
  phoare_proc; phoare_inline*; stmt_sp; stmt_wp
  -- EC: seq 1 : true; auto.
  phoare_seq_lossless 1 : (True)
  -- EC: + call (A_ll (SRO.Bounder(FInit(DFSetSize(F)))) _); auto.
  · phoare_call (@A_ll _ ?_ ?_)
    · phoare_auto
    -- EC: by proc; inline*; sp; if; auto; sp; if; auto; sp; call F_ll; auto.
    · phoare_proc; phoare_inline*; stmt_sp; stmt_if
      · stmt_sp; stmt_if
        · phoare_auto; phoare_call F_ll; phoare_auto
        · phoare_auto
      · phoare_auto
  -- EC: if; auto; sp.
  --     by call F_ll; auto.
  · stmt_if
    · phoare_auto; phoare_call F_ll; phoare_auto
    · phoare_auto

end

end Preimage

/-! ## Section `SecondPreimage` (EC l. 479–865) -/

namespace SecondPreimage

open GaudisCrypt.SHA3.SLCommon.Prefix (invm)
open GaudisCrypt.SHA3.SHA3Security.Preimage (invm_dom_rng invmC' invmC useful)
-- EC proves the section's local `equiv_sponge_perm`, `equiv_ro_iro` again, word for word
open Preimage (equiv_sponge_perm equiv_ro_iro)

section

-- (the restriction as in section `Preimage`, and the variables of `SRO`'s section-local
-- modules, as in the clone's theory)
-- EC: declare module A <: SRO.AdvSecondPreimage {-SRO.RO.RO, -SRO.RO.FRO, -SRO.Bounder, -Perm,
--   -Gconcl_list.BIRO2.IRO, -Simulator, -Cntr, -BIRO.IRO, -F.RO, -F.FRO, -Redo, -C, -Gconcl.S,
--   -BlockSponge.BIRO.IRO, -BlockSponge.C, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
--   -Gconcl_list.Simulator, -D2Pre}.
declare module A <: SRO.AdvSecondPreimage {-SRO.RO, -SRO.FRO, -SRO.Bounder, -Perm,
  -Gconcl_list.BIRO2.IRO, -Simulator, -Cntr, -IRO, -SLCommon.F.RO, -SLCommon.F.FRO,
  -SLCommon.Redo, -SLCommon.C, -Gconcl.S, -BlockSponge.BIRO.IRO, -BlockSponge.C,
  -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO, -Gconcl_list.Simulator, -D2Pre,
  -SRO.SecondPreimage.SecondPreimage2, -SRO.SecondPreimage.D1,
  -Gconcl_list.SimLast,
  -Pilot.Sponge.HybridIRO.HybridIROLazy.mp, -Pilot.Sponge.HybridIRO.HybridIROEager.mp,
  -Pilot.Sponge.HybridIRO.ERO.RO.m, -Pilot.Sponge.HybridIRO.ERO.FRO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.RO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.FRO.m,
  -GaudisCrypt.SHA3.Handle.G1, -GaudisCrypt.SHA3.Gext.G2, -GaudisCrypt.SHA3.ConcreteF.PF,
  -GaudisCrypt.SHA3.Handle.FRO.m, -GaudisCrypt.SHA3.Handle.ROhandle.RO,
  -Pilot.Gext.ReSample.count, -Pilot.Gcol.Gcol.sample_c, -Pilot.ConcreteF.Switching.DBounder,
  -Pilot.ConcreteF.Switching.ARP, -Pilot.ConcreteF.Switching.PRPi.PRPi} with glob R

-- EC: declare axiom A_ll (F <: SRO.Oracle {-A}) : islossless F.get => islossless A(F).guess.
variable (A_ll : ∀ (F <: SRO.Oracle {-R}), islossless F.get → islossless A(F).guess)

include R A_ll

set_option maxHeartbeats 40000000 in
-- one declaration: EC's two `have`s, each a `byequiv` through the adversary's oracle
set_option synthInstance.maxHeartbeats 400000 in
-- EC's restriction checks by instance search (`A` against the modules of the lemmas applied)
set_option synthInstance.maxSize 1024 in
/-- EC's `lemma Sponge_second_preimage_resistant &m mess :
(D2Pre.m2{m} = mess) =>
Pr[SRO.SecondPreimage(A, FM(CSetSize(Sponge), Perm)).main(mess) @ &m : res] <=
(limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r +
(sigma + 1)%r / (2%r ^ size_out)`. -/
theorem Sponge_second_preimage_resistant (m : VariableAssignment) (mess : List Bool) :
    D2Pre.m2.get m = mess →
    Pr[ SRO.SecondPreimage(A, FM(CSetSize(Sponge), Perm)).main (mess) @ &m : §res ] ≤
      ((GaudisCrypt.SHA3.SHA3Indiff.limit ^ 2 - GaudisCrypt.SHA3.SHA3Indiff.limit : ℤ) : ℝ) /
          ((2 ^ (r + c + 1).toNat : ℤ) : ℝ) +
        ((4 * GaudisCrypt.SHA3.SHA3Indiff.limit ^ 2 : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ) +
      ((sigma + 1 : ℤ) : ℝ) / (2 : ℝ) ^ size_out := by
  -- EC: move=> init_mess.
  intro init_mess
  -- EC: rewrite -(doutE1 witness).
  rw [div_eq_mul_inv ((sigma + 1 : ℤ) : ℝ), ← doutE1 default]
  -- EC: rewrite(second_preimage_resistant_if_indifferentiable A A_ll (CSetSize(Sponge)) Perm &m
  --       mess init_mess).
  refine S.second_preimage_resistant_if_indifferentiable A (CSetSize Sponge) Perm m mess
    init_mess ?_
  -- EC: exists (SimSetSize(Simulator)); split.
  refine ⟨SimSetSize Simulator, inferInstance, ?_, ?_⟩
  -- EC: + by move=> F _; proc; inline*; auto.
  · intro F _
    rw [SimSetSize_init_eq]
    phoare_proc; phoare_inline*; phoare_auto
  -- EC: have->:Pr[Indiff0.Indif(CSetSize(Sponge, Perm), Perm, D2Pre(A)).main() @ &m : res] =
  --       Pr[RealIndif(Sponge, Perm, DRestr(DSetSize(D2Pre(A)))).main() @ &m : res].
  have h1 : Pr[ Indiff0.GReal(CSetSize(Sponge), Perm, D2Pre(A)).main () @ &m : §res ] =
      Pr[ RealIndif(Sponge, Perm, DRestr(DSetSize(D2Pre(A)))).main () @ &m : §res ] := by
    -- EC: byequiv=>//=; proc.
    byequiv; equiv_proc
    --     (GAP 6: `CSetSize(Sponge)` applied to `Perm` at the clone's module types)
    erw [CSetSize_Sponge_Perm_init _ _ rfl rfl, CSetSize_Sponge_Perm_f _ _ rfl rfl]
    repeat stmt_inline{1} 0
    repeat stmt_inline{2} 0
    stmt_sp; stmt_wp
    -- EC: seq 1 1 : (={m1, m2, glob SRO.Counter, glob Perm}
    --       /\ invm Perm.m{1} Perm.mi{1}
    --       /\ ={c}(SRO.Counter,Cntr)); last first.
    equiv_seq 1 1 : (={m1, m2, SRO.Counter.c, Perm.m, Perm.mi} ∧ invm §Perm.m{1} §Perm.mi{1} ∧
      §SRO.Counter.c{1} = §Cntr.c{2})
    swap
    -- EC: - if; auto; sp.
    · stmt_if
      · ec_close
      · stmt_sp
        -- EC: case(SRO.Counter.c{1} + ((size m2{1} + 1) %/ r + 1) +
        --       max ((size_out + r - 1) %/ r - 1) 0 < limit); last first.
        equiv_case (§SRO.Counter.c{1} + ((size §m2{1} + 1) / r + 1) +
          max ((size_out + r - 1) / r - 1) 0 < GaudisCrypt.SHA3.SHA3Indiff.limit)
        swap
        -- EC: * rcondf{1} 2; 1: by auto; inline*; auto; conseq(: _ ==> true); auto.
        · stmt_rcondf{1} 2
          · intro σ₂
            hoare_call (: True ==> True) / SRO.Counter.c
            ec_auto
          -- EC: rcondf{2} 2; 1: by auto; inline*; auto; conseq(: _ ==> true); auto.
          stmt_rcondf{2} 2
          · intro σ₁
            hoare_call (: True ==> True) / SRO.Counter.c
            ec_auto; ec_progress
            have e : SecureRO.Counter.c.get g = SecureRO.Counter.c.get σ₁.globals :=
              (‹SecureRO.Counter.c.get g = _›).trans (‹SecureRO.Counter.c.get σ₁.globals = _›).symm
            rw [e]
            exact ‹GaudisCrypt.SHA3.SHA3Indiff.limit ≤ _›
          -- EC: auto; inline*; auto; sp; conseq(: _ ==> true); auto.
          stmt_wp
          --     (GAP 1: `Perm.f` behind the first port's view is opened first)
          simp only [Indifferentiability.PRIMITIVE.view, Perm, PRP.RP.RP, PRP.StrongPRP.PRP.mk]
          stmt_inline*
          stmt_sp
          equiv_conseq (: _ ==> True)
          · ec_close
          -- EC: if{2}; sp; auto; sim.
          stmt_if{2}
          --     (EC's `sim` through the two loops is the `while` rule on each)
          · stmt_sp; stmt_wp
            equiv_while (={i, sa, sc, Perm.m, Perm.mi} ∧ §n{1} = §n0{2})
            --     (GAP 2: the pair `x3` back from its components)
            · stmt_sp; stmt_if
              · ec_close
              · stmt_sp; stmt_if
                · ec_progress
                  have e : x3₁ = x4₂ := Prod.ext ‹x3₁.1 = x4₂.1› ‹x3₁.2 = x4₂.2›
                  simp [e]
                · ec_auto; ec_prep
                  have e : x3₁ = x4₂ := Prod.ext ‹x3₁.1 = x4₂.1› ‹x3₁.2 = x4₂.2›
                  subst e
                  exact fun a _ => ⟨rfl, rfl, rfl, rfl⟩
                · ec_auto; ec_prep
                  have e : x3₁ = x4₂ := Prod.ext ‹x3₁.1 = x4₂.1› ‹x3₁.2 = x4₂.2›
                  subst e
                  exact ⟨rfl, rfl⟩
              · ec_auto; ec_close
            equiv_while (={xs, sa, sc, i, Perm.m, Perm.mi} ∧ §n{1} = §n0{2})
            · stmt_sp; stmt_if
              · ec_close
              · ec_auto
              · ec_auto
            ec_auto; ec_close
          · stmt_wp
            -- EC: while{1}(invm Perm.m{1} Perm.mi{1}) (((size_out + r - 1) %/ r)-i{1}).
            equiv_while{1} (invm §Perm.m{1} §Perm.mi{1}) ((((§n{1} + r - 1) / r) - §i{1}).toNat)
            · while_ll_phoare
              -- EC: + auto; sp; if; auto.
              --       - sp; if ;auto; progress.
              --         * exact (useful _ _ _ H H2).
              intro σ₂
              ec_auto
              intro Perm_m mi i n sa sc hI
              split_ifs with h1 h2
              · exact (is_lossless_iff_expected _).mp (useful _ _ _ hI.1 (of_decide_eq_false h2))
              · rfl
              · rfl
            --         * rewrite invm_set=>//=.
            --           by move:H4; rewrite  supp_dexcepted.
            --         * smt().
            --         smt().
            --       smt().
            · intro σ₂ k
              hoare_auto; ec_progress
              exact SLCommon.Prefix.invm_set _ _ _ _ ‹¬Perm_m.dom (sa, sc)›
                (EC.not_of_mem_support_dexcepted ‹a ∈ _›) ‹invm Perm_m mi› _ _
            -- EC: conseq(:_==> invm Perm.m{1} Perm.mi{1}); 1:smt().
            equiv_conseq (: _ ==> invm §Perm.m{1} §Perm.mi{1})
            · ec_close
            -- EC: while{1}(invm Perm.m{1} Perm.mi{1})(size xs{1}).
            equiv_while{1} (invm §Perm.m{1} §Perm.mi{1}) ((size §xs{1}).toNat)
            · while_ll_phoare
              intro σ₂
              -- EC: + move=> _ z; auto; sp; if; auto; progress.
              --       * exact (useful _ _ _ H H1).
              ec_auto
              intros; split_ifs
              · exact (is_lossless_iff_expected _).mp
                  (useful _ _ _ (‹invm _ _ ∧ _›).1 (of_decide_eq_false ‹_›))
              · rfl
            · intro σ₂ k
              hoare_auto; ec_progress
              --       smt().
              · cases xs with
                | nil => exact absurd ‹([] : List block).isEmpty = false› (by simp)
                | cons a l => simp [size, behead]
              --       * rewrite invm_set=>//=.
              --         by move:H3; rewrite supp_dexcepted.
              · exact SLCommon.Prefix.invm_set _ _ _ _ ‹¬Perm_m.dom _›
                  (EC.not_of_mem_support_dexcepted ‹a ∈ _›) ‹invm Perm_m mi› _ _
              --       * smt().
              · cases xs with
                | nil => exact absurd ‹([] : List block).isEmpty = false› (by simp)
                | cons a l => simp [size, behead]
            -- EC: auto; smt(size_ge0 size_eq0).
            · ec_auto
        -- EC: rcondt{1} 2; first by auto; inline*; auto; conseq(:_==> true); auto.
        stmt_rcondt{1} 2
        · intro σ₂
          hoare_call (: True ==> True) / SRO.Counter.c
          ec_auto
        -- EC: rcondt{2} 2; first by auto; inline*; auto; conseq(:_==> true); auto.
        stmt_rcondt{2} 2
        · intro σ₁
          hoare_call (: True ==> True) / SRO.Counter.c
          --     (the two sides' counters are equal, by the clone's `increase_counter`)
          ec_auto; ec_progress
          have e : SecureRO.Counter.c.get g = SecureRO.Counter.c.get σ₁.globals :=
            (‹SecureRO.Counter.c.get g = _›).trans (‹SecureRO.Counter.c.get σ₁.globals = _›).symm
          rw [e]
          exact ‹SRO.Counter.c.get σ₁.globals + _ + _ < _›
        -- EC: sim 3 3.
        stmt_wp
        -- EC: exists* m1{1}, m2{1}; elim* => a1 a2 c1 c2.
        equiv_exists* §m1{1}, §m2{1}, §Cntr.c{2}
        intro a1 a2 c2
        -- EC: call (equiv_sponge_perm (c2 + ((size a1 + 1) %/ r + 1) +
        --       max ((size_out + r - 1) %/ r - 1) 0) a2).
        equiv_call (equiv_sponge_perm
          (c2 + ((size a1 + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0) a2)
        -- EC: auto; call (equiv_sponge_perm c2 a1); auto; progress.
        ec_auto
        equiv_call (equiv_sponge_perm c2 a1)
        ec_auto; ec_progress
        -- EC: smt(List.size_ge0 divz_ge0 gt0_r).
        · exact le_of_lt ‹SecureRO.increase_counter Cntr_c₂ m1₂ < SecureRO.bound_counter›
        -- EC: smt(List.size_ge0 divz_ge0 gt0_r).
        · rw [‹Cntr.c.get g₂ = _›]
          exact le_of_lt ‹SecureRO.increase_counter Cntr_c₂ m1₂ + _ + _ < _›
      · ec_auto
    -- EC: call(: ={glob SRO.Counter, glob Perm, glob SRO.Bounder}
    --       /\ invm Perm.m{1} Perm.mi{1} /\ ={c}(SRO.Counter,Cntr)).
    equiv_call (_ : ={SRO.Counter.c, Perm.m, Perm.mi, SRO.Bounder.bounder} ∧
      invm §Perm.m{1} §Perm.mi{1} ∧ §SRO.Counter.c{1} = §Cntr.c{2})
    -- EC: + proc; sp; if; auto; sp; if; auto; sp.
    · equiv_proc; stmt_sp
      stmt_if
      · ec_close
      · stmt_sp
        stmt_if
        · ec_close
        · stmt_sp
          -- EC: exists * x{1}; elim* => m c1 c2 b1 b2.
          equiv_exists* §x{1}, §Cntr.c{2}
          intro m' c1
          -- EC: by call(equiv_sponge_perm c1 m); auto; smt().
          equiv_call (equiv_sponge_perm c1 m')
          ec_auto; ec_progress
          · exact le_of_lt ‹SecureRO.increase_counter _ _ < _›
          · exact (‹SRO.Counter.c.get g₁ = _›).trans (‹Cntr.c.get g₂ = _›).symm
        · ec_auto; ec_close
      · ec_auto
    -- EC: inline*; auto; progress.
    --     by rewrite /invm=> x y; rewrite 2!emptyE.
    --     (GAP 7: `D2Pre.m2` and `glob A` past the initializations' writes)
    ec_auto; ec_progress
    · have h := congrArg D2Pre.m2.get ‹Perm.m.set _ _ = _›
      simp_reads_all; exact h
    · have h := congrArg (FVP.fvP A).touched_getter.get ‹Perm.m.set _ _ = _›
      simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at h
      exact h
    · have h := congrArg D2Pre.m2.get ‹Perm.m.set _ _ = _›
      simp_reads_all; exact h
  -- EC: have->:Pr[Indiff0.Indif(RO, SimSetSize(Simulator, RO), D2Pre(A)).main() @ &m : res] =
  --       Pr[IdealIndif(BIRO.IRO, Simulator, DRestr(DSetSize(D2Pre(A)))).main() @ &m : res].
  have h2 : Pr[ Indiff0.GIdeal(RO, SimSetSize(Simulator), D2Pre(A)).main () @ &m : §res ] =
      Pr[ IdealIndif(IRO.asF, Simulator, DRestr(DSetSize(D2Pre(A)))).main () @ &m : §res ] := by
    -- EC: byequiv=>//=; proc.
    byequiv; equiv_proc
    --     (GAP 6: `SimSetSize(Simulator, RO).init` is `Simulator.init`)
    rw [SimSetSize_init_eq]
    repeat stmt_inline{1} 0
    repeat stmt_inline{2} 0
    stmt_sp; stmt_wp
    -- EC: seq 1 1 : (={m1, m2, glob SRO.Counter}
    --       /\ ={c}(SRO.Counter,Cntr)
    --       /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); last first.
    equiv_seq 1 1 : (={m1, m2, SRO.Counter.c} ∧ §SRO.Counter.c{1} = §Cntr.c{2} ∧
      same_ro §SRO.RO.m{1} §IRO.mp{2})
    swap
    -- EC: - if; auto; sp.
    · stmt_if
      · ec_close
      · stmt_sp
        -- EC: case: (SRO.Counter.c{1} + ((size m2{1} + 1) %/ r + 1) +
        --       max ((size_out + r - 1) %/ r - 1) 0 < limit); last first.
        equiv_case (§SRO.Counter.c{1} + ((size §m2{1} + 1) / r + 1) +
          max ((size_out + r - 1) / r - 1) 0 < GaudisCrypt.SHA3.SHA3Indiff.limit)
        swap
        -- EC: * rcondf{1} 2; first by auto; inline*; auto.
        · stmt_rcondf{1} 2
          · intro σ₂
            hoare_call (: True ==> True) / SRO.Counter.c
            ec_auto
          -- EC: rcondf{2} 2; first auto; inline*; auto; sp.
          --     + rcondt 1; 1:by auto=> |> &0 /#.
          --       by sp; rcondt 1; auto; conseq(:_==> true); auto.
          stmt_rcondf{2} 2
          · intro σ₁
            hoare_call (: True ==> True) / SRO.Counter.c
            ec_auto; ec_progress
            have e : SecureRO.Counter.c.get g = SecureRO.Counter.c.get σ₁.globals :=
              (‹SecureRO.Counter.c.get g = _›).trans (‹SecureRO.Counter.c.get σ₁.globals = _›).symm
            rw [e]
            exact ‹GaudisCrypt.SHA3.SHA3Indiff.limit ≤ _›
          -- EC: inline*;sp; auto.
          stmt_inline*; stmt_sp; stmt_wp
          -- EC: rcondt{2} 1; first by auto; smt().
          stmt_rcondt{2} 1
          · hoare_auto; ec_progress
            exact le_of_lt ‹SecureRO.increase_counter _ _ < SecureRO.bound_counter›
          -- EC: conseq(:_==> true); first smt(dout_ll).
          --     sp; rcondt{2} 1; auto; conseq(:_==> true); auto.
          stmt_sp
          stmt_rcondt{2} 1
          · hoare_auto
          -- EC: by while{2}(true)(n0{2}-i{2}); auto; 1:(sp; if; auto); smt(dbool_ll).
          stmt_wp
          equiv_while{2} True ((§n0{2} - §i{2}).toNat)
          · while_ll_phoare
            intro σ₁
            ec_auto
            intros; split_ifs
            · exact (is_lossless_iff_expected _).mp dbool_ll
            · rfl
          · intro σ₁ k
            hoare_auto
          · ec_auto; ec_progress
            exact (is_lossless_iff_expected _).mp GaudisCrypt.SHA3.SHA3Security.Params.dout_ll
        -- EC: rcondt{1} 2; first by auto; inline*; auto.
        stmt_rcondt{1} 2
        · intro σ₂
          hoare_call (: True ==> True) / SRO.Counter.c
          ec_auto
        -- EC: rcondt{2} 2; first auto; inline*; auto; sp.
        --     + rcondt 1; first by auto; smt().
        --       by sp; rcondt 1; auto; conseq(:_==> true); auto.
        stmt_rcondt{2} 2
        · intro σ₁
          hoare_call (: True ==> True) / SRO.Counter.c
          ec_auto; ec_progress
          have e : SecureRO.Counter.c.get g = SecureRO.Counter.c.get σ₁.globals :=
            (‹SecureRO.Counter.c.get g = _›).trans (‹SecureRO.Counter.c.get σ₁.globals = _›).symm
          rw [e]
          exact ‹SRO.Counter.c.get σ₁.globals + _ + _ < _›
        -- EC: sim 3 3.
        stmt_wp
        -- EC: exists* m1{1}, m2{1}; elim*=> a1 a2 c1 c2.
        equiv_exists* §m1{1}, §m2{1}, §Cntr.c{2}
        intro a1 a2 c2
        -- EC: call(equiv_ro_iro (c2 + ((size a1 + 1) %/ r + 1) +
        --       max ((size_out + r - 1) %/ r - 1) 0) a2).
        equiv_call (equiv_ro_iro
          (c2 + ((size a1 + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0) a2)
        -- EC: auto; call(equiv_ro_iro c2 a1); auto; smt().
        ec_auto
        equiv_call (equiv_ro_iro c2 a1)
        ec_auto; ec_progress
        · exact le_of_lt ‹SecureRO.increase_counter Cntr_c₂ m1₂ < SecureRO.bound_counter›
        · rw [‹Cntr.c.get g₂ = _›]
          exact le_of_lt ‹SecureRO.increase_counter Cntr_c₂ m1₂ + _ + _ < _›
      · ec_auto
    -- EC: call(: ={glob SRO.Counter, glob SRO.Bounder} /\ ={c}(SRO.Counter,Cntr)
    --       /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); auto.
    equiv_call (_ : ={SRO.Counter.c, SRO.Bounder.bounder} ∧ §SRO.Counter.c{1} = §Cntr.c{2} ∧
      same_ro §SRO.RO.m{1} §IRO.mp{2})
    -- EC: + proc; sp; if; auto; sp; if; auto; sp.
    · equiv_proc; stmt_sp
      stmt_if
      · ec_close
      · stmt_sp
        stmt_if
        · ec_close
        · -- EC: exists* x{1}; elim* => a c1 c2 b1 b2.
          equiv_exists* §x{1}, §Cntr.c{2}
          intro a c1
          -- EC: call(equiv_ro_iro c1 a); auto; smt().
          equiv_call (equiv_ro_iro c1 a)
          ec_auto; ec_progress
          · exact le_of_lt ‹SecureRO.increase_counter _ _ < _›
          · exact (‹SRO.Counter.c.get g₁ = _›).trans (‹Cntr.c.get g₂ = _›).symm
        · ec_auto; ec_close
      · ec_auto
    -- EC: smt(mem_empty).
    --     (GAP 7: `D2Pre.m2` and `glob A` past the initializations' writes)
    ec_auto; ec_progress
    · have h := congrArg D2Pre.m2.get ‹Simulator.m.set _ _ = _›
      simp_reads_all; exact h
    · have h := congrArg (FVP.fvP A).touched_getter.get ‹Simulator.m.set _ _ = _›
      simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at h
      exact h
    · have h := ‹(SRO.RO.m.get globals₁).dom m›
      rw [‹SRO.RO.m.get globals₁ = FMap.empty›] at h
      exact absurd h (FMap.mem_empty _)
    · have h := ‹(IRO.mp.get globals₂).dom _›
      rw [‹IRO.mp.get globals₂ = FMap.empty›] at h
      exact absurd h (FMap.mem_empty _)
    · have h := ‹(SRO.RO.m.get globals₁).dom m›
      rw [‹SRO.RO.m.get globals₁ = FMap.empty›] at h
      exact absurd h (FMap.mem_empty _)
    · have h := congrArg D2Pre.m2.get ‹Simulator.m.set _ _ = _›
      simp_reads_all; exact h
  rw [h1, h2]
  -- EC: have->//=:= SHA3Indiff (DSetSize(D2Pre(A))) &m _.
  refine @Pilot.SHA3Indiff.SHA3Indiff _ _ _ (DSetSize (D2Pre A)) ⟨by fp_finite, by fp_disjoint⟩
    (R ⊔ (SRO.Counter.c.footprint ⊔ (SRO.Bounder.bounder.footprint ⊔ D2Pre.m2.footprint)))
    inferInstance ⟨‹Footprint.Restricted R _›.finite.sup (by fp_finite), by fp_disjoint⟩ m ?_
  -- EC: move=> F P P_f_ll P_fi_ll F_ll; proc; inline*; auto; sp.
  intro F _ P _ P_f_ll P_fi_ll F_ll
  phoare_proc; phoare_inline*; stmt_sp; stmt_wp
  -- EC: seq 1 : true; auto.
  phoare_seq_lossless 1 : (True)
  -- EC: + call (A_ll (SRO.Bounder(FInit(DFSetSize(F)))) _); auto.
  · phoare_call (@A_ll _ ?_ ?_)
    · phoare_auto
    -- EC: by proc; inline*; sp; if; auto; sp; if; auto; sp; call F_ll; auto.
    · phoare_proc; phoare_inline*; stmt_sp; stmt_if
      · stmt_sp; stmt_if
        · phoare_auto; phoare_call F_ll; phoare_auto
        · phoare_auto
      · phoare_auto
  -- EC: if; auto; sp.
  · stmt_if
    · stmt_sp
      -- EC: seq 1 : true; auto.
      phoare_seq_lossless 1 : (True)
      -- EC: + by call F_ll; auto.
      · phoare_call F_ll; phoare_auto
      -- EC: sp; if; auto; sp; call F_ll; auto.
      · stmt_sp; stmt_if
        · phoare_auto; phoare_call F_ll; phoare_auto
        · phoare_auto
    · phoare_auto

end

end SecondPreimage

/-! ## Section `Collision` (EC l. 869–1239) -/

namespace Collision

open GaudisCrypt.SHA3.SLCommon.Prefix (invm)
open GaudisCrypt.SHA3.SHA3Security.Preimage (invm_dom_rng invmC' invmC useful)
-- EC proves the section's local `equiv_sponge_perm`, `equiv_ro_iro` again, word for word
open Preimage (equiv_sponge_perm equiv_ro_iro)

section

-- EC: declare module A <: SRO.AdvCollision {-SRO.RO.RO, -SRO.RO.FRO, -SRO.Bounder, -Perm,
--   -Gconcl_list.BIRO2.IRO, -Simulator, -Cntr, -BIRO.IRO, -F.RO, -F.FRO, -Redo, -C, -Gconcl.S,
--   -BlockSponge.BIRO.IRO, -BlockSponge.C, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
--   -Gconcl_list.Simulator}.
declare module A <: SRO.AdvCollision {-SRO.RO, -SRO.FRO, -SRO.Bounder, -Perm,
  -Gconcl_list.BIRO2.IRO, -Simulator, -Cntr, -IRO, -SLCommon.F.RO, -SLCommon.F.FRO,
  -SLCommon.Redo, -SLCommon.C, -Gconcl.S, -BlockSponge.BIRO.IRO, -BlockSponge.C,
  -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO, -Gconcl_list.Simulator,
  -Gconcl_list.SimLast,
  -Pilot.Sponge.HybridIRO.HybridIROLazy.mp, -Pilot.Sponge.HybridIRO.HybridIROEager.mp,
  -Pilot.Sponge.HybridIRO.ERO.RO.m, -Pilot.Sponge.HybridIRO.ERO.FRO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.RO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.FRO.m,
  -GaudisCrypt.SHA3.Handle.G1, -GaudisCrypt.SHA3.Gext.G2, -GaudisCrypt.SHA3.ConcreteF.PF,
  -GaudisCrypt.SHA3.Handle.FRO.m, -GaudisCrypt.SHA3.Handle.ROhandle.RO,
  -Pilot.Gext.ReSample.count, -Pilot.Gcol.Gcol.sample_c, -Pilot.ConcreteF.Switching.DBounder,
  -Pilot.ConcreteF.Switching.ARP, -Pilot.ConcreteF.Switching.PRPi.PRPi} with glob R

-- EC: declare axiom A_ll (F <: SRO.Oracle {-A}) : islossless F.get => islossless A(F).guess.
variable (A_ll : ∀ (F <: SRO.Oracle {-R}), islossless F.get → islossless A(F).guess)

include R A_ll

set_option maxHeartbeats 40000000 in
-- one declaration: EC's two `have`s, each a `byequiv` through the adversary's oracle
set_option synthInstance.maxHeartbeats 400000 in
-- EC's restriction checks by instance search (`A` against the modules of the lemmas applied)
set_option synthInstance.maxSize 1024 in
/-- EC's `lemma Sponge_coll_resistant &m :
Pr[SRO.Collision(A, FM(CSetSize(Sponge), Perm)).main() @ &m : res] <=
(limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r +
(sigma * (sigma - 1) + 2)%r / 2%r / (2%r ^ size_out)`. -/
theorem Sponge_coll_resistant (m : VariableAssignment) :
    Pr[ SRO.Collision(A, FM(CSetSize(Sponge), Perm)).main () @ &m : §res ] ≤
      ((GaudisCrypt.SHA3.SHA3Indiff.limit ^ 2 - GaudisCrypt.SHA3.SHA3Indiff.limit : ℤ) : ℝ) /
          ((2 ^ (r + c + 1).toNat : ℤ) : ℝ) +
        ((4 * GaudisCrypt.SHA3.SHA3Indiff.limit ^ 2 : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ) +
      ((sigma * (sigma - 1) + 2 : ℤ) : ℝ) / 2 / (2 : ℝ) ^ size_out := by
  -- EC: rewrite -(doutE1 witness).
  rw [div_eq_mul_inv (((sigma * (sigma - 1) + 2 : ℤ) : ℝ) / 2), ← doutE1 default]
  -- EC: rewrite (coll_resistant_if_indifferentiable A A_ll (CSetSize(Sponge)) Perm &m).
  refine S.coll_resistant_if_indifferentiable A (CSetSize Sponge) Perm m ?_
  -- EC: exists (SimSetSize(Simulator)); split.
  refine ⟨SimSetSize Simulator, inferInstance, ?_, ?_⟩
  -- EC: + by move=> F _; proc; inline*; auto.
  · intro F _
    rw [SimSetSize_init_eq]
    phoare_proc; phoare_inline*; phoare_auto
  -- EC: have->:Pr[Indiff0.Indif(CSetSize(Sponge, Perm), Perm, DColl(A)).main() @ &m : res] =
  --       Pr[RealIndif(Sponge, Perm, DRestr(DSetSize(DColl(A)))).main() @ &m : res].
  have h1 : Pr[ Indiff0.GReal(CSetSize(Sponge), Perm, DColl(A)).main () @ &m : §res ] =
      Pr[ RealIndif(Sponge, Perm, DRestr(DSetSize(DColl(A)))).main () @ &m : §res ] := by
    -- EC: byequiv=>//=; proc.
    byequiv; equiv_proc
    --     (GAP 6: `CSetSize(Sponge)` applied to `Perm` at the clone's module types)
    erw [CSetSize_Sponge_Perm_init _ _ rfl rfl, CSetSize_Sponge_Perm_f _ _ rfl rfl]
    repeat stmt_inline{1} 0
    repeat stmt_inline{2} 0
    stmt_sp; stmt_wp
    -- EC: seq 2 2 : (={m1, m2, glob SRO.Counter, glob Perm}
    --       /\ invm Perm.m{1} Perm.mi{1}
    --       /\ ={c}(SRO.Counter,Cntr)); last first.
    --     (EC's `(m1, m2) <@ A.guess()` is two statements, here one)
    equiv_seq 1 1 : (={m1, m2, SRO.Counter.c, Perm.m, Perm.mi} ∧ invm §Perm.m{1} §Perm.mi{1} ∧
      §SRO.Counter.c{1} = §Cntr.c{2})
    swap
    -- EC: - if; auto; sp.
    · stmt_if
      · ec_close
      · stmt_sp
        -- EC: case(SRO.Counter.c{1} + ((size m2{1} + 1) %/ r + 1) +
        --       max ((size_out + r - 1) %/ r - 1) 0 < limit); last first.
        equiv_case (§SRO.Counter.c{1} + ((size §m2{1} + 1) / r + 1) +
          max ((size_out + r - 1) / r - 1) 0 < GaudisCrypt.SHA3.SHA3Indiff.limit)
        swap
        -- EC: * rcondf{1} 2; 1: by auto; inline*; auto; conseq(: _ ==> true); auto.
        · stmt_rcondf{1} 2
          · intro σ₂
            hoare_call (: True ==> True) / SRO.Counter.c
            ec_auto
          -- EC: rcondf{2} 2; 1: by auto; inline*; auto; conseq(: _ ==> true); auto.
          stmt_rcondf{2} 2
          · intro σ₁
            hoare_call (: True ==> True) / SRO.Counter.c
            ec_auto; ec_progress
            have e : SecureRO.Counter.c.get g = SecureRO.Counter.c.get σ₁.globals :=
              (‹SecureRO.Counter.c.get g = _›).trans (‹SecureRO.Counter.c.get σ₁.globals = _›).symm
            rw [e]
            exact ‹GaudisCrypt.SHA3.SHA3Indiff.limit ≤ _›
          -- EC: auto; inline*; auto; sp; conseq(: _ ==> true); auto.
          stmt_wp
          --     (GAP 1: `Perm.f` behind the first port's view is opened first)
          simp only [Indifferentiability.PRIMITIVE.view, Perm, PRP.RP.RP, PRP.StrongPRP.PRP.mk]
          stmt_inline*
          stmt_sp
          equiv_conseq (: _ ==> True)
          · ec_close
          -- EC: if{2}; sp; auto; sim.
          stmt_if{2}
          --     (EC's `sim` through the two loops is the `while` rule on each)
          · stmt_sp; stmt_wp
            equiv_while (={i, sa, sc, Perm.m, Perm.mi} ∧ §n{1} = §n0{2})
            --     (GAP 2: the pair `x3` back from its components)
            · stmt_sp; stmt_if
              · ec_close
              · stmt_sp; stmt_if
                · ec_progress
                  have e : x3₁ = x4₂ := Prod.ext ‹x3₁.1 = x4₂.1› ‹x3₁.2 = x4₂.2›
                  simp [e]
                · ec_auto; ec_prep
                  have e : x3₁ = x4₂ := Prod.ext ‹x3₁.1 = x4₂.1› ‹x3₁.2 = x4₂.2›
                  subst e
                  exact fun a _ => ⟨rfl, rfl, rfl, rfl⟩
                · ec_auto; ec_prep
                  have e : x3₁ = x4₂ := Prod.ext ‹x3₁.1 = x4₂.1› ‹x3₁.2 = x4₂.2›
                  subst e
                  exact ⟨rfl, rfl⟩
              · ec_auto; ec_close
            equiv_while (={xs, sa, sc, i, Perm.m, Perm.mi} ∧ §n{1} = §n0{2})
            · stmt_sp; stmt_if
              · ec_close
              · ec_auto
              · ec_auto
            ec_auto; ec_close
          · stmt_wp
            -- EC: while{1}(invm Perm.m{1} Perm.mi{1}) (((size_out + r - 1) %/ r)-i{1}).
            equiv_while{1} (invm §Perm.m{1} §Perm.mi{1}) ((((§n{1} + r - 1) / r) - §i{1}).toNat)
            · while_ll_phoare
              -- EC: + auto; sp; if; auto.
              --       - sp; if ;auto; progress.
              --         * exact (useful _ _ _ H H2).
              intro σ₂
              ec_auto
              intro Perm_m mi i n sa sc hI
              split_ifs with h1 h2
              · exact (is_lossless_iff_expected _).mp (useful _ _ _ hI.1 (of_decide_eq_false h2))
              · rfl
              · rfl
            --         * rewrite invm_set=>//=.
            --           by move:H4; rewrite  supp_dexcepted.
            --         * smt().
            --         smt().
            --       smt().
            · intro σ₂ k
              hoare_auto; ec_progress
              exact SLCommon.Prefix.invm_set _ _ _ _ ‹¬Perm_m.dom (sa, sc)›
                (EC.not_of_mem_support_dexcepted ‹a ∈ _›) ‹invm Perm_m mi› _ _
            -- EC: conseq(:_==> invm Perm.m{1} Perm.mi{1}); 1:smt().
            equiv_conseq (: _ ==> invm §Perm.m{1} §Perm.mi{1})
            · ec_close
            -- EC: while{1}(invm Perm.m{1} Perm.mi{1})(size xs{1}).
            equiv_while{1} (invm §Perm.m{1} §Perm.mi{1}) ((size §xs{1}).toNat)
            · while_ll_phoare
              intro σ₂
              -- EC: + move=> _ z; auto; sp; if; auto; progress.
              --       * exact (useful _ _ _ H H1).
              ec_auto
              intros; split_ifs
              · exact (is_lossless_iff_expected _).mp
                  (useful _ _ _ (‹invm _ _ ∧ _›).1 (of_decide_eq_false ‹_›))
              · rfl
            · intro σ₂ k
              hoare_auto; ec_progress
              --       smt().
              · cases xs with
                | nil => exact absurd ‹([] : List block).isEmpty = false› (by simp)
                | cons a l => simp [size, behead]
              --       * rewrite invm_set=>//=.
              --         by move:H3; rewrite supp_dexcepted.
              · exact SLCommon.Prefix.invm_set _ _ _ _ ‹¬Perm_m.dom _›
                  (EC.not_of_mem_support_dexcepted ‹a ∈ _›) ‹invm Perm_m mi› _ _
              --       * smt().
              · cases xs with
                | nil => exact absurd ‹([] : List block).isEmpty = false› (by simp)
                | cons a l => simp [size, behead]
            -- EC: auto; smt(size_ge0 size_eq0).
            · ec_auto
        -- EC: rcondt{1} 2; first by auto; inline*; auto; conseq(:_==> true); auto.
        stmt_rcondt{1} 2
        · intro σ₂
          hoare_call (: True ==> True) / SRO.Counter.c
          ec_auto
        -- EC: rcondt{2} 2; first by auto; inline*; auto; conseq(:_==> true); auto.
        stmt_rcondt{2} 2
        · intro σ₁
          hoare_call (: True ==> True) / SRO.Counter.c
          --     (the two sides' counters are equal, by the clone's `increase_counter`)
          ec_auto; ec_progress
          have e : SecureRO.Counter.c.get g = SecureRO.Counter.c.get σ₁.globals :=
            (‹SecureRO.Counter.c.get g = _›).trans (‹SecureRO.Counter.c.get σ₁.globals = _›).symm
          rw [e]
          exact ‹SRO.Counter.c.get σ₁.globals + _ + _ < _›
        -- EC: sim 3 3.
        stmt_wp
        -- EC: exists* m1{1}, m2{1}; elim* => a1 a2 c1 c2.
        equiv_exists* §m1{1}, §m2{1}, §Cntr.c{2}
        intro a1 a2 c2
        -- EC: call (equiv_sponge_perm (c2 + ((size a1 + 1) %/ r + 1) +
        --       max ((size_out + r - 1) %/ r - 1) 0) a2).
        equiv_call (equiv_sponge_perm
          (c2 + ((size a1 + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0) a2)
        -- EC: auto; call (equiv_sponge_perm c2 a1); auto; progress.
        ec_auto
        equiv_call (equiv_sponge_perm c2 a1)
        ec_auto; ec_progress
        -- EC: smt(List.size_ge0 divz_ge0 gt0_r).
        · exact le_of_lt ‹SecureRO.increase_counter Cntr_c₂ m1₂ < SecureRO.bound_counter›
        -- EC: smt(List.size_ge0 divz_ge0 gt0_r).
        · rw [‹Cntr.c.get g₂ = _›]
          exact le_of_lt ‹SecureRO.increase_counter Cntr_c₂ m1₂ + _ + _ < _›
      · ec_auto
    -- EC: call(: ={glob SRO.Counter, glob Perm, glob SRO.Bounder}
    --       /\ invm Perm.m{1} Perm.mi{1} /\ ={c}(SRO.Counter,Cntr)).
    equiv_call (_ : ={SRO.Counter.c, Perm.m, Perm.mi, SRO.Bounder.bounder} ∧
      invm §Perm.m{1} §Perm.mi{1} ∧ §SRO.Counter.c{1} = §Cntr.c{2})
    -- EC: + proc; sp; if; auto; sp; if; auto; sp.
    · equiv_proc; stmt_sp
      stmt_if
      · ec_close
      · stmt_sp
        stmt_if
        · ec_close
        · stmt_sp
          -- EC: exists * x{1}; elim* => m c1 c2 b1 b2.
          equiv_exists* §x{1}, §Cntr.c{2}
          intro m' c1
          -- EC: by call(equiv_sponge_perm c1 m); auto; smt().
          equiv_call (equiv_sponge_perm c1 m')
          ec_auto; ec_progress
          · exact le_of_lt ‹SecureRO.increase_counter _ _ < _›
          · exact (‹SRO.Counter.c.get g₁ = _›).trans (‹Cntr.c.get g₂ = _›).symm
        · ec_auto; ec_close
      · ec_auto
    -- EC: inline*; auto; progress.
    --     by rewrite /invm=> x y; rewrite 2!emptyE.
    --     (GAP 7: `glob A` past the initializations' writes)
    ec_auto; ec_progress
    have h := congrArg (FVP.fvP A).touched_getter.get ‹Perm.m.set _ _ = _›
    simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at h
    exact h
  -- EC: have->:Pr[Indiff0.Indif(RO, SimSetSize(Simulator, RO), DColl(A)).main() @ &m : res] =
  --       Pr[IdealIndif(BIRO.IRO, Simulator, DRestr(DSetSize(DColl(A)))).main() @ &m : res].
  have h2 : Pr[ Indiff0.GIdeal(RO, SimSetSize(Simulator), DColl(A)).main () @ &m : §res ] =
      Pr[ IdealIndif(IRO.asF, Simulator, DRestr(DSetSize(DColl(A)))).main () @ &m : §res ] := by
    -- EC: byequiv=>//=; proc.
    byequiv; equiv_proc
    --     (GAP 6: `SimSetSize(Simulator, RO).init` is `Simulator.init`)
    rw [SimSetSize_init_eq]
    repeat stmt_inline{1} 0
    repeat stmt_inline{2} 0
    stmt_sp; stmt_wp
    -- EC: seq 1 1 : (={m1, m2, glob SRO.Counter}
    --       /\ ={c}(SRO.Counter,Cntr)
    --       /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); last first.
    equiv_seq 1 1 : (={m1, m2, SRO.Counter.c} ∧ §SRO.Counter.c{1} = §Cntr.c{2} ∧
      same_ro §SRO.RO.m{1} §IRO.mp{2})
    swap
    -- EC: - if; auto; sp.
    · stmt_if
      · ec_close
      · stmt_sp
        -- EC: case: (SRO.Counter.c{1} + ((size m2{1} + 1) %/ r + 1) +
        --       max ((size_out + r - 1) %/ r - 1) 0 < limit); last first.
        equiv_case (§SRO.Counter.c{1} + ((size §m2{1} + 1) / r + 1) +
          max ((size_out + r - 1) / r - 1) 0 < GaudisCrypt.SHA3.SHA3Indiff.limit)
        swap
        -- EC: * rcondf{1} 2; first by auto; inline*; auto.
        · stmt_rcondf{1} 2
          · intro σ₂
            hoare_call (: True ==> True) / SRO.Counter.c
            ec_auto
          -- EC: rcondf{2} 2; first auto; inline*; auto; sp.
          --     + rcondt 1; 1:by auto=> |> &0 /#.
          --       by sp; rcondt 1; auto; conseq(:_==> true); auto.
          stmt_rcondf{2} 2
          · intro σ₁
            hoare_call (: True ==> True) / SRO.Counter.c
            ec_auto; ec_progress
            have e : SecureRO.Counter.c.get g = SecureRO.Counter.c.get σ₁.globals :=
              (‹SecureRO.Counter.c.get g = _›).trans (‹SecureRO.Counter.c.get σ₁.globals = _›).symm
            rw [e]
            exact ‹GaudisCrypt.SHA3.SHA3Indiff.limit ≤ _›
          -- EC: inline*;sp; auto.
          stmt_inline*; stmt_sp; stmt_wp
          -- EC: rcondt{2} 1; 1:by auto=> |> &0 /#.
          stmt_rcondt{2} 1
          · hoare_auto; ec_progress
            exact le_of_lt ‹SecureRO.increase_counter _ _ < SecureRO.bound_counter›
          -- EC: conseq(:_==> true); first smt(dout_ll).
          --     sp; rcondt{2} 1; auto; conseq(:_==> true); auto.
          stmt_sp
          stmt_rcondt{2} 1
          · hoare_auto
          -- EC: by while{2}(true)(n0{2}-i{2}); auto; 1:(sp; if; auto); smt(dbool_ll).
          stmt_wp
          equiv_while{2} True ((§n0{2} - §i{2}).toNat)
          · while_ll_phoare
            intro σ₁
            ec_auto
            intros; split_ifs
            · exact (is_lossless_iff_expected _).mp dbool_ll
            · rfl
          · intro σ₁ k
            hoare_auto
          · ec_auto; ec_progress
            exact (is_lossless_iff_expected _).mp GaudisCrypt.SHA3.SHA3Security.Params.dout_ll
        -- EC: rcondt{1} 2; first by auto; inline*; auto.
        stmt_rcondt{1} 2
        · intro σ₂
          hoare_call (: True ==> True) / SRO.Counter.c
          ec_auto
        -- EC: rcondt{2} 2; first auto; inline*; auto; sp.
        --     + rcondt 1; 1:by auto=> |> &0 /#.
        --       by sp; rcondt 1; auto; conseq(:_==> true); auto.
        stmt_rcondt{2} 2
        · intro σ₁
          hoare_call (: True ==> True) / SRO.Counter.c
          ec_auto; ec_progress
          have e : SecureRO.Counter.c.get g = SecureRO.Counter.c.get σ₁.globals :=
            (‹SecureRO.Counter.c.get g = _›).trans (‹SecureRO.Counter.c.get σ₁.globals = _›).symm
          rw [e]
          exact ‹SRO.Counter.c.get σ₁.globals + _ + _ < _›
        -- EC: sim 3 3.
        stmt_wp
        -- EC: exists* m1{1}, m2{1}; elim*=> a1 a2 c1 c2.
        equiv_exists* §m1{1}, §m2{1}, §Cntr.c{2}
        intro a1 a2 c2
        -- EC: call(equiv_ro_iro (c2 + ((size a1 + 1) %/ r + 1) +
        --       max ((size_out + r - 1) %/ r - 1) 0) a2).
        equiv_call (equiv_ro_iro
          (c2 + ((size a1 + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0) a2)
        -- EC: auto; call(equiv_ro_iro c2 a1); auto; smt().
        ec_auto
        equiv_call (equiv_ro_iro c2 a1)
        ec_auto; ec_progress
        · exact le_of_lt ‹SecureRO.increase_counter Cntr_c₂ m1₂ < SecureRO.bound_counter›
        · rw [‹Cntr.c.get g₂ = _›]
          exact le_of_lt ‹SecureRO.increase_counter Cntr_c₂ m1₂ + _ + _ < _›
      · ec_auto
    -- EC: call(: ={glob SRO.Counter, glob SRO.Bounder} /\ ={c}(SRO.Counter,Cntr)
    --       /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); auto.
    equiv_call (_ : ={SRO.Counter.c, SRO.Bounder.bounder} ∧ §SRO.Counter.c{1} = §Cntr.c{2} ∧
      same_ro §SRO.RO.m{1} §IRO.mp{2})
    -- EC: + proc; sp; if; auto; sp; if; auto; sp.
    · equiv_proc; stmt_sp
      stmt_if
      · ec_close
      · stmt_sp
        stmt_if
        · ec_close
        · -- EC: exists* x{1}; elim* => a c1 c2 b1 b2.
          equiv_exists* §x{1}, §Cntr.c{2}
          intro a c1
          -- EC: call(equiv_ro_iro c1 a); auto; smt().
          equiv_call (equiv_ro_iro c1 a)
          ec_auto; ec_progress
          · exact le_of_lt ‹SecureRO.increase_counter _ _ < _›
          · exact (‹SRO.Counter.c.get g₁ = _›).trans (‹Cntr.c.get g₂ = _›).symm
        · ec_auto; ec_close
      · ec_auto
    -- EC: smt(mem_empty).
    --     (GAP 7: `glob A` past the initializations' writes)
    ec_auto; ec_progress
    · have h := congrArg (FVP.fvP A).touched_getter.get ‹Simulator.m.set _ _ = _›
      simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at h
      exact h
    · have h := ‹(SRO.RO.m.get globals₁).dom m›
      rw [‹SRO.RO.m.get globals₁ = FMap.empty›] at h
      exact absurd h (FMap.mem_empty _)
    · have h := ‹(IRO.mp.get globals₂).dom _›
      rw [‹IRO.mp.get globals₂ = FMap.empty›] at h
      exact absurd h (FMap.mem_empty _)
    · have h := ‹(SRO.RO.m.get globals₁).dom m›
      rw [‹SRO.RO.m.get globals₁ = FMap.empty›] at h
      exact absurd h (FMap.mem_empty _)
  rw [h1, h2]
  -- EC: have->//=:= SHA3Indiff (DSetSize(DColl(A))) &m _.
  refine @Pilot.SHA3Indiff.SHA3Indiff _ _ _ (DSetSize (DColl A)) ⟨by fp_finite, by fp_disjoint⟩
    (R ⊔ (SRO.Counter.c.footprint ⊔ SRO.Bounder.bounder.footprint))
    inferInstance ⟨‹Footprint.Restricted R _›.finite.sup (by fp_finite), by fp_disjoint⟩ m ?_
  -- EC: move=> F P P_f_ll P_fi_ll F_ll; proc; inline*; auto; sp.
  intro F _ P _ P_f_ll P_fi_ll F_ll
  phoare_proc; phoare_inline*; stmt_sp; stmt_wp
  -- EC: seq 1 : true; auto.
  phoare_seq_lossless 1 : (True)
  -- EC: + call (A_ll (SRO.Bounder(FInit(DFSetSize(F)))) _); auto.
  · phoare_call (@A_ll _ ?_ ?_)
    · phoare_auto
    -- EC: by proc; inline*; sp; if; auto; sp; if; auto; sp; call F_ll; auto.
    · phoare_proc; phoare_inline*; stmt_sp; stmt_if
      · stmt_sp; stmt_if
        · phoare_auto; phoare_call F_ll; phoare_auto
        · phoare_auto
      · phoare_auto
  -- EC: if; auto; sp.
  · stmt_if
    · stmt_sp
      -- EC: seq 1 : true; auto.
      phoare_seq_lossless 1 : (True)
      -- EC: + by call F_ll; auto.
      · phoare_call F_ll; phoare_auto
      -- EC: sp; if; auto; sp; call F_ll; auto.
      · stmt_sp; stmt_if
        · phoare_auto; phoare_call F_ll; phoare_auto
        · phoare_auto
    · phoare_auto

end

end Collision

/-! ## The modules `X`, `AdvCollisionSHA3`, and section `SHA3_Collision` (EC l. 1241–1274) -/

-- EC's `module X (F : SRO.Oracle)`
module X using (F : SRO.Oracle) : SRO.Oracle {
  proc get (bl : List Bool) : f_out {
    var r : f_out;
    r <- call F.get ($bl ++ [false, true]);
    return $r
  };
}

-- EC's `module AdvCollisionSHA3 (A : SRO.AdvCollision) (F : SRO.Oracle)`, with `A` a Lean
-- parameter so that `AdvCollisionSHA3 A` is an `SRO.AdvCollision`
set_option linter.gaudisCrypt.using false in
module AdvCollisionSHA3 (A : SRO.AdvCollision) using (F : SRO.Oracle) {
  proc guess () : (List Bool × List Bool) {
    var m1 : List Bool, m2 : List Bool;
    m1, m2 <- call A(X(F)).guess ();
    return ($m1 ++ [false, true], $m2 ++ [false, true])
  };
}

/-- `AdvCollisionSHA3(A)` touches `A`'s variables only (EC reads the globals off the code). -/
@[fp_bound] theorem fvP_AdvCollisionSHA3 (A : SRO.AdvCollision) :
    FVP.fvP (AdvCollisionSHA3 A) ≤ FVP.fvP A := by
  (fp_module)

/-- EC's `glob AdvCollisionSHA3(A)`: `glob A`. -/
instance instECGlobAdvCollisionSHA3 (A : SRO.AdvCollision) {R : Footprint VariableAssignment}
    [h : Module.ECGlob A R] : Module.ECGlob (AdvCollisionSHA3 A) R :=
  ⟨h.finite.mono (fvP_AdvCollisionSHA3 A), (fvP_AdvCollisionSHA3 A).trans h.le, h.base⟩

namespace SHA3_Collision

section

-- EC: declare module A <: SRO.AdvCollision {-SRO.RO.RO, -SRO.RO.FRO, -SRO.Bounder, -Perm,
--   -Gconcl_list.BIRO2.IRO, -Simulator, -Cntr, -BIRO.IRO, -F.RO, -F.FRO, -Redo, -C, -Gconcl.S,
--   -BlockSponge.BIRO.IRO, -BlockSponge.C, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
--   -Gconcl_list.Simulator}.
declare module A <: SRO.AdvCollision {-SRO.RO, -SRO.FRO, -SRO.Bounder, -Perm,
  -Gconcl_list.BIRO2.IRO, -Simulator, -Cntr, -IRO, -SLCommon.F.RO, -SLCommon.F.FRO,
  -SLCommon.Redo, -SLCommon.C, -Gconcl.S, -BlockSponge.BIRO.IRO, -BlockSponge.C,
  -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO, -Gconcl_list.Simulator,
  -Gconcl_list.SimLast,
  -Pilot.Sponge.HybridIRO.HybridIROLazy.mp, -Pilot.Sponge.HybridIRO.HybridIROEager.mp,
  -Pilot.Sponge.HybridIRO.ERO.RO.m, -Pilot.Sponge.HybridIRO.ERO.FRO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.RO.m,
  -Pilot.Gconcl_list.Simplify_Simulator.IRO2.FRO.m,
  -GaudisCrypt.SHA3.Handle.G1, -GaudisCrypt.SHA3.Gext.G2, -GaudisCrypt.SHA3.ConcreteF.PF,
  -GaudisCrypt.SHA3.Handle.FRO.m, -GaudisCrypt.SHA3.Handle.ROhandle.RO,
  -Pilot.Gext.ReSample.count, -Pilot.Gcol.Gcol.sample_c, -Pilot.ConcreteF.Switching.DBounder,
  -Pilot.ConcreteF.Switching.ARP, -Pilot.ConcreteF.Switching.PRPi.PRPi} with glob R

-- EC: declare axiom A_ll (F <: SRO.Oracle {-A}) : islossless F.get => islossless A(F).guess.
variable (A_ll : ∀ (F <: SRO.Oracle {-R}), islossless F.get → islossless A(F).guess)

include R A_ll

set_option synthInstance.maxHeartbeats 400000 in
-- EC's restriction checks by instance search (`AdvCollisionSHA3(A)` against the modules of
-- `Sponge_coll_resistant`)
set_option synthInstance.maxSize 1024 in
/-- EC's `lemma SHA3_coll_resistant &m :
Pr[SRO.Collision(AdvCollisionSHA3(A), FM(CSetSize(Sponge), Perm)).main() @ &m : res] <=
(limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r +
(sigma * (sigma - 1) + 2)%r / 2%r / (2%r ^ size_out)`. -/
theorem SHA3_coll_resistant (m : VariableAssignment) :
    Pr[ SRO.Collision(AdvCollisionSHA3(A), FM(CSetSize(Sponge), Perm)).main () @ &m : §res ] ≤
      ((GaudisCrypt.SHA3.SHA3Indiff.limit ^ 2 - GaudisCrypt.SHA3.SHA3Indiff.limit : ℤ) : ℝ) /
          ((2 ^ (r + c + 1).toNat : ℤ) : ℝ) +
        ((4 * GaudisCrypt.SHA3.SHA3Indiff.limit ^ 2 : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ) +
      ((sigma * (sigma - 1) + 2 : ℤ) : ℝ) / 2 / (2 : ℝ) ^ size_out := by
  -- EC: apply (Sponge_coll_resistant (AdvCollisionSHA3(A)) _ &m).
  refine @Collision.Sponge_coll_resistant _ _ _ _ (AdvCollisionSHA3 A)
    ⟨by fp_finite, by fp_disjoint⟩ R inferInstance inferInstance ?_ m
  -- EC: by move=> F F_ll; proc; inline*; call(A_ll (X(F)) _); auto; proc; call F_ll; auto.
  intro F _ F_ll
  phoare_proc
  phoare_call (@A_ll _ ?_ ?_)
  · phoare_auto
  · phoare_proc; phoare_call F_ll; phoare_auto

end

end SHA3_Collision

end GaudisCrypt.SHA3.Pilot.SHA3Security
