import GaudisCrypt.Examples.SHA3.Pilot.IndifRO_is_secure
import GaudisCrypt.Examples.SHA3.Pilot.SHA3Indiff
import GaudisCrypt.Examples.SHA3.SHA3Security

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

/-!
# Top-level proof of SHA-3 security (EasyCrypt `proof/SHA3Security.ec`) — EC-fidelity port, in
progress

Ported so far: the file's modules, the clone `S` of `IndifRO_is_secure`, and, of section
`Preimage`, `equiv_sponge_perm` (EC l. 168) and `equiv_ro_iro` (EC l. 213).

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
  first port's (`SHA3Security.Preimage.*`).
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
  `inline FC(Sponge(Perm)).f` does not elaborate over the first port's views: by index.
* GAP 4: the exit goal of a one-sided `while` does not frame a variable of the other side that
  only the invariant reads: the conjunct is added to the invariant (GAP 7 of `Pilot/Sponge.lean`).
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

/-! ## Section `Preimage` (EC l. 125–475), in progress -/

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

end Preimage

end GaudisCrypt.SHA3.Pilot.SHA3Security
