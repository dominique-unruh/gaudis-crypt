import GaudisCrypt.Examples.SHA3.Pilot.IndifRO_is_secure
import GaudisCrypt.Examples.SHA3.Pilot.SHA3Indiff
import GaudisCrypt.Examples.SHA3.SHA3Security

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

/-!
# Top-level proof of SHA-3 security (EasyCrypt `proof/SHA3Security.ec`) — EC-fidelity port, in
progress

Ported so far: the file's modules, the clone `S` of `IndifRO_is_secure`, and, of section
`Preimage`, `equiv_sponge_perm` (EC l. 168).

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

Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* GAP 1: `Perm.f` behind the first port's views is not opened by `inline*`: unfolded first
  (`simp only [PRIMITIVE.view, Perm, …]`).
* GAP 2: the closers split `={sa, sc}` at `x <- (sa, sc)` into components; the pair's equation is
  put back by hand before the leaf is closed (as in `Pilot/SHA3_OIndiff.lean`).
* GAP 3: `FInit(F).get` is `F.f` in EC (an alias); here a call (E5), inlined first.  EC's path
  `inline FC(Sponge(Perm)).f` does not elaborate over the first port's views: by index.
-/

-- the clone `S.SRO` contains a module named like its theory; kept (exception E1)
set_option linter.dupNamespace false
-- the `module` command's lemmas do not use every parameter class
set_option linter.unusedSectionVars false

namespace GaudisCrypt.SHA3.Pilot.SHA3Security

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.Sponge
open GaudisCrypt.SHA3.Sponge.BIRO
open GaudisCrypt.SHA3.SHA3Indiff (Simulator Cntr FC PC DRestr)
open GaudisCrypt.SHA3.SHA3Security (size_out sigma f_out dout to_list of_list doutE1)

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

end Preimage

end GaudisCrypt.SHA3.Pilot.SHA3Security
