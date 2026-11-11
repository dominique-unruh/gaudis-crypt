import GaudisCrypt.Examples.SHA3.SmartCounter.SLCommon
import GaudisCrypt.Examples.SHA3.Pilot.Indifferentiability
import GaudisCrypt.Syntax.Clone
import GaudisCrypt.Syntax.ModuleSubtype
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECCallUpto
import GaudisCrypt.Logic.ECInline
import GaudisCrypt.Logic.ECSeq
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.CallSpec
import GaudisCrypt.Logic.ECCallFrame
import GaudisCrypt.Logic.ECClose

/-!
# The squeezeless sponge: common definitions (EasyCrypt `proof/smart_counter/SLCommon.ec`) —
EC-fidelity port

The construction `SqueezelessSponge`, the counting and restricting wrappers `C`, `PC`, `DPRestr`,
`FC`, `DFRestr`, `DRestr`, and their lemmas.  The operators without modules (the parameter class
with `max_size`, `state`, the `Prefix` theory, the handle operators) are
`SmartCounter/SLCommonCore.lean`, shared with the first port.

Translation (as the pilots' `IndifRO_is_secure`):
* `clone include Indifferentiability with type p <- state, … rename [module] "GReal" as
  "RealIndif" [module] "GIdeal" as "IdealIndif"` is `clone import … as Indiff` (`clone` has no
  `include` and no `rename`), `RealIndif` and `IdealIndif` aliases of `GReal`, `GIdeal`;
* `clone import FullRO as F with …` is the namespace `F` of `PROM.FullRO` at the clone's types,
  its module variables `global_var`s;
* the procedure aliases of `PRestr`, `FRestr` (`proc f = DPRestr(P).f`) are wrapped in a call
  (exception E5);
* `DRestr(D, F, P)` takes `D` as a Lean parameter: `DRestr(D)` is EC's partial application.
-/

namespace GaudisCrypt.SHA3.Pilot.SLCommon

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM
open GaudisCrypt.SHA3.Common hiding PRIMITIVE
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix

variable [SLCommon.Params]

/-- EC's `type state = block * capacity` (`SLCommonCore`'s, named here: a root `state` exists). -/
abbrev state := GaudisCrypt.SHA3.SLCommon.state

/-! The clone's module types, variables and modules are the first port's
(`SmartCounter/SLCommon.lean`): one declaration per EC variable, shared with the pilots of
`Handle`, `Gcol`, `Gext`, `Gconcl`.  EC's subtyping of its module types, as `Pilot/Indifferentiability`
declares it. -/

module_subtype PRIMITIVE <: DPRIMITIVE

module_subtype FUNCTIONALITY <: DFUNCTIONALITY

module PRestr using (P : PRIMITIVE) : PRIMITIVE {
  proc init () : Unit {
    _ <- call C.init ();
    _ <- call P.init ();
    return ()
  };
  proc f (x : state) : state {
    var y : state;
    y <- call DPRestr(P).f ($x);
    return $y
  };
  proc fi (x : state) : state {
    var y : state;
    y <- call DPRestr(P).fi ($x);
    return $y
  };
}

module FRestr using (F : FUNCTIONALITY) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call Redo.init ();
    _ <- call F.init ();
    return ()
  };
  proc f (bs : List block) : block {
    var b : block;
    b <- call DFRestr(F).f ($bs);
    return $b
  };
}

/-- EC's `lemma rp_ll (P <: DPRIMITIVE{-C}): islossless P.f => islossless DPRestr(P).f`. -/
theorem rp_ll : ∀ (P <: DPRIMITIVE {-C}), islossless P.f → islossless DPRestr(P).f := by
  intro P _ Hll; phoare_proc; stmt_sp; stmt_if
  · phoare_auto; phoare_call Hll; phoare_auto
  · phoare_auto

/-- EC's `lemma rpi_ll (P <: DPRIMITIVE{-C}): islossless P.fi => islossless DPRestr(P).fi`. -/
theorem rpi_ll : ∀ (P <: DPRIMITIVE {-C}), islossless P.fi → islossless DPRestr(P).fi := by
  intro P _ Hll; phoare_proc; stmt_sp; stmt_if
  · phoare_auto; phoare_call Hll; phoare_auto
  · phoare_auto

/-- EC's `lemma rf_ll (F <: DFUNCTIONALITY{-C}): islossless F.f => islossless DFRestr(F).f`. -/
theorem rf_ll : ∀ (F <: DFUNCTIONALITY {-C}), islossless F.f → islossless DFRestr(F).f := by
  intro F _ Hll; phoare_proc; stmt_sp; stmt_if
  · stmt_if
    · phoare_auto; phoare_call Hll; phoare_auto
    · phoare_auto
  · phoare_auto

/-- EC's `lemma DRestr_ll (D <: DISTINGUISHER{-C}): (forall (F <: DFUNCTIONALITY{-D})
(P <: DPRIMITIVE{-D}), islossless P.f => islossless P.fi => islossless F.f =>
islossless D(F,P).distinguish) => forall (F <: DFUNCTIONALITY{-DRestr(D)})
(P <: DPRIMITIVE{-DRestr(D)}), islossless P.f => islossless P.fi => islossless F.f =>
islossless DRestr(D, F, P).distinguish`; `{-DRestr(D)}` is `{-D, -C}`, its globals. -/
theorem DRestr_ll : ∀ (D <: DISTINGUISHER {-C}),
    (∀ (F <: DFUNCTIONALITY {-D}), ∀ (P <: DPRIMITIVE {-D}),
      islossless P.f → islossless P.fi → islossless F.f → islossless D(F, P).distinguish) →
    ∀ (F <: DFUNCTIONALITY {-D, -C}), ∀ (P <: DPRIMITIVE {-D, -C}),
      islossless P.f → islossless P.fi → islossless F.f →
        islossless DRestr(D, F, P).distinguish := by
  intro D _ D_ll F _ P _ p_ll pi_ll f_ll
  phoare_proc
  phoare_call (@D_ll (Module.app DFRestr F) ⟨by fp_finite, by fp_disjoint⟩
    (Module.app DPRestr P) ⟨by fp_finite, by fp_disjoint⟩ (rp_ll P p_ll) (rpi_ll P pi_ll)
    (rf_ll F f_ll))
  phoare_inline*; phoare_auto

/-! ### Section `RESTR` -/

section RESTR

declare module F <: FUNCTIONALITY {-C, -Redo}
declare module P <: PRIMITIVE {-C, -F, -Redo}
declare module D <: DISTINGUISHER {-F, -P, -C, -Redo}

set_option maxHeartbeats 500000 in
-- one declaration: the distinguisher's call over three oracles, each by `sim`
/-- EC's `lemma swap_restr &m: Pr[Indif(FRestr(F), PRestr(P), D).main() @ &m: res] =
Pr[Indif(F,P,DRestr(D)).main() @ &m: res]`. -/
theorem swap_restr (m : VariableAssignment) :
    Pr[ Indif(FRestr(F), PRestr(P), D).main () @ &m : §res ] =
      Pr[ Indif(F, P, DRestr(D)).main () @ &m : §res ] := by
  byequiv; equiv_proc; stmt_inline*; stmt_wp
  stmt_swap{1} [1..2] 3
  equiv_call (_ : ={glob D, glob F, glob P, C.c, C.queries})
  · equiv_proc; stmt_inline*; sim
  · equiv_proc; stmt_inline*; sim
  · equiv_proc; stmt_inline*; sim
  · stmt_swap{1} [2..2] 3
    sim

end RESTR

/-! ### Section `COUNT` -/

section COUNT

declare module P <: PRIMITIVE {-C}
declare module CO <: CONSTRUCTION {-C, -P}
declare module D <: DISTINGUISHER {-C, -P, -CO}

-- EC's `declare axiom`s
variable (f_ll : islossless P.f) (fi_ll : islossless P.fi) (CO_ll : islossless CO(P).f)
variable (D_ll : ∀ (F <: DFUNCTIONALITY {-D}), ∀ (P <: DPRIMITIVE {-D}),
  islossless P.f → islossless P.fi → islossless F.f → islossless D(F, P).distinguish)

set_option maxHeartbeats 1000000 in
-- one declaration: EC's up-to-bad call over three oracles, with their thirteen goals
include f_ll fi_ll CO_ll D_ll in
/-- EC's `lemma Pr_restr &m : Pr[Indif(FC(CO(P)), PC(P), D).main()@ &m:res /\ C.c <= max_size] <=
Pr[Indif(CO(P), P, DRestr(D)).main()@ &m:res]`.

EC's proof, step for step: `byequiv (_: ={glob D, glob P, glob CO} ==> …); symmetry; proc;
inline *; wp; call (_: max_size < C.c, ={glob P, glob CO, glob C})`, then per oracle its
equivalence (`proc; sp; if{1}`, the call kept by `sim`, EC's `call (_: true)`; `call{2} f_ll`
past the bad event), the left oracle's losslessness and the right one's `phoare` (`call f_ll`
keeping `C.c`, `phoare_call f_ll / C.c`); EC's `auto => /#` is `auto_close`, its
`smt(prefix_sizel)` the instance of `prefix_sizel` and `auto_close`.  Deviation: the right
oracles' `islossless` (exception E11). -/
theorem Pr_restr (m : VariableAssignment) :
    Pr[ Indif(FC(CO(P)), PC(P), D).main () @ &m : §res ∧ §C.c ≤ max_size ] ≤
      Pr[ Indif(CO(P), P, DRestr(D)).main () @ &m : §res ] := by
  byequiv (_ : ={glob D, glob P, glob CO} ==> §C.c{1} ≤ max_size → ={res})
  · equiv_sym; equiv_proc; stmt_inline*; stmt_wp
    equiv_call (_ : max_size < §C.c, ={glob P, glob CO, glob C})
    · exact D_ll
    -- `P.f`
    · equiv_proc; stmt_sp; equiv_if{1}
      · sim; auto_close
      · stmt_wp; equiv_call{2} f_ll / C.c; equiv_skip; auto_close
    · phoare_proc; stmt_sp; stmt_if
      · phoare_auto; phoare_call f_ll; phoare_auto
      · phoare_auto
    · phoare_proc; stmt_wp; phoare_call f_ll / C.c; phoare_auto; auto_close
    · phoare_proc; stmt_wp; phoare_call f_ll; phoare_auto
    -- `P.fi`
    · equiv_proc; stmt_sp; equiv_if{1}
      · sim; auto_close
      · stmt_wp; equiv_call{2} fi_ll / C.c; equiv_skip; auto_close
    · phoare_proc; stmt_sp; stmt_if
      · phoare_auto; phoare_call fi_ll; phoare_auto
      · phoare_auto
    · phoare_proc; stmt_wp; phoare_call fi_ll / C.c; phoare_auto; auto_close
    · phoare_proc; stmt_wp; phoare_call fi_ll; phoare_auto
    -- `CO(P).f`
    · equiv_proc; stmt_sp; equiv_if
      · equiv_if{1}
        · sim; auto_close
        · stmt_wp; equiv_call{2} CO_ll / C.c; stmt_wp; equiv_skip; auto_close
      · equiv_auto
      · auto_close
    · phoare_proc; stmt_sp; stmt_if
      · stmt_if
        · phoare_auto; phoare_call CO_ll; phoare_auto
        · phoare_auto
      · phoare_auto
    · phoare_proc; stmt_sp; stmt_if
      · stmt_wp; phoare_call CO_ll / C.c; phoare_auto
        intro _ _ q bs
        have := prefix_sizel bs (get_max_prefix bs (elems q.fdom))
        auto_close
      · phoare_auto; auto_close
    · phoare_proc; stmt_sp; stmt_if
      · phoare_auto; phoare_call CO_ll; phoare_auto
      · phoare_auto
    · sim; have := max_ge0; auto_close
  · auto_close

end COUNT

/-- `module GReal(D : DISTINGUISHER) = RealIndif(SqueezelessSponge, PC(Perm), D)`, `Perm` the
`PRIMITIVE` of `Common`'s permutation (EC's clone of `RP` at `block * capacity`). -/

module_subtype (EC.PRP.StrongPRP.PRP (block × capacity)) <: GaudisCrypt.SHA3.SLCommon.PRIMITIVE

noncomputable abbrev GReal (D : DISTINGUISHER) : procmod () → Bool :=
  RealIndif SqueezelessSponge (Module.app PC (Perm : PRIMITIVE)) D

end GaudisCrypt.SHA3.Pilot.SLCommon
