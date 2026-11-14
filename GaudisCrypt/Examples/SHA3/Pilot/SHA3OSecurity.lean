import GaudisCrypt.Examples.SHA3.Pilot.SecureORO
import GaudisCrypt.Examples.SHA3.Pilot.SecureHash
import GaudisCrypt.Examples.SHA3.Pilot.SHA3_OIndiff
import GaudisCrypt.Examples.SHA3.SHA3OSecurity

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

/-!
# Top-level proof of SHA-3 security, with failing oracles (EasyCrypt `proof/SHA3OSecurity.ec`) —
EC-fidelity port, in progress

Ported so far: the clones `SORO`, `SH`, the file's modules (EC l. 1–175), and the local modules
of section `Preimage` (EC l. 194–300) with its first lemmas, `rw_RF_List_While` (EC l. 301)
and `eq_IRO_RFWhile` (EC l. 337).

Translation:
* the file-level type `f_out`, the operators `size_out`, `sigma`, `dout`, `to_list`, `of_list`
  and their axioms are the first port's class `SHA3OSecurity.Params`; `doutE1` is the first
  port's;
* `clone import SecureORO as SORO with …`, `clone import SecureHash as SH with …` are `clone`
  over the pilot theories (`Syntax/Clone.lean`), their `realize`s the clones' `proof *`.  Both
  are imported, as in EC; where a name is in both (`Bounder`, `Preimage`, `AdvPreimage`, …) it is
  written with its clone (`SH.AdvPreimage`), as EC does where it matters;
* EC's `import OIndif` (the clone of `SHA3_OIndiff`): the sponge's module types
  (`OFUNCTIONALITY`, `ODPRIMITIVE`, …) are the first port's `SHA3_OIndiff.OIndif`; `SH`'s own are
  `SH.OIndif.…`, as EC's `OIndif.OFUNCTIONALITY` after the clone;
* `FSetSize(F)` aliases `init`: wrapped in a call (exception E5);
  `OSponge(P) = FSetSize(CSome(Sponge, P))` is `Module.comp FSetSize (CSome Sponge)`.
* EC's module types are structural: a sponge-level `OFUNCTIONALITY` is an `ODFUNCTIONALITY`,
  an `OPRIMITIVE` an `ODPRIMITIVE` of `SH.OIndif` too.  Here each such use is a coercion,
  declared once (`module_subtype`);
* EC's theory `Program` (the clone `PBool`: `Sample`, `LoopSnoc`, `Sample_LoopSnoc_eq`) is the
  first port's `PBool.LoopSnoc.sample` and the rule `prhlStmt_dlist_left`
  (`Lib/EC/DListCall.lean`); EC's two `transitivity` steps through `Sample.sample` and
  `LoopSnoc.sample` are one, its first leg the lemma `Preimage.dlist_LoopSnoc` (as in E12);
* the sections' operators on maps (`inv`, …) and the value lemmas about them that EC proves
  inline by `smt` (`inv_fresh`) are the first port's;
* EC's `alias{1} 1 mp = BIRO.IRO.mp` names the map before a loop: `equiv_exists* §IRO.mp{1}`;
* the sections' local modules are modules of the namespace of their section (`Preimage.FInit`,
  …); their variables (`Log.m`, `RFList.m`) are `global_var`s, which the section's adversary
  is restricted against (fresh in EC); a local module that takes the section's adversary has
  it as a Lean parameter (`Dist_of_P1Adv A`, `SORO_P1 A`).
-/

-- the clones contain modules named like their theories; kept (exception E1)
set_option linter.dupNamespace false
-- the `module` command's lemmas do not use every parameter class
set_option linter.unusedSectionVars false

namespace GaudisCrypt.SHA3.Pilot.SHA3OSecurity

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.Sponge
open GaudisCrypt.SHA3.Sponge.BIRO
open GaudisCrypt.SHA3.SHA3Indiff (Simulator Cntr FC PC DRestr)
open GaudisCrypt.SHA3.SHA3_OIndiff (FSome PSome Poget CSome OSimulator Counter OFC OPC ODRestr
  DFSome DPSome OD)
open GaudisCrypt.SHA3.SHA3_OIndiff.OIndif
open GaudisCrypt.SHA3.SHA3OSecurity (size_out sigma f_out dout to_list of_list doutE1)

variable [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params]
  [GaudisCrypt.SHA3.SHA3OSecurity.Params]

/-! ## `clone import SecureORO as SORO with …` (EC l. 88–103) -/

clone import GaudisCrypt.SHA3.Pilot.SecureORO as SORO with
  type «from» <- List Bool, type «to» <- f_out,
  op sampleto <- dout,
  op bound <- sigma,
  op increase_counter <- fun (c : ℤ) (m : List Bool) =>
    c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0
  -- EC: realize bound_ge0 by exact(sigma_ge0).
  --     realize sampleto_ll by exact(dout_ll).   (likewise `sampleto_fu`, `sampleto_full`)
  --     realize increase_counter_spec by smt(List.size_ge0 divz_ge0 gt0_r).
  proof * by first
    | exact GaudisCrypt.SHA3.SHA3OSecurity.Params.sigma_ge0
    | exact GaudisCrypt.SHA3.SHA3OSecurity.Params.dout_ll
    | exact GaudisCrypt.SHA3.SHA3OSecurity.Params.dout_fu
    | exact GaudisCrypt.SHA3.SHA3OSecurity.Params.dout_full
    | (intro c m
       have hr := gt0_r
       have h1 : 0 ≤ (size m + 1) / r := Int.ediv_nonneg (by unfold size; omega) hr.le
       have := le_max_right ((size_out + r - 1) / r - 1) 0
       omega)

/-! ## `clone import SecureHash as SH with …` (EC l. 105–118) -/

clone import GaudisCrypt.SHA3.Pilot.SecureHash as SH with
  type «from» <- List Bool, type «to» <- f_out,
  type block <- GaudisCrypt.SHA3.SHA3Indiff.state,
  op sampleto <- dout,
  op bound <- sigma,
  op increase_counter <- fun (c : ℤ) (m : List Bool) =>
    c + ((size m + 1) / r + 1) + max ((size_out + r - 1) / r - 1) 0
  proof * by first
    | exact GaudisCrypt.SHA3.SHA3OSecurity.Params.sigma_ge0
    | exact GaudisCrypt.SHA3.SHA3OSecurity.Params.dout_ll
    | exact GaudisCrypt.SHA3.SHA3OSecurity.Params.dout_fu
    | exact GaudisCrypt.SHA3.SHA3OSecurity.Params.dout_full
    | (intro c m
       have hr := gt0_r
       have h1 : 0 ≤ (size m + 1) / r := Int.ediv_nonneg (by unfold size; omega) hr.le
       have := le_max_right ((size_out + r - 1) / r - 1) 0
       omega)

/-! ## The file's modules (EC l. 143–175) -/

-- EC's `module FSetSize (F : OFUNCTIONALITY) : OIndif.OFUNCTIONALITY`; `proc init = F.init` is
-- wrapped in a call (E5); `proc get = f`, outside the module type, is `FSetSize.get`
module FSetSize using (F : OFUNCTIONALITY) : SH.OIndif.OFUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (x : List Bool) : (Option f_out) {
    var y : Option (List Bool), r : Option f_out;
    y <- call F.f (($x, size_out));
    r <- if $y ≠ none then of_list (oget $y) else none;
    return $r
  };
}

-- EC's `module DFSetSize (F : ODFUNCTIONALITY) : OIndif.OFUNCTIONALITY`
module DFSetSize using (F : ODFUNCTIONALITY) : SH.OIndif.OFUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (x : List Bool) : (Option f_out) {
    var y : Option (List Bool), r : Option f_out;
    y <- call F.f (($x, size_out));
    r <- if $y ≠ none then of_list (oget $y) else none;
    return $r
  };
}

-- EC's `module FIgnoreSize (F : OIndif.ODFUNCTIONALITY) : OFUNCTIONALITY`
module FIgnoreSize using (F : SH.OIndif.ODFUNCTIONALITY) : OFUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (xi : List Bool × ℤ) : (Option (List Bool)) {
    var x : List Bool, i : ℤ, y : Option f_out, r : Option f_out;
    x, i <- $xi;
    r <- (default : Option f_out);
    y <- call F.f ($x);
    return Option.map to_list $r
  };
}

/-- EC's `module (OSponge : OIndif.OCONSTRUCTION) (P : OIndif.ODPRIMITIVE) =
FSetSize(CSome(Sponge,P))`. -/
noncomputable def OSponge : SH.OIndif.OCONSTRUCTION := Module.comp FSetSize (CSome Sponge)

-- EC's subtyping of the sponge's module types (`SHA3_OIndiff`'s `OIndif`), as coercions
module_subtype OFUNCTIONALITY <: ODFUNCTIONALITY
module_subtype OPRIMITIVE <: ODPRIMITIVE
-- … and of the clone `SH`'s: a sponge-level primitive is one of `SH.OIndif`'s (EC's module types
-- are structural)
module_subtype OPRIMITIVE <: SH.OIndif.ODPRIMITIVE

/-! ## Section `Preimage` (EC l. 190–916), in progress: its local modules -/

namespace Preimage

-- EC's local `module FInit (F : OIndif.ODFUNCTIONALITY) : OIndif.OFUNCTIONALITY`; `proc f = F.f`
-- is wrapped in a call (E5)
module FInit using (F : SH.OIndif.ODFUNCTIONALITY) : SH.OIndif.OFUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (x : List Bool) : (Option f_out) {
    var y : Option f_out;
    y <- call F.f ($x);
    return $y
  };
}

-- EC's local `module PInit (P : ODPRIMITIVE) : OPRIMITIVE`; its aliases are wrapped in a call (E5)
module PInit using (P : ODPRIMITIVE) : OPRIMITIVE {
  proc init () : Unit {
    return ()
  };
  proc f (x : GaudisCrypt.SHA3.SHA3Indiff.state) : (Option GaudisCrypt.SHA3.SHA3Indiff.state) {
    var y : Option GaudisCrypt.SHA3.SHA3Indiff.state;
    y <- call P.f ($x);
    return $y
  };
  proc fi (x : GaudisCrypt.SHA3.SHA3Indiff.state) : (Option GaudisCrypt.SHA3.SHA3Indiff.state) {
    var y : Option GaudisCrypt.SHA3.SHA3Indiff.state;
    y <- call P.fi ($x);
    return $y
  };
}

-- EC's local `module OF (F : Oracle) : OIndif.ODFUNCTIONALITY`; `proc f = F.get` is wrapped in a
-- call (E5)
module OF using (F : SORO.Oracle) : SH.OIndif.ODFUNCTIONALITY {
  proc f (x : List Bool) : (Option f_out) {
    var y : Option f_out;
    y <- call F.get ($x);
    return $y
  };
}

-- EC's local `module Log = { var m : (bool list * int, bool) fmap }`
global_var Log.m : FMap (List Bool × ℤ) Bool

-- EC's local `module ExtendOutputSize (F : Oracle) : ODFUNCTIONALITY`
module ExtendOutputSize using (F : SORO.Oracle) : ODFUNCTIONALITY {
  proc f (xk : List Bool × ℤ) : (Option (List Bool)) {
    var x : List Bool, k : ℤ, o : Option f_out, l : Option (List Bool), suffix : List Bool,
      «prefix» : List Bool, i : ℤ, r : Bool;
    x, k <- $xk;
    l <- (none : Option (List Bool));
    «prefix» <- [];
    suffix <- [];
    o <- call F.get ($x);
    «prefix» <- take $k (to_list (oget $o));
    i <- size_out;
    while (decide ($i < $k)) {
      if (!(decide (FMap.dom $Log.m ($x, $i)))) {
        r <$ dbool;
        Log.m <- FMap.set $Log.m ($x, $i) $r;
      }
      suffix <- rcons $suffix (oget (FMap.get $Log.m ($x, $i)));
      i <- $i + 1;
    }
    l <- some ($«prefix» ++ $suffix);
    return $l
  };
}

/-- EC's `local module OFC2 (F : Oracle) = OFC(ExtendOutputSize(F))`. -/
noncomputable def OFC2 : SORO.Oracle →ₘ OFUNCTIONALITY := Module.comp OFC ExtendOutputSize

-- EC's local `module ExtendOutput (F : RF)`; `proc f = ExtendOutputSize(F).f` is wrapped in a
-- call (E5), `proc get = f` is `ExtendOutput.get`
module ExtendOutput using (F : SORO.RF_T) {
  proc init () : Unit {
    Log.m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    _ <- call F.init ();
    return ()
  };
  proc f (xk : List Bool × ℤ) : (Option (List Bool)) {
    var y : Option (List Bool);
    y <- call ExtendOutputSize(F).f ($xk);
    return $y
  };
}

-- EC's local `module (Dist_of_P1Adv (A : SH.AdvPreimage) : ODISTINGUISHER) (F : ODFUNCTIONALITY)
-- (P : ODPRIMITIVE)`, with `A` a Lean parameter
open Classical in
set_option linter.gaudisCrypt.using false in
module Dist_of_P1Adv (A : SH.AdvPreimage) using (F : ODFUNCTIONALITY, P : ODPRIMITIVE) {
  proc distinguish () : Bool {
    var hash : f_out, hash' : Option f_out, m : List Bool;
    Log.m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    hash <$ dout;
    m <- call A(DFSetSize(F), P).guess ($hash);
    hash' <- call DFSetSize(F).f ($m);
    return decide ($hash' = some $hash)
  };
}

-- EC's local `module (SORO_P1 (A : SH.AdvPreimage) : SORO.AdvPreimage) (F : Oracle)`, with `A` a
-- Lean parameter
set_option maxHeartbeats 10000000 in
-- the `module` command's typing proof of this nest of oracles
set_option linter.gaudisCrypt.using false in
module SORO_P1 (A : SH.AdvPreimage) using (F : SORO.Oracle) {
  proc guess (h : f_out) : (List Bool) {
    var mi : List Bool;
    Log.m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    Counter.c <- 0;
    _ <- call OSimulator(ExtendOutputSize(F)).init ();
    mi <- call A(DFSetSize(OFC(ExtendOutputSize(F))),
      OPC(OSimulator(ExtendOutputSize(F)))).guess ($h);
    return $mi
  };
}

-- EC's local `module RFList`
global_var RFList.m : FMap (List Bool) f_out

module RFList : SORO.RF_T {
  proc init () : Unit {
    RFList.m <- (FMap.empty : FMap (List Bool) f_out);
    return ()
  };
  proc get (x : List Bool) : (Option f_out) {
    var z : List Bool;
    if (!(decide (FMap.dom $RFList.m $x))) {
      z <$ dlist dbool size_out;
      RFList.m <- FMap.set $RFList.m $x (oget (of_list $z));
    }
    return FMap.get $RFList.m $x
  };
  proc sample (_x : List Bool) : Unit {
    return ()
  };
}

-- EC's local `module RFWhile`
module RFWhile : SORO.RF_T {
  proc init () : Unit {
    RFList.m <- (FMap.empty : FMap (List Bool) f_out);
    return ()
  };
  proc get (x : List Bool) : (Option f_out) {
    var l : List Bool, i : ℤ, b : Bool;
    if (!(decide (FMap.dom $RFList.m $x))) {
      i <- 0;
      l <- [];
      while (decide ($i < size_out)) {
        b <$ dbool;
        l <- rcons $l $b;
        i <- $i + 1;
      }
      RFList.m <- FMap.set $RFList.m $x (oget (of_list $l));
    }
    return FMap.get $RFList.m $x
  };
  proc sample (_x : List Bool) : Unit {
    return ()
  };
}

/-- EC's `Sample_LoopSnoc_eq` (theory `Program`, the clone `PBool`), through `Sample.sample`:
sampling `dlist dbool size_out` is running `LoopSnoc.sample(size_out)`.  EC's module `Sample` is
not ported (the first port has `LoopSnoc` and the rule `prhlStmt_dlist_left`,
`Lib/EC/DListCall.lean`): EC's two `transitivity` steps of `rw_RF_List_While` are one, with this
as its first leg (as in exception E12). -/
theorem dlist_LoopSnoc :
    equiv[ True ==> §z{1} = §z{2} ]
      { var z : List Bool;
        z <$ dlist dbool size_out; } ~
      { var z : List Bool;
        z <- call
          (GaudisCrypt.SHA3.SHA3OSecurity.PBool.LoopSnoc.sample).procedure (size_out); } := by
  refine prhlStmt_dlist_left _ { get := fun _ => size_out } (fun _ => rfl) ?_
  equiv_call (_ : ={arg} ==> ={res})
  · equiv_proc; sim
  · ec_auto

/-- EC's `local equiv rw_RF_List_While :
RFList.get ~ RFWhile.get : ={arg, glob RFList} ==> ={res, glob RFWhile}`. -/
theorem rw_RF_List_While :
    equiv[ RFList.get (x) ~ RFWhile.get (x) : ={x, RFList.m} ==> ={res, RFList.m} ] := by
  -- EC: proc; if; 1, 3: auto; wp.
  equiv_proc; stmt_if
  · ec_close
  · stmt_wp
    -- EC: conseq(:_==> z{1} = l{2})=> />.
    equiv_conseq (: _ ==> §z{1} = §l{2})
    · ec_close
    -- EC: transitivity{1} { z <@ Sample.sample(size_out); } (true ==> ={z}) (true ==> z{1} = l{2})
    --     … transitivity{1} { z <@ LoopSnoc.sample(size_out); } (true ==> ={z})
    --       (true ==> z{1} = l{2})=>/>; last first.
    --     (one step: EC's module `Sample` is not ported, `dlist_LoopSnoc`)
    equiv_trans{1} {
        z <- call (GaudisCrypt.SHA3.SHA3OSecurity.PBool.LoopSnoc.sample).procedure (size_out); }
      (True ==> §z{1} = §z{2}) (True ==> §z{1} = §l{2})
    · intro σ₁ σ₂ _
      exact ⟨σ₁, trivial⟩
    · intro τ₁ τ τ₂ h₁ h₂
      exact h₁.trans h₂
    -- EC: by call(Sample_LoopSnoc_eq); auto.
    · exact dlist_LoopSnoc
    -- EC: + inline*; auto; sim.
    --       by while(={l, i} /\ n{1} = size_out); auto; smt(cats1).
    · stmt_inline*; stmt_wp
      equiv_while (={i} ∧ §l0{1} = §l{2} ∧ §n{1} = size_out)
      · ec_auto; ec_close
      ec_auto
  · ec_auto

-- EC's `op inv` (l. 331) is the first port's
open GaudisCrypt.SHA3.SHA3OSecurity (inv)

set_option maxHeartbeats 4000000 in
-- one declaration: both cases of the oracle, each with a loop
/-- EC's `local equiv eq_IRO_RFWhile :
BIRO.IRO.f ~ RFWhile.get :
arg{1} = (x{2}, size_out) /\ inv BIRO.IRO.mp{1} RFList.m{2} ==>
res{2} = of_list res{1} /\ size res{1} = size_out /\ inv BIRO.IRO.mp{1} RFList.m{2}`. -/
theorem eq_IRO_RFWhile :
    equiv[ IRO.f (xn) ~ RFWhile.get (x) :
      §xn{1} = (§x{2}, size_out) ∧ inv §IRO.mp{1} §RFList.m{2} ==>
      §res{2} = of_list §res{1} ∧ size §res{1} = size_out ∧ inv §IRO.mp{1} §RFList.m{2} ] := by
  -- EC: proc; inline*; sp.
  equiv_proc; stmt_inline*; stmt_sp
  -- EC: rcondt{1} 1; 1: by auto.
  stmt_rcondt{1} 1
  · hoare_auto
  -- EC: if{2}; sp; last first.
  stmt_if{2}
  swap
  -- EC: + alias{1} 1 mp = BIRO.IRO.mp.
  --     (the map before the loop is named by `exists*`)
  · equiv_exists* §IRO.mp{1}
    intro mp
    -- EC: conseq(:_==> BIRO.IRO.mp{1} = mp{1} /\ size bs{1} = i{1} /\ i{1} = size_out /\
    --       inv mp{1} RFList.m{2} /\
    --       bs{1} = take i{1} (to_list (oget RFList.m{2}.[x{1}])))=> />.
    equiv_conseq (: _ ==> §IRO.mp{1} = mp ∧ size §bs{1} = §i{1} ∧ §i{1} = size_out ∧
      inv mp §RFList.m{2} ∧
      §bs{1} = take §i{1} (to_list (oget (FMap.get §RFList.m{2} §x{1}))))
    --     - move=> &l &r H0 H1 H2 H3 H4 bs_L mp_L H5 H6 H7 H8 H9.
    --       rewrite take_oversize 1:spec_dout 1:H5 //.
    --       rewrite eq_sym to_listK => ->.
    --       by have:=H4; rewrite domE; smt().
    --     - smt(take_oversize spec_dout).
    · ec_progress
      have hd : RFList_m₂.dom x₂1 := by simpa using ‹decide (RFList_m₂.dom x₂1) = !false›
      have ht : take size_out (to_list (oget (RFList_m₂.get x₂1))) =
          to_list (oget (RFList_m₂.get x₂1)) :=
        take_oversize _ _ (le_of_eq (GaudisCrypt.SHA3.SHA3OSecurity.Params.spec_dout _))
      have hk : of_list (to_list (oget (RFList_m₂.get x₂1))) = some (oget (RFList_m₂.get x₂1)) :=
        (GaudisCrypt.SHA3.SHA3OSecurity.Params.to_listK _ _).mp rfl
      rw [ht, hk]
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd)
      rw [hv]
      rfl
    -- EC: while{1}(BIRO.IRO.mp{1} = mp{1} /\ size bs{1} = i{1} /\
    --       0 <= i{1} <= size_out /\ n{1} = size_out /\
    --       inv mp{1} RFList.m{2} /\ x{1} \in RFList.m{2} /\
    --       bs{1} = take i{1} (to_list (oget RFList.m{2}.[x{1}])))(size_out - i{1});
    --     auto=> />.
    equiv_while{1} (§IRO.mp{1} = mp ∧ size §bs{1} = §i{1} ∧ 0 ≤ §i{1} ∧ §i{1} ≤ size_out ∧
        §n{1} = size_out ∧ inv mp §RFList.m{2} ∧ FMap.dom §RFList.m{2} §x{1} ∧
        §bs{1} = take §i{1} (to_list (oget (FMap.get §RFList.m{2} §x{1}))))
      ((size_out - §i{1}).toNat)
    · while_ll_phoare
      intro σ₂
      ec_auto
      intros; split_ifs
      · exact (is_lossless_iff_expected _).mp dbool_ll
      · rfl
    -- EC: + sp; rcondf 1; auto=> />; 1: smt().
    · intro σ₂ k
      stmt_sp
      stmt_rcondf 1
      · hoare_auto; ec_prep
        simp [(‹inv IRO_mp v›).2.2.1 _ ‹v.dom x0› n0 ⟨‹0 ≤ n0›, ‹n0 < size_out›⟩]
      --       move=> &h H0 H1 H2 H3 H4 H5 H6 H7 H8.
      --       rewrite size_rcons //=; do!split; 1, 2, 4: smt(size_ge0).
      --       rewrite (take_nth witness) 1:spec_dout 1:size_ge0//=.
      --       rewrite - H7; congr; rewrite H5=> //=.
      --       by apply H4=> //=.
      hoare_auto; ec_progress
      · rw [size_rcons, ‹size (take n0 _) = n0›]
      · have hdom := (‹inv IRO_mp v›).2.2.1 _ ‹v.dom x0› n0 ⟨‹0 ≤ n0›, ‹n0 < size_out›⟩
        rw [take_nth default n0 (to_list (oget (v.get x0))) ⟨‹0 ≤ n0›,
            lt_of_lt_of_eq ‹n0 < size_out›
              (GaudisCrypt.SHA3.SHA3OSecurity.Params.spec_dout _).symm⟩,
          (‹inv IRO_mp v›).2.2.2 _ _ hdom]
        rfl
    -- EC: smt(size_out_gt0 size_ge0 take0).
    · ec_auto; ec_progress
      exact GaudisCrypt.SHA3.SHA3OSecurity.Params.size_out_gt0.le
  -- EC: auto=> //=.
  --     conseq(:_==> l{2} = bs{1} /\ size bs{1} = i{1} /\ i{1} = n{1} /\ n{1} = size_out /\
  --       inv BIRO.IRO.mp{1} RFList.m{2}.[x{2} <- oget (of_list l{2})])=> />.
  · stmt_wp
    equiv_conseq (: _ ==> §l{2} = §bs{1} ∧ size §bs{1} = §i{1} ∧ §i{1} = §n{1} ∧
      §n{1} = size_out ∧ inv §IRO.mp{1} (FMap.set §RFList.m{2} §x{2} (oget (of_list §l{2}))))
    --     + smt(get_setE spec2_dout).
    --     + smt(get_setE spec2_dout).
    · ec_progress
      have hne : of_list l₂ ≠ none :=
        GaudisCrypt.SHA3.SHA3OSecurity.Params.spec2_dout l₂ ‹size l₂ = size_out›
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hne
      rw [FMap.get_set_sameE, hv]
      rfl
    -- EC: alias{1} 1 m = BIRO.IRO.mp; sp.
    --     (the map before the loop is named by `exists*`)
    equiv_exists* §IRO.mp{1}
    intro m
    stmt_sp
    -- EC: conseq(:_==> l{2} = bs{1} /\ size bs{1} = i{1} /\ i{1} = n{1} /\
    --       n{1} = size_out /\ inv m{1} RFList.m{2} /\
    --       (forall j, (x{1}, j) \in BIRO.IRO.mp{1} => 0 <= j < i{1}) /\
    --       (forall l j, l <> x{1} => m{1}.[(l,j)] = BIRO.IRO.mp{1}.[(l,j)]) /\
    --       (forall j, 0 <= j < i{1} => (x{1}, j) \in BIRO.IRO.mp{1}) /\
    --       (forall j, 0 <= j < i{1} => BIRO.IRO.mp{1}.[(x{1},j)] = Some (nth witness bs{1} j))).
    equiv_conseq (: _ ==> §l{2} = §bs{1} ∧ size §bs{1} = §i{1} ∧ §i{1} = §n{1} ∧
      §n{1} = size_out ∧ inv m §RFList.m{2} ∧
      (∀ j, FMap.dom §IRO.mp{1} (§x{1}, j) → 0 ≤ j ∧ j < §i{1}) ∧
      (∀ l j, l ≠ §x{1} → FMap.get m (l, j) = FMap.get §IRO.mp{1} (l, j)) ∧
      (∀ j, 0 ≤ j ∧ j < §i{1} → FMap.dom §IRO.mp{1} (§x{1}, j)) ∧
      (∀ j, 0 ≤ j ∧ j < §i{1} →
        FMap.get §IRO.mp{1} (§x{1}, j) = some (nth default §bs{1} j)))
    --     + move=> /> &l &r H0 H1 H2 H3 H4 mp_L bs_L H5 H6 H7 H8 H9; do!split;
    --         ..-2 : smt(domE mem_set).
    --       move=> l j Hin. rewrite get_setE/=. case: (l = x{r}) => [<<-|]. …
    --     (EC's argument, stated once in the first port: `inv_fresh`)
    · ec_prep
      exact ⟨‹size l₂1 = size_out›, GaudisCrypt.SHA3.SHA3OSecurity.inv_fresh _ _ _ _ _
        ‹inv mp₁ RFList_m₂› ‹¬RFList_m₂.dom x₂1› ‹size l₂1 = size_out›
        (fun l j h => (‹∀ l j, l ≠ x₂1 → mp₁.get (l, j) = IRO_mp₁.get (l, j)› l j h).symm)
        (fun j => ⟨‹∀ j, IRO_mp₁.dom (x₂1, j) → 0 ≤ j ∧ j < size_out› j,
          ‹∀ j, 0 ≤ j ∧ j < size_out → IRO_mp₁.dom (x₂1, j)› j⟩)
        (fun j h0 h1 =>
          ‹∀ j, 0 ≤ j ∧ j < size_out → IRO_mp₁.get (x₂1, j) = some (nth default l₂1 j)› j
            ⟨h0, h1⟩)⟩
    -- EC: while(l{2} = bs{1} /\ size bs{1} = i{1} /\ 0 <= i{1} <= n{1} /\ ={i} /\
    --       n{1} = size_out /\ inv m{1} RFList.m{2} /\ … ).
    equiv_while (§l{2} = §bs{1} ∧ size §bs{1} = §i{1} ∧ 0 ≤ §i{1} ∧ §i{1} ≤ §n{1} ∧
      §i{1} = §i{2} ∧ §n{1} = size_out ∧ inv m §RFList.m{2} ∧
      (∀ j, FMap.dom §IRO.mp{1} (§x{1}, j) → 0 ≤ j ∧ j < §i{1}) ∧
      (∀ l j, l ≠ §x{1} → FMap.get m (l, j) = FMap.get §IRO.mp{1} (l, j)) ∧
      (∀ j, 0 ≤ j ∧ j < §i{1} → FMap.dom §IRO.mp{1} (§x{1}, j)) ∧
      (∀ j, 0 ≤ j ∧ j < §i{1} →
        FMap.get §IRO.mp{1} (§x{1}, j) = some (nth default §bs{1} j)))
    -- EC: + sp; rcondt{1} 1; auto=> />.
    · stmt_sp
      stmt_rcondt{1} 1
      --       - smt().
      · intro σ₂
        hoare_auto; ec_prep
        exact fun h => lt_irrefl _
          ((‹∀ j, mp.dom (x0, j) → 0 ≤ j ∧ j < (localVarLens "i" ℤ).get σ₂› _ h).2)
      --       move=> &l &r H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 rL _.
      --       rewrite get_setE /= size_rcons /=; do!split; 1,2: smt(size_ge0).
      ec_auto; ec_progress
      · rw [FMap.get_set_sameE]; rfl
      · rw [size_rcons]
      --       - smt(mem_set).
      · rcases (FMap.mem_set _ _ _ _).mp ‹_› with h | h
        · exact (‹∀ j, mp₁.dom (x0₁, j) → 0 ≤ j ∧ j < size l₂› _ h).1
        · rw [(Prod.mk.inj h).2]; exact ‹0 ≤ size l₂›
      · rcases (FMap.mem_set _ _ _ _).mp ‹_› with h | h
        · have := (‹∀ j, mp₁.dom (x0₁, j) → 0 ≤ j ∧ j < size l₂› _ h).2
          omega
        · rw [(Prod.mk.inj h).2]; omega
      --       - smt(get_setE).
      · rw [FMap.get_set_neqE _ _ _ _ (fun e => ‹l ≠ x0₁› (Prod.mk.inj e).1)]
        exact ‹∀ l j, l ≠ x0₁ → m.get (l, j) = mp₁.get (l, j)› _ _ ‹_›
      --       - smt(mem_set).
      · rw [FMap.mem_set]
        by_cases hj : j = size l₂
        · right; rw [hj]
        · left
          exact ‹∀ j, 0 ≤ j ∧ j < size l₂ → mp₁.dom (x0₁, j)› j ⟨‹0 ≤ j›, by omega⟩
      --       - move=>j Hj0 Hjsize; rewrite get_setE/=nth_rcons.
      --         case: (j = size bs{l})=>[->>//=|h].
      --         have/=Hjs:j < size bs{l} by smt().
      --         by rewrite Hjs/=H9//=.
      · rw [FMap.get_set_sameE, nth_rcons]
        by_cases hj : j = size l₂
        · subst hj
          rw [FMap.get_set_sameE]
          simp [oget]
        · have hlt : j < size l₂ := by omega
          rw [FMap.get_set_neqE _ _ _ _ (fun e => hj (Prod.mk.inj e).2), if_pos hlt]
          exact ‹∀ j, 0 ≤ j ∧ j < size l₂ → mp₁.get (x0₁, j) = some (nth default l₂ j)› j
            ⟨‹0 ≤ j›, hlt⟩
    -- EC: by auto; smt(size_out_gt0).
    ec_auto; ec_progress
    · exact GaudisCrypt.SHA3.SHA3OSecurity.Params.size_out_gt0.le
    · exact absurd ((‹inv mp₁ m₂›).2.1 _ _ ‹mp₁.dom (x₂, j)›) ‹¬m₂.dom x₂›
    · exact absurd ((‹inv mp₁ m₂›).2.1 _ _ ‹mp₁.dom (x₂, j)›) ‹¬m₂.dom x₂›

end Preimage

end GaudisCrypt.SHA3.Pilot.SHA3OSecurity
