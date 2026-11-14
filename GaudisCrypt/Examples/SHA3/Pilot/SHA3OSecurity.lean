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
of section `Preimage` (EC l. 194–300) with its first lemmas, `rw_RF_List_While` (EC l. 301),
`eq_IRO_RFWhile` (EC l. 337), `eq_extend` (EC l. 430), `of_listK`, `Fill_In`, `eq_eager_ideal`
(EC l. 492), `eq_eager_ideal2` (EC l. 512), `Dist`, `Game`, `eager_ideal` (EC l. 574),
`rw_ideal_2` (EC l. 652), `rw_ideal` (EC l. 792), `leq_ideal` (EC l. 870), `rw_real`
(EC l. 881) and `Sponge_preimage_resistant` (EC l. 898): section `Preimage` is complete.
Sections `SecondPreimage` and `Collision` are to do.

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
* the sections' operators on maps (`inv`, `eq_extend_size`) and the value lemmas about them
  that EC proves inline by `smt` (`inv_fresh`, `eq_extend_size_set_lt`, …) are the first port's;
* `FSetSize`'s `proc get = f` (outside its module type) makes `FSetSize(F)` an `Oracle` in EC:
  a coercion of `SH.OIndif.OFUNCTIONALITY` to `SORO.Oracle` (`get` is `f`);
* a loop that does not write a variable the condition after it reads (EC's `conseq (: _ ==>
  true)`): the variable's fact is kept in the Hoare loop's invariant (GAP 1);
* `clone import FullRO as Eager with …` is the first port's namespace `SHA3OSecurity.Eager`
  (`RO_T`, `RO`, `LRO`, the variables `Eager.RO.m`, `Eager.FRO.m`), re-exported under `Eager`;
* a variable of an inlined callee whose name is also one of the other side, or of the
  precondition at another type (`x1`{1}, `x0`{2}), and a variable the statement no longer
  mentions (`k` after `wp`, in `splitwhile`'s condition) are written with their lenses,
  `§(localVarLens "x0" (List Bool)){2}` (GAP 2);
* GAP 3: the first port's `ODRestr` hands the adversary its primitive built with the first
  port's module type constructor, which the clone `SH`'s projections do not see through:
  `simp only [ODPRIMITIVE_f_mk]` (`ODPRIMITIVE_fi_mk`) in front of `proc` on the primitive's
  procedures;
* GAP 4: after `sp` through a game's initializations, `glob A` is equal in the two memories by
  the memories' equation, taken out by hand (GAP 7 of `Pilot/SHA3Security.lean`);
* GAP 5: `equiv_call (_ : ={x₁, …})` on the adversary puts `={glob A}` into the oracles'
  judgments (EC's do not have it), and the `wp`s below then carry `glob A` read over written
  memories, on which `inline` does not end (40M heartbeats).  Where the oracles' proofs are
  long, the invariant is written in two parts, `(_ : ={x₁, …} ∧ ={y₁, …})`: the general form,
  with EC's oracle judgments;
* a call behind the module type's record (`(SORO.RF_T.get RFList)`) keeps the other variables
  only with its footprint stated at that spelling (`fvP_RF_T_get_RFList`, `fvP_SORO_Bounder`,
  `fvP_RFWhile`: EC reads them off the code);
* EC's `rnd f g` between `dlist dbool size_out` and `dout` is `equiv_rnd (fun l => oget
  (of_list l))`: it asks that `f` push the first distribution to the second, which is the first
  port's `dlist_dout` (EC's `dout_equal_dlist`, `to_listK`);
* GAP 6: a game of the clone `SH` applied to the sponge's modules (`SH.Preimage(A, OSponge,
  PSome(Perm))`) has them behind the clone's projections and coercions, which `inline` does not
  open: `OPRIMITIVE_coe_eq`, `OSponge_app`, `PSome_Perm_init` (all by `rfl`) put them at the
  sponge's module types first;
* GAP 7: `sim` does not end on two loops that call the permutation after a `conseq` that keeps
  `glob Perm` (it does where only locals are kept): the `while` rule and `call (_ : ={glob
  Perm})`;
* EC's chains `inline{1} 1; inline{2} 1; sp` down to the adversary's call are
  `repeat stmt_inline{1} 0; repeat stmt_inline{2} 0; stmt_sp`; `sim n n` in front of a call or a
  conditional is `stmt_wp` (`sim n n` where a sampling is left);
* `Dist(F)` is used as an `RO_Distinguisher` (`Eager.RO_LRO_D (Dist A)`): its `distinguish`
  takes that type's `unit`;
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

/-- EC's `proc get = f` of `FSetSize`: `FSetSize(F)` is also an `Oracle`, its `get` the procedure
`f`.  (A coercion of the module type: EC's alias is outside the module type.) -/
noncomputable instance : Coe SH.OIndif.OFUNCTIONALITY SORO.Oracle :=
  ⟨fun F => SORO.Oracle.mk { get := SH.OIndif.OFUNCTIONALITY.f F }⟩

/-! ## `clone import Program as PBool`, `clone import FullRO as Eager` (EC l. 177–188)

The first port's namespaces: `PBool.LoopSnoc.sample`, and the clone `Eager` of `PROM.FullRO` at
`bool list * int`, `bool`, with its module variables `Eager.RO.m`, `Eager.FRO.m`. -/

namespace Eager
export GaudisCrypt.SHA3.SHA3OSecurity.Eager (RO.m FRO.m RO_T RO_Distinguisher RO LRO)

/-- The clone's `RO_LRO_D` (`PROM.FullRO`'s, at the clone's `dout` and module variables, its
`dout_ll` `dbool_ll`): a distinguisher cannot tell `RO` from `LRO`.  Its side conditions, which
EC checks itself, are found (`ec_module`, `fp_disjoint`). -/
theorem RO_LRO_D (D : RO_Distinguisher)
    (hD : Module.ECModule D (PROM.FullRO.RO_ext (List Bool × ℤ) Bool) := by ec_module)
    (hdisj : FVP.fvP D ≤ (RO.m.footprint ⊔ FRO.m.footprint)ᶜ := by fp_disjoint) :
    type_of% (PROM.FullRO.FullEager.RO_LRO_D (List Bool × ℤ) Bool Unit Bool (fun _ => dbool)
      FRO.m (fun _ => dbool_ll) RO.m D hD hdisj) :=
  PROM.FullRO.FullEager.RO_LRO_D (List Bool × ℤ) Bool Unit Bool (fun _ => dbool) FRO.m
    (fun _ => dbool_ll) RO.m D hD hdisj

end Eager

/-- A sponge-level primitive given to an adversary of the clone `SH` (EC's module types are
structural): its `f` is the primitive's.  (The first port's `ODRestr` builds the primitive with
its own module type's constructor, which the clone's projection lemma does not match.) -/
theorem ODPRIMITIVE_f_mk (f fi) :
    SH.OIndif.ODPRIMITIVE.f (GaudisCrypt.SHA3.OptionIndifferentiability.ODPRIMITIVE.mk
      SHA3Indiff.state (List Bool × ℤ) (List Bool) { f := f, fi := fi }) = f :=
  SH.OIndif.ODPRIMITIVE.f.mk_simp { f := f, fi := fi }

/-- As `ODPRIMITIVE_f_mk`, for `fi`. -/
theorem ODPRIMITIVE_fi_mk (f fi) :
    SH.OIndif.ODPRIMITIVE.fi (GaudisCrypt.SHA3.OptionIndifferentiability.ODPRIMITIVE.mk
      SHA3Indiff.state (List Bool × ℤ) (List Bool) { f := f, fi := fi }) = fi :=
  SH.OIndif.ODPRIMITIVE.fi.mk_simp { f := f, fi := fi }

/-! ## Section `Preimage` (EC l. 190–916) -/

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

-- EC's `op eq_extend_size` (l. 407) is the first port's
open GaudisCrypt.SHA3.SHA3OSecurity (eq_extend_size)

-- EC's local `module ExtendSample (F : OFUNCTIONALITY)`; `proc init = F.init` is wrapped in a
-- call (E5)
module ExtendSample using (F : OFUNCTIONALITY) : OFUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (xk : List Bool × ℤ) : (Option (List Bool)) {
    var x : List Bool, k : ℤ, y : Option (List Bool);
    x, k <- $xk;
    if (decide ($k ≤ size_out)) {
      y <- call F.f (($x, size_out));
      y <- Option.map (take $k) $y;
    } else {
      y <- call F.f (($x, $k));
    }
    return $y
  };
}

set_option maxHeartbeats 4000000 in
-- one declaration: the two cases, three loops
/-- EC's `local equiv eq_extend :
ExtendSample(FSome(BIRO.IRO)).f ~ ExtendOutputSize(FSetSize(FSome(BIRO.IRO))).f :
={arg} /\ eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2} ==>
={res} /\ eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2}`. -/
theorem eq_extend :
    equiv[ ExtendSample(FSome(IRO.asF)).f (x) ~
        ExtendOutputSize(FSetSize(FSome(IRO.asF))).f (x) :
      ={x} ∧ eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log.m{2} ==>
      ={res} ∧ eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log.m{2} ] := by
  -- EC: proc; inline*; auto; sp.
  equiv_proc; stmt_inline*; stmt_wp; stmt_sp
  -- EC: rcondt{2} 1; 1: auto.
  stmt_rcondt{2} 1
  · hoare_auto
  -- EC: if{1}; sp.
  stmt_if{1}
  · stmt_sp
    -- EC: - rcondt{1} 1; auto.
    stmt_rcondt{1} 1
    · hoare_auto
    -- EC: rcondf{2} 8; 1: auto.
    --     - conseq(:_==> true); 1: smt().
    --       by while(true); auto.
    stmt_rcondf{2} 8
    · intro σ₁
      stmt_wp
      --     (GAP 1: `k`, which the loop does not write, is kept by the invariant)
      hoare_while (§k ≤ size_out)
      · hoare_auto
      · intros; simp_all
      · hoare_auto
    -- EC: auto=> /=.
    stmt_wp
    -- EC: conseq(:_==> ={bs, k} /\ size bs{1} = size_out /\
    --       eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2})=> //=.
    equiv_conseq (: _ ==> ={bs, k} ∧ size §bs{1} = size_out ∧
      eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log.m{2})
    --     - smt(cats0 to_listK spec2_dout).
    · ec_progress
      have hk : to_list (oget (of_list bs₂1)) = bs₂1 :=
        GaudisCrypt.SHA3.SHA3OSecurity.to_list_oget_of_list _ ‹size bs₂1 = size_out›
      change some (take xk₂.2 bs₂1) = some (take xk₂.2 (to_list (oget (of_list bs₂1))) ++ [])
      rw [hk, List.append_nil]
    -- EC: while(={k, bs, n, x2} /\ i{1} = i0{2} /\ n{1} = size_out /\
    --       0 <= i{1} <= n{1} /\ size bs{1} = i{1} /\
    --       eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2}).
    equiv_while (={k, bs, n} ∧ §(localVarLens "x1" (List Bool)){1} = §x2{2} ∧ §i{1} = §i0{2} ∧
      §n{1} = size_out ∧ 0 ≤ §i{1} ∧ §i{1} ≤ §n{1} ∧ size §bs{1} = §i{1} ∧
      eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log.m{2})
    -- EC: - by sp; if; auto=> />; smt(domE get_setE size_rcons).
    · stmt_sp; stmt_if
      --     (EC's `smt` on `eq_extend_size`: the first port's `eq_extend_size_dom_lt`,
      --     `eq_extend_size_set_lt`)
      · ec_progress
        simp [GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_dom_lt
          ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ size bs₂› ‹size bs₂ < size_out›]
      · ec_auto; ec_progress
        · rw [size_rcons]
        · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_lt a
            ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ size bs₂› ‹size bs₂ < size_out›).1 _ _
            ⟨‹0 ≤ j›, ‹j < size_out›⟩
        · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_lt a
            ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ size bs₂› ‹size bs₂ < size_out›).2.1 _ _
            ‹size_out ≤ j›
        · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_lt
            (m2 := mp₂) a ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ size bs₂›
            ‹size bs₂ < size_out›).2.2 _ _ ‹_›
      · ec_auto; ec_progress
        · rw [(‹eq_extend_size mp₁ mp₂ m₂›).1 _ _ ⟨‹0 ≤ size bs₂›, ‹size bs₂ < size_out›⟩]
        · rw [size_rcons]
    -- EC: by auto=> />; smt(size_eq0 size_out_gt0).
    ec_auto; ec_progress
    exact GaudisCrypt.SHA3.SHA3OSecurity.Params.size_out_gt0.le
  · stmt_sp
    -- EC: rcondt{1} 1; 1: auto.
    stmt_rcondt{1} 1
    · hoare_auto
    -- EC: splitwhile{1} 1 : i0 < size_out; auto=> /=.
    stmt_splitwhile{1} 1 : §i0 < size_out
    stmt_wp
    -- EC: while( (i0, n0, x3){1} = (i, k, x){2} /\ bs0{1} = prefix{2} ++ suffix{2} /\
    --       size_out <= i{2} <= k{2} /\ eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2}).
    equiv_while (§i0{1} = §i{2} ∧ §n1{1} = §k{2} ∧ §x4{1} = §x{2} ∧
      §bs0{1} = §«prefix»{2} ++ §suffix{2} ∧ size_out ≤ §i{2} ∧ §i{2} ≤ §k{2} ∧
      eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log.m{2})
    -- EC: + sp; if; auto=> />; 1,3:smt(domE rcons_cat).
    --       move=> &1 &2 out_le_i _ ih1 ih2 ih3 i_lt_k xi_notin_mp r _.
    --       by rewrite !get_set_sameE /= rcons_cat //= #smt:(get_setE size_out_gt0).
    --     (EC's `smt` on `eq_extend_size`: the first port's `eq_extend_size_dom_ge`,
    --     `eq_extend_size_set_ge`)
    · stmt_sp; stmt_if
      · ec_progress
        simp [GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_dom_ge
          ‹eq_extend_size mp₁ mp₂ m₂› ‹size_out ≤ i₂›]
      · ec_auto; ec_progress
        · rw [FMap.get_set_sameE, FMap.get_set_sameE]
          simp [rcons]
        · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_ge a
            ‹eq_extend_size mp₁ mp₂ m₂› ‹size_out ≤ i₂›).1 _ _ ⟨‹0 ≤ j›, ‹j < size_out›⟩
        · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_ge a
            ‹eq_extend_size mp₁ mp₂ m₂› ‹size_out ≤ i₂›).2.1 _ _ ‹size_out ≤ j›
        · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_ge
            (m3 := m₂) a ‹eq_extend_size mp₁ mp₂ m₂› ‹size_out ≤ i₂›).2.2 _ _ ‹_›
      · ec_auto; ec_progress
        rw [(‹eq_extend_size mp₁ mp₂ m₂›).2.1 _ _ ‹size_out ≤ i₂›]
        simp [rcons]
    -- EC: auto=> //=.
    stmt_wp
    -- EC: conseq(:_==> ={i0} /\ size bs{2} = i0{1} /\ (i0, x3){1} = (n, x2){2} /\
    --       bs0{1} = bs{2} /\ size bs{2} = size_out /\
    --       eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2}).
    equiv_conseq (: _ ==> ={i0} ∧ size §bs{2} = §i0{1} ∧ §i0{1} = §n{2} ∧ §x4{1} = §x2{2} ∧
      §bs0{1} = §bs{2} ∧ size §bs{2} = size_out ∧
      eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log.m{2})
    --     + move=> />; smt(cats0 take_oversize spec_dout to_listK spec2_dout).
    · ec_progress
      have hk : to_list (oget (of_list bs₂1)) = bs₂1 :=
        GaudisCrypt.SHA3.SHA3OSecurity.to_list_oget_of_list _ ‹size bs₂1 = size_out›
      change bs₂1 = take xk₂.2 (to_list (oget (of_list bs₂1))) ++ []
      rw [hk, List.append_nil, take_oversize _ _ (by
        rw [‹size bs₂1 = size_out›]; exact le_of_lt ‹size_out < xk₂.2›)]
    -- EC: while(={i0} /\ x3{1} = x2{2} /\ 0 <= i0{1} <= n{2} /\ n{2} = size_out /\
    --       bs0{1} = bs{2} /\ size bs{2} = i0{1} /\ size_out <= n0{1} /\
    --       eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2}).
    equiv_while (={i0} ∧ §x4{1} = §x2{2} ∧ 0 ≤ §i0{1} ∧ §i0{1} ≤ §n{2} ∧ §n{2} = size_out ∧
      §bs0{1} = §bs{2} ∧ size §bs{2} = §i0{1} ∧ size_out ≤ §n1{1} ∧
      eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log.m{2})
    -- EC: + by sp; if; auto=> />; smt(size_rcons domE get_setE size_rcons mem_set).
    --     (the last bullet of each branch: the two loops' guards after `splitwhile`)
    · stmt_sp; stmt_if
      · ec_progress
        simp [GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_dom_lt
          ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ size bs₂› ‹size bs₂ < size_out›]
      · ec_auto; ec_progress
        · rw [size_rcons]
        · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_lt a
            ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ size bs₂› ‹size bs₂ < size_out›).1 _ _
            ⟨‹0 ≤ j›, ‹j < size_out›⟩
        · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_lt a
            ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ size bs₂› ‹size bs₂ < size_out›).2.1 _ _
            ‹size_out ≤ j›
        · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_lt
            (m2 := mp₂) a ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ size bs₂›
            ‹size bs₂ < size_out›).2.2 _ _ ‹_›
        · have hn := ‹size_out ≤ n1₁›
          by_cases h : size bs₂ + 1 < size_out
          · simp [h, show size bs₂ + 1 < n1₁ by omega]
          · simp [h]
      · ec_auto; ec_progress
        · rw [(‹eq_extend_size mp₁ mp₂ m₂›).1 _ _ ⟨‹0 ≤ size bs₂›, ‹size bs₂ < size_out›⟩]
        · rw [size_rcons]
        · have hn := ‹size_out ≤ n1₁›
          by_cases h : size bs₂ + 1 < size_out
          · simp [h, show size bs₂ + 1 < n1₁ by omega]
          · simp [h]
    -- EC: by auto=> />; smt(size_out_gt0).
    ec_auto; ec_progress
    · exact GaudisCrypt.SHA3.SHA3OSecurity.Params.size_out_gt0.le
    · have h0 : (0 : ℤ) < size_out := GaudisCrypt.SHA3.SHA3OSecurity.Params.size_out_gt0
      have h2 := ‹size_out < xn0₁.2›
      simp [h0, show (0 : ℤ) < xn0₁.2 by omega]

/-- EC's `local lemma of_listK l : of_list (to_list l) = Some l`. -/
theorem of_listK (l : f_out) : of_list (to_list l) = some l :=
  -- EC: by rewrite -to_listK.
  (GaudisCrypt.SHA3.SHA3OSecurity.Params.to_listK l (to_list l)).mp rfl

-- EC's local `module Fill_In (F : RO)`; `proc init = F.init` is wrapped in a call (E5)
module Fill_In using (F : Eager.RO_T) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (xn : List Bool × ℤ) : (List Bool) {
    var x : List Bool, n : ℤ, l : List Bool, b : Bool, i : ℤ;
    x, n <- $xn;
    i <- 0;
    l <- [];
    while (decide ($i < $n)) {
      b <- call F.get (($x, $i));
      l <- rcons $l $b;
      i <- $i + 1;
    }
    while (decide ($i < size_out)) {
      _ <- call F.sample (($x, $i));
      i <- $i + 1;
    }
    return $l
  };
}

set_option maxHeartbeats 4000000 in
-- one declaration: two loops
/-- EC's `local equiv eq_eager_ideal :
BIRO.IRO.f ~ Fill_In(LRO).f :
={arg} /\ BIRO.IRO.mp{1} = RO.m{2} ==> ={res} /\ BIRO.IRO.mp{1} = RO.m{2}`. -/
theorem eq_eager_ideal :
    equiv[ IRO.f (xn) ~ Fill_In(Eager.LRO).f (x) :
      §xn{1} = §x{2} ∧ §IRO.mp{1} = §Eager.RO.m{2} ==>
      ={res} ∧ §IRO.mp{1} = §Eager.RO.m{2} ] := by
  -- EC: proc; inline*; sp; rcondt{1} 1; auto.
  equiv_proc; stmt_inline*; stmt_sp
  stmt_rcondt{1} 1
  · hoare_auto
  -- EC: while{2}(bs{1} = l{2} /\ BIRO.IRO.mp{1} = RO.m{2})(size_out - i{2}).
  equiv_while{2} (§bs{1} = §l{2} ∧ §IRO.mp{1} = §Eager.RO.m{2}) ((size_out - §i{2}).toNat)
  · while_ll_phoare
    intro σ₁
    ec_auto
  -- EC: + by auto=> />; smt().
  · intro σ₁ k
    hoare_auto
  -- EC: conseq(:_==> bs{1} = l{2} /\ BIRO.IRO.mp{1} = RO.m{2}); 1: smt().
  equiv_conseq (: _ ==> §bs{1} = §l{2} ∧ §IRO.mp{1} = §Eager.RO.m{2})
  · ec_close
  -- EC: while(={i, n, x} /\ bs{1} = l{2} /\ BIRO.IRO.mp{1} = RO.m{2}).
  equiv_while (={i, n, x} ∧ §bs{1} = §l{2} ∧ §IRO.mp{1} = §Eager.RO.m{2})
  -- EC: + sp; if{1}.
  · stmt_sp
    stmt_if{1}
    -- EC: - by rcondt{2} 2; auto=> />.
    · stmt_rcondt{2} 2
      · intro σ₁
        hoare_auto
      ec_auto
    -- EC: by rcondf{2} 2; auto=> />; smt(dbool_ll).
    · stmt_rcondf{2} 2
      · intro σ₁
        hoare_auto
      ec_auto; ec_progress
      exact (is_lossless_iff_expected _).mp dbool_ll
  -- EC: by auto.
  ec_auto

/-- The list step of `eq_eager_ideal2`'s second loop (EC's `smt(cats1 take_cat cats0 take_size)`,
twice). -/
private theorem take_rcons_le {α : Type} (k : ℤ) (bs : List α) (b : α) (h : k ≤ size bs) :
    take k (rcons bs b) = take k bs := by
  change take k (bs ++ [b]) = take k bs
  rw [take_cat]
  split_ifs with hlt
  · rfl
  · rw [show k = size bs by omega, take_size, sub_self, take0, cats0]

set_option maxHeartbeats 4000000 in
-- one declaration: the two cases, five loops
/-- EC's `local equiv eq_eager_ideal2 :
ExtendSample(FSome(BIRO.IRO)).f ~ FSome(Fill_In(RO)).f :
={arg} /\ BIRO.IRO.mp{1} = RO.m{2} ==> ={res} /\ BIRO.IRO.mp{1} = RO.m{2}`. -/
theorem eq_eager_ideal2 :
    equiv[ ExtendSample(FSome(IRO.asF)).f (x) ~ FSome(Fill_In(Eager.RO)).f (x) :
      ={x} ∧ §IRO.mp{1} = §Eager.RO.m{2} ==> ={res} ∧ §IRO.mp{1} = §Eager.RO.m{2} ] := by
  -- EC: proc; inline*; sp.
  equiv_proc; stmt_inline*; stmt_sp
  -- EC: if{1}; sp.
  stmt_if{1}
  · stmt_sp
    -- EC: + rcondt{1} 1; auto=> /=/>.
    stmt_rcondt{1} 1
    · hoare_auto
    stmt_wp
    --     (`x1`{1}, `x0`{2} are also names of the other side or of the precondition at another
    --     type: written with their lenses below, GAP 2; EC's `x2`{1} is `x1`)
    -- EC: conseq(:_==> take k{1} bs{1} = l{2} /\ BIRO.IRO.mp{1} = RO.m{2}).
    equiv_conseq (: _ ==> take §k{1} §bs{1} = §l{2} ∧ §IRO.mp{1} = §Eager.RO.m{2})
    --     * by move=> /> /#.
    · ec_close
    -- EC: case: (0 <= n{2}); last first.
    equiv_case (0 ≤ §n{2})
    swap
    -- EC: + rcondf{2} 1; 1: by auto; smt().
    · stmt_rcondf{2} 1
      · intro σ₁
        hoare_auto; ec_close
      -- EC: conseq(:_==> BIRO.IRO.mp{1} = RO.m{2} /\ ={i} /\ n{1} = size_out /\
      --       x2{1} = x0{2})=> />.
      equiv_conseq (: _ ==> §IRO.mp{1} = §Eager.RO.m{2} ∧ ={i} ∧ §n{1} = size_out ∧
        §(localVarLens "x1" (List Bool)){1} = §(localVarLens "x0" (List Bool)){2})
      --     - smt(take_le0).
      · ec_progress
        exact take_le0 _ _ (le_of_lt ‹xn₂.2 < 0›)
      -- EC: while(={i} /\ x2{1} = x0{2} /\ n{1} = size_out /\ BIRO.IRO.mp{1} = RO.m{2}).
      equiv_while (={i} ∧
        §(localVarLens "x1" (List Bool)){1} = §(localVarLens "x0" (List Bool)){2} ∧
        §n{1} = size_out ∧ §IRO.mp{1} = §Eager.RO.m{2})
      -- EC: - sp; if{1}.
      · stmt_sp
        stmt_if{1}
        --   - by rcondt{2} 2; auto=> />.
        · stmt_rcondt{2} 2
          · intro σ₁
            hoare_auto
          ec_auto
        --   by rcondf{2} 2; auto=> />; smt(dbool_ll).
        · stmt_rcondf{2} 2
          · intro σ₁
            hoare_auto
          ec_auto; ec_progress
          exact (is_lossless_iff_expected _).mp dbool_ll
      -- EC: by auto=> />.
      ec_auto
    -- EC: splitwhile{1} 1 : i < k.
    --     (`k` is no variable of the statement after `wp`: written with its lens, GAP 2)
    stmt_splitwhile{1} 1 : §i < §(localVarLens "k" ℤ)
    -- EC: while(={i} /\ n{1} = size_out /\ x2{1} = x0{2} /\  BIRO.IRO.mp{1} = RO.m{2} /\
    --       take k{1} bs{1} = l{2} /\ size bs{1} = i{1} /\ k{1} <= i{1} <= size_out).
    equiv_while (={i} ∧ §n{1} = size_out ∧
      §(localVarLens "x1" (List Bool)){1} = §(localVarLens "x0" (List Bool)){2} ∧
      §IRO.mp{1} = §Eager.RO.m{2} ∧ take §k{1} §bs{1} = §l{2} ∧ size §bs{1} = §i{1} ∧
      §k{1} ≤ §i{1} ∧ §i{1} ≤ size_out)
    -- EC: * sp; if{1}.
    · stmt_sp
      stmt_if{1}
      --   - by rcondt{2} 2; auto=> />; smt(dbool_ll cats1 take_cat cats0 take_size size_rcons).
      · stmt_rcondt{2} 2
        · intro σ₁
          hoare_auto
        ec_auto; ec_progress
        · exact take_rcons_le _ _ _ (by rw [‹size bs₁ = _›]; exact ‹k₁ ≤ _›)
        · rw [size_rcons, ‹size bs₁ = _›]
      --   by rcondf{2} 2; auto=> />; smt(dbool_ll cats1 take_cat cats0 take_size size_rcons).
      · stmt_rcondf{2} 2
        · intro σ₁
          hoare_auto
        ec_auto; ec_progress
        · exact (is_lossless_iff_expected _).mp dbool_ll
        · exact take_rcons_le _ _ _ (by rw [‹size bs₁ = _›]; exact ‹k₁ ≤ _›)
        · rw [size_rcons, ‹size bs₁ = _›]
    -- EC: conseq(:_==> ={i} /\ n{1} = size_out /\ x2{1} = x0{2} /\  BIRO.IRO.mp{1} = RO.m{2} /\
    --       bs{1} = l{2} /\ size bs{1} = i{1} /\ k{1} = i{1}).
    equiv_conseq (: _ ==> ={i} ∧ §n{1} = size_out ∧
      §(localVarLens "x1" (List Bool)){1} = §(localVarLens "x0" (List Bool)){2} ∧
      §IRO.mp{1} = §Eager.RO.m{2} ∧ §bs{1} = §l{2} ∧ size §bs{1} = §i{1} ∧ §k{1} = §i{1})
    --     + smt(take_size).
    · ec_progress
      exact take_oversize _ _ (le_of_eq ‹size l₂1 = _›)
    -- EC: while(={i} /\ x2{1} = x0{2} /\ n{1} = size_out /\ k{1} = n{2} /\
    --       0 <= i{1} <= k{1} <= size_out /\ bs{1} = l{2} /\ size bs{1} = i{1} /\
    --       BIRO.IRO.mp{1} = RO.m{2}).
    equiv_while (={i} ∧
      §(localVarLens "x1" (List Bool)){1} = §(localVarLens "x0" (List Bool)){2} ∧
      §n{1} = size_out ∧ §k{1} = §n{2} ∧ 0 ≤ §i{1} ∧ §i{1} ≤ §k{1} ∧ §k{1} ≤ size_out ∧
      §bs{1} = §l{2} ∧ size §bs{1} = §i{1} ∧ §IRO.mp{1} = §Eager.RO.m{2})
    -- EC: + sp; if{1}.
    · stmt_sp
      stmt_if{1}
      --   - by rcondt{2} 2; auto=> />; smt(size_rcons).
      · stmt_rcondt{2} 2
        · intro σ₁
          hoare_auto
        ec_auto; ec_progress
        · rw [size_rcons, ‹size l₂ = _›]
        · have hn := ‹n₂ ≤ size_out›
          by_cases h : x1₂.2 + 1 < n₂
          · simp [h, show x1₂.2 + 1 < size_out by omega]
          · simp [h]
      --   by rcondf{2} 2; auto=> />; smt(size_rcons dbool_ll).
      · stmt_rcondf{2} 2
        · intro σ₁
          hoare_auto
        ec_auto; ec_progress
        · exact (is_lossless_iff_expected _).mp dbool_ll
        · rw [size_rcons, ‹size l₂ = _›]
        · have hn := ‹n₂ ≤ size_out›
          by_cases h : x1₂.2 + 1 < n₂
          · simp [h, show x1₂.2 + 1 < size_out by omega]
          · simp [h]
    -- EC: by auto=> />; smt(size_ge0 size_out_gt0).
    ec_auto; ec_progress
    have h0 : (0 : ℤ) < size_out := GaudisCrypt.SHA3.SHA3OSecurity.Params.size_out_gt0
    simp [h0]
  · stmt_sp
    -- EC: rcondt{1} 1; auto.
    stmt_rcondt{1} 1
    · hoare_auto
    stmt_wp
    -- EC: rcondf{2} 2; 1: auto.
    --     + conseq(:_==> i = n)=> [/> /#|].
    --       by while(i <= n); auto=> />; smt(size_out_gt0).
    stmt_rcondf{2} 2
    · intro σ₁
      --     (GAP 1: `n`, which the loop does not write, is kept by the invariant)
      hoare_while (§i ≤ §n ∧ size_out < §n)
      · hoare_auto
      · ec_progress
      · hoare_auto; ec_progress
        have h0 : (0 : ℤ) < size_out := GaudisCrypt.SHA3.SHA3OSecurity.Params.size_out_gt0
        have h1 := ‹size_out < _›
        have h2 := ‹_ = v.2›
        omega
    -- EC: while(i0{1} = i{2} /\ x3{1} = x0{2} /\ n0{1} = n{2} /\ bs0{1} = l{2} /\
    --       BIRO.IRO.mp{1} = RO.m{2}).
    equiv_while (§i0{1} = §i{2} ∧ §x4{1} = §x0{2} ∧ §n1{1} = §n{2} ∧ §bs0{1} = §l{2} ∧
      §IRO.mp{1} = §Eager.RO.m{2})
    -- EC: + sp; if{1}.
    · stmt_sp
      stmt_if{1}
      --   - by rcondt{2} 2; auto=> />.
      · stmt_rcondt{2} 2
        · intro σ₁
          hoare_auto
        ec_auto
      --   by rcondf{2} 2; auto; smt(dbool_ll).
      · stmt_rcondf{2} 2
        · intro σ₁
          hoare_auto
        ec_auto; ec_progress
        exact (is_lossless_iff_expected _).mp dbool_ll
    -- EC: by auto=> />.
    ec_auto

-- EC's local `module Dist (F : RO)`, `proc distinguish = OIndif(…).main`, with the section's `A`
-- a Lean parameter; the alias is wrapped in a call (E5), and `distinguish` takes
-- `RO_Distinguisher`'s `unit` (`RO_LRO_D Dist`)
set_option linter.gaudisCrypt.using false in
module Dist (A : SH.AdvPreimage) using (F : Eager.RO_T) {
  proc distinguish (_x : Unit) : Bool {
    var b : Bool;
    b <- call OIndif(FSome(Fill_In(F)), OSimulator(FSome(Fill_In(F))),
      ODRestr(Dist_of_P1Adv(A))).main ();
    return $b
  };
}

-- EC's local `module Game (F : RO)`, with the section's `A` a Lean parameter
set_option linter.gaudisCrypt.using false in
module Game (A : SH.AdvPreimage) using (F : Eager.RO_T) {
  proc distinguish () : Bool {
    var bo : Bool;
    _ <- call OSimulator(FSome(Fill_In(F))).init ();
    Counter.c <- 0;
    Log.m <- (FMap.empty : FMap (List Bool × ℤ) Bool);
    _ <- call F.init ();
    bo <- call Dist(A, F).distinguish (());
    return $bo
  };
}

/-- `RFList`'s `get` as the oracle games call it (behind the module type's record) touches
`RFList.m` only (EC reads the globals off the code). -/
@[fp_bound] theorem fvP_RF_T_get_RFList :
    FVP.fvP (SORO.RF_T.get RFList) ≤ RFList.m.footprint := by
  fp_module RFList.m

/-- `RFWhile`'s `get` as the oracle games call it touches `RFList.m` only. -/
@[fp_bound] theorem fvP_RF_T_get_RFWhile :
    FVP.fvP (SORO.RF_T.get RFWhile) ≤ RFList.m.footprint := by
  fp_module RFList.m

/-- The clone `SORO`'s `Bounder` touches `SORO.Bounder.bounder` only (EC reads the globals off
the code). -/
@[fp_bound] theorem fvP_SORO_Bounder : FVP.fvP SORO.Bounder ≤ SORO.Bounder.bounder.footprint := by
  fp_module SORO.Bounder.bounder

/-- `RFWhile` touches `RFList.m` only. -/
@[fp_bound] theorem fvP_RFWhile : FVP.fvP RFWhile ≤ RFList.m.footprint := by
  fp_module RFList.m

/-- `PSome(Perm)` in a game of the clone `SH` (at the clone's module type, where `inline` does
not see the first port's record): its `init` is the sponge-level one, by definition. -/
theorem PSome_Perm_init (P : SH.OIndif.OPRIMITIVE) (hP : P = PSome Perm) :
    @GaudisCrypt.SHA3.Pilot.SecureHash.OIndif.OPRIMITIVE.init (List Bool) f_out SHA3Indiff.state
        _ _ _ SH.params P =
      GaudisCrypt.SHA3.OptionIndifferentiability.OPRIMITIVE.init SHA3Indiff.state (List Bool × ℤ)
        (List Bool) (PSome Perm) := by
  subst hP
  rfl

/-- EC's `OSponge(P) = FSetSize(CSome(Sponge, P))`, unfolded: `FSetSize(FSome(Sponge(Poget(P))))`
at the sponge's module types (`OSponge` is a composition at the clone `SH`'s, where `inline`
does not open the sponge's functors). -/
theorem OSponge_app (P : ODPRIMITIVE) :
    Module.app OSponge P =
      Module.app FSetSize (Module.app FSome (Module.app Sponge (Module.app Poget P))) := by
  unfold OSponge CSome
  erw [Module.app_comp, Module.app_comp, Module.app_comp]
  rfl

/-- A sponge-level primitive used as a `DPRIMITIVE` of the clone `SH` (in `SH.Preimage`, for
`OSponge`) is the same module used as the sponge's (EC's module types are structural): the two
coercions build it with the two module types' projections. -/
theorem OPRIMITIVE_coe_eq (P : OPRIMITIVE) :
    (SH.OIndif.ODPRIMITIVE.mk { f := SH.OIndif.OPRIMITIVE.f P, fi := SH.OIndif.OPRIMITIVE.fi P } :
        SH.OIndif.ODPRIMITIVE) =
      (((P : ODPRIMITIVE)) : SH.OIndif.ODPRIMITIVE) :=
  rfl

set_option maxHeartbeats 10000000 in
-- `fp_module` through `SORO_P1`'s nest of oracles
/-- `SORO_P1(A)` touches `A`'s variables, `Log.m`, `Counter.c`, the simulator's maps and
`Gconcl_list.BIRO2.IRO.mp` (EC reads the globals off the code). -/
@[fp_bound] theorem fvP_SORO_P1 (A : SH.AdvPreimage) :
    FVP.fvP (SORO_P1 A) ≤ FVP.fvP A ⊔ (Log.m.footprint ⊔ (Counter.c.footprint ⊔
      (Simulator.m.footprint ⊔ (Simulator.mi.footprint ⊔ (Simulator.paths.footprint ⊔
        Gconcl_list.BIRO2.IRO.mp.footprint))))) := by
  have h : FVP.fvP (SORO_P1 A) ≤ FVP.fvP A ⊔ (Lens.pair Log.m (Lens.pair Counter.c
      (Lens.pair Simulator.m (Lens.pair Simulator.mi (Lens.pair Simulator.paths
        Gconcl_list.BIRO2.IRO.mp))))).footprint := by
    fp_module (Lens.pair Log.m (Lens.pair Counter.c (Lens.pair Simulator.m
      (Lens.pair Simulator.mi (Lens.pair Simulator.paths Gconcl_list.BIRO2.IRO.mp)))))
  simpa only [Footprint.lens_pair] using h

set_option maxHeartbeats 4000000 in
-- `fp_module` through the adversary's oracles
/-- `Dist_of_P1Adv(A)` touches `A`'s variables and `Log.m` (EC reads the globals off the code). -/
@[fp_bound] theorem fvP_Dist_of_P1Adv (A : SH.AdvPreimage) :
    FVP.fvP (Dist_of_P1Adv A) ≤ FVP.fvP A ⊔ Log.m.footprint := by
  fp_module Log.m

set_option synthInstance.checkSynthOrder false in
/-- EC's `glob Dist_of_P1Adv(A)`: `glob A` (the region given for `A`) and `Log.m`. -/
instance instECGlobDist_of_P1Adv (A : SH.AdvPreimage) {R : Footprint VariableAssignment}
    [h : Module.ECGlob A R] : Module.ECGlob (Dist_of_P1Adv A) (R ⊔ Log.m.footprint) := by
  obtain ⟨GF, hGF, hRGF⟩ := h.base
  exact ⟨(h.finite.sup (by fp_finite)).mono (fvP_Dist_of_P1Adv A),
    (fvP_Dist_of_P1Adv A).trans (sup_le_sup_right h.le _),
    ⟨GF ⊔ Log.m.footprint, hGF.sup (by fp_finite),
      sup_le (hRGF.trans (Footprint.glob_mono le_sup_left))
        (Footprint.le_glob_of_le le_sup_right)⟩⟩

section

-- EC: declare module A <: SH.AdvPreimage {-Perm, -Counter, -Bounder, -F.RO, -F.FRO, -Redo, -C,
--   -Gconcl.S, -BlockSponge.BIRO.IRO, -BlockSponge.C, -BIRO.IRO, -Gconcl_list.BIRO2.IRO,
--   -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO, -Gconcl_list.Simulator, -SHA3Indiff.Simulator,
--   -SHA3Indiff.Cntr, -SORO.Bounder, -SORO.RO.RO, -RO, -FRO}.
-- (and the variables of local modules, fresh in EC: the section's `Log.m`, `RFList.m`,
-- `SORO.Preimage.Preimage2` of the lemma `RO_is_preimage_resistant` applied to `SORO_P1(A)`, and
-- those of `Pilot/SHA3_OIndiff.lean`'s `SHA3OIndiff`, applied to `Dist_of_P1Adv(A)`)
declare module A <: SH.AdvPreimage {-Perm, -Counter, -SH.Bounder, -SLCommon.F.RO,
  -SLCommon.F.FRO, -SLCommon.Redo, -SLCommon.C, -Gconcl.S, -BlockSponge.BIRO.IRO,
  -BlockSponge.C, -IRO, -Gconcl_list.BIRO2.IRO, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
  -Gconcl_list.Simulator, -Simulator, -Cntr, -SORO.Bounder, -SORO.RO, -SORO.FRO,
  -Eager.RO.m, -Eager.FRO.m, -Log.m, -RFList.m, -SORO.Preimage.Preimage2,
  -Gconcl_list.SimLast, -OSimulator,
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
-- one declaration: EC's two `have`s, each a `byequiv` through the adversary's oracles
/-- EC's `local lemma eager_ideal &m`. -/
theorem eager_ideal (m : VariableAssignment) :
    Pr[ OIndif(FSome(IRO.asF), OSimulator(FSome(IRO.asF)),
        ODRestr(Dist_of_P1Adv(A))).main () @ &m : §res ] =
    Pr[ OIndif(ExtendSample(FSome(IRO.asF)), OSimulator(ExtendSample(FSome(IRO.asF))),
        ODRestr(Dist_of_P1Adv(A))).main () @ &m : §res ] := by
  -- EC: have->:
  --       Pr[SHA3_OIndiff.OIndif.OIndif(FSome(BIRO.IRO), OSimulator(FSome(BIRO.IRO)),
  --         ODRestr(Dist_of_P1Adv(A))).main() @ &m : res] =
  --       Pr[Game(LRO).distinguish() @ &m : res].
  have h1 : Pr[ OIndif(FSome(IRO.asF), OSimulator(FSome(IRO.asF)),
        ODRestr(Dist_of_P1Adv(A))).main () @ &m : §res ] =
      Pr[ Game(A, Eager.LRO).distinguish () @ &m : §res ] := by
    -- EC: + byequiv=> //=; proc.
    --       inline{2} 1; sp; inline{2} 1; sp; inline{2} 1; sp; inline{2} 1; sp.
    --       inline{1} 1; inline{2} 1; sp.  (six times)
    --       inline{1} 1; inline{2} 1; sp; sim 3 3.
    --     (both games inlined up to the adversary's call; EC's `sim 3 3` is `wp`)
    byequiv; equiv_proc
    repeat stmt_inline{1} 0
    repeat stmt_inline{2} 0
    stmt_sp
    stmt_wp
    -- EC: seq 2 2 : (={hash, m, glob OFC} /\ BIRO.IRO.mp{1} = RO.m{2}); last first.
    equiv_seq 2 2 : (={hash, m, Counter.c} ∧ §IRO.mp{1} = §Eager.RO.m{2})
    swap
    -- EC: - inline{1} 1; inline{2} 1; sp; sim 1 1.
    --       inline{1} 1; inline{2} 1; sp; sim 1 1; if; auto.
    --       inline{1} 1; inline{2} 1; sp; sim 1 1.
    --       by call eq_eager_ideal; auto.
    · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_wp
      stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_wp
      stmt_if
      · ec_close
      · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_wp
        equiv_call eq_eager_ideal
        ec_auto
      · ec_auto
    -- EC: call(: ={glob OFC, glob OSimulator} /\ BIRO.IRO.mp{1} = RO.m{2}); auto.
    equiv_call (_ : ={Counter.c, Simulator.m, Simulator.mi, Simulator.paths,
      Gconcl_list.BIRO2.IRO.mp} ∧ §IRO.mp{1} = §Eager.RO.m{2})
    -- EC: - proc; sp; if; auto.
    --     (GAP 3: the primitive's `f` behind the first port's constructor)
    · simp only [ODPRIMITIVE_f_mk]
      equiv_proc; stmt_sp
      stmt_if
      · ec_close
      -- EC: inline{1} 1; inline{2} 1; sp; sim 1 1.
      · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_wp
        -- EC: if; [1,3:by auto]; sim 1 1.
        stmt_if
        · ec_close
        · stmt_wp
          -- EC: if; [1,3:by auto|2:sim 4 4]; sp.
          stmt_if
          · ec_close
          · sim 4 4
            stmt_sp
            -- EC: if; [1:by auto=> /> &1 &2 <- /> <- />|2:sim 1 1|3:sim].
            stmt_if
            · ec_close
            -- EC: * inline{1} 1; inline{2} 1; sp; sim 1 1.
            --       by call eq_eager_ideal; auto=> /> &1 &2 <- /> <- />.
            · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_wp
              equiv_call eq_eager_ideal
              ec_auto; ec_close
            -- EC: by move=> /> &1 &2 <- /> <- />.
            · sim; ec_close
          · ec_auto
        · ec_auto
      · ec_auto
    -- EC: - by proc; inline*; sim.
    · simp only [ODPRIMITIVE_fi_mk]
      equiv_proc; stmt_inline*; sim
    -- EC: proc; sim 1 1.
    --     inline{1} 1; inline{2} 1; sp; sim 1 1.
    · equiv_proc; stmt_wp
      stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_wp
      -- EC: if; [1,3:by auto]; sim 1 1.
      stmt_if
      · ec_close
      -- EC: inline{1} 1; inline{2} 1; sp; sim 1 1.
      --     by call eq_eager_ideal; auto.
      · stmt_wp
        stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_wp
        equiv_call eq_eager_ideal
        ec_auto
      · ec_auto
    --     (GAP 4: `glob A` past the initializations' writes, from the two memories' equation)
    ec_auto; ec_progress
    have h := congrArg (FVP.fvP A).touched_getter.get ‹Simulator.m.set _ _ = _›
    simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at h
    exact h
  -- EC: have->:
  --       Pr[SHA3_OIndiff.OIndif.OIndif(ExtendSample(FSome(BIRO.IRO)),
  --         OSimulator(ExtendSample(FSome(BIRO.IRO))),
  --         ODRestr(Dist_of_P1Adv(A))).main() @ &m : res] =
  --       Pr[Game(RO).distinguish() @ &m : res].
  have h2 : Pr[ OIndif(ExtendSample(FSome(IRO.asF)), OSimulator(ExtendSample(FSome(IRO.asF))),
        ODRestr(Dist_of_P1Adv(A))).main () @ &m : §res ] =
      Pr[ Game(A, Eager.RO).distinguish () @ &m : §res ] := by
    -- EC: + byequiv=> //=; proc.
    --       inline{2} 1; sp; inline{2} 1; sp; inline{2} 1; sp; inline{2} 1; sp.
    --       inline{1} 1; inline{2} 1; sp.  (six times)
    --       inline{1} 1; inline{2} 1; sp; sim 3 3.
    --     (both games inlined up to the adversary's call; EC's `sim 3 3` is `wp`)
    byequiv; equiv_proc
    repeat stmt_inline{1} 0
    repeat stmt_inline{2} 0
    stmt_sp
    stmt_wp
    -- EC: seq 2 2 : (={hash, m, glob OFC} /\ BIRO.IRO.mp{1} = RO.m{2}); last first.
    equiv_seq 2 2 : (={hash, m, Counter.c} ∧ §IRO.mp{1} = §Eager.RO.m{2})
    swap
    -- EC: - inline{1} 1; inline{2} 1; sp; sim 1 1.
    --       inline{1} 1; inline{2} 1; sp; sim 1 1.
    --       by if; auto; call eq_eager_ideal2; auto.
    · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_wp
      stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_wp
      stmt_if
      · ec_close
      · stmt_wp
        equiv_call eq_eager_ideal2
        ec_auto
      · ec_auto
    -- EC: call(: ={glob OFC, glob OSimulator} /\ BIRO.IRO.mp{1} = RO.m{2}); auto.
    equiv_call (_ : ={Counter.c, Simulator.m, Simulator.mi, Simulator.paths,
      Gconcl_list.BIRO2.IRO.mp} ∧ §IRO.mp{1} = §Eager.RO.m{2})
    -- EC: - proc; sp; if; auto.
    --     (GAP 3: the primitive's `f` behind the first port's constructor)
    · simp only [ODPRIMITIVE_f_mk]
      equiv_proc; stmt_sp
      stmt_if
      · ec_close
      -- EC: inline{1} 1; inline{2} 1; sp; sim 1 1.
      · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_wp
        -- EC: if; [1,3:by auto]; sim 1 1.
        stmt_if
        · ec_close
        · stmt_wp
          -- EC: if; [1,3:by auto]; sim 4 4; sp.
          stmt_if
          · ec_close
          · sim 4 4
            stmt_sp
            -- EC: if; [1:by auto=> /> &1 &2 <- /> <- />|2:sim 1 1|3:sim].
            stmt_if
            · ec_close
            -- EC: * by call eq_eager_ideal2; auto=> /> &1 &2 <- /> <- />.
            · stmt_wp
              equiv_call eq_eager_ideal2
              ec_auto; ec_close
            -- EC: by move=> /> &1 &2 <- /> <- />.
            · sim; ec_close
          · ec_auto
        · ec_auto
      · ec_auto
    -- EC: - by proc; inline*; sim.
    · simp only [ODPRIMITIVE_fi_mk]
      equiv_proc; stmt_inline*; sim
    -- EC: proc; sim 1 1.
    --     inline{1} 1; inline{2} 1; sp; sim 1 1.
    · equiv_proc; stmt_wp
      stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_wp
      -- EC: if; [1,3:by auto]; sim 1 1.
      stmt_if
      · ec_close
      -- EC: by call eq_eager_ideal2; auto.
      · stmt_wp
        equiv_call eq_eager_ideal2
        ec_auto
      · ec_auto
    --     (GAP 4: `glob A` past the initializations' writes, from the two memories' equation)
    ec_auto; ec_progress
    have h := congrArg (FVP.fvP A).touched_getter.get ‹Simulator.m.set _ _ = _›
    simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at h
    exact h
  rw [h1, h2]
  -- EC: rewrite eq_sym; byequiv=> //=; proc.
  symm
  byequiv; equiv_proc
  -- EC: call(RO_LRO_D Dist _); first by rewrite dbool_ll.
  equiv_call (Eager.RO_LRO_D (Dist A))
  -- EC: by inline*; auto=> />.
  stmt_inline*; ec_auto

set_option maxHeartbeats 40000000 in
-- one declaration: EC's three `have`s and its last `byequiv`
/-- EC's `local lemma rw_ideal_2 &m`. -/
theorem rw_ideal_2 (m : VariableAssignment) :
    Pr[ OIndif(FSome(IRO.asF), OSimulator(FSome(IRO.asF)),
        ODRestr(Dist_of_P1Adv(A))).main () @ &m : §res ] ≤
    Pr[ SORO.Preimage(SORO_P1(A), RFList).main () @ &m : §res ] := by
  -- EC: have->:Pr[SORO.Preimage(SORO_P1(A), RFList).main() @ &m : res] =
  --       Pr[SORO.Preimage(SORO_P1(A), RFWhile).main() @ &m : res].
  have h1 : Pr[ SORO.Preimage(SORO_P1(A), RFList).main () @ &m : §res ] =
      Pr[ SORO.Preimage(SORO_P1(A), RFWhile).main () @ &m : §res ] := by
    -- EC: + byequiv(: ={glob A} ==> _)=>//=; proc.
    byequiv; equiv_proc
    -- EC: swap 1.
    stmt_swap 1
    -- EC: inline{1} 1; inline{2} 1; sp.
    --     inline{1} 1; inline{2} 1; sp.
    --     inline{1} 2; inline{2} 2; sp.
    stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
    stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
    stmt_inline{1} 0; stmt_inline{2} 0
    -- EC: swap[1..2] 3; sp.
    stmt_swap{1} [1..2] 3; stmt_swap{2} [1..2] 3; stmt_sp
    -- EC: inline{1} 1; inline{2} 1; sp.
    --     inline{1} 1; inline{2} 1; sp.
    stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
    stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
    -- EC: inline{1} 5; inline{2} 5; wp.
    stmt_inline{1} 1; stmt_inline{2} 1; stmt_wp
    -- EC: seq 3 3 : (={mi, h, hash, glob A, glob SORO.Bounder, glob RFList}); last first.
    equiv_seq 3 3 : (={mi, h, hash, glob A, SORO.Bounder.bounder, RFList.m})
    swap
    -- EC: - sp; if; auto; call(rw_RF_List_While); auto.
    · stmt_sp
      stmt_if
      · ec_close
      · equiv_call rw_RF_List_While; ec_auto
      · ec_auto
    -- EC: call(: ={glob SORO.Bounder, glob RFList, glob OSimulator, glob OPC, glob Log}); auto.
    --     (GAP 5: the invariant in two parts — the form `(_ : ={x₁, …})` puts `={glob A}` into
    --     the oracles' judgments, where the steps below do not end)
    equiv_call (_ : ={SORO.Bounder.bounder, RFList.m} ∧ ={Simulator.m, Simulator.mi,
      Simulator.paths, Gconcl_list.BIRO2.IRO.mp, Counter.c, Log.m})
    -- EC: - proc; sp; if; auto.
    · equiv_proc; stmt_sp
      stmt_if
      · ec_close
      -- EC: inline{1} 1; inline{2} 1; sp; if; [1,3:by auto]; sim 1 1.
      · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
        stmt_if
        · ec_close
        · sim 1 1
          -- EC: if; [1,3:by auto]; sim 4 4.
          stmt_if
          · ec_close
          · sim 4 4
            -- EC: sp; if; [1:by auto=> /> &1 &2 <- /> <- />|2:sim 3 3|3:sim].
            stmt_sp
            stmt_if
            · ec_close
            · sim 3 3
              -- EC: + inline{1} 1; inline{2} 1; sp; sim 1 1.
              --       inline{1} 1; inline{2} 1; sp; if; auto=> />.
              stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; sim 1 1
              stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
              stmt_if
              · ec_close
              --       - by call(rw_RF_List_While); auto=> /> &1 &2 <- /> <- />.
              · stmt_wp; equiv_call rw_RF_List_While; ec_auto; ec_close
              --       by move=> /> &1 &2 <- /> <- />.
              · ec_auto; ec_close
            -- EC: by move=> /> &1 &2 <- /> <- />.
            · sim; ec_close
          · ec_auto
        · ec_auto
      · ec_auto
    -- EC: - by sim.
    · equiv_proc; sim
    -- EC: proc; sim 1 1.
    --     inline{1} 1; inline{2} 1; sp; if; auto.
    · equiv_proc; sim 1 1
      stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
      stmt_if
      · ec_close
      -- EC: inline{1} 1; inline{2} 1; sp; sim 1 1.
      --     inline{1} 1; inline{2} 1; sp; if; auto; sim 2 2.
      --     by call(rw_RF_List_While); auto.
      · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; sim 1 1
        stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
        stmt_if
        · ec_close
        · sim 2 2; equiv_call rw_RF_List_While; ec_auto
        · ec_auto
      · ec_auto
    --     (GAP 4: `glob A` past the initializations' writes, from the two memories' equation)
    ec_auto; ec_progress
    have h := congrArg (FVP.fvP A).touched_getter.get ‹SORO.Bounder.bounder.set _ _ = _›
    simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at h
    exact h
  -- EC: rewrite (eager_ideal &m).
  rw [h1, eager_ideal A m]; clear h1
  -- EC: have->:Pr[SHA3_OIndiff.OIndif.OIndif(ExtendSample(FSome(BIRO.IRO)),
  --         OSimulator(ExtendSample(FSome(BIRO.IRO))),
  --          ODRestr(Dist_of_P1Adv(A))).main() @ &m : res] =
  --       Pr[SHA3_OIndiff.OIndif.OIndif(ExtendSample(FSome(BIRO.IRO)),
  --         OSimulator(ExtendOutputSize(FSetSize(FSome(BIRO.IRO)))),
  --         ODRestr(Dist_of_P1Adv(A))).main() @ &m : res].
  have h3 : Pr[ OIndif(ExtendSample(FSome(IRO.asF)), OSimulator(ExtendSample(FSome(IRO.asF))),
        ODRestr(Dist_of_P1Adv(A))).main () @ &m : §res ] =
      Pr[ OIndif(ExtendSample(FSome(IRO.asF)),
        OSimulator(ExtendOutputSize(FSetSize(FSome(IRO.asF)))),
        ODRestr(Dist_of_P1Adv(A))).main () @ &m : §res ] := by
    -- EC: + byequiv=> //=; proc; inline*; sp.
    byequiv; equiv_proc
    stmt_inline*; stmt_sp
    -- EC: seq 2 2 : (={m, hash, glob OSimulator, glob OFC} /\
    --       eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2}); last first.
    equiv_seq 2 2 : (={m, hash, Simulator.m, Simulator.mi, Simulator.paths,
      Gconcl_list.BIRO2.IRO.mp, Counter.c} ∧ eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log.m{2})
    swap
    · stmt_sp
      stmt_if
      · ec_close
      · stmt_sp
        stmt_if
        · ec_close
        · stmt_sp
          stmt_rcondt{1} 1
          · hoare_auto
          stmt_rcondt{2} 1
          · intro σ₁
            hoare_auto
          stmt_wp
          equiv_while (={i, n, bs, x3} ∧ size §bs{1} = §i{1} ∧
            eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log.m{2} ∧ §n{1} = size_out ∧ 0 ≤ §i{1} ∧
            §i{1} ≤ §n{1})
          · stmt_sp; stmt_if
            · ec_progress
              simp [GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_dom_lt
                ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ size bs₂› ‹size bs₂ < size_out›]
            · ec_auto; ec_progress
              · rw [size_rcons]
              · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_lt a
                  ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ size bs₂› ‹size bs₂ < size_out›).1 _ _
                  ⟨‹0 ≤ j›, ‹j < size_out›⟩
              · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_lt a
                  ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ size bs₂› ‹size bs₂ < size_out›).2.1 _ _
                  ‹size_out ≤ j›
              · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_lt
                  (m2 := mp₂) a ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ size bs₂›
                  ‹size bs₂ < size_out›).2.2 _ _ ‹_›
            · ec_auto; ec_progress
              · rw [(‹eq_extend_size mp₁ mp₂ m₂›).1 _ _ ⟨‹0 ≤ size bs₂›, ‹size bs₂ < size_out›⟩]
              · rw [size_rcons]
          ec_auto; ec_progress
          exact GaudisCrypt.SHA3.SHA3OSecurity.Params.size_out_gt0.le
        · stmt_sp
          stmt_rcondt{1} 1
          · hoare_auto
          stmt_rcondt{2} 1
          · intro σ₁
            hoare_auto
          stmt_wp
          equiv_while (={i0, n1})
          · stmt_sp
            stmt_if{1}
            · stmt_if{2}
              · ec_auto
              · ec_auto; ec_progress
                exact (is_lossless_iff_expected _).mp dbool_ll
            · stmt_if{2}
              · ec_auto; ec_progress
                exact (is_lossless_iff_expected _).mp dbool_ll
              · ec_auto
          ec_auto
      · ec_auto
    -- EC: call(: ={glob OSimulator, glob OFC} /\
    --       eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2}); last first; auto.
    equiv_call (_ : ={Simulator.m, Simulator.mi, Simulator.paths, Gconcl_list.BIRO2.IRO.mp,
      Counter.c} ∧ eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log.m{2})
    · simp only [ODPRIMITIVE_f_mk]
      equiv_proc; stmt_sp
      stmt_if
      · ec_close
      · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
        stmt_if
        · ec_close
        · stmt_if
          · ec_close
          · stmt_sp
            stmt_if
            · ec_close
            · stmt_wp; equiv_rnd; stmt_wp
              equiv_call eq_extend; ec_auto; ec_close
            · sim; ec_close
          · ec_auto
        · ec_auto
      · ec_auto
    · simp only [ODPRIMITIVE_fi_mk]
      equiv_proc; stmt_sp
      stmt_if
      · ec_close
      · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
        stmt_if
        · ec_close
        · ec_auto
        · ec_auto
      · ec_auto
    · equiv_proc
      stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
      stmt_if
      · ec_close
      · stmt_inline*; stmt_sp
        stmt_rcondt{1} 1
        · hoare_auto
        stmt_rcondt{2} 1
        · intro σ₁
          hoare_auto
        stmt_sp
        stmt_rcondt{1} 1
        · hoare_auto
        stmt_rcondt{2} 1
        · intro σ₁
          hoare_auto
        stmt_wp
        equiv_conseq (: _ ==> ={bs} ∧ eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log.m{2})
        · ec_close
        equiv_while (={i, n, x3, bs} ∧ 0 ≤ §i{1} ∧ §i{1} ≤ size_out ∧ §n{1} = size_out ∧
          eq_extend_size §IRO.mp{1} §IRO.mp{2} §Log.m{2})
        · stmt_sp; stmt_if
          · ec_progress
            simp [GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_dom_lt
              ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ n0₂› ‹n0₂ < size_out›]
          · ec_auto; ec_progress
            · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_lt a
                ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ n0₂› ‹n0₂ < size_out›).1 _ _
                ⟨‹0 ≤ j›, ‹j < size_out›⟩
            · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_lt a
                ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ n0₂› ‹n0₂ < size_out›).2.1 _ _
                ‹size_out ≤ j›
            · exact (GaudisCrypt.SHA3.SHA3OSecurity.Preimage.eq_extend_size_set_lt
                (m2 := mp₂) a ‹eq_extend_size mp₁ mp₂ m₂› ‹0 ≤ n0₂›
                ‹n0₂ < size_out›).2.2 _ _ ‹_›
          · ec_auto; ec_progress
            rw [(‹eq_extend_size mp₁ mp₂ m₂›).1 _ _ ⟨‹0 ≤ n0₂›, ‹n0₂ < size_out›⟩]
        ec_auto; ec_progress
        exact GaudisCrypt.SHA3.SHA3OSecurity.Params.size_out_gt0.le
      · ec_auto
    ec_auto; ec_progress
    · have h := congrArg (FVP.fvP A).touched_getter.get ‹Simulator.m.set _ _ = _›
      simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at h
      exact h
    · have hd := ‹(IRO.mp.get globals₁).dom (x, j)›
      rw [‹IRO.mp.get globals₁ = FMap.empty›] at hd
      exact absurd hd (FMap.mem_empty _)
  rw [h3]; clear h3
  -- EC: byequiv=> //=; proc.
  byequiv
  case hE => exact fun _ _ _ _ h => h
  equiv_proc
  -- EC: inline{1} 1; inline{2} 2; sp.
  --     inline{1} 1; inline{2} 3; swap{2}[1..2]1; sp.
  --     inline{1} 1; inline{2} 3; sp.
  --     inline{1} 1; sp.
  --     inline{1} 1; sp.
  --     swap{2} 1 1; sp; swap{2}[1..2]3; sp.
  --     inline{1} 1; sp; auto.
  --     (the left game inlined down to the adversary's call; on the right the swaps of the first
  --     `have`: the first port's `OIndif` runs the simulator's `init` first, so EC's positions
  --     differ)
  repeat stmt_inline{1} 0
  stmt_swap{2} 1
  stmt_inline{2} 0; stmt_inline{2} 0; stmt_sp
  stmt_inline{2} 0
  stmt_swap{2} [1..2] 3; stmt_sp
  stmt_inline{2} 0; stmt_inline{2} 0; stmt_sp
  -- EC: seq 2 5 : (={glob A, glob OSimulator, glob Counter, glob Log, hash, m} /\
  --       inv BIRO.IRO.mp{1} RFList.m{2} /\
  --       SORO.Bounder.bounder{2} <= Counter.c{1}); last first.
  equiv_seq 2 4 : (={glob A, Simulator.m, Simulator.mi, Simulator.paths,
    Gconcl_list.BIRO2.IRO.mp, Counter.c, Log.m, m} ∧ §hash0{1} = §hash{2} ∧
    inv §IRO.mp{1} §RFList.m{2} ∧ §SORO.Bounder.bounder{2} ≤ §Counter.c{1})
  swap
  -- EC: + inline{1} 1; inline{2} 1; sp; inline{1} 1; sp; auto.
  · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_inline{1} 0; stmt_sp; stmt_wp
    -- EC: if{1}; sp; last first.
    stmt_if{1}
    swap
    -- EC: - conseq(:_==> true)=> />.
    --       inline*; if{2}; auto; sp; if{2}; auto.
    --       by while{2}(true)(size_out - i{2}); auto=>/>; smt(dbool_ll).
    · equiv_conseq (: _ ==> True)
      · ec_close
      stmt_inline*
      stmt_if{2}
      · stmt_sp
        stmt_if{2}
        · stmt_wp
          equiv_while{2} (True) ((size_out - §i{2}).toNat)
          · while_ll_phoare
            intro σ₁
            ec_auto; ec_progress
            exact (is_lossless_iff_expected _).mp dbool_ll
          · intro σ₁ k
            hoare_auto
          ec_auto
        · ec_auto
      · ec_auto
    -- EC: rcondt{2} 1; 1: by auto=> />; smt(divz_ge0 gt0_r size_ge0).
    --     (EC's `smt`: the first port's `lt_increase_counter`)
    stmt_rcondt{2} 1
    · intro σ₁
      hoare_auto; ec_progress
      exact lt_of_le_of_lt ‹bounder ≤ _› (lt_of_lt_of_le
        (GaudisCrypt.SHA3.SHA3OSecurity.lt_increase_counter _ _ _) ‹_ ≤ SHA3Indiff.limit›)
    -- EC: inline{1} 1; sp; auto.
    --     rcondt{1} 1; auto=> /=.
    stmt_inline{1} 0; stmt_sp; stmt_wp
    stmt_rcondt{1} 1
    · hoare_auto; ec_close
    -- EC: inline{1} 1; sp; auto.
    --     by call(eq_IRO_RFWhile); auto; smt(take_oversize).
    stmt_inline{1} 0; stmt_sp; stmt_wp
    equiv_call eq_IRO_RFWhile
    ec_auto; ec_progress
    have h := ‹(if _ then _ else _) = some hash₂›
    simp only [Option.map_some, ne_eq, reduceCtorEq, not_false_eq_true, if_true, oget_some] at h
    rwa [take_oversize _ _
      (le_of_eq ((‹size r₁ = size_out›).trans (‹xk₁.2 = size_out›).symm))] at h
  -- EC: auto; call(: ={glob OSimulator, glob Counter, glob Log} /\
  --       inv BIRO.IRO.mp{1} RFList.m{2} /\
  --       SORO.Bounder.bounder{2} <= Counter.c{1}); auto; last first.
  stmt_wp
  equiv_call (_ : ={Simulator.m, Simulator.mi, Simulator.paths, Gconcl_list.BIRO2.IRO.mp,
    Counter.c, Log.m} ∧ inv §IRO.mp{1} §RFList.m{2} ∧
    §SORO.Bounder.bounder{2} ≤ §Counter.c{1})
  -- EC: + proc; sp; if; auto=> />; 1: smt().
  --     (GAP 3 on the left: the primitive's `f` behind the first port's constructor)
  · simp only [ODPRIMITIVE_f_mk]
    equiv_proc; stmt_sp
    stmt_if
    · ec_close
    -- EC: inline{1} 1; inline{2} 1; sp; auto.
    --     if; 1, 3: auto; -1: smt().
    · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_wp
      stmt_if
      · ec_close
      -- EC: if; 1,3:auto=> /> + + + + + + + + + + + _ + _ /#.
      · stmt_if
        · ec_close
        -- EC: sp; if; [1:by auto=> /> &1 &2 <- /> <-]; last first.
        · stmt_sp
          stmt_if
          · ec_close
          -- EC: inline{1} 1; inline{2} 1; sp.
          --     inline{1} 1; inline{2} 1; sp.
          --     rcondt{2} 1; 1: by auto; smt().
          · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
            stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
            stmt_rcondt{2} 1
            · intro σ₁
              hoare_auto; ec_progress
              exact lt_of_le_of_lt ‹bounder ≤ _› (Int.lt_of_add_one_le ‹_ + 1 ≤ SHA3Indiff.limit›)
            -- EC: sp.
            --     seq 3 2 : (={x0, x1, o1, k0, Log.m, suffix, glob OSimulator} /\
            --       inv BIRO.IRO.mp{1} RFList.m{2} /\
            --       SORO.Bounder.bounder{2} <= Counter.c{2} + 1); last first.
            --     (and `={Counter.c}`, which the postcondition reads)
            stmt_sp
            equiv_seq 3 2 : (={x0, x1, o1, k0, Log.m, suffix, Simulator.m, Simulator.mi,
              Simulator.paths, Gconcl_list.BIRO2.IRO.mp, Counter.c} ∧
              inv §IRO.mp{1} §RFList.m{2} ∧ §SORO.Bounder.bounder{2} ≤ §Counter.c{2} + 1)
            swap
            -- EC: - by conseq(:_==> ={y, x1, glob OSimulator, Log.m}); 1: smt(); sim=> />.
            · equiv_conseq (: _ ==> ={y, x1, Simulator.m, Simulator.mi, Simulator.paths,
                Gconcl_list.BIRO2.IRO.mp, Log.m})
              · ec_close
              sim
            -- EC: inline{1} 1; auto.
            --     by call(eq_IRO_RFWhile); auto=> /> &1 &2 + <- /> <- /#.
            stmt_inline{1} 0; stmt_wp
            equiv_call eq_IRO_RFWhile; ec_auto; ec_close
          -- EC: + by conseq (: ={y, glob OSimulator}); [|sim]=> /> &1 &2 <- /> <- /#.
          · equiv_conseq (: _ ==> ={y, Simulator.m, Simulator.mi, Simulator.paths,
              Gconcl_list.BIRO2.IRO.mp})
            · ec_close
            sim; ec_close
        · ec_auto; ec_close
      · ec_auto; ec_close
    · ec_auto
  -- EC: + by proc; inline*; sp; if; auto; sp; if; auto=> />; smt().
  · simp only [ODPRIMITIVE_fi_mk]
    equiv_proc; stmt_inline*; stmt_sp
    stmt_if
    · ec_close
    · stmt_sp; stmt_if
      · ec_close
      · ec_auto; ec_close
      · ec_auto; ec_close
    · ec_auto
  -- EC: proc.
  --     inline{1} 1; inline{2} 1; sp; if; auto=> /=.
  · equiv_proc
    stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
    stmt_if
    · ec_close
    -- EC: inline{1} 1; inline{2} 1; sp.
    --     rcondt{1} 1; 1: auto.
    · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
      stmt_rcondt{1} 1
      · hoare_auto
      -- EC: inline{1} 1; auto.
      stmt_inline{1} 0; stmt_wp
      -- EC: rcondf{2} 4; 1: auto.
      --     + inline*; auto; sp; if; auto; sp; if; auto=> />; conseq(:_==> true); 1: smt().
      --       by while(true); auto.
      --     (the call does not write what the condition reads: the framed `hoare_call`)
      stmt_rcondf{2} 4
      · intro σ₁
        stmt_wp; hoare_call (: True ==> True) / Log.m; ec_auto
      -- EC: inline{2} 1; sp.
      --     rcondt{2} 1; 1: by auto; smt(divz_ge0 gt0_r size_ge0).
      stmt_inline{2} 0; stmt_sp
      stmt_rcondt{2} 1
      · intro σ₁
        hoare_auto; ec_progress
        exact lt_of_le_of_lt ‹bounder ≤ _› (lt_of_lt_of_le
          (GaudisCrypt.SHA3.SHA3OSecurity.lt_increase_counter _ _ _) ‹_ ≤ SHA3Indiff.limit›)
      -- EC: auto; call eq_IRO_RFWhile; auto=> />.
      --     move=> /> &l &r H0 H1 H2 H3 H5 H6 result_L mp_L m_R H7 H8 H9 H10 H11; split;
      --       2: smt(divz_ge0 gt0_r size_ge0).
      --     rewrite cats0 take_oversize 1:/# take_oversize 1:spec_dout //=.
      --     have h:=spec2_dout result_L H7.
      --     have-> := some_oget _ h.
      --     by rewrite /= eq_sym -to_listK.
      --     (the first port's `to_list_oget_of_list`, `lt_increase_counter`)
      stmt_wp
      equiv_call eq_IRO_RFWhile
      ec_auto; ec_progress
      · have hk : to_list (oget (of_list r₁)) = r₁ :=
          GaudisCrypt.SHA3.SHA3OSecurity.to_list_oget_of_list _ ‹size r₁ = size_out›
        rw [hk, ‹xk₂.2 = size_out›, ‹xk₁.2 = size_out›, List.append_nil]
        rfl
      · have h1 := GaudisCrypt.SHA3.SHA3OSecurity.lt_increase_counter (Counter.c.get g₁)
          xk₁.1 xk₁.2
        have h2 := ‹bounder₂ ≤ Counter.c.get g₁›
        rw [‹SORO.Bounder.bounder.get g₂ = bounder₂ + 1›]
        omega
    · ec_auto
  -- EC: + by inline*; auto; smt(mem_empty).
  --     (GAP 4: `glob A` past the initializations' writes; `inv` of the empty maps)
  ec_auto; ec_progress
  · have h := congrArg (FVP.fvP A).touched_getter.get ‹Simulator.m.set _ _ = _›
    simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at h
    exact h
  all_goals first
    | (have hd := ‹(IRO.mp.get globals₁).dom (l, i)›
       rw [‹IRO.mp.get globals₁ = FMap.empty›] at hd
       exact absurd hd (FMap.mem_empty _))
    | (have hd := ‹(RFList.m.get globals₂).dom l›
       rw [‹RFList.m.get globals₂ = FMap.empty›] at hd
       exact absurd hd (FMap.mem_empty _))

set_option maxHeartbeats 40000000 in
-- one declaration: the adversary's three oracles
/-- EC's `local lemma rw_ideal &m`. -/
theorem rw_ideal (m : VariableAssignment) :
    Pr[ OIndif(FSome(IRO.asF), OSimulator(FSome(IRO.asF)),
        ODRestr(Dist_of_P1Adv(A))).main () @ &m : §res ] ≤
    Pr[ SORO.Preimage(SORO_P1(A), SORO.RF(SORO.RO)).main () @ &m : §res ] := by
  -- EC: rewrite (StdOrder.RealOrder.ler_trans _ _ _ (rw_ideal_2 &m)).
  refine (rw_ideal_2 A m).trans ?_
  -- EC: byequiv(: ={glob A} ==> _) => //=; proc; inline*; sp; wp.
  byequiv
  case hE => exact fun _ _ _ _ h => h
  equiv_proc
  -- EC: swap{2} 2; sp; swap{2}[1..2] 6; sp.
  --     swap{1} 2; sp; swap{1}[1..2] 6; sp.
  --     (EC's `inline*` leaves the last query for after the adversary's call)
  stmt_swap 1
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_sp
  stmt_swap{1} [1..2] 6; stmt_swap{2} [1..2] 6; stmt_sp
  -- EC: seq 2 2 : (Log.m{1} = empty /\ … /\ ={glob A, h, hash}); 1: auto=> />.
  --     seq 1 1 : (={glob A, glob SHA3Indiff.Simulator, glob SORO.Bounder, glob Counter,
  --       glob Log, mi, h, hash} /\ RFList.m{1} = SORO.RO.RO.m{2}).
  --     (EC's first `seq` is the initializations, which `sp` has taken; the sampling of `hash`
  --     and `h <- hash` are the first two of the three statements)
  equiv_seq 3 3 : (={glob A, Simulator.m, Simulator.mi, Simulator.paths,
    Gconcl_list.BIRO2.IRO.mp, SORO.Bounder.bounder, Counter.c, Log.m, mi, h, hash} ∧
    §RFList.m{1} = §SORO.RO.m{2})
  swap
  -- EC: sp; if; 1, 3: auto; sp; wp 1 2.
  · stmt_inline*; stmt_sp
    stmt_if
    · ec_close
    · stmt_sp; stmt_wp
      -- EC: if{1}.
      --     + wp=> />.
      --       rnd (fun x => oget (of_list x)) to_list; auto=> />.
      --       move=> &l c Hc Hnin; split. … (the bijection's three conditions)
      --     (`rnd f g` is `equiv_rnd f`: it asks that `f` push `dlist dbool size_out` to `dout`,
      --     the first port's `dlist_dout`, EC's `dout_equal_dlist` and `to_listK`)
      stmt_if{1}
      · stmt_wp
        equiv_rnd (fun l => oget (of_list l))
        ec_auto; ec_progress
        · exact GaudisCrypt.SHA3.SHA3OSecurity.Preimage.dlist_dout
        · exact congrArg (fun o => some (oget o)) ‹_ = some hash₂›
      -- EC: by auto=> />; smt(dout_ll).
      · ec_auto; ec_progress
        · exact (is_lossless_iff_expected _).mp GaudisCrypt.SHA3.SHA3OSecurity.Params.dout_ll
        · rw [‹RO_m₂.get x1₂ = some hash₂›]; rfl
    · ec_auto
  -- EC: + call(: ={glob SHA3Indiff.Simulator, glob SORO.Bounder, glob Counter, glob Log} /\
  --       RFList.m{1} = SORO.RO.RO.m{2}); auto.
  equiv_call (_ : ={Simulator.m, Simulator.mi, Simulator.paths, Gconcl_list.BIRO2.IRO.mp,
    SORO.Bounder.bounder, Counter.c, Log.m} ∧ §RFList.m{1} = §SORO.RO.m{2})
  -- EC: - proc; sp; if; 1, 3: auto; sp.
  --       inline *; sp; sim.
  · equiv_proc; stmt_sp
    stmt_if
    · ec_close
    · stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp; stmt_wp
      -- EC: if; 1: auto; sim.
      stmt_if
      · ec_close
      · stmt_wp
        -- EC: if; 1: auto; sim.
        stmt_if
        · ec_close
        · sim 4 4
          -- EC: sp; if; [2,3:sim]; [1,3:by auto=> /> &1 &2 <- /> <- />].
          stmt_sp
          stmt_if
          · ec_close
          -- EC: sp; if; 1: auto; sim; -1: smt().
          --     (EC's `sim` over what follows the bounder's conditional — the loop on `Log.m` —
          --     with `RFList.m{1} = RO.m{2}` kept: `seq` at the conditional, `conseq` to the
          --     equalities, `sim`)
          · stmt_wp
            stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
            stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
            equiv_seq 1 1 : (={y, x0, x1, k0, suffix, Simulator.m, Simulator.mi, Simulator.paths,
              Gconcl_list.BIRO2.IRO.mp, SORO.Bounder.bounder, Counter.c, Log.m} ∧
              §RFList.m{1} = §SORO.RO.m{2})
            swap
            · equiv_conseq (: _ ==> ={o0, x0, Simulator.m, Simulator.mi, Simulator.paths,
                Gconcl_list.BIRO2.IRO.mp, Log.m})
              · ec_close
              sim
            stmt_if
            · ec_close
            -- EC: sp; if{1}.
            --     * rcondt{2} 2.
            --       + by auto=> /> + + <- /> <- />.
            --       auto.
            --       rnd (fun l => oget (of_list l)) to_list; auto=> />. …
            --     (EC's `rcondt{2} 2` is the `wp` through the right's conditional, as in the
            --     lemma's last step: its side goal would need the chain of `sp`'s tuple
            --     equations by hand)
            · stmt_inline{1} 0; stmt_inline{2} 0; stmt_inline{2} 0; stmt_sp
              stmt_if{1}
              · stmt_wp
                equiv_rnd (fun l => oget (of_list l))
                ec_auto; ec_progress
                · exact GaudisCrypt.SHA3.SHA3OSecurity.Preimage.dlist_dout
                · rw [FMap.get_set_sameE]; rfl
              -- EC: by auto=> /> + + + <- /> <-; smt(dout_ll).
              · ec_auto; ec_progress
                · exact (is_lossless_iff_expected _).mp
                    GaudisCrypt.SHA3.SHA3OSecurity.Params.dout_ll
                · obtain ⟨v, hv⟩ :=
                    Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp ‹RO_m₂.dom _›)
                  rw [hv]; rfl
            · ec_auto; ec_close
          · sim; ec_close
        · ec_auto
      · ec_auto
    · ec_auto
  -- EC: - by proc; inline*; sp; if; auto; sp; if; auto.
  · equiv_proc; stmt_inline*; stmt_sp
    stmt_if
    · ec_close
    · stmt_sp; stmt_if
      · ec_close
      · ec_auto
      · ec_auto
    · ec_auto
  -- EC: - proc; inline*; sp; if; auto; sp; if; auto; sp; sim.
  --       if{1}.
  --       * rcondt{2} 2; auto.
  --         rnd (fun l => oget (of_list l)) to_list; auto=> />. …
  --     (as in the first oracle)
  · equiv_proc; stmt_inline*; stmt_sp
    stmt_if
    · ec_close
    · stmt_sp
      equiv_seq 1 1 : (={y0, x1, k0, suffix, l, k, Simulator.m, Simulator.mi, Simulator.paths,
        Gconcl_list.BIRO2.IRO.mp, SORO.Bounder.bounder, Counter.c, Log.m} ∧
        §RFList.m{1} = §SORO.RO.m{2})
      swap
      · equiv_conseq (: _ ==> ={r, Counter.c, Log.m})
        · ec_close
        sim
      stmt_if
      · ec_close
      · stmt_sp; stmt_if{1}
        · stmt_wp
          equiv_rnd (fun l => oget (of_list l))
          ec_auto; ec_progress
          · exact GaudisCrypt.SHA3.SHA3OSecurity.Preimage.dlist_dout
          · rw [‹xk₂.1 = xk₁.1›, FMap.get_set_sameE]; rfl
        · ec_auto; ec_progress
          · exact (is_lossless_iff_expected _).mp GaudisCrypt.SHA3.SHA3OSecurity.Params.dout_ll
          · have hd := ‹RO_m₂.dom xk₂.1›
            rw [‹xk₂.1 = xk₁.1›] at hd ⊢
            obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd)
            rw [hv]; rfl
      · ec_auto
    · ec_auto
  -- EC: by auto=> />; smt(dout_ll).
  --     (GAP 4: `glob A` past the initializations' writes)
  ec_auto; ec_progress
  have h := congrArg (FVP.fvP A).touched_getter.get ‹SORO.Bounder.bounder.set _ _ = _›
  simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at h
  exact h

/-- EC's `local lemma leq_ideal &m`. -/
theorem leq_ideal (m : VariableAssignment) :
    Pr[ OIndif(FSome(IRO.asF), OSimulator(FSome(IRO.asF)),
        ODRestr(Dist_of_P1Adv(A))).main () @ &m : §res ] ≤
      ((sigma + 1 : ℤ) : ℝ) / (2 : ℝ) ^ size_out := by
  -- EC: rewrite (StdOrder.RealOrder.ler_trans _ _ _ (rw_ideal &m)).
  refine (rw_ideal A m).trans ?_
  -- EC: rewrite (StdOrder.RealOrder.ler_trans _ _ _
  --       (RO_is_preimage_resistant (SORO_P1(A)) &m)).
  --     (EC checks `SORO_P1(A)` against the restriction of `RO_is_preimage_resistant`)
  have hP : Module.Declared (SORO_P1 A) (SORO.RO.m.footprint ⊔ SORO.Bounder.bounder.footprint ⊔
      SORO.Preimage.Preimage2.hash.footprint) := ⟨by fp_finite, by fp_disjoint⟩
  refine (SORO.RO_is_preimage_resistant (SORO_P1 A) m).trans ?_
  -- EC: by rewrite doutE1.
  rw [div_eq_mul_inv, ← doutE1 default]
  exact le_rfl


set_option maxHeartbeats 40000000 in
-- one declaration: the adversary's three oracles
/-- EC's `local lemma rw_real &m`. -/
theorem rw_real (m : VariableAssignment) :
    Pr[ SH.Preimage(A, OSponge, PSome(Perm)).main () @ &m : §res ] =
    Pr[ OIndif(FSome(Sponge(Poget(PSome(Perm)))), PSome(Perm),
        ODRestr(Dist_of_P1Adv(A))).main () @ &m : §res ] := by
  -- EC: byequiv=>//=; proc; inline*; sp; wp=> />.
  --     swap{1} 4; sp.
  --     seq 2 2 : (={glob A, glob Perm, hash, m} /\ Bounder.bounder{1} = Counter.c{2}).
  --     (GAP 6: `OSponge` and its primitive at the sponge's module types first.  EC's `inline*`
  --     would also open the sponge's calls of the permutation in the last query, whose locals
  --     the two sides then name at two spellings of the state type; so `seq` first, on the games
  --     with the right one opened down to the adversary's call, and the initializations after)
  byequiv; equiv_proc
  simp only [OPRIMITIVE_coe_eq]
  erw [OSponge_app]
  stmt_inline{2} 2; stmt_inline{2} 2; stmt_inline{2} 2
  stmt_wp
  equiv_seq 4 6 : (={glob A, Perm.m, Perm.mi, m} ∧ §hash{1} = §hash0{2} ∧
    §SH.Bounder.bounder{1} = §Counter.c{2})
  swap
  -- EC: by sp; if; auto=>/=; sim; auto.
  --     (the last query opened down to the sponge's loops; `sim` after `conseq` to the
  --     equalities the event reads)
  · stmt_inline{1} 0; stmt_inline{2} 0; stmt_inline{2} 0; stmt_sp
    stmt_if
    · ec_close
    · stmt_inline{1} 0; stmt_inline{1} 0; stmt_inline{1} 0
      stmt_inline{2} 0; stmt_inline{2} 0
      stmt_sp; stmt_wp
      equiv_conseq (: _ ==> ={z0, n})
      · ec_close
      sim
    · ec_auto
  --     (the initializations: `PSome(Perm).init` behind the clone's projection, GAP 6)
  stmt_inline{1} 0
  rw [PSome_Perm_init _ rfl]
  simp only [PSome, GaudisCrypt.SHA3.OptionIndifferentiability.OPRIMITIVE.init.mk_simp]
  stmt_inline*
  stmt_swap{1} 4; stmt_sp
  -- EC: + call(: ={glob Perm} /\ Bounder.bounder{1} = Counter.c{2})=> //=.
  equiv_call (_ : ={Perm.m, Perm.mi} ∧ §SH.Bounder.bounder{1} = §Counter.c{2})
  -- EC: - by proc; inline*; sp; if; auto; 2:sim=> />; 1: smt().
  · simp only [ODPRIMITIVE_f_mk]
    equiv_proc; stmt_inline*; stmt_sp
    stmt_if
    · ec_close
    · stmt_sp; stmt_if
      · ec_close
      · ec_auto
      · ec_auto
    · ec_auto
  -- EC: - by proc; inline*; sp; if; auto; 2:sim=> />; 1: smt().
  · simp only [ODPRIMITIVE_fi_mk]
    equiv_proc; stmt_inline*; stmt_sp
    stmt_if
    · ec_close
    · stmt_sp; stmt_if
      · ec_close
      · ec_auto
      · ec_auto
    · ec_auto
  -- EC: - proc; inline*; sp; if; auto; sp=> />.
  --       by conseq(:_==> ={z0, glob Perm})=> />; sim.
  --     (GAP 7: `sim` does not end on the two loops here; the `while` rule, the permutation's
  --     calls by `call (_ : ={glob Perm})`)
  · equiv_proc
    stmt_inline{1} 0; stmt_inline{2} 0; stmt_inline{2} 0; stmt_sp
    stmt_if
    · ec_close
    · stmt_inline{1} 0; stmt_inline{1} 0; stmt_inline{1} 0
      stmt_inline{2} 0; stmt_inline{2} 0
      stmt_sp; stmt_wp
      equiv_conseq (: _ ==> ={z0, n, Perm.m, Perm.mi})
      · ec_close
      equiv_while (={i, n, z0, sa, sc, Perm.m, Perm.mi})
      · stmt_sp; stmt_if
        · ec_close
        · equiv_call (_ : ={Perm.m, Perm.mi}); ec_auto; ec_close
        · ec_auto; ec_close
      equiv_while (={xs, i, n, z0, sa, sc, Perm.m, Perm.mi})
      · stmt_wp; equiv_call (_ : ={Perm.m, Perm.mi}); ec_auto
      ec_auto
    · ec_auto
  -- EC: by auto.
  --     (GAP 4: `glob A` past the initializations' writes)
  ec_auto; ec_progress
  have h := congrArg (FVP.fvP A).touched_getter.get ‹Perm.m.set _ _ = _›
  simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl] at h
  exact h

set_option maxHeartbeats 40000000 in
-- one declaration: EC's restriction checks and the losslessness of `Dist_of_P1Adv(A)`
set_option synthInstance.maxHeartbeats 400000 in
-- EC's restriction checks by instance search (`A` against the modules of `SHA3OIndiff`)
set_option synthInstance.maxSize 1024 in
/-- EC's `lemma Sponge_preimage_resistant &m:
(forall (F <: OIndif.ODFUNCTIONALITY) (P <: OIndif.ODPRIMITIVE),
islossless F.f => islossless P.f => islossless P.fi => islossless A(F,P).guess) =>
Pr[Preimage(A, OSponge, PSome(Perm)).main() @ &m : res] <=
(limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r +
(sigma + 1)%r / (2%r ^ size_out)`. -/
theorem Sponge_preimage_resistant (m : VariableAssignment) :
    (∀ (F <: SH.OIndif.ODFUNCTIONALITY), ∀ (P <: SH.OIndif.ODPRIMITIVE),
      islossless F.f → islossless P.f → islossless P.fi → islossless A(F, P).guess) →
    Pr[ SH.Preimage(A, OSponge, PSome(Perm)).main () @ &m : §res ] ≤
      ((SHA3Indiff.limit ^ 2 - SHA3Indiff.limit : ℤ) : ℝ) / ((2 ^ (r + c + 1).toNat : ℤ) : ℝ) +
        ((4 * SHA3Indiff.limit ^ 2 : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ) +
      ((sigma + 1 : ℤ) : ℝ) / (2 : ℝ) ^ size_out := by
  -- EC: move=> A_ll.
  intro A_ll
  -- EC: rewrite (rw_real &m).
  rw [rw_real A m]
  -- EC: have := SHA3OIndiff (Dist_of_P1Adv(A)) &m _.
  have h := @Pilot.SHA3_OIndiff.SHA3OIndiff _ _ _ (Dist_of_P1Adv A)
    ⟨by fp_finite, by fp_disjoint⟩ (R ⊔ Log.m.footprint) inferInstance
    ⟨‹Footprint.Restricted R _›.finite.sup (by fp_finite), by fp_disjoint⟩ m ?_
  · -- EC: by have/#:=leq_ideal &m.
    --     (EC's `OGReal`, `OGIdeal` are module aliases, which `/#` sees through: the first
    --     port's `OGReal_eq`, and `OGIdeal` by definition)
    have h2 := leq_ideal A m
    rw [GaudisCrypt.SHA3.SHA3OSecurity.OGReal_eq] at h
    refine le_trans (sub_le_iff_le_add.mp (abs_le.mp h).2) ?_
    exact (add_le_add_iff_left _).mpr h2
  -- EC: + move=> F P Hp Hpi Hf; proc; inline*; sp; auto; call Hf; auto.
  · intro F P Hp Hpi Hf
    phoare_proc; phoare_inline*; stmt_sp; stmt_wp
    --     (the adversary's call in the middle: pHL `seq`, as in `Pilot/SHA3Security.lean`)
    phoare_seq_lossless 2 : (True)
    -- EC: call(A_ll (DFSetSize(F)) P _ Hp Hpi); auto.
    · phoare_call (A_ll _ _ ?_ Hp Hpi)
      -- EC: smt(dout_ll).
      · phoare_auto
        intros
        exact (is_lossless_iff_expected _).mp GaudisCrypt.SHA3.SHA3OSecurity.Params.dout_ll
      -- EC: - proc; inline*; auto; call Hf; auto.
      · simp only [SH.OIndif.ODFUNCTIONALITY.f.mk_simp]
        phoare_proc; phoare_auto; phoare_call Hf; phoare_auto
    · stmt_sp; phoare_call Hf; phoare_auto

end

end Preimage

end GaudisCrypt.SHA3.Pilot.SHA3OSecurity
