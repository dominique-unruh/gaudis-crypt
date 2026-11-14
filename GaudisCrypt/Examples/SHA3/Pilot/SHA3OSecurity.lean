import GaudisCrypt.Examples.SHA3.Pilot.SecureORO
import GaudisCrypt.Examples.SHA3.Pilot.SecureHash
import GaudisCrypt.Examples.SHA3.Pilot.SHA3_OIndiff
import GaudisCrypt.Examples.SHA3.SHA3OSecurity

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

/-!
# Top-level proof of SHA-3 security, with failing oracles (EasyCrypt `proof/SHA3OSecurity.ec`) —
EC-fidelity port, in progress

Ported so far: the clones `SORO`, `SH` and the file's modules (EC l. 1–175).

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

end GaudisCrypt.SHA3.Pilot.SHA3OSecurity
