import GaudisCrypt.Examples.SHA3.SmartCounter.SLCommonCore
import GaudisCrypt.Examples.SHA3.Indifferentiability
import GaudisCrypt.Lib.EC.FSet
import GaudisCrypt.Lib.EC.PROM
import GaudisCrypt.Lib.EC.DProd
import GaudisCrypt.Lib.EC.Tuple
import GaudisCrypt.Logic.PHoare
import GaudisCrypt.Logic.AbstractCallUpto
import GaudisCrypt.Logic.HoareFrame

/-!
# The squeezeless sponge: common definitions (EasyCrypt `proof/smart_counter/SLCommon.ec`)

The squeezeless sponge, whose ideal functionality is a fixed-output-length random oracle whose
output length is the input block size; its security holds even when the padding is not
prefix-free.  This file has the construction, the counting and restricting wrappers, the prefix
operators and the handle operators used by the whole `smart_counter` proof.

Translation notes (see `notes/SHA3/README.md`):
* `op max_size : { int | 0 <= max_size } as max_ge0` extends the parameter class: `Params`.
* `prefix` is a Lean keyword, hence `«prefix»`.
* `clone include Indifferentiability with type p <- state …` is the abbreviations below
  (`PRIMITIVE` …, `Indif`, `RealIndif`, `IdealIndif`); `clone import FullRO as F …` is the
  namespace `F`.
* Modules whose procedures alias another module's (`PRestr`, `FRestr`: `proc f = DPRestr(P).f`)
  are Lean functions assembling the procedures with `T.mk`.
* `DRestr(D : DISTINGUISHER, F, P)` takes `D` as a Lean parameter, so that `DRestr D` is a
  `DISTINGUISHER` (EasyCrypt uses it partially applied, `DRestr(D)`).
* A memory restriction `{-C}` is a footprint hypothesis against `C.footprint`.
-/

namespace GaudisCrypt.SHA3.SLCommon

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common

variable [Params]

/-! ## `clone include Indifferentiability with type p <- state, type f_in <- block list,
type f_out <- block rename [module] "GReal" as "RealIndif" [module] "GIdeal" as "IdealIndif"` -/

abbrev PRIMITIVE := Indifferentiability.PRIMITIVE state (List block) block
abbrev DPRIMITIVE := Indifferentiability.DPRIMITIVE state (List block) block
abbrev FUNCTIONALITY := Indifferentiability.FUNCTIONALITY state (List block) block
abbrev DFUNCTIONALITY := Indifferentiability.DFUNCTIONALITY state (List block) block
abbrev CONSTRUCTION := Indifferentiability.CONSTRUCTION state (List block) block
abbrev SIMULATOR := Indifferentiability.SIMULATOR state (List block) block
abbrev DISTINGUISHER := Indifferentiability.DISTINGUISHER state (List block) block
noncomputable abbrev Indif := Indifferentiability.Indif state (List block) block
noncomputable abbrev RealIndif := Indifferentiability.GReal state (List block) block
noncomputable abbrev IdealIndif := Indifferentiability.GIdeal state (List block) block
abbrev distHoles := Indifferentiability.distHoles state (List block) block
noncomputable abbrev distExt := Indifferentiability.distExt state (List block) block

/-! ## The ideal functionality -/


-- `clone import FullRO as F with type in_t <- block list, type out_t <- block,
-- op dout _ <- bdistr, type d_in_t <- unit, type d_out_t <- bool`
namespace F
noncomputable abbrev dout : List block → SubProbability block := fun _ => bdistr
/-- The clone's module variable `F.RO.m`. -/
global_var RO.m : FMap (List block) block
/-- The clone's module variable `F.FRO.m`. -/
global_var FRO.m : FMap (List block) (block × flag)
noncomputable abbrev RO := PROM.FullRO.RO (List block) block dout RO.m
/-- `F.RO` as its type `RO` (`PROM.FullRO.RO.asRO`). -/
noncomputable abbrev RO.asRO := PROM.FullRO.RO.asRO (List block) block dout RO.m
/-- The module type `F.RO` (exception E3). -/
abbrev RO_T := PROM.FullRO.RO_T (List block) block
noncomputable abbrev LRO := PROM.FullRO.LRO (List block) block dout RO.m
noncomputable abbrev FRO := PROM.FullRO.FRO (List block) block dout FRO.m
abbrev RO_Distinguisher := PROM.FullRO.RO_Distinguisher (List block) block Unit Bool
namespace FullEager
noncomputable abbrev RRO := PROM.FullRO.FullEager.RRO (List block) block dout FRO.m
end FullEager
end F

/-! ## The squeezeless sponge -/

/-- EC's `Redo.prefixes`. -/
global_var Redo.prefixes : FMap (List block) state

module Redo {
  proc init () : Unit {
    Redo.prefixes <- FMap.set (FMap.empty : FMap (List block) state) [] (b0, c0);
    return ()
  };
}

-- The squeezeless sponge construction
module SqueezelessSponge using (P : DPRIMITIVE) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call Redo.init ();
    return ()
  };
  proc f (p : List block) : block {
    var sa : block, sc : capacity, i : ℤ;
    sa, sc <- (b0, c0);
    i <- 0;
    while ($i < size $p) {
      if (decide (FMap.dom ($Redo.prefixes : FMap (List block) state) (take ($i + 1) $p))) {
        sa, sc <- oget (FMap.get ($Redo.prefixes : FMap (List block) state) (take ($i + 1) $p));
      } else {
        sa, sc <- ($sa +^ nth default $p $i, $sc);
        sa, sc <- call P.f (($sa, $sc));
        Redo.prefixes <- FMap.set $Redo.prefixes (take ($i + 1) $p) ($sa, $sc);
      }
      i <- $i + 1;
    }
    return $sa
  };
}


open Prefix

/-! ## Counting and restricting -/

/-- EC's `C.c`. -/
global_var C.c : ℤ
/-- EC's `C.queries`. -/
global_var C.queries : FMap (List block) block

module C {
  proc init () : Unit {
    C.c <- 0;
    C.queries <- FMap.set (FMap.empty : FMap (List block) block) [] b0;
    return ()
  };
}

/-- What `C` touches: the restriction `{-C}`. -/
noncomputable def C.footprint : Footprint VariableAssignment :=
  C.c.footprint ⊔ (C.queries).footprint

module PC using (P : PRIMITIVE) : PRIMITIVE {
  proc init () : Unit {
    _ <- call C.init ();
    _ <- call P.init ();
    return ()
  };
  proc f (x : state) : state {
    var y : state;
    y <- (b0, c0);
    y <- call P.f ($x);
    C.c <- $C.c + 1;
    return $y
  };
  proc fi (x : state) : state {
    var y : state;
    y <- (b0, c0);
    y <- call P.fi ($x);
    C.c <- $C.c + 1;
    return $y
  };
}

module DPRestr using (P : DPRIMITIVE) : DPRIMITIVE {
  proc f (x : state) : state {
    var y : state;
    y <- (b0, c0);
    if (decide ($C.c + 1 ≤ max_size)) {
      y <- call P.f ($x);
      C.c <- $C.c + 1;
    }
    return $y
  };
  proc fi (x : state) : state {
    var y : state;
    y <- (b0, c0);
    if (decide ($C.c + 1 ≤ max_size)) {
      y <- call P.fi ($x);
      C.c <- $C.c + 1;
    }
    return $y
  };
}

-- `PRestr.init`, the procedure of `PRestr` that is not `DPRestr`'s
module PRestr.init_ using (P : PRIMITIVE) {
  proc init () : Unit {
    _ <- call C.init ();
    _ <- call P.init ();
    return ()
  };
}

/-- EC's `PRestr(P)`: `proc init`, and `proc f = DPRestr(P).f`, `proc fi = DPRestr(P).fi`. -/
noncomputable def PRestr (P : PRIMITIVE) : PRIMITIVE :=
  Indifferentiability.PRIMITIVE.mk state (List block) block
    { init := Module.app PRestr.init_ P
      f := Indifferentiability.DPRIMITIVE.f state (List block) block
        (Module.app DPRestr (Indifferentiability.PRIMITIVE.view state (List block) block P))
      fi := Indifferentiability.DPRIMITIVE.fi state (List block) block
        (Module.app DPRestr (Indifferentiability.PRIMITIVE.view state (List block) block P)) }

module FC using (F : FUNCTIONALITY) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (bs : List block) : block {
    var b : block;
    b <- b0;
    if (!(decide (FMap.dom ($C.queries : FMap (List block) block) $bs))) {
      C.c <- $C.c + size $bs - «prefix» $bs (get_max_prefix $bs (elems (FMap.fdom
        ($C.queries : FMap (List block) block))));
      b <- call F.f ($bs);
      C.queries <- FMap.set $C.queries $bs $b;
    } else {
      b <- oget (FMap.get $C.queries $bs);
    }
    return $b
  };
}

module DFRestr using (F : DFUNCTIONALITY) : DFUNCTIONALITY {
  proc f (bs : List block) : block {
    var b : block;
    b <- b0;
    if (!(decide (FMap.dom ($C.queries : FMap (List block) block) $bs))) {
      if (decide ($C.c + size $bs - «prefix» $bs (get_max_prefix $bs (elems (FMap.fdom
          ($C.queries : FMap (List block) block)))) ≤ max_size)) {
        C.c <- $C.c + size $bs - «prefix» $bs (get_max_prefix $bs (elems (FMap.fdom
          ($C.queries : FMap (List block) block))));
        b <- call F.f ($bs);
        C.queries <- FMap.set $C.queries $bs $b;
      }
    } else {
      b <- oget (FMap.get $C.queries $bs);
    }
    return $b
  };
}

-- `FRestr.init`, the procedure of `FRestr` that is not `DFRestr`'s
module FRestr.init_ using (F : FUNCTIONALITY) {
  proc init () : Unit {
    _ <- call Redo.init ();
    _ <- call F.init ();
    return ()
  };
}

/-- EC's `FRestr(F)`: `proc init`, and `proc f = DFRestr(F).f`. -/
noncomputable def FRestr (F : FUNCTIONALITY) : FUNCTIONALITY :=
  Indifferentiability.FUNCTIONALITY.mk state (List block) block
    { init := Module.app FRestr.init_ F
      f := Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app DFRestr (Indifferentiability.FUNCTIONALITY.view state (List block) block F)) }

-- EC's `DRestr(D : DISTINGUISHER, F : DFUNCTIONALITY, P : DPRIMITIVE)`, with `D` a Lean parameter
-- so that `DRestr D` is a `DISTINGUISHER`
set_option linter.gaudisCrypt.using false in
module DRestr (D : DISTINGUISHER) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call C.init ();
    b <- call (Module.app D (Module.pair (Module.app DFRestr F) (Module.app DPRestr P))) ();
    return $b
  };
}

/-- `lemma rp_ll (P<:DPRIMITIVE{-C}): islossless P.f => islossless DPRestr(P).f`.
EC: `proc;sp;if;auto;call Hll;auto`. -/
theorem rp_ll (P : DPRIMITIVE) (_hP : FVP.fvP P ≤ C.footprintᶜ) :
    (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
    (Indifferentiability.DPRIMITIVE.f state (List block) block
      (Module.app DPRestr P)).procedure.IsLossless := by
  intro hll
  rw [Procedure.isLossless_iff_phoareProc] at hll ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 5
  phoare_simp [hll]
  phoare_skip
  simp

/-- `lemma rpi_ll (P<:DPRIMITIVE{-C}): islossless P.fi => islossless DPRestr(P).fi`.
EC: `proc;sp;if;auto;call Hll;auto`. -/
theorem rpi_ll (P : DPRIMITIVE) (_hP : FVP.fvP P ≤ C.footprintᶜ) :
    (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
    (Indifferentiability.DPRIMITIVE.fi state (List block) block
      (Module.app DPRestr P)).procedure.IsLossless := by
  intro hll
  rw [Procedure.isLossless_iff_phoareProc] at hll ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 5
  phoare_simp [hll]
  phoare_skip
  simp

/-- `lemma rf_ll (F<:DFUNCTIONALITY{-C}): islossless F.f => islossless DFRestr(F).f`.
EC: `proc;sp;if;auto;if=>//;auto;call Hll;auto`. -/
theorem rf_ll (F : DFUNCTIONALITY) (_hF : FVP.fvP F ≤ C.footprintᶜ) :
    (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
    (Indifferentiability.DFUNCTIONALITY.f state (List block) block
      (Module.app DFRestr F)).procedure.IsLossless := by
  intro hll
  rw [Procedure.isLossless_iff_phoareProc] at hll ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 5
  phoare_simp [hll]
  phoare_skip
  simp

/-- `DFRestr` touches `C`'s variables only.  Not an EC lemma: EasyCrypt reads a concrete
module's globals off its code (for `fp_disjoint`, as `glob DRestr(D)`'s side conditions). -/
@[fp_bound] theorem fvP_DFRestr : FVP.fvP DFRestr ≤ C.footprint := by
  fp_module (Lens.pair C.c C.queries)

/-- `DPRestr` touches `C`'s variables only.  Not an EC lemma (as `fvP_DFRestr`). -/
@[fp_bound] theorem fvP_DPRestr : FVP.fvP DPRestr ≤ C.footprint := by
  fp_module (Lens.pair C.c C.queries)

/-- `FC` touches `C`'s variables only.  Not an EC lemma (as `fvP_DFRestr`). -/
@[fp_bound] theorem fvP_FC : FVP.fvP FC ≤ C.footprint := by
  fp_module (Lens.pair C.c C.queries)

/-- `PC` touches `C`'s variables only.  Not an EC lemma (as `fvP_DFRestr`). -/
@[fp_bound] theorem fvP_PC : FVP.fvP PC ≤ C.footprint := by
  fp_module (Lens.pair C.c C.queries)

/-- `PC(P).f` is lossless when `P.f` is.  Not an EC lemma: EC proves it inline in `Pr_restr`'s
`apply D_ll` (`islossless` of the counting oracles). -/
theorem pc_f_ll (P : PRIMITIVE) :
    (Indifferentiability.PRIMITIVE.f state (List block) block P).procedure.IsLossless →
    (Indifferentiability.PRIMITIVE.f state (List block) block
      (Module.app PC P)).procedure.IsLossless := by
  intro hll
  rw [Procedure.isLossless_iff_phoareProc] at hll ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 6
  phoare_simp [hll]
  phoare_skip
  simp

/-- `PC(P).fi` is lossless when `P.fi` is.  Not an EC lemma (as `pc_f_ll`). -/
theorem pc_fi_ll (P : PRIMITIVE) :
    (Indifferentiability.PRIMITIVE.fi state (List block) block P).procedure.IsLossless →
    (Indifferentiability.PRIMITIVE.fi state (List block) block
      (Module.app PC P)).procedure.IsLossless := by
  intro hll
  rw [Procedure.isLossless_iff_phoareProc] at hll ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 6
  phoare_simp [hll]
  phoare_skip
  simp

/-- `FC(F).f` is lossless when `F.f` is.  Not an EC lemma (as `pc_f_ll`). -/
theorem fc_ll (F : FUNCTIONALITY) :
    (Indifferentiability.FUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
    (Indifferentiability.FUNCTIONALITY.f state (List block) block
      (Module.app FC F)).procedure.IsLossless := by
  intro hll
  rw [Procedure.isLossless_iff_phoareProc] at hll ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 5
  phoare_simp [hll]
  phoare_skip
  simp

/-- `lemma DRestr_ll (D<:DISTINGUISHER{-C}): (forall (F<:DFUNCTIONALITY{-D})(P<:DPRIMITIVE{-D}),
islossless P.f => islossless P.fi => islossless F.f => islossless D(F,P).distinguish) =>
forall (F <: DFUNCTIONALITY{-DRestr(D)}) (P <: DPRIMITIVE{-DRestr(D)}), islossless P.f =>
islossless P.fi => islossless F.f => islossless DRestr(D, F, P).distinguish`.
`{-DRestr(D)}` excludes `glob DRestr(D)`: `C`'s variables and `glob D`.
EC: `move=> D_ll F P p_ll pi_ll f_ll;proc. call (D_ll (DFRestr(F)) (DPRestr(P)) _ _ _).
+ by apply (rp_ll P). + by apply (rpi_ll P). + by apply (rf_ll F). by inline *;auto.` -/
theorem DRestr_ll (D : DISTINGUISHER) (_hDm : Module.ECModule D distExt)
    (_hD : FVP.fvP D ≤ C.footprintᶜ) :
    (∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D).globᶜ →
      FVP.fvP P ≤ (FVP.fvP D).globᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless) →
    ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (C.footprint ⊔ (FVP.fvP D).glob)ᶜ →
      FVP.fvP P ≤ (C.footprint ⊔ (FVP.fvP D).glob)ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app (DRestr D) (Module.pair F P)).procedure.IsLossless := by
  intro D_ll F P hF hP p_ll pi_ll f_ll
  -- `call (D_ll (DFRestr(F)) (DPRestr(P)) _ _ _)`, with `rp_ll`, `rpi_ll`, `rf_ll`
  have hll := D_ll (Module.app DFRestr F) (Module.app DPRestr P) (by fp_disjoint)
    (by fp_disjoint) (rp_ll P (by fp_disjoint) p_ll) (rpi_ll P (by fp_disjoint) pi_ll)
    (rf_ll F (by fp_disjoint) f_ll)
  rw [Procedure.isLossless_iff_phoareProc] at hll ⊢
  phoare_proc_to_stmt
  -- `inline *;auto`
  phoare_inline 0
  phoare_inline 0
  phoare_wp 6
  phoare_simp [hll]
  phoare_skip
  simp

section RESTR

variable (F : FUNCTIONALITY) (P : PRIMITIVE) (D : DISTINGUISHER)

/-- `declare module F <: FUNCTIONALITY{-C, -Redo}`, `P <: PRIMITIVE{-C, -F, -Redo}`,
`D <: DISTINGUISHER{-F, -P, -C, -Redo}`; `lemma swap_restr &m: Pr[Indif(FRestr(F), PRestr(P),
D).main()@ &m: res] = Pr[Indif(F,P,DRestr(D)).main()@ &m: res]`.
EC: `byequiv=>//;auto. proc;inline *;wp. swap{1}[1..2] 3;sim;auto;call(:true);auto.`
EC's `sim` tracks `={glob D, glob F, glob P, glob C}` and so ignores the left's
`Redo.prefixes <- …` (from `FRestr.init`); here that write is swapped to the end instead, past
the calls that cannot see it (`{-Redo}`), and `equiv_sim` needs equal globals. -/
theorem swap_restr (_hD : Module.ECModule D (distExt))
    (_hF : FVP.fvP F ≤ (C.footprint ⊔ (Redo.prefixes).footprint)ᶜ)
    (_hP : FVP.fvP P ≤ (C.footprint ⊔ (FVP.fvP F).glob ⊔ (Redo.prefixes).footprint)ᶜ)
    (_hDd : FVP.fvP D ≤ ((FVP.fvP F).glob ⊔ (FVP.fvP P).glob ⊔ C.footprint ⊔
      (Redo.prefixes).footprint)ᶜ)
    (m : VariableAssignment) :
    Procedure.Pr (Module.app Indif (Module.pair (FRestr F) (Module.pair (PRestr P) D))).procedure
        () m (fun r _ => r = true) =
      Procedure.Pr (Module.app Indif (Module.pair F (Module.pair P (DRestr D)))).procedure
        () m (fun r _ => r = true) := by
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ _ r₂ _ h => by rw [h]) rfl
  -- `proc;inline *`
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  repeat stmt_inline{1} 1
  repeat stmt_inline{2} 2
  -- `FRestr(F).f` is `DFRestr(F).f`, `PRestr(P).f` is `DPRestr(P).f` (EC: by definition)
  simp only [FRestr, PRestr, Indifferentiability.FUNCTIONALITY.f.mk_simp,
    Indifferentiability.PRIMITIVE.f.mk_simp, Indifferentiability.PRIMITIVE.fi.mk_simp,
    Indifferentiability.DFUNCTIONALITY.mk_f, Indifferentiability.DPRIMITIVE.mk_f_fi,
    Indifferentiability.FUNCTIONALITY.view, Indifferentiability.PRIMITIVE.view]
  -- `Redo.prefixes <- …` to the end; `swap{1}[1..2] 3`: `C.init`'s writes past `P.init();
  -- F.init()`
  stmt_swap{1} 9 3
  stmt_swap{1} 5 4
  stmt_swap{1} 4 4
  -- `wp; sim; auto; call(:true); auto`
  equiv_sim

end RESTR

/-- `Pr_restr`'s oracle subgoal for `f` (EC, inline in its `call`):
`proc; sp; if{1}; 1:by auto; call(_:true); auto. by auto; call{2} f_ll; auto=>/#`: the restricted
oracle against the counting one, up to the bad event `max_size < C.c{2}`, at equal states.
Not an EC lemma. -/
theorem Pr_restr_f_upto (P : PRIMITIVE) (_hP : FVP.fvP P ≤ C.footprintᶜ)
    (f_ll : (Indifferentiability.PRIMITIVE.f state (List block) block P).procedure.IsLossless) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂ ∧ ¬ max_size < C.c.get g₂)
      (Indifferentiability.DPRIMITIVE.f state (List block) block (Module.app DPRestr
        (Indifferentiability.PRIMITIVE.view state (List block) block P))).procedure
      (Indifferentiability.PRIMITIVE.f state (List block) block (Module.app PC P)).procedure
      (fun r₁ g₁ r₂ g₂ => max_size < C.c.get g₂ ∨ (r₁ = r₂ ∧ g₁ = g₂)) := by
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  simp only [Indifferentiability.PRIMITIVE.view_f]
  stmt_wp
  equiv_seq_last 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §allGlobals{1} = §allGlobals{2} ∧
    ¬max_size < §C.c{2})
  · equiv_sim
  · equiv_if{1}
    · stmt_wp{1}
      equiv_call
      equiv_skip
      intro _ _ _ _ _ _ h
      exact ⟨h.1.1, h.1.2.2.1, fun _ _ => Or.inr trivial⟩
    · -- `call{2} f_ll`: the right's call alone, lossless, with `C.c` framed
      have hp : ∀ a, (procedureDenotation
          (Indifferentiability.PRIMITIVE.f state (List block) block P).procedure
            a).inFootprint (C.c.footprint)ᶜ := fun a =>
        ProgramDenotation.inFootprint_mono (Module.Proc.inFootprint_fvP _ a) (by fp_disjoint)
      refine prhlStmt_of_equiv_right (StmtWithHoles.Equiv.skip_seq _).symm
        (prhlStmt_seq_right ?_)
      equiv_skip
      intro σ₂ g₁ _ _ ⟨⟨_, _, hg, _⟩, hguard⟩
      refine ⟨(congrFun (Stmt.ewp_call _ _ _ (fun _ => 1)) σ₂).trans (f_ll _ _),
        fun v hv => Or.inl (hoareStmt.satisfies
          (hoare_call_frame (B := fun τ => max_size < C.c.get τ.globals + 1) C.c hp)
          (fun r g hgc => ?_) v hv)⟩
      subst hg
      simp only [decide_eq_false_iff_not, not_le] at hguard
      change max_size < C.c.get g + 1
      omega

/-- `Pr_restr`'s oracle subgoal for `fi` (EC, inline in its `call`):
`proc; sp; if{1}; 1:by auto; call(_:true); auto. by auto; call{2} fi_ll; auto=>/#`: the restricted
oracle against the counting one, up to the bad event `max_size < C.c{2}`, at equal states.
Not an EC lemma. -/
theorem Pr_restr_fi_upto (P : PRIMITIVE) (_hP : FVP.fvP P ≤ C.footprintᶜ)
    (fi_ll : (Indifferentiability.PRIMITIVE.fi state (List block) block P).procedure.IsLossless) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂ ∧ ¬ max_size < C.c.get g₂)
      (Indifferentiability.DPRIMITIVE.fi state (List block) block (Module.app DPRestr
        (Indifferentiability.PRIMITIVE.view state (List block) block P))).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block) block (Module.app PC P)).procedure
      (fun r₁ g₁ r₂ g₂ => max_size < C.c.get g₂ ∨ (r₁ = r₂ ∧ g₁ = g₂)) := by
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  simp only [Indifferentiability.PRIMITIVE.view_fi]
  stmt_wp
  equiv_seq_last 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §allGlobals{1} = §allGlobals{2} ∧
    ¬max_size < §C.c{2})
  · equiv_sim
  · equiv_if{1}
    · stmt_wp{1}
      equiv_call
      equiv_skip
      intro _ _ _ _ _ _ h
      exact ⟨h.1.1, h.1.2.2.1, fun _ _ => Or.inr trivial⟩
    · -- `call{2} fi_ll`: the right's call alone, lossless, with `C.c` framed
      have hp : ∀ a, (procedureDenotation
          (Indifferentiability.PRIMITIVE.fi state (List block) block P).procedure
            a).inFootprint (C.c.footprint)ᶜ := fun a =>
        ProgramDenotation.inFootprint_mono (Module.Proc.inFootprint_fvP _ a) (by fp_disjoint)
      refine prhlStmt_of_equiv_right (StmtWithHoles.Equiv.skip_seq _).symm
        (prhlStmt_seq_right ?_)
      equiv_skip
      intro σ₂ g₁ _ _ ⟨⟨_, _, hg, _⟩, hguard⟩
      refine ⟨(congrFun (Stmt.ewp_call _ _ _ (fun _ => 1)) σ₂).trans (fi_ll _ _),
        fun v hv => Or.inl (hoareStmt.satisfies
          (hoare_call_frame (B := fun τ => max_size < C.c.get τ.globals + 1) C.c hp)
          (fun r g hgc => ?_) v hv)⟩
      subst hg
      simp only [decide_eq_false_iff_not, not_le] at hguard
      change max_size < C.c.get g + 1
      omega

/-- `Pr_restr`'s oracle subgoal for the functionality (EC, inline in its `call`):
`proc;inline*;sp 1 1;if;auto;if{1};auto;1:by call(_: ={glob P});auto;sim. by call{2} CO_ll;auto=>/#`
— `DFRestr(F)` against `FC(F)`, up to the bad event, at equal states.  Not an EC lemma. -/
theorem Pr_restr_F_upto (F : FUNCTIONALITY) (_hF : FVP.fvP F ≤ C.footprintᶜ)
    (F_ll : (Indifferentiability.FUNCTIONALITY.f state (List block) block F).procedure.IsLossless) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂ ∧ ¬ max_size < C.c.get g₂)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block (Module.app DFRestr
        (Indifferentiability.FUNCTIONALITY.view state (List block) block F))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block) block (Module.app FC F)).procedure
      (fun r₁ g₁ r₂ g₂ => max_size < C.c.get g₂ ∨ (r₁ = r₂ ∧ g₁ = g₂)) := by
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  simp only [Indifferentiability.FUNCTIONALITY.view_f]
  stmt_wp
  equiv_seq_last 1 1 : (§(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2} ∧
    §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧
    §allGlobals{1} = §allGlobals{2} ∧ ¬max_size < §C.c{2})
  · equiv_sim
  · equiv_if
    · equiv_if{1}
      · equiv_sim
      · -- `call{2} CO_ll`: the right's call alone, lossless, with `C.c` framed
        have hp : ∀ a, (procedureDenotation
            (Indifferentiability.FUNCTIONALITY.f state (List block) block F).procedure
              a).inFootprint (C.c.footprint)ᶜ := fun a =>
          ProgramDenotation.inFootprint_mono (Module.Proc.inFootprint_fvP _ a) (by fp_disjoint)
        stmt_wp{2}
        refine prhlStmt_seq_right ?_
        stmt_wp{2}
        equiv_skip
        intro σ₂ g₁ bs₁ _ ⟨⟨⟨hbs, _, hg, _⟩, _⟩, hguard⟩
        refine ⟨(congrFun (Stmt.ewp_call _ _ _ (fun _ => 1)) _).trans (F_ll _ _),
          fun v hv => Or.inl (hoareStmt.satisfies
            (hoare_call_frame (B := fun τ => max_size < C.c.get τ.globals) C.c hp)
            (fun r g hgc => ?_) v hv)⟩
        change max_size < C.c.get g
        rw [hgc]
        subst hg hbs
        simp only [decide_eq_false_iff_not, not_le] at hguard
        simpa [Lens.intoGlobal, Lens.chain, ProgramState.globalL, Lens.set_get] using hguard
    · equiv_sim
    · rintro _ _ _ _ _ _ ⟨rfl, -, rfl, -⟩
      rfl

/-- `Pr_restr`'s oracle subgoal for the counting `f` (EC: `by move=> _;proc;sp;auto;call
f_ll;auto=>/#`, its Hoare part): `PC(P).f` keeps the bad event.  Not an EC lemma. -/
theorem PC_f_bad (P : PRIMITIVE) (_hP : FVP.fvP P ≤ C.footprintᶜ) :
    hoareProc (fun _ g => max_size < C.c.get g ∧ True)
      (Indifferentiability.PRIMITIVE.f state (List block) block (Module.app PC P)).procedure
      (fun _ g => max_size < C.c.get g ∧ True) := by
  hoare_proc_to_stmt
  have hp : ∀ a, (procedureDenotation
      (Indifferentiability.PRIMITIVE.f state (List block) block P).procedure a).inFootprint
      (C.c.footprint)ᶜ := fun a =>
    ProgramDenotation.inFootprint_mono (Module.Proc.inFootprint_fvP _ a) (by fp_disjoint)
  hoare_inline 0
  hoare_wp 2
  hoare_call (hoare_call_frame C.c hp)
  hoare_wp 3
  hoare_skip
  rintro c ⟨hc, -⟩ r g rfl
  omega

/-- `Pr_restr`'s oracle subgoal for the counting `fi` (EC: `by move=> _;proc;sp;auto;call
f_ll;auto=>/#`, its Hoare part): `PC(P).fi` keeps the bad event.  Not an EC lemma. -/
theorem PC_fi_bad (P : PRIMITIVE) (_hP : FVP.fvP P ≤ C.footprintᶜ) :
    hoareProc (fun _ g => max_size < C.c.get g ∧ True)
      (Indifferentiability.PRIMITIVE.fi state (List block) block (Module.app PC P)).procedure
      (fun _ g => max_size < C.c.get g ∧ True) := by
  hoare_proc_to_stmt
  have hp : ∀ a, (procedureDenotation
      (Indifferentiability.PRIMITIVE.fi state (List block) block P).procedure a).inFootprint
      (C.c.footprint)ᶜ := fun a =>
    ProgramDenotation.inFootprint_mono (Module.Proc.inFootprint_fvP _ a) (by fp_disjoint)
  hoare_inline 0
  hoare_wp 2
  hoare_call (hoare_call_frame C.c hp)
  hoare_wp 3
  hoare_skip
  rintro c ⟨hc, -⟩ r g rfl
  omega

/-- `Pr_restr`'s oracle subgoal for the counting functionality (EC: `by move=> _;proc;sp;if;auto;
call CO_ll;auto;smt(prefix_sizel)`, its Hoare part): `FC(F).f` keeps the bad event.  Not an EC
lemma. -/
theorem FC_f_bad (F : FUNCTIONALITY) (_hF : FVP.fvP F ≤ C.footprintᶜ) :
    hoareProc (fun _ g => max_size < C.c.get g ∧ True)
      (Indifferentiability.FUNCTIONALITY.f state (List block) block (Module.app FC F)).procedure
      (fun _ g => max_size < C.c.get g ∧ True) := by
  hoare_proc_to_stmt
  have hp : ∀ a, (procedureDenotation
      (Indifferentiability.FUNCTIONALITY.f state (List block) block F).procedure a).inFootprint
      (C.c.footprint)ᶜ := fun a =>
    ProgramDenotation.inFootprint_mono (Module.Proc.inFootprint_fvP _ a) (by fp_disjoint)
  hoare_inline 0
  hoare_wp 1
  hoare_split 1
  refine hoare_seq (B := fun σ => max_size < C.c.get σ.globals) ?_ ?_
  · refine hoare_pre (hoare_if_wp (At := fun σ => max_size < C.c.get σ.globals)
      (Ae := fun σ => max_size < C.c.get σ.globals) ?_ ?_) fun _ h => ⟨fun _ => h, fun _ => h⟩
    · hoare_wp 1
      hoare_call (hoare_call_frame C.c hp)
      hoare_wp 1
      hoare_skip
      -- the cost `size bs - prefix …` is nonnegative (EC: `smt(prefix_sizel)`)
      intro c bs q hc r g hg
      have := Prefix.prefix_sizel bs (Prefix.get_max_prefix bs (FSet.elems q.fdom))
      omega
    · hoare_wp 1
      hoare_skip
      exact fun _ h => h
  · hoare_wp 3
    hoare_skip
    exact fun _ h => h.1

section COUNT

variable (P : PRIMITIVE) (CO : CONSTRUCTION) (D : DISTINGUISHER)

/-- `declare module P <: PRIMITIVE{-C}`, `CO <: CONSTRUCTION{-C, -P}`,
`D <: DISTINGUISHER{-C, -P, -CO}`, with the axioms `f_ll`, `fi_ll`, `CO_ll`, `D_ll`;
`lemma Pr_restr &m : Pr[Indif(FC(CO(P)), PC(P), D).main()@ &m:res /\ C.c <= max_size] <=
Pr[Indif(CO(P), P, DRestr(D)).main()@ &m:res]`.
EC: `byequiv (_: ={glob D, glob P, glob CO} ==> C.c{1} <= max_size => ={res}); symmetry;
proc;inline *;wp. call (_: max_size < C.c, ={glob P, glob CO, glob C}). + apply D_ll. + …
auto;call (_:true);auto;call(:true);auto=>/#.`  The `call` is the up-to-bad abstract call rule
(`prhlProc_abstract_call_upto_module`; `={glob …}` before the bad event as equal states, its
oracle subgoals `Pr_restr_F_upto`, `Pr_restr_f_upto`, `Pr_restr_fi_upto`, `FC_f_bad`, `PC_f_bad`,
`PC_fi_bad`; `D` lossless with both oracles by `D_ll`, exception E11).
`Pr_restr_of_region` states `D_ll` over a region `G` outside `P`, `CO` and `C` (exception E14);
`Pr_restr` is its instance at `G = glob D`. -/
theorem Pr_restr_of_region (hD : Module.ECModule D (distExt))
    (_hP : FVP.fvP P ≤ C.footprintᶜ)
     (_hCO : FVP.fvP CO ≤ (C.footprint ⊔ (FVP.fvP P).glob)ᶜ)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (FVP.fvP P).glob ⊔ (FVP.fvP CO).glob)ᶜ)
    (f_ll : (Indifferentiability.PRIMITIVE.f state (List block) block P).procedure.IsLossless)
    (fi_ll : (Indifferentiability.PRIMITIVE.fi state (List block) block P).procedure.IsLossless)
    (CO_ll : (Indifferentiability.FUNCTIONALITY.f state (List block) block
      (Module.app CO (Indifferentiability.PRIMITIVE.view state (List block) block
        P))).procedure.IsLossless)
    (G : Footprint VariableAssignment) (_hPG : FVP.fvP P ≤ Gᶜ) (_hCOG : FVP.fvP CO ≤ Gᶜ)
    (_hCG : G ≤ C.footprintᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ Gᶜ →
      FVP.fvP P ≤ Gᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (m : VariableAssignment) :
    Procedure.Pr (Module.app Indif (Module.pair
        (Module.app FC
          (Module.app CO (Indifferentiability.PRIMITIVE.view state (List block) block P)))
        (Module.pair (Module.app PC P) D))).procedure
        () m (fun r g => r = true ∧ C.c.get g ≤ max_size) ≤
      Procedure.Pr (Module.app Indif (Module.pair
        (Module.app CO (Indifferentiability.PRIMITIVE.view state (List block) block P))
        (Module.pair P (DRestr D)))).procedure () m (fun r _ => r = true) := by
  -- EC: `call (_: max_size < C.c, ={glob P, glob CO, glob C})`, `={glob …}` as equal states
  have hcall := prhlProc_abstract_call_upto_module (Lens.pair C.c C.queries) D distExt
    hD.representable (Lens.pair C.c C.queries).compl.footprint
    (by rw [← Lens.compl_footprint, Footprint.lens_pair]; fp_disjoint)
    (le_of_eq (Lens.compl_footprint _).symm)
    (fun n => by
      cases n with
      | zero => exact inferInstanceAs (Countable (List block))
      | succ m => cases m with
        | zero => exact inferInstanceAs (Countable state)
        | succ m => cases m with
          | zero => exact inferInstanceAs (Countable state)
          | succ m => nomatch m)
    (fun ω => max_size < ω.1) (· = ·) (fun _ _ => True)
    (Module.pair (Module.app DFRestr (Indifferentiability.FUNCTIONALITY.view state (List block)
        block (Module.app CO (Indifferentiability.PRIMITIVE.view state (List block) block P))))
      (Module.app DPRestr (Indifferentiability.PRIMITIVE.view state (List block) block P)))
    (Module.pair (Indifferentiability.FUNCTIONALITY.view state (List block) block
        (Module.app FC (Module.app CO (Indifferentiability.PRIMITIVE.view state (List block) block
          P))))
      (Indifferentiability.PRIMITIVE.view state (List block) block (Module.app PC P)))
    -- `apply D_ll` (with `rp_ll`, `rpi_ll`, `rf_ll`, and their counting twins)
    (D_ll _ _ (by fp_disjoint) (by fp_disjoint)
      (rp_ll _ (by fp_disjoint) (by rw [Indifferentiability.PRIMITIVE.view_f]; exact f_ll))
      (rpi_ll _ (by fp_disjoint) (by rw [Indifferentiability.PRIMITIVE.view_fi]; exact fi_ll))
      (rf_ll _ (by fp_disjoint) (by rw [Indifferentiability.FUNCTIONALITY.view_f]; exact CO_ll)))
    (D_ll _ _ (by fp_disjoint) (by fp_disjoint)
      (by rw [Indifferentiability.PRIMITIVE.view_f]; exact pc_f_ll P f_ll)
      (by rw [Indifferentiability.PRIMITIVE.view_fi]; exact pc_fi_ll P fi_ll)
      (by rw [Indifferentiability.FUNCTIONALITY.view_f]; exact fc_ll _ CO_ll))
    -- the oracles, up to the bad event
    (fun n => by
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair]
        exact prhlProc_upto_of_eq _ _ (Pr_restr_F_upto _ (by fp_disjoint) CO_ll)
      | succ m => cases m with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.snd_pair,
            Indifferentiability.PRIMITIVE.view_f]
          exact prhlProc_upto_of_eq _ _ (Pr_restr_f_upto _ (by fp_disjoint) f_ll)
        | succ m => cases m with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.snd_pair,
              Indifferentiability.PRIMITIVE.view_fi]
            exact prhlProc_upto_of_eq _ _ (Pr_restr_fi_upto _ (by fp_disjoint) fi_ll)
          | succ m => nomatch m)
    (fun _ _ _ => hoareProc_true _)
    -- the counting oracles keep the bad event
    (fun n _ => by
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Indifferentiability.FUNCTIONALITY.view_f]
        exact FC_f_bad _ (by fp_disjoint)
      | succ m => cases m with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.snd_pair,
            Indifferentiability.PRIMITIVE.view_f]
          exact PC_f_bad _ (by fp_disjoint)
        | succ m => cases m with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.snd_pair,
              Indifferentiability.PRIMITIVE.view_fi]
            exact PC_fi_bad _ (by fp_disjoint)
          | succ m => nomatch m)
  -- `byequiv (_: ={glob D, glob P, glob CO} ==> C.c{1} <= max_size => ={res})`
  refine Procedure.Pr_le_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ g₁ r₂ _ => C.c.get g₁ ≤ max_size → r₁ = r₂) ?_
    (fun r₁ g₁ r₂ g₂ h hr => h hr.2 ▸ hr.1) rfl
  -- `symmetry; proc; inline *; wp`
  equiv_proc_to_stmt
  equiv_sym
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  repeat stmt_inline{1} 2
  repeat stmt_inline{2} 1
  -- `C.init`'s writes past `P.init(); CO(P).init()` (EC: `auto`, by `{-C}`)
  stmt_swap{2} 5 3
  stmt_swap{2} 4 3
  stmt_wp
  equiv_call hcall
  -- `auto; call (_:true); auto; call(:true); auto=>/#`
  equiv_sim
  intro σ₁ σ₂ h
  refine ⟨h.symm, fun r g => ⟨by simp [Setter.throwaway, ProgramState.globalL],
    fun r' g' => ⟨?_, ?_⟩⟩⟩
  · simp only [Setter.throwaway, ProgramState.globalL, syncInv_compl_eq_iff]
    by_cases hm : max_size < 0
    · exact Or.inl hm
    · refine Or.inr ⟨trivial, ?_⟩
      simpa [Lens.set_get, Lens.get_of_disjoint_set, Lens.get_of_disjoint_set'] using hm
  · intro r₁ g₁ r₂ g₂ hpost hle
    rcases hpost with hb | ⟨hr, _⟩
    · exact absurd hle (not_le.mpr hb)
    · exact hr.symm

/-- EC's `Pr_restr` (see `Pr_restr_of_region`), `D_ll` over `glob D`. -/
theorem Pr_restr (hD : Module.ECModule D (distExt))
    (_hP : FVP.fvP P ≤ C.footprintᶜ)
     (_hCO : FVP.fvP CO ≤ (C.footprint ⊔ (FVP.fvP P).glob)ᶜ)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (FVP.fvP P).glob ⊔ (FVP.fvP CO).glob)ᶜ)
    (f_ll : (Indifferentiability.PRIMITIVE.f state (List block) block P).procedure.IsLossless)
    (fi_ll : (Indifferentiability.PRIMITIVE.fi state (List block) block P).procedure.IsLossless)
    (CO_ll : (Indifferentiability.FUNCTIONALITY.f state (List block) block
      (Module.app CO (Indifferentiability.PRIMITIVE.view state (List block) block
        P))).procedure.IsLossless)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D).globᶜ →
      FVP.fvP P ≤ (FVP.fvP D).globᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (m : VariableAssignment) :
    Procedure.Pr (Module.app Indif (Module.pair
        (Module.app FC
          (Module.app CO (Indifferentiability.PRIMITIVE.view state (List block) block P)))
        (Module.pair (Module.app PC P) D))).procedure
        () m (fun r g => r = true ∧ C.c.get g ≤ max_size) ≤
      Procedure.Pr (Module.app Indif (Module.pair
        (Module.app CO (Indifferentiability.PRIMITIVE.view state (List block) block P))
        (Module.pair P (DRestr D)))).procedure () m (fun r _ => r = true) :=
  Pr_restr_of_region P CO D hD _hP _hCO _hDd f_ll fi_ll CO_ll (FVP.fvP D).glob
    (by fp_disjoint) (by fp_disjoint) (by fp_disjoint) D_ll m

end COUNT

/-! ## The initial game -/

/-- `module GReal(D : DISTINGUISHER) = RealIndif(SqueezelessSponge, PC(Perm), D)`. -/
noncomputable def GReal (D : DISTINGUISHER) : procmod () → Bool :=
  RealIndif SqueezelessSponge (Module.app PC Perm) D

end GaudisCrypt.SHA3.SLCommon
