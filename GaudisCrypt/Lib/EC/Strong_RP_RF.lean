import GaudisCrypt.Lib.EC.PRP
import GaudisCrypt.Lib.EC.Dexcepted
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.Representation
import GaudisCrypt.Logic.EqualOutside
import GaudisCrypt.Logic.PHoare
import GaudisCrypt.FV
import GaudisCrypt.Logic.Granular

/-!
# EasyCrypt's PRP/PRF switching lemma (`theories/crypto/prp_prf/Strong_RP_RF.eca`)

The abstract theory's types `D`, `K` and operators `uD`, `dK`, `q` are section variables (with
their axioms as hypotheses where used), so a `clone` is an application.  Only what ported
developments use is here: `ARP`, `DBounder` and the statement of `Conclusion`.

The `PRPi` clone (`clone import RP as PRPi with op dD <- uD rename "RP" as "PRPi"`) is
`PRP.RP.RP D uD`.  Module variables (`PRPi.m`, `ARP.coll` …) are parameters: a clone of this theory
declares its own `global_var`s and passes them.
-/

namespace GaudisCrypt.EC.Strong_RP_RF

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PRP.StrongPRP

variable (D : Type) [DecidableEq D] [Inhabited D]

variable (uD : SubProbability D) (q : ℤ)

/-! ### Distinguishers are EasyCrypt-like modules

(Exception E2 of the SHA-3 port is a theorem here.) -/

/-- The oracle procedures a `Distinguisher` may call: `f` and `fi`. -/
abbrev SPRP_Oracles.holes : HoleSigs := .cons (procsig (D) -> D) (.cons (procsig (D) -> D) .empty)

/-- `O.f`, `O.fi` out of the oracles `O`. -/
noncomputable def SPRP_Oracles.ext (O : SPRP_Oracles D) : (SPRP_Oracles.holes D).Instantiation :=
  ((SPRP_Oracles.f D O).procedure, (SPRP_Oracles.fi D O).procedure)

/-- **Every `Distinguisher` is representable** over `f` and `fi`
(`Module.representable_of_firstOrder`). -/
theorem Distinguisher.representable (Dist : Distinguisher D) :
    Module.Representable Dist (SPRP_Oracles.ext D) :=
  Module.representable_of_firstOrder (M := SPRP_Oracles D)
    (by change (SPRP_Oracles.typeRep D).FirstOrder
        simp only [SPRP_Oracles.typeRep, ModuleTypeRep.FirstOrder, and_self])
    (fun n => by
      cases n with
      | zero => exact ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
                          exact ⟨default⟩, ⟨default⟩⟩
      | succ n => cases n with
        | zero => exact ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
                            exact ⟨default⟩, ⟨default⟩⟩
        | succ n => nomatch n)
    (SPRP_Oracles.ext D) (fun _ => rfl) Dist

/-- A `Distinguisher` is EasyCrypt-like as soon as it has finitely many globals. -/
theorem Distinguisher.ecModule (Dist : Distinguisher D) (hD : (FVP.fvP Dist).FinitelySupported) :
    Module.ECModule Dist (SPRP_Oracles.ext D) :=
  ⟨Distinguisher.representable D Dist, hD⟩

/-- `clone import RP as PRPi with op dD <- uD rename "RP" as "PRPi"`, with its module variables
`PRPi.m`, `PRPi.mi` passed by the clone. -/
noncomputable abbrev PRPi.PRPi (m mi : Lens (FMap D D) VariableAssignment) := PRP.RP.RP D uD m mi

section ARP
/-! `ARP`'s module variables `coll`, `m`, `mi` are parameters (see `PRP.lean`). -/
variable (coll : Lens Bool VariableAssignment) (m mi : Lens (FMap D D) VariableAssignment)

-- An "almost random permutation": it keeps track of collisions explicitly.
module ARP : (PRP D) {
  proc init () : Unit {
    m <- (FMap.empty : FMap D D);
    mi <- (FMap.empty : FMap D D);
    coll <- false;
    return ()
  };
  proc f (x : D) : D {
    var y : D;
    if (!(decide (FMap.dom ($m : FMap D D) $x))) {
      y <$ uD;
      coll <- $coll || decide (FMap.rng ($m : FMap D D) $y);
      m <- FMap.set $m $x $y;
      mi <- FMap.set $mi $y $x;
    }
    return oget (FMap.get $m $x)
  };
  proc fi (y : D) : D {
    var x : D;
    if (!(decide (FMap.dom ($mi : FMap D D) $y))) {
      x <$ uD;
      coll <- $coll || decide (FMap.rng ($mi : FMap D D) $x);
      m <- FMap.set $m $x $y;
      mi <- FMap.set $mi $y $x;
    }
    return oget (FMap.get $mi $y)
  };
}

end ARP

/-! To factor out the difficult step, the PRP is parameterized by a procedure that samples its
output (EC's `Sample_t`), with two instantiations. -/

-- EC's `module type Sample_t = { proc sample(X:D -> bool): D }`
moduletype Sample_t {
  proc sample (X : D → Prop) -> D;
}

module Direct : (Sample_t D) {
  proc sample (X : D → Prop) : D {
    var r : D;
    r <$ dexcepted uD $X;
    return $r
  };
}

open Classical in
module Indirect : (Sample_t D) {
  proc sample (X : D → Prop) : D {
    var r : D;
    r <$ uD;
    if (decide ($X $r)) {
      r <$ dexcepted uD $X;
    }
    return $r
  };
}

section PRPi'
/-! `PRPi'` uses the `PRPi` clone's variables `PRPi.m`, `PRPi.mi`, parameters (see `PRP.lean`). -/
variable (PRPi_m PRPi_mi : Lens (FMap D D) VariableAssignment)

-- EC's `module PRPi'(S : Sample_t)`; its alias `proc init = PRPi.init` is wrapped in a call
-- (exception E5 of the SHA-3 port)
module PRPi' using (S : Sample_t D) : (PRP D) {
  proc init () : Unit {
    _ <- call (PRP.init D (PRPi.PRPi D uD PRPi_m PRPi_mi)) ();
    return ()
  };
  proc f (x : D) : D {
    var r : D;
    if (!(decide (FMap.dom ($PRPi_m : FMap D D) $x))) {
      r <- call S.sample (FMap.rng ($PRPi_m : FMap D D));
      PRPi_m <- FMap.set $PRPi_m $x $r;
      PRPi_mi <- FMap.set $PRPi_mi (oget (FMap.get ($PRPi_m : FMap D D) $x)) $x;
    }
    return oget (FMap.get ($PRPi_m : FMap D D) $x)
  };
  proc fi (x : D) : D {
    var r : D;
    if (!(decide (FMap.dom ($PRPi_mi : FMap D D) $x))) {
      r <- call S.sample (FMap.rng ($PRPi_mi : FMap D D));
      PRPi_mi <- FMap.set $PRPi_mi $x $r;
      PRPi_m <- FMap.set $PRPi_m (oget (FMap.get ($PRPi_mi : FMap D D) $x)) $x;
    }
    return oget (FMap.get ($PRPi_mi : FMap D D) $x)
  };
}

end PRPi'

section DBounder
/-! `DBounder.FBounder`'s module variable `c` is a parameter (see `PRP.lean`). -/
variable (c : Lens ℤ VariableAssignment)

-- EC's `DBounder(D, F).FBounder`
module DBounder.FBounder using (F : SPRP_Oracles D) : (SPRP_Oracles D) {
  proc f (x : D) : D {
    var r : D;
    r <- default;
    if (decide ($c < q)) {
      r <- call F.f ($x);
      c <- $c + 1;
    }
    return $r
  };
  proc fi (x : D) : D {
    var r : D;
    r <- default;
    if (decide ($c < q)) {
      r <- call F.fi ($x);
      c <- $c + 1;
    }
    return $r
  };
}

-- EC's `DBounder(D : Distinguisher, F : SPRP_Oracles)`, with `D` a Lean parameter so that
-- `DBounder Dist` is a `Distinguisher`
set_option linter.gaudisCrypt.using false in
module DBounder (Dist : Distinguisher D) using (F : SPRP_Oracles D) {
  proc distinguish () : Bool {
    var b : Bool;
    c <- 0;
    b <- call (Module.app Dist (Module.app (DBounder.FBounder D q c) F)) ();
    return $b
  };
}

end DBounder

/-! ### The section `PRPi_PRPi'_Indirect`

`local clone include Dexcepted.TwoStepSampling with type i <- unit, type t <- D, op dt _ <- uD`
is `dexcepted_indirect` (`Lib/EC/Dexcepted.lean`). -/

section PRPi_PRPi'_Indirect

/-- EC's `equiv eq_Direct_Indirect : Direct.sample ~ Indirect.sample : ={X} ==> ={res}` (of the
section `PRPi_PRPi'_Indirect`; here before it, as `PRPi'` follows), with `={glob}` kept (EC's call
rule frames it; `uD` lossless, EC's `dD_ll` of the `TwoStepSampling` clone).  The right side's
run is a sampling from `uD \ X` (`dexcepted_indirect`), coupled by the identity
(`equiv_rnd_run`). -/
theorem eq_Direct_Indirect (huD : is_lossless uD) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂) (Direct.sample D uD).procedure
      (Indirect.sample D uD).procedure (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  equiv_proc
  stmt_inline 0
  stmt_wp
  equiv_rnd_run 2
  stmt_wp
  equiv_skip
  rintro σ₂ g₁ X₁ ⟨hX, hg⟩
  refine ⟨?_, fun _ _ => hg⟩
  generalize hτ : (localVarLens "X0" (D → Prop)).set _ _ = τ
  have hXτ : (localVarLens "X0" (D → Prop)).get τ = X₁ := by rw [← hτ, hX]; simp_reads; trivial
  refine SubProbability.ext_of_expected fun F => ?_
  rw [programDenotation_seq, ProgramDenotation.bind_apply, programDenotation_sample_apply,
    SubProbability.expected_bind, SubProbability.expected_hbind, SubProbability.expected_hbind]
  simp only [expected_pure, programDenotation_ifThenElse_apply]
  simp_reads
  rw [hXτ, ← dexcepted_indirect uD X₁ huD, SubProbability.expected_bind]
  refine congrArg uD.expected (funext fun a => ?_)
  by_cases ha : X₁ a
  · simp only [ha, decide_true, if_true, programDenotation_sample_apply,
      SubProbability.expected_hbind, expected_pure]
    simp only [(localVarLens "r" D).set_set]
    simp_reads
    rw [hXτ]
  · simp only [ha, decide_false, Bool.false_eq_true, if_false, programDenotation_skip_apply,
      expected_pure]
variable (PRPi_m PRPi_mi : Lens (FMap D D) VariableAssignment)

/-- The first half of EC's `transitivity PRPi'(Direct).f` in `eq_PRPi_PRPi'_f_Indirect`:
`PRPi.f ~ PRPi'(Direct).f` (EC's `proc; inline *; if; auto`). -/
theorem eq_PRPi_PRPi'_f_Direct [Lens.Disjoint PRPi_m PRPi_mi] :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (PRP.f D (PRPi.PRPi D uD PRPi_m PRPi_mi)).procedure
      (PRP.f D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Direct D uD))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §allGlobals{1} = §allGlobals{2})
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
      intros
      simp_all [FMap.get_set_sameE, oget]

/-- The second half: `PRPi'(Direct).f ~ PRPi'(Indirect).f` (EC's `proc; if; wp;
call eq_Direct_Indirect`). -/
theorem eq_PRPi'_f_Direct_Indirect (huD : is_lossless uD) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (PRP.f D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Direct D uD))).procedure
      (PRP.f D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  have hs := eq_Direct_Indirect D uD huD
  equiv_proc
  stmt_inline 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §allGlobals{1} = §allGlobals{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» => equiv_skip; intros; simp_all
    case «then» =>
      stmt_wp
      equiv_call hs
      equiv_skip
      rintro g₁ g₂ a₁ a₂ ⟨⟨rfl, rfl⟩, -⟩
      exact ⟨⟨rfl, rfl⟩, by rintro r₁ g₁ r₂ g₂ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩⟩


/-- `eq_PRPi_PRPi'_f_Direct` for `fi`. -/
theorem eq_PRPi_PRPi'_fi_Direct [Lens.Disjoint PRPi_m PRPi_mi] :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (PRP.fi D (PRPi.PRPi D uD PRPi_m PRPi_mi)).procedure
      (PRP.fi D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Direct D uD))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§y{1} = §x0{2} ∧ §allGlobals{1} = §allGlobals{2})
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
      intros
      simp_all [FMap.get_set_sameE, oget]

/-- `eq_PRPi'_f_Direct_Indirect` for `fi`. -/
theorem eq_PRPi'_fi_Direct_Indirect (huD : is_lossless uD) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (PRP.fi D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Direct D uD))).procedure
      (PRP.fi D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  have hs := eq_Direct_Indirect D uD huD
  equiv_proc
  stmt_inline 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §allGlobals{1} = §allGlobals{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» => equiv_skip; intros; simp_all
    case «then» =>
      stmt_wp
      equiv_call hs
      equiv_skip
      rintro g₁ g₂ a₁ a₂ ⟨⟨rfl, rfl⟩, -⟩
      exact ⟨⟨rfl, rfl⟩, by rintro r₁ g₁ r₂ g₂ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩⟩

/-- EC's `local equiv eq_PRPi_PRPi'_f_Indirect : PRPi.f ~ PRPi'(Indirect).f :
={x, PRPi.m, PRPi.mi} ==> ={res, PRPi.m, PRPi.mi}`, at equal states (the invariant of the abstract
call below), by EC's `transitivity PRPi'(Direct).f` (`prhlProc.trans`). -/
theorem eq_PRPi_PRPi'_f_Indirect [Lens.Disjoint PRPi_m PRPi_mi] (huD : is_lossless uD) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (PRP.f D (PRPi.PRPi D uD PRPi_m PRPi_mi)).procedure
      (PRP.f D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) :=
  prhlProc_conseq (prhlProc.trans (eq_PRPi_PRPi'_f_Direct D uD PRPi_m PRPi_mi)
      (eq_PRPi'_f_Direct_Indirect D uD PRPi_m PRPi_mi huD))
    (fun a₁ g₁ _ _ h => ⟨a₁, g₁, ⟨rfl, rfl⟩, h⟩)
    (fun _ _ _ _ ⟨_, _, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ => ⟨h1.trans h3, h2.trans h4⟩)

/-- EC's `local equiv eq_PRPi_PRPi'_fi_Indirect`, as `eq_PRPi_PRPi'_f_Indirect`. -/
theorem eq_PRPi_PRPi'_fi_Indirect [Lens.Disjoint PRPi_m PRPi_mi] (huD : is_lossless uD) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂)
      (PRP.fi D (PRPi.PRPi D uD PRPi_m PRPi_mi)).procedure
      (PRP.fi D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) :=
  prhlProc_conseq (prhlProc.trans (eq_PRPi_PRPi'_fi_Direct D uD PRPi_m PRPi_mi)
      (eq_PRPi'_fi_Direct_Indirect D uD PRPi_m PRPi_mi huD))
    (fun a₁ g₁ _ _ h => ⟨a₁, g₁, ⟨rfl, rfl⟩, h⟩)
    (fun _ _ _ _ ⟨_, _, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ => ⟨h1.trans h3, h2.trans h4⟩)


/-- The `byequiv` of EC's `pr_PRPi_PRPi'_Indirect`: `IND(PRPi, D) ~ IND(PRPi'(Indirect), D)`, by
EC's `call (_: ={PRPi.m, PRPi.mi})` (`prhlProc_abstract_call_equal_outside_module` with `I`
equality; `[Countable D]` for the rule, exception E8). -/
theorem pr_PRPi_PRPi'_Indirect_equiv [Countable D] [Lens.Disjoint PRPi_m PRPi_mi]
    (huD : is_lossless uD) (Dist : Distinguisher D)
    (hDd : FVP.fvP Dist ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (Module.app (IND D) (Module.pair (PRPi.PRPi D uD PRPi_m PRPi_mi) Dist)).procedure
      (Module.app (IND D) (Module.pair (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD))
        Dist)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hcall := prhlProc_abstract_call_equal_outside_module (Lens.pair PRPi_m PRPi_mi) Dist
    (SPRP_Oracles.ext D) (Distinguisher.representable D Dist)
    (by rw [Footprint.lens_pair]; exact hDd) Eq
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable D)
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable D)
        | succ n => nomatch n)
    (SPRP_Oracles.mk D
      { f := PRP.f D (PRPi.PRPi D uD PRPi_m PRPi_mi)
        fi := PRP.fi D (PRPi.PRPi D uD PRPi_m PRPi_mi) })
    (SPRP_Oracles.mk D
      { f := PRP.f D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD))
        fi := PRP.fi D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD)) })
    (fun n => by cases n with
      | zero =>
        simp only [SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_zero_cons,
          SPRP_Oracles.f.mk_simp, Lens.equal_outside_and_get_eq_iff]
        exact eq_PRPi_PRPi'_f_Indirect D uD PRPi_m PRPi_mi huD
      | succ n => cases n with
        | zero =>
          simp only [SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single, SPRP_Oracles.fi.mk_simp,
            Lens.equal_outside_and_get_eq_iff]
          exact eq_PRPi_PRPi'_fi_Indirect D uD PRPi_m PRPi_mi huD
        | succ n => nomatch n)
  simp only [Lens.equal_outside_and_get_eq_iff] at hcall
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_call hcall
  stmt_wp
  equiv_skip
  rintro g₁ g₂ rfl
  exact ⟨rfl, fun _ _ _ _ h => h.1⟩

/-- EC's `pr_PRPi_PRPi'_Indirect &m`, for `declare module D <: Distinguisher {-PRPi}`. -/
theorem pr_PRPi_PRPi'_Indirect [Countable D] [Lens.Disjoint PRPi_m PRPi_mi]
    (huD : is_lossless uD) (Dist : Distinguisher D)
    (hDd : FVP.fvP Dist ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint)ᶜ) (m : VariableAssignment) :
    Procedure.Pr (Module.app (IND D) (Module.pair (PRPi.PRPi D uD PRPi_m PRPi_mi) Dist)).procedure
        () m (fun r _ => r = true) =
      Procedure.Pr (Module.app (IND D) (Module.pair
        (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD)) Dist)).procedure () m
        (fun r _ => r = true) :=
  Procedure.Pr_eq_of_prhlProc (pr_PRPi_PRPi'_Indirect_equiv D uD PRPi_m PRPi_mi huD Dist hDd)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true) (fun r₁ _ r₂ _ h => by rw [h])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl

end PRPi_PRPi'_Indirect

/-- EC's `Conclusion`, for `D <: Distinguisher {-PRPi, -ARP, -DBounder}`, under the theory's
axiom `uD_uf_fu` (`uD` uniform, lossless and full).  `mu uD (pred1 witness)` is the probability of
`default`. -/
theorem Conclusion (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y})
    (PRPi_m PRPi_mi ARP_m ARP_mi : Lens (FMap D D) VariableAssignment)
    (ARP_coll : Lens Bool VariableAssignment) (FBounder_c : Lens ℤ VariableAssignment)
    (Dist : Distinguisher D)
    (_hD : FVP.fvP Dist ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ ARP_m.footprint ⊔
      ARP_mi.footprint ⊔ ARP_coll.footprint ⊔ FBounder_c.footprint)ᶜ)
    (m : VariableAssignment) :
    (∀ O : SPRP_Oracles D, FVP.fvP O ≤ (FVP.fvP Dist).globᶜ →
      (SPRP_Oracles.f D O).procedure.IsLossless → (SPRP_Oracles.fi D O).procedure.IsLossless →
      (Module.app Dist O).procedure.IsLossless) →
    |(Procedure.Pr (Module.app (IND D) (Module.pair (PRPi.PRPi D uD PRPi_m PRPi_mi)
        (DBounder D q FBounder_c Dist))).procedure () m (fun r _ => r = true) : ℝ) -
      (Procedure.Pr (Module.app (IND D) (Module.pair (ARP D uD ARP_coll ARP_m ARP_mi)
        (DBounder D q FBounder_c Dist))).procedure () m (fun r _ => r = true) : ℝ)| ≤
      ((q ^ 2 - q : ℤ) : ℝ) / 2 * (uD.1 {default}).toReal := by
  sorry

end GaudisCrypt.EC.Strong_RP_RF
