import GaudisCrypt.Lib.EC.PRP
import GaudisCrypt.Lib.EC.Dexcepted
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.PHoareWp
import GaudisCrypt.Logic.SyntacticFrame
import GaudisCrypt.Logic.ConcreteFootprint
import GaudisCrypt.Logic.ExpectationCall
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

/-! EC's lossless lemmas (`notin_supportIP`, `excepted_lossless`, `Indirect_ll`,
`PRPi'_Indirect_f_ll`, `PRPi'_Indirect_fi_ll`): only `excepted_lossless` is used downstream
(`ConcreteF`); `uD`'s fullness (`uD_full`) is part of EC's axiom `uD_uf_fu`. -/

omit [DecidableEq D] [Inhabited D] in
/-- `uD` is full (EC's `is_full`, part of `uD_uf_fu`): lossless and uniform, no point has
probability `0`. -/
theorem uD_full (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y}) (x : D) :
    uD.1 {x} ≠ 0 := by
  intro h0
  have hall : ∀ y, uD.1 {y} = 0 := fun y => (uD_uf_fu.2 y x).trans h0
  have h1 := (uD.toPMF uD_uf_fu.1).tsum_coe
  have : ∑' y, (uD.toPMF uD_uf_fu.1) y = 0 := ENNReal.tsum_eq_zero.mpr fun y => hall y
  rw [this] at h1
  exact zero_ne_one h1

/-- `lemma excepted_lossless (m : (D,D) fmap)`: `uD \ rng m` is lossless when `m` misses a key. -/
theorem excepted_lossless (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y})
    (m : FMap D D) (h : ∃ x, ¬ FMap.dom m x) : is_lossless (dexcepted uD (FMap.rng m)) := by
  obtain ⟨y, hy⟩ := FMap.endo_dom_rng m h
  exact dexcepted_ll uD _ uD_uf_fu.1 ⟨y, hy, uD_full D uD uD_uf_fu y⟩
/-! ### The section `Upto`, with `declare module D <: Distinguisher {-PRPi, -ARP}` -/

section Upto

/-! The local module's variable `PRP_indirect_bad.bad` is the lens parameter
`PRP_indirect_bad_bad` (exception E6 of the SHA-3 port). -/
variable (PRPi_m PRPi_mi : Lens (FMap D D) VariableAssignment)
variable (PRP_indirect_bad_bad : Lens Bool VariableAssignment)

open Classical in
-- EC's `local module PRP_indirect_bad` (it has more procedures than `PRP`: no type annotation, its
-- `PRP` view is `PRP_indirect_bad.asPRP`)
module PRP_indirect_bad {
  proc init () : Unit {
    _ <- call (PRP.init D (PRPi.PRPi D uD PRPi_m PRPi_mi)) ();
    PRP_indirect_bad_bad <- false;
    return ()
  };
  proc sample (X : D → Prop) : D {
    var r : D;
    r <$ uD;
    if (decide ($X $r)) {
      PRP_indirect_bad_bad <- true;
      r <$ dexcepted uD $X;
    }
    return $r
  };
  proc f (x : D) : D {
    var r : D;
    if (!(decide (FMap.dom ($PRPi_m : FMap D D) $x))) {
      r <- call (PRP_indirect_bad.sample D uD PRPi_m PRPi_mi PRP_indirect_bad_bad)
        (FMap.rng ($PRPi_m : FMap D D));
      PRPi_m <- FMap.set $PRPi_m $x $r;
      PRPi_mi <- FMap.set $PRPi_mi (oget (FMap.get ($PRPi_m : FMap D D) $x)) $x;
    }
    return oget (FMap.get ($PRPi_m : FMap D D) $x)
  };
  proc fi (y : D) : D {
    var r : D;
    if (!(decide (FMap.dom ($PRPi_mi : FMap D D) $y))) {
      r <- call (PRP_indirect_bad.sample D uD PRPi_m PRPi_mi PRP_indirect_bad_bad)
        (FMap.rng ($PRPi_mi : FMap D D));
      PRPi_mi <- FMap.set $PRPi_mi $y $r;
      PRPi_m <- FMap.set $PRPi_m (oget (FMap.get ($PRPi_mi : FMap D D) $y)) $y;
    }
    return oget (FMap.get ($PRPi_mi : FMap D D) $y)
  };
}

/-- `PRP_indirect_bad` at the module type `PRP`. -/
noncomputable def PRP_indirect_bad.asPRP : PRP D :=
  PRP.mk D
    { init := PRP_indirect_bad.init D uD PRPi_m PRPi_mi PRP_indirect_bad_bad
      f := PRP_indirect_bad.f D uD PRPi_m PRPi_mi PRP_indirect_bad_bad
      fi := PRP_indirect_bad.fi D uD PRPi_m PRPi_mi PRP_indirect_bad_bad }

variable (ARP_coll : Lens Bool VariableAssignment)
  (ARP_m ARP_mi : Lens (FMap D D) VariableAssignment)

/-- The `f` bullet of EC's `call (_: ARP.coll, !PRP_indirect_bad.bad{1} /\\ ={m,mi}(PRPi,ARP),
(PRP_indirect_bad.bad{1} <=> ARP.coll{2}))` in `pr_PRPi'_Indirect_ARP` (EC's `proc; if; inline *;
swap{1} 1; seq 1 4 …; sp; if{1}`): before the bad event `ARP.coll`, the oracles agree; the bad
event comes with `PRP_indirect_bad.bad` (`excepted_lossless` for the resampling). -/
theorem PRP_indirect_bad_f_ARP_f [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_m] [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi]
    [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi] [Lens.Disjoint ARP_m ARP_mi]
    (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y}) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ (¬ PRP_indirect_bad_bad.get g₁ ∧
        PRPi_m.get g₁ = ARP_m.get g₂ ∧ PRPi_mi.get g₁ = ARP_mi.get g₂) ∧ ¬ ARP_coll.get g₂)
      (PRP_indirect_bad.f D uD PRPi_m PRPi_mi PRP_indirect_bad_bad).procedure
      (PRP.f D (ARP D uD ARP_coll ARP_m ARP_mi)).procedure
      (fun r₁ g₁ r₂ g₂ => (ARP_coll.get g₂ ∧ (PRP_indirect_bad_bad.get g₁ ↔ ARP_coll.get g₂)) ∨
        (r₁ = r₂ ∧ (¬ PRP_indirect_bad_bad.get g₁ ∧
          PRPi_m.get g₁ = ARP_m.get g₂ ∧ PRPi_mi.get g₁ = ARP_mi.get g₂) ∧ ¬ ARP_coll.get g₂)) := by
  have := (inferInstance : Lens.Disjoint PRPi_m PRPi_mi).symm
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_m).symm
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_mi).symm
  have := (inferInstance : Lens.Disjoint ARP_coll ARP_m).symm
  have := (inferInstance : Lens.Disjoint ARP_coll ARP_mi).symm
  have := (inferInstance : Lens.Disjoint ARP_m ARP_mi).symm
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{1} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ (¬ §PRP_indirect_bad_bad{1} = true ∧
      §PRPi_m{1} = §ARP_m{2} ∧ §PRPi_mi{1} = §ARP_mi{2}) ∧ ¬ §ARP_coll{2} = true)
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» =>
      equiv_skip
      intros; simp_all
    case «then» =>
      stmt_wp
      equiv_seq 1 0 : (§r0{1} = §y{2} ∧ §X{1} = (§PRPi_m{1}).rng ∧ §x0{1} = §x0{2} ∧
        ¬ (§PRPi_m{1}).dom §x0{1} ∧ (¬ §PRP_indirect_bad_bad{1} = true ∧
        §PRPi_m{1} = §ARP_m{2} ∧ §PRPi_mi{1} = §ARP_mi{2}) ∧ ¬ §ARP_coll{2} = true)
      · equiv_rnd
        stmt_wp
        equiv_skip
        rintro _ _ _ _ _ _ _ _ ⟨⟨rfl, ⟨_, rfl, rfl⟩, _⟩, _⟩
        simp_all
      · equiv_if{1}
        case «then» =>
          stmt_wp{1} 2
          equiv_skip
          rintro σ₁ y₂ x0₂ m₂ mi₂ c₂ ⟨⟨rfl, hX, rfl, hd, ⟨_, rfl, rfl⟩, _⟩, hXr⟩
          refine ⟨?_, fun a _ => Or.inl ?_⟩
          · rw [← is_lossless_iff_expected, hX]
            exact excepted_lossless D uD uD_uf_fu _ ⟨_, hd⟩
          · simp only [decide_eq_true_eq] at hXr
            rw [hX] at hXr
            simp [hXr]
        case «else» =>
          equiv_skip
          rintro σ₁ y₂ x0₂ m₂ mi₂ c₂ ⟨⟨rfl, hX, rfl, hd, ⟨hb, rfl, rfl⟩, hc⟩, hXr⟩
          simp only [decide_eq_false_iff_not] at hXr
          rw [hX] at hXr
          simp_all [FMap.get_set_sameE, oget]

/-- The `fi` bullet of that `call`, as `PRP_indirect_bad_f_ARP_f`. -/
theorem PRP_indirect_bad_fi_ARP_fi [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_m] [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi]
    [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi] [Lens.Disjoint ARP_m ARP_mi]
    (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y}) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ (¬ PRP_indirect_bad_bad.get g₁ ∧
        PRPi_m.get g₁ = ARP_m.get g₂ ∧ PRPi_mi.get g₁ = ARP_mi.get g₂) ∧ ¬ ARP_coll.get g₂)
      (PRP_indirect_bad.fi D uD PRPi_m PRPi_mi PRP_indirect_bad_bad).procedure
      (PRP.fi D (ARP D uD ARP_coll ARP_m ARP_mi)).procedure
      (fun r₁ g₁ r₂ g₂ => (ARP_coll.get g₂ ∧ (PRP_indirect_bad_bad.get g₁ ↔ ARP_coll.get g₂)) ∨
        (r₁ = r₂ ∧ (¬ PRP_indirect_bad_bad.get g₁ ∧
          PRPi_m.get g₁ = ARP_m.get g₂ ∧ PRPi_mi.get g₁ = ARP_mi.get g₂) ∧ ¬ ARP_coll.get g₂)) := by
  have := (inferInstance : Lens.Disjoint PRPi_m PRPi_mi).symm
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_m).symm
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_mi).symm
  have := (inferInstance : Lens.Disjoint ARP_coll ARP_m).symm
  have := (inferInstance : Lens.Disjoint ARP_coll ARP_mi).symm
  have := (inferInstance : Lens.Disjoint ARP_m ARP_mi).symm
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{1} 0
  stmt_wp
  equiv_seq 1 1 : (§y0{1} = §y0{2} ∧ (¬ §PRP_indirect_bad_bad{1} = true ∧
      §PRPi_m{1} = §ARP_m{2} ∧ §PRPi_mi{1} = §ARP_mi{2}) ∧ ¬ §ARP_coll{2} = true)
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» =>
      equiv_skip
      intros; simp_all
    case «then» =>
      stmt_wp
      equiv_seq 1 0 : (§r0{1} = §x0{2} ∧ §X{1} = (§PRPi_mi{1}).rng ∧ §y0{1} = §y0{2} ∧
        ¬ (§PRPi_mi{1}).dom §y0{1} ∧ (¬ §PRP_indirect_bad_bad{1} = true ∧
        §PRPi_m{1} = §ARP_m{2} ∧ §PRPi_mi{1} = §ARP_mi{2}) ∧ ¬ §ARP_coll{2} = true)
      · equiv_rnd
        stmt_wp
        equiv_skip
        rintro _ _ _ _ _ _ _ _ ⟨⟨rfl, ⟨_, rfl, rfl⟩, _⟩, _⟩
        simp_all
      · equiv_if{1}
        case «then» =>
          stmt_wp{1} 2
          equiv_skip
          rintro σ₁ y₂ x0₂ m₂ mi₂ c₂ ⟨⟨rfl, hX, rfl, hd, ⟨_, rfl, rfl⟩, _⟩, hXr⟩
          refine ⟨?_, fun a _ => Or.inl ?_⟩
          · rw [← is_lossless_iff_expected, hX]
            exact excepted_lossless D uD uD_uf_fu _ ⟨_, hd⟩
          · simp only [decide_eq_true_eq] at hXr
            rw [hX] at hXr
            simp [hXr]
        case «else» =>
          equiv_skip
          rintro σ₁ y₂ x0₂ m₂ mi₂ c₂ ⟨⟨rfl, hX, rfl, hd, ⟨hb, rfl, rfl⟩, hc⟩, hXr⟩
          simp only [decide_eq_false_iff_not] at hXr
          rw [hX] at hXr
          simp_all [FMap.get_set_sameE, oget]

/-- EC's `PRP_indirect_bad.bad ==> PRP_indirect_bad.bad` for `f` (the left oracle keeps `invQ`
once `ARP.coll` holds). -/
theorem PRP_indirect_bad_f_bad [Lens.Disjoint PRP_indirect_bad_bad PRPi_m]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi] :
    hoareProc (fun _ g => PRP_indirect_bad_bad.get g = true)
      (PRP_indirect_bad.f D uD PRPi_m PRPi_mi PRP_indirect_bad_bad).procedure
      (fun _ g => PRP_indirect_bad_bad.get g = true) := by
  hoare_proc_to_stmt
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_m).symm
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_mi).symm
  repeat hoare_inline 0
  hoare_wp 1
  hoare_split 1
  refine hoare_seq (B := fun σ => PRP_indirect_bad_bad.get σ.globals = true) ?_ ?_
  · refine hoare_pre (hoare_if_wp (At := fun σ => PRP_indirect_bad_bad.get σ.globals = true)
      (Ae := fun σ => PRP_indirect_bad_bad.get σ.globals = true) ?_ ?_)
      fun _ h => ⟨fun _ => h, fun _ => h⟩
    · hoare_wp 3
      hoare_split 1
      refine hoare_seq (B := fun σ => PRP_indirect_bad_bad.get σ.globals = true) ?_ ?_
      · refine hoare_pre (hoare_if_wp (At := fun σ => PRP_indirect_bad_bad.get σ.globals = true)
          (Ae := fun σ => PRP_indirect_bad_bad.get σ.globals = true) ?_ ?_)
          fun _ h => ⟨fun _ => h, fun _ => h⟩
        · hoare_wp 2
          hoare_skip
          intros; simp_all
        · hoare_skip
          intros; simp_all
      · hoare_wp 3
        hoare_skip
        intros; simp_all
    · hoare_skip
      intros; simp_all
  · hoare_wp 2
    hoare_skip
    intros; simp_all

/-- `PRP_indirect_bad_f_bad` for `fi`. -/
theorem PRP_indirect_bad_fi_bad [Lens.Disjoint PRP_indirect_bad_bad PRPi_m]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi] :
    hoareProc (fun _ g => PRP_indirect_bad_bad.get g = true)
      (PRP_indirect_bad.fi D uD PRPi_m PRPi_mi PRP_indirect_bad_bad).procedure
      (fun _ g => PRP_indirect_bad_bad.get g = true) := by
  hoare_proc_to_stmt
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_m).symm
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_mi).symm
  repeat hoare_inline 0
  hoare_wp 1
  hoare_split 1
  refine hoare_seq (B := fun σ => PRP_indirect_bad_bad.get σ.globals = true) ?_ ?_
  · refine hoare_pre (hoare_if_wp (At := fun σ => PRP_indirect_bad_bad.get σ.globals = true)
      (Ae := fun σ => PRP_indirect_bad_bad.get σ.globals = true) ?_ ?_)
      fun _ h => ⟨fun _ => h, fun _ => h⟩
    · hoare_wp 3
      hoare_split 1
      refine hoare_seq (B := fun σ => PRP_indirect_bad_bad.get σ.globals = true) ?_ ?_
      · refine hoare_pre (hoare_if_wp (At := fun σ => PRP_indirect_bad_bad.get σ.globals = true)
          (Ae := fun σ => PRP_indirect_bad_bad.get σ.globals = true) ?_ ?_)
          fun _ h => ⟨fun _ => h, fun _ => h⟩
        · hoare_wp 2
          hoare_skip
          intros; simp_all
        · hoare_skip
          intros; simp_all
      · hoare_wp 3
        hoare_skip
        intros; simp_all
    · hoare_skip
      intros; simp_all
  · hoare_wp 2
    hoare_skip
    intros; simp_all

/-- `ARP.f` keeps `ARP.coll` and `invQ` (EC's `move=> &1; proc; if; auto`). -/
theorem ARP_f_coll [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi] (b : Bool) :
    hoareProc (fun _ g => ARP_coll.get g = true ∧ (b = true ↔ ARP_coll.get g = true))
      (PRP.f D (ARP D uD ARP_coll ARP_m ARP_mi)).procedure
      (fun _ g => ARP_coll.get g = true ∧ (b = true ↔ ARP_coll.get g = true)) := by
  hoare_proc_to_stmt
  have := (inferInstance : Lens.Disjoint ARP_coll ARP_m).symm
  have := (inferInstance : Lens.Disjoint ARP_coll ARP_mi).symm
  hoare_inline 0
  hoare_wp 1
  hoare_split 1
  refine hoare_seq (B := fun σ => ARP_coll.get σ.globals = true ∧
    (b = true ↔ ARP_coll.get σ.globals = true)) ?_ ?_
  · refine hoare_pre (hoare_if_wp (At := fun σ => ARP_coll.get σ.globals = true ∧
        (b = true ↔ ARP_coll.get σ.globals = true))
      (Ae := fun σ => ARP_coll.get σ.globals = true ∧ (b = true ↔ ARP_coll.get σ.globals = true))
      ?_ ?_) fun _ h => ⟨fun _ => h, fun _ => h⟩
    · hoare_wp 4
      hoare_skip
      intros; simp_all
    · hoare_skip
      intros; simp_all
  · hoare_wp 2
    hoare_skip
    intros; simp_all

/-- `ARP_f_coll` for `fi`. -/
theorem ARP_fi_coll [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi] (b : Bool) :
    hoareProc (fun _ g => ARP_coll.get g = true ∧ (b = true ↔ ARP_coll.get g = true))
      (PRP.fi D (ARP D uD ARP_coll ARP_m ARP_mi)).procedure
      (fun _ g => ARP_coll.get g = true ∧ (b = true ↔ ARP_coll.get g = true)) := by
  hoare_proc_to_stmt
  have := (inferInstance : Lens.Disjoint ARP_coll ARP_m).symm
  have := (inferInstance : Lens.Disjoint ARP_coll ARP_mi).symm
  hoare_inline 0
  hoare_wp 1
  hoare_split 1
  refine hoare_seq (B := fun σ => ARP_coll.get σ.globals = true ∧
    (b = true ↔ ARP_coll.get σ.globals = true)) ?_ ?_
  · refine hoare_pre (hoare_if_wp (At := fun σ => ARP_coll.get σ.globals = true ∧
        (b = true ↔ ARP_coll.get σ.globals = true))
      (Ae := fun σ => ARP_coll.get σ.globals = true ∧ (b = true ↔ ARP_coll.get σ.globals = true))
      ?_ ?_) fun _ h => ⟨fun _ => h, fun _ => h⟩
    · hoare_wp 4
      hoare_skip
      intros; simp_all
    · hoare_skip
      intros; simp_all
  · hoare_wp 2
    hoare_skip
    intros; simp_all

/-- `ARP.f` is lossless. -/
theorem ARP_f_ll (huD : is_lossless uD) :
    (PRP.f D (ARP D uD ARP_coll ARP_m ARP_mi)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_ewp
  have h1 := (is_lossless_iff_expected uD).mp huD
  split_ifs <;> simp [h1]

/-- `ARP.fi` is lossless. -/
theorem ARP_fi_ll (huD : is_lossless uD) :
    (PRP.fi D (ARP D uD ARP_coll ARP_m ARP_mi)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_ewp
  have h1 := (is_lossless_iff_expected uD).mp huD
  split_ifs <;> simp [h1]

/-- `PRP_indirect_bad.f` is lossless (EC: `seq 2: (X = rng PRPi.m /\\ x \\notin PRPi.m) …`,
`excepted_lossless`). -/
theorem PRP_indirect_bad_f_ll (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y}) :
    (PRP_indirect_bad.f D uD PRPi_m PRPi_mi PRP_indirect_bad_bad).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  rename_i σ _
  have h1 := (is_lossless_iff_expected uD).mp uD_uf_fu.1
  split_ifs with hd
  · rfl
  · have h2 := (is_lossless_iff_expected _).mp
      (excepted_lossless D uD uD_uf_fu (PRPi_m.get σ.globals) ⟨_, hd⟩)
    simp [h1, h2]

/-- `PRP_indirect_bad.fi` is lossless. -/
theorem PRP_indirect_bad_fi_ll (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y}) :
    (PRP_indirect_bad.fi D uD PRPi_m PRPi_mi PRP_indirect_bad_bad).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  rename_i σ _
  have h1 := (is_lossless_iff_expected uD).mp uD_uf_fu.1
  split_ifs with hd
  · rfl
  · have h2 := (is_lossless_iff_expected _).mp
      (excepted_lossless D uD uD_uf_fu (PRPi_mi.get σ.globals) ⟨_, hd⟩)
    simp [h1, h2]


@[fp_bound] theorem fvP_ARP [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi]
    [Lens.Disjoint ARP_m ARP_mi] :
    FVP.fvP (ARP D uD ARP_coll ARP_m ARP_mi) ≤
      ARP_coll.footprint ⊔ (ARP_m.footprint ⊔ ARP_mi.footprint) := by
  fp_module (Lens.pair ARP_coll (Lens.pair ARP_m ARP_mi))

@[fp_bound] theorem fvP_PRP_indirect_bad_asPRP [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_m] [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi] :
    FVP.fvP (PRP_indirect_bad.asPRP D uD PRPi_m PRPi_mi PRP_indirect_bad_bad) ≤
      PRPi_m.footprint ⊔ (PRPi_mi.footprint ⊔ PRP_indirect_bad_bad.footprint) := by
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_m).symm
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_mi).symm
  fp_module (Lens.pair PRPi_m (Lens.pair PRPi_mi PRP_indirect_bad_bad))
@[fp_bound] theorem fvP_ARP_f [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi]
    [Lens.Disjoint ARP_m ARP_mi] :
    FVP.fvP (PRP.f D (ARP D uD ARP_coll ARP_m ARP_mi)) ≤
      ARP_coll.footprint ⊔ (ARP_m.footprint ⊔ ARP_mi.footprint) := by
  fp_module (Lens.pair ARP_coll (Lens.pair ARP_m ARP_mi))

@[fp_bound] theorem fvP_ARP_fi [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi]
    [Lens.Disjoint ARP_m ARP_mi] :
    FVP.fvP (PRP.fi D (ARP D uD ARP_coll ARP_m ARP_mi)) ≤
      ARP_coll.footprint ⊔ (ARP_m.footprint ⊔ ARP_mi.footprint) := by
  fp_module (Lens.pair ARP_coll (Lens.pair ARP_m ARP_mi))

@[fp_bound] theorem fvP_PRP_indirect_bad_f [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_m] [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi] :
    FVP.fvP (PRP.f D (PRP_indirect_bad.asPRP D uD PRPi_m PRPi_mi PRP_indirect_bad_bad)) ≤
      PRPi_m.footprint ⊔ (PRPi_mi.footprint ⊔ PRP_indirect_bad_bad.footprint) := by
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_m).symm
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_mi).symm
  fp_module (Lens.pair PRPi_m (Lens.pair PRPi_mi PRP_indirect_bad_bad))

@[fp_bound] theorem fvP_PRP_indirect_bad_fi [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_m] [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi] :
    FVP.fvP (PRP.fi D (PRP_indirect_bad.asPRP D uD PRPi_m PRPi_mi PRP_indirect_bad_bad)) ≤
      PRPi_m.footprint ⊔ (PRPi_mi.footprint ⊔ PRP_indirect_bad_bad.footprint) := by
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_m).symm
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_mi).symm
  fp_module (Lens.pair PRPi_m (Lens.pair PRPi_mi PRP_indirect_bad_bad))

/-- The `f` oracle of EC's `PRPi'_Indirect_eq` (`inline *; sim`): `PRPi'(Indirect).f` and
`PRP_indirect_bad.f` agree, the states equal except on `PRP_indirect_bad.bad`. -/
theorem PRPi'_Indirect_f_bad_f [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_m]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi] :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ PRP_indirect_bad_bad.equal_outside g₁ g₂ ∧ True)
      (PRP.f D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD))).procedure
      (PRP_indirect_bad.f D uD PRPi_m PRPi_mi PRP_indirect_bad_bad).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ PRP_indirect_bad_bad.equal_outside g₁ g₂ ∧ True) := by
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_m).symm
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_mi).symm
  have := (inferInstance : Lens.Disjoint PRPi_m PRPi_mi).symm
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧
      PRP_indirect_bad_bad.equal_outside §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ a₁ a₂ ⟨rfl, h⟩
    exact ⟨rfl, h⟩
  · equiv_if
    case guard =>
      rintro g₁ g₂ a₁ a₂ ⟨rfl, h⟩
      rw [h.get_disjoint (X := PRPi_m)]
    case «else» =>
      equiv_skip
      rintro g₁ g₂ a₁ a₂ ⟨⟨rfl, h⟩, -⟩
      exact ⟨by rw [h.get_disjoint (X := PRPi_m)], h⟩
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§r0{1} = §r0{2} ∧ §X{1} = §X{2} ∧ §x0{1} = §x0{2} ∧
        PRP_indirect_bad_bad.equal_outside §allGlobals{1} §allGlobals{2})
      · equiv_rnd
        stmt_wp
        equiv_skip
        rintro g₁ g₂ a₁ a₂ ⟨⟨rfl, h⟩, -⟩ _ _
        exact ⟨by rw [h.get_disjoint (X := PRPi_m)], rfl, h⟩
      · equiv_if
        case guard =>
          rintro σ₁ σ₂ ⟨h1, h2, -, -⟩
          exact decide_eq_decide.mpr (by rw [h1]; exact Iff.of_eq (congrFun h2 _))
        case «then» =>
          equiv_rnd
          stmt_wp
          equiv_skip
          rintro σ₁ g₂ r0₂ X₂ x0₂ ⟨⟨hr, hX, hx, h⟩, -⟩
          rw [hX, hx]
          generalize σ₁.globals = g₁ at h ⊢
          refine ⟨rfl, fun a _ => ?_⟩
          rw [← h.get_disjoint (X := PRPi_m), ← h.get_disjoint (X := PRPi_mi)]
          exact ⟨rfl, (((h.set_right _).set_disjoint _).set_disjoint _)⟩
        case «else» =>
          equiv_skip
          rintro σ₁ g₂ r0₂ X₂ x0₂ ⟨⟨hr, -, hx, h⟩, -⟩
          rw [hr, hx]
          generalize σ₁.globals = g₁ at h ⊢
          rw [← h.get_disjoint (X := PRPi_m), ← h.get_disjoint (X := PRPi_mi)]
          exact ⟨rfl, (h.set_disjoint _).set_disjoint _⟩
/-- The `fi` oracle of EC's `PRPi'_Indirect_eq`. -/
theorem PRPi'_Indirect_fi_bad_fi [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_m]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi] :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ PRP_indirect_bad_bad.equal_outside g₁ g₂ ∧ True)
      (PRP.fi D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD))).procedure
      (PRP_indirect_bad.fi D uD PRPi_m PRPi_mi PRP_indirect_bad_bad).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ PRP_indirect_bad_bad.equal_outside g₁ g₂ ∧ True) := by
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_m).symm
  have := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_mi).symm
  have := (inferInstance : Lens.Disjoint PRPi_m PRPi_mi).symm
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §y0{2} ∧
      PRP_indirect_bad_bad.equal_outside §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ a₁ a₂ ⟨rfl, h⟩
    exact ⟨rfl, h⟩
  · equiv_if
    case guard =>
      rintro g₁ g₂ a₁ a₂ ⟨rfl, h⟩
      rw [h.get_disjoint (X := PRPi_mi)]
    case «else» =>
      equiv_skip
      rintro g₁ g₂ a₁ a₂ ⟨⟨rfl, h⟩, -⟩
      exact ⟨by rw [h.get_disjoint (X := PRPi_mi)], h⟩
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§r0{1} = §r0{2} ∧ §X{1} = §X{2} ∧ §x0{1} = §y0{2} ∧
        PRP_indirect_bad_bad.equal_outside §allGlobals{1} §allGlobals{2})
      · equiv_rnd
        stmt_wp
        equiv_skip
        rintro g₁ g₂ a₁ a₂ ⟨⟨rfl, h⟩, -⟩ _ _
        exact ⟨by rw [h.get_disjoint (X := PRPi_mi)], rfl, h⟩
      · equiv_if
        case guard =>
          rintro σ₁ σ₂ ⟨h1, h2, -, -⟩
          exact decide_eq_decide.mpr (by rw [h1]; exact Iff.of_eq (congrFun h2 _))
        case «then» =>
          equiv_rnd
          stmt_wp
          equiv_skip
          rintro σ₁ g₂ r0₂ X₂ x0₂ ⟨⟨hr, hX, hx, h⟩, -⟩
          rw [hX, hx]
          generalize σ₁.globals = g₁ at h ⊢
          refine ⟨rfl, fun a _ => ?_⟩
          rw [← h.get_disjoint (X := PRPi_m), ← h.get_disjoint (X := PRPi_mi)]
          exact ⟨rfl, (((h.set_right _).set_disjoint _).set_disjoint _)⟩
        case «else» =>
          equiv_skip
          rintro σ₁ g₂ r0₂ X₂ x0₂ ⟨⟨hr, -, hx, h⟩, -⟩
          rw [hr, hx]
          generalize σ₁.globals = g₁ at h ⊢
          rw [← h.get_disjoint (X := PRPi_m), ← h.get_disjoint (X := PRPi_mi)]
          exact ⟨rfl, (h.set_disjoint _).set_disjoint _⟩


/-- The `byequiv` of EC's `local lemma PRPi'_Indirect_eq` (`proc; inline *; sim`): the distinguisher
called with the two oracles, the states equal except on `PRP_indirect_bad.bad`
(`prhlProc_abstract_call_equal_outside_module`). -/
theorem PRPi'_Indirect_eq_equiv [Countable D] [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_m] [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi]
    (Dist : Distinguisher D) (hDd : FVP.fvP Dist ≤ (PRP_indirect_bad_bad.footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (Module.app (IND D) (Module.pair (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD))
        Dist)).procedure
      (Module.app (IND D) (Module.pair
        (PRP_indirect_bad.asPRP D uD PRPi_m PRPi_mi PRP_indirect_bad_bad) Dist)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hcall := prhlProc_abstract_call_equal_outside_module PRP_indirect_bad_bad Dist
    (SPRP_Oracles.ext D) (Distinguisher.representable D Dist) hDd (fun _ _ => True)
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable D)
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable D)
        | succ n => nomatch n)
    (SPRP_Oracles.mk D
      { f := PRP.f D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD))
        fi := PRP.fi D (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD)) })
    (SPRP_Oracles.mk D
      { f := PRP.f D (PRP_indirect_bad.asPRP D uD PRPi_m PRPi_mi PRP_indirect_bad_bad)
        fi := PRP.fi D (PRP_indirect_bad.asPRP D uD PRPi_m PRPi_mi PRP_indirect_bad_bad) })
    (fun n => by cases n with
      | zero =>
        simp only [SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_zero_cons,
          SPRP_Oracles.f.mk_simp, PRP_indirect_bad.asPRP, PRP.f.mk_simp]
        exact PRPi'_Indirect_f_bad_f D uD PRPi_m PRPi_mi PRP_indirect_bad_bad
      | succ n => cases n with
        | zero =>
          simp only [SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single, SPRP_Oracles.fi.mk_simp,
            PRP_indirect_bad.asPRP, PRP.fi.mk_simp]
          exact PRPi'_Indirect_fi_bad_fi D uD PRPi_m PRPi_mi PRP_indirect_bad_bad
        | succ n => nomatch n)
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_call hcall
  stmt_wp
  equiv_skip
  rintro g₁ g₂ rfl
  exact ⟨(Lens.equal_outside.refl _).set_right _, fun _ _ _ _ h => h.1⟩
/-- The `byequiv: PRP_indirect_bad.bad` of EC's `pr_PRPi'_Indirect_ARP`: EC's
`call (_: ARP.coll, !PRP_indirect_bad.bad{1} /\\ ={m,mi}(PRPi,ARP),
(PRP_indirect_bad.bad{1} <=> ARP.coll{2}))` (`prhlProc_abstract_call_upto_module`, the oracle state
of both sides as one lens, `={glob D}` framed syntactically: `prhlProc_upto_of_writesKeep`;
`D` lossless with both oracles by `D_ll`, exception E11), then `inline *; auto`. -/
theorem pr_PRPi'_Indirect_ARP_equiv [Countable D] [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_m] [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi]
    [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi] [Lens.Disjoint ARP_m ARP_mi]
    [Lens.Disjoint PRPi_m ARP_m] [Lens.Disjoint PRPi_m ARP_mi] [Lens.Disjoint PRPi_m ARP_coll]
    [Lens.Disjoint PRPi_mi ARP_m] [Lens.Disjoint PRPi_mi ARP_mi] [Lens.Disjoint PRPi_mi ARP_coll]
    [Lens.Disjoint PRP_indirect_bad_bad ARP_m] [Lens.Disjoint PRP_indirect_bad_bad ARP_mi]
    [Lens.Disjoint PRP_indirect_bad_bad ARP_coll]
    (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y})
    (Dist : Distinguisher D) (G : Footprint VariableAssignment) (hDG : FVP.fvP Dist ≤ G)
    (hG : G ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ PRP_indirect_bad_bad.footprint ⊔
      ARP_coll.footprint ⊔ ARP_m.footprint ⊔ ARP_mi.footprint)ᶜ)
    (D_ll : ∀ O : SPRP_Oracles D, FVP.fvP O ≤ Gᶜ →
      (SPRP_Oracles.f D O).procedure.IsLossless → (SPRP_Oracles.fi D O).procedure.IsLossless →
      (Module.app Dist O).procedure.IsLossless) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (Module.app (IND D) (Module.pair
        (PRP_indirect_bad.asPRP D uD PRPi_m PRPi_mi PRP_indirect_bad_bad) Dist)).procedure
      (Module.app (IND D) (Module.pair (ARP D uD ARP_coll ARP_m ARP_mi) Dist)).procedure
      (fun r₁ g₁ r₂ g₂ => (ARP_coll.get g₂ ∧ (PRP_indirect_bad_bad.get g₁ ↔ ARP_coll.get g₂)) ∨
        (r₁ = r₂ ∧ ¬ PRP_indirect_bad_bad.get g₁ ∧ ¬ ARP_coll.get g₂)) := by
  have hll₁ : (Module.app Dist (SPRP_Oracles.mk D
      { f := PRP.f D (PRP_indirect_bad.asPRP D uD PRPi_m PRPi_mi PRP_indirect_bad_bad)
        fi := PRP.fi D
          (PRP_indirect_bad.asPRP D uD PRPi_m PRPi_mi PRP_indirect_bad_bad) })).procedure
      |>.IsLossless := by
    refine D_ll _ (by fp_disjoint) ?_ ?_
    · simp only [SPRP_Oracles.f.mk_simp, PRP_indirect_bad.asPRP, PRP.f.mk_simp]
      exact PRP_indirect_bad_f_ll D uD PRPi_m PRPi_mi PRP_indirect_bad_bad uD_uf_fu
    · simp only [SPRP_Oracles.fi.mk_simp, PRP_indirect_bad.asPRP, PRP.fi.mk_simp]
      exact PRP_indirect_bad_fi_ll D uD PRPi_m PRPi_mi PRP_indirect_bad_bad uD_uf_fu
  have hll₂ : (Module.app Dist (SPRP_Oracles.mk D
      { f := PRP.f D (ARP D uD ARP_coll ARP_m ARP_mi)
        fi := PRP.fi D (ARP D uD ARP_coll ARP_m ARP_mi) })).procedure.IsLossless := by
    refine D_ll _ (by fp_disjoint) ?_ ?_
    · simp only [SPRP_Oracles.f.mk_simp]
      exact ARP_f_ll D uD ARP_coll ARP_m ARP_mi uD_uf_fu.1
    · simp only [SPRP_Oracles.fi.mk_simp]
      exact ARP_fi_ll D uD ARP_coll ARP_m ARP_mi uD_uf_fu.1
  have hDd : FVP.fvP Dist ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔
      PRP_indirect_bad_bad.footprint ⊔ ARP_coll.footprint ⊔ ARP_m.footprint ⊔ ARP_mi.footprint)ᶜ :=
    hDG.trans hG
  have hFm : PRPi_m.footprint ≤ (FVP.fvP Dist)ᶜ := (Footprint.le_compl_comm _ _).mp
    (hDd.trans (Footprint.compl_antimono (le_sup_left.trans (le_sup_left.trans
      (le_sup_left.trans (le_sup_left.trans le_sup_left))))))
  have hFmi : PRPi_mi.footprint ≤ (FVP.fvP Dist)ᶜ := (Footprint.le_compl_comm _ _).mp
    (hDd.trans (Footprint.compl_antimono (le_sup_right.trans (le_sup_left.trans
      (le_sup_left.trans (le_sup_left.trans le_sup_left))))))
  have hFb : PRP_indirect_bad_bad.footprint ≤ (FVP.fvP Dist)ᶜ := (Footprint.le_compl_comm _ _).mp
    (hDd.trans (Footprint.compl_antimono (le_sup_right.trans (le_sup_left.trans
      (le_sup_left.trans le_sup_left)))))
  have hFc : ARP_coll.footprint ≤ (FVP.fvP Dist)ᶜ := (Footprint.le_compl_comm _ _).mp
    (hDd.trans (Footprint.compl_antimono (le_sup_right.trans (le_sup_left.trans le_sup_left))))
  have hFam : ARP_m.footprint ≤ (FVP.fvP Dist)ᶜ := (Footprint.le_compl_comm _ _).mp
    (hDd.trans (Footprint.compl_antimono (le_sup_right.trans le_sup_left)))
  have hFami : ARP_mi.footprint ≤ (FVP.fvP Dist)ᶜ := (Footprint.le_compl_comm _ _).mp
    (hDd.trans (Footprint.compl_antimono (le_sup_right)))
  haveI := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_m).symm
  haveI := (inferInstance : Lens.Disjoint PRP_indirect_bad_bad PRPi_mi).symm
  haveI := (inferInstance : Lens.Disjoint ARP_coll ARP_m).symm
  haveI := (inferInstance : Lens.Disjoint ARP_coll ARP_mi).symm
  -- the oracle state, both sides: `PRPi.m, PRPi.mi, PRP_indirect_bad.bad` and `ARP.m, ARP.mi,
  -- ARP.coll`
  have hFL : FVP.fvP Dist ≤ ((Lens.pair (Lens.pair PRPi_m (Lens.pair PRPi_mi PRP_indirect_bad_bad))
      (Lens.pair ARP_m (Lens.pair ARP_mi ARP_coll))).footprint)ᶜ := by
    rw [Footprint.lens_pair, Footprint.lens_pair, Footprint.lens_pair, Footprint.lens_pair,
      Footprint.lens_pair]
    refine hDd.trans (Footprint.compl_antimono (le_of_eq ?_))
    ac_rfl
  have hcall := prhlProc_abstract_call_upto_module
    (Lens.pair (Lens.pair PRPi_m (Lens.pair PRPi_mi PRP_indirect_bad_bad))
      (Lens.pair ARP_m (Lens.pair ARP_mi ARP_coll))) Dist (SPRP_Oracles.ext D)
    (Distinguisher.representable D Dist) (FVP.fvP Dist) le_rfl hFL
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable D)
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable D)
        | succ n => nomatch n)
    (fun ω => ω.2.2.2 = true)
    (fun ω₁ ω₂ => ¬ ω₁.1.2.2 = true ∧ ω₁.1.1 = ω₂.2.1 ∧ ω₁.1.2.1 = ω₂.2.2.1)
    (fun ω₁ ω₂ => (ω₁.1.2.2 = true ↔ ω₂.2.2.2 = true)) _ _ hll₁ hll₂
    (fun n => by cases n with
      | zero =>
        simp only [SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_zero_cons,
          SPRP_Oracles.f.mk_simp, PRP_indirect_bad.asPRP, PRP.f.mk_simp]
        refine prhlProc_upto_of_writesKeep _ ?_ ?_
          (PRP_indirect_bad_f_ARP_f D uD PRPi_m PRPi_mi PRP_indirect_bad_bad ARP_coll ARP_m ARP_mi
            uD_uf_fu)
        · writes_keep
        · writes_keep
      | succ n => cases n with
        | zero =>
          simp only [SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single, SPRP_Oracles.fi.mk_simp,
            PRP_indirect_bad.asPRP, PRP.fi.mk_simp]
          refine prhlProc_upto_of_writesKeep _ ?_ ?_
            (PRP_indirect_bad_fi_ARP_fi D uD PRPi_m PRPi_mi PRP_indirect_bad_bad ARP_coll ARP_m
              ARP_mi uD_uf_fu)
          · writes_keep
          · writes_keep
        | succ n => nomatch n)
    (fun n ω₂ hb => by cases n with
      | zero =>
        simp only [SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_zero_cons,
          SPRP_Oracles.f.mk_simp, PRP_indirect_bad.asPRP, PRP.f.mk_simp, hb, iff_true]
        exact PRP_indirect_bad_f_bad D uD PRPi_m PRPi_mi PRP_indirect_bad_bad
      | succ n => cases n with
        | zero =>
          simp only [SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single, SPRP_Oracles.fi.mk_simp,
            PRP_indirect_bad.asPRP, PRP.fi.mk_simp, hb, iff_true]
          exact PRP_indirect_bad_fi_bad D uD PRPi_m PRPi_mi PRP_indirect_bad_bad
        | succ n => nomatch n)
    (fun n ω₁ => by cases n with
      | zero =>
        simp only [SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_zero_cons,
          SPRP_Oracles.f.mk_simp]
        exact ARP_f_coll D uD ARP_coll ARP_m ARP_mi ω₁.1.2.2
      | succ n => cases n with
        | zero =>
          simp only [SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single, SPRP_Oracles.fi.mk_simp]
          exact ARP_fi_coll D uD ARP_coll ARP_m ARP_mi ω₁.1.2.2
        | succ n => nomatch n)
  equiv_proc
  stmt_inline 0
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_call hcall
  stmt_wp
  equiv_skip
  rintro g g' rfl
  refine ⟨Or.inr ⟨?_, ?_⟩, ?_⟩
  · simp only [touched_set_of_le_compl hFm, touched_set_of_le_compl hFmi,
      touched_set_of_le_compl hFb, touched_set_of_le_compl hFc, touched_set_of_le_compl hFam,
      touched_set_of_le_compl hFami]
  · haveI := (inferInstance : Lens.Disjoint PRPi_m PRPi_mi).symm
    haveI := (inferInstance : Lens.Disjoint ARP_m ARP_mi).symm
    simp [Lens.get_of_disjoint_set, Lens.set_get]
  · rintro r₁ g₁ r₂ g₂ (⟨hc, hq⟩ | ⟨hr, -, ⟨hb, -, -⟩, hc⟩)
    · exact Or.inl ⟨hc, hq⟩
    · exact Or.inr ⟨hr, hb, hc⟩

/-- EC's `local lemma PRPi'_Indirect_eq &m`. -/
theorem PRPi'_Indirect_eq [Countable D] [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_m] [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi]
    (Dist : Distinguisher D) (hDd : FVP.fvP Dist ≤ (PRP_indirect_bad_bad.footprint)ᶜ)
    (m : VariableAssignment) :
    Procedure.Pr (Module.app (IND D) (Module.pair
        (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD)) Dist)).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (Module.app (IND D) (Module.pair
        (PRP_indirect_bad.asPRP D uD PRPi_m PRPi_mi PRP_indirect_bad_bad) Dist)).procedure () m
        (fun r _ => r = true) :=
  Procedure.Pr_eq_of_prhlProc
    (PRPi'_Indirect_eq_equiv D uD PRPi_m PRPi_mi PRP_indirect_bad_bad Dist hDd)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true) (fun r₁ _ r₂ _ h => by rw [h])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl

/-- EC's `pr_PRPi'_Indirect_ARP`, for a distinguisher whose globals are in a region `G` outside the
oracles' variables, lossless with oracles outside `G` (`G = glob D` is EC's statement; a region
lets `PartialConclusion` apply it to `DBounder(D)`, whose `glob` is not `D`'s). -/
theorem pr_PRPi'_Indirect_ARP_of_region [Countable D] [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_m] [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi]
    [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi] [Lens.Disjoint ARP_m ARP_mi]
    [Lens.Disjoint PRPi_m ARP_m] [Lens.Disjoint PRPi_m ARP_mi] [Lens.Disjoint PRPi_m ARP_coll]
    [Lens.Disjoint PRPi_mi ARP_m] [Lens.Disjoint PRPi_mi ARP_mi] [Lens.Disjoint PRPi_mi ARP_coll]
    [Lens.Disjoint PRP_indirect_bad_bad ARP_m] [Lens.Disjoint PRP_indirect_bad_bad ARP_mi]
    [Lens.Disjoint PRP_indirect_bad_bad ARP_coll]
    (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y})
    (Dist : Distinguisher D) (G : Footprint VariableAssignment) (hDG : FVP.fvP Dist ≤ G)
    (hG : G ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ PRP_indirect_bad_bad.footprint ⊔
      ARP_coll.footprint ⊔ ARP_m.footprint ⊔ ARP_mi.footprint)ᶜ)
    (D_ll : ∀ O : SPRP_Oracles D, FVP.fvP O ≤ Gᶜ →
      (SPRP_Oracles.f D O).procedure.IsLossless → (SPRP_Oracles.fi D O).procedure.IsLossless →
      (Module.app Dist O).procedure.IsLossless)
    (m : VariableAssignment) :
    |(Procedure.Pr (Module.app (IND D) (Module.pair
        (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD)) Dist)).procedure () m
        (fun r _ => r = true) : ℝ) -
      Procedure.Pr (Module.app (IND D) (Module.pair (ARP D uD ARP_coll ARP_m ARP_mi)
        Dist)).procedure () m (fun r _ => r = true)| ≤
      Procedure.Pr (Module.app (IND D) (Module.pair (ARP D uD ARP_coll ARP_m ARP_mi)
        Dist)).procedure () m (fun _ g => ARP_coll.get g = true) := by
  rw [PRPi'_Indirect_eq D uD PRPi_m PRPi_mi PRP_indirect_bad_bad Dist
    (hDG.trans (hG.trans (Footprint.compl_antimono
      (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))) m]
  refine Procedure.Pr_abs_sub_le_of_prhlProc_upto
    (pr_PRPi'_Indirect_ARP_equiv D uD PRPi_m PRPi_mi PRP_indirect_bad_bad ARP_coll ARP_m ARP_mi
      uD_uf_fu Dist G hDG hG D_ll)
    (bad₁ := fun _ g => PRP_indirect_bad_bad.get g = true) ?_ ?_ rfl
  · rintro r₁ g₁ r₂ g₂ (⟨_, hq⟩ | ⟨_, hb, hc⟩)
    · exact hq
    · exact ⟨fun h => absurd h hb, fun h => absurd h hc⟩
  · rintro r₁ g₁ r₂ g₂ (⟨hc, _⟩ | ⟨rfl, _, _⟩) hnc
    · exact absurd hc hnc
    · exact Iff.rfl

/-- EC's `lemma pr_PRPi'_Indirect_ARP &m`, for `declare module D <: Distinguisher {-PRPi, -ARP}`
with the axiom `D_ll` (the restriction stated against `glob D`, exception E7; the module
variables are lens parameters, disjoint, exception E8). -/
theorem pr_PRPi'_Indirect_ARP [Countable D] [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint PRP_indirect_bad_bad PRPi_m] [Lens.Disjoint PRP_indirect_bad_bad PRPi_mi]
    [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi] [Lens.Disjoint ARP_m ARP_mi]
    [Lens.Disjoint PRPi_m ARP_m] [Lens.Disjoint PRPi_m ARP_mi] [Lens.Disjoint PRPi_m ARP_coll]
    [Lens.Disjoint PRPi_mi ARP_m] [Lens.Disjoint PRPi_mi ARP_mi] [Lens.Disjoint PRPi_mi ARP_coll]
    [Lens.Disjoint PRP_indirect_bad_bad ARP_m] [Lens.Disjoint PRP_indirect_bad_bad ARP_mi]
    [Lens.Disjoint PRP_indirect_bad_bad ARP_coll]
    (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y})
    (Dist : Distinguisher D)
    (hDg : (FVP.fvP Dist).glob ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔
      PRP_indirect_bad_bad.footprint ⊔ ARP_coll.footprint ⊔ ARP_m.footprint ⊔ ARP_mi.footprint)ᶜ)
    (D_ll : ∀ O : SPRP_Oracles D, FVP.fvP O ≤ (FVP.fvP Dist).globᶜ →
      (SPRP_Oracles.f D O).procedure.IsLossless → (SPRP_Oracles.fi D O).procedure.IsLossless →
      (Module.app Dist O).procedure.IsLossless)
    (m : VariableAssignment) :
    |(Procedure.Pr (Module.app (IND D) (Module.pair
        (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD)) Dist)).procedure () m
        (fun r _ => r = true) : ℝ) -
      Procedure.Pr (Module.app (IND D) (Module.pair (ARP D uD ARP_coll ARP_m ARP_mi)
        Dist)).procedure () m (fun r _ => r = true)| ≤
      Procedure.Pr (Module.app (IND D) (Module.pair (ARP D uD ARP_coll ARP_m ARP_mi)
        Dist)).procedure () m (fun _ g => ARP_coll.get g = true) :=
  pr_PRPi'_Indirect_ARP_of_region D uD PRPi_m PRPi_mi PRP_indirect_bad_bad ARP_coll ARP_m ARP_mi
    uD_uf_fu Dist _ (Footprint.le_glob _) hDg D_ll m

end Upto

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

/-- `DBounder(D)` touches `D`'s variables and its counter. -/
theorem fvP_DBounder (Dist : Distinguisher D) :
    FVP.fvP (DBounder D q c Dist) ≤ FVP.fvP Dist ⊔ c.footprint := by
  fp_module c

/-- `DBounder.FBounder` touches its counter only. -/
@[fp_bound] theorem fvP_FBounder :
    FVP.fvP (DBounder.FBounder D q c) ≤ c.footprint := by
  fp_module c

/-- `DBounder.FBounder(O).f` is lossless if `O.f` is (EC: `proc; sp; if; wp; call O_f_ll`). -/
theorem FBounder_f_ll (O : SPRP_Oracles D) (hO : (SPRP_Oracles.f D O).procedure.IsLossless) :
    (SPRP_Oracles.f D (Module.app (DBounder.FBounder D q c) O)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hO ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 3
  phoare_simp [hO]
  phoare_wp 2
  phoare_skip
  simp

/-- `DBounder.FBounder(O).fi` is lossless if `O.fi` is. -/
theorem FBounder_fi_ll (O : SPRP_Oracles D) (hO : (SPRP_Oracles.fi D O).procedure.IsLossless) :
    (SPRP_Oracles.fi D (Module.app (DBounder.FBounder D q c) O)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hO ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 3
  phoare_simp [hO]
  phoare_wp 2
  phoare_skip
  simp

/-- `DBounder(D)` is lossless with `O` if `D` is with `DBounder.FBounder(O)` (EC's
`call (D_ll (<: DBounder(D,O).FBounder) _ _)` in `PartialConclusion`). -/
theorem DBounder_ll (Dist : Distinguisher D) (O : SPRP_Oracles D)
    (hll : (Module.app Dist (Module.app (DBounder.FBounder D q c) O)).procedure.IsLossless) :
    (Module.app (DBounder D q c Dist) O).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_wp 3
  phoare_skip
  intro σ _
  exact hll.ewp_const _ _ _

end DBounder

/-! ### The section `CollisionProbability`

With `declare module D <: Distinguisher {-ARP, -DBounder}`.

EC's local module `FEL(D)` (`DBounder` with EC's invariant built into its oracles) is not
ported: the potential below carries the invariant (see `IND_ARP_DBounder_potential`). -/

section CollisionProbability

variable (c : Lens ℤ VariableAssignment)
variable (ARP_coll : Lens Bool VariableAssignment)
  (ARP_m ARP_mi : Lens (FMap D D) VariableAssignment)

theorem expected_mono_le {γ : Type} {μ : SubProbability γ} {f g : γ → ENNReal}
    (h : ∀ a, f a ≤ g a) : μ.expected f ≤ μ.expected g := by
  rw [SubProbability.expected_eq_tsum, SubProbability.expected_eq_tsum]
  exact ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

theorem expected_const_le_self {γ : Type} (μ : SubProbability γ) (c : ENNReal) :
    μ.expected (fun _ => c) ≤ c := by
  letI : MeasurableSpace γ := ⊤
  change ∫⁻ _, c ∂μ.1 ≤ c
  rw [MeasureTheory.lintegral_const]
  calc c * μ.1 Set.univ ≤ c * 1 := by gcongr; exact μ.2.1
    _ = c := mul_one c

open Classical in
/-- A uniform draw lands in the range of `m` with probability at most `|dom m| · μ`. -/
theorem expected_rng_le {d : SubProbability D} (hfu : is_funiform d) (m : FMap D D) :
    d.expected (fun a => indicatorE (FMap.rng m a)) ≤ (FMap.fdom m).card * d.1 {default} := by
  rw [SubProbability.expected_eq_tsum]
  calc ∑' a, indicatorE (FMap.rng m a) * d.1 {a}
      = ∑' a, if a ∈ FMap.frng m then d.1 {a} else 0 := by
        refine tsum_congr fun a => ?_
        by_cases h : FMap.rng m a
        · simp [indicatorE, h, (FMap.mem_frng m a).mpr h]
        · have : a ∉ FMap.frng m := fun h' => h ((FMap.mem_frng m a).mp h')
          simp [indicatorE, h, this]
    _ = ∑ a ∈ FMap.frng m, d.1 {a} := by
        rw [tsum_eq_sum (s := FMap.frng m) (fun a ha => by simp [ha])]
        exact Finset.sum_congr rfl fun a ha => by simp [ha]
    _ = (FMap.frng m).card * d.1 {default} := by
        rw [Finset.sum_congr rfl fun a _ => hfu a default, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (FMap.fdom m).card * d.1 {default} := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast FMap.leq_card_rng_dom m) zero_le

open Classical in
/-- The potential of EC's `fel 2` in `pr_PRFi_collision`, on `(c, ARP.m, ARP.mi, ARP.coll)`: `1`
once
`ARP.coll`, the bound still to pay for the queries from `c` on while `|dom ARP.m|, |dom ARP.mi| ≤
c` (EC's invariant), `⊤` otherwise. -/
noncomputable def collPotential (q : ℤ) (μ : ENNReal) (s : ℤ × FMap D D × FMap D D × Bool) :
    ENNReal :=
  if s.2.2.2 = true then 1
  else if 0 ≤ s.1 ∧ ((FMap.fdom s.2.1).card : ℤ) ≤ s.1 ∧ ((FMap.fdom s.2.2.1).card : ℤ) ≤ s.1 then
    ∑ i ∈ Finset.Ico s.1.toNat q.toNat, (i : ENNReal) * μ
  else ⊤

omit [Inhabited D] in
theorem card_fdom_set_le (m : FMap D D) (x y : D) :
    ((FMap.fdom (FMap.set m x y)).card : ℤ) ≤ (FMap.fdom m).card + 1 := by
  rw [FMap.fdom_set]
  exact_mod_cast Finset.card_insert_le _ _

open Classical in
/-- **The step of EC's `fel 2`**, at a query `x` of `f` from the potential's state
`(c, m, mi, coll)`: the potential does not increase in expectation. -/
theorem collPotential_step {d : SubProbability D} (hfu : is_funiform d) (q b : ℤ)
    (m mi : FMap D D) (coll : Bool) (Q : Prop) [Decidable Q]
    (m' mi' : D → FMap D D) (hm' : ∀ a, ((FMap.fdom (m' a)).card : ℤ) ≤ (FMap.fdom m).card + 1)
    (hmi' : ∀ a, ((FMap.fdom (mi' a)).card : ℤ) ≤ (FMap.fdom mi).card + 1) (R : FMap D D)
    (hR : R = m ∨ R = mi) :
    (if b < q then
      (if Q then d.expected (fun a => collPotential D q (d.1 {default})
          (b + 1, m' a, mi' a, coll || decide (FMap.rng R a)))
        else collPotential D q (d.1 {default}) (b + 1, m, mi, coll))
      else collPotential D q (d.1 {default}) (b, m, mi, coll)) ≤
      collPotential D q (d.1 {default}) (b, m, mi, coll) := by
  set μ := d.1 {default}
  by_cases hb : b < q
  swap
  · simp [hb]
  rw [if_pos hb]
  by_cases hcol : coll = true
  · have h1 : ∀ m₀ mi₀ c₀, collPotential D q μ (c₀, m₀, mi₀, coll) = 1 := fun _ _ _ => by
      simp [collPotential, hcol]
    simp only [h1]
    split_ifs
    · refine (expected_mono_le fun a => ?_).trans (expected_const_le_self d 1)
      simp [collPotential, hcol]
    · exact le_rfl
  have hcol' : coll = false := by simpa using hcol
  by_cases hinv : 0 ≤ b ∧ ((FMap.fdom m).card : ℤ) ≤ b ∧ ((FMap.fdom mi).card : ℤ) ≤ b
  swap
  · simp [collPotential, hcol', hinv]
  set T := ∑ i ∈ Finset.Ico (b + 1).toNat q.toNat, (i : ENNReal) * μ
  have hφ : collPotential D q μ (b, m, mi, coll) = (b.toNat : ENNReal) * μ + T := by
    simp only [collPotential, hcol', hinv, and_self, if_true, Bool.false_eq_true, if_false]
    rw [Finset.sum_eq_sum_Ico_succ_bot (show b.toNat < q.toNat by omega),
      show b.toNat + 1 = (b + 1).toNat by omega]
  rw [hφ]
  split_ifs with hQ
  · calc d.expected
          (fun a => collPotential D q μ (b + 1, m' a, mi' a, coll || decide (FMap.rng R a)))
        ≤ d.expected (fun a => indicatorE (FMap.rng R a) + T) := by
          refine expected_mono_le fun a => ?_
          by_cases hr : FMap.rng R a
          · simp [collPotential, hcol', hr, indicatorE]
          · have hinv' : 0 ≤ b + 1 ∧ ((FMap.fdom (m' a)).card : ℤ) ≤ b + 1 ∧
                ((FMap.fdom (mi' a)).card : ℤ) ≤ b + 1 :=
              ⟨by omega, (hm' a).trans (by omega), (hmi' a).trans (by omega)⟩
            simp [collPotential, hcol', hr, hinv', T, indicatorE]
      _ = d.expected (fun a => indicatorE (FMap.rng R a)) + d.expected (fun _ => T) :=
          SubProbability.expected_add _ _ _
      _ ≤ (FMap.fdom R).card * μ + T :=
          add_le_add (expected_rng_le D hfu R) (expected_const_le_self d T)
      _ ≤ (b.toNat : ENNReal) * μ + T := by
          gcongr
          rcases hR with rfl | rfl <;> exact_mod_cast (show _ ≤ b.toNat by omega)
  · have hinv' : 0 ≤ b + 1 ∧ ((FMap.fdom m).card : ℤ) ≤ b + 1 ∧ ((FMap.fdom mi).card : ℤ) ≤ b + 1 :=
      ⟨by omega, by omega, by omega⟩
    simp only [collPotential, hcol', hinv', and_self, if_true, Bool.false_eq_true, if_false]
    exact le_add_self
/-- The oracle premise of EC's `fel 2` for `f`: a query of `DBounder(ARP).f` does not increase
the potential in expectation (`collPotential_step`, EC's `rnd (rng ARP.m)` and `mu_mem_le`). -/
theorem DBounder_ARP_f_potential [Lens.Disjoint c ARP_m] [Lens.Disjoint c ARP_mi]
    [Lens.Disjoint c ARP_coll] [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi]
    [Lens.Disjoint ARP_m ARP_mi] (hfu : is_funiform uD) :
    phoareProc (fun _ _ => True)
      (SPRP_Oracles.f D (Module.app (DBounder.FBounder D q c) (SPRP_Oracles.mk D
        { f := PRP.f D (ARP D uD ARP_coll ARP_m ARP_mi)
          fi := PRP.fi D (ARP D uD ARP_coll ARP_m ARP_mi) }))).procedure
      (fun _ g => collPotential D q (uD.1 {default})
        (c.get g, ARP_m.get g, ARP_mi.get g, ARP_coll.get g))
      (· ≤ ·)
      (fun _ g => collPotential D q (uD.1 {default})
        (c.get g, ARP_m.get g, ARP_mi.get g, ARP_coll.get g)) := by
  phoare_proc_to_stmt
  haveI := (inferInstance : Lens.Disjoint c ARP_m).symm
  haveI := (inferInstance : Lens.Disjoint c ARP_mi).symm
  haveI := (inferInstance : Lens.Disjoint c ARP_coll).symm
  haveI := (inferInstance : Lens.Disjoint ARP_coll ARP_m).symm
  haveI := (inferInstance : Lens.Disjoint ARP_coll ARP_mi).symm
  haveI := (inferInstance : Lens.Disjoint ARP_m ARP_mi).symm
  repeat phoare_inline 0
  phoare_ewp
  rename_i σ _
  exact collPotential_step D hfu q _ _ _ _ _
    (fun a => (ARP_m.get σ.globals).set ((localVarLens "x" D).get σ) a)
    (fun a => (ARP_mi.get σ.globals).set a ((localVarLens "x" D).get σ))
    (fun a => card_fdom_set_le D _ _ _) (fun a => card_fdom_set_le D _ _ _) _ (Or.inl rfl)
/-- The oracle premise for `fi`. -/
theorem DBounder_ARP_fi_potential [Lens.Disjoint c ARP_m] [Lens.Disjoint c ARP_mi]
    [Lens.Disjoint c ARP_coll] [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi]
    [Lens.Disjoint ARP_m ARP_mi] (hfu : is_funiform uD) :
    phoareProc (fun _ _ => True)
      (SPRP_Oracles.fi D (Module.app (DBounder.FBounder D q c) (SPRP_Oracles.mk D
        { f := PRP.f D (ARP D uD ARP_coll ARP_m ARP_mi)
          fi := PRP.fi D (ARP D uD ARP_coll ARP_m ARP_mi) }))).procedure
      (fun _ g => collPotential D q (uD.1 {default})
        (c.get g, ARP_m.get g, ARP_mi.get g, ARP_coll.get g))
      (· ≤ ·)
      (fun _ g => collPotential D q (uD.1 {default})
        (c.get g, ARP_m.get g, ARP_mi.get g, ARP_coll.get g)) := by
  phoare_proc_to_stmt
  haveI := (inferInstance : Lens.Disjoint c ARP_m).symm
  haveI := (inferInstance : Lens.Disjoint c ARP_mi).symm
  haveI := (inferInstance : Lens.Disjoint c ARP_coll).symm
  haveI := (inferInstance : Lens.Disjoint ARP_coll ARP_m).symm
  haveI := (inferInstance : Lens.Disjoint ARP_coll ARP_mi).symm
  haveI := (inferInstance : Lens.Disjoint ARP_m ARP_mi).symm
  repeat phoare_inline 0
  phoare_ewp
  rename_i σ _
  exact collPotential_step D hfu q _ _ _ _ _
    (fun a => (ARP_m.get σ.globals).set a ((localVarLens "x" D).get σ))
    (fun a => (ARP_mi.get σ.globals).set ((localVarLens "x" D).get σ) a)
    (fun a => card_fdom_set_le D _ _ _) (fun a => card_fdom_set_le D _ _ _) _ (Or.inr rfl)

/-- EC's `fel 2 FEL.c (fun x, x%r * mu uD (pred1 witness)) q ARP.coll …` in `pr_PRFi_collision`, as
a
supermartingale over the distinguisher (`Module.ewp_app_le`).  The potential is `⊤` off EC's
invariant `card (fdom ARP.m) <= c /\\ card (fdom ARP.mi) <= c`, so it applies to
`IND(ARP, DBounder(D))` directly: EC's two `have`s through `c <= q` and the local module `FEL`
(which restates `DBounder` with that invariant) are not needed. -/
theorem IND_ARP_DBounder_potential [Countable D] [Lens.Disjoint c ARP_m]
    [Lens.Disjoint c ARP_mi] [Lens.Disjoint c ARP_coll] [Lens.Disjoint ARP_coll ARP_m]
    [Lens.Disjoint ARP_coll ARP_mi] [Lens.Disjoint ARP_m ARP_mi] (hfu : is_funiform uD)
    (Dist : Distinguisher D)
    (hDd : FVP.fvP Dist ≤ (ARP_coll.footprint ⊔ ARP_m.footprint ⊔ ARP_mi.footprint ⊔
      c.footprint)ᶜ) :
    phoareProc (fun _ _ => True)
      (Module.app (IND D) (Module.pair (ARP D uD ARP_coll ARP_m ARP_mi)
        (DBounder D q c Dist))).procedure
      (fun _ g => indicatorE (ARP_coll.get g = true)) (· ≤ ·)
      (fun _ _ => ∑ i ∈ Finset.Ico (0 : ℤ).toNat q.toNat, (i : ENNReal) * uD.1 {default}) := by
  haveI := (inferInstance : Lens.Disjoint c ARP_m).symm
  haveI := (inferInstance : Lens.Disjoint c ARP_mi).symm
  haveI := (inferInstance : Lens.Disjoint c ARP_coll).symm
  haveI := (inferInstance : Lens.Disjoint ARP_coll ARP_m).symm
  haveI := (inferInstance : Lens.Disjoint ARP_coll ARP_mi).symm
  haveI := (inferInstance : Lens.Disjoint ARP_m ARP_mi).symm
  have hL : FVP.fvP Dist ≤
      ((Lens.pair c (Lens.pair ARP_m (Lens.pair ARP_mi ARP_coll))).footprint)ᶜ := by
    rw [Footprint.lens_pair, Footprint.lens_pair, Footprint.lens_pair]
    refine hDd.trans (Footprint.compl_antimono (le_of_eq ?_))
    ac_rfl
  phoare_proc_to_stmt
  phoare_inline 0
  repeat phoare_inline 0
  intro σ _
  simp only [Stmt.ewp_seq, Stmt.ewp_assign]
  simp_reads
  erw [Stmt.ewp_call]
  simp_reads
  refine le_trans (ProgramDenotation.wp_le_wp_of_le _ _ _ (fun r =>
    show indicatorE (ARP_coll.get r.2 = true) ≤ (fun s : ℤ × FMap D D × FMap D D × Bool =>
      collPotential D q (uD.1 {default}) s)
      ((Lens.pair c (Lens.pair ARP_m (Lens.pair ARP_mi ARP_coll))).get r.2) by
    by_cases h : ARP_coll.get r.2 = true
    · simp [indicatorE, h, collPotential, Lens.pair]
    · simp [indicatorE, h]) _) ?_
  refine le_trans (Module.ewp_app_le (Lens.pair c (Lens.pair ARP_m (Lens.pair ARP_mi ARP_coll)))
    Dist (SPRP_Oracles.ext D) (Distinguisher.representable D Dist) hL
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable D)
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable D)
        | succ n => nomatch n)
    _ (fun s => collPotential D q (uD.1 {default}) s)
    (fun n a g => by cases n with
      | zero =>
        simp only [SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_zero_cons]
        exact DBounder_ARP_f_potential D uD q c ARP_coll ARP_m ARP_mi hfu a g trivial
      | succ n => cases n with
        | zero =>
          simp only [SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single]
          exact DBounder_ARP_fi_potential D uD q c ARP_coll ARP_m ARP_mi hfu a g trivial
        | succ n => nomatch n) _ _) ?_
  simp only [Lens.pair, Lens.set_get, Lens.get_of_disjoint_set]
  have h0 : ((FMap.fdom (FMap.empty : FMap D D)).card : ℤ) ≤ 0 := by simp [FMap.fdom, FMap.empty]
  simp only [collPotential, Bool.false_eq_true, if_false, le_refl, h0, and_self, if_true]
  exact le_rfl

/-- EC's `lemma pr_PRFi_collision &m`, for `declare module D <: Distinguisher {-ARP, -DBounder}`
(EC's `D_ll` is not needed; `q` of either sign, EC's `ge0_q` not needed either). -/
theorem pr_PRFi_collision [Countable D] [Lens.Disjoint c ARP_m]
    [Lens.Disjoint c ARP_mi] [Lens.Disjoint c ARP_coll] [Lens.Disjoint ARP_coll ARP_m]
    [Lens.Disjoint ARP_coll ARP_mi] [Lens.Disjoint ARP_m ARP_mi] (hfu : is_funiform uD)
    (Dist : Distinguisher D)
    (hDd : FVP.fvP Dist ≤ (ARP_coll.footprint ⊔ ARP_m.footprint ⊔ ARP_mi.footprint ⊔
      c.footprint)ᶜ) (m : VariableAssignment) :
    (Procedure.Pr (Module.app (IND D) (Module.pair (ARP D uD ARP_coll ARP_m ARP_mi)
        (DBounder D q c Dist))).procedure () m (fun _ g => ARP_coll.get g = true) : ℝ) ≤
      ((q ^ 2 - q : ℤ) : ℝ) / 2 * (uD.1 {default}).toReal := by
  have hB := IND_ARP_DBounder_potential D uD q c ARP_coll ARP_m ARP_mi hfu Dist hDd () m trivial
  rw [← Procedure.Pr_eq_ewp] at hB
  set μ := uD.1 {default}
  have hμ : μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((MeasureTheory.measure_mono (Set.subset_univ _)).trans uD.2.1)
  have hR := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ =>
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top i) hμ) hB
  rw [ENNReal.coe_toReal, ENNReal.toReal_sum (fun i _ =>
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top i) hμ)] at hR
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, Int.toNat_zero] at hR
  refine hR.trans ?_
  rw [← Finset.range_eq_Ico, ← Finset.sum_mul]
  have hs : (∑ i ∈ Finset.range q.toNat, (i : ℝ)) = (q.toNat : ℝ) * (q.toNat - 1) / 2 := by
    rw [← Nat.cast_sum, Finset.sum_range_id]
    rcases hn : q.toNat with _ | n
    · simp
    · rw [Nat.cast_div (Nat.even_mul_pred_self (n + 1)).two_dvd (by norm_num)]
      push_cast
      ring
  rw [hs]
  rcases le_or_gt 0 q with hq | hq
  · rw [show ((q.toNat : ℕ) : ℝ) = (q : ℝ) by exact_mod_cast Int.toNat_of_nonneg hq]
    push_cast
    exact le_of_eq (by ring)
  · rw [show q.toNat = 0 by omega]
    have h0 : (0 : ℝ) ≤ ((q ^ 2 - q : ℤ) : ℝ) / 2 := by
      have : (0 : ℤ) ≤ q ^ 2 - q := by nlinarith
      positivity
    simpa using mul_nonneg h0 ENNReal.toReal_nonneg

end CollisionProbability

section
variable (PRPi_m PRPi_mi : Lens (FMap D D) VariableAssignment)
variable (ARP_coll : Lens Bool VariableAssignment)
  (ARP_m ARP_mi : Lens (FMap D D) VariableAssignment)
variable (FBounder_c : Lens ℤ VariableAssignment)

/-- `PartialConclusion` with `D`'s losslessness over a region `G` containing `D` and outside the
module variables (exception E14 of the SHA-3 port), `G` inside the `glob` of a finitely supported
`GF` (for the fresh choice of the section `Upto`'s local variable). -/
theorem PartialConclusion_of_region [Countable D] [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi] [Lens.Disjoint ARP_m ARP_mi]
    [Lens.Disjoint PRPi_m ARP_m] [Lens.Disjoint PRPi_m ARP_mi] [Lens.Disjoint PRPi_m ARP_coll]
    [Lens.Disjoint PRPi_mi ARP_m] [Lens.Disjoint PRPi_mi ARP_mi] [Lens.Disjoint PRPi_mi ARP_coll]
    [Lens.Disjoint FBounder_c PRPi_m] [Lens.Disjoint FBounder_c PRPi_mi]
    [Lens.Disjoint FBounder_c ARP_m] [Lens.Disjoint FBounder_c ARP_mi]
    [Lens.Disjoint FBounder_c ARP_coll]
    (hfs : (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ ARP_coll.footprint ⊔ ARP_m.footprint ⊔
      ARP_mi.footprint ⊔ FBounder_c.footprint).FinitelySupported)
    (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y})
    (Dist : Distinguisher D) (hD : Module.ECModule Dist (SPRP_Oracles.ext D))
    (G GF : Footprint VariableAssignment) (hGF : GF.FinitelySupported) (hGGF : G ≤ GF.glob)
    (hDG : FVP.fvP Dist ≤ G)
    (hG : G ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ ARP_coll.footprint ⊔
      ARP_m.footprint ⊔ ARP_mi.footprint ⊔ FBounder_c.footprint)ᶜ)
    (D_ll : ∀ O : SPRP_Oracles D, FVP.fvP O ≤ Gᶜ →
      (SPRP_Oracles.f D O).procedure.IsLossless → (SPRP_Oracles.fi D O).procedure.IsLossless →
      (Module.app Dist O).procedure.IsLossless)
    (m : VariableAssignment) :
    |(Procedure.Pr (Module.app (IND D) (Module.pair
        (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD))
        (DBounder D q FBounder_c Dist))).procedure () m (fun r _ => r = true) : ℝ) -
      Procedure.Pr (Module.app (IND D) (Module.pair (ARP D uD ARP_coll ARP_m ARP_mi)
        (DBounder D q FBounder_c Dist))).procedure () m (fun r _ => r = true)| ≤
      ((q ^ 2 - q : ℤ) : ℝ) / 2 * (uD.1 {default}).toReal := by
  -- the section `Upto`'s local variable `PRP_indirect_bad.bad`, fresh (exception E6)
  obtain ⟨B, hBg, hB, -⟩ := Footprint.exists_fresh_glob Bool hGF hfs
  have hB' : ∀ {X : Footprint VariableAssignment}, X ≤ GF ⊔ (PRPi_m.footprint ⊔
      PRPi_mi.footprint ⊔ ARP_coll.footprint ⊔ ARP_m.footprint ⊔ ARP_mi.footprint ⊔
      FBounder_c.footprint) → B.footprint ≤ Xᶜ :=
    fun h => hB.trans (Footprint.compl_antimono h)
  haveI : Lens.Disjoint B PRPi_m := Lens.disjoint_of_footprint_le_compl _ _ (hB'
    (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans
      (le_sup_left.trans le_sup_right))))))
  haveI : Lens.Disjoint B PRPi_mi := Lens.disjoint_of_footprint_le_compl _ _ (hB'
    (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans
      (le_sup_left.trans le_sup_right))))))
  haveI : Lens.Disjoint B ARP_coll := Lens.disjoint_of_footprint_le_compl _ _ (hB'
    (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_right)))))
  haveI : Lens.Disjoint B ARP_m := Lens.disjoint_of_footprint_le_compl _ _ (hB'
    (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_right))))
  haveI : Lens.Disjoint B ARP_mi := Lens.disjoint_of_footprint_le_compl _ _ (hB'
    (le_sup_right.trans (le_sup_left.trans le_sup_right)))
  haveI : Lens.Disjoint B FBounder_c := Lens.disjoint_of_footprint_le_compl _ _ (hB'
    (le_sup_right.trans le_sup_right))
  haveI := (inferInstance : Lens.Disjoint FBounder_c PRPi_m).symm
  haveI := (inferInstance : Lens.Disjoint FBounder_c PRPi_mi).symm
  haveI := (inferInstance : Lens.Disjoint FBounder_c ARP_m).symm
  haveI := (inferInstance : Lens.Disjoint FBounder_c ARP_mi).symm
  haveI := (inferInstance : Lens.Disjoint FBounder_c ARP_coll).symm
  have hBg' : G ≤ B.footprintᶜ :=
    (Footprint.le_compl_comm _ _).mp (hBg.trans (Footprint.compl_antimono hGGF))
  have hDd : FVP.fvP Dist ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ ARP_coll.footprint ⊔
      ARP_m.footprint ⊔ ARP_mi.footprint ⊔ FBounder_c.footprint)ᶜ := hDG.trans hG
  -- `pr_PRPi'_Indirect_ARP (DBounder(D))`, its `D_ll` from `D`'s (EC: `call (D_ll …)`)
  have hupto := pr_PRPi'_Indirect_ARP_of_region D uD PRPi_m PRPi_mi B ARP_coll ARP_m ARP_mi
    uD_uf_fu (DBounder D q FBounder_c Dist) (G ⊔ FBounder_c.footprint)
    ((fvP_DBounder D q FBounder_c Dist).trans (sup_le_sup_right hDG _))
    (by
      have h1 := (Footprint.le_compl_comm _ _).mp hG
      have h2 := (Footprint.le_compl_comm _ _).mp hBg'
      refine sup_le ((Footprint.le_compl_comm _ _).mpr ?_) (by fp_disjoint)
      simp only [sup_le_iff] at h1 ⊢
      exact ⟨⟨⟨⟨⟨h1.1.1.1.1.1, h1.1.1.1.1.2⟩, h2⟩, h1.1.1.1.2⟩, h1.1.1.2⟩, h1.1.2⟩)
    (fun O hO hf hfi => DBounder_ll D q FBounder_c Dist O (D_ll _ (by fp_disjoint)
      (FBounder_f_ll D q FBounder_c O hf) (FBounder_fi_ll D q FBounder_c O hfi))) m
  -- `pr_PRFi_collision D`
  have hcoll := pr_PRFi_collision D uD q FBounder_c ARP_coll ARP_m ARP_mi uD_uf_fu.2 Dist
    (by fp_disjoint) m
  exact hupto.trans hcoll

/-- EC's `lemma PartialConclusion (D <: Distinguisher {-PRPi, -ARP, -DBounder}) &m`.  The section
`Upto`'s local variable `PRP_indirect_bad.bad` is chosen fresh (exception E6), outside `glob D`
too; `pr_PRPi'_Indirect_ARP` is applied to `DBounder(D)` at the region `glob D ⊔ DBounder.c`. -/
theorem PartialConclusion [Countable D] [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi] [Lens.Disjoint ARP_m ARP_mi]
    [Lens.Disjoint PRPi_m ARP_m] [Lens.Disjoint PRPi_m ARP_mi] [Lens.Disjoint PRPi_m ARP_coll]
    [Lens.Disjoint PRPi_mi ARP_m] [Lens.Disjoint PRPi_mi ARP_mi] [Lens.Disjoint PRPi_mi ARP_coll]
    [Lens.Disjoint FBounder_c PRPi_m] [Lens.Disjoint FBounder_c PRPi_mi]
    [Lens.Disjoint FBounder_c ARP_m] [Lens.Disjoint FBounder_c ARP_mi]
    [Lens.Disjoint FBounder_c ARP_coll]
    (hfs : (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ ARP_coll.footprint ⊔ ARP_m.footprint ⊔
      ARP_mi.footprint ⊔ FBounder_c.footprint).FinitelySupported)
    (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y})
    (Dist : Distinguisher D) (hD : Module.ECModule Dist (SPRP_Oracles.ext D))
    (hDg : (FVP.fvP Dist).glob ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ ARP_coll.footprint ⊔
      ARP_m.footprint ⊔ ARP_mi.footprint ⊔ FBounder_c.footprint)ᶜ)
    (D_ll : ∀ O : SPRP_Oracles D, FVP.fvP O ≤ (FVP.fvP Dist).globᶜ →
      (SPRP_Oracles.f D O).procedure.IsLossless → (SPRP_Oracles.fi D O).procedure.IsLossless →
      (Module.app Dist O).procedure.IsLossless)
    (m : VariableAssignment) :
    |(Procedure.Pr (Module.app (IND D) (Module.pair
        (Module.app (PRPi' D uD PRPi_m PRPi_mi) (Indirect D uD))
        (DBounder D q FBounder_c Dist))).procedure () m (fun r _ => r = true) : ℝ) -
      Procedure.Pr (Module.app (IND D) (Module.pair (ARP D uD ARP_coll ARP_m ARP_mi)
        (DBounder D q FBounder_c Dist))).procedure () m (fun r _ => r = true)| ≤
      ((q ^ 2 - q : ℤ) : ℝ) / 2 * (uD.1 {default}).toReal :=
  PartialConclusion_of_region D uD q PRPi_m PRPi_mi ARP_coll ARP_m ARP_mi FBounder_c hfs uD_uf_fu
    Dist hD _ _ hD.finitelySupported le_rfl (Footprint.le_glob _) hDg D_ll m
end

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

/-- `Conclusion` with `D`'s losslessness over a region `G` containing `D` and outside the module
variables (exception E14 of the SHA-3 port), `G` inside the `glob` of a finitely supported `GF`. -/
theorem Conclusion_of_region [Countable D]
    (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y})
    (PRPi_m PRPi_mi ARP_m ARP_mi : Lens (FMap D D) VariableAssignment)
    (ARP_coll : Lens Bool VariableAssignment) (FBounder_c : Lens ℤ VariableAssignment)
    [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi] [Lens.Disjoint ARP_m ARP_mi]
    [Lens.Disjoint PRPi_m ARP_m] [Lens.Disjoint PRPi_m ARP_mi] [Lens.Disjoint PRPi_m ARP_coll]
    [Lens.Disjoint PRPi_mi ARP_m] [Lens.Disjoint PRPi_mi ARP_mi] [Lens.Disjoint PRPi_mi ARP_coll]
    [Lens.Disjoint FBounder_c PRPi_m] [Lens.Disjoint FBounder_c PRPi_mi]
    [Lens.Disjoint FBounder_c ARP_m] [Lens.Disjoint FBounder_c ARP_mi]
    [Lens.Disjoint FBounder_c ARP_coll]
    (hfs : (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ ARP_coll.footprint ⊔ ARP_m.footprint ⊔
      ARP_mi.footprint ⊔ FBounder_c.footprint).FinitelySupported)
    (Dist : Distinguisher D) (hD : (FVP.fvP Dist).FinitelySupported)
    (G GF : Footprint VariableAssignment) (hGF : GF.FinitelySupported) (hGGF : G ≤ GF.glob)
    (hDG : FVP.fvP Dist ≤ G)
    (hG : G ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ ARP_coll.footprint ⊔
      ARP_m.footprint ⊔ ARP_mi.footprint ⊔ FBounder_c.footprint)ᶜ)
    (m : VariableAssignment) :
    (∀ O : SPRP_Oracles D, FVP.fvP O ≤ Gᶜ →
      (SPRP_Oracles.f D O).procedure.IsLossless → (SPRP_Oracles.fi D O).procedure.IsLossless →
      (Module.app Dist O).procedure.IsLossless) →
    |(Procedure.Pr (Module.app (IND D) (Module.pair (PRPi.PRPi D uD PRPi_m PRPi_mi)
        (DBounder D q FBounder_c Dist))).procedure () m (fun r _ => r = true) : ℝ) -
      (Procedure.Pr (Module.app (IND D) (Module.pair (ARP D uD ARP_coll ARP_m ARP_mi)
        (DBounder D q FBounder_c Dist))).procedure () m (fun r _ => r = true) : ℝ)| ≤
      ((q ^ 2 - q : ℤ) : ℝ) / 2 * (uD.1 {default}).toReal := by
  intro D_ll
  have hDd : FVP.fvP Dist ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ ARP_coll.footprint ⊔
      ARP_m.footprint ⊔ ARP_mi.footprint ⊔ FBounder_c.footprint)ᶜ :=
    hDG.trans hG
  haveI := (inferInstance : Lens.Disjoint FBounder_c PRPi_m).symm
  haveI := (inferInstance : Lens.Disjoint FBounder_c PRPi_mi).symm
  rw [pr_PRPi_PRPi'_Indirect D uD PRPi_m PRPi_mi uD_uf_fu.1 (DBounder D q FBounder_c Dist)
    ((fvP_DBounder D q FBounder_c Dist).trans (by fp_disjoint)) m]
  exact PartialConclusion_of_region D uD q PRPi_m PRPi_mi ARP_coll ARP_m ARP_mi FBounder_c hfs
    uD_uf_fu Dist (Distinguisher.ecModule D Dist hD) G GF hGF hGGF hDG hG D_ll m

/-- EC's `Conclusion`, for `D <: Distinguisher {-PRPi, -ARP, -DBounder}`, under the theory's
axiom `uD_uf_fu` (`uD` uniform, lossless and full).  `mu uD (pred1 witness)` is the probability of
`default`.  The restriction is stated against `glob D` (exception E7); the module variables are lens
parameters, disjoint and finitely supported (exceptions E6, E8; a clone with `global_var`s
discharges these); `D`'s representation is a theorem (`Distinguisher.ecModule`). -/
theorem Conclusion [Countable D] (uD_uf_fu : uD.1 Set.univ = 1 ∧ ∀ x y, uD.1 {x} = uD.1 {y})
    (PRPi_m PRPi_mi ARP_m ARP_mi : Lens (FMap D D) VariableAssignment)
    (ARP_coll : Lens Bool VariableAssignment) (FBounder_c : Lens ℤ VariableAssignment)
    [Lens.Disjoint PRPi_m PRPi_mi]
    [Lens.Disjoint ARP_coll ARP_m] [Lens.Disjoint ARP_coll ARP_mi] [Lens.Disjoint ARP_m ARP_mi]
    [Lens.Disjoint PRPi_m ARP_m] [Lens.Disjoint PRPi_m ARP_mi] [Lens.Disjoint PRPi_m ARP_coll]
    [Lens.Disjoint PRPi_mi ARP_m] [Lens.Disjoint PRPi_mi ARP_mi] [Lens.Disjoint PRPi_mi ARP_coll]
    [Lens.Disjoint FBounder_c PRPi_m] [Lens.Disjoint FBounder_c PRPi_mi]
    [Lens.Disjoint FBounder_c ARP_m] [Lens.Disjoint FBounder_c ARP_mi]
    [Lens.Disjoint FBounder_c ARP_coll]
    (hfs : (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ ARP_coll.footprint ⊔ ARP_m.footprint ⊔
      ARP_mi.footprint ⊔ FBounder_c.footprint).FinitelySupported)
    (Dist : Distinguisher D) (hD : (FVP.fvP Dist).FinitelySupported)
    (_hD : (FVP.fvP Dist).glob ≤ (PRPi_m.footprint ⊔ PRPi_mi.footprint ⊔ ARP_coll.footprint ⊔
      ARP_m.footprint ⊔ ARP_mi.footprint ⊔ FBounder_c.footprint)ᶜ)
    (m : VariableAssignment) :
    (∀ O : SPRP_Oracles D, FVP.fvP O ≤ (FVP.fvP Dist).globᶜ →
      (SPRP_Oracles.f D O).procedure.IsLossless → (SPRP_Oracles.fi D O).procedure.IsLossless →
      (Module.app Dist O).procedure.IsLossless) →
    |(Procedure.Pr (Module.app (IND D) (Module.pair (PRPi.PRPi D uD PRPi_m PRPi_mi)
        (DBounder D q FBounder_c Dist))).procedure () m (fun r _ => r = true) : ℝ) -
      (Procedure.Pr (Module.app (IND D) (Module.pair (ARP D uD ARP_coll ARP_m ARP_mi)
        (DBounder D q FBounder_c Dist))).procedure () m (fun r _ => r = true) : ℝ)| ≤
      ((q ^ 2 - q : ℤ) : ℝ) / 2 * (uD.1 {default}).toReal :=
  Conclusion_of_region D uD q uD_uf_fu PRPi_m PRPi_mi ARP_m ARP_mi ARP_coll FBounder_c hfs Dist hD
    _ _ hD le_rfl (Footprint.le_glob _) _hD m

end GaudisCrypt.EC.Strong_RP_RF
