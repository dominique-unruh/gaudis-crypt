import GaudisCrypt.Examples.SHA3.SmartCounter.SLCommon
import GaudisCrypt.Lib.EC.Strong_RP_RF
import GaudisCrypt.Logic.FrameTactics
import GaudisCrypt.Logic.EqualOutside

/-!
# From the permutation to a random function (EasyCrypt `proof/smart_counter/ConcreteF.eca`)

The real game with the ideal permutation is close to the same game with `PF`, a random function
with an inverse, up to the PRP/PRF switching bound (`Real_Concrete`).

Translation notes (see `notes/SHA3/README.md`):
* The section's `declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo}` and `declare axiom
  D_ll` are hypotheses of the lemmas.  So are the local modules' parameters.
* `local clone import Strong_RP_RF as Switching with type D <- state, op uD <- dstate,
  type K <- unit, op dK <- dunit tt, op q <- max_size` is the namespace `Switching`, and its
  realized axioms `ge0_q`, `uD_uf_fu` are lemmas.  The clone is local, so its module variables are
  lens parameters of the local declarations that mention them (exception E6).
* EasyCrypt checks this file only up to an anomaly at line 418 (inside the proof of
  `Real_Concrete`); see `notes/SHA3/README.md`.
-/

namespace GaudisCrypt.SHA3.ConcreteF

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.SLCommon
open GaudisCrypt.SHA3.SLCommon.Prefix

-- `state` also names the RO library's globals (`Lib/RO/Basic.lean`, at the root), and
-- `PRIMITIVE` also `Common`'s (the `PRP` clone); here they are `SLCommon`'s, which EasyCrypt's
-- `clone include Indifferentiability` puts in scope last
export GaudisCrypt.SHA3.SLCommon (state PRIMITIVE)

variable [SLCommon.Params]

/-- EC's `PF.m`. -/
global_var PF.m : FMap state state
/-- EC's `PF.mi`. -/
global_var PF.mi : FMap state state

module PF : PRIMITIVE {
  proc init () : Unit {
    PF.m <- (FMap.empty : FMap state state);
    PF.mi <- (FMap.empty : FMap state state);
    return ()
  };
  proc f (x : state) : state {
    var y1 : block, y2 : capacity;
    if (!(decide (FMap.dom ($PF.m : FMap state state) $x))) {
      y1 <$ bdistr;
      y2 <$ cdistr;
      PF.m <- FMap.set $PF.m $x ($y1, $y2);
      PF.mi <- FMap.set $PF.mi ($y1, $y2) $x;
    }
    return oget (FMap.get ($PF.m : FMap state state) $x)
  };
  proc fi (x : state) : state {
    var y1 : block, y2 : capacity;
    if (!(decide (FMap.dom ($PF.mi : FMap state state) $x))) {
      y1 <$ bdistr;
      y2 <$ cdistr;
      PF.mi <- FMap.set $PF.mi $x ($y1, $y2);
      PF.m <- FMap.set $PF.m ($y1, $y2) $x;
    }
    return oget (FMap.get ($PF.mi : FMap state state) $x)
  };
}

/-- `module CF(D : DISTINGUISHER) = Indif(SqueezelessSponge(PF), PF, D)`. -/
noncomputable def CF (D : DISTINGUISHER) : procmod () → Bool :=
  Module.app Indif (Module.pair
    (Module.app SqueezelessSponge (Indifferentiability.PRIMITIVE.view state (List block) block PF))
    (Module.pair PF D))

/-! ## The section -/

section

variable (D : DISTINGUISHER)

/-- `local module GReal' = Indif(FC(SqueezelessSponge(Perm)), PC(Perm), D)`. -/
noncomputable def GReal' : procmod () → Bool :=
  Module.app Indif (Module.pair
    (Module.app FC (Module.app SqueezelessSponge
      (Indifferentiability.PRIMITIVE.view state (List block) block Perm)))
    (Module.pair (Module.app PC Perm) D))

/-! `local clone import Strong_RP_RF as Switching with type D <- state, op uD <- dstate,
type K <- unit, op dK <- (MUnit.dunit<:unit> tt), op q <- max_size` -/

namespace Switching
/-! The clone is local: its module variables (`PRPi.m`, `PRPi.mi`, `ARP.coll`, `ARP.m`, `ARP.mi`,
`DBounder.FBounder.c`) are lens parameters of the local declarations that mention them, fresh by
hypothesis (exception E6). -/
-- one binder each: a declaration takes only the variables it mentions
variable (PRPi_m : Lens (FMap state state) VariableAssignment)
variable (PRPi_mi : Lens (FMap state state) VariableAssignment)
variable (ARP_coll : Lens Bool VariableAssignment)
variable (ARP_m : Lens (FMap state state) VariableAssignment)
variable (ARP_mi : Lens (FMap state state) VariableAssignment)
variable (DBounder_FBounder_c : Lens ℤ VariableAssignment)
noncomputable abbrev PRPi.PRPi := Strong_RP_RF.PRPi.PRPi state dstate PRPi_m PRPi_mi
noncomputable abbrev ARP := Strong_RP_RF.ARP state dstate ARP_coll ARP_m ARP_mi
noncomputable abbrev DBounder := Strong_RP_RF.DBounder state max_size DBounder_FBounder_c
abbrev PRPSec.PRP := EC.PRP.StrongPRP.PRP state
abbrev PRPSec.SPRP_Oracles := EC.PRP.StrongPRP.SPRP_Oracles state
abbrev PRPSec.Distinguisher := EC.PRP.StrongPRP.Distinguisher state
noncomputable abbrev PRPSec.IND := EC.PRP.StrongPRP.IND state

/-- `realize ge0_q`. -/
theorem ge0_q : 0 ≤ (max_size : ℤ) := max_ge0

/-- `realize uD_uf_fu`: `dstate` is uniform, lossless and full. -/
theorem uD_uf_fu : dstate.1 Set.univ = 1 ∧ ∀ x y, dstate.1 {x} = dstate.1 {y} := by
  refine ⟨dprod_ll BitWord.dunifin_ll BitWord.dunifin_ll, ?_⟩
  rintro ⟨x1, x2⟩ ⟨y1, y2⟩
  rw [dstate, dprod1E, dprod1E, bdistr, cdistr, Block.DBlock.dunifin, Capacity.DCapacity.dunifin,
    BitWord.dunifin_funi x1 y1, BitWord.dunifin_funi x2 y2]
end Switching

/-! ## `DoubleBounding`'s invariant and oracle steps -/

/-- `PRPSec.SPRP_Oracles` and `DPRIMITIVE` are the same module type: the same `f`. -/
theorem DPRIMITIVE_f_eq (X : Switching.PRPSec.SPRP_Oracles) :
    Indifferentiability.DPRIMITIVE.f state (List block) block X =
      PRP.StrongPRP.SPRP_Oracles.f state X := rfl

/-- `PRPSec.SPRP_Oracles` and `DPRIMITIVE` are the same module type: the same `fi`. -/
theorem DPRIMITIVE_fi_eq (X : Switching.PRPSec.SPRP_Oracles) :
    Indifferentiability.DPRIMITIVE.fi state (List block) block X =
      PRP.StrongPRP.SPRP_Oracles.fi state X := rfl

/-- The view of a PRP as `DPRIMITIVE`: its `f`. -/
theorem dprim_f_mk (P : Switching.PRPSec.PRP) :
    Indifferentiability.DPRIMITIVE.f state (List block) block
      (PRP.StrongPRP.SPRP_Oracles.mk state
        { f := PRP.StrongPRP.PRP.f state P, fi := PRP.StrongPRP.PRP.fi state P }) =
      PRP.StrongPRP.PRP.f state P := by
  rw [DPRIMITIVE_f_eq]; simp

/-- The view of a PRP as `DPRIMITIVE`: its `fi`. -/
theorem dprim_fi_mk (P : Switching.PRPSec.PRP) :
    Indifferentiability.DPRIMITIVE.fi state (List block) block
      (PRP.StrongPRP.SPRP_Oracles.mk state
        { f := PRP.StrongPRP.PRP.f state P, fi := PRP.StrongPRP.PRP.fi state P }) =
      PRP.StrongPRP.PRP.fi state P := by
  rw [DPRIMITIVE_fi_eq]; simp

/-- `FBounder(O)` as `DPRIMITIVE`: its `f`. -/
theorem dprim_f_FB (c : Lens ℤ VariableAssignment) (X : Switching.PRPSec.SPRP_Oracles) :
    Indifferentiability.DPRIMITIVE.f state (List block) block
      (Module.app (Strong_RP_RF.DBounder.FBounder state max_size c) X) =
      PRP.StrongPRP.SPRP_Oracles.f state
        (Module.app (Strong_RP_RF.DBounder.FBounder state max_size c) X) := rfl

/-- `FBounder(O)` as `DPRIMITIVE`: its `fi`. -/
theorem dprim_fi_FB (c : Lens ℤ VariableAssignment) (X : Switching.PRPSec.SPRP_Oracles) :
    Indifferentiability.DPRIMITIVE.fi state (List block) block
      (Module.app (Strong_RP_RF.DBounder.FBounder state max_size c) X) =
      PRP.StrongPRP.SPRP_Oracles.fi state
        (Module.app (Strong_RP_RF.DBounder.FBounder state max_size c) X) := rfl

/-- The prefix facts of `DoubleBounding`'s invariant: `Redo.prefixes` is closed under prefixes,
knows `[]`, and every query. -/
def dbPre (Q : FMap (List block) block) (pref : FMap (List block) state) : Prop :=
  all_prefixes pref ∧ FMap.dom pref [] ∧ ∀ x, FMap.dom Q x → FMap.dom pref x

/-- `DoubleBounding`'s invariant on `(DBounder.FBounder.c, C.c, C.queries, Redo.prefixes)`: equal
`C`, `Redo` on both sides, the right's counter below `C.c`, and the prefix facts. -/
def dbI (x y : ℤ × ℤ × FMap (List block) block × FMap (List block) state) : Prop :=
  x.2 = y.2 ∧ y.1 ≤ y.2.1 ∧ dbPre y.2.2.1 y.2.2.2

/-- The longest prefix of `p` among the queries `Q` (EC's `prefix p (get_max_prefix p (elems
(fdom Q)))`).  An abbreviation, not an EC declaration. -/
noncomputable abbrev dbq (p : List block) (Q : FMap (List block) block) : ℤ :=
  «prefix» p (get_max_prefix p (FSet.elems (FMap.fdom Q)))

/-- Under `dbPre`, the prefixes of `p` up to its longest queried prefix are known. -/
theorem dbPre_take (Q : FMap (List block) block) (pref : FMap (List block) state)
    (p : List block) (h : dbPre Q pref) (j : ℤ) (hj0 : 0 ≤ j) (hj : j ≤ dbq p Q) :
    FMap.dom pref (take j p) := by
  obtain ⟨hall, h0, hQ⟩ := h
  by_cases hq : 0 < dbq p Q
  · have hmem : FMap.dom Q (get_max_prefix p (FSet.elems (FMap.fdom Q))) :=
      (mem_elems_fdom _ _).1 (prefix_gt0_mem _ _ hq)
    rw [prefix_take_leq p _ j hj]
    exact hall _ (hQ _ hmem) j
  · have : j = 0 := by omega
    subst this
    simpa [take] using h0

/-- Adding the next prefix `take (i + 1) p` keeps `dbPre`, when the prefixes up to `i` are known. -/
theorem dbPre_step (Q : FMap (List block) block) (pref : FMap (List block) state)
    (p : List block) (i : ℤ) (w : state) (h : dbPre Q pref)
    (hall : ∀ j, 0 ≤ j → j ≤ i → FMap.dom pref (take j p)) (hi : 0 ≤ i) :
    dbPre Q (FMap.set pref (take (i + 1) p) w) := by
  obtain ⟨hpre, h0, hQ⟩ := h
  have grow : ∀ l, FMap.dom pref l → FMap.dom (FMap.set pref (take (i + 1) p) w) l :=
    fun l hl => (FMap.mem_set _ _ _ _).2 (Or.inl hl)
  refine ⟨?_, grow _ h0, fun x hx => grow _ (hQ x hx)⟩
  intro l hl k
  rcases (FMap.mem_set _ _ _ _).1 hl with hl | rfl
  · exact grow _ (hpre l hl k)
  · by_cases hk : k ≤ i
    · rw [take_take, min_eq_left (by omega)]
      by_cases hk0 : 0 ≤ k
      · exact grow _ (hall k hk0 hk)
      · have : take k p = take 0 p := by simp [take]; omega
        rw [this]
        exact grow _ (hall 0 le_rfl hi)
    · rw [take_take, min_eq_right (by omega)]
      exact (FMap.mem_set _ _ _ _).2 (Or.inr rfl)

/-- Answering a query whose prefix is known keeps `dbPre`. -/
theorem dbPre_query (Q : FMap (List block) block) (pref : FMap (List block) state)
    (bs : List block) (w : block) (h : dbPre Q pref) (hb : FMap.dom pref bs) :
    dbPre (FMap.set Q bs w) pref := by
  obtain ⟨hpre, h0, hQ⟩ := h
  refine ⟨hpre, h0, fun x hx => ?_⟩
  rcases (FMap.mem_set _ _ _ _).1 hx with hx | rfl
  · exact hQ x hx
  · exact hb

section DB
variable (c : Lens ℤ VariableAssignment) [Lens.Disjoint c C.c] [Lens.Disjoint c C.queries]
  [Lens.Disjoint c Redo.prefixes]

/-- The lens of `DoubleBounding`'s invariant. -/
noncomputable abbrev dbL : Lens (ℤ × ℤ × FMap (List block) block × FMap (List block) state)
    VariableAssignment :=
  Lens.pair c (Lens.pair C.c (Lens.pair C.queries Redo.prefixes))

/-- A write of the counter on the right keeps the states equal outside `dbL`. -/
theorem dbL_c_right {g₁ g₂ : VariableAssignment} (h : (dbL c).equal_outside g₁ g₂) (v : ℤ) :
    (dbL c).equal_outside g₁ (c.set v g₂) := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨(v, x.2), by simp only [dbL, Lens.pair, c.set_set]⟩

/-- A write of `C.c` on the right keeps the states equal outside `dbL`. -/
theorem dbL_Cc_right {g₁ g₂ : VariableAssignment} (h : (dbL c).equal_outside g₁ g₂) (v : ℤ) :
    (dbL c).equal_outside g₁ (C.c.set v g₂) := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨(x.1, v, x.2.2), ?_⟩
  simp only [dbL, Lens.pair]
  rw [← (inferInstance : Lens.Disjoint c C.c).commute, C.c.set_set]

/-- A write of `C.c` on the left keeps the states equal outside `dbL`. -/
theorem dbL_Cc_left {g₁ g₂ : VariableAssignment} (h : (dbL c).equal_outside g₁ g₂) (v : ℤ) :
    (dbL c).equal_outside (C.c.set v g₁) g₂ := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨x, ?_⟩
  simp only [dbL, Lens.pair]
  rw [(inferInstance : Lens.Disjoint Redo.prefixes C.c).commute,
    (inferInstance : Lens.Disjoint C.queries C.c).commute, C.c.set_set]

/-- A write of `C.queries` on the right keeps the states equal outside `dbL`. -/
theorem dbL_Cq_right {g₁ g₂ : VariableAssignment} (h : (dbL c).equal_outside g₁ g₂)
    (v : FMap (List block) block) : (dbL c).equal_outside g₁ (C.queries.set v g₂) := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨(x.1, x.2.1, v, x.2.2.2), ?_⟩
  simp only [dbL, Lens.pair]
  rw [← (inferInstance : Lens.Disjoint c C.queries).commute,
    ← (inferInstance : Lens.Disjoint C.c C.queries).commute, C.queries.set_set]

/-- A write of `C.queries` on the left keeps the states equal outside `dbL`. -/
theorem dbL_Cq_left {g₁ g₂ : VariableAssignment} (h : (dbL c).equal_outside g₁ g₂)
    (v : FMap (List block) block) : (dbL c).equal_outside (C.queries.set v g₁) g₂ := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨x, ?_⟩
  simp only [dbL, Lens.pair]
  rw [(inferInstance : Lens.Disjoint Redo.prefixes C.queries).commute, C.queries.set_set]

/-- A write of `Redo.prefixes` on the right keeps the states equal outside `dbL`. -/
theorem dbL_R_right {g₁ g₂ : VariableAssignment} (h : (dbL c).equal_outside g₁ g₂)
    (v : FMap (List block) state) : (dbL c).equal_outside g₁ (Redo.prefixes.set v g₂) := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨(x.1, x.2.1, x.2.2.1, v), ?_⟩
  simp only [dbL, Lens.pair]
  rw [← (inferInstance : Lens.Disjoint c Redo.prefixes).commute,
    ← (inferInstance : Lens.Disjoint C.c Redo.prefixes).commute,
    ← (inferInstance : Lens.Disjoint C.queries Redo.prefixes).commute, Redo.prefixes.set_set]

/-- A write of `Redo.prefixes` on the left keeps the states equal outside `dbL`. -/
theorem dbL_R_left {g₁ g₂ : VariableAssignment} (h : (dbL c).equal_outside g₁ g₂)
    (v : FMap (List block) state) : (dbL c).equal_outside (Redo.prefixes.set v g₁) g₂ := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨x, by simp only [dbL, Lens.pair, Redo.prefixes.set_set]⟩

variable (P : Switching.PRPSec.PRP)

theorem DB_P_f (hP : FVP.fvP P ≤ ((dbL c).footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ (dbL c).equal_outside g₁ g₂ ∧
        dbI ((dbL c).get g₁) ((dbL c).get g₂))
      (Indifferentiability.DPRIMITIVE.f state (List block) block (Module.app DPRestr
        (PRP.StrongPRP.SPRP_Oracles.mk state
          { f := PRP.StrongPRP.PRP.f state P, fi := PRP.StrongPRP.PRP.fi state P }))).procedure
      (Indifferentiability.DPRIMITIVE.f state (List block) block (Module.app DPRestr
        (Module.app (Strong_RP_RF.DBounder.FBounder state max_size c)
          (PRP.StrongPRP.SPRP_Oracles.mk state
            { f := PRP.StrongPRP.PRP.f state P, fi := PRP.StrongPRP.PRP.fi state P })))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ (dbL c).equal_outside g₁ g₂ ∧
        dbI ((dbL c).get g₁) ((dbL c).get g₂)) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  rw [dprim_f_mk, dprim_f_FB]
  repeat stmt_inline{2} 0
  simp only [PRP.StrongPRP.SPRP_Oracles.f.mk_simp]
  have hPf : FVP.fvP (PRP.StrongPRP.PRP.f state P) ≤ ((dbL c).footprint)ᶜ := by fp_disjoint
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧
      §(localVarLens "y" state){1} = §(localVarLens "y" state){2} ∧
      (dbL c).equal_outside §allGlobals{1} §allGlobals{2} ∧
      dbI ((dbL c).get §allGlobals{1}) ((dbL c).get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  · equiv_if
    case guard =>
      rintro g₁ g₂ x0 y x0' y' ⟨-, -, -, hI1, -, -⟩
      rw [show C.c.get g₁ = C.c.get g₂ from congrArg Prod.fst hI1]
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§x0{1} = §x1{2} ∧
          (dbL c).equal_outside §allGlobals{1} §allGlobals{2} ∧
          dbI ((dbL c).get §allGlobals{1}) ((dbL c).get §allGlobals{2}) ∧ §C.c{1} + 1 ≤ max_size)
      · stmt_wp
        equiv_skip
        rintro g₁ g₂ x0 y x0' y' ⟨⟨rfl, -, he, hI⟩, hg⟩
        simp only [decide_eq_true_eq] at hg
        exact ⟨rfl, he, hI, hg⟩
      · equiv_if{2}
        case «then» =>
          stmt_wp{2} 1
          equiv_call (prhlProc_self_equal_outside_module (dbL c) (PRP.StrongPRP.PRP.f state P)
            hPf dbI)
          equiv_skip
          rintro g₁ g₂ x0 x1 ⟨⟨hx, he, hI, hlt⟩, -⟩
          refine ⟨⟨hx, he, hI⟩, ?_⟩
          rintro r g₁' r' g₂' ⟨rfl, he', ⟨h1, h2, h3⟩⟩
          refine ⟨rfl, dbL_Cc_left c (dbL_Cc_right c (dbL_c_right c he' _) _) _, ?_⟩
          simp only [Prod.mk.injEq] at h1
          dsimp only at h2
          haveI := (inferInstance : Lens.Disjoint c C.c).symm
          simp only [dbI, Lens.get_of_disjoint_set, Lens.set_get]
          exact ⟨by rw [h1.1, h1.2.1, h1.2.2], by omega, h3⟩
        case «else» =>
          refine prhlStmt_pre prhlStmt_false ?_
          rintro σ₁ σ₂ ⟨⟨-, -, ⟨hI1, hc, -⟩, hlt⟩, hg⟩
          simp only [Prod.mk.injEq] at hI1
          simp only [decide_eq_false_iff_not, not_lt] at hg
          dsimp only at hc
          have := hI1.1
          omega
    case «else» =>
      equiv_skip
      rintro g₁ g₂ x0 y x0' y' ⟨⟨-, rfl, he, hI⟩, -⟩
      exact ⟨rfl, he, hI⟩

theorem DB_P_fi (hP : FVP.fvP P ≤ ((dbL c).footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ (dbL c).equal_outside g₁ g₂ ∧
        dbI ((dbL c).get g₁) ((dbL c).get g₂))
      (Indifferentiability.DPRIMITIVE.fi state (List block) block (Module.app DPRestr
        (PRP.StrongPRP.SPRP_Oracles.mk state
          { f := PRP.StrongPRP.PRP.f state P, fi := PRP.StrongPRP.PRP.fi state P }))).procedure
      (Indifferentiability.DPRIMITIVE.fi state (List block) block (Module.app DPRestr
        (Module.app (Strong_RP_RF.DBounder.FBounder state max_size c)
          (PRP.StrongPRP.SPRP_Oracles.mk state
            { f := PRP.StrongPRP.PRP.f state P, fi := PRP.StrongPRP.PRP.fi state P })))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ (dbL c).equal_outside g₁ g₂ ∧
        dbI ((dbL c).get g₁) ((dbL c).get g₂)) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  rw [dprim_fi_mk, dprim_fi_FB]
  repeat stmt_inline{2} 0
  simp only [PRP.StrongPRP.SPRP_Oracles.fi.mk_simp]
  have hPf : FVP.fvP (PRP.StrongPRP.PRP.fi state P) ≤ ((dbL c).footprint)ᶜ := by fp_disjoint
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧
      §(localVarLens "y" state){1} = §(localVarLens "y" state){2} ∧
      (dbL c).equal_outside §allGlobals{1} §allGlobals{2} ∧
      dbI ((dbL c).get §allGlobals{1}) ((dbL c).get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  · equiv_if
    case guard =>
      rintro g₁ g₂ x0 y x0' y' ⟨-, -, -, hI1, -, -⟩
      rw [show C.c.get g₁ = C.c.get g₂ from congrArg Prod.fst hI1]
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§x0{1} = §x1{2} ∧
          (dbL c).equal_outside §allGlobals{1} §allGlobals{2} ∧
          dbI ((dbL c).get §allGlobals{1}) ((dbL c).get §allGlobals{2}) ∧ §C.c{1} + 1 ≤ max_size)
      · stmt_wp
        equiv_skip
        rintro g₁ g₂ x0 y x0' y' ⟨⟨rfl, -, he, hI⟩, hg⟩
        simp only [decide_eq_true_eq] at hg
        exact ⟨rfl, he, hI, hg⟩
      · equiv_if{2}
        case «then» =>
          stmt_wp{2} 1
          equiv_call (prhlProc_self_equal_outside_module (dbL c) (PRP.StrongPRP.PRP.fi state P)
            hPf dbI)
          equiv_skip
          rintro g₁ g₂ x0 x1 ⟨⟨hx, he, hI, hlt⟩, -⟩
          refine ⟨⟨hx, he, hI⟩, ?_⟩
          rintro r g₁' r' g₂' ⟨rfl, he', ⟨h1, h2, h3⟩⟩
          refine ⟨rfl, dbL_Cc_left c (dbL_Cc_right c (dbL_c_right c he' _) _) _, ?_⟩
          simp only [Prod.mk.injEq] at h1
          dsimp only at h2
          haveI := (inferInstance : Lens.Disjoint c C.c).symm
          simp only [dbI, Lens.get_of_disjoint_set, Lens.set_get]
          exact ⟨by rw [h1.1, h1.2.1, h1.2.2], by omega, h3⟩
        case «else» =>
          refine prhlStmt_pre prhlStmt_false ?_
          rintro σ₁ σ₂ ⟨⟨-, -, ⟨hI1, hc, -⟩, hlt⟩, hg⟩
          simp only [Prod.mk.injEq] at hI1
          simp only [decide_eq_false_iff_not, not_lt] at hg
          dsimp only at hc
          have := hI1.1
          omega
    case «else» =>
      equiv_skip
      rintro g₁ g₂ x0 y x0' y' ⟨⟨-, rfl, he, hI⟩, -⟩
      exact ⟨rfl, he, hI⟩


set_option maxHeartbeats 4000000 in
theorem DB_F_f (hP : FVP.fvP P ≤ ((dbL c).footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ (dbL c).equal_outside g₁ g₂ ∧
        dbI ((dbL c).get g₁) ((dbL c).get g₂))
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block (Module.app DFRestr
        (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
          { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
              (Module.app SqueezelessSponge (PRP.StrongPRP.SPRP_Oracles.mk state
                { f := PRP.StrongPRP.PRP.f state P,
                  fi := PRP.StrongPRP.PRP.fi state P })) }))).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block (Module.app DFRestr
        (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
          { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
              (Module.app SqueezelessSponge
                (Module.app (Strong_RP_RF.DBounder.FBounder state max_size c)
                  (PRP.StrongPRP.SPRP_Oracles.mk state
                    { f := PRP.StrongPRP.PRP.f state P,
                      fi := PRP.StrongPRP.PRP.fi state P }))) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ (dbL c).equal_outside g₁ g₂ ∧
        dbI ((dbL c).get g₁) ((dbL c).get g₂)) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  rw [dprim_f_mk, dprim_f_FB]
  repeat stmt_inline{2} 0
  simp only [PRP.StrongPRP.SPRP_Oracles.f.mk_simp]
  have hPf : FVP.fvP (PRP.StrongPRP.PRP.f state P) ≤ ((dbL c).footprint)ᶜ := by fp_disjoint
  stmt_wp
  equiv_seq 1 1 : (§bs{1} = §bs{2} ∧
      §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧
      (dbL c).equal_outside §allGlobals{1} §allGlobals{2} ∧
      dbI ((dbL c).get §allGlobals{1}) ((dbL c).get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  · equiv_if
    case guard =>
      rintro g₁ g₂ bs b bs' b' ⟨rfl, -, -, hI1, -, -⟩
      rw [show C.queries.get g₁ = C.queries.get g₂ from congrArg (fun t => t.2.1) hI1]
    case «else» =>
      stmt_wp
      equiv_skip
      rintro g₁ g₂ bs b bs' b' ⟨⟨rfl, -, he, hI⟩, -⟩
      exact ⟨by rw [show C.queries.get g₁ = C.queries.get g₂ from congrArg (fun t => t.2.1) hI.1],
        he, hI⟩
    case «then» =>
      equiv_if
      case guard =>
        rintro g₁ g₂ bs b bs' b' ⟨⟨rfl, -, -, hI1, -, -⟩, -⟩
        rw [show C.queries.get g₁ = C.queries.get g₂ from congrArg (fun t => t.2.1) hI1,
          show C.c.get g₁ = C.c.get g₂ from congrArg Prod.fst hI1]
      case «else» =>
        equiv_skip
        rintro g₁ g₂ bs b bs' b' ⟨⟨⟨rfl, rfl, he, hI⟩, -⟩, -⟩
        exact ⟨rfl, he, hI⟩
      case «then» =>
        stmt_wp
        equiv_while (§p{1} = §p{2} ∧ §p{1} = §bs{1} ∧ §bs{1} = §bs{2} ∧ §i{1} = §i{2} ∧
          §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧
          (dbL c).equal_outside §allGlobals{1} §allGlobals{2} ∧
          dbI ((dbL c).get §allGlobals{1}) ((dbL c).get §allGlobals{2}) ∧
          0 ≤ §i{2} ∧ §i{2} ≤ size §p{2} ∧ §C.c{2} ≤ max_size ∧
          (∀ j, 0 ≤ j → j ≤ §i{2} → FMap.dom §Redo.prefixes{2} (take j §p{2})) ∧
          (∀ j, 0 ≤ j → j ≤ dbq §p{2} §C.queries{2} → FMap.dom §Redo.prefixes{2} (take j §p{2})) ∧
          §c{2} ≤ §C.c{2} - (size §p{2} - dbq §p{2} §C.queries{2}) +
            max 0 (§i{2} - dbq §p{2} §C.queries{2}))
        case guard =>
          rintro g₁ g₂ p bs i sa sc p' bs' i' sa' sc' ⟨rfl, -, -, rfl, -⟩
          rfl
        case exit =>
          rintro g₁ g₂ p bs i sa sc p' bs' i' sa' sc'
            ⟨rfl, hb, rfl, rfl, rfl, rfl, he, hI, hi0, hip, hCm, hall, hq, hcnt⟩ hg
          simp only [decide_eq_false_iff_not, not_lt] at hg
          have hi : i = size p := by omega
          subst hi
          subst hb
          refine ⟨rfl, dbL_Cq_left c (dbL_Cq_right c he _) _, ?_⟩
          obtain ⟨hI1, -, hpre⟩ := hI
          have eC1 : C.c.get g₁ = C.c.get g₂ := congrArg Prod.fst hI1
          have eQ1 : C.queries.get g₁ = C.queries.get g₂ := congrArg (fun t => t.2.1) hI1
          have eR1 : Redo.prefixes.get g₁ = Redo.prefixes.get g₂ := congrArg (fun t => t.2.2) hI1
          haveI := (inferInstance : Lens.Disjoint c C.queries).symm
          simp only [dbI, Lens.get_of_disjoint_set, Lens.set_get]
          rw [eC1, eQ1, eR1]
          have hqs : dbq p (C.queries.get g₂) ≤ size p := prefix_sizel _ _
          have hm : max 0 (size p - dbq p (C.queries.get g₂)) = size p - dbq p (C.queries.get g₂) :=
            max_eq_right (by omega)
          rw [hm] at hcnt
          have hdp : FMap.dom (Redo.prefixes.get g₂) p := by
            simpa [take_size] using hall (size p) hi0 le_rfl
          exact ⟨rfl, by omega, dbPre_query _ _ _ _ hpre hdp⟩
        case body =>
          stmt_wp
          equiv_if
          case guard =>
            rintro g₁ g₂ p bs i sa sc p' bs' i' sa' sc' ⟨⟨rfl, -, -, rfl, -, -, -, hI1, -⟩, -⟩
            rw [show Redo.prefixes.get g₁ = Redo.prefixes.get g₂ from
              congrArg (fun t => t.2.2) hI1.1]
          case «then» =>
            stmt_wp
            equiv_skip
            rintro g₁ g₂ p bs i sa sc p' bs' i' sa' sc'
              ⟨⟨⟨rfl, hb, rfl, rfl, rfl, rfl, he, hI, hi0, hip, hCm, hall, hq, hcnt⟩, hg⟩, hg1⟩
            simp only [decide_eq_true_eq] at hg hg1
            have hR : Redo.prefixes.get g₁ = Redo.prefixes.get g₂ := congrArg (fun t => t.2.2) hI.1
            have hmx : max 0 (i - dbq p (C.queries.get g₂)) ≤
                max 0 (i + 1 - dbq p (C.queries.get g₂)) := max_le_max le_rfl (by omega)
            refine ⟨rfl, hb, rfl, rfl, by rw [hR], by rw [hR], he, hI, by omega, by omega, hCm, ?_,
              hq, by omega⟩
            intro j hj0 hj
            rcases lt_or_eq_of_le hj with hj | rfl
            · exact hall j hj0 (by omega)
            · rw [← hR]
              exact hg1
          case «else» =>
            stmt_wp
            refine prhlStmt_fix_right (fun σ => (dbL c).get σ.globals) (fun v => ?_)
            equiv_seq 1 1 : (§p{1} = §p{2} ∧ §p{1} = §bs{1} ∧ §bs{1} = §bs{2} ∧ §i{1} = §i{2} ∧
                (§sa{1}, §sc{1}) = §x0{2} ∧
                (dbL c).equal_outside §allGlobals{1} §allGlobals{2} ∧
                dbI ((dbL c).get §allGlobals{1}) ((dbL c).get §allGlobals{2}) ∧
                (dbL c).get §allGlobals{2} = v ∧
                0 ≤ §i{2} ∧ §i{2} < size §p{2} ∧ §C.c{2} ≤ max_size ∧
                (∀ j, 0 ≤ j → j ≤ §i{2} → FMap.dom §Redo.prefixes{2} (take j §p{2})) ∧
                (∀ j, 0 ≤ j → j ≤ dbq §p{2} §C.queries{2} →
                  FMap.dom §Redo.prefixes{2} (take j §p{2})) ∧
                dbq §p{2} §C.queries{2} ≤ §i{2} ∧
                §c{2} ≤ §C.c{2} - size §p{2} + §i{2})
            · stmt_wp
              equiv_skip
              rintro g₁ g₂ p bs i sa sc p' bs' i' sa' sc'
                ⟨⟨⟨⟨rfl, hb, rfl, rfl, rfl, rfl, he, hI, hi0, hip, hCm, hall, hq, hcnt⟩, hg⟩, hg1⟩,
                  hv⟩
              simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hg hg1
              have hR : Redo.prefixes.get g₁ = Redo.prefixes.get g₂ :=
                congrArg (fun t => t.2.2) hI.1
              have hqi : dbq p (C.queries.get g₂) ≤ i := by
                by_contra hlt
                exact hg1 (hR ▸ hq (i + 1) (by omega) (by omega))
              have hmax : max 0 (i - dbq p (C.queries.get g₂)) = i - dbq p (C.queries.get g₂) :=
                max_eq_right (by omega)
              rw [hmax] at hcnt
              exact ⟨rfl, hb, rfl, rfl, rfl, he, hI, hv, hi0, hg, hCm, hall, hq, hqi, by omega⟩
            · equiv_if{2}
              case «then» =>
                stmt_wp{2} 1
                equiv_call (prhlProc_self_equal_outside_module (dbL c)
                  (PRP.StrongPRP.PRP.f state P) hPf (fun x y => dbI x y ∧ y = v))
                equiv_skip
                rintro g₁ g₂ p bs i sa sc p' bs' i' x0
                  ⟨⟨rfl, hb, rfl, rfl, hx, he, hI, hv, hi0, hip, hCm, hall, hq, hqi, hcnt⟩, -⟩
                refine ⟨⟨hx, he, hI, hv⟩, ?_⟩
                rintro r g₁' r' g₂' ⟨rfl, he', hI', hv'⟩
                refine ⟨rfl, hb, rfl, rfl, rfl, rfl,
                  dbL_R_left c (dbL_R_right c (dbL_c_right c he' _) _) _, ?_⟩
                have hv0 := hv'.trans hv.symm
                simp only [Prod.mk.injEq] at hv0
                obtain ⟨ec, eC, eQ, eR⟩ := hv0
                obtain ⟨hI1, -, -⟩ := hI'
                simp only [Prod.mk.injEq] at hI1
                obtain ⟨eC1, eQ1, eR1⟩ := hI1
                haveI := (inferInstance : Lens.Disjoint c Redo.prefixes).symm
                simp only [dbI, Lens.get_of_disjoint_set, Lens.set_get]
                rw [eC1, eQ1, eR1, ec, eC, eQ, eR]
                obtain ⟨-, -, hpre⟩ := hI
                have hm : max 0 (i + 1 - dbq p (C.queries.get g₂)) =
                    i + 1 - dbq p (C.queries.get g₂) := max_eq_right (by omega)
                rw [hm]
                refine ⟨⟨rfl, by omega, dbPre_step _ _ p i _ hpre hall hi0⟩, by omega, by omega,
                  hCm,
                  ?_, fun j hj0 hj => (FMap.mem_set _ _ _ _).2 (Or.inl (hq j hj0 hj)), by omega⟩
                intro j hj0 hj
                rcases lt_or_eq_of_le hj with hj | rfl
                · exact (FMap.mem_set _ _ _ _).2 (Or.inl (hall j hj0 (by omega)))
                · exact (FMap.mem_set _ _ _ _).2 (Or.inr rfl)
              case «else» =>
                refine prhlStmt_pre prhlStmt_false ?_
                rintro σ₁ σ₂ ⟨⟨-, -, -, -, -, -, ⟨-, hc, -⟩, -, -, hip, hCm, -, -, -, hcnt⟩, hg⟩
                dsimp only at hc
                simp only [decide_eq_false_iff_not, not_lt] at hg
                omega
        stmt_wp
        equiv_skip
        rintro g₁ g₂ bs b bs' b' ⟨⟨⟨rfl, -, he, hI⟩, hnq⟩, hg⟩
        obtain ⟨hI1, hc, hpre⟩ := hI
        have eC1 : C.c.get g₁ = C.c.get g₂ := congrArg Prod.fst hI1
        have eQ1 : C.queries.get g₁ = C.queries.get g₂ := congrArg (fun t => t.2.1) hI1
        have eR1 : Redo.prefixes.get g₁ = Redo.prefixes.get g₂ := congrArg (fun t => t.2.2) hI1
        dsimp only at hc
        simp only [decide_eq_true_eq] at hg
        refine ⟨rfl, rfl, dbL_Cc_left c (dbL_Cc_right c he _) _, ?_⟩
        haveI := (inferInstance : Lens.Disjoint c C.c).symm
        simp only [dbI, Lens.get_of_disjoint_set, Lens.set_get]
        rw [eC1, eQ1, eR1] at *
        change dbPre (C.queries.get g₂) (Redo.prefixes.get g₂) at hpre
        have hq0 : 0 ≤ dbq bs (C.queries.get g₂) := prefix_ge0 _ _
        have hqs : dbq bs (C.queries.get g₂) ≤ size bs := prefix_sizel _ _
        have hm : max 0 (0 - dbq bs (C.queries.get g₂)) = 0 := max_eq_left (by omega)
        rw [hm]
        refine ⟨⟨rfl, by unfold dbq at hq0 hqs; omega, hpre⟩, by unfold dbq at hqs hq0; omega, hg,
          ?_, dbPre_take _ _ bs hpre, by unfold dbq at hq0 hqs ⊢; omega⟩
        intro j hj0 hj
        have : j = 0 := by omega
        subst this
        simpa [take] using hpre.2.1

end DB


omit [SLCommon.Params] in
theorem size_behead {α : Type} (l : List α) : l ≠ [] → size (behead l) = size l - 1 := by
  cases l with
  | nil => intro h; exact absurd rfl h
  | cons a l => intro _; simp [size, behead]

-- `local module (D' : PRPSec.Distinguisher) (P' : PRPSec.SPRP_Oracles)`, with `D` a Lean
-- parameter
set_option linter.gaudisCrypt.using false in
module D' (D : DISTINGUISHER) using (P' : Switching.PRPSec.SPRP_Oracles) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call Redo.init ();
    b <- call (Module.app (DRestr D) (Module.pair
      (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
        { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
            (Module.app SqueezelessSponge P') })
      P')) ();
    return $b
  };
}

set_option maxHeartbeats 4000000 in
-- the inlined oracles' wp goals are large
/-- `local lemma DoubleBounding (P <: PRPSec.PRP {-D, -C, -DBounder, -Redo})`; `DBounder`'s
variable is the lens `DBounder_FBounder_c`, fresh for the section's modules (exception E6). -/
theorem DoubleBounding (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ ((Perm.m).footprint ⊔
      (Perm.mi).footprint ⊔ C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔
      (Redo.prefixes).footprint)ᶜ)
    (DBounder_FBounder_c : Lens ℤ VariableAssignment)
    (_hfresh : DBounder_FBounder_c.footprint ≤ (FVP.fvP D ⊔ C.footprint ⊔
      (Redo.prefixes).footprint)ᶜ)
    (P : Switching.PRPSec.PRP)
    (_hP : FVP.fvP P ≤ ((FVP.fvP D).glob ⊔ C.footprint ⊔ DBounder_FBounder_c.footprint ⊔
      (Redo.prefixes).footprint)ᶜ)
    (m : VariableAssignment) :
    Procedure.Pr (Module.app Switching.PRPSec.IND (Module.pair P (D' D))).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (Module.app Switching.PRPSec.IND
        (Module.pair P (Switching.DBounder DBounder_FBounder_c (D' D)))).procedure () m
        (fun r _ => r = true) := by
  unfold C.footprint at _hDd _hfresh _hP
  have hcc : DBounder_FBounder_c.footprint ≤ (C.c.footprint)ᶜ :=
    _hfresh.trans (Footprint.compl_antimono (by fp_sub))
  have hcq : DBounder_FBounder_c.footprint ≤ (C.queries.footprint)ᶜ :=
    _hfresh.trans (Footprint.compl_antimono (by fp_sub))
  have hcr : DBounder_FBounder_c.footprint ≤ (Redo.prefixes.footprint)ᶜ :=
    _hfresh.trans (Footprint.compl_antimono (by fp_sub))
  haveI : Lens.Disjoint DBounder_FBounder_c C.c := Lens.disjoint_of_footprint_le_compl _ _ hcc
  haveI : Lens.Disjoint DBounder_FBounder_c C.queries :=
    Lens.disjoint_of_footprint_le_compl _ _ hcq
  haveI : Lens.Disjoint DBounder_FBounder_c Redo.prefixes :=
    Lens.disjoint_of_footprint_le_compl _ _ hcr
  have hdisj : FVP.fvP D ≤ ((dbL DBounder_FBounder_c).footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [dbL, Footprint.lens_pair]
    refine sup_le (_hfresh.trans (Footprint.compl_antimono (by fp_sub)))
      (sup_le ?_ (sup_le ?_ ?_)) <;>
    exact (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_sub)))
  have hPL : FVP.fvP P ≤ ((dbL DBounder_FBounder_c).footprint)ᶜ := by
    refine _hP.trans (Footprint.compl_antimono ?_)
    simp only [dbL, Footprint.lens_pair]
    fp_sub
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ g₁ r₂ g₂ h => by rw [h]) rfl
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  repeat stmt_inline{1} 1
  repeat stmt_inline{2} 1
  stmt_wp
  equiv_seq 8 10 : (§allGlobals{1} = §allGlobals{2})
  · equiv_sim
  · equiv_seq 1 1 : ((dbL DBounder_FBounder_c).equal_outside §allGlobals{1} §allGlobals{2} ∧
        dbI ((dbL DBounder_FBounder_c).get §allGlobals{1})
          ((dbL DBounder_FBounder_c).get §allGlobals{2}))
    · stmt_wp
      equiv_skip
      rintro g₁ g₂ rfl
      refine ⟨dbL_Cq_left _ (dbL_Cq_right _ (dbL_Cc_left _ (dbL_Cc_right _ (dbL_R_left _
        (dbL_R_right _ (dbL_c_right _ (Lens.equal_outside.refl g₁) 0) _) _) _) _) _) _, ?_⟩
      haveI := (inferInstance : Lens.Disjoint DBounder_FBounder_c C.c).symm
      haveI := (inferInstance : Lens.Disjoint DBounder_FBounder_c C.queries).symm
      haveI := (inferInstance : Lens.Disjoint DBounder_FBounder_c Redo.prefixes).symm
      simp only [dbI, Lens.get_of_disjoint_set, Lens.set_get]
      refine ⟨trivial, le_rfl, ?_, ?_, ?_⟩
      · intro l hl k
        obtain rfl : l = [] := by simpa [FMap.mem_set, FMap.mem_empty] using hl
        simp [take, FMap.mem_set]
      · simp [FMap.mem_set]
      · intro x hx
        obtain rfl : x = [] := by simpa [FMap.mem_set, FMap.mem_empty] using hx
        simp [FMap.mem_set]
    · have hcall := prhlProc_abstract_call_equal_outside_module (dbL DBounder_FBounder_c) D
        distExt hD.representable hdisj dbI (fun n => by
          cases n with
          | zero => exact inferInstanceAs (Countable (List block))
          | succ n => cases n with
            | zero => exact inferInstanceAs (Countable state)
            | succ n => cases n with
              | zero => exact inferInstanceAs (Countable state)
              | succ n => nomatch n)
        (Module.pair (Module.app DFRestr
          (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
            { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
                (Module.app SqueezelessSponge (PRP.StrongPRP.SPRP_Oracles.mk state
                  { f := PRP.StrongPRP.PRP.f state P, fi := PRP.StrongPRP.PRP.fi state P })) }))
          (Module.app DPRestr (PRP.StrongPRP.SPRP_Oracles.mk state
            { f := PRP.StrongPRP.PRP.f state P, fi := PRP.StrongPRP.PRP.fi state P })))
        (Module.pair (Module.app DFRestr
          (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
            { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
                (Module.app SqueezelessSponge
                  (Module.app (Strong_RP_RF.DBounder.FBounder state max_size DBounder_FBounder_c)
                    (PRP.StrongPRP.SPRP_Oracles.mk state
                      { f := PRP.StrongPRP.PRP.f state P,
                        fi := PRP.StrongPRP.PRP.fi state P }))) }))
          (Module.app DPRestr
            (Module.app (Strong_RP_RF.DBounder.FBounder state max_size DBounder_FBounder_c)
              (PRP.StrongPRP.SPRP_Oracles.mk state
                { f := PRP.StrongPRP.PRP.f state P, fi := PRP.StrongPRP.PRP.fi state P }))))
        (fun n => by
          cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
              Module.fst_pair]
            exact DB_F_f DBounder_FBounder_c P hPL
          | succ n => cases n with
            | zero =>
              simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
                HoleSigs.Instantiation.lookup_zero_cons, Module.snd_pair]
              exact DB_P_f DBounder_FBounder_c P hPL
            | succ n => cases n with
              | zero =>
                simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
                  HoleSigs.Instantiation.lookup_zero_single, Module.snd_pair]
                exact DB_P_fi DBounder_FBounder_c P hPL
              | succ n => nomatch n)
      equiv_call hcall
      equiv_skip
      exact fun _ _ h => ⟨h, fun _ _ _ _ h' => h'.1⟩

/-- `local clone import ProdSampling with type t1 <- block, type t2 <- capacity`. -/
noncomputable abbrev S := DProd.ProdSampling.S block capacity

/-- EC's `Real_Concrete`, for `declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo}` with
the axiom `D_ll` (over a region `G` outside the restrictions, exception E14).
`mu dstate (pred1 witness)` is the probability of `default`. -/
theorem Real_Concrete (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ ((Perm.m).footprint ⊔
      (Perm.mi).footprint ⊔ C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔
      (Redo.prefixes).footprint)ᶜ)
    (G : Footprint VariableAssignment)
    (_hGd : G ≤ ((Perm.m).footprint ⊔
      (Perm.mi).footprint ⊔ C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔
      (Redo.prefixes).footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ Gᶜ →
      FVP.fvP P ≤ Gᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (m : VariableAssignment) :
    (Procedure.Pr (GReal D).procedure () m (fun r g => r = true ∧ C.c.get g ≤ max_size) : ℝ) ≤
      (Procedure.Pr (CF (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) +
        ((max_size ^ 2 - max_size : ℤ) : ℝ) / 2 * (dstate.1 {default}).toReal := by
  sorry

end

end GaudisCrypt.SHA3.ConcreteF
