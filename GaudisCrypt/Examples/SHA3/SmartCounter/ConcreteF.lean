import GaudisCrypt.Examples.SHA3.SmartCounter.SLCommon
import GaudisCrypt.Lib.EC.Strong_RP_RF
import GaudisCrypt.Logic.FrameTactics
import GaudisCrypt.Logic.EqualOutside
import GaudisCrypt.Logic.LoopTransform
import GaudisCrypt.Logic.GlobMono

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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  rw [dprim_f_mk, dprim_f_FB]
  repeat stmt_inline{2} 0
  simp only [PRP.StrongPRP.SPRP_Oracles.f.mk_simp]
  have hPf : FVP.fvP (PRP.StrongPRP.PRP.f state P) ≤ ((dbL c).footprint)ᶜ := by fp_disjoint
  stmt_wp
  equiv_seq_last 1 1 : (§x0{1} = §x0{2} ∧
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
      equiv_seq_last 1 1 : (§x0{1} = §x1{2} ∧
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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  rw [dprim_fi_mk, dprim_fi_FB]
  repeat stmt_inline{2} 0
  simp only [PRP.StrongPRP.SPRP_Oracles.fi.mk_simp]
  have hPf : FVP.fvP (PRP.StrongPRP.PRP.fi state P) ≤ ((dbL c).footprint)ᶜ := by fp_disjoint
  stmt_wp
  equiv_seq_last 1 1 : (§x0{1} = §x0{2} ∧
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
      equiv_seq_last 1 1 : (§x0{1} = §x1{2} ∧
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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  rw [dprim_f_mk, dprim_f_FB]
  repeat stmt_inline{2} 0
  simp only [PRP.StrongPRP.SPRP_Oracles.f.mk_simp]
  have hPf : FVP.fvP (PRP.StrongPRP.PRP.f state P) ≤ ((dbL c).footprint)ᶜ := by fp_disjoint
  stmt_wp
  equiv_seq_last 1 1 : (§bs{1} = §bs{2} ∧
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
        equiv_while_raw (§p{1} = §p{2} ∧ §p{1} = §bs{1} ∧ §bs{1} = §bs{2} ∧ §i{1} = §i{2} ∧
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
            equiv_seq_last 1 1 : (§p{1} = §p{2} ∧ §p{1} = §bs{1} ∧ §bs{1} = §bs{2} ∧ §i{1} = §i{2} ∧
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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  repeat stmt_inline{1} 1
  repeat stmt_inline{2} 1
  stmt_wp
  equiv_seq_last 8 10 : (§allGlobals{1} = §allGlobals{2})
  · equiv_sim
  · equiv_seq_last 1 1 : ((dbL DBounder_FBounder_c).equal_outside §allGlobals{1} §allGlobals{2} ∧
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

/-! ### `Real_Concrete`'s game steps

EC's `byequiv; proc; inline *; sim` steps between `Indif`, `CF` and `PRPSec.IND` (the module
views bridged by `rfl`/`simp` lemmas), and the `ARP`/`PF` step (`ARP` with `PF`'s maps, its
`coll` flag outside `PF`). -/

/-- `PF` as a PRP is the record of its procedures. -/
theorem PF_prp_eq : (PF : Switching.PRPSec.PRP) =
    PRP.StrongPRP.PRP.mk state { init := PF.init, f := PF.f, fi := PF.fi } := rfl

theorem PF_f_eq : PRP.StrongPRP.PRP.f state (PF : Switching.PRPSec.PRP) = PF.f := by
  rw [PF_prp_eq]; simp

theorem PF_fi_eq : PRP.StrongPRP.PRP.fi state (PF : Switching.PRPSec.PRP) = PF.fi := by
  rw [PF_prp_eq]; simp

theorem PF_init_eq : PRP.StrongPRP.PRP.init state (PF : Switching.PRPSec.PRP) = PF.init := by
  rw [PF_prp_eq]; simp

theorem Perm_init_eq : Indifferentiability.PRIMITIVE.init state (List block) block Perm =
    PRP.RP.RP.init (block × capacity) dD Perm.m Perm.mi := by
  unfold Perm PRP.RP.RP
  simp [Indifferentiability.PRIMITIVE.init, PRP.StrongPRP.PRP.mk]

theorem view_Perm_eq : Indifferentiability.PRIMITIVE.view state (List block) block Perm =
    PRP.StrongPRP.SPRP_Oracles.mk state
      { f := PRP.StrongPRP.PRP.f state (Switching.PRPi.PRPi Perm.m Perm.mi),
        fi := PRP.StrongPRP.PRP.fi state (Switching.PRPi.PRPi Perm.m Perm.mi) } := rfl

theorem mk_Perm_eq : Indifferentiability.DPRIMITIVE.mk state (List block) block
      { f := Indifferentiability.PRIMITIVE.f state (List block) block Perm,
        fi := Indifferentiability.PRIMITIVE.fi state (List block) block Perm } =
    PRP.StrongPRP.SPRP_Oracles.mk state
      { f := PRP.StrongPRP.PRP.f state (Switching.PRPi.PRPi Perm.m Perm.mi),
        fi := PRP.StrongPRP.PRP.fi state (Switching.PRPi.PRPi Perm.m Perm.mi) } := rfl

/-- EC: `Pr[Indif(SqueezelessSponge(Perm), Perm, DRestr(D)).main() @ &m: res] =
Pr[PRPSec.IND(PRPi.PRPi, D'(D)).main() @ &m: res]` (`byequiv; proc; inline *; sim`). -/
theorem Indif_IND_Perm (m : VariableAssignment) :
    Procedure.Pr (Module.app Indif (Module.pair
        (Module.app SqueezelessSponge (Indifferentiability.PRIMITIVE.view state (List block) block
          Perm)) (Module.pair Perm (DRestr D)))).procedure () m (fun r _ => r = true) =
      Procedure.Pr (Module.app Switching.PRPSec.IND
        (Module.pair (Switching.PRPi.PRPi Perm.m Perm.mi) (D' D))).procedure () m
        (fun r _ => r = true) := by
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ g₁ r₂ g₂ h => by rw [h]) rfl
  equiv_proc_to_stmt
  stmt_inline{1} 0
  rw [Perm_init_eq]
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  rw [view_Perm_eq, mk_Perm_eq]
  stmt_wp
  equiv_sim

theorem view_PF_sprp : Indifferentiability.PRIMITIVE.view state (List block) block PF =
    PRP.StrongPRP.SPRP_Oracles.mk state
      { f := PRP.StrongPRP.PRP.f state (PF : Switching.PRPSec.PRP),
        fi := PRP.StrongPRP.PRP.fi state (PF : Switching.PRPSec.PRP) } := rfl

theorem mk_PF_eq : Indifferentiability.DPRIMITIVE.mk state (List block) block
      { f := Indifferentiability.PRIMITIVE.f state (List block) block PF,
        fi := Indifferentiability.PRIMITIVE.fi state (List block) block PF } =
    PRP.StrongPRP.SPRP_Oracles.mk state
      { f := PRP.StrongPRP.PRP.f state (PF : Switching.PRPSec.PRP),
        fi := PRP.StrongPRP.PRP.fi state (PF : Switching.PRPSec.PRP) } := rfl

theorem PF_prim_init_eq : Indifferentiability.PRIMITIVE.init state (List block) block PF =
    PF.init := by
  rw [← PF_init_eq]; rfl

/-- EC: `Pr[CF(DRestr(D)).main() @ &m: res] = Pr[PRPSec.IND(PF, D'(D)).main() @ &m: res]`
(`byequiv; proc; inline *; sim`). -/
theorem CF_IND_PF (m : VariableAssignment) :
    Procedure.Pr (CF (DRestr D)).procedure () m (fun r _ => r = true) =
      Procedure.Pr (Module.app Switching.PRPSec.IND
        (Module.pair (PF : Switching.PRPSec.PRP) (D' D))).procedure () m
        (fun r _ => r = true) := by
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ _ r₂ _ => r₁ = r₂) ?_ (fun r₁ g₁ r₂ g₂ h => by rw [h]) rfl
  unfold CF
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  rw [view_PF_sprp, mk_PF_eq]
  stmt_wp
  equiv_sim

section ARPPF
variable (coll : Lens Bool VariableAssignment) [Lens.Disjoint PF.m coll] [Lens.Disjoint PF.mi coll]

theorem ARP_PF_f :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ coll.equal_outside g₁ g₂ ∧ True)
      (PRP.StrongPRP.PRP.f state (Switching.ARP coll PF.m PF.mi)).procedure
      (PRP.StrongPRP.PRP.f state (PF : Switching.PRPSec.PRP)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ coll.equal_outside g₁ g₂ ∧ True) := by
  rw [PF_f_eq]
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§x0{1} = §x0{2} ∧ coll.equal_outside §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, he⟩
    exact ⟨rfl, he⟩
  · equiv_if
    case guard =>
      rintro g₁ g₂ x _ ⟨rfl, he⟩
      rw [Lens.equal_outside.get_disjoint (X := PF.m) he]
    case «else» =>
      equiv_skip
      rintro g₁ g₂ x _ ⟨⟨rfl, he⟩, -⟩
      exact ⟨by rw [Lens.equal_outside.get_disjoint (X := PF.m) he], he⟩
    case «then» =>
      stmt_wp
      equiv_rnd_dprod
      equiv_skip
      rintro g₁ g₂ x0 _ ⟨⟨rfl, he⟩, -⟩
      refine fun p _ => ?_
      haveI := (inferInstance : Lens.Disjoint PF.m coll).symm
      haveI := (inferInstance : Lens.Disjoint PF.mi coll).symm
      simp only [Lens.get_of_disjoint_set, Prod.mk.eta]
      have hm := Lens.equal_outside.get_disjoint (X := PF.m) he
      have hmi := Lens.equal_outside.get_disjoint (X := PF.mi) he
      rw [hm, hmi]
      exact ⟨rfl, Lens.equal_outside.set_disjoint (Lens.equal_outside.set_disjoint
        (Lens.equal_outside.set_left he _) _) _⟩

theorem ARP_PF_fi :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ coll.equal_outside g₁ g₂ ∧ True)
      (PRP.StrongPRP.PRP.fi state (Switching.ARP coll PF.m PF.mi)).procedure
      (PRP.StrongPRP.PRP.fi state (PF : Switching.PRPSec.PRP)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ coll.equal_outside g₁ g₂ ∧ True) := by
  rw [PF_fi_eq]
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§y{1} = §x0{2} ∧ coll.equal_outside §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, he⟩
    exact ⟨rfl, he⟩
  · equiv_if
    case guard =>
      rintro g₁ g₂ y _ ⟨rfl, he⟩
      rw [Lens.equal_outside.get_disjoint (X := PF.mi) he]
    case «else» =>
      equiv_skip
      rintro g₁ g₂ y _ ⟨⟨rfl, he⟩, -⟩
      exact ⟨by rw [Lens.equal_outside.get_disjoint (X := PF.mi) he], he⟩
    case «then» =>
      stmt_wp
      equiv_rnd_dprod
      equiv_skip
      rintro g₁ g₂ y _ ⟨⟨rfl, he⟩, -⟩
      refine fun p _ => ?_
      haveI := (inferInstance : Lens.Disjoint PF.m coll).symm
      haveI := (inferInstance : Lens.Disjoint PF.mi coll).symm
      simp only [Lens.get_of_disjoint_set, Prod.mk.eta]
      have hm := Lens.equal_outside.get_disjoint (X := PF.m) he
      have hmi := Lens.equal_outside.get_disjoint (X := PF.mi) he
      rw [hm, hmi, ← (inferInstance : Lens.Disjoint PF.mi PF.m).commute]
      exact ⟨rfl, Lens.equal_outside.set_disjoint (Lens.equal_outside.set_disjoint
        (Lens.equal_outside.set_left he _) _) _⟩

/-- EC: `PRPSec.IND(ARP, Dist) ~ PRPSec.IND(PF, Dist)` with `ARP.m = PF.m`, `ARP.mi = PF.mi`:
the two oracles sample the same pair, `ARP.coll` (outside `Dist`) only differs.  The call is
the equal-outside abstract call rule over `coll`. -/
theorem IND_ARP_PF (Dist : Switching.PRPSec.Distinguisher)
    (hDd : FVP.fvP Dist ≤ (coll.footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (Module.app Switching.PRPSec.IND (Module.pair (Switching.ARP coll PF.m PF.mi) Dist)).procedure
      (Module.app Switching.PRPSec.IND
        (Module.pair (PF : Switching.PRPSec.PRP) Dist)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hcall := prhlProc_abstract_call_equal_outside_module coll Dist
    (Strong_RP_RF.SPRP_Oracles.ext state) (Strong_RP_RF.Distinguisher.representable state Dist)
    hDd (fun _ _ => True)
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable state)
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable state)
        | succ n => nomatch n)
    (PRP.StrongPRP.SPRP_Oracles.mk state
      { f := PRP.StrongPRP.PRP.f state (Switching.ARP coll PF.m PF.mi)
        fi := PRP.StrongPRP.PRP.fi state (Switching.ARP coll PF.m PF.mi) })
    (PRP.StrongPRP.SPRP_Oracles.mk state
      { f := PRP.StrongPRP.PRP.f state (PF : Switching.PRPSec.PRP)
        fi := PRP.StrongPRP.PRP.fi state (PF : Switching.PRPSec.PRP) })
    (fun n => by cases n with
      | zero =>
        simp only [Strong_RP_RF.SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_zero_cons,
          PRP.StrongPRP.SPRP_Oracles.f.mk_simp]
        exact ARP_PF_f coll
      | succ n => cases n with
        | zero =>
          simp only [Strong_RP_RF.SPRP_Oracles.ext, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single, PRP.StrongPRP.SPRP_Oracles.fi.mk_simp]
          exact ARP_PF_fi coll
        | succ n => nomatch n)
  equiv_proc_to_stmt
  stmt_inline 0
  rw [PF_init_eq]
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_call hcall
  stmt_wp
  equiv_skip
  rintro g₁ g₂ rfl
  exact ⟨(Lens.equal_outside.refl _).set_left _, fun _ _ _ _ h => h.1⟩

end ARPPF

/-- `SqueezelessSponge(P).f` is lossless when `P.f` is: its loop is counted (variant
`size p - i`).  Not an EC lemma: EC proves it inline in `CF_G1`. -/
theorem SqueezelessSponge_f_ll (P : DPRIMITIVE)
    (hP : (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless) :
    (Indifferentiability.FUNCTIONALITY.f state (List block) block
      (Module.app SqueezelessSponge P)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hP ⊢
  refine phoareProc_eq_of_le_ge (fun _ _ _ => Procedure.ewp_const_le _ _ _ _) ?_
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_while_ge 1 variant (size §p - §i).toNat
  case body =>
    phoare_wp 4
    phoare_simp [hP]
    phoare_skip
    intros
    split <;> simp
  case exit => trivial
  case decreases =>
    intro k
    hoare_wp 1
    hoare_split 1
    refine hoare_seq (hoare_if_wp (At := ?At) (Ae := ?Ae) ?_ ?_) ?_
    rotate_left 2
    · hoare_wp 1
      exact hoare_skip_wp _
    · hoare_wp 1
      hoare_call
      hoare_wp 1
      exact hoare_skip_wp _
    hoare_skip
    rintro i p _ ⟨hlt, rfl⟩
    simp only [decide_eq_true_eq] at hlt
    exact ⟨fun _ => by omega, fun _ _ _ => by omega⟩
  phoare_wp 4
  phoare_skip
  intros; exact le_rfl

/-! ## `GReal ~ GReal'` (the first step of `Real_Concrete`) -/

/-- The lens of `GReal_GReal'`'s invariant: `C.c`, `C.queries`, `Redo.prefixes`. -/
noncomputable abbrev grL : Lens (ℤ × FMap (List block) block × FMap (List block) state)
    VariableAssignment :=
  Lens.pair C.c (Lens.pair C.queries Redo.prefixes)

/-- `GReal_GReal'`'s invariant on `(C.c, C.queries, Redo.prefixes)` (EC's `={C.c, Redo.prefixes}
/\ prefix_inv C.queries{2} Redo.prefixes{1} /\ Redo.prefixes{1}.[[]] = Some (b0, c0) /\
all_prefixes Redo.prefixes{1}`): the left's `C.queries` is not used. -/
def grI (x y : ℤ × FMap (List block) block × FMap (List block) state) : Prop :=
  x.1 = y.1 ∧ x.2.2 = y.2.2 ∧ prefix_inv y.2.1 y.2.2 ∧ FMap.get y.2.2 [] = some (b0, c0) ∧
    all_prefixes y.2.2

/-- A write of `C.c` on the right keeps the states equal outside `grL`. -/
theorem grL_Cc_right {g₁ g₂ : VariableAssignment} (h : grL.equal_outside g₁ g₂) (v : ℤ) :
    grL.equal_outside g₁ (C.c.set v g₂) := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨(v, x.2), by simp only [grL, Lens.pair, C.c.set_set]⟩

/-- A write of `C.c` on the left keeps the states equal outside `grL`. -/
theorem grL_Cc_left {g₁ g₂ : VariableAssignment} (h : grL.equal_outside g₁ g₂) (v : ℤ) :
    grL.equal_outside (C.c.set v g₁) g₂ := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨x, ?_⟩
  simp only [grL, Lens.pair]
  rw [(inferInstance : Lens.Disjoint Redo.prefixes C.c).commute,
    (inferInstance : Lens.Disjoint C.queries C.c).commute, C.c.set_set]

/-- A write of `C.queries` on the right keeps the states equal outside `grL`. -/
theorem grL_Cq_right {g₁ g₂ : VariableAssignment} (h : grL.equal_outside g₁ g₂)
    (v : FMap (List block) block) : grL.equal_outside g₁ (C.queries.set v g₂) := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨(x.1, v, x.2.2), ?_⟩
  simp only [grL, Lens.pair]
  rw [← (inferInstance : Lens.Disjoint C.c C.queries).commute, C.queries.set_set]

/-- A write of `Redo.prefixes` on the right keeps the states equal outside `grL`. -/
theorem grL_R_right {g₁ g₂ : VariableAssignment} (h : grL.equal_outside g₁ g₂)
    (v : FMap (List block) state) : grL.equal_outside g₁ (Redo.prefixes.set v g₂) := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨(x.1, x.2.1, v), ?_⟩
  simp only [grL, Lens.pair]
  rw [← (inferInstance : Lens.Disjoint C.c Redo.prefixes).commute,
    ← (inferInstance : Lens.Disjoint C.queries Redo.prefixes).commute, Redo.prefixes.set_set]

/-- A write of `Redo.prefixes` on the left keeps the states equal outside `grL`. -/
theorem grL_R_left {g₁ g₂ : VariableAssignment} (h : grL.equal_outside g₁ g₂)
    (v : FMap (List block) state) : grL.equal_outside (Redo.prefixes.set v g₁) g₂ := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨x, by simp only [grL, Lens.pair, Redo.prefixes.set_set]⟩

/-- The initial `C.queries`, `Redo.prefixes` satisfy `grI`. -/
theorem grI_init (c : ℤ) :
    grI (c, FMap.set FMap.empty [] b0, FMap.set FMap.empty [] (b0, c0))
      (c, FMap.set FMap.empty [] b0, FMap.set FMap.empty [] (b0, c0)) := by
  have hnil : ∀ i, take i ([] : List block) = [] := fun i => by simp [take]
  refine ⟨rfl, rfl, ⟨?_, ?_, ?_⟩, by simp [FMap.get_set_sameE], ?_⟩
  · intro bs hbs
    obtain rfl : bs = [] := by simpa [FMap.mem_set, FMap.mem_empty] using hbs
    simp [FMap.get_set_sameE, oget]
  · intro bs hbs i
    obtain rfl : bs = [] := by simpa [FMap.mem_set, FMap.mem_empty] using hbs
    simp [hnil, FMap.mem_set]
  · intro bs i hne hbs
    exact absurd (by simpa [FMap.mem_set, FMap.mem_empty] using hbs) hne
  · intro bs hbs i
    obtain rfl : bs = [] := by simpa [FMap.mem_set, FMap.mem_empty] using hbs
    simp [hnil, FMap.mem_set]

/-- `Perm` touches `Perm.m`, `Perm.mi`.  Not an EC lemma (EC reads it off the code). -/
theorem fvP_Perm : FVP.fvP Perm ≤ (Lens.pair Perm.m Perm.mi).footprint := by
  fp_module (Lens.pair Perm.m Perm.mi)

/-- `Perm` is outside `grL`. -/
theorem fvP_Perm_grL : FVP.fvP Perm ≤ (grL.footprint)ᶜ :=
  fvP_Perm.trans (Lens.footprint_le_compl_of_disjoint _ _)

/-- `PC(Perm).f` on both sides keeps `grL`'s invariant (EC: `proc; inline*; sp; if; auto`). -/
theorem GR_P_f :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ grL.equal_outside g₁ g₂ ∧
        grI (grL.get g₁) (grL.get g₂))
      (Indifferentiability.PRIMITIVE.f state (List block) block (Module.app PC Perm)).procedure
      (Indifferentiability.PRIMITIVE.f state (List block) block (Module.app PC Perm)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ grL.equal_outside g₁ g₂ ∧
        grI (grL.get g₁) (grL.get g₂)) := by
  have hP := fvP_Perm_grL
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  have hPf : FVP.fvP (Indifferentiability.PRIMITIVE.f state (List block) block Perm) ≤
      (grL.footprint)ᶜ := by fp_disjoint
  stmt_wp
  equiv_call (prhlProc_self_equal_outside_module grL _ hPf grI)
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x x' ⟨rfl, he, hI⟩
  refine ⟨⟨rfl, he, hI⟩, ?_⟩
  rintro r g₁' r' g₂' ⟨rfl, he', hI'⟩
  refine ⟨rfl, grL_Cc_left (grL_Cc_right he' _) _, ?_⟩
  exact ⟨congrArg (· + 1) hI'.1, hI'.2⟩

/-- `PC(Perm).fi` on both sides keeps `grL`'s invariant (EC: `proc; inline*; sp; if; auto`). -/
theorem GR_P_fi :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ grL.equal_outside g₁ g₂ ∧
        grI (grL.get g₁) (grL.get g₂))
      (Indifferentiability.PRIMITIVE.fi state (List block) block (Module.app PC Perm)).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block) block (Module.app PC Perm)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ grL.equal_outside g₁ g₂ ∧
        grI (grL.get g₁) (grL.get g₂)) := by
  have hP := fvP_Perm_grL
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  have hPf : FVP.fvP (Indifferentiability.PRIMITIVE.fi state (List block) block Perm) ≤
      (grL.footprint)ᶜ := by fp_disjoint
  stmt_wp
  equiv_call (prhlProc_self_equal_outside_module grL _ hPf grI)
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x x' ⟨rfl, he, hI⟩
  refine ⟨⟨rfl, he, hI⟩, ?_⟩
  rintro r g₁' r' g₂' ⟨rfl, he', hI'⟩
  refine ⟨rfl, grL_Cc_left (grL_Cc_right he' _) _, ?_⟩
  exact ⟨congrArg (· + 1) hI'.1, hI'.2⟩

omit [SLCommon.Params] in
/-- The size of `take j p`. -/
theorem size_take' {α : Type} (j : ℤ) (p : List α) : size (take j p) = min (max j 0) (size p) := by
  simp only [size, take, List.length_take]
  omega

/-- A prefix of `p` known to `Redo.prefixes` and extended by a query is at most `p`'s longest
queried prefix. -/
theorem gr_max (Q : FMap (List block) block) (pref : FMap (List block) state) (p : List block)
    (j : ℤ) (h3 : ∀ l, l ≠ [] → FMap.dom pref l → ∃ l2, FMap.dom Q (l ++ l2)) (hj0 : 0 < j)
    (hjs : j ≤ size p) (hd : FMap.dom pref (take j p)) : j ≤ dbq p Q := by
  have hne : take j p ≠ [] := by
    intro h
    have := size_take' j p
    rw [h] at this
    have h0 : size ([] : List block) = 0 := rfl
    omega
  obtain ⟨l2, hl2⟩ := h3 _ hne hd
  have h1 : «prefix» p (take j p ++ l2) ≤ dbq p Q :=
    get_max_prefix_max p _ _ ((mem_elems_fdom _ _).2 hl2)
  have h2 : «prefix» (take j p) p ≤ «prefix» (take j p ++ l2) p := prefix_leq_prefix_cat _ _ _
  have h3' : «prefix» (take j p) p = min (size p) (max j 0) := by
    rw [prefix_take_min, prefix_eq]
  have h4 := prefixC p (take j p ++ l2)
  omega

/-- The prefix facts that `Redo.prefixes` keeps during a fresh query `p` of `FC`: `prefix_inv`'s
first two components, its third for the queries and `p`, `[]`, and `all_prefixes`. -/
def grPre (Q : FMap (List block) block) (p : List block) (pref : FMap (List block) state) :
    Prop :=
  (∀ bs, FMap.dom Q bs → oget (FMap.get Q bs) = (oget (FMap.get pref bs)).1) ∧
  (∀ bs, FMap.dom Q bs → ∀ i, FMap.dom pref (take i bs)) ∧
  (∀ l, l ≠ [] → FMap.dom pref l → (∃ l2, FMap.dom Q (l ++ l2)) ∨ ∃ l2, l ++ l2 = p) ∧
  FMap.get pref [] = some (b0, c0) ∧ all_prefixes pref

/-- The invariant of the two loops on a fresh query `p` at step `i`: `grPre`, `(sa, sc)` the
state of `take i p`, the prefixes of `p` up to `i` and up to its longest queried prefix known, and
none longer than both. -/
def grLoop (Q : FMap (List block) block) (pref : FMap (List block) state) (p : List block) (i : ℤ)
    (sa : block) (sc : capacity) : Prop :=
  grPre Q p pref ∧ 0 ≤ i ∧ i ≤ size p ∧ FMap.get pref (take i p) = some (sa, sc) ∧
  (∀ j, 0 ≤ j → j ≤ i → FMap.dom pref (take j p)) ∧
  (∀ j, 0 ≤ j → j ≤ dbq p Q → FMap.dom pref (take j p)) ∧
  (∀ j, dbq p Q < j → j ≤ size p → FMap.dom pref (take j p) → j ≤ i)

/-- `grLoop` holds when the loops start. -/
theorem grLoop_init (Q : FMap (List block) block) (pref : FMap (List block) state)
    (p : List block) (hinv : prefix_inv Q pref) (h0 : FMap.get pref [] = some (b0, c0))
    (hall : all_prefixes pref) : grLoop Q pref p 0 b0 c0 := by
  obtain ⟨h1, h2, h3⟩ := hinv
  have hnil : take 0 p = [] := by simp [take]
  have hd0 : FMap.dom pref [] := by rw [FMap.domE, h0]; simp
  have h3' : ∀ l, l ≠ [] → FMap.dom pref l → ∃ l2, FMap.dom Q (l ++ l2) := by
    intro l hl hd
    rw [← take_size l] at hl hd ⊢
    exact h3 l (size l) hl hd
  have hQ : ∀ x, FMap.dom Q x → FMap.dom pref x := fun x hx => by
    simpa [take_size] using h2 x hx (size x)
  refine ⟨⟨h1, h2, fun l hl hd => Or.inl (h3' l hl hd), h0, hall⟩, le_rfl,
    by simp [size], by rw [hnil, h0], ?_, dbPre_take Q pref p ⟨hall, hd0, hQ⟩, ?_⟩
  · intro j hj0 hj
    obtain rfl : j = 0 := by omega
    rw [hnil]; exact hd0
  · intro j hj hjs hd
    have hq0 : 0 ≤ dbq p Q := prefix_ge0 _ _
    have := gr_max Q pref p j h3' (by omega) hjs hd
    omega

/-- A loop step that reads a known prefix keeps `grLoop`, and stays below the longest queried
prefix. -/
theorem grLoop_read (Q : FMap (List block) block) (pref : FMap (List block) state)
    (p : List block) (i : ℤ) (sa : block) (sc : capacity) (h : grLoop Q pref p i sa sc)
    (hi : i < size p) (hd : FMap.dom pref (take (i + 1) p)) :
    i + 1 ≤ dbq p Q ∧ grLoop Q pref p (i + 1) (oget (FMap.get pref (take (i + 1) p))).1
      (oget (FMap.get pref (take (i + 1) p))).2 := by
  obtain ⟨hpre, hi0, his, hget, hall, hq, hmax⟩ := h
  have hle : i + 1 ≤ dbq p Q := by
    by_contra hlt
    have := hmax (i + 1) (by omega) (by omega) hd
    omega
  refine ⟨hle, hpre, by omega, by omega, ?_, ?_, hq, fun j hj hjs hdj => ?_⟩
  · rw [FMap.domE] at hd
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hd
    simp [hw, oget]
  · intro j hj0 hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact hall j hj0 (by omega)
    · exact hd
  · have := hmax j hj hjs hdj
    omega

/-- A loop step that computes a new prefix keeps `grLoop`, and is past the longest queried
prefix. -/
theorem grLoop_call (Q : FMap (List block) block) (pref : FMap (List block) state)
    (p : List block) (i : ℤ) (sa : block) (sc : capacity) (h : grLoop Q pref p i sa sc)
    (hi : i < size p) (hd : ¬ FMap.dom pref (take (i + 1) p)) :
    dbq p Q ≤ i ∧ ∀ w : state,
      grLoop Q (FMap.set pref (take (i + 1) p) w) p (i + 1) w.1 w.2 := by
  obtain ⟨⟨h1, h2, h3, h0, hpall⟩, hi0, his, hget, hall, hq, hmax⟩ := h
  have hle : dbq p Q ≤ i := by
    by_contra hlt
    exact hd (hq (i + 1) (by omega) (by omega))
  refine ⟨hle, fun w => ?_⟩
  have hQ : ∀ x, FMap.dom Q x → FMap.dom pref x := fun x hx => by
    simpa [take_size] using h2 x hx (size x)
  have hd0 : FMap.dom pref [] := by rw [FMap.domE, h0]; simp
  have grow : ∀ l, FMap.dom pref l → FMap.dom (FMap.set pref (take (i + 1) p) w) l :=
    fun l hl => (FMap.mem_set _ _ _ _).2 (Or.inl hl)
  have hne : ∀ l, FMap.dom pref l → l ≠ take (i + 1) p := fun l hl he => hd (he ▸ hl)
  refine ⟨⟨fun bs hbs => ?_, fun bs hbs j => grow _ (h2 bs hbs j), fun l hl hdl => ?_, ?_,
    (dbPre_step Q pref p i w ⟨hpall, hd0, hQ⟩ hall hi0).1⟩, by omega, by omega,
    by simp, fun j hj0 hj => ?_, fun j hj0 hj => grow _ (hq j hj0 hj), fun j hj hjs hdj => ?_⟩
  · rw [FMap.get_set_neqE _ _ _ _ (hne bs (hQ bs hbs))]
    exact h1 bs hbs
  · rcases (FMap.mem_set _ _ _ _).1 hdl with hdl | rfl
    · exact h3 l hl hdl
    · exact Or.inr ⟨drop (i + 1) p, cat_take_drop _ _⟩
  · rw [FMap.get_set_neqE _ _ _ _ (hne [] hd0)]
    exact h0
  · rcases lt_or_eq_of_le hj with hj | rfl
    · exact grow _ (hall j hj0 (by omega))
    · exact (FMap.mem_set _ _ _ _).2 (Or.inr rfl)
  · rcases (FMap.mem_set _ _ _ _).1 hdj with hdj | he
    · have := hmax j hj hjs hdj
      omega
    · have e1 := size_take' j p
      have e2 := size_take' (i + 1) p
      rw [he] at e1
      omega

/-- When the loops end, `i` is `size p` and the query `p` answered `sa` keeps `prefix_inv`. -/
theorem grLoop_exit (Q : FMap (List block) block) (pref : FMap (List block) state)
    (p : List block) (i : ℤ) (sa : block) (sc : capacity) (h : grLoop Q pref p i sa sc)
    (hi : ¬ i < size p) :
    i = size p ∧ prefix_inv (FMap.set Q p sa) pref ∧ FMap.get pref [] = some (b0, c0) ∧
      all_prefixes pref := by
  obtain ⟨⟨h1, h2, h3, h0, hpall⟩, hi0, his, hget, hall, hq, hmax⟩ := h
  have hip : i = size p := by omega
  subst hip
  rw [take_size] at hget
  have hdp : FMap.dom pref p := by rw [FMap.domE, hget]; simp
  refine ⟨rfl, ⟨fun bs hbs => ?_, fun bs hbs j => ?_, fun bs j hne hdj => ?_⟩, h0, hpall⟩
  · by_cases hb : bs = p
    · subst hb
      simp [hget, oget]
    · rw [FMap.get_set_neqE _ _ _ _ hb]
      exact h1 bs (by simpa [FMap.mem_set, hb] using hbs)
  · by_cases hb : bs = p
    · subst hb
      exact hpall _ hdp j
    · exact h2 bs (by simpa [FMap.mem_set, hb] using hbs) j
  · rcases h3 _ hne hdj with ⟨l2, hl2⟩ | ⟨l2, hl2⟩
    · exact ⟨l2, (FMap.mem_set _ _ _ _).2 (Or.inl hl2)⟩
    · exact ⟨l2, (FMap.mem_set _ _ _ _).2 (Or.inr hl2)⟩

/-- Under `grI`, the prefixes of a query are known on the left. -/
theorem grI_dom {x y : ℤ × FMap (List block) block × FMap (List block) state} (h : grI x y)
    {bs : List block} (hb : FMap.dom y.2.1 bs) (j : ℤ) : FMap.dom x.2.2 (take j bs) := by
  rw [h.2.1]
  exact h.2.2.1.2.1 bs hb j

omit [SLCommon.Params] in
/-- A false precondition. -/
theorem hoare_false' {s : Stmt} {B : ProgramState → Prop} : hoareStmt (fun _ => False) s B :=
  fun _ h => h.elim

/-- `SqueezelessSponge(PC(Perm)).f ~ FC(SqueezelessSponge(Perm)).f` under `grI` (EC: `proc;
inline *; wp; sp; if{2}`, the cached case a one-sided loop, the fresh one synchronized loops
whose counter difference is the number of known blocks). -/
theorem GR_F_f :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ grL.equal_outside g₁ g₂ ∧
        grI (grL.get g₁) (grL.get g₂))
      (Indifferentiability.FUNCTIONALITY.f state (List block) block
        (Module.app SqueezelessSponge
          (Indifferentiability.PRIMITIVE.view state (List block) block
            (Module.app PC Perm)))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block) block
        (Module.app FC (Module.app SqueezelessSponge
          (Indifferentiability.PRIMITIVE.view state (List block) block Perm)))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ grL.equal_outside g₁ g₂ ∧
        grI (grL.get g₁) (grL.get g₂)) := by
  have hP := fvP_Perm_grL
  have hPf : FVP.fvP (Indifferentiability.PRIMITIVE.f state (List block) block Perm) ≤
      (grL.footprint)ᶜ := by fp_disjoint
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  rw [Indifferentiability.PRIMITIVE.view_f]
  stmt_wp
  equiv_seq_last 1 1 : (§p{1} = §bs{2} ∧ §sa{1} = b0 ∧ §sc{1} = c0 ∧ §i{1} = 0 ∧
      §(localVarLens "b" block){2} = b0 ∧
      grL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      grI (grL.get §allGlobals{1}) (grL.get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  · equiv_if{2}
    case «then» =>
      stmt_wp
      equiv_while_raw (§p{1} = §p{2} ∧ §p{2} = §bs{2} ∧ §i{1} = §i{2} ∧ §sa{1} = §sa{2} ∧
          §sc{1} = §sc{2} ∧ grL.equal_outside §allGlobals{1} §allGlobals{2} ∧
          §Redo.prefixes{1} = §Redo.prefixes{2} ∧
          §C.c{1} = §C.c{2} - (size §p{2} - dbq §p{2} §C.queries{2}) +
            max 0 (§i{2} - dbq §p{2} §C.queries{2}) ∧
          ¬ FMap.dom §C.queries{2} §p{2} ∧
          grLoop §C.queries{2} §Redo.prefixes{2} §p{2} §i{2} §sa{2} §sc{2})
      case guard =>
        rintro g₁ g₂ p i sa sc p' bs i' sa' sc' ⟨rfl, -, rfl, -⟩
        rfl
      case exit =>
        rintro g₁ g₂ p i sa sc p' bs i' sa' sc'
          ⟨rfl, rfl, rfl, rfl, rfl, he, hR, hc, hnq, hL⟩ hg
        simp only [decide_eq_false_iff_not] at hg
        obtain ⟨rfl, hinv, h0, hall⟩ := grLoop_exit _ _ _ _ _ _ hL hg
        have hqs : dbq p (C.queries.get g₂) ≤ size p := prefix_sizel _ _
        refine ⟨rfl, grL_Cq_right he _, ?_, hR, hinv, h0, hall⟩
        rw [max_eq_right (by omega)] at hc
        dsimp only
        omega
      case body =>
        stmt_wp
        equiv_if
        case guard =>
          rintro g₁ g₂ p i sa sc p' bs i' sa' sc' ⟨⟨rfl, -, rfl, -, -, -, hR, -⟩, -⟩
          rw [hR]
        case «then» =>
          stmt_wp
          equiv_skip
          rintro g₁ g₂ p i sa sc p' bs i' sa' sc'
            ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, he, hR, hc, hnq, hL⟩, hg⟩, hg1⟩
          simp only [decide_eq_true_eq] at hg hg1
          obtain ⟨hle, hL'⟩ := grLoop_read _ _ _ _ _ _ hL hg (hR ▸ hg1)
          refine ⟨rfl, rfl, rfl, by rw [hR], by rw [hR], he, hR, by omega, hnq, hR ▸ hL'⟩
        case «else» =>
          stmt_wp
          refine prhlStmt_fix_left (fun σ => grL.get σ.globals) (fun u => ?_)
          refine prhlStmt_fix_right (fun σ => grL.get σ.globals) (fun v => ?_)
          equiv_seq_last 1 1 : (§x0{1} = (§sa{2}, §sc{2}) ∧ §p{1} = §p{2} ∧ §p{2} = §bs{2} ∧
              §i{1} = §i{2} ∧ grL.equal_outside §allGlobals{1} §allGlobals{2} ∧
              grL.get §allGlobals{1} = u ∧ grL.get §allGlobals{2} = v ∧
              §Redo.prefixes{1} = §Redo.prefixes{2} ∧
              §C.c{1} + 1 = §C.c{2} - (size §p{2} - dbq §p{2} §C.queries{2}) +
                max 0 (§i{2} + 1 - dbq §p{2} §C.queries{2}) ∧
              ¬ FMap.dom §C.queries{2} §p{2} ∧
              ∀ w : state, grLoop §C.queries{2}
                (FMap.set §Redo.prefixes{2} (take (§i{2} + 1) §p{2}) w) §p{2} (§i{2} + 1) w.1 w.2)
          · stmt_wp
            equiv_skip
            rintro g₁ g₂ p i sa sc p' bs i' sa' sc'
              ⟨⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, he, hR, hc, hnq, hL⟩, hg⟩, hg1⟩, hu⟩, hv⟩
            simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hg hg1
            rw [hR] at hg1
            obtain ⟨hle, hL'⟩ := grLoop_call _ _ _ _ _ _ hL hg hg1
            exact ⟨rfl, rfl, rfl, rfl, he, hu, hv, hR, by omega, hnq, hL'⟩
          · equiv_call (prhlProc_self_equal_outside_module grL _ hPf (fun x y => x = u ∧ y = v))
            equiv_skip
            rintro g₁ g₂ x0 p i sa sc p' bs i' ⟨rfl, rfl, rfl, rfl, he, hu, hv, hR, hc, hnq, hL⟩
            refine ⟨⟨rfl, he, hu, hv⟩, ?_⟩
            rintro r g₁' r' g₂' ⟨rfl, he', hu', hv'⟩
            have h1 := hu'.trans hu.symm
            have h2 := hv'.trans hv.symm
            have c1 : C.c.get g₁' = C.c.get g₁ := congrArg Prod.fst h1
            have r1 : Redo.prefixes.get g₁' = Redo.prefixes.get g₁ := congrArg (fun t => t.2.2) h1
            have c2 : C.c.get g₂' = C.c.get g₂ := congrArg Prod.fst h2
            have q2 : C.queries.get g₂' = C.queries.get g₂ := congrArg (fun t => t.2.1) h2
            have r2 : Redo.prefixes.get g₂' = Redo.prefixes.get g₂ := congrArg (fun t => t.2.2) h2
            refine ⟨rfl, rfl, rfl, rfl, rfl, grL_R_left (grL_R_right (grL_Cc_left he' _) _) _,
              by rw [r1, r2, hR], by rw [c1, c2, q2]; exact hc, by rw [q2]; exact hnq, ?_⟩
            rw [q2, r2]
            exact hL r
      stmt_wp
      equiv_skip
      rintro g₁ g₂ p sa sc i bs b ⟨⟨rfl, rfl, rfl, rfl, -, he, hI⟩, hg⟩
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hg
      obtain ⟨hc, hR, hinv, h0, hall⟩ := hI
      dsimp only at hc hR hinv h0 hall
      have hq0 : 0 ≤ dbq p (C.queries.get g₂) := prefix_ge0 _ _
      have hqe : dbq p (C.queries.get g₂) =
          «prefix» p (get_max_prefix p (FSet.elems (C.queries.get g₂).fdom)) := rfl
      refine ⟨rfl, rfl, rfl, rfl, grL_Cc_right he _, hR, by omega, hg,
        grLoop_init _ _ _ hinv h0 hall⟩
    case «else» =>
      stmt_wp
      equiv_while_noframe{1} (§p{1} = §bs{2} ∧ FMap.dom §C.queries{2} §bs{2} ∧
          grL.equal_outside §allGlobals{1} §allGlobals{2} ∧
          grI (grL.get §allGlobals{1}) (grL.get §allGlobals{2}) ∧
          0 ≤ §i{1} ∧ §i{1} ≤ size §p{1} ∧
          FMap.get §Redo.prefixes{1} (take §i{1} §p{1}) = some (§sa{1}, §sc{1}))
        ((size §p{1} - §i{1}).toNat)
      case lossless =>
        intro σ₂ σ hI hg
        simp only [eval_lens_full, eval_lens_global] at hI hg
        obtain ⟨hp, hdq, -, hI, -⟩ := hI
        have hd := grI_dom hI hdq ((localVarLens "i" ℤ).get σ + 1)
        rw [← hp] at hd
        have hd' : FMap.dom (Redo.prefixes.get σ.globals)
            (take ((localVarLens "i" ℤ).get σ + 1) ((localVarLens "p" (List block)).get σ)) := hd
        simp only [Stmt.ewp_seq, Stmt.ewp_assign, Stmt.ewp_ifThenElse, eval_lens_full,
          eval_lens_global, hd', decide_true, if_true]
      case «variant» =>
        intro σ₂ k
        hoare_wp 1
        refine hoare_pre (hoare_if_wp (hoare_assign_wp _ _ _) hoare_false') ?_
        intro σ ⟨⟨hp, hdq, he, hI, hi0, hip, hget⟩, hg, hk⟩
        simp only [eval_lens_full, eval_lens_global] at hp hdq he hI hi0 hip hget hg hk
        have hd := grI_dom hI hdq ((localVarLens "i" ℤ).get σ + 1)
        rw [← hp] at hd
        have hd' : FMap.dom (Redo.prefixes.get σ.globals)
            (take ((localVarLens "i" ℤ).get σ + 1) ((localVarLens "p" (List block)).get σ)) := hd
        refine ⟨fun _ => ?_, fun hc => ?_⟩
        · simp_reads
          simp only [decide_eq_true_eq] at hg
          obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).1 hd')
          refine ⟨⟨hp, hdq, he, hI, by omega, by omega, by rw [hw]; rfl⟩, by omega⟩
        · simp only [eval_lens_full, eval_lens_global] at hc
          simp [hd'] at hc
      case exit =>
        rintro g₂ g₁ bs p i sa sc ⟨rfl, hdq, he, hI, hi0, hip, hget⟩ hg
        simp only [decide_eq_false_iff_not, not_lt] at hg
        obtain rfl : i = size p := by omega
        rw [take_size] at hget
        refine ⟨?_, he, hI⟩
        have h1 := hI.2.2.1.1 p hdq
        have h2 : Redo.prefixes.get g₁ = Redo.prefixes.get g₂ := hI.2.1
        change oget ((C.queries.get g₂).get p) = (oget ((Redo.prefixes.get g₂).get p)).1 at h1
        rw [h1, ← h2, hget]
        rfl
      equiv_skip
      rintro g₁ g₂ p sa sc i bs b ⟨⟨rfl, rfl, rfl, rfl, -, he, hI⟩, hg⟩
      simp only [Bool.not_eq_false', decide_eq_true_eq] at hg
      have h2 : Redo.prefixes.get g₁ = Redo.prefixes.get g₂ := hI.2.1
      refine ⟨rfl, hg, he, hI, le_rfl, by simp [size], ?_⟩
      rw [show take 0 p = [] by simp [take], h2]
      exact hI.2.2.2.1

/-- The first step of EC's `Real_Concrete` (its `have ->:`): counting the queries of
`SqueezelessSponge(PC(Perm))` block by block, or by `FC` on the new blocks of each fresh query,
gives the same `C.c` (EC: `byequiv; proc; inline *; call (_: ={C.c, glob Perm, Redo.prefixes} /\
prefix_inv C.queries{2} Redo.prefixes{1} /\ Redo.prefixes{1}.[[]] = Some (b0, c0) /\
all_prefixes Redo.prefixes{1})`). -/
theorem GReal_GReal' (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ ((Perm.m).footprint ⊔
      (Perm.mi).footprint ⊔ C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔
      (Redo.prefixes).footprint)ᶜ)
    (m : VariableAssignment) :
    Procedure.Pr (GReal D).procedure () m (fun r g => r = true ∧ C.c.get g ≤ max_size) =
      Procedure.Pr (GReal' D).procedure () m (fun r g => r = true ∧ C.c.get g ≤ max_size) := by
  unfold C.footprint at _hDd
  have hdisj : FVP.fvP D ≤ (grL.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [grL, Footprint.lens_pair]
    refine sup_le ?_ (sup_le ?_ ?_) <;>
    exact (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_sub)))
  have hP := fvP_Perm_grL
  have hPq : FVP.fvP Perm ≤ (C.queries.footprint)ᶜ :=
    fvP_Perm.trans (Lens.footprint_le_compl_of_disjoint _ _)
  refine Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
    (B := fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ C.c.get g₁ = C.c.get g₂) ?_
    (fun r₁ g₁ r₂ g₂ h => by rw [h.1, h.2]) rfl
  unfold GReal GReal' RealIndif Indifferentiability.GReal
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  repeat stmt_inline{1} 1
  repeat stmt_inline{2} 1
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (grL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      grI (grL.get §allGlobals{1}) (grL.get §allGlobals{2}))
  · stmt_wp
    equiv_call_frame C.queries
    stmt_wp
    equiv_skip
    intro σ₁ σ₂ hg
    refine ⟨by rw [hg], fun r g hq => ?_⟩
    simp only [Setter.throwaway, ProgramState.globalL]
    rw [hq]
    exact ⟨Lens.equal_outside.refl _, grI_init _⟩
  · have hcall := prhlProc_abstract_call_equal_outside_module grL D
      distExt hD.representable hdisj grI (fun n => by
        cases n with
        | zero => exact inferInstanceAs (Countable (List block))
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable state)
          | succ n => cases n with
            | zero => exact inferInstanceAs (Countable state)
            | succ n => nomatch n)
      (Module.pair (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
          { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
              (Module.app SqueezelessSponge
                (Indifferentiability.PRIMITIVE.view state (List block) block
                  (Module.app PC Perm))) })
        (Indifferentiability.DPRIMITIVE.mk state (List block) block
          { f := Indifferentiability.PRIMITIVE.f state (List block) block (Module.app PC Perm),
            fi := Indifferentiability.PRIMITIVE.fi state (List block) block
              (Module.app PC Perm) }))
      (Module.pair (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
          { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
              (Module.app FC (Module.app SqueezelessSponge
                (Indifferentiability.PRIMITIVE.view state (List block) block Perm))) })
        (Indifferentiability.DPRIMITIVE.mk state (List block) block
          { f := Indifferentiability.PRIMITIVE.f state (List block) block (Module.app PC Perm),
            fi := Indifferentiability.PRIMITIVE.fi state (List block) block
              (Module.app PC Perm) }))
      (fun n => by
        cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
            Module.fst_pair, Indifferentiability.DFUNCTIONALITY.f.mk_simp]
          exact GR_F_f
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_cons, Module.snd_pair,
              Indifferentiability.DPRIMITIVE.f.mk_simp]
            exact GR_P_f
          | succ n => cases n with
            | zero =>
              simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
                HoleSigs.Instantiation.lookup_zero_single, Module.snd_pair,
                Indifferentiability.DPRIMITIVE.fi.mk_simp]
              exact GR_P_fi
            | succ n => nomatch n)
    equiv_call hcall
    equiv_skip
    exact fun _ _ h => ⟨h, fun _ _ _ _ h' => ⟨h'.1, h'.2.2.1⟩⟩

/-- `SqueezelessSponge` touches `Redo.prefixes`.  Not an EC lemma. -/
@[fp_bound] theorem fvP_SqueezelessSponge :
    FVP.fvP SqueezelessSponge ≤ Redo.prefixes.footprint := by
  fp_module Redo.prefixes

/-- `SqueezelessSponge(O)` touches `Redo.prefixes` and `O`'s variables.  Not an EC lemma. -/
@[fp_bound] theorem fvP_SqueezelessSponge_app (O : DPRIMITIVE) :
    FVP.fvP (Module.app SqueezelessSponge O) ≤ Redo.prefixes.footprint ⊔ FVP.fvP O :=
  (FVP.fvP_app _ _).trans (sup_le_sup_right fvP_SqueezelessSponge _)

/-- `DFRestr(F).f` is lossless when `F.f` is: `rf_ll` without `{-C}`, which its proof does not
use.  Not an EC lemma (EC proves it inline in `CF_G1`). -/
theorem rf_ll' (F : DFUNCTIONALITY) :
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

/-- `SqueezelessSponge(O)` as `DFUNCTIONALITY` is its view. -/
theorem view_SS_eq (O : DPRIMITIVE) :
    Indifferentiability.FUNCTIONALITY.view state (List block) block
        (Module.app SqueezelessSponge O) =
      Indifferentiability.DFUNCTIONALITY.mk state (List block) block
        { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
            (Module.app SqueezelessSponge O) } := rfl

/-- EC's `islossless D'(D).distinguish` (inline in `Real_Concrete`, for `Conclusion D'`): from
`D_ll` over a region `G` outside `C` and `Redo`, for lossless oracles outside `G` and `C`. -/
theorem D'_ll (D : DISTINGUISHER) (G : Footprint VariableAssignment)
    (_hCG : G ≤ (C.footprint ⊔ Redo.prefixes.footprint)ᶜ)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ Gᶜ →
      FVP.fvP P ≤ Gᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless)
    (O : Switching.PRPSec.SPRP_Oracles) (_hOG : FVP.fvP O ≤ Gᶜ)
    (_hOC : FVP.fvP O ≤ C.footprintᶜ)
    (f_ll : (PRP.StrongPRP.SPRP_Oracles.f state O).procedure.IsLossless)
    (fi_ll : (PRP.StrongPRP.SPRP_Oracles.fi state O).procedure.IsLossless) :
    (Module.app (D' D) O).procedure.IsLossless := by
  have hll := D_ll (Module.app DFRestr (Indifferentiability.FUNCTIONALITY.view state (List block)
      block (Module.app SqueezelessSponge O))) (Module.app DPRestr O) (by fp_disjoint)
    (by fp_disjoint)
    (rp_ll O (by fp_disjoint) f_ll) (rpi_ll O (by fp_disjoint) fi_ll)
    (rf_ll' _ (by
      rw [Indifferentiability.FUNCTIONALITY.view_f]
      exact SqueezelessSponge_f_ll O f_ll))
  rw [Procedure.isLossless_iff_phoareProc] at hll ⊢
  phoare_proc_to_stmt
  repeat phoare_inline 0
  rw [← view_SS_eq]
  phoare_wp 10
  phoare_simp [hll]
  phoare_skip
  simp

/-- `Perm` touches `Perm.m` and `Perm.mi` (the joined form of `fvP_Perm`). -/
@[fp_bound] theorem fvP_Perm_sup : FVP.fvP Perm ≤ (Perm.m).footprint ⊔ (Perm.mi).footprint := by
  simpa only [Footprint.lens_pair] using fvP_Perm

/-- EC's `p_ll := f_ll _` (`RP`'s `f_ll`: `dstate` is full).  `Perm.f` samples from
`dstate \ rng Perm.m`, lossless since `Perm.m` misses the queried key (`excepted_lossless`). -/
theorem Perm_f_ll :
    (Indifferentiability.PRIMITIVE.f state (List block) block Perm).procedure.IsLossless := by
  rw [← Indifferentiability.PRIMITIVE.view_f, view_Perm_eq, dprim_f_mk,
    Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  rename_i σ _
  split_ifs with hd
  · rfl
  · have h2 := (is_lossless_iff_expected _).mp
      (Strong_RP_RF.excepted_lossless state dstate Switching.uD_uf_fu (Perm.m.get σ.globals)
        ⟨_, hd⟩)
    simp [h2]

/-- EC's `pi_ll := fi_ll _` (as `Perm_f_ll`). -/
theorem Perm_fi_ll :
    (Indifferentiability.PRIMITIVE.fi state (List block) block Perm).procedure.IsLossless := by
  rw [← Indifferentiability.PRIMITIVE.view_fi, view_Perm_eq, dprim_fi_mk,
    Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_ewp
  rename_i σ _
  split_ifs with hd
  · rfl
  · have h2 := (is_lossless_iff_expected _).mp
      (Strong_RP_RF.excepted_lossless state dstate Switching.uD_uf_fu (Perm.mi.get σ.globals)
        ⟨_, hd⟩)
    simp [h2]

set_option maxHeartbeats 2000000 in
/-- `PF` touches `PF.m` and `PF.mi`.  Not an EC lemma. -/
theorem fvP_PF : FVP.fvP PF ≤ (Lens.pair PF.m PF.mi).footprint := by
  fp_module (Lens.pair PF.m PF.mi)

set_option maxHeartbeats 4000000 in
/-- `D'(D)` touches `D`'s variables, `C`'s and `Redo.prefixes`.  Not an EC lemma. -/
theorem fvP_D' (D : DISTINGUISHER) : FVP.fvP (D' D) ≤
    FVP.fvP D ⊔ (Lens.pair C.c (Lens.pair C.queries Redo.prefixes)).footprint := by
  fp_module (Lens.pair C.c (Lens.pair C.queries Redo.prefixes))

/-- EC's `Real_Concrete`, for `declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo}` with
the axiom `D_ll` (over a region `G` outside the restrictions, `G` inside the `glob` of a finitely
supported `GF`, exception E14).  The local clone's module variables `DBounder.FBounder.c` and
`ARP.coll` are fresh lenses (exception E6).
`mu dstate (pred1 witness)` is the probability of `default`. -/
theorem Real_Concrete (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ ((Perm.m).footprint ⊔
      (Perm.mi).footprint ⊔ C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔
      (Redo.prefixes).footprint)ᶜ)
    (G : Footprint VariableAssignment)
    (_hGd : G ≤ ((Perm.m).footprint ⊔
      (Perm.mi).footprint ⊔ C.footprint ⊔ (PF.m).footprint ⊔ (PF.mi).footprint ⊔
      (Redo.prefixes).footprint)ᶜ)
    (GF : Footprint VariableAssignment) (hGF : GF.FinitelySupported) (hGGF : G ≤ GF.glob)
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
  have fsv : ∀ {T : Type} (x : Lens T VariableAssignment) {v : VariableName}
      [Lens.IsGlobalVar x v], x.footprint.FinitelySupported :=
    fun x => Footprint.FinitelySupported.globalVar x
  have hDfs := hD.finitelySupported
  have hCfs : C.footprint.FinitelySupported := (fsv _).sup (fsv _)
  have hRedofs := Footprint.FinitelySupported.globalVar Redo.prefixes
  have hRfs : ((Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ C.footprint ⊔ (PF.m).footprint ⊔
      (PF.mi).footprint ⊔ (Redo.prefixes).footprint).FinitelySupported :=
    (((((fsv _).sup (fsv _)).sup hCfs).sup (fsv _)).sup (fsv _)).sup
      hRedofs
  -- `DBounder.FBounder.c` and `ARP.coll`, fresh (exception E6)
  obtain ⟨c, hcg, hc, hcfs⟩ := Footprint.exists_fresh_glob ℤ hGF (hDfs.sup hRfs)
  obtain ⟨coll, hcollg, hcoll, hcollfs⟩ :=
    Footprint.exists_fresh_glob Bool hGF ((hDfs.sup hRfs).sup hcfs)
  have hDc : FVP.fvP D ≤ c.footprintᶜ := (Footprint.le_compl_comm _ _).mp
    (hc.trans (Footprint.compl_antimono (le_sup_left.trans le_sup_right)))
  have hDcoll : FVP.fvP D ≤ coll.footprintᶜ := (Footprint.le_compl_comm _ _).mp
    (hcoll.trans (Footprint.compl_antimono
      (le_sup_left.trans (le_sup_left.trans le_sup_right))))
  have hcG : G ≤ c.footprintᶜ := hGGF.trans ((Footprint.le_compl_comm _ _).mp hcg)
  have hcollG : G ≤ coll.footprintᶜ := hGGF.trans ((Footprint.le_compl_comm _ _).mp hcollg)
  haveI : Lens.Disjoint c Perm.m := Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint c Perm.mi := Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint c PF.m := Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint c PF.mi := Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint c C.c := Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint c C.queries := Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint c Redo.prefixes :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint coll c := Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint coll PF.m := Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint coll PF.mi := Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint coll Perm.m := Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint coll Perm.mi := Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint coll C.c := Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint coll C.queries :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint coll Redo.prefixes :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI := (inferInstance : Lens.Disjoint coll C.c).symm
  haveI := (inferInstance : Lens.Disjoint coll C.queries).symm
  haveI := (inferInstance : Lens.Disjoint coll Redo.prefixes).symm
  haveI := (inferInstance : Lens.Disjoint coll c).symm
  haveI := (inferInstance : Lens.Disjoint coll PF.m).symm
  haveI := (inferInstance : Lens.Disjoint coll PF.mi).symm
  haveI := (inferInstance : Lens.Disjoint coll Perm.m).symm
  haveI := (inferInstance : Lens.Disjoint coll Perm.mi).symm
  have hfresh : c.footprint ≤ (FVP.fvP D ⊔ C.footprint ⊔ (Redo.prefixes).footprint)ᶜ :=
    hc.trans (Footprint.compl_antimono (by fp_sub))
  have hPerm : FVP.fvP Perm ≤ (Perm.m).footprint ⊔ (Perm.mi).footprint := by
    simpa only [Footprint.lens_pair] using fvP_Perm
  have hPF : FVP.fvP PF ≤ (PF.m).footprint ⊔ (PF.mi).footprint := by
    simpa only [Footprint.lens_pair] using fvP_PF
  have hPermfs : (FVP.fvP Perm).FinitelySupported :=
    Footprint.FinitelySupported.mono hPerm ((fsv _).sup (fsv _))
  have hSSfs : (FVP.fvP SqueezelessSponge).FinitelySupported :=
    Footprint.FinitelySupported.mono fvP_SqueezelessSponge hRedofs
  have hCG : G ≤ C.footprintᶜ :=
    _hGd.trans (Footprint.compl_antimono (by fp_sub))
  have hCRG : G ≤ (C.footprint ⊔ (Redo.prefixes).footprint)ᶜ :=
    _hGd.trans (Footprint.compl_antimono (by fp_sub))
  -- `GReal ~ GReal'`
  have h1 := GReal_GReal' D hD _hDd m
  -- `Pr_restr Perm SqueezelessSponge D p_ll pi_ll f_ll D_ll`
  have hCO : FVP.fvP SqueezelessSponge ≤ (C.footprint ⊔ (FVP.fvP Perm).glob)ᶜ :=
    fvP_SqueezelessSponge.trans ((Footprint.le_compl_comm _ _).mpr (sup_le (by fp_disjoint)
      ((Footprint.le_compl_comm _ _).mp (Footprint.globalVar_le_compl_glob hPermfs Redo.prefixes
        (hPerm.trans (by fp_disjoint))))))
  have hDPC : FVP.fvP D ≤ (C.footprint ⊔ (FVP.fvP Perm).glob ⊔
      (FVP.fvP SqueezelessSponge).glob)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr (sup_le (sup_le ?_ ?_) ?_)
    · exact (Footprint.le_compl_comm _ _).mp (by fp_disjoint)
    · exact (Footprint.le_compl_comm _ _).mp (Footprint.le_compl_glob_symm hPermfs
        (hPerm.trans (by fp_disjoint)))
    · exact (Footprint.le_compl_comm _ _).mp (Footprint.le_compl_glob_symm hSSfs
        (fvP_SqueezelessSponge.trans (by fp_disjoint)))
  have h2 := Pr_restr_of_region Perm SqueezelessSponge D hD
    (hPerm.trans (by unfold C.footprint; fp_disjoint)) hCO hDPC
    Perm_f_ll Perm_fi_ll
    (SqueezelessSponge_f_ll _ (by rw [Indifferentiability.PRIMITIVE.view_f]; exact Perm_f_ll))
    G (by fp_disjoint) (by fp_disjoint) hCG D_ll m
  -- `Indif(SqueezelessSponge(Perm), Perm, DRestr(D)) = PRPSec.IND(PRPi.PRPi, D'(D))`, then
  -- `DoubleBounding PRPi.PRPi`
  have h3 := Indif_IND_Perm D m
  have hPRPi : FVP.fvP (Switching.PRPi.PRPi Perm.m Perm.mi) ≤ ((FVP.fvP D).glob ⊔
      C.footprint ⊔ c.footprint ⊔ (Redo.prefixes).footprint)ᶜ :=
    (hPerm : FVP.fvP (Switching.PRPi.PRPi Perm.m Perm.mi) ≤ _).trans
      (by unfold C.footprint; fp_disjoint)
  have h4 := DoubleBounding D hD _hDd c hfresh _ hPRPi m
  -- `CF(DRestr(D)) = PRPSec.IND(PF, D'(D))`, `DoubleBounding PF`
  have h8 := CF_IND_PF D m
  have hPFb : FVP.fvP (PF : Switching.PRPSec.PRP) ≤ ((FVP.fvP D).glob ⊔
      C.footprint ⊔ c.footprint ⊔ (Redo.prefixes).footprint)ᶜ :=
    (hPF : FVP.fvP (PF : Switching.PRPSec.PRP) ≤ _).trans (by unfold C.footprint; fp_disjoint)
  have h7 := DoubleBounding D hD _hDd c hfresh _ hPFb m
  -- `PRPSec.IND(ARP, DBounder(D')) = PRPSec.IND(PF, DBounder(D'))` (`ARP.m = PF.m`, …)
  have hDB : FVP.fvP (Switching.DBounder c (D' D)) ≤ coll.footprintᶜ :=
    (Strong_RP_RF.fvP_DBounder state max_size c (D' D)).trans (sup_le ((fvP_D' D).trans
      (by simp only [Footprint.lens_pair]; fp_disjoint)) (by fp_disjoint))
  have h6 : Procedure.Pr (Module.app Switching.PRPSec.IND (Module.pair
        (Switching.ARP coll PF.m PF.mi) (Switching.DBounder c (D' D)))).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (Module.app Switching.PRPSec.IND (Module.pair (PF : Switching.PRPSec.PRP)
        (Switching.DBounder c (D' D)))).procedure () m (fun r _ => r = true) :=
    Procedure.Pr_eq_of_prhlProc (A := fun _ g₁ _ g₂ => g₁ = g₂)
      (B := fun r₁ _ r₂ _ => r₁ = r₂) (IND_ARP_PF coll _ hDB)
      (fun r₁ g₁ r₂ g₂ h => by rw [h]) rfl
  -- `Conclusion D'`, over `G ⊔ (glob D ⊔ C ⊔ Redo)` (exception E14)
  have hXfs := (hDfs.sup hCfs).sup hRedofs
  have hD'fs : (FVP.fvP (D' D)).FinitelySupported :=
    Footprint.FinitelySupported.mono (fvP_D' D) (hDfs.sup (by
      simp only [Footprint.lens_pair]; exact (fsv _).sup ((fsv _).sup (fsv _))))
  have hfs : ((Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ coll.footprint ⊔ (PF.m).footprint ⊔
      (PF.mi).footprint ⊔ c.footprint).FinitelySupported :=
    (((((fsv _).sup (fsv _)).sup hcollfs).sup (fsv _)).sup (fsv _)).sup
      hcfs
  have hRG := (Footprint.le_compl_comm _ _).mp _hGd
  have hYD : (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ coll.footprint ⊔ (PF.m).footprint ⊔
      (PF.mi).footprint ⊔ c.footprint ≤ (FVP.fvP D)ᶜ := by
    refine sup_le (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_) ?_ <;>
    refine (Footprint.le_compl_comm _ _).mp ?_ <;> fp_disjoint
  have hG' : G ⊔ (FVP.fvP D ⊔ C.footprint ⊔ (Redo.prefixes).footprint) ≤
      ((Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ coll.footprint ⊔ (PF.m).footprint ⊔
        (PF.mi).footprint ⊔ c.footprint)ᶜ := by
    refine sup_le ((Footprint.le_compl_comm _ _).mpr ?_) (sup_le (sup_le
      ((Footprint.le_compl_comm _ _).mpr hYD) (by unfold C.footprint; fp_disjoint))
      (by fp_disjoint))
    refine sup_le (sup_le (sup_le (sup_le (sup_le ?_ ?_)
      ((Footprint.le_compl_comm _ _).mp hcollG)) ?_) ?_) ((Footprint.le_compl_comm _ _).mp hcG)
    all_goals exact le_trans (by fp_sub) hRG
  have h5 := Strong_RP_RF.Conclusion_of_region state dstate max_size Switching.uD_uf_fu
    Perm.m Perm.mi PF.m PF.mi coll c hfs (D' D) hD'fs
    (G ⊔ (FVP.fvP D ⊔ C.footprint ⊔ (Redo.prefixes).footprint))
    (GF ⊔ (FVP.fvP D ⊔ C.footprint ⊔ (Redo.prefixes).footprint)) (hGF.sup hXfs)
    (sup_le (hGGF.trans (Footprint.glob_mono le_sup_left))
      (Footprint.le_glob_of_le le_sup_right))
    ((fvP_D' D).trans (by simp only [Footprint.lens_pair]; unfold C.footprint; fp_sub))
    hG' m
    (fun O _ hO hf hfi => D'_ll D G hCRG D_ll O (hO.trans (Footprint.compl_antimono le_sup_left))
      (hO.trans (Footprint.compl_antimono (by fp_mem))) hf hfi)
  -- `smt()`
  rw [h1, h8, h7, ← h6]
  have h2' : (Procedure.Pr (GReal' D).procedure () m
      (fun r g => r = true ∧ C.c.get g ≤ max_size) : ℝ) ≤
      (Procedure.Pr (Module.app Switching.PRPSec.IND (Module.pair
        (Switching.PRPi.PRPi Perm.m Perm.mi) (Switching.DBounder c (D' D)))).procedure () m
        (fun r _ => r = true) : ℝ) := by
    rw [← h4, ← h3]; exact_mod_cast h2
  have := (abs_sub_le_iff.mp h5).1
  linarith

end

end GaudisCrypt.SHA3.ConcreteF
