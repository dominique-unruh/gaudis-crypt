import GaudisCrypt.Examples.SHA3.SHA3_OIndiff
import GaudisCrypt.Examples.SHA3.SecureORO
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Lib.EC.DList
import GaudisCrypt.Lib.EC.DListCall
import GaudisCrypt.Logic.FootprintUpper
import GaudisCrypt.Logic.PRHLFrame

/-!
# Top-level proof of SHA-3 security with failing oracles (EasyCrypt `proof/SHA3OSecurity.ec`)

Preimage, second-preimage and collision resistance of the sponge with outputs of `size_out` bits
(`OSponge`) in `SecureHash`'s games, against adversaries making `sigma` queries.  Each proof goes
through `SHA3_OIndiff` and the resistance of the random oracle (`SecureORO`).

Translation notes (see `notes/SHA3/README.md`):
* The file-level abstract type `f_out`, operators `size_out`, `dout`, `to_list`, `of_list` and the
  axioms (including `sigma_ge0`, an axiom about the defined `sigma`) are the parameter class
  `Params`, as in `SHA3Security`.
* Name resolution follows EasyCrypt's (checked with `print`): unqualified `OFUNCTIONALITY` …
  are `SHA3_OIndiff.OIndif`'s; `OIndif.X` is `SH.OIndif.X` (the clone `SH` comes later); `Oracle`
  and `RF` are `SORO`'s; `RO`, `FRO`, `LRO` are `Eager`'s.
* `clone import SecureORO as SORO`, `clone import SecureHash as SH`, `clone import FullRO as Eager`
  are namespaces of abbreviations that declare the clones' module variables; their `realize`s are
  `SORO.axioms`, `SH.axioms`.
* `FSetSize` and `ExtendOutput` have `proc get = f`, a procedure outside their type: it is
  `FSetSize.get`, the same procedure as `FSetSize.f` (an abbreviation).  Their aliases of a
  parameter's procedures are wrapped in a call (exception E5), as in the sections' `FInit`,
  `PInit`, `OF`, `ExtendSample`, `Fill_In` and `Dist`.  `OSponge(P) = FSetSize(CSome(Sponge, P))`
  is `Module.comp FSetSize (CSome Sponge)`; `OFC2(F) = OFC(ExtendOutputSize(F))` is
  `Module.comp OFC ExtendOutputSize`, written out where it is called inside a module body.
* The sections' local modules have variables (`Log.m`, `RFList.m`, `Dist_of_P2Adv.m`): lens
  parameters of the local declarations, with freshness hypotheses (`LocalFresh`, exception E6).
  `Log` has only its variable, so it is that lens alone.  The sections' local declarations go into
  namespaces named after the sections.
* `Dist(F)` is used as an `RO_Distinguisher` (`RO_LRO_D Dist`): its `distinguish` takes `Unit`.
* `OIndif(F, OSimulator(F), D)` (from `SHA3_OIndiff`) is written `IdealGame F D`.
-/

-- EasyCrypt's clones contain modules named like them (`SORO.RO.RO`, `SH.OIndif` …); kept (E1)
set_option linter.dupNamespace false
-- the parameter classes are section variables of every declaration, used or not
set_option linter.unusedSectionVars false

namespace GaudisCrypt.SHA3.SHA3OSecurity

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.Sponge GaudisCrypt.SHA3.Sponge.BIRO
open GaudisCrypt.SHA3.SHA3Indiff GaudisCrypt.SHA3.SHA3_OIndiff GaudisCrypt.SHA3.SHA3_OIndiff.OIndif

-- the last imports (`Sponge`, `SHA3_OIndiff`) win over `Common`'s and the root-level names
export GaudisCrypt.SHA3.SHA3_OIndiff (state PRIMITIVE)

variable [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params]

/-- EasyCrypt's file-level abstract type and operators, with their axioms: `op size_out` with
`size_out_gt0`, `axiom sigma_ge0`, `type f_out`, `op dout` with `dout_ll`, `dout_fu`, `dout_full`,
`op to_list`, `op of_list` with `spec_dout`, `spec2_dout`, `to_list_inj`, `to_listK` and
`dout_equal_dlist`. -/
class Params : Type 1 where
  size_out : ℤ
  size_out_gt0 : 0 < size_out
  sigma_ge0 : 0 ≤ SHA3Indiff.limit
  f_out : Type
  f_out_inhabited : Inhabited f_out
  dout : SubProbability f_out
  dout_ll : is_lossless dout
  dout_fu : is_funiform dout
  dout_full : is_full dout
  to_list : f_out → List Bool
  of_list : List Bool → Option f_out
  spec_dout : ∀ l, size (to_list l) = size_out
  spec2_dout : ∀ l, size l = size_out → of_list l ≠ none
  to_list_inj : Function.Injective to_list
  to_listK : ∀ e l, to_list e = l ↔ of_list l = some e
  dout_equal_dlist : (dout >>= fun x => pure (to_list x)) = dlist dbool size_out

variable [Params]

def size_out : ℤ := Params.size_out
/-- `op sigma : int = SHA3Indiff.limit`. -/
def sigma : ℤ := SHA3Indiff.limit
abbrev f_out : Type := Params.f_out
instance : Inhabited f_out := Params.f_out_inhabited
noncomputable def dout : SubProbability f_out := Params.dout
def to_list : f_out → List Bool := Params.to_list
def of_list : List Bool → Option f_out := Params.of_list

theorem doutE1 (x : f_out) : (dout.1 {x}).toReal = ((2 : ℝ) ^ size_out)⁻¹ := by
  have hlen : ((to_list x).length : ℤ) = size_out := Params.spec_dout x
  have h := map_mu1_inj dout Params.to_list_inj x
  change (Params.dout >>= fun a => (pure (Params.to_list a) : SubProbability _)).1
    {Params.to_list x} = _ at h
  rw [Params.dout_equal_dlist, dlist1E _ _ (Params.to_list x) (Params.spec_dout x)] at h
  change _ = dout.1 {x} at h
  rw [← h]
  simp only [dbool1E, List.map_const', List.prod_replicate, ENNReal.toReal_pow,
    ENNReal.toReal_inv]
  have hl : ((Params.to_list x).length : ℤ) = size_out := hlen
  rw [← zpow_natCast, hl, ENNReal.toReal_ofNat, inv_zpow]

/-! ## `clone import SecureHash as SH with type from <- bool list, type to <- f_out,
type block <- state, op sampleto <- dout, op bound <- sigma, op increase_counter <- …` -/

namespace SH
namespace OIndif
abbrev OPRIMITIVE := OptionIndifferentiability.OPRIMITIVE state (List Bool) f_out
abbrev ODPRIMITIVE := OptionIndifferentiability.ODPRIMITIVE state (List Bool) f_out
abbrev OFUNCTIONALITY := OptionIndifferentiability.OFUNCTIONALITY state (List Bool) f_out
abbrev ODFUNCTIONALITY := OptionIndifferentiability.ODFUNCTIONALITY state (List Bool) f_out
abbrev OCONSTRUCTION := OptionIndifferentiability.OCONSTRUCTION state (List Bool) f_out
end OIndif
end SH

/-- `FSome` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_FSome : FVP.fvP FSome ≤ ⊥ := by
  fp_module

/-- `Poget` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_Poget : FVP.fvP Poget ≤ ⊥ := by
  fp_module

/-- `PSome`'s `f` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_PSome_own_f : FVP.fvP PSome.own.f ≤ ⊥ := by
  fp_module

/-- `PSome`'s `fi` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_PSome_own_fi : FVP.fvP PSome.own.fi ≤ ⊥ := by
  fp_module

/-- `Sponge` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_Sponge : FVP.fvP Sponge.Sponge ≤ ⊥ := by
  fp_module

/-! `clone import Program as PBool with type t <- bool, op d <- dbool` -/

namespace PBool
noncomputable abbrev LoopSnoc.sample := DList.Program.LoopSnoc.sample Bool dbool
end PBool

/-! `clone import FullRO as Eager with type in_t <- bool list * int, type out_t <- bool,
op dout _ <- dbool, type d_in_t <- unit, type d_out_t <- bool` -/

namespace Eager
/-- The clone's module variables. -/
global_var RO.m : FMap (List Bool × ℤ) Bool
global_var FRO.m : FMap (List Bool × ℤ) (Bool × flag)
abbrev RO_T := PROM.FullRO.RO_T (List Bool × ℤ) Bool
abbrev RO_Distinguisher := PROM.FullRO.RO_Distinguisher (List Bool × ℤ) Bool Unit Bool
noncomputable abbrev RO := PROM.FullRO.RO.asRO (List Bool × ℤ) Bool (fun _ => dbool) RO.m
noncomputable abbrev LRO := PROM.FullRO.LRO (List Bool × ℤ) Bool (fun _ => dbool) RO.m
end Eager

/-- The section `Preimage`'s op `inv`: the map of `BIRO.IRO` and `RFList.m` agree on the first
`size_out` bits. -/
def inv (m1 : FMap (List Bool × ℤ) Bool) (m2 : FMap (List Bool) f_out) : Prop :=
  (∀ l i, FMap.dom m1 (l, i) → 0 ≤ i ∧ i < size_out) ∧
  (∀ l i, FMap.dom m1 (l, i) → FMap.dom m2 l) ∧
  (∀ l, FMap.dom m2 l → ∀ i, 0 ≤ i ∧ i < size_out → FMap.dom m1 (l, i)) ∧
  (∀ l i, FMap.dom m1 (l, i) →
    FMap.get m1 (l, i) = some (nth default (to_list (oget (FMap.get m2 l))) i))

/-- `of_list` inverts `to_list` on lists of length `size_out` (`spec2_dout`, `to_listK`). -/
theorem to_list_oget_of_list (l : List Bool) (h : size l = size_out) :
    to_list (oget (of_list l)) = l := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (Params.spec2_dout l h)
  have := (Params.to_listK v l).mpr hv
  simp only [of_list, to_list, hv, oget, Option.getD_some]
  exact this

/-- `increase_counter` increases the counter. -/
theorem lt_increase_counter {α : Type} (c : ℤ) (l : List α) (k : ℤ) :
    c < increase_counter c l k := by
  have hr := gt0_r
  have h1 : 0 ≤ (size l + 1) / r := Int.ediv_nonneg (by unfold size; omega) hr.le
  unfold increase_counter
  have := le_max_right ((k + r - 1) / r - 1) 0
  omega

/-- The exit of `eq_IRO_RFWhile`'s fresh case: `inv` after the loop sampled `bs` for `x` into
`BIRO.IRO.mp` and `RFList.m` gets `x`.  Not an EC lemma (EC's `smt` after the `while`). -/
theorem inv_fresh (m mp0 : FMap (List Bool × ℤ) Bool) (m2 : FMap (List Bool) f_out)
    (x bs : List Bool) (h0 : inv mp0 m2) (hx : ¬ FMap.dom m2 x) (hsz : size bs = size_out)
    (h1 : ∀ l j, l ≠ x → FMap.get m (l, j) = FMap.get mp0 (l, j))
    (h2 : ∀ j, FMap.dom m (x, j) ↔ 0 ≤ j ∧ j < size_out)
    (h3 : ∀ j, 0 ≤ j → j < size_out → FMap.get m (x, j) = some (nth default bs j)) :
    inv m (FMap.set m2 x (oget (of_list bs))) := by
  have hdom : ∀ l j, l ≠ x → (FMap.dom m (l, j) ↔ FMap.dom mp0 (l, j)) := fun l j hl => by
    rw [FMap.domE, FMap.domE, h1 l j hl]
  refine ⟨fun l i h => ?_, fun l i h => ?_, fun l h i hi => ?_, fun l i h => ?_⟩
  · by_cases hl : l = x
    · subst hl
      exact (h2 i).mp h
    · exact h0.1 l i ((hdom l i hl).mp h)
  · by_cases hl : l = x
    · exact (FMap.mem_set _ _ _ _).mpr (Or.inr hl)
    · exact (FMap.mem_set _ _ _ _).mpr (Or.inl (h0.2.1 l i ((hdom l i hl).mp h)))
  · by_cases hl : l = x
    · subst hl
      exact (h2 i).mpr hi
    · have hl2 : FMap.dom m2 l := ((FMap.mem_set _ _ _ _).mp h).resolve_right hl
      exact (hdom l i hl).mpr (h0.2.2.1 l hl2 i hi)
  · by_cases hl : l = x
    · subst hl
      have hi := (h2 i).mp h
      rw [h3 i hi.1 hi.2, FMap.get_set_sameE]
      simp only [oget, Option.getD_some]
      rw [show Option.getD (of_list bs) default = oget (of_list bs) from rfl,
        to_list_oget_of_list bs hsz]
    · rw [FMap.get_set_neqE _ _ _ _ hl, h1 l i hl]
      exact h0.2.2.2 l i ((hdom l i hl).mp h)

/-- The section `Preimage`'s op `eq_extend_size`. -/
def eq_extend_size (m1 m2 m3 : FMap (List Bool × ℤ) Bool) : Prop :=
  (∀ x j, 0 ≤ j ∧ j < size_out → FMap.get m1 (x, j) = FMap.get m2 (x, j)) ∧
  (∀ x j, size_out ≤ j → FMap.get m1 (x, j) = FMap.get m3 (x, j)) ∧
  (∀ x j, FMap.dom m1 (x, j) → 0 ≤ j)

/-! ## The section `Preimage`, with `declare module A <: SH.AdvPreimage {…}` (its local
declarations in the namespace `Preimage`) -/

namespace Preimage

/-- `eq_extend_size` survives a common update of the first two maps below `size_out`. -/
theorem eq_extend_size_set_lt {m1 m2 m3 : FMap (List Bool × ℤ) Bool} {x : List Bool} {j : ℤ}
    (b : Bool) (h : eq_extend_size m1 m2 m3) (hj0 : 0 ≤ j) (hj : j < size_out) :
    eq_extend_size (FMap.set m1 (x, j) b) (FMap.set m2 (x, j) b) m3 := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun x' j' hj' => ?_, fun x' j' hj' => ?_, fun x' j' hd => ?_⟩
  · rw [FMap.get_setE, FMap.get_setE, h1 x' j' hj']
  · have : (x', j') ≠ (x, j) := fun he => by
      obtain ⟨-, rfl⟩ := Prod.mk.inj he
      omega
    rw [FMap.get_set_neqE _ _ _ _ this, h2 x' j' hj']
  · rcases (FMap.mem_set _ _ _ _).mp hd with hd | he
    · exact h3 x' j' hd
    · obtain ⟨-, rfl⟩ := Prod.mk.inj he
      exact hj0

/-- `eq_extend_size` survives a common update of the first and the third map from `size_out`. -/
theorem eq_extend_size_set_ge {m1 m2 m3 : FMap (List Bool × ℤ) Bool} {x : List Bool} {j : ℤ}
    (b : Bool) (h : eq_extend_size m1 m2 m3) (hj : size_out ≤ j) :
    eq_extend_size (FMap.set m1 (x, j) b) m2 (FMap.set m3 (x, j) b) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hs : (0 : ℤ) < size_out := Params.size_out_gt0
  refine ⟨fun x' j' hj' => ?_, fun x' j' hj' => ?_, fun x' j' hd => ?_⟩
  · have : (x', j') ≠ (x, j) := fun he => by
      obtain ⟨-, rfl⟩ := Prod.mk.inj he
      omega
    rw [FMap.get_set_neqE _ _ _ _ this, h1 x' j' hj']
  · rw [FMap.get_setE, FMap.get_setE, h2 x' j' hj']
  · rcases (FMap.mem_set _ _ _ _).mp hd with hd | he
    · exact h3 x' j' hd
    · obtain ⟨-, rfl⟩ := Prod.mk.inj he
      omega

theorem eq_extend_size_dom_lt {m1 m2 m3 : FMap (List Bool × ℤ) Bool} {x : List Bool} {j : ℤ}
    (h : eq_extend_size m1 m2 m3) (hj0 : 0 ≤ j) (hj : j < size_out) :
    FMap.dom m1 (x, j) ↔ FMap.dom m2 (x, j) := by
  rw [FMap.domE, FMap.domE, h.1 x j ⟨hj0, hj⟩]

theorem eq_extend_size_dom_ge {m1 m2 m3 : FMap (List Bool × ℤ) Bool} {x : List Bool} {j : ℤ}
    (h : eq_extend_size m1 m2 m3) (hj : size_out ≤ j) :
    FMap.dom m1 (x, j) ↔ FMap.dom m3 (x, j) := by
  rw [FMap.domE, FMap.domE, h.2.1 x j hj]

/-- `dlist dbool size_out` read back by `of_list` is `dout` (`dout_equal_dlist`, `of_listK`). -/
theorem dlist_dout :
    (dlist dbool size_out >>= fun l => (pure (oget (of_list l)) : SubProbability f_out)) =
      dout := by
  refine SubProbability.ext_of_expected fun F => ?_
  rw [SubProbability.expected_bind]
  change (dlist dbool Params.size_out).expected _ = Params.dout.expected F
  rw [← Params.dout_equal_dlist, SubProbability.expected_bind]
  simp only [expected_pure]
  refine congrArg Params.dout.expected (funext fun x => ?_)
  have := (Params.to_listK x (Params.to_list x)).mp rfl
  simp only [of_list, this, oget, Option.getD_some]

end Preimage

/-- `OGReal(CSome(Sponge), PSome(Perm))` is
`OIndif(FSome(Sponge(Poget(PSome(Perm)))), PSome(Perm))`. -/
theorem OGReal_eq (D : ODISTINGUISHER) :
    OGReal (CSome Sponge.Sponge) (PSome Perm) D =
      Module.app OIndif.OIndif (Module.pair
        (Module.app FSome (Module.app Sponge.Sponge (Module.app Poget
          (OptionIndifferentiability.OPRIMITIVE.view state (List Bool × ℤ) (List Bool)
              (PSome Perm)))))
        (Module.pair (PSome Perm) D)) := by
  unfold OIndif.OGReal OptionIndifferentiability.OGReal CSome
  erw [Module.app_comp, Module.app_comp]

end GaudisCrypt.SHA3.SHA3OSecurity
