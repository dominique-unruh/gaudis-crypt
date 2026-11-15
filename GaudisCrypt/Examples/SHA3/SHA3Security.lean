import GaudisCrypt.Examples.SHA3.SHA3Indiff
import GaudisCrypt.Lib.EC.PROM
import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Logic.PHoareWp
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.ExpectationCall
import GaudisCrypt.Logic.EqualOutside
import GaudisCrypt.Lib.EC.DList
import GaudisCrypt.Lib.EC.ListRange
import GaudisCrypt.Logic.PRHLTransitivity
import GaudisCrypt.Logic.PRHLFrame
import GaudisCrypt.Logic.FootprintUpper

/-!
# Top-level proof of SHA-3 security (EasyCrypt `proof/SHA3Security.ec`)

Preimage, second-preimage and collision resistance of the sponge with outputs of `size_out` bits
(`CSetSize(Sponge)`), against adversaries making `sigma` queries: `IndifRO_is_secure` applied to
`SHA3Indiff`.  `SHA3_coll_resistant` is the collision resistance of `SHA3`'s padding.

Translation notes (see `notes/SHA3/README.md`):
* The file-level abstract type `f_out`, operators `size_out`, `sigma`, `dout`, `to_list`,
  `of_list` and their axioms are the parameter class `Params` (as `Common.Params`).
* `clone import IndifRO_is_secure as S with …` is the namespace `S` of abbreviations, opened.  The
  clone declares its module variables (`S.SRO.RO.RO.m` …); its `realize`s are `S.axioms`.
* `CSetSize(F)(P)`, `FSetSize(F)` alias `init` and are applied to module parameters: the alias is
  wrapped in a call (exception E5), as is `DSetSize(D)(F)(P) = D(DFSetSize(F), P)`.
  `SimSetSize(S)(F) = S(FGetSize(F))` is `Module.comp S FGetSize`.
* The sections' local lemmas, repeated in each section, go into namespaces named after the sections
  (`Preimage.invmC` …).  Their `clone import Program as Prog` (`Prog2`, `Prog3`) are
  `DList.Program` at `bool`, `dbool`.
* `declare axiom A_ll` is the hypothesis `_A_ll` (`S.D_ll`).
-/

-- the clone `S.SRO.RO` contains the module `RO` (`S.SRO.RO.RO`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.SHA3Security

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.SLCommon.Prefix
open GaudisCrypt.SHA3.Sponge GaudisCrypt.SHA3.Sponge.BIRO GaudisCrypt.SHA3.SHA3Indiff

-- the last imports (`Sponge`, `SHA3Indiff`) win over `Common`'s and the root-level names
export GaudisCrypt.SHA3.SHA3Indiff (state PRIMITIVE limit)

variable [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params]

/-- EasyCrypt's file-level abstract type and operators, with their axioms: `op size_out` with
`size_out_gt0`, `op sigma` with `sigma_gt0`, `type f_out`, `op dout` with `dout_ll`, `dout_fu`,
`dout_full`, `op to_list`, `op of_list` with `spec_dout`, `spec2_dout`, `to_list_inj`, `to_listK`
and `dout_equal_dlist`. -/
class Params : Type 1 where
  size_out : ℤ
  size_out_gt0 : 0 < size_out
  sigma : ℤ
  sigma_gt0 : 0 < sigma
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
def sigma : ℤ := Params.sigma
abbrev f_out : Type := Params.f_out
instance : Inhabited f_out := Params.f_out_inhabited
/-- `f_out` is countable (`to_list` is injective). -/
instance : Countable f_out := Function.Injective.countable Params.to_list_inj
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

/-! ## `clone import IndifRO_is_secure as S with type block <- block * capacity,
type f_in <- bool list, type f_out <- f_out, op sampleto <- dout, op bound <- (limit ^ 2 - limit)%r
/ (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r, op limit <- sigma, op bound_counter <- limit,
op increase_counter <- …` -/

namespace S

namespace Indiff0
abbrev PRIMITIVE := Indifferentiability.PRIMITIVE (block × capacity) (List Bool) f_out
abbrev DPRIMITIVE := Indifferentiability.DPRIMITIVE (block × capacity) (List Bool) f_out
abbrev FUNCTIONALITY := Indifferentiability.FUNCTIONALITY (block × capacity) (List Bool) f_out
abbrev DFUNCTIONALITY := Indifferentiability.DFUNCTIONALITY (block × capacity) (List Bool) f_out
abbrev CONSTRUCTION := Indifferentiability.CONSTRUCTION (block × capacity) (List Bool) f_out
abbrev SIMULATOR := Indifferentiability.SIMULATOR (block × capacity) (List Bool) f_out
abbrev DISTINGUISHER := Indifferentiability.DISTINGUISHER (block × capacity) (List Bool) f_out
end Indiff0

end S

open S

/-- The bound of `SHA3Indiff`, `(limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r +
(4 * limit ^ 2)%r / (2 ^ c)%r`, the clone's `bound`. -/
noncomputable abbrev bound : ℝ := SHA3Indiff.bound

/-- The section's ops `same_ro`, `same_ro2`: the map of `SRO.RO.RO` agrees with that of
`BIRO.IRO` on the first `size_out` bits. -/
def same_ro (m1 : FMap (List Bool) f_out) (m2 : FMap (List Bool × ℤ) Bool) : Prop :=
  (∀ m, FMap.dom m1 m → ∀ i, 0 ≤ i ∧ i < size_out → FMap.dom m2 (m, i)) ∧
  (∀ m, (∃ i, 0 ≤ i ∧ i < size_out ∧ FMap.dom m2 (m, i)) → FMap.dom m1 m) ∧
  (∀ m, FMap.dom m1 m →
    to_list (oget (FMap.get m1 m)) = (range 0 size_out).map fun i => oget (FMap.get m2 (m, i)))

def same_ro2 (m1 : FMap (List Bool) (List Bool)) (m2 : FMap (List Bool × ℤ) Bool) : Prop :=
  (∀ m, FMap.dom m1 m → ∀ i, 0 ≤ i ∧ i < size_out → FMap.dom m2 (m, i)) ∧
  (∀ m, (∃ i, 0 ≤ i ∧ i < size_out ∧ FMap.dom m2 (m, i)) → FMap.dom m1 m) ∧
  (∀ m, FMap.dom m1 m →
    oget (FMap.get m1 m) = (range 0 size_out).map fun i => oget (FMap.get m2 (m, i)))

/-- `of_list` inverts `to_list` on lists of length `size_out` (`spec2_dout`, `to_listK`). -/
theorem to_list_oget_of_list (l : List Bool) (h : size l = size_out) :
    to_list (oget (of_list l)) = l := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (Params.spec2_dout l h)
  have := (Params.to_listK v l).mpr hv
  simp only [of_list, to_list, hv, oget, Option.getD_some]
  exact this

/-- `dout` is `dlist dbool size_out` read back by `of_list` (`dout_equal_dlist`, `to_listK`). -/
theorem dout_dlist : dout = (dlist dbool size_out).hbind fun l => pure (oget (of_list l)) := by
  refine SubProbability.ext_of_expected fun F => ?_
  rw [SubProbability.expected_hbind]
  change _ = (dlist dbool Params.size_out).expected _
  rw [← Params.dout_equal_dlist, SubProbability.expected_bind]
  simp only [expected_pure]
  refine congrArg (Params.dout.expected) (funext fun x => ?_)
  have := (Params.to_listK x (Params.to_list x)).mp rfl
  simp only [of_list, this, oget, Option.getD_some]

/-! ### The real side of the sections' first `have`

`GReal(CSetSize(Sponge), Perm, D(A))` against `RealIndif(Sponge, Perm, DRestr(DSetSize(D(A))))`: the
two games differ in `Cntr.c` (written on the right only); EC's invariant `={glob SRO.Counter,
glob Perm} /\ invm Perm.m{1} Perm.mi{1} /\ ={c}(SRO.Counter, Cntr)` is the states equal outside
`realL` with `realI` on its contents (the adversary is outside `realL`). -/

/-- `Sponge` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_Sponge : FVP.fvP Sponge.Sponge ≤ ⊥ := by
  fp_module

/-! ### The sections' side conditions: adversaries, distinguishers, the simulator -/

set_option maxHeartbeats 4000000 in
/-- `Simulator` touches its maps and `Gconcl_list.BIRO2.IRO.mp`.  Not an EC lemma. -/
@[fp_bound] theorem fvP_Simulator : FVP.fvP Simulator ≤ (Simulator.m).footprint ⊔
    ((Simulator.mi).footprint ⊔ ((Simulator.paths).footprint ⊔
      (Gconcl_list.BIRO2.IRO.mp).footprint)) := by
  have h : FVP.fvP Simulator ≤ (Lens.pair Simulator.m (Lens.pair Simulator.mi
      (Lens.pair Simulator.paths Gconcl_list.BIRO2.IRO.mp))).footprint := by
    fp_module (Lens.pair Simulator.m (Lens.pair Simulator.mi
      (Lens.pair Simulator.paths Gconcl_list.BIRO2.IRO.mp)))
  simpa only [Footprint.lens_pair] using h

/-! ## The section `Preimage`, with `declare module A <: SRO.AdvPreimage {…, -DPre}` and
`declare axiom A_ll` (its local declarations in the namespace `Preimage`) -/

namespace Preimage

theorem invm_dom_rng (m mi : FMap state state) : invm m mi → FMap.dom m = FMap.rng mi := by
  intro h
  funext x
  apply propext
  rw [FMap.domE, FMap.rngE]
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hx
    exact ⟨v, (h x v).mp hv⟩
  · rintro ⟨a, ha⟩
    rw [(h x a).mpr ha]
    simp

theorem invmC' (m mi : FMap state state) : invm m mi → invm mi m :=
  fun h x y => (h y x).symm

theorem invmC (m mi : FMap state state) : invm m mi ↔ invm mi m :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

theorem useful (m mi : FMap state state) (a : state) :
    invm m mi → ¬ FMap.dom m a → is_lossless (dexcepted (dprod bdistr cdistr) (FMap.rng m)) :=
  fun _ h => EC.Strong_RP_RF.excepted_lossless state SLCommon.dstate ConcreteF.Switching.uD_uf_fu m
    ⟨a, h⟩

/-- `clone import Program as Prog with type t <- bool, op d <- dbool`. -/
noncomputable abbrev Prog.LoopSnoc.sample := DList.Program.LoopSnoc.sample Bool dbool

end Preimage

/-! ## The section `SecondPreimage`, with `declare module A <: SRO.AdvSecondPreimage
{…, -D2Pre}` and `declare axiom A_ll` (its local declarations in the namespace
`SecondPreimage`) -/

namespace SecondPreimage

/-- `clone import Program as Prog2 with type t <- bool, op d <- dbool`. -/
noncomputable abbrev Prog2.LoopSnoc.sample := DList.Program.LoopSnoc.sample Bool dbool

end SecondPreimage

/-! ## The section `Collision`, with `declare module A <: SRO.AdvCollision {…}` and
`declare axiom A_ll` (its local declarations in the namespace `Collision`) -/

namespace Collision

/-- `clone import Program as Prog3 with type t <- bool, op d <- dbool`. -/
noncomputable abbrev Prog3.LoopSnoc.sample := DList.Program.LoopSnoc.sample Bool dbool

end Collision

end GaudisCrypt.SHA3.SHA3Security
