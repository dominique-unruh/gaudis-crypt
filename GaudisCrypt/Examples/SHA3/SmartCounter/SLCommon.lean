import GaudisCrypt.Examples.SHA3.Common
import GaudisCrypt.Examples.SHA3.Indifferentiability
import GaudisCrypt.Lib.EC.FSet
import GaudisCrypt.Lib.EC.PROM
import GaudisCrypt.Lib.EC.DProd
import GaudisCrypt.Lib.EC.Tuple
import GaudisCrypt.Logic.PHoare

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

/-- EasyCrypt's `op max_size : { int | 0 <= max_size } as max_ge0`: the maximal number of calls to
the permutation and its inverse, including those performed by the construction. -/
class Params extends Common.Params where
  max_size : ℤ
  max_ge0 : 0 ≤ max_size

variable [Params]

def max_size : ℤ := Params.max_size
theorem max_ge0 : 0 ≤ max_size := Params.max_ge0

/-- `abbrev ([+]) (x : 'b) = fun (_ : 'a) => x`. -/
abbrev «[+]» {α β : Type*} (x : β) : α → β := fun _ => x

abbrev state := block × capacity

noncomputable def dstate : SubProbability state := dprod bdistr cdistr

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

/-- `clone export Tuple as TupleBl with type t <- block, op Support.enum <- Block.blocks`. -/
noncomputable def TupleBl.wordn (n : ℤ) : List (List block) := Tuple.wordn Block.blocks n

noncomputable def bl_enum : List (List block) :=
  (mkseq (fun i => TupleBl.wordn i) (max_size + 1)).flatten

noncomputable def bl_univ : FSet (List block) := bl_enum.toFinset

-- `clone import FullRO as F with type in_t <- block list, type out_t <- block,
-- op dout _ <- bdistr, type d_in_t <- unit, type d_out_t <- bool`
namespace F
noncomputable abbrev dout : List block → SubProbability block := fun _ => bdistr
noncomputable abbrev RO := PROM.FullRO.RO (List block) block dout
/-- `F.RO.m`. -/
noncomputable abbrev RO.m := PROM.FullRO.RO.m (in_t := List block) (out_t := block)
noncomputable abbrev LRO := PROM.FullRO.LRO (List block) block dout
noncomputable abbrev FRO := PROM.FullRO.FRO (List block) block dout
abbrev RO_Distinguisher := PROM.FullRO.RO_Distinguisher (List block) block Unit Bool
namespace FullEager
noncomputable abbrev RRO := PROM.FullRO.FullEager.RRO (List block) block dout
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

/-- `clone export DProd.ProdSampling as Sample2 with type t1 <- block, type t2 <- capacity`. -/
noncomputable abbrev Sample2.S := DProd.ProdSampling.S block capacity

/-! ## Useful types and operators for the proof -/

def incl {α β : Type} [DecidableEq α] (m m' : FMap α β) : Prop :=
  ∀ x, FMap.get m x ≠ none → FMap.get m' x = FMap.get m x

abbrev handle := ℤ
abbrev hstate := block × handle
abbrev ccapacity := capacity × flag
abbrev smap := FMap state state
abbrev hsmap := FMap hstate hstate
abbrev handles := FMap handle ccapacity

def is_pre_permutation {α : Type} [DecidableEq α] (m mi : FMap α α) : Prop :=
  (∀ x, FMap.rng m x → FMap.dom mi x) ∧ (∀ x, FMap.rng mi x → FMap.dom m x)

theorem half_permutation_set {α : Type} [DecidableEq α] (m' mi' : FMap α α) (x' y' : α) :
    (∀ x, FMap.rng m' x → FMap.dom mi' x) →
    (∀ x, FMap.rng (FMap.set m' x' y') x → FMap.dom (FMap.set mi' y' x') x) := by
  sorry

theorem pre_permutation_set {α : Type} [DecidableEq α] (m mi : FMap α α) (x y : α) :
    is_pre_permutation m mi → is_pre_permutation (FMap.set m x y) (FMap.set mi y x) := by
  sorry

/-- Functional version of the construction, using handles. -/
def step_hpath (mh : hsmap) (sah : Option hstate) (b : block) : Option hstate :=
  if sah = none then none
  else
    let sah := oget sah
    FMap.get mh (sah.1 +^ b, sah.2)

def build_hpath (mh : hsmap) (bs : List block) : Option hstate :=
  bs.foldl (step_hpath mh) (some (b0, 0))

inductive build_hpath_spec (mh : hsmap) (p : List block) (v : block) (h : handle) : Prop where
  | Empty : p = [] → v = b0 → h = 0 → build_hpath_spec mh p v h
  | Extend (p' : List block) (b v' : block) (h' : handle) :
      p = rcons p' b → build_hpath mh p' = some (v', h') →
      FMap.get mh (v' +^ b, h') = some (v, h) → build_hpath_spec mh p v h

theorem build_hpathP (mh : hsmap) (p : List block) (v : block) (h : handle) :
    build_hpath mh p = some (v, h) ↔ build_hpath_spec mh p v h := by
  sorry

theorem build_hpath_map0 (p : List block) :
    build_hpath FMap.empty p = if p = [] then some (b0, 0) else none := by
  sorry

/-! ## Prefixes (EC's `theory Prefix`) -/

namespace Prefix

section Generic

variable {α : Type} [DecidableEq α] [Inhabited α]

def «prefix» : List α → List α → ℤ
  | x :: s', y :: t' => if x = y then 1 + «prefix» s' t' else 0
  | _, _ => 0

theorem prefix0s (s : List α) : «prefix» [] s = 0 := by
  sorry

theorem prefixs0 (s : List α) : «prefix» s [] = 0 := by
  sorry

theorem prefix_eq (l : List α) : «prefix» l l = size l := by
  sorry

theorem prefixC (l1 l2 : List α) : «prefix» l1 l2 = «prefix» l2 l1 := by
  sorry

theorem prefix_ge0 (l1 l2 : List α) : 0 ≤ «prefix» l1 l2 := by
  sorry

theorem prefix_sizel (l1 l2 : List α) : «prefix» l1 l2 ≤ size l1 := by
  sorry

theorem prefix_sizer (l1 l2 : List α) : «prefix» l1 l2 ≤ size l2 := by
  sorry

theorem prefix_take (l1 l2 : List α) :
    take («prefix» l1 l2) l1 = take («prefix» l1 l2) l2 := by
  sorry

theorem take_take (l : List α) (i j : ℤ) : take i (take j l) = take (min i j) l := by
  sorry

theorem prefix_take_leq (l1 l2 : List α) (i : ℤ) : i ≤ «prefix» l1 l2 → take i l1 = take i l2 := by
  sorry

theorem prefix_nth (l1 l2 : List α) :
    let i := «prefix» l1 l2
    ∀ j, 0 ≤ j ∧ j < i → nth default l1 j = nth default l2 j := by
  sorry

def max_prefix (l1 l2 : List α) : List (List α) → List α
  | [] => l2
  | l' :: ll' =>
    if «prefix» l1 l2 < «prefix» l1 l' then max_prefix l1 l' ll' else max_prefix l1 l2 ll'

def get_max_prefix (l : List α) : List (List α) → List α
  | [] => []
  | l' :: ll' => max_prefix l l' ll'

end Generic

def prefix_inv (queries : FMap (List block) block) (prefixes : FMap (List block) state) : Prop :=
  (∀ bs : List block, FMap.dom queries bs →
    oget (FMap.get queries bs) = (oget (FMap.get prefixes bs)).1) ∧
  (∀ bs : List block, FMap.dom queries bs → ∀ i, FMap.dom prefixes (take i bs)) ∧
  (∀ bs : List block, ∀ i, take i bs ≠ [] → FMap.dom prefixes (take i bs) →
    ∃ l2, FMap.dom queries (take i bs ++ l2))

def all_prefixes (prefixes : FMap (List block) state) : Prop :=
  ∀ bs : List block, FMap.dom prefixes bs → ∀ i, FMap.dom prefixes (take i bs)

section Generic2

variable {α : Type} [DecidableEq α] [Inhabited α]

theorem aux_mem_get_max_prefix (l1 l2 : List α) (ll : List (List α)) :
    max_prefix l1 l2 ll = l2 ∨ max_prefix l1 l2 ll ∈ ll := by
  sorry

theorem mem_get_max_prefix (l : List α) (ll : List (List α)) :
    ll ≠ [] → get_max_prefix l ll ∈ ll := by
  sorry

end Generic2

theorem take_get_max_prefix (l : List block) (prefixes : FMap (List block) state) :
    (∃ b, FMap.dom prefixes b) → all_prefixes prefixes →
    FMap.dom prefixes (take («prefix» l (get_max_prefix l (elems (FMap.fdom prefixes)))) l) := by
  sorry

theorem take_get_max_prefix2 (l : List block) (prefixes : FMap (List block) state) (i : ℤ) :
    (∃ b, FMap.dom prefixes b) → all_prefixes prefixes →
    i ≤ «prefix» l (get_max_prefix l (elems (FMap.fdom prefixes))) →
    FMap.dom prefixes (take i l) := by
  sorry

section Generic3

variable {α : Type} [DecidableEq α] [Inhabited α]

theorem prefix_cat (l l1 l2 : List α) : «prefix» (l ++ l1) (l ++ l2) = size l + «prefix» l1 l2 := by
  sorry

theorem prefix_leq_take (l1 l2 : List α) (i : ℤ) :
    0 ≤ i ∧ i ≤ min (size l1) (size l2) → take i l1 = take i l2 → i ≤ «prefix» l1 l2 := by
  sorry

theorem prefix0 (l1 l2 : List α) :
    «prefix» l1 l2 = 0 ↔ l1 = [] ∨ l2 = [] ∨ head default l1 ≠ head default l2 := by
  sorry

theorem head_nth0 (l : List α) : head default l = nth default l 0 := by
  sorry

theorem get_prefix (l1 l2 : List α) (i : ℤ) :
    0 ≤ i ∧ i ≤ min (size l1) (size l2) →
    (drop i l1 = [] ∨ drop i l2 = [] ∨
      (i < min (size l1) (size l2) ∧ nth default l1 i ≠ nth default l2 i)) →
    take i l1 = take i l2 → i = «prefix» l1 l2 := by
  sorry

theorem get_max_prefix_leq (l1 l2 : List α) (ll : List (List α)) :
    «prefix» l1 l2 ≤ «prefix» l1 (max_prefix l1 l2 ll) := by
  sorry

theorem get_max_prefix_is_max (l1 l2 : List α) (ll : List (List α)) :
    ∀ l3, l3 ∈ ll → «prefix» l1 l3 ≤ «prefix» l1 (max_prefix l1 l2 ll) := by
  sorry

theorem get_max_prefix_max (l : List α) (ll : List (List α)) :
    ∀ l2, l2 ∈ ll → «prefix» l l2 ≤ «prefix» l (get_max_prefix l ll) := by
  sorry

end Generic3

theorem all_take_in (l : List block) (i : ℤ) (prefixes : FMap (List block) state) :
    0 ≤ i ∧ i ≤ size l → all_prefixes prefixes → FMap.dom prefixes (take i l) →
    i ≤ «prefix» l (get_max_prefix l (elems (FMap.fdom prefixes))) := by
  sorry

theorem prefix_inv_leq (l : List block) (i : ℤ) (prefixes : FMap (List block) state)
    (queries : FMap (List block) block) :
    0 ≤ i ∧ i ≤ size l → elems (FMap.fdom queries) ≠ [] → all_prefixes prefixes →
    FMap.dom prefixes (take i l) → prefix_inv queries prefixes →
    i ≤ «prefix» l (get_max_prefix l (elems (FMap.fdom queries))) := by
  sorry

section Generic4

variable {α : Type} [DecidableEq α] [Inhabited α]

theorem max_prefix_eq (l : List α) (ll : List (List α)) : max_prefix l l ll = l := by
  sorry

theorem prefix_max_prefix_eq_size (l1 l2 : List α) (ll : List (List α)) :
    l1 = l2 ∨ l1 ∈ ll → «prefix» l1 (max_prefix l1 l2 ll) = size l1 := by
  sorry

theorem prefix_get_max_prefix_eq_size (l : List α) (ll : List (List α)) :
    l ∈ ll → «prefix» l (get_max_prefix l ll) = size l := by
  sorry

theorem get_max_prefix_exists (l : List α) (ll : List (List α)) :
    ll ≠ [] → ∃ l2, take («prefix» l (get_max_prefix l ll)) l ++ l2 ∈ ll := by
  sorry

theorem prefix_geq (l1 l2 : List α) :
    «prefix» l1 l2 = «prefix» (take («prefix» l1 l2) l1) (take («prefix» l1 l2) l2) := by
  sorry

theorem prefix_take_prefix (l1 l2 : List α) :
    «prefix» (take («prefix» l1 l2) l1) l2 = «prefix» l1 l2 := by
  sorry

theorem prefix_leq_prefix_cat (l1 l2 l3 : List α) : «prefix» l1 l2 ≤ «prefix» (l1 ++ l3) l2 := by
  sorry

theorem prefix_take_leq_prefix (l1 l2 : List α) (i : ℤ) :
    «prefix» (take i l1) l2 ≤ «prefix» l1 l2 := by
  sorry

theorem prefix_take_geq_prefix (l1 l2 : List α) (i : ℤ) :
    «prefix» l1 l2 ≤ i → «prefix» l1 l2 = «prefix» (take i l1) l2 := by
  sorry

theorem get_max_prefix_take (l : List α) (ll : List (List α)) (i : ℤ) :
    «prefix» l (get_max_prefix l ll) ≤ i → get_max_prefix l ll = get_max_prefix (take i l) ll := by
  sorry

theorem drop_prefix_neq (l1 l2 : List α) :
    drop («prefix» l1 l2) l1 = [] ∨ drop («prefix» l1 l2) l1 ≠ drop («prefix» l1 l2) l2 := by
  sorry

theorem prefix_prefix_prefix (l1 l2 l3 : List α) (ll : List (List α)) :
    «prefix» l1 l2 ≤ «prefix» l1 l3 →
    «prefix» l1 (max_prefix l1 l2 ll) ≤ «prefix» l1 (max_prefix l1 l3 ll) := by
  sorry

theorem prefix_lt_size (l : List α) (ll : List (List α)) :
    «prefix» l (get_max_prefix l ll) < size l →
    ∀ i, «prefix» l (get_max_prefix l ll) < i → take i l ∉ ll := by
  sorry

end Generic4

theorem asfadst (queries : FMap (List block) block) (prefixes : FMap (List block) state)
    (bs : List block) :
    prefix_inv queries prefixes → elems (FMap.fdom queries) ≠ [] → all_prefixes prefixes →
    (∀ j, 0 ≤ j ∧ j ≤ size bs → FMap.dom prefixes (take j bs)) →
    take («prefix» bs (get_max_prefix bs (elems (FMap.fdom queries))) + 1) bs = bs := by
  sorry

theorem prefix_exchange_prefix_inv {α : Type} [DecidableEq α] [Inhabited α]
    (ll1 ll2 : List (List α)) (l : List α) :
    (∀ l2, l2 ∈ ll1 → l2 ∈ ll2) →
    (∀ l2 : List α, l2 ∈ ll1 → ∀ i, take i l2 ∈ ll2) →
    (∀ l2, l2 ∈ ll2 → ∃ l3, l2 ++ l3 ∈ ll1) →
    «prefix» l (get_max_prefix l ll1) = «prefix» l (get_max_prefix l ll2) := by
  sorry

theorem prefix_inv_nil (queries : FMap (List block) block) (prefixes : FMap (List block) state) :
    prefix_inv queries prefixes → elems (FMap.fdom queries) = [] →
    FMap.fdom prefixes ⊆ fset1 [] := by
  sorry

theorem aux_prefix_exchange (queries : FMap (List block) block)
    (prefixes : FMap (List block) state) (l : List block) :
    prefix_inv queries prefixes → all_prefixes prefixes → elems (FMap.fdom queries) ≠ [] →
    «prefix» l (get_max_prefix l (elems (FMap.fdom queries))) =
      «prefix» l (get_max_prefix l (elems (FMap.fdom prefixes))) := by
  sorry

theorem prefix_exchange (queries : FMap (List block) block) (prefixes : FMap (List block) state)
    (l : List block) :
    prefix_inv queries prefixes → all_prefixes prefixes →
    «prefix» l (get_max_prefix l (elems (FMap.fdom queries))) =
      «prefix» l (get_max_prefix l (elems (FMap.fdom prefixes))) := by
  sorry

def all_prefixes_fset (prefixes : FSet (List block)) : Prop :=
  ∀ bs, bs ∈ prefixes → ∀ i, take i bs ∈ prefixes

def inv_prefix_block (queries : FMap (List block) block) (prefixes : FMap (List block) block) :
    Prop :=
  (∀ bs : List block, FMap.dom queries bs → FMap.get queries bs = FMap.get prefixes bs) ∧
  (∀ bs : List block, FMap.dom queries bs → ∀ i, 0 < i ∧ i ≤ size bs →
    FMap.dom prefixes (take i bs))

theorem prefix_gt0_mem {α : Type} [DecidableEq α] [Inhabited α] (l : List α)
    (ll : List (List α)) :
    0 < «prefix» l (get_max_prefix l ll) → get_max_prefix l ll ∈ ll := by
  sorry

theorem inv_prefix_block_mem_take (queries prefixes : FMap (List block) block) (l : List block)
    (i : ℤ) :
    inv_prefix_block queries prefixes →
    0 < i ∧ i < «prefix» l (get_max_prefix l (elems (FMap.fdom queries))) →
    FMap.dom prefixes (take i l) := by
  sorry

section Generic5

variable {α : Type} [DecidableEq α] [Inhabited α]

theorem prefix_cat_leq_prefix_size (l1 l2 l3 : List α) :
    «prefix» (l1 ++ l2) l3 ≤ «prefix» l1 l3 + size l2 := by
  sorry

theorem prefix_cat1 (l1 l2 l3 : List α) :
    «prefix» (l1 ++ l2) l3 =
      «prefix» l1 l3 + if «prefix» l1 l3 = size l1 then «prefix» l2 (drop (size l1) l3) else 0 := by
  sorry

theorem prefix_leq_prefix_cat_size (l1 l2 : List α) (ll : List (List α)) :
    «prefix» (l1 ++ l2) (get_max_prefix (l1 ++ l2) ll) ≤
      «prefix» l1 (get_max_prefix l1 ll) +
        if «prefix» l1 (get_max_prefix l1 ll) = size l1 then
          «prefix» l2 (get_max_prefix l2 (ll.map (drop (size l1))))
        else 0 := by
  sorry

theorem diff_size_prefix_leq_cat (l1 l2 : List α) (ll : List (List α)) :
    size l1 - «prefix» l1 (get_max_prefix l1 ll) ≤
      size (l1 ++ l2) - «prefix» (l1 ++ l2) (get_max_prefix (l1 ++ l2) ll) := by
  sorry

end Generic5

def invm {α β : Type} [DecidableEq α] [DecidableEq β] (m mi : FMap (α × β) (α × β)) : Prop :=
  ∀ x y, FMap.get m x = some y ↔ FMap.get mi y = some x

theorem invm_set {α β : Type} [DecidableEq α] [DecidableEq β] (m mi : FMap (α × β) (α × β))
    (x y : α × β) :
    ¬ FMap.dom m x → ¬ FMap.rng m y → invm m mi → invm (FMap.set m x y) (FMap.set mi y x) := by
  sorry

end Prefix

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

theorem rp_ll (P : DPRIMITIVE) (_hP : FVP.fvP P ≤ C.footprintᶜ) :
    (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
    (Indifferentiability.DPRIMITIVE.f state (List block) block
      (Module.app DPRestr P)).procedure.IsLossless := by
  sorry

theorem rpi_ll (P : DPRIMITIVE) (_hP : FVP.fvP P ≤ C.footprintᶜ) :
    (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
    (Indifferentiability.DPRIMITIVE.fi state (List block) block
      (Module.app DPRestr P)).procedure.IsLossless := by
  sorry

theorem rf_ll (F : DFUNCTIONALITY) (_hF : FVP.fvP F ≤ C.footprintᶜ) :
    (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
    (Indifferentiability.DFUNCTIONALITY.f state (List block) block
      (Module.app DFRestr F)).procedure.IsLossless := by
  sorry

theorem DRestr_ll (D : DISTINGUISHER) (_hD : FVP.fvP D ≤ C.footprintᶜ) :
    (∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D)ᶜ →
      FVP.fvP P ≤ (FVP.fvP D)ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless) →
    ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP (DRestr D))ᶜ →
      FVP.fvP P ≤ (FVP.fvP (DRestr D))ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app (DRestr D) (Module.pair F P)).procedure.IsLossless := by
  sorry

section RESTR

variable (F : FUNCTIONALITY) (P : PRIMITIVE) (D : DISTINGUISHER)

/-- `declare module F <: FUNCTIONALITY{-C, -Redo}`, `P <: PRIMITIVE{-C, -F, -Redo}`,
`D <: DISTINGUISHER{-F, -P, -C, -Redo}`. -/
theorem swap_restr (hD : Module.Representable D (distExt))
    (_hF : FVP.fvP F ≤ (C.footprint ⊔ (Redo.prefixes).footprint)ᶜ)
    (_hP : FVP.fvP P ≤ (C.footprint ⊔ FVP.fvP F ⊔ (Redo.prefixes).footprint)ᶜ)
    (_hDd : FVP.fvP D ≤ (FVP.fvP F ⊔ FVP.fvP P ⊔ C.footprint ⊔ (Redo.prefixes).footprint)ᶜ)
    (m : VariableAssignment) :
    Procedure.Pr (Module.app Indif (Module.pair (FRestr F) (Module.pair (PRestr P) D))).procedure
        () m (fun r _ => r = true) =
      Procedure.Pr (Module.app Indif (Module.pair F (Module.pair P (DRestr D)))).procedure
        () m (fun r _ => r = true) := by
  sorry

end RESTR

section COUNT

variable (P : PRIMITIVE) (CO : CONSTRUCTION) (D : DISTINGUISHER)

/-- `declare module P <: PRIMITIVE{-C}`, `CO <: CONSTRUCTION{-C, -P}`,
`D <: DISTINGUISHER{-C, -P, -CO}`, with the axioms `f_ll`, `fi_ll`, `CO_ll`, `D_ll`. -/
theorem Pr_restr (hD : Module.Representable D (distExt))
    (_hP : FVP.fvP P ≤ C.footprintᶜ) (_hCO : FVP.fvP CO ≤ (C.footprint ⊔ FVP.fvP P)ᶜ)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ FVP.fvP P ⊔ FVP.fvP CO)ᶜ)
    (f_ll : (Indifferentiability.PRIMITIVE.f state (List block) block P).procedure.IsLossless)
    (fi_ll : (Indifferentiability.PRIMITIVE.fi state (List block) block P).procedure.IsLossless)
    (CO_ll : (Indifferentiability.FUNCTIONALITY.f state (List block) block
      (Module.app CO (Indifferentiability.PRIMITIVE.view state (List block) block P))
      ).procedure.IsLossless)
    (D_ll : ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D)ᶜ →
      FVP.fvP P ≤ (FVP.fvP D)ᶜ →
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
  sorry

end COUNT

/-! ## Operators and properties of handles -/

noncomputable def hinv (handles : handles) (c : capacity) : Option handle :=
  FMap.find (fun _ cf => decide (cf.1 = c)) handles

noncomputable def hinvK (handles : handles) (c : capacity) : Option handle :=
  FMap.find (fun _ c' => decide (c' = c)) (FMap.restr Known handles)

def huniq (handles : handles) : Prop :=
  ∀ h1 h2 cf1 cf2, FMap.get handles h1 = some cf1 → FMap.get handles h2 = some cf2 →
    cf1.1 = cf2.1 → h1 = h2

theorem hinvP (handles : handles) (c : capacity) :
    if hinv handles c = none then ∀ h f, FMap.get handles h ≠ some (c, f)
    else ∃ f, FMap.get handles (oget (hinv handles c)) = some (c, f) := by
  sorry

theorem huniq_hinv (handles : handles) (h : handle) :
    huniq handles → FMap.dom handles h →
    hinv handles (oget (FMap.get handles h)).1 = some h := by
  sorry

theorem hinvKP (handles : handles) (c : capacity) :
    if hinvK handles c = none then ∀ h, FMap.get handles h ≠ some (c, Known)
    else FMap.get handles (oget (hinvK handles c)) = some (c, Known) := by
  sorry

theorem huniq_hinvK (handles : handles) (c : capacity) :
    huniq handles → FMap.rng handles (c, Known) →
    FMap.get handles (oget (hinvK handles c)) = some (c, Known) := by
  sorry

theorem huniq_hinvK_h (h : handle) (handles : handles) (c : capacity) :
    huniq handles → FMap.get handles h = some (c, Known) → hinvK handles c = some h := by
  sorry

/-! ## The initial game -/

/-- `module GReal(D : DISTINGUISHER) = RealIndif(SqueezelessSponge, PC(Perm), D)`. -/
noncomputable def GReal (D : DISTINGUISHER) : procmod () → Bool :=
  RealIndif SqueezelessSponge (Module.app PC Perm) D

end GaudisCrypt.SHA3.SLCommon
