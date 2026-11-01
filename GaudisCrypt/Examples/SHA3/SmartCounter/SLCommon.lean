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

omit [Params] in
theorem half_permutation_set {α : Type} [DecidableEq α] (m' mi' : FMap α α) (x' y' : α) :
    (∀ x, FMap.rng m' x → FMap.dom mi' x) →
    (∀ x, FMap.rng (FMap.set m' x' y') x → FMap.dom (FMap.set mi' y' x') x) := by
  intro h x0 ⟨x, hx⟩
  change FMap.get (FMap.set m' x' y') x = some x0 at hx
  rw [FMap.get_setE] at hx
  rw [FMap.mem_set]
  split_ifs at hx
  · exact Or.inr (Option.some.inj hx).symm
  · exact Or.inl (h x0 ⟨x, hx⟩)

theorem pre_permutation_set {α : Type} [DecidableEq α] (m mi : FMap α α) (x y : α) :
    is_pre_permutation m mi → is_pre_permutation (FMap.set m x y) (FMap.set mi y x) := by
  rintro ⟨h1, h2⟩
  exact ⟨half_permutation_set m mi x y h1, half_permutation_set mi m y x h2⟩

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
  rcases List.eq_nil_or_concat p with rfl | ⟨p, b, rfl⟩
  · constructor
    · intro hb
      simp only [build_hpath, List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact .Empty rfl rfl rfl
    · rintro (⟨-, rfl, rfl⟩ | ⟨p', b, v', h', hp, -, -⟩)
      · rfl
      · simp [rcons] at hp
  · rw [List.concat_eq_append]
    have hstep : build_hpath mh (p ++ [b]) = step_hpath mh (build_hpath mh p) b := by
      simp [build_hpath, List.foldl_append]
    rw [hstep]
    constructor
    · cases hp : build_hpath mh p with
      | none => simp [step_hpath]
      | some s =>
        obtain ⟨v', h'⟩ := s
        intro hs
        simp only [step_hpath, reduceCtorEq, if_false, oget, Option.getD_some] at hs
        exact .Extend p b v' h' rfl hp hs
    · rintro (⟨hnil, -, -⟩ | ⟨p', b', v', h', heq, hb, hm⟩)
      · simp at hnil
      · have := List.append_inj' heq rfl
        simp only [List.cons.injEq, and_true] at this
        obtain ⟨rfl, rfl⟩ := this
        simp [step_hpath, hb, hm, oget]

theorem build_hpath_map0 (p : List block) :
    build_hpath FMap.empty p = if p = [] then some (b0, 0) else none := by
  rcases List.eq_nil_or_concat p with rfl | ⟨p, b, rfl⟩
  · rfl
  · rw [List.concat_eq_append, if_neg (by simp)]
    simp only [build_hpath, List.foldl_append, List.foldl_cons, List.foldl_nil, step_hpath]
    split_ifs
    · rfl
    · exact FMap.emptyE _

/-! ## Prefixes (EC's `theory Prefix`) -/

namespace Prefix

section Generic

variable {α : Type} [DecidableEq α] [Inhabited α]
omit [Params]

def «prefix» : List α → List α → ℤ
  | x :: s', y :: t' => if x = y then 1 + «prefix» s' t' else 0
  | _, _ => 0

theorem prefix0s (s : List α) : «prefix» [] s = 0 := by
  cases s <;> rfl

theorem prefixs0 (s : List α) : «prefix» s [] = 0 := by
  cases s <;> rfl

theorem prefix_eq (l : List α) : «prefix» l l = size l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [«prefix», ih, size]; ring

theorem prefixC (l1 l2 : List α) : «prefix» l1 l2 = «prefix» l2 l1 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> rfl
  | cons x l1 ih =>
    cases l2 with
    | nil => rfl
    | cons y l2 => simp only [«prefix», ih, eq_comm]

theorem prefix_ge0 (l1 l2 : List α) : 0 ≤ «prefix» l1 l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [«prefix»]
  | cons x l1 ih =>
    cases l2 with
    | nil => simp [«prefix»]
    | cons y l2 => simp only [«prefix»]; split_ifs <;> linarith [ih l2]

theorem prefix_sizel (l1 l2 : List α) : «prefix» l1 l2 ≤ size l1 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [«prefix», size]
  | cons x l1 ih =>
    cases l2 with
    | nil => simp only [«prefix», size, List.length_cons]; omega
    | cons y l2 =>
      simp only [«prefix», size, List.length_cons] at ih ⊢
      split_ifs <;> push_cast <;> linarith [ih l2]

theorem prefix_sizer (l1 l2 : List α) : «prefix» l1 l2 ≤ size l2 := by
  rw [prefixC]; exact prefix_sizel l2 l1

theorem prefix_take (l1 l2 : List α) :
    take («prefix» l1 l2) l1 = take («prefix» l1 l2) l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [«prefix», take]
  | cons x l1 ih =>
    cases l2 with
    | nil => simp [«prefix», take]
    | cons y l2 =>
      simp only [«prefix»]
      split_ifs with h
      · subst h
        have h0 := prefix_ge0 l1 l2
        have := ih l2
        simp only [take] at this ⊢
        rw [show (1 + «prefix» l1 l2).toNat = («prefix» l1 l2).toNat + 1 by omega]
        simp [this]
      · simp [take]

omit [DecidableEq α] [Inhabited α] in
theorem take_take (l : List α) (i j : ℤ) : take i (take j l) = take (min i j) l := by
  simp only [take, List.take_take]
  congr 1
  omega

theorem prefix_take_leq (l1 l2 : List α) (i : ℤ) : i ≤ «prefix» l1 l2 → take i l1 = take i l2 := by
  intro hi
  have h := prefix_take l1 l2
  rw [show i = min i («prefix» l1 l2) by omega, ← take_take, h, take_take]

theorem prefix_nth (l1 l2 : List α) :
    let i := «prefix» l1 l2
    ∀ j, 0 ≤ j ∧ j < i → nth default l1 j = nth default l2 j := by
  intro i j ⟨hj0, hji⟩
  have h := congrArg (fun l => nth default l j) (prefix_take l1 l2)
  simp only [nth, take, if_pos hj0] at h ⊢
  have hj : j.toNat < («prefix» l1 l2).toNat := by omega
  simpa [List.getD_eq_getElem?_getD, List.getElem?_take, hj] using h

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
omit [Params]

theorem aux_mem_get_max_prefix (l1 l2 : List α) (ll : List (List α)) :
    max_prefix l1 l2 ll = l2 ∨ max_prefix l1 l2 ll ∈ ll := by
  induction ll generalizing l2 with
  | nil => exact Or.inl rfl
  | cons l' ll' ih =>
    simp only [max_prefix]
    split_ifs
    · rcases ih l' with h | h
      · rw [h]; exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases ih l2 with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_get_max_prefix (l : List α) (ll : List (List α)) :
    ll ≠ [] → get_max_prefix l ll ∈ ll := by
  intro hne
  obtain ⟨l', ll', rfl⟩ := List.exists_cons_of_ne_nil hne
  rcases aux_mem_get_max_prefix l l' ll' with h | h
  · simp only [get_max_prefix]; rw [h]; exact List.mem_cons_self
  · simp only [get_max_prefix]; exact List.mem_cons_of_mem _ h

end Generic2

/-- Not an EasyCrypt lemma: `elems (fdom m)` lists the domain (EasyCrypt's `memE` and
`mem_fdom` together). -/
theorem mem_elems_fdom {β : Type} (m : FMap (List block) β) (x : List block) :
    x ∈ elems (FMap.fdom m) ↔ FMap.dom m x := by
  simp only [elems, Finset.mem_toList]; exact FMap.mem_fdom m x

theorem take_get_max_prefix (l : List block) (prefixes : FMap (List block) state) :
    (∃ b, FMap.dom prefixes b) → all_prefixes prefixes →
    FMap.dom prefixes (take («prefix» l (get_max_prefix l (elems (FMap.fdom prefixes)))) l) := by
  rintro ⟨b, hb⟩ hall
  have hne : elems (FMap.fdom prefixes) ≠ [] := List.ne_nil_of_mem ((mem_elems_fdom _ _).mpr hb)
  rw [prefix_take]
  exact hall _ ((mem_elems_fdom _ _).mp (mem_get_max_prefix _ _ hne)) _

theorem take_get_max_prefix2 (l : List block) (prefixes : FMap (List block) state) (i : ℤ) :
    (∃ b, FMap.dom prefixes b) → all_prefixes prefixes →
    i ≤ «prefix» l (get_max_prefix l (elems (FMap.fdom prefixes))) →
    FMap.dom prefixes (take i l) := by
  rintro ⟨b, hb⟩ hall hi
  have hne : elems (FMap.fdom prefixes) ≠ [] := List.ne_nil_of_mem ((mem_elems_fdom _ _).mpr hb)
  rw [prefix_take_leq _ _ i hi]
  exact hall _ ((mem_elems_fdom _ _).mp (mem_get_max_prefix _ _ hne)) _

section Generic3

variable {α : Type} [DecidableEq α] [Inhabited α]
omit [Params]

omit [DecidableEq α] [Inhabited α] in
private theorem take_cons_pos (z : α) (zs : List α) {i : ℤ} (hi : 0 < i) :
    take i (z :: zs) = z :: take (i - 1) zs := by
  simp only [take]; rw [show i.toNat = (i - 1).toNat + 1 by omega]; rfl

omit [DecidableEq α] [Inhabited α] in
private theorem drop_cons_pos (z : α) (zs : List α) {i : ℤ} (hi : 0 < i) :
    drop i (z :: zs) = drop (i - 1) zs := by
  simp only [drop]; rw [show i.toNat = (i - 1).toNat + 1 by omega]; rfl

/-- Not an EasyCrypt lemma: the common prefix of a truncated list. -/
theorem prefix_take_min (l1 l2 : List α) (i : ℤ) :
    «prefix» (take i l1) l2 = min («prefix» l1 l2) (max i 0) := by
  induction l1 generalizing l2 i with
  | nil => simp [take, prefix0s]
  | cons x l1 ih =>
    rcases le_or_gt i 0 with hi | hi
    · rw [show take i (x :: l1) = [] by simp [take, Int.toNat_eq_zero.mpr hi], prefix0s]
      have := prefix_ge0 (x :: l1) l2
      omega
    · rw [take_cons_pos x l1 hi]
      cases l2 with
      | nil => rw [prefixs0, prefixs0]; omega
      | cons y l2 =>
        simp only [«prefix», ih]
        split_ifs <;> omega

theorem prefix_cat (l l1 l2 : List α) : «prefix» (l ++ l1) (l ++ l2) = size l + «prefix» l1 l2 := by
  induction l with
  | nil => simp [size]
  | cons x l ih => simp [«prefix», ih, size]; ring

theorem prefix_leq_take (l1 l2 : List α) (i : ℤ) :
    0 ≤ i ∧ i ≤ min (size l1) (size l2) → take i l1 = take i l2 → i ≤ «prefix» l1 l2 := by
  induction l1 generalizing l2 i with
  | nil => rintro ⟨h0, hi⟩ -; simp [size] at hi; simp [prefix0s]; omega
  | cons x l1 ih =>
    rintro ⟨h0, hi⟩ ht
    cases l2 with
    | nil => simp [size] at hi; simp [prefixs0]; omega
    | cons y l2 =>
      rcases (show i = 0 ∨ 0 < i by omega) with rfl | hpos
      · exact prefix_ge0 _ _
      · have hti : ∀ (z : α) (zs : List α), take i (z :: zs) = z :: take (i - 1) zs := by
          intro z zs; simp only [take]; rw [show i.toNat = (i - 1).toNat + 1 by omega]; rfl
        rw [hti, hti] at ht
        obtain ⟨rfl, ht'⟩ := List.cons.inj ht
        simp only [«prefix», if_true, size, List.length_cons] at hi ⊢
        have := ih l2 (i - 1) ⟨by omega, by simp only [size]; omega⟩ ht'
        omega

theorem prefix0 (l1 l2 : List α) :
    «prefix» l1 l2 = 0 ↔ l1 = [] ∨ l2 = [] ∨ head default l1 ≠ head default l2 := by
  cases l1 with
  | nil => simp [prefix0s]
  | cons x l1 =>
    cases l2 with
    | nil => simp [prefixs0]
    | cons y l2 =>
      simp only [«prefix», head, List.headD_cons, reduceCtorEq, false_or]
      split_ifs with h
      · have := prefix_ge0 l1 l2; simp [h]; omega
      · simp [h]

theorem head_nth0 (l : List α) : head default l = nth default l 0 := by
  cases l <;> simp [head, nth]

theorem get_prefix (l1 l2 : List α) (i : ℤ) :
    0 ≤ i ∧ i ≤ min (size l1) (size l2) →
    (drop i l1 = [] ∨ drop i l2 = [] ∨
      (i < min (size l1) (size l2) ∧ nth default l1 i ≠ nth default l2 i)) →
    take i l1 = take i l2 → i = «prefix» l1 l2 := by
  induction l1 generalizing l2 i with
  | nil => rintro ⟨h0, hi⟩ - -; simp [size] at hi; simp [prefix0s]; omega
  | cons x l1 ih =>
    rintro ⟨h0, hi⟩ hd ht
    cases l2 with
    | nil => simp [size] at hi; simp [prefixs0]; omega
    | cons y l2 =>
      rcases (show i = 0 ∨ 0 < i by omega) with rfl | hpos
      · simp only [drop, Int.toNat_zero, List.drop_zero, reduceCtorEq, false_or, nth,
          le_refl, if_true, List.getD_cons_zero] at hd
        simp only [«prefix»]
        rw [if_neg hd.2]
      · have hti : ∀ (z : α) (zs : List α), take i (z :: zs) = z :: take (i - 1) zs := by
          intro z zs; simp only [take]; rw [show i.toNat = (i - 1).toNat + 1 by omega]; rfl
        have hdi : ∀ (z : α) (zs : List α), drop i (z :: zs) = drop (i - 1) zs := by
          intro z zs; simp only [drop]; rw [show i.toNat = (i - 1).toNat + 1 by omega]; rfl
        have hni : ∀ (z : α) (zs : List α), nth default (z :: zs) i = nth default zs (i - 1) := by
          intro z zs; simp only [nth, if_pos (le_of_lt hpos), if_pos (show 0 ≤ i - 1 by omega)]
          rw [show i.toNat = (i - 1).toNat + 1 by omega]; rfl
        rw [hti, hti] at ht
        obtain ⟨rfl, ht'⟩ := List.cons.inj ht
        rw [hdi, hdi, hni, hni] at hd
        simp only [«prefix», if_true, size, List.length_cons] at hi hd ⊢
        have := ih l2 (i - 1) ⟨by omega, by simp only [size]; omega⟩
          (by rcases hd with h | h | ⟨h1, h2⟩
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr ⟨by simp only [size]; omega, h2⟩)) ht'
        omega

theorem get_max_prefix_leq (l1 l2 : List α) (ll : List (List α)) :
    «prefix» l1 l2 ≤ «prefix» l1 (max_prefix l1 l2 ll) := by
  induction ll generalizing l2 with
  | nil => exact le_refl _
  | cons l' ll' ih =>
    simp only [max_prefix]
    split_ifs with h
    · exact le_trans (le_of_lt h) (ih l')
    · exact ih l2

theorem get_max_prefix_is_max (l1 l2 : List α) (ll : List (List α)) :
    ∀ l3, l3 ∈ ll → «prefix» l1 l3 ≤ «prefix» l1 (max_prefix l1 l2 ll) := by
  induction ll generalizing l2 with
  | nil => intro l3 h; simp at h
  | cons l' ll' ih =>
    intro l3 h3
    simp only [max_prefix]
    rcases List.mem_cons.mp h3 with rfl | h3
    · split_ifs with h
      · exact get_max_prefix_leq _ _ _
      · exact le_trans (not_lt.mp h) (get_max_prefix_leq _ _ _)
    · split_ifs
      · exact ih l' l3 h3
      · exact ih l2 l3 h3

theorem get_max_prefix_max (l : List α) (ll : List (List α)) :
    ∀ l2, l2 ∈ ll → «prefix» l l2 ≤ «prefix» l (get_max_prefix l ll) := by
  intro l2 h2
  cases ll with
  | nil => simp at h2
  | cons l' ll' =>
    simp only [get_max_prefix]
    rcases List.mem_cons.mp h2 with rfl | h2
    · exact get_max_prefix_leq _ _ _
    · exact get_max_prefix_is_max _ _ _ _ h2

end Generic3

theorem all_take_in (l : List block) (i : ℤ) (prefixes : FMap (List block) state) :
    0 ≤ i ∧ i ≤ size l → all_prefixes prefixes → FMap.dom prefixes (take i l) →
    i ≤ «prefix» l (get_max_prefix l (elems (FMap.fdom prefixes))) := by
  rintro ⟨h0, hi⟩ - hdom
  have h1 := get_max_prefix_max l _ _ ((mem_elems_fdom _ _).mpr hdom)
  rw [prefixC, prefix_take_min, prefix_eq] at h1
  omega

theorem prefix_inv_leq (l : List block) (i : ℤ) (prefixes : FMap (List block) state)
    (queries : FMap (List block) block) :
    0 ≤ i ∧ i ≤ size l → elems (FMap.fdom queries) ≠ [] → all_prefixes prefixes →
    FMap.dom prefixes (take i l) → prefix_inv queries prefixes →
    i ≤ «prefix» l (get_max_prefix l (elems (FMap.fdom queries))) := by
  rintro ⟨h0, hi⟩ - - hdom ⟨-, -, hex⟩
  by_cases ht : take i l = []
  · have hi0 : i = 0 := by
      simp only [take, List.take_eq_nil_iff] at ht
      rcases ht with ht | rfl
      · omega
      · simp [size] at hi; omega
    have := prefix_ge0 l (get_max_prefix l (elems (FMap.fdom queries)))
    omega
  · obtain ⟨l2, hl2⟩ := hex l i ht hdom
    have h1 := get_max_prefix_max l _ _ ((mem_elems_fdom _ _).mpr hl2)
    have h2 := prefix_take_min (take i l ++ l2) l (size (take i l))
    have hk : ∀ a b : List block, take (size a) (a ++ b) = a := fun a b => by simp [take, size]
    rw [hk, prefix_take_min, prefix_eq] at h2
    rw [prefixC] at h1
    omega

section Generic4

variable {α : Type} [DecidableEq α] [Inhabited α]
omit [Params]

theorem max_prefix_eq (l : List α) (ll : List (List α)) : max_prefix l l ll = l := by
  induction ll with
  | nil => rfl
  | cons l' ll ih =>
    simp only [max_prefix]
    rw [if_neg (by rw [prefix_eq]; exact not_lt.mpr (prefix_sizel _ _))]
    exact ih

theorem prefix_max_prefix_eq_size (l1 l2 : List α) (ll : List (List α)) :
    l1 = l2 ∨ l1 ∈ ll → «prefix» l1 (max_prefix l1 l2 ll) = size l1 := by
  intro h
  apply le_antisymm (prefix_sizel _ _)
  rcases h with rfl | h
  · rw [max_prefix_eq, prefix_eq]
  · have := get_max_prefix_is_max l1 l2 ll l1 h
    rwa [prefix_eq] at this

theorem prefix_get_max_prefix_eq_size (l : List α) (ll : List (List α)) :
    l ∈ ll → «prefix» l (get_max_prefix l ll) = size l := by
  intro h
  apply le_antisymm (prefix_sizel _ _)
  have := get_max_prefix_max l ll l h
  rwa [prefix_eq] at this

theorem get_max_prefix_exists (l : List α) (ll : List (List α)) :
    ll ≠ [] → ∃ l2, take («prefix» l (get_max_prefix l ll)) l ++ l2 ∈ ll := by
  intro hne
  refine ⟨drop («prefix» l (get_max_prefix l ll)) (get_max_prefix l ll), ?_⟩
  rw [prefix_take, cat_take_drop]
  exact mem_get_max_prefix l ll hne

theorem prefix_geq (l1 l2 : List α) :
    «prefix» l1 l2 = «prefix» (take («prefix» l1 l2) l1) (take («prefix» l1 l2) l2) := by
  have h1 := prefix_take_min l1 (take («prefix» l1 l2) l2) («prefix» l1 l2)
  have h2 := prefix_take_min l2 l1 («prefix» l1 l2)
  rw [prefixC (take _ l2) l1, prefixC l2 l1] at h2
  have := prefix_ge0 l1 l2
  omega

theorem prefix_take_prefix (l1 l2 : List α) :
    «prefix» (take («prefix» l1 l2) l1) l2 = «prefix» l1 l2 := by
  rw [prefix_take_min]
  have := prefix_ge0 l1 l2
  omega

theorem prefix_leq_prefix_cat (l1 l2 l3 : List α) : «prefix» l1 l2 ≤ «prefix» (l1 ++ l3) l2 := by
  have h := prefix_take_min (l1 ++ l3) l2 (size l1)
  rw [show take (size l1) (l1 ++ l3) = l1 by simp [take, size]] at h
  omega

theorem prefix_take_leq_prefix (l1 l2 : List α) (i : ℤ) :
    «prefix» (take i l1) l2 ≤ «prefix» l1 l2 := by
  rw [prefix_take_min]
  omega

theorem prefix_take_geq_prefix (l1 l2 : List α) (i : ℤ) :
    «prefix» l1 l2 ≤ i → «prefix» l1 l2 = «prefix» (take i l1) l2 := by
  intro h
  rw [prefix_take_min]
  have := prefix_ge0 l1 l2
  omega

/-- Not an EasyCrypt lemma: `max_prefix` depends on its first argument only through the common
prefixes with the candidates. -/
theorem max_prefix_congr (l1 l1' l2 : List α) (ll : List (List α))
    (h : ∀ l', l' = l2 ∨ l' ∈ ll → «prefix» l1 l' = «prefix» l1' l') :
    max_prefix l1 l2 ll = max_prefix l1' l2 ll := by
  induction ll generalizing l2 with
  | nil => rfl
  | cons l3 ll ih =>
    simp only [max_prefix]
    rw [h l2 (Or.inl rfl), h l3 (Or.inr List.mem_cons_self)]
    split_ifs
    · exact ih l3 fun l' hl' => h l' (Or.inr (by
        rcases hl' with rfl | hl'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ hl'))
    · exact ih l2 fun l' hl' => h l' (hl'.imp_right (List.mem_cons_of_mem _))

theorem get_max_prefix_take (l : List α) (ll : List (List α)) (i : ℤ) :
    «prefix» l (get_max_prefix l ll) ≤ i → get_max_prefix l ll = get_max_prefix (take i l) ll := by
  intro hi
  cases ll with
  | nil => rfl
  | cons l2 ll =>
    simp only [get_max_prefix] at hi ⊢
    have h0 := prefix_ge0 l (max_prefix l l2 ll)
    apply max_prefix_congr
    intro l' hl'
    have hle : «prefix» l l' ≤ «prefix» l (max_prefix l l2 ll) := by
      rcases hl' with rfl | hl'
      · exact get_max_prefix_leq _ _ _
      · exact get_max_prefix_is_max _ _ _ _ hl'
    rw [prefix_take_min]
    omega

theorem drop_prefix_neq (l1 l2 : List α) :
    drop («prefix» l1 l2) l1 = [] ∨ drop («prefix» l1 l2) l1 ≠ drop («prefix» l1 l2) l2 := by
  induction l1 generalizing l2 with
  | nil => left; simp [drop]
  | cons x l1 ih =>
    cases l2 with
    | nil => right; simp [prefixs0, drop]
    | cons y l2 =>
      simp only [«prefix»]
      split_ifs with h
      · have h0 := prefix_ge0 l1 l2
        rw [drop_cons_pos _ _ (by omega), drop_cons_pos _ _ (by omega), add_sub_cancel_left]
        exact ih l2
      · right; simp [drop, h]

theorem prefix_prefix_prefix (l1 l2 l3 : List α) (ll : List (List α)) :
    «prefix» l1 l2 ≤ «prefix» l1 l3 →
    «prefix» l1 (max_prefix l1 l2 ll) ≤ «prefix» l1 (max_prefix l1 l3 ll) := by
  induction ll generalizing l2 l3 with
  | nil => exact id
  | cons l4 ll ih =>
    intro h
    simp only [max_prefix]
    split_ifs <;> first | exact le_refl _ | exact ih _ _ (by omega)

theorem prefix_lt_size (l : List α) (ll : List (List α)) :
    «prefix» l (get_max_prefix l ll) < size l →
    ∀ i, «prefix» l (get_max_prefix l ll) < i → take i l ∉ ll := by
  intro hp i hi hmem
  have h1 := get_max_prefix_max l ll _ hmem
  rw [prefixC, prefix_take_min, prefix_eq] at h1
  omega

end Generic4

theorem asfadst (queries : FMap (List block) block) (prefixes : FMap (List block) state)
    (bs : List block) :
    prefix_inv queries prefixes → elems (FMap.fdom queries) ≠ [] → all_prefixes prefixes →
    (∀ j, 0 ≤ j ∧ j ≤ size bs → FMap.dom prefixes (take j bs)) →
    take («prefix» bs (get_max_prefix bs (elems (FMap.fdom queries))) + 1) bs = bs := by
  intro hinv hne hall hj
  have h := prefix_inv_leq bs (size bs) prefixes queries ⟨by simp [size], le_refl _⟩ hne hall
    (hj _ ⟨by simp [size], le_refl _⟩) hinv
  simp only [take]
  apply List.take_of_length_le
  simp only [size] at h
  omega

theorem prefix_exchange_prefix_inv {α : Type} [DecidableEq α] [Inhabited α]
    (ll1 ll2 : List (List α)) (l : List α) :
    (∀ l2, l2 ∈ ll1 → l2 ∈ ll2) →
    (∀ l2 : List α, l2 ∈ ll1 → ∀ i, take i l2 ∈ ll2) →
    (∀ l2, l2 ∈ ll2 → ∃ l3, l2 ++ l3 ∈ ll1) →
    «prefix» l (get_max_prefix l ll1) = «prefix» l (get_max_prefix l ll2) := by
  intro h1 _ h3
  by_cases hne : ll1 = []
  · subst hne
    have : ll2 = [] := List.eq_nil_iff_forall_not_mem.mpr fun l2 hl2 => by
      obtain ⟨l3, h⟩ := h3 l2 hl2; simp at h
    subst this; rfl
  · have hm1 := mem_get_max_prefix l ll1 hne
    have hm2 := mem_get_max_prefix l ll2 (List.ne_nil_of_mem (h1 _ hm1))
    obtain ⟨l3, hl3⟩ := h3 _ hm2
    have a := get_max_prefix_max l ll2 _ (h1 _ hm1)
    have b := get_max_prefix_max l ll1 _ hl3
    have c := prefix_leq_prefix_cat (get_max_prefix l ll2) l l3
    rw [prefixC (get_max_prefix l ll2) l, prefixC (get_max_prefix l ll2 ++ l3) l] at c
    omega

theorem prefix_inv_nil (queries : FMap (List block) block) (prefixes : FMap (List block) state) :
    prefix_inv queries prefixes → elems (FMap.fdom queries) = [] →
    FMap.fdom prefixes ⊆ fset1 [] := by
  rintro ⟨-, -, h3⟩ hq x hx
  simp only [fset1, Finset.mem_singleton]
  by_contra hne
  obtain ⟨l2, hl2⟩ := h3 x (size x) (by rwa [take_size]) (by rw [take_size]; exact hx)
  have := (mem_elems_fdom queries _).mpr hl2
  rw [hq] at this
  simp at this

theorem aux_prefix_exchange (queries : FMap (List block) block)
    (prefixes : FMap (List block) state) (l : List block) :
    prefix_inv queries prefixes → all_prefixes prefixes → elems (FMap.fdom queries) ≠ [] →
    «prefix» l (get_max_prefix l (elems (FMap.fdom queries))) =
      «prefix» l (get_max_prefix l (elems (FMap.fdom prefixes))) := by
  rintro ⟨-, h2, h3⟩ - h4
  apply prefix_exchange_prefix_inv
  · intro l2 hl2
    rw [mem_elems_fdom] at hl2 ⊢
    simpa only [take_size] using h2 l2 hl2 (size l2)
  · intro l2 hl2 i
    rw [mem_elems_fdom] at hl2 ⊢
    exact h2 l2 hl2 i
  · intro l2 hl2
    rw [mem_elems_fdom] at hl2
    by_cases hnil : l2 = []
    · subst hnil
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ h4
      exact ⟨q, by simpa using hq⟩
    · obtain ⟨l3, hl3⟩ := h3 l2 (size l2) (by rwa [take_size]) (by rwa [take_size])
      rw [take_size] at hl3
      exact ⟨l3, (mem_elems_fdom _ _).mpr hl3⟩

theorem prefix_exchange (queries : FMap (List block) block) (prefixes : FMap (List block) state)
    (l : List block) :
    prefix_inv queries prefixes → all_prefixes prefixes →
    «prefix» l (get_max_prefix l (elems (FMap.fdom queries))) =
      «prefix» l (get_max_prefix l (elems (FMap.fdom prefixes))) := by
  intro hinv hall
  by_cases h4 : elems (FMap.fdom queries) = []
  · have h6 := prefix_inv_nil queries prefixes hinv h4
    rw [h4]
    simp only [fset1] at h6
    rcases Finset.subset_singleton_iff.mp h6 with h | h <;>
      simp [h, elems, get_max_prefix, max_prefix]
  · exact aux_prefix_exchange queries prefixes l hinv hall h4

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
  intro h
  cases ll with
  | nil => simp [get_max_prefix, prefixs0] at h
  | cons l' ll' => exact mem_get_max_prefix _ _ (List.cons_ne_nil _ _)

theorem inv_prefix_block_mem_take (queries prefixes : FMap (List block) block) (l : List block)
    (i : ℤ) :
    inv_prefix_block queries prefixes →
    0 < i ∧ i < «prefix» l (get_max_prefix l (elems (FMap.fdom queries))) →
    FMap.dom prefixes (take i l) := by
  rintro ⟨-, hall⟩ ⟨h0, hi⟩
  have hmem := prefix_gt0_mem l (elems (FMap.fdom queries)) (by omega)
  rw [mem_elems_fdom] at hmem
  rw [prefix_take_leq l _ i (le_of_lt hi)]
  exact hall _ hmem i ⟨h0, le_trans (le_of_lt hi) (prefix_sizer _ _)⟩

section Generic5

variable {α : Type} [DecidableEq α] [Inhabited α]
omit [Params]

theorem prefix_cat_leq_prefix_size (l1 l2 l3 : List α) :
    «prefix» (l1 ++ l2) l3 ≤ «prefix» l1 l3 + size l2 := by
  induction l1 generalizing l3 with
  | nil => simpa [prefix0s] using prefix_sizel l2 l3
  | cons x l1 ih =>
    cases l3 with
    | nil => simp [prefixs0, size]
    | cons y l3 =>
      simp only [List.cons_append, «prefix»]
      split_ifs
      · linarith [ih l3]
      · simp [size]

theorem prefix_cat1 (l1 l2 l3 : List α) :
    «prefix» (l1 ++ l2) l3 =
      «prefix» l1 l3 + if «prefix» l1 l3 = size l1 then «prefix» l2 (drop (size l1) l3) else 0 := by
  induction l1 generalizing l3 with
  | nil => simp [prefix0s, size, drop]
  | cons x l1 ih =>
    have hs : size (x :: l1) = size l1 + 1 := by simp [size]
    cases l3 with
    | nil =>
      rw [List.cons_append, prefixs0, prefixs0, if_neg (by have := prefix_ge0 l1 l1; simp [size]; omega)]
      simp
    | cons y l3 =>
      simp only [List.cons_append, «prefix»]
      have hs0 : (0 : ℤ) ≤ size l1 := by simp [size]
      have hd : drop (size (x :: l1)) (y :: l3) = drop (size l1) l3 := by
        rw [hs, drop_cons_pos _ _ (by omega), add_sub_cancel_right]
      have h0 := prefix_ge0 l1 l3
      by_cases hxy : x = y
      · rw [hd]
        simp only [if_pos hxy, ih, hs]
        split_ifs <;> omega
      · simp only [if_neg hxy, hs]
        split_ifs <;> omega

theorem prefix_leq_prefix_cat_size (l1 l2 : List α) (ll : List (List α)) :
    «prefix» (l1 ++ l2) (get_max_prefix (l1 ++ l2) ll) ≤
      «prefix» l1 (get_max_prefix l1 ll) +
        if «prefix» l1 (get_max_prefix l1 ll) = size l1 then
          «prefix» l2 (get_max_prefix l2 (ll.map (drop (size l1))))
        else 0 := by
  cases ll with
  | nil => simp [get_max_prefix, prefixs0]
  | cons l' ll' =>
    have hm := mem_get_max_prefix (l1 ++ l2) (l' :: ll') (List.cons_ne_nil _ _)
    have hq := get_max_prefix_max l1 (l' :: ll') _ hm
    have hqs := prefix_sizel l1 (get_max_prefix l1 (l' :: ll'))
    have hr := get_max_prefix_max l2 ((l' :: ll').map (drop (size l1))) _
      (List.mem_map_of_mem (f := drop (size l1)) hm)
    have h0 := prefix_ge0 l2 (get_max_prefix l2 ((l' :: ll').map (drop (size l1))))
    rw [prefix_cat1]
    split_ifs <;> omega

theorem diff_size_prefix_leq_cat (l1 l2 : List α) (ll : List (List α)) :
    size l1 - «prefix» l1 (get_max_prefix l1 ll) ≤
      size (l1 ++ l2) - «prefix» (l1 ++ l2) (get_max_prefix (l1 ++ l2) ll) := by
  have h := prefix_leq_prefix_cat_size l1 l2 ll
  have hs : size (l1 ++ l2) = size l1 + size l2 := by simp [size]
  have h2 := prefix_sizel l2 (get_max_prefix l2 (ll.map (drop (size l1))))
  have h3 : (0 : ℤ) ≤ size l2 := by simp [size]
  split_ifs at h <;> omega

end Generic5

def invm {α β : Type} [DecidableEq α] [DecidableEq β] (m mi : FMap (α × β) (α × β)) : Prop :=
  ∀ x y, FMap.get m x = some y ↔ FMap.get mi y = some x

omit [Params] in
theorem invm_set {α β : Type} [DecidableEq α] [DecidableEq β] (m mi : FMap (α × β) (α × β))
    (x y : α × β) :
    ¬ FMap.dom m x → ¬ FMap.rng m y → invm m mi → invm (FMap.set m x y) (FMap.set mi y x) := by
  intro hx hy hinv a b
  rw [FMap.get_setE, FMap.get_setE]
  rcases eq_or_ne a x with hax | hax <;> rcases eq_or_ne b y with hby | hby
  · subst hax hby; simp
  · subst hax
    rw [if_pos rfl, if_neg hby]
    constructor
    · intro h; exact absurd (Option.some.inj h).symm hby
    · intro h
      exact absurd ((FMap.domE _ _).mpr (by rw [(hinv a b).mpr h]; simp)) hx
  · subst hby
    rw [if_neg hax, if_pos rfl]
    constructor
    · intro h; exact absurd ⟨a, h⟩ hy
    · intro h; exact absurd (Option.some.inj h).symm hax
  · rw [if_neg hax, if_neg hby]
    exact hinv a b

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

theorem DRestr_ll (D : DISTINGUISHER) (_hD : FVP.fvP D ≤ C.footprintᶜ) :
    (∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP D).globᶜ →
      FVP.fvP P ≤ (FVP.fvP D).globᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app D (Module.pair F P)).procedure.IsLossless) →
    ∀ (F : DFUNCTIONALITY) (P : DPRIMITIVE), FVP.fvP F ≤ (FVP.fvP (DRestr D)).globᶜ →
      FVP.fvP P ≤ (FVP.fvP (DRestr D)).globᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app (DRestr D) (Module.pair F P)).procedure.IsLossless := by
  sorry

section RESTR

variable (F : FUNCTIONALITY) (P : PRIMITIVE) (D : DISTINGUISHER)

/-- `declare module F <: FUNCTIONALITY{-C, -Redo}`, `P <: PRIMITIVE{-C, -F, -Redo}`,
`D <: DISTINGUISHER{-F, -P, -C, -Redo}`. -/
theorem swap_restr (hD : Module.ECModule D (distExt))
    (_hF : FVP.fvP F ≤ (C.footprint ⊔ (Redo.prefixes).footprint)ᶜ)
    (_hP : FVP.fvP P ≤ (C.footprint ⊔ (FVP.fvP F).glob ⊔ (Redo.prefixes).footprint)ᶜ)
    (_hDd : FVP.fvP D ≤ ((FVP.fvP F).glob ⊔ (FVP.fvP P).glob ⊔ C.footprint ⊔
      (Redo.prefixes).footprint)ᶜ)
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
theorem Pr_restr (hD : Module.ECModule D (distExt))
    (_hP : FVP.fvP P ≤ C.footprintᶜ)
     (_hCO : FVP.fvP CO ≤ (C.footprint ⊔ (FVP.fvP P).glob)ᶜ)
    (_hDd : FVP.fvP D ≤ (C.footprint ⊔ (FVP.fvP P).glob ⊔ (FVP.fvP CO).glob)ᶜ)
    (f_ll : (Indifferentiability.PRIMITIVE.f state (List block) block P).procedure.IsLossless)
    (fi_ll : (Indifferentiability.PRIMITIVE.fi state (List block) block P).procedure.IsLossless)
    (CO_ll : (Indifferentiability.FUNCTIONALITY.f state (List block) block
      (Module.app CO (Indifferentiability.PRIMITIVE.view state (List block) block P))
      ).procedure.IsLossless)
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
  unfold hinv
  rcases FMap.findP (fun _ cf => decide (cf.1 = c)) handles with ⟨hn, hall⟩ | ⟨x, y, hf, hg, hp⟩
  · rw [if_pos hn]
    intro h f hh
    simpa using hall h _ hh
  · rw [hf, if_neg (by simp)]
    simp only [decide_eq_true_eq] at hp
    exact ⟨y.2, by simp [oget, hg, ← hp]⟩

theorem huniq_hinv (handles : handles) (h : handle) :
    huniq handles → FMap.dom handles h →
    hinv handles (oget (FMap.get handles h)).1 = some h := by
  intro hu hd
  obtain ⟨cf, hcf⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd)
  rw [hcf]
  simp only [oget, Option.getD_some]
  have hp := hinvP handles cf.1
  split_ifs at hp with hn
  · exact absurd hcf (hp h cf.2)
  · obtain ⟨f, hf⟩ := hp
    obtain ⟨h', hh'⟩ := Option.ne_none_iff_exists'.mp hn
    rw [hh'] at hf ⊢
    simp only [oget, Option.getD_some] at hf
    rw [hu h' h (cf.1, f) cf hf hcf rfl]

theorem hinvKP (handles : handles) (c : capacity) :
    if hinvK handles c = none then ∀ h, FMap.get handles h ≠ some (c, Known)
    else FMap.get handles (oget (hinvK handles c)) = some (c, Known) := by
  unfold hinvK
  rcases FMap.findP (fun _ c' => decide (c' = c)) (FMap.restr Known handles) with
    ⟨hn, hall⟩ | ⟨x, y, hf, hg, hp⟩
  · rw [if_pos hn]
    intro h hh
    simpa using hall h c (by rw [FMap.restrP, hh]; simp)
  · rw [hf, if_neg (by simp)]
    simp only [decide_eq_true_eq] at hp
    subst hp
    rw [FMap.restrP] at hg
    obtain ⟨⟨a, f⟩, hx, hb⟩ := Option.bind_eq_some_iff.mp hg
    split_ifs at hb with hfk
    obtain rfl := Option.some.inj hb
    subst hfk
    simpa [oget] using hx

theorem huniq_hinvK (handles : handles) (c : capacity) :
    huniq handles → FMap.rng handles (c, Known) →
    FMap.get handles (oget (hinvK handles c)) = some (c, Known) := by
  rintro - ⟨h, hh⟩
  have hp := hinvKP handles c
  split_ifs at hp
  · exact absurd hh (hp h)
  · exact hp

theorem huniq_hinvK_h (h : handle) (handles : handles) (c : capacity) :
    huniq handles → FMap.get handles h = some (c, Known) → hinvK handles c = some h := by
  intro hu hh
  have hp := hinvKP handles c
  split_ifs at hp with hn
  · exact absurd hh (hp h)
  · obtain ⟨h', hh'⟩ := Option.ne_none_iff_exists'.mp hn
    rw [hh'] at hp ⊢
    simp only [oget, Option.getD_some] at hp
    rw [hu h' h _ _ hp hh rfl]

/-! ## The initial game -/

/-- `module GReal(D : DISTINGUISHER) = RealIndif(SqueezelessSponge, PC(Perm), D)`. -/
noncomputable def GReal (D : DISTINGUISHER) : procmod () → Bool :=
  RealIndif SqueezelessSponge (Module.app PC Perm) D

end GaudisCrypt.SHA3.SLCommon
