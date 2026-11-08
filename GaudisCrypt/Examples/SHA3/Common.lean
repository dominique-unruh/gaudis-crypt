import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Lib.EC.BitWord
import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Lib.EC.PRP

/-!
# SHA-3: common definitions and lemmas (EasyCrypt `proof/Common.ec`)

The sponge's rate `r` and capacity `c`; blocks and capacities as bit words; the ideal
permutation `Perm`; padding, chunking and the conversions between bits and blocks; the validity
predicates.

The mapping conventions are in `notes/SHA3/README.md`, the declaration-by-declaration status in
`notes/SHA3/Mapping.md`.  In this file:
* `op r : { int | 2 <= r } as ge2_r` and `op c : { int | 0 < c } as gt0_c` (abstract constants
  with axioms) are the fields of the parameter class `Params`.  Every later file takes
  `[Common.Params]`.
* `clone export BitWord as Block with op n <- r rename "word" as "block" …` is the namespace
  `Block` of abbreviations at `n := r`, exported; `Capacity` likewise.
* `clone export PRP as PRPt with type D <- block * capacity`, `clone export StrongPRP as PRPSec`
  and `clone export RP as Perm with op dD <- bdistr \`*\` cdistr` are applications of
  `GaudisCrypt/Lib/EC/PRP.lean` at `D := block × capacity`.
* `int` is `ℤ`, `%/`, `%%`, `%|` are `/`, `%`, `∣` (EasyCrypt's division is Euclidean, as Lean's
  on `ℤ`), and list operations on `int` are those of `GaudisCrypt/Lib/EC/List.lean`.
-/

namespace GaudisCrypt.SHA3.Common

open GaudisCrypt GaudisCrypt.EC

/-- EasyCrypt's abstract constants `op r : { int | 2 <= r } as ge2_r` and
`op c : { int | 0 < c } as gt0_c`. -/
class Params where
  r : ℤ
  c : ℤ
  ge2_r : 2 ≤ r
  gt0_c : 0 < c

variable [Params]

/-- `op r`: the rate. -/
def r : ℤ := Params.r
/-- `op c`: the capacity. -/
def c : ℤ := Params.c

theorem ge2_r : 2 ≤ r := Params.ge2_r
theorem gt0_c : 0 < c := Params.gt0_c

/-! ## -/

theorem gt0_r : 0 < r := lt_of_lt_of_le (by norm_num) ge2_r

theorem ge0_r : 0 ≤ r := le_of_lt gt0_r

theorem ge0_c : 0 ≤ c := le_of_lt gt0_c

/-! ## `clone export BitWord as Capacity` and `clone export BitWord as Block` -/

namespace Capacity
/-- `capacity` (`word` at `n := c`). -/
abbrev capacity := BitWord.word c
def mkcapacity : List Bool → capacity := BitWord.mkword
def ofcapacity : capacity → List Bool := BitWord.ofword
/-- `c0` (`zerow`). -/
def c0 : capacity := BitWord.zerow
namespace DCapacity
noncomputable def dunifin : SubProbability capacity := BitWord.dunifin
end DCapacity
end Capacity

export Capacity (capacity mkcapacity ofcapacity c0)

namespace Block
/-- `block` (`word` at `n := r`). -/
abbrev block := BitWord.word r
def mkblock : List Bool → block := BitWord.mkword
def ofblock : block → List Bool := BitWord.ofword
/-- `b0` (`zerow`). -/
def b0 : block := BitWord.zerow
namespace DBlock
noncomputable def dunifin : SubProbability block := BitWord.dunifin
end DBlock
/-- `blocks` (`enum`, the clone's `FinType` enumeration). -/
noncomputable def blocks : List block := (Finset.univ : Finset block).toList
end Block

export Block (block mkblock ofblock b0)

noncomputable def cdistr : SubProbability capacity := Capacity.DCapacity.dunifin
noncomputable def bdistr : SubProbability block := Block.DBlock.dunifin

/-! ## Auxiliary lemmas -/

theorem dvdz_close (n : ℤ) : r ∣ n → 0 < n ∧ n < 2 * r → n = r := by
  intro hd ⟨h0, h2⟩
  obtain ⟨m, rfl⟩ := hd
  have hr := gt0_r
  have hm0 : 0 < m := by
    by_contra h; push Not at h; nlinarith
  have hm2 : m < 2 := by
    by_contra h; push Not at h; nlinarith
  obtain rfl : m = 1 := by omega
  ring

omit [Params] in
theorem chunk_nil' {α : Type} (r : ℤ) : BitChunking.chunk r ([] : List α) = [] := by
  simp [BitChunking.chunk, size, mkseq, iota_]

omit [Params] in
theorem chunk_sing' (r : ℤ) (xs : List Bool) :
    0 < r → size xs = r → BitChunking.chunk r xs = [xs] := by
  intro h0 hs
  have hl : (xs.length : ℤ) = r := hs
  have hn : r.toNat = xs.length := by omega
  simp [BitChunking.chunk, mkseq, iota_, size, hl, Int.ediv_self (ne_of_gt h0), drop, take, hn]

theorem b0P : b0 = mkblock (nseq r false) := by
  apply List.Vector.ext
  intro i
  simp only [b0, mkblock, BitWord.zerow, BitWord.mkword, nseq, List.Vector.get_replicate,
    List.Vector.get_ofFn, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

theorem bits2w_inj_eq (cs ds : List Bool) :
    size cs = r → size ds = r → (mkblock cs = mkblock ds ↔ cs = ds) := by
  intro hc hd
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have hc' : cs.length = r.toNat := by have : (cs.length : ℤ) = r := hc; omega
  have hd' : ds.length = r.toNat := by have : (ds.length : ℤ) = r := hd; omega
  apply List.ext_getElem (hc'.trans hd'.symm)
  intro i h1 h2
  have := congrArg (fun w : block => w.get ⟨i, hc' ▸ h1⟩) h
  simpa [mkblock, BitWord.mkword, List.getD_eq_getElem?_getD, h1, h2] using this

omit [Params] in
theorem last_drop_all_but_last {α : Type} (y : α) (xs : List α) :
    xs = [] ∨ drop (size xs - 1) xs = [last y xs] := by
  rcases List.eq_nil_or_concat xs with h | ⟨ys, z, rfl⟩
  · exact Or.inl h
  · right
    simp [drop, size, last]

/-! ## The primitive: `clone export PRP as PRPt with type D <- block * capacity`,
`clone export StrongPRP as PRPSec`, `clone export RP as Perm with op dD <- bdistr \`*\` cdistr` -/

namespace PRPSec
abbrev PRP := EC.PRP.StrongPRP.PRP (block × capacity)
abbrev SPRP_Oracles := EC.PRP.StrongPRP.SPRP_Oracles (block × capacity)
abbrev Distinguisher := EC.PRP.StrongPRP.Distinguisher (block × capacity)
end PRPSec

/-- The `RP` clone's `op dD <- bdistr \`*\` cdistr`. -/
noncomputable abbrev dD : SubProbability (block × capacity) := dprod bdistr cdistr

/-- `realize dD_ll`. -/
theorem dD_ll : is_lossless dD := by
  exact dprod_ll BitWord.dunifin_ll BitWord.dunifin_ll

/-- `[module type] "PRP" as "PRIMITIVE"`. -/
abbrev PRIMITIVE := EC.PRP.StrongPRP.PRP (block × capacity)

/-- The clone's module variables `Perm.m`, `Perm.mi`. -/
global_var Perm.m : FMap (block × capacity) (block × capacity)
global_var Perm.mi : FMap (block × capacity) (block × capacity)

/-- `[module] "RP" as "Perm"`: the ideal permutation on `block * capacity`. -/
noncomputable abbrev Perm := EC.PRP.RP.RP (block × capacity) dD Perm.m Perm.mi

/-! ## Needed blocks computation -/

/-- Not an EasyCrypt lemma: `(n + r - 1) %/ r` is `n %/ r`, plus one unless `r` divides `n`. -/
theorem needed_blocks_eq (n : ℤ) :
    (n + r - 1) / r = n / r + if n % r = 0 then 0 else 1 := by
  have hr := gt0_r
  have hk0 := Int.emod_nonneg n (ne_of_gt hr)
  have hkr := Int.emod_lt_of_pos n hr
  have he : n + r - 1 = (n % r + r - 1) + n / r * r := by
    have := Int.emod_add_mul_ediv n r; linarith [mul_comm r (n / r)]
  rw [he, Int.add_mul_ediv_right _ _ (ne_of_gt hr)]
  split_ifs with h
  · rw [h, Int.ediv_eq_zero_of_lt (by linarith) (by linarith)]; ring
  · have : n % r + r - 1 = (n % r - 1) + 1 * r := by ring
    rw [this, Int.add_mul_ediv_right _ _ (ne_of_gt hr),
      Int.ediv_eq_zero_of_lt (by omega) (by linarith)]
    ring

theorem needed_blocks0 : (0 + r - 1) / r = 0 := by
  have hr := gt0_r
  exact Int.ediv_eq_zero_of_lt (by linarith) (by linarith)

theorem needed_blocks_non_pos (n : ℤ) : n ≤ 0 → (n + r - 1) / r ≤ 0 := by
  intro h
  have hr := gt0_r
  calc (n + r - 1) / r ≤ (r - 1) / r := Int.ediv_le_ediv hr (by linarith)
    _ = 0 := Int.ediv_eq_zero_of_lt (by linarith) (by linarith)

theorem needed_blocks_suff (n : ℤ) : n ≤ (n + r - 1) / r * r := by
  have hr := gt0_r
  have h1 := Int.emod_add_mul_ediv (n + r - 1) r
  have h2 := Int.emod_lt_of_pos (n + r - 1) hr
  nlinarith [mul_comm r ((n + r - 1) / r)]

theorem needed_blocks_correct (n : ℤ) :
    0 ≤ (n + r - 1) / r * r - n ∧ (n + r - 1) / r * r - n < r := by
  have hr := gt0_r
  have h1 := Int.emod_add_mul_ediv (n + r - 1) r
  have h2 := Int.emod_lt_of_pos (n + r - 1) hr
  have h3 := Int.emod_nonneg (n + r - 1) (ne_of_gt hr)
  constructor <;> nlinarith [mul_comm r ((n + r - 1) / r)]

theorem needed_blocks_prod_r (n : ℤ) : (n * r + r - 1) / r = n := by
  have hr := gt0_r
  have : n * r + r - 1 = (r - 1) + n * r := by ring
  rw [this, Int.add_mul_ediv_right _ _ (ne_of_gt hr),
    Int.ediv_eq_zero_of_lt (by linarith) (by linarith), zero_add]

theorem needed_blocks_eq_div_r (n : ℤ) : r ∣ n ↔ n / r = (n + r - 1) / r := by
  rw [needed_blocks_eq, Int.dvd_iff_emod_eq_zero]
  split_ifs with h <;> simp [h]

theorem needed_blocks_succ_eq_div_r (n : ℤ) : ¬ r ∣ n ↔ n / r + 1 = (n + r - 1) / r := by
  rw [needed_blocks_eq, Int.dvd_iff_emod_eq_zero]
  split_ifs with h <;> simp [h]

theorem needed_blocks_rel_div_r (n : ℤ) :
    n / r = (n + r - 1) / r ∨ n / r + 1 = (n + r - 1) / r := by
  rw [needed_blocks_eq]
  split_ifs <;> simp

/-! ## Padding/unpadding -/

def num0 (n : ℤ) : ℤ := (-(n + 2)) % r

def mkpad (n : ℤ) : List Bool := true :: rcons (nseq (num0 n) false) true

def pad (s : List Bool) : List Bool := s ++ mkpad (size s)

def unpad (s : List Bool) : Option (List Bool) :=
  if !last false s then none else
  let i := index true (behead s.reverse)
  if i + 1 = size s then none
  else
    let n := size s - (i + 2)
    if i = num0 n then some (take n s) else none

theorem rev_mkpad (n : ℤ) : (mkpad n).reverse = mkpad n := by
  simp [mkpad, rcons, nseq, List.reverse_replicate]

theorem last_mkpad (b : Bool) (n : ℤ) : last b (mkpad n) = true := by
  unfold last mkpad rcons
  rw [← List.cons_append]
  simp only [List.getLastD_concat]

theorem head_mkpad (b : Bool) (n : ℤ) : head b (mkpad n) = true := by
  simp [head, mkpad]

theorem last_pad (b : Bool) (s : List Bool) : last b (pad s) = true := by
  unfold last pad mkpad rcons
  rw [← List.cons_append, ← List.append_assoc]
  simp only [List.getLastD_concat]

theorem size_mkpad (n : ℤ) : size (mkpad n) = num0 n + 2 := by
  have h : 0 ≤ num0 n := Int.emod_nonneg _ (ne_of_gt gt0_r)
  simp [size, mkpad, rcons, nseq, Int.toNat_of_nonneg h]
  ring

theorem size_pad_equiv (m : ℤ) : 0 ≤ m → m + num0 m + 2 = (m + 1) / r * r + r := by
  intro _
  have hr := gt0_r
  have h1 := Int.emod_add_mul_ediv (m + 1) r
  have h2 := Int.emod_nonneg (m + 1) (ne_of_gt hr)
  have h3 := Int.emod_lt_of_pos (m + 1) hr
  have hn : num0 m = r - (m + 1) % r - 1 := by
    unfold num0
    have : -(m + 2) = (r - (m + 1) % r - 1) + (-((m + 1) / r) - 1) * r := by
      linarith [mul_comm r ((m + 1) / r)]
    rw [this, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by linarith) (by linarith)]
  rw [hn]
  linarith [mul_comm r ((m + 1) / r)]

theorem size_padE (s : List Bool) : size (pad s) = size s + num0 (size s) + 2 := by
  simp only [pad, size, List.length_append]
  push_cast
  have := size_mkpad (size s)
  simp only [size] at this
  rw [this]
  ring

theorem size_pad (s : List Bool) : size (pad s) = (size s + 1) / r * r + r := by
  rw [size_padE]
  exact size_pad_equiv _ (by simp [size])

theorem size_pad_dvd_r (s : List Bool) : r ∣ size (pad s) := by
  rw [size_padE]
  unfold num0
  have := Int.emod_add_mul_ediv (-(size s + 2)) r
  exact ⟨-((-(size s + 2)) / r), by linarith [mul_comm r ((-(size s + 2)) / r)]⟩

theorem dvd_r_num0 (m : ℤ) : r ∣ (m + num0 m + 2) := by
  unfold num0
  have := Int.emod_add_mul_ediv (-(m + 2)) r
  exact ⟨-((-(m + 2)) / r), by linarith [mul_comm r ((-(m + 2)) / r)]⟩

theorem num0_ge0 (m : ℤ) : 0 ≤ num0 m := by
  exact Int.emod_nonneg _ (ne_of_gt gt0_r)

theorem num0_ltr (m : ℤ) : num0 m < r := by
  exact Int.emod_lt_of_pos _ gt0_r

theorem index_true_behead_mkpad (n : ℤ) : index true (behead (mkpad n)) = num0 n := by
  simp only [index, behead, mkpad, rcons, nseq, List.tail_cons]
  rw [List.idxOf_append_of_notMem (by simp), List.length_replicate]
  exact Int.toNat_of_nonneg (num0_ge0 n)

theorem padE (s : List Bool) (n : ℤ) :
    0 ≤ n ∧ n < r → r ∣ (size s + n + 2) →
    pad s = s ++ [true] ++ nseq n false ++ [true] := by
  rintro ⟨h0, hr⟩ ⟨k, hk⟩
  have hn : num0 (size s) = n := by
    unfold num0
    have : -(size s + 2) = n + (-k) * r := by linarith [mul_comm r k]
    rw [this, Int.add_mul_emod_self_right, Int.emod_eq_of_lt h0 hr]
  simp [pad, mkpad, rcons, hn]

theorem padK : pcancel pad unpad := by
  intro t
  have hk := num0_ge0 (size t)
  have hrev : behead (pad t).reverse = nseq (num0 (size t)) false ++ true :: t.reverse := by
    simp [behead, pad, mkpad, rcons, nseq, List.reverse_replicate]
  have hidx : index true (behead (pad t).reverse) = num0 (size t) := by
    rw [hrev]
    simp only [index, nseq]
    rw [List.idxOf_append_of_notMem (by simp), List.length_replicate, List.idxOf_cons_self]
    simp [Int.toNat_of_nonneg hk]
  have hsz := size_padE t
  have hst : 0 ≤ size t := by simp [size]
  unfold unpad
  simp only [last_pad, Bool.not_true, Bool.false_eq_true, if_false, hidx, hsz]
  rw [if_neg (by omega), show size t + num0 (size t) + 2 - (num0 (size t) + 2) = size t by ring,
    if_pos rfl]
  simp [take, pad, size]

omit [Params] in
/-- Not an EasyCrypt lemma: a bit list with a `true` is `false`s, that `true`, and the rest. -/
theorem split_first_true :
    ∀ l : List Bool, l.idxOf true < l.length →
      l = List.replicate (l.idxOf true) false ++ true :: l.drop (l.idxOf true + 1)
  | [], h => by simp at h
  | true :: l, _ => by simp
  | false :: l, h => by
      have h' : l.idxOf true < l.length := by
        simp at h; omega
      have ih := split_first_true l h'
      simp only [List.idxOf_cons, List.drop_succ_cons]
      exact congrArg _ ih

/-- Not an EasyCrypt lemma: what `unpad` accepts is a padding. -/
theorem pad_of_unpad_some (t y : List Bool) (h : unpad t = some y) : t = pad y := by
  unfold unpad at h
  dsimp only at h
  split_ifs at h with h1 h2 h3
  obtain ⟨rfl⟩ := Option.some.inj h
  -- `t` ends with `true`
  obtain ⟨t', rfl⟩ : ∃ t', t = t' ++ [true] := by
    rcases List.eq_nil_or_concat t with rfl | ⟨t', z, rfl⟩
    · simp [last] at h1
    · refine ⟨t', ?_⟩
      have : z = true := by simpa [last] using h1
      rw [this, List.concat_eq_append]
  -- `behead (rev t) = rev t'`, and its first `true` lies inside it
  have hb : behead (t' ++ [true]).reverse = t'.reverse := by simp [behead]
  have hlen : size (t' ++ [true]) = (t'.length : ℤ) + 1 := by simp [size]
  rw [hb, hlen] at h2 h3
  rw [hb, hlen]
  set i := t'.reverse.idxOf true with hi
  have hidx : index true t'.reverse = (i : ℤ) := rfl
  rw [hidx] at h2 h3 ⊢
  have hil : i < t'.reverse.length := by
    have := List.idxOf_le_length (a := true) (l := t'.reverse)
    rw [← hi] at this
    rcases this.lt_or_eq with h | h
    · exact h
    · exfalso; apply h2; rw [h]; simp
  -- `rev t' = nseq i false ++ true :: u`
  set u := t'.reverse.drop (i + 1) with hu
  have hsplit : t'.reverse = List.replicate i false ++ true :: u := split_first_true _ hil
  have ht' : t' = u.reverse ++ true :: List.replicate i false := by
    have := congrArg List.reverse hsplit
    simpa [List.reverse_replicate] using this
  have hul : (t'.length : ℤ) = (u.length : ℤ) + i + 1 := by
    rw [ht']; simp; ring
  rw [show (t'.length : ℤ) + 1 - ((i : ℤ) + 2) = u.length by omega] at h3 ⊢
  rw [ht']
  have htake : take (u.length : ℤ) ((u.reverse ++ true :: List.replicate i false) ++ [true]) =
      u.reverse := by
    simp [take]
  rw [htake]
  simp only [pad, mkpad, rcons, nseq, size, List.length_reverse]
  rw [← h3]
  simp

theorem unpadK : ocancel unpad pad := by
  intro t
  cases h : unpad t with
  | none => trivial
  | some y => exact (pad_of_unpad_some t y h).symm

inductive unpad_spec (t : List Bool) : Prop where
  | Unpad (s : List Bool) (n : ℤ) :
      (0 ≤ n ∧ n < r) → r ∣ (size s + n + 2) → t = s ++ [true] ++ nseq n false ++ [true] →
      unpad_spec t

theorem unpadP (t : List Bool) : unpad t ≠ none ↔ unpad_spec t := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp h
    refine ⟨y, num0 (size y), ⟨num0_ge0 _, num0_ltr _⟩, dvd_r_num0 _, ?_⟩
    rw [pad_of_unpad_some t y hy]
    simp [pad, mkpad, rcons]
  · rintro ⟨s, n, hn, hd, rfl⟩
    rw [← padE s n hn hd, padK s]
    simp

/-! ## Chunking -/

def chunk (bs : List Bool) : List (List Bool) := BitChunking.chunk r bs

omit [Params] in
/-- Not an EasyCrypt lemma: fewer than `r` bits make no chunk. -/
theorem chunk_lt' {α : Type} (r : ℤ) (bs : List α) (h : size bs < r) :
    BitChunking.chunk r bs = [] := by
  have hs : 0 ≤ size bs := by simp [size]
  simp [BitChunking.chunk, mkseq, iota_, Int.ediv_eq_zero_of_lt hs h]

omit [Params] in
/-- Not an EasyCrypt lemma: at least `r` bits make a first chunk, then the chunks of the rest. -/
theorem chunk_cons' {α : Type} (r : ℤ) (bs : List α) (h0 : 0 < r) (h : r ≤ size bs) :
    BitChunking.chunk r bs = take r bs :: BitChunking.chunk r (drop r bs) := by
  have hs : size (drop r bs) = size bs - r := by
    simp only [size, drop, List.length_drop] at h ⊢; omega
  have hd : size bs / r = size (drop r bs) / r + 1 := by
    rw [hs, show size bs = (size bs - r) + 1 * r by ring, Int.add_mul_ediv_right _ _ (ne_of_gt h0)]
    ring_nf
  have hq : 0 ≤ size (drop r bs) / r := Int.ediv_nonneg (by simp [size]) (le_of_lt h0)
  unfold BitChunking.chunk
  rw [hd, mkseqSr _ _ hq]
  refine congrArg₂ _ (by simp [drop]) (eq_in_mkseq fun k hk _ => ?_)
  simp only [drop, List.drop_drop]
  congr 2
  have h1 : 0 ≤ r * k := mul_nonneg (le_of_lt h0) hk
  rw [mul_add, mul_one, Int.toNat_add (le_of_lt h0) h1, Nat.add_comm]

theorem size_chunk (bs : List Bool) : size (chunk bs) = size bs / r := by
  have : 0 ≤ size bs / r := Int.ediv_nonneg (by simp [size]) ge0_r
  rw [chunk, BitChunking.chunk, size_mkseq]
  omega

theorem in_chunk_size (bs b : List Bool) : b ∈ chunk bs → size b = r := by
  intro hb
  obtain ⟨i, hi0, hi, rfl⟩ := mem_mkseq.mp hb
  have hr := gt0_r
  have h1 : (i + 1) * r ≤ size bs := by
    have := Int.ediv_mul_le (size bs) (ne_of_gt hr)
    have : (i + 1) * r ≤ size bs / r * r := Int.mul_le_mul_of_nonneg_right (by omega) ge0_r
    linarith
  have h2 : 0 ≤ r * i := mul_nonneg ge0_r hi0
  have h1' : r * i + r ≤ size bs := by linarith
  have h3 : ((r * i).toNat : ℤ) = r * i := Int.toNat_of_nonneg h2
  have h4 : (r.toNat : ℤ) = r := Int.toNat_of_nonneg ge0_r
  simp only [size, take, drop, List.length_take, List.length_drop, Nat.cast_min] at h1' ⊢
  omega

theorem chunkK (bs : List Bool) : r ∣ size bs → (chunk bs).flatten = bs := by
  intro hd
  induction hn : bs.length using Nat.strong_induction_on generalizing bs with
  | _ n ih =>
    by_cases hb : bs = []
    · subst hb; simp [chunk, chunk_nil' r]
    · have hr := gt0_r
      have hpos : 0 < size bs := by
        simp only [size]; have := List.length_pos_of_ne_nil hb; omega
      have hle : r ≤ size bs := Int.le_of_dvd hpos hd
      have hdd : r ∣ size (drop r bs) := by
        have : size (drop r bs) = size bs - r := by
          simp only [size, drop, List.length_drop] at hle ⊢; omega
        rw [this]; exact dvd_sub hd dvd_rfl
      rw [chunk, chunk_cons' r bs hr hle, List.flatten_cons]
      have hlt : (drop r bs).length < n := by
        have : (bs.length : ℤ) = size bs := rfl
        simp only [drop, List.length_drop]; omega
      rw [← chunk, ih (drop r bs).length hlt _ hdd rfl]
      simp [take, drop]

theorem chunk_nil : chunk [] = [] := by
  exact chunk_nil' r

theorem chunk_sing (xs : List Bool) : size xs = r → chunk xs = [xs] := by
  exact chunk_sing' r xs gt0_r

theorem chunk_cat (xs ys : List Bool) : r ∣ size xs → chunk (xs ++ ys) = chunk xs ++ chunk ys := by
  intro hd
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | _ n ih =>
    by_cases hne : xs = []
    · subst hne; simp [chunk_nil]
    · have hr := gt0_r
      have hpos : 0 < size xs := by
        simp only [size]; have := List.length_pos_of_ne_nil hne; omega
      have hle : r ≤ size xs := Int.le_of_dvd hpos hd
      have hle' : r ≤ size (xs ++ ys) := by simp only [size, List.length_append] at hle ⊢; omega
      have hdd : r ∣ size (drop r xs) := by
        have : size (drop r xs) = size xs - r := by
          simp only [size, drop, List.length_drop] at hle ⊢; omega
        rw [this]; exact dvd_sub hd dvd_rfl
      have hdr : drop r (xs ++ ys) = drop r xs ++ ys := by
        simp only [drop]; rw [List.drop_append_of_le_length (by simp only [size] at hle; omega)]
      have htr : take r (xs ++ ys) = take r xs := by
        simp only [take]; rw [List.take_append_of_le_length (by simp only [size] at hle; omega)]
      have e1 : chunk (xs ++ ys) = take r xs :: chunk (drop r xs ++ ys) := by
        rw [chunk, chunk_cons' r _ hr hle', hdr, htr]; rfl
      have e2 : chunk xs = take r xs :: chunk (drop r xs) := chunk_cons' r _ hr hle
      have hlt : (drop r xs).length < n := by
        have : (xs.length : ℤ) = size xs := rfl
        simp only [drop, List.length_drop]; omega
      rw [e1, e2, ih (drop r xs).length hlt _ hdd rfl]
      rfl

theorem chunk_padK : pcancel (chunk ∘ pad) (unpad ∘ List.flatten) := by
  intro s
  simp only [Function.comp_apply]
  rw [chunkK _ (size_pad_dvd_r s), padK]

theorem flattenK (bs : List (List Bool)) : (∀ b, b ∈ bs → size b = r) → chunk bs.flatten = bs := by
  induction bs with
  | nil => intro; exact chunk_nil
  | cons b bs ih =>
    intro h
    have hr := gt0_r
    have hb := h b List.mem_cons_self
    have hle : r ≤ size (b :: bs).flatten := by
      simp only [List.flatten_cons, size, List.length_append] at hb ⊢; omega
    have hbl : b.length = r.toNat := by simp only [size] at hb; omega
    rw [chunk, chunk_cons' r _ hr hle, ← chunk]
    simp only [List.flatten_cons, take, drop, List.take_left' hbl, List.drop_left' hbl]
    rw [ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')]

/-! ## Converting between block lists and bits -/

def blocks2bits (xs : List block) : List Bool := (xs.map ofblock).flatten

theorem blocks2bits_nil : blocks2bits [] = [] := by
  rfl

theorem blocks2bits_sing (x : block) : blocks2bits [x] = ofblock x := by
  simp [blocks2bits]

theorem blocks2bits_cat (xs ys : List block) :
    blocks2bits (xs ++ ys) = blocks2bits xs ++ blocks2bits ys := by
  simp [blocks2bits]

theorem size_blocks2bits (xs : List block) : size (blocks2bits xs) = r * size xs := by
  induction xs with
  | nil => simp [blocks2bits, size]
  | cons x xs ih =>
    have hx := BitWord.size_word ge0_r x
    simp only [blocks2bits, List.map_cons, List.flatten_cons, size, List.length_append,
      List.length_cons] at ih hx ⊢
    push_cast
    rw [show ((ofblock x).length : ℤ) = r from hx, ih]
    ring

theorem size_blocks2bits_dvd_r (xs : List block) : r ∣ size (blocks2bits xs) := by
  exact ⟨size xs, size_blocks2bits xs⟩

def bits2blocks (xs : List Bool) : List block := (chunk xs).map mkblock

theorem bits2blocks_nil : bits2blocks [] = [] := by
  simp [bits2blocks, chunk_nil]

theorem bits2blocks_sing (xs : List Bool) : size xs = r → bits2blocks xs = [mkblock xs] := by
  intro h
  simp [bits2blocks, chunk_sing xs h]

theorem bits2blocks_cat (xs ys : List Bool) : r ∣ size xs → r ∣ size ys →
    bits2blocks (xs ++ ys) = bits2blocks xs ++ bits2blocks ys := by
  intro hx _
  simp [bits2blocks, chunk_cat xs ys hx]

theorem blocks2bitsK : cancel blocks2bits bits2blocks := by
  intro xs
  have h : ∀ b ∈ xs.map ofblock, size b = r := by
    intro b hb
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb
    exact BitWord.size_word ge0_r x
  simp only [bits2blocks, blocks2bits]
  rw [flattenK _ h, List.map_map]
  conv_rhs => rw [← List.map_id xs]
  exact List.map_congr_left fun x _ => BitWord.mkwordK x

theorem bits2blocksK (bs : List Bool) : r ∣ size bs → blocks2bits (bits2blocks bs) = bs := by
  intro hd
  have h : (chunk bs).map (fun b => ofblock (mkblock b)) = chunk bs := by
    conv_rhs => rw [← List.map_id (chunk bs)]
    exact List.map_congr_left fun b hb => BitWord.ofwordK b (in_chunk_size bs b hb)
  simp only [blocks2bits, bits2blocks, List.map_map, Function.comp_def]
  rw [h, chunkK bs hd]

/-! ## Padding to blocks / unpadding from blocks -/

def pad2blocks : List Bool → List block := bits2blocks ∘ pad

def unpad_blocks : List block → Option (List Bool) := unpad ∘ blocks2bits

theorem pad2blocksK : pcancel pad2blocks unpad_blocks := by
  intro x
  simp only [unpad_blocks, pad2blocks, Function.comp_apply]
  rw [bits2blocksK _ (size_pad_dvd_r x), padK]

theorem unpadBlocksK : ocancel unpad_blocks pad2blocks := by
  intro xs
  cases h : unpad_blocks xs with
  | none => trivial
  | some y =>
    simp only [unpad_blocks, Function.comp_apply] at h
    show bits2blocks (pad y) = xs
    rw [← pad_of_unpad_some _ y h, blocks2bitsK]

theorem pad2blocks_inj : Function.Injective pad2blocks := by
  intro a b h
  have ha := pad2blocksK a
  rw [h, pad2blocksK b] at ha
  exact (Option.some.inj ha).symm

theorem size_pad2blocks (s : List Bool) : size (pad2blocks s) = (size s + 1) / r + 1 := by
  have hr := gt0_r
  simp only [pad2blocks, bits2blocks, Function.comp_apply, size, List.length_map]
  have h := size_chunk (pad s)
  simp only [size] at h
  rw [h]
  have h2 := size_pad s
  simp only [size] at h2
  rw [h2, show ((s.length : ℤ) + 1) / r * r + r = ((s.length : ℤ) + 1) / r * r + 1 * r by ring,
    ← add_mul, Int.mul_ediv_cancel _ (ne_of_gt hr)]

/-! ## Extending/stripping -/

def extend (xs : List block) (n : ℤ) : List block := xs ++ nseq n b0

def strip (xs : List block) : List block × ℤ :=
  let i := find (fun x => x != b0) xs.reverse
  (take (size xs - i) xs, i)

omit [Params] in
/-- Not an EasyCrypt lemma: before the first match, `findIdx` sees only non-matches. -/
theorem findIdx_replicate_append {α : Type} (p : α → Bool) (a : α) (ha : p a = false) (k : ℕ)
    (l : List α) : (List.replicate k a ++ l).findIdx p = k + l.findIdx p := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, List.findIdx_cons, ha, ih]; omega

theorem strip_ge0 (xs : List block) : 0 ≤ (strip xs).2 := by
  simp [strip, find]

theorem extendK (xs : List block) (n : ℤ) :
    last b0 xs ≠ b0 → 0 ≤ n → strip (extend xs n) = (xs, n) := by
  intro hl hn
  have hne : xs ≠ [] := by rintro rfl; exact hl rfl
  obtain ⟨ys, z, rfl⟩ := List.eq_nil_or_concat xs |>.resolve_left hne
  have hz : z ≠ b0 := by simpa [last] using hl
  have hrev : (extend (ys.concat z) n).reverse =
      List.replicate n.toNat b0 ++ z :: ys.reverse := by
    simp [extend, nseq, List.reverse_replicate]
  have hfind : find (fun x => x != b0) (extend (ys.concat z) n).reverse = n := by
    have hz' : (z != b0) = true := by simpa using hz
    rw [hrev, find, findIdx_replicate_append _ _ (by simp)]
    simp [List.findIdx_cons, hz', Int.toNat_of_nonneg hn]
  simp only [strip, hfind]
  refine Prod.ext ?_ rfl
  simp only [extend, nseq, take, size, List.length_append, List.length_replicate]
  rw [show ((ys.concat z).length + n.toNat : ℕ) - n = ((ys.concat z).length : ℤ) by omega,
    Int.toNat_natCast]
  exact List.take_left' rfl

theorem stripK (xs : List block) : extend (strip xs).1 (strip xs).2 = xs := by
  set i := (xs.reverse.findIdx fun x => x != b0) with hi
  have hil : i ≤ xs.length := by
    have := List.findIdx_le_length (p := fun x => x != b0) (xs := xs.reverse)
    simpa using this
  have hstrip : strip xs = (take (size xs - i) xs, (i : ℤ)) := rfl
  rw [hstrip]
  have htake : (xs.reverse.take i) = List.replicate i b0 := by
    refine List.eq_replicate_iff.mpr ⟨by simp; omega, fun b hb => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    rw [List.getElem_take]
    have := List.not_of_lt_findIdx (p := fun x => x != b0) (xs := xs.reverse) (i := j)
      (by rw [List.length_take] at hj; omega)
    simpa using this
  have hdrop : xs.drop (xs.length - i) = List.replicate i b0 := by
    have := congrArg List.reverse htake
    rw [List.reverse_take, List.reverse_reverse, List.reverse_replicate] at this
    simpa using this
  simp only [extend, take, nseq, size]
  rw [show (((xs.length : ℤ) - i).toNat) = xs.length - i by omega, Int.toNat_natCast, ← hdrop]
  exact List.take_append_drop _ _

/-! ## Validity -/

/-- In `Sponge`. -/
def valid_toplevel (_ : List Bool) : Prop := True

instance (bs : List Bool) : Decidable (valid_toplevel bs) := inferInstanceAs (Decidable True)

/-- In `BlockSponge`. -/
def valid_block (xs : List block) : Prop := unpad_blocks xs ≠ none

instance (xs : List block) : Decidable (valid_block xs) :=
  inferInstanceAs (Decidable (unpad_blocks xs ≠ none))

theorem valid_pad2blocks (bs : List Bool) : valid_block (pad2blocks bs) := by
  unfold valid_block
  rw [pad2blocksK]
  simp

inductive valid_block_spec (xs : List block) : Prop where
  | ValidBlock (s : List Bool) (n : ℤ) :
      (0 ≤ n ∧ n < r) → blocks2bits xs = s ++ [true] ++ nseq n false ++ [true] →
      valid_block_spec xs

theorem valid_blockP (xs : List block) : valid_block xs ↔ valid_block_spec xs := by
  unfold valid_block unpad_blocks
  rw [Function.comp_apply, unpadP]
  constructor
  · rintro ⟨s, n, hn, -, he⟩
    exact ⟨s, n, hn, he⟩
  · rintro ⟨s, n, hn, he⟩
    refine ⟨s, n, hn, ?_, he⟩
    have h1 := size_blocks2bits xs
    rw [he] at h1
    simp only [size, List.length_append, List.length_singleton, nseq, List.length_replicate]
      at h1 ⊢
    rw [show ((s.length + 1 + n.toNat + 1 : ℕ) : ℤ) = (s.length : ℤ) + n + 2 by omega] at h1
    exact ⟨_, h1⟩

theorem valid_block_ends_not_b0 (xs : List block) : valid_block xs → last b0 xs ≠ b0 := by
  intro hv
  obtain ⟨s, n, hn, he⟩ := (valid_blockP xs).mp hv
  rcases List.eq_nil_or_concat xs with rfl | ⟨ys, x, rfl⟩
  · simp [blocks2bits] at he
  · intro hx
    simp only [last, List.concat_eq_append, List.getLastD_concat] at hx
    have hlast := congrArg (last false) he
    rw [List.concat_eq_append, blocks2bits_cat, blocks2bits_sing, hx] at hlast
    have hb0 : ofblock (b0 : block) = List.replicate r.toNat false := rfl
    obtain ⟨k, hk⟩ : ∃ k, r.toNat = k + 1 := ⟨r.toNat - 1, by have := gt0_r; omega⟩
    rw [hb0, hk, List.replicate_succ', ← List.append_assoc] at hlast
    simp only [last, List.getLastD_concat] at hlast
    exact Bool.false_ne_true hlast

inductive valid_block_struct_spec (xs : List block) : Prop where
  | ValidBlockStruct1 (ys : List block) (x : block) (s : List Bool) (n : ℤ) :
      xs = ys ++ [x] → 0 ≤ n → ofblock x = s ++ [true] ++ nseq n false ++ [true] →
      valid_block_struct_spec xs
  | ValidBlockStruct2 (ys : List block) (y z : block) :
      xs = ys ++ [y, z] → last false (ofblock y) = true →
      ofblock z = nseq (r - 1) false ++ [true] →
      valid_block_struct_spec xs

theorem valid_block_structP (xs : List block) : valid_block xs ↔ valid_block_struct_spec xs := by
  have hr := gt0_r
  have hsz : ∀ x : block, (ofblock x).length = r.toNat := fun x => by simp [ofblock, BitWord.ofword]
  rw [valid_blockP]
  constructor
  · rintro ⟨s, n, ⟨hn0, hnr⟩, he⟩
    -- the last block
    have hne : xs ≠ [] := by rintro rfl; simp [blocks2bits] at he
    obtain ⟨ys, x, rfl⟩ := List.eq_nil_or_concat xs |>.resolve_left hne
    rw [List.concat_eq_append, blocks2bits_cat, blocks2bits_sing,
      show s ++ [true] ++ nseq n false ++ [true] = s ++ ([true] ++ nseq n false ++ [true]) by simp]
      at he
    rcases List.append_eq_append_iff.mp he with ⟨a', hs, hx⟩ | ⟨c', hys, ht⟩
    · -- the padding lies within the last block
      exact .ValidBlockStruct1 ys x a' n (by simp) hn0 (by rw [hx]; simp)
    · -- the padding straddles the last two blocks
      have hlen := congrArg List.length ht
      simp only [List.length_append, List.length_singleton, nseq, List.length_replicate, hsz]
        at hlen
      rcases c' with _ | ⟨b, c''⟩
      · exact .ValidBlockStruct1 ys x [] n (by simp) hn0 (by simpa using ht.symm)
      · have hc'' : c'' = [] := by
          apply List.eq_nil_of_length_eq_zero; simp at hlen; omega
        subst hc''
        have hb : b = true := by simpa using congrArg List.head? ht
        subst hb
        have hn : n = r - 1 := by simp at hlen; omega
        have hx : ofblock x = nseq (r - 1) false ++ [true] := by
          have := ht; simp only [List.cons_append, List.cons.injEq] at this
          simpa [hn] using this.2.symm
        have hne' : ys ≠ [] := by rintro rfl; simp [blocks2bits] at hys
        obtain ⟨ys', y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hne'
        rw [List.concat_eq_append, blocks2bits_cat, blocks2bits_sing] at hys
        have hy : last false (ofblock y) = true := by
          have hl := congrArg (last false) hys
          have hpos : (ofblock y).length ≠ 0 := by rw [hsz y]; omega
          obtain ⟨u, v, huv⟩ := List.eq_nil_or_concat (ofblock y) |>.resolve_left
            (fun h => hpos (by rw [h]; rfl))
          rw [huv, List.concat_eq_append, ← List.append_assoc] at hl
          simp only [last, List.getLastD_concat] at hl
          rw [huv]; simpa [last, List.concat_eq_append] using hl
        exact .ValidBlockStruct2 ys' y x (by simp) hy hx
  · rintro (⟨ys, x, s, n, rfl, hn0, hx⟩ | ⟨ys, y, z, rfl, hy, hz⟩)
    · have hlen := congrArg List.length hx
      simp only [hsz, List.length_append, List.length_singleton, nseq, List.length_replicate]
        at hlen
      refine ⟨blocks2bits ys ++ s, n, ⟨hn0, by omega⟩, ?_⟩
      rw [blocks2bits_cat, blocks2bits_sing, hx]
      simp
    · have hpos : (ofblock y).length ≠ 0 := by rw [hsz y]; omega
      obtain ⟨u, v, huv⟩ := List.eq_nil_or_concat (ofblock y) |>.resolve_left
        (fun h => hpos (by rw [h]; rfl))
      have hv : v = true := by
        rw [huv] at hy; simpa [last, List.concat_eq_append] using hy
      refine ⟨blocks2bits ys ++ u, r - 1, ⟨by omega, by omega⟩, ?_⟩
      rw [show ys ++ [y, z] = ys ++ [y] ++ [z] by simp, blocks2bits_cat, blocks2bits_cat,
        blocks2bits_sing, blocks2bits_sing, huv, hz, hv]
      simp

/-- In `AbsorbSponge`. -/
def valid_absorb (xs : List block) : Prop := valid_block (strip xs).1

inductive valid_absorb_spec (xs : List block) : Prop where
  | ValidAbsorb (ys : List block) (n : ℤ) :
      valid_block ys → 0 ≤ n → xs = ys ++ nseq n b0 → valid_absorb_spec xs

theorem valid_absorbP (xs : List block) : valid_absorb xs ↔ valid_absorb_spec xs := by
  constructor
  · intro hv
    exact ⟨(strip xs).1, (strip xs).2, hv, strip_ge0 xs, (stripK xs).symm⟩
  · rintro ⟨ys, n, hv, hn, rfl⟩
    unfold valid_absorb
    rw [show ys ++ nseq n b0 = extend ys n from rfl,
      extendK ys n (valid_block_ends_not_b0 ys hv) hn]
    exact hv

end GaudisCrypt.SHA3.Common
