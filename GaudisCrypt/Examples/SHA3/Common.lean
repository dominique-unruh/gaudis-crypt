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
  sorry

theorem chunk_nil' {α : Type} (r : ℤ) : BitChunking.chunk r ([] : List α) = [] := by
  sorry

theorem chunk_sing' (r : ℤ) (xs : List Bool) :
    0 < r → size xs = r → BitChunking.chunk r xs = [xs] := by
  sorry

theorem b0P : b0 = mkblock (nseq r false) := by
  sorry

theorem bits2w_inj_eq (cs ds : List Bool) :
    size cs = r → size ds = r → (mkblock cs = mkblock ds ↔ cs = ds) := by
  sorry

theorem last_drop_all_but_last {α : Type} (y : α) (xs : List α) :
    xs = [] ∨ drop (size xs - 1) xs = [last y xs] := by
  sorry

/-! ## The primitive: `clone export PRP as PRPt with type D <- block * capacity`,
`clone export StrongPRP as PRPSec`, `clone export RP as Perm with op dD <- bdistr \`*\` cdistr` -/

namespace PRPSec
abbrev PRP := EC.PRP.StrongPRP.PRP (block × capacity)
abbrev SPRP_Oracles := EC.PRP.StrongPRP.SPRP_Oracles (block × capacity)
abbrev Distinguisher := EC.PRP.StrongPRP.Distinguisher (block × capacity)
end PRPSec

/-- The `RP` clone's `op dD <- bdistr \`*\` cdistr`. -/
noncomputable def dD : SubProbability (block × capacity) := dprod bdistr cdistr

/-- `realize dD_ll`. -/
theorem dD_ll : is_lossless dD := by
  sorry

/-- `[module type] "PRP" as "PRIMITIVE"`. -/
abbrev PRIMITIVE := EC.PRP.StrongPRP.PRP (block × capacity)

/-- `[module] "RP" as "Perm"`: the ideal permutation on `block * capacity`. -/
noncomputable abbrev Perm := EC.PRP.RP.RP (block × capacity) dD

/-! ## Needed blocks computation -/

theorem needed_blocks0 : (0 + r - 1) / r = 0 := by
  sorry

theorem needed_blocks_non_pos (n : ℤ) : n ≤ 0 → (n + r - 1) / r ≤ 0 := by
  sorry

theorem needed_blocks_suff (n : ℤ) : n ≤ (n + r - 1) / r * r := by
  sorry

theorem needed_blocks_correct (n : ℤ) :
    0 ≤ (n + r - 1) / r * r - n ∧ (n + r - 1) / r * r - n < r := by
  sorry

theorem needed_blocks_prod_r (n : ℤ) : (n * r + r - 1) / r = n := by
  sorry

theorem needed_blocks_eq_div_r (n : ℤ) : r ∣ n ↔ n / r = (n + r - 1) / r := by
  sorry

theorem needed_blocks_succ_eq_div_r (n : ℤ) : ¬ r ∣ n ↔ n / r + 1 = (n + r - 1) / r := by
  sorry

theorem needed_blocks_rel_div_r (n : ℤ) :
    n / r = (n + r - 1) / r ∨ n / r + 1 = (n + r - 1) / r := by
  sorry

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
  sorry

theorem last_mkpad (b : Bool) (n : ℤ) : last b (mkpad n) = true := by
  sorry

theorem head_mkpad (b : Bool) (n : ℤ) : head b (mkpad n) = true := by
  sorry

theorem last_pad (b : Bool) (s : List Bool) : last b (pad s) = true := by
  sorry

theorem size_mkpad (n : ℤ) : size (mkpad n) = num0 n + 2 := by
  sorry

theorem size_pad_equiv (m : ℤ) : 0 ≤ m → m + num0 m + 2 = (m + 1) / r * r + r := by
  sorry

theorem size_padE (s : List Bool) : size (pad s) = size s + num0 (size s) + 2 := by
  sorry

theorem size_pad (s : List Bool) : size (pad s) = (size s + 1) / r * r + r := by
  sorry

theorem size_pad_dvd_r (s : List Bool) : r ∣ size (pad s) := by
  sorry

theorem dvd_r_num0 (m : ℤ) : r ∣ (m + num0 m + 2) := by
  sorry

theorem num0_ge0 (m : ℤ) : 0 ≤ num0 m := by
  sorry

theorem num0_ltr (m : ℤ) : num0 m < r := by
  sorry

theorem index_true_behead_mkpad (n : ℤ) : index true (behead (mkpad n)) = num0 n := by
  sorry

theorem padE (s : List Bool) (n : ℤ) :
    0 ≤ n ∧ n < r → r ∣ (size s + n + 2) →
    pad s = s ++ [true] ++ nseq n false ++ [true] := by
  sorry

theorem padK : pcancel pad unpad := by
  sorry

theorem unpadK : ocancel unpad pad := by
  sorry

inductive unpad_spec (t : List Bool) : Prop where
  | Unpad (s : List Bool) (n : ℤ) :
      (0 ≤ n ∧ n < r) → r ∣ (size s + n + 2) → t = s ++ [true] ++ nseq n false ++ [true] →
      unpad_spec t

theorem unpadP (t : List Bool) : unpad t ≠ none ↔ unpad_spec t := by
  sorry

/-! ## Chunking -/

def chunk (bs : List Bool) : List (List Bool) := BitChunking.chunk r bs

theorem size_chunk (bs : List Bool) : size (chunk bs) = size bs / r := by
  sorry

theorem in_chunk_size (bs b : List Bool) : b ∈ chunk bs → size b = r := by
  sorry

theorem chunkK (bs : List Bool) : r ∣ size bs → (chunk bs).flatten = bs := by
  sorry

theorem chunk_nil : chunk [] = [] := by
  sorry

theorem chunk_sing (xs : List Bool) : size xs = r → chunk xs = [xs] := by
  sorry

theorem chunk_cat (xs ys : List Bool) : r ∣ size xs → chunk (xs ++ ys) = chunk xs ++ chunk ys := by
  sorry

theorem chunk_padK : pcancel (chunk ∘ pad) (unpad ∘ List.flatten) := by
  sorry

theorem flattenK (bs : List (List Bool)) : (∀ b, b ∈ bs → size b = r) → chunk bs.flatten = bs := by
  sorry

/-! ## Converting between block lists and bits -/

def blocks2bits (xs : List block) : List Bool := (xs.map ofblock).flatten

theorem blocks2bits_nil : blocks2bits [] = [] := by
  sorry

theorem blocks2bits_sing (x : block) : blocks2bits [x] = ofblock x := by
  sorry

theorem blocks2bits_cat (xs ys : List block) :
    blocks2bits (xs ++ ys) = blocks2bits xs ++ blocks2bits ys := by
  sorry

theorem size_blocks2bits (xs : List block) : size (blocks2bits xs) = r * size xs := by
  sorry

theorem size_blocks2bits_dvd_r (xs : List block) : r ∣ size (blocks2bits xs) := by
  sorry

def bits2blocks (xs : List Bool) : List block := (chunk xs).map mkblock

theorem bits2blocks_nil : bits2blocks [] = [] := by
  sorry

theorem bits2blocks_sing (xs : List Bool) : size xs = r → bits2blocks xs = [mkblock xs] := by
  sorry

theorem bits2blocks_cat (xs ys : List Bool) : r ∣ size xs → r ∣ size ys →
    bits2blocks (xs ++ ys) = bits2blocks xs ++ bits2blocks ys := by
  sorry

theorem blocks2bitsK : cancel blocks2bits bits2blocks := by
  sorry

theorem bits2blocksK (bs : List Bool) : r ∣ size bs → blocks2bits (bits2blocks bs) = bs := by
  sorry

/-! ## Padding to blocks / unpadding from blocks -/

def pad2blocks : List Bool → List block := bits2blocks ∘ pad

def unpad_blocks : List block → Option (List Bool) := unpad ∘ blocks2bits

theorem pad2blocksK : pcancel pad2blocks unpad_blocks := by
  sorry

theorem unpadBlocksK : ocancel unpad_blocks pad2blocks := by
  sorry

theorem pad2blocks_inj : Function.Injective pad2blocks := by
  sorry

theorem size_pad2blocks (s : List Bool) : size (pad2blocks s) = (size s + 1) / r + 1 := by
  sorry

/-! ## Extending/stripping -/

def extend (xs : List block) (n : ℤ) : List block := xs ++ nseq n b0

def strip (xs : List block) : List block × ℤ :=
  let i := find (fun x => x != b0) xs.reverse
  (take (size xs - i) xs, i)

theorem strip_ge0 (xs : List block) : 0 ≤ (strip xs).2 := by
  sorry

theorem extendK (xs : List block) (n : ℤ) :
    last b0 xs ≠ b0 → 0 ≤ n → strip (extend xs n) = (xs, n) := by
  sorry

theorem stripK (xs : List block) : extend (strip xs).1 (strip xs).2 = xs := by
  sorry

/-! ## Validity -/

/-- In `Sponge`. -/
def valid_toplevel (_ : List Bool) : Prop := True

/-- In `BlockSponge`. -/
def valid_block (xs : List block) : Prop := unpad_blocks xs ≠ none

instance (xs : List block) : Decidable (valid_block xs) :=
  inferInstanceAs (Decidable (unpad_blocks xs ≠ none))

theorem valid_pad2blocks (bs : List Bool) : valid_block (pad2blocks bs) := by
  sorry

inductive valid_block_spec (xs : List block) : Prop where
  | ValidBlock (s : List Bool) (n : ℤ) :
      (0 ≤ n ∧ n < r) → blocks2bits xs = s ++ [true] ++ nseq n false ++ [true] →
      valid_block_spec xs

theorem valid_blockP (xs : List block) : valid_block xs ↔ valid_block_spec xs := by
  sorry

theorem valid_block_ends_not_b0 (xs : List block) : valid_block xs → last b0 xs ≠ b0 := by
  sorry

inductive valid_block_struct_spec (xs : List block) : Prop where
  | ValidBlockStruct1 (ys : List block) (x : block) (s : List Bool) (n : ℤ) :
      xs = ys ++ [x] → 0 ≤ n → ofblock x = s ++ [true] ++ nseq n false ++ [true] →
      valid_block_struct_spec xs
  | ValidBlockStruct2 (ys : List block) (y z : block) :
      xs = ys ++ [y, z] → last false (ofblock y) = true →
      ofblock z = nseq (r - 1) false ++ [true] →
      valid_block_struct_spec xs

theorem valid_block_structP (xs : List block) : valid_block xs ↔ valid_block_struct_spec xs := by
  sorry

/-- In `AbsorbSponge`. -/
def valid_absorb (xs : List block) : Prop := valid_block (strip xs).1

inductive valid_absorb_spec (xs : List block) : Prop where
  | ValidAbsorb (ys : List block) (n : ℤ) :
      valid_block ys → 0 ≤ n → xs = ys ++ nseq n b0 → valid_absorb_spec xs

theorem valid_absorbP (xs : List block) : valid_absorb xs ↔ valid_absorb_spec xs := by
  sorry

end GaudisCrypt.SHA3.Common
