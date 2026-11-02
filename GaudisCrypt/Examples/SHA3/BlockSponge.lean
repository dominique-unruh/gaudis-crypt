import GaudisCrypt.Examples.SHA3.IRO
import GaudisCrypt.Examples.SHA3.SmartCounter.Gconcl

/-!
# The padded block sponge construction (EasyCrypt `proof/BlockSponge.ec`)

The sponge on blocks: absorb a valid block list, squeeze `n` blocks.  Its ideal functionality is
the infinite random oracle `BIRO.IRO` on valid block lists, and its simulator is the squeezeless
sponge's (`Gconcl.S`) through `Last`.

Translation notes (see `notes/SHA3/README.md`):
* `clone include Indifferentiability with type p <- block * capacity, type f_in <- block list *
  int, type f_out <- block list rename … "Indif" as "Experiment" …` is the abbreviations below.
* `op parse` with its axioms `formatK`, `parseK`, `parse_nil` is the parameter class `Params`
  (over `SLCommon.Params`).
* A procedure whose EasyCrypt parameters `(bl, nb)` are the module type's single parameter
  (`f_in = block list * int`) takes that pair, `x`, and names its components.
* `module Sim (F) = Gconcl.S(Last(F))` is the composite functor `Module.comp Gconcl.S Last`.
* `Last : SLCommon.DFUNCTIONALITY` has, in EasyCrypt, also an empty `init` outside its type: here
  `Last` has the type's `f` alone, and `Last.init` is a module of its own.
* `DRestr(D)(F)(P)` takes `D` as a Lean parameter, as in `SLCommon`.
-/

namespace GaudisCrypt.SHA3.BlockSponge

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon (state max_size)

export GaudisCrypt.SHA3.SLCommon (state)

variable [SLCommon.Params]

/-! ## Indifferentiability: `clone include Indifferentiability with type p <- block * capacity,
type f_in <- block list * int, type f_out <- block list rename [module] "Indif" as "Experiment"
[module] "GReal" as "RealIndif" [module] "GIdeal" as "IdealIndif"` -/

abbrev PRIMITIVE := Indifferentiability.PRIMITIVE state (List block × ℤ) (List block)
abbrev DPRIMITIVE := Indifferentiability.DPRIMITIVE state (List block × ℤ) (List block)
abbrev FUNCTIONALITY := Indifferentiability.FUNCTIONALITY state (List block × ℤ) (List block)
abbrev DFUNCTIONALITY := Indifferentiability.DFUNCTIONALITY state (List block × ℤ) (List block)
abbrev CONSTRUCTION := Indifferentiability.CONSTRUCTION state (List block × ℤ) (List block)
abbrev SIMULATOR := Indifferentiability.SIMULATOR state (List block × ℤ) (List block)
abbrev DISTINGUISHER := Indifferentiability.DISTINGUISHER state (List block × ℤ) (List block)
noncomputable abbrev Experiment := Indifferentiability.Indif state (List block × ℤ) (List block)
noncomputable abbrev RealIndif := Indifferentiability.GReal state (List block × ℤ) (List block)
noncomputable abbrev IdealIndif := Indifferentiability.GIdeal state (List block × ℤ) (List block)
abbrev distHoles := Indifferentiability.distHoles state (List block × ℤ) (List block)
noncomputable abbrev distExt := Indifferentiability.distExt state (List block × ℤ) (List block)

/-! ## The ideal functionality: `clone import IRO as BIRO with type from <- block list,
type to <- block, op valid <- valid_block, op dto <- bdistr` -/

namespace BIRO
/-- `op valid <- valid_block`, as a test. -/
def valid (p : List block) : Bool := decide (valid_block p)
abbrev IRO_T := IRO.IRO_T block (List block)
/-- The clone's module variable `BIRO.IRO.mp`. -/
global_var IRO.mp : FMap (List block × ℤ) block
noncomputable abbrev IRO := IRO.IRO block (List block) valid bdistr IRO.mp
noncomputable abbrev IRO.init :=
  GaudisCrypt.SHA3.IRO.IRO.init block (List block) valid bdistr IRO.mp
noncomputable abbrev IRO.fill_in :=
  GaudisCrypt.SHA3.IRO.IRO.fill_in block (List block) valid bdistr IRO.mp
noncomputable abbrev IRO.f :=
  GaudisCrypt.SHA3.IRO.IRO.f block (List block) valid bdistr IRO.mp
/-- `BIRO.IRO` as the functionality it is used as (its procedures `init` and `f`). -/
noncomputable def IRO.asF : FUNCTIONALITY :=
  Indifferentiability.FUNCTIONALITY.mk state (List block × ℤ) (List block)
    { init := GaudisCrypt.SHA3.IRO.IRO.init block (List block) valid bdistr IRO.mp
      f := GaudisCrypt.SHA3.IRO.IRO.f block (List block) valid bdistr IRO.mp }
end BIRO

/-! ## Validity and parsing/formatting of functionality queries -/

def format (p : List block) (n : ℤ) : List block := p ++ nseq (n - 1) b0

/-- EasyCrypt's abstract `op parse : block list -> (block list * int)` with its axioms
`formatK`, `parseK`, `parse_nil`. -/
class Params where
  parse : List block → List block × ℤ
  formatK : ∀ bs, format (parse bs).1 (parse bs).2 = bs
  parseK : ∀ p n, 0 < n → valid_block p → parse (format p n) = (p, n)
  parse_nil : parse [] = ([], 0)

variable [Params]

def parse : List block → List block × ℤ := Params.parse
theorem formatK (bs : List block) : format (parse bs).1 (parse bs).2 = bs := Params.formatK bs
theorem parseK (p : List block) (n : ℤ) : 0 < n → valid_block p → parse (format p n) = (p, n) :=
  Params.parseK p n
theorem parse_nil : parse [] = ([], 0) := Params.parse_nil

theorem parse_injective : Function.Injective parse := by
  intro bs1 bs2 eq_format
  rw [← formatK bs1, eq_format, formatK bs2]

theorem parse_valid (p : List block) : valid_block p → parse p = (p, 1) := by
  intro h
  have hp : format p 1 = p := by simp [format, nseq]
  conv_lhs => rw [← hp]
  exact parseK p 1 one_pos h

/-! ## Restrictions

The counter for the functionality counts the number of times the underlying primitive is called
inside the functionality: the number of blocks of the input message plus the number of
additional blocks the squeezing phase has to output. -/

/-- EC's `C.c`. -/
global_var C.c : ℤ

module C {
  proc init () : Unit {
    C.c <- 0;
    return ()
  };
}

module FC using (F : DFUNCTIONALITY) : FUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (x : List block × ℤ) : (List block) {
    var bl : List block, nb : ℤ, z : List block;
    bl, nb <- $x;
    z <- [];
    if (decide ($C.c + size $bl + max ($nb - 1) 0 ≤ max_size)) {
      C.c <- $C.c + size $bl + max ($nb - 1) 0;
      z <- call F.f (($bl, $nb));
    }
    return $z
  };
}

module PC using (P : DPRIMITIVE) : PRIMITIVE {
  proc init () : Unit {
    return ()
  };
  proc f (a : state) : state {
    var z : state;
    z <- (b0, c0);
    if (decide ($C.c + 1 ≤ max_size)) {
      z <- call P.f ($a);
      C.c <- $C.c + 1;
    }
    return $z
  };
  proc fi (a : state) : state {
    var z : state;
    z <- (b0, c0);
    if (decide ($C.c + 1 ≤ max_size)) {
      z <- call P.fi ($a);
      C.c <- $C.c + 1;
    }
    return $z
  };
}

-- EC's `DRestr(D)(F)(P)`, with `D` a Lean parameter so that `DRestr D` is a `DISTINGUISHER`
set_option linter.gaudisCrypt.using false in
module DRestr (D : DISTINGUISHER) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call C.init ();
    b <- call (Module.app D (Module.pair
      (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
            (Module.app FC F) })
      (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
            (Module.app PC P)
          fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
            (Module.app PC P) }))) ();
    return $b
  };
}

/-! ## The simulator -/

-- EC's `Last(F)`'s procedure `init`, outside its type `SLCommon.DFUNCTIONALITY`
module Last.init {
  proc init () : Unit {
    return ()
  };
}

module Last using (F : DFUNCTIONALITY) : SLCommon.DFUNCTIONALITY {
  proc f (p : List block) : block {
    var z : List block;
    z <- [];
    z <- call F.f (parse $p);
    return last b0 $z
  };
}

/-- `module (Sim : SIMULATOR) (F : DFUNCTIONALITY) = Gconcl.S(Last(F))`. -/
noncomputable def Sim : SIMULATOR := Module.comp Gconcl.S Last

/-! ## The sponge construction -/

module Sponge using (P : DPRIMITIVE) : FUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (x : List block × ℤ) : (List block) {
    var xs : List block, n : ℤ, z : List block, sa : block, sc : capacity, i : ℤ;
    xs, n <- $x;
    z <- [];
    sa, sc <- (b0, Capacity.c0);
    i <- 0;
    if (decide (valid_block $xs)) {
      -- absorption
      while (!(List.isEmpty $xs)) {
        sa, sc <- call P.f (($sa +^ head b0 $xs, $sc));
        xs <- behead $xs;
      }
      -- squeezing
      while ($i < $n) {
        z <- rcons $z $sa;
        i <- $i + 1;
        if ($i < $n) {
          sa, sc <- call P.f (($sa, $sc));
        }
      }
    }
    return $z
  };
}

end GaudisCrypt.SHA3.BlockSponge
