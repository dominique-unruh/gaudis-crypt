import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.AbstractCall
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Lib.EC.FMap
import GaudisCrypt.Lib.EC.FSet
import GaudisCrypt.Lib.EC.IterProc

/-!
# EasyCrypt's programmable random oracles (`theories/crypto/PROM.ec`), `FullRO`

The abstract theory `FullRO`'s types `in_t`, `out_t`, `d_in_t`, `d_out_t` and its operator
`dout` are section variables, so a `clone` is an application.  Only what ported developments use
is here: the module types, `MainD`, the oracles `RO`, `LRO`, `FRO` and `FullEager.RRO`, and the
statement of `FullEager.RO_LRO_D`.

Translation notes (see `notes/SHA3/README.md`):
* EasyCrypt's module type and module `RO` share a name, as do `FRO` and `FRO`; the module types
  are `RO_T` and `FRO_T` (exception E3 of the SHA-3 port).
* `module RO : RO, ROmap` has both types: it is declared at `ROmap` (the larger), and `RO.asRO`
  is its `RO_T` view.
* `proc init = RO.init` (a procedure alias) is the same procedure: `LRO` and `RRO` are assembled
  with `RO_T.mk`/`FRO_T.mk` from the procedures they share.
-/

namespace GaudisCrypt.EC.PROM

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet

/-- `type flag = [ Unknown | Known ]`. -/
inductive flag where
  | Unknown
  | Known
  deriving DecidableEq, Inhabited

export flag (Unknown Known)

/-- `fv \is f`: the flag of a (bound) entry. -/
def is_ {α : Type} [Inhabited α] (fv : Option (α × flag)) (f : flag) : Prop := (oget fv).2 = f

instance {α : Type} [Inhabited α] (fv : Option (α × flag)) (f : flag) : Decidable (is_ fv f) :=
  inferInstanceAs (Decidable ((oget fv).2 = f))

namespace FullRO

section ModuleTypes

variable (in_t out_t : Type)

-- EC's `module type RO` (renamed: exception E3)
moduletype RO_T {
  proc init () -> Unit;
  proc get (x : in_t) -> out_t;
  proc set (x : in_t, y : out_t) -> Unit;
  proc rem (x : in_t) -> Unit;
  proc sample (x : in_t) -> Unit;
}

moduletype ROmap {
  proc init () -> Unit;
  proc get (x : in_t) -> out_t;
  proc set (x : in_t, y : out_t) -> Unit;
  proc rem (x : in_t) -> Unit;
  proc sample (x : in_t) -> Unit;
  proc restrK () -> (FMap in_t out_t);
}

-- EC's `module type FRO` (renamed: exception E3)
moduletype FRO_T {
  proc init () -> Unit;
  proc get (x : in_t) -> out_t;
  proc set (x : in_t, y : out_t) -> Unit;
  proc rem (x : in_t) -> Unit;
  proc sample (x : in_t) -> Unit;
  proc queried (x : in_t, f : flag) -> Bool;
  proc allKnown () -> (FMap in_t out_t);
}

end ModuleTypes

section Distinguishers

variable (in_t out_t d_in_t d_out_t : Type) [Inhabited d_in_t] [Inhabited d_out_t]

/-- EC's `module type RO_Distinguisher (G : RO) = { proc distinguish(_ : d_in_t): d_out_t }`. -/
abbrev RO_Distinguisher := RO_T in_t out_t →ₘ procmod (d_in_t) → d_out_t

/-- EC's `module type FRO_Distinguisher (G : FRO) = { proc distinguish(_ : d_in_t): d_out_t }`. -/
abbrev FRO_Distinguisher := FRO_T in_t out_t →ₘ procmod (d_in_t) → d_out_t

module MainD using (D : RO_Distinguisher in_t out_t d_in_t d_out_t, RO : RO_T in_t out_t) {
  proc distinguish (x : d_in_t) : d_out_t {
    var r : d_out_t;
    _ <- call RO.init ();
    r <- call (Module.app D RO) ($x);
    return $r
  };
}

end Distinguishers

section Variables
variable {in_t out_t : Type}
/-- EC's `RO.m`. -/
global_var RO.m : FMap in_t out_t
/-- EC's `FRO.m`. -/
global_var FRO.m : FMap in_t (out_t × flag)
end Variables

section Oracles

variable (in_t out_t : Type) [DecidableEq in_t] [Inhabited in_t] [Inhabited out_t]
  (dout : in_t → SubProbability out_t)

-- EC's `MkRO.RO` (declared at `ROmap`; `RO.asRO` is its `RO` view)
module RO : (ROmap in_t out_t) {
  proc init () : Unit {
    RO.m <- (FMap.empty : FMap in_t out_t);
    return ()
  };
  proc get (x : in_t) : out_t {
    var r : out_t;
    r <$ dout $x;
    if (!(decide (FMap.dom ($RO.m : FMap in_t out_t) $x))) {
      RO.m <- FMap.set $RO.m $x $r;
    }
    return oget (FMap.get $RO.m $x)
  };
  proc set (x : in_t, y : out_t) : Unit {
    RO.m <- FMap.set $RO.m $x $y;
    return ()
  };
  proc rem (x : in_t) : Unit {
    RO.m <- FMap.rem ($RO.m : FMap in_t out_t) $x;
    return ()
  };
  proc sample (x : in_t) : Unit {
    _ <- call (RO.get in_t out_t dout) ($x);
    return ()
  };
  proc restrK () : (FMap in_t out_t) {
    return $RO.m
  };
}

/-- `RO` at its type `RO` (EasyCrypt's `module RO : RO, ROmap`). -/
noncomputable def RO.asRO : RO_T in_t out_t :=
  RO_T.mk in_t out_t
    { init := ROmap.init in_t out_t (RO in_t out_t dout)
      get := ROmap.get in_t out_t (RO in_t out_t dout)
      set := ROmap.set in_t out_t (RO in_t out_t dout)
      rem := ROmap.rem in_t out_t (RO in_t out_t dout)
      sample := ROmap.sample in_t out_t (RO in_t out_t dout) }

-- `LRO.sample`, the one procedure of `LRO` that is not `RO`'s
module LRO.sample_ {
  proc sample (x : in_t) : Unit {
    return ()
  };
}

/-- EC's `MkRO.LRO`: `RO` with `proc sample(x : in_t) = { }` (and `proc init = RO.init` …). -/
noncomputable def LRO : RO_T in_t out_t :=
  RO_T.mk in_t out_t
    { init := ROmap.init in_t out_t (RO in_t out_t dout)
      get := ROmap.get in_t out_t (RO in_t out_t dout)
      set := ROmap.set in_t out_t (RO in_t out_t dout)
      rem := ROmap.rem in_t out_t (RO in_t out_t dout)
      sample := LRO.sample_ in_t out_t }

module FRO : (FRO_T in_t out_t) {
  proc init () : Unit {
    FRO.m <- (FMap.empty : FMap in_t (out_t × flag));
    return ()
  };
  proc get (x : in_t) : out_t {
    var r : out_t;
    r <$ dout $x;
    if (decide (FMap.dom ($FRO.m : FMap in_t (out_t × flag)) $x)) {
      r <- (oget (FMap.get $FRO.m $x)).1;
    }
    FRO.m <- FMap.set $FRO.m $x ($r, Known);
    return $r
  };
  proc set (x : in_t, y : out_t) : Unit {
    FRO.m <- FMap.set $FRO.m $x ($y, Known);
    return ()
  };
  proc rem (x : in_t) : Unit {
    FRO.m <- FMap.rem ($FRO.m : FMap in_t (out_t × flag)) $x;
    return ()
  };
  proc sample (x : in_t) : Unit {
    var c : out_t;
    c <$ dout $x;
    if (!(decide (FMap.dom ($FRO.m : FMap in_t (out_t × flag)) $x))) {
      FRO.m <- FMap.set $FRO.m $x ($c, Unknown);
    }
    return ()
  };
  proc queried (x : in_t, f : flag) : Bool {
    return decide (FMap.dom ($FRO.m : FMap in_t (out_t × flag)) $x ∧
      is_ (FMap.get ($FRO.m : FMap in_t (out_t × flag)) $x) $f)
  };
  proc allKnown () : (FMap in_t out_t) {
    return FMap.restr Known $FRO.m
  };
}

end Oracles

namespace FullEager

section RRO

variable (in_t out_t : Type) [DecidableEq in_t] [Inhabited in_t] [Inhabited out_t]
  (dout : in_t → SubProbability out_t)

-- EC's `RRO.I`
module RRO.I {
  proc f (x : in_t) : Unit {
    var c : out_t;
    c <$ dout $x;
    FRO.m <- FMap.set $FRO.m $x ($c, Unknown);
    return ()
  };
}

-- `RRO.get` and `RRO.resample`, the procedures of `RRO` that are not `FRO`'s
module RRO.own {
  proc get (x : in_t) : out_t {
    var r : out_t;
    r <$ dout $x;
    if (!(decide (FMap.dom ($FRO.m : FMap in_t (out_t × flag)) $x)) ||
        decide (is_ (FMap.get ($FRO.m : FMap in_t (out_t × flag)) $x) Unknown)) {
      FRO.m <- FMap.set $FRO.m $x ($r, Known);
    }
    return (oget (FMap.get $FRO.m $x)).1
  };
  proc resample () : Unit {
    _ <- call (Module.app (IterProc.Iter in_t) (RRO.I in_t out_t dout))
      ((FMap.fdom (FMap.restr Unknown ($FRO.m : FMap in_t (out_t × flag)))).toList);
    return ()
  };
}

/-- EC's `FullEager.RRO : FRO` (with `proc init = FRO.init` …; its extra procedure `resample` is
`RRO.own.resample`). -/
noncomputable def RRO : FRO_T in_t out_t :=
  FRO_T.mk in_t out_t
    { init := FRO_T.init in_t out_t (FRO in_t out_t dout)
      get := RRO.own.get in_t out_t dout
      set := FRO_T.set in_t out_t (FRO in_t out_t dout)
      rem := FRO_T.rem in_t out_t (FRO in_t out_t dout)
      sample := FRO_T.sample in_t out_t (FRO in_t out_t dout)
      queried := FRO_T.queried in_t out_t (FRO in_t out_t dout)
      allKnown := FRO_T.allKnown in_t out_t (FRO in_t out_t dout) }

end RRO

section RO_LRO_D

variable (in_t out_t d_in_t d_out_t : Type) [DecidableEq in_t] [Inhabited in_t] [Inhabited out_t]
  (dout : in_t → SubProbability out_t)

/-- EC's `FullEager.RO_LRO_D`, for `declare module D <: RO_Distinguisher {-RO, -FRO}` and
`axiom dout_ll x : is_lossless (dout x)`:
`equiv[ D(RO).distinguish ~ D(LRO).distinguish : ={glob D, RO.m, arg} ==> ={res, glob D} ]`. -/
theorem RO_LRO_D (dout_ll : ∀ x, (dout x).1 Set.univ = 1)
    (D : RO_Distinguisher in_t out_t d_in_t d_out_t)
    (hD : Module.Representable D (holes := .cons (procsig (in_t) -> out_t) .empty)
      fun G => (RO_T.get in_t out_t G).procedure)
    (hdisj : FVP.fvP D ≤ ((RO.m (in_t := in_t) (out_t := out_t)).footprint ⊔
      (FRO.m (in_t := in_t) (out_t := out_t)).footprint)ᶜ) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧
        (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂ ∧
        (RO.m (in_t := in_t) (out_t := out_t)).get g₁ = RO.m.get g₂)
      (Module.app D (RO.asRO in_t out_t dout)).procedure
      (Module.app D (LRO in_t out_t dout)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂) := by
  sorry

end RO_LRO_D

end FullEager

end FullRO

end GaudisCrypt.EC.PROM
