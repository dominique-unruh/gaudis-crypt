import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.Granular
import GaudisCrypt.Logic.Representation
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
* The module variables `RO.m`, `FRO.m` are parameters: each clone declares its own `global_var`s
  (`F.RO.m`, `F2.RO.m` …) and passes them.
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

/-- The oracle procedures an `RO_Distinguisher` may call: all of `RO`'s (EasyCrypt's module type
puts no restriction on them).  The holes of its representation (`Module.Representable`, exception
E2 of the SHA-3 port). -/
abbrev RO_holes : HoleSigs :=
  .cons (procsig () -> Unit) (.cons (procsig (in_t) -> out_t) (.cons (procsig (in_t, out_t) -> Unit)
    (.cons (procsig (in_t) -> Unit) (.cons (procsig (in_t) -> Unit) .empty))))

/-- `G.init`, `G.get`, `G.set`, `G.rem`, `G.sample` out of the oracle `G`. -/
noncomputable def RO_ext (G : RO_T in_t out_t) : (RO_holes in_t out_t).Instantiation :=
  ((RO_T.init in_t out_t G).procedure, (RO_T.get in_t out_t G).procedure,
   (RO_T.set in_t out_t G).procedure, (RO_T.rem in_t out_t G).procedure,
   (RO_T.sample in_t out_t G).procedure)

/-- The oracle procedures an `FRO_Distinguisher` may call: all of `FRO`'s. -/
abbrev FRO_holes : HoleSigs :=
  .cons (procsig () -> Unit) (.cons (procsig (in_t) -> out_t) (.cons (procsig (in_t, out_t) -> Unit)
    (.cons (procsig (in_t) -> Unit) (.cons (procsig (in_t) -> Unit)
      (.cons (procsig (in_t, flag) -> Bool) (.cons (procsig () -> (FMap in_t out_t)) .empty))))))

/-- `G.init`, `G.get` … `G.allKnown` out of the oracle `G`. -/
noncomputable def FRO_ext (G : FRO_T in_t out_t) : (FRO_holes in_t out_t).Instantiation :=
  ((FRO_T.init in_t out_t G).procedure, (FRO_T.get in_t out_t G).procedure,
   (FRO_T.set in_t out_t G).procedure, (FRO_T.rem in_t out_t G).procedure,
   (FRO_T.sample in_t out_t G).procedure, (FRO_T.queried in_t out_t G).procedure,
   (FRO_T.allKnown in_t out_t G).procedure)

omit [Inhabited d_in_t] [Inhabited d_out_t] in
/-- **Every `RO_Distinguisher` is representable** over all of `RO`'s procedures
(`Module.representable_of_firstOrder`): for it, exception E2 is a theorem. -/
theorem RO_Distinguisher.representable [Inhabited in_t] [Inhabited out_t]
    (D : RO_Distinguisher in_t out_t d_in_t d_out_t) :
    Module.Representable D (RO_ext in_t out_t) :=
  Module.representable_of_firstOrder (M := RO_T in_t out_t)
    (by show (RO_T.typeRep in_t out_t).FirstOrder
        simp only [RO_T.typeRep, ModuleTypeRep.FirstOrder, and_self])
    (fun n => by
      cases n with
      | zero => exact ⟨by simp, inferInstance⟩
      | succ n => cases n with
        | zero => exact ⟨by simp; exact ⟨default⟩, ⟨default⟩⟩
        | succ n => cases n with
          | zero => exact ⟨by simp; exact ⟨⟨default⟩, ⟨default⟩⟩, inferInstance⟩
          | succ n => cases n with
            | zero => exact ⟨by simp; exact ⟨default⟩, inferInstance⟩
            | succ n => cases n with
              | zero => exact ⟨by simp; exact ⟨default⟩, inferInstance⟩
              | succ n => nomatch n)
    (RO_ext in_t out_t) (fun _ => rfl) D

omit [Inhabited d_in_t] [Inhabited d_out_t] in
/-- An `RO_Distinguisher` is EasyCrypt-like as soon as it has finitely many globals: its
representability is `RO_Distinguisher.representable`. -/
theorem RO_Distinguisher.ecModule [Inhabited in_t] [Inhabited out_t]
    (D : RO_Distinguisher in_t out_t d_in_t d_out_t) (hD : (FVP.fvP D).FinitelySupported) :
    Module.ECModule D (RO_ext in_t out_t) :=
  ⟨RO_Distinguisher.representable in_t out_t d_in_t d_out_t D, hD⟩

omit [Inhabited d_in_t] [Inhabited d_out_t] in
/-- **Every `FRO_Distinguisher` is representable** over all of `FRO`'s procedures. -/
theorem FRO_Distinguisher.representable [Inhabited in_t] [Inhabited out_t]
    (D : FRO_Distinguisher in_t out_t d_in_t d_out_t) :
    Module.Representable D (FRO_ext in_t out_t) :=
  Module.representable_of_firstOrder (M := FRO_T in_t out_t)
    (by show (FRO_T.typeRep in_t out_t).FirstOrder
        simp only [FRO_T.typeRep, ModuleTypeRep.FirstOrder, and_self])
    (fun n => by
      cases n with
      | zero => exact ⟨by simp, inferInstance⟩
      | succ n => cases n with
        | zero => exact ⟨by simp; exact ⟨default⟩, ⟨default⟩⟩
        | succ n => cases n with
          | zero => exact ⟨by simp; exact ⟨⟨default⟩, ⟨default⟩⟩, inferInstance⟩
          | succ n => cases n with
            | zero => exact ⟨by simp; exact ⟨default⟩, inferInstance⟩
            | succ n => cases n with
              | zero => exact ⟨by simp; exact ⟨default⟩, inferInstance⟩
              | succ n => cases n with
                | zero => exact ⟨by simp; exact ⟨⟨default⟩, ⟨.Unknown⟩⟩, inferInstance⟩
                | succ n => cases n with
                  | zero => exact ⟨by simp, ⟨FMap.empty⟩⟩
                  | succ n => nomatch n)
    (FRO_ext in_t out_t) (fun _ => rfl) D

module MainD using (D : RO_Distinguisher in_t out_t d_in_t d_out_t, RO : RO_T in_t out_t) {
  proc distinguish (x : d_in_t) : d_out_t {
    var r : d_out_t;
    _ <- call RO.init ();
    r <- call (Module.app D RO) ($x);
    return $r
  };
}

end Distinguishers

section Oracles

variable (in_t out_t : Type) [DecidableEq in_t] [Inhabited in_t] [Inhabited out_t]
  (dout : in_t → SubProbability out_t)

section RO
/-! `RO`'s module variable `m` is a parameter: a clone declares its own (`F.RO.m`) and passes it,
so two clones never share it. -/
variable (m : Lens (FMap in_t out_t) VariableAssignment)

-- EC's `MkRO.RO` (declared at `ROmap`; `RO.asRO` is its `RO` view)
module RO : (ROmap in_t out_t) {
  proc init () : Unit {
    m <- (FMap.empty : FMap in_t out_t);
    return ()
  };
  proc get (x : in_t) : out_t {
    var r : out_t;
    r <$ dout $x;
    if (!(decide (FMap.dom ($m : FMap in_t out_t) $x))) {
      m <- FMap.set $m $x $r;
    }
    return oget (FMap.get $m $x)
  };
  proc set (x : in_t, y : out_t) : Unit {
    m <- FMap.set $m $x $y;
    return ()
  };
  proc rem (x : in_t) : Unit {
    m <- FMap.rem ($m : FMap in_t out_t) $x;
    return ()
  };
  proc sample (x : in_t) : Unit {
    _ <- call (RO.get in_t out_t dout m) ($x);
    return ()
  };
  proc restrK () : (FMap in_t out_t) {
    return $m
  };
}

/-- `RO` at its type `RO` (EasyCrypt's `module RO : RO, ROmap`). -/
noncomputable def RO.asRO : RO_T in_t out_t :=
  RO_T.mk in_t out_t
    { init := ROmap.init in_t out_t (RO in_t out_t dout m)
      get := ROmap.get in_t out_t (RO in_t out_t dout m)
      set := ROmap.set in_t out_t (RO in_t out_t dout m)
      rem := ROmap.rem in_t out_t (RO in_t out_t dout m)
      sample := ROmap.sample in_t out_t (RO in_t out_t dout m) }

-- `LRO.sample`, the one procedure of `LRO` that is not `RO`'s
module LRO.sample_ {
  proc sample (x : in_t) : Unit {
    return ()
  };
}

/-- EC's `MkRO.LRO`: `RO` with `proc sample(x : in_t) = { }` (and `proc init = RO.init` …). -/
noncomputable def LRO : RO_T in_t out_t :=
  RO_T.mk in_t out_t
    { init := ROmap.init in_t out_t (RO in_t out_t dout m)
      get := ROmap.get in_t out_t (RO in_t out_t dout m)
      set := ROmap.set in_t out_t (RO in_t out_t dout m)
      rem := ROmap.rem in_t out_t (RO in_t out_t dout m)
      sample := LRO.sample_ in_t out_t }

end RO

section FRO
/-! `FRO`'s module variable `m` is a parameter (see `RO`). -/
variable (m : Lens (FMap in_t (out_t × flag)) VariableAssignment)

module FRO : (FRO_T in_t out_t) {
  proc init () : Unit {
    m <- (FMap.empty : FMap in_t (out_t × flag));
    return ()
  };
  proc get (x : in_t) : out_t {
    var r : out_t;
    r <$ dout $x;
    if (decide (FMap.dom ($m : FMap in_t (out_t × flag)) $x)) {
      r <- (oget (FMap.get $m $x)).1;
    }
    m <- FMap.set $m $x ($r, Known);
    return $r
  };
  proc set (x : in_t, y : out_t) : Unit {
    m <- FMap.set $m $x ($y, Known);
    return ()
  };
  proc rem (x : in_t) : Unit {
    m <- FMap.rem ($m : FMap in_t (out_t × flag)) $x;
    return ()
  };
  proc sample (x : in_t) : Unit {
    var c : out_t;
    c <$ dout $x;
    if (!(decide (FMap.dom ($m : FMap in_t (out_t × flag)) $x))) {
      m <- FMap.set $m $x ($c, Unknown);
    }
    return ()
  };
  proc queried (x : in_t, f : flag) : Bool {
    return decide (FMap.dom ($m : FMap in_t (out_t × flag)) $x ∧
      is_ (FMap.get ($m : FMap in_t (out_t × flag)) $x) $f)
  };
  proc allKnown () : (FMap in_t out_t) {
    return FMap.restr Known $m
  };
}

end FRO

end Oracles

namespace FullEager

section RRO

variable (in_t out_t : Type) [DecidableEq in_t] [Inhabited in_t] [Inhabited out_t]
  (dout : in_t → SubProbability out_t) (m : Lens (FMap in_t (out_t × flag)) VariableAssignment)

-- EC's `RRO.I`
module RRO.I {
  proc f (x : in_t) : Unit {
    var c : out_t;
    c <$ dout $x;
    m <- FMap.set $m $x ($c, Unknown);
    return ()
  };
}

-- `RRO.get` and `RRO.resample`, the procedures of `RRO` that are not `FRO`'s
module RRO.own {
  proc get (x : in_t) : out_t {
    var r : out_t;
    r <$ dout $x;
    if (!(decide (FMap.dom ($m : FMap in_t (out_t × flag)) $x)) ||
        decide (is_ (FMap.get ($m : FMap in_t (out_t × flag)) $x) Unknown)) {
      m <- FMap.set $m $x ($r, Known);
    }
    return (oget (FMap.get $m $x)).1
  };
  proc resample () : Unit {
    _ <- call (Module.app (IterProc.Iter in_t) (RRO.I in_t out_t dout m))
      ((FMap.fdom (FMap.restr Unknown ($m : FMap in_t (out_t × flag)))).toList);
    return ()
  };
}

/-- EC's `FullEager.RRO : FRO` (with `proc init = FRO.init` …; its extra procedure `resample` is
`RRO.own.resample`). -/
noncomputable def RRO : FRO_T in_t out_t :=
  FRO_T.mk in_t out_t
    { init := FRO_T.init in_t out_t (FRO in_t out_t dout m)
      get := RRO.own.get in_t out_t dout m
      set := FRO_T.set in_t out_t (FRO in_t out_t dout m)
      rem := FRO_T.rem in_t out_t (FRO in_t out_t dout m)
      sample := FRO_T.sample in_t out_t (FRO in_t out_t dout m)
      queried := FRO_T.queried in_t out_t (FRO in_t out_t dout m)
      allKnown := FRO_T.allKnown in_t out_t (FRO in_t out_t dout m) }

end RRO

section RO_LRO_D

variable (in_t out_t d_in_t d_out_t : Type) [DecidableEq in_t] [Inhabited in_t] [Inhabited out_t]
  [Inhabited d_in_t] [Inhabited d_out_t] (dout : in_t → SubProbability out_t)
  (FRO_m : Lens (FMap in_t (out_t × flag)) VariableAssignment)

/-- EC's `FullEager.RO_LRO_D`, for `declare module D <: RO_Distinguisher {-RO, -FRO}` and
`axiom dout_ll x : is_lossless (dout x)`:
`equiv[ D(RO).distinguish ~ D(LRO).distinguish : ={glob D, RO.m, arg} ==> ={res, glob D} ]`. -/
theorem RO_LRO_D (dout_ll : ∀ x, (dout x).1 Set.univ = 1)
    (RO_m : Lens (FMap in_t out_t) VariableAssignment)
    (D : RO_Distinguisher in_t out_t d_in_t d_out_t)
    (hD : Module.ECModule D (RO_ext in_t out_t))
    (hdisj : FVP.fvP D ≤ (RO_m.footprint ⊔ FRO_m.footprint)ᶜ) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧
        (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂ ∧
        RO_m.get g₁ = RO_m.get g₂)
      (Module.app D (RO.asRO in_t out_t dout RO_m)).procedure
      (Module.app D (LRO in_t out_t dout RO_m)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂) := by
  sorry

-- EC's `FullEager.EagerCore.Eager (D : FRO_Distinguisher)`, with `D` a Lean parameter
set_option linter.gaudisCrypt.using false in
module Eager (D : FRO_Distinguisher in_t out_t d_in_t d_out_t) {
  proc main1 (x : d_in_t) : d_out_t {
    var b : d_out_t;
    _ <- call (FRO_T.init in_t out_t (FRO in_t out_t dout FRO_m)) ();
    b <- call (Module.app D (FRO in_t out_t dout FRO_m)) ($x);
    return $b
  };
  proc main2 (x : d_in_t) : d_out_t {
    var b : d_out_t;
    _ <- call (FRO_T.init in_t out_t (FRO in_t out_t dout FRO_m)) ();
    b <- call (Module.app D (RRO in_t out_t dout FRO_m)) ($x);
    _ <- call (RRO.own.resample in_t out_t dout FRO_m) ();
    return $b
  };
}

/-- EC's `FullEager.EagerCore.Eager_1_2`, for `declare module D <: FRO_Distinguisher {-FRO}`:
`equiv[ Eager(D).main1 ~ Eager(D).main2 : ={glob D, arg} ==> ={res, glob FRO, glob D} ]`. -/
theorem Eager_1_2 (dout_ll : ∀ x, (dout x).1 Set.univ = 1)
    (D : FRO_Distinguisher in_t out_t d_in_t d_out_t)
    (hD : Module.ECModule D (FRO_ext in_t out_t))
    (hdisj : FVP.fvP D ≤ (FRO_m.footprint)ᶜ) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧
        (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (Eager.main1 in_t out_t d_in_t d_out_t dout FRO_m D).procedure
      (Eager.main2 in_t out_t d_in_t d_out_t dout FRO_m D).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        FRO_m.get g₁ = FRO_m.get g₂ ∧
        (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂) := by
  sorry

end RO_LRO_D

end FullEager

end FullRO

end GaudisCrypt.EC.PROM
