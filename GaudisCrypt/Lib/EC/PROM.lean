import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.Granular
import GaudisCrypt.Logic.Representation
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Lib.EC.FMap
import GaudisCrypt.Lib.EC.FSet
import GaudisCrypt.Lib.EC.IterProc
import GaudisCrypt.Logic.SyntacticFrame
import GaudisCrypt.Logic.ConcreteFootprint
import GaudisCrypt.Logic.EagerAbstract
import GaudisCrypt.Logic.EagerBridge
import GaudisCrypt.Logic.PHoareWp

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

instance : Countable flag :=
  Function.Injective.countable
    (f := fun f : flag => match f with | Unknown => false | Known => true)
    (by intro a b; cases a <;> cases b <;> simp)

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

/-! The footprints of `RO` and `LRO`: their procedures touch `m` only (`LRO` is not a `module`:
`fp_disjoint` reads them here). -/

@[fp_bound] theorem fvP_RO_sample :
    FVP.fvP (RO_T.sample in_t out_t (RO.asRO in_t out_t dout m)) ≤ m.footprint := by
  fp_module m

@[fp_bound] theorem fvP_LRO_init :
    FVP.fvP (RO_T.init in_t out_t (LRO in_t out_t dout m)) ≤ m.footprint := by
  fp_module m

@[fp_bound] theorem fvP_LRO_get :
    FVP.fvP (RO_T.get in_t out_t (LRO in_t out_t dout m)) ≤ m.footprint := by
  fp_module m

@[fp_bound] theorem fvP_LRO_sample :
    FVP.fvP (RO_T.sample in_t out_t (LRO in_t out_t dout m)) ≤ m.footprint := by
  fp_module m

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

/-- `FRO` at the type `RO` (EasyCrypt's subtyping `FRO <: RO`: `D(FRO)` for an
`RO_Distinguisher D`). -/
noncomputable def FRO.asRO : RO_T in_t out_t :=
  RO_T.mk in_t out_t
    { init := FRO_T.init in_t out_t (FRO in_t out_t dout m)
      get := FRO_T.get in_t out_t (FRO in_t out_t dout m)
      set := FRO_T.set in_t out_t (FRO in_t out_t dout m)
      rem := FRO_T.rem in_t out_t (FRO in_t out_t dout m)
      sample := FRO_T.sample in_t out_t (FRO in_t out_t dout m) }

end FRO

section RO_FRO
/-! EC's `RO_FRO_init` … `RO_FRO_D`: `RO` and `FRO` agree up to the flags. -/
variable (RO_m : Lens (FMap in_t out_t) VariableAssignment)
  (FRO_m : Lens (FMap in_t (out_t × flag)) VariableAssignment)

/-- `equiv RO_FRO_init : RO.init ~ FRO.init : true ==> RO.m{1} = noflags FRO.m{2}`. -/
theorem RO_FRO_init : prhlProc (fun _ _ _ _ => True)
    (ROmap.init in_t out_t (RO in_t out_t dout RO_m)).procedure
    (FRO_T.init in_t out_t (FRO in_t out_t dout FRO_m)).procedure
    (fun _ g₁ _ g₂ => RO_m.get g₁ = FMap.noflags (FRO_m.get g₂)) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_skip
  intro _
  simp [FMap.noflags, FMap.map_empty]

/-- `equiv RO_FRO_get : RO.get ~ FRO.get : ={x} /\ RO.m{1} = noflags FRO.m{2} ==>
={res} /\ RO.m{1} = noflags FRO.m{2}`. -/
theorem RO_FRO_get :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ RO_m.get g₁ = FMap.noflags (FRO_m.get g₂))
    (ROmap.get in_t out_t (RO in_t out_t dout RO_m)).procedure
    (FRO_T.get in_t out_t (FRO in_t out_t dout FRO_m)).procedure
    (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ RO_m.get g₁ = FMap.noflags (FRO_m.get g₂)) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  rintro x _ _ m ⟨rfl, rfl⟩
  refine ⟨rfl, fun a _ => ?_⟩
  unfold FMap.noflags
  by_cases h : FMap.dom m x
  · obtain ⟨⟨y, f⟩, hy⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp h)
    have h' : FMap.dom (FMap.map (fun _ (p : out_t × flag) => p.1) m) x :=
      (FMap.mem_map _ _ _).mpr h
    simp only [h, h', decide_true, Bool.not_true, Bool.false_eq_true, if_true, if_false, ite_self]
    rw [FMap.map_set, FMap.get_set_id _ _ _ (by simp [FMap.mapE, hy, oget])]
    simp [FMap.mapE, hy, oget]
  · have h' : ¬ FMap.dom (FMap.map (fun _ (p : out_t × flag) => p.1) m) x :=
      fun h' => h ((FMap.mem_map _ _ _).mp h')
    simp [h, h', FMap.map_set, oget]

/-- `equiv RO_FRO_set : RO.set ~ FRO.set : ={x, y} /\ RO.m{1} = noflags FRO.m{2} ==>
RO.m{1} = noflags FRO.m{2}`. -/
theorem RO_FRO_set :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ RO_m.get g₁ = FMap.noflags (FRO_m.get g₂))
    (ROmap.set in_t out_t (RO in_t out_t dout RO_m)).procedure
    (FRO_T.set in_t out_t (FRO in_t out_t dout FRO_m)).procedure
    (fun _ g₁ _ g₂ => RO_m.get g₁ = FMap.noflags (FRO_m.get g₂)) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_skip
  rintro x y _ _ _ m ⟨h, rfl⟩
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  exact (FMap.map_set _ m x (y, Known)).symm

/-- `equiv RO_FRO_rem : RO.rem ~ FRO.rem : ={x} /\ RO.m{1} = noflags FRO.m{2} ==>
RO.m{1} = noflags FRO.m{2}`. -/
theorem RO_FRO_rem :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ RO_m.get g₁ = FMap.noflags (FRO_m.get g₂))
    (ROmap.rem in_t out_t (RO in_t out_t dout RO_m)).procedure
    (FRO_T.rem in_t out_t (FRO in_t out_t dout FRO_m)).procedure
    (fun _ g₁ _ g₂ => RO_m.get g₁ = FMap.noflags (FRO_m.get g₂)) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_skip
  rintro x _ _ m ⟨rfl, rfl⟩
  exact (FMap.map_rem _ _ _).symm

/-- `equiv RO_FRO_sample : RO.sample ~ FRO.sample : ={x} /\ RO.m{1} = noflags FRO.m{2} ==>
RO.m{1} = noflags FRO.m{2}`. -/
theorem RO_FRO_sample :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ RO_m.get g₁ = FMap.noflags (FRO_m.get g₂))
    (ROmap.sample in_t out_t (RO in_t out_t dout RO_m)).procedure
    (FRO_T.sample in_t out_t (FRO in_t out_t dout FRO_m)).procedure
    (fun _ g₁ _ g₂ => RO_m.get g₁ = FMap.noflags (FRO_m.get g₂)) := by
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  rintro x _ _ m ⟨rfl, rfl⟩
  refine ⟨rfl, fun a _ => ?_⟩
  have hd : FMap.dom (FMap.noflags m) x ↔ FMap.dom m x := FMap.mem_map _ _ _
  by_cases h : FMap.dom m x
  · simp [h, hd.mpr h]
  · simp [h, FMap.noflags, FMap.mem_map, FMap.map_set]

variable (d_in_t d_out_t : Type)

/-- `equiv RO_FRO_D (D <: RO_Distinguisher { -RO, -FRO }) : D(RO).distinguish ~
D(FRO).distinguish : ={arg, glob D} /\ RO.m{1} = noflags FRO.m{2} ==>
={res, glob D} /\ RO.m{1} = noflags FRO.m{2}`.  `RO.m` and `FRO.m` are distinct variables, and the
oracles' arguments countable (exception E8). -/
theorem RO_FRO_D [Countable in_t] [Countable out_t] [Lens.Disjoint RO_m FRO_m]
    (D : RO_Distinguisher in_t out_t d_in_t d_out_t)
    (hD : Module.ECModule D (RO_ext in_t out_t))
    (hdisj : FVP.fvP D ≤ (RO_m.footprint ⊔ FRO_m.footprint)ᶜ) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧
        (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂ ∧
        RO_m.get g₁ = FMap.noflags (FRO_m.get g₂))
      (Module.app D (RO.asRO in_t out_t dout RO_m)).procedure
      (Module.app D (FRO.asRO in_t out_t dout FRO_m)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂ ∧
        RO_m.get g₁ = FMap.noflags (FRO_m.get g₂)) := by
  have hRO : RO_m.footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (hdisj.trans (Footprint.compl_antimono le_sup_left))
  have hFRO : FRO_m.footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (hdisj.trans (Footprint.compl_antimono le_sup_right))
  have hL : FVP.fvP D ≤ ((Lens.pair RO_m FRO_m).footprint)ᶜ := by
    rw [Footprint.lens_pair]; exact hdisj
  exact prhlProc_abstract_call_module (Lens.pair RO_m FRO_m) D (RO_ext in_t out_t)
    hD.representable hL (fun a b => a.1 = FMap.noflags b.2)
    (fun n => by
      cases n with
      | zero => exact inferInstanceAs (Countable Unit)
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable in_t)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable (in_t × out_t))
          | succ n => cases n with
            | zero => exact inferInstanceAs (Countable in_t)
            | succ n => cases n with
              | zero => exact inferInstanceAs (Countable in_t)
              | succ n => nomatch n)
    (RO.asRO in_t out_t dout RO_m) (FRO.asRO in_t out_t dout FRO_m) (fun n => by
      -- EC: `proc (RO.m{1} = noflags FRO.m{2}) => //; conseq RO_FRO_init …`
      refine prhlProc_conseq (prhlProc_globInvF_of_writesKeep _ ?_ ?_ ?_) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => ⟨h.1, h.2⟩)
      all_goals cases n with
      | zero =>
        simp only [RO_ext, RO.asRO, FRO.asRO, RO_T.init.mk_simp,
          HoleSigs.Instantiation.lookup_zero_cons]
        first
          | writes_keep; done
          | exact prhlProc_conseq (RO_FRO_init in_t out_t dout RO_m FRO_m)
              (fun _ _ _ _ _ => trivial) fun _ _ _ _ h => ⟨trivial, h⟩
      | succ n => cases n with
      | zero =>
        simp only [RO_ext, RO.asRO, FRO.asRO, RO_T.get.mk_simp,
          HoleSigs.Instantiation.lookup_succ, HoleSigs.Instantiation.lookup_zero_cons]
        first
          | writes_keep; done
          | exact RO_FRO_get in_t out_t dout RO_m FRO_m
      | succ n => cases n with
      | zero =>
        simp only [RO_ext, RO.asRO, FRO.asRO, RO_T.set.mk_simp,
          HoleSigs.Instantiation.lookup_succ, HoleSigs.Instantiation.lookup_zero_cons]
        first
          | writes_keep; done
          | exact prhlProc_conseq (RO_FRO_set in_t out_t dout RO_m FRO_m)
              (fun _ _ _ _ h => h) fun _ _ _ _ h => ⟨trivial, h⟩
      | succ n => cases n with
      | zero =>
        simp only [RO_ext, RO.asRO, FRO.asRO, RO_T.rem.mk_simp,
          HoleSigs.Instantiation.lookup_succ, HoleSigs.Instantiation.lookup_zero_cons]
        first
          | writes_keep; done
          | exact prhlProc_conseq (RO_FRO_rem in_t out_t dout RO_m FRO_m)
              (fun _ _ _ _ h => h) fun _ _ _ _ h => ⟨trivial, h⟩
      | succ n => cases n with
      | zero =>
        simp only [RO_ext, RO.asRO, FRO.asRO, RO_T.sample.mk_simp,
          HoleSigs.Instantiation.lookup_succ, HoleSigs.Instantiation.lookup_zero_single]
        first
          | writes_keep; done
          | exact prhlProc_conseq (RO_FRO_sample in_t out_t dout RO_m FRO_m)
              (fun _ _ _ _ h => h) fun _ _ _ _ h => ⟨trivial, h⟩
      | succ n => nomatch n)

end RO_FRO

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

/-- `RRO` at the type `RO` (EasyCrypt's subtyping `FRO <: RO`: `D(RRO)` for an
`RO_Distinguisher D`). -/
noncomputable def RRO.asRO : RO_T in_t out_t :=
  RO_T.mk in_t out_t
    { init := FRO_T.init in_t out_t (RRO in_t out_t dout m)
      get := FRO_T.get in_t out_t (RRO in_t out_t dout m)
      set := FRO_T.set in_t out_t (RRO in_t out_t dout m)
      rem := FRO_T.rem in_t out_t (RRO in_t out_t dout m)
      sample := FRO_T.sample in_t out_t (RRO in_t out_t dout m) }

end RRO

section EagerCore

variable (in_t out_t d_in_t d_out_t : Type) [DecidableEq in_t] [Inhabited in_t] [Inhabited out_t]
  [Inhabited d_in_t] [Inhabited d_out_t] (dout : in_t → SubProbability out_t)
  (FRO_m : Lens (FMap in_t (out_t × flag)) VariableAssignment)

/-- `RRO.resample();`, the block of PROM's eager judgments, as a program on the globals. -/
noncomputable abbrev RRO.resampleDen : ProgramDenotation VariableAssignment Unit :=
  procedureDenotation (RRO.own.resample in_t out_t dout FRO_m).procedure ()

/-- `RRO.resample` touches only `FRO.m` (EC: by its code). -/
theorem RRO.resample_fvP :
    FVP.fvP_proc (RRO.own.resample in_t out_t dout FRO_m).procedure ≤ FRO_m.footprint :=
  FVP.fvP_proc_le_of_within _ (by within_lens) (by within_lens)

theorem RRO.resample_inFootprint :
    (RRO.resampleDen in_t out_t dout FRO_m).inFootprint FRO_m.footprint :=
  ProgramDenotation.inFootprint_mono
    (Lib.RO.Instantiate.procedureDenotation_inFootprint_fvP_proc
      (RRO.own.resample in_t out_t dout FRO_m).procedure ())
    (RRO.resample_fvP in_t out_t dout FRO_m)

/-- `RRO.resample()` keeps every region outside `FRO.m`, `glob D` in particular. -/
theorem RRO.resample_keeps {F : Footprint VariableAssignment} (hF : FRO_m.footprint ≤ Fᶜ)
    (g : VariableAssignment) :
    (RRO.resampleDen in_t out_t dout FRO_m g).satisfies
      (fun u => F.touched_getter.get u.2 = F.touched_getter.get g) := by
  intro u hu
  have hc := ProgramDenotation.preserves_compl_of_inFootprint FRO_m
    (RRO.resample_inFootprint in_t out_t dout FRO_m) g u hu
  have : u.2 = FRO_m.set (FRO_m.get u.2) g :=
    Lens.eq_of_get_compl_get FRO_m (FRO_m.set_get _ _).symm
      (by rw [hc, Lens.compl_get_set])
  rw [this, touched_set_of_le_compl hF]

/-- `RRO.I.f`'s run: sample `c`, write `FRO.m.[t] <- (c, Unknown)`. -/
theorem RRO.I_f_denotation (t : in_t) (g : VariableAssignment) :
    procedureDenotation (RRO.I.f.procedure in_t out_t dout FRO_m) t g =
      (dout t).hbind fun c => pure ((), FRO_m.set (FMap.set (FRO_m.get g) t (c, Unknown)) g) := by
  refine SubProbability.ext_of_expected fun F => ?_
  simp only [procedureDenotation, RRO.I.f.procedure, SubProbability.expected_hbind,
    programDenotation_seq, ProgramDenotation.bind_apply, SubProbability.expected_bind,
    programDenotation_sample_apply, programDenotation_assign_apply, expected_pure]
  have hx : (localVarLens "x" in_t).get
      ⟨g, (RRO.I.f.procedure in_t out_t dout FRO_m).initLocals t⟩ = t := by
    simp [ProcedureWithHoles.initLocals, VariableAssignment.setParams, localVarLens,
      RRO.I.f.procedure]
    exact (varLens (VariableName.mk "x" in_t)).set_get _ _
  simp_reads
  erw [hx]

theorem RRO.I_f_procedure :
    (IterProc.Orcl.f in_t (RRO.I in_t out_t dout FRO_m)).procedure =
      RRO.I.f.procedure in_t out_t dout FRO_m := by
  simp only [IterProc.Orcl.f, RRO.I, RRO.I.f, Module.procedure_proc']

/-- `equiv iter_perm2 : Iter(RRO.I).iter_12 ~ Iter(RRO.I).iter_21 : ={glob RRO.I, t1, t2} ==>
={glob RRO.I}`, denotationally (exception E9: the form `iter_perm` and `iter1_perm` take).  EC:
`proc; inline*; case: ((t1 = t2){1}); first by auto. swap{2} [4..5] -3; auto … set_setE`. -/
theorem iter_perm2 (t₁ t₂ : in_t) :
    (procedureDenotation (IterProc.Orcl.f in_t (RRO.I in_t out_t dout FRO_m)).procedure t₁ >>=
        fun _ =>
          procedureDenotation (IterProc.Orcl.f in_t (RRO.I in_t out_t dout FRO_m)).procedure t₂) =
      (procedureDenotation (IterProc.Orcl.f in_t (RRO.I in_t out_t dout FRO_m)).procedure t₂ >>=
        fun _ =>
        procedureDenotation (IterProc.Orcl.f in_t (RRO.I in_t out_t dout FRO_m)).procedure t₁) := by
  rw [RRO.I_f_procedure]
  by_cases h : t₁ = t₂
  · subst h; rfl
  funext g
  refine SubProbability.ext_of_expected fun F => ?_
  simp only [ProgramDenotation.bind_apply, RRO.I_f_denotation, SubProbability.expected_bind,
    SubProbability.expected_hbind, expected_pure, FRO_m.set_get, FRO_m.set_set]
  rw [SubProbability.expected_comm]
  refine congrArg _ (funext fun c₂ => congrArg _ (funext fun c₁ => ?_))
  rw [FMap.set_setE, if_neg h]

/-- `RRO.I.f` is lossless (EC: `proc; auto=> /> &m'; exact/dout_ll` in `RRO_resample_ll`). -/
theorem RRO_I_f_ll (dout_ll : ∀ x, (dout x).1 Set.univ = 1) :
    (IterProc.Orcl.f in_t (RRO.I in_t out_t dout FRO_m)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 5
  phoare_skip
  intro _ _
  simp [SubProbability.expected, dout_ll]

/-- `lemma RRO_resample_ll : islossless RRO.resample`.  EC: `proc; call (iter_ll RRO.I _)=> //.
by proc; auto=> /> &m'; exact/dout_ll.` -/
theorem RRO_resample_ll (dout_ll : ∀ x, (dout x).1 Set.univ = 1) :
    (RRO.own.resample in_t out_t dout FRO_m).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 3
  phoare_skip
  intro σ _ _
  have hll := IterProc.iter_ll (RRO.I in_t out_t dout FRO_m)
    (RRO_I_f_ll in_t out_t dout FRO_m dout_ll)
  rw [IterProc.Iter.iter.apply_simp, Module.procedure_proc'] at hll
  simp only [IterProc.Orcl.f, RRO.I, RRO.I.f, Module.procedure_proc'] at hll
  exact hll.ewp_const _ _ _

/-- `eager [RRO.resample();, FRO.init ~ RRO.init, RRO.resample(); : ={FRO.m} ==> ={FRO.m}]`, at
equality invariants (exception E10). -/
theorem eager_init (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.init in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.init in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  -- EC: `eager proc. inline{2} *; rcondf{2} 3; auto=> />.
  -- + by rewrite restr0 fdom0 elems_fset0. by call{1} RRO_resample_ll.`
  refine eagerR_of_prhlStmt FRO_m _ _ _ a (y := localVarLens "r" Unit) (fun _ _ => rfl)
    (RRO.resample_inFootprint in_t out_t dout FRO_m)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) a)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) a)
    (fun _ _ => rfl) ?_
  unfold eagerLeftStmt eagerRightStmt
  repeat stmt_inline{2} 0
  equiv_rcondf{2}
  stmt_inline{1} 1
  stmt_wp
  -- EC's `call{1} RRO_resample_ll`
  unfold prhlStmt
  rw [show programDenotation (StmtWithHoles.skip (h := .empty)) =
    (pure () : ProgramDenotation ProgramState Unit) from funext programDenotation_skip_apply]
  refine ProgramDenotation.prhl2.kill_left' fun σ₁ σ₂ _ =>
    ⟨Stmt.call_wp_one (RRO_resample_ll in_t out_t dout FRO_m dout_ll) _ _ _,
      Stmt.call_satisfies fun _ _ => ?_⟩
  simp [FMap.restr0, FMap.fdom0]

/-- `RRO.resample()`'s run: `Iter(RRO.I).iter` over the `Unknown` entries. -/
theorem RRO.resample_denotation (g : VariableAssignment) :
    procedureDenotation (RRO.own.resample in_t out_t dout FRO_m).procedure () g =
      procedureDenotation
        (Module.app (IterProc.Iter.iter in_t) (RRO.I in_t out_t dout FRO_m)).procedure
        (FMap.fdom (FMap.restr Unknown (FRO_m.get g))).toList g := by
  rw [RRO.own.resample, Module.procedure_proc']
  refine SubProbability.ext_of_expected fun F => ?_
  simp only [procedureDenotation, RRO.own.resample.procedure, SubProbability.expected_hbind,
    programDenotation_hcall_apply, expected_pure, IterProc.Iter.apply_simp]
  simp_reads
  rfl

/-- `RRO.resample()` as the call of `Iter(RRO.I).iter` it makes. -/
theorem RRO.resample_call_eq :
    programDenotation (StmtWithHoles.call (h := .empty) Setter.throwaway
        (RRO.own.resample in_t out_t dout FRO_m).procedure ⟨fun _ => ()⟩) =
      programDenotation (StmtWithHoles.call (h := .empty) Setter.throwaway
        (Module.app (IterProc.Iter.iter in_t) (RRO.I in_t out_t dout FRO_m)).procedure
        GaudiExpr[ (FMap.fdom (FMap.restr Unknown ($FRO_m : FMap in_t (out_t × flag)))).toList ]) :=
    by
  funext σ
  rw [programDenotation_hcall_apply, programDenotation_hcall_apply,
    RRO.resample_denotation]
  simp_reads
  trivial

/-- From a state where `x` is bound with flag `Unknown`, `RRO.resample()` is `RRO.I.f(x)` then
the iteration over the other `Unknown` entries (EC's `Iter(RRO.I).iter_1s(x, elems (fdom (restr
Unknown FRO.m) `\` fset1 x))`, by `iter1_perm RRO.I iter_perm2`). -/
theorem RRO.resample_call_split (x : in_t) (σ : ProgramState)
    (hx : FMap.in_dom_with (FRO_m.get σ.globals) x Unknown) :
    programDenotation (StmtWithHoles.call (h := .empty) Setter.throwaway
        (RRO.own.resample in_t out_t dout FRO_m).procedure ⟨fun _ => ()⟩) σ =
      programDenotation (StmtWithHoles.seq
        (StmtWithHoles.call (h := .empty) Setter.throwaway
          (IterProc.Orcl.f in_t (RRO.I in_t out_t dout FRO_m)).procedure ⟨fun _ => x⟩)
        (StmtWithHoles.call (h := .empty) Setter.throwaway
          (Module.app (IterProc.Iter.iter in_t) (RRO.I in_t out_t dout FRO_m)).procedure
          GaudiExpr[ (FMap.fdom (FMap.restr Unknown ($FRO_m : FMap in_t (out_t × flag))) \ {x}
            ).toList ])) σ := by
  set S := FMap.fdom (FMap.restr Unknown (FRO_m.get σ.globals)) with hSdef
  have hS : x ∈ S := (FMap.mem_fdom _ _).mpr ((FMap.dom_restr _ _ _).mpr hx)
  have hperm : (x :: (S \ {x}).toList).Perm S.toList := by
    rw [Finset.sdiff_singleton_eq_erase]
    have := Finset.toList_insert (Finset.notMem_erase x S)
    rw [Finset.insert_erase hS] at this
    exact this.symm
  rw [RRO.resample_call_eq, programDenotation_seq, ProgramDenotation.bind_apply,
    programDenotation_hcall_apply, programDenotation_hcall_apply]
  have hL : ∀ c : out_t, (FMap.fdom (FMap.restr Unknown
      (FMap.set (FRO_m.get σ.globals) x (c, Unknown))) \ {x}).toList = (S \ {x}).toList := by
    intro c
    rw [FMap.restr_set_eq, FMap.fdom_set,
      Finset.insert_sdiff_of_mem _ (Finset.mem_singleton_self x)]
  have hiter := (IterProc.iter1_perm (RRO.I in_t out_t dout FRO_m)
    (iter_perm2 in_t out_t dout FRO_m) hperm).symm
  erw [hiter]
  refine SubProbability.ext_of_expected fun F => ?_
  simp only [ProgramDenotation.bind_apply, SubProbability.expected_hbind,
    SubProbability.expected_bind, RRO.I_f_procedure, RRO.I_f_denotation, expected_pure,
    programDenotation_hcall_apply]
  refine congrArg _ (funext fun c => ?_)
  simp_reads
  have hg : (Setter.throwaway.set () (ProgramState.globalL.set
      (FRO_m.set ((FRO_m.get σ.globals).set x (c, Unknown)) σ.globals) σ)).globals =
      FRO_m.set ((FRO_m.get σ.globals).set x (c, Unknown)) σ.globals := rfl
  rw [hg, FRO_m.set_get, hL c]
  rfl

/-- `equiv I_f_eqex x1 mx1 mx2 : RRO.I.f ~ RRO.I.f : ={x} /\ x1 <> x{1} /\
eq_except (pred1 x1) FRO.m{1} FRO.m{2} /\ FRO.m{1}.[x1] = mx1 /\ FRO.m{2}.[x1] = mx2 ==>
eq_except (pred1 x1) FRO.m{1} FRO.m{2} /\ FRO.m{1}.[x1] = mx1 /\ FRO.m{2}.[x1] = mx2`. -/
theorem I_f_eqex (x1 : in_t) (mx1 mx2 : Option (out_t × flag)) :
    prhlProc (sig₁ := procsig (in_t) → Unit) (sig₂ := procsig (in_t) → Unit)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ x1 ≠ a₁ ∧
        (FMap.eq_except (· = x1) (FRO_m.get g₁) (FRO_m.get g₂) ∧
          FMap.get (FRO_m.get g₁) x1 = mx1 ∧ FMap.get (FRO_m.get g₂) x1 = mx2))
      (IterProc.Orcl.f in_t (RRO.I in_t out_t dout FRO_m)).procedure
      (IterProc.Orcl.f in_t (RRO.I in_t out_t dout FRO_m)).procedure
      (fun _ g₁ _ g₂ => FMap.eq_except (· = x1) (FRO_m.get g₁) (FRO_m.get g₂) ∧
          FMap.get (FRO_m.get g₁) x1 = mx1 ∧ FMap.get (FRO_m.get g₂) x1 = mx2) := by
  rw [RRO.I_f_procedure]
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  rintro x m₁ _ m₂ ⟨rfl, hx, he, h1, h2⟩
  refine ⟨rfl, fun c _ => ⟨FMap.eq_except_set _ he _ _ _ fun _ => rfl, ?_, ?_⟩⟩
  · rw [FMap.get_set_neqE _ _ _ _ hx, h1]
  · rw [FMap.get_set_neqE _ _ _ _ hx, h2]

/-- `equiv I_f_neq x1 mx1 : RRO.I.f ~ RRO.I.f : ={x, FRO.m} /\ x1 <> x{1} /\ FRO.m{1}.[x1] = mx1
==> ={FRO.m} /\ FRO.m{1}.[x1] = mx1`. -/
theorem I_f_neq (x1 : in_t) (mx1 : Option (out_t × flag)) :
    prhlProc (sig₁ := procsig (in_t) → Unit) (sig₂ := procsig (in_t) → Unit)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ x1 ≠ a₁ ∧
        (FRO_m.get g₁ = FRO_m.get g₂ ∧ FMap.get (FRO_m.get g₁) x1 = mx1))
      (IterProc.Orcl.f in_t (RRO.I in_t out_t dout FRO_m)).procedure
      (IterProc.Orcl.f in_t (RRO.I in_t out_t dout FRO_m)).procedure
      (fun _ g₁ _ g₂ => FRO_m.get g₁ = FRO_m.get g₂ ∧ FMap.get (FRO_m.get g₁) x1 = mx1) := by
  rw [RRO.I_f_procedure]
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  rintro x m _ _ ⟨rfl, hx, rfl, h1⟩
  exact ⟨rfl, fun c _ => ⟨rfl, by rw [FMap.get_set_neqE _ _ _ _ hx, h1]⟩⟩

/-- `equiv I_f_set x1 r1 : RRO.I.f ~ RRO.I.f : ={x} /\ x1 <> x{1} /\ FRO.m{1}.[x1] = None /\
FRO.m{2} = FRO.m{1}.[x1 <- (r1, Known)] ==> FRO.m{1}.[x1] = None /\
FRO.m{2} = FRO.m{1}.[x1 <- (r1, Known)]`. -/
theorem I_f_set (x1 : in_t) (r1 : out_t) :
    prhlProc (sig₁ := procsig (in_t) → Unit) (sig₂ := procsig (in_t) → Unit)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ x1 ≠ a₁ ∧
        (FMap.get (FRO_m.get g₁) x1 = none ∧
          FRO_m.get g₂ = FMap.set (FRO_m.get g₁) x1 (r1, Known)))
      (IterProc.Orcl.f in_t (RRO.I in_t out_t dout FRO_m)).procedure
      (IterProc.Orcl.f in_t (RRO.I in_t out_t dout FRO_m)).procedure
      (fun _ g₁ _ g₂ => FMap.get (FRO_m.get g₁) x1 = none ∧
          FRO_m.get g₂ = FMap.set (FRO_m.get g₁) x1 (r1, Known)) := by
  rw [RRO.I_f_procedure]
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  rintro x m₁ _ m₂ ⟨rfl, hx, h1, rfl⟩
  refine ⟨rfl, fun c _ => ⟨by rw [FMap.get_set_neqE _ _ _ _ hx, h1], ?_⟩⟩
  rw [FMap.set_setE, if_neg hx]

/-- `eager [RRO.resample();, FRO.get ~ RRO.get, RRO.resample(); : ={x, FRO.m} ==>
={res, FRO.m}]`, at equality invariants (exception E10). -/
theorem eager_get (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a : in_t) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.get in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.get in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  refine eagerR_of_prhlStmt FRO_m _ _ _ _ (y := localVarLens "r" out_t) (fun _ _ => rfl)
    (RRO.resample_inFootprint in_t out_t dout FRO_m)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) _)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) _)
    (fun _ _ => rfl) ?_
  unfold eagerLeftStmt eagerRightStmt
  refine prhlStmt_seq_congr_right_snd (RRO.resample_call_eq in_t out_t dout FRO_m) ?_
  -- EC: `eager proc. wp; case ((x \in FRO.m /\ FRO.m.[x] \is Known){1}).`
  refine prhlStmt_case (fun σ₁ _ => FMap.in_dom_with (FRO_m.get σ₁.globals) a Known) ?_ ?_
  · refine prhlStmt_seq_congr_left
      (fun _ _ _ => congrFun (RRO.resample_call_eq in_t out_t dout FRO_m) _) ?_
    stmt_inline{1} 1
    stmt_inline{2} 0
    stmt_wp
    -- EC: `rnd{1}; rcondf{2} 2; …; exists* x{1}, ((oget FRO.m.[x{2}]){1}); elim * => x1 mx;
    -- inline RRO.resample. call (iter_inv RRO.I (fun z=> x1<>z)
    -- (fun o1 o2 => o1 = o2 /\ o1.[x1]= Some mx) _)`
    stmt_wp{1} 1
    stmt_wp
    refine prhlStmt_fix_left (fun σ₁ => FMap.get (FRO_m.get σ₁.globals) a) fun v => ?_
    equiv_call (IterProc.iter_inv (RRO.I in_t out_t dout FRO_m) (fun z => a ≠ z)
      (fun g₁ g₂ => FRO_m.get g₁ = FRO_m.get g₂ ∧ FMap.get (FRO_m.get g₁) a = v)
      (I_f_neq in_t out_t dout FRO_m a v))
    stmt_wp
    stmt_wp{2} 1
    stmt_wp
    equiv_skip
    rintro σ₁ σ₂ ⟨⟨hm, hK⟩, rfl⟩
    rw [hm] at hK ⊢
    obtain ⟨hd, hf⟩ := hK
    obtain ⟨⟨w, k⟩, hw⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd)
    rw [hw] at hf
    simp only [Option.getD_some] at hf
    subst hf
    simp only [hd, hw, is_, oget, Option.getD_some, decide_true, Bool.not_true, Bool.false_or,
      reduceCtorEq, decide_false, Bool.false_eq_true, if_false, ite_self]
    refine ⟨by simp [SubProbability.expected, dout_ll], fun _ _ => ⟨⟨by first | rfl | trivial,
      fun z hz => ?_, by first | rfl | trivial, by first | rfl | trivial⟩,
        fun r₁ g₁ r₂ g₂ ⟨hg, hv⟩ => ⟨by simp [SubProbability.expected, dout_ll],
        fun _ _ => ?_⟩⟩⟩
    · rw [Finset.mem_toList, FMap.mem_fdom, FMap.dom_restr] at hz
      rintro rfl
      have := hz.2
      rw [hw] at this
      simp at this
    · have e1 : FRO_m.get (Setter.throwaway.set r₁ (ProgramState.globalL.set g₁ σ₁)).globals =
          FRO_m.get g₁ := rfl
      have e2 : ∀ τ, (Setter.throwaway.set r₂ (ProgramState.globalL.set g₂ τ)).globals = g₂ :=
        fun _ => rfl
      have e3 : ∀ τ, (localVarLens "r" out_t).get (Setter.throwaway.set r₂
          (ProgramState.globalL.set g₂ ((localVarLens "r" out_t).set w τ))) = w :=
        fun τ => (localVarLens "r" out_t).set_get τ w
      simp only [e1, e2, e3]
      have hd' : FMap.dom (FRO_m.get g₁) a := by simp [FMap.domE, hv]
      simp only [hd', decide_true, if_true, hv, Option.getD_some]
      exact ⟨trivial, by rw [← hg]; exact FMap.get_set_id _ _ _ hv⟩
  · -- EC: `case ((x \in FRO.m){1}).`
    refine prhlStmt_case (fun σ₁ _ => FMap.dom (FRO_m.get σ₁.globals) a) ?_ ?_
    · -- EC: `inline{1} RRO.resample=> /=; rnd{1}. transitivity{1}
      -- { Iter(RRO.I).iter_1s(x, elems ((fdom (restr Unknown FRO.m)) `\` fset1 x)); } …`
      refine prhlStmt_seq_congr_left (fun σ₁ _ h => RRO.resample_call_split in_t out_t dout FRO_m
        a σ₁ ⟨h.2, ?_⟩) ?_
      · have hK := h.1.2
        unfold FMap.in_dom_with at hK
        cases hf : ((FMap.get (FRO_m.get σ₁.globals) a).getD default).2 with
        | Unknown => rfl
        | Known => exact absurd ⟨h.2, hf⟩ hK
      stmt_inline{1} 2
      stmt_inline{2} 0
      stmt_wp
      stmt_wp{1} 1
      stmt_wp
      -- EC: `seq 5 3 : (={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\ … /\
      -- FRO.m{1}.[x{2}] = Some (result{2}, Unknown) /\ FRO.m{2}.[x{2}] = Some (result{2}, Known))`
      equiv_seq_last 1 1 : (FMap.eq_except (· = a) §FRO_m{1} §FRO_m{2} ∧
        FMap.get §FRO_m{1} a = some (§r{2}, Unknown) ∧ FMap.get §FRO_m{2} a = some (§r{2}, Known))
      case h₁ =>
        stmt_inline{1} 0
        stmt_wp
        equiv_rnd
        stmt_wp
        equiv_skip
        rintro σ₂ _ ⟨⟨rfl, hK⟩, hd⟩ c _
        obtain ⟨⟨w, k⟩, hw⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd)
        have hk : k = Unknown := by
          cases k with
          | Unknown => rfl
          | Known => exact absurd ⟨hd, by rw [hw]; rfl⟩ hK
        subst hk
        simp only [hd, hw, is_, oget, Option.getD_some, decide_true, Bool.not_true,
          Bool.false_or, if_true, FMap.get_set_sameE]
        exact ⟨FMap.eq_except_set (fun x => x = a) (FMap.eq_except_refl _ _) a _ _
          (fun h => absurd rfl h), trivial, trivial⟩
      case h₂ =>
        -- EC: `exists* x{1}, FRO.m{1}.[x{2}], FRO.m{2}.[x{2}]; elim*=> x1 mx1 mx2.
        -- call (iter_inv RRO.I (fun z => x1 <> z) (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\
        -- o1.[x1] = mx1 /\ o2.[x1] = mx2) (I_f_eqex x1 mx1 mx2))`
        refine prhlStmt_fix_right (fun σ₂ => (localVarLens "r" out_t).get σ₂) fun ρ => ?_
        equiv_call (IterProc.iter_inv (RRO.I in_t out_t dout FRO_m) (fun z => a ≠ z)
          (fun g₁ g₂ => FMap.eq_except (· = a) (FRO_m.get g₁) (FRO_m.get g₂) ∧
            FMap.get (FRO_m.get g₁) a = some (ρ, Unknown) ∧
            FMap.get (FRO_m.get g₂) a = some (ρ, Known))
          (I_f_eqex in_t out_t dout FRO_m a (some (ρ, Unknown)) (some (ρ, Known))))
        equiv_skip
        rintro σ₁ σ₂ ⟨⟨he, h1, h2⟩, hρ⟩
        rw [hρ] at h1 h2
        refine ⟨⟨?_, fun z hz => ?_, he, h1, h2⟩, fun r₁ g₁ r₂ g₂ ⟨he', h1', h2'⟩ =>
          ⟨by simp [SubProbability.expected, dout_ll], fun _ _ => ?_⟩⟩
        · congr 1
          ext z
          rw [Finset.mem_sdiff, Finset.mem_singleton, FMap.mem_fdom, FMap.mem_fdom,
            FMap.dom_restr, FMap.dom_restr]
          by_cases hz : z = a
          · subst hz
            simp only [not_true_eq_false, and_false, false_iff]
            intro h
            have h3 := h.2
            rw [h2] at h3
            exact absurd h3 (show Known ≠ Unknown by decide)
          · simp only [hz, not_false_eq_true, and_true]
            exact FMap.in_dom_with_congr (he z hz) _
        · rw [Finset.mem_toList, Finset.mem_sdiff, Finset.mem_singleton] at hz
          exact fun h => hz.2 h.symm
        · have e1 : FRO_m.get (Setter.throwaway.set r₁ (ProgramState.globalL.set g₁ σ₁)).globals =
              FRO_m.get g₁ := rfl
          have e2 : (localVarLens "r" out_t).get
              (Setter.throwaway.set r₂ (ProgramState.globalL.set g₂ σ₂)) = ρ := hρ
          have e3 : (Setter.throwaway.set r₂ (ProgramState.globalL.set g₂ σ₂)).globals = g₂ := rfl
          simp only [e1, e2, e3]
          have hd' : FMap.dom (FRO_m.get g₁) a := by simp [FMap.domE, h1']
          simp only [hd', decide_true, if_true, h1', oget, Option.getD_some]
          exact ⟨trivial, FMap.set_eq_of_eq_except he' h2'⟩
    · -- EC: `swap{1} -1; seq 1 1 : (={r, x, FRO.m} /\ ! dom FRO.m{1} x{1}); 1:by auto.`
      refine prhlStmt_seq_congr_left
        (fun _ _ _ => congrFun (RRO.resample_call_eq in_t out_t dout FRO_m) _) ?_
      stmt_inline{1} 1
      stmt_inline{2} 0
      stmt_wp
      stmt_swap{1} 1 3
      equiv_seq_last 1 1 : (§x{1} = a ∧ FMap.get §FRO_m{1} a = none ∧
        §FRO_m{2} = FMap.set §FRO_m{1} a (§r0{1}, Known) ∧ §r{2} = §r0{1})
      case h₁ =>
        stmt_wp
        equiv_rnd
        stmt_wp
        equiv_skip
        rintro σ₂ _ ⟨⟨rfl, -⟩, hnd⟩ c _
        simp only [hnd, decide_false, Bool.not_false, Bool.true_or, if_true,
          FMap.get_set_sameE, oget, Option.getD_some]
        exact ⟨by simpa [FMap.domE] using hnd, trivial, trivial⟩
      case h₂ =>
        -- EC: `inline RRO.resample; exists* x{1},r{1}; elim*=> x1 r1. call (iter_inv RRO.I
        -- (fun z=> x1 <> z) (fun o1 o2 => o1.[x1] = None /\ o2 = o1.[x1 <- (r1, Known)])
        -- (I_f_set x1 r1)); auto.`
        refine prhlStmt_fix_left (fun σ₁ => (localVarLens "r0" out_t).get σ₁) fun r1 => ?_
        equiv_call (IterProc.iter_inv (RRO.I in_t out_t dout FRO_m) (fun z => a ≠ z)
          (fun g₁ g₂ => FMap.get (FRO_m.get g₁) a = none ∧
            FRO_m.get g₂ = FMap.set (FRO_m.get g₁) a (r1, Known))
          (I_f_set in_t out_t dout FRO_m a r1))
        equiv_skip
        rintro σ₁ σ₂ ⟨⟨hx, h1, h2, hr⟩, hr1⟩
        rw [hr1] at h2 hr
        refine ⟨⟨?_, fun z hz => ?_, h1, h2⟩, fun r₁ g₁ r₂ g₂ ⟨h1', h2'⟩ => ?_⟩
        · rw [h2, FMap.restr_set, if_neg (by decide), FMap.rem_id _ _ ?_]
          rw [FMap.dom_restr]
          exact fun h => absurd ((FMap.domE _ _).mp h.1) (by rw [h1]; exact fun h => h rfl)
        · rw [Finset.mem_toList, FMap.mem_fdom, FMap.dom_restr] at hz
          rintro rfl
          exact absurd ((FMap.domE _ _).mp hz.1) (by rw [h1]; exact fun h => h rfl)
        · have e1 : FRO_m.get (Setter.throwaway.set r₁ (ProgramState.globalL.set g₁ σ₁)).globals =
              FRO_m.get g₁ := rfl
          have ex : (localVarLens "x" in_t).get
              (Setter.throwaway.set r₁ (ProgramState.globalL.set g₁ σ₁)) = a := hx
          have e0 : (localVarLens "r0" out_t).get
              (Setter.throwaway.set r₁ (ProgramState.globalL.set g₁ σ₁)) = r1 := hr1
          have er : (localVarLens "r" out_t).get
              (Setter.throwaway.set r₂ (ProgramState.globalL.set g₂ σ₂)) = r1 := hr
          have e3 : (Setter.throwaway.set r₂ (ProgramState.globalL.set g₂ σ₂)).globals = g₂ := rfl
          simp only [e1, ex, e0, er, e3]
          have hnd : ¬ FMap.dom (FRO_m.get g₁) a := by simp [FMap.domE, h1']
          simp only [hnd, decide_false, Bool.false_eq_true, if_false, ite_self]
          exact ⟨trivial, h2'.symm⟩

/-- `eager [RRO.resample();, FRO.set ~ RRO.set, RRO.resample(); : ={x, y} /\ ={FRO.m} ==>
={res, FRO.m}]`, at equality invariants (exception E10). -/
theorem eager_set (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a : (in_t × out_t)) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.set in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.set in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  -- EC: `eager proc. inline RRO.resample=> /=; wp.
  -- case ((x \in FRO.m /\ FRO.m.[x] \is Unknown){1}).`
  refine eagerR_of_prhlStmt FRO_m _ _ _ _ (y := localVarLens "r" Unit) (fun _ _ => rfl)
    (RRO.resample_inFootprint in_t out_t dout FRO_m)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) _)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) _)
    (fun _ _ => rfl) ?_
  unfold eagerLeftStmt eagerRightStmt
  refine prhlStmt_seq_congr_right_snd (RRO.resample_call_eq in_t out_t dout FRO_m) ?_
  refine prhlStmt_case (fun σ₁ _ => FMap.in_dom_with (FRO_m.get σ₁.globals) a.1 Unknown) ?_ ?_
  · -- EC: `transitivity{1}
    -- { Iter(RRO.I).iter_1s(x, elems (fdom (restr Unknown FRO.m) `\` fset1 x)); }`
    refine prhlStmt_seq_congr_left
      (fun σ₁ _ h => RRO.resample_call_split in_t out_t dout FRO_m a.1 σ₁ h.2) ?_
    stmt_inline{1} 2
    stmt_inline{2} 0
    stmt_wp
    -- EC: `seq 3 1 : (={x, y} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\ … /\
    -- (FRO.m.[x] = Some (y, Known)){2})`
    equiv_seq_last 1 1 : (FMap.eq_except (· = a.1) §FRO_m{1} §FRO_m{2} ∧
      FMap.get §FRO_m{2} a.1 = some (a.2, Known) ∧ FMap.in_dom_with §FRO_m{1} a.1 Unknown)
    case h₁ =>
      stmt_inline{1} 0
      stmt_wp
      stmt_wp{1} 1
      stmt_wp
      equiv_skip
      rintro m _ ⟨rfl, hU⟩
      refine ⟨by simp [SubProbability.expected, dout_ll], fun c _ =>
        ⟨FMap.eq_except_set (fun x => x = a.1) (FMap.eq_except_refl _ _) a.1 _ _
          (fun h => absurd rfl h), FMap.get_set_sameE _ _ _,
          by rw [FMap.in_dom_with_set, if_pos rfl]⟩⟩
    case h₂ =>
      -- EC: `exists* x{1}, y{1}, (FRO.m.[x]{1}); elim*=> x1 y1 mx1. call (iter_inv RRO.I …
      -- (I_f_eqex x1 mx1 mx2))`
      refine prhlStmt_fix_left (fun σ₁ => FMap.get (FRO_m.get σ₁.globals) a.1) fun v => ?_
      equiv_call (IterProc.iter_inv (RRO.I in_t out_t dout FRO_m) (fun z => a.1 ≠ z)
        (fun g₁ g₂ => FMap.eq_except (· = a.1) (FRO_m.get g₁) (FRO_m.get g₂) ∧
          FMap.get (FRO_m.get g₁) a.1 = v ∧ FMap.get (FRO_m.get g₂) a.1 = some (a.2, Known))
        (I_f_eqex in_t out_t dout FRO_m a.1 v (some (a.2, Known))))
      equiv_skip
      rintro σ₁ σ₂ ⟨⟨he, h2, hU⟩, rfl⟩
      refine ⟨⟨?_, fun z hz => ?_, he, rfl, h2⟩, fun _ g₁ _ g₂ ⟨he', _, h2'⟩ =>
        FMap.set_eq_of_eq_except he' h2'⟩
      · congr 1
        ext z
        rw [Finset.mem_sdiff, Finset.mem_singleton, FMap.mem_fdom, FMap.mem_fdom,
          FMap.dom_restr, FMap.dom_restr]
        by_cases hz : z = a.1
        · subst hz
          simp only [not_true_eq_false, and_false, false_iff]
          intro h
          have h3 := h.2
          rw [h2] at h3
          exact absurd h3 (show Known ≠ Unknown by decide)
        · simp only [hz, not_false_eq_true, and_true]
          exact FMap.in_dom_with_congr (he z hz) _
      · rw [Finset.mem_toList, Finset.mem_sdiff, Finset.mem_singleton] at hz
        exact fun h => hz.2 h.symm
  · -- EC: `exists* x{1}, y{1}, (FRO.m.[x]{1}); elim*=> x1 y1 mx1. call (iter_inv RRO.I …)`
    refine prhlStmt_seq_congr_left
      (fun _ _ _ => congrFun (RRO.resample_call_eq in_t out_t dout FRO_m) _) ?_
    stmt_inline{1} 1
    stmt_inline{2} 0
    stmt_wp
    refine prhlStmt_fix_left (fun σ₁ => FMap.get (FRO_m.get σ₁.globals) a.1) fun v => ?_
    equiv_call (IterProc.iter_inv (RRO.I in_t out_t dout FRO_m) (fun z => a.1 ≠ z)
      (fun g₁ g₂ => FMap.eq_except (· = a.1) (FRO_m.get g₁) (FRO_m.get g₂) ∧
        FMap.get (FRO_m.get g₁) a.1 = v ∧ FMap.get (FRO_m.get g₂) a.1 = some (a.2, Known))
      (I_f_eqex in_t out_t dout FRO_m a.1 v (some (a.2, Known))))
    stmt_wp
    equiv_skip
    rintro σ₁ σ₂ ⟨⟨hm, hU⟩, rfl⟩
    rw [← hm]
    refine ⟨⟨?_, fun z hz => ?_,
      FMap.eq_except_setr (fun x => x = a.1) (FMap.eq_except_refl _ _) a.1 rfl _,
      rfl, FMap.get_set_sameE _ _ _⟩, fun _ g₁ _ g₂ ⟨he, _, h2⟩ =>
        FMap.set_eq_of_eq_except he h2⟩
    · rw [FMap.restr_set, if_neg (by decide), FMap.rem_id _ _ (by rwa [FMap.dom_restr])]
    · rw [Finset.mem_toList, FMap.mem_fdom, FMap.dom_restr] at hz
      rintro rfl
      exact hU hz

/-- `eager [RRO.resample();, FRO.rem ~ RRO.rem, RRO.resample(); : ={x} /\ ={FRO.m} ==>
={res, FRO.m}]`, at equality invariants (exception E10). -/
theorem eager_rem (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a : in_t) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.rem in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.rem in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  -- EC: `eager proc; case ((x \in FRO.m /\ FRO.m.[x] \is Unknown){1}).` …
  refine eagerR_of_prhlStmt FRO_m _ _ _ _ (y := localVarLens "r" Unit) (fun _ _ => rfl)
    (RRO.resample_inFootprint in_t out_t dout FRO_m)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) _)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) _)
    (fun _ _ => rfl) ?_
  unfold eagerLeftStmt eagerRightStmt
  refine prhlStmt_seq_congr_right_snd (RRO.resample_call_eq in_t out_t dout FRO_m) ?_
  refine prhlStmt_case (fun σ₁ _ => FMap.in_dom_with (FRO_m.get σ₁.globals) a Unknown) ?_ ?_
  · refine prhlStmt_seq_congr_left
      (fun σ₁ _ h => RRO.resample_call_split in_t out_t dout FRO_m a σ₁ h.2) ?_
    stmt_inline{1} 2
    stmt_inline{2} 0
    stmt_wp
    -- EC: `seq 3 1 : (={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\ … /\
    -- (FRO.m.[x] = None){2})`
    equiv_seq_last 1 1 : (FMap.eq_except (· = a) §FRO_m{1} §FRO_m{2} ∧ FMap.get §FRO_m{2} a = none ∧
      FMap.in_dom_with §FRO_m{1} a Unknown)
    case h₁ =>
      -- EC: `inline *; auto=> |> &2 x_in_m2 x_is_U2; rewrite dout_ll=> //= c _. …`
      stmt_inline{1} 0
      stmt_wp
      stmt_wp{1} 1
      stmt_wp
      equiv_skip
      rintro m _ ⟨rfl, hU⟩
      refine ⟨by simp [SubProbability.expected, dout_ll], fun c _ => ⟨?_, ?_, ?_⟩⟩
      · exact FMap.eq_except_remr (fun x => x = a)
          (FMap.eq_except_setl (fun x => x = a) (FMap.eq_except_refl _ _) a rfl _) a rfl
      · rw [FMap.remE, if_pos rfl]
      · rw [FMap.in_dom_with_set, if_pos rfl]
    case h₂ =>
      -- EC: `exists* x{1}, (FRO.m.[x]{1}); elim*=> x1 mx1. call (iter_inv RRO.I (fun z=> x1<>z)
      -- (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1] = mx1 /\ o2.[x1] = None) _)`
      refine prhlStmt_fix_left (fun σ₁ => FMap.get (FRO_m.get σ₁.globals) a) fun v => ?_
      equiv_call (IterProc.iter_inv (RRO.I in_t out_t dout FRO_m) (fun z => a ≠ z)
        (fun g₁ g₂ => FMap.eq_except (· = a) (FRO_m.get g₁) (FRO_m.get g₂) ∧
          FMap.get (FRO_m.get g₁) a = v ∧ FMap.get (FRO_m.get g₂) a = none)
        (I_f_eqex in_t out_t dout FRO_m a v none))
      equiv_skip
      rintro σ₁ σ₂ ⟨⟨he, h2, hU⟩, rfl⟩
      refine ⟨⟨?_, fun z hz => ?_, he, rfl, h2⟩, fun _ g₁ _ g₂ ⟨he', _, h2'⟩ =>
        FMap.rem_eq_of_eq_except he' h2'⟩
      · congr 1
        ext z
        rw [Finset.mem_sdiff, Finset.mem_singleton, FMap.mem_fdom, FMap.mem_fdom,
          FMap.dom_restr, FMap.dom_restr]
        by_cases hz : z = a
        · subst hz
          simp only [not_true_eq_false, and_false, false_iff]
          intro h; exact absurd ((FMap.domE _ _).mp h.1) (by rw [h2]; exact fun h => h rfl)
        · simp only [hz, not_false_eq_true, and_true]
          exact FMap.in_dom_with_congr (he z hz) _
      · rw [Finset.mem_toList, Finset.mem_sdiff, Finset.mem_singleton] at hz
        exact fun h => hz.2 h.symm
  · -- EC: `inline RRO.resample; wp. exists *x{1}, (FRO.m.[x]{1}); elim*=> x1 mx1.
    -- call (iter_inv RRO.I (fun z=> x1<>z) (… o2.[x1]=None) _). auto …`
    refine prhlStmt_seq_congr_left
      (fun _ _ _ => congrFun (RRO.resample_call_eq in_t out_t dout FRO_m) _) ?_
    stmt_inline{1} 1
    stmt_inline{2} 0
    stmt_wp
    refine prhlStmt_fix_left (fun σ₁ => FMap.get (FRO_m.get σ₁.globals) a) fun v => ?_
    equiv_call (IterProc.iter_inv (RRO.I in_t out_t dout FRO_m) (fun z => a ≠ z)
      (fun g₁ g₂ => FMap.eq_except (· = a) (FRO_m.get g₁) (FRO_m.get g₂) ∧
        FMap.get (FRO_m.get g₁) a = v ∧ FMap.get (FRO_m.get g₂) a = none)
      (I_f_eqex in_t out_t dout FRO_m a v none))
    stmt_wp
    equiv_skip
    rintro σ₁ σ₂ ⟨⟨hm, hU⟩, rfl⟩
    rw [← hm]
    refine ⟨⟨?_, fun z hz => ?_,
      FMap.eq_except_remr (fun x => x = a) (FMap.eq_except_refl _ _) a rfl,
      rfl, by rw [FMap.remE, if_pos rfl]⟩, fun _ g₁ _ g₂ ⟨he, _, h2⟩ =>
        FMap.rem_eq_of_eq_except he h2⟩
    · rw [FMap.restr_rem, if_neg hU]
    · rw [Finset.mem_toList, FMap.mem_fdom, FMap.dom_restr] at hz
      rintro rfl
      exact hU hz

/-- `eager [RRO.resample();, FRO.sample ~ RRO.sample, RRO.resample(); : ={x, FRO.m} ==>
={res, FRO.m}]`, at equality invariants (exception E10). -/
theorem eager_sample (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a : in_t) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.sample in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.sample in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  -- EC: `eager proc.` …
  refine eagerR_of_prhlStmt FRO_m _ _ _ _ (y := localVarLens "r" Unit) (fun _ _ => rfl)
    (RRO.resample_inFootprint in_t out_t dout FRO_m)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) _)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) _)
    (fun _ _ => rfl) ?_
  unfold eagerLeftStmt eagerRightStmt
  refine prhlStmt_seq_congr_left
    (fun _ _ _ => congrFun (RRO.resample_call_eq in_t out_t dout FRO_m) _) ?_
  -- EC: `case: ((x \notin FRO.m){2}).`
  refine prhlStmt_case (fun _ σ₂ => ¬ FMap.dom (FRO_m.get σ₂.globals) a) ?_ ?_
  · -- EC: `rcondt{2} 2; transitivity{2} { c <$ dout x; FRO.m.[x] <- (c, Unknown);
    -- Iter(RRO.I).iter_1s(x, elems ((fdom (restr Unknown FRO.m)) `\` fset1 x)); }`
    refine prhlStmt_seq_congr_right_snd_on (fun σ => ¬ FMap.dom (FRO_m.get σ.globals) a)
      (fun σ => FMap.in_dom_with (FRO_m.get σ.globals) a Unknown) (fun _ _ h => h.2) ?_
      (fun σ h => RRO.resample_call_split in_t out_t dout FRO_m a σ h) ?_
    · stmt_inline 0
      hoare_wp 5
      refine hoare_skip_of_imp fun σ h c _ => ?_
      have hg : ¬ FMap.dom (FRO_m.get σ.globals) a := h
      rw [if_pos (by simpa using hg), FMap.in_dom_with_set, if_pos rfl]
    · -- EC: `inline Iter(RRO.I).iter_1s RRO.I.f RRO.resample; wp; swap{1} -1.`
      stmt_inline{1} 1
      stmt_inline{2} 0
      stmt_inline{2} 0
      stmt_wp
      stmt_swap{1} 1 3
      -- EC: `seq 1 7 : (={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\ … /\
      -- (FRO.m.[x]){2} = Some (c{1}, Unknown) /\ (FRO.m.[x]){1} = None)`
      equiv_seq_last 1 1 : (§x{1} = a ∧ FMap.eq_except (· = a) §FRO_m{1} §FRO_m{2} ∧
        FMap.get §FRO_m{2} a = some (§c{1}, Unknown) ∧ FMap.get §FRO_m{1} a = none)
      case h₁ =>
        -- EC: `wp; rnd; auto=> /> &2; rewrite domE dout_ll=> /= x_notin_m c _ cL _. …`
        stmt_wp
        equiv_rnd
        stmt_wp
        stmt_wp{2} 1
        stmt_wp
        equiv_skip
        rintro σ₂ _ ⟨rfl, hnd⟩
        refine ⟨by simp [SubProbability.expected, dout_ll], fun c₀ _ c _ => ?_⟩
        rw [if_pos (by simpa using hnd)]
        refine ⟨FMap.eq_except_setr (fun x => x = a)
          (FMap.eq_except_setr (fun x => x = a) (FMap.eq_except_refl _ _) a rfl _) a rfl _,
          FMap.get_set_sameE _ _ _, ?_⟩
        simpa [FMap.domE] using hnd
      case h₂ =>
        -- EC: `exists* x{1}, c{1}; elim*=> x1 c1. call (iter_inv RRO.I (fun z=> x1<>z)
        -- (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1]= None /\ o2.[x1]=mx2) _)`
        refine prhlStmt_fix_left (fun σ₁ => (localVarLens "c" out_t).get σ₁) fun c => ?_
        equiv_call (IterProc.iter_inv (RRO.I in_t out_t dout FRO_m) (fun z => a ≠ z)
          (fun g₁ g₂ => FMap.eq_except (· = a) (FRO_m.get g₁) (FRO_m.get g₂) ∧
            FMap.get (FRO_m.get g₁) a = none ∧ FMap.get (FRO_m.get g₂) a = some (c, Unknown))
          (I_f_eqex in_t out_t dout FRO_m a none (some (c, Unknown))))
        equiv_skip
        rintro σ₁ σ₂ ⟨⟨hx, he, h2, h1⟩, hc⟩
        rw [hc] at h2
        refine ⟨⟨?_, fun z hz => ?_, he, h1, h2⟩, fun r₁ g₁ r₂ g₂ ⟨he', h1', h2'⟩ => ?_⟩
        · congr 1
          ext z
          rw [Finset.mem_sdiff, Finset.mem_singleton, FMap.mem_fdom, FMap.mem_fdom,
            FMap.dom_restr, FMap.dom_restr]
          by_cases hz : z = a
          · subst hz
            simp only [not_true_eq_false, and_false, iff_false]
            intro h; exact absurd ((FMap.domE _ _).mp h.1) (by rw [h1]; exact fun h => h rfl)
          · simp only [hz, not_false_eq_true, and_true]
            exact FMap.in_dom_with_congr (he z hz) _
        · rw [Finset.mem_toList, FMap.mem_fdom, FMap.dom_restr] at hz
          rintro rfl
          exact absurd ((FMap.domE _ _).mp hz.1) (by rw [h1]; exact fun h => h rfl)
        · have ex : (localVarLens "x" in_t).get
              (Setter.throwaway.set r₁ (ProgramState.globalL.set g₁ σ₁)) = a := hx
          have ec : (localVarLens "c" out_t).get
              (Setter.throwaway.set r₁ (ProgramState.globalL.set g₁ σ₁)) = c := hc
          simp only [ex, ec]
          have hd : ¬ FMap.dom (FRO_m.get (Setter.throwaway.set r₁
              (ProgramState.globalL.set g₁ σ₁)).globals) a := by
            show ¬ FMap.dom (FRO_m.get g₁) a
            simp [FMap.domE, h1']
          split_ifs with h
          · exact FMap.set_eq_of_eq_except he' h2'
          · exact absurd h (by simpa using hd)
  · -- EC: `rcondf{2} 2; first by auto. swap{1} 2 -1; inline *; auto.
    -- while (={l, FRO.m} /\ (dom FRO.m x){1}); auto.`
    refine prhlStmt_seq_congr_right_snd (RRO.resample_call_eq in_t out_t dout FRO_m) ?_
    stmt_inline{1} 1
    stmt_inline{2} 0
    stmt_wp
    stmt_wp{1} 1
    stmt_wp
    equiv_call (IterProc.iter_inv (RRO.I in_t out_t dout FRO_m) (fun _ => True)
      (fun g₁ g₂ => FRO_m.get g₁ = FRO_m.get g₂ ∧ FMap.dom (FRO_m.get g₁) a) (by
        rw [RRO.I_f_procedure]
        equiv_proc_to_stmt
        stmt_inline{1} 0
        stmt_inline{2} 0
        stmt_wp
        equiv_rnd
        stmt_wp
        equiv_skip
        rintro x m _ _ ⟨rfl, rfl, hd⟩
        exact ⟨rfl, fun c _ => ⟨rfl, (FMap.mem_set _ _ _ _).mpr (Or.inl hd)⟩⟩))
    stmt_wp
    stmt_wp{2} 1
    stmt_wp
    equiv_skip
    intro σ₁ σ₂ ⟨hm, hd⟩
    have hd' := not_not.mp hd
    refine ⟨by simp [SubProbability.expected, dout_ll], fun c _ => ⟨⟨by simp [hd', hm],
      by simp [hd', hm], by rw [hm]; exact hd'⟩, fun r₁ g₁ r₂ g₂ ⟨hg, hgd⟩ =>
        ⟨by simp [SubProbability.expected, dout_ll], fun c' _ => ?_⟩⟩⟩
    show (if (!decide (FMap.dom (FRO_m.get g₁) a)) = true then _ else FRO_m.get g₁) =
      FRO_m.get g₂
    rw [hg] at hgd
    simp [hgd, hg]

/-- `eager [RRO.resample();, FRO.queried ~ RRO.queried, RRO.resample(); : ={x, f} /\
={FRO.m} ==> ={res, FRO.m}]`, at equality invariants (exception E10). -/
theorem eager_queried (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.queried in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.queried in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  -- EC: `eager proc; inline *; wp; while (={l, FRO.m} /\ (forall z, z \in l =>
  -- in_dom_with FRO.m z Unknown){1} /\ in_dom_with FRO.m{1} x{1} f{1} = result{2})`
  refine eagerR_of_prhlStmt FRO_m _ _ _ a (y := localVarLens "r" Bool) (fun _ _ => rfl)
    (RRO.resample_inFootprint in_t out_t dout FRO_m)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) a)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) a)
    (fun _ _ => rfl) ?_
  unfold eagerLeftStmt eagerRightStmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_while (={l, FRO_m} ∧ (∀ z ∈ §l{1}, FMap.in_dom_with §FRO_m{1} z Unknown) ∧
    decide (FMap.dom §FRO_m{1} a.1 ∧ is_ (FMap.get §FRO_m{1} a.1) a.2) = §r{2})
  case body =>
    stmt_wp
    equiv_rnd
    stmt_wp
    equiv_skip
    rintro l m _ _ r ⟨⟨⟨rfl, rfl⟩, hinv, rfl⟩, hne⟩
    cases l with
    | nil => simp at hne
    | cons h t =>
      refine ⟨rfl, fun c _ => ⟨⟨rfl, rfl⟩, fun z hz => ?_, ?_⟩⟩
      · show FMap.in_dom_with (FMap.set m h (c, Unknown)) z Unknown
        rw [FMap.in_dom_with_set]
        split_ifs
        · rfl
        · exact hinv z (List.mem_cons_of_mem _ hz)
      · show decide (FMap.dom (FMap.set m h (c, Unknown)) a.1 ∧
            is_ (FMap.get (FMap.set m h (c, Unknown)) a.1) a.2) =
          decide (FMap.dom m a.1 ∧ is_ (FMap.get m a.1) a.2)
        rw [decide_eq_decide]
        by_cases hx : a.1 = h
        · have hh := hinv h List.mem_cons_self
          rw [← hx] at hh ⊢
          simp only [is_, oget, FMap.mem_set, FMap.get_set_sameE, Option.getD_some, hh.1, hh.2,
            or_true, true_and]
        · simp only [is_, FMap.mem_set, FMap.get_set_neqE _ _ _ _ hx, hx, or_false]
  case guard => rintro _ _ _ _ _ ⟨⟨rfl, -⟩, -⟩; rfl
  case exit => exact fun _ _ _ _ ⟨⟨_, h⟩, _, hr⟩ _ => ⟨hr, h⟩
  case hpre =>
    stmt_wp
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨by rw [h], h⟩, fun z hz => ?_, decide_eq_decide.mpr (by rw [h])⟩
    rw [Finset.mem_toList, FMap.mem_fdom, FMap.dom_restr] at hz
    exact hz

/-- `eager [RRO.resample();, FRO.allKnown ~ RRO.allKnown, RRO.resample(); : ={FRO.m} ==>
={res, FRO.m}]`, at equality invariants (exception E10). -/
theorem eager_allKnown (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.allKnown in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.allKnown in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  -- EC: `eager proc; inline *; wp; while (={l, FRO.m} /\ (forall z, mem l z =>
  -- in_dom_with FRO.m z Unknown){1} /\ restr Known FRO.m{1} = result{2})`
  refine eagerR_of_prhlStmt FRO_m _ _ _ a (y := localVarLens "r" (FMap in_t out_t)) (fun _ _ => rfl)
    (RRO.resample_inFootprint in_t out_t dout FRO_m)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) a)
    (procedureDenotation_inFootprint_of_within _ (by within_lens) (by within_lens) a)
    (fun _ _ => rfl) ?_
  unfold eagerLeftStmt eagerRightStmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_while (={l, FRO_m} ∧ (∀ z ∈ §l{1}, FMap.in_dom_with §FRO_m{1} z Unknown) ∧
    FMap.restr Known §FRO_m{1} = §r{2})
  case body =>
    stmt_wp
    equiv_rnd
    stmt_wp
    equiv_skip
    rintro l m _ _ r ⟨⟨⟨rfl, rfl⟩, hinv, rfl⟩, hne⟩
    cases l with
    | nil => simp at hne
    | cons h t =>
      refine ⟨rfl, fun a _ => ⟨⟨rfl, rfl⟩, fun z hz => ?_, ?_⟩⟩
      · show FMap.in_dom_with (FMap.set m h (a, Unknown)) z Unknown
        rw [FMap.in_dom_with_set]
        split_ifs
        · rfl
        · exact hinv z (List.mem_cons_of_mem _ hz)
      · show FMap.restr Known (FMap.set m h (a, Unknown)) = FMap.restr Known m
        rw [FMap.restr_set, if_neg (by decide)]
        refine FMap.rem_id _ _ fun hd => ?_
        have h1 := (FMap.dom_restr m Known h).mp hd
        have h2 := hinv h List.mem_cons_self
        exact absurd (h1.2.symm.trans h2.2) (by decide)
  case guard => rintro _ _ _ _ _ ⟨⟨rfl, -⟩, -⟩; rfl
  case exit => rintro _ _ _ _ _ ⟨⟨-, rfl⟩, -, h⟩ -; exact ⟨h, rfl⟩
  case hpre =>
    stmt_wp
    equiv_skip
    rintro m _ rfl
    refine ⟨⟨rfl, rfl⟩, fun z hz => ?_, rfl⟩
    rw [Finset.mem_toList, FMap.mem_fdom, FMap.dom_restr] at hz
    exact hz

omit [Inhabited d_in_t] [Inhabited d_out_t] in
/-- `lemma eager_D (D <: FRO_Distinguisher {-FRO}) : eager [RRO.resample();, D(FRO).distinguish ~
D(RRO).distinguish, RRO.resample(); : ={glob D, FRO.m, arg} ==> ={FRO.m, glob D} /\ ={res}]`, at
equality invariants (exception E10).  EC: `eager proc (={FRO.m}) => //; try by sim;` then the seven
`eager_*` lemmas — here `eager_call_module`, whose `SwapLoc` side is footprint disjointness. -/
theorem eager_D [Countable in_t] [Countable out_t] (dout_ll : ∀ x, (dout x).1 Set.univ = 1)
    (D : FRO_Distinguisher in_t out_t d_in_t d_out_t)
    (hD : Module.ECModule D (FRO_ext in_t out_t))
    (hdisj : FVP.fvP D ≤ (FRO_m.footprint)ᶜ) (a : d_in_t) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (Module.app D (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (Module.app D (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) :=
  eager_call_module FRO_m D (FRO_ext in_t out_t) hD.representable hdisj
    (fun n => by
      cases n with
      | zero => exact inferInstanceAs (Countable Unit)
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable in_t)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable (in_t × out_t))
          | succ n => cases n with
            | zero => exact inferInstanceAs (Countable in_t)
            | succ n => cases n with
              | zero => exact inferInstanceAs (Countable in_t)
              | succ n => cases n with
                | zero => exact inferInstanceAs (Countable (in_t × flag))
                | succ n => cases n with
                  | zero => exact inferInstanceAs (Countable Unit)
                  | succ n => nomatch n)
    _ (RRO.resample_inFootprint in_t out_t dout FRO_m) _ _
    (fun n a => by
      cases n with
      | zero => exact eager_init in_t out_t dout FRO_m dout_ll a
      | succ n => cases n with
        | zero => exact eager_get in_t out_t dout FRO_m dout_ll a
        | succ n => cases n with
          | zero => exact eager_set in_t out_t dout FRO_m dout_ll a
          | succ n => cases n with
            | zero => exact eager_rem in_t out_t dout FRO_m dout_ll a
            | succ n => cases n with
              | zero => exact eager_sample in_t out_t dout FRO_m dout_ll a
              | succ n => cases n with
                | zero => exact eager_queried in_t out_t dout FRO_m dout_ll a
                | succ n => cases n with
                  | zero => exact eager_allKnown in_t out_t dout FRO_m dout_ll a
                  | succ n => nomatch n)
    a

omit [Inhabited d_in_t] [Inhabited d_out_t] in
/-- EC's `eager_D` at an `RO_Distinguisher` (EasyCrypt's subtyping `RO_Distinguisher <:
FRO_Distinguisher`): `eager_call_module` over `RO`'s procedures, by the same oracle lemmas. -/
theorem eager_D_RO [Countable in_t] [Countable out_t] (dout_ll : ∀ x, (dout x).1 Set.univ = 1)
    (D : RO_Distinguisher in_t out_t d_in_t d_out_t)
    (hD : Module.ECModule D (RO_ext in_t out_t))
    (hdisj : FVP.fvP D ≤ (FRO_m.footprint)ᶜ) (a : d_in_t) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (Module.app D (FRO.asRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (Module.app D (RRO.asRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) :=
  eager_call_module FRO_m D (RO_ext in_t out_t) hD.representable hdisj
    (fun n => by
      cases n with
      | zero => exact inferInstanceAs (Countable Unit)
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable in_t)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable (in_t × out_t))
          | succ n => cases n with
            | zero => exact inferInstanceAs (Countable in_t)
            | succ n => cases n with
              | zero => exact inferInstanceAs (Countable in_t)
              | succ n => nomatch n)
    _ (RRO.resample_inFootprint in_t out_t dout FRO_m) _ _
    (fun n a => by
      simp only [RO_ext, FRO.asRO, RRO.asRO, RO_T.init.mk_simp, RO_T.get.mk_simp,
        RO_T.set.mk_simp, RO_T.rem.mk_simp, RO_T.sample.mk_simp]
      cases n with
      | zero => exact eager_init in_t out_t dout FRO_m dout_ll a
      | succ n => cases n with
        | zero => exact eager_get in_t out_t dout FRO_m dout_ll a
        | succ n => cases n with
          | zero => exact eager_set in_t out_t dout FRO_m dout_ll a
          | succ n => cases n with
            | zero => exact eager_rem in_t out_t dout FRO_m dout_ll a
            | succ n => cases n with
              | zero => exact eager_sample in_t out_t dout FRO_m dout_ll a
              | succ n => nomatch n)
    a


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

/-- `Eager(D).main1`'s run: `FRO.init()`, then `D(FRO)`. -/
theorem Eager.main1_denotation (D : FRO_Distinguisher in_t out_t d_in_t d_out_t) (a : d_in_t) :
    procedureDenotation (Eager.main1 in_t out_t d_in_t d_out_t dout FRO_m D).procedure a =
      (procedureDenotation (FRO_T.init in_t out_t (FRO in_t out_t dout FRO_m)).procedure () >>=
        fun _ => procedureDenotation (Module.app D (FRO in_t out_t dout FRO_m)).procedure a) := by
  rw [Eager.main1, Module.procedure_proc']
  funext g
  refine SubProbability.ext_of_expected fun F => ?_
  conv_lhs => rw [procedureDenotation]
  simp only [Eager.main1.procedure, SubProbability.expected_hbind,
    programDenotation_seq, ProgramDenotation.bind_apply, SubProbability.expected_bind,
    programDenotation_hcall_apply, programDenotation_assign_apply, expected_pure]
  simp_reads
  refine congrArg _ (funext fun r => ?_)
  have hx : ∀ (r₁ : Unit) r₂, (localVarLens "x" d_in_t).get (Setter.throwaway.set r₁
      (ProgramState.globalL.set r₂ ⟨g, (Eager.main1.procedure in_t out_t d_in_t d_out_t dout FRO_m
        D).initLocals a⟩)) = a := by
    intro r₁ r₂
    simp only [ProcedureWithHoles.initLocals, VariableAssignment.setParams, localVarLens,
      Eager.main1.procedure]
    exact (varLens (VariableName.mk "x" d_in_t)).set_get _ _
  erw [hx]
  rfl

/-- `Eager(D).main2`'s run: `FRO.init()`, `D(RRO)`, then `RRO.resample()`. -/
theorem Eager.main2_denotation (D : FRO_Distinguisher in_t out_t d_in_t d_out_t) (a : d_in_t) :
    procedureDenotation (Eager.main2 in_t out_t d_in_t d_out_t dout FRO_m D).procedure a =
      (procedureDenotation (FRO_T.init in_t out_t (FRO in_t out_t dout FRO_m)).procedure () >>=
        fun _ => procedureDenotation (Module.app D (RRO in_t out_t dout FRO_m)).procedure a >>=
          fun b => RRO.resampleDen in_t out_t dout FRO_m >>= fun _ => pure b) := by
  rw [Eager.main2, Module.procedure_proc']
  funext g
  refine SubProbability.ext_of_expected fun F => ?_
  conv_lhs => rw [procedureDenotation]
  simp only [Eager.main2.procedure, SubProbability.expected_hbind,
    programDenotation_seq, ProgramDenotation.bind_apply, SubProbability.expected_bind,
    programDenotation_hcall_apply, expected_pure, ProgramDenotation.pure_apply]
  simp_reads
  have hx : ∀ (r₁ : Unit) r₂, (localVarLens "x" d_in_t).get (Setter.throwaway.set r₁
      (ProgramState.globalL.set r₂ ⟨g, (Eager.main2.procedure in_t out_t d_in_t d_out_t dout FRO_m
        D).initLocals a⟩)) = a := by
    intro r₁ r₂
    simp only [ProcedureWithHoles.initLocals, VariableAssignment.setParams, localVarLens,
      Eager.main2.procedure]
    exact (varLens (VariableName.mk "x" d_in_t)).set_get _ _
  have hb : ∀ (r₃ : Unit) g₃ v τ, (localVarLens "b" d_out_t).get (Setter.throwaway.set r₃
      (ProgramState.globalL.set g₃ ((localVarLens "b" d_out_t).set v τ))) = v :=
    fun _ _ v τ => (localVarLens "b" d_out_t).set_get τ v
  refine congrArg _ (funext fun r => ?_)
  erw [hx]
  simp only [hb]
  rfl



/-- `FRO.init()`'s run: `FRO.m <- empty`. -/
theorem FRO_init_denotation (g : VariableAssignment) :
    procedureDenotation (FRO_T.init in_t out_t (FRO in_t out_t dout FRO_m)).procedure () g =
      pure ((), FRO_m.set FMap.empty g) := by
  rw [FRO, FRO_T.init.mk_simp, FRO.init, Module.procedure_proc']
  refine SubProbability.ext_of_expected fun F => ?_
  simp only [procedureDenotation, FRO.init.procedure, SubProbability.expected_hbind,
    programDenotation_assign_apply, expected_pure]
  simp_reads
  trivial

/-- EC's `inline *; rcondf{2} 3 … restr0 fdom0 elems_fset0`: `RRO.resample()` right after
`FRO.init()` does nothing. -/
theorem FRO_init_resample :
    (procedureDenotation (FRO_T.init in_t out_t (FRO in_t out_t dout FRO_m)).procedure () >>=
        fun _ => RRO.resampleDen in_t out_t dout FRO_m) =
      procedureDenotation (FRO_T.init in_t out_t (FRO in_t out_t dout FRO_m)).procedure () := by
  funext g
  rw [ProgramDenotation.bind_apply, FRO_init_denotation, SubProbability.pure_bind,
    RRO.resampleDen, RRO.resample_denotation, IterProc.Iter.iter_denotation, FRO_m.set_get,
    FMap.restr0, FMap.fdom0, Finset.toList_empty]
  rfl



/-- EC's `transitivity{1} { FRO.init(); RRO.resample(); b <@ D(FRO).distinguish(x); } …`
and `eager call (eager_D D)`: `main2` runs as `main1`. -/
theorem Eager.main2_eq_main1 [Countable in_t] [Countable out_t]
    (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (D : FRO_Distinguisher in_t out_t d_in_t d_out_t)
    (hD : Module.ECModule D (FRO_ext in_t out_t)) (hdisj : FVP.fvP D ≤ (FRO_m.footprint)ᶜ)
    (a : d_in_t) :
    procedureDenotation (Eager.main2 in_t out_t d_in_t d_out_t dout FRO_m D).procedure a =
      procedureDenotation (Eager.main1 in_t out_t d_in_t d_out_t dout FRO_m D).procedure a := by
  rw [Eager.main2_denotation, Eager.main1_denotation]
  have h := ProgramDenotation.eagerR_to_eq
    (eager_D in_t out_t d_in_t d_out_t dout FRO_m dout_ll D hD hdisj a)
  rw [← h, ← ProgramDenotation.bind_assoc, FRO_init_resample]

/-- EC's `sim` on an oracle procedure of `FRO` in an abstract call against `FRO` itself: the
syntactic frame for `glob D` and the self-coupling of code within `FRO.m`. -/
local macro "oracle_sim" : tactic => `(tactic| (
  refine prhlProc_globInvF_of_writesKeep _ ?_ ?_ (prhlProc_refl_of_within _ _ ?_ ?_) <;>
  (dsimp only [FRO_ext, HoleSigs.Instantiation.lookup_succ,
    HoleSigs.Instantiation.lookup_zero_cons, HoleSigs.Instantiation.lookup_zero_single]
   first | (writes_keep; done) | within_lens)))

/-- `main1` against itself, from `={glob D, arg}` (EC's `seq 1 1 : (={glob D, FRO.m, x})` and the
abstract call of `D` with `FRO` on both sides, whose oracles are `sim`). -/
theorem Eager.main1_self [Countable in_t] [Countable out_t]
    (D : FRO_Distinguisher in_t out_t d_in_t d_out_t)
    (hD : Module.ECModule D (FRO_ext in_t out_t)) (hdisj : FVP.fvP D ≤ (FRO_m.footprint)ᶜ) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧
        (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂)
      (Eager.main1 in_t out_t d_in_t d_out_t dout FRO_m D).procedure
      (Eager.main1 in_t out_t d_in_t d_out_t dout FRO_m D).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        FRO_m.get g₁ = FRO_m.get g₂ ∧
        (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂) := by
  have hm : FRO_m.footprint ≤ (FVP.fvP D)ᶜ := (Footprint.le_compl_comm _ _).mp hdisj
  have hcall := prhlProc_abstract_call_module FRO_m D (FRO_ext in_t out_t) hD.representable
    hdisj (fun x y => x = y)
    (fun n => by
      cases n with
      | zero => exact inferInstanceAs (Countable Unit)
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable in_t)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable (in_t × out_t))
          | succ n => cases n with
            | zero => exact inferInstanceAs (Countable in_t)
            | succ n => cases n with
              | zero => exact inferInstanceAs (Countable in_t)
              | succ n => cases n with
                | zero => exact inferInstanceAs (Countable (in_t × flag))
                | succ n => cases n with
                  | zero => exact inferInstanceAs (Countable Unit)
                  | succ n => nomatch n)
    (FRO in_t out_t dout FRO_m) (FRO in_t out_t dout FRO_m)
    (fun n => by
      cases n with
      | zero => oracle_sim
      | succ n => cases n with
        | zero => oracle_sim
        | succ n => cases n with
          | zero => oracle_sim
          | succ n => cases n with
            | zero => oracle_sim
            | succ n => cases n with
              | zero => oracle_sim
              | succ n => cases n with
                | zero => oracle_sim
                | succ n => cases n with
                  | zero => oracle_sim
                  | succ n => nomatch n)
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_call hcall
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x₁ x₂ ⟨rfl, hg⟩
  refine ⟨⟨rfl, ?_, by rw [FRO_m.set_get, FRO_m.set_get]⟩,
    fun r₁ g₁ r₂ g₂ ⟨hr, hglob, hI⟩ => ⟨hr, hI, hglob⟩⟩
  rw [touched_set_of_le_compl hm, touched_set_of_le_compl hm]
  exact hg

/-- EC's `FullEager.EagerCore.Eager_1_2`, for `declare module D <: FRO_Distinguisher {-FRO}`
(the oracles' arguments countable: exception E8):
`equiv[ Eager(D).main1 ~ Eager(D).main2 : ={glob D, arg} ==> ={res, glob FRO, glob D} ]`. -/
theorem Eager_1_2 [Countable in_t] [Countable out_t] (dout_ll : ∀ x, (dout x).1 Set.univ = 1)
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
  intro a₁ a₂
  rw [Eager.main2_eq_main1 in_t out_t d_in_t d_out_t dout FRO_m dout_ll D hD hdisj a₂]
  exact Eager.main1_self in_t out_t d_in_t d_out_t dout FRO_m D hD hdisj a₁ a₂

section LRO_RRO
/-! EC's `LRO_RRO_init` … `LRO_RRO_D`: `LRO` and `RRO` agree on the known entries. -/
variable (RO_m : Lens (FMap in_t out_t) VariableAssignment)

/-- `equiv LRO_RRO_init : LRO.init ~ RRO.init : true ==> RO.m{1} = restr Known FRO.m{2}`. -/
theorem LRO_RRO_init : prhlProc (fun _ _ _ _ => True)
    (RO_T.init in_t out_t (LRO in_t out_t dout RO_m)).procedure
    (FRO_T.init in_t out_t (RRO in_t out_t dout FRO_m)).procedure
    (fun _ g₁ _ g₂ => RO_m.get g₁ = FMap.restr Known (FRO_m.get g₂)) := by
  simp only [LRO, RRO, RO_T.init.mk_simp, FRO_T.init.mk_simp]
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_skip
  intro _
  exact (FMap.restr0 _).symm

/-- `equiv LRO_RRO_get : LRO.get ~ RRO.get : ={x} /\ RO.m{1} = restr Known FRO.m{2} ==>
={res} /\ RO.m{1} = restr Known FRO.m{2}`. -/
theorem LRO_RRO_get :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ RO_m.get g₁ = FMap.restr Known (FRO_m.get g₂))
    (RO_T.get in_t out_t (LRO in_t out_t dout RO_m)).procedure
    (FRO_T.get in_t out_t (RRO in_t out_t dout FRO_m)).procedure
    (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ RO_m.get g₁ = FMap.restr Known (FRO_m.get g₂)) := by
  simp only [LRO, RRO, RO_T.get.mk_simp, FRO_T.get.mk_simp]
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  rintro x _ _ m ⟨rfl, rfl⟩
  refine ⟨rfl, fun a _ => ?_⟩
  have hd := FMap.dom_restr m Known x
  rcases hm : FMap.get m x with _ | ⟨y, _ | _⟩
  · have h1 : ¬ FMap.dom m x := by simp [FMap.domE, hm]
    have h2 : ¬ FMap.dom (FMap.restr Known m) x := by rw [hd, FMap.in_dom_with]; simp [h1]
    simp [h1, h2, FMap.restr_set_eq, oget]
  · have h1 : FMap.dom m x := by simp [FMap.domE, hm]
    have h2 : ¬ FMap.dom (FMap.restr Known m) x := by
      rw [hd, FMap.in_dom_with]; simp [hm]
    simp [h1, h2, is_, oget, FMap.restr_set_eq]
  · have h1 : FMap.dom m x := by simp [FMap.domE, hm]
    have h2 : FMap.dom (FMap.restr Known m) x := by rw [hd, FMap.in_dom_with]; simp [h1, hm]
    simp [h1, h2, hm, is_, oget, FMap.restrP]

/-- `equiv LRO_RRO_set : LRO.set ~ RRO.set : ={x, y} /\ RO.m{1} = restr Known FRO.m{2} ==>
RO.m{1} = restr Known FRO.m{2}`. -/
theorem LRO_RRO_set :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ RO_m.get g₁ = FMap.restr Known (FRO_m.get g₂))
    (RO_T.set in_t out_t (LRO in_t out_t dout RO_m)).procedure
    (FRO_T.set in_t out_t (RRO in_t out_t dout FRO_m)).procedure
    (fun _ g₁ _ g₂ => RO_m.get g₁ = FMap.restr Known (FRO_m.get g₂)) := by
  simp only [LRO, RRO, RO_T.set.mk_simp, FRO_T.set.mk_simp]
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_skip
  rintro x y _ _ _ m ⟨h, rfl⟩
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  exact (FMap.restr_set_eq m Known x y).symm

/-- `equiv LRO_RRO_rem : LRO.rem ~ RRO.rem : ={x} /\ RO.m{1} = restr Known FRO.m{2} ==>
RO.m{1} = restr Known FRO.m{2}`. -/
theorem LRO_RRO_rem :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ RO_m.get g₁ = FMap.restr Known (FRO_m.get g₂))
    (RO_T.rem in_t out_t (LRO in_t out_t dout RO_m)).procedure
    (FRO_T.rem in_t out_t (RRO in_t out_t dout FRO_m)).procedure
    (fun _ g₁ _ g₂ => RO_m.get g₁ = FMap.restr Known (FRO_m.get g₂)) := by
  simp only [LRO, RRO, RO_T.rem.mk_simp, FRO_T.rem.mk_simp]
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_skip
  rintro x _ _ m ⟨rfl, rfl⟩
  rw [FMap.restr_rem]
  split_ifs with h
  · rfl
  · exact FMap.rem_id _ _ (by rwa [FMap.dom_restr])

/-- `equiv LRO_RRO_sample : LRO.sample ~ RRO.sample : ={x} /\ RO.m{1} = restr Known FRO.m{2} ==>
RO.m{1} = restr Known FRO.m{2}` (with the section's `dout_ll`). -/
theorem LRO_RRO_sample (dout_ll : ∀ x, (dout x).1 Set.univ = 1) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ RO_m.get g₁ = FMap.restr Known (FRO_m.get g₂))
    (RO_T.sample in_t out_t (LRO in_t out_t dout RO_m)).procedure
    (FRO_T.sample in_t out_t (RRO in_t out_t dout FRO_m)).procedure
    (fun _ g₁ _ g₂ => RO_m.get g₁ = FMap.restr Known (FRO_m.get g₂)) := by
  simp only [LRO, RRO, RO_T.sample.mk_simp, FRO_T.sample.mk_simp]
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  stmt_wp{2} 1
  stmt_wp
  equiv_skip
  rintro x _ _ m ⟨rfl, rfl⟩
  refine ⟨by simp [SubProbability.expected, dout_ll], fun a _ => ?_⟩
  by_cases h : FMap.dom m x
  · simp [h]
  · have h2 : ¬ FMap.dom (FMap.restr Known m) x := by
      rw [FMap.dom_restr, FMap.in_dom_with]; simp [h]
    simp [h, FMap.restr_set, FMap.rem_id _ _ h2]

omit [Inhabited d_in_t] [Inhabited d_out_t] in
/-- `equiv LRO_RRO_D (D <: RO_Distinguisher{-RO, -FRO}) : D(LRO).distinguish ~
D(RRO).distinguish : ={glob D, arg} /\ RO.m{1} = restr Known FRO.m{2} ==>
={res, glob D} /\ RO.m{1} = restr Known FRO.m{2}`.  `RO.m` and `FRO.m` are distinct variables, and
the oracles' arguments countable (exception E8). -/
theorem LRO_RRO_D (dout_ll : ∀ x, (dout x).1 Set.univ = 1) [Countable in_t] [Countable out_t]
    [Lens.Disjoint RO_m FRO_m] (D : RO_Distinguisher in_t out_t d_in_t d_out_t)
    (hD : Module.ECModule D (RO_ext in_t out_t))
    (hdisj : FVP.fvP D ≤ (RO_m.footprint ⊔ FRO_m.footprint)ᶜ) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧
        (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂ ∧
        RO_m.get g₁ = FMap.restr Known (FRO_m.get g₂))
      (Module.app D (LRO in_t out_t dout RO_m)).procedure
      (Module.app D (RRO.asRO in_t out_t dout FRO_m)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧
        (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂ ∧
        RO_m.get g₁ = FMap.restr Known (FRO_m.get g₂)) := by
  have hRO : RO_m.footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (hdisj.trans (Footprint.compl_antimono le_sup_left))
  have hFRO : FRO_m.footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (hdisj.trans (Footprint.compl_antimono le_sup_right))
  have hL : FVP.fvP D ≤ ((Lens.pair RO_m FRO_m).footprint)ᶜ := by
    rw [Footprint.lens_pair]; exact hdisj
  exact prhlProc_abstract_call_module (Lens.pair RO_m FRO_m) D (RO_ext in_t out_t)
    hD.representable hL (fun a b => a.1 = FMap.restr Known b.2)
    (fun n => by
      cases n with
      | zero => exact inferInstanceAs (Countable Unit)
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable in_t)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable (in_t × out_t))
          | succ n => cases n with
            | zero => exact inferInstanceAs (Countable in_t)
            | succ n => cases n with
              | zero => exact inferInstanceAs (Countable in_t)
              | succ n => nomatch n)
    (LRO in_t out_t dout RO_m) (RRO.asRO in_t out_t dout FRO_m) (fun n => by
      -- EC: `proc (RO.m{1} = restr Known FRO.m{2}) => //; conseq LRO_RRO_init …`
      refine prhlProc_conseq (prhlProc_globInvF_of_writesKeep _ ?_ ?_ ?_) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => ⟨h.1, h.2⟩)
      all_goals cases n with
      | zero =>
        simp only [RO_ext, RRO.asRO, RO_T.init.mk_simp,
          HoleSigs.Instantiation.lookup_zero_cons]
        first
          | writes_keep; done
          | exact prhlProc_conseq (LRO_RRO_init in_t out_t dout FRO_m RO_m)
              (fun _ _ _ _ _ => trivial) fun _ _ _ _ h => ⟨trivial, h⟩
      | succ n => cases n with
      | zero =>
        simp only [RO_ext, RRO.asRO, RO_T.get.mk_simp,
          HoleSigs.Instantiation.lookup_succ, HoleSigs.Instantiation.lookup_zero_cons]
        first
          | writes_keep; done
          | exact LRO_RRO_get in_t out_t dout FRO_m RO_m
      | succ n => cases n with
      | zero =>
        simp only [RO_ext, RRO.asRO, RO_T.set.mk_simp,
          HoleSigs.Instantiation.lookup_succ, HoleSigs.Instantiation.lookup_zero_cons]
        first
          | writes_keep; done
          | exact prhlProc_conseq (LRO_RRO_set in_t out_t dout FRO_m RO_m)
              (fun _ _ _ _ h => h) fun _ _ _ _ h => ⟨trivial, h⟩
      | succ n => cases n with
      | zero =>
        simp only [RO_ext, RRO.asRO, RO_T.rem.mk_simp,
          HoleSigs.Instantiation.lookup_succ, HoleSigs.Instantiation.lookup_zero_cons]
        first
          | writes_keep; done
          | exact prhlProc_conseq (LRO_RRO_rem in_t out_t dout FRO_m RO_m)
              (fun _ _ _ _ h => h) fun _ _ _ _ h => ⟨trivial, h⟩
      | succ n => cases n with
      | zero =>
        simp only [RO_ext, RRO.asRO, RO_T.sample.mk_simp,
          HoleSigs.Instantiation.lookup_succ, HoleSigs.Instantiation.lookup_zero_single]
        first
          | writes_keep; done
          | exact prhlProc_conseq (LRO_RRO_sample in_t out_t dout FRO_m RO_m dout_ll)
              (fun _ _ _ _ h => h) fun _ _ _ _ h => ⟨trivial, h⟩
      | succ n => nomatch n)

end LRO_RRO

end EagerCore

section RO_LRO_D

variable (in_t out_t d_in_t d_out_t : Type) [DecidableEq in_t] [Inhabited in_t] [Inhabited out_t]
  [Inhabited d_in_t] [Inhabited d_out_t] (dout : in_t → SubProbability out_t)
  (FRO_m : Lens (FMap in_t (out_t × flag)) VariableAssignment)

/-- EC's `FullEager.RO_LRO_D`, for `declare module D <: RO_Distinguisher {-RO, -FRO}` and
`axiom dout_ll x : is_lossless (dout x)`:
`equiv[ D(RO).distinguish ~ D(LRO).distinguish : ={glob D, RO.m, arg} ==> ={res, glob D} ]`.
`RO.m` and `FRO.m` are distinct variables, and the oracles' arguments countable (exception E8).
EC's proof: two `transitivity`s through `M.main1 = RRO.resample(); D(FRO)` and
`M.main2 = D(RRO); RRO.resample()`, by `RO_FRO_D`, `eager_D` and `LRO_RRO_D`. -/
theorem RO_LRO_D [Countable in_t] [Countable out_t] (dout_ll : ∀ x, (dout x).1 Set.univ = 1)
    (RO_m : Lens (FMap in_t out_t) VariableAssignment) [Lens.Disjoint RO_m FRO_m]
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
  have hFRO_D : FVP.fvP D ≤ (FRO_m.footprint)ᶜ :=
    hdisj.trans (Footprint.compl_antimono le_sup_right)
  have hm : FRO_m.footprint ≤ (FVP.fvP D)ᶜ := (Footprint.le_compl_comm _ _).mp hFRO_D
  set R := RRO.resampleDen in_t out_t dout FRO_m with hRdef
  set G := (FVP.fvP D).touched_getter.get with hG
  let tag : FMap in_t out_t → FMap in_t (out_t × flag) := FMap.map fun _ c => (c, Known)
  -- `resample` from a state with no `Unknown` entry does nothing (EC's `rcondf{2} 3`)
  have hR_pure : ∀ g, FMap.restr Unknown (FRO_m.get g) = FMap.empty → R g = pure ((), g) := by
    intro g h
    rw [hRdef, RRO.resampleDen, RRO.resample_denotation, IterProc.Iter.iter_denotation, h,
      FMap.fdom0, Finset.toList_empty]
    rfl
  have hR_ll : ∀ g, (R g).1 Set.univ = 1 := by
    intro g
    have := RRO_resample_ll in_t out_t dout FRO_m dout_ll () g
    unfold Procedure.ewp ProgramDenotation.wp SubProbability.expected at this
    rw [MeasureTheory.lintegral_one] at this
    exact this
  intro a₁ a₂
  -- EC: `transitivity M.main1 (={glob D, arg} /\ FRO.m{2} = map (fun _ c => (c, Known)) RO.m{1}
  -- ==> ={res, glob D}) …`; `M.main1 = RRO.resample(); D(FRO)`
  have h1 : ProgramDenotation.prhl2
      (fun g₁ gm => a₁ = a₂ ∧ G g₁ = G gm ∧ FRO_m.get gm = tag (RO_m.get g₁))
      (procedureDenotation (Module.app D (RO.asRO in_t out_t dout RO_m)).procedure a₁)
      (R >>= fun _ =>
        procedureDenotation (Module.app D (FRO.asRO in_t out_t dout FRO_m)).procedure a₂)
      (fun u v => u.1 = v.1 ∧ G u.2 = G v.2) := by
    rintro g₁ gm ⟨rfl, hg, hF⟩
    have e : (R >>= fun _ => procedureDenotation
        (Module.app D (FRO.asRO in_t out_t dout FRO_m)).procedure a₁) gm =
        procedureDenotation (Module.app D (FRO.asRO in_t out_t dout FRO_m)).procedure a₁ gm := by
      have hU : FMap.restr Unknown (FRO_m.get gm) = FMap.empty := by
        rw [hF]; exact FMap.restr_map_tag_ne _ (by decide)
      rw [ProgramDenotation.bind_apply, hR_pure gm hU, SubProbability.pure_bind]
    rw [e]
    obtain ⟨μ, hm1, hm2, hsat⟩ := RO_FRO_D _ _ dout RO_m FRO_m _ _ D hD hdisj a₁ a₁ g₁ gm
      ⟨rfl, hg, by rw [hF, FMap.noflags_map_tag]⟩
    exact ⟨μ, hm1, hm2, fun w hw => ⟨(hsat w hw).1, (hsat w hw).2.1⟩⟩
  -- EC: `transitivity M.main2 (={glob D, FRO.m, arg} ==> …)`, `by proc; eager call (eager_D D)`
  have heq := ProgramDenotation.eagerR_to_eq
    (eager_D_RO _ _ _ _ dout FRO_m dout_ll D hD hFRO_D a₂)
  rw [heq] at h1
  -- EC: `proc*; inline M.main2; wp; call{1} RRO_resample_ll. symmetry; call (LRO_RRO_D D); auto`
  have h2 : ProgramDenotation.prhl2
      (fun gm g₂ => G gm = G g₂ ∧ FRO_m.get gm = tag (RO_m.get g₂))
      (procedureDenotation (Module.app D (RRO.asRO in_t out_t dout FRO_m)).procedure a₂ >>=
        fun r => R >>= fun _ => pure r)
      (procedureDenotation (Module.app D (LRO in_t out_t dout RO_m)).procedure a₂)
      (fun u v => u.1 = v.1 ∧ G u.2 = G v.2) := by
    have hl := (LRO_RRO_D _ _ _ _ dout FRO_m RO_m dout_ll D hD hdisj a₂ a₂).symm
    rw [← ProgramDenotation.bind_pure
      (procedureDenotation (Module.app D (LRO in_t out_t dout RO_m)).procedure a₂)]
    refine ProgramDenotation.prhl2.bind (hl.conseq (fun gm g₂ ⟨hg, hF⟩ =>
      ⟨rfl, hg.symm, by rw [hF, FMap.restr_map_tag]⟩) fun _ _ h => h) fun b₁ b₂ => ?_
    refine ProgramDenotation.prhl2_lossless_left b₂ (fun τ => ?_) fun τ₁ τ₂ hM => ?_
    · rw [ProgramDenotation.bind_apply, SubProbability.expected_bind]
      simp only [ProgramDenotation.pure_apply, expected_pure]
      exact RRO_resample_ll in_t out_t dout FRO_m dout_ll () τ
    · obtain ⟨hb, hg, -⟩ := hM
      rw [ProgramDenotation.bind_apply]
      refine SubProbability.satisfies_bind _ fun v hv => ?_
      rw [ProgramDenotation.pure_apply]
      refine SubProbability.satisfies_pure _ _ ⟨hb.symm, ?_⟩
      exact (RRO.resample_keeps in_t out_t dout FRO_m hm τ₁ v hv).trans hg.symm
  have htr := ProgramDenotation.prhl2.trans h1 h2
  rintro g₁ g₂ ⟨rfl, hg, hm'⟩
  obtain ⟨μ, m1, m2, sat⟩ := htr g₁ g₂ ⟨FRO_m.set (tag (RO_m.get g₁)) g₁,
    ⟨rfl, by rw [hG, touched_set_of_le_compl hm], FRO_m.set_get _ _⟩,
    ⟨by rw [hG, touched_set_of_le_compl hm]; exact hg, by rw [FRO_m.set_get, hm']⟩⟩
  refine ⟨μ, m1, m2, fun w hw => ?_⟩
  obtain ⟨y, ⟨e1, g1⟩, ⟨e2, g2⟩⟩ := sat w hw
  exact ⟨e1.trans e2, g1.trans g2⟩

end RO_LRO_D

end FullEager

end FullRO

end GaudisCrypt.EC.PROM
