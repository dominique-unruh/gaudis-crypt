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
  equiv_proc
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
  equiv_proc
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
  equiv_proc
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
  equiv_proc
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
  equiv_proc
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

/-- `lemma RRO_resample_ll : islossless RRO.resample`. -/
theorem RRO_resample_ll (dout_ll : ∀ x, (dout x).1 Set.univ = 1) :
    (RRO.own.resample in_t out_t dout FRO_m).procedure.IsLossless := by
  sorry

/-- `eager [RRO.resample();, FRO.init ~ RRO.init, RRO.resample(); : ={FRO.m} ==> ={FRO.m}]`, at
equality invariants (exception E10). -/
theorem eager_init (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.init in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.init in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  sorry

/-- `eager [RRO.resample();, FRO.get ~ RRO.get, RRO.resample(); : ={x, FRO.m} ==>
={res, FRO.m}]`, at equality invariants (exception E10). -/
theorem eager_get (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.get in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.get in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  sorry

/-- `eager [RRO.resample();, FRO.set ~ RRO.set, RRO.resample(); : ={x, y} /\ ={FRO.m} ==>
={res, FRO.m}]`, at equality invariants (exception E10). -/
theorem eager_set (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.set in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.set in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  sorry

/-- `eager [RRO.resample();, FRO.rem ~ RRO.rem, RRO.resample(); : ={x} /\ ={FRO.m} ==>
={res, FRO.m}]`, at equality invariants (exception E10). -/
theorem eager_rem (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.rem in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.rem in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  sorry

/-- `eager [RRO.resample();, FRO.sample ~ RRO.sample, RRO.resample(); : ={x, FRO.m} ==>
={res, FRO.m}]`, at equality invariants (exception E10). -/
theorem eager_sample (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.sample in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.sample in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  sorry

/-- `eager [RRO.resample();, FRO.queried ~ RRO.queried, RRO.resample(); : ={x, f} /\
={FRO.m} ==> ={res, FRO.m}]`, at equality invariants (exception E10). -/
theorem eager_queried (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.queried in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.queried in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  sorry

/-- `eager [RRO.resample();, FRO.allKnown ~ RRO.allKnown, RRO.resample(); : ={FRO.m} ==>
={res, FRO.m}]`, at equality invariants (exception E10). -/
theorem eager_allKnown (dout_ll : ∀ x, (dout x).1 Set.univ = 1) (a) :
    ProgramDenotation.eagerR (RRO.resampleDen in_t out_t dout FRO_m)
      (RRO.resampleDen in_t out_t dout FRO_m) (fun σ₁ σ₂ => σ₁ = σ₂)
      (procedureDenotation (FRO_T.allKnown in_t out_t (FRO in_t out_t dout FRO_m)).procedure a)
      (procedureDenotation (FRO_T.allKnown in_t out_t (RRO in_t out_t dout FRO_m)).procedure a)
      (fun u v => u = v) := by
  sorry

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

section LRO_RRO
/-! EC's `LRO_RRO_init` … `LRO_RRO_D`: `LRO` and `RRO` agree on the known entries. -/
variable (RO_m : Lens (FMap in_t out_t) VariableAssignment)

/-- `equiv LRO_RRO_init : LRO.init ~ RRO.init : true ==> RO.m{1} = restr Known FRO.m{2}`. -/
theorem LRO_RRO_init : prhlProc (fun _ _ _ _ => True)
    (RO_T.init in_t out_t (LRO in_t out_t dout RO_m)).procedure
    (FRO_T.init in_t out_t (RRO in_t out_t dout FRO_m)).procedure
    (fun _ g₁ _ g₂ => RO_m.get g₁ = FMap.restr Known (FRO_m.get g₂)) := by
  simp only [LRO, RRO, RO_T.init.mk_simp, FRO_T.init.mk_simp]
  equiv_proc
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
  equiv_proc
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
  equiv_proc
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
  equiv_proc
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
  equiv_proc
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

end RO_LRO_D

end FullEager

end FullRO

end GaudisCrypt.EC.PROM
