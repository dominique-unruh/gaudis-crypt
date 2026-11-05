import GaudisCrypt.Examples.SHA3.SHA3Indiff
import GaudisCrypt.Examples.SHA3.OptionIndifferentiability

/-!
# Indifferentiability of the sponge with failing oracles (EasyCrypt `proof/SHA3_OIndiff.ec`)

`SHA3OIndiff`: `SHA3Indiff` restated for `OptionIndifferentiability`, whose oracles return
`option`s and whose restriction to `limit` calls makes the oracles fail (`None`) beyond it.  The
proof reduces it to `SHA3Indiff.security`.

Translation notes (see `notes/SHA3/README.md`):
* `clone import OptionIndifferentiability as OIndif with type p <- state, type f_out <- bool list,
  type f_in <- bool list * int` is the namespace `OIndif` of abbreviations, opened.
* `require import SHA3Indiff` comes last, so its `state`, `parse` and `valid` win over the
  root-level `state` and `Sponge.BIRO.valid`; stated with `export`.
* `FSome(F)` has `proc init = F.init` and is used as a functor (`CSome`): its `init` calls `F.init`
  (exception E5).  `PSome(P)` is only applied to `Perm`: it is a Lean function assembling
  `P.init` with its own `f`, `fi` (`PSome.own`).  `CSome(C)(P) = FSome(C(Poget(P)))` is
  `Module.comp FSome (Module.comp C Poget)`.
* `OSimulator`, `OFC`, `OPC`, `DFSome`, `DPSome` have no type in EasyCrypt; they are declared at the
  types they are used as.
* The section's `declare module Dist` is used by none of its lemmas: `SHA3OIndiff` quantifies its
  own `Dist`.
-/

-- the clone `OIndif` contains the module `OIndif` (`OIndif.OIndif`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.SHA3_OIndiff

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.Sponge
open GaudisCrypt.SHA3.Sponge.BIRO GaudisCrypt.SHA3.SHA3Indiff

-- EasyCrypt's last import, `SHA3Indiff`, shadows the root-level `state` and `Sponge.BIRO.valid`;
-- `PRIMITIVE` is `Sponge`'s (over `Common`'s), as in `SHA3Indiff`
export GaudisCrypt.SHA3.SHA3Indiff (state parse valid PRIMITIVE)

variable [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params]

/-! ## `clone import OptionIndifferentiability as OIndif with type p <- state,
type f_out <- bool list, type f_in <- bool list * int` -/

namespace OIndif
abbrev OPRIMITIVE := OptionIndifferentiability.OPRIMITIVE state (List Bool × ℤ) (List Bool)
abbrev ODPRIMITIVE := OptionIndifferentiability.ODPRIMITIVE state (List Bool × ℤ) (List Bool)
abbrev OFUNCTIONALITY :=
  OptionIndifferentiability.OFUNCTIONALITY state (List Bool × ℤ) (List Bool)
abbrev ODFUNCTIONALITY :=
  OptionIndifferentiability.ODFUNCTIONALITY state (List Bool × ℤ) (List Bool)
abbrev OCONSTRUCTION := OptionIndifferentiability.OCONSTRUCTION state (List Bool × ℤ) (List Bool)
abbrev OSIMULATOR := OptionIndifferentiability.OSIMULATOR state (List Bool × ℤ) (List Bool)
abbrev ODISTINGUISHER :=
  OptionIndifferentiability.ODISTINGUISHER state (List Bool × ℤ) (List Bool)
noncomputable abbrev OIndif := OptionIndifferentiability.OIndif state (List Bool × ℤ) (List Bool)
noncomputable abbrev OGReal := OptionIndifferentiability.OGReal state (List Bool × ℤ) (List Bool)
noncomputable abbrev OGIdeal := OptionIndifferentiability.OGIdeal state (List Bool × ℤ) (List Bool)
abbrev distHoles := OptionIndifferentiability.distHoles state (List Bool × ℤ) (List Bool)
noncomputable abbrev distExt :=
  OptionIndifferentiability.distExt state (List Bool × ℤ) (List Bool)
end OIndif

open OIndif

-- EC's `FSome (F : FUNCTIONALITY) : OFUNCTIONALITY`; its `proc init = F.init` is wrapped in a call,
-- as `FSome` is used as a functor (`CSome`; exception E5)
module FSome using (F : FUNCTIONALITY) : OFUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    return ()
  };
  proc f (x : List Bool × ℤ) : (Option (List Bool)) {
    var z : List Bool;
    z <- call F.f ($x);
    return some $z
  };
}

-- `PSome(P).f` and `PSome(P).fi`, the procedures of `PSome` that are not `P`'s
module PSome.own using (P : PRIMITIVE) {
  proc f (x : state) : (Option state) {
    var z : state;
    z <- call P.f ($x);
    return some $z
  };
  proc fi (x : state) : (Option state) {
    var z : state;
    z <- call P.fi ($x);
    return some $z
  };
}

/-- EC's `PSome (P : PRIMITIVE) : OPRIMITIVE`: `proc init = P.init`, and `proc f`, `proc fi`. -/
noncomputable def PSome (P : PRIMITIVE) : OPRIMITIVE :=
  OptionIndifferentiability.OPRIMITIVE.mk state (List Bool × ℤ) (List Bool)
    { init := Indifferentiability.PRIMITIVE.init (block × capacity) (List Bool × ℤ) (List Bool) P
      f := Module.app PSome.own.f P
      fi := Module.app PSome.own.fi P }

module Poget using (P : ODPRIMITIVE) : DPRIMITIVE {
  proc f (x : state) : state {
    var z : Option state;
    z <- call P.f ($x);
    return oget $z
  };
  proc fi (x : state) : state {
    var z : Option state;
    z <- call P.fi ($x);
    return oget $z
  };
}

/-- `module (CSome (C : CONSTRUCTION) : OCONSTRUCTION) (P : ODPRIMITIVE) = FSome(C(Poget(P)))`. -/
noncomputable def CSome (C : CONSTRUCTION) : OCONSTRUCTION :=
  Module.comp FSome (Module.comp C Poget)

module OSimulator using (F : ODFUNCTIONALITY) : OPRIMITIVE {
  proc init () : Unit {
    Simulator.m <- (FMap.empty : FMap state state);
    Simulator.mi <- (FMap.empty : FMap state state);
    Simulator.paths <- FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0);
    _ <- call Gconcl_list.BIRO2.IRO.init ();
    return ()
  };
  proc f (x : state) : (Option state) {
    var p : List block, v : block, z : List block, q : List block, k : ℤ, cs : List Bool,
      y : state, y1 : block, y2 : capacity, o : Option (List Bool);
    if (!(decide (FMap.dom ($Simulator.m : FMap state state) $x))) {
      if (decide (FMap.dom ($Simulator.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($Simulator.paths : FMap capacity (List block × block)) ($x).2);
        z <- [];
        q, k <- parse (rcons $p ($v +^ ($x).1));
        if (valid $q) {
          o <- call F.f ((oget (unpad_blocks $q), $k * r));
          cs <- oget $o;
          z <- bits2blocks $cs;
        } else {
          z <- call Gconcl_list.BIRO2.IRO.f (($q, $k));
        }
        y1 <- last b0 $z;
      } else {
        y1 <$ bdistr;
      }
      y2 <$ cdistr;
      y <- ($y1, $y2);
      Simulator.m <- FMap.set $Simulator.m $x $y;
      Simulator.mi <- FMap.set $Simulator.mi $y $x;
      if (decide (FMap.dom ($Simulator.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($Simulator.paths : FMap capacity (List block × block)) ($x).2);
        Simulator.paths <- FMap.set $Simulator.paths $y2 (rcons $p ($v +^ ($x).1), ($y).1);
      }
    } else {
      y <- oget (FMap.get ($Simulator.m : FMap state state) $x);
    }
    return some $y
  };
  proc fi (x : state) : (Option state) {
    var y : state, y1 : block, y2 : capacity;
    if (!(decide (FMap.dom ($Simulator.mi : FMap state state) $x))) {
      y1 <$ bdistr;
      y2 <$ cdistr;
      y <- ($y1, $y2);
      Simulator.mi <- FMap.set $Simulator.mi $x $y;
      Simulator.m <- FMap.set $Simulator.m $y $x;
    } else {
      y <- oget (FMap.get ($Simulator.mi : FMap state state) $x);
    }
    return some $y
  };
}

/-- EC's `Counter.c`. -/
global_var Counter.c : ℤ

module Counter {
  proc init () : Unit {
    Counter.c <- 0;
    return ()
  };
}

def increase_counter {α : Type} (c : ℤ) (l : List α) (n : ℤ) : ℤ :=
  c + ((size l + 1) / r + 1) + max ((n + r - 1) / r - 1) 0

module OFC using (F : ODFUNCTIONALITY) : OFUNCTIONALITY {
  proc init () : Unit {
    _ <- call Counter.init ();
    return ()
  };
  proc f (x : List Bool × ℤ) : (Option (List Bool)) {
    var l : List Bool, k : ℤ, o : Option (List Bool);
    l, k <- $x;
    o <- (none : Option (List Bool));
    if (decide (increase_counter $Counter.c $l $k ≤ limit)) {
      o <- call F.f (($l, $k));
      Counter.c <- increase_counter $Counter.c $l $k;
    }
    return $o
  };
}

module OPC using (P : ODPRIMITIVE) : OPRIMITIVE {
  proc init () : Unit {
    return ()
  };
  proc f (x : state) : (Option state) {
    var o : Option state;
    o <- (none : Option state);
    if (decide ($Counter.c + 1 ≤ limit)) {
      o <- call P.f ($x);
      Counter.c <- $Counter.c + 1;
    }
    return $o
  };
  proc fi (x : state) : (Option state) {
    var o : Option state;
    o <- (none : Option state);
    if (decide ($Counter.c + 1 ≤ limit)) {
      o <- call P.fi ($x);
      Counter.c <- $Counter.c + 1;
    }
    return $o
  };
}

-- EC's `ODRestr(D)(F)(P)`, with `D` a Lean parameter so that `ODRestr D` is an `ODISTINGUISHER`
set_option linter.gaudisCrypt.using false in
module ODRestr (D : ODISTINGUISHER) using (F : ODFUNCTIONALITY, P : ODPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call Counter.init ();
    b <- call (Module.app D (Module.pair
      (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app OFC F) })
      (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OPC P)
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OPC P) }))) ();
    return $b
  };
}

/-! ## The section, with `declare module Dist <: ODISTINGUISHER {-Perm, -Gconcl_list.SimLast, …}`
(used by none of its lemmas) -/

section

module DFSome using (F : DFUNCTIONALITY) : ODFUNCTIONALITY {
  proc f (x : List Bool × ℤ) : (Option (List Bool)) {
    var z : List Bool;
    z <- call F.f ($x);
    return some $z
  };
}

module DPSome using (P : DPRIMITIVE) : ODPRIMITIVE {
  proc f (x : state) : (Option state) {
    var z : state;
    z <- call P.f ($x);
    return some $z
  };
  proc fi (x : state) : (Option state) {
    var z : state;
    z <- call P.fi ($x);
    return some $z
  };
}

-- EC's local `(OD (D : ODISTINGUISHER) : DISTINGUISHER) (F : DFUNCTIONALITY) (P : DPRIMITIVE)`,
-- with `D` a Lean parameter so that `OD D` is a `DISTINGUISHER`
set_option linter.gaudisCrypt.using false in
module OD (D : ODISTINGUISHER) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call Counter.init ();
    b <- call (Module.app D (Module.pair
      (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app OFC (Module.app DFSome F)) })
      (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OPC (Module.app DPSome P))
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OPC (Module.app DPSome P)) }))) ();
    return $b
  };
}

/-! ### The two `have`s of `SHA3OIndiff`

The option games against the bit-level games of `SHA3Indiff` for `DRestr(OD(Dist))`: they differ in
`Cntr.c` (written on the right only); EC's invariant `={glob Counter} /\ ={c}(Counter, Cntr)` (with
`={glob Perm}` or `={glob IRO, glob Simulator}`) is the states equal outside `ocL` with `ocI`. -/

/-- The two counters: `Counter.c` (both sides) and `Cntr.c` (right). -/
noncomputable def ocL : Lens (ℤ × ℤ) VariableAssignment := Lens.pair Counter.c Cntr.c

/-- EC's `={glob Counter} /\ ={c}(Counter, Cntr)`, on the contents of `ocL`. -/
def ocI (v₁ v₂ : ℤ × ℤ) : Prop := v₁.1 = v₂.1 ∧ v₂.1 = v₂.2

omit [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params] in
/-- `ocL`'s contents. -/
@[simp] theorem ocL_get (g : VariableAssignment) : ocL.get g = (Counter.c.get g, Cntr.c.get g) :=
  rfl

omit [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params] in
/-- `ocL`'s footprint, its variables'. -/
theorem ocL_footprint : ocL.footprint = Counter.c.footprint ⊔ Cntr.c.footprint := by
  simp only [ocL, Footprint.lens_pair]

omit [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params] in
/-- Writes of `Counter.c` keep the states equal outside `ocL`. -/
theorem ocL_Counter {g₁ g₂ : VariableAssignment} (h : ocL.equal_outside g₁ g₂) (u v : ℤ) :
    ocL.equal_outside (Counter.c.set u g₁) (Counter.c.set v g₂) := by
  have e : ∀ g, Counter.c.set u g = ocL.set (u, Cntr.c.get g) g := fun g => by
    simp only [ocL, Lens.pair]
    rw [Cntr.c.get_set]
  have e' : ∀ g, Counter.c.set v g = ocL.set (v, Cntr.c.get g) g := fun g => by
    simp only [ocL, Lens.pair]
    rw [Cntr.c.get_set]
  rw [e, e']
  exact (h.set_left _).set_right _

omit [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params] in
/-- A write of `Cntr.c` on the right keeps the states equal outside `ocL`. -/
theorem ocL_Cntr_right {g₁ g₂ : VariableAssignment} (h : ocL.equal_outside g₁ g₂) (v : ℤ) :
    ocL.equal_outside g₁ (Cntr.c.set v g₂) := by
  have e : Cntr.c.set v g₂ = ocL.set (Counter.c.get g₂, v) g₂ := by
    simp only [ocL, Lens.pair]
    rw [show Counter.c.get g₂ = Counter.c.get (Cntr.c.set v g₂) from
      (Lens.get_of_disjoint_set _ _ _ _).symm, Counter.c.get_set]
  rw [e]
  exact h.set_right _

/-- EC's premise of the `call` of the oracles below the counters: `P₁.f ~ Q.f` with `res{1} =
Some res{2}`, the states equal outside `ocL` and any relation `J` of its contents kept (the
procedures do not touch the counters).  An abbreviation. -/
def SomeEquiv {α β : Type} [Countable α] (p₁ : Procedure (procsig (α) -> (Option β)))
    (p₂ : Procedure (procsig (α) -> (β))) : Prop :=
  ∀ J : ℤ × ℤ → ℤ × ℤ → Prop,
    prhlProc (sig₁ := procsig (α) -> (Option β)) (sig₂ := procsig (α) -> (β))
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ocL.equal_outside g₁ g₂ ∧ J (ocL.get g₁) (ocL.get g₂))
      p₁ p₂
      (fun r₁ g₁ r₂ g₂ => r₁ = some r₂ ∧ ocL.equal_outside g₁ g₂ ∧ J (ocL.get g₁) (ocL.get g₂))

theorem opc_f (P₁ : ODPRIMITIVE) (Q : DPRIMITIVE)
    (h : SomeEquiv
      (OptionIndifferentiability.ODPRIMITIVE.f state (List Bool × ℤ) (List Bool) P₁).procedure
      (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        Q).procedure) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ocL.equal_outside g₁ g₂ ∧ ocI (ocL.get g₁) (ocL.get g₂))
      (OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
        (Module.app OPC P₁)).procedure
      (OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
        (Module.app OPC (Module.app DPSome
          (Indifferentiability.DPRIMITIVE.mk (block × capacity) (List Bool × ℤ) (List Bool)
            { f := Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
                (Module.app PC Q),
              fi := Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ)
                (List Bool) (Module.app PC Q) })))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ocL.equal_outside g₁ g₂ ∧ ocI (ocL.get g₁) (ocL.get g₂)) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §o{1} = §o{2} ∧
      ocL.equal_outside §allGlobals{1} §allGlobals{2} ∧ ocI §ocL{1} §ocL{2})
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  equiv_if
  case guard =>
    rintro g₁ g₂ _ _ _ _ ⟨-, -, -, hI⟩
    simp only [ocL_get, ocI] at hI
    rw [hI.1]
  case «else» =>
    equiv_skip
    rintro g₁ g₂ _ _ _ _ ⟨⟨-, ho, he, hI⟩, -⟩
    exact ⟨ho, he, hI⟩
  case «then» =>
    stmt_inline{2} 0
    simp only [Indifferentiability.DPRIMITIVE.f.mk_simp]
    stmt_inline{2} 0
    stmt_wp
    refine prhlStmt_fix_left (fun σ => Counter.c.get σ.globals) fun k => ?_
    equiv_seq 1 1 : (§x0{1} = §a{2} ∧ ocL.equal_outside §allGlobals{1} §allGlobals{2} ∧
        Counter.c.get §allGlobals{1} = k ∧ Counter.c.get §allGlobals{2} = k ∧
        Cntr.c.get §allGlobals{2} = k ∧ k + 1 ≤ limit)
    · stmt_wp
      equiv_skip
      rintro g₁ g₂ x0 _ x0' _ ⟨⟨⟨rfl, -, he, hI⟩, hg⟩, rfl⟩
      simp only [ocL_get, ocI] at hI
      simp only [decide_eq_true_eq] at hg
      exact ⟨rfl, he, rfl, hI.1.symm, by rw [← hI.2, ← hI.1], hg⟩
    equiv_if{2}
    case «then» =>
      stmt_wp
      equiv_call (h fun v₁ v₂ => v₁.1 = k ∧ v₂.1 = k ∧ v₂.2 = k)
      equiv_skip
      rintro g₁ g₂ x0 a ⟨⟨rfl, he, h1, h2, h3, -⟩, -⟩
      refine ⟨⟨rfl, he, h1, h2, h3⟩, ?_⟩
      rintro r₁ g₁' r₂ g₂' ⟨rfl, he', h1', h2', h3'⟩
      refine ⟨rfl, ocL_Counter (ocL_Cntr_right he' _) _ _, ?_⟩
      simp only [ocL_get, ocI]
      simp_reads
      simp only [ocL_get] at h1' h2' h3'
      omega
    case «else» =>
      refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
      obtain ⟨⟨-, -, -, -, h3, hk⟩, hg⟩ := h
      simp only [decide_eq_false_iff_not] at hg
      exact hg (h3 ▸ hk)

theorem opc_fi (P₁ : ODPRIMITIVE) (Q : DPRIMITIVE)
    (h : SomeEquiv
      (OptionIndifferentiability.ODPRIMITIVE.fi state (List Bool × ℤ) (List Bool) P₁).procedure
      (Indifferentiability.DPRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
        Q).procedure) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ocL.equal_outside g₁ g₂ ∧ ocI (ocL.get g₁) (ocL.get g₂))
      (OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
        (Module.app OPC P₁)).procedure
      (OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
        (Module.app OPC (Module.app DPSome
          (Indifferentiability.DPRIMITIVE.mk (block × capacity) (List Bool × ℤ) (List Bool)
            { f := Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
                (Module.app PC Q),
              fi := Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ)
                (List Bool) (Module.app PC Q) })))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ocL.equal_outside g₁ g₂ ∧ ocI (ocL.get g₁) (ocL.get g₂)) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §o{1} = §o{2} ∧
      ocL.equal_outside §allGlobals{1} §allGlobals{2} ∧ ocI §ocL{1} §ocL{2})
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  equiv_if
  case guard =>
    rintro g₁ g₂ _ _ _ _ ⟨-, -, -, hI⟩
    simp only [ocL_get, ocI] at hI
    rw [hI.1]
  case «else» =>
    equiv_skip
    rintro g₁ g₂ _ _ _ _ ⟨⟨-, ho, he, hI⟩, -⟩
    exact ⟨ho, he, hI⟩
  case «then» =>
    stmt_inline{2} 0
    simp only [Indifferentiability.DPRIMITIVE.fi.mk_simp]
    stmt_inline{2} 0
    stmt_wp
    refine prhlStmt_fix_left (fun σ => Counter.c.get σ.globals) fun k => ?_
    equiv_seq 1 1 : (§x0{1} = §a{2} ∧ ocL.equal_outside §allGlobals{1} §allGlobals{2} ∧
        Counter.c.get §allGlobals{1} = k ∧ Counter.c.get §allGlobals{2} = k ∧
        Cntr.c.get §allGlobals{2} = k ∧ k + 1 ≤ limit)
    · stmt_wp
      equiv_skip
      rintro g₁ g₂ x0 _ x0' _ ⟨⟨⟨rfl, -, he, hI⟩, hg⟩, rfl⟩
      simp only [ocL_get, ocI] at hI
      simp only [decide_eq_true_eq] at hg
      exact ⟨rfl, he, rfl, hI.1.symm, by rw [← hI.2, ← hI.1], hg⟩
    equiv_if{2}
    case «then» =>
      stmt_wp
      equiv_call (h fun v₁ v₂ => v₁.1 = k ∧ v₂.1 = k ∧ v₂.2 = k)
      equiv_skip
      rintro g₁ g₂ x0 a ⟨⟨rfl, he, h1, h2, h3, -⟩, -⟩
      refine ⟨⟨rfl, he, h1, h2, h3⟩, ?_⟩
      rintro r₁ g₁' r₂ g₂' ⟨rfl, he', h1', h2', h3'⟩
      refine ⟨rfl, ocL_Counter (ocL_Cntr_right he' _) _ _, ?_⟩
      simp only [ocL_get, ocI]
      simp_reads
      simp only [ocL_get] at h1' h2' h3'
      omega
    case «else» =>
      refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
      obtain ⟨⟨-, -, -, -, h3, hk⟩, hg⟩ := h
      simp only [decide_eq_false_iff_not] at hg
      exact hg (h3 ▸ hk)

theorem ofc_f (F₁ : ODFUNCTIONALITY) (F₂ : DFUNCTIONALITY)
    (h : SomeEquiv
      (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool × ℤ) (List Bool) F₁).procedure
      (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
        F₂).procedure) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ocL.equal_outside g₁ g₂ ∧ ocI (ocL.get g₁) (ocL.get g₂))
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app OFC F₁)).procedure
      (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app OFC (Module.app DFSome
          (Indifferentiability.DFUNCTIONALITY.mk (block × capacity) (List Bool × ℤ) (List Bool)
            { f := Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ)
                (List Bool) (Module.app FC F₂) })))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ocL.equal_outside g₁ g₂ ∧ ocI (ocL.get g₁) (ocL.get g₂)) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§l{1} = §l{2} ∧ §k{1} = §k{2} ∧ §o{1} = §o{2} ∧
      ocL.equal_outside §allGlobals{1} §allGlobals{2} ∧ ocI §ocL{1} §ocL{2})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ ⟨rfl, he, hI⟩
    exact ⟨rfl, rfl, he, hI⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ _ _ _ _ _ _ ⟨rfl, rfl, -, -, hI⟩
    simp only [ocL_get, ocI] at hI
    rw [hI.1]
  case «else» =>
    equiv_skip
    rintro g₁ g₂ _ _ _ _ _ _ ⟨⟨-, -, ho, he, hI⟩, -⟩
    exact ⟨ho, he, hI⟩
  case «then» =>
    stmt_inline{2} 0
    simp only [Indifferentiability.DFUNCTIONALITY.f.mk_simp]
    stmt_inline{2} 0
    stmt_wp
    refine prhlStmt_fix_left (fun σ => (Counter.c.get σ.globals,
      (localVarLens "l" (List Bool)).get σ, (localVarLens "k" ℤ).get σ)) fun q => ?_
    equiv_seq 1 1 : (§l{1} = §bs{2} ∧ §k{1} = §n{2} ∧
        ocL.equal_outside §allGlobals{1} §allGlobals{2} ∧
        Counter.c.get §allGlobals{1} = q.1 ∧ Counter.c.get §allGlobals{2} = q.1 ∧
        Cntr.c.get §allGlobals{2} = q.1 ∧ §l{1} = q.2.1 ∧ §k{1} = q.2.2 ∧
        §l{2} = q.2.1 ∧ §k{2} = q.2.2 ∧ increase_counter q.1 q.2.1 q.2.2 ≤ limit)
    · stmt_wp
      equiv_skip
      rintro g₁ g₂ l k o l' k' o' ⟨⟨⟨rfl, rfl, -, he, hI⟩, hg⟩, rfl⟩
      simp only [ocL_get, ocI] at hI
      simp only [decide_eq_true_eq] at hg
      exact ⟨rfl, rfl, he, rfl, hI.1.symm, by rw [← hI.2, ← hI.1], rfl, rfl, rfl, rfl, hg⟩
    equiv_if{2}
    case «then» =>
      equiv_call (h fun v₁ v₂ => v₁.1 = q.1 ∧ v₂.1 = q.1 ∧
        v₂.2 = increase_counter q.1 q.2.1 q.2.2)
      stmt_wp
      equiv_skip
      rintro g₁ g₂ l₁ k₁ bs n l₂ k₂ ⟨⟨hbs, hn, he, h1, h2, h3, hl1, hk1, hl2, hk2, -⟩, -⟩
      subst hbs hn hl1 hk1 hl2 hk2
      refine ⟨⟨rfl, ocL_Cntr_right he _, ?_, ?_, ?_⟩, ?_⟩
      · exact h1
      · simp only [ocL_get]
        simp_reads
        exact h2
      · simp only [ocL_get]
        simp_reads
        rw [h3]
        rfl
      · rintro r₁ g₁' r₂ g₂' ⟨rfl, he', h1', h2', h3'⟩
        refine ⟨rfl, ocL_Counter he' _ _, ?_⟩
        simp only [ocL_get, ocI]
        simp_reads
        simp only [ocL_get] at h1' h2' h3'
        rw [h1', h2', h3']
        exact ⟨rfl, rfl⟩
    case «else» =>
      refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
      obtain ⟨⟨hl, hk, -, -, -, h3, hl', hk', -, -, hc⟩, hg⟩ := h
      simp only [decide_eq_false_iff_not] at hg
      apply hg
      rw [h3, ← hl, ← hk, hl', hk']
      exact hc

omit [Gconcl_list.Params] in
/-- EC's `call (_ : I); while …` on `Sponge(P₁).f ~ Sponge(P₂).f`: an invariant `I` kept by
`P₁.f ~ P₂.f` (equal arguments to equal results) is kept by the sponge, both loops in lockstep.
Not an EC lemma. -/
theorem Sponge_f_equiv (P₁ P₂ : DPRIMITIVE) (I : VariableAssignment → VariableAssignment → Prop)
    (hPf : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ I g₁ g₂)
      (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        P₁).procedure
      (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        P₂).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ I g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ I g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app Sponge.Sponge P₁)).procedure
      (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app Sponge.Sponge P₂)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ I g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 2 2 : (§n{1} = §n{2} ∧ §z{1} = §z{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧
      §i{1} = §i{2} ∧ §xs{1} = §xs{2} ∧ I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ ⟨rfl, hg⟩
    exact ⟨rfl, rfl, hg⟩
  equiv_seq 1 1 : (§n{1} = §n{2} ∧ §z{1} = §z{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧
      §i{1} = §i{2} ∧ I §allGlobals{1} §allGlobals{2})
  · equiv_while (§n{1} = §n{2} ∧ §z{1} = §z{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧
        §i{1} = §i{2} ∧ §xs{1} = §xs{2} ∧ I §allGlobals{1} §allGlobals{2})
    case body =>
      stmt_wp
      equiv_call hPf
      equiv_skip
      rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, hg⟩, -⟩
      exact ⟨⟨rfl, hg⟩, fun _ _ _ _ ⟨rfl, hg'⟩ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, hg'⟩⟩
    case guard => intros; simp_all
    case exit =>
      rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, -, hg⟩ -
      exact ⟨rfl, rfl, rfl, rfl, rfl, hg⟩
    · equiv_skip
      intros; simp_all
  · equiv_while (§n{1} = §n{2} ∧ §z{1} = §z{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧
        §i{1} = §i{2} ∧ I §allGlobals{1} §allGlobals{2})
    case body =>
      equiv_seq 1 1 : ((§n{1} = §n{2} ∧ §z{1} = §z{2} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧
        §i{1} = §i{2} ∧ I §allGlobals{1} §allGlobals{2}) ∧ §i{1} = §i{2})
      · stmt_wp
        equiv_skip
        intros; simp_all
      · equiv_if
        case guard => intros; simp_all
        case «then» =>
          equiv_call hPf
          equiv_skip
          rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, hg⟩, -⟩, -⟩
          exact ⟨⟨rfl, hg⟩, fun _ _ _ _ ⟨rfl, hg'⟩ => ⟨rfl, rfl, rfl, rfl, rfl, hg'⟩⟩
        case «else» => equiv_skip; intros; simp_all
    case guard => intros; simp_all
    case exit =>
      rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, hg⟩ -
      exact ⟨rfl, hg⟩
    · equiv_skip
      intros; simp_all

/-- `PSome(P).f ~ P.f` with `res{1} = Some res{2}`, for `P` outside the counters (EC: `inline*;
sim`). -/
theorem psome_f (P : PRIMITIVE)
    (hP : FVP.fvP (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
      P) ≤ (ocL.footprint)ᶜ) :
    SomeEquiv (OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
        (PSome P)).procedure
      (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        P).procedure := by
  intro J
  simp only [PSome, OptionIndifferentiability.OPRIMITIVE.f.mk_simp]
  equiv_proc
  stmt_inline{1} 0
  stmt_wp
  equiv_call (prhlProc_self_equal_outside_module ocL _ hP J)
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x x' ⟨rfl, he, hJ⟩
  exact ⟨⟨rfl, he, hJ⟩, fun _ _ _ _ ⟨rfl, he', hJ'⟩ => ⟨rfl, he', hJ'⟩⟩

/-- `PSome(P).fi ~ P.fi` with `res{1} = Some res{2}`, for `P` outside the counters. -/
theorem psome_fi (P : PRIMITIVE)
    (hP : FVP.fvP (Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
      P) ≤ (ocL.footprint)ᶜ) :
    SomeEquiv (OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
        (PSome P)).procedure
      (Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
        P).procedure := by
  intro J
  simp only [PSome, OptionIndifferentiability.OPRIMITIVE.fi.mk_simp]
  equiv_proc
  stmt_inline{1} 0
  stmt_wp
  equiv_call (prhlProc_self_equal_outside_module ocL _ hP J)
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x x' ⟨rfl, he, hJ⟩
  exact ⟨⟨rfl, he, hJ⟩, fun _ _ _ _ ⟨rfl, he', hJ'⟩ => ⟨rfl, he', hJ'⟩⟩

/-- `Poget(PSome(P)).f ~ P.f`, the states equal outside `ocL` with any `J` (EC: `inline*; sim`). -/
theorem poget_psome_f (P : PRIMITIVE)
    (hP : FVP.fvP (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
      P) ≤ (ocL.footprint)ᶜ) (J : ℤ × ℤ → ℤ × ℤ → Prop) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ocL.equal_outside g₁ g₂ ∧ J (ocL.get g₁) (ocL.get g₂))
      (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app Poget (OptionIndifferentiability.OPRIMITIVE.view state (List Bool × ℤ)
          (List Bool) (PSome P)))).procedure
      (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Indifferentiability.PRIMITIVE.view (block × capacity) (List Bool × ℤ) (List Bool)
          P)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ocL.equal_outside g₁ g₂ ∧ J (ocL.get g₁) (ocL.get g₂)) := by
  simp only [OptionIndifferentiability.OPRIMITIVE.view, Indifferentiability.PRIMITIVE.view,
    Indifferentiability.DPRIMITIVE.f.mk_simp]
  equiv_proc
  stmt_inline{1} 0
  simp only [OptionIndifferentiability.ODPRIMITIVE.f.mk_simp]
  stmt_wp
  equiv_call (psome_f P hP J)
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x x' ⟨rfl, he, hJ⟩
  exact ⟨⟨rfl, he, hJ⟩, fun _ _ _ _ ⟨hr, he', hJ'⟩ => ⟨by rw [hr]; rfl, he', hJ'⟩⟩

/-- The real side's functionality: `FSome(Sponge(Poget(PSome(Perm)))).f ~ Sponge(Perm).f` with
`res{1} = Some res{2}` (EC: `inline*; …; sim; while (={glob Perm, …})`). -/
theorem real_F (P : PRIMITIVE)
    (hP : FVP.fvP (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
      P) ≤ (ocL.footprint)ᶜ) :
    SomeEquiv (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app FSome (Module.app Sponge.Sponge (Module.app Poget
          (OptionIndifferentiability.OPRIMITIVE.view state (List Bool × ℤ) (List Bool)
            (PSome P)))))).procedure
      (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app Sponge.Sponge (Indifferentiability.PRIMITIVE.view (block × capacity)
          (List Bool × ℤ) (List Bool) P))).procedure := by
  intro J
  equiv_proc
  stmt_inline{1} 0
  stmt_wp
  equiv_call (Sponge_f_equiv _ _ (fun g₁ g₂ => ocL.equal_outside g₁ g₂ ∧ J (ocL.get g₁)
    (ocL.get g₂)) (poget_psome_f P hP J))
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x x' ⟨rfl, he, hJ⟩
  exact ⟨⟨rfl, he, hJ⟩, fun _ _ _ _ ⟨rfl, he', hJ'⟩ => ⟨rfl, he', hJ'⟩⟩

instance : Lens.Disjoint Simulator.m ocL := by unfold ocL; infer_instance
instance : Lens.Disjoint Simulator.mi ocL := by unfold ocL; infer_instance
instance : Lens.Disjoint Simulator.paths ocL := by unfold ocL; infer_instance

omit [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params] in
/-- The same write of a variable outside `ocL` keeps the states equal outside `ocL` and the
contents of `ocL`. -/
theorem ocL_set {β : Type} {X : Lens β VariableAssignment} [Lens.Disjoint X ocL]
    {J : ℤ × ℤ → ℤ × ℤ → Prop} {g₁ g₂ : VariableAssignment}
    (h : ocL.equal_outside g₁ g₂ ∧ J (ocL.get g₁) (ocL.get g₂)) (v : β) :
    ocL.equal_outside (X.set v g₁) (X.set v g₂) ∧
      J (ocL.get (X.set v g₁)) (ocL.get (X.set v g₂)) := by
  refine ⟨h.1.set_disjoint v, ?_⟩
  rw [Lens.get_of_disjoint_set ocL X, Lens.get_of_disjoint_set ocL X]
  exact h.2

/-- `FSome(F).f ~ F.f` with `res{1} = Some res{2}`, for `F` outside the counters (EC: `inline*;
sim`). -/
theorem fsome_f (F : FUNCTIONALITY)
    (hF : FVP.fvP (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ)
      (List Bool) F) ≤ (ocL.footprint)ᶜ) :
    SomeEquiv (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        (Module.app FSome F)).procedure
      (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
        F).procedure := by
  intro J
  equiv_proc
  stmt_inline{1} 0
  stmt_wp
  equiv_call (prhlProc_self_equal_outside_module ocL _ hF J)
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x x' ⟨rfl, he, hJ⟩
  exact ⟨⟨rfl, he, hJ⟩, fun _ _ _ _ ⟨rfl, he', hJ'⟩ => ⟨rfl, he', hJ'⟩⟩

/-- `OSimulator(FSome(F)).fi ~ Simulator(F).fi` with `res{1} = Some res{2}`: the same code on the
same variables (EC: `inline*; sim`). -/
theorem osim_fi (F : FUNCTIONALITY) :
    SomeEquiv (OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
        (Module.app OSimulator (OptionIndifferentiability.OFUNCTIONALITY.view state
          (List Bool × ℤ) (List Bool) (Module.app FSome F)))).procedure
      (Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app Simulator (Indifferentiability.FUNCTIONALITY.view (block × capacity)
          (List Bool × ℤ) (List Bool) F))).procedure := by
  intro J
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ ocL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      J §ocL{1} §ocL{2})
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  equiv_if
  case guard =>
    rintro g₁ g₂ _ _ ⟨rfl, he, -⟩
    rw [he.get_disjoint]
  case «else» =>
    stmt_wp
    equiv_skip
    rintro g₁ g₂ _ _ ⟨⟨rfl, he, hJ⟩, -⟩
    exact ⟨by rw [he.get_disjoint], he, hJ⟩
  case «then» =>
    stmt_wp
    equiv_rnd
    equiv_rnd
    equiv_skip
    rintro g₁ g₂ _ _ ⟨⟨rfl, he, hJ⟩, -⟩
    intro _ _ _ _
    rw [he.get_disjoint (X := Simulator.m), he.get_disjoint (X := Simulator.mi)]
    exact ⟨(he.set_disjoint _).set_disjoint _, hJ⟩

/-- `OSimulator(FSome(F)).f ~ Simulator(F).f` with `res{1} = Some res{2}`: the same code on the
same variables, but for the call of `F.f`, through `FSome` on the left (EC: `inline*; sim;
if; …`). -/
theorem osim_f (F : FUNCTIONALITY)
    (hF : FVP.fvP (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ)
      (List Bool) F) ≤ (ocL.footprint)ᶜ) :
    SomeEquiv (OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
        (Module.app OSimulator (OptionIndifferentiability.OFUNCTIONALITY.view state
          (List Bool × ℤ) (List Bool) (Module.app FSome F)))).procedure
      (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
        (Module.app Simulator (Indifferentiability.FUNCTIONALITY.view (block × capacity)
          (List Bool × ℤ) (List Bool) F))).procedure := by
  intro J
  have hB : FVP.fvP Gconcl_list.BIRO2.IRO.f ≤ (ocL.footprint)ᶜ := by
    rw [ocL_footprint]
    fp_disjoint
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ ocL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      J §ocL{1} §ocL{2})
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  equiv_if
  case guard =>
    rintro g₁ g₂ _ _ ⟨rfl, he, -⟩
    rw [he.get_disjoint]
  case «else» =>
    stmt_wp
    equiv_skip
    rintro g₁ g₂ _ _ ⟨⟨rfl, he, hJ⟩, -⟩
    exact ⟨by rw [he.get_disjoint], he, hJ⟩
  case «then» =>
    simp only [OptionIndifferentiability.OFUNCTIONALITY.view,
      OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp, Indifferentiability.FUNCTIONALITY.view,
      Indifferentiability.DFUNCTIONALITY.f.mk_simp]
    equiv_seq 5 5 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧
        ocL.equal_outside §allGlobals{1} §allGlobals{2} ∧ J §ocL{1} §ocL{2})
    · equiv_if
      case guard =>
        rintro g₁ g₂ _ _ ⟨⟨rfl, he, -⟩, -⟩
        rw [he.get_disjoint]
      case «then» =>
        stmt_wp
        equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧
            ocL.equal_outside §allGlobals{1} §allGlobals{2} ∧ J §ocL{1} §ocL{2})
        · stmt_wp
          equiv_skip
          rintro g₁ g₂ _ _ ⟨⟨⟨rfl, he, hJ⟩, -⟩, -⟩
          rw [he.get_disjoint]
          exact ⟨rfl, rfl, rfl, he, hJ⟩
        equiv_if
        case guard =>
          rintro g₁ g₂ _ _ _ _ _ _ ⟨rfl, rfl, rfl, -, -⟩
          rfl
        case «then» =>
          stmt_wp
          equiv_call (fsome_f F hF J)
          equiv_skip
          rintro g₁ g₂ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, he, hJ⟩, -⟩
          refine ⟨⟨rfl, he, hJ⟩, fun r₁ _ r₂ _ ⟨hr, he', hJ'⟩ => ⟨rfl, ?_, he', hJ'⟩⟩
          rw [hr]
          rfl
        case «else» =>
          equiv_call (prhlProc_self_equal_outside_module ocL _ hB J)
          equiv_skip
          rintro g₁ g₂ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, he, hJ⟩, -⟩
          exact ⟨⟨rfl, he, hJ⟩, fun _ _ _ _ ⟨rfl, he', hJ'⟩ => ⟨rfl, rfl, he', hJ'⟩⟩
      case «else» =>
        equiv_rnd
        equiv_skip
        rintro g₁ g₂ _ _ ⟨⟨⟨rfl, he, hJ⟩, -⟩, -⟩
        exact fun _ _ => ⟨rfl, he, hJ⟩
    equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §y{1} = §y{2} ∧ §y2{1} = §y2{2} ∧
        ocL.equal_outside §allGlobals{1} §allGlobals{2} ∧ J §ocL{1} §ocL{2})
    · stmt_wp
      equiv_rnd
      equiv_skip
      rintro g₁ g₂ _ _ _ _ ⟨rfl, rfl, he, hJ⟩
      intro _ _
      rw [he.get_disjoint (X := Simulator.m), he.get_disjoint (X := Simulator.mi)]
      exact ⟨rfl, rfl, (he.set_disjoint _).set_disjoint _, hJ⟩
    equiv_if
    case guard =>
      rintro g₁ g₂ _ _ _ _ _ _ ⟨rfl, -, -, he, -⟩
      rw [he.get_disjoint]
    case «then» =>
      stmt_wp
      equiv_skip
      rintro g₁ g₂ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, he, hJ⟩, -⟩
      rw [he.get_disjoint (X := Simulator.paths)]
      exact ⟨rfl, he.set_disjoint _, hJ⟩
    case «else» =>
      equiv_skip
      rintro g₁ g₂ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, he, hJ⟩, -⟩
      exact ⟨rfl, he, hJ⟩

/-- `PSome(P).init` is `P.init`. -/
theorem PSome_init (P : PRIMITIVE) :
    OptionIndifferentiability.OPRIMITIVE.init state (List Bool × ℤ) (List Bool) (PSome P) =
      Indifferentiability.PRIMITIVE.init (block × capacity) (List Bool × ℤ) (List Bool) P := by
  simp [PSome]

/-- `FSome(F).init` is the module of its procedure. -/
theorem FSome_init (F : FUNCTIONALITY) :
    OptionIndifferentiability.OFUNCTIONALITY.init state (List Bool × ℤ) (List Bool)
      (Module.app FSome F) = Module.app FSome.init F := by
  rw [FSome.apply_simp]
  exact Module.fst_pair _ _

omit [Gconcl_list.Params] in
/-- `Sponge(P).init` is the module of its procedure. -/
theorem Sponge_init (P : DPRIMITIVE) :
    Indifferentiability.FUNCTIONALITY.init (block × capacity) (List Bool × ℤ) (List Bool)
      (Module.app Sponge.Sponge P) = Sponge.init := by
  rw [Sponge.apply_simp]
  exact Module.fst_pair _ _

theorem real_equiv (Dist : ODISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (hDc : FVP.fvP Dist ≤ (ocL.footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (OGReal (CSome Sponge.Sponge) (PSome Perm) (ODRestr Dist)).procedure
      (RealIndif Sponge.Sponge Perm (DRestr (OD Dist))).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hPf : FVP.fvP (Indifferentiability.PRIMITIVE.f (block × capacity) (List Bool × ℤ)
      (List Bool) Perm) ≤ (ocL.footprint)ᶜ := by
    rw [ocL_footprint]
    fp_disjoint
  have hPfi : FVP.fvP (Indifferentiability.PRIMITIVE.fi (block × capacity) (List Bool × ℤ)
      (List Bool) Perm) ≤ (ocL.footprint)ᶜ := by
    rw [ocL_footprint]
    fp_disjoint
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  simp only [CSome, Module.app_comp, PSome_init, FSome_init, Sponge_init]
  repeat stmt_inline{1} 1
  repeat stmt_inline{2} 1
  stmt_wp
  equiv_seq 1 1 : (ocL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      ocI (ocL.get §allGlobals{1}) (ocL.get §allGlobals{2}))
  · stmt_wp
    equiv_call (prhlProc_refl
      (Indifferentiability.PRIMITIVE.init (block × capacity) (List Bool × ℤ) (List Bool)
        Perm).procedure)
    stmt_wp
    equiv_skip
    rintro σ₁ σ₂ h
    refine ⟨h, fun _ g₁ _ g₂ hg => ?_⟩
    subst hg
    refine ⟨ocL_Counter (ocL_Cntr_right (Lens.equal_outside.refl g₁) 0) 0 0, ?_⟩
    simp only [ocL_get, ocI]
    simp_reads
    trivial
  stmt_split{1} 1
  stmt_split{2} 1
  refine prhlStmt_seq_call (prhlProc_abstract_call_equal_outside_module
    ocL Dist distExt hD.1 hDc ocI ?hc _ _ ?horacle) ?_
  case hc =>
    intro _ n
    cases n with
    | zero => exact inferInstanceAs (Countable (List Bool × ℤ))
    | succ n => cases n with
      | zero => exact inferInstanceAs (Countable (block × capacity))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable (block × capacity))
        | succ n => nomatch n
  case horacle =>
    intro _ n
    cases n with
    | zero =>
      simp only [OptionIndifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
        Module.fst_pair, Module.snd_pair, OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
        OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
        OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
      refine ofc_f _ _ ?_
      simp only [OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
        Indifferentiability.DFUNCTIONALITY.f.mk_simp]
      exact real_F Perm hPf
    | succ n => cases n with
      | zero =>
        simp only [OptionIndifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
          HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
          OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
          OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
          OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
        refine opc_f _ _ ?_
        simp only [OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
          Indifferentiability.DPRIMITIVE.f.mk_simp]
        exact psome_f Perm hPf
      | succ n => cases n with
        | zero =>
          simp only [OptionIndifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
            OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
            OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
            OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
          refine opc_fi _ _ ?_
          simp only [OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp,
            Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact psome_fi Perm hPfi
        | succ n => nomatch n
  equiv_skip
  intro σ₁ σ₂ h
  refine ⟨⟨rfl, h⟩, fun r₁ g₁ r₂ g₂ ⟨hr, _⟩ => ?_⟩
  simp_reads
  exact hr

theorem ideal_equiv (Dist : ODISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (hDc : FVP.fvP Dist ≤ (ocL.footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (OGIdeal (Module.app FSome BIRO.IRO.asF) OSimulator (ODRestr Dist)).procedure
      (IdealIndif BIRO.IRO.asF Simulator (DRestr (OD Dist))).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hI : FVP.fvP (Indifferentiability.FUNCTIONALITY.f (block × capacity) (List Bool × ℤ)
      (List Bool) BIRO.IRO.asF) ≤ (ocL.footprint)ᶜ := by
    rw [ocL_footprint]
    fp_disjoint
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (ocL.equal_outside §allGlobals{1} §allGlobals{2} ∧
      ocI (ocL.get §allGlobals{1}) (ocL.get §allGlobals{2}))
  · stmt_wp
    equiv_skip
    rintro σ₁ σ₂ h
    refine ⟨ocL_Counter (ocL_Cntr_right (h ▸ Lens.equal_outside.refl _) 0) 0 0, ?_⟩
    simp only [ocL_get, ocI]
    simp_reads
    trivial
  stmt_split{1} 1
  stmt_split{2} 1
  refine prhlStmt_seq_call (prhlProc_abstract_call_equal_outside_module
    ocL Dist distExt hD.1 hDc ocI ?hc _ _ ?horacle) ?_
  case hc =>
    intro _ n
    cases n with
    | zero => exact inferInstanceAs (Countable (List Bool × ℤ))
    | succ n => cases n with
      | zero => exact inferInstanceAs (Countable (block × capacity))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable (block × capacity))
        | succ n => nomatch n
  case horacle =>
    intro _ n
    cases n with
    | zero =>
      simp only [OptionIndifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
        Module.fst_pair, Module.snd_pair, OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
        OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
        OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
      refine ofc_f _ _ ?_
      simp only [OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
        Indifferentiability.DFUNCTIONALITY.f.mk_simp]
      exact fsome_f _ hI
    | succ n => cases n with
      | zero =>
        simp only [OptionIndifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
          HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
          OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
          OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
          OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
        refine opc_f _ _ ?_
        simp only [OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
          Indifferentiability.DPRIMITIVE.f.mk_simp]
        exact osim_f _ hI
      | succ n => cases n with
        | zero =>
          simp only [OptionIndifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
            OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp,
            OptionIndifferentiability.ODPRIMITIVE.f.mk_simp,
            OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp]
          refine opc_fi _ _ ?_
          simp only [OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp,
            Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact osim_fi _
        | succ n => nomatch n
  equiv_skip
  intro σ₁ σ₂ h
  refine ⟨⟨rfl, h⟩, fun r₁ g₁ r₂ g₂ ⟨hr, _⟩ => ?_⟩
  simp_reads
  exact hr

/-- `SHA3OIndiff`'s restriction `{-Counter, -Perm, -IRO, -BlockSponge.BIRO.IRO, -Cntr, -Simulator,
-Gconcl_list.SimLast(Gconcl.S), -BlockSponge.C, -Gconcl.S, -SLCommon.F.RO, -SLCommon.F.FRO,
-SLCommon.Redo, -SLCommon.C, -Gconcl_list.BIRO2.IRO, -Gconcl_list.F2.RO, -Gconcl_list.F2.FRO,
-Gconcl_list.Simulator, -OSimulator}`: `SHA3Indiff`'s, and `Counter`, `OSimulator` (an
abbreviation). -/
def ODistRestrictions (Dist : ODISTINGUISHER) : Prop :=
  FVP.fvP Dist ≤ (DistRestrictions.footprint ⊔ Counter.c.footprint ⊔
    (FVP.fvP OSimulator).glob)ᶜ

set_option maxHeartbeats 4000000 in
-- `fp_module` through `OD`'s nest of oracles
/-- `OD(Dist)` touches `Dist`'s variables and `Counter.c`.  Not an EC lemma. -/
theorem fvP_OD (Dist : ODISTINGUISHER) :
    FVP.fvP (OD Dist) ≤ FVP.fvP Dist ⊔ Counter.c.footprint := by
  fp_module Counter.c

/-- `Counter.c` is outside `SHA3Indiff`'s restrictions (`-Gconcl_list.SimLast` by
`Footprint.le_compl_glob_symm`).  Not an EC lemma. -/
theorem Counter_DistRestrictions : Counter.c.footprint ≤ DistRestrictions.footprintᶜ := by
  have hSL : (FVP.fvP (Gconcl_list.SimLast Gconcl.S)).FinitelySupported := SimLast_ECModule.2
  have hg : (FVP.fvP (Gconcl_list.SimLast Gconcl.S)).glob ≤ Counter.c.footprintᶜ :=
    (Footprint.le_compl_comm _ _).mp (Footprint.globalVar_le_compl_glob hSL Counter.c
      (by fp_disjoint))
  unfold DistRestrictions.footprint
  refine (Footprint.le_compl_comm _ _).mpr ?_
  unfold SLCommon.C.footprint
  repeat' refine sup_le ?_ ?_
  all_goals first
    | with_reducible exact hg
    | fp_disjoint

/-- `SHA3Indiff.Gext0Fresh` for an `ODISTINGUISHER`: the variables of `Gconcl`'s
`local clone import Gext as Gext0` lie outside `Dist` (exception E13). -/
def OGext0Fresh (Dist : ODISTINGUISHER) : Prop :=
  FVP.fvP Dist ≤ ((ConcreteF.PF.m).footprint ⊔ (ConcreteF.PF.mi).footprint ⊔
    (Handle.G1.m).footprint ⊔
    (Handle.G1.mi).footprint ⊔ (Handle.G1.mh).footprint ⊔ (Handle.G1.mhi).footprint ⊔
    Handle.G1.chandle.footprint ⊔ (Handle.G1.paths).footprint ⊔ Handle.G1.bext.footprint ⊔
    Handle.G1.bcol.footprint ⊔ (Handle.FRO.m).footprint ⊔ (Handle.ROhandle.RO.m).footprint)ᶜ

/-- `OPC(DPSome(P)).f` is lossless when `P.f` is (EC: `proc; inline*; sp; if; auto; call hp;
auto`). -/
theorem OPC_DPSome_f_ll (P : DPRIMITIVE)
    (hP : (Indifferentiability.DPRIMITIVE.f (block × capacity) (List Bool × ℤ) (List Bool)
      P).procedure.IsLossless) :
    (OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
      (Module.app OPC (Module.app DPSome P))).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hP ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_inline 0
  phoare_wp 5
  phoare_simp [hP]
  phoare_skip
  simp

/-- `OPC(DPSome(P)).fi` is lossless when `P.fi` is. -/
theorem OPC_DPSome_fi_ll (P : DPRIMITIVE)
    (hP : (Indifferentiability.DPRIMITIVE.fi (block × capacity) (List Bool × ℤ) (List Bool)
      P).procedure.IsLossless) :
    (OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
      (Module.app OPC (Module.app DPSome P))).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hP ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_inline 0
  phoare_wp 5
  phoare_simp [hP]
  phoare_skip
  simp

/-- `OFC(DFSome(F)).f` is lossless when `F.f` is (EC: `proc; inline*; sp; if; auto; call hf;
auto`). -/
theorem OFC_DFSome_f_ll (F : DFUNCTIONALITY)
    (hF : (Indifferentiability.DFUNCTIONALITY.f (block × capacity) (List Bool × ℤ) (List Bool)
      F).procedure.IsLossless) :
    (OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
      (Module.app OFC (Module.app DFSome F))).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hF ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_inline 0
  phoare_wp 6
  phoare_simp [hF]
  phoare_skip
  simp

/-- EC's `SHA3OIndiff (Dist <: ODISTINGUISHER {…}) &m`, whose hypothesis that `Dist` is lossless
for lossless oracles puts no restriction on the oracles; with `OGext0Fresh Dist` (exception E13).
EC: `move=>h; have->: Pr[OGReal(…)] = Pr[RealIndif(Sponge, Perm, DRestr(OD(Dist)))] (byequiv:
`real_equiv`); have->: Pr[OGIdeal(…)] = Pr[IdealIndif(IRO, Simulator, DRestr(OD(Dist)))]
(`ideal_equiv`); apply (security (OD(Dist)) _ &m)`, `OD(Dist)` lossless by `h`. -/
theorem SHA3OIndiff (Dist : ODISTINGUISHER) (hD : Module.ECModule Dist distExt)
    (_hDd : ODistRestrictions Dist) (_hG : OGext0Fresh Dist) (m : VariableAssignment) :
    (∀ (F : ODFUNCTIONALITY) (P : ODPRIMITIVE),
      (OptionIndifferentiability.ODPRIMITIVE.f state (List Bool × ℤ) (List Bool)
        P).procedure.IsLossless →
      (OptionIndifferentiability.ODPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
        P).procedure.IsLossless →
      (OptionIndifferentiability.ODFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
        F).procedure.IsLossless →
      (Module.app Dist (Module.pair F P)).procedure.IsLossless) →
    |(Procedure.Pr (OGReal (CSome Sponge.Sponge) (PSome Perm) (ODRestr Dist)).procedure () m
        (fun r _ => r = true) : ℝ) -
      (Procedure.Pr (OGIdeal (Module.app FSome BIRO.IRO.asF) OSimulator (ODRestr Dist)).procedure
        () m (fun r _ => r = true) : ℝ)| ≤ bound := by
  intro h
  unfold ODistRestrictions at _hDd
  have hDR : FVP.fvP Dist ≤ DistRestrictions.footprintᶜ :=
    _hDd.trans (Footprint.compl_antimono (le_sup_left.trans le_sup_left))
  have hDC : FVP.fvP Dist ≤ Counter.c.footprintᶜ :=
    _hDd.trans (Footprint.compl_antimono (le_sup_right.trans le_sup_left))
  have hDCntr : FVP.fvP Dist ≤ Cntr.c.footprintᶜ :=
    hDR.trans (Footprint.compl_antimono (by unfold DistRestrictions.footprint; fp_sub))
  have hDc : FVP.fvP Dist ≤ (ocL.footprint)ᶜ := by
    rw [ocL_footprint]
    exact (Footprint.le_compl_comm _ _).mpr (sup_le ((Footprint.le_compl_comm _ _).mp hDC)
      ((Footprint.le_compl_comm _ _).mp hDCntr))
  rw [Procedure.Pr_eq_of_prhlProc (a₁ := ()) (a₂ := ()) (real_equiv Dist hD hDc)
      (fun r₁ g₁ r₂ g₂ h => by rw [h]) rfl,
    Procedure.Pr_eq_of_prhlProc (a₁ := ()) (a₂ := ()) (ideal_equiv Dist hD hDc)
      (fun r₁ g₁ r₂ g₂ h => by rw [h]) rfl]
  have hODd : DistRestrictions (OD Dist) :=
    (fvP_OD Dist).trans (sup_le hDR Counter_DistRestrictions)
  have hODg : Gext0Fresh (OD Dist) := by
    unfold Gext0Fresh
    unfold OGext0Fresh at _hG
    exact (fvP_OD Dist).trans (sup_le _hG (by fp_disjoint))
  have hll : Dist_lossless (OD Dist) := by
    intro F P _ _ pll pill fll
    have hll := h (OptionIndifferentiability.ODFUNCTIONALITY.mk state (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OFUNCTIONALITY.f state (List Bool × ℤ) (List Bool)
            (Module.app OFC (Module.app DFSome F)) })
      (OptionIndifferentiability.ODPRIMITIVE.mk state (List Bool × ℤ) (List Bool)
        { f := OptionIndifferentiability.OPRIMITIVE.f state (List Bool × ℤ) (List Bool)
            (Module.app OPC (Module.app DPSome P))
          fi := OptionIndifferentiability.OPRIMITIVE.fi state (List Bool × ℤ) (List Bool)
            (Module.app OPC (Module.app DPSome P)) })
      (by simpa only [OptionIndifferentiability.ODPRIMITIVE.f.mk_simp] using
        OPC_DPSome_f_ll P pll)
      (by simpa only [OptionIndifferentiability.ODPRIMITIVE.fi.mk_simp] using
        OPC_DPSome_fi_ll P pill)
      (by simpa only [OptionIndifferentiability.ODFUNCTIONALITY.f.mk_simp] using
        OFC_DFSome_f_ll F fll)
    rw [Procedure.isLossless_iff_phoareProc] at hll ⊢
    phoare_proc_to_stmt
    phoare_inline 0
    phoare_inline 0
    phoare_wp 5
    phoare_simp [hll]
    phoare_skip
    simp
  exact security (OD Dist)
    ⟨Distinguisher_representable _, (hD.finitelySupported.sup
      (Footprint.FinitelySupported.globalVar _)).mono (fvP_OD Dist)⟩ hODd hODg hll m

end

end GaudisCrypt.SHA3.SHA3_OIndiff
