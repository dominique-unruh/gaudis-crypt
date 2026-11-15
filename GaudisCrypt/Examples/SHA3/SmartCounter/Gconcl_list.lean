import GaudisCrypt.Examples.SHA3.BlockSponge
import GaudisCrypt.Logic.PHoareLossless
import GaudisCrypt.Logic.WritesKeepFrame
import GaudisCrypt.Logic.LoopTransform
import GaudisCrypt.Lib.EC.DexceptedSupport

/-!
# From the squeezeless sponge to the block sponge (EasyCrypt `proof/smart_counter/Gconcl_list.ec`)

`Real_Ideal`: the block sponge on the ideal permutation is indifferentiable from the infinite
random oracle `BIRO.IRO`, with the simulator `Simulator`, up to the bound of `Gconcl.Real_Ideal`.

Translation notes (see `notes/SHA3/README.md` and `Exceptions.md`):
* `op valid = valid_block` (as a test) and the axioms on `parse` and `format` are the parameter
  class `Params` (over `BlockSponge.Params`).
* Both `SLCommon` and `BlockSponge` define `C`, `DRestr`, `DISTINGUISHER` …; as in EasyCrypt (where
  `BlockSponge` is imported last), the unqualified names are `BlockSponge`'s, and `SLCommon`'s are
  written `SLCommon.X`.
* The clones `BIRO2` (of `IRO`), `F2` (of `SLCommon`'s `F`) declare their own module variables;
  the section's local `IRO2` (of `PROM.FullRO`) has its variable as a lens parameter of the local
  declarations, fresh by hypothesis (exception E6).
* `SLCommon`'s and `BlockSponge`'s `PRIMITIVE`/`DPRIMITIVE` are one module type in EasyCrypt (they
  depend on `state` only); in Lean their instances differ, so a module passing one as the other
  repackages it with `mk` (`A`'s `P`).
* Local modules that alias a procedure of an applied functor (`L`, `L2`, `L3`, `L4`, `D2`, `D3`,
  `D5`, `D6`) are Lean functions returning that procedure.  `SimLast` and `DValid` are used as
  functors: their aliased procedures are wrapped in a call (exception E5); so is `S2`
  (`S(Last(F))`, whose `PRIMITIVE` is `SLCommon`'s).
-/

namespace GaudisCrypt.SHA3.Gconcl_list

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.Handle
open GaudisCrypt.SHA3.BlockSponge (format parse formatK parseK parse_nil Last Sponge)

export GaudisCrypt.SHA3.SLCommon (state max_size)
export GaudisCrypt.SHA3.BlockSponge (PRIMITIVE DPRIMITIVE FUNCTIONALITY DFUNCTIONALITY
  CONSTRUCTION SIMULATOR DISTINGUISHER C FC PC DRestr RealIndif IdealIndif distExt)

variable [SLCommon.Params] [BlockSponge.Params]

/-! ## Theory parameters: validity of functionality queries -/

/-- `op valid : block list -> bool = valid_block`. -/
def valid (p : List block) : Bool := decide (valid_block p)

/-- EasyCrypt's axioms on `valid`, `parse` and `format`. -/
class Params where
  valid_spec : ∀ p, valid p = true → p ≠ []
  parse_gt0 : ∀ x, 0 < (parse x).2
  parse_not_valid : ∀ x, valid (parse x).1 = false →
    ∀ i, valid (parse (format (parse x).1 i)).1 = false
  parse_twice : ∀ p n x, (p, n) = parse x → ∀ i, 0 < i ∧ i ≤ n → parse (format p i) = (p, i)
  valid_uniq : ∀ p1 p2 n1 n2, valid p1 = true → valid p2 = true →
    format p1 n1 = format p2 n2 → p1 = p2 ∧ n1 = n2

variable [Params]

theorem valid_spec (p : List block) : valid p = true → p ≠ [] := Params.valid_spec p
theorem parse_gt0 (x : List block) : 0 < (parse x).2 := Params.parse_gt0 x
theorem parse_not_valid (x : List block) : valid (parse x).1 = false →
    ∀ i, valid (parse (format (parse x).1 i)).1 = false := Params.parse_not_valid x
theorem parse_twice (p : List block) (n : ℤ) (x : List block) :
    (p, n) = parse x → ∀ i, 0 < i ∧ i ≤ n → parse (format p i) = (p, i) :=
  Params.parse_twice p n x

/-! ## The squeezing functionality and the distinguisher's adapter -/

module DSqueeze using (F : SLCommon.DFUNCTIONALITY) : FUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (x : List block × ℤ) : (List block) {
    var p : List block, n : ℤ, lres : List block, b : block, i : ℤ;
    p, n <- $x;
    lres <- [];
    b <- b0;
    i <- 0;
    if (valid $p) {
      b <- call F.f ($p);
      while ($i < $n) {
        i <- $i + 1;
        lres <- rcons $lres $b;
        if ($i < $n) {
          b <- call F.f (format $p ($i + 1));
        }
      }
    }
    return $lres
  };
}

-- `Squeeze.init`, the procedure of `Squeeze` that is not `DSqueeze`'s
module Squeeze.init_ using (F : SLCommon.FUNCTIONALITY) {
  proc init () : Unit {
    _ <- call BlockSponge.C.init ();
    _ <- call F.init ();
    return ()
  };
}

/-- EC's `Squeeze(F : SLCommon.FUNCTIONALITY) : FUNCTIONALITY`: `proc init`, and
`proc f = DSqueeze(F).f`. -/
noncomputable def Squeeze (F : SLCommon.FUNCTIONALITY) : FUNCTIONALITY :=
  Indifferentiability.FUNCTIONALITY.mk state (List block × ℤ) (List block)
    { init := Module.app GaudisCrypt.SHA3.Gconcl_list.Squeeze.init_ F
      f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app DSqueeze (Indifferentiability.FUNCTIONALITY.view state (List block) block F)) }

-- EC's `A(D : DISTINGUISHER) : SLCommon.DISTINGUISHER`, with `D` a Lean parameter; `P` is
-- `SLCommon`'s `DPRIMITIVE`, repackaged as `BlockSponge`'s for `D` (one module type in EasyCrypt)
set_option linter.gaudisCrypt.using false in
module A (D : DISTINGUISHER) using (F : SLCommon.DFUNCTIONALITY, P : SLCommon.DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call BlockSponge.C.init ();
    b <- call (Module.app (DRestr D) (Module.pair
      (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
            (Module.app DSqueeze F) })
      (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.DPRIMITIVE.f state (List block) block P
          fi := Indifferentiability.DPRIMITIVE.fi state (List block) block P }))) ();
    return $b
  };
}

module NIndif using (F : FUNCTIONALITY, P : PRIMITIVE, D : DISTINGUISHER) {
  proc main () : Bool {
    var b : Bool;
    _ <- call BlockSponge.C.init ();
    _ <- call P.init ();
    _ <- call F.init ();
    b <- call (Module.app D (Module.pair
      (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block) F })
      (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P
          fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block) P }))) ();
    return $b
  };
}

/-- `module P = Perm`. -/
noncomputable abbrev P : PRIMITIVE := Perm

/-! `clone IRO as BIRO2 with type from <- block list, type to <- block, op valid <- predT,
op dto <- bdistr` -/

namespace BIRO2
/-- The clone's module variable `BIRO2.IRO.mp`. -/
global_var IRO.mp : FMap (List block × ℤ) block
noncomputable abbrev IRO := IRO.IRO block (List block) (fun _ => true) bdistr IRO.mp
noncomputable abbrev IRO.init :=
  GaudisCrypt.SHA3.IRO.IRO.init block (List block) (fun _ => true) bdistr IRO.mp
noncomputable abbrev IRO.f :=
  GaudisCrypt.SHA3.IRO.IRO.f block (List block) (fun _ => true) bdistr IRO.mp
end BIRO2

module Valid using (F : DFUNCTIONALITY) : FUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (x : List block × ℤ) : (List block) {
    var q : List block, k : ℤ, re : List block;
    q, k <- $x;
    re <- [];
    q, k <- parse (format $q $k);
    if (valid $q) {
      re <- call F.f (($q, $k));
    } else {
      re <- call BIRO2.IRO.f (($q, $k));
    }
    return $re
  };
}

-- EC's `SimLast(S : SLCommon.SIMULATOR)(F : DFUNCTIONALITY)`, with `S` a Lean parameter; its
-- aliases `proc f = S(Last(Valid(F))).f` and `proc fi = …` are wrapped in a call (exception E5)
set_option linter.gaudisCrypt.using false in
module SimLast (S : SLCommon.SIMULATOR) using (F : DFUNCTIONALITY) : PRIMITIVE {
  proc init () : Unit {
    _ <- call BIRO2.IRO.init ();
    _ <- call (Indifferentiability.PRIMITIVE.init state (List block) block
      (Module.app S (Module.app Last (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ)
        (List block) (Module.app Valid F))))) ();
    return ()
  };
  proc f (x : state) : state {
    var y : state;
    y <- call (Indifferentiability.PRIMITIVE.f state (List block) block
      (Module.app S (Module.app Last (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ)
        (List block) (Module.app Valid F))))) ($x);
    return $y
  };
  proc fi (x : state) : state {
    var y : state;
    y <- call (Indifferentiability.PRIMITIVE.fi state (List block) block
      (Module.app S (Module.app Last (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ)
        (List block) (Module.app Valid F))))) ($x);
    return $y
  };
}

/-! `clone F as F2`: a second random oracle `block list -> block`, with its own variables -/

namespace F2
noncomputable abbrev dout : List block → SubProbability block := fun _ => bdistr
/-- The clone's module variable `F2.RO.m`. -/
global_var RO.m : FMap (List block) block
/-- The clone's module variable `F2.FRO.m`. -/
global_var FRO.m : FMap (List block) (block × flag)
noncomputable abbrev RO := PROM.FullRO.RO (List block) block dout RO.m
noncomputable abbrev RO.asRO := PROM.FullRO.RO.asRO (List block) block dout RO.m
noncomputable abbrev LRO := PROM.FullRO.LRO (List block) block dout RO.m
noncomputable abbrev FRO := PROM.FullRO.FRO (List block) block dout FRO.m
abbrev RO_T := PROM.FullRO.RO_T (List block) block
end F2

/-! ## The section `Ideal` -/

section Ideal

/-- The section's `op (<=) (m1 m2 : (block list, 'b) fmap)`. -/
def «<=» {β : Type} (m1 m2 : FMap (List block) β) : Prop :=
  ∀ x, x ≠ [] → FMap.dom m1 x → FMap.get m1 x = FMap.get m2 x

theorem leq_add_nin {β : Type} (m1 m2 : FMap (List block) β) (x : List block) (y : β) :
    «<=» m1 m2 → ¬ FMap.dom m2 x → «<=» m1 (FMap.set m2 x y) := by
  intro h hn a ha hd
  rw [FMap.get_setE]
  split_ifs with hax
  · subst hax
    exact absurd ((FMap.domE _ _).mpr (h a ha hd ▸ (FMap.domE _ _).mp hd)) hn
  · exact h a ha hd

theorem leq_add_in {β : Type} [Inhabited β] (m1 m2 : FMap (List block) β) (x : List block) :
    «<=» m1 m2 → FMap.dom m2 x → «<=» (FMap.set m1 x (oget (FMap.get m2 x))) m2 := by
  intro h hx a ha hd
  rw [FMap.get_setE]
  split_ifs with hax
  · subst hax
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hx)
    simp [hv, oget]
  · rcases (FMap.mem_set _ _ _ _).mp hd with hd | hd
    · exact h a ha hd
    · exact absurd hd hax

theorem leq_nin_dom {β : Type} (m1 m2 : FMap (List block) β) (x : List block) :
    «<=» m1 m2 → x ≠ [] → ¬ FMap.dom m2 x → ¬ FMap.dom m1 x := by
  intro h hx hn hd
  exact hn ((FMap.domE _ _).mpr (h x hx hd ▸ (FMap.domE _ _).mp hd))

theorem prefix_leq1 (l : List block) (m : FMap (List block) block) (i : ℤ) :
    0 ≤ i → FMap.dom m (format l (i + 1)) →
    size (format l (i + 1)) ≤ «prefix» (format l (i + 1 + 1))
        (get_max_prefix (format l (i + 1 + 1)) (elems (FMap.fdom m))) ∧
      «prefix» (format l (i + 1 + 1))
        (get_max_prefix (format l (i + 1 + 1)) (elems (FMap.fdom m))) ≤
        size (format l (i + 1 + 1)) := by
  intro hi hd
  have hf : format l (i + 1 + 1) = format l (i + 1) ++ [b0] := by
    simp only [format, nseq, List.append_assoc]
    rw [show (i + 1 + 1 - 1).toNat = (i + 1 - 1).toNat + 1 by omega, List.replicate_succ']
  rw [hf]
  have hm := (mem_elems_fdom m (format l (i + 1))).mpr hd
  have h1 := get_max_prefix_max (format l (i + 1) ++ [b0]) _ _ hm
  have h2 : «prefix» (format l (i + 1) ++ [b0]) (format l (i + 1)) = size (format l (i + 1)) := by
    rw [prefixC]
    have := prefix_cat (format l (i + 1)) [] [b0]
    rw [List.append_nil, prefix0s] at this
    omega
  exact ⟨h2 ▸ h1, prefix_sizel _ _⟩

theorem prefix_le1 (l : List block) (m : FMap (List block) block) (i : ℤ) :
    0 ≤ i → FMap.dom m (format l (i + 1)) →
    size (format l (i + 1 + 1)) - «prefix» (format l (i + 1 + 1))
      (get_max_prefix (format l (i + 1 + 1)) (elems (FMap.fdom m))) ≤ 1 := by
  intro hi hd
  have h := prefix_leq1 l m i hi hd
  have hf : size (format l (i + 1 + 1)) = size (format l (i + 1)) + 1 := by
    simp only [format, nseq, size, List.length_append, List.length_replicate]
    omega
  omega

theorem leq_add2 {β : Type} (m1 m2 : FMap (List block) β) (x : List block) (y : β) :
    «<=» m1 m2 → ¬ FMap.dom m2 x → «<=» (FMap.set m1 x y) (FMap.set m2 x y) := by
  intro h hn a ha hd
  rw [FMap.get_setE, FMap.get_setE]
  split_ifs with hax
  · rfl
  · rcases (FMap.mem_set _ _ _ _).mp hd with hd | hd
    · exact h a ha hd
    · exact absurd hd hax

-- `IF'(F).f`, the procedure of `IF'` that is not `F`'s
module IF'.f_ using (F : SLCommon.F.RO_T) {
  proc f (x : List block) : block {
    var b : block, i : ℤ, p : List block, n : ℤ;
    b <- b0;
    i <- 0;
    p, n <- parse $x;
    while ($i < $n) {
      i <- $i + 1;
      _ <- call F.sample (format $p $i);
    }
    b <- call F.get ($x);
    return $b
  };
}

/-- EC's local `IF'(F : F.RO)`: `proc init = F.init`, and `proc f`. -/
noncomputable def IF' (F : SLCommon.F.RO_T) : SLCommon.FUNCTIONALITY :=
  Indifferentiability.FUNCTIONALITY.mk state (List block) block
    { init := PROM.FullRO.RO_T.init (List block) block F
      f := Module.app GaudisCrypt.SHA3.Gconcl_list.IF'.f_ F }

/-- EC's local `L(D : DISTINGUISHER)(F : F.RO)`: `proc distinguish =
SLCommon.IdealIndif(IF'(F), S, A(D)).main`. -/
noncomputable def L (D : DISTINGUISHER) (F : SLCommon.F.RO_T) : procmod () → Bool :=
  SLCommon.IdealIndif (IF' F) Gconcl.S (A D)

-- `Valid2(F).f`, the procedure of `Valid2` that is not `F`'s
module Valid2.f_ using (F : SLCommon.F.RO_T) {
  proc f (q : List block) : block {
    var r : block, s : List block, t : ℤ;
    r <- b0;
    s, t <- parse $q;
    r <- call F.get ($q);
    return $r
  };
}

/-- EC's local `Valid2(F : F.RO)`: `proc init = F.init`, and `proc f`. -/
noncomputable def Valid2 (F : SLCommon.F.RO_T) : SLCommon.FUNCTIONALITY :=
  Indifferentiability.FUNCTIONALITY.mk state (List block) block
    { init := PROM.FullRO.RO_T.init (List block) block F
      f := Module.app GaudisCrypt.SHA3.Gconcl_list.Valid2.f_ F }

/-- EC's local `L2(D)(F)`: `proc distinguish = SLCommon.IdealIndif(Valid2(F), S, A(D)).main`. -/
noncomputable def L2 (D : DISTINGUISHER) (F : SLCommon.F.RO_T) : procmod () → Bool :=
  SLCommon.IdealIndif (Valid2 F) Gconcl.S (A D)

/-- The section's restriction `{-SLCommon.C, -C, -IF, -S}` (an abbreviation). -/
def DRestrictions_Ideal (D : DISTINGUISHER) : Prop :=
  FVP.fvP D ≤ (SLCommon.C.footprint ⊔ BlockSponge.C.c.footprint ⊔ (SLCommon.F.RO.m).footprint ⊔
    (Gconcl.S.m).footprint ⊔ (Gconcl.S.mi).footprint ⊔ (Gconcl.S.paths).footprint)ᶜ

omit [BlockSponge.Params] [Params] in
/-- `format p 1 = p`. -/
theorem format_one (p : List block) : format p 1 = p := by simp [format, nseq]

omit [BlockSponge.Params] [Params] in
theorem get_eq_some_oget {m : FMap (List block) block} {x : List block} (h : FMap.dom m x) :
    FMap.get m x = some (oget (FMap.get m x)) := by
  rw [FMap.domE] at h
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
  rw [hv]; rfl

omit [BlockSponge.Params] [Params] in
/-- `bdistr` is lossless, as an expectation. -/
theorem bdistr_expected_one : bdistr.expected (fun _ => (1 : ENNReal)) = 1 :=
  (is_lossless_iff_expected bdistr).mp BitWord.dunifin_ll

omit [BlockSponge.Params] [Params] in
theorem format_ne_nil {p : List block} (hp : p ≠ []) (k : ℤ) : format p k ≠ [] := by
  simp [format, hp]

inductive inv_L_L3 (m1 m2 m3 : FMap (List block) block) : Prop where
  | INV :
      m1 = FMap.add m2 m3 → (∀ l, FMap.dom m2 l → valid (parse l).1 = true) →
      (∀ l, FMap.dom m3 l → valid (parse l).1 = false) → inv_L_L3 m1 m2 m3

module IF2 using (F : SLCommon.F.RO_T, F2 : F2.RO_T) : SLCommon.FUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    _ <- call F2.init ();
    return ()
  };
  proc f (x : List block) : block {
    var b : block, i : ℤ, p : List block, n : ℤ;
    b <- b0;
    i <- 0;
    p, n <- parse $x;
    if (valid $p) {
      while ($i < $n) {
        i <- $i + 1;
        _ <- call F.sample (format $p $i);
      }
      b <- call F.get ($x);
    } else {
      while ($i < $n) {
        i <- $i + 1;
        _ <- call F2.sample (format $p $i);
      }
      b <- call F2.get ($x);
    }
    return $b
  };
}

theorem lemma1 (m1 m2 m3 : FMap (List block) block) (p : List block) (i : ℤ) (r : block) :
    inv_L_L3 m1 m2 m3 → valid p = true → 0 < i → ¬ FMap.dom m1 (format p i) →
    ¬ FMap.dom m2 (format p i) →
    inv_L_L3 (FMap.set m1 (format p i) r) (FMap.set m2 (format p i) r) m3 := by
  rintro ⟨rfl, h2, h3⟩ hp hi hn1 hn2
  have hpk : parse (format p i) = (p, i) := parseK p i hi (by simpa [valid] using hp)
  have hget : ∀ (a b : FMap (List block) block) y,
      FMap.get (FMap.add a b) y = if FMap.dom b y then FMap.get b y else FMap.get a y := by
    intro a b y
    unfold FMap.add FMap.get FMap.dom
    split_ifs with h
    · exact Finmap.lookup_union_left (Finmap.mem_keys.mp h)
    · exact Finmap.lookup_union_right (mt Finmap.mem_keys.mpr h)
  have hdom : ∀ (a b : FMap (List block) block) y,
      FMap.dom (FMap.add a b) y ↔ FMap.dom a y ∨ FMap.dom b y := by
    intro a b y
    simp only [FMap.dom, FMap.add, Finmap.mem_keys, Finmap.mem_union, or_comm]
  have hn3 : ¬ FMap.dom m3 (format p i) := fun h => hn1 ((hdom _ _ _).mpr (Or.inr h))
  refine ⟨?_, ?_, h3⟩
  · refine (FMap.fmap_eqP _ _).mp fun y => ?_
    rw [FMap.get_setE, hget, hget, FMap.get_setE]
    by_cases hy : y = format p i
    · subst hy; simp [hn3]
    · simp [hy]
  · intro l hl
    rcases (FMap.mem_set _ _ _ _).mp hl with hl | rfl
    · exact h2 l hl
    · rw [hpk]; exact hp

theorem lemma2 (m1 m2 m3 : FMap (List block) block) (p : List block) (i : ℤ) :
    inv_L_L3 m1 m2 m3 → valid p = true → 0 < i → FMap.dom m1 (format p i) →
    FMap.dom m2 (format p i) := by
  rintro ⟨rfl, -, h3⟩ hp hi hd
  have hpk : parse (format p i) = (p, i) := parseK p i hi (by simpa [valid] using hp)
  have hd' : FMap.dom m2 (format p i) ∨ FMap.dom m3 (format p i) := by
    simpa only [FMap.dom, FMap.add, Finmap.mem_keys, Finmap.mem_union, or_comm] using hd
  rcases hd' with hd' | hd'
  · exact hd'
  · have := h3 _ hd'
    rw [hpk] at this
    simp [hp] at this

theorem incl_dom (m1 m2 m3 : FMap (List block) block) (l : List block) :
    inv_L_L3 m1 m2 m3 → (FMap.dom m1 l ↔ FMap.dom m2 l ∨ FMap.dom m3 l) := by
  rintro ⟨rfl, -, -⟩
  simp only [FMap.dom, FMap.add, Finmap.mem_keys, Finmap.mem_union, or_comm]

theorem lemma3 (m1 m2 m3 : FMap (List block) block) (x : List block) (r : block) :
    inv_L_L3 m1 m2 m3 → valid (parse x).1 = false → ¬ FMap.dom m1 x →
    inv_L_L3 (FMap.set m1 x r) m2 (FMap.set m3 x r) := by
  rintro ⟨rfl, h2, h3⟩ hv hn1
  have hget : ∀ (a b : FMap (List block) block) y,
      FMap.get (FMap.add a b) y = if FMap.dom b y then FMap.get b y else FMap.get a y := by
    intro a b y
    unfold FMap.add FMap.get FMap.dom
    split_ifs with h
    · exact Finmap.lookup_union_left (Finmap.mem_keys.mp h)
    · exact Finmap.lookup_union_right (mt Finmap.mem_keys.mpr h)
  refine ⟨?_, h2, ?_⟩
  · refine (FMap.fmap_eqP _ _).mp fun y => ?_
    rw [FMap.get_setE, hget, hget, FMap.get_setE]
    by_cases hy : y = x
    · subst hy; simp [FMap.mem_set]
    · simp [hy, FMap.mem_set]
  · intro l hl
    rcases (FMap.mem_set _ _ _ _).mp hl with hl | rfl
    · exact h3 l hl
    · exact hv

omit [BlockSponge.Params] [Params] in
/-- The entries of `FMap.add a b`: `b`'s first. -/
theorem add_get (a b : FMap (List block) block) (y : List block) :
    FMap.get (FMap.add a b) y = if FMap.dom b y then FMap.get b y else FMap.get a y := by
  unfold FMap.add FMap.get FMap.dom
  split_ifs with h
  · exact Finmap.lookup_union_left (Finmap.mem_keys.mp h)
  · exact Finmap.lookup_union_right (mt Finmap.mem_keys.mpr h)

omit [BlockSponge.Params] [Params] in
/-- The domain of `FMap.add a b`. -/
theorem add_dom (a b : FMap (List block) block) (y : List block) :
    FMap.dom (FMap.add a b) y ↔ FMap.dom a y ∨ FMap.dom b y := by
  simp only [FMap.dom, FMap.add, Finmap.mem_keys, Finmap.mem_union, or_comm]

namespace inv_L_L3

variable {m1 m2 m3 : FMap (List block) block} {x : List block}

omit [Params]

theorem dom_valid (h : inv_L_L3 m1 m2 m3) (hv : valid (parse x).1 = true) :
    FMap.dom m1 x ↔ FMap.dom m2 x := by
  obtain ⟨rfl, -, h3⟩ := h
  rw [add_dom]
  exact ⟨fun hd => hd.resolve_right fun hd3 => by have := h3 x hd3; simp [hv] at this, Or.inl⟩

theorem get_valid (h : inv_L_L3 m1 m2 m3) (hv : valid (parse x).1 = true) :
    FMap.get m1 x = FMap.get m2 x := by
  obtain ⟨rfl, -, h3⟩ := h
  rw [add_get, if_neg fun hd3 => by have := h3 x hd3; simp [hv] at this]

theorem dom_invalid (h : inv_L_L3 m1 m2 m3) (hv : valid (parse x).1 = false) :
    FMap.dom m1 x ↔ FMap.dom m3 x := by
  obtain ⟨rfl, h2, -⟩ := h
  rw [add_dom]
  exact ⟨fun hd => hd.resolve_left fun hd2 => by have := h2 x hd2; simp [hv] at this, Or.inr⟩

theorem get_invalid (h : inv_L_L3 m1 m2 m3) (hv : valid (parse x).1 = false) :
    FMap.get m1 x = FMap.get m3 x := by
  obtain ⟨rfl, h2, -⟩ := h
  rw [add_get]
  split_ifs with hd3
  · rfl
  · have : ¬ FMap.dom m2 x := fun hd2 => by have := h2 x hd2; simp [hv] at this
    rw [FMap.domE, not_not] at this hd3
    rw [this, hd3]

theorem set_valid (h : inv_L_L3 m1 m2 m3) (hv : valid (parse x).1 = true) (r : block) :
    inv_L_L3 (FMap.set m1 x r) (FMap.set m2 x r) m3 := by
  obtain ⟨rfl, h2, h3⟩ := h
  have hn3 : ¬ FMap.dom m3 x := fun hd3 => by have := h3 x hd3; simp [hv] at this
  refine ⟨?_, ?_, h3⟩
  · refine (FMap.fmap_eqP _ _).mp fun y => ?_
    rw [FMap.get_setE, add_get, add_get, FMap.get_setE]
    by_cases hy : y = x
    · subst hy; simp [hn3]
    · simp [hy]
  · intro l hl
    rcases (FMap.mem_set _ _ _ _).mp hl with hl | rfl
    · exact h2 l hl
    · exact hv

end inv_L_L3

omit [Params] in
/-- The invariant holds of the empty maps (`F.RO.init`, `F2.RO.init`). -/
theorem inv_L_L3_empty : inv_L_L3 FMap.empty FMap.empty FMap.empty := by
  refine ⟨(FMap.fmap_eqP _ _).mp fun y => ?_, fun l h => absurd h (FMap.mem_empty _),
    fun l h => absurd h (FMap.mem_empty _)⟩
  rw [add_get, if_neg (FMap.mem_empty _)]

/-- The call of EC's local `D2(D)(F)`:
`D(FC(DSqueeze(Valid2(F))), PC(S(Valid2(F)))).distinguish`, its oracles in the form inlining `L2`
leaves them in (`view`s and `Valid2` unfolded). -/
noncomputable abbrev D2o (D : DISTINGUISHER) (F : SLCommon.F.RO_T) : procmod () → Bool :=
  (Module.app D (Module.pair
  (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
    { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ)
          (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app DSqueeze (Indifferentiability.DFUNCTIONALITY.mk state
                (List block) block { f := Module.app Valid2.f_ F })) })) })
  (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
    { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.PRIMITIVE.f state (List block) block
              (Module.app Gconcl.S (Indifferentiability.DFUNCTIONALITY.mk state
                (List block) block { f := Module.app Valid2.f_ F }))
            fi := Indifferentiability.PRIMITIVE.fi state (List block) block
              (Module.app Gconcl.S (Indifferentiability.DFUNCTIONALITY.mk state
                (List block) block { f := Module.app Valid2.f_ F })) }))
      fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.PRIMITIVE.f state (List block) block
              (Module.app Gconcl.S (Indifferentiability.DFUNCTIONALITY.mk state
                (List block) block { f := Module.app Valid2.f_ F }))
            fi := Indifferentiability.PRIMITIVE.fi state (List block) block
              (Module.app Gconcl.S (Indifferentiability.DFUNCTIONALITY.mk state
                (List block) block { f := Module.app Valid2.f_ F })) })) })))

set_option maxHeartbeats 4000000 in
-- the module command's equation for the large body
-- EC's local `D2(D)(F : F.RO)`, with `D` a Lean parameter so that `D2 D` is an
-- `F.RO_Distinguisher` (for `RO_LRO_D`); its `distinguish` calls `D2o` (exception E5) and takes
-- EasyCrypt's `d_in_t = unit`
set_option linter.gaudisCrypt.using false in
module D2 (D : DISTINGUISHER) using (F : SLCommon.F.RO_T) {
  proc distinguish (_u : Unit) : Bool {
    var b : Bool;
    b <- call (D2o D F) ();
    return $b
  };
}

/-- `D2o D F` is `D2(D)(F).distinguish` (the wrapper's call). -/
theorem D2o_D2 (D : DISTINGUISHER) (F : SLCommon.F.RO_T) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂) (D2o D F).procedure (Module.app (D2 D) F).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  equiv_proc_to_stmt
  stmt_inline{2} 0
  stmt_wp
  equiv_call (prhlProc_refl _)
  stmt_wp
  equiv_skip
  intro g₁ g₂ h
  exact ⟨h, fun _ _ _ _ h => h⟩

/-- `D2(D)(F).distinguish` is `D2o D F`. -/
theorem D2_D2o (D : DISTINGUISHER) (F : SLCommon.F.RO_T) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂) (Module.app (D2 D) F).procedure (D2o D F).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_wp
  equiv_call (prhlProc_refl _)
  stmt_wp
  equiv_skip
  intro g₁ g₂ h
  exact ⟨h, fun _ _ _ _ h => h⟩

set_option maxHeartbeats 4000000 in
-- `within_lens` through the oracles
omit [Params] in
/-- `D2 D` touches `glob D`, `C.c` and `S`'s variables (and its oracle's).  Not an EC lemma. -/
theorem fvP_D2 (D : DISTINGUISHER) :
    FVP.fvP (D2 D) ≤ FVP.fvP D ⊔ (Lens.pair BlockSponge.C.c (Lens.pair Gconcl.S.m
      (Lens.pair Gconcl.S.mi Gconcl.S.paths))).footprint := by
  fp_module (Lens.pair BlockSponge.C.c (Lens.pair Gconcl.S.m
      (Lens.pair Gconcl.S.mi Gconcl.S.paths)))

set_option maxHeartbeats 4000000 in
-- inlining `L2`
/-- `L2(D, F.RO) ~ L2(D, F.LRO)` (EC: `proc; sp; inline*; sp; wp; call (F.FullEager.RO_LRO_D
(D2(D)) _)`). -/
theorem L2_RO_LRO (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal D)
    (_hDd' : FVP.fvP D ≤ ((SLCommon.F.FRO.m).footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (L2 D SLCommon.F.RO.asRO).procedure (L2 D SLCommon.F.LRO).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hX : (Lens.pair BlockSponge.C.c (Lens.pair Gconcl.S.m
      (Lens.pair Gconcl.S.mi Gconcl.S.paths))).footprint.FinitelySupported := by
    simp only [Footprint.lens_pair]
    repeat (first | exact .varLens _ | refine .sup ?_ ?_)
  have hmod := PROM.FullRO.RO_Distinguisher.ecModule (List block) block Unit Bool (D2 D)
    ((hD.finitelySupported.sup hX).mono (fvP_D2 D))
  unfold DRestrictions_Ideal at _hDd
  have hdisj : FVP.fvP (D2 D) ≤ ((SLCommon.F.RO.m).footprint ⊔ (SLCommon.F.FRO.m).footprint)ᶜ := by
    refine (fvP_D2 D).trans ((Footprint.le_compl_comm _ _).mp (sup_le ?_ ?_))
    · refine (Footprint.le_compl_comm _ _).mp (sup_le ?_ ?_)
      · exact _hDd.trans (Footprint.compl_antimono (by fp_sub))
      · simp only [Footprint.lens_pair]
        fp_disjoint
    · refine (Footprint.le_compl_comm _ _).mp (sup_le _hDd' ?_)
      simp only [Footprint.lens_pair]
      fp_disjoint
  have hRO := PROM.FullRO.FullEager.RO_LRO_D (List block) block Unit Bool SLCommon.F.dout
    SLCommon.F.FRO.m (fun _ => BitWord.dunifin_ll) SLCommon.F.RO.m (D2 D) hmod hdisj
  have h := prhlProc_conseq (prhlProc.trans (D2o_D2 D SLCommon.F.RO.asRO)
      (prhlProc.trans hRO (D2_D2o D SLCommon.F.LRO)))
    (A := fun _ g₁ _ g₂ => g₁ = g₂) (B := fun r₁ _ r₂ _ => r₁ = r₂)
    (fun a₁ g₁ a₃ g₃ h => ⟨(), g₁, rfl, (), g₃, ⟨rfl, by rw [h], by rw [h]⟩, rfl⟩)
    (fun r₁ g₁ r₃ g₃ ⟨r₂, g₂, ⟨h1, _⟩, r₂', g₂', ⟨h2, _⟩, h3, _⟩ => h1.trans (h2.trans h3))
  unfold L2 SLCommon.IdealIndif Indifferentiability.GIdeal
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp,
    Indifferentiability.FUNCTIONALITY.view, Valid2, Indifferentiability.FUNCTIONALITY.f.mk_simp]
  stmt_wp
  equiv_call h
  stmt_wp
  equiv_skip
  intro g₁ g₂ h
  subst h
  exact ⟨rfl, fun _ _ _ _ h => h⟩

/-- The call of EC's local `D3(D)(F)`: `D(FC(DSqueeze(IF'(F))), PC(S(IF'(F)))).distinguish` (as
`D2o`). -/
noncomputable abbrev D3o (D : DISTINGUISHER) (F : SLCommon.F.RO_T) : procmod () → Bool :=
  (Module.app D (Module.pair
  (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
    { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ)
          (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app DSqueeze (Indifferentiability.DFUNCTIONALITY.mk state
                (List block) block { f := Module.app IF'.f_ F })) })) })
  (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
    { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.PRIMITIVE.f state (List block) block
              (Module.app Gconcl.S (Indifferentiability.DFUNCTIONALITY.mk state
                (List block) block { f := Module.app IF'.f_ F }))
            fi := Indifferentiability.PRIMITIVE.fi state (List block) block
              (Module.app Gconcl.S (Indifferentiability.DFUNCTIONALITY.mk state
                (List block) block { f := Module.app IF'.f_ F })) }))
      fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.PRIMITIVE.f state (List block) block
              (Module.app Gconcl.S (Indifferentiability.DFUNCTIONALITY.mk state
                (List block) block { f := Module.app IF'.f_ F }))
            fi := Indifferentiability.PRIMITIVE.fi state (List block) block
              (Module.app Gconcl.S (Indifferentiability.DFUNCTIONALITY.mk state
                (List block) block { f := Module.app IF'.f_ F })) })) })))

set_option maxHeartbeats 4000000 in
-- the module command's equation for the large body
-- EC's local `D3(D)(F : F.RO)` (as `D2`)
set_option linter.gaudisCrypt.using false in
module D3 (D : DISTINGUISHER) using (F : SLCommon.F.RO_T) {
  proc distinguish (_u : Unit) : Bool {
    var b : Bool;
    b <- call (D3o D F) ();
    return $b
  };
}

/-- `D3o D F` is `D3(D)(F).distinguish` (the wrapper's call). -/
theorem D3o_D3 (D : DISTINGUISHER) (F : SLCommon.F.RO_T) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂) (D3o D F).procedure (Module.app (D3 D) F).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  equiv_proc_to_stmt
  stmt_inline{2} 0
  stmt_wp
  equiv_call (prhlProc_refl _)
  stmt_wp
  equiv_skip
  intro g₁ g₂ h
  exact ⟨h, fun _ _ _ _ h => h⟩

/-- `D3(D)(F).distinguish` is `D3o D F`. -/
theorem D3_D3o (D : DISTINGUISHER) (F : SLCommon.F.RO_T) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂) (Module.app (D3 D) F).procedure (D3o D F).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_wp
  equiv_call (prhlProc_refl _)
  stmt_wp
  equiv_skip
  intro g₁ g₂ h
  exact ⟨h, fun _ _ _ _ h => h⟩

set_option maxHeartbeats 4000000 in
-- `within_lens` through the oracles
omit [Params] in
/-- `D3 D` touches `glob D`, `C.c` and `S`'s variables (and its oracle's).  Not an EC lemma. -/
theorem fvP_D3 (D : DISTINGUISHER) :
    FVP.fvP (D3 D) ≤ FVP.fvP D ⊔ (Lens.pair BlockSponge.C.c (Lens.pair Gconcl.S.m
      (Lens.pair Gconcl.S.mi Gconcl.S.paths))).footprint := by
  fp_module (Lens.pair BlockSponge.C.c (Lens.pair Gconcl.S.m
      (Lens.pair Gconcl.S.mi Gconcl.S.paths)))

set_option maxHeartbeats 4000000 in
-- inlining `L`
/-- `L(D, F.RO) ~ L(D, F.LRO)` (EC: `call (F.FullEager.RO_LRO_D (D3(D)) _)`). -/
theorem L_RO_LRO (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal D)
    (_hDd' : FVP.fvP D ≤ ((SLCommon.F.FRO.m).footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (L D SLCommon.F.RO.asRO).procedure (L D SLCommon.F.LRO).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hX : (Lens.pair BlockSponge.C.c (Lens.pair Gconcl.S.m
      (Lens.pair Gconcl.S.mi Gconcl.S.paths))).footprint.FinitelySupported := by
    simp only [Footprint.lens_pair]
    repeat (first | exact .varLens _ | refine .sup ?_ ?_)
  have hmod := PROM.FullRO.RO_Distinguisher.ecModule (List block) block Unit Bool (D3 D)
    ((hD.finitelySupported.sup hX).mono (fvP_D3 D))
  unfold DRestrictions_Ideal at _hDd
  have hdisj : FVP.fvP (D3 D) ≤ ((SLCommon.F.RO.m).footprint ⊔ (SLCommon.F.FRO.m).footprint)ᶜ := by
    refine (fvP_D3 D).trans ((Footprint.le_compl_comm _ _).mp (sup_le ?_ ?_))
    · refine (Footprint.le_compl_comm _ _).mp (sup_le ?_ ?_)
      · exact _hDd.trans (Footprint.compl_antimono (by fp_sub))
      · simp only [Footprint.lens_pair]
        fp_disjoint
    · refine (Footprint.le_compl_comm _ _).mp (sup_le _hDd' ?_)
      simp only [Footprint.lens_pair]
      fp_disjoint
  have hRO := PROM.FullRO.FullEager.RO_LRO_D (List block) block Unit Bool SLCommon.F.dout
    SLCommon.F.FRO.m (fun _ => BitWord.dunifin_ll) SLCommon.F.RO.m (D3 D) hmod hdisj
  have h := prhlProc_conseq (prhlProc.trans (D3o_D3 D SLCommon.F.RO.asRO)
      (prhlProc.trans hRO (D3_D3o D SLCommon.F.LRO)))
    (A := fun _ g₁ _ g₂ => g₁ = g₂) (B := fun r₁ _ r₂ _ => r₁ = r₂)
    (fun a₁ g₁ a₃ g₃ h => ⟨(), g₁, rfl, (), g₃, ⟨rfl, by rw [h], by rw [h]⟩, rfl⟩)
    (fun r₁ g₁ r₃ g₃ ⟨r₂, g₂, ⟨h1, _⟩, r₂', g₂', ⟨h2, _⟩, h3, _⟩ => h1.trans (h2.trans h3))
  unfold L SLCommon.IdealIndif Indifferentiability.GIdeal
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp,
    Indifferentiability.FUNCTIONALITY.view, IF', Indifferentiability.FUNCTIONALITY.f.mk_simp]
  stmt_wp
  equiv_call h
  stmt_wp
  equiv_skip
  intro g₁ g₂ h
  subst h
  exact ⟨rfl, fun _ _ _ _ h => h⟩

module DSqueeze2 using (F : SLCommon.F.RO_T, F2 : F2.RO_T) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call F.init ();
    _ <- call F2.init ();
    return ()
  };
  proc f (x : List block × ℤ) : (List block) {
    var p : List block, n : ℤ, lres : List block, b : block, i : ℤ, pp : List block, nn : ℤ;
    p, n <- $x;
    lres <- [];
    b <- b0;
    i <- 0;
    pp, nn <- parse (format $p $n);
    if (valid $p) {
      if (decide ($n ≤ 0)) {
        _ <- call F.sample ($p);
      }
      while ($i < $n) {
        i <- $i + 1;
        b <- call F.get (format $p $i);
        lres <- rcons $lres $b;
      }
    } else {
      if (decide ($nn ≤ 0)) {
        _ <- call F2.sample ($pp);
      }
      while ($i < $nn - $n) {
        i <- $i + 1;
        _ <- call F2.sample (format $pp $i);
      }
      while ($i < $n) {
        i <- $i + 1;
        b <- call F2.get (format $pp $i);
        lres <- rcons $lres $b;
      }
    }
    return $lres
  };
}

module FValid using (F : DFUNCTIONALITY) : DFUNCTIONALITY {
  proc f (x : List block × ℤ) : (List block) {
    var p : List block, n : ℤ, r : List block;
    p, n <- $x;
    r <- [];
    if (valid $p) {
      r <- call F.f (($p, $n));
    }
    return $r
  };
}

-- EC's local `DValid(D)(F)(P) = D(FValid(F), P)`, with `D` a Lean parameter; used as a
-- `DISTINGUISHER`, its procedure is a call of `D(FValid(F), P).distinguish` (exception E5)
set_option linter.gaudisCrypt.using false in
module DValid (D : DISTINGUISHER) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    b <- call (Module.app D (Module.pair (Module.app FValid F) P)) ();
    return $b
  };
}

-- EC's local `S2(F) = S(Last(F))`; used as a `SIMULATOR` (`BlockSponge`'s `PRIMITIVE`, while `S`
-- returns `SLCommon`'s), its procedures are calls of `S(Last(F))`'s (exception E5)
module S2 using (F : DFUNCTIONALITY) : PRIMITIVE {
  proc init () : Unit {
    _ <- call (Indifferentiability.PRIMITIVE.init state (List block) block
      (Module.app Gconcl.S (Module.app Last F))) ();
    return ()
  };
  proc f (x : state) : state {
    var y : state;
    y <- call (Indifferentiability.PRIMITIVE.f state (List block) block
      (Module.app Gconcl.S (Module.app Last F))) ($x);
    return $y
  };
  proc fi (x : state) : state {
    var y : state;
    y <- call (Indifferentiability.PRIMITIVE.fi state (List block) block
      (Module.app Gconcl.S (Module.app Last F))) ($x);
    return $y
  };
}

/-- EC's local `L4(D)(F)(F2)`: `proc distinguish = IdealIndif(DSqueeze2(F, F2), S2,
DValid(DRestr(D))).main`. -/
noncomputable def L4 (D : DISTINGUISHER) (F : SLCommon.F.RO_T) (F2 : F2.RO_T) :
    procmod () → Bool :=
  IdealIndif (Module.app DSqueeze2 (Module.pair F F2)) S2 (DValid (DRestr D))

/-- The section's restriction `{-SLCommon.C, -C, -IF, -S, -F2.RO, -BIRO.IRO, -BIRO2.IRO}` (an
abbreviation). -/
def DRestrictions_Ideal2 (D : DISTINGUISHER) : Prop :=
  DRestrictions_Ideal D ∧ FVP.fvP D ≤ ((F2.RO.m).footprint ⊔ (BlockSponge.BIRO.IRO.mp).footprint ⊔
    (BIRO2.IRO.mp).footprint)ᶜ

def inv_map (m1 : FMap (List block) block) (m2 : FMap (List block × ℤ) block) : Prop :=
  (∀ p n x, parse x = (p, n + 1) → (FMap.dom m2 (p, n) ↔ FMap.dom m1 x)) ∧
  (∀ p n x, parse x = (p, n + 1) → (FMap.dom m1 x ↔ FMap.dom m2 (p, n))) ∧
  (∀ p n x, parse x = (p, n + 1) → FMap.get m2 (p, n) = FMap.get m1 x) ∧
  (∀ p n x, parse x = (p, n + 1) → FMap.get m1 x = FMap.get m2 (p, n))

inductive INV_L4_ideal (m1 : FMap (List block) block) (m2 : FMap (List block × ℤ) block)
    (m3 : FMap (List block) block) (m4 : FMap (List block × ℤ) block) : Prop where
  | inv_maps :
      inv_map m1 m2 → inv_map m3 m4 →
      (∀ p n, FMap.dom m2 (p, n) → valid p = true ∧ 0 ≤ n) →
      (∀ p n, FMap.dom m4 (p, n) → valid p = false ∧ 0 ≤ n) →
      INV_L4_ideal m1 m2 m3 m4

theorem lemma5 (m1 : FMap (List block) block) (m2 : FMap (List block × ℤ) block)
    (m3 : FMap (List block) block) (m4 : FMap (List block × ℤ) block) (p : List block) (i : ℤ)
    (r : block) :
    INV_L4_ideal m1 m2 m3 m4 → ¬ FMap.dom m2 (p, i) → 0 ≤ i → valid p = true →
    INV_L4_ideal (FMap.set m1 (format p (i + 1)) r) (FMap.set m2 (p, i) r) m3 m4 := by
  rintro ⟨⟨h1, h2, h3, h4⟩, inv34, hd2, hd4⟩ hn hi hp
  have hpk : parse (format p (i + 1)) = (p, i + 1) :=
    parseK p (i + 1) (by omega) (by simpa [valid] using hp)
  have key : ∀ p' n x, parse x = (p', n + 1) → ((p', n) = (p, i) ↔ x = format p (i + 1)) := by
    intro p' n x hx
    constructor
    · intro h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      have := formatK x
      rw [hx] at this
      exact this.symm
    · rintro rfl
      rw [hpk] at hx
      obtain ⟨rfl, h⟩ := Prod.mk.inj hx
      rw [show i = n by omega]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, inv34, ?_, hd4⟩
  · intro p' n x hx
    rw [FMap.mem_set, FMap.mem_set, h1 p' n x hx, key p' n x hx]
  · intro p' n x hx
    rw [FMap.mem_set, FMap.mem_set, h1 p' n x hx, key p' n x hx]
  · intro p' n x hx
    rw [FMap.get_setE, FMap.get_setE, h3 p' n x hx]
    by_cases h : x = format p (i + 1)
    · rw [if_pos h, if_pos ((key p' n x hx).mpr h)]
    · rw [if_neg h, if_neg (mt (key p' n x hx).mp h)]
  · intro p' n x hx
    rw [FMap.get_setE, FMap.get_setE, h3 p' n x hx]
    by_cases h : x = format p (i + 1)
    · rw [if_pos h, if_pos ((key p' n x hx).mpr h)]
    · rw [if_neg h, if_neg (mt (key p' n x hx).mp h)]
  · intro p' n hd
    rcases (FMap.mem_set _ _ _ _).mp hd with hd | h
    · exact hd2 p' n hd
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨hp, hi⟩

theorem lemma5bis (m1 : FMap (List block) block) (m2 : FMap (List block × ℤ) block)
    (m3 : FMap (List block) block) (m4 : FMap (List block × ℤ) block) (p : List block) (i : ℤ)
    (r : block) :
    INV_L4_ideal m1 m2 m3 m4 → ¬ FMap.dom m4 (p, i) → 0 ≤ i → valid p = false →
    parse (format p (i + 1)) = (p, i + 1) →
    INV_L4_ideal m1 m2 (FMap.set m3 (format p (i + 1)) r) (FMap.set m4 (p, i) r) := by
  rintro ⟨inv12, ⟨h1, h2, h3, h4⟩, hd2, hd4⟩ hn hi hp hpk
  have key : ∀ p' n x, parse x = (p', n + 1) → ((p', n) = (p, i) ↔ x = format p (i + 1)) := by
    intro p' n x hx
    constructor
    · intro h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      have := formatK x
      rw [hx] at this
      exact this.symm
    · rintro rfl
      rw [hpk] at hx
      obtain ⟨rfl, h⟩ := Prod.mk.inj hx
      rw [show i = n by omega]
  refine ⟨inv12, ⟨?_, ?_, ?_, ?_⟩, hd2, ?_⟩
  · intro p' n x hx
    rw [FMap.mem_set, FMap.mem_set, h1 p' n x hx, key p' n x hx]
  · intro p' n x hx
    rw [FMap.mem_set, FMap.mem_set, h1 p' n x hx, key p' n x hx]
  · intro p' n x hx
    rw [FMap.get_setE, FMap.get_setE, h3 p' n x hx]
    by_cases h : x = format p (i + 1)
    · rw [if_pos h, if_pos ((key p' n x hx).mpr h)]
    · rw [if_neg h, if_neg (mt (key p' n x hx).mp h)]
  · intro p' n x hx
    rw [FMap.get_setE, FMap.get_setE, h3 p' n x hx]
    by_cases h : x = format p (i + 1)
    · rw [if_pos h, if_pos ((key p' n x hx).mpr h)]
    · rw [if_neg h, if_neg (mt (key p' n x hx).mp h)]
  · intro p' n hd
    rcases (FMap.mem_set _ _ _ _).mp hd with hd | h
    · exact hd4 p' n hd
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨hp, hi⟩

omit [Params] in
/-- The initial maps satisfy `INV_L4_ideal`. -/
theorem INV_L4_ideal_empty :
    INV_L4_ideal FMap.empty FMap.empty FMap.empty FMap.empty := by
  have hm : inv_map (FMap.empty : FMap (List block) block) FMap.empty :=
    ⟨fun _ _ _ _ => iff_of_false (FMap.mem_empty _) (FMap.mem_empty _),
      fun _ _ _ _ => iff_of_false (FMap.mem_empty _) (FMap.mem_empty _), fun _ _ _ _ => rfl,
      fun _ _ _ _ => rfl⟩
  exact ⟨hm, hm,
    fun _ _ h => absurd h (FMap.mem_empty _), fun _ _ h => absurd h (FMap.mem_empty _)⟩

-- `L4(D)(F)(F2.RO)` as an `F.RO_Distinguisher`, for `RO_LRO_D`: EC applies `RO_LRO_D` to
-- `D5(D)`, the distinguisher left after inlining `L4`; here to the whole of `L4` (whose
-- `distinguish` calls the game's `main`, exception E5), which is the same equivalence
set_option linter.gaudisCrypt.using false in
module L4F (D : DISTINGUISHER) using (F : SLCommon.F.RO_T) {
  proc distinguish (_u : Unit) : Bool {
    var b : Bool;
    b <- call (Module.app (Indifferentiability.Indif state (List block × ℤ) (List block))
      (Module.pair (Module.app DSqueeze2 (Module.pair F F2.RO.asRO)) (Module.pair (Module.app S2
        (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app DSqueeze2 (Module.pair F F2.RO.asRO)) })) (DValid (DRestr D))))) ();
    return $b
  };
}

/-- `L4` is `L4F`'s `distinguish` (its call). -/
theorem L4F_bridge (D : DISTINGUISHER) (F : SLCommon.F.RO_T) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂) (L4 D F F2.RO.asRO).procedure
      (Module.app (L4F D) F).procedure (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  unfold L4 IdealIndif Indifferentiability.GIdeal
  equiv_proc_to_stmt
  stmt_inline{2} 0
  simp only [Indifferentiability.FUNCTIONALITY.view]
  stmt_wp
  equiv_call (prhlProc_refl _)
  stmt_wp
  equiv_skip
  intro g₁ g₂ h
  exact ⟨h, fun _ _ _ _ h => h⟩

/-- `L4F`'s `distinguish` is `L4`. -/
theorem L4F_bridge' (D : DISTINGUISHER) (F : SLCommon.F.RO_T) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂) (Module.app (L4F D) F).procedure
      (L4 D F F2.RO.asRO).procedure (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  unfold L4 IdealIndif Indifferentiability.GIdeal
  equiv_proc_to_stmt
  stmt_inline{1} 0
  simp only [Indifferentiability.FUNCTIONALITY.view]
  stmt_wp
  equiv_call (prhlProc_refl _)
  stmt_wp
  equiv_skip
  intro g₁ g₂ h
  exact ⟨h, fun _ _ _ _ h => h⟩

set_option maxHeartbeats 4000000 in
-- `within_lens` through `L4`'s modules
omit [Params] in
/-- `L4F D` touches `glob D`, `C.c`, `S`'s variables and the other clone's `RO.m`.  Not an EC
lemma. -/
theorem fvP_L4F (D : DISTINGUISHER) :
    FVP.fvP (L4F D) ≤ FVP.fvP D ⊔ (Lens.pair BlockSponge.C.c (Lens.pair Gconcl.S.m
      (Lens.pair Gconcl.S.mi
      (Lens.pair Gconcl.S.paths F2.RO.m)))).footprint := by
  fp_module (Lens.pair BlockSponge.C.c (Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi
      (Lens.pair Gconcl.S.paths F2.RO.m))))

/-- `L4(D, F.RO, F2.RO) ~ L4(D, F.LRO, F2.RO)` (EC: `call (F.FullEager.RO_LRO_D (D5(D)) _)`). -/
theorem L4_F_RO_LRO (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal2 D)
    (_hDd' : FVP.fvP D ≤ ((SLCommon.F.FRO.m).footprint ⊔ (F2.FRO.m).footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (L4 D SLCommon.F.RO.asRO F2.RO.asRO).procedure (L4 D SLCommon.F.LRO F2.RO.asRO).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hX : (Lens.pair BlockSponge.C.c (Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi
      (Lens.pair Gconcl.S.paths F2.RO.m)))).footprint.FinitelySupported := by
    simp only [Footprint.lens_pair]
    repeat (first | exact .varLens _ | refine .sup ?_ ?_)
  have hmod := PROM.FullRO.RO_Distinguisher.ecModule (List block) block Unit Bool (L4F D)
    ((hD.finitelySupported.sup hX).mono (fvP_L4F D))
  obtain ⟨h1, h2⟩ := _hDd
  unfold DRestrictions_Ideal at h1
  have hdisj : FVP.fvP (L4F D) ≤ ((SLCommon.F.RO.m).footprint ⊔ (SLCommon.F.FRO.m).footprint)ᶜ := by
    refine (fvP_L4F D).trans ((Footprint.le_compl_comm _ _).mp (sup_le ?_ ?_))
    · refine (Footprint.le_compl_comm _ _).mp (sup_le (by fp_disjoint) ?_)
      simp only [Footprint.lens_pair]
      fp_disjoint
    · refine (Footprint.le_compl_comm _ _).mp (sup_le (by fp_disjoint) ?_)
      simp only [Footprint.lens_pair]
      fp_disjoint
  have hRO := PROM.FullRO.FullEager.RO_LRO_D (List block) block Unit Bool SLCommon.F.dout
    SLCommon.F.FRO.m (fun _ => BitWord.dunifin_ll) SLCommon.F.RO.m (L4F D) hmod hdisj
  exact prhlProc_conseq (prhlProc.trans (L4F_bridge D SLCommon.F.RO.asRO)
      (prhlProc.trans hRO (L4F_bridge' D SLCommon.F.LRO)))
    (fun a₁ g₁ a₃ g₃ h => ⟨(), g₁, rfl, (), g₃, ⟨rfl, by rw [h], by rw [h]⟩, rfl⟩)
    (fun r₁ g₁ r₃ g₃ ⟨r₂, g₂, ⟨h1, _⟩, r₂', g₂', ⟨h2, _⟩, h3, _⟩ => h1.trans (h2.trans h3))

-- `L4(D)(F.LRO)(F2)` as an `F2.RO_Distinguisher` (EC's `D6(D)`, as `L4F` for `D5`)
set_option linter.gaudisCrypt.using false in
module L4G (D : DISTINGUISHER) using (F2' : F2.RO_T) {
  proc distinguish (_u : Unit) : Bool {
    var b : Bool;
    b <- call (Module.app (Indifferentiability.Indif state (List block × ℤ) (List block))
      (Module.pair (Module.app DSqueeze2 (Module.pair SLCommon.F.LRO F2'))
        (Module.pair (Module.app S2
        (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app DSqueeze2 (Module.pair SLCommon.F.LRO F2')) })) (DValid (DRestr D))))) ();
    return $b
  };
}

/-- `L4` is `L4G`'s `distinguish` (its call). -/
theorem L4G_bridge (D : DISTINGUISHER) (F2' : F2.RO_T) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂) (L4 D SLCommon.F.LRO F2').procedure
      (Module.app (L4G D) F2').procedure (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  unfold L4 IdealIndif Indifferentiability.GIdeal
  equiv_proc_to_stmt
  stmt_inline{2} 0
  simp only [Indifferentiability.FUNCTIONALITY.view]
  stmt_wp
  equiv_call (prhlProc_refl _)
  stmt_wp
  equiv_skip
  intro g₁ g₂ h
  exact ⟨h, fun _ _ _ _ h => h⟩

/-- `L4G`'s `distinguish` is `L4`. -/
theorem L4G_bridge' (D : DISTINGUISHER) (F2' : F2.RO_T) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂) (Module.app (L4G D) F2').procedure
      (L4 D SLCommon.F.LRO F2').procedure (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  unfold L4 IdealIndif Indifferentiability.GIdeal
  equiv_proc_to_stmt
  stmt_inline{1} 0
  simp only [Indifferentiability.FUNCTIONALITY.view]
  stmt_wp
  equiv_call (prhlProc_refl _)
  stmt_wp
  equiv_skip
  intro g₁ g₂ h
  exact ⟨h, fun _ _ _ _ h => h⟩

set_option maxHeartbeats 4000000 in
-- `within_lens` through `L4`'s modules
omit [Params] in
/-- `L4G D` touches `glob D`, `C.c`, `S`'s variables and the other clone's `RO.m`.  Not an EC
lemma. -/
theorem fvP_L4G (D : DISTINGUISHER) :
    FVP.fvP (L4G D) ≤ FVP.fvP D ⊔ (Lens.pair BlockSponge.C.c (Lens.pair Gconcl.S.m
      (Lens.pair Gconcl.S.mi
      (Lens.pair Gconcl.S.paths SLCommon.F.RO.m)))).footprint := by
  fp_module (Lens.pair BlockSponge.C.c (Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi
      (Lens.pair Gconcl.S.paths SLCommon.F.RO.m))))

/-- `L4(D, F.LRO, F2.RO) ~ L4(D, F.LRO, F2.LRO)` (EC: `call (F2.FullEager.RO_LRO_D (D6(D)) _)`). -/
theorem L4_F2_RO_LRO (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal2 D)
    (_hDd' : FVP.fvP D ≤ ((SLCommon.F.FRO.m).footprint ⊔ (F2.FRO.m).footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (L4 D SLCommon.F.LRO F2.RO.asRO).procedure (L4 D SLCommon.F.LRO F2.LRO).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hX : (Lens.pair BlockSponge.C.c (Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi
      (Lens.pair Gconcl.S.paths SLCommon.F.RO.m)))).footprint.FinitelySupported := by
    simp only [Footprint.lens_pair]
    repeat (first | exact .varLens _ | refine .sup ?_ ?_)
  have hmod := PROM.FullRO.RO_Distinguisher.ecModule (List block) block Unit Bool (L4G D)
    ((hD.finitelySupported.sup hX).mono (fvP_L4G D))
  obtain ⟨h1, h2⟩ := _hDd
  unfold DRestrictions_Ideal at h1
  have hdisj : FVP.fvP (L4G D) ≤ ((F2.RO.m).footprint ⊔ (F2.FRO.m).footprint)ᶜ := by
    refine (fvP_L4G D).trans ((Footprint.le_compl_comm _ _).mp (sup_le ?_ ?_))
    · refine (Footprint.le_compl_comm _ _).mp (sup_le (by fp_disjoint) ?_)
      simp only [Footprint.lens_pair]
      fp_disjoint
    · refine (Footprint.le_compl_comm _ _).mp (sup_le (by fp_disjoint) ?_)
      simp only [Footprint.lens_pair]
      fp_disjoint
  have hRO := PROM.FullRO.FullEager.RO_LRO_D (List block) block Unit Bool F2.dout
    F2.FRO.m (fun _ => BitWord.dunifin_ll) F2.RO.m (L4G D) hmod hdisj
  exact prhlProc_conseq (prhlProc.trans (L4G_bridge D F2.RO.asRO)
      (prhlProc.trans hRO (L4G_bridge' D F2.LRO)))
    (fun a₁ g₁ a₃ g₃ h => ⟨(), g₁, rfl, (), g₃, ⟨rfl, by rw [h], by rw [h]⟩, rfl⟩)
    (fun r₁ g₁ r₃ g₃ ⟨r₂, g₂, ⟨h1, _⟩, r₂', g₂', ⟨h2, _⟩, h3, _⟩ => h1.trans (h2.trans h3))

end Ideal

/-! ## The section `Real` -/

section Real

inductive m_p (m : FMap state state) (p : FMap (List block) state) : Prop where
  | IND_M_P :
      FMap.get p [] = some (b0, c0) →
      (∀ l, FMap.dom p l → ∀ i, 0 ≤ i ∧ i < size l →
        ∃ b c, FMap.get p (take i l) = some (b, c) ∧
          FMap.get m (b +^ nth default l i, c) = FMap.get p (take (i + 1) l)) →
      m_p m p

inductive INV_Real (c1 c2 : ℤ) (m mi : FMap state state) (p : FMap (List block) state) :
    Prop where
  | INV_real : c1 ≤ c2 → m_p m p → invm m mi → INV_Real c1 c2 m mi p

theorem INV_Real_incr (c1 c2 : ℤ) (m mi : FMap state state) (p : FMap (List block) state) :
    INV_Real c1 c2 m mi p → INV_Real (c1 + 1) (c2 + 1) m mi p := by
  rintro ⟨h, hm, hi⟩
  exact ⟨by omega, hm, hi⟩

theorem INV_Real_addm_mi (c1 c2 : ℤ) (m mi : FMap state state) (p : FMap (List block) state)
    (x y : state) :
    INV_Real c1 c2 m mi p → ¬ FMap.dom m x → ¬ FMap.rng m y →
    INV_Real c1 c2 (FMap.set m x y) (FMap.set mi y x) p := by
  rintro ⟨hc, ⟨h0, hmp⟩, hinv⟩ hx hy
  refine ⟨hc, ⟨h0, ?_⟩, invm_set m mi x y hx hy hinv⟩
  intro l hl i hi
  obtain ⟨b, c, hb, hm⟩ := hmp l hl i hi
  refine ⟨b, c, hb, ?_⟩
  rw [FMap.get_setE, if_neg]
  · exact hm
  · intro heq
    apply hx
    rw [FMap.domE, ← heq, hm]
    by_cases hs : i + 1 < size l
    · obtain ⟨b', c', hb', -⟩ := hmp l hl (i + 1) ⟨by omega, hs⟩
      rw [hb']; simp
    · have : take (i + 1) l = l := List.take_of_length_le (by simp only [size] at hs; omega)
      rw [this, ← FMap.domE]; exact hl

theorem invmC (m mi : FMap state state) : invm m mi ↔ invm mi m :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

theorem invm_dom_rng (m mi : FMap state state) : invm m mi → FMap.dom m = FMap.rng mi := by
  intro h
  funext x
  apply propext
  rw [FMap.domE, FMap.rngE]
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hx
    exact ⟨v, (h x v).mp hv⟩
  · rintro ⟨a, ha⟩
    rw [(h x a).mpr ha]
    simp

theorem all_prefixes_of_INV_real (c1 c2 : ℤ) (m mi : FMap state state)
    (p : FMap (List block) state) : INV_Real c1 c2 m mi p → all_prefixes p := by
  rintro ⟨-, ⟨h0, hmp⟩, -⟩ bs hbs i
  by_cases hi0 : i ≤ 0
  · have : take i bs = [] := by simp [take, show i.toNat = 0 by omega]
    rw [this, FMap.domE, h0]; simp
  by_cases his : size bs ≤ i
  · have : take i bs = bs := List.take_of_length_le (by simp only [size] at his; omega)
    rw [this]; exact hbs
  · obtain ⟨b, c, hb, -⟩ := hmp bs hbs i ⟨by omega, by omega⟩
    rw [FMap.domE, hb]; simp

theorem lemma2' (c1 c2 : ℤ) (m mi : FMap state state) (p : FMap (List block) state)
    (bl : List block) (i : ℤ) (sa : block) (sc : capacity) :
    INV_Real c1 c2 m mi p → 1 < i → valid bl = true → FMap.dom m (sa, sc) →
    ¬ FMap.dom p (format bl i) → FMap.get p (format bl (i - 1)) = some (sa, sc) →
    INV_Real c1 c2 m mi (FMap.set p (format bl i) (oget (FMap.get m (sa, sc)))) := by
  intro inv0 hi hv hdm hnp hpbl
  have hx0 : ∀ x : block, x +^ b0 = x := fun x => by
    apply List.Vector.ext; intro j; simp [BitWord.xorw, b0, BitWord.zerow]
  have hf : format bl i = rcons (format bl (i - 1)) b0 := by
    simp only [format, nseq, rcons, List.append_assoc]
    rw [show (i - 1).toNat = (i - 1 - 1).toNat + 1 by omega, List.replicate_succ']
  have key : ∀ (bl : List block) (b sa : block) (sc : capacity),
      FMap.dom m (sa +^ b, sc) → ¬ FMap.dom p (rcons bl b) → FMap.get p bl = some (sa, sc) →
      INV_Real c1 c2 m mi (FMap.set p (rcons bl b) (oget (FMap.get m (sa +^ b, sc)))) := by
    intro bl b sa sc hdm hnp hpbl
    have hall := all_prefixes_of_INV_real c1 c2 m mi p inv0
    obtain ⟨hc, ⟨h0, hmp⟩, hinv⟩ := inv0
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hdm)
    have hdp : ∀ k, FMap.dom p k →
        FMap.get (FMap.set p (rcons bl b) (oget (FMap.get m (sa +^ b, sc)))) k = FMap.get p k :=
      fun k hk => FMap.get_set_neqE _ _ _ _ (fun h => hnp (h ▸ hk))
    have hdpl : FMap.dom p bl := by rw [FMap.domE, hpbl]; simp
    refine ⟨hc, ⟨?_, ?_⟩, hinv⟩
    · rw [hdp [] (by rw [FMap.domE, h0]; simp)]; exact h0
    · intro l hl j hj
      rcases (FMap.mem_set _ _ _ _).mp hl with hl | rfl
      · obtain ⟨b', c', hb, hm⟩ := hmp l hl j hj
        refine ⟨b', c', ?_, ?_⟩
        · rw [hdp _ (hall l hl j)]; exact hb
        · rw [hdp _ (hall l hl (j + 1))]; exact hm
      · have hs : size (rcons bl b) = size bl + 1 := by simp [size, rcons]
        have ht : ∀ k, k ≤ size bl → take k (rcons bl b) = take k bl := by
          intro k hk
          simp only [take, rcons, size] at hk ⊢
          rw [List.take_append_of_le_length (by omega)]
        by_cases hjs : j < size bl
        · have hn : nth default (rcons bl b) j = nth default bl j := by
            simp only [nth, rcons, size] at hjs ⊢
            rw [if_pos hj.1, if_pos hj.1]
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_append_left (show j.toNat < bl.length by omega)]
          obtain ⟨b', c', hb, hm⟩ := hmp bl hdpl j ⟨hj.1, hjs⟩
          refine ⟨b', c', ?_, ?_⟩
          · rw [ht j (by omega), hdp _ (hall bl hdpl j)]; exact hb
          · rw [ht (j + 1) (by omega), hdp _ (hall bl hdpl (j + 1)), hn]; exact hm
        · have hj' : j = size bl := by omega
          subst hj'
          refine ⟨sa, sc, ?_, ?_⟩
          · rw [ht _ le_rfl, take_size, hdp bl hdpl]; exact hpbl
          · have hn : nth default (rcons bl b) (size bl) = b := by simp [nth, rcons, size]
            have ht2 : take (size bl + 1) (rcons bl b) = rcons bl b :=
              List.take_of_length_le (by simp [rcons, size])
            rw [hn, ht2, FMap.get_set_sameE, hv]
            simp [oget]
  rw [hf] at hnp ⊢
  have := key (format bl (i - 1)) b0 sa sc (by rw [hx0]; exact hdm) hnp hpbl
  rwa [hx0] at this

theorem take_format (bl : List block) (n i : ℤ) :
    0 < n → 0 ≤ i ∧ i < size bl + n →
    take i (format bl n) = if i ≤ size bl then take i bl else format bl (i - size bl + 1) := by
  rintro hn ⟨hi0, his⟩
  simp only [format, take, nseq, size, List.take_append, List.take_replicate] at his ⊢
  split_ifs with h
  · rw [show i.toNat - bl.length = 0 by omega]; simp
  · rw [List.take_of_length_le (by omega)]
    congr 2; omega

theorem lemma4 (c c' : ℤ) (m mi : FMap state state) (p : FMap (List block) state)
    (bl : List block) (i : ℤ) (sa : block) (sc : capacity) :
    INV_Real c c' m mi p → 0 < i → FMap.get p (format bl i) = some (sa, sc) →
    FMap.dom p (format bl (i + 1)) → FMap.get p (format bl (i + 1)) = FMap.get m (sa, sc) := by
  rintro ⟨-, ⟨-, hmp⟩, -⟩ hi hp hd
  have hx0 : ∀ x : block, x +^ b0 = x := fun x => by
    apply List.Vector.ext; intro j; simp [BitWord.xorw, b0, BitWord.zerow]
  have hf : format bl (i + 1) = format bl i ++ [b0] := by
    simp only [format, nseq, List.append_assoc]
    rw [show (i + 1 - 1).toNat = (i - 1).toNat + 1 by omega, List.replicate_succ']
  rw [hf] at hd ⊢
  obtain ⟨b, c, hb, hm⟩ := hmp _ hd (size (format bl i)) ⟨by simp [size], by simp [size]⟩
  have ht1 : take (size (format bl i)) (format bl i ++ [b0]) = format bl i := by simp [take, size]
  have ht2 : take (size (format bl i) + 1) (format bl i ++ [b0]) = format bl i ++ [b0] :=
    List.take_of_length_le (by simp [size])
  have hn : nth default (format bl i ++ [b0]) (size (format bl i)) = b0 := by simp [nth, size]
  rw [ht1, hp] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb).symm
  rw [hn, ht2, hx0] at hm
  exact hm.symm

theorem lemma_3 (c1 c2 : ℤ) (m mi : FMap state state) (p : FMap (List block) state)
    (bl : List block) (b sa : block) (sc : capacity) :
    INV_Real c1 c2 m mi p → FMap.dom m (sa +^ b, sc) → ¬ FMap.dom p (rcons bl b) →
    FMap.get p bl = some (sa, sc) →
    INV_Real c1 c2 m mi (FMap.set p (rcons bl b) (oget (FMap.get m (sa +^ b, sc)))) := by
  intro inv0 hdm hnp hpbl
  have hall := all_prefixes_of_INV_real c1 c2 m mi p inv0
  obtain ⟨hc, ⟨h0, hmp⟩, hinv⟩ := inv0
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hdm)
  have hdp : ∀ k, FMap.dom p k →
      FMap.get (FMap.set p (rcons bl b) (oget (FMap.get m (sa +^ b, sc)))) k = FMap.get p k :=
    fun k hk => FMap.get_set_neqE _ _ _ _ (fun h => hnp (h ▸ hk))
  have hdpl : FMap.dom p bl := by rw [FMap.domE, hpbl]; simp
  refine ⟨hc, ⟨?_, ?_⟩, hinv⟩
  · rw [hdp [] (by rw [FMap.domE, h0]; simp)]; exact h0
  · intro l hl j hj
    rcases (FMap.mem_set _ _ _ _).mp hl with hl | rfl
    · obtain ⟨b', c', hb, hm⟩ := hmp l hl j hj
      refine ⟨b', c', ?_, ?_⟩
      · rw [hdp _ (hall l hl j)]; exact hb
      · rw [hdp _ (hall l hl (j + 1))]; exact hm
    · have hs : size (rcons bl b) = size bl + 1 := by simp [size, rcons]
      have ht : ∀ k, k ≤ size bl → take k (rcons bl b) = take k bl := by
        intro k hk
        simp only [take, rcons, size] at hk ⊢
        rw [List.take_append_of_le_length (by omega)]
      by_cases hjs : j < size bl
      · have hn : nth default (rcons bl b) j = nth default bl j := by
          simp only [nth, rcons, size] at hjs ⊢
          rw [if_pos hj.1, if_pos hj.1]
          simp [List.getD_eq_getElem?_getD,
            List.getElem?_append_left (show j.toNat < bl.length by omega)]
        obtain ⟨b', c', hb, hm⟩ := hmp bl hdpl j ⟨hj.1, hjs⟩
        refine ⟨b', c', ?_, ?_⟩
        · rw [ht j (by omega), hdp _ (hall bl hdpl j)]; exact hb
        · rw [ht (j + 1) (by omega), hdp _ (hall bl hdpl (j + 1)), hn]; exact hm
      · have hj' : j = size bl := by omega
        subst hj'
        refine ⟨sa, sc, ?_, ?_⟩
        · rw [ht _ le_rfl, take_size, hdp bl hdpl]; exact hpbl
        · have hn : nth default (rcons bl b) (size bl) = b := by simp [nth, rcons, size]
          have ht2 : take (size bl + 1) (rcons bl b) = rcons bl b :=
            List.take_of_length_le (by simp [rcons, size])
          rw [hn, ht2, FMap.get_set_sameE, hv]
          simp [oget]

omit [BlockSponge.Params] [Params] in
/-- `P`, at `DPRIMITIVE`, is `Perm`'s two procedures. -/
theorem P_view : Indifferentiability.PRIMITIVE.view state (List block × ℤ) (List block) P =
    Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
      { f := PRP.RP.RP.f (block × capacity) dD Perm.m Perm.mi
        fi := PRP.RP.RP.fi (block × capacity) dD Perm.m Perm.mi } := by
  unfold Indifferentiability.PRIMITIVE.view P Perm PRP.RP.RP
  simp [Indifferentiability.PRIMITIVE.f, Indifferentiability.PRIMITIVE.fi, PRP.StrongPRP.PRP.mk]

omit [BlockSponge.Params] [Params] in
/-- `format p (j + 1)` is `format p j` and one more `b0`. -/
theorem format_succ (bl : List block) (j : ℤ) (hj : 0 < j) :
    format bl (j + 1) = format bl j ++ [b0] := by
  simp only [format, nseq, List.append_assoc]
  rw [show (j + 1 - 1).toNat = (j - 1).toNat + 1 by omega, List.replicate_succ']

omit [BlockSponge.Params] [Params] in
/-- The first `k` blocks of `format p (j + 1)` are those of `format p j`, for
`k <= size (format p j)`. -/
theorem take_format_succ (bl : List block) (j k : ℤ) (hj : 0 < j) (hk : k ≤ size (format bl j)) :
    take k (format bl (j + 1)) = take k (format bl j) := by
  rw [format_succ bl j hj]
  simp only [take, size] at hk ⊢
  rw [List.take_append_of_le_length (by omega)]

omit [BlockSponge.Params] [Params] in
/-- `b0` is the unit of `+^`. -/
theorem xorw_b0 (x : block) : x +^ b0 = x := by
  apply List.Vector.ext; intro j; simp [BitWord.xorw, b0, BitWord.zerow]

omit [SLCommon.Params] [BlockSponge.Params] [Params] in
/-- The absorbing loops' guards agree: `i < size l` iff `drop i l` is not empty. -/
theorem decide_lt_size_drop {α : Type} (l : List α) (i : ℤ) (h : 0 ≤ i) :
    decide (i < size l) = !(drop i l).isEmpty := by
  simp only [size, drop]
  by_cases hi : i < l.length <;> simp [hi] <;> omega

omit [SLCommon.Params] [BlockSponge.Params] [Params] in
/-- `head x0 (drop i l) = nth default l i` within `l`. -/
theorem head_drop_nth {α : Type} [Inhabited α] (x0 : α) (l : List α) (i : ℤ)
    (h : 0 ≤ i ∧ i < size l) :
    head x0 (drop i l) = nth default l i := by
  simp only [size] at h
  simp only [head, drop, nth, if_pos h.1]
  rw [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  rfl

omit [SLCommon.Params] [BlockSponge.Params] [Params] in
/-- `behead (drop i l) = drop (i + 1) l`. -/
theorem behead_drop_succ {α : Type} (l : List α) (i : ℤ) (h : 0 ≤ i) :
    behead (drop i l) = drop (i + 1) l := by
  simp only [behead, drop, List.tail_drop]
  congr 1; omega

omit [BlockSponge.Params] [Params] in
/-- `INV_Real` after `Perm.init` and `Redo.init`. -/
theorem INV_Real_init :
    INV_Real 0 0 (FMap.empty : FMap state state) FMap.empty
      (FMap.set (FMap.empty : FMap (List block) state) [] (b0, c0)) := by
  refine ⟨le_rfl, ⟨FMap.get_set_sameE _ _ _, ?_⟩, ?_⟩
  · intro l hl i hi
    rcases (FMap.mem_set _ _ _ _).mp hl with hl | rfl
    · exact absurd hl (FMap.mem_empty _)
    · simp [size] at hi; omega
  · intro x y
    simp

omit [BlockSponge.Params] [Params] in
/-- `INV_Real` with a larger bound. -/
theorem INV_Real_mono {c1 c2 c2' : ℤ} {m mi : FMap state state} {p : FMap (List block) state}
    (h : INV_Real c1 c2 m mi p) (h2 : c2 ≤ c2') : INV_Real c1 c2' m mi p := by
  obtain ⟨hc, hm, hi⟩ := h
  exact ⟨hc.trans h2, hm, hi⟩

end Real

/-- The bound of `concl` and `Real_Ideal`. -/
noncomputable def bound : ℝ :=
  ((max_size ^ 2 - max_size : ℤ) : ℝ) / 2 / ((2 ^ r.toNat : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ) +
    (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) +
    (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ))

/-! ## Footprints and losslessness of the oracles (for `A_lossless`, `Ideal_lossless`)

EasyCrypt reads a concrete module's globals off its code and proves the oracles' losslessness inline
(`proc; inline*; ...; while (true) (n - i)`); here they are lemmas. -/

omit [BlockSponge.Params] [Params] in
/-- `FC` touches `C.c` only.  Not an EC lemma (EC reads it off the code). -/
@[fp_bound] theorem fvP_FC : FVP.fvP BlockSponge.FC ≤ (BlockSponge.C.c).footprint := by
  fp_module BlockSponge.C.c

omit [BlockSponge.Params] [Params] in
/-- `PC` touches `C.c` only.  Not an EC lemma. -/
@[fp_bound] theorem fvP_PC : FVP.fvP BlockSponge.PC ≤ (BlockSponge.C.c).footprint := by
  fp_module BlockSponge.C.c

omit [BlockSponge.Params] [Params] in
/-- `IRO.init` touches its map only.  Not an EC lemma. -/
@[fp_bound] theorem fvP_IRO_init (valid : List block → Bool) (d : SubProbability block)
    (mp : Lens (FMap (List block × ℤ) block) VariableAssignment) :
    FVP.fvP (IRO.IRO.init block (List block) valid d mp) ≤ mp.footprint := by
  fp_module mp

omit [BlockSponge.Params] [Params] in
/-- `IRO.f` touches its map only.  Not an EC lemma. -/
@[fp_bound] theorem fvP_IRO_f (valid : List block → Bool) (d : SubProbability block)
    (mp : Lens (FMap (List block × ℤ) block) VariableAssignment) :
    FVP.fvP (IRO.IRO.f block (List block) valid d mp) ≤ mp.footprint := by
  fp_module mp

omit [Params] in
/-- `SimLast(S)` touches `S`'s globals and `BIRO2.IRO.mp`.  Not an EC lemma. -/
@[fp_bound] theorem fvP_SimLast (S : SLCommon.SIMULATOR) :
    FVP.fvP (SimLast S) ≤ FVP.fvP S ⊔ (BIRO2.IRO.mp).footprint := by
  fp_module BIRO2.IRO.mp

omit [BlockSponge.Params] [Params] in
/-- `Gconcl.S` touches `S.m`, `S.mi`, `S.paths`.  Not an EC lemma. -/
@[fp_bound] theorem fvP_S : FVP.fvP Gconcl.S ≤
    (Gconcl.S.m).footprint ⊔ ((Gconcl.S.mi).footprint ⊔ (Gconcl.S.paths).footprint) := by
  have h : FVP.fvP Gconcl.S ≤
      (Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi Gconcl.S.paths)).footprint := by
    fp_module (Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi Gconcl.S.paths))
  simpa only [Footprint.lens_pair] using h

omit [BlockSponge.Params] [Params] in
/-- `DSqueeze` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_DSqueeze : FVP.fvP DSqueeze ≤ ⊥ := by
  fp_module

omit [BlockSponge.Params] [Params] in
/-- `P.f` is lossless (`ConcreteF.Perm_f_ll`: `Perm.m` misses the queried key, so its range misses
a value).  Not an EC lemma. -/
theorem P_f_ll :
    (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P).procedure.IsLossless :=
  ConcreteF.Perm_f_ll

omit [BlockSponge.Params] [Params] in
/-- `Sponge` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_Sponge : FVP.fvP Sponge ≤ ⊥ := by
  fp_module

/-! ## The section `Real_Ideal` -/

section Real_Ideal

omit [Params] in
/-- `A(D)` touches `D`'s globals and `C.c`.  Not an EC lemma. -/
theorem fvP_A (D : DISTINGUISHER) : FVP.fvP (A D) ≤ FVP.fvP D ⊔ BlockSponge.C.c.footprint := by
  fp_module BlockSponge.C.c

omit [BlockSponge.Params] [Params] in
/-- `DWord.dunifin1E`. -/
theorem dunifin1E' {n : ℤ} (x : BitWord.word n) :
    (BitWord.dunifin : SubProbability (BitWord.word n)).1 {x} = ((2 : ENNReal) ^ n.toNat)⁻¹ := by
  letI : MeasurableSpace (BitWord.word n) := ⊤
  change (PMF.uniformOfFintype (BitWord.word n)).toMeasure {x} = _
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x), PMF.uniformOfFintype_apply]
  simp [BitWord.word, card_vector]

omit [BlockSponge.Params] [Params] in
/-- `dstate`'s mass at a point (EC: `dprod1E`, `dunifin1E`, `block_card`, `capacity_card`). -/
theorem dstate1E_toReal (x : state) :
    (SLCommon.dstate.1 {x}).toReal = 1 / ((2 ^ r.toNat : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ) := by
  obtain ⟨a, b⟩ := x
  rw [SLCommon.dstate, dprod1E, bdistr, cdistr, Block.DBlock.dunifin, Capacity.DCapacity.dunifin,
    dunifin1E', dunifin1E']
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv]

end Real_Ideal

/-! ## The section `Real_Ideal_Abs` (its local declarations in a namespace of that name, as
`invmC` is also a local lemma of `Real`) -/

namespace Real_Ideal_Abs

-- EC's local `Neg_D(D)(F)(P)`, with `D` a Lean parameter
set_option linter.gaudisCrypt.using false in
module Neg_D (D : DISTINGUISHER) using (F : DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    b <- call (Module.app D (Module.pair F P)) ();
    return !$b
  };
}

omit [Params] in
/-- `Neg_D(D)` touches what `D` does.  Not an EC lemma. -/
theorem fvP_Neg_D (D : DISTINGUISHER) : FVP.fvP (Real_Ideal_Abs.Neg_D D) ≤ FVP.fvP D := by
  fp_module

omit [SLCommon.Params] [BlockSponge.Params] [Params] in
/-- EC's `Neg_A_Pr_minus`, for a lossless procedure. -/
theorem Pr_false_eq_one_sub {p : Procedure (procsig () -> Bool)} (hp : p.IsLossless)
    (σ : VariableAssignment) :
    ((p.Pr () σ (fun r _ => r = false) : NNReal) : ℝ) =
      1 - ((p.Pr () σ (fun r _ => r = true) : NNReal) : ℝ) := by
  have h1 : (p.Pr () σ (fun r _ => r = false) : ENNReal) + p.Pr () σ (fun r _ => r = true) = 1 := by
    rw [Procedure.Pr_eq_ewp, Procedure.Pr_eq_ewp, ← Procedure.ewp_add, ← hp () σ]
    congr 1
    funext v g
    cases v <;> simp [indicatorE]
  have h2 : (p.Pr () σ (fun r _ => r = false) : ℝ) + p.Pr () σ (fun r _ => r = true) = 1 := by
    have := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top] at this
    simpa using this
  linarith

/-- A game on `Neg_D(D)` answers the negation of the game on `D` (EC: `byequiv; proc; inline*;
sim`). -/
theorem Indif_Neg_D (F : FUNCTIONALITY) (P0 : PRIMITIVE) (D : DISTINGUISHER) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (Module.app (Indifferentiability.Indif state (List block × ℤ) (List block))
        (Module.pair F (Module.pair P0 (DRestr D)))).procedure
      (Module.app (Indifferentiability.Indif state (List block × ℤ) (List block))
        (Module.pair F (Module.pair P0 (DRestr (Neg_D D))))).procedure
      (fun r₁ _ r₂ _ => r₁ = !r₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{1} 2
  stmt_inline{2} 2
  stmt_inline{2} 3
  stmt_wp
  simp only [Bool.not_not]
  equiv_sim

end Real_Ideal_Abs

/-! ## The simulator -/

/-- EC's `Simulator.m`. -/
global_var Simulator.m : FMap state state
/-- EC's `Simulator.mi`. -/
global_var Simulator.mi : FMap state state
/-- EC's `Simulator.paths`. -/
global_var Simulator.paths : FMap capacity (List block × block)
/-- EC's `Simulator.unvalid_map`. -/
global_var Simulator.unvalid_map : FMap (List block × ℤ) block

module Simulator using (F : DFUNCTIONALITY) : PRIMITIVE {
  proc init () : Unit {
    Simulator.m <- (FMap.empty : FMap state state);
    Simulator.mi <- (FMap.empty : FMap state state);
    Simulator.paths <- FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0);
    Simulator.unvalid_map <- (FMap.empty : FMap (List block × ℤ) block);
    return ()
  };
  proc f (x : state) : state {
    var p : List block, v : block, q : List block, k : ℤ, cs : List block, y : state,
      y1 : block, y2 : capacity, r : block;
    if (!(decide (FMap.dom ($Simulator.m : FMap state state) $x))) {
      if (decide (FMap.dom ($Simulator.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($Simulator.paths : FMap capacity (List block × block)) ($x).2);
        q, k <- parse (rcons $p ($v +^ ($x).1));
        if (valid $q) {
          cs <- call F.f (($q, $k));
          y1 <- last b0 $cs;
        } else {
          if (decide (0 < $k)) {
            if (!(decide (FMap.dom ($Simulator.unvalid_map : FMap (List block × ℤ) block)
                ($q, $k - 1)))) {
              r <$ bdistr;
              Simulator.unvalid_map <- FMap.set $Simulator.unvalid_map ($q, $k - 1) $r;
            }
            y1 <- oget (FMap.get ($Simulator.unvalid_map : FMap (List block × ℤ) block)
              ($q, $k - 1));
          } else {
            y1 <- b0;
          }
        }
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
    return $y
  };
  proc fi (x : state) : state {
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
    return $y
  };
}

/-! ## The section `Simplify_Simulator` (its local declarations in a namespace of that name, as
`L` is also a local module of `Ideal`) -/

namespace Simplify_Simulator

-- `local clone import PROM.FullRO as IRO2 with type in_t <- block list * int,
-- type out_t <- block, op dout _ <- bdistr, type d_in_t <- unit, type d_out_t <- bool`
namespace IRO2
noncomputable abbrev dout : List block × ℤ → SubProbability block := fun _ => bdistr
abbrev RO_T := PROM.FullRO.RO_T (List block × ℤ) block
end IRO2

-- EC's local `Simu(FRO : IRO2.RO)(F : DFUNCTIONALITY)`; both parameters are module parameters, so
-- that `L` (which applies it to its own parameter) is an `IRO2.RO_Distinguisher`
module Simu using (FRO : IRO2.RO_T, F : DFUNCTIONALITY) : PRIMITIVE {
  proc init () : Unit {
    _ <- call (Indifferentiability.PRIMITIVE.init state (List block × ℤ) (List block)
      (Module.app Simulator F)) ();
    _ <- call (PROM.FullRO.RO_T.init (List block × ℤ) block FRO) ();
    return ()
  };
  proc f (x : state) : state {
    var p : List block, q : List block, v : block, k : ℤ, i : ℤ, cs : List block, y : state,
      y1 : block, y2 : capacity;
    if (!(decide (FMap.dom ($Simulator.m : FMap state state) $x))) {
      if (decide (FMap.dom ($Simulator.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($Simulator.paths : FMap capacity (List block × block)) ($x).2);
        q, k <- parse (rcons $p ($v +^ ($x).1));
        if (valid $q) {
          cs <- call F.f (($q, $k));
          y1 <- last b0 $cs;
        } else {
          if (decide (0 < $k)) {
            i <- 0;
            while ($i < $k) {
              _ <- call (PROM.FullRO.RO_T.sample (List block × ℤ) block FRO) (($q, $i));
              i <- $i + 1;
            }
            y1 <- call (PROM.FullRO.RO_T.get (List block × ℤ) block FRO) (($q, $k - 1));
          } else {
            y1 <- b0;
          }
        }
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
    return $y
  };
  proc fi (x : state) : state {
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
    return $y
  };
}

-- EC's local `L(F : IRO2.RO)`: `proc distinguish = IdealIndif(BIRO.IRO, Simu(F), DRestr(D)).main`,
-- for the section's `D` (a Lean parameter, so that `L D` is an `IRO2.RO_Distinguisher`, for
-- `RO_LRO_D`); its `distinguish` calls the game's `main` (exception E5) and takes EasyCrypt's
-- `d_in_t = unit`
set_option linter.gaudisCrypt.using false in
module L (D : DISTINGUISHER) using (FRO : IRO2.RO_T) {
  proc distinguish (_u : Unit) : Bool {
    var b : Bool;
    b <- call (Module.app (Indifferentiability.Indif state (List block × ℤ) (List block))
      (Module.pair BlockSponge.BIRO.IRO.asF (Module.pair (Module.app Simu (Module.pair FRO
        (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
          BlockSponge.BIRO.IRO.asF))) (DRestr D)))) ();
    return $b
  };
}

end Simplify_Simulator

end GaudisCrypt.SHA3.Gconcl_list
