import GaudisCrypt.Examples.SHA3.BlockSponge

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
* Local modules that alias a procedure of an applied functor (`L`, `L2`, `L3`, `L4`, `D2`, `D3`,
  `D5`, `D6`) are Lean functions returning that procedure.  `SimLast` and `DValid` are used as
  functors: their aliased procedures are wrapped in a call (exception E5).  `S2` is
  `Module.comp Gconcl.S Last`.
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
theorem valid_uniq (p1 p2 : List block) (n1 n2 : ℤ) : valid p1 = true → valid p2 = true →
    format p1 n1 = format p2 n2 → p1 = p2 ∧ n1 = n2 := Params.valid_uniq p1 p2 n1 n2

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

-- EC's `A(D : DISTINGUISHER) : SLCommon.DISTINGUISHER`, with `D` a Lean parameter
set_option linter.gaudisCrypt.using false in
module A (D : DISTINGUISHER) using (F : SLCommon.DFUNCTIONALITY, P : DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call BlockSponge.C.init ();
    b <- call (Module.app (DRestr D) (Module.pair
      (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
            (Module.app DSqueeze F) })
      P)) ();
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

/-- `={glob D}`: agreement on what `D` may touch (an abbreviation). -/
def eqGlob {M : Type 1} [IsModule M] (D : M) (g₁ g₂ : VariableAssignment) : Prop :=
  (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂

/-- `local equiv ideal_equiv (D <: DISTINGUISHER {-SLCommon.C, -C, -IF, -S}) :
SLCommon.IdealIndif(IF, S, SLCommon.DRestr(A(D))).main ~ SLCommon.IdealIndif(IF, S, A(D)).main :
={glob D} ==> ={glob D, res}`. -/
theorem ideal_equiv (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ (SLCommon.C.footprint ⊔ BlockSponge.C.c.footprint ⊔
      (SLCommon.F.RO.m).footprint ⊔
      (Gconcl.S.m).footprint ⊔ (Gconcl.S.mi).footprint ⊔ (Gconcl.S.paths).footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => eqGlob D g₁ g₂)
      (SLCommon.IdealIndif Gconcl.IF Gconcl.S (SLCommon.DRestr (A D))).procedure
      (SLCommon.IdealIndif Gconcl.IF Gconcl.S (A D)).procedure
      (fun r₁ g₁ r₂ g₂ => eqGlob D g₁ g₂ ∧ r₁ = r₂) := by
  sorry

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

/-- `local equiv Ideal_equiv_valid (D <: DISTINGUISHER {-SLCommon.C, -C, -IF, -S}) :
L(D, F.LRO).distinguish ~ L2(D, F.LRO).distinguish : ={glob D} ==> ={glob D, res}`. -/
theorem Ideal_equiv_valid (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal D) :
    prhlProc (fun _ g₁ _ g₂ => eqGlob D g₁ g₂)
      (L D SLCommon.F.LRO).procedure (L2 D SLCommon.F.LRO).procedure
      (fun r₁ g₁ r₂ g₂ => eqGlob D g₁ g₂ ∧ r₁ = r₂) := by
  sorry

/-- `local equiv ideal_equiv2 (D <: …) : L2(D, F.RO).distinguish ~
SLCommon.IdealIndif(IF, S, A(D)).main : ={glob D} ==> ={glob D, res}`. -/
theorem ideal_equiv2 (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal D) :
    prhlProc (fun _ g₁ _ g₂ => eqGlob D g₁ g₂)
      (L2 D SLCommon.F.RO.asRO).procedure (SLCommon.IdealIndif Gconcl.IF Gconcl.S (A D)).procedure
      (fun r₁ g₁ r₂ g₂ => eqGlob D g₁ g₂ ∧ r₁ = r₂) := by
  sorry

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

/-- EC's local `L3(D)(F)`: `proc distinguish = SLCommon.IdealIndif(IF2(F, F2.RO), S, A(D)).main`. -/
noncomputable def L3 (D : DISTINGUISHER) (F : SLCommon.F.RO_T) : procmod () → Bool :=
  SLCommon.IdealIndif (Module.app IF2 (Module.pair F F2.RO.asRO)) Gconcl.S (A D)

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

/-- `local equiv Ideal_equiv3 (D <: DISTINGUISHER {-SLCommon.C, -C, -IF, -S, -F2.RO}) :
L(D, F.RO).distinguish ~ L3(D, F.RO).distinguish : ={glob D} ==> ={glob D, res}`. -/
theorem Ideal_equiv3 (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal D) (_hDF2 : FVP.fvP D ≤ (F2.RO.m).footprintᶜ) :
    prhlProc (fun _ g₁ _ g₂ => eqGlob D g₁ g₂)
      (L D SLCommon.F.RO.asRO).procedure (L3 D SLCommon.F.RO.asRO).procedure
      (fun r₁ g₁ r₂ g₂ => eqGlob D g₁ g₂ ∧ r₁ = r₂) := by
  sorry

/-- EC's local `D2(D)(F)`: `proc distinguish = D(FC(DSqueeze(Valid2(F))),
PC(S(Valid2(F)))).distinguish`. -/
noncomputable def D2 (D : DISTINGUISHER) (F : SLCommon.F.RO_T) : procmod () → Bool :=
  Module.app D (Module.pair
    (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
      (Module.app FC (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
        (Module.app DSqueeze (Indifferentiability.FUNCTIONALITY.view state (List block) block
          (Valid2 F))))))
    (Indifferentiability.PRIMITIVE.view state (List block × ℤ) (List block)
      (Module.app PC (Indifferentiability.PRIMITIVE.view state (List block) block
        (Module.app Gconcl.S (Indifferentiability.FUNCTIONALITY.view state (List block) block
          (Valid2 F)))))))

/-- EC's local `D3(D)(F)`: `proc distinguish =
D(FC(DSqueeze(IF'(F))), PC(S(IF'(F)))).distinguish`. -/
noncomputable def D3 (D : DISTINGUISHER) (F : SLCommon.F.RO_T) : procmod () → Bool :=
  Module.app D (Module.pair
    (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
      (Module.app FC (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
        (Module.app DSqueeze (Indifferentiability.FUNCTIONALITY.view state (List block) block
          (IF' F))))))
    (Indifferentiability.PRIMITIVE.view state (List block × ℤ) (List block)
      (Module.app PC (Indifferentiability.PRIMITIVE.view state (List block) block
        (Module.app Gconcl.S (Indifferentiability.FUNCTIONALITY.view state (List block) block
          (IF' F)))))))

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

/-- EC's local `S2(F) = S(Last(F))`. -/
noncomputable def S2 : SIMULATOR := Module.comp Gconcl.S Last

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

/-- `local equiv equiv_L3_L4 : L3(D, F.RO).distinguish ~ L4(D, F.RO, F2.RO).distinguish :
={glob D} ==> ={glob D, res}`. -/
theorem equiv_L3_L4 (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal2 D) :
    prhlProc (fun _ g₁ _ g₂ => eqGlob D g₁ g₂)
      (L3 D SLCommon.F.RO.asRO).procedure (L4 D SLCommon.F.RO.asRO F2.RO.asRO).procedure
      (fun r₁ g₁ r₂ g₂ => eqGlob D g₁ g₂ ∧ r₁ = r₂) := by
  sorry

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

/-- `local equiv equiv_L4_ideal : L4(D, F.LRO, F2.LRO).distinguish ~
IdealIndif(BIRO.IRO, SimLast(S), DRestr(D)).main : ={glob D} ==> ={glob D, res}`. -/
theorem equiv_L4_ideal (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal2 D) :
    prhlProc (fun _ g₁ _ g₂ => eqGlob D g₁ g₂)
      (L4 D SLCommon.F.LRO F2.LRO).procedure
      (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S) (DRestr D)).procedure
      (fun r₁ g₁ r₂ g₂ => eqGlob D g₁ g₂ ∧ r₁ = r₂) := by
  sorry

/-- EC's local `D5(D)(F) = D(FC(FValid(DSqueeze2(F, F2.RO))), PC(S(Last(DSqueeze2(F, F2.RO)))))`. -/
noncomputable def D5 (D : DISTINGUISHER) (F : SLCommon.F.RO_T) : procmod () → Bool :=
  Module.app D (Module.pair
    (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
      (Module.app FC (Module.app FValid
        (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
          (Module.app DSqueeze2 (Module.pair F F2.RO.asRO))))))
    (Indifferentiability.PRIMITIVE.view state (List block × ℤ) (List block)
      (Module.app PC (Indifferentiability.PRIMITIVE.view state (List block) block
        (Module.app Gconcl.S (Module.app Last
          (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
            (Module.app DSqueeze2 (Module.pair F F2.RO.asRO)))))))))

/-- EC's local `D6(D)(F2) = D(FC(FValid(DSqueeze2(F.LRO, F2))),
PC(S(Last(DSqueeze2(F.LRO, F2)))))`. -/
noncomputable def D6 (D : DISTINGUISHER) (F2 : F2.RO_T) : procmod () → Bool :=
  Module.app D (Module.pair
    (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
      (Module.app FC (Module.app FValid
        (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
          (Module.app DSqueeze2 (Module.pair SLCommon.F.LRO F2))))))
    (Indifferentiability.PRIMITIVE.view state (List block × ℤ) (List block)
      (Module.app PC (Indifferentiability.PRIMITIVE.view state (List block) block
        (Module.app Gconcl.S (Module.app Last
          (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
            (Module.app DSqueeze2 (Module.pair SLCommon.F.LRO F2)))))))))

/-- EC's `equiv_ideal`, for `D <: DISTINGUISHER {-SLCommon.C, -C, -IF, -S, -F.FRO, -F2.RO,
-F2.FRO, -BIRO.IRO, -BIRO2.IRO}`. -/
theorem equiv_ideal (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal2 D)
    (_hDd' : FVP.fvP D ≤ ((SLCommon.F.FRO.m).footprint ⊔ (F2.FRO.m).footprint)ᶜ)
    (m : VariableAssignment) :
    Procedure.Pr (SLCommon.IdealIndif Gconcl.IF Gconcl.S (SLCommon.DRestr (A D))).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S) (DRestr D)).procedure ()
        m (fun r _ => r = true) := by
  sorry

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

theorem invmC' (m mi : FMap state state) : invm m mi → invm mi m :=
  fun h x y => (h y x).symm

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

theorem take_nseq {α : Type} (a : α) (i j : ℤ) :
    take j (nseq i a) = if j ≤ i then nseq j a else nseq i a := by
  simp only [take, nseq, List.take_replicate]
  split_ifs <;> congr 1 <;> omega

theorem take_format (bl : List block) (n i : ℤ) :
    0 < n → 0 ≤ i ∧ i < size bl + n →
    take i (format bl n) = if i ≤ size bl then take i bl else format bl (i - size bl + 1) := by
  rintro hn ⟨hi0, his⟩
  simp only [format, take, nseq, size, List.take_append, List.take_replicate] at his ⊢
  split_ifs with h
  · rw [show i.toNat - bl.length = 0 by omega]; simp
  · rw [List.take_of_length_le (by omega)]
    congr 2; omega

/-- `local lemma equiv_sponge (D <: DISTINGUISHER {-P, -Redo, -C, -SLCommon.C}) :
equiv[ GReal(A(D)).main ~ NIndif(Squeeze(SqueezelessSponge(P)), P, DRestr(D)).main : ={glob D} ==>
={res, glob D, glob P, C.c} /\ SLCommon.C.c{1} <= C.c{2} <= max_size ]`. -/
theorem equiv_sponge (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ ((Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (SLCommon.Redo.prefixes).footprint ⊔ BlockSponge.C.c.footprint ⊔ SLCommon.C.footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => eqGlob D g₁ g₂)
      (SLCommon.GReal (A D)).procedure
      (Module.app NIndif (Module.pair (Squeeze (Module.app SLCommon.SqueezelessSponge
        (Indifferentiability.PRIMITIVE.view state (List block) block P))) (Module.pair P
        (DRestr D)))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eqGlob D g₁ g₂ ∧ Perm.m.get g₁ = Perm.m.get g₂ ∧
        Perm.mi.get g₁ = Perm.mi.get g₂ ∧ BlockSponge.C.c.get g₁ = BlockSponge.C.c.get g₂ ∧
        SLCommon.C.c.get g₁ ≤ BlockSponge.C.c.get g₂ ∧ BlockSponge.C.c.get g₂ ≤ max_size) := by
  sorry

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

/-- `local lemma squeeze_squeezeless (D <: DISTINGUISHER {-P, -Redo, -C, -SLCommon.C}) :
equiv[ NIndif(Squeeze(SqueezelessSponge(P)), P, DRestr(D)).main ~ RealIndif(Sponge, P,
DRestr(D)).main : ={glob D} ==> ={res, glob P, glob D, C.c} /\ C.c{1} <= max_size ]`. -/
theorem squeeze_squeezeless (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ ((Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (SLCommon.Redo.prefixes).footprint ⊔ BlockSponge.C.c.footprint ⊔ SLCommon.C.footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => eqGlob D g₁ g₂)
      (Module.app NIndif (Module.pair (Squeeze (Module.app SLCommon.SqueezelessSponge
        (Indifferentiability.PRIMITIVE.view state (List block) block P))) (Module.pair P
        (DRestr D)))).procedure
      (RealIndif Sponge P (DRestr D)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ Perm.m.get g₁ = Perm.m.get g₂ ∧
        Perm.mi.get g₁ = Perm.mi.get g₂ ∧ eqGlob D g₁ g₂ ∧
        BlockSponge.C.c.get g₁ = BlockSponge.C.c.get g₂ ∧ BlockSponge.C.c.get g₁ ≤ max_size) := by
  sorry

/-- EC's `pr_real`, for `D <: DISTINGUISHER {-SLCommon.C, -C, -Perm, -Redo}`. -/
theorem pr_real (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ ((Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (SLCommon.Redo.prefixes).footprint ⊔ BlockSponge.C.c.footprint ⊔ SLCommon.C.footprint)ᶜ)
    (m : VariableAssignment) :
    Procedure.Pr (SLCommon.GReal (A D)).procedure () m
        (fun r g => r = true ∧ SLCommon.C.c.get g ≤ max_size) =
      Procedure.Pr (RealIndif Sponge P (DRestr D)).procedure () m (fun r _ => r = true) := by
  sorry

end Real

/-- The restriction `{-Perm, -F.RO, -F.FRO, -Redo, -SLCommon.C, -S, -BIRO.IRO, -C, -BIRO2.IRO,
-F2.RO, -F2.FRO}` of the last sections (an abbreviation). -/
def DRestrictions_Real_Ideal (D : DISTINGUISHER) : Prop :=
  FVP.fvP D ≤ ((Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ (SLCommon.F.RO.m).footprint ⊔
    (SLCommon.F.FRO.m).footprint ⊔ (SLCommon.Redo.prefixes).footprint ⊔ SLCommon.C.footprint ⊔
    (Gconcl.S.m).footprint ⊔ (Gconcl.S.mi).footprint ⊔ (Gconcl.S.paths).footprint ⊔
    (BlockSponge.BIRO.IRO.mp).footprint ⊔ BlockSponge.C.c.footprint ⊔ (BIRO2.IRO.mp).footprint ⊔
    (F2.RO.m).footprint ⊔ (F2.FRO.m).footprint)ᶜ

/-- `D_lossless`/`D_ll`: `D(F, P).distinguish` is lossless for lossless oracles (an
abbreviation of EasyCrypt's axiom). -/
def D_lossless (D : DISTINGUISHER) : Prop :=
  ∀ (F0 : DFUNCTIONALITY) (P0 : DPRIMITIVE), FVP.fvP F0 ≤ (FVP.fvP D).globᶜ →
    FVP.fvP P0 ≤ (FVP.fvP D).globᶜ →
    (Indifferentiability.DPRIMITIVE.f state (List block × ℤ) (List block) P0).procedure.IsLossless →
    (Indifferentiability.DPRIMITIVE.fi state (List block × ℤ) (List block)
      P0).procedure.IsLossless →
    (Indifferentiability.DFUNCTIONALITY.f state (List block × ℤ) (List block)
      F0).procedure.IsLossless →
    (Module.app D (Module.pair F0 P0)).procedure.IsLossless

/-- The bound of `concl` and `Real_Ideal`. -/
noncomputable def bound : ℝ :=
  ((max_size ^ 2 - max_size : ℤ) : ℝ) / 2 / ((2 ^ r.toNat : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ) +
    (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) +
    (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ))

/-! ## The section `Real_Ideal` -/

section Real_Ideal

/-- EC's `A_lossless`. -/
theorem A_lossless (D : DISTINGUISHER) (_hDd : DRestrictions_Real_Ideal D) :
    D_lossless D →
    ∀ (F : SLCommon.DFUNCTIONALITY) (P0 : SLCommon.DPRIMITIVE),
      FVP.fvP F ≤ (FVP.fvP (A D)).globᶜ →
      FVP.fvP P0 ≤ (FVP.fvP (A D)).globᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P0).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P0).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app (A D) (Module.pair F P0)).procedure.IsLossless := by
  sorry

/-- EC's `concl`. -/
theorem concl (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) :
    D_lossless D → ∀ m : VariableAssignment,
      (Procedure.Pr (RealIndif Sponge P (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) ≤
        (Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S)
          (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) + bound := by
  sorry

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

theorem Neg_D_lossless (D : DISTINGUISHER) (F : DFUNCTIONALITY) (P0 : DPRIMITIVE)
    (_hF : FVP.fvP F ≤ (FVP.fvP (Neg_D D)).globᶜ)
    (_hP : FVP.fvP P0 ≤ (FVP.fvP (Neg_D D)).globᶜ) :
    (Indifferentiability.DPRIMITIVE.f state (List block × ℤ) (List block) P0).procedure.IsLossless →
    (Indifferentiability.DPRIMITIVE.fi state (List block × ℤ) (List block)
      P0).procedure.IsLossless →
    (Indifferentiability.DFUNCTIONALITY.f state (List block × ℤ) (List block)
      F).procedure.IsLossless →
    (Module.app (Neg_D D) (Module.pair F P0)).procedure.IsLossless := by
  sorry

theorem useful (m mi : FMap state state) (a : state) :
    invm m mi → ¬ FMap.dom m a → is_lossless (dexcepted (dprod bdistr cdistr) (FMap.rng m)) :=
  fun _ h => EC.Strong_RP_RF.excepted_lossless state SLCommon.dstate ConcreteF.Switching.uD_uf_fu m
    ⟨a, h⟩

theorem invmC (m mi : FMap state state) : invm m mi ↔ invm mi m :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

theorem Real_lossless (D : DISTINGUISHER) :
    (RealIndif Sponge P (DRestr (Neg_D D))).procedure.IsLossless := by
  sorry

theorem Ideal_lossless (D : DISTINGUISHER) :
    (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S)
      (DRestr (Neg_D D))).procedure.IsLossless := by
  sorry

theorem neg_D_concl (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (_D_lossless : D_lossless D) (m : VariableAssignment) :
    (Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S) (DRestr D)).procedure ()
        m (fun r _ => r = true) : ℝ) ≤
      (Procedure.Pr (RealIndif Sponge P (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) +
        bound := by
  sorry

end Real_Ideal_Abs

/-- EC's `Inefficient_Real_Ideal`. -/
theorem Inefficient_Real_Ideal (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) :
    D_lossless D → ∀ m : VariableAssignment,
      |(Procedure.Pr (RealIndif Sponge Perm (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) -
        (Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S)
          (DRestr D)).procedure () m (fun r _ => r = true) : ℝ)| ≤ bound := by
  sorry

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
/-! The clone is local: its module variable `IRO2.RO.m` is the lens parameter `IRO2_RO_m` of the
local declarations that mention it, fresh by hypothesis (exception E6). -/
variable (IRO2_RO_m : Lens (FMap (List block × ℤ) block) VariableAssignment)
noncomputable abbrev RO.asRO := PROM.FullRO.RO.asRO (List block × ℤ) block dout IRO2_RO_m
noncomputable abbrev LRO := PROM.FullRO.LRO (List block × ℤ) block dout IRO2_RO_m
abbrev RO_T := PROM.FullRO.RO_T (List block × ℤ) block
end IRO2

-- EC's local `Simu(FRO : IRO2.RO)(F : DFUNCTIONALITY)`, with `FRO` a Lean parameter so that
-- `Simu FRO` is a `SIMULATOR`
set_option linter.gaudisCrypt.using false in
module Simu (FRO : IRO2.RO_T) using (F : DFUNCTIONALITY) : PRIMITIVE {
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

/-- EC's local `L(F : IRO2.RO)`: `proc distinguish = IdealIndif(BIRO.IRO, Simu(F), DRestr(D)).main`,
for the section's `D`. -/
noncomputable def L (D : DISTINGUISHER) (F : IRO2.RO_T) : procmod () → Bool :=
  IdealIndif BlockSponge.BIRO.IRO.asF (Simu F) (DRestr D)

/-- What `DRestrictions` excludes (an abbreviation). -/
noncomputable def DRestrictions.footprint : Footprint VariableAssignment :=
  (Simulator.m).footprint ⊔ (Simulator.mi).footprint ⊔ (Simulator.paths).footprint ⊔
    (Simulator.unvalid_map).footprint ⊔ (SLCommon.F.RO.m).footprint ⊔
    (BlockSponge.BIRO.IRO.mp).footprint ⊔ BlockSponge.C.c.footprint ⊔ (Gconcl.S.m).footprint ⊔
    (Gconcl.S.mi).footprint ⊔ (Gconcl.S.paths).footprint ⊔ (BIRO2.IRO.mp).footprint

/-- The section's restriction `{-Simulator, -F.RO, -BIRO.IRO, -C, -S, -BIRO2.IRO}` (an
abbreviation). -/
def DRestrictions (D : DISTINGUISHER) : Prop :=
  FVP.fvP D ≤ DRestrictions.footprintᶜ

theorem equal1 (D : DISTINGUISHER) (hD : Module.ECModule D distExt) (_hDd : DRestrictions D)
    (IRO2_RO_m : Lens (FMap (List block × ℤ) block) VariableAssignment)
    (_hfresh : IRO2_RO_m.footprint ≤ (FVP.fvP D ⊔ DRestrictions.footprint)ᶜ)
    (_D_lossless : D_lossless D) (m : VariableAssignment) :
    Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S) (DRestr D)).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (L D (IRO2.RO.asRO IRO2_RO_m)).procedure () m (fun r _ => r = true) := by
  sorry

theorem equal2 (D : DISTINGUISHER) (hD : Module.ECModule D distExt) (_hDd : DRestrictions D)
    (IRO2_RO_m : Lens (FMap (List block × ℤ) block) VariableAssignment)
    (_hfresh : IRO2_RO_m.footprint ≤ (FVP.fvP D ⊔ DRestrictions.footprint)ᶜ)
    (_D_lossless : D_lossless D) (m : VariableAssignment) :
    Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF Simulator (DRestr D)).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (L D (IRO2.LRO IRO2_RO_m)).procedure () m (fun r _ => r = true) := by
  sorry

end Simplify_Simulator

/-- EC's `Simplify_simulator`. -/
theorem Simplify_simulator (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : Simplify_Simulator.DRestrictions D) :
    D_lossless D → ∀ m : VariableAssignment,
      Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF Simulator (DRestr D)).procedure () m
          (fun r _ => r = true) =
        Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S) (DRestr D)).procedure
          () m (fun r _ => r = true) := by
  sorry

/-- EC's `Real_Ideal`: the block sponge is indifferentiable from the infinite random oracle, with
the simulator `Simulator`. -/
theorem Real_Ideal (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (_hDs : Simplify_Simulator.DRestrictions D) :
    D_lossless D → ∀ m : VariableAssignment,
      |(Procedure.Pr (RealIndif Sponge Perm (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) -
        (Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF Simulator (DRestr D)).procedure () m
          (fun r _ => r = true) : ℝ)| ≤ bound := by
  sorry

end GaudisCrypt.SHA3.Gconcl_list
