import GaudisCrypt.Examples.SHA3.BlockSponge
import GaudisCrypt.Logic.PHoareLossless
import GaudisCrypt.Logic.WritesKeepFrame

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

/-- `={glob D}`: agreement on what `D` may touch (an abbreviation). -/
def eqGlob {M : Type 1} [IsModule M] (D : M) (g₁ g₂ : VariableAssignment) : Prop :=
  (FVP.fvP D).touched_getter.get g₁ = (FVP.fvP D).touched_getter.get g₂

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

/-- The oracles' invariant of the section's equivalences: `={glob S, glob C}` and a relation `R`
between the values of `K₁` (left) and `K₂` (right). -/
def sInv {α β : Type} (K₁ : Lens α VariableAssignment) (K₂ : Lens β VariableAssignment)
    (R : α → β → Prop) (g₁ g₂ : VariableAssignment) : Prop :=
  Gconcl.S.m.get g₁ = Gconcl.S.m.get g₂ ∧ Gconcl.S.mi.get g₁ = Gconcl.S.mi.get g₂ ∧
  Gconcl.S.paths.get g₁ = Gconcl.S.paths.get g₂ ∧ R (K₁.get g₁) (K₂.get g₂) ∧
  BlockSponge.C.c.get g₁ = BlockSponge.C.c.get g₂

/-- The invariant of `Ideal_equiv_valid` and `ideal_equiv2`: `={glob S, glob C, glob F.RO}`. -/
abbrev idInv : VariableAssignment → VariableAssignment → Prop :=
  sInv SLCommon.F.RO.m SLCommon.F.RO.m Eq

/-- Close a goal of equalities and `sInv` left by a wp step: the reads through the writes, then
`simp_all`. -/
macro "id_close" : tactic => `(tactic| (
  intros
  simp only [idInv, sInv] at *
  (try simp_reads)
  simp_all))

/-- `IF'(F.LRO).f ~ Valid2(F.LRO).f` under `idInv` (EC: `inline F.LRO.sample; while{1} (true)
(n{1} - i{1})`: `LRO.sample` does nothing). -/
theorem IF'_Valid2_f :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ idInv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block) block
        (IF' SLCommon.F.LRO)).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block) block
        (Valid2 SLCommon.F.LRO)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ idInv g₁ g₂) := by
  unfold idInv sInv IF' Valid2
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_while{1} (§x0{1} = §x{2} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
      §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧ §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
      §SLCommon.F.RO.m{1} = §SLCommon.F.RO.m{2} ∧ §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
    (§n{1} - §i{1}).toNat
  case lossless =>
    intro σ₁ σ _ _
    simp [Stmt.ewp_seq, Stmt.ewp_assign]
  case «variant» =>
    intro σ₂ k
    hoare_wp 4
    hoare_skip
    rintro x0 m mi paths m1 c i n ⟨h, hc, rfl⟩
    refine ⟨h, ?_⟩
    simp only [decide_eq_true_eq] at hc
    omega
  case exit =>
    rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ - _ -
    and_intros <;> rfl
  stmt_wp
  equiv_skip
  exact fun _ _ _ _ _ _ _ _ _ _ _ _ h => h

/-- `FC(DSqueeze(F₁)).f ~ FC(DSqueeze(F₂)).f` under `sInv`, from `F₁.f ~ F₂.f` (EC: `proc; sp; if;
auto; call (_: ={glob S, glob F.RO})`, the loops in lockstep). -/
theorem FC_f_sInv {α β : Type} {K₁ : Lens α VariableAssignment} {K₂ : Lens β VariableAssignment}
    {R : α → β → Prop} [Lens.Disjoint BlockSponge.C.c K₁] [Lens.Disjoint BlockSponge.C.c K₂]
    {F₁ F₂ : SLCommon.FUNCTIONALITY}
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sInv K₁ K₂ R g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block) block F₁).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block) block F₂).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sInv K₁ K₂ R g₁ g₂)) :
    prhlProc (sig₁ := procsig (List block × ℤ) -> (List block))
      (sig₂ := procsig (List block × ℤ) -> (List block))
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sInv K₁ K₂ R g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app DSqueeze (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
                { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
                    F₁ })) }))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app DSqueeze (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
                { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
                    F₂ })) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sInv K₁ K₂ R g₁ g₂) := by
  unfold sInv
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§bl{1} = §bl{2} ∧ §nb{1} = §nb{2} ∧ §z{1} = §z{2} ∧
      §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
      §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧ §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
      R §K₁{1} §K₂{2} ∧ §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» =>
      equiv_skip
      intros; simp_all
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧
          §b{1} = §b{2} ∧ §i{1} = §i{2} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
      §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧ §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
      R §K₁{1} §K₂{2} ∧ §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
      · stmt_wp
        equiv_skip
        intros; simp_all
      · equiv_if
        case guard => intros; simp_all
        case «else» =>
          equiv_skip
          intros; simp_all
        case «then» =>
          equiv_while (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧
              §b{1} = §b{2} ∧ §i{1} = §i{2} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
      §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧ §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
      R §K₁{1} §K₂{2} ∧ §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
          case body =>
            equiv_seq 1 1 : (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧
                §b{1} = §b{2} ∧ §i{1} = §i{2} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
      §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧ §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
      R §K₁{1} §K₂{2} ∧ §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
            · stmt_wp
              equiv_skip
              intros; simp_all
            · equiv_if
              case guard => intros; simp_all
              case «else» =>
                equiv_skip
                intros; simp_all
              case «then» =>
                equiv_call h
                equiv_skip
                rintro g₁ g₂ p n l b i _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, hE⟩, -⟩
                exact ⟨⟨rfl, hE⟩, fun _ _ _ _ ⟨hr, hE'⟩ => ⟨rfl, rfl, rfl, hr, rfl, hE'⟩⟩
          case guard => intros; simp_all
          case exit => intros; simp_all
          equiv_call h
          equiv_skip
          rintro g₁ g₂ p n l b i _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, hE⟩, -⟩
          exact ⟨⟨rfl, hE⟩, fun _ _ _ _ ⟨hr, hE'⟩ => ⟨rfl, rfl, rfl, hr, rfl, hE'⟩⟩

omit [BlockSponge.Params] [Params] in
/-- `S(F₁).f ~ S(F₂).f` under `sInv`, from `F₁.f ~ F₂.f` (at `S`'s call of `F.f`). -/
theorem S_f_sInv {α β : Type} {K₁ : Lens α VariableAssignment} {K₂ : Lens β VariableAssignment}
    {R : α → β → Prop} [Lens.Disjoint Gconcl.S.m K₁] [Lens.Disjoint Gconcl.S.m K₂]
    [Lens.Disjoint Gconcl.S.mi K₁] [Lens.Disjoint Gconcl.S.mi K₂] [Lens.Disjoint Gconcl.S.paths K₁]
    [Lens.Disjoint Gconcl.S.paths K₂]
    {F₁ F₂ : SLCommon.FUNCTIONALITY}
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sInv K₁ K₂ R g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block) block F₁).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block) block F₂).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sInv K₁ K₂ R g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sInv K₁ K₂ R g₁ g₂)
      (Indifferentiability.PRIMITIVE.f state (List block) block
        (Module.app Gconcl.S (Indifferentiability.FUNCTIONALITY.view state (List block) block
          F₁))).procedure
      (Indifferentiability.PRIMITIVE.f state (List block) block
        (Module.app Gconcl.S (Indifferentiability.FUNCTIONALITY.view state (List block) block
          F₂))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sInv K₁ K₂ R g₁ g₂) := by
  unfold sInv
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
      §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧ §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
      R §K₁{1} §K₂{2} ∧ §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» =>
      stmt_wp
      equiv_skip
      intros; simp_all
    case «then» =>
      equiv_seq 5 5 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
      §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧ §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
      R §K₁{1} §K₂{2} ∧ §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
      · equiv_if
        case guard => intros; simp_all
        case «then» =>
          equiv_call h
          stmt_wp
          equiv_skip
          rintro g₁ g₂ x0 _ ⟨⟨⟨rfl, hE⟩, -⟩, -⟩
          exact ⟨⟨by rw [hE.2.2.1], hE⟩, fun _ _ _ _ ⟨hr, hE'⟩ => ⟨rfl, hr, hE'⟩⟩
        case «else» =>
          equiv_rnd
          equiv_skip
          intros; simp_all
      · stmt_wp
        equiv_rnd
        equiv_skip
        rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, hR, rfl⟩ _ -
        simp only [ite_self]
        and_intros <;> first | rfl | trivial

omit [Params] in
/-- `PC(P).f` keeps `sInv`, from `P.f` (EC: `proc; sp; if; auto; call (_: ={glob S,
glob F.RO})`). -/
theorem PC_f_sInv {α β : Type} {K₁ : Lens α VariableAssignment} {K₂ : Lens β VariableAssignment}
    {R : α → β → Prop} [Lens.Disjoint BlockSponge.C.c K₁] [Lens.Disjoint BlockSponge.C.c K₂]
    {X₁ X₂ Y₁ Y₂ : procmod (state) → state}
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sInv K₁ K₂ R g₁ g₂) X₁.procedure X₂.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sInv K₁ K₂ R g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sInv K₁ K₂ R g₁ g₂)
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := X₁, fi := Y₁ }))).procedure
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := X₂, fi := Y₂ }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sInv K₁ K₂ R g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp]
  stmt_wp
  equiv_seq 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ sInv K₁ K₂ R §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    id_close
  · equiv_if
    case guard => id_close
    case «else» =>
      equiv_skip
      id_close
    case «then» =>
      stmt_wp
      equiv_call h
      equiv_skip
      rintro g₁ g₂ a z _ _ ⟨⟨rfl, -, hE⟩, -⟩
      exact ⟨⟨rfl, hE⟩, fun _ _ _ _ ⟨hr, hE'⟩ => ⟨hr, by id_close⟩⟩

omit [Params] in
/-- `PC(P).fi` keeps `sInv`, from `P.fi` (EC: `proc; sp; if; auto; call (_: ={glob S,
glob F.RO})`). -/
theorem PC_fi_sInv {α β : Type} {K₁ : Lens α VariableAssignment} {K₂ : Lens β VariableAssignment}
    {R : α → β → Prop} [Lens.Disjoint BlockSponge.C.c K₁] [Lens.Disjoint BlockSponge.C.c K₂]
    {X₁ X₂ Y₁ Y₂ : procmod (state) → state}
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sInv K₁ K₂ R g₁ g₂) Y₁.procedure Y₂.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sInv K₁ K₂ R g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sInv K₁ K₂ R g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := X₁, fi := Y₁ }))).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := X₂, fi := Y₂ }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sInv K₁ K₂ R g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.fi.mk_simp]
  stmt_wp
  equiv_seq 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ sInv K₁ K₂ R §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    id_close
  · equiv_if
    case guard => id_close
    case «else» =>
      equiv_skip
      id_close
    case «then» =>
      stmt_wp
      equiv_call h
      equiv_skip
      rintro g₁ g₂ a z _ _ ⟨⟨rfl, -, hE⟩, -⟩
      exact ⟨⟨rfl, hE⟩, fun _ _ _ _ ⟨hr, hE'⟩ => ⟨hr, by id_close⟩⟩

/-- `C.c` equal on both sides and a relation `R` between a lens on each side: the invariant
`PC_f_cInv`, `PC_fi_cInv` lift oracle steps through `PC` with. -/
def cInv {α β : Type} (K₁ : Lens α VariableAssignment) (K₂ : Lens β VariableAssignment)
    (R : α → β → Prop) (g₁ g₂ : VariableAssignment) : Prop :=
  BlockSponge.C.c.get g₁ = BlockSponge.C.c.get g₂ ∧ R (K₁.get g₁) (K₂.get g₂)

/-- Close a side condition about `cInv`. -/
local macro "c_close" : tactic => `(tactic| (
  intros
  (try simp only [cInv] at *)
  (try simp_reads)
  (try simp_all)))

omit [Params] in
/-- `PC(P).f` keeps `cInv`, from `P.f` (as `PC_f_sInv`). -/
theorem PC_f_cInv {α β : Type} {K₁ : Lens α VariableAssignment} {K₂ : Lens β VariableAssignment}
    {R : α → β → Prop} [Lens.Disjoint BlockSponge.C.c K₁] [Lens.Disjoint BlockSponge.C.c K₂]
    {X₁ X₂ Y₁ Y₂ : procmod (state) → state}
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ cInv K₁ K₂ R g₁ g₂) X₁.procedure X₂.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ cInv K₁ K₂ R g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ cInv K₁ K₂ R g₁ g₂)
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := X₁, fi := Y₁ }))).procedure
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := X₂, fi := Y₂ }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ cInv K₁ K₂ R g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp]
  stmt_wp
  equiv_seq 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ cInv K₁ K₂ R §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    c_close
  · equiv_if
    case guard => c_close
    case «else» =>
      equiv_skip
      c_close
    case «then» =>
      stmt_wp
      equiv_call h
      equiv_skip
      rintro g₁ g₂ a z _ _ ⟨⟨rfl, -, hE⟩, -⟩
      exact ⟨⟨rfl, hE⟩, fun _ _ _ _ ⟨hr, hE'⟩ => ⟨hr, by c_close⟩⟩

omit [Params] in
/-- `PC(P).fi` keeps `cInv`, from `P.fi` (as `PC_fi_sInv`). -/
theorem PC_fi_cInv {α β : Type} {K₁ : Lens α VariableAssignment} {K₂ : Lens β VariableAssignment}
    {R : α → β → Prop} [Lens.Disjoint BlockSponge.C.c K₁] [Lens.Disjoint BlockSponge.C.c K₂]
    {X₁ X₂ Y₁ Y₂ : procmod (state) → state}
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ cInv K₁ K₂ R g₁ g₂) Y₁.procedure Y₂.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ cInv K₁ K₂ R g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ cInv K₁ K₂ R g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := X₁, fi := Y₁ }))).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := X₂, fi := Y₂ }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ cInv K₁ K₂ R g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.fi.mk_simp]
  stmt_wp
  equiv_seq 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ cInv K₁ K₂ R §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    c_close
  · equiv_if
    case guard => c_close
    case «else» =>
      equiv_skip
      c_close
    case «then» =>
      stmt_wp
      equiv_call h
      equiv_skip
      rintro g₁ g₂ a z _ _ ⟨⟨rfl, -, hE⟩, -⟩
      exact ⟨⟨rfl, hE⟩, fun _ _ _ _ ⟨hr, hE'⟩ => ⟨hr, by c_close⟩⟩

omit [BlockSponge.Params] [Params] in
/-- `S(F₁).fi ~ S(F₂).fi`: `S.fi` does not call `F` (EC: `sim`). -/
theorem S_fi_sInv {α β : Type} {K₁ : Lens α VariableAssignment} {K₂ : Lens β VariableAssignment}
    {R : α → β → Prop} [Lens.Disjoint Gconcl.S.m K₁] [Lens.Disjoint Gconcl.S.m K₂]
    [Lens.Disjoint Gconcl.S.mi K₁] [Lens.Disjoint Gconcl.S.mi K₂] [Lens.Disjoint Gconcl.S.paths K₁]
    [Lens.Disjoint Gconcl.S.paths K₂]
    {F₁ F₂ : SLCommon.FUNCTIONALITY} :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sInv K₁ K₂ R g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi state (List block) block
        (Module.app Gconcl.S (Indifferentiability.FUNCTIONALITY.view state (List block) block
          F₁))).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block) block
        (Module.app Gconcl.S (Indifferentiability.FUNCTIONALITY.view state (List block) block
          F₂))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sInv K₁ K₂ R g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ sInv K₁ K₂ R §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    id_close
  · equiv_if
    case guard => id_close
    case «else» =>
      stmt_wp
      equiv_skip
      id_close
    case «then» =>
      stmt_wp
      equiv_rnd
      equiv_rnd
      equiv_skip
      id_close

omit [BlockSponge.Params] [Params] in
/-- `format p 1 = p`. -/
theorem format_one (p : List block) : format p 1 = p := by simp [format, nseq]

omit [SLCommon.Params] [BlockSponge.Params] [Params] in
theorem size_nonneg' {α : Type} (s : List α) : 0 ≤ size s := by simp [size]

omit [BlockSponge.Params] [Params] in
theorem get_eq_some_oget {m : FMap (List block) block} {x : List block} (h : FMap.dom m x) :
    FMap.get m x = some (oget (FMap.get m x)) := by
  rw [FMap.domE] at h
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
  rw [hv]; rfl

omit [BlockSponge.Params] [Params] in
/-- `m1 <= m2` gives `m2` the non-empty keys of `m1`, with their values. -/
theorem leq_dom {q m : FMap (List block) block} (h : «<=» q m) {x : List block} (hx : x ≠ [])
    (hd : FMap.dom q x) : FMap.dom m x ∧ FMap.get m x = FMap.get q x := by
  have he := h x hx hd
  refine ⟨?_, he.symm⟩
  rw [FMap.domE] at hd ⊢
  rwa [← he]

omit [BlockSponge.Params] [Params] in
/-- `bdistr` is lossless, as an expectation. -/
theorem bdistr_expected_one : bdistr.expected (fun _ => (1 : ENNReal)) = 1 :=
  (is_lossless_iff_expected bdistr).mp BitWord.dunifin_ll

omit [BlockSponge.Params] [Params] in
theorem format_ne_nil {p : List block} (hp : p ≠ []) (k : ℤ) : format p k ≠ [] := by
  simp [format, hp]

/-- After `format p i`, `format p (i + 1)` costs at most one block (`prefix_le1`). -/
theorem cost_le1 (p : List block) (q : FMap (List block) block) (i : ℤ) (hi : 1 ≤ i)
    (hd : FMap.dom q (format p i)) :
    size (format p (i + 1)) - «prefix» (format p (i + 1))
      (get_max_prefix (format p (i + 1)) (elems (FMap.fdom q))) ≤ 1 := by
  have h := prefix_le1 p q (i - 1) (by omega) (by simpa using hd)
  simpa using h

/-- `ideal_equiv`'s invariant: `={glob IF, glob S, glob A} /\ SLCommon.C.c{1} <= C.c{1} /\
SLCommon.C.queries{1} <= F.RO.m{2}`. -/
abbrev ieInv := sInv (Lens.pair SLCommon.F.RO.m (Lens.pair BlockSponge.C.c
  (Lens.pair SLCommon.C.c SLCommon.C.queries))) SLCommon.F.RO.m
  (fun x y => x.1 = y ∧ x.2.2.1 ≤ x.2.1 ∧ «<=» x.2.2.2 y)

/-- Close a goal of equalities and `ieInv` left by a wp step. -/
macro "ie_close" : tactic => `(tactic| (
  intros
  (try simp only [ieInv, sInv, Lens.pair] at *)
  (try simp_reads)
  (try simp_all)
  try omega))

/-- `IF.f ~ IF.f` under `ieInv` (`F.RO.get` on both sides; `C.queries <= F.RO.m` kept by
`leq_add_nin`). -/
theorem IF_f_ie :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ieInv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block) block Gconcl.IF).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block) block Gconcl.IF).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ieInv g₁ g₂) := by
  unfold Gconcl.IF
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x _ ⟨rfl, h⟩ a -
  simp only [ieInv, sInv, Lens.pair] at h ⊢
  obtain ⟨e1, e2, e3, ⟨hro, hc, hq⟩, e5⟩ := h
  rw [hro]
  by_cases hd : FMap.dom (SLCommon.F.RO.m.get g₂) x
  · simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
    and_intros <;> trivial
  · simp only [hd, decide_false, Bool.not_false, if_true]
    simp_reads
    exact ⟨e1, e2, e3, ⟨hc, leq_add_nin _ _ _ _ hq hd⟩, e5⟩

omit [Params] in
/-- `PC(DPRestr(P)).f ~ PC(P).f` under `ieInv`, from `P.f ~ P.f` (EC: `proc; inline*; sp; if; auto;
sp; rcondt{1} 1`: `SLCommon.C.c <= C.c` makes `DPRestr`'s test pass). -/
theorem PC_DPRestr_f {X Y : procmod (state) → state}
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ieInv g₁ g₂) X.procedure X.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ieInv g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ieInv g₁ g₂)
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.DPRIMITIVE.f state (List block) block
              (Module.app SLCommon.DPRestr (Indifferentiability.DPRIMITIVE.mk state (List block)
                  block
                { f := X, fi := Y })),
            fi := Indifferentiability.DPRIMITIVE.fi state (List block) block
              (Module.app SLCommon.DPRestr (Indifferentiability.DPRIMITIVE.mk state (List block)
                  block
                { f := X, fi := Y })) }))).procedure
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := X, fi := Y }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ieInv g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp]
  stmt_inline{1} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp]
  stmt_wp
  equiv_seq 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ ieInv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    ie_close
  · equiv_if
    case guard => ie_close
    case «else» =>
      equiv_skip
      ie_close
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§x0{1} = §a{2} ∧ ieInv §allGlobals{1} §allGlobals{2} ∧
          §BlockSponge.C.c{1} + 1 ≤ max_size)
      · stmt_wp
        equiv_skip
        ie_close
      · equiv_if{1}
        case «then» =>
          stmt_wp
          equiv_call h
          equiv_skip
          rintro g₁ g₂ x0 a ⟨⟨rfl, hI, -⟩, -⟩
          exact ⟨⟨rfl, hI⟩, fun _ _ _ _ ⟨hr, hI'⟩ => ⟨hr, by ie_close⟩⟩
        case «else» =>
          refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
          obtain ⟨⟨-, hI, hb⟩, hs⟩ := h
          simp only [ieInv, sInv, Lens.pair, decide_eq_false_iff_not] at hI hs
          omega


omit [Params] in
/-- `PC(DPRestr(P)).fi ~ PC(P).fi` under `ieInv`,
    from `P.fi ~ P.fi` (EC: `proc; inline*; sp; if; auto;
sp; rcondt{1} 1`: `SLCommon.C.c <= C.c` makes `DPRestr`'s test pass). -/
theorem PC_DPRestr_fi {X Y : procmod (state) → state}
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ieInv g₁ g₂) Y.procedure Y.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ieInv g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ieInv g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.DPRIMITIVE.f state (List block) block
              (Module.app SLCommon.DPRestr (Indifferentiability.DPRIMITIVE.mk state (List block)
                  block
                { f := X, fi := Y })),
            fi := Indifferentiability.DPRIMITIVE.fi state (List block) block
              (Module.app SLCommon.DPRestr (Indifferentiability.DPRIMITIVE.mk state (List block)
                  block
                { f := X, fi := Y })) }))).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := X, fi := Y }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ieInv g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.fi.mk_simp]
  stmt_inline{1} 0
  simp only [Indifferentiability.DPRIMITIVE.fi.mk_simp]
  stmt_wp
  equiv_seq 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ ieInv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    ie_close
  · equiv_if
    case guard => ie_close
    case «else» =>
      equiv_skip
      ie_close
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§x0{1} = §a{2} ∧ ieInv §allGlobals{1} §allGlobals{2} ∧
          §BlockSponge.C.c{1} + 1 ≤ max_size)
      · stmt_wp
        equiv_skip
        ie_close
      · equiv_if{1}
        case «then» =>
          stmt_wp
          equiv_call h
          equiv_skip
          rintro g₁ g₂ x0 a ⟨⟨rfl, hI, -⟩, -⟩
          exact ⟨⟨rfl, hI⟩, fun _ _ _ _ ⟨hr, hI'⟩ => ⟨hr, by ie_close⟩⟩
        case «else» =>
          refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
          obtain ⟨⟨-, hI, hb⟩, hs⟩ := h
          simp only [ieInv, sInv, Lens.pair, decide_eq_false_iff_not] at hI hs
          omega


set_option maxHeartbeats 4000000 in
-- the inlined loops' wp goals are large
/-- `FC(DSqueeze(DFRestr(IF))).f ~ FC(DSqueeze(IF)).f` under `ieInv`.  EC: `splitwhile` and
`rcondt` over the loop; here one loop invariant, `SLCommon.C.c + max (n - 1 - i) 0 <= C.c` and
`i < n => SLCommon.C.queries.[format p (i + 1)] = Some b`, makes `DFRestr`'s test pass (`cost_le1`),
and `C.queries <= F.RO.m` answers its cached queries as `F.RO.get` does. -/
theorem FC_DSqueeze_DFRestr_f :
    prhlProc (sig₁ := procsig (List block × ℤ) -> (List block))
      (sig₂ := procsig (List block × ℤ) -> (List block))
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ ieInv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app DSqueeze (Module.app SLCommon.DFRestr
                (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
                  { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
                      Gconcl.IF }))) }))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app DSqueeze (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
                { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
                    Gconcl.IF })) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ ieInv g₁ g₂) := by
  unfold Gconcl.IF
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§bl{1} = §bl{2} ∧ §nb{1} = §nb{2} ∧ §z{1} = §z{2} ∧
      ieInv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    (rintro g₁ g₂ x _ ⟨rfl, h⟩; exact ⟨rfl, rfl, h⟩)
  · equiv_if
    case guard =>
      rintro g₁ g₂ bl nb z _ _ _ ⟨rfl, rfl, rfl, h⟩
      simp only [ieInv, sInv, Lens.pair] at h
      rw [h.2.2.2.2]
    case «else» =>
      equiv_skip
      (rintro g₁ g₂ bl nb z _ _ _ ⟨⟨rfl, rfl, rfl, h⟩, -⟩; exact ⟨rfl, h⟩)
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧ §i{1} = §i{2} ∧
          §i{1} = 0 ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
            §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧ §SLCommon.F.RO.m{1} = §SLCommon.F.RO.m{2} ∧
            §BlockSponge.C.c{1} = §BlockSponge.C.c{2} ∧
            «<=» §SLCommon.C.queries{1} §SLCommon.F.RO.m{2} ∧ §BlockSponge.C.c{1} ≤ max_size ∧
          §SLCommon.C.c{1} + size §p{1} + max (§n{1} - 1) 0 ≤ §BlockSponge.C.c{1})
      · stmt_wp
        equiv_skip
        rintro g₁ g₂ bl nb z _ _ _ ⟨⟨rfl, rfl, rfl, h⟩, hg⟩
        simp only [ieInv, sInv, Lens.pair] at h
        simp only [decide_eq_true_eq] at hg
        obtain ⟨e1, e2, e3, ⟨hro, hc, hq⟩, e5⟩ := h
        exact ⟨rfl, rfl, e1, e2, e3, hro, by rw [e5], hq, hg, by linarith⟩
      · equiv_if
        case guard => intros; simp_all
        case «else» =>
          equiv_skip
          rintro g₁ g₂ p n l i _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, -, e1, e2, e3, hro, e5, hq, hb, hs⟩, -⟩
          refine ⟨rfl, ?_⟩
          simp only [ieInv, sInv, Lens.pair]
          exact ⟨e1, e2, e3, ⟨hro, by linarith [size_nonneg' p, le_max_right (n - 1) 0], hq⟩, e5⟩
        case «then» =>
          equiv_seq 1 1 : (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧ §i{1} = §i{2} ∧
            §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧ 0 ≤ §i{1} ∧
            valid §p{1} = true ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
                §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
            §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧ §SLCommon.F.RO.m{1} = §SLCommon.F.RO.m{2} ∧
            §BlockSponge.C.c{1} = §BlockSponge.C.c{2} ∧
            «<=» §SLCommon.C.queries{1} §SLCommon.F.RO.m{2} ∧ §BlockSponge.C.c{1} ≤ max_size ∧
            §SLCommon.C.c{1} + max (§n{1} - 1 - §i{1}) 0 ≤ §BlockSponge.C.c{1} ∧
            (§i{1} < §n{1} → FMap.get §SLCommon.C.queries{1} (format §p{1} (§i{1} + 1)) =
              some §(localVarLens "b" block){1}))
          · stmt_wp
            equiv_seq 1 1 : (§bs{1} = §p{1} ∧ §x2{2} = §p{2} ∧ §p{1} = §p{2} ∧ §n{1} = §n{2} ∧
                §lres{1} = §lres{2} ∧ §i{1} = §i{2} ∧ §i{1} = 0 ∧ valid §p{1} = true ∧
                    §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
            §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧ §SLCommon.F.RO.m{1} = §SLCommon.F.RO.m{2} ∧
            §BlockSponge.C.c{1} = §BlockSponge.C.c{2} ∧
            «<=» §SLCommon.C.queries{1} §SLCommon.F.RO.m{2} ∧ §BlockSponge.C.c{1} ≤ max_size ∧
                §SLCommon.C.c{1} + size §p{1} + max (§n{1} - 1) 0 ≤ §BlockSponge.C.c{1})
            · stmt_wp
              equiv_skip
              rintro p n l i m mi paths ro c q sc _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, h0,
                  rfl, rfl, rfl, rfl, rfl, hq, hb, hs⟩, hv⟩
              exact ⟨rfl, rfl, rfl, rfl, h0, hv, rfl, rfl, rfl, rfl, rfl, hq, hb, hs⟩
            · equiv_if{1}
              case «then» =>
                equiv_if{1}
                case «then» =>
                  stmt_wp
                  equiv_rnd
                  stmt_wp
                  equiv_skip
                  rintro p p' n l i m mi paths ro c q sc _ _ _ _ _ _ _ _ _ _
                    ⟨⟨⟨hpp, rfl, rfl, rfl, rfl, rfl, rfl, hv, rfl, rfl, rfl, rfl, rfl, hq, hb,
                        hs⟩, hnd⟩, hg⟩ a -
                  subst hpp
                  have hpre := prefix_ge0 p (get_max_prefix p (elems (FMap.fdom q)))
                  have hmx := le_max_right (n - 1) 0
                  simp only [ite_self, sub_zero]
                  by_cases hd : FMap.dom ro p
                  · simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
                    refine ⟨trivial, trivial, trivial, trivial, trivial, le_refl _, hv, trivial,
                        trivial,
                      trivial, trivial, trivial, leq_add_in _ _ _ hq hd, hb, by linarith,
                          fun _ => ?_⟩
                    simp [format_one, FMap.get_set_sameE, oget]
                  · simp only [hd, decide_false, Bool.not_false, if_true, FMap.get_set_sameE]
                    refine ⟨trivial, trivial, trivial, trivial, trivial, le_refl _, hv, trivial,
                        trivial,
                      trivial, trivial, trivial, leq_add2 _ _ _ _ hq hd, hb, by linarith,
                          fun _ => ?_⟩
                    simp [format_one, FMap.get_set_sameE, oget]
                case «else» =>
                  refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
                  obtain ⟨⟨⟨hbs, -, -, -, -, -, -, -, -, -, -, -, -, -, hb, hs⟩, -⟩, hg⟩ := h
                  simp only [decide_eq_false_iff_not, not_le] at hg
                  rw [hbs] at hg
                  linarith [prefix_ge0 ((localVarLens "p" (List block)).get σ₁)
                    (get_max_prefix ((localVarLens "p" (List block)).get σ₁)
                      (elems (SLCommon.C.queries.get σ₁.globals).fdom)), le_max_right
                    ((localVarLens "n" ℤ).get σ₁ - 1) 0]
              case «else» =>
                stmt_wp
                stmt_wp{2} 1
                equiv_skip
                rintro p p' n l i m mi paths ro c q sc _ _ _ _ _ _ _ _ _ _
                  ⟨⟨hpp, rfl, rfl, rfl, rfl, rfl, rfl, hv, rfl, rfl, rfl, rfl, rfl, hq, hb, hs⟩, hd⟩
                subst hpp
                simp only [Bool.not_eq_false', decide_eq_true_eq] at hd
                obtain ⟨hdr, hget⟩ := leq_dom hq (valid_spec p hv) hd
                refine ⟨bdistr_expected_one, fun a _ => ?_⟩
                simp only [hdr, decide_true, Bool.not_true, Bool.false_eq_true, if_false,
                    sub_zero, hget]
                and_intros <;> first | rfl | trivial | assumption |
                  linarith [size_nonneg' p, le_max_right (n - 1) 0] |
                  (intro; rw [zero_add, format_one]; exact get_eq_some_oget hd)
          · equiv_while (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧ §i{1} = §i{2} ∧
            §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧ 0 ≤ §i{1} ∧
            valid §p{1} = true ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
                §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
            §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧ §SLCommon.F.RO.m{1} = §SLCommon.F.RO.m{2} ∧
            §BlockSponge.C.c{1} = §BlockSponge.C.c{2} ∧
            «<=» §SLCommon.C.queries{1} §SLCommon.F.RO.m{2} ∧ §BlockSponge.C.c{1} ≤ max_size ∧
            §SLCommon.C.c{1} + max (§n{1} - 1 - §i{1}) 0 ≤ §BlockSponge.C.c{1} ∧
            (§i{1} < §n{1} → FMap.get §SLCommon.C.queries{1} (format §p{1} (§i{1} + 1)) =
              some §(localVarLens "b" block){1}))
            case body =>
              equiv_seq 1 1 : (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧ §i{1} = §i{2} ∧
                  §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧ 1 ≤ §i{1} ∧
                  §i{1} ≤ §n{1} ∧ valid §p{1} = true ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
                      §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
                  §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
                      §SLCommon.F.RO.m{1} = §SLCommon.F.RO.m{2} ∧
                  §BlockSponge.C.c{1} = §BlockSponge.C.c{2} ∧
                  «<=» §SLCommon.C.queries{1} §SLCommon.F.RO.m{2} ∧ §BlockSponge.C.c{1} ≤ max_size ∧
                  §SLCommon.C.c{1} + (§n{1} - §i{1}) ≤ §BlockSponge.C.c{1} ∧
                  FMap.get §SLCommon.C.queries{1} (format §p{1} §i{1}) =
                    some §(localVarLens "b" block){1})
              · stmt_wp
                equiv_skip
                rintro p n l i b m mi paths ro c q sc _ _ _ _ _ _ _ _ _ _
                  ⟨⟨rfl, rfl, rfl, rfl, rfl, hi, hv, rfl, rfl, rfl, rfl, rfl, hq, hb, hs, hf⟩, hg⟩
                simp only [decide_eq_true_eq] at hg
                rw [max_eq_left (by omega : 0 ≤ n - 1 - i)] at hs
                exact ⟨rfl, rfl, rfl, rfl, rfl, by omega, by omega, hv, rfl, rfl, rfl, rfl, rfl,
                    hq, hb,
                  by linarith, hf hg⟩
              · equiv_if
                case guard =>
                  rintro p n l i b m mi paths ro c q sc _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, -⟩
                  rfl
                case «else» =>
                  equiv_skip
                  rintro p n l i b m mi paths ro c q sc _ _ _ _ _ _ _ _ _ _
                    ⟨⟨rfl, rfl, rfl, rfl, rfl, hi, hin, hv, rfl, rfl, rfl, rfl, rfl, hq, hb, hs,
                        -⟩, hg⟩
                  simp only [decide_eq_false_iff_not, not_lt] at hg
                  rw [max_eq_right (by omega : n - 1 - i ≤ 0)]
                  exact ⟨rfl, rfl, rfl, rfl, rfl, by omega, hv, rfl, rfl, rfl, rfl, rfl, hq, hb,
                      by linarith,
                    fun h => absurd h (by omega)⟩
                case «then» =>
                  stmt_wp
                  equiv_seq 1 1 : (§bs0{1} = format §p{1} (§i{1} + 1) ∧
                      §x3{2} = format §p{2} (§i{2} + 1) ∧
                      §p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧ §i{1} = §i{2} ∧
                      1 ≤ §i{1} ∧ §i{1} < §n{1} ∧ valid §p{1} = true ∧
                          §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
                  §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
                      §SLCommon.F.RO.m{1} = §SLCommon.F.RO.m{2} ∧
                  §BlockSponge.C.c{1} = §BlockSponge.C.c{2} ∧
                  «<=» §SLCommon.C.queries{1} §SLCommon.F.RO.m{2} ∧ §BlockSponge.C.c{1} ≤ max_size ∧
                      §SLCommon.C.c{1} + (§n{1} - §i{1}) ≤ §BlockSponge.C.c{1} ∧
                      FMap.dom §SLCommon.C.queries{1} (format §p{1} §i{1}))
                  · stmt_wp
                    equiv_skip
                    rintro p n l i b m mi paths ro c q sc _ _ _ _ _ _ _ _ _ _
                      ⟨⟨rfl, rfl, rfl, rfl, rfl, hi, hin, hv, rfl, rfl, rfl, rfl, rfl, hq, hb,
                          hs, hf⟩, hg⟩
                    simp only [decide_eq_true_eq] at hg
                    exact ⟨rfl, rfl, rfl, rfl, hi, hg, hv, rfl, rfl, rfl, rfl, rfl, hq, hb, hs,
                      (FMap.domE _ _).mpr (by rw [hf]; simp)⟩
                  · equiv_if{1}
                    case «then» =>
                      equiv_if{1}
                      case «then» =>
                        stmt_wp
                        equiv_rnd
                        stmt_wp
                        equiv_skip
                        rintro bs p i n l m mi paths ro c q sc _ _ _ _ _ _ _ _ _ _
                          ⟨⟨⟨rfl, hx3, rfl, rfl, rfl, rfl, hi, hin, hv, rfl, rfl, rfl, rfl, rfl,
                              hq, hb, hs, hdq⟩, -⟩,
                          -⟩ a -
                        subst hx3
                        have hc1 := cost_le1 p q i hi hdq
                        simp only [ite_self]
                        rw [max_eq_left (by omega : 0 ≤ n - 1 - i)]
                        by_cases hd : FMap.dom ro (format p (i + 1))
                        · simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
                          refine ⟨trivial, trivial, trivial, trivial, trivial, by omega, hv,
                              trivial, trivial,
                            trivial, trivial, trivial, leq_add_in _ _ _ hq hd, hb, by linarith,
                                fun _ => ?_⟩
                          simp [FMap.get_set_sameE, oget]
                        · simp only [hd, decide_false, Bool.not_false, if_true, FMap.get_set_sameE]
                          exact ⟨trivial, trivial, trivial, trivial, trivial, by omega, hv,
                              trivial, trivial,
                            trivial, trivial, trivial, leq_add2 _ _ _ _ hq hd, hb, by linarith,
                                fun _ => trivial⟩
                      case «else» =>
                        refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
                        obtain ⟨⟨⟨hbs, -, -, -, -, -, hi, hin, -, -, -, -, -, -, -, hb, hs, hdq⟩,
                            -⟩, hg⟩ := h
                        simp only [decide_eq_false_iff_not, not_le] at hg
                        rw [hbs] at hg
                        have := cost_le1 _ _ _ hi hdq
                        linarith
                    case «else» =>
                      stmt_wp
                      stmt_wp{2} 1
                      equiv_skip
                      rintro bs p i n l m mi paths ro c q sc _ _ _ _ _ _ _ _ _ _
                        ⟨⟨rfl, hx3, rfl, rfl, rfl, rfl, hi, hin, hv, rfl, rfl, rfl, rfl, rfl, hq,
                            hb, hs, hdq⟩, hd⟩
                      subst hx3
                      simp only [Bool.not_eq_false', decide_eq_true_eq] at hd
                      obtain ⟨hdr, hget⟩ := leq_dom hq (format_ne_nil (valid_spec p hv) _) hd
                      refine ⟨bdistr_expected_one, fun a _ => ?_⟩
                      simp only [hdr, decide_true, Bool.not_true, Bool.false_eq_true, if_false,
                          hget]
                      rw [max_eq_left (by omega : 0 ≤ n - 1 - i)]
                      and_intros <;> first | rfl | trivial | assumption | omega | linarith |
                        (intro; exact get_eq_some_oget hd)
            case guard => intros; simp_all
            case exit =>
              rintro g₁ g₂ p n l i b _ _ _ _ _
                ⟨rfl, rfl, rfl, rfl, rfl, hi, hv, e1, e2, e3, hro, e5, hq, hb, hs, -⟩ hg
              simp only [decide_eq_false_iff_not, not_lt] at hg
              refine ⟨rfl, ?_⟩
              simp only [ieInv, sInv, Lens.pair]
              exact ⟨e1, e2, e3, ⟨hro, by linarith [le_max_right (n - 1 - i) 0], hq⟩, e5⟩
            equiv_skip
            intros; assumption

set_option maxHeartbeats 4000000 in
-- the oracles' footprint checks through the nested wrappers
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
  have hsm : (Gconcl.S.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_mem)))
  have hsmi : (Gconcl.S.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_mem)))
  have hspa : (Gconcl.S.paths).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_mem)))
  have hro : (SLCommon.F.RO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_mem)))
  have hcc : (BlockSponge.C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_mem)))
  have hsc : (SLCommon.C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      unfold SLCommon.C.footprint; fp_mem)))
  have hsq : (SLCommon.C.queries).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by
      unfold SLCommon.C.footprint; fp_mem)))
  let Lg := Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi (Lens.pair Gconcl.S.paths
    (Lens.pair SLCommon.F.RO.m (Lens.pair BlockSponge.C.c (Lens.pair SLCommon.C.c
      SLCommon.C.queries)))))
  let I : SLCommon.smap × SLCommon.smap × FMap capacity (List block × block) ×
      FMap (List block) block × ℤ × ℤ × FMap (List block) block →
      SLCommon.smap × SLCommon.smap × FMap capacity (List block × block) ×
      FMap (List block) block × ℤ × ℤ × FMap (List block) block → Prop := fun x y =>
    x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧
      (x.2.2.2.1 = y.2.2.2.1 ∧ x.2.2.2.2.2.1 ≤ x.2.2.2.2.1 ∧ «<=» x.2.2.2.2.2.2 y.2.2.2.1) ∧
      x.2.2.2.2.1 = y.2.2.2.2.1
  have hI : ∀ g₁ g₂, I (Lg.get g₁) (Lg.get g₂) ↔ ieInv g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (Lg.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [Lg, Footprint.lens_pair]
    exact sup_le hsm (sup_le hsmi (sup_le hspa (sup_le hro (sup_le hcc (sup_le hsc hsq)))))
  unfold SLCommon.IdealIndif Indifferentiability.GIdeal
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    refine ⟨?_, (hI _ _).mpr ?_⟩
    · simp only [touched_set_of_le_compl hsm, touched_set_of_le_compl hsmi,
        touched_set_of_le_compl hspa, touched_set_of_le_compl hro, touched_set_of_le_compl hcc,
        touched_set_of_le_compl hsc, touched_set_of_le_compl hsq]
      exact h
    · simp only [ieInv, sInv, Lens.pair]
      simp_reads
      refine fun x hx hd => absurd ((FMap.mem_set _ _ _ _).mp hd) ?_
      rintro (h | rfl)
      · exact FMap.mem_empty _ h
      · exact hx rfl
  · stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_moduleF Lg D distExt hD.representable
      (FVP.fvP D) le_rfl hL I ?hc _ _ ?horacle) ?_
    case hc =>
      intro _ n
      cases n with
      | zero => exact inferInstanceAs (Countable (List block × ℤ))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable state)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable state)
          | succ n => nomatch n
    case horacle =>
      intro _ n
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair, Indifferentiability.DFUNCTIONALITY.f.mk_simp]
        exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
          FC_DSqueeze_DFRestr_f
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
            (PC_DPRestr_f (S_f_sInv IF_f_ie))
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
              Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              (PC_DPRestr_fi (S_fi_sInv (K₁ := Lens.pair SLCommon.F.RO.m (Lens.pair BlockSponge.C.c
                (Lens.pair SLCommon.C.c SLCommon.C.queries))) (K₂ := SLCommon.F.RO.m)
                (R := fun x y => x.1 = y ∧ x.2.2.1 ≤ x.2.1 ∧ «<=» x.2.2.2 y)))
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, hg, -⟩
    refine ⟨?_, ?_⟩
    · simp_reads
      exact hg
    · simp_reads
      trivial

set_option maxHeartbeats 4000000 in
-- the oracles' footprint checks through the nested wrappers
/-- `local equiv Ideal_equiv_valid (D <: DISTINGUISHER {-SLCommon.C, -C, -IF, -S}) :
L(D, F.LRO).distinguish ~ L2(D, F.LRO).distinguish : ={glob D} ==> ={glob D, res}`. -/
theorem Ideal_equiv_valid (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal D) :
    prhlProc (fun _ g₁ _ g₂ => eqGlob D g₁ g₂)
      (L D SLCommon.F.LRO).procedure (L2 D SLCommon.F.LRO).procedure
      (fun r₁ g₁ r₂ g₂ => eqGlob D g₁ g₂ ∧ r₁ = r₂) := by
  have hsm : (Gconcl.S.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hsmi : (Gconcl.S.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hspa : (Gconcl.S.paths).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hro : (SLCommon.F.RO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hcc : (BlockSponge.C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  let Lg := Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi (Lens.pair Gconcl.S.paths
    (Lens.pair SLCommon.F.RO.m BlockSponge.C.c)))
  let I : SLCommon.smap × SLCommon.smap × FMap capacity (List block × block) ×
      FMap (List block) block × ℤ → SLCommon.smap × SLCommon.smap ×
      FMap capacity (List block × block) × FMap (List block) block × ℤ → Prop := fun x y =>
    x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧ x.2.2.2.2 = y.2.2.2.2
  have hI : ∀ g₁ g₂, I (Lg.get g₁) (Lg.get g₂) ↔ idInv g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (Lg.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [Lg, Footprint.lens_pair]
    exact sup_le hsm (sup_le hsmi (sup_le hspa (sup_le hro hcc)))
  unfold L L2 SLCommon.IdealIndif Indifferentiability.GIdeal
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    refine ⟨?_, (hI _ _).mpr ?_⟩
    · simp only [touched_set_of_le_compl hsm, touched_set_of_le_compl hsmi,
        touched_set_of_le_compl hspa, touched_set_of_le_compl hro, touched_set_of_le_compl hcc]
      exact h
    · simp only [idInv, sInv]
      simp_reads
      trivial
  · stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_moduleF Lg D distExt hD.representable
      (FVP.fvP D) le_rfl hL I ?hc _ _ ?horacle) ?_
    case hc =>
      intro _ n
      cases n with
      | zero => exact inferInstanceAs (Countable (List block × ℤ))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable state)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable state)
          | succ n => nomatch n
    case horacle =>
      intro _ n
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair]
        exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
          (FC_f_sInv IF'_Valid2_f)
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
            (PC_f_sInv (S_f_sInv IF'_Valid2_f))
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
              Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              (PC_fi_sInv (S_fi_sInv (K₁ := SLCommon.F.RO.m) (K₂ := SLCommon.F.RO.m) (R := Eq)))
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, hg, -⟩
    refine ⟨?_, ?_⟩
    · simp_reads
      exact hg
    · simp_reads
      trivial

/-- `Valid2(F.RO).f ~ IF.f` under `idInv` (EC: `inline*; sp; wp 2 2; sim`). -/
theorem Valid2_IF_f :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ idInv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block) block
        (Valid2 SLCommon.F.RO.asRO)).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block) block Gconcl.IF).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ idInv g₁ g₂) := by
  unfold Valid2 Gconcl.IF
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x _ ⟨rfl, e1, e2, e3, e4, e5⟩ a -
  rw [e4]
  split_ifs <;> exact ⟨rfl, by id_close⟩

set_option maxHeartbeats 4000000 in
-- the oracles' footprint checks through the nested wrappers
/-- `local equiv ideal_equiv2 (D <: …) : L2(D, F.RO).distinguish ~
SLCommon.IdealIndif(IF, S, A(D)).main : ={glob D} ==> ={glob D, res}`. -/
theorem ideal_equiv2 (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal D) :
    prhlProc (fun _ g₁ _ g₂ => eqGlob D g₁ g₂)
      (L2 D SLCommon.F.RO.asRO).procedure (SLCommon.IdealIndif Gconcl.IF Gconcl.S (A D)).procedure
      (fun r₁ g₁ r₂ g₂ => eqGlob D g₁ g₂ ∧ r₁ = r₂) := by
  have hsm : (Gconcl.S.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hsmi : (Gconcl.S.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hspa : (Gconcl.S.paths).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hro : (SLCommon.F.RO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hcc : (BlockSponge.C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  let Lg := Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi (Lens.pair Gconcl.S.paths
    (Lens.pair SLCommon.F.RO.m BlockSponge.C.c)))
  let I : SLCommon.smap × SLCommon.smap × FMap capacity (List block × block) ×
      FMap (List block) block × ℤ → SLCommon.smap × SLCommon.smap ×
      FMap capacity (List block × block) × FMap (List block) block × ℤ → Prop := fun x y =>
    x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧ x.2.2.2.2 = y.2.2.2.2
  have hI : ∀ g₁ g₂, I (Lg.get g₁) (Lg.get g₂) ↔ idInv g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (Lg.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [Lg, Footprint.lens_pair]
    exact sup_le hsm (sup_le hsmi (sup_le hspa (sup_le hro hcc)))
  unfold L2 SLCommon.IdealIndif Indifferentiability.GIdeal
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    refine ⟨?_, (hI _ _).mpr ?_⟩
    · simp only [touched_set_of_le_compl hsm, touched_set_of_le_compl hsmi,
        touched_set_of_le_compl hspa, touched_set_of_le_compl hro, touched_set_of_le_compl hcc]
      exact h
    · simp only [idInv, sInv]
      simp_reads
      trivial
  · stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_moduleF Lg D distExt hD.representable
      (FVP.fvP D) le_rfl hL I ?hc _ _ ?horacle) ?_
    case hc =>
      intro _ n
      cases n with
      | zero => exact inferInstanceAs (Countable (List block × ℤ))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable state)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable state)
          | succ n => nomatch n
    case horacle =>
      intro _ n
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair]
        exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
          (FC_f_sInv Valid2_IF_f)
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
            (PC_f_sInv (S_f_sInv Valid2_IF_f))
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
              Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              (PC_fi_sInv (S_fi_sInv (K₁ := SLCommon.F.RO.m) (K₂ := SLCommon.F.RO.m) (R := Eq)))
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, hg, -⟩
    refine ⟨?_, ?_⟩
    · simp_reads
      exact hg
    · simp_reads
      trivial

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

/-- `Ideal_equiv3`'s invariant on the oracles: `inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2}`. -/
abbrev L3Inv := sInv SLCommon.F.RO.m (Lens.pair SLCommon.F.RO.m F2.RO.m)
  (fun m p => inv_L_L3 m p.1 p.2)

set_option maxHeartbeats 4000000 in
-- the inlined loops' wp goals are large
/-- `IF'(F.RO).f ~ IF2(F.RO, F2.RO).f` under `L3Inv` (EC: `if{2}` on `valid p`; the loops in
lockstep, sampling `F.RO` on the left against `F.RO` (valid) or `F2.RO` (not valid) on the
right). -/
theorem IF'_IF2_f :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L3Inv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block) block
        (IF' SLCommon.F.RO.asRO)).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block) block
        (Module.app IF2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L3Inv g₁ g₂) := by
  unfold L3Inv sInv IF'
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 4 1 : (§x0{1} = §x0{2} ∧ §i{1} = 0 ∧ §i{2} = 0 ∧ §p{1} = §p{2} ∧ §n{1} = §n{2} ∧
      parse §x0{1} = (§p{1}, §n{1}) ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
      §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧ §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
      inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2} ∧
      §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
  · stmt_wp
    equiv_skip
    rintro _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, h, rfl⟩
    and_intros <;> first | rfl | trivial
  · equiv_if{2}
    case «then» =>
      stmt_wp
      equiv_rnd
      stmt_wp
      equiv_while (§x0{1} = §x0{2} ∧ §i{1} = §i{2} ∧ §p{1} = §p{2} ∧ §n{1} = §n{2} ∧
          parse §x0{1} = (§p{1}, §n{1}) ∧ valid §p{1} = true ∧ 0 ≤ §i{1} ∧
          §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
          §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧ §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
      case body =>
        stmt_wp
        equiv_rnd
        stmt_wp
        equiv_skip
        rintro x0 i p n m mi paths m1 c _ _ _ _ _ _ _ m2 m3 _
          ⟨⟨rfl, rfl, rfl, rfl, hpx, hv, hi, rfl, rfl, rfl, hinv, rfl⟩, hc⟩ a -
        simp only [decide_eq_true_eq] at hc
        have hv' : valid (parse (format p (i + 1))).1 = true := by
          rw [parseK p (i + 1) (by omega) (by simpa [valid] using hv)]; exact hv
        have hd := hinv.dom_valid hv'
        simp only [ite_self]
        by_cases h1 : FMap.dom m2 (format p (i + 1))
        · simp only [h1, hd.mpr h1, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
          and_intros <;> first | trivial | rfl | assumption | omega
        · simp only [h1, mt hd.mp h1, decide_false, Bool.not_false, if_true]
          and_intros <;> first | trivial | rfl | assumption | omega | exact hinv.set_valid hv' a
      case guard => intros; simp_all
      case exit =>
        rintro x0 i p n m mi paths m1 c _ _ _ _ _ _ _ m2 m3 _
          ⟨rfl, rfl, rfl, rfl, hpx, hv, hi, rfl, rfl, rfl, hinv, rfl⟩ - a -
        have hv' : valid (parse x0).1 = true := by rw [hpx]; exact hv
        have hd := hinv.dom_valid hv'
        simp only [ite_self]
        by_cases h1 : FMap.dom m2 x0
        · simp only [h1, hd.mpr h1, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
          and_intros <;> first | trivial | rfl | assumption | rw [hinv.get_valid hv']
        · simp only [h1, mt hd.mp h1, decide_false, Bool.not_false, if_true]
          and_intros <;> first | trivial | rfl | assumption | exact hinv.set_valid hv' a |
            simp only [FMap.get_set_sameE]
      equiv_skip
      rintro x0 i p n m mi paths m1 c _ _ _ _ _ _ _ m2 m3 _
        ⟨⟨rfl, rfl, rfl, rfl, rfl, hpx, rfl, rfl, rfl, hinv, rfl⟩, hv⟩
      exact ⟨rfl, rfl, rfl, rfl, hpx, hv, le_rfl, rfl, rfl, rfl, hinv, rfl⟩
    case «else» =>
      stmt_wp
      equiv_rnd
      stmt_wp
      equiv_while (§x0{1} = §x0{2} ∧ §i{1} = §i{2} ∧ §p{1} = §p{2} ∧ §n{1} = §n{2} ∧
          parse §x0{1} = (§p{1}, §n{1}) ∧ valid §p{1} = false ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
          §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧ §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
      case body =>
        stmt_wp
        equiv_rnd
        stmt_wp
        equiv_skip
        rintro x0 i p n m mi paths m1 c _ _ _ _ _ _ _ m2 m3 _
          ⟨⟨rfl, rfl, rfl, rfl, hpx, hv, rfl, rfl, rfl, hinv, rfl⟩, -⟩ a -
        have hv' : valid (parse (format p (i + 1))).1 = false := by
          have := parse_not_valid x0 (by rw [hpx]; exact hv) (i + 1)
          rwa [hpx] at this
        have hd := hinv.dom_invalid hv'
        simp only [ite_self]
        by_cases h1 : FMap.dom m3 (format p (i + 1))
        · simp only [h1, hd.mpr h1, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
          and_intros <;> trivial
        · simp only [h1, mt hd.mp h1, decide_false, Bool.not_false, if_true]
          and_intros <;> first | trivial | rfl | assumption |
            exact lemma3 _ _ _ _ a hinv hv' (mt hd.mp h1)
      case guard => intros; simp_all
      case exit =>
        rintro x0 i p n m mi paths m1 c _ _ _ _ _ _ _ m2 m3 _
          ⟨rfl, rfl, rfl, rfl, hpx, hv, rfl, rfl, rfl, hinv, rfl⟩ - a -
        have hv' : valid (parse x0).1 = false := by rw [hpx]; exact hv
        have hd := hinv.dom_invalid hv'
        simp only [ite_self]
        by_cases h1 : FMap.dom m3 x0
        · simp only [h1, hd.mpr h1, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
          and_intros <;> first | trivial | rfl | assumption | rw [hinv.get_invalid hv']
        · simp only [h1, mt hd.mp h1, decide_false, Bool.not_false, if_true]
          and_intros <;> first | trivial | rfl | assumption |
            exact lemma3 _ _ _ _ a hinv hv' (mt hd.mp h1) | simp only [FMap.get_set_sameE]
      equiv_skip
      rintro x0 i p n m mi paths m1 c _ _ _ _ _ _ _ m2 m3 _
        ⟨⟨rfl, rfl, rfl, rfl, rfl, hpx, rfl, rfl, rfl, hinv, rfl⟩, hv⟩
      exact ⟨rfl, rfl, rfl, rfl, hpx, hv, rfl, rfl, rfl, hinv, rfl⟩

omit [Params] in
/-- The invariant holds of the empty maps (`F.RO.init`, `F2.RO.init`). -/
theorem inv_L_L3_empty : inv_L_L3 FMap.empty FMap.empty FMap.empty := by
  refine ⟨(FMap.fmap_eqP _ _).mp fun y => ?_, fun l h => absurd h (FMap.mem_empty _),
    fun l h => absurd h (FMap.mem_empty _)⟩
  rw [add_get, if_neg (FMap.mem_empty _)]

set_option maxHeartbeats 4000000 in
-- the oracles' footprint checks through the nested wrappers
/-- `local equiv Ideal_equiv3 (D <: DISTINGUISHER {-SLCommon.C, -C, -IF, -S, -F2.RO}) :
L(D, F.RO).distinguish ~ L3(D, F.RO).distinguish : ={glob D} ==> ={glob D, res}`. -/
theorem Ideal_equiv3 (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal D) (_hDF2 : FVP.fvP D ≤ (F2.RO.m).footprintᶜ) :
    prhlProc (fun _ g₁ _ g₂ => eqGlob D g₁ g₂)
      (L D SLCommon.F.RO.asRO).procedure (L3 D SLCommon.F.RO.asRO).procedure
      (fun r₁ g₁ r₂ g₂ => eqGlob D g₁ g₂ ∧ r₁ = r₂) := by
  have hsm : (Gconcl.S.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hsmi : (Gconcl.S.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hspa : (Gconcl.S.paths).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hro : (SLCommon.F.RO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  have hf2 : (F2.RO.m).footprint ≤ (FVP.fvP D)ᶜ := (Footprint.le_compl_comm _ _).mp _hDF2
  have hcc : (BlockSponge.C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by gcol_fp)))
  let Lg := Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi (Lens.pair Gconcl.S.paths
    (Lens.pair SLCommon.F.RO.m (Lens.pair F2.RO.m BlockSponge.C.c))))
  let I : SLCommon.smap × SLCommon.smap × FMap capacity (List block × block) ×
      FMap (List block) block × FMap (List block) block × ℤ → SLCommon.smap × SLCommon.smap ×
      FMap capacity (List block × block) × FMap (List block) block × FMap (List block) block × ℤ →
      Prop := fun x y =>
    x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ inv_L_L3 x.2.2.2.1 y.2.2.2.1 y.2.2.2.2.1 ∧
      x.2.2.2.2.2 = y.2.2.2.2.2
  have hI : ∀ g₁ g₂, I (Lg.get g₁) (Lg.get g₂) ↔ L3Inv g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (Lg.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [Lg, Footprint.lens_pair]
    exact sup_le hsm (sup_le hsmi (sup_le hspa (sup_le hro (sup_le hf2 hcc))))
  unfold L L3 SLCommon.IdealIndif Indifferentiability.GIdeal
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    refine ⟨?_, (hI _ _).mpr ?_⟩
    · simp only [touched_set_of_le_compl hsm, touched_set_of_le_compl hsmi,
        touched_set_of_le_compl hspa, touched_set_of_le_compl hro, touched_set_of_le_compl hf2,
        touched_set_of_le_compl hcc]
      exact h
    · simp only [L3Inv, sInv]
      simp_reads
      exact inv_L_L3_empty
  · stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_moduleF Lg D distExt hD.representable
      (FVP.fvP D) le_rfl hL I ?hc _ _ ?horacle) ?_
    case hc =>
      intro _ n
      cases n with
      | zero => exact inferInstanceAs (Countable (List block × ℤ))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable state)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable state)
          | succ n => nomatch n
    case horacle =>
      intro _ n
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair]
        exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
          (FC_f_sInv IF'_IF2_f)
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
            (PC_f_sInv (S_f_sInv IF'_IF2_f))
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
              Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              (PC_fi_sInv (S_fi_sInv (K₁ := SLCommon.F.RO.m)
                (K₂ := Lens.pair SLCommon.F.RO.m F2.RO.m) (R := fun m p => inv_L_L3 m p.1 p.2)))
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, hg, -⟩
    refine ⟨?_, ?_⟩
    · simp_reads
      exact hg
    · simp_reads
      trivial

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

omit [BlockSponge.Params] [Params] in
/-- `S_f_sInv` for `S` applied to a `DFUNCTIONALITY` (as in `S2`'s `S(Last(F))`). -/
theorem S_f_sInvD {α β : Type} {K₁ : Lens α VariableAssignment} {K₂ : Lens β VariableAssignment}
    {R : α → β → Prop} [Lens.Disjoint Gconcl.S.m K₁] [Lens.Disjoint Gconcl.S.m K₂]
    [Lens.Disjoint Gconcl.S.mi K₁] [Lens.Disjoint Gconcl.S.mi K₂] [Lens.Disjoint Gconcl.S.paths K₁]
    [Lens.Disjoint Gconcl.S.paths K₂]
    {G₁ G₂ : SLCommon.DFUNCTIONALITY}
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sInv K₁ K₂ R g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block G₁).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block G₂).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sInv K₁ K₂ R g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sInv K₁ K₂ R g₁ g₂)
      (Indifferentiability.PRIMITIVE.f state (List block) block
        (Module.app Gconcl.S G₁)).procedure
      (Indifferentiability.PRIMITIVE.f state (List block) block
        (Module.app Gconcl.S G₂)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sInv K₁ K₂ R g₁ g₂) := by
  unfold sInv
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
      §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧ §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
      R §K₁{1} §K₂{2} ∧ §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
  · stmt_wp
    equiv_skip
    intros; simp_all
  · equiv_if
    case guard => intros; simp_all
    case «else» =>
      stmt_wp
      equiv_skip
      intros; simp_all
    case «then» =>
      equiv_seq 5 5 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
      §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧ §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
      R §K₁{1} §K₂{2} ∧ §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
      · equiv_if
        case guard => intros; simp_all
        case «then» =>
          equiv_call h
          stmt_wp
          equiv_skip
          rintro g₁ g₂ x0 _ ⟨⟨⟨rfl, hE⟩, -⟩, -⟩
          exact ⟨⟨by rw [hE.2.2.1], hE⟩, fun _ _ _ _ ⟨hr, hE'⟩ => ⟨rfl, hr, hE'⟩⟩
        case «else» =>
          equiv_rnd
          equiv_skip
          intros; simp_all
      · stmt_wp
        equiv_rnd
        equiv_skip
        rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, hR, rfl⟩ _ -
        simp only [ite_self]
        and_intros <;> first | rfl | trivial

omit [BlockSponge.Params] [Params] in
/-- `S_fi_sInv` for `S` applied to a `DFUNCTIONALITY`. -/
theorem S_fi_sInvD {α β : Type} {K₁ : Lens α VariableAssignment} {K₂ : Lens β VariableAssignment}
    {R : α → β → Prop} [Lens.Disjoint Gconcl.S.m K₁] [Lens.Disjoint Gconcl.S.m K₂]
    [Lens.Disjoint Gconcl.S.mi K₁] [Lens.Disjoint Gconcl.S.mi K₂] [Lens.Disjoint Gconcl.S.paths K₁]
    [Lens.Disjoint Gconcl.S.paths K₂]
    {G₁ G₂ : SLCommon.DFUNCTIONALITY} :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sInv K₁ K₂ R g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi state (List block) block
        (Module.app Gconcl.S G₁)).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block) block
        (Module.app Gconcl.S G₂)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sInv K₁ K₂ R g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ sInv K₁ K₂ R §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    id_close
  · equiv_if
    case guard => id_close
    case «else» =>
      stmt_wp
      equiv_skip
      id_close
    case «then» =>
      stmt_wp
      equiv_rnd
      equiv_rnd
      equiv_skip
      id_close

omit [BlockSponge.Params] [Params] in
/-- `equiv_L4_ideal`'s invariant: `={glob S, glob C} /\ INV_L4_ideal F.RO.m{1} BIRO.IRO.mp{2}
F2.RO.m{1} BIRO2.IRO.mp{2}`. -/
abbrev L4Inv := sInv (Lens.pair SLCommon.F.RO.m F2.RO.m)
  (Lens.pair BlockSponge.BIRO.IRO.mp BIRO2.IRO.mp) (fun x y => INV_L4_ideal x.1 y.1 x.2 y.2)

/-- `FC(FValid(DSqueeze2(F.LRO, F2.LRO))).f ~ FC(BIRO.IRO).f` under `L4Inv` (EC: the `f` oracle
of `equiv_L4_ideal`'s `call (: ...)`, coupling `F.LRO`'s samples with `BIRO.IRO`'s). -/
theorem FC_FValid_f :
    prhlProc (sig₁ := procsig (List block × ℤ) -> (List block))
      (sig₂ := procsig (List block × ℤ) -> (List block))
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L4Inv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Module.app FValid
          (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
            { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
                (Module.app DSqueeze2 (Module.pair SLCommon.F.LRO F2.LRO)) })))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              BlockSponge.BIRO.IRO.asF }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L4Inv g₁ g₂) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§bl{1} = §bl{2} ∧ §nb{1} = §nb{2} ∧ §z{1} = §z{2} ∧
      §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
          §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          INV_L4_ideal
              §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
  · stmt_wp
    equiv_skip
    (rintro g₁ g₂ x _ ⟨rfl, h⟩; simp only [L4Inv, sInv, Lens.pair] at h; exact ⟨rfl, rfl, h⟩)
  · equiv_if
    case guard =>
      rintro bl nb z m mi paths r1 f1 c _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, -, rfl⟩
      rfl
    case «else» =>
      equiv_skip
      rintro g₁ g₂ bl nb z _ _ _ ⟨⟨rfl, rfl, rfl, h⟩, -⟩
      refine ⟨rfl, ?_⟩
      simp only [L4Inv, sInv, Lens.pair]
      exact h
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§p{1} = §(localVarLens "x1" (List block)){2} ∧ §n{1} = §n{2} ∧
          §(localVarLens "r" (List block)){1} = §bs{2} ∧ §bs{2} = [] ∧ §i{2} = 0 ∧
              §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
          §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          INV_L4_ideal
              §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
      · stmt_wp
        equiv_skip
        rintro bl nb z m mi paths r1 f1 c _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, hI,
            rfl⟩, -⟩
        exact ⟨rfl, rfl, rfl, rfl, rfl, hI, rfl⟩
      · equiv_if
        case guard => (rintro p n r m mi paths ro f2 c _ _ _ _ _ _ _ _ _ _ ⟨rfl, -⟩; rfl)
        case «else» =>
          equiv_skip
          rintro g₁ g₂ p n r x1 n2 bs i ⟨⟨rfl, rfl, rfl, -, -, h⟩, -⟩
          refine ⟨rfl, ?_⟩
          simp only [L4Inv, sInv, Lens.pair]
          exact h
        case «then» =>
          stmt_wp
          equiv_seq 1 1 : (§p0{1} = §(localVarLens "x1" (List block)){2} ∧ §n0{1} = §n{2} ∧
              §i{1} = §i{2} ∧ §lres{1} = §bs{2} ∧ §i{1} = 0 ∧ valid §p0{1} = true ∧
                  §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
          §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          INV_L4_ideal
              §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
          · stmt_wp
            equiv_skip
            rintro p n r m mi paths ro f2 c _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, hI, rfl⟩, hv⟩
            exact ⟨rfl, rfl, rfl, rfl, hv, rfl, rfl, rfl, hI, rfl⟩
          · equiv_if{1}
            case «else» =>
              refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
              (exact Bool.false_ne_true (h.2.symm.trans h.1.2.2.2.2.2.1))
            case «then» =>
              equiv_seq 1 1 : (§p0{1} = §(localVarLens "x1" (List block)){2} ∧ §n0{1} = §n{2} ∧
                  §i{1} = §i{2} ∧
                §lres{1} = §bs{2} ∧ valid §p0{1} = true ∧ 0 ≤ §i{1} ∧
                    §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
          §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          INV_L4_ideal
              §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
              · stmt_wp
                equiv_skip
                rintro p0 n0 i lres m mi paths ro f2 c _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, h0,
                    hv, rfl, rfl, rfl, hI, rfl⟩, -⟩
                simp only [ite_self]
                and_intros <;> first | trivial | assumption | omega
              · equiv_while (§p0{1} = §(localVarLens "x1" (List block)){2} ∧ §n0{1} = §n{2} ∧
                  §i{1} = §i{2} ∧
                §lres{1} = §bs{2} ∧ valid §p0{1} = true ∧ 0 ≤ §i{1} ∧
                    §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
          §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          INV_L4_ideal
              §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
                case body =>
                  stmt_wp
                  equiv_seq 1 1 : (§x4{1} = format §p0{1} §i{1} ∧
                      §(localVarLens "x2" (List block)){2} =
                      §(localVarLens "x1" (List block)){2} ∧ §n0{2} + 1 = §i{1} ∧
                      §p0{1} = §(localVarLens "x1" (List block)){2} ∧ §n0{1} = §n{2} ∧
                      §i{1} = §i{2} + 1 ∧ §lres{1} = §bs{2} ∧ valid §p0{1} = true ∧ 1 ≤ §i{1} ∧
                      §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
                      §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
                      INV_L4_ideal §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1}
                        §BIRO2.IRO.mp{2} ∧ §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
                  · stmt_wp
                    equiv_skip
                    rintro p0 n0 i lres m mi paths ro f2 c _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl,
                        hv, hi, rfl, rfl, rfl, hI, rfl⟩, -⟩
                    and_intros <;> first | rfl | assumption | omega
                  · equiv_if{2}
                    case «then» =>
                      stmt_wp
                      equiv_rnd
                      equiv_skip
                      rintro x4 p0 i n0 lres m mi paths ro f2 c
                          x2 x1 n0' n i' bs m' mi' paths' mp mp1 c'
                        ⟨⟨rfl, rfl, hn0, rfl, rfl, rfl, rfl, hv, hi1, rfl, rfl, rfl, hI, rfl⟩,
                            hnd⟩ a -
                      obtain rfl : n0' = i' := by omega
                      have hpk : parse (format p0 (n0' + 1)) = (p0, n0' + 1) :=
                        parseK p0 (n0' + 1) (by omega) (by simpa [valid] using hv)
                      have hI' := hI
                      obtain ⟨⟨h1, h2, h3, h4⟩, -, -, -⟩ := hI'
                      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hnd
                      have hnd1 : ¬ FMap.dom ro (format p0 (n0' + 1)) :=
                        fun h => hnd ((h1 _ _ _ hpk).mpr h)
                      simp only [hnd1, decide_false, Bool.not_false, if_true, FMap.get_set_sameE]
                      and_intros <;> first | trivial | rfl | assumption | omega |
                        exact lemma5 _ _ _ _ _ _ _ hI hnd (by omega) hv
                    case «else» =>
                      stmt_wp{1} 1
                      equiv_skip
                      rintro x4 p0 i n0 lres m mi paths ro f2 c
                          x2 x1 n0' n i' bs m' mi' paths' mp mp1 c'
                        ⟨⟨rfl, rfl, hn0, rfl, rfl, rfl, rfl, hv, hi1, rfl, rfl, rfl, hI, rfl⟩, hnd⟩
                      obtain rfl : n0' = i' := by omega
                      have hpk : parse (format p0 (n0' + 1)) = (p0, n0' + 1) :=
                        parseK p0 (n0' + 1) (by omega) (by simpa [valid] using hv)
                      have hI' := hI
                      obtain ⟨⟨h1, h2, h3, h4⟩, -, -, -⟩ := hI'
                      simp only [Bool.not_eq_false', decide_eq_true_eq] at hnd
                      have hd1 : FMap.dom ro (format p0 (n0' + 1)) := (h1 _ _ _ hpk).mp hnd
                      refine ⟨bdistr_expected_one, fun a _ => ?_⟩
                      simp only [hd1, decide_true, Bool.not_true, Bool.false_eq_true, if_false,
                          h4 _ _ _ hpk]
                      and_intros <;> first | trivial | rfl | assumption | omega
                case guard =>
                  rintro p0 n0 i lres m mi paths ro f2 c _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, -⟩
                  rfl
                case exit =>
                  rintro g₁ g₂ p0 n0 i lres x1 n2 i2 bs ⟨rfl, rfl, rfl, rfl, -, -, h⟩ -
                  refine ⟨rfl, ?_⟩
                  simp only [L4Inv, sInv, Lens.pair]
                  exact h
                equiv_skip
                intros; assumption

set_option maxHeartbeats 1600000 in
-- two inlined loops (valid and invalid branch)
/-- `DSqueeze2(F.LRO, F2.LRO).f ~ Valid(BIRO.IRO).f` under `L4Inv`, on well-formed inputs
(`parse (format p n) = (p, n)`): valid prefixes couple `F.LRO` with `BIRO.IRO` (`lemma5`), invalid
ones `F2.LRO` with `BIRO2.IRO` (`lemma5bis`). -/
theorem DSqueeze2_Valid_f :
    prhlProc (sig₁ := procsig (List block × ℤ) -> (List block))
      (sig₂ := procsig (List block × ℤ) -> (List block))
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ parse (format a₁.1 a₁.2) = a₁ ∧ L4Inv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app DSqueeze2 (Module.pair SLCommon.F.LRO F2.LRO))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app Valid (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ)
          (List block) BlockSponge.BIRO.IRO.asF))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L4Inv g₁ g₂) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§p{1} = §q{2} ∧ §n{1} = §k{2} ∧ §pp{1} = §p{1} ∧ §nn{1} = §n{1} ∧
      §lres{1} = [] ∧ §i{1} = 0 ∧ parse (format §p{1} §n{1}) = (§p{1},
          §n{1}) ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
          §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          INV_L4_ideal
              §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, hp, h⟩
    simp only [L4Inv, sInv, Lens.pair] at h
    refine ⟨?_, ?_, ?_, ?_, ?_, h⟩ <;> simp [hp]
  · equiv_if
    case guard => (rintro p n pp nn lres i m mi paths r1 r2 c _ _ _ _ _ _ _ _ ⟨rfl, -⟩; rfl)
    case «then» =>
      stmt_wp
      equiv_seq 1 1 : (§p{1} = §(localVarLens "x1" (List block)){2} ∧ §n{1} = §n{2} ∧
          §i{1} = §i{2} ∧
              §lres{1} = §bs{2} ∧ valid §p{1} = true ∧ 0 ≤ §i{1} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
                  §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
          §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          INV_L4_ideal
              §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
      · stmt_wp
        equiv_skip
        rintro p n pp nn lres i m mi paths r1 r2 c _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl,
            -, rfl, rfl, rfl, hI, rfl⟩, hv⟩
        simp only [ite_self]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI, ?_⟩ <;> first | trivial
      · equiv_if{2}
        case «else» =>
          refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
          obtain ⟨⟨hp, -, -, -, hv, -⟩, hb⟩ := h
          rw [← hp] at hb
          exact Bool.false_ne_true (hb.symm.trans hv)
        case «then» =>
          equiv_while (§p{1} = §(localVarLens "x1" (List block)){2} ∧ §n{1} = §n{2} ∧
              §i{1} = §i{2} ∧
              §lres{1} = §bs{2} ∧ valid §p{1} = true ∧ 0 ≤ §i{1} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
                  §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
          §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          INV_L4_ideal
              §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
          case body =>
            stmt_wp
            equiv_seq 1 1 : (§x2{1} = format §p{1} §i{1} ∧
                §x2{2} = §(localVarLens "x1" (List block)){2} ∧ §n0{2} + 1 = §i{1} ∧
                §p{1} = §(localVarLens "x1" (List block)){2} ∧ §n{1} = §n{2} ∧ §i{1} = §i{2} + 1 ∧
                    §lres{1} = §bs{2} ∧
                valid §p{1} = true ∧ 1 ≤ §i{1} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
                    §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
                §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
                INV_L4_ideal §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1}
                  §BIRO2.IRO.mp{2} ∧ §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
            · stmt_wp
              equiv_skip
              rintro p n i lres m mi paths ro f2 c _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, hv, hi,
                  rfl, rfl, rfl, hI, rfl⟩, -⟩
              and_intros <;> first | rfl | assumption | omega
            · equiv_if{2}
              case «then» =>
                stmt_wp
                equiv_rnd
                equiv_skip
                rintro x2 p i n lres m mi paths ro f2 c x2' x1 n0' n' i' bs m' mi' paths' mp mp1 c'
                  ⟨⟨rfl, rfl, hn0, rfl, rfl, rfl, rfl, hv, hi1, rfl, rfl, rfl, hI, rfl⟩, hnd⟩ a -
                obtain rfl : n0' = i' := by omega
                have hpk : parse (format p (n0' + 1)) = (p, n0' + 1) :=
                  parseK p (n0' + 1) (by omega) (by simpa [valid] using hv)
                have hI' := hI
                obtain ⟨⟨h1, h2, h3, h4⟩, -, -, -⟩ := hI'
                simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hnd
                have hnd1 : ¬ FMap.dom ro (format p (n0' + 1)) :=
                  fun h => hnd ((h1 _ _ _ hpk).mpr h)
                simp only [hnd1, decide_false, Bool.not_false, if_true, FMap.get_set_sameE]
                and_intros <;> first | trivial | rfl | assumption | omega |
                  exact lemma5 _ _ _ _ _ _ _ hI hnd (by omega) hv
              case «else» =>
                stmt_wp{1} 1
                equiv_skip
                rintro x2 p i n lres m mi paths ro f2 c x2' x1 n0' n' i' bs m' mi' paths' mp mp1 c'
                  ⟨⟨rfl, rfl, hn0, rfl, rfl, rfl, rfl, hv, hi1, rfl, rfl, rfl, hI, rfl⟩, hnd⟩
                obtain rfl : n0' = i' := by omega
                have hpk : parse (format p (n0' + 1)) = (p, n0' + 1) :=
                  parseK p (n0' + 1) (by omega) (by simpa [valid] using hv)
                have hI' := hI
                obtain ⟨⟨h1, h2, h3, h4⟩, -, -, -⟩ := hI'
                simp only [Bool.not_eq_false', decide_eq_true_eq] at hnd
                have hd1 : FMap.dom ro (format p (n0' + 1)) := (h1 _ _ _ hpk).mp hnd
                refine ⟨bdistr_expected_one, fun a _ => ?_⟩
                simp only [hd1, decide_true, Bool.not_true, Bool.false_eq_true, if_false,
                    h4 _ _ _ hpk]
                and_intros <;> first | trivial | rfl | assumption | omega
          case guard =>
            rintro p n i lres m mi paths r1 r2 c _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, -⟩
            rfl
          case exit =>
            rintro g₁ g₂ p n i lres x1 n2 i2 bs ⟨rfl, rfl, rfl, rfl, -, -, h⟩ -
            refine ⟨rfl, ?_⟩
            simp only [L4Inv, sInv, Lens.pair]
            exact h
          equiv_skip
          intros; rename_i h; exact h.1
    case «else» =>
      stmt_wp
      equiv_seq 1 1 : (§pp{1} = §x3{2} ∧ §n{1} = §n1{2} ∧ §i{1} = §i0{2} ∧
              §lres{1} = §bs0{2} ∧ valid §pp{1} = false ∧ 0 ≤ §i{1} ∧
              parse (format §pp{1} §n{1}) = (§pp{1},
                  §n{1}) ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
          §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          INV_L4_ideal
              §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
      · equiv_rcondf{1}
        stmt_wp
        equiv_skip
        rintro p n pp nn lres i m mi paths r1 r2 c _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl,
            hpk, rfl, rfl, rfl, hI, rfl⟩, hv⟩
        simp only [ite_self]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI,
            ?_⟩ <;> first | trivial | assumption | exact le_rfl | simp
      · equiv_if{2}
        case «else» =>
          refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
          exact h.2
        case «then» =>
          equiv_while (§pp{1} = §x3{2} ∧ §n{1} = §n1{2} ∧ §i{1} = §i0{2} ∧
              §lres{1} = §bs0{2} ∧ valid §pp{1} = false ∧ 0 ≤ §i{1} ∧
              parse (format §pp{1} §n{1}) = (§pp{1},
                  §n{1}) ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
          §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          INV_L4_ideal
              §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
          case body =>
            stmt_wp
            equiv_seq 1 1 : (§x5{1} = format §pp{1} §i{1} ∧ §x4{2} = §x3{2} ∧ §n2{2} + 1 = §i{1} ∧
                §pp{1} = §x3{2} ∧ §n{1} = §n1{2} ∧ §i{1} = §i0{2} + 1 ∧ §lres{1} = §bs0{2} ∧
                valid §pp{1} = false ∧ 1 ≤ §i{1} ∧ §i{1} ≤ §n{1} ∧
                parse (format §pp{1} §n{1}) = (§pp{1},
                    §n{1}) ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
                §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
                INV_L4_ideal §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1}
                  §BIRO2.IRO.mp{2} ∧ §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
            · stmt_wp
              equiv_skip
              rintro pp n i lres m mi paths ro f2 c _ _ _ _ _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl, rfl, hv,
                  hi, hpn, rfl, rfl, rfl, hI, rfl⟩, hlt⟩
              simp only [decide_eq_true_eq] at hlt
              and_intros <;> first | rfl | assumption | omega
            · equiv_if{2}
              case «then» =>
                stmt_wp
                equiv_rnd
                equiv_skip
                rintro x5 pp i n lres m mi paths ro f2 c x4 x3 n2 n1 i0 bs0 m' mi' paths' mp mp1 c'
                  ⟨⟨rfl, rfl, hn2, rfl, rfl, rfl, rfl, hv, hi1, hin, hpn, rfl, rfl, rfl, hI, rfl⟩,
                      hnd⟩ a -
                obtain rfl : n2 = i0 := by omega
                have hpk : parse (format pp (n2 + 1)) = (pp, n2 + 1) :=
                  parse_twice pp n _ hpn.symm _ ⟨by omega, by omega⟩
                have hI' := hI
                obtain ⟨-, ⟨h1, h2, h3, h4⟩, -, -⟩ := hI'
                simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hnd
                have hnd1 : ¬ FMap.dom f2 (format pp (n2 + 1)) :=
                  fun h => hnd ((h1 _ _ _ hpk).mpr h)
                simp only [hnd1, decide_false, Bool.not_false, if_true, FMap.get_set_sameE]
                and_intros <;> first | trivial | rfl | assumption | omega |
                  exact lemma5bis _ _ _ _ _ _ _ hI hnd (by omega) hv hpk
              case «else» =>
                stmt_wp{1} 1
                equiv_skip
                rintro x5 pp i n lres m mi paths ro f2 c x4 x3 n2 n1 i0 bs0 m' mi' paths' mp mp1 c'
                  ⟨⟨rfl, rfl, hn2, rfl, rfl, rfl, rfl, hv, hi1, hin, hpn, rfl, rfl, rfl, hI, rfl⟩,
                      hnd⟩
                obtain rfl : n2 = i0 := by omega
                have hpk : parse (format pp (n2 + 1)) = (pp, n2 + 1) :=
                  parse_twice pp n _ hpn.symm _ ⟨by omega, by omega⟩
                have hI' := hI
                obtain ⟨-, ⟨h1, h2, h3, h4⟩, -, -⟩ := hI'
                simp only [Bool.not_eq_false', decide_eq_true_eq] at hnd
                have hd1 : FMap.dom f2 (format pp (n2 + 1)) := (h1 _ _ _ hpk).mp hnd
                refine ⟨bdistr_expected_one, fun a _ => ?_⟩
                simp only [hd1, decide_true, Bool.not_true, Bool.false_eq_true, if_false,
                    h4 _ _ _ hpk]
                and_intros <;> first | trivial | rfl | assumption | omega
          case guard =>
            rintro p n i lres m mi paths r1 r2 c _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, -⟩
            rfl
          case exit =>
            rintro g₁ g₂ pp n i lres x3 n1 i0 bs0 ⟨rfl, rfl, rfl, rfl, -, -, -, h⟩ -
            refine ⟨rfl, ?_⟩
            simp only [L4Inv, sInv, Lens.pair]
            exact h
          equiv_skip
          intros; rename_i h; exact h

/-- `Last(DSqueeze2(F.LRO, F2.LRO)).f ~ Last(Valid(BIRO.IRO)).f` under `L4Inv`. -/
theorem Last_f_L4 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L4Inv g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app Last (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
          (Module.app DSqueeze2 (Module.pair SLCommon.F.LRO F2.LRO))))).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app Last (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
          (Module.app Valid
            (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
              BlockSponge.BIRO.IRO.asF))))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L4Inv g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.FUNCTIONALITY.view_f]
  stmt_wp
  equiv_call DSqueeze2_Valid_f
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x _ ⟨rfl, h⟩
  exact ⟨⟨rfl, by rw [formatK], h⟩, fun _ _ _ _ ⟨hr, h'⟩ => ⟨hr ▸ rfl, h'⟩⟩

/-- `S2(DSqueeze2(F.LRO, F2.LRO)).f ~ SimLast(S)(BIRO.IRO).f` under `L4Inv`. -/
theorem S2_SimLast_f :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L4Inv g₁ g₂)
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app S2 (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
          (Module.app DSqueeze2 (Module.pair SLCommon.F.LRO F2.LRO))))).procedure
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app (SimLast Gconcl.S) (Indifferentiability.FUNCTIONALITY.view state
          (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L4Inv g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_call (S_f_sInvD Last_f_L4)
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x _ ⟨rfl, h⟩
  exact ⟨⟨rfl, h⟩, fun _ _ _ _ h => h⟩

/-- `S2(DSqueeze2(F.LRO, F2.LRO)).fi ~ SimLast(S)(BIRO.IRO).fi` under `L4Inv`. -/
theorem S2_SimLast_fi :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L4Inv g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app S2 (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
          (Module.app DSqueeze2 (Module.pair SLCommon.F.LRO F2.LRO))))).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app (SimLast Gconcl.S) (Indifferentiability.FUNCTIONALITY.view state
          (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L4Inv g₁ g₂) := by
  equiv_proc
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_call (S_fi_sInvD (K₁ := Lens.pair SLCommon.F.RO.m F2.RO.m)
    (K₂ := Lens.pair BlockSponge.BIRO.IRO.mp BIRO2.IRO.mp)
    (R := fun x y => INV_L4_ideal x.1 y.1 x.2 y.2))
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x _ ⟨rfl, h⟩
  exact ⟨⟨rfl, h⟩, fun _ _ _ _ h => h⟩

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

set_option maxHeartbeats 4000000 in
-- the oracles' footprint checks through the nested wrappers
/-- `local equiv equiv_L4_ideal : L4(D, F.LRO, F2.LRO).distinguish ~
IdealIndif(BIRO.IRO, SimLast(S), DRestr(D)).main : ={glob D} ==> ={glob D, res}`. -/
theorem equiv_L4_ideal (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal2 D) :
    prhlProc (fun _ g₁ _ g₂ => eqGlob D g₁ g₂)
      (L4 D SLCommon.F.LRO F2.LRO).procedure
      (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S) (DRestr D)).procedure
      (fun r₁ g₁ r₂ g₂ => eqGlob D g₁ g₂ ∧ r₁ = r₂) := by
  have hsm : (Gconcl.S.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.1.trans (Footprint.compl_antimono (by gcol_fp)))
  have hsmi : (Gconcl.S.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.1.trans (Footprint.compl_antimono (by gcol_fp)))
  have hspa : (Gconcl.S.paths).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.1.trans (Footprint.compl_antimono (by gcol_fp)))
  have hro : (SLCommon.F.RO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.1.trans (Footprint.compl_antimono (by gcol_fp)))
  have hf2 : (F2.RO.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.2.trans (Footprint.compl_antimono (by gcol_fp)))
  have hiro : (BlockSponge.BIRO.IRO.mp).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.2.trans (Footprint.compl_antimono (by gcol_fp)))
  have hiro2 : (BIRO2.IRO.mp).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.2.trans (Footprint.compl_antimono (by gcol_fp)))
  have hcc : (BlockSponge.C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.1.trans (Footprint.compl_antimono (by gcol_fp)))
  let Lg := Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi (Lens.pair Gconcl.S.paths
    (Lens.pair (Lens.pair SLCommon.F.RO.m F2.RO.m)
      (Lens.pair (Lens.pair BlockSponge.BIRO.IRO.mp BIRO2.IRO.mp) BlockSponge.C.c))))
  let I : SLCommon.smap × SLCommon.smap × FMap capacity (List block × block) ×
      (FMap (List block) block × FMap (List block) block) ×
      (FMap (List block × ℤ) block × FMap (List block × ℤ) block) × ℤ →
      SLCommon.smap × SLCommon.smap × FMap capacity (List block × block) ×
      (FMap (List block) block × FMap (List block) block) ×
      (FMap (List block × ℤ) block × FMap (List block × ℤ) block) × ℤ → Prop := fun x y =>
    x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧
      INV_L4_ideal x.2.2.2.1.1 y.2.2.2.2.1.1 x.2.2.2.1.2 y.2.2.2.2.1.2 ∧
      x.2.2.2.2.2 = y.2.2.2.2.2
  have hI : ∀ g₁ g₂, I (Lg.get g₁) (Lg.get g₂) ↔ L4Inv g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (Lg.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [Lg, Footprint.lens_pair]
    exact sup_le hsm (sup_le hsmi (sup_le hspa (sup_le (sup_le hro hf2)
      (sup_le (sup_le hiro hiro2) hcc))))
  unfold L4 IdealIndif Indifferentiability.GIdeal
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    refine ⟨?_, (hI _ _).mpr ?_⟩
    · simp only [touched_set_of_le_compl hsm, touched_set_of_le_compl hsmi,
        touched_set_of_le_compl hspa, touched_set_of_le_compl hro, touched_set_of_le_compl hf2,
        touched_set_of_le_compl hiro, touched_set_of_le_compl hiro2,
        touched_set_of_le_compl hcc]
      exact h
    · simp only [L4Inv, sInv]
      simp_reads
      exact INV_L4_ideal_empty
  · stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_moduleF Lg D distExt hD.representable
      (FVP.fvP D) le_rfl hL I ?hc _ _ ?horacle) ?_
    case hc =>
      intro _ n
      cases n with
      | zero => exact inferInstanceAs (Countable (List block × ℤ))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable state)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable state)
          | succ n => nomatch n
    case horacle =>
      intro _ n
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair, Indifferentiability.DFUNCTIONALITY.f.mk_simp]
        exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep') FC_FValid_f
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
            (PC_f_sInv S2_SimLast_f)
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
              Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              (PC_fi_sInv S2_SimLast_fi)
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, hg, -⟩
    refine ⟨?_, ?_⟩
    · simp_reads
      exact hg
    · simp_reads
      trivial

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

omit [BlockSponge.Params] [Params] in
/-- `IRO.f` is lossless (for `bdistr`): its loop is counted.  Not an EC lemma: EC proves it inline
(`while (true) (n - i)`). -/
theorem IRO_f_ll (valid : List block → Bool)
    (mp : Lens (FMap (List block × ℤ) block) VariableAssignment) :
    (IRO.IRO.f block (List block) valid bdistr mp).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  refine phoareProc_eq_of_le_ge (fun _ _ _ => Procedure.ewp_const_le _ _ _ _) ?_
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_wp 1
  phoare_split 1
  refine phoareStmt_seq_ge_one ?_ ?_
  · refine phoareStmt_if_ge ?_ ?_
    · phoare_while_ge 1 variant (§n - §i).toNat
      case body =>
        stmt_wp
        phoare_wp 3
        phoare_skip
        intros
        split <;> simp [bdistr_expected_one]
      case exit => trivial
      case decreases =>
        intro k
        hoare_wp 3
        hoare_split 1
        refine hoare_seq (hoare_if_wp (hoare_seq (hoare_assign_wp _ _ _) (hoare_sample_wp _ _))
          (hoare_skip_wp _)) ?_
        hoare_wp 2
        hoare_skip
        rintro i n _ _ ⟨hlt, rfl⟩
        simp only [decide_eq_true_eq] at hlt
        exact ⟨fun _ _ _ => by omega, fun _ => by omega⟩
      phoare_skip
      intros; exact le_rfl
    · phoare_skip
      intros; exact le_rfl
  · phoare_wp 5
    phoare_skip
    intros; exact le_rfl

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

omit [BlockSponge.Params] [Params] in
/-- `BIRO.IRO` touches `BIRO.IRO.mp` only.  Not an EC lemma. -/
@[fp_bound] theorem fvP_IRO_asF :
    FVP.fvP BlockSponge.BIRO.IRO.asF ≤ (BlockSponge.BIRO.IRO.mp).footprint := by
  fp_module BlockSponge.BIRO.IRO.mp

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

/-- `Valid(F).f` is lossless when `F.f` is.  Not an EC lemma. -/
theorem Valid_f_ll (F : DFUNCTIONALITY)
    (hF : (Indifferentiability.DFUNCTIONALITY.f state (List block × ℤ) (List block)
      F).procedure.IsLossless) :
    (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
      (Module.app Valid F)).procedure.IsLossless := by
  have hB := IRO_f_ll (fun _ => true) BIRO2.IRO.mp
  rw [Procedure.isLossless_iff_phoareProc] at hF hB ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 7
  phoare_simp [hF, hB]
  phoare_skip
  simp

omit [Params] in
/-- `Last(F).f` is lossless when `F.f` is.  Not an EC lemma. -/
theorem Last_f_ll (F : DFUNCTIONALITY)
    (hF : (Indifferentiability.DFUNCTIONALITY.f state (List block × ℤ) (List block)
      F).procedure.IsLossless) :
    (Indifferentiability.DFUNCTIONALITY.f state (List block) block
      (Module.app Last F)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hF ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 5
  phoare_simp [hF]
  phoare_skip
  simp

omit [BlockSponge.Params] [Params] in
/-- `S(F).f` is lossless when `F.f` is.  Not an EC lemma. -/
theorem S_f_ll (F : SLCommon.DFUNCTIONALITY)
    (hF : (Indifferentiability.DFUNCTIONALITY.f state (List block) block
      F).procedure.IsLossless) :
    (Indifferentiability.PRIMITIVE.f state (List block) block
      (Module.app Gconcl.S F)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hF ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 4
  phoare_skip
  intros
  split
  · split
    · convert hF _ _ trivial using 2
      funext _ _
      simp only [ite_self]
      exact Gext.cdistr_expected_one
    · simp [bdistr_expected_one, Gext.cdistr_expected_one]
  · rfl

omit [BlockSponge.Params] [Params] in
/-- `S(F).fi` is lossless.  Not an EC lemma. -/
theorem S_fi_ll (F : SLCommon.DFUNCTIONALITY) :
    (Indifferentiability.PRIMITIVE.fi state (List block) block
      (Module.app Gconcl.S F)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 4
  phoare_skip
  simp [bdistr_expected_one, Gext.cdistr_expected_one]

/-- `SimLast(S)(F).f` is lossless when `F.f` is.  Not an EC lemma. -/
theorem SimLast_f_ll (F : DFUNCTIONALITY)
    (hF : (Indifferentiability.DFUNCTIONALITY.f state (List block × ℤ) (List block)
      F).procedure.IsLossless) :
    (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
      (Module.app (SimLast Gconcl.S) F)).procedure.IsLossless := by
  have hS := S_f_ll _ (Last_f_ll _ (Valid_f_ll F hF))
  rw [Procedure.isLossless_iff_phoareProc] at hS ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 4
  phoare_simp [hS]
  phoare_skip
  simp

/-- `SimLast(S)(F).fi` is lossless.  Not an EC lemma. -/
theorem SimLast_fi_ll (F : DFUNCTIONALITY) :
    (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
      (Module.app (SimLast Gconcl.S) F)).procedure.IsLossless := by
  have hS := S_fi_ll (Module.app Last (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ)
    (List block) (Module.app Valid F)))
  rw [Procedure.isLossless_iff_phoareProc] at hS ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 4
  phoare_simp [hS]
  phoare_skip
  simp

omit [Params] in
/-- `FC(F).f` is lossless when `F.f` is.  Not an EC lemma. -/
theorem FC_f_ll (F : DFUNCTIONALITY)
    (hF : (Indifferentiability.DFUNCTIONALITY.f state (List block × ℤ) (List block)
      F).procedure.IsLossless) :
    (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
      (Module.app BlockSponge.FC F)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hF ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 6
  phoare_simp [hF]
  phoare_skip
  simp

omit [Params] in
/-- `PC(P).f` is lossless when `P.f` is.  Not an EC lemma. -/
theorem PC_f_ll (P : DPRIMITIVE)
    (hP : (Indifferentiability.DPRIMITIVE.f state (List block × ℤ) (List block)
      P).procedure.IsLossless) :
    (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
      (Module.app BlockSponge.PC P)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hP ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 5
  phoare_simp [hP]
  phoare_skip
  simp

omit [Params] in
/-- `PC(P).fi` is lossless when `P.fi` is.  Not an EC lemma. -/
theorem PC_fi_ll (P : DPRIMITIVE)
    (hP : (Indifferentiability.DPRIMITIVE.fi state (List block × ℤ) (List block)
      P).procedure.IsLossless) :
    (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
      (Module.app BlockSponge.PC P)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hP ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 5
  phoare_simp [hP]
  phoare_skip
  simp

/-- `DSqueeze(F).f` is lossless when `F.f` is: its loop is counted.  Not an EC lemma (EC:
`while(true)(n-i)` in `A_lossless`). -/
theorem DSqueeze_f_ll (F : SLCommon.DFUNCTIONALITY)
    (hF : (Indifferentiability.DFUNCTIONALITY.f state (List block) block
      F).procedure.IsLossless) :
    (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
      (Module.app DSqueeze F)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hF ⊢
  refine phoareProc_eq_of_le_ge (fun _ _ _ => Procedure.ewp_const_le _ _ _ _) ?_
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_split 1
  refine phoareStmt_seq_ge_one ?_ ?_
  · refine phoareStmt_if_ge ?_ ?_
    · phoare_while_ge 1 variant (§n - §i).toNat
      case body =>
        phoare_wp 3
        phoare_simp [hF]
        phoare_skip
        intros
        simp
      case exit => trivial
      case decreases =>
        intro k
        hoare_split 1
        refine hoare_seq (hoare_if_wp (hoare_call_wp _ _ _ (hoareProc_true _) _)
          (hoare_skip_wp _)) ?_
        hoare_wp 2
        hoare_skip
        rintro i n ⟨hlt, rfl⟩
        simp only [decide_eq_true_eq] at hlt
        exact ⟨fun _ _ _ => by omega, fun _ => by omega⟩
      phoare_wp 1
      phoare_simp [hF]
      phoare_skip
      intros; exact le_rfl
    · phoare_skip
      intros; exact le_rfl
  · phoare_wp 6
    phoare_skip
    intros; exact le_rfl

omit [BlockSponge.Params] [Params] in
/-- `DSqueeze` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_DSqueeze : FVP.fvP DSqueeze ≤ ⊥ := by
  fp_module

/-! ## The section `Real_Ideal` -/

section Real_Ideal

/-- EC's `A_lossless`.  `{-A(D)}` is `glob A(D)`: `C.c` and `glob D` (as for `DRestr_ll`). -/
theorem A_lossless (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) :
    D_lossless D →
    ∀ (F : SLCommon.DFUNCTIONALITY) (P0 : SLCommon.DPRIMITIVE),
      FVP.fvP F ≤ ((BlockSponge.C.c).footprint ⊔ (FVP.fvP D).glob)ᶜ →
      FVP.fvP P0 ≤ ((BlockSponge.C.c).footprint ⊔ (FVP.fvP D).glob)ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P0).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P0).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app (A D) (Module.pair F P0)).procedure.IsLossless := by
  intro D_ll F P0 hF hP p_ll pi_ll f_ll
  unfold DRestrictions_Real_Ideal at _hDd
  have hPf : (Indifferentiability.DPRIMITIVE.f state (List block × ℤ) (List block)
      (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.DPRIMITIVE.f state (List block) block P0,
          fi := Indifferentiability.DPRIMITIVE.fi state (List block) block
            P0 })).procedure.IsLossless := by
    simpa only [Indifferentiability.DPRIMITIVE.f.mk_simp] using p_ll
  have hPfi : (Indifferentiability.DPRIMITIVE.fi state (List block × ℤ) (List block)
      (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.DPRIMITIVE.f state (List block) block P0,
          fi := Indifferentiability.DPRIMITIVE.fi state (List block) block
            P0 })).procedure.IsLossless := by
    simpa only [Indifferentiability.DPRIMITIVE.fi.mk_simp] using pi_ll
  have hFf : (Indifferentiability.DFUNCTIONALITY.f state (List block × ℤ) (List block)
      (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
            (Module.app DSqueeze F) })).procedure.IsLossless := by
    simpa only [Indifferentiability.DFUNCTIONALITY.f.mk_simp] using DSqueeze_f_ll F f_ll
  have hll := D_ll
    (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
      { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
          (Module.app BlockSponge.FC (Indifferentiability.DFUNCTIONALITY.mk state
            (List block × ℤ) (List block)
            { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
                (Module.app DSqueeze F) })) })
    (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
      { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
          (Module.app BlockSponge.PC (Indifferentiability.DPRIMITIVE.mk state
            (List block × ℤ) (List block)
            { f := Indifferentiability.DPRIMITIVE.f state (List block) block P0,
              fi := Indifferentiability.DPRIMITIVE.fi state (List block) block P0 })),
        fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
          (Module.app BlockSponge.PC (Indifferentiability.DPRIMITIVE.mk state
            (List block × ℤ) (List block)
            { f := Indifferentiability.DPRIMITIVE.f state (List block) block P0,
              fi := Indifferentiability.DPRIMITIVE.fi state (List block) block P0 })) })
    (by fp_disjoint) (by fp_disjoint)
    (by simpa only [Indifferentiability.DPRIMITIVE.f.mk_simp] using PC_f_ll _ hPf)
    (by simpa only [Indifferentiability.DPRIMITIVE.fi.mk_simp] using PC_fi_ll _ hPfi)
    (by simpa only [Indifferentiability.DFUNCTIONALITY.f.mk_simp] using FC_f_ll _ hFf)
  rw [Procedure.isLossless_iff_phoareProc] at hll ⊢
  phoare_proc_to_stmt
  repeat phoare_inline 0
  phoare_wp 20
  phoare_simp [hll]
  phoare_skip
  simp

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

/-- EC's local `Neg_D_lossless`.  `{-Neg_D(D)}` is `glob D`: `Neg_D` has no globals. -/
theorem Neg_D_lossless (D : DISTINGUISHER) (D_ll : D_lossless D) (F : DFUNCTIONALITY)
    (P0 : DPRIMITIVE)
    (hF : FVP.fvP F ≤ (FVP.fvP D).globᶜ)
    (hP : FVP.fvP P0 ≤ (FVP.fvP D).globᶜ) :
    (Indifferentiability.DPRIMITIVE.f state (List block × ℤ) (List block) P0).procedure.IsLossless →
    (Indifferentiability.DPRIMITIVE.fi state (List block × ℤ) (List block)
      P0).procedure.IsLossless →
    (Indifferentiability.DFUNCTIONALITY.f state (List block × ℤ) (List block)
      F).procedure.IsLossless →
    (Module.app (Neg_D D) (Module.pair F P0)).procedure.IsLossless := by
  intro p_ll pi_ll f_ll
  have hll := D_ll F P0 hF hP p_ll pi_ll f_ll
  rw [Procedure.isLossless_iff_phoareProc] at hll ⊢
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 3
  phoare_simp [hll]
  phoare_skip
  simp

theorem useful (m mi : FMap state state) (a : state) :
    invm m mi → ¬ FMap.dom m a → is_lossless (dexcepted (dprod bdistr cdistr) (FMap.rng m)) :=
  fun _ h => EC.Strong_RP_RF.excepted_lossless state SLCommon.dstate ConcreteF.Switching.uD_uf_fu m
    ⟨a, h⟩

theorem invmC (m mi : FMap state state) : invm m mi ↔ invm mi m :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

/-- EC's local `Real_lossless`. -/
theorem Real_lossless (D : DISTINGUISHER) (_hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (_D_ll : D_lossless D) :
    (RealIndif Sponge P (DRestr (Neg_D D))).procedure.IsLossless := by
  sorry

/-- EC's local `Ideal_lossless`. -/
theorem Ideal_lossless (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (D_ll : D_lossless D) :
    (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S)
      (DRestr (Neg_D D))).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  have hI : (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
      BlockSponge.BIRO.IRO.asF).procedure.IsLossless := by
    simpa only [BlockSponge.BIRO.IRO.asF, Indifferentiability.FUNCTIONALITY.f.mk_simp]
      using IRO_f_ll BlockSponge.BIRO.valid BlockSponge.BIRO.IRO.mp
  have hIv : (Indifferentiability.DFUNCTIONALITY.f state (List block × ℤ) (List block)
      (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
        BlockSponge.BIRO.IRO.asF)).procedure.IsLossless := by
    simpa only [Indifferentiability.FUNCTIONALITY.view_f] using hI
  unfold DRestrictions_Real_Ideal at _hDd
  have hPf : (Indifferentiability.DPRIMITIVE.f state (List block × ℤ) (List block)
      (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
            (Module.app (SimLast Gconcl.S) (Indifferentiability.FUNCTIONALITY.view state
              (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF)),
          fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
            (Module.app (SimLast Gconcl.S) (Indifferentiability.FUNCTIONALITY.view state
              (List block × ℤ) (List block)
                BlockSponge.BIRO.IRO.asF)) })).procedure.IsLossless := by
    simpa only [Indifferentiability.DPRIMITIVE.f.mk_simp] using SimLast_f_ll _ hIv
  have hPfi : (Indifferentiability.DPRIMITIVE.fi state (List block × ℤ) (List block)
      (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
            (Module.app (SimLast Gconcl.S) (Indifferentiability.FUNCTIONALITY.view state
              (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF)),
          fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
            (Module.app (SimLast Gconcl.S) (Indifferentiability.FUNCTIONALITY.view state
              (List block × ℤ) (List block)
                BlockSponge.BIRO.IRO.asF)) })).procedure.IsLossless := by
    simpa only [Indifferentiability.DPRIMITIVE.fi.mk_simp] using SimLast_fi_ll _
  have hFf : (Indifferentiability.DFUNCTIONALITY.f state (List block × ℤ) (List block)
      (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
            BlockSponge.BIRO.IRO.asF })).procedure.IsLossless := by
    simpa only [Indifferentiability.DFUNCTIONALITY.f.mk_simp] using hI
  have hll := D_ll
    (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
      { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
          (Module.app BlockSponge.FC (Indifferentiability.DFUNCTIONALITY.mk state
            (List block × ℤ) (List block)
            { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
                BlockSponge.BIRO.IRO.asF })) })
    (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
      { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
          (Module.app BlockSponge.PC (Indifferentiability.DPRIMITIVE.mk state
            (List block × ℤ) (List block)
            { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
                (Module.app (SimLast Gconcl.S) (Indifferentiability.FUNCTIONALITY.view state
                  (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF)),
              fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
                (Module.app (SimLast Gconcl.S) (Indifferentiability.FUNCTIONALITY.view state
                  (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF)) })),
        fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
          (Module.app BlockSponge.PC (Indifferentiability.DPRIMITIVE.mk state
            (List block × ℤ) (List block)
            { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
                (Module.app (SimLast Gconcl.S) (Indifferentiability.FUNCTIONALITY.view state
                  (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF)),
              fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
                (Module.app (SimLast Gconcl.S) (Indifferentiability.FUNCTIONALITY.view state
                  (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF)) })) })
    (by fp_disjoint) (by fp_disjoint)
    (by simpa only [Indifferentiability.DPRIMITIVE.f.mk_simp] using PC_f_ll _ hPf)
    (by simpa only [Indifferentiability.DPRIMITIVE.fi.mk_simp] using PC_fi_ll _ hPfi)
    (by simpa only [Indifferentiability.DFUNCTIONALITY.f.mk_simp] using FC_f_ll _ hFf)
  rw [Procedure.isLossless_iff_phoareProc] at hll
  unfold IdealIndif Indifferentiability.GIdeal
  repeat phoare_inline 0
  phoare_wp 20
  phoare_simp [hll]
  phoare_skip
  simp

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
  intro D_ll m
  have h1 := concl D hD _hDd D_ll m
  have h2 := Real_Ideal_Abs.neg_D_concl D hD _hDd D_ll m
  rw [abs_sub_le_iff]
  constructor <;> linarith

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

section equal2_steps

variable (IRO2_RO_m : Lens (FMap (List block × ℤ) block) VariableAssignment)
  [Lens.Disjoint IRO2_RO_m Simulator.m] [Lens.Disjoint Simulator.m IRO2_RO_m]
  [Lens.Disjoint IRO2_RO_m Simulator.mi] [Lens.Disjoint Simulator.mi IRO2_RO_m]
  [Lens.Disjoint IRO2_RO_m Simulator.paths] [Lens.Disjoint Simulator.paths IRO2_RO_m]
  [Lens.Disjoint IRO2_RO_m Simulator.unvalid_map] [Lens.Disjoint Simulator.unvalid_map IRO2_RO_m]
  [Lens.Disjoint IRO2_RO_m BlockSponge.BIRO.IRO.mp]
  [Lens.Disjoint BlockSponge.BIRO.IRO.mp IRO2_RO_m]
  [Lens.Disjoint IRO2_RO_m BlockSponge.C.c] [Lens.Disjoint BlockSponge.C.c IRO2_RO_m]
  [Lens.Disjoint IRO2_RO_m Gconcl.S.m] [Lens.Disjoint Gconcl.S.m IRO2_RO_m]
  [Lens.Disjoint IRO2_RO_m Gconcl.S.mi] [Lens.Disjoint Gconcl.S.mi IRO2_RO_m]
  [Lens.Disjoint IRO2_RO_m Gconcl.S.paths] [Lens.Disjoint Gconcl.S.paths IRO2_RO_m]

/-- `equal2`'s invariant (EC's `={BIRO.IRO.mp, C.c, Simulator.m, Simulator.mi, Simulator.paths}
/\ Simulator.unvalid_map{1} = IRO2.RO.m{2}`), in the shape of `sInv` (with `={glob S}`, which
neither side writes) so that `PC_f_sInv` lifts its steps. -/
def e2Inv (g₁ g₂ : VariableAssignment) : Prop := sInv
  (Lens.pair Simulator.m (Lens.pair Simulator.mi (Lens.pair Simulator.paths
    (Lens.pair Simulator.unvalid_map BlockSponge.BIRO.IRO.mp))))
  (Lens.pair Simulator.m (Lens.pair Simulator.mi (Lens.pair Simulator.paths
    (Lens.pair IRO2_RO_m BlockSponge.BIRO.IRO.mp)))) Eq g₁ g₂

/-- Close a side condition about `e2Inv`: unfold it, read through the writes, `simp_all`. -/
local macro "e2_close" : tactic => `(tactic| (
  intros
  (try simp only [e2Inv, sInv, Lens.pair, Prod.mk.injEq] at *)
  (try simp_reads)
  (try simp_all)
  (try omega)))

set_option maxHeartbeats 4000000 in
-- the inlined simulators, with `IRO.f`'s loop and `LRO.get`
omit [Lens.Disjoint IRO2_RO_m Simulator.unvalid_map] [Lens.Disjoint Simulator.unvalid_map IRO2_RO_m]
    [Lens.Disjoint BlockSponge.C.c IRO2_RO_m] [Lens.Disjoint Gconcl.S.m IRO2_RO_m]
    [Lens.Disjoint Gconcl.S.mi IRO2_RO_m] [Lens.Disjoint Gconcl.S.paths IRO2_RO_m] in
/-- `Simulator(BIRO.IRO).f ~ Simu(IRO2.LRO)(BIRO.IRO).f` under `e2Inv` (EC: `equal2`'s inner
`call`; `Simu`'s sampling loop is a no-op for `LRO`, `while{2}`, and `LRO.get` samples whether or
not the entry is known). -/
theorem Simulator_f_Simu :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ e2Inv IRO2_RO_m g₁ g₂)
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app Simulator (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ)
          (List block) BlockSponge.BIRO.IRO.asF))).procedure
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app (Simu (IRO2.LRO IRO2_RO_m)) (Indifferentiability.FUNCTIONALITY.view state
          (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ e2Inv IRO2_RO_m g₁ g₂) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    e2_close
  · equiv_if
    case guard => e2_close
    case «else» =>
      stmt_wp
      equiv_skip
      e2_close
    case «then» =>
      equiv_seq 5 5 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧
        e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
      · equiv_if
        case guard => e2_close
        case «else» =>
          equiv_rnd
          equiv_skip
          e2_close
        case «then» =>
          equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧
            e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
          · stmt_wp
            equiv_skip
            e2_close
          · equiv_if
            case guard => e2_close
            case «then» =>
              stmt_wp
              equiv_seq 1 1 : (§x1{1} = §x1{2} ∧ §n{1} = §n{2} ∧ §i{1} = §i0{2} ∧ §bs{1} = §bs{2} ∧
                    §x0{1} = §x0{2} ∧ e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
              · stmt_wp
                equiv_skip
                e2_close
              · equiv_if
                case guard => e2_close
                case «else» =>
                  equiv_skip
                  e2_close
                case «then» =>
                  equiv_while (§x1{1} = §x1{2} ∧ §n{1} = §n{2} ∧ §i{1} = §i0{2} ∧ §bs{1} = §bs{2} ∧
                    §x0{1} = §x0{2} ∧ e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
                  case body =>
                    stmt_wp
                    equiv_seq 1 1 : (§x2{1} = §x2{2} ∧ §n0{1} = §n0{2} ∧ §x2{1} = §x1{1} ∧
                        §n0{1} = §i{1} ∧ (§x1{1} = §x1{2} ∧ §n{1} = §n{2} ∧ §i{1} = §i0{2} ∧
                            §bs{1} = §bs{2} ∧
                    §x0{1} = §x0{2} ∧ e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2}))
                    · stmt_wp
                      equiv_skip
                      e2_close
                    · equiv_if
                      case guard => e2_close
                      case «then» =>
                        stmt_wp
                        equiv_rnd
                        equiv_skip
                        e2_close
                      case «else» =>
                        equiv_skip
                        e2_close
                  case guard => e2_close
                  case exit => e2_close
                  equiv_skip
                  e2_close
            case «else» =>
              equiv_if
              case guard => e2_close
              case «else» =>
                stmt_wp
                equiv_skip
                e2_close
              case «then» =>
                stmt_wp
                equiv_seq 1 3 : (§x0{1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧ 0 < §k{1} ∧
                    e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
                · equiv_while{2} (§x0{1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧ 0 < §k{1} ∧
                    e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2}) (§k{2} - §i{2}).toNat
                  case lossless =>
                    intro σ₁ σ _ _
                    simp only [Stmt.ewp_seq, Stmt.ewp_assign]
                  case «variant» =>
                    intro σ₁ k
                    hoare_wp 3
                    refine hoare_skip_of_imp fun σ h => ?_
                    obtain ⟨hpre, hlt, hk⟩ := h
                    refine ⟨hpre, ?_⟩
                    have h1 : (localVarLens "i" ℤ).get σ < (localVarLens "k" ℤ).get σ := by
                      simpa using hlt
                    have h2 : ((localVarLens "k" ℤ).get σ - (localVarLens "i" ℤ).get σ).toNat = k :=
                      hk
                    subst h2
                    refine (Int.toNat_lt_toNat ?_).mpr ?_
                    · linarith
                    · linarith
                  case exit => e2_close
                  stmt_wp
                  equiv_skip
                  e2_close
                · equiv_if{1}
                  case «then» =>
                    stmt_wp
                    equiv_rnd
                    stmt_wp
                    equiv_skip
                    rintro g₁ g₂ x0 q k _ _ _ ⟨⟨rfl, rfl, rfl, hk, hI⟩, hnd⟩ a -
                    have hI' := hI
                    simp only [e2Inv, sInv, Lens.pair, Prod.mk.injEq] at hI'
                    obtain ⟨hs1, hs2, hs3, ⟨hm, hmi, hpa, hun, hiro⟩, hc⟩ := hI'
                    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hnd
                    rw [hun] at hnd
                    simp only [hnd, decide_false, Bool.not_false, if_true, FMap.get_set_sameE]
                    refine ⟨by trivial, by trivial, ?_⟩
                    simp only [e2Inv, sInv, Lens.pair, Prod.mk.injEq]
                    simp_reads
                    simp_all
                  case «else» =>
                    stmt_wp{2} 1
                    stmt_wp
                    equiv_skip
                    rintro g₁ g₂ x0 q k _ _ _ ⟨⟨rfl, rfl, rfl, hk, hI⟩, hd⟩
                    have hI' := hI
                    simp only [e2Inv, sInv, Lens.pair, Prod.mk.injEq] at hI'
                    obtain ⟨-, -, -, ⟨hm, hmi, hpa, hun, hiro⟩, hc⟩ := hI'
                    simp only [Bool.not_eq_false', decide_eq_true_eq] at hd
                    rw [hun] at hd
                    refine ⟨bdistr_expected_one, fun a _ => ?_⟩
                    simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
                    exact ⟨by trivial, by rw [hun], hI⟩
      · stmt_wp
        equiv_rnd
        equiv_skip
        e2_close


omit [Lens.Disjoint IRO2_RO_m Simulator.m] [Lens.Disjoint IRO2_RO_m Simulator.mi]
    [Lens.Disjoint IRO2_RO_m Simulator.paths] [Lens.Disjoint IRO2_RO_m Simulator.unvalid_map]
    [Lens.Disjoint Simulator.unvalid_map IRO2_RO_m]
    [Lens.Disjoint BlockSponge.BIRO.IRO.mp IRO2_RO_m]
    [Lens.Disjoint IRO2_RO_m BlockSponge.C.c] [Lens.Disjoint BlockSponge.C.c IRO2_RO_m]
    [Lens.Disjoint IRO2_RO_m Gconcl.S.m] [Lens.Disjoint Gconcl.S.m IRO2_RO_m]
    [Lens.Disjoint IRO2_RO_m Gconcl.S.mi] [Lens.Disjoint Gconcl.S.mi IRO2_RO_m]
    [Lens.Disjoint IRO2_RO_m Gconcl.S.paths] [Lens.Disjoint Gconcl.S.paths IRO2_RO_m] in
/-- `Simulator(BIRO.IRO).fi ~ Simu(IRO2.LRO)(BIRO.IRO).fi` under `e2Inv` (the same code). -/
theorem Simulator_fi_Simu :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ e2Inv IRO2_RO_m g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app Simulator (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ)
          (List block) BlockSponge.BIRO.IRO.asF))).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app (Simu (IRO2.LRO IRO2_RO_m)) (Indifferentiability.FUNCTIONALITY.view state
          (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ e2Inv IRO2_RO_m g₁ g₂) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§x0{1} = §x0{2} ∧ e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    e2_close
  · equiv_if
    case guard => e2_close
    case «else» =>
      stmt_wp
      equiv_skip
      e2_close
    case «then» =>
      stmt_wp
      equiv_rnd
      equiv_rnd
      equiv_skip
      e2_close

omit [Params] [Lens.Disjoint IRO2_RO_m Simulator.m] [Lens.Disjoint IRO2_RO_m Simulator.mi]
    [Lens.Disjoint IRO2_RO_m Simulator.paths] [Lens.Disjoint IRO2_RO_m Simulator.unvalid_map]
    [Lens.Disjoint Simulator.unvalid_map IRO2_RO_m] [Lens.Disjoint IRO2_RO_m BlockSponge.C.c]
    [Lens.Disjoint IRO2_RO_m Gconcl.S.m] [Lens.Disjoint IRO2_RO_m Gconcl.S.mi]
    [Lens.Disjoint IRO2_RO_m Gconcl.S.paths] in
/-- `FC(BIRO.IRO).f` keeps `e2Inv`: the same procedure on both sides, within `BIRO.IRO.mp` and
`C.c` (`prhlProc_refl_of_within`), framed by the rest (`prhlProc_frame_of_writesKeep`). -/
theorem FC_IRO_e2 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ e2Inv IRO2_RO_m g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              BlockSponge.BIRO.IRO.asF }))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              BlockSponge.BIRO.IRO.asF }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ e2Inv IRO2_RO_m g₁ g₂) := by
  have h0 := prhlProc_refl_of_within (X := Lens.pair BlockSponge.BIRO.IRO.mp BlockSponge.C.c)
    (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
      (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
            BlockSponge.BIRO.IRO.asF }))).procedure
    (by within_lens) (by within_lens)
  have h1 := prhlProc_frame_of_writesKeep
    (Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi (Lens.pair Gconcl.S.paths
      (Lens.pair Simulator.m (Lens.pair Simulator.mi (Lens.pair Simulator.paths
        Simulator.unvalid_map)))))).get
    (Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi (Lens.pair Gconcl.S.paths
      (Lens.pair Simulator.m (Lens.pair Simulator.mi (Lens.pair Simulator.paths
        IRO2_RO_m)))))).get Eq
    (by writes_keep <;> (intro v σ; simp only [Lens.pair]; simp_reads; try trivial))
    (by writes_keep <;> (intro v σ; simp only [Lens.pair]; simp_reads; try trivial)) h0
  refine prhlProc_conseq h1 ?_ ?_
  · rintro a₁ g₁ a₂ g₂ ⟨rfl, hI⟩
    simp only [e2Inv, sInv, Lens.pair, Prod.mk.injEq] at hI ⊢
    obtain ⟨h1, h2, h3, ⟨h4, h5, h6, h7, h8⟩, h9⟩ := hI
    exact ⟨⟨trivial, h8, h9⟩, h1, h2, h3, h4, h5, h6, h7⟩
  · rintro r₁ g₁ r₂ g₂ ⟨⟨rfl, hX⟩, hK⟩
    simp only [e2Inv, sInv, Lens.pair, Prod.mk.injEq] at hX hK ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hK
    exact ⟨trivial, h1, h2, h3, ⟨h4, h5, h6, h7, hX.1⟩, hX.2⟩

end equal2_steps

set_option maxHeartbeats 4000000 in
-- the abstract call's oracle side conditions
/-- `equal2`'s `byequiv` (EC: `proc; inline*; auto; call (: ={BIRO.IRO.mp, C.c, Simulator.m,
Simulator.mi, Simulator.paths} /\ Simulator.unvalid_map{1} = IRO2.RO.m{2})`). -/
theorem equal2_equiv (D : DISTINGUISHER) (hD : Module.ECModule D distExt) (_hDd : DRestrictions D)
    (IRO2_RO_m : Lens (FMap (List block × ℤ) block) VariableAssignment)
    (_hfresh : IRO2_RO_m.footprint ≤ (FVP.fvP D ⊔ DRestrictions.footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (IdealIndif BlockSponge.BIRO.IRO.asF Simulator (DRestr D)).procedure
      (L D (IRO2.LRO IRO2_RO_m)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  unfold DRestrictions DRestrictions.footprint at _hDd
  unfold DRestrictions.footprint at _hfresh
  have hIRO2D : FVP.fvP D ≤ (IRO2_RO_m.footprint)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hfresh.trans (Footprint.compl_antimono le_sup_left))
  haveI : Lens.Disjoint IRO2_RO_m Simulator.m :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Simulator.m IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m Simulator.mi :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Simulator.mi IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m Simulator.paths :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Simulator.paths IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m Simulator.unvalid_map :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Simulator.unvalid_map IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m BlockSponge.BIRO.IRO.mp :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint BlockSponge.BIRO.IRO.mp IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m BlockSponge.C.c :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint BlockSponge.C.c IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m Gconcl.S.m :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Gconcl.S.m IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m Gconcl.S.mi :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Gconcl.S.mi IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m Gconcl.S.paths :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Gconcl.S.paths IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  have hgm : (Gconcl.S.m).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hgmi : (Gconcl.S.mi).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hgpa : (Gconcl.S.paths).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hsm : (Simulator.m).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hsmi : (Simulator.mi).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hspa : (Simulator.paths).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hsun : (Simulator.unvalid_map).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hro2 : (IRO2_RO_m).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hiro : (BlockSponge.BIRO.IRO.mp).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hcc : (BlockSponge.C.c).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  let Lg := Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi (Lens.pair Gconcl.S.paths
    (Lens.pair Simulator.m (Lens.pair Simulator.mi (Lens.pair Simulator.paths
      (Lens.pair Simulator.unvalid_map (Lens.pair IRO2_RO_m
        (Lens.pair BlockSponge.BIRO.IRO.mp BlockSponge.C.c))))))))
  let I := fun (x y : SLCommon.smap × SLCommon.smap × FMap capacity (List block × block) ×
      FMap state state × FMap state state × FMap capacity (List block × block) ×
      FMap (List block × ℤ) block × FMap (List block × ℤ) block ×
      FMap (List block × ℤ) block × ℤ) =>
    x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧
      (x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1) =
        (y.2.2.2.1, y.2.2.2.2.1, y.2.2.2.2.2.1, y.2.2.2.2.2.2.2.1, y.2.2.2.2.2.2.2.2.1) ∧
      x.2.2.2.2.2.2.2.2.2 = y.2.2.2.2.2.2.2.2.2
  have hI : ∀ g₁ g₂, I (Lg.get g₁) (Lg.get g₂) ↔ e2Inv IRO2_RO_m g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (Lg.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [Lg, Footprint.lens_pair]
    refine sup_le (by fp_disjoint) (sup_le (by fp_disjoint) (sup_le (by fp_disjoint)
      (sup_le (by fp_disjoint) (sup_le (by fp_disjoint) (sup_le (by fp_disjoint)
        (sup_le (by fp_disjoint) (sup_le (by fp_disjoint) (sup_le (by fp_disjoint)
          (by fp_disjoint)))))))))
  unfold L IdealIndif Indifferentiability.GIdeal
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    subst h
    refine ⟨?_, ?_⟩
    · simp only [touched_set_of_le_compl (show (BlockSponge.C.c).footprint ≤ (FVP.fvP D)ᶜ by
          fp_disjoint),
        touched_set_of_le_compl (show (BlockSponge.BIRO.IRO.mp).footprint ≤ (FVP.fvP D)ᶜ by
          fp_disjoint),
        touched_set_of_le_compl (show (IRO2_RO_m).footprint ≤ (FVP.fvP D)ᶜ by fp_disjoint),
        touched_set_of_le_compl (show (Simulator.unvalid_map).footprint ≤ (FVP.fvP D)ᶜ by
          fp_disjoint),
        touched_set_of_le_compl (show (Simulator.paths).footprint ≤ (FVP.fvP D)ᶜ by fp_disjoint),
        touched_set_of_le_compl (show (Simulator.mi).footprint ≤ (FVP.fvP D)ᶜ by fp_disjoint),
        touched_set_of_le_compl (show (Simulator.m).footprint ≤ (FVP.fvP D)ᶜ by fp_disjoint)]
    · simp only [Lg, I, Lens.pair]
      simp_reads
      trivial
  · stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_moduleF Lg D distExt hD.representable
      (FVP.fvP D) le_rfl hL I ?hc _ _ ?horacle) ?_
    case hc =>
      intro _ n
      cases n with
      | zero => exact inferInstanceAs (Countable (List block × ℤ))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable state)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable state)
          | succ n => nomatch n
    case horacle =>
      intro _ n
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair, Indifferentiability.DFUNCTIONALITY.f.mk_simp]
        exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
          (prhlProc_conseq (FC_IRO_e2 IRO2_RO_m) (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
            (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
            (prhlProc_conseq (PC_f_sInv (Simulator_f_Simu IRO2_RO_m))
              (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
              (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
              Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              (prhlProc_conseq (PC_fi_sInv (Simulator_fi_Simu IRO2_RO_m))
                (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
                (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, -, -⟩
    simp_reads
    trivial

omit [SLCommon.Params] [BlockSponge.Params] [Params] in
/-- EC's `last_rcons`. -/
theorem last_rcons_eq {α : Type} (x0 : α) (s : List α) (x : α) : last x0 (rcons s x) = x := by
  simp [last, rcons]

section equal1_steps

variable (IRO2_RO_m : Lens (FMap (List block × ℤ) block) VariableAssignment)
  [Lens.Disjoint IRO2_RO_m Simulator.m] [Lens.Disjoint Simulator.m IRO2_RO_m]
  [Lens.Disjoint IRO2_RO_m Simulator.mi] [Lens.Disjoint Simulator.mi IRO2_RO_m]
  [Lens.Disjoint IRO2_RO_m Simulator.paths] [Lens.Disjoint Simulator.paths IRO2_RO_m]
  [Lens.Disjoint IRO2_RO_m BlockSponge.BIRO.IRO.mp]
  [Lens.Disjoint BlockSponge.BIRO.IRO.mp IRO2_RO_m]
  [Lens.Disjoint IRO2_RO_m BlockSponge.C.c] [Lens.Disjoint BlockSponge.C.c IRO2_RO_m]

/-- `equal1`'s invariant (EC: `={BIRO.IRO.mp, C.c} /\ ={m, mi, paths}(S, Simulator) /\
BIRO2.IRO.mp{1} = IRO2.RO.m{2}`; EC's `incl Simulator.unvalid_map{2} BIRO2.IRO.mp{1}` is not needed:
`Simu` does not use `unvalid_map`). -/
def e1Inv (g₁ g₂ : VariableAssignment) : Prop := cInv
  (Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi (Lens.pair Gconcl.S.paths
    (Lens.pair BlockSponge.BIRO.IRO.mp BIRO2.IRO.mp))))
  (Lens.pair Simulator.m (Lens.pair Simulator.mi (Lens.pair Simulator.paths
    (Lens.pair BlockSponge.BIRO.IRO.mp IRO2_RO_m)))) Eq g₁ g₂

/-- Close a side condition about `e1Inv`. -/
local macro "e1_close" : tactic => `(tactic| (
  intros
  (try simp only [e1Inv, cInv, Lens.pair, Prod.mk.injEq] at *)
  (try simp_reads)
  (try simp_all)
  (try omega)))

set_option maxHeartbeats 4000000 in
-- the inlined simulators, with three loops
omit [Lens.Disjoint BlockSponge.C.c IRO2_RO_m] in
/-- `SimLast(S)(BIRO.IRO).f ~ Simu(IRO2.RO)(BIRO.IRO).f` under `e1Inv` (EC: `equal1`'s inner `call`;
on an invalid prefix, `BIRO2.IRO.f`'s loop and `Simu`'s `RO.sample` loop fill the same entries,
and the final `RO.get` finds its entry known). -/
theorem SimLast_f_Simu :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ e1Inv IRO2_RO_m g₁ g₂)
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app (SimLast Gconcl.S) (Indifferentiability.FUNCTIONALITY.view state
          (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF))).procedure
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app (Simu (IRO2.RO.asRO IRO2_RO_m)) (Indifferentiability.FUNCTIONALITY.view state
          (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ e1Inv IRO2_RO_m g₁ g₂) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§(localVarLens "x1" state){1} = §x0{2} ∧
      e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    e1_close
  · equiv_if
    case guard => e1_close
    case «else» =>
      stmt_wp
      equiv_skip
      e1_close
    case «then» =>
      equiv_seq 5 5 : (§(localVarLens "x1" state){1} = §x0{2} ∧ §y1{1} = §y1{2} ∧
          e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
      · equiv_if
        case guard => e1_close
        case «else» =>
          equiv_rnd
          equiv_skip
          e1_close
        case «then» =>
          stmt_wp
          equiv_seq 1 1 : (§(localVarLens "x1" state){1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧
              0 < §k{1} ∧
              e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
          · stmt_wp
            equiv_skip
            rintro g₁ g₂ x _ ⟨⟨⟨rfl, hI⟩, -⟩, -⟩
            have hI' := hI
            simp only [e1Inv, cInv, Lens.pair, Prod.mk.injEq] at hI'
            obtain ⟨hc, hm, hmi, hpa, hiro, hb2⟩ := hI'
            rw [formatK, hpa]
            exact ⟨rfl, rfl, rfl, parse_gt0 _, hI⟩
          · equiv_if
            case guard => e1_close
            case «then» =>
              stmt_wp
              equiv_seq 1 1 : (§(localVarLens "x3" (List block)){1} =
                  §(localVarLens "x1" (List block)){2} ∧ §n{1} = §n{2} ∧ §i{1} = §i0{2} ∧ §bs{1} =
                      §bs{2} ∧
                  §(localVarLens "x1" state){1} = §x0{2} ∧
                      e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
              · stmt_wp
                equiv_skip
                e1_close
              · equiv_if
                case guard => e1_close
                case «else» =>
                  equiv_skip
                  e1_close
                case «then» =>
                  equiv_while (§(localVarLens "x3" (List block)){1} =
                      §(localVarLens "x1" (List block)){2} ∧ §n{1} = §n{2} ∧ §i{1} =
                          §i0{2} ∧ §bs{1} = §bs{2} ∧
                  §(localVarLens "x1" state){1} = §x0{2} ∧
                      e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
                  case body =>
                    stmt_wp
                    equiv_seq 1 1 : (§(localVarLens "x4" (List block)){1} =
                        §(localVarLens "x2" (List block)){2} ∧ §n0{1} = §n0{2} ∧
                        §(localVarLens "x4" (List block)){1} =
                            §(localVarLens "x3" (List block)){1} ∧ §n0{1} = §i{1} ∧
                                (§(localVarLens "x3" (List block)){1} =
                                    §(localVarLens "x1" (List block)){2} ∧ §n{1} = §n{2} ∧ §i{1} =
                                        §i0{2} ∧ §bs{1} = §bs{2} ∧
                  §(localVarLens "x1" state){1} = §x0{2} ∧
                      e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2}))
                    · stmt_wp
                      equiv_skip
                      e1_close
                    · equiv_if
                      case guard => e1_close
                      case «then» =>
                        stmt_wp
                        equiv_rnd
                        equiv_skip
                        e1_close
                      case «else» =>
                        equiv_skip
                        e1_close
                  case guard => e1_close
                  case exit => e1_close
                  equiv_skip
                  e1_close
            case «else» =>
              equiv_if{2}
              case «else» =>
                refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
                simp only [decide_eq_false_iff_not] at h
                exact h.2 (by rw [← h.1.1.2.2.1]; exact h.1.1.2.2.2.1)
              case «then» =>
                stmt_wp
                equiv_seq 0 3 : (last b0 §bs0{1} = oget ((§IRO2_RO_m{2}).get (§q{2}, §k{2} - 1)) ∧
                    (§IRO2_RO_m{2}).dom (§q{2}, §k{2} - 1) ∧
                        §(localVarLens "x1" state){1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧
                            0 < §k{1} ∧ e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
                · equiv_seq 1 1 : (§(localVarLens "x5" (List block)){1} = §q{2} ∧ §n1{1} = §k{2} ∧
                    §i0{1} = §i{2} ∧ 0 ≤ §i0{1} ∧
                      §i0{1} ≤ §n1{1} ∧
                      (0 < §i0{1} → last b0 §bs0{1} =
                        oget ((§IRO2_RO_m{2}).get (§q{2}, §i0{1} - 1)) ∧
                        (§IRO2_RO_m{2}).dom (§q{2}, §i0{1} - 1)) ∧
                            §(localVarLens "x1" state){1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧
                                0 < §k{1} ∧ e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
                  · stmt_wp
                    equiv_skip
                    rintro g₁ g₂ x1 q k x0 q' k' ⟨⟨⟨rfl, rfl, rfl, hk, hI⟩, -⟩, -⟩
                    exact ⟨rfl, rfl, hk.le, False.elim, rfl, rfl, rfl, hk, hI⟩
                  · equiv_if{1}
                    case «else» =>
                      refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
                      exact absurd h.2 (by decide)
                    case «then» =>
                      equiv_while (§(localVarLens "x5" (List block)){1} = §q{2} ∧ §n1{1} = §k{2} ∧
                          §i0{1} = §i{2} ∧ 0 ≤ §i0{1} ∧
                      §i0{1} ≤ §n1{1} ∧
                      (0 < §i0{1} → last b0 §bs0{1} =
                        oget ((§IRO2_RO_m{2}).get (§q{2}, §i0{1} - 1)) ∧
                        (§IRO2_RO_m{2}).dom (§q{2}, §i0{1} - 1)) ∧
                            §(localVarLens "x1" state){1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧
                                0 < §k{1} ∧ e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
                      case body =>
                        stmt_wp
                        equiv_seq 1 1 : (§x6{1} = §(localVarLens "x5" (List block)){1} ∧
                            §n2{1} = §i0{1} ∧
                            §(localVarLens "x4" (List block × ℤ)){2} = (§q{2}, §i{2}) ∧
                            §i0{1} < §n1{1} ∧ (§(localVarLens "x5" (List block)){1} = §q{2} ∧
                                §n1{1} = §k{2} ∧ §i0{1} = §i{2} ∧ 0 ≤ §i0{1} ∧
                      §i0{1} ≤ §n1{1} ∧
                      (0 < §i0{1} → last b0 §bs0{1} =
                        oget ((§IRO2_RO_m{2}).get (§q{2}, §i0{1} - 1)) ∧
                        (§IRO2_RO_m{2}).dom (§q{2}, §i0{1} - 1)) ∧
                            §(localVarLens "x1" state){1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧
                                0 < §k{1} ∧ e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2}))
                        · stmt_wp
                          equiv_skip
                          rintro g₁ g₂ x5 n1 i0 bs0 x1 q k q' k' i x0 ⟨hL, hlt⟩
                          simp only [decide_eq_true_eq] at hlt
                          exact ⟨hlt, hL⟩
                        · equiv_if{1}
                          case «then» =>
                            stmt_wp
                            equiv_rnd
                            equiv_skip
                            rintro g₁ g₂ x6 x5 n2 i0 n1 bs0 x1 q k x4 q' i k' x0
                              ⟨⟨h1, h2, h3, hlt, h5, h6, h7, h0, hle, -, h11, h12, h13, hk, hI⟩,
                                  hnd⟩ a -
                            subst h1 h2 h3 h5 h6 h7 h11 h12 h13
                            have hI' := hI
                            simp only [e1Inv, cInv, Lens.pair, Prod.mk.injEq] at hI'
                            obtain ⟨hc, hm, hmi, hpa, hiro, hb2⟩ := hI'
                            simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hnd
                            rw [hb2] at hnd
                            simp only [hnd, decide_false, Bool.not_false, if_true,
                              FMap.get_set_sameE, last_rcons_eq, add_sub_cancel_right]
                            refine ⟨trivial, trivial, trivial, by omega, by omega,
                              fun _ => ⟨trivial, (FMap.mem_set _ _ _ _).mpr (Or.inr rfl)⟩, trivial,
                              trivial, trivial, hk, ?_⟩
                            simp only [e1Inv, cInv, Lens.pair, Prod.mk.injEq]
                            simp_reads
                            simp_all
                          case «else» =>
                            stmt_wp{2} 1
                            equiv_skip
                            rintro g₁ g₂ x6 x5 n2 i0 n1 bs0 x1 q k x4 q' i k' x0
                              ⟨⟨h1, h2, h3, hlt, h5, h6, h7, h0, hle, -, h11, h12, h13, hk, hI⟩, hd⟩
                            subst h1 h2 h3 h5 h6 h7 h11 h12 h13
                            have hI' := hI
                            simp only [e1Inv, cInv, Lens.pair, Prod.mk.injEq] at hI'
                            obtain ⟨hc, hm, hmi, hpa, hiro, hb2⟩ := hI'
                            simp only [Bool.not_eq_false', decide_eq_true_eq] at hd
                            rw [hb2] at hd
                            refine ⟨bdistr_expected_one, fun a _ => ?_⟩
                            simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, if_false,
                              last_rcons_eq, add_sub_cancel_right, hb2]
                            exact ⟨trivial, trivial, trivial, by omega, by omega,
                              fun _ => ⟨trivial, trivial⟩, trivial, trivial, trivial, hk, hI⟩
                      case guard => e1_close
                      case exit =>
                        rintro g₁ g₂ x5 n1 i0 bs0 x1 q k q' k' i x0
                          ⟨h1, h2, h3, h0, hle, hL, h11, h12, h13, hk, hI⟩ hex
                        simp only [decide_eq_false_iff_not, not_lt] at hex
                        have hik : i0 = k' := by omega
                        obtain ⟨hl, hd⟩ := hL (by omega)
                        rw [hik] at hl hd
                        exact ⟨hl, hd, h11, h12, h13, hk, hI⟩
                      equiv_skip
                      intros; rename_i h; exact h
                · stmt_wp{2} 1
                  stmt_wp
                  equiv_skip
                  rintro g₁ g₂ bs0 x1 q k q' k' x0 ⟨hl, hd, h1, h2, h3, hk, hI⟩
                  refine ⟨bdistr_expected_one, fun a _ => ?_⟩
                  simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
                  exact ⟨h1, hl, hI⟩
      · stmt_wp
        equiv_rnd
        equiv_skip
        e1_close


omit [Lens.Disjoint IRO2_RO_m Simulator.m] [Lens.Disjoint IRO2_RO_m Simulator.mi]
    [Lens.Disjoint IRO2_RO_m Simulator.paths] [Lens.Disjoint IRO2_RO_m BlockSponge.BIRO.IRO.mp]
    [Lens.Disjoint IRO2_RO_m BlockSponge.C.c] [Lens.Disjoint BlockSponge.C.c IRO2_RO_m] in
/-- `SimLast(S)(BIRO.IRO).fi ~ Simu(IRO2.RO)(BIRO.IRO).fi` under `e1Inv` (`S.fi` and
`Simulator.fi` are the same code on different maps). -/
theorem SimLast_fi_Simu :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ e1Inv IRO2_RO_m g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app (SimLast Gconcl.S) (Indifferentiability.FUNCTIONALITY.view state
          (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF))).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app (Simu (IRO2.RO.asRO IRO2_RO_m)) (Indifferentiability.FUNCTIONALITY.view state
          (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ e1Inv IRO2_RO_m g₁ g₂) := by
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (§(localVarLens "x1" state){1} = §x0{2} ∧
      e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    e1_close
  · equiv_if
    case guard => e1_close
    case «else» =>
      stmt_wp
      equiv_skip
      e1_close
    case «then» =>
      stmt_wp
      equiv_rnd
      equiv_rnd
      equiv_skip
      e1_close

omit [Params] [Lens.Disjoint IRO2_RO_m Simulator.m] [Lens.Disjoint IRO2_RO_m Simulator.mi]
    [Lens.Disjoint IRO2_RO_m Simulator.paths] [Lens.Disjoint IRO2_RO_m BlockSponge.BIRO.IRO.mp]
    [Lens.Disjoint IRO2_RO_m BlockSponge.C.c] in
/-- `FC(BIRO.IRO).f` keeps `e1Inv` (as `FC_IRO_e2`). -/
theorem FC_IRO_e1 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ e1Inv IRO2_RO_m g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              BlockSponge.BIRO.IRO.asF }))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              BlockSponge.BIRO.IRO.asF }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ e1Inv IRO2_RO_m g₁ g₂) := by
  have h0 := prhlProc_refl_of_within (X := Lens.pair BlockSponge.BIRO.IRO.mp BlockSponge.C.c)
    (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
      (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
            BlockSponge.BIRO.IRO.asF }))).procedure
    (by within_lens) (by within_lens)
  have h1 := prhlProc_frame_of_writesKeep
    (Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi (Lens.pair Gconcl.S.paths BIRO2.IRO.mp))).get
    (Lens.pair Simulator.m (Lens.pair Simulator.mi (Lens.pair Simulator.paths IRO2_RO_m))).get
    Eq
    (by writes_keep <;> (intro v σ; simp only [Lens.pair]; simp_reads; try trivial))
    (by writes_keep <;> (intro v σ; simp only [Lens.pair]; simp_reads; try trivial)) h0
  refine prhlProc_conseq h1 ?_ ?_
  · rintro a₁ g₁ a₂ g₂ ⟨rfl, hI⟩
    simp only [e1Inv, cInv, Lens.pair, Prod.mk.injEq] at hI ⊢
    obtain ⟨hc, h1, h2, h3, h4, h5⟩ := hI
    exact ⟨⟨trivial, h4, hc⟩, h1, h2, h3, h5⟩
  · rintro r₁ g₁ r₂ g₂ ⟨⟨rfl, hX⟩, hK⟩
    simp only [e1Inv, cInv, Lens.pair, Prod.mk.injEq] at hX hK ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hK
    exact ⟨trivial, hX.2, h1, h2, h3, hX.1, h4⟩

end equal1_steps

set_option maxHeartbeats 4000000 in
-- the abstract call's oracle side conditions
/-- `equal1`'s `byequiv` (EC: `proc; inline*; auto; call (: ={BIRO.IRO.mp, C.c} /\
={m, mi, paths}(S, Simulator) /\ BIRO2.IRO.mp{1} = IRO2.RO.m{2} /\ …)`). -/
theorem equal1_equiv (D : DISTINGUISHER) (hD : Module.ECModule D distExt) (_hDd : DRestrictions D)
    (IRO2_RO_m : Lens (FMap (List block × ℤ) block) VariableAssignment)
    (_hfresh : IRO2_RO_m.footprint ≤ (FVP.fvP D ⊔ DRestrictions.footprint)ᶜ) :
    prhlProc (fun _ g₁ _ g₂ => g₁ = g₂)
      (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S) (DRestr D)).procedure
      (L D (IRO2.RO.asRO IRO2_RO_m)).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  unfold DRestrictions DRestrictions.footprint at _hDd
  unfold DRestrictions.footprint at _hfresh
  have hIRO2D : FVP.fvP D ≤ (IRO2_RO_m.footprint)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hfresh.trans (Footprint.compl_antimono le_sup_left))
  haveI : Lens.Disjoint IRO2_RO_m Simulator.m :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Simulator.m IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m Simulator.mi :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Simulator.mi IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m Simulator.paths :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Simulator.paths IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m Simulator.unvalid_map :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Simulator.unvalid_map IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m BlockSponge.BIRO.IRO.mp :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint BlockSponge.BIRO.IRO.mp IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m BlockSponge.C.c :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint BlockSponge.C.c IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m Gconcl.S.m :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Gconcl.S.m IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m Gconcl.S.mi :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Gconcl.S.mi IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m Gconcl.S.paths :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint Gconcl.S.paths IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  haveI : Lens.Disjoint IRO2_RO_m BIRO2.IRO.mp :=
    Lens.disjoint_of_footprint_le_compl _ _ (by fp_disjoint)
  haveI : Lens.Disjoint BIRO2.IRO.mp IRO2_RO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp (by fp_disjoint))
  have hb2 : (BIRO2.IRO.mp).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hgm : (Gconcl.S.m).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hgmi : (Gconcl.S.mi).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hgpa : (Gconcl.S.paths).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hsm : (Simulator.m).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hsmi : (Simulator.mi).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hspa : (Simulator.paths).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hsun : (Simulator.unvalid_map).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hro2 : (IRO2_RO_m).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hiro : (BlockSponge.BIRO.IRO.mp).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  have hcc : (BlockSponge.C.c).footprint ≤ (FVP.fvP D)ᶜ := by fp_disjoint
  let Lg := Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi (Lens.pair Gconcl.S.paths
    (Lens.pair Simulator.m (Lens.pair Simulator.mi (Lens.pair Simulator.paths
      (Lens.pair BIRO2.IRO.mp (Lens.pair IRO2_RO_m
        (Lens.pair BlockSponge.BIRO.IRO.mp BlockSponge.C.c))))))))
  let I := fun (x y : SLCommon.smap × SLCommon.smap × FMap capacity (List block × block) ×
      FMap state state × FMap state state × FMap capacity (List block × block) ×
      FMap (List block × ℤ) block × FMap (List block × ℤ) block ×
      FMap (List block × ℤ) block × ℤ) =>
    x.2.2.2.2.2.2.2.2.2 = y.2.2.2.2.2.2.2.2.2 ∧
      (x.1, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.1) =
        (y.2.2.2.1, y.2.2.2.2.1, y.2.2.2.2.2.1, y.2.2.2.2.2.2.2.2.1, y.2.2.2.2.2.2.2.1)
  have hI : ∀ g₁ g₂, I (Lg.get g₁) (Lg.get g₂) ↔ e1Inv IRO2_RO_m g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (Lg.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [Lg, Footprint.lens_pair]
    refine sup_le (by fp_disjoint) (sup_le (by fp_disjoint) (sup_le (by fp_disjoint)
      (sup_le (by fp_disjoint) (sup_le (by fp_disjoint) (sup_le (by fp_disjoint)
        (sup_le (by fp_disjoint) (sup_le (by fp_disjoint) (sup_le (by fp_disjoint)
          (by fp_disjoint)))))))))
  unfold L IdealIndif Indifferentiability.GIdeal
  equiv_proc
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    subst h
    refine ⟨?_, ?_⟩
    · simp only [touched_set_of_le_compl (show (BlockSponge.C.c).footprint ≤ (FVP.fvP D)ᶜ by
          fp_disjoint),
        touched_set_of_le_compl (show (BlockSponge.BIRO.IRO.mp).footprint ≤ (FVP.fvP D)ᶜ by
          fp_disjoint),
        touched_set_of_le_compl (show (IRO2_RO_m).footprint ≤ (FVP.fvP D)ᶜ by fp_disjoint),
        touched_set_of_le_compl (show (Simulator.unvalid_map).footprint ≤ (FVP.fvP D)ᶜ by
          fp_disjoint),
        touched_set_of_le_compl (show (Simulator.paths).footprint ≤ (FVP.fvP D)ᶜ by fp_disjoint),
        touched_set_of_le_compl (show (Simulator.mi).footprint ≤ (FVP.fvP D)ᶜ by fp_disjoint),
        touched_set_of_le_compl (show (Simulator.m).footprint ≤ (FVP.fvP D)ᶜ by fp_disjoint),
        touched_set_of_le_compl hgm, touched_set_of_le_compl hgmi, touched_set_of_le_compl hgpa,
        touched_set_of_le_compl hb2]
    · simp only [Lg, I, Lens.pair]
      simp_reads
      trivial
  · stmt_split{1} 1
    stmt_split{2} 1
    refine prhlStmt_seq_call (prhlProc_abstract_call_moduleF Lg D distExt hD.representable
      (FVP.fvP D) le_rfl hL I ?hc _ _ ?horacle) ?_
    case hc =>
      intro _ n
      cases n with
      | zero => exact inferInstanceAs (Countable (List block × ℤ))
      | succ n => cases n with
        | zero => exact inferInstanceAs (Countable state)
        | succ n => cases n with
          | zero => exact inferInstanceAs (Countable state)
          | succ n => nomatch n
    case horacle =>
      intro _ n
      cases n with
      | zero =>
        simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_zero_cons,
          Module.fst_pair, Module.snd_pair, Indifferentiability.DFUNCTIONALITY.f.mk_simp]
        exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
          (prhlProc_conseq (FC_IRO_e1 IRO2_RO_m) (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
            (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
            (prhlProc_conseq (PC_f_cInv (SimLast_f_Simu IRO2_RO_m))
              (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
              (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
              Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              (prhlProc_conseq (PC_fi_cInv (SimLast_fi_Simu IRO2_RO_m))
                (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
                (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, -, -⟩
    simp_reads
    trivial

theorem equal1 (D : DISTINGUISHER) (hD : Module.ECModule D distExt) (_hDd : DRestrictions D)
    (IRO2_RO_m : Lens (FMap (List block × ℤ) block) VariableAssignment)
    (_hfresh : IRO2_RO_m.footprint ≤ (FVP.fvP D ⊔ DRestrictions.footprint)ᶜ)
    (_D_lossless : D_lossless D) (m : VariableAssignment) :
    Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S) (DRestr D)).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (L D (IRO2.RO.asRO IRO2_RO_m)).procedure () m (fun r _ => r = true) :=
  Procedure.Pr_eq_of_prhlProc (equal1_equiv D hD _hDd IRO2_RO_m _hfresh)
    (fun r₁ _ r₂ _ h => by rw [h]) rfl

theorem equal2 (D : DISTINGUISHER) (hD : Module.ECModule D distExt) (_hDd : DRestrictions D)
    (IRO2_RO_m : Lens (FMap (List block × ℤ) block) VariableAssignment)
    (_hfresh : IRO2_RO_m.footprint ≤ (FVP.fvP D ⊔ DRestrictions.footprint)ᶜ)
    (_D_lossless : D_lossless D) (m : VariableAssignment) :
    Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF Simulator (DRestr D)).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (L D (IRO2.LRO IRO2_RO_m)).procedure () m (fun r _ => r = true) :=
  Procedure.Pr_eq_of_prhlProc (equal2_equiv D hD _hDd IRO2_RO_m _hfresh)
    (fun r₁ _ r₂ _ h => by rw [h]) rfl

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
  intro D_ll m
  rw [Simplify_simulator D hD _hDs D_ll m]
  exact Inefficient_Real_Ideal D hD _hDd D_ll m

end GaudisCrypt.SHA3.Gconcl_list
