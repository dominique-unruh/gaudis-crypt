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
  equiv_proc_to_stmt
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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§bl{1} = §bl{2} ∧ §nb{1} = §nb{2} ∧ §z{1} = §z{2} ∧
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
      equiv_seq_last 1 1 : (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧
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
          equiv_while_raw (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧
              §b{1} = §b{2} ∧ §i{1} = §i{2} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
      §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧ §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
      R §K₁{1} §K₂{2} ∧ §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
          case body =>
            equiv_seq_last 1 1 : (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧
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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§x0{1} = §x0{2} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
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
      equiv_seq_last 5 5 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ sInv K₁ K₂ R §allGlobals{1} §allGlobals{2})
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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.fi.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ sInv K₁ K₂ R §allGlobals{1} §allGlobals{2})
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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ cInv K₁ K₂ R §allGlobals{1} §allGlobals{2})
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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.fi.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ cInv K₁ K₂ R §allGlobals{1} §allGlobals{2})
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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§x0{1} = §x0{2} ∧ sInv K₁ K₂ R §allGlobals{1} §allGlobals{2})
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
  equiv_proc_to_stmt
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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp]
  stmt_inline{1} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ ieInv §allGlobals{1} §allGlobals{2})
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
      equiv_seq_last 1 1 : (§x0{1} = §a{2} ∧ ieInv §allGlobals{1} §allGlobals{2} ∧
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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.fi.mk_simp]
  stmt_inline{1} 0
  simp only [Indifferentiability.DPRIMITIVE.fi.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ ieInv §allGlobals{1} §allGlobals{2})
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
      equiv_seq_last 1 1 : (§x0{1} = §a{2} ∧ ieInv §allGlobals{1} §allGlobals{2} ∧
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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§bl{1} = §bl{2} ∧ §nb{1} = §nb{2} ∧ §z{1} = §z{2} ∧
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
      equiv_seq_last 1 1 : (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧ §i{1} = §i{2} ∧
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
          equiv_seq_last 1 1 : (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧ §i{1} = §i{2} ∧
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
            equiv_seq_last 1 1 : (§bs{1} = §p{1} ∧ §x2{2} = §p{2} ∧ §p{1} = §p{2} ∧ §n{1} = §n{2} ∧
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
          · equiv_while_raw (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧ §i{1} = §i{2} ∧
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
              equiv_seq_last 1 1 : (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §lres{2} ∧ §i{1} = §i{2} ∧
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
                  equiv_seq_last 1 1 : (§bs0{1} = format §p{1} (§i{1} + 1) ∧
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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
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
  equiv_proc_to_stmt
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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 4 1 : (§x0{1} = §x0{2} ∧ §i{1} = 0 ∧ §i{2} = 0 ∧ §p{1} = §p{2} ∧ §n{1} = §n{2} ∧
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
      equiv_while_raw (§x0{1} = §x0{2} ∧ §i{1} = §i{2} ∧ §p{1} = §p{2} ∧ §n{1} = §n{2} ∧
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
      equiv_while_raw (§x0{1} = §x0{2} ∧ §i{1} = §i{2} ∧ §p{1} = §p{2} ∧ §n{1} = §n{2} ∧
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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§x0{1} = §x0{2} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
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
      equiv_seq_last 5 5 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
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
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§x0{1} = §x0{2} ∧ sInv K₁ K₂ R §allGlobals{1} §allGlobals{2})
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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§bl{1} = §bl{2} ∧ §nb{1} = §nb{2} ∧ §z{1} = §z{2} ∧
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
      equiv_seq_last 1 1 : (§p{1} = §(localVarLens "x1" (List block)){2} ∧ §n{1} = §n{2} ∧
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
          equiv_seq_last 1 1 : (§p0{1} = §(localVarLens "x1" (List block)){2} ∧ §n0{1} = §n{2} ∧
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
              equiv_seq_last 1 1 : (§p0{1} = §(localVarLens "x1" (List block)){2} ∧ §n0{1} = §n{2} ∧
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
              · equiv_while_raw (§p0{1} = §(localVarLens "x1" (List block)){2} ∧ §n0{1} = §n{2} ∧
                  §i{1} = §i{2} ∧
                §lres{1} = §bs{2} ∧ valid §p0{1} = true ∧ 0 ≤ §i{1} ∧
                    §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
          §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          INV_L4_ideal
              §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
                case body =>
                  stmt_wp
                  equiv_seq_last 1 1 : (§x4{1} = format §p0{1} §i{1} ∧
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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§p{1} = §q{2} ∧ §n{1} = §k{2} ∧ §pp{1} = §p{1} ∧ §nn{1} = §n{1} ∧
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
      equiv_seq_last 1 1 : (§p{1} = §(localVarLens "x1" (List block)){2} ∧ §n{1} = §n{2} ∧
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
          equiv_while_raw (§p{1} = §(localVarLens "x1" (List block)){2} ∧ §n{1} = §n{2} ∧
              §i{1} = §i{2} ∧
              §lres{1} = §bs{2} ∧ valid §p{1} = true ∧ 0 ≤ §i{1} ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧
                  §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
          §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          INV_L4_ideal
              §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
          case body =>
            stmt_wp
            equiv_seq_last 1 1 : (§x2{1} = format §p{1} §i{1} ∧
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
      equiv_seq_last 1 1 : (§pp{1} = §x3{2} ∧ §n{1} = §n1{2} ∧ §i{1} = §i0{2} ∧
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
          equiv_while_raw (§pp{1} = §x3{2} ∧ §n{1} = §n1{2} ∧ §i{1} = §i0{2} ∧
              §lres{1} = §bs0{2} ∧ valid §pp{1} = false ∧ 0 ≤ §i{1} ∧
              parse (format §pp{1} §n{1}) = (§pp{1},
                  §n{1}) ∧ §Gconcl.S.m{1} = §Gconcl.S.m{2} ∧ §Gconcl.S.mi{1} = §Gconcl.S.mi{2} ∧
          §Gconcl.S.paths{1} = §Gconcl.S.paths{2} ∧
          INV_L4_ideal
              §SLCommon.F.RO.m{1} §BlockSponge.BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ∧
          §BlockSponge.C.c{1} = §BlockSponge.C.c{2})
          case body =>
            stmt_wp
            equiv_seq_last 1 1 : (§x5{1} = format §pp{1} §i{1} ∧ §x4{2} = §x3{2} ∧ §n2{2} + 1 = §i{1} ∧
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
  equiv_proc_to_stmt
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
  equiv_proc_to_stmt
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
  equiv_proc_to_stmt
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
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
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

/-- `equiv_L3_L4`'s invariant (EC: `={glob S, glob C, glob F.RO, glob F2.RO}`). -/
abbrev L34Inv := sInv (Lens.pair SLCommon.F.RO.m F2.RO.m) (Lens.pair SLCommon.F.RO.m F2.RO.m) Eq

/-- `IF2(F.RO, F2.RO).f ~ Last(DSqueeze2(F.RO, F2.RO)).f` (EC: `equiv_L3_L4`'s simulator `call`):
the sampling loop of `IF2` against `DSqueeze2`'s `get` loop, in lockstep; `IF2`'s final `get` finds
its entry. -/
theorem IF2_Last :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L34Inv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block) block
        (Module.app IF2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO))).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app Last (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
          (Module.app DSqueeze2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO))))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L34Inv g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.FUNCTIONALITY.view_f]
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§(localVarLens "x0" (List block)){1} = format §p0{2} §n{2} ∧ §p{1} = §p0{2} ∧
      §n{1} = §n{2} ∧ §pp{2} = §p0{2} ∧ §nn{2} = §n{2} ∧ 0 < §n{1} ∧ §i{1} = 0 ∧ §i{2} = 0 ∧
      §lres{2} = [] ∧ L34Inv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, h⟩
    rw [formatK]
    exact ⟨rfl, rfl, rfl, rfl, rfl, parse_gt0 x, h⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ x0 p n i p0 n' pp nn i' lres ⟨-, rfl, -⟩
    rfl
  case «then» =>
    simp only [PROM.FullRO.RO.asRO, PROM.FullRO.RO_T.get.mk_simp,
      PROM.FullRO.RO_T.sample.mk_simp]
    equiv_seq_last 1 0 : (§i{1} = §n{1} ∧ §x0{1} = format §p{1} §n{1} ∧ 0 < §n{1} ∧
        last b0 §lres{2} = oget (FMap.get §SLCommon.F.RO.m{1} §x0{1}) ∧
        FMap.dom §SLCommon.F.RO.m{1} §x0{1} ∧ L34Inv §allGlobals{1} §allGlobals{2})
    · equiv_seq_last 1 1 : (§i{1} = §i{2} ∧ §p{1} = §p0{2} ∧ §n{1} = §n{2} ∧ 0 ≤ §i{1} ∧ §i{1} ≤ §n{1} ∧
          0 < §n{1} ∧ §x0{1} = format §p0{2} §n{2} ∧
          (0 < §i{1} → last b0 §lres{2} = oget (FMap.get §SLCommon.F.RO.m{1} (format §p{1} §i{1})) ∧
            FMap.dom §SLCommon.F.RO.m{1} (format §p{1} §i{1})) ∧
          L34Inv §allGlobals{1} §allGlobals{2})
      · equiv_if{2}
        case «then» =>
          refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
          obtain ⟨⟨⟨-, -, hn, -, -, hn0, -⟩, -⟩, hg⟩ := h
          simp only [decide_eq_true_eq] at hg
          omega
        case «else» =>
          equiv_skip
          rintro g₁ g₂ x0 p n i p0 n' pp nn i' lres
            ⟨⟨⟨rfl, rfl, rfl, -, -, hn0, rfl, rfl, rfl, h⟩, -⟩, -⟩
          exact ⟨rfl, rfl, rfl, le_rfl, hn0.le, hn0, rfl, fun h => absurd h (lt_irrefl _), h⟩
      equiv_while_raw (§i{1} = §i{2} ∧ §p{1} = §p0{2} ∧ §n{1} = §n{2} ∧ 0 ≤ §i{1} ∧ §i{1} ≤ §n{1} ∧
          0 < §n{1} ∧ §x0{1} = format §p0{2} §n{2} ∧
          (0 < §i{1} → last b0 §lres{2} = oget (FMap.get §SLCommon.F.RO.m{1} (format §p{1} §i{1})) ∧
            FMap.dom §SLCommon.F.RO.m{1} (format §p{1} §i{1})) ∧
          L34Inv §allGlobals{1} §allGlobals{2})
      case guard =>
        rintro g₁ g₂ i p n x0 i' p0 n' lres ⟨rfl, -, rfl, -⟩
        rfl
      case exit =>
        rintro g₁ g₂ i p n x0 i' p0 n' lres ⟨rfl, rfl, rfl, hi0, hin, hn0, rfl, hl, h⟩ hg
        simp only [decide_eq_false_iff_not, not_lt] at hg
        obtain rfl : i = n := le_antisymm hin hg
        obtain ⟨hl1, hd⟩ := hl hn0
        exact ⟨rfl, rfl, hn0, hl1, hd, h⟩
      case body =>
        stmt_wp
        stmt_inline{1} 0
        stmt_inline{1} 0
        stmt_inline{2} 0
        stmt_wp
        equiv_rnd
        stmt_wp
        equiv_skip
        rintro g₁ g₂ i p n x0 i' p0 n' lres
          ⟨⟨rfl, rfl, rfl, hi0, hin, hn0, rfl, hl, ⟨hsm, hsmi, hsp, hR, hc⟩⟩, hg⟩
        have hm : SLCommon.F.RO.m.get g₁ = SLCommon.F.RO.m.get g₂ := by
          simpa [Lens.pair] using congrArg Prod.fst hR
        have hm2 : F2.RO.m.get g₁ = F2.RO.m.get g₂ := by
          simpa [Lens.pair] using congrArg Prod.snd hR
        intro a _
        simp only [decide_eq_true_eq] at hg
        rw [← hm]
        by_cases hd : FMap.dom (SLCommon.F.RO.m.get g₁) (format p (i + 1))
        all_goals simp only [hd, decide_true, decide_false, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, if_true, if_false]
        · refine ⟨trivial, trivial, trivial, by omega, by omega, hn0, trivial,
            fun _ => ⟨by simp [last, rcons], trivial⟩, hsm, hsmi, hsp, hR, hc⟩
        · refine ⟨trivial, trivial, trivial, by omega, by omega, hn0, trivial,
            fun _ => ⟨by simp [last, rcons], ?_⟩, ?_⟩
          · simp [FMap.domE]
          · simp only [L34Inv, sInv, Lens.pair] at hR ⊢
            simp_reads
            exact ⟨hsm, hsmi, hsp, by rw [hm, hm2], hc⟩
      case hpre =>
        equiv_skip
        intros
        assumption
    stmt_inline{1} 0
    stmt_wp
    stmt_wp{1} 1
    stmt_wp
    equiv_skip
    rintro g₁ g₂ i n x0 p lres ⟨rfl, rfl, hn0, hl, hd, h⟩
    refine ⟨bdistr_expected_one, fun a _ => ?_⟩
    simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
    exact ⟨hl.symm, h⟩
  case «else» =>
    simp only [PROM.FullRO.RO.asRO, PROM.FullRO.RO_T.get.mk_simp,
      PROM.FullRO.RO_T.sample.mk_simp]
    equiv_seq_last 1 0 : (§i{1} = §n{1} ∧ §x0{1} = format §p{1} §n{1} ∧ 0 < §n{1} ∧
        last b0 §lres{2} = oget (FMap.get §F2.RO.m{1} §x0{1}) ∧
        FMap.dom §F2.RO.m{1} §x0{1} ∧ L34Inv §allGlobals{1} §allGlobals{2})
    · equiv_seq_last 1 1 : (§i{1} = §i{2} ∧ §p{1} = §pp{2} ∧ §n{1} = §n{2} ∧ 0 ≤ §i{1} ∧ §i{1} ≤ §n{1} ∧
          0 < §n{1} ∧ §x0{1} = format §pp{2} §n{2} ∧
          (0 < §i{1} → last b0 §lres{2} = oget (FMap.get §F2.RO.m{1} (format §p{1} §i{1})) ∧
            FMap.dom §F2.RO.m{1} (format §p{1} §i{1})) ∧ L34Inv §allGlobals{1} §allGlobals{2})
      · equiv_rcondf{2}
        equiv_if{2}
        case «then» =>
          refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
          obtain ⟨⟨⟨-, -, hn, -, hnn, hn0, -⟩, -⟩, hg⟩ := h
          simp only [decide_eq_true_eq] at hg
          omega
        case «else» =>
          equiv_skip
          rintro g₁ g₂ x0 p n i p0 n' pp nn i' lres
            ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, hn0, rfl, rfl, rfl, h⟩, -⟩, -⟩
          exact ⟨by simp, rfl, rfl, rfl, le_rfl, hn0.le, hn0, rfl,
            fun h => absurd h (lt_irrefl _), h⟩
      equiv_while_raw (§i{1} = §i{2} ∧ §p{1} = §pp{2} ∧ §n{1} = §n{2} ∧ 0 ≤ §i{1} ∧ §i{1} ≤ §n{1} ∧
          0 < §n{1} ∧ §x0{1} = format §pp{2} §n{2} ∧
          (0 < §i{1} → last b0 §lres{2} = oget (FMap.get §F2.RO.m{1} (format §p{1} §i{1})) ∧
            FMap.dom §F2.RO.m{1} (format §p{1} §i{1})) ∧ L34Inv §allGlobals{1} §allGlobals{2})
      case guard =>
        rintro g₁ g₂ i p n x0 i' pp n' lres ⟨rfl, -, rfl, -⟩
        rfl
      case exit =>
        rintro g₁ g₂ i p n x0 i' pp n' lres ⟨rfl, rfl, rfl, hi0, hin, hn0, rfl, hl, h⟩ hg
        simp only [decide_eq_false_iff_not, not_lt] at hg
        obtain rfl : i = n := le_antisymm hin hg
        obtain ⟨hl1, hd⟩ := hl hn0
        exact ⟨rfl, rfl, hn0, hl1, hd, h⟩
      case body =>
        stmt_wp
        stmt_inline{1} 0
        stmt_inline{1} 0
        stmt_inline{2} 0
        stmt_wp
        equiv_rnd
        stmt_wp
        equiv_skip
        rintro g₁ g₂ i p n x0 i' pp n' lres
          ⟨⟨rfl, rfl, rfl, hi0, hin, hn0, rfl, hl, ⟨hsm, hsmi, hsp, hR, hc⟩⟩, hg⟩
        have hm : F2.RO.m.get g₁ = F2.RO.m.get g₂ := by
          simpa [Lens.pair] using congrArg Prod.snd hR
        have hm1 : SLCommon.F.RO.m.get g₁ = SLCommon.F.RO.m.get g₂ := by
          simpa [Lens.pair] using congrArg Prod.fst hR
        intro a _
        simp only [decide_eq_true_eq] at hg
        rw [← hm]
        by_cases hd : FMap.dom (F2.RO.m.get g₁) (format p (i + 1))
        all_goals simp only [hd, decide_true, decide_false, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, if_true, if_false]
        · refine ⟨trivial, trivial, trivial, by omega, by omega, hn0, trivial,
            fun _ => ⟨by simp [last, rcons], trivial⟩, hsm, hsmi, hsp, hR, hc⟩
        · refine ⟨trivial, trivial, trivial, by omega, by omega, hn0, trivial,
            fun _ => ⟨by simp [last, rcons], ?_⟩, ?_⟩
          · simp [FMap.domE]
          · simp only [L34Inv, sInv, Lens.pair] at hR ⊢
            simp_reads
            exact ⟨hsm, hsmi, hsp, by rw [hm, hm1], hc⟩
      case hpre =>
        equiv_skip
        intros
        assumption
    stmt_inline{1} 0
    stmt_wp
    stmt_wp{1} 1
    stmt_wp
    equiv_skip
    rintro g₁ g₂ i n x0 p lres ⟨rfl, rfl, hn0, hl, hd, h⟩
    refine ⟨bdistr_expected_one, fun a _ => ?_⟩
    simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
    exact ⟨hl.symm, h⟩


/-- `IF2_Last`, with `IF2` seen as a `DFUNCTIONALITY`. -/
theorem IF2_Last_view :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L34Inv g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Indifferentiability.FUNCTIONALITY.view state (List block) block
          (Module.app IF2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO)))).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Module.app Last (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
          (Module.app DSqueeze2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO))))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L34Inv g₁ g₂) := by
  rw [Indifferentiability.FUNCTIONALITY.view_f]
  exact IF2_Last

/-- `S(IF2).f ~ S2(DSqueeze2).f` under `L34Inv` (`S_f_sInvD` with `IF2_Last`). -/
theorem S_IF2_S2_f :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L34Inv g₁ g₂)
      (Indifferentiability.PRIMITIVE.f state (List block) block
        (Module.app Gconcl.S (Indifferentiability.FUNCTIONALITY.view state (List block) block
          (Module.app IF2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO))))).procedure
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app S2 (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
          (Module.app DSqueeze2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO))))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L34Inv g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{2} 0
  stmt_wp
  equiv_call (S_f_sInvD IF2_Last_view)
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x _ ⟨rfl, h⟩
  exact ⟨⟨rfl, h⟩, fun _ _ _ _ h => h⟩

/-- `S(IF2).f ~ S2(DSqueeze2).f` under `L34Inv` (`S_f_sInvD` with `IF2_Last`). -/
theorem S_IF2_S2_fi :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L34Inv g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi state (List block) block
        (Module.app Gconcl.S (Indifferentiability.FUNCTIONALITY.view state (List block) block
          (Module.app IF2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO))))).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app S2 (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
          (Module.app DSqueeze2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO))))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L34Inv g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{2} 0
  stmt_wp
  equiv_call (S_fi_sInvD (K₁ := Lens.pair SLCommon.F.RO.m F2.RO.m)
    (K₂ := Lens.pair SLCommon.F.RO.m F2.RO.m) (R := Eq))
  stmt_wp
  equiv_skip
  rintro g₁ g₂ x _ ⟨rfl, h⟩
  exact ⟨⟨rfl, h⟩, fun _ _ _ _ h => h⟩

/-- `IF2.f(format bl k) ~ F.RO.get(format bl k)` when the shorter prefixes `format bl j`, `j < k`,
are known (EC: `equiv_L3_L4`'s `splitwhile{1} 1 : i1 + 1 < n1`): `IF2`'s samples of known entries
are dropped, its last one is coupled with `get`, and its final `get` finds the entry. -/
theorem IF2_get (bl : List block) (k : ℤ) :
    prhlProc (sig₁ := procsig (List block) -> block) (sig₂ := procsig (List block) -> block)
      (fun a₁ g₁ a₂ g₂ => a₁ = format bl k ∧ a₂ = format bl k ∧ valid bl = true ∧ 0 < k ∧
        (∀ j, 1 ≤ j → j < k → FMap.dom (SLCommon.F.RO.m.get g₁) (format bl j)) ∧ L34Inv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block) block
        (Module.app IF2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO))).procedure
      (PROM.FullRO.RO_T.get (List block) block SLCommon.F.RO.asRO).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L34Inv g₁ g₂ ∧
        ∀ j, 1 ≤ j → j ≤ k → FMap.dom (SLCommon.F.RO.m.get g₁) (format bl j)) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  simp only [PROM.FullRO.RO.asRO, PROM.FullRO.RO_T.get.mk_simp, PROM.FullRO.RO_T.sample.mk_simp]
  stmt_inline{2} 0
  repeat stmt_inline{1} 0
  equiv_seq_last 2 3 : (§x0{1} = format bl k ∧ §p{1} = bl ∧ §n{1} = k ∧ §i{1} = 0 ∧
      §x0{2} = format bl k ∧ valid bl = true ∧ 0 < k ∧
      (∀ j, 1 ≤ j → j < k → FMap.dom §SLCommon.F.RO.m{1} (format bl j)) ∧
      L34Inv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x₁ x₂ ⟨rfl, rfl, hv, hk, hpre, h⟩
    rw [parseK bl k hk (by simpa [valid] using hv)]
    exact ⟨rfl, rfl, rfl, rfl, hv, hk, hpre, h⟩
  equiv_seq_last 1 1 : (§(localVarLens "b" block){1} = oget (FMap.get §SLCommon.F.RO.m{2} §x0{2}) ∧
      L34Inv §allGlobals{1} §allGlobals{2} ∧
      ∀ j, 1 ≤ j → j ≤ k → FMap.dom §SLCommon.F.RO.m{1} (format bl j))
  rotate_left
  · stmt_wp
    equiv_skip
    exact fun _ _ _ _ h => h
  equiv_if{1}
  case «else» =>
    refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
    obtain ⟨⟨-, hp, -, -, -, hv, -⟩, hg⟩ := h
    rw [hp, hv] at hg
    exact Bool.noConfusion hg
  case «then» =>
    equiv_seq_last 5 0 : (0 < k ∧ §x0{1} = format bl k ∧ §x0{2} = format bl k ∧
        (∀ j, 1 ≤ j → j ≤ k → FMap.dom §SLCommon.F.RO.m{1} (format bl j)) ∧
        L34Inv §allGlobals{1} §allGlobals{2})
    rotate_left
    · stmt_wp
      stmt_wp{1} 1
      stmt_wp
      equiv_skip
      rintro g₁ g₂ x0 x0' ⟨hk, rfl, rfl, hall, h⟩
      have hd := hall k (by omega) le_rfl
      have hm : SLCommon.F.RO.m.get g₁ = SLCommon.F.RO.m.get g₂ := by
        simpa [Lens.pair] using congrArg Prod.fst h.2.2.2.1
      refine ⟨bdistr_expected_one, fun a _ => ?_⟩
      simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
      exact ⟨by rw [hm], h, hall⟩
    refine prhlStmt_splitwhile_left
      ⟨fun σ => decide ((localVarLens "i" ℤ).get σ + 1 < (localVarLens "n" ℤ).get σ)⟩
      (fun σ => ((localVarLens "n" ℤ).get σ - (localVarLens "i" ℤ).get σ).toNat) ?_ ?_
    · intro k'
      simp only [Getter.andB_get, Bool.and_eq_true]
      hoare_wp 7
      hoare_skip
      rintro i n p m ⟨⟨h1, h2⟩, rfl⟩ a _
      simp only [ite_self]
      simp only [decide_eq_true_eq] at h2
      omega
    unfold Getter.andB
    equiv_seq_last 1 2 : (0 < k ∧ §p{1} = bl ∧ §n{1} = k ∧ §i{1} = k - 1 ∧ §x0{1} = format bl k ∧
        §x0{2} = format bl k ∧ (∀ j, 1 ≤ j → j < k → FMap.dom §SLCommon.F.RO.m{1} (format bl j)) ∧
        L34Inv §allGlobals{1} §allGlobals{2})
    · equiv_while{1} (§p{1} = bl ∧ §n{1} = k ∧ 0 ≤ §i{1} ∧ §i{1} ≤ k - 1 ∧
          §x0{1} = format bl k ∧ §x0{2} = format bl k ∧
          (∀ j, 1 ≤ j → j < k → FMap.dom §SLCommon.F.RO.m{1} (format bl j)) ∧
          L34Inv §allGlobals{1} §allGlobals{2}) ((§n{1} - §i{1}).toNat)
      case lossless =>
        intro σ₂ σ _ _
        simp [Stmt.ewp_seq, Stmt.ewp_assign, Stmt.ewp_sample, Stmt.ewp_ifThenElse]
        simp only [Stmt.ewp_skip, ite_self]
        exact bdistr_expected_one
      case «variant» =>
        intro σ₂ k'
        hoare_wp 7
        refine hoare_skip_of_imp (fun σ h => ?_)
        simp only [eval_lens_full, eval_lens_global] at h
        obtain ⟨⟨hp, hn, hi0, hik, hx, hx', hpre, hI⟩, hg, hk⟩ := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
        have hi0' : 0 ≤ (localVarLens "i" ℤ).get σ := by simpa using hi0
        have hik' : (localVarLens "i" ℤ).get σ ≤ k - 1 := by simpa using hik
        have hn' : (localVarLens "n" ℤ).get σ = k := by simpa using hn
        have hk' : ((localVarLens "n" ℤ).get σ - (localVarLens "i" ℤ).get σ).toNat = k' := by
          simpa using hk
        have hg' : (localVarLens "i" ℤ).get σ + 1 < (localVarLens "n" ℤ).get σ := by
          simpa using hg.2
        intro a _
        have hd : FMap.dom (SLCommon.F.RO.m.get σ.globals)
            (format ((localVarLens "p" (List block)).get σ) ((localVarLens "i" ℤ).get σ + 1)) := by
          rw [hp]; exact hpre _ (by omega) (by omega)
        simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
        exact ⟨⟨hp, hn, by omega, by omega, hx, hx', hpre, hI⟩, by omega⟩
      case exit =>
        rintro g₁ g₂ x0' p n i x0 ⟨rfl, rfl, hi0, hik, rfl, rfl, hpre, h⟩ hg
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hg
        exact ⟨by omega, rfl, rfl, by omega, rfl, rfl, hpre, h⟩
      equiv_skip
      rintro g₁ g₂ x0 p n i x0' ⟨⟨rfl, rfl, rfl, rfl, rfl, hv, hk, hpre, h⟩, -⟩
      exact ⟨rfl, rfl, le_rfl, by omega, rfl, rfl, hpre, h⟩
    refine prhlStmt_unroll_left ?_
    equiv_if{1}
    case «else» =>
      refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
      obtain ⟨⟨-, -, hn, hi, -⟩, hg⟩ := h
      simp only [decide_eq_false_iff_not, not_lt] at hg
      omega
    case «then» =>
      equiv_rcondf{1}
      stmt_wp
      equiv_rnd
      stmt_wp
      equiv_skip
      rintro g₁ g₂ p n i x0 x0' ⟨⟨hk, hp, hn, hi, hx, hx', hpre, h⟩, -⟩ a _
      subst p n i x0 x0'
      have hm : SLCommon.F.RO.m.get g₁ = SLCommon.F.RO.m.get g₂ := by
        simpa [Lens.pair] using congrArg Prod.fst h.2.2.2.1
      have hm2 : F2.RO.m.get g₁ = F2.RO.m.get g₂ := by
        simpa [Lens.pair] using congrArg Prod.snd h.2.2.2.1
      rw [show k - 1 + 1 = k by ring, ← hm]
      by_cases hd : FMap.dom (SLCommon.F.RO.m.get g₁) (format bl k)
      all_goals simp only [hd, decide_true, decide_false, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, if_true, if_false, ite_self, lt_irrefl, decide_false]
      · exact ⟨trivial, hk, trivial, trivial, fun j h1 h2 => by
          rcases (show j < k ∨ j = k by omega) with hj | rfl
          · exact hpre j h1 hj
          · exact hd, h⟩
      · refine ⟨trivial, hk, trivial, trivial, fun j h1 h2 => ?_, ?_⟩
        · rw [FMap.mem_set]
          rcases (show j < k ∨ j = k by omega) with hj | rfl
          · exact Or.inl (hpre j h1 hj)
          · exact Or.inr rfl
        simp only [L34Inv, sInv, Lens.pair] at h ⊢
        simp_reads
        exact ⟨h.1, h.2.1, h.2.2.1, by rw [hm, hm2], h.2.2.2.2⟩

omit [BlockSponge.Params] [Params] in
/-- `F.RO.get` as `RO`'s procedure. -/
theorem F_RO_get_eq : PROM.FullRO.RO_T.get (List block) block SLCommon.F.RO.asRO =
    PROM.FullRO.RO.get (List block) block SLCommon.F.dout SLCommon.F.RO.m := by
  simp [PROM.FullRO.RO.asRO, PROM.FullRO.RO_T.get.mk_simp, PROM.FullRO.RO,
    PROM.FullRO.ROmap.get.mk_simp]

omit [BlockSponge.Params] [Params] in
/-- `F.RO.sample` as `RO`'s procedure. -/
theorem F_RO_sample_eq : PROM.FullRO.RO_T.sample (List block) block SLCommon.F.RO.asRO =
    PROM.FullRO.ROmap.sample (List block) block
      (PROM.FullRO.RO (List block) block SLCommon.F.dout SLCommon.F.RO.m) := by
  simp [PROM.FullRO.RO.asRO, PROM.FullRO.RO_T.sample.mk_simp]

/-- `IF2.f(format bl 1) ~ F.RO.sample(format bl 1)` (`IF2_get`, the result discarded). -/
theorem IF2_sample (bl : List block) :
    prhlProc (sig₁ := procsig (List block) -> block) (sig₂ := procsig (List block) -> Unit)
      (fun a₁ g₁ a₂ g₂ => a₁ = format bl 1 ∧ a₂ = format bl 1 ∧ valid bl = true ∧
        L34Inv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block) block
        (Module.app IF2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO))).procedure
      (PROM.FullRO.RO_T.sample (List block) block SLCommon.F.RO.asRO).procedure
      (fun _ g₁ _ g₂ => L34Inv g₁ g₂) := by
  rw [F_RO_sample_eq]
  equiv_proc_to_stmt
  stmt_inline{2} 0
  simp only [← F_RO_get_eq]
  stmt_wp
  equiv_call (IF2_get bl 1)
  stmt_wp
  equiv_skip
  rintro σ₂ g₁ x ⟨rfl, hx, hv, h⟩
  refine ⟨⟨rfl, hx, hv, fun j h1 h2 => absurd h2 (by omega), h⟩, fun r₁ g₁ r₂ g₂ ⟨_, h', _⟩ => ?_⟩
  simp only [Setter.throwaway]
  simp_reads
  exact h'

/-- `DSqueeze(IF2).f ~ FValid(DSqueeze2).f` (EC: `equiv_L3_L4`'s functionality `call`). For `n > 0`:
the first `get` of `DSqueeze2` is unrolled against `IF2.f(p)`, `DSqueeze`'s loop is split before its
last round (EC's `splitwhile{1} 8 : i + 1 < n`), and each call is `IF2_get`. -/
theorem DS_IF2_FValid :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L34Inv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app DSqueeze (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
          { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
              (Module.app IF2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO)) }))).procedure
      (Indifferentiability.DFUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FValid
          (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app DSqueeze2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO)) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L34Inv g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DFUNCTIONALITY.f.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§p{1} = §p{2} ∧ §n{1} = §n{2} ∧ §lres{1} = [] ∧
      §(localVarLens "r" (List block)){2} = [] ∧
      §(localVarLens "b" block){1} = b0 ∧ §i{1} = 0 ∧ L34Inv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, h⟩
    exact ⟨rfl, rfl, h⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ p n lres b i p' n' r ⟨rfl, -⟩
    rfl
  case «else» =>
    equiv_skip
    rintro g₁ g₂ p n lres b i p' n' r ⟨⟨-, -, rfl, rfl, -, -, h⟩, -⟩
    exact ⟨rfl, h⟩
  case «then» =>
    stmt_inline{2} 0
    stmt_wp
    equiv_seq_last 2 1 : (§p{1} = §p0{2} ∧ §n{1} = §n0{2} ∧ §lres{1} = [] ∧ §lres0{2} = [] ∧
        §i{1} = 0 ∧ §i0{2} = 0 ∧ valid §p{1} = true ∧ L34Inv §allGlobals{1} §allGlobals{2})
    · stmt_wp
      equiv_skip
      rintro g₁ g₂ p n lres b i p' n' r ⟨⟨rfl, rfl, rfl, -, -, rfl, h⟩, hv⟩
      exact ⟨rfl, rfl, rfl, rfl, hv, h⟩
    equiv_if{2}
    case «else» =>
      refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
      obtain ⟨⟨hp, -, -, -, -, -, hv, -⟩, hg⟩ := h
      rw [← hp, hv] at hg
      exact Bool.noConfusion hg
    case «then» =>
      equiv_case (§n{1} ≤ 0)
      case hp =>
        equiv_rcondf{1}
        equiv_rcondf{2}
        equiv_if{2}
        case «else» =>
          refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
          obtain ⟨⟨⟨⟨-, hn, -⟩, -⟩, hle⟩, hg⟩ := h
          simp only [decide_eq_false_iff_not, not_le] at hg
          omega
        case «then» =>
          refine prhlStmt_fix_left (fun σ => (localVarLens "p" (List block)).get σ) (fun q => ?_)
          equiv_call (IF2_sample q)
          equiv_skip
          rintro σ₂ g₁ p n lres i ⟨⟨⟨⟨⟨hp, hn, hl, hl0, hi, hi0, hv, h⟩, -⟩, hle⟩, -⟩, hq⟩
          subst hq
          refine ⟨⟨by rw [format_one], by rw [format_one, ← hp], hv, h⟩,
            fun r₁ g₁' r₂ g₂' h' => ?_⟩
          simp only [Setter.throwaway]
          simp_reads
          refine ⟨?_, ?_, by rw [hl, hl0], h'⟩
          · simp only [decide_eq_false_iff_not, not_lt]
            rw [hi0, ← hn]
            exact hle
          · simp only [decide_eq_false_iff_not, not_lt]
            omega
      case hn =>
        equiv_seq_last 2 1 : (§p{1} = §p0{2} ∧ §n{1} = §n0{2} ∧ §lres{1} = [] ∧ §lres0{2} = [] ∧
            §i{1} = 0 ∧ §i0{2} = 0 ∧ valid §p{1} = true ∧ 0 < §n{1} ∧
            L34Inv §allGlobals{1} §allGlobals{2})
        · equiv_if{2}
          case «then» =>
            refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
            obtain ⟨⟨⟨⟨-, hn, -⟩, -⟩, hle⟩, hg⟩ := h
            simp only [decide_eq_true_eq] at hg
            omega
          case «else» =>
            equiv_skip
            rintro g₁ g₂ p n lres i p0 n0 lres0 i0
              ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, hv, h⟩, -⟩, hle⟩, -⟩
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hv, by omega, h⟩
        refine prhlStmt_unroll_right ?_
        equiv_if{2}
        case «else» =>
          refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
          obtain ⟨⟨-, hn, -, -, -, hi0, -, hpos, -⟩, hg⟩ := h
          simp only [decide_eq_false_iff_not, not_lt] at hg
          omega
        case «then» =>
          equiv_seq_last 1 1 : (§p{1} = §p0{2} ∧ §n{1} = §n0{2} ∧ §i0{2} = §i{1} + 1 ∧ 0 ≤ §i{1} ∧
              §i0{2} ≤ §n{1} ∧ rcons §lres{1} §(localVarLens "b" block){1} = §lres0{2} ∧
              valid §p{1} = true ∧ 0 < §n{1} ∧
              (∀ j, 1 ≤ j → j ≤ §i0{2} → FMap.dom §SLCommon.F.RO.m{1} (format §p{1} j)) ∧
              L34Inv §allGlobals{1} §allGlobals{2})
          · stmt_wp
            refine prhlStmt_fix_left (fun σ => (localVarLens "p" (List block)).get σ) (fun q => ?_)
            equiv_call (IF2_get q 1)
            stmt_wp
            equiv_skip
            rintro g₁ g₂ p n lres i p0 n0 lres0 i0
              ⟨⟨⟨hp, hn, hl, hl0, hi, hi0, hv, hpos, h⟩, hg⟩, hq⟩
            subst hq hl hl0 hi hi0
            refine ⟨⟨by rw [format_one], by rw [hp, zero_add, format_one], hv,
              fun j h1 h2 => absurd h2 (by omega), h⟩,
              fun r₁ g₁ r₂ g₂ ⟨hr, h', hd⟩ => ⟨hp, hn, rfl, le_rfl, by omega, by rw [hr], hv, hpos,
                (fun j h1 h2 => hd j h1 (by omega)), h'⟩⟩
          refine prhlStmt_splitwhile_left
            ⟨fun σ => decide ((localVarLens "i" ℤ).get σ + 1 < (localVarLens "n" ℤ).get σ)⟩
            (fun σ => ((localVarLens "n" ℤ).get σ - (localVarLens "i" ℤ).get σ).toNat) ?_ ?_
          · intro k'
            simp only [Getter.andB_get, Bool.and_eq_true]
            hoare_split 1
            refine hoare_seq (hoare_if_wp (hoare_call_wp _ _ _ (hoareProc_true _) _)
              (hoare_skip_wp _)) ?_
            hoare_wp 2
            refine hoare_skip_of_imp (fun σ h => ?_)
            obtain ⟨⟨-, h2⟩, hk⟩ := h
            have h2' : (localVarLens "i" ℤ).get σ + 1 < (localVarLens "n" ℤ).get σ := by
              simpa using h2
            have hk' : ((localVarLens "n" ℤ).get σ - (localVarLens "i" ℤ).get σ).toNat = k' := by
              simpa using hk
            refine ⟨fun _ _ _ => ?_, fun _ => ?_⟩
            all_goals
              show ((localVarLens "n" ℤ).get σ - ((localVarLens "i" ℤ).get σ + 1)).toNat < k'
              omega
          unfold Getter.andB
          equiv_seq_last 1 0 : (§p{1} = §p0{2} ∧ §n{1} = §n0{2} ∧ §i{1} + 1 = §n{1} ∧
              rcons §lres{1} §(localVarLens "b" block){1} = §lres0{2} ∧
              L34Inv §allGlobals{1} §allGlobals{2})
          · equiv_while_raw (§p{1} = §p0{2} ∧ §n{1} = §n0{2} ∧ §i0{2} = §i{1} + 1 ∧ 0 ≤ §i{1} ∧
              §i0{2} ≤ §n{1} ∧ rcons §lres{1} §(localVarLens "b" block){1} = §lres0{2} ∧
              valid §p{1} = true ∧ 0 < §n{1} ∧
              (∀ j, 1 ≤ j → j ≤ §i0{2} → FMap.dom §SLCommon.F.RO.m{1} (format §p{1} j)) ∧
              L34Inv §allGlobals{1} §allGlobals{2})
            case guard =>
              rintro g₁ g₂ p n i lres b p0 n0 i0 lres0 ⟨-, hn, hi, -, hle, -⟩
              rw [← hn, hi]
              by_cases h : i + 1 < n
              · simp only [h, decide_true, Bool.and_true, decide_eq_true_eq]
                omega
              · simp only [h, decide_false, Bool.and_false]
            case exit =>
              rintro g₁ g₂ p n i lres b p0 n0 i0 lres0 ⟨hp, hn, hi, hi0', hle, hl, -, -, -, h⟩ hg
              simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hg
              exact ⟨hp, hn, by omega, hl, h⟩
            case body =>
              stmt_wp
              equiv_seq_last 1 1 : (§p{1} = §p0{2} ∧ §n{1} = §n0{2} ∧ §i0{2} = §i{1} + 1 ∧ 0 < §i{1} ∧
                  §i{1} < §n{1} ∧ §lres{1} = §lres0{2} ∧ valid §p{1} = true ∧ 0 < §n{1} ∧
                  (∀ j, 1 ≤ j → j ≤ §i{1} → FMap.dom §SLCommon.F.RO.m{1} (format §p{1} j)) ∧
                  L34Inv §allGlobals{1} §allGlobals{2})
              · stmt_wp
                equiv_skip
                rintro g₁ g₂ p n i lres b p0 n0 i0 lres0
                  ⟨⟨hp, hn, hi, hi0', hle, hl, hv, hpos, hdom, h⟩, hg⟩
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
                exact ⟨hp, hn, by omega, by omega, hg.2, hl, hv, hpos,
                  fun j h1 h2 => hdom j h1 (by omega), h⟩
              equiv_if{1}
              case «else» =>
                refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
                obtain ⟨⟨-, -, -, -, hlt, -⟩, hg⟩ := h
                simp only [decide_eq_false_iff_not, not_lt] at hg
                omega
              case «then» =>
                refine prhlStmt_fix_left (fun σ => ((localVarLens "p" (List block)).get σ,
                  (localVarLens "i" ℤ).get σ)) (fun q => ?_)
                equiv_call (IF2_get q.1 (q.2 + 1))
                equiv_skip
                rintro g₁ g₂ p n i lres p0 n0 i0 lres0
                  ⟨⟨⟨hp, hn, hi, hi0, hlt, hl, hv, hpos, hdom, h⟩, -⟩, hq⟩
                subst hq hp hi
                refine ⟨⟨rfl, rfl, hv, by omega, fun j h1 h2 => hdom j h1 (by omega), h⟩,
                  fun r₁ g₁ r₂ g₂ ⟨hr, h', hd⟩ => ⟨rfl, hn, rfl, by omega, by omega,
                    by rw [hl, hr], hv, hpos, fun j h1 h2 => ?_, h'⟩⟩
                exact hd j h1 h2
            case hpre =>
              equiv_skip
              intros
              assumption
          refine prhlStmt_unroll_left ?_
          equiv_if{1}
          case «else» =>
            refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
            obtain ⟨⟨-, -, hi, -⟩, hg⟩ := h
            simp only [decide_eq_false_iff_not, not_lt] at hg
            omega
          case «then» =>
            equiv_rcondf{1}
            equiv_seq_last 1 0 : (§i{1} = §n{1} ∧ §lres{1} = §lres0{2} ∧
                L34Inv §allGlobals{1} §allGlobals{2})
            · stmt_wp
              equiv_skip
              rintro g₁ g₂ p n i lres b p0 n0 lres0 ⟨⟨-, -, hi, hl, h⟩, -⟩
              exact ⟨hi, hl, h⟩
            equiv_if{1}
            case «then» =>
              refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
              obtain ⟨⟨hi, -⟩, hg⟩ := h
              simp only [decide_eq_true_eq] at hg
              omega
            case «else» =>
              equiv_skip
              rintro g₁ g₂ i n lres lres0 ⟨⟨-, hl, h⟩, hg⟩
              exact ⟨hg, hl, h⟩

/-- `FC` over `DS_IF2_FValid`. -/
theorem FC_L34 :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ L34Inv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app DSqueeze (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
                { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
                    (Module.app IF2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO)) })) }))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Module.app FValid
          (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
            { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
                (Module.app DSqueeze2 (Module.pair SLCommon.F.RO.asRO F2.RO.asRO)) })))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ L34Inv g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DFUNCTIONALITY.f.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§bl{1} = §bl{2} ∧ §nb{1} = §nb{2} ∧ §z{1} = §z{2} ∧
      L34Inv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, h⟩
    exact ⟨rfl, rfl, h⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ bl nb _ _ _ _ ⟨rfl, rfl, -, ⟨-, -, -, -, hc⟩⟩
    rw [hc]
  case «else» =>
    equiv_skip
    rintro g₁ g₂ bl nb z _ _ _ ⟨⟨rfl, rfl, rfl, h⟩, -⟩
    exact ⟨rfl, h⟩
  case «then» =>
    equiv_call DS_IF2_FValid
    stmt_wp
    equiv_skip
    rintro g₁ g₂ bl nb z _ _ _ ⟨⟨rfl, rfl, -, ⟨hsm, hsmi, hsp, hR, hc⟩⟩, -⟩
    refine ⟨⟨rfl, ?_⟩, fun _ _ _ _ h => h⟩
    simp only [L34Inv, sInv] at hR ⊢
    simp_reads
    exact ⟨hsm, hsmi, hsp, hR, by rw [hc]⟩

/-- `local equiv equiv_L3_L4 : L3(D, F.RO).distinguish ~ L4(D, F.RO, F2.RO).distinguish :
={glob D} ==> ={glob D, res}`. -/
theorem equiv_L3_L4 (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Ideal2 D) :
    prhlProc (fun _ g₁ _ g₂ => eqGlob D g₁ g₂)
      (L3 D SLCommon.F.RO.asRO).procedure (L4 D SLCommon.F.RO.asRO F2.RO.asRO).procedure
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
  have hcc : (BlockSponge.C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.1.trans (Footprint.compl_antimono (by gcol_fp)))
  let Lg := Lens.pair Gconcl.S.m (Lens.pair Gconcl.S.mi (Lens.pair Gconcl.S.paths
    (Lens.pair (Lens.pair SLCommon.F.RO.m F2.RO.m) BlockSponge.C.c)))
  let I : SLCommon.smap × SLCommon.smap × FMap capacity (List block × block) ×
      (FMap (List block) block × FMap (List block) block) × ℤ →
      SLCommon.smap × SLCommon.smap × FMap capacity (List block × block) ×
      (FMap (List block) block × FMap (List block) block) × ℤ → Prop := fun x y =>
    x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧
      x.2.2.2.2 = y.2.2.2.2
  have hI : ∀ g₁ g₂, I (Lg.get g₁) (Lg.get g₂) ↔ L34Inv g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (Lg.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [Lg, Footprint.lens_pair]
    exact sup_le hsm (sup_le hsmi (sup_le hspa (sup_le (sup_le hro hf2) hcc)))
  unfold L3 L4 SLCommon.IdealIndif IdealIndif Indifferentiability.GIdeal
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    refine ⟨?_, (hI _ _).mpr ?_⟩
    · simp only [touched_set_of_le_compl hsm, touched_set_of_le_compl hsmi,
        touched_set_of_le_compl hspa, touched_set_of_le_compl hro, touched_set_of_le_compl hf2,
        touched_set_of_le_compl hcc]
      exact h
    · simp only [L34Inv, sInv, Lens.pair]
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
          (prhlProc_conseq FC_L34 (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
            (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
            (prhlProc_conseq (PC_f_sInv S_IF2_S2_f) (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
              (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
              Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
            exact prhlProc_globInvF_of_writesKeep _ (by writes_keep') (by writes_keep')
              (prhlProc_conseq (PC_fi_sInv S_IF2_S2_fi) (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
                (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, hg, -⟩
    simp_reads
    exact hg

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
  have hF : FVP.fvP D ≤ ((SLCommon.F.FRO.m).footprint)ᶜ :=
    _hDd'.trans (Footprint.compl_antimono le_sup_left)
  have hF2 : FVP.fvP D ≤ ((F2.RO.m).footprint)ᶜ :=
    _hDd.2.trans (Footprint.compl_antimono (le_sup_left.trans le_sup_left))
  -- each `byequiv` of EC's proof
  have e1 := Procedure.Pr_eq_of_prhlProc (ideal_equiv D hD _hDd.1) (E₁ := fun r _ => r = true)
    (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h.2]) (a₁ := ()) (a₂ := ()) (σ₁ := m)
    (σ₂ := m) rfl
  have e2 := Procedure.Pr_eq_of_prhlProc (ideal_equiv2 D hD _hDd.1) (E₁ := fun r _ => r = true)
    (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h.2]) (a₁ := ()) (a₂ := ()) (σ₁ := m)
    (σ₂ := m) rfl
  have e3 := Procedure.Pr_eq_of_prhlProc (L2_RO_LRO D hD _hDd.1 hF) (E₁ := fun r _ => r = true)
    (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h]) (a₁ := ()) (a₂ := ()) (σ₁ := m)
    (σ₂ := m) rfl
  have e4 := Procedure.Pr_eq_of_prhlProc (Ideal_equiv_valid D hD _hDd.1)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h.2])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl
  have e5 := Procedure.Pr_eq_of_prhlProc (L_RO_LRO D hD _hDd.1 hF) (E₁ := fun r _ => r = true)
    (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h]) (a₁ := ()) (a₂ := ()) (σ₁ := m)
    (σ₂ := m) rfl
  have e6 := Procedure.Pr_eq_of_prhlProc (Ideal_equiv3 D hD _hDd.1 hF2)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h.2])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl
  have e7 := Procedure.Pr_eq_of_prhlProc (equiv_L3_L4 D hD _hDd) (E₁ := fun r _ => r = true)
    (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h.2]) (a₁ := ()) (a₂ := ()) (σ₁ := m)
    (σ₂ := m) rfl
  have e8 := Procedure.Pr_eq_of_prhlProc (L4_F_RO_LRO D hD _hDd _hDd')
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl
  have e9 := Procedure.Pr_eq_of_prhlProc (L4_F2_RO_LRO D hD _hDd _hDd')
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl
  have e10 := Procedure.Pr_eq_of_prhlProc (equiv_L4_ideal D hD _hDd)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h.2])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl
  rw [e1, ← e2, e3, ← e4, ← e5, e6, e7, e8, e9, e10]

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
/-- `P.f` is `Perm.f` (`P` is `Perm`, a `StrongPRP.PRP`, read as a `PRIMITIVE`). -/
theorem P_f : Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P =
    PRP.RP.RP.f (block × capacity) dD Perm.m Perm.mi := by
  unfold P Perm PRP.RP.RP
  simp [Indifferentiability.PRIMITIVE.f, PRP.StrongPRP.PRP.mk]

omit [BlockSponge.Params] [Params] in
/-- `P.f`, at `SLCommon`'s `PRIMITIVE`, is `Perm.f`. -/
theorem P_f' : Indifferentiability.PRIMITIVE.f state (List block) block P =
    PRP.RP.RP.f (block × capacity) dD Perm.m Perm.mi := by
  unfold P Perm PRP.RP.RP
  simp [Indifferentiability.PRIMITIVE.f, PRP.StrongPRP.PRP.mk]

omit [BlockSponge.Params] [Params] in
/-- `P.fi` is `Perm.fi`. -/
theorem P_fi : Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block) P =
    PRP.RP.RP.fi (block × capacity) dD Perm.m Perm.mi := by
  unfold P Perm PRP.RP.RP
  simp [Indifferentiability.PRIMITIVE.fi, PRP.StrongPRP.PRP.mk]

omit [BlockSponge.Params] [Params] in
/-- `P.init` is `Perm.init`. -/
theorem P_init : Indifferentiability.PRIMITIVE.init state (List block × ℤ) (List block) P =
    PRP.RP.RP.init (block × capacity) dD Perm.m Perm.mi := by
  unfold P Perm PRP.RP.RP
  simp [Indifferentiability.PRIMITIVE.init, PRP.StrongPRP.PRP.mk]

omit [BlockSponge.Params] [Params] in
/-- `P`, at `SLCommon`'s `DPRIMITIVE`, is `Perm`'s two procedures (for `writes_keep`, which
does not unfold `P`). -/
theorem P_view' : Indifferentiability.PRIMITIVE.view state (List block) block P =
    Indifferentiability.DPRIMITIVE.mk state (List block) block
      { f := PRP.RP.RP.f (block × capacity) dD Perm.m Perm.mi
        fi := PRP.RP.RP.fi (block × capacity) dD Perm.m Perm.mi } := by
  unfold Indifferentiability.PRIMITIVE.view P Perm PRP.RP.RP
  simp [Indifferentiability.PRIMITIVE.f, Indifferentiability.PRIMITIVE.fi, PRP.StrongPRP.PRP.mk]

omit [BlockSponge.Params] [Params] in
/-- `P`, at `DPRIMITIVE`, is `Perm`'s two procedures. -/
theorem P_view : Indifferentiability.PRIMITIVE.view state (List block × ℤ) (List block) P =
    Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
      { f := PRP.RP.RP.f (block × capacity) dD Perm.m Perm.mi
        fi := PRP.RP.RP.fi (block × capacity) dD Perm.m Perm.mi } := by
  unfold Indifferentiability.PRIMITIVE.view P Perm PRP.RP.RP
  simp [Indifferentiability.PRIMITIVE.f, Indifferentiability.PRIMITIVE.fi, PRP.StrongPRP.PRP.mk]

/-- The part of `squeeze_squeezeless`'s invariant the functionalities keep: `={glob Perm}` and
`INV_Real` (whose counters only say `0 <= C.c{1}`, kept by `rInv`). -/
def sqInv (g₁ g₂ : VariableAssignment) : Prop :=
  Perm.m.get g₁ = Perm.m.get g₂ ∧ Perm.mi.get g₁ = Perm.mi.get g₂ ∧
    INV_Real 0 0 (Perm.m.get g₁) (Perm.mi.get g₁) (SLCommon.Redo.prefixes.get g₁)

omit [BlockSponge.Params] [Params] in
/-- `format p (j + 1)` is `format p j` and one more `b0`. -/
theorem format_succ (bl : List block) (j : ℤ) (hj : 0 < j) :
    format bl (j + 1) = format bl j ++ [b0] := by
  simp only [format, nseq, List.append_assoc]
  rw [show (j + 1 - 1).toNat = (j - 1).toNat + 1 by omega, List.replicate_succ']

omit [BlockSponge.Params] [Params] in
/-- `size (format p j) = size p + j - 1`, for `0 < j`. -/
theorem size_format_pos (bl : List block) (j : ℤ) (hj : 0 < j) :
    size (format bl j) = size bl + j - 1 := by
  simp only [format, size, nseq, List.length_append, List.length_replicate]
  omega

omit [BlockSponge.Params] [Params] in
/-- The first `k` blocks of `format p (j + 1)` are those of `format p j`, for
`k <= size (format p j)`. -/
theorem take_format_succ (bl : List block) (j k : ℤ) (hj : 0 < j) (hk : k ≤ size (format bl j)) :
    take k (format bl (j + 1)) = take k (format bl j) := by
  rw [format_succ bl j hj]
  simp only [take, size] at hk ⊢
  rw [List.take_append_of_le_length (by omega)]

omit [BlockSponge.Params] [Params] in
/-- `format p (j + 1)` is its first `size (format p j) + 1` blocks. -/
theorem take_format_last (bl : List block) (j : ℤ) (hj : 0 < j) :
    take (size (format bl j) + 1) (format bl (j + 1)) = format bl (j + 1) := by
  rw [show size (format bl j) + 1 = size (format bl (j + 1)) by
    rw [size_format_pos _ _ hj, size_format_pos _ _ (by omega)]; ring]
  exact take_size _

omit [BlockSponge.Params] [Params] in
/-- The last block of `format p (j + 1)` is `b0`. -/
theorem nth_format_last (bl : List block) (j : ℤ) (hj : 0 < j) :
    nth default (format bl (j + 1)) (size (format bl j)) = b0 := by
  rw [format_succ bl j hj]
  simp [nth, size]

omit [BlockSponge.Params] [Params] in
/-- `b0` is the unit of `+^`. -/
theorem xorw_b0 (x : block) : x +^ b0 = x := by
  apply List.Vector.ext; intro j; simp [BitWord.xorw, b0, BitWord.zerow]

/-- `SqueezelessSponge(P).f(format p (j + 1)) ~ P.f(sa, sc)` when `format p j` is known with
value `(sa, sc)` (EC: `squeeze_squeezeless`'s squeezing `call`s, after its `splitwhile{1} 1 :
i1 < size p1 - 1`).  All but the last block are known prefixes; the last one is a known prefix
(`lemma4`, the call on the right does not sample) or a `Perm.f` call on the same input on both
sides (`lemma2'`). -/
theorem SS_f_extend (bl : List block) (j : ℤ) :
    prhlProc (sig₁ := procsig (List block) -> block) (sig₂ := procsig (state) -> state)
      (fun a₁ g₁ a₂ g₂ => valid bl = true ∧ 0 < j ∧ a₁ = format bl (j + 1) ∧
        FMap.get (SLCommon.Redo.prefixes.get g₁) (format bl j) = some a₂ ∧ sqInv g₁ g₂)
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block
        (Indifferentiability.FUNCTIONALITY.view state (List block) block
          (Module.app SLCommon.SqueezelessSponge
            (Indifferentiability.PRIMITIVE.view state (List block) block P)))).procedure
      (Indifferentiability.DPRIMITIVE.f state (List block × ℤ) (List block)
        (Indifferentiability.PRIMITIVE.view state (List block × ℤ) (List block) P)).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂.1 ∧
        FMap.get (SLCommon.Redo.prefixes.get g₁) (format bl (j + 1)) = some r₂ ∧ sqInv g₁ g₂) := by
  simp only [Indifferentiability.FUNCTIONALITY.view, Indifferentiability.DFUNCTIONALITY.f.mk_simp,
    Indifferentiability.PRIMITIVE.view, Indifferentiability.DPRIMITIVE.f.mk_simp, P_f]
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp, P_f']
  stmt_wp
  equiv_seq_last 1 2 : (§p{1} = format bl (j + 1) ∧ §sa{1} = b0 ∧ §sc{1} = c0 ∧ §i{1} = 0 ∧
      valid bl = true ∧ 0 < j ∧
      FMap.get §SLCommon.Redo.prefixes{1} (format bl j) = some §(localVarLens "x" state){2} ∧
      sqInv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x₁ x₂ ⟨hv, hj, rfl, hp, hs⟩
    exact ⟨rfl, hv, hj, hp, hs⟩
  refine prhlStmt_splitwhile_left
    ⟨fun σ => decide ((localVarLens "i" ℤ).get σ + 1 <
      size ((localVarLens "p" (List block)).get σ))⟩
    (fun σ => (size ((localVarLens "p" (List block)).get σ) - (localVarLens "i" ℤ).get σ).toNat)
    ?_ ?_
  · intro k
    hoare_wp 1
    refine hoare_pre (hoare_if_wp (Ae := fun σ => (size ((localVarLens "p" (List block)).get σ) -
        ((localVarLens "i" ℤ).get σ + 1)).toNat < k) (hoare_assign_wp _ _ _) ?_) ?_
    · hoare_wp 1
      hoare_call
      hoare_wp 1
      hoare_skip
      intro _ _ h _ _
      exact h
    · rintro σ ⟨hg, rfl⟩
      simp only [Getter.andB_get, Bool.and_eq_true, decide_eq_true_eq] at hg
      refine ⟨fun _ => ?_, fun _ => ?_⟩
      · simp_reads
        have h2 := hg.2
        generalize size ((localVarLens "p" (List block)).get σ) = a at h2 ⊢
        generalize (localVarLens "i" ℤ).get σ = b at h2 ⊢
        omega
      · have h2 := hg.2
        omega
  unfold Getter.andB
  equiv_seq_last 1 2 : (§p{1} = format bl (j + 1) ∧ §i{1} = size (format bl j) ∧
      FMap.get §SLCommon.Redo.prefixes{1} (format bl j) = some (§sa{1}, §sc{1}) ∧
      §(localVarLens "x" state){2} = (§sa{1}, §sc{1}) ∧ valid bl = true ∧ 0 < j ∧
      sqInv §allGlobals{1} §allGlobals{2})
  · equiv_while{1} (§p{1} = format bl (j + 1) ∧ 0 ≤ §i{1} ∧ §i{1} ≤ size (format bl j) ∧
        FMap.get §SLCommon.Redo.prefixes{1} (take §i{1} §p{1}) = some (§sa{1}, §sc{1}) ∧
        FMap.get §SLCommon.Redo.prefixes{1} (format bl j) = some §(localVarLens "x" state){2} ∧
        valid bl = true ∧ 0 < j ∧ sqInv §allGlobals{1} §allGlobals{2})
      ((size §p{1} - §i{1}).toNat)
    case lossless =>
      rintro σ₂ σ hI hg
      simp only [eval_lens_full, eval_lens_global, eval_getter_full,
        allGlobals_get] at hI
      obtain ⟨hp, hi0, hij, -, hfj, -, hj, -, -, hinv⟩ := hI
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      have hle : (localVarLens "i" ℤ).get σ + 1 ≤ size (format bl j) := by
        have h2 := hg.2
        rw [hp, size_format_pos _ _ (by omega)] at h2
        rw [size_format_pos _ _ hj]; omega
      have hd : FMap.dom (SLCommon.Redo.prefixes.get σ.globals)
          (take ((localVarLens "i" ℤ).get σ + 1) ((localVarLens "p" (List block)).get σ)) := by
        rw [hp, take_format_succ bl j _ hj hle]
        exact all_prefixes_of_INV_real _ _ _ _ _ hinv _ (by rw [FMap.domE, hfj]; simp) _
      simp only [Stmt.ewp_seq, Stmt.ewp_assign, Stmt.ewp_ifThenElse]
      simp_reads
      rw [if_pos (by simpa using hd)]
    case «variant» =>
      intro σ₂ k
      hoare_wp 1
      refine hoare_pre (hoare_if_wp (Ae := fun _ => False) (hoare_assign_wp _ _ _)
        (fun _ h => h.elim)) ?_
      rintro σ ⟨hI, hg, rfl⟩
      simp only [eval_lens_full, eval_lens_global, eval_getter_full,
        allGlobals_get] at hI
      obtain ⟨hp, hi0, hij, hpre, hfj, hv, hj, hs⟩ := hI
      have hinv := hs.2.2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      have hle : (localVarLens "i" ℤ).get σ + 1 ≤ size (format bl j) := by
        have h2 := hg.2
        rw [hp, size_format_pos _ _ (by omega)] at h2
        rw [size_format_pos _ _ hj]; omega
      have hd : FMap.dom (SLCommon.Redo.prefixes.get σ.globals)
          (take ((localVarLens "i" ℤ).get σ + 1) ((localVarLens "p" (List block)).get σ)) := by
        rw [hp, take_format_succ bl j _ hj hle]
        exact all_prefixes_of_INV_real _ _ _ _ _ hinv _ (by rw [FMap.domE, hfj]; simp) _
      refine ⟨fun _ => ?_, fun hd' => absurd hd (by simpa using hd')⟩
      simp only [eval_lens_full, eval_lens_global] at hg ⊢
      try simp_reads
      refine ⟨⟨hp, by omega, hle, ?_, hfj, hv, hj, hs⟩, ?_⟩
      · obtain ⟨v, hv'⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd)
        rw [hv']; rfl
      · have h2 := hg.2
        generalize size ((localVarLens "p" (List block)).get σ) = a at h2 ⊢
        generalize (localVarLens "i" ℤ).get σ = b at h2 ⊢
        omega
    case exit =>
      rintro g₁ g₂ x₁ p i sa sc ⟨rfl, hi0, hij, hpre, hfj, hv, hj, hs⟩ hg
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hg
      have hsz := size_format_pos bl (j + 1) (by omega)
      have hsz' := size_format_pos bl j hj
      have hi : i = size (format bl j) := by omega
      subst hi
      rw [take_format_succ bl j _ hj le_rfl, take_size] at hpre
      rw [hpre] at hfj
      exact ⟨rfl, rfl, hpre, (Option.some.inj hfj).symm, hv, hj, hs⟩
    equiv_skip
    rintro g₁ g₂ p x sa sc i ⟨rfl, rfl, rfl, rfl, hv, hj, hfj, hs⟩
    refine ⟨rfl, le_rfl, by rw [size_format_pos _ _ hj]; simp only [size] at *; omega, ?_, hfj,
      hv, hj, hs⟩
    rw [take, show (0 : ℤ).toNat = 0 from rfl, List.take_zero]
    exact hs.2.2.2.1
  refine prhlStmt_unroll_left ?_
  equiv_if{1}
  case «else» =>
    refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
    obtain ⟨⟨hp, hi, -, -, -, hj, -⟩, hg⟩ := h
    simp only [decide_eq_false_iff_not, not_lt] at hg
    rw [hp, hi, size_format_pos _ _ (by omega), size_format_pos _ _ hj] at hg
    omega
  case «then» =>
    equiv_rcondf{1}
    stmt_wp
    equiv_if{1}
    case «then» =>
      stmt_wp
      equiv_seq_last 0 1 : (§p{1} = format bl (j + 1) ∧ §i{1} = size (format bl j) ∧
          FMap.get §SLCommon.Redo.prefixes{1} (format bl j) = some (§sa{1}, §sc{1}) ∧
          §x0{2} = (§sa{1}, §sc{1}) ∧ 0 < j ∧ sqInv §allGlobals{1} §allGlobals{2} ∧
          FMap.dom §SLCommon.Redo.prefixes{1} (format bl (j + 1)))
      · stmt_wp
        equiv_skip
        rintro g₁ g₂ p i sa sc x ⟨⟨⟨rfl, rfl, hpj, rfl, -, hj, hs⟩, -⟩, hd⟩
        rw [take_format_last bl j hj] at hd
        exact ⟨rfl, rfl, hpj, rfl, hj, hs, by simpa using hd⟩
      equiv_if{2}
      case «then» =>
        refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
        obtain ⟨⟨-, -, hpj, hx, hj, ⟨hm, -, hinv⟩, hd⟩, hg⟩ := h
        have h4 := lemma4 _ _ _ _ _ bl j _ _ hinv hj hpj hd
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hg
        apply hg
        have hx' : (localVarLens "x0" (block × capacity)).get σ₂ =
            ((localVarLens "sa" block).get σ₁, (localVarLens "sc" capacity).get σ₁) := hx
        rw [hx', ← hm, FMap.domE, ← h4, ← FMap.domE]
        exact hd
      case «else» =>
        equiv_skip
        rintro g₁ g₂ p i sa sc x0 ⟨⟨rfl, rfl, hpj, rfl, hj, hs, hd⟩, -⟩
        have h4 := lemma4 _ _ _ _ _ bl j _ _ hs.2.2 hj hpj hd
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd)
        have hsz := size_format_pos bl (j + 1) (by omega)
        have hsz' := size_format_pos bl j hj
        refine ⟨by simp only [decide_eq_false_iff_not, not_lt]; omega, ?_, ?_, hs⟩
        · rw [take_format_last bl j hj, ← hs.1, ← h4]
        · rw [← hs.1, ← h4, hv]; rfl
    case «else» =>
      stmt_wp
      stmt_inline{1} 0
      stmt_wp
      equiv_seq_last 1 1 : (§x1{1} = §x0{2} ∧ §p{1} = format bl (j + 1) ∧
          §i{1} = size (format bl j) ∧
          ¬ FMap.dom §SLCommon.Redo.prefixes{1} (format bl (j + 1)) ∧
          FMap.get §SLCommon.Redo.prefixes{1} (format bl j) = some §x1{1} ∧
          valid bl = true ∧ 0 < j ∧ sqInv §allGlobals{1} §allGlobals{2})
      · stmt_wp
        equiv_skip
        rintro σ₁ σ₂ ⟨⟨⟨hp, hi, hpj, hx, hv, hj, hs⟩, -⟩, hd⟩
        rw [hp, hi] at hd ⊢
        rw [take_format_last bl j hj] at hd
        rw [nth_format_last bl j hj, xorw_b0]
        exact ⟨hx.symm, rfl, rfl, by simpa using hd, hpj, hv, hj, hs⟩
      equiv_if
      case guard =>
        rintro g₁ g₂ x1 p i x0 ⟨rfl, -, -, -, -, -, -, hm, -⟩
        rw [hm]
      case «then» =>
        stmt_wp
        equiv_rnd
        equiv_skip
        rintro g₁ g₂ x1 p i x0 ⟨⟨rfl, rfl, rfl, hnd, hpj, hv, hj, hm, hmi, hinv⟩, hg⟩
        refine ⟨by rw [hm], fun a ha => ?_⟩
        have hsz := size_format_pos bl (j + 1) (by omega)
        have hsz' := size_format_pos bl j hj
        have hnd' : ¬ FMap.dom (Perm.m.get g₁) x1 := by simpa using hg
        have hinv' := INV_Real_addm_mi _ _ _ _ _ _ _ hinv hnd' (not_of_mem_support_dexcepted ha)
        have h2 := lemma2' 0 0 _ _ _ bl (j + 1) x1.1 x1.2 hinv' (by omega) hv
          (by rw [FMap.domE, FMap.get_set_sameE]; simp) hnd (by simpa using hpj)
        refine ⟨by simp only [decide_eq_false_iff_not, not_lt]; omega, by rw [hm], ?_, ?_⟩
        · rw [take_format_last bl j hj, FMap.get_set_sameE, ← hm]
        · simp only [sqInv]
          simp_reads
          refine ⟨by rw [hm], by rw [hmi], ?_⟩
          rw [take_format_last bl j hj]
          simpa using h2
      case «else» =>
        equiv_skip
        rintro g₁ g₂ x1 p i x0 ⟨⟨rfl, rfl, rfl, hnd, hpj, hv, hj, hm, hmi, hinv⟩, hg⟩
        have hsz := size_format_pos bl (j + 1) (by omega)
        have hsz' := size_format_pos bl j hj
        have hd' : FMap.dom (Perm.m.get g₁) x1 := by simpa using hg
        have h2 := lemma2' 0 0 _ _ _ bl (j + 1) x1.1 x1.2 hinv (by omega) hv hd' hnd
          (by simpa using hpj)
        refine ⟨by simp only [decide_eq_false_iff_not, not_lt]; omega, by rw [hm], ?_, ?_⟩
        · rw [take_format_last bl j hj, FMap.get_set_sameE, ← hm]
        · simp only [sqInv]
          simp_reads
          refine ⟨hm, hmi, ?_⟩
          rw [take_format_last bl j hj]
          simpa using h2

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

omit [SLCommon.Params] [BlockSponge.Params] [Params] in
/-- EC's `take_nth`: `take (i + 1) l = rcons (take i l) (nth default l i)` within `l`. -/
theorem take_succ_rcons {α : Type} [Inhabited α] (l : List α) (i : ℤ) (h : 0 ≤ i ∧ i < size l) :
    take (i + 1) l = rcons (take i l) (nth default l i) := by
  simp only [size] at h
  simp only [take, rcons, nth, if_pos h.1]
  rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one,
    List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  rfl

omit [BlockSponge.Params] [Params] in
/-- Under `INV_Real`, a known prefix `take (i + 1) l` is `Perm.m` at the state of `take i l` and the
block `nth default l i` (EC: `hmp1` in `squeeze_squeezeless`). -/
theorem INV_Real_cached {c1 c2 : ℤ} {m mi : FMap state state} {p : FMap (List block) state}
    (hinv : INV_Real c1 c2 m mi p) (l : List block) (i : ℤ) (hi : 0 ≤ i ∧ i < size l)
    (sa : block) (sc : capacity) (hp : FMap.get p (take i l) = some (sa, sc))
    (hd : FMap.dom p (take (i + 1) l)) :
    FMap.get m (sa +^ nth default l i, sc) = FMap.get p (take (i + 1) l) := by
  obtain ⟨-, ⟨-, hmp⟩, -⟩ := hinv
  have hs : size (take (i + 1) l) = i + 1 := by
    simp only [size, take, List.length_take] at hi ⊢; omega
  obtain ⟨b, c, hb, hm⟩ := hmp _ hd i ⟨hi.1, by omega⟩
  have ht1 : take i (take (i + 1) l) = take i l := by
    simp only [take, List.take_take]; congr 1; omega
  have ht2 : take (i + 1) (take (i + 1) l) = take (i + 1) l := by
    simp only [take, List.take_take, min_self]
  have hn : nth default (take (i + 1) l) i = nth default l i := by
    simp only [size] at hi
    simp only [nth, take, if_pos hi.1, List.getD_eq_getElem?_getD, List.getElem?_take]
    rw [if_pos (by omega)]
  rw [ht1, hp] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb).symm
  rw [hn, ht2] at hm
  exact hm

/-- `Squeeze(SqueezelessSponge(P)).f ~ Sponge(P).f` (EC: `squeeze_squeezeless`'s functionality
`call`, behind `FC`).  Absorbing: `SqueezelessSponge`'s loop on `p` against `Sponge`'s on `xs`, with
`xs{2} = drop i0{1} p0{1}` and the prefix `take i0 p0` known with value `(sa, sc){2}`; squeezing:
the loops in lockstep, each call by `SS_f_extend` (EC's `splitwhile{1} 1 : i + 1 < n` is not
needed: the invariant's fact about the next prefix holds under `i < n`). -/
theorem DSqueeze_Sponge :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sqInv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app DSqueeze (Indifferentiability.FUNCTIONALITY.view state (List block) block
          (Module.app SLCommon.SqueezelessSponge
            (Indifferentiability.PRIMITIVE.view state (List block) block P))))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app Sponge (Indifferentiability.PRIMITIVE.view state (List block × ℤ)
          (List block) P))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sqInv g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§p{1} = §xs{2} ∧ §n{1} = §n{2} ∧ §lres{1} = [] ∧ §z{2} = [] ∧ §b{1} = b0 ∧
      §sa{2} = b0 ∧ §sc{2} = c0 ∧ §i{1} = 0 ∧ §i{2} = 0 ∧ sqInv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, h⟩
    simp_all
  equiv_if
  case guard =>
    intros
    simp_all [valid]
  case «else» =>
    equiv_skip
    intros
    simp_all
  case «then» =>
    equiv_seq_last 1 1 : (§i{1} = 0 ∧ §i{2} = 0 ∧ §n{1} = §n{2} ∧ §lres{1} = [] ∧ §z{2} = [] ∧
        §b{1} = §sa{2} ∧ valid §p{1} = true ∧
        FMap.get §SLCommon.Redo.prefixes{1} §p{1} = some (§sa{2}, §sc{2}) ∧
        sqInv §allGlobals{1} §allGlobals{2})
    · stmt_inline{1} 0
      simp only [Indifferentiability.PRIMITIVE.view, Indifferentiability.DPRIMITIVE.f.mk_simp, P_f,
        P_f']
      stmt_wp
      equiv_seq_last 1 1 : (§p0{1} = §p{1} ∧ §sa0{1} = §sa{2} ∧ §sc0{1} = §sc{2} ∧ 0 ≤ §i0{1} ∧
          §i0{1} ≤ size §p0{1} ∧ §xs{2} = drop §i0{1} §p0{1} ∧
          FMap.get §SLCommon.Redo.prefixes{1} (take §i0{1} §p0{1}) = some (§sa{2}, §sc{2}) ∧
          §i{1} = 0 ∧ §i{2} = 0 ∧ §n{1} = §n{2} ∧ §lres{1} = [] ∧ §z{2} = [] ∧
          valid §p{1} = true ∧ sqInv §allGlobals{1} §allGlobals{2})
      · stmt_wp
        equiv_skip
        rintro g₁ g₂ p n lres b i xs n' z sa sc i'
          ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs⟩, hv⟩
        obtain ⟨-, ⟨h0, -⟩, -⟩ := hs.2.2
        refine ⟨rfl, rfl, by simp [size], by simp [drop], ?_, rfl, rfl, rfl, rfl, rfl, hv, hs⟩
        simpa [take] using h0
      equiv_while_raw (§p0{1} = §p{1} ∧ §sa0{1} = §sa{2} ∧ §sc0{1} = §sc{2} ∧ 0 ≤ §i0{1} ∧
          §i0{1} ≤ size §p0{1} ∧ §xs{2} = drop §i0{1} §p0{1} ∧
          FMap.get §SLCommon.Redo.prefixes{1} (take §i0{1} §p0{1}) = some (§sa{2}, §sc{2}) ∧
          §i{1} = 0 ∧ §i{2} = 0 ∧ §n{1} = §n{2} ∧ §lres{1} = [] ∧ §z{2} = [] ∧
          valid §p{1} = true ∧ sqInv §allGlobals{1} §allGlobals{2})
      case guard =>
        rintro g₁ g₂ p0 p sa0 sc0 i0 i n lres sa sc xs i' n' z ⟨-, -, -, hi0, -, rfl, -⟩
        exact decide_lt_size_drop _ _ hi0
      case exit =>
        rintro g₁ g₂ p0 p sa0 sc0 i0 i n lres sa sc xs i' n' z
          ⟨rfl, rfl, rfl, hi0, hi1, rfl, hpre, rfl, rfl, rfl, rfl, rfl, hv, hs⟩ hg
        simp only [decide_eq_false_iff_not, not_lt] at hg
        have : i0 = size p0 := le_antisymm hi1 hg
        subst this
        rw [take_size] at hpre
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hv, hpre, hs⟩
      case body =>
        stmt_wp
        stmt_inline{2} 0
        stmt_wp
        equiv_if{1}
        case «then» =>
          stmt_wp
          equiv_seq_last 0 1 : (§x{2} = (§sa{2} +^ nth default §p0{1} §i0{1}, §sc{2}) ∧
              §p0{1} = §p{1} ∧ 0 ≤ §i0{1} ∧ §i0{1} < size §p0{1} ∧ §xs{2} = drop §i0{1} §p0{1} ∧
              FMap.get §SLCommon.Redo.prefixes{1} (take §i0{1} §p0{1}) = some (§sa{2}, §sc{2}) ∧
              FMap.dom §SLCommon.Redo.prefixes{1} (take (§i0{1} + 1) §p0{1}) ∧
              §i{1} = 0 ∧ §i{2} = 0 ∧ §n{1} = §n{2} ∧ §lres{1} = [] ∧ §z{2} = [] ∧
              valid §p{1} = true ∧ sqInv §allGlobals{1} §allGlobals{2})
          · stmt_wp
            equiv_skip
            rintro g₁ g₂ p0 p sa0 sc0 i0 i n lres sa sc xs i' n' z
              ⟨⟨⟨rfl, rfl, rfl, hi0, hi1, rfl, hpre, rfl, rfl, rfl, rfl, rfl, hv, hs⟩, hg⟩, hd⟩
            simp only [decide_eq_true_eq] at hg hd
            exact ⟨by rw [head_drop_nth _ _ _ ⟨hi0, hg⟩], rfl, hi0, hg, rfl, hpre, hd, rfl, rfl,
              rfl, rfl, rfl, hv, hs⟩
          equiv_if{2}
          case «then» =>
            refine prhlStmt_conseq prhlStmt_false (fun σ₁ σ₂ h => ?_) (fun _ _ h => h)
            obtain ⟨⟨hx, -, hi0, hi1, -, hpre, hd, -, -, -, -, -, -, hm, -, hinv⟩, hg⟩ := h
            have h4 := INV_Real_cached hinv _ _ ⟨hi0, hi1⟩ _ _ hpre hd
            simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hg
            apply hg
            have hx' : (localVarLens "x" (block × capacity)).get σ₂ =
                ((localVarLens "sa" block).get σ₂ +^
                  nth default ((localVarLens "p0" (List block)).get σ₁)
                    ((localVarLens "i0" ℤ).get σ₁),
                  (localVarLens "sc" capacity).get σ₂) := hx
            rw [hx', ← hm, FMap.domE, h4, ← FMap.domE]
            exact hd
          case «else» =>
            equiv_skip
            rintro g₁ g₂ p0 i0 p i n lres x sa sc xs i' n' z
              ⟨⟨rfl, rfl, hi0, hi1, rfl, hpre, hd, rfl, rfl, rfl, rfl, rfl, hv, hm, hmi, hinv⟩, -⟩
            have h4 := INV_Real_cached hinv _ _ ⟨hi0, hi1⟩ _ _ hpre hd
            rw [hm] at h4
            obtain ⟨v, hv'⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hd)
            refine ⟨rfl, by rw [h4], by rw [h4], by omega, by omega, behead_drop_succ _ _ hi0,
              by rw [h4, hv']; rfl, rfl, rfl, rfl, rfl, rfl, hv, hm, hmi, hinv⟩
        case «else» =>
          stmt_wp
          stmt_inline{1} 0
          stmt_wp
          equiv_seq_last 1 1 : (§x0{1} = §x{2} ∧ §x{2} = (§sa{2} +^ nth default §p0{1} §i0{1}, §sc{2}) ∧
              §p0{1} = §p{1} ∧ 0 ≤ §i0{1} ∧ §i0{1} < size §p0{1} ∧ §xs{2} = drop §i0{1} §p0{1} ∧
              FMap.get §SLCommon.Redo.prefixes{1} (take §i0{1} §p0{1}) = some (§sa{2}, §sc{2}) ∧
              ¬ FMap.dom §SLCommon.Redo.prefixes{1} (take (§i0{1} + 1) §p0{1}) ∧
              §i{1} = 0 ∧ §i{2} = 0 ∧ §n{1} = §n{2} ∧ §lres{1} = [] ∧ §z{2} = [] ∧
              valid §p{1} = true ∧ sqInv §allGlobals{1} §allGlobals{2})
          · stmt_wp
            equiv_skip
            intro σ₁ σ₂ ⟨⟨⟨hp, hsa, hsc, hi0, hi1, hxs, hpre, hi, hi', hn, hl, hz, hv, hs⟩, hg⟩, hd⟩
            simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hg hd
            refine ⟨by rw [hsa, hsc, hxs, head_drop_nth _ _ _ ⟨hi0, hg⟩],
              by rw [hxs, head_drop_nth _ _ _ ⟨hi0, hg⟩], hp, hi0, hg, hxs, hpre, hd, hi, hi', hn,
              hl, hz, hv, hs⟩
          equiv_if
          case guard =>
            rintro g₁ g₂ x0 p0 i0 p i n lres x sa sc xs i' n' z
              ⟨rfl, -, -, -, -, -, -, -, -, -, -, -, -, -, hm, -⟩
            rw [hm]
          case «then» =>
            stmt_wp
            equiv_rnd
            equiv_skip
            rintro g₁ g₂ x0 p0 i0 p i n lres x sa sc xs i' n' z
              ⟨⟨rfl, rfl, rfl, hi0, hi1, rfl, hpre, hnd, rfl, rfl, rfl, rfl, rfl, hv, hm, hmi,
                hinv⟩, hg⟩
            refine ⟨by rw [hm], fun a ha => ?_⟩
            have hnd' : ¬ FMap.dom (Perm.m.get g₁) (sa +^ nth default p0 i0, sc) := by
              simpa using hg
            have hinv' := INV_Real_addm_mi _ _ _ _ _ _ _ hinv hnd' (not_of_mem_support_dexcepted ha)
            have h3 := lemma_3 0 0 _ _ _ (take i0 p0) (nth default p0 i0) sa sc hinv'
              (by rw [FMap.domE, FMap.get_set_sameE]; simp)
              (by rwa [← take_succ_rcons _ _ ⟨hi0, hi1⟩]) hpre
            refine ⟨rfl, by rw [hm], by rw [hm], by omega, by omega, behead_drop_succ _ _ hi0,
              by rw [FMap.get_set_sameE, hm], rfl, rfl, rfl, rfl, rfl, hv, ?_⟩
            simp only [sqInv]
            simp_reads
            refine ⟨by rw [hm], by rw [hmi], ?_⟩
            rw [take_succ_rcons _ _ ⟨hi0, hi1⟩]
            simpa using h3
          case «else» =>
            equiv_skip
            rintro g₁ g₂ x0 p0 i0 p i n lres x sa sc xs i' n' z
              ⟨⟨rfl, rfl, rfl, hi0, hi1, rfl, hpre, hnd, rfl, rfl, rfl, rfl, rfl, hv, hm, hmi,
                hinv⟩, hg⟩
            have hd' : FMap.dom (Perm.m.get g₁) (sa +^ nth default p0 i0, sc) := by simpa using hg
            have h3 := lemma_3 0 0 _ _ _ (take i0 p0) (nth default p0 i0) sa sc hinv hd'
              (by rwa [← take_succ_rcons _ _ ⟨hi0, hi1⟩]) hpre
            refine ⟨rfl, by rw [hm], by rw [hm], by omega, by omega, behead_drop_succ _ _ hi0,
              by rw [FMap.get_set_sameE, hm], rfl, rfl, rfl, rfl, rfl, hv, ?_⟩
            simp only [sqInv]
            simp_reads
            refine ⟨hm, hmi, ?_⟩
            rw [take_succ_rcons _ _ ⟨hi0, hi1⟩]
            simpa using h3
      case hpre =>
        equiv_skip
        intros
        assumption
    equiv_while_raw (§i{1} = §i{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §z{2} ∧
        §(localVarLens "b" block){1} = §sa{2} ∧ 0 ≤ §i{1} ∧ valid §p{1} = true ∧
        (§i{1} < §n{1} →
          FMap.get §SLCommon.Redo.prefixes{1} (format §p{1} (§i{1} + 1)) = some (§sa{2}, §sc{2})) ∧
        sqInv §allGlobals{1} §allGlobals{2})
    case guard =>
      rintro g₁ g₂ i n lres b p i' n' z sa sc ⟨rfl, rfl, -⟩
      rfl
    case exit =>
      rintro g₁ g₂ i n lres b p i' n' z sa sc ⟨rfl, rfl, rfl, -, -, -, -, hs⟩ -
      exact ⟨rfl, hs⟩
    case body =>
      equiv_seq_last 1 1 : (§i{1} = §i{2} ∧ §n{1} = §n{2} ∧ §lres{1} = §z{2} ∧
          §(localVarLens "b" block){1} = §sa{2} ∧ 0 < §i{1} ∧ valid §p{1} = true ∧
          FMap.get §SLCommon.Redo.prefixes{1} (format §p{1} §i{1}) = some (§sa{2}, §sc{2}) ∧
          sqInv §allGlobals{1} §allGlobals{2})
      · stmt_wp
        equiv_skip
        rintro g₁ g₂ i n lres b p i' n' z sa sc ⟨⟨rfl, rfl, rfl, rfl, hi0, hv, hpf, hs⟩, hg⟩
        simp only [decide_eq_true_eq] at hg
        exact ⟨rfl, rfl, rfl, rfl, by omega, hv, hpf hg, hs⟩
      equiv_if
      case guard =>
        rintro g₁ g₂ i n lres b p i' n' z sa sc ⟨rfl, rfl, -⟩
        rfl
      case «else» =>
        equiv_skip
        rintro g₁ g₂ i n lres b p i' n' z sa sc ⟨⟨rfl, rfl, rfl, rfl, hi0, hv, -, hs⟩, hg⟩
        simp only [decide_eq_false_iff_not, not_lt] at hg
        exact ⟨rfl, rfl, rfl, rfl, by omega, hv, fun h => absurd h (by omega), hs⟩
      case «then» =>
        refine prhlStmt_fix_left
          (fun σ => ((localVarLens "p" (List block)).get σ, (localVarLens "i" ℤ).get σ))
          (fun q => ?_)
        equiv_call (SS_f_extend q.1 q.2)
        equiv_skip
        rintro g₁ g₂ i n lres b p i' n' z sa sc ⟨⟨⟨rfl, rfl, rfl, rfl, hi0, hv, hpf, hs⟩, -⟩, rfl⟩
        exact ⟨⟨hv, hi0, rfl, hpf, hs⟩, fun r₁ g₁' r₂ g₂' ⟨hr, hpf', hs'⟩ =>
          ⟨rfl, rfl, rfl, hr, by omega, hv, fun _ => hpf', hs'⟩⟩
    case hpre =>
      equiv_skip
      rintro g₁ g₂ i n lres b p i' n' z sa sc ⟨rfl, rfl, rfl, rfl, rfl, rfl, hv, hpp, hs⟩
      exact ⟨rfl, rfl, rfl, rfl, le_rfl, hv, fun _ => by simpa [format, nseq] using hpp, hs⟩

/-- `P.f ~ P.f` keeps `sqInv` (`INV_Real_addm_mi`). -/
theorem Perm_f_sq :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sqInv g₁ g₂)
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P).procedure
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sqInv g₁ g₂) := by
  rw [P_f]
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§x0{1} = §x0{2} ∧ sqInv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, h⟩
    exact ⟨rfl, h⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ x _ ⟨rfl, hm, -, -⟩
    rw [hm]
  case «else» =>
    equiv_skip
    rintro g₁ g₂ x _ ⟨⟨rfl, hm, hmi, hinv⟩, -⟩
    exact ⟨by rw [hm], hm, hmi, hinv⟩
  case «then» =>
    stmt_wp
    equiv_rnd
    equiv_skip
    rintro g₁ g₂ x _ ⟨⟨rfl, hm, hmi, hinv⟩, hg⟩
    refine ⟨by rw [hm], fun a ha => ?_⟩
    simp only [sqInv]
    simp_reads
    refine ⟨by rw [hm], by rw [hm], by rw [hmi], ?_⟩
    exact INV_Real_addm_mi _ _ _ _ _ _ _ hinv (by simpa using hg)
      (not_of_mem_support_dexcepted ha)

/-- `P.fi ~ P.fi` keeps `sqInv`. -/
theorem Perm_fi_sq :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ sqInv g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block) P).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block) P).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ sqInv g₁ g₂) := by
  rw [P_fi]
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§y0{1} = §y0{2} ∧ sqInv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, h⟩
    exact ⟨rfl, h⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ x _ ⟨rfl, -, hmi, -⟩
    rw [hmi]
  case «else» =>
    equiv_skip
    rintro g₁ g₂ x _ ⟨⟨rfl, hm, hmi, hinv⟩, -⟩
    exact ⟨by rw [hmi], hm, hmi, hinv⟩
  case «then» =>
    stmt_wp
    equiv_rnd
    equiv_skip
    rintro g₁ g₂ y _ ⟨⟨rfl, hm, hmi, hinv⟩, hg⟩
    refine ⟨by rw [hmi], fun a ha => ?_⟩
    simp only [sqInv]
    simp_reads
    refine ⟨by rw [hmi], by rw [hm], by rw [hmi], ?_⟩
    have hinvm : invm (Perm.m.get g₁) (Perm.mi.get g₁) := by obtain ⟨-, -, h⟩ := hinv; exact h
    refine INV_Real_addm_mi _ _ _ _ _ _ _ hinv ?_ ?_
    · rw [invm_dom_rng _ _ hinvm]
      exact not_of_mem_support_dexcepted ha
    · rw [← invm_dom_rng _ _ (invmC' _ _ hinvm)]
      simpa using hg

/-- `squeeze_squeezeless`'s invariant (EC: `={glob Perm, C.c} /\ C.c{1} <= max_size /\
INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1}`; `INV_Real`'s counters only say
`0 <= C.c{1}`, not needed). -/
def rInv (g₁ g₂ : VariableAssignment) : Prop :=
  BlockSponge.C.c.get g₁ = BlockSponge.C.c.get g₂ ∧ BlockSponge.C.c.get g₁ ≤ max_size ∧
    sqInv g₁ g₂

/-- `PC(P).f` keeps `rInv` (EC: `squeeze_squeezeless`'s first oracle subgoal). -/
theorem PC_f_rInv :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ rInv g₁ g₂)
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P
            fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
              P }))).procedure
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P
            fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
              P }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ rInv g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ rInv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ a _ ⟨rfl, h⟩
    exact ⟨rfl, h⟩
    
  · equiv_if
    case guard =>
      rintro g₁ g₂ a _ z _ ⟨-, -, hc, -⟩
      rw [hc]
    case «else» =>
      equiv_skip
      rintro g₁ g₂ a _ z _ ⟨⟨-, rfl, h⟩, -⟩
      exact ⟨rfl, h⟩
    case «then» =>
      stmt_wp
      equiv_call (prhlProc_frame_of_writesKeep BlockSponge.C.c.get BlockSponge.C.c.get
        (fun c₁ c₂ => c₁ = c₂ ∧ c₁ + 1 ≤ max_size)
        (by rw [P_f]; writes_keep <;> (intro v σ; simp_reads; try trivial))
        (by rw [P_f]; writes_keep <;> (intro v σ; simp_reads; try trivial)) Perm_f_sq)
      equiv_skip
      rintro g₁ g₂ a _ z _ ⟨⟨rfl, -, hc, -, hs⟩, hg⟩
      refine ⟨⟨⟨rfl, hs⟩, hc, by simpa using hg⟩, fun r₁ g₁' r₂ g₂' ⟨⟨hr, hs'⟩, hc', hg'⟩ => ?_⟩
      simp only [rInv, sqInv] at hs' ⊢
      simp_reads
      exact ⟨hr, by rw [hc'], hg', hs'⟩

/-- `PC(P).fi` keeps `rInv`. -/
theorem PC_fi_rInv :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ rInv g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P
            fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
              P }))).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P
            fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
              P }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ rInv g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.fi.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ rInv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ a _ ⟨rfl, h⟩
    exact ⟨rfl, h⟩
    
  · equiv_if
    case guard =>
      rintro g₁ g₂ a _ z _ ⟨-, -, hc, -⟩
      rw [hc]
    case «else» =>
      equiv_skip
      rintro g₁ g₂ a _ z _ ⟨⟨-, rfl, h⟩, -⟩
      exact ⟨rfl, h⟩
    case «then» =>
      stmt_wp
      equiv_call (prhlProc_frame_of_writesKeep BlockSponge.C.c.get BlockSponge.C.c.get
        (fun c₁ c₂ => c₁ = c₂ ∧ c₁ + 1 ≤ max_size)
        (by rw [P_fi]; writes_keep <;> (intro v σ; simp_reads; try trivial))
        (by rw [P_fi]; writes_keep <;> (intro v σ; simp_reads; try trivial)) Perm_fi_sq)
      equiv_skip
      rintro g₁ g₂ a _ z _ ⟨⟨rfl, -, hc, -, hs⟩, hg⟩
      refine ⟨⟨⟨rfl, hs⟩, hc, by simpa using hg⟩, fun r₁ g₁' r₂ g₂' ⟨⟨hr, hs'⟩, hc', hg'⟩ => ?_⟩
      simp only [rInv, sqInv] at hs' ⊢
      simp_reads
      exact ⟨hr, by rw [hc'], hg', hs'⟩

/-- `FC(Squeeze(SqueezelessSponge(P))).f ~ FC(Sponge(P)).f` keeps `rInv`: `DSqueeze_Sponge`,
with `C.c` framed through the call. -/
theorem FC_rInv :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ rInv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app DSqueeze (Indifferentiability.FUNCTIONALITY.view state (List block) block
                (Module.app SLCommon.SqueezelessSponge
                  (Indifferentiability.PRIMITIVE.view state (List block) block P)))) }))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app Sponge (Indifferentiability.PRIMITIVE.view state (List block × ℤ)
                (List block) P)) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ rInv g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DFUNCTIONALITY.f.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§bl{1} = §bl{2} ∧ §nb{1} = §nb{2} ∧ §z{1} = §z{2} ∧
      rInv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, h⟩
    exact ⟨rfl, rfl, h⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ bl nb _ _ _ _ ⟨rfl, rfl, -, hc, -⟩
    rw [hc]
  case «else» =>
    equiv_skip
    rintro g₁ g₂ bl nb z _ _ _ ⟨⟨rfl, rfl, rfl, h⟩, -⟩
    exact ⟨rfl, h⟩
  case «then» =>
    equiv_call (prhlProc_frame_of_writesKeep BlockSponge.C.c.get BlockSponge.C.c.get
      (fun c₁ c₂ => c₁ = c₂ ∧ c₁ ≤ max_size)
      (by rw [P_view']; writes_keep <;> (intro v σ; simp_reads; try trivial))
      (by rw [P_view]; writes_keep <;> (intro v σ; simp_reads; try trivial)) DSqueeze_Sponge)
    stmt_wp
    equiv_skip
    rintro g₁ g₂ bl nb z _ _ _ ⟨⟨rfl, rfl, -, hc, -, hs⟩, hg⟩
    simp only [decide_eq_true_eq] at hg
    refine ⟨⟨⟨rfl, ?_⟩, by rw [hc], hg⟩, fun r₁ g₁' r₂ g₂' ⟨⟨hr, hs'⟩, hc', hle⟩ =>
      ⟨hr, hc', hle, hs'⟩⟩
    simp only [sqInv] at hs ⊢
    simp_reads
    exact hs

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
  have hm : (Perm.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_sub)))
  have hmi : (Perm.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_sub)))
  have hpr : (SLCommon.Redo.prefixes).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_sub)))
  have hcc : (BlockSponge.C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_sub)))
  unfold RealIndif Indifferentiability.GReal
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [P_init, Squeeze, Indifferentiability.FUNCTIONALITY.init.mk_simp]
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  let Lg := Lens.pair Perm.m (Lens.pair Perm.mi
    (Lens.pair SLCommon.Redo.prefixes BlockSponge.C.c))
  let I : FMap state state × FMap state state × FMap (List block) state × ℤ →
      FMap state state × FMap state state × FMap (List block) state × ℤ → Prop := fun x y =>
    x.2.2.2 = y.2.2.2 ∧ x.2.2.2 ≤ max_size ∧ x.1 = y.1 ∧ x.2.1 = y.2.1 ∧
      INV_Real 0 0 x.1 x.2.1 x.2.2.1
  have hI : ∀ g₁ g₂, I (Lg.get g₁) (Lg.get g₂) ↔ rInv g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (Lg.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [Lg, Footprint.lens_pair]
    exact sup_le hm (sup_le hmi (sup_le hpr hcc))
  stmt_wp
  equiv_seq_last 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    refine ⟨?_, (hI _ _).mpr ?_⟩
    · simp only [touched_set_of_le_compl hm, touched_set_of_le_compl hmi,
        touched_set_of_le_compl hpr, touched_set_of_le_compl hcc]
      exact h
    · simp only [rInv, sqInv]
      simp_reads
      exact ⟨SLCommon.max_ge0, INV_Real_init⟩
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
          Module.fst_pair, Module.snd_pair, Indifferentiability.DFUNCTIONALITY.f.mk_simp,
          Indifferentiability.FUNCTIONALITY.f.mk_simp]
        exact prhlProc_globInvF_of_writesKeep _ (by rw [P_view']; writes_keep')
          (by rw [P_view]; writes_keep')
          (prhlProc_conseq FC_rInv (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
            (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact prhlProc_globInvF_of_writesKeep _ (by rw [P_f, P_fi]; writes_keep')
            (by rw [P_f, P_fi]; writes_keep')
            (prhlProc_conseq PC_f_rInv (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
              (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
              Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
            exact prhlProc_globInvF_of_writesKeep _ (by rw [P_f, P_fi]; writes_keep')
              (by rw [P_f, P_fi]; writes_keep')
              (prhlProc_conseq PC_fi_rInv (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
                (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, hg, hI'⟩
    obtain ⟨hc, hle, hm', hmi', -⟩ := (hI _ _).mp hI'
    simp_reads
    exact ⟨hm', hmi', hg, hc, hle⟩

omit [BlockSponge.Params] [Params] in
/-- `P.fi`, at `SLCommon`'s `PRIMITIVE`, is `Perm.fi`. -/
theorem P_fi' : Indifferentiability.PRIMITIVE.fi state (List block) block P =
    PRP.RP.RP.fi (block × capacity) dD Perm.m Perm.mi := by
  unfold P Perm PRP.RP.RP
  simp [Indifferentiability.PRIMITIVE.fi, PRP.StrongPRP.PRP.mk]

omit [BlockSponge.Params] [Params] in
/-- `Perm` as `SLCommon`'s `PRIMITIVE` (for `writes_keep` through `SLCommon.PC(Perm)`). -/
theorem Perm_mk : (Perm : SLCommon.PRIMITIVE) =
    Indifferentiability.PRIMITIVE.mk state (List block) block
      { init := PRP.RP.RP.init (block × capacity) dD Perm.m Perm.mi
        f := PRP.RP.RP.f (block × capacity) dD Perm.m Perm.mi
        fi := PRP.RP.RP.fi (block × capacity) dD Perm.m Perm.mi } := rfl

/-- `equiv_sponge`'s invariant without the counters (EC: `={Redo.prefixes, glob P, C.c} /\ C.c{1} <=
max_size`). -/
def eInv0 (g₁ g₂ : VariableAssignment) : Prop :=
  SLCommon.Redo.prefixes.get g₁ = SLCommon.Redo.prefixes.get g₂ ∧
    Perm.m.get g₁ = Perm.m.get g₂ ∧ Perm.mi.get g₁ = Perm.mi.get g₂ ∧
    BlockSponge.C.c.get g₁ = BlockSponge.C.c.get g₂ ∧ BlockSponge.C.c.get g₁ ≤ max_size

/-- `INV_Real` with `SLCommon.C.c` (the primitive calls on the left) below `k`. -/
def cntInv (k : ℤ) (g : VariableAssignment) : Prop :=
  INV_Real (SLCommon.C.c.get g) k (Perm.m.get g) (Perm.mi.get g) (SLCommon.Redo.prefixes.get g)

omit [BlockSponge.Params] [Params] in
/-- `INV_Real` with a larger bound. -/
theorem INV_Real_mono {c1 c2 c2' : ℤ} {m mi : FMap state state} {p : FMap (List block) state}
    (h : INV_Real c1 c2 m mi p) (h2 : c2 ≤ c2') : INV_Real c1 c2' m mi p := by
  obtain ⟨hc, hm, hi⟩ := h
  exact ⟨hc.trans h2, hm, hi⟩

/-- `SqueezelessSponge(SLCommon.PC(P)).f ~ SqueezelessSponge(P).f` on `bl`: same code, the left
counting its calls of `P`. With `take s bl` known, only the prefixes past `s` can call `P`, so the
count grows by at most `size bl - s` (EC: `equiv_sponge`'s inner `while`s, with `s = 0` for
absorbing and `s = size (format p i)` for squeezing). -/
theorem SS_gen (bl : List block) (s k : ℤ) :
    prhlProc (sig₁ := procsig (List block) -> block) (sig₂ := procsig (List block) -> block)
      (fun a₁ g₁ a₂ g₂ => a₁ = bl ∧ a₂ = bl ∧ 0 ≤ s ∧ s ≤ size bl ∧
        FMap.dom (SLCommon.Redo.prefixes.get g₁) (take s bl) ∧ eInv0 g₁ g₂ ∧ cntInv k g₁)
      (Indifferentiability.FUNCTIONALITY.f state (List block) block
        (Module.app SLCommon.SqueezelessSponge (Indifferentiability.PRIMITIVE.view state
          (List block) block (Module.app SLCommon.PC Perm)))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block) block
        (Module.app SLCommon.SqueezelessSponge (Indifferentiability.PRIMITIVE.view state
          (List block) block P))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eInv0 g₁ g₂ ∧ cntInv (k + (size bl - s)) g₁ ∧
        ∃ c, FMap.get (SLCommon.Redo.prefixes.get g₁) bl = some (r₁, c)) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.PRIMITIVE.view, Indifferentiability.DPRIMITIVE.f.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§p{1} = bl ∧ §p{2} = bl ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧ §i{1} = §i{2} ∧
      0 ≤ §i{1} ∧ §i{1} ≤ size bl ∧
      FMap.get §SLCommon.Redo.prefixes{1} (take §i{1} bl) = some (§sa{1}, §sc{1}) ∧
      0 ≤ s ∧ s ≤ size bl ∧ FMap.dom §SLCommon.Redo.prefixes{1} (take s bl) ∧
      eInv0 §allGlobals{1} §allGlobals{2} ∧ cntInv (k + max 0 (§i{1} - s)) §allGlobals{1})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x₁ x₂ ⟨h1, h2, hs0, hsl, hd, he, hc⟩
    subst x₁ x₂
    have h0 : FMap.get (SLCommon.Redo.prefixes.get g₁) [] = some (b0, c0) := by
      obtain ⟨-, ⟨h0, -⟩, -⟩ := hc; exact h0
    exact ⟨rfl, rfl, by simp only [size]; omega, by simpa [take] using h0, hs0, hsl, hd, he,
      INV_Real_mono hc (by omega)⟩
  equiv_while_raw (§p{1} = bl ∧ §p{2} = bl ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧ §i{1} = §i{2} ∧
      0 ≤ §i{1} ∧ §i{1} ≤ size bl ∧
      FMap.get §SLCommon.Redo.prefixes{1} (take §i{1} bl) = some (§sa{1}, §sc{1}) ∧
      0 ≤ s ∧ s ≤ size bl ∧ FMap.dom §SLCommon.Redo.prefixes{1} (take s bl) ∧
      eInv0 §allGlobals{1} §allGlobals{2} ∧ cntInv (k + max 0 (§i{1} - s)) §allGlobals{1})
  case guard =>
    rintro g₁ g₂ p sa sc i p' sa' sc' i' ⟨hp, hp', -, -, hi, -⟩
    rw [hp, hp', hi]
  case exit =>
    rintro g₁ g₂ p sa sc i p' sa' sc' i'
      ⟨hp, hp', hsa, -, hi, hi0, hil, hpre, hs0, hsl, -, he, hc⟩ hg
    subst p p'
    simp only [decide_eq_false_iff_not, not_lt] at hg
    obtain rfl : i = size bl := le_antisymm hil hg
    rw [take_size] at hpre
    exact ⟨hsa, he, INV_Real_mono hc (by omega), _, hpre⟩
  case body =>
    stmt_wp
    equiv_if
    case guard =>
      rintro g₁ g₂ p sa sc i p' sa' sc' i' ⟨⟨hp, hp', -, -, hi, -, -, -, -, -, -, ⟨hpe, -⟩, -⟩, -⟩
      rw [hp, hp', hi, hpe]
    case «then» =>
      stmt_wp
      equiv_skip
      rintro g₁ g₂ p sa sc i p' sa' sc' i'
        ⟨⟨⟨hp, hp', hsa, hsc, hi, hi0, hil, hpre, hs0, hsl, hd, he, hc⟩, hg⟩, hdd⟩
      subst p p' i'
      simp only [decide_eq_true_eq] at hg hdd
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((FMap.domE _ _).mp hdd)
      refine ⟨rfl, rfl, by rw [he.1], by rw [he.1], rfl, by omega, by omega, by simp [hv, oget],
        hs0, hsl, hd, he, INV_Real_mono hc (by omega)⟩
    case «else» =>
      stmt_wp
      simp only [P_f']
      stmt_inline{1} 0
      stmt_inline{2} 0
      simp only [P_f']
      stmt_inline{1} 0
      stmt_wp
      equiv_seq_last 1 1 : (§p{1} = bl ∧ §p{2} = bl ∧ §x0{1} = §x{2} ∧ §i{1} = §i{2} ∧ 0 ≤ §i{1} ∧
          §i{1} < size bl ∧ s ≤ §i{1} ∧
          ¬ FMap.dom §SLCommon.Redo.prefixes{1} (take (§i{1} + 1) bl) ∧
          (∃ sa0 sc0, FMap.get §SLCommon.Redo.prefixes{1} (take §i{1} bl) = some (sa0, sc0) ∧
            §x{2} = (sa0 +^ nth default bl §i{1}, sc0)) ∧
          0 ≤ s ∧ s ≤ size bl ∧ FMap.dom §SLCommon.Redo.prefixes{1} (take s bl) ∧
          eInv0 §allGlobals{1} §allGlobals{2} ∧ cntInv (k + max 0 (§i{1} - s)) §allGlobals{1})
      · stmt_wp
        equiv_skip
        intro σ₁ σ₂ ⟨⟨⟨hp, hp', hsa, hsc, hi, hi0, hil, hpre, hs0, hsl, hd, he, hc⟩, hg⟩, hnd⟩
        simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hg hnd
        rw [hp] at hg hnd
        rw [hp, hp', ← hsa, ← hsc, ← hi]
        have hsi : s ≤ (localVarLens "i" ℤ).get σ₁ := by
          by_contra hlt
          apply hnd
          have := all_prefixes_of_INV_real _ _ _ _ _ hc (take s bl) hd
            ((localVarLens "i" ℤ).get σ₁ + 1)
          rwa [show take ((localVarLens "i" ℤ).get σ₁ + 1) (take s bl) =
            take ((localVarLens "i" ℤ).get σ₁ + 1) bl by
              simp only [take, List.take_take]; congr 1; omega] at this
        exact ⟨rfl, rfl, rfl, rfl, hi0, hg, hsi, hnd, ⟨_, _, hpre, rfl⟩, hs0, hsl, hd, he, hc⟩
      equiv_if
      case guard =>
        rintro g₁ g₂ p x0 i p' x i' ⟨-, -, hx, -, -, -, -, -, -, -, -, -, ⟨-, hm, -⟩, -⟩
        rw [hx, hm]
      case «then» =>
        stmt_wp
        equiv_rnd
        equiv_skip
        rintro g₁ g₂ p x0 i p' x i' ⟨⟨hp, hp', hx, hi, hi0, hil, hsi, hnd, ⟨sa0, sc0, hpre, hx2⟩,
          hs0, hsl, hd, ⟨hpe, hm, hmi, hcc, hcm⟩, hc⟩, hg⟩
        subst p p' i' x
        refine ⟨by rw [hm], fun a ha => ?_⟩
        have hnd' : ¬ FMap.dom (Perm.m.get g₁) x0 := by simpa using hg
        have hinv1 := INV_Real_addm_mi _ _ _ _ _ _ _ hc hnd' (not_of_mem_support_dexcepted ha)
        have h3 := lemma_3 _ _ _ _ _ (take i bl) (nth default bl i) sa0 sc0 hinv1
          (by rw [FMap.domE, ← hx2, FMap.get_set_sameE]; simp)
          (by rwa [← take_succ_rcons _ _ ⟨hi0, hil⟩]) hpre
        rw [← hx2] at h3
        refine ⟨rfl, rfl, by rw [hm], by rw [hm], rfl, by omega, by omega,
          by rw [FMap.get_set_sameE], hs0, hsl, (FMap.mem_set _ _ _ _).mpr (Or.inl hd), ?_, ?_⟩
        · simp only [eInv0]
          simp_reads
          exact ⟨by rw [hpe, hm], by rw [hm], by rw [hmi], hcc, hcm⟩
        · simp only [cntInv]
          simp_reads
          rw [take_succ_rcons _ _ ⟨hi0, hil⟩, Prod.mk.eta]
          obtain ⟨hc', hmp', hiv'⟩ := h3
          exact ⟨by omega, hmp', hiv'⟩
      case «else» =>
        equiv_skip
        rintro g₁ g₂ p x0 i p' x i' ⟨⟨hp, hp', hx, hi, hi0, hil, hsi, hnd, ⟨sa0, sc0, hpre, hx2⟩,
          hs0, hsl, hd, ⟨hpe, hm, hmi, hcc, hcm⟩, hc⟩, hg⟩
        subst p p' i' x
        have hd' : FMap.dom (Perm.m.get g₁) x0 := by simpa using hg
        have h3 := lemma_3 _ _ _ _ _ (take i bl) (nth default bl i) sa0 sc0 hc
          (by rw [← hx2]; exact hd') (by rwa [← take_succ_rcons _ _ ⟨hi0, hil⟩]) hpre
        rw [← hx2] at h3
        refine ⟨rfl, rfl, by rw [hm], by rw [hm], rfl, by omega, by omega,
          by rw [FMap.get_set_sameE], hs0, hsl, (FMap.mem_set _ _ _ _).mpr (Or.inl hd), ?_, ?_⟩
        · simp only [eInv0]
          simp_reads
          exact ⟨by rw [hpe, hm], hm, hmi, hcc, hcm⟩
        · simp only [cntInv]
          simp_reads
          rw [take_succ_rcons _ _ ⟨hi0, hil⟩, Prod.mk.eta]
          obtain ⟨hc', hmp', hiv'⟩ := h3
          exact ⟨by omega, hmp', hiv'⟩
  case hpre =>
    equiv_skip
    intros
    assumption

/-- `DSqueeze` over the two squeezeless sponges: the count grows by at most
`size bl + max (nb - 1) 0` (EC: `equiv_sponge`'s functionality `call`). -/
theorem DSqueeze_count (bl : List block) (nb k : ℤ) :
    prhlProc (sig₁ := procsig (List block × ℤ) -> List block)
      (sig₂ := procsig (List block × ℤ) -> List block)
      (fun a₁ g₁ a₂ g₂ => a₁ = (bl, nb) ∧ a₂ = (bl, nb) ∧ eInv0 g₁ g₂ ∧ cntInv k g₁)
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app DSqueeze (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
          { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
              (Module.app SLCommon.SqueezelessSponge (Indifferentiability.PRIMITIVE.view state
                (List block) block (Module.app SLCommon.PC Perm))) }))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app DSqueeze (Indifferentiability.FUNCTIONALITY.view state (List block) block
          (Module.app SLCommon.SqueezelessSponge
            (Indifferentiability.PRIMITIVE.view state (List block) block P))))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eInv0 g₁ g₂ ∧ cntInv (k + size bl + max (nb - 1) 0) g₁) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DFUNCTIONALITY.f.mk_simp, Indifferentiability.FUNCTIONALITY.view]
  stmt_wp
  equiv_seq_last 1 1 : (§p{1} = bl ∧ §p{2} = bl ∧ §n{1} = nb ∧ §n{2} = nb ∧ §lres{1} = [] ∧
      §lres{2} = [] ∧ §(localVarLens "b" block){1} = b0 ∧ §(localVarLens "b" block){2} = b0 ∧
      §i{1} = 0 ∧ §i{2} = 0 ∧ eInv0 §allGlobals{1} §allGlobals{2} ∧ cntInv k §allGlobals{1})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x₁ x₂ ⟨rfl, rfl, he, hc⟩
    exact ⟨rfl, rfl, rfl, rfl, he, hc⟩
  have hsz : 0 ≤ size bl := by simp only [size]; omega
  equiv_if
  case guard =>
    rintro g₁ g₂ p n lres b i p' n' lres' b' i' ⟨hp, hp', -⟩
    rw [hp, hp']
  case «else» =>
    equiv_skip
    rintro g₁ g₂ p n lres b i p' n' lres' b' i' ⟨⟨-, -, -, -, hl, hl', -, -, -, -, he, hc⟩, -⟩
    exact ⟨by rw [hl, hl'], he, INV_Real_mono hc (by omega)⟩
  case «then» =>
    equiv_seq_last 1 1 : (§p{1} = bl ∧ §p{2} = bl ∧ §n{1} = nb ∧ §n{2} = nb ∧ §lres{1} = [] ∧
        §lres{2} = [] ∧ §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧
        §i{1} = 0 ∧ §i{2} = 0 ∧ valid bl = true ∧ FMap.dom §SLCommon.Redo.prefixes{1} bl ∧
        eInv0 §allGlobals{1} §allGlobals{2} ∧ cntInv (k + size bl) §allGlobals{1})
    · equiv_call (SS_gen bl 0 k)
      equiv_skip
      rintro g₁ g₂ p n lres b i p' n' lres' b' i'
        ⟨⟨hp, hp', hn, hn', hl, hl', -, -, hi, hi', he, hc⟩, hv⟩
      subst p p'
      refine ⟨⟨rfl, rfl, hsz, ?_, he, hc⟩, fun r₁ g₁' r₂ g₂' ⟨hr, he', hc', c, hpc⟩ =>
        ⟨rfl, rfl, hn, hn', hl, hl', hr, hi, hi', hv, by rw [FMap.domE, hpc]; simp, he',
          by simpa using hc'⟩⟩
      obtain ⟨-, ⟨h0, -⟩, -⟩ := hc
      simp [take, FMap.domE, h0]
    equiv_while_raw (§p{1} = bl ∧ §p{2} = bl ∧ §n{1} = nb ∧ §n{2} = nb ∧ §i{1} = §i{2} ∧
        §lres{1} = §lres{2} ∧ §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧
        0 ≤ §i{1} ∧ valid bl = true ∧
        (§i{1} < nb → FMap.dom §SLCommon.Redo.prefixes{1} (format bl (§i{1} + 1))) ∧
        eInv0 §allGlobals{1} §allGlobals{2} ∧
        cntInv (k + size bl + max 0 (min §i{1} (nb - 1))) §allGlobals{1})
    case guard =>
      rintro g₁ g₂ p n i lres b p' n' i' lres' b' ⟨-, -, hn, hn', hi, -⟩
      rw [hn, hn', hi]
    case exit =>
      rintro g₁ g₂ p n i lres b p' n' i' lres' b' ⟨-, -, hn, -, -, hl, -, hi0, -, -, he, hc⟩ hg
      subst n
      simp only [decide_eq_false_iff_not, not_lt] at hg
      exact ⟨hl, he, INV_Real_mono hc (by omega)⟩
    case body =>
      equiv_seq_last 1 1 : (§p{1} = bl ∧ §p{2} = bl ∧ §n{1} = nb ∧ §n{2} = nb ∧ §i{1} = §i{2} ∧
          §lres{1} = §lres{2} ∧ §(localVarLens "b" block){1} = §(localVarLens "b" block){2} ∧
          0 < §i{1} ∧ §i{1} ≤ nb ∧ valid bl = true ∧
          FMap.dom §SLCommon.Redo.prefixes{1} (format bl §i{1}) ∧
          eInv0 §allGlobals{1} §allGlobals{2} ∧
          cntInv (k + size bl + max 0 (min (§i{1} - 1) (nb - 1))) §allGlobals{1})
      · stmt_wp
        equiv_skip
        rintro g₁ g₂ p n i lres b p' n' i' lres' b'
          ⟨⟨hp, hp', hn, hn', hi, hl, hb, hi0, hv, hdf, he, hc⟩, hg⟩
        subst n
        simp only [decide_eq_true_eq] at hg
        refine ⟨hp, hp', rfl, hn', by rw [hi], by rw [hl, hb], hb, by omega, by omega, hv, hdf hg,
          he, by simpa using hc⟩
      equiv_if
      case guard =>
        rintro g₁ g₂ p n i lres b p' n' i' lres' b' ⟨-, -, hn, hn', hi, -⟩
        rw [hn, hn', hi]
      case «else» =>
        equiv_skip
        rintro g₁ g₂ p n i lres b p' n' i' lres' b'
          ⟨⟨hp, hp', hn, hn', hi, hl, hb, hi0, hil, hv, hdf, he, hc⟩, hg⟩
        subst n
        simp only [decide_eq_false_iff_not, not_lt] at hg
        exact ⟨hp, hp', rfl, hn', hi, hl, hb, by omega, hv, fun h => absurd h (by omega), he,
          INV_Real_mono hc (by omega)⟩
      case «then» =>
        refine prhlStmt_fix_left (fun σ => (localVarLens "i" ℤ).get σ) (fun j => ?_)
        equiv_call (SS_gen (format bl (j + 1)) (size (format bl j))
          (k + size bl + max 0 (min (j - 1) (nb - 1))))
        equiv_skip
        rintro g₁ g₂ p n i lres b p' n' i' lres' b'
          ⟨⟨⟨hp, hp', hn, hn', hi, hl, hb, hi0, hil, hv, hdf, he, hc⟩, hg⟩, hj⟩
        subst p p' n i' j
        simp only [decide_eq_true_eq] at hg
        have hsz1 := size_format_pos bl (i + 1) (by omega)
        have hsz2 := size_format_pos bl i hi0
        refine ⟨⟨rfl, rfl, by omega, by omega, ?_, he, hc⟩,
          fun r₁ g₁' r₂ g₂' ⟨hr, he', hc', c, hpc⟩ => ⟨rfl, rfl, rfl, hn', rfl, hl, hr, by omega,
            hv, fun _ => by rw [FMap.domE, hpc]; simp, he', INV_Real_mono hc' (by omega)⟩⟩
        rw [take_format_succ bl i _ hi0 le_rfl, take_size]
        exact hdf
    case hpre =>
      equiv_skip
      rintro g₁ g₂ p n lres b i p' n' lres' b' i'
        ⟨hp, hp', hn, hn', hl, hl', hb, hi, hi', hv, hd, he, hc⟩
      subst i i'
      refine ⟨hp, hp', hn, hn', rfl, by rw [hl, hl'], hb, le_rfl, hv,
        fun _ => by simpa [format, nseq] using hd, he, INV_Real_mono hc (by omega)⟩

/-- `equiv_sponge`'s invariant (EC: `={Redo.prefixes, glob P, C.c} /\ C.c{1} <= max_size /\
INV_Real SLCommon.C.c{1} C.c{2} Perm.m{1} Perm.mi{1} Redo.prefixes{1}`). -/
def eInv (g₁ g₂ : VariableAssignment) : Prop :=
  eInv0 g₁ g₂ ∧ cntInv (BlockSponge.C.c.get g₁) g₁

/-- `FC` over the two squeezes keeps `eInv`: `DSqueeze_count` from the counter before `FC`'s
increment, with `C.c` framed through the call. -/
theorem FC_count :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ eInv g₁ g₂)
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app DSqueeze (Indifferentiability.DFUNCTIONALITY.mk state (List block) block
                { f := Indifferentiability.FUNCTIONALITY.f state (List block) block
                    (Module.app SLCommon.SqueezelessSponge (Indifferentiability.PRIMITIVE.view state
                      (List block) block (Module.app SLCommon.PC Perm))) })) }))).procedure
      (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
        (Module.app FC (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
              (Module.app DSqueeze (Indifferentiability.FUNCTIONALITY.view state (List block) block
                (Module.app SLCommon.SqueezelessSponge
                  (Indifferentiability.PRIMITIVE.view state (List block) block P)))) }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eInv g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DFUNCTIONALITY.f.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§bl{1} = §bl{2} ∧ §nb{1} = §nb{2} ∧ §z{1} = §z{2} ∧
      eInv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ x _ ⟨rfl, h⟩
    exact ⟨rfl, rfl, h⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ bl nb _ _ _ _ ⟨rfl, rfl, -, ⟨-, -, -, hc, -⟩, -⟩
    rw [hc]
  case «else» =>
    equiv_skip
    rintro g₁ g₂ bl nb z _ _ _ ⟨⟨rfl, rfl, rfl, h⟩, -⟩
    exact ⟨rfl, h⟩
  case «then» =>
    refine prhlStmt_fix_left (fun σ => ((localVarLens "bl" (List block)).get σ,
      (localVarLens "nb" ℤ).get σ, BlockSponge.C.c.get σ.globals)) (fun q => ?_)
    equiv_call (prhlProc_frame_of_writesKeep BlockSponge.C.c.get BlockSponge.C.c.get
      (fun c₁ c₂ => c₁ = q.2.2 + size q.1 + max (q.2.1 - 1) 0 ∧ c₂ = c₁)
      (by rw [Perm_mk]; writes_keep <;> (intro v σ; simp_reads; try trivial))
      (by rw [P_view']; writes_keep <;> (intro v σ; simp_reads; try trivial))
      (DSqueeze_count q.1 q.2.1 q.2.2))
    stmt_wp
    equiv_skip
    rintro g₁ g₂ bl nb z _ _ _ ⟨⟨⟨rfl, rfl, -, ⟨hpe, hm, hmi, hcc, hcm⟩, hc⟩, hg⟩, rfl⟩
    simp only [decide_eq_true_eq] at hg
    refine ⟨⟨⟨rfl, rfl, ?_, ?_⟩, rfl, by rw [hcc]⟩,
      fun r₁ g₁' r₂ g₂' ⟨⟨hr, he', hc'⟩, h1, h2⟩ => ⟨hr, he', ?_⟩⟩
    · simp only [eInv0]
      simp_reads
      exact ⟨hpe, hm, hmi, by rw [hcc], hg⟩
    · simp only [cntInv] at hc ⊢
      simp_reads
      exact hc
    · simp only [cntInv] at hc' ⊢
      rw [h1]
      exact hc'

/-- `PC(SLCommon.PC(P)).f ~ PC(P).f` keeps `eInv`: both counters grow by one. -/
theorem PC_f_count :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ eInv g₁ g₂)
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.PRIMITIVE.f state (List block) block
              (Module.app SLCommon.PC Perm)
            fi := Indifferentiability.PRIMITIVE.fi state (List block) block
              (Module.app SLCommon.PC Perm) }))).procedure
      (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P
            fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
              P }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eInv g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.f.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ eInv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ a _ ⟨rfl, h⟩
    exact ⟨rfl, h⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ a _ _ _ ⟨-, -, ⟨-, -, -, hc, -⟩, -⟩
    rw [hc]
  case «else» =>
    equiv_skip
    rintro g₁ g₂ a z _ _ ⟨⟨-, rfl, h⟩, -⟩
    exact ⟨rfl, h⟩
  case «then» =>
    stmt_wp
    simp only [P_f]
    stmt_inline{1} 0
    stmt_inline{2} 0
    simp only [P_f']
    stmt_inline{1} 0
    stmt_wp
    equiv_seq_last 1 1 : (§x0{1} = §x{2} ∧ §BlockSponge.C.c{1} + 1 ≤ max_size ∧
        eInv §allGlobals{1} §allGlobals{2})
    · stmt_wp
      equiv_skip
      rintro σ₁ σ₂ ⟨⟨ha, -, h⟩, hg⟩
      exact ⟨ha, by simpa using hg, h⟩
    equiv_if
    case guard =>
      rintro g₁ g₂ x0 x ⟨rfl, -, ⟨-, hm, -⟩, -⟩
      rw [hm]
    case «then» =>
      stmt_wp
      equiv_rnd
      equiv_skip
      rintro g₁ g₂ x0 x ⟨⟨rfl, hcm1, ⟨hpe, hm, hmi, hcc, hcm⟩, hc⟩, hg⟩
      refine ⟨by rw [hm], fun a ha => ⟨by rw [hm], ?_⟩⟩
      have hnd : ¬ FMap.dom (Perm.m.get g₁) x0 := by simpa using hg
      simp only [eInv, eInv0, cntInv] at hc ⊢
      simp_reads
      exact ⟨⟨hpe, by rw [hm], by rw [hmi], by rw [hcc], hcm1⟩, INV_Real_incr _ _ _ _ _
        (INV_Real_addm_mi _ _ _ _ _ _ _ hc hnd (not_of_mem_support_dexcepted ha))⟩
    case «else» =>
      equiv_skip
      rintro g₁ g₂ x0 x ⟨⟨rfl, hcm1, ⟨hpe, hm, hmi, hcc, hcm⟩, hc⟩, -⟩
      simp only [eInv, eInv0, cntInv] at hc ⊢
      simp_reads
      exact ⟨by rw [hm], ⟨hpe, hm, hmi, by rw [hcc], hcm1⟩, INV_Real_incr _ _ _ _ _ hc⟩

/-- `PC(SLCommon.PC(P)).fi ~ PC(P).fi` keeps `eInv`. -/
theorem PC_fi_count :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ eInv g₁ g₂)
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.PRIMITIVE.f state (List block) block
              (Module.app SLCommon.PC Perm)
            fi := Indifferentiability.PRIMITIVE.fi state (List block) block
              (Module.app SLCommon.PC Perm) }))).procedure
      (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
        (Module.app PC (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
          { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P
            fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
              P }))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ eInv g₁ g₂) := by
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [Indifferentiability.DPRIMITIVE.fi.mk_simp]
  stmt_wp
  equiv_seq_last 1 1 : (§a{1} = §a{2} ∧ §z{1} = §z{2} ∧ eInv §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    rintro g₁ g₂ a _ ⟨rfl, h⟩
    exact ⟨rfl, h⟩
  equiv_if
  case guard =>
    rintro g₁ g₂ a _ _ _ ⟨-, -, ⟨-, -, -, hc, -⟩, -⟩
    rw [hc]
  case «else» =>
    equiv_skip
    rintro g₁ g₂ a z _ _ ⟨⟨-, rfl, h⟩, -⟩
    exact ⟨rfl, h⟩
  case «then» =>
    stmt_wp
    simp only [P_fi]
    stmt_inline{1} 0
    stmt_inline{2} 0
    simp only [P_fi']
    stmt_inline{1} 0
    stmt_wp
    equiv_seq_last 1 1 : (§y0{1} = §y{2} ∧ §BlockSponge.C.c{1} + 1 ≤ max_size ∧
        eInv §allGlobals{1} §allGlobals{2})
    · stmt_wp
      equiv_skip
      rintro σ₁ σ₂ ⟨⟨ha, -, h⟩, hg⟩
      exact ⟨ha, by simpa using hg, h⟩
    equiv_if
    case guard =>
      rintro g₁ g₂ y0 y ⟨rfl, -, ⟨-, -, hmi, -⟩, -⟩
      rw [hmi]
    case «then» =>
      stmt_wp
      equiv_rnd
      equiv_skip
      rintro g₁ g₂ y0 y ⟨⟨rfl, hcm1, ⟨hpe, hm, hmi, hcc, hcm⟩, hc⟩, hg⟩
      refine ⟨by rw [hmi], fun a ha => ⟨by rw [hmi], ?_⟩⟩
      have hnd : ¬ FMap.dom (Perm.mi.get g₁) y0 := by simpa using hg
      simp only [eInv, eInv0, cntInv] at hc ⊢
      simp_reads
      have hinvm : invm (Perm.m.get g₁) (Perm.mi.get g₁) := by obtain ⟨-, -, h⟩ := hc; exact h
      refine ⟨⟨hpe, by rw [hm], by rw [hmi], by rw [hcc], hcm1⟩, INV_Real_incr _ _ _ _ _
        (INV_Real_addm_mi _ _ _ _ _ _ _ hc ?_ ?_)⟩
      · rw [invm_dom_rng _ _ hinvm]
        exact not_of_mem_support_dexcepted ha
      · rw [← invm_dom_rng _ _ (invmC' _ _ hinvm)]
        exact hnd
    case «else» =>
      equiv_skip
      rintro g₁ g₂ y0 y ⟨⟨rfl, hcm1, ⟨hpe, hm, hmi, hcc, hcm⟩, hc⟩, -⟩
      simp only [eInv, eInv0, cntInv] at hc ⊢
      simp_reads
      exact ⟨by rw [hmi], ⟨hpe, hm, hmi, by rw [hcc], hcm1⟩, INV_Real_incr _ _ _ _ _ hc⟩

omit [BlockSponge.Params] [Params] in
/-- `P.init`, at `SLCommon`'s `PRIMITIVE`, is `Perm.init`. -/
theorem P_init' : Indifferentiability.PRIMITIVE.init state (List block) block P =
    PRP.RP.RP.init (block × capacity) dD Perm.m Perm.mi := by
  unfold P Perm PRP.RP.RP
  simp [Indifferentiability.PRIMITIVE.init, PRP.StrongPRP.PRP.mk]

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
  have hm : (Perm.m).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_sub)))
  have hmi : (Perm.mi).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_sub)))
  have hpr : (SLCommon.Redo.prefixes).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_sub)))
  have hcc : (BlockSponge.C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono (by fp_sub)))
  have hsC : SLCommon.C.footprint ≤ (FVP.fvP D)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (_hDd.trans (Footprint.compl_antimono le_sup_right))
  have hsc : (SLCommon.C.c).footprint ≤ (FVP.fvP D)ᶜ :=
    le_trans (by unfold SLCommon.C.footprint; exact le_sup_left) hsC
  have hsq : (SLCommon.C.queries).footprint ≤ (FVP.fvP D)ᶜ :=
    le_trans (by unfold SLCommon.C.footprint; exact le_sup_right) hsC
  let Lg := Lens.pair Perm.m (Lens.pair Perm.mi (Lens.pair SLCommon.Redo.prefixes
    (Lens.pair BlockSponge.C.c SLCommon.C.c)))
  let I : FMap state state × FMap state state × FMap (List block) state × ℤ × ℤ →
      FMap state state × FMap state state × FMap (List block) state × ℤ × ℤ → Prop := fun x y =>
    (x.2.2.1 = y.2.2.1 ∧ x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧
      x.2.2.2.1 ≤ max_size) ∧ INV_Real x.2.2.2.2 x.2.2.2.1 x.1 x.2.1 x.2.2.1
  have hI : ∀ g₁ g₂, I (Lg.get g₁) (Lg.get g₂) ↔ eInv g₁ g₂ := fun _ _ => Iff.rfl
  have hL : FVP.fvP D ≤ (Lg.footprint)ᶜ := by
    refine (Footprint.le_compl_comm _ _).mpr ?_
    simp only [Lg, Footprint.lens_pair]
    exact sup_le hm (sup_le hmi (sup_le hpr (sup_le hcc hsc)))
  unfold SLCommon.GReal SLCommon.RealIndif Indifferentiability.GReal
  equiv_proc_to_stmt
  stmt_inline{1} 0
  stmt_inline{2} 0
  simp only [P_init, Squeeze, Indifferentiability.FUNCTIONALITY.init.mk_simp]
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  simp only [P_init']
  repeat stmt_inline{1} 0
  stmt_wp
  equiv_seq_last 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
  · stmt_wp
    equiv_skip
    intro g₁ g₂ h
    refine ⟨?_, (hI _ _).mpr ?_⟩
    · simp only [touched_set_of_le_compl hm, touched_set_of_le_compl hmi,
        touched_set_of_le_compl hpr, touched_set_of_le_compl hcc, touched_set_of_le_compl hsc,
        touched_set_of_le_compl hsq]
      exact h
    · simp only [eInv, eInv0, cntInv]
      simp_reads
      exact ⟨SLCommon.max_ge0, INV_Real_init⟩
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
          Module.fst_pair, Module.snd_pair, Indifferentiability.DFUNCTIONALITY.f.mk_simp,
          Indifferentiability.FUNCTIONALITY.f.mk_simp]
        exact prhlProc_globInvF_of_writesKeep _ (by rw [Perm_mk]; writes_keep')
          (by rw [P_view']; writes_keep')
          (prhlProc_conseq FC_count (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
            (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
      | succ n => cases n with
        | zero =>
          simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
            HoleSigs.Instantiation.lookup_zero_cons, Module.fst_pair, Module.snd_pair,
            Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
          exact prhlProc_globInvF_of_writesKeep _ (by rw [Perm_mk]; writes_keep')
            (by rw [P_f, P_fi]; writes_keep')
            (prhlProc_conseq PC_f_count (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
              (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
        | succ n => cases n with
          | zero =>
            simp only [Indifferentiability.distExt, HoleSigs.Instantiation.lookup_succ,
              HoleSigs.Instantiation.lookup_zero_single, Module.fst_pair, Module.snd_pair,
              Indifferentiability.DPRIMITIVE.f.mk_simp, Indifferentiability.DPRIMITIVE.fi.mk_simp]
            exact prhlProc_globInvF_of_writesKeep _ (by rw [Perm_mk]; writes_keep')
              (by rw [P_f, P_fi]; writes_keep')
              (prhlProc_conseq PC_fi_count (fun _ _ _ _ h => ⟨h.1, (hI _ _).mp h.2⟩)
                (fun _ _ _ _ h => ⟨h.1, (hI _ _).mpr h.2⟩))
          | succ n => nomatch n
    equiv_skip
    intro σ₁ σ₂ h
    refine ⟨⟨rfl, h⟩, ?_⟩
    rintro r g₁ _ g₂ ⟨rfl, hg, hI'⟩
    obtain ⟨⟨hpe, hm', hmi', hcc', hcm⟩, hc⟩ := (hI _ _).mp hI'
    obtain ⟨hle, -, -⟩ := hc
    simp_reads
    exact ⟨hg, hm', hmi', hcc', hcc' ▸ hle, hcc' ▸ hcm⟩

/-- EC's `pr_real`, for `D <: DISTINGUISHER {-SLCommon.C, -C, -Perm, -Redo}`. -/
theorem pr_real (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : FVP.fvP D ≤ ((Perm.m).footprint ⊔ (Perm.mi).footprint ⊔
      (SLCommon.Redo.prefixes).footprint ⊔ BlockSponge.C.c.footprint ⊔ SLCommon.C.footprint)ᶜ)
    (m : VariableAssignment) :
    Procedure.Pr (SLCommon.GReal (A D)).procedure () m
        (fun r g => r = true ∧ SLCommon.C.c.get g ≤ max_size) =
      Procedure.Pr (RealIndif Sponge P (DRestr D)).procedure () m (fun r _ => r = true) := by
  -- EC: `rewrite (byequiv (squeeze_squeezeless D)); byequiv (equiv_sponge D)`
  have e1 := Procedure.Pr_eq_of_prhlProc (equiv_sponge D hD _hDd)
    (E₁ := fun r g => r = true ∧ SLCommon.C.c.get g ≤ max_size)
    (E₂ := fun r g => r = true ∧ BlockSponge.C.c.get g ≤ max_size)
    (fun r₁ g₁ r₂ g₂ ⟨hr, _, _, _, _, h1, h2⟩ => by
      subst hr
      exact ⟨fun ⟨h, _⟩ => ⟨h, h2⟩, fun ⟨h, _⟩ => ⟨h, h1.trans h2⟩⟩)
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl
  have e2 := Procedure.Pr_eq_of_prhlProc (squeeze_squeezeless D hD _hDd)
    (E₁ := fun r g => r = true ∧ BlockSponge.C.c.get g ≤ max_size)
    (E₂ := fun r _ => r = true)
    (fun r₁ g₁ r₂ g₂ ⟨hr, _, _, _, _, h1⟩ => by
      subst hr
      exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, h1⟩⟩)
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl
  rw [e1, e2]

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

omit [BlockSponge.Params] [Params] in
/-- `P.f` is lossless (`ConcreteF.Perm_f_ll`: `Perm.m` misses the queried key, so its range misses
a value).  Not an EC lemma. -/
theorem P_f_ll :
    (Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P).procedure.IsLossless :=
  ConcreteF.Perm_f_ll

omit [BlockSponge.Params] [Params] in
/-- `P.fi` is lossless (`ConcreteF.Perm_fi_ll`).  Not an EC lemma. -/
theorem P_fi_ll :
    (Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block) P).procedure.IsLossless :=
  ConcreteF.Perm_fi_ll

omit [BlockSponge.Params] [Params] in
/-- `Sponge` has no globals.  Not an EC lemma. -/
@[fp_bound] theorem fvP_Sponge : FVP.fvP Sponge ≤ ⊥ := by
  fp_module

omit [Params] in
/-- `Sponge(P).f` is lossless when `P.f` is: both loops are counted (variants `size xs` and
`n - i`).  Not an EC lemma (EC: the two `while` in `Real_lossless`). -/
theorem Sponge_f_ll (P0 : DPRIMITIVE)
    (hP : (Indifferentiability.DPRIMITIVE.f state (List block × ℤ) (List block)
      P0).procedure.IsLossless) :
    (Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
      (Module.app Sponge P0)).procedure.IsLossless := by
  rw [Procedure.isLossless_iff_phoareProc] at hP ⊢
  refine phoareProc_eq_of_le_ge (fun _ _ _ => Procedure.ewp_const_le _ _ _ _) ?_
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_wp 1
  phoare_split 1
  refine phoareStmt_seq_ge_one ?_ ?_
  · refine phoareStmt_if_ge ?_ ?_
    · phoare_split 1
      refine phoareStmt_seq_ge_one ?_ ?_
      · phoare_while_ge 1 variant (§n - §i).toNat
        case body =>
          phoare_wp 3
          phoare_simp [hP]
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
        phoare_skip
        intros; exact le_rfl
      · phoare_while_ge 1 variant (§xs).length
        case body =>
          phoare_wp 2
          phoare_simp [hP]
          phoare_skip
          intros
          simp
        case exit => trivial
        case decreases =>
          intro k
          hoare_wp 1
          hoare_call
          hoare_skip
          rintro (_ | ⟨b, xs⟩) ⟨hne, rfl⟩ _ _
          · simp at hne
          · simp [behead]
        phoare_skip
        intros; exact le_rfl
    · phoare_skip
      intros; exact le_rfl
  · phoare_wp 6
    phoare_skip
    intros; exact le_rfl

/-! ## The section `Real_Ideal` -/

section Real_Ideal

omit [BlockSponge.Params] [Params] in
/-- Every `SLCommon` distinguisher is representable over `F.f`, `P.f`, `P.fi`
(`Module.representable_of_firstOrder`).  Not an EC lemma. -/
theorem SLDistinguisher_representable (D : SLCommon.DISTINGUISHER) :
    Module.Representable D SLCommon.distExt := by
  refine Module.representable_of_firstOrder ?_ ?_ SLCommon.distExt (fun _ => rfl) D
  · simp [IsModule.moduleTypeRep, ModuleTypeRep.FirstOrder, Module.moduleTypeRep,
      Indifferentiability.DFUNCTIONALITY.typeRep, Indifferentiability.DPRIMITIVE.typeRep]
  · intro sig n
    cases n with
    | zero => exact ⟨fun U hU => by simp at hU; subst hU; exact ⟨[]⟩, inferInstance⟩
    | succ n => cases n with
      | zero => exact ⟨fun U hU => by simp at hU; subst hU; infer_instance, inferInstance⟩
      | succ n => cases n with
        | zero => exact ⟨fun U hU => by simp at hU; subst hU; infer_instance, inferInstance⟩
        | succ n => nomatch n

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

omit [SLCommon.Params] [BlockSponge.Params] [Params] in
/-- A variable outside a finitely supported footprint is outside its `glob`. -/
theorem le_compl_glob_of_le_compl {F : Footprint VariableAssignment} (hF : F.FinitelySupported)
    {T : Type} (X : Lens T VariableAssignment) (v : VariableName)
    (hX : X.footprint = (varLens v).footprint)
    (h : X.footprint ≤ Fᶜ) : X.footprint ≤ F.globᶜ := by
  rw [hX] at h ⊢
  exact (Footprint.le_compl_comm _ _).mp
    (hF.glob_le_compl_varLens v ((Footprint.le_compl_comm _ _).mp h))

/-- `Gconcl.Gext0Fresh` at `BlockSponge`'s `DISTINGUISHER`: the variables of `Gconcl`'s
`local clone import Gext as Gext0` lie outside `D` (exception E13). -/
def Gext0Fresh (D : DISTINGUISHER) : Prop :=
  FVP.fvP D ≤ ((ConcreteF.PF.m).footprint ⊔ (ConcreteF.PF.mi).footprint ⊔ (G1.m).footprint ⊔
    (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔ G1.chandle.footprint ⊔
    (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔ (Handle.FRO.m).footprint ⊔
    (ROhandle.RO.m).footprint)ᶜ

/-- `D_lossless` over a region `G` the oracles stay out of; `D_lossless D` is the case
`G := glob D` (exception E14). -/
def D_lossless_at (D : DISTINGUISHER) (G : Footprint VariableAssignment) : Prop :=
  ∀ (F0 : DFUNCTIONALITY) (P0 : DPRIMITIVE), FVP.fvP F0 ≤ Gᶜ → FVP.fvP P0 ≤ Gᶜ →
    (Indifferentiability.DPRIMITIVE.f state (List block × ℤ) (List block) P0).procedure.IsLossless →
    (Indifferentiability.DPRIMITIVE.fi state (List block × ℤ) (List block)
      P0).procedure.IsLossless →
    (Indifferentiability.DFUNCTIONALITY.f state (List block × ℤ) (List block)
      F0).procedure.IsLossless →
    (Module.app D (Module.pair F0 P0)).procedure.IsLossless

/-- A region `G` outside the variables of `DRestrictions_Real_Ideal` (exception E14): the
variables of the games of `Real_Ideal`, which their oracles touch (an abbreviation). -/
def RealIdealRegion (G : Footprint VariableAssignment) : Prop :=
  G ≤ ((Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ (SLCommon.F.RO.m).footprint ⊔
    (SLCommon.F.FRO.m).footprint ⊔ (SLCommon.Redo.prefixes).footprint ⊔ SLCommon.C.footprint ⊔
    (Gconcl.S.m).footprint ⊔ (Gconcl.S.mi).footprint ⊔ (Gconcl.S.paths).footprint ⊔
    (BlockSponge.BIRO.IRO.mp).footprint ⊔ BlockSponge.C.c.footprint ⊔ (BIRO2.IRO.mp).footprint ⊔
    (F2.RO.m).footprint ⊔ (F2.FRO.m).footprint)ᶜ

/-- EC's `A_lossless` over a region `G` outside `C.c` (exception E14). -/
theorem A_lossless_at (D : DISTINGUISHER) (G : Footprint VariableAssignment)
    (hGc : (BlockSponge.C.c).footprint ≤ Gᶜ) :
    D_lossless_at D G →
    ∀ (F : SLCommon.DFUNCTIONALITY) (P0 : SLCommon.DPRIMITIVE),
      FVP.fvP F ≤ ((BlockSponge.C.c).footprint ⊔ G)ᶜ →
      FVP.fvP P0 ≤ ((BlockSponge.C.c).footprint ⊔ G)ᶜ →
      (Indifferentiability.DPRIMITIVE.f state (List block) block P0).procedure.IsLossless →
      (Indifferentiability.DPRIMITIVE.fi state (List block) block P0).procedure.IsLossless →
      (Indifferentiability.DFUNCTIONALITY.f state (List block) block F).procedure.IsLossless →
      (Module.app (A D) (Module.pair F P0)).procedure.IsLossless := by
  intro D_ll F P0 hF hP p_ll pi_ll f_ll
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
  intro D_ll
  unfold DRestrictions_Real_Ideal at _hDd
  exact A_lossless_at D _ (le_compl_glob_of_le_compl hD.finitelySupported _ _ rfl (by fp_disjoint))
    D_ll

/-- EC's `concl`, for `D_ll` over a region `G` (exception E14): `Real_Ideal` applied to `A(D)`,
whose `D_ll` is `A_lossless_at` over `C.c ⊔ G`. -/
theorem concl_at (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (_hG : Gext0Fresh D) (G : Footprint VariableAssignment)
    (hGc : (BlockSponge.C.c).footprint ≤ Gᶜ)
    (hGX : G ≤ (SLCommon.C.footprint ⊔
      (ConcreteF.PF.m).footprint ⊔ (ConcreteF.PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ (SLCommon.F.RO.m).footprint ⊔
      (SLCommon.Redo.prefixes).footprint ⊔ (Handle.FRO.m).footprint ⊔
      (ROhandle.RO.m).footprint)ᶜ)
    (GF : Footprint VariableAssignment) (hGF : GF.FinitelySupported) (hGGF : G ≤ GF.glob)
    (D_ll : D_lossless_at D G) (m : VariableAssignment) :
    (Procedure.Pr (RealIndif Sponge P (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) ≤
      (Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S)
        (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) + bound := by
  have hA := fvP_A D
  have hAm : Module.ECModule (A D) SLCommon.distExt :=
    ⟨SLDistinguisher_representable (A D), (hD.finitelySupported.sup (.varLens _)).mono hA⟩
  unfold DRestrictions_Real_Ideal at _hDd
  unfold Gext0Fresh at _hG
  have hR : Gconcl.DRestrictions (A D) := by
    unfold Gconcl.DRestrictions
    exact hA.trans (sup_le (_hDd.trans (Footprint.compl_antimono (by fp_sub))) (by fp_disjoint))
  have hGA : Gconcl.Gext0Fresh (A D) := by
    unfold Gconcl.Gext0Fresh
    exact hA.trans (sup_le _hG (by fp_disjoint))
  have h := Gconcl.Real_Ideal (A D) hAm hR hGA (BlockSponge.C.c.footprint ⊔ G)
    (sup_le (by fp_disjoint) hGX) (BlockSponge.C.c.footprint ⊔ GF)
    ((Footprint.FinitelySupported.globalVar _).sup hGF)
    (sup_le (Footprint.le_glob_of_le le_sup_left) (hGGF.trans (Footprint.glob_mono le_sup_right)))
    (A_lossless_at D G hGc D_ll) m
  have e1 := pr_real D hD (_hDd.trans (Footprint.compl_antimono (by fp_sub))) m
  have e2 := equiv_ideal D hD ⟨_hDd.trans (Footprint.compl_antimono (by fp_sub)),
    _hDd.trans (Footprint.compl_antimono (by fp_sub))⟩
    (_hDd.trans (Footprint.compl_antimono (by fp_sub))) m
  rw [← e1, ← e2]
  rw [dstate1E_toReal] at h
  refine h.trans (le_of_eq ?_)
  unfold bound
  ring

/-- `glob D` lies outside the variables `concl_at` needs. -/
theorem glob_hyps (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (_hG : Gext0Fresh D) :
    (BlockSponge.C.c).footprint ≤ (FVP.fvP D).globᶜ ∧
      (FVP.fvP D).glob ≤ (SLCommon.C.footprint ⊔
      (ConcreteF.PF.m).footprint ⊔ (ConcreteF.PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ (SLCommon.F.RO.m).footprint ⊔
      (SLCommon.Redo.prefixes).footprint ⊔ (Handle.FRO.m).footprint ⊔
      (ROhandle.RO.m).footprint)ᶜ := by
  unfold DRestrictions_Real_Ideal at _hDd
  unfold Gext0Fresh at _hG
  refine ⟨le_compl_glob_of_le_compl hD.finitelySupported _ _ rfl (by fp_disjoint), ?_⟩
  refine (Footprint.le_compl_comm _ _).mp ?_
  unfold SLCommon.C.footprint
  repeat' refine sup_le ?_ ?_
  all_goals exact le_compl_glob_of_le_compl hD.finitelySupported _ _ rfl (by fp_disjoint)

/-- `glob D` is a `RealIdealRegion`. -/
theorem glob_RealIdealRegion (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) : RealIdealRegion (FVP.fvP D).glob := by
  unfold DRestrictions_Real_Ideal at _hDd
  unfold RealIdealRegion
  refine (Footprint.le_compl_comm _ _).mp ?_
  unfold SLCommon.C.footprint
  repeat' refine sup_le ?_ ?_
  all_goals exact le_compl_glob_of_le_compl hD.finitelySupported _ _ rfl (by fp_disjoint)

/-- EC's `concl`, with `Gext0Fresh` (exception E13). -/
theorem concl (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (_hG : Gext0Fresh D) :
    D_lossless D → ∀ m : VariableAssignment,
      (Procedure.Pr (RealIndif Sponge P (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) ≤
        (Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S)
          (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) + bound := by
  intro D_ll m
  exact concl_at D hD _hDd _hG _ (glob_hyps D hD _hDd _hG).1 (glob_hyps D hD _hDd _hG).2
    (FVP.fvP D) hD.finitelySupported le_rfl D_ll m

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

/-- EC's local `Neg_D_lossless` over a region `G` (exception E14). -/
theorem Neg_D_lossless_at (D : DISTINGUISHER) (G : Footprint VariableAssignment)
    (D_ll : D_lossless_at D G) (F : DFUNCTIONALITY) (P0 : DPRIMITIVE)
    (hF : FVP.fvP F ≤ Gᶜ) (hP : FVP.fvP P0 ≤ Gᶜ) :
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
    (Module.app (Neg_D D) (Module.pair F P0)).procedure.IsLossless :=
  Neg_D_lossless_at D _ D_ll F P0 hF hP

theorem useful (m mi : FMap state state) (a : state) :
    invm m mi → ¬ FMap.dom m a → is_lossless (dexcepted (dprod bdistr cdistr) (FMap.rng m)) :=
  fun _ h => EC.Strong_RP_RF.excepted_lossless state SLCommon.dstate ConcreteF.Switching.uD_uf_fu m
    ⟨a, h⟩

theorem invmC (m mi : FMap state state) : invm m mi ↔ invm mi m :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

/-- EC's local `Real_lossless`, `D_ll` over a region `G` (exception E14).  EC calls `D` under the
invariant `invm Perm.m Perm.mi`, which it needs for `useful` (losslessness of the excepted
sampling).  Here `D_ll` is applied directly: `Perm.f`/`Perm.fi` are lossless in every state
(`P_f_ll`/`P_fi_ll`, a finite map missing a key misses a value), so no invariant is needed. -/
theorem Real_lossless_at (D : DISTINGUISHER) (_hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (G : Footprint VariableAssignment)
    (hG : RealIdealRegion G) (D_ll : D_lossless_at D G) :
    (RealIndif Sponge P (DRestr (Neg_D D))).procedure.IsLossless := by
  unfold RealIdealRegion at hG
  rw [Procedure.isLossless_iff_phoareProc]
  phoare_proc_to_stmt
  unfold RealIndif Indifferentiability.GReal
  phoare_inline 0
  simp only [P_init]
  repeat phoare_inline 0
  have hv : (Indifferentiability.DPRIMITIVE.f state (List block × ℤ) (List block)
      (Indifferentiability.PRIMITIVE.view state (List block × ℤ) (List block)
        P)).procedure.IsLossless := by
    rw [Indifferentiability.PRIMITIVE.view_f]; exact P_f_ll
  have hS : (Indifferentiability.DFUNCTIONALITY.f state (List block × ℤ) (List block)
      (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
            (Module.app Sponge (Indifferentiability.PRIMITIVE.view state (List block × ℤ)
              (List block) P)) })).procedure.IsLossless := by
    simpa only [Indifferentiability.DFUNCTIONALITY.f.mk_simp] using Sponge_f_ll _ hv
  have hPm : (Indifferentiability.DPRIMITIVE.f state (List block × ℤ) (List block)
      (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P,
          fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
            P })).procedure.IsLossless := by
    simpa only [Indifferentiability.DPRIMITIVE.f.mk_simp] using P_f_ll
  have hPmi : (Indifferentiability.DPRIMITIVE.fi state (List block × ℤ) (List block)
      (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
        { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P,
          fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
            P })).procedure.IsLossless := by
    simpa only [Indifferentiability.DPRIMITIVE.fi.mk_simp] using P_fi_ll
  have hll := D_ll
    (Indifferentiability.DFUNCTIONALITY.mk state (List block × ℤ) (List block)
      { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
          (Module.app BlockSponge.FC (Indifferentiability.DFUNCTIONALITY.mk state
            (List block × ℤ) (List block)
            { f := Indifferentiability.FUNCTIONALITY.f state (List block × ℤ) (List block)
                (Module.app Sponge (Indifferentiability.PRIMITIVE.view state (List block × ℤ)
                  (List block) P)) })) })
    (Indifferentiability.DPRIMITIVE.mk state (List block × ℤ) (List block)
      { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block)
          (Module.app BlockSponge.PC (Indifferentiability.DPRIMITIVE.mk state
            (List block × ℤ) (List block)
            { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P,
              fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block) P })),
        fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block)
          (Module.app BlockSponge.PC (Indifferentiability.DPRIMITIVE.mk state
            (List block × ℤ) (List block)
            { f := Indifferentiability.PRIMITIVE.f state (List block × ℤ) (List block) P,
              fi := Indifferentiability.PRIMITIVE.fi state (List block × ℤ) (List block) P })) })
    (by fp_disjoint) (by fp_disjoint)
    (by simpa only [Indifferentiability.DPRIMITIVE.f.mk_simp] using PC_f_ll _ hPm)
    (by simpa only [Indifferentiability.DPRIMITIVE.fi.mk_simp] using PC_fi_ll _ hPmi)
    (by simpa only [Indifferentiability.DFUNCTIONALITY.f.mk_simp] using FC_f_ll _ hS)
  rw [Procedure.isLossless_iff_phoareProc] at hll
  phoare_wp 20
  phoare_simp [hll]
  phoare_skip
  simp

/-- EC's local `Real_lossless`. -/
theorem Real_lossless (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (D_ll : D_lossless D) :
    (RealIndif Sponge P (DRestr (Neg_D D))).procedure.IsLossless :=
  Real_lossless_at D hD _hDd _ (glob_RealIdealRegion D hD _hDd) D_ll

/-- EC's local `Ideal_lossless`, `D_ll` over a region `G` (exception E14). -/
theorem Ideal_lossless_at (D : DISTINGUISHER) (G : Footprint VariableAssignment)
    (hG : RealIdealRegion G) (D_ll : D_lossless_at D G) :
    (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S)
      (DRestr (Neg_D D))).procedure.IsLossless := by
  unfold RealIdealRegion at hG
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

/-- EC's local `Ideal_lossless`. -/
theorem Ideal_lossless (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (D_ll : D_lossless D) :
    (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S)
      (DRestr (Neg_D D))).procedure.IsLossless :=
  Ideal_lossless_at D _ (glob_RealIdealRegion D hD _hDd) D_ll

omit [BlockSponge.Params] [Params] in
/-- Every distinguisher is representable over `F.f`, `P.f`, `P.fi`.  Not an EC lemma. -/
theorem Distinguisher_representable (D : DISTINGUISHER) : Module.Representable D distExt := by
  refine Module.representable_of_firstOrder ?_ ?_ distExt (fun _ => rfl) D
  · simp [IsModule.moduleTypeRep, ModuleTypeRep.FirstOrder, Module.moduleTypeRep,
      Indifferentiability.DFUNCTIONALITY.typeRep, Indifferentiability.DPRIMITIVE.typeRep]
  · intro sig n
    cases n with
    | zero => exact ⟨fun U hU => by simp at hU; subst hU; exact ⟨([], 0)⟩, ⟨[]⟩⟩
    | succ n => cases n with
      | zero => exact ⟨fun U hU => by simp at hU; subst hU; infer_instance, inferInstance⟩
      | succ n => cases n with
        | zero => exact ⟨fun U hU => by simp at hU; subst hU; infer_instance, inferInstance⟩
        | succ n => nomatch n

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

/-- EC's local `neg_D_concl`, with `Gext0Fresh` (exception E13), `D_ll` over a region `G`
(exception E14): `concl_at` for `Neg_D(D)`, and both games lossless. -/
theorem neg_D_concl_at (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (_hG : Gext0Fresh D)
    (G : Footprint VariableAssignment) (hGc : (BlockSponge.C.c).footprint ≤ Gᶜ)
    (hGX : G ≤ (SLCommon.C.footprint ⊔
      (ConcreteF.PF.m).footprint ⊔ (ConcreteF.PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ (SLCommon.F.RO.m).footprint ⊔
      (SLCommon.Redo.prefixes).footprint ⊔ (Handle.FRO.m).footprint ⊔
      (ROhandle.RO.m).footprint)ᶜ)
    (GF : Footprint VariableAssignment) (hGF : GF.FinitelySupported) (hGGF : G ≤ GF.glob)
    (hRI : RealIdealRegion G)
    (_D_lossless : D_lossless_at D G) (m : VariableAssignment) :
    (Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S) (DRestr D)).procedure ()
        m (fun r _ => r = true) : ℝ) ≤
      (Procedure.Pr (RealIndif Sponge P (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) +
        bound := by
  have hN := fvP_Neg_D D
  have hNm : Module.ECModule (Real_Ideal_Abs.Neg_D D) distExt :=
    ⟨Distinguisher_representable _, hD.finitelySupported.mono hN⟩
  have hNd : DRestrictions_Real_Ideal (Real_Ideal_Abs.Neg_D D) := hN.trans _hDd
  have hNg : Gext0Fresh (Real_Ideal_Abs.Neg_D D) := hN.trans _hG
  have hc := concl_at (Real_Ideal_Abs.Neg_D D) hNm hNd hNg G hGc hGX GF hGF hGGF
    (fun F0 P0 hF hP => Real_Ideal_Abs.Neg_D_lossless_at D G _D_lossless F0 P0 hF hP) m
  have eI := Procedure.Pr_eq_of_prhlProc (Indif_Neg_D BlockSponge.BIRO.IRO.asF
    (Module.app (SimLast Gconcl.S) (Indifferentiability.FUNCTIONALITY.view state
      (List block × ℤ) (List block) BlockSponge.BIRO.IRO.asF)) D)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = false)
    (fun r₁ _ r₂ _ h => by subst h; cases r₂ <;> simp) (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl
  have eR := Procedure.Pr_eq_of_prhlProc (Indif_Neg_D (Module.app Sponge
    (Indifferentiability.PRIMITIVE.view state (List block × ℤ) (List block) P)) P D)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = false)
    (fun r₁ _ r₂ _ h => by subst h; cases r₂ <;> simp) (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl
  have lI := Pr_false_eq_one_sub (Real_Ideal_Abs.Ideal_lossless_at D G hRI _D_lossless) m
  have lR := Pr_false_eq_one_sub (Real_Ideal_Abs.Real_lossless_at D hD _hDd G hRI _D_lossless) m
  unfold IdealIndif Indifferentiability.GIdeal at hc lI ⊢
  unfold RealIndif Indifferentiability.GReal at hc lR ⊢
  rw [eI, lI]
  rw [eR, lR]
  linarith

/-- EC's local `neg_D_concl`, with `Gext0Fresh` (exception E13): `neg_D_concl_at` over `glob D`
(exception E14). -/
theorem neg_D_concl (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (_hG : Gext0Fresh D) (_D_lossless : D_lossless D)
    (m : VariableAssignment) :
    (Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S) (DRestr D)).procedure ()
        m (fun r _ => r = true) : ℝ) ≤
      (Procedure.Pr (RealIndif Sponge P (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) +
        bound :=
  neg_D_concl_at D hD _hDd _hG _ (glob_hyps D hD _hDd _hG).1 (glob_hyps D hD _hDd _hG).2
    (FVP.fvP D) hD.finitelySupported le_rfl (glob_RealIdealRegion D hD _hDd) _D_lossless m

end Real_Ideal_Abs

/-- EC's `Inefficient_Real_Ideal`, `D_ll` over a region `G` (exception E14). -/
theorem Inefficient_Real_Ideal_at (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (_hG : Gext0Fresh D)
    (G : Footprint VariableAssignment) (hGc : (BlockSponge.C.c).footprint ≤ Gᶜ)
    (hGX : G ≤ (SLCommon.C.footprint ⊔
      (ConcreteF.PF.m).footprint ⊔ (ConcreteF.PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ (SLCommon.F.RO.m).footprint ⊔
      (SLCommon.Redo.prefixes).footprint ⊔ (Handle.FRO.m).footprint ⊔
      (ROhandle.RO.m).footprint)ᶜ)
    (GF : Footprint VariableAssignment) (hGF : GF.FinitelySupported) (hGGF : G ≤ GF.glob)
    (hRI : RealIdealRegion G)
    (D_ll : D_lossless_at D G) (m : VariableAssignment) :
      |(Procedure.Pr (RealIndif Sponge Perm (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) -
        (Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S)
          (DRestr D)).procedure () m (fun r _ => r = true) : ℝ)| ≤ bound := by
  have h1 := concl_at D hD _hDd _hG G hGc hGX GF hGF hGGF D_ll m
  have h2 := Real_Ideal_Abs.neg_D_concl_at D hD _hDd _hG G hGc hGX GF hGF hGGF hRI D_ll m
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- EC's `Inefficient_Real_Ideal`. -/
theorem Inefficient_Real_Ideal (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (_hG : Gext0Fresh D) :
    D_lossless D → ∀ m : VariableAssignment,
      |(Procedure.Pr (RealIndif Sponge Perm (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) -
        (Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S)
          (DRestr D)).procedure () m (fun r _ => r = true) : ℝ)| ≤ bound := fun D_ll m =>
  Inefficient_Real_Ideal_at D hD _hDd _hG _ (glob_hyps D hD _hDd _hG).1 (glob_hyps D hD _hDd _hG).2
    (FVP.fvP D) hD.finitelySupported le_rfl (glob_RealIdealRegion D hD _hDd) D_ll m

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
        (Module.app Simu (Module.pair (IRO2.LRO IRO2_RO_m)
          (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
            BlockSponge.BIRO.IRO.asF)))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ e2Inv IRO2_RO_m g₁ g₂) := by
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§x0{1} = §x0{2} ∧ e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
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
      equiv_seq_last 5 5 : (§x0{1} = §x0{2} ∧ §y1{1} = §y1{2} ∧
        e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
      · equiv_if
        case guard => e2_close
        case «else» =>
          equiv_rnd
          equiv_skip
          e2_close
        case «then» =>
          equiv_seq_last 1 1 : (§x0{1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧
            e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
          · stmt_wp
            equiv_skip
            e2_close
          · equiv_if
            case guard => e2_close
            case «then» =>
              stmt_wp
              equiv_seq_last 1 1 : (§x1{1} = §x1{2} ∧ §n{1} = §n{2} ∧ §i{1} = §i0{2} ∧ §bs{1} = §bs{2} ∧
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
                  equiv_while_raw (§x1{1} = §x1{2} ∧ §n{1} = §n{2} ∧ §i{1} = §i0{2} ∧ §bs{1} = §bs{2} ∧
                    §x0{1} = §x0{2} ∧ e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
                  case body =>
                    stmt_wp
                    equiv_seq_last 1 1 : (§x2{1} = §x2{2} ∧ §n0{1} = §n0{2} ∧ §x2{1} = §x1{1} ∧
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
                equiv_seq_last 1 3 : (§x0{1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧ 0 < §k{1} ∧
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
        (Module.app Simu (Module.pair (IRO2.LRO IRO2_RO_m)
          (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
            BlockSponge.BIRO.IRO.asF)))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ e2Inv IRO2_RO_m g₁ g₂) := by
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§x0{1} = §x0{2} ∧ e2Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
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
      (Module.app (L D) (IRO2.LRO IRO2_RO_m)).procedure
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
  unfold IdealIndif Indifferentiability.GIdeal
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
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
        (Module.app Simu (Module.pair (IRO2.RO.asRO IRO2_RO_m)
          (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
            BlockSponge.BIRO.IRO.asF)))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ e1Inv IRO2_RO_m g₁ g₂) := by
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§(localVarLens "x1" state){1} = §x0{2} ∧
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
      equiv_seq_last 5 5 : (§(localVarLens "x1" state){1} = §x0{2} ∧ §y1{1} = §y1{2} ∧
          e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
      · equiv_if
        case guard => e1_close
        case «else» =>
          equiv_rnd
          equiv_skip
          e1_close
        case «then» =>
          stmt_wp
          equiv_seq_last 1 1 : (§(localVarLens "x1" state){1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧
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
              equiv_seq_last 1 1 : (§(localVarLens "x3" (List block)){1} =
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
                  equiv_while_raw (§(localVarLens "x3" (List block)){1} =
                      §(localVarLens "x1" (List block)){2} ∧ §n{1} = §n{2} ∧ §i{1} =
                          §i0{2} ∧ §bs{1} = §bs{2} ∧
                  §(localVarLens "x1" state){1} = §x0{2} ∧
                      e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
                  case body =>
                    stmt_wp
                    equiv_seq_last 1 1 : (§(localVarLens "x4" (List block)){1} =
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
                equiv_seq_last 0 3 : (last b0 §bs0{1} = oget ((§IRO2_RO_m{2}).get (§q{2}, §k{2} - 1)) ∧
                    (§IRO2_RO_m{2}).dom (§q{2}, §k{2} - 1) ∧
                        §(localVarLens "x1" state){1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧
                            0 < §k{1} ∧ e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
                · equiv_seq_last 1 1 : (§(localVarLens "x5" (List block)){1} = §q{2} ∧ §n1{1} = §k{2} ∧
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
                      equiv_while_raw (§(localVarLens "x5" (List block)){1} = §q{2} ∧ §n1{1} = §k{2} ∧
                          §i0{1} = §i{2} ∧ 0 ≤ §i0{1} ∧
                      §i0{1} ≤ §n1{1} ∧
                      (0 < §i0{1} → last b0 §bs0{1} =
                        oget ((§IRO2_RO_m{2}).get (§q{2}, §i0{1} - 1)) ∧
                        (§IRO2_RO_m{2}).dom (§q{2}, §i0{1} - 1)) ∧
                            §(localVarLens "x1" state){1} = §x0{2} ∧ §q{1} = §q{2} ∧ §k{1} = §k{2} ∧
                                0 < §k{1} ∧ e1Inv IRO2_RO_m §allGlobals{1} §allGlobals{2})
                      case body =>
                        stmt_wp
                        equiv_seq_last 1 1 : (§x6{1} = §(localVarLens "x5" (List block)){1} ∧
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
        (Module.app Simu (Module.pair (IRO2.RO.asRO IRO2_RO_m)
          (Indifferentiability.FUNCTIONALITY.view state (List block × ℤ) (List block)
            BlockSponge.BIRO.IRO.asF)))).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ e1Inv IRO2_RO_m g₁ g₂) := by
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (§(localVarLens "x1" state){1} = §x0{2} ∧
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
      (Module.app (L D) (IRO2.RO.asRO IRO2_RO_m)).procedure
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
  unfold IdealIndif Indifferentiability.GIdeal
  equiv_proc_to_stmt
  repeat stmt_inline{1} 0
  repeat stmt_inline{2} 0
  stmt_wp
  equiv_seq_last 1 1 : (globInvF Lg (FVP.fvP D) I §allGlobals{1} §allGlobals{2})
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
    (G : Footprint VariableAssignment) (_D_lossless : D_lossless_at D G) (m : VariableAssignment) :
    Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S) (DRestr D)).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (Module.app (L D) (IRO2.RO.asRO IRO2_RO_m)).procedure () m
        (fun r _ => r = true) :=
  Procedure.Pr_eq_of_prhlProc (equal1_equiv D hD _hDd IRO2_RO_m _hfresh)
    (fun r₁ _ r₂ _ h => by rw [h]) rfl

theorem equal2 (D : DISTINGUISHER) (hD : Module.ECModule D distExt) (_hDd : DRestrictions D)
    (IRO2_RO_m : Lens (FMap (List block × ℤ) block) VariableAssignment)
    (_hfresh : IRO2_RO_m.footprint ≤ (FVP.fvP D ⊔ DRestrictions.footprint)ᶜ)
    (G : Footprint VariableAssignment) (_D_lossless : D_lossless_at D G) (m : VariableAssignment) :
    Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF Simulator (DRestr D)).procedure () m
        (fun r _ => r = true) =
      Procedure.Pr (Module.app (L D) (IRO2.LRO IRO2_RO_m)).procedure () m
        (fun r _ => r = true) :=
  Procedure.Pr_eq_of_prhlProc (equal2_equiv D hD _hDd IRO2_RO_m _hfresh)
    (fun r₁ _ r₂ _ h => by rw [h]) rfl

set_option maxHeartbeats 2000000 in
-- `within_lens` through `Indif`, `Simu` and `DRestr`
omit [Params] in
/-- `L D` touches `glob D`, `Simulator`'s variables, `BIRO.IRO.mp` and `C.c` (and its oracle's).
Not an EC lemma: EasyCrypt reads a concrete module's globals off its code (for `RO_LRO_D`'s side
conditions, in `Simplify_simulator`). -/
theorem fvP_L (D : DISTINGUISHER) :
    FVP.fvP (L D) ≤ FVP.fvP D ⊔ (Lens.pair Simulator.m (Lens.pair Simulator.mi
      (Lens.pair Simulator.paths (Lens.pair Simulator.unvalid_map
        (Lens.pair BlockSponge.BIRO.IRO.mp BlockSponge.C.c))))).footprint := by
  fp_module (Lens.pair Simulator.m (Lens.pair Simulator.mi
      (Lens.pair Simulator.paths (Lens.pair Simulator.unvalid_map
        (Lens.pair BlockSponge.BIRO.IRO.mp BlockSponge.C.c)))))

end Simplify_Simulator

/-- EC's `Simplify_simulator` (EC: `rewrite (equal1 &m) (equal2 &m) eq_sym; byequiv (RO_LRO_D L _)`;
the local clone `IRO2`'s variables are fresh, exception E6). -/
theorem Simplify_simulator_at (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : Simplify_Simulator.DRestrictions D) (G : Footprint VariableAssignment) :
    D_lossless_at D G → ∀ m : VariableAssignment,
      Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF Simulator (DRestr D)).procedure () m
          (fun r _ => r = true) =
        Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S) (DRestr D)).procedure
          () m (fun r _ => r = true) := by
  intro D_ll m
  -- the local clone `IRO2`'s variables, fresh (exception E6)
  have hX : (Lens.pair Simulator.m (Lens.pair Simulator.mi
      (Lens.pair Simulator.paths (Lens.pair Simulator.unvalid_map
        (Lens.pair BlockSponge.BIRO.IRO.mp BlockSponge.C.c))))).footprint.FinitelySupported := by
    simp only [Footprint.lens_pair]
    repeat (first | exact .varLens _ | refine .sup ?_ ?_)
  have hfin : (FVP.fvP D ⊔ Simplify_Simulator.DRestrictions.footprint).FinitelySupported :=
    hD.finitelySupported.sup (by
      simp only [Simplify_Simulator.DRestrictions.footprint]
      repeat (first | exact .varLens _ | refine .sup ?_ ?_))
  haveI : Nonempty (FMap (List block × ℤ) block) := ⟨FMap.empty⟩
  haveI : Nonempty (FMap (List block × ℤ) (block × PROM.flag)) := ⟨FMap.empty⟩
  obtain ⟨RO_m, hRO, hROfs⟩ := Footprint.exists_fresh (FMap (List block × ℤ) block) hfin
  obtain ⟨FRO_m, hFRO, -⟩ :=
    Footprint.exists_fresh (FMap (List block × ℤ) (block × PROM.flag)) (hfin.sup hROfs)
  haveI : Lens.Disjoint RO_m FRO_m :=
    Lens.disjoint_of_footprint_le_compl _ _ ((Footprint.le_compl_comm _ _).mp
      (hFRO.trans (Footprint.compl_antimono le_sup_right)))
  have hLmod := PROM.FullRO.RO_Distinguisher.ecModule (List block × ℤ) block Unit Bool
    (Simplify_Simulator.L D) ((hD.finitelySupported.sup hX).mono (Simplify_Simulator.fvP_L D))
  have hXR : (Lens.pair Simulator.m (Lens.pair Simulator.mi
      (Lens.pair Simulator.paths (Lens.pair Simulator.unvalid_map
        (Lens.pair BlockSponge.BIRO.IRO.mp BlockSponge.C.c))))).footprint ≤
      Simplify_Simulator.DRestrictions.footprint := by
    simp only [Footprint.lens_pair, Simplify_Simulator.DRestrictions.footprint]
    fp_sub
  have hLd : FVP.fvP (Simplify_Simulator.L D) ≤ (RO_m.footprint ⊔ FRO_m.footprint)ᶜ := by
    refine (Simplify_Simulator.fvP_L D).trans ((Footprint.le_compl_comm _ _).mp (sup_le ?_ ?_))
    · exact hRO.trans (Footprint.compl_antimono (sup_le_sup_left hXR _))
    · exact hFRO.trans (Footprint.compl_antimono ((sup_le_sup_left hXR _).trans le_sup_left))
  have e := Procedure.Pr_eq_of_prhlProc (PROM.FullRO.FullEager.RO_LRO_D (List block × ℤ) block
    Unit Bool Simplify_Simulator.IRO2.dout FRO_m (fun _ => BitWord.dunifin_ll) RO_m
    (Simplify_Simulator.L D) hLmod hLd)
    (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true) (fun _ _ _ _ h => by rw [h.1])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) ⟨rfl, rfl, rfl⟩
  rw [Simplify_Simulator.equal2 D hD _hDd RO_m hRO G D_ll m,
    Simplify_Simulator.equal1 D hD _hDd RO_m hRO G D_ll m]
  exact e.symm

/-- EC's `Simplify_simulator` (`Simplify_simulator_at` over `glob D`, exception E14). -/
theorem Simplify_simulator (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : Simplify_Simulator.DRestrictions D) :
    D_lossless D → ∀ m : VariableAssignment,
      Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF Simulator (DRestr D)).procedure () m
          (fun r _ => r = true) =
        Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF (SimLast Gconcl.S) (DRestr D)).procedure
          () m (fun r _ => r = true) :=
  Simplify_simulator_at D hD _hDd _

/-- EC's `Real_Ideal`, `D_ll` over a region `G` (exception E14). -/
theorem Real_Ideal_at (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (_hDs : Simplify_Simulator.DRestrictions D)
    (_hG : Gext0Fresh D)
    (G : Footprint VariableAssignment) (hGc : (BlockSponge.C.c).footprint ≤ Gᶜ)
    (hGX : G ≤ (SLCommon.C.footprint ⊔
      (ConcreteF.PF.m).footprint ⊔ (ConcreteF.PF.mi).footprint ⊔ (G1.m).footprint ⊔
      (G1.mi).footprint ⊔ (G1.mh).footprint ⊔ (G1.mhi).footprint ⊔
      G1.chandle.footprint ⊔ (G1.paths).footprint ⊔ G1.bext.footprint ⊔ G1.bcol.footprint ⊔
      (Perm.m).footprint ⊔ (Perm.mi).footprint ⊔ (SLCommon.F.RO.m).footprint ⊔
      (SLCommon.Redo.prefixes).footprint ⊔ (Handle.FRO.m).footprint ⊔
      (ROhandle.RO.m).footprint)ᶜ)
    (GF : Footprint VariableAssignment) (hGF : GF.FinitelySupported) (hGGF : G ≤ GF.glob)
    (hRI : RealIdealRegion G)
    (D_ll : D_lossless_at D G) (m : VariableAssignment) :
      |(Procedure.Pr (RealIndif Sponge Perm (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) -
        (Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF Simulator (DRestr D)).procedure () m
          (fun r _ => r = true) : ℝ)| ≤ bound := by
  rw [Simplify_simulator_at D hD _hDs G D_ll m]
  exact Inefficient_Real_Ideal_at D hD _hDd _hG G hGc hGX GF hGF hGGF hRI D_ll m

/-- EC's `Real_Ideal`: the block sponge is indifferentiable from the infinite random oracle, with
the simulator `Simulator`. -/
theorem Real_Ideal (D : DISTINGUISHER) (hD : Module.ECModule D distExt)
    (_hDd : DRestrictions_Real_Ideal D) (_hDs : Simplify_Simulator.DRestrictions D)
    (_hG : Gext0Fresh D) :
    D_lossless D → ∀ m : VariableAssignment,
      |(Procedure.Pr (RealIndif Sponge Perm (DRestr D)).procedure () m (fun r _ => r = true) : ℝ) -
        (Procedure.Pr (IdealIndif BlockSponge.BIRO.IRO.asF Simulator (DRestr D)).procedure () m
          (fun r _ => r = true) : ℝ)| ≤ bound := by
  intro D_ll m
  rw [Simplify_simulator D hD _hDs D_ll m]
  exact Inefficient_Real_Ideal D hD _hDd _hG D_ll m

end GaudisCrypt.SHA3.Gconcl_list
