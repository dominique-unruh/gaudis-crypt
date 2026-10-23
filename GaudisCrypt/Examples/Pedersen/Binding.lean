import GaudisCrypt.Examples.Pedersen.Pedersen
import GaudisCrypt.Logic.PRHLWp

/-!
# Pedersen binding, relationally (EC's `pedersen_computational_binding`)

EC's
```
module DLogAttacker(B:Binder) : DL.DLog.Adversary = {
  proc guess (h: group) : exp option = {
    var x, c, m, m', d, d';
    (c, m, d, m', d') <@ B.bind(h);
    if ((c = g ^ d * h ^ m) /\ (c = g ^ d' * h ^ m') /\ (m <> m'))
      x <- Some((d - d') * inv (m' - m));
    else
      x <- None;
    return x;
  }
}.

lemma pedersen_computational_binding (B<:Binder) &m:
  Pr[BindingExperiment(Pedersen, B).main() @ &m : res] =
  Pr[DL.DLog.DLogExperiment(DLogAttacker(B)).main() @ &m : res].
proof.
  byequiv => //.
  proc; inline*.
  wp; call (_: true); auto => /> x _ [ c m d m' d'] /= comm comm' m_neq_m'.
  … (algebra) …
qed.
```
A binder that opens a commitment two ways reveals the discrete logarithm of `h`: from
`g^d · h^m = g^d' · h^m'` and `h = g^x`, `x = (d - d') / (m' - m)`.

`PedersenGroup` has a commutative ring of exponents and nothing about the generator, so the two
facts the algebra needs are hypotheses of the theorem, as EC gets them from its prime-order
group clone: an inverse `finv` on the exponents (EC's `inv`), and injectivity of `x ↦ g^x`
(EC's `pow_bij`).
-/

namespace GaudisCrypt.Examples.Pedersen

open GaudisCrypt

variable (group : PedersenGroup)

-- EC's `DLog.Adversary`: guesses the discrete logarithm of `h`, or gives up.
moduletype DLogAdversary {
  proc guess (h : group.G) -> Option group.F;
}

-- EC's `DLogExperiment`.
module DLogExperiment using (A : DLogAdversary group) {
  proc main () : Bool {
    var x : group.F, x' : Option group.F;
    x <$ SubProbability.uniform;
    x' <- call A.guess (group.g ^ $x);
    return $x' == some $x
  };
}

variable (finv : group.F → group.F)

-- EC's `DLogAttacker(B)`: the reduction from binding to discrete log.
module DLogAttacker using (B : Binder group.types) : (DLogAdversary group) {
  proc guess (h : group.G) : (Option group.F) {
    var x : Option group.F, c : group.G, m m' : group.F, d d' : group.F;
    c,m,d,m',d' <- call B.bind ($h);
    if ($c == group.g ^ $d * $h ^ $m && $c == group.g ^ $d' * $h ^ $m' && !($m == $m')) {
      x <- some (($d - $d') * finv ($m' - $m));
    } else {
      x <- none;
    }
    return $x
  };
}

/-- `BindingExperiment(Pedersen, B).main`. -/
noncomputable abbrev bindingGame (B : Binder group.types) : procmod () -> Bool :=
  Module.app (Module.app (BindingExperiment.main group.types) (Pedersen group)) B

/-- `DLogExperiment(DLogAttacker(B)).main`. -/
noncomputable abbrev dlogGame (B : Binder group.types) : procmod () -> Bool :=
  Module.app (DLogExperiment group) (Module.app (DLogAttacker group finv) B)

/-- The binding game and the discrete-log game, run on the reduction, are equivalent (EC's
`byequiv` in `pedersen_computational_binding`), given an exponent inverse `finv` and injective
`x ↦ g^x`. -/
theorem binding_prhl (B : Binder group.types)
    (hinv : ∀ a : group.F, a ≠ 0 → a * finv a = 1)
    (hinj : ∀ a b : group.F, group.g ^ a = group.g ^ b → a = b) :
    equiv[ (bindingGame group B) ~ (dlogGame group finv B) :
      §allGlobals{1} = §allGlobals{2} ==> ={res} ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline{1} 3
  stmt_inline{1} 2
  stmt_inline{1} 0
  stmt_inline{2} 0
  stmt_wp
  equiv_call
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  intro _ _ h x
  refine ⟨h, ?_⟩
  rintro ⟨c, m, d, m', d'⟩ _
  simp only [ite_self]
  cases hcb : (c == group.g ^ d * (group.g ^ x) ^ m && c == group.g ^ d' * (group.g ^ x) ^ m' &&
      !(m == m'))
  · simp
  · -- two openings of `c` reveal `x`
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hcb
    obtain ⟨⟨h1, h2⟩, hne⟩ := hcb
    have e : d + x * m = d' + x * m' := hinj _ _ (by
      rw [Pedersen.pow_add group, Pedersen.pow_add group, ← Pedersen.pow_mul group,
        ← Pedersen.pow_mul group, ← h1, ← h2])
    have hx : (d - d') * finv (m' - m) = x := by
      rw [show d - d' = x * (m' - m) by linear_combination e, mul_assoc,
        hinv _ (sub_ne_zero.mpr (Ne.symm hne)), mul_one]
    simp [hx]

/-- **EC's `pedersen_computational_binding`**: breaking binding is solving discrete log. -/
theorem pedersen_computational_binding (B : Binder group.types)
    (hinv : ∀ a : group.F, a ≠ 0 → a * finv a = 1)
    (hinj : ∀ a b : group.F, group.g ^ a = group.g ^ b → a = b) (σ : VariableAssignment) :
    Procedure.Pr (Module.Proc.procedure (bindingGame group B)) () σ (fun r _ => r = true)
      = Procedure.Pr (Module.Proc.procedure (dlogGame group finv B)) () σ (fun r _ => r = true) :=
  Procedure.Pr_eq_of_prhlProc (binding_prhl group finv B hinv hinj)
    (fun r₁ _ r₂ _ (h : r₁ = r₂) => by rw [h]) rfl

/-! ## The standard discrete-log experiment (EC's `std_red_dl_bridge`)

EC's `DLogStdExperiment` asks for the logarithm itself; an adversary that may give up is turned
into one that never does by guessing at random when it gives up:
```
module StdRedAdversary(L:DLog.Adversary) = {
  proc guess(h: group) : exp = {
    var lx, x;
    lx <@ L.guess(h);
    if (lx = None) x <$ dt; else x <- oget lx;
    return x;
  }
}.

local lemma std_red_dl_bridge (B<:Binder) &m:
  Pr[DL.DLog.DLogExperiment(DLogAttacker(B)).main() @ &m : res] <=
  Pr[DL.DLog.DLogStdExperiment(DL.StdRedAdversary(DLogAttacker(B))).main() @ &m : res].
proof.
  byequiv => //.
  proc; wp; inline{2} DL.StdRedAdversary(DLogAttacker(B)).guess; wp.
  seq 2 3: (x'{1} = lx{2} /\ x{1} = x{2}).
  + by inline*; wp; call (_: true); auto.
  by if{2}; auto => />; apply dt_ll.
qed.
```
-/

-- EC's `DLog.StdAdversary`: guesses the discrete logarithm of `h`.
moduletype DLogStdAdversary {
  proc guess (h : group.G) -> group.F;
}

-- EC's `DLogStdExperiment`.
module DLogStdExperiment using (A : DLogStdAdversary group) {
  proc main () : Bool {
    var x : group.F, x' : group.F;
    x <$ SubProbability.uniform;
    x' <- call A.guess (group.g ^ $x);
    return $x' == $x
  };
}

-- EC's `StdRedAdversary(L)`.
module StdRedAdversary using (L : DLogAdversary group) : (DLogStdAdversary group) {
  proc guess (h : group.G) : group.F {
    var lx : Option group.F, x : group.F;
    lx <- call L.guess ($h);
    if ($lx == none) {
      x <$ SubProbability.uniform;
    } else {
      x <- ($lx).getD default;
    }
    return $x
  };
}

/-- A may-fail adversary does at most as well as the standard one built from it. -/
theorem std_red_prhl (L : DLogAdversary group) :
    equiv[ (Module.app (DLogExperiment group) L)
        ~ (Module.app (DLogStdExperiment group) (Module.app (StdRedAdversary group) L)) :
      §allGlobals{1} = §allGlobals{2} ==> §res{1} = true → §res{2} = true ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline{2} 0
  stmt_wp
  equiv_seq 0 1 : §x'{1} = §lx{2} ∧ §x{1} = §x{2}
  · equiv_call
    stmt_wp
    equiv_rnd
    stmt_wp
    equiv_skip
    exact fun _ _ h _ => h
  · equiv_if{2}
    case «then» =>
      -- the adversary gave up: it did not win on the left either
      stmt_wp{2} 1
      equiv_skip
      rintro x' x _ _ ⟨⟨rfl, rfl⟩, hn⟩ _ hx
      simp only [beq_iff_eq] at hn hx
      simp [hn] at hx
    case «else» =>
      stmt_wp
      equiv_skip
      rintro x' x _ _ ⟨⟨rfl, rfl⟩, -⟩ hx
      simp only [beq_iff_eq] at hx
      simp [hx]

/-- **EC's `std_red_dl_bridge`**. -/
theorem std_red_dl_bridge (L : DLogAdversary group) (σ : VariableAssignment) :
    Procedure.Pr (Module.Proc.procedure (Module.app (DLogExperiment group) L)) () σ
        (fun r _ => r = true)
      ≤ Procedure.Pr (Module.Proc.procedure
          (Module.app (DLogStdExperiment group) (Module.app (StdRedAdversary group) L))) () σ
        (fun r _ => r = true) :=
  Procedure.Pr_le_of_prhlProc (std_red_prhl group L)
    (fun r₁ _ r₂ _ (h : r₁ = true → r₂ = true) => h) rfl

/-- **EC's `pedersen_std_computational_binding`**: breaking binding is at most solving standard
discrete log. -/
theorem pedersen_std_computational_binding (B : Binder group.types)
    (hinv : ∀ a : group.F, a ≠ 0 → a * finv a = 1)
    (hinj : ∀ a b : group.F, group.g ^ a = group.g ^ b → a = b) (σ : VariableAssignment) :
    Procedure.Pr (Module.Proc.procedure (bindingGame group B)) () σ (fun r _ => r = true)
      ≤ Procedure.Pr (Module.Proc.procedure (Module.app (DLogStdExperiment group)
          (Module.app (StdRedAdversary group) (Module.app (DLogAttacker group finv) B)))) () σ
        (fun r _ => r = true) :=
  (pedersen_computational_binding group finv B hinv hinj σ).trans_le
    (std_red_dl_bridge group _ σ)

end GaudisCrypt.Examples.Pedersen
