import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.PHoareWp
import GaudisCrypt.Logic.StmtSwap

/-!
# ElGamal is IND-CPA under DDH (EasyCrypt `examples/elgamal.ec`)

EC's proof, for every lossless adversary `A`:
```
local lemma cpa_ddh0 &m:
    Pr[CPA(ElGamal,A).main() @ &m : res] = Pr[DDH0(DDHAdv(A)).main() @ &m : res].
proof.
  byequiv=> //; proc; inline *.
  swap{1} 7 -5.
  auto; call (_:true).
  auto; call (_:true).
  by auto=> /> sk _ y _ r b _; rewrite expM.
qed.

local lemma ddh1_gb &m:
    Pr[DDH1(DDHAdv(A)).main() @ &m : res] = Pr[Gb.main() @ &m : res].
proof.
  byequiv=> //; proc; inline *.
  swap{1} 3 2; swap{1} [5..6] 2; swap{2} 6 -2.
  auto; call (_:true); wp.
  rnd (fun z, z + loge (if b then m1 else m0){2})
      (fun z, z - loge (if b then m1 else m0){2}).
  auto; call (_:true).
  auto; progress. …
qed.

local lemma Gb_half &m:
   Pr[Gb.main()@ &m : res] = 1%r/2%r.
proof.
  byphoare=> //; proc.
  rnd  (pred1 b')=> //=.
  conseq (: _ ==> true).
  + by move=> /> b; rewrite dbool1E pred1E.
  islossless;[ apply Ag_ll | apply Ac_ll].
qed.

lemma conclusion &m :
  `| Pr[CPA(ElGamal,A).main() @ &m : res] - 1%r/2%r | =
  `| Pr[DDH0(DDHAdv(A)).main() @ &m : res] - Pr[DDH1(DDHAdv(A)).main() @ &m : res] |.
```
The relational proofs are EC's scripts with `swap` (`stmt_swap{i} n k`).  Two differences:
* our inliner assigns a call's parameters in one tuple assignment, which `stmt_split_pair`
  takes apart before the swaps can reach one parameter (EC inlines one assignment per
  parameter);
* in `cpa_ddh0` the right side's `y` (and what depends on it) moves *down* past the adversary's
  `choose` and the coin, where EC moves the left side's `y` up — the same alignment.
`Gb_half` is `phoare_wp` through the game (the coin's two values average to `1/2` whatever the
guess) and losslessness, with no `rnd (pred1 b')`.

The group: EC's `DiffieHellman` clone — a group with a generator, exponents in a commutative
ring, the exponent laws, and a discrete logarithm (`loge`, used by `ddh1_gb`'s coupling).
`DDHGroup` records exactly these.  The adversary's `guess` takes the ciphertext as two
arguments (EC: one pair).
-/

namespace GaudisCrypt.Examples.EasyCryptBench.ElGamal

open GaudisCrypt

/-- EC's `DiffieHellman` clone: a group `G` with generator `g`, exponents in a commutative ring
`F`, and a discrete logarithm of every element (EC's `loge`). -/
structure DDHGroup where
  G : Type
  F : Type
  g : G
  gmul : G → G → G
  gpow : G → F → G
  log : G → F
  [g_inhabited : Inhabited G]
  [f_inhabited : Inhabited F]
  [f_fintype : Fintype F]
  [f_commring : CommRing F]
  gpow_add : ∀ (h : G) (a b : F), gpow h (a + b) = gmul (gpow h a) (gpow h b)
  gpow_mul : ∀ (h : G) (a b : F), gpow (gpow h a) b = gpow h (a * b)
  gpow_log : ∀ m : G, gpow g (log m) = m

variable (P : DDHGroup)

@[reducible] instance : Inhabited P.G := P.g_inhabited
@[reducible] instance : Inhabited P.F := P.f_inhabited
@[reducible] instance : Fintype P.F := P.f_fintype
@[reducible] instance : CommRing P.F := P.f_commring
@[reducible] noncomputable instance : DecidableEq P.G := Classical.decEq _
@[reducible] instance : Mul P.G := ⟨P.gmul⟩
@[reducible] instance : Pow P.G P.F := ⟨P.gpow⟩

theorem pow_add (h : P.G) (a b : P.F) : h ^ (a + b) = h ^ a * h ^ b := P.gpow_add h a b
theorem pow_mul (h : P.G) (a b : P.F) : (h ^ a) ^ b = h ^ (a * b) := P.gpow_mul h a b
theorem pow_log (m : P.G) : P.g ^ P.log m = m := P.gpow_log m

-- EC's `PKE_CPA.Scheme` (key generation and encryption).
moduletype Scheme {
  proc kg () -> P.G × P.F;
  proc enc (pk : P.G, m : P.G) -> P.G × P.G;
}

-- EC's `PKE_CPA.Adversary`.
moduletype Adversary {
  proc choose (pk : P.G) -> P.G × P.G;
  proc guess (c1 : P.G, c2 : P.G) -> Bool;
}

-- EC's `ElGamal` (the scheme).
module ElGamalScheme : (Scheme P) {
  proc kg () : (P.G × P.F) {
    var sk : P.F;
    sk <$ SubProbability.uniform;
    return (P.g ^ $sk, $sk)
  };
  proc enc (pk : P.G, m : P.G) : (P.G × P.G) {
    var y : P.F;
    y <$ SubProbability.uniform;
    return (P.g ^ $y, $pk ^ $y * $m)
  };
}

-- EC's `CPA(S, A)`.
module CPA using (S : Scheme P, A : Adversary P) {
  proc main () : Bool {
    var pk : P.G, sk : P.F, m0 m1 : P.G, b b' : Bool, c1 c2 : P.G;
    pk,sk <- call S.kg ();
    m0,m1 <- call A.choose ($pk);
    b <$ SubProbability.uniform;
    c1,c2 <- call S.enc ($pk, if $b then $m1 else $m0);
    b' <- call A.guess ($c1, $c2);
    return $b' == $b
  };
}

-- EC's `DDH.Adversary`.
moduletype DDHAdversary {
  proc guess (gx : P.G, gy : P.G, gz : P.G) -> Bool;
}

-- EC's `DDH0(A)`.
module DDH0 using (A : DDHAdversary P) {
  proc main () : Bool {
    var x y : P.F, b : Bool;
    x <$ SubProbability.uniform;
    y <$ SubProbability.uniform;
    b <- call A.guess (P.g ^ $x, P.g ^ $y, P.g ^ ($x * $y));
    return $b
  };
}

-- EC's `DDH1(A)`.
module DDH1 using (A : DDHAdversary P) {
  proc main () : Bool {
    var x y z : P.F, b : Bool;
    x <$ SubProbability.uniform;
    y <$ SubProbability.uniform;
    z <$ SubProbability.uniform;
    b <- call A.guess (P.g ^ $x, P.g ^ $y, P.g ^ $z);
    return $b
  };
}

-- EC's `DDHAdv(A)`: the reduction.
module DDHAdv using (A : Adversary P) : (DDHAdversary P) {
  proc guess (gx : P.G, gy : P.G, gz : P.G) : Bool {
    var m0 m1 : P.G, b b' : Bool;
    m0,m1 <- call A.choose ($gx);
    b <$ SubProbability.uniform;
    b' <- call A.guess ($gy, $gz * if $b then $m1 else $m0);
    return $b' == $b
  };
}

-- EC's local module `Gb`.
module Gb using (A : Adversary P) {
  proc main () : Bool {
    var x y z : P.F, m0 m1 : P.G, b b' : Bool;
    x <$ SubProbability.uniform;
    y <$ SubProbability.uniform;
    m0,m1 <- call A.choose (P.g ^ $x);
    z <$ SubProbability.uniform;
    b' <- call A.guess (P.g ^ $y, P.g ^ $z);
    b <$ SubProbability.uniform;
    return $b' == $b
  };
}

/-- `CPA(ElGamal, A).main`. -/
noncomputable abbrev cpaGame (A : Adversary P) : procmod () -> Bool :=
  Module.app (CPA P) (Module.pair (ElGamalScheme P) A)

theorem cpa_ddh0 (A : Adversary P) :
    equiv[ (cpaGame P A) ~ (Module.app (DDH0 P) (Module.app (DDHAdv P) A)) :
      §allGlobals{1} = §allGlobals{2} ==> ={res} ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline 0
  stmt_inline{1} 1
  stmt_split_pair{2} 4
  -- EC's `swap{1} 7 -5`, the other way round: the right side's `y` and what depends on it move
  -- after the adversary's `choose` and the coin
  stmt_swap{2} 6 2
  stmt_swap{2} 5 2
  stmt_swap{2} 2 4
  stmt_wp
  equiv_call prhlProc_refl _
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_rnd
  equiv_call prhlProc_refl _
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  intro σ₁ σ₂ h sk
  refine ⟨h, ?_⟩
  rintro r g₁ _ _ ⟨rfl, rfl⟩ b y
  refine ⟨⟨by rw [ElGamal.pow_mul], rfl⟩, ?_⟩
  rintro _ _ _ _ ⟨rfl, -⟩
  rfl

theorem ddh1_gb (A : Adversary P) :
    equiv[ (Module.app (DDH1 P) (Module.app (DDHAdv P) A)) ~ (Module.app (Gb P) A) :
      §allGlobals{1} = §allGlobals{2} ==> ={res} ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline{1} 0
  stmt_split_pair{1} 5
  -- EC's `swap{1} 3 2; swap{1} [5..6] 2; swap{2} 6 -2`: the exponent `z` drawn after the
  -- adversary's choice and the coin, on both sides
  stmt_swap{1} 7 2
  stmt_swap{1} 3 5
  stmt_swap{2} 6 -2
  stmt_wp
  equiv_call prhlProc_refl _
  stmt_wp
  equiv_rnd (fun z => z + P.log (if §b0{1} then §m1{1} else §m0{1}))
  equiv_rnd
  equiv_call prhlProc_refl _
  stmt_wp
  equiv_rnd
  equiv_rnd
  stmt_wp
  equiv_skip
  intro σ₁ σ₂ h _ _
  refine ⟨h, ?_⟩
  rintro r g₁ _ _ ⟨rfl, rfl⟩ b z
  refine ⟨⟨by rw [ElGamal.pow_add, ElGamal.pow_log], rfl⟩, ?_⟩
  rintro _ _ _ _ ⟨rfl, -⟩
  rfl

/-- EC's `Gb_half`: in `Gb` the coin is drawn after the adversary has guessed, so it guesses right
with probability exactly `1/2` (for a lossless adversary). -/
theorem gb_half (A : Adversary P) (hc : (Adversary.choose P A).procedure.IsLossless)
    (hg : (Adversary.guess P A).procedure.IsLossless) :
    phoare[ (Module.app (Gb P) A) : True ==> §res = true ] = (1 / 2) := by
  phoare_proc_to_stmt
  phoare_inline 0
  stmt_wp
  phoare_wp 6
  stmt_wp
  phoare_skip
  intro σ _
  -- the coin matches the guess with probability `1/2` whatever the guess; the adversary's calls
  -- then only contribute their mass
  have hcoin : ∀ v : Bool,
      indicatorE ((v == true) = true) / 2 + indicatorE ((v == false) = true) / 2 = 1 / 2 := by
    intro v; cases v <;> simp
  simp only [hcoin, hg.ewp_const, ENNReal.sum_div_card, hc.ewp_const]

/-- **EC's `conclusion`**: ElGamal's IND-CPA advantage is the DDH advantage of the reduction,
for every lossless adversary. -/
theorem conclusion (A : Adversary P) (hc : (Adversary.choose P A).procedure.IsLossless)
    (hg : (Adversary.guess P A).procedure.IsLossless) (m : VariableAssignment) :
    |(Procedure.Pr (Module.Proc.procedure (cpaGame P A)) () m (fun r _ => r = true) : ℝ) - 1 / 2|
      = |(Procedure.Pr (Module.Proc.procedure (Module.app (DDH0 P) (Module.app (DDHAdv P) A))) ()
            m (fun r _ => r = true) : ℝ)
          - (Procedure.Pr (Module.Proc.procedure (Module.app (DDH1 P) (Module.app (DDHAdv P) A)))
            () m (fun r _ => r = true) : ℝ)| := by
  have h0 := Procedure.Pr_eq_of_prhlProc (cpa_ddh0 P A) (E₁ := fun r _ => r = true)
    (E₂ := fun r _ => r = true) (fun r₁ _ r₂ _ (h : r₁ = r₂) => by rw [h])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl
  have h1 := Procedure.Pr_eq_of_prhlProc (ddh1_gb P A) (E₁ := fun r _ => r = true)
    (E₂ := fun r _ => r = true) (fun r₁ _ r₂ _ (h : r₁ = r₂) => by rw [h])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl
  have h2 := Procedure.Pr_of_phoareProc (gb_half P A hc hg) (args := ()) (σ := m) trivial
  have h2' : (Procedure.Pr (Module.Proc.procedure (Module.app (Gb P) A)) () m
      (fun r _ => r = true) : ℝ) = 1 / 2 := by
    have := congrArg ENNReal.toReal h2
    simpa using this
  rw [h0, h1, h2']

end GaudisCrypt.Examples.EasyCryptBench.ElGamal
