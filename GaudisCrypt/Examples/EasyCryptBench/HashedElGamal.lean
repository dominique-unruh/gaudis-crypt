import GaudisCrypt.Examples.EasyCryptBench.ElGamal

/-!
# Hashed ElGamal is IND-CPA under DDH and entropy smoothing
(EasyCrypt `examples/hashed_elgamal_std.ec`)

The ciphertext is `(g^y, hash hk (pk^y) +^ m)`.  EC's proof, for every lossless adversary:
```
local lemma cpa_ddh0 &m:
    Pr[CPA(Hashed_ElGamal,A).main() @ &m : res] = Pr[DDH0(DDHAdv(A)).main() @ &m : res].
proof.
  byequiv=> //; proc; inline *.
  swap{1} 1 1; swap{1} 8 -6; swap{2} 6 -3.
  auto; call (: true). auto; call (: true).
  by auto=> /> sk _ y _ hk _ [m0 m1] b _ /=; rewrite -expM.
qed.

local lemma ddh1_es1 &m:
    Pr[DDH1(DDHAdv(A)).main() @ &m : res] = Pr[ES1(ESAdv(A)).main() @ &m : res].
proof.
  byequiv=> //; proc; inline *.
  swap{1} 7 -3; swap{2} [5..6] -4; swap{2} 4 -1.
  auto; call (: true). auto; call (:true). by auto.
qed.

local lemma es0_Gb &m:
    Pr[ES0(ESAdv(A)).main() @ &m : res] = Pr[Gb.main()@ &m : res].
proof.
  byequiv=> //; proc; inline *.
  swap{1} 2 1. swap{1} [3..4] 4. swap{2} 7 -2.
  auto; call (: true); wp.
  rnd (fun w, w +^ (b0{1} ? m1{1} : m0{1})).
  auto; call (: true).
  by auto=> /> *; split => *; algebra.
qed.

local lemma Gb_half &m: Pr[Gb.main()@ &m : res] = 1%r/2%r.

lemma conclusion &m :
     `| Pr[CPA(Hashed_ElGamal,A).main() @ &m : res] - 1%r/2%r |
  <= `| Pr[DDH0(DDHAdv(A)).main() @ &m : res] - Pr[DDH1(DDHAdv(A)).main() @ &m : res] |
   + `| Pr[ES0(ESAdv(A)).main() @ &m : res] - Pr[ES1(ESAdv(A)).main() @ &m : res]|.
```
The relational proofs here are EC's, with `stmt_swap`/`stmt_split_pair` for its `swap`s and
`equiv_call` for its `call (: true)`.  The swaps are not EC's index for index: our inliner
assigns a call's parameters as one tuple (split first) and resets the callee's locals on entry,
so in `ddh1_es1` the reset of `DDHAdv`'s locals moves out of the way before `hk` can move past
it; and where EC moves both sides, one side suffices here.

The group and DDH games are ElGamal's (`ElGamal.DDHGroup`, `DDH0`, `DDH1`).  EC's
`EntropySmoothing` theory is `ES`: hash keys from a lossless distribution `dhkey`, a hash into
bit strings, and bit strings with `+^` — here any finite additive group (only translation is
used: the coupling `w ↦ w + m_b`).
-/

namespace GaudisCrypt.Examples.EasyCryptBench.HashedElGamal

open GaudisCrypt
open GaudisCrypt.Examples.EasyCryptBench.ElGamal (DDHGroup DDHAdversary DDH0 DDH1)

variable (P : DDHGroup)

/-- EC's `EntropySmoothing` theory: hash keys drawn from a lossless distribution `dhkey`, a
hash `hash : hkey → group → bits`, and bit strings with `+^` (here any finite additive group). -/
structure ES where
  HK : Type
  [hk_inhabited : Inhabited HK]
  dhkey : SubProbability HK
  dhkey_ll : dhkey.expected (fun _ => 1) = 1
  Bits : Type
  [bits_group : AddCommGroup Bits]
  [bits_fintype : Fintype Bits]
  [bits_inhabited : Inhabited Bits]
  hash : HK → P.G → Bits

variable {P} (E : ES P)

@[reducible] instance : Inhabited E.HK := E.hk_inhabited
@[reducible] instance : AddCommGroup E.Bits := E.bits_group
@[reducible] instance : Fintype E.Bits := E.bits_fintype
@[reducible] instance : Inhabited E.Bits := E.bits_inhabited

variable (P)

-- EC's `EntropySmoothing.AdvES`.
moduletype AdvES {
  proc guess (hk : E.HK, h : E.Bits) -> Bool;
}

-- EC's `ES0(A)`: a uniform bit string.
module ES0 using (A : AdvES P E) {
  proc main () : Bool {
    var b : Bool, hk : E.HK, h : E.Bits;
    hk <$ E.dhkey;
    h <$ SubProbability.uniform;
    b <- call A.guess ($hk, $h);
    return $b
  };
}

-- EC's `ES1(A)`: the hash of a uniform group element.
module ES1 using (A : AdvES P E) {
  proc main () : Bool {
    var b : Bool, hk : E.HK, z : P.F;
    hk <$ E.dhkey;
    z <$ SubProbability.uniform;
    b <- call A.guess ($hk, E.hash $hk (P.g ^ $z));
    return $b
  };
}

-- EC's `PKE_CPA.Scheme` at hashed ElGamal's types.
moduletype Scheme {
  proc kg () -> (E.HK × P.G) × (E.HK × P.F);
  proc enc (pk : E.HK × P.G, m : E.Bits) -> P.G × E.Bits;
}

-- EC's `PKE_CPA.Adversary`.
moduletype Adversary {
  proc choose (pk : E.HK × P.G) -> E.Bits × E.Bits;
  proc guess (c1 : P.G, c2 : E.Bits) -> Bool;
}

-- EC's `Hashed_ElGamal`.
module HashedElGamalScheme : (Scheme P E) {
  proc kg () : ((E.HK × P.G) × (E.HK × P.F)) {
    var hk : E.HK, sk : P.F;
    hk <$ E.dhkey;
    sk <$ SubProbability.uniform;
    return (($hk, P.g ^ $sk), ($hk, $sk))
  };
  proc enc (pk : E.HK × P.G, m : E.Bits) : (P.G × E.Bits) {
    var y : P.F, h : E.Bits;
    y <$ SubProbability.uniform;
    h <- E.hash ($pk).1 (($pk).2 ^ $y);
    return (P.g ^ $y, $h + $m)
  };
}

-- EC's `CPA(S, A)`.
module CPA using (S : Scheme P E, A : Adversary P E) {
  proc main () : Bool {
    var pk : E.HK × P.G, sk : E.HK × P.F, m0 m1 : E.Bits, b b' : Bool, c1 : P.G, c2 : E.Bits;
    pk,sk <- call S.kg ();
    m0,m1 <- call A.choose ($pk);
    b <$ SubProbability.uniform;
    c1,c2 <- call S.enc ($pk, if $b then $m1 else $m0);
    b' <- call A.guess ($c1, $c2);
    return $b' == $b
  };
}

-- EC's `DDHAdv(A)`.
module DDHAdv using (A : Adversary P E) : (DDHAdversary P) {
  proc guess (gx : P.G, gy : P.G, gz : P.G) : Bool {
    var hk : E.HK, m0 m1 : E.Bits, b b' : Bool, h : E.Bits;
    hk <$ E.dhkey;
    m0,m1 <- call A.choose (($hk, $gx));
    b <$ SubProbability.uniform;
    h <- E.hash $hk $gz;
    b' <- call A.guess ($gy, $h + if $b then $m1 else $m0);
    return $b' == $b
  };
}

-- EC's `ESAdv(A)`.
module ESAdv using (A : Adversary P E) : (AdvES P E) {
  proc guess (hk : E.HK, h : E.Bits) : Bool {
    var x y : P.F, m0 m1 : E.Bits, b b' : Bool;
    x <$ SubProbability.uniform;
    y <$ SubProbability.uniform;
    m0,m1 <- call A.choose (($hk, P.g ^ $x));
    b <$ SubProbability.uniform;
    b' <- call A.guess (P.g ^ $y, $h + if $b then $m1 else $m0);
    return $b' == $b
  };
}

-- EC's local module `Gb`.
module Gb using (A : Adversary P E) {
  proc main () : Bool {
    var hk : E.HK, x y : P.F, v : E.Bits, m0 m1 : E.Bits, b b' : Bool;
    hk <$ E.dhkey;
    x <$ SubProbability.uniform;
    y <$ SubProbability.uniform;
    m0,m1 <- call A.choose (($hk, P.g ^ $x));
    v <$ SubProbability.uniform;
    b' <- call A.guess (P.g ^ $y, $v);
    b <$ SubProbability.uniform;
    return $b' == $b
  };
}

theorem cpa_ddh0 (A : Adversary P E) :
    equiv[ (Module.app (CPA P E) (Module.pair (HashedElGamalScheme P E) A))
        ~ (Module.app (DDH0 P) (Module.app (DDHAdv P E) A)) :
      §allGlobals{1} = §allGlobals{2} ==> ={res} ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline 0
  stmt_inline{1} 1
  stmt_swap{1} 2 1
  stmt_split_pair{2} 4
  stmt_swap{2} 6 3
  stmt_swap{2} 5 3
  stmt_swap{2} 2 5
  stmt_wp
  equiv_call
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_rnd
  equiv_call
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  -- the hashed shared secrets agree: `pk^y = (g^sk)^y = g^(sk·y)`
  intro _ _ h _ _ _
  exact ⟨h, fun _ _ _ _ => by rw [ElGamal.pow_mul]⟩

theorem ddh1_es1 (A : Adversary P E) :
    equiv[ (Module.app (DDH1 P) (Module.app (DDHAdv P E) A))
        ~ (Module.app (ES1 P E) (Module.app (ESAdv P E) A)) :
      §allGlobals{1} = §allGlobals{2} ==> ={res} ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline 0
  -- EC's `swap{1} 7 -3; swap{2} [5..6] -4; swap{2} 4 -1`, here on the left only: the samplings
  -- in the order `hk, z, x, y` of the right (the inlined reset of `DDHAdv`'s locals, `hk`
  -- among them, moved out of the way first)
  stmt_swap{1} 4 -3
  stmt_swap{1} 6 -4
  stmt_swap{1} 5 -2
  stmt_wp
  equiv_call
  stmt_wp
  equiv_rnd
  equiv_call
  stmt_wp
  equiv_rnd
  equiv_rnd
  stmt_wp
  equiv_rnd
  equiv_rnd
  stmt_wp
  equiv_skip
  exact fun _ _ h _ _ _ _ _ => h

theorem es0_gb (A : Adversary P E) :
    equiv[ (Module.app (ES0 P E) (Module.app (ESAdv P E) A)) ~ (Module.app (Gb P E) A) :
      §allGlobals{1} = §allGlobals{2} ==> ={res} ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline{1} 0
  stmt_split_pair{1} 4
  -- EC's `swap{1} 2 1; swap{1} [3..4] 4; swap{2} 7 -2`: the uniform string `h` drawn after the
  -- adversary's choice and the coin
  stmt_swap{1} 5 4
  stmt_swap{1} 2 6
  stmt_swap{2} 7 -2
  stmt_wp
  equiv_call
  stmt_wp
  equiv_rnd (fun w => w + if §b0{1} then §m1{1} else §m0{1})
  equiv_rnd
  equiv_call
  equiv_rnd
  equiv_rnd
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  exact fun _ _ h _ _ _ _ => h

/-- A lossless distribution's expectation of a constant is the constant. -/
theorem ES.dhkey_expected_const (c : ENNReal) : E.dhkey.expected (fun _ => c) = c := by
  have h := E.dhkey_ll
  letI : MeasurableSpace E.HK := ⊤
  change ∫⁻ _, c ∂E.dhkey.1 = c
  change ∫⁻ _, (1 : ENNReal) ∂E.dhkey.1 = 1 at h
  rw [MeasureTheory.lintegral_const]
  rw [MeasureTheory.lintegral_const, one_mul] at h
  rw [h, mul_one]

/-- EC's `Gb_half`. -/
theorem gb_half (A : Adversary P E) (hc : (Adversary.choose P E A).procedure.IsLossless)
    (hg : (Adversary.guess P E A).procedure.IsLossless) :
    phoare[ (Module.app (Gb P E) A) : True ==> §res = true ] = (1 / 2) := by
  phoare_proc_to_stmt
  phoare_inline 0
  stmt_wp
  phoare_wp 7
  stmt_wp
  phoare_skip
  intro σ _
  have hcoin : ∀ v : Bool,
      indicatorE ((v == true) = true) / 2 + indicatorE ((v == false) = true) / 2 = 1 / 2 := by
    intro v; cases v <;> simp
  simp only [hcoin, hg.ewp_const, ENNReal.sum_div_card, hc.ewp_const, E.dhkey_expected_const]

/-- `Pr[M : res]`, as a real number (EC's `Pr[M.main() @ &m : res]`). -/
noncomputable abbrev prRes (M : procmod () -> Bool) (m : VariableAssignment) : ℝ :=
  (Procedure.Pr (Module.Proc.procedure M) () m (fun r _ => r = true) : ℝ)

/-- `byequiv` for two games returning booleans, related with `={res}` from equal globals. -/
theorem prRes_eq {M₁ M₂ : procmod () -> Bool}
    (h : equiv[ M₁ ~ M₂ : §allGlobals{1} = §allGlobals{2} ==> ={res} ])
    (m : VariableAssignment) : prRes M₁ m = prRes M₂ m := by
  unfold prRes
  rw [Procedure.Pr_eq_of_prhlProc h (E₁ := fun r _ => r = true) (E₂ := fun r _ => r = true)
    (fun r₁ _ r₂ _ (h : r₁ = r₂) => by rw [h]) (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl]

/-- **EC's `conclusion`**: hashed ElGamal's IND-CPA advantage is at most the DDH advantage plus
the entropy-smoothing advantage of the two reductions, for every lossless adversary. -/
theorem conclusion (A : Adversary P E) (hc : (Adversary.choose P E A).procedure.IsLossless)
    (hg : (Adversary.guess P E A).procedure.IsLossless) (m : VariableAssignment) :
    |prRes (Module.app (CPA P E) (Module.pair (HashedElGamalScheme P E) A)) m - 1 / 2|
      ≤ |prRes (Module.app (DDH0 P) (Module.app (DDHAdv P E) A)) m
          - prRes (Module.app (DDH1 P) (Module.app (DDHAdv P E) A)) m|
        + |prRes (Module.app (ES0 P E) (Module.app (ESAdv P E) A)) m
          - prRes (Module.app (ES1 P E) (Module.app (ESAdv P E) A)) m| := by
  have hgb : prRes (Module.app (Gb P E) A) m = 1 / 2 := by
    have h := congrArg ENNReal.toReal
      (Procedure.Pr_of_phoareProc (gb_half P E A hc hg) (args := ()) (σ := m) trivial)
    unfold prRes
    simpa using h
  rw [prRes_eq (cpa_ddh0 P E A), prRes_eq (ddh1_es1 P E A), prRes_eq (es0_gb P E A), hgb,
    abs_sub_comm (1 / 2)]
  exact abs_sub_le _ _ _

end GaudisCrypt.Examples.EasyCryptBench.HashedElGamal
