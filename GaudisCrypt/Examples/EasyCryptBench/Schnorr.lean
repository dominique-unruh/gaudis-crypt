import GaudisCrypt.Examples.EasyCryptBench.ElGamal

/-!
# The Schnorr proof of knowledge is a Sigma protocol (EasyCrypt `examples/SchnorrPK.ec`)

All three properties of EC's `SchnorrPKSecurity`, standard axioms:

* `completeness` — an honest run with `h = g ^ w` verifies with probability `1` (`phoare = 1`:
  inline, `phoare_wp`, both samplings averaged out by `ENNReal.sum_div_card`);
* `special_soundness` — two accepting transcripts with distinct challenges yield the witness
  `(z - z') / (e - e')` with probability `1` (deterministic: inline, `stmt_wp`, algebra);
* `shvzk` — the simulated transcript is distributed as the real one, against every distinguisher
  (`equiv`; EC's script below).

```
byequiv => //. proc; inline*.
seq 27 22: (... to{1} = Some t{2} /\ ={h, w, e}).
+ swap{1} 15 -7; swap{2} 12 -5; swap{1} 11 -3; wp.
  rnd (fun z, z - w{1}*e{1}) (fun r, r + w{1}*e{1}).
  by seq 2 2 : (#pre /\ ={w0}); auto => />; progress; algebra.
by call (_:true); rcondf{1} 1; auto.
```

Here: the two swaps go on the real side (the challenge drawn before the commitment's randomness),
the retry loop is removed by `equiv_rcondf{1}` (EC's `rcondf{1}`), the simulator's response is
coupled with the commitment's randomness along `z ↦ z - e·w`, and the ideal game's unused
commitment randomness is a one-sided sampling.

The group is ElGamal's `DDHGroup` (no group identity or inverse: the algebra is on exponents,
`pow_add`/`pow_mul` and `ring`).  Special soundness needs what EC's `ZModE` field provides: an
inverse on exponents (`finv`, a parameter of the extractor) and injectivity of `g ^ ·`.
-/

namespace GaudisCrypt.Examples.EasyCryptBench.Schnorr

open GaudisCrypt
open GaudisCrypt.Examples.EasyCryptBench.ElGamal (DDHGroup)

variable (P : DDHGroup)

@[reducible] noncomputable instance : DecidableEq P.F := Classical.decEq _

/-! ## EC's `SigmaProtocol` theory, at Schnorr's types

statement = group, witness = message = exponent … : `x : G`, `w : F`, messages `G`, secrets,
challenges and responses `F`; challenges drawn uniformly (EC's `de = dt`). -/

-- EC's `SigmaScheme`.
moduletype SigmaScheme {
  proc gen () -> P.G × P.F;
  proc commit (x : P.G, w : P.F) -> P.G × P.F;
  proc test (x : P.G, m : P.G) -> P.F;
  proc respond (sw : P.G × P.F, ms : P.G × P.F, e : P.F) -> P.F;
  proc verify (x : P.G, m : P.G, e : P.F, z : P.F) -> Bool;
}

-- EC's `SigmaAlgorithms`: the extractor and the simulator.
moduletype SigmaAlgorithms {
  proc soundness (x : P.G, m : P.G, e : P.F, z : P.F, e' : P.F, z' : P.F) -> Option P.F;
  proc simulate (x : P.G, e : P.F) -> P.G × P.F × P.F;
}

-- EC's `SigmaTraceDistinguisher`.
moduletype Distinguisher {
  proc distinguish (x : P.G, t : P.G × P.F × P.F) -> Bool;
}

-- EC's `Completeness(S)`.
module Completeness using (S : SigmaScheme P) {
  proc main (x : P.G, w : P.F) : Bool {
    var e : P.F, m : P.G, s : P.F, z : P.F, b : Bool;
    m,s <- call S.commit ($x, $w);
    e <- call S.test ($x, $m);
    z <- call S.respond (($x, $w), ($m, $s), $e);
    b <- call S.verify ($x, $m, $e, $z);
    return $b
  };
}

-- EC's `SpecialSoundnessExperiment(S, A)`.
module SpecialSoundnessExperiment using (S : SigmaScheme P, A : SigmaAlgorithms P) {
  proc main (x : P.G, m : P.G, e : P.F, z : P.F, e' : P.F, z' : P.F) : (Option P.F) {
    var s sto : Option P.F, w : P.F, r v v' : Bool;
    sto <- call A.soundness ($x, $m, $e, $z, $e', $z');
    if (!($e == $e') && !($sto == none)) {
      w <- ($sto).getD default;
      r <- $x == P.g ^ $w;
      v <- call S.verify ($x, $m, $e, $z);
      v' <- call S.verify ($x, $m, $e', $z');
      if ($r && $v && $v') {
        s <- some $w;
      } else {
        s <- none;
      }
    } else {
      s <- none;
    }
    return $s
  };
}

-- EC's `SimulateHonestVerifier(S, A, D).gameIdeal`, with the calls of
-- `SpecialHVZKExperiment(S, A).main(x, e)` (simulate, verify, keep the transcript if it
-- verifies) written out.  The scheme `S` and the simulator `A` are Lean parameters and only the
-- distinguisher `D` a module parameter: the `module` command does not manage the well-typedness
-- proof of a functor of three module parameters.
module SHVIdeal (S : SigmaScheme P) (A : SigmaAlgorithms P) using (D : Distinguisher P) {
  proc main () : Bool {
    var b : Bool, e : P.F, i : ℕ, m : P.G, s : P.F, t : P.G × P.F × P.F,
      ot : Option (P.G × P.F × P.F), x : P.G, w : P.F, v : Bool;
    x,w <- call (SigmaScheme.gen P S) ();
    m,s <- call (SigmaScheme.commit P S) ($x, $w);
    e <$ SubProbability.uniform;
    t <- call (SigmaAlgorithms.simulate P A) ($x, $e);
    v <- call (SigmaScheme.verify P S) ($x, ($t).1, ($t).2.1, ($t).2.2);
    if ($v) { ot <- some $t; } else { ot <- none; }
    i <- 0;
    while ($ot == none) {
      t <- call (SigmaAlgorithms.simulate P A) ($x, $e);
      v <- call (SigmaScheme.verify P S) ($x, ($t).1, ($t).2.1, ($t).2.2);
      if ($v) { ot <- some $t; } else { ot <- none; }
      i <- $i + 1;
    }
    t <- ($ot).getD default;
    b <- call D.distinguish ($x, $t);
    return $b
  };
}

-- EC's `SimulateHonestVerifier(S, A, D).gameReal`, with `Run(S).main()` written out.
module SHVReal using (S : SigmaScheme P, D : Distinguisher P) {
  proc main () : Bool {
    var b : Bool, t : P.G × P.F × P.F, m : P.G, e : P.F, z : P.F, x : P.G, w : P.F, s : P.F;
    x,w <- call S.gen ();
    m,s <- call S.commit ($x, $w);
    e <- call S.test ($x, $m);
    z <- call S.respond (($x, $w), ($m, $s), $e);
    t <- ($m, $e, $z);
    b <- call D.distinguish ($x, $t);
    return $b
  };
}

/-! ## The Schnorr protocol -/

-- EC's `SchnorrPK`.
module SchnorrPK : (SigmaScheme P) {
  proc gen () : (P.G × P.F) {
    var h : P.G, w : P.F;
    w <$ SubProbability.uniform;
    if ($w == 0) { w <- 0; }
    h <- P.g ^ $w;
    return ($h, $w)
  };
  proc commit (_h : P.G, _w : P.F) : (P.G × P.F) {
    var r : P.F, a : P.G;
    r <$ SubProbability.uniform;
    a <- P.g ^ $r;
    return ($a, $r)
  };
  proc test (_h : P.G, _a : P.G) : P.F {
    var e : P.F;
    e <$ SubProbability.uniform;
    return $e
  };
  proc respond (sw : P.G × P.F, ms : P.G × P.F, e : P.F) : P.F {
    var z w r : P.F;
    w <- ($sw).2;
    r <- ($ms).2;
    z <- $r + $e * $w;
    return $z
  };
  proc verify (h : P.G, a : P.G, e : P.F, z : P.F) : Bool {
    var v v' : P.G;
    v <- $a * $h ^ $e;
    v' <- P.g ^ $z;
    return $v == $v'
  };
}

variable (finv : P.F → P.F)

-- EC's `SchnorrPKAlgorithms`.
module SchnorrPKAlgorithms : (SigmaAlgorithms P) {
  proc soundness (h : P.G, a : P.G, e : P.F, z : P.F, e' : P.F, z' : P.F) : (Option P.F) {
    var sto : Option P.F, w : P.F, v v' : Bool;
    v <- P.g ^ $z == $a * $h ^ $e;
    v' <- P.g ^ $z' == $a * $h ^ $e';
    if (!($e == $e') && $v && $v') {
      w <- ($z - $z') * finv ($e - $e');
      sto <- some $w;
    } else {
      sto <- none;
    }
    return $sto
  };
  proc simulate (h : P.G, e : P.F) : (P.G × P.F × P.F) {
    var a : P.G, z : P.F;
    z <$ SubProbability.uniform;
    a <- P.g ^ $z * $h ^ (- $e);
    return ($a, $e, $z)
  };
}

/-! ## Completeness (EC's `schnorr_proof_of_knowledge_completeness`) -/

theorem completeness_phoare :
    phoare[ (Module.app (Completeness P) (SchnorrPK P)) (x, w) :
      §x = P.g ^ §w ==> §res = true ] = 1 := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_inline 0
  phoare_inline 0
  phoare_inline 0
  phoare_inline 0
  stmt_wp
  phoare_wp 10
  phoare_skip
  intro x w hx
  subst hx
  have hv : ∀ r e : P.F, P.g ^ r * (P.g ^ w) ^ e = P.g ^ (r + e * w) := by
    intro r e; rw [ElGamal.pow_mul, ← ElGamal.pow_add, mul_comm]
  simp only [hv, beq_self_eq_true, indicatorE_true, ENNReal.sum_div_card]

/-- EC's `schnorr_proof_of_knowledge_completeness`:
`Pr[Completeness(SchnorrPK).main(h, w) : res] = 1` whenever `h = g ^ w`. -/
theorem completeness (w : P.F) (m : VariableAssignment) :
    Procedure.Pr (Module.Proc.procedure (Module.app (Completeness P) (SchnorrPK P)))
      (P.g ^ w, w) m (fun r _ => r = true) = 1 := by
  have h := Procedure.Pr_of_phoareProc (completeness_phoare P) (args := (P.g ^ w, w)) (σ := m) rfl
  exact ENNReal.coe_eq_one.mp h

/-! ## Special soundness (EC's `schnorr_proof_of_knowledge_special_soundness`) -/

theorem special_soundness_phoare (h msg : P.G) (ch ch' r r' : P.F)
    (hinv : ∀ a : P.F, a ≠ 0 → a * finv a = 1) (hinj : ∀ a b : P.F, P.g ^ a = P.g ^ b → a = b)
    (hne : ch ≠ ch') (h₁ : P.g ^ r = msg * h ^ ch) (h₂ : P.g ^ r' = msg * h ^ ch') :
    phoare[ (Module.app (SpecialSoundnessExperiment P)
        (Module.pair (SchnorrPK P) (SchnorrPKAlgorithms P finv))) (x, m, e, z, e', z') :
      §x = h ∧ §m = msg ∧ §e = ch ∧ §z = r ∧ §e' = ch' ∧ §z' = r' ==>
      §res ≠ none ∧ h = P.g ^ (§res).getD default ] = 1 := by
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_inline 0
  phoare_inline 0
  phoare_inline 0
  stmt_wp
  phoare_skip
  rintro x m e z e' z' ⟨hx, hm, he, hz, he', hz'⟩
  subst x m e z e' z'
  -- the extracted witness is `log h`: both transcripts give `r = log msg + log h · ch`
  have hexp : ∀ c s : P.F, P.g ^ s = msg * h ^ c → s = P.log msg + P.log h * c := by
    intro c s hs
    apply hinj
    rw [hs, ElGamal.pow_add, ← ElGamal.pow_mul, ElGamal.pow_log, ElGamal.pow_log]
  have hw : P.g ^ ((r - r') * finv (ch - ch')) = h := by
    rw [hexp ch r h₁, hexp ch' r' h₂,
      show P.log msg + P.log h * ch - (P.log msg + P.log h * ch') = P.log h * (ch - ch') by ring,
      mul_assoc, hinv _ (sub_ne_zero.mpr hne), mul_one, ElGamal.pow_log]
  simp [hne, h₁, h₂, hw]

/-- EC's `schnorr_proof_of_knowledge_special_soundness`: from two accepting transcripts with
distinct challenges, the extractor returns a witness, with probability `1`. -/
theorem special_soundness (h msg : P.G) (ch ch' r r' : P.F)
    (hinv : ∀ a : P.F, a ≠ 0 → a * finv a = 1) (hinj : ∀ a b : P.F, P.g ^ a = P.g ^ b → a = b)
    (hne : ch ≠ ch') (h₁ : P.g ^ r = msg * h ^ ch) (h₂ : P.g ^ r' = msg * h ^ ch')
    (m : VariableAssignment) :
    Procedure.Pr (Module.Proc.procedure (Module.app (SpecialSoundnessExperiment P)
        (Module.pair (SchnorrPK P) (SchnorrPKAlgorithms P finv))))
      (h, msg, ch, r, ch', r') m (fun s _ => s ≠ none ∧ h = P.g ^ s.getD default) = 1 := by
  have hp := special_soundness_phoare P finv h msg ch ch' r r' hinv hinj hne h₁ h₂
  have hpr := Procedure.Pr_of_phoareProc hp (args := (h, msg, ch, r, ch', r')) (σ := m)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ENNReal.coe_eq_one.mp hpr

/-! ## Special honest-verifier zero knowledge (EC's `schnorr_proof_of_knowledge_shvzk`) -/

theorem shvzk_prhl (D : Distinguisher P) :
    equiv[ (Module.app (SHVIdeal P (SchnorrPK P) (SchnorrPKAlgorithms P finv)) D)
        ~ (Module.app (SHVReal P) (Module.pair (SchnorrPK P) D)) :
      §allGlobals{1} = §allGlobals{2} ==> ={res} ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline{1} 3
  stmt_inline{1} 2
  stmt_inline{1} 1
  stmt_inline{2} 3
  stmt_inline{2} 2
  stmt_inline{2} 1
  stmt_inline 0
  -- EC's `swap`s: on the real side the challenge is drawn before the commitment's randomness
  -- (the test's reset of its locals moved out of the way first)
  stmt_swap{2} 11 -3
  stmt_swap{2} 13 -4
  stmt_wp
  equiv_call
  stmt_wp
  -- the simulator's transcript verifies, so its retry loop does not run (EC's `rcondf{1}`)
  equiv_rcondf{1}
  stmt_wp
  -- the simulated response is the real one: `z = r + e·w` (EC's `rnd (fun z, z - w*e)`)
  equiv_rnd (fun z => z - §e{1} * §w{1})
  stmt_wp
  equiv_rnd
  -- the ideal game's commitment randomness is not used
  stmt_wp{1}
  stmt_wp{1} 1
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  intro globals₁ globals₂ hg w _ e z
  subst hg
  generalize (if (w == 0) = true then 0 else w) = w
  have hv : P.g ^ (z - e * w) * (P.g ^ w) ^ e = P.g ^ z := by
    rw [ElGamal.pow_mul, ← ElGamal.pow_add]; congr 1; ring
  have ha : P.g ^ z * (P.g ^ w) ^ (-e) = P.g ^ (z - e * w) := by
    rw [ElGamal.pow_mul, ← ElGamal.pow_add]; congr 1; ring
  simp [ha, hv]

/-- EC's `schnorr_proof_of_knowledge_shvzk`: the distinguisher cannot tell the simulated transcript
from the real one. -/
theorem shvzk (D : Distinguisher P) (m : VariableAssignment) :
    Procedure.Pr (Module.Proc.procedure
        (Module.app (SHVIdeal P (SchnorrPK P) (SchnorrPKAlgorithms P finv)) D)) () m
        (fun r _ => r = true)
      = Procedure.Pr (Module.Proc.procedure
          (Module.app (SHVReal P) (Module.pair (SchnorrPK P) D))) () m (fun r _ => r = true) :=
  Procedure.Pr_eq_of_prhlProc (shvzk_prhl P finv D) (E₁ := fun r _ => r = true)
    (E₂ := fun r _ => r = true) (fun r₁ _ r₂ _ (h : r₁ = r₂) => by rw [h])
    (a₁ := ()) (a₂ := ()) (σ₁ := m) (σ₂ := m) rfl

end GaudisCrypt.Examples.EasyCryptBench.Schnorr
