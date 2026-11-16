import GaudisCrypt.Lib.EC.Group
import GaudisCrypt.Lib.EC.SigmaProtocol
import GaudisCrypt.Lib.EC.Logic
import GaudisCrypt.Syntax.Clone
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Syntax.ModuleSubtype
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.CallSpec
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECCallEquiv
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECSeq
import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Logic.StmtSwap
import GaudisCrypt.Logic.ECInlineParams
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.ECRnd

/-!
# The Schnorr proof of knowledge is a Sigma protocol (EasyCrypt `examples/SchnorrPK.ec`)

EC's file, declaration by declaration and script line by line: completeness (with its
losslessness), special soundness and special honest-verifier zero knowledge, all proven.

Translation (as `Examples/ElGamal.lean`):
* `clone Group.CyclicGroup as G … clone GP.FDistr as FD. clone GP.ZModE.ZModpField as ZPF.` is
  the section's group (`Lib/EC/Group.lean`), the field's lemmas Mathlib's.
* `theory SchnorrTypes`: its type abbreviations (`statement = group`, `witness = exp`, …) are
  written out in the clone of `SigmaProtocol`; `R_DL` is a proposition.
* `clone import SigmaProtocol as SP with … op R = R_DL, op de = dt` is `clone import`; the
  theory's `R` is opened (EC's `export SigmaProtocol`).
* The proofs' `(D <: SigmaTraceDistinguisher)` is the binder `∀ (D <: SigmaTraceDistinguisher)`.

Gap list (the examples' infrastructure batch; numbers as in `Examples/ElGamal.lean` where the
gap is the same):
* GAP 1: `stmt_split_params` after `inline*` (one assignment per parameter, as EC).
* GAP 3 (closed 2026-11-15): the path `SimulateHonestVerifier(SchnorrPK, SchnorrPKAlgorithms,
  D).gameIdeal` into a module without a module type that has several module parameters.
* GAP 5 (closed 2026-11-15): `byphoare (_: h = x /\ w' = w ==> _)` on a clone's game is
  `byphoare (: §x = h ∧ §w = w' ==> _)`.
* GAP 6: EC's `seq 2 2 : (#pre /\ ={w0})`: there is no `#pre`; the precondition is written out.
* The last steps in the group (EC's `algebra`, and the eight rewrites of special soundness) are
  by hand; special soundness finds the witness through `loge`, where EC rewrites with `expM`,
  `expB`, `mulcV`, ….
-/

set_option ec.strict true

-- EasyCrypt names the scheme after the file (`SchnorrPK.SchnorrPK`); kept (exception E1)
set_option linter.dupNamespace false
-- EC's procedures have parameters they do not use (`commit(h, w)`, `test(h, a)`)
set_option linter.unusedVariables false

namespace GaudisCrypt.Examples.SchnorrPK

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.CyclicGroup
open GaudisCrypt.EC.SigmaProtocol (R)

variable {group exp : Type} [CommGroup group] [Field exp] [Fintype exp] [DecidableEq exp]
  [CyclicGroup.Params group exp]

/-! `theory SchnorrTypes` -/

/-- EC's `op R_DL (h : group) (w : exp) = (h = g ^ w)`. -/
def R_DL (h : group) (w : exp) : Prop := h = g ^ w

clone import GaudisCrypt.EC.SigmaProtocol as SP with
  type statement <- group, type witness <- exp, type message <- group, type secret <- exp,
  type challenge <- exp, type response <- exp,
  op R <- R_DL, op de <- dt

open Classical in
module SchnorrPK : SigmaScheme {
  proc gen () : (group × exp) {
    var h : group, w : exp;
    w <$ dt;
    if (decide ($w = 0)) {
      w <- 0;
    }
    h <- g ^ $w;
    return ($h, $w)
  };
  proc commit (h : group, w : exp) : (group × exp) {
    var r : exp, a : group;
    r <$ dt;
    a <- g ^ $r;
    return ($a, $r)
  };
  proc test (h : group, a : group) : exp {
    var e : exp;
    e <$ dt;
    return $e
  };
  proc respond (sw : group × exp, ms : group × exp, e : exp) : exp {
    var z : exp, w : exp, r : exp;
    w <- ($sw).2;
    r <- ($ms).2;
    z <- $r + $e * $w;
    return $z
  };
  proc verify (h : group, a : group, e : exp, z : exp) : Bool {
    var v : group, v' : group;
    v <- $a * ($h ^ $e);
    v' <- g ^ $z;
    return decide ($v = $v')
  };
}

open Classical in
module SchnorrPKAlgorithms : SigmaAlgorithms {
  proc soundness (h : group, a : group, e : exp, z : exp, e' : exp, z' : exp) : (Option exp) {
    var sto : Option exp, w : exp, v : Bool, v' : Bool;
    v <- decide (g ^ $z = $a * ($h ^ $e));
    v' <- decide (g ^ $z' = $a * ($h ^ $e'));
    if (decide ($e ≠ $e') && $v && $v') {
      w <- ($z - $z') / ($e - $e');
      sto <- some $w;
    } else {
      sto <- none;
    }
    return $sto
  };
  proc simulate (h : group, e : exp) : (group × exp × exp) {
    var a : group, z : exp;
    z <$ dt;
    a <- (g ^ $z) * ($h ^ (-$e));
    return ($a, $e, $z)
  };
}

section SchnorrPKSecurity

/-- EC's `lemma schnorr_proof_of_knowledge_completeness_ll:
islossless Completeness(SchnorrPK).main`. -/
theorem schnorr_proof_of_knowledge_completeness_ll :
    islossless Completeness(SchnorrPK).main := by
  -- EC: by islossless; apply FDistr.dt_ll.
  islossless

/-- EC's `lemma schnorr_proof_of_knowledge_completeness h w' &m: R h w' =>
Pr[Completeness(SchnorrPK).main(h, w') @ &m : res] = 1%r`. -/
theorem schnorr_proof_of_knowledge_completeness (h : group) (w' : exp) (m : VariableAssignment) :
    R h w' → Pr[ Completeness(SchnorrPK).main (h, w') @ &m : §res ] = 1 := by
  -- EC: rewrite /R /R_DL; move => sigmarel.
  intro sigmarel
  -- EC: byphoare (_: h = x /\ w' = w ==> _) => //; rewrite sigmarel.
  byphoare (: §x = h ∧ §w = w' ==> _)
  -- EC: proc; inline*; swap 3 -2; swap 8 -7.
  --     (GAP 1)
  phoare_proc; phoare_inline*; stmt_split_params; stmt_swap 3 -2; stmt_swap 8 -7
  -- EC: auto=> &hr />.
  --     by rewrite dt_ll => /> *; algebra.
  --     (EC's `algebra`: the verification's equation by `expD`, `expM`; then `dt` is lossless)
  phoare_auto
  intro x1 w hxw
  obtain ⟨rfl, rfl⟩ := hxw
  have hR : x1 = (g : group) ^ w := sigmarel
  have key : ∀ a b : exp, (g : group) ^ a * x1 ^ b = g ^ (a + b * w) := fun a b => by
    rw [hR, expD, mul_comm b w, expM]
  simp only [key, decide_true, eq_self, dt_ll, implies_true, and_self]

set_option maxHeartbeats 2000000 in
-- one declaration: the experiment with its two inlined verifications and nested conditionals
/-- EC's `lemma schnorr_proof_of_knowledge_special_soundness (h: statement) msg (ch ch' r r' :
exp) &m: ch <> ch' => g ^ r = msg*(h ^ ch) => g ^ r' = msg*(h ^ ch') =>
Pr[SpecialSoundnessExperiment(SchnorrPK, SchnorrPKAlgorithms).main(h, msg, ch, r, ch', r') @ &m :
(res <> None /\ R h (oget res))] = 1%r`. -/
theorem schnorr_proof_of_knowledge_special_soundness (h : group) (msg : group)
    (ch ch' r r' : exp) (m : VariableAssignment) :
    ch ≠ ch' → g ^ r = msg * (h ^ ch) → g ^ r' = msg * (h ^ ch') →
    Pr[ SpecialSoundnessExperiment(SchnorrPK, SchnorrPKAlgorithms).main (h, msg, ch, r, ch', r')
      @ &m : §res ≠ none ∧ R h (oget §res) ] = 1 := by
  -- EC: move => challenges_differ accepting_transcript_1 accepting_transcript_2.
  intro challenges_differ accepting_transcript_1 accepting_transcript_2
  -- EC: byphoare (_: h = x /\ msg = m /\ ch = e /\ ch' = e' /\ r = z /\ r' = z' ==> _) => //.
  byphoare (: §x = h ∧ §m = msg ∧ §e = ch ∧ §e' = ch' ∧ §z = r ∧ §z' = r' ==> _)
  -- EC: proc; simplify; inline*.
  phoare_proc; phoare_inline*
  -- EC: auto; rewrite /R /R_DL /oget => &hr /> hne 2!-> /=.
  --     rewrite expM !expB accepting_transcript_1 accepting_transcript_2.
  --     rewrite invM (mulcC m{hr}) -mulcA (mulcA m{hr}) mulcV mulcA mulc1 -expB -expM.
  --     by rewrite ZPF.divrr ?ZPF.subr_eq0 // exp1.
  --     (the extracted witness is `loge h`: here through the logarithms of `h` and `msg`)
  phoare_auto
  rintro x m1 e e' z z' ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hw : x = (g : group) ^ ((z - z') / (e - e')) := by
    obtain ⟨a, rfl⟩ : ∃ a : exp, m1 = g ^ a := ⟨loge m1, (expgK m1).symm⟩
    obtain ⟨b, rfl⟩ : ∃ b : exp, x = g ^ b := ⟨loge x, (expgK x).symm⟩
    have h1 : z = a + b * e := by
      have := congrArg (loge : group → exp) accepting_transcript_1
      rwa [← expM, ← expD, loggK, loggK] at this
    have h2 : z' = a + b * e' := by
      have := congrArg (loge : group → exp) accepting_transcript_2
      rwa [← expM, ← expD, loggK, loggK] at this
    have hne : e - e' ≠ 0 := sub_ne_zero.mpr challenges_differ
    congr 1
    rw [h1, h2]; field_simp; ring
  simp [challenges_differ, accepting_transcript_1, accepting_transcript_2, oget, R, R_DL, ← hw]

set_option maxHeartbeats 4000000 in
-- one declaration: the two games inlined, with the simulator's loop
/-- EC's `lemma schnorr_proof_of_knowledge_shvzk (D<: SigmaTraceDistinguisher) &m:
Pr[SimulateHonestVerifier(SchnorrPK, SchnorrPKAlgorithms, D).gameIdeal() @ &m : res] =
Pr[SimulateHonestVerifier(SchnorrPK, SchnorrPKAlgorithms, D).gameReal() @ &m : res]`. -/
theorem schnorr_proof_of_knowledge_shvzk : ∀ (D <: SigmaTraceDistinguisher),
    ∀ m : VariableAssignment,
    Pr[ SimulateHonestVerifier(SchnorrPK, SchnorrPKAlgorithms, D).gameIdeal () @ &m : §res ] =
      Pr[ SimulateHonestVerifier(SchnorrPK, SchnorrPKAlgorithms, D).gameReal () @ &m : §res ] := by
  intro D m
  -- EC: byequiv => //.
  byequiv
  -- EC: proc; inline*.
  --     (GAP 1)
  equiv_proc; stmt_inline*
  stmt_split_params
  -- EC: seq 27 22: ((glob D){1} = (glob D){2} /\ i{1} = 0 /\ x{1} = h{1} /\ x{2} = h{2} /\
  --                  to{1} = Some t{2} /\ ={h, w, e}).
  equiv_seq 27 22 : (={glob D} ∧ §i{1} = 0 ∧ §x{1} = §h{1} ∧ §x{2} = §h{2} ∧
    §«to»{1} = some §t{2} ∧ ={h, w, e})
  · -- EC: swap{1} 15 -7; swap{2} 12 -5; swap{1} 11 -3; wp.
    stmt_swap{1} 15 -7; stmt_swap{2} 12 -5; stmt_swap{1} 11 -3; stmt_wp
    -- EC: rnd (fun z, z - w{1}*e{1}) (fun r, r + w{1}*e{1}).
    equiv_rnd (fun z => z - §w{1} * §e{1}) (fun r => r + §w{1} * §e{1})
    -- EC: by seq 2 2 : (#pre  /\ ={w0}); auto => />; progress; algebra.
    --     (GAP 6: `#pre` written out; EC's `algebra`: the simulated transcript is the real one
    --     and verifies, by `expM`, `expD`)
    equiv_seq 2 2 : (={allGlobals, w0})
    · equiv_auto
    equiv_auto; auto_progress
    · congr 1
      refine Prod.ext ?_ (Prod.ext rfl ?_)
      · rw [← expM, ← expD]; congr 1; ring_nf
      · ring
    · rename_i hv
      exact hv (by rw [← expM, ← expM, ← expD, ← expD]; congr 1; ring)
  · -- EC: by call (_:true); rcondf{1} 1; auto.
    equiv_call (_ : True); stmt_rcondf{1} 1
    · hoare_auto
    equiv_auto
    intros; simp_all [oget]

end SchnorrPKSecurity

end GaudisCrypt.Examples.SchnorrPK
