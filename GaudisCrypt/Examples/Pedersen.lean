import GaudisCrypt.Lib.EC.DLog
import GaudisCrypt.Lib.EC.Commitment
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
import GaudisCrypt.Logic.ECInline
import GaudisCrypt.Logic.ECInlineParams
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.ECRnd
import GaudisCrypt.Lib.EC.Logic

/-!
# The Pedersen commitment scheme (EasyCrypt `examples/Pedersen.ec`)

Pedersen, "Non-interactive and information-theoretic secure verifiable secret sharing".  EC's
file, declaration by declaration and script line by line: correctness, perfect hiding (the
unhider wins with probability exactly `1/2`), and computational binding by reduction to the
discrete logarithm (`Lib/EC/DLog.lean`).  All of EC's lemmas are proven.

Translation:
* `clone DLog as DL. import DL.G DL.GP DL.FD DL.GP.ZModE.` clones the theory without
  instantiating it: the file stays abstract in the group, the section's
  `variable {group exp} … [CyclicGroup.Params group exp]` (`Lib/EC/Group.lean`); EC's `DL.DLog.X`
  is `DLog.DLog.X`, `DL.StdRedAdversary` is `DLog.StdRedAdversary`.
* `theory PedersenTypes` (`value = group`, `message = exp`, `commitment = group`,
  `openingkey = exp`) is written out in the clone of `Commitment`.
* The lemmas' `(U <: Unhider)`, `(B <: Binder)` are the binders `∀ (U <: Unhider)`.
* EC's `local module FakeCommit(U : Unhider)` is a module with a module parameter, as there.

Gap list (what keeps the file from reading as EC's; items of the examples' infrastructure
batch):
* GAP 1 (closed 2026-11-15): EC's `call (_ : true)` on the adversary is `equiv_call (_ : True)`.
* GAP 2 (closed 2026-11-15): pHL on an event reached with probability `1` — `call H` with
  `H : islossless f`, `rnd`, `auto` — keeps the judgment an event, as EC does
  (`Logic/PHoareRnd.lean`): `fakecommit_half` is EC's script.
* GAP 3 (closed 2026-11-15): after inlining, `x` is a group element on the left
  (`Correctness`'s key) and an exponent on the right (`FakeCommit`'s secret): two variables
  of one name.  `§x{2}` is the right side's, in the tactics' conditions and in the goals as
  shown.
* GAP 4: `islossless` closes the samplings (EC's hint `random`) and leaves the calls; EC's takes
  the hypotheses `uc_ll`, `ug_ll` and leaves the samplings.  `hi_ll` ends with `assumption`
  where EC's ends with `apply dt_ll || apply DBool.dbool_ll`.
* GAP 5 (closed 2026-11-15): `byequiv` on `Pr[…] ≤ Pr[…]` closes the events' implication
  `res{1} → res{2}` itself, as EC's `=> //`.
* GAP 6: the field algebra of `pedersen_computational_binding` (EC's `field`, `ring`,
  `pow_bij`) is by hand, as is naming what `auto => /> x _ [c m d m' d'] /= comm comm'
  m_neq_m'` names (`rename_i`, `obtain`).
* GAP 8 (closed 2026-11-15): `inline{2} DL.StdRedAdversary(DLogAttacker(B)).guess` finds the
  call the experiment makes through its module type.
* GAP 7 (goals as shown): `byequiv` states `={allGlobals}` (the whole global state) where EC
  shows `={glob U}`.
-/

set_option ec.strict true

-- EasyCrypt names the scheme after the file (`Pedersen.Pedersen`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.Examples.Pedersen

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.CyclicGroup

variable {group exp : Type} [CommGroup group] [Field exp] [Fintype exp] [DecidableEq exp]
  [DecidableEq group] [CyclicGroup.Params group exp]

-- EC: clone import Commitment as CM with
--       type CommitmentProtocol.value      <- value,
--       type CommitmentProtocol.message    <- message,
--       type CommitmentProtocol.commitment <- commitment,
--       type CommitmentProtocol.openingkey <- openingkey.
clone import GaudisCrypt.EC.CommitmentProtocol as CM with
  type value <- group, type message <- exp, type commitment <- group, type openingkey <- exp

module Pedersen : CommitmentScheme {
  proc gen () : group {
    var x : exp, h : group;
    x <$ dt;
    h <- g ^ $x;
    return $h
  };
  proc commit (h : group, m : exp) : (group × exp) {
    var c : group, d : exp;
    d <$ dt;
    c <- g ^ $d * $h ^ $m;
    return ($c, $d)
  };
  proc verify (h : group, m : exp, c : group, d : exp) : Bool {
    var c' : group;
    c' <- g ^ $d * $h ^ $m;
    return decide ($c = $c')
  };
}

module DLogAttacker using (B : Binder) {
  proc guess (h : group) : (Option exp) {
    var x : Option exp, c : group, m : exp, m' : exp, d : exp, d' : exp;
    c, m, d, m', d' <- call B.bind ($h);
    if (decide ($c = g ^ $d * $h ^ $m ∧ $c = g ^ $d' * $h ^ $m' ∧ $m ≠ $m')) {
      x <- some (($d - $d') * ($m' - $m)⁻¹);
    } else {
      x <- none;
    }
    return $x
  };
}

-- EC's `local module FakeCommit(U : Unhider)` of the section.  (EC: "Clearly, there are many
-- useless lines, but their presence helps for the proofs".)
module FakeCommit using (U : Unhider) {
  proc main () : Bool {
    var b : Bool, b' : Bool, x : exp, h : group, c : group, d : exp, m0 : exp, m1 : exp;
    x <$ dt;
    h <- g ^ $x;
    m0, m1 <- call U.choose ($h);
    b <$ dbool;
    d <$ dt;
    c <- g ^ $d; -- message independent - fake commitment
    b' <- call U.guess ($c);
    return decide ($b = $b')
  };
}

section PedersenSecurity

/-- Correctness.  EC's `lemma pedersen_correctness:
hoare[Correctness(Pedersen).main: true ==> res]`. -/
theorem pedersen_correctness :
    hoare[ Correctness(Pedersen).main : True ==> §res ] := by
  -- EC: proc; inline *;auto.
  hoare_proc; hoare_inline*; hoare_auto

/-- EC's `local lemma hi_ll (U<:Unhider): islossless U.choose => islossless U.guess =>
islossless FakeCommit(U).main`. -/
theorem hi_ll : ∀ (U <: Unhider), islossless U.choose → islossless U.guess →
    islossless FakeCommit(U).main := by
  -- EC: by move => uc_ll ug_ll; islossless; (apply dt_ll || apply DBool.dbool_ll).
  --     (GAP 4)
  intro U uc_ll ug_ll; islossless <;> assumption

/-- Perfect hiding.  EC's `local lemma fakecommit_half (U<:Unhider) &m: islossless U.choose =>
islossless U.guess => Pr[FakeCommit(U).main() @ &m : res] = 1%r/2%r`. -/
theorem fakecommit_half : ∀ (U <: Unhider), ∀ m : VariableAssignment, islossless U.choose →
    islossless U.guess → Pr[ FakeCommit(U).main () @ &m : §res ] = 1 / 2 := by
  -- EC: move => uc_ll ug_ll; byphoare => //.
  intro U m uc_ll ug_ll; byphoare
  -- EC: proc; wp.
  --     (the result is already in the postcondition: there is nothing for `wp`)
  phoare_proc
  -- EC: swap 4 3.
  stmt_swap 4 3
  -- EC: rnd (pred1 b'); call ug_ll; wp; rnd; call uc_ll; auto => />.
  phoare_rnd (pred1 §b'); phoare_call ug_ll; stmt_wp; phoare_rnd; phoare_call uc_ll; phoare_auto
  -- EC: by rewrite dt_ll /= => v _ result; rewrite DBool.dbool1E.
  smt_close [dt_ll, mu_pred1, dbool1E_mu1, pred1E]

/-- EC's `local lemma phi_hi (U<:Unhider) &m:
Pr[HidingExperiment(Pedersen,U).main() @ &m : res] = Pr[FakeCommit(U).main() @ &m : res]`. -/
theorem phi_hi : ∀ (U <: Unhider), ∀ m : VariableAssignment,
    Pr[ HidingExperiment(Pedersen, U).main () @ &m : §res ] =
      Pr[ FakeCommit(U).main () @ &m : §res ] := by
  intro U m
  -- EC: byequiv => //.
  byequiv
  -- EC: proc; inline*.
  equiv_proc; stmt_inline*
  -- EC: call (_:true); wp.
  equiv_call (_ : True); stmt_wp
  -- EC: rnd (fun d, (d + x * (b?m1:m0)){2})
  --         (fun d, (d - x * (b?m1:m0)){2}).
  equiv_rnd (fun d => d + §x{2} * (if §b{2} then §m1{2} else §m0{2}))
    (fun d => d - §x{2} * (if §b{2} then §m1{2} else §m0{2}))
  -- EC: by wp; rnd; call (_: true); auto => />; progress; algebra.
  --     (`progress` closes the bijection's two equations itself and splits the conditional;
  --     EC's `algebra` on the commitment's equation is `expD`, `expM`)
  stmt_wp; equiv_rnd; equiv_call (_ : True); equiv_auto; auto_progress
  all_goals rw [expD, expM]

/-- Perfect hiding - QED.  EC's `lemma pedersen_perfect_hiding (U<:Unhider) &m:
islossless U.choose => islossless U.guess =>
Pr[HidingExperiment(Pedersen,U).main() @ &m : res] = 1%r/2%r`. -/
theorem pedersen_perfect_hiding : ∀ (U <: Unhider), ∀ m : VariableAssignment,
    islossless U.choose → islossless U.guess →
    Pr[ HidingExperiment(Pedersen, U).main () @ &m : §res ] = 1 / 2 := by
  -- EC: by move => uc_ll ug_ll; rewrite (phi_hi U &m) (fakecommit_half U &m).
  intro U m uc_ll ug_ll; rw [phi_hi U m, fakecommit_half U m uc_ll ug_ll]

/-- Computational binding - QED.  EC's `lemma pedersen_computational_binding (B<:Binder) &m:
Pr[BindingExperiment(Pedersen, B).main() @ &m : res] =
Pr[DL.DLog.DLogExperiment(DLogAttacker(B)).main() @ &m : res]`. -/
theorem pedersen_computational_binding : ∀ (B <: Binder), ∀ m : VariableAssignment,
    Pr[ BindingExperiment(Pedersen, B).main () @ &m : §res ] =
      Pr[ DLog.DLog.DLogExperiment(DLogAttacker(B)).main () @ &m : §res ] := by
  intro B m
  -- EC: byequiv => //.
  byequiv
  -- EC: proc; inline*.
  equiv_proc; stmt_inline*
  -- EC: wp; call (_: true); auto => /> x _ [ c m d m' d'] /= comm comm' m_neq_m'.
  --     (GAP 6: the names; EC's `/>` closes the case where the binder's output does not verify)
  stmt_wp; equiv_call (_ : True); equiv_auto; auto_progress
  · rename_i _ x _ r _ comm comm' m_neq_m' _
    obtain ⟨c, μ, d, μ', d'⟩ := r
    simp only at comm comm' m_neq_m' ⊢
    -- EC: rewrite eq_sym eqT.
    --     have ->: (d - d') * inv (m' - m) = x <=> (d - d') = x * (m' - m).
    --     + by split => [<- | ->]; field; apply: contra m_neq_m' => heq;ring heq.
    --     have -> : d - d' = x * (m' - m) <=> d + x * m = d' + x * m'.
    --     + by split => heq; ring heq.
    --     by rewrite pow_bij !(expD, expM, -comm, -comm').
    --     (GAP 6: the same three steps, from the last: the exponents agree since the two
    --     openings give the same commitment)
    have key : d + x * μ = d' + x * μ' := by
      have h : (g : group) ^ (d + x * μ) = g ^ (d' + x * μ') := by
        rw [expD, expM, expD, expM, ← comm, ← comm']
      simpa [loggK] using congrArg loge h
    have hne : μ' - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm m_neq_m')
    simp only [← comm, ← comm', m_neq_m', ne_eq, not_false_eq_true, decide_true, Bool.and_self,
      true_iff, Option.some.injEq]
    rw [← div_eq_mul_inv, div_eq_iff hne]
    linear_combination key
  · rename_i h _
    simpa [and_assoc] using h

/-!
EC: "The following two are to compare probability directly with book discrete logarithm
experiment. Not strictly necessary though, only for completeness."
-/

/-- EC's `local lemma std_red_dl_bridge (B<:Binder) &m:
Pr[DL.DLog.DLogExperiment(DLogAttacker(B)).main() @ &m : res] <=
Pr[DL.DLog.DLogStdExperiment(DL.StdRedAdversary(DLogAttacker(B))).main() @ &m : res]`. -/
theorem std_red_dl_bridge : ∀ (B <: Binder), ∀ m : VariableAssignment,
    Pr[ DLog.DLog.DLogExperiment(DLogAttacker(B)).main () @ &m : §res ] ≤
      Pr[ DLog.DLog.DLogStdExperiment(DLog.StdRedAdversary(DLogAttacker(B))).main () @ &m :
        §res ] := by
  intro B m
  -- EC: byequiv => //.
  byequiv
  -- EC: proc; wp; inline{2} DL.StdRedAdversary(DLogAttacker(B)).guess; wp.
  --     (nothing for the two `wp` but the last assignment)
  equiv_proc; stmt_inline{2} (DLog.StdRedAdversary(DLogAttacker(B)).guess); stmt_wp
  -- EC: seq 2 3: (x'{1} = lx{2} /\ x{1} = x{2}).
  equiv_seq 2 3 : (§x'{1} = §lx{2} ∧ ={x})
  -- EC: + by inline*; wp; call (_: true); auto.
  · stmt_inline*; stmt_wp; equiv_call (_ : True); equiv_auto
  -- EC: by if{2}; auto => />; apply dt_ll.
  --     (`dt` is lossless by its hint; what EC's `/>` closes of the `else` branch is left)
  stmt_if{2} <;> equiv_auto
  smt_close [oget]

/-- EC's `lemma pedersen_std_computational_binding (B<:Binder) &m:
Pr[BindingExperiment(Pedersen, B).main() @ &m : res] <=
Pr[DL.DLog.DLogStdExperiment(DL.StdRedAdversary(DLogAttacker(B))).main() @ &m : res]`. -/
theorem pedersen_std_computational_binding : ∀ (B <: Binder), ∀ m : VariableAssignment,
    Pr[ BindingExperiment(Pedersen, B).main () @ &m : §res ] ≤
      Pr[ DLog.DLog.DLogStdExperiment(DLog.StdRedAdversary(DLogAttacker(B))).main () @ &m :
        §res ] := by
  -- EC: by rewrite(pedersen_computational_binding B &m); apply (std_red_dl_bridge B &m).
  intro B m; rw [pedersen_computational_binding B m]; exact std_red_dl_bridge B m

end PedersenSecurity

end GaudisCrypt.Examples.Pedersen
