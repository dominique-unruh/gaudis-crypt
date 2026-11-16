import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Syntax.Clone
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.PHoareSeq
import GaudisCrypt.Logic.PHoareWhileRev
import GaudisCrypt.Logic.PHoareExactTactics
import GaudisCrypt.Logic.ByPrEquiv
import GaudisCrypt.Lib.EC.Logic
import GaudisCrypt.Lib.EC.DUniform
import GaudisCrypt.Lib.EC.DBoolBiased

/-!
# Von Neumann's trick (EasyCrypt `examples/vonNeumann.eca`)

EC: "In this theory, we illustrate some reasoning on distributions on Von Neumann's trick to
simulate a fair coin toss using only a biased coin (of unknown bias)."  Two flips of the biased
coin are repeated until they differ, and the first is returned: `Simulate.sample` returns each
bit with the probability of a fair coin (`Simulate_is_Fair`).

EC's file, declaration by declaration and script line by line.  All of EC's lemmas are proven.

Translation:
* `op p : { real | 0%r < p < 1%r } as in01_p` is the class `Params`; `clone import FixedBiased
  as Biased with op p <- p` is a clone of `Lib/EC/DBoolBiased.lean`.
* `duniform`, `duniform1E`, `duniformE` are `Lib/EC/DUniform.lean`; `b2r (a <> b)` is
  `if a ≠ b then 1 else 0`, `b2i (b = b')` is `if §b = §b' then 1 else 0`, `pred1 x \o fst` is
  `pred1 x ∘ Prod.fst`.
* pHL's bounds are reals, as EC's.

Gap list (what keeps the file from reading as EC's):
* GAP 1: EC's `equiv SamplePair` is `SamplePair_Fair` (a module and a lemma cannot share a
  name).
* GAP 2: `bypr (res{1}) (res{2})=> // &1 &2 b0` introduces the arguments and the memories
  (`intro a1 m1 a2 m2 b0 _`); EC's `have ->: Pr[Fair.sample() @ &2 : res = b0] = 1%r/2%r` is a
  `have` used by transitivity (the goal's `Pr` is about the argument `a2`, a variable, until
  `cases`).
* GAP 3: `byphoare (: True ==> _)` for EC's `byphoare (_: true ==> res = x)=> //` (the
  postcondition is the event's); `conseq (: _: = e)` is `phoare_conseq (: _ ==> _ : = e)`.
* GAP 4: `vn_fst` (`mu dvn (pred1 x ∘ Prod.fst) = 1/2`) is stated once; EC rewrites `vnE` and
  counts at its two uses.
* GAP 5: after `rnd E; auto` the goals `mu d E = … ∧ ∀ v ∈ d, …` are
  `smt_close [mu_pred1, pred1E]`, with `dbiased1E` where EC has `rewrite dbiasedE`; three of
  them (`rnd (pred1 (!x)); auto=> /#`, a case analysis on booleans) and the conditions of
  three `conseq ih=> /#` are by hand, as is the bounds' equation of `Simulate_is_Fair`
  (`dbiased1E` and `ring`; EC: `smt`).
* GAP 6: the rule for `while I V k ε` has two goals more than EC's (`bound_le_one`, `sat`), and
  `rate` (`0 < 2 p (1 - p)`), which EC's `=> />` leaves in a conjunction; `seq 1: b p (1%r - p)
  (1%r - p) p` leaves `0 ≤ pᵢ` (`nonneg`) when `positivity` does not find it.
-/

set_option ec.strict true
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace GaudisCrypt.Examples.VonNeumann

open GaudisCrypt GaudisCrypt.EC

module Fair {
  proc sample () : Bool {
    var b : Bool;
    b <$ dbool;
    return $b
  };
}

/-- EC's `op p : { real | 0%r < p < 1%r } as in01_p`. -/
class Params where
  p : ℝ
  in01_p : 0 < p ∧ p < 1

export Params (p in01_p)

variable [Params]

-- EC: clone import FixedBiased as Biased with op p <- p proof *.
--     realize in01_p by apply/in01_p.
clone import GaudisCrypt.EC.FixedBiased as Biased with
  op p <- p
  proof * by exact in01_p

module Simulate {
  proc sample () : Bool {
    var b : Bool, b' : Bool;
    b <- true;
    b' <- true;
    while (decide ($b = $b')) {
      b <$ dbiased;
      b' <$ dbiased;
    }
    return $b
  };
}

/-- EC's `op svn = [(true, false); (false, true)]`. -/
def svn : List (Bool × Bool) := [(true, false), (false, true)]

/-- EC's `op dvn = duniform svn`. -/
noncomputable def dvn : SubProbability (Bool × Bool) := duniform svn

theorem vn1E (a b : Bool) : mu1 dvn (a, b) = (1 / 2) * (if a ≠ b then 1 else 0) := by
  -- EC: by rewrite duniform1E; case: a b => [] [] @/svn.
  rw [dvn, duniform1E]; cases a <;> cases b <;> simp [svn, undup, size]

theorem vnE (E : Bool × Bool → Prop) [DecidablePred E] :
    mu dvn E = 1 / 2 * (count E svn : ℝ) := by
  -- EC: by rewrite duniformE /= (_ : undup svn = svn).
  rw [dvn, duniformE, show undup svn = svn from by decide]
  simp [svn, size]; ring

module SamplePair {
  proc sample () : Bool {
    var b : Bool, b' : Bool;
    b, b' <$ dvn;
    return $b
  };
}

/-- Each value of the first coin has probability `1/2` under `dvn` (EC proves it where it is
used: `rewrite vnE; pose c := count _ _; …`, `rewrite !vnE /svn …`). -/
theorem vn_fst (x : Bool) : mu dvn (pred1 x ∘ Prod.fst) = 1 / 2 := by
  classical
  rw [vnE]; cases x <;> simp [count, svn, pred1]

theorem SamplePair_Fair : equiv[ SamplePair.sample ~ Fair.sample : True ==> ={res} ] := by
  -- EC: bypr (res{1}) (res{2})=> // &1 &2 b0.
  bypr (res{1}) (res{2})
  intro a1 m1 a2 m2 b0 _
  -- EC: have ->: Pr[Fair.sample() @ &2: res = b0] = 1%r/2%r.
  --      byphoare (_: true ==> res = b0)=> //.
  --      by proc; rnd (pred1 b0); skip=> />; rewrite dbool1E.
  have h : Pr[ Fair.sample () @ &m2 : §res = b0 ] = 1 / 2 := by
    byphoare (: True ==> _)
    phoare_proc; phoare_rnd (pred1 b0); phoare_auto
    smt_close [mu_pred1, dbool1E_mu1, pred1E]
  cases a1; cases a2
  refine (?_ : _ = (1 / 2 : ℝ)).trans h.symm
  -- EC: byphoare (_: true ==> res = b0)=> //.
  --     proc; rnd ((pred1 b0) \o fst); skip => />.
  byphoare (: True ==> _)
  phoare_proc; phoare_rnd (pred1 b0 ∘ Prod.fst); phoare_auto
  -- EC: rewrite vnE; pose c := count _ _; suff ->//: c%r = 1%r.
  --     by move=> @/c; case: {+}b0.
  exact ⟨vn_fst b0, fun v _ => Iff.rfl⟩

/-! We can now prove that sampling a pair in the restricted distribution and flipping two coins
independently until they are distinct, returning the first one, are equivalent. -/

theorem Simulate_is_Fair (x : Bool) (m : VariableAssignment) :
    Pr[ Simulate.sample () @ &m : §res = x ] = Pr[ Fair.sample () @ &m : §res = x ] := by
  -- EC: have <-:
  --         Pr[SamplePair.sample() @ &m: res = x]
  --       = Pr[Fair.sample() @ &m: res = x].
  --     + by byequiv SamplePair.
  have h1 : Pr[ SamplePair.sample () @ &m : §res = x ] =
      Pr[ Fair.sample () @ &m : §res = x ] := by
    byequiv (SamplePair_Fair)
  rw [← h1]
  -- EC: have ->:
  --         Pr[SamplePair.sample() @ &m: res = x]
  --       = mu dvn (pred1 x \o fst).
  --     + byphoare (_: true ==> res = x)=> //.
  --       by proc; rnd (pred1 x \o fst); skip=> />.
  have h2 : Pr[ SamplePair.sample () @ &m : §res = x ] = mu dvn (pred1 x ∘ Prod.fst) := by
    byphoare (: True ==> _)
    case hx => exact ge0_mu _ _
    phoare_proc; phoare_rnd (pred1 x ∘ Prod.fst); phoare_auto
  rw [h2]
  -- EC: byphoare (_: true ==> res = x)=> //; proc; sp.
  byphoare (: True ==> _)
  case hx => exact ge0_mu _ _
  phoare_proc; stmt_sp
  -- EC: conseq (: _: =(if b = b' then mu dvn (pred1 x \o fst) else b2r (b = x)))=> //.
  phoare_conseq (: _ ==> _ : =
    (if §b = §b' then mu dvn (pred1 x ∘ Prod.fst) else if §b = x then 1 else 0))
  · rintro b b' ⟨rfl, rfl⟩; simp
  -- EC: conseq (: true ==> _).
  phoare_conseq (: True ==> _)
  -- EC: while true (b2i (b = b')) 1 (2%r * p * (1%r - p))=> />.
  phoare_while (True) (if §b = §b' then 1 else 0) 1 (2 * p * (1 - p))
  · intro b b' h
    rw [if_neg (of_decide_eq_false h)]
    by_cases hb : b = x <;> simp [hb, indicatorE]
  · -- EC: + by move=> /#.
    smt_close
  · -- EC: + move=> ih.
    intro w ih
    -- EC: seq 1: (b = x) (mu1 dbiased x)
    --       (mu1 dbiased (!x) + mu1 dbiased x * mu dvn (pred1 x \o fst))
    --       (mu1 dbiased (!x)) (mu1 dbiased (!x) * mu dvn (pred1 x \o fst))=> //.
    phoare_seq 1 : (§b = x) (mu1 dbiased x)
      (mu1 dbiased (!x) + mu1 dbiased x * mu dvn (pred1 x ∘ Prod.fst))
      (mu1 dbiased (!x)) (mu1 dbiased (!x) * mu dvn (pred1 x ∘ Prod.fst))
    · -- EC: + by rnd (pred1 x); auto=> />; rewrite dbiased.
      phoare_rnd (pred1 x); phoare_auto
      smt_close [mu_pred1, pred1E]
    · -- EC: + seq 1: (b' = !x) (mu1 dbiased (!x)) 1%r (mu1 dbiased x)
      --         (mu dvn (pred1 x \o fst)) (b = x)=> //.
      phoare_seq 1 : (§b' = !x) (mu1 dbiased (!x)) 1 (mu1 dbiased x)
        (mu dvn (pred1 x ∘ Prod.fst)) (§b = x)
      · -- EC: + by auto.
        hoare_auto
      · -- EC: + by rnd (pred1 (!x)); auto.
        phoare_rnd (pred1 (!x)); phoare_auto
        smt_close [mu_pred1, pred1E]
      · -- EC: + by conseq ih=> />; rewrite -negbDR.
        phoare_conseq ih
        smt_close
      · -- EC: + by rnd (pred1 x); auto=> /#.
        phoare_rnd (pred1 x); phoare_auto
        exact fun _ _ => ⟨mu_pred1 _ _, fun v _ => by cases v <;> cases x <;> simp [pred1]⟩
      · -- EC: conseq ih=> /> &0.
        --     rewrite ge0_mu /= => -> /#.
        phoare_conseq ih
        rintro b' b ⟨h, rfl⟩; cases b' <;> cases b <;> simp_all
    · -- EC: + by rnd (pred1 (!x)); auto=> /#.
      phoare_rnd (pred1 (!x)); phoare_auto
      exact fun _ _ _ =>
        ⟨mu_pred1 _ _, fun v _ => by cases v <;> cases x <;> simp [pred1]⟩
    · -- EC: + seq 1: (b' = x) _ 0%r (mu1 dbiased (!x)) (mu dvn (pred1 x \o fst))
      --         (b <> x)=> //.
      phoare_seq 1 : (§b' = x) _ 0 (mu1 dbiased (!x)) (mu dvn (pred1 x ∘ Prod.fst)) (§b ≠ x)
      · -- EC: + by auto.
        hoare_auto
      · -- EC: + by conseq ih=> /> &0 ->.
        phoare_conseq ih
        rintro b' b ⟨rfl, h⟩; cases b' <;> cases b <;> simp_all
      · -- EC: + by rnd (pred1 (!x)); auto=> /#.
        phoare_rnd (pred1 (!x)); phoare_auto
        exact fun _ _ => ⟨mu_pred1 _ _, fun v _ => by cases v <;> cases x <;> simp [pred1]⟩
      · -- EC: conseq ih=> /> &0.
        --     rewrite ge0_mu /= => /#.
        phoare_conseq ih
        rintro b' b ⟨h1, h2⟩; cases b' <;> cases b <;> cases x <;> simp_all
    -- EC: move=> {ih} _ -> /=; rewrite !vnE /svn /(\o)/ pred1 /= /b2i /=.
    --     by move: x=> [] /=; rewrite !dbiased1E /#.
    intro b b' h
    rw [if_pos (of_decide_eq_true h), vn_fst, dbiased1E, dbiased1E]
    cases x <;> simp <;> ring
  · -- EC: + by auto=> />; rewrite dbiased_ll.
    phoare_auto
    smt_close [dbiased_ll]
  · have := in01_p (self := ‹_›)
    exact mul_pos (mul_pos two_pos this.1) (by linarith)
  · -- EC: split => //= [|z]; first by smt w=(in01_p).
    --     conseq (_: true ==> b <> b'); first by move=> /#.
    intro z
    phoare_conseq (: True ==> §b ≠ §b')
    · smt_close
    -- EC: seq 1: b p (1%r - p) (1%r - p) p=> //.
    phoare_seq 1 : (§b) p (1 - p) (1 - p) p
    · -- EC: + by rnd; skip=> />; rewrite dbiasedE.
      phoare_rnd (pred1 true); phoare_auto
      smt_close [mu_pred1, dbiased1E, pred1E]
    · -- EC: + by rnd; skip=> />; rewrite dbiasedE.
      phoare_rnd (pred1 false); phoare_auto
      smt_close [mu_pred1, dbiased1E, pred1E]
    · -- EC: + by rnd; skip=> />; rewrite dbiasedE.
      phoare_rnd (pred1 false); phoare_auto
      smt_close [mu_pred1, dbiased1E, pred1E]
    · -- EC: + by rnd; skip=> /> &hr _; rewrite dbiasedE.
      phoare_rnd (pred1 true); phoare_auto
      smt_close [mu_pred1, dbiased1E, pred1E]
    · -- EC: smt(in01_p).
      smt_close [in01_p]
    · smt_close [in01_p]
  · intro b b'
    rw [ENNReal.ofReal_le_one]
    split_ifs
    · exact le1_mu _ _
    · exact le_rfl
    · exact zero_le_one
  · exact ⟨(localVarLens "b" Bool).set x ⟨VariableAssignment.init, VariableAssignment.init⟩,
      indicatorE_of (Lens.set_get _ _ _)⟩

end GaudisCrypt.Examples.VonNeumann
