import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Syntax.Clone
import GaudisCrypt.Language.Variables
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECSeq
import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Logic.ECInline
import GaudisCrypt.Logic.ECInlineParams
import GaudisCrypt.Logic.ECRnd
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECLoop
import GaudisCrypt.Logic.ECWhile
import GaudisCrypt.Logic.ECWhileRel
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.PHoareSeq
import GaudisCrypt.Logic.PHoareWhileRev
import GaudisCrypt.Lib.EC.Logic
import GaudisCrypt.Lib.EC.BitWord
import GaudisCrypt.Lib.EC.BitWordRing
import GaudisCrypt.Lib.EC.Bigop

/-!
# Private information retrieval (EasyCrypt `examples/PIR.ec`)

Two-server PIR: to read entry `i` of a database `a` replicated on two servers without either
server learning `i`, the client sends the first server a random subset `s` of the indices
`[0, N)` and the second server `s` with `i` flipped; each server returns the xor of the entries
it was asked for, and the two answers xor to `a i`.

EC's file, declaration by declaration and script line by line.  **In progress**: the first
half (to line 115) is here and proven — `sxor_cons`, `sxor2_cons`, `PIR_correct`,
`PIR_secure1`, `PIR_secure2`, `PIR_secuity_s_byequiv`, `PIR_secuity_s'_byequiv`.  Not yet
ported: the alternative proof (lines 117–383): the `restr` lemmas, `Pr_PIR_s`, `Pr_PIR_s'`,
`PIR_secuity_s_bypr`, `PIR_secuity_s'_bypr`, `PIR_s_uniform`, `PIR_s'_uniform`.  (The old port
of the whole file, in the style before the EC layer, is `Examples/EasyCryptBench/PIR.lean`.)

Translation:
* `clone import BitWord as BS`, `op N`, `op a`, `axiom N_pos` are the class `Params` (`n` the
  length of `BS.word`); `clone import Bigop as BBS` is a clone of `Lib/EC/Bigop.lean`.
* `var s, s' : int list` of `module PIR` are `global_var PIR.s`, `PIR.s'` before the module.
* `var j <- 0` is the declaration and the assignment `j <- 0`.

Gap list (what keeps the file from reading as EC's):
* GAP 1: `PIR_correct`'s `conseq (_: _ ==> sxor2 PIR.s PIR.s' i)` and the loop invariant carry
  `§i = i0`: the `post` goal of `hoare_conseq` and the loop rule's goals do not have the
  precondition's facts about unmodified variables (EC's `move=> &m ->`).
* GAP 2: `PIR_correct`'s loop body goal is closed by hand (EC: `smt(sxor2_cons)`,
  `smt(sxor_cons)`; `smt_close [sxor2_cons, sxor_cons]` does not see through `sxor2`); EC's
  `ring` on the two answers is the lemma `xorw_cancel`.
* GAP 3: `while (={j,PIR.s});auto` is `equiv_while (={j, PIR.s}) <;> equiv_auto`, then
  `auto_progress`; EC's `rnd (fun x => !x)` is `equiv_rnd (fun x => !x) (fun x => !x)`.
* The variant of pHL's `while (true) (N-j)` is a natural number: `(N - §j).toNat`.
-/

set_option ec.strict true
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace GaudisCrypt.Examples.PIR

open GaudisCrypt GaudisCrypt.EC

/-- The file's operators: the length `n` of words (EC's `clone import BitWord as BS`), the size
`N` of the database, and the database `a`. -/
class Params where
  /-- `BS.n`: the length of a word. -/
  n : ℤ
  gt0_n : 0 < n
  /-- `op N : int`. -/
  N : ℤ
  /-- The database: `op a : int -> word`. -/
  a : ℤ → BitWord.word n
  /-- `axiom N_pos : 0 <= N`. -/
  N_pos : 0 ≤ N

export Params (N a N_pos)

variable [Params]

/-- EC's `BS.word`. -/
abbrev word : Type := BitWord.word Params.n

-- EC: clone import Bigop as BBS with type t <- BS.word, op Support.idm <- BS.zerow,
--       op Support.( + ) <- BS.(+^) proof * by smt(xorwA xorwC xorw0).
clone import GaudisCrypt.EC.Bigop as BBS with
  type t <- word, op idm <- BitWord.zerow, op add <- BitWord.xorw
  proof * by first
    | exact BitWord.xorwA
    | exact BitWord.xorwC
    | exact fun x => by rw [BitWord.xorwC, BitWord.xorw0]

/-- EC's `pred sxor`. -/
def sxor (s s' : List ℤ) (i : ℤ) : Prop := ∃ s1 s2, s = s1 ++ s2 ∧ s' = s1 ++ i :: s2

/-- EC's `pred sxor2`. -/
def sxor2 (s s' : List ℤ) (i : ℤ) : Prop := sxor s s' i ∨ sxor s' s i

theorem sxor_cons (s : List ℤ) (i : ℤ) : sxor s (i :: s) i := by
  -- EC: by exists [] s.
  exact ⟨[], s, rfl, rfl⟩

theorem sxor2_cons (s s' : List ℤ) (i j : ℤ) : sxor2 s s' i → sxor2 (j :: s) (j :: s') i := by
  -- EC: move=> [].
  --       move=> [] s1 s2 [] -> ->.
  --       by left; exists (j :: s1) s2.
  --     + move=> [] s1 s2 [] -> ->.
  --       by right; exists (j :: s1) s2.
  rintro (⟨s1, s2, rfl, rfl⟩ | ⟨s1, s2, rfl, rfl⟩)
  · exact Or.inl ⟨j :: s1, s2, rfl, rfl⟩
  · exact Or.inr ⟨j :: s1, s2, rfl, rfl⟩

/-- EC's `ring` on the answers of `PIR_correct`. -/
theorem xorw_cancel (x y z : word) :
    (x +^ y +^ (x +^ (z +^ y)) = z) ∧ (x +^ (z +^ y) +^ (x +^ y) = z) := by
  constructor <;>
  · apply List.Vector.ext; intro k
    simp only [BitWord.xorwE]
    cases x.get k <;> cases y.get k <;> cases z.get k <;> rfl

global_var PIR.s : List ℤ
global_var PIR.s' : List ℤ

module PIR {
  proc query (s : List ℤ) : word {
    return big predT a $s
  };
  proc main (i : ℤ) : word {
    var r : word, r' : word, j : ℤ, b : Bool;
    j <- 0;
    PIR.s, PIR.s' <- ([], []);
    while ($j < N) {
      b <$ dbool;
      if ($j = $i) {
        if ($b) { PIR.s <- $j :: $PIR.s; } else { PIR.s' <- $j :: $PIR.s'; }
      } else {
        if ($b) { PIR.s <- $j :: $PIR.s; PIR.s' <- $j :: $PIR.s'; }
      }
      j <- $j + 1;
    }
    r <- call PIR.query ($PIR.s);
    r' <- call PIR.query ($PIR.s');
    return $r +^ $r'
  };
}

theorem PIR_correct (m : VariableAssignment) (i0 : ℤ) :
    0 ≤ i0 ∧ i0 < N → Pr[ PIR.main (i0) @ &m : §res = a i0 ] = 1 := by
  -- EC: move=> bound.
  intro bound
  -- EC: byphoare (_: i = i0 ==> res = a i0) => // {&m}.
  byphoare (: §i = i0 ==> _)
  -- EC: conseq (: _ ==> true) (: _ ==> res = a i0)=> //.
  phoare_proc; phoare_conseq (: _ ==> True) (: _ ==> _)
  · -- EC: + proc;inline *;wp.
    hoare_inline*; stmt_wp
    -- EC: conseq (_: _ ==> sxor2 PIR.s PIR.s' i) => //.
    hoare_conseq (: _ ==> sxor2 §PIR.s §PIR.s' §i ∧ §i = i0)
    · -- EC: + by move=> &m -> s s' [] [s1 s2 [-> ->]]; rewrite !big_cat big_consT; ring.
      rintro σ ⟨⟨s1, s2, h1, h2⟩ | ⟨s1, s2, h1, h2⟩, rfl⟩
      · have h1' : PIR.s.get σ.globals = _ := h1
        have h2' : PIR.s'.get σ.globals = _ := h2
        rw [h1', h2', big_cat, big_cat, big_consT]; exact (xorw_cancel _ _ _).1
      · have h1' : PIR.s'.get σ.globals = _ := h1
        have h2' : PIR.s.get σ.globals = _ := h2
        rw [h1', h2', big_cat, big_cat, big_consT]; exact (xorw_cancel _ _ _).2
    -- EC: while (j <= N /\ if j <= i then PIR.s = PIR.s' else sxor2 PIR.s PIR.s' i).
    hoare_while (§i = i0 ∧ §j ≤ N ∧ if §j ≤ §i then §PIR.s = §PIR.s' else sxor2 §PIR.s §PIR.s' §i)
    · -- EC: + wp;rnd;skip => /= &m [[_]] + HjN.
      --       have -> /= : j{m} + 1 <= N by smt ().
      --       case: (j{m} <= i{m})=> Hji; 2:smt(sxor2_cons).
      --       move=> -> b _;case: (j{m} = i{m}) => [->> | /#].
      --       by rewrite (_ : !(i{m}+1 <= i{m})) 1:/# /=; smt (sxor_cons).
      hoare_auto
      rintro i j s s' ⟨⟨rfl, -, hI⟩, hj⟩ b -
      have hj' : j < N := of_decide_eq_true hj
      simp only [ite_self, true_and]
      refine ⟨by omega, ?_⟩
      rcases lt_trichotomy j i with h | rfl | h
      · have h1 : j ≠ i := by omega
        rw [if_pos (by omega)] at hI
        simp [h1, show j + 1 ≤ i by omega, hI]
      · rw [if_pos le_rfl] at hI
        cases b <;> simp [hI, sxor2, sxor_cons]
      · have h1 : j ≠ i := by omega
        rw [if_neg (by omega)] at hI
        cases b <;> simp [h1, show ¬ j + 1 ≤ i by omega, hI, sxor2_cons]
    · smt_close []
    -- EC: by auto => /#.
    hoare_auto
    smt_close []
  -- EC: proc;inline *;wp.
  phoare_inline*; stmt_wp
  -- EC: while (true) (N-j).
  phoare_while (True) ((N - §j).toNat)
  · -- EC: + move=> z;wp;rnd predT;skip => &hr />;smt (dbool_ll).
    intro z; phoare_auto
    smt_close [dbool_ll]
  -- EC: by auto=> /#.
  phoare_auto

theorem PIR_secure1 : equiv[ PIR.main ~ PIR.main : True ==> ={PIR.s} ] := by
  -- EC: proc;inline *;wp.
  equiv_proc; stmt_inline*; stmt_wp
  -- EC: while (={j,PIR.s});auto.
  equiv_while (={j, PIR.s}) <;> equiv_auto
  auto_progress

theorem PIR_secure2 : equiv[ PIR.main ~ PIR.main : True ==> ={PIR.s'} ] := by
  -- EC: proc;inline *;wp.
  equiv_proc; stmt_inline*; stmt_wp
  -- EC: while (={j,PIR.s'});2: by auto.
  equiv_while (={j, PIR.s'})
  case hpre => equiv_auto
  -- EC: wp; case: ((j = i){1} = (j = i){2}).
  stmt_wp; equiv_case ((§j{1} = §i{1}) = (§j{2} = §i{2}))
  · -- EC: + auto;smt (dbool_funi dbool_fu).
    equiv_auto
  -- EC: rnd (fun x => !x);skip;smt (dbool_funi dbool_fu).
  equiv_rnd (fun x => !x) (fun x => !x); equiv_auto
  smt_close []

theorem PIR_secuity_s_byequiv (i1 i2 : ℤ) (m1 m2 : VariableAssignment) (x : List ℤ) :
    Pr[ PIR.main (i1) @ &m1 : §PIR.s = x ] = Pr[ PIR.main (i2) @ &m2 : §PIR.s = x ] := by
  -- EC: by byequiv PIR_secure1.
  byequiv (PIR_secure1)

theorem PIR_secuity_s'_byequiv (i1 i2 : ℤ) (m1 m2 : VariableAssignment) (x : List ℤ) :
    Pr[ PIR.main (i1) @ &m1 : §PIR.s' = x ] = Pr[ PIR.main (i2) @ &m2 : §PIR.s' = x ] := by
  -- EC: by byequiv PIR_secure2.
  byequiv (PIR_secure2)

end GaudisCrypt.Examples.PIR
