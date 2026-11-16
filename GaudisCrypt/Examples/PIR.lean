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
import GaudisCrypt.Logic.ECWhileHoare
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.PHoareSeq
import GaudisCrypt.Logic.PHoareWhileRev
import GaudisCrypt.Logic.PHoareExactTactics
import GaudisCrypt.Lib.EC.Logic
import GaudisCrypt.Lib.EC.BitWord
import GaudisCrypt.Lib.EC.BitWordRing
import GaudisCrypt.Lib.EC.Bigop
import GaudisCrypt.Lib.EC.FSetOflist

/-!
# Private information retrieval (EasyCrypt `examples/PIR.ec`)

Two-server PIR: to read entry `i` of a database `a` replicated on two servers without either
server learning `i`, the client sends the first server a random subset `s` of the indices
`[0, N)` and the second server `s` with `i` flipped; each server returns the xor of the entries
it was asked for, and the two answers xor to `a i`.

EC's file, declaration by declaration and script line by line: correctness (`PIR_correct`),
security by a coupling (`PIR_secure1`, `PIR_secure2` and the two `byequiv` lemmas), the
probability of each query computed in pHL (`Pr_PIR_s`, `Pr_PIR_s'` and the two `bypr` lemmas),
and the uniformity equivalences (`PIR_s_uniform`, `PIR_s'_uniform`).  All of EC's lemmas are
proven.

Translation:
* `clone import BitWord as BS`, `op N`, `op a`, `axiom N_pos` are the class `Params` (`n` the
  length of `BS.word`); `clone import Bigop as BBS` is a clone of `Lib/EC/Bigop.lean`.
* `var s, s' : int list` of `module PIR` are `global_var PIR.s`, `PIR.s'` before the module.
* `var j <- 0` is the declaration and the assignment `j <- 0`.
* pHL's bounds are reals, as EC's: `1 / 2 ^ (N - §j)` is `1%r/2%r^(N-j)` (an integer power).
* `int fset` is `FSet ℤ` (`Finset`), `` `|` `` and `` `&` `` are `∪` and `∩`, `oflist` and the
  membership lemmas are `Lib/EC/FSetOflist.lean`; `b ^^ (j \in x1)` is
  `b ^^ decide (j ∈ x1)`.

Gap list (what keeps the file from reading as EC's):
* GAP 1 (closed 2026-11-16): `PIR_correct`'s `conseq (_: _ ==> sxor2 PIR.s PIR.s' i)` and its
  `while` are EC's: `hoare_conseq` and `hoare_while` keep what the precondition says of the
  variables the code does not modify (`i = i0`), as EC's do.
* GAP 2: `PIR_correct`'s loop body is one `smt_close [sxor2_cons, sxor_cons]` where EC takes
  the cases apart first (`case: (j{m} <= i{m})`, …); EC's `ring` on the two answers is the
  lemma `xorw_cancel`.
* GAP 3: `while (={j,PIR.s});auto` is `equiv_while (={j, PIR.s}) <;> equiv_auto`, then
  `auto_progress`; EC's `rnd (fun x => !x)` is `equiv_rnd (fun x => !x) (fun x => !x)`.
* The variant of pHL's `while (true) (N-j)` is a natural number: `(N - §j).toNat`.
* GAP 4: the `restr` lemmas are proven from `mem_restr` (membership in `restr s n`) where EC
  rewrites with `FSet` lemmas and calls `smt`.  In `PIR_s_uniform`, `PIR_s'_uniform` the
  conditions of `rnd` are split by hand as in EC (EC's two `ring` are a case analysis on the
  booleans), and EC's `rewrite !oflist_cons !restrS //` goes into the hints of `smt_close`.
* GAP 5 (closed 2026-11-16): `(s, s') <- ([], [])` is EC's tuple assignment (the condition
  `sp` leaves on the pair is taken apart by the closer).
* GAP 6 (`Pr_PIR_s`, `Pr_PIR_s'`): `byphoare (: True ==> _)` for EC's `byphoare=> //` (the
  default precondition fixes the argument and the memory); `case: (is_restr x N)` is
  `by_cases`; the rule for `while I V k ε` has two goals more than EC's (`bound_le_one`,
  `sat`: `Logic/PHoareWhileRev.lean`); `exists * j, PIR.s; elim * => j0 s0` is two
  `stmt_exists *`; EC's `smt (…)` on the `restr` lemmas are `smt_close […]` with
  EC's hints, the rewrites that precede them (`rewrite oflist_cons`, `rewrite -set0E`) added
  to the hints; one hint list differs (the `¬ E` bound of the second `seq`: EC's membership
  lemmas `in_fsetU in_fset1 nin_is_restr` are `is_restr_diff is_restr_Ueq is_restr_restr`),
  and `ENNReal.ofReal_zero` is a hint where the bound is `0`.  By hand: the two goals of the
  loop rule that EC does not have, `pre_bound` (EC: `have ->>: j = N by smt()`), the `variant`
  goal (EC: `smt (dbool_ll)`), and the final equation on powers of two (EC: `rewrite -exprS`,
  `ring`).
-/

set_option ec.strict true
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace GaudisCrypt.Examples.PIR

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet

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
    (PIR.s, PIR.s') <- ([], []);
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
    hoare_conseq (: _ ==> sxor2 §PIR.s §PIR.s' §i)
    · -- EC: + by move=> &m -> s s' [] [s1 s2 [-> ->]]; rewrite !big_cat big_consT; ring.
      rintro σ hσ τ ⟨hi, -⟩ (⟨s1, s2, h1, h2⟩ | ⟨s1, s2, h1, h2⟩) <;> obtain rfl := hi.trans hσ
      · have h1' : PIR.s.get τ.globals = _ := h1
        have h2' : PIR.s'.get τ.globals = _ := h2
        rw [h1', h2', big_cat, big_cat, big_consT]; exact (xorw_cancel _ _ _).1
      · have h1' : PIR.s'.get τ.globals = _ := h1
        have h2' : PIR.s.get τ.globals = _ := h2
        rw [h1', h2', big_cat, big_cat, big_consT]; exact (xorw_cancel _ _ _).2
    -- EC: while (j <= N /\ if j <= i then PIR.s = PIR.s' else sxor2 PIR.s PIR.s' i).
    hoare_while (§j ≤ N ∧ if §j ≤ §i then §PIR.s = §PIR.s' else sxor2 §PIR.s §PIR.s' §i)
    · -- EC: + wp;rnd;skip => /= &m [[_]] + HjN.
      --       have -> /= : j{m} + 1 <= N by smt ().
      --       case: (j{m} <= i{m})=> Hji; 2:smt(sxor2_cons).
      --       move=> -> b _;case: (j{m} = i{m}) => [->> | /#].
      --       by rewrite (_ : !(i{m}+1 <= i{m})) 1:/# /=; smt (sxor_cons).
      hoare_auto
      smt_close [sxor2_cons, sxor_cons]
    -- EC: by auto => /#.
    hoare_auto
    smt_close
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

/-!
Alternative proof: we show that the distribution of `PIR.s` and `PIR.s'` is uniform.  First
version: we use `phoare`.
-/

/-- EC's `op restr (s : int fset) n = s `&` oflist (iota_ 0 n)`. -/
def restr (s : FSet ℤ) (n : ℤ) : FSet ℤ := s ∩ oflist (iota_ 0 n)

/-- EC's `op is_restr (s : int fset) n = s = restr s n`. -/
def is_restr (s : FSet ℤ) (n : ℤ) : Prop := s = restr s n

instance (s : FSet ℤ) (n : ℤ) : Decidable (is_restr s n) := by unfold is_restr; infer_instance

/-- Membership in `restr s n` (EC's `rewrite /restr in_fsetI mem_oflist mem_iota`). -/
theorem mem_restr (s : FSet ℤ) (n x : ℤ) : x ∈ restr s n ↔ x ∈ s ∧ 0 ≤ x ∧ x < n := by
  rw [restr, in_fsetI, mem_oflist, mem_iota, zero_add]

theorem restrS (s : FSet ℤ) (j : ℤ) : 0 ≤ j →
    restr s (j + 1) = (if j ∈ s then fset1 j else fset0) ∪ restr s j := by
  -- EC: move=> H0j;rewrite /restr iotaSr //= -cats1 oflist_cat.
  --     by rewrite fsetUC fsetIUr -set1E fsetI1.
  intro H0j; ext x
  rw [in_fsetU, mem_restr, mem_restr]
  split_ifs with h
  · rw [in_fset1]; constructor
    · rintro ⟨h1, h2, h3⟩; by_cases hx : x = j
      · exact Or.inl hx
      · exact Or.inr ⟨h1, h2, by omega⟩
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨h, H0j, by omega⟩
      · exact ⟨h1, h2, by omega⟩
  · rw [in_fset0, false_or]; constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, lt_of_le_of_ne (by omega) fun hx => h (hx ▸ h1)⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by omega⟩

theorem nin_is_restr (n : ℤ) (s : FSet ℤ) : is_restr s n → ¬ n ∈ s := by
  -- EC: by move=> ->;rewrite /restr in_fsetI mem_oflist mem_iota.
  intro h hn; rw [h, mem_restr] at hn; omega

theorem is_restr_diff (n : ℤ) (s1 s2 : FSet ℤ) : is_restr s2 n → fset1 n ∪ s1 ≠ s2 := by
  -- EC: move => /nin_is_restr Hs2;apply contraT => Heq.
  --     rewrite /= in Heq;subst s2.
  --     by apply Hs2;rewrite in_fsetU in_fset1.
  intro Hs2 Heq; subst Heq
  exact nin_is_restr _ _ Hs2 (by rw [in_fsetU, in_fset1]; exact Or.inl rfl)

theorem is_restr_Ueq (n : ℤ) (s1 s2 : FSet ℤ) : is_restr s1 n → is_restr s2 n →
    (fset1 n ∪ s1 = fset1 n ∪ s2) = (s1 = s2) := by
  -- EC: move=> Hs1 Hs2;rewrite eq_iff;split => [ | -> //].
  --     rewrite !fsetP => H x; have := H x.
  --     rewrite !in_fsetU in_fset1;case: (x = n) => /= [-> | //].
  --     by rewrite !nin_is_restr.
  intro Hs1 Hs2; apply propext; constructor
  · rw [fsetP, fsetP]; intro H x; have := H x
    rw [in_fsetU, in_fsetU, in_fset1] at this
    by_cases hx : x = n
    · subst hx; simp [nin_is_restr _ _ Hs1, nin_is_restr _ _ Hs2]
    · simpa [hx] using this
  · rintro rfl; rfl

theorem is_restr_addS (n : ℤ) (s : FSet ℤ) : 0 ≤ n → is_restr s n →
    is_restr (fset1 n ∪ s) (n + 1) := by
  -- EC: move=> Hn Hs;apply fsetP => x.
  --     rewrite /restr !inE Hs !(in_fsetI, mem_oflist, mem_iota) /#.
  intro Hn Hs; rw [is_restr, fsetP]; intro x
  rw [mem_restr, in_fsetU, in_fset1]
  constructor
  · rintro (rfl | hx)
    · exact ⟨Or.inl rfl, Hn, by omega⟩
    · have := (mem_restr s n x).mp (Hs ▸ hx); exact ⟨Or.inr hx, this.2.1, by omega⟩
  · exact fun h => h.1

theorem is_restrS (n : ℤ) (s : FSet ℤ) : 0 ≤ n → is_restr s n → is_restr s (n + 1) := by
  -- EC: by move=> Hn Hs; rewrite /is_restr restrS // (@nin_is_restr _ _ Hs) /= fset0U.
  intro Hn Hs
  rw [is_restr, restrS _ _ Hn, if_neg (nin_is_restr _ _ Hs), fset0U]; exact Hs

theorem is_restr_restr (n : ℤ) (s : FSet ℤ) : is_restr (restr s n) n := by
  -- EC: apply fsetP => x;rewrite /restr !in_fsetI !mem_oflist /#.
  rw [is_restr, fsetP]; intro x; simp only [mem_restr]; tauto

theorem is_restr_fset0 (n : ℤ) : is_restr fset0 n := by
  -- EC: by apply fsetP => x;rewrite /restr in_fsetI in_fset0.
  rw [is_restr, fsetP]; intro x; rw [mem_restr, in_fset0]; tauto

theorem restr_0 (s : FSet ℤ) : restr s 0 = fset0 := by
  -- EC: apply fsetP => x;rewrite /restr in_fsetI in_fset0 mem_oflist mem_iota /#.
  rw [fsetP]; intro x; rw [mem_restr, in_fset0]; constructor
  · rintro ⟨-, h1, h2⟩; omega
  · exact False.elim

theorem Pr_PIR_s (i0 : ℤ) (m : VariableAssignment) (x : FSet ℤ) :
    Pr[ PIR.main (i0) @ &m : oflist §PIR.s = x ] =
      if is_restr x N then 1 / 2 ^ N else 0 := by
  -- EC: byphoare=> // {i0};proc;inline *;wp.
  byphoare (: True ==> _); phoare_proc; phoare_inline*; stmt_wp
  -- EC: case: (is_restr x N);first last.
  by_cases hx : is_restr x N
  rotate_left
  · -- EC: + conseq (_ : _ ==> _ : = 0%r) => [ _ | ].
    --       + smt(expr_ge0 divr_ge0).
    phoare_conseq (: _ ==> _ : = 0)
    · simp [hx]
    -- EC: hoare;conseq (_ : _ ==> is_restr (oflist PIR.s) N); 1:by smt().
    phoare_hoare
    hoare_conseq (: _ ==> is_restr (oflist §PIR.s) N)
    · smt_close
    -- EC: while (0<= j <= N /\ is_restr (oflist PIR.s) j).
    hoare_while (0 ≤ §j ∧ §j ≤ N ∧ is_restr (oflist §PIR.s) §j)
    · -- EC: + by auto => &m1 />;rewrite oflist_cons;smt (is_restrS is_restr_addS).
      hoare_auto
      smt_close [oflist_cons, is_restrS, is_restr_addS]
    -- EC: auto=> ?;rewrite -set0E;smt (is_restr_fset0 N_pos).
    hoare_auto
    smt_close [set0E, is_restr_fset0, N_pos]
  -- EC: sp; conseq (_ : _ ==> _ : = (if (oflist PIR.s) = restr x j then 1%r/2%r^(N-j)
  --       else 0%r)).
  stmt_sp
  phoare_conseq (: _ ==> _ : = (if oflist §PIR.s = restr x §j then 1 / 2 ^ (N - §j) else 0))
  · -- EC: + move=> {&m} &m />;rewrite -set0E.
    --       split.
    --       + smt(expr_ge0 invr_ge0).
    --       have -> // : fset0 = restr x 0.
    --       + by apply fsetP=> z;rewrite /restr !inE mem_oflist mem_iota /#.
    smt_close [restr_0, set0E]
  -- EC: conseq (_ : _ ==> oflist PIR.s = restr x j) (_: _ ==> j = N) => //;1:smt().
  phoare_conseq (: _ ==> oflist §PIR.s = restr x §j) (: _ ==> §j = N)
  · smt_close
  · -- EC: + while(0 <= j <= N);auto;smt (N_pos).
    hoare_while (0 ≤ §j ∧ §j ≤ N) <;> hoare_auto <;> smt_close [N_pos]
  -- EC: conseq (: (0 <= j <= N /\ is_restr (oflist PIR.s) j) ==> _) => //.
  phoare_conseq (: 0 ≤ §j ∧ §j ≤ N ∧ is_restr (oflist §PIR.s) §j ==> _)
  · -- EC: + move=> />; smt(N_pos set0E is_restr_fset0).
    smt_close [N_pos, set0E, is_restr_fset0]
  -- EC: while (0 <= j <= N /\ is_restr (oflist PIR.s) j) (N-j) N 1%r => //.
  phoare_while (0 ≤ §j ∧ §j ≤ N ∧ is_restr (oflist §PIR.s) §j) (N - §j) N 1
  · -- EC: + move=> /> s j *; have ->>: j = N by smt().
    --       by rewrite subzz expr0.
    rintro j s ⟨H0j, HjN, Hs⟩ Hj
    obtain rfl : j = N := le_antisymm HjN (not_lt.mp (of_decide_eq_false Hj))
    by_cases h : oflist s = restr x N <;> simp [h, indicatorE]
  · -- EC: + smt(N_pos).
    smt_close [N_pos]
  · -- EC: + move=> H.
    intro w H
    -- EC: case (oflist PIR.s = restr x j);first last.
    phoare_case (oflist §PIR.s = restr x §j)
    rotate_left
    · -- EC: + seq 3 : true _ 0%r 0%r _ (0 <= j <= N /\ is_restr (oflist PIR.s) j /\
      --         oflist PIR.s <> restr x j).
      phoare_seq 3 : (True) _ 0 0 _
        (0 ≤ §j ∧ §j ≤ N ∧ is_restr (oflist §PIR.s) §j ∧ oflist §PIR.s ≠ restr x §j)
      · -- EC: + auto => /> &hr H0j ???? b ?.
        --       rewrite restrS //= oflist_cons.
        --       smt (is_restr_addS is_restrS is_restr_Ueq  is_restr_diff fset0U
        --         is_restr_restr).
        hoare_auto
        smt_close [restrS, oflist_cons, is_restr_addS, is_restrS, is_restr_Ueq, is_restr_diff,
          fset0U, is_restr_restr]
      · -- EC: by conseq H=> /#.
        phoare_conseq H
        · smt_close
        · smt_close [ENNReal.ofReal_zero]
      · -- EC: + by hoare;auto.
        phoare_hoare; hoare_auto
      -- EC: smt().
      smt_close
    -- EC: conseq (_ : _ : = (1%r / 2%r ^ (N - j))).
    --     + smt(divr_ge0 expr_ge0).
    phoare_conseq (: _ ==> _ : = (1 / 2 ^ (N - §j)))
    · smt_close
    -- EC: exists * j, PIR.s;elim * => j0 s0.
    stmt_exists * §j
    intro j0
    stmt_exists * §PIR.s
    intro s0
    -- EC: seq 3: (b = j0 \in x) (1%r/2%r) (1%r / 2%r ^ (N - (j0+1))) _ 0%r
    --       (1 <= j <= N /\ j = j0 + 1 /\ (PIR.s = if b then j0 :: s0 else s0) /\
    --        is_restr (oflist s0) j0 /\ oflist s0 = restr x j0).
    phoare_seq 3 : (§b = decide (j0 ∈ x)) (1 / 2) (1 / 2 ^ (N - (j0 + 1))) _ 0
      (1 ≤ §j ∧ §j ≤ N ∧ §j = j0 + 1 ∧ (§PIR.s = if §b then j0 :: s0 else s0) ∧
        is_restr (oflist s0) j0 ∧ oflist s0 = restr x j0)
    · -- EC: + by auto => /> /#.
      hoare_auto
      smt_close
    · -- EC: + by wp => /=;rnd (pred1 (j0 \in x));skip => /> &hr;rewrite dbool1E.
      stmt_wp; phoare_rnd (pred1 (decide (j0 ∈ x))); phoare_auto
      smt_close [dbool_ll, mu_pred1, dbool1E_mu1, pred1E]
    · -- EC: + conseq H=> />.
      --       + split.
      --         + smt(divr_ge0 expr_ge0).
      --         case: (j0 \in x) => Hjx ?? His Hof.
      --         + by rewrite oflist_cons restrS 1:/# Hjx Hof.
      --         by rewrite restrS 1:/# Hjx Hof /= fset0U.
      --       smt (is_restrS is_restr_addS oflist_cons).
      phoare_conseq H
      · smt_close [is_restrS, is_restr_addS, oflist_cons]
      · smt_close [restrS, oflist_cons, fset0U]
    · -- EC: + conseq H=> /> &0 />.
      --       + smt(restrS oflist_cons fset0U in_fsetU in_fset1 nin_is_restr).
      --       smt(is_restr_addS oflist_cons is_restrS fset0U).
      phoare_conseq H
      · smt_close [is_restr_addS, oflist_cons, is_restrS, fset0U]
      · -- (EC's hints are the membership lemmas; ours are the lemmas on `is_restr`)
        smt_close [restrS, oflist_cons, fset0U, is_restr_diff, is_restr_Ueq, is_restr_restr,
          ENNReal.ofReal_zero]
    -- EC: move=> &hr /> ?????; rewrite -exprS 1:/#; congr;congr;ring.
    rintro j s ⟨⟨⟨⟨⟨H0j, HjN, -⟩, Hj⟩, -⟩, rfl⟩, -⟩
    have h2 : (2 : ℝ) ^ (N - j) = 2 ^ (N - (j + 1)) * 2 := by
      rw [← zpow_add_one₀ (by norm_num)]; congr 1; ring
    rw [h2]; field_simp
  · -- EC: + wp;rnd predT;skip => /> &hr.
    --       smt (dbool_ll oflist_cons is_restrS is_restr_addS).
    phoare_auto
    smt_close [dbool_ll, oflist_cons, is_restrS, is_restr_addS]
  · -- EC: move=> z;auto=> />;smt (dbool_ll).
    intro z; phoare_auto
    rintro j s i ⟨-, -, rfl⟩
    simp only [ite_self]
    rw [show (fun _ : Bool => indicatorE (N - (j + 1) < N - j)) = fun _ => 1 from
      funext fun _ => indicatorE_of (by omega), (is_lossless_iff_expected _).mp dbool_ll,
      ENNReal.ofReal_one]
  · -- (our rule's goal: the bound is at most `1`)
    rintro j s ⟨H0j, HjN, -⟩
    split_ifs
    · rw [ENNReal.ofReal_le_one]
      exact (div_le_one (by positivity)).mpr (one_le_zpow₀ (by norm_num) (by omega))
    · simp
  · -- (our rule's goal: some state satisfies the postcondition)
    refine ⟨(localVarLens "j" ℤ).set 0 ⟨PIR.s.set [] VariableAssignment.init,
      VariableAssignment.init⟩, indicatorE_of ?_⟩
    have e1 : ((localVarLens "j" ℤ).set 0 ⟨PIR.s.set [] VariableAssignment.init,
        VariableAssignment.init⟩).globals = PIR.s.set [] VariableAssignment.init := rfl
    rw [e1, Lens.set_get, Lens.set_get, restr_0]; rfl

theorem Pr_PIR_s' (i0 : ℤ) (m : VariableAssignment) (x : FSet ℤ) :
    Pr[ PIR.main (i0) @ &m : oflist §PIR.s' = x ] =
      if is_restr x N then 1 / 2 ^ N else 0 := by
  -- EC: byphoare=> // {i0};proc;inline *;wp.
  byphoare (: True ==> _); phoare_proc; phoare_inline*; stmt_wp
  -- EC: case: (is_restr x N);first last.
  by_cases hx : is_restr x N
  rotate_left
  · -- EC: + conseq (_ : _ ==> _ : = 0%r) => [ _ | ].
    --       + smt(expr_ge0 divr_ge0).
    phoare_conseq (: _ ==> _ : = 0)
    · simp [hx]
    -- EC: hoare;conseq (_ : _ ==> is_restr (oflist PIR.s') N); 1:by smt().
    phoare_hoare
    hoare_conseq (: _ ==> is_restr (oflist §PIR.s') N)
    · smt_close
    -- EC: while (0<= j <= N /\ is_restr (oflist PIR.s') j).
    hoare_while (0 ≤ §j ∧ §j ≤ N ∧ is_restr (oflist §PIR.s') §j)
    · -- EC: + by auto => &m1 />;rewrite oflist_cons;smt (is_restrS is_restr_addS).
      hoare_auto
      smt_close [oflist_cons, is_restrS, is_restr_addS]
    -- EC: auto=> ?;rewrite -set0E;smt (is_restr_fset0 N_pos).
    hoare_auto
    smt_close [set0E, is_restr_fset0, N_pos]
  -- EC: sp; conseq (_ : _ ==> _ : = (if (oflist PIR.s') = restr x j then 1%r/2%r^(N-j)
  --       else 0%r)).
  stmt_sp
  phoare_conseq (: _ ==> _ : = (if oflist §PIR.s' = restr x §j then 1 / 2 ^ (N - §j) else 0))
  · -- EC: + move=> {&m} &m />;rewrite -set0E.
    --       split.
    --       + smt(expr_ge0 invr_ge0).
    --       have -> // : fset0 = restr x 0.
    --       + by apply fsetP=> z;rewrite /restr !inE mem_oflist mem_iota /#.
    smt_close [restr_0, set0E]
  -- EC: conseq (_ : _ ==> oflist PIR.s' = restr x j) (_: _ ==> j = N) => //;1:smt().
  phoare_conseq (: _ ==> oflist §PIR.s' = restr x §j) (: _ ==> §j = N)
  · smt_close
  · -- EC: + while(0 <= j <= N);auto;smt (N_pos).
    hoare_while (0 ≤ §j ∧ §j ≤ N) <;> hoare_auto <;> smt_close [N_pos]
  -- EC: conseq (: (0 <= j <= N /\ is_restr (oflist PIR.s') j) ==> _) => //.
  phoare_conseq (: 0 ≤ §j ∧ §j ≤ N ∧ is_restr (oflist §PIR.s') §j ==> _)
  · -- EC: + move=> />; smt(N_pos set0E is_restr_fset0).
    smt_close [N_pos, set0E, is_restr_fset0]
  -- EC: while (0 <= j <= N /\ is_restr (oflist PIR.s') j) (N-j) N 1%r => //.
  phoare_while (0 ≤ §j ∧ §j ≤ N ∧ is_restr (oflist §PIR.s') §j) (N - §j) N 1
  · -- EC: + move=> /> s j *; have ->>: j = N by smt().
    --       by rewrite subzz expr0.
    rintro j s ⟨H0j, HjN, Hs⟩ Hj
    obtain rfl : j = N := le_antisymm HjN (not_lt.mp (of_decide_eq_false Hj))
    by_cases h : oflist s = restr x N <;> simp [h, indicatorE]
  · -- EC: + smt(N_pos).
    smt_close [N_pos]
  · -- EC: + move=> H.
    intro w H
    -- EC: case (oflist PIR.s' = restr x j);first last.
    phoare_case (oflist §PIR.s' = restr x §j)
    rotate_left
    · -- EC: + seq 3 : true _ 0%r 0%r _ (0 <= j <= N /\ is_restr (oflist PIR.s') j /\
      --         oflist PIR.s' <> restr x j).
      phoare_seq 3 : (True) _ 0 0 _
        (0 ≤ §j ∧ §j ≤ N ∧ is_restr (oflist §PIR.s') §j ∧ oflist §PIR.s' ≠ restr x §j)
      · -- EC: + auto => /> &hr H0j ???? b ?.
        --       rewrite restrS //= oflist_cons.
        --       smt (is_restr_addS is_restrS is_restr_Ueq  is_restr_diff fset0U
        --         is_restr_restr).
        hoare_auto
        smt_close [restrS, oflist_cons, is_restr_addS, is_restrS, is_restr_Ueq, is_restr_diff,
          fset0U, is_restr_restr]
      · -- EC: by conseq H=> /#.
        phoare_conseq H
        · smt_close
        · smt_close [ENNReal.ofReal_zero]
      · -- EC: + by hoare;auto.
        phoare_hoare; hoare_auto
      -- EC: smt().
      smt_close
    -- EC: conseq (_ : _ : = (1%r / 2%r ^ (N - j))).
    --     + smt(divr_ge0 expr_ge0).
    phoare_conseq (: _ ==> _ : = (1 / 2 ^ (N - §j)))
    · smt_close
    -- EC: exists * j, PIR.s';elim * => j0 s0.
    stmt_exists * §j
    intro j0
    stmt_exists * §PIR.s'
    intro s0
    -- EC: seq 3: (b = ((j0 = i) ^^ (j0 \in x))) (1%r/2%r) (1%r / 2%r ^ (N - (j0+1))) _ 0%r
    --       (1 <= j <= N /\ j = j0 + 1 /\ (PIR.s' = if (j0=i) then (if b then s0 else j0::s0)
    --          else if b then j0 :: s0 else s0) /\
    --        is_restr (oflist s0) j0 /\ oflist s0 = restr x j0).
    phoare_seq 3 : (§b = (decide (j0 = §i) ^^ decide (j0 ∈ x))) (1 / 2) (1 / 2 ^ (N - (j0 + 1))) _ 0
      (1 ≤ §j ∧ §j ≤ N ∧ §j = j0 + 1 ∧
        (§PIR.s' = if decide (j0 = §i) then (if §b then s0 else j0 :: s0)
          else if §b then j0 :: s0 else s0) ∧
        is_restr (oflist s0) j0 ∧ oflist s0 = restr x j0)
    · -- EC: + by auto => /> /#.
      hoare_auto
      smt_close
    · -- EC: + by wp => /=;rnd (pred1 ((j0 = i) ^^ (j0 \in x)));skip => /> &hr;rewrite dbool1E.
      stmt_wp; phoare_rnd (pred1 (decide (j0 = §i) ^^ decide (j0 ∈ x))); phoare_auto
      smt_close [dbool_ll, mu_pred1, dbool1E_mu1, pred1E]
    · -- EC: + conseq H=> />.
      --       + split.
      --         + smt(divr_ge0 expr_ge0).
      --         case: (j0 \in x) => Hjx ?? His Hof.
      --         + by rewrite oflist_cons restrS 1:/# Hjx Hof.
      --         by rewrite restrS 1:/# Hjx Hof /= fset0U.
      --       smt (is_restrS is_restr_addS oflist_cons).
      phoare_conseq H
      · smt_close [is_restrS, is_restr_addS, oflist_cons]
      · smt_close [restrS, oflist_cons, fset0U]
    · -- EC: + conseq H=> /> &0 />.
      --       + smt(restrS oflist_cons fset0U in_fsetU in_fset1 nin_is_restr).
      --       smt(is_restr_addS oflist_cons is_restrS fset0U).
      phoare_conseq H
      · smt_close [is_restr_addS, oflist_cons, is_restrS, fset0U]
      · -- (EC's hints are the membership lemmas; ours are the lemmas on `is_restr`)
        smt_close [restrS, oflist_cons, fset0U, is_restr_diff, is_restr_Ueq, is_restr_restr,
          ENNReal.ofReal_zero]
    -- EC: move=> &hr /> ?????; rewrite -exprS 1:/#; congr;congr;ring.
    rintro j s ⟨⟨⟨⟨⟨H0j, HjN, -⟩, Hj⟩, -⟩, rfl⟩, -⟩
    have h2 : (2 : ℝ) ^ (N - j) = 2 ^ (N - (j + 1)) * 2 := by
      rw [← zpow_add_one₀ (by norm_num)]; congr 1; ring
    rw [h2]; field_simp
  · -- EC: + wp;rnd predT;skip => /> &hr.
    --       smt (dbool_ll oflist_cons is_restrS is_restr_addS).
    phoare_auto
    smt_close [dbool_ll, oflist_cons, is_restrS, is_restr_addS]
  · -- EC: move=> z;auto=> />;smt (dbool_ll).
    intro z; phoare_auto
    rintro j s i ⟨-, -, rfl⟩
    simp only [ite_self]
    rw [show (fun _ : Bool => indicatorE (N - (j + 1) < N - j)) = fun _ => 1 from
      funext fun _ => indicatorE_of (by omega), (is_lossless_iff_expected _).mp dbool_ll,
      ENNReal.ofReal_one]
  · -- (our rule's goal: the bound is at most `1`)
    rintro j s ⟨H0j, HjN, -⟩
    split_ifs
    · rw [ENNReal.ofReal_le_one]
      exact (div_le_one (by positivity)).mpr (one_le_zpow₀ (by norm_num) (by omega))
    · simp
  · -- (our rule's goal: some state satisfies the postcondition)
    refine ⟨(localVarLens "j" ℤ).set 0 ⟨PIR.s'.set [] VariableAssignment.init,
      VariableAssignment.init⟩, indicatorE_of ?_⟩
    have e1 : ((localVarLens "j" ℤ).set 0 ⟨PIR.s'.set [] VariableAssignment.init,
        VariableAssignment.init⟩).globals = PIR.s'.set [] VariableAssignment.init := rfl
    rw [e1, Lens.set_get, Lens.set_get, restr_0]; rfl

theorem PIR_secuity_s_bypr (i1 i2 : ℤ) (m1 m2 : VariableAssignment) (x : FSet ℤ) :
    Pr[ PIR.main (i1) @ &m1 : oflist §PIR.s = x ] =
      Pr[ PIR.main (i2) @ &m2 : oflist §PIR.s = x ] := by
  -- EC: by rewrite (@Pr_PIR_s i1 &m1 x) (@Pr_PIR_s i2 &m2 x).
  rw [Pr_PIR_s i1 m1 x, Pr_PIR_s i2 m2 x]

theorem PIR_secuity_s'_bypr (i1 i2 : ℤ) (m1 m2 : VariableAssignment) (x : FSet ℤ) :
    Pr[ PIR.main (i1) @ &m1 : oflist §PIR.s' = x ] =
      Pr[ PIR.main (i2) @ &m2 : oflist §PIR.s' = x ] := by
  -- EC: by rewrite (@Pr_PIR_s' i1 &m1 x) (@Pr_PIR_s' i2 &m2 x).
  rw [Pr_PIR_s' i1 m1 x, Pr_PIR_s' i2 m2 x]

/-!
Other version without explicit computation of the probability: we first show that the
probability is uniform.  (EC: "unfortunately this does not allow to conclude in EasyCrypt.  We
need to be able to do the projection of memories.")
-/

theorem PIR_s_uniform (x1 x2 : FSet ℤ) : 0 ≤ N → is_restr x1 N → is_restr x2 N →
    equiv[ PIR.main ~ PIR.main : ={i} ==>
      ((oflist §PIR.s{1} = x1) = (oflist §PIR.s{2} = x2)) ] := by
  -- EC: move=> HN B1 B2;proc;inline *;wp.
  intro HN B1 B2; equiv_proc; stmt_inline*; stmt_wp
  -- EC: while (={i,j} /\ 0 <= j{1} <= N /\
  --            is_restr (oflist PIR.s{1}) j{1} /\ is_restr (oflist PIR.s{2}) j{1} /\
  --            ((oflist PIR.s{1} = restr x1 j{1}) = (oflist PIR.s{2} = restr x2 j{1}))).
  equiv_while (={i, j} ∧ 0 ≤ §j{1} ∧ §j{1} ≤ N ∧
    is_restr (oflist §PIR.s{1}) §j{1} ∧ is_restr (oflist §PIR.s{2}) §j{1} ∧
    ((oflist §PIR.s{1} = restr x1 §j{1}) = (oflist §PIR.s{2} = restr x2 §j{1})))
  · -- EC: + wp.
    --       rnd (fun b => b ^^ (j{1} \in x1) ^^ (j{1} \in x2)).
    stmt_wp
    equiv_rnd (fun b => b ^^ decide (§j{1} ∈ x1) ^^ decide (§j{1} ∈ x2))
      (fun b => b ^^ decide (§j{1} ∈ x1) ^^ decide (§j{1} ∈ x2))
    -- EC: skip => &m1 &m2 /> H0j HjN Hrs1 Hrs2 Hs Hj; split.
    --     + by move=> b _;ring.
    --     move=> _ b _;split;1: by ring.
    --     move=> _; rewrite !oflist_cons !restrS //.
    --     smt (is_restr_addS is_restrS is_restr_diff is_restr_Ueq is_restr_restr  fset0U).
    equiv_auto
    rintro i j s₁ _ _ s₂ ⟨⟨⟨rfl, rfl⟩, H0j, HjN, Hrs1, Hrs2, Hs⟩, Hj, -⟩
    have hb : ∀ b : Bool, b = (b ^^ decide (j ∈ x1) ^^ decide (j ∈ x2) ^^ decide (j ∈ x1) ^^
        decide (j ∈ x2)) := fun b => by
      cases b <;> cases decide (j ∈ x1) <;> cases decide (j ∈ x2) <;> rfl
    refine ⟨hb, fun b => ⟨hb b, ?_⟩⟩
    smt_close [oflist_cons, restrS, is_restr_addS, is_restrS, is_restr_diff, is_restr_Ueq,
      is_restr_restr, fset0U]
  -- EC: auto; move => &m1 &m2 />.
  --     rewrite !restr_0 -set0E /=;smt (is_restr_fset0).
  equiv_auto
  smt_close [restr_0, set0E, is_restr_fset0]

theorem PIR_s'_uniform (x1 x2 : FSet ℤ) : 0 ≤ N → is_restr x1 N → is_restr x2 N →
    equiv[ PIR.main ~ PIR.main : ={i} ==>
      ((oflist §PIR.s'{1} = x1) = (oflist §PIR.s'{2} = x2)) ] := by
  -- EC: move=> HN B1 B2;proc;inline *;wp.
  intro HN B1 B2; equiv_proc; stmt_inline*; stmt_wp
  -- EC: while (={i,j} /\ 0 <= j{1} <= N /\
  --            is_restr (oflist PIR.s'{1}) j{1} /\ is_restr (oflist PIR.s'{2}) j{1} /\
  --            ((oflist PIR.s'{1} = restr x1 j{1}) = (oflist PIR.s'{2} = restr x2 j{1}))).
  equiv_while (={i, j} ∧ 0 ≤ §j{1} ∧ §j{1} ≤ N ∧
    is_restr (oflist §PIR.s'{1}) §j{1} ∧ is_restr (oflist §PIR.s'{2}) §j{1} ∧
    ((oflist §PIR.s'{1} = restr x1 §j{1}) = (oflist §PIR.s'{2} = restr x2 §j{1})))
  · -- EC: + wp.
    --       rnd (fun b => b ^^ (j{1} \in x1) ^^ (j{1} \in x2)).
    stmt_wp
    equiv_rnd (fun b => b ^^ decide (§j{1} ∈ x1) ^^ decide (§j{1} ∈ x2))
      (fun b => b ^^ decide (§j{1} ∈ x1) ^^ decide (§j{1} ∈ x2))
    -- EC: skip => &m1 &m2 [#] 2!->> H0j HjN Hrs1 Hrs2 Hs Hj _; split.
    --     + move=> b _;ring.
    --     move=> _ b _; split;1: by ring.
    --     move=> _; rewrite /= !oflist_cons !restrS //.
    --     smt (is_restr_addS is_restrS is_restr_diff is_restr_Ueq is_restr_restr  fset0U).
    equiv_auto
    rintro i j s₁ _ _ s₂ ⟨⟨⟨rfl, rfl⟩, H0j, HjN, Hrs1, Hrs2, Hs⟩, Hj, -⟩
    have hb : ∀ b : Bool, b = (b ^^ decide (j ∈ x1) ^^ decide (j ∈ x2) ^^ decide (j ∈ x1) ^^
        decide (j ∈ x2)) := fun b => by
      cases b <;> cases decide (j ∈ x1) <;> cases decide (j ∈ x2) <;> rfl
    refine ⟨hb, fun b => ⟨hb b, ?_⟩⟩
    smt_close [oflist_cons, restrS, is_restr_addS, is_restrS, is_restr_diff, is_restr_Ueq,
      is_restr_restr, fset0U]
  -- EC: auto => &m1 &m2 />.
  --     rewrite !restr_0 -set0E /=;smt (is_restr_fset0).
  equiv_auto
  smt_close [restr_0, set0E, is_restr_fset0]

end GaudisCrypt.Examples.PIR
