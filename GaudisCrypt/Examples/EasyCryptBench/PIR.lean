import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.PHoareWp

/-!
# Private information retrieval (EasyCrypt `examples/PIR.ec`)

Two-server PIR: to read entry `i` of a database `a` replicated on two servers without either
server learning `i`, the client sends the first server a random subset `s` of the indices
`[0, N)` and the second server `s' = s △ {i}`; each server returns the XOR of the entries it was
asked for, and the two answers XOR to `a i`.

```
module PIR = {
  proc query (s:int list) = {
    return (big predT a s);
  }

  var s, s' : int list

  proc main (i:int) = {
    var r, r' : word;
    var j <- 0;
    var b;

    (s, s') <- ([], []);
    while (j < N) {
      b <$ {0,1};
      if (j = i) {
        if (b) s <- j :: s; else s' <- j :: s';
      } else {
        if (b) { s <- j :: s; s' <- j :: s'; }
      }
      j <- j + 1;
    }

    r <@ query(s);
    r' <@ query(s');

    return r +^ r';
  }
}.

equiv PIR_secure1: PIR.main ~ PIR.main : true ==> ={PIR.s}.
proof.
  proc;inline *;wp.
  while (={j,PIR.s});auto.
qed.

equiv PIR_secure2: PIR.main ~ PIR.main : true ==> ={PIR.s'}.
proof.
  proc;inline *;wp.
  while (={j,PIR.s'});2: by auto.
  wp; case: ((j = i){1} = (j = i){2}).
  + auto;smt (dbool_funi dbool_fu).
  rnd (fun x => !x);skip;smt (dbool_funi dbool_fu).
qed.

lemma PIR_secuity_s_byequiv i1 i2 &m1 &m2 x:
   Pr[PIR.main(i1) @ &m1 : PIR.s = x] = Pr[PIR.main(i2) @ &m2 : PIR.s = x].
proof. by byequiv PIR_secure1. qed.
```

The privacy statements: the query each server sees is distributed independently of `i` — the
two runs, for *any* two indices, can be coupled so that `s` (resp. `s'`) is the same.  `secure2`
couples the coins with one state-dependent function (negation exactly in the rounds where the two
runs disagree on whether this is the index) where EC splits cases and uses two `rnd`s.

Correctness, `Pr[PIR.main(i0) @ &m : res = a i0] = 1` (EC's `PIR_correct`, via `byphoare` with a
Hoare invariant and `while true (N-j)` for termination), is `correct`: one lower-bound loop rule
with a variant (`phoare_while_ge I variant N - §j`), whose invariant is EC's
`j ≤ N ∧ (if j ≤ i then s = s' else sxor2 s s' i)` as an indicator.
-/

namespace GaudisCrypt.Examples.EasyCryptBench.PIR

open GaudisCrypt

/-- The query sent to the first server. -/
global_var s : List ℕ
/-- The query sent to the second server. -/
global_var s' : List ℕ

/-- The database: entries in a group of characteristic 2 (EC's `word` with `+^`). -/
structure Database where
  W : Type
  [group : AddCommGroup W]
  [inhabited : Inhabited W]
  a : ℕ → W
  char_two : ∀ x : W, x + x = 0

@[reducible] instance (D : Database) : AddCommGroup D.W := D.group
@[reducible] instance (D : Database) : Inhabited D.W := D.inhabited

variable (N : ℕ) (D : Database)

/-- A server's answer: the sum of the entries asked for. -/
noncomputable def query := proc (q : List ℕ) : D.W {
  return ((List.map D.a $q).sum)
}

noncomputable def main := proc (i : ℕ) : D.W {
  var j : ℕ, b : Bool, r : D.W, r' : D.W;
  j <- 0;
  s <- [];
  s' <- [];
  while ($j < N) {
    b <$ SubProbability.uniform;
    if ($j == $i) {
      if ($b) { s <- $j :: $s; } else { s' <- $j :: $s'; }
    } else {
      if ($b) { s <- $j :: $s; s' <- $j :: $s'; }
    }
    j <- $j + 1;
  }
  r <- call (query D) ($s);
  r' <- call (query D) ($s');
  return $r + $r'
}

/-- The first server's query does not depend on the index (EC's `PIR_secure1`). -/
theorem secure1 : equiv[ (main N D) ~ (main N D) : True ==> ={s} ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline 0
  stmt_inline 0
  stmt_wp
  equiv_while ={j, s}
  case body =>
    stmt_wp
    equiv_rnd
    equiv_skip
    rintro j s _ _ _ _ ⟨⟨rfl, rfl⟩, -⟩ a
    simp
  case guard => rintro _ _ _ _ ⟨rfl, -⟩; rfl
  case exit => exact fun _ _ _ _ h _ => h.2
  stmt_wp
  equiv_skip
  exact fun _ => trivial

/-- The second server's query does not depend on the index (EC's `PIR_secure2`): where the two
runs disagree on whether this round is the index, their coins are coupled as negations. -/
theorem secure2 : equiv[ (main N D) ~ (main N D) : True ==> ={s'} ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline 0
  stmt_inline 0
  stmt_wp
  equiv_while ={j, s'}
  case body =>
    stmt_wp
    equiv_rnd (fun b => if (§j{1} == §i0{1}) = (§j{2} == §i0{2}) then b else !b)
    equiv_skip
    rintro j s i₁ _ _ i₂ ⟨⟨rfl, rfl⟩, -⟩
    refine ⟨by split_ifs <;> simp, fun a => ?_⟩
    simp only [beq_iff_eq]
    split_ifs <;> simp_all
  case guard => rintro _ _ _ _ ⟨rfl, -⟩; rfl
  case exit => exact fun _ _ _ _ h _ => h.2
  stmt_wp
  equiv_skip
  exact fun _ => trivial

/-- What the first server sees is distributed independently of the index and of the initial
memory (EC's `PIR_secuity_s_byequiv`). -/
theorem security_s (i₁ i₂ : ℕ) (m₁ m₂ : VariableAssignment) (x : List ℕ) :
    Procedure.Pr (main N D) i₁ m₁ (fun _ g => s.get g = x)
      = Procedure.Pr (main N D) i₂ m₂ (fun _ g => s.get g = x) :=
  Procedure.Pr_eq_of_prhlProc (secure1 N D)
    (fun _ g₁ _ g₂ (h : s.get g₁ = s.get g₂) => by rw [h]) trivial

/-- The same for the second server (EC's `PIR_secuity_s'_byequiv`). -/
theorem security_s' (i₁ i₂ : ℕ) (m₁ m₂ : VariableAssignment) (x : List ℕ) :
    Procedure.Pr (main N D) i₁ m₁ (fun _ g => s'.get g = x)
      = Procedure.Pr (main N D) i₂ m₂ (fun _ g => s'.get g = x) :=
  Procedure.Pr_eq_of_prhlProc (secure2 N D)
    (fun _ g₁ _ g₂ (h : s'.get g₁ = s'.get g₂) => by rw [h]) trivial

/-! ## Correctness (EC's `PIR_correct`)

The two queries differ in exactly the index: one is the other with `i` inserted (`sxor2`), so
the answers add up to `a i` in characteristic 2.  A probability-`1` statement: partial
correctness (the invariant) and termination — the loop is counted, so the lower bound needs the
variant rule (`phoare_while_ge I variant V`). -/

/-- `s'` is `s` with `i` inserted somewhere. -/
def sxor (s s' : List ℕ) (i : ℕ) : Prop := ∃ s₁ s₂, s = s₁ ++ s₂ ∧ s' = s₁ ++ i :: s₂

/-- One of the two queries is the other with `i` inserted. -/
def sxor2 (s s' : List ℕ) (i : ℕ) : Prop := sxor s s' i ∨ sxor s' s i

theorem sxor2_cons {s s' : List ℕ} {i : ℕ} (j : ℕ) (h : sxor2 s s' i) :
    sxor2 (j :: s) (j :: s') i := by
  rcases h with ⟨s₁, s₂, rfl, rfl⟩ | ⟨s₁, s₂, rfl, rfl⟩
  · exact Or.inl ⟨j :: s₁, s₂, rfl, rfl⟩
  · exact Or.inr ⟨j :: s₁, s₂, rfl, rfl⟩

/-- The answers to two queries that differ in `i` add up to `a i`. -/
theorem answer_of_sxor2 {s s' : List ℕ} {i : ℕ} (h : sxor2 s s' i) :
    (List.map D.a s).sum + (List.map D.a s').sum = D.a i := by
  have key : ∀ x y : D.W, x + (x + y) = y := fun x y => by
    rw [← add_assoc, D.char_two, zero_add]
  rcases h with ⟨s₁, s₂, rfl, rfl⟩ | ⟨s₁, s₂, rfl, rfl⟩ <;>
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  · calc _ = ((List.map D.a s₁).sum + (List.map D.a s₂).sum) +
          (((List.map D.a s₁).sum + (List.map D.a s₂).sum) + D.a i) := by abel
      _ = D.a i := key _ _
  · calc _ = ((List.map D.a s₁).sum + (List.map D.a s₂).sum) +
          (((List.map D.a s₁).sum + (List.map D.a s₂).sum) + D.a i) := by abel
      _ = D.a i := key _ _

/-- **Correctness**: the two answers add up to the requested entry, with probability `1`. -/
theorem correct (i₀ : ℕ) (hi : i₀ < N) :
    phoare[ (main N D) : §i = i₀ ==> §res = D.a i₀ ] = 1 := by
  refine phoareProc_eq_of_le_ge (fun _ _ _ => ?_) ?_
  · exact (Procedure.ewp_mono _ _ (fun _ _ => indicatorE_le_one _) _).trans
      (Procedure.ewp_const_le _ _ _ _)
  phoare_proc_to_stmt
  phoare_inline 0
  phoare_inline 0
  phoare_inline 0
  stmt_wp
  phoare_while_ge
    indicatorE (§i0 = i₀ ∧ §j ≤ N ∧ if §j ≤ §i0 then §s = §s' else sxor2 §s §s' §i0)
    variant N - §j
  case body =>
    stmt_wp
    phoare_wp 1
    phoare_skip
    intro j i0 s s' hj
    simp only [ite_self, beq_iff_eq]
    by_cases hinv : i0 = i₀ ∧ j ≤ N ∧ if j ≤ i0 then s = s' else sxor2 s s' i0
    swap
    · simp [indicatorE_of_not hinv]
    rw [indicatorE_of hinv]
    obtain ⟨rfl, -, hrel⟩ := hinv
    have hjN : j + 1 ≤ N := by simpa using hj
    -- either coin keeps the invariant: before the index the queries agree, at it one of them
    -- gets the index, after it both get the same
    have hT : if j + 1 ≤ i0 then j :: s = (if j = i0 then s' else j :: s')
        else sxor2 (j :: s) (if j = i0 then s' else j :: s') i0 := by
      rcases lt_trichotomy j i0 with hlt | rfl | hgt
      · rw [if_pos hlt.le] at hrel
        rw [if_pos (Nat.succ_le_of_lt hlt), if_neg hlt.ne, hrel]
      · rw [if_pos le_rfl] at hrel
        rw [if_neg (by omega), if_pos rfl, hrel]
        exact Or.inr ⟨[], s', rfl, rfl⟩
      · rw [if_neg (Nat.not_le.mpr hgt)] at hrel
        rw [if_neg (by omega), if_neg hgt.ne']
        exact sxor2_cons j hrel
    have hF : if j + 1 ≤ i0 then s = (if j = i0 then j :: s' else s')
        else sxor2 s (if j = i0 then j :: s' else s') i0 := by
      rcases lt_trichotomy j i0 with hlt | rfl | hgt
      · rw [if_pos hlt.le] at hrel
        rw [if_pos (Nat.succ_le_of_lt hlt), if_neg hlt.ne, hrel]
      · rw [if_pos le_rfl] at hrel
        rw [if_neg (by omega), if_pos rfl, hrel]
        exact Or.inl ⟨[], s', rfl, rfl⟩
      · rw [if_neg (Nat.not_le.mpr hgt)] at hrel
        rw [if_neg (by omega), if_neg hgt.ne']
        exact hrel
    rw [indicatorE_of rfl, indicatorE_of hjN, indicatorE_of hT, indicatorE_of hF]
    simp [ENNReal.inv_two_add_inv_two]
  case exit =>
    intro j i0 s s' hj
    rw [← indicatorE_and, ← indicatorE_and]
    by_cases hinv : i0 = i₀ ∧ j ≤ N ∧ if j ≤ i0 then s = s' else sxor2 s s' i0
    · obtain ⟨rfl, -, hrel⟩ := hinv
      rw [if_neg (by simp at hj; omega)] at hrel
      exact (indicatorE_le_one _).trans (indicatorE_of (answer_of_sxor2 D hrel)).ge
    · rw [indicatorE_of_not hinv]
      exact zero_le
  case decreases =>
    intro k
    stmt_wp
    hoare_wp 1
    hoare_skip
    intro j _ ⟨hj, hk⟩ _ _
    simp only [ite_self, decide_eq_true_eq] at hj ⊢
    omega
  stmt_wp
  phoare_skip
  rintro _ rfl
  simp

/-- **EC's `PIR_correct`**, as EC states it: `Pr[PIR.main(i0) @ &m : res = a i0] = 1`. -/
theorem pir_correct (i₀ : ℕ) (hi : i₀ < N) (m : VariableAssignment) :
    (Procedure.Pr (main N D) i₀ m (fun r _ => r = D.a i₀) : ENNReal) = 1 :=
  Procedure.Pr_of_phoareProc (correct N D i₀ hi) (args := i₀) (σ := m) rfl

/-! ## Uniformity of a query, relationally (EC's `PIR_s_uniform`)

For any two index sets `x₁`, `x₂` in `[0, N)`, the run on the left yields the query `x₁` exactly
when the run on the right yields `x₂`: the coins are coupled by `b ↦ b ⊕ (j ∈ x₁) ⊕ (j ∈ x₂)`,
so that the left run takes index `j` into its query as `x₁` does exactly when the right one takes
it as `x₂` does.  (EC: "unfortunately this does not allow to conclude in EasyCrypt", for lack of
projections of memories; here `security_s` concludes directly.) -/

/-- One round of the query, restricted to the indices seen so far: the query extended by `j` or
not is `x` up to `j` exactly when it was `x` below `j` and took `j` as `x` does. -/
theorem toFinset_step {q : List ℕ} {x : Finset ℕ} {j : ℕ} (b : Bool)
    (hq : ∀ y ∈ q.toFinset, y < j) :
    ((if b then j :: q else q).toFinset = x.filter (· < j + 1)) ↔
      (q.toFinset = x.filter (· < j) ∧ (b = true ↔ j ∈ x)) := by
  have hj : j ∉ q.toFinset := fun h => lt_irrefl _ (hq j h)
  have hsplit : x.filter (· < j + 1) = if j ∈ x then insert j (x.filter (· < j))
      else x.filter (· < j) := by
    ext y
    by_cases hy : y = j
    · subst hy; by_cases hx : y ∈ x <;> simp [hx]
    · have : y ≤ j ↔ y < j := by omega
      by_cases hx : j ∈ x <;> simp [hx, hy, this]
  have hnot : j ∉ x.filter (· < j) := by simp
  rw [hsplit]
  cases b <;> by_cases hx : j ∈ x <;> simp only [hx, if_true, if_false, Bool.false_eq_true,
    List.toFinset_cons, iff_true, iff_false, not_true, and_true, and_false]
  · intro h; rw [h] at hj; exact hj (Finset.mem_insert_self j _)
  · constructor
    · intro h
      rw [← Finset.erase_insert hj, h, Finset.erase_insert hnot]
    · intro h; rw [h]
  · intro h; exact hnot (by rw [← h]; exact Finset.mem_insert_self j _)

/-- A query below `j`, extended by `j` or not, is below `j + 1`. -/
theorem bounded_step {q : List ℕ} {j : ℕ} (hq : ∀ y ∈ q.toFinset, y < j) (b : Bool) :
    ∀ y ∈ (if b then j :: q else q).toFinset, y < j + 1 := by
  intro y hy
  cases b
  · exact Nat.lt_succ_of_lt (hq y hy)
  · simp only [if_true, List.toFinset_cons, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact Nat.lt_succ_self y
    · exact Nat.lt_succ_of_lt (hq y hy)

/-- **EC's `PIR_s_uniform`**: for any two index sets in `[0, N)`, on the same index, the first
query is `x₁` on the left exactly when it is `x₂` on the right. -/
theorem s_uniform (x₁ x₂ : Finset ℕ) (h₁ : x₁ ⊆ Finset.range N) (h₂ : x₂ ⊆ Finset.range N) :
    equiv[ (main N D) ~ (main N D) : ={i} ==>
      ((§s{1}).toFinset = x₁ ↔ (§s{2}).toFinset = x₂) ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline 0
  stmt_inline 0
  stmt_wp
  equiv_while ={i0, j} ∧ §j{1} ≤ N ∧ (∀ y ∈ (§s{1}).toFinset, y < §j{1}) ∧
      (∀ y ∈ (§s{2}).toFinset, y < §j{2}) ∧
      ((§s{1}).toFinset = x₁.filter (· < §j{1}) ↔ (§s{2}).toFinset = x₂.filter (· < §j{2}))
  case body =>
    stmt_wp
    equiv_rnd (fun b => b ^^ (decide (§j{1} ∈ x₁) ^^ decide (§j{2} ∈ x₂)))
    equiv_skip
    rintro i j s₁ _ _ s₂ ⟨⟨⟨rfl, rfl⟩, -, hs₁, hs₂, hiff⟩, hj⟩ a
    simp only [ite_self]
    refine ⟨by simp, by simpa using hj, bounded_step hs₁ _, bounded_step hs₂ _, ?_⟩
    rw [toFinset_step _ hs₁, toFinset_step _ hs₂, hiff]
    refine and_congr_right fun _ => ?_
    cases a <;> by_cases hx₁ : j ∈ x₁ <;> by_cases hx₂ : j ∈ x₂ <;> simp [hx₁, hx₂]
  case guard => rintro _ _ _ _ _ _ ⟨⟨_, rfl⟩, -⟩; rfl
  case exit =>
    rintro _ j s₁ _ _ s₂ ⟨⟨-, rfl⟩, hjN, -, -, hiff⟩ hj
    have hjN : j = N := by simp at hj; omega
    subst hjN
    have hx (x : Finset ℕ) (hx : x ⊆ Finset.range j) : x.filter (· < j) = x :=
      Finset.filter_true_of_mem fun y hy => Finset.mem_range.mp (hx hy)
    rwa [hx x₁ h₁, hx x₂ h₂] at hiff
  stmt_wp
  equiv_skip
  rintro _ _ rfl
  simp

/-- **EC's `PIR_s'_uniform`**: the same for the second query.  It takes `j` when the coin says so,
except at the index, where it takes `j` when the coin says not to; the two runs have the same
index, so the same coupling works. -/
theorem s'_uniform (x₁ x₂ : Finset ℕ) (h₁ : x₁ ⊆ Finset.range N) (h₂ : x₂ ⊆ Finset.range N) :
    equiv[ (main N D) ~ (main N D) : ={i} ==>
      ((§s'{1}).toFinset = x₁ ↔ (§s'{2}).toFinset = x₂) ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline 0
  stmt_inline 0
  stmt_wp
  equiv_while ={i0, j} ∧ §j{1} ≤ N ∧ (∀ y ∈ (§s'{1}).toFinset, y < §j{1}) ∧
      (∀ y ∈ (§s'{2}).toFinset, y < §j{2}) ∧
      ((§s'{1}).toFinset = x₁.filter (· < §j{1}) ↔ (§s'{2}).toFinset = x₂.filter (· < §j{2}))
  case body =>
    stmt_wp
    equiv_rnd (fun b => b ^^ (decide (§j{1} ∈ x₁) ^^ decide (§j{2} ∈ x₂)))
    equiv_skip
    rintro i j s₁ _ _ s₂ ⟨⟨⟨rfl, rfl⟩, -, hs₁, hs₂, hiff⟩, hj⟩ a
    -- the second query takes `j` exactly when `a ^^ (j == i)`
    have hq (b : Bool) (q : List ℕ) : (if (j == i) = true then (if b = true then q else j :: q)
        else (if b = true then j :: q else q)) = if (b ^^ (j == i)) = true then j :: q else q := by
      cases b <;> cases (j == i) <;> rfl
    simp only [hq, ite_self]
    refine ⟨by simp, by simpa using hj, bounded_step hs₁ _, bounded_step hs₂ _, ?_⟩
    rw [toFinset_step _ hs₁, toFinset_step _ hs₂, hiff]
    refine and_congr_right fun _ => ?_
    cases a <;> cases (j == i) <;> by_cases hx₁ : j ∈ x₁ <;> by_cases hx₂ : j ∈ x₂ <;>
      simp [hx₁, hx₂]
  case guard => rintro _ _ _ _ _ _ ⟨⟨_, rfl⟩, -⟩; rfl
  case exit =>
    rintro _ j s₁ _ _ s₂ ⟨⟨-, rfl⟩, hjN, -, -, hiff⟩ hj
    have hjN : j = N := by simp at hj; omega
    subst hjN
    have hx (x : Finset ℕ) (hx : x ⊆ Finset.range j) : x.filter (· < j) = x :=
      Finset.filter_true_of_mem fun y hy => Finset.mem_range.mp (hx hy)
    rwa [hx x₁ h₁, hx x₂ h₂] at hiff
  stmt_wp
  equiv_skip
  rintro _ _ rfl
  simp

end GaudisCrypt.Examples.EasyCryptBench.PIR
