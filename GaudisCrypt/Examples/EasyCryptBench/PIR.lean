import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.PRHLWp

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
two runs, for *any* two indices, can be coupled so that `s` (resp. `s'`) is the same.
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

end GaudisCrypt.Examples.EasyCryptBench.PIR
