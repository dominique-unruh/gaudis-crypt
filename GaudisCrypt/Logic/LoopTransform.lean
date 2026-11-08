import GaudisCrypt.Logic.PRHLStmt

/-!
# Loop transformations and statement-level transitivity

EasyCrypt rewrites loops in a relational judgment before reasoning about them: `splitwhile{i} k :
e` (a loop `while c b` becomes `while (c /\ e) b; while c b`) and `unroll{i} k` (one iteration
peeled off as a conditional).  Here both are denotational equivalences of statements
(`StmtWithHoles.Equiv`), moved into a judgment with `prhlStmt_of_equiv_left`/`_right`.

`splitwhile` is proven for loops whose first part terminates by a variant (every SHA-3 loop is
bounded): the remaining loop's expectation is then a fixed point of the first part's loop, from
above (`Stmt.ewp_while_le`) and from below (`Stmt.ewp_while_ge_variant`).

EasyCrypt's `transitivity{i} { code } P Q` at the statement level is `prhlStmt.trans`.
-/

namespace GaudisCrypt

/-! ## Equivalence from denotations -/

/-- Statements with the same run are equivalent. -/
theorem Stmt.Equiv.of_denotation_eq {a b : Stmt}
    (h : ∀ σ, programDenotation a σ = programDenotation b σ) : a.Equiv b := by
  intro inst
  rw [StmtWithHoles.instantiate_empty, StmtWithHoles.instantiate_empty]
  rintro sa sb rfl
  rw [← h]
  exact ProgramDenotation.EquivInLens.refl (programDenotation a) _ _ rfl

/-- Statements with the same expectations have the same run. -/
theorem Stmt.denotation_eq_of_ewp {a b : Stmt}
    (h : ∀ (g : ProgramState → ENNReal) σ, a.ewp g σ = b.ewp g σ) (σ : ProgramState) :
    programDenotation a σ = programDenotation b σ :=
  SubProbability.ext_of_expected fun F => by
    have := h (fun τ => F ((), τ)) σ
    simp only [Stmt.ewp, ProgramDenotation.wp] at this
    exact this

/-! ## `splitwhile` -/

/-- The guard `c /\ e` of the first loop of a split. -/
def Getter.andB (c e : Getter Bool ProgramState) : Getter Bool ProgramState :=
  ⟨fun σ => c.get σ && e.get σ⟩

@[simp] theorem Getter.andB_get (c e : Getter Bool ProgramState) (σ : ProgramState) :
    (c.andB e).get σ = (c.get σ && e.get σ) := rfl

/-- **`splitwhile`**, on expectations: a loop is the same loop run first while `e` also holds,
then on.  `V` decreases on every round of the first loop. -/
theorem Stmt.ewp_splitwhile (c e : Getter Bool ProgramState) (body : Stmt)
    (V : ProgramState → ℕ)
    (hvar : ∀ k, hoareStmt (fun σ => (c.andB e).get σ = true ∧ V σ = k) body (fun τ => V τ < k))
    (g : ProgramState → ENNReal) (σ : ProgramState) :
    Stmt.ewp (StmtWithHoles.while c body) g σ =
      Stmt.ewp (StmtWithHoles.seq (StmtWithHoles.while (c.andB e) body)
        (StmtWithHoles.while c body)) g σ := by
  rw [Stmt.ewp_seq]
  set h := Stmt.ewp (StmtWithHoles.while c body) g with hh
  have hfix : ∀ τ, (c.andB e).get τ = true → body.ewp h τ = h τ := fun τ hτ => by
    have hc : c.get τ = true := by simp only [Getter.andB_get, Bool.and_eq_true] at hτ; exact hτ.1
    rw [hh, Stmt.ewp_while_unfold c body g τ, if_pos hc]
  refine le_antisymm ?_ ?_
  · exact Stmt.ewp_while_ge_variant h h V hvar (fun τ hτ => (hfix τ hτ).ge) (fun _ _ => le_rfl) σ
  · exact Stmt.ewp_while_le h h (fun τ hτ => (hfix τ hτ).le) (fun _ _ => le_rfl) σ

/-- **`splitwhile`** (EC's `splitwhile … : e`), as an equivalence of statements. -/
theorem Stmt.Equiv.splitwhile (c e : Getter Bool ProgramState) (body : Stmt)
    (V : ProgramState → ℕ)
    (hvar : ∀ k, hoareStmt (fun σ => (c.andB e).get σ = true ∧ V σ = k) body
      (fun τ => V τ < k)) :
    (StmtWithHoles.while c body).Equiv
      (StmtWithHoles.seq (StmtWithHoles.while (c.andB e) body) (StmtWithHoles.while c body)) :=
  Stmt.Equiv.of_denotation_eq fun σ =>
    Stmt.denotation_eq_of_ewp (fun g σ => Stmt.ewp_splitwhile c e body V hvar g σ) σ

/-! ## `unroll` -/

/-- **`unroll`** (EC's `unroll`): one round of a loop, peeled off as a conditional. -/
theorem Stmt.Equiv.unroll (c : Getter Bool ProgramState) (body : Stmt) :
    (StmtWithHoles.while c body).Equiv
      (StmtWithHoles.ifThenElse c (StmtWithHoles.seq body (StmtWithHoles.while c body))
        StmtWithHoles.skip) :=
  Stmt.Equiv.of_denotation_eq fun σ => by
    rw [programDenotation_while_unfold, programDenotation_ifThenElse_apply]
    split_ifs with hc
    · rw [programDenotation_seq, ProgramDenotation.bind_apply]
    · rw [programDenotation_skip_apply]

/-! ## A conditional followed by code -/

/-- The code after a conditional goes into both branches (what EC's `if` does with the rest of the
code). -/
theorem Stmt.Equiv.seq_ite (c : Getter Bool ProgramState) (t e s : Stmt) :
    (StmtWithHoles.seq (StmtWithHoles.ifThenElse c t e) s).Equiv
      (StmtWithHoles.ifThenElse c (StmtWithHoles.seq t s) (StmtWithHoles.seq e s)) :=
  Stmt.Equiv.of_denotation_eq fun σ => by
    rw [programDenotation_seq, ProgramDenotation.bind_apply, programDenotation_ifThenElse_apply,
      programDenotation_ifThenElse_apply]
    split_ifs <;> rw [programDenotation_seq, ProgramDenotation.bind_apply]

/-! ## In judgments, for a trailing loop -/

variable {A B : ProgramState → ProgramState → Prop}

/-- `splitwhile{1}` on a trailing loop. -/
theorem prhlStmt_seq_splitwhile_left {s₁ s₂ body : Stmt} {c : Getter Bool ProgramState}
    (e : Getter Bool ProgramState) (V : ProgramState → ℕ)
    (hvar : ∀ k, hoareStmt (fun σ => (c.andB e).get σ = true ∧ V σ = k) body (fun τ => V τ < k))
    (h : prhlStmt A (.seq s₁ (.seq (.while (c.andB e) body) (.while c body))) s₂ B) :
    prhlStmt A (.seq s₁ (.while c body)) s₂ B :=
  prhlStmt_of_equiv_left
    (StmtWithHoles.EquivInLens.seq (StmtWithHoles.Equiv.refl s₁)
      (Stmt.Equiv.splitwhile c e body V hvar)) h

/-- `splitwhile{2}` on a trailing loop. -/
theorem prhlStmt_seq_splitwhile_right {s₁ s₂ body : Stmt} {c : Getter Bool ProgramState}
    (e : Getter Bool ProgramState) (V : ProgramState → ℕ)
    (hvar : ∀ k, hoareStmt (fun σ => (c.andB e).get σ = true ∧ V σ = k) body (fun τ => V τ < k))
    (h : prhlStmt A s₁ (.seq s₂ (.seq (.while (c.andB e) body) (.while c body))) B) :
    prhlStmt A s₁ (.seq s₂ (.while c body)) B :=
  prhlStmt_of_equiv_right
    (StmtWithHoles.EquivInLens.seq (StmtWithHoles.Equiv.refl s₂)
      (Stmt.Equiv.splitwhile c e body V hvar)) h

/-- `unroll{1}` on a trailing loop. -/
theorem prhlStmt_seq_unroll_left {s₁ s₂ body : Stmt} {c : Getter Bool ProgramState}
    (h : prhlStmt A (.seq s₁ (.ifThenElse c (.seq body (.while c body)) .skip)) s₂ B) :
    prhlStmt A (.seq s₁ (.while c body)) s₂ B :=
  prhlStmt_of_equiv_left
    (StmtWithHoles.EquivInLens.seq (StmtWithHoles.Equiv.refl s₁) (Stmt.Equiv.unroll c body)) h

/-- `unroll{2}` on a trailing loop. -/
theorem prhlStmt_seq_unroll_right {s₁ s₂ body : Stmt} {c : Getter Bool ProgramState}
    (h : prhlStmt A s₁ (.seq s₂ (.ifThenElse c (.seq body (.while c body)) .skip)) B) :
    prhlStmt A s₁ (.seq s₂ (.while c body)) B :=
  prhlStmt_of_equiv_right
    (StmtWithHoles.EquivInLens.seq (StmtWithHoles.Equiv.refl s₂) (Stmt.Equiv.unroll c body)) h

/-- `splitwhile{1}` on a loop that is the whole left statement. -/
theorem prhlStmt_splitwhile_left {s₂ body : Stmt} {c : Getter Bool ProgramState}
    (e : Getter Bool ProgramState) (V : ProgramState → ℕ)
    (hvar : ∀ k, hoareStmt (fun σ => (c.andB e).get σ = true ∧ V σ = k) body (fun τ => V τ < k))
    (h : prhlStmt A (.seq (.while (c.andB e) body) (.while c body)) s₂ B) :
    prhlStmt A (.while c body) s₂ B :=
  prhlStmt_of_equiv_left (Stmt.Equiv.splitwhile c e body V hvar) h

/-- `splitwhile{2}` on a loop that is the whole right statement. -/
theorem prhlStmt_splitwhile_right {s₁ body : Stmt} {c : Getter Bool ProgramState}
    (e : Getter Bool ProgramState) (V : ProgramState → ℕ)
    (hvar : ∀ k, hoareStmt (fun σ => (c.andB e).get σ = true ∧ V σ = k) body (fun τ => V τ < k))
    (h : prhlStmt A s₁ (.seq (.while (c.andB e) body) (.while c body)) B) :
    prhlStmt A s₁ (.while c body) B :=
  prhlStmt_of_equiv_right (Stmt.Equiv.splitwhile c e body V hvar) h

/-- `unroll{1}` on a loop that is the whole left statement. -/
theorem prhlStmt_unroll_left {s₂ body : Stmt} {c : Getter Bool ProgramState}
    (h : prhlStmt A (.ifThenElse c (.seq body (.while c body)) .skip) s₂ B) :
    prhlStmt A (.while c body) s₂ B :=
  prhlStmt_of_equiv_left (Stmt.Equiv.unroll c body) h

/-- `unroll{2}` on a loop that is the whole right statement. -/
theorem prhlStmt_unroll_right {s₁ body : Stmt} {c : Getter Bool ProgramState}
    (h : prhlStmt A s₁ (.ifThenElse c (.seq body (.while c body)) .skip) B) :
    prhlStmt A s₁ (.while c body) B :=
  prhlStmt_of_equiv_right (Stmt.Equiv.unroll c body) h

/-! ## Induction -/

/-- A judgment by cases on a measure of the initial states (for an induction on it, e.g. on the
rounds a loop has left: EC's `elim` on an integer in a proof by induction). -/
theorem prhlStmt_of_forall_nat {c₁ c₂ : Stmt} (f : ProgramState → ProgramState → ℕ)
    (h : ∀ k, prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ f σ₁ σ₂ = k) c₁ c₂ B) : prhlStmt A c₁ c₂ B :=
  fun σ₁ σ₂ hA => h (f σ₁ σ₂) σ₁ σ₂ ⟨hA, rfl⟩

/-! ## Transitivity -/

/-- **Transitivity** of statement judgments (EC's `transitivity{i} { code } P Q`, with `code` the
middle statement): the preconditions and postconditions compose through a middle state. -/
theorem prhlStmt.trans {A₂ B₂ : ProgramState → ProgramState → Prop} {c₁ c₂ c₃ : Stmt}
    (h₁ : prhlStmt A c₁ c₂ B) (h₂ : prhlStmt A₂ c₂ c₃ B₂) :
    prhlStmt (fun σ₁ σ₃ => ∃ σ₂, A σ₁ σ₂ ∧ A₂ σ₂ σ₃) c₁ c₃
      (fun τ₁ τ₃ => ∃ τ₂, B τ₁ τ₂ ∧ B₂ τ₂ τ₃) := by
  intro σ₁ σ₃ hA
  obtain ⟨μ, m1, m2, sat⟩ := ProgramDenotation.prhl2.trans h₁ h₂ σ₁ σ₃ hA
  exact ⟨μ, m1, m2, fun x hx => by
    obtain ⟨y, hy⟩ := sat x hx
    exact ⟨y.2, hy⟩⟩

end GaudisCrypt
