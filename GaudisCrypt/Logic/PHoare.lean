import GaudisCrypt.Logic.Hoare

/-!
# Probabilistic Hoare logic

EasyCrypt's `phoare[ c : P ==> Q ] ⋈ r` (`⋈` one of `=`, `≤`, `≥`): from every state satisfying
`P`, the probability that `c` ends in a state satisfying `Q` is `⋈ r`.

The judgment is stated for an *expectation* `g` rather than an event: `Stmt.ewp c g σ` is the
expected value of `g` after running `c` from `σ`, and an event `Q` is its indicator
`if Q then 1 else 0`.  The reason is the sequencing law `phoareStmt_seq_iff`, which is exact,
for all three relations: the judgment about `p; q` is the one about `p` with the expectation `g`
replaced by `q.ewp g`.  So backwards reasoning only ever rewrites the expectation, as long as
the code has an exact wp (everything but loops, including calls to abstract procedures, whose
wp stays a symbolic term).

The relation `ρ` is `Eq`, `LE.le` or `GE.ge` (the constants, not lambdas, so that rules
and the printer can match on them); the bound `r` may depend on the initial
state.
-/

namespace GaudisCrypt

/-- The expected value of `g` after running `c` from `σ`. -/
noncomputable def Stmt.ewp (c : Stmt) (g : ProgramState → ENNReal) : ProgramState → ENNReal :=
  (programDenotation c).wp fun r => g r.2

/-- The expected value of `G` (of the result and the globals) after running the procedure `p` on
`args` from the globals `σ`. -/
noncomputable def Procedure.ewp {sig} (p : Procedure sig) (args : sig.ParamType)
    (G : sig.ret → VariableAssignment → ENNReal) : VariableAssignment → ENNReal :=
  (procedureDenotation p args).wp fun r => G r.1 r.2

/-- `phoare[ A ==> g ] ρ r { c }`: from every state satisfying `A`, the expected value of `g`
    after `c` is in the relation `ρ` to `r`. -/
def phoareStmt (A : ProgramState → Prop) (c : Stmt) (g : ProgramState → ENNReal)
    (ρ : ENNReal → ENNReal → Prop) (r : ProgramState → ENNReal) : Prop :=
  ∀ σ, A σ → ρ (c.ewp g σ) (r σ)

/-- `phoare[ p : A ==> G ] ρ r`: on all arguments and globals satisfying `A`, the expected value
    of `G` after `p` is in the relation `ρ` to `r`. -/
def phoareProc {sig} (A : sig.ParamType → VariableAssignment → Prop) (p : Procedure sig)
    (G : sig.ret → VariableAssignment → ENNReal) (ρ : ENNReal → ENNReal → Prop)
    (r : sig.ParamType → VariableAssignment → ENNReal) : Prop :=
  ∀ args σ, A args σ → ρ (p.ewp args G σ) (r args σ)

/-! ## Events and probabilities -/

open Classical in
/-- The indicator of a proposition, as an expectation: `1` if it holds, else `0` (EC's `b2r`). -/
noncomputable def indicatorE (Q : Prop) : ENNReal := if Q then 1 else 0

@[simp] theorem indicatorE_true : indicatorE True = 1 := by simp [indicatorE]
@[simp] theorem indicatorE_false : indicatorE False = 0 := by simp [indicatorE]
theorem indicatorE_of {Q : Prop} (h : Q) : indicatorE Q = 1 := by simp [indicatorE, h]
theorem indicatorE_of_not {Q : Prop} (h : ¬ Q) : indicatorE Q = 0 := by simp [indicatorE, h]

/-- The probability that the procedure `p`, run on `args` from the globals `σ`, ends with a
    result and globals satisfying `E` — EC's `Pr[p(args) @ &σ : E]`. -/
noncomputable def Procedure.Pr {sig} (p : Procedure sig) (args : sig.ParamType)
    (σ : VariableAssignment) (E : sig.ret → VariableAssignment → Prop) : NNReal :=
  (procedureDenotation p args σ).ofEvent {r | E r.1 r.2}

/-- A probability is the expectation of the event's indicator. -/
theorem Procedure.Pr_eq_ewp {sig} (p : Procedure sig) (args : sig.ParamType)
    (σ : VariableAssignment) (E : sig.ret → VariableAssignment → Prop) :
    (p.Pr args σ E : ENNReal) = p.ewp args (fun v g => indicatorE (E v g)) σ := by
  have hi := expectation_indicator (procedureDenotation p args σ) {r | E r.1 r.2} 1
  rw [one_mul] at hi
  rw [Procedure.Pr, ← hi, Procedure.ewp, ProgramDenotation.wp]
  rfl

/-- EC's `byphoare`: a probability, from a procedure judgment about the event. -/
theorem Procedure.Pr_of_phoareProc {sig} {A : sig.ParamType → VariableAssignment → Prop}
    {p : Procedure sig} {E : sig.ret → VariableAssignment → Prop} {ρ : ENNReal → ENNReal → Prop}
    {r : sig.ParamType → VariableAssignment → ENNReal}
    (h : phoareProc A p (fun v g => indicatorE (E v g)) ρ r)
    {args : sig.ParamType} {σ : VariableAssignment} (hA : A args σ) :
    ρ (p.Pr args σ E) (r args σ) := by
  rw [Procedure.Pr_eq_ewp]
  exact h args σ hA

/-- EC's `islossless p`: `p` terminates with probability `1`, on all arguments and globals. -/
def Procedure.IsLossless {sig} (p : Procedure sig) : Prop :=
  ∀ args σ, p.ewp args (fun _ _ => 1) σ = 1

theorem Procedure.isLossless_iff_phoareProc {sig} (p : Procedure sig) :
    p.IsLossless ↔ phoareProc (fun _ _ => True) p (fun _ _ => 1) Eq (fun _ _ => 1) :=
  ⟨fun h args σ _ => h args σ, fun h args σ => h args σ trivial⟩

/-! ## Hoare triples as probability-`0` judgments -/

/-- `hoare[ A ==> B ] { c }` is `phoare[ A ==> ¬B ] = 0 { c }`. -/
theorem hoareStmt_iff_phoareStmt {A : ProgramState → Prop} {c : Stmt} {B : ProgramState → Prop} :
    hoareStmt A c B ↔ phoareStmt A c (fun σ => indicatorE (¬ B σ)) Eq (fun _ => 0) := by
  rw [hoareStmt_iff_wp]
  have : (Set.indicator {r : Unit × ProgramState | ¬ B r.2} fun _ => (1 : ENNReal))
      = fun r => indicatorE (¬ B r.2) := by
    funext r; by_cases h : B r.2 <;> simp [indicatorE, h]
  simp only [phoareStmt, Stmt.ewp, this]

/-- The same for procedures. -/
theorem hoareProc_iff_phoareProc {sig} {A : sig.ParamType → VariableAssignment → Prop}
    {p : Procedure sig} {B : sig.ret → VariableAssignment → Prop} :
    hoareProc A p B ↔
      phoareProc A p (fun v g => indicatorE (¬ B v g)) Eq
        (fun _ _ => 0) := by
  rw [hoareProc_iff_wp]
  have : (Set.indicator {r : sig.ret × VariableAssignment | ¬ B r.1 r.2} fun _ => (1 : ENNReal))
      = fun r => indicatorE (¬ B r.1 r.2) := by
    funext r; by_cases h : B r.1 r.2 <;> simp [indicatorE, h]
  simp only [phoareProc, Procedure.ewp, this]

/-! ## Structural rules -/

/-- **Sequencing is exact**: the judgment about `p; q` is the one about `p`, with `q`'s expected
    value of `g` in place of `g`. -/
theorem phoareStmt_seq_iff {A : ProgramState → Prop} {p q : Stmt} {g : ProgramState → ENNReal}
    {ρ : ENNReal → ENNReal → Prop} {r : ProgramState → ENNReal} :
    phoareStmt A (.seq p q) g ρ r ↔ phoareStmt A p (q.ewp g) ρ r := by
  simp only [phoareStmt, Stmt.ewp, programDenotation, wp_bind]

/-- Strengthening the precondition. -/
theorem phoareStmt_pre {A A' : ProgramState → Prop} {c : Stmt} {g : ProgramState → ENNReal}
    {ρ : ENNReal → ENNReal → Prop} {r : ProgramState → ENNReal}
    (h : phoareStmt A' c g ρ r) (hA : ∀ σ, A σ → A' σ) : phoareStmt A c g ρ r :=
  fun σ hσ => h σ (hA σ hσ)

/-- An upper bound is monotone in the expectation, downwards. -/
theorem phoareStmt_le_of_le {A : ProgramState → Prop} {c : Stmt} {g g' : ProgramState → ENNReal}
    {r : ProgramState → ENNReal} (h : phoareStmt A c g' LE.le r) (hg : ∀ σ, g σ ≤ g' σ) :
    phoareStmt A c g LE.le r := fun σ hσ =>
  (ProgramDenotation.wp_le_wp_of_le _ _ _ (fun x => hg x.2) σ).trans (h σ hσ)

/-- A lower bound is monotone in the expectation, upwards. -/
theorem phoareStmt_ge_of_ge {A : ProgramState → Prop} {c : Stmt} {g g' : ProgramState → ENNReal}
    {r : ProgramState → ENNReal} (h : phoareStmt A c g' GE.ge r) (hg : ∀ σ, g' σ ≤ g σ) :
    phoareStmt A c g GE.ge r := fun σ hσ =>
  (h σ hσ).trans (ProgramDenotation.wp_le_wp_of_le _ _ _ (fun x => hg x.2) σ)

/-- An exact judgment gives both bounds. -/
theorem phoareStmt_le_of_eq {A : ProgramState → Prop} {c : Stmt} {g : ProgramState → ENNReal}
    {r : ProgramState → ENNReal} (h : phoareStmt A c g Eq r) :
    phoareStmt A c g LE.le r := fun σ hσ => (h σ hσ).le

theorem phoareStmt_ge_of_eq {A : ProgramState → Prop} {c : Stmt} {g : ProgramState → ENNReal}
    {r : ProgramState → ENNReal} (h : phoareStmt A c g Eq r) :
    phoareStmt A c g GE.ge r := fun σ hσ => (h σ hσ).ge

/-- Two bounds give an exact judgment. -/
theorem phoareStmt_eq_of_le_ge {A : ProgramState → Prop} {c : Stmt} {g : ProgramState → ENNReal}
    {r : ProgramState → ENNReal} (h₁ : phoareStmt A c g LE.le r)
    (h₂ : phoareStmt A c g GE.ge r) : phoareStmt A c g Eq r := fun σ hσ =>
  le_antisymm (h₁ σ hσ) (h₂ σ hσ)

/-- At `skip`, the judgment is about `g` itself. -/
theorem phoareStmt_skip_iff {A : ProgramState → Prop} {g : ProgramState → ENNReal}
    {ρ : ENNReal → ENNReal → Prop} {r : ProgramState → ENNReal} :
    phoareStmt A .skip g ρ r ↔ ∀ σ, A σ → ρ (g σ) (r σ) := by
  simp only [phoareStmt, Stmt.ewp, programDenotation, ProgramDenotation.skip, wp_pure]

/-! ## Exact expectations of the statements -/

theorem Stmt.ewp_skip (g : ProgramState → ENNReal) :
    Stmt.ewp (StmtWithHoles.skip) g = g := by
  funext σ
  simp only [Stmt.ewp, programDenotation, ProgramDenotation.skip, wp_pure]

theorem Stmt.ewp_seq (p q : Stmt) (g : ProgramState → ENNReal) :
    Stmt.ewp (StmtWithHoles.seq p q) g = p.ewp (q.ewp g) := by
  simp only [Stmt.ewp, programDenotation, wp_bind]

theorem Stmt.ewp_assign {α} (x : Setter α ProgramState) (e : Getter α ProgramState)
    (g : ProgramState → ENNReal) :
    Stmt.ewp (StmtWithHoles.assign x e) g = fun σ => g (x.set (e.get σ) σ) := by
  funext σ
  simp only [Stmt.ewp, StmtWithHoles.assign, programDenotation, wp_bind, wp_get_g, wp_lift,
    wp_set_g, AsGetter.toG, AsSetter.toS, id_eq, expected_pure]

theorem Stmt.ewp_sample {α} (x : Setter α ProgramState) (e : Getter (SubProbability α) ProgramState)
    (g : ProgramState → ENNReal) :
    Stmt.ewp (StmtWithHoles.sample x e) g = fun σ => (e.get σ).expected fun a => g (x.set a σ) := by
  funext σ
  simp only [Stmt.ewp, programDenotation, wp_bind, wp_get_g, wp_lift, wp_set_g, AsGetter.toG,
    AsSetter.toS, id_eq]

theorem Stmt.ewp_ifThenElse (c : Getter Bool ProgramState) (p q : Stmt)
    (g : ProgramState → ENNReal) :
    Stmt.ewp (StmtWithHoles.ifThenElse c p q) g
      = fun σ => if c.get σ then p.ewp g σ else q.ewp g σ := by
  funext σ
  simp only [Stmt.ewp, programDenotation, wp_bind, wp_get_g, AsGetter.toG, id_eq, wp_ite]

/-- A call's expectation is the callee's, at the arguments, of `g` after writing the result and
    the globals back.  For an abstract callee this stays a symbolic term. -/
theorem Stmt.ewp_call {sig} (x : Setter sig.ret ProgramState) (p : Procedure sig)
    (args : Getter sig.ParamType ProgramState) (g : ProgramState → ENNReal) :
    (Stmt.call x p args).ewp g
      = fun σ => p.ewp (args.get σ) (fun v gl => g (x.set v (ProgramState.globalL.set gl σ)))
          σ.globals := by
  funext σ
  simp only [Stmt.ewp, Stmt.call, StmtWithHoles.call, programDenotation, procedureWithHoles_eta,
    wp_bind, wp_get_g, wp_zoom, wp_set_g, AsGetter.toG, AsSetter.toS, id_eq, Procedure.ewp]
  rfl

/-! ## Expectation algebra

What is left of a judgment once `phoare_wp` has run: sums and quotients of symbolic procedure
expectations.  Linearity, losslessness, and the arithmetic of averages. -/

theorem Procedure.ewp_add {sig} (p : Procedure sig) (args : sig.ParamType)
    (F G : sig.ret → VariableAssignment → ENNReal) (σ : VariableAssignment) :
    p.ewp args (fun v g => F v g + G v g) σ = p.ewp args F σ + p.ewp args G σ :=
  ProgramDenotation.wp_add _ (fun r => F r.1 r.2) (fun r => G r.1 r.2) σ

theorem Procedure.ewp_const_mul {sig} (p : Procedure sig) (args : sig.ParamType) (c : ENNReal)
    (F : sig.ret → VariableAssignment → ENNReal) (σ : VariableAssignment) :
    p.ewp args (fun v g => c * F v g) σ = c * p.ewp args F σ :=
  ProgramDenotation.wp_const_mul _ c (fun r => F r.1 r.2) σ

theorem Procedure.ewp_finset_sum {sig} {β : Type*} [Fintype β] (p : Procedure sig)
    (args : sig.ParamType) (F : β → sig.ret → VariableAssignment → ENNReal)
    (σ : VariableAssignment) :
    p.ewp args (fun v g => ∑ b, F b v g) σ = ∑ b, p.ewp args (F b) σ :=
  ProgramDenotation.wp_finset_sum _ (fun b r => F b r.1 r.2) σ

theorem Procedure.ewp_mono {sig} (p : Procedure sig) (args : sig.ParamType)
    {F G : sig.ret → VariableAssignment → ENNReal} (h : ∀ v g, F v g ≤ G v g)
    (σ : VariableAssignment) : p.ewp args F σ ≤ p.ewp args G σ :=
  ProgramDenotation.wp_le_wp_of_le _ _ _ (fun r => h r.1 r.2) σ

/-- A lossless procedure's expectation of a constant is the constant. -/
theorem Procedure.IsLossless.ewp_const {sig} {p : Procedure sig} (h : p.IsLossless)
    (args : sig.ParamType) (c : ENNReal) (σ : VariableAssignment) :
    p.ewp args (fun _ _ => c) σ = c := by
  have := Procedure.ewp_const_mul p args c (fun _ _ => 1) σ
  simp only [mul_one] at this
  rw [this, h args σ, mul_one]

/-- The expectation of a constant is at most the constant (any procedure). -/
theorem Procedure.ewp_const_le {sig} (p : Procedure sig) (args : sig.ParamType) (c : ENNReal)
    (σ : VariableAssignment) : p.ewp args (fun _ _ => c) σ ≤ c :=
  ProgramDenotation.wp_const_le _ c σ

/-- An event and its negation partition. -/
theorem indicatorE_add_not (Q : Prop) : indicatorE Q + indicatorE (¬ Q) = 1 := by
  by_cases h : Q <;> simp [indicatorE, h]

theorem indicatorE_not_add (Q : Prop) : indicatorE (¬ Q) + indicatorE Q = 1 := by
  rw [add_comm, indicatorE_add_not]

/-- The union bound for two events. -/
theorem indicatorE_or_le (Q Q' : Prop) : indicatorE (Q ∨ Q') ≤ indicatorE Q + indicatorE Q' := by
  by_cases h : Q <;> by_cases h' : Q' <;> simp [indicatorE, h, h']

/-- A uniform draw hits a given point with chance `1 / |α|`. -/
theorem ENNReal.sum_indicatorE_eq_div_card {α : Type*} [Fintype α] (v : α) :
    ∑ x : α, indicatorE (v = x) / (Fintype.card α : ENNReal) = 1 / Fintype.card α := by
  classical
  have : ∀ x : α, indicatorE (v = x) / (Fintype.card α : ENNReal)
      = if v = x then 1 / (Fintype.card α : ENNReal) else 0 := fun x => by
    by_cases h : v = x <;> simp [indicatorE, h]
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The average of a constant over a nonempty finite type is the constant. -/
theorem ENNReal.sum_div_card {α : Type*} [Fintype α] [Nonempty α] (c : ENNReal) :
    ∑ _x : α, c / (Fintype.card α : ENNReal) = c := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.mul_div_cancel' (by simp [Fintype.card_ne_zero]) (by simp)]

/-! ## Calls with a specification

EC's `call (_ : P ==> Q)` for `phoare`: a trailing call `x <- p(a)` is closed by a judgment about
`p`, and the expectation before it becomes the judgment's bound — under the side condition that
the precondition holds at the arguments and the expectation after the call (the *continuation*
`fun v gl => g (x.set v (globalL.set gl σ))`) is related to the judgment's postcondition as the
relation needs.  Where the condition fails, the bound is the trivial one (`⊤` for `≤`, `0` for
`≥`), or for `=` the call's own symbolic expectation, so that the `=` rule is exact. -/

open Classical in
/-- The call rule for upper bounds. -/
theorem phoareStmt_call_le {sig} {A : ProgramState → Prop} {pre : Stmt}
    {x : Setter sig.ret ProgramState} {p : Procedure sig} {a : Getter sig.ParamType ProgramState}
    {g r : ProgramState → ENNReal} {P : sig.ParamType → VariableAssignment → Prop}
    {G : sig.ret → VariableAssignment → ENNReal} {R : sig.ParamType → VariableAssignment → ENNReal}
    (h : phoareProc P p G LE.le R)
    (h' : phoareStmt A pre (fun σ =>
      if P (a.get σ) σ.globals ∧
          ∀ v gl, g (x.set v (ProgramState.globalL.set gl σ)) ≤ G v gl
        then R (a.get σ) σ.globals else ⊤) LE.le r) :
    phoareStmt A (.seq pre (Stmt.call x p a)) g LE.le r := by
  rw [phoareStmt_seq_iff]
  refine phoareStmt_le_of_le h' fun σ => ?_
  rw [Stmt.ewp_call]
  split_ifs with hC
  · exact (Procedure.ewp_mono _ _ hC.2 _).trans (h _ _ hC.1)
  · exact le_top

open Classical in
/-- The call rule for lower bounds. -/
theorem phoareStmt_call_ge {sig} {A : ProgramState → Prop} {pre : Stmt}
    {x : Setter sig.ret ProgramState} {p : Procedure sig} {a : Getter sig.ParamType ProgramState}
    {g r : ProgramState → ENNReal} {P : sig.ParamType → VariableAssignment → Prop}
    {G : sig.ret → VariableAssignment → ENNReal} {R : sig.ParamType → VariableAssignment → ENNReal}
    (h : phoareProc P p G GE.ge R)
    (h' : phoareStmt A pre (fun σ =>
      if P (a.get σ) σ.globals ∧
          ∀ v gl, G v gl ≤ g (x.set v (ProgramState.globalL.set gl σ))
        then R (a.get σ) σ.globals else 0) GE.ge r) :
    phoareStmt A (.seq pre (Stmt.call x p a)) g GE.ge r := by
  rw [phoareStmt_seq_iff]
  refine phoareStmt_ge_of_ge h' fun σ => ?_
  rw [Stmt.ewp_call]
  split_ifs with hC
  · exact (h _ _ hC.1).trans (Procedure.ewp_mono _ _ hC.2 _)
  · exact bot_le

open Classical in
/-- The call rule for exact values: where the condition holds the call's expectation *is* the
    bound, elsewhere it stays as it was. -/
theorem phoareStmt_call_eq {sig} {A : ProgramState → Prop} {pre : Stmt}
    {x : Setter sig.ret ProgramState} {p : Procedure sig} {a : Getter sig.ParamType ProgramState}
    {g r : ProgramState → ENNReal} {ρ : ENNReal → ENNReal → Prop}
    {P : sig.ParamType → VariableAssignment → Prop}
    {G : sig.ret → VariableAssignment → ENNReal} {R : sig.ParamType → VariableAssignment → ENNReal}
    (h : phoareProc P p G Eq R)
    (h' : phoareStmt A pre (fun σ =>
      if P (a.get σ) σ.globals ∧
          ∀ v gl, g (x.set v (ProgramState.globalL.set gl σ)) = G v gl
        then R (a.get σ) σ.globals else (Stmt.call x p a).ewp g σ) ρ r) :
    phoareStmt A (.seq pre (Stmt.call x p a)) g ρ r := by
  rw [phoareStmt_seq_iff]
  convert h' using 3
  split_ifs with hC
  · rw [Stmt.ewp_call, ← h _ _ hC.1]
    exact congrArg (fun F => p.ewp _ F _) (funext fun v => funext fun gl => hC.2 v gl)
  · rfl

/-- An exact procedure judgment gives both bounds. -/
theorem phoareProc_le_of_eq {sig} {A : sig.ParamType → VariableAssignment → Prop}
    {p : Procedure sig} {G : sig.ret → VariableAssignment → ENNReal}
    {R : sig.ParamType → VariableAssignment → ENNReal} (h : phoareProc A p G Eq R) :
    phoareProc A p G LE.le R := fun a σ hA => (h a σ hA).le

theorem phoareProc_ge_of_eq {sig} {A : sig.ParamType → VariableAssignment → Prop}
    {p : Procedure sig} {G : sig.ret → VariableAssignment → ENNReal}
    {R : sig.ParamType → VariableAssignment → ENNReal} (h : phoareProc A p G Eq R) :
    phoareProc A p G GE.ge R := fun a σ hA => (h a σ hA).ge

/-- A procedure judgment as a rewrite rule for the callee's expectation. -/
theorem phoareProc.ewp_eq {sig} {P : sig.ParamType → VariableAssignment → Prop}
    {p : Procedure sig} {G : sig.ret → VariableAssignment → ENNReal}
    {R : sig.ParamType → VariableAssignment → ENNReal} (h : phoareProc P p G Eq R)
    {args : sig.ParamType} {σ : VariableAssignment} (hP : P args σ) :
    p.ewp args G σ = R args σ := h args σ hP

theorem phoareProc.ewp_le {sig} {P : sig.ParamType → VariableAssignment → Prop}
    {p : Procedure sig} {G : sig.ret → VariableAssignment → ENNReal}
    {R : sig.ParamType → VariableAssignment → ENNReal} (h : phoareProc P p G LE.le R)
    {args : sig.ParamType} {σ : VariableAssignment} (hP : P args σ) :
    p.ewp args G σ ≤ R args σ := h args σ hP

theorem phoareProc.ewp_ge {sig} {P : sig.ParamType → VariableAssignment → Prop}
    {p : Procedure sig} {G : sig.ret → VariableAssignment → ENNReal}
    {R : sig.ParamType → VariableAssignment → ENNReal} (h : phoareProc P p G GE.ge R)
    {args : sig.ParamType} {σ : VariableAssignment} (hP : P args σ) :
    R args σ ≤ p.ewp args G σ := h args σ hP

theorem Procedure.ewp_mul_const {sig} (p : Procedure sig) (args : sig.ParamType) (c : ENNReal)
    (F : sig.ret → VariableAssignment → ENNReal) (σ : VariableAssignment) :
    p.ewp args (fun v g => F v g * c) σ = p.ewp args F σ * c := by
  simp only [mul_comm _ c]
  exact Procedure.ewp_const_mul p args c F σ

/-- A conjunction of events is the product of their indicators. -/
theorem indicatorE_and (Q Q' : Prop) : indicatorE (Q ∧ Q') = indicatorE Q * indicatorE Q' := by
  by_cases h : Q <;> by_cases h' : Q' <;> simp [indicatorE, h, h']

/-! ## Loops

The rule for upper bounds: an *expectation invariant* `I` bounds a loop's expectation of `g` if one
iteration (from a state where the test passes) does not increase it, and `g` is below it where the
test fails — `I` is a pre-fixed point of the loop's wp functional (`wp_while_invariant`).  A
qualitative invariant `inv` is folded in as `if inv then ‹potential› else ⊤`. -/

/-- The loop's expectation of `g` is below the invariant `I`. -/
theorem Stmt.ewp_while_le {c : Getter Bool ProgramState} {body : Stmt}
    (I g : ProgramState → ENNReal)
    (hbody : ∀ σ, c.get σ = true → body.ewp I σ ≤ I σ)
    (hexit : ∀ σ, c.get σ = false → g σ ≤ I σ) (σ : ProgramState) :
    Stmt.ewp (StmtWithHoles.while c body) g σ ≤ I σ := by
  have h := wp_while_invariant (ProgramDenotation.get c) (programDenotation body) I
    (fun r => g r.2) fun st => by
      simp only [wp_get_g, AsGetter.toG, id_eq]
      cases hc : c.get st
      · exact hexit st hc
      · exact hbody st hc
  simp only [Stmt.ewp, programDenotation]
  exact h σ

/-- **The loop rule for upper bounds**, for a trailing loop: the body preserves the invariant `I`
    (as an upper bound, from the states where the test passes), the expectation is below `I` where
    the test fails, and the code before the loop is judged with `I` as its expectation. -/
theorem phoareStmt_while_le {A : ProgramState → Prop} {pre body : Stmt}
    {c : Getter Bool ProgramState} {g r : ProgramState → ENNReal} (I : ProgramState → ENNReal)
    (hbody : phoareStmt (fun σ => c.get σ = true) body I LE.le I)
    (hexit : ∀ σ, c.get σ = false → g σ ≤ I σ)
    (hpre : phoareStmt A pre I LE.le r) :
    phoareStmt A (.seq pre (.while c body)) g LE.le r := by
  rw [phoareStmt_seq_iff]
  exact phoareStmt_le_of_le hpre fun σ => Stmt.ewp_while_le I g hbody hexit σ

/-! ## Loops: termination and lower bounds

An upper-bound invariant cannot see that a loop terminates — a loop that never does has
expectation `0`, below everything.  Lower bounds need termination: `Stmt.ewp_while_one` is the
zero-one argument (if every iteration exits with probability at least `ε > 0`, the loop
terminates almost surely), and `Stmt.ewp_while_ge` the lower-bound rule built on it, by
complement: with mass `1`, `Pr[g] = 1 − Pr[¬g]`, and `1 − I` is an upper invariant for `1 − g`. -/

theorem Stmt.ewp_add (s : Stmt) (F G : ProgramState → ENNReal) (σ : ProgramState) :
    s.ewp (fun τ => F τ + G τ) σ = s.ewp F σ + s.ewp G σ :=
  ProgramDenotation.wp_add _ (fun r => F r.2) (fun r => G r.2) σ

theorem Stmt.ewp_const_mul (s : Stmt) (c : ENNReal) (F : ProgramState → ENNReal)
    (σ : ProgramState) : s.ewp (fun τ => c * F τ) σ = c * s.ewp F σ :=
  ProgramDenotation.wp_const_mul _ c (fun r => F r.2) σ

theorem Stmt.ewp_mono (s : Stmt) {F G : ProgramState → ENNReal} (h : ∀ τ, F τ ≤ G τ)
    (σ : ProgramState) : s.ewp F σ ≤ s.ewp G σ :=
  ProgramDenotation.wp_le_wp_of_le _ _ _ (fun r => h r.2) σ

theorem Stmt.ewp_const_le (s : Stmt) (c : ENNReal) (σ : ProgramState) :
    s.ewp (fun _ => c) σ ≤ c :=
  ProgramDenotation.wp_const_le _ c σ

/-- The fixed-point equation of a loop. -/
theorem Stmt.ewp_while_unfold (c : Getter Bool ProgramState) (body : Stmt)
    (g : ProgramState → ENNReal) (σ : ProgramState) :
    Stmt.ewp (StmtWithHoles.while c body) g σ
      = if c.get σ then body.ewp (Stmt.ewp (StmtWithHoles.while c body) g) σ else g σ := by
  simp only [Stmt.ewp, programDenotation]
  conv_lhs => rw [wp_while_unfold]
  simp only [wp_get_g, AsGetter.toG, id_eq]

/-- **Almost-sure termination** (the zero-one argument): if the body is lossless and exits the
    loop with probability at least `ε > 0` from every state where the test passes, the loop
    terminates with probability `1`. -/
theorem Stmt.ewp_while_one {c : Getter Bool ProgramState} {body : Stmt} (ε : ENNReal)
    (hε0 : ε ≠ 0) (hε1 : ε ≤ 1)
    (hll : ∀ σ, c.get σ = true → body.ewp (fun _ => 1) σ = 1)
    (hprog : ∀ σ, c.get σ = true → ε ≤ body.ewp (fun τ => indicatorE (c.get τ = false)) σ)
    (σ : ProgramState) : Stmt.ewp (StmtWithHoles.while c body) (fun _ => 1) σ = 1 := by
  set T := Stmt.ewp (StmtWithHoles.while c body) (fun _ => 1) with hT
  have hT1 : ∀ τ, T τ ≤ 1 := fun τ => Stmt.ewp_const_le _ 1 τ
  have hunfold : ∀ τ, T τ = if c.get τ then body.ewp T τ else 1 :=
    fun τ => Stmt.ewp_while_unfold c body _ τ
  set m := ⨅ τ, T τ
  have hm1 : m ≤ 1 := (iInf_le _ σ).trans (hT1 σ)
  -- every state is at least `m + (1 − m) ε` likely to terminate
  have hlow : ∀ τ, m + (1 - m) * ε ≤ T τ := by
    intro τ
    rw [hunfold τ]
    split_ifs with hc
    · have hpt : ∀ τ', m + (1 - m) * indicatorE (c.get τ' = false) ≤ T τ' := by
        intro τ'
        cases hc' : c.get τ'
        · rw [hunfold τ', hc', indicatorE_of rfl, mul_one, add_tsub_cancel_of_le hm1]
          simp
        · rw [indicatorE_of_not (by simp), mul_zero, add_zero]
          exact iInf_le _ τ'
      calc m + (1 - m) * ε
          ≤ m * body.ewp (fun _ => 1) τ
              + (1 - m) * body.ewp (fun τ' => indicatorE (c.get τ' = false)) τ := by
            rw [hll τ hc, mul_one]
            gcongr
            exact hprog τ hc
        _ = body.ewp (fun τ' => m + (1 - m) * indicatorE (c.get τ' = false)) τ := by
            rw [Stmt.ewp_add, Stmt.ewp_const_mul]
            congr 1
            have := Stmt.ewp_const_mul body m (fun _ => 1) τ
            simp only [mul_one] at this
            exact this.symm
        _ ≤ body.ewp T τ := Stmt.ewp_mono _ hpt τ
    · calc m + (1 - m) * ε ≤ m + (1 - m) * 1 := by gcongr
        _ = 1 := by rw [mul_one, add_tsub_cancel_of_le hm1]
  -- so `m ≥ m + (1 − m) ε`, which forces `m = 1`
  have hle : m + (1 - m) * ε ≤ m + 0 := by rw [add_zero]; exact le_iInf hlow
  have hm_top : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hm1
  have h0 : (1 - m) * ε = 0 := le_antisymm ((ENNReal.add_le_add_iff_left hm_top).mp hle) bot_le
  have hm : 1 ≤ m := tsub_eq_zero_iff_le.mp ((mul_eq_zero.mp h0).resolve_right hε0)
  exact le_antisymm (hT1 σ) (hm.trans (iInf_le _ σ))

/-- With mass `1`, the expectation of `1 − g` is `1` minus that of `g` (for `g ≤ 1`). -/
theorem Stmt.ewp_one_sub (s : Stmt) {g : ProgramState → ENNReal} (hg : ∀ τ, g τ ≤ 1)
    {σ : ProgramState} (h1 : s.ewp (fun _ => 1) σ = 1) :
    s.ewp (fun τ => 1 - g τ) σ = 1 - s.ewp g σ := by
  have hsum : s.ewp g σ + s.ewp (fun τ => 1 - g τ) σ = 1 := by
    have h : (fun τ => g τ + (1 - g τ)) = fun _ => (1 : ENNReal) :=
      funext fun τ => add_tsub_cancel_of_le (hg τ)
    rw [← Stmt.ewp_add, h, h1]
  have hfin : s.ewp g σ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_self_add)
  exact ENNReal.eq_sub_of_add_eq hfin (by rw [add_comm]; exact hsum)

/-- **The lower-bound rule for a loop**: an invariant `I ≤ 1` that one iteration does not decrease
    (where the test passes) and that is below `g` where the test fails is a lower bound for the
    loop's expectation of `g ≤ 1`, provided the loop terminates almost surely
    (`Stmt.ewp_while_one`). -/
theorem Stmt.ewp_while_ge {c : Getter Bool ProgramState} {body : Stmt}
    (I g : ProgramState → ENNReal) (hI1 : ∀ τ, I τ ≤ 1) (hg1 : ∀ τ, g τ ≤ 1)
    (hll : ∀ σ, c.get σ = true → body.ewp (fun _ => 1) σ = 1)
    (hterm : ∀ σ, Stmt.ewp (StmtWithHoles.while c body) (fun _ => 1) σ = 1)
    (hbody : ∀ σ, c.get σ = true → I σ ≤ body.ewp I σ)
    (hexit : ∀ σ, c.get σ = false → I σ ≤ g σ) (σ : ProgramState) :
    I σ ≤ Stmt.ewp (StmtWithHoles.while c body) g σ := by
  -- `1 − I` bounds the loop's expectation of `1 − g` from above
  have hup : Stmt.ewp (StmtWithHoles.while c body) (fun τ => 1 - g τ) σ ≤ 1 - I σ := by
    refine Stmt.ewp_while_le (fun τ => 1 - I τ) _ (fun τ hc => ?_) (fun τ hc => ?_) σ
    · rw [Stmt.ewp_one_sub body hI1 (hll τ hc)]
      exact tsub_le_tsub_left (hbody τ hc) 1
    · exact tsub_le_tsub_left (hexit τ hc) 1
  rw [Stmt.ewp_one_sub _ hg1 (hterm σ)] at hup
  have hfin : Stmt.ewp (StmtWithHoles.while c body) g σ ≤ 1 :=
    (Stmt.ewp_mono _ hg1 σ).trans (Stmt.ewp_const_le _ 1 σ)
  calc I σ = 1 - (1 - I σ) := (ENNReal.sub_sub_cancel ENNReal.one_ne_top (hI1 σ)).symm
    _ ≤ 1 - (1 - Stmt.ewp (StmtWithHoles.while c body) g σ) := tsub_le_tsub_left hup 1
    _ = _ := ENNReal.sub_sub_cancel ENNReal.one_ne_top hfin

/-- An indicator is at most `1`. -/
@[simp] theorem indicatorE_le_one (Q : Prop) : indicatorE Q ≤ 1 := by
  by_cases h : Q <;> simp [indicatorE, h]

/-- **The loop rule for lower bounds**, for a trailing loop: an invariant `I ≤ 1` that the body
    does not decrease (from the states where the test passes) and that is below `g ≤ 1` where the
    test fails, and almost-sure termination — the body is lossless and exits the loop with
    probability at least `ε > 0` (`Stmt.ewp_while_one`).  The code before the loop is judged with
    `I` as its expectation. -/
theorem phoareStmt_while_ge {A : ProgramState → Prop} {pre body : Stmt}
    {c : Getter Bool ProgramState} {g r : ProgramState → ENNReal} (I : ProgramState → ENNReal)
    (ε : ENNReal)
    (hbody : phoareStmt (fun σ => c.get σ = true) body I GE.ge I)
    (hexit : ∀ σ, c.get σ = false → I σ ≤ g σ)
    (hpre : phoareStmt A pre I GE.ge r)
    (hll : phoareStmt (fun σ => c.get σ = true) body (fun _ => 1) Eq (fun _ => 1))
    (hprog : phoareStmt (fun σ => c.get σ = true) body (fun τ => indicatorE (c.get τ = false))
      GE.ge (fun _ => ε))
    (hI1 : ∀ τ, I τ ≤ 1) (hg1 : ∀ τ, g τ ≤ 1) (hε0 : ε ≠ 0) (hε1 : ε ≤ 1) :
    phoareStmt A (.seq pre (.while c body)) g GE.ge r := by
  rw [phoareStmt_seq_iff]
  refine phoareStmt_ge_of_ge hpre fun σ => ?_
  exact Stmt.ewp_while_ge I g hI1 hg1 hll
    (Stmt.ewp_while_one ε hε0 hε1 hll hprog) hbody hexit σ

/-- Two procedure bounds give an exact judgment. -/
theorem phoareProc_eq_of_le_ge {sig} {A : sig.ParamType → VariableAssignment → Prop}
    {p : Procedure sig} {G : sig.ret → VariableAssignment → ENNReal}
    {R : sig.ParamType → VariableAssignment → ENNReal} (h₁ : phoareProc A p G LE.le R)
    (h₂ : phoareProc A p G GE.ge R) : phoareProc A p G Eq R := fun a σ hA =>
  le_antisymm (h₁ a σ hA) (h₂ a σ hA)

/-! ## Procedure judgments as statement judgments -/

/-- A procedure judgment is the statement judgment about the one-line body `res <- p(args);`, as
    for Hoare triples (`hoareProc_as_hoareStmt`). -/
theorem phoareProc_as_phoareStmt {sig : ProcedureSignature}
    (resL : Lens sig.ret VariableAssignment) (argsL : Lens sig.ParamType VariableAssignment)
    (A : sig.ParamType → VariableAssignment → Prop) (p : Procedure sig)
    (G : sig.ret → VariableAssignment → ENNReal) (ρ : ENNReal → ENNReal → Prop)
    (r : sig.ParamType → VariableAssignment → ENNReal) :
    phoareProc A p G ρ r ↔
      phoareStmt
        (fun σ => A (argsL.get σ.locals) σ.globals)
        (Stmt.call resL.intoLocal p argsL.intoLocal)
        (fun σ => G (resL.get σ.locals) σ.globals) ρ
        (fun σ => r (argsL.get σ.locals) σ.globals) := by
  -- the statement's expectation is the procedure's: the result slot reads back the result
  have key : ∀ σ : ProgramState,
      (Stmt.call resL.intoLocal p argsL.intoLocal).ewp
          (fun σ => G (resL.get σ.locals) σ.globals) σ
        = p.ewp (argsL.get σ.locals) G σ.globals := by
    intro σ
    rw [Stmt.ewp_call]
    simp only [Lens.intoLocal, Lens.chain, ProgramState.localL, ProgramState.globalL,
      Lens.set_get]
  constructor
  · intro h σ hA
    rw [key]
    exact h _ _ hA
  · intro h args st hA
    have hget := h ⟨st, argsL.set args VariableAssignment.init⟩ (by simpa [Lens.set_get] using hA)
    rw [key] at hget
    simpa [Lens.set_get] using hget

end GaudisCrypt
