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
