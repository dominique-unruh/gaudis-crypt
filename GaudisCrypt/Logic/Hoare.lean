import GaudisCrypt.Language.Programs
import GaudisCrypt.WeakestPreconditions

namespace GaudisCrypt

def hoareStmt (A : ProgramState → Prop) (p : Stmt) (B : ProgramState → Prop) :=
  ∀ σ, A σ → (programDenotation p σ).ofEvent (fun (_, σ') => ¬ B σ') = 0

def hoareProc {sig} (A : sig.ParamType → VariableAssignment → Prop) (p : Procedure sig)
    (B : sig.ret → VariableAssignment → Prop) :=
  ∀ args σ, A args σ → (procedureDenotation p args σ).ofEvent (fun (ret, σ') => ¬ B ret σ') = 0


-- TODO: belongs in `Language/SubProbability.lean` next to `ofEvent`.
/-- A sub-event of a null event is null.  `ofEvent` is `toNNReal` of the measure and the measure
    is finite (total mass `≤ 1`), so the `ℝ≥0` and the `ℝ≥0∞` values vanish together and
    monotonicity of the measure carries over. -/
lemma SubProbability.ofEvent_eq_zero_of_subset {α} {μ : SubProbability α} {E F : Set α}
    (hEF : E ⊆ F) (h : μ.ofEvent F = 0) : μ.ofEvent E = 0 := by
  have hfin : μ.1 F ≠ ⊤ :=
    (((MeasureTheory.measure_mono (Set.subset_univ _)).trans μ.2.1).trans_lt ENNReal.one_lt_top).ne
  rw [SubProbability.ofEvent, ENNReal.toNNReal_eq_zero_iff] at h ⊢
  exact Or.inl (nonpos_iff_eq_zero.mp
    ((MeasureTheory.measure_mono hEF).trans_eq (h.resolve_right hfin)))

/-- An expectation is `0` when the function vanishes on the support: the measure is discrete,
    so the points outside the support carry no mass. -/
theorem SubProbability.expected_eq_zero_of_support {α} {μ : SubProbability α}
    {f : α → ENNReal} (h : ∀ a ∈ μ.support, f a = 0) : μ.expected f = 0 := by
  rw [SubProbability.expected, lintegral_eq_tsum_smul μ.2.2]
  refine ENNReal.tsum_eq_zero.mpr fun a => ?_
  by_cases ha : a ∈ μ.support
  · rw [h a ha, mul_zero]
  · have hfin : μ.1 {a} ≠ ⊤ :=
      (((MeasureTheory.measure_mono (Set.subset_univ _)).trans μ.2.1).trans_lt
        ENNReal.one_lt_top).ne
    have h0 : (μ.1 {a}).toNNReal = 0 := not_not.mp ha
    rw [(ENNReal.toNNReal_eq_zero_iff _).mp h0 |>.resolve_right hfin, zero_mul]

/-- `hoareStmt` is monotone in its postcondition: a weaker `B` is a weaker triple, because the null
    event `¬ B` only shrinks. -/
lemma hoareStmt_mono {A : ProgramState → Prop} {p : Stmt}
    {B₁ B₂ : ProgramState → Prop} (hB : ∀ σ, B₁ σ → B₂ σ) (h : hoareStmt A p B₁) :
    hoareStmt A p B₂ := fun σ hA =>
  SubProbability.ofEvent_eq_zero_of_subset (fun _ hq hb => hq (hB _ hb)) (h σ hA)

/-- `hoareProc` is monotone in its postcondition, for the same reason as `hoareStmt_mono`. -/
lemma hoareProc_mono {sig} {A : sig.ParamType → VariableAssignment → Prop} {p : Procedure sig}
    {B₁ B₂ : sig.ret → VariableAssignment → Prop} (hB : ∀ r σ, B₁ r σ → B₂ r σ)
    (h : hoareProc A p B₁) :
    hoareProc A p B₂ := fun args σ hA =>
  SubProbability.ofEvent_eq_zero_of_subset (fun _ hq hb => hq (hB _ _ hb)) (h args σ hA)

/-- A `hoareStmt` triple *is* a `wp` statement: `wp` against the indicator of the failure event is
    that event's mass (`expectation_indicator`), so the triple is exactly that `wp` being `0`. -/
theorem hoareStmt_iff_wp {A : ProgramState → Prop} {p : Stmt}
    {B : ProgramState → Prop} :
    hoareStmt A p B ↔ ∀ σ, A σ →
      (programDenotation p).wp (Set.indicator {r | ¬ B r.2} fun _ => 1) σ = 0 := by
  simp only [hoareStmt, ProgramDenotation.wp, expectation_indicator, one_mul, ENNReal.coe_eq_zero]
  rfl

/-- The same for `hoareProc`. -/
theorem hoareProc_iff_wp {sig} {A : sig.ParamType → VariableAssignment → Prop}
    {p : Procedure sig} {B : sig.ret → VariableAssignment → Prop} :
    hoareProc A p B ↔ ∀ args σ, A args σ →
      (procedureDenotation p args).wp (Set.indicator {r | ¬ B r.1 r.2} fun _ => 1) σ = 0 := by
  simp only [hoareProc, ProgramDenotation.wp, expectation_indicator, one_mul, ENNReal.coe_eq_zero]
  rfl

/-- A `hoareStmt` triple from a `wp` computation — the direction of `hoareStmt_iff_wp` that proofs
    actually use. -/
lemma hoareStmt_of_wp {A : ProgramState → Prop} {p : Stmt} {B : ProgramState → Prop}
    (h : ∀ σ, A σ →
      (programDenotation p).wp (Set.indicator {r | ¬ B r.2} fun _ => 1) σ = 0) :
    hoareStmt A p B :=
  hoareStmt_iff_wp.mpr h

/-- The same for `hoareProc`. -/
lemma hoareProc_of_wp {sig} {A : sig.ParamType → VariableAssignment → Prop} {p : Procedure sig}
    {B : sig.ret → VariableAssignment → Prop}
    (h : ∀ args σ, A args σ →
      (procedureDenotation p args).wp
        (Set.indicator {r | ¬ B r.1 r.2} fun _ => 1) σ = 0) :
    hoareProc A p B :=
  hoareProc_iff_wp.mpr h

/-- Strengthening the precondition.  The triple comes first, so that `apply hoare_pre` leaves
    it with an open precondition `?A'`, to be filled by the wp steps, and the implication into
    it as the last goal. -/
theorem hoare_pre {A A' : ProgramState → Prop} {p : Stmt} {B : ProgramState → Prop}
    (h : hoareStmt A' p B) (hA : ∀ σ, A σ → A' σ) : hoareStmt A p B :=
  fun σ hσ => h σ (hA σ hσ)

/-- Weakening the postcondition (`hoareStmt_mono`, with the triple first as in `hoare_pre`):
    `apply hoare_post` leaves the triple with an open postcondition `?B'` and the implication out
    of it as the last goal. -/
theorem hoare_post {A : ProgramState → Prop} {p : Stmt} {B B' : ProgramState → Prop}
    (h : hoareStmt A p B') (hB : ∀ σ, B' σ → B σ) : hoareStmt A p B :=
  hoareStmt_mono hB h

/-- The wp rule for sampling: the postcondition must hold after writing any value in the
    support of the sampled distribution. -/
theorem hoare_sample_wp {α} {e : Getter (SubProbability α) ProgramState}
    (x : Setter α ProgramState) (B : ProgramState → Prop) :
    hoareStmt (fun σ => ∀ a ∈ (e.get σ).support, B (x.set a σ)) (.sample x e) B := by
  refine hoareStmt_of_wp fun σ hA => ?_
  simp only [programDenotation, wp_bind, wp_get_g, wp_lift, wp_set_g, AsGetter.toG,
    AsSetter.toS, id_eq]
  exact SubProbability.expected_eq_zero_of_support fun a ha =>
    Set.indicator_of_notMem (not_not.mpr (hA a ha)) _

/-- The wp rule for assignment: the postcondition, at the state with the value written. -/
theorem hoare_assign_wp {α} (x : Setter α ProgramState) (e : Getter α ProgramState)
    (B : ProgramState → Prop) :
    hoareStmt (fun σ => B (x.set (e.get σ) σ)) (.assign x e) B := by
  refine hoareStmt_of_wp fun σ hA => ?_
  simp only [StmtWithHoles.assign, programDenotation, wp_bind, wp_get_g, wp_lift, wp_set_g,
    AsGetter.toG, AsSetter.toS, id_eq, expected_pure]
  exact Set.indicator_of_notMem (not_not.mpr hA) _

/-- A procedure triple is the statement triple about the one-line body

      res <- p(args);

    where `res` and `args` are any two lenses into the caller's locals.  The callee runs in its own
    frame, so the two need not be disjoint, and neither needs to avoid `p`'s parameter names.
    `args` is read before `res` is written, and only `res` and the globals are read afterwards.
    `hoareStmt` quantifies over every initial state; the `←` direction picks one whose `args` slot
    holds the given arguments.  The tactic `hoare_proc_to_stmt` (`Syntax/HoareSyntax.lean`) picks
    the two for a given triple: one local variable per parameter, and one for the result. -/
theorem hoareProc_as_hoareStmt {sig : ProcedureSignature}
    (resL : Lens sig.ret VariableAssignment) (argsL : Lens sig.ParamType VariableAssignment)
    (A : sig.ParamType → VariableAssignment → Prop) (p : Procedure sig)
    (B : sig.ret → VariableAssignment → Prop) :
    hoareProc A p B ↔
      hoareStmt
        (fun σ => A (argsL.get σ.locals) σ.globals)
        (Stmt.call resL.intoLocal p argsL.intoLocal)
        (fun σ => B (resL.get σ.locals) σ.globals) := by
  rw [hoareProc_iff_wp, hoareStmt_iff_wp]
  -- The statement's `wp` is the procedure's own: reading `args` and writing `res` are both
  -- deterministic, and neither touches the global state the postcondition looks at.
  have key : ∀ σ : ProgramState,
      (programDenotation (Stmt.call resL.intoLocal p argsL.intoLocal)).wp
          (Set.indicator {r | ¬ B (resL.get r.2.locals) r.2.globals} fun _ => 1) σ
        = (procedureDenotation p (argsL.get σ.locals)).wp
            (Set.indicator {r | ¬ B r.1 r.2} fun _ => 1) σ.globals := by
    intro σ
    simp only [Stmt.call, StmtWithHoles.call, programDenotation, procedureWithHoles_eta,
      wp_bind, wp_get_g, wp_zoom, wp_set_g, AsGetter.toG, AsSetter.toS, id_eq]
    congr 1
    funext as'
    -- the failure events correspond: `res` reads back `as'.1`, and writing it leaves the global
    -- state at `as'.2`
    have hmem : (((), resL.intoLocal.set as'.1 (ProgramState.globalL.set as'.2 σ))
          ∈ {r | ¬ B (resL.get r.2.locals) r.2.globals}) ↔ as' ∈ {r | ¬ B r.1 r.2} := by
      simp only [Set.mem_setOf_eq, Lens.intoLocal, Lens.chain, ProgramState.localL,
        ProgramState.globalL, Lens.set_get]
    by_cases h : as' ∈ {r : sig.ret × VariableAssignment | ¬ B r.1 r.2}
    · rw [Set.indicator_of_mem (hmem.mpr h), Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (fun hc => h (hmem.mp hc)), Set.indicator_of_notMem h]
  constructor
  · intro h σ hA
    rw [key]
    exact h _ _ hA
  · intro h args st hA
    have hget := h ⟨st, argsL.set args VariableAssignment.init⟩ (by simpa [Lens.set_get] using hA)
    rw [key] at hget
    simpa [Lens.set_get] using hget

end GaudisCrypt
