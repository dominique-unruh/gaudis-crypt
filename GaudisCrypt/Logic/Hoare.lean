import GaudisCrypt.Language.Programs
import GaudisCrypt.WeakestPreconditions

namespace GaudisCrypt

variable [ProgramSpec]

def hoareStmt (A : ProcedureState l → Prop) (p : Stmt l) (B : ProcedureState l → Prop) :=
  ∀ σ, A σ → (programDenotation p σ).ofEvent (fun (_, σ') => ¬ B σ') = 0

def hoareProc {sig} (A : sig.ParamType → State → Prop) (p : Procedure sig)
    (B : sig.ret → State → Prop) :=
  ∀ args σ, A args σ → (procedureDenotation p args σ).ofEvent (fun (ret, σ') => ¬ B ret σ') = 0


omit [ProgramSpec] in
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

/-- `hoareStmt` is monotone in its postcondition: a weaker `B` is a weaker triple, because the null
    event `¬ B` only shrinks. -/
lemma hoareStmt_mono {l} {A : ProcedureState l → Prop} {p : Stmt l}
    {B₁ B₂ : ProcedureState l → Prop} (hB : ∀ σ, B₁ σ → B₂ σ) (h : hoareStmt A p B₁) :
    hoareStmt A p B₂ := fun σ hA =>
  SubProbability.ofEvent_eq_zero_of_subset (fun _ hq hb => hq (hB _ hb)) (h σ hA)

/-- `hoareProc` is monotone in its postcondition, for the same reason as `hoareStmt_mono`. -/
lemma hoareProc_mono {sig} {A : sig.ParamType → State → Prop} {p : Procedure sig}
    {B₁ B₂ : sig.ret → State → Prop} (hB : ∀ r σ, B₁ r σ → B₂ r σ) (h : hoareProc A p B₁) :
    hoareProc A p B₂ := fun args σ hA =>
  SubProbability.ofEvent_eq_zero_of_subset (fun _ hq hb => hq (hB _ _ hb)) (h args σ hA)

/-- A `hoareStmt` triple from a `wp` computation: `wp` against the indicator of the failure event is
    that event's mass (`expectation_indicator`), so the triple is exactly that `wp` being `0`. -/
lemma hoareStmt_of_wp {l} {A : ProcedureState l → Prop} {p : Stmt l} {B : ProcedureState l → Prop}
    (h : ∀ σ, A σ →
      (programDenotation p).wp (Set.indicator {r | ¬ B r.2} fun _ => 1) σ = 0) :
    hoareStmt A p B := by
  intro σ hA
  have h0 := h σ hA
  simp only [ProgramDenotation.wp, expectation_indicator, one_mul, ENNReal.coe_eq_zero] at h0
  exact h0

/-- The same for `hoareProc`. -/
lemma hoareProc_of_wp {sig} {A : sig.ParamType → State → Prop} {p : Procedure sig}
    {B : sig.ret → State → Prop}
    (h : ∀ args σ, A args σ →
      (procedureDenotation p args).wp
        (Set.indicator {r | ¬ B r.1 r.2} fun _ => 1) σ = 0) :
    hoareProc A p B := by
  intro args σ hA
  have h0 := h args σ hA
  simp only [ProgramDenotation.wp, expectation_indicator, one_mul, ENNReal.coe_eq_zero] at h0
  exact h0


end GaudisCrypt
