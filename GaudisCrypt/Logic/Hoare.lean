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

/-- A `hoareStmt` triple *is* a `wp` statement: `wp` against the indicator of the failure event is
    that event's mass (`expectation_indicator`), so the triple is exactly that `wp` being `0`. -/
theorem hoareStmt_iff_wp {l} {A : ProcedureState l → Prop} {p : Stmt l}
    {B : ProcedureState l → Prop} :
    hoareStmt A p B ↔ ∀ σ, A σ →
      (programDenotation p).wp (Set.indicator {r | ¬ B r.2} fun _ => 1) σ = 0 := by
  simp only [hoareStmt, ProgramDenotation.wp, expectation_indicator, one_mul, ENNReal.coe_eq_zero]
  rfl

/-- The same for `hoareProc`. -/
theorem hoareProc_iff_wp {sig} {A : sig.ParamType → State → Prop} {p : Procedure sig}
    {B : sig.ret → State → Prop} :
    hoareProc A p B ↔ ∀ args σ, A args σ →
      (procedureDenotation p args).wp (Set.indicator {r | ¬ B r.1 r.2} fun _ => 1) σ = 0 := by
  simp only [hoareProc, ProgramDenotation.wp, expectation_indicator, one_mul, ENNReal.coe_eq_zero]
  rfl

/-- A `hoareStmt` triple from a `wp` computation — the direction of `hoareStmt_iff_wp` that proofs
    actually use. -/
lemma hoareStmt_of_wp {l} {A : ProcedureState l → Prop} {p : Stmt l} {B : ProcedureState l → Prop}
    (h : ∀ σ, A σ →
      (programDenotation p).wp (Set.indicator {r | ¬ B r.2} fun _ => 1) σ = 0) :
    hoareStmt A p B :=
  hoareStmt_iff_wp.mpr h

/-- The same for `hoareProc`. -/
lemma hoareProc_of_wp {sig} {A : sig.ParamType → State → Prop} {p : Procedure sig}
    {B : sig.ret → State → Prop}
    (h : ∀ args σ, A args σ →
      (procedureDenotation p args).wp
        (Set.indicator {r | ¬ B r.1 r.2} fun _ => 1) σ = 0) :
    hoareProc A p B :=
  hoareProc_iff_wp.mpr h


-- TODO: the three lenses below belong in `Language/Lens.lean` / next to `typeListToTuple` in
-- `Language/Programs.lean`; they are here while `hoareProc_as_hoareStmt` is being drafted.

/-- The trivial lens onto `Unit`: the one value to read, and writing it is a no-op.  The lens laws
    hold by `Unit`'s eta — in particular `set_get` is `() = v`. -/
def Lens.unit {m : Type} : Lens Unit m where
  get _ := ()
  set _ s := s
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

/-- The head component of `typeListToTuple (x :: xs)`.  Two cases, because a one-element
    `typeListToTuple` *is* that element rather than a pair with `Unit`. -/
def typeListToTuple.headL : (x : Type) → (xs : List Type) → Lens x (typeListToTuple (x :: xs))
  | _, []     => Lens.id
  | _, _ :: _ => Lens.fst

/-- The tail components of `typeListToTuple (x :: xs)`, i.e. `typeListToTuple xs`.  At `xs = []`
    that is `Unit`, which no component of the tuple holds — hence `Lens.unit`. -/
def typeListToTuple.tailL : (x : Type) → (xs : List Type) →
    Lens (typeListToTuple xs) (typeListToTuple (x :: xs))
  | _, []     => Lens.unit
  | _, _ :: _ => Lens.snd

/-- `typeListToTuple (x :: xs)` assembled from a head and a tail — the constructor matching
    `typeListToTuple.headL` and `typeListToTuple.tailL`.  At `xs = []` the tail carries no
    information and is discarded. -/
def typeListToTuple.cons : (x : Type) → (xs : List Type) → x → typeListToTuple xs →
    typeListToTuple (x :: xs)
  | _, [],     v, _  => v
  | _, _ :: _, v, vs => (v, vs)

omit [ProgramSpec] in
@[simp] theorem typeListToTuple.headL_get_cons (x : Type) (xs : List Type) (v : x)
    (vs : typeListToTuple xs) :
    (typeListToTuple.headL x xs).get (typeListToTuple.cons x xs v vs) = v := by
  cases xs <;> rfl

omit [ProgramSpec] in
@[simp] theorem typeListToTuple.tailL_get_cons (x : Type) (xs : List Type) (v : x)
    (vs : typeListToTuple xs) :
    (typeListToTuple.tailL x xs).get (typeListToTuple.cons x xs v vs) = vs := by
  cases xs <;> rfl

/-- `res`, the head slot of the caller's local state `typeListToTuple (sig.ret :: sig.params)`.
    That local state is a raw tuple, not a `ProcedureScope`, so nothing here needs
    `Inhabited sig.ret`, as a `var res : sig.ret;` declaration would. -/
abbrev ProcedureSignature.resL (sig : ProcedureSignature) :
    Lens sig.ret (ProcedureState (typeListToTuple (sig.ret :: sig.params))) :=
  ProcedureState.scopedL.chain (typeListToTuple.headL sig.ret sig.params)

/-- The argument expression of the call: the parameter slots of the caller's local state. -/
abbrev ProcedureSignature.argsL (sig : ProcedureSignature) :
    Lens sig.ParamType (ProcedureState (typeListToTuple (sig.ret :: sig.params))) :=
  ProcedureState.scopedL.chain (typeListToTuple.tailL sig.ret sig.params)

/-- Writing `res` leaves the global state alone — it goes into the `locals` field. -/
@[simp] theorem ProcedureSignature.global_resL_set (sig : ProcedureSignature) (r : sig.ret)
    (τ : ProcedureState (typeListToTuple (sig.ret :: sig.params))) :
    (sig.resL.set r τ).global = τ.global := rfl

/-- The caller state assembled from a result value and an argument tuple has those arguments. -/
@[simp] theorem ProcedureSignature.argsL_get_cons (sig : ProcedureSignature) (st : State)
    (r : sig.ret) (args : sig.ParamType) :
    sig.argsL.get ⟨st, typeListToTuple.cons sig.ret sig.params r args⟩ = args := by
  simp [ProcedureSignature.argsL, Lens.chain, ProcedureState.scopedL]

/-- A procedure triple is the statement triple about the one-line body

      res <- p(args);

    run in a local state that is the result slot followed by `sig`'s own parameter slots.  The
    parameters being the caller's, `args` is just the projection onto them — no assignment is
    needed to set the call up, and `res` needs no `var` declaration.  `hoareStmt` quantifies over
    every initial state, i.e. over every `(res₀, args, σ)`, which is
    `hoareProc`'s `∀ args σ` plus an unconstrained `res₀` that neither side's condition mentions —
    so the two are equivalent, not merely one-directional. -/
theorem hoareProc_as_hoareStmt {sig : ProcedureSignature}
    (A : sig.ParamType → State → Prop) (p : Procedure sig) (B : sig.ret → State → Prop) :
    hoareProc A p B ↔
      hoareStmt (l := typeListToTuple (sig.ret :: sig.params))
        (fun σ => A (sig.argsL.get σ) σ.global)
        (Stmt.call sig.resL p sig.argsL)
        (fun σ => B (sig.resL.get σ) σ.global) := by
  rw [hoareProc_iff_wp, hoareStmt_iff_wp]
  -- The statement's `wp` is the procedure's own: reading `args` and writing `res` are both
  -- deterministic, and neither touches the global state the postcondition looks at.
  have key : ∀ σ : ProcedureState (typeListToTuple (sig.ret :: sig.params)),
      (programDenotation (Stmt.call sig.resL p sig.argsL)).wp
          (Set.indicator {r | ¬ B (sig.resL.get r.2) r.2.global} fun _ => 1) σ
        = (procedureDenotation p (sig.argsL.get σ)).wp
            (Set.indicator {r | ¬ B r.1 r.2} fun _ => 1) σ.global := by
    intro σ
    simp only [Stmt.call, StmtWithHoles.call, programDenotation, procedureWithHoles_eta,
      wp_bind, wp_get_g, wp_zoom, wp_set_g, AsGetter.toG, AsSetter.toS, id_eq]
    congr 1
    funext as'
    -- the failure events correspond: `res` reads back `as'.1`, and writing it leaves the global
    -- state at `as'.2`
    have hmem : (((), sig.resL.set as'.1 (ProcedureState.globalL.set as'.2 σ))
          ∈ {r | ¬ B (sig.resL.get r.2) r.2.global}) ↔ as' ∈ {r | ¬ B r.1 r.2} := by
      simp only [Set.mem_setOf_eq, Lens.set_get,
        ProcedureSignature.global_resL_set, ProcedureState.globalL]
    by_cases h : as' ∈ {r : sig.ret × State | ¬ B r.1 r.2}
    · rw [Set.indicator_of_mem (hmem.mpr h), Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (fun hc => h (hmem.mp hc)), Set.indicator_of_notMem h]
  constructor
  · intro h σ hA
    rw [key]
    exact h _ _ hA
  · intro h args st hA
    -- the caller state witnessing `(args, st)`: the result slot can be filled with the value the
    -- procedure itself would return, so no `Inhabited sig.ret` is needed
    have hget := h ⟨st, typeListToTuple.cons _ _
      (p.return_val.get ⟨st, sig.localVariableInit p.locals args⟩) args⟩ (by simpa using hA)
    rw [key] at hget
    simpa using hget

end GaudisCrypt
