import GaudisCrypt.Logic.EagerAbstract
import GaudisCrypt.Logic.Granular
import GaudisCrypt.Logic.ConcreteFootprint

/-!
# From relational statements to the eager judgment

`ProgramDenotation.eagerR S S (=) p q (=)` (`Logic/EagerRhl.lean`) is a judgment about two
composite programs on the globals, `S; p` and `q; S`.  EasyCrypt proves its `eager` lemmas by the
relational tactics on those composites.  This file lets the `equiv_*` tactics do the same.

* `ProgramDenotation.preserves_compl_of_inFootprint`: a run confined to a lens `X` keeps
  everything outside `X` (`X.compl`).
* `ProgramDenotation.eagerR_of_prhl2_lens`: **the frame**.  When `S`, `p` and `q` are confined to
  `X`, a coupling of the composites with equal results and equal `X` is the full equality-invariant
  eager judgment.  EasyCrypt's `eager` lemmas about an oracle state `X` (`={x, FRO.m} ==>
  ={res, FRO.m}`) are proven at this postcondition.
* `prhl2_composite_of_prhlStmt`: the composites are the runs of the statements
  `_ <- R(); r <- p(a)` and `r <- q(a); _ <- R()`, so a `prhlStmt` between those statements
  gives the coupling.
* `eagerR_of_prhlStmt`: the two together.
-/

namespace GaudisCrypt

open GaudisCrypt.Lib.RO.Instantiate

variable {Ω : Type} (X : Lens Ω VariableAssignment)

/-- A run confined to `X` keeps the content outside `X`. -/
theorem ProgramDenotation.preserves_compl_of_inFootprint {α : Type}
    {p : ProgramDenotation VariableAssignment α} (hp : p.inFootprint X.footprint)
    (σ : VariableAssignment) :
    (p σ).satisfies (fun xs => X.compl.get xs.2 = X.compl.get σ) := by
  have h := ProgramDenotation.preserves_touched_of_fromLens hp (Lens.footprint_fromLens X.compl)
    (by rw [← Lens.compl_footprint]) σ
  exact fun xs hxs => (Lens.footprint_touched_getter_eq_iff X.compl _ _).mp (h xs hxs)

/-- Two states that agree on `X` and outside it are equal. -/
theorem Lens.eq_of_get_compl_get {x y : VariableAssignment} (h₁ : X.get x = X.get y)
    (h₂ : X.compl.get x = X.compl.get y) : x = y :=
  X.splitSpace.injective (Prod.ext h₁ h₂)

/-- **The frame for the eager judgment**: with `S`, `p` and `q` confined to `X`, a coupling of
`S; p` and `q; S` with equal results and equal `X` gives the equality-invariant judgment. -/
theorem ProgramDenotation.eagerR_of_prhl2_lens {α : Type}
    {S : ProgramDenotation VariableAssignment Unit} {p q : ProgramDenotation VariableAssignment α}
    (hS : S.inFootprint X.footprint) (hp : p.inFootprint X.footprint)
    (hq : q.inFootprint X.footprint)
    (h : ProgramDenotation.prhl2 (fun σ₁ σ₂ => σ₁ = σ₂) (S >>= fun _ => p)
      (q >>= fun a => S >>= fun _ => pure a) (fun u v => u.1 = v.1 ∧ X.get u.2 = X.get v.2)) :
    ProgramDenotation.eagerR S S (fun σ₁ σ₂ => σ₁ = σ₂) p q (fun u v => u = v) := by
  have h₁ : (S >>= fun _ => p).inFootprint X.footprint :=
    ProgramDenotation.inFootprint_bind hS fun _ => hp
  have h₂ : (q >>= fun a => S >>= fun _ => pure a).inFootprint X.footprint :=
    ProgramDenotation.inFootprint_bind hq fun a =>
      ProgramDenotation.inFootprint_bind hS fun _ => ProgramDenotation.inFootprint_pure _ _
  intro σ₁ σ₂ hσ
  subst hσ
  obtain ⟨μ, hm1, hm2, hsat⟩ := h σ₁ σ₁ rfl
  have hμ₁ : μ.satisfies (fun w => X.compl.get w.1.2 = X.compl.get σ₁) :=
    coupling_satisfies_fst (by
      rw [hm1]; exact ProgramDenotation.preserves_compl_of_inFootprint X h₁ σ₁)
  have hμ₂ : μ.satisfies (fun w => X.compl.get w.2.2 = X.compl.get σ₁) :=
    coupling_satisfies_snd (by
      rw [hm2]; exact ProgramDenotation.preserves_compl_of_inFootprint X h₂ σ₁)
  refine ⟨μ, hm1, hm2, fun w hw => ?_⟩
  obtain ⟨hr, hX⟩ := hsat w hw
  exact Prod.ext hr (Lens.eq_of_get_compl_get X hX ((hμ₁ w hw).trans (hμ₂ w hw).symm))

/-- **A run confined to `X` from two states equal on `X`** (EC's `sim` on code touching only
`X`): the two runs couple with equal results and equal `X`.  The second state is the first with
its outside replaced, a deterministic update outside `X`, which the run commutes with. -/
theorem ProgramDenotation.prhl2_refl_of_inFootprint {α : Type}
    {p : ProgramDenotation VariableAssignment α} (hp : p.inFootprint X.footprint) :
    ProgramDenotation.prhl2 (fun g₁ g₂ => X.get g₁ = X.get g₂) p p
      (fun u v => u.1 = v.1 ∧ X.get u.2 = X.get v.2) := by
  intro g₁ g₂ hX
  let u : VariableAssignment → VariableAssignment := fun g => X.compl.set (X.compl.get g₂) g
  have hu : u g₁ = g₂ := by
    refine Lens.eq_of_get_compl_get X ?_ ?_
    · haveI : Lens.Disjoint X.compl X := ⟨fun st v w => by
        induction v using Quotient.inductionOn
        rename_i z
        change X.set (X.get (X.set w st)) z = X.set w (X.set (X.get st) z)
        rw [X.set_get, X.set_set]⟩
      rw [Lens.get_of_disjoint_set]; exact hX
    · exact X.compl.set_get _ _
  have hmem : diracKer u ∈ (X.footprint)ᶜ.updates := by
    rw [Lens.compl_footprint]
    exact X.compl.diracKer_liftFunction_mem_footprint (fun _ => X.compl.get g₂)
  have hp₂ : p g₂ = p g₁ >>= fun xs => pure (xs.1, u xs.2) := by
    rw [← hu]; exact inFootprint_subprob hp hmem g₁
  refine ⟨p g₁ >>= fun xs => pure (xs, (xs.1, u xs.2)), ?_, ?_, ?_⟩
  · rw [SubProbability.bind_assoc]
    simp only [SubProbability.pure_bind]
    exact SubProbability.bind_pure _
  · rw [hp₂, SubProbability.bind_assoc]
    simp only [SubProbability.pure_bind]
  · refine SubProbability.satisfies_bind _ fun xs _ => SubProbability.satisfies_pure _ _ ⟨rfl, ?_⟩
    haveI : Lens.Disjoint X.compl X := ⟨fun st v w => by
      induction v using Quotient.inductionOn
      rename_i z
      change X.set (X.get (X.set w st)) z = X.set w (X.set (X.get st) z)
      rw [X.set_get, X.set_set]⟩
    exact (Lens.get_of_disjoint_set X X.compl (X.compl.get g₂) xs.2).symm

/-- `ProgramDenotation.prhl2_refl_of_inFootprint` for a procedure: EC's `sim` on an oracle
procedure whose code touches only `X`, from `={arg, X}` to `={res, X}`. -/
theorem prhlProc_refl_of_inFootprint {sig : ProcedureSignature} (p : Procedure sig)
    (hp : ∀ a, (procedureDenotation p a).inFootprint X.footprint) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ X.get g₁ = X.get g₂) p p
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ X.get g₁ = X.get g₂) := by
  intro a₁ a₂ g₁ g₂ ⟨ha, hX⟩
  subst ha
  exact ProgramDenotation.prhl2_refl_of_inFootprint X (hp a₁) g₁ g₂ hX

/-- `prhlProc_refl_of_inFootprint` for a procedure within `X` (`within_lens`). -/
theorem prhlProc_refl_of_within {sig : ProcedureSignature} (p : Procedure sig)
    (hb : p.body.Within X) (hr : p.return_val.Within X) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ X.get g₁ = X.get g₂) p p
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ X.get g₁ = X.get g₂) :=
  prhlProc_refl_of_inFootprint X p fun a => procedureDenotation_inFootprint_of_within p hb hr a

/-- A run on the left only, against a value on the right: lossless, and the postcondition on all
its outcomes (`ProgramDenotation.prhl2.kill_left` for any result types). -/
theorem ProgramDenotation.prhl2_lossless_left {α β : Type}
    {A : VariableAssignment → VariableAssignment → Prop}
    {p : ProgramDenotation VariableAssignment α} (b : β)
    {B : α × VariableAssignment → β × VariableAssignment → Prop}
    (hloss : ∀ σ, (p σ).expected (fun _ => 1) = 1)
    (h : ∀ σ₁ σ₂, A σ₁ σ₂ → (p σ₁).satisfies fun u => B u (b, σ₂)) :
    ProgramDenotation.prhl2 A p (pure b) B := by
  intro σ₁ σ₂ hA
  refine ⟨(p σ₁) >>= fun u => pure (u, (b, σ₂)), ?_, ?_, ?_⟩
  · rw [SubProbability.bind_assoc]
    simp only [SubProbability.pure_bind]
    exact SubProbability.bind_pure _
  · refine SubProbability.ext_of_expected (fun F => ?_)
    rw [SubProbability.expected_map, SubProbability.expected_bind]
    simp only [expected_pure]
    show (p σ₁).expected (fun _ => F (b, σ₂)) = (pure (b, σ₂) : SubProbability _).expected F
    rw [expected_pure]
    have h1 := hloss σ₁
    unfold SubProbability.expected at h1 ⊢
    rw [MeasureTheory.lintegral_one] at h1
    rw [MeasureTheory.lintegral_const, h1, mul_one]
  · exact SubProbability.satisfies_bind _ fun u hu =>
      SubProbability.satisfies_pure _ _ (h σ₁ σ₂ hA u hu)

/-! ## The composites as statements -/

/-- `programDenotation_call_apply`, for `StmtWithHoles.call` (the form the program syntax and the
inliner use). -/
theorem programDenotation_hcall_apply {sig : ProcedureSignature} (x : Setter sig.ret ProgramState)
    (p : Procedure sig) (args : Getter sig.ParamType ProgramState) (σ : ProgramState) :
    programDenotation (StmtWithHoles.call (h := .empty) x p args) σ
      = (procedureDenotation p (args.get σ) σ.globals).hbind fun r =>
          pure ((), x.set r.1 (ProgramState.globalL.set r.2 σ)) :=
  programDenotation_call_apply x p args σ

section Composite

variable {sig : ProcedureSignature} (R : Procedure ⟨[], Unit⟩) (p q : Procedure sig)
  (a : sig.ParamType) (y : Lens sig.ret ProgramState)

/-- `_ <- R(); y <- p(a)`: the eager side's composite, as a statement. -/
def eagerLeftStmt : Stmt :=
  StmtWithHoles.seq (StmtWithHoles.call Setter.throwaway R ⟨fun _ => ()⟩)
    (StmtWithHoles.call y.toSetter p ⟨fun _ => a⟩)

/-- `y <- q(a); _ <- R()`: the lazy side's composite, as a statement. -/
def eagerRightStmt : Stmt :=
  StmtWithHoles.seq (StmtWithHoles.call y.toSetter q ⟨fun _ => a⟩)
    (StmtWithHoles.call Setter.throwaway R ⟨fun _ => ()⟩)

variable {y} (hy : ∀ v σ, (y.set v σ).globals = σ.globals)
include hy

theorem eagerLeftStmt_denotation (g loc : VariableAssignment) :
    (procedureDenotation R () >>= fun _ => procedureDenotation p a) g =
      (programDenotation (eagerLeftStmt R p a y) ⟨g, loc⟩).hbind fun u =>
        pure (y.get u.2, u.2.globals) := by
  refine SubProbability.ext_of_expected fun F => ?_
  simp only [eagerLeftStmt, ProgramDenotation.bind_apply, programDenotation_seq,
    programDenotation_hcall_apply, SubProbability.expected_bind, SubProbability.expected_hbind,
    expected_pure]
  congr 1; funext r
  congr 1; funext r'
  simp only [Setter.throwaway, y.set_get, hy]
  rfl

theorem eagerRightStmt_denotation
    (hyg : ∀ g σ, y.get (ProgramState.globalL.set g σ) = y.get σ) (g loc : VariableAssignment) :
    (procedureDenotation q a >>= fun r => procedureDenotation R () >>= fun _ => pure r) g =
      (programDenotation (eagerRightStmt R q a y) ⟨g, loc⟩).hbind fun u =>
        pure (y.get u.2, u.2.globals) := by
  refine SubProbability.ext_of_expected fun F => ?_
  simp only [eagerRightStmt, ProgramDenotation.bind_apply, programDenotation_seq,
    programDenotation_hcall_apply, SubProbability.expected_bind, SubProbability.expected_hbind,
    expected_pure, ProgramDenotation.pure_apply]
  congr 1; funext r
  rw [hy]
  congr 1; funext r'
  simp only [Setter.throwaway, hyg, y.set_get]
  rfl

/-- **From statements to the eager judgment**: a `prhlStmt` between `_ <- R(); y <- p(a)` and
`y <- q(a); _ <- R()`, from equal `X` to equal `y` and equal `X`, is the equality-invariant
eager judgment, when `R`, `p` and `q` are confined to `X`.  EasyCrypt's `eager proc` on a concrete
pair of procedures, followed by its relational proof. -/
theorem eagerR_of_prhlStmt (hR : (procedureDenotation R ()).inFootprint X.footprint)
    (hp : (procedureDenotation p a).inFootprint X.footprint)
    (hq : (procedureDenotation q a).inFootprint X.footprint)
    (hyg : ∀ g σ, y.get (ProgramState.globalL.set g σ) = y.get σ)
    (h : prhlStmt (fun σ₁ σ₂ => X.get σ₁.globals = X.get σ₂.globals) (eagerLeftStmt R p a y)
      (eagerRightStmt R q a y)
      (fun σ₁ σ₂ => y.get σ₁ = y.get σ₂ ∧ X.get σ₁.globals = X.get σ₂.globals)) :
    ProgramDenotation.eagerR (procedureDenotation R ()) (procedureDenotation R ())
      (fun σ₁ σ₂ => σ₁ = σ₂) (procedureDenotation p a) (procedureDenotation q a)
      (fun u v => u = v) := by
  refine ProgramDenotation.eagerR_of_prhl2_lens X hR hp hq ?_
  intro σ₁ σ₂ hσ
  subst hσ
  obtain ⟨μ, hm1, hm2, hsat⟩ := h ⟨σ₁, VariableAssignment.init⟩ ⟨σ₁, VariableAssignment.init⟩ rfl
  let f : Unit × ProgramState → sig.ret × VariableAssignment := fun u => (y.get u.2, u.2.globals)
  refine ⟨μ >>= fun w => pure (f w.1, f w.2), ?_, ?_, ?_⟩
  · rw [eagerLeftStmt_denotation R p a hy σ₁ VariableAssignment.init, ← hm1,
      SubProbability.hbind_eq_bind, SubProbability.bind_assoc, SubProbability.bind_assoc]
    congr 1; funext w
    rw [SubProbability.pure_bind, SubProbability.pure_bind]
  · rw [eagerRightStmt_denotation R q a hy hyg σ₁ VariableAssignment.init, ← hm2,
      SubProbability.hbind_eq_bind, SubProbability.bind_assoc, SubProbability.bind_assoc]
    congr 1; funext w
    rw [SubProbability.pure_bind, SubProbability.pure_bind]
  · exact SubProbability.satisfies_bind _ fun w hw =>
      SubProbability.satisfies_pure _ _ (hsat w hw)

end Composite

end GaudisCrypt
