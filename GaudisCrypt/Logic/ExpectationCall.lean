import GaudisCrypt.Logic.AbstractCall
import GaudisCrypt.Logic.PHoare

/-!
# The abstract call rule for expectations (supermartingales)

An adversary that cannot touch an oracle's state `L`, run with oracles that do not increase the
expectation of a potential `φ` of that state, does not increase it either.  This is the unary,
quantitative counterpart of the relational abstract call rule (`Logic/AbstractCall.lean`), and
what EasyCrypt's failure event lemma (`fel`) rests on: with `φ` the indicator of the bad event plus
the bound still to be paid for the remaining oracle calls, `Pr[bad] ≤ φ(initial state)`.

The proof is an induction over the adversary's statement (`ConfinedP`, from its footprint): code
without holes keeps the content of `L` (`inFootprint_preserves_touched`, `L` lifted is a lens
region), an oracle call is the hypothesis, sequences compose by monotonicity, and loops are
`Stmt.ewp_while_le` with `φ` as the invariant.
-/

namespace GaudisCrypt

open GaudisCrypt.Lib.RO.Instantiate

variable {Ω : Type} (L : Lens Ω VariableAssignment)

/-- A point mass charges its point. -/
theorem SubProbability.pure_singleton_ne_zero {α : Type*} (a : α) :
    (pure a : SubProbability α).1 {a} ≠ 0 := by
  letI : MeasurableSpace α := ⊤
  change (MeasureTheory.Measure.dirac a) {a} ≠ 0
  simp

/-- A program confined outside `L` (lifted through the globals) keeps `L`'s value. -/
theorem ProgramDenotation.satisfies_frame_globals {α : Type}
    {p : ProgramDenotation ProgramState α}
    (hp : p.inFootprint ((ProgramState.globalL.chain L).footprint)ᶜ) (σ : ProgramState) :
    (p σ).satisfies fun r => L.get r.2.globals = L.get σ.globals := fun r hr =>
  (Lens.footprint_touched_getter_eq_iff (ProgramState.globalL.chain L) _ _).mp
    (inFootprint_preserves_touched hp (le_of_eq (Footprint.compl_compl _).symm)
      (Lens.footprint_hasReset _ σ) r hr)

/-- A statement confined outside `L` does not increase the expectation of a function of `L`. -/
theorem Stmt.ewp_le_of_confined {s : Stmt} (φ : Ω → ENNReal)
    (hs : (programDenotation s).inFootprint ((ProgramState.globalL.chain L).footprint)ᶜ)
    (σ : ProgramState) :
    s.ewp (fun τ => φ (L.get τ.globals)) σ ≤ φ (L.get σ.globals) := by
  have h := ProgramDenotation.satisfies_frame_globals L hs σ
  have heq : s.ewp (fun τ => φ (L.get τ.globals)) σ = s.ewp (fun _ => φ (L.get σ.globals)) σ := by
    simp only [Stmt.ewp, ProgramDenotation.wp]
    exact SubProbability.expected_congr_satisfies h fun r hr => by rw [hr]
  rw [heq]
  exact Stmt.ewp_const_le s _ σ

/-- **The body induction**: an adversary statement confined outside `L`, its holes filled with
oracles that do not increase `φ` in expectation, does not increase it. -/
theorem StmtWithHoles.ewp_instantiate_le {holes : HoleSigs} (inst : holes.Instantiation)
    (φ : Ω → ENNReal)
    (hhole : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (a : sig'.ParamType)
      (g : VariableAssignment),
      (inst.lookup n).ewp a (fun _ g' => φ (L.get g')) g ≤ φ (L.get g)) :
    ∀ (s : StmtWithHoles holes), ConfinedP ((ProgramState.globalL.chain L).footprint)ᶜ s →
      ∀ σ, (s.instantiate inst).ewp (fun τ => φ (L.get τ.globals)) σ ≤ φ (L.get σ.globals)
  | .skip, _, σ => by
      show Stmt.ewp StmtWithHoles.skip _ σ ≤ _
      rw [Stmt.ewp_skip]
  | .sample x e, h, σ => Stmt.ewp_le_of_confined L φ h σ
  | .call' x ns hl hn b r p, h, σ => Stmt.ewp_le_of_confined L φ h σ
  | .hole n x p, h, σ => by
      obtain ⟨-, hx⟩ := (show _ ∧ _ from h)
      show Stmt.ewp (Stmt.call x (inst.lookup n) p) _ σ ≤ _
      rw [Stmt.ewp_call]
      refine le_of_eq_of_le ?_ (hhole n (p.get σ) σ.globals)
      simp only [Procedure.ewp, ProgramDenotation.wp]
      congr 1
      funext r
      have hset := ProgramDenotation.satisfies_frame_globals L (hx r.1)
        (ProgramState.globalL.set r.2 σ) ((), x.set r.1 (ProgramState.globalL.set r.2 σ))
        (SubProbability.pure_singleton_ne_zero _)
      simp only at hset
      rw [hset]
      rfl
  | .seq s t, h, σ => by
      obtain ⟨hs, ht⟩ := (show _ ∧ _ from h)
      show Stmt.ewp (StmtWithHoles.seq (s.instantiate inst) (t.instantiate inst)) _ σ ≤ _
      rw [Stmt.ewp_seq]
      exact (Stmt.ewp_mono _ (fun τ => StmtWithHoles.ewp_instantiate_le inst φ hhole t ht τ)
        σ).trans (StmtWithHoles.ewp_instantiate_le inst φ hhole s hs σ)
  | .ifThenElse c t e, h, σ => by
      obtain ⟨-, ht, he⟩ := (show _ ∧ _ ∧ _ from h)
      show Stmt.ewp (StmtWithHoles.ifThenElse c (t.instantiate inst) (e.instantiate inst)) _ σ ≤ _
      rw [Stmt.ewp_ifThenElse]
      dsimp only
      split
      · exact StmtWithHoles.ewp_instantiate_le inst φ hhole t ht σ
      · exact StmtWithHoles.ewp_instantiate_le inst φ hhole e he σ
  | .while c t, h, σ => by
      obtain ⟨-, ht⟩ := (show _ ∧ _ from h)
      show Stmt.ewp (StmtWithHoles.while c (t.instantiate inst)) _ σ ≤ _
      exact Stmt.ewp_while_le _ _
        (fun τ _ => StmtWithHoles.ewp_instantiate_le inst φ hhole t ht τ) (fun _ _ => le_rfl) σ

/-- **The abstract call rule for expectations** (a procedure with holes): an adversary that cannot
touch `L` (`FVP.fvP_proc A ≤ L.footprintᶜ`), its holes filled with oracles that do not increase the
expectation of `φ ∘ L`, does not increase it. -/
theorem ProcedureWithHoles.ewp_instantiate_le {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) (hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (inst : holes.Instantiation) (φ : Ω → ENNReal)
    (hhole : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (a : sig'.ParamType)
      (g : VariableAssignment),
      (inst.lookup n).ewp a (fun _ g' => φ (L.get g')) g ≤ φ (L.get g))
    (a : sig.ParamType) (g : VariableAssignment) :
    (A.instantiate inst).ewp a (fun _ g' => φ (L.get g')) g ≤ φ (L.get g) := by
  have hconf := confinedP_of_fv _ hc A.body
    ((fvP_stmt_body_le_fvP_proc A).trans (fvP_proc_le_chain_compl L A hdisj))
  have h := StmtWithHoles.ewp_instantiate_le L inst φ hhole A.body hconf
    ⟨g, (A.instantiate inst).initLocals a⟩
  simp only [Procedure.ewp, ProgramDenotation.wp, procedureDenotation,
    SubProbability.expected_hbind, expected_pure]
  exact h

/-- **The abstract call rule for expectations, for a module** (EasyCrypt's `declare module D <: T
{-O}`): `D` applied to oracles that do not increase the expectation of `φ ∘ L`, `L` outside `D`,
does not increase it (exception E2 for the representation). -/
theorem Module.ewp_app_le {T : Type 1} [IsModule T] {sig : ProcedureSignature}
    {holes : HoleSigs} (D : Module.Arr T (Module.Proc sig)) (ext : T → holes.Instantiation)
    (hD : Module.Representable D ext) (hdisj : FVP.fvP D ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (O : T) (φ : Ω → ENNReal)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (a : sig'.ParamType)
      (g : VariableAssignment),
      ((ext O).lookup n).ewp a (fun _ g' => φ (L.get g')) g ≤ φ (L.get g))
    (a : sig.ParamType) (g : VariableAssignment) :
    (Module.app D O).procedure.ewp a (fun _ g' => φ (L.get g')) g ≤ φ (L.get g) := by
  obtain ⟨p, hden, hle⟩ := hD
  have h := ProcedureWithHoles.ewp_instantiate_le L p (hle.trans hdisj) hc (ext O) φ horacle a g
  simp only [Procedure.ewp] at h ⊢
  rwa [hden O a]

end GaudisCrypt
