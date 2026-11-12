import GaudisCrypt.Logic.AbstractCall
import GaudisCrypt.Logic.AbstractCallUpto
import GaudisCrypt.Logic.Inline

/-!
# The syntactic frame: what a statement does not write, it keeps

EasyCrypt frames a call's invariant syntactically.  An oracle that writes none of `D`'s variables
keeps `glob D`, and the oracle premise of the abstract call rule then needs only the oracle's own
relation (`={arg} ∧ inv ==> ={res} ∧ inv`).  `prhlProc_globInvF_of_confined` does this from a
footprint (`inFootprint`), which a concrete procedure does not come with.

The syntactic route instead looks at every write of the statement, its callees' bodies included:
`StmtWithHoles.WritesKeep G s` says each of them keeps `G` of the globals.  A write to a local
variable keeps the globals outright.  A write to a global lens outside a region `F` keeps
`F.touched_getter` (`touched_set_of_le_compl`).  `hoareStmt_of_writesKeep` turns that into a Hoare
triple by induction over the statement.  `prhlProc_globInvF_of_writesKeep` puts it into the
oracle premise.

The tactic `writes_keep` reduces a `WritesKeep` goal to the conditions on single writes.  It
unfolds module procedures as the inliner does (`Flatten.unfoldProcedure`), closes the writes to
local variables by `rfl`, and the writes to global lenses outside the region by
`touched_set_of_le_compl` with a hypothesis from the context.
-/

namespace GaudisCrypt

/-- A procedure triple from a triple about its body, run on the initial locals. -/
theorem hoareProc_of_body {sig} {p : Procedure sig} {A : sig.ParamType → VariableAssignment → Prop}
    {B : sig.ret → VariableAssignment → Prop}
    (h : ∀ a, hoareStmt (fun σ => A a σ.globals ∧ σ.locals = p.initLocals a) p.body
      (fun σ => B (p.return_val.get σ) σ.globals)) : hoareProc A p B := by
  rw [hoareProc_iff_wp]
  intro a σ hA
  have := hoareStmt_iff_wp.mp (h a) ⟨σ, p.initLocals a⟩ ⟨hA, rfl⟩
  simp only [ProgramDenotation.wp, procedureDenotation, SubProbability.expected_hbind,
    expected_pure] at this ⊢
  convert this using 2
  funext u
  simp [Set.indicator]

/-- Every write of the statement, its callees' included, keeps `G` of the globals. -/
def StmtWithHoles.WritesKeep {β : Type*} (G : VariableAssignment → β) {h : HoleSigs} :
    StmtWithHoles h → Prop
  | .skip => True
  | .sample x _ => ∀ v σ, G (x.set v σ).globals = G σ.globals
  | .call' x _ _ _ body _ _ => (∀ v σ, G (x.set v σ).globals = G σ.globals) ∧ body.WritesKeep G
  | .hole _ _ _ => False
  | .seq s t => s.WritesKeep G ∧ t.WritesKeep G
  | .ifThenElse _ t e => t.WritesKeep G ∧ e.WritesKeep G
  | .while _ t => t.WritesKeep G

/-- **The syntactic frame**: a statement whose writes keep `G` keeps it. -/
theorem hoareStmt_of_writesKeep {β : Type*} (G : VariableAssignment → β) (c : β) :
    ∀ s : Stmt, StmtWithHoles.WritesKeep G s →
      hoareStmt (fun σ => G σ.globals = c) s (fun σ => G σ.globals = c)
  | .skip, _ => hoare_skip_of_imp fun _ h => h
  | .sample x _, hs => hoare_pre (hoare_sample_wp x _) fun σ hσ a _ => (hs a σ).trans hσ
  | .call' x ns hl hn body r p, hs => by
      obtain ⟨hx, hb⟩ := (show _ ∧ _ from hs)
      have hp : hoareProc (fun _ g => G g = c) ⟨ns, hl, hn, body, r⟩ (fun _ g => G g = c) :=
        hoareProc_of_body fun a => hoare_pre (hoareStmt_of_writesKeep G c body hb)
          fun σ hσ => hσ.1
      exact hoare_pre (hoare_call_wp x ⟨ns, hl, hn, body, r⟩ p hp _)
        fun σ hσ => ⟨hσ, fun v g hg => (hx v _).trans hg⟩
  | .seq s t, hst =>
      have hs := (show _ ∧ _ from hst).1
      have ht := (show _ ∧ _ from hst).2
      hoare_seq (hoareStmt_of_writesKeep G c t ht) (hoareStmt_of_writesKeep G c s hs)
  | .ifThenElse _ t e, hte =>
      have ht := (show _ ∧ _ from hte).1
      have he := (show _ ∧ _ from hte).2
      hoare_pre (hoare_if_wp (hoareStmt_of_writesKeep G c t ht) (hoareStmt_of_writesKeep G c e he))
        fun _ hσ => ⟨fun _ => hσ, fun _ => hσ⟩
  | .while _ t, ht =>
      hoare_while _ (hoare_pre (hoareStmt_of_writesKeep G c t ht) fun _ hσ => hσ.1)
        fun _ hσ _ => hσ
termination_by s => s.depth
decreasing_by all_goals simp [StmtWithHoles.depth]; try omega

/-- A procedure whose writes keep `G` keeps it. -/
theorem hoareProc_of_writesKeep {sig} {β : Type*} (G : VariableAssignment → β) (p : Procedure sig)
    (hp : StmtWithHoles.WritesKeep G p.body) (c : β) :
    hoareProc (fun _ g => G g = c) p (fun _ g => G g = c) :=
  hoareProc_of_body fun _ => hoare_pre (hoareStmt_of_writesKeep G c _ hp) fun _ hσ => hσ.1

/-- `hoareProc_of_writesKeep`, as the runs of the procedure. -/
theorem Procedure.satisfies_of_writesKeep {sig} {β : Type*} (G : VariableAssignment → β)
    (p : Procedure sig) (hp : StmtWithHoles.WritesKeep G p.body) (a : sig.ParamType)
    (g : VariableAssignment) :
    (procedureDenotation p a g).satisfies fun r => G r.2 = G g := by
  intro u hu
  by_contra hB
  have h0 := SubProbability.ofEvent_eq_zero_of_subset (Set.singleton_subset_iff.mpr hB)
    (hoareProc_of_writesKeep G p hp (G g) a g rfl)
  have hfin : (procedureDenotation p a g).1 {u} ≠ ⊤ :=
    (((MeasureTheory.measure_mono (Set.subset_univ _)).trans
      (procedureDenotation p a g).2.1).trans_lt ENNReal.one_lt_top).ne
  rw [SubProbability.ofEvent, ENNReal.toNNReal_eq_zero_iff] at h0
  exact hu (h0.resolve_right hfin)

open GaudisCrypt.Lib.RO.Instantiate

variable {Ω : Type} (L : Lens Ω VariableAssignment)

/-- **EasyCrypt's oracle premise, by the syntactic frame**: `prhlProc_globInvF_of_confined` for
oracles whose writes keep the content of `F`. -/
theorem prhlProc_globInvF_of_writesKeep {F : Footprint VariableAssignment}
    {sig' : ProcedureSignature} {I : Ω → Ω → Prop} {o₁ o₂ : Procedure sig'}
    (h₁ : StmtWithHoles.WritesKeep F.touched_getter.get o₁.body)
    (h₂ : StmtWithHoles.WritesKeep F.touched_getter.get o₂.body)
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ I (L.get g₁) (L.get g₂)) o₁ o₂
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ I (L.get g₁) (L.get g₂))) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L F I g₁ g₂) o₁ o₂
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L F I g₁ g₂) := by
  intro a₁ a₂ g₁ g₂ ⟨ha, hglob, hI⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := h a₁ a₂ g₁ g₂ ⟨ha, hI⟩
  have hμ₁ : μ.satisfies (fun w => F.touched_getter.get w.1.2 = F.touched_getter.get g₁) :=
    coupling_satisfies_fst (by rw [hm1]; exact Procedure.satisfies_of_writesKeep _ o₁ h₁ a₁ g₁)
  have hμ₂ : μ.satisfies (fun w => F.touched_getter.get w.2.2 = F.touched_getter.get g₂) :=
    coupling_satisfies_snd (by rw [hm2]; exact Procedure.satisfies_of_writesKeep _ o₂ h₂ a₂ g₂)
  refine ⟨μ, hm1, hm2, fun w hw => ?_⟩
  obtain ⟨hr, hI'⟩ := hsat w hw
  exact ⟨hr, by rw [hμ₁ w hw, hμ₂ w hw]; exact hglob, hI'⟩

/-- **EasyCrypt's oracle premise up to `bad`, by the syntactic frame**: the oracle premise of
`prhlProc_abstract_call_upto(_module)` at `F`, for oracles whose writes keep the content of `F`, from
a judgment about the `L`-contents (EC's `call (: bad, invP, invQ)` on concrete oracles, `={glob D}`
framed syntactically). -/
theorem prhlProc_upto_of_writesKeep {F : Footprint VariableAssignment}
    {sig' : ProcedureSignature} {I Q : Ω → Ω → Prop} {bad : Ω → Prop} {o₁ o₂ : Procedure sig'}
    (h₁ : StmtWithHoles.WritesKeep F.touched_getter.get o₁.body)
    (h₂ : StmtWithHoles.WritesKeep F.touched_getter.get o₂.body)
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ I (L.get g₁) (L.get g₂) ∧ ¬ bad (L.get g₂)) o₁ o₂
      (fun r₁ g₁ r₂ g₂ => (bad (L.get g₂) ∧ Q (L.get g₁) (L.get g₂)) ∨
        (r₁ = r₂ ∧ I (L.get g₁) (L.get g₂) ∧ ¬ bad (L.get g₂)))) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ syncInv L F I bad g₁ g₂) o₁ o₂
      (fun r₁ g₁ r₂ g₂ => badInv L bad Q g₁ g₂ ∨ (r₁ = r₂ ∧ syncInv L F I bad g₁ g₂)) := by
  intro a₁ a₂ g₁ g₂ ⟨ha, hglob, hI⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := h a₁ a₂ g₁ g₂ ⟨ha, hI⟩
  have hμ₁ : μ.satisfies (fun w => F.touched_getter.get w.1.2 = F.touched_getter.get g₁) :=
    coupling_satisfies_fst (by rw [hm1]; exact Procedure.satisfies_of_writesKeep _ o₁ h₁ a₁ g₁)
  have hμ₂ : μ.satisfies (fun w => F.touched_getter.get w.2.2 = F.touched_getter.get g₂) :=
    coupling_satisfies_snd (by rw [hm2]; exact Procedure.satisfies_of_writesKeep _ o₂ h₂ a₂ g₂)
  refine ⟨μ, hm1, hm2, fun w hw => ?_⟩
  rcases hsat w hw with hb | ⟨hr, hI'⟩
  · exact Or.inl hb
  · exact Or.inr ⟨hr, by rw [hμ₁ w hw, hμ₂ w hw]; exact hglob, hI'⟩

open Lean Meta Elab Tactic in
/-- Split a goal `head … s` (a predicate on statements defined by recursion on them, such as
`StmtWithHoles.WritesKeep`) down to its leaves, unfolding the procedures of modules
(`Flatten.unfoldProcedure`) where the statement is a callee's body. -/
partial def stmtPredSplit (head : Name) (g : MVarId) (fuel : Nat := 256)
    (onStuck? : Option (MVarId → MetaM MVarId) := none) :
    MetaM (List MVarId) := do
  if fuel == 0 then return [g]
  let ty ← whnf (← instantiateMVars (← g.getType))
  if ty.isAppOfArity ``And 2 then
    let gs ← g.apply (mkConst ``And.intro [])
    return (← gs.mapM (stmtPredSplit head · (fuel - 1) onStuck?)).flatten
  else if ty.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return []
  else if ty.isAppOf head then
    let some p := ty.find? (·.isAppOf ``Module.Proc.procedure)
      | throwError "stuck at{indentExpr ty}"
    -- a callee the plain unfolding cannot open (a view, `PRIMITIVE.f (Module.pair' …)`): with
    -- the views read off (`ECProc.accessorNorm`'s steps; the goal shows no code to the user)
    let r ← try Flatten.unfoldProcedure p
      catch _ => Flatten.unfoldProcedure p (views := true)
    let g ← g.replaceTargetDefEq ty
    let g ← match r.proof? with
      | none => g.replaceTargetDefEq (ty.replace fun e => if e == p then some r.expr else none)
      | some h => do
        let res ← g.rewrite ty h
        g.replaceTargetEq res.eNew res.eqProof
    stmtPredSplit head g (fuel - 1) onStuck?
  else
    return [← g.replaceTargetDefEq ty]

open Lean Meta in
/-- `stmtPredSplit` for `StmtWithHoles.WritesKeep`. -/
def writesKeepSplit (g : MVarId) (onStuck? : Option (MVarId → MetaM MVarId) := none) :
    MetaM (List MVarId) :=
  stmtPredSplit ``StmtWithHoles.WritesKeep g (onStuck? := onStuck?)

open Lean Elab Tactic in
/-- `writes_keep`: on a goal `StmtWithHoles.WritesKeep G s`, the conditions on the single writes
of `s`, callees included.  Writes to local variables are closed by `rfl`, writes to a global lens
`X` by `touched_set_of_le_compl` with a hypothesis `X.footprint ≤ Fᶜ` from the context. -/
elab "writes_keep" : tactic => do
  liftMetaTactic (writesKeepSplit ·)
  evalTactic (← `(tactic| all_goals first
    | exact fun _ _ => rfl
    | exact fun v σ => touched_set_of_le_compl (by assumption) v σ.globals
    | skip))

end GaudisCrypt
