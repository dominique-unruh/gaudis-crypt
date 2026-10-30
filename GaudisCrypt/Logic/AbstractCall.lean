import GaudisCrypt.Lib.RO.GlobTransfer
import GaudisCrypt.Logic.PRHLStmt

/-!
# The abstract call rule (EasyCrypt's `call (: inv)` for an adversary with oracles)

An adversary `A` is a procedure with holes, and its holes are its oracles.  Run against two
instantiations of the oracles `inst₁`/`inst₂`, it couples with itself as EasyCrypt's abstract
call rule says:

```
  equiv[ inst₁.o ~ inst₂.o : ={arg} ∧ inv ==> ={res} ∧ inv ]   (for every oracle o)
  ─────────────────────────────────────────────────────────────────────────────────
  equiv[ A(inst₁) ~ A(inst₂) : ={arg} ∧ ={glob A} ∧ inv ==> ={res} ∧ ={glob A} ∧ inv ]
```

`glob A` is `FVP.glob A`, whatever `A` may touch.  The invariant `inv` reads only the oracles'
state: a lens `L` with `A` disjoint from it (`hdisj : FVP.fvP_proc A ≤ L.footprintᶜ`, EasyCrypt's
`A <: T {-O}`).  This is EasyCrypt's discipline too: an invariant mentioning `glob A` is rejected
there.  Globals outside `glob A` and `L` are unconstrained, as in EasyCrypt.

* `prhl2_instantiate_globInv`: the rule on denotations.  It is the oracle-agnostic machinery of
  `Lib/RO/ROCouplingEquiv.lean` (`instantiate_of_fvP_gen`).  It uses the adversary-side
  compatibility `footprintCompat_globInv`, which generalizes `footprintCompat_PGlob` from equal
  random-oracle tables to any `inv` on the `L`-content.  It also uses the hole coupling
  `hhole_of_prhl2`, from the per-oracle specifications.
* `prhlProc_abstract_call`: the rule as a `prhlProc` judgment.  Its oracle premises carry
  `={glob A}` along.
* `prhlProc_globInv_of_confined`: drops `={glob A}` from an oracle premise when the oracle is
  confined to `L`.  Its runs only rewrite the `L`-content, which `glob A` cannot see.  With it, the
  premises are EasyCrypt's: `={arg} ∧ inv ==> ={res} ∧ inv`.
-/

namespace GaudisCrypt

open GaudisCrypt.Lib.RO.Instantiate

variable {Ω : Type} (L : Lens Ω VariableAssignment)

/-- The abstract call invariant `={glob A} ∧ inv`, where `inv` reads the oracle region `L`. -/
def globInv {holes : HoleSigs} {sig : ProcedureSignature} (A : ProcedureWithHoles holes sig)
    (I : Ω → Ω → Prop) : VariableAssignment → VariableAssignment → Prop :=
  fun g₁ g₂ => (FVP.glob A).get g₁ = (FVP.glob A).get g₂ ∧ I (L.get g₁) (L.get g₂)

/-- An adversary disjoint from the global lens `L` is disjoint from it as a procedure (`L` lifted
through `globalL`).  This is `fvP_proc_le_roLift_compl` for an arbitrary lens. -/
theorem fvP_proc_le_chain_compl {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) (hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ) :
    fvP_proc A ≤ ((ProgramState.globalL.chain L).footprint)ᶜ := by
  rw [show FVP.fvP_proc A =
      Lens.reduceFootprint ProgramState.globalL (FVP.fvP_stmt A.body) ⊔
        Lens.reduceFootprint ProgramState.globalL ((ProgramDenotation.get A.return_val).footprint)
      from rfl] at hdisj
  change fvP_stmt A.body ⊔ (ProgramDenotation.get A.return_val).footprint
      ≤ ((ProgramState.globalL.chain L).footprint)ᶜ
  refine sup_le ?_ ?_
  · refine reduce_chain_le_compl
      (le_trans (Lens.reduceFootprint_mono _ (fvP_stmt_le_FVP A.body)) ?_)
    exact le_trans le_sup_left hdisj
  · exact reduce_chain_le_compl (le_trans le_sup_right hdisj)

/-- A write through a lens `X` that `A` cannot see leaves `glob A` unchanged. -/
theorem glob_set_of_le_compl {holes : HoleSigs} {sig : ProcedureSignature}
    {A : ProcedureWithHoles holes sig} {β : Type} {X : Lens β VariableAssignment}
    (h : X.footprint ≤ (FVP.fvP_proc A)ᶜ) (v : β) (g : VariableAssignment) :
    (FVP.glob A).get (X.set v g) = (FVP.glob A).get g :=
  Footprint.touched_getter_get_eq_of_mem (h (X.diracKer_liftFunction_mem_footprint
    (Function.const _ v))) g

/-- **The adversary's own steps preserve the call invariant.**  Every program confined to what
`A` may touch self-couples from `globInv`-related states.  This generalizes
`footprintCompat_PGlob` from equal random-oracle tables to any `inv` on the `L`-content.  It runs
the orbit self-coupling (`prhl2_self_of_orbit`) and re-attaches `inv` through the coupling's
marginals: neither side's run changes its `L`-content. -/
theorem footprintCompat_globInv {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) (hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ)
    (I : Ω → Ω → Prop) :
    FootprintCompat (globInv L A I) (fvP_proc A) := by
  intro γ p hp ps₁ ps₂ hpre
  obtain ⟨⟨hglob, hI⟩, hloc⟩ := hpre
  have horbG : Relation.EqvGen (fun a b : state => ∃ f : Function.End state,
      diracKer f ∈ ((FVP.fvP_proc A)ᶜ).updates ∧ f a = b) ps₁.globals ps₂.globals :=
    Quotient.exact hglob
  have horb : Relation.EqvGen (fun a b => ∃ fp ∈ liftedGlobSteps A, fp a = b) ps₁ ps₂ := by
    have h0 := lifted_orbit_of_global A ps₁.locals horbG
    have h1 : (⟨ps₂.globals, ps₁.locals⟩ : ProgramState) = ps₂ := by rw [hloc]
    exact h1 ▸ h0
  have hU : ∀ fp ∈ liftedGlobSteps A, diracKer fp ∈ ((fvP_proc A)ᶜ).updates := by
    rintro fp ⟨f, hf, rfl⟩
    exact lifted_step_mem_fvP_proc_compl A hf
  obtain ⟨μ, hm1, hm2, hsat⟩ := prhl2_self_of_orbit hp _ hU ps₁ ps₂ horb
  have hSle : (ProgramState.globalL.chain L).footprint ≤ (fvP_proc A)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (fvP_proc_le_chain_compl L A hdisj)
  have hLeg : ∀ ps : ProgramState,
      (p ps).satisfies (fun xs => L.get xs.2.globals = L.get ps.globals) := by
    intro ps xs hxs
    exact (Lens.footprint_touched_getter_eq_iff (ProgramState.globalL.chain L) _ _).mp
      (inFootprint_preserves_touched hp hSle (Lens.footprint_hasReset _ ps) xs hxs)
  have hμ₁ : μ.satisfies (fun w => L.get w.1.2.globals = L.get ps₁.globals) :=
    coupling_satisfies_fst (by rw [hm1]; exact hLeg ps₁)
  have hμ₂ : μ.satisfies (fun w => L.get w.2.2.globals = L.get ps₂.globals) :=
    coupling_satisfies_snd (by rw [hm2]; exact hLeg ps₂)
  refine ⟨μ, hm1, hm2, ?_⟩
  intro w hw
  obtain ⟨hres, horbw⟩ := hsat w hw
  have hgl := glob_locals_of_lifted_orbit A horbw
  refine ⟨hres, ⟨hgl.1, ?_⟩, hgl.2⟩
  rw [hμ₁ w hw, hμ₂ w hw]
  exact hI

/-- **The hole coupling from per-oracle specifications**: calls of the two instantiations of an
oracle couple under `liftRel P` when the oracle procedures do under `P`.  This generalizes
`ro_hhole_prhl` from the random oracle to any pair of instantiations. -/
theorem hhole_of_prhl2 {P : state → state → Prop} {holes : HoleSigs}
    (inst₁ inst₂ : holes.Instantiation)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (a : sig'.ParamType),
      ProgramDenotation.prhl2 P (procedureDenotation (inst₁.lookup n) a)
        (procedureDenotation (inst₂.lookup n) a) (liftPost P))
    {sig' : ProcedureSignature} (n : HoleIndex holes sig')
    (x : Setter sig'.ret ProgramState) (p : Getter sig'.ParamType ProgramState)
    (hp : GetOK P p)
    (hx : ∀ ret, ProgramDenotation.prhl2 (liftRel P) (ProgramDenotation.set x ret)
        (ProgramDenotation.set x ret) (liftRelPost P)) :
    ProgramDenotation.prhl2 (liftRel P)
      (programDenotation (StmtWithHoles.call x (inst₁.lookup n) p))
      (programDenotation (StmtWithHoles.call x (inst₂.lookup n) p)) (liftRelPost P) := by
  rw [denote_call, denote_call]
  refine ProgramDenotation.prhl2.bind hp (fun args₁ args₂ => ?_)
  intro σ₁ σ₂ hpre
  obtain ⟨rfl, hrel⟩ := hpre
  refine (ProgramDenotation.prhl2.bind (M := liftRelPost P) ?_ (fun ret₁ ret₂ => ?_)) σ₁ σ₂ hrel
  · exact ProgramDenotation.prhl2.conseq (prhl2_zoom (horacle n args₁))
      (fun _ _ h => h) (fun _ _ hB => ⟨hB.1.1, hB.1.2, hB.2⟩)
  · intro τ₁ τ₂ hpre2
    obtain ⟨rfl, hrel2⟩ := hpre2
    exact hx ret₁ τ₁ τ₂ hrel2

/-- **The abstract call rule, on denotations.**  The adversary `A`, disjoint from the oracle region
`L`, run against two instantiations whose oracles preserve `globInv L A I`, preserves it and
returns equal results. -/
theorem prhl2_instantiate_globInv {holes : HoleSigs} {sig : ProcedureSignature}
    (inst₁ inst₂ : holes.Instantiation) (A : ProcedureWithHoles holes sig) (args : sig.ParamType)
    (hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ) (I : Ω → Ω → Prop)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (a : sig'.ParamType),
      ProgramDenotation.prhl2 (globInv L A I) (procedureDenotation (inst₁.lookup n) a)
        (procedureDenotation (inst₂.lookup n) a) (liftPost (globInv L A I))) :
    ProgramDenotation.prhl2 (globInv L A I)
      (procedureDenotation (A.instantiate inst₁) args)
      (procedureDenotation (A.instantiate inst₂) args) (liftPost (globInv L A I)) :=
  instantiate_of_fvP_gen inst₁ inst₂ A args (footprintCompat_globInv L A hdisj I) hc
    (fun n x p hp hx => hhole_of_prhl2 inst₁ inst₂ horacle n x p hp hx)

/-- **The abstract call rule** (EasyCrypt's `call (: inv)` for an abstract adversary), as a
`prhlProc` judgment.  The oracle premises carry `={glob A}`; `prhlProc_globInv_of_confined`
removes it for oracles confined to `L`. -/
theorem prhlProc_abstract_call {holes : HoleSigs} {sig : ProcedureSignature}
    (inst₁ inst₂ : holes.Instantiation) (A : ProcedureWithHoles holes sig)
    (hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ) (I : Ω → Ω → Prop)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInv L A I g₁ g₂)
        (inst₁.lookup n) (inst₂.lookup n)
        (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInv L A I g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInv L A I g₁ g₂)
      (A.instantiate inst₁) (A.instantiate inst₂)
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInv L A I g₁ g₂) := by
  intro a₁ a₂ g₁ g₂ ⟨ha, hg⟩
  subst ha
  exact prhl2_instantiate_globInv L inst₁ inst₂ A a₁ hdisj I hc
    (fun n a σ₁ σ₂ h => horacle n a a σ₁ σ₂ ⟨rfl, h⟩) g₁ g₂ hg

/-- A run confined to the lens `L` only rewrites the `L`-content: every final state is
`L.set v σ` for some `v`. -/
theorem satisfies_lens_set_of_inFootprint {γ : Type} {p : ProgramDenotation VariableAssignment γ}
    (hp : p.inFootprint L.footprint) (σ : VariableAssignment) :
    (p σ).satisfies (fun xs => ∃ v, L.set v σ = xs.2) := by
  haveI : Lens.Disjoint L.compl L := ⟨fun st v w => by
    induction v using Quotient.inductionOn
    rename_i u
    change L.set (L.get (L.set w st)) u = L.set w (L.set (L.get st) u)
    rw [L.set_get, L.set_set]⟩
  intro xs hxs
  have h := (Lens.footprint_touched_getter_eq_iff _ _ _).mp
    (inFootprint_preserves_touched hp (Lens.footprint_le_compl_of_disjoint L.compl L)
      (Lens.footprint_hasReset L.compl σ) xs hxs)
  exact Quotient.exact h.symm

/-- **Oracles confined to `L` keep `glob A`.**  An `L`-confined run changes only the `L`-content,
which `A` (disjoint from `L`) cannot see. -/
theorem glob_eq_of_inFootprint {holes : HoleSigs} {sig : ProcedureSignature}
    {A : ProcedureWithHoles holes sig} (hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ)
    {γ : Type} {p : ProgramDenotation VariableAssignment γ}
    (hp : p.inFootprint L.footprint) (σ : VariableAssignment) :
    (p σ).satisfies (fun xs => (FVP.glob A).get xs.2 = (FVP.glob A).get σ) := by
  intro xs hxs
  obtain ⟨v, hv⟩ := satisfies_lens_set_of_inFootprint L hp σ xs hxs
  rw [← hv]
  have hmem : diracKer (L.liftFunction (Function.const _ v)) ∈ ((FVP.fvP_proc A)ᶜ).updates :=
    (Footprint.le_compl_comm _ _).mp hdisj (L.diracKer_liftFunction_mem_footprint _)
  exact Footprint.touched_getter_get_eq_of_mem hmem σ

/-- **EasyCrypt's oracle premise.**  For oracles confined to `L`, the premise of
`prhlProc_abstract_call` follows from `={arg} ∧ inv ==> ={res} ∧ inv` alone: `={glob A}` survives
because the oracles cannot see it. -/
theorem prhlProc_globInv_of_confined {holes : HoleSigs} {sig sig' : ProcedureSignature}
    {A : ProcedureWithHoles holes sig} (hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ)
    {I : Ω → Ω → Prop} {o₁ o₂ : Procedure sig'}
    (h₁ : ∀ a, (procedureDenotation o₁ a).inFootprint L.footprint)
    (h₂ : ∀ a, (procedureDenotation o₂ a).inFootprint L.footprint)
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ I (L.get g₁) (L.get g₂)) o₁ o₂
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ I (L.get g₁) (L.get g₂))) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInv L A I g₁ g₂) o₁ o₂
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInv L A I g₁ g₂) := by
  intro a₁ a₂ g₁ g₂ ⟨ha, hglob, hI⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := h a₁ a₂ g₁ g₂ ⟨ha, hI⟩
  have hμ₁ : μ.satisfies (fun w => (FVP.glob A).get w.1.2 = (FVP.glob A).get g₁) :=
    coupling_satisfies_fst (by rw [hm1]; exact glob_eq_of_inFootprint L hdisj (h₁ a₁) g₁)
  have hμ₂ : μ.satisfies (fun w => (FVP.glob A).get w.2.2 = (FVP.glob A).get g₂) :=
    coupling_satisfies_snd (by rw [hm2]; exact glob_eq_of_inFootprint L hdisj (h₂ a₂) g₂)
  refine ⟨μ, hm1, hm2, fun w hw => ?_⟩
  obtain ⟨hr, hI'⟩ := hsat w hw
  exact ⟨hr, by rw [hμ₁ w hw, hμ₂ w hw]; exact hglob, hI'⟩

end GaudisCrypt
