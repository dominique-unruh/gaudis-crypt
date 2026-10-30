import GaudisCrypt.Lib.RO.GlobTransfer
import GaudisCrypt.Logic.PRHLStmt

/-!
# The abstract call rule (EasyCrypt's `call (: inv)` for an adversary with oracles)

An adversary run against two instantiations of its oracles couples with itself as EasyCrypt's
abstract call rule says (`equivF_abs_spec`, `src/phl/ecPhlFun.ml`):

```
  equiv[ O₁.o ~ O₂.o : ={arg} ∧ inv ==> ={res} ∧ inv ]   (for every oracle o the adversary may call)
  ──────────────────────────────────────────────────────────────────────────────────────
  equiv[ D(O₁) ~ D(O₂) : ={arg} ∧ ={glob D} ∧ inv ==> ={res} ∧ ={glob D} ∧ inv ]
```

The invariant `inv` reads only the oracles' state: a lens `L` that the adversary is disjoint from
(EasyCrypt's `D <: T {-O}`; EasyCrypt also rejects an `inv` that mentions `glob D`).  Globals
outside `glob D` and `L` are unconstrained, as in EasyCrypt.

`={glob}` is agreement on a region `F` (`globInvF`): everything the adversary may touch, and
possibly more, but disjoint from `L`.  There are three forms.

* **Procedures with holes** (`prhlProc_abstract_call`).  The adversary is
  `A : ProcedureWithHoles holes sig`, its holes are the oracle procedures it may call, and
  `F = FVP.fvP_proc A`, so `={glob}` is `FVP.glob A`.
* **Modules** (`prhlProc_abstract_call_module`).  The adversary is a module
  `D : Module.Arr T (procmod …)`, as EasyCrypt declares it, and `F = FVP.fvP D`.  It comes with a
  hypothesis `D.Representable ext`: applied to any oracles `O`, `D` behaves like a procedure with
  holes filled with `ext O`, the procedures EasyCrypt lets `D` call (its `OI.allowed`).  In
  EasyCrypt this holds by construction; in Gaudí it is the gap recorded as exception E2 of the
  SHA-3 port.
* **Any region** (`prhlProc_abstract_callF`), which the other two instantiate.

The proof is the oracle-agnostic machinery of `Lib/RO/ROCouplingEquiv.lean`
(`instantiate_of_fvP_gen`), with two ingredients.
* `footprintCompat_globInvF`: the adversary's own steps preserve the invariant.  `={glob}` is
  carried by the orbit self-coupling and `inv` by the per-run preservation of the `L`-content.
  It generalizes `footprintCompat_PGlob` from equal random-oracle tables.
* `hhole_of_prhl2`: the per-oracle specifications give the per-call coupling.  It generalizes
  `ro_hhole_prhl`.

The oracle premises carry `={glob}` along, as EasyCrypt's do when an oracle can use `D`.  For
oracles confined to `L`, `prhlProc_globInvF_of_confined` removes it, as EasyCrypt does.
`glob_set_of_le_compl` rewrites `={glob}` through a write that the region cannot see.
-/

namespace GaudisCrypt

open GaudisCrypt.Lib.RO.Instantiate

variable {Ω : Type} (L : Lens Ω VariableAssignment)

/-! ## The invariant and the adversary's own steps -/

/-- The abstract call invariant `={glob} ∧ inv`.  `={glob}` is agreement on the region `F`, and
`inv` reads the oracle region `L`. -/
def globInvF (F : Footprint VariableAssignment) (I : Ω → Ω → Prop) :
    VariableAssignment → VariableAssignment → Prop :=
  fun g₁ g₂ => F.touched_getter.get g₁ = F.touched_getter.get g₂ ∧ I (L.get g₁) (L.get g₂)

/-- `globInvF` at the footprint of a procedure with holes: `={glob A} ∧ inv`. -/
def globInv {holes : HoleSigs} {sig : ProcedureSignature} (A : ProcedureWithHoles holes sig)
    (I : Ω → Ω → Prop) : VariableAssignment → VariableAssignment → Prop :=
  globInvF L (FVP.fvP_proc A) I

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

/-- A write through a lens `X` outside the region `F` leaves `F`'s content unchanged. -/
theorem touched_set_of_le_compl {F : Footprint VariableAssignment} {β : Type}
    {X : Lens β VariableAssignment} (h : X.footprint ≤ Fᶜ) (v : β) (g : VariableAssignment) :
    F.touched_getter.get (X.set v g) = F.touched_getter.get g :=
  Footprint.touched_getter_get_eq_of_mem (h (X.diracKer_liftFunction_mem_footprint
    (Function.const _ v))) g

/-- A write through a lens `X` that `A` cannot see leaves `glob A` unchanged. -/
theorem glob_set_of_le_compl {holes : HoleSigs} {sig : ProcedureSignature}
    {A : ProcedureWithHoles holes sig} {β : Type} {X : Lens β VariableAssignment}
    (h : X.footprint ≤ (FVP.fvP_proc A)ᶜ) (v : β) (g : VariableAssignment) :
    (FVP.glob A).get (X.set v g) = (FVP.glob A).get g :=
  touched_set_of_le_compl h v g

/-- The global steps outside `F`, lifted to procedure states (fixing the locals). -/
def liftedStepsOutside (F : Footprint VariableAssignment) : Set (Function.End ProgramState) :=
  { fp | ∃ f : Function.End state, diracKer f ∈ (Fᶜ).updates ∧
      fp = ProgramState.globalL.liftFunction f }

lemma lifted_orbit_outside {F : Footprint VariableAssignment} (loc : VariableAssignment)
    {g₁ g₂ : state}
    (h : Relation.EqvGen (fun a b : state => ∃ f : Function.End state,
        diracKer f ∈ (Fᶜ).updates ∧ f a = b) g₁ g₂) :
    Relation.EqvGen (fun a b => ∃ fp ∈ liftedStepsOutside F, fp a = b)
      (⟨g₁, loc⟩ : ProgramState) ⟨g₂, loc⟩ := by
  induction h with
  | rel a b hab =>
      obtain ⟨f, hf, rfl⟩ := hab
      exact Relation.EqvGen.rel _ _ ⟨ProgramState.globalL.liftFunction f, ⟨f, hf, rfl⟩, rfl⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

lemma touched_locals_of_lifted_orbit {F : Footprint VariableAssignment} {x y : ProgramState}
    (h : Relation.EqvGen (fun a b => ∃ fp ∈ liftedStepsOutside F, fp a = b) x y) :
    F.touched_getter.get x.globals = F.touched_getter.get y.globals ∧ x.locals = y.locals := by
  induction h with
  | rel a b hab =>
      obtain ⟨fp, ⟨f, hf, rfl⟩, rfl⟩ := hab
      exact ⟨(Footprint.touched_getter_get_eq_of_mem hf a.globals).symm, rfl⟩
  | refl a => exact ⟨rfl, rfl⟩
  | symm a b _ ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | trans a b c _ _ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1, ih₁.2.trans ih₂.2⟩

/-- **The adversary's own steps preserve the call invariant.**  Every program confined to what
`A` may touch self-couples from `globInvF`-related states, for any region `F` that contains `A`'s
footprint and is disjoint from `L`.  It generalizes `footprintCompat_PGlob` from equal
random-oracle tables to any `inv` on the `L`-content.  It runs the orbit self-coupling
(`prhl2_self_of_orbit`) and re-attaches `inv` through the coupling's marginals: neither side's run
changes its `L`-content. -/
theorem footprintCompat_globInvF {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) (F : Footprint VariableAssignment)
    (hAF : FVP.fvP_proc A ≤ F) (hFL : F ≤ (L.footprint)ᶜ) (I : Ω → Ω → Prop) :
    FootprintCompat (globInvF L F I) (fvP_proc A) := by
  intro γ p hp ps₁ ps₂ hpre
  obtain ⟨⟨hglob, hI⟩, hloc⟩ := hpre
  have horbG : Relation.EqvGen (fun a b : state => ∃ f : Function.End state,
      diracKer f ∈ (Fᶜ).updates ∧ f a = b) ps₁.globals ps₂.globals :=
    Quotient.exact hglob
  have horb : Relation.EqvGen (fun a b => ∃ fp ∈ liftedStepsOutside F, fp a = b) ps₁ ps₂ := by
    have h0 := lifted_orbit_outside ps₁.locals horbG
    have h1 : (⟨ps₂.globals, ps₁.locals⟩ : ProgramState) = ps₂ := by rw [hloc]
    exact h1 ▸ h0
  have hU : ∀ fp ∈ liftedStepsOutside F, diracKer fp ∈ ((fvP_proc A)ᶜ).updates := by
    rintro fp ⟨f, hf, rfl⟩
    exact lifted_step_mem_fvP_proc_compl A (Footprint.compl_antimono hAF hf)
  obtain ⟨μ, hm1, hm2, hsat⟩ := prhl2_self_of_orbit hp _ hU ps₁ ps₂ horb
  have hSle : (ProgramState.globalL.chain L).footprint ≤ (fvP_proc A)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (fvP_proc_le_chain_compl L A (le_trans hAF hFL))
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
  have hgl := touched_locals_of_lifted_orbit horbw
  refine ⟨hres, ⟨hgl.1, ?_⟩, hgl.2⟩
  rw [hμ₁ w hw, hμ₂ w hw]
  exact hI

/-! ## The oracle side -/

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

/-- **Oracles confined to `L` keep the `F`-content** of a region `F` disjoint from `L`: an
`L`-confined run changes only the `L`-content. -/
theorem touched_eq_of_inFootprint {F : Footprint VariableAssignment} (hFL : F ≤ (L.footprint)ᶜ)
    {γ : Type} {p : ProgramDenotation VariableAssignment γ}
    (hp : p.inFootprint L.footprint) (σ : VariableAssignment) :
    (p σ).satisfies (fun xs => F.touched_getter.get xs.2 = F.touched_getter.get σ) := by
  intro xs hxs
  obtain ⟨v, hv⟩ := satisfies_lens_set_of_inFootprint L hp σ xs hxs
  rw [← hv]
  exact touched_set_of_le_compl ((Footprint.le_compl_comm _ _).mp hFL) v σ

/-- **EasyCrypt's oracle premise.**  For oracles confined to `L`, the oracle premise of the rule
follows from `={arg} ∧ inv ==> ={res} ∧ inv` alone: `={glob}` survives because the oracles cannot
see it. -/
theorem prhlProc_globInvF_of_confined {F : Footprint VariableAssignment}
    (hFL : F ≤ (L.footprint)ᶜ) {sig' : ProcedureSignature}
    {I : Ω → Ω → Prop} {o₁ o₂ : Procedure sig'}
    (h₁ : ∀ a, (procedureDenotation o₁ a).inFootprint L.footprint)
    (h₂ : ∀ a, (procedureDenotation o₂ a).inFootprint L.footprint)
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ I (L.get g₁) (L.get g₂)) o₁ o₂
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ I (L.get g₁) (L.get g₂))) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L F I g₁ g₂) o₁ o₂
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L F I g₁ g₂) := by
  intro a₁ a₂ g₁ g₂ ⟨ha, hglob, hI⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := h a₁ a₂ g₁ g₂ ⟨ha, hI⟩
  have hμ₁ : μ.satisfies (fun w => F.touched_getter.get w.1.2 = F.touched_getter.get g₁) :=
    coupling_satisfies_fst (by rw [hm1]; exact touched_eq_of_inFootprint L hFL (h₁ a₁) g₁)
  have hμ₂ : μ.satisfies (fun w => F.touched_getter.get w.2.2 = F.touched_getter.get g₂) :=
    coupling_satisfies_snd (by rw [hm2]; exact touched_eq_of_inFootprint L hFL (h₂ a₂) g₂)
  refine ⟨μ, hm1, hm2, fun w hw => ?_⟩
  obtain ⟨hr, hI'⟩ := hsat w hw
  exact ⟨hr, by rw [hμ₁ w hw, hμ₂ w hw]; exact hglob, hI'⟩

/-- `prhlProc_globInvF_of_confined` at the footprint of a procedure with holes. -/
theorem prhlProc_globInv_of_confined {holes : HoleSigs} {sig sig' : ProcedureSignature}
    {A : ProcedureWithHoles holes sig} (hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ)
    {I : Ω → Ω → Prop} {o₁ o₂ : Procedure sig'}
    (h₁ : ∀ a, (procedureDenotation o₁ a).inFootprint L.footprint)
    (h₂ : ∀ a, (procedureDenotation o₂ a).inFootprint L.footprint)
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ I (L.get g₁) (L.get g₂)) o₁ o₂
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ I (L.get g₁) (L.get g₂))) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInv L A I g₁ g₂) o₁ o₂
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInv L A I g₁ g₂) :=
  prhlProc_globInvF_of_confined L hdisj h₁ h₂ h

/-! ## The rule -/

/-- **The abstract call rule, on denotations**, for any region `F` that contains `A`'s footprint
and is disjoint from the oracle region `L`. -/
theorem prhl2_instantiate_globInvF {holes : HoleSigs} {sig : ProcedureSignature}
    (inst₁ inst₂ : holes.Instantiation) (A : ProcedureWithHoles holes sig) (args : sig.ParamType)
    (F : Footprint VariableAssignment) (hAF : FVP.fvP_proc A ≤ F) (hFL : F ≤ (L.footprint)ᶜ)
    (I : Ω → Ω → Prop)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (a : sig'.ParamType),
      ProgramDenotation.prhl2 (globInvF L F I) (procedureDenotation (inst₁.lookup n) a)
        (procedureDenotation (inst₂.lookup n) a) (liftPost (globInvF L F I))) :
    ProgramDenotation.prhl2 (globInvF L F I)
      (procedureDenotation (A.instantiate inst₁) args)
      (procedureDenotation (A.instantiate inst₂) args) (liftPost (globInvF L F I)) :=
  instantiate_of_fvP_gen inst₁ inst₂ A args (footprintCompat_globInvF L A F hAF hFL I) hc
    (fun n x p hp hx => hhole_of_prhl2 inst₁ inst₂ horacle n x p hp hx)

/-- **The abstract call rule**, as a `prhlProc` judgment, for any region `F` that contains `A`'s
footprint and is disjoint from the oracle region `L`. -/
theorem prhlProc_abstract_callF {holes : HoleSigs} {sig : ProcedureSignature}
    (inst₁ inst₂ : holes.Instantiation) (A : ProcedureWithHoles holes sig)
    (F : Footprint VariableAssignment) (hAF : FVP.fvP_proc A ≤ F) (hFL : F ≤ (L.footprint)ᶜ)
    (I : Ω → Ω → Prop)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L F I g₁ g₂)
        (inst₁.lookup n) (inst₂.lookup n)
        (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L F I g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L F I g₁ g₂)
      (A.instantiate inst₁) (A.instantiate inst₂)
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L F I g₁ g₂) := by
  intro a₁ a₂ g₁ g₂ ⟨ha, hg⟩
  subst ha
  exact prhl2_instantiate_globInvF L inst₁ inst₂ A a₁ F hAF hFL I hc
    (fun n a σ₁ σ₂ h => horacle n a a σ₁ σ₂ ⟨rfl, h⟩) g₁ g₂ hg

/-- **The abstract call rule for a procedure with holes** (`={glob}` is `FVP.glob A`). -/
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
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInv L A I g₁ g₂) :=
  prhlProc_abstract_callF L inst₁ inst₂ A _ le_rfl hdisj I hc horacle

/-! ## Modules

EasyCrypt declares an adversary as a module of a functor type, `declare module D <: T`.  The rule
applies to such a module through a representation: a procedure with holes `p` that `D`, applied
to any oracles `O`, behaves like when filled with `ext O`.  `ext` picks the oracle procedures `D`
may call (EasyCrypt's `OI.allowed`).  In EasyCrypt every module is such code by construction; in
Gaudí the module language is more general, and the representation is a hypothesis
(`Module.Representable`) until a representation lemma is proven. -/

/-- `D` applied to oracles `O` behaves like `p` filled with `ext O`, and `p` touches nothing that
`D` does not. -/
structure Module.RepresentedBy {T : Type 1} [IsModule T] {sig : ProcedureSignature}
    (D : Module.Arr T (Module.Proc sig)) {holes : HoleSigs} (ext : T → holes.Instantiation)
    (p : ProcedureWithHoles holes sig) : Prop where
  denote : ∀ (O : T) (a : sig.ParamType),
    procedureDenotation (Module.app D O).procedure a = procedureDenotation (p.instantiate (ext O)) a
  fvP_le : FVP.fvP_proc p ≤ FVP.fvP D

/-- `D` is represented by some procedure with holes, its oracles chosen by `ext`. -/
def Module.Representable {T : Type 1} [IsModule T] {sig : ProcedureSignature}
    (D : Module.Arr T (Module.Proc sig)) {holes : HoleSigs} (ext : T → holes.Instantiation) :
    Prop :=
  ∃ p, Module.RepresentedBy D ext p

/-- **The abstract call rule for a module** (EasyCrypt's `declare module D <: T {-O}`, then
`call (: inv)`).  `={glob D}` is agreement on `FVP.fvP D`, everything `D` may touch. -/
theorem prhlProc_abstract_call_module {T : Type 1} [IsModule T] {sig : ProcedureSignature}
    {holes : HoleSigs} (D : Module.Arr T (Module.Proc sig)) (ext : T → holes.Instantiation)
    (hD : Module.Representable D ext) (hdisj : FVP.fvP D ≤ (L.footprint)ᶜ) (I : Ω → Ω → Prop)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (O₁ O₂ : T)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L (FVP.fvP D) I g₁ g₂)
        ((ext O₁).lookup n) ((ext O₂).lookup n)
        (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L (FVP.fvP D) I g₁ g₂)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF L (FVP.fvP D) I g₁ g₂)
      (Module.app D O₁).procedure (Module.app D O₂).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF L (FVP.fvP D) I g₁ g₂) := by
  obtain ⟨p, hden, hle⟩ := hD
  intro a₁ a₂
  rw [hden O₁ a₁, hden O₂ a₂]
  exact prhlProc_abstract_callF L (ext O₁) (ext O₂) p _ hle hdisj I hc horacle a₁ a₂

/-! ## Representability of concrete functor modules

`fvP` only grows when a procedure's holes are filled: a hole node contributes the write of the
result and the read of the arguments, and the call that replaces it contributes those and more.
So a functor module `D` whose application reduces to `p.instantiate (ext O)` (what the `module`
command's `apply_simp` lemmas state) is represented by `p`.  The footprint half goes through one
oracle `O₀` with an empty footprint:
`fvP_proc p ≤ fvP_proc (p.instantiate (ext O₀)) = fvP (D O₀) ≤ fvP D ⊔ fvP O₀ = fvP D`. -/

theorem FVP.fvP_stmt_le_instantiate {holes : HoleSigs} (s : StmtWithHoles holes)
    (inst : holes.Instantiation) :
    FVP.fvP_stmt s ≤ FVP.fvP_stmt (s.instantiate inst) := by
  induction s with
  | skip => exact le_rfl
  | sample x e => exact le_rfl
  | call' x ns hl hn b r p => exact le_rfl
  | hole n x p =>
      exact sup_le_sup_left (le_sup_of_le_right le_sup_right) _
  | seq s1 s2 ih1 ih2 => exact sup_le_sup (ih1 inst) (ih2 inst)
  | ifThenElse c t e iht ihe => exact sup_le_sup_left (sup_le_sup (iht inst) (ihe inst)) _
  | «while» c t iht => exact sup_le_sup_left (iht inst) _

theorem FVP.fvP_proc_le_instantiate {holes : HoleSigs} {sig : ProcedureSignature}
    (p : ProcedureWithHoles holes sig) (inst : holes.Instantiation) :
    FVP.fvP_proc p ≤ FVP.fvP_proc (p.instantiate inst) :=
  sup_le_sup_right (Lens.reduceFootprint_mono _ (FVP.fvP_stmt_le_instantiate p.body inst)) _

/-- Reducing the empty footprint through a lens gives the empty footprint. -/
theorem Lens.reduceFootprint_bot {a b : Type*} (lens : Lens a b) :
    Lens.reduceFootprint lens ⊥ = ⊥ :=
  le_bot_iff.mp (le_trans (Lens.reduceFootprint_mono lens bot_le)
    (FVP.Lens.reduceFootprint_extend_le lens ⊥))

theorem FVP.fvP_module_proc {sig : ProcedureSignature} (q : Procedure sig) :
    FVP.fvP (Module.proc q) = FVP.fvP_proc q := by
  unfold FVP.fvP InductiveFunctionGettersSetters.eval InductiveFunction.eval
    InductiveFunction.eval'
  change fvpInductiveFunctionGS.inductiveFunction.evalMexpr (Module.proc q).expression = _
  rw [Module.proc, Module.toModule_expression, ModuleExpression.reduce_proc]
  rfl

/-- **A functor module that applies to `p.instantiate (ext O)` is represented by `p`**, given one
oracle module `O₀` with an empty footprint (to bound `p`'s footprint by `D`'s). -/
theorem Module.representedBy_of_app_eq {T : Type 1} [IsModule T] {sig : ProcedureSignature}
    (D : Module.Arr T (Module.Proc sig)) {holes : HoleSigs} (ext : T → holes.Instantiation)
    (p : ProcedureWithHoles holes sig)
    (happ : ∀ O, Module.app D O = Module.proc (p.instantiate (ext O)))
    (O₀ : T) (h₀ : FVP.fvP O₀ = ⊥) :
    Module.RepresentedBy D ext p where
  denote O a := by rw [happ O, Module.procedure_proc']
  fvP_le := by
    calc FVP.fvP_proc p ≤ FVP.fvP_proc (p.instantiate (ext O₀)) :=
          FVP.fvP_proc_le_instantiate p _
      _ = FVP.fvP (Module.app D O₀) := by rw [happ O₀, FVP.fvP_module_proc]
      _ ≤ FVP.fvP D ⊔ FVP.fvP O₀ := FVP.fvP_app D O₀
      _ = FVP.fvP D := by rw [h₀, sup_bot_eq]

end GaudisCrypt
