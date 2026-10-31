import GaudisCrypt.Logic.Inline

/-!
# Representing functor modules by procedures with holes

The abstract call rule needs an adversary `D` as code: a procedure with holes `p` that `D`,
applied to oracles `O`, behaves like when filled with `ext O` (`Module.RepresentedBy`,
`Logic/AbstractCall.lean`).  Exception E2 of the SHA-3 port takes this as a hypothesis.  Every
module is code, though: a closed normal module expression.  This file works towards extracting the
representation from that normal form, for functors over first-order oracle types (products of
procedures), with the full list of the oracle's procedures as `ext`.

* **Substituting procedures with holes for holes** (`StmtWithHoles.substHoles`,
  `ProcedureWithHoles.substHoles`): each hole call becomes the flattened call of the substituted
  procedure, everything else is re-targeted along `Flatten.trafo`.  Sound
  (`ProcedureWithHoles.procedureDenotation_substHoles`), from the inliner's term-level lemmas
  (`StmtWithHoles.equivInLens_flattenCall`, `StmtWithHoles.applyLens`, the `EquivInLens`
  congruences).  This is the extraction step for a procedure with holes applied to a tuple.
* **First-order normal forms** (`ModuleExpression.FONormal`, `foNormal_of_hasType`,
  `Module.expression_shape`): over first-order parameters a normal term of first-order type is a
  procedure, a tuple, a component of a parameter, or a procedure with holes applied to such a tuple.
  These are the cases the extraction recurses on.
-/

namespace GaudisCrypt

namespace Flatten

/-- Write the arguments into the parameter slots `names` of a fresh callee frame `emb` (all its
other locals `init`). -/
noncomputable def paramWriter (names : List String) (tys : List Type)
    (hlen : names.length = tys.length) : Setter (typeListToTuple tys) ProgramState where
  set a σ := emb.set (ProgramState.localL.set
    (VariableAssignment.setParams names tys hlen a VariableAssignment.init) (emb.get σ)) σ
  set_set σ a b := by
    simp only [emb.set_get, ProgramState.localL.set_set, emb.set_set]

end Flatten

open Flatten in
/-- The call of a procedure with holes `q`, flattened into the caller: reset the callee frame,
write the arguments, run `q`'s body in the frame `emb`, store the return value. -/
noncomputable def StmtWithHoles.flattenedCall {h : HoleSigs} {sig : ProcedureSignature}
    (x : Setter sig.ret ProgramState) (q : ProcedureWithHoles h sig)
    (args : Getter sig.ParamType ProgramState) : StmtWithHoles h :=
  ((StmtWithHoles.assign (emb.chainSetter (resetSetter Set.univ)) ⟨fun _st => ()⟩).seq
    (StmtWithHoles.assign (a := typeListToTuple sig.params)
      (paramWriter q.parameterNames sig.params q.parameterNames_length)
      (trafo.chainGetter args))).seq
    ((q.body.applyLens emb).seq
      (StmtWithHoles.assign (trafo.chainSetter x) (emb.chainGetter q.return_val)))

open Flatten in
/-- **Flattening the call of a procedure with holes**: calling `q` filled with `inst` is
equivalent, along `trafo`, to `q`'s flattened call filled with `inst`.  This is
`StmtWithHoles.equivInLens_flattenCall` at the instantiated body, with `applyLens` commuted past
the instantiation. -/
theorem equivInLens_flattenedCall {h : HoleSigs} {sig : ProcedureSignature}
    (x : Setter sig.ret ProgramState) (q : ProcedureWithHoles h sig)
    (args : Getter sig.ParamType ProgramState) (inst : h.Instantiation) :
    (programDenotation (Stmt.call x (q.instantiate inst) args)).EquivInLens
      (programDenotation ((StmtWithHoles.flattenedCall x q args).instantiate inst)) trafo := by
  let P := paramWriter q.parameterNames sig.params q.parameterNames_length
  let σ₁ : ProgramState → ProgramState := fun τ =>
    (emb.chainSetter (resetSetter Set.univ)).set () τ
  let f : ProgramState → ProgramState := fun τ => P.set (args.get (trafo.get (σ₁ τ))) (σ₁ τ)
  have hvis₁ : ∀ τ, trafo.get (σ₁ τ) = trafo.get τ := fun τ => by
    simp only [σ₁, emb_chainSetter_resetSetter_univ_set, trafo_get_emb_set]
    rfl
  have hemb₁ : ∀ τ, emb.get (σ₁ τ) = ⟨τ.globals, VariableAssignment.init⟩ := fun τ => by
    simp only [σ₁, emb_chainSetter_resetSetter_univ_set, emb.set_get]
  have hpre := StmtWithHoles.equivInLens_flattenCall (hCtx := .empty) trafo emb
    trafo_chain_globalL emb_chain_globalL trafo_get_emb_set x q.parameterNames
    q.parameterNames_length q.parameterNames_nodup args (q.body.instantiate inst) q.return_val
    ((StmtWithHoles.assign (emb.chainSetter (resetSetter Set.univ)) ⟨fun _st => ()⟩).seq
      (StmtWithHoles.assign P (trafo.chainGetter args))) f
    (fun _ τ => programDenotation_seq_apply_det (programDenotation_assign_apply _ _)
      (programDenotation_assign_apply _ _) τ)
    (fun τ => by
      simp only [f, hvis₁, P, paramWriter, emb.set_get, hemb₁]
      rfl)
    (fun τ => by
      simp only [f, hvis₁, P, paramWriter, trafo_get_emb_set]
      change ProgramState.globalL.set (emb.get (σ₁ τ)).globals _ = _
      rw [hemb₁]
      have hg : (trafo.get τ).globals = τ.globals :=
        congrArg (fun L : Lens VariableAssignment ProgramState => L.get τ) trafo_chain_globalL
      rw [← hg]
      exact ProgramState.globalL.get_set (trafo.get τ)) ⟨⟩
  simp only [StmtWithHoles.instantiate, StmtWithHoles.weaken_instantiate] at hpre
  simp only [StmtWithHoles.flattenedCall, StmtWithHoles.instantiate, StmtWithHoles.assign,
    StmtWithHoles.applyLens_instantiate]
  exact hpre


open Flatten in
/-- **Substituting procedures with holes for the holes of a statement**: each hole `n` becomes
the flattened call of `q n`; everything else is re-targeted along `trafo`, which makes room for
the callee frames. -/
noncomputable def StmtWithHoles.substHoles {h h' : HoleSigs}
    (q : ∀ {sig : ProcedureSignature}, HoleIndex h sig → ProcedureWithHoles h' sig) :
    StmtWithHoles h → StmtWithHoles h'
  | .skip => .skip
  | .sample x e => .sample (trafo.chainSetter x) (trafo.chainGetter e)
  | .call' x ns hl hn b r p => .call' (trafo.chainSetter x) ns hl hn b r (trafo.chainGetter p)
  | .hole n x p => StmtWithHoles.flattenedCall x (q n) p
  | .seq s t => .seq (substHoles q s) (substHoles q t)
  | .ifThenElse c t e => .ifThenElse (trafo.chainGetter c) (substHoles q t) (substHoles q e)
  | .while c t => .while (trafo.chainGetter c) (substHoles q t)

open Flatten in
/-- **The substitution is sound**: filling the holes of `s` with the `q n` filled with `inst'` is
equivalent, along `trafo`, to filling the substituted statement with `inst'`. -/
theorem StmtWithHoles.equivInLens_substHoles {h h' : HoleSigs}
    (q : ∀ {sig : ProcedureSignature}, HoleIndex h sig → ProcedureWithHoles h' sig)
    (inst : h.Instantiation) (inst' : h'.Instantiation)
    (hinst : ∀ {sig : ProcedureSignature} (n : HoleIndex h sig),
      inst.lookup n = (q n).instantiate inst') :
    ∀ s : StmtWithHoles h, (programDenotation (s.instantiate inst)).EquivInLens
      (programDenotation ((s.substHoles q).instantiate inst')) trafo
  | .skip => by
      simp only [StmtWithHoles.substHoles, StmtWithHoles.instantiate, programDenotation,
        ProgramDenotation.skip]
      exact ProgramDenotation.EquivInLens.pure ()
  | .sample x e => by
      have := ProgramDenotation.equivInLens_zoom trafo
        (programDenotation (StmtWithHoles.sample x e))
      rw [← programDenotation_applyLens trafo trafo_chain_globalL] at this
      exact this
  | .call' x ns hl hn b r p => by
      have := ProgramDenotation.equivInLens_zoom trafo
        (programDenotation (StmtWithHoles.call' x ns hl hn b r p))
      rw [← programDenotation_applyLens trafo trafo_chain_globalL] at this
      exact this
  | .hole n x p => by
      simp only [StmtWithHoles.substHoles, StmtWithHoles.instantiate, hinst n]
      exact equivInLens_flattenedCall x (q n) p inst'
  | .seq s t => by
      simp only [StmtWithHoles.substHoles, StmtWithHoles.instantiate, programDenotation]
      exact ProgramDenotation.EquivInLens.bind
        (StmtWithHoles.equivInLens_substHoles q inst inst' hinst s)
        fun _ => StmtWithHoles.equivInLens_substHoles q inst inst' hinst t
  | .ifThenElse c t e => by
      simp only [StmtWithHoles.substHoles, StmtWithHoles.instantiate, programDenotation]
      refine ProgramDenotation.EquivInLens.bind (ProgramDenotation.EquivInLens.get trafo c)
        fun bv => ?_
      cases bv
      · simpa using StmtWithHoles.equivInLens_substHoles q inst inst' hinst e
      · simpa using StmtWithHoles.equivInLens_substHoles q inst inst' hinst t
  | .while c t => by
      simp only [StmtWithHoles.substHoles, StmtWithHoles.instantiate, programDenotation]
      exact ProgramDenotation.EquivInLens.while_loop (ProgramDenotation.EquivInLens.get trafo c)
        (StmtWithHoles.equivInLens_substHoles q inst inst' hinst t)

open Flatten in
/-- A procedure with its holes substituted (`StmtWithHoles.substHoles`). -/
noncomputable def ProcedureWithHoles.substHoles {h h' : HoleSigs} {sig : ProcedureSignature}
    (p : ProcedureWithHoles h sig)
    (q : ∀ {sig : ProcedureSignature}, HoleIndex h sig → ProcedureWithHoles h' sig) :
    ProcedureWithHoles h' sig :=
  ⟨p.parameterNames, p.parameterNames_length, p.parameterNames_nodup, p.body.substHoles q,
    trafo.chainGetter p.return_val⟩

open Flatten in
/-- **The substitution is sound for procedures**: `p` with its holes substituted by the `q n`,
filled with `inst'`, computes what `p` filled with the `q n` filled with `inst'` computes.  The
parameter names must not start with `@` (`escape` keeps them). -/
theorem ProcedureWithHoles.procedureDenotation_substHoles {h h' : HoleSigs}
    {sig : ProcedureSignature} (p : ProcedureWithHoles h sig)
    (q : ∀ {sig : ProcedureSignature}, HoleIndex h sig → ProcedureWithHoles h' sig)
    (inst : h.Instantiation) (inst' : h'.Instantiation)
    (hinst : ∀ {sig : ProcedureSignature} (n : HoleIndex h sig),
      inst.lookup n = (q n).instantiate inst')
    (hfix : ∀ n ∈ p.parameterNames, escape n = n) :
    procedureDenotation ((p.substHoles q).instantiate inst') =
      procedureDenotation (p.instantiate inst) := by
  have hb : StmtWithHoles.EquivInLens (hCtx := .empty) (p.body.instantiate inst)
      ((p.body.substHoles q).instantiate inst') trafo := fun i => by
    rw [StmtWithHoles.instantiate_empty, StmtWithHoles.instantiate_empty]
    exact StmtWithHoles.equivInLens_substHoles q inst inst' hinst p.body
  exact procedureDenotation_congr p.parameterNames p.parameterNames_length
    p.parameterNames_nodup trafo _ _ p.return_val hb
    (fixesEntry_trafo _ _ _ hfix) trafo_chain_globalL

/-- First-order module types: products of procedures (and `unit`), no functors. -/
def ModuleTypeRep.FirstOrder : ModuleTypeRep → Prop
  | .proc _ => True
  | .unit => True
  | .prod a b => a.FirstOrder ∧ b.FirstOrder
  | .arr _ _ => False

theorem HoleSigs.toModuleTypeRepTuple_firstOrder :
    ∀ holes : HoleSigs, holes.toModuleTypeRepTuple.FirstOrder
  | .empty => trivial
  | .cons _ h => ⟨trivial, HoleSigs.toModuleTypeRepTuple_firstOrder h⟩

namespace ModuleExpression

/-- A chain of projections of a variable: a component of a module parameter. -/
inductive FOProj : ModuleExpression → Prop
  | var (n : Nat) : FOProj (.var n)
  | fst {e} : FOProj e → FOProj (.fst e)
  | snd {e} : FOProj e → FOProj (.snd e)

/-- The normal forms of first-order type over first-order parameters: procedures, tuples,
components of parameters, and procedures with holes applied to such (not literal) tuples. -/
inductive FONormal : ModuleExpression → Prop
  | «proc» {sig} (p : Procedure sig) : FONormal (.proc p)
  | unit : FONormal .unit
  | pair {a b} : FONormal a → FONormal b → FONormal (.pair a b)
  | proj {e} : FOProj e → FONormal e
  | appProcHoles {holes sig} (ne : holes.NonEmpty) (p : ProcedureWithHoles holes sig) {arg} :
      FONormal arg → ¬ IsProcTuple arg → FONormal (.app (.procHoles ne p) arg)

/-- **Inversion of first-order normal forms**: over first-order parameters, a normal term of
first-order type is an `FONormal`; a neutral term has first-order type, and is a component of a
parameter unless it has procedure type. -/
theorem foNormal_of_hasType {Δ : ModuleContext} (hΔ : ∀ A ∈ Δ, A.FirstOrder) :
    ∀ (m : ModuleExpression) {T : ModuleTypeRep}, m.HasType Δ T →
      (Normal m → T.FirstOrder → FONormal m) ∧
      (Neutral m → T.FirstOrder ∧ FONormal m ∧ (FOProj m ∨ ∃ sig, T = .proc sig))
  | .var n, T, h => by
      obtain ⟨hn, rfl⟩ := h.var_inv
      have hT := hΔ _ (List.getElem_mem hn)
      exact ⟨fun _ _ => .proj (.var n), fun _ => ⟨hT, .proj (.var n), .inl (.var n)⟩⟩
  | .proc p, T, h => by
      obtain rfl := h.proc_inv
      exact ⟨fun _ _ => .proc p, fun hn => nomatch hn⟩
  | .unit, T, _ => ⟨fun _ _ => .unit, fun hn => nomatch hn⟩
  | .procHoles ne p, T, h => by
      obtain rfl := h.procHoles_inv
      exact ⟨fun _ hT => hT.elim, fun hn => nomatch hn⟩
  | .abs b, T, h => by
      obtain ⟨A, B, rfl, -⟩ := h.abs_inv
      exact ⟨fun _ hT => hT.elim, fun hn => nomatch hn⟩
  | .pair a b, T, h => by
      obtain ⟨A, B, rfl, ha, hb⟩ := h.pair_inv
      refine ⟨fun hn hT => ?_, fun hn => nomatch hn⟩
      cases hn with
      | neutral hne => exact nomatch hne
      | pair na nb =>
        exact .pair ((foNormal_of_hasType hΔ a ha).1 na hT.1)
          ((foNormal_of_hasType hΔ b hb).1 nb hT.2)
  | .fst e, T, h => by
      obtain ⟨B, he⟩ := h.fst_inv
      have hneu : Neutral (.fst e) →
          T.FirstOrder ∧ FONormal (.fst e) ∧ (FOProj (.fst e) ∨ ∃ sig, T = .proc sig) := by
        intro hn
        cases hn with
        | fst hne =>
          obtain ⟨hT, -, hproj⟩ := (foNormal_of_hasType hΔ e he).2 hne
          rcases hproj with hp | ⟨sig, hsig⟩
          · exact ⟨hT.1, .proj (.fst hp), .inl (.fst hp)⟩
          · cases hsig
      refine ⟨fun hn _ => ?_, hneu⟩
      cases hn with
      | neutral hne => exact (hneu hne).2.1
  | .snd e, T, h => by
      obtain ⟨A, he⟩ := h.snd_inv
      have hneu : Neutral (.snd e) →
          T.FirstOrder ∧ FONormal (.snd e) ∧ (FOProj (.snd e) ∨ ∃ sig, T = .proc sig) := by
        intro hn
        cases hn with
        | snd hne =>
          obtain ⟨hT, -, hproj⟩ := (foNormal_of_hasType hΔ e he).2 hne
          rcases hproj with hp | ⟨sig, hsig⟩
          · exact ⟨hT.2, .proj (.snd hp), .inl (.snd hp)⟩
          · cases hsig
      refine ⟨fun hn _ => ?_, hneu⟩
      cases hn with
      | neutral hne => exact (hneu hne).2.1
  | .app f arg, T, h => by
      obtain ⟨A, hf, harg⟩ := h.app_inv
      have hneu : Neutral (.app f arg) →
          T.FirstOrder ∧ FONormal (.app f arg) ∧ (FOProj (.app f arg) ∨ ∃ sig, T = .proc sig) := by
        intro hn
        cases hn with
        | app hfn _ => exact ((foNormal_of_hasType hΔ f hf).2 hfn).1.elim
        | appProcHoles ne nArg hnt =>
          have h' := hf.procHoles_inv
          injection h' with hA hT
          subst hA hT
          exact ⟨trivial, .appProcHoles ne _ ((foNormal_of_hasType hΔ arg harg).1 nArg
            (HoleSigs.toModuleTypeRepTuple_firstOrder _)) hnt, .inr ⟨_, rfl⟩⟩
      refine ⟨fun hn _ => ?_, hneu⟩
      cases hn with
      | neutral hne => exact (hneu hne).2.1

end ModuleExpression

/-- **The shape of a first-order functor module**: a closed normal module of type
`T →ₘ procmod …`, `T` first-order, is a procedure with holes, or an abstraction whose body is a
first-order normal form over the parameter. -/
theorem Module.expression_shape {T : ModuleTypeRep} {sig : ProcedureSignature}
    (hT : T.FirstOrder) (D : GaudisCrypt.Module (.arr T (.proc sig))) :
    (∃ (holes : HoleSigs) (ne : holes.NonEmpty) (p : ProcedureWithHoles holes sig),
        D.expression = .procHoles ne p) ∨
      ∃ b, D.expression = .abs b ∧ b.FONormal ∧ b.HasType [T] (.proc sig) := by
  have ht := D.typed
  have hn := D.normal
  revert ht hn
  generalize D.expression = e
  intro ht hn
  cases hn with
  | «proc» => exact absurd ht.proc_inv (by simp)
  | procHoles =>
      have h' := ht.procHoles_inv
      injection h' with _ hs
      injection hs with hs
      subst hs
      exact .inl ⟨_, _, _, rfl⟩
  | abs hb =>
      obtain ⟨A, B, hAB, hbody⟩ := ht.abs_inv
      injection hAB with hA hB
      subst hA hB
      refine .inr ⟨_, rfl, (ModuleExpression.foNormal_of_hasType
        (fun A hA => by simp at hA; exact hA ▸ hT) _ hbody).1 hb trivial, hbody⟩
  | pair => exact absurd ht.pair_inv (by rintro ⟨_, _, h, -⟩; cases h)
  | unit => exact absurd ht.unit_inv (by simp)

end GaudisCrypt
