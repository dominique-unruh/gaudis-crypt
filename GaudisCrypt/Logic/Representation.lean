import GaudisCrypt.Logic.Inline
import GaudisCrypt.FV
import GaudisCrypt.Lib.RO.InstantiateCommon

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
* **The footprint of a substitution** (`FVP.fvP_proc_substHoles_le`): no more than the procedure's
  own and the substituted procedures'.  `fvP` sees a procedure's globals only
  (`Lens.reduceFootprint ProgramState.globalL`), and the renamings of the locals are invisible
  there: a kernel on the globals commutes with `zoom l p` once it commutes with `p`, for `l`
  keeping the globals (`Footprint.GlobalsCommute.zoom`, by `Lens.reduceFootprint_alt_def`).  The
  callee frame's reset and parameter writes are on the locals alone (`footprint_zoom_localL_le`).
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

/-- A slot update on both sides of the renaming `ι`: slot `n` on the right, slot `ι n` on the
left. -/
theorem VariableAssignment.update_withName_rel (ι : String → String) (hι : ι.Injective)
    {m m' : VariableAssignment} (hm : ∀ v : VariableName, m (v.withName (ι v.name)) = m' v)
    (n : String) (T : Type) [Nonempty T] (a : T) (v : VariableName) :
    (varLens (.mk (ι n) T)).set a m (v.withName (ι v.name)) =
      (varLens (.mk n T)).set a m' v := by
  classical
  by_cases hv : v = .mk n T
  · subst hv
    show Function.update m (.mk (ι n) T) a (.mk (ι n) T) = Function.update m' (.mk n T) a (.mk n T)
    rw [Function.update_self, Function.update_self]
  · have hw : v.withName (ι v.name) ≠ .mk (ι n) T := by
      intro h
      apply hv
      have hn : ι v.name = ι n := congrArg VariableName.name h
      have ht : v.type = T := congrArg VariableName.type h
      exact VariableName.ext' (hι hn) ht
    simp only [varLens]
    rw [Function.update_of_ne hw, Function.update_of_ne hv]
    exact hm v

/-- `setParams` commutes with renaming the slots by `ι`. -/
theorem VariableAssignment.setParams_map_withName (ι : String → String) (hι : ι.Injective) :
    ∀ (names : List String) (tys : List Type) (h : names.length = tys.length)
      (h' : (names.map ι).length = tys.length) (args : typeListToTuple tys)
      {m m' : VariableAssignment}, (∀ v : VariableName, m (v.withName (ι v.name)) = m' v) →
      ∀ v : VariableName, VariableAssignment.setParams (names.map ι) tys h' args m
          (v.withName (ι v.name)) = VariableAssignment.setParams names tys h args m' v
  | [], [], _, _, _, _, _, hm, v => by simpa [VariableAssignment.setParams] using hm v
  | [n], [T], _, _, a, _, _, hm, v => by
      haveI : Nonempty T := ⟨a⟩
      exact VariableAssignment.update_withName_rel ι hι hm n T a v
  | n :: n' :: ns, T :: T' :: Ts, h, h', (a, as), _, _, hm, v => by
      haveI : Nonempty T := ⟨a⟩
      exact VariableAssignment.setParams_map_withName ι hι (n' :: ns) (T' :: Ts)
        (by simpa using h) (by simpa using h') as
        (VariableAssignment.update_withName_rel ι hι hm n T a) v
  | [], _ :: _, h, _, _, _, _, _, _ => absurd h (by simp)
  | _ :: _, [], h, _, _, _, _, _, _ => absurd h (by simp)
  | [_], _ :: _ :: _, h, _, _, _, _, _, _ => absurd h (by simp)
  | _ :: _ :: _, [_], h, _, _, _, _, _, _ => absurd h (by simp)

open Flatten in
/-- `trafo` sees the parameters written into the escaped slots in the original ones. -/
theorem Flatten.trafo_get_entry_escape (names : List String) (tys : List Type)
    (h : names.length = tys.length) (h' : (names.map escape).length = tys.length)
    (args : typeListToTuple tys) (st : VariableAssignment) :
    trafo.get ⟨st, VariableAssignment.setParams (names.map escape) tys h' args
        VariableAssignment.init⟩ =
      ⟨st, VariableAssignment.setParams names tys h args VariableAssignment.init⟩ := by
  change (⟨st, fun v => VariableAssignment.setParams (names.map escape) tys h' args
      VariableAssignment.init (v.withName (escape v.name))⟩ : ProgramState) = _
  congr 1
  funext v
  exact VariableAssignment.setParams_map_withName escape escape_injective names tys h h' args
    (fun _ => rfl) v

/-- `procedureDenotation_congr` with the parameters renamed: the renaming `l` sees the entry state
of `names'` as that of `names`. -/
theorem Flatten.procedureDenotation_congr_rename {sig : ProcedureSignature}
    (names names' : List String) (hlen : names.length = sig.params.length)
    (hlen' : names'.length = sig.params.length) (hnodup : names.Nodup) (hnodup' : names'.Nodup)
    (l : Lens ProgramState ProgramState) (b b' : Stmt) (r : Getter sig.ret ProgramState)
    (hb : b.EquivInLens b' l)
    (hinit : ∀ (st : VariableAssignment) (args : typeListToTuple sig.params),
      l.get ⟨st, VariableAssignment.setParams names' sig.params hlen' args VariableAssignment.init⟩
        = ⟨st, VariableAssignment.setParams names sig.params hlen args VariableAssignment.init⟩)
    (hglobL : l.chain ProgramState.globalL = ProgramState.globalL) :
    procedureDenotation (⟨names', hlen', hnodup', b', l.chainGetter r⟩ : Procedure sig)
      = procedureDenotation (⟨names, hlen, hnodup, b, r⟩ : Procedure sig) := by
  have hglob : ∀ τ, (l.get τ).globals = τ.globals := fun τ =>
    congrArg (fun L : Lens VariableAssignment ProgramState => L.get τ) hglobL
  funext argv st
  let τ : ProgramState :=
    ⟨st, VariableAssignment.setParams names' sig.params hlen' argv VariableAssignment.init⟩
  have h := hb ⟨⟩ (l.get τ) τ rfl
  rw [StmtWithHoles.instantiate_empty, StmtWithHoles.instantiate_empty, hinit] at h
  change (programDenotation b' τ).hbind (fun p => Pure.pure (r.get (l.get p.2), p.2.globals))
    = (programDenotation b ⟨st, VariableAssignment.setParams names sig.params hlen argv
        VariableAssignment.init⟩).hbind (fun p => Pure.pure (r.get p.2, p.2.globals))
  rw [← h, SubProbability.mapState_eq, SubProbability.bind_hbind]
  congr 1; funext p
  rw [SubProbability.pure_hbind, hglob]

open Flatten in
/-- A procedure with its holes substituted (`StmtWithHoles.substHoles`). -/
noncomputable def ProcedureWithHoles.substHoles {h h' : HoleSigs} {sig : ProcedureSignature}
    (p : ProcedureWithHoles h sig)
    (q : ∀ {sig : ProcedureSignature}, HoleIndex h sig → ProcedureWithHoles h' sig) :
    ProcedureWithHoles h' sig :=
  ⟨p.parameterNames.map escape, by simp [p.parameterNames_length],
    p.parameterNames_nodup.map escape_injective, p.body.substHoles q,
    trafo.chainGetter p.return_val⟩

open Flatten in
/-- **The substitution is sound for procedures**: `p` with its holes substituted by the `q n`,
filled with `inst'`, computes what `p` filled with the `q n` filled with `inst'` computes. -/
theorem ProcedureWithHoles.procedureDenotation_substHoles {h h' : HoleSigs}
    {sig : ProcedureSignature} (p : ProcedureWithHoles h sig)
    (q : ∀ {sig : ProcedureSignature}, HoleIndex h sig → ProcedureWithHoles h' sig)
    (inst : h.Instantiation) (inst' : h'.Instantiation)
    (hinst : ∀ {sig : ProcedureSignature} (n : HoleIndex h sig),
      inst.lookup n = (q n).instantiate inst') :
    procedureDenotation ((p.substHoles q).instantiate inst') =
      procedureDenotation (p.instantiate inst) := by
  have hb : StmtWithHoles.EquivInLens (hCtx := .empty) (p.body.instantiate inst)
      ((p.body.substHoles q).instantiate inst') trafo := fun i => by
    rw [StmtWithHoles.instantiate_empty, StmtWithHoles.instantiate_empty]
    exact StmtWithHoles.equivInLens_substHoles q inst inst' hinst p.body
  exact procedureDenotation_congr_rename p.parameterNames _ p.parameterNames_length _
    p.parameterNames_nodup _ trafo _ _ p.return_val hb
    (fun st args => trafo_get_entry_escape _ _ _ _ args st) trafo_chain_globalL

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

/-! ## The footprint of a substitution -/

section SubstFootprint
open Classical

/-- A kernel `f` on the globals, lifted to program states, commutes with every update of `R`:
the condition `Lens.reduceFootprint_alt_def` characterizes `R`'s share of the globals by. -/
def Footprint.GlobalsCommute (R : Footprint ProgramState)
    (f : VariableAssignment → SubProbability VariableAssignment) : Prop :=
  ∀ g ∈ R.updates, ProgramState.globalL.liftSubProbability f * g =
    g * ProgramState.globalL.liftSubProbability f

/-- Comparing the globals' shares of two footprints by the kernels commuting with them. -/
theorem reduce_globalL_le_of_globalsCommute {A B : Footprint ProgramState}
    (h : ∀ f, B.GlobalsCommute f → A.GlobalsCommute f) :
    Lens.reduceFootprint ProgramState.globalL A ≤ Lens.reduceFootprint ProgramState.globalL B := by
  rw [Lens.reduceFootprint_alt_def, Lens.reduceFootprint_alt_def]
  exact Footprint.from_mono (Set.centralizer_subset fun f hf => h f hf)

theorem Footprint.GlobalsCommute.mono {A B : Footprint ProgramState} (hAB : A ≤ B) {f}
    (h : B.GlobalsCommute f) : A.GlobalsCommute f := fun g hg => h g (hAB hg)

/-- Commuting with a join: with each joinand (the updates of a join are the bicommutant of the
union). -/
theorem Footprint.GlobalsCommute.iSup {ι : Sort*} {A : ι → Footprint ProgramState} {f}
    (h : ∀ i, (A i).GlobalsCommute f) : (⨆ i, A i).GlobalsCommute f := by
  intro g hg
  have hF : ProgramState.globalL.liftSubProbability f ∈
      Set.centralizer (⋃ x ∈ Set.range A, x.updates) := by
    rw [Set.mem_centralizer_iff]
    intro k hk
    simp only [Set.mem_iUnion, Set.mem_range] at hk
    obtain ⟨_, ⟨i, rfl⟩, hk⟩ := hk
    exact (h i k hk).symm
  exact ((Set.mem_centralizer_iff.mp hg) _ hF)

theorem Footprint.GlobalsCommute.sup {A B : Footprint ProgramState} {f}
    (hA : A.GlobalsCommute f) (hB : B.GlobalsCommute f) : (A ⊔ B).GlobalsCommute f := by
  rw [sup_eq_iSup]
  exact Footprint.GlobalsCommute.iSup fun b => by cases b <;> assumption

variable (l : Lens ProgramState ProgramState)
  (hl : l.chain ProgramState.globalL = ProgramState.globalL)
include hl

theorem globals_set_of_chain (τ σ : ProgramState) : (l.set τ σ).globals = τ.globals := by
  have h1 : ∀ x, (l.get x).globals = x.globals := fun x =>
    congrArg (fun L : Lens VariableAssignment ProgramState => L.get x) hl
  rw [← h1, l.set_get]

theorem globalL_set_set_of_chain (g : VariableAssignment) (τ σ : ProgramState) :
    ProgramState.globalL.set g (l.set τ σ) = l.set (ProgramState.globalL.set g τ) σ := by
  have h2 : ∀ x, l.set (ProgramState.globalL.set g (l.get x)) x = ProgramState.globalL.set g x :=
    fun x => congrArg (fun L : Lens VariableAssignment ProgramState => L.set g x) hl
  rw [← h2, l.set_get, l.set_set]

theorem get_globalL_set_of_chain (g : VariableAssignment) (σ : ProgramState) :
    l.get (ProgramState.globalL.set g σ) = ProgramState.globalL.set g (l.get σ) := by
  have h2 : l.set (ProgramState.globalL.set g (l.get σ)) σ = ProgramState.globalL.set g σ :=
    congrArg (fun L : Lens VariableAssignment ProgramState => L.set g σ) hl
  rw [← h2, l.set_get]

theorem set_globalL_set_of_chain (g : VariableAssignment) (τ σ : ProgramState) :
    l.set τ (ProgramState.globalL.set g σ) = l.set τ σ := by
  have h2 : l.set (ProgramState.globalL.set g (l.get σ)) σ = ProgramState.globalL.set g σ :=
    congrArg (fun L : Lens VariableAssignment ProgramState => L.set g σ) hl
  rw [← h2, l.set_set]

/-- **A zoomed program commutes with what the original commutes with**, along a lens of program
states that keeps the globals: a kernel on the globals commutes with every generator of
`zoom l p` once it commutes with those of `p`, at the zoomed state. -/
theorem Footprint.GlobalsCommute.zoom {α : Type} {p : ProgramDenotation ProgramState α} {f}
    (hf : p.footprint.GlobalsCommute f) : (ProgramDenotation.zoom l p).footprint.GlobalsCommute f := by
  intro g hg
  set F : ProgramState → SubProbability ProgramState := ProgramState.globalL.liftSubProbability f
  have hgen : F ∈ Set.centralizer (Set.range fun (y : α) (st : ProgramState) =>
      (do let (x, st') ← ProgramDenotation.zoom l p st; if x = y then pure st' else ⊥ :
        SubProbability ProgramState)) := by
    rw [Set.mem_centralizer_iff]
    rintro _ ⟨y, rfl⟩
    have hy := hf _ (Set.subset_centralizer_centralizer (show (fun st : ProgramState =>
      (do let (x, st') ← p st; if x = y then pure st' else ⊥ : SubProbability ProgramState)) ∈
        Set.range _ from ⟨y, rfl⟩))
    set k : ProgramState → SubProbability ProgramState := fun st =>
      (do let (x, st') ← p st; if x = y then pure st' else ⊥ : SubProbability ProgramState)
    have hk' : (fun st : ProgramState =>
        (do let (x, st') ← ProgramDenotation.zoom l p st; if x = y then pure st' else ⊥ :
          SubProbability ProgramState)) = fun σ => k (l.get σ) >>= fun τ => pure (l.set τ σ) := by
      funext σ
      simp only [ProgramDenotation.zoom, k, SubProbability.hbind_bind, SubProbability.pure_bind,
        SubProbability.bind_assoc]
      rw [SubProbability.hbind_eq_bind]
      congr 1; funext w
      split_ifs <;> simp [SubProbability.pure_bind, SubProbability.bot_bind]
    have hF : ∀ τ σ, F (l.set τ σ) = F τ >>= fun τ' => pure (l.set τ' σ) := by
      intro τ σ
      simp only [F, Lens.liftSubProbability, SubProbability.hbind_bind, SubProbability.pure_bind]
      change (f (l.set τ σ).globals).hbind _ = (f τ.globals).hbind _
      rw [globals_set_of_chain l hl]
      congr 1; funext g
      exact congrArg pure (globalL_set_set_of_chain l hl g τ σ)
    show (fun st : ProgramState =>
        (do let (x, st') ← ProgramDenotation.zoom l p st; if x = y then pure st' else ⊥ :
          SubProbability ProgramState)) * F = F * (fun st : ProgramState =>
        (do let (x, st') ← ProgramDenotation.zoom l p st; if x = y then pure st' else ⊥ :
          SubProbability ProgramState))
    rw [hk']
    funext σ
    change F σ >>= (fun σ' => k (l.get σ') >>= fun τ => pure (l.set τ σ')) =
      (k (l.get σ) >>= fun τ => pure (l.set τ σ)) >>= F
    rw [SubProbability.bind_assoc]
    simp only [SubProbability.pure_bind, hF]
    rw [← SubProbability.bind_assoc]
    have hyσ : k (l.get σ) >>= F = F (l.get σ) >>= k := congrFun hy (l.get σ)
    rw [hyσ]
    simp only [F, Lens.liftSubProbability, SubProbability.hbind_bind, SubProbability.pure_bind]
    change (f σ.globals).hbind _ = (f (l.get σ).globals).hbind _
    have h1 : (l.get σ).globals = σ.globals :=
      congrArg (fun L : Lens VariableAssignment ProgramState => L.get σ) hl
    rw [h1]
    congr 1; funext g
    rw [get_globalL_set_of_chain l hl]
    congr 1; funext τ
    rw [set_globalL_set_of_chain l hl]
  rw [ProgramDenotation.footprint, Footprint.from_updates] at hg
  exact (Set.mem_centralizer_iff.mp hg) F hgen


/-- The globals' share of a read through `l.chainGetter`. -/
theorem reduce_globalL_getter_chain_le {α : Type} (g : Getter α ProgramState) :
    Lens.reduceFootprint ProgramState.globalL
        (ProgramDenotation.get (l.chainGetter g)).footprint ≤
      Lens.reduceFootprint ProgramState.globalL (ProgramDenotation.get g).footprint := by
  rw [← ProgramDenotation.zoom_get]
  exact reduce_globalL_le_of_globalsCommute fun f hf => Footprint.GlobalsCommute.zoom l hl hf

/-- The globals' share of a write through `l.chainSetter`. -/
theorem reduce_globalL_setter_chain_le {α : Type} (x : Setter α ProgramState) :
    Lens.reduceFootprint ProgramState.globalL
        (ProgramDenotation.footprint' (ProgramDenotation.set (l.chainSetter x))) ≤
      Lens.reduceFootprint ProgramState.globalL
        (ProgramDenotation.footprint' (ProgramDenotation.set x)) := by
  refine reduce_globalL_le_of_globalsCommute fun f hf => ?_
  refine Footprint.GlobalsCommute.iSup fun v => ?_
  rw [← ProgramDenotation.zoom_set]
  exact Footprint.GlobalsCommute.zoom l hl (hf.mono (le_iSup (fun v =>
    (ProgramDenotation.set x v).footprint) v))

omit hl in
/-- `fvP`'s statement-level footprint, spelled out. -/
@[simp] theorem fvpGS_join (A B : Footprint ProgramState) :
    FVP.fvpInductiveFunctionGS.join A B = A ⊔ B := rfl

omit hl in
@[simp] theorem fvpGS_getter {α : Type} (g : Getter α ProgramState) :
    FVP.fvpInductiveFunctionGS.getter g = (ProgramDenotation.get g).footprint := rfl

omit hl in
@[simp] theorem fvpGS_setter {α : Type} (x : Setter α ProgramState) :
    FVP.fvpInductiveFunctionGS.setter x =
      ProgramDenotation.footprint' (ProgramDenotation.set x) := rfl

omit hl in
@[simp] theorem fvpGS_reduce {a b : Type 1} (L : Lens a b) (R : Footprint b) :
    FVP.fvpInductiveFunctionGS.reduce L R = Lens.reduceFootprint L R := rfl

omit hl in
@[simp] theorem fvpGS_nothing : (FVP.fvpInductiveFunctionGS.nothing : Footprint ProgramState) = ⊥ :=
  rfl

/-- **Re-targeting a statement along `l` does not add to its globals' share.** -/
theorem reduce_globalL_stmt_applyLens_le {h : HoleSigs} :
    ∀ s : StmtWithHoles h,
      Lens.reduceFootprint ProgramState.globalL
          (FVP.fvpInductiveFunctionGS.stmt (s.applyLens l)) ≤
        Lens.reduceFootprint ProgramState.globalL (FVP.fvpInductiveFunctionGS.stmt s)
  | .skip => le_rfl
  | .sample x e => by
      simp only [StmtWithHoles.applyLens, InductiveFunctionGettersSetters.stmt, fvpGS_join,
        fvpGS_getter, fvpGS_setter, Lens.reduceFootprint_sup]
      exact sup_le_sup (reduce_globalL_setter_chain_le l hl x)
        (reduce_globalL_getter_chain_le l hl e)
  | .call' x ns hl' hn b r p => by
      simp only [StmtWithHoles.applyLens, InductiveFunctionGettersSetters.stmt, fvpGS_join,
        fvpGS_getter, fvpGS_setter, Lens.reduceFootprint_sup]
      exact sup_le_sup (reduce_globalL_setter_chain_le l hl x)
        (sup_le_sup le_rfl (sup_le_sup le_rfl (reduce_globalL_getter_chain_le l hl p)))
  | .hole n x p => by
      simp only [StmtWithHoles.applyLens, InductiveFunctionGettersSetters.stmt, fvpGS_join,
        fvpGS_getter, fvpGS_setter, Lens.reduceFootprint_sup]
      exact sup_le_sup (reduce_globalL_setter_chain_le l hl x)
        (reduce_globalL_getter_chain_le l hl p)
  | .seq s t => by
      simp only [StmtWithHoles.applyLens, InductiveFunctionGettersSetters.stmt, fvpGS_join,
        Lens.reduceFootprint_sup]
      exact sup_le_sup (reduce_globalL_stmt_applyLens_le s) (reduce_globalL_stmt_applyLens_le t)
  | .ifThenElse c t e => by
      simp only [StmtWithHoles.applyLens, InductiveFunctionGettersSetters.stmt, fvpGS_join,
        fvpGS_getter, Lens.reduceFootprint_sup]
      exact sup_le_sup (reduce_globalL_getter_chain_le l hl c)
        (sup_le_sup (reduce_globalL_stmt_applyLens_le t) (reduce_globalL_stmt_applyLens_le e))
  | .while c t => by
      simp only [StmtWithHoles.applyLens, InductiveFunctionGettersSetters.stmt, fvpGS_join,
        fvpGS_getter, Lens.reduceFootprint_sup]
      exact sup_le_sup (reduce_globalL_getter_chain_le l hl c) (reduce_globalL_stmt_applyLens_le t)

omit hl in
/-- A program on the locals alone, zoomed into the program state, is outside the globals. -/
theorem footprint_zoom_localL_le {α : Type} (q : ProgramDenotation VariableAssignment α) :
    (ProgramDenotation.zoom ProgramState.localL q).footprint ≤
      (ProgramState.globalL.footprint)ᶜ := by
  have hz : ProgramDenotation.zoom ProgramState.localL q = ProgramState.localL.lift q := by
    funext σ
    simp only [ProgramDenotation.zoom, Lens.lift]
    rw [SubProbability.hbind_eq_bind]
  rw [hz]
  haveI := (inferInstance : Lens.Disjoint ProgramState.globalL ProgramState.localL).symm
  exact (ProgramDenotation.footprint_le_of_inFootprint
    (Lib.RO.Instantiate.lift_inFootprint_self _ _)).trans
    (Lens.footprint_le_compl_of_disjoint ProgramState.localL ProgramState.globalL)

omit hl in
/-- A write that changes only the locals, as a function of the locals, is outside the globals. -/
theorem footprint'_set_le_of_locals {α : Type} (y : Setter α ProgramState)
    (φ : α → VariableAssignment → VariableAssignment)
    (hy : ∀ v σ, y.set v σ = ProgramState.localL.set (φ v σ.locals) σ) :
    ProgramDenotation.footprint' (ProgramDenotation.set y) ≤
      (ProgramState.globalL.footprint)ᶜ := by
  refine iSup_le fun v => ?_
  have hz : ProgramDenotation.set y v =
      ProgramDenotation.zoom ProgramState.localL (fun loc => pure ((), φ v loc)) := by
    funext σ
    rw [ProgramDenotation.set_apply', hy]
    simp only [ProgramDenotation.zoom, SubProbability.pure_hbind]
    rfl
  rw [hz]
  exact footprint_zoom_localL_le _

omit hl in
/-- A read of a constant is nothing. -/
theorem footprint_get_const_le {α : Type} (c : α) (R : Footprint ProgramState) :
    (ProgramDenotation.get (⟨fun _ => c⟩ : Getter α ProgramState)).footprint ≤ R := by
  have hz : ProgramDenotation.get (⟨fun _ => c⟩ : Getter α ProgramState) = pure c := by
    funext σ
    rw [ProgramDenotation.get_apply']
    rfl
  rw [hz]
  exact ProgramDenotation.footprint_le_of_inFootprint (ProgramDenotation.inFootprint_pure c R)

omit hl in
/-- An assignment reads its expression as a point mass: no more than reading the expression. -/
theorem footprint_get_pure_le {α : Type} (e : Getter α ProgramState) :
    (ProgramDenotation.get (⟨fun st => pure (e.get st)⟩ :
        Getter (SubProbability α) ProgramState)).footprint ≤
      (ProgramDenotation.get e).footprint := by
  have hz : ProgramDenotation.get (⟨fun st => pure (e.get st)⟩ :
      Getter (SubProbability α) ProgramState) =
      ProgramDenotation.get e >>= fun v => pure (pure v) := by
    funext σ
    rw [ProgramDenotation.bind_apply, ProgramDenotation.get_apply', ProgramDenotation.get_apply',
      SubProbability.pure_bind]
    rfl
  rw [hz]
  refine (ProgramDenotation.footprint_bind_le _ _).trans (sup_le le_rfl (iSup_le fun v => ?_))
  exact ProgramDenotation.footprint_le_of_inFootprint (ProgramDenotation.inFootprint_pure _ _)

omit hl in
theorem reduce_globalL_le_of_le_compl {A : Footprint ProgramState}
    (h : A ≤ (ProgramState.globalL.footprint)ᶜ) (R : Footprint VariableAssignment) :
    Lens.reduceFootprint ProgramState.globalL A ≤ R :=
  ((Lens.reduceFootprint_mono _ h).trans (Lens.reduceFootprint_compl_footprint _).le).trans
    bot_le

omit hl in
theorem reduce_globalL_getter_pure_le {α : Type} (e : Getter α ProgramState) :
    Lens.reduceFootprint ProgramState.globalL
        (ProgramDenotation.get (⟨fun st => pure (e.get st)⟩ :
          Getter (SubProbability α) ProgramState)).footprint ≤
      Lens.reduceFootprint ProgramState.globalL (ProgramDenotation.get e).footprint :=
  Lens.reduceFootprint_mono _ (footprint_get_pure_le e)

open Flatten in
omit hl in
/-- **The globals' share of a substituted statement**: the statement's own, plus a bound `Q` on the
substituted procedures'. -/
theorem reduce_globalL_stmt_substHoles_le {h h' : HoleSigs}
    (q : ∀ {sig : ProcedureSignature}, HoleIndex h sig → ProcedureWithHoles h' sig)
    (Q : Footprint VariableAssignment)
    (hQ : ∀ {sig : ProcedureSignature} (n : HoleIndex h sig), FVP.fvP_proc (q n) ≤ Q) :
    ∀ s : StmtWithHoles h,
      Lens.reduceFootprint ProgramState.globalL
          (FVP.fvpInductiveFunctionGS.stmt (s.substHoles q)) ≤
        Lens.reduceFootprint ProgramState.globalL (FVP.fvpInductiveFunctionGS.stmt s) ⊔ Q
  | .skip => le_sup_left
  | .sample x e =>
      (reduce_globalL_stmt_applyLens_le trafo trafo_chain_globalL (.sample x e)).trans le_sup_left
  | .call' x ns hl' hn b r p =>
      (reduce_globalL_stmt_applyLens_le trafo trafo_chain_globalL
        (.call' x ns hl' hn b r p)).trans le_sup_left
  | .hole n x p => by
      have hq := hQ n
      simp only [FVP.fvP_proc, InductiveFunctionGettersSetters.proc, fvpGS_reduce] at hq
      simp only [StmtWithHoles.substHoles, StmtWithHoles.flattenedCall, StmtWithHoles.assign,
        InductiveFunctionGettersSetters.stmt, fvpGS_join, fvpGS_getter, fvpGS_setter,
        Lens.reduceFootprint_sup]
      refine sup_le (sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)) (sup_le ?_ (sup_le ?_ ?_))
      · exact reduce_globalL_le_of_le_compl (footprint'_set_le_of_locals _
          (fun _ loc => (VariableAssignment.embed tag tag_injective).set VariableAssignment.init loc)
          (fun v σ => by cases v; rw [emb_chainSetter_resetSetter_univ_set]; rfl)) _
      · exact reduce_globalL_le_of_le_compl (footprint_get_const_le _ _) _
      · exact reduce_globalL_le_of_le_compl (footprint'_set_le_of_locals _
          (fun a loc => (VariableAssignment.embed tag tag_injective).set
            (VariableAssignment.setParams _ _ (q n).parameterNames_length a
              VariableAssignment.init) loc)
          (fun _ _ => rfl)) _
      · exact ((reduce_globalL_getter_chain_le trafo trafo_chain_globalL
          (⟨fun st => pure (p.get st)⟩ : Getter (SubProbability _) ProgramState)).trans
          ((reduce_globalL_getter_pure_le p).trans le_sup_right)).trans le_sup_left
      · exact ((reduce_globalL_stmt_applyLens_le emb emb_chain_globalL _).trans
          (le_sup_left.trans hq)).trans le_sup_right
      · exact ((reduce_globalL_setter_chain_le trafo trafo_chain_globalL x).trans
          le_sup_left).trans le_sup_left
      · exact ((reduce_globalL_getter_chain_le emb emb_chain_globalL
          (⟨fun st => pure ((q n).return_val.get st)⟩ : Getter (SubProbability _) ProgramState)).trans
          ((reduce_globalL_getter_pure_le _).trans (le_sup_right.trans hq))).trans le_sup_right
  | .seq s t => by
      simp only [StmtWithHoles.substHoles, InductiveFunctionGettersSetters.stmt, fvpGS_join,
        Lens.reduceFootprint_sup]
      exact sup_le ((reduce_globalL_stmt_substHoles_le q Q hQ s).trans
          (sup_le_sup_right le_sup_left _))
        ((reduce_globalL_stmt_substHoles_le q Q hQ t).trans (sup_le_sup_right le_sup_right _))
  | .ifThenElse c t e => by
      simp only [StmtWithHoles.substHoles, InductiveFunctionGettersSetters.stmt, fvpGS_join,
        fvpGS_getter, Lens.reduceFootprint_sup]
      refine sup_le ((reduce_globalL_getter_chain_le trafo trafo_chain_globalL c).trans
        (le_sup_left.trans le_sup_left)) (sup_le ?_ ?_)
      · exact (reduce_globalL_stmt_substHoles_le q Q hQ t).trans
          (sup_le_sup_right (le_sup_left.trans le_sup_right) _)
      · exact (reduce_globalL_stmt_substHoles_le q Q hQ e).trans
          (sup_le_sup_right (le_sup_right.trans le_sup_right) _)
  | .while c t => by
      simp only [StmtWithHoles.substHoles, InductiveFunctionGettersSetters.stmt, fvpGS_join,
        fvpGS_getter, Lens.reduceFootprint_sup]
      exact sup_le ((reduce_globalL_getter_chain_le trafo trafo_chain_globalL c).trans
        (le_sup_left.trans le_sup_left))
        ((reduce_globalL_stmt_substHoles_le q Q hQ t).trans (sup_le_sup_right le_sup_right _))

open Flatten in
omit hl in
/-- **The footprint of a substituted procedure**: the procedure's own, plus a bound on the
substituted procedures'. -/
theorem FVP.fvP_proc_substHoles_le {h h' : HoleSigs} {sig : ProcedureSignature}
    (p : ProcedureWithHoles h sig)
    (q : ∀ {sig : ProcedureSignature}, HoleIndex h sig → ProcedureWithHoles h' sig)
    (Q : Footprint VariableAssignment)
    (hQ : ∀ {sig : ProcedureSignature} (n : HoleIndex h sig), FVP.fvP_proc (q n) ≤ Q) :
    FVP.fvP_proc (p.substHoles q) ≤ FVP.fvP_proc p ⊔ Q := by
  simp only [FVP.fvP_proc, InductiveFunctionGettersSetters.proc, fvpGS_reduce,
    ProcedureWithHoles.substHoles]
  refine sup_le ((reduce_globalL_stmt_substHoles_le q Q hQ p.body).trans
    (sup_le_sup_right le_sup_left _)) ?_
  exact (reduce_globalL_getter_chain_le trafo trafo_chain_globalL p.return_val).trans
    (le_sup_right.trans le_sup_left)

end SubstFootprint

end GaudisCrypt
