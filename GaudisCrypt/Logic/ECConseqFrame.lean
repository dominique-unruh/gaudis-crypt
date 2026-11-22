import GaudisCrypt.Logic.StmtSwap
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.HoareFrame
import GaudisCrypt.Logic.FrameTactics
import GaudisCrypt.Logic.Granular
import GaudisCrypt.Logic.ModuleFootprint
import GaudisCrypt.Logic.Fel
import GaudisCrypt.Logic.ECCallAbstract

/-!
# EasyCrypt's `conseq` keeps what the code does not modify

EC's `conseq (_: P' ==> Q')` on `c₁ ~ c₂ : P ==> Q` asks `P => P'` and
`forall &1 &2, P => forall (modified variables), Q' => Q`: the variables the code does not write
keep their values from the precondition.  Here that is a frame on each side
(`prhlStmt_conseq_frame`): the variables `Q` reads whose writes the code commutes with
(`Stmt.CommutesWith`, shown as for `stmt_swap`; such code keeps them, `Stmt.satisfies_keep`)
keep their values from the start, and the side goal is
`∀ σ₁ σ₂, P σ₁ σ₂ → ∀ τ₁ τ₂, (frames) → Q' τ₁ τ₂ → Q τ₁ τ₂`.  `equiv_conseq (: P ==> Q)` on
statements is this rule (`Logic/ECConseq.lean`).
-/

namespace GaudisCrypt

open GaudisCrypt.Lib.RO.Instantiate

open Classical in
/-- **A statement that commutes with every write to `x` keeps `x`**. -/
theorem Stmt.satisfies_keep {α : Type} (x : Lens α ProgramState) {s : Stmt}
    (h : ∀ v, s.CommutesWith (x.set v)) (σ : ProgramState) :
    (programDenotation s σ).satisfies fun r => x.get r.2 = x.get σ := by
  have hk : hoareStmt (fun τ => τ = σ) s (fun τ => x.get τ = x.get σ) := by
    rw [hoareStmt_iff_wp]
    intro τ hτ
    rw [hτ]
    have key : s.ewp (fun ρ => if x.get ρ = x.get σ then 0 else 1) σ = 0 := by
      have hc := h (x.get σ) (fun ρ => if x.get ρ = x.get σ then 0 else 1) σ
      rw [x.get_set] at hc
      rw [hc]
      simp only [x.set_get, if_true]
      exact le_antisymm (Stmt.ewp_const_le s 0 σ) bot_le
    rw [← key]
    simp only [Stmt.ewp]
    congr 1
    funext r
    by_cases hr : x.get r.2 = x.get σ <;> simp [Set.indicator, hr]
  exact hk.satisfies rfl

/-- `s` keeps `x`: every run ends with `x` as it started. -/
def Stmt.Keeps {α : Type} (x : Lens α ProgramState) (s : Stmt) : Prop :=
  ∀ c, hoareStmt (fun τ => x.get τ = c) s (fun τ => x.get τ = c)

namespace Stmt.Keeps

variable {α : Type} {x : Lens α ProgramState}

theorem satisfies {s : Stmt} (h : Stmt.Keeps x s) (σ : ProgramState) :
    (programDenotation s σ).satisfies fun r => x.get r.2 = x.get σ :=
  (h (x.get σ)).satisfies rfl

theorem «skip» : Stmt.Keeps x StmtWithHoles.skip := fun _ => hoare_skip_of_imp fun _ h => h

theorem seq {p q : Stmt} (hp : Stmt.Keeps x p) (hq : Stmt.Keeps x q) :
    Stmt.Keeps x (.seq p q) := fun c => hoare_seq (hq c) (hp c)

theorem ite {b : Getter Bool ProgramState} {p q : Stmt} (hp : Stmt.Keeps x p)
    (hq : Stmt.Keeps x q) : Stmt.Keeps x (.ifThenElse b p q) := fun c =>
  hoare_pre (hoare_if_wp (hp c) (hq c)) fun _ h => ⟨fun _ => h, fun _ => h⟩

theorem «while» {b : Getter Bool ProgramState} {body : Stmt} (h : Stmt.Keeps x body) :
    Stmt.Keeps x (.while b body) := fun c =>
  hoare_while _ (hoare_pre (h c) fun _ h => h.1) fun _ h _ => h

theorem assign {β : Type} {y : Setter β ProgramState} {e : Getter β ProgramState}
    (hy : ∀ v σ, x.get (y.set v σ) = x.get σ) : Stmt.Keeps x (.assign y e) := fun _ =>
  hoare_pre (hoare_assign_wp y e _) fun σ h => (hy _ σ).trans h

theorem sample {β : Type} {y : Setter β ProgramState} {e : Getter (SubProbability β) ProgramState}
    (hy : ∀ v σ, x.get (y.set v σ) = x.get σ) : Stmt.Keeps x (.sample y e) := fun _ =>
  hoare_pre (hoare_sample_wp y _) fun σ h a _ => (hy a σ).trans h

/-- A call keeps what neither its result nor the globals it leaves hold (a local other than the
result). -/
theorem «call» {sig : ProcedureSignature} {y : Setter sig.ret ProgramState} {p : Procedure sig}
    {args : Getter sig.ParamType ProgramState}
    (hy : ∀ r g σ, x.get (y.set r (ProgramState.globalL.set g σ)) = x.get σ) :
    Stmt.Keeps x (Stmt.call y p args) := fun _ =>
  hoare_pre (hoare_call_wp y p args (hoareProc_const p True) _) fun σ h =>
    ⟨trivial, fun r g _ => (hy r g σ).trans h⟩

/-- A call keeps a global `L` outside the callee's footprint. -/
theorem call_frame {sig : ProcedureSignature} {y : Setter sig.ret ProgramState}
    {p : Procedure sig} {args : Getter sig.ParamType ProgramState} {γ : Type}
    (L : Lens γ VariableAssignment)
    (hp : ∀ a, (procedureDenotation p a).inFootprint (L.footprint)ᶜ)
    (hy : ∀ r g σ, L.get g = L.get σ.globals →
      x.get (y.set r (ProgramState.globalL.set g σ)) = x.get σ) :
    Stmt.Keeps x (Stmt.call y p args) := fun _ =>
  hoare_pre (hoare_call_frame L hp) fun σ h r g hg => (hy r g σ hg).trans h

/-- A call keeps a global `L` outside the callee's footprint, its result written elsewhere. -/
theorem call_global {sig : ProcedureSignature} {y : Setter sig.ret ProgramState}
    {p : Procedure sig} {args : Getter sig.ParamType ProgramState} {γ : Type}
    (L : Lens γ VariableAssignment)
    (hp : ∀ a, (procedureDenotation p a).inFootprint (L.footprint)ᶜ)
    (hy : ∀ r σ, L.get (y.set r σ).globals = L.get σ.globals) :
    Stmt.Keeps L.intoGlobal (Stmt.call y p args) :=
  call_frame L hp fun r g σ hg => by
    rw [Lens.intoGlobal_get_eq, Lens.intoGlobal_get_eq, hy]
    exact hg

/-- A call keeps a global `L` that every write of the callee keeps (EC's frame by writes: a callee
that reads `L`, or whose module touches it elsewhere, without writing it), its result written
elsewhere. -/
theorem call_writes {sig : ProcedureSignature} {y : Setter sig.ret ProgramState}
    {p : Procedure sig} {args : Getter sig.ParamType ProgramState} {γ : Type}
    (L : Lens γ VariableAssignment) (hp : StmtWithHoles.WritesKeep L.get p.body)
    (hy : ∀ r σ, L.get (y.set r σ).globals = L.get σ.globals) :
    Stmt.Keeps L.intoGlobal (Stmt.call y p args) := fun c =>
  hoare_pre (hoare_call_wp y p args (hoareProc_of_writesKeep L.get p hp c) _) fun σ h =>
    ⟨by rw [Lens.intoGlobal_get_eq] at h; exact h, fun r g hg => by
      rw [Lens.intoGlobal_get_eq, hy]
      exact hg⟩

/-- A call of a declared module `D` on oracles `O` keeps a global `L` outside `D` that every write
of every oracle procedure keeps (EC's frame by writes through an abstract call: the adversary
does not touch `L`, its oracles read it at most), its result written elsewhere. -/
theorem call_app_writes {T : Type 1} [IsModule T] {sig : ProcedureSignature} {holes : HoleSigs}
    (D : Module.Arr T (Module.Proc sig)) (ext : T → holes.Instantiation)
    (hD : Module.Representable D ext) {γ : Type} (L : Lens γ VariableAssignment)
    (hdisj : FVP.fvP D ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (O : T)
    (hO : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      StmtWithHoles.WritesKeep L.get ((ext O).lookup n).body)
    {y : Setter sig.ret ProgramState} {args : Getter sig.ParamType ProgramState}
    (hy : ∀ r σ, L.get (y.set r σ).globals = L.get σ.globals) :
    Stmt.Keeps L.intoGlobal (Stmt.call y (Module.app D O).procedure args) := fun c =>
  hoare_pre (hoare_call_wp y _ args
      (Module.hoare_app_inv (L := L) D ext hD hdisj hc O (fun v => v = c)
        fun n => hoareProc_of_writesKeep L.get _ (hO n) c) _) fun σ h =>
    ⟨by rw [Lens.intoGlobal_get_eq] at h; exact h, fun r g hg => by
      rw [Lens.intoGlobal_get_eq, hy]
      exact hg⟩

end Stmt.Keeps

/-- `s` keeps the region `F` of the globals (EC's `glob A`, `F = fvP A`): every run ends with
the same `F.touched_getter` of the globals as it started. -/
def Stmt.KeepsRegion (F : Footprint VariableAssignment) (s : Stmt) : Prop :=
  ∀ c, hoareStmt (fun τ => F.touched_getter.get τ.globals = c) s
    (fun τ => F.touched_getter.get τ.globals = c)

namespace Stmt.KeepsRegion

variable {F : Footprint VariableAssignment}

theorem satisfies {s : Stmt} (h : Stmt.KeepsRegion F s) (σ : ProgramState) :
    (programDenotation s σ).satisfies fun r =>
      F.touched_getter.get r.2.globals = F.touched_getter.get σ.globals :=
  (h (F.touched_getter.get σ.globals)).satisfies rfl

theorem «skip» : Stmt.KeepsRegion F StmtWithHoles.skip := fun _ => hoare_skip_of_imp fun _ h => h

theorem seq {p q : Stmt} (hp : Stmt.KeepsRegion F p) (hq : Stmt.KeepsRegion F q) :
    Stmt.KeepsRegion F (.seq p q) := fun c => hoare_seq (hq c) (hp c)

theorem ite {b : Getter Bool ProgramState} {p q : Stmt} (hp : Stmt.KeepsRegion F p)
    (hq : Stmt.KeepsRegion F q) : Stmt.KeepsRegion F (.ifThenElse b p q) := fun c =>
  hoare_pre (hoare_if_wp (hp c) (hq c)) fun _ h => ⟨fun _ => h, fun _ => h⟩

theorem «while» {b : Getter Bool ProgramState} {body : Stmt} (h : Stmt.KeepsRegion F body) :
    Stmt.KeepsRegion F (.while b body) := fun c =>
  hoare_while _ (hoare_pre (h c) fun _ h => h.1) fun _ h _ => h

theorem assign {β : Type} {y : Setter β ProgramState} {e : Getter β ProgramState}
    (hy : ∀ v σ, F.touched_getter.get (y.set v σ).globals = F.touched_getter.get σ.globals) :
    Stmt.KeepsRegion F (.assign y e) := fun _ =>
  hoare_pre (hoare_assign_wp y e _) fun σ h => (hy _ σ).trans h

theorem sample {β : Type} {y : Setter β ProgramState} {e : Getter (SubProbability β) ProgramState}
    (hy : ∀ v σ, F.touched_getter.get (y.set v σ).globals = F.touched_getter.get σ.globals) :
    Stmt.KeepsRegion F (.sample y e) := fun _ =>
  hoare_pre (hoare_sample_wp y _) fun σ h a _ => (hy a σ).trans h

/-- A call of a module's procedure staying out of `F.glob` keeps `F` (EC's `glob A` across a call
of a concrete procedure outside `A`), its result written where `F` does not look. -/
theorem «call» {sig : ProcedureSignature} {y : Setter sig.ret ProgramState} {M : Module.Proc sig}
    {args : Getter sig.ParamType ProgramState} (hF : F.FinitelySupported)
    (hM : FVP.fvP M ≤ F.globᶜ)
    (hy : ∀ r σ, F.touched_getter.get (y.set r σ).globals = F.touched_getter.get σ.globals) :
    Stmt.KeepsRegion F (Stmt.call y M.procedure args) := by
  obtain ⟨L, hL⟩ := hF.glob_fromLens
  have hp : ∀ a, (procedureDenotation M.procedure a).inFootprint (L.footprint)ᶜ := fun a =>
    ProgramDenotation.inFootprint_mono (Module.Proc.inFootprint_fvP M a) (hL ▸ hM)
  intro c
  refine hoare_pre (hoare_call_frame L hp) fun σ h r g hg => ?_
  rw [hy, globals_globalL_set, ← h]
  exact Footprint.touched_getter_eq_of_le (hL ▸ Footprint.le_glob F)
    ((Lens.footprint_touched_getter_eq_iff L _ _).mpr hg)

end Stmt.KeepsRegion

theorem SubProbability.satisfies_and' {γ : Type*} {μ : SubProbability γ} {P Q : γ → Prop}
    (hP : μ.satisfies P) (hQ : μ.satisfies Q) : μ.satisfies fun x => P x ∧ Q x :=
  fun x hx => ⟨hP x hx, hQ x hx⟩

theorem SubProbability.satisfies_true' {γ : Type*} (μ : SubProbability γ) :
    μ.satisfies fun _ => True :=
  fun _ _ => trivial

/-- **EC's `conseq`, with frames**: `F₁`, `F₂` relate each side's state at the start to its
state at the end (what its code keeps). -/
theorem prhlStmt_conseq_frame {A A' B B' : ProgramState → ProgramState → Prop} {c₁ c₂ : Stmt}
    (F₁ F₂ : ProgramState → ProgramState → Prop)
    (hF₁ : ∀ σ, (programDenotation c₁ σ).satisfies fun r => F₁ σ r.2)
    (hF₂ : ∀ σ, (programDenotation c₂ σ).satisfies fun r => F₂ σ r.2)
    (h : prhlStmt A' c₁ c₂ B') (hA : ∀ σ₁ σ₂, A σ₁ σ₂ → A' σ₁ σ₂)
    (hB : ∀ σ₁ σ₂, A σ₁ σ₂ → ∀ τ₁ τ₂, F₁ σ₁ τ₁ → F₂ σ₂ τ₂ → B' τ₁ τ₂ → B τ₁ τ₂) :
    prhlStmt A c₁ c₂ B := by
  intro σ₁ σ₂ hAσ
  obtain ⟨μ, m1, m2, sat⟩ := h σ₁ σ₂ (hA _ _ hAσ)
  have h1 : μ.satisfies fun w => F₁ σ₁ w.1.2 :=
    coupling_satisfies_fst (B := fun r : Unit × ProgramState => F₁ σ₁ r.2) (by rw [m1]; exact hF₁ σ₁)
  have h2 : μ.satisfies fun w => F₂ σ₂ w.2.2 :=
    coupling_satisfies_snd (B := fun r : Unit × ProgramState => F₂ σ₂ r.2) (by rw [m2]; exact hF₂ σ₂)
  exact ⟨μ, m1, m2, fun w hw => hB σ₁ σ₂ hAσ _ _ (h1 w hw) (h2 w hw) (sat w hw)⟩

/-- A Hoare triple from what holds on every outcome (the converse of `hoareStmt.satisfies`). -/
theorem hoareStmt_of_satisfies {A B : ProgramState → Prop} {s : Stmt}
    (h : ∀ σ, A σ → (programDenotation s σ).satisfies fun u => B u.2) : hoareStmt A s B :=
  hoareStmt_of_wp fun σ hσ =>
    SubProbability.expected_eq_zero_of_support fun a ha => by
      have hB : B a.2 := h σ hσ a fun h0 => ha (by
        show (programDenotation s σ).ofEvent {a} = 0
        simp [SubProbability.ofEvent, h0])
      simp [Set.indicator, hB]

/-- **EC's `conseq` on a Hoare triple, with the frame**: `F` relates the state at the start to
the state at the end (what the code keeps). -/
theorem hoareStmt_conseq_frame {A A' B B' : ProgramState → Prop} {c : Stmt}
    (F : ProgramState → ProgramState → Prop)
    (hF : ∀ σ, (programDenotation c σ).satisfies fun r => F σ r.2)
    (h : hoareStmt A' c B') (hA : ∀ σ, A σ → A' σ)
    (hB : ∀ σ, A σ → ∀ τ, F σ τ → B' τ → B τ) : hoareStmt A c B :=
  hoareStmt_of_satisfies fun σ hσ u hu =>
    hB σ hσ u.2 (hF σ u hu) (hoareStmt.satisfies h (hA σ hσ) u hu)

/-- **EC's `while I`** on a Hoare triple whose code ends with a loop: the body keeps `I`, and
the code before establishes `I` and, for every final state `τ` of the loop that its frame `F`
allows (what the loop keeps), `I` and a false guard give the postcondition. -/
theorem hoareStmt_seq_while_ec {A Q I : ProgramState → Prop} {s body : Stmt}
    {c : Getter Bool ProgramState} (F : ProgramState → ProgramState → Prop)
    (hF : ∀ σ, (programDenotation (.while c body) σ).satisfies fun r => F σ r.2)
    (hb : hoareStmt (fun σ => I σ ∧ c.get σ = true) body I)
    (hpre : hoareStmt A s fun σ => I σ ∧ ∀ τ, F σ τ → I τ → c.get τ = false → Q τ) :
    hoareStmt A (.seq s (.while c body)) Q := by
  refine hoare_seq ?_ hpre
  refine hoareStmt_conseq_frame F hF
    (hoare_while I (B := fun σ => I σ ∧ c.get σ = false) hb fun σ hI hc => ⟨hI, hc⟩)
    (fun _ h => h.1) ?_
  rintro σ ⟨-, hK⟩ τ hf ⟨hI, hc⟩
  exact hK τ hf hI hc

namespace ECConseqFrame

open Lean Meta Elab Tactic

/-- `Stmt.Keeps.call_app_writes` for `goal` (`Stmt.Keeps L.intoGlobal s`, `s` a call of a declared
module `D` on oracles `O`): `D`'s representation from its declaration and the oracles' module
type's `T.ext` (else its canonical one, as `equiv_call`'s), `D` outside `L` (`fp_disjoint`), the
oracles' arguments countable, every write of every oracle procedure keeping `L`
(`ECCallEquiv.writesKeepProof`), the result elsewhere (`StmtSwap.discharge`). -/
def callAppWrites (goal s L : Lean.Expr) : MetaM Lean.Expr := do
  let p ← whnfR (s.getArg! (s.getAppNumArgs - 2))
  unless p.isAppOfArity ``Module.Proc.procedure 2 do throwError "keeps: the callee"
  let M := p.getArg! 1
  unless M.isAppOfArity ``Module.app 6 do throwError "keeps: not an applied module"
  let D := M.getArg! 4
  let O := M.getArg! 5
  let T₀ ← inferType O
  let T ← whnfR T₀
  -- the oracles' procedures, in the order of the holes, as the canonical `ext` gives them
  -- (`Module.fst O`, …), and the simp lemmas that take them apart (`Module.fst_pair`, the module
  -- types' records' `T.f.mk_simp`)
  let comps ← ECCall.components T₀ O (literal := false)
  let procs ← comps.flatMapM fun (C, X) => ECCall.procsOf C X
  let env ← getEnv
  let mut simps : Array Ident := #[mkIdent ``Module.fst_pair, mkIdent ``Module.snd_pair]
  for (C, _) in comps do
    let some c := C.getAppFn.constName? | continue
    if isStructure env (c ++ `Structure) then
      for f in getStructureFields env (c ++ `Structure) do
        let n := c ++ f ++ `mk_simp
        if env.contains n && !simps.contains (mkIdent n) then simps := simps.push (mkIdent n)
  let m ← mkFreshExprMVar goal
  let log ← Core.getMessageLog
  -- only this proof's messages (errors logged earlier in the file are not its own)
  Core.resetMessageLog
  try
    let rest ← Elab.Term.TermElabM.run' <| Elab.Term.withoutErrToSorry <|
      Elab.Tactic.run m.mvarId! do
        let Ds ← Elab.Term.exprToSyntax D
        let Os ← Elab.Term.exprToSyntax O
        let Ls ← Elab.Term.exprToSyntax L
        let TS ← Elab.Term.exprToSyntax T₀
        -- the oracles' module type's `T.ext`, else its canonical one
        let extC := (T.getAppFn.constName?.getD .anonymous) ++ `ext
        let exts ← if (← getEnv).contains extC then
            Elab.Term.exprToSyntax (mkAppN (← mkConstWithFreshMVarLevels extC) T.getAppArgs)
          else `(fun O => (Module.moduleTypeRep $TS).extOf (Module.cast $TS O))
        evalTactic (← `(tactic| refine Stmt.Keeps.call_app_writes $Ds $exts
          (Module.Declared.ecModule $Ds $exts).representable $Ls ?hdisj ?hc $Os ?hO ?hy))
        for g in ← getGoals do g.setTag (← g.getTag).eraseMacroScopes
        let take (n : Name) : TacticM MVarId := do
          let gs ← getGoals
          let some g ← gs.findM? fun g => return (← g.getTag) == n
            | throwError "keeps: no goal `{n}`"
          setGoals (gs.filter (· != g))
          return g
        let gd ← take `hdisj
        -- within a budget: where it holds, `fp_disjoint` takes a tenth of a second; where the
        -- adversary does touch the variable, it took up to 19 s to fail (`SHA3OSecurity`)
        let [] ← tryCatchRuntimeEx
            (withCurrHeartbeats <|
              withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000 * 1000 }) do
                evalTacticAt (← `(tactic| ((try simp only [Footprint.lens_pair]); fp_disjoint)))
                  gd)
            (fun _ => throwError "keeps: the adversary touches the variable")
          | throwError "keeps: the adversary touches the variable"
        let gc ← take `hc
        for g in ← ECCall.splitHoles gc procs.size do
          let [] ← evalTacticAt (← `(tactic| first
            | infer_instance
            | (dsimp only [ProcedureSignature.ParamType, typeListToTuple]; infer_instance))) g
            | throwError "keeps: an oracle's arguments"
        -- each oracle's writes, its procedure for the instantiation's lookup
        let go ← take `hO
        let os ← ECCall.splitHoles go procs.size
        let mut left := []
        for (g, pr) in os.zip procs.toList do
          let g' ← g.withContext do
            let ty ← instantiateMVars (← g.getType)
            g.change (ty.replace fun e =>
              if e.isAppOf ``HoleSigs.Instantiation.lookup then some pr else none)
          let gs ← evalTacticAt (← `(tactic| try simp only [$[$simps:ident],*])) g'
          left := left ++ gs
        setGoals ((← getGoals) ++ left)
    -- the oracles' writes, and the result's
    for g in rest do
      let t ← instantiateMVars (← g.getType)
      if t.isAppOf ``StmtWithHoles.WritesKeep then g.assign (← ECCallEquiv.writesKeepProof t)
      else g.assign (← StmtSwap.discharge t none)
    if (← Core.getMessageLog).hasErrors then throwError "keeps: the abstract call"
    let pf ← instantiateMVars m
    if pf.hasExprMVar || pf.hasSyntheticSorry || pf.hasSorry then
      throwError "keeps: the abstract call"
    return pf
  finally
    Core.setMessageLog log

/-- A proof of `Stmt.Keeps x s`, by the statement's syntax: writes to other variables (the side
equations by `StmtSwap.discharge`), calls keeping the caller's other locals, a global outside
the callee's footprint (`fp_disjoint`), or a global no write of the callee's body touches (EC's
frame by writes, `ECCallEquiv.writesKeepProof`). -/
partial def keepsOf (s x : Lean.Expr) : MetaM Lean.Expr := do
  let s ← TacticMisc.openStmt (← instantiateMVars s)
  let goal ← mkAppM ``Stmt.Keeps #[x, s]
  let byRule (lem : Name) (extra : Array (Name × Lean.Expr) := #[]) : MetaM Lean.Expr := do
    let c ← mkConstWithFreshMVarLevels lem
    let cTy ← inferType c
    let names := cTy.getForallBinderNames
    let (ms, _, concl) ← forallMetaTelescope cTy
    for (n, v) in extra do
      let some i := names.findIdx? (· == n) | throwError "keeps: no `{n}` in `{lem}`"
      unless ← isDefEq ms[i]! v do throwError "keeps: `{n}`"
    unless ← isDefEq concl goal do throwError "keeps: `{lem}` does not apply"
    for m in ms do
      if ← m.mvarId!.isAssigned then continue
      let t ← instantiateMVars (← inferType m)
      unless ← isProp t do continue
      let pf ← if t.isAppOf ``Stmt.Keeps then keepsOf t.appArg! x
        else if (← forallTelescope t fun _ b =>
            pure (b.isAppOf ``ProgramDenotation.inFootprint)) then do
          -- `∀ a, inFootprint (L.footprint)ᶜ` from the callee's `fvP` and `fp_disjoint`
          forallTelescope t fun as b => do
            let_expr ProgramDenotation.inFootprint _ _ den R := b
              | throwError "keeps: footprint"
            let p ← whnfR (den.getArg! 1)
            unless p.isAppOfArity ``Module.Proc.procedure 2 do throwError "keeps: callee"
            let hM ← mkAppM ``Module.Proc.inFootprint_fvP #[p.getArg! 1, as[0]!]
            let le ← mkFreshExprMVar
              (← mkAppM ``LE.le #[← mkAppM ``FVP.fvP #[p.getArg! 1], R])
            FootprintSolver.solve le.mvarId!
            mkLambdaFVars as (← mkAppM ``ProgramDenotation.inFootprint_mono #[hM, le])
        else if t.isAppOf ``StmtWithHoles.WritesKeep then ECCallEquiv.writesKeepProof t
        else StmtSwap.discharge t none
      unless ← isDefEq m pf do throwError "keeps: cannot use the proof of{indentExpr t}"
    instantiateMVars (mkAppN c ms)
  match s.getAppFn.constName? with
  | some ``StmtWithHoles.skip => byRule ``Stmt.Keeps.«skip»
  | some ``StmtWithHoles.seq => byRule ``Stmt.Keeps.seq
  | some ``StmtWithHoles.ifThenElse => byRule ``Stmt.Keeps.ite
  | some ``StmtWithHoles.while => byRule ``Stmt.Keeps.«while»
  | some ``StmtWithHoles.assign => byRule ``Stmt.Keeps.assign
  | some ``StmtWithHoles.sample => byRule ``Stmt.Keeps.sample
  | some ``StmtWithHoles.call | some ``Stmt.call | some ``StmtWithHoles.call' =>
    try byRule ``Stmt.Keeps.«call»
    catch _ =>
      -- a global `L.intoGlobal`, outside the callee
      unless x.isAppOfArity ``Lens.intoGlobal 2 do throwError "keeps: the call"
      try byRule ``Stmt.Keeps.call_global #[(`L, x.appArg!)]
      catch _ =>
        -- EC's frame by writes: the callee does not write it
        unless ec.frameWrites.get (← getOptions) do throwError "keeps: the call"
        try byRule ``Stmt.Keeps.call_writes #[(`L, x.appArg!)]
        catch _ =>
          -- … through a call of a declared module on oracles that do not write it
          callAppWrites goal s x.appArg!
  | _ => throwError "keeps: no rule for{indentExpr s}"

/-- A write keeps the region: `∀ v σ, F.touched_getter.get (y.set v σ).globals = …` — a local
(the globals unchanged) or a global outside `F` (`touched_set_of_le_compl`, `fp_disjoint`). -/
def dischargeRegionWrite (ty : Lean.Expr) : MetaM Lean.Expr := do
  let m ← mkFreshExprMVar ty
  let log ← Core.getMessageLog
  -- only this proof's messages (errors logged earlier in the file are not its own)
  Core.resetMessageLog
  try
    let gs ← Elab.Term.TermElabM.run' <| Elab.Term.withoutErrToSorry <|
      Elab.Tactic.run m.mvarId! do
        Elab.Tactic.evalTactic (← `(tactic| (
          intro v σ
          simp only [liftLens, LiftLens.lift, Lens.pair, localVarLens, globals_intoLocal_set,
            globals_intoGlobal_set, globals_resetSetter_set, globals_globalL_set,
            Setter.throwaway_set]
          repeat (rw [GaudisCrypt.touched_set_of_le_compl ?_]; rotate_left; fp_disjoint)
          done)))
    unless gs.isEmpty do throwError "keeps region: a write"
    if (← Core.getMessageLog).hasErrors then throwError "keeps region: a write"
    let pf ← instantiateMVars m
    if pf.hasSyntheticSorry || pf.hasSorry then throwError "keeps region: a write"
    return pf
  finally
    Core.setMessageLog log

/-- A proof of the proposition `ty` by the tactic `tac` (no goal left, no error, no `sorry`). -/
def byTactic (ty : Lean.Expr) (tac : TSyntax `tactic) : MetaM Lean.Expr := do
  let m ← mkFreshExprMVar ty
  let log ← Core.getMessageLog
  -- only this proof's messages (errors logged earlier in the file are not its own)
  Core.resetMessageLog
  try
    let gs ← Elab.Term.TermElabM.run' <| Elab.Term.withoutErrToSorry <|
      Elab.Tactic.run m.mvarId! (Elab.Tactic.evalTactic tac)
    unless gs.isEmpty do throwError "keeps region: {ty}"
    if (← Core.getMessageLog).hasErrors then throwError "keeps region: {ty}"
    let pf ← instantiateMVars m
    if pf.hasSyntheticSorry || pf.hasSorry then throwError "keeps region: {ty}"
    return pf
  finally
    Core.setMessageLog log

/-- A proof of `Stmt.KeepsRegion F s`, by the statement's syntax (calls of modules' procedures
outside `F.glob`: `Stmt.KeepsRegion.call`). -/
partial def keepsRegionOf (s F : Lean.Expr) : MetaM Lean.Expr := do
  let s ← TacticMisc.openStmt (← instantiateMVars s)
  let goal ← mkAppM ``Stmt.KeepsRegion #[F, s]
  let byRule (lem : Name) : MetaM Lean.Expr := do
    let c ← mkConstWithFreshMVarLevels lem
    let (ms, _, concl) ← forallMetaTelescope (← inferType c)
    unless ← isDefEq concl goal do throwError "keeps region: `{lem}` does not apply"
    for m in ms do
      if ← m.mvarId!.isAssigned then continue
      let t ← instantiateMVars (← inferType m)
      unless ← isProp t do continue
      let pf ← if t.isAppOf ``Stmt.KeepsRegion then keepsRegionOf t.appArg! F
        else if t.isAppOf ``Footprint.FinitelySupported then byTactic t (← `(tactic| fp_finite))
        else if t.isAppOf ``LE.le then byTactic t (← `(tactic| fp_disjoint))
        else dischargeRegionWrite t
      unless ← isDefEq m pf do throwError "keeps region: cannot use the proof of{indentExpr t}"
    instantiateMVars (mkAppN c ms)
  match s.getAppFn.constName? with
  | some ``StmtWithHoles.skip => byRule ``Stmt.KeepsRegion.«skip»
  | some ``StmtWithHoles.seq => byRule ``Stmt.KeepsRegion.seq
  | some ``StmtWithHoles.ifThenElse => byRule ``Stmt.KeepsRegion.ite
  | some ``StmtWithHoles.while => byRule ``Stmt.KeepsRegion.«while»
  | some ``StmtWithHoles.assign => byRule ``Stmt.KeepsRegion.assign
  | some ``StmtWithHoles.sample => byRule ``Stmt.KeepsRegion.sample
  | some ``StmtWithHoles.call | some ``Stmt.call | some ``StmtWithHoles.call' =>
    byRule ``Stmt.KeepsRegion.«call»
  | _ => throwError "keeps region: no rule for{indentExpr s}"

/-- The regions `F` whose `F.touched_getter` the conditions `es` read (EC's `glob A`). -/
def regionsOf (es : Array Lean.Expr) : MetaM (Array Lean.Expr) := do
  let out ← IO.mkRef (#[] : Array Lean.Expr)
  for e in es do
    Meta.forEachExpr (← instantiateMVars e) fun t => do
      if t.isAppOfArity ``Footprint.touched_getter 2 && !t.hasLooseBVars then
        let F := t.appArg!
        unless (← out.get).contains F do out.modify (·.push F)
  out.get

/-- The frame of the statement `s` for the variables `xs` (lenses of the program state): those
it keeps (`keepsOf`), as `fun σ τ => x.get τ = x.get σ ∧ …`, and the proof of
`∀ σ, (programDenotation s σ).satisfies fun r => F σ r.2`. -/
def frameOf (s : Lean.Expr) (xs : Array Lean.Expr) (regions : Array Lean.Expr := #[]) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let ps := mkConst ``ProgramState
  -- the `let`s of the locals by their values (the same statement, by `zeta`)
  let s ← Meta.transform (← instantiateMVars s) (pre := fun e => do
    if let .letE _ _ v b _ := e then return .visit (b.instantiate1 v)
    return .continue)
  let mut kept : Array (Lean.Expr × Lean.Expr) := #[]
  for x in xs do
    let s' ← saveState
    try
      let pf ← keepsOf s x
      unless (← isTypeCorrect pf) do throwError "frame"
      kept := kept.push (x, pf)
      trace[ec.frame] "kept: {x}"
    catch e =>
      s'.restore
      trace[ec.frame] "not kept: {x}\n{e.toMessageData}"
  let mut keptR : Array (Lean.Expr × Lean.Expr) := #[]
  for F in regions do
    let s' ← saveState
    try
      let pf ← keepsRegionOf s F
      unless (← isTypeCorrect pf) do throwError "frame"
      keptR := keptR.push (F, pf)
      trace[ec.frame] "kept (region): {F}"
    catch e =>
      s'.restore
      trace[ec.frame] "not kept (region): {F}\n{e.toMessageData}"
  withLocalDeclD `σ ps fun σ => withLocalDeclD `τ ps fun τ => do
    -- a global as the conditions read it, `X.get σ.globals` (`X.intoGlobal.get σ`, by `rfl`)
    let get (x st : Lean.Expr) : MetaM Lean.Expr := do
      if x.isAppOfArity ``Lens.intoGlobal 2 then
        return ← mkAppM ``Getter.get #[← mkAppM ``Lens.toGetter #[x.appArg!],
          ← mkAppM ``ProgramState.globals #[st]]
      mkAppM ``Getter.get #[← mkAppM ``Lens.toGetter #[x], st]
    let getR (F st : Lean.Expr) : MetaM Lean.Expr := do
      mkAppM ``Getter.get #[← mkAppM ``Footprint.touched_getter #[F],
        ← mkAppM ``ProgramState.globals #[st]]
    let mut body := mkConst ``True
    for (F, _) in keptR.reverse do
      body ← mkAppM ``And #[← mkEq (← getR F τ) (← getR F σ), body]
    for (x, _) in kept.reverse do
      body ← mkAppM ``And #[← mkEq (← get x τ) (← get x σ), body]
    let F ← mkLambdaFVars #[σ, τ] body
    let μ ← mkAppM ``programDenotation #[s, σ]
    let mut pf ← mkAppM ``SubProbability.satisfies_true' #[μ]
    for (_, hk) in keptR.reverse do
      pf ← mkAppM ``SubProbability.satisfies_and'
        #[← mkAppM ``Stmt.KeepsRegion.satisfies #[hk, σ], pf]
    for (_, hk) in kept.reverse do
      pf ← mkAppM ``SubProbability.satisfies_and' #[← mkAppM ``Stmt.Keeps.satisfies #[hk, σ], pf]
    return (F, ← mkLambdaFVars #[σ] pf)

end ECConseqFrame

end GaudisCrypt
