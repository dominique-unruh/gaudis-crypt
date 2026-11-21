import GaudisCrypt.Logic.ECCallOneSided
import GaudisCrypt.Logic.PRHLStmt
import GaudisCrypt.Lib.RO.GlobTransfer

/-!
# The relational call rule with the callees' frames

`prhlStmt_seq_call_frame`: EC's `call` keeps what the callees do not touch.  The postcondition
is asked for the results and globals the callees' judgment relates **and** that are in each
side's frame of its globals before the call (`Module.Proc.Frame`: a variable outside the
callee's footprint keeps its value, `Module.Proc.frame_lens`).  `ECCallEquiv.frameFor` builds
the frame of a callee for the variables a condition reads.

Used by the call tactics for concrete callees (`Logic/ECCallEquiv.lean`) and for the procedures
of a declared module with several procedures (`Logic/ECCallAbstract.lean`).
-/

namespace GaudisCrypt

open GaudisCrypt.Lib.RO.Instantiate

/-- **EC's `call (: P ==> Q)`**, with each callee's frame: the callees' runs coupled by `h`; the
postcondition for every results and globals `h` relates that are in each side's frame of its
globals before the call.  The frames come first, as in `conseq`'s and `while`'s rules: what they
keep rewrites the reads of `Q` (`simp_all` rewrites a premise with the ones before it only). -/
theorem prhlStmt_seq_call_frame {sig₁ sig₂ : ProcedureSignature} {M₁ : Module.Proc sig₁}
    {M₂ : Module.Proc sig₂}
    {P : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop}
    {Q : sig₁.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop}
    (h : prhlProc P M₁.procedure M₂.procedure Q)
    {Fr₁ Fr₂ : VariableAssignment → VariableAssignment → Prop} (hFr₁ : M₁.Frame Fr₁)
    (hFr₂ : M₂.Frame Fr₂) {x₁ : Setter sig₁.ret ProgramState}
    {e₁ : Getter sig₁.ParamType ProgramState} {x₂ : Setter sig₂.ret ProgramState}
    {e₂ : Getter sig₂.ParamType ProgramState} {A B : ProgramState → ProgramState → Prop}
    {s₁ s₂ : Stmt}
    (hpre : prhlStmt A s₁ s₂ fun σ₁ σ₂ => P (e₁.get σ₁) σ₁.globals (e₂.get σ₂) σ₂.globals ∧
      ∀ r₁ g₁ r₂ g₂, Fr₁ σ₁.globals g₁ → Fr₂ σ₂.globals g₂ → Q r₁ g₁ r₂ g₂ →
        B (x₁.set r₁ (ProgramState.globalL.set g₁ σ₁))
          (x₂.set r₂ (ProgramState.globalL.set g₂ σ₂))) :
    prhlStmt A (.seq s₁ (Stmt.call x₁ M₁.procedure e₁)) (.seq s₂ (Stmt.call x₂ M₂.procedure e₂))
      B := by
  refine prhlStmt_seq (B := fun σ₁ σ₂ => _) ?_ hpre
  intro σ₁ σ₂ ⟨hA, hB⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := h (e₁.get σ₁) (e₂.get σ₂) σ₁.globals σ₂.globals hA
  have hμ₁ : μ.satisfies (fun w => Fr₁ σ₁.globals w.1.2) :=
    coupling_satisfies_fst (by rw [hm1]; exact hFr₁ _ _)
  have hμ₂ : μ.satisfies (fun w => Fr₂ σ₂.globals w.2.2) :=
    coupling_satisfies_snd (by rw [hm2]; exact hFr₂ _ _)
  refine ⟨μ >>= fun w => pure (((), x₁.set w.1.1 (ProgramState.globalL.set w.1.2 σ₁)),
    ((), x₂.set w.2.1 (ProgramState.globalL.set w.2.2 σ₂))), ?_, ?_, ?_⟩
  · refine SubProbability.marginal_fst_eq fun F => ?_
    rw [SubProbability.expected_map, SubProbability.expected_fst_of_marginal hm1
      (fun r => F ((), x₁.set r.1 (ProgramState.globalL.set r.2 σ₁))),
      programDenotation_call_apply, SubProbability.expected_hbind]
    simp only [expected_pure]
  · refine SubProbability.marginal_snd_eq fun F => ?_
    rw [SubProbability.expected_map, SubProbability.expected_snd_of_marginal hm2
      (fun r => F ((), x₂.set r.1 (ProgramState.globalL.set r.2 σ₂))),
      programDenotation_call_apply, SubProbability.expected_hbind]
    simp only [expected_pure]
  · exact SubProbability.satisfies_bind _ fun w hw => SubProbability.satisfies_pure _ _
      (hB _ _ _ _ (hμ₁ w hw) (hμ₂ w hw) (hsat w hw))

/-- **EC's frame by writes**: a lens that every write of `M`'s body keeps (its callees'
included) is a frame of `M` — a callee that reads `X` without writing it keeps it, where
`Module.Proc.frame_lens` asks `M` to stay out of `X` altogether. -/
theorem Module.Proc.frame_lens_writes {sig : ProcedureSignature} {M : Module.Proc sig} {β : Type}
    (X : Lens β VariableAssignment) (hp : StmtWithHoles.WritesKeep X.get M.procedure.body) :
    M.Frame fun g g' => X.get g' = X.get g :=
  fun a g => Procedure.satisfies_of_writesKeep X.get M.procedure hp a g

namespace ECCallEquiv

open Lean Meta Elab Tactic

/-- A proof of `StmtWithHoles.WritesKeep G s`: the single writes of `s`, its callees' included
(`writesKeepSplit`, which unfolds module procedures as the inliner does), each by `rfl` (a write
to a local) or `StmtSwap.discharge` (a write to another global). -/
def writesKeepProof (ty : Lean.Expr) : MetaM Lean.Expr := do
  let m ← mkFreshExprMVar ty
  let gs ← writesKeepSplit m.mvarId!
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    let s ← saveState
    let ok ← try
        let (_, g') ← g.intros
        g'.refl
        pure true
      catch _ => s.restore; pure false
    unless ok do g.assign (← StmtSwap.discharge t none)
  let r ← instantiateMVars m
  if r.hasExprMVar then throwError "writes keep: a write is left"
  return r

/-- `Module.Proc.frame_lens_writes` for `M` and the lens `X`, when every write of `M`'s body
keeps `X` (`writesKeepProof`); the state is restored if not. -/
def frameLensWrites? (M X : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let s ← saveState
  try
    let c ← mkConstWithFreshMVarLevels ``Module.Proc.frame_lens_writes
    let (ms, _, _) ← forallMetaTelescope (← inferType c)
    -- binders: `sig`, `M`, `β`, `X`, `hp`
    unless ← isDefEq ms[1]! M do throwError "frame: the callee"
    unless ← isDefEq ms[3]! X do throwError "frame: the lens"
    let hp ← writesKeepProof (← instantiateMVars (← inferType ms[4]!))
    unless ← isDefEq ms[4]! hp do throwError "frame: the writes"
    let e ← instantiateMVars (mkAppN c ms)
    if e.hasExprMVar then throwError "frame: open"
    return some e
  catch _ =>
    s.restore
    return none

/-- `t` elaborates, with no error and no `sorry`; the state is restored if not. -/
def elabClean (t : Term) : TermElabM (Option Lean.Expr) := do
  let s ← saveState
  let log ← Core.getMessageLog
  -- only this elaboration's messages: errors logged earlier in the file are not this term's
  Core.resetMessageLog
  try
    let e ← Term.withoutErrToSorry do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    if e.hasSorry || e.hasMVar || (← Core.getMessageLog).hasErrors then
      s.restore; Core.setMessageLog log; return none
    Core.setMessageLog log
    return some e
  catch _ => s.restore; Core.setMessageLog log; return none

/-- The frame of the callee `M` for the global variables `xs` and the regions `Rs` a condition
reads: those `M` stays out of, or, for a variable, does not write (EC's call keeps them), combined
with `Module.Proc.frame_and`. -/
def frameFor (M : Lean.Expr) (xs Rs : Array Lean.Expr) : TermElabM Lean.Expr := do
  let MS ← Term.exprToSyntax M
  let mut parts : Array Lean.Expr := #[]
  for x in xs do
    let XS ← Term.exprToSyntax x
    if let some e ← elabClean (← `(Module.Proc.frame_lens (M := $MS) $XS (by fp_disjoint))) then
      parts := parts.push e
    -- EC's frame by writes: `M` reads `X` but does not write it
    else if let some e ← frameLensWrites? M x then
      parts := parts.push e
  for R in Rs do
    let RS ← Term.exprToSyntax R
    if let some e ← elabClean
        (← `(Module.Proc.frame_glob (M := $MS) $RS (by fp_finite) (by fp_disjoint))) then
      parts := parts.push e
    else if let some X ← TacticMisc.regionLens? R then
      let XS ← Term.exprToSyntax X
      if let some e ← elabClean (← `(Module.Proc.frame_region (M := $MS) $XS (R := $RS)
          (by first | rfl | simp only [Footprint.lens_pair]) (by fp_disjoint))) then
        parts := parts.push e
  match parts.back? with
  | none => mkAppM ``Module.Proc.frame_true #[M]
  | some last => parts.pop.foldrM (fun p acc => mkAppM ``Module.Proc.frame_and #[p, acc]) last

/-- The global variables (`global_var`s, `module_var`s, a clone's aliases of them) that `e`
reads, as written: the closed lenses on the globals whose head has a key (`x.key_eq`). -/
def globalVarsIn (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let env ← getEnv
  let xs ← IO.mkRef (#[] : Array Lean.Expr)
  Meta.forEachExpr (← instantiateMVars e) fun x => do
    if x.hasLooseBVars then return
    let some c := x.getAppFn.constName? | return
    let isVar ← if env.contains (c ++ `key_eq) then pure true else do
      if (← getReducibilityStatus c) != .reducible then pure false else
      let some c' := (← whnfR x).getAppFn.constName? | pure false
      pure (c' != c && env.contains (c' ++ `key_eq))
    unless isVar do return
    let t ← whnfR (← inferType x)
    unless t.isAppOfArity ``Lens 2 && (t.getArg! 1).isConstOf ``VariableAssignment do return
    unless (← xs.get).contains x do xs.modify (·.push x)
  xs.get

end ECCallEquiv

end GaudisCrypt
