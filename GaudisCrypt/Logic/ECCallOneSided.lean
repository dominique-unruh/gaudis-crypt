import GaudisCrypt.Logic.Granular
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.ModuleFootprint

/-!
# EasyCrypt's one-sided call of a lossless procedure: `call{1} H`, `call{2} H`

    prhlStmt_seq_call_left_lossless    -- `x <- M(e)` at the end of the left side only
    prhlStmt_seq_call_right_lossless   -- the mirror

EC's `call{1} (H : islossless M)` drops a call at the end of one side: the call terminates (`H`),
and the postcondition must hold whatever the call returns and does to `M`'s globals — EC's
`forall r (gM : glob M), Q`.  Here what the postcondition may rely on staying put is a **frame**
`Fr g g'` between the globals before and after the call, which every run of `M` keeps:

* a lens `X` outside `M`'s footprint keeps its value (`Module.Proc.frame_lens`);
* the `glob` of a finitely supported `G` that `M` stays out of keeps its content
  (`Module.Proc.frame_glob`: EC's `={glob A}` against an abstract `A`);
* frames combine (`Module.Proc.frame_and`), and `True` is one (`Module.Proc.frame_true`).

The tactic:

    equiv_call{1} H                     -- EC's `call{1} H`, no frame
    equiv_call{1} H / x₁, …, glob A     -- with the frame `x₁`, …, `glob A`

`H : islossless M` may have holes (`_`, EC's `call{1} (S_ll RO _)`): they are goals after the
judgment's.  The frame's side conditions — lenses outside `M`'s footprint, `M` outside `glob A`,
`A` finitely supported — are shown by `fp_disjoint` and `fp_finite`.

A frame against an arbitrary footprint would not be sound
(`CounterExamples/FramingNeedsReset.lean`).
-/

namespace GaudisCrypt

variable {sig : ProcedureSignature} {M : Module.Proc sig}
  {A B : ProgramState → ProgramState → Prop} {s₁ s₂ : Stmt}

/-- `Fr` is a frame of `M`: every run of `M` from globals `g` ends in globals `g'` with
`Fr g g'`. -/
def Module.Proc.Frame (M : Module.Proc sig) (Fr : VariableAssignment → VariableAssignment → Prop) :
    Prop :=
  ∀ a g, (procedureDenotation M.procedure a g).satisfies fun r => Fr g r.2

theorem Module.Proc.frame_true (M : Module.Proc sig) : M.Frame fun _ _ => True :=
  fun _ _ _ _ => trivial

theorem Module.Proc.frame_and {F₁ F₂ : VariableAssignment → VariableAssignment → Prop}
    (h₁ : M.Frame F₁) (h₂ : M.Frame F₂) : M.Frame fun g g' => F₁ g g' ∧ F₂ g g' :=
  fun a g r hr => ⟨h₁ a g r hr, h₂ a g r hr⟩

/-- A lens outside `M`'s footprint is a frame of `M`. -/
theorem Module.Proc.frame_lens {β : Type} (X : Lens β VariableAssignment)
    (hX : X.footprint ≤ (FVP.fvP M)ᶜ) : M.Frame fun g g' => X.get g' = X.get g :=
  fun a g => Procedure.satisfies_frame (fun a => Module.Proc.inFootprint_fvP M a) X hX a g

/-- The `glob` of a finitely supported `G` that `M` stays out of is a frame of `M`. -/
theorem Module.Proc.frame_glob (G : Footprint VariableAssignment) (hG : G.FinitelySupported)
    (hMG : FVP.fvP M ≤ G.globᶜ) :
    M.Frame fun g g' => G.touched_getter.get g' = G.touched_getter.get g :=
  fun a g => ProgramDenotation.preserves_touched_of_glob (Module.Proc.inFootprint_fvP M a) hG hMG g

/-- **EC's `call{1} H`**, `H : islossless M`: the call `x₁ <- M(e₁)` at the end of the left side,
nothing on the right.  The precondition: the postcondition for every result `r` and every
globals `g` in the frame `Fr` of the left state's. -/
theorem prhlStmt_seq_call_left_lossless (hll : M.procedure.IsLossless)
    {Fr : VariableAssignment → VariableAssignment → Prop} (hFr : M.Frame Fr)
    {x₁ : Setter sig.ret ProgramState} {e₁ : Getter sig.ParamType ProgramState}
    (hpre : prhlStmt A s₁ s₂ fun σ₁ σ₂ => ∀ r g, Fr σ₁.globals g →
      B (x₁.set r (ProgramState.globalL.set g σ₁)) σ₂) :
    prhlStmt A (.seq s₁ (Stmt.call x₁ M.procedure e₁)) s₂ B :=
  prhlStmt_seq_left (prhlStmt_post hpre fun σ₁ _ hB => ⟨Stmt.call_wp_one hll _ _ _,
    Stmt.call_satisfies fun r hr => hB r.1 r.2 (hFr (e₁.get σ₁) σ₁.globals r hr)⟩)

/-- **EC's `call{2} H`**: the mirror of `prhlStmt_seq_call_left_lossless`. -/
theorem prhlStmt_seq_call_right_lossless (hll : M.procedure.IsLossless)
    {Fr : VariableAssignment → VariableAssignment → Prop} (hFr : M.Frame Fr)
    {x₂ : Setter sig.ret ProgramState} {e₂ : Getter sig.ParamType ProgramState}
    (hpre : prhlStmt A s₁ s₂ fun σ₁ σ₂ => ∀ r g, Fr σ₂.globals g →
      B σ₁ (x₂.set r (ProgramState.globalL.set g σ₂))) :
    prhlStmt A s₁ (.seq s₂ (Stmt.call x₂ M.procedure e₂)) B :=
  prhlStmt_of_symm (prhlStmt_seq_call_left_lossless hll hFr hpre.symm)

namespace ECCallOneSided

open Lean Meta Elab Tactic PRHLWp

/-- The frame `x₁, …, glob A` as a proof of `M.Frame _`: a lens, or the `glob` of a module. -/
def frameTerm (xs : Array Term) : TacticM Term := do
  let parts ← xs.mapM fun t => match t with
    | `(glob $a) => `(Module.Proc.frame_glob (FVP.fvP $a) (by fp_finite) (by fp_disjoint))
    | _ => `(Module.Proc.frame_lens $(⟨t⟩) (by fp_disjoint))
  match parts.back? with
  | none => `(Module.Proc.frame_true _)
  | some last => parts.pop.foldrM (fun p acc => `(Module.Proc.frame_and $p $acc)) last

end ECCallOneSided

/-- **EC's `call{i} H`**: see the module docstring. -/
syntax (name := equivCallOneSided) "equiv_call" Judgment.judgmentSide ppSpace term:max
  (" / " term,+)? : tactic

open Lean Meta Elab Tactic PRHLWp ECCallOneSided in
elab_rules : tactic
  | `(tactic| equiv_call $s:judgmentSide $h:term $[/ $xs:term,*]?) => withMainContext do
    let some side := Judgment.sideOf? (some s) | throwError "equiv_call: a side, 1 or 2"
    let g ← getMainGoal
    let _ ← prhlGoal g "equiv_call"
    let g ← HoareSplit.hoareSplit 1 g (some side)
    let lem := mkIdent (if side == 1 then ``prhlStmt_seq_call_left_lossless
      else ``prhlStmt_seq_call_right_lossless)
    let fr ← frameTerm ((xs.map (·.getElems)).getD #[])
    let (gs, holes) ← g.withContext do
      let (hE, holes) ← elabTermWithHoles h none `lossless (allowNaturalHoles := true)
      let gs ← Tactic.run g (evalTactic
        (← `(tactic| refine $lem $(← Term.exprToSyntax hE) $fr ?_)))
      return (gs, holes)
    let gs ← gs.mapM fun g' => do
      try Judgment.simpArg g' 3 relSimpDecls [] catch _ => pure g'
    replaceMainGoal (gs ++ holes)

end GaudisCrypt
