import GaudisCrypt.Logic.FelTactic
import GaudisCrypt.Logic.ExpectationFrame
import GaudisCrypt.Logic.ECCallAbstract

/-!
# EasyCrypt's `fel` over a procedure the oracles call

    fel cntr step q bad [M : pre] inv?

EC's `fel` names, between brackets, the procedures whose calls may set the failure event `bad`.
They need not be the adversary's oracles: `Gcol.eca`'s `Pr_col` names `Gcol.sample_c`, which the
oracles `S.f`, `S.fi`, `M.f` call.  EC then checks the rest of the oracles' code syntactically:
it must not touch the counter and `bad` other than through the named procedures.

Here (`phoareStmt_fel_inner`): the named procedure has EC's premises (`FelProc`, as `FelOracle`
with `pre` a condition on all the globals — it may read what the oracles write), from which its
calls do not increase `fel`'s potential (`FelProc.ewp_le`); every oracle satisfies the syntactic
check `StmtWithHoles.ExpDecr` for that potential (its writes keep the view of the counter, `bad`
and `inv`; its calls are to the named procedure or check again), which `exp_decr` discharges.
-/

namespace GaudisCrypt

variable {Ω : Type} (L : Lens Ω VariableAssignment) (cntr : Ω → ℤ) (step : ℤ → ENNReal) (q : ℤ)
  (bad inv : Ω → Prop)

/-- EC's premises of `fel` for a procedure `p` named in `[p : pre]`, over the view `L.get` of the
globals; `pre` a condition on the globals themselves (`FelOracle` with `pre` read through `L`). -/
structure FelProc {sig : ProcedureSignature} (pre : VariableAssignment → Prop) (p : Procedure sig) :
    Prop where
  /-- a call that may set `bad` is one of the `q` the bound pays for -/
  lt : ∀ g, inv (L.get g) → ¬ bad (L.get g) → pre g → cntr (L.get g) < q
  /-- … and sets it with probability at most `step cntr` -/
  step : phoareProc (fun _ g => inv (L.get g) ∧ ¬ bad (L.get g) ∧ pre g) p
    (fun _ g' => indicatorE (bad (L.get g'))) (· ≤ ·) (fun _ g => step (cntr (L.get g)))
  /-- … and increases the counter (unless it set `bad`) -/
  incr : ∀ c, hoareProc (fun _ g => inv (L.get g) ∧ ¬ bad (L.get g) ∧ pre g ∧
      cntr (L.get g) = c) p (fun _ g' => inv (L.get g') ∧ (bad (L.get g') ∨ c < cntr (L.get g')))
  /-- the other calls do not set `bad` nor decrease the counter -/
  same : ∀ c, hoareProc (fun _ g => inv (L.get g) ∧ ¬ bad (L.get g) ∧ ¬ pre g ∧
      cntr (L.get g) = c) p (fun _ g' => inv (L.get g') ∧ ¬ bad (L.get g') ∧ c ≤ cntr (L.get g'))
  /-- `bad` persists -/
  keep : hoareProc (fun _ g => inv (L.get g) ∧ bad (L.get g)) p
    (fun _ g' => inv (L.get g') ∧ bad (L.get g'))

variable {L cntr step q bad inv}

/-- **The step of the potential** for a procedure named in `fel`'s brackets: its calls do not
increase `felPotential` in expectation (as `FelOracle.ewp_le`). -/
theorem FelProc.ewp_le {sig : ProcedureSignature} {pre : VariableAssignment → Prop}
    {p : Procedure sig} (h : FelProc L cntr step q bad inv pre p) (a : sig.ParamType)
    (g : VariableAssignment) :
    p.ewp a (fun _ g' => felPotential cntr step q bad inv (L.get g')) g ≤
      felPotential cntr step q bad inv (L.get g) := by
  classical
  by_cases hi : inv (L.get g)
  swap
  · simp only [felPotential, hi, not_false_eq_true, if_true]
    exact le_top
  by_cases hb : bad (L.get g)
  · rw [show felPotential cntr step q bad inv (L.get g) = 1 by simp [felPotential, hi, hb]]
    refine (Procedure.ewp_mono_of_hoare h.keep ⟨hi, hb⟩ (G := fun _ _ => 1)
      fun v g' ⟨hi', hb'⟩ => by simp [felPotential, hi', hb']).trans ?_
    exact Procedure.ewp_const_le _ _ _ _
  have hpot : felPotential cntr step q bad inv (L.get g) =
      ∑ i ∈ Finset.Ico (cntr (L.get g)) q, step i := by simp [felPotential, hi, hb]
  rw [hpot]
  set c := cntr (L.get g)
  by_cases hp : pre g
  · have hlt := h.lt g hi hb hp
    refine (Procedure.ewp_mono_of_hoare (h.incr c) ⟨hi, hb, hp, rfl⟩
      (G := fun _ g' => indicatorE (bad (L.get g')) + ∑ i ∈ Finset.Ico (c + 1) q, step i)
      fun v g' ⟨hi', hc'⟩ => ?_).trans ?_
    · by_cases hb' : bad (L.get g')
      · simp [felPotential, hi', hb']
      · have hc'' : c + 1 ≤ cntr (L.get g') := (hc'.resolve_left hb')
        simp only [felPotential, hi', not_true_eq_false, if_false, hb', indicatorE_false,
          zero_add]
        exact felPotential_sum_anti hc''
    rw [Procedure.ewp_add]
    refine (add_le_add (h.step a g ⟨hi, hb, hp⟩) (Procedure.ewp_const_le _ _ _ _)).trans
      (le_of_eq ?_)
    rw [← Finset.insert_Ico_add_one_left_eq_Ico hlt, Finset.sum_insert (by simp)]
  · refine (Procedure.ewp_mono_of_hoare (h.same c) ⟨hi, hb, hp, rfl⟩
      (G := fun _ _ => ∑ i ∈ Finset.Ico c q, step i)
      fun v g' ⟨hi', hb', hc'⟩ => ?_).trans (Procedure.ewp_const_le _ _ _ _)
    simp only [felPotential, hi', not_true_eq_false, if_false, hb']
    exact felPotential_sum_anti hc'

/-- **EC's `fel` with the bad event set in procedures the oracles call**: `D` applied to oracles
whose bodies pass the syntactic check `ExpDecr` for `fel`'s potential, started where `inv` holds
and `bad` does not, ends in `bad` with probability at most `∑_{i ∈ [cntr, q)} step i`. -/
theorem Module.fel_expDecr {T : Type 1} [IsModule T] {sig : ProcedureSignature}
    {holes : HoleSigs} (D : Module.Arr T (Module.Proc sig)) (ext : T → holes.Instantiation)
    (hD : Module.Representable D ext) (hdisj : FVP.fvP D ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (O : T)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      StmtWithHoles.ExpDecr (fun g => L.get g) (felPotential cntr step q bad inv)
        ((ext O).lookup n).body)
    (a : sig.ParamType) (g : VariableAssignment) (hi : inv (L.get g)) (hb : ¬ bad (L.get g)) :
    (Module.app D O).procedure.ewp a (fun _ g' => indicatorE (bad (L.get g'))) g ≤
      ∑ i ∈ Finset.Ico (cntr (L.get g)) q, step i := by
  classical
  have hpot := Module.ewp_app_le (L := L) D ext hD hdisj hc O (felPotential cntr step q bad inv)
    (fun n a g => Procedure.ewp_le_of_expDecr (fun g => L.get g) _ _ (horacle n) a g) a g
  refine (Procedure.ewp_mono _ _ (fun v g' => ?_) _).trans (hpot.trans (le_of_eq ?_))
  · by_cases hi' : inv (L.get g')
    · by_cases hb' : bad (L.get g') <;> simp [felPotential, hi', hb']
    · simp [felPotential, hi']
  · simp [felPotential, hi, hb]

/-- **EC's `fel … [M : pre]` on a statement**, `M` a procedure the oracles call: as
`phoareStmt_fel`, the oracles checked syntactically (`ExpDecr`, with `M`'s step `FelProc.ewp_le`
for its calls), the event `E` at most `bad`. -/
theorem phoareStmt_fel_inner {T : Type 1} [IsModule T] {sig : ProcedureSignature}
    {holes : HoleSigs} (D : Module.Arr T (Module.Proc sig)) (ext : T → holes.Instantiation)
    (hD : Module.Representable D ext) (hdisj : FVP.fvP D ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (O : T)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      StmtWithHoles.ExpDecr (fun g => L.get g) (felPotential cntr step q bad inv)
        ((ext O).lookup n).body)
    {A : ProgramState → Prop} {s₀ : Stmt} {x : Setter sig.ret ProgramState}
    {e : Getter sig.ParamType ProgramState} {r : ENNReal} {E : ProgramState → ENNReal}
    (hx : ∀ v τ, L.get (x.set v τ).globals = L.get τ.globals)
    (hE : ∀ τ, E τ ≤ indicatorE (bad (L.get τ.globals)))
    (hinit : hoareStmt A s₀ fun τ => inv (L.get τ.globals) ∧ ¬ bad (L.get τ.globals) ∧
      cntr (L.get τ.globals) = 0)
    (hsum : ∑ i ∈ Finset.Ico 0 q, step i ≤ r) :
    phoareStmt A (.seq s₀ (Stmt.call x (Module.app D O).procedure e)) E
      (@LE.le ENNReal _) (fun _ => r) := by
  intro σ hA
  rw [Stmt.ewp_seq, Stmt.ewp_call]
  have hσ := hoare_pre hinit fun τ (hτ : τ = σ) => hτ ▸ hA
  refine (Stmt.ewp_mono_of_hoare hσ (G := fun _ => r) fun τ ⟨hi, hb, h0⟩ => ?_).trans
    (Stmt.ewp_const_le _ _ _)
  have hfel := Module.fel_expDecr D ext hD hdisj hc O horacle (e.get τ) τ.globals hi hb
  rw [h0] at hfel
  refine le_trans ?_ (hfel.trans hsum)
  refine Procedure.ewp_mono _ _ (fun v gl => ?_) _
  refine (hE _).trans (le_of_eq ?_)
  rw [hx]
  rfl

/-- The bad event is below `fel`'s potential. -/
theorem indicatorE_le_felPotential (s : Ω) :
    indicatorE (bad s) ≤ felPotential cntr step q bad inv s := by
  classical
  by_cases hi : inv s
  · by_cases hb : bad s <;> simp [felPotential, hi, hb]
  · simp [felPotential, hi]

/-- **EC's `fel … [M : pre]` on a statement with code after the adversary**: as
`phoareStmt_fel_inner`, the code `s₁` after the call checked like the oracles (`ExpDecr`: EC's
`Gext.distinguish` resamples after `D`, through `ReSample.f`). -/
theorem phoareStmt_fel_inner_rest {T : Type 1} [IsModule T] {sig : ProcedureSignature}
    {holes : HoleSigs} (D : Module.Arr T (Module.Proc sig)) (ext : T → holes.Instantiation)
    (hD : Module.Representable D ext) (hdisj : FVP.fvP D ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (O : T)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      StmtWithHoles.ExpDecr (fun g => L.get g) (felPotential cntr step q bad inv)
        ((ext O).lookup n).body)
    {A : ProgramState → Prop} {s₀ s₁ : Stmt} {x : Setter sig.ret ProgramState}
    {e : Getter sig.ParamType ProgramState} {r : ENNReal} {E : ProgramState → ENNReal}
    (hx : ∀ v τ, L.get (x.set v τ).globals = L.get τ.globals)
    (hrest : StmtWithHoles.ExpDecr (fun g => L.get g) (felPotential cntr step q bad inv) s₁)
    (hE : ∀ τ, E τ ≤ indicatorE (bad (L.get τ.globals)))
    (hinit : hoareStmt A s₀ fun τ => inv (L.get τ.globals) ∧ ¬ bad (L.get τ.globals) ∧
      cntr (L.get τ.globals) = 0)
    (hsum : ∑ i ∈ Finset.Ico 0 q, step i ≤ r) :
    phoareStmt A (.seq s₀ (.seq (Stmt.call x (Module.app D O).procedure e) s₁)) E
      (@LE.le ENNReal _) (fun _ => r) := by
  classical
  intro σ hA
  simp only [Stmt.ewp_seq]
  have hσ := hoare_pre hinit fun τ (hτ : τ = σ) => hτ ▸ hA
  refine (Stmt.ewp_mono_of_hoare hσ (G := fun _ => r) fun τ ⟨hi, hb, h0⟩ => ?_).trans
    (Stmt.ewp_const_le _ _ _)
  -- after the call: `s₁` does not increase the potential, which is above `E`
  refine (Stmt.ewp_mono _ (fun τ' => (Stmt.ewp_mono s₁ (fun τ'' => (hE τ'').trans
    (indicatorE_le_felPotential (L.get τ''.globals))) τ').trans
    (Stmt.ewp_le_of_expDecr (fun g => L.get g) (felPotential cntr step q bad inv) s₁ hrest τ'))
    τ).trans ?_
  -- the call: the abstract call's potential step, the oracles checked syntactically
  rw [Stmt.ewp_call]
  have hpot := Module.ewp_app_le (L := L) D ext hD hdisj hc O (felPotential cntr step q bad inv)
    (fun n a g => Procedure.ewp_le_of_expDecr (fun g => L.get g) _ _ (horacle n) a g)
    (e.get τ) τ.globals
  refine le_trans (le_of_eq ?_) (hpot.trans (le_of_eq_of_le ?_ hsum))
  · simp only [Procedure.ewp]
    congr 1; funext w; rw [hx]; rfl
  · simp [felPotential, hi, hb, h0]

/-- `indicatorE` is monotone. -/
theorem indicatorE_mono {P Q : Prop} (h : P → Q) : indicatorE P ≤ indicatorE Q := by
  classical
  by_cases hP : P
  · simp [indicatorE, hP, h hP]
  · simp [indicatorE, hP]

end GaudisCrypt

namespace GaudisCrypt.FelInner

open Lean Meta Elab Tactic

/-- A write `∀ v σ, L.get (x.set v σ).globals = L.get σ.globals` to a global `X` outside the view
`L` (`x` its lift to the program state), the disjointness by `fp_disjoint` (`exp_decr_write`
takes it from a hypothesis). -/
elab "exp_decr_write_fp" : tactic => do
  evalTactic (← `(tactic| intro v σ))
  evalTactic (← `(tactic| refine (Lens.footprint_touched_getter_eq_iff _ _ _).mp ?_))
  let ty ← instantiateMVars (← getMainTarget)
  let some x := ty.find? fun e => e.isAppOf `GaudisCrypt.liftLens || e.isAppOf ``Lens.intoGlobal
    | throwError "exp_decr_write_fp: no write to a global in{indentExpr ty}"
  let X ← Term.exprToSyntax x.appArg!
  evalTactic (← `(tactic| (
    refine touched_set_of_le_compl (X := $X) ?_ v σ.globals
    (try simp only [Footprint.lens_pair])
    fp_disjoint)))

/-- `expDecrSplit` (`Logic/ExpectationFrame.lean`) for `fel`: a call's step lemma is also looked for
at default transparency when none matches reducibly (a named procedure reached through an
oracle record, `Iter(ReSample)`'s `Orcl.f (Orcl.mk {f := ReSample.f})`). -/
partial def expDecrSplit' (g : MVarId) (fuel : Nat := 256) : TacticM (List MVarId) := do
  if fuel == 0 then return [g]
  let ty ← whnf (← instantiateMVars (← g.getType))
  if ty.isAppOfArity ``And 2 then
    let gs ← g.apply (mkConst ``And.intro [])
    return (← gs.mapM (expDecrSplit' · (fuel - 1))).flatten
  else if ty.isAppOfArity ``Or 2 then
    let s ← saveState
    try
      let [g'] ← g.apply (mkConst ``Or.inl []) | throwError "Or.inl"
      let ty ← instantiateMVars (← g'.getType)
      let ty' := ty.replace fun e =>
        if e.isAppOfArity ``ProcedureWithHoles.mk 7 then
          match e.getArg! 5 with
          | .app (.app (.app (.const ``ProcedureWithHoles.body _) _) _) p => some p
          | .proj _ 3 p => some p
          | _ => none
        else none
      let g' ← g'.replaceTargetDefEq ty'
      try withReducible g'.assumption catch _ => g'.assumption
      return []
    catch _ =>
      s.restore
      let [g'] ← g.apply (mkConst ``Or.inr []) | throwError "Or.inr"
      expDecrSplit' g' (fuel - 1)
  else if ty.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return []
  else if ty.isAppOf ``StmtWithHoles.ExpDecr then
    let some p := ty.find? (·.isAppOf ``Module.Proc.procedure)
      | throwError "stuck at{indentExpr ty}"
    let r ← Flatten.unfoldProcedure p
    let g ← g.replaceTargetDefEq ty
    let g ← match r.proof? with
      | none => g.replaceTargetDefEq (ty.replace fun e => if e == p then some r.expr else none)
      | some h => do
        let res ← g.rewrite ty h
        g.replaceTargetEq res.eNew res.eqProof
    expDecrSplit' g (fuel - 1)
  else
    return [← g.replaceTargetDefEq ty]

/-- For each statement on the right spine of `s` (through the `let`s of the locals): whether it
calls an applied module (`Module.app`), the adversary's call. -/
partial def spineCalls (s : Lean.Expr) : MetaM (List Bool) := do
  let s ← TacticMisc.openStmt s
  if let .letE n ty val body _ := s then
    return ← withLetDecl n ty val fun fv => spineCalls (body.instantiate1 fv)
  let hasApp (e : Lean.Expr) := (e.find? (·.isAppOfArity ``GaudisCrypt.Module.app 6)).isSome
  if s.isAppOfArity ``StmtWithHoles.seq 3 then
    return hasApp (s.getArg! 1) :: (← spineCalls (s.getArg! 2))
  return [hasApp s]

end GaudisCrypt.FelInner

/-- **EC's `fel cntr step q bad [M : pre, …] inv`** with procedures `M` that the oracles call (see
the module docstring); `inv` may be left out (EC's `true`). -/
syntax (name := felInner) "fel " term:max term:max term:max term:max " [" (term " : " term),+ "]"
  (ppSpace colGt term:max)? : tactic

open Lean Meta Elab Tactic GaudisCrypt GaudisCrypt.FelTactic GaudisCrypt.ECCall PHoareWp in
elab_rules (kind := felInner) : tactic
  | `(tactic| fel $cntr $step $q $bad [ $[$ms : $ps],* ] $[$inv?]?) => do
    -- what follows the call (EC's `fel` takes the whole procedure), then `s₀; x <- call D(O)`
    -- (`s₀; (x <- call D(O); s₁)` when calls follow it, `Gext`'s resampling)
    evalTactic (← `(tactic| try stmt_wp))
    let k ← withMainContext do
      let ty ← instantiateMVars (← getMainTarget)
      let some stmt := ty.getAppArgs.find? fun a =>
          (a.find? (·.isAppOfArity ``GaudisCrypt.Module.app 6)).isSome
        | throwError "fel: no call of an applied module in{indentExpr ty}"
      let flags ← GaudisCrypt.FelInner.spineCalls stmt
      let some i := (flags.toArray.zipIdx.reverse.find? (·.1)).map (·.2)
        | throwError "fel: no call of an applied module in{indentExpr stmt}"
      pure (flags.length - i)
    liftMetaTactic1 fun g => some <$> Judgment.onStmt (HoareSplit.splitSeq k) g
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    let some callee := ty.find? (·.isAppOfArity ``GaudisCrypt.Module.app 6)
      | throwError "fel: no call of an applied module in{indentExpr ty}"
    let O := callee.getArg! 5
    let T ← whnfR (← inferType O)
    -- the oracles' procedures: `T.ext`, or the canonical one of a product of module types
    let ext ← do
      let some C := T.getAppFn.constName?
        | throwError "fel: the oracles' type is not a module type:{indentExpr T}"
      if (← getEnv).contains (C ++ `ext) then
        pure (mkAppN (← mkConstWithFreshMVarLevels (C ++ `ext)) T.getAppArgs)
      else g.withContext do
        let TS ← Term.exprToSyntax T
        let e ← Term.elabTerm (← `(fun O => (Module.moduleTypeRep $TS).extOf (Module.cast $TS O)))
          none
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e
    -- the conditions, as functions of the state
    let cntrF ← elabGoalFunction cntr (mkConst ``Int)
    let badF ← elabGoalFunction bad (mkSort Level.zero)
    let invF ← match inv? with
      | some i => elabGoalFunction i (mkSort Level.zero)
      | none => elabGoalFunction (← `(True)) (mkSort Level.zero)
    let (stepE, qE) ← withMainContext do
      let s ← Term.elabTermEnsuringType step (← mkArrow (mkConst ``Int) (mkConst ``ENNReal))
      let q ← Term.elabTermEnsuringType q (mkConst ``Int)
      Term.synthesizeSyntheticMVarsNoPostponing
      return (← instantiateMVars s, ← instantiateMVars q)
    let (L, fs) ← g.withContext (inferView [cntrF, badF, invF])
    let (cntr', bad', inv') := (fs[0]!, fs[1]!, fs[2]!)
    -- per named procedure: its procedure, `pre` over its own view of the globals, the goal of
    -- its premises (`FelProc`) and its step lemma
    let mut procGoals : Array MVarId := #[]
    let mut steps : Array (Lean.Expr × Lean.Expr) := #[]
    for M in ms, P in ps do
      let preF ← elabGoalFunction P (mkSort Level.zero)
      let (pre, p) ← g.withContext do
        let (Lp, ps') ← inferView [preF]
        let pre ← withLocalDeclD `g (mkConst ``VariableAssignment) fun gv => do
          mkLambdaFVars #[gv] (mkApp ps'[0]!
            (← mkAppM ``Getter.get #[← mkAppM ``Lens.toGetter #[Lp], gv]))
        let Me ← Term.elabTerm M none
        Term.synthesizeSyntheticMVarsNoPostponing
        let Me ← instantiateMVars Me
        let p ← if (← whnfR (← inferType Me)).isAppOf ``ProcedureWithHoles then pure Me
          else mkAppM ``Module.Proc.procedure #[Me]
        pure (pre, p)
      let fo ← g.withContext do
        let ty ← mkAppOptM ``FelProc #[none, L, cntr', stepE, qE, bad', inv', none, pre, p]
        mkFreshExprSyntheticOpaqueMVar ty `felproc
      procGoals := procGoals.push fo.mvarId!
      let st ← g.withContext do mkAppM ``FelProc.ewp_le #[fo]
      steps := steps.push (st, ← g.withContext (inferType st))
    -- the rule
    let stx ← if k == 1 then
      `(tactic| refine phoareStmt_fel_inner (L := $(← Term.exprToSyntax L))
        (cntr := $(← Term.exprToSyntax cntr')) (step := $(← Term.exprToSyntax stepE))
        (q := $(← Term.exprToSyntax qE)) (bad := $(← Term.exprToSyntax bad'))
        (inv := $(← Term.exprToSyntax inv')) _ $(← Term.exprToSyntax ext)
        (Module.Declared.ecModule _ $(← Term.exprToSyntax ext)).representable ?hdisj ?hc _
        ?horacle ?hx ?hE ?init ?sum)
      else
      `(tactic| refine phoareStmt_fel_inner_rest (L := $(← Term.exprToSyntax L))
        (cntr := $(← Term.exprToSyntax cntr')) (step := $(← Term.exprToSyntax stepE))
        (q := $(← Term.exprToSyntax qE)) (bad := $(← Term.exprToSyntax bad'))
        (inv := $(← Term.exprToSyntax inv')) _ $(← Term.exprToSyntax ext)
        (Module.Declared.ecModule _ $(← Term.exprToSyntax ext)).representable ?hdisj ?hc _
        ?horacle ?hx ?hrest ?hE ?init ?sum)
    evalTactic stx
    untagGoals
    closeTagged `hdisj (← `(tactic| ((try simp only [Footprint.lens_pair]); fp_disjoint)))
    closeTagged `hx (← `(tactic| (intro _ _; rfl)))
    closeTagged `hE (← `(tactic| first
      | (intro _; exact le_rfl)
      | (intro _; simp only [← indicatorE_and]; apply indicatorE_mono; intro h
         simp only [Lens.pair] at *; first | exact h | exact h.1 | exact h.2)))
    let byTag (t : Name) : TacticM (Option MVarId) := do
      (← getGoals).findM? fun g => return (← g.getTag) == t
    -- the oracles' procedures, one goal each
    let comps ← components T O false
    let procs := (← comps.mapM fun (C, X) => procsOf C X).flatten
    let k := procs.size
    if let some gc ← byTag `hc then
      for h in ← splitHoles gc k do
        let [] ← evalTacticAt (← `(tactic| first
            | infer_instance
            | (dsimp only [ProcedureSignature.ParamType, typeListToTuple]; infer_instance))) h
          | throwError "fel: an oracle's argument type is not countable"
      setGoals ((← getGoals).filter (· != gc))
    let mut left : Array MVarId := #[]
    if let some go ← byTag `horacle then
      setGoals ((← getGoals).filter (· != go))
      let hs := (← splitHoles go k).toArray
      for i in [0:k] do
        let h := hs[i]!
        -- the oracle's procedure in place of `(ext O).lookup _`, the named procedures' steps in
        -- context, then the syntactic check
        let h ← h.withContext do
          let ty ← instantiateMVars (← h.getType)
          h.change (ty.replace fun e =>
            if e.isAppOf ``HoleSigs.Instantiation.lookup then some procs[i]! else none)
        let mut hm := h
        for (st, sty) in steps do
          let (_, h') ← (← hm.assert `hstep sty st).intro1P
          hm := h'
        let h₀ := hm
        let h₁ ← (do
          let [h'] ← evalTacticAt (← `(tactic| simp only [Module.fst_pair, Module.snd_pair])) h₀
            | pure h₀
          pure h') <|> pure h₀
        let gs ← GaudisCrypt.FelInner.expDecrSplit' h₁
        for g' in gs do
          let rest ← evalTacticAt (← `(tactic| first
              | exact fun _ _ => rfl
              | exp_decr_write
              | exp_decr_write_fp)) g' <|> pure [g']
          for r in rest do
            r.setTag `oracle
            left := left.push r
    -- the code after the call: checked as the oracles are
    if let some gr ← byTag `hrest then
      setGoals ((← getGoals).filter (· != gr))
      let mut hm := gr
      for (st, sty) in steps do
        let (_, h') ← (← hm.assert `hstep sty st).intro1P
        hm := h'
      for g' in ← GaudisCrypt.FelInner.expDecrSplit' hm do
        let rest ← evalTacticAt (← `(tactic| first
            | exact fun _ _ => rfl
            | exp_decr_write
            | exp_decr_write_fp)) g' <|> pure [g']
        for r in rest do
          r.setTag `oracle
          left := left.push r
    -- the named procedures' premises (`FelProc.mk`)
    let mut prem : Array MVarId := #[]
    for fo in procGoals do
      -- (anonymous holes, tagged here: named ones would be shared between the procedures)
      let gs ← evalTacticAt (← `(tactic| refine FelProc.mk ?_ ?_ ?_ ?_ ?_)) fo
      for (g', t) in gs.zip [`lt, `step, `incr, `same, `keep] do g'.setTag t
      prem := prem ++ gs.toArray
    setGoals ((← getGoals) ++ prem.toList ++ left.toList)
    untagGoals
    -- EC needs no `lt` (its event bounds the counter): closed when it is arithmetic
    for _ in [0:ms.size] do
      closeTagged `lt (← `(tactic| (intro _ _ _ _; beta_reduce at *; simp only [Lens.pair] at *; (try simp only at *); omega)))
    -- EC's order: the sum, the initialization, the named procedures' premises, the rest
    let gs ← getGoals
    let order := [`sum, `init, `lt, `step, `incr, `same, `keep]
    let named ← order.filterMapM fun n => gs.findM? fun g => return (← g.getTag) == n
    setGoals (named ++ gs.filter (fun g => !named.contains g))
