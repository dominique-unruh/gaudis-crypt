import GaudisCrypt.Logic.PHoare
import GaudisCrypt.Logic.SyntacticFrame
import GaudisCrypt.Logic.Inline
import GaudisCrypt.Syntax.PHoareSyntax
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Syntax.CloneRegistry

/-!
# EasyCrypt's `proc`: a procedure judgment as the judgment about its body

    phoare_proc     -- EC's `proc` on `phoare[ M.f : P ==> Q ] ⋈ r`
    hoare_proc      -- EC's `proc` on `hoare[ M.f : P ==> Q ]`
    equiv_proc      -- EC's `proc` on `equiv[ M₁.f ~ M₂.g : P ==> Q ]`

The goal becomes the judgment about the procedure's body, its parameters local variables under
their own names, the postcondition read at the return value: no call, no copies of the arguments,
no reset of the callee's frame, so that EC's statement counts (`seq 1`, `wp 2`) are ours.

Sound as EC's `proc` is: the body's judgment is proven from **every** state whose parameter
variables hold the arguments, whatever the other locals hold (`phoareProc_of_body_anyLocals`);
the run of the procedure starts from one of them (its other locals at their initial values).  It is
unprovable only for a body reading a local before writing it, as in EC.
-/

namespace GaudisCrypt

/-- The expectation of a procedure is its body's, from its initial locals, read at the return
value (`Procedure.ewp_eq_body` for an expectation of the result too). -/
theorem Procedure.ewp_eq_body_ret {sig} (p : Procedure sig) (args : sig.ParamType)
    (G : sig.ret → VariableAssignment → ENNReal) (st : VariableAssignment) :
    p.ewp args G st =
      Stmt.ewp p.body (fun σ => G (p.return_val.get σ) σ.globals) ⟨st, p.initLocals args⟩ := by
  simp only [Procedure.ewp, Stmt.ewp, procedureDenotation, ProgramDenotation.wp,
    SubProbability.expected_hbind, expected_pure]

/-- **EC's `proc`** for `phoare`: the judgment about the body, from any state whose parameter
variables (`argsL`, read back from the initial locals by `hargs`) satisfy the precondition. -/
theorem phoareProc_of_body_anyLocals {sig} (argsL : Lens sig.ParamType VariableAssignment)
    {A : sig.ParamType → VariableAssignment → Prop} {p : Procedure sig}
    {G : sig.ret → VariableAssignment → ENNReal} {ρ : ENNReal → ENNReal → Prop}
    {r : sig.ParamType → VariableAssignment → ENNReal}
    (hargs : ∀ args, argsL.get (p.initLocals args) = args)
    (h : phoareStmt (fun σ => A (argsL.get σ.locals) σ.globals) p.body
      (fun σ => G (p.return_val.get σ) σ.globals) ρ (fun σ => r (argsL.get σ.locals) σ.globals)) :
    phoareProc A p G ρ r := by
  intro args st hA
  have := h ⟨st, p.initLocals args⟩ (by simpa only [hargs] using hA)
  simp only [hargs] at this
  rwa [Procedure.ewp_eq_body_ret]

/-- **EC's `proc`** for Hoare triples, as `phoareProc_of_body_anyLocals` (`hoareProc_of_body`,
from the initial locals only, with the precondition strengthened). -/
theorem hoareProc_of_body_anyLocals {sig} (argsL : Lens sig.ParamType VariableAssignment)
    {A : sig.ParamType → VariableAssignment → Prop} {p : Procedure sig}
    {B : sig.ret → VariableAssignment → Prop}
    (hargs : ∀ args, argsL.get (p.initLocals args) = args)
    (h : hoareStmt (fun σ => A (argsL.get σ.locals) σ.globals) p.body
      (fun σ => B (p.return_val.get σ) σ.globals)) :
    hoareProc A p B :=
  hoareProc_of_body fun a => hoare_pre h fun σ ⟨hA, hl⟩ => by rw [hl, hargs]; exact hA

/-- **EC's `proc`** for pRHL, as `phoareProc_of_body_anyLocals`: the judgment about the two bodies,
from any states whose parameter variables satisfy the precondition. -/
theorem prhlProc_of_body_anyLocals {sig₁ sig₂ : ProcedureSignature}
    {A : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop}
    {p₁ : Procedure sig₁} {p₂ : Procedure sig₂}
    {B : sig₁.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop}
    (argsL₁ : Lens sig₁.ParamType VariableAssignment)
    (argsL₂ : Lens sig₂.ParamType VariableAssignment)
    (hargs₁ : ∀ args, argsL₁.get (p₁.initLocals args) = args)
    (hargs₂ : ∀ args, argsL₂.get (p₂.initLocals args) = args)
    (h : prhlStmt
      (fun σ₁ σ₂ => A (argsL₁.get σ₁.locals) σ₁.globals (argsL₂.get σ₂.locals) σ₂.globals)
      p₁.body p₂.body
      (fun σ₁ σ₂ => B (p₁.return_val.get σ₁) σ₁.globals (p₂.return_val.get σ₂) σ₂.globals)) :
    prhlProc A p₁ p₂ B := by
  intro a₁ a₂ g₁ g₂ hA
  let σ₁ : ProgramState := ⟨g₁, p₁.initLocals a₁⟩
  let σ₂ : ProgramState := ⟨g₂, p₂.initLocals a₂⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := h σ₁ σ₂ (by simpa only [σ₁, σ₂, hargs₁, hargs₂] using hA)
  refine ⟨μ >>= fun x => pure ((p₁.return_val.get x.1.2, x.1.2.globals),
    (p₂.return_val.get x.2.2, x.2.2.globals)), ?_, ?_, ?_⟩
  · refine SubProbability.marginal_fst_eq fun F => ?_
    rw [SubProbability.expected_map, SubProbability.expected_fst_of_marginal hm1
      (fun u => F (p₁.return_val.get u.2, u.2.globals))]
    simp only [procedureDenotation, SubProbability.expected_hbind, expected_pure, σ₁]
  · refine SubProbability.marginal_snd_eq fun F => ?_
    rw [SubProbability.expected_map, SubProbability.expected_snd_of_marginal hm2
      (fun u => F (p₂.return_val.get u.2, u.2.globals))]
    simp only [procedureDenotation, SubProbability.expected_hbind, expected_pure, σ₂]
  · exact SubProbability.satisfies_bind _ fun x hx => SubProbability.satisfies_pure _ _ (hsat x hx)

namespace ECProc

open Lean Meta Elab Tactic PRHLWp

/-- One procedure, prepared for EC's `proc`: its literal `p'` (`Flatten.unfoldProcedure`, `proof`
of `p = p'`), body, return value, the lens of its parameter variables over the locals and their
slots in the program state, and the proof that the lens reads the arguments back from the
initial locals. -/
structure Side where
  p : Lean.Expr
  p' : Lean.Expr
  proof? : Option Lean.Expr
  body : Lean.Expr
  ret : Lean.Expr
  argsVA : Lean.Expr
  argSlots : List Lean.Expr
  hargs : Lean.Expr
deriving Inhabited

/-- `Side` of the procedure `p` of signature `sig`. -/
def side (sig p : Lean.Expr) : MetaM Side := do
  let rp ← Flatten.unfoldProcedure p
  let p' ← instantiateMVars rp.expr
  unless p'.isAppOfArity ``ProcedureWithHoles.mk 7 do
    throwError "proc: no literal procedure for{indentExpr p}"
  let some tys ← ModuleDecl.listLit? (← whnf (mkApp (mkConst ``ProcedureSignature.params) sig))
    | throwError "proc: the parameter list of{indentExpr sig}\nis not a list literal"
  let names ← procParamNames p' tys.length
  let slots ← (names.toList.zip tys).mapM fun (n, T) => mkVarSlots n T
  let argsVA ← mkTupleLens (mkConst ``VariableAssignment) (slots.map (·.1))
  let paramTy := mkApp (mkConst ``ProcedureSignature.ParamType) sig
  let hargsTy ← withLocalDeclD `args paramTy fun a => do
    let lhs ← mkLensGet argsVA (← mkAppM ``ProcedureWithHoles.initLocals #[p', a])
    mkForallFVars #[a] (← mkEq lhs a)
  let hargs ← mkFreshExprSyntheticOpaqueMVar hargsTy
  -- the arguments taken apart (`setParams` is by cases on the tuple), the slots compared by their
  -- keys (the literal ones of the lens, `setParams`'s `encode n`)
  let argsId := mkIdent `args
  let ids := (Array.range tys.length).map fun i => mkIdent (.mkSimple s!"a{i}")
  let simpTac ← `(tactic| simp (config := { decide := true }) [ProcedureWithHoles.initLocals,
    VariableAssignment.setParams, Lens.pair, varLens_set, Function.update_apply])
  let tac ← match tys.length with
    | 0 => `(tactic| (intro _; rfl))
    | 1 => `(tactic| (intro $argsId:ident; $simpTac))
    | _ => `(tactic| (intro $argsId:ident; obtain ⟨$[$ids],*⟩ := $argsId:ident; $simpTac))
  let [] ← Term.TermElabM.run' (Tactic.run hargs.mvarId! (evalTactic tac))
    | throwError "proc: could not read the parameters back:{indentExpr hargsTy}"
  let hargs ← instantiateMVars hargs
  return ⟨p, p', rp.proof?, p'.getArg! 5, p'.getArg! 6, argsVA, slots.map (·.2), hargs⟩

/-- EC's `proc` on the goal `g`: a `phoareProc`, `hoareProc` or `prhlProc` judgment becomes the
judgment about the bodies (`phoareProc_of_body_anyLocals`, `hoareProc_of_body_anyLocals`,
`prhlProc_of_body_anyLocals`), the conditions in the shape the statement notation builds (as
`hoareProcToStmt` does).  The new goal is returned. -/
def procStep (g : MVarId) : MetaM MVarId := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let args := ty.getAppArgs
  let ps := mkConst ``ProgramState
  let globalsOf (σ : Lean.Expr) := mkAppM ``ProgramState.globals #[σ]
  -- the judgment's kind: rule, positions of the procedures and signatures
  let (rule, procPos, sigPos) ←
    if ty.isAppOfArity ``phoareProc 6 then pure (``phoareProc_of_body_anyLocals, [2], [0])
    else if ty.isAppOfArity ``hoareProc 4 then pure (``hoareProc_of_body_anyLocals, [2], [0])
    else if ty.isAppOfArity ``prhlProc 6 then pure (``prhlProc_of_body_anyLocals, [3, 4], [0, 1])
    else throwError "proc: expected a procedure judgment (`phoare[ M : P ==> Q ] ⋈ r`, \
      `hoare[ M : P ==> Q ]`, `equiv[ M₁ ~ M₂ : P ==> Q ]`), got{indentExpr ty}"
  let sides ← (procPos.zip sigPos).mapM fun (i, j) => side args[j]! args[i]!
  -- the judgment about the bodies
  let rhs ← if ty.isAppOf ``prhlProc then do
      let #[s₁, s₂] := sides.toArray | unreachable!
      let cond (C : Lean.Expr) (v₁ v₂ : Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr :=
        withLocalDeclD `σ₁ ps fun σ₁ => withLocalDeclD `σ₂ ps fun σ₂ => do
          let c := C.beta #[← v₁ σ₁, ← globalsOf σ₁, ← v₂ σ₂, ← globalsOf σ₂]
          mkLambdaFVars #[σ₁, σ₂] (← reduceArgProjections (← zetaReduce c))
      let pre ← cond args[2]! (mkTupleRead · s₁.argSlots) (mkTupleRead · s₂.argSlots)
      let post ← cond args[5]! (fun σ => mkAppM ``Getter.get #[s₁.ret, σ])
        (fun σ => mkAppM ``Getter.get #[s₂.ret, σ])
      mkAppM ``prhlStmt #[pre, s₁.body, s₂.body, post]
    else do
      let s := sides.head!
      let cond (C : Lean.Expr) (val : Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr := do
        let f ← withLocalDeclD `σ ps fun σ => do
          let c := C.beta #[← val σ, ← globalsOf σ]
          mkLambdaFVars #[σ] (← reduceArgProjections (← zetaReduce c))
        mkAppM ``Getter.get #[← ProgramSyntax.getterViaState f]
      let readArgs := (mkTupleRead · s.argSlots)
      let readRet := fun σ => mkAppM ``Getter.get #[s.ret, σ]
      let pre ← cond args[1]! readArgs
      if ty.isAppOf ``phoareProc then
        mkAppM ``phoareStmt #[pre, s.body, ← cond args[3]! readRet, args[4]!,
          ← cond args[5]! readArgs]
      else mkAppM ``hoareStmt #[pre, s.body, ← cond args[3]! readRet]
  -- the rule at the literals: its conclusion, then the lenses, the read-backs and the new goal by
  -- their names
  let c ← mkConstWithFreshMVarLevels rule
  let cTy ← inferType c
  let names := cTy.getForallBinderNames
  let (ms, _, concl) ← forallMetaTelescope cTy
  let tyLit := mkAppN ty.getAppFn
    ((procPos.zip sides).foldl (fun a (i, s) => a.set! i s.p') args)
  unless ← isDefEq concl tyLit do throwError "proc: the rule does not fit{indentExpr tyLit}"
  let arg (n : Name) : MetaM Lean.Expr := do
    let some i := names.findIdx? (· == n) | throwError "proc: `{rule}` has no argument `{n}`"
    return ms[i]!
  let suffixes := if sides.length == 1 then [""] else ["₁", "₂"]
  for (s, sfx) in sides.zip suffixes do
    unless ← isDefEq (← arg (.mkSimple s!"argsL{sfx}")) s.argsVA do
      throwError "proc: the parameter lens does not fit"
    unless ← isDefEq (← arg (.mkSimple s!"hargs{sfx}")) s.hargs do
      throwError "proc: the parameters' read-back does not fit"
  let h ← arg `h
  unless ← isDefEq (← inferType h) rhs do
    throwError "proc: the bodies' judgment{indentExpr rhs}\nis not the rule's\
      {indentExpr (← inferType h)}"
  let g' ← mkFreshExprSyntheticOpaqueMVar rhs (← g.getTag)
  h.mvarId!.assign g'
  -- back from the literals to the procedures, one side at a time
  let mut pf ← instantiateMVars (mkAppN c ms)
  let mut cur := (procPos.zip sides).foldl (fun a (i, s) => a.set! i s.p') args
  for (i, s) in (procPos.zip sides).reverse do
    if let some e := s.proof? then
      let before := cur.set! i s.p
      let motive ← withLocalDeclD `q (← inferType s.p) fun q =>
        mkLambdaFVars #[q] (mkAppN ty.getAppFn (before.set! i q))
      pf ← mkEqMPR (← mkCongrArg motive e) pf
      cur := before
    else cur := cur.set! i s.p
  g.assign pf
  -- a relational judgment's conditions simplified as `equiv_proc_to_stmt` does
  if ty.isAppOf ``prhlProc then
    let g'' ← Judgment.simpArg g'.mvarId! 0 relSimpDecls []
    return ← Judgment.simpArg g'' 3 relSimpDecls []
  return g'.mvarId!

/-- A module's procedure read off a module built from a record (`DPRIMITIVE.f (DPRIMITIVE.mk
{ f := P.f, … })`, what a module type's view leaves at a call) or out of a `Module.pair`, read off
(`T.f.mk_simp`, `Module.fst_pair'`, …) everywhere in the goal: the two sides of a call then name
the same procedure (`P.f`), as EC's `sim` sees them. -/
def accessorNorm (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let readOff? (e : Lean.Expr) : MetaM (Option Simp.Result) := do
    let some c := e.getAppFn.constName? | return none
    let args := e.getAppArgs
    if args.isEmpty then return none
    let acc := (← Flatten.isAccessor c) && args.back!.isAppOf (c.getPrefix ++ `mk)
    unless acc || (Flatten.pairLemma? c).isSome do return none
    Flatten.moduleStep? e
  let pre : Simp.Simproc := fun e => do
    if let some r ← readOff? e then return .visit r
    -- the accessor under a clone's alias (`Indiff.DPRIMITIVE.f`): the theory's, by definition
    let some c := e.getAppFn.constName? | return .continue
    if (cloneOf? (← getEnv) c).isNone then return .continue
    let some e' ← Meta.unfoldDefinition? e | return .continue
    let e' := e'.headBeta
    let some r ← readOff? e' | return .continue
    return .visit r
  let ctx ← Simp.mkContext (config := { zeta := false, iota := false, proj := false })
  let (r, _) ← Simp.main ty ctx (methods := { pre })
  if r.expr == ty then return g
  applySimpResultToTarget g ty r

end ECProc

open Lean Elab Tactic in
/-- **EC's `proc`** on `phoare[ M.f : P ==> Q ] ⋈ r`: see the module docstring. -/
elab "phoare_proc" : tactic => do
  -- EC's `proc` on `islossless M`: the `phoare` judgment it is
  let g ← getMainGoal
  if (← instantiateMVars (← g.getType)).cleanupAnnotations.isAppOf ``Procedure.IsLossless then
    evalTactic (← `(tactic| rw [Procedure.isLossless_iff_phoareProc]))
  liftMetaTactic1 fun g => some <$> (ECProc.procStep g >>= ECProc.accessorNorm)

open Lean Elab Tactic in
/-- **EC's `proc`** on `hoare[ M.f : P ==> Q ]`: see the module docstring. -/
elab "hoare_proc" : tactic => liftMetaTactic1 fun g =>
  some <$> (ECProc.procStep g >>= ECProc.accessorNorm)

open Lean Elab Tactic in
/-- **EC's `proc`** on `equiv[ M₁.f ~ M₂.g : P ==> Q ]`: see the module docstring. -/
elab "equiv_proc" : tactic => liftMetaTactic1 fun g =>
  some <$> (ECProc.procStep g >>= ECProc.accessorNorm)

end GaudisCrypt
