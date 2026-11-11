import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.Inline
import GaudisCrypt.Logic.EqualOutside
import GaudisCrypt.Syntax.CloneRegistry
import GaudisCrypt.Logic.ECSimGlob
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Lib.EC.DProd
import GaudisCrypt.Logic.LensWriteNorm

/-!
# EasyCrypt's `inline*` and `sim`

    stmt_inline*     -- EC's `inline*`: every call whose callee is spelled out, on both sides
    stmt_inline*{i}  -- … on side `i`
    phoare_inline*, hoare_inline*
    sim              -- EC's `sim`, on a relational judgment about two statements

`inline*` inlines call sites until only calls of abstract procedures are left (EC's `inline*`,
which does not inline a declared module either).

`sim` goes backwards over the two statements, computing the relation needed before each step
from the one needed after it, as EC's `sim` does with its sets of equal variables, but with any
relation: deterministic code on either side by wp (`stmt_wp`: copies, dead assignments and
the frame resets of inlined calls disappear into the relation), samplings on both sides
coupled by the identity (`equiv_rnd`), calls of the same procedure on both sides from equal
arguments and globals (`equiv_call`), conditionals on both sides (`prhlStmt_seq_if_bwd`):
equal guards, each branch's relation found by `sim` on the branches (a branch it does not
finish stops it at the conditional), and loops on both sides (`prhlStmt_seq_while`): EC's
equality set as the invariant (the relation after the loops and the variables they mention
equal), the bodies by `sim`.  Where both statements are used up, the precondition must imply
what is left (`equiv_skip`), closed by `simp_all` if it can; anything else (calls of different
procedures, a sampling against other code) stops `sim` with that goal.
-/

namespace GaudisCrypt

section Rules

variable {A Aₜ Aₑ B : ProgramState → ProgramState → Prop} {c₁ c₂ : Getter Bool ProgramState}
  {s₁ s₂ t₁ t₂ e₁ e₂ : Stmt}

/-- **Conditionals on both sides, backwards** (EC's `sim` on `if`s): the branches related from
`Aₜ` and `Aₑ`, and before the conditionals equal guards and the branch's relation.  The branches'
judgments come first, so that their relations are found before the code before them is
processed. -/
theorem prhlStmt_seq_if_bwd (ht : prhlStmt Aₜ t₁ t₂ B) (he : prhlStmt Aₑ e₁ e₂ B)
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ => c₁.get σ₁ = c₂.get σ₂ ∧
      (c₁.get σ₁ = true → Aₜ σ₁ σ₂) ∧ (c₁.get σ₁ = false → Aₑ σ₁ σ₂)) :
    prhlStmt A (.seq s₁ (.ifThenElse c₁ t₁ e₁)) (.seq s₂ (.ifThenElse c₂ t₂ e₂)) B := by
  refine prhlStmt_seq (prhlStmt_if (fun _ _ h => h.1) ?_ ?_) h
  · exact prhlStmt_pre ht fun _ _ h => h.1.2.1 h.2
  · exact prhlStmt_pre he fun _ _ h => h.1.2.2 h.2

/-- **Calls of the same procedure, the states equal outside `L`** (EC's `sim` with `={glob A}`):
a module `M` that does not touch `L`, called on both sides with equal arguments from states equal
outside `L`, returns the same result in states again equal outside `L`, each with its `L` as it
was (`prhlProc_self_equal_outside_module`): after the call, the same globals `g` on both sides
but for each side's own `L`. -/
theorem prhlStmt_seq_call_outside {Ω : Type} (L : Lens Ω VariableAssignment)
    {sig : ProcedureSignature} {M : Module.Proc sig} (hM : FVP.fvP M ≤ (L.footprint)ᶜ)
    {x₁ x₂ : Setter sig.ret ProgramState} {e₁ e₂ : Getter sig.ParamType ProgramState}
    (hpre : prhlStmt A s₁ s₂ fun σ₁ σ₂ => e₁.get σ₁ = e₂.get σ₂ ∧
      L.equal_outside σ₁.globals σ₂.globals ∧
      ∀ r g, B (x₁.set r (ProgramState.globalL.set (L.set (L.get σ₁.globals) g) σ₁))
        (x₂.set r (ProgramState.globalL.set (L.set (L.get σ₂.globals) g) σ₂))) :
    prhlStmt A (.seq s₁ (Stmt.call x₁ M.procedure e₁)) (.seq s₂ (Stmt.call x₂ M.procedure e₂)) B := by
  refine prhlStmt_seq (B := fun σ₁ σ₂ => _) ?_ hpre
  intro σ₁ σ₂ ⟨he, hL, hB⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := prhlProc_self_equal_outside_module L M hM
    (fun l₁ l₂ => l₁ = L.get σ₁.globals ∧ l₂ = L.get σ₂.globals)
    (e₁.get σ₁) (e₂.get σ₂) σ₁.globals σ₂.globals ⟨he, hL, rfl, rfl⟩
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
  · refine SubProbability.satisfies_bind _ fun w hw => SubProbability.satisfies_pure _ _ ?_
    obtain ⟨hr, ⟨x, hx⟩, h1, h2⟩ := hsat w hw
    have e₁ : w.1.2 = L.set (L.get σ₁.globals) w.1.2 := by rw [← h1, L.get_set]
    have e₂ : w.2.2 = L.set (L.get σ₂.globals) w.1.2 := by
      rw [← hx, ← h2, ← hx, L.set_get]
    simp only
    rw [← hr, e₂]
    conv => arg 1; rw [e₁]
    exact hB _ _

end Rules

/-- States equal outside `L` as an equation: the second is the first with the second's `L`
written (so that `sim`'s implications are about chains of writes, `lensWriteNorm`). -/
theorem Lens.equal_outside_iff_set {Ω : Type} (L : Lens Ω VariableAssignment)
    (g₁ g₂ : VariableAssignment) : L.equal_outside g₁ g₂ ↔ L.set (L.get g₂) g₁ = g₂ := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [L.set_get]
  · exact fun h => ⟨L.get g₂, h⟩


namespace ECSim

open Lean Meta Elab Tactic PRHLWp

/-- EC's `inline*` on side `side?` of the goal `g` (a registered judgment): call sites inlined
(`Flatten.judgmentInline`) until every one left fails (an abstract procedure). -/
def inlineAll (g : MVarId) (side? : Option Nat) : MetaM MVarId := do
  let mut g := g
  -- rounds: a call through a view of a concrete module (`PRIMITIVE.init Perm`, `Perm` a record
  -- of another module type) is read off by `ECProc.accessorNorm` (EC's structural subtyping),
  -- then inlined
  for _ in [0:8] do
    let mut k := 0
    for _ in [0:500] do
      let (d, ty) ← Judgment.descOf g side?
      let n ← Flatten.countCallSites (ty.getArg! d.stmtArg)
      if k ≥ n then break
      let s ← saveState
      try g ← Flatten.judgmentInline k g side?
      catch _ =>
        s.restore
        k := k + 1
    let g' ← try ECProc.accessorNorm g catch _ => pure g
    if g' == g then break
    g := g'
  return g

/-- `inlineAll` on both sides of a relational judgment, or on the one statement. -/
def inlineAllSides (g : MVarId) (side? : Option Nat) : MetaM MVarId := do
  let (descs, _) ← Judgment.descsOf g
  if side?.isNone && descs.size == 2 then
    inlineAll (← inlineAll g (some 1)) (some 2)
  else inlineAll g side?

/-- The kind of the last statement of `s`: `skip`, a conditional, a call, a sampling, or other. -/
inductive Last | skip | cond | call | sample | loop | other
  deriving BEq

/-- The last statement of the right-nested `s` (after `stripLets`). -/
partial def lastOf (s : Lean.Expr) : Lean.Expr :=
  let s := stripLets s
  if s.isAppOf ``StmtWithHoles.seq then
    let l := lastOf (s.getArg! 2)
    if (stripLets l).isAppOf ``StmtWithHoles.skip then lastOf (s.getArg! 1) else l
  else s

/-- The kind of the last statement of `s`. -/
def lastKind (s : Lean.Expr) : MetaM Last := do
  let l := stripLets (lastOf s)
  if l.isAppOf ``StmtWithHoles.skip then return .skip
  if l.isAppOf ``StmtWithHoles.ifThenElse then return .cond
  if l.isAppOf ``StmtWithHoles.call' || l.isAppOf ``Stmt.call || l.isAppOf ``StmtWithHoles.call
    then return .call
  if l.isAppOf ``StmtWithHoles.sample then return .sample
  if l.isAppOf ``StmtWithHoles.while then return .loop
  -- a call spelled through a definition
  if let some l' ← unfoldDefinition? l then
    if l'.isAppOf ``StmtWithHoles.call' then return .call
  return .other

/-- Close `∀ …, A → B` (what `equiv_skip` leaves) by `simp_all`, if it can. -/
def closeImp (g : MVarId) : TacticM (List MVarId) := do
  let s ← saveState
  -- the reads through writes to the state (`HoareWp.simpReadsDecls`: locals past resets and
  -- writes to globals, …), for the local copies inlining leaves (`hash0 <- §DPre.h`)
  let reads : Array Ident := (HoareWp.simpReadsDecls.map mkIdent).toArray ++
    #[mkIdent ``Setter.throwaway, mkIdent ``lensWriteNorm]
  let readsTac ← `(tactic| simp_all (config := { decide := true }) [$[$reads:ident],*])
  try
    let gs ← evalTacticAt (← `(tactic| first
      | (intros; subst_vars; simp_all; done)
      | (intros; subst_vars; simp_all [lensWriteNorm]; done)
      | (intros
         -- states equal outside a frame: an equation of chains of writes
         simp only [Lens.equal_outside_iff_set] at *
         simp_all [Lens.set_get, Lens.get_of_disjoint_set, lensWriteNorm]; done)
      | (intros
         -- … with the same conditional writes on both sides, once the hypotheses are substituted
         simp only [Lens.equal_outside_iff_set] at *
         casesm* _ ∧ _
         subst_vars
         split_ifs <;> simp_all [Lens.set_get, Lens.get_of_disjoint_set, lensWriteNorm]; done)
      | (intros; simp_all [Setter.throwaway, ProgramState.globalL, lensWriteNorm]; done)
      | (intros; subst_vars; $readsTac:tactic; done)
      | (intros
         -- states agreeing on `glob A` and some variables (EC's `={glob A, x}`, the invariant
         -- `globInvF` of an abstract call): `glob A` past the writes outside it (`fp_disjoint`),
         -- the writes read through
         simp only [globInvF, Prod.mk.injEq] at *
         (try simp (disch := fp_disjoint) only [touched_set_of_le_compl])
         simp_all (config := { contextual := true }) [Lens.set_get, Lens.get_of_disjoint_set,
           Setter.throwaway, ProgramState.globalL]
         done)
      | (intros
         -- … the variables' equations substituted first, the conditional writes split
         simp only [globInvF, Prod.mk.injEq] at *
         casesm* _ ∧ _
         (try split_ifs) <;> (try simp (disch := fp_disjoint) only [touched_set_of_le_compl]) <;>
           simp_all (config := { contextual := true }) [Lens.set_get, Lens.get_of_disjoint_set,
             Setter.throwaway, ProgramState.globalL]
         done))) g
    if gs.isEmpty then return [] else s.restore; return [g]
  catch _ => s.restore; return [g]

/-- Run the tactic `stx` on `g`, the goals it leaves. -/
def runOn (g : MVarId) (stx : TSyntax `tactic) : TacticM (List MVarId) := evalTacticAt stx g

/-- EC's equality set of a relational precondition `A` (`fun σ₁ σ₂ => …`): the regions it keeps
equal (`R.touched_getter.get σ₁.globals = …`) and the global variables it reads. -/
def eqSetOf (A : Lean.Expr) : MetaM (Array Lean.Expr × Array Lean.Expr) := do
  let A ← instantiateMVars A
  if A.getAppFn.isMVar then return (#[], #[])
  let ps := mkConst ``ProgramState
  withLocalDeclD `σ₁ ps fun σ₁ => withLocalDeclD `σ₂ ps fun σ₂ => do
    let body := (mkApp2 A σ₁ σ₂).headBeta
    let Rs ← IO.mkRef (#[] : Array Lean.Expr)
    let xs ← IO.mkRef (#[] : Array Lean.Expr)
    Meta.forEachExpr body fun e => do
      if e.isAppOfArity ``Getter.get 4 then
        let G := e.getArg! 2
        if G.isAppOf ``Footprint.touched_getter then
          let R := G.appArg!
          let local_ := R.containsFVar σ₁.fvarId! || R.containsFVar σ₂.fvarId!
          unless local_ || (← Rs.get).contains R do Rs.modify (·.push R)
        else if G.isAppOfArity ``Lens.toGetter 3 then
          let x := G.getArg! 2
          let t ← whnfR (← inferType x)
          if t.isAppOfArity ``Lens 2 && (t.getArg! 1).isConstOf ``VariableAssignment &&
              !(x.containsFVar σ₁.fvarId! || x.containsFVar σ₂.fvarId!) &&
              !(← xs.get).contains x then
            xs.modify (·.push x)
    return (← Rs.get, ← xs.get)

/-- EC's `sim` through a call with an equality set: when the judgment's precondition keeps a
region `R` equal (`R.touched_getter.get σ₁.globals = R.touched_getter.get σ₂.globals`) that
contains the callee `M` (`fp_le`), the call rule `prhlStmt_seq_call_glob`, its frames the global
variables the precondition or the postcondition reads that `M` does not touch (`fp_disjoint`).
`none` if no region fits. -/
def callGlob (g : MVarId) (eqset : Array Lean.Expr × Array Lean.Expr) :
    TacticM (Option MVarId) := g.withContext do
  let s ← saveState
  try
    let g ← HoareSplit.hoareSplit 1 g
    let ty ← prhlGoal g "sim"
    -- the callee `M` (`M.procedure`) of the left side's last statement
    let st ← TacticMisc.openStmt (ty.getArg! 1)
    let last ← if st.isAppOfArity ``StmtWithHoles.seq 3 then TacticMisc.openStmt (st.getArg! 2)
      else pure st
    unless last.isAppOf ``Stmt.call || last.isAppOf ``StmtWithHoles.call do
      throwError "sim: not a call"
    let p := last.getArg! (last.getAppNumArgs - 2)
    unless p.isAppOf ``Module.Proc.procedure do throwError "sim: not a module's procedure"
    let M := p.appArg!
    let (Rs, xs) := eqset
    -- EC's call keeps every variable outside the callee: the frames also cover what the
    -- postcondition reads
    let (_, ys) ← eqSetOf (ty.getArg! 3)
    let xs := xs ++ ys.filter (!xs.contains ·)
    -- the region containing the callee
    let MS ← Term.exprToSyntax M
    let mut R? : Option Lean.Expr := none
    for R in Rs do
      let RS ← Term.exprToSyntax R
      let s' ← saveState
      try
        let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[← mkAppM ``FVP.fvP #[M], R])
        let [] ← runOn m.mvarId! (← `(tactic| fp_le)) | failure
        let _ := RS
        R? := some R
        break
      catch _ => s'.restore
    -- none given (plain `sim`): EC's equality set for the call, the variables read after it that
    -- the callee touches (`F.RO.m` for `RO.get`), as one region
    if R?.isNone then
      let mut zs : Array Term := #[]
      for x in xs do
        let s' ← saveState
        let outside ← try
            let m ← mkFreshExprSyntheticOpaqueMVar
              (← mkAppM ``LE.le #[← mkAppM ``Lens.footprint #[x],
                ← mkAppM ``Compl.compl #[← mkAppM ``FVP.fvP #[M]]])
            let [] ← runOn m.mvarId! (← `(tactic| fp_disjoint)) | failure
            pure true
          catch _ => pure false
        s'.restore
        unless outside do zs := zs.push (← `(Lens.footprint $(← Term.exprToSyntax x)))
      if let some last := zs.back? then
        let RS ← zs.pop.foldrM (fun z acc => `($z ⊔ $acc)) last
        let R ← Term.elabTerm RS (some (← mkAppM ``Footprint #[mkConst ``VariableAssignment]))
        Term.synthesizeSyntheticMVarsNoPostponing
        let R ← instantiateMVars R
        let s' ← saveState
        try
          let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[← mkAppM ``FVP.fvP #[M], R])
          let [] ← runOn m.mvarId! (← `(tactic| fp_le)) | failure
          R? := some R
        catch _ => s'.restore
    let some R := R? | throwError "sim: no region contains the callee"
    -- the frames: the variables read that `M` does not touch
    let mut frames : Array Term := #[]
    for x in xs do
      let XS ← Term.exprToSyntax x
      let s' ← saveState
      try
        let m ← mkFreshExprSyntheticOpaqueMVar
          (← mkAppM ``LE.le #[← mkAppM ``Lens.footprint #[x],
            ← mkAppM ``Compl.compl #[← mkAppM ``FVP.fvP #[M]]])
        let [] ← runOn m.mvarId! (← `(tactic| fp_disjoint)) | failure
        frames := frames.push (← `(Module.Proc.frame_lens $XS (by fp_disjoint)))
      catch _ => s'.restore
    let fr ← match frames.back? with
      | none => `(Module.Proc.frame_true _)
      | some l => frames.pop.foldrM (fun f acc => `(Module.Proc.frame_and $f $acc)) l
    -- the rule, its arguments by hand: `R`, `M`, the bound (`fp_le`), the frame
    let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_call_glob
    let cTy ← inferType c
    let names := cTy.getForallBinderNames
    let (ms, _, concl) ← forallMetaTelescope cTy
    let idx (n : Name) : TacticM Nat := do
      let some i := names.findIdx? (· == n) | throwError "sim: no argument `{n}`"
      return i
    unless ← isDefEq ms[← idx `R]! R do throwError "sim: R"
    unless ← isDefEq ms[← idx `M]! M do throwError "sim: M"
    unless ← isDefEq concl (← g.getType) do throwError "sim: the call rule does not apply"
    let hM := ms[← idx `hM]!.mvarId!
    let [] ← runOn hM (← `(tactic| fp_le)) | throwError "sim: the callee is not in the region"
    let hFrM := ms[← idx `hFr]!
    let hFr ← Term.elabTermEnsuringType fr (← instantiateMVars (← inferType hFrM))
    Term.synthesizeSyntheticMVarsNoPostponing
    unless ← isDefEq hFrM (← instantiateMVars hFr) do throwError "sim: the frame"
    g.assign (mkAppN c ms)
    let hp := ms[← idx `hpre]!.mvarId!
    hp.setKind .syntheticOpaque
    return some (← Judgment.simpArg hp 3 relSimpDecls [])
  catch _ => s.restore; return none

/-- The program variables the statements `ss` mention: the locals (`localVarLens`, of the
program state) and the global variables (`global_var`s, of the globals, or a clone's alias of one,
`FRO.m := ROhandle.FRO.m`, as written), in order. -/
def varsOf (ss : Array Lean.Expr) : MetaM (Array Lean.Expr × Array Lean.Expr) := do
  let env ← getEnv
  let locals ← IO.mkRef (#[] : Array Lean.Expr)
  let globals ← IO.mkRef (#[] : Array Lean.Expr)
  for s in ss do
    Meta.forEachExpr (← instantiateMVars s) fun e => do
      -- (free variables are allowed: the section's instances, `[SLCommon.Params]`)
      if e.hasLooseBVars then return
      let some c := e.getAppFn.constName? | return
      if c == ``localVarLens || (c == ``Lens.intoLocal && e.isApp && e.appArg!.isAppOf ``varLens) then
        -- fully applied (the last argument is a proof of the name's key)
        let t ← whnfR (← inferType e)
        if t.isAppOfArity ``Lens 2 && !(← locals.get).contains e then locals.modify (·.push e)
      else if DeclareModule.isGlobalVar env c || (← isGlobalAlias env c e) then
        let t ← whnfR (← inferType e)
        if t.isAppOfArity ``Lens 2 && (t.getArg! 1).isConstOf ``VariableAssignment then
          unless (← globals.get).contains e do globals.modify (·.push e)
  return (← locals.get, ← globals.get)
where
  /-- `e` (headed by `c`) a reducible alias of a global variable. -/
  isGlobalAlias (env : Environment) (c : Name) (e : Lean.Expr) : MetaM Bool := do
    unless (← getReducibilityStatus c) == .reducible do return false
    let e' ← whnfR e
    let some c' := e'.getAppFn.constName? | return false
    return c' != c && DeclareModule.isGlobalVar env c'

/-- `set_option debug.sim true`: `sim` reports why it stops at two loops. -/
register_option debug.sim : Bool := {
  defValue := false
  descr := "sim: report why it stops at two loops"
}

/-- A set of program variables: the local slots and the globals (as `varsOf` returns them). -/
abbrev VarSet := Array Lean.Expr × Array Lean.Expr

/-- `x` among `xs`, as a variable (`lensKey`: a local's two spellings are one variable). -/
private def containsVar (xs : Array Lean.Expr) (x : Lean.Expr) : MetaM Bool := do
  let k ← lensKey x
  xs.anyM fun y => return (← lensKey y) == k

private def vsUnion (a b : VarSet) : MetaM VarSet := do
  let mut (ls, gs) := a
  for x in b.1 do unless ← containsVar ls x do ls := ls.push x
  for x in b.2 do unless ← containsVar gs x do gs := gs.push x
  return (ls, gs)

private def vsDiff (a b : VarSet) : MetaM VarSet :=
  return (← a.1.filterM fun x => return !(← containsVar b.1 x),
    ← a.2.filterM fun x => return !(← containsVar b.2 x))

private def vsMeets (a b : VarSet) : MetaM Bool :=
  return (← a.1.anyM (containsVar b.1)) || (← a.2.anyM (containsVar b.2))

/-- **EC's equality sets, backwards**: the variables that must be equal on the two sides before
`s` (run on both) for those of `S` to be equal after it.  An assignment or sampling to variables
of `S` replaces them by what it reads (otherwise it does not matter); a conditional adds its
guard; a loop the fixpoint of its body with its guard; anything else (a call, a hole) everything
it mentions. -/
partial def eqBack (s : Lean.Expr) (S : VarSet) : MetaM VarSet := do
  let s := stripLets (← instantiateMVars s)
  let args := s.getAppArgs
  let last (k : Nat) : Lean.Expr := args[args.size - k]!
  match s.getAppFn.constName? with
  | some ``StmtWithHoles.skip => return S
  | some ``StmtWithHoles.seq => eqBack (last 2) (← eqBack (last 1) S)
  | some ``StmtWithHoles.ifThenElse =>
    let t ← eqBack (last 2) S
    let e ← eqBack (last 1) S
    vsUnion (← vsUnion (← varsOf #[last 3]) t) e
  | some ``StmtWithHoles.while =>
    let c ← varsOf #[last 2]
    let mut I ← vsUnion S c
    for _ in [0:20] do
      let I' ← vsUnion I (← eqBack (last 1) I)
      if I'.1.size == I.1.size && I'.2.size == I.2.size then return I'
      I := I'
    return I
  | some ``StmtWithHoles.sample | some ``StmtWithHoles.assign =>
    let W ← varsOf #[last 2]
    if ← vsMeets W S then vsUnion (← vsDiff S W) (← varsOf #[last 1]) else return S
  | _ => vsUnion S (← varsOf #[s])

/-- EC's `sim` invariant of two loops: the relation `B` after them, and the variables both loops
mention equal on the two sides (a variable of one side only — `Perm.m` against `PRPi.m`, EC's
`sim (_: ={m,mi}(Perm,PRPi))` — is related by `B`, if at all). -/
def loopInv (B : Lean.Expr) (loops : Array Lean.Expr) : MetaM Lean.Expr := do
  let (ls, gs) ← if h : loops.size = 2 then do
      let (ls₁, gs₁) ← varsOf #[loops[0]]
      let (ls₂, gs₂) ← varsOf #[loops[1]]
      -- of those, the ones `B` and the loops need (EC's equality set, `eqBack`): not a local the
      -- body writes before reading it (an inlined callee's `x0`, named differently on the sides)
      let SB ← varsOf #[B]
      let (nl, ng) ← vsUnion (← eqBack loops[0] SB) (← eqBack loops[1] SB)
      pure (← ls₁.filterM fun x => return (← containsVar ls₂ x) && (← containsVar nl x),
        ← gs₁.filterM fun x => return (← containsVar gs₂ x) && (← containsVar ng x))
    else varsOf loops
  let ps := mkConst ``ProgramState
  withLocalDeclD `σ₁ ps fun σ₁ => withLocalDeclD `σ₂ ps fun σ₂ => do
    let get (x st : Lean.Expr) : MetaM Lean.Expr := do
      mkAppM ``Getter.get #[← mkAppM ``Lens.toGetter #[x], st]
    let mut eqs : Array Lean.Expr := #[]
    for x in ls do eqs := eqs.push (← mkEq (← get x σ₁) (← get x σ₂))
    for x in gs do
      eqs := eqs.push (← mkEq (← get x (← mkAppM ``ProgramState.globals #[σ₁]))
        (← get x (← mkAppM ``ProgramState.globals #[σ₂])))
    let body ← eqs.foldrM (fun e acc => mkAppM ``And #[e, acc]) (mkApp2 B σ₁ σ₂).headBeta
    mkLambdaFVars #[σ₁, σ₂] body

/-- EC's `sim` invariant of two loops as an **equality set**: the variables the relation `B` after
them reads, closed backwards through each loop (`eqBack`), equal on the two sides (`B` itself left
out: it may read what the loops change, `F.RO.m` at the loops' `p`; at the exit it follows from
the equalities). -/
def loopInvEq (B : Lean.Expr) (l₁ l₂ : Lean.Expr) : MetaM Lean.Expr := do
  let SB ← varsOf #[B]
  let (ls, gs) ← vsUnion (← eqBack l₁ SB) (← eqBack l₂ SB)
  let ps := mkConst ``ProgramState
  withLocalDeclD `σ₁ ps fun σ₁ => withLocalDeclD `σ₂ ps fun σ₂ => do
    let get (x st : Lean.Expr) : MetaM Lean.Expr := do
      mkAppM ``Getter.get #[← mkAppM ``Lens.toGetter #[x], st]
    let mut eqs : Array Lean.Expr := #[]
    for x in ls do eqs := eqs.push (← mkEq (← get x σ₁) (← get x σ₂))
    for x in gs do
      eqs := eqs.push (← mkEq (← get x (← mkAppM ``ProgramState.globals #[σ₁]))
        (← get x (← mkAppM ``ProgramState.globals #[σ₂])))
    let some last := eqs.back? | throwError "sim: no variables for the loops' equality set"
    let body ← (eqs.pop).foldrM (fun e acc => mkAppM ``And #[e, acc]) last
    mkLambdaFVars #[σ₁, σ₂] body

/-- The variables (lenses of the state or of the globals) a relational precondition `A` keeps
equal, `x.get σ₁ = x.get σ₂`: EC's equality set. -/
def eqVarsOf (A : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let A ← instantiateMVars A
  if A.getAppFn.isMVar then return #[]
  let ps := mkConst ``ProgramState
  withLocalDeclD `σ₁ ps fun σ₁ => withLocalDeclD `σ₂ ps fun σ₂ => do
    let body := (mkApp2 A σ₁ σ₂).headBeta
    let xs ← IO.mkRef (#[] : Array Lean.Expr)
    let lensOf? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
      if e.isAppOfArity ``Getter.get 4 && (e.getArg! 2).isAppOfArity ``Lens.toGetter 3 then
        some ((e.getArg! 2).getArg! 2, e.getArg! 3) else none
    Meta.forEachExpr body fun e => do
      let some (_, a, b) := e.eq? | return
      let some (x, sa) := lensOf? a | return
      let some (y, sb) := lensOf? b | return
      unless x == y && sa.containsFVar σ₁.fvarId! && sb.containsFVar σ₂.fvarId! do return
      if x.containsFVar σ₁.fvarId! || x.containsFVar σ₂.fvarId! then return
      unless (← xs.get).contains x do xs.modify (·.push x)
    xs.get

/-- EC's `sim (_: J)` invariant of two loops: `J`, the variables both loops mention equal, and
of the precondition's equality set (its regions `Rs`, its variables `xs`) what neither or both
loops mention. -/
def loopInvWith (J : Lean.Expr) (Rs xs : Array Lean.Expr) (l₁ l₂ : Lean.Expr) :
    MetaM Lean.Expr := do
  -- the locals the bodies reset (inlining's temporaries, dead at the loop's head) are not kept
  let resets ← IO.mkRef (#[] : Array String)
  for l in [l₁, l₂] do
    Meta.forEachExpr (← instantiateMVars l) fun e => do
      if e.isAppOf ``resetSetter then
        Meta.forEachExpr e fun t => do
          if let .lit (.strVal str) := t then resets.modify (·.push str)
  let resets ← resets.get
  let reset (x : Lean.Expr) : Bool := (x.find? fun a =>
    match a with | .lit (.strVal str) => resets.contains str | _ => false).isSome
  let (ls₁, gs₁) ← varsOf #[l₁]
  let (ls₂, gs₂) ← varsOf #[l₂]
  let ls₁ := ls₁.filter (!reset ·)
  let ls₂ := ls₂.filter (!reset ·)
  let both (v : Lean.Expr) : Bool := (ls₁.contains v && ls₂.contains v) ||
    (gs₁.contains v && gs₂.contains v)
  let neither (v : Lean.Expr) : Bool := !(ls₁.contains v || ls₂.contains v ||
    gs₁.contains v || gs₂.contains v)
  let mut vs : Array Lean.Expr := ls₁.filter ls₂.contains ++ gs₁.filter gs₂.contains
  for x in xs do
    if (both x || neither x) && !vs.contains x then vs := vs.push x
  let ps := mkConst ``ProgramState
  withLocalDeclD `σ₁ ps fun σ₁ => withLocalDeclD `σ₂ ps fun σ₂ => do
    -- a lens of the state or of the globals, or a region (`glob A`)
    let get (x st : Lean.Expr) : MetaM Lean.Expr := do
      let t ← whnfR (← inferType x)
      if t.isAppOf ``Footprint then
        return ← mkAppM ``Getter.get #[← mkAppM ``Footprint.touched_getter #[x],
          ← mkAppM ``ProgramState.globals #[st]]
      if t.isAppOfArity ``Lens 2 && (t.getArg! 1).isConstOf ``VariableAssignment then
        return ← mkAppM ``Getter.get #[← mkAppM ``Lens.toGetter #[x],
          ← mkAppM ``ProgramState.globals #[st]]
      mkAppM ``Getter.get #[← mkAppM ``Lens.toGetter #[x], st]
    let mut eqs : Array Lean.Expr := #[]
    for x in vs ++ Rs do eqs := eqs.push (← mkEq (← get x σ₁) (← get x σ₂))
    let body ← eqs.foldrM (fun e acc => mkAppM ``And #[e, acc]) (mkApp2 J σ₁ σ₂).headBeta
    mkLambdaFVars #[σ₁, σ₂] body

/-- `auto_close` (`Logic/ECClose.lean`, which imports this file) on `g`, when the environment has
it: the goals left (`[g]` if it does not close it). -/
def autoCloseIfAvailable (g : MVarId) : TacticM (List MVarId) := do
  let .ok stx := Parser.runParserCategory (← getEnv) `tactic "auto_close" | return [g]
  let s ← saveState
  try
    let gs ← evalTacticAt stx g
    if gs.isEmpty then return [] else s.restore; return [g]
  catch _ => s.restore; return [g]

/-- EC's `sim` on the relational goal `g`, backwards (see the module docstring); the goals left.
`open?`: the precondition is a metavariable to be found (a branch of a conditional), assigned the
relation left where the statements are used up. -/
partial def sim (g : MVarId) (frame? : Option Lean.Expr := none) (fuel : Nat := 400)
    (eqset : Array Lean.Expr × Array Lean.Expr := (#[], #[]))
    (inv? : Option (Lean.Expr × Array Lean.Expr) := none) :
    TacticM (List MVarId) := do
  if fuel == 0 then return [g]
  -- the deterministic code at the end of both sides
  let g ← Judgment.wpDet g none
  let ty ← prhlGoal g "sim"
  -- EC's equality set: the precondition's, at the start (a branch's precondition is still open)
  let eqset ← if eqset.1.isEmpty && eqset.2.isEmpty then g.withContext (eqSetOf (ty.getArg! 0))
    else pure eqset
  let k₁ ← lastKind (ty.getArg! 1)
  let k₂ ← lastKind (ty.getArg! 2)
  match k₁, k₂ with
  | .skip, .skip =>
    -- both used up: an open precondition is what is left, else the implication
    let pre ← instantiateMVars (ty.getArg! 0)
    if pre.getAppFn.isMVar then
      let ty' ← g.getType
      let post := (← instantiateMVars ty').getArg! 3
      unless ← isDefEq pre post do return [g]
      let gs ← applyLemma ``prhlStmt_skip g
      for h in gs do
        let _ ← evalTacticAt (← `(tactic| exact fun _ _ h => h)) h
      return []
    if debug.sim.get (← getOptions) then
      IO.eprintln s!"sim (skip): precondition not open: {← ppExpr pre}"
    let g ← equivSkip g
    closeImp g
  | .cond, .cond =>
    let s ← saveState
    let g₀ := g
    let g ← HoareSplit.hoareSplit 1 g
    -- by hand, not `applyLemma`: the branches' relations `Aₜ`, `Aₑ` stay ordinary metavariables,
    -- for the branches' `sim` to assign
    let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_if_bwd
    let cTy ← inferType c
    let names := cTy.getForallBinderNames
    let (ms, _, concl) ← forallMetaTelescope cTy
    unless ← isDefEq concl (← g.getType) do return [g]
    let arg (n : Name) : TacticM MVarId := do
      let some i := names.findIdx? (· == n) | throwError "sim: no argument `{n}`"
      let m := ms[i]!.mvarId!
      m.setKind .syntheticOpaque
      return m
    let ht ← arg `ht
    let he ← arg `he
    let h ← arg `h
    g.assign (mkAppN c ms)
    let rt ← sim ht frame? (fuel - 1) eqset inv?
    let re ← sim he frame? (fuel - 1) eqset inv?
    -- a branch `sim` does not finish leaves its precondition open: EC's `sim` stops at the
    -- conditional then
    for n in [`Aₜ, `Aₑ] do
      let some i := names.findIdx? (· == n) | continue
      if (← instantiateMVars ms[i]!).getAppFn.isMVar then
        if debug.sim.get (← getOptions) then
          let left := if n == `Aₜ then rt else re
          let msg ← match left.head? with
            | some h => h.withContext do
                pure s!"{← ppExpr (← instantiateMVars (← h.getType))}"
            | none => pure "(no goal)"
          IO.eprintln s!"sim (if, branch {n} not finished): {msg}"
        s.restore
        return [g₀]
    let h ← Judgment.simpArg h 3 relSimpDecls []
    return rt ++ re ++ (← sim h frame? (fuel - 1) eqset inv?)
  | .call, .call =>
    -- with a frame: the call rule for states equal outside it, the callee's disjointness from
    -- it by `fp_disjoint`
    if let some L := frame? then
      let s ← saveState
      try
        let g ← HoareSplit.hoareSplit 1 g
        let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_call_outside
        let cTy ← inferType c
        let names := cTy.getForallBinderNames
        let (ms, _, concl) ← forallMetaTelescope cTy
        let some iL := names.findIdx? (· == `L) | throwError "sim: no `L`"
        unless ← isDefEq ms[iL]! L do throwError "sim: the frame does not fit"
        unless ← isDefEq concl (← g.getType) do throwError "sim: not the frame's call rule"
        g.assign (mkAppN c ms)
        let some iM := names.findIdx? (· == `hM) | throwError "sim: no `hM`"
        let some ip := names.findIdx? (· == `hpre) | throwError "sim: no `hpre`"
        let hM := ms[iM]!.mvarId!
        let [] ← runOn hM (← `(tactic| ((try simp only [Footprint.lens_pair]); fp_disjoint)))
          | throwError "sim: the callee touches the frame"
        let hp := ms[ip]!.mvarId!
        hp.setKind .syntheticOpaque
        return ← sim (← Judgment.simpArg hp 3 relSimpDecls []) frame? (fuel - 1) eqset inv?
      catch _ => s.restore
    -- EC's `sim` with an equality set: a region the precondition keeps equal, the callee in it
    if let some g' ← callGlob g eqset then return ← sim g' frame? (fuel - 1) eqset inv?
    let s ← saveState
    let called? ← try
      -- calls of procedures spelled differently (an abstract procedure with oracles that are
      -- the same once unfolded, `A(Bounder(FM(C,P)))` and `A(Bounder(FInit(C(P))))`): their
      -- equality by `simp` (the modules' `apply_simp` lemmas), then `rfl`
      let gs ← runOn g (← `(tactic| equiv_call))
      -- the callees' equality within a budget: oracles that differ (`A(Bounder(FInit(RO)))`,
      -- `A(Bounder(RO))`) fail it, and are left to EC's `call (_: ={…})`
      let gs ← gs.filterMapM fun h => do
        unless (← h.getTag).eraseMacroScopes == `callee do return some h
        let s ← saveState
        let ok ← tryCatchRuntimeEx
          (withCurrHeartbeats <|
            withTheReader Core.Context (fun c => { c with maxHeartbeats := 50000 * 1000 }) do
              let rest ← runOn h (← `(tactic| first | (simp; rfl) | rfl))
              pure rest.isEmpty)
          (fun _ => pure false)
        unless ok do s.restore; throwError "sim: the callees differ"
        return none
      pure (some gs)
    catch _ => pure none
    match called? with
    | some [g'] => sim g' frame? (fuel - 1) eqset inv?
    | some gs => return gs
    | none => s.restore; return [g]
  | .loop, .loop =>
    -- EC's `sim` through two loops: its equality set as the invariant (the relation after them,
    -- and the variables the loops mention equal; else, when the relation after them reads what
    -- the loops change, the equalities of the variables it reads instead of it); the bodies by
    -- `sim`, the guards agree and the exit by `closeImp`, then on before the loops.  Otherwise it
    -- stops at them.
    let s ← saveState
    let attempt (eqOnly : Bool) : TacticM (List MVarId) := do
      let g ← HoareSplit.hoareSplit 1 g
      let ty ← prhlGoal g "sim"
      let B ← instantiateMVars (ty.getArg! 3)
      if B.getAppFn.isMVar then throwError "sim: the relation after the loops is open"
      let l₁ := stripLets (lastOf (ty.getArg! 1))
      let l₂ := stripLets (lastOf (ty.getArg! 2))
      let I ← if eqOnly then loopInvEq B l₁ l₂ else match inv? with
        | some (J, xs) => loopInvWith J eqset.1 xs l₁ l₂
        | none => loopInv B #[l₁, l₂]
      let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_while
      let (ms, _, concl) ← forallMetaTelescope (← inferType c)
      unless ← isDefEq ms[0]! I do throwError "sim: the invariant"
      unless ← isDefEq concl ty do throwError "sim: not two loops"
      g.assign (← instantiateMVars (mkAppN c ms))
      let n := ms.size
      let (gGuard, gBody, gExit, gPre) :=
        (ms[n - 4]!.mvarId!, ms[n - 3]!.mvarId!, ms[n - 2]!.mvarId!, ms[n - 1]!.mvarId!)
      for m in [gGuard, gBody, gExit, gPre] do m.setKind .syntheticOpaque
      let rb ← sim (← Judgment.simpArg gBody 0 relSimpDecls []) frame? (fuel - 1) eqset inv?
      -- what `sim` leaves of the bodies (a relation between different variables, `glob A` past
      -- writes): `auto_close`
      let rb ← rb.flatMapM autoCloseIfAvailable
      unless rb.isEmpty do throwError "sim: the loops' bodies"
      for m in [gGuard, gExit] do
        let m ← try generalizeReadsRel m catch _ => pure m
        let r ← closeImp m
        let r ← r.flatMapM autoCloseIfAvailable
        if let some m' := r.head? then
          throwError "sim: the loops' guards or exit:{indentExpr (← instantiateMVars (← m'.getType))}"
      sim gPre frame? (fuel - 1) eqset inv?
    try attempt false
    catch e =>
      s.restore
      if debug.sim.get (← getOptions) then
        -- printed, not logged: an enclosing rule's `restore` would drop a log message
        IO.eprintln s!"sim (loops): {← e.toMessageData.toString}"
      if inv?.isSome then return [g]
      try attempt true
      catch e =>
        s.restore
        if debug.sim.get (← getOptions) then
          IO.eprintln s!"sim (loops, equality set): {← e.toMessageData.toString}"
        return [g]
  | .sample, .sample =>
    let s ← saveState
    try
      let gs ← runOn g (← `(tactic| equiv_rnd))
      match gs with
      | [g'] => sim g' frame? (fuel - 1) eqset inv?
      | _ => return gs
    catch _ =>
      s.restore
      -- a product sampling against two samplings (`x <$ d1 \`*\` d2` against `x₁ <$ d1;
      -- x₂ <$ d2`, either side), coupled by the identity: EC's `sample_sample2`
      try
        let gs ← runOn g (← `(tactic| equiv_rnd_dprod))
        match gs with
        | [g'] => sim g' frame? (fuel - 1) eqset inv?
        | _ => return gs
      catch _ => s.restore; return [g]
  | _, _ => return [g]

end ECSim

open Lean Elab Tactic ECSim in
/-- **EC's `inline*`** on a statement judgment, on both sides of a relational one or on side `i`
with `stmt_inline*{i}`. -/
-- two tokens: `stmt_inline*` would be read as `stmt_inline` and `*`
elab "stmt_inline" "*" s:(Judgment.judgmentSide)? : tactic =>
  liftMetaTactic1 fun g => some <$> inlineAllSides g (Judgment.sideOf? s)

open Lean Elab Tactic ECSim in
/-- **EC's `inline*`** on a `phoare` statement judgment. -/
elab "phoare_inline" "*" : tactic => liftMetaTactic1 fun g => some <$> inlineAllSides g none

open Lean Elab Tactic ECSim in
/-- **EC's `inline*`** on a Hoare triple about a statement. -/
elab "hoare_inline" "*" : tactic => liftMetaTactic1 fun g => some <$> inlineAllSides g none

open Lean Elab Tactic ECSim in
/-- **EC's `sim`**: see the module docstring. -/
elab "sim" : tactic => do
  let g ← ECProc.accessorNorm (← getMainGoal)
  let s ← saveState
  let gs ← sim g
  -- calls of different concrete procedures (`G4.S(F.LRO).f`, `S(IF).f`), where EC's `sim` goes
  -- into the callees: our call rule stops at them (inside a conditional, `sim` then stops before
  -- it and does nothing), so the callees inlined (`inline*`), then `sim` and `auto_close` on what
  -- it leaves — kept only if that closes the goal.  (Inlining inside a branch would put the
  -- branch's open precondition under the inliner's frame.)  Only when `sim` made no progress: a
  -- partial `sim` (EC's `sim;` before further steps) stays as it is.
  unless gs == [g] do replaceMainGoal gs; return
  let sPlain ← saveState
  s.restore
  let ok ← try
      let g' ← inlineAllSides g none
      if g' == g then pure false else
        let gs' ← sim g'
        let rest ← gs'.flatMapM autoCloseIfAvailable
        pure rest.isEmpty
    catch _ => pure false
  if ok then replaceMainGoal [] else
    sPlain.restore
    replaceMainGoal gs

open Lean Meta Elab Tactic ECSim PRHLWp in
/-- **EC's `sim (_: I)`**: `sim` with the relation `I` (`§x{1}`, `§y{2}`; EC's
`={m,mi}(Perm,PRPi)` is `§Perm.m{1} = §PRPi.m{2} ∧ …`) kept through loops, with EC's equality
set: the loops' invariant is `I`, the variables both loops mention equal, and the
precondition's equalities the loops keep. -/
elab "sim" " (" "_" " : " I:term ")" : tactic => withMainContext do
  let g ← ECProc.accessorNorm (← getMainGoal)
  let ty ← prhlGoal g "sim"
  let Ie ← g.withContext (elabRelCond ty I)
  let xs ← g.withContext (eqVarsOf (ty.getArg! 0))
  let gs ← sim g none 400 (#[], #[]) (some (Ie, xs))
  replaceMainGoal gs

open Lean Meta Elab Tactic ECSim PRHLWp in
/-- **EC's `sim n₁ n₂`**: `sim` on the code after the first `n₁` statements of the left side and
the first `n₂` of the right; the goal left is the code before, its postcondition what `sim` needs
(the relation between the two parts is open, for `sim` to compute). -/
elab "sim" ppSpace n₁:num ppSpace n₂:num : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← prhlGoal g "sim"
  let l₁ ← HoareSplit.seqLength (ty.getArg! 1)
  let l₂ ← HoareSplit.seqLength (ty.getArg! 2)
  unless n₁.getNat ≤ l₁ && n₂.getNat ≤ l₂ do
    throwError "sim: the sides have {l₁} and {l₂} statements"
  let g ← HoareSplit.hoareSplit (l₁ - n₁.getNat) g (some 1)
  let g ← HoareSplit.hoareSplit (l₂ - n₂.getNat) g (some 2)
  g.withContext do
    -- `prhlStmt_seq` by hand: its middle relation an ordinary metavariable, for `sim` to assign
    let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq
    let (ms, _, concl) ← forallMetaTelescope (← inferType c)
    unless ← isDefEq concl (← g.getType) do throwError "sim: cannot cut the code"
    g.assign (mkAppN c ms)
    let hAfter := ms[ms.size - 2]!.mvarId!
    let hBefore := ms[ms.size - 1]!.mvarId!
    hAfter.setKind .syntheticOpaque
    hBefore.setKind .syntheticOpaque
    let rest ← sim hAfter
    replaceMainGoal (rest ++ [hBefore])

open Lean Elab Tactic ECSim in
/-- **EC's `sim` with a frame**: `sim / x₁, …, xₙ`, the states equal except on the globals `xᵢ`
(EC's `={glob A}`: variables the calls of the same procedure do not touch, written by one side
only or at different times), calls of the same procedure by `prhlStmt_seq_call_outside`. -/
elab "sim" " / " xs:term,+ : tactic => withMainContext do
  let xs := xs.getElems
  let some last := xs.back? | throwError "sim: a frame"
  let L ← (xs.pop).foldrM (fun x acc => `(Lens.pair $x $acc)) last
  let Le ← Term.elabTerm L none
  Term.synthesizeSyntheticMVarsNoPostponing
  let g ← getMainGoal
  -- the clone's names as the code spells them (`SRO.RO.m` ↦ `SecureRO.RO.m`)
  let gs ← sim g (some (← unfoldCloneAliases (← instantiateMVars Le)))
  replaceMainGoal gs

end GaudisCrypt
