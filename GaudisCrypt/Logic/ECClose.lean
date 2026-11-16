import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECCallUpto
import GaudisCrypt.Logic.RenameReads
import GaudisCrypt.Lib.EC.List

/-!
# A closer for what EC leaves to `auto => /#`

    auto_close

EC closes the logical goals its program tactics leave with `smt` (`/#`, `smt(…)`).  We have no
SMT solver (by decision), but those goals come in a few shapes, and `auto_close` takes them
apart the way one does by hand:

* introduce everything, take the hypotheses apart (`∧`, `∃`, `∨`), substitute the equations of
  variables (the states of EC's `sp`: `σ = x.set v τ`);
* simplify the reads through writes everywhere, the hypotheses included (`simp_reads_all`; through
  the inliner's renamings, `rename_reads`), and the
  `glob` of a region past writes outside it (`glob_simp`, EC's implicit `={glob D}`);
* the tests back to propositions (`decide … = true`), indicators of events (`indicatorE P = 1`);
* split the goal (`∧`, `if`), and close each part by `rfl`, an assumption (either way round),
  `trivial`, `omega` (EC's `/#` on counters), or `simp_all`.

It closes the goal or fails, leaving it untouched.  It does not know the lemmas EC's `smt(l)`
is given: state those first (`have := l …`).
-/

namespace GaudisCrypt

open Lean Meta Elab Tactic

/-- `e` is a name (a variable with an accessible name) or a tuple of names. -/
partial def namedTuple (lctx : LocalContext) (e : Lean.Expr) : Bool :=
  let anon (n : Name) := n.hasMacroScopes || n.isInaccessibleUserName
  if e.isFVar then !anon (lctx.get! e.fvarId!).userName
  else if e.isAppOfArity ``Prod.mk 4 then namedTuple lctx (e.getArg! 2) && namedTuple lctx (e.getArg! 3)
  else false

/-- EC's `<<-` on reads: an equation between a read of the state (`FRO.m.get σ.globals`) and a
named variable (EC's `elim* => hs0`) rewrites the read into the name everywhere, so the closer
works with the names (`subst_vars` would eliminate the name instead). -/
elab "subst_reads" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut rules : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  let anon (n : Name) := n.hasMacroScopes || n.isInaccessibleUserName
  for d in lctx do
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    let isRead (e : Lean.Expr) := !e.isFVar && (e.find? fun t => t.isAppOf ``Getter.get ||
      t.isAppOf ``ProgramState.globals).isSome
    -- a name (EC's `elim*` name, `<<-`), or a tuple of names (`(x1, x2)`, EC's `->>`)
    let named (e : Lean.Expr) : Bool := namedTuple lctx e
    let h ← Term.exprToSyntax d.toExpr
    if isRead a && named b then rules := rules.push (← `(Lean.Parser.Tactic.simpLemma| $h:term))
    else if isRead b && named a then
      rules := rules.push (← `(Lean.Parser.Tactic.simpLemma| ← $h:term))
  if rules.isEmpty then return
  evalTactic (← `(tactic| simp only [$rules,*] at *))

/-- The state a read is of: `σ` for `G.get σ` and `G.get σ.globals`. -/
def readState? (e : Lean.Expr) : Option (Lean.Expr × FVarId) :=
  if e.isAppOfArity ``Getter.get 4 then
    let s := e.getArg! 3
    let s := if s.isAppOfArity ``ProgramState.globals 1 then s.appArg! else s
    if s.isFVar then some (e.getArg! 2, s.fvarId!) else none
  else none

/-- EC's memories as one: an equation between reads of the same variable in two states (the frame
`X.get τ = X.get σ` that `conseq` and `call` leave for what the code does not modify, or `={x}`)
rewrites the read of the later state (in the context) into the earlier one's, everywhere.  One
direction for every pair of states, so the rewriting cannot loop; of two equations saying the same
(`X.get τ₁ = X.get τ₂` from an invariant, `X.get τ₂ = X.get τ₁` from a frame) one is dropped, so
that `simp_all` does not loop on them either. -/
elab "subst_frames" : tactic => withMainContext do
  let g ← getMainGoal
  let lctx ← getLCtx
  let mut thms : SimpTheorems := {}
  let mut rules : Array FVarId := #[]
  let mut seen : Array (Lean.Expr × FVarId × FVarId) := #[]
  let mut twins : Array FVarId := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    let some (Ga, sa) := readState? a | continue
    let some (Gb, sb) := readState? b | continue
    unless sa != sb && Ga == Gb do continue
    -- the same equation again (either way round): dropped
    if seen.any fun (G, x, y) => G == Ga && ((x == sa && y == sb) || (x == sb && y == sa)) then
      twins := twins.push d.fvarId
      continue
    seen := seen.push (Ga, sa, sb)
    let (ia, ib) := ((lctx.get! sa).index, (lctx.get! sb).index)
    thms ← thms.add (.fvar d.fvarId) #[] d.toExpr (inv := ia < ib)
    rules := rules.push d.fvarId
  let g ← g.tryClearMany twins
  if rules.isEmpty then
    replaceMainGoal [g]
    return
  -- every hypothesis but the rules themselves, and the goal
  let lctx ← g.withContext getLCtx
  let others := lctx.foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail || rules.contains d.fvarId then acc else acc.push d.fvarId
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simpGoal g ctx (fvarIdsToSimp := others)
  match r with
  | none => replaceMainGoal []
  | some (_, g') => replaceMainGoal [g']

/-- EC's `progress` on implications: a hypothesis `p → q` whose premise `p` is another hypothesis
(up to reducible unfolding) becomes `q`; repeated while one applies. -/
elab "mp_hyps" : tactic => withMainContext do
  let mut g ← getMainGoal
  for _ in [0:32] do
    let lctx ← g.withContext getLCtx
    let mut step : Option (FVarId × Lean.Expr × Lean.Expr) := none
    for d in lctx do
      if d.isImplementationDetail then continue
      let t ← g.withContext (instantiateMVars d.type)
      let .forallE _ p q _ := t | continue
      if q.hasLooseBVars then continue
      unless ← g.withContext (Meta.isProp p) do continue
      for e in lctx do
        if e.isImplementationDetail || e.fvarId == d.fvarId then continue
        if ← g.withContext (withReducible (isDefEq e.type p)) then
          step := some (d.fvarId, mkApp d.toExpr e.toExpr, q); break
      if step.isSome then break
    let some (h, pf, q) := step | break
    let g1 ← g.assert (← g.withContext (pure (lctx.get! h).userName)) q pf
    let (_, g2) ← g1.intro1P
    g ← g2.clear h
  replaceMainGoal [g]

/-- EC's `<<*`: an equation between a named variable (EC's `elim* => hs`) and an anonymous one
(a read generalized by the closer) eliminates the anonymous one, so the names stay. -/
elab "subst_named" : tactic => withMainContext do
  let mut g ← getMainGoal
  for _ in [0:64] do
    let lctx ← g.withContext getLCtx
    let mut found : Option FVarId := none
    for d in lctx do
      if d.isImplementationDetail then continue
      let some (_, a, b) := (← g.withContext (instantiateMVars d.type)).eq? | continue
      unless a.isFVar && b.isFVar do continue
      let anon (n : Name) := n.hasMacroScopes || n.isInaccessibleUserName
      let (da, db) := (lctx.get! a.fvarId!, lctx.get! b.fvarId!)
      if anon da.userName && !anon db.userName then
        found := some a.fvarId!; break
      if anon db.userName && !anon da.userName then
        found := some b.fvarId!; break
    let some x := found | break
    g ← g.withContext (substVar g x)
  replaceMainGoal [g]

/-- `simp_reads` on the goal and every hypothesis (a hypothesis simplified to `False` closes the
goal). -/
elab "simp_reads_all" : tactic => withMainContext do
  let g ← getMainGoal
  let mut g := g
  let mut progress := false
  let hyps := (← g.getDecl).lctx.foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d.fvarId
  for h in hyps do
    let ty ← g.withContext do instantiateMVars (← h.getType)
    unless ← g.withContext (isProp ty) do continue
    let r ← g.withContext do Judgment.simpWithNames PRHLWp.relSimpDecls [] ty
    if r.expr == ty then continue
    progress := true
    match ← applySimpResultToLocalDecl g h r false with
    | none => replaceMainGoal []; return
    | some (_, g') => g := g'
  let ty ← g.withContext do instantiateMVars (← g.getType)
  let r ← g.withContext do Judgment.simpWithNames PRHLWp.relSimpDecls [] ty
  if r.expr != ty then
    progress := true
    g ← applySimpResultToTarget g ty r
  unless progress do throwError "simp_reads_all: no progress"
  replaceMainGoal [g]

/-- The steps `auto_close` and `auto_progress` share: introduce, take the hypotheses apart,
substitute, simplify the reads and the tests (see the module docstring). -/
macro "auto_prep" : tactic => `(tactic| (
  -- the `let`s of the conditions first (introduced, they would hide the reads)
  try simp only [] at *
  all_goals intros
  all_goals try casesm* _ ∧ _, ∃ _, _, _ ∨ _
  all_goals try norm_decide
  all_goals try glob_tuples
  all_goals try casesm* _ ∧ _
  all_goals try mp_hyps
  all_goals try casesm* _ ∧ _
  all_goals try subst_named
  all_goals try subst_reads
  all_goals try subst_vars
  all_goals try glob_reads
  all_goals try subst_frames
  all_goals try rename_reads
  all_goals try simp only [Setter.throwaway_set] at *
  all_goals try simp_reads_all
  all_goals try glob_simp
  -- … and in the hypotheses
  all_goals try simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl,
    GaudisCrypt.touched_getter_get_ite, ite_self] at *
  all_goals try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true',
    Bool.not_eq_eq_eq_not, Bool.not_true, not_lt, not_le, and_true, true_and,
    indicatorE_eq_one_iff, if_true, if_false, Prod.mk.injEq, ite_self] at *
  -- what the simplification took apart
  all_goals try casesm* _ ∧ _, ∃ _, _, _ ∨ _
  all_goals try mp_hyps
  all_goals try casesm* _ ∧ _
  all_goals try subst_frames
  all_goals try subst_named
  all_goals try subst_vars
  -- tuple equations the substitutions made (`x₁ = x₂` with `x = (bs, n)`): componentwise (EC's
  -- `progress`); a procedure's arguments are typed `sig.ParamType`, a tuple once unfolded
  all_goals try dsimp only [ProcedureSignature.ParamType, typeListToTuple] at *
  all_goals try simp only [Prod.mk.injEq] at *
  all_goals try casesm* _ ∧ _
  all_goals try subst_vars))

/-- **What EC leaves to `auto => /#`**: see the module docstring. -/
syntax "auto_close" : tactic

macro_rules
  | `(tactic| auto_close) => `(tactic| focus (
      auto_prep
      all_goals first
        | done
        | trivial
        | rfl
        | assumption
        | (apply Eq.symm; assumption)
        | omega
        | (apply And.intro <;> auto_close)
        | (split_ifs <;> auto_close)
        | (intro _; auto_close)
        | (clear_decl_hyps; simp_all; done)
        | fail "auto_close: a goal is left (state the lemmas EC's `smt` is given, or close it \
            by hand)"
      done))

open Lean Elab Tactic in
/-- `simp_all; done`, failing (as an ordinary error, so `first` goes on) also when `simp_all` runs
into a runtime limit (a rewriting cycle among the hypotheses, e.g. the frames of EC's `while`
reaching the recursion limit), which `try`/`first` would not catch. -/
elab "simp_all_done_safe" : tactic => do
  let s ← saveState
  tryCatchRuntimeEx (evalTactic (← `(tactic| (clear_decl_hyps; simp_all; done)))) fun _ => do
    s.restore
    throwError "simp_all_done_safe: simp_all did not close the goal"

/-- **EC's `progress`** (`auto => />; progress`): `auto_close`'s steps, the goals it cannot close
left (split as far as it goes), for the lemmas EC's `smt` calls are given. -/
syntax "auto_progress" : tactic

macro_rules
  | `(tactic| auto_progress) => `(tactic| focus (
      auto_prep
      all_goals first
        | done
        | trivial
        | rfl
        | assumption
        | (apply Eq.symm; assumption)
        | omega
        | (apply And.intro <;> auto_progress)
        | (split_ifs <;> auto_progress)
        | (intro _; auto_progress)
        | simp_all_done_safe
        | skip))

end GaudisCrypt

namespace GaudisCrypt

open Lean Meta Elab Tactic in
/-- `generalize_reads_all`: every read of a variable in a state (`x.get σ`, `X.get σ.globals`,
`σ` a local) a fresh variable, in the goal and the hypotheses: EC's view of a memory as its
variables' values. -/
elab "generalize_reads_all" : tactic => withMainContext do
  let g ← getMainGoal
  -- the propositions among the hypotheses go into the goal, and come back after
  let hyps ← (← getLCtx).foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    if ← isProp d.type then return acc.push d.fvarId else return acc
  let (_, g) ← g.revert hyps (preserveOrder := true)
  let g ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let reads ← IO.mkRef (#[] : Array Lean.Expr)
    Meta.forEachExpr t fun e => do
      unless e.isAppOfArity ``Getter.get 4 && !e.hasLooseBVars do return
      let st := e.appArg!
      let ok := st.isFVar || (st.isAppOfArity ``ProgramState.globals 1 && st.appArg!.isFVar)
      if ok && !(← reads.get).contains e then reads.modify (·.push e)
    let rs ← reads.get
    if rs.isEmpty then return g
    let args := rs.map fun r => ({ expr := r, xName? := some `v } : GeneralizeArg)
    let (_, g) ← g.generalize args
    return g
  -- the hypotheses back under their names (EC's `elim*` names, `inv0`, …)
  let (_, g) ← g.introNP hyps.size
  replaceMainGoal [g]

open Lean Meta Elab Tactic

namespace ECClose

/-- The instances of the lemma `lemName` (`∀ xs, P xs`) at the terms of `targets`: each subterm of its
conclusion that mentions all its non-instance arguments (a pattern, `size l` of `size_ge0 :
0 ≤ size l`) matched (reducibly) against each target term, the instance kept when that fixes the
arguments (the instance arguments synthesized). -/
def instancesOf (lemName : Name) (targets : Array Lean.Expr) : MetaM (Array Lean.Expr) := do
  let mut out : Array Lean.Expr := #[]
  for t in targets do
    let r? ← withNewMCtxDepth do
      -- (its universe levels open at this depth, to be fixed by the match)
      let lem ← mkConstWithFreshMVarLevels lemName
      let (ms, bis, concl) ← forallMetaTelescopeReducing (← inferType lem)
      if ms.isEmpty then return none
      let vars := (ms.zip bis).filterMap fun (m, bi) => if bi.isInstImplicit then none else some m
      -- the application subterms of the conclusion that mention every argument
      let subs ← IO.mkRef (#[] : Array Lean.Expr)
      Meta.forEachExpr concl fun e => do
        if e.isApp && vars.all (fun m => (e.find? (· == m)).isSome) then
          subs.modify (·.push e)
      for p in ← subs.get do
        -- (the same head: by name for a constant, the lemma's universe levels being open)
        let sameHead := match p.getAppFn.constName?, t.getAppFn.constName? with
          | some a, some b => a == b
          | _, _ => p.getAppFn == t.getAppFn
        unless sameHead do continue
        let s ← saveState
        if ← withReducible (isDefEq p t) then
          -- the instance arguments
          let mut ok := true
          for (m, bi) in ms.zip bis do
            if bi.isInstImplicit && !(← m.mvarId!.isAssigned) then
              try
                let inst ← synthInstance (← inferType m)
                unless ← isDefEq m inst do ok := false
              catch _ => ok := false
          if ok then
            let pf ← instantiateMVars (mkAppN lem ms)
            unless pf.hasMVar do return some pf
        s.restore
      return none
    if let some pf := r? then
      let pty ← inferType pf
      unless ← out.anyM (fun q => return (← inferType q) == pty) do out := out.push pf
  return out

end ECClose

open ECClose in
/-- `ec_instances [l₁, …]`: the instances of the lemmas `lᵢ` (`∀ xs, P xs`) at the terms of the
goal and the hypotheses, as hypotheses (what EC's provers instantiate on the goal's terms: a
`smt(List.size_ge0)` on `0 <= size p`).  At most 64. -/
elab "ec_instances" " [" ls:ident,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let mut sources := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    unless d.isImplementationDetail do sources := sources.push (← instantiateMVars d.type)
  let lctx ← getLCtx
  let termsRef ← IO.mkRef (#[] : Array Lean.Expr)
  for src in sources do
    Meta.forEachExpr src fun e => do
      -- (`Meta.forEachExpr` opens binders: a term with a variable of a binder is not a term of
      -- the goal, and an instance at it would mention an unknown variable)
      if e.isApp && !e.hasLooseBVars && !e.hasAnyFVar (fun f => !lctx.contains f) then
        termsRef.modify (·.push e)
  let terms ← termsRef.get
  let mut hyps : Array Hypothesis := #[]
  for l in ls.getElems do
    for pf in ← instancesOf (← realizeGlobalConstNoOverloadWithInfo l) terms do
      if hyps.size ≥ 64 then break
      hyps := hyps.push { userName := `h_inst, type := ← inferType pf, value := pf }
  if hyps.isEmpty then return
  let (_, g') ← g.assertHypotheses hyps
  replaceMainGoal [g']

namespace ECClose

/-- The instances of the lemma `lemName` at the terms `targets`: an application in its
conclusion with the head of a target term and one of the lemma's arguments matched against
it; then the instance arguments synthesized and the hypotheses (arguments that are proofs)
found among the local hypotheses.  Kept when that fixes every argument. -/
def instancesAt (lemName : Name) (targets : Array Lean.Expr) : MetaM (Array Lean.Expr) := do
  let lctx ← getLCtx
  -- the heads of the lemma's patterns, once: a target with another head is not looked at
  let heads ← withNewMCtxDepth do
    let lem ← mkConstWithFreshMVarLevels lemName
    let (ms, bis, concl) ← forallMetaTelescopeReducing (← inferType lem)
    let mut vars : Array Lean.Expr := #[]
    for (m, bi) in ms.zip bis do
      if bi.isExplicit && !(← isProp (← inferType m)) then vars := vars.push m
    let ref ← IO.mkRef (#[] : Array Name)
    unless vars.isEmpty do
      Meta.forEachExpr concl fun e => do
        if e.isApp && vars.all (fun m => (e.find? (· == m)).isSome) then
          if let some c := e.getAppFn.constName? then ref.modify (·.push c)
    ref.get
  if heads.isEmpty then return #[]
  let mut out : Array Lean.Expr := #[]
  let mut seen : Array Lean.Expr := #[]
  for t in targets do
    let some c := t.getAppFn.constName? | continue
    unless heads.contains c do continue
    if seen.contains t then continue
    seen := seen.push t
    let r? ← withNewMCtxDepth do
      let lem ← mkConstWithFreshMVarLevels lemName
      let (ms, bis, concl) ← forallMetaTelescopeReducing (← inferType lem)
      if ms.isEmpty then return none
      -- the arguments a pattern must mention: the explicit ones that are not proofs (the
      -- implicit ones come with the instances, the proofs from the context)
      let mut vars : Array Lean.Expr := #[]
      for (m, bi) in ms.zip bis do
        if bi.isExplicit && !(← isProp (← inferType m)) then vars := vars.push m
      if vars.isEmpty then return none
      let subs ← IO.mkRef (#[] : Array Lean.Expr)
      Meta.forEachExpr concl fun e => do
        if e.isApp && !e.hasAnyFVar (fun f => !lctx.contains f) &&
            vars.all (fun m => (e.find? (· == m)).isSome) then
          subs.modify (·.push e)
      for p in ← subs.get do
        let sameHead := match p.getAppFn.constName?, t.getAppFn.constName? with
          | some a, some b => a == b
          | _, _ => p.getAppFn == t.getAppFn
        unless sameHead do continue
        let s ← saveState
        if ← withReducible (isDefEq p t) then
          let mut ok := true
          -- the instance arguments
          for (m, bi) in ms.zip bis do
            if bi.isInstImplicit && !(← m.mvarId!.isAssigned) then
              try
                let inst ← synthInstance (← instantiateMVars (← inferType m))
                unless ← isDefEq m inst do ok := false
              catch _ => ok := false
          -- the hypotheses: among the local ones
          for m in ms do
            if !ok then break
            if ← m.mvarId!.isAssigned then continue
            let mty ← instantiateMVars (← inferType m)
            unless ← isProp mty do continue
            let mut found := false
            for d in lctx do
              if d.isImplementationDetail then continue
              if ← isDefEq mty d.type then
                if ← isDefEq m d.toExpr then found := true; break
            unless found do ok := false
          if ok then
            let pf ← instantiateMVars (mkAppN lem ms)
            unless pf.hasMVar do return some pf
        s.restore
      return none
    if let some pf := r? then
      let pty ← inferType pf
      unless ← out.anyM (fun q => return (← inferType q) == pty) do out := out.push pf
  return out

/-- The application subterms of `src` that are terms of the local context (no variable of a
binder: `Meta.forEachExpr` opens them). -/
def termsOf (src : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let lctx ← getLCtx
  let ref ← IO.mkRef (#[] : Array Lean.Expr)
  Meta.forEachExpr src fun e => do
    if e.isApp && !e.hasLooseBVars && !e.hasAnyFVar (fun f => !lctx.contains f) then
      ref.modify (·.push e)
  ref.get

end ECClose

open ECClose

/-- `ec_instances_chain [l₁, …]`: as `ec_instances`, over three rounds (the instances' own terms
are terms to instantiate at: a chain of lemmas), with the lemmas' hypotheses found among the
local ones. -/
elab "ec_instances_chain" " [" ls:ident,* "]" : tactic => do
  let names ← ls.getElems.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
  let mut total := 0
  for _ in [0:3] do
    let added ← withMainContext do
      let g ← getMainGoal
      let mut terms ← termsOf (← instantiateMVars (← g.getType))
      let mut have_ : Array Lean.Expr := #[]
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          let ty ← instantiateMVars d.type
          have_ := have_.push ty
          terms := terms ++ (← termsOf ty)
      let mut hyps : Array Hypothesis := #[]
      for l in names do
        for pf in ← instancesAt l terms do
          if total + hyps.size ≥ 64 then break
          let pty ← inferType pf
          if have_.contains pty then continue
          if ← hyps.anyM (fun h => return h.type == pty) then continue
          hyps := hyps.push { userName := `h_inst, type := pty, value := pf }
      if hyps.isEmpty then return 0
      let (_, g') ← g.assertHypotheses hyps
      replaceMainGoal [g']
      return hyps.size
    if added == 0 then break
    total := total + added

/-- The predicates of the file being checked that the goal or its hypotheses mention:
definitions with values in `Prop` (EC's `pred`, whose body its provers see). -/
def localPreds : TacticM (Array Name) := withMainContext do
  let env ← getEnv
  let mut srcs := #[← instantiateMVars (← getMainTarget)]
  for d in ← getLCtx do
    unless d.isImplementationDetail do srcs := srcs.push (← instantiateMVars d.type)
  let mut out : Array Name := #[]
  for src in srcs do
    for c in src.getUsedConstants do
      if out.contains c then continue
      unless (env.getModuleIdxFor? c).isNone do continue
      let some (.defnInfo info) := env.find? c | continue
      if c.isInternalDetail || (← isInstance c) then continue
      let isPred ← forallTelescope info.type fun _ b => return b.isProp
      if isPred then out := out.push c
  return out

/-- The term of a parameter that is a fact: a lemma `l` with no modifier whose term is not a
name. -/
def ECClose.factTerm? (p : Syntax) : Option Syntax :=
  let q := if p.isOfKind ``Lean.Parser.Tactic.grindParam then p[0] else p
  if q.isOfKind ``Lean.Parser.Tactic.grindLemma && !q.getArgs.back!.isIdent then
    some q.getArgs.back! else none

/-- The facts among `smt_close`'s parameters (terms that are not a name: a lemma applied to
its arguments) and the others (lemma names, with modifiers). -/
def ECClose.splitParams (ps : Array Syntax) : Array Syntax × Array Syntax :=
  ps.partition fun p => (ECClose.factTerm? p).isSome

/-- The lemma names among `smt_close`'s parameters (plain identifiers). -/
def ECClose.paramIdents (ps : Array Syntax) : Array Ident :=
  ps.filterMap fun p => (p.find? (·.isIdent)).map (⟨·⟩)

/-- Whether a parameter of `smt_close` is the name of a closed lemma: a constant with no
argument but instances (`dbool_ll : is_lossless dbool`, an axiom of a theory such as
`gt0_n : 0 < n`).  There is nothing to instantiate in it: it is a fact (and `grind` does not
take it as a lemma when its instance is built from the context: "unknown free variable"). -/
def ECClose.isClosedLemma (p : Syntax) : MetaM Bool := do
  let q := if p.isOfKind ``Lean.Parser.Tactic.grindParam then p[0] else p
  -- (a `grindLemma` is an optional modifier and a term)
  unless q.isOfKind ``Lean.Parser.Tactic.grindLemma && q.getArgs.size == 2 && q[0].isNone &&
      q[1].isIdent do
    return false
  let [c] ← (resolveGlobalConst q[1] <|> pure []) | return false
  let some info := (← getEnv).find? c | return false
  forallTelescope info.type fun xs b => do
    unless ← isProp b do return false
    xs.allM fun x => return (← x.fvarId!.getBinderInfo).isInstImplicit

/-- The parameters of `smt_close` that `grind` is given: the lemma names that are not closed
lemmas (`ECClose.isClosedLemma`), with their modifiers. -/
def ECClose.grindParams (ps : Array Syntax) : MetaM (Array Syntax) := do
  (ECClose.splitParams ps).2.filterM fun p => return !(← ECClose.isClosedLemma p)

/-- The preparation of `smt_close`: its facts as hypotheses, before the preprocessing (which
puts them in the form of the goal). -/
syntax "smt_facts" (" [" Lean.Parser.Tactic.grindParam,* "]")? : tactic

elab_rules : tactic
  | `(tactic| smt_facts [$ls,*]) => do
    for p in ls.getElems do
      if let some t := ECClose.factTerm? p.raw then
        evalTactic (← `(tactic| have := $(⟨t⟩)))
      else if ← ECClose.isClosedLemma p.raw then
        let q := if p.raw.isOfKind ``Lean.Parser.Tactic.grindParam then p.raw[0] else p.raw
        evalTactic (← `(tactic| have := $(⟨q[1]⟩)))

/-- The closing step of `smt_close` on one goal: see `smt_close`. -/
syntax "smt_grind" (" [" Lean.Parser.Tactic.grindParam,* "]")? : tactic

elab_rules : tactic
  | `(tactic| smt_grind [$ls,*]) => do
    let lemmas : Array (TSyntax ``Lean.Parser.Tactic.grindParam) :=
      (← ECClose.grindParams (ls.getElems.map (·.raw))).map (⟨·⟩)
    let ids : Array Ident := ECClose.paramIdents (lemmas.map (·.raw))
    let preds ← localPreds
    let extra : Array (TSyntax ``Lean.Parser.Tactic.grindParam) ←
      preds.mapM fun c => `(Lean.Parser.Tactic.grindParam| $(mkIdent c):ident)
    let all := lemmas ++ extra
    -- (the first two alternatives are the closer as it was: a goal they close is closed as
    -- before)
    evalTactic (← `(tactic| first
      | grind [GaudisCrypt.EC.oget_some, $lemmas,*]
      | (ec_instances [$ids,*]; grind [GaudisCrypt.EC.oget_some, $lemmas,*])
      | grind [GaudisCrypt.EC.oget_some, $all,*]
      | linarith
      | (ec_instances_chain [$ids,*]; (try simp_reads_all); first
          | linarith
          | grind [GaudisCrypt.EC.oget_some, $all,*])))

/-- **EC's `smt(l₁, …)`**: `auto_close`'s preprocessing, the reads of the states as variables
(`generalize_reads_all`), their equations substituted, then `grind` with the lemmas `lᵢ`; if that
fails, once more with the lemmas' instances at the goal's terms as hypotheses (`ec_instances`:
EC's provers instantiate them there, `grind`'s E-matching may not, through definitions).

Then, what EC's provers also do:
* the predicates of the file being checked that the goal mentions are unfolded (EC's `pred`:
  its body is known to the provers; a predicate of the library is named, `smt_close [P]`);
* linear arithmetic over an ordered field (`linarith`: `grind` does not do it over the reals);
* the lemmas are instantiated in a chain (`ec_instances_chain`: at the terms of the instances
  too, their hypotheses taken from the context), for EC's `smt(l₁ l₂ l₃)` on a chain of
  (in)equalities between probabilities.

A parameter that is not a name — a lemma applied to its arguments, `smt_close [l A m]` — is a
fact: it becomes a hypothesis first.  So does the name of a lemma with no argument but
instances (`smt_close [dbool_ll, gt0_n]`). -/
syntax "smt_close" (" [" Lean.Parser.Tactic.grindParam,* "]")? : tactic

macro_rules
  | `(tactic| smt_close) => `(tactic| smt_close [])
  | `(tactic| smt_close [$ls,*]) => do
    `(tactic| focus (
      smt_facts [$ls,*]
      auto_prep
      all_goals try generalize_reads_all
      all_goals try subst_named
      all_goals try subst_vars
      all_goals smt_grind [$ls,*]))

end GaudisCrypt
