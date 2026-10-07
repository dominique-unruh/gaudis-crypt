import GaudisCrypt.Logic.StmtEquiv

/-!
# Meta helpers for statement rewriting

Generic pieces of the statement-rewriting tactics: exposing a statement's head (`openStmt`),
re-associating sequences (`flattenSeq`), and running a statement rewriter on the statement of a
Hoare triple (`hoareOnStmt`).  A rewriter returns its result together with a proof of
`StmtWithHoles.Equiv` (`Logic/StmtEquiv.lean`).  Users: `Inline.lean` and `HoareSplit.lean`.
-/

namespace GaudisCrypt.TacticMisc

open Lean Meta

/-! ## Exposing statements -/

/-- The statement heads a traversal stops at.  `call` is one: `whnf` would step through it to the
`call'` it is defined as, which spreads the callee over several arguments and no longer prints as
a call.  `applyLens` and `weaken` are the inliner's (`Inline.lean`, which imports this file), and
so are named unchecked. -/
def stmtHeads : Array Name :=
  #[``StmtWithHoles.skip, ``StmtWithHoles.sample, ``StmtWithHoles.call', ``StmtWithHoles.call,
    ``Stmt.call, ``StmtWithHoles.hole, ``StmtWithHoles.seq, ``StmtWithHoles.ifThenElse,
    ``StmtWithHoles.while, ``StmtWithHoles.assign,
    `GaudisCrypt.StmtWithHoles.applyLens, `GaudisCrypt.StmtWithHoles.weaken]

/-- Head reduction that keeps `let`s: beta, iota and projections only. -/
def whnfNoZeta (e : Lean.Expr) : MetaM Lean.Expr :=
  withConfig (fun c => { c with zeta := false, zetaDelta := false }) (whnfCore e)

/-- Expose a statement position: reduce until a statement head (or a `let`) is visible, without
zeta-reducing and without stepping through `assign` or `call`. -/
partial def openStmt (e : Lean.Expr) : MetaM Lean.Expr := do
  let e' ← whnfNoZeta e
  if e'.isLet then return e'
  if let some n := e'.getAppFn.constName? then
    if stmtHeads.contains n then return e'
  match ← unfoldDefinition? e' with
  | some e'' => openStmt e''
  | none => return e'

/-- Is this `skip`? -/
def isSkip (e : Lean.Expr) : Bool := e.isAppOf ``StmtWithHoles.skip

/-- Is this `_ <- e`, an assignment with no effect? -/
def isThrowawayAssign (e : Lean.Expr) : Bool :=
  e.isAppOfArity ``StmtWithHoles.assign 4 && (e.getArg! 2).isAppOf ``Setter.throwaway

/-- `a.Equiv a`. -/
def mkEquivRefl (s : Lean.Expr) : MetaM Lean.Expr := mkAppM ``StmtWithHoles.Equiv.refl #[s]

/-! ## `flattenSeq` -/

/-- Concatenate two already right-nested sequences, dropping `skip`s and `_ <- e`s: returns the
result together with a proof of `(a.seq b).Equiv result`. -/
partial def concatSeq (a b : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  if isSkip a then return (b, ← mkAppM ``StmtWithHoles.Equiv.skip_seq #[b])
  if isSkip b then return (a, ← mkAppM ``StmtWithHoles.Equiv.seq_skip #[a])
  if isThrowawayAssign a then
    return (b, ← mkAppM ``StmtWithHoles.Equiv.throwaway_seq #[a.getArg! 3, b])
  if isThrowawayAssign b then
    return (a, ← mkAppM ``StmtWithHoles.Equiv.seq_throwaway #[a, b.getArg! 3])
  if a.isAppOfArity ``StmtWithHoles.seq 3 then
    let x := a.getAppArgs[1]!
    let y := a.getAppArgs[2]!
    let (r, p) ← concatSeq y b
    let p₁ ← mkAppM ``StmtWithHoles.Equiv.seq_assoc #[x, y, b]
    let p₂ ← mkAppM ``StmtWithHoles.EquivInLens.seq #[← mkEquivRefl x, p]
    let (r', p₃) ← if isSkip r then pure (x, ← mkAppM ``StmtWithHoles.Equiv.seq_skip #[x])
      else do let s ← mkAppM ``StmtWithHoles.seq #[x, r]; pure (s, ← mkEquivRefl s)
    return (r', ← mkAppM ``StmtWithHoles.Equiv.trans
      #[← mkAppM ``StmtWithHoles.Equiv.trans #[p₁, p₂], p₃])
  let s ← mkAppM ``StmtWithHoles.seq #[a, b]
  return (s, ← mkEquivRefl s)

/-- Re-associate `seq` to the right and drop `skip`s and `_ <- e`s, returning the result and a
proof of `‹input›.Equiv result`.  Never fails; `if`s are not otherwise touched. -/
partial def flattenSeq (s₀ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let s ← openStmt s₀
  match s with
  | .letE n ty val body _ =>
      withLetDecl n ty val fun fv => do
        let (r, p) ← flattenSeq (body.instantiate1 fv)
        return (← mkLetFVars #[fv] r (usedLetOnly := false),
                ← mkLetFVars #[fv] p (usedLetOnly := false))
  | _ =>
    let args := s.getAppArgs
    match s.getAppFn.constName? with
    | some ``StmtWithHoles.seq =>
        let (a, pa) ← flattenSeq args[1]!
        let (b, pb) ← flattenSeq args[2]!
        let (r, p) ← concatSeq a b
        let pseq ← mkAppM ``StmtWithHoles.EquivInLens.seq #[pa, pb]
        return (r, ← mkAppM ``StmtWithHoles.Equiv.trans #[pseq, p])
    | some ``StmtWithHoles.ifThenElse =>
        let (t, pt) ← flattenSeq args[2]!
        let (e, pe) ← flattenSeq args[3]!
        return (← mkAppM ``StmtWithHoles.ifThenElse #[args[1]!, t, e],
                ← mkAppM ``StmtWithHoles.Equiv.ifThenElse #[args[1]!, pt, pe])
    | some ``StmtWithHoles.while =>
        let (b, pb) ← flattenSeq args[2]!
        return (← mkAppM ``StmtWithHoles.while #[args[1]!, b],
                ← mkAppM ``StmtWithHoles.Equiv.while #[args[1]!, pb])
    | _ => return (s, ← mkEquivRefl s)

/-! ## Rewriting the statement of a triple -/

/-- On a goal `hoareStmt A s B`: rewrite the statement with `f`, which returns the new statement
`s'` and a proof of `s.Equiv s'` (as `flattenSeq` and `HoareSplit.splitSeq` do), and continue with
the triple about `s'`.  The conditions are untouched — `conv` for the statement of a triple. -/
def hoareOnStmt (f : Lean.Expr → MetaM (Lean.Expr × Lean.Expr)) (g : MVarId) : MetaM MVarId :=
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOfArity ``hoareStmt 3 do
      throwError "expected a goal `hoareStmt A s B`, got{indentExpr ty}"
    let (A, s, B) := (ty.getArg! 0, ty.getArg! 1, ty.getArg! 2)
    let (s', p) ← f s
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``hoareStmt #[A, s', B]) (← g.getTag)
    g.assign
      (← mkAppOptM ``hoareStmt_of_equiv #[some A, some B, some s, some s', some p, some g'])
    return g'.mvarId!

/-! ## Reads of the state as plain values

What the Hoare rules leave is a goal `∀ σ, … x.get σ …`: the state is only read, through lenses
(local variables, globals, anything else).  `generalizeReads` replaces each read by a universally
quantified value, giving `∀ x, … x …`; the same read, wherever it occurs, becomes the same value.

Only one direction is proved: the new goal implies the old one (a value for every read, not only
the values some state has).  So it is always sound, but the new goal can be strictly stronger: when
`σ` is still used elsewhere (it then stays, `∀ σ x, …`, with the link between `x` and `σ` cut), or
when two of the lenses overlap (a variable and a pair containing it, say), since their values are
then quantified independently.  For distinct variables and no other use of `σ`, nothing is lost. -/

/-- Wrappers a read is named through: the name comes from their last argument (the inner lens). -/
def readNameWrappers : List String :=
  ["chain", "chainGetter", "toGetter", "toG", "intoLocal", "intoGlobal", "liftLens"]

/-- Generic combinators a read is not named after. -/
def readNameStoplist : List String := ["mk", "pair", "fst", "snd", "id"]

/-- `s` as an identifier: only letters, digits, `_` and `'`, not starting with a digit, and `v`
if nothing is left (a made-up name like `@.x` becomes `x`). -/
def sanitizeName (s : String) : String :=
  let s := String.ofList (s.toList.filter fun c => c.isAlphanum || c == '_' || c == '\'')
  if s.isEmpty then "v" else if s.front.isDigit then "v" ++ s else s

/-- A name for the value a read through the getter `g` yields: the variable's name for a local
or global variable slot (`(varLens ⟨n, …⟩).intoLocal` / `.intoGlobal`, also spelled
`localVarLens n T`); else, through the wrappers of `readNameWrappers`, the last component of the
lens's head constant or the name of the local it is; else `v`. -/
partial def readBaseName (g : Lean.Expr) : MetaM String := do
  -- not `whnfR` on `g`: that turns `Lens.toGetter x` into the primitive projection `x.1`
  if let some n ← varName? g then return sanitizeName n
  match g.getAppFn with
  | .const c _ =>
      match c with
      | .str _ s =>
          if readNameWrappers.contains s && g.getAppNumArgs > 0 then readBaseName g.appArg!
          else if readNameStoplist.contains s then return "v"
          else return sanitizeName s
      | _ => return "v"
  | .fvar x => return sanitizeName (← x.getUserName).eraseMacroScopes.toString
  | _ => return "v"
where
  varName? (l : Lean.Expr) : MetaM (Option String) := do
    let l ← whnfR l
    unless l.isAppOfArity ``Lens.intoLocal 2 || l.isAppOfArity ``Lens.intoGlobal 2 do
      return none
    let v ← whnfR l.appArg!
    unless v.isAppOfArity ``varLens 1 do return none
    let name ← whnfR v.appArg!
    unless name.isAppOfArity ``VariableName.mk 5 do return none
    let .lit (.strVal n) ← instantiateMVars (name.getArg! 0) | return none
    return some n

/-- The reads `Getter.get g σ` in `e`, in order of appearance, without syntactic duplicates.  Only
closed ones (a read under a binder that mentions the bound variable cannot be generalized), and
only through a getter that does not itself mention `σ`. -/
partial def collectReadsOf (σ : FVarId) (e : Lean.Expr) (acc : Array Lean.Expr := #[]) :
    Array Lean.Expr :=
  if e.isAppOfArity ``Getter.get 4 && e.appArg!.isFVarOf σ && !e.hasLooseBVars
      && !(e.getArg! 2).containsFVar σ then
    if acc.contains e then acc else acc.push e
  else match e with
    | .app f a => collectReadsOf σ a (collectReadsOf σ f acc)
    | .lam _ t b _ | .forallE _ t b _ => collectReadsOf σ b (collectReadsOf σ t acc)
    | .letE _ t v b _ => collectReadsOf σ b (collectReadsOf σ v (collectReadsOf σ t acc))
    | .mdata _ b | .proj _ _ b => collectReadsOf σ b acc
    | _ => acc

/-- The binder names inside `e`, so that a new name does not shadow them. -/
partial def binderNamesIn (e : Lean.Expr) (acc : Array String := #[]) : Array String :=
  match e with
  | .app f a => binderNamesIn a (binderNamesIn f acc)
  | .lam n t b _ | .forallE n t b _ =>
      binderNamesIn b (binderNamesIn t (acc.push n.eraseMacroScopes.toString))
  | .letE n t v b _ =>
      binderNamesIn b (binderNamesIn v (binderNamesIn t (acc.push n.eraseMacroScopes.toString)))
  | .mdata _ b | .proj _ _ b => binderNamesIn b acc
  | _ => acc

/-- `base`, or `base1`, `base2`, … if taken. -/
def freshIn (used : Array String) (base : String) : String := Id.run do
  if !used.contains base then return base
  let mut i := 1
  while used.contains (base ++ toString i) do i := i + 1
  return base ++ toString i

/-- On a goal `∀ σ : ProgramState, P σ`: generalize every read `g.get σ` to a universally
quantified value (`readBaseName`, made unique against the context, the goal's binders and each
other).  Reads that agree up to reducible unfolding become one value.  If `σ` is then unused it is
dropped, giving `∀ m x …, P'`; otherwise it stays in front, `∀ σ m x …, P'`. -/
def generalizeReads (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let .forallE _ dom _ _ := ty
    | throwError "generalizeReads: expected a goal `∀ σ : ProgramState, …`, got{indentExpr ty}"
  unless ← isDefEq dom (mkConst ``ProgramState) do
    throwError "generalizeReads: the first binder is not a `ProgramState`:{indentExpr ty}"
  let (σ, g) ← g.intro1
  g.withContext do
    let body ← instantiateMVars (← g.getType)
    let mut used := binderNamesIn body
    for d in ← getLCtx do
      used := used.push d.userName.eraseMacroScopes.toString
    let mut reads : Array Lean.Expr := #[]
    let mut args : Array GeneralizeArg := #[]
    for r in collectReadsOf σ body do
      -- `generalize` abstracts up to instances-transparency defeq, so a read that agrees with
      -- an earlier one is taken by it, and would only leave an unused variable behind
      if ← reads.anyM fun r' => withReducible (isDefEq r r') then continue
      reads := reads.push r
      let n := freshIn used (← readBaseName (r.getArg! 2))
      used := used.push n
      args := args.push { expr := r, xName? := some (Name.mkSimple n) }
    if args.isEmpty then
      throwError "generalizeReads: no read of the state in{indentExpr ty}"
    let (xs, g) ← g.generalize args
    let (g, keepσ) ← try pure (← g.clear σ, false) catch _ => pure (g, true)
    let (_, g) ← g.revert (if keepσ then #[σ] ++ xs else xs) (preserveOrder := true)
    return g

end GaudisCrypt.TacticMisc
