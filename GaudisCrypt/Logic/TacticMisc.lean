import GaudisCrypt.Logic.Judgment
import GaudisCrypt.Logic.ECReport

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

/-- The statement `s` resets locals (`reset_vars S`, what inlining a call leaves for the callee's
locals): not one of EC's statements, which inlines without them. -/
def isReset (s : Lean.Expr) : MetaM Bool := do
  let s ← openStmt s
  return s.isAppOf ``StmtWithHoles.assign && s.getAppArgs.any (·.isAppOf ``resetSetter)

/-- Whether each statement along the right spine of `s` is a reset (`isReset`), through the
`let`s of the locals. -/
partial def spineResets (s : Lean.Expr) : MetaM (List Bool) := do
  let s ← openStmt s
  if let .letE n ty val body _ := s then
    return ← withLetDecl n ty val fun fv => spineResets (body.instantiate1 fv)
  if s.isAppOfArity ``StmtWithHoles.seq 3 then
    return (← isReset (s.getArg! 1)) :: (← spineResets (s.getArg! 2))
  return [← isReset s]

/-- EC's statements of a spine (`spineResets`) as groups of ours: each with the resets just before
it (the sizes of the groups, in order). -/
def ecGroups (rs : List Bool) : Array Nat := Id.run do
  let mut out := #[]
  let mut pending := 0
  for r in rs do
    if r then pending := pending + 1
    else
      out := out.push (pending + 1)
      pending := 0
  if pending > 0 then out := out.push pending
  return out

/-- **EC's code gap `pos`** in the statement `s`, as our gap (the number of our statements before
it): `pos ≥ 0` after EC's first `pos` statements, `-k` after the `k`-th from the end (`-1`: after
the last); EC's statements are `ecGroups` (the resets inlining leaves belong to the statement
after them, so they are not counted). -/
def ecGapIn (pos : Int) (s : Lean.Expr) : MetaM Nat := do
  let gs := ecGroups (← spineResets s)
  let n := gs.size
  let gap : Int := if pos ≥ 0 then pos else n + pos + 1
  unless 0 ≤ gap ∧ gap ≤ n do
    throwError "position {pos} is outside a statement of {n} statements"
  return (gs.extract 0 gap.toNat).foldl (· + ·) 0

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

/-- The wp rule for trailing deterministic code (`Stmt.Det`), for Hoare triples. -/
theorem hoare_seq_det {A B : ProgramState → Prop} {s d : Stmt} {upd : ProgramState → ProgramState}
    (hd : Stmt.Det d upd) (h : hoareStmt A s (fun σ => B (upd σ))) :
    hoareStmt A (.seq s d) B :=
  hoare_seq (hoareStmt_of_wp fun σ hB => by
    rw [hd]
    exact Set.indicator_of_notMem (not_not.mpr hB) _) h

/-- The wp rule for a trailing sampling, for Hoare triples: every value in the support. -/
theorem hoare_seq_sample {α} {A B : ProgramState → Prop} {s : Stmt}
    {x : Setter α ProgramState} {e : Getter (SubProbability α) ProgramState}
    (h : hoareStmt A s (fun σ => ∀ a ∈ (e.get σ).support, B (x.set a σ))) :
    hoareStmt A (.seq s (.sample x e)) B :=
  hoare_seq (hoare_sample_wp x B) h

run_meta registerJudgment {
  head := ``hoareStmt
  stmtArg := 1
  equivLemma := ``hoareStmt_of_equiv
  transportLemma := ``hoareStmt_of_equivInLens }

/-- On a goal about a statement judgment (`hoareStmt A s B`, or any registered one): rewrite the
statement with `f`, which returns the new statement `s'` and a proof of `s.Equiv s'` (as
`flattenSeq` and `HoareSplit.splitSeq` do), and continue with the judgment about `s'`.  The
conditions are untouched — `conv` for the statement of a judgment (`Judgment.onStmt`). -/
def hoareOnStmt (f : Lean.Expr → MetaM (Lean.Expr × Lean.Expr)) (g : MVarId) : MetaM MVarId :=
  Judgment.onStmt f g

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

/-- `s` is the state `σ`, or its globals or locals. -/
def isStateOf (σ : FVarId) (s : Lean.Expr) : Bool :=
  s.isFVarOf σ ||
    ((s.isAppOfArity ``ProgramState.globals 1 || s.isAppOfArity ``ProgramState.locals 1)
      && s.appArg!.isFVarOf σ)

/-- `x.get s` for `x` a lens or getter into `ProgramState` or `VariableAssignment` (its type `X`):
a lens read through `Lens.toGetter`, and a read of the globals at `s.globals`.  `none` for any
other type. -/
def readOfContainer (X x s : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let X ← whnfR X
  let isLens := X.isAppOfArity ``Lens 2
  unless isLens || X.isAppOfArity ``Getter 2 do return none
  let M := X.appArg!
  let s ← if ← withReducible (isDefEq M (mkConst ``ProgramState)) then pure s
    else if ← withReducible (isDefEq M (mkConst ``VariableAssignment)) then
      pure (mkApp (mkConst ``ProgramState.globals) s)
    else return none
  let g ← if isLens then mkAppM ``Lens.toGetter #[x] else pure x
  return some (← mkAppM ``Getter.get #[g, s])

/-- One step of `unfoldReads` at `e`, if a rule applies.  Every rule is a definitional unfolding,
and fires only on a read of the state `σ` itself:

* `(Getter.mk f).get σ` ↦ `f σ`, and a `let` of the `CurrentState` (as `GaudiExpr[ ]` binds it)
  is substituted;
* `eval x` in the current state `⟨σ⟩` ↦ `x.get σ` (or `x.get σ.globals` for a global);
* `(AsGetter.toG x).get σ` ↦ `x.get σ`;
* `(x.pair y).get σ` ↦ `(x.get σ, y.get σ)`;
* `(x.chain Lens.fst).get σ` ↦ `(x.get σ).1`, and likewise for `Lens.snd`.

`eval`/`CurrentState` (`Syntax/ExpressionSyntax.lean`) are not imported here, so they are matched
by name. -/
partial def unfoldReadStep (σ : FVarId) (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if e.isAppOfArity `GaudisCrypt.eval 5 then
    let cs := e.getArg! 3
    unless cs.isAppOfArity `GaudisCrypt.CurrentState.mk 1 && cs.appArg!.isFVarOf σ do
      return none
    return ← readOfContainer (← inferType (e.getArg! 4)) (e.getArg! 4) cs.appArg!
  unless e.isAppOfArity ``Getter.get 4 && isStateOf σ e.appArg! do return none
  let s := e.appArg!
  let g := e.getArg! 2
  if g.isAppOfArity ``Getter.mk 3 then
    let mut r := g.appArg!.beta #[s]
    while true do
      let .letE _ t v b _ := r | break
      unless t.isConstOf `GaudisCrypt.CurrentState do break
      r := b.instantiate1 v
    return some r
  if g.isAppOfArity ``AsGetter.toG 5 then
    return ← readOfContainer (← inferType g.appArg!) g.appArg! s
  unless g.isAppOfArity ``Lens.toGetter 3 do return none
  let l := g.appArg!
  let getAt (x s : Lean.Expr) : MetaM Lean.Expr := do
    mkAppM ``Getter.get #[← mkAppM ``Lens.toGetter #[x], s]
  if l.isAppOfArity ``Lens.pair 6 then
    return some (← mkAppM ``Prod.mk #[← getAt (l.getArg! 3) s, ← getAt (l.getArg! 4) s])
  if l.isAppOfArity ``Lens.chain 5 then
    let y := l.getArg! 4
    let fst := y.isAppOfArity ``Lens.fst 2
    unless fst || y.isAppOfArity ``Lens.snd 2 do return none
    let inner ← getAt (l.getArg! 3) s
    -- the component of a pair read directly, not as a projection of the pair
    if let some p ← unfoldReadStep σ inner then
      if p.isAppOfArity ``Prod.mk 4 then return some (p.getArg! (if fst then 2 else 3))
    return some (← mkAppM (if fst then ``Prod.fst else ``Prod.snd) #[inner])
  -- a pair or a component of one in the locals or globals: read it there
  if s.isFVarOf σ && (l.isAppOfArity ``Lens.intoGlobal 2 || l.isAppOfArity ``Lens.intoLocal 2) then
    let x := l.appArg!
    if x.isAppOfArity ``Lens.pair 6 || x.isAppOfArity ``Lens.chain 5 then
      let part := if l.isAppOfArity ``Lens.intoGlobal 2 then ``ProgramState.globals
        else ``ProgramState.locals
      return some (← getAt x (mkApp (mkConst part) s))
  return none

/-- Unfold the reads of `σ` in `e` that are not reads of a lens or getter as it is, but of
an expression built around them (`unfoldReadStep`), until none is left: what remains are reads
`x.get σ` (or `x.get σ.globals`) of the lenses and getters themselves.  A definitional rewrite. -/
def unfoldReads (σ : FVarId) (e : Lean.Expr) (foldRenames : Bool := true) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    -- the globals of the state an inlined call renamed (`(Flatten.rename r).chain Flatten.trafo`,
    -- `Flatten.emb`): renaming touches the locals only, they are the state's globals (by `rfl`,
    -- `globals_chain_get`, …); generalized as a state of its own they would be unrelated to them
    if foldRenames && e.isAppOfArity ``ProgramState.globals 1 then
      let a := e.appArg!
      if a.isAppOfArity ``Getter.get 4 && isStateOf σ a.appArg! &&
          ((a.getArg! 2).find? fun t => t.isConstOf `GaudisCrypt.Flatten.trafo ||
            t.isConstOf `GaudisCrypt.Flatten.emb || t.isAppOf `GaudisCrypt.Flatten.rename).isSome then
        let s := a.appArg!
        let r := mkApp (mkConst ``ProgramState.globals) s
        if (← inferType s).isConstOf ``ProgramState then
          if ← withDefault (isDefEq e r) then return .visit r
    match ← unfoldReadStep σ e with
    | some r => return .visit r
    | none => return .done e)

/-- The reads `Getter.get g s` in `e`, `s` the state `σ` or its globals or locals, in order of
appearance, without syntactic duplicates.  Only closed ones (a read under a binder that mentions the
bound variable cannot be generalized), and only through a getter that does not itself mention
`σ`. -/
partial def collectReadsOf (σ : FVarId) (e : Lean.Expr) (acc : Array Lean.Expr := #[]) :
    Array Lean.Expr :=
  if e.isAppOfArity ``Getter.get 4 && isStateOf σ e.appArg! && !e.hasLooseBVars
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

/-- The `Decidable` instances under `decide p` re-synthesized for `p` as it stands: simplifying
the reads in `p` (`simp_reads`) leaves the instance about the old `p` — equal by unfolding, but
not at instances transparency, so that rewriting or generalizing a read through the `decide`
fails ("not type-correct").  Each instance is replaced by the synthesized one when the two are
equal by definition (a `change`). -/
def normDecide (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun t => do
    if t.isAppOfArity ``Decidable.decide 2 then
      let p := t.getArg! 0
      let i := t.getArg! 1
      if p.hasLooseBVars then return .continue
      try
        let j ← synthInstance (mkApp (mkConst ``Decidable) p)
        if j != i then
          if ← withDefault (isDefEq i j) then
            return .done (mkApp2 (mkConst ``Decidable.decide) p j)
      catch _ => pure ()
    return .continue)

/-- `normDecide` on the goal (a `change`). -/
def normDecideGoal (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let ty' ← normDecide ty
  if ty' == ty then return g
  g.replaceTargetDefEq ty'

/-- A region of variables, `X.footprint = R` (`X` their `Lens.pair`): equal on it is equal on
`X` (EC's `={glob C}` as `={C.c, C.queries}`). -/
theorem touched_getter_eq_iff_of_lens {β : Type} {X : Lens β VariableAssignment}
    {R : Footprint VariableAssignment} (hR : X.footprint = R) (a b : VariableAssignment) :
    (R.touched_getter.get a = R.touched_getter.get b) = (X.get a = X.get b) := by
  subst hR; exact propext (Lens.footprint_touched_getter_eq_iff X a b)

/-- The variables' lens of a region of variables `x₁.footprint ⊔ (x₂.footprint ⊔ …)`: their
`Lens.pair` (EC's `glob C` of a concrete module, `glob_region`). -/
partial def regionLens? (R : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let R ← instantiateMVars R
  if R.isAppOfArity ``Lens.footprint 3 then return some R.appArg!
  if R.getAppNumArgs ≥ 2 then
    let n := R.getAppNumArgs
    if R.isAppOf ``Max.max || R.isAppOf ``SemilatticeSup.sup then
      let some a ← regionLens? (R.getArg! (n - 2)) | return none
      let some b ← regionLens? (R.getArg! (n - 1)) | return none
      try
        -- `Lens.pair a b`, its instance `[Lens.Disjoint a b]` (trailing) synthesized
        let p ← mkAppM ``Lens.pair #[a, b]
        let .forallE _ d _ _ ← whnf (← inferType p) | return some p
        return some (mkApp p (← synthInstance d))
      catch _ => return none
  return none

/-- **EC's `glob M` of a concrete module given by its code**: for a region `R` (`FVP.fvP M`), a
proof of `∀ a b, (R.touched_getter.get a = R.touched_getter.get b) = (X.get a = X.get b)`, `X` the
pair of the variables `M` writes (`Logic/GlobWrites.lean` sets it: the reading needs the module
footprint tactics, which come later than this file). -/
initialize globRegionHook : IO.Ref (Lean.Expr → MetaM (Option Lean.Expr)) ←
  IO.mkRef fun _ => pure none

/-- EC's `glob C` of a concrete module, a region of variables `x₁.footprint ⊔ (x₂.footprint ⊔ …)`
(`glob_region`): its equalities `R.touched_getter.get a = R.touched_getter.get b` as the
variables' (`={C.c, C.queries}`: `touched_getter_eq_iff_of_lens` with their `Lens.pair`, the tuple
taken apart), before the reads are generalized (a generalized region would be a value unrelated
to the variables).  Nothing if no such region occurs. -/
def globTuples (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let mut thms : SimpTheorems := {}
  let mut found := false
  let mut seen : Array Lean.Expr := #[]
  let cands := (← (Meta.transform (m := StateT (Array Lean.Expr) MetaM) ty (pre := fun e => do
    if e.isAppOfArity ``Footprint.touched_getter 2 then
      modify (·.push e.appArg!)
    return .continue)).run #[]).2
  for R in cands do
    if seen.contains R || R.hasLooseBVars then continue
    seen := seen.push R
    let some X ← regionLens? R | do
      -- a concrete module's region, read off its code
      let some pf ← (try (← globRegionHook.get) R catch _ => pure none) | continue
      thms ← thms.add (.other (← mkFreshUserName `globTuple)) #[] pf
      found := true
      continue
    -- `X.footprint = R`, by `Footprint.lens_pair`
    let lhs ← mkAppM ``Lens.footprint #[X]
    let hR ← try
        let t ← ({} : SimpTheorems).addConst ``Footprint.lens_pair
        let ctx ← Simp.mkContext (simpTheorems := #[t]) (congrTheorems := ← getSimpCongrTheorems)
        let (r, _) ← simp lhs ctx
        unless ← isDefEq r.expr R do failure
        r.getProof
      catch _ => continue
    let pf ← mkAppM ``touched_getter_eq_iff_of_lens #[hR]
    let pf ← mkLambdaFVars #[] pf
    thms ← thms.add (.other (← mkFreshUserName `globTuple)) #[] pf
    found := true
  if !found then return g
  thms ← thms.addConst ``Prod.mk.injEq
  thms ← thms.addDeclToUnfold ``Lens.pair
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp ty ctx
  if r.expr == ty then return g
  applySimpResultToTarget g ty r

/-- `globTuples` on the target and on every hypothesis mentioning a region's `touched_getter`
(each reverted, rewritten, and introduced again under its name). -/
def globTuplesAll (g : MVarId) : MetaM MVarId := do
  let g ← globTuples g
  -- the hypotheses mentioning a region, reverted together (their ids change on reverting)
  let hs ← g.withContext do
    let mut hs := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if (t.find? (·.isAppOfArity ``Footprint.touched_getter 2)).isSome then hs := hs.push d.fvarId
    pure hs
  if hs.isEmpty then return g
  let (fvs, g1) ← g.revert hs (preserveOrder := true)
  let g2 ← globTuples g1
  let (_, g3) ← g2.introNP fvs.size
  return g3

/-- On a goal `∀ σ : ProgramState, P σ`: first unfold the reads of `σ` through expressions,
pairs and the like down to reads of lenses and getters (`unfoldReads`), then generalize every read
`g.get σ` (or `g.get σ.globals`) to a universally quantified value (`readBaseName`, made unique
against the context, the goal's binders and each other).  Reads that agree up to reducible
unfolding become one value.  If `σ` is then unused it is dropped, giving `∀ m x …, P'`; otherwise
it stays in front, `∀ σ m x …, P'`.  With no read left, only the unfolding is done (and `σ`
dropped if unused).  Atomic: if it fails, nothing is assigned (callers fall back to the goal as
it was, and a half-done assignment would lose the new goal). -/
def generalizeReads (g : MVarId) : MetaM MVarId := commitIfNoEx <| g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let .forallE _ dom _ _ := ty
    | throwError "generalizeReads: expected a goal `∀ σ : ProgramState, …`, got{indentExpr ty}"
  unless ← isDefEq dom (mkConst ``ProgramState) do
    throwError "generalizeReads: the first binder is not a `ProgramState`:{indentExpr ty}"
  let (σ, g) ← g.intro1
  g.withContext do
    let g ← g.change (← unfoldReads σ (← instantiateMVars (← g.getType)))
    let g ← try globTuples g catch _ => pure g
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
    let (xs, g) ← if args.isEmpty then pure (#[], g) else g.generalize args
    let (g, keepσ) ← try pure (← g.clear σ, false) catch _ => pure (g, true)
    let (_, g) ← g.revert (if keepσ then #[σ] ++ xs else xs) (preserveOrder := true)
    return g

/-- `generalizeReads`, for the tactic `tac`: if it fails, the goal stays about the states, and
`tac` says so (`ECReport.fallback`). -/
def generalizeReadsOr (tac : String) (g : MVarId) : MetaM MVarId := do
  -- no state to generalize (the goal is not `∀ σ : ProgramState, …`): nothing to do, nothing
  -- to say
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let .forallE _ dom _ _ := ty | return g
  unless ← isDefEq dom (mkConst ``ProgramState) do return g
  try generalizeReads g
  catch e =>
    ECReport.fallback tac m!"the reads are not generalized: the goal stays about the states" (some e)
    pure g

end GaudisCrypt.TacticMisc

open Lean Meta Elab Tactic in
/-- `TacticMisc.normDecide` on the goal and every hypothesis (the instances under `decide`
about the propositions as they stand). -/
elab "norm_decide" : tactic => withMainContext do
  let mut g ← getMainGoal
  g ← GaudisCrypt.TacticMisc.normDecideGoal g
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let t' ← GaudisCrypt.TacticMisc.normDecide t
    if t' != t then g ← g.replaceLocalDeclDefEq d.fvarId t'
  replaceMainGoal [g]

open Lean Meta Elab Tactic in
/-- EC's `={glob C}` of a concrete module as its variables' equalities (`TacticMisc.globTuples`),
in the goal and the hypotheses. -/
elab "glob_tuples" : tactic => withMainContext do
  replaceMainGoal [← GaudisCrypt.TacticMisc.globTuplesAll (← getMainGoal)]
