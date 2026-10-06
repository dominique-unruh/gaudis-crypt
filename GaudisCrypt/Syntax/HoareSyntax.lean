import GaudisCrypt.Logic.Hoare
import GaudisCrypt.Syntax.ModuleSyntax

/-!
# Concrete syntax for Hoare triples

`hoare[ P ==> Q ] { … }` is the triple `hoareStmt P p Q`, where the body is parsed by the
statement parser of `ProgramSyntax.lean` (the same one `proc` and the module syntax use):

    hoare[ §x = 1 ==> §x = 2 ] {
      var u : Nat;
      let one := 1;
      u <- $x + one;
      x <- $u;
    }

Like a `proc` body, the block may open with `var` declarations and may contain Lean
binders (`let`/`have`/`letI`/`haveI`) in statement position.  Both kinds of binder are
**repeated around `P` and `Q`**: the `var`s (as `letI`s, exactly as in the body) and
the binders on the *spine* of the statement sequence (`ProgramSyntax.wrapSpineBinders`,
which is what `proc` does for its return value).  So a precondition or postcondition may
mention the local program variables and the body's `let`s.  A `var x : T` binds `x` to its
local slot `localVarLens "x" T`, so `§x` in a condition is literally the term the body reads
and writes; the type comes from the declaration.

`P` and `Q` are ordinary `GaudiExpr[ ]` expressions of type `Prop`, so program variables
are read with the `$`/`§` sigil.  The state they are read at is the whole `ProgramState`
(globals and locals); a triple about a procedure is the second form below.

Both forms also **print** in this surface syntax, and round-trip: the delaborators are at the
end of each of the two sections below, and like the ones in `ProgramSyntax.lean` they step
aside under `pp.gaudisCrypt false` and whenever the term is not of the shape the notation
builds.

# Concrete syntax for procedure triples

`hoare[ M (x, m) : P ==> Q ]` is `hoareProc P' M.procedure Q'`, where `M` is a procedure
module (or a bare `Procedure`) and `x, m` name its parameters:

    hoare[ S.commit (x, m) : §x = §h ==> §res ≠ §h ]

The precondition sees the parameters and the globals, the postcondition `res` and the
globals — `hoareProc`'s own shape, which does *not* give the postcondition the entry
parameters.  A property relating the result to an argument is not a `hoareProc` triple and has
to be stated another way (save the argument into a global, or use a relational judgment);
EasyCrypt imposes the same restriction.

Everything is read with the sigil, parameters included: `§x` for a parameter, `§y` for a
global, `§res` for the result and `§params` for the whole argument tuple.  One spelling for
every variable, so a condition can be lifted out of a procedure body unchanged.

The parameter names may be left out — `hoare[ S.commit : … ]` — in which case they are looked
up in the `@[gaudiProcParamNames]` attribute that `moduletype` and `module` record them in.
Names written at the triple win over the recorded ones, with a warning if they disagree; an
explicit `()` asserts that the procedure takes none.  Without recorded names, they are read off
the procedure itself if its `parameterNames` reduce to a literal list (as for a `proc` literal);
a procedure whose names cannot be found either way (a variable, say) has to have them written.

`M` is parsed at `term:max`, so an applied module expression needs parentheses:
`hoare[ (Module.app X A) (x) : … ]`.  Without that, `M (x, m)` would parse as an application
and swallow the parameter list.

There is no `{ … }` block in this form: no body is written at the triple, and the procedure's
own locals are invisible to `hoareProc`, so there is nothing for a `var` to declare.  A Lean
`let`/`have` in front of the triple scopes over both conditions.

## How it elaborates

The two conditions are plain lambdas of exactly the shape `hoareProc` asks for:

    hoareProc (sig := ‹sig›)
      (fun args σ =>
        let params : Getter _ ProgramState := Getter.mk fun _ => args
        let x : Getter _ ProgramState := Getter.mk fun _ => (Lens.id.ofst).get args
        let m : Getter _ ProgramState := Getter.mk fun _ => (Lens.id.osnd).get args
        (GaudiExpr[ P ] : Getter Prop ProgramState).get ⟨σ, VariableAssignment.init⟩)
      (Module.Proc.procedure M)
      (fun res σ =>
        let res : Getter _ ProgramState := Getter.mk fun _ => res
        (GaudiExpr[ Q ] : Getter Prop ProgramState).get ⟨σ, VariableAssignment.init⟩)

Points worth knowing:

* `GaudiExpr[ ]` reads from a `ProgramState` (that is `CurrentState`'s field type), so the
  condition is read at `⟨σ, VariableAssignment.init⟩`: the globals of the triple, and locals that
  no condition can mention (there is no `var` here).  Globals resolve through the
  `Evaluatable (Lens T State) T` instance.  The parameters and the result are not locals of
  this state but getters that ignore it, so no argument tuple has to be packed into the state
  and the result never has to masquerade as a variable.
* A parameter's getter is the projection `(mkChain (navSteps k n)).get args` out of the
  argument tuple `sig.ParamType`.  It is *not* the callee's slot `localVarLens "x" T`: under
  `hoareProc`'s shape the precondition is about the argument tuple, not about the callee's
  entry frame (stating it over that frame would change `hoareProc`'s type).
* The parameter binders are plain `let`s, not `letI`s: they have to *survive* elaboration, so
  that a condition mentioning a parameter prints as `§x` rather than as the inlined slot getter,
  and so that the written names stay recoverable from the term.  Every name is bound whether a
  condition uses it or not; the binder idents carry no source position, so an unmentioned one
  does not trip the unused-variable linter.
* `sig` is passed explicitly, because `ProcedureSignature.ParamType ?sig ≟ A × B` does not
  determine `?sig`.  This is a term elaborator rather than a macro for that reason: it
  elaborates `M` first, and then has `sig` as an `Expr` to hand to `exprToSyntax` — which is
  also how the binder types `args : sig.ParamType` and `res : sig.ret` get written without
  reconstructing any type syntax.

## Why `hoare[` and not `hoare [`

The leading atom is glued to the bracket on purpose.  A term-level syntax cannot start with
a *non-reserved* identifier-like atom — Lean's leading-parser table never reaches it, so a
production opening with `&"hoare"` is simply never tried — and the spaced form `hoare [ … ]`
would therefore have to make `hoare` a reserved keyword.  Gluing makes `hoare[` a token of
its own and leaves the bare word `hoare` available as an ordinary identifier (a keyword is
banned in every position, binders and `unfold`/attribute arguments included, and a constant
so named prints as `«hoare»`).  EasyCrypt spells its triples `hoare[ … : pre ==> post ]`, so
this is also the familiar form.

The underlying definition is `hoareStmt`, not `hoare`, so reserving the keyword would no
longer collide with anything today — the spaced form is available should we want it, at the
price of that project-wide reservation.
-/

namespace GaudisCrypt

open Lean in section

variable [ProgramSpec]

syntax ppGroup("hoare[ " term " ==> " term " ] " "{")
         (ppIndent(ppLine ppGroup("var " proc_binder,* ";")))*
         gaudi_stmt*
       ppDedent(ppDedent(ppLine)) "}" : term

macro_rules
  | `(hoare[ $pre:term ==> $post:term ] {
        $[var $locals:proc_binder,* ;]*
        $stmts:gaudi_stmt*
      }) => do
    -- multiple `var …;` lines are concatenated into a single local-variable list, and a
    -- binder declaring several names is flattened into one entry each
    let localBs := (← (locals.toList.flatMap (·.getElems.toList)).mapM
      ProgramSyntax.parseBinder).flatten.toArray
    ProgramSyntax.checkDistinct (localBs.map (·.1))
    -- one `letI` per local, binding it to its local slot, as in a `proc`
    let binds ← localBs.mapM fun (id, ty) => ProgramSyntax.varBinding id ty
    let body ← ProgramSyntax.wrapLetI binds (← `((GaudiProg[ $stmts* ] : Stmt)))
    -- a condition sees the local variables *and* the body's spine binders; `GaudiExpr[ ]`
    -- gives a `Getter Prop …`, and `hoareStmt` wants the underlying predicate
    let cond (p : Term) : MacroM Term := do
      ProgramSyntax.wrapLetI binds (← ProgramSyntax.wrapSpineBinders stmts
        (← `((GaudiExpr[ $p ] : Getter Prop ProgramState).get)))
    `(hoareStmt $(← cond pre) $body $(← cond post))

end

/-! ### Printing a statement triple

`hoareStmt A p B` prints as `hoare[ P ==> Q ] { … }` whenever the body prints as statements.
A condition of the shape the macro builds — a `GaudiExpr[ ]` getter under exactly the
`let`/`have` binders on the body's spine — prints as the `P` it was written as.  Any other
condition `c : ProgramState → Prop` (one a rewrite or `dsimp` produced, say) prints as
`c CurrentState.state`, β-reduced, which re-elaborates to `c` up to η.  If `c` mentions its
argument inside a nested `GaudiExpr[ ]`, where `CurrentState.state` would read the nested state,
it prints as `let σ := CurrentState.state; c σ` instead (`ProgramSyntax.getterViaState`, which
also prints the expression slots of statements that are not of the shape the macros build).

A condition without the spine binders is printed as it is, and the macro wraps it in them again.
That is sound when it mentions none of their names, and otherwise the delaborator steps aside.

The `var`s are recovered the way the `proc` delaborator recovers them (see "Program variables"
in `ProgramSyntax.lean`), over the body and both conditions together: a slot
`localVarLens "x" T` is one variable wherever it occurs in the three, so `§x` in a condition
and `x` in the body print under the same name and the same `var` line. -/

section Printing
open Lean PrettyPrinter Delaborator SubExpr ProgramSyntax

private partial def syntaxMentions (n : Name) : Syntax → Bool
  | .ident _ _ v _ => v.eraseMacroScopes == n
  | .node _ _ args => args.any (syntaxMentions n)
  | _ => false

/-- The `P` of a condition `c` (after the spine binders): `(GaudiExpr[ P ]).get` with no state
argument of its own, or failing that, `c CurrentState.state` (see
`ProgramSyntax.getterViaState`). -/
private def delabCondBody : DelabM Term :=
  (do guard ((← getExpr).isAppOfArity ``Getter.get 3)
      withNaryArg 2 delabGaudiExpr) <|>
  (do withExpr (← getterViaState (← getExpr)) delabGaudiExpr)

/-- A condition of a statement triple: the spine `let`s, then the condition proper.  A
condition without them is printed as it is, the macro wraps it in them again; that is only
faithful if it mentions none of their names. -/
private def delabStmtCond (spineNames : Array Name) : DelabM (Array Name × Term) :=
  (withPeeledLets spineNames.size (fun _ => true) #[] (anon := true) fun bs => do
      guard (bs == spineNames)
      return (bs, ← delabCondBody)) <|>
  (do let p ← delabCondBody
      guard <| !spineNames.any (syntaxMentions · p)
      return (spineNames, p))

/-- Print a statement triple as `hoare[ P ==> Q ] { … }`. -/
@[delab app.GaudisCrypt.hoareStmt]
private def delabHoareStmt : Delab := do
  guardSurfaceSyntax
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  let parts := #[e.getArg! 1, e.getArg! 2, e.getArg! 3]
  let vars := (← frameVars parts #[]).filter (·.printable)
  withVarLocals vars.toList parts fun es => do
    let stmts ← withExpr es[1]! (delabGaudiStmts #[])
    let spineNames := spineLetNames stmts
    let (preSpine, pre) ← withExpr es[0]! (delabStmtCond spineNames)
    let (postSpine, post) ← withExpr es[2]! (delabStmtCond spineNames)
    guard (preSpine == spineNames && postSpine == spineNames)
    let locals ← vars.mapM varBinder
    let varLines : Array (Syntax.TSepArray `proc_binder ",") :=
      if locals.isEmpty then #[] else #[locals]
    `(hoare[ $pre ==> $post ] {
        $[var $varLines:proc_binder,* ;]*
        $stmts:gaudi_stmt* })

end Printing

/-! ## Procedure triples -/

-- `M` at `term:max`: at any lower precedence the parameter list would be parsed as an
-- application of `M` to a tuple.  The statement form above starts with the same token, and the
-- two are told apart by what follows the first term (`:` here, `==>` there).
syntax ppGroup("hoare[ " term:max (" (" ident,* ")")? " : " term " ==> " term " ]") : term

open Lean Elab Term Meta in section

variable [ProgramSpec]

/-- The procedure a triple is about, elaborated (`M.procedure` for a procedure module `M`), the
same thing as syntax, and its signature.  `M` may be a procedure module — then the triple is
about `M.procedure` — or already a `Procedure`. -/
private def procedureOf (M : Term) : TermElabM (Lean.Expr × Term × Lean.Expr) := do
  let e ← withSynthesize <| elabTerm M none
  -- `M` itself did not elaborate; its own error has been reported, and a second one about the
  -- type we could not read off it would only be noise
  if e.hasSyntheticSorry then throwAbortTerm
  let mut ty ← instantiateMVars (← inferType e)
  for _ in [0:8] do
    if ty.isAppOfArity ``Module.Proc 2 then
      return (← mkAppM ``Module.Proc.procedure #[e],
        ← `(Module.Proc.procedure $(← exprToSyntax e)), ty.appArg!)
    if ty.isAppOfArity ``Procedure 2 then
      return (e, ← exprToSyntax e, ty.appArg!)
    -- `Procedure sig` is `ProcedureWithHoles .empty sig`, and that is the spelling a
    -- `module`-declared `X.f.procedure` carries
    if ty.isAppOfArity ``ProcedureWithHoles 3 then
      if (← whnf (ty.getArg! 1)).isConstOf ``HoleSigs.empty then
        return (e, ← exprToSyntax e, ty.appArg!)
      throwErrorAt M "a triple is about a hole-free procedure, but this one still has holes — \
        instantiate them first"
    if ty.isAppOf ``Module.Arr then
      throwErrorAt M "a triple is about a procedure, but this module still takes module \
        parameters — apply them first"
    let ty' ← whnfCore ty
    if ty' == ty then break
    ty := ty'
  throwErrorAt M m!"expected a procedure or a procedure module `Module.Proc …`, \
    but this has type{indentExpr ty}"

/-- The parameter names `@[gaudiProcParamNames]` records for the procedure `e`, if any.  A
procedure written as `X.f.procedure` carries them on that constant, so no special case is
needed for the `Module.Proc.procedure` wrapper. -/
private def recordedParamNames? {m} [Monad m] [MonadEnv m] (e : Lean.Expr) :
    m (Option (Array Name)) := do
  let some c := e.getAppFn.constName? | return none
  return gaudiProcParamNamesAttr.getParam? (← getEnv) c

/-- `Module.Proc.procedure M` ↦ the procedure module `M` it is the procedure of. -/
private def procModule? (p : Lean.Expr) : Option Lean.Expr :=
  if p.isAppOfArity ``Module.Proc.procedure 3 then some p.appArg! else none

/-- The strings of a list that reduces (`whnf`, element by element) to a literal list of string
literals. -/
private partial def stringList? (e : Lean.Expr) : MetaM (Option (List String)) := do
  match (← whnf e).getAppFnArgs with
  | (``List.nil, _) => return some []
  | (``List.cons, #[_, h, t]) =>
      let .lit (.strVal s) ← whnf h | return none
      return (s :: ·) <$> (← stringList? t)
  | _ => return none

/-- The parameter names of the procedure `p` that can be found without being written: the ones
`@[gaudiProcParamNames]` records (on `M` for `p = Module.Proc.procedure M`), else
`p.parameterNames` if it reduces to a literal list (a `proc` literal, say). -/
def knownParamNames? (p : Lean.Expr) : MetaM (Option (Array Name)) := do
  if let some ns ← recordedParamNames? ((procModule? p).getD p) then return some ns
  let reduced ← try stringList? (← mkAppM ``ProcedureWithHoles.parameterNames #[p])
    catch _ => pure none
  return reduced.map fun ns => ns.toArray.map Name.mkSimple

/-- The parameter names of a triple about the procedure `p`: the ones written at the triple if
there are any (they win, with a warning when the known names disagree), else the known ones
(`knownParamNames?`). -/
private def paramNamesOf (M : Term) (written? : Option (Array Ident)) (p : Lean.Expr) (n : Nat) :
    TermElabM (Array Name) := do
  let recorded? ← knownParamNames? p
  match written? with
  | some ids =>
      let written := ids.map (·.getId)
      unless written.size == n do
        throwError "this procedure takes {n} parameter(s), but {written.size} are named here"
      if let some recorded := recorded? then
        if recorded.size == n && recorded != written then
          logWarning m!"the declared parameter names of this procedure are \
            {recorded.toList}, not {written.toList}"
      return written
  | none =>
      match recorded? with
      | some recorded =>
          unless recorded.size == n do
            throwErrorAt M "this procedure takes {n} parameter(s), but the names known for \
              it are {recorded.toList}"
          return recorded
      | none =>
          if n == 0 then return #[]
          throwErrorAt M "no parameter names are known for this procedure; write them at \
            the triple, as in `hoare[ M (x, y) : … ]`"

elab_rules : term <= expectedType?
  | `(hoare[ $M:term $[( $written:ident,* )]? : $pre:term ==> $post:term ]) => do
    let (procExpr, procTerm, sig) ← procedureOf M
    -- the arity, and with it how many slots to emit; the *types* are never written out, they
    -- reach the binders as `Expr`s through `exprToSyntax`
    let params ← whnf (mkApp (mkConst ``ProcedureSignature.params) sig)
    let some tys ← ModuleDecl.listLit? params
      | throwErrorAt M m!"the parameter list of this procedure's signature is not a list \
          literal:{indentExpr params}"
    let n := tys.length
    let names ← paramNamesOf M (written.map (·.getElems)) procExpr n
    -- generated binders carry no source position, so an unmentioned parameter does not trip
    -- the unused-variable linter
    let argsId := mkIdent `args
    let stId := mkIdent `σ
    let resId := mkIdent `res
    let pack ← `((⟨$stId, VariableAssignment.init⟩ : ProgramState))
    -- `params`/`res` first, so a parameter that happens to be called `params` shadows it
    let bind (id : Ident) (val : Term) : TermElabM (Ident × Term) := do
      return (id, ← `((Getter.mk fun _ => $val : Getter _ ProgramState)))
    let mut preBs := #[← bind (mkIdent `params) argsId]
    for k in [0:n] do
      let slot ← liftMacroM (ProgramSyntax.mkChain (ProgramSyntax.navSteps k n))
      preBs := preBs.push (← bind (mkIdent names[k]!) (← `(($slot).get $argsId)))
    -- a plain `let`, not `letI`: the binder has to *survive* in the elaborated term, so that a
    -- condition mentioning a parameter reads back as `§x` rather than as the inlined slot getter
    let wrap (bs : Array (Ident × Term)) (body : Term) : TermElabM Term :=
      bs.foldrM (fun (id, val) acc => `(let $id := $val; $acc)) body
    let cond (bs : Array (Ident × Term)) (p : Term) : TermElabM Term := do
      wrap bs (← `((GaudiExpr[ $p ] : Getter Prop ProgramState).get $pack))
    let paramTy ← exprToSyntax (← whnf (mkApp (mkConst ``ProcedureSignature.ParamType) sig))
    let retTy ← exprToSyntax (← whnf (mkApp (mkConst ``ProcedureSignature.ret) sig))
    let preTerm ← `(fun ($argsId : $paramTy) ($stId : State) => $(← cond preBs pre))
    let postTerm ← `(fun ($resId : $retTy) ($stId : State) =>
      $(← cond #[← bind resId resId] post))
    elabTerm (← `(hoareProc (sig := $(← exprToSyntax sig)) $preTerm $procTerm $postTerm))
      expectedType?

end

/-! ### Printing a procedure triple

`hoareProc A p B` prints as `hoare[ M (x, y) : P ==> Q ]` when both conditions have the shape
the elaborator builds: `fun args σ => let … ; (GaudiExpr[ P ]).get ⟨σ, ()⟩`, with one
`Getter.mk` `let` per bound name.  The shape is checked on the raw term, which is also where
the two things a printed triple could otherwise get wrong are ruled out: that the condition is
read at *this* triple's `σ` and not at some other state in scope, and that it goes through the
`let`-bound getters rather than mentioning `args`/`σ` itself (neither has a surface spelling).

The parameter names are always printed, whether they were written at the triple or taken from
the callee's `@[gaudiProcParamNames]` — printing them is faithful either way, and does not
depend on the attribute still being there. -/

section Printing
open Lean PrettyPrinter Delaborator SubExpr

private partial def packedCondGo (e : Lean.Expr) (d : Nat) : Option Nat :=
  match e with
  | .letE _ _ v b _ => if v.isAppOf ``Getter.mk then (· + 1) <$> packedCondGo b (d + 1) else none
  | _ =>
    if e.isAppOfArity ``Getter.get 4 then
      -- inside `d` `let`s and the two lambdas, `σ` is `bvar d` and `args` is `bvar (d + 1)`
      let self := e.getArg! 2
      let pack := e.getArg! 3
      if pack.isAppOfArity ``ProgramState.mk 3 && pack.getArg! 1 == Lean.Expr.bvar d
          && (pack.getArg! 2).isConstOf ``VariableAssignment.init
          && !self.hasLooseBVar d && !self.hasLooseBVar (d + 1) then some 0 else none
    else none

/-- The number of `let`s in a condition of the shape the procedure-triple elaborator builds,
or `none` if it has some other shape. -/
private def packedCondLets? : Lean.Expr → Option Nat
  | .lam _ _ (.lam _ _ b _) _ => packedCondGo b 0
  | _ => none

/-- The bound names and the condition term of one side of a procedure triple. -/
private def delabProcCond (n : Nat) : DelabM (Array Name × Term) :=
  withBindingBody `args <| withBindingBody `σ <|
    withPeeledLets n (·.isAppOf ``Getter.mk) #[] fun names => do
      return (names, ← withNaryArg 2 delabGaudiExpr)

/-- Print a procedure triple as `hoare[ M (x, y) : P ==> Q ]`. -/
@[delab app.GaudisCrypt.hoareProc]
private def delabHoareProc : Delab := do
  guardSurfaceSyntax
  guard ((← getExpr).getAppNumArgs == 5)
  let some nPre := packedCondLets? ((← getExpr).getArg! 2) | failure
  let some nPost := packedCondLets? ((← getExpr).getArg! 4) | failure
  guard (nPre ≥ 1 && nPost == 1)
  let (preNames, pre) ← withNaryArg 2 (delabProcCond nPre)
  let (postNames, post) ← withNaryArg 4 (delabProcCond nPost)
  -- the elaborator binds `params` ahead of the parameters, and `res` in the postcondition
  guard (preNames[0]! == `params && postNames == #[`res])
  let ids := (preNames.extract 1 preNames.size).map mkIdent
  -- a procedure module prints as the module itself; the notation re-inserts `.procedure`
  let callee ← withNaryArg 3 do
    if (procModule? (← getExpr)).isSome then withNaryArg 2 delab else delab
  if ids.isEmpty then
    `(hoare[ $callee:term : $pre ==> $post ])
  else
    `(hoare[ $callee:term ( $ids,* ) : $pre ==> $post ])

end Printing

/-! ## From a procedure triple to a statement triple

`hoareProcToStmt` is `hoareProc_as_hoareStmt` as a conversion — in the shape of an
Isabelle `conv` (`cterm -> thm`), `Expr → MetaM Simp.Result`: the term it rewrites to and the
proof of the equation.  The two lenses the lemma quantifies over are chosen here: one local
variable per parameter of the procedure, under the parameter's name, and one for the result, so
that the statement prints as

    hoare[ P ==> Q ] { var res : R, x : X, y : Y; res <- call p (§x, §y); }

The signature is read off the term, so the `Nonempty` instances the slots need are found at the
concrete types. -/

section Conv
open Lean Meta Elab Tactic

/-- The parameter names of the procedure `p` with `n` parameters: `knownParamNames?`, else
`arg1`, …, `argn`. -/
private def procParamNames (p : Lean.Expr) (n : Nat) : MetaM (Array String) := do
  if let some ns ← knownParamNames? p then
    if ns.size == n then return ns.map (·.toString (escape := false))
  return (Array.range n).map fun i => s!"arg{i + 1}"

/-- The local variable `n : T`: its slot `varLens ⟨n, T, …⟩` in the locals, and the same slot as
`localVarLens n T` in the program state.  The key is the literal `variable_name_key` gives. -/
private def mkVarSlots (inst : Lean.Expr) (n : String) (T : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let ne ← synthInstance (← mkAppM ``Nonempty #[T])
  let key := mkNatLit (VariableName.encode n)
  let keyCorrect ← mkExpectedTypeHint (← mkEqRefl key)
    (← mkEq key (mkApp (mkConst ``VariableName.encode) (mkStrLit n)))
  let name := mkAppN (mkConst ``VariableName.mk) #[mkStrLit n, T, ne, key, keyCorrect]
  return (mkApp (mkConst ``varLens) name,
    mkAppN (mkConst ``localVarLens) #[inst, mkStrLit n, T, ne, key, keyCorrect])

/-- The tuple lens of the slots `ls` over the carrier `m` (`typeListToTuple`'s shape): `Lens.punit`
for none, the slot itself for one, `Lens.pair` on the right-nested rest otherwise.  Only the
lemma's side needs it; the statement reads the slots one by one. -/
private def mkTupleLens (m : Lean.Expr) : List Lean.Expr → MetaM Lean.Expr
  | [] => mkAppOptM ``Lens.punit #[some m, some (mkConst ``Unit), none]
  | [l] => pure l
  -- `mkAppOptM`, not `mkAppM`: the trailing `Lens.Disjoint` instance has to be synthesized too
  | l :: ls => do
      mkAppOptM ``Lens.pair #[none, none, none, some l, some (← mkTupleLens m ls), none]

/-- `L.get s`, read through `getter`. -/
private def mkLensGet (L s : Lean.Expr) : MetaM Lean.Expr := do
  mkAppM ``Getter.get #[← mkAppM ``Lens.toGetter #[L], s]

/-- The tuple `(x₁.get s, …, xₙ.get s)` of reads of the slots `ls` at `s` (`typeListToTuple`'s
shape, `()` for none). -/
private def mkTupleRead (s : Lean.Expr) : List Lean.Expr → MetaM Lean.Expr
  | [] => pure (mkConst ``Unit.unit)
  | [l] => mkLensGet l s
  | l :: ls => do mkAppM ``Prod.mk #[← mkLensGet l s, ← mkTupleRead s ls]

/-- Reduce, up to defeq, the projections a procedure triple's precondition takes of the argument
tuple, once that tuple is a literal tuple: `Lens.id.get t` ↦ `t`, `L.ofst.get t` ↦ `L.get t.1`,
`L.osnd.get t` ↦ `L.get t.2`, `(x, y).1` ↦ `x`, `(x, y).2` ↦ `y`. -/
private def reduceArgProjections (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let r? ← do
      if let some (l, t) := ProgramSyntax.lensGet? e then
        if l.isAppOf ``Lens.id then pure (some t)
        else if l.isAppOfArity ``Lens.ofst 4 then
          some <$> mkLensGet l.appArg! (← mkAppM ``Prod.fst #[t])
        else if l.isAppOfArity ``Lens.osnd 4 then
          some <$> mkLensGet l.appArg! (← mkAppM ``Prod.snd #[t])
        else pure none
      else if e.isAppOfArity ``Prod.fst 3 && e.appArg!.isAppOfArity ``Prod.mk 4 then
        pure (some (e.appArg!.getArg! 2))
      else if e.isAppOfArity ``Prod.snd 3 && e.appArg!.isAppOfArity ``Prod.mk 4 then
        pure (some (e.appArg!.getArg! 3))
      else pure none
    let some r := r? | return .continue
    if ← isDefEq r e then return .visit r else return .continue)

/-- `hoareProc A p B` ↦ the `hoareStmt` about `res <- call p (x₁, …, xₙ);`, with one local
variable per parameter of `p` (see the section docstring), and the proof of the equation.

The conditions are `A`/`B` applied to the reads of the slots, with their `let`s substituted (the
procedure-triple notation binds the parameter names, which would shadow the variables) and the
parameter projections reduced, so that the parameter `x` reads as the variable `§x`; then put in
the shape `GaudiExpr[ P ].get` by `ProgramSyntax.getterViaState`. -/
def hoareProcToStmt (e : Lean.Expr) : MetaM Simp.Result := do
  let e ← instantiateMVars e
  unless e.isAppOfArity ``hoareProc 5 do
    throwError "expected a procedure triple `hoareProc A p B`, got{indentExpr e}"
  let #[inst, sig, A, p, B] := e.getAppArgs | unreachable!
  let some tys ← ModuleDecl.listLit? (← whnf (mkApp (mkConst ``ProcedureSignature.params) sig))
    | throwError "the parameter list of{indentExpr sig}\nis not a list literal"
  let ret ← whnf (mkApp (mkConst ``ProcedureSignature.ret) sig)
  let names ← procParamNames p tys.length
  -- the result variable must not be one of the parameters
  let resName := Id.run do
    let mut r := "res"
    while names.contains r do r := r ++ "'"
    return r
  let (resVA, resPS) ← mkVarSlots inst resName ret
  let slots ← (names.toList.zip tys).mapM fun (n, T) => mkVarSlots inst n T
  let va := mkConst ``VariableAssignment
  let ps := mkApp (mkConst ``ProgramState) inst
  let argsVA ← mkTupleLens va (slots.map (·.1))
  let argSlots := slots.map (·.2)
  -- the statement, over the slots in the program state
  -- each condition in the shape the statement-triple notation builds, `GaudiExpr[ P ].get`, with
  -- its reads brought into printable form by `getterViaState` (the same rewrites the printer
  -- applies to a condition of any other shape)
  let cond (C : Lean.Expr) (val : Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr := do
    let f ← withLocalDeclD `σ ps fun σ => do
      let c := C.beta #[← val σ, ← mkAppM ``ProgramState.globals #[σ]]
      mkLambdaFVars #[σ] (← reduceArgProjections (← zetaReduce c))
    mkAppM ``Getter.get #[← ProgramSyntax.getterViaState f]
  let pre ← cond A (mkTupleRead · argSlots)
  let post ← cond B (mkLensGet resPS ·)
  -- the arguments as the call reads them: the slot itself for one, the tuple of reads otherwise
  let argsGetter ← match argSlots with
    | [l] => mkAppM ``Lens.toGetter #[l]
    | _ => withLocalDeclD `st ps fun st => do
        mkAppM ``Getter.mk #[← mkLambdaFVars #[st] (← mkTupleRead st argSlots)]
  -- `sig` explicitly: `ProcedureSignature.ret ?sig =?= R` does not determine it
  let body ← mkAppOptM ``Stmt.call #[some inst, some sig, some (← mkAppM ``Lens.toSetter #[resPS]),
    some p, some argsGetter]
  let rhs ← mkAppM ``hoareStmt #[pre, body, post]
  -- the proof: the lemma at the same slots in the locals, which is the statement up to unfolding
  -- `Lens.intoLocal`, `Lens.pair` (against the tuple of reads) and the `let`s and projections
  let pf ← mkAppOptM ``hoareProc_as_hoareStmt
    #[some inst, some sig, some resVA, some argsVA, some A, some p, some B]
  let goal ← mkEq e rhs
  unless ← isDefEq (← mkEq e (← instantiateMVars (← inferType pf)).iff?.get!.2) goal do
    throwError "hoareProcToStmt: the statement built is not the lemma's"
  return { expr := rhs, proof? := some (← mkExpectedTypeHint (← mkPropExt pf) goal) }

/-- Rewrite a goal `hoareProc A p B` to the `hoareStmt` about `res <- call p (x₁, …, xₙ);`, one
local variable per parameter — the conversion `hoareProcToStmt` applied to the goal. -/
elab "hoare_proc_to_stmt" : tactic => liftMetaTactic1 fun g => do
  let r ← hoareProcToStmt (← g.getType)
  applySimpResultToTarget g (← g.getType) r

end Conv

end GaudisCrypt
