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
**repeated around `P` and `Q`**: the `var` lenses (as `let`s, exactly as in the body) and
the binders on the *spine* of the statement sequence (`ProgramSyntax.wrapSpineBinders`,
which is what `proc` does for its return value).  So a precondition or postcondition may
mention the local program variables and the body's `let`s.

`P` and `Q` are ordinary `GaudiExpr[ ]` expressions of type `Prop`, so program variables
are read with the `$`/`§` sigil.  The local state is `ProcedureScope [] locals` — no
parameters; a triple about a procedure is the second form below.

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
explicit `()` asserts that the procedure takes none.  A procedure with no recorded names (a
`proc` literal, say) has to have them written.

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
        let params : Getter _ (ProcedureState Unit) := Getter.mk fun _ => args
        let x : Getter _ (ProcedureState Unit) := Getter.mk fun _ => (Lens.id.ofst).get args
        let m : Getter _ (ProcedureState Unit) := Getter.mk fun _ => (Lens.id.osnd).get args
        (GaudiExpr[ P ] : Getter Prop (ProcedureState Unit)).get ⟨σ, ()⟩)
      (Module.Proc.procedure M)
      (fun res σ =>
        let res : Getter _ (ProcedureState Unit) := Getter.mk fun _ => res
        (GaudiExpr[ Q ] : Getter Prop (ProcedureState Unit)).get ⟨σ, ()⟩)

Points worth knowing:

* The ambient state is installed at the **closed** carrier `ProcedureState Unit`.
  `GaudiExpr[ ]` always reads from a `ProcedureState S` (that is `CurrentState`'s field type),
  and `Unit` locals is the smallest such state: globals resolve through the existing
  `Evaluatable S (Lens T State) T` instance, and there are no locals, which is right for a
  pre/postcondition.  So no `ProcedureScope` appears, no argument tuple has to be packed into
  one, and the result never has to masquerade as a parameter.
* A parameter's slot is the **same lens chain the procedure body uses**: `proc` binds its
  `k`-th parameter to `Lens.intoParams $slot` for
  `slot = ProgramSyntax.mkChain (ProgramSyntax.navSteps k n)`, and the triple emits that same
  `$slot`, applied rather than composed.  The two encodings of "parameter `k` of `n`"
  therefore coincide, which is what lets a tactic relate a triple's parameter getter to the
  body's parameter lens.
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
    let nl := localBs.size
    let localSigmas ← localBs.mapM fun (_, ty) => `(⟨$ty, inferInstance⟩)
    let localsTerm ← `([$localSigmas,*])
    -- the local state: no parameters, just the declared locals
    let L ← `(ProcedureScope [] $localsTerm)
    -- one `let` per local, binding it to its lens into `ProcedureState L`
    let mut binds : Array (Ident × Term × Term) := #[]
    for j in [0:nl] do
      let (id, ty) := localBs[j]!
      let slot ← ProgramSyntax.mkChain (ProgramSyntax.navSteps j nl)
      binds := binds.push (id, ← `(Lens $ty (ProcedureState $L)), ← `(Lens.intoLocalVars $slot))
    let wrap (bs : Array (Ident × Term × Term)) (inner : Term) : MacroM Term :=
      bs.foldrM (fun (id, ty, val) acc => `(let $id : $ty := $val; $acc)) inner
    let body ← wrap binds (← `((GaudiProg[ $stmts* ] : Stmt $L)))
    -- a condition sees the local lenses *and* the body's spine binders; `GaudiExpr[ ]`
    -- gives a `Getter Prop …`, and `hoareStmt` wants the underlying predicate
    let cond (p : Term) : MacroM Term := do
      wrap binds (← ProgramSyntax.wrapSpineBinders stmts
        (← `((GaudiExpr[ $p ] : Getter Prop (ProcedureState $L)).get)))
    `(hoareStmt $(← cond pre) $body $(← cond post))

end

/-! ### Printing a statement triple

`hoareStmt A p B` prints as `hoare[ P ==> Q ] { … }` when all three parts agree on the
`let`-bound prefix the macro repeats around them: one `Lens.intoLocalVars` binder per `var`,
and then — in the conditions only — the `let`/`have` binders on the body's spine.  If they
disagree, or either condition is not a `GaudiExpr[ ]` getter, the delaborator steps aside and
the `hoareStmt` application prints as it is. -/

section Printing
open Lean PrettyPrinter Delaborator SubExpr

/-- A condition of a statement triple: the local-variable and spine `let`s, then
`(GaudiExpr[ P ]).get` with no state argument of its own. -/
private def delabStmtCond (nl : Nat) (spineNames : Array Name) :
    DelabM (Array Name × Array Name × Term) :=
  withPeeledLets nl (·.isAppOf ``Lens.intoLocalVars) #[] fun ls =>
    withPeeledLets spineNames.size (fun _ => true) #[] (anon := true) fun bs => do
      guard ((← getExpr).isAppOfArity ``Getter.get 3)
      return (ls, bs, ← withNaryArg 2 delabGaudiExpr)

/-- Print a statement triple as `hoare[ P ==> Q ] { … }`. -/
@[delab app.GaudisCrypt.hoareStmt]
private def delabHoareStmt : Delab := do
  guardSurfaceSyntax
  guard ((← getExpr).getAppNumArgs == 5)
  -- the local state has to be the one the macro builds: no parameters, only declared locals
  let localTys ← withNaryArg 1 do
    guard ((← getExpr).isAppOfArity ``ProcedureScope 2)
    guard ((← getExpr).getArg! 0 |>.isAppOfArity ``List.nil 1)
    withNaryArg 1 delabLocalTypes
  let nl := localTys.size
  let (localNames, stmts) ← withNaryArg 3 <|
    withPeeledLets nl (·.isAppOf ``Lens.intoLocalVars) #[] fun ls => do
      return (ls, ← delabGaudiStmts #[])
  let spineNames := spineLetNames stmts
  let (preLocals, preSpine, pre) ← withNaryArg 2 (delabStmtCond nl spineNames)
  let (postLocals, postSpine, post) ← withNaryArg 4 (delabStmtCond nl spineNames)
  guard (preLocals == localNames && postLocals == localNames)
  guard (preSpine == spineNames && postSpine == spineNames)
  let locals ← (localNames.zip localTys).mapM fun (n, t) =>
    `(proc_binder| $(mkIdent n):ident : $t)
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

/-- The procedure a triple is about: its elaborated form (which carries the parameter names,
if any are recorded), the same thing as syntax, and its signature.  `M` may be a procedure
module — then the triple is about `M.procedure` — or already a `Procedure`. -/
private def procedureOf (M : Term) : TermElabM (Lean.Expr × Term × Lean.Expr) := do
  let e ← withSynthesize <| elabTerm M none
  -- `M` itself did not elaborate; its own error has been reported, and a second one about the
  -- type we could not read off it would only be noise
  if e.hasSyntheticSorry then throwAbortTerm
  let mut ty ← instantiateMVars (← inferType e)
  for _ in [0:8] do
    if ty.isAppOfArity ``Module.Proc 2 then
      return (e, ← `(Module.Proc.procedure $(← exprToSyntax e)), ty.appArg!)
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
private def recordedParamNames? (e : Lean.Expr) : TermElabM (Option (Array Name)) := do
  let some c := e.getAppFn.constName? | return none
  return gaudiProcParamNamesAttr.getParam? (← getEnv) c

/-- The parameter names of a triple: the ones written at the triple if there are any (they win,
with a warning when the recorded names disagree), else the recorded ones. -/
private def paramNamesOf (M : Term) (written? : Option (Array Ident)) (e : Lean.Expr) (n : Nat) :
    TermElabM (Array Name) := do
  let recorded? ← recordedParamNames? e
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
            throwErrorAt M "this procedure takes {n} parameter(s), but the names recorded for \
              it are {recorded.toList}"
          return recorded
      | none =>
          if n == 0 then return #[]
          throwErrorAt M "no parameter names are recorded for this procedure; write them at \
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
    let pack ← `((⟨$stId, ()⟩ : ProcedureState Unit))
    -- `params`/`res` first, so a parameter that happens to be called `params` shadows it
    let bind (id : Ident) (val : Term) : TermElabM (Ident × Term) := do
      return (id, ← `((Getter.mk fun _ => $val : Getter _ (ProcedureState Unit))))
    let mut preBs := #[← bind (mkIdent `params) argsId]
    for k in [0:n] do
      let slot ← liftMacroM (ProgramSyntax.mkChain (ProgramSyntax.navSteps k n))
      preBs := preBs.push (← bind (mkIdent names[k]!) (← `(($slot).get $argsId)))
    -- a plain `let`, not `letI`: the binder has to *survive* in the elaborated term, so that a
    -- condition mentioning a parameter reads back as `§x` rather than as the inlined slot getter
    let wrap (bs : Array (Ident × Term)) (body : Term) : TermElabM Term :=
      bs.foldrM (fun (id, val) acc => `(let $id := $val; $acc)) body
    let cond (bs : Array (Ident × Term)) (p : Term) : TermElabM Term := do
      wrap bs (← `((GaudiExpr[ $p ] : Getter Prop (ProcedureState Unit)).get $pack))
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
      if pack.isAppOfArity ``ProcedureState.mk 4 && pack.getArg! 2 == Lean.Expr.bvar d
          && !self.hasLooseBVar d && !self.hasLooseBVar (d + 1) then some 0 else none
    else none

/-- The number of `let`s in a condition of the shape the procedure-triple elaborator builds,
or `none` if it has some other shape.  (The `locals` component of the repacked state is not
checked: it is a `Unit`, so it carries nothing.) -/
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
    if (← getExpr).isAppOfArity ``Module.Proc.procedure 3 then withNaryArg 2 delab else delab
  if ids.isEmpty then
    `(hoare[ $callee:term : $pre ==> $post ])
  else
    `(hoare[ $callee:term ( $ids,* ) : $pre ==> $post ])

end Printing

end GaudisCrypt
