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
        letI params : Getter _ (ProcedureState Unit) := Getter.mk fun _ => args
        letI x : Getter _ (ProcedureState Unit) := Getter.mk fun _ => (Lens.id.ofst).get args
        letI m : Getter _ (ProcedureState Unit) := Getter.mk fun _ => (Lens.id.osnd).get args
        (GaudiExpr[ P ] : Getter Prop (ProcedureState Unit)).get ⟨σ, ()⟩)
      (Module.Proc.procedure M)
      (fun res σ =>
        letI res : Getter _ (ProcedureState Unit) := Getter.mk fun _ => res
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
    let wrap (bs : Array (Ident × Term)) (body : Term) : TermElabM Term :=
      bs.foldrM (fun (id, val) acc => `(letI $id := $val; $acc)) body
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

end GaudisCrypt
