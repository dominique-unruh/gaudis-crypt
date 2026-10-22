import GaudisCrypt.Logic.PHoare
import GaudisCrypt.Syntax.HoareSyntax

/-!
# Concrete syntax for probabilistic Hoare judgments

The two forms of `hoare[ … ]` (`Syntax/HoareSyntax.lean`), with a relation and a bound after the
bracket:

    phoare[ P ==> Q ] = r { … }             -- phoareStmt, about a statement
    phoare[ M (x, y) : P ==> Q ] <= r       -- phoareProc, about a procedure

The relation is `=`, `<=`/`≤` or `>=`/`≥`.  The bound `r` is parsed at `term:max`, so anything
but an atom needs parentheses (`= (1/2)`), as in EasyCrypt; it is an `ENNReal` expression read
like the precondition (it may mention the parameters and the globals, or for the statement
form the program state).

The postcondition `Q` is **either an event or an expectation**: a `Prop` is the event, and the
judgment is about its indicator `indicatorE Q` (EC's `phoare`); an `ENNReal` expression is the
expectation itself.  The elaborator tries the event first.  An indicator `indicatorE Q` prints
as `Q`, so both round-trip.
-/

namespace GaudisCrypt

open Lean

declare_syntax_cat phoare_rel
syntax " = " : phoare_rel
syntax " <= " : phoare_rel
syntax " >= " : phoare_rel
syntax " ≤ " : phoare_rel
syntax " ≥ " : phoare_rel

/-- The relation a `phoare_rel` token stands for, at `ENNReal`. -/
def phoareRelTerm : TSyntax `phoare_rel → MacroM Term
  | `(phoare_rel| =) => `((@Eq ENNReal))
  | `(phoare_rel| <=) | `(phoare_rel| ≤) => `((@LE.le ENNReal _))
  | `(phoare_rel| >=) | `(phoare_rel| ≥) => `((@GE.ge ENNReal _))
  | _ => Macro.throwUnsupported

/-! ## Statement judgments -/

syntax ppGroup("phoare[ " term " ==> " term " ] " phoare_rel term:max " {")
         (ppIndent(ppLine ppGroup("var " proc_binder,* ";")))*
         gaudi_stmt*
       ppDedent(ppDedent(ppLine)) "}" : term

open Elab Term Meta in
/-- Elaborate `mk post`, the judgment with the postcondition read as an event (`indicatorE`);
    if that fails, with the postcondition read as an expectation. -/
def elabEventOrExpectation (mk : Term → TermElabM Term) (post : Term)
    (expectedType? : Option Lean.Expr) : TermElabM Lean.Expr := do
  let s ← saveState
  let hadErrors ← MonadLog.hasErrors
  -- a failure can be thrown, or only logged (an instance problem at default-instance time, say
  -- `1 / 2 : Prop`): both count
  let event? ← try
      withoutErrToSorry do
        let e ← elabTerm (← mk (← `(indicatorE ($post)))) expectedType?
        synthesizeSyntheticMVarsNoPostponing
        if !hadErrors && (← MonadLog.hasErrors) then pure none else pure (some e)
    catch _ => pure none
  if let some e := event? then return e
  s.restore
  elabTerm (← mk post) expectedType?

open Elab Term Meta in
elab_rules : term <= expectedType?
  | `(phoare[ $pre:term ==> $post:term ] $rel:phoare_rel $bound:term {
        $[var $locals:proc_binder,* ;]*
        $stmts:gaudi_stmt*
      }) => do
    let localBs := (← (locals.toList.flatMap (·.getElems.toList)).mapM fun b =>
      liftMacroM (ProgramSyntax.parseBinder b)).flatten.toArray
    liftMacroM <| ProgramSyntax.checkDistinct (localBs.map (·.1))
    let binds ← localBs.mapM fun (id, ty) => liftMacroM (ProgramSyntax.varBinding id ty)
    let body ← liftMacroM <| ProgramSyntax.wrapLetI binds (← `((GaudiProg[ $stmts* ] : Stmt)))
    -- as for `hoare[ ]`: a condition sees the local variables and the body's spine binders
    let cond (p : Term) (ty : Term) : TermElabM Term := liftMacroM do
      ProgramSyntax.wrapLetI binds (← ProgramSyntax.wrapSpineBinders stmts
        (← `((GaudiExpr[ $p ] : Getter $ty ProgramState).get)))
    let ρ ← liftMacroM (phoareRelTerm rel)
    let preT ← cond pre (← `(Prop))
    let boundT ← cond bound (← `(ENNReal))
    elabEventOrExpectation (fun (q : Term) => show TermElabM Term from do
        `(phoareStmt $preT $body $(← cond q (← `(ENNReal))) $ρ $boundT)) post expectedType?

/-! ## Procedure judgments -/

syntax ppGroup("phoare[ " term:max (" (" ident,* ")")? " : " term " ==> " term " ] "
  phoare_rel term:max) : term

open Elab Term Meta in
elab_rules : term <= expectedType?
  | `(phoare[ $M:term $[( $written:ident,* )]? : $pre:term ==> $post:term ] $rel:phoare_rel
        $bound:term) => do
    let (procExpr, procTerm, sig) ← procedureOf M
    let params ← whnf (mkApp (mkConst ``ProcedureSignature.params) sig)
    let some tys ← ModuleDecl.listLit? params
      | throwErrorAt M m!"the parameter list of this procedure's signature is not a list \
          literal:{indentExpr params}"
    let n := tys.length
    let names ← paramNamesOf M (written.map (·.getElems)) procExpr n
    -- the binders and their shape are those of `hoare[ M : … ]` (see `HoareSyntax.lean`)
    let argsId := mkIdent `args
    let stId := mkIdent `σ
    let resId := mkIdent `res
    let pack ← `((⟨$stId, VariableAssignment.init⟩ : ProgramState))
    let bind (id : Ident) (val : Term) : TermElabM (Ident × Term) := do
      return (id, ← `((Getter.mk fun _ => $val : Getter _ ProgramState)))
    let mut preBs := #[← bind (mkIdent `params) argsId]
    for k in [0:n] do
      let slot ← liftMacroM (ProgramSyntax.mkChain (ProgramSyntax.navSteps k n))
      preBs := preBs.push (← bind (mkIdent names[k]!) (← `(($slot).get $argsId)))
    let wrap (bs : Array (Ident × Term)) (body : Term) : TermElabM Term :=
      bs.foldrM (fun (id, val) acc => `(let $id := $val; $acc)) body
    let cond (bs : Array (Ident × Term)) (p : Term) (ty : Term) : TermElabM Term := do
      wrap bs (← `((GaudiExpr[ $p ] : Getter $ty ProgramState).get $pack))
    let paramTy ← exprToSyntax (← whnf (mkApp (mkConst ``ProcedureSignature.ParamType) sig))
    let retTy ← exprToSyntax (← whnf (mkApp (mkConst ``ProcedureSignature.ret) sig))
    let preTerm ← `(fun ($argsId : $paramTy) ($stId : VariableAssignment) =>
      $(← cond preBs pre (← `(Prop))))
    let boundTerm ← `(fun ($argsId : $paramTy) ($stId : VariableAssignment) =>
      $(← cond preBs bound (← `(ENNReal))))
    let resBs := #[← bind resId resId]
    let ρ ← liftMacroM (phoareRelTerm rel)
    let sigT ← exprToSyntax sig
    elabEventOrExpectation (fun (q : Term) => show TermElabM Term from do
        let postTerm ← `(fun ($resId : $retTy) ($stId : VariableAssignment) =>
          $(← cond resBs q (← `(ENNReal))))
        `(phoareProc (sig := $sigT) $preTerm $procTerm $postTerm $ρ $boundTerm))
      post expectedType?

/-! ## Printing -/

section Printing
open PrettyPrinter Delaborator SubExpr ProgramSyntax

/-- The relation token for `ρ`, if it is one of the three. -/
def phoareRelSyntax? (ρ : Lean.Expr) : DelabM (Option (TSyntax `phoare_rel)) := do
  if ρ.isAppOfArity ``Eq 1 then return some (← `(phoare_rel| =))
  if ρ.isAppOfArity ``LE.le 2 then return some (← `(phoare_rel| ≤))
  if ρ.isAppOfArity ``GE.ge 2 then return some (← `(phoare_rel| ≥))
  return none

/-- A postcondition `indicatorE Q` prints as the event `Q`. -/
def stripIndicator (t : Term) : DelabM Term := do
  let `(indicatorE $q) := t | return t
  if let `(($q')) := q then return q'
  return q

/-- The bound, parenthesized unless it is an atom (it is parsed at `term:max`). -/
def parenBound (t : Term) : DelabM Term := do
  if t.raw.isIdent || t.raw.isNatLit?.isSome || t.raw.isOfKind numLitKind ||
      t.raw.isOfKind ``Lean.Parser.Term.paren then return t
  `(($t))

/-- Print a statement judgment as `phoare[ P ==> Q ] ⋈ r { … }`. -/
@[delab app.GaudisCrypt.phoareStmt]
private def delabPHoareStmt : Delab := do
  guardSurfaceSyntax
  let e ← getExpr
  guard (e.getAppNumArgs == 5)
  let some rel ← phoareRelSyntax? (e.getArg! 3) | failure
  let parts := #[e.getArg! 0, e.getArg! 1, e.getArg! 2, e.getArg! 4]
  let vars := (← frameVars parts #[]).filter (·.printable)
  withVarLocals vars.toList parts fun es => do
    let stmts ← withExpr es[1]! (delabGaudiStmts #[])
    let spineNames := spineLetNames stmts
    let (preSpine, pre) ← withExpr es[0]! (delabStmtCond spineNames)
    let (postSpine, post) ← withExpr es[2]! (delabStmtCond spineNames)
    let (boundSpine, bound) ← withExpr es[3]! (delabStmtCond spineNames)
    guard (preSpine == spineNames && postSpine == spineNames && boundSpine == spineNames)
    let post ← stripIndicator post
    let bound ← parenBound bound
    let locals ← vars.mapM varBinder
    let varLines : Array (Syntax.TSepArray `proc_binder ",") :=
      if locals.isEmpty then #[] else #[locals]
    `(phoare[ $pre ==> $post ] $rel:phoare_rel $bound {
        $[var $varLines:proc_binder,* ;]*
        $stmts:gaudi_stmt* })

/-- Print a procedure judgment as `phoare[ M (x, y) : P ==> Q ] ⋈ r`. -/
@[delab app.GaudisCrypt.phoareProc]
private def delabPHoareProc : Delab := do
  guardSurfaceSyntax
  let e ← getExpr
  guard (e.getAppNumArgs == 6)
  let some rel ← phoareRelSyntax? (e.getArg! 4) | failure
  let some nPre := packedCondLets? (e.getArg! 1) | failure
  let some nPost := packedCondLets? (e.getArg! 3) | failure
  let some nBound := packedCondLets? (e.getArg! 5) | failure
  guard (nPre ≥ 1 && nPost == 1 && nBound == nPre)
  let (preNames, pre) ← withNaryArg 1 (delabProcCond nPre)
  let (postNames, post) ← withNaryArg 3 (delabProcCond nPost)
  let (boundNames, bound) ← withNaryArg 5 (delabProcCond nBound)
  guard (preNames[0]! == `params && postNames == #[`res] && boundNames == preNames)
  let post ← stripIndicator post
  let bound ← parenBound bound
  let ids := (preNames.extract 1 preNames.size).map mkIdent
  let callee ← withNaryArg 2 do
    if (procModule? (← getExpr)).isSome then withNaryArg 1 delab else delab
  if ids.isEmpty then
    `(phoare[ $callee:term : $pre ==> $post ] $rel:phoare_rel $bound)
  else
    `(phoare[ $callee:term ( $ids,* ) : $pre ==> $post ] $rel:phoare_rel $bound)

end Printing

/-! ## From a procedure judgment to a statement judgment

`phoareProc_as_phoareStmt` as a conversion, exactly as `hoareProcToStmt` does it for Hoare
triples: one local variable per parameter, one for the result, so that the goal prints as

    phoare[ P ==> Q ] ⋈ r { var res : R, x : X; res <- call p (§x); }
-/

section Conv
open Elab Tactic Meta

/-- `phoareProc A p G ρ r` ↦ the `phoareStmt` about `res <- call p (x₁, …, xₙ);`, and the proof
of the equation (see `hoareProcToStmt`). -/
def phoareProcToStmt (e : Lean.Expr) : MetaM Simp.Result := do
  let e ← instantiateMVars e
  unless e.isAppOfArity ``phoareProc 6 do
    throwError "expected a procedure judgment `phoareProc A p G ρ r`, got{indentExpr e}"
  let #[sig, A, p, G, ρ, r] := e.getAppArgs | unreachable!
  let some tys ← ModuleDecl.listLit? (← whnf (mkApp (mkConst ``ProcedureSignature.params) sig))
    | throwError "the parameter list of{indentExpr sig}\nis not a list literal"
  let ret ← whnf (mkApp (mkConst ``ProcedureSignature.ret) sig)
  let names ← procParamNames p tys.length
  let resName := Id.run do
    let mut r := "res"
    while names.contains r do r := r ++ "'"
    return r
  let (resVA, resPS) ← mkVarSlots resName ret
  let slots ← (names.toList.zip tys).mapM fun (n, T) => mkVarSlots n T
  let va := mkConst ``VariableAssignment
  let ps := mkConst ``ProgramState
  let argsVA ← mkTupleLens va (slots.map (·.1))
  let argSlots := slots.map (·.2)
  let cond (C : Lean.Expr) (val : Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr := do
    let f ← withLocalDeclD `σ ps fun σ => do
      let c := C.beta #[← val σ, ← mkAppM ``ProgramState.globals #[σ]]
      mkLambdaFVars #[σ] (← reduceArgProjections (← zetaReduce c))
    mkAppM ``Getter.get #[← ProgramSyntax.getterViaState f]
  let pre ← cond A (mkTupleRead · argSlots)
  let post ← cond G (mkLensGet resPS ·)
  let bound ← cond r (mkTupleRead · argSlots)
  let argsGetter ← match argSlots with
    | [l] => mkAppM ``Lens.toGetter #[l]
    | _ => withLocalDeclD `st ps fun st => do
        mkAppM ``Getter.mk #[← mkLambdaFVars #[st] (← mkTupleRead st argSlots)]
  let body ← mkAppOptM ``Stmt.call #[some sig, some (← mkAppM ``Lens.toSetter #[resPS]),
    some p, some argsGetter]
  let rhs ← mkAppM ``phoareStmt #[pre, body, post, ρ, bound]
  let pf ← mkAppOptM ``phoareProc_as_phoareStmt
    #[some sig, some resVA, some argsVA, some A, some p, some G, some ρ, some r]
  let goal ← mkEq e rhs
  unless ← isDefEq (← mkEq e (← instantiateMVars (← inferType pf)).iff?.get!.2) goal do
    throwError "phoareProcToStmt: the statement built is not the lemma's"
  return { expr := rhs, proof? := some (← mkExpectedTypeHint (← mkPropExt pf) goal) }

/-- Rewrite a goal `phoareProc A p G ρ r` to the `phoareStmt` about `res <- call p (x₁, …, xₙ);`,
one local variable per parameter. -/
elab "phoare_proc_to_stmt" : tactic => liftMetaTactic1 fun g => do
  let r ← phoareProcToStmt (← g.getType)
  applySimpResultToTarget g (← g.getType) r

end Conv

end GaudisCrypt
