import GaudisCrypt.Logic.PRHLStmt
import GaudisCrypt.Syntax.HoareSyntax

/-!
# Concrete syntax for relational judgments (pRHL)

EasyCrypt's `equiv` judgments, in the two forms of `hoare[ … ]` (`Syntax/HoareSyntax.lean`):

    equiv[ P ==> Q ] { var x : X; … } ~ { var y : Y; … }     -- prhlStmt, about two statements
    equiv[ M₁ (x) ~ M₂ (y) : P ==> Q ]                       -- prhlProc, about two procedures

The conditions are about **two** states, and every read says which: `§x{1}` reads `x` in the
left state, `§x{2}` in the right one (EC's `x{1}`, `x{2}`); `={x, y}` is `§x{1} = §x{2} ∧
§y{1} = §y{2}` (EC's `={x, y}`).  A read without a side (`§x`, `$x`) is an error in a relational
condition.

In the statement form, each side may declare its local variables; a condition sees those of both
sides (a name declared on both sides must have the same type there).  In the procedure form, the
precondition sees each side's parameters and globals, the postcondition each side's result `res`
and globals: `§res{1} = §res{2}`, `§x{1}` for the left parameter `x`.  As for `hoare[ M (x) : … ]`,
the parameter names may be left out when they are recorded.

The sided reads are expanded when the condition is elaborated: `§x{1}` becomes
`@eval _ _ _ (CurrentState.mk σ₁) x`, a read at the left state `σ₁` the condition is a function
of — the read `§x` of a `hoare[ ]` condition, at a given state.  So the reads are what the
unary tactics already handle (`simpReads`, `generalizeReads`).  (No printer yet: a relational
judgment prints as the plain term.)
-/

namespace GaudisCrypt

open Lean

/-- `§x{1}`, `§x{2}`: the value of the program variable `x` in the left or the right state of a
relational condition (`equiv[ … ]`). -/
syntax (name := relEval) "§" noWs term:max noWs "{" num "}" : term

/-- `={x, y}`: `x` and `y` agree on the two sides of a relational condition (EC's `={x, y}`). -/
syntax (name := relEqs) "={" term,* "}" : term

macro_rules
  | `(relEval| §$_:term{$_:num}) =>
      Macro.throwError "a sided read `§x{i}` is only meaningful in a relational condition \
        (`equiv[ … ]`)"

macro_rules
  | `(={ $_,* }) =>
      Macro.throwError "`={…}` is only meaningful in a relational condition (`equiv[ … ]`)"

namespace RelSyntax

/-- The read of the program variable `x` at the state `st`: what `§x` means where `st` is the
current state. -/
def readAt (st : Term) (x : Term) : MacroM Term :=
  `((@eval _ _ _ (CurrentState.mk $st) $x))

/-- Expand the sided reads of a relational condition: `§x{i}` ↦ a read at `states i` — of the
term `param i x` instead if that gives one (the parameters of a procedure judgment) — and
`={x, y}` ↦ the equations.  Unsided reads are rejected. -/
partial def expand (states : Nat → Option Term) (param : Nat → Name → Option Term)
    (stx : Syntax) : MacroM Syntax :=
  stx.replaceM fun s => do
    if s.getKind == ``relEval then
      let x : Term := ⟨s[1]⟩
      let some k := s[3].isNatLit? | Macro.throwErrorAt s "expected a side `{1}` or `{2}`"
      return some (← side k x)
    if s.getKind == ``relEqs then
      let xs := s[1].getSepArgs.map (⟨·⟩ : Syntax → Term)
      if xs.isEmpty then return some (← `(True))
      let eqs ← xs.mapM fun x => do `($(← side 1 x) = $(← side 2 x))
      return some (← eqs.pop.foldrM (fun e acc => `($e ∧ $acc)) eqs.back!)
    if s.isAntiquot then
      Macro.throwErrorAt s "in a relational condition, a read says which side it is about: \
        `§x{1}` or `§x{2}`"
    match s with
    | `(§$_:term) =>
        Macro.throwErrorAt s "in a relational condition, a read says which side it is about: \
          `§x{1}` or `§x{2}`"
    | _ => return none
where
  side (k : Nat) (x : Term) : MacroM Term := do
    let some st := states k
      | Macro.throwErrorAt x s!"a relational condition has the sides 1 and 2, not {k}"
    if x.raw.isIdent then
      if let some p := param k x.raw.getId.eraseMacroScopes then return ← readAt st p
    readAt st ⟨← expand states param x⟩

/-- The `letI` bindings of the local variables of the two sides: their union, a name declared on
both sides with the same type bound once. -/
def unionBinds (b₁ b₂ : Array (Ident × Term)) : MacroM (Array (Ident × Term)) := do
  let mut bs := b₁
  for (id, ty) in b₂ do
    match bs.find? (·.1.getId.eraseMacroScopes == id.getId.eraseMacroScopes) with
    | some (_, ty₁) =>
        unless ty₁.raw.structEq ty.raw do
          Macro.throwErrorAt id s!"`{id.getId.eraseMacroScopes}` is declared on both sides with \
            different types"
    | none => bs := bs.push (id, ty)
  return bs

/-- The local variables a `var …;` block declares. -/
def localsOf (locals : Array (Syntax.TSepArray `proc_binder ",")) :
    MacroM (Array (Ident × Term)) := do
  let bs := (← (locals.toList.flatMap (·.getElems.toList)).mapM ProgramSyntax.parseBinder).flatten
  ProgramSyntax.checkDistinct (bs.toArray.map (·.1))
  return bs.toArray

end RelSyntax

/-! ## Statement judgments -/

syntax ppGroup("equiv[ " term " ==> " term " ] " "{")
         (ppIndent(ppLine ppGroup("var " proc_binder,* ";")))*
         gaudi_stmt*
       ppDedent(ppDedent(ppLine)) "}" " ~ " "{"
         (ppIndent(ppLine ppGroup("var " proc_binder,* ";")))*
         gaudi_stmt*
       ppDedent(ppDedent(ppLine)) "}" : term

macro_rules
  | `(equiv[ $pre:term ==> $post:term ] {
        $[var $locals₁:proc_binder,* ;]*
        $stmts₁:gaudi_stmt*
      } ~ {
        $[var $locals₂:proc_binder,* ;]*
        $stmts₂:gaudi_stmt*
      }) => do
    let bs₁ ← RelSyntax.localsOf locals₁
    let bs₂ ← RelSyntax.localsOf locals₂
    let body (bs : Array (Ident × Term)) (stmts : Array (TSyntax `gaudi_stmt)) : MacroM Term := do
      let binds ← bs.mapM fun (id, ty) => ProgramSyntax.varBinding id ty
      ProgramSyntax.wrapLetI binds (← `((GaudiProg[ $stmts* ] : Stmt)))
    let binds ← (← RelSyntax.unionBinds bs₁ bs₂).mapM fun (id, ty) =>
      ProgramSyntax.varBinding id ty
    let cond (p : Term) : MacroM Term := do
      let σ₁ ← `(σ₁)
      let σ₂ ← `(σ₂)
      let states (k : Nat) : Option Term := if k == 1 then some σ₁ else if k == 2 then some σ₂
        else none
      let p' : Term := ⟨← RelSyntax.expand states (fun _ _ => none) p⟩
      ProgramSyntax.wrapLetI binds
        (← `(fun ($σ₁ : ProgramState) ($σ₂ : ProgramState) => ($p' : Prop)))
    `(prhlStmt $(← cond pre) $(← body bs₁ stmts₁) $(← body bs₂ stmts₂) $(← cond post))

/-! ## Procedure judgments -/

syntax ppGroup("equiv[ " term:max (" (" ident,* ")")? " ~ " term:max (" (" ident,* ")")?
  " : " term " ==> " term " ]") : term

open Elab Term Meta in
elab_rules : term <= expectedType?
  | `(equiv[ $M₁:term $[( $written₁:ident,* )]? ~ $M₂:term $[( $written₂:ident,* )]? :
        $pre:term ==> $post:term ]) => do
    let side (M : Term) (written : Option (Array Ident)) :
        TermElabM (Term × Lean.Expr × Array Name × Term × Term) := do
      let (procExpr, procTerm, sig) ← procedureOf M
      let params ← whnf (mkApp (mkConst ``ProcedureSignature.params) sig)
      let some tys ← ModuleDecl.listLit? params
        | throwErrorAt M m!"the parameter list of this procedure's signature is not a list \
            literal:{indentExpr params}"
      let names ← paramNamesOf M written procExpr tys.length
      let paramTy ← exprToSyntax (← whnf (mkApp (mkConst ``ProcedureSignature.ParamType) sig))
      let retTy ← exprToSyntax (← whnf (mkApp (mkConst ``ProcedureSignature.ret) sig))
      return (procTerm, sig, names, paramTy, retTy)
    let (procTerm₁, sig₁, names₁, paramTy₁, retTy₁) ← side M₁ (written₁.map (·.getElems))
    let (procTerm₂, sig₂, names₂, paramTy₂, retTy₂) ← side M₂ (written₂.map (·.getElems))
    let args₁ := mkIdent `args₁
    let args₂ := mkIdent `args₂
    let g₁ := mkIdent `σ₁
    let g₂ := mkIdent `σ₂
    let pack (g : Ident) : TermElabM Term := `((⟨$g, VariableAssignment.init⟩ : ProgramState))
    let states₁ ← pack g₁
    let states₂ ← pack g₂
    let states (k : Nat) : Option Term :=
      if k == 1 then some states₁ else if k == 2 then some states₂ else none
    -- each side's parameters, bound to fresh names (the two sides may share them)
    let paramBinds (k : Nat) (names : Array Name) (args : Ident) :
        TermElabM (Array (Name × Ident × Term)) := do
      let n := names.size
      let mut bs := #[(`params, ← `(Getter.mk fun _ => $args))]
      for i in [0:n] do
        let slot ← liftMacroM (ProgramSyntax.mkChain (ProgramSyntax.navSteps i n))
        bs := bs.push (names[i]!, ← `(Getter.mk fun _ => ($slot).get $args))
      bs.mapM fun (nm, val) => do
        let id := mkIdent (← MonadQuotation.addMacroScope (nm.appendAfter s!"_{k}"))
        return (nm, id, val)
    let bs₁ ← paramBinds 1 names₁ args₁
    let bs₂ ← paramBinds 2 names₂ args₂
    let lookup (bs₁ bs₂ : Array (Name × Ident × Term)) (k : Nat) (n : Name) : Option Term :=
      let bs := if k == 1 then bs₁ else bs₂
      (bs.find? (·.1 == n)).map fun (_, id, _) => (id : Term)
    let wrap (bs : Array (Name × Ident × Term)) (body : Term) : TermElabM Term :=
      bs.foldrM (fun (_, id, val) acc => `(let $id:ident : Getter _ ProgramState := $val; $acc))
        body
    let preBody : Term := ⟨← liftMacroM (RelSyntax.expand states (lookup bs₁ bs₂) pre)⟩
    let preTerm ← `(fun ($args₁ : $paramTy₁) ($g₁ : VariableAssignment) ($args₂ : $paramTy₂)
        ($g₂ : VariableAssignment) => $(← wrap (bs₁ ++ bs₂) (← `(($preBody : Prop)))))
    let r₁ := mkIdent `r₁
    let r₂ := mkIdent `r₂
    let res₁ := #[(`res, mkIdent (← MonadQuotation.addMacroScope `res_1),
      ← `(Getter.mk fun _ => $r₁))]
    let res₂ := #[(`res, mkIdent (← MonadQuotation.addMacroScope `res_2),
      ← `(Getter.mk fun _ => $r₂))]
    let postBody : Term := ⟨← liftMacroM (RelSyntax.expand states (lookup res₁ res₂) post)⟩
    let postTerm ← `(fun ($r₁ : $retTy₁) ($g₁ : VariableAssignment) ($r₂ : $retTy₂)
        ($g₂ : VariableAssignment) => $(← wrap (res₁ ++ res₂) (← `(($postBody : Prop)))))
    elabTerm (← `(prhlProc (sig₁ := $(← exprToSyntax sig₁)) (sig₂ := $(← exprToSyntax sig₂))
      $preTerm $procTerm₁ $procTerm₂ $postTerm)) expectedType?

end GaudisCrypt
