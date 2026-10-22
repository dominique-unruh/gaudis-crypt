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

/-! ## Printing

`prhlStmt A c₁ c₂ B` prints as `equiv[ P ==> Q ] { … } ~ { … }` when both statements print as
statements and both conditions are functions of the two states that only *read* them: a read
`§x` at the left state (`eval` at `CurrentState.mk σ₁`, `x.get σ₁`, `g.get σ₁.globals` for a
global `g`) prints as `§x{1}`, at the right state as `§x{2}`.  Otherwise the judgment prints as
the plain term.  The reads are first replaced by `relRead σ i x` (the read, carrying its side),
which the unexpander prints as `§x{i}`; the variables are recovered over the two statements and
the two conditions together, each declared on the side whose statement uses it (the left one if
only the conditions do). -/

universe u v in
/-- The read of `x` at the state `σ` of side `i` of a relational condition — `§x{i}`.  Only the
printer builds it; it is the read `Evaluatable.eval σ x`. -/
def relRead {X : Type u} {T : Type v} [Evaluatable X T] (σ : ProgramState) (_i : Nat) (x : X) :
    T :=
  Evaluatable.eval σ x

section Printing
open PrettyPrinter Delaborator SubExpr ProgramSyntax Meta

@[app_unexpander relRead]
def unexpandRelRead : Unexpander
  | `($_ $_ $i $x) =>
      return Syntax.node .none ``relEval
        #[Syntax.atom .none "§", x, Syntax.atom .none "{", i, Syntax.atom .none "}"]
  | _ => throw ()

/-- `s.globals`, as a projection function or a primitive projection, ↦ `s`. -/
private def globalsOf? (e : Lean.Expr) : Option Lean.Expr :=
  if e.isAppOfArity ``ProgramState.globals 1 then some e.appArg!
  else match e with
    | .proj ``ProgramState 0 s => some s
    | _ => none

/-- Replace the reads of the state `σ` in `e` by `relRead σ i x`: `eval` at `CurrentState.mk σ`,
`x.get σ`, and `g.get σ.globals` for a global `g`. -/
def markReads (σ : Lean.Expr) (i : Nat) (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let mk (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
      try some <$> mkAppOptM ``relRead #[none, none, none, some σ, some (mkNatLit i), some x]
      catch _ => pure none
    if e.isAppOfArity ``eval 5 then
      let cs := e.getArg! 3
      if cs.isAppOfArity ``CurrentState.mk 1 && cs.appArg! == σ then
        if let some r ← mk (e.getArg! 4) then return .done r
      return .continue
    let some (l, s) := ProgramSyntax.lensGet? e | return .continue
    unless s == σ || globalsOf? s == some σ do return .continue
    let some r ← mk l | return .continue
    if ← isDefEq r e then return .done r else return .continue)

/-- A relational condition `fun σ₁ σ₂ => P` with its reads marked (`markReads`). -/
def markCond (c : Lean.Expr) : MetaM Lean.Expr := do
  let .lam n₁ t₁ (.lam n₂ t₂ b bi₂) bi₁ := c | failure
  guard (t₁.isConstOf ``ProgramState && t₂.isConstOf ``ProgramState)
  withLocalDecl n₁ bi₁ t₁ fun s₁ => withLocalDecl n₂ bi₂ t₂ fun s₂ => do
    let b ← markReads s₂ 2 (← markReads s₁ 1 (b.instantiateRev #[s₁, s₂]))
    mkLambdaFVars #[s₁, s₂] b

/-- Do the states (loose bound variables `0` and `1` of `e`) occur other than as the state of a
`relRead`? -/
private partial def statesEscape (e : Lean.Expr) (d : Nat := 0) : Bool :=
  if e.isAppOfArity ``relRead 6 then statesEscape (e.getArg! 5) d
  else match e with
    | .bvar j => j == d || j == d + 1
    | .app f a => statesEscape f d || statesEscape a d
    | .lam _ t b _ | .forallE _ t b _ => statesEscape t d || statesEscape b (d + 1)
    | .letE _ t v b _ => statesEscape t d || statesEscape v d || statesEscape b (d + 1)
    | .mdata _ b | .proj _ _ b => statesEscape b d
    | _ => false

/-- Print a marked relational condition `fun σ₁ σ₂ => P` as `P`. -/
def delabRelCond : DelabM Term := do
  let .lam _ _ (.lam _ _ b _) _ := ← getExpr | failure
  guard !(statesEscape b)
  withBindingBody `σ₁ <| withBindingBody `σ₂ delab

/-- Print a relational judgment as `equiv[ P ==> Q ] { … } ~ { … }`. -/
@[delab app.GaudisCrypt.prhlStmt]
private def delabPrhlStmt : Delab := do
  guardSurfaceSyntax
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  let pre ← markCond (e.getArg! 0)
  let post ← markCond (e.getArg! 3)
  let parts := #[pre, e.getArg! 1, e.getArg! 2, post]
  let vars := (← frameVars parts #[]).filter (·.printable)
  let occursIn (v : FrameVar) (s : Lean.Expr) : Bool :=
    v.slots.any fun t => (s.find? (· == t)).isSome
  let vars₂ := vars.filter (occursIn · (e.getArg! 2))
  let vars₁ := vars.filter fun v => occursIn v (e.getArg! 1) || !occursIn v (e.getArg! 2)
  withVarLocals vars.toList parts fun es => do
    let stmts₁ ← withExpr es[1]! (delabGaudiStmts #[])
    let stmts₂ ← withExpr es[2]! (delabGaudiStmts #[])
    -- the conditions do not see the statements' spine binders
    guard ((spineLetNames stmts₁).isEmpty && (spineLetNames stmts₂).isEmpty)
    let p ← withExpr es[0]! delabRelCond
    let q ← withExpr es[3]! delabRelCond
    let lines (vs : Array FrameVar) : DelabM (Array (Syntax.TSepArray `proc_binder ",")) := do
      let bs ← vs.mapM varBinder
      return if bs.isEmpty then #[] else #[bs]
    let l₁ ← lines vars₁
    let l₂ ← lines vars₂
    `(equiv[ $p ==> $q ] {
        $[var $l₁:proc_binder,* ;]*
        $stmts₁:gaudi_stmt* } ~ {
        $[var $l₂:proc_binder,* ;]*
        $stmts₂:gaudi_stmt* })

end Printing

end GaudisCrypt
