import GaudisCrypt.Syntax.ModuleSyntax

/-!
# EasyCrypt's module paths: `M(A, B).f`

EasyCrypt names a procedure of an applied functor as `M(A, B).f`.  Here that is a term:

    Preimage(A, RO).main        -- a procedure module (`Module.Proc sig`)

where `M(A₁, …, Aₙ)` is `Module.app M (Module.pair A₁ (… Aₙ))` and `.f` picks the procedure:

* the result is of a `moduletype` `C`: `.f` is its accessor, `C.f (Module.app M …)`;
* the result is a procedure module itself (a `module` with a single procedure and no declared
  type): `.f` must be the name of that procedure, `M.f`.

The arguments are module paths again: a name (`RO`), an application (`Bounder(RO)`), or any Lean
term in parentheses (`(RO.asRF sampleto m)`).  The head `M` is a name, so a module that still
takes Lean parameters is written in the old form (`Module.app (M p) A`) or with the parameters
bundled into instances.

The form exists at the term level only with the trailing `.f`.  Without it, `M(x)` would also
read EasyCrypt's `M.f(x)` of a `Pr[ ]` or of a procedure judgment as a module application.

Printing: an accessor applied to a module application, and a single-procedure module applied,
print in this form whenever their heads are names (`ModuleApplicationSyntaxTest.lean`).
-/

namespace GaudisCrypt

open Lean

/-- A module path: a name, an application `M(A, …)`, or a Lean term in parentheses. -/
declare_syntax_cat ec_mod
-- at `max`, like the path itself: the default (`lead`) precedence of these nodes would make the
-- parenthesizer wrap a path wherever a `term:max` is expected
syntax:max ident : ec_mod
syntax:max ident noWs "(" ec_mod,+ ")" : ec_mod
syntax:max "(" term ")" : ec_mod

/-- `M(A₁, …, Aₙ).f`: the procedure `f` of the module `M` applied to `A₁, …, Aₙ`.  `atomic`, so
that EC's `M.f(x)` (the procedure `M.f` and its arguments, as in `Pr[ M.f(x) @ &m : E ]`) falls
back to the name `M.f` instead of failing as a path without its `.f`. -/
syntax:max (name := ecProcPath) atomic(ident noWs "(" ec_mod,+ ")" noWs "." noWs ident) : term

namespace ModuleApplication

/-- The Lean term of a module path. -/
partial def ecModTerm : TSyntax `ec_mod → MacroM Term
  | `(ec_mod| $x:ident) => pure x
  | `(ec_mod| ($t:term)) => pure t
  | `(ec_mod| $m:ident($args,*)) => do appTerm m (← args.getElems.mapM ecModTerm)
  | _ => Macro.throwUnsupported
where
  /-- `Module.app m (Module.pair a₁ (… aₙ))`. -/
  appTerm (m : Ident) (args : Array Term) : MacroM Term := do
    let some last := args.back? | Macro.throwUnsupported
    let arg ← (args.pop).foldrM (fun a acc => `(Module.pair $a $acc)) last
    `(Module.app $m $arg)

/-- The procedures of the `module` `x`: the constants `x.f` its definition mentions that have a
`x.f.procedure`. -/
def moduleProcs (env : Environment) (x : Name) : Array Name := Id.run do
  let some ci := env.find? x | return #[]
  let some v := ci.value? | return #[]
  let mut out := #[]
  for c in v.getUsedConstants do
    if c.getPrefix == x && env.contains (c ++ `procedure) && !out.contains c then
      out := out.push c
  return out

/-- `c` is the accessor of a `moduletype`'s field (it has `c.utilities`). -/
def isAccessor (env : Environment) (c : Name) : Bool :=
  env.contains (c ++ `utilities)

end ModuleApplication

open Elab Term Meta ModuleApplication in
elab_rules : term
  | `($m:ident($args,*).$f:ident) => do
    -- `M(A).f.g` is `(M(A).f).g`: field notation after a path prints this way
    if let fname :: rest@(_ :: _) := f.getId.components then
      let path ← `($m:ident($args,*).$(mkIdent fname):ident)
      return ← elabTerm (← `(($path).$(mkIdent (Name.fromComponents rest)):ident)) none
    let app ← liftMacroM <| ecModTerm.appTerm m (← liftMacroM <| args.getElems.mapM ecModTerm)
    let e ← withSynthesize <| elabTerm app none
    if e.hasSyntheticSorry then throwAbortTerm
    let ty ← instantiateMVars (← inferType e)
    let fname := f.getId
    -- a `moduletype`: its accessor
    if let some C := ty.getAppFn.constName? then
      let acc := C ++ fname
      if isAccessor (← getEnv) acc then
        return mkAppN (← mkConstWithFreshMVarLevels acc) (ty.getAppArgs.push e)
    -- a procedure module: `f` names the module's procedure
    if (← whnfR ty).isAppOf ``Module.Proc then
      let x ← realizeGlobalConstNoOverloadWithInfo m
      let procs := moduleProcs (← getEnv) x
      unless procs.contains (x ++ fname) do
        throwErrorAt f "the module `{x}` has no procedure `{fname}`{if procs.isEmpty then
          m!"" else m!" (its procedure: {procs.map (·.getString!)})"}"
      return e
    throwErrorAt f "`{fname}` is not a procedure of this module, of type{indentExpr ty}"

/-! ## Printing -/

section Printing
open PrettyPrinter Delaborator SubExpr Meta ModuleApplication

/-- The arguments of a module application: a right-nested `Module.pair` chain split into its
components, each printed as a module path. -/
partial def delabPairArgs : DelabM (Array (TSyntax `ec_mod)) := do
  if (← getExpr).isAppOfArity ``Module.pair 6 then
    let hd ← withNaryArg 4 delabEcMod
    return #[hd] ++ (← withNaryArg 5 delabPairArgs)
  return #[← delabEcMod]
where
  /-- A module path: `M(…)` for an application with a name for its head, a name, or a
  parenthesized term. -/
  delabEcMod : DelabM (TSyntax `ec_mod) := do
    if let some (m, args) ← delabApp? then return ← `(ec_mod| $m:ident($args,*))
    let t ← delab
    if let `($x:ident) := t then return ← `(ec_mod| $x:ident)
    `(ec_mod| ($t))
  /-- `Module.app M A` with `M` printing as a name: the name and the argument paths. -/
  delabApp? : DelabM (Option (Ident × Array (TSyntax `ec_mod))) := do
    unless (← getExpr).isAppOfArity ``Module.app 6 do return none
    let `($m:ident) ← withNaryArg 4 delab | return none
    return some (m, ← withNaryArg 5 delabPairArgs)

/-- `C.f (Module.app M A)` for a `moduletype` accessor `C.f`: `M(A).f`. -/
@[delab app]
def delabAccessorPath : Delab := do
  guardSurfaceSyntax
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  guard (isAccessor (← getEnv) c && e.getAppNumArgs ≥ 1 && e.appArg!.isAppOfArity ``Module.app 6)
  let some (m, args) ← withAppArg delabPairArgs.delabApp? | failure
  `($m:ident($args,*).$(mkIdent (Name.mkSimple c.getString!)):ident)

/-- `Module.app X A` of a single-procedure `module` `X` with procedure `f`: `X(A).f`. -/
@[delab app.GaudisCrypt.Module.app]
def delabProcModulePath : Delab := do
  guardSurfaceSyntax
  let e ← getExpr
  guard (e.getAppNumArgs == 6)
  let some x := (e.getArg! 4).getAppFn.constName? | failure
  let #[f] := moduleProcs (← getEnv) x | failure
  guard ((← whnfR (e.getArg! 1)).isAppOf ``Module.Proc)
  let some (m, args) ← delabPairArgs.delabApp? | failure
  `($m:ident($args,*).$(mkIdent (Name.mkSimple f.getString!)):ident)

end Printing

end GaudisCrypt
