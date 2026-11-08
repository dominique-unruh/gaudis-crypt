import GaudisCrypt.Syntax.ModuleSyntax

/-!
# EasyCrypt's subtyping of module types: `module_subtype`

    module_subtype RF <: Oracle

makes a module of type `RF` usable where an `Oracle` is expected, as EasyCrypt does for a module
type with (at least) the procedures of another: a `Coe RF Oracle` whose function builds the
`Oracle` from `RF`'s procedures of the same names, `fun s => Oracle.mk { get := s.get }` — or,
when the two module types have the same procedures (equal by definition), the identity: the
module itself, as EC sees it.  The
function is a `fun` building the record, not a named function, so that the coercion unfolds to
the record the `module` command reads a callee like `A(Bounder(F))` back from; it prints back as
the module (`Syntax/ModuleApplicationSyntax.lean`).  Either side may be a module type applied to
its parameters, in parentheses (`(PROM.FullRO.RO_T «from» «to»)`).
-/

namespace GaudisCrypt

open Lean Elab Command

/-- `module_subtype S <: T`: see the module docstring. -/
syntax (docComment)? "module_subtype " term:max " <: " term:max : command

/-- The fields of the structure `n`, if it is one. -/
private def getStructureFields? (env : Environment) (n : Name) : Option (Array Name) :=
  if isStructure env n then some (getStructureFields env n) else none

/-- The `moduletype` a module type term names: its head constant. -/
private partial def headModuleType (t : Term) : CommandElabM Name := do
  match t with
  | `(($t)) => headModuleType t
  | `($f:ident $_*) => liftTermElabM <| realizeGlobalConstNoOverloadWithInfo f
  | `($f:ident) => liftTermElabM <| realizeGlobalConstNoOverloadWithInfo f
  | _ => throwErrorAt t "module_subtype: expected a module type, a name applied to its parameters"

elab_rules : command
  | `($[$doc?]? module_subtype $S <: $T) => do
    -- the same procedures (the two module types equal by definition): EC's subtyping is the
    -- identity, and so is the view — a module of `S` is one of `T` as it stands, no record
    -- `runTermElabM`: the section's variables (its instances) in scope
    let same ← runTermElabM fun _ => do
      let log ← Core.getMessageLog
      try
        Term.withoutErrToSorry do
          let Se ← Term.elabType S
          Term.synthesizeSyntheticMVarsNoPostponing
          let Se ← instantiateMVars Se
          if Se.hasMVar || Se.hasSorry then return false
          -- `T`'s parameters (if written without them) from `S`
          let Te ← Term.elabType T
          unless ← Meta.isDefEq Se Te do return false
          Term.synthesizeSyntheticMVarsNoPostponing
          let Te ← instantiateMVars Te
          if Te.hasMVar || Te.hasSorry then return false
          return !(← Core.getMessageLog).hasErrors
      catch _ => return false
      finally Core.setMessageLog log
    if same then
      elabCommand (← `($[$doc?]? noncomputable instance : Coe $S $T := ⟨fun s => s⟩))
      return
    let env ← getEnv
    let C ← headModuleType T
    let some fields := getStructureFields? env (C ++ `Structure)
      | throwErrorAt T "module_subtype: `{C}` is not a `moduletype` (no `{C}.Structure`)"
    let some (.ctorInfo ctor) := env.find? (C ++ `Structure ++ `mk)
      | throwErrorAt T "module_subtype: no constructor `{C}.Structure.mk`"
    let some mkInfo := env.find? (C ++ `mk)
      | throwErrorAt T "module_subtype: no constructor `{C}.mk`"
    -- `C.mk`'s parameters (the module type's) before the record, left to unification
    let mkArity := (← liftTermElabM <| Meta.forallTelescope mkInfo.type fun xs _ => pure xs.size)
    let s := mkIdent `s
    let args ← fields.mapM fun f => `($s.$(mkIdent f):ident)
    let hole ← `(_)
    let holes (n : Nat) : Array Term := Array.replicate n hole
    let record ← `(@$(mkCIdent (C ++ `Structure ++ `mk)) $(holes ctor.numParams)* $args*)
    let body ← `(@$(mkCIdent (C ++ `mk)) $(holes (mkArity - 1))* $record)
    elabCommand (← `($[$doc?]? noncomputable instance : Coe $S $T := ⟨fun $s => $body⟩))

end GaudisCrypt
