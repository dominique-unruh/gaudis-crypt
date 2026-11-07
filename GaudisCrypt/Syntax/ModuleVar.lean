import GaudisCrypt.Language.Variables

/-!
# Module variables of a generic theory: `module_var`

    module_var RO.m : FMap «from» «to»

declares the module variable `RO.m` of a theory whose types are section variables, as
`global_var` does (the slot of `⟨"N.RO.m", T⟩`, `N.RO.m` the full name, with its
`Lens.IsGlobalVar` instance, disjoint from the other globals by instance search), but taking the
section's instances too.  With the theory's operators in a class whose types are
`outParam`s (`class Params (from to : outParam Type)`), that instance is what determines the types
where the variable is used alone (`RO.m`, `§RO.m`), as EC's `RO.m` is used.  (`global_var` takes
only the section variables its type mentions, so there the types would stay undetermined.)

The name's key proof is a theorem of its own, `RO.m.key_eq : k = VariableName.encode "N.RO.m"`,
proven once here.  With the proof `rfl` (as `VariableName.mk` makes it), every use of the
instance would evaluate `encode "N.RO.m"` again — in instance search, to check the proof against
the instance's pattern, and in the kernel — which for a name of 50 characters is some 0.5 s per
disjointness found; with the theorem it is nothing (its type is already the pattern's).
-/

-- the quotations' layout (`$[$doc?]? module_var`) trips the whitespace linter
set_option linter.style.whitespace false

namespace GaudisCrypt

open Lean Elab Command

/-- `module_var x : T`: see the module docstring. -/
syntax (docComment)? "module_var " ident " : " term : command

elab_rules : command
  | `($[$doc?]? module_var $x : $T) => do
    let full := (← getCurrNamespace) ++ x.getId.eraseMacroScopes
    let n := quote full.toString
    -- the section's instances, used in the body so that the definition takes them (a section
    -- variable is part of a definition only where it is used)
    let instTys : Array Term := (← getScope).varDecls.filterMap fun b =>
      match b with
      | `(Lean.Parser.Term.bracketedBinderF| [$ty]) => some ty
      | `(Lean.Parser.Term.bracketedBinderF| [$_ : $ty]) => some ty
      | _ => none
    -- the key and its proof, a theorem (see the module docstring)
    let k := Syntax.mkNumLit (toString (VariableName.encode full.toString))
    let kx := mkIdentFrom x (x.getId ++ `key_eq)
    elabCommand (← `(variable_name_key_theorem $kx $n))
    let body ← instTys.foldrM (fun ty acc => `(have _ := (inferInstance : $ty); $acc))
      (← `(varLens (@VariableName.mk $n $T _ $k $kx)))
    elabCommand (← `($[$doc?]? @[nolint unusedArguments]
      noncomputable def $x : Lens $T VariableAssignment := $body))
    elabCommand (← `(instance : Lens.IsGlobalVar ($x : Lens $T VariableAssignment)
        (@VariableName.mk $n $T _ $k $kx) := ⟨rfl, HEq.rfl⟩))

end GaudisCrypt
