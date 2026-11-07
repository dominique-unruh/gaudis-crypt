import Lean

/-!
# The registry of EasyCrypt clones

The clones `clone` (`Syntax/Clone.lean`) has made, and how a name of a clone's theory reads in the
clone: what the framework needs to know of clones (`declare module`'s restrictions and the
footprints of concrete modules find a clone's variables under the clone's names; module paths
follow a clone's aliases to the theory's modules).  Apart from the command, so that the command
can change without the framework being rebuilt.
-/

namespace GaudisCrypt

open Lean

/-- The clones made so far: a clone's namespace `C` ↦ its theory `T`. -/
initialize cloneExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (c, t) => m.insert c t
    addImportedFn := fun as => as.foldl (init := {}) fun m es =>
      es.foldl (init := m) fun m (c, t) => m.insert c t }

/-- The clone (its namespace and theory) whose namespace `n` is in, if any (the innermost). -/
def cloneOf? (env : Environment) (n : Name) : Option (Name × Name) := Id.run do
  let m := cloneExt.getState env
  let mut p := n.getPrefix
  while !p.isAnonymous do
    if let some t := m.find? p then return some (p, t)
    p := p.getPrefix
  return none

/-- The name `v` (of theory `T`) as the clone `C` has it, if the clone has it: `C.x` for `T.x`. -/
def cloneRename? (env : Environment) (C T v : Name) : Option Name :=
  if T.isPrefixOf v then
    let a := C ++ v.replacePrefix T .anonymous
    if env.contains a then some a else none
  else none

/-- `e` with the aliases of clones unfolded (`SRO.RO.m` ↦ `SecureRO.RO.m` at the clone's
instance): as code spells them, which reads the theory's definitions.  For tactics that take
variables or modules from the user (`equiv_call (_ : ={…})`, a frame). -/
def unfoldCloneAliases (e : Expr) : MetaM Expr := Meta.transform e (post := fun x => do
  let some c := x.getAppFn.constName? | return .continue
  if (cloneOf? (← getEnv) c).isNone then return .continue
  match ← Meta.unfoldDefinition? x with
  | some x' => return .visit x'.headBeta
  | none => return .continue)

/-- The declaration an alias of a clone stands for, through nested clones (`S.SRO.Bounder` ↦
`IndifRO_is_secure.SRO.Bounder` ↦ `SecureRO.Bounder`); any other name itself. -/
partial def cloneBase (env : Environment) (c : Name) : Name :=
  if (cloneOf? env c).isNone then c else
  match env.find? c >>= (·.value?) with
  | some v =>
    let rec body : Expr → Expr
      | .lam _ _ b _ => body b
      | e => e
    match (body v).getAppFn.constName? with
    | some c' => if c' == c then c else cloneBase env c'
    | none => c
  | none => c

end GaudisCrypt
