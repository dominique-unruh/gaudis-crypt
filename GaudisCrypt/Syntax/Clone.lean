import GaudisCrypt.Syntax.CloneRegistry

/-!
# EasyCrypt's `clone`

    clone import GaudisCrypt.SHA3.SecureRO as SRO with
      type «from» <- f_in, type «to» <- f_out,
      op bound <- limit, op sampleto <- sampleto
      proof * by first | exact limit_gt0 | exact sampleto_ll

An abstract theory `T` is a namespace whose declarations take the theory's types as implicit
section variables and its operators and axioms as one instance `[T.Params …]` (a class whose
types are `outParam`s, so that inside the theory nothing is written).  A clone is then:

* the instance `C.params : T.Params …`, the `op`s its data fields, the `proof *` tactic its
  axioms (EC's `proof *`; without it every axiom must be an `op`… — that is, an error);
* the clone's namespace `C`: for every definition and theorem `T.x` an alias `C.x`, `T.x` at the
  clone's types (`type a <- τ`, by the binder's name), at `C.params`, and at the instances the
  theory's types need (found by instance search where the clone is made).  A definition's alias
  is reducible, a theorem's a theorem, so that `C.Bounder`, `C.RO_is_collision_resistant` are
  EC's `SRO.Bounder`, `SRO.RO_is_collision_resistant`;
* `clone import`: `open C`, so the clone's names are used bare, as EC's (a declaration of the
  current namespace shadows an opened one, as a later EC declaration does).

The clone's instance is an instance: the theory's own instances (the coercions of EC's subtyping
of module types, `module_subtype`) take the theory's, and are then found at the clone.  Clones at
different types do not compete (the types select the instance), nor do clones of a theory without
operators (its `Params` is a proposition, `class Params (p f_in f_out : outParam Type) : Prop`,
its instances equal); two clones of one theory at the same types with different operators would,
and are not supported (EC's `SRO` and a second `SRO'` at the same types).  Used through its
namespace, each clone is its own: the aliases name the instance.

The clone's module variables are the theory's (`global_var`/`module_var` slots are named after
`T`): two clones of one theory at the same types share them, where EC gives each clone its own.
-/

namespace GaudisCrypt

open Lean Meta Elab Command Term

declare_syntax_cat cloneSubst (behavior := symbol)
syntax (name := cloneType) &"type" ident " <- " withPosition(term) : cloneSubst
syntax (name := cloneOp) &"op" ident " <- " withPosition(term) : cloneSubst

/-- EasyCrypt's `clone [import] T as C with type a <- τ, op o <- e proof * by tac`: see the
module docstring. -/
syntax (name := cloneCmd) "clone " (&"import")? ident ppSpace &"as" ppSpace ident
  (" with " sepBy1(cloneSubst, ", "))? (&"proof" "*" ppSpace Lean.Parser.Term.byTactic)? : command

namespace Clone

/-- Declarations of the theory that are not aliased: internal ones, the generated equations and
auxiliary recursors, instances, and inductive types with their constructors and recursors (an
alias of a structure would not have its constructor notation). -/
def skip (env : Environment) (n : Name) : Bool :=
  n.isInternalDetail || isPrivateName n || isAuxRecursor env n || isNoConfusion env n ||
    (match env.find? n with
     | some (.defnInfo _) | some (.thmInfo _) => false
     | _ => true)

/-- The application of `c` at the clone: its leading theory binders filled (the types by name,
the theory's instance by `params`, other instances by instance search), the rest kept. -/
def instantiate (c : Name) (types : NameMap Expr) (paramsCls : Option Name)
    (params : Option Expr) : MetaM Expr := do
  let info ← getConstInfo c
  let mut e := Lean.mkConst c (info.levelParams.map mkLevelParam)
  let mut t := info.type
  repeat
    let .forallE n d b bi := t | break
    if bi.isImplicit || bi.isStrictImplicit then
      let some v := types.find? n.eraseMacroScopes | break
      e := mkApp e v
      t := b.instantiate1 v
    else if bi.isInstImplicit then
      let isParams := paramsCls.isSome && d.getAppFn.constName? == paramsCls
      let v? ← if isParams then pure params else
        try pure (some (← synthInstance d)) catch _ => pure none
      let some v := v? | break
      if isParams then
        unless ← isDefEq d (← inferType v) do
          throwError "clone: {c}'s theory instance{indentExpr d}\nis not the clone's{indentExpr (← inferType v)}"
      e := mkApp e v
      t := b.instantiate1 v
    else break
  instantiateMVars e


/-- The free variables `e` depends on, closed under the types of those variables. -/
def usedVars (vars : Array Expr) (es : Array Expr) : MetaM (Array Expr) := do
  let mut s : CollectFVars.State := {}
  for e in es do s := collectFVars s (← instantiateMVars e)
  let mut changed := true
  while changed do
    changed := false
    for v in vars do
      if s.fvarSet.contains v.fvarId! then
        let s' := collectFVars s (← instantiateMVars (← inferType v))
        if s'.fvarSet.size != s.fvarSet.size then
          s := s'
          changed := true
  -- the section's instances on what is used (the current theory's `Params`, as `module_var`
  -- takes them): where the alias is used alone they are what determines the types
  changed := true
  while changed do
    changed := false
    for v in vars do
      if s.fvarSet.contains v.fvarId! then continue
      let d ← v.fvarId!.getDecl
      unless d.binderInfo.isInstImplicit do continue
      let ts := collectFVars {} (← instantiateMVars d.type)
      if !ts.fvarSet.isEmpty && ts.fvarIds.all (s.fvarSet.contains ·) then
        s := { s with fvarSet := s.fvarSet.insert v.fvarId!, fvarIds := s.fvarIds.push v.fvarId! }
        changed := true
  return vars.filter fun v => s.fvarSet.contains v.fvarId!

end Clone

open Clone in
elab_rules : command
  | `(cloneCmd| clone $[import%$imp]? $T:ident as $C:ident $[with $substs,*]?
        $[proof * $tac?]?) => do
    let env ← getEnv
    let some T' := (← resolveNamespace T).head?
      | throwErrorAt T "clone: unknown theory {T}"
    let substs := (substs.map (·.getElems)).getD #[]
    let tys : Array (Name × Term) := substs.filterMap fun s =>
      if s.raw.isOfKind ``cloneType then
        some (s.raw[1].getId.eraseMacroScopes, ⟨s.raw[3]⟩) else none
    let ops : Array (Ident × Term) := substs.filterMap fun s =>
      if s.raw.isOfKind ``cloneOp then some (⟨s.raw[1]⟩, ⟨s.raw[3]⟩) else none
    let Cn := (← getCurrNamespace) ++ C.getId
    modifyEnv (cloneExt.addEntry · (Cn, T'))
    let paramsCls := T' ++ `Params
    let hasParams := env.contains paramsCls
    let consts := env.constants.fold (init := #[]) fun acc n _ =>
      if T'.isPrefixOf n && n != T' && !(paramsCls.isPrefixOf n) && !skip env n then acc.push n
      else acc
    let consts := consts.qsort Name.lt
    runTermElabM fun vars => do
      let types ← tys.foldlM (init := ({} : NameMap Expr)) fun m (n, τ) => do
        return m.insert n (← instantiateMVars (← elabType τ))
      -- the instance `C.params`, at the section variables it uses
      let params? ← if !hasParams then pure none else do
        let clsInfo ← getConstInfo paramsCls
        let tyArgs ← forallTelescope clsInfo.type fun xs _ => xs.mapM fun x => do
          let n := (← x.fvarId!.getDecl).userName.eraseMacroScopes
          match types.find? n with
          | some τ => pure τ
          | none => throwErrorAt T "clone: the theory's type {n} is not instantiated (`type {n} <- …`)"
        let clsTy := mkAppN (Lean.mkConst paramsCls (clsInfo.levelParams.map fun _ => Level.one)) tyArgs
        let fields := getStructureFieldsFlattened env paramsCls (includeSubobjectFields := false)
        let mut vals : Array Term := #[]
        for f in fields do
          match ops.find? (·.1.getId.eraseMacroScopes == f) with
          | some (_, e) => vals := vals.push e
          | none =>
            match tac? with
            | some tac => vals := vals.push ⟨tac.raw⟩
            | none => throwErrorAt T "clone: {f} is neither an `op` nor proved (`proof * by …`)"
        let pv ← elabTermEnsuringType (← `(⟨$vals,*⟩)) clsTy
        synthesizeSyntheticMVarsNoPostponing
        let pv ← instantiateMVars pv
        let used ← usedVars vars #[pv]
        let lam ← instantiateMVars (← mkLambdaFVars used pv)
        let pn := Cn ++ `params
        let pty ← instantiateMVars (← inferType lam)
        addDecl (.defnDecl { name := pn, levelParams := [], type := pty, value := lam,
                             hints := ReducibilityHints.abbrev, safety := .safe })
        modifyEnv (addNoncomputable · pn)
        setReducibilityStatus pn .reducible
        addDocStringCore pn "The clone's operators and axioms (EC's `with op … proof *`)."
        -- an instance: the theory's own instances (its subtyping coercions) take it
        addInstance pn AttributeKind.global (eval_prio default)
        pure (some (mkAppN (Lean.mkConst pn) used))
      -- the aliases: each theory declaration at the clone
      let mut insts : Array (Name × Name × Expr) := #[]
      for c in consts do
        let aliasN := Cn ++ c.replacePrefix T' .anonymous
        if (← getEnv).contains aliasN then continue
        let s ← saveState
        let e? ← try
            let e ← instantiate c types (if hasParams then some paramsCls else none) params?
            pure (if (← instantiateMVars e).hasMVar then none else some e)
          catch _ => pure none
        match e? with
        | some e => insts := insts.push (c, aliasN, e)
        | none => s.restore
      -- a theory declaration at the clone, in a type, is the clone's alias (so that an alias's type
      -- reads as EC's, `SRO.RF → SRO.RF`, and field notation on a clone's module type finds the
      -- clone's accessors); the alias itself, at the section variables it uses
      let mut folds : Array (Expr × Expr) := #[]
      for (c, aliasN, e) in insts do
        let used ← usedVars vars #[e]
        let info ← getConstInfo c
        folds := folds.push (e, mkAppN (Lean.mkConst aliasN (info.levelParams.map mkLevelParam)) used)
      let fold (t : Expr) : MetaM Expr := Meta.transform t (post := fun x => do
        let some f := x.getAppFn.constName? | return .continue
        -- the theory's operators at the clone's instance are the clone's (`bound` is `limit`)
        if hasParams && paramsCls.isPrefixOf f then
          if let some x' ← unfoldProjInst? x then return .visit x'.headBeta
        for (e, r) in folds do
          if e.getAppFn.constName? == some f then
            let k := e.getAppNumArgs
            if x.getAppNumArgs ≥ k && (x.getAppArgs.extract 0 k) == e.getAppArgs then
              return .done (mkAppN r (x.getAppArgs.extract k x.getAppNumArgs))
        return .continue)
      let mut pending : Array (Name × Name × Expr × Expr) := #[]
      for (c, aliasN, e) in insts do
        let ty ← fold (← instantiateMVars (← inferType e))
        pending := pending.push (c, aliasN, e, ty)
      -- added once the aliases their types mention are
      let mut progress := true
      while progress && !pending.isEmpty do
        progress := false
        let mut rest := #[]
        for (c, aliasN, e, ty0) in pending do
          let env ← getEnv
          unless ty0.getUsedConstants.all env.contains do
            rest := rest.push (c, aliasN, e, ty0)
            continue
          progress := true
          let s ← saveState
          try
            let used ← usedVars vars #[e, ty0]
            let lam ← instantiateMVars (← mkLambdaFVars used e)
            let ty ← instantiateMVars (← mkForallFVars used ty0)
            let info ← getConstInfo c
            let lps := info.levelParams
            match info with
            | .thmInfo _ =>
              addDecl (.thmDecl { name := aliasN, levelParams := lps, type := ty, value := lam })
            | _ =>
              addDecl (.defnDecl { name := aliasN, levelParams := lps, type := ty, value := lam,
                                   hints := ReducibilityHints.abbrev, safety := .safe })
              modifyEnv (addNoncomputable · aliasN)
              setReducibilityStatus aliasN .reducible
            if let some doc ← findDocString? (← getEnv) c then addDocStringCore aliasN doc
          catch _ => s.restore
        pending := rest
    if imp.isSome then
      modifyScope fun sc => { sc with openDecls := .simple Cn [] :: sc.openDecls }

end GaudisCrypt
