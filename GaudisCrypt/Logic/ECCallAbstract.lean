import GaudisCrypt.Logic.ECGlob
import GaudisCrypt.Logic.FelTactic
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.FootprintUpper

/-!
# EasyCrypt's `call (_: ={glob A, x₁, …})` on an abstract procedure

    equiv_call (_ : ={glob A, Bounder.bounder, Counter.c, RO.m})

The last statements of both sides call the same declared module `A` (`declare module`), with
oracles `O₁`, `O₂` (`A(O₁).f`, `A(O₂).f`).  EC's `call (_: ={glob A, X})`: the two calls agree on
their results and on `glob A` and `X` afterwards, if their arguments and `glob A`, `X` agree
before, and if the oracles' procedures keep that agreement (`prhlProc_abstract_call_module`, the
invariant `globInvF X (glob A) Eq`).

Goals, as EC's: the oracles' judgments (`oracle`, one per procedure of the oracles' module type,
each `equiv[ O₁.f ~ O₂.f : ={arg, glob A, X} ==> ={res, glob A, X} ]`), then the code before the
calls (`pre`).  The representation of `A` comes from its declaration and the oracles' module type
`T.ext`; `A`'s disjointness from `X` and the oracles' countable arguments are discharged as for
`hoare_call (: inv)`.  `glob A` may be written or left out: it is always part of the invariant.
-/

namespace GaudisCrypt

/-- **A concrete procedure keeps `={glob R}`**: a procedure module `M` touching only `R` (its
footprint below `R`) runs the same from equal arguments and states equal on `R` (EC's
`call (_ : ={glob P})` on a concrete callee, its oracle judgment by `sim`). -/
theorem prhlProc_glob_module {sig : ProcedureSignature} (M : Module.Proc sig)
    {R : Footprint VariableAssignment} (hM : FVP.fvP M ≤ R) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ R.touched_getter.get g₁ = R.touched_getter.get g₂)
      M.procedure M.procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ R.touched_getter.get g₁ = R.touched_getter.get g₂) :=
  prhlProc_glob fun a => ProgramDenotation.inFootprint_mono (Module.Proc.inFootprint_fvP M a) hM

/-- A statement about every oracle of a module type with one more procedure: the first one, and
every other. -/
theorem HoleIndex.forall_cons {s : ProcedureSignature} {holes : HoleSigs}
    {P : ∀ {sig' : ProcedureSignature}, HoleIndex (.cons s holes) sig' → Prop}
    (h0 : P .zero) (hs : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'), P (.succ n)) :
    ∀ {sig' : ProcedureSignature} (n : HoleIndex (.cons s holes) sig'), P n := by
  intro _ n
  cases n with
  | zero => exact h0
  | succ n => exact hs n

/-- A statement about every oracle of a module type without procedures. -/
theorem HoleIndex.forall_empty {P : ∀ {sig' : ProcedureSignature}, HoleIndex .empty sig' → Prop} :
    ∀ {sig' : ProcedureSignature} (n : HoleIndex .empty sig'), P n :=
  fun n => nomatch n

end GaudisCrypt

namespace GaudisCrypt.ECCall

open Lean Meta Elab Tactic FelTactic

/-- The components of the oracles `O : T` (`T` a `×ₘ` of module types): each module type and
module, in the order of the holes (`ModuleTypeRep.holesApp`); a literal pair's components, or
(`literal := false`) `Module.fst O`, `Module.snd O` — what `T`'s canonical `ext` reduces to. -/
partial def components (T O : Lean.Expr) (literal := true) :
    MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let T' ← whnfR T
  if T'.isAppOfArity ``GaudisCrypt.Module.Prod 4 then
    let (X, Y) ← if literal && O.isAppOfArity ``GaudisCrypt.Module.pair 6 then
        pure (O.getArg! 4, O.getArg! 5)
      else pure (← mkAppM ``GaudisCrypt.Module.fst #[O], ← mkAppM ``GaudisCrypt.Module.snd #[O])
    return (← components (T'.getArg! 0) X literal) ++ (← components (T'.getArg! 1) Y literal)
  return #[(T', O)]

/-- The procedures of a module `X` of a module type `C` declared by `moduletype` (its fields, in
order), as `(C.f X).procedure`. -/
def procsOf (C X : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let some c := C.getAppFn.constName?
    | throwError "equiv_call: the oracles' type is not a module type:{indentExpr C}"
  let some fs := getStructureFields? (← getEnv) (c ++ `Structure)
    | throwError "equiv_call: `{c}` is not a module type declared by `moduletype`"
  fs.mapM fun f => do
    let acc ← mkConstWithFreshMVarLevels (c ++ f)
    mkAppM ``GaudisCrypt.Module.Proc.procedure #[mkAppN acc (C.getAppArgs.push X)]

/-- `holes` as a literal `.cons s₁ (… .empty)` (the signatures left as they are). -/
partial def holesLit (h : Lean.Expr) : MetaM Lean.Expr := do
  let h ← whnf h
  if h.isAppOfArity ``HoleSigs.cons 2 then
    return mkApp2 h.getAppFn (h.getArg! 0) (← holesLit (h.getArg! 1))
  return h

/-- Split a goal `∀ {sig'} (n : HoleIndex holes sig'), P n` over the `k` holes. -/
partial def splitHoles (g : MVarId) (k : Nat) : TacticM (List MVarId) := do
  -- the holes as a literal, for `HoleIndex.forall_cons` to apply
  let ty ← instantiateMVars (← g.getType)
  let g ← match ty.find? (·.isAppOfArity ``HoleIndex 2) with
    | some hi =>
      let h := hi.getArg! 0
      if h.isAppOf ``HoleSigs.cons || h.isAppOf ``HoleSigs.empty then pure g
      else g.withContext do
        let lit ← holesLit h
        g.change (ty.replace fun e => if e == h then some lit else none)
    | none => pure g
  if k == 0 then
    let [] ← evalTacticAt (← `(tactic| apply HoleIndex.forall_empty)) g
      | throwError "equiv_call: more oracle procedures than expected"
    return []
  let [g0, g1] ← evalTacticAt (← `(tactic| apply HoleIndex.forall_cons)) g
    | throwError "equiv_call: fewer oracle procedures than expected"
  return g0 :: (← splitHoles g1 (k - 1))

/-- In the goal `g` about the hole `k`: each `(ext O).lookup _` the procedure of `O₁` or `O₂` it
is (`procs₁[k]`, `procs₂[k]`); the views `L.get g` taken apart (`Lens.pair`); the goal's
remaining `fun`s applied. -/
def niceGoal (g : MVarId) (O₁ : Lean.Expr) (p₁ p₂ : Lean.Expr) : TacticM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let ty' := ty.replace fun e =>
    if e.isAppOf ``HoleSigs.Instantiation.lookup then
      some (if (e.find? (· == O₁)).isSome then p₁ else p₂)
    else none
  let g ← g.change ty'
  let [g] ← evalTacticAt (← `(tactic|
      ((try dsimp only [Lens.pair]); (try simp only [Module.fst_pair, Module.snd_pair])))) g
    | return g
  return g


end GaudisCrypt.ECCall

namespace GaudisCrypt

open Lean Meta Elab Tactic FelTactic PRHLWp ECCall

/-- **EC's `call (_: ={glob A, x₁, …})`**: see the module docstring. -/
syntax (name := equivCallInv) "equiv_call" " (" "_" " : " "={" term,+ "}" ")" : tactic

elab_rules (kind := equivCallInv) : tactic
  | `(tactic| equiv_call (_ : ={ $xs:term,* })) => withMainContext do
    let g ← getMainGoal
    let _ ← prhlGoal g "equiv_call"
    let g ← HoareSplit.hoareSplit 1 g
    setGoals [g]
    let ty ← instantiateMVars (← g.getType)
    -- the callee of the left side's last statement (not a module applied anywhere in the goal)
    let abs? ← g.withContext do
      let st ← TacticMisc.openStmt (ty.getArg! 1)
      let last ← if st.isAppOfArity ``StmtWithHoles.seq 3 then TacticMisc.openStmt (st.getArg! 2)
        else pure st
      try
        let (ext, _, C) ← abstractCall last
        pure (some (ext, C))
      catch _ => pure none
    -- an abstract callee `D(O)` (`D` declared) of a module type without `T.ext` (a product
    -- `DFUNCTIONALITY ×ₘ DPRIMITIVE`): its canonical `ext`, one oracle goal per procedure
    let lastCall (stmt : Lean.Expr) : MetaM (Option Lean.Expr) := do
      let st ← TacticMisc.openStmt stmt
      let last ← if st.isAppOfArity ``StmtWithHoles.seq 3 then TacticMisc.openStmt (st.getArg! 2)
        else pure st
      return last.find? (·.isAppOfArity ``GaudisCrypt.Module.app 6)
    let gen? ← if abs?.isSome then pure none else g.withContext do
      let some c₁ ← lastCall (ty.getArg! 1) | pure none
      let some c₂ ← lastCall (ty.getArg! 2) | pure none
      if (c₁.getArg! 4).isFVar then pure (some (c₁.getArg! 4, c₁.getArg! 5, c₂.getArg! 5))
      else pure none
    if let some (D, O₁, O₂) := gen? then
      g.withContext do
        let isGlob : Term → Bool := fun t => match t with
          | `(glob $_) => true
          | _ => false
        let items := xs.getElems.filter (!isGlob ·)
        let some last := items.back?
          | throwError "equiv_call: the oracles' variables, `=\{glob A, x₁, …}`"
        let L ← items.pop.foldrM (fun x acc => `(Lens.pair $x $acc)) last
        let L ← do
          let Le ← Term.elabTerm L none
          Term.synthesizeSyntheticMVarsNoPostponing
          Term.exprToSyntax (← unfoldCloneAliases (← instantiateMVars Le))
        -- the region kept equal: the `glob`s named, the callee's among them
        let DS ← Term.exprToSyntax D
        let globs ← xs.getElems.filterMapM fun (t : Term) => match t with
          | `(glob $a) => return some (← `(FVP.fvP $a))
          | _ => return none
        let globs ← if globs.isEmpty then pure #[← `(FVP.fvP $DS)] else pure globs
        let F ← globs.pop.foldrM (fun x acc => `($x ⊔ $acc)) globs.back!
        let T ← inferType O₁
        let TS ← Term.exprToSyntax T
        let extS ← `(fun O => (Module.moduleTypeRep $TS).extOf (Module.cast $TS O))
        evalTactic (← `(tactic| refine prhlStmt_seq_call
            (prhlProc_abstract_call_moduleF (L := $L) _ $extS
              (Module.Declared.ecModule _ $extS).representable $F (by fp_le) ?hdisj Eq ?hc _ _
              ?oracle) ?pre))
        untagGoals
        closeTagged `hdisj (← `(tactic| ((try simp only [Footprint.lens_pair]); fp_disjoint)))
        -- the oracles' procedures, and EC's order of them (the last component first)
        let comps ← components T O₁
        let nprocs ← comps.mapM fun (C, X) => return (← procsOf C X).size
        let k := nprocs.foldl (· + ·) 0
        let mut start := 0
        let mut groups : Array (Array Nat) := #[]
        for n in nprocs do
          groups := groups.push ((List.range n).toArray.map (start + ·))
          start := start + n
        let ecOrder := groups.reverse.flatten
        let procsFS (O : Lean.Expr) : MetaM (Array Lean.Expr) := do
          return (← (← components T O false).mapM fun (C, X) => procsOf C X).flatten
        let fs₁ ← procsFS O₁
        let fs₂ ← procsFS O₂
        let byTag (t : Name) : TacticM (Option MVarId) := do
          (← getGoals).findM? fun g => return (← g.getTag) == t
        let mut done : Array MVarId := #[]
        if let some gc ← byTag `hc then
          for h in ← splitHoles gc k do
            let [] ← evalTacticAt (← `(tactic| first
                | infer_instance
                | (dsimp only [ProcedureSignature.ParamType, typeListToTuple]; infer_instance))) h
              | throwError "equiv_call: an oracle's argument type is not countable"
          done := done.push gc
        let mut oracleGs : Array MVarId := #[]
        if let some go ← byTag `oracle then
          let hs := (← splitHoles go k).toArray
          for i in ecOrder do
            let h ← niceGoal hs[i]! O₁ fs₁[i]! fs₂[i]!
            let h ← (do
              let [h'] ← evalTacticAt (← `(tactic| dsimp only [globInvF])) h | pure h
              pure h') <|> pure h
            h.setTag `oracle
            oracleGs := oracleGs.push h
          done := done.push go
        let rest ← (← getGoals).filterM fun g' => return !done.contains g'
        let rest ← rest.mapM fun g' => do
          if (← g'.getTag) == `pre then
            try Judgment.simpArg g' 3 relSimpDecls [] catch _ => pure g'
          else pure g'
        setGoals (oracleGs.toList ++ rest)
      return
    -- a concrete callee: it touches only what `={…}` names (`prhlProc_glob_module`)
    let some (ext, C) := abs? | do
      let Rs ← xs.getElems.mapM fun (t : Term) => match t with
        | `(glob $a) => `(FVP.fvP $a)
        | _ => `(Lens.footprint $t)
      let some last := Rs.back? | throwError "equiv_call: `=\{glob M, x₁, …}`"
      let R ← Rs.pop.foldrM (fun x acc => `($x ⊔ $acc)) last
      g.withContext <| evalTactic (← `(tactic| refine prhlStmt_seq_call
          (prhlProc_glob_module _ (R := $R) ?hM) ?pre))
      untagGoals
      closeTagged `hM (← `(tactic| fp_le))
      return
    let isGlob : Term → Bool := fun t => match t with
      | `(glob $_) => true
      | _ => false
    let items := xs.getElems.filter (!isGlob ·)
    let some last := items.back?
      | throwError "equiv_call: the oracles' variables, `=\{glob A, x₁, …}`"
    let L ← items.pop.foldrM (fun x acc => `(Lens.pair $x $acc)) last
    let L ← g.withContext do
      let Le ← Term.elabTerm L none
      Term.synthesizeSyntheticMVarsNoPostponing
      Term.exprToSyntax (← unfoldCloneAliases (← instantiateMVars Le))
    let extS ← Term.exprToSyntax ext
    g.withContext <| evalTactic (← `(tactic| refine prhlStmt_seq_call
        (prhlProc_abstract_call_module (L := $L) _ $extS
          (Module.Declared.ecModule _ $extS).representable ?hdisj Eq ?hc _ _ ?oracle) ?pre))
    untagGoals
    closeTagged `hdisj (← `(tactic| ((try simp only [Footprint.lens_pair]); fp_disjoint)))
    closeTagged `hc (← `(tactic| (apply HoleIndex.forall_single; first
      | infer_instance
      | (dsimp only [ProcedureSignature.ParamType, typeListToTuple]; infer_instance))))
    -- the oracles' judgments, each procedure out of `T.ext` and the record (`T.f.mk_simp`)
    let gs ← getGoals
    if let some go ← gs.findM? (fun g => return (← g.getTag) == `oracle) then
      let env ← getEnv
      let mkSimps : Array Ident := match getStructureFields? env (C ++ `Structure) with
        | some fs => fs.filterMap fun f =>
            let n := C ++ f ++ `mk_simp
            if env.contains n then some (mkIdent n) else none
        | none => #[]
      let extC := C ++ `ext
      let [go'] ← evalTacticAt (← `(tactic| apply HoleIndex.forall_single)) go
        | throwError "equiv_call: one oracle procedure expected"
      let rest ← evalTacticAt (← `(tactic|
          simp only [$(mkIdent extC):ident, HoleSigs.Instantiation.lookup_zero_single,
            $[$mkSimps:ident],*])) go'
      setGoals (gs.filter (· != go) ++ rest)
      for r in rest do r.setTag `oracle
    -- the code before the calls: its postcondition simplified as `equiv_call`'s
    let gs ← getGoals
    let gs ← gs.mapM fun g' => do
      if (← g'.getTag) == `pre then
        try Judgment.simpArg g' 3 relSimpDecls [] catch _ => pure g'
      else pure g'
    -- EC's order: the oracles' judgments, then the code before the calls
    let isOracle (g' : MVarId) : TacticM Bool := return (← g'.getTag) == `oracle
    setGoals ((← gs.filterM isOracle) ++ (← gs.filterM fun g' => return !(← isOracle g')))

end GaudisCrypt
