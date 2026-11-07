import GaudisCrypt.Logic.FelTactic
import GaudisCrypt.Logic.PRHLWp

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

open Lean Meta Elab Tactic FelTactic PRHLWp

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
    let (ext, C) ← g.withContext do
      let st ← TacticMisc.openStmt (ty.getArg! 1)
      let last ← if st.isAppOfArity ``StmtWithHoles.seq 3 then TacticMisc.openStmt (st.getArg! 2)
        else pure st
      let (ext, _, C) ← abstractCall last
      return (ext, C)
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
