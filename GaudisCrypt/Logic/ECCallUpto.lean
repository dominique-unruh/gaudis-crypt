import GaudisCrypt.Logic.SyntacticFrame
import GaudisCrypt.Logic.PRHLStmt
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.FrameTactics
import GaudisCrypt.Logic.ModuleFootprint

/-!
# EasyCrypt's up-to-bad abstract call `call (_: bad, I, J)` — the rule

    equiv_call (_ : §G1.bcol ∨ §G1.bext, ={C.c, C.queries} ∧ INV …, FMap.dom §C.queries{2} [])

EC's `call (_: bad, I, J)` on `D(O₁).f ~ D(O₂).f` (`D` declared, `O₁`, `O₂` concrete): before
the bad event (on the right) the two runs agree on `glob D`, the results and `I`; after it, only
`J` is kept.  `prhlProc_abstract_call_upto_ec` is `prhlProc_abstract_call_upto_module`
(`Logic/AbstractCallUpto.lean`) with EC's premises:

* per oracle procedure `o`, EC's `equiv[ O₁.o ~ O₂.o : !bad{2} /\ ={arg} /\ I ==>
  if bad{2} then J else ={res} /\ I ]`, `={glob D}` framed syntactically (the oracles' writes keep
  `glob D`, `StmtWithHoles.WritesKeep`);
* EC's right premise `forall &1, phoare[ O₂.o : bad /\ J ==> bad /\ J ] = 1`;
* the left premise as a Hoare triple `J` is kept by `O₁.o` after `bad`;
* `D(O₁)` and `D(O₂)` lossless.

**Deviation** (exception E11 of the SHA-3 port, `notes/SHA3/Exceptions.md`): EC asks the left
oracles lossless only after the bad event (`forall &2, bad{2} => phoare[ O₁.o : J ==> J ] = 1`),
and `D_ll` with them; the rule here asks `D(O₁)`, `D(O₂)` lossless outright (the tactic derives
that from `D_ll` and each oracle's `islossless`), since its coupling after the bad event needs the
adversary's remaining runs lossless.  Every use in the SHA-3 proofs proves the oracles lossless
outright.

**The tactic** `equiv_call (_ : bad, I[, J])` (`bad` unsided, about the right state; `I`, `J`
relational): the global variables the three read become the view `L` (EC's invariants on memories,
here on `L`'s contents), and the goals come in EC's order —
1. `D_ll`'s statement (`∀ (F <: … {-D}) (P <: … {-D}), islossless P.f → … → islossless D(F, P)`,
   the oracles' procedures in EC's order: the last component's first), closed by `exact D_ll`;
2. per oracle procedure, in that order: the equivalence, the left oracle's `islossless`, the right
   one's `phoare[ … : bad ∧ J ==> bad ∧ J ] = 1`, and (the deviation) the right one's
   `islossless`;
3. the code before the calls.
The frame (`={glob D}` kept by the oracles), `L`'s disjointness from `D`, the oracles' countable
arguments and, when `J` does not read the left side, `J`'s preservation on the left are closed.
-/

namespace GaudisCrypt

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

/-- `phoare[ p : A ==> B ] = 1`: `B` holds after every run from `A` (a Hoare triple). -/
theorem hoareProc_of_phoareProc_eq_one {sig : ProcedureSignature}
    {A : sig.ParamType → VariableAssignment → Prop} {p : Procedure sig}
    {B : sig.ret → VariableAssignment → Prop}
    (h : phoareProc A p (fun v g => indicatorE (B v g)) Eq (fun _ _ => 1)) : hoareProc A p B := by
  rw [hoareProc_iff_phoareProc]
  intro a σ hA
  have hle : p.ewp a (fun v g => indicatorE (B v g) + indicatorE (¬ B v g)) σ ≤ 1 := by
    refine (Procedure.ewp_mono _ _ (G := fun _ _ => 1) (fun v g => ?_) _).trans
      (Procedure.ewp_const_le _ _ _ _)
    by_cases hb : B v g <;> simp [indicatorE, hb]
  have h1 : p.ewp a (fun v g => indicatorE (B v g)) σ = 1 := h a σ hA
  rw [Procedure.ewp_add, h1] at hle
  change _ = 0
  exact nonpos_iff_eq_zero.mp
    ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp (by simpa using hle))

open GaudisCrypt.Lib.RO.Instantiate

variable {Ω : Type} (L : Lens Ω VariableAssignment)

open Classical in
/-- **EC's `call (_: bad, I, J)` on an abstract procedure**: see the module docstring. -/
theorem prhlProc_abstract_call_upto_ec {T : Type 1} [IsModule T] {sig : ProcedureSignature}
    {holes : HoleSigs} (D : Module.Arr T (Module.Proc sig)) (ext : T → holes.Instantiation)
    (hD : Module.Representable D ext) (hDL : FVP.fvP D ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (bad : Ω → Prop) (I Q : Ω → Ω → Prop) (O₁ O₂ : T)
    (hll₁ : (Module.app D O₁).procedure.IsLossless)
    (hll₂ : (Module.app D O₂).procedure.IsLossless)
    (hwk₁ : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      StmtWithHoles.WritesKeep (FVP.fvP D).touched_getter.get ((ext O₁).lookup n).body)
    (hwk₂ : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      StmtWithHoles.WritesKeep (FVP.fvP D).touched_getter.get ((ext O₂).lookup n).body)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      prhlProc (fun a₁ g₁ a₂ g₂ => ¬ bad (L.get g₂) ∧ a₁ = a₂ ∧ I (L.get g₁) (L.get g₂))
        ((ext O₁).lookup n) ((ext O₂).lookup n)
        (fun r₁ g₁ r₂ g₂ => if bad (L.get g₂) then Q (L.get g₁) (L.get g₂)
          else r₁ = r₂ ∧ I (L.get g₁) (L.get g₂)))
    (hQ₁ : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (ω₂ : Ω), bad ω₂ →
      hoareProc (fun _ g => Q (L.get g) ω₂) ((ext O₁).lookup n) (fun _ g => Q (L.get g) ω₂))
    (hQ₂ : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (ω₁ : Ω),
      phoareProc (fun _ g => bad (L.get g) ∧ Q ω₁ (L.get g)) ((ext O₂).lookup n)
        (fun _ g => indicatorE (bad (L.get g) ∧ Q ω₁ (L.get g))) Eq (fun _ _ => 1)) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ syncInv L (FVP.fvP D) I bad g₁ g₂)
      (Module.app D O₁).procedure (Module.app D O₂).procedure
      (fun r₁ g₁ r₂ g₂ => badInv L bad Q g₁ g₂ ∨
        (r₁ = r₂ ∧ syncInv L (FVP.fvP D) I bad g₁ g₂)) := by
  refine prhlProc_conseq (prhlProc_abstract_call_upto_module L D ext hD (FVP.fvP D) le_rfl hDL hc
    bad I Q O₁ O₂ hll₁ hll₂ (fun n => prhlProc_upto_of_writesKeep L (hwk₁ n) (hwk₂ n)
      (prhlProc_conseq (horacle n) (fun _ _ _ _ ⟨ha, hI, hb⟩ => ⟨hb, ha, hI⟩)
        (fun _ _ _ _ h => ?_))) hQ₁
    (fun n ω₁ => hoareProc_of_phoareProc_eq_one (hQ₂ n ω₁)))
    (fun _ _ _ _ h => Or.inr h) (fun _ _ _ _ h => h)
  split_ifs at h with hb
  · exact Or.inl ⟨hb, h⟩
  · exact Or.inr ⟨h.1, h.2, hb⟩

end GaudisCrypt

namespace GaudisCrypt.ECCallUpto

open Lean Meta Elab Tactic PRHLWp FelTactic

/-- `§x` without a side ↦ `§x{2}`: EC's `bad` is about the right memory. -/
partial def onRight (stx : Syntax) : MacroM Syntax :=
  stx.replaceM fun s => do
    if s.getKind == ``relEval then return some s
    match s with
    | `(§$x:term) => return some (← `(§$x{2}))
    | _ => return none

/-- A read `eval` at `CurrentState.mk σ` of `x`: `(σ, x)`. -/
def readOf? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``eval 5 then
    let cs := e.getArg! 3
    if cs.isAppOfArity ``CurrentState.mk 1 then some (cs.appArg!, e.getArg! 4) else none
  else none

/-- The conditions `bad`, `I`, `J` (functions of the two states) on the contents of the global
variables they read: the lens `L` of those variables (in order of appearance), its content type
`Ω`, and `bad`, `I`, `J` as predicates on `Ω`. -/
def onGlobals (fs : Array Lean.Expr) :
    TacticM (Lean.Expr × Lean.Expr × Array Lean.Expr) := do
  let ps := mkConst ``ProgramState
  withLocalDeclD `σ₁ ps fun σ₁ => withLocalDeclD `σ₂ ps fun σ₂ => do
    let es ← fs.mapM fun f => do
      zetaReduce (← instantiateMVars (mkApp2 f σ₁ σ₂)).headBeta
    -- the global variables read
    let xsRef ← IO.mkRef (#[] : Array Lean.Expr)
    for e in es do
      Meta.forEachExpr e fun s => do
        if let some (σ, x) := readOf? s then
          if σ == σ₁ || σ == σ₂ then
            unless (← xsRef.get).contains x do xsRef.modify (·.push x)
    let xs ← xsRef.get
    if xs.isEmpty then throwError "equiv_call: the conditions read no global variable"
    let tys ← xs.mapM fun x => do
      let t ← whnfR (← inferType x)
      unless t.isAppOfArity ``Lens 2 && (t.getArg! 1).isConstOf ``VariableAssignment do
        throwError "equiv_call: the conditions read{indentExpr x}\nwhich is not a global variable"
      return t.getArg! 0
    let Ω ← tys.pop.foldrM (fun t acc => mkAppM ``Prod #[t, acc]) tys.back!
    let xsS ← xs.mapM fun x => (Term.exprToSyntax x : TermElabM Term)
    let LS ← xsS.pop.foldrM (fun x acc => `(Lens.pair $x $acc)) xsS.back!
    let L ← Term.elabTermEnsuringType LS (← mkAppM ``Lens #[Ω, mkConst ``VariableAssignment])
    Term.synthesizeSyntheticMVarsNoPostponing
    let L ← instantiateMVars L
    withLocalDeclD `ω₁ Ω fun ω₁ => withLocalDeclD `ω₂ Ω fun ω₂ => do
      let proj (k : Nat) (ω : Lean.Expr) : MetaM Lean.Expr := do
        let mut e := ω
        for _ in [0:k] do e ← mkAppM ``Prod.snd #[e]
        if k + 1 < xs.size then e ← mkAppM ``Prod.fst #[e]
        return e
      let subst (e : Lean.Expr) : MetaM Lean.Expr := do
        let e' ← Meta.transform e (pre := fun s => do
          if let some (σ, x) := readOf? s then
            if let some k := xs.idxOf? x then
              if σ == σ₁ then return .done (← proj k ω₁)
              if σ == σ₂ then return .done (← proj k ω₂)
          return .continue)
        if e'.containsFVar σ₁.fvarId! || e'.containsFVar σ₂.fvarId! then
          throwError "equiv_call: a condition reads the states other than through global \
            variables:{indentExpr e'}"
        return e'
      let preds ← es.mapM fun e => do mkLambdaFVars #[ω₁, ω₂] (← subst e)
      return (L, Ω, preds)


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


/-- Hole `i`'s component and its position in it, for components with `nprocs` procedures. -/
def holeComp (nprocs : Array Nat) (i : Nat) : Nat × Nat := Id.run do
  let mut c := 0
  let mut off := i
  while c < nprocs.size && off ≥ nprocs[c]! do
    off := off - nprocs[c]!
    c := c + 1
  return (c, off)

/-- EC's `D_ll`: `∀ (X₁ : C₁) [Module.Declared X₁ G] …, islossless (in `order`) → islossless
D(X₁, …)`, over the oracles' component module types `Cs`. -/
def llStatement (D G : Lean.Expr) (Cs : Array Lean.Expr) (order : Array Nat) :
    MetaM Lean.Expr := do
  let rec go (j : Nat) (xs : Array Lean.Expr) : MetaM Lean.Expr := do
    if h : j < Cs.size then
      withLocalDecl (Name.mkSimple s!"O{j}") .default Cs[j] fun X => do
        let decl ← mkAppM ``Module.Declared #[X, G]
        withLocalDecl `inst .instImplicit decl fun i => do
          mkForallFVars #[X, i] (← go (j + 1) (xs.push X))
    else
      let mut O := xs.back!
      for X in xs.pop.reverse do O ← mkAppM ``GaudisCrypt.Module.pair #[X, O]
      let ps ← (List.range xs.size).toArray.mapM fun c => procsOf Cs[c]! xs[c]!
      let nprocs := ps.map (·.size)
      let prems ← order.mapM fun i => do
        let (c, off) := holeComp nprocs i
        let pc := ps[c]!
        mkAppM ``Procedure.IsLossless #[pc[off]!]
      let concl ← mkAppM ``Procedure.IsLossless #[← mkAppM ``GaudisCrypt.Module.Proc.procedure
        #[← mkAppM ``GaudisCrypt.Module.app #[D, O]]]
      prems.foldrM (fun p acc => mkArrow p acc) concl
  go 0 #[]

end GaudisCrypt.ECCallUpto

namespace GaudisCrypt

open Lean Meta Elab Tactic PRHLWp FelTactic ECCallUpto

/-- **EC's `call (_: bad, I, J)`**: see the module docstring. -/
syntax (name := equivCallUpto) "equiv_call" " (" "_" " : " term ", " term (", " term)? ")" :
  tactic

elab_rules (kind := equivCallUpto) : tactic
  | `(tactic| equiv_call (_ : $bad, $I $[, $J]?)) => withMainContext do
    let g ← getMainGoal
    let ty0 ← prhlGoal g "equiv_call"
    -- the conditions, as functions of the two states (`bad` on the right)
    let badStx : Term := ⟨← liftMacroM (onRight bad)⟩
    let badF ← elabRelCond ty0 badStx
    let IF ← elabRelCond ty0 I
    let JF ← elabRelCond ty0 (← match J with | some J => pure J | none => `(True))
    let (L, _Ω, preds) ← onGlobals #[badF, IF, JF]
    let badΩ ← withLocalDeclD `ω₁ _Ω fun ω₁ => do
      let b := (mkApp preds[0]! ω₁).headBeta
      if b.hasLooseBVars then throwError "equiv_call: `bad` reads the left state"
      return b
    let g ← HoareSplit.hoareSplit 1 g
    setGoals [g]
    let ty ← instantiateMVars (← g.getType)
    g.withContext do
      let st ← TacticMisc.openStmt (ty.getArg! 1)
      let last ← if st.isAppOfArity ``StmtWithHoles.seq 3 then TacticMisc.openStmt (st.getArg! 2)
        else pure st
      let some callee := last.find? (·.isAppOfArity ``GaudisCrypt.Module.app 6)
        | throwError "equiv_call: no call of an applied module last on the left"
      let T ← inferType (callee.getArg! 5)
      let TS ← Term.exprToSyntax T
      let extS ← `(fun O => (Module.moduleTypeRep $TS).extOf (Module.cast $TS O))
      let LS ← Term.exprToSyntax L
      let badS ← Term.exprToSyntax badΩ
      let IS ← Term.exprToSyntax preds[1]!
      let QS ← Term.exprToSyntax preds[2]!
      evalTactic (← `(tactic| refine prhlStmt_seq_call
          (prhlProc_abstract_call_upto_ec (L := $LS) _ $extS
            (Module.Declared.ecModule _ $extS).representable ?hdisj ?hc $badS $IS $QS _ _
            ?ll₁ ?ll₂ ?wk₁ ?wk₂ ?oracle ?left ?right) ?pre))
      untagGoals
      -- the oracles' procedures, hole by hole, and EC's order of them (the last component first)
      let D := callee.getArg! 4
      let O₁ := callee.getArg! 5
      let comps₁ ← components T O₁
      -- the right oracles, out of the goal about `D(O₂)`'s losslessness
      let some gll₂ ← (← getGoals).findM? (fun g => return (← g.getTag) == `ll₂)
        | throwError "equiv_call: the right oracles not found"
      let some O₂ := ((← instantiateMVars (← gll₂.getType)).find?
          (·.isAppOfArity ``GaudisCrypt.Module.app 6)).map (·.getArg! 5)
        | throwError "equiv_call: the right oracles not found"
      let comps₂ ← components T O₂
      let procs₁ := (← comps₁.mapM fun (C, X) => procsOf C X).flatten
      let procs₂ := (← comps₂.mapM fun (C, X) => procsOf C X).flatten
      -- the same, as `T`'s canonical `ext` reduces to them (`Module.fst`, `Module.snd`)
      let procsFS (O : Lean.Expr) : MetaM (Array Lean.Expr) := do
        return (← (← components T O false).mapM fun (C, X) => procsOf C X).flatten
      let fs₁ ← procsFS O₁
      let fs₂ ← procsFS O₂
      let nprocs ← comps₁.mapM fun (C, X) => return (← procsOf C X).size
      -- hole indices of each component, and EC's order: components reversed
      let mut start := 0
      let mut groups : Array (Array Nat) := #[]
      for n in nprocs do
        groups := groups.push ((List.range n).toArray.map (start + ·))
        start := start + n
      let ecOrder := groups.reverse.flatten
      let k := procs₁.size
      let byTag (t : Name) : TacticM (Option MVarId) := do
        (← getGoals).findM? fun g => return (← g.getTag) == t
      -- side conditions
      closeTagged `hdisj (← `(tactic| ((try simp only [Footprint.lens_pair]); fp_disjoint)))
      let mut done : Array MVarId := #[]
      if let some gc ← byTag `hc then
        for h in ← splitHoles gc k do
          let [] ← evalTacticAt (← `(tactic| first
              | infer_instance
              | (dsimp only [ProcedureSignature.ParamType, typeListToTuple]; infer_instance))) h
            | throwError "equiv_call: an oracle's argument type is not countable"
        done := done.push gc
      for t in [`wk₁, `wk₂] do
        if let some gw ← byTag t then
          let hs ← splitHoles gw k
          for (h, i) in hs.zipIdx do
            let h ← niceGoal h O₁ fs₁[i]! fs₂[i]!
            let rest ← h.withContext do
              setGoals [h]
              liftMetaTactic (writesKeepSplit ·)
              evalTactic (← `(tactic| all_goals first
                | exact fun _ _ => rfl
                | exact fun v σ => touched_set_of_le_compl (by fp_disjoint) v σ.globals))
              getGoals
            unless rest.isEmpty do
              throwError "equiv_call: an oracle writes `glob` of the abstract module"
          done := done.push gw
      -- `J` kept by the left oracles: closed when `J` does not read the left side
      if let some gl ← byTag `left then
        let s ← saveState
        try
          let [] ← evalTacticAt (← `(tactic| (intro _ _ _ _; exact hoareProc_const _ _))) gl
            | throwError "no"
          done := done.push gl
        catch _ => s.restore
      -- the per-oracle goals, in EC's order
      let mut oracleGs : Array MVarId := #[]
      if let some go ← byTag `oracle then
        let hs := (← splitHoles go k).toArray
        for i in ecOrder do
          let h ← niceGoal hs[i]! O₁ fs₁[i]! fs₂[i]!
          h.setTag `oracle
          oracleGs := oracleGs.push h
        done := done.push go
      let mut rightGs : Array MVarId := #[]
      if let some gr ← byTag `right then
        let hs := (← splitHoles gr k).toArray
        for i in ecOrder do
          let [h] ← evalTacticAt (← `(tactic| intro _)) hs[i]! | throwError "equiv_call: right"
          let h ← niceGoal h O₁ fs₁[i]! fs₂[i]!
          h.setTag `right
          rightGs := rightGs.push h
        done := done.push gr
      -- the losslessness of `D(O₁)`, `D(O₂)` from EC's `D_ll` and the oracles' losslessness
      let G ← mkAppM ``Footprint.glob #[← mkAppM ``FVP.fvP #[D]]
      let llOf (p : Lean.Expr) : MetaM Lean.Expr := mkAppM ``Procedure.IsLossless #[p]
      let llL ← ecOrder.mapM fun i => do
        let m ← mkFreshExprSyntheticOpaqueMVar (← llOf procs₁[i]!) `left
        pure (i, m)
      let llR ← ecOrder.mapM fun i => do
        let m ← mkFreshExprSyntheticOpaqueMVar (← llOf procs₂[i]!) `right_ll
        pure (i, m)
      -- `D_ll`'s statement: `∀ (X₁ <: C₁ {-D}) …, islossless …(EC's order) → islossless D(…)`
      let llTy ← llStatement D G (comps₁.map (·.1)) ecOrder
      let llM ← mkFreshExprSyntheticOpaqueMVar llTy `ll
      let declProof (X : Lean.Expr) : TacticM Lean.Expr := do
        let e ← Term.elabTermEnsuringType
          (← `(Module.Declared.mk (by fp_finite) (by fp_disjoint)))
          (← mkAppM ``Module.Declared #[X, G])
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e
      for (tag, comps, lls) in [(`ll₁, comps₁, llL), (`ll₂, comps₂, llR)] do
        if let some gll ← byTag tag then
          let mut args : Array Lean.Expr := #[]
          for (_, X) in comps do
            args := args.push X
            args := args.push (← declProof X)
          args := args ++ lls.map (·.2)
          let pf := mkAppN llM args
          unless ← isDefEq (← gll.getType) (← inferType pf) do
            throwError "equiv_call: the losslessness of the adversary, from `D_ll`'s form"
          gll.assign pf
          done := done.push gll
      -- the code before the calls: its postcondition with the invariants unfolded
      let pre ← byTag `pre
      let pre ← match pre with
        | some p => do
          let [p'] ← evalTacticAt (← `(tactic|
              dsimp only [syncInv, badInv, globInvF, Lens.pair])) p | pure (some p)
          p'.setTag `pre
          pure (some p')
        | none => pure none
      -- EC's order: `D_ll`, then per oracle its judgment, the left oracle's losslessness, the
      -- right one's `phoare`, and (the deviation) the right one's losslessness; then the code
      -- before the calls
      let others ← (← getGoals).filterM fun g => return !done.contains g && some g != pre
      let mut out : Array MVarId := #[llM.mvarId!]
      for j in [0:k] do
        out := out.push oracleGs[j]!
        out := out.push llL[j]!.2.mvarId!
        out := out.push rightGs[j]!
        out := out.push llR[j]!.2.mvarId!
      let others ← others.filterM fun g => return !out.contains g
      setGoals (out.toList ++ others ++ pre.toList)

end GaudisCrypt
