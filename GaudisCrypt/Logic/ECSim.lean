import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.Inline
import GaudisCrypt.Logic.EqualOutside
import GaudisCrypt.Syntax.CloneRegistry

/-!
# EasyCrypt's `inline*` and `sim`

    stmt_inline*     -- EC's `inline*`: every call whose callee is spelled out, on both sides
    stmt_inline*{i}  -- … on side `i`
    phoare_inline*, hoare_inline*
    sim              -- EC's `sim`, on a relational judgment about two statements

`inline*` inlines call sites until only calls of abstract procedures are left (EC's `inline*`,
which does not inline a declared module either).

`sim` goes backwards over the two statements, computing the relation needed before each step
from the one needed after it, as EC's `sim` does with its sets of equal variables, but with any
relation: deterministic code on either side by wp (`stmt_wp`: copies, dead assignments and
the frame resets of inlined calls disappear into the relation), samplings on both sides
coupled by the identity (`equiv_rnd`), calls of the same procedure on both sides from equal
arguments and globals (`equiv_call`), and conditionals on both sides (`prhlStmt_seq_if_bwd`):
equal guards, each branch's relation found by `sim` on the branches.  Where both statements
are used up, the precondition must imply what is left (`equiv_skip`), closed by `simp_all` if it
can; anything else (a loop, calls of different procedures, a sampling against other code) stops
`sim` with that goal.
-/

namespace GaudisCrypt

section Rules

variable {A Aₜ Aₑ B : ProgramState → ProgramState → Prop} {c₁ c₂ : Getter Bool ProgramState}
  {s₁ s₂ t₁ t₂ e₁ e₂ : Stmt}

/-- **Conditionals on both sides, backwards** (EC's `sim` on `if`s): the branches related from
`Aₜ` and `Aₑ`, and before the conditionals equal guards and the branch's relation.  The branches'
judgments come first, so that their relations are found before the code before them is
processed. -/
theorem prhlStmt_seq_if_bwd (ht : prhlStmt Aₜ t₁ t₂ B) (he : prhlStmt Aₑ e₁ e₂ B)
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ => c₁.get σ₁ = c₂.get σ₂ ∧
      (c₁.get σ₁ = true → Aₜ σ₁ σ₂) ∧ (c₁.get σ₁ = false → Aₑ σ₁ σ₂)) :
    prhlStmt A (.seq s₁ (.ifThenElse c₁ t₁ e₁)) (.seq s₂ (.ifThenElse c₂ t₂ e₂)) B := by
  refine prhlStmt_seq (prhlStmt_if (fun _ _ h => h.1) ?_ ?_) h
  · exact prhlStmt_pre ht fun _ _ h => h.1.2.1 h.2
  · exact prhlStmt_pre he fun _ _ h => h.1.2.2 h.2

/-- **Calls of the same procedure, the states equal outside `L`** (EC's `sim` with `={glob A}`):
a module `M` that does not touch `L`, called on both sides with equal arguments from states equal
outside `L`, returns the same result in states again equal outside `L`, each with its `L` as it
was (`prhlProc_self_equal_outside_module`): after the call, the same globals `g` on both sides
but for each side's own `L`. -/
theorem prhlStmt_seq_call_outside {Ω : Type} (L : Lens Ω VariableAssignment)
    {sig : ProcedureSignature} {M : Module.Proc sig} (hM : FVP.fvP M ≤ (L.footprint)ᶜ)
    {x₁ x₂ : Setter sig.ret ProgramState} {e₁ e₂ : Getter sig.ParamType ProgramState}
    (hpre : prhlStmt A s₁ s₂ fun σ₁ σ₂ => e₁.get σ₁ = e₂.get σ₂ ∧
      L.equal_outside σ₁.globals σ₂.globals ∧
      ∀ r g, B (x₁.set r (ProgramState.globalL.set (L.set (L.get σ₁.globals) g) σ₁))
        (x₂.set r (ProgramState.globalL.set (L.set (L.get σ₂.globals) g) σ₂))) :
    prhlStmt A (.seq s₁ (Stmt.call x₁ M.procedure e₁)) (.seq s₂ (Stmt.call x₂ M.procedure e₂)) B := by
  refine prhlStmt_seq (B := fun σ₁ σ₂ => _) ?_ hpre
  intro σ₁ σ₂ ⟨he, hL, hB⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := prhlProc_self_equal_outside_module L M hM
    (fun l₁ l₂ => l₁ = L.get σ₁.globals ∧ l₂ = L.get σ₂.globals)
    (e₁.get σ₁) (e₂.get σ₂) σ₁.globals σ₂.globals ⟨he, hL, rfl, rfl⟩
  refine ⟨μ >>= fun w => pure (((), x₁.set w.1.1 (ProgramState.globalL.set w.1.2 σ₁)),
    ((), x₂.set w.2.1 (ProgramState.globalL.set w.2.2 σ₂))), ?_, ?_, ?_⟩
  · refine SubProbability.marginal_fst_eq fun F => ?_
    rw [SubProbability.expected_map, SubProbability.expected_fst_of_marginal hm1
      (fun r => F ((), x₁.set r.1 (ProgramState.globalL.set r.2 σ₁))),
      programDenotation_call_apply, SubProbability.expected_hbind]
    simp only [expected_pure]
  · refine SubProbability.marginal_snd_eq fun F => ?_
    rw [SubProbability.expected_map, SubProbability.expected_snd_of_marginal hm2
      (fun r => F ((), x₂.set r.1 (ProgramState.globalL.set r.2 σ₂))),
      programDenotation_call_apply, SubProbability.expected_hbind]
    simp only [expected_pure]
  · refine SubProbability.satisfies_bind _ fun w hw => SubProbability.satisfies_pure _ _ ?_
    obtain ⟨hr, ⟨x, hx⟩, h1, h2⟩ := hsat w hw
    have e₁ : w.1.2 = L.set (L.get σ₁.globals) w.1.2 := by rw [← h1, L.get_set]
    have e₂ : w.2.2 = L.set (L.get σ₂.globals) w.1.2 := by
      rw [← hx, ← h2, ← hx, L.set_get]
    simp only
    rw [← hr, e₂]
    conv => arg 1; rw [e₁]
    exact hB _ _

end Rules

/-- States equal outside `L` as an equation: the second is the first with the second's `L`
written (so that `sim`'s implications are about chains of writes, `lensWriteNorm`). -/
theorem Lens.equal_outside_iff_set {Ω : Type} (L : Lens Ω VariableAssignment)
    (g₁ g₂ : VariableAssignment) : L.equal_outside g₁ g₂ ↔ L.set (L.get g₂) g₁ = g₂ := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [L.set_get]
  · exact fun h => ⟨L.get g₂, h⟩

namespace ECSim

open Lean Meta

/-- A write `X.set v s` through a lens `X` (`Setter.set (Lens.toSetter X) v s`): `(X, v, s)`. -/
def lensWrite? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``Setter.set 5 then
    let S := e.getArg! 2
    if S.isAppOfArity ``Lens.toSetter 3 then some (S.getArg! 2, e.getArg! 3, e.getArg! 4)
    else none
  else none

/-- **Chains of writes in normal form** (EC's memory: what a run of assignments leaves): two
writes of the same lens are one (`Setter.set_set`), two writes of disjoint lenses
(`Lens.Disjoint`, by instance search) in a fixed order (`Expr.lt` of the lenses), swapped by
`Lens.Disjoint.commute` when out of order.  Two chains of writes on the same state are equal
once in normal form exactly when they write the same values to the same lenses. -/
simproc_decl lensWriteNorm (Setter.set _ _ (Setter.set _ _ _)) := fun e => do
  let some (X, v, s) := lensWrite? e | return .continue
  let some (Y, w, t) := lensWrite? s | return .continue
  if X == Y then
    -- `X.set v (X.set w t) = X.set v t`
    let pf ← mkAppM ``Setter.set_set #[e.getArg! 2, t, w, v]
    return .visit { expr := mkAppN e.getAppFn ((e.getAppArgs).set! 4 t), proof? := pf }
  unless Y.lt X do return .continue
  let some inst ← (do
      let ty ← mkAppM ``Lens.Disjoint #[X, Y]
      try some <$> synthInstance ty catch _ => pure none) | return .continue
  -- `X.set v (Y.set w t) = Y.set w (X.set v t)`
  let pf ← mkAppOptM ``Lens.Disjoint.commute
    #[none, none, none, X, Y, inst, t, v, w]
  let rhs := (← instantiateMVars (← inferType pf)).appArg!
  return .visit { expr := rhs, proof? := pf }

end ECSim

namespace ECSim

open Lean Meta Elab Tactic PRHLWp

/-- EC's `inline*` on side `side?` of the goal `g` (a registered judgment): call sites inlined
(`Flatten.judgmentInline`) until every one left fails (an abstract procedure). -/
def inlineAll (g : MVarId) (side? : Option Nat) : MetaM MVarId := do
  let mut g := g
  let mut k := 0
  for _ in [0:500] do
    let (d, ty) ← Judgment.descOf g side?
    let n ← Flatten.countCallSites (ty.getArg! d.stmtArg)
    if k ≥ n then break
    let s ← saveState
    try g ← Flatten.judgmentInline k g side?
    catch _ =>
      s.restore
      k := k + 1
  return g

/-- `inlineAll` on both sides of a relational judgment, or on the one statement. -/
def inlineAllSides (g : MVarId) (side? : Option Nat) : MetaM MVarId := do
  let (descs, _) ← Judgment.descsOf g
  if side?.isNone && descs.size == 2 then
    inlineAll (← inlineAll g (some 1)) (some 2)
  else inlineAll g side?

/-- The kind of the last statement of `s`: `skip`, a conditional, a call, a sampling, or other. -/
inductive Last | skip | cond | call | sample | other
  deriving BEq

/-- The last statement of the right-nested `s` (after `stripLets`). -/
partial def lastOf (s : Lean.Expr) : Lean.Expr :=
  let s := stripLets s
  if s.isAppOf ``StmtWithHoles.seq then
    let l := lastOf (s.getArg! 2)
    if (stripLets l).isAppOf ``StmtWithHoles.skip then lastOf (s.getArg! 1) else l
  else s

/-- The kind of the last statement of `s`. -/
def lastKind (s : Lean.Expr) : MetaM Last := do
  let l := stripLets (lastOf s)
  if l.isAppOf ``StmtWithHoles.skip then return .skip
  if l.isAppOf ``StmtWithHoles.ifThenElse then return .cond
  if l.isAppOf ``StmtWithHoles.call' || l.isAppOf ``Stmt.call || l.isAppOf ``StmtWithHoles.call
    then return .call
  if l.isAppOf ``StmtWithHoles.sample then return .sample
  -- a call spelled through a definition
  if let some l' ← unfoldDefinition? l then
    if l'.isAppOf ``StmtWithHoles.call' then return .call
  return .other

/-- Close `∀ …, A → B` (what `equiv_skip` leaves) by `simp_all`, if it can. -/
def closeImp (g : MVarId) : TacticM (List MVarId) := do
  let s ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| first
      | (intros; subst_vars; simp_all; done)
      | (intros; subst_vars; simp_all [lensWriteNorm]; done)
      | (intros
         -- states equal outside a frame: an equation of chains of writes
         simp only [Lens.equal_outside_iff_set] at *
         simp_all [Lens.set_get, Lens.get_of_disjoint_set, lensWriteNorm]; done)
      | (intros
         -- … with the same conditional writes on both sides, once the hypotheses are substituted
         simp only [Lens.equal_outside_iff_set] at *
         casesm* _ ∧ _
         subst_vars
         split_ifs <;> simp_all [Lens.set_get, Lens.get_of_disjoint_set, lensWriteNorm]; done)
      | (intros; simp_all [Setter.throwaway, ProgramState.globalL, lensWriteNorm]; done)
      | (intros
         -- states agreeing on `glob A` and some variables (EC's `={glob A, x}`, the invariant
         -- `globInvF` of an abstract call): `glob A` past the writes outside it (`fp_disjoint`),
         -- the writes read through
         simp only [globInvF, Prod.mk.injEq] at *
         (try simp (disch := fp_disjoint) only [touched_set_of_le_compl])
         simp_all (config := { contextual := true }) [Lens.set_get, Lens.get_of_disjoint_set,
           Setter.throwaway, ProgramState.globalL]
         done)
      | (intros
         -- … the variables' equations substituted first, the conditional writes split
         simp only [globInvF, Prod.mk.injEq] at *
         casesm* _ ∧ _
         (try split_ifs) <;> (try simp (disch := fp_disjoint) only [touched_set_of_le_compl]) <;>
           simp_all (config := { contextual := true }) [Lens.set_get, Lens.get_of_disjoint_set,
             Setter.throwaway, ProgramState.globalL]
         done))) g
    if gs.isEmpty then return [] else s.restore; return [g]
  catch _ => s.restore; return [g]

/-- Run the tactic `stx` on `g`, the goals it leaves. -/
def runOn (g : MVarId) (stx : TSyntax `tactic) : TacticM (List MVarId) := evalTacticAt stx g

/-- EC's `sim` on the relational goal `g`, backwards (see the module docstring); the goals left.
`open?`: the precondition is a metavariable to be found (a branch of a conditional), assigned the
relation left where the statements are used up. -/
partial def sim (g : MVarId) (frame? : Option Lean.Expr := none) (fuel : Nat := 400) :
    TacticM (List MVarId) := do
  if fuel == 0 then return [g]
  -- the deterministic code at the end of both sides
  let g ← Judgment.wpDet g none
  let ty ← prhlGoal g "sim"
  let k₁ ← lastKind (ty.getArg! 1)
  let k₂ ← lastKind (ty.getArg! 2)
  match k₁, k₂ with
  | .skip, .skip =>
    -- both used up: an open precondition is what is left, else the implication
    let pre ← instantiateMVars (ty.getArg! 0)
    if pre.getAppFn.isMVar then
      let ty' ← g.getType
      let post := (← instantiateMVars ty').getArg! 3
      unless ← isDefEq pre post do return [g]
      let gs ← applyLemma ``prhlStmt_skip g
      for h in gs do
        let _ ← evalTacticAt (← `(tactic| exact fun _ _ h => h)) h
      return []
    let g ← equivSkip g
    closeImp g
  | .cond, .cond =>
    let g ← HoareSplit.hoareSplit 1 g
    -- by hand, not `applyLemma`: the branches' relations `Aₜ`, `Aₑ` stay ordinary metavariables,
    -- for the branches' `sim` to assign
    let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_if_bwd
    let cTy ← inferType c
    let names := cTy.getForallBinderNames
    let (ms, _, concl) ← forallMetaTelescope cTy
    unless ← isDefEq concl (← g.getType) do return [g]
    let arg (n : Name) : TacticM MVarId := do
      let some i := names.findIdx? (· == n) | throwError "sim: no argument `{n}`"
      let m := ms[i]!.mvarId!
      m.setKind .syntheticOpaque
      return m
    let ht ← arg `ht
    let he ← arg `he
    let h ← arg `h
    g.assign (mkAppN c ms)
    let rt ← sim ht frame? (fuel - 1)
    let re ← sim he frame? (fuel - 1)
    let h ← Judgment.simpArg h 3 relSimpDecls []
    return rt ++ re ++ (← sim h frame? (fuel - 1))
  | .call, .call =>
    -- with a frame: the call rule for states equal outside it, the callee's disjointness from
    -- it by `fp_disjoint`
    if let some L := frame? then
      let s ← saveState
      try
        let g ← HoareSplit.hoareSplit 1 g
        let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_call_outside
        let cTy ← inferType c
        let names := cTy.getForallBinderNames
        let (ms, _, concl) ← forallMetaTelescope cTy
        let some iL := names.findIdx? (· == `L) | throwError "sim: no `L`"
        unless ← isDefEq ms[iL]! L do throwError "sim: the frame does not fit"
        unless ← isDefEq concl (← g.getType) do throwError "sim: not the frame's call rule"
        g.assign (mkAppN c ms)
        let some iM := names.findIdx? (· == `hM) | throwError "sim: no `hM`"
        let some ip := names.findIdx? (· == `hpre) | throwError "sim: no `hpre`"
        let hM := ms[iM]!.mvarId!
        let [] ← runOn hM (← `(tactic| ((try simp only [Footprint.lens_pair]); fp_disjoint)))
          | throwError "sim: the callee touches the frame"
        let hp := ms[ip]!.mvarId!
        hp.setKind .syntheticOpaque
        return ← sim (← Judgment.simpArg hp 3 relSimpDecls []) frame? (fuel - 1)
      catch _ => s.restore
    let s ← saveState
    try
      -- calls of procedures spelled differently (an abstract procedure with oracles that are
      -- the same once unfolded, `A(Bounder(FM(C,P)))` and `A(Bounder(FInit(C(P))))`): their
      -- equality by `simp` (the modules' `apply_simp` lemmas), then `rfl`
      let gs ← runOn g (← `(tactic| equiv_call))
      -- the callees' equality within a budget: oracles that differ (`A(Bounder(FInit(RO)))`,
      -- `A(Bounder(RO))`) fail it, and are left to EC's `call (_: ={…})`
      let gs ← gs.filterMapM fun h => do
        unless (← h.getTag).eraseMacroScopes == `callee do return some h
        let s ← saveState
        let ok ← tryCatchRuntimeEx
          (withCurrHeartbeats <|
            withTheReader Core.Context (fun c => { c with maxHeartbeats := 50000 * 1000 }) do
              let rest ← runOn h (← `(tactic| first | (simp; rfl) | rfl))
              pure rest.isEmpty)
          (fun _ => pure false)
        unless ok do s.restore; throwError "sim: the callees differ"
        return none
      match gs with
      | [g'] => sim g' frame? (fuel - 1)
      | _ => return gs
    catch _ => s.restore; return [g]
  | .sample, .sample =>
    let s ← saveState
    try
      let gs ← runOn g (← `(tactic| equiv_rnd))
      match gs with
      | [g'] => sim g' frame? (fuel - 1)
      | _ => return gs
    catch _ => s.restore; return [g]
  | _, _ => return [g]

end ECSim

open Lean Elab Tactic ECSim in
/-- **EC's `inline*`** on a statement judgment, on both sides of a relational one or on side `i`
with `stmt_inline*{i}`. -/
-- two tokens: `stmt_inline*` would be read as `stmt_inline` and `*`
elab "stmt_inline" "*" s:(Judgment.judgmentSide)? : tactic =>
  liftMetaTactic1 fun g => some <$> inlineAllSides g (Judgment.sideOf? s)

open Lean Elab Tactic ECSim in
/-- **EC's `inline*`** on a `phoare` statement judgment. -/
elab "phoare_inline" "*" : tactic => liftMetaTactic1 fun g => some <$> inlineAllSides g none

open Lean Elab Tactic ECSim in
/-- **EC's `inline*`** on a Hoare triple about a statement. -/
elab "hoare_inline" "*" : tactic => liftMetaTactic1 fun g => some <$> inlineAllSides g none

open Lean Elab Tactic ECSim in
/-- **EC's `sim`**: see the module docstring. -/
elab "sim" : tactic => do
  let g ← getMainGoal
  let gs ← sim g
  replaceMainGoal gs

open Lean Meta Elab Tactic ECSim PRHLWp in
/-- **EC's `sim n₁ n₂`**: `sim` on the code after the first `n₁` statements of the left side and
the first `n₂` of the right; the goal left is the code before, its postcondition what `sim` needs
(the relation between the two parts is open, for `sim` to compute). -/
elab "sim" ppSpace n₁:num ppSpace n₂:num : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← prhlGoal g "sim"
  let l₁ ← HoareSplit.seqLength (ty.getArg! 1)
  let l₂ ← HoareSplit.seqLength (ty.getArg! 2)
  unless n₁.getNat ≤ l₁ && n₂.getNat ≤ l₂ do
    throwError "sim: the sides have {l₁} and {l₂} statements"
  let g ← HoareSplit.hoareSplit (l₁ - n₁.getNat) g (some 1)
  let g ← HoareSplit.hoareSplit (l₂ - n₂.getNat) g (some 2)
  g.withContext do
    -- `prhlStmt_seq` by hand: its middle relation an ordinary metavariable, for `sim` to assign
    let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq
    let (ms, _, concl) ← forallMetaTelescope (← inferType c)
    unless ← isDefEq concl (← g.getType) do throwError "sim: cannot cut the code"
    g.assign (mkAppN c ms)
    let hAfter := ms[ms.size - 2]!.mvarId!
    let hBefore := ms[ms.size - 1]!.mvarId!
    hAfter.setKind .syntheticOpaque
    hBefore.setKind .syntheticOpaque
    let rest ← sim hAfter
    replaceMainGoal (rest ++ [hBefore])

open Lean Elab Tactic ECSim in
/-- **EC's `sim` with a frame**: `sim / x₁, …, xₙ`, the states equal except on the globals `xᵢ`
(EC's `={glob A}`: variables the calls of the same procedure do not touch, written by one side
only or at different times), calls of the same procedure by `prhlStmt_seq_call_outside`. -/
elab "sim" " / " xs:term,+ : tactic => withMainContext do
  let xs := xs.getElems
  let some last := xs.back? | throwError "sim: a frame"
  let L ← (xs.pop).foldrM (fun x acc => `(Lens.pair $x $acc)) last
  let Le ← Term.elabTerm L none
  Term.synthesizeSyntheticMVarsNoPostponing
  let g ← getMainGoal
  -- the clone's names as the code spells them (`SRO.RO.m` ↦ `SecureRO.RO.m`)
  let gs ← sim g (some (← unfoldCloneAliases (← instantiateMVars Le)))
  replaceMainGoal gs

end GaudisCrypt
