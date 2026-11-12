import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.PHoareWp
import GaudisCrypt.Logic.GlobWrites

/-!
# EasyCrypt's `auto` and `rnd` steps for `hoare` and `phoare`

    phoare_auto, hoare_auto   -- EC's `auto`: wp over the code back to the last call, then `skip`

Our `phoare` is computed by wp, samplings included (exact averages), so EC's `rnd` steps on a
`phoare` goal become, once `phoare_auto` has gone through the code, steps on an expectation
`d.expected f ≤ r` left by a sampling:

    rnd_pred1 v    -- EC's `rnd (pred1 v)`: `f a ≤ [v = a]`, bounded by `d {v}`
    rnd_bound      -- EC's `rnd` with a lossless distribution: `f a ≤ r` for every `a`
    rnd_null       -- EC's `hoare`: `f` is `0` on the support, whatever the bound

Each leaves the pointwise goal (the obligation EC's `auto` would leave after the step).
-/

namespace GaudisCrypt

namespace SubProbability

variable {α : Type} {d : SubProbability α} {f : α → ENNReal} {r : ENNReal}

/-- EC's `rnd (pred1 v)` on an upper bound: an expectation below the indicator of `v` is at most
the mass of `v`. -/
theorem expected_le_of_le_pred1 (v : α) (h : ∀ a, f a ≤ indicatorE (v = a))
    (hv : d.1 {v} ≤ r) : d.expected f ≤ r := by
  refine le_trans ?_ hv
  calc d.expected f ≤ d.expected (fun a => indicatorE (v = a)) := by
        rw [SubProbability.expected_eq_tsum, SubProbability.expected_eq_tsum]
        exact ENNReal.tsum_le_tsum fun a => by gcongr; exact h a
    _ ≤ d.1 {v} := by
        rw [SubProbability.expected_eq_tsum,
          tsum_eq_single v (fun a ha => by simp [indicatorE, Ne.symm ha])]
        simp [indicatorE]

/-- EC's `rnd` on a lossless distribution: a pointwise bound is a bound of the expectation (the
total mass is at most `1`). -/
theorem expected_le_of_le (h : ∀ a, f a ≤ r) : d.expected f ≤ r := by
  calc d.expected f ≤ d.expected (fun _ => r) := by
        rw [SubProbability.expected_eq_tsum, SubProbability.expected_eq_tsum]
        exact ENNReal.tsum_le_tsum fun a => by gcongr; exact h a
    _ ≤ r := by
        letI : MeasurableSpace α := ⊤
        change ∫⁻ _, r ∂d.1 ≤ r
        rw [MeasureTheory.lintegral_const]
        calc r * d.1 Set.univ ≤ r * 1 := by gcongr; exact d.2.1
          _ = r := mul_one r

/-- EC's `hoare` (probability `0`): an expectation null on the support is below anything. -/
theorem expected_le_of_null (h : ∀ a ∈ d.support, f a = 0) : d.expected f ≤ r :=
  (le_of_eq (SubProbability.expected_eq_zero_of_support h)).trans bot_le

end SubProbability

/-- An event's indicator is `1` exactly when the event holds (what a `phoare … = 1` leaves). -/
@[simp] theorem indicatorE_eq_one_iff (Q : Prop) : indicatorE Q = 1 ↔ Q := by
  by_cases h : Q <;> simp [indicatorE, h]

/-- Equal on a region `R` (EC's `={glob C}`), so equal on each variable inside it
(`={C.c, C.queries}`, a concrete module's `glob` being its variables). -/
theorem Lens.get_eq_of_touched_getter_eq {β m : Type*} (x : Lens β m) {R : Footprint m}
    (hx : x.footprint ≤ R) {σ σ' : m} (h : R.touched_getter.get σ = R.touched_getter.get σ') :
    x.get σ = x.get σ' :=
  (Lens.footprint_touched_getter_eq_iff x σ σ').1 (Footprint.touched_getter_eq_of_le hx h)

namespace ECAuto

open Lean Meta Elab Tactic in
/-- **EC's `={glob C}` as the equalities of `C`'s variables**: for each hypothesis
`R.touched_getter.get a = R.touched_getter.get b`, the hypotheses `x.get a = x.get b` for the
variables `x` read at `a` or `b` (in the goal or a hypothesis) that lie inside `R`: `R` a region of
variables among which `x` is (`fp_le`), or a concrete module's footprint and the module writes `x`
(`fp_writes`). -/
def globReads (g : MVarId) : TacticM MVarId := g.withContext do
  let lctx ← getLCtx
  -- the regions kept equal
  let mut eqs : Array (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    unless l.isAppOfArity ``Getter.get 4 && r.isAppOfArity ``Getter.get 4 do continue
    let (G, G') := (l.getArg! 2, r.getArg! 2)
    unless G.isAppOfArity ``Footprint.touched_getter 2 && G == G' do continue
    eqs := eqs.push (d.toExpr, G.appArg!, l.getArg! 3, r.getArg! 3)
  if eqs.isEmpty then return g
  -- the variables read
  let mut texts : Array Lean.Expr := #[← instantiateMVars (← g.getType)]
  for d in lctx do
    unless d.isImplementationDetail do texts := texts.push (← instantiateMVars d.type)
  let mut g := g
  for (h, R, a, b) in eqs do
    let xs ← IO.mkRef (#[] : Array Lean.Expr)
    for t in texts do
      Meta.forEachExpr t fun e => do
        if e.isAppOfArity ``Getter.get 4 && (e.getArg! 2).isAppOfArity ``Lens.toGetter 3 then
          let st := e.getArg! 3
          let x := (e.getArg! 2).appArg!
          if (st == a || st == b) && !x.hasLooseBVars &&
              !(← xs.get).contains x then
            xs.modify (·.push x)
    for x in ← xs.get do
      let s ← saveState
      -- `x` inside `R`: a region of variables among which `x` is (`fp_le`), or a concrete
      -- module's that writes `x` (`fp_writes`)
      let viaLe : TacticM Lean.Expr := do
        let hle ← mkFreshExprSyntheticOpaqueMVar
          (← mkAppM ``LE.le #[← mkAppM ``Lens.footprint #[x], R])
        let [] ← Tactic.run hle.mvarId! (evalTactic (← `(tactic| fp_le))) | failure
        mkAppM ``Lens.get_eq_of_touched_getter_eq #[x, ← instantiateMVars hle, h]
      let viaWrites : TacticM Lean.Expr := do
        let hw ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Footprint.HasWrites #[R, x])
        GlobWrites.goModule hw.mvarId!
        mkAppM ``Lens.get_eq_of_touched_getter_eq_of_hasWrites #[x, ← instantiateMVars hw, h]
      try
        let pf ← try viaLe catch _ => s.restore; viaWrites
        let (_, g') ← (← g.assert `hglob (← inferType pf) pf).intro1P
        g := g'
      catch _ => s.restore
  return g

open Lean Meta Elab Tactic

/-- EC's `auto` on the statement judgment `g` (a registered one): wp over the statements from the
end (`Judgment.wpOne`: deterministic code, samplings, conditionals) until a call or `skip`. -/
def wpAll (g : MVarId) : MetaM MVarId := do
  let mut g := g
  for _ in [0:1000] do
    let (d, ty) ← Judgment.descOf g none
    let st := ty.getArg! d.stmtArg
    let k ← ECSim.lastKind st
    if k == .skip || k == .call then break
    let s ← saveState
    try g ← Judgment.wpOne g none
    catch _ =>
      s.restore
      break
  return g

/-- The precondition (argument `0`) with its reads of pairs of globals taken apart
(`(§(Lens.pair X Y)).1` is `§X`), so that `skip` generalizes the reads to plain variables (as
`fel`'s view of several variables reads them). -/
def splitPairReads (g : MVarId) : MetaM MVarId := do
  let s ← saveState
  try Judgment.simpArg g 0 [``Lens.pair, ``eval_lens_global] []
  catch _ => s.restore; return g

/-- `hoare_skip` with the goal beta-reduced first (as `phoare_skip` does), so that the reads are
generalized to plain variables. -/
def hoareSkipGen (g : MVarId) : MetaM MVarId := do
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``hoare_skip_of_imp)
  let [g] := gs | throwError "hoare_auto: `hoare_skip_of_imp` left {gs.length} goals"
  let g ← g.withContext do
    g.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← g.getType)))
  -- the reads through writes first (`sp`'s `∃ v, P (x.set v σ)`): reads of `σ` then, generalized
  -- with the postcondition's (else they stay reads of `σ` unrelated to the generalized values)
  let g ← g.withContext do
    let ty ← instantiateMVars (← g.getType)
    try
      let r ← Judgment.simpWithNames PRHLWp.relSimpDecls [] ty
      applySimpResultToTarget g ty r
    catch _ => pure g
  try TacticMisc.generalizeReads g catch _ => pure g

end ECAuto

open Lean Elab Tactic in
/-- **EC's `={glob C}` as `={C.c, C.queries}`** in a closer: see `ECAuto.globReads`. -/
elab "glob_reads" : tactic => do replaceMainGoal [← ECAuto.globReads (← getMainGoal)]

open Lean Elab Tactic ECAuto in
/-- **EC's `auto`** on a `phoare` statement judgment: wp back to the last call, then `skip` if
the code is used up, the trivial goals (`1 = 1`) closed. -/
elab "phoare_auto" : tactic => do
  liftMetaTactic1 fun g => do return some (← splitPairReads (← wpAll g))
  evalTactic (← `(tactic| try phoare_skip))
  -- what EC's `auto` closes by itself: `1 = 1`, `x ≤ x` under the binders
  evalTactic (← `(tactic| try (intros; first | rfl | exact le_rfl)))

/-- **EC's `auto`** on a relational judgment about statements: `wp`, the samplings on both
sides by `rnd` (with `wp` after each), `skip` when the code is used up, and the trivial goals
closed (`simp_all` only when it closes the goal). -/
macro "equiv_auto" : tactic => `(tactic| (
  (try stmt_wp)
  -- the samplings: coupled when both sides end with one, else each by itself (EC's `auto`
  -- takes a sampling of a lossless distribution on one side)
  (repeat (first
    | (equiv_rnd; try stmt_wp)
    | (equiv_rnd{1}; try stmt_wp)
    | (equiv_rnd{2}; try stmt_wp)))
  (try equiv_skip_ec)
  (try ((try simp_reads); intros; first
    | rfl
    | trivial
    | (simp_all; done)
    | ((try simp only [eval, Evaluatable.eval, decide_eq_true_eq, decide_eq_false_iff_not] at *)
       casesm* _ ∧ _; (try subst_vars); glob_reads; first | assumption | (simp_all; done))))))

open Lean Elab Tactic ECAuto in
/-- **EC's `auto`** on a Hoare triple about a statement (the memories of a side goal
`∀ σ₁, hoare[ … ]` introduced first; the trivial goals closed). -/
elab "hoare_auto" : tactic => do
  -- a side goal `∀ σ₁, hoare[ … ]` (EC's `forall &1`, from a one-sided rule): the memory first
  evalTactic (← `(tactic| intros))
  liftMetaTactic1 fun g => do return some (← splitPairReads (← wpAll g))
  liftMetaTactic1 fun g => do
    let s ← saveState
    try return some (← hoareSkipGen g) catch _ => s.restore; return some g
  -- what EC's `auto` closes by itself
  evalTactic (← `(tactic| try ((try simp_reads); intros; first
    | trivial
    | (simp_all; done)
    | ((try simp only [eval, Evaluatable.eval, decide_eq_true_eq, decide_eq_false_iff_not] at *)
       casesm* _ ∧ _; (try subst_vars); first | assumption | (simp_all; done)))))

-- the variables the steps introduce (`a`, `ha`) are the proof's to name: not hygienic
set_option hygiene false

/-- **EC's `rnd (pred1 v)`** on a goal `d.expected f ≤ r`: the goal `f a ≤ [v = a]` for every
`a` (`a` introduced), then `d {v} ≤ r` unless `le_rfl` closes it. -/
macro "rnd_pred1 " v:term:max : tactic => `(tactic|
  (refine SubProbability.expected_le_of_le_pred1 $v (fun a => ?_) ?_
   rotate_left
   first | exact le_rfl | rotate_right))

/-- **EC's `rnd`** with a lossless distribution, on a goal `d.expected f ≤ r`: the goal
`f a ≤ r` for every `a` (`a` introduced). -/
macro "rnd_bound" : tactic => `(tactic|
  refine SubProbability.expected_le_of_le (fun a => ?_))

/-- **EC's `hoare`** (probability `0`) on a goal `d.expected f ≤ r`: the goal `f a = 0` for every
`a` in the support (`a`, `ha` introduced). -/
macro "rnd_null" : tactic => `(tactic|
  refine SubProbability.expected_le_of_null (fun a ha => ?_))

set_option hygiene true

end GaudisCrypt
