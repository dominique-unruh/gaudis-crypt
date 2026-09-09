import GaudisCrypt.Language.ModuleExpressionConfluence
import GaudisCrypt.Language.ModuleExpressionNormalization

/-! # Module expressions

Everything about `ModuleExpression.reduce` that rests on confluence
(`ModuleExpressionConfluence.lean`) or on normalization
(`ModuleExpressionNormalization.lean`): `reduce` is idempotent, agrees on convertible terms,
computes a normal form of a well-typed term, and is a congruence for every constructor — plus
the `reduce_simp` tactic built out of those lemmas.

`ModuleExpressionBasics.lean` holds the part of the development that needs neither: the syntax
tree, typing, substitution, reduction, normal forms and the `moduletyping`/`normalmodule`
tactics.  This file is the one downstream modules import. -/

namespace GaudisCrypt

variable [ProgramSpec]

namespace ModuleExpression

theorem multiStepReduction_confluence {m n1 n2 : ModuleExpression}
  (_ : m.MultiStepReduction n1) (_ : m.MultiStepReduction n2)
  (_ : n1.Stuck) (_ : n2.Stuck) :
  n1 = n2 := by
  rename_i h1 h2 s1 s2
  obtain ⟨d, hd1, hd2⟩ := multiStepReduction_confluent h1 h2
  rw [s1.eq_of_multiStepReduction hd1, s2.eq_of_multiStepReduction hd2]

theorem multiStepReduction_terminating {m n} (h : m.MultiStepReduction n) :
    Terminating m ↔ Terminating n := by
  constructor
  · rintro ⟨s, hs, hms⟩
    obtain ⟨d, hsd, hnd⟩ := multiStepReduction_confluent hms h
    exact ⟨d, hs.eq_of_multiStepReduction hsd ▸ hs, hnd⟩
  · rintro ⟨s, hs, hns⟩
    exact ⟨s, hs, h.trans hns⟩

@[simp] theorem reduce_of_stuck {m : ModuleExpression} (h : m.Stuck) : reduce m = m :=
  multiStepReduction_confluence
    (multiStepReduction_reduce h.terminating) .refl (reduce_stuck h.terminating) h

/-- Termination is invariant along equireducibility: each `ReductionStep` preserves it via
    `multiStepReduction_terminating`, and refl/symm/trans closure is immediate. -/
theorem convertible_terminating {m n : ModuleExpression} (h : convertible m n) :
    Terminating m ↔ Terminating n := by
  unfold convertible at h
  induction h with
  | rel x y hxy =>
      exact multiStepReduction_terminating (Relation.ReflTransGen.head hxy .refl)
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem reduce_terminating {m : ModuleExpression} : Terminating m ↔ Terminating (reduce m) := by
  constructor
  · intro h; exact (reduce_stuck h).terminating
  · intro h
    by_contra hm
    exact hm ((convertible_terminating convertible_reduce).mpr h)

/-- Reduction preserves typing. -/
theorem reduce_hasType {m Δ T} (h : m.HasType Δ T) : (reduce m).HasType Δ T :=
  h.preservation_multi (multiStepReduction_reduce h.terminating)

/-- The reduct of a well-typed closed term is closed-normal. -/
theorem reduce_normal {m} (h : m.HasType Δ T) : (reduce m).Normal :=
  Stuck.normal (reduce_stuck h.terminating) (reduce_hasType h)

/-- The reduct of a well-typed closed term is closed-normal. -/
theorem reduce_normalClosed {m T} (h : m.HasType [] T) : (reduce m).NormalClosed :=
  Normal.normalClosed (reduce_normal h) (reduce_hasType h)

theorem reduce_idempotent (m : ModuleExpression) : reduce (reduce m) = reduce m := by
  by_cases h : Terminating m
  · exact reduce_of_stuck (reduce_stuck h)
  · have hnr : ¬Terminating (reduce m) := fun hh =>
      h ((convertible_terminating convertible_reduce).mpr hh)
    exact reduce_eq_of_convertible_not_term (Relation.EqvGen.symm _ _ convertible_reduce) hnr h

/-- A normal term is its own reduct (normal terms are stuck). -/
@[simp] theorem reduce_of_normal {m : ModuleExpression} (h : m.Normal) : reduce m = m :=
  reduce_of_stuck h.stuck

@[simp] theorem reduce_proc {sig} (p : Procedure sig) : reduce (.proc p) = .proc p :=
  reduce_of_stuck Normal.proc.stuck

theorem confluence {m m1 m2 : ModuleExpression}
    (h1 : m.MultiStepReduction m1) (h2 : m.MultiStepReduction m2) : reduce m1 = reduce m2 := by
  by_cases ht : Terminating m1
  · have ht2 : Terminating m2 :=
      (multiStepReduction_terminating h2).mp ((multiStepReduction_terminating h1).mpr ht)
    exact multiStepReduction_confluence
      (h1.trans (multiStepReduction_reduce ht))
      (h2.trans (multiStepReduction_reduce ht2))
      (reduce_stuck ht) (reduce_stuck ht2)
  · have ht2 : ¬ Terminating m2 := fun h =>
      ht ((multiStepReduction_terminating h1).mp ((multiStepReduction_terminating h2).mpr h))
    have h12 : convertible m1 m2 :=
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (convertible_of_multiStep h1))
        (convertible_of_multiStep h2)
    exact reduce_eq_of_convertible_not_term h12 ht ht2

theorem reduce_step {m n : ModuleExpression} (h : m.ReductionStep n) : reduce m = reduce n :=
  confluence .refl (Relation.ReflTransGen.head h .refl)

theorem reduce_convertible {m n : ModuleExpression} (_ : convertible m n) :
  reduce m = reduce n := by
  rename_i h
  unfold convertible at h
  induction h with
  | rel x y hxy => exact reduce_step hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem reduce_multiStepReduction {m n : ModuleExpression} (h : m.MultiStepReduction n) :
    reduce m = reduce n :=
  reduce_convertible (convertible_of_multiStep h)

theorem reduce_convertible_iff {m n : ModuleExpression} :
  convertible m n ↔ reduce m = reduce n := by
  constructor
  · exact reduce_convertible
  · intro h
    exact Relation.EqvGen.trans _ _ _ (h ▸ convertible_reduce)
      (Relation.EqvGen.symm _ _ convertible_reduce)


theorem reduce_beta (body arg : ModuleExpression) :
    reduce (.app (.abs body) arg) = reduce (body.substitute arg) :=
  confluence .refl (Relation.ReflTransGen.head ReductionStep.beta .refl)

theorem reduce_pair_terminating {m1 m2 : ModuleExpression}
    (h1 : Terminating m1) (h2 : Terminating m2) :
    reduce (.pair m1 m2) = .pair (reduce m1) (reduce m2) := by
  have hst : Stuck (.pair (reduce m1) (reduce m2)) :=
    stuck_pair (reduce_stuck h1) (reduce_stuck h2)
  have hred : (ModuleExpression.pair m1 m2).MultiStepReduction (.pair (reduce m1) (reduce m2)) :=
    multiStepReduction_pair_cong (multiStepReduction_reduce h1) (multiStepReduction_reduce h2)
  have hterm : Terminating (.pair m1 m2) := ⟨_, hst, hred⟩
  exact multiStepReduction_confluence
    (multiStepReduction_reduce hterm) hred (reduce_stuck hterm) hst

/-! #### Remaining `reduce` specification lemmas -/

@[simp] theorem reduce_fst (m m' : ModuleExpression) :
    reduce (.fst (.pair m m')) = reduce m := reduce_step .fstPair

@[simp] theorem reduce_snd (m m' : ModuleExpression) :
    reduce (.snd (.pair m m')) = reduce m' := reduce_step .sndPair

theorem reduce_fst_cong (m m' : ModuleExpression) :
    reduce m = reduce m' → reduce (.fst m) = reduce (.fst m') := by
  rw [← reduce_convertible_iff, ← reduce_convertible_iff]
  intro h
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (.fst hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem reduce_snd_cong (m m' : ModuleExpression) :
    reduce m = reduce m' → reduce (.snd m) = reduce (.snd m') := by
  rw [← reduce_convertible_iff, ← reduce_convertible_iff]
  intro h
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (.snd hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- Congruence form for `.pair`: combines two independently-computed simplifications
    `reduce a = a'` / `reduce b = b'` (however they were obtained — `a'`/`b'` need not
    themselves be fully reduced) into one for the surrounding `.pair`. Proved directly via
    `convertible`: `pairL`/`pairR` lift `convertible_reduce` through `.pair` on each side, and
    `reduce_convertible_iff` turns the resulting `convertible` witness back into a `reduce`
    equation. -/
theorem reduce_pair_cong {a a' b b' : ModuleExpression} (ha : reduce a = a') (hb : reduce b = b') :
    reduce (.pair a b) = reduce (.pair a' b') := by
  have congL : ∀ {a b c : ModuleExpression}, convertible a b →
      convertible (.pair a c) (.pair b c) := by
    intro a b c h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ (.pairL hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have congR : ∀ {a b c : ModuleExpression}, convertible b c →
      convertible (.pair a b) (.pair a c) := by
    intro a b c h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ (.pairR hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  rw [← reduce_convertible_iff]
  exact Relation.EqvGen.trans _ _ _
    (congL (ha ▸ convertible_reduce)) (congR (hb ▸ convertible_reduce))

/-- Congruence form for `.app`, matching `reduce_pair_cong`. -/
theorem reduce_app_cong {a a' b b' : ModuleExpression} (ha : reduce a = a') (hb : reduce b = b') :
    reduce (.app a b) = reduce (.app a' b') := by
  have congL : ∀ {a b c : ModuleExpression}, convertible a b →
      convertible (.app a c) (.app b c) := by
    intro a b c h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ (.appL hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have congR : ∀ {a b c : ModuleExpression}, convertible b c →
      convertible (.app a b) (.app a c) := by
    intro a b c h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ (.appR hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  rw [← reduce_convertible_iff]
  exact Relation.EqvGen.trans _ _ _
    (congL (ha ▸ convertible_reduce)) (congR (hb ▸ convertible_reduce))

/-! One-sided congruences.  `reduce_pair_cong`/`reduce_app_cong` replace *both* components, so
simplifying only one of them means proving `reduce b = b'` for the other by `rfl`, i.e. putting
`reduce b` there — a `reduce` around a component that had none.  These leave the other component
exactly as it is.  (The hypothesis `reduce a = a'` already forces `a'` to be `reduce a`, hence
`reduce a' = a'` by idempotence, which is what makes the untouched side go through.) -/

theorem reduce_pair_cong_left {a a' b : ModuleExpression} (ha : reduce a = a') :
    reduce (.pair a b) = reduce (.pair a' b) :=
  have ha' : reduce a' = a' := ha ▸ reduce_idempotent a
  (reduce_pair_cong ha rfl).trans (reduce_pair_cong ha' rfl).symm

theorem reduce_pair_cong_right {a b b' : ModuleExpression} (hb : reduce b = b') :
    reduce (.pair a b) = reduce (.pair a b') :=
  have hb' : reduce b' = b' := hb ▸ reduce_idempotent b
  (reduce_pair_cong rfl hb).trans (reduce_pair_cong rfl hb').symm

theorem reduce_app_cong_left {a a' b : ModuleExpression} (ha : reduce a = a') :
    reduce (.app a b) = reduce (.app a' b) :=
  have ha' : reduce a' = a' := ha ▸ reduce_idempotent a
  (reduce_app_cong ha rfl).trans (reduce_app_cong ha' rfl).symm

theorem reduce_app_cong_right {a b b' : ModuleExpression} (hb : reduce b = b') :
    reduce (.app a b) = reduce (.app a b') :=
  have hb' : reduce b' = b' := hb ▸ reduce_idempotent b
  (reduce_app_cong rfl hb).trans (reduce_app_cong rfl hb').symm

/-- Congruence form for `.abs`, matching `reduce_pair_cong`/`reduce_app_cong`. -/
theorem reduce_abs_cong {a a' : ModuleExpression} (ha : reduce a = a') :
    reduce (.abs a) = reduce (.abs a') := by
  have cong : ∀ {a b : ModuleExpression}, convertible a b → convertible (.abs a) (.abs b) := by
    intro a b h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ (.lam hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  rw [← reduce_convertible_iff]
  exact cong (ha ▸ convertible_reduce)

/-! #### Stripping an inner `reduce`

`reduce` only cares about its argument up to convertibility, so a subterm that is already a
`reduce` can be replaced by what it reduces (`reduce_idempotent` on both sides of the matching
`_cong` lemma).  This is what makes the `.reduce`s that `toModule` leaves behind disappear when a
composite expression is reduced — the `moduleApply` tactic (`GaudisCrypt/Language/Syntax2.lean`)
uses all six of them to bring the two sides of an `X.apply_simp` goal into the same shape. -/

theorem reduce_app_left (f x : ModuleExpression) :
    (ModuleExpression.app f.reduce x).reduce = (ModuleExpression.app f x).reduce := by
  rw [(reduce_app_cong rfl rfl : reduce (.app f x) = reduce (.app f.reduce x.reduce)),
    (reduce_app_cong rfl rfl :
      reduce (.app f.reduce x) = reduce (.app f.reduce.reduce x.reduce)), reduce_idempotent]

theorem reduce_app_right (f x : ModuleExpression) :
    (ModuleExpression.app f x.reduce).reduce = (ModuleExpression.app f x).reduce := by
  rw [(reduce_app_cong rfl rfl : reduce (.app f x) = reduce (.app f.reduce x.reduce)),
    (reduce_app_cong rfl rfl :
      reduce (.app f x.reduce) = reduce (.app f.reduce x.reduce.reduce)), reduce_idempotent]

theorem reduce_pair_left (a b : ModuleExpression) :
    (ModuleExpression.pair a.reduce b).reduce = (ModuleExpression.pair a b).reduce :=
  (reduce_pair_cong_left (a := a) (b := b) rfl).symm

theorem reduce_pair_right (a b : ModuleExpression) :
    (ModuleExpression.pair a b.reduce).reduce = (ModuleExpression.pair a b).reduce :=
  (reduce_pair_cong_right (a := a) (b := b) rfl).symm

theorem reduce_fst_inner (m : ModuleExpression) :
    (ModuleExpression.fst m.reduce).reduce = (ModuleExpression.fst m).reduce :=
  reduce_fst_cong _ _ (reduce_idempotent m)

theorem reduce_snd_inner (m : ModuleExpression) :
    (ModuleExpression.snd m.reduce).reduce = (ModuleExpression.snd m).reduce :=
  reduce_snd_cong _ _ (reduce_idempotent m)

end ModuleExpression

/-! # Tactics -/

/-! ## `reduce_simp` -/

private lemma reduce_eq_guard_aux1 m n : ModuleExpression.reduce m = ModuleExpression.reduce n → ModuleExpression.reduce m = ModuleExpression.reduce n := by intro; assumption
private lemma reduce_eq_guard_aux2 m n : ModuleExpression.reduce m = n →
    ModuleExpression.reduce m = ModuleExpression.reduce n := by
  -- `n` *is* `reduce m`, so reducing it again changes nothing
  intro h
  rw [← h, ModuleExpression.reduce_idempotent]


open Lean Elab Tactic Meta in
/-- `reduceSimpHead` takes a goal of the form
`reduce M = reduce ?m` or `reduce M = ?m` and solves it by instantiating the rhs as `reduce M'`
where M' is the result of applying a single reduction step.

Rules of the form `reduce X = reduce Y` or `reduce X = Y`
or `convertible X Y` or `MultiStepReduction X Y` or `Step X Y`
in the context are also used as reduction steps.

It fails when no step applies.  In particular a term that is already normal is *not* its business:
it never uses `reduce_of_normal`, so it neither succeeds without reducing nor leaves a `reduce`
around a component it did not touch.  Collapsing the `reduce` of a normal term is the second rule
of `reduceSimpProcImpl` instead.

A plain `TacticM` function, not a `syntax`/`macro_rules` pair, so it adds nothing to the tactic
grammar. The head-step alternatives stay a `first | …` quotation run via `evalTactic`; the
congruence rules — the only recursive part — are tried in order by hand, each followed by a
recursive call, with backtracking between them. Invoke it from a proof with `run_tac`.
-/
partial def reduceSimpHead : TacticM Unit := do
  let headStep : TacticM Unit := do
    evalTactic (← `(tactic|
        (first
         | (apply ModuleExpression.reduce_beta;
            try simp only [ModuleExpression.substitute, ModuleExpression.substituteSimultaneously,
                           ModuleExpression.variableSubstitution, ModuleExpression.liftSubst])
         | apply ModuleExpression.reduce_fst
         | apply ModuleExpression.reduce_snd
         | (apply ModuleExpression.reduce_step; assumption)
         | (apply ModuleExpression.reduce_multiStepReduction; assumption)
         | (apply ModuleExpression.reduce_convertible; assumption)
         | (apply reduce_eq_guard_aux1; assumption)
         | (apply reduce_eq_guard_aux2; assumption))))
  let congRules : List Name :=
    [``ModuleExpression.reduce_pair_cong_left, ``ModuleExpression.reduce_pair_cong_right,
     ``ModuleExpression.reduce_app_cong_left, ``ModuleExpression.reduce_app_cong_right,
     ``ModuleExpression.reduce_abs_cong, ``ModuleExpression.reduce_fst_cong,
     ``ModuleExpression.reduce_snd_cong]
  let congStep : TacticM Unit := do
    let saved ← Elab.Tactic.saveState
    for rule in congRules do
      try
        evalTactic (← `(tactic| apply $(mkIdent rule)))
        reduceSimpHead
        return
      catch _ =>
        saved.restore
    throwError "reduceSimpHead: no reduction step applies"
  try headStep
  catch _ => congStep



open Lean Meta Simp in
/-- Solve a fresh `e = ?m` goal with `tac` and report the outcome as a `Simp.Result`, or `none` if
    `tac` fails or leaves the goal open.  `?m`, which `tac` assigns, is the replacement term. -/
private def reduceSimpRun (e : Lean.Expr) (tac : Elab.Tactic.TacticM Unit) :
    SimpM (Option Simp.Result) := do
  try
    let mTarget ← mkFreshExprMVar (← inferType e)
    let goalMVar ← mkFreshExprMVar (← mkEq e mTarget)
    let remaining ← Elab.Tactic.run goalMVar.mvarId! tac |>.run'
    if !remaining.isEmpty then
      return none
    return some { expr := ← instantiateMVars mTarget, proof? := some (← instantiateMVars goalMVar) }
  catch _ =>
    return none

open Lean Meta Simp in
/-- The rewrite `reduce_simp` performs at a `ModuleExpression.reduce x` subterm: one reduction
    step via `reduceSimpHead`, or — when nothing reduces — collapsing the `reduce` outright via
    `reduce_of_normal`, whose `Normal x` side condition `normalmodule` discharges.  The two are
    complementary: `reduceSimpHead` only ever reports a genuine step (it neither succeeds
    without reducing nor invents `reduce`s along the way), and it no longer knows about normal
    terms, which is exactly what the second rule is for.

    Returns `.continue` (no rewrite) when neither applies — matching `moduletyping`/
    `normalmodule`'s leniency: an unreducible term (e.g. containing an opaque free variable with
    no matching hypothesis, whose normality is therefore not provable either) is left as it is
    rather than treated as an error. -/
private def reduceSimpProcImpl (e : Lean.Expr) : SimpM Simp.Step := do
  if let some r ← reduceSimpRun e reduceSimpHead then
    return .visit r
  let collapseNormal : Elab.Tactic.TacticM Unit := do
    Elab.Tactic.evalTactic
      (← `(tactic| (apply ModuleExpression.reduce_of_normal; normalmodule)))
  if let some r ← reduceSimpRun e collapseNormal then
    return .visit r
  return .continue

/- The obvious next step, `simproc reduceSimp (ModuleExpression.reduce _) := reduceSimpProcImpl`,
   doesn't work: the `simproc` command elaborates its *pattern* in an isolated `TermElabM`
   (`Lean.Elab.elabSimprocPattern`, confirmed by reading the source), disconnected from this
   section's `variable [ProgramSpec]` — and then force-synthesizes every instance-implicit in it
   (`Term.synthesizeSyntheticMVars`), so it always fails to find a `ProgramSpec` (there isn't a
   global one; that's the whole point of it being a section variable). This isn't a workaround-
   able syntax issue, it's structural: *no* `[ProgramSpec]`-parameterized declaration can be
   registered as a discrimination-tree-keyed `simproc` this way.

   So `reduce_simp` doesn't register anything globally. It drives `Lean.Meta.Simp.main` itself,
   at tactic-run time (where a concrete `ProgramSpec` *is* available, from the calling goal's own
   context), passing a custom `Simp.Methods.post` hook instead of a `Simprocs`/discrimination-tree
   entry — `post` is a plain `Expr → SimpM Step`, checked by hand (`isAppOfArity`) against the
   already-elaborated `Expr`s simp's traversal visits, no pattern registration involved at all.
   Simp's own bottom-up traversal (confirmed reliable all along — only its conditional-rewrite
   *discharge* step was ever the problem) still does the "keep visiting exposed subterms" work. -/
open Lean Meta Elab Tactic in
/-- Fully normalize `reduce m` subterms — one reduction step at a time via `reduceSimpHead`,
    then the `reduce` collapsed via `reduce_of_normal` (see `reduceSimpProcImpl`) — repeatedly,
    including inside freshly-exposed nested `reduce`s (handled by `simp`'s own subterm traversal,
    not by this tactic). Lenient per subterm — whatever it can't reduce is left as it is — but,
    like `simp`, it fails when that is *every* subterm and the goal comes back unchanged.  Closes
    the goal outright if it simplifies all the way to `True`.

    `substitute` and friends are in the simp set because `reduce_beta`'s result is
    `reduce (body.substitute arg)`, with `substitute` a structurally recursive `def` that no
    `reduceSimpHead` branch matches on: unfolding it is what turns that result back into a
    constructor tree the next step can work on.

    The tactic keyword `reduce_simp` is this function; it stays a keyword because proofs are
    written with it by hand.  Tactics that want it as a step call `reduceSimp` directly rather
    than going back through the grammar. -/
def reduceSimp : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let simpTheorems ← Lean.Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
    let simpTheorems ← [``ModuleExpression.substitute, ``ModuleExpression.substituteSimultaneously,
      ``ModuleExpression.variableSubstitution, ``ModuleExpression.liftSubst].foldlM
      (·.addDeclToUnfold ·) simpTheorems
    let congrTheorems ← getSimpCongrTheorems
    let ctx ← Simp.mkContext (simpTheorems := #[simpTheorems]) (congrTheorems := congrTheorems)
    -- `post`: try our own hook first, then fall through to `Simp.postDefault` (no simprocs of
    -- its own, but it's what actually consults `ctx.simpTheorems` — needed so e.g. a fully
    -- reduced `x = x` goal collapses to `True` via `eq_self`, which a bare custom `post`
    -- wouldn't do on its own since it doesn't touch `ctx.simpTheorems` at all).
    let methods : Simp.Methods :=
      { pre := Simp.preDefault #[]
        post :=
          (fun e => do
            if e.isAppOfArity ``ModuleExpression.reduce 2 then
              reduceSimpProcImpl e
            else
              return .continue) >> Simp.postDefault #[] }
    let (r, _) ← Simp.main target ctx (methods := methods)
    if r.expr.isConstOf ``True then
      match r.proof? with
      | some proof => goal.assign (← mkOfEqTrue proof)
      | none => goal.assign (mkConst ``True.intro)
      replaceMainGoal []
    else if (← instantiateMVars r.expr) == target then
      throwError "reduce_simp made no progress"
    else
      replaceMainGoal [← applySimpResultToTarget goal target r]

@[inherit_doc reduceSimp]
elab "reduce_simp" : tactic => reduceSimp

end GaudisCrypt
